//! DNS resolution for OAuth HTTP requests that applies the metadata address
//! policy to the addresses the client actually connects to.
//!
//! Hosts named by discovered metadata may resolve to any public address. A
//! loopback or private address is allowed only when the base URL itself names
//! one: a loopback or private IP literal, or `localhost`. The base host's DNS
//! answers never widen the policy, since the resource may control them.
//! Link-local (including cloud instance metadata), unspecified, broadcast,
//! multicast and reserved addresses are never allowed. The base URL's own host
//! is filtered too, so it can't be rebound to an internal address. Configured
//! proxy hosts are not filtered.

use std::{
    net::{IpAddr, SocketAddr, ToSocketAddrs},
    sync::Arc,
};

use reqwest::dns::{Addrs, Name, Resolve, Resolving};
use tracing::warn;
use url::{Host, Url};

use super::AuthorizationManager;

const PROXY_ENV_VARS: [&str; 6] = [
    "HTTP_PROXY",
    "http_proxy",
    "HTTPS_PROXY",
    "https_proxy",
    "ALL_PROXY",
    "all_proxy",
];

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum AddressClass {
    Public,
    Loopback,
    Private,
    Blocked,
}

impl AddressClass {
    pub(super) fn of(addr: IpAddr) -> Self {
        let addr = match addr {
            IpAddr::V6(v6) => {
                AuthorizationManager::embedded_ipv4(v6).map_or(IpAddr::V6(v6), IpAddr::V4)
            }
            v4 => v4,
        };
        match addr {
            IpAddr::V4(v4) => {
                let octets = v4.octets();
                if !AuthorizationManager::is_disallowed_metadata_ipv4(v4) {
                    Self::Public
                } else if v4.is_loopback() {
                    Self::Loopback
                } else if v4.is_private() || (octets[0] == 100 && (64..=127).contains(&octets[1])) {
                    Self::Private
                } else {
                    Self::Blocked
                }
            }
            IpAddr::V6(v6) => {
                if !AuthorizationManager::is_disallowed_metadata_ipv6(v6) {
                    Self::Public
                } else if v6.is_loopback() {
                    Self::Loopback
                } else if (v6.segments()[0] & 0xfe00) == 0xfc00 {
                    Self::Private
                } else {
                    Self::Blocked
                }
            }
        }
    }
}

/// Resolves names with the operating system resolver.
struct SystemResolver;

impl Resolve for SystemResolver {
    fn resolve(&self, name: Name) -> Resolving {
        let host = name.as_str().to_owned();
        Box::pin(async move {
            let addrs =
                tokio::task::spawn_blocking(move || (host.as_str(), 0).to_socket_addrs()).await??;
            Ok(Box::new(addrs) as Addrs)
        })
    }
}

/// Filters resolved addresses by the class of the base URL's host.
#[derive(Clone)]
pub(super) struct MetadataAddressResolver {
    base_ip: Option<IpAddr>,
    unfiltered_hosts: Arc<[String]>,
    base_classes: Arc<[AddressClass]>,
    lookup: Arc<dyn Resolve>,
}

impl MetadataAddressResolver {
    pub(super) fn new(base_url: &Url) -> Self {
        Self::with_lookup(base_url, Arc::new(SystemResolver)).with_proxy_hosts(
            PROXY_ENV_VARS
                .iter()
                .filter_map(|var| std::env::var(var).ok()),
        )
    }

    pub(super) fn with_lookup(base_url: &Url, lookup: Arc<dyn Resolve>) -> Self {
        let base_ip = literal_ip(base_url);
        let base_classes = match base_url.host() {
            Some(Host::Ipv4(v4)) => vec![AddressClass::of(IpAddr::V4(v4))],
            Some(Host::Ipv6(v6)) => vec![AddressClass::of(IpAddr::V6(v6))],
            Some(Host::Domain(domain))
                if AuthorizationManager::is_loopback_metadata_host(Host::Domain(domain)) =>
            {
                vec![AddressClass::Loopback]
            }
            _ => Vec::new(),
        };
        Self {
            base_ip,
            unfiltered_hosts: Arc::new([]),
            base_classes: base_classes.into(),
            lookup,
        }
    }

    /// Exempts the hosts of proxy URLs, since a proxied request resolves only
    /// the proxy's name and the proxy resolves the target.
    pub(super) fn with_proxy_hosts(mut self, proxies: impl IntoIterator<Item = String>) -> Self {
        let proxy_hosts = proxies.into_iter().filter_map(|proxy| {
            let proxy = if proxy.contains("://") {
                proxy
            } else {
                format!("http://{proxy}")
            };
            Url::parse(&proxy).ok()?.host_str().map(normalize_host)
        });
        self.unfiltered_hosts = self
            .unfiltered_hosts
            .iter()
            .cloned()
            .chain(proxy_hosts)
            .collect();
        self
    }

    /// Also allows private addresses, whatever the base URL names.
    pub(super) fn allowing_private_addresses(mut self) -> Self {
        if !self.base_classes.contains(&AddressClass::Private) {
            self.base_classes = self
                .base_classes
                .iter()
                .copied()
                .chain([AddressClass::Private])
                .collect();
        }
        self
    }

    /// Applies the policy to an IP-literal host, which reqwest connects to
    /// without resolving. The base URL's own literal is always allowed.
    pub(super) fn allows_url(&self, url: &Url) -> bool {
        match literal_ip(url) {
            Some(ip) => {
                self.base_ip == Some(ip)
                    || Self::is_allowed(AddressClass::of(ip), &self.base_classes)
            }
            None => true,
        }
    }

    #[cfg(test)]
    pub(super) fn with_base_classes(mut self, classes: Vec<AddressClass>) -> Self {
        self.base_classes = classes.into();
        self
    }

    pub(super) fn is_allowed(class: AddressClass, base_classes: &[AddressClass]) -> bool {
        match class {
            AddressClass::Public => true,
            AddressClass::Loopback | AddressClass::Private => base_classes.contains(&class),
            AddressClass::Blocked => false,
        }
    }
}

impl Resolve for MetadataAddressResolver {
    fn resolve(&self, name: Name) -> Resolving {
        let this = self.clone();
        Box::pin(async move {
            let host = normalize_host(name.as_str());
            let resolved: Vec<SocketAddr> = this.lookup.resolve(name).await?.collect();
            if this.unfiltered_hosts.contains(&host) {
                return Ok(Box::new(resolved.into_iter()) as Addrs);
            }

            let allowed: Vec<SocketAddr> = resolved
                .into_iter()
                .filter(|addr| Self::is_allowed(AddressClass::of(addr.ip()), &this.base_classes))
                .collect();
            if allowed.is_empty() {
                warn!("rejecting every resolved address of `{host}` for OAuth requests");
                return Err(format!(
                    "no address of `{host}` is allowed for OAuth requests from this resource"
                )
                .into());
            }
            Ok(Box::new(allowed.into_iter()) as Addrs)
        })
    }
}

fn literal_ip(url: &Url) -> Option<IpAddr> {
    match url.host()? {
        Host::Ipv4(v4) => Some(IpAddr::V4(v4)),
        Host::Ipv6(v6) => Some(IpAddr::V6(v6)),
        Host::Domain(_) => None,
    }
}

fn normalize_host(host: &str) -> String {
    host.trim_end_matches('.').to_ascii_lowercase()
}

