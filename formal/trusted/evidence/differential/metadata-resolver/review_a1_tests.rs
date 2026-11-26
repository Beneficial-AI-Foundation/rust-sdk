#[cfg(test)]
mod review_a1 {
    use super::*;

    fn old_normalize_host(host: &str) -> String {
        host.trim_end_matches('.').to_ascii_lowercase()
    }
    fn old_is_loopback_domain(domain: &str) -> bool {
        let domain = domain.trim_end_matches('.').to_ascii_lowercase();
        domain == "localhost" || domain.ends_with(".localhost")
    }
    fn old_proxy_hosts(start: &[String], proxies: Vec<String>) -> Vec<String> {
        let proxy_hosts = proxies.into_iter().filter_map(|proxy| {
            let proxy = if proxy.contains("://") { proxy } else { format!("http://{proxy}") };
            Url::parse(&proxy).ok()?.host_str().map(normalize_host)
        });
        let a: Arc<[String]> = start.iter().cloned().chain(proxy_hosts).collect();
        a.to_vec()
    }
    fn old_base_classes(base_url: &Url) -> Vec<AddressClass> {
        match base_url.host() {
            Some(Host::Ipv4(v4)) => vec![AddressClass::of(IpAddr::V4(v4))],
            Some(Host::Ipv6(v6)) => vec![AddressClass::of(IpAddr::V6(v6))],
            Some(Host::Domain(domain))
                if AuthorizationManager::is_loopback_metadata_host(Host::Domain(domain)) =>
            {
                vec![AddressClass::Loopback]
            }
            _ => Vec::new(),
        }
    }
    fn old_allowed(this: &MetadataAddressResolver, host: &String, resolved: Vec<SocketAddr>) -> Option<Vec<SocketAddr>> {
        if this.unfiltered_hosts.contains(host) {
            return Some(resolved);
        }
        let allowed: Vec<SocketAddr> = resolved
            .into_iter()
            .filter(|addr| MetadataAddressResolver::is_allowed(AddressClass::of(addr.ip()), &this.base_classes))
            .collect();
        if allowed.is_empty() { None } else { Some(allowed) }
    }

    const HOSTS: &[&str] = &[
        "", ".", "..", "localhost", "localhost.", "LOCALHOST..", "a.localhost", ".localhost",
        "x.LocalHost.", "localhost.com", "xlocalhost", "ÄLOCALHOST", "Straße.de.", "a..b..",
        "127.0.0.1", "[::1]", "İ.localhost", "local host",
    ];

    #[test]
    fn normalize_and_loopback_agree() {
        for h in HOSTS {
            assert_eq!(normalize_host(h), old_normalize_host(h), "{h:?}");
            assert_eq!(
                AuthorizationManager::is_loopback_metadata_host(Host::Domain(h)),
                old_is_loopback_domain(h),
                "{h:?}"
            );
        }
    }

    #[test]
    fn proxy_hosts_agree() {
        let proxies: Vec<String> = [
            "", "://", "host:8080", "http://User@Host.:1", "[::1]:80", "socks5://Proxy.Example.",
            "http://", "not a url", " ", "a b", "HTTP://X", "http://[::ffff:1.2.3.4]", "x://y",
            "file:///tmp", "mailto:a@b", "1.2.3.4", "proxy.:3128", "://h", "h://", "http:/h",
            "data:text/plain,hi", "http://%41", "https://xn--strae-oqa.de", "http://Straße.de",
            "a:b", "localhost:1", "127.1", "0x7f.1", "http://[fe80::1%25eth0]",
        ]
        .iter()
        .map(|s| s.to_string())
        .collect();
        let base = MetadataAddressResolver::with_lookup(
            &Url::parse("https://example.com").unwrap(),
            Arc::new(SystemResolver),
        )
        .with_proxy_hosts(vec!["pre.example".to_string()]);
        let start = base.unfiltered_hosts.to_vec();
        let new = base.clone().with_proxy_hosts(proxies.clone());
        assert_eq!(new.unfiltered_hosts.to_vec(), old_proxy_hosts(&start, proxies.clone()));
        for p in &proxies {
            let new = base.clone().with_proxy_hosts(vec![p.clone()]);
            assert_eq!(new.unfiltered_hosts.to_vec(), old_proxy_hosts(&start, vec![p.clone()]), "{p:?}");
        }
        // an iterator that is not a Vec
        let new = base.clone().with_proxy_hosts(proxies.clone().into_iter().rev());
        let mut r = proxies.clone(); r.reverse();
        assert_eq!(new.unfiltered_hosts.to_vec(), old_proxy_hosts(&start, r));
        eprintln!("{:?}", new.unfiltered_hosts);
    }

    #[test]
    fn base_classes_and_private_agree() {
        let urls = [
            "http://localhost", "http://LOCALHOST.", "http://a.localhost:8080", "http://127.0.0.1",
            "http://10.0.0.1", "http://[::1]", "http://[fc00::1]", "http://[::ffff:10.0.0.1]",
            "http://169.254.169.254", "https://example.com", "file:///x", "mailto:a@b",
            "data:,x", "http://100.64.0.1", "http://0.0.0.0", "http://[fe80::1]", "x://localhost",
            "http://8.8.8.8",
        ];
        for u in urls {
            let url = Url::parse(u).unwrap();
            let r = MetadataAddressResolver::with_lookup(&url, Arc::new(SystemResolver));
            assert_eq!(r.base_classes.to_vec(), old_base_classes(&url), "{u}");
            assert!(r.unfiltered_hosts.is_empty());
            let old_ip = match url.host() {
                Some(Host::Ipv4(v4)) => Some(IpAddr::V4(v4)),
                Some(Host::Ipv6(v6)) => Some(IpAddr::V6(v6)),
                _ => None,
            };
            assert_eq!(r.base_ip, old_ip);
            let p = r.clone().allowing_private_addresses();
            let mut old: Vec<AddressClass> = r.base_classes.to_vec();
            if !old.contains(&AddressClass::Private) { old = old.iter().copied().chain([AddressClass::Private]).collect(); }
            assert_eq!(p.base_classes.to_vec(), old);
            let pp = p.clone().allowing_private_addresses();
            assert_eq!(pp.base_classes.to_vec(), p.base_classes.to_vec());
        }
    }

    #[test]
    fn allowed_addresses_agree() {
        let ips: Vec<SocketAddr> = [
            "8.8.8.8", "127.0.0.1", "10.1.2.3", "169.254.169.254", "::1", "fc00::1", "2001:db8::1",
            "::ffff:127.0.0.1", "100.64.0.1", "0.0.0.0", "1.1.1.1", "::ffff:8.8.8.8", "fe80::1",
        ].iter().map(|s| (s.parse::<IpAddr>().unwrap(), 443).into()).collect();
        let urls = ["https://example.com", "http://localhost", "http://10.0.0.1", "http://[::1]"];
        for u in urls {
            for priv_ in [false, true] {
                let mut r = MetadataAddressResolver::with_lookup(&Url::parse(u).unwrap(), Arc::new(SystemResolver))
                    .with_proxy_hosts(vec!["proxy.local".to_string()]);
                if priv_ { r = r.allowing_private_addresses(); }
                for mask in 0u32..(1 << ips.len()) {
                    let resolved: Vec<SocketAddr> = ips.iter().enumerate().filter(|(i, _)| mask >> i & 1 == 1).map(|(_, a)| *a).collect();
                    for host in ["proxy.local", "other"] {
                        let h = host.to_string();
                        assert_eq!(r.allowed_addresses(&h, resolved.clone()), old_allowed(&r, &h, resolved.clone()));
                    }
                }
            }
        }
    }
}
