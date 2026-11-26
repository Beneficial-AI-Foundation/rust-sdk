// Appended inside `mod old` after old_body.rs: the original AuthorizationManager::
// is_loopback_metadata_host (crates/rmcp/src/transport/auth.rs at 7caec76, before hunk H9)
// and an accessor for the original normalize_host.
pub(super) fn old_is_loopback_metadata_host(host: Host<&str>) -> bool {
    match host {
        Host::Domain(domain) => {
            let domain = domain.trim_end_matches('.').to_ascii_lowercase();
            domain == "localhost" || domain.ends_with(".localhost")
        }
        Host::Ipv4(addr) => addr.is_loopback(),
        Host::Ipv6(addr) => addr.is_loopback(),
    }
}
pub(super) fn old_normalize_host(host: &str) -> String { normalize_host(host) }
