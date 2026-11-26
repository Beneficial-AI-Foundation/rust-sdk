#[cfg(test)]
mod diff_tests {
    use std::{collections::HashMap, net::IpAddr, sync::{Arc, Mutex}};

    use reqwest::dns::{Addrs, Name, Resolve, Resolving};
    use url::{Host, Url};

    use super::{old, AddressClass, MetadataAddressResolver};

    fn hosts() -> Vec<String> {
        let atoms = ["", ".", "..", "localhost", "LOCALHOST", "LocalHost", "a", "A", "x.localhost",
            "X.LOCALHOST", "localhost.", "localhost..", ".localhost", "a.localhost.", "localhostx",
            "xlocalhost", "local", "é", "É", "\u{212A}", "\u{0130}", "ı", "ß", "Ä.localhost",
            "x.localhost.x", "a..b", "1.2.3.4", "[::1]", "LOCALHOST\u{0}", "localhost .", "–."];
        let mut v: Vec<String> = atoms.iter().map(|s| s.to_string()).collect();
        for a in atoms.iter() {
            for b in atoms.iter() {
                v.push(format!("{a}{b}"));
                v.push(format!("{a}.{b}"));
            }
        }
        v
    }

    #[test]
    fn diff_is_loopback_and_normalize() {
        let mut n = 0;
        for h in hosts() {
            let new = crate::transport::auth::AuthorizationManager::is_loopback_metadata_host(
                Host::Domain(h.as_str()),
            );
            let o = old::old_is_loopback_metadata_host(Host::Domain(h.as_str()));
            assert_eq!(new, o, "is_loopback {h:?}");
            assert_eq!(super::normalize_host(&h), old::old_normalize_host(&h), "normalize {h:?}");
            // prim against the std expressions
            assert_eq!(super::prim::trim_end_dots(&h), h.trim_end_matches('.'));
            for p in ["", ".", "://", "localhost", ".localhost", "é", "\u{212A}"] {
                assert_eq!(super::prim::ends_with(&h, p), h.ends_with(p));
                assert_eq!(super::prim::contains(&h, p), h.contains(p));
            }
            n += 1;
        }
        eprintln!("diff_is_loopback_and_normalize: {n} hosts");
    }

    fn urls() -> Vec<String> {
        let mut v = vec![];
        for h in ["localhost", "LOCALHOST.", "a.localhost", "a.localhost..", "127.0.0.1", "10.0.0.1",
            "100.64.0.1", "169.254.169.254", "8.8.8.8", "[::1]", "[fd00::1]", "[::ffff:127.0.0.1]",
            "[::ffff:10.0.0.1]", "[fe80::1]", "example.com", "EXAMPLE.com.", "xn--bcher-kva.de",
            "bücher.de", "0x7f.1", "2130706433", "[64:ff9b::a00:9]", "localhost%2e"] {
            v.push(format!("http://{h}/"));
            v.push(format!("https://{h}:8443/x"));
        }
        v.push("file:///tmp/x".into());
        v.push("mailto:a@b".into());
        v.push("data:text/plain,hi".into());
        v.push("unix:/run/x".into());
        v
    }

    #[derive(Default)]
    struct Fake(Mutex<HashMap<String, Result<Vec<IpAddr>, String>>>);
    impl Resolve for Fake {
        fn resolve(&self, name: Name) -> Resolving {
            let r = self.0.lock().unwrap().get(name.as_str()).cloned()
                .unwrap_or_else(|| Ok(Vec::new()));
            Box::pin(async move {
                match r {
                    Ok(ips) => {
                        let addrs: Vec<std::net::SocketAddr> =
                            ips.into_iter().map(|ip| (ip, 7).into()).collect();
                        Ok(Box::new(addrs.into_iter()) as Addrs)
                    }
                    Err(e) => Err(e.into()),
                }
            })
        }
    }

    fn proxies_sets() -> Vec<Vec<String>> {
        let ps = ["", "://", "proxy", "PROXY.example.", "http://Proxy.Example.:3128",
            "socks5://10.0.0.1:1080", "[::1]:8080", "user:pw@Host.Local.:1", "http://[fd00::1]",
            "bücher.de", "h:/x", "  spaced  ", "http://", "localhost", "a b", "%zz", "http://h/p?q#f",
            "file:///x", "data:text/plain,x", "unix:/run/x", "mailto:a@b"];
        let mut v: Vec<Vec<String>> = vec![vec![]];
        for p in ps.iter() { v.push(vec![p.to_string()]); }
        for p in ps.iter() { for q in ps.iter() { v.push(vec![p.to_string(), q.to_string()]); } }
        v
    }

    fn ips() -> Vec<IpAddr> {
        ["127.0.0.1", "10.0.0.1", "8.8.8.8", "169.254.169.254", "::1", "fd00::1", "fe80::1",
         "::ffff:127.0.0.1", "::ffff:10.0.0.1", "::ffff:8.8.8.8", "2606:4700::1111", "0.0.0.0",
         "100.64.0.1", "64:ff9b::a00:9"].iter().map(|s| s.parse().unwrap()).collect()
    }

    fn eq_state(a: &MetadataAddressResolver, b: &old::MetadataAddressResolver, ctx: &str) {
        assert_eq!(a.base_ip, b.base_ip, "{ctx}");
        assert_eq!(&*a.unfiltered_hosts, &*b.unfiltered_hosts, "{ctx}");
        assert_eq!(format!("{:?}", &*a.base_classes), format!("{:?}", &*b.base_classes), "{ctx}");
    }

    #[tokio::test]
    async fn diff_resolver_construction_and_resolve() {
        let fake = Arc::new(Fake::default());
        let ipl = ips();
        let mut answers: Vec<Result<Vec<IpAddr>, String>> = vec![Ok(vec![]), Err("boom".into())];
        for a in &ipl { answers.push(Ok(vec![*a])); }
        for a in &ipl { for b in &ipl { answers.push(Ok(vec![*a, *b])); } }
        let names = ["proxy", "PROXY.example.", "proxy.example", "host.local", "10.0.0.1", "fd00::1",
            "Host.Local.", "x", "bücher.de", "xn--bcher-kva.de"];
        let mut cases = 0u64;
        for u in urls() {
            let Ok(url) = Url::parse(&u) else { continue };
            for proxies in proxies_sets() {
                let a = MetadataAddressResolver::with_lookup(&url, fake.clone())
                    .with_proxy_hosts(proxies.clone());
                let b = old::MetadataAddressResolver::with_lookup(&url, fake.clone())
                    .with_proxy_hosts(proxies.clone());
                eq_state(&a, &b, &format!("{u} {proxies:?}"));
                // allowing_private_addresses, applied once and twice
                let a2 = a.clone().allowing_private_addresses().allowing_private_addresses();
                let b2 = b.clone().allowing_private_addresses().allowing_private_addresses();
                eq_state(&a2, &b2, &format!("allowing {u} {proxies:?}"));
                // chaining with_proxy_hosts twice
                let a3 = a.clone().with_proxy_hosts(proxies.clone());
                let b3 = b.clone().with_proxy_hosts(proxies.clone());
                eq_state(&a3, &b3, &format!("twice {u} {proxies:?}"));
                for t in urls() {
                    let Ok(tu) = Url::parse(&t) else { continue };
                    assert_eq!(a.allows_url(&tu), b.allows_url(&tu));
                    assert_eq!(a2.allows_url(&tu), b2.allows_url(&tu));
                }
                cases += 1;
            }
            // resolve on the plain and the proxy-exempting resolvers
            let proxies = vec!["proxy".to_string(), "http://Host.Local.:1".to_string()];
            for (ra, rb) in [
                (MetadataAddressResolver::with_lookup(&url, fake.clone()),
                 old::MetadataAddressResolver::with_lookup(&url, fake.clone())),
                (MetadataAddressResolver::with_lookup(&url, fake.clone()).with_proxy_hosts(proxies.clone()),
                 old::MetadataAddressResolver::with_lookup(&url, fake.clone()).with_proxy_hosts(proxies.clone())),
                (MetadataAddressResolver::with_lookup(&url, fake.clone()).allowing_private_addresses(),
                 old::MetadataAddressResolver::with_lookup(&url, fake.clone()).allowing_private_addresses()),
            ] {
                for ans in &answers {
                    for nm in names {
                        fake.0.lock().unwrap().insert(nm.to_string(), ans.clone());
                        let n1: Name = nm.parse().unwrap();
                        let n2: Name = nm.parse().unwrap();
                        let x = ra.resolve(n1).await.map(|i| i.collect::<Vec<_>>()).map_err(|e| e.to_string());
                        let y = rb.resolve(n2).await.map(|i| i.collect::<Vec<_>>()).map_err(|e| e.to_string());
                        assert_eq!(x, y, "resolve {u} {nm} {ans:?}");
                        cases += 1;
                    }
                }
            }
        }
        eprintln!("diff_resolver_construction_and_resolve: {cases} cases");
    }

    /// The six proxy variables of `PROXY_ENV_VARS`, in its order.
    const PROXY_VARS: [&str; 6] =
        ["HTTP_PROXY", "http_proxy", "HTTPS_PROXY", "https_proxy", "ALL_PROXY", "all_proxy"];
    /// Set only in the environment of the child process that `diff_new_reads_env` starts.
    const ENV_CHILD: &str = "RMCP_DIFF_NEW_READS_ENV_CHILD";

    /// The comparison of `diff_new_reads_env`, run by it in a child process (the same test
    /// binary) whose environment holds the test values of the proxy variables. Ignored in a
    /// normal run; without `ENV_CHILD` set it checks nothing.
    #[test]
    #[ignore = "run by diff_new_reads_env in a child process"]
    fn diff_new_reads_env_child() {
        if std::env::var_os(ENV_CHILD).is_none() {
            return;
        }
        let got = super::prim::proxy_env_values();
        let want: Vec<String> = PROXY_VARS.iter().filter_map(|v| std::env::var(v).ok()).collect();
        assert_eq!(got, want);
        for u in urls() {
            let Ok(url) = Url::parse(&u) else { continue };
            let a = MetadataAddressResolver::new(&url);
            let b = old::MetadataAddressResolver::new(&url);
            eq_state(&a, &b, &u);
        }
        eprintln!("env values {got:?}; unfiltered for localhost: {:?}",
            MetadataAddressResolver::new(&Url::parse("http://localhost").unwrap()).unfiltered_hosts);
        let _ = AddressClass::Public;
    }

    /// `new` and `prim::proxy_env_values` against the original with six proxy variables (one
    /// non-Unicode, one unset). The variables are set only in a child process: changing this
    /// process's environment would race with the other tests of the library suite, whose
    /// `reqwest` clients read the proxy variables when they are built.
    #[test]
    fn diff_new_reads_env() {
        use std::os::unix::ffi::OsStrExt;
        let vals: [Option<&[u8]>; 6] = [Some(b"Proxy.One."), Some(b"\xff\xfe"), None,
            Some(b"socks5://[::1]:1"), Some(b""), Some(b"two")];
        let module = module_path!().split_once("::").unwrap().1;
        let mut cmd = std::process::Command::new(std::env::current_exe().unwrap());
        cmd.args(["--exact", &format!("{module}::diff_new_reads_env_child"), "--ignored",
            "--nocapture", "--test-threads=1"]).env(ENV_CHILD, "1");
        for (k, v) in PROXY_VARS.iter().zip(vals.iter()) {
            match v {
                Some(b) => cmd.env(k, std::ffi::OsStr::from_bytes(b)),
                None => cmd.env_remove(k),
            };
        }
        let out = cmd.output().unwrap();
        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);
        eprint!("{stderr}");
        assert!(out.status.success(), "child failed:\n{stdout}\n{stderr}");
        assert!(stdout.contains("test result: ok. 1 passed; 0 failed"), "child: {stdout}");
    }
}
