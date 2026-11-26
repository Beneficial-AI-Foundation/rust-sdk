# Differential tests of translation patch 05 (`metadata_resolver.rs`)

Evidence that translation patch 05 (`formal/trusted/patches/05-metadata-resolver.patch`)
keeps the behaviour of `crates/rmcp/src/transport/auth/metadata_resolver.rs` and of
`AuthorizationManager::is_loopback_metadata_host` (`crates/rmcp/src/transport/auth.rs`). Written
by the two independent reviewers of the patch-05 translation stage (review round 1,
2026-11-25); recorded here in the round-2 fixes. Not part of any build or CI job; they change no
SDK `*.rs` file and no patch: `run.sh` appends them to a scratch copy only.

## What is compared

The patched code (patches 01–05 applied by `scripts/apply-patches.sh`) against the original code
of upstream `7caec76`, compiled side by side in one test binary:

- `old_body.rs`: `metadata_resolver.rs` at `7caec76` before its `mod tests` (lines 1–226,
  byte-identical to the file in the repository; `run.sh` checks this with `cmp` against `git
  show 7caec76:crates/rmcp/src/transport/auth/metadata_resolver.rs | head -226`, and that line
  227 is the `#[cfg(test)]` of `mod tests`, before it creates anything). `run.sh` turns it into the child module `old`
  of the patched file with three edits, each checked to apply exactly once: the import of
  `AuthorizationManager` one level up, the four fields of `MetadataAddressResolver`
  `pub(super)` (so that the tests can compare them), and `with_lookup`'s guard calling
  `old_is_loopback_metadata_host`, so that the old side runs no patched code.
- `old_wrappers.rs`: the original `is_loopback_metadata_host` of `auth.rs` (before hunk H9) and
  an accessor for the original `normalize_host`. `run.sh` checks that its lines 4–13 are lines
  1401–1410 of `crates/rmcp/src/transport/auth.rs` at `7caec76` with the indentation of four
  spaces removed and the first line renamed to `pub(super) fn old_is_loopback_metadata_host(`,
  that line 14 is the accessor `old_normalize_host` and that there is no other line (lines 1–3
  are comments).
- `diff_tests.rs` (reviewer b, module `diff_tests`, three tests and the ignored helper
  `diff_new_reads_env_child`; `diff_new_reads_env` moved into a child process in the round-3 fixes):
  - `diff_is_loopback_and_normalize`: 1,953 host strings (31 atoms, among them empty, dots,
    `localhost` variants, non-ASCII letters such as `é`, `K` (U+212A), `İ`, `ß`, an IPv6
    literal and a NUL byte, and all their pairwise concatenations with and without a `.`):
    patched against original `is_loopback_metadata_host(Host::Domain(_))` and `normalize_host`,
    and `prim::{trim_end_dots, ends_with, contains}` against `trim_end_matches('.')`,
    `ends_with` and `contains` for 7 patterns.
  - `diff_resolver_construction_and_resolve`: 327,504 cases. For 48 URL strings (all of them
    parse: domains, `localhost` variants, IPv4/IPv6 literals including IPv4-mapped
    and NAT64, IDNA, `file:`, `mailto:`, `data:`, `unix:`) and 463 proxy lists (none, each of
    21 proxy strings, every ordered pair), the state (`base_ip`, `unfiltered_hosts`,
    `base_classes`) after `with_lookup` + `with_proxy_hosts`, after
    `allowing_private_addresses` applied twice and after `with_proxy_hosts` applied twice, and
    `allows_url` on every URL for the first two; and `resolve` (the async shell with
    `allowed_addresses`) on three resolvers per URL (plain, with proxy hosts, private allowed)
    for 212 lookup answers (empty, an error `boom`, each of 14 addresses, every ordered pair)
    and 10 names (6,823 cases per URL): the `Ok` address lists and the `Err` messages must be
    equal. This covers an unfiltered (proxy) host whose lookup is empty (both `Ok([])`), a
    lookup error (propagated unchanged by both), and the policy error message.
  - `diff_new_reads_env`: starts the test binary itself as a child process that runs only the
    ignored test `diff_new_reads_env_child`, with the six proxy variables set in the child's
    environment (one non-Unicode, `\xff\xfe`, and one unset) and the marker
    `RMCP_DIFF_NEW_READS_ENV_CHILD=1`; the child checks `prim::proxy_env_values()` against
    `PROXY_ENV_VARS.iter().filter_map(|v| std::env::var(v).ok())` (the non-Unicode value is
    dropped by both) and compares the state of `MetadataAddressResolver::new` with the original
    `new` for every URL; the parent requires the child to exit successfully with `1 passed; 0
    failed`. The test process's own environment is never changed: a first version that set the
    variables in-process (restoring them afterwards with a drop guard) made two upstream tests
    fail when run in the same process as the full library suite,
    `public_resource_cannot_be_redirected_to_internal_ip_literal` ("no address of `proxy.one` is
    allowed") and `loopback_resource_reaches_loopback_authorization_server_by_hostname`, because
    `reqwest` clients built concurrently read the proxy variables (2026-11-26).
    `diff_new_reads_env_child` without the marker checks nothing, so it passes trivially when
    ignored tests are run directly.
- `review_a1_tests.rs` (reviewer a, module `review_a1`, four tests, with local copies of the
  original expressions): `normalize_and_loopback_agree` (18 hosts),
  `proxy_hosts_agree` (29 proxy strings, all at once, one by one and reversed through a
  non-`Vec` iterator, on top of an existing unfiltered host), `base_classes_and_private_agree`
  (18 base URLs: `base_classes`, `base_ip`, empty `unfiltered_hosts`, `allowing_private_addresses`
  once and twice), `allowed_addresses_agree` (every subset of 13 socket addresses, 2^13 = 8,192,
  for 4 base URLs, private addresses allowed or not, and an unfiltered and a filtered host:
  `allowed_addresses` against the original filter/collect with the empty-to-`None` rule).

## How to run

```
formal/trusted/evidence/differential/metadata-resolver/run.sh [--full] <new scratch directory>
```

`run.sh` runs `scripts/apply-patches.sh` with `RMCP_LLBC_DIR=<scratch>/llbc` (the copy is
`<scratch>/llbc/work`), appends the module `old` (written to `<scratch>/old_module.rs` as well)
and the two test modules to the copy's `metadata_resolver.rs`, and runs

```
cargo test -p rmcp --lib --features request-state,server,client,client-side-sse,transport-streamable-http-server,transport-streamable-http-client,auth,macros \
  --target-dir <scratch>/target -- metadata_resolver::diff_tests metadata_resolver::review_a1 --nocapture
```

in `<scratch>/llbc/work`, with the toolchain of the repository's `rust-toolchain.toml`
(`<scratch>/toolchain.txt`). It fails unless exactly 7 tests pass (and the helper
`diff_new_reads_env_child` is reported ignored). With `--full` it runs the whole library suite of
the patched copy and the differential modules in one test process (no test-name filter, no
`--nocapture`) and fails unless the suite reports `0 failed` and all 7 differential tests are
reported `ok`.

Before it creates anything, `run.sh` canonicalises the parent of the scratch path (which must
exist; symlinks resolved) and refuses: a last component that is empty, `.` or `..`; a scratch
path that is a symlink; `/`, `$HOME` or an ancestor of `$HOME`; the repository, a path inside it
or an ancestor of it; an existing non-directory; an existing non-empty directory. It then runs
the two drift checks above (`old_body.rs`, `old_wrappers.rs` against `7caec76`, failing with a
message naming the file), creates only the scratch directory itself, and writes nothing outside
it; it deletes nothing.

## Results

- Reviewers, 2026-11-25 (round 1): all 7 tests pass, 0 differences.
- Re-run 2026-11-25 (round-2 fixes, patch 05 as in this commit, cargo and rustc 1.96.1,
  dependencies resolved afresh, `sha2 0.11.2`): `test result: ok. 7 passed; 0 failed; 0
  ignored; 0 measured; 847 filtered out`; `diff_is_loopback_and_normalize: 1953 hosts`;
  `diff_resolver_construction_and_resolve: 327504 cases`; `diff_new_reads_env`: `env values
  ["Proxy.One.", "socks5://[::1]:1", "", "two"]` (the non-Unicode `http_proxy` dropped),
  `unfiltered for localhost: ["proxy.one", "[::1]", "two"]` (the empty value parses to no host).
- Re-run 2026-11-26 (round-3 fixes: drift checks, scratch guard, child process for
  `diff_new_reads_env`; same toolchain): `run.sh <scratch>`: `test result: ok. 7 passed; 0
  failed; 1 ignored; 0 measured; 847 filtered out`, same three counts and values as above.
  `run.sh --full <scratch>` (the whole library suite and the differential modules in one
  process): `test result: ok. 854 passed; 0 failed; 1 ignored; 0 measured; 0 filtered out`
  (847 library tests and the 7 differential tests; the ignored one is the child helper).
  Refusal cases (with stub `rsync`/`rm` first on `PATH`): a path inside the repository, the
  repository, `/`, `$HOME`, a non-empty directory (also reached through `..`), a missing parent,
  `<repo>/formal/..`, a symlink to a directory of the repository and a child of such a symlink:
  each refused with exit 2, nothing created; `old_body.rs` with one appended line, and
  `old_wrappers.rs` with `is_loopback` changed or one appended line: each refused with exit 2
  (files restored afterwards).

Not covered: the async glue around the lookup beyond the cases above (cancellation, the
`warn!` output), `SystemResolver` (N02) and real DNS, and inputs outside the listed sets. These
tests catch a behaviour change of the patch; they are not a proof.
