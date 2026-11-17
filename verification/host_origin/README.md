# Host/Origin Aeneas extraction

This is an initial extraction of production `rmcp` code at SDK commit `0e2396f`.
It is not a proof of the Host/Origin rejection property in issue #3.

`RmcpHostOrigin/Funs.lean` contains the extracted bodies of `host_is_allowed`,
`origin_is_allowed`, `AllowedPort::matches`, `default_port`, and generated
closures/trait implementations. `FunsExternal.lean` contains declarations for
external Rust operations and the deliberately opaque production parsers
`parse_allowed_authority` and `parse_allowed_origin`. `Types.lean` and
`TypesExternal.lean` are required by the generated function files.
`translation.json` maps Lean definitions to their Rust sources.

## Reproduce

Use Charon `0.1.235`, Aeneas `5d08da45`, and Rust
`nightly-2026-06-01`. Set `CHARON` and `AENEAS` to those binaries. From
`crates/rmcp`, run:

```sh
env RUSTUP_TOOLCHAIN=nightly-2026-06-01 CARGO_NET_OFFLINE=true "$CHARON" cargo \
  --preset=aeneas \
  --start-from rmcp::transport::streamable_http_server::tower::host_is_allowed \
  --start-from rmcp::transport::streamable_http_server::tower::origin_is_allowed \
  --opaque rmcp::transport::streamable_http_server::tower::parse_allowed_authority \
  --opaque rmcp::transport::streamable_http_server::tower::parse_allowed_origin \
  --dest-file /tmp/RmcpHostOrigin.llbc -- \
  --no-default-features --features server,transport-streamable-http-server --lib
"$AENEAS" -backend lean /tmp/RmcpHostOrigin.llbc \
  -dest ../../verification/host_origin/RmcpHostOrigin \
  -split-files -emit-json -no-progress-bar
```

Copy the generated `FunsExternal_Template.lean` and
`TypesExternal_Template.lean` to the corresponding files without `_Template`.
The pinned Aeneas generator also emits `filter_map` and `any` fields in one
`Iterator` instance that do not exist in its Lean library; remove those fields
from `Funs.lean` as shown in the checked-in file. All four `.lean` files then
compile with Lean 4.31.0 and Aeneas `5d08da45`'s built Lean library.

## Remaining boundaries

- The two `parse_allowed_*` functions are axioms here. Their parsing behavior,
  including malformed input, is outside this extraction.
- Iterator operations, string equality/dereference, and some `Option` operations
  remain external declarations. They need reviewed models before a property
  about matching can be proved.
- The request-level `validate_dns_rebinding_headers` path was attempted with
  Charon and Aeneas. Charon produced LLBC, but Aeneas failed on tracing-related
  definitions and string-pattern signatures (`trim_matches` and `strip_suffix`).
  Thus `parse_host_header`, `validate_origin_header`, and the early return from
  `StreamableHttpService::handle` are not in these Lean files.
- No target theorem has been proved. In particular, these files do not yet show
  that rejected Host/Origin requests cannot reach MCP request processing.
