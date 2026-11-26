/-- [x]:
    Source: 'crates/rmcp/src/a.rs', lines 1:0-2:0 -/
def transport.auth.metadata_resolver.literal_ip
  (target : url.Url) : Result (Option Nat) := do
  let o ← url.Url.host target
  ok none
