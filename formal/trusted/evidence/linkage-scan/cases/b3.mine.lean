/-- [x]:
    Source: 'crates/rmcp/src/a.rs', lines 1:0-2:0 -/
def a.b.f (y : Option Nat) : Result Nat := do
  match y with
  | none => do
    let g <- ok 0
    ok g
  | some z => ok (z + g)
