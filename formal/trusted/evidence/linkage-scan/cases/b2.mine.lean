/-- [x]:
    Source: 'crates/rmcp/src/a.rs', lines 1:0-2:0 -/
def a.b.f (y : Option Nat) : Result Nat := do
  match y with
  | none => ok ((fun g => g) 0)
  | some z => ok (z + g)
