/-- [x]:
    Source: 'crates/rmcp/src/a.rs', lines 1:0-2:0 -/
def a.b.f (y : Nat) : Result Nat := do
  -- see /- below
  let t := g + y
  /- note -/
  ok t
