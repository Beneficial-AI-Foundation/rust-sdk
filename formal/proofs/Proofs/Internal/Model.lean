/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Defs
import Proofs.Model.NumberOrString

/-!
# Internal spec file for crates/rmcp/src/model.rs (crate-internal functions: M06, M07)

These are guarantees about crate-internal (`pub(crate)`) functions, kept out of `formal/specs/`,
which holds only the public API (human decision 2026-11-24); the public functions of `model.rs`
are in `formal/specs/Specs/Model.lean`. Index of all guarantees: `formal/specs/README.md`.

| ID | Function | Guarantee | Assumptions |
|---|---|---|---|
| M06 | `NumberOrString::numeric_string_value` | number: `None`; string: (a) | none |
| M07 | `NumberOrString::matches_response_id` | `true` iff (b) | none |

Each row says that the call does not panic and that its result satisfies the guarantee. (a) the
value of its bytes under `Defs.parseI64` (the grammar of `i64::from_str`: an optional `+` or `-`,
then one or more ASCII digits, in the `i64` range), `None` if rejected. (b) the two ids are equal,
or `self` is `Number(n)` and the response id is a string whose `Defs.parseI64` value is `n`.

Restated from `formal/specs/Specs/Model.lean` on 2026-11-24, when `formal/specs/` was restricted
to the public API; the statements and their `#print axioms` checks are unchanged. Each is a
theorem `Theorems.model.NumberOrString.<function>` proved by the spec theorem in
`Proofs/Model/NumberOrString.lean`. Signed off by the spec owner on 2026-11-24 (S24/S25 spec
cycle, `formal/docs/STATUS.md`).

Translated configuration (the proofs hold only for it): target `x86_64-unknown-linux-gnu`,
`--no-default-features` with the features `request-state`, `server`, `client`, `client-side-sse`,
`transport-streamable-http-server`, `transport-streamable-http-client` and `auth` (widened for
Phase 2, plan Section 15), with `overflow-checks=true` and `debug-assertions=true` (plan
Section 1). Aeneas `nightly-2026.08.20-5d08da4`. Line numbers refer to upstream `7caec76`,
unmodified (plan Section 13).

Definitions used: `Defs.JsonRpc` (`numericValue`) and `Defs.IntParse` (`Defs.parseI64`, through
`numericValue`), both in the `Defs` library (`formal/specs/Defs/`).

External models used (`trusted/Rmcp/FunsExternal.lean`): the models of the `Arc` deref (line
761), `str::parse` (line 1023), `i64::from_str` (line 1009, through the S27 deferred law
`Theorems.External.I64.Insts.CoreStrTraitsFromStrParseIntError.from_str_eq_parseI64` in
`Proofs/Internal/External.lean`) and `Result::ok` (`core.result.Result.ok`, line 828); M07 also
uses `Option`'s `PartialEq` (line 811) and the `Arc<str>` `PartialEq` (line 780), which calls the
`str` equality `Str.Insts.CoreCmpPartialEqStr.eq` (line 735), and the derived `PartialEq` of
`NumberOrString` (translated from line 304; no statement is about it). No statement reaches a
native-code assumption.

Statements here, in Rust source order: M06 (line 322), M07 (330).
-/

open Aeneas Aeneas.Std Result
open rmcp  -- for `model.…` in the statements; theorems named in full
open Defs.JsonRpc

/-- M06 `numeric_string_value`: `None` for a numeric id; for a string id, the value of its bytes
under `Defs.parseI64` (the `i64::from_str` grammar), `None` if rejected. -/
theorem Theorems.model.NumberOrString.numeric_string_value (self : model.NumberOrString) :
    rmcp.model.NumberOrString.numeric_string_value self ⦃ (result : Option I64) =>
      result.map (·.val) = numericValue self ⦄ :=
  rmcp.model.NumberOrString.numeric_string_value_spec self

/--
info: 'Theorems.model.NumberOrString.numeric_string_value' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.model.NumberOrString.numeric_string_value

/-- M07 `matches_response_id`: `true` iff the ids are equal, or `self` is a number `n` and the
response id is a string whose `Defs.parseI64` value is `n`. -/
theorem Theorems.model.NumberOrString.matches_response_id
    (self response_id : model.NumberOrString) :
    rmcp.model.NumberOrString.matches_response_id self response_id ⦃ (result : Bool) =>
      (result = true ↔
        self = response_id ∨
          ∃ n : I64, self = .Number n ∧ numericValue response_id = some n.val) ⦄ :=
  rmcp.model.NumberOrString.matches_response_id_spec self response_id

/--
info: 'Theorems.model.NumberOrString.matches_response_id' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.model.NumberOrString.matches_response_id
