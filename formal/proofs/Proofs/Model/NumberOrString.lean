/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Rmcp.Funs
import Defs.JsonRpc
import Proofs.External.IntParse

/-!
# Spec theorems for `NumberOrString` (M06, M07)

`numeric_string_value` (M06) parses a string id with `i64::from_str` and keeps `Ok`; its value is
`Defs.JsonRpc.numericValue`, by the S27 deferred law `from_str_eq_parseI64`
(`Proofs/External/IntParse.lean`). `matches_response_id` (M07) is the derived equality, or else a
numeric request id against the parsed response id; its proof uses M06.

Source: "crates/rmcp/src/model.rs", lines 322–337 at `7caec76`
-/

open Aeneas Aeneas.Std Result
open Defs.JsonRpc

namespace rmcp.model.NumberOrString

/-- **Spec theorem for `rmcp::model::NumberOrString::numeric_string_value`** (M06)

`None` for a numeric id; for a string id, the integer its bytes denote under Rust's `i64::from_str`
grammar (`Defs.parseI64`: optional single `+`/`-`, at least one ASCII digit, nothing else, value
in `[-2^63, 2^63 - 1]`), `None` when the grammar rejects them (plan Section 16.1, M06; Section 17,
"M06"; `model.rs` lines 322–327: `Self::String(id) => id.parse().ok()`, `Self::Number(_) =>
None`). Stated as `result.map (·.val) = numericValue self`, which determines `result` because
`I64.val` is injective. No premise: `Arc` deref, `str::parse` and `Result::ok` never fail in
their models. The proof needs the S27 deferred law of `Proofs.External.IntParse`. -/
@[step]
theorem numeric_string_value_spec (self : model.NumberOrString) :
    numeric_string_value self ⦃ (result : Option I64) =>
      result.map (·.val) = numericValue self ⦄ := by
  match self with
  | .Number n => simp only [numeric_string_value, numericValue, Option.map_eq_none_iff, WP.spec_ok]
  | .String a =>
    obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists
      (I64.Insts.CoreStrTraitsFromStrParseIntError.from_str_eq_parseI64 a.data)
    simp only [numeric_string_value, alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref,
      core.str.Str.parse_eq, bind_tc_ok, numericValue, hr]
    rcases r with n | e
    · simp only [core.result.Result.ok, WP.spec_ok, Option.map_some] at hp ⊢
      exact hp
    · simp only [core.result.Result.ok, WP.spec_ok, Option.map_none] at hp ⊢
      exact hp

/-- **Spec theorem for `rmcp::model::NumberOrString::matches_response_id`** (M07)

`true` exactly when the two ids are equal, or the request id `self` is a number `n` and the
response id is a string whose `Defs.parseI64` value is `n` (plan Section 16.1, M07; `model.rs`
lines 330–337: `self == response_id || matches!(self, Self::Number(request_id) if
response_id.numeric_string_value() == Some(*request_id))`).

Equality is Lean equality of `NumberOrString`, which is the derived `PartialEq` (line 304): equal
numbers, or string ids with equal bytes (the `Arc<str>` model compares contents, plan Section 17,
"M07"; a `Str` is determined by its bytes). The asymmetry is stated, not hidden (plan Section
17): `Number 1` matches `String "1"`, but `String "1"` does not match `Number 1` (the second
disjunct needs `self` to be a number). No premise. -/
@[step]
theorem matches_response_id_spec (self response_id : model.NumberOrString) :
    matches_response_id self response_id ⦃ (result : Bool) =>
      (result = true ↔
        self = response_id ∨
          ∃ n : I64, self = .Number n ∧ numericValue response_id = some n.val) ⦄ := by
  obtain ⟨o, ho, hpo⟩ := WP.spec_imp_exists (numeric_string_value_spec response_id)
  match self, response_id with
  | .Number n, .Number m =>
    simp only [matches_response_id, Insts.CoreCmpPartialEqNumberOrString.eq, read_discriminant,
      ↓reduceIte, lift, core.cmp.impls.PartialEqI64.eq, numeric_string_value,
      core.option.Option.Insts.CoreCmpPartialEqOption.eq, liftFun2, bind_tc_ok,
      Bool.false_eq_true, decide_eq_true_eq, Number.injEq, numericValue, reduceCtorEq, and_false,
      exists_const, or_false]
    by_cases h : n = m <;>
      simp only [h, ↓reduceIte, iff_true, iff_false, Bool.not_eq_true, WP.spec_ok]
  | .Number n, .String b =>
    simp only [matches_response_id, Insts.CoreCmpPartialEqNumberOrString.eq, read_discriminant,
      Int.not_eq, IScalar.ofInt_val_eq, ne_eq, zero_ne_one, not_false_eq_true, one_ne_zero,
      zero_lt_one, Int.reduceLT, or_false, or_self, IScalar.val_not_eq_imp_not_eq, ↓reduceIte, ho,
      bind_tc_ok, Bool.false_eq_true, reduceCtorEq, Number.injEq, exists_eq_left', false_or]
    rw [← hpo]
    rcases o with _ | k
    · simp only [core.option.Option.Insts.CoreCmpPartialEqOption.eq, bind_tc_ok,
        Bool.false_eq_true, ↓reduceIte, Option.map_none, reduceCtorEq, iff_false,
        Bool.not_eq_true, WP.spec_ok]
    · have hk : k.val = n.val ↔ k = n :=
        ⟨fun h => IScalar.eq_of_val_eq h, fun h => h ▸ rfl⟩
      by_cases h : k = n <;>
        simp only [core.option.Option.Insts.CoreCmpPartialEqOption.eq, liftFun2,
          core.cmp.impls.PartialEqI64.eq, h, decide_true, decide_false, bind_tc_ok,
          Bool.false_eq_true, ↓reduceIte, Option.map_some, Option.some.injEq, hk, iff_true,
          iff_false, Bool.not_eq_true, WP.spec_ok]
  | .String a, .Number m =>
    simp only [matches_response_id, Insts.CoreCmpPartialEqNumberOrString.eq, read_discriminant,
      Int.not_eq, IScalar.ofInt_val_eq, ne_eq, one_ne_zero, not_false_eq_true, zero_ne_one,
      Int.reduceLT, zero_lt_one, or_true, or_self, IScalar.val_not_eq_imp_not_eq, ↓reduceIte,
      bind_tc_ok, Bool.false_eq_true, reduceCtorEq, false_and, exists_const, iff_false,
      Bool.not_eq_true, WP.spec_ok]
  | .String a, .String b =>
    simp only [matches_response_id, Insts.CoreCmpPartialEqNumberOrString.eq, read_discriminant,
      ↓reduceIte, alloc.sync.Arc.Insts.CoreCmpPartialEqArc.eq, Str.Insts.CoreCmpPartialEqStr.eq,
      bind_tc_ok, decide_eq_true_eq, String.injEq, reduceCtorEq, false_and, exists_const,
      or_false]
    have hab : a.data.val = b.data.val ↔ a = b := by
      rcases a with ⟨x⟩
      rcases b with ⟨y⟩
      constructor
      · intro h
        rw [show x = y from Subtype.ext h]
      · intro h
        cases h
        rfl
    by_cases h : a = b <;>
      simp only [hab, h, ↓reduceIte, iff_true, iff_false, Bool.not_eq_true, WP.spec_ok]

end rmcp.model.NumberOrString
