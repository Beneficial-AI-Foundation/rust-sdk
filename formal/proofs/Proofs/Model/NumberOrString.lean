/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Rmcp.Funs
import Defs.JsonRpc
import Proofs.External.IntParse
import Proofs.External.Option

/-!
# Spec theorems for `NumberOrString` (M06, M07)

`numeric_string_value` (M06) parses a string id with `i64::from_str` and keeps `Ok`; its value is
`Defs.JsonRpc.numericValue`, by the S27 deferred law `from_str_eq_parseI64`
(`Proofs/External/IntParse.lean`). `matches_response_id` (M07) is the derived equality, or else a
numeric request id against the parsed response id; its proof uses M06. The `Arc`, `str`,
`Option` and `Result` steps use the signed-off laws of `Proofs/External/{String,Option}.lean`
(`deref_spec`, `eq_str_spec`, `data_val_inj`, `eq_i64_spec` through `eq_i64_some_spec`,
`ok_spec`), not the model bodies.

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
    obtain ⟨d, hd, hdv⟩ :=
      WP.spec_imp_exists (alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref_spec Global a)
    obtain ⟨o, ho, hov⟩ := WP.spec_imp_exists (core.result.Result.ok_spec r)
    simp only [numeric_string_value, hd, hdv, core.str.Str.parse_eq, hr, ho, bind_tc_ok,
      numericValue, WP.spec_ok, hov, ← hp]
    rcases r with n | e <;> rfl

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
    obtain ⟨c, hc, hcv⟩ := WP.spec_imp_exists
      (core.option.Option.Insts.CoreCmpPartialEqOption.eq_i64_some_spec o n)
    rw [hpo] at hcv
    simp only [numericValue, reduceCtorEq, iff_false, Bool.not_eq_true] at hcv
    simp only [matches_response_id, Insts.CoreCmpPartialEqNumberOrString.eq, read_discriminant,
      ↓reduceIte, lift, core.cmp.impls.PartialEqI64.eq, ho, hc, hcv, bind_tc_ok,
      Bool.false_eq_true, decide_eq_true_eq, Number.injEq, numericValue, reduceCtorEq, and_false,
      exists_const, or_false]
    by_cases h : n = m <;>
      simp only [h, ↓reduceIte, iff_true, iff_false, Bool.not_eq_true, WP.spec_ok]
  | .Number n, .String b =>
    obtain ⟨c, hc, hcv⟩ := WP.spec_imp_exists
      (core.option.Option.Insts.CoreCmpPartialEqOption.eq_i64_some_spec o n)
    rw [hpo] at hcv
    simp only [matches_response_id, Insts.CoreCmpPartialEqNumberOrString.eq, read_discriminant,
      Int.not_eq, IScalar.ofInt_val_eq, ne_eq, zero_ne_one, not_false_eq_true, one_ne_zero,
      zero_lt_one, Int.reduceLT, or_false, or_self, IScalar.val_not_eq_imp_not_eq, ↓reduceIte, ho,
      hc, bind_tc_ok, Bool.false_eq_true, reduceCtorEq, Number.injEq, exists_eq_left', false_or]
    cases c <;> simpa only [Bool.false_eq_true, ↓reduceIte, true_iff, false_iff, WP.spec_ok]
      using hcv
  | .String a, .Number m =>
    simp only [matches_response_id, Insts.CoreCmpPartialEqNumberOrString.eq, read_discriminant,
      Int.not_eq, IScalar.ofInt_val_eq, ne_eq, one_ne_zero, not_false_eq_true, zero_ne_one,
      Int.reduceLT, zero_lt_one, or_true, or_self, IScalar.val_not_eq_imp_not_eq, ↓reduceIte,
      bind_tc_ok, Bool.false_eq_true, reduceCtorEq, false_and, exists_const, iff_false,
      Bool.not_eq_true, WP.spec_ok]
  | .String a, .String b =>
    simp only [matches_response_id, Insts.CoreCmpPartialEqNumberOrString.eq, read_discriminant,
      ↓reduceIte, String.injEq, reduceCtorEq, false_and, exists_const, or_false]
    obtain ⟨c, hc, hcv⟩ := WP.spec_imp_exists
      (alloc.sync.Arc.Insts.CoreCmpPartialEqArc.eq_str_spec Global a b)
    rw [alloc.sync.Arc.data_val_inj] at hcv
    simp only [hc, bind_tc_ok]
    cases c <;> simpa only [Bool.false_eq_true, ↓reduceIte, true_iff, false_iff, WP.spec_ok]
      using hcv

end rmcp.model.NumberOrString
