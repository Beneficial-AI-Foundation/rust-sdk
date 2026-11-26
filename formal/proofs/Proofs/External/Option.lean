/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Rmcp.Funs

@[expose] public section

/-!
# Laws of the Phase 2 external models: Option (plan steps S26/S27, stage 6)

Proofs of the Phase 2 laws signed off by the spec owner on 2026-11-23 (plan steps S26/S27),
restated in `formal/proofs/Proofs/Internal/External.lean` (Phase 2 part); the draft file was removed at
incorporation. For this group (spec owner sign-off 2026-11-23). Filled in by the stage-6 prover.
`core.option.Option.or_else_spec` was added on 2026-11-25 (human decision: every external reached
by the translation has a `_spec` theorem).
-/

open Aeneas Aeneas.Std Result
open rmcp ExtModel

/-- `Option::or_else` on `Some x`: `Some x`; the closure is not called. -/
theorem core.option.Option.or_else_some {T : Type} {F : Type}
    (opsfunctionFnOnceFTupleOptionInst : core.ops.function.FnOnce F Unit (Option T))
    (x : T) (f : F) :
    core.option.Option.or_else opsfunctionFnOnceFTupleOptionInst (some x) f = ok (some x) := by
  rfl

/-- `Option::or_else` on `None`: the result of the closure, through its `FnOnce` instance,
including its failure. -/
theorem core.option.Option.or_else_none {T : Type} {F : Type}
    (opsfunctionFnOnceFTupleOptionInst : core.ops.function.FnOnce F Unit (Option T))
    (f : F) :
    core.option.Option.or_else opsfunctionFnOnceFTupleOptionInst none f =
      opsfunctionFnOnceFTupleOptionInst.call_once f () := by
  rfl

/-- **Spec theorem for `Option::or_else`**, for every closure instance: a postcondition `P` holds
of the result when it holds of `Some x` for `self = Some x` (the closure is not called) and the
closure's `call_once` meets it for `self = None` (`or_else_some`, `or_else_none`). -/
theorem core.option.Option.or_else_spec {T : Type} {F : Type}
    (opsfunctionFnOnceFTupleOptionInst : core.ops.function.FnOnce F Unit (Option T))
    (self : Option T) (f : F) (P : Option T → Prop) (hsome : ∀ x, self = some x → P (some x))
    (hnone : self = none → opsfunctionFnOnceFTupleOptionInst.call_once f () ⦃ P ⦄) :
    core.option.Option.or_else opsfunctionFnOnceFTupleOptionInst self f ⦃ P ⦄ := by
  cases self with
  | some x => simp only [core.option.Option.or_else, WP.spec_ok]; exact hsome x rfl
  | none => exact hnone rfl

/-- `<Option<T> as PartialEq>::eq`, for every instance of `T`: `Some l == Some r` is `l == r`
through the instance (including its failure); a `Some` and a `None` are unequal; two `None`
are equal. -/
theorem core.option.Option.Insts.CoreCmpPartialEqOption.eq_eq {T : Type}
    (cmpPartialEqInst : core.cmp.PartialEq T T) (l r : T) :
    core.option.Option.Insts.CoreCmpPartialEqOption.eq cmpPartialEqInst (some l) (some r) =
        cmpPartialEqInst.eq l r ∧
      core.option.Option.Insts.CoreCmpPartialEqOption.eq cmpPartialEqInst (some l) none =
        ok false ∧
      core.option.Option.Insts.CoreCmpPartialEqOption.eq cmpPartialEqInst none (some r) =
        ok false ∧
      core.option.Option.Insts.CoreCmpPartialEqOption.eq cmpPartialEqInst none none =
        ok true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **Spec theorem for `<Option<T> as PartialEq>::eq`** for an instance that decides equality
on the values compared: the result is `true` exactly when the two options are equal. -/
theorem core.option.Option.Insts.CoreCmpPartialEqOption.eq_spec {T : Type}
    (cmpPartialEqInst : core.cmp.PartialEq T T) (self : Option T) (other : Option T)
    (h_inst : ∀ l r, self = some l → other = some r →
      cmpPartialEqInst.eq l r ⦃ (b : Bool) => (b = true ↔ l = r) ⦄) :
    core.option.Option.Insts.CoreCmpPartialEqOption.eq cmpPartialEqInst self other
      ⦃ (result : Bool) => (result = true ↔ self = other) ⦄ := by
  match self, other with
  | some l, some r =>
    have h := h_inst l r rfl rfl
    simp only [core.option.Option.Insts.CoreCmpPartialEqOption.eq, Option.some.injEq]
    exact h
  | some _, none => simp only [core.option.Option.Insts.CoreCmpPartialEqOption.eq, reduceCtorEq,
                      iff_false, Bool.not_eq_true, WP.spec_ok]
  | none, some _ => simp only [core.option.Option.Insts.CoreCmpPartialEqOption.eq, reduceCtorEq,
                      iff_false, Bool.not_eq_true, WP.spec_ok]
  | none, none => simp only [core.option.Option.Insts.CoreCmpPartialEqOption.eq, iff_true,
                    WP.spec_ok]

/-- **Spec theorem for `<Option<i64> as PartialEq>::eq`** at the instance of the translation
(`core.cmp.PartialEqI64`, value equality): option equality. -/
@[step]
theorem core.option.Option.Insts.CoreCmpPartialEqOption.eq_i64_spec
    (self : Option I64) (other : Option I64) :
    core.option.Option.Insts.CoreCmpPartialEqOption.eq core.cmp.PartialEqI64 self other
      ⦃ (result : Bool) => (result = true ↔ self = other) ⦄ := by
  apply core.option.Option.Insts.CoreCmpPartialEqOption.eq_spec
  intro l r _ _
  simp only [liftFun2, core.cmp.impls.PartialEqI64.eq, WP.spec_ok, decide_eq_true_eq]

/-- `<Option<i64> as PartialEq>::eq` against `Some n` compares the values: `eq_i64_spec` with
the right-hand side a `Some`, as M07 uses it to compare the parsed response id with the numeric
request id. -/
theorem core.option.Option.Insts.CoreCmpPartialEqOption.eq_i64_some_spec
    (self : Option I64) (n : I64) :
    core.option.Option.Insts.CoreCmpPartialEqOption.eq core.cmp.PartialEqI64 self (some n)
      ⦃ (result : Bool) => (result = true ↔ self.map (·.val) = some n.val) ⦄ := by
  rw [← Option.map_some, (Option.map_injective (fun _ _ => IScalar.eq_of_val_eq)).eq_iff]
  exact core.option.Option.Insts.CoreCmpPartialEqOption.eq_i64_spec self (some n)

/-- **Spec theorem for `Result::ok`**: `Ok x ↦ Some x`, `Err _ ↦ None`; never fails. -/
@[step]
theorem core.result.Result.ok_spec {T : Type} {E : Type} (self : core.result.Result T E) :
    core.result.Result.ok self ⦃ (result : Option T) =>
      result = match self with
        | core.result.Result.Ok x => some x
        | core.result.Result.Err _ => none ⦄ := by
  match self with
  | core.result.Result.Ok _ => simp only [core.result.Result.ok, WP.spec_ok]
  | core.result.Result.Err _ => simp only [core.result.Result.ok, WP.spec_ok]
