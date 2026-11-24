/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Rmcp.Funs
import Defs.Sse

/-!
# Spec theorems for `SseEventSizeLimiter` (T01–T03, C01, C02)

The limiter that bounds the size of one server-sent event: `check_limit` (T01) tests
`sat(retained_size + line_size) ≤ max_size`; `finish_line` (T02) folds the current line into the
retained size; `observe` (T03) feeds a chunk byte by byte, ending lines at CR, LF and CR LF (also
across chunks), and stops at the first byte whose check fails. The composition theorems say that
chunk boundaries do not change the result (C01, `SseEventSizeLimiter.observe_append` and its
corollary) and that an accepted chunk keeps the bound (C02, two forms).

Source: "crates/rmcp/src/transport/common/client_side_sse.rs", lines 48 (`observe`),
75 (`finish_line`) and 90 (`check_limit`) at upstream `7caec76` (not touched by patch 01).

Proof outline. `check_limit` and `finish_line` are unfolded directly (equations
`check_limit_eq`, `finish_line_eq`). One iteration of the translated loop is one
`Defs.Sse.step` (`observe_loop_body_eq`), so the loop is the fold `Defs.Sse.observe` by
induction on the number of remaining bytes (`observe_loop_eq`). Since `Defs.Sse.ofLimiter` is
injective, C01 follows from the model fact `Defs.Sse.observe_append`, and C02 from the model
invariant that a successful step keeps the bound and `maxSize` (`withinLimit_observe`).
-/

open Aeneas Aeneas.Std Result
open rmcp.transport.common.client_side_sse
open core.result.Result.Insts

namespace Proofs.ClientSideSse

/-! ## Model-level helpers -/

/-- `usize::saturating_add` is `Defs.Sse.satAdd` with the cap `Usize.max`, on values. -/
theorem saturating_add_val (x y : Usize) :
    (core.num.Usize.saturating_add x y).val = Defs.Sse.satAdd Usize.max x.val y.val := by
  simp only [core.num.Usize.saturating_add, UScalar.saturating_add, Defs.Sse.satAdd]
  have hm : UScalar.max .Usize = Usize.max := UScalar.max_USize_eq
  rw [hm]
  have h1 : Usize.max < 2 ^ UScalarTy.Usize.numBits := by
    have := UScalar.max_USize_eq; rw [← this, UScalar.max]; simp
  simp only [UScalar.val, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- `Defs.Sse.ofLimiter` is injective: a `Usize` is determined by its value. -/
theorem ofLimiter_injective : Function.Injective Defs.Sse.ofLimiter := by
  rintro ⟨a1, a2, a3, a4, a5⟩ ⟨b1, b2, b3, b4, b5⟩ h
  simp only [Defs.Sse.ofLimiter, Defs.Sse.State.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have e1 : a1 = b1 := UScalar.eq_of_val_eq h1
  have e2 : a2 = b2 := UScalar.eq_of_val_eq h2
  have e3 : a3 = b3 := UScalar.eq_of_val_eq h3
  subst e1 e2 e3 h4 h5; rfl

/-- A successful `Defs.Sse.step` from a state within the bound leaves a state within the bound,
with the same `maxSize`. -/
theorem withinLimit_step (st : Defs.Sse.State) (x : U8)
    (hb : Defs.Sse.withinLimit Usize.max st = true)
    (hok : (Defs.Sse.step Usize.max st x).ok = true) :
    Defs.Sse.withinLimit Usize.max (Defs.Sse.step Usize.max st x).state = true ∧
      (Defs.Sse.step Usize.max st x).state.maxSize = st.maxSize := by
  unfold Defs.Sse.step at hok ⊢
  by_cases h1 : st.previousWasCr = true ∧ x.val = 10
  · rw [if_pos h1]; exact ⟨by simpa [Defs.Sse.withinLimit] using hb, rfl⟩
  rw [if_neg h1] at hok ⊢
  by_cases h13 : x.val = 13
  · rw [if_pos h13] at hok ⊢
    simp only at hok ⊢
    by_cases ho : (Defs.Sse.finishLine Usize.max { st with previousWasCr := false }).ok = true
    · rw [if_pos ho] at hok ⊢
      exact ⟨by simpa [Defs.Sse.withinLimit, Defs.Sse.finishLine] using ho, rfl⟩
    · rw [if_neg ho] at hok; exact absurd hok ho
  rw [if_neg h13] at hok ⊢
  simp only at hok ⊢
  by_cases h10 : x.val = 10
  · rw [if_pos h10] at hok ⊢
    exact ⟨hok, rfl⟩
  · rw [if_neg h10] at hok ⊢
    exact ⟨hok, rfl⟩

/-- A successful `Defs.Sse.observe` from a state within the bound leaves a state within the
bound, with the same `maxSize`. -/
theorem withinLimit_observe (st : Defs.Sse.State) (l : List U8)
    (hb : Defs.Sse.withinLimit Usize.max st = true)
    (hok : (Defs.Sse.observe Usize.max st l).ok = true) :
    Defs.Sse.withinLimit Usize.max (Defs.Sse.observe Usize.max st l).state = true ∧
      (Defs.Sse.observe Usize.max st l).state.maxSize = st.maxSize := by
  induction l generalizing st with
  | nil => exact ⟨hb, rfl⟩
  | cons x xs ih =>
    simp only [Defs.Sse.observe] at hok ⊢
    split at hok
    · rename_i hs
      rw [if_pos hs]
      obtain ⟨h1, h2⟩ := withinLimit_step st x hb hs
      obtain ⟨h3, h4⟩ := ih _ h1 hok
      exact ⟨h3, h4.trans h2⟩
    · simp_all

/-! ## `check_limit` and `finish_line` as equations -/

/-- `check_limit` returns the verdict of `Defs.Sse.withinLimit` on the state of `self`. -/
theorem check_limit_eq (self : SseEventSizeLimiter) :
    SseEventSizeLimiter.check_limit self =
      ok (Defs.Sse.toResult (Defs.Sse.withinLimit Usize.max (Defs.Sse.ofLimiter self))) := by
  unfold SseEventSizeLimiter.check_limit
  simp only [lift, bind_tc_ok, Defs.Sse.toResult, Defs.Sse.withinLimit, Defs.Sse.ofLimiter]
  split <;> rename_i h <;> simp_all [saturating_add_val]

/-- `finish_line` returns the verdict of `Defs.Sse.finishLine` and a state whose model is the
state of `Defs.Sse.finishLine`. -/
theorem finish_line_eq (self : SseEventSizeLimiter) :
    ∃ s', SseEventSizeLimiter.finish_line self =
      ok (Defs.Sse.toResult (Defs.Sse.finishLine Usize.max (Defs.Sse.ofLimiter self)).ok, s') ∧
      Defs.Sse.ofLimiter s' = (Defs.Sse.finishLine Usize.max (Defs.Sse.ofLimiter self)).state := by
  unfold SseEventSizeLimiter.finish_line
  have key : ∀ i : Usize, i.val = (if self.line_size.val = 0 then 0
      else if self.line_is_comment then self.retained_size.val
      else Defs.Sse.satAdd Usize.max
        (Defs.Sse.satAdd Usize.max self.retained_size.val self.line_size.val) 1) →
      ∃ s', (do
          let r ← SseEventSizeLimiter.check_limit
            { self with retained_size := i, line_size := 0#usize, line_is_comment := false }
          ok (r,
            { self with retained_size := i, line_size := 0#usize, line_is_comment := false })) =
        ok (Defs.Sse.toResult (Defs.Sse.finishLine Usize.max (Defs.Sse.ofLimiter self)).ok, s') ∧
        Defs.Sse.ofLimiter s' =
          (Defs.Sse.finishLine Usize.max (Defs.Sse.ofLimiter self)).state := by
    intro i hi
    refine ⟨{ self with retained_size := i, line_size := 0#usize, line_is_comment := false },
      ?_, ?_⟩
    · rw [check_limit_eq]
      simp [Defs.Sse.finishLine, Defs.Sse.ofLimiter, hi]
    · simp [Defs.Sse.finishLine, Defs.Sse.ofLimiter, hi]
  split
  · apply key; simp_all
  · split
    · apply key; simp_all
    · simp only [lift, bind_tc_ok]; apply key; simp_all [saturating_add_val]

/-! ## One loop iteration is one `Defs.Sse.step` -/

/-- `?` on a verdict: `Continue` for `Ok(())`, `Break (Err(()))` for `Err(())`. -/
theorem branch_eq (x : core.result.Result Unit Unit) :
    CoreOpsTry.branch x =
      ok (match x with | .Ok v => .Continue v | .Err e => .Break (.Err e)) := by
  cases x <;> rfl

/-- The residual of `?` converts back to `Err(())`. -/
theorem from_residual_eq (e : Unit) :
    CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame Unit)
      (.Err e) = ok (.Err ()) := by
  rfl

/-- One iteration of the translated loop on a byte `b` is one `Defs.Sse.step`: it continues
with the stepped state when the step succeeds, and stops with `Err(())` and that state when it
fails. -/
theorem observe_loop_body_eq (iter iter1 : core.slice.iter.Iter U8) (b : U8)
    (hnext : core.slice.iter.IteratorSliceIter.next iter = ok (some b, iter1))
    (st : SseEventSizeLimiter) :
    ∃ st', Defs.Sse.ofLimiter st' = (Defs.Sse.step Usize.max (Defs.Sse.ofLimiter st) b).state ∧
      SseEventSizeLimiter.observe_loop.body iter st =
        ok (if (Defs.Sse.step Usize.max (Defs.Sse.ofLimiter st) b).ok
            then .cont (iter1, st') else .done (.Err (), st')) := by
  unfold SseEventSizeLimiter.observe_loop.body
  rw [hnext]
  simp only [bind_tc_ok, uncurry_apply_pair]
  obtain ⟨s1, hfl1, hs1⟩ := finish_line_eq { st with previous_was_cr := false }
  rcases st with ⟨m, r, l, c, p⟩
  simp only [Defs.Sse.ofLimiter] at hs1 hfl1 ⊢
  -- the line-end branches (CR, LF), with `setCr` for CR
  have finCase : ∀ (setCr : Bool) (st0 : Defs.Sse.State) (s2 : SseEventSizeLimiter)
      (hs2 : Defs.Sse.ofLimiter s2 = (Defs.Sse.finishLine Usize.max st0).state),
      ∃ st', Defs.Sse.ofLimiter st' = (let o := Defs.Sse.finishLine Usize.max st0
          if setCr then (if o.ok then
            (⟨true, { o.state with previousWasCr := true }⟩ : Defs.Sse.Outcome) else o)
          else o).state ∧
        (do
          let cf ← CoreOpsTry.branch (Defs.Sse.toResult (Defs.Sse.finishLine Usize.max st0).ok)
          match cf with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            ok (ControlFlow.cont (iter1,
              if setCr then { s2 with previous_was_cr := true } else s2))
          | core.ops.control_flow.ControlFlow.Break residual => do
            let r1 ← CoreOpsTryTraitFromResidualResultInfallible.from_residual
                Unit (core.convert.FromSame Unit) residual
            ok (ControlFlow.done (r1, s2))) =
        ok (if (let o := Defs.Sse.finishLine Usize.max st0
          if setCr then (if o.ok then
            (⟨true, { o.state with previousWasCr := true }⟩ : Defs.Sse.Outcome) else o)
          else o).ok
            then .cont (iter1, st') else .done (.Err (), st')) := by
    intro setCr st0 s2 hs2
    generalize Defs.Sse.finishLine Usize.max st0 = F at hs2 ⊢
    rcases F with ⟨ok1, F⟩
    cases ok1 <;> cases setCr
    all_goals first
      | exact ⟨s2, by simpa using hs2, by simp [Defs.Sse.toResult, branch_eq, from_residual_eq]⟩
      | exact ⟨{ s2 with previous_was_cr := true }, by simp only at hs2 ⊢; rw [← hs2]; rfl,
          by simp [Defs.Sse.toResult, branch_eq]⟩
  have h13v : b ≠ 13#u8 → b.val ≠ 13 := by
    intro hb hv; apply hb; apply UScalar.eq_of_val_eq; simpa using hv
  have h10v : b ≠ 10#u8 → b.val ≠ 10 := by
    intro hb hv; apply hb; apply UScalar.eq_of_val_eq; simpa using hv
  have hmodel : ∀ p, b ≠ 13#u8 → b ≠ 10#u8 →
      Defs.Sse.step Usize.max ⟨m.val, r.val, l.val, c, p⟩ b =
        let R : SseEventSizeLimiter := ⟨m, r, core.num.Usize.saturating_add l 1#usize,
          (if l = 0#usize then decide (b = 58#u8) else c), false⟩
        ⟨Defs.Sse.withinLimit Usize.max (Defs.Sse.ofLimiter R), Defs.Sse.ofLimiter R⟩ := by
    intro p hb13 hb10
    have := h13v hb13; have := h10v hb10
    by_cases hl : l = 0#usize
    · subst hl
      have h58 : (b.val = 58) ↔ b = 58#u8 :=
        ⟨fun hv => UScalar.eq_of_val_eq (by simpa using hv), fun hb => by subst hb; rfl⟩
      simp [Defs.Sse.step, Defs.Sse.ofLimiter, saturating_add_val, *]
    · have hl' : l.val ≠ 0 := by intro h; apply hl; apply UScalar.eq_of_val_eq; simpa using h
      simp_all [Defs.Sse.step, Defs.Sse.ofLimiter, saturating_add_val]
  have hcl := check_limit_eq ⟨m, r, core.num.Usize.saturating_add l 1#usize,
          (if l = 0#usize then decide (b = 58#u8) else c), false⟩
  -- the branch of any other byte
  have otherCase : ∀ (p : Bool), b ≠ 13#u8 → b ≠ 10#u8 → ∃ st',
      Defs.Sse.ofLimiter st' = (Defs.Sse.step Usize.max ⟨m.val, r.val, l.val, c, p⟩ b).state ∧
      (do
        let b ← if l = 0#usize then ok (decide (b = 58#u8)) else ok c
        let i ← lift (core.num.Usize.saturating_add l 1#usize)
        let r_1 ← SseEventSizeLimiter.check_limit ⟨m, r, i, b, false⟩
        let cf ← CoreOpsTry.branch r_1
        match cf with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          ok (ControlFlow.cont (iter1, (⟨m, r, i, b, false⟩ : SseEventSizeLimiter)))
        | core.ops.control_flow.ControlFlow.Break residual => do
          let r1 ← CoreOpsTryTraitFromResidualResultInfallible.from_residual
              Unit (core.convert.FromSame Unit) residual
          ok (ControlFlow.done (r1, (⟨m, r, i, b, false⟩ : SseEventSizeLimiter)))) =
      ok (if (Defs.Sse.step Usize.max ⟨m.val, r.val, l.val, c, p⟩ b).ok
          then .cont (iter1, st') else .done (.Err (), st')) := by
    intro p hb13 hb10
    rw [hmodel p hb13 hb10]
    refine ⟨_, rfl, ?_⟩
    have hif : (if l = 0#usize then ok (decide (b = 58#u8)) else ok c : Result Bool) =
        ok (if l = 0#usize then decide (b = 58#u8) else c) := by split <;> rfl
    rw [hif]
    simp only [bind_tc_ok, lift, hcl]
    have helper : ∀ (x : Bool) (R : SseEventSizeLimiter),
        (do
          let cf ← CoreOpsTry.branch (Defs.Sse.toResult x)
          match cf with
          | core.ops.control_flow.ControlFlow.Continue _ => ok (ControlFlow.cont (iter1, R))
          | core.ops.control_flow.ControlFlow.Break residual => do
            let r1 ← CoreOpsTryTraitFromResidualResultInfallible.from_residual
                Unit (core.convert.FromSame Unit) residual
            ok (ControlFlow.done (r1, R))) =
        ok (if x = true then .cont (iter1, R) else .done (.Err (), R)) := by
      intro x R; cases x <;> rfl
    exact helper _ _
  cases p
  · simp only [Bool.false_eq_true, if_false]
    by_cases h13 : b = 13#u8
    · subst h13
      obtain ⟨s2, hfl2, hs2⟩ := finish_line_eq ⟨m, r, l, c, false⟩
      rw [hfl2]
      exact finCase true _ s2 hs2
    by_cases h10 : b = 10#u8
    · subst h10
      obtain ⟨s2, hfl2, hs2⟩ := finish_line_eq ⟨m, r, l, c, false⟩
      rw [hfl2]
      exact finCase false _ s2 hs2
    -- `b` is neither CR nor LF: the default arm of the match on `byte`
    split
    · contradiction
    · contradiction
    · exact otherCase false h13 h10
  · simp only [if_true]
    by_cases h10 : b = 10#u8
    · subst h10
      refine ⟨⟨m, r, l, c, false⟩, rfl, ?_⟩
      rfl
    simp only [h10, if_false]
    by_cases h13 : b = 13#u8
    · subst h13
      rw [hfl1]
      exact finCase true _ s1 hs1
    split
    · contradiction
    · contradiction
    · exact otherCase true h13 h10

/-! ## The loop is the fold `Defs.Sse.observe` -/

/-- The slice iterator yields the byte at position `i` while `i` is in range. -/
theorem next_of_lt (s : Slice U8) (i : Nat) (h : i < s.val.length) :
    core.slice.iter.IteratorSliceIter.next (⟨s, i⟩ : core.slice.iter.Iter U8) =
      ok (some s.val[i], ⟨s, i + 1⟩) := by
  have hlen : i < s.len.val := by simpa [Slice.len] using h
  simp only [core.slice.iter.IteratorSliceIter.next, dif_pos hlen]
  rfl

/-- The slice iterator yields `none` at the end of the slice. -/
theorem next_of_le (s : Slice U8) (i : Nat) (h : s.val.length ≤ i) :
    core.slice.iter.IteratorSliceIter.next (⟨s, i⟩ : core.slice.iter.Iter U8) =
      ok (none, ⟨s, i⟩) := by
  have hlen : ¬ i < s.len.val := by simp [Slice.len]; omega
  simp only [core.slice.iter.IteratorSliceIter.next, dif_neg hlen]

/-- The translated loop from position `i` is `Defs.Sse.observe` on the bytes from `i` on, by
induction on the number `n` of remaining bytes. -/
theorem observe_loop_eq (s : Slice U8) : ∀ n i st, s.val.length - i = n →
    ∃ st', SseEventSizeLimiter.observe_loop ⟨s, i⟩ st =
      ok (Defs.Sse.toResult
        (Defs.Sse.observe Usize.max (Defs.Sse.ofLimiter st) (s.val.drop i)).ok, st') ∧
      Defs.Sse.ofLimiter st' =
        (Defs.Sse.observe Usize.max (Defs.Sse.ofLimiter st) (s.val.drop i)).state := by
  intro n
  induction n with
  | zero =>
    intro i st hn
    refine ⟨st, ?_, ?_⟩
    · have hge : s.val.length ≤ i := by omega
      rw [SseEventSizeLimiter.observe_loop, loop]
      have hb : SseEventSizeLimiter.observe_loop.body ⟨s, i⟩ st = ok (.done (.Ok (), st)) := by
        unfold SseEventSizeLimiter.observe_loop.body
        rw [next_of_le s i hge]
        rfl
      simp only [hb, List.drop_eq_nil_of_le hge]
      rfl
    · rw [List.drop_eq_nil_of_le (by omega)]; rfl
  | succ n ih =>
    intro i st hn
    have hlt : i < s.val.length := by omega
    obtain ⟨st1, hst1, hb⟩ :=
      observe_loop_body_eq ⟨s, i⟩ ⟨s, i + 1⟩ s.val[i] (next_of_lt s i hlt) st
    rw [List.drop_eq_getElem_cons hlt, Defs.Sse.observe.eq_2]
    rw [SseEventSizeLimiter.observe_loop, loop]
    simp only [hb]
    cases hok : (Defs.Sse.step Usize.max (Defs.Sse.ofLimiter st) s.val[i]).ok
    · refine ⟨st1, ?_, ?_⟩
      · simp only [hok, if_false, Bool.false_eq_true]; rfl
      · simp only [if_false, Bool.false_eq_true]; exact hst1
    · obtain ⟨st2, h2, h3⟩ := ih (i + 1) st1 (by omega)
      refine ⟨st2, ?_, ?_⟩
      · simp only [if_true]
        rw [← hst1]
        exact h2
      · simp only [if_true]
        rw [← hst1]; exact h3

/-- `observe` returns the verdict of `Defs.Sse.observe` and a state whose model is the state of
`Defs.Sse.observe`. -/
theorem observe_eq (self : SseEventSizeLimiter) (chunk : Slice U8) :
    ∃ st', SseEventSizeLimiter.observe self chunk =
      ok (Defs.Sse.toResult
        (Defs.Sse.observe Usize.max (Defs.Sse.ofLimiter self) chunk.val).ok, st') ∧
      Defs.Sse.ofLimiter st' =
        (Defs.Sse.observe Usize.max (Defs.Sse.ofLimiter self) chunk.val).state := by
  unfold SseEventSizeLimiter.observe
  obtain ⟨st', h1, h2⟩ := observe_loop_eq chunk _ 0 self rfl
  simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,
    bind_tc_ok, h1, List.drop_zero] at h2 ⊢
  exact ⟨st', rfl, h2⟩

end Proofs.ClientSideSse

namespace rmcp.transport.common.client_side_sse.SseEventSizeLimiter

/-! ## Spec theorems T03, T02, T01, in Rust source order -/

/-- **Spec theorem for
`rmcp::transport::common::client_side_sse::SseEventSizeLimiter::observe`** (T03)

The call never fails. Its result and its final `self` are those of `Defs.Sse.observe`: the left
fold of `Defs.Sse.step` over the bytes of `chunk`, from the state of `self`, stopping at the
first byte whose step fails (plan Section 16.2, T03; `client_side_sse.rs` lines 48–73,
`for &byte in chunk` with `?` on `finish_line` and `check_limit`). So CR, LF and CR LF each end
one line; a CR at the end of one call and an LF at the start of the next are one line end
(`previous_was_cr`, lines 50–55); a line whose first byte is `:` is a comment (line 65); an
empty chunk returns `Ok(())` with `self` unchanged; on `Err(())`, `self` is the state reached
at the failing byte, with the bytes after it unread, and when a CR byte fails,
`previous_was_cr` is `false` (plan Section 17). `max_size` never changes. No premise. -/
@[step]
theorem observe_spec (self : SseEventSizeLimiter) (chunk : Slice U8) :
    observe self chunk ⦃ (result : core.result.Result Unit Unit × SseEventSizeLimiter) =>
      Defs.Sse.ofLimiter result.2 =
        (Defs.Sse.observe Usize.max (Defs.Sse.ofLimiter self) chunk.val).state ∧
      result.1 = Defs.Sse.toResult
        (Defs.Sse.observe Usize.max (Defs.Sse.ofLimiter self) chunk.val).ok ⦄ := by
  obtain ⟨st', h1, h2⟩ := Proofs.ClientSideSse.observe_eq self chunk
  rw [h1, WP.spec_ok]
  exact ⟨h2, rfl⟩

/-- **Spec theorem for
`rmcp::transport::common::client_side_sse::SseEventSizeLimiter::finish_line`** (T02)

The call never fails. The new `self` is `Defs.Sse.finishLine` of the old one: an empty line
(`line_size = 0`) resets `retained_size` to 0; a non-comment line adds `line_size + 1` to it,
saturating at `usize::MAX` (the `+ 1` is the newline that joins `data` values; a line end
counts one byte whatever its form, so this is not the raw byte size); a comment line
leaves it unchanged; then `line_size := 0` and `line_is_comment := false`; `max_size` and
`previous_was_cr` are unchanged (plan Section 16.2, T02; `client_side_sse.rs` lines 75–86). The
result is T01 on the new state: `Err(())` exactly when the saturating sum of the new
`retained_size` and `line_size` (which is 0) exceeds `max_size` (line 87). No premise. -/
@[step]
theorem finish_line_spec (self : SseEventSizeLimiter) :
    finish_line self ⦃ (result : core.result.Result Unit Unit × SseEventSizeLimiter) =>
      Defs.Sse.ofLimiter result.2 =
        (Defs.Sse.finishLine Usize.max (Defs.Sse.ofLimiter self)).state ∧
      result.1 =
        Defs.Sse.toResult (Defs.Sse.withinLimit Usize.max (Defs.Sse.ofLimiter result.2)) ⦄ := by
  obtain ⟨s', h, hs⟩ := Proofs.ClientSideSse.finish_line_eq self
  rw [h, WP.spec_ok]
  exact ⟨hs, by rw [hs]; rfl⟩

/-- **Spec theorem for
`rmcp::transport::common::client_side_sse::SseEventSizeLimiter::check_limit`** (T01)

The call never fails. `Err(())` exactly when `sat(retained_size + line_size) > max_size`, with
`sat` the sum saturating at `usize::MAX`; `Ok(())` otherwise, so a sum exactly at `max_size`
passes (plan Section 16.2, T01; Section 22; `client_side_sse.rs` lines 90–96). Stated as
`Defs.Sse.toResult` of `Defs.Sse.withinLimit` (`decide (satAdd Usize.max retained_size
line_size ≤ max_size)`) on the state of `self`, the form in which T02 and T03 use the verdict.
It takes `&self`, so it returns no state. No premise. -/
@[step]
theorem check_limit_spec (self : SseEventSizeLimiter) :
    check_limit self ⦃ (result : core.result.Result Unit Unit) =>
      result = Defs.Sse.toResult
        (Defs.Sse.withinLimit Usize.max (Defs.Sse.ofLimiter self)) ⦄ := by
  rw [Proofs.ClientSideSse.check_limit_eq, WP.spec_ok]

/-! ## Composition theorems C01, C02 (plan Section 16.4) -/

/-- **C01** (former plan name `sse_observe_append`), general form: chunk boundaries do not change
the limiter. `observe` on the concatenation `ab = a ++ b` from `self` is `observe` on `a` from
`self`, followed, if that returns `Ok(())` with state `s`, by `observe` on `b` from `s`; if it
returns `Err(())` with state `s`, the call on `ab` returns `Err(())` with the same state `s`
(the bytes of `b` are not read). Result and state, including when a CR LF is split between `a`
and `b` (plan Section 16.4, C01; uses T03; `client_side_sse.rs` lines 48–73: `for &byte in
chunk` with `?`). The model-level fact is `Defs.Sse.observe_append`. About the translated
function `SseEventSizeLimiter::observe`. No call is assumed to succeed. The premise `h_ab`
names the concatenation as a slice, since `Slice U8` is bounded by `Usize.max`. Not tagged
`@[step]`. -/
theorem observe_append (self : SseEventSizeLimiter) (a b ab : Slice U8)
    (h_ab : ab.val = a.val ++ b.val) :
    observe self ab = (do
      let (r, s) ← observe self a
      match r with
      | .Ok () => observe s b
      | .Err () => ok (.Err (), s)) := by
  obtain ⟨sab, hab, hsab⟩ := Proofs.ClientSideSse.observe_eq self ab
  obtain ⟨sa, ha, hsa⟩ := Proofs.ClientSideSse.observe_eq self a
  rw [hab, ha, h_ab, Defs.Sse.observe_append] at *
  simp only [bind_tc_ok, uncurry_apply_pair]
  revert hsab hab
  cases hoka : (Defs.Sse.observe Usize.max (Defs.Sse.ofLimiter self) a.val).ok
  · simp only [hoka, Bool.false_eq_true, if_false]
    intro _ hsab
    have : sab = sa := Proofs.ClientSideSse.ofLimiter_injective (hsab.trans hsa.symm)
    subst this; rfl
  · simp only [hoka, if_true]
    intro _ hsab
    obtain ⟨sb, hb, hsb⟩ := Proofs.ClientSideSse.observe_eq sa b
    show _ = observe sa b
    rw [hb, hsa] at *
    have : sab = sb := Proofs.ClientSideSse.ofLimiter_injective (hsab.trans hsb.symm)
    subst this; rfl

/-- **C01** (former plan name `sse_observe_append`), in the plan's form: if `observe` on `a` from
`self` returns `Ok(())` with state `self'`, then `observe` on the concatenation `ab = a ++ b`
from `self` returns exactly what `observe` on `b` from `self'` returns, result and state (plan
Section 16.4, C01; uses T03; `client_side_sse.rs` lines 48–73). A corollary of
`observe_append`. About the translated function `SseEventSizeLimiter::observe`. It takes a
successful call on `a` as its hypothesis and covers only that case; it does not show that any
call succeeds (T03 shows that every call returns). Not tagged `@[step]`. -/
theorem observe_append_of_observe_eq_ok (self self' : SseEventSizeLimiter) (a b ab : Slice U8)
    (h_ab : ab.val = a.val ++ b.val)
    (h_a : observe self a = ok (.Ok (), self')) :
    observe self ab = observe self' b := by
  rw [observe_append self a b ab h_ab, h_a]; rfl

/-- **C02** (former plan name `sse_observe_bound`): the limiter's memory guarantee at each chunk
boundary. If the bound `sat(retained_size + line_size) ≤ max_size` (saturating at
`usize::MAX`) holds for `self` and `observe` on `chunk` returns `Ok(())` with state `self'`,
then it holds for `self'`, and `max_size` is unchanged; so at the end of every accepted chunk
the limiter retains at most `max_size` counted bytes of the current event (plan Section 16.4,
C02; uses T01–T03; `client_side_sse.rs` lines 48–96). The theorem says nothing about the
states inside the chunk; the corollary below covers every prefix of an accepted chunk. The
premise `h_bound` is needed: an empty chunk and an LF that completes a CR LF check nothing
(plan Section 17), so without it a state over the bound would be accepted with its sizes
unchanged (an absorbed LF still clears `previous_was_cr`, lines 50–55). It matters only when
`chunk` is `[]`, or is a single LF and `self` has a pending CR: every other accepted chunk ends
with a checked byte that passed, or with an absorbed LF whose CR came earlier in the same chunk
and passed its check, with no size change in between. A fresh
limiter (`new`, lines 38–46: both sizes 0) satisfies it. About the translated function
`SseEventSizeLimiter::observe`. It takes a successful call as its hypothesis and covers only
that case; it does not show that any call succeeds. Not tagged `@[step]`. -/
theorem max_size_eq_and_satAdd_le_of_observe_eq_ok (self self' : SseEventSizeLimiter)
    (chunk : Slice U8)
    (h_bound :
      Defs.Sse.satAdd Usize.max self.retained_size.val self.line_size.val ≤ self.max_size.val)
    (h_ok : observe self chunk = ok (.Ok (), self')) :
    self'.max_size = self.max_size ∧
    Defs.Sse.satAdd Usize.max self'.retained_size.val self'.line_size.val ≤
      self'.max_size.val := by
  obtain ⟨st', h1, h2⟩ := Proofs.ClientSideSse.observe_eq self chunk
  rw [h1] at h_ok
  simp only [ok.injEq, Prod.mk.injEq] at h_ok
  obtain ⟨hr, rfl⟩ := h_ok
  have hok : (Defs.Sse.observe Usize.max (Defs.Sse.ofLimiter self) chunk.val).ok = true := by
    revert hr
    cases (Defs.Sse.observe Usize.max (Defs.Sse.ofLimiter self) chunk.val).ok <;>
      simp [Defs.Sse.toResult]
  have hb : Defs.Sse.withinLimit Usize.max (Defs.Sse.ofLimiter self) = true := by
    simpa [Defs.Sse.withinLimit, Defs.Sse.ofLimiter] using h_bound
  obtain ⟨h3, h4⟩ := Proofs.ClientSideSse.withinLimit_observe _ _ hb hok
  rw [← h2] at h3 h4
  refine ⟨UScalar.eq_of_val_eq (by simpa [Defs.Sse.ofLimiter] using h4), ?_⟩
  simpa [Defs.Sse.withinLimit, Defs.Sse.ofLimiter] using h3

/-- **C02, prefix form** (plan Section 16.4, C02 and C01): if the bound holds for `self` and
`observe` on `ab = a ++ b` returns `Ok(())`, then `observe` on the prefix `a` also returns
`Ok(())`, with a state `self'` that keeps `max_size` and satisfies the bound. So every prefix of
an accepted chunk is accepted and leaves the bound holding; the chunk can be cut anywhere.
Follows from `observe_append` and `max_size_eq_and_satAdd_le_of_observe_eq_ok`
(`client_side_sse.rs` lines 48–96). About the translated function
`SseEventSizeLimiter::observe`. It takes a successful call on `ab` as its hypothesis and
covers only that case. Not tagged `@[step]`. -/
theorem exists_observe_eq_ok_and_max_size_eq_and_satAdd_le_of_observe_append_eq_ok
    (self self'' : SseEventSizeLimiter) (a b ab : Slice U8)
    (h_ab : ab.val = a.val ++ b.val)
    (h_bound :
      Defs.Sse.satAdd Usize.max self.retained_size.val self.line_size.val ≤ self.max_size.val)
    (h_ok : observe self ab = ok (.Ok (), self'')) :
    ∃ self', observe self a = ok (.Ok (), self') ∧ self'.max_size = self.max_size ∧
      Defs.Sse.satAdd Usize.max self'.retained_size.val self'.line_size.val ≤
        self'.max_size.val := by
  rw [observe_append self a b ab h_ab] at h_ok
  obtain ⟨sa, ha, -⟩ := Proofs.ClientSideSse.observe_eq self a
  rw [ha] at h_ok ⊢
  revert h_ok
  cases hk : (Defs.Sse.observe Usize.max (Defs.Sse.ofLimiter self) a.val).ok
  · simp [Defs.Sse.toResult]
  · intro _
    refine ⟨sa, by simp [Defs.Sse.toResult], ?_⟩
    exact max_size_eq_and_satAdd_le_of_observe_eq_ok self sa a h_bound
      (by rw [ha]; simp [Defs.Sse.toResult, hk])

end rmcp.transport.common.client_side_sse.SseEventSizeLimiter
