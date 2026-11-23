/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Rmcp.Funs
import Defs.Wire
import Defs.CodecState
import Proofs.External.Iter
import Proofs.External.Prim
import Proofs.External.Std

/-!
# Spec theorem for `RequestStateCodec::rs1_fallbacks_verify` (E09a)

Tries every rs1 fallback key id in order: looks the id up in the key table (`expect`, which
panics on an unknown id), verifies the tag over the transcript under that key, and ORs the
results, with no early exit. The result is `true` iff some fallback key verifies the tag.

Source: "crates/rmcp/src/model/request_state.rs", line 644 at local commit `46cfb02`
(the translation base; not yet a pinned fork commit).

Proof: `loop.spec_decr_nat` with the invariant that the accumulator is `Rs1Verifies` on the
fallbacks already visited (`List.take i`); the lookup is rewritten by `HashMap.get_eq` and
`HashMap.find_string`, since `step` does not apply to the generic `HashMap.get` call.
-/

open Aeneas Aeneas.Std Result
open rmcp
open rmcp.model.request_state
open Defs.CodecState (KeyTable FallbacksKnown Rs1Verifies)

namespace rmcp.model.request_state.RequestStateCodec

/-- **Spec theorem for `rmcp::model::request_state::RequestStateCodec::rs1_fallbacks_verify`**
(E09a)

`true` iff some rs1 fallback id names a key of `keys` that verifies `tag` over `transcript`
(`Rs1Verifies`: `∃ kid ∈ rs1_fallbacks, ∃ key ∈ lookupKey keys kid, tag = hmacSha256 key
transcript`), plan Section 2.2, E09a. It does not say which fallback matched; `false` when there
is no fallback.

Precondition `h_known`: every fallback id is a key id of `keys`. It is sufficient for the loop
not to panic, which is what the theorem states. It is also necessary, by the following argument
from the code (not proved): the loop (lines 651–655) has no early exit and looks up every
fallback, so `keys.get(kid).expect("validated rs1 fallback key")` (line 652) panics on the first
id that is not a key, whether or not an earlier fallback matched.

The statement is functional only and says nothing about timing: the comment on line 643 (every
fallback is tried so that timing does not identify the matching key) is not covered, and
`Rs1Verifies` does not depend on the order of the fallbacks.

Stated exceptions. Under the size convention of `formal/trusted/Rmcp/FunsExternal.lean` (plan
Section 4, row "HMAC"; assumption "Unlimited memory" of row "Standard library"),
`hmac_sha256_verify` (line 653) is modelled as always succeeding, whereas the `u64` bit-length
counter of SHA-256 overflows, a panic under `overflow-checks`, for a `transcript` of at least
`2^61 − 64` bytes or a fallback key of at least `2^61` bytes. For such inputs the statement
promises a result where the Rust code panics.

Assumptions: the statement reaches the locked native-code assumption
`rmcp.model.request_state.RequestStateCodec.rs1_fallbacks_verify_loop.body._native.decide.ax_3`
(`toStr "validated rs1 fallback key"`, the `expect` message of line 652;
`formal/trusted/native-axioms.lock`), so its `#print axioms` list will include it. -/
@[step]
theorem rs1_fallbacks_verify_spec (keys : KeyTable) (rs1_fallbacks : Slice String)
    (transcript : Slice Std.U8) (tag : Slice Std.U8)
    (h_known : FallbacksKnown keys rs1_fallbacks.val) :
    rs1_fallbacks_verify keys rs1_fallbacks transcript tag ⦃ (result : Bool) =>
      -- lines 650–656: `verified |= hmac_sha256_verify(key, transcript, tag)` over all ids
      result = decide (Rs1Verifies keys rs1_fallbacks.val transcript.val tag.val) ⦄ := by
  unfold rs1_fallbacks_verify rs1_fallbacks_verify_loop
  simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter, bind_tc_ok]
  apply loop.spec_decr_nat
    (measure := fun (p : core.slice.iter.Iter String × Bool) => rs1_fallbacks.length - p.1.i)
    (inv := fun p => p.1.slice = rs1_fallbacks ∧ p.1.i ≤ rs1_fallbacks.length ∧
      p.2 = decide (Rs1Verifies keys (rs1_fallbacks.val.take p.1.i) transcript.val tag.val))
  · rintro ⟨it, v⟩ ⟨hs, hi, hv⟩
    simp only at hs hi hv
    subst hs
    unfold rs1_fallbacks_verify_loop.body
    step as ⟨o, iter1, hr⟩
    rcases hr with ⟨hlt, ho, hit⟩ | ⟨hge, hr⟩
    · rcases o with _ | kid
      · simp at ho
      simp only [Option.some.injEq] at ho
      dsimp only
      have hlt' : it.i < it.slice.val.length := hlt
      have hkid : kid = it.slice.val[it.i] := by rw [ho, getElem!_pos it.slice.val it.i hlt']
      have hmem : kid ∈ Defs.CodecState.keyIds keys := by
        rw [hkid]; exact h_known _ (List.getElem_mem _)
      rw [_root_.std.collections.hash.map.HashMap.get_eq, Proofs.External.HashMap.find_string,
        bind_tc_ok]
      have hsome := (Proofs.External.HashMap.find?_key_isSome_iff keys.entries kid).2 hmem
      generalize ho1 : (keys.entries.find? (fun e => decide (e.1 = kid))).map Prod.snd = o1
        at hsome
      rcases o1 with _ | key
      · simp at hsome
      simp only [core.option.Option.expect, Result.ofOption, bind_tc_ok]
      step as ⟨v1, hv1⟩
      step as ⟨m, hm⟩
      subst hv1 hm
      have hl : Defs.CodecState.lookupKey keys kid = some key.inner.val := by
        unfold Defs.CodecState.lookupKey
        rw [Option.map_eq_some_iff] at ho1
        obtain ⟨e, he, rfl⟩ := ho1
        simp [he]
      subst hit
      refine ⟨rfl, ?_, ?_, ?_⟩
      · simp only [Slice.length] at hlt' ⊢; omega
      · simp only
        rw [List.take_add_one, List.getElem?_eq_getElem hlt', hv, ← hkid]
        simp [Rs1Verifies, Defs.CodecState.TagVerifies, List.mem_append, or_and_right,
          exists_or, hl, alloc.vec.Vec.deref]
      · simp only [Slice.length] at hlt' ⊢; omega
    · simp only [Prod.mk.injEq] at hr
      obtain ⟨ho, hit⟩ := hr
      rcases o with _ | kid
      swap
      · simp at ho
      dsimp only
      simp only [WP.spec_ok]
      have : it.i = it.slice.val.length := by simp only [Slice.length] at hge hi; omega
      rw [hv, this, List.take_length]
  · simp [Rs1Verifies]

end rmcp.model.request_state.RequestStateCodec
