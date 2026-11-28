/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Rmcp.Funs
public import Defs.Wire
public import Defs.RequestState
public import Defs.CodecState
public import Proofs.External.Std
public import Proofs.External.String
public import Proofs.Model.RequestState.Common

@[expose] public section

/-!
# Spec theorems for `with_rs1_signing` and `with_rs1_fallback` (R11, R12)

The keyring builders of `RequestStateCodec`: check that the codec is a keyring and that the
`&str` id names a key (`HashMap::contains_key` through `Borrow<str> for String`,
`Proofs.External.HashMap.find_borrowStr_eq`), then append the owned id to the rs1 fallbacks
unless already present (`slice::Iter::any`, `sliceIterAny_eq`). Statements signed off by the spec
owner on 2026-11-25.

Source: "crates/rmcp/src/model/request_state.rs", lines 373–432 in the patched copy (patches 01,
02 and 03 on origin/main `7caec76`); ten lines lower upstream.
-/

open Aeneas Aeneas.Std Result
open Defs.Wire (components versionV1 versionV2 transcriptV1 transcriptV2 minKeyLength maxKidLen
  expiryLen frameBytes domainV1 domainV2 b64Len dot Expired)
open Defs.CodecState (CodecValid CodecFallbacksKnown openAt resultBytes keyIds lookupKey
  sealModeKid)
open Defs.RequestState (StrIs kidEmptyMsg kidTooLongMsg)
open rmcp.model.request_state (SealOptions RequestStateCodec Keys SealMode RequestStateError)

open Defs.CodecState (sealAt sealExpiry CodecSealKeyKnown SealFits KeyringFits IterYields
  KeyringFailure keyringCheck rs1SigningNeedsKeyringMsg rs1SigningKidMissingMsg
  rs1FallbackNeedsKeyringMsg rs1FallbackKidMissingMsg)

namespace Proofs.RequestState.Keyring

open rmcp

/-- `slice::Iter::any` with a closure that does not change its state computes `List.any`. -/
theorem sliceIterAny_eq {T F : Type} (inst : core.ops.function.FnMut F T Bool) (p : T → Bool)
    (f : F) (hp : ∀ x, inst.call_mut f x = ok (p x, f)) :
    ∀ l : List T, ∃ n, ExtModel.sliceIterAny inst l f = ok (l.any p, n)
  | [] => ⟨0, rfl⟩
  | x :: rest => by
    obtain ⟨n, hn⟩ := sliceIterAny_eq inst p f hp rest
    simp only [ExtModel.sliceIterAny, hp, bind_ok, List.any_cons]
    cases hpx : p x
    · exact ⟨n + 1, by simp only [uncurry_apply_pair, Bool.false_eq_true, ↓reduceIte, hn,
        bind_ok, Bool.false_or]⟩
    · exact ⟨1, by simp only [uncurry_apply_pair, ↓reduceIte, Bool.true_or]⟩

end Proofs.RequestState.Keyring

namespace rmcp.model.request_state.RequestStateCodec

/-! ## `with_rs1_signing`, `with_rs1_fallback` (R11, R12) -/

/-- **R11. Spec theorem for `rmcp::model::request_state::RequestStateCodec::with_rs1_signing`**

`kid.as_ref()` (caller code; `h_as_ref` names the `&str` `k` it returns) is evaluated first
(patched line 374, upstream 384). Then, in the Rust order of checks:

* a single-key codec → `InvalidKeyring("rs1 transitional signing requires a keyring")` (patched
  lines 376–378, upstream 386–388);
* a keyring with no key id whose UTF-8 bytes are `k` (`keys.contains_key(kid)`, line 384) →
  `InvalidKeyring("rs1 signing key id is not present in the keyring")` (lines 385–387);
* otherwise `Ok codec`: `k` is the UTF-8 encoding of a key id `kidStr`; `codec` has the same key
  table, seal mode `Rs1 { key_id: kidStr }` (`kid.to_owned()` line 390, seal-mode update lines
  391–393), and the rs1 fallbacks with `kidStr`
  appended unless it is already one of them (lines 394–396; order kept, no duplicate added). It
  preserves `CodecValid`.

Premise `h_fits` (R): Lean-model domain (`KeyringFits`). Inherited exception (P): a `Drop` impl
of the caller's `kid` that panics (it is dropped on return; not translated). Rust tests:
`constructor_invariants_are_enforced` (patched lines 1284–1344) and
`rolling_migration_is_bidirectionally_compatible` (lines 1180–1210). -/
@[step]
theorem with_rs1_signing_spec {T0 : Type} (coreconvertAsRefT0StrInst : core.convert.AsRef T0 Str)
    (self : RequestStateCodec) (kid : T0) (k : Str)
    (h_as_ref : coreconvertAsRefT0StrInst.as_ref kid = ok k)
    (h_fits : KeyringFits self) :
    with_rs1_signing coreconvertAsRefT0StrInst self kid ⦃ (result :
        core.result.Result RequestStateCodec RequestStateError) =>
      match result with
      | .Ok codec =>
        ∃ keys seal_mode rs1_fallbacks kidStr,
          self.keys = .Ring keys seal_mode rs1_fallbacks ∧
          ExtModel.utf8 kidStr = (k : Slice Std.U8).val ∧ kidStr ∈ keyIds keys ∧
          (∃ fallbacks : alloc.vec.Vec String,
            codec.keys = .Ring keys (.Rs1 kidStr) fallbacks ∧
            fallbacks.val = if kidStr ∈ rs1_fallbacks.val then rs1_fallbacks.val
              else rs1_fallbacks.val ++ [kidStr]) ∧
          (CodecValid self → CodecValid codec)
      | .Err e =>
        ((∃ key, self.keys = .Single key) ∧
          ∃ msg, e = .InvalidKeyring msg ∧ StrIs msg rs1SigningNeedsKeyringMsg) ∨
        ((∃ keys seal_mode rs1_fallbacks, self.keys = .Ring keys seal_mode rs1_fallbacks ∧
            ∀ kidStr ∈ keyIds keys, ExtModel.utf8 kidStr ≠ (k : Slice Std.U8).val) ∧
          ∃ msg, e = .InvalidKeyring msg ∧ StrIs msg rs1SigningKidMissingMsg) ⦄ := by
  unfold with_rs1_signing
  simp only [h_as_ref, bind_ok]
  rcases self with ⟨key | ⟨keys, seal_mode, rs1_fallbacks⟩⟩
  · simp only [WP.spec_ok]
    left
    exact ⟨⟨key, rfl⟩, _, rfl, Proofs.RequestState.strIs_toStr _ _⟩
  · simp only [KeyringFits] at h_fits
    obtain ⟨hk, hlen⟩ := h_fits
    have hfind := Proofs.External.HashMap.find_borrowStr_eq (V := zeroize.Zeroizing
      (alloc.vec.Vec Std.U8)) k keys.entries
      (fun e he => hk e.1 (List.mem_map.2 ⟨e, he, rfl⟩))
    simp only [std.collections.hash.map.HashMap.contains_key, hfind, bind_ok]
    cases hf : keys.entries.find? (fun e => decide (ExtModel.utf8 e.1 = k.val)) with
    | none =>
      simp only [Option.map_none, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        WP.spec_ok]
      right
      refine ⟨⟨keys, seal_mode, rs1_fallbacks, rfl, ?_⟩, _, rfl,
        Proofs.RequestState.strIs_toStr _ _⟩
      intro kidStr hmem heq
      rw [List.find?_eq_none] at hf
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hmem
      exact hf e he (decide_eq_true heq)
    | some e =>
      have he := List.mem_of_find?_eq_some hf
      have hpe := List.find?_some hf
      rw [decide_eq_true_eq] at hpe
      have hto : Str.Insts.AllocBorrowToOwnedString.to_owned k = ok e.1 := by
        simp only [Str.Insts.AllocBorrowToOwnedString.to_owned, ← hpe,
          Proofs.External.Utf8.strOfBytes?_utf8]
      have hany := Proofs.RequestState.Keyring.sliceIterAny_eq
        (with_rs1_signing.closure.Insts.CoreOpsFunctionFnMutTupleShared0StringBool
          coreconvertAsRefT0StrInst) (fun x => decide (x = e.1)) e.1 (fun x => by
          simp only [
            with_rs1_signing.closure.Insts.CoreOpsFunctionFnMutTupleShared0StringBool.call_mut,
            alloc.string.String.Insts.CoreCmpPartialEqString.eq, bind_ok])
        rs1_fallbacks.val
      obtain ⟨n, hn⟩ := hany
      simp only [Option.map_some, Option.isSome_some, ↓reduceIte, hto, bind_ok,
        alloc.string.String.Insts.CoreCloneClone.clone, core.slice.Slice.iter,
        core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any,
        alloc.vec.Vec.deref, Slice.from_val, List.drop_zero, hn, uncurry_apply_pair]
      have hmemk : e.1 ∈ keyIds keys := List.mem_map.2 ⟨e, he, rfl⟩
      by_cases hin : e.1 ∈ rs1_fallbacks.val
      · have hany' : (rs1_fallbacks.val.any fun x => decide (x = e.1)) = true := by
          simp only [List.any_eq_true, decide_eq_true_eq, exists_eq_right, hin]
        simp only [hany', ↓reduceIte, WP.spec_ok]
        refine ⟨keys, seal_mode, rs1_fallbacks, e.1, rfl, hpe, hmemk,
          ⟨rs1_fallbacks, rfl, by simp only [hin, ↓reduceIte]⟩, ?_⟩
        intro hv
        simp only [CodecValid] at hv ⊢
        exact ⟨hv.1, hv.2.1, hmemk, hv.2.2.2⟩
      · have hany' : (rs1_fallbacks.val.any fun x => decide (x = e.1)) = false := by
          simp only [List.any_eq_false, decide_eq_true_eq]
          intro x hx hxe
          exact hin (hxe ▸ hx)
        simp only [hany', Bool.false_eq_true, ↓reduceIte]
        step as ⟨fb, hfb⟩
        refine ⟨keys, seal_mode, rs1_fallbacks, e.1, rfl, hpe, hmemk,
          ⟨fb, rfl, by simp only [hin, ↓reduceIte, hfb]⟩, ?_⟩
        intro hv
        simp only [CodecValid] at hv ⊢
        refine ⟨hv.1, ?_, hmemk, hv.2.2.2⟩
        intro x hx
        rw [hfb, List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hv.2.1 x hx
        · exact hmemk

/-- **R12. Spec theorem for `rmcp::model::request_state::RequestStateCodec::with_rs1_fallback`**

`kid.as_ref()` (caller code; `h_as_ref`) is evaluated first (patched line 411, upstream 421).
Then, in the Rust order of checks:

* a single-key codec → `InvalidKeyring("rs1 fallbacks require a keyring")` (patched lines
  413–415, upstream 423–425);
* a keyring with no key id whose UTF-8 bytes are `k` (line 421) →
  `InvalidKeyring("rs1 fallback key id is not present in the keyring")` (lines 422–424);
* otherwise `Ok codec`: `k` is the UTF-8 encoding of a key id `kidStr`; `codec` has the same key
  table and seal mode, and the rs1 fallbacks with `kidStr` appended unless it is already one of
  them (lines 426–428; "Adding the same id more than once has no effect", doc line 403). It
  preserves `CodecValid`.

Premise `h_fits` (R). Inherited exception (P): a `Drop` impl of the caller's `kid` that panics.
Rust tests: `constructor_invariants_are_enforced`,
`multiple_legacy_fallbacks_are_supported` (patched lines 1213–1233). -/
@[step]
theorem with_rs1_fallback_spec {T0 : Type}
    (coreconvertAsRefT0StrInst : core.convert.AsRef T0 Str)
    (self : RequestStateCodec) (kid : T0) (k : Str)
    (h_as_ref : coreconvertAsRefT0StrInst.as_ref kid = ok k)
    (h_fits : KeyringFits self) :
    with_rs1_fallback coreconvertAsRefT0StrInst self kid ⦃ (result :
        core.result.Result RequestStateCodec RequestStateError) =>
      match result with
      | .Ok codec =>
        ∃ keys seal_mode rs1_fallbacks kidStr,
          self.keys = .Ring keys seal_mode rs1_fallbacks ∧
          ExtModel.utf8 kidStr = (k : Slice Std.U8).val ∧ kidStr ∈ keyIds keys ∧
          (∃ fallbacks : alloc.vec.Vec String,
            codec.keys = .Ring keys seal_mode fallbacks ∧
            fallbacks.val = if kidStr ∈ rs1_fallbacks.val then rs1_fallbacks.val
              else rs1_fallbacks.val ++ [kidStr]) ∧
          (CodecValid self → CodecValid codec)
      | .Err e =>
        ((∃ key, self.keys = .Single key) ∧
          ∃ msg, e = .InvalidKeyring msg ∧ StrIs msg rs1FallbackNeedsKeyringMsg) ∨
        ((∃ keys seal_mode rs1_fallbacks, self.keys = .Ring keys seal_mode rs1_fallbacks ∧
            ∀ kidStr ∈ keyIds keys, ExtModel.utf8 kidStr ≠ (k : Slice Std.U8).val) ∧
          ∃ msg, e = .InvalidKeyring msg ∧ StrIs msg rs1FallbackKidMissingMsg) ⦄ := by
  unfold with_rs1_fallback
  simp only [h_as_ref, bind_ok]
  rcases self with ⟨key | ⟨keys, seal_mode, rs1_fallbacks⟩⟩
  · simp only [WP.spec_ok]
    left
    exact ⟨⟨key, rfl⟩, _, rfl, Proofs.RequestState.strIs_toStr _ _⟩
  · simp only [KeyringFits] at h_fits
    obtain ⟨hk, hlen⟩ := h_fits
    have hfind := Proofs.External.HashMap.find_borrowStr_eq (V := zeroize.Zeroizing
      (alloc.vec.Vec Std.U8)) k keys.entries
      (fun e he => hk e.1 (List.mem_map.2 ⟨e, he, rfl⟩))
    simp only [std.collections.hash.map.HashMap.contains_key, hfind, bind_ok]
    cases hf : keys.entries.find? (fun e => decide (ExtModel.utf8 e.1 = k.val)) with
    | none =>
      simp only [Option.map_none, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        WP.spec_ok]
      right
      refine ⟨⟨keys, seal_mode, rs1_fallbacks, rfl, ?_⟩, _, rfl,
        Proofs.RequestState.strIs_toStr _ _⟩
      intro kidStr hmem heq
      rw [List.find?_eq_none] at hf
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hmem
      exact hf e he (decide_eq_true heq)
    | some e =>
      have he := List.mem_of_find?_eq_some hf
      have hpe := List.find?_some hf
      rw [decide_eq_true_eq] at hpe
      have hto : Str.Insts.AllocBorrowToOwnedString.to_owned k = ok e.1 := by
        simp only [Str.Insts.AllocBorrowToOwnedString.to_owned, ← hpe,
          Proofs.External.Utf8.strOfBytes?_utf8]
      have hany := Proofs.RequestState.Keyring.sliceIterAny_eq
        (with_rs1_fallback.closure.Insts.CoreOpsFunctionFnMutTupleShared0StringBool
          coreconvertAsRefT0StrInst) (fun x => decide (ExtModel.utf8 x = k.val)) k (fun x => by
          simp only [
            with_rs1_fallback.closure.Insts.CoreOpsFunctionFnMutTupleShared0StringBool.call_mut,
            alloc.string.String.Insts.CoreCmpPartialEqStr.eq, bind_ok])
        rs1_fallbacks.val
      obtain ⟨n, hn⟩ := hany
      simp only [Option.map_some, Option.isSome_some, ↓reduceIte, hto, bind_ok,
        core.slice.Slice.iter,
        core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any,
        alloc.vec.Vec.deref, Slice.from_val, List.drop_zero, hn, uncurry_apply_pair]
      have hmemk : e.1 ∈ keyIds keys := List.mem_map.2 ⟨e, he, rfl⟩
      have hiff : (rs1_fallbacks.val.any fun x => decide (ExtModel.utf8 x = k.val)) =
          decide (e.1 ∈ rs1_fallbacks.val) := by
        rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff]
        constructor
        · rintro ⟨x, hx, hxe⟩
          rw [decide_eq_true_eq, ← hpe] at hxe
          exact Proofs.External.Utf8.utf8_injective hxe ▸ hx
        · intro h
          exact ⟨e.1, h, decide_eq_true hpe⟩
      rw [hiff]
      by_cases hin : e.1 ∈ rs1_fallbacks.val
      · simp only [hin, decide_true, ↓reduceIte, WP.spec_ok]
        refine ⟨keys, seal_mode, rs1_fallbacks, e.1, rfl, hpe, hmemk,
          ⟨rs1_fallbacks, rfl, by simp only [hin, ↓reduceIte]⟩, fun hv => hv⟩
      · simp only [hin, decide_false, Bool.false_eq_true, ↓reduceIte]
        step as ⟨fb, hfb⟩
        refine ⟨keys, seal_mode, rs1_fallbacks, e.1, rfl, hpe, hmemk,
          ⟨fb, rfl, by simp only [hin, ↓reduceIte, hfb]⟩, ?_⟩
        intro hv
        simp only [CodecValid] at hv ⊢
        refine ⟨hv.1, ?_, hv.2.2.1, hv.2.2.2⟩
        intro x hx
        rw [hfb, List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hv.2.1 x hx
        · exact hmemk

end rmcp.model.request_state.RequestStateCodec
