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
public import Proofs.Model.RequestState.ValidateKeyLength
public import Proofs.Model.RequestState.ValidateConfigKid

@[expose] public section

/-!
# Spec theorem for `new_with_keyring` (R15)

The loop over the caller's iterator is proved by induction on the list of items it yields
(`Defs.CodecState.IterYields`), with the invariant that the key table holds the accepted entries in
order (`ringEntries`) and that `keyringScan` accepts them; `new_with_keyring_loop_eq` unfolds one
iteration. `NewWithKeyringPost` (proof-only) is the postcondition of R15. The non-vacuity example
of the R15 premises closes the file. Statement signed off by the spec owner on 2026-11-25.

Source: "crates/rmcp/src/model/request_state.rs", lines 319–364 in the patched copy (patches 01,
02 and 03 on origin/main `7caec76`).
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

namespace Proofs.RequestState.NewWithKeyring

open rmcp

open rmcp.model.request_state.RequestStateCodec in
/-- One iteration of the `new_with_keyring` loop. -/
theorem new_with_keyring_loop_eq {K V T2 T3 Clause3_IntoIter : Type}
    (iK : core.convert.Into K String) (iV : core.convert.Into V (alloc.vec.Vec Std.U8))
    (iT2 : core.convert.Into T2 String)
    (iI : core.iter.traits.collect.IntoIterator T3 (K × V) Clause3_IntoIter)
    (it : Clause3_IntoIter) (active_kid : T2) (ring : Defs.CodecState.KeyTable) :
    new_with_keyring_loop iK iV iT2 iI it active_kid ring =
      (do
        let r ← new_with_keyring_loop.body iK iV iT2 iI active_kid it ring
        match r with
        | .done y => ok y
        | .cont (it', ring') => new_with_keyring_loop iK iV iT2 iI it' active_kid ring') := by
  conv_lhs => unfold new_with_keyring_loop; rw [loop]
  congr 1
  funext r
  rcases r with ⟨it', ring'⟩ | y
  · rfl
  · rfl

open Defs.CodecState (keyringScan) in
/-- Scanning a concatenation whose first part is accepted continues with its ids as seen. -/
theorem keyringScan_append_of_eq_none (seen : List String) (l1 l2 : List (String × List U8))
    (h : keyringScan seen l1 = none) :
    keyringScan seen (l1 ++ l2) = keyringScan (seen ++ l1.map Prod.fst) l2 := by
  induction l1 generalizing seen with
  | nil => simp only [List.nil_append, List.map_nil, List.append_nil]
  | cons c l1 ih =>
    obtain ⟨kid, key⟩ := c
    simp only [keyringScan] at h
    simp only [List.cons_append, keyringScan, List.map_cons]
    split_ifs at h ⊢
    rw [ih _ h, List.append_assoc, List.singleton_append]

open Defs.CodecState (keyringScan) in
/-- An accepted scan has distinct ids, ids of 1 to 255 bytes and keys of at least 32 bytes. -/
theorem nodup_and_bounds_of_keyringScan_eq_none (seen : List String) (l : List (String × List U8))
    (h : keyringScan seen l = none) (hs : seen.Nodup) :
    (seen ++ l.map Prod.fst).Nodup ∧ ∀ c ∈ l, 1 ≤ c.1.utf8ByteSize ∧
      c.1.utf8ByteSize ≤ Defs.Wire.maxKidLen ∧ Defs.Wire.minKeyLength ≤ c.2.length := by
  induction l generalizing seen with
  | nil => simp only [List.map_nil, List.append_nil, hs, List.not_mem_nil, false_imp_iff,
      implies_true, and_self]
  | cons c l ih =>
    obtain ⟨kid, key⟩ := c
    simp only [keyringScan] at h
    split_ifs at h with h1 h2 h3 h4
    have hs' : (seen ++ [kid]).Nodup := by
      rw [List.nodup_append]
      exact ⟨hs, List.nodup_singleton kid, fun a ha b hb hab => by
        rw [List.mem_singleton] at hb; subst hb; subst hab; exact h4 ha⟩
    obtain ⟨ih1, ih2⟩ := ih _ h hs'
    refine ⟨?_, ?_⟩
    · simpa only [List.map_cons, List.append_assoc, List.singleton_append] using ih1
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · dsimp only
        omega
      · exact ih2 c hc

open Defs.CodecState (keyringScan keyringCheck KeyringFailure lookupKey keyIds CodecValid) in
/-- The postcondition of R15 for the entries `entries` and active id `active`. -/
def NewWithKeyringPost (active : String) (entries : List (String × alloc.vec.Vec Std.U8))
    (result : core.result.Result RequestStateCodec RequestStateError) : Prop :=
  match result with
  | .Ok codec =>
    keyringCheck active (entries.map fun c => (c.1, c.2.val)) = .ok () ∧
    (∃ ring rs1_fallbacks, codec.keys = .Ring ring (.Rs2 active) rs1_fallbacks ∧
      rs1_fallbacks.val = [] ∧
      (keyIds ring).Perm (entries.map Prod.fst) ∧
      (∀ c ∈ entries, lookupKey ring c.1 = some c.2.val) ∧
      ∃ c ∈ entries, c.1 = active ∧ lookupKey ring active = some c.2.val) ∧
    CodecValid codec
  | .Err e =>
    ∃ f, keyringCheck active (entries.map fun c => (c.1, c.2.val)) = .error f ∧ f.Describes e

/-- The key table built from accepted entries, in order. -/
def ringEntries (acc : List (String × alloc.vec.Vec Std.U8)) :
    List (String × zeroize.Zeroizing (alloc.vec.Vec Std.U8)) :=
  acc.map fun c => (c.1, { inner := c.2 })

/-- In a table built from entries with distinct ids, each id holds its entry's key. -/
theorem lookupKey_eq_some_of_ringEntries (ring : Defs.CodecState.KeyTable)
    (acc : List (String × alloc.vec.Vec Std.U8)) (hring : ring.entries = ringEntries acc)
    (hnd : (acc.map Prod.fst).Nodup) (c : String × alloc.vec.Vec Std.U8) (hc : c ∈ acc) :
    Defs.CodecState.lookupKey ring c.1 = some c.2.val := by
  have hnd' : (ring.entries.map Prod.fst).Nodup := by
    rw [hring, ringEntries, List.map_map]; exact hnd
  have hm : (c.1, ({ inner := c.2 } : zeroize.Zeroizing (alloc.vec.Vec Std.U8))) ∈
      ring.entries := by
    rw [hring, ringEntries]; exact List.mem_map.2 ⟨c, hc, rfl⟩
  have h := Proofs.External.HashMap.find?_key_of_mem ring.entries c.1 _ hnd' hm
  have := congrArg (Option.map fun e : zeroize.Zeroizing (alloc.vec.Vec Std.U8) =>
    e.inner.val) h
  rw [Option.map_map] at this
  exact this

open Defs.CodecState (keyringScan keyringCheck KeyringFailure lookupKey keyIds CodecValid) in
open rmcp.model.request_state.RequestStateCodec in
/-- The `new_with_keyring` loop, from a state that has accepted `acc`, on an iterator that yields
`xs`, converted to `es`. -/
theorem new_with_keyring_loop_spec {K V T2 T3 Clause3_IntoIter : Type}
    (iK : core.convert.Into K String) (iV : core.convert.Into V (alloc.vec.Vec Std.U8))
    (iT2 : core.convert.Into T2 String)
    (iI : core.iter.traits.collect.IntoIterator T3 (K × V) Clause3_IntoIter)
    (active_kid : T2) (active : String)
    (h_active : iT2.into active_kid = ok active)
    (h_fit_active : active.utf8ByteSize ≤ Usize.max) :
    ∀ (xs : List (K × V)) (es : List (String × alloc.vec.Vec Std.U8)) (it : Clause3_IntoIter)
      (acc : List (String × alloc.vec.Vec Std.U8)) (ring : Defs.CodecState.KeyTable),
      Defs.CodecState.IterYields iI.iteratorInst.next it xs →
      List.Forall₂ (fun (p : K × V) (c : String × alloc.vec.Vec Std.U8) =>
        iK.into p.1 = ok c.1 ∧ iV.into p.2 = ok c.2) xs es →
      (∀ c ∈ es, c.1.utf8ByteSize ≤ Usize.max) →
      ring.entries = ringEntries acc →
      keyringScan [] (acc.map fun c => (c.1, c.2.val)) = none →
      new_with_keyring_loop iK iV iT2 iI it active_kid ring ⦃ r =>
        NewWithKeyringPost active (acc ++ es) r ⦄
  | [], es, it, acc, ring, hy, hf, hfit, hring, hscan => by
    cases hf
    obtain ⟨it', hnext⟩ := hy
    rw [new_with_keyring_loop_eq]
    unfold new_with_keyring_loop.body
    simp only [hnext, bind_ok, uncurry_apply_pair, std.collections.hash.map.HashMap.is_empty,
      hring]
    rw [List.append_nil]
    set accm := acc.map fun c => (c.1, c.2.val) with haccm
    rcases hacc : acc with _ | ⟨c0, acc'⟩
    · simp only [ringEntries, List.map_nil, List.isEmpty_nil, ↓reduceIte, bind_ok, WP.spec_ok,
        NewWithKeyringPost]
      refine ⟨.emptyKeyring, ?_, _, rfl, Proofs.RequestState.strIs_toStr _ _⟩
      simp only [keyringCheck, keyringScan, ↓reduceIte]
    rw [← hacc]
    have hne : acc ≠ [] := by rw [hacc]; exact List.cons_ne_nil _ _
    have hne' : accm ≠ [] := by rw [haccm]; simpa only [ne_eq, List.map_eq_nil_iff] using hne
    have hemp : (ringEntries acc).isEmpty = false := by
      simp only [ringEntries, List.isEmpty_eq_false_iff, ne_eq, List.map_eq_nil_iff]; exact hne
    simp only [hemp, Bool.false_eq_true, ↓reduceIte, h_active, bind_ok]
    step with alloc.string.String.Insts.CoreOpsDerefDerefStr.deref_spec _ h_fit_active
      as ⟨sa, hsa⟩
    have hsal : (sa : Slice Std.U8).val.length = active.utf8ByteSize := by
      rw [hsa, Proofs.External.Utf8.length_utf8]
    step with validate_config_kid_spec as ⟨r, hr⟩
    rcases r with _ | e
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      rw [hsal] at hr
      have hfind := Proofs.External.HashMap.find_string (V := zeroize.Zeroizing
        (alloc.vec.Vec Std.U8)) active ring.entries
      simp only [std.collections.hash.map.HashMap.contains_key, hfind, bind_ok]
      have hiff := Proofs.External.HashMap.find?_key_isSome_iff ring.entries active
      have hkeys : ring.entries.map Prod.fst = accm.map Prod.fst := by
        rw [hring, haccm, ringEntries, List.map_map, List.map_map]; rfl
      rw [hkeys] at hiff
      by_cases hin : active ∈ accm.map Prod.fst
      · have hb := hiff.2 hin
        simp only [hb, ↓reduceIte, bind_ok, WP.spec_ok, NewWithKeyringPost]
        obtain ⟨hnd, hall⟩ := nodup_and_bounds_of_keyringScan_eq_none [] accm hscan List.nodup_nil
        rw [List.nil_append] at hnd
        have hfst : accm.map Prod.fst = acc.map Prod.fst := by
          rw [haccm, List.map_map]; rfl
        rw [hfst] at hnd hin
        have hids : keyIds ring = acc.map Prod.fst := by
          rw [keyIds, hring, ringEntries, List.map_map]; rfl
        have h0 : ¬ active.utf8ByteSize = 0 := by omega
        have h1 : ¬ Defs.Wire.maxKidLen < active.utf8ByteSize := by omega
        refine ⟨?_, ⟨ring, _, rfl, rfl, by rw [hids], fun c hc =>
          lookupKey_eq_some_of_ringEntries ring acc hring hnd c hc, ?_⟩, ?_⟩
        · rw [← haccm]
          have hin' : active ∈ accm.map Prod.fst := by rw [hfst]; exact hin
          simp only [keyringCheck, hscan, hne', h0, h1, hin', ↓reduceIte]
        · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hin
          exact ⟨c, hc, rfl, lookupKey_eq_some_of_ringEntries ring acc hring hnd c hc⟩
        · simp only [CodecValid]
          refine ⟨by rw [hids]; exact hnd, ?_, by rw [hids]; exact hin, ?_⟩
          · intro kid hk
            have h : (alloc.vec.Vec.new String).val = [] := rfl
            rw [h] at hk
            exact absurd hk List.not_mem_nil
          · intro e he
            rw [hring, ringEntries] at he
            obtain ⟨c, hc, rfl⟩ := List.mem_map.1 he
            have := hall (c.1, c.2.val) (by rw [haccm]; exact List.mem_map.2 ⟨c, hc, rfl⟩)
            dsimp only at this ⊢
            omega
      · have hb : ((ring.entries.find? fun e => decide (e.1 = active)).map Prod.snd).isSome =
            false := by
          cases h : ((ring.entries.find? fun e => decide (e.1 = active)).map Prod.snd).isSome
          · rfl
          · exact absurd (hiff.1 h) hin
        simp only [hb, Bool.false_eq_true, ↓reduceIte, bind_ok, WP.spec_ok, NewWithKeyringPost]
        refine ⟨.activeKidMissing, ?_, _, rfl, Proofs.RequestState.strIs_toStr _ _⟩
        rw [← haccm]
        have h0 : ¬ active.utf8ByteSize = 0 := by omega
        have h1 : ¬ Defs.Wire.maxKidLen < active.utf8ByteSize := by omega
        simp only [keyringCheck, hscan, hne', h0, h1, hin, ↓reduceIte]
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, WP.spec_ok, NewWithKeyringPost]
      rw [hsal] at hr
      rw [← haccm]
      rcases hr with ⟨h0, hmsg⟩ | ⟨h1, hmsg⟩
      · exact ⟨.kidEmpty, by simp only [keyringCheck, hscan, hne', h0, ↓reduceIte], hmsg⟩
      · have h0 : ¬ active.utf8ByteSize = 0 := by simp only [Defs.Wire.maxKidLen] at h1; omega
        exact ⟨.kidTooLong, by simp only [keyringCheck, hscan, hne', h0, h1, ↓reduceIte],
          hmsg⟩
  | x :: xs, es, it, acc, ring, hy, hf, hfit, hring, hscan => by
    obtain ⟨it', hnext, hy'⟩ := hy
    cases hf with
    | cons hxc hrest =>
    rename_i c es'
    obtain ⟨hk, hv⟩ := hxc
    obtain ⟨xk, xv⟩ := x
    have hfc : c.1.utf8ByteSize ≤ Usize.max := hfit c List.mem_cons_self
    have hfit' : ∀ c ∈ es', c.1.utf8ByteSize ≤ Usize.max :=
      fun c hc => hfit c (List.mem_cons_of_mem _ hc)
    have ih := new_with_keyring_loop_spec iK iV iT2 iI active_kid active h_active h_fit_active
      xs es' it'
    rw [new_with_keyring_loop_eq]
    unfold new_with_keyring_loop.body
    simp only [hnext, bind_ok, uncurry_apply_pair, hk, hv, zeroize.Zeroizing.new]
    step with alloc.string.String.Insts.CoreOpsDerefDerefStr.deref_spec _ hfc as ⟨sk, hsk⟩
    have hskl : (sk : Slice Std.U8).val.length = c.1.utf8ByteSize := by
      rw [hsk, Proofs.External.Utf8.length_utf8]
    set accm := acc.map fun c => (c.1, c.2.val) with haccm
    have hmap : (acc ++ c :: es').map (fun c => (c.1, c.2.val)) =
        accm ++ (c.1, c.2.val) :: es'.map (fun c => (c.1, c.2.val)) := by
      rw [List.map_append, List.map_cons]
    have hscan' : keyringScan [] ((acc ++ c :: es').map (fun c => (c.1, c.2.val))) =
        keyringScan (accm.map Prod.fst) ((c.1, c.2.val) :: es'.map (fun c => (c.1, c.2.val))) := by
      rw [hmap, keyringScan_append_of_eq_none [] accm _ hscan, List.nil_append]
    step with validate_config_kid_spec as ⟨r, hr⟩
    rw [hskl] at hr
    rcases r with _ | e
    · obtain ⟨h0, h1⟩ := hr
      have h0' : ¬ c.1.utf8ByteSize = 0 := by omega
      have h1' : ¬ Defs.Wire.maxKidLen < c.1.utf8ByteSize := by omega
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref]
      step with validate_key_length_spec as ⟨r1, hr1⟩
      simp only [alloc.vec.Vec.deref, Slice.from_val] at hr1
      rcases r1 with _ | e
      · simp only [bind_ok, std.collections.hash.map.HashMap.entry,
          Proofs.External.HashMap.lookupEntry_string_eq]
        have h2' : ¬ c.2.val.length < Defs.Wire.minKeyLength := by omega
        have hkeys : ring.entries.map Prod.fst = accm.map Prod.fst := by
          rw [hring, haccm, ringEntries, List.map_map, List.map_map]; rfl
        by_cases hdup : c.1 ∈ accm.map Prod.fst
        · obtain ⟨e, he⟩ : ∃ e, ring.entries.find? (fun e => decide (e.1 = c.1)) = some e :=
            by
            rw [← hkeys] at hdup
            obtain ⟨e, he, hec⟩ := List.mem_map.1 hdup
            cases h : ring.entries.find? (fun e => decide (e.1 = c.1)) with
            | none =>
              rw [List.find?_eq_none] at h
              exact absurd (decide_eq_true hec) (h e he)
            | some e => exact ⟨e, rfl⟩
          obtain ⟨ek, ev⟩ := e
          simp only [he, bind_ok, uncurry_apply_pair, WP.spec_ok, NewWithKeyringPost]
          refine ⟨.duplicateKid, ?_, _, rfl, Proofs.RequestState.strIs_toStr _ _⟩
          simp only [keyringCheck, hscan', keyringScan, h0', h1', h2', hdup, ↓reduceIte]
        · have hnone : ring.entries.find? (fun e => decide (e.1 = c.1)) = none := by
            rw [List.find?_eq_none]
            intro e he hec
            rw [decide_eq_true_eq] at hec
            exact hdup (hkeys ▸ List.mem_map.2 ⟨e, he, hec⟩)
          simp only [hnone, std.collections.hash.map.VacantEntry.insert, bind_ok,
            uncurry_apply_pair]
          have hpost := ih (acc ++ [c])
            { ring with entries := ring.entries ++ [(c.1, { inner := c.2 })] } hy' hrest hfit'
            (by simp only [hring, ringEntries, List.map_append, List.map_cons, List.map_nil])
            (by
              rw [List.map_append, keyringScan_append_of_eq_none [] accm _ hscan, List.nil_append]
              simp only [List.map_cons, List.map_nil, keyringScan, h0', h1', h2', hdup,
                ↓reduceIte])
          rw [List.append_assoc, List.singleton_append] at hpost
          exact hpost
      · simp only [bind_ok, bind_tc_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, WP.spec_ok, NewWithKeyringPost]
        obtain ⟨h2, hmsg⟩ := hr1
        refine ⟨.keyTooShort c.2.val.length, ?_, hmsg⟩
        simp only [keyringCheck, hscan', keyringScan, h0', h1', h2, ↓reduceIte]
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, WP.spec_ok, NewWithKeyringPost]
      rcases hr with ⟨h0, hmsg⟩ | ⟨h1, hmsg⟩
      · exact ⟨.kidEmpty, by simp only [keyringCheck, hscan', keyringScan, h0, ↓reduceIte],
          hmsg⟩
      · have h0 : ¬ c.1.utf8ByteSize = 0 := by simp only [Defs.Wire.maxKidLen] at h1; omega
        exact ⟨.kidTooLong, by simp only [keyringCheck, hscan', keyringScan, h0, h1,
          ↓reduceIte], hmsg⟩

end Proofs.RequestState.NewWithKeyring

namespace rmcp.model.request_state.RequestStateCodec

/-! ## `new_with_keyring` (R15) -/

/-- **R15. Spec theorem for `rmcp::model::request_state::RequestStateCodec::new_with_keyring`**

Caller code, named by premises (it may panic; the statement says nothing about that case): the
`IntoIterator` of `keys` returns the iterator `it` (`h_into_iter`), which yields `items` and then
`None` (`h_yields`); each item `(kid, key)` converts by `kid.into()` and `key.into()` (patched
lines 329–330, both before any check) to the entry of `entries` at the same position
(`h_entries`); `active_kid.into()` returns `active` (line 349; called only after the loop).
Lean-model domain (U): the converted ids have at most `usize::MAX` UTF-8 bytes (`h_fit`,
`h_fit_active`; the Lean model of `String::deref` fails above it). Not covered (lead decision
2026-11-25: the premises stay unconditional): an infinite iterator (no finite `items`); and
caller code that Rust never runs but the premises require to return: every call of `next` and
`into()` after the first rejected entry, and `active_kid.into()` when Rust returns before line
349. If such code would panic or diverge, the premises fail and the statement says nothing.

Result, in the Rust order of checks (`keyringCheck`, `Defs.CodecState`):

* `Err e` exactly when `keyringCheck active entries` is a failure `f`, and `e` is the error of
  `f` (`KeyringFailure.Describes`): per entry in order, an empty id, an id over 255 bytes
  (E04, line 331), a key under 32 bytes (`KeyTooShort`, E03, line 332), a repeated id
  (`"duplicate key id"`, line 338); then no entry (`"keyring must contain at least one key"`,
  lines 343–347); then the active id empty or over 255 bytes (line 350); then the active id not
  a key id (`"active key id is not present in the keyring"`, lines 351–355).
* `Ok codec` exactly when `keyringCheck` succeeds; `codec` is a keyring (lines 357–363) whose key
  ids are, up to order, the configured ids (`List.Perm`), each holding its configured key
  (`lookupKey`), with seal mode `Rs2 { key_id: active }` (the active id is one of the
  configured ids and holds its configured key) and no rs1 fallback, and it satisfies
  `CodecValid` (all four clauses).

Not tagged `@[step]`: its premises about caller code cannot be discharged by `step` in a
caller.

Hash keys rule (`ExtModel.randomState`): nothing is said about the map's `hash_builder` or the
order of its entries, and no two results are compared; the content is stated through `keyIds`
and `lookupKey`. Inherited exceptions: (N) `HashMap::new` panics if the operating system's random
source fails (model of `HashMap::new`); (P) a caller `Drop` impl that panics (of `active_kid`,
the iterator, the items not yet consumed; dropped on every return path, including the early
error returns). Rust tests: `constructor_invariants_are_enforced` (patched
lines 1284–1344), `rotation_keeps_previous_rs2_key_verifiable` (lines 1162–1177). -/
theorem new_with_keyring_spec {K V T2 T3 Clause3_IntoIter : Type}
    (coreconvertIntoKStringInst : core.convert.Into K String)
    (coreconvertIntoVVecU8Inst : core.convert.Into V (alloc.vec.Vec Std.U8))
    (coreconvertIntoT2StringInst : core.convert.Into T2 String)
    (coreitertraitscollectIntoIteratorT3PairClause3_IntoIterInst :
      core.iter.traits.collect.IntoIterator T3 (K × V) Clause3_IntoIter)
    (active_kid : T2) (keys : T3)
    (it : Clause3_IntoIter) (items : List (K × V))
    (entries : List (String × alloc.vec.Vec Std.U8)) (active : String)
    (h_into_iter :
      coreitertraitscollectIntoIteratorT3PairClause3_IntoIterInst.into_iter keys = ok it)
    (h_yields :
      IterYields coreitertraitscollectIntoIteratorT3PairClause3_IntoIterInst.iteratorInst.next it
        items)
    (h_entries : List.Forall₂ (fun (p : K × V) (c : String × alloc.vec.Vec Std.U8) =>
      coreconvertIntoKStringInst.into p.1 = ok c.1 ∧
      coreconvertIntoVVecU8Inst.into p.2 = ok c.2) items entries)
    (h_active : coreconvertIntoT2StringInst.into active_kid = ok active)
    (h_fit : ∀ c ∈ entries, c.1.utf8ByteSize ≤ Usize.max)
    (h_fit_active : active.utf8ByteSize ≤ Usize.max) :
    new_with_keyring coreconvertIntoKStringInst coreconvertIntoVVecU8Inst
      coreconvertIntoT2StringInst coreitertraitscollectIntoIteratorT3PairClause3_IntoIterInst
      active_kid keys ⦃ (result : core.result.Result RequestStateCodec RequestStateError) =>
      match result with
      | .Ok codec =>
        keyringCheck active (entries.map fun c => (c.1, c.2.val)) = .ok () ∧
        (∃ ring rs1_fallbacks, codec.keys = .Ring ring (.Rs2 active) rs1_fallbacks ∧
          rs1_fallbacks.val = [] ∧
          (keyIds ring).Perm (entries.map Prod.fst) ∧
          (∀ c ∈ entries, lookupKey ring c.1 = some c.2.val) ∧
          ∃ c ∈ entries, c.1 = active ∧ lookupKey ring active = some c.2.val) ∧
        CodecValid codec
      | .Err e =>
        ∃ f, keyringCheck active (entries.map fun c => (c.1, c.2.val)) = .error f ∧
          f.Describes e ⦄ := by
  unfold new_with_keyring
  simp only [std.collections.hash.map.HashMapKVRandomStateGlobal.new, h_into_iter, bind_ok]
  have h := Proofs.RequestState.NewWithKeyring.new_with_keyring_loop_spec coreconvertIntoKStringInst
    coreconvertIntoVVecU8Inst coreconvertIntoT2StringInst
    coreitertraitscollectIntoIteratorT3PairClause3_IntoIterInst active_kid active h_active
    h_fit_active items entries it []
    { hash_builder := ExtModel.randomState, alloc := alloc.alloc.Global.mk, entries := [] }
    h_yields h_entries h_fit rfl rfl
  rw [List.nil_append] at h
  exact h

end rmcp.model.request_state.RequestStateCodec

/-! ## Non-vacuity of the R15 premises

A list-based iterator, identity conversions, one entry `("a", 32 zero bytes)` and active id
`"a"`. -/

namespace Examples.NewWithKeyring

/-- The identity `Into<String>` conversion. -/
def intoString : core.convert.Into String String := ⟨fun s => ok s⟩

/-- The identity `Into<Vec<u8>>` conversion. -/
def intoVec : core.convert.Into (alloc.vec.Vec Std.U8) (alloc.vec.Vec Std.U8) := ⟨fun v => ok v⟩

/-- A list as an `IntoIterator`: the iterator is the list of remaining items. -/
def listIntoIter {T : Type} : core.iter.traits.collect.IntoIterator (List T) T (List T) :=
  { iteratorInst := { next := fun l => match l with
        | [] => ok (none, [])
        | x :: xs => ok (some x, xs) }
    into_iter := fun l => ok l }

/-- A 32-byte key of zeros. -/
def key32 : alloc.vec.Vec Std.U8 :=
  alloc.vec.Vec.from (List.replicate 32 0#u8) (by simp only [List.length_replicate]; scalar_tac)

/-- Non-vacuity of R15 (round 2, reviewer proposal checked): the premises of
`new_with_keyring_spec` hold together for one entry `("a", key32)` and active id `"a"`, and its
conclusion forces the `Ok` branch. The proof of this `example` has no placeholder; it depends on
`new_with_keyring_spec`, which is a placeholder in this draft. -/
example : rmcp.model.request_state.RequestStateCodec.new_with_keyring intoString intoVec
    intoString listIntoIter "a" [("a", key32)] ⦃ (r :
      core.result.Result RequestStateCodec RequestStateError) => ∃ codec, r = .Ok codec ⦄ := by
  have ha : "a".utf8ByteSize = 1 := by decide
  apply WP.spec_mono (rmcp.model.request_state.RequestStateCodec.new_with_keyring_spec
    intoString intoVec intoString listIntoIter "a" [("a", key32)] [("a", key32)] [("a", key32)]
    [("a", key32)] "a" rfl ⟨[], rfl, [], rfl⟩
    (List.Forall₂.cons ⟨rfl, rfl⟩ List.Forall₂.nil) rfl
    (by intro c hc; simp only [List.mem_singleton] at hc; subst hc; simp only [ha]; scalar_tac)
    (by simp only [ha]; scalar_tac))
  intro r hr
  cases r with
  | Ok c => exact ⟨c, rfl⟩
  | Err e =>
    obtain ⟨f, hf, -⟩ := hr
    have hk : key32.val.length = 32 := rfl
    simp [keyringCheck, Defs.CodecState.keyringScan, ha, hk, Defs.Wire.maxKidLen,
      Defs.Wire.minKeyLength] at hf

end Examples.NewWithKeyring
