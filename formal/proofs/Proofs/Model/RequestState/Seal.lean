/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Rmcp.Funs
public import Defs.Wire
public import Defs.CodecState
public import Proofs.External.Std
public import Proofs.External.String
public import Proofs.Model.RequestStateWire.Common
public import Proofs.Model.RequestStateWire.Frame
public import Proofs.Model.RequestState.SealRs1
public import Proofs.Model.RequestState.SealRs2
-- module system: `val_saturating_add_eq_sealExpiry` unfolds these library definitions, not
-- exposed by Aeneas
import all Aeneas.Std.Scalar.SaturatingOps

@[expose] public section

/-!
# Spec theorems for sealing: `seal_at` (R10a), `seal_with` (R10), `seal` (R09)

The private `seal_at` frames the payload with the expiry `sealExpiry` (W15 `frame_spec`) and seals
it with E07 `seal_rs1_spec` or E08 `seal_rs2_spec` under the single key or the seal-mode key of a
keyring; its expected result is `Defs.CodecState.sealAt`. `seal_with` is `seal_at` at the clock
reading `ExtModel.nowMs`, `seal` is `seal_with` with the default options. The corollaries derive
the premises (S) and (D) from `CodecValid` and a length bound. Statements signed off by the spec
owner on 2026-11-25.

Source: "crates/rmcp/src/model/request_state.rs", lines 436–443 and 533–561 in the patched copy
(patches 01, 02 and 03 on origin/main `7caec76`).
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

namespace Proofs.RequestState.Seal

/-- The expiry that `seal_at` computes for a time-to-live `d` at `now` (patched lines 534–538) is
`sealExpiry (some d) now`. -/
theorem val_saturating_add_eq_sealExpiry (d : core.time.Duration) (now_ms : I64) :
    (core.num.I64.saturating_add now_ms
      (UScalar.hcast IScalarTy.I64
        (core.cmp.impls.OrdU128.min
          (⟨BitVec.ofNat 128 (d.secs.val * 1000 + d.nanos.val / 1000000)⟩ : U128)
          (IScalar.hcast UScalarTy.U128 core.num.I64.MAX)))).val =
      Defs.CodecState.sealExpiry (some d) now_ms.val := by
  have hs := d.secs.hBounds
  have hn := d.nanos.hBounds
  simp only [Defs.CodecState.sealExpiry, Defs.CodecState.durationMillis]
  generalize hm : d.secs.val * 1000 + d.nanos.val / 1000000 = m
  have hms : m < 2 ^ 128 := by subst hm; scalar_tac
  have h0 : (⟨BitVec.ofNat 128 m⟩ : U128).val = m := by
    show (BitVec.ofNat 128 m).toNat = m
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hms
  have h1 : (IScalar.hcast UScalarTy.U128 core.num.I64.MAX).val = 2 ^ 63 - 1 := by
    rw [IScalar.hcast_val_eq]; simp [core.num.I64.MAX, I64.rMax]
  have h2 : (core.cmp.impls.OrdU128.min (⟨BitVec.ofNat 128 m⟩ : U128)
      (IScalar.hcast UScalarTy.U128 core.num.I64.MAX)).val = min m (2 ^ 63 - 1) := by
    rw [core.cmp.impls.OrdU128.min_val, h1, h0]
  generalize core.cmp.impls.OrdU128.min (⟨BitVec.ofNat 128 m⟩ : U128)
      (IScalar.hcast UScalarTy.U128 core.num.I64.MAX) = x at h2
  have h3 : (UScalar.hcast IScalarTy.I64 x).val = (min m (2 ^ 63 - 1) : Nat) := by
    rw [UScalar.hcast_val_eq, h2]
    have : IScalarTy.I64.numBits = 64 := rfl
    rw [this]
    apply Int.bmod_eq_of_le <;> omega
  generalize UScalar.hcast IScalarTy.I64 x = y at h3
  have hImax : I64.max = 2 ^ 63 - 1 := by rw [I64.max_eq]; rfl
  have hImin : I64.min = - 2 ^ 63 := by rw [I64.min_eq]; rfl
  have hy : min ((m : Nat) : Int) I64.max = y.val := by
    rw [h3, hImax]; omega
  rw [hy]
  have hnow := now_ms.hBounds
  have key : ∀ v : Int, I64.min ≤ v → v ≤ I64.max →
      (⟨BitVec.ofInt IScalarTy.I64.numBits v⟩ : IScalar .I64).val = v := by
    intro v h1 h2
    rw [hImin] at h1
    rw [hImax] at h2
    have hnb : IScalarTy.I64.numBits = 64 := rfl
    show (BitVec.ofInt IScalarTy.I64.numBits v).toInt = v
    rw [BitVec.toInt_ofInt, hnb]
    apply Int.bmod_eq_of_le <;> omega
  simp only [core.num.I64.saturating_add, IScalar.saturating_add,
    IScalar.max_IScalarTy_I64_eq, IScalar.min_IScalarTy_I64_eq]
  rw [key]
  · rw [hImin, hImax]; omega
  · rw [hImin, hImax]; omega

/-- Under `CodecValid`, a length bound on the associated data and the payload gives the seal
premises (S) and (D). -/
theorem codecSealKeyKnown_and_sealFits_of_codecValid (codec : RequestStateCodec) (p a : Nat)
    (h_valid : Defs.CodecState.CodecValid codec)
    (h_len : a + 2 * p + 512 ≤ ExtModel.maxStringBytes) :
    Defs.CodecState.CodecSealKeyKnown codec ∧ Defs.CodecState.SealFits codec p a := by
  have hM := Proofs.External.Utf8.maxStringBytes_le_usize_max
  have hv1 : Defs.Wire.versionV1.length = 3 := rfl
  have hv2 : Defs.Wire.versionV2.length = 3 := rfl
  have hd1 : Defs.Wire.domainV1.length = 26 := rfl
  have hd2 : Defs.Wire.domainV2.length = 26 := rfl
  have hel : Defs.Wire.expiryLen = 8 := rfl
  rcases codec with ⟨key | ⟨keys, sm, fb⟩⟩
  · simp only [Defs.CodecState.CodecSealKeyKnown, Defs.CodecState.SealFits, true_and, hv1, hd1,
      hel, Defs.Wire.b64Len]
    omega
  · simp only [Defs.CodecState.CodecValid] at h_valid
    obtain ⟨-, -, hsm, hent⟩ := h_valid
    refine ⟨hsm, ?_⟩
    cases sm with
    | Rs1 kid =>
      simp only [Defs.CodecState.SealFits, hv1, hd1, hel, Defs.Wire.b64Len]
      omega
    | Rs2 kid =>
      simp only [Defs.CodecState.sealModeKid] at hsm
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hsm
      have hk := (hent e he).2.2
      simp only [Defs.CodecState.SealFits, hv2, hd2, hel, Defs.Wire.b64Len]
      simp only [Defs.Wire.maxKidLen] at hk
      omega

end Proofs.RequestState.Seal

namespace rmcp.model.request_state.RequestStateCodec

/-! ## Sealing (R09, R10; private `seal_at`) -/

/-- **R10a (internal). Spec theorem for
`rmcp::model::request_state::RequestStateCodec::seal_at`** (private; restated in
`formal/proofs/Proofs/Internal/Model/RequestState.lean`)

At an explicit time `now_ms`, the UTF-8 bytes of the token are `sealAt self payload ad ttl
now_ms` (patched lines 533–561; upstream 540–569, before patch 01's refactor onto `wire::frame`
and patch 03 hunk 1, `let ttl = options.ttl;`). Premises: (S) `h_key`, the seal-mode key id is a
key id (else the `expect` at line 549 or 555 panics); (D) `h_fits`, the Lean-model domain.
Inherited exceptions: (H) HMAC `2^61`; (V) a transcript above `isize::MAX` bytes. Rust tests
(they call `seal_at` directly): `within_ttl_opens`, `past_ttl_is_expired`,
`no_ttl_never_expires`, `ttl_and_associated_data_combine` (patched lines 985–1038),
`rs1_known_answer_is_unchanged` (lines 1105–1119),
`rs2_roundtrips_with_associated_data_and_ttl` (lines 1139–1159). -/
@[step]
theorem seal_at_spec (self : RequestStateCodec) (payload : Slice Std.U8)
    (options : SealOptions) (now_ms : Std.I64)
    (h_key : CodecSealKeyKnown self)
    (h_fits : SealFits self payload.val.length options.associated_data.val.length) :
    seal_at self payload options now_ms ⦃ (result : String) =>
      sealAt self payload.val options.associated_data.val options.ttl now_ms.val =
        some (ExtModel.utf8 result) ⦄ := by
  unfold seal_at
  rcases hT : options.ttl with _ | d
  case' none =>
    simp only
    rw [show (none : Option core.time.Duration) = options.ttl from hT.symm]
    have hE : (0#i64 : I64).val = sealExpiry options.ttl now_ms.val := by rw [hT]; rfl
    generalize (0#i64 : I64) = E at hE ⊢
  case' some =>
    simp only [core.time.Duration.as_millis, lift, bind_ok]
    rw [show (some d : Option core.time.Duration) = options.ttl from hT.symm]
    have hE := Proofs.RequestState.Seal.val_saturating_add_eq_sealExpiry d now_ms
    rw [← hT] at hE
    generalize core.num.I64.saturating_add _ _ = E at hE ⊢
  all_goals
    clear hT
    have hM := Proofs.External.Utf8.maxStringBytes_le_usize_max
    have hU := Usize.cMax_bound_concrete.1
    have hv1 : versionV1.length = 3 := rfl
    have hv2 : versionV2.length = 3 := rfl
    have hd1 : domainV1.length = 26 := rfl
    have hd2 : domainV2.length = 26 := rfl
    have hel : expiryLen = 8 := rfl
    rcases self with ⟨key | ⟨keys, sm, fb⟩⟩ <;> [skip; cases sm]
    all_goals simp only [SealFits, hel] at h_fits
    all_goals
      step with request_state_wire.frame_spec as ⟨body, hbody⟩
      · rw [Proofs.RequestStateWire.length_frameBytes]; omega
      rw [hE] at hbody
    all_goals
      have hbd : (body.deref : Slice Std.U8).val = frameBytes (sealExpiry options.ttl now_ms.val)
          payload.val := by rw [alloc.vec.Vec.deref, Slice.from_val, hbody]
      have hbl := Proofs.RequestStateWire.length_frameBytes (sealExpiry options.ttl now_ms.val)
        payload.val
    · -- single key
      simp only [zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref, bind_ok]
      have h_len : (transcriptV1 options.associated_data.val body.deref.val).length ≤
          Usize.max := by
        rw [Proofs.RequestStateWire.length_transcriptV1, hbd, hbl]; omega
      have h_cap : versionV1.length + 2 + b64Len body.deref.val.length + b64Len 32 ≤
          ExtModel.maxStringBytes := by
        rw [hbd, hbl]; omega
      step with seal_rs1_spec _ _ _ h_len h_cap as ⟨r, hr⟩
      rw [hbd] at hr
      simp only [sealAt, Defs.CodecState.tokenV1, hr, alloc.vec.Vec.deref, Slice.from_val]
    · -- keyring, rs1
      rename_i kid
      have hkid : kid ∈ keyIds keys := h_key
      step with std.collections.hash.map.HashMap.get_string_spec as ⟨o, ho⟩
      have hsome : o.isSome := by
        rw [ho, Proofs.External.HashMap.find?_key_isSome_iff]; exact hkid
      step with core.option.Option.expect.spec _ _ hsome as ⟨z, hz⟩
      have hlk : lookupKey keys kid = some z.inner.val := by
        have := congrArg (Option.map fun e : zeroize.Zeroizing (alloc.vec.Vec Std.U8) =>
          e.inner.val) (ho.symm.trans hz)
        rw [Option.map_map] at this
        exact this
      simp only [zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref, bind_ok]
      have h_len : (transcriptV1 options.associated_data.val body.deref.val).length ≤
          Usize.max := by
        rw [Proofs.RequestStateWire.length_transcriptV1, hbd, hbl]; omega
      have h_cap : versionV1.length + 2 + b64Len body.deref.val.length + b64Len 32 ≤
          ExtModel.maxStringBytes := by
        rw [hbd, hbl]; omega
      step with seal_rs1_spec _ _ _ h_len h_cap as ⟨r, hr⟩
      rw [hbd] at hr
      simp only [sealAt, hlk, Option.map_some, Defs.CodecState.tokenV1, hr, alloc.vec.Vec.deref,
        Slice.from_val]
    · -- keyring, rs2
      rename_i kid
      have hkid : kid ∈ keyIds keys := h_key
      have hks : kid.utf8ByteSize ≤ Usize.max := by omega
      step with alloc.string.String.Insts.CoreOpsDerefDerefStr.deref_spec _ hks as ⟨sk, hsk⟩
      have hskl : (sk : Slice Std.U8).val.length = kid.utf8ByteSize := by
        rw [hsk, Proofs.External.Utf8.length_utf8]
      step with std.collections.hash.map.HashMap.get_string_spec as ⟨o, ho⟩
      have hsome : o.isSome := by
        rw [ho, Proofs.External.HashMap.find?_key_isSome_iff]; exact hkid
      step with core.option.Option.expect.spec _ _ hsome as ⟨z, hz⟩
      have hlk : lookupKey keys kid = some z.inner.val := by
        have := congrArg (Option.map fun e : zeroize.Zeroizing (alloc.vec.Vec Std.U8) =>
          e.inner.val) (ho.symm.trans hz)
        rw [Option.map_map] at this
        exact this
      simp only [zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref, bind_ok]
      have h_len : (transcriptV2 (sk : Slice Std.U8).val options.associated_data.val
          body.deref.val).length ≤ Usize.max := by
        rw [Proofs.RequestStateWire.length_transcriptV2, hbd, hbl, hskl]; omega
      have h_cap : versionV2.length + 3 + b64Len (sk : Slice Std.U8).val.length +
          b64Len body.deref.val.length + b64Len 32 ≤ ExtModel.maxStringBytes := by
        rw [hbd, hbl, hskl]; omega
      step with seal_rs2_spec _ _ _ _ h_len h_cap as ⟨r, hr⟩
      rw [hbd, hsk] at hr
      simp only [sealAt, hlk, Option.map_some, Defs.CodecState.tokenV2, hr, alloc.vec.Vec.deref,
        Slice.from_val]

/-- **R10. Spec theorem for `rmcp::model::request_state::RequestStateCodec::seal_with`**

Seals `payload` with `options` at the clock reading: the UTF-8 bytes of the token are
`sealAt self payload ad ttl t` for `t = ExtModel.nowMs`, the time the call reads
(`self.seal_at(payload, options, Self::now_ms())`, patched lines 441–443, upstream 451–453;
`now_ms` patched lines 733–735). `sealAt` (`Defs.CodecState`) is the expected result of the
private `seal_at`. Clock: `nowMs` is opaque, so the statement is the `seal_at` statement at an
arbitrary `I64` reading; it says nothing about two calls (in Rust two calls read different
times) and does not constrain the value of `nowMs`. The reading matters only with a ttl
(`sealExpiry none t = 0`).

Premises: (S) `h_key` (`CodecSealKeyKnown`; every codec built through the public API has it:
`CodecValid`, R04–R06, R11, R12, R15); (D) `h_fits` (`SealFits`).

Inherited exceptions, where Rust panics and this statement promises a result: (K) the clock is
before 1970 or outside chrono's range (evaluated first, line 442); (H) a transcript of at least
`2^61 − 64` bytes or a key of at least `2^61` bytes; (V) a transcript above `isize::MAX` bytes
(possible only through long associated data: (D) bounds the payload by the capacity sum).
Rust tests (they call `seal_with`): `associated_data::{matching_context_opens,
different_context_is_rejected, missing_context_is_rejected}` (patched lines 945–951, 954–963,
966–976). -/
@[step]
theorem seal_with_spec (self : RequestStateCodec) (payload : Slice Std.U8)
    (options : SealOptions)
    (h_key : CodecSealKeyKnown self)
    (h_fits : SealFits self payload.val.length options.associated_data.val.length) :
    seal_with self payload options ⦃ (result : String) =>
      sealAt self payload.val options.associated_data.val options.ttl ExtModel.nowMs.val =
        some (ExtModel.utf8 result) ⦄ := by
  unfold seal_with model.request_state.RequestStateCodec.now_ms
  simp only [bind_ok]
  exact seal_at_spec self payload options ExtModel.nowMs h_key h_fits

/-- **R10, corollary. `seal_with` under `CodecValid` and a length premise**

The conclusion of R10 (clock as in R10: one reading, parametric), with (S) and (D) replaced by
`CodecValid self` and (Ls) `associated_data.len() + 2 * payload.len() + 512 ≤ isize::MAX`. Under
`CodecValid` an `rs2` key id has at most 255 bytes, so the capacity sum is at most
`6 + 340 + b64Len(8 + p) + 44 ≤ 404 + 4p/3` and the transcript at most `305 + a + p`; (S) is
the third clause of `CodecValid`. Inherited exceptions: (K), (H); (V) does not arise (the
transcript is at most `305 + a + p ≤ isize::MAX` by (Ls)). Not tagged `@[step]`. -/
theorem seal_with_spec_of_length_le (self : RequestStateCodec) (payload : Slice Std.U8)
    (options : SealOptions)
    (h_valid : CodecValid self)
    (h_len : options.associated_data.val.length + 2 * payload.val.length + 512 ≤
      ExtModel.maxStringBytes) :
    seal_with self payload options ⦃ (result : String) =>
      sealAt self payload.val options.associated_data.val options.ttl ExtModel.nowMs.val =
        some (ExtModel.utf8 result) ⦄ := by
  obtain ⟨h_key, h_fits⟩ :=
    Proofs.RequestState.Seal.codecSealKeyKnown_and_sealFits_of_codecValid self
      payload.val.length options.associated_data.val.length h_valid h_len
  exact seal_with_spec self payload options h_key h_fits

/-- **R09. Spec theorem for `rmcp::model::request_state::RequestStateCodec::seal`**

Seals `payload` with the default options, no associated data and no ttl
(`self.seal_with(payload, &SealOptions::default())`, patched lines 436–438, upstream 446–448;
`SealOptions::default()` as R01): the UTF-8 bytes of the token are `sealAt self payload [] none t`
for `t = ExtModel.nowMs`. Clock as R10; here the token does not depend on the reading
(`sealExpiry none t = 0`, so the body is `frameBytes 0 payload`), but the clock is still read.

Premises (S) `h_key` and (D) `h_fits` with no associated data. Inherited exceptions: (K) (the
clock is read even though the token does not use it), (H). (V) does not arise: (D) bounds the
transcript by the capacity sum. Rust tests: `seal_open_roundtrips_bytes` (patched lines
818–824), `empty_payload_roundtrips` (lines 845–850). -/
@[step]
theorem seal_spec (self : RequestStateCodec) (payload : Slice Std.U8)
    (h_key : CodecSealKeyKnown self)
    (h_fits : SealFits self payload.val.length 0) :
    RequestStateCodec.seal self payload ⦃ (result : String) =>
      sealAt self payload.val [] none ExtModel.nowMs.val = some (ExtModel.utf8 result) ⦄ := by
  unfold RequestStateCodec.seal
  simp only [SealOptions.Insts.CoreDefaultDefault.default,
    Shared0Slice.Insts.CoreDefaultDefault.default,
    core.option.Option.Insts.CoreDefaultDefault.default, bind_ok]
  have h := seal_with_spec self payload { associated_data := Slice.new Std.U8, ttl := none }
    h_key (by simp only [Slice.new_val, List.length_nil]; exact h_fits)
  simp only [Slice.new_val] at h
  exact h

/-- **R09, corollary. `seal` under `CodecValid` and a length premise**

As R09, with (S) and (D) replaced by `CodecValid self` and
`2 * payload.len() + 512 ≤ isize::MAX`. Clock as R09: one reading `ExtModel.nowMs`, parametric;
nothing about two calls; the value of `nowMs` is not constrained. Inherited exceptions as R09:
(K) clock range (the clock is read), (H) HMAC `2^61`. Not tagged `@[step]`. -/
theorem seal_spec_of_length_le (self : RequestStateCodec) (payload : Slice Std.U8)
    (h_valid : CodecValid self)
    (h_len : 2 * payload.val.length + 512 ≤ ExtModel.maxStringBytes) :
    RequestStateCodec.seal self payload ⦃ (result : String) =>
      sealAt self payload.val [] none ExtModel.nowMs.val = some (ExtModel.utf8 result) ⦄ := by
  obtain ⟨h_key, h_fits⟩ :=
    Proofs.RequestState.Seal.codecSealKeyKnown_and_sealFits_of_codecValid self
      payload.val.length 0 h_valid (by omega)
  exact seal_spec self payload h_key h_fits

end rmcp.model.request_state.RequestStateCodec
