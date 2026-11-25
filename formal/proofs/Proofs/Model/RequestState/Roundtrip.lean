/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Rmcp.Funs
public import Defs.Wire
public import Defs.CodecState
public import Proofs.External.Base64
public import Proofs.External.String
public import Proofs.Model.RequestStateWire.Common
public import Proofs.Model.RequestState.SealRs1
public import Proofs.Model.RequestState.SealRs2
public import Proofs.Model.RequestState.OpenRs1At
public import Proofs.Model.RequestState.OpenRs2At
public import Proofs.Model.RequestState.OpenAt
public import Proofs.Model.RequestState.Seal

@[expose] public section

/-!
# Round trips of the request-state codec (S15)

Plan Section 3, "Round-trip", and Section 5, "Theorem names": sealing a body with `seal_rs1`
(E07) or `seal_rs2` (E08) and opening the token with `open_rs1_at` (E09), `open_rs2_at` (E10) or
`open_at` (E11) returns exactly `body[8..]`. The four composition theorems `rs1_roundtrip`,
`rs2_roundtrip`, `open_at_roundtrip_rs1` and `open_at_roundtrip_rs2` compose the spec theorems
of E07–E11; no target function body is unfolded. Since R09–R15 (translation patch 03, statements
signed off 2026-11-25) the file also holds the model round trip `openAt_eq_ok_of_sealAt_eq_some`
(`openAt` of a `sealAt` token) and R10b `seal_at_roundtrip` (the private `seal_at`, R10a, then
`open_at`, E11), with the token bounds `token_bounds_of_sealAt_eq_some`.

Proof outline: the seal spec gives the UTF-8 bytes of the token; their `.`-components are the
version and the Base64url encodings (which contain no `.`), so the opener's `.`-count and
transcript premises hold, and the opener's result `openRs1`/`openRs2`/`openAt` (Defs.CodecState)
evaluates to `Ok (body[8..])` under the key, expiry and body-length premises. The existence of a
`Str` holding the token's bytes follows from the capacity premise `h_cap` and
`maxStringBytes ≤ Usize.max`.

Source: "crates/rmcp/src/model/request_state.rs", lines 559–570 (`open_at`), 572–583
(`seal_rs1`), 585–605 (`seal_rs2`), 607–641 (`open_rs1_at`), 659–693 (`open_rs2_at`) and
695–702 (`open_authenticated_body`) in the patched copy (patch 01 on origin/main 7caec76,
D2 fallback 2026-11-23); line numbers refer to it.
-/

open Aeneas Aeneas.Std Result
open rmcp
open rmcp.model.request_state
open Defs.Wire (dot versionV1 versionV2 transcriptV1 transcriptV2 b64Len expiryLen bodyExpiry
  maxKidLen components Expired)
open Defs.CodecState (CodecFallbacksKnown lookupKey resultBytes openRs1 openRs2 openAt openBody
  Rs1Accepts noRs1Fallback TagVerifies maxEncodedKidLen)

namespace Proofs.RequestState.Roundtrip

open Proofs.RequestStateWire Proofs.External.Base64

theorem ne_dot_of_mem_versionV1 : ∀ x ∈ versionV1, x ≠ dot := by decide

theorem ne_dot_of_mem_versionV2 : ∀ x ∈ versionV2, x ≠ dot := by decide

theorem ne_dot_of_mem_b64 (x : List U8) : ∀ c ∈ ExtModel.b64 x, c ≠ dot :=
  fun _ hc h => dot_notMem_b64 x (h ▸ hc)

/-- The `.`-components of an `rs1` token are its version, body encoding and tag encoding. -/
theorem components_tokenV1 (b t : List U8) :
    components (versionV1 ++ [dot] ++ ExtModel.b64 b ++ [dot] ++ ExtModel.b64 t) =
      [versionV1, ExtModel.b64 b, ExtModel.b64 t] := by
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [components_append_dot _ _ ne_dot_of_mem_versionV1,
    components_append_dot _ _ (ne_dot_of_mem_b64 b),
    components_eq_singleton _ (ne_dot_of_mem_b64 t)]

/-- The `.`-components of an `rs2` token are its version and the encodings of kid, body and
tag. -/
theorem components_tokenV2 (k b t : List U8) :
    components (versionV2 ++ [dot] ++ ExtModel.b64 k ++ [dot] ++ ExtModel.b64 b ++ [dot] ++
      ExtModel.b64 t) = [versionV2, ExtModel.b64 k, ExtModel.b64 b, ExtModel.b64 t] := by
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [components_append_dot _ _ ne_dot_of_mem_versionV2,
    components_append_dot _ _ (ne_dot_of_mem_b64 k),
    components_append_dot _ _ (ne_dot_of_mem_b64 b),
    components_eq_singleton _ (ne_dot_of_mem_b64 t)]

/-- A byte list with at most four `.`-components has fewer than `Usize.max` `.` bytes (the
`.`-count premise of E09 and E10). -/
theorem count_dot_lt_of_length_components_le (s : List U8) (h : (components s).length ≤ 4) :
    s.count dot < Usize.max := by
  rw [length_components] at h
  have : 4 < Usize.max := by scalar_tac
  omega

/-- A body of at least 8 bytes that is not expired opens to `body[8..]`. -/
theorem openBody_eq_ok (body : List U8) (now : Int) (h_body : expiryLen ≤ body.length)
    (h_expiry : ¬ Expired (bodyExpiry body) now) :
    openBody body now = .ok (body.drop expiryLen) := by
  simp only [openBody, Nat.not_lt.mpr h_body, ↓reduceIte, h_expiry]

/-- The expected result of opening a sealed `rs1` token under the round-trip premises. -/
theorem openRs1_eq_ok (self : RequestStateCodec) (tok key ad body : List U8) (now : Int)
    (hc : components tok = [versionV1, ExtModel.b64 body,
      ExtModel.b64 (ExtModel.hmacSha256 key (transcriptV1 ad body)).val])
    (h_body : expiryLen ≤ body.length)
    (h_expiry : ¬ Expired (bodyExpiry body) now)
    (h_key : (∃ k, self.keys = .Single k ∧ k.inner.val = key) ∨
      (∃ keys seal_mode rs1_fallbacks kid, self.keys = .Ring keys seal_mode rs1_fallbacks ∧
        kid ∈ rs1_fallbacks.val ∧ lookupKey keys kid = some key)) :
    openRs1 self tok ad now = .ok (body.drop expiryLen) := by
  have hnf : noRs1Fallback self = false := by
    rcases h_key with ⟨k, hk, _⟩ | ⟨keys, sm, fbs, kid, hk, hmem, _⟩
    · simp only [noRs1Fallback, hk]
    · simp only [noRs1Fallback, hk, List.isEmpty_eq_false_iff]
      exact List.ne_nil_of_mem hmem
  have hacc : Rs1Accepts self (transcriptV1 ad body)
      (ExtModel.hmacSha256 key (transcriptV1 ad body)).val := by
    rcases h_key with ⟨k, hk, hkv⟩ | ⟨keys, sm, fbs, kid, hk, hmem, hl⟩
    · simp only [Rs1Accepts, hk, TagVerifies, hkv]
    · simp only [Rs1Accepts, hk]
      exact ⟨kid, hmem, key, hl, rfl⟩
  rw [openRs1, hc]
  simp only [ne_eq, not_true_eq_false, ↓reduceIte, b64Decode_b64, hnf, Bool.false_eq_true,
    hacc]
  exact openBody_eq_ok body now h_body h_expiry

/-- The expected result of opening a sealed `rs2` token under the round-trip premises. -/
theorem openRs2_eq_ok (self : RequestStateCodec) (tok kid key ad body : List U8) (now : Int)
    (kidStr : String)
    (hc : components tok = [versionV2, ExtModel.b64 kid, ExtModel.b64 body,
      ExtModel.b64 (ExtModel.hmacSha256 key (transcriptV2 kid ad body)).val])
    (h_body : expiryLen ≤ body.length)
    (h_expiry : ¬ Expired (bodyExpiry body) now)
    (h_kid_utf8 : kid = ExtModel.utf8 kidStr)
    (h_kid_len : 1 ≤ kid.length ∧ kid.length ≤ maxKidLen)
    (h_key : ∃ keys seal_mode rs1_fallbacks, self.keys = .Ring keys seal_mode rs1_fallbacks ∧
      lookupKey keys kidStr = some key) :
    openRs2 self tok ad now = .ok (body.drop expiryLen) := by
  obtain ⟨keys, sm, fbs, hk, hl⟩ := h_key
  have henc : ¬ maxEncodedKidLen < (ExtModel.b64 kid).length := by
    rw [length_b64]
    simp only [maxEncodedKidLen, maxKidLen] at h_kid_len ⊢
    omega
  have hkl : ¬ (kid.length = 0 ∨ maxKidLen < kid.length) := by omega
  have hs : ExtModel.strOfBytes? kid = some kidStr := by
    rw [h_kid_utf8]
    exact Proofs.External.Utf8.strOfBytes?_utf8 kidStr
  rw [openRs2, hc]
  simp only [ne_eq, not_true_eq_false, ↓reduceIte, henc, b64Decode_b64, hkl, hs, hk, hl,
    TagVerifies]
  exact openBody_eq_ok body now h_body h_expiry

/-- An HMAC SHA-256 tag has 32 bytes. -/
theorem length_hmacSha256 (key msg : List U8) : (ExtModel.hmacSha256 key msg).val.length = 32 := by
  simp only [Array.property, UScalar.ofNatCore_val_eq]

end Proofs.RequestState.Roundtrip

open Proofs.RequestState.Roundtrip

namespace rmcp.model.request_state.RequestStateCodec

/-- **rs1 round trip: `seal_rs1` then `open_rs1_at`** (plan S15, plan Section 3 "Round-trip")

About the translated `seal_rs1` (E07, request_state.rs lines 572–583) and `open_rs1_at` (E09,
lines 607–641). Sealing `body` under `key` and `associated_data` terminates; some `sealed : Str`
holds the UTF-8 bytes of the token; and opening any such `sealed` with the codec `self`, the same
`associated_data` and the time `now_ms` terminates with `Ok` of `body[8..]`. Premises: the
no-overflow domains `h_len` (transcript) and `h_cap` (capacity sum) of E07; the body has at
least 8 bytes (`h_body`); the body is not expired at `now_ms` (`h_expiry`); the same associated
data for both calls; `self` is a single-key codec with the bytes of `key` or a ring with an rs1
fallback id whose key has the bytes of `key` (`h_key`); every rs1 fallback id is a key id
(`h_fallbacks`). -/
theorem rs1_roundtrip (self : RequestStateCodec) (key : Slice Std.U8)
    (associated_data : Slice Std.U8) (body : Slice Std.U8) (now_ms : Std.I64)
    (h_len : (transcriptV1 associated_data.val body.val).length ≤ Usize.max)
    (h_cap : versionV1.length + 2 + b64Len body.val.length + b64Len 32 ≤
      ExtModel.maxStringBytes)
    (h_body : expiryLen ≤ body.val.length)
    (h_expiry : ¬ Expired (bodyExpiry body.val) now_ms.val)
    (h_key : (∃ k, self.keys = .Single k ∧ k.inner.val = key.val) ∨
      (∃ keys seal_mode rs1_fallbacks kid, self.keys = .Ring keys seal_mode rs1_fallbacks ∧
        kid ∈ rs1_fallbacks.val ∧ lookupKey keys kid = some key.val))
    (h_fallbacks : CodecFallbacksKnown self) :
    seal_rs1 key associated_data body ⦃ (token : String) =>
      (∃ sealed : Str, (sealed : Slice Std.U8).val = ExtModel.utf8 token) ∧
      ∀ sealed : Str, (sealed : Slice Std.U8).val = ExtModel.utf8 token →
      open_rs1_at self sealed associated_data now_ms ⦃ (result :
          core.result.Result (alloc.vec.Vec Std.U8) RequestStateError) =>
        -- line 640 → E01 line 698: `Ok(payload.to_vec())`, payload = body[8..]
        resultBytes result = .ok (body.val.drop expiryLen) ⦄ ⦄ := by
  apply WP.spec_mono (seal_rs1_spec key associated_data body h_len h_cap)
  intro token htok
  refine ⟨⟨Slice.from (ExtModel.utf8 token) ?_, Slice.from_val _ _⟩, fun sealed hs => ?_⟩
  · have h1 := Proofs.External.Base64.length_b64_le_b64Len body.val
    have h2 := Proofs.External.Base64.length_b64_le_b64Len
      (ExtModel.hmacSha256 key.val (transcriptV1 associated_data.val body.val)).val
    have h4 := Proofs.External.Utf8.maxStringBytes_le_usize_max
    rw [length_hmacSha256] at h2
    rw [htok]
    simp only [List.length_append, List.length_singleton]
    omega
  · rw [htok] at hs
    have hc := components_tokenV1 body.val (ExtModel.hmacSha256 key.val
      (transcriptV1 associated_data.val body.val)).val
    rw [← hs] at hc
    apply WP.spec_mono (open_rs1_at_spec self sealed associated_data now_ms
      (count_dot_lt_of_length_components_le _ (by rw [hc]; exact Nat.le_succ 3)) ?_ h_fallbacks)
    · intro r hr
      rw [hr]
      exact openRs1_eq_ok self _ key.val associated_data.val body.val now_ms.val hc h_body
        h_expiry h_key
    · intro b t bd hcb hd
      rw [hc] at hcb
      simp only [List.cons.injEq, and_true, true_and] at hcb
      rw [← hcb.1, Proofs.External.Base64.b64Decode_b64, Option.some.injEq] at hd
      rw [← hd]
      exact h_len

/-- **rs2 round trip: `seal_rs2` then `open_rs2_at`** (plan S15, plan Section 3 "Round-trip")

About the translated `seal_rs2` (E08, request_state.rs lines 585–605) and `open_rs2_at` (E10,
lines 659–693). Sealing `body` under `kid`, `key` and `associated_data` terminates; some
`sealed : Str` holds the UTF-8 bytes of the token; and opening any such `sealed` with the codec
`self`, the same `associated_data` and the time `now_ms` terminates with `Ok` of `body[8..]`.
Premises: the no-overflow domains `h_len` and `h_cap` of E08; the body has at least 8 bytes
(`h_body`); the body is not expired at `now_ms` (`h_expiry`); the same associated data for both
calls; the bytes of `kid` are the UTF-8 encoding of `kidStr` (`h_kid_utf8`) and number 1 to 255
(`h_kid_len`); `self` is a ring whose key table holds the bytes of `key` under `kidStr`
(`h_key`). -/
theorem rs2_roundtrip (self : RequestStateCodec) (kid : Str) (key : Slice Std.U8)
    (associated_data : Slice Std.U8) (body : Slice Std.U8) (now_ms : Std.I64) (kidStr : String)
    (h_len : (transcriptV2 (kid : Slice Std.U8).val associated_data.val body.val).length ≤
      Usize.max)
    (h_cap : versionV2.length + 3 + b64Len (kid : Slice Std.U8).val.length +
      b64Len body.val.length + b64Len 32 ≤ ExtModel.maxStringBytes)
    (h_body : expiryLen ≤ body.val.length)
    (h_expiry : ¬ Expired (bodyExpiry body.val) now_ms.val)
    (h_kid_utf8 : (kid : Slice Std.U8).val = ExtModel.utf8 kidStr)
    (h_kid_len : 1 ≤ (kid : Slice Std.U8).val.length ∧
      (kid : Slice Std.U8).val.length ≤ maxKidLen)
    (h_key : ∃ keys seal_mode rs1_fallbacks, self.keys = .Ring keys seal_mode rs1_fallbacks ∧
      lookupKey keys kidStr = some key.val) :
    seal_rs2 kid key associated_data body ⦃ (token : String) =>
      (∃ sealed : Str, (sealed : Slice Std.U8).val = ExtModel.utf8 token) ∧
      ∀ sealed : Str, (sealed : Slice Std.U8).val = ExtModel.utf8 token →
      open_rs2_at self sealed associated_data now_ms ⦃ (result :
          core.result.Result (alloc.vec.Vec Std.U8) RequestStateError) =>
        -- line 692 → E01 line 698: `Ok(payload.to_vec())`, payload = body[8..]
        resultBytes result = .ok (body.val.drop expiryLen) ⦄ ⦄ := by
  apply WP.spec_mono (seal_rs2_spec kid key associated_data body h_len h_cap)
  intro token htok
  refine ⟨⟨Slice.from (ExtModel.utf8 token) ?_, Slice.from_val _ _⟩, fun sealed hs => ?_⟩
  · have h0 := Proofs.External.Base64.length_b64_le_b64Len (kid : Slice U8).val
    have h1 := Proofs.External.Base64.length_b64_le_b64Len body.val
    have h2 := Proofs.External.Base64.length_b64_le_b64Len
      (ExtModel.hmacSha256 key.val (transcriptV2 (kid : Slice U8).val associated_data.val
        body.val)).val
    have h4 := Proofs.External.Utf8.maxStringBytes_le_usize_max
    rw [length_hmacSha256] at h2
    rw [htok]
    simp only [List.length_append, List.length_singleton]
    omega
  · rw [htok] at hs
    have hc := components_tokenV2 (kid : Slice Std.U8).val body.val (ExtModel.hmacSha256 key.val
      (transcriptV2 (kid : Slice Std.U8).val associated_data.val body.val)).val
    rw [← hs] at hc
    apply WP.spec_mono (open_rs2_at_spec self sealed associated_data now_ms
      (count_dot_lt_of_length_components_le _ (by rw [hc]; exact Nat.le_refl 4)) ?_)
    · intro r hr
      rw [hr]
      exact openRs2_eq_ok self _ _ key.val associated_data.val body.val now_ms.val kidStr
        hc h_body h_expiry h_kid_utf8 h_kid_len h_key
    · intro k b t kd bd hcb hk hd
      rw [hc] at hcb
      simp only [List.cons.injEq, and_true, true_and] at hcb
      rw [← hcb.1, Proofs.External.Base64.b64Decode_b64, Option.some.injEq] at hk
      rw [← hcb.2.1, Proofs.External.Base64.b64Decode_b64, Option.some.injEq] at hd
      rw [← hk, ← hd]
      exact h_len

/-- **rs1 round trip through `open_at`: `seal_rs1` then `open_at`** (plan S15, plan Section 3
"Round-trip")

About the translated `seal_rs1` (E07, request_state.rs lines 572–583) and `open_at` (E11, lines
559–570), which dispatches an `rs1` token to `open_rs1_at` (line 566). Same conclusion and
premises as `rs1_roundtrip`: the no-overflow domains `h_len`, `h_cap` of E07, a body of at least
8 bytes, not expired at `now_ms`, the same associated data, the key condition `h_key` and the
fallback clause `h_fallbacks`. -/
theorem open_at_roundtrip_rs1 (self : RequestStateCodec) (key : Slice Std.U8)
    (associated_data : Slice Std.U8) (body : Slice Std.U8) (now_ms : Std.I64)
    (h_len : (transcriptV1 associated_data.val body.val).length ≤ Usize.max)
    (h_cap : versionV1.length + 2 + b64Len body.val.length + b64Len 32 ≤
      ExtModel.maxStringBytes)
    (h_body : expiryLen ≤ body.val.length)
    (h_expiry : ¬ Expired (bodyExpiry body.val) now_ms.val)
    (h_key : (∃ k, self.keys = .Single k ∧ k.inner.val = key.val) ∨
      (∃ keys seal_mode rs1_fallbacks kid, self.keys = .Ring keys seal_mode rs1_fallbacks ∧
        kid ∈ rs1_fallbacks.val ∧ lookupKey keys kid = some key.val))
    (h_fallbacks : CodecFallbacksKnown self) :
    seal_rs1 key associated_data body ⦃ (token : String) =>
      (∃ sealed : Str, (sealed : Slice Std.U8).val = ExtModel.utf8 token) ∧
      ∀ sealed : Str, (sealed : Slice Std.U8).val = ExtModel.utf8 token →
      open_at self sealed associated_data now_ms ⦃ (result :
          core.result.Result (alloc.vec.Vec Std.U8) RequestStateError) =>
        -- line 566 → line 640 → E01 line 698
        resultBytes result = .ok (body.val.drop expiryLen) ⦄ ⦄ := by
  apply WP.spec_mono (seal_rs1_spec key associated_data body h_len h_cap)
  intro token htok
  refine ⟨⟨Slice.from (ExtModel.utf8 token) ?_, Slice.from_val _ _⟩, fun sealed hs => ?_⟩
  · have h1 := Proofs.External.Base64.length_b64_le_b64Len body.val
    have h2 := Proofs.External.Base64.length_b64_le_b64Len
      (ExtModel.hmacSha256 key.val (transcriptV1 associated_data.val body.val)).val
    have h4 := Proofs.External.Utf8.maxStringBytes_le_usize_max
    rw [length_hmacSha256] at h2
    rw [htok]
    simp only [List.length_append, List.length_singleton]
    omega
  · rw [htok] at hs
    have hc := components_tokenV1 body.val (ExtModel.hmacSha256 key.val
      (transcriptV1 associated_data.val body.val)).val
    rw [← hs] at hc
    apply WP.spec_mono (open_at_spec self sealed associated_data now_ms ?_ ?_
      (fun _ => h_fallbacks))
    · intro r hr
      rw [hr, openAt, hc]
      simp only [List.head?_cons, ↓reduceIte]
      exact openRs1_eq_ok self _ key.val associated_data.val body.val now_ms.val hc h_body
        h_expiry h_key
    · intro b t bd hcb hd
      rw [hc] at hcb
      simp only [List.cons.injEq, and_true, true_and] at hcb
      rw [← hcb.1, Proofs.External.Base64.b64Decode_b64, Option.some.injEq] at hd
      rw [← hd]
      exact h_len
    · intro k b t kd bd hcb
      rw [hc] at hcb
      simp only [List.cons.injEq, List.ne_cons_self, and_false] at hcb

/-- **rs2 round trip through `open_at`: `seal_rs2` then `open_at`** (plan S15, plan Section 3
"Round-trip")

About the translated `seal_rs2` (E08, request_state.rs lines 585–605) and `open_at` (E11, lines
559–570), which dispatches an `rs2` token to `open_rs2_at` (line 567). Same conclusion and
premises as `rs2_roundtrip`: the no-overflow domains `h_len`, `h_cap` of E08, a body of at least
8 bytes, not expired at `now_ms`, the same associated data, a UTF-8 kid `kidStr` of 1 to 255
bytes, and a ring holding the bytes of `key` under `kidStr`. No codec-state premise: the token
starts with `"rs2"`. -/
theorem open_at_roundtrip_rs2 (self : RequestStateCodec) (kid : Str) (key : Slice Std.U8)
    (associated_data : Slice Std.U8) (body : Slice Std.U8) (now_ms : Std.I64) (kidStr : String)
    (h_len : (transcriptV2 (kid : Slice Std.U8).val associated_data.val body.val).length ≤
      Usize.max)
    (h_cap : versionV2.length + 3 + b64Len (kid : Slice Std.U8).val.length +
      b64Len body.val.length + b64Len 32 ≤ ExtModel.maxStringBytes)
    (h_body : expiryLen ≤ body.val.length)
    (h_expiry : ¬ Expired (bodyExpiry body.val) now_ms.val)
    (h_kid_utf8 : (kid : Slice Std.U8).val = ExtModel.utf8 kidStr)
    (h_kid_len : 1 ≤ (kid : Slice Std.U8).val.length ∧
      (kid : Slice Std.U8).val.length ≤ maxKidLen)
    (h_key : ∃ keys seal_mode rs1_fallbacks, self.keys = .Ring keys seal_mode rs1_fallbacks ∧
      lookupKey keys kidStr = some key.val) :
    seal_rs2 kid key associated_data body ⦃ (token : String) =>
      (∃ sealed : Str, (sealed : Slice Std.U8).val = ExtModel.utf8 token) ∧
      ∀ sealed : Str, (sealed : Slice Std.U8).val = ExtModel.utf8 token →
      open_at self sealed associated_data now_ms ⦃ (result :
          core.result.Result (alloc.vec.Vec Std.U8) RequestStateError) =>
        -- line 567 → line 692 → E01 line 698
        resultBytes result = .ok (body.val.drop expiryLen) ⦄ ⦄ := by
  apply WP.spec_mono (seal_rs2_spec kid key associated_data body h_len h_cap)
  intro token htok
  refine ⟨⟨Slice.from (ExtModel.utf8 token) ?_, Slice.from_val _ _⟩, fun sealed hs => ?_⟩
  · have h0 := Proofs.External.Base64.length_b64_le_b64Len (kid : Slice U8).val
    have h1 := Proofs.External.Base64.length_b64_le_b64Len body.val
    have h2 := Proofs.External.Base64.length_b64_le_b64Len
      (ExtModel.hmacSha256 key.val (transcriptV2 (kid : Slice U8).val associated_data.val
        body.val)).val
    have h4 := Proofs.External.Utf8.maxStringBytes_le_usize_max
    rw [length_hmacSha256] at h2
    rw [htok]
    simp only [List.length_append, List.length_singleton]
    omega
  · rw [htok] at hs
    have hc := components_tokenV2 (kid : Slice Std.U8).val body.val (ExtModel.hmacSha256 key.val
      (transcriptV2 (kid : Slice Std.U8).val associated_data.val body.val)).val
    rw [← hs] at hc
    apply WP.spec_mono (open_at_spec self sealed associated_data now_ms ?_ ?_ ?_)
    · intro r hr
      have hv : versionV2 ≠ versionV1 := by decide
      rw [hr, openAt, hc]
      simp only [List.head?_cons, Option.some.injEq, hv, ↓reduceIte]
      exact openRs2_eq_ok self _ _ key.val associated_data.val body.val now_ms.val kidStr
        hc h_body h_expiry h_kid_utf8 h_kid_len h_key
    · intro b t bd hcb
      rw [hc] at hcb
      simp only [List.cons.injEq, List.cons_ne_self, and_false] at hcb
    · intro k b t kd bd hcb hk hd
      rw [hc] at hcb
      simp only [List.cons.injEq, and_true, true_and] at hcb
      rw [← hcb.1, Proofs.External.Base64.b64Decode_b64, Option.some.injEq] at hk
      rw [← hcb.2.1, Proofs.External.Base64.b64Decode_b64, Option.some.injEq] at hd
      rw [← hk, ← hd]
      exact h_len
    · intro hh
      rw [hc] at hh
      simp only [List.head?_cons, Option.some.injEq] at hh
      exact absurd hh (by decide)

end rmcp.model.request_state.RequestStateCodec

/-! ## R09–R15: the model round trip and R10b -/

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

/-! ## Optional composition (model level, no translated function, no clock)

A round trip of the `Defs` models at explicit times (internal; proved in
`Proofs/Model/RequestState/Roundtrip.lean`, restated in
`formal/proofs/Proofs/Internal/Model/RequestState.lean`): with R10 at one reading and R08 at
another it is the user-level round trip, but that combination involves two readings and is not
stated. -/

namespace Proofs.RequestState.Roundtrip

open Defs.CodecState (sealAt sealExpiry)

/-- The token of `sealAt` under the seal domain (D): it fits in a `String`, and the transcripts
that `open_at` rebuilds from its components fit in `usize::MAX` bytes. -/
theorem token_bounds_of_sealAt_eq_some (codec : RequestStateCodec) (payload ad : List U8)
    (ttl : Option core.time.Duration) (now : Int) (tok : List U8)
    (h : Defs.CodecState.sealAt codec payload ad ttl now = some tok)
    (hf : Defs.CodecState.SealFits codec payload.length ad.length) :
    tok.length ≤ ExtModel.maxStringBytes ∧
    (∀ b t body, components tok = [versionV1, b, t] → ExtModel.b64Decode b = some body →
      (transcriptV1 ad body).length ≤ Usize.max) ∧
    (∀ k b t kid body, components tok = [versionV2, k, b, t] →
      ExtModel.b64Decode k = some kid → ExtModel.b64Decode b = some body →
      (transcriptV2 kid ad body).length ≤ Usize.max) := by
  have hv1 : versionV1.length = 3 := rfl
  have hv2 : versionV2.length = 3 := rfl
  have hd1 : Defs.Wire.domainV1.length = 26 := rfl
  have hd2 : Defs.Wire.domainV2.length = 26 := rfl
  have hel : Defs.Wire.expiryLen = 8 := rfl
  set body := Defs.Wire.frameBytes (Defs.CodecState.sealExpiry ttl now) payload with hbody
  have hbl : body.length = 8 + payload.length := Proofs.RequestStateWire.length_frameBytes _ _
  -- the rs1 case, shared by a single-key codec and an rs1 keyring
  have rs1 : ∀ key : List U8, tok = Defs.CodecState.tokenV1 key ad body →
      Defs.Wire.domainV1.length + 8 + ad.length + Defs.Wire.expiryLen + payload.length ≤
        Usize.max ∧
      versionV1.length + 2 + Defs.Wire.b64Len (Defs.Wire.expiryLen + payload.length) +
        Defs.Wire.b64Len 32 ≤ ExtModel.maxStringBytes →
      tok.length ≤ ExtModel.maxStringBytes ∧
      (∀ b t body, components tok = [versionV1, b, t] → ExtModel.b64Decode b = some body →
        (transcriptV1 ad body).length ≤ Usize.max) ∧
      (∀ k b t kid body, components tok = [versionV2, k, b, t] →
        ExtModel.b64Decode k = some kid → ExtModel.b64Decode b = some body →
        (transcriptV2 kid ad body).length ≤ Usize.max) := by
    intro key htok ⟨hf1, hf2⟩
    have hc := Proofs.RequestState.Roundtrip.components_tokenV1 body
      (ExtModel.hmacSha256 key (transcriptV1 ad body)).val
    rw [← Defs.CodecState.tokenV1, ← htok] at hc
    have h1 := Proofs.External.Base64.length_b64_le_b64Len body
    have h2 := Proofs.External.Base64.length_b64_le_b64Len
      (ExtModel.hmacSha256 key (transcriptV1 ad body)).val
    rw [Proofs.RequestState.Roundtrip.length_hmacSha256] at h2
    refine ⟨?_, ?_, ?_⟩
    · rw [htok, Defs.CodecState.tokenV1]
      simp only [List.length_append, List.length_singleton]
      rw [hbl] at h1
      rw [hel] at hf2
      omega
    · intro b t bd hcb hd
      rw [hc] at hcb
      simp only [List.cons.injEq, and_true, true_and] at hcb
      rw [← hcb.1, Proofs.External.Base64.b64Decode_b64, Option.some.injEq] at hd
      rw [← hd, Proofs.RequestStateWire.length_transcriptV1, hbl]
      rw [hel, hd1] at hf1
      omega
    · intro k b t kid bd hcb
      rw [hc] at hcb
      simp only [List.cons.injEq, reduceCtorEq, and_false] at hcb
  rcases codec with ⟨key | ⟨keys, sm, fb⟩⟩
  · simp only [Defs.CodecState.sealAt, Option.some.injEq] at h
    exact rs1 key.inner.val h.symm hf
  · cases sm with
    | Rs1 kid =>
      simp only [Defs.CodecState.sealAt] at h
      obtain ⟨k, -, hk⟩ := Option.map_eq_some_iff.1 h
      exact rs1 k hk.symm hf
    | Rs2 kid =>
      simp only [Defs.CodecState.sealAt] at h
      obtain ⟨k, -, hk⟩ := Option.map_eq_some_iff.1 h
      rw [← hbody] at hk
      simp only [Defs.CodecState.SealFits] at hf
      obtain ⟨hf1, hf2⟩ := hf
      have hc := Proofs.RequestState.Roundtrip.components_tokenV2 (ExtModel.utf8 kid) body
        (ExtModel.hmacSha256 k (transcriptV2 (ExtModel.utf8 kid) ad body)).val
      rw [← Defs.CodecState.tokenV2, hk] at hc
      have hkl : (ExtModel.utf8 kid).length = kid.utf8ByteSize :=
        Proofs.External.Utf8.length_utf8 kid
      have h0 := Proofs.External.Base64.length_b64_le_b64Len (ExtModel.utf8 kid)
      have h1 := Proofs.External.Base64.length_b64_le_b64Len body
      have h2 := Proofs.External.Base64.length_b64_le_b64Len
        (ExtModel.hmacSha256 k (transcriptV2 (ExtModel.utf8 kid) ad body)).val
      rw [Proofs.RequestState.Roundtrip.length_hmacSha256] at h2
      refine ⟨?_, ?_, ?_⟩
      · rw [← hk, Defs.CodecState.tokenV2]
        simp only [List.length_append, List.length_singleton]
        rw [hbl] at h1
        rw [hkl] at h0
        rw [hel] at hf2
        omega
      · intro b t bd hcb
        rw [hc] at hcb
        simp only [List.cons.injEq, reduceCtorEq, and_false] at hcb
      · intro kk b t kd bd hcb hk1 hb1
        rw [hc] at hcb
        simp only [List.cons.injEq, and_true, true_and] at hcb
        rw [← hcb.1, Proofs.External.Base64.b64Decode_b64, Option.some.injEq] at hk1
        rw [← hcb.2.1, Proofs.External.Base64.b64Decode_b64, Option.some.injEq] at hb1
        rw [← hk1, ← hb1, Proofs.RequestStateWire.length_transcriptV2, hbl, hkl]
        rw [hel, hd2] at hf1
        omega

/-- **Model round trip: `openAt` of a `sealAt` token** (plan Section 3, "Round-trip"). For a
`CodecValid` codec whose rs1 seal-mode id (if any) is also an rs1 fallback (`h_rs1`; true of every
codec from `with_rs1_signing`, which is not a clause of `CodecValid`), sealing at time `now` and
opening with the same associated data at time `now'` returns the payload, provided the expiry has
not passed (`h_live`, the negation of `Expired`). `CodecValid` is kept as the premise
(spec-owner decision 2026-11-25), but the proof uses only one consequence of it: for an `Rs2`
seal mode, the key id has 1 to 255 UTF-8 bytes (its fourth clause applied to the seal-mode id,
which is a key id by its third clause), so the `rs2` opener accepts its encoding (at most 340
bytes) and its length; for an `Rs1` seal mode it uses `h_rs1`; the key lookup comes from
`h_seal` itself. The other clauses (distinct ids, fallbacks known, key lengths) are unused. -/
theorem openAt_eq_ok_of_sealAt_eq_some (codec : RequestStateCodec) (payload ad : List U8)
    (ttl : Option core.time.Duration) (now now' : Std.I64) (token : List U8)
    (h_valid : CodecValid codec)
    (h_rs1 : ∀ keys kid rs1_fallbacks, codec.keys = .Ring keys (.Rs1 kid) rs1_fallbacks →
      kid ∈ rs1_fallbacks.val)
    (h_live : ¬ Expired (sealExpiry ttl now.val) now'.val)
    (h_seal : sealAt codec payload ad ttl now.val = some token) :
    openAt codec token ad now'.val = .ok payload := by
  have hImax : I64.max = 2 ^ 63 - 1 := by rw [I64.max_eq]; rfl
  have hImin : I64.min = - 2 ^ 63 := by rw [I64.min_eq]; rfl
  have hrange : -2 ^ 63 ≤ sealExpiry ttl now.val ∧ sealExpiry ttl now.val < 2 ^ 63 := by
    cases ttl with
    | none => simp only [sealExpiry]; omega
    | some d => simp only [sealExpiry, hImax, hImin]; omega
  set body := frameBytes (sealExpiry ttl now.val) payload with hbody
  have hbe : Defs.Wire.bodyExpiry body = sealExpiry ttl now.val :=
    Proofs.RequestStateWire.bodyExpiry_frameBytes _ _ hrange.1 hrange.2
  have hbl : expiryLen ≤ body.length := by
    rw [hbody, Proofs.RequestStateWire.length_frameBytes]; simp only [expiryLen]; omega
  have hdrop : body.drop expiryLen = payload := by
    have hl : (Defs.Wire.be64OfInt (sealExpiry ttl now.val)).length = 8 := by
      rw [Defs.Wire.be64OfInt, Proofs.RequestStateWire.length_be64]
    rw [hbody, frameBytes, expiryLen, List.drop_append_of_le_length (by omega),
      List.drop_of_length_le (by omega), List.nil_append]
  have hexp : ¬ Expired (Defs.Wire.bodyExpiry body) now'.val := by rw [hbe]; exact h_live
  have hv12 : versionV1 ≠ versionV2 := by decide
  rcases codec with ⟨key | ⟨keys, sm, fb⟩⟩
  · simp only [sealAt, Option.some.injEq] at h_seal
    subst h_seal
    have hc := Proofs.RequestState.Roundtrip.components_tokenV1 body
      (ExtModel.hmacSha256 key.inner.val (transcriptV1 ad body)).val
    rw [openAt, Defs.CodecState.tokenV1, hc]
    simp only [List.head?_cons, ↓reduceIte]
    rw [← hdrop]
    exact Proofs.RequestState.Roundtrip.openRs1_eq_ok _ _ key.inner.val ad body _ hc hbl hexp
      (Or.inl ⟨key, rfl, rfl⟩)
  · cases sm with
    | Rs1 kid =>
      simp only [sealAt] at h_seal
      obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.1 h_seal
      have hc := Proofs.RequestState.Roundtrip.components_tokenV1 body
        (ExtModel.hmacSha256 k (transcriptV1 ad body)).val
      rw [openAt, Defs.CodecState.tokenV1, hc]
      simp only [List.head?_cons, ↓reduceIte]
      rw [← hdrop]
      exact Proofs.RequestState.Roundtrip.openRs1_eq_ok _ _ k ad body _ hc hbl hexp
        (Or.inr ⟨keys, _, fb, kid, rfl, h_rs1 keys kid fb rfl, hk⟩)
    | Rs2 kid =>
      simp only [sealAt] at h_seal
      obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.1 h_seal
      have hc := Proofs.RequestState.Roundtrip.components_tokenV2 (ExtModel.utf8 kid) body
        (ExtModel.hmacSha256 k (transcriptV2 (ExtModel.utf8 kid) ad body)).val
      simp only [CodecValid] at h_valid
      obtain ⟨-, -, hsm, hent⟩ := h_valid
      simp only [sealModeKid] at hsm
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hsm
      have hk2 := (hent e he).2
      rw [openAt, Defs.CodecState.tokenV2, hc]
      simp only [List.head?_cons, Option.some.injEq, Ne.symm hv12, ↓reduceIte]
      rw [← hdrop]
      refine Proofs.RequestState.Roundtrip.openRs2_eq_ok _ _ _ k ad body _ e.1 hc hbl hexp rfl
        ?_ ⟨keys, _, fb, rfl, hk⟩
      rw [Proofs.External.Utf8.length_utf8]
      exact hk2

end Proofs.RequestState.Roundtrip

namespace rmcp.model.request_state.RequestStateCodec

/-- **R10b (internal). Round trip of the translated `seal_at` and `open_at`** (plan Section 3,
"Round-trip"; explicit times, no clock reading)

About the private `seal_at` (R10a; patched lines 533–561, upstream 540–569) and `open_at` (E11;
patched lines 563–574, upstream 571–582). Beside `open_at_roundtrip_rs1`/`rs2` (S15); restated
as `Theorems.request_state.RequestStateCodec.seal_at_roundtrip` in
`formal/proofs/Proofs/Internal/Model/RequestState.lean`. Sealing `payload` with `options` at time
`now` terminates; some `sealed : Str` holds the UTF-8 bytes of the token; and opening any such
`sealed` with the same associated data at time `now'` terminates with `Ok` of the payload.

Premises: `h_valid` (`CodecValid self`; used for (S), its third clause; for E11's (F), its second
clause; and for an `Rs2` seal mode, the key id's 1 to 255 bytes, its fourth clause); `h_rs1`, an
`Rs1` seal-mode id is an rs1 fallback (else a keyring codec would not accept its own `rs1`
token); `h_fits` (D), which also bounds the transcripts E11 rebuilds from the token (the same
bytes as the sealed transcripts), so E11's (T) needs no premise; `h_live`, the expiry has not
passed at `now'`. No premise on the token: its `.`-components are the version and Base64url
encodings.

Inherited exceptions: (H) HMAC `2^61`; (V) a transcript above `isize::MAX` bytes. Rust tests
(`seal_at` then `open_at`): `within_ttl_opens`, `past_ttl_is_expired` (the boundary of
`h_live`: opened after the expiry, it fails with `Expired`), `no_ttl_never_expires`,
`ttl_and_associated_data_combine` (patched lines 985–1038),
`rs2_roundtrips_with_associated_data_and_ttl` (lines 1139–1159); for the `h_rs1` path (a keyring
sealing `rs1`), `rolling_migration_is_bidirectionally_compatible` (lines 1180–1210, through
`seal`/`open`). The pending patch-02 boundary tests will add an rs1-ring `seal_at` → `open_at`
case. Intended `#print axioms`:
`[propext, Classical.choice, Quot.sound]`. Not tagged `@[step]`. -/
theorem seal_at_roundtrip (self : RequestStateCodec) (payload : Slice Std.U8)
    (options : SealOptions) (now now' : Std.I64)
    (h_valid : CodecValid self)
    (h_rs1 : ∀ keys kid rs1_fallbacks, self.keys = .Ring keys (.Rs1 kid) rs1_fallbacks →
      kid ∈ rs1_fallbacks.val)
    (h_fits : SealFits self payload.val.length options.associated_data.val.length)
    (h_live : ¬ Expired (sealExpiry options.ttl now.val) now'.val) :
    rmcp.model.request_state.RequestStateCodec.seal_at self payload options now ⦃
      (token : String) =>
      (∃ sealed : Str, (sealed : Slice Std.U8).val = ExtModel.utf8 token) ∧
      ∀ sealed : Str, (sealed : Slice Std.U8).val = ExtModel.utf8 token →
      rmcp.model.request_state.RequestStateCodec.open_at self sealed options.associated_data
        now' ⦃ (result : core.result.Result (alloc.vec.Vec Std.U8) RequestStateError) =>
        resultBytes result = .ok payload.val ⦄ ⦄ := by
  have hkey : CodecSealKeyKnown self := by
    rcases self with ⟨key | ⟨keys, sm, fb⟩⟩
    · trivial
    · exact h_valid.2.2.1
  have hfb : CodecFallbacksKnown self := by
    rcases self with ⟨key | ⟨keys, sm, fb⟩⟩
    · trivial
    · exact h_valid.2.1
  apply WP.spec_mono (rmcp.model.request_state.RequestStateCodec.seal_at_spec self payload options
    now hkey h_fits)
  intro token htok
  obtain ⟨hlen, hl1, hl2⟩ := Proofs.RequestState.Roundtrip.token_bounds_of_sealAt_eq_some self
    payload.val options.associated_data.val options.ttl now.val _ htok h_fits
  refine ⟨⟨Slice.from (ExtModel.utf8 token)
    (le_trans hlen Proofs.External.Utf8.maxStringBytes_le_usize_max), Slice.from_val _ _⟩,
    fun sealed hs => ?_⟩
  rw [← hs] at hl1 hl2 htok
  apply WP.spec_mono (rmcp.model.request_state.RequestStateCodec.open_at_spec self sealed
    options.associated_data now' hl1 hl2 (fun _ => hfb))
  intro r hr
  rw [hr]
  exact Proofs.RequestState.Roundtrip.openAt_eq_ok_of_sealAt_eq_some self payload.val
    options.associated_data.val options.ttl
    now now' _ h_valid h_rs1 h_live htok

end rmcp.model.request_state.RequestStateCodec
