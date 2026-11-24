/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Rmcp.Funs
import Defs.Wire
import Defs.CodecState
import Proofs.External.Base64
import Proofs.External.String
import Proofs.Model.RequestStateWire.Common
import Proofs.Model.RequestState.SealRs1
import Proofs.Model.RequestState.SealRs2
import Proofs.Model.RequestState.OpenRs1At
import Proofs.Model.RequestState.OpenRs2At
import Proofs.Model.RequestState.OpenAt

/-!
# Round trips of the request-state codec (S15)

Plan Section 3, "Round-trip", and Section 5, "Theorem names": sealing a body with `seal_rs1`
(E07) or `seal_rs2` (E08) and opening the token with `open_rs1_at` (E09), `open_rs2_at` (E10) or
`open_at` (E11) returns exactly `body[8..]`. The four composition theorems `rs1_roundtrip`,
`rs2_roundtrip`, `open_at_roundtrip_rs1` and `open_at_roundtrip_rs2` compose the spec theorems
of E07–E11; no target function body is unfolded. The seal wrappers `seal_at`, `seal_with` and
`seal` are excluded (plan Section 2.3), so none appears.

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
    simp only [maxEncodedKidLen, maxKidLen] at *
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
  simp only [List.Vector.length_val, UScalar.ofNatCore_val_eq]

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
  refine ⟨⟨⟨ExtModel.utf8 token, ?_⟩, rfl⟩, fun sealed hs => ?_⟩
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
  refine ⟨⟨⟨ExtModel.utf8 token, ?_⟩, rfl⟩, fun sealed hs => ?_⟩
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
  refine ⟨⟨⟨ExtModel.utf8 token, ?_⟩, rfl⟩, fun sealed hs => ?_⟩
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
  refine ⟨⟨⟨ExtModel.utf8 token, ?_⟩, rfl⟩, fun sealed hs => ?_⟩
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
