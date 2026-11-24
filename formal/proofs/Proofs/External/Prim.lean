/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Rmcp.FunsExternal
import Proofs.External.Base64
import Proofs.External.String

/-!
# Specs of the `prim` externals (HMAC-SHA256, Base64url)

Spec theorems for the four `request_state_wire::prim` functions
(`crates/rmcp/src/model/request_state_wire.rs` lines 247–277 in the patched copy, patch 01 on
origin/main 7caec76; line numbers refer to it), modelled in
`formal/trusted/Rmcp/FunsExternal.lean` (sections HMAC and Base64). HMAC is stated in terms of
the opaque reference function `ExtModel.hmacSha256`, Base64 in terms of `ExtModel.b64` and
`ExtModel.b64Decode`, whose laws are in `Proofs.External.Base64`.
-/

open Aeneas Aeneas.Std Result

namespace model.request_state_wire.prim

open ExtModel Proofs.External.Utf8 Proofs.External.Base64

/-- **Spec theorem for `rmcp::model::request_state_wire::prim::hmac_sha256`**

Always succeeds (any key length) with the HMAC-SHA256 tag `hmacSha256 key msg`. -/
@[step]
theorem hmac_sha256_spec (key : Slice U8) (msg : Slice U8) :
    hmac_sha256 key msg ⦃ (result : Std.Array U8 32#usize) =>
      result = hmacSha256 key.val msg.val ⦄ := by
  simp [hmac_sha256]

/-- **Spec theorem for `rmcp::model::request_state_wire::prim::hmac_sha256_verify`**

Always succeeds; the result is `true` exactly when `tag` is, byte for byte, the HMAC-SHA256 tag
of `msg` under `key`. -/
@[step]
theorem hmac_sha256_verify_spec (key : Slice U8) (msg : Slice U8) (tag : Slice U8) :
    hmac_sha256_verify key msg tag ⦃ (result : Bool) =>
      result = decide (tag.val = (hmacSha256 key.val msg.val).val) ⦄ := by
  simp [hmac_sha256_verify]

/-- A tag whose length is not 32 is rejected (in particular a truncated tag). -/
theorem hmac_sha256_verify_eq_ok_false_of_length_ne (key : Slice U8) (msg : Slice U8)
    (tag : Slice U8) (h : tag.length ≠ 32) : hmac_sha256_verify key msg tag = ok false := by
  simp only [hmac_sha256_verify, ok.injEq, decide_eq_false_iff_not]
  intro heq
  apply h
  rw [Slice.length, heq, (hmacSha256 key.val msg.val).property]
  rfl

/-- The tag that `hmac_sha256` computes is accepted. -/
theorem hmac_sha256_verify_hmac_sha256 (key : Slice U8) (msg : Slice U8) (tag : Slice U8)
    (h : tag.val = (hmacSha256 key.val msg.val).val) :
    hmac_sha256_verify key msg tag = ok true := by
  simp [hmac_sha256_verify, h]

/-- **Spec theorem for `rmcp::model::request_state_wire::prim::b64_encode_into`**

Appends the unpadded Base64url symbols of `input` to `out`: the bytes of the result are those
of `out` followed by `b64 input` (`(4n + 2) / 3` symbols for `n` input bytes,
`Proofs.External.Base64.length_b64`). Precondition: the result fits in a Rust `String`
(`isize::MAX` bytes); otherwise the Rust code panics (`b64_encode_into_fail`). -/
@[step]
theorem b64_encode_into_spec (input : Slice U8) (out : String)
    (h : out.utf8ByteSize + (4 * input.length + 2) / 3 ≤ maxStringBytes) :
    b64_encode_into input out ⦃ (result : String) =>
      utf8 result = utf8 out ++ b64 input.val ⦄ := by
  have hb : utf8 (String.ofList ((b64 input.val).map (fun b => Char.ofNat b.val))) =
      b64 input.val := utf8_ofList_ascii _ (val_lt_128_of_mem_b64 _)
  have hlen : (out ++ String.ofList ((b64 input.val).map (fun b => Char.ofNat b.val))
      ).utf8ByteSize ≤ maxStringBytes := by
    rw [← length_utf8, utf8_append, hb, List.length_append, length_utf8, length_b64]; exact h
  simp only [b64_encode_into, growString, if_pos hlen, WP.spec_ok, utf8_append, hb]

/-- Beyond the `String` limit, `b64_encode_into` panics. -/
theorem b64_encode_into_fail (input : Slice U8) (out : String)
    (h : maxStringBytes < out.utf8ByteSize + (4 * input.length + 2) / 3) :
    b64_encode_into input out = fail Error.panic := by
  have hb : utf8 (String.ofList ((b64 input.val).map (fun b => Char.ofNat b.val))) =
      b64 input.val := utf8_ofList_ascii _ (val_lt_128_of_mem_b64 _)
  have hlen : ¬ (out ++ String.ofList ((b64 input.val).map (fun b => Char.ofNat b.val))
      ).utf8ByteSize ≤ maxStringBytes := by
    rw [← length_utf8, utf8_append, hb, List.length_append, length_utf8, length_b64]
    simp only [Slice.length] at h; omega
  simp only [b64_encode_into, growString, if_neg hlen]

/-- **Spec theorem for `rmcp::model::request_state_wire::prim::b64_decode`**

Always succeeds; the result is `b64Decode input`: `some` of the decoded bytes exactly when
`input` is the unpadded Base64url encoding of them (`b64Decode_eq_some_iff`), `none` otherwise. -/
@[step]
theorem b64_decode_spec (input : Slice U8) :
    b64_decode input ⦃ (result : Option (alloc.vec.Vec U8)) =>
      result.map (fun v => v.val) = b64Decode input.val ⦄ := by
  unfold b64_decode
  split <;> simp_all

end model.request_state_wire.prim
