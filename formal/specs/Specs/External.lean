/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Defs
import Proofs
import Mathlib.Tactic.Recall

/-!
# Spec file for the external models (S08–S09)

Statements about the Lean models of the externals in `trusted/Rmcp/{Types,Funs}External.lean`
(plan Section 4), restated with `recall` from their proofs in `Proofs/External/`, each followed
by the assumptions its proof depends on, checked by `#print axioms` under `#guard_msgs`. Each
depends on at most `propext`, `Classical.choice` and `Quot.sound`: the externals are definitions,
structures and four `opaque` constants, and add no assumption (`#print axioms` does not list
`opaque` constants such as `ExtModel.hmacSha256`, so changes to the models are caught only by
review of `trusted/`). Approved by the spec owner on 2026-11-23 (evidence/S08.md, S09.md); the
draft text was in `specs/Drafts/External.lean`, removed at incorporation.
-/

/-! ## `Proofs/External/Base64.lean` -/

open Aeneas Aeneas.Std

namespace Proofs.External.Base64

open ExtModel

/-- **Round trip:** decoding the encoding gives the input back. -/
recall b64Decode_b64 : ∀ x : List U8, b64Decode (b64 x) = some x

/-- info: 'Proofs.External.Base64.b64Decode_b64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Proofs.External.Base64.b64Decode_b64

/-- **Canonicity:** every input that decodes is the encoding of its result. With
`b64Decode_b64`, `b64Decode s = some y ↔ b64 y = s`: the decoder accepts exactly the canonical
unpadded encodings and rejects everything else (padding, foreign bytes, length `≡ 1 (mod 4)`,
non-zero trailing bits). -/
recall b64_of_b64Decode : ∀ (s y : List U8), b64Decode s = some y → b64 y = s

/-- info: 'Proofs.External.Base64.b64_of_b64Decode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Proofs.External.Base64.b64_of_b64Decode

/-- `b64Decode` accepts exactly the encodings, and returns what was encoded. -/
recall b64Decode_eq_some_iff (s y : List U8) : b64Decode s = some y ↔ b64 y = s

/-- info: 'Proofs.External.Base64.b64Decode_eq_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Proofs.External.Base64.b64Decode_eq_some_iff

/-- **Alphabet:** every byte of an encoding is a symbol of the URL-safe alphabet. -/
recall b64_alphabet : ∀ (x : List U8), ∀ c ∈ b64 x, (b64Val c).isSome

/-- info: 'Proofs.External.Base64.b64_alphabet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Proofs.External.Base64.b64_alphabet

/-- The symbols of the URL-safe alphabet are the bytes `A`–`Z`, `a`–`z`, `0`–`9`, `-`, `_`. -/
recall b64Val_isSome_iff (c : U8) :
    (b64Val c).isSome ↔ (65 ≤ c.val ∧ c.val ≤ 90) ∨ (97 ≤ c.val ∧ c.val ≤ 122) ∨
      (48 ≤ c.val ∧ c.val ≤ 57) ∨ c.val = 45 ∨ c.val = 95

/-- info: 'Proofs.External.Base64.b64Val_isSome_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Proofs.External.Base64.b64Val_isSome_iff

/-- In particular an encoding never contains the separator `.` (`Defs.Wire.dot`). -/
recall dot_not_mem_b64 (x : List U8) : Defs.Wire.dot ∉ b64 x

/-- info: 'Proofs.External.Base64.dot_not_mem_b64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Proofs.External.Base64.dot_not_mem_b64

/-- **Length:** the unpadded encoding of `n` bytes has `⌈4n/3⌉ = (4n + 2) / 3` symbols. -/
recall length_b64 : ∀ x : List U8, (b64 x).length = (4 * x.length + 2) / 3

/-- info: 'Proofs.External.Base64.length_b64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Proofs.External.Base64.length_b64

/-- The encoding is never longer than `Defs.Wire.b64Len` (`4 * ⌈n/3⌉`, the padded length that
`wire::b64_len` computes). -/
recall length_b64_le_b64Len (x : List U8) : (b64 x).length ≤ Defs.Wire.b64Len x.length

/-- info: 'Proofs.External.Base64.length_b64_le_b64Len' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Proofs.External.Base64.length_b64_le_b64Len

/-- For a length divisible by 3 the encoding has exactly `Defs.Wire.b64Len` symbols. -/
recall length_b64_of_dvd (x : List U8) (h : 3 ∣ x.length) :
    (b64 x).length = Defs.Wire.b64Len x.length

/-- info: 'Proofs.External.Base64.length_b64_of_dvd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Proofs.External.Base64.length_b64_of_dvd

/-- URL-safe symbols: `[0xfb, 0xef, 0xbe]` ↦ `----`, `[0xff, 0xff, 0xff]` ↦ `____`,
`[0xfb, 0xff]` ↦ `-_8`. -/
recall b64_url_safe_symbols :
    b64 [251#u8, 239#u8, 190#u8] = [45#u8, 45#u8, 45#u8, 45#u8] ∧
    b64 [255#u8, 255#u8, 255#u8] = [95#u8, 95#u8, 95#u8, 95#u8] ∧
    b64 [251#u8, 255#u8] = [45#u8, 95#u8, 56#u8]

/-- info: 'Proofs.External.Base64.b64_url_safe_symbols' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Proofs.External.Base64.b64_url_safe_symbols

/-- The standard-alphabet symbols `+` (43) and `/` (47) are rejected. -/
recall b64Decode_rejects_standard_symbols :
    b64Decode [43#u8, 43#u8, 43#u8, 43#u8] = none ∧
    b64Decode [47#u8, 47#u8, 47#u8, 47#u8] = none

/-- info: 'Proofs.External.Base64.b64Decode_rejects_standard_symbols' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Proofs.External.Base64.b64Decode_rejects_standard_symbols

/-- Padding is rejected: `Zg==`, `Zm8=`, `Zm9vYg==`. -/
recall b64Decode_rejects_padding :
    b64Decode [90#u8, 103#u8, 61#u8, 61#u8] = none ∧
    b64Decode [90#u8, 109#u8, 56#u8, 61#u8] = none ∧
    b64Decode [90#u8, 109#u8, 57#u8, 118#u8, 89#u8, 103#u8, 61#u8, 61#u8] = none

/-- info: 'Proofs.External.Base64.b64Decode_rejects_padding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Proofs.External.Base64.b64Decode_rejects_padding

/-- Non-canonical trailing bits are rejected: `Zh`, `Zm9`, `_x`; `_w` decodes to `[0xff]`. -/
recall b64Decode_trailing_bits :
    b64Decode [90#u8, 104#u8] = none ∧
    b64Decode [90#u8, 109#u8, 57#u8] = none ∧
    b64Decode [95#u8, 120#u8] = none ∧
    b64Decode [95#u8, 119#u8] = some [255#u8]

/-- info: 'Proofs.External.Base64.b64Decode_trailing_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Proofs.External.Base64.b64Decode_trailing_bits

/-- Impossible lengths and foreign bytes are rejected: `Z`, `Zm9vY`, `!!!!`, `Zm 9v`, `Zm9v
`. -/
recall b64Decode_rejects_malformed :
    b64Decode [90#u8] = none ∧
    b64Decode [90#u8, 109#u8, 57#u8, 118#u8, 89#u8] = none ∧
    b64Decode [33#u8, 33#u8, 33#u8, 33#u8] = none ∧
    b64Decode [90#u8, 109#u8, 32#u8, 57#u8, 118#u8] = none ∧
    b64Decode [90#u8, 109#u8, 57#u8, 118#u8, 10#u8] = none

/-- info: 'Proofs.External.Base64.b64Decode_rejects_malformed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Proofs.External.Base64.b64Decode_rejects_malformed

end Proofs.External.Base64

/-! ## `Proofs/External/String.lean` -/

open Aeneas Aeneas.Std

namespace Proofs.External.Utf8

open ExtModel Proofs.External.Base64

/-- `utf8 s` has `s.utf8ByteSize` bytes. -/
recall length_utf8 (s : String) : (utf8 s).length = s.utf8ByteSize

/-- info: 'Proofs.External.Utf8.length_utf8' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Proofs.External.Utf8.length_utf8

/-- `utf8` is additive. -/
recall utf8_append (s t : String) : utf8 (s ++ t) = utf8 s ++ utf8 t

/-- info: 'Proofs.External.Utf8.utf8_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Proofs.External.Utf8.utf8_append

/-- `strOfBytes?` inverts `utf8`. -/
recall strOfBytes?_utf8 (s : String) : strOfBytes? (utf8 s) = some s

/-- info: 'Proofs.External.Utf8.strOfBytes?_utf8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Proofs.External.Utf8.strOfBytes?_utf8

/-- `strOfBytes? l = some s` exactly when `l` is the UTF-8 encoding of `s`. -/
recall strOfBytes?_eq_some_iff (l : List U8) (s : String) :
    strOfBytes? l = some s ↔ l = utf8 s

/-- info: 'Proofs.External.Utf8.strOfBytes?_eq_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Proofs.External.Utf8.strOfBytes?_eq_some_iff

/-- `strOfBytes? l = none` exactly when `l` is the encoding of no string (not UTF-8). -/
recall strOfBytes?_eq_none_iff (l : List U8) : strOfBytes? l = none ↔ ∀ s, l ≠ utf8 s

/-- info: 'Proofs.External.Utf8.strOfBytes?_eq_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Proofs.External.Utf8.strOfBytes?_eq_none_iff

/-- Two strings with the same bytes are equal. -/
recall utf8_inj {s t : String} (h : utf8 s = utf8 t) : s = t

/-- info: 'Proofs.External.Utf8.utf8_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Proofs.External.Utf8.utf8_inj

/-- ASCII bytes, as characters, encode to themselves. -/
recall utf8_ofList_ascii (l : List U8) (h : ∀ b ∈ l, b.val < 128) :
    utf8 (String.ofList (l.map (fun b => Char.ofNat b.val))) = l

/-- info: 'Proofs.External.Utf8.utf8_ofList_ascii' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Proofs.External.Utf8.utf8_ofList_ascii

/-- Appending an ASCII character appends its one byte. -/
recall utf8_push_ascii (s : String) (c : Char) (h : c.toNat < 128) :
    utf8 (s.push c) = utf8 s ++ [byte c.toNat]

/-- info: 'Proofs.External.Utf8.utf8_push_ascii' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Proofs.External.Utf8.utf8_push_ascii

/-- An ASCII character is one byte. -/
recall utf8_ofList_singleton_ascii (ch : Char) (h : ch.toNat < 128) :
    utf8 (String.ofList [ch]) = [byte ch.toNat]

/-- info: 'Proofs.External.Utf8.utf8_ofList_singleton_ascii' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Proofs.External.Utf8.utf8_ofList_singleton_ascii

/-- The bytes of the Aeneas `toStr` of a literal are its `utf8` bytes. -/
recall toStr_val (s : String) (h : s.toByteArray.size ≤ U32.max) :
    (toStr s h).val = utf8 s

/-- info: 'Proofs.External.Utf8.toStr_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Proofs.External.Utf8.toStr_val

/-- Every symbol of an encoding is ASCII. -/
recall b64_ascii (x : List U8) : ∀ b ∈ b64 x, b.val < 128

/-- info: 'Proofs.External.Utf8.b64_ascii' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Proofs.External.Utf8.b64_ascii

/-- A Rust `String` length (at most `isize::MAX`) fits in a `usize`, so the bytes of any
`String` the models produce form a `Slice`. -/
recall maxStringBytes_le_usize_max : maxStringBytes ≤ Usize.max

/-- info: 'Proofs.External.Utf8.maxStringBytes_le_usize_max' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Proofs.External.Utf8.maxStringBytes_le_usize_max

end Proofs.External.Utf8

/-! ## `Proofs/External/Prim.lean` -/

open Aeneas Aeneas.Std Result

namespace model.request_state_wire.prim

open ExtModel Proofs.External.Utf8 Proofs.External.Base64

/-- **Spec theorem for `rmcp::model::request_state_wire::prim::hmac_sha256`**

Always succeeds (any key length) with the HMAC-SHA256 tag `hmacSha256 key msg`. -/
recall hmac_sha256_spec (key : Slice U8) (msg : Slice U8) :
    hmac_sha256 key msg ⦃ (result : Std.Array U8 32#usize) =>
      result = hmacSha256 key.val msg.val ⦄

/-- info: 'model.request_state_wire.prim.hmac_sha256_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms model.request_state_wire.prim.hmac_sha256_spec

/-- **Spec theorem for `rmcp::model::request_state_wire::prim::hmac_sha256_verify`**

Always succeeds; the result is `true` exactly when `tag` is, byte for byte, the HMAC-SHA256 tag
of `msg` under `key`. -/
recall hmac_sha256_verify_spec (key : Slice U8) (msg : Slice U8) (tag : Slice U8) :
    hmac_sha256_verify key msg tag ⦃ (result : Bool) =>
      result = decide (tag.val = (hmacSha256 key.val msg.val).val) ⦄

/-- info: 'model.request_state_wire.prim.hmac_sha256_verify_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms model.request_state_wire.prim.hmac_sha256_verify_spec

/-- A tag whose length is not 32 is rejected (in particular a truncated tag). -/
recall hmac_sha256_verify_wrong_length (key : Slice U8) (msg : Slice U8) (tag : Slice U8)
    (h : tag.length ≠ 32) : hmac_sha256_verify key msg tag = ok false

/--
info: 'model.request_state_wire.prim.hmac_sha256_verify_wrong_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms model.request_state_wire.prim.hmac_sha256_verify_wrong_length

/-- The tag that `hmac_sha256` computes is accepted. -/
recall hmac_sha256_verify_hmac_sha256 (key : Slice U8) (msg : Slice U8) (tag : Slice U8)
    (h : tag.val = (hmacSha256 key.val msg.val).val) :
    hmac_sha256_verify key msg tag = ok true

/--
info: 'model.request_state_wire.prim.hmac_sha256_verify_hmac_sha256' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms model.request_state_wire.prim.hmac_sha256_verify_hmac_sha256

/-- **Spec theorem for `rmcp::model::request_state_wire::prim::b64_encode_into`**

Appends the unpadded Base64url symbols of `input` to `out`: the bytes of the result are those
of `out` followed by `b64 input` (`(4n + 2) / 3` symbols for `n` input bytes,
`Proofs.External.Base64.length_b64`). Precondition: the result fits in a Rust `String`
(`isize::MAX` bytes); otherwise the Rust code panics (`b64_encode_into_fail`). -/
recall b64_encode_into_spec (input : Slice U8) (out : String)
    (h : out.utf8ByteSize + (4 * input.length + 2) / 3 ≤ maxStringBytes) :
    b64_encode_into input out ⦃ (result : String) =>
      utf8 result = utf8 out ++ b64 input.val ⦄

/-- info: 'model.request_state_wire.prim.b64_encode_into_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms model.request_state_wire.prim.b64_encode_into_spec

/-- Beyond the `String` limit, `b64_encode_into` panics. -/
recall b64_encode_into_fail (input : Slice U8) (out : String)
    (h : maxStringBytes < out.utf8ByteSize + (4 * input.length + 2) / 3) :
    b64_encode_into input out = fail Error.panic

/-- info: 'model.request_state_wire.prim.b64_encode_into_fail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms model.request_state_wire.prim.b64_encode_into_fail

/-- **Spec theorem for `rmcp::model::request_state_wire::prim::b64_decode`**

Always succeeds; the result is `b64Decode input`: `some` of the decoded bytes exactly when
`input` is the unpadded Base64url encoding of them (`b64Decode_eq_some_iff`), `none` otherwise. -/
recall b64_decode_spec (input : Slice U8) :
    b64_decode input ⦃ (result : Option (alloc.vec.Vec U8)) =>
      result.map (fun v => v.val) = b64Decode input.val ⦄

/-- info: 'model.request_state_wire.prim.b64_decode_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms model.request_state_wire.prim.b64_decode_spec

end model.request_state_wire.prim

/-! ## `Proofs/External/Std.lean` -/

open Aeneas Aeneas.Std Result

open ExtModel Proofs.External.Utf8 Proofs.External.Base64

/-- **Spec theorem for `core::borrow::{impl Borrow<T> for T}::borrow`**: the identity. -/
recall core.borrow.Borrow.Blanket.borrow_spec {T : Type} (self : T) :
    core.borrow.Borrow.Blanket.borrow self ⦃ (result : T) => result = self ⦄

/-- info: 'core.borrow.Borrow.Blanket.borrow_spec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms core.borrow.Borrow.Blanket.borrow_spec

/-- **Spec theorem for `core::option::Option::ok_or`**: `Some v ↦ Ok v`, `None ↦ Err err`. -/
recall core.option.Option.ok_or_spec {T : Type} {E : Type} (self : Option T) (err : E) :
    core.option.Option.ok_or self err ⦃ (result : core.result.Result T E) =>
      result = match self with
        | some v => core.result.Result.Ok v
        | none => core.result.Result.Err err ⦄

/-- info: 'core.option.Option.ok_or_spec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms core.option.Option.ok_or_spec

/-- **Spec theorem for `<Option<T> as Default>::default`**: `None`. -/
recall core.option.Option.Insts.CoreDefaultDefault.default_spec (T : Type) :
    core.option.Option.Insts.CoreDefaultDefault.default T ⦃ (result : Option T) =>
      result = none ⦄

/-- info: 'core.option.Option.Insts.CoreDefaultDefault.default_spec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms core.option.Option.Insts.CoreDefaultDefault.default_spec

/-- **Spec theorem for `core::result::Result::is_err`**: `true` exactly for `Err`. -/
recall core.result.Result.is_err_spec {T : Type} {E : Type} (self : core.result.Result T E) :
    core.result.Result.is_err self ⦃ (result : Bool) =>
      result = match self with
        | core.result.Result.Ok _ => false
        | core.result.Result.Err _ => true ⦄

/-- info: 'core.result.Result.is_err_spec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms core.result.Result.is_err_spec

/-- `core::result::Result::map_err` on `Ok`: unchanged, the closure is not called. -/
recall core.result.Result.map_err_Ok {T E F O : Type}
    (inst : core.ops.function.FnOnce O E F) (t : T) (op : O) :
    core.result.Result.map_err inst (core.result.Result.Ok t : core.result.Result T E) op =
      ok (core.result.Result.Ok t)

/-- info: 'core.result.Result.map_err_Ok' does not depend on any axioms -/
#guard_msgs in
#print axioms core.result.Result.map_err_Ok

/-- `core::result::Result::map_err` on `Err e`: `Err (op e)`; the closure's failure
propagates. -/
recall core.result.Result.map_err_Err {T E F O : Type}
    (inst : core.ops.function.FnOnce O E F) (e : E) (op : O) :
    core.result.Result.map_err inst (core.result.Result.Err e : core.result.Result T E) op =
      (do let f ← inst.call_once op e; ok (core.result.Result.Err f))

/-- info: 'core.result.Result.map_err_Err' does not depend on any axioms -/
#guard_msgs in
#print axioms core.result.Result.map_err_Err

/-- **Spec theorem for `<&[T] as Default>::default`**: the empty slice. -/
recall Shared0Slice.Insts.CoreDefaultDefault.default_spec (T : Type) :
    Shared0Slice.Insts.CoreDefaultDefault.default T ⦃ (result : Slice T) =>
      result.val = [] ⦄

/-- info: 'Shared0Slice.Insts.CoreDefaultDefault.default_spec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shared0Slice.Insts.CoreDefaultDefault.default_spec

/-- **Spec theorem for `core::str::str::len`**: the number of bytes; for every `Str`. -/
recall core.str.Str.len_spec (self : Str) :
    core.str.Str.len self ⦃ (result : Usize) => result.val = self.val.length ⦄

/-- info: 'core.str.Str.len_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms core.str.Str.len_spec

/-- **Spec theorem for `core::str::str::as_bytes`**: the same bytes; for every `Str`. -/
recall core.str.Str.as_bytes_spec (self : Str) :
    core.str.Str.as_bytes self ⦃ (result : Slice U8) => result.val = self.val ⦄

/-- info: 'core.str.Str.as_bytes_spec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms core.str.Str.as_bytes_spec

/-- **Spec theorem for `String::with_capacity`**: the empty string, if `capacity ≤ isize::MAX`
(else `with_capacity_fail`). -/
recall alloc.string.String.with_capacity_spec (capacity : Usize)
    (h : capacity.val ≤ maxStringBytes) :
    alloc.string.String.with_capacity capacity ⦃ (result : String) => result = "" ⦄

/-- info: 'alloc.string.String.with_capacity_spec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms alloc.string.String.with_capacity_spec

/-- `String::with_capacity` panics ("capacity overflow") above `isize::MAX`. -/
recall alloc.string.String.with_capacity_fail (capacity : Usize)
    (h : maxStringBytes < capacity.val) :
    alloc.string.String.with_capacity capacity = fail Error.panic

/-- info: 'alloc.string.String.with_capacity_fail' depends on axioms: [propext] -/
#guard_msgs in
#print axioms alloc.string.String.with_capacity_fail

/-- **Spec theorem for `String::push_str`**: for a UTF-8 argument (`string` is the bytes of `t`,
as every Rust `&str` is) whose result fits in a `String`, appends `t`; the result's bytes are
the old bytes followed by `string`. -/
recall alloc.string.String.push_str_spec (self : String) (string : Str) (t : String)
    (ht : string.val = utf8 t) (h : self.utf8ByteSize + string.val.length ≤ maxStringBytes) :
    alloc.string.String.push_str self string ⦃ (result : String) =>
      result = self ++ t ∧ utf8 result = utf8 self ++ string.val ⦄

/-- info: 'alloc.string.String.push_str_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms alloc.string.String.push_str_spec

/-- `String::push_str` with a result beyond `isize::MAX` bytes panics. -/
recall alloc.string.String.push_str_fail (self : String) (string : Str) (t : String)
    (ht : string.val = utf8 t) (h : maxStringBytes < self.utf8ByteSize + string.val.length) :
    alloc.string.String.push_str self string = fail Error.panic

/-- info: 'alloc.string.String.push_str_fail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms alloc.string.String.push_str_fail

/-- `String::push_str` with bytes that are not UTF-8 (no Rust `&str`) is outside the Rust
domain: `fail undef`. -/
recall alloc.string.String.push_str_not_utf8 (self : String) (string : Str)
    (h : ∀ t, string.val ≠ utf8 t) :
    alloc.string.String.push_str self string = fail Error.undef

/-- info: 'alloc.string.String.push_str_not_utf8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms alloc.string.String.push_str_not_utf8

/-- **Spec theorem for `String::push`**: appends the character if the result fits in a
`String`; the result's bytes are the old bytes followed by the character's encoding. -/
recall alloc.string.String.push_spec (self : String) (ch : Char)
    (h : self.utf8ByteSize + ch.utf8Size ≤ maxStringBytes) :
    alloc.string.String.push self ch ⦃ (result : String) =>
      result = self.push ch ∧ utf8 result = utf8 self ++ utf8 (String.ofList [ch]) ⦄

/-- info: 'alloc.string.String.push_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms alloc.string.String.push_spec

/-- `String::push` with a result beyond `isize::MAX` bytes panics. -/
recall alloc.string.String.push_fail (self : String) (ch : Char)
    (h : maxStringBytes < self.utf8ByteSize + ch.utf8Size) :
    alloc.string.String.push self ch = fail Error.panic

/-- info: 'alloc.string.String.push_fail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms alloc.string.String.push_fail

/-- **Spec theorem for `String::as_bytes`**: the UTF-8 bytes. The precondition holds for every
Rust `String` (at most `isize::MAX` bytes); see `as_bytes_fail`. -/
recall alloc.string.String.as_bytes_spec (self : String) (h : self.utf8ByteSize ≤ Usize.max) :
    alloc.string.String.as_bytes self ⦃ (result : Slice U8) => result.val = utf8 self ⦄

/-- info: 'alloc.string.String.as_bytes_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms alloc.string.String.as_bytes_spec

/-- `String::as_bytes` on a Lean `String` longer than `Usize.max` bytes (no Rust `String`). -/
recall alloc.string.String.as_bytes_fail (self : String) (h : Usize.max < self.utf8ByteSize) :
    alloc.string.String.as_bytes self = fail Error.maximumSizeExceeded

/-- info: 'alloc.string.String.as_bytes_fail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms alloc.string.String.as_bytes_fail

/-- **Spec theorem for `String::from_utf8`**: `Ok s` when the bytes are the encoding of `s`;
otherwise `Err` carrying the bytes. -/
recall alloc.string.String.from_utf8_spec (vec : alloc.vec.Vec U8) :
    alloc.string.String.from_utf8 vec ⦃ (result : core.result.Result String
        alloc.string.FromUtf8Error) =>
      match result with
      | core.result.Result.Ok s => vec.val = utf8 s
      | core.result.Result.Err e => (∀ s, vec.val ≠ utf8 s) ∧ e.bytes = vec ⦄

/-- info: 'alloc.string.String.from_utf8_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms alloc.string.String.from_utf8_spec

/-- **Spec theorem for `<String as PartialEq>::eq`**: equality. -/
recall alloc.string.String.Insts.CoreCmpPartialEqString.eq_spec (self : String)
    (other : String) :
    alloc.string.String.Insts.CoreCmpPartialEqString.eq self other ⦃ (result : Bool) =>
      result = decide (self = other) ⦄

/-- info: 'alloc.string.String.Insts.CoreCmpPartialEqString.eq_spec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms alloc.string.String.Insts.CoreCmpPartialEqString.eq_spec

/-- **Spec theorem for `<String as Eq>::assert_fields_are_eq`**: succeeds. -/
recall alloc.string.String.Insts.CoreCmpEq.assert_fields_are_eq_spec (self : String) :
    alloc.string.String.Insts.CoreCmpEq.assert_fields_are_eq self ⦃ (_ : Unit) => True ⦄

/-- info: 'alloc.string.String.Insts.CoreCmpEq.assert_fields_are_eq_spec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms alloc.string.String.Insts.CoreCmpEq.assert_fields_are_eq_spec

/-- **Spec theorem for `<String as Clone>::clone`**: the same string. -/
recall alloc.string.String.Insts.CoreCloneClone.clone_spec (self : String) :
    alloc.string.String.Insts.CoreCloneClone.clone self ⦃ (result : String) =>
      result = self ⦄

/-- info: 'alloc.string.String.Insts.CoreCloneClone.clone_spec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms alloc.string.String.Insts.CoreCloneClone.clone_spec

/-- `<String as Hash>::hash` writes the bytes and then `0xff` (for a Rust-sized `String`). -/
recall alloc.string.String.Insts.CoreHashHash.hash_eq {H : Type}
    (inst : core.hash.Hasher H) (self : String) (state : H)
    (h : self.utf8ByteSize ≤ Usize.max) :
    alloc.string.String.Insts.CoreHashHash.hash inst self state =
      (do
        let state ← inst.write state ⟨utf8 self, by rw [length_utf8]; exact h⟩
        inst.write state ⟨[byte 255], by scalar_tac⟩)

/-- info: 'alloc.string.String.Insts.CoreHashHash.hash_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms alloc.string.String.Insts.CoreHashHash.hash_eq

/-- **Spec theorem for `Vec::is_empty`**: `true` exactly for the empty vector. -/
recall alloc.vec.Vec.is_empty_spec {T : Type} (A : Type) (self : alloc.vec.Vec T) :
    alloc.vec.Vec.is_empty A self ⦃ (result : Bool) => result = decide (self.val = []) ⦄

/-- info: 'alloc.vec.Vec.is_empty_spec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms alloc.vec.Vec.is_empty_spec

/-- **Spec theorem for `<RandomState as Clone>::clone`**: the same value. -/
recall std.hash.random.RandomState.Insts.CoreCloneClone.clone_spec
    (self : std.hash.random.RandomState) :
    std.hash.random.RandomState.Insts.CoreCloneClone.clone self ⦃
      (result : std.hash.random.RandomState) => result = self ⦄

/-- info: 'std.hash.random.RandomState.Insts.CoreCloneClone.clone_spec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms std.hash.random.RandomState.Insts.CoreCloneClone.clone_spec

/-- **Spec theorem for `<RandomState as BuildHasher>::build_hasher`**: the map's keys, no
bytes written. -/
recall std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher.build_hasher_spec
    (self : std.hash.random.RandomState) :
    std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher.build_hasher self ⦃
      (result : std.hash.random.DefaultHasher) =>
        result = { k0 := self.k0, k1 := self.k1, written := [] } ⦄

/-- info: 'std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher.build_hasher_spec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher.build_hasher_spec

/-- **Spec theorem for `<DefaultHasher as Hasher>::write`**: appends the bytes. -/
recall std.hash.random.DefaultHasher.Insts.CoreHashHasher.write_spec
    (self : std.hash.random.DefaultHasher) (msg : Slice U8) :
    std.hash.random.DefaultHasher.Insts.CoreHashHasher.write self msg ⦃
      (result : std.hash.random.DefaultHasher) =>
        result = { self with written := self.written ++ msg.val } ⦄

/-- info: 'std.hash.random.DefaultHasher.Insts.CoreHashHasher.write_spec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms std.hash.random.DefaultHasher.Insts.CoreHashHasher.write_spec

/-- **Spec theorem for `<DefaultHasher as Hasher>::finish`**: SipHash-1-3 of keys and bytes. -/
recall std.hash.random.DefaultHasher.Insts.CoreHashHasher.finish_spec
    (self : std.hash.random.DefaultHasher) :
    std.hash.random.DefaultHasher.Insts.CoreHashHasher.finish self ⦃ (result : U64) =>
      result = sipHash13 self.k0 self.k1 self.written ⦄

/--
info: 'std.hash.random.DefaultHasher.Insts.CoreHashHasher.finish_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms std.hash.random.DefaultHasher.Insts.CoreHashHasher.finish_spec

/-- `HashMap::get` is the lookup `ExtModel.HashMap.find` over the entries, whatever the
hashing instances. -/
recall std.collections.hash.map.HashMap.get_eq
    {K V S A Q Clause2_Hasher : Type} (eqK : core.cmp.Eq K) (hashK : core.hash.Hash K)
    (bh : rmcp.core.hash.BuildHasher S Clause2_Hasher) (borrow : rmcp.core.borrow.Borrow K Q)
    (hashQ : core.hash.Hash Q) (eqQ : core.cmp.Eq Q)
    (self : std.collections.hash.map.HashMap K V S A) (k : Q) :
    std.collections.hash.map.HashMap.get eqK hashK bh borrow hashQ eqQ self k =
      ExtModel.HashMap.find borrow eqQ k self.entries

/-- info: 'std.collections.hash.map.HashMap.get_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms std.collections.hash.map.HashMap.get_eq

/-- **Spec theorem for `HashMap::get`** at the instance of the translation (`K = Q = String`,
`S = RandomState`): the value of the first entry whose key is `k`. With pairwise distinct keys
(the Rust invariant) this is the value stored under `k`
(`Proofs.External.HashMap.find?_key_of_mem`), and `None` when `k` is not a key
(`Proofs.External.HashMap.find?_key_of_not_mem`); without distinct keys, a value is found exactly
when `k` is a key (`Proofs.External.HashMap.find?_key_isSome_iff`). -/
recall std.collections.hash.map.HashMap.get_string_spec {V A : Type}
    (self : std.collections.hash.map.HashMap String V std.hash.random.RandomState A)
    (k : String) :
    std.collections.hash.map.HashMap.get rmcp.alloc.string.String.Insts.CoreCmpEq
      rmcp.alloc.string.String.Insts.CoreHashHash
      rmcp.std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher
      (rmcp.core.borrow.Borrow.Blanket String) rmcp.alloc.string.String.Insts.CoreHashHash
      rmcp.alloc.string.String.Insts.CoreCmpEq self k ⦃ (result : Option V) =>
        result = (self.entries.find? (fun e => decide (e.1 = k))).map Prod.snd ⦄

/-- info: 'std.collections.hash.map.HashMap.get_string_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms std.collections.hash.map.HashMap.get_string_spec

namespace Proofs.External.HashMap

/-- With distinct keys, the first entry with key `k` is the one stored under `k`. -/
recall find?_key_of_mem {V : Type} (entries : List (String × V)) (k : String) (v : V)
    (hnd : (entries.map Prod.fst).Nodup) (hm : (k, v) ∈ entries) :
    (entries.find? (fun e => decide (e.1 = k))).map Prod.snd = some v

/-- info: 'Proofs.External.HashMap.find?_key_of_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Proofs.External.HashMap.find?_key_of_mem

/-- No entry has key `k`: the lookup gives `none`. -/
recall find?_key_of_not_mem {V : Type} (entries : List (String × V)) (k : String)
    (h : k ∉ entries.map Prod.fst) :
    (entries.find? (fun e => decide (e.1 = k))).map Prod.snd = none

/-- info: 'Proofs.External.HashMap.find?_key_of_not_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Proofs.External.HashMap.find?_key_of_not_mem

/-- **Found, without distinct keys:** the lookup returns a value exactly when `k` is a key; no
`Nodup` premise (with duplicate keys it is the value of the first entry). -/
recall find?_key_isSome_iff {V : Type} (entries : List (String × V)) (k : String) :
    ((entries.find? (fun e => decide (e.1 = k))).map Prod.snd).isSome ↔
      k ∈ entries.map Prod.fst

/-- info: 'Proofs.External.HashMap.find?_key_isSome_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Proofs.External.HashMap.find?_key_isSome_iff

end Proofs.External.HashMap

/-- `HashMap::clone`: clones the hash builder, the allocator and every key and value. -/
recall std.collections.hash.map.HashMap.Insts.CoreCloneClone.clone_eq
    {K V S A : Type} (cK : core.clone.Clone K) (cV : core.clone.Clone V)
    (cS : core.clone.Clone S) (cA : core.clone.Clone A)
    (self : std.collections.hash.map.HashMap K V S A) :
    std.collections.hash.map.HashMap.Insts.CoreCloneClone.clone cK cV cS cA self =
      (do
        let hash_builder ← cS.clone self.hash_builder
        let alloc ← cA.clone self.alloc
        let entries ← self.entries.mapM (fun (e : K × V) => do
          let k ← cK.clone e.1
          let v ← cV.clone e.2
          ok (k, v))
        ok { hash_builder, alloc, entries })

/-- info: 'std.collections.hash.map.HashMap.Insts.CoreCloneClone.clone_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms std.collections.hash.map.HashMap.Insts.CoreCloneClone.clone_eq

/-- **Spec theorem for `Zeroizing::new`**: wraps the value. -/
recall zeroize.Zeroizing.new_spec {Z : Type} (inst : rmcp.zeroize.Zeroize Z) (value : Z) :
    zeroize.Zeroizing.new inst value ⦃ (result : zeroize.Zeroizing Z) =>
      result.inner = value ⦄

/-- info: 'zeroize.Zeroizing.new_spec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms zeroize.Zeroizing.new_spec

/-- **Spec theorem for `<Zeroizing<Z> as Deref>::deref`**: the wrapped value. -/
recall zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref_spec {Z : Type}
    (inst : rmcp.zeroize.Zeroize Z) (self : zeroize.Zeroizing Z) :
    zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref inst self ⦃ (result : Z) =>
      result = self.inner ⦄

/-- info: 'zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref_spec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref_spec

/-- `<Zeroizing<Z> as Clone>::clone` wraps a clone of the value. -/
recall zeroize.Zeroizing.Insts.CoreCloneClone.clone_eq {Z : Type} (inst : rmcp.zeroize.Zeroize Z)
    (cZ : core.clone.Clone Z) (self : zeroize.Zeroizing Z) :
    zeroize.Zeroizing.Insts.CoreCloneClone.clone inst cZ self =
      (do let v ← cZ.clone self.inner; ok { inner := v })

/-- info: 'zeroize.Zeroizing.Insts.CoreCloneClone.clone_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms zeroize.Zeroizing.Insts.CoreCloneClone.clone_eq

/-- `<Z as Zeroize>::zeroize` for `Z: DefaultIsZeroes` is `Z::default()`. -/
recall zeroize.Zeroize.Blanket.zeroize_eq {Z : Type} (inst : rmcp.zeroize.DefaultIsZeroes Z)
    (self : Z) :
    zeroize.Zeroize.Blanket.zeroize inst self = inst.coredefaultDefaultInst.default

/-- info: 'zeroize.Zeroize.Blanket.zeroize_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms zeroize.Zeroize.Blanket.zeroize_eq

/-- `<Vec<Z> as Zeroize>::zeroize` zeroizes each element and returns the empty vector. -/
recall alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize_eq {Z : Type} (inst : rmcp.zeroize.Zeroize Z)
    (self : alloc.vec.Vec Z) :
    alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize inst self =
      (do let _ ← self.val.mapM inst.zeroize; ok (alloc.vec.Vec.new Z))

/-- info: 'alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize_eq
