/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Defs
public import Defs.Wire
public import Proofs.External.Base64
public import Proofs.External.String
public import Proofs.External.Prim
public import Proofs.External.Std
public import Proofs.External.Option
public import Proofs.External.IntParse
public import Proofs.External.Net
public import Proofs.External.Auth

@[expose] public section

/-!
# Internal spec file for the external models (S08–S09, S26–S27)

These are laws of the trusted Lean models of the external functions the translated code calls
(`std`/`core`/`alloc`, `core::net`, integer parsing, the HMAC and Base64 primitives of patch 01's
`prim` module), not guarantees about rmcp functions; they are kept out of `formal/specs/`, which
holds only the public API (human decision 2026-11-24). They state what the models in
`formal/trusted/` compute, so that a reviewer can compare them with the Rust documentation; the
spec proofs use them. Index of all guarantees: `formal/specs/README.md`.

| Section (count) | What the laws say |
|---|---|
| Base64 (14) | unpadded Base64url: round trip, canonical decoding, alphabet, lengths |
| String (12) | `utf8` bytes: length, append, injective, inverse `strOfBytes?`, ASCII |
| Prim (7) | `prim`: HMAC = `hmacSha256`, verify = tag equality, Base64 calls |
| Std (39) | `Option`, `Result`, `str`, `String`, `Vec`, hashing, `HashMap`, `zeroize` |
| String, Phase 2 (6) | `str` equality, `String` deref, `Arc` deref and equality |
| Option, Phase 2 (6) | `Option::or_else`, `Option` equality, `Result::ok` |
| Std, Phase 2 (10) | `slice::first`, slice-array equality, `strip_suffix`, `RangeInclusive` |
| IntParse, Phase 2 (7) | `i64::from_str`: errors, round trips, equal to `Defs.parseI64` |
| Net, Phase 2 (15) | `Ipv4Addr`/`Ipv6Addr` octets, segments and range predicates |
| Auth, A04–A10 (1) | `str::trim` on UTF-8 bytes is the char-level trim |

Premises: many laws have none; others name the parts of a value (the octets of an address), require
that a Lean `String` or `Vec` is no larger than a Rust one can be (`Usize.max` or `isize::MAX`
bytes), or that an instance decides equality; the `_fail` laws state where the model fails (where
Rust panics, or for Lean values that no Rust value has). Counts are of the theorems in each section
below (117 in all).

Statements about the Lean models of the externals in `trusted/Rmcp/{Types,Funs}External.lean`
(plan Section 4), restated as theorems `Theorems.External.<original name>` proved by the laws in
`Proofs/External/`, each followed by the assumptions its proof depends on, checked by
`#print axioms` under `#guard_msgs`. Each depends on at most `propext`, `Classical.choice` and
`Quot.sound`: the externals are definitions, structures and five `opaque` constants
(`ExtModel.hmacSha256`, `ExtModel.sipHash13`, `ExtModel.nowMs` and the types
`ExtModel.SerdeJsonErrorImpl`, `ExtModel.SerdeJsonValue`), and add no assumption (`#print axioms`
does not list `opaque` constants, so changes to the models are caught only by review of
`trusted/`). Approved by the spec owner on 2026-11-23 (S08/S09 evidence, git history at 223ff12);
the statements entered git already incorporated, in af41799.

Phase 2 (plan steps S26/S27, plan Section 18): the laws of the models of the Phase 2 externals
(`trusted/Rmcp/{Types,Funs}External.lean`, sections "Phase 2"), restated in the last part of
this file as `Theorems.External.<original name>` and proved at stage 6 in
`Proofs/External/{String,Option,Std,IntParse,Net}.lean`. Signed off by the spec owner on
2026-11-23; the statements are the ones restated in this
project file. Each depends on at most `propext`, `Classical.choice` and `Quot.sound`. The S27
deferred law `I64.Insts.CoreStrTraitsFromStrParseIntError.from_str_eq_parseI64` was signed off
separately, on 2026-11-24 (S24 sign-off, S24/S25 spec cycle in `STATUS.md` at 9047c72); its
signed-off statements are the ones in this project file. Moved here
from `formal/specs/Specs/External.lean` on 2026-11-24 (statements unchanged). Definitions from
the moved `Defs` modules keep their Lean names (`Defs.Wire.dot`, `Defs.Wire.b64Len` are in module
`Defs.Wire`, back in `formal/specs/Defs/` since the request-state public specifications).

Aeneas upgrade (2026-11-24, `nightly-2026.11.24-fb44cb4`; reviewed and re-signed by the spec owner 2026-11-24): four functions are defined in the Aeneas library instead of by a project model
(`core::borrow::Borrow`, `Option::ok_or`, `Result::map_err`, `Vec::is_empty`; lead decision N8);
forced restatements, name-only: the `Borrow` rename (`Aeneas.Std.core.borrow.Borrow`), the arity
of `alloc.vec.Vec.is_empty_spec` and the `Slice.from` form in `hash_eq`. The model of
`RangeInclusive::contains` follows `nightly-2026-09-17` (an exhausted range contains nothing), and
`contains_u8_spec` and `contains_eq_match_le` are restated exactly for it (exhausted branch
`item < start`; human decision 2026-11-24); `new_contains_u8_spec` is unchanged. 46
`#print axioms` lists below changed in that upgrade (standard axioms added); every list is within
`propext`, `Classical.choice`, `Quot.sound`.

A04–A10 (2026-11-27): the law `trimWhitespace_utf8Bytes` of the model of `str::trim` (section
"`auth.rs` OAuth metadata URL and issuer checks" of `trusted/Rmcp/FunsExternal.lean`), signed
off by the human spec owner on 2026-11-27 with the statements of
`Proofs.Internal.Transport.Auth.AuthMetadata`, restated in the last part of this file and proved
in `Proofs/External/Auth.lean`. The signed-off statements are the ones in this project file. It
depends on `propext`, `Classical.choice` and `Quot.sound`.
-/

/-! ## `Proofs/External/Base64.lean` -/

open Aeneas Aeneas.Std

namespace Proofs.External.Base64

open ExtModel

/-- **Round trip:** decoding the encoding gives the input back. -/
theorem _root_.Theorems.External.Base64.b64Decode_b64 : ∀ x : List U8, b64Decode (b64 x) = some x :=
  _root_.Proofs.External.Base64.b64Decode_b64

/--
info: 'Theorems.External.Base64.b64Decode_b64' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.Base64.b64Decode_b64

/-- **Canonicity:** every input that decodes is the encoding of its result. With
`b64Decode_b64`, `b64Decode s = some y ↔ b64 y = s`: the decoder accepts exactly the canonical
unpadded encodings and rejects everything else (padding, foreign bytes, length `≡ 1 (mod 4)`,
non-zero trailing bits). -/
theorem _root_.Theorems.External.Base64.b64_of_b64Decode
    : ∀ (s y : List U8), b64Decode s = some y → b64 y = s :=
  _root_.Proofs.External.Base64.b64_of_b64Decode

/--
info: 'Theorems.External.Base64.b64_of_b64Decode' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.Base64.b64_of_b64Decode

/-- `b64Decode` accepts exactly the encodings, and returns what was encoded. -/
theorem _root_.Theorems.External.Base64.b64Decode_eq_some_iff
    (s y : List U8) : b64Decode s = some y ↔ b64 y = s :=
  _root_.Proofs.External.Base64.b64Decode_eq_some_iff s y

/--
info: 'Theorems.External.Base64.b64Decode_eq_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.Base64.b64Decode_eq_some_iff

/-- **Alphabet:** every byte of an encoding is a symbol of the URL-safe alphabet. -/
theorem _root_.Theorems.External.Base64.isSome_b64Val_of_mem_b64
    : ∀ (x : List U8), ∀ c ∈ b64 x, (b64Val c).isSome :=
  _root_.Proofs.External.Base64.isSome_b64Val_of_mem_b64

/--
info: 'Theorems.External.Base64.isSome_b64Val_of_mem_b64' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.Base64.isSome_b64Val_of_mem_b64

/-- The symbols of the URL-safe alphabet are the bytes `A`–`Z`, `a`–`z`, `0`–`9`, `-`, `_`. -/
theorem _root_.Theorems.External.Base64.isSome_b64Val_iff (c : U8) :
    (b64Val c).isSome ↔ (65 ≤ c.val ∧ c.val ≤ 90) ∨ (97 ≤ c.val ∧ c.val ≤ 122) ∨
      (48 ≤ c.val ∧ c.val ≤ 57) ∨ c.val = 45 ∨ c.val = 95 :=
  _root_.Proofs.External.Base64.isSome_b64Val_iff c

/--
info: 'Theorems.External.Base64.isSome_b64Val_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.Base64.isSome_b64Val_iff

/-- In particular an encoding never contains the separator `.` (`Defs.Wire.dot`). -/
theorem _root_.Theorems.External.Base64.dot_notMem_b64 (x : List U8) : Defs.Wire.dot ∉ b64 x :=
  _root_.Proofs.External.Base64.dot_notMem_b64 x

/--
info: 'Theorems.External.Base64.dot_notMem_b64' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.Base64.dot_notMem_b64

/-- **Length:** the unpadded encoding of `n` bytes has `⌈4n/3⌉ = (4n + 2) / 3` symbols. -/
theorem _root_.Theorems.External.Base64.length_b64
    : ∀ x : List U8, (b64 x).length = (4 * x.length + 2) / 3 :=
  _root_.Proofs.External.Base64.length_b64

/--
info: 'Theorems.External.Base64.length_b64' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.Base64.length_b64

/-- The encoding is never longer than `Defs.Wire.b64Len` (`4 * ⌈n/3⌉`, the padded length that
`wire::b64_len` computes). -/
theorem _root_.Theorems.External.Base64.length_b64_le_b64Len
    (x : List U8) : (b64 x).length ≤ Defs.Wire.b64Len x.length :=
  _root_.Proofs.External.Base64.length_b64_le_b64Len x

/--
info: 'Theorems.External.Base64.length_b64_le_b64Len' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.Base64.length_b64_le_b64Len

/-- For a length divisible by 3 the encoding has exactly `Defs.Wire.b64Len` symbols. -/
theorem _root_.Theorems.External.Base64.length_b64_of_dvd (x : List U8) (h : 3 ∣ x.length) :
    (b64 x).length = Defs.Wire.b64Len x.length :=
  _root_.Proofs.External.Base64.length_b64_of_dvd x h

/--
info: 'Theorems.External.Base64.length_b64_of_dvd' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.Base64.length_b64_of_dvd

/-- URL-safe symbols: `[0xfb, 0xef, 0xbe]` ↦ `----`, `[0xff, 0xff, 0xff]` ↦ `____`,
`[0xfb, 0xff]` ↦ `-_8`. -/
theorem _root_.Theorems.External.Base64.b64_url_safe_symbols :
    b64 [251#u8, 239#u8, 190#u8] = [45#u8, 45#u8, 45#u8, 45#u8] ∧
    b64 [255#u8, 255#u8, 255#u8] = [95#u8, 95#u8, 95#u8, 95#u8] ∧
    b64 [251#u8, 255#u8] = [45#u8, 95#u8, 56#u8] :=
  _root_.Proofs.External.Base64.b64_url_safe_symbols

/--
info: 'Theorems.External.Base64.b64_url_safe_symbols' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.Base64.b64_url_safe_symbols

/-- The standard-alphabet symbols `+` (43) and `/` (47) are rejected. -/
theorem _root_.Theorems.External.Base64.b64Decode_rejects_standard_symbols :
    b64Decode [43#u8, 43#u8, 43#u8, 43#u8] = none ∧
    b64Decode [47#u8, 47#u8, 47#u8, 47#u8] = none :=
  _root_.Proofs.External.Base64.b64Decode_rejects_standard_symbols

/--
info: 'Theorems.External.Base64.b64Decode_rejects_standard_symbols' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.Base64.b64Decode_rejects_standard_symbols

/-- Padding is rejected: `Zg==`, `Zm8=`, `Zm9vYg==`. -/
theorem _root_.Theorems.External.Base64.b64Decode_rejects_padding :
    b64Decode [90#u8, 103#u8, 61#u8, 61#u8] = none ∧
    b64Decode [90#u8, 109#u8, 56#u8, 61#u8] = none ∧
    b64Decode [90#u8, 109#u8, 57#u8, 118#u8, 89#u8, 103#u8, 61#u8, 61#u8] = none :=
  _root_.Proofs.External.Base64.b64Decode_rejects_padding

/--
info: 'Theorems.External.Base64.b64Decode_rejects_padding' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.Base64.b64Decode_rejects_padding

/-- Non-canonical trailing bits are rejected: `Zh`, `Zm9`, `_x`; `_w` decodes to `[0xff]`. -/
theorem _root_.Theorems.External.Base64.b64Decode_trailing_bits :
    b64Decode [90#u8, 104#u8] = none ∧
    b64Decode [90#u8, 109#u8, 57#u8] = none ∧
    b64Decode [95#u8, 120#u8] = none ∧
    b64Decode [95#u8, 119#u8] = some [255#u8] :=
  _root_.Proofs.External.Base64.b64Decode_trailing_bits

/--
info: 'Theorems.External.Base64.b64Decode_trailing_bits' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.Base64.b64Decode_trailing_bits

/-- Impossible lengths and foreign bytes are rejected: `Z`, `Zm9vY`, `!!!!`, `Zm 9v`, `Zm9v
`. -/
theorem _root_.Theorems.External.Base64.b64Decode_rejects_malformed :
    b64Decode [90#u8] = none ∧
    b64Decode [90#u8, 109#u8, 57#u8, 118#u8, 89#u8] = none ∧
    b64Decode [33#u8, 33#u8, 33#u8, 33#u8] = none ∧
    b64Decode [90#u8, 109#u8, 32#u8, 57#u8, 118#u8] = none ∧
    b64Decode [90#u8, 109#u8, 57#u8, 118#u8, 10#u8] = none :=
  _root_.Proofs.External.Base64.b64Decode_rejects_malformed

/--
info: 'Theorems.External.Base64.b64Decode_rejects_malformed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.Base64.b64Decode_rejects_malformed

end Proofs.External.Base64

/-! ## `Proofs/External/String.lean` -/

open Aeneas Aeneas.Std

namespace Proofs.External.Utf8

open ExtModel Proofs.External.Base64

/-- `utf8 s` has `s.utf8ByteSize` bytes. -/
theorem _root_.Theorems.External.Utf8.length_utf8 (s : String) : (utf8 s).length = s.utf8ByteSize :=
  _root_.Proofs.External.Utf8.length_utf8 s

/--
info: 'Theorems.External.Utf8.length_utf8' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.Utf8.length_utf8

/-- `utf8` is additive. -/
theorem _root_.Theorems.External.Utf8.utf8_append
    (s t : String) : utf8 (s ++ t) = utf8 s ++ utf8 t :=
  _root_.Proofs.External.Utf8.utf8_append s t

/--
info: 'Theorems.External.Utf8.utf8_append' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.Utf8.utf8_append

/-- `strOfBytes?` inverts `utf8`. -/
theorem _root_.Theorems.External.Utf8.strOfBytes?_utf8
    (s : String) : strOfBytes? (utf8 s) = some s :=
  _root_.Proofs.External.Utf8.strOfBytes?_utf8 s

/--
info: 'Theorems.External.Utf8.strOfBytes?_utf8' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.Utf8.strOfBytes?_utf8

/-- `strOfBytes? l = some s` exactly when `l` is the UTF-8 encoding of `s`. -/
theorem _root_.Theorems.External.Utf8.strOfBytes?_eq_some_iff (l : List U8) (s : String) :
    strOfBytes? l = some s ↔ l = utf8 s :=
  _root_.Proofs.External.Utf8.strOfBytes?_eq_some_iff l s

/--
info: 'Theorems.External.Utf8.strOfBytes?_eq_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.Utf8.strOfBytes?_eq_some_iff

/-- `strOfBytes? l = none` exactly when `l` is the encoding of no string (not UTF-8). -/
theorem _root_.Theorems.External.Utf8.strOfBytes?_eq_none_iff
    (l : List U8) : strOfBytes? l = none ↔ ∀ s, l ≠ utf8 s :=
  _root_.Proofs.External.Utf8.strOfBytes?_eq_none_iff l

/--
info: 'Theorems.External.Utf8.strOfBytes?_eq_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.Utf8.strOfBytes?_eq_none_iff

/-- Two strings with the same bytes are equal. -/
theorem _root_.Theorems.External.Utf8.utf8_injective {s t : String} (h : utf8 s = utf8 t) : s = t :=
  _root_.Proofs.External.Utf8.utf8_injective h

/--
info: 'Theorems.External.Utf8.utf8_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.Utf8.utf8_injective

/-- ASCII bytes, as characters, encode to themselves. -/
theorem _root_.Theorems.External.Utf8.utf8_ofList_ascii (l : List U8) (h : ∀ b ∈ l, b.val < 128) :
    utf8 (String.ofList (l.map (fun b => Char.ofNat b.val))) = l :=
  _root_.Proofs.External.Utf8.utf8_ofList_ascii l h

/--
info: 'Theorems.External.Utf8.utf8_ofList_ascii' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.Utf8.utf8_ofList_ascii

/-- Appending an ASCII character appends its one byte. -/
theorem _root_.Theorems.External.Utf8.utf8_push_ascii (s : String) (c : Char) (h : c.toNat < 128) :
    utf8 (s.push c) = utf8 s ++ [byte c.toNat] :=
  _root_.Proofs.External.Utf8.utf8_push_ascii s c h

/--
info: 'Theorems.External.Utf8.utf8_push_ascii' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.Utf8.utf8_push_ascii

/-- An ASCII character is one byte. -/
theorem _root_.Theorems.External.Utf8.utf8_ofList_singleton_ascii (ch : Char) (h : ch.toNat < 128) :
    utf8 (String.ofList [ch]) = [byte ch.toNat] :=
  _root_.Proofs.External.Utf8.utf8_ofList_singleton_ascii ch h

/--
info: 'Theorems.External.Utf8.utf8_ofList_singleton_ascii' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.Utf8.utf8_ofList_singleton_ascii

/-- The bytes of the Aeneas `toStr` of a literal are its `utf8` bytes. -/
theorem _root_.Theorems.External.Utf8.toStr_val (s : String) (h : s.toByteArray.size ≤ U32.max) :
    (toStr s h).val = utf8 s :=
  _root_.Proofs.External.Utf8.toStr_val s h

/--
info: 'Theorems.External.Utf8.toStr_val' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.Utf8.toStr_val

/-- Every symbol of an encoding is ASCII. -/
theorem _root_.Theorems.External.Utf8.val_lt_128_of_mem_b64 (x : List U8) :
    ∀ b ∈ b64 x, b.val < 128 :=
  _root_.Proofs.External.Utf8.val_lt_128_of_mem_b64 x

/--
info: 'Theorems.External.Utf8.val_lt_128_of_mem_b64' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.Utf8.val_lt_128_of_mem_b64

/-- A Rust `String` length (at most `isize::MAX`) fits in a `usize`, so the bytes of any
`String` the models produce form a `Slice`. -/
theorem _root_.Theorems.External.Utf8.maxStringBytes_le_usize_max : maxStringBytes ≤ Usize.max :=
  _root_.Proofs.External.Utf8.maxStringBytes_le_usize_max

/--
info: 'Theorems.External.Utf8.maxStringBytes_le_usize_max' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Theorems.External.Utf8.maxStringBytes_le_usize_max

end Proofs.External.Utf8

/-! ## `Proofs/External/Prim.lean` -/

open Aeneas Aeneas.Std Result

namespace model.request_state_wire.prim

open ExtModel Proofs.External.Utf8 Proofs.External.Base64

/-- **Spec theorem for `rmcp::model::request_state_wire::prim::hmac_sha256`**

Always succeeds (any key length) with the HMAC-SHA256 tag `hmacSha256 key msg`. -/
theorem _root_.Theorems.External.model.request_state_wire.prim.hmac_sha256_spec
    (key : Slice U8) (msg : Slice U8) :
    hmac_sha256 key msg ⦃ (result : Std.Array U8 32#usize) =>
      result = hmacSha256 key.val msg.val ⦄ :=
  _root_.model.request_state_wire.prim.hmac_sha256_spec key msg

/--
info: 'Theorems.External.model.request_state_wire.prim.hmac_sha256_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.model.request_state_wire.prim.hmac_sha256_spec

/-- **Spec theorem for `rmcp::model::request_state_wire::prim::hmac_sha256_verify`**

Always succeeds; the result is `true` exactly when `tag` is, byte for byte, the HMAC-SHA256 tag
of `msg` under `key`. -/
theorem _root_.Theorems.External.model.request_state_wire.prim.hmac_sha256_verify_spec
    (key : Slice U8) (msg : Slice U8) (tag : Slice U8) :
    hmac_sha256_verify key msg tag ⦃ (result : Bool) =>
      result = decide (tag.val = (hmacSha256 key.val msg.val).val) ⦄ :=
  _root_.model.request_state_wire.prim.hmac_sha256_verify_spec key msg tag

/--
info: 'Theorems.External.model.request_state_wire.prim.hmac_sha256_verify_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.model.request_state_wire.prim.hmac_sha256_verify_spec

/-- A tag whose length is not 32 is rejected (in particular a truncated tag). -/
theorem _root_.Theorems.External.model.request_state_wire.prim.hmac_sha256_verify_eq_ok_false_of_length_ne
    (key : Slice U8) (msg : Slice U8) (tag : Slice U8)
    (h : tag.length ≠ 32) : hmac_sha256_verify key msg tag = ok false :=
  _root_.model.request_state_wire.prim.hmac_sha256_verify_eq_ok_false_of_length_ne key msg tag h

/--
info: 'Theorems.External.model.request_state_wire.prim.hmac_sha256_verify_eq_ok_false_of_length_ne' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.model.request_state_wire.prim.hmac_sha256_verify_eq_ok_false_of_length_ne

/-- The tag that `hmac_sha256` computes is accepted. -/
theorem _root_.Theorems.External.model.request_state_wire.prim.hmac_sha256_verify_hmac_sha256
    (key : Slice U8) (msg : Slice U8) (tag : Slice U8)
    (h : tag.val = (hmacSha256 key.val msg.val).val) :
    hmac_sha256_verify key msg tag = ok true :=
  _root_.model.request_state_wire.prim.hmac_sha256_verify_hmac_sha256 key msg tag h

/--
info: 'Theorems.External.model.request_state_wire.prim.hmac_sha256_verify_hmac_sha256' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.model.request_state_wire.prim.hmac_sha256_verify_hmac_sha256

/-- **Spec theorem for `rmcp::model::request_state_wire::prim::b64_encode_into`**

Appends the unpadded Base64url symbols of `input` to `out`: the bytes of the result are those
of `out` followed by `b64 input` (`(4n + 2) / 3` symbols for `n` input bytes,
`Proofs.External.Base64.length_b64`). Precondition: the result fits in a Rust `String`
(`isize::MAX` bytes); otherwise the Rust code panics (`b64_encode_into_fail`). -/
theorem _root_.Theorems.External.model.request_state_wire.prim.b64_encode_into_spec
    (input : Slice U8) (out : String)
    (h : out.utf8ByteSize + (4 * input.length + 2) / 3 ≤ maxStringBytes) :
    b64_encode_into input out ⦃ (result : String) =>
      utf8 result = utf8 out ++ b64 input.val ⦄ :=
  _root_.model.request_state_wire.prim.b64_encode_into_spec input out h

/--
info: 'Theorems.External.model.request_state_wire.prim.b64_encode_into_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.model.request_state_wire.prim.b64_encode_into_spec

/-- Beyond the `String` limit, `b64_encode_into` panics. -/
theorem _root_.Theorems.External.model.request_state_wire.prim.b64_encode_into_fail
    (input : Slice U8) (out : String)
    (h : maxStringBytes < out.utf8ByteSize + (4 * input.length + 2) / 3) :
    b64_encode_into input out = fail Error.panic :=
  _root_.model.request_state_wire.prim.b64_encode_into_fail input out h

/--
info: 'Theorems.External.model.request_state_wire.prim.b64_encode_into_fail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.model.request_state_wire.prim.b64_encode_into_fail

/-- **Spec theorem for `rmcp::model::request_state_wire::prim::b64_decode`**

Always succeeds; the result is `b64Decode input`: `some` of the decoded bytes exactly when
`input` is the unpadded Base64url encoding of them (`b64Decode_eq_some_iff`), `none` otherwise. -/
theorem _root_.Theorems.External.model.request_state_wire.prim.b64_decode_spec (input : Slice U8) :
    b64_decode input ⦃ (result : Option (alloc.vec.Vec U8)) =>
      result.map (fun v => v.val) = b64Decode input.val ⦄ :=
  _root_.model.request_state_wire.prim.b64_decode_spec input

/--
info: 'Theorems.External.model.request_state_wire.prim.b64_decode_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.model.request_state_wire.prim.b64_decode_spec

end model.request_state_wire.prim

/-! ## `Proofs/External/Std.lean` -/

open Aeneas Aeneas.Std Result

open ExtModel Proofs.External.Utf8 Proofs.External.Base64

/-- **Spec theorem for `core::borrow::{impl Borrow<T> for T}::borrow`**: the identity. -/
theorem Theorems.External.core.borrow.Borrow.Blanket.borrow_spec {T : Type} (self : T) :
    core.borrow.Borrow.Blanket.borrow self ⦃ (result : T) => result = self ⦄ :=
  _root_.core.borrow.Borrow.Blanket.borrow_spec self

/--
info: 'Theorems.External.core.borrow.Borrow.Blanket.borrow_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.core.borrow.Borrow.Blanket.borrow_spec

/-- **Spec theorem for `core::option::Option::ok_or`**: `Some v ↦ Ok v`, `None ↦ Err err`. -/
theorem Theorems.External.core.option.Option.ok_or_spec
    {T : Type} {E : Type} (self : Option T) (err : E) :
    core.option.Option.ok_or self err ⦃ (result : core.result.Result T E) =>
      result = match self with
        | some v => core.result.Result.Ok v
        | none => core.result.Result.Err err ⦄ :=
  _root_.core.option.Option.ok_or_spec self err

/--
info: 'Theorems.External.core.option.Option.ok_or_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.core.option.Option.ok_or_spec

/-- **Spec theorem for `<Option<T> as Default>::default`**: `None`. -/
theorem Theorems.External.core.option.Option.Insts.CoreDefaultDefault.default_spec (T : Type) :
    core.option.Option.Insts.CoreDefaultDefault.default T ⦃ (result : Option T) =>
      result = none ⦄ :=
  _root_.core.option.Option.Insts.CoreDefaultDefault.default_spec T

/--
info: 'Theorems.External.core.option.Option.Insts.CoreDefaultDefault.default_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.core.option.Option.Insts.CoreDefaultDefault.default_spec

/-- **Spec theorem for `core::result::Result::is_err`**: `true` exactly for `Err`. -/
theorem Theorems.External.core.result.Result.is_err_spec
    {T : Type} {E : Type} (self : core.result.Result T E) :
    core.result.Result.is_err self ⦃ (result : Bool) =>
      result = match self with
        | core.result.Result.Ok _ => false
        | core.result.Result.Err _ => true ⦄ :=
  _root_.core.result.Result.is_err_spec self

/--
info: 'Theorems.External.core.result.Result.is_err_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.core.result.Result.is_err_spec

/-- `core::result::Result::map_err` on `Ok`: unchanged, the closure is not called. -/
theorem Theorems.External.core.result.Result.map_err_ok {T E F O : Type}
    (inst : core.ops.function.FnOnce O E F) (t : T) (op : O) :
    core.result.Result.map_err inst (core.result.Result.Ok t : core.result.Result T E) op =
      ok (core.result.Result.Ok t) :=
  _root_.core.result.Result.map_err_ok inst t op

/--
info: 'Theorems.External.core.result.Result.map_err_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.core.result.Result.map_err_ok

/-- `core::result::Result::map_err` on `Err e`: `Err (op e)`; the closure's failure
propagates. -/
theorem Theorems.External.core.result.Result.map_err_err {T E F O : Type}
    (inst : core.ops.function.FnOnce O E F) (e : E) (op : O) :
    core.result.Result.map_err inst (core.result.Result.Err e : core.result.Result T E) op =
      (do let f ← inst.call_once op e; ok (core.result.Result.Err f)) :=
  _root_.core.result.Result.map_err_err inst e op

/--
info: 'Theorems.External.core.result.Result.map_err_err' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.core.result.Result.map_err_err

/-- **Spec theorem for `<&[T] as Default>::default`**: the empty slice. -/
theorem Theorems.External.Shared0Slice.Insts.CoreDefaultDefault.default_spec (T : Type) :
    Shared0Slice.Insts.CoreDefaultDefault.default T ⦃ (result : Slice T) =>
      result.val = [] ⦄ :=
  _root_.Shared0Slice.Insts.CoreDefaultDefault.default_spec T

/--
info: 'Theorems.External.Shared0Slice.Insts.CoreDefaultDefault.default_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.Shared0Slice.Insts.CoreDefaultDefault.default_spec

/-- **Spec theorem for `core::str::str::len`**: the number of bytes; for every `Str`. -/
theorem Theorems.External.core.str.Str.len_spec (self : Str) :
    core.str.Str.len self ⦃ (result : Usize) => result.val = self.val.length ⦄ :=
  _root_.core.str.Str.len_spec self

/--
info: 'Theorems.External.core.str.Str.len_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.core.str.Str.len_spec

/-- **Spec theorem for `core::str::str::as_bytes`**: the same bytes; for every `Str`. -/
theorem Theorems.External.core.str.Str.as_bytes_spec (self : Str) :
    core.str.Str.as_bytes self ⦃ (result : Slice U8) => result.val = self.val ⦄ :=
  _root_.core.str.Str.as_bytes_spec self

/--
info: 'Theorems.External.core.str.Str.as_bytes_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.core.str.Str.as_bytes_spec

/-- **Spec theorem for `String::with_capacity`**: the empty string, if `capacity ≤ isize::MAX`
(else `with_capacity_fail`). -/
theorem Theorems.External.alloc.string.String.with_capacity_spec (capacity : Usize)
    (h : capacity.val ≤ maxStringBytes) :
    alloc.string.String.with_capacity capacity ⦃ (result : String) => result = "" ⦄ :=
  _root_.alloc.string.String.with_capacity_spec capacity h

/--
info: 'Theorems.External.alloc.string.String.with_capacity_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.alloc.string.String.with_capacity_spec

/-- `String::with_capacity` panics ("capacity overflow") above `isize::MAX`. -/
theorem Theorems.External.alloc.string.String.with_capacity_fail (capacity : Usize)
    (h : maxStringBytes < capacity.val) :
    alloc.string.String.with_capacity capacity = fail Error.panic :=
  _root_.alloc.string.String.with_capacity_fail capacity h

/--
info: 'Theorems.External.alloc.string.String.with_capacity_fail' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.alloc.string.String.with_capacity_fail

/-- **Spec theorem for `String::push_str`**: for a UTF-8 argument (`string` is the bytes of `t`,
as every Rust `&str` is) whose result fits in a `String`, appends `t`; the result's bytes are
the old bytes followed by `string`. -/
theorem Theorems.External.alloc.string.String.push_str_spec
    (self : String) (string : Str) (t : String)
    (ht : string.val = utf8 t) (h : self.utf8ByteSize + string.val.length ≤ maxStringBytes) :
    alloc.string.String.push_str self string ⦃ (result : String) =>
      result = self ++ t ∧ utf8 result = utf8 self ++ string.val ⦄ :=
  _root_.alloc.string.String.push_str_spec self string t ht h

/--
info: 'Theorems.External.alloc.string.String.push_str_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.alloc.string.String.push_str_spec

/-- `String::push_str` with a result beyond `isize::MAX` bytes panics. -/
theorem Theorems.External.alloc.string.String.push_str_fail
    (self : String) (string : Str) (t : String)
    (ht : string.val = utf8 t) (h : maxStringBytes < self.utf8ByteSize + string.val.length) :
    alloc.string.String.push_str self string = fail Error.panic :=
  _root_.alloc.string.String.push_str_fail self string t ht h

/--
info: 'Theorems.External.alloc.string.String.push_str_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.alloc.string.String.push_str_fail

/-- `String::push_str` with bytes that are not UTF-8 (no Rust `&str`) is outside the Rust
domain: `fail undef`. -/
theorem Theorems.External.alloc.string.String.push_str_not_utf8 (self : String) (string : Str)
    (h : ∀ t, string.val ≠ utf8 t) :
    alloc.string.String.push_str self string = fail Error.undef :=
  _root_.alloc.string.String.push_str_not_utf8 self string h

/--
info: 'Theorems.External.alloc.string.String.push_str_not_utf8' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.alloc.string.String.push_str_not_utf8

/-- **Spec theorem for `String::push`**: appends the character if the result fits in a
`String`; the result's bytes are the old bytes followed by the character's encoding. -/
theorem Theorems.External.alloc.string.String.push_spec (self : String) (ch : Char)
    (h : self.utf8ByteSize + ch.utf8Size ≤ maxStringBytes) :
    alloc.string.String.push self ch ⦃ (result : String) =>
      result = self.push ch ∧ utf8 result = utf8 self ++ utf8 (String.ofList [ch]) ⦄ :=
  _root_.alloc.string.String.push_spec self ch h

/--
info: 'Theorems.External.alloc.string.String.push_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.alloc.string.String.push_spec

/-- `String::push` with a result beyond `isize::MAX` bytes panics. -/
theorem Theorems.External.alloc.string.String.push_fail (self : String) (ch : Char)
    (h : maxStringBytes < self.utf8ByteSize + ch.utf8Size) :
    alloc.string.String.push self ch = fail Error.panic :=
  _root_.alloc.string.String.push_fail self ch h

/--
info: 'Theorems.External.alloc.string.String.push_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.alloc.string.String.push_fail

/-- **Spec theorem for `String::as_bytes`**: the UTF-8 bytes. The precondition holds for every
Rust `String` (at most `isize::MAX` bytes); see `as_bytes_fail`. -/
theorem Theorems.External.alloc.string.String.as_bytes_spec
    (self : String) (h : self.utf8ByteSize ≤ Usize.max) :
    alloc.string.String.as_bytes self ⦃ (result : Slice U8) => result.val = utf8 self ⦄ :=
  _root_.alloc.string.String.as_bytes_spec self h

/--
info: 'Theorems.External.alloc.string.String.as_bytes_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.alloc.string.String.as_bytes_spec

/-- `String::as_bytes` on a Lean `String` longer than `Usize.max` bytes (no Rust `String`). -/
theorem Theorems.External.alloc.string.String.as_bytes_fail
    (self : String) (h : Usize.max < self.utf8ByteSize) :
    alloc.string.String.as_bytes self = fail Error.maximumSizeExceeded :=
  _root_.alloc.string.String.as_bytes_fail self h

/--
info: 'Theorems.External.alloc.string.String.as_bytes_fail' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.alloc.string.String.as_bytes_fail

/-- **Spec theorem for `String::from_utf8`**: `Ok s` when the bytes are the encoding of `s`;
otherwise `Err` carrying the bytes. -/
theorem Theorems.External.alloc.string.String.from_utf8_spec (vec : alloc.vec.Vec U8) :
    alloc.string.String.from_utf8 vec ⦃ (result : core.result.Result String
        alloc.string.FromUtf8Error) =>
      match result with
      | core.result.Result.Ok s => vec.val = utf8 s
      | core.result.Result.Err e => (∀ s, vec.val ≠ utf8 s) ∧ e.bytes = vec ⦄ :=
  _root_.alloc.string.String.from_utf8_spec vec

/--
info: 'Theorems.External.alloc.string.String.from_utf8_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.alloc.string.String.from_utf8_spec

/-- **Spec theorem for `<String as PartialEq>::eq`**: equality. -/
theorem Theorems.External.alloc.string.String.Insts.CoreCmpPartialEqString.eq_spec (self : String)
    (other : String) :
    alloc.string.String.Insts.CoreCmpPartialEqString.eq self other ⦃ (result : Bool) =>
      result = decide (self = other) ⦄ :=
  _root_.alloc.string.String.Insts.CoreCmpPartialEqString.eq_spec self other

/--
info: 'Theorems.External.alloc.string.String.Insts.CoreCmpPartialEqString.eq_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.alloc.string.String.Insts.CoreCmpPartialEqString.eq_spec

/-- **Spec theorem for `<String as Eq>::assert_fields_are_eq`**: succeeds. -/
theorem Theorems.External.alloc.string.String.Insts.CoreCmpEq.assert_fields_are_eq_spec
    (self : String) :
    alloc.string.String.Insts.CoreCmpEq.assert_fields_are_eq self ⦃ (_ : Unit) => True ⦄ :=
  _root_.alloc.string.String.Insts.CoreCmpEq.assert_fields_are_eq_spec self

/--
info: 'Theorems.External.alloc.string.String.Insts.CoreCmpEq.assert_fields_are_eq_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.alloc.string.String.Insts.CoreCmpEq.assert_fields_are_eq_spec

/-- **Spec theorem for `<String as Clone>::clone`**: the same string. -/
theorem Theorems.External.alloc.string.String.Insts.CoreCloneClone.clone_spec (self : String) :
    alloc.string.String.Insts.CoreCloneClone.clone self ⦃ (result : String) =>
      result = self ⦄ :=
  _root_.alloc.string.String.Insts.CoreCloneClone.clone_spec self

/--
info: 'Theorems.External.alloc.string.String.Insts.CoreCloneClone.clone_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.alloc.string.String.Insts.CoreCloneClone.clone_spec

/-- `<String as Hash>::hash` writes the bytes and then `0xff` (for a Rust-sized `String`). -/
theorem Theorems.External.alloc.string.String.Insts.CoreHashHash.hash_eq {H : Type}
    (inst : core.hash.Hasher H) (self : String) (state : H)
    (h : self.utf8ByteSize ≤ Usize.max) :
    alloc.string.String.Insts.CoreHashHash.hash inst self state =
      (do
        let state ← inst.write state (Slice.from (utf8 self) (by rw [length_utf8]; exact h))
        inst.write state (Slice.from [byte 255] (by scalar_tac))) :=
  _root_.alloc.string.String.Insts.CoreHashHash.hash_eq inst self state h

/--
info: 'Theorems.External.alloc.string.String.Insts.CoreHashHash.hash_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.alloc.string.String.Insts.CoreHashHash.hash_eq

/-- **Spec theorem for `Vec::is_empty`**: `true` exactly for the empty vector. -/
theorem Theorems.External.alloc.vec.Vec.is_empty_spec
    {T : Type} (self : alloc.vec.Vec T) :
    alloc.vec.Vec.is_empty self ⦃ (result : Bool) => result = decide (self.val = []) ⦄ :=
  _root_.alloc.vec.Vec.is_empty_spec self

/--
info: 'Theorems.External.alloc.vec.Vec.is_empty_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.alloc.vec.Vec.is_empty_spec

/-- **Spec theorem for `<RandomState as Clone>::clone`**: the same value. -/
theorem Theorems.External.std.hash.random.RandomState.Insts.CoreCloneClone.clone_spec
    (self : std.hash.random.RandomState) :
    std.hash.random.RandomState.Insts.CoreCloneClone.clone self ⦃
      (result : std.hash.random.RandomState) => result = self ⦄ :=
  _root_.std.hash.random.RandomState.Insts.CoreCloneClone.clone_spec self

/--
info: 'Theorems.External.std.hash.random.RandomState.Insts.CoreCloneClone.clone_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.std.hash.random.RandomState.Insts.CoreCloneClone.clone_spec

/-- **Spec theorem for `<RandomState as BuildHasher>::build_hasher`**: the map's keys, no
bytes written. -/
theorem Theorems.External.std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher.build_hasher_spec
    (self : std.hash.random.RandomState) :
    std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher.build_hasher self ⦃
      (result : std.hash.random.DefaultHasher) =>
        result = { k0 := self.k0, k1 := self.k1, written := [] } ⦄ :=
  _root_.std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher.build_hasher_spec self

/--
info: 'Theorems.External.std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher.build_hasher_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher.build_hasher_spec

/-- **Spec theorem for `<DefaultHasher as Hasher>::write`**: appends the bytes. -/
theorem Theorems.External.std.hash.random.DefaultHasher.Insts.CoreHashHasher.write_spec
    (self : std.hash.random.DefaultHasher) (msg : Slice U8) :
    std.hash.random.DefaultHasher.Insts.CoreHashHasher.write self msg ⦃
      (result : std.hash.random.DefaultHasher) =>
        result = { self with written := self.written ++ msg.val } ⦄ :=
  _root_.std.hash.random.DefaultHasher.Insts.CoreHashHasher.write_spec self msg

/--
info: 'Theorems.External.std.hash.random.DefaultHasher.Insts.CoreHashHasher.write_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.std.hash.random.DefaultHasher.Insts.CoreHashHasher.write_spec

/-- **Spec theorem for `<DefaultHasher as Hasher>::finish`**: SipHash-1-3 of keys and bytes. -/
theorem Theorems.External.std.hash.random.DefaultHasher.Insts.CoreHashHasher.finish_spec
    (self : std.hash.random.DefaultHasher) :
    std.hash.random.DefaultHasher.Insts.CoreHashHasher.finish self ⦃ (result : U64) =>
      result = sipHash13 self.k0 self.k1 self.written ⦄ :=
  _root_.std.hash.random.DefaultHasher.Insts.CoreHashHasher.finish_spec self

/--
info: 'Theorems.External.std.hash.random.DefaultHasher.Insts.CoreHashHasher.finish_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.std.hash.random.DefaultHasher.Insts.CoreHashHasher.finish_spec

/-- `HashMap::get` is the lookup `ExtModel.HashMap.find` over the entries, whatever the
hashing instances. -/
theorem Theorems.External.std.collections.hash.map.HashMap.get_eq
    {K V S A Q Clause2_Hasher : Type} (eqK : core.cmp.Eq K) (hashK : core.hash.Hash K)
    (bh : rmcp.core.hash.BuildHasher S Clause2_Hasher) (borrow : Aeneas.Std.core.borrow.Borrow K Q)
    (hashQ : core.hash.Hash Q) (eqQ : core.cmp.Eq Q)
    (self : std.collections.hash.map.HashMap K V S A) (k : Q) :
    std.collections.hash.map.HashMap.get eqK hashK bh borrow hashQ eqQ self k =
      ExtModel.HashMap.find borrow eqQ k self.entries :=
  _root_.std.collections.hash.map.HashMap.get_eq eqK hashK bh borrow hashQ eqQ self k

/--
info: 'Theorems.External.std.collections.hash.map.HashMap.get_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.std.collections.hash.map.HashMap.get_eq

/-- **Spec theorem for `HashMap::get`** at the instance of the translation (`K = Q = String`,
`S = RandomState`): the value of the first entry whose key is `k`. With pairwise distinct keys
(the Rust invariant) this is the value stored under `k`
(`Proofs.External.HashMap.find?_key_of_mem`), and `None` when `k` is not a key
(`Proofs.External.HashMap.find?_key_of_not_mem`); without distinct keys, a value is found exactly
when `k` is a key (`Proofs.External.HashMap.find?_key_isSome_iff`). -/
theorem Theorems.External.std.collections.hash.map.HashMap.get_string_spec {V A : Type}
    (self : std.collections.hash.map.HashMap String V std.hash.random.RandomState A)
    (k : String) :
    std.collections.hash.map.HashMap.get rmcp.alloc.string.String.Insts.CoreCmpEq
      rmcp.alloc.string.String.Insts.CoreHashHash
      rmcp.std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher
      (Aeneas.Std.core.borrow.Borrow.Blanket String) rmcp.alloc.string.String.Insts.CoreHashHash
      rmcp.alloc.string.String.Insts.CoreCmpEq self k ⦃ (result : Option V) =>
        result = (self.entries.find? (fun e => decide (e.1 = k))).map Prod.snd ⦄ :=
  _root_.std.collections.hash.map.HashMap.get_string_spec self k

/--
info: 'Theorems.External.std.collections.hash.map.HashMap.get_string_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.std.collections.hash.map.HashMap.get_string_spec

namespace Proofs.External.HashMap

/-- With distinct keys, the first entry with key `k` is the one stored under `k`. -/
theorem _root_.Theorems.External.HashMap.find?_key_of_mem
    {V : Type} (entries : List (String × V)) (k : String) (v : V)
    (hnd : (entries.map Prod.fst).Nodup) (hm : (k, v) ∈ entries) :
    (entries.find? (fun e => decide (e.1 = k))).map Prod.snd = some v :=
  _root_.Proofs.External.HashMap.find?_key_of_mem entries k v hnd hm

/--
info: 'Theorems.External.HashMap.find?_key_of_mem' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.HashMap.find?_key_of_mem

/-- No entry has key `k`: the lookup gives `none`. -/
theorem _root_.Theorems.External.HashMap.find?_key_of_not_mem
    {V : Type} (entries : List (String × V)) (k : String)
    (h : k ∉ entries.map Prod.fst) :
    (entries.find? (fun e => decide (e.1 = k))).map Prod.snd = none :=
  _root_.Proofs.External.HashMap.find?_key_of_not_mem entries k h

/--
info: 'Theorems.External.HashMap.find?_key_of_not_mem' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.HashMap.find?_key_of_not_mem

/-- **Found, without distinct keys:** the lookup returns a value exactly when `k` is a key; no
`Nodup` premise (with duplicate keys it is the value of the first entry). -/
theorem _root_.Theorems.External.HashMap.find?_key_isSome_iff
    {V : Type} (entries : List (String × V)) (k : String) :
    ((entries.find? (fun e => decide (e.1 = k))).map Prod.snd).isSome ↔
      k ∈ entries.map Prod.fst :=
  _root_.Proofs.External.HashMap.find?_key_isSome_iff entries k

/--
info: 'Theorems.External.HashMap.find?_key_isSome_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.HashMap.find?_key_isSome_iff

end Proofs.External.HashMap

/-- `HashMap::clone`: clones the hash builder, the allocator and every key and value. -/
theorem Theorems.External.std.collections.hash.map.HashMap.Insts.CoreCloneClone.clone_eq
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
        ok { hash_builder, alloc, entries }) :=
  _root_.std.collections.hash.map.HashMap.Insts.CoreCloneClone.clone_eq cK cV cS cA self

/--
info: 'Theorems.External.std.collections.hash.map.HashMap.Insts.CoreCloneClone.clone_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.std.collections.hash.map.HashMap.Insts.CoreCloneClone.clone_eq

/-- **Spec theorem for `Zeroizing::new`**: wraps the value. -/
theorem Theorems.External.zeroize.Zeroizing.new_spec
    {Z : Type} (inst : rmcp.zeroize.Zeroize Z) (value : Z) :
    zeroize.Zeroizing.new inst value ⦃ (result : zeroize.Zeroizing Z) =>
      result.inner = value ⦄ :=
  _root_.zeroize.Zeroizing.new_spec inst value

/--
info: 'Theorems.External.zeroize.Zeroizing.new_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.zeroize.Zeroizing.new_spec

/-- **Spec theorem for `<Zeroizing<Z> as Deref>::deref`**: the wrapped value. -/
theorem Theorems.External.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref_spec {Z : Type}
    (inst : rmcp.zeroize.Zeroize Z) (self : zeroize.Zeroizing Z) :
    zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref inst self ⦃ (result : Z) =>
      result = self.inner ⦄ :=
  _root_.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref_spec inst self

/--
info: 'Theorems.External.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref_spec

/-- `<Zeroizing<Z> as Clone>::clone` wraps a clone of the value. -/
theorem Theorems.External.zeroize.Zeroizing.Insts.CoreCloneClone.clone_eq
    {Z : Type} (inst : rmcp.zeroize.Zeroize Z)
    (cZ : core.clone.Clone Z) (self : zeroize.Zeroizing Z) :
    zeroize.Zeroizing.Insts.CoreCloneClone.clone inst cZ self =
      (do let v ← cZ.clone self.inner; ok { inner := v }) :=
  _root_.zeroize.Zeroizing.Insts.CoreCloneClone.clone_eq inst cZ self

/--
info: 'Theorems.External.zeroize.Zeroizing.Insts.CoreCloneClone.clone_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.zeroize.Zeroizing.Insts.CoreCloneClone.clone_eq

/-- `<Z as Zeroize>::zeroize` for `Z: DefaultIsZeroes` is `Z::default()`. -/
theorem Theorems.External.zeroize.Zeroize.Blanket.zeroize_eq
    {Z : Type} (inst : rmcp.zeroize.DefaultIsZeroes Z)
    (self : Z) :
    zeroize.Zeroize.Blanket.zeroize inst self = inst.coredefaultDefaultInst.default :=
  _root_.zeroize.Zeroize.Blanket.zeroize_eq inst self

/--
info: 'Theorems.External.zeroize.Zeroize.Blanket.zeroize_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.zeroize.Zeroize.Blanket.zeroize_eq

/-- `<Vec<Z> as Zeroize>::zeroize` zeroizes each element and returns the empty vector. -/
theorem Theorems.External.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize_eq
    {Z : Type} (inst : rmcp.zeroize.Zeroize Z)
    (self : alloc.vec.Vec Z) :
    alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize inst self =
      (do let _ ← self.val.mapM inst.zeroize; ok (alloc.vec.Vec.new Z)) :=
  _root_.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize_eq inst self

/--
info: 'Theorems.External.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize_eq

/-! # Phase 2 (S26/S27)

The laws of the Phase 2 external models, in the order of their proof files. -/

open rmcp ExtModel

/-! ## `Proofs/External/String.lean`: strings and `Arc` (Phase 2) -/

/-- **Spec theorem for `<str as PartialEq>::eq`**: byte-list equality, for every `Str`. -/
theorem Theorems.External.Str.Insts.CoreCmpPartialEqStr.eq_spec (self : Str) (other : Str) :
    Str.Insts.CoreCmpPartialEqStr.eq self other ⦃ (result : Bool) =>
      (result = true ↔ self.val = other.val) ⦄ :=
  _root_.Str.Insts.CoreCmpPartialEqStr.eq_spec self other

/--
info: 'Theorems.External.Str.Insts.CoreCmpPartialEqStr.eq_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.Str.Insts.CoreCmpPartialEqStr.eq_spec

/-- **Spec theorem for `<String as Deref<Target = str>>::deref`**: the UTF-8 bytes of the
string. The precondition holds for every Rust `String` (at most `isize::MAX` bytes); see
`deref_fail`. -/
theorem Theorems.External.alloc.string.String.Insts.CoreOpsDerefDerefStr.deref_spec
    (self : String) (h : self.utf8ByteSize ≤ Usize.max) :
    alloc.string.String.Insts.CoreOpsDerefDerefStr.deref self ⦃ (result : Str) =>
      result.val = utf8 self ⦄ :=
  _root_.alloc.string.String.Insts.CoreOpsDerefDerefStr.deref_spec self h

/--
info: 'Theorems.External.alloc.string.String.Insts.CoreOpsDerefDerefStr.deref_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.alloc.string.String.Insts.CoreOpsDerefDerefStr.deref_spec

/-- `<String as Deref>::deref` on a Lean `String` longer than `Usize.max` bytes (no Rust
`String` is): `fail maximumSizeExceeded`, as for the Phase 1 model of `String::as_bytes`
(`alloc.string.String.as_bytes_fail`). With `deref_spec` this covers every `String`. -/
theorem Theorems.External.alloc.string.String.Insts.CoreOpsDerefDerefStr.deref_fail
    (self : String) (h : Usize.max < self.utf8ByteSize) :
    alloc.string.String.Insts.CoreOpsDerefDerefStr.deref self = fail Error.maximumSizeExceeded :=
  _root_.alloc.string.String.Insts.CoreOpsDerefDerefStr.deref_fail self h

/--
info: 'Theorems.External.alloc.string.String.Insts.CoreOpsDerefDerefStr.deref_fail' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.alloc.string.String.Insts.CoreOpsDerefDerefStr.deref_fail

/-- **Spec theorem for `<Arc<T> as Deref>::deref`**: the shared value, for every `T` and every
allocator type `A`. -/
theorem Theorems.External.alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref_spec {T : Type} (A : Type)
    (self : alloc.sync.Arc T) :
    alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref A self ⦃ (result : T) =>
      result = self.data ⦄ :=
  _root_.alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref_spec A self

/--
info: 'Theorems.External.alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref_spec

/-- `<Arc<T> as PartialEq>::eq` is the equality of the instance of `T` on the shared values,
for every instance, including its failure. -/
theorem Theorems.External.alloc.sync.Arc.Insts.CoreCmpPartialEqArc.eq_eq {T : Type} (A : Type)
    (corecmpPartialEqInst : core.cmp.PartialEq T T) (self : alloc.sync.Arc T)
    (other : alloc.sync.Arc T) :
    alloc.sync.Arc.Insts.CoreCmpPartialEqArc.eq A corecmpPartialEqInst self other =
      corecmpPartialEqInst.eq self.data other.data :=
  _root_.alloc.sync.Arc.Insts.CoreCmpPartialEqArc.eq_eq A corecmpPartialEqInst self other

/--
info: 'Theorems.External.alloc.sync.Arc.Insts.CoreCmpPartialEqArc.eq_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.alloc.sync.Arc.Insts.CoreCmpPartialEqArc.eq_eq

/-- **Spec theorem for `<Arc<str> as PartialEq>::eq`** at the instance of the translation:
equality of the bytes of the shared strings (plan Section 17, M07: "compares `Arc<str>` by
contents"). -/
theorem Theorems.External.alloc.sync.Arc.Insts.CoreCmpPartialEqArc.eq_str_spec (A : Type)
    (self : alloc.sync.Arc Str) (other : alloc.sync.Arc Str) :
    alloc.sync.Arc.Insts.CoreCmpPartialEqArc.eq A Str.Insts.CoreCmpPartialEqStr self other
      ⦃ (result : Bool) => (result = true ↔ self.data.val = other.data.val) ⦄ :=
  _root_.alloc.sync.Arc.Insts.CoreCmpPartialEqArc.eq_str_spec A self other

/--
info: 'Theorems.External.alloc.sync.Arc.Insts.CoreCmpPartialEqArc.eq_str_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.alloc.sync.Arc.Insts.CoreCmpPartialEqArc.eq_str_spec

/-! ## `Proofs/External/Option.lean`: `Option` and `Result` (Phase 2) -/

/-- `Option::or_else` on `Some x`: `Some x`; the closure is not called. -/
theorem Theorems.External.core.option.Option.or_else_some {T : Type} {F : Type}
    (opsfunctionFnOnceFTupleOptionInst : core.ops.function.FnOnce F Unit (Option T))
    (x : T) (f : F) :
    core.option.Option.or_else opsfunctionFnOnceFTupleOptionInst (some x) f = ok (some x) :=
  _root_.core.option.Option.or_else_some opsfunctionFnOnceFTupleOptionInst x f

/--
info: 'Theorems.External.core.option.Option.or_else_some' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.core.option.Option.or_else_some

/-- `Option::or_else` on `None`: the result of the closure, through its `FnOnce` instance,
including its failure (same model and Rust lines as `or_else_some`). With `or_else_some` this
covers every case. -/
theorem Theorems.External.core.option.Option.or_else_none {T : Type} {F : Type}
    (opsfunctionFnOnceFTupleOptionInst : core.ops.function.FnOnce F Unit (Option T))
    (f : F) :
    core.option.Option.or_else opsfunctionFnOnceFTupleOptionInst none f =
      opsfunctionFnOnceFTupleOptionInst.call_once f () :=
  _root_.core.option.Option.or_else_none opsfunctionFnOnceFTupleOptionInst f

/--
info: 'Theorems.External.core.option.Option.or_else_none' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.core.option.Option.or_else_none

/-- `<Option<T> as PartialEq>::eq`, for every instance of `T`: `Some l == Some r` is `l == r`
through the instance (including its failure); a `Some` and a `None` are unequal; two `None`
are equal. -/
theorem Theorems.External.core.option.Option.Insts.CoreCmpPartialEqOption.eq_eq {T : Type}
    (cmpPartialEqInst : core.cmp.PartialEq T T) (l r : T) :
    core.option.Option.Insts.CoreCmpPartialEqOption.eq cmpPartialEqInst (some l) (some r) =
        cmpPartialEqInst.eq l r ∧
      core.option.Option.Insts.CoreCmpPartialEqOption.eq cmpPartialEqInst (some l) none =
        ok false ∧
      core.option.Option.Insts.CoreCmpPartialEqOption.eq cmpPartialEqInst none (some r) =
        ok false ∧
      core.option.Option.Insts.CoreCmpPartialEqOption.eq cmpPartialEqInst none none =
        ok true :=
  _root_.core.option.Option.Insts.CoreCmpPartialEqOption.eq_eq cmpPartialEqInst l r

/--
info: 'Theorems.External.core.option.Option.Insts.CoreCmpPartialEqOption.eq_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.core.option.Option.Insts.CoreCmpPartialEqOption.eq_eq

/-- **Spec theorem for `<Option<T> as PartialEq>::eq`** for an instance that decides equality
on the values compared: the result is `true` exactly when the two options are equal. The
hypothesis is needed only when both are `Some` (same model and Rust lines as `eq_eq`). -/
theorem Theorems.External.core.option.Option.Insts.CoreCmpPartialEqOption.eq_spec {T : Type}
    (cmpPartialEqInst : core.cmp.PartialEq T T) (self : Option T) (other : Option T)
    (h_inst : ∀ l r, self = some l → other = some r →
      cmpPartialEqInst.eq l r ⦃ (b : Bool) => (b = true ↔ l = r) ⦄) :
    core.option.Option.Insts.CoreCmpPartialEqOption.eq cmpPartialEqInst self other
      ⦃ (result : Bool) => (result = true ↔ self = other) ⦄ :=
  _root_.core.option.Option.Insts.CoreCmpPartialEqOption.eq_spec cmpPartialEqInst self other h_inst

/--
info: 'Theorems.External.core.option.Option.Insts.CoreCmpPartialEqOption.eq_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.core.option.Option.Insts.CoreCmpPartialEqOption.eq_spec

/-- **Spec theorem for `<Option<i64> as PartialEq>::eq`** at the instance of the translation
(`core.cmp.PartialEqI64` of the Aeneas library, value equality): option equality. -/
theorem Theorems.External.core.option.Option.Insts.CoreCmpPartialEqOption.eq_i64_spec
    (self : Option I64) (other : Option I64) :
    core.option.Option.Insts.CoreCmpPartialEqOption.eq core.cmp.PartialEqI64 self other
      ⦃ (result : Bool) => (result = true ↔ self = other) ⦄ :=
  _root_.core.option.Option.Insts.CoreCmpPartialEqOption.eq_i64_spec self other

/--
info: 'Theorems.External.core.option.Option.Insts.CoreCmpPartialEqOption.eq_i64_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.core.option.Option.Insts.CoreCmpPartialEqOption.eq_i64_spec

/-- **Spec theorem for `Result::ok`**: `Ok x ↦ Some x`, `Err _ ↦ None`; never fails. -/
theorem Theorems.External.core.result.Result.ok_spec
    {T : Type} {E : Type} (self : core.result.Result T E) :
    core.result.Result.ok self ⦃ (result : Option T) =>
      result = match self with
        | core.result.Result.Ok x => some x
        | core.result.Result.Err _ => none ⦄ :=
  _root_.core.result.Result.ok_spec self

/--
info: 'Theorems.External.core.result.Result.ok_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.core.result.Result.ok_spec

/-! ## `Proofs/External/Std.lean`: slices and ranges (Phase 2) -/

/-- **Spec theorem for `slice::first`**: the first element, `None` for the empty slice. -/
theorem Theorems.External.core.slice.Slice.first_spec {T : Type} (self : Slice T) :
    core.slice.Slice.first self ⦃ (result : Option T) => result = self.val.head? ⦄ :=
  _root_.core.slice.Slice.first_spec self

/--
info: 'Theorems.External.core.slice.Slice.first_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.core.slice.Slice.first_spec

/-- **Spec theorem for `<[T; N] as SlicePattern>::as_slice`**: the same elements. -/
theorem Theorems.External.Array.Insts.CoreSliceSlicePattern.as_slice_spec {T : Type} {N : Usize}
    (self : Array T N) :
    Array.Insts.CoreSliceSlicePattern.as_slice self ⦃ (result : Slice T) =>
      result.val = self.val ⦄ :=
  _root_.Array.Insts.CoreSliceSlicePattern.as_slice_spec self

/--
info: 'Theorems.External.Array.Insts.CoreSliceSlicePattern.as_slice_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.Array.Insts.CoreSliceSlicePattern.as_slice_spec

/-- **Spec theorem for `[T] == [U; N]`**, for an instance whose `ne` decides the negation of a
relation `R` on the elements compared: the result is `true` exactly when the slice and the
array have the same length and are related element-wise (`List.Forall₂ R`; equal lengths
follow, so the slice has length `N`). -/
theorem Theorems.External.Slice.Insts.CoreCmpPartialEqArray.eq_spec
    {T : Type} {U : Type} {N : Usize}
    (cmpPartialEqInst : core.cmp.PartialEq T U) (self : Slice T) (other : Array U N)
    (R : T → U → Prop)
    (h_ne : ∀ a ∈ self.val, ∀ b ∈ other.val,
      cmpPartialEqInst.ne a b ⦃ (d : Bool) => (d = true ↔ ¬ R a b) ⦄) :
    Slice.Insts.CoreCmpPartialEqArray.eq cmpPartialEqInst self other ⦃ (result : Bool) =>
      (result = true ↔ List.Forall₂ R self.val other.val) ⦄ :=
  _root_.Slice.Insts.CoreCmpPartialEqArray.eq_spec cmpPartialEqInst self other R h_ne

/--
info: 'Theorems.External.Slice.Insts.CoreCmpPartialEqArray.eq_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.Slice.Insts.CoreCmpPartialEqArray.eq_spec

/-- **Spec theorem for `[u16] == [u16; N]`** at the instance of the translation
(`core.cmp.PartialEqU16`): list equality of the elements (in particular `false` when the
lengths differ). Same model and Rust lines as `eq_spec`. -/
theorem Theorems.External.Slice.Insts.CoreCmpPartialEqArray.eq_u16_spec {N : Usize}
    (self : Slice U16) (other : Array U16 N) :
    Slice.Insts.CoreCmpPartialEqArray.eq core.cmp.PartialEqU16 self other ⦃ (result : Bool) =>
      (result = true ↔ self.val = other.val) ⦄ :=
  _root_.Slice.Insts.CoreCmpPartialEqArray.eq_u16_spec self other

/--
info: 'Theorems.External.Slice.Insts.CoreCmpPartialEqArray.eq_u16_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.Slice.Insts.CoreCmpPartialEqArray.eq_u16_spec

/-- **Spec theorem for `slice::strip_suffix`**, for every pattern instance and every element
instance whose `ne` decides the negation of a relation `R` on the elements compared: let `suf`
be the pattern as a slice; the result is `Some head` exactly when `self` is `head` followed by
a list related element-wise to `suf`, and `None` when no such split exists. The `head` is
unique (`Forall₂` fixes the length of the tail). -/
theorem Theorems.External.core.slice.Slice.strip_suffix_spec {T : Type} {P : Type}
    (SlicePatternInst : core.slice.SlicePattern P T) (cmpPartialEqInst : core.cmp.PartialEq T T)
    (self : Slice T) (suffix : P) (suf : Slice T) (R : T → T → Prop)
    (h_suf : SlicePatternInst.as_slice suffix = ok suf)
    (h_ne : ∀ a ∈ self.val, ∀ b ∈ suf.val,
      cmpPartialEqInst.ne a b ⦃ (d : Bool) => (d = true ↔ ¬ R a b) ⦄) :
    core.slice.Slice.strip_suffix SlicePatternInst cmpPartialEqInst self suffix
      ⦃ (result : Option (Slice T)) =>
        match result with
        | some head => ∃ tail, self.val = head.val ++ tail ∧ List.Forall₂ R tail suf.val
        | none =>
          ¬ ∃ head tail, self.val = head ++ tail ∧ List.Forall₂ R tail suf.val ⦄ :=
  _root_.core.slice.Slice.strip_suffix_spec SlicePatternInst cmpPartialEqInst self suffix suf R
    h_suf h_ne

/--
info: 'Theorems.External.core.slice.Slice.strip_suffix_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.core.slice.Slice.strip_suffix_spec

/-- `slice::strip_suffix` with a pattern whose `as_slice` does not return: its failure or
divergence propagates (same model and Rust lines as `strip_suffix_spec`; `as_slice` is the
first call). With `strip_suffix_spec` this covers every result of `as_slice`. -/
theorem Theorems.External.core.slice.Slice.strip_suffix_fail {T : Type} {P : Type}
    (SlicePatternInst : core.slice.SlicePattern P T) (cmpPartialEqInst : core.cmp.PartialEq T T)
    (self : Slice T) (suffix : P) :
    (∀ e, SlicePatternInst.as_slice suffix = fail e →
      core.slice.Slice.strip_suffix SlicePatternInst cmpPartialEqInst self suffix = fail e) ∧
    (SlicePatternInst.as_slice suffix = div →
      core.slice.Slice.strip_suffix SlicePatternInst cmpPartialEqInst self suffix = div) :=
  _root_.core.slice.Slice.strip_suffix_fail SlicePatternInst cmpPartialEqInst self suffix

/--
info: 'Theorems.External.core.slice.Slice.strip_suffix_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.core.slice.Slice.strip_suffix_fail

/-- **Spec theorem for `[u8]::strip_suffix(&[c])`** at the instances of the translation (the
pattern `[u8; 1]`, `core.cmp.PartialEqU8`): `Some head` with `self = head ++ [c]` when the last
byte is `c`, otherwise `None` (in particular for the empty slice). Same model and Rust lines as
`strip_suffix_spec`. -/
theorem Theorems.External.core.slice.Slice.strip_suffix_u8_single_spec (self : Slice U8) (c : U8) :
    core.slice.Slice.strip_suffix (Array.Insts.CoreSliceSlicePattern U8 1#usize)
        core.cmp.PartialEqU8 self (Array.make 1#usize [c])
      ⦃ (result : Option (Slice U8)) =>
        match result with
        | some head => self.val = head.val ++ [c]
        | none => self.val.getLast? ≠ some c ⦄ :=
  _root_.core.slice.Slice.strip_suffix_u8_single_spec self c

/--
info: 'Theorems.External.core.slice.Slice.strip_suffix_u8_single_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.core.slice.Slice.strip_suffix_u8_single_spec

/-- **Spec theorem for `RangeInclusive<u8>::contains`** at the instances of the translation
(`core.cmp.PartialOrdU8`): `start ≤ item ≤ end` for a range that is not exhausted,
`start ≤ item < start` (so never) for an exhausted one; never fails. Rust:
`core/src/ops/range.rs` lines 539–545, 886–900 and 1142–1157 (exhausted end bound
`Excluded(start)`). -/
theorem Theorems.External.core.ops.range.RangeInclusive.contains_u8_spec
    (self : core.ops.range.RangeInclusive U8) (item : U8) :
    core.ops.range.RangeInclusive.contains core.cmp.PartialOrdU8 core.cmp.PartialOrdU8
        core.cmp.PartialOrdU8 self item ⦃ (result : Bool) =>
      (result = true ↔ self.start.val ≤ item.val ∧
        (if self.exhausted then item.val < self.start.val
         else item.val ≤ self.«end».val)) ⦄ :=
  _root_.core.ops.range.RangeInclusive.contains_u8_spec self item

/--
info: 'Theorems.External.core.ops.range.RangeInclusive.contains_u8_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.core.ops.range.RangeInclusive.contains_u8_spec

/-- **`(a..=b).contains(&x)` for `u8`**: `a ≤ x ≤ b`. The range built by
`RangeInclusive::new` (Aeneas library, `exhausted = false`) is not exhausted, so this is
`contains_u8_spec` for a fresh range. -/
theorem Theorems.External.core.ops.range.RangeInclusive.new_contains_u8_spec (a b item : U8) :
    (do
      let r ← core.ops.range.RangeInclusive.new a b
      core.ops.range.RangeInclusive.contains core.cmp.PartialOrdU8 core.cmp.PartialOrdU8
        core.cmp.PartialOrdU8 r item) ⦃ (result : Bool) =>
      (result = true ↔ a.val ≤ item.val ∧ item.val ≤ b.val) ⦄ :=
  _root_.core.ops.range.RangeInclusive.new_contains_u8_spec a b item

/--
info: 'Theorems.External.core.ops.range.RangeInclusive.new_contains_u8_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.core.ops.range.RangeInclusive.new_contains_u8_spec

/-- `RangeInclusive::contains`, for every instance: `start <= item` is evaluated first; if it
fails or diverges that propagates, if it is `false` the result is `false` without a second
call, and if it is `true` the result is `item < start` (exhausted) or `item <= end` (not
exhausted), including its failure. The four cases cover every result of the first call (same
model and Rust lines as `contains_u8_spec`; `&&` short-circuits; the exhausted end bound is
`Excluded(start)`, `core/src/ops/range.rs` lines 1142–1157). -/
theorem Theorems.External.core.ops.range.RangeInclusive.contains_eq_match_le {Idx : Type} {U : Type}
    (cmpPartialOrdInst : core.cmp.PartialOrd Idx Idx)
    (cmpPartialOrdInst1 : core.cmp.PartialOrd Idx U)
    (cmpPartialOrdInst2 : core.cmp.PartialOrd U Idx)
    (self : core.ops.range.RangeInclusive Idx) (item : U) :
    (∀ e, cmpPartialOrdInst1.le self.start item = fail e →
      core.ops.range.RangeInclusive.contains cmpPartialOrdInst cmpPartialOrdInst1
        cmpPartialOrdInst2 self item = fail e) ∧
    (cmpPartialOrdInst1.le self.start item = div →
      core.ops.range.RangeInclusive.contains cmpPartialOrdInst cmpPartialOrdInst1
        cmpPartialOrdInst2 self item = div) ∧
    (cmpPartialOrdInst1.le self.start item = ok false →
      core.ops.range.RangeInclusive.contains cmpPartialOrdInst cmpPartialOrdInst1
        cmpPartialOrdInst2 self item = ok false) ∧
    (cmpPartialOrdInst1.le self.start item = ok true →
      core.ops.range.RangeInclusive.contains cmpPartialOrdInst cmpPartialOrdInst1
        cmpPartialOrdInst2 self item =
        if self.exhausted then cmpPartialOrdInst2.lt item self.start
        else cmpPartialOrdInst2.le item self.«end») :=
  _root_.core.ops.range.RangeInclusive.contains_eq_match_le cmpPartialOrdInst cmpPartialOrdInst1
    cmpPartialOrdInst2 self item

/--
info: 'Theorems.External.core.ops.range.RangeInclusive.contains_eq_match_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.core.ops.range.RangeInclusive.contains_eq_match_le

/-! ## `Proofs/External/IntParse.lean`: `str::parse` and `i64::from_str` (Phase 2) -/

/-- **`i64::from_str` on the empty input**: `Err` with kind `Empty`. -/
theorem Theorems.External.I64.Insts.CoreStrTraitsFromStrParseIntError.from_str_empty
    (src : Str) (h : src.val = []) :
    I64.Insts.CoreStrTraitsFromStrParseIntError.from_str src =
      ok (core.result.Result.Err { kind := ExtModel.IntErrorKind.Empty }) :=
  _root_.I64.Insts.CoreStrTraitsFromStrParseIntError.from_str_empty src h

/--
info: 'Theorems.External.I64.Insts.CoreStrTraitsFromStrParseIntError.from_str_empty' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.I64.Insts.CoreStrTraitsFromStrParseIntError.from_str_empty

/-- **`i64::from_str` on a lone sign** (`"+"` or `"-"`): `Err` with kind `InvalidDigit`. -/
theorem Theorems.External.I64.Insts.CoreStrTraitsFromStrParseIntError.from_str_lone_sign
    (src : Str) (c : U8) (h : src.val = [c]) (hc : c.val = 43 ∨ c.val = 45) :
    I64.Insts.CoreStrTraitsFromStrParseIntError.from_str src =
      ok (core.result.Result.Err { kind := ExtModel.IntErrorKind.InvalidDigit }) :=
  _root_.I64.Insts.CoreStrTraitsFromStrParseIntError.from_str_lone_sign src c h hc

/--
info: 'Theorems.External.I64.Insts.CoreStrTraitsFromStrParseIntError.from_str_lone_sign' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.I64.Insts.CoreStrTraitsFromStrParseIntError.from_str_lone_sign

/-- **Spec theorem for `i64::from_str`** on every other input: `src = sign ++ body`, with `sign`
empty, `+` or `-`, `body` nonempty, and `body` not starting with `+` or `-` when `sign` is
empty (so that the split is the one Rust makes). Let `neg` say that the sign is `-`, `d` the
longest prefix of `body` made of decimal digits and `v` its value. Then, never failing: `Err`
with kind `PosOverflow` (no `-`) or `NegOverflow` (`-`) if `v` is out of range for the sign;
otherwise `Err` with kind `InvalidDigit` if `body` has a byte that is not a digit; otherwise
`Ok n` with `n = v` or `n = -v`. -/
theorem Theorems.External.I64.Insts.CoreStrTraitsFromStrParseIntError.from_str_spec
    (src : Str) (sign body : List U8)
    (h_src : src.val = sign ++ body)
    (h_sign : sign = [] ∨ sign = [43#u8] ∨ sign = [45#u8])
    (h_body : body ≠ [])
    (h_unsigned : sign = [] → ∀ c ∈ body.head?, c.val ≠ 43 ∧ c.val ≠ 45) :
    I64.Insts.CoreStrTraitsFromStrParseIntError.from_str src
      ⦃ (result : core.result.Result I64 core.num.error.ParseIntError) =>
        let neg : Prop := sign = [45#u8]
        let d := body.takeWhile (fun c => decide (48 ≤ c.val ∧ c.val ≤ 57))
        let v : Nat := Nat.ofDigits 10 (d.map (fun c => c.val - 48)).reverse
        let overflow : Prop := (neg ∧ 2 ^ 63 < v) ∨ (¬ neg ∧ 2 ^ 63 ≤ v)
        match result with
        | core.result.Result.Ok n =>
          ¬ overflow ∧ d = body ∧ n.val = (if neg then -(v : Int) else (v : Int))
        | core.result.Result.Err e =>
          (overflow ∧ (neg → e.kind = ExtModel.IntErrorKind.NegOverflow) ∧
              (¬ neg → e.kind = ExtModel.IntErrorKind.PosOverflow)) ∨
            (¬ overflow ∧ d ≠ body ∧ e.kind = ExtModel.IntErrorKind.InvalidDigit) ⦄ :=
  _root_.I64.Insts.CoreStrTraitsFromStrParseIntError.from_str_spec src sign body h_src h_sign h_body
    h_unsigned

/--
info: 'Theorems.External.I64.Insts.CoreStrTraitsFromStrParseIntError.from_str_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.I64.Insts.CoreStrTraitsFromStrParseIntError.from_str_spec

/-- **Round trip of `i64::from_str`**: parsing the decimal rendering of `n` (Rust's
`n.to_string()`: `-` for a negative value, then the digits of `|n|` without leading zeros;
here `toString` of the `Int` value) gives `n`. -/
theorem Theorems.External.I64.Insts.CoreStrTraitsFromStrParseIntError.from_str_toString
    (n : I64) (src : Str) (h_src : src.val = utf8 (toString n.val)) :
    I64.Insts.CoreStrTraitsFromStrParseIntError.from_str src =
      ok (core.result.Result.Ok n) :=
  _root_.I64.Insts.CoreStrTraitsFromStrParseIntError.from_str_toString n src h_src

/--
info: 'Theorems.External.I64.Insts.CoreStrTraitsFromStrParseIntError.from_str_toString' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.I64.Insts.CoreStrTraitsFromStrParseIntError.from_str_toString

/-- **Round trip with an explicit sign and leading zeros**: `sign`, then `k` zeros, then the
decimal digits of `|n|` parse to `n`, where `sign` is empty or `+` for `n ≥ 0` and `-` for
`n ≤ 0` (so `"-0"`, `"+007"` and `"-0042"` are accepted). Same model and Rust lines as
`from_str_spec`. -/
theorem Theorems.External.I64.Insts.CoreStrTraitsFromStrParseIntError.from_str_signed_toString
    (n : I64) (src : Str) (sign : List U8) (k : Nat)
    (h_sign : (sign = [] ∧ 0 ≤ n.val) ∨ (sign = [43#u8] ∧ 0 ≤ n.val) ∨
      (sign = [45#u8] ∧ n.val ≤ 0))
    (h_src : src.val = sign ++ List.replicate k 48#u8 ++ utf8 (toString n.val.natAbs)) :
    I64.Insts.CoreStrTraitsFromStrParseIntError.from_str src =
      ok (core.result.Result.Ok n) :=
  _root_.I64.Insts.CoreStrTraitsFromStrParseIntError.from_str_signed_toString n src sign k h_sign
    h_src

/--
info: 'Theorems.External.I64.Insts.CoreStrTraitsFromStrParseIntError.from_str_signed_toString' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.I64.Insts.CoreStrTraitsFromStrParseIntError.from_str_signed_toString

/-- `str::parse` calls `from_str` of the `FromStr` instance, including its failure. -/
theorem Theorems.External.core.str.Str.parse_eq {F : Type} {Clause0_Err : Type}
    (traitsFromStrInst : core.str.traits.FromStr F Clause0_Err) (self : Str) :
    core.str.Str.parse traitsFromStrInst self = traitsFromStrInst.from_str self :=
  _root_.core.str.Str.parse_eq traitsFromStrInst self

/--
info: 'Theorems.External.core.str.Str.parse_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.core.str.Str.parse_eq

/-- **S27 deferred law** (signed off 2026-11-24, S24/S25 spec cycle; signed-off statements are the
ones in this project file): `i64::from_str` never fails, and returns
`Ok n` exactly when `Defs.parseI64` accepts the bytes of `src`, with `n.val` its value;
otherwise `Err _` (error kind unconstrained). M06 uses it. -/
theorem Theorems.External.I64.Insts.CoreStrTraitsFromStrParseIntError.from_str_eq_parseI64
    (src : Str) :
    I64.Insts.CoreStrTraitsFromStrParseIntError.from_str src
      ⦃ (result : core.result.Result I64 core.num.error.ParseIntError) =>
        (match result with
         | .Ok n => some n.val
         | .Err _ => none) = Defs.parseI64 src.val ⦄ :=
  _root_.I64.Insts.CoreStrTraitsFromStrParseIntError.from_str_eq_parseI64 src

/--
info: 'Theorems.External.I64.Insts.CoreStrTraitsFromStrParseIntError.from_str_eq_parseI64' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.I64.Insts.CoreStrTraitsFromStrParseIntError.from_str_eq_parseI64

/-! ## `Proofs/External/Net.lean`: IP addresses (Phase 2) -/

/-- Every `Ipv4Addr` has four octets (the model's `Array U8 4#usize`, Rust `octets: [u8; 4]`,
`core/src/net/ip_addr.rs` lines 74–76). -/
theorem Theorems.External.core.net.ip_addr.Ipv4Addr.exists_octets (a : core.net.ip_addr.Ipv4Addr) :
    ∃ o0 o1 o2 o3 : U8, a.addrOctets.val = [o0, o1, o2, o3] :=
  _root_.core.net.ip_addr.Ipv4Addr.exists_octets a

/--
info: 'Theorems.External.core.net.ip_addr.Ipv4Addr.exists_octets' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.core.net.ip_addr.Ipv4Addr.exists_octets

/-- **Spec theorem for `Ipv4Addr::octets`**: the four octets, most significant first. -/
theorem Theorems.External.core.net.ip_addr.Ipv4Addr.octets_spec (self : core.net.ip_addr.Ipv4Addr) :
    core.net.ip_addr.Ipv4Addr.octets self ⦃ (result : Array U8 4#usize) =>
      result = self.addrOctets ⦄ :=
  _root_.core.net.ip_addr.Ipv4Addr.octets_spec self

/--
info: 'Theorems.External.core.net.ip_addr.Ipv4Addr.octets_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.core.net.ip_addr.Ipv4Addr.octets_spec

/-- **Spec theorem for `Ipv4Addr::is_private`**: `10.0.0.0/8`, `172.16.0.0/12` or
`192.168.0.0/16` (RFC 1918). -/
theorem Theorems.External.core.net.ip_addr.Ipv4Addr.is_private_spec
    (self : core.net.ip_addr.Ipv4Addr)
    (o0 o1 o2 o3 : U8) (h : self.addrOctets.val = [o0, o1, o2, o3]) :
    core.net.ip_addr.Ipv4Addr.is_private self ⦃ (result : Bool) =>
      (result = true ↔ o0.val = 10 ∨ (o0.val = 172 ∧ o1.val / 16 = 1) ∨
        (o0.val = 192 ∧ o1.val = 168)) ⦄ :=
  _root_.core.net.ip_addr.Ipv4Addr.is_private_spec self o0 o1 o2 o3 h

/--
info: 'Theorems.External.core.net.ip_addr.Ipv4Addr.is_private_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.core.net.ip_addr.Ipv4Addr.is_private_spec

/-- **Spec theorem for `Ipv4Addr::is_loopback`**: `127.0.0.0/8`. -/
theorem Theorems.External.core.net.ip_addr.Ipv4Addr.is_loopback_spec
    (self : core.net.ip_addr.Ipv4Addr)
    (o0 o1 o2 o3 : U8) (h : self.addrOctets.val = [o0, o1, o2, o3]) :
    core.net.ip_addr.Ipv4Addr.is_loopback self ⦃ (result : Bool) =>
      (result = true ↔ o0.val = 127) ⦄ :=
  _root_.core.net.ip_addr.Ipv4Addr.is_loopback_spec self o0 o1 o2 o3 h

/--
info: 'Theorems.External.core.net.ip_addr.Ipv4Addr.is_loopback_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.core.net.ip_addr.Ipv4Addr.is_loopback_spec

/-- **Spec theorem for `Ipv4Addr::is_link_local`**: `169.254.0.0/16` (RFC 3927). -/
theorem Theorems.External.core.net.ip_addr.Ipv4Addr.is_link_local_spec
    (self : core.net.ip_addr.Ipv4Addr)
    (o0 o1 o2 o3 : U8) (h : self.addrOctets.val = [o0, o1, o2, o3]) :
    core.net.ip_addr.Ipv4Addr.is_link_local self ⦃ (result : Bool) =>
      (result = true ↔ o0.val = 169 ∧ o1.val = 254) ⦄ :=
  _root_.core.net.ip_addr.Ipv4Addr.is_link_local_spec self o0 o1 o2 o3 h

/--
info: 'Theorems.External.core.net.ip_addr.Ipv4Addr.is_link_local_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.core.net.ip_addr.Ipv4Addr.is_link_local_spec

/-- **Spec theorem for `Ipv4Addr::is_broadcast`**: exactly `255.255.255.255`. -/
theorem Theorems.External.core.net.ip_addr.Ipv4Addr.is_broadcast_spec
    (self : core.net.ip_addr.Ipv4Addr)
    (o0 o1 o2 o3 : U8) (h : self.addrOctets.val = [o0, o1, o2, o3]) :
    core.net.ip_addr.Ipv4Addr.is_broadcast self ⦃ (result : Bool) =>
      (result = true ↔ o0.val = 255 ∧ o1.val = 255 ∧ o2.val = 255 ∧ o3.val = 255) ⦄ :=
  _root_.core.net.ip_addr.Ipv4Addr.is_broadcast_spec self o0 o1 o2 o3 h

/--
info: 'Theorems.External.core.net.ip_addr.Ipv4Addr.is_broadcast_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.core.net.ip_addr.Ipv4Addr.is_broadcast_spec

/-- **Spec theorem for `Ipv4Addr::is_unspecified`**: exactly `0.0.0.0`. -/
theorem Theorems.External.core.net.ip_addr.Ipv4Addr.is_unspecified_spec
    (self : core.net.ip_addr.Ipv4Addr)
    (o0 o1 o2 o3 : U8) (h : self.addrOctets.val = [o0, o1, o2, o3]) :
    core.net.ip_addr.Ipv4Addr.is_unspecified self ⦃ (result : Bool) =>
      (result = true ↔ o0.val = 0 ∧ o1.val = 0 ∧ o2.val = 0 ∧ o3.val = 0) ⦄ :=
  _root_.core.net.ip_addr.Ipv4Addr.is_unspecified_spec self o0 o1 o2 o3 h

/--
info: 'Theorems.External.core.net.ip_addr.Ipv4Addr.is_unspecified_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.core.net.ip_addr.Ipv4Addr.is_unspecified_spec

/-- **Spec theorem for `Ipv4Addr::is_multicast`**: `224.0.0.0/4` (first four bits `1110`). -/
theorem Theorems.External.core.net.ip_addr.Ipv4Addr.is_multicast_spec
    (self : core.net.ip_addr.Ipv4Addr)
    (o0 o1 o2 o3 : U8) (h : self.addrOctets.val = [o0, o1, o2, o3]) :
    core.net.ip_addr.Ipv4Addr.is_multicast self ⦃ (result : Bool) =>
      (result = true ↔ o0.val / 16 = 14) ⦄ :=
  _root_.core.net.ip_addr.Ipv4Addr.is_multicast_spec self o0 o1 o2 o3 h

/--
info: 'Theorems.External.core.net.ip_addr.Ipv4Addr.is_multicast_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.core.net.ip_addr.Ipv4Addr.is_multicast_spec

/-- **Spec theorem for `<Ipv4Addr as From<u32>>::from`**: the big-endian bytes of `ip`, most
significant first; reading them back as a big-endian number gives `ip`. -/
theorem Theorems.External.core.net.ip_addr.Ipv4Addr.Insts.CoreConvertFromU32.from_spec (ip : U32) :
    core.net.ip_addr.Ipv4Addr.Insts.CoreConvertFromU32.from ip
      ⦃ (result : core.net.ip_addr.Ipv4Addr) =>
        result.addrOctets.val.map (fun o => o.val) =
          [ip.val / 2 ^ 24, ip.val / 2 ^ 16 % 256, ip.val / 2 ^ 8 % 256, ip.val % 256] ∧
        ∀ o0 o1 o2 o3 : U8, result.addrOctets.val = [o0, o1, o2, o3] →
          o0.val * 2 ^ 24 + o1.val * 2 ^ 16 + o2.val * 2 ^ 8 + o3.val = ip.val ⦄ :=
  _root_.core.net.ip_addr.Ipv4Addr.Insts.CoreConvertFromU32.from_spec ip

/--
info: 'Theorems.External.core.net.ip_addr.Ipv4Addr.Insts.CoreConvertFromU32.from_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.core.net.ip_addr.Ipv4Addr.Insts.CoreConvertFromU32.from_spec

/-- **The IPv4 address of two segments**: for `ip = g · 2^16 + h` (the value of
`(u32::from(g) << 16) | u32::from(h)` in A01), the octets are the high and low bytes of `g`,
then of `h`; so an address embedded in the last 32 bits of an IPv6 address has the octets of
those bits. Same model and Rust lines as `from_spec`. -/
theorem Theorems.External.core.net.ip_addr.Ipv4Addr.Insts.CoreConvertFromU32.from_u32_segments
    (ip : U32) (g h : U16) (h_ip : ip.val = g.val * 2 ^ 16 + h.val) :
    core.net.ip_addr.Ipv4Addr.Insts.CoreConvertFromU32.from ip
      ⦃ (result : core.net.ip_addr.Ipv4Addr) =>
        result.addrOctets.val.map (fun o => o.val) =
          [g.val / 256, g.val % 256, h.val / 256, h.val % 256] ⦄ :=
  _root_.core.net.ip_addr.Ipv4Addr.Insts.CoreConvertFromU32.from_u32_segments ip g h h_ip

/--
info: 'Theorems.External.core.net.ip_addr.Ipv4Addr.Insts.CoreConvertFromU32.from_u32_segments' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.core.net.ip_addr.Ipv4Addr.Insts.CoreConvertFromU32.from_u32_segments

/-- Every `Ipv6Addr` has eight segments (the model's `Array U16 8#usize`; Rust stores 16
octets, `core/src/net/ip_addr.rs` lines 168–170, and `segments` reads them as eight
big-endian `u16`, lines 1495–1510: the stated change of representation of
`core.net.ip_addr.Ipv6Addr`). -/
theorem Theorems.External.core.net.ip_addr.Ipv6Addr.exists_segments
    (a : core.net.ip_addr.Ipv6Addr) :
    ∃ s0 s1 s2 s3 s4 s5 s6 s7 : U16,
      a.addrSegments.val = [s0, s1, s2, s3, s4, s5, s6, s7] :=
  _root_.core.net.ip_addr.Ipv6Addr.exists_segments a

/--
info: 'Theorems.External.core.net.ip_addr.Ipv6Addr.exists_segments' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.core.net.ip_addr.Ipv6Addr.exists_segments

/-- **Spec theorem for `Ipv6Addr::segments`**: the eight segments, most significant first. -/
theorem Theorems.External.core.net.ip_addr.Ipv6Addr.segments_spec
    (self : core.net.ip_addr.Ipv6Addr) :
    core.net.ip_addr.Ipv6Addr.segments self ⦃ (result : Array U16 8#usize) =>
      result = self.addrSegments ⦄ :=
  _root_.core.net.ip_addr.Ipv6Addr.segments_spec self

/--
info: 'Theorems.External.core.net.ip_addr.Ipv6Addr.segments_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.core.net.ip_addr.Ipv6Addr.segments_spec

/-- **Spec theorem for `Ipv6Addr::is_unspecified`**: exactly `::` (every segment `0`). -/
theorem Theorems.External.core.net.ip_addr.Ipv6Addr.is_unspecified_spec
    (self : core.net.ip_addr.Ipv6Addr)
    (s0 s1 s2 s3 s4 s5 s6 s7 : U16)
    (h : self.addrSegments.val = [s0, s1, s2, s3, s4, s5, s6, s7]) :
    core.net.ip_addr.Ipv6Addr.is_unspecified self ⦃ (result : Bool) =>
      (result = true ↔ s0.val = 0 ∧ s1.val = 0 ∧ s2.val = 0 ∧ s3.val = 0 ∧ s4.val = 0 ∧
        s5.val = 0 ∧ s6.val = 0 ∧ s7.val = 0) ⦄ :=
  _root_.core.net.ip_addr.Ipv6Addr.is_unspecified_spec self s0 s1 s2 s3 s4 s5 s6 s7 h

/--
info: 'Theorems.External.core.net.ip_addr.Ipv6Addr.is_unspecified_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.core.net.ip_addr.Ipv6Addr.is_unspecified_spec

/-- **Spec theorem for `Ipv6Addr::is_loopback`**: exactly `::1`. -/
theorem Theorems.External.core.net.ip_addr.Ipv6Addr.is_loopback_spec
    (self : core.net.ip_addr.Ipv6Addr)
    (s0 s1 s2 s3 s4 s5 s6 s7 : U16)
    (h : self.addrSegments.val = [s0, s1, s2, s3, s4, s5, s6, s7]) :
    core.net.ip_addr.Ipv6Addr.is_loopback self ⦃ (result : Bool) =>
      (result = true ↔ s0.val = 0 ∧ s1.val = 0 ∧ s2.val = 0 ∧ s3.val = 0 ∧ s4.val = 0 ∧
        s5.val = 0 ∧ s6.val = 0 ∧ s7.val = 1) ⦄ :=
  _root_.core.net.ip_addr.Ipv6Addr.is_loopback_spec self s0 s1 s2 s3 s4 s5 s6 s7 h

/--
info: 'Theorems.External.core.net.ip_addr.Ipv6Addr.is_loopback_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.core.net.ip_addr.Ipv6Addr.is_loopback_spec

/-- **Spec theorem for `Ipv6Addr::is_multicast`**: `ff00::/8` (first eight bits all `1`). -/
theorem Theorems.External.core.net.ip_addr.Ipv6Addr.is_multicast_spec
    (self : core.net.ip_addr.Ipv6Addr)
    (s0 s1 s2 s3 s4 s5 s6 s7 : U16)
    (h : self.addrSegments.val = [s0, s1, s2, s3, s4, s5, s6, s7]) :
    core.net.ip_addr.Ipv6Addr.is_multicast self ⦃ (result : Bool) =>
      (result = true ↔ s0.val / 256 = 255) ⦄ :=
  _root_.core.net.ip_addr.Ipv6Addr.is_multicast_spec self s0 s1 s2 s3 s4 s5 s6 s7 h

/--
info: 'Theorems.External.core.net.ip_addr.Ipv6Addr.is_multicast_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.core.net.ip_addr.Ipv6Addr.is_multicast_spec

/-! ## `Proofs/External/Auth.lean`: `str::trim` on UTF-8 bytes (A04–A10) -/

section Trim

open Defs (utf8Bytes)
open Defs.AuthMetadata

/-- **A07, the byte model of `str::trim` is the char-level trim**: on the UTF-8 bytes of a string,
`ExtModel.trimWhitespace` gives the bytes of `trimUnicodeWhitespace` (Unicode `White_Space`
removed at both ends). No premise. -/
theorem Theorems.External.trimWhitespace_utf8Bytes (s : String) :
    ExtModel.trimWhitespace (utf8Bytes s) = utf8Bytes (trimUnicodeWhitespace s) :=
  Proofs.External.Auth.trimWhitespace_utf8Bytes s

/--
info: 'Theorems.External.trimWhitespace_utf8Bytes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.External.trimWhitespace_utf8Bytes

end Trim
