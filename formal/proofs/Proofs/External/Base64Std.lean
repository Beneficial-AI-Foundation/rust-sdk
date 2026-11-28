/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Rmcp.Funs
public import Proofs.External.String
public import Proofs.External.WP
public import Proofs.External.Base64

@[expose] public section

/-!
# Specs of the externals of the `mcp_headers.rs` header-value encoding (G01–G04, patch 07)

Spec theorems for the models of `formal/trusted/Rmcp/FunsExternal.lean`, section "`mcp_headers.rs`
header-value encoding": the eight `mcp_headers::prim` functions that translation patch 07 adds
(`crates/rmcp/src/transport/common/mcp_headers.rs` in the patched copy) and the three `core`
functions `char::is_ascii_alphanumeric`, `<[T]>::last` and `Option<&T>::copied` that the targets
G01–G04 reach (human decisions GD1, GD2 2026-11-27). Each external has a theorem named after it
with `_spec`; where a model can fail, a `_fail` theorem covers each failure (`wrap_sentinel_fail`,
`base64_encode_fail`, `base64_decode_fail`), and `wrap_sentinel_not_utf8` the `fail undef` of
`wrap_sentinel` off UTF-8 (named as `alloc.string.String.push_str_not_utf8`).

"Std" in the module name is the *standard* Base64 alphabet of RFC 4648 Section 4 (`+` and `/`,
with `=` padding: `base64::engine::general_purpose::STANDARD`), as opposed to the URL-safe
alphabet of `Proofs.External.Base64`; it does not refer to the Rust standard library. The three
generic `core` specs at the end (`<[T]>::last`, `Option<&T>::copied`,
`char::is_ascii_alphanumeric`) live here, not in a module of standard-library specs, because
patch 07 is the first translation that calls them.

Section "Bounds" gives the bridging lemmas from a bound on the input length to the premises of
`base64_encode_spec`, `wrap_sentinel_spec` and `base64_decode_spec`: an input of at most
`isize::MAX / 2` bytes has a padded encoding that fits in a `String` together with the 11 sentinel
bytes, and an input of at most `isize::MAX` bytes has a decode buffer of at most `isize::MAX`
bytes.

Section "Padded standard Base64" proves the laws of `ExtModel.b64StdPad` and
`ExtModel.b64StdPadDecode`, the alphabet renaming of the reviewed Base64url models `b64` and
`b64Decode` (`Proofs.External.Base64`): the round trip
`b64StdPadDecode (b64StdPad x) = some x` (`b64StdPadDecode_b64StdPad`), the decoder accepts exactly
the padded encodings (`b64StdPadDecode_eq_some_iff`), every encoded byte is visible ASCII,
`0x21`–`0x7E` (`visible_of_mem_b64StdPad`), and the encoded length is `4 ⌈n / 3⌉`
(`length_b64StdPad`, the `encoded_len` of `base64-0.23.1`); the RFC 4648 Section 10 vectors and
the strictness cases are checked by `decide`.

Section "Control and non-ASCII bytes" proves that the byte-level model of
`prim::has_control_or_non_ascii` equals Rust's char-level test on valid UTF-8
(`any_isControlOrNonAsciiByte_utf8`, GD2): a char below `U+0020` or equal to `U+007F` is one
byte with that value, a char above `U+007F` has only bytes of at least `0x80`, and a char in
`U+0020`–`U+007E` is one byte in `0x20`–`0x7E`.
-/

open Aeneas Aeneas.Std Result
open rmcp

namespace Proofs.External.Base64Std

open ExtModel Proofs.External.Byte Proofs.External.Base64 Proofs.External.Utf8

/-! ### Padded standard Base64 -/

/-- The symbols of the URL-safe alphabet. -/
theorem val_of_isSome_b64Val {c : U8} (h : (b64Val c).isSome) :
    (65 ≤ c.val ∧ c.val ≤ 90) ∨ (97 ≤ c.val ∧ c.val ≤ 122) ∨ (48 ≤ c.val ∧ c.val ≤ 57) ∨
      c.val = 45 ∨ c.val = 95 := (isSome_b64Val_iff c).1 h

/-- `stdToUrl` undoes `urlToStd` on the URL-safe symbols. -/
theorem stdToUrl_urlToStd {c : U8} (h : (b64Val c).isSome) : stdToUrl (urlToStd c) = c := by
  have := val_of_isSome_b64Val h
  unfold urlToStd stdToUrl
  split_ifs <;> simp_all [byte_val] <;> first | omega | (apply byte_eq; simp_all)

/-- `urlToStd` maps the URL-safe symbols to the standard alphabet `A`–`Z`, `a`–`z`, `0`–`9`, `+`,
`/`. -/
theorem val_urlToStd {c : U8} (h : (b64Val c).isSome) :
    (65 ≤ (urlToStd c).val ∧ (urlToStd c).val ≤ 90) ∨
      (97 ≤ (urlToStd c).val ∧ (urlToStd c).val ≤ 122) ∨
      (48 ≤ (urlToStd c).val ∧ (urlToStd c).val ≤ 57) ∨ (urlToStd c).val = 43 ∨
      (urlToStd c).val = 47 := by
  have := val_of_isSome_b64Val h
  unfold urlToStd
  split_ifs <;> first | omega | (simp only [byte_val]; omega) | simp_all [byte_val]

/-- `urlToStd` undoes `stdToUrl` on the bytes that `stdToUrl` sends to URL-safe symbols, except
`-` and `_` themselves. -/
theorem urlToStd_stdToUrl {c : U8} (h : (b64Val (stdToUrl c)).isSome) (h45 : c.val ≠ 45)
    (h95 : c.val ≠ 95) : urlToStd (stdToUrl c) = c := by
  have := val_of_isSome_b64Val h
  unfold stdToUrl at *
  split_ifs at * <;> unfold urlToStd <;> split_ifs <;> simp_all [byte_val] <;>
    first | omega | (apply byte_eq; simp_all)

theorem byte61_notMem {w : List U8} (hw : ∀ c ∈ w, c.val ≠ 61) : byte 61 ∉ w :=
  fun h => hw _ h (by simp [byte_val])

/-- `padBody` removes exactly the canonical padding of a symbol list. -/
theorem padBody_append_replicate (w : List U8) (p : Nat) (hw : ∀ c ∈ w, c.val ≠ 61)
    (hp : p ≤ 2) (hlen : p = 0 ∨ 2 ≤ w.length) :
    padBody (w ++ List.replicate p (byte 61)) = w := by
  have hn := byte61_notMem hw
  unfold padBody
  rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2) with rfl | rfl | rfl
  · simp only [List.replicate_zero, List.append_nil]
    have h2 : ¬ w.drop (w.length - 2) = [byte 61, byte 61] := fun hd =>
      hn (List.mem_of_mem_drop (by rw [hd]; simp : byte 61 ∈ w.drop (w.length - 2)))
    have h1 : ¬ w.drop (w.length - 1) = [byte 61] := fun hd =>
      hn (List.mem_of_mem_drop (by rw [hd]; simp : byte 61 ∈ w.drop (w.length - 1)))
    simp [h1, h2]
  · have hl : 2 ≤ w.length := by omega
    have e1 : (w ++ List.replicate 1 (byte 61)).length - 2 = w.length - 1 := by
      simp only [List.length_append, List.length_replicate]; omega
    have e2 : (w ++ List.replicate 1 (byte 61)).length - 1 = w.length := by simp
    have h2 : ¬ (w ++ [byte 61]).drop (w.length - 1) = [byte 61, byte 61] := by
      intro hd
      rw [List.drop_append_of_le_length (by omega)] at hd
      have := (List.append_inj' (s₂ := [byte 61]) (t₂ := [byte 61]) hd (by simp)).1
      exact hn (List.mem_of_mem_drop (by simp [this] : byte 61 ∈ w.drop (w.length - 1)))
    rw [e1, e2]
    simp only [List.replicate_one] at h2 ⊢
    simp [h2]
  · have e1 : (w ++ List.replicate 2 (byte 61)).length - 2 = w.length := by simp
    rw [e1]
    simp [List.replicate]

/-- Every list is its `padBody` followed by at most two `=`. -/
theorem eq_padBody_append_replicate (s : List U8) :
    ∃ k ≤ 2, s = padBody s ++ List.replicate k (byte 61) := by
  unfold padBody
  split_ifs with h2 h1
  · exact ⟨2, le_refl _, by
      conv => lhs; rw [← List.take_append_drop (s.length - 2) s]
      rw [h2]; rfl⟩
  · exact ⟨1, by omega, by
      conv => lhs; rw [← List.take_append_drop (s.length - 1) s]
      rw [h1]; rfl⟩
  · exact ⟨0, by omega, by simp⟩

theorem length_b64_mod_four_ne_one (x : List U8) : (b64 x).length % 4 ≠ 1 := by
  rw [length_b64]; omega

/-- **Round trip:** decoding the padded standard encoding of `x` gives `x`. -/
theorem b64StdPadDecode_b64StdPad (x : List U8) : b64StdPadDecode (b64StdPad x) = some x := by
  have hsym : ∀ c ∈ b64 x, (b64Val c).isSome := fun c hc => isSome_b64Val_of_mem_b64 x c hc
  have hne : ∀ c ∈ (b64 x).map urlToStd, c.val ≠ 61 ∧ c.val ≠ 45 ∧ c.val ≠ 95 := by
    intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    have := val_urlToStd (hsym d hd); omega
  have hm := length_b64_mod_four_ne_one x
  have hbody : padBody (b64StdPad x) = (b64 x).map urlToStd := by
    unfold b64StdPad
    apply padBody_append_replicate _ _ (fun c hc => (hne c hc).1) (by omega)
    simp only [List.length_map]; omega
  have hlen : (b64StdPad x).length % 4 = 0 := by
    unfold b64StdPad
    simp only [List.length_append, List.length_map, List.length_replicate]; omega
  have hany : ((b64 x).map urlToStd).any (fun c => c.val = 45 || c.val = 95) = false := by
    simp only [List.any_eq_false, Bool.or_eq_true, decide_eq_true_eq, not_or]
    intro c hc; exact ⟨(hne c hc).2.1, (hne c hc).2.2⟩
  have hmap : ((b64 x).map urlToStd).map stdToUrl = b64 x := by
    rw [List.map_map]
    conv => rhs; rw [← List.map_id (b64 x)]
    exact List.map_congr_left (fun c hc => stdToUrl_urlToStd (hsym c hc))
  unfold b64StdPadDecode
  simp only [hlen, hbody, hany, hmap, ne_eq, not_true_eq_false, ↓reduceIte, Bool.false_eq_true,
    b64Decode_b64]

/-- **Canonicity:** the decoder accepts exactly the padded standard encodings, and returns what
was encoded. -/
theorem b64StdPadDecode_eq_some_iff (s y : List U8) :
    b64StdPadDecode s = some y ↔ b64StdPad y = s := by
  refine ⟨fun h => ?_, fun h => h ▸ b64StdPadDecode_b64StdPad y⟩
  unfold b64StdPadDecode at h
  split_ifs at h with hl hany
  have hb := b64_of_b64Decode _ _ h
  have hbody : (b64 y).map urlToStd = padBody s := by
    rw [hb, List.map_map]
    conv => rhs; rw [← List.map_id (padBody s)]
    apply List.map_congr_left
    intro c hc
    have hs : (b64Val (stdToUrl c)).isSome :=
      isSome_b64Val_of_mem_b64 y _ (hb ▸ List.mem_map_of_mem hc)
    simp only [List.any_eq_true, Bool.or_eq_true, decide_eq_true_eq, not_exists, not_and,
      not_or] at hany
    exact urlToStd_stdToUrl hs (hany c hc).1 (hany c hc).2
  obtain ⟨k, hk, hs⟩ := eq_padBody_append_replicate s
  have hlen : (b64 y).length = (padBody s).length := by rw [← hbody, List.length_map]
  have hk' : k = (4 - (b64 y).length % 4) % 4 := by
    have := congrArg List.length hs
    simp only [List.length_append, List.length_replicate] at this
    omega
  unfold b64StdPad
  rw [hbody, ← hk', ← hs]

/-- **Visible ASCII:** every byte of the padded standard encoding is in `0x21`–`0x7E`. -/
theorem visible_of_mem_b64StdPad {x : List U8} {c : U8} (h : c ∈ b64StdPad x) :
    0x21 ≤ c.val ∧ c.val ≤ 0x7E := by
  unfold b64StdPad at h
  rcases List.mem_append.1 h with h | h
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 h
    have := val_urlToStd (isSome_b64Val_of_mem_b64 x d hd); omega
  · rw [List.eq_of_mem_replicate h, byte_val]; omega

/-- In particular the encoding is ASCII. -/
theorem val_lt_128_of_mem_b64StdPad (x : List U8) : ∀ c ∈ b64StdPad x, c.val < 128 :=
  fun _ h => by have := visible_of_mem_b64StdPad h; omega

/-- **Length:** the padded encoding of `n` bytes has `4 ⌈n / 3⌉` bytes (`encoded_len(n, true)`,
`base64-0.23.1/src/encode.rs` lines 101–129). -/
theorem length_b64StdPad (x : List U8) : (b64StdPad x).length = (x.length + 2) / 3 * 4 := by
  unfold b64StdPad
  simp only [List.length_append, List.length_map, List.length_replicate, length_b64]
  omega

/-! #### Vectors

RFC 4648 Section 10 (standard alphabet, padded), bytes as decimal ASCII codes: `f o b a r` =
`102 111 98 97 114`, `Z g = m 8 9 v Y F y` = `90 103 61 109 56 57 118 89 70 121`; the two
symbols that differ from Base64url (`+` = 43, `/` = 47: the bytes `251 255` encode as `+/8=`); and
the strictness cases: unpadded input (`Zg`), short padding (`Zg=`), padding after one symbol
(`Z===`), URL-safe symbols (`-_8=`), non-zero trailing bits (`Zh==`), padding inside (`Zg==Zg==`),
only padding (`====`), and the empty input. Each value agrees with `base64-0.23.1` `BASE64_STANDARD`
(`formal/trusted/evidence/README.md`, section "Header-value externals"). -/

theorem b64StdPad_rfc4648_empty : b64StdPad [] = [] := by decide
theorem b64StdPad_rfc4648_f : b64StdPad [102#u8] = [90#u8, 103#u8, 61#u8, 61#u8] := by decide
theorem b64StdPad_rfc4648_fo :
    b64StdPad [102#u8, 111#u8] = [90#u8, 109#u8, 56#u8, 61#u8] := by decide
theorem b64StdPad_rfc4648_foobar :
    b64StdPad [102#u8, 111#u8, 111#u8, 98#u8, 97#u8, 114#u8] =
      [90#u8, 109#u8, 57#u8, 118#u8, 89#u8, 109#u8, 70#u8, 121#u8] := by decide
theorem b64StdPad_plus_slash : b64StdPad [251#u8, 255#u8] = [43#u8, 47#u8, 56#u8, 61#u8] := by
  decide
theorem b64StdPadDecode_plus_slash :
    b64StdPadDecode [43#u8, 47#u8, 56#u8, 61#u8] = some [251#u8, 255#u8] := by decide
theorem b64StdPadDecode_rejects_unpadded : b64StdPadDecode [90#u8, 103#u8] = none := by decide
theorem b64StdPadDecode_rejects_short_padding :
    b64StdPadDecode [90#u8, 103#u8, 61#u8] = none := by decide
theorem b64StdPadDecode_rejects_early_padding :
    b64StdPadDecode [90#u8, 61#u8, 61#u8, 61#u8] = none := by decide
theorem b64StdPadDecode_rejects_url_safe :
    b64StdPadDecode [45#u8, 95#u8, 56#u8, 61#u8] = none := by decide
theorem b64StdPadDecode_rejects_trailing_bits :
    b64StdPadDecode [90#u8, 104#u8, 61#u8, 61#u8] = none := by decide
theorem b64StdPadDecode_empty : b64StdPadDecode [] = some [] := by decide
theorem b64StdPadDecode_rejects_all_padding :
    b64StdPadDecode [61#u8, 61#u8, 61#u8, 61#u8] = none := by decide
theorem b64StdPadDecode_rejects_inner_padding :
    b64StdPadDecode [90#u8, 103#u8, 61#u8, 61#u8, 90#u8, 103#u8, 61#u8, 61#u8] = none := by
  decide

/-! ### Control and non-ASCII bytes -/

/-- One char: some byte of its UTF-8 encoding is below `0x20` or above `0x7E` exactly when its
code point is. -/
theorem any_isControlOrNonAsciiByte_utf8_singleton (c : Char) :
    (utf8 (String.ofList [c])).any isControlOrNonAsciiByte =
      decide (c.toNat < 0x20 ∨ 0x7E < c.toNat) := by
  by_cases hc : c.toNat < 128
  · rw [utf8_ofList_singleton_ascii c hc]
    simp only [List.any_cons, List.any_nil, Bool.or_false, isControlOrNonAsciiByte, byte_val,
      Nat.mod_eq_of_lt (by omega : c.toNat < 256)]
  · have hge := le_val_of_mem_utf8_ofList_singleton (Nat.le_of_not_lt hc)
    have hne : utf8 (String.ofList [c]) ≠ [] := by
      rw [utf8_ofList, List.flatMap_cons, List.flatMap_nil, List.append_nil, ne_eq,
        List.map_eq_nil_iff]
      intro h
      have := congrArg List.length h
      rw [String.length_utf8EncodeChar, List.length_nil] at this
      exact absurd this (Nat.ne_of_gt (Char.utf8Size_pos c))
    obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil _ hne
    have h1 : (utf8 (String.ofList [c])).any isControlOrNonAsciiByte = true :=
      List.any_eq_true.2 ⟨b, hb, by
        simp only [isControlOrNonAsciiByte, decide_eq_true_eq]; have := hge b hb; omega⟩
    rw [h1]
    simp only [Bool.true_eq, decide_eq_true_eq]
    omega

/-- **Byte test = char test on UTF-8** (GD2): on the UTF-8 bytes of a string, the byte-level model
of `prim::has_control_or_non_ascii` is Rust's
`value.chars().any(|c| (c as u32) < 0x20 || (c as u32) > 0x7E)`. -/
theorem any_isControlOrNonAsciiByte_utf8 (t : String) :
    (utf8 t).any isControlOrNonAsciiByte =
      t.toList.any (fun c => decide (c.toNat < 0x20 ∨ 0x7E < c.toNat)) := by
  conv => lhs; rw [← String.ofList_toList (s := t)]
  induction t.toList with
  | nil => simp only [utf8_ofList, List.flatMap_nil, List.any_nil]
  | cons c cs ih =>
    rw [utf8_ofList_cons, List.any_append, any_isControlOrNonAsciiByte_utf8_singleton, ih,
      List.any_cons]

/-! ### Bounds -/

/-- `isize::MAX` is at least `2 ^ 31 - 1` on every platform, in particular at least 1000. -/
theorem thousand_le_maxStringBytes : 1000 ≤ maxStringBytes := by
  unfold maxStringBytes
  scalar_tac

/-- **Decode buffer:** for an input of at most `isize::MAX` bytes, the decode buffer
`b64StdDecodedLenEstimate n` (`3 ⌈n / 4⌉` bytes) is at most `isize::MAX` bytes, the premise of
`base64_decode_spec`. -/
theorem b64StdDecodedLenEstimate_le_of_le {n : Nat} (h : n ≤ maxStringBytes) :
    b64StdDecodedLenEstimate n ≤ maxStringBytes := by
  have := thousand_le_maxStringBytes
  unfold b64StdDecodedLenEstimate
  split_ifs <;> omega

/-- **Encode buffer:** for an input of at most `isize::MAX / 2` bytes, the padded encoding
(`(n + 2) / 3 * 4` bytes, `length_b64StdPad`) fits in a `String` together with the 11 bytes of
the sentinel. -/
theorem add_two_div_three_mul_four_add_eleven_le {n : Nat} (h : n ≤ maxStringBytes / 2) :
    (n + 2) / 3 * 4 + 11 ≤ maxStringBytes := by
  have := thousand_le_maxStringBytes
  omega

/-- The premise of `base64_encode_spec` from a bound on the input length. -/
theorem add_two_div_three_mul_four_le {n : Nat} (h : n ≤ maxStringBytes / 2) :
    (n + 2) / 3 * 4 ≤ maxStringBytes :=
  (Nat.le_add_right _ _).trans (add_two_div_three_mul_four_add_eleven_le h)

/-- The premise of `wrap_sentinel_spec` for the output of `base64_encode` (whose bytes are
`b64StdPad x`, `base64_encode_spec`) from a bound on the input length. -/
theorem length_b64StdPad_add_eleven_le {x : List U8} (h : x.length ≤ maxStringBytes / 2) :
    (b64StdPad x).length + 11 ≤ maxStringBytes := by
  rw [length_b64StdPad]; exact add_two_div_three_mul_four_add_eleven_le h

end Proofs.External.Base64Std

/-! ## The `mcp_headers::prim` functions -/

namespace transport.common.mcp_headers.prim

open ExtModel Proofs.External.Utf8 Proofs.External.Base64Std

/-- **Spec theorem for `rmcp::transport::common::mcp_headers::prim::has_control_or_non_ascii`**

Always succeeds: `true` exactly when some byte of `value` is below `0x20` or above `0x7E`. On the
bytes of a string this is the char-level test of Rust (`has_control_or_non_ascii_spec_utf8`). -/
@[step]
theorem has_control_or_non_ascii_spec (value : Str) :
    transport.common.mcp_headers.prim.has_control_or_non_ascii value ⦃ (result : Bool) =>
      result = value.val.any isControlOrNonAsciiByte ⦄ := by
  simp only [transport.common.mcp_headers.prim.has_control_or_non_ascii, WP.spec_ok]

/-- The spec on valid UTF-8 (every Rust `&str`): `true` exactly when some char of the string has
a code point below `0x20` or above `0x7E`. -/
theorem has_control_or_non_ascii_spec_utf8 (value : Str) (t : String) (ht : value.val = utf8 t) :
    transport.common.mcp_headers.prim.has_control_or_non_ascii value ⦃ (result : Bool) =>
      result = t.toList.any (fun c => decide (c.toNat < 0x20 ∨ 0x7E < c.toNat)) ⦄ := by
  simp only [transport.common.mcp_headers.prim.has_control_or_non_ascii, WP.spec_ok, ht,
    any_isControlOrNonAsciiByte_utf8]

/-- **Spec theorem for `rmcp::transport::common::mcp_headers::prim::starts_with`**

Always succeeds: `true` exactly when the bytes of `pre` are a prefix of the bytes of `s`. -/
@[step]
theorem starts_with_spec (s : Str) (pre : Str) :
    transport.common.mcp_headers.prim.starts_with s pre ⦃ (result : Bool) =>
      (result = true ↔ pre.val <+: s.val) ⦄ := by
  simp only [transport.common.mcp_headers.prim.starts_with, WP.spec_ok, decide_eq_true_eq]

/-- **Spec theorem for `rmcp::transport::common::mcp_headers::prim::ends_with`**

Always succeeds: `true` exactly when the bytes of `suffix` are a suffix of the bytes of `s`. -/
@[step]
theorem ends_with_spec (s : Str) (suffix : Str) :
    transport.common.mcp_headers.prim.ends_with s suffix ⦃ (result : Bool) =>
      (result = true ↔ suffix.val <:+ s.val) ⦄ := by
  simp only [transport.common.mcp_headers.prim.ends_with, WP.spec_ok, decide_eq_true_eq]

/-- **Spec theorem for `rmcp::transport::common::mcp_headers::prim::strip_prefix`**

Always succeeds: the bytes of `s` after `pre` if `pre` is a prefix of `s`, otherwise `None`. -/
@[step]
theorem strip_prefix_spec (s : Str) (pre : Str) :
    transport.common.mcp_headers.prim.strip_prefix s pre ⦃ (result : Option Str) =>
      result.map (·.val) = if pre.val <+: s.val then some (s.val.drop pre.val.length)
        else none ⦄ := by
  unfold transport.common.mcp_headers.prim.strip_prefix
  by_cases h : pre.val <+: s.val
  · rw [ite_eq_left h]
    refine (WP.spec_ok _).2 ?_
    rw [ite_eq_left h]
    exact congrArg some (Slice.from_val _ _)
  · rw [ite_eq_right h]
    refine (WP.spec_ok _).2 ?_
    rw [ite_eq_right h, Option.map_none]

/-- **Spec theorem for `rmcp::transport::common::mcp_headers::prim::strip_suffix`**

Always succeeds: the bytes of `s` before `suffix` if `suffix` is a suffix of `s`, otherwise
`None`. -/
@[step]
theorem strip_suffix_spec (s : Str) (suffix : Str) :
    transport.common.mcp_headers.prim.strip_suffix s suffix ⦃ (result : Option Str) =>
      result.map (·.val) = if suffix.val <:+ s.val then
        some (s.val.take (s.val.length - suffix.val.length)) else none ⦄ := by
  unfold transport.common.mcp_headers.prim.strip_suffix
  by_cases h : suffix.val <:+ s.val
  · rw [ite_eq_left h]
    refine (WP.spec_ok _).2 ?_
    rw [ite_eq_left h]
    exact congrArg some (Slice.from_val _ _)
  · rw [ite_eq_right h]
    refine (WP.spec_ok _).2 ?_
    rw [ite_eq_right h, Option.map_none]

/-- **Spec theorem for `rmcp::transport::common::mcp_headers::prim::wrap_sentinel`**

For a UTF-8 argument (`encoded` is the bytes of `t`, as every Rust `&str` is) whose result fits in
a `String`: the string `"=?base64?" ++ t ++ "?="`, whose bytes are `=?base64?` (9 bytes), the
bytes of `encoded`, and `?=` (2 bytes). -/
@[step]
theorem wrap_sentinel_spec (encoded : Str) (t : String) (ht : encoded.val = utf8 t)
    (h : encoded.val.length + 11 ≤ maxStringBytes) :
    transport.common.mcp_headers.prim.wrap_sentinel encoded ⦃ (result : String) =>
      result = "=?base64?" ++ t ++ "?=" ∧
        utf8 result = utf8 "=?base64?" ++ encoded.val ++ utf8 "?=" ⦄ := by
  have hlen : ("=?base64?" ++ t ++ "?=").utf8ByteSize ≤ maxStringBytes := by
    rw [← length_utf8, utf8_append, utf8_append, ← ht]
    simp only [List.length_append]
    have h1 : (utf8 "=?base64?").length = 9 := by rw [length_utf8]; rfl
    have h2 : (utf8 "?=").length = 2 := by rw [length_utf8]; rfl
    omega
  simp only [transport.common.mcp_headers.prim.wrap_sentinel, ht, strOfBytes?_utf8, growString,
    ite_eq_left hlen, WP.spec_ok, utf8_append, true_and]

/-- Beyond the `String` limit, `wrap_sentinel` panics. -/
theorem wrap_sentinel_fail (encoded : Str) (t : String) (ht : encoded.val = utf8 t)
    (h : maxStringBytes < encoded.val.length + 11) :
    transport.common.mcp_headers.prim.wrap_sentinel encoded = fail Error.panic := by
  have hlen : ¬ ("=?base64?" ++ t ++ "?=").utf8ByteSize ≤ maxStringBytes := by
    rw [← length_utf8, utf8_append, utf8_append, ← ht]
    simp only [List.length_append]
    have h1 : (utf8 "=?base64?").length = 9 := by rw [length_utf8]; rfl
    have h2 : (utf8 "?=").length = 2 := by rw [length_utf8]; rfl
    omega
  simp only [transport.common.mcp_headers.prim.wrap_sentinel, ht, strOfBytes?_utf8, growString,
    ite_eq_right hlen]

/-- `wrap_sentinel` with bytes that are not UTF-8 (no Rust `&str`) is outside the Rust domain:
`fail undef`. -/
theorem wrap_sentinel_not_utf8 (encoded : Str) (h : ∀ t, encoded.val ≠ utf8 t) :
    transport.common.mcp_headers.prim.wrap_sentinel encoded = fail Error.undef := by
  simp only [transport.common.mcp_headers.prim.wrap_sentinel, (strOfBytes?_eq_none_iff _).2 h]

/-- **Spec theorem for `rmcp::transport::common::mcp_headers::prim::base64_encode`**

The bytes of the result are the padded standard Base64 encoding `b64StdPad value.val`
(`4 ⌈n / 3⌉` bytes for `n` input bytes, `length_b64StdPad`). Precondition: the result fits in a
Rust `String` (`isize::MAX` bytes); otherwise the Rust code panics (`base64_encode_fail`). -/
@[step]
theorem base64_encode_spec (value : Str)
    (h : (value.val.length + 2) / 3 * 4 ≤ maxStringBytes) :
    transport.common.mcp_headers.prim.base64_encode value ⦃ (result : String) =>
      utf8 result = b64StdPad value.val ⦄ := by
  have hb : utf8 (String.ofList ((b64StdPad value.val).map (fun b => Char.ofNat b.val))) =
      b64StdPad value.val := utf8_ofList_ascii _ (val_lt_128_of_mem_b64StdPad _)
  have hlen : (String.ofList ((b64StdPad value.val).map (fun b => Char.ofNat b.val))
      ).utf8ByteSize ≤ maxStringBytes := by
    rw [← length_utf8, hb, length_b64StdPad]; exact h
  simp only [transport.common.mcp_headers.prim.base64_encode, growString, ite_eq_left hlen,
    WP.spec_ok, hb]

/-- Beyond the `String` limit, `base64_encode` panics. -/
theorem base64_encode_fail (value : Str)
    (h : maxStringBytes < (value.val.length + 2) / 3 * 4) :
    transport.common.mcp_headers.prim.base64_encode value = fail Error.panic := by
  have hb : utf8 (String.ofList ((b64StdPad value.val).map (fun b => Char.ofNat b.val))) =
      b64StdPad value.val := utf8_ofList_ascii _ (val_lt_128_of_mem_b64StdPad _)
  have hlen : ¬ (String.ofList ((b64StdPad value.val).map (fun b => Char.ofNat b.val))
      ).utf8ByteSize ≤ maxStringBytes := by
    rw [← length_utf8, hb, length_b64StdPad]; omega
  simp only [transport.common.mcp_headers.prim.base64_encode, growString, ite_eq_right hlen]

/-- **Spec theorem for `rmcp::transport::common::mcp_headers::prim::base64_decode`**

When the decode buffer fits (`b64StdDecodedLenEstimate` bytes at most `isize::MAX`): the result
is `b64StdPadDecode value.val`, `some` of the decoded bytes exactly when `value` is the padded
standard encoding of them (`b64StdPadDecode_eq_some_iff`), `none` otherwise. -/
@[step]
theorem base64_decode_spec (value : Str)
    (h : b64StdDecodedLenEstimate value.val.length ≤ maxStringBytes) :
    transport.common.mcp_headers.prim.base64_decode value
      ⦃ (result : Option (alloc.vec.Vec U8)) =>
        result.map (fun v => v.val) = b64StdPadDecode value.val ⦄ := by
  unfold transport.common.mcp_headers.prim.base64_decode
  rw [ite_eq_right (Nat.not_lt.2 h)]
  split <;> simp_all only [Option.map_eq_none_iff, WP.spec_ok, Option.map_some,
    alloc.vec.Vec.from_val]

/-- Beyond the buffer limit, `base64_decode` panics (before reading the input). -/
theorem base64_decode_fail (value : Str)
    (h : maxStringBytes < b64StdDecodedLenEstimate value.val.length) :
    transport.common.mcp_headers.prim.base64_decode value = fail Error.panic := by
  simp only [transport.common.mcp_headers.prim.base64_decode, ite_eq_left h]

end transport.common.mcp_headers.prim

/-! ## Standard library -/

/-- **Spec theorem for `char::is_ascii_alphanumeric`**

Always succeeds: `true` exactly when the code point is in `0`–`9`, `A`–`Z` or `a`–`z`. -/
@[step]
theorem core.char.methods.Char.is_ascii_alphanumeric_spec (self : Char) :
    core.char.methods.Char.is_ascii_alphanumeric self ⦃ (result : Bool) =>
      (result = true ↔ (48 ≤ self.toNat ∧ self.toNat ≤ 57) ∨ (65 ≤ self.toNat ∧ self.toNat ≤ 90) ∨
        (97 ≤ self.toNat ∧ self.toNat ≤ 122)) ⦄ := by
  simp only [core.char.methods.Char.is_ascii_alphanumeric, WP.spec_ok, decide_eq_true_eq]

/-- **Spec theorem for `<[T]>::last`**: the last element, `None` for the empty slice. -/
@[step]
theorem core.slice.Slice.last_spec {T : Type} (self : Slice T) :
    core.slice.Slice.last self ⦃ (result : Option T) => result = self.val.getLast? ⦄ := by
  simp only [core.slice.Slice.last, WP.spec_ok]

/-- **Spec theorem for `Option<&T>::copied`**: the same option (a shared borrow is its value in
the translation). -/
@[step]
theorem core.option.OptionShared0T.copied_spec {T : Type} (markerCopyInst : core.marker.Copy T)
    (self : Option T) :
    core.option.OptionShared0T.copied markerCopyInst self ⦃ (result : Option T) =>
      result = self ⦄ := by
  simp only [core.option.OptionShared0T.copied, WP.spec_ok]
