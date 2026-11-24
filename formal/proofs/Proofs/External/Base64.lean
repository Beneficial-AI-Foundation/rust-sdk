/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Rmcp.FunsExternal
import Defs.Wire
import Proofs.External.Byte

/-!
# Laws of the Base64url model

Theorems about `ExtModel.b64` and `ExtModel.b64Decode` (`formal/trusted/Rmcp/FunsExternal.lean`),
the model of `base64-0.23.1` `URL_SAFE_NO_PAD` behind `prim::b64_encode_into` and
`prim::b64_decode` (`crates/rmcp/src/model/request_state_wire.rs` lines 268–276 in the patched
copy, patch 01 on origin/main 7caec76; line numbers refer to it). Since the model is a definition,
these are proved, not assumed: decoding inverts encoding, every decodable input
is the encoding of its result (so `b64Decode` rejects padding, foreign symbols, impossible
lengths and non-canonical trailing bits), the output alphabet, the output length, and the
RFC 4648 Section 10 vectors and the strictness cases of the Rust tests, checked by `decide`.
-/

open Aeneas Aeneas.Std

namespace Proofs.External.Base64

open ExtModel Proofs.External.Byte

/-- `b64Val` inverts `b64Sym` on 6-bit values. -/
theorem b64Val_b64Sym {n : Nat} (h : n < 64) : b64Val (b64Sym n) = some n := by
  unfold b64Sym
  split_ifs <;> simp only [b64Val, byte_val] <;> split_ifs <;>
    first | omega | (simp only [Option.some.injEq]; omega)

/-- Every symbol that `b64Val` accepts is `b64Sym` of its value, and the value has 6 bits. -/
theorem b64Sym_b64Val {c : U8} {n : Nat} (h : b64Val c = some n) : b64Sym n = c ∧ n < 64 := by
  unfold b64Val at h
  split_ifs at h <;> simp only [Option.some.injEq, ReduceNat.reduceNatEq] at h <;> subst h <;>
    refine ⟨?_, by omega⟩ <;> unfold b64Sym <;> split_ifs <;>
    first | omega | (apply byte_eq; omega)

/-- `b64Sym` produces only symbols of the URL-safe alphabet. -/
theorem isSome_b64Val_b64Sym (n : Nat) : (b64Val (b64Sym n)).isSome := by
  unfold b64Sym
  split_ifs <;> simp only [b64Val, byte_val] <;> split_ifs <;>
    first | rfl | omega

/-- **Round trip:** decoding the encoding gives the input back. -/
theorem b64Decode_b64 : ∀ x : List U8, b64Decode (b64 x) = some x
  | a :: b :: c :: rest => by
    have ha := val_lt a; have hb := val_lt b; have hc := val_lt c
    simp only [b64, b64Decode, b64Val_b64Sym (show a.val / 4 < 64 by omega),
      b64Val_b64Sym (show a.val % 4 * 16 + b.val / 16 < 64 by omega),
      b64Val_b64Sym (show b.val % 16 * 4 + c.val / 64 < 64 by omega),
      b64Val_b64Sym (show c.val % 64 < 64 by omega), b64Decode_b64 rest,
      Option.bind_eq_bind, Option.bind_some, Option.some.injEq, List.cons.injEq]
    refine ⟨byte_eq ?_, byte_eq ?_, byte_eq ?_, trivial⟩ <;> omega
  | [a, b] => by
    have ha := val_lt a; have hb := val_lt b
    simp only [b64, b64Decode, b64Val_b64Sym (show a.val / 4 < 64 by omega),
      b64Val_b64Sym (show a.val % 4 * 16 + b.val / 16 < 64 by omega),
      b64Val_b64Sym (show b.val % 16 * 4 < 64 by omega),
      Option.bind_eq_bind, Option.bind_some]
    rw [if_pos (by omega)]
    simp only [Option.some.injEq, List.cons.injEq]
    refine ⟨byte_eq ?_, byte_eq ?_, trivial⟩ <;> omega
  | [a] => by
    have ha := val_lt a
    simp only [b64, b64Decode, b64Val_b64Sym (show a.val / 4 < 64 by omega),
      b64Val_b64Sym (show a.val % 4 * 16 < 64 by omega), Option.bind_eq_bind, Option.bind_some]
    rw [if_pos (by omega)]
    simp only [Option.some.injEq, List.cons.injEq]
    exact ⟨byte_eq (by omega), trivial⟩
  | [] => rfl

/-- **Canonicity:** every input that decodes is the encoding of its result. With
`b64Decode_b64`, `b64Decode s = some y ↔ b64 y = s`: the decoder accepts exactly the canonical
unpadded encodings and rejects everything else (padding, foreign bytes, length `≡ 1 (mod 4)`,
non-zero trailing bits). -/
theorem b64_of_b64Decode : ∀ (s y : List U8), b64Decode s = some y → b64 y = s
  | c0 :: c1 :: c2 :: c3 :: rest, y, h => by
    simp only [b64Decode, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨v0, h0, v1, h1, v2, h2, v3, h3, tail, ht, hy⟩ := h
    obtain ⟨e0, l0⟩ := b64Sym_b64Val h0; obtain ⟨e1, l1⟩ := b64Sym_b64Val h1
    obtain ⟨e2, l2⟩ := b64Sym_b64Val h2; obtain ⟨e3, l3⟩ := b64Sym_b64Val h3
    simp only [Option.some.injEq] at hy; subst hy
    simp only [b64, byte_val, b64_of_b64Decode rest tail ht, List.cons.injEq]
    refine ⟨?_, ?_, ?_, ?_, trivial⟩
    · rw [← e0]; congr 1; omega
    · rw [← e1]; congr 1; omega
    · rw [← e2]; congr 1; omega
    · rw [← e3]; congr 1; omega
  | [c0, c1, c2], y, h => by
    simp only [b64Decode, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨v0, h0, v1, h1, v2, h2, hy⟩ := h
    obtain ⟨e0, l0⟩ := b64Sym_b64Val h0; obtain ⟨e1, l1⟩ := b64Sym_b64Val h1
    obtain ⟨e2, l2⟩ := b64Sym_b64Val h2
    split at hy
    · simp only [Option.some.injEq] at hy; subst hy
      simp only [b64, byte_val, List.cons.injEq]
      refine ⟨?_, ?_, ?_, trivial⟩
      · rw [← e0]; congr 1; omega
      · rw [← e1]; congr 1; omega
      · rw [← e2]; congr 1; omega
    · simp only [reduceCtorEq] at hy
  | [c0, c1], y, h => by
    simp only [b64Decode, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨v0, h0, v1, h1, hy⟩ := h
    obtain ⟨e0, l0⟩ := b64Sym_b64Val h0; obtain ⟨e1, l1⟩ := b64Sym_b64Val h1
    split at hy
    · simp only [Option.some.injEq] at hy; subst hy
      simp only [b64, byte_val, List.cons.injEq]
      refine ⟨?_, ?_, trivial⟩
      · rw [← e0]; congr 1; omega
      · rw [← e1]; congr 1; omega
    · simp only [reduceCtorEq] at hy
  | [_], y, h => by simp only [b64Decode, reduceCtorEq] at h
  | [], y, h => by simp only [b64Decode, Option.some.injEq] at h; subst h; rfl

/-- `b64Decode` accepts exactly the encodings, and returns what was encoded. -/
theorem b64Decode_eq_some_iff (s y : List U8) : b64Decode s = some y ↔ b64 y = s :=
  ⟨b64_of_b64Decode s y, fun h => h ▸ b64Decode_b64 y⟩

/-- **Alphabet:** every byte of an encoding is a symbol of the URL-safe alphabet. -/
theorem isSome_b64Val_of_mem_b64 : ∀ (x : List U8), ∀ c ∈ b64 x, (b64Val c).isSome
  | a :: b :: c :: rest => by
    intro d hd
    simp only [b64, List.mem_cons] at hd
    rcases hd with h | h | h | h | h <;> first | (subst h; exact isSome_b64Val_b64Sym _) |
      exact isSome_b64Val_of_mem_b64 rest d h
  | [a, b] => by
    intro d hd; simp only [b64, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with h | h | h <;> (subst h; exact isSome_b64Val_b64Sym _)
  | [a] => by
    intro d hd; simp only [b64, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with h | h <;> (subst h; exact isSome_b64Val_b64Sym _)
  | [] => by simp only [b64, List.not_mem_nil, IsEmpty.forall_iff, implies_true]

/-- The symbols of the URL-safe alphabet are the bytes `A`–`Z`, `a`–`z`, `0`–`9`, `-`, `_`. -/
theorem isSome_b64Val_iff (c : U8) :
    (b64Val c).isSome ↔ (65 ≤ c.val ∧ c.val ≤ 90) ∨ (97 ≤ c.val ∧ c.val ≤ 122) ∨
      (48 ≤ c.val ∧ c.val ≤ 57) ∨ c.val = 45 ∨ c.val = 95 := by
  unfold b64Val
  split_ifs <;> simp only [Option.isSome_some, Option.isSome_none, true_iff, Bool.false_eq_true,
    false_iff] <;> omega

/-- In particular an encoding never contains the separator `.` (`Defs.Wire.dot`). -/
theorem dot_notMem_b64 (x : List U8) : Defs.Wire.dot ∉ b64 x := by
  intro h
  have := (isSome_b64Val_iff _).1 (isSome_b64Val_of_mem_b64 x _ h)
  rw [Defs.Wire.dot, UScalar.ofNatCore_val_eq] at this; omega

/-- **Length:** the unpadded encoding of `n` bytes has `⌈4n/3⌉ = (4n + 2) / 3` symbols. -/
theorem length_b64 : ∀ x : List U8, (b64 x).length = (4 * x.length + 2) / 3
  | _ :: _ :: _ :: rest => by
    simp only [b64, List.length_cons, length_b64 rest]; omega
  | [_, _] => by simp only [b64, List.length_cons, List.length_nil]
  | [_] => by simp only [b64, List.length_cons, List.length_nil]
  | [] => rfl

/-- A Base64 text `s` that decodes to `y` has at least `4|y| / 3` symbols: `4|y| ≤ 3|s|`
(from the round trip `b64 y = s`, `b64_of_b64Decode`, and the length of `b64`, `length_b64`). -/
theorem four_mul_length_le_of_b64Decode (s y : List U8) (h : b64Decode s = some y) :
    4 * y.length ≤ 3 * s.length := by
  have hl := length_b64 y
  rw [b64_of_b64Decode s y h] at hl
  omega

/-- The encoding is never longer than `Defs.Wire.b64Len` (`4 * ⌈n/3⌉`, the padded length that
`wire::b64_len` computes). -/
theorem length_b64_le_b64Len (x : List U8) : (b64 x).length ≤ Defs.Wire.b64Len x.length := by
  rw [length_b64, Defs.Wire.b64Len]; omega

/-- For a length divisible by 3 the encoding has exactly `Defs.Wire.b64Len` symbols. -/
theorem length_b64_of_dvd (x : List U8) (h : 3 ∣ x.length) :
    (b64 x).length = Defs.Wire.b64Len x.length := by
  rw [length_b64, Defs.Wire.b64Len]; omega

/-! ### Vectors

RFC 4648 Section 10 (the URL-safe alphabet agrees with the standard one on them), as in the
Rust test `rfc4648_base64url_vectors`, and the cases of `base64url_alphabet_and_append` and
`base64url_decode_is_strict` (`request_state_wire.rs`, in the patched copy). Bytes are written
as decimal ASCII codes: `f o b a r` = `102 111 98 97 114`;
`Z m g 9 v Y F y` = `90 109 103 57 118 89 70 121`. -/

theorem b64_rfc4648_empty : b64 [] = [] := by decide
theorem b64_rfc4648_f : b64 [102#u8] = [90#u8, 103#u8] := by decide
theorem b64_rfc4648_fo : b64 [102#u8, 111#u8] = [90#u8, 109#u8, 56#u8] := by decide
theorem b64_rfc4648_foo :
    b64 [102#u8, 111#u8, 111#u8] = [90#u8, 109#u8, 57#u8, 118#u8] := by decide
theorem b64_rfc4648_foob :
    b64 [102#u8, 111#u8, 111#u8, 98#u8] = [90#u8, 109#u8, 57#u8, 118#u8, 89#u8, 103#u8] := by
  decide
theorem b64_rfc4648_fooba :
    b64 [102#u8, 111#u8, 111#u8, 98#u8, 97#u8] =
      [90#u8, 109#u8, 57#u8, 118#u8, 89#u8, 109#u8, 69#u8] := by decide
theorem b64_rfc4648_foobar :
    b64 [102#u8, 111#u8, 111#u8, 98#u8, 97#u8, 114#u8] =
      [90#u8, 109#u8, 57#u8, 118#u8, 89#u8, 109#u8, 70#u8, 121#u8] := by decide

theorem b64Decode_rfc4648_foobar :
    b64Decode [90#u8, 109#u8, 57#u8, 118#u8, 89#u8, 109#u8, 70#u8, 121#u8] =
      some [102#u8, 111#u8, 111#u8, 98#u8, 97#u8, 114#u8] := by decide
theorem b64Decode_rfc4648_fooba :
    b64Decode [90#u8, 109#u8, 57#u8, 118#u8, 89#u8, 109#u8, 69#u8] =
      some [102#u8, 111#u8, 111#u8, 98#u8, 97#u8] := by decide

/-- URL-safe symbols: `[0xfb, 0xef, 0xbe]` ↦ `----`, `[0xff, 0xff, 0xff]` ↦ `____`,
`[0xfb, 0xff]` ↦ `-_8`. -/
theorem b64_url_safe_symbols :
    b64 [251#u8, 239#u8, 190#u8] = [45#u8, 45#u8, 45#u8, 45#u8] ∧
    b64 [255#u8, 255#u8, 255#u8] = [95#u8, 95#u8, 95#u8, 95#u8] ∧
    b64 [251#u8, 255#u8] = [45#u8, 95#u8, 56#u8] := by decide

/-- The standard-alphabet symbols `+` (43) and `/` (47) are rejected. -/
theorem b64Decode_rejects_standard_symbols :
    b64Decode [43#u8, 43#u8, 43#u8, 43#u8] = none ∧
    b64Decode [47#u8, 47#u8, 47#u8, 47#u8] = none := by decide

/-- Padding is rejected: `Zg==`, `Zm8=`, `Zm9vYg==`. -/
theorem b64Decode_rejects_padding :
    b64Decode [90#u8, 103#u8, 61#u8, 61#u8] = none ∧
    b64Decode [90#u8, 109#u8, 56#u8, 61#u8] = none ∧
    b64Decode [90#u8, 109#u8, 57#u8, 118#u8, 89#u8, 103#u8, 61#u8, 61#u8] = none := by decide

/-- Non-canonical trailing bits are rejected: `Zh`, `Zm9`, `_x`; `_w` decodes to `[0xff]`. -/
theorem b64Decode_trailing_bits :
    b64Decode [90#u8, 104#u8] = none ∧
    b64Decode [90#u8, 109#u8, 57#u8] = none ∧
    b64Decode [95#u8, 120#u8] = none ∧
    b64Decode [95#u8, 119#u8] = some [255#u8] := by decide

/-- Impossible lengths and foreign bytes are rejected: `Z`, `Zm9vY`, `!!!!`, `Zm 9v`, `Zm9v
`. -/
theorem b64Decode_rejects_malformed :
    b64Decode [90#u8] = none ∧
    b64Decode [90#u8, 109#u8, 57#u8, 118#u8, 89#u8] = none ∧
    b64Decode [33#u8, 33#u8, 33#u8, 33#u8] = none ∧
    b64Decode [90#u8, 109#u8, 32#u8, 57#u8, 118#u8] = none ∧
    b64Decode [90#u8, 109#u8, 57#u8, 118#u8, 10#u8] = none := by decide

end Proofs.External.Base64
