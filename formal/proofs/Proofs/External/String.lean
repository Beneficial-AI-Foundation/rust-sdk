/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Rmcp.Funs
public import Proofs.External.Byte
public import Proofs.External.WP
public import Proofs.External.Base64
public import Defs.Bytes

@[expose] public section

/-!
# UTF-8 facts for the `String` models

Lemmas about `ExtModel.utf8` (the bytes of a Lean `String`) and `ExtModel.strOfBytes?` (the
`String` with given bytes), used by the specs of the `String`/`str` externals
(`formal/trusted/Rmcp/FunsExternal.lean`): they are inverse to each other, `utf8` is additive and
counts `utf8ByteSize` bytes, ASCII text has one byte per character, and the Aeneas `toStr` of a
literal has the bytes `utf8` gives. `utf8Bytes_eq_utf8` identifies `Defs.utf8Bytes` (the encoding
the Phase 2 definitions use) with `utf8`. The character-level facts `utf8_ofList`,
`utf8_ofList_cons`, `le_toNat_of_mem_utf8EncodeChar` and `le_val_of_mem_utf8_ofList_singleton`
(with `toNat_le_toNat_or`) are generic; they moved here from `Proofs.External.Skill` on
2026-11-25 (translation patch 05), so that `Proofs.External.MetadataResolver` does not import the
skills file.

Section "Phase 2: strings and `Arc`" proves the signed-off laws of plan steps S26/S27 for
`<str as PartialEq>::eq` (with the equation `eq_eq` derived from it), `<String as Deref>::deref`
and `Arc` (`deref`, `eq`), and `alloc.sync.Arc.data_val_inj` (an `Arc<str>` is determined by the
bytes it shares). The spec theorems `alloc.string.String.Insts.CoreCmpPartialEqStr.eq_spec` and
`alloc.sync.Arc.Insts.CoreCmpPartialEqArc.eq_spec` (for every instance) were added on 2026-11-25
(human decision: every external reached by the translation has a `_spec` theorem). It needs `Rmcp.Funs` for the instance `Str.Insts.CoreCmpPartialEqStr`.
-/

open Aeneas Aeneas.Std

namespace Proofs.External.Utf8

open ExtModel Proofs.External.Byte Proofs.External.Base64

theorem byteArray_toList_loop (bs : ByteArray) (i : Nat) (r : List UInt8) :
    ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
  fun_induction ByteArray.toList.loop bs i r with
  | case1 i r h ih =>
    rw [ih]
    have h' : i < bs.data.toList.length := by
      rw [Array.length_toList]; exact h
    rw [List.drop_eq_getElem_cons h', List.reverse_cons, List.append_assoc, List.singleton_append]
    congr 2
    rw [ByteArray.get!, getElem!_pos bs.data i h, Array.getElem_toList]
  | case2 i r h =>
    have h' : bs.data.toList.length ≤ i := by
      rw [Array.length_toList]; exact Nat.le_of_not_lt h
    rw [List.drop_eq_nil_of_le h', List.append_nil]

/-- `ByteArray.toList` (a loop) lists the bytes of the array. -/
theorem byteArray_toList (bs : ByteArray) : bs.toList = bs.data.toList := by
  rw [ByteArray.toList, byteArray_toList_loop, List.reverse_nil, List.nil_append, List.drop_zero]

theorem toUInt8_byte (x : UInt8) : (byte x.toNat).val.toUInt8 = x := by
  rw [byte_val, Nat.mod_eq_of_lt (UInt8.toNat_lt x)]; exact UInt8.ofNat_toNat

theorem byte_toUInt8 (x : U8) : byte x.val.toUInt8.toNat = x := by
  apply byte_eq
  rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (val_lt x)]

theorem utf8_eq (s : String) : utf8 s = s.toByteArray.data.toList.map (fun x => byte x.toNat) := by
  rw [utf8, byteArray_toList]

/-- `Defs.utf8Bytes`, the encoding of the Phase 2 definitions, is the trusted model's
`ExtModel.utf8`, by definition. -/
theorem utf8Bytes_eq_utf8 (s : String) : Defs.utf8Bytes s = ExtModel.utf8 s := rfl

/-- `utf8 s` has `s.utf8ByteSize` bytes. -/
theorem length_utf8 (s : String) : (utf8 s).length = s.utf8ByteSize := by
  rw [utf8_eq, List.length_map, Array.length_toList]; rfl

@[simp] theorem utf8_empty : utf8 "" = [] := by
  rw [utf8_eq]; rfl

/-- `utf8` is additive. -/
theorem utf8_append (s t : String) : utf8 (s ++ t) = utf8 s ++ utf8 t := by
  rw [utf8_eq, utf8_eq, utf8_eq, String.toByteArray_append, ByteArray.toList_data_append,
    List.map_append]

theorem bytes_utf8 (s : String) :
    (⟨((utf8 s).map (fun b => b.val.toUInt8)).toArray⟩ : ByteArray) = s.toByteArray := by
  rw [utf8_eq, List.map_map]
  have : ((fun b : U8 => b.val.toUInt8) ∘ fun x : UInt8 => byte x.toNat) = id := by
    funext x; exact toUInt8_byte x
  rw [this, List.map_id, Array.toArray_toList]

/-- `strOfBytes?` inverts `utf8`. -/
theorem strOfBytes?_utf8 (s : String) : strOfBytes? (utf8 s) = some s := by
  rw [strOfBytes?, bytes_utf8, String.fromUTF8?, dite_eq_left s.isValidUTF8]
  rfl

/-- `strOfBytes? l = some s` exactly when `l` is the UTF-8 encoding of `s`. -/
theorem strOfBytes?_eq_some_iff (l : List U8) (s : String) :
    strOfBytes? l = some s ↔ l = utf8 s := by
  constructor
  · intro h
    rw [strOfBytes?, String.fromUTF8?] at h
    split at h
    · rename_i hv
      simp only [Option.some.injEq] at h
      subst h
      rw [utf8_eq]
      change l = (List.map (fun b : U8 => b.val.toUInt8) l).toArray.toList.map _
      rw [List.toList_toArray, List.map_map]
      conv => lhs; rw [← List.map_id l]
      apply List.map_congr_left
      intro x _
      exact (byte_toUInt8 x).symm
    · simp only [reduceCtorEq] at h
  · intro h; subst h; exact strOfBytes?_utf8 s

/-- `strOfBytes? l = none` exactly when `l` is the encoding of no string (not UTF-8). -/
theorem strOfBytes?_eq_none_iff (l : List U8) : strOfBytes? l = none ↔ ∀ s, l ≠ utf8 s := by
  constructor
  · intro h s hs; rw [hs, strOfBytes?_utf8] at h; simp only [reduceCtorEq] at h
  · intro h
    cases hl : strOfBytes? l with
    | none => rfl
    | some s => exact absurd ((strOfBytes?_eq_some_iff l s).1 hl) (h s)

/-- Two strings with the same bytes are equal. -/
theorem utf8_injective {s t : String} (h : utf8 s = utf8 t) : s = t := by
  have := strOfBytes?_utf8 s
  rw [h, strOfBytes?_utf8] at this
  exact (Option.some.inj this).symm

theorem utf8EncodeChar_ofNat {n : Nat} (h : n < 128) :
    String.utf8EncodeChar (Char.ofNat n) = [UInt8.ofNat n] := by
  have hv : (Char.ofNat n).val.toNat = n := by
    rw [Char.ofNat, dite_eq_left (Or.inl (by omega))]
    simp only [Char.ofNatAux, UInt32.ofBitVec_ofNatLT, UInt32.toNat_ofNatLT]
  simp only [String.utf8EncodeChar, hv]
  rw [ite_eq_left (by omega)]

/-- ASCII bytes, as characters, encode to themselves. -/
theorem utf8_ofList_ascii (l : List U8) (h : ∀ b ∈ l, b.val < 128) :
    utf8 (String.ofList (l.map (fun b => Char.ofNat b.val))) = l := by
  rw [utf8_eq, String.toByteArray_ofList, List.utf8Encode, List.toList_data_toByteArray,
    List.flatMap_map]
  have : l.flatMap (fun b => String.utf8EncodeChar (Char.ofNat b.val)) =
      l.map (fun b => UInt8.ofNat b.val) := by
    induction l with
    | nil => rfl
    | cons b t ih =>
      rw [List.flatMap_cons, List.map_cons, utf8EncodeChar_ofNat (h b List.mem_cons_self),
        ih (fun c hc => h c (List.mem_cons_of_mem b hc))]
      rfl
  rw [this, List.map_map]
  conv => rhs; rw [← List.map_id l]
  apply List.map_congr_left
  intro x _
  exact byte_toUInt8 x

/-- Appending an ASCII character appends its one byte. -/
theorem utf8_push_ascii (s : String) (c : Char) (h : c.toNat < 128) :
    utf8 (s.push c) = utf8 s ++ [byte c.toNat] := by
  have hc : c = Char.ofNat c.toNat := (Char.ofNat_toNat c).symm
  have : s.push c = s ++ String.ofList [c] := by
    apply String.toByteArray_inj.1
    rw [String.toByteArray_push, String.toByteArray_append, String.toByteArray_ofList]
  rw [this, utf8_append]
  congr 1
  have h1 : [c] = [byte c.toNat].map (fun b => Char.ofNat b.val) := by
    rw [List.map_cons, List.map_nil, byte_val, Nat.mod_eq_of_lt (by omega), ← hc]
  rw [h1, utf8_ofList_ascii]
  intro b hb
  rw [List.mem_singleton] at hb
  subst hb; rw [byte_val]; omega

/-- An ASCII character is one byte. -/
theorem utf8_ofList_singleton_ascii (ch : Char) (h : ch.toNat < 128) :
    utf8 (String.ofList [ch]) = [byte ch.toNat] := by
  have h1 : [ch] = [byte ch.toNat].map (fun b => Char.ofNat b.val) := by
    rw [List.map_cons, List.map_nil, byte_val, Nat.mod_eq_of_lt (by omega), Char.ofNat_toNat]
  rw [h1, utf8_ofList_ascii]
  intro b hb
  rw [List.mem_singleton] at hb
  subst hb; rw [byte_val]; omega

/-- A byte `x ||| k` is at least `k`. -/
theorem toNat_le_toNat_or (x k : UInt8) : k.toNat ≤ (x ||| k).toNat := by
  rw [UInt8.toNat_or]; exact Nat.right_le_or

/-- Every byte of the UTF-8 encoding of a non-ASCII character is at least 128. -/
theorem le_toNat_of_mem_utf8EncodeChar {c : Char} (hc : 128 ≤ c.toNat) :
    ∀ b ∈ String.utf8EncodeChar c, 128 ≤ b.toNat := by
  have h1 : c.utf8Size ≠ 1 := by
    intro h
    have h' := UInt32.le_iff_toNat_le.1 (Char.utf8Size_eq_one_iff.1 h)
    have : c.toNat = c.val.toNat := rfl
    have : (127 : UInt32).toNat = 127 := rfl
    omega
  have hpos := Char.utf8Size_pos c
  have hle := Char.utf8Size_le_four c
  have h2 : ∀ x : UInt8, 128 ≤ (x ||| 0x80).toNat := fun x => toNat_le_toNat_or x 0x80
  have h3 : ∀ x : UInt8, 128 ≤ (x ||| 0xc0).toNat :=
    fun x => le_trans (by decide) (toNat_le_toNat_or x 0xc0)
  have h4 : ∀ x : UInt8, 128 ≤ (x ||| 0xe0).toNat :=
    fun x => le_trans (by decide) (toNat_le_toNat_or x 0xe0)
  have h5 : ∀ x : UInt8, 128 ≤ (x ||| 0xf0).toNat :=
    fun x => le_trans (by decide) (toNat_le_toNat_or x 0xf0)
  intro b hb
  rcases (by omega : c.utf8Size = 2 ∨ c.utf8Size = 3 ∨ c.utf8Size = 4) with h | h | h
  · rw [String.utf8EncodeChar_eq_cons_cons h] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> simp only [h2, h3]
  · rw [String.utf8EncodeChar_eq_cons_cons_cons h] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> simp only [h2, h4]
  · rw [String.utf8EncodeChar_eq_cons_cons_cons_cons h] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> simp only [h2, h5]

/-- The UTF-8 bytes of a string of characters: the encodings of the characters, in order. -/
theorem utf8_ofList (cs : List Char) :
    utf8 (String.ofList cs) =
      cs.flatMap (fun c => (String.utf8EncodeChar c).map (fun x => byte x.toNat)) := by
  rw [utf8_eq, String.toByteArray_ofList, List.utf8Encode, List.toList_data_toByteArray,
    List.map_flatMap]

/-- The UTF-8 bytes of `c :: cs` are those of `c` followed by those of `cs`. -/
theorem utf8_ofList_cons (c : Char) (cs : List Char) :
    utf8 (String.ofList (c :: cs)) = utf8 (String.ofList [c]) ++ utf8 (String.ofList cs) := by
  rw [utf8_ofList, utf8_ofList, utf8_ofList, List.flatMap_cons, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]

/-- Every UTF-8 byte of a non-ASCII character is at least 128. -/
theorem le_val_of_mem_utf8_ofList_singleton {c : Char} (hc : 128 ≤ c.toNat) :
    ∀ b ∈ utf8 (String.ofList [c]), 128 ≤ b.val := by
  intro b hb
  rw [utf8_ofList, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_map] at hb
  obtain ⟨x, hx, rfl⟩ := hb
  have := le_toNat_of_mem_utf8EncodeChar hc x hx
  rw [byte_val, Nat.mod_eq_of_lt x.toNat_lt]
  exact this

/-- The bytes of the Aeneas `toStr` of a literal are its `utf8` bytes. -/
theorem toStr_val (s : String) (h : s.toByteArray.size ≤ U32.max) :
    (toStr s h).val = utf8 s := by
  rw [toStr, utf8, Slice.from_val]
  apply List.map_congr_left
  intro x _
  apply UScalar.eq_of_val_eq
  rw [byte_val, Nat.mod_eq_of_lt (UInt8.toNat_lt x)]
  rfl

/-- Every symbol of an encoding is ASCII. -/
theorem val_lt_128_of_mem_b64 (x : List U8) : ∀ b ∈ b64 x, b.val < 128 := by
  intro b hb
  have := (isSome_b64Val_iff b).1 (isSome_b64Val_of_mem_b64 x b hb)
  omega

/-- A Rust `String` length (at most `isize::MAX`) fits in a `usize`, so the bytes of any
`String` the models produce form a `Slice`. -/
theorem maxStringBytes_le_usize_max : maxStringBytes ≤ Usize.max := by
  simp only [maxStringBytes, Isize.max, Usize.max, Isize.numBits, Usize.numBits]
  rcases System.Platform.numBits_eq with h | h <;>
    simp only [IScalarTy.Isize_numBits_eq, UScalarTy.Usize_numBits_eq, h] <;> decide

end Proofs.External.Utf8

/-! ## Phase 2: strings and `Arc` -/

open Result
open rmcp ExtModel Proofs.External.Utf8

/-- **Spec theorem for `<str as PartialEq>::eq`**: byte-list equality, for every `Str`. -/
@[step]
theorem Str.Insts.CoreCmpPartialEqStr.eq_spec (self : Str) (other : Str) :
    Str.Insts.CoreCmpPartialEqStr.eq self other ⦃ (result : Bool) =>
      (result = true ↔ self.val = other.val) ⦄ := by
  simp only [Str.Insts.CoreCmpPartialEqStr.eq, WP.spec_ok, decide_eq_true_eq]

/-- `<str as PartialEq>::eq` as an equation, for rewriting inside a `do` block; from
`Str.Insts.CoreCmpPartialEqStr.eq_spec`. -/
theorem Str.Insts.CoreCmpPartialEqStr.eq_eq (self : Str) (other : Str) :
    Str.Insts.CoreCmpPartialEqStr.eq self other = ok (decide (self.val = other.val)) := by
  obtain ⟨b, hb, hbv⟩ :=
    Proofs.External.WP.exists_ok_of_spec (Str.Insts.CoreCmpPartialEqStr.eq_spec self other)
  rw [hb, Bool.eq_iff_iff.2 (hbv.trans decide_eq_true_iff.symm)]

/-- **Spec theorem for `<String as PartialEq<str>>::eq`**: the UTF-8 bytes of the string are the
bytes of the `str`, for every `String` and `Str`; never fails. -/
@[step]
theorem alloc.string.String.Insts.CoreCmpPartialEqStr.eq_spec (self : String) (other : Str) :
    alloc.string.String.Insts.CoreCmpPartialEqStr.eq self other ⦃ (result : Bool) =>
      (result = true ↔ utf8 self = other.val) ⦄ := by
  simp only [alloc.string.String.Insts.CoreCmpPartialEqStr.eq, WP.spec_ok, decide_eq_true_eq]

/-- **Spec theorem for `<String as Deref<Target = str>>::deref`**: the UTF-8 bytes of the
string. The precondition holds for every Rust `String` (at most `isize::MAX` bytes); see
`deref_fail`. -/
@[step]
theorem alloc.string.String.Insts.CoreOpsDerefDerefStr.deref_spec
    (self : String) (h : self.utf8ByteSize ≤ Usize.max) :
    alloc.string.String.Insts.CoreOpsDerefDerefStr.deref self ⦃ (result : Str) =>
      result.val = utf8 self ⦄ := by
  rw [← length_utf8] at h
  simp only [alloc.string.String.Insts.CoreOpsDerefDerefStr.deref, alloc.string.String.as_bytes,
    dite_eq_left h]
  exact (WP.spec_ok (p := fun result : Str => result.val = utf8 self) _).2 (Slice.from_val _ _)

/-- `<String as Deref>::deref` on a Lean `String` longer than `Usize.max` bytes (no Rust
`String` is): `fail maximumSizeExceeded`. -/
theorem alloc.string.String.Insts.CoreOpsDerefDerefStr.deref_fail
    (self : String) (h : Usize.max < self.utf8ByteSize) :
    alloc.string.String.Insts.CoreOpsDerefDerefStr.deref self = fail Error.maximumSizeExceeded := by
  rw [← length_utf8] at h
  simp only [alloc.string.String.Insts.CoreOpsDerefDerefStr.deref, alloc.string.String.as_bytes,
    dite_eq_right (Nat.not_le.2 h)]
  rfl

/-- **Spec theorem for `<Arc<T> as Deref>::deref`**: the shared value, for every `T` and every
allocator type `A`. -/
@[step]
theorem alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref_spec {T : Type} (A : Type)
    (self : alloc.sync.Arc T) :
    alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref A self ⦃ (result : T) =>
      result = self.data ⦄ := by
  simp only [alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref, WP.spec_ok]

/-- `<Arc<T> as PartialEq>::eq` is the equality of the instance of `T` on the shared values,
for every instance, including its failure. -/
theorem alloc.sync.Arc.Insts.CoreCmpPartialEqArc.eq_eq {T : Type} (A : Type)
    (corecmpPartialEqInst : core.cmp.PartialEq T T) (self : alloc.sync.Arc T)
    (other : alloc.sync.Arc T) :
    alloc.sync.Arc.Insts.CoreCmpPartialEqArc.eq A corecmpPartialEqInst self other =
      corecmpPartialEqInst.eq self.data other.data := by
  rfl

/-- **Spec theorem for `<Arc<T> as PartialEq>::eq`**, for every `T`, allocator type `A` and
instance: the result meets every postcondition that the instance's `eq` on the shared values
meets (from `eq_eq`); `eq_str_spec` is the instance of the translation. -/
theorem alloc.sync.Arc.Insts.CoreCmpPartialEqArc.eq_spec {T : Type} (A : Type)
    (corecmpPartialEqInst : core.cmp.PartialEq T T) (self : alloc.sync.Arc T)
    (other : alloc.sync.Arc T) (P : Bool → Prop)
    (h : corecmpPartialEqInst.eq self.data other.data ⦃ P ⦄) :
    alloc.sync.Arc.Insts.CoreCmpPartialEqArc.eq A corecmpPartialEqInst self other ⦃ P ⦄ := by
  rw [alloc.sync.Arc.Insts.CoreCmpPartialEqArc.eq_eq]
  exact h

/-- **Spec theorem for `<Arc<str> as PartialEq>::eq`** at the instance of the translation:
equality of the bytes of the shared strings. -/
@[step]
theorem alloc.sync.Arc.Insts.CoreCmpPartialEqArc.eq_str_spec (A : Type)
    (self : alloc.sync.Arc Str) (other : alloc.sync.Arc Str) :
    alloc.sync.Arc.Insts.CoreCmpPartialEqArc.eq A Str.Insts.CoreCmpPartialEqStr self other
      ⦃ (result : Bool) => (result = true ↔ self.data.val = other.data.val) ⦄ := by
  rw [alloc.sync.Arc.Insts.CoreCmpPartialEqArc.eq_eq]
  exact Str.Insts.CoreCmpPartialEqStr.eq_spec self.data other.data

/-- Two `Arc<str>` are equal exactly when their shared strings have the same bytes. -/
theorem alloc.sync.Arc.data_val_inj {a b : alloc.sync.Arc Str} :
    a.data.val = b.data.val ↔ a = b := by
  obtain ⟨x⟩ := a
  obtain ⟨y⟩ := b
  exact ⟨fun h => congrArg alloc.sync.Arc.mk (Slice.ext _ _ h), fun h => by cases h; rfl⟩
