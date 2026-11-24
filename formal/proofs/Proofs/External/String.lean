/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Rmcp.Funs
import Proofs.External.Base64

/-!
# UTF-8 facts for the `String` models

Lemmas about `ExtModel.utf8` (the bytes of a Lean `String`) and `ExtModel.strOfBytes?` (the
`String` with given bytes), used by the specs of the `String`/`str` externals
(`formal/trusted/Rmcp/FunsExternal.lean`): they are inverse to each other, `utf8` is additive and
counts `utf8ByteSize` bytes, ASCII text has one byte per character, and the Aeneas `toStr` of a
literal has the bytes `utf8` gives.

Section "Phase 2: strings and `Arc`" proves the signed-off laws of plan steps S26/S27 for
`<str as PartialEq>::eq`, `<String as Deref>::deref` and `Arc` (`deref`, `eq`). It needs
`Rmcp.Funs` for the instance `Str.Insts.CoreCmpPartialEqStr`.
-/

open Aeneas Aeneas.Std

namespace Proofs.External.Utf8

open ExtModel Proofs.External.Base64

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
    rfl
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
  rw [strOfBytes?, bytes_utf8, String.fromUTF8?, dif_pos s.isValidUTF8]
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
    · simp at h
  · intro h; subst h; exact strOfBytes?_utf8 s

/-- `strOfBytes? l = none` exactly when `l` is the encoding of no string (not UTF-8). -/
theorem strOfBytes?_eq_none_iff (l : List U8) : strOfBytes? l = none ↔ ∀ s, l ≠ utf8 s := by
  constructor
  · intro h s hs; rw [hs, strOfBytes?_utf8] at h; simp at h
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
    rw [Char.ofNat, dif_pos (Or.inl (by omega))]; simp [Char.ofNatAux]
  simp only [String.utf8EncodeChar, hv]
  rw [if_pos (by omega)]

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
      rw [List.flatMap_cons, List.map_cons, utf8EncodeChar_ofNat (h b (by simp)),
        ih (fun c hc => h c (by simp [hc]))]
      rfl
  rw [this, List.map_map]
  conv => rhs; rw [← List.map_id l]
  apply List.map_congr_left
  intro x _
  exact byte_toUInt8 x

/-- Appending an ASCII character appends its one byte. -/
theorem utf8_push_ascii (s : String) (c : Char) (h : c.toNat < 128) :
    utf8 (s.push c) = utf8 s ++ [byte c.toNat] := by
  have hc : c = Char.ofNat c.toNat := by simp
  have : s.push c = s ++ String.ofList [c] := by
    apply String.toByteArray_inj.1
    rw [String.toByteArray_push, String.toByteArray_append, String.toByteArray_ofList]
  rw [this, utf8_append]
  congr 1
  have h1 : [c] = [byte c.toNat].map (fun b => Char.ofNat b.val) := by
    rw [List.map_cons, List.map_nil, byte_val, Nat.mod_eq_of_lt (by omega), ← hc]
  rw [h1, utf8_ofList_ascii]
  intro b hb; simp at hb; subst hb; rw [byte_val]; omega

/-- An ASCII character is one byte. -/
theorem utf8_ofList_singleton_ascii (ch : Char) (h : ch.toNat < 128) :
    utf8 (String.ofList [ch]) = [byte ch.toNat] := by
  have h1 : [ch] = [byte ch.toNat].map (fun b => Char.ofNat b.val) := by
    rw [List.map_cons, List.map_nil, byte_val, Nat.mod_eq_of_lt (by omega)]; simp
  rw [h1, utf8_ofList_ascii]
  intro b hb; simp at hb; subst hb; rw [byte_val]; omega

/-- The bytes of the Aeneas `toStr` of a literal are its `utf8` bytes. -/
theorem toStr_val (s : String) (h : s.toByteArray.size ≤ U32.max) :
    (toStr s h).val = utf8 s := by
  rw [toStr, utf8]
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
  rcases System.Platform.numBits_eq with h | h <;> simp [h]

end Proofs.External.Utf8

/-! ## Phase 2: strings and `Arc` -/

open Result
open rmcp ExtModel Proofs.External.Utf8

/-- **Spec theorem for `<str as PartialEq>::eq`**: byte-list equality, for every `Str`. -/
@[step]
theorem Str.Insts.CoreCmpPartialEqStr.eq_spec (self : Str) (other : Str) :
    Str.Insts.CoreCmpPartialEqStr.eq self other ⦃ (result : Bool) =>
      (result = true ↔ self.val = other.val) ⦄ := by
  simp [Str.Insts.CoreCmpPartialEqStr.eq]

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
    dif_pos h]
  exact (WP.spec_ok (p := fun result : Str => result.val = utf8 self) _).2 rfl

/-- `<String as Deref>::deref` on a Lean `String` longer than `Usize.max` bytes (no Rust
`String` is): `fail maximumSizeExceeded`. -/
theorem alloc.string.String.Insts.CoreOpsDerefDerefStr.deref_fail
    (self : String) (h : Usize.max < self.utf8ByteSize) :
    alloc.string.String.Insts.CoreOpsDerefDerefStr.deref self = fail Error.maximumSizeExceeded := by
  rw [← length_utf8] at h
  simp only [alloc.string.String.Insts.CoreOpsDerefDerefStr.deref, alloc.string.String.as_bytes,
    dif_neg (Nat.not_le.2 h)]
  rfl

/-- **Spec theorem for `<Arc<T> as Deref>::deref`**: the shared value, for every `T` and every
allocator type `A`. -/
@[step]
theorem alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref_spec {T : Type} (A : Type)
    (self : alloc.sync.Arc T) :
    alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref A self ⦃ (result : T) =>
      result = self.data ⦄ := by
  simp [alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref]

/-- `<Arc<T> as PartialEq>::eq` is the equality of the instance of `T` on the shared values,
for every instance, including its failure. -/
theorem alloc.sync.Arc.Insts.CoreCmpPartialEqArc.eq_eq {T : Type} (A : Type)
    (corecmpPartialEqInst : core.cmp.PartialEq T T) (self : alloc.sync.Arc T)
    (other : alloc.sync.Arc T) :
    alloc.sync.Arc.Insts.CoreCmpPartialEqArc.eq A corecmpPartialEqInst self other =
      corecmpPartialEqInst.eq self.data other.data := by
  rfl

/-- **Spec theorem for `<Arc<str> as PartialEq>::eq`** at the instance of the translation:
equality of the bytes of the shared strings. -/
@[step]
theorem alloc.sync.Arc.Insts.CoreCmpPartialEqArc.eq_str_spec (A : Type)
    (self : alloc.sync.Arc Str) (other : alloc.sync.Arc Str) :
    alloc.sync.Arc.Insts.CoreCmpPartialEqArc.eq A Str.Insts.CoreCmpPartialEqStr self other
      ⦃ (result : Bool) => (result = true ↔ self.data.val = other.data.val) ⦄ := by
  rw [alloc.sync.Arc.Insts.CoreCmpPartialEqArc.eq_eq]
  exact Str.Insts.CoreCmpPartialEqStr.eq_spec self.data other.data
