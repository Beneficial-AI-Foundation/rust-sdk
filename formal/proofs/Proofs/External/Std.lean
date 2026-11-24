/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Rmcp.Funs
import Proofs.External.String

/-!
# Specs of the standard-library, `HashMap`, `zeroize` and clock externals

Spec theorems for the models in `formal/trusted/Rmcp/FunsExternal.lean` (sections Standard
library and Clock). Each covers success and, where the model can fail, the failure. Names follow
the style guide: the full generated name of the external with `_spec`; equation lemmas for
functions that take a trait instance whose behaviour is not fixed (`map_err`, `clone`, ...), and
for `ok_or` and `is_err` (`ok_or_eq`, `is_err_eq`, from their spec theorems, for rewriting inside
a `do` block).

Section "Phase 2: slices and ranges" proves the signed-off laws of plan steps S26/S27 for
`slice::first`, `<[T; N] as SlicePattern>::as_slice`, `[T] == [U; N]`, `slice::strip_suffix`
and `RangeInclusive::contains`.
-/

open Aeneas Aeneas.Std Result

open ExtModel Proofs.External.Utf8 Proofs.External.Base64

/-! ## `core` -/

/-- **Spec theorem for `core::borrow::{impl Borrow<T> for T}::borrow`**: the identity. -/
@[step]
theorem core.borrow.Borrow.Blanket.borrow_spec {T : Type} (self : T) :
    core.borrow.Borrow.Blanket.borrow self ⦃ (result : T) => result = self ⦄ := by
  simp only [core.borrow.Borrow.Blanket.borrow, WP.spec_ok]

/-- **Spec theorem for `core::option::Option::ok_or`**: `Some v ↦ Ok v`, `None ↦ Err err`. -/
@[step]
theorem core.option.Option.ok_or_spec {T : Type} {E : Type} (self : Option T) (err : E) :
    core.option.Option.ok_or self err ⦃ (result : core.result.Result T E) =>
      result = match self with
        | some v => core.result.Result.Ok v
        | none => core.result.Result.Err err ⦄ := by
  match self with
  | some _ => simp only [core.option.Option.ok_or, WP.spec_ok]
  | none => simp only [core.option.Option.ok_or, WP.spec_ok]

/-- `Option::ok_or` as an equation, for rewriting inside a `do` block; from
`core.option.Option.ok_or_spec`. -/
theorem core.option.Option.ok_or_eq {T E : Type} (o : Option T) (err : E) :
    core.option.Option.ok_or o err = Aeneas.Std.Result.ok (match o with
      | some v => core.result.Result.Ok v
      | none => core.result.Result.Err err) := by
  obtain ⟨r, hr, h⟩ :=
    Proofs.External.WP.exists_ok_of_spec (core.option.Option.ok_or_spec o err)
  rw [hr, h]

/-- **Spec theorem for `<Option<T> as Default>::default`**: `None`. -/
@[step]
theorem core.option.Option.Insts.CoreDefaultDefault.default_spec (T : Type) :
    core.option.Option.Insts.CoreDefaultDefault.default T ⦃ (result : Option T) =>
      result = none ⦄ := by
  simp only [core.option.Option.Insts.CoreDefaultDefault.default, WP.spec_ok]

/-- **Spec theorem for `core::result::Result::is_err`**: `true` exactly for `Err`. -/
@[step]
theorem core.result.Result.is_err_spec {T : Type} {E : Type} (self : core.result.Result T E) :
    core.result.Result.is_err self ⦃ (result : Bool) =>
      result = match self with
        | core.result.Result.Ok _ => false
        | core.result.Result.Err _ => true ⦄ := by
  match self with
  | core.result.Result.Ok _ => simp only [core.result.Result.is_err, WP.spec_ok]
  | core.result.Result.Err _ => simp only [core.result.Result.is_err, WP.spec_ok]

/-- `Result::is_err` as an equation, for rewriting inside a `do` block; from
`core.result.Result.is_err_spec`. -/
theorem core.result.Result.is_err_eq {T E : Type} (r : core.result.Result T E) :
    core.result.Result.is_err r = Aeneas.Std.Result.ok (match r with
      | core.result.Result.Ok _ => false
      | core.result.Result.Err _ => true) := by
  obtain ⟨b, hb, h⟩ :=
    Proofs.External.WP.exists_ok_of_spec (core.result.Result.is_err_spec r)
  rw [hb, h]

/-- `core::result::Result::map_err` on `Ok`: unchanged, the closure is not called. -/
@[simp]
theorem core.result.Result.map_err_ok {T E F O : Type}
    (inst : core.ops.function.FnOnce O E F) (t : T) (op : O) :
    core.result.Result.map_err inst (core.result.Result.Ok t : core.result.Result T E) op =
      Aeneas.Std.Result.ok (core.result.Result.Ok t) := rfl

/-- `core::result::Result::map_err` on `Err e`: `Err (op e)`; the closure's failure
propagates. -/
@[simp]
theorem core.result.Result.map_err_err {T E F O : Type}
    (inst : core.ops.function.FnOnce O E F) (e : E) (op : O) :
    core.result.Result.map_err inst (core.result.Result.Err e : core.result.Result T E) op =
      (do let f ← inst.call_once op e; Aeneas.Std.Result.ok (core.result.Result.Err f)) := rfl

/-- **Spec theorem for `<&[T] as Default>::default`**: the empty slice. -/
@[step]
theorem Shared0Slice.Insts.CoreDefaultDefault.default_spec (T : Type) :
    Shared0Slice.Insts.CoreDefaultDefault.default T ⦃ (result : Slice T) =>
      result.val = [] ⦄ := by
  simp only [Shared0Slice.Insts.CoreDefaultDefault.default, Slice.new, WP.spec_ok]

/-- **Spec theorem for `core::str::str::len`**: the number of bytes; for every `Str`. -/
@[step]
theorem core.str.Str.len_spec (self : Str) :
    core.str.Str.len self ⦃ (result : Usize) => result.val = self.val.length ⦄ := by
  simp only [core.str.Str.len, WP.spec_ok, Usize.ofNatCore_val_eq]

/-- **Spec theorem for `core::str::str::as_bytes`**: the same bytes; for every `Str`. -/
@[step]
theorem core.str.Str.as_bytes_spec (self : Str) :
    core.str.Str.as_bytes self ⦃ (result : Slice U8) => result.val = self.val ⦄ := by
  simp only [core.str.Str.as_bytes, WP.spec_ok]

/-! ## `alloc::string::String` -/

/-- **Spec theorem for `String::with_capacity`**: the empty string, if `capacity ≤ isize::MAX`
(else `with_capacity_fail`). -/
@[step]
theorem alloc.string.String.with_capacity_spec (capacity : Usize)
    (h : capacity.val ≤ maxStringBytes) :
    alloc.string.String.with_capacity capacity ⦃ (result : String) => result = "" ⦄ := by
  simp only [alloc.string.String.with_capacity, h, ↓reduceIte, WP.spec_ok]

/-- `String::with_capacity` panics ("capacity overflow") above `isize::MAX`. -/
theorem alloc.string.String.with_capacity_fail (capacity : Usize)
    (h : maxStringBytes < capacity.val) :
    alloc.string.String.with_capacity capacity = fail Error.panic := by
  simp only [alloc.string.String.with_capacity, Nat.not_le.2 h, ↓reduceIte]

/-- **Spec theorem for `String::push_str`**: for a UTF-8 argument (`string` is the bytes of `t`,
as every Rust `&str` is) whose result fits in a `String`, appends `t`; the result's bytes are
the old bytes followed by `string`. -/
@[step]
theorem alloc.string.String.push_str_spec (self : String) (string : Str) (t : String)
    (ht : string.val = utf8 t) (h : self.utf8ByteSize + string.val.length ≤ maxStringBytes) :
    alloc.string.String.push_str self string ⦃ (result : String) =>
      result = self ++ t ∧ utf8 result = utf8 self ++ string.val ⦄ := by
  have hlen : (self ++ t).utf8ByteSize ≤ maxStringBytes := by
    rw [String.utf8ByteSize_append, ← length_utf8 t, ← ht]; exact h
  simp only [alloc.string.String.push_str, ht, strOfBytes?_utf8, growString, if_pos hlen,
    WP.spec_ok, utf8_append, true_and]

/-- `String::push_str` with a result beyond `isize::MAX` bytes panics. -/
theorem alloc.string.String.push_str_fail (self : String) (string : Str) (t : String)
    (ht : string.val = utf8 t) (h : maxStringBytes < self.utf8ByteSize + string.val.length) :
    alloc.string.String.push_str self string = fail Error.panic := by
  have hlen : ¬ (self ++ t).utf8ByteSize ≤ maxStringBytes := by
    rw [String.utf8ByteSize_append, ← length_utf8 t, ← ht]; omega
  simp only [alloc.string.String.push_str, ht, strOfBytes?_utf8, growString, if_neg hlen]

/-- `String::push_str` with bytes that are not UTF-8 (no Rust `&str`) is outside the Rust
domain: `fail undef`. -/
theorem alloc.string.String.push_str_not_utf8 (self : String) (string : Str)
    (h : ∀ t, string.val ≠ utf8 t) :
    alloc.string.String.push_str self string = fail Error.undef := by
  simp only [alloc.string.String.push_str, (strOfBytes?_eq_none_iff _).2 h]

/-- **Spec theorem for `String::push`**: appends the character if the result fits in a
`String`; the result's bytes are the old bytes followed by the character's encoding. -/
@[step]
theorem alloc.string.String.push_spec (self : String) (ch : Char)
    (h : self.utf8ByteSize + ch.utf8Size ≤ maxStringBytes) :
    alloc.string.String.push self ch ⦃ (result : String) =>
      result = self.push ch ∧ utf8 result = utf8 self ++ utf8 (String.ofList [ch]) ⦄ := by
  have hlen : (self.push ch).utf8ByteSize ≤ maxStringBytes := by
    rw [String.utf8ByteSize_push]; exact h
  have hp : self.push ch = self ++ String.ofList [ch] := by
    apply String.toByteArray_inj.1
    rw [String.toByteArray_push, String.toByteArray_append, String.toByteArray_ofList]
  simp only [alloc.string.String.push, growString, if_pos hlen, WP.spec_ok, true_and]
  rw [hp, utf8_append]

/-- `String::push` with a result beyond `isize::MAX` bytes panics. -/
theorem alloc.string.String.push_fail (self : String) (ch : Char)
    (h : maxStringBytes < self.utf8ByteSize + ch.utf8Size) :
    alloc.string.String.push self ch = fail Error.panic := by
  have hlen : ¬ (self.push ch).utf8ByteSize ≤ maxStringBytes := by
    rw [String.utf8ByteSize_push]; omega
  simp only [alloc.string.String.push, growString, if_neg hlen]

/-- **Spec theorem for `String::as_bytes`**: the UTF-8 bytes. The precondition holds for every
Rust `String` (at most `isize::MAX` bytes); see `as_bytes_fail`. -/
@[step]
theorem alloc.string.String.as_bytes_spec (self : String) (h : self.utf8ByteSize ≤ Usize.max) :
    alloc.string.String.as_bytes self ⦃ (result : Slice U8) => result.val = utf8 self ⦄ := by
  rw [← length_utf8] at h
  simp only [alloc.string.String.as_bytes, h, ↓reduceDIte, WP.spec_ok]

/-- `String::as_bytes` on a Lean `String` longer than `Usize.max` bytes (no Rust `String`). -/
theorem alloc.string.String.as_bytes_fail (self : String) (h : Usize.max < self.utf8ByteSize) :
    alloc.string.String.as_bytes self = fail Error.maximumSizeExceeded := by
  rw [← length_utf8] at h
  simp only [alloc.string.String.as_bytes, Nat.not_le.2 h, ↓reduceDIte]

/-- **Spec theorem for `String::from_utf8`**: `Ok s` when the bytes are the encoding of `s`;
otherwise `Err` carrying the bytes. -/
@[step]
theorem alloc.string.String.from_utf8_spec (vec : alloc.vec.Vec U8) :
    alloc.string.String.from_utf8 vec ⦃ (result : core.result.Result String
        alloc.string.FromUtf8Error) =>
      match result with
      | core.result.Result.Ok s => vec.val = utf8 s
      | core.result.Result.Err e => (∀ s, vec.val ≠ utf8 s) ∧ e.bytes = vec ⦄ := by
  unfold alloc.string.String.from_utf8
  split
  · rename_i s hs; simpa only [ne_eq, WP.spec_ok] using (strOfBytes?_eq_some_iff _ _).1 hs
  · rename_i hs; simpa only [ne_eq, WP.spec_ok, and_true] using (strOfBytes?_eq_none_iff _).1 hs

/-- **Spec theorem for `<String as PartialEq>::eq`**: equality. -/
@[step]
theorem alloc.string.String.Insts.CoreCmpPartialEqString.eq_spec (self : String)
    (other : String) :
    alloc.string.String.Insts.CoreCmpPartialEqString.eq self other ⦃ (result : Bool) =>
      result = decide (self = other) ⦄ := by
  simp only [alloc.string.String.Insts.CoreCmpPartialEqString.eq, WP.spec_ok]

/-- **Spec theorem for `<String as Eq>::assert_fields_are_eq`**: succeeds. -/
@[step]
theorem alloc.string.String.Insts.CoreCmpEq.assert_fields_are_eq_spec (self : String) :
    alloc.string.String.Insts.CoreCmpEq.assert_fields_are_eq self ⦃ (_ : Unit) => True ⦄ := by
  simp only [alloc.string.String.Insts.CoreCmpEq.assert_fields_are_eq, WP.spec_ok]

/-- **Spec theorem for `<String as Clone>::clone`**: the same string. -/
@[step]
theorem alloc.string.String.Insts.CoreCloneClone.clone_spec (self : String) :
    alloc.string.String.Insts.CoreCloneClone.clone self ⦃ (result : String) =>
      result = self ⦄ := by
  simp only [alloc.string.String.Insts.CoreCloneClone.clone, WP.spec_ok]

/-- `<String as Hash>::hash` writes the bytes and then `0xff` (for a Rust-sized `String`). -/
theorem alloc.string.String.Insts.CoreHashHash.hash_eq {H : Type}
    (inst : core.hash.Hasher H) (self : String) (state : H)
    (h : self.utf8ByteSize ≤ Usize.max) :
    alloc.string.String.Insts.CoreHashHash.hash inst self state =
      (do
        let state ← inst.write state ⟨utf8 self, by rw [length_utf8]; exact h⟩
        inst.write state ⟨[byte 255], by scalar_tac⟩) := by
  have h' : (utf8 self).length ≤ Usize.max := by rw [length_utf8]; exact h
  simp only [alloc.string.String.Insts.CoreHashHash.hash, alloc.string.String.as_bytes, h',
    ↓reduceDIte, bind_tc_ok]

/-! ## `Vec`, hashing, `HashMap` -/

/-- **Spec theorem for `Vec::is_empty`**: `true` exactly for the empty vector. -/
@[step]
theorem alloc.vec.Vec.is_empty_spec {T : Type} (A : Type) (self : alloc.vec.Vec T) :
    alloc.vec.Vec.is_empty A self ⦃ (result : Bool) => result = decide (self.val = []) ⦄ := by
  simp only [alloc.vec.Vec.is_empty, List.length_eq_zero_iff, WP.spec_ok]

/-- **Spec theorem for `<RandomState as Clone>::clone`**: the same value. -/
@[step]
theorem std.hash.random.RandomState.Insts.CoreCloneClone.clone_spec
    (self : std.hash.random.RandomState) :
    std.hash.random.RandomState.Insts.CoreCloneClone.clone self ⦃
      (result : std.hash.random.RandomState) => result = self ⦄ := by
  simp only [std.hash.random.RandomState.Insts.CoreCloneClone.clone, WP.spec_ok]

/-- **Spec theorem for `<RandomState as BuildHasher>::build_hasher`**: the map's keys, no
bytes written. -/
@[step]
theorem std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher.build_hasher_spec
    (self : std.hash.random.RandomState) :
    std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher.build_hasher self ⦃
      (result : std.hash.random.DefaultHasher) =>
        result = { k0 := self.k0, k1 := self.k1, written := [] } ⦄ := by
  simp only [std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher.build_hasher,
    WP.spec_ok]

/-- **Spec theorem for `<DefaultHasher as Hasher>::write`**: appends the bytes. -/
@[step]
theorem std.hash.random.DefaultHasher.Insts.CoreHashHasher.write_spec
    (self : std.hash.random.DefaultHasher) (msg : Slice U8) :
    std.hash.random.DefaultHasher.Insts.CoreHashHasher.write self msg ⦃
      (result : std.hash.random.DefaultHasher) =>
        result = { self with written := self.written ++ msg.val } ⦄ := by
  simp only [std.hash.random.DefaultHasher.Insts.CoreHashHasher.write, WP.spec_ok]

/-- **Spec theorem for `<DefaultHasher as Hasher>::finish`**: SipHash-1-3 of keys and bytes. -/
@[step]
theorem std.hash.random.DefaultHasher.Insts.CoreHashHasher.finish_spec
    (self : std.hash.random.DefaultHasher) :
    std.hash.random.DefaultHasher.Insts.CoreHashHasher.finish self ⦃ (result : U64) =>
      result = sipHash13 self.k0 self.k1 self.written ⦄ := by
  simp only [std.hash.random.DefaultHasher.Insts.CoreHashHasher.finish, WP.spec_ok]

/-- `HashMap::get` is the lookup `ExtModel.HashMap.find` over the entries, whatever the
hashing instances. -/
theorem std.collections.hash.map.HashMap.get_eq
    {K V S A Q Clause2_Hasher : Type} (eqK : core.cmp.Eq K) (hashK : core.hash.Hash K)
    (bh : rmcp.core.hash.BuildHasher S Clause2_Hasher) (borrow : rmcp.core.borrow.Borrow K Q)
    (hashQ : core.hash.Hash Q) (eqQ : core.cmp.Eq Q)
    (self : std.collections.hash.map.HashMap K V S A) (k : Q) :
    std.collections.hash.map.HashMap.get eqK hashK bh borrow hashQ eqQ self k =
      ExtModel.HashMap.find borrow eqQ k self.entries := rfl

namespace Proofs.External.HashMap

/-- Lookup with the `String` instances is `List.find?` by key equality. -/
theorem find_string {V : Type} (q : String) :
    ∀ entries : List (String × V),
      ExtModel.HashMap.find (rmcp.core.borrow.Borrow.Blanket String)
        rmcp.alloc.string.String.Insts.CoreCmpEq q entries =
      ok ((entries.find? (fun e => decide (e.1 = q))).map Prod.snd)
  | [] => rfl
  | (k, v) :: rest => by
    simp only [ExtModel.HashMap.find, rmcp.core.borrow.Borrow.Blanket,
      core.borrow.Borrow.Blanket.borrow, rmcp.alloc.string.String.Insts.CoreCmpEq,
      rmcp.alloc.string.String.Insts.CoreCmpPartialEqString,
      alloc.string.String.Insts.CoreCmpPartialEqString.eq, bind_tc_ok, List.find?_cons]
    by_cases h : q = k
    · subst h; simp only [decide_true, ↓reduceIte, Option.map_some]
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, Ne.symm h]
      exact find_string q rest

end Proofs.External.HashMap

/-- **Spec theorem for `HashMap::get`** at the instance of the translation (`K = Q = String`,
`S = RandomState`): the value of the first entry whose key is `k`. With pairwise distinct keys
(the Rust invariant) this is the value stored under `k`
(`Proofs.External.HashMap.find?_key_of_mem`), and `None` when `k` is not a key
(`Proofs.External.HashMap.find?_key_of_not_mem`); without distinct keys, a value is found exactly
when `k` is a key (`Proofs.External.HashMap.find?_key_isSome_iff`). -/
@[step]
theorem std.collections.hash.map.HashMap.get_string_spec {V A : Type}
    (self : std.collections.hash.map.HashMap String V std.hash.random.RandomState A)
    (k : String) :
    std.collections.hash.map.HashMap.get rmcp.alloc.string.String.Insts.CoreCmpEq
      rmcp.alloc.string.String.Insts.CoreHashHash
      rmcp.std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher
      (rmcp.core.borrow.Borrow.Blanket String) rmcp.alloc.string.String.Insts.CoreHashHash
      rmcp.alloc.string.String.Insts.CoreCmpEq self k ⦃ (result : Option V) =>
        result = (self.entries.find? (fun e => decide (e.1 = k))).map Prod.snd ⦄ := by
  rw [std.collections.hash.map.HashMap.get_eq, Proofs.External.HashMap.find_string]
  simp only [WP.spec_ok]

namespace Proofs.External.HashMap

/-- With distinct keys, the first entry with key `k` is the one stored under `k`. -/
theorem find?_key_of_mem {V : Type} (entries : List (String × V)) (k : String) (v : V)
    (hnd : (entries.map Prod.fst).Nodup) (hm : (k, v) ∈ entries) :
    (entries.find? (fun e => decide (e.1 = k))).map Prod.snd = some v := by
  induction entries with
  | nil => simp only [List.not_mem_nil] at hm
  | cons e rest ih =>
    obtain ⟨k', v'⟩ := e
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    simp only [List.mem_cons, Prod.mk.injEq] at hm
    by_cases hk : k' = k
    · subst hk
      rcases hm with ⟨_, rfl⟩ | hm
      · simp only [decide_true, List.find?_cons_of_pos, Option.map_some]
      · exact absurd ⟨(k', v), hm, rfl⟩ hnd.1
    · rcases hm with ⟨h1, _⟩ | hm
      · exact absurd h1.symm hk
      · simp only [hk, decide_false, Bool.false_eq_true, not_false_eq_true, List.find?_cons_of_neg,
          ih hnd.2 hm]

/-- No entry has key `k`: the lookup gives `none`. -/
theorem find?_key_of_not_mem {V : Type} (entries : List (String × V)) (k : String)
    (h : k ∉ entries.map Prod.fst) :
    (entries.find? (fun e => decide (e.1 = k))).map Prod.snd = none := by
  simp only [Option.map_eq_none_iff, List.find?_eq_none, decide_eq_true_eq]
  intro e he hek
  exact h (List.mem_map.2 ⟨e, he, hek⟩)

/-- **Found, without distinct keys:** the lookup returns a value exactly when `k` is a key; no
`Nodup` premise (with duplicate keys it is the value of the first entry). -/
theorem find?_key_isSome_iff {V : Type} (entries : List (String × V)) (k : String) :
    ((entries.find? (fun e => decide (e.1 = k))).map Prod.snd).isSome ↔
      k ∈ entries.map Prod.fst := by
  simp only [Option.isSome_map, List.find?_isSome, decide_eq_true_eq, Prod.exists, exists_and_right,
    exists_eq_right, List.mem_map]

end Proofs.External.HashMap

/-- `HashMap::clone`: clones the hash builder, the allocator and every key and value. -/
theorem std.collections.hash.map.HashMap.Insts.CoreCloneClone.clone_eq
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
        ok { hash_builder, alloc, entries }) := rfl

/-! ## `zeroize` -/

/-- **Spec theorem for `Zeroizing::new`**: wraps the value. -/
@[step]
theorem zeroize.Zeroizing.new_spec {Z : Type} (inst : rmcp.zeroize.Zeroize Z) (value : Z) :
    zeroize.Zeroizing.new inst value ⦃ (result : zeroize.Zeroizing Z) =>
      result.inner = value ⦄ := by
  simp only [zeroize.Zeroizing.new, WP.spec_ok]

/-- **Spec theorem for `<Zeroizing<Z> as Deref>::deref`**: the wrapped value. -/
@[step]
theorem zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref_spec {Z : Type}
    (inst : rmcp.zeroize.Zeroize Z) (self : zeroize.Zeroizing Z) :
    zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref inst self ⦃ (result : Z) =>
      result = self.inner ⦄ := by
  simp only [zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref, WP.spec_ok]

/-- `<Zeroizing<Z> as Clone>::clone` wraps a clone of the value. -/
theorem zeroize.Zeroizing.Insts.CoreCloneClone.clone_eq {Z : Type} (inst : rmcp.zeroize.Zeroize Z)
    (cZ : core.clone.Clone Z) (self : zeroize.Zeroizing Z) :
    zeroize.Zeroizing.Insts.CoreCloneClone.clone inst cZ self =
      (do let v ← cZ.clone self.inner; ok { inner := v }) := rfl

/-- `<Z as Zeroize>::zeroize` for `Z: DefaultIsZeroes` is `Z::default()`. -/
theorem zeroize.Zeroize.Blanket.zeroize_eq {Z : Type} (inst : rmcp.zeroize.DefaultIsZeroes Z)
    (self : Z) :
    zeroize.Zeroize.Blanket.zeroize inst self = inst.coredefaultDefaultInst.default := rfl

/-- `<Vec<Z> as Zeroize>::zeroize` zeroizes each element and returns the empty vector. -/
theorem alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize_eq {Z : Type} (inst : rmcp.zeroize.Zeroize Z)
    (self : alloc.vec.Vec Z) :
    alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize inst self =
      (do let _ ← self.val.mapM inst.zeroize; ok (alloc.vec.Vec.new Z)) := rfl

/-! ## Clock

No statement about the function `RequestStateCodec::now_ms` (nor the functions `open`,
`open_with`; Lean `rmcp.model.request_state.RequestStateCodec.{now_ms, open, open_with}`; a
variable named `now_ms` is not covered): the clock is one
opaque constant `ExtModel.nowMs`, which makes every reader pure, so a statement about it could
relate readings in a way the Rust code does not guarantee (review rule, `formal/README.md`,
"Trusted base"). Statements about opening use `open_at` with an explicit time. -/

/-! ## Phase 2: slices and ranges -/

open rmcp

/-- **Spec theorem for `slice::first`**: the first element, `None` for the empty slice. -/
@[step]
theorem core.slice.Slice.first_spec {T : Type} (self : Slice T) :
    core.slice.Slice.first self ⦃ (result : Option T) => result = self.val.head? ⦄ := by
  unfold core.slice.Slice.first
  cases h : self.val <;> exact (WP.spec_ok _).mpr rfl

/-- **Spec theorem for `<[T; N] as SlicePattern>::as_slice`**: the same elements. -/
@[step]
theorem Array.Insts.CoreSliceSlicePattern.as_slice_spec {T : Type} {N : Usize}
    (self : Array T N) :
    Array.Insts.CoreSliceSlicePattern.as_slice self ⦃ (result : Slice T) =>
      result.val = self.val ⦄ := by
  simp only [Array.Insts.CoreSliceSlicePattern.as_slice, Array.to_slice, WP.spec_ok]

namespace Proofs.External.Slice

/-- `ExtModel.sliceEqSameLength` on lists of equal length, for an instance whose `ne` decides
the negation of `R` on their elements: element-wise relatedness. -/
theorem sliceEqSameLength_spec {T U : Type} (inst : core.cmp.PartialEq T U) (R : T → U → Prop)
    (l : List T) (r : List U) (hlen : l.length = r.length)
    (h_ne : ∀ a ∈ l, ∀ b ∈ r, inst.ne a b ⦃ (d : Bool) => (d = true ↔ ¬ R a b) ⦄) :
    ExtModel.sliceEqSameLength inst l r ⦃ (result : Bool) =>
      (result = true ↔ List.Forall₂ R l r) ⦄ := by
  induction l generalizing r with
  | nil =>
    cases r with
    | nil =>
      simp only [ExtModel.sliceEqSameLength, List.forall₂_nil_right_iff, iff_true, WP.spec_ok]
    | cons _ _ => exact absurd hlen (Nat.succ_ne_zero _).symm
  | cons a l ih =>
    cases r with
    | nil => exact absurd hlen (Nat.succ_ne_zero _)
    | cons b r =>
      obtain ⟨d, hd, hP⟩ :=
        WP.spec_imp_exists (h_ne a List.mem_cons_self b List.mem_cons_self)
      simp only [ExtModel.sliceEqSameLength, hd, bind_tc_ok, List.forall₂_cons]
      cases d with
      | true =>
        simp only [↓reduceIte, WP.spec_ok, Bool.false_eq_true, false_iff, not_and]
        exact fun hR => absurd hR (hP.1 rfl)
      | false =>
        have hR : R a b := by simpa only [Bool.false_eq_true, false_iff, not_not] using hP
        simp only [Bool.false_eq_true, ↓reduceIte, hR, true_and]
        exact ih r (Nat.succ.inj hlen)
          (fun x hx y hy => h_ne x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem b hy))

end Proofs.External.Slice

/-- **Spec theorem for `[T] == [U; N]`**, for an instance whose `ne` decides the negation of a
relation `R` on the elements compared: the result is `true` exactly when the slice and the
array have the same length and are related element-wise. -/
theorem Slice.Insts.CoreCmpPartialEqArray.eq_spec {T : Type} {U : Type} {N : Usize}
    (cmpPartialEqInst : core.cmp.PartialEq T U) (self : Slice T) (other : Array U N)
    (R : T → U → Prop)
    (h_ne : ∀ a ∈ self.val, ∀ b ∈ other.val,
      cmpPartialEqInst.ne a b ⦃ (d : Bool) => (d = true ↔ ¬ R a b) ⦄) :
    Slice.Insts.CoreCmpPartialEqArray.eq cmpPartialEqInst self other ⦃ (result : Bool) =>
      (result = true ↔ List.Forall₂ R self.val other.val) ⦄ := by
  unfold Slice.Insts.CoreCmpPartialEqArray.eq
  split
  · rename_i h
    apply Proofs.External.Slice.sliceEqSameLength_spec _ _ _ _ _ h_ne
    rw [h, other.property]
  · rename_i h
    have hl : self.val.length ≠ other.val.length := by rw [other.property]; exact h
    simp only [WP.spec_ok, Bool.false_eq_true, false_iff]
    exact fun hf => hl hf.length_eq

/-- **Spec theorem for `[u16] == [u16; N]`** at the instance of the translation
(`core.cmp.PartialEqU16`): list equality of the elements. -/
@[step]
theorem Slice.Insts.CoreCmpPartialEqArray.eq_u16_spec {N : Usize}
    (self : Slice U16) (other : Array U16 N) :
    Slice.Insts.CoreCmpPartialEqArray.eq core.cmp.PartialEqU16 self other ⦃ (result : Bool) =>
      (result = true ↔ self.val = other.val) ⦄ := by
  have h := Slice.Insts.CoreCmpPartialEqArray.eq_spec core.cmp.PartialEqU16 self other (· = ·)
    (fun a _ b _ => by
      simp only [liftFun2, core.cmp.impls.PartialEqU16.ne, UScalar.neq_to_neq_val, decide_not,
        WP.spec_ok, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not])
  rw [List.forall₂_eq_eq_eq] at h
  exact h

/-- **Spec theorem for `slice::strip_suffix`**, for every pattern instance and every element
instance whose `ne` decides the negation of a relation `R` on the elements compared. -/
theorem core.slice.Slice.strip_suffix_spec {T : Type} {P : Type}
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
          ¬ ∃ head tail, self.val = head ++ tail ∧ List.Forall₂ R tail suf.val ⦄ := by
  unfold core.slice.Slice.strip_suffix
  simp only [h_suf, bind_tc_ok]
  split
  · rename_i hle
    have hle' : suf.val.length ≤ self.val.length := by
      have := hle; simp only [UScalar.le_equiv, Slice.len_val] at this; exact this
    obtain ⟨mid, hmid, hmv, -⟩ := WP.spec_imp_exists (Usize.sub_spec hle)
    have hsl : ∀ s : Slice T, s.length = s.val.length := fun _ => rfl
    simp only [Slice.len_val, hsl] at hmv
    have hmle : mid.val ≤ self.length := by rw [hmv, hsl]; omega
    have hdrop : (self.val.drop mid.val).length = suf.val.length := by
      rw [List.length_drop, hmv]; omega
    obtain ⟨⟨head, tail⟩, hsp, hP⟩ :=
      WP.spec_imp_exists (core.slice.Slice.split_at.spec self mid hmle)
    simp only [WP.uncurry'_pair] at hP
    obtain ⟨-, -, hhead, htail⟩ := hP
    have hdrop' : tail.val.length = suf.val.length := by rw [htail]; exact hdrop
    rw [hmid, bind_tc_ok, hsp, bind_tc_ok]
    show (do
      let b ← ExtModel.sliceEq cmpPartialEqInst tail.val suf.val
      if b then ok (some head) else ok none) ⦃ (result : Option (Slice T)) =>
        match result with
        | some head => ∃ tail, self.val = head.val ++ tail ∧ List.Forall₂ R tail suf.val
        | none =>
          ¬ ∃ head tail, self.val = head ++ tail ∧ List.Forall₂ R tail suf.val ⦄
    rw [ExtModel.sliceEq, if_pos hdrop']
    obtain ⟨b, hb, hbP⟩ := WP.spec_imp_exists (Proofs.External.Slice.sliceEqSameLength_spec
      cmpPartialEqInst R _ _ hdrop'
      (fun x hx y hy => h_ne x (by rw [htail] at hx; exact List.mem_of_mem_drop hx) y hy))
    rw [hb, bind_tc_ok]
    cases b with
    | true =>
      simp only [↓reduceIte, WP.spec_ok]
      refine ⟨tail.val, ?_, hbP.1 rfl⟩
      rw [hhead, htail, List.take_append_drop]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      rintro ⟨h', t', hs, hf⟩
      have hlen := congrArg List.length hs
      rw [List.length_append, hf.length_eq] at hlen
      have ht' : t' = tail.val := by
        have hk : self.val.length - suf.val.length = h'.length := by omega
        rw [htail, hmv, hk, hs, List.drop_left]
      rw [ht'] at hf
      exact Bool.false_ne_true (hbP.2 hf)
  · rename_i hlt
    have hlt' : self.val.length < suf.val.length := by
      have := hlt; simp only [UScalar.le_equiv, Slice.len_val] at this
      exact Nat.lt_of_not_le this
    simp only [WP.spec_ok]
    rintro ⟨head, tail, hs, hf⟩
    have := congrArg List.length hs
    rw [List.length_append, hf.length_eq] at this
    omega

/-- `slice::strip_suffix` with a pattern whose `as_slice` does not return: its failure or
divergence propagates. -/
theorem core.slice.Slice.strip_suffix_fail {T : Type} {P : Type}
    (SlicePatternInst : core.slice.SlicePattern P T) (cmpPartialEqInst : core.cmp.PartialEq T T)
    (self : Slice T) (suffix : P) :
    (∀ e, SlicePatternInst.as_slice suffix = fail e →
      core.slice.Slice.strip_suffix SlicePatternInst cmpPartialEqInst self suffix = fail e) ∧
    (SlicePatternInst.as_slice suffix = div →
      core.slice.Slice.strip_suffix SlicePatternInst cmpPartialEqInst self suffix = div) := by
  constructor
  · intro e h
    rw [core.slice.Slice.strip_suffix, h]
    rfl
  · intro h
    rw [core.slice.Slice.strip_suffix, h]
    rfl

/-- **Spec theorem for `[u8]::strip_suffix(&[c])`** at the instances of the translation (the
pattern `[u8; 1]`, `core.cmp.PartialEqU8`): `Some head` with `self = head ++ [c]` when the last
byte is `c`, otherwise `None`. -/
@[step]
theorem core.slice.Slice.strip_suffix_u8_single_spec (self : Slice U8) (c : U8) :
    core.slice.Slice.strip_suffix (Array.Insts.CoreSliceSlicePattern U8 1#usize)
        core.cmp.PartialEqU8 self (Array.make 1#usize [c])
      ⦃ (result : Option (Slice U8)) =>
        match result with
        | some head => self.val = head.val ++ [c]
        | none => self.val.getLast? ≠ some c ⦄ := by
  have h := core.slice.Slice.strip_suffix_spec (Array.Insts.CoreSliceSlicePattern U8 1#usize)
    core.cmp.PartialEqU8 self (Array.make 1#usize [c]) (Array.to_slice (Array.make 1#usize [c]))
    (· = ·) rfl (fun a _ b _ => by
      simp only [liftFun2, core.cmp.impls.PartialEqU8.ne, UScalar.neq_to_neq_val, decide_not,
        WP.spec_ok, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not])
  apply WP.spec_mono h
  intro result hr
  cases result with
  | some head =>
    obtain ⟨tail, hs, hf⟩ := hr
    rw [List.forall₂_eq_eq_eq] at hf
    rw [hs, hf]
    rfl
  | none =>
    intro hl
    apply hr
    refine ⟨self.val.dropLast, [c], ?_, ?_⟩
    · exact (List.dropLast_append_getLast? c hl).symm
    · rw [List.forall₂_eq_eq_eq]
      rfl

/-- **Spec theorem for `RangeInclusive<u8>::contains`** at the instances of the translation
(`core.cmp.PartialOrdU8`): `start ≤ item ≤ end` for a range that is not exhausted,
`start ≤ item < end` for an exhausted one; never fails. -/
@[step]
theorem core.ops.range.RangeInclusive.contains_u8_spec
    (self : core.ops.range.RangeInclusive U8) (item : U8) :
    core.ops.range.RangeInclusive.contains core.cmp.PartialOrdU8 core.cmp.PartialOrdU8
        core.cmp.PartialOrdU8 self item ⦃ (result : Bool) =>
      (result = true ↔ self.start.val ≤ item.val ∧
        (if self.exhausted then item.val < self.«end».val
         else item.val ≤ self.«end».val)) ⦄ := by
  unfold core.ops.range.RangeInclusive.contains
  cases hx : self.exhausted <;> by_cases h1 : self.start.val ≤ item.val <;>
    simp only [liftFun2, core.cmp.impls.PartialOrdU8.le, h1, decide_true, Bool.false_eq_true,
      ↓reduceIte, bind_tc_ok, true_and, WP.spec_ok, decide_eq_true_eq, decide_false, false_and,
      iff_false, Bool.not_eq_true, core.cmp.impls.PartialOrdU8.lt]

/-- **`(a..=b).contains(&x)` for `u8`**: `a ≤ x ≤ b`. -/
theorem core.ops.range.RangeInclusive.new_contains_u8_spec (a b item : U8) :
    (do
      let r ← core.ops.range.RangeInclusive.new a b
      core.ops.range.RangeInclusive.contains core.cmp.PartialOrdU8 core.cmp.PartialOrdU8
        core.cmp.PartialOrdU8 r item) ⦃ (result : Bool) =>
      (result = true ↔ a.val ≤ item.val ∧ item.val ≤ b.val) ⦄ := by
  rw [core.ops.range.RangeInclusive.new, bind_tc_ok]
  exact core.ops.range.RangeInclusive.contains_u8_spec ⟨a, b, false⟩ item

/-- `RangeInclusive::contains`, for every instance: `start <= item` is evaluated first; if it
fails or diverges that propagates, if it is `false` the result is `false` without a second
call, and if it is `true` the result is `item < end` (exhausted) or `item <= end` (not
exhausted), including its failure. -/
theorem core.ops.range.RangeInclusive.contains_eq_match_le {Idx : Type} {U : Type}
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
        if self.exhausted then cmpPartialOrdInst2.lt item self.«end»
        else cmpPartialOrdInst2.le item self.«end») := by
  refine ⟨fun e h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    rw [core.ops.range.RangeInclusive.contains, h] <;> rfl
