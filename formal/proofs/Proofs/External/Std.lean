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
functions that take a trait instance whose behaviour is not fixed (`map_err`, `clone`, ...).
-/

open Aeneas Aeneas.Std Result

open ExtModel Proofs.External.Utf8 Proofs.External.Base64

/-! ## `core` -/

/-- **Spec theorem for `core::borrow::{impl Borrow<T> for T}::borrow`**: the identity. -/
@[step]
theorem core.borrow.Borrow.Blanket.borrow_spec {T : Type} (self : T) :
    core.borrow.Borrow.Blanket.borrow self ⦃ (result : T) => result = self ⦄ := by
  simp [core.borrow.Borrow.Blanket.borrow]

/-- **Spec theorem for `core::option::Option::ok_or`**: `Some v ↦ Ok v`, `None ↦ Err err`. -/
@[step]
theorem core.option.Option.ok_or_spec {T : Type} {E : Type} (self : Option T) (err : E) :
    core.option.Option.ok_or self err ⦃ (result : core.result.Result T E) =>
      result = match self with
        | some v => core.result.Result.Ok v
        | none => core.result.Result.Err err ⦄ := by
  match self with
  | some _ => simp [core.option.Option.ok_or]
  | none => simp [core.option.Option.ok_or]

/-- **Spec theorem for `<Option<T> as Default>::default`**: `None`. -/
@[step]
theorem core.option.Option.Insts.CoreDefaultDefault.default_spec (T : Type) :
    core.option.Option.Insts.CoreDefaultDefault.default T ⦃ (result : Option T) =>
      result = none ⦄ := by
  simp [core.option.Option.Insts.CoreDefaultDefault.default]

/-- **Spec theorem for `core::result::Result::is_err`**: `true` exactly for `Err`. -/
@[step]
theorem core.result.Result.is_err_spec {T : Type} {E : Type} (self : core.result.Result T E) :
    core.result.Result.is_err self ⦃ (result : Bool) =>
      result = match self with
        | core.result.Result.Ok _ => false
        | core.result.Result.Err _ => true ⦄ := by
  match self with
  | core.result.Result.Ok _ => simp [core.result.Result.is_err]
  | core.result.Result.Err _ => simp [core.result.Result.is_err]

/-- `core::result::Result::map_err` on `Ok`: unchanged, the closure is not called. -/
@[simp]
theorem core.result.Result.map_err_Ok {T E F O : Type}
    (inst : core.ops.function.FnOnce O E F) (t : T) (op : O) :
    core.result.Result.map_err inst (core.result.Result.Ok t : core.result.Result T E) op =
      Aeneas.Std.Result.ok (core.result.Result.Ok t) := rfl

/-- `core::result::Result::map_err` on `Err e`: `Err (op e)`; the closure's failure
propagates. -/
@[simp]
theorem core.result.Result.map_err_Err {T E F O : Type}
    (inst : core.ops.function.FnOnce O E F) (e : E) (op : O) :
    core.result.Result.map_err inst (core.result.Result.Err e : core.result.Result T E) op =
      (do let f ← inst.call_once op e; Aeneas.Std.Result.ok (core.result.Result.Err f)) := rfl

/-- **Spec theorem for `<&[T] as Default>::default`**: the empty slice. -/
@[step]
theorem Shared0Slice.Insts.CoreDefaultDefault.default_spec (T : Type) :
    Shared0Slice.Insts.CoreDefaultDefault.default T ⦃ (result : Slice T) =>
      result.val = [] ⦄ := by
  simp [Shared0Slice.Insts.CoreDefaultDefault.default, Slice.new]

/-- **Spec theorem for `core::str::str::len`**: the number of bytes; for every `Str`. -/
@[step]
theorem core.str.Str.len_spec (self : Str) :
    core.str.Str.len self ⦃ (result : Usize) => result.val = self.val.length ⦄ := by
  simp [core.str.Str.len]

/-- **Spec theorem for `core::str::str::as_bytes`**: the same bytes; for every `Str`. -/
@[step]
theorem core.str.Str.as_bytes_spec (self : Str) :
    core.str.Str.as_bytes self ⦃ (result : Slice U8) => result.val = self.val ⦄ := by
  simp [core.str.Str.as_bytes]

/-! ## `alloc::string::String` -/

/-- **Spec theorem for `String::with_capacity`**: the empty string, if `capacity ≤ isize::MAX`
(else `with_capacity_fail`). -/
@[step]
theorem alloc.string.String.with_capacity_spec (capacity : Usize)
    (h : capacity.val ≤ maxStringBytes) :
    alloc.string.String.with_capacity capacity ⦃ (result : String) => result = "" ⦄ := by
  simp [alloc.string.String.with_capacity, h]

/-- `String::with_capacity` panics ("capacity overflow") above `isize::MAX`. -/
theorem alloc.string.String.with_capacity_fail (capacity : Usize)
    (h : maxStringBytes < capacity.val) :
    alloc.string.String.with_capacity capacity = fail Error.panic := by
  simp [alloc.string.String.with_capacity, Nat.not_le.2 h]

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
  simp [alloc.string.String.push_str, (strOfBytes?_eq_none_iff _).2 h]

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
  simp [alloc.string.String.as_bytes, h]

/-- `String::as_bytes` on a Lean `String` longer than `Usize.max` bytes (no Rust `String`). -/
theorem alloc.string.String.as_bytes_fail (self : String) (h : Usize.max < self.utf8ByteSize) :
    alloc.string.String.as_bytes self = fail Error.maximumSizeExceeded := by
  rw [← length_utf8] at h
  simp [alloc.string.String.as_bytes, Nat.not_le.2 h]

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
  · rename_i s hs; simpa using (strOfBytes?_eq_some_iff _ _).1 hs
  · rename_i hs; simpa using (strOfBytes?_eq_none_iff _).1 hs

/-- **Spec theorem for `<String as PartialEq>::eq`**: equality. -/
@[step]
theorem alloc.string.String.Insts.CoreCmpPartialEqString.eq_spec (self : String)
    (other : String) :
    alloc.string.String.Insts.CoreCmpPartialEqString.eq self other ⦃ (result : Bool) =>
      result = decide (self = other) ⦄ := by
  simp [alloc.string.String.Insts.CoreCmpPartialEqString.eq]

/-- **Spec theorem for `<String as Eq>::assert_fields_are_eq`**: succeeds. -/
@[step]
theorem alloc.string.String.Insts.CoreCmpEq.assert_fields_are_eq_spec (self : String) :
    alloc.string.String.Insts.CoreCmpEq.assert_fields_are_eq self ⦃ (_ : Unit) => True ⦄ := by
  simp [alloc.string.String.Insts.CoreCmpEq.assert_fields_are_eq]

/-- **Spec theorem for `<String as Clone>::clone`**: the same string. -/
@[step]
theorem alloc.string.String.Insts.CoreCloneClone.clone_spec (self : String) :
    alloc.string.String.Insts.CoreCloneClone.clone self ⦃ (result : String) =>
      result = self ⦄ := by
  simp [alloc.string.String.Insts.CoreCloneClone.clone]

/-- `<String as Hash>::hash` writes the bytes and then `0xff` (for a Rust-sized `String`). -/
theorem alloc.string.String.Insts.CoreHashHash.hash_eq {H : Type}
    (inst : core.hash.Hasher H) (self : String) (state : H)
    (h : self.utf8ByteSize ≤ Usize.max) :
    alloc.string.String.Insts.CoreHashHash.hash inst self state =
      (do
        let state ← inst.write state ⟨utf8 self, by rw [length_utf8]; exact h⟩
        inst.write state ⟨[byte 255], by scalar_tac⟩) := by
  have h' : (utf8 self).length ≤ Usize.max := by rw [length_utf8]; exact h
  simp [alloc.string.String.Insts.CoreHashHash.hash, alloc.string.String.as_bytes, h']

/-! ## `Vec`, hashing, `HashMap` -/

/-- **Spec theorem for `Vec::is_empty`**: `true` exactly for the empty vector. -/
@[step]
theorem alloc.vec.Vec.is_empty_spec {T : Type} (A : Type) (self : alloc.vec.Vec T) :
    alloc.vec.Vec.is_empty A self ⦃ (result : Bool) => result = decide (self.val = []) ⦄ := by
  simp [alloc.vec.Vec.is_empty]

/-- **Spec theorem for `<RandomState as Clone>::clone`**: the same value. -/
@[step]
theorem std.hash.random.RandomState.Insts.CoreCloneClone.clone_spec
    (self : std.hash.random.RandomState) :
    std.hash.random.RandomState.Insts.CoreCloneClone.clone self ⦃
      (result : std.hash.random.RandomState) => result = self ⦄ := by
  simp [std.hash.random.RandomState.Insts.CoreCloneClone.clone]

/-- **Spec theorem for `<RandomState as BuildHasher>::build_hasher`**: the map's keys, no
bytes written. -/
@[step]
theorem std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher.build_hasher_spec
    (self : std.hash.random.RandomState) :
    std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher.build_hasher self ⦃
      (result : std.hash.random.DefaultHasher) =>
        result = { k0 := self.k0, k1 := self.k1, written := [] } ⦄ := by
  simp [std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher.build_hasher]

/-- **Spec theorem for `<DefaultHasher as Hasher>::write`**: appends the bytes. -/
@[step]
theorem std.hash.random.DefaultHasher.Insts.CoreHashHasher.write_spec
    (self : std.hash.random.DefaultHasher) (msg : Slice U8) :
    std.hash.random.DefaultHasher.Insts.CoreHashHasher.write self msg ⦃
      (result : std.hash.random.DefaultHasher) =>
        result = { self with written := self.written ++ msg.val } ⦄ := by
  simp [std.hash.random.DefaultHasher.Insts.CoreHashHasher.write]

/-- **Spec theorem for `<DefaultHasher as Hasher>::finish`**: SipHash-1-3 of keys and bytes. -/
@[step]
theorem std.hash.random.DefaultHasher.Insts.CoreHashHasher.finish_spec
    (self : std.hash.random.DefaultHasher) :
    std.hash.random.DefaultHasher.Insts.CoreHashHasher.finish self ⦃ (result : U64) =>
      result = sipHash13 self.k0 self.k1 self.written ⦄ := by
  simp [std.hash.random.DefaultHasher.Insts.CoreHashHasher.finish]

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
    · subst h; simp
    · simp [h, Ne.symm h]
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
  simp

namespace Proofs.External.HashMap

/-- With distinct keys, the first entry with key `k` is the one stored under `k`. -/
theorem find?_key_of_mem {V : Type} (entries : List (String × V)) (k : String) (v : V)
    (hnd : (entries.map Prod.fst).Nodup) (hm : (k, v) ∈ entries) :
    (entries.find? (fun e => decide (e.1 = k))).map Prod.snd = some v := by
  induction entries with
  | nil => simp at hm
  | cons e rest ih =>
    obtain ⟨k', v'⟩ := e
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    simp only [List.mem_cons, Prod.mk.injEq] at hm
    by_cases hk : k' = k
    · subst hk
      rcases hm with ⟨_, rfl⟩ | hm
      · simp
      · exact absurd ⟨(k', v), hm, rfl⟩ hnd.1
    · rcases hm with ⟨h1, _⟩ | hm
      · exact absurd h1.symm hk
      · simp [hk, ih hnd.2 hm]

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
  simp [Option.isSome_map, List.find?_isSome, List.mem_map]

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
  simp [zeroize.Zeroizing.new]

/-- **Spec theorem for `<Zeroizing<Z> as Deref>::deref`**: the wrapped value. -/
@[step]
theorem zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref_spec {Z : Type}
    (inst : rmcp.zeroize.Zeroize Z) (self : zeroize.Zeroizing Z) :
    zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref inst self ⦃ (result : Z) =>
      result = self.inner ⦄ := by
  simp [zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref]

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
