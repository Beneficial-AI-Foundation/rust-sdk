/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Rmcp.Funs
public import Proofs.External.String
public import Proofs.External.WP

@[expose] public section

/-!
# Specs of the standard-library, `HashMap`, `zeroize` and clock externals

Spec theorems for the models in `formal/trusted/Rmcp/FunsExternal.lean` (sections Standard
library and Clock). Since the Aeneas upgrade of 2026-11-24 four of the functions specified here
are defined in the Aeneas library, no longer by a project model (lead decision N8):
`core::borrow::Borrow` (`core.borrow.Borrow.Blanket.borrow`), `Option::ok_or`,
`Result::map_err` and `Vec::is_empty`. Forced restatements in that upgrade (name-only, human
decision 2026-11-24): the arity of `alloc.vec.Vec.is_empty_spec` (no allocator argument); the
`Borrow` rename (`Aeneas.Std.core.borrow.Borrow`) in `std.collections.hash.map.HashMap.get_eq`,
`get_string_spec` and the helper `Proofs.External.HashMap.find_string`; and `Slice.from` instead
of the anonymous constructor in `alloc.string.String.Insts.CoreHashHash.hash_eq`. `RangeInclusive::contains` follows
`nightly-2026-09-17` since that upgrade: an exhausted range contains nothing (exhausted branch
`item < start`; human decision 2026-11-24). Each covers success and, where the model can fail, the failure. Names follow
the style guide: the full generated name of the external with `_spec`; equation lemmas for
functions that take a trait instance whose behaviour is not fixed (`map_err`, `clone`, ...), and
for `ok_or` and `is_err` (`ok_or_eq`, `is_err_eq`, from their spec theorems, for rewriting inside
a `do` block).

Section "Phase 2: slices and ranges" proves the signed-off laws of plan steps S26/S27 for
`slice::first`, `<[T; N] as SlicePattern>::as_slice`, `[T] == [U; N]`, `slice::strip_suffix`
and `RangeInclusive::contains`.

Added 2026-11-25 (human decision: every external reached by the translation has a model and a
spec theorem `<generated name>_spec`): the `_spec` theorems of `<String as Hash>::hash`,
`<str as Hash>::hash`, `HashMap::{get, clone}`, the `zeroize` externals, `now_ms` (the one
exception to the clock rule for the model's own spec), `RangeInclusive::contains` for every
instance, and section "Public `request_state.rs` API (R09–R15)". Each is general over the type
parameters; the behaviour of a trait instance or closure is a hypothesis.
-/

open Aeneas Aeneas.Std Result

open ExtModel Proofs.External.Utf8 Proofs.External.Base64

/-! ## `core` -/

/-- **Spec theorem for `core::borrow::{impl Borrow<T> for T}::borrow`**: the identity (the Aeneas
library's definition since the Aeneas upgrade of 2026-11-24). -/
@[step]
theorem core.borrow.Borrow.Blanket.borrow_spec {T : Type} (self : T) :
    core.borrow.Borrow.Blanket.borrow self ⦃ (result : T) => result = self ⦄ := by
  simp only [core.borrow.Borrow.Blanket.borrow, WP.spec_ok]

/-- **Spec theorem for `core::option::Option::ok_or`**: `Some v ↦ Ok v`, `None ↦ Err err` (the
Aeneas library's definition since the Aeneas upgrade of 2026-11-24). -/
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

/-- `core::result::Result::map_err` on `Ok`: unchanged, the closure is not called (the Aeneas
library's definition since the Aeneas upgrade of 2026-11-24). -/
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
  simp only [Shared0Slice.Insts.CoreDefaultDefault.default, WP.spec_ok, Slice.new_val]

/-- **Spec theorem for `core::str::str::len`**: the number of bytes; for every `Str`. -/
@[step]
theorem core.str.Str.len_spec (self : Str) :
    core.str.Str.len self ⦃ (result : Usize) => result.val = self.val.length ⦄ := by
  simp only [core.str.Str.len, WP.spec_ok, Usize.ofNatCore_val_eq]

/-- **Spec theorem for `core::str::str::as_bytes`**: the same bytes; for every `Str`. -/
@[step]
theorem core.str.Str.as_bytes_spec (self : Str) :
    core.str.Str.as_bytes self ⦃ (result : Slice U8) => result.val = self.val ⦄ := by
  exact (WP.spec_ok (p := fun result : Slice U8 => result.val = self.val) _).2 rfl

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
  simp only [alloc.string.String.push_str, ht, strOfBytes?_utf8, growString, ite_eq_left hlen,
    WP.spec_ok, utf8_append, true_and]

/-- `String::push_str` with a result beyond `isize::MAX` bytes panics. -/
theorem alloc.string.String.push_str_fail (self : String) (string : Str) (t : String)
    (ht : string.val = utf8 t) (h : maxStringBytes < self.utf8ByteSize + string.val.length) :
    alloc.string.String.push_str self string = fail Error.panic := by
  have hlen : ¬ (self ++ t).utf8ByteSize ≤ maxStringBytes := by
    rw [String.utf8ByteSize_append, ← length_utf8 t, ← ht]; omega
  simp only [alloc.string.String.push_str, ht, strOfBytes?_utf8, growString, ite_eq_right hlen]

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
  simp only [alloc.string.String.push, growString, ite_eq_left hlen, WP.spec_ok, true_and]
  rw [hp, utf8_append]

/-- `String::push` with a result beyond `isize::MAX` bytes panics. -/
theorem alloc.string.String.push_fail (self : String) (ch : Char)
    (h : maxStringBytes < self.utf8ByteSize + ch.utf8Size) :
    alloc.string.String.push self ch = fail Error.panic := by
  have hlen : ¬ (self.push ch).utf8ByteSize ≤ maxStringBytes := by
    rw [String.utf8ByteSize_push]; omega
  simp only [alloc.string.String.push, growString, ite_eq_right hlen]

/-- **Spec theorem for `String::as_bytes`**: the UTF-8 bytes. The precondition holds for every
Rust `String` (at most `isize::MAX` bytes); see `as_bytes_fail`. -/
@[step]
theorem alloc.string.String.as_bytes_spec (self : String) (h : self.utf8ByteSize ≤ Usize.max) :
    alloc.string.String.as_bytes self ⦃ (result : Slice U8) => result.val = utf8 self ⦄ := by
  rw [← length_utf8] at h
  simp only [alloc.string.String.as_bytes, h, ↓reduceDIte, WP.spec_ok, Slice.from_val]

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
        let state ← inst.write state (Slice.from (utf8 self) (by rw [length_utf8]; exact h))
        inst.write state (Slice.from [byte 255] (by scalar_tac))) := by
  have h' : (utf8 self).length ≤ Usize.max := by rw [length_utf8]; exact h
  simp only [alloc.string.String.Insts.CoreHashHash.hash, alloc.string.String.as_bytes, h',
    ↓reduceDIte, bind_ok]

/-- **Spec theorem for `<String as Hash>::hash`**, for every hasher instance whose `write`
appends by a function `w` of the state and the bytes: `w` applied to the UTF-8 bytes and then
to `[0xff]`, for a string of at most `Usize.max` bytes (every Rust `String`; from `hash_eq`). -/
theorem alloc.string.String.Insts.CoreHashHash.hash_spec {H : Type}
    (inst : core.hash.Hasher H) (w : H → List U8 → H)
    (hw : ∀ s m, inst.write s m ⦃ (r : H) => r = w s m.val ⦄)
    (self : String) (state : H) (h : self.utf8ByteSize ≤ Usize.max) :
    alloc.string.String.Insts.CoreHashHash.hash inst self state ⦃ (result : H) =>
      result = w (w state (utf8 self)) [byte 255] ⦄ := by
  rw [alloc.string.String.Insts.CoreHashHash.hash_eq inst self state h]
  obtain ⟨s1, hs1, hs1v⟩ := Proofs.External.WP.exists_ok_of_spec (hw state
    (Slice.from (utf8 self) (by rw [length_utf8]; exact h)))
  rw [hs1, bind_ok, hs1v, Slice.from_val]
  exact WP.spec_mono (hw _ _) (fun r hr => by rw [hr, Slice.from_val])

/-- **Spec theorem for `<str as Hash>::hash`**, for every hasher instance whose `write` appends
by a function `w` of the state and the bytes: `w` applied to the bytes of the `str` and then to
`[0xff]`; for every `Str`. -/
theorem Str.Insts.CoreHashHash.hash_spec {H : Type}
    (inst : core.hash.Hasher H) (w : H → List U8 → H)
    (hw : ∀ s m, inst.write s m ⦃ (r : H) => r = w s m.val ⦄)
    (self : Str) (state : H) :
    Str.Insts.CoreHashHash.hash inst self state ⦃ (result : H) =>
      result = w (w state self.val) [byte 255] ⦄ := by
  obtain ⟨s1, hs1, hs1v⟩ := Proofs.External.WP.exists_ok_of_spec (hw state self)
  simp only [Str.Insts.CoreHashHash.hash, hs1, bind_ok, hs1v]
  exact WP.spec_mono (hw _ _) (fun r hr => by rw [hr, Slice.from_val])

/-! ## `Vec`, hashing, `HashMap` -/

/-- **Spec theorem for `Vec::is_empty`**: `true` exactly for the empty vector (the Aeneas library's
definition since the Aeneas upgrade of 2026-11-24, without the allocator argument). -/
@[step]
theorem alloc.vec.Vec.is_empty_spec {T : Type} (self : alloc.vec.Vec T) :
    alloc.vec.Vec.is_empty self ⦃ (result : Bool) => result = decide (self.val = []) ⦄ := by
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
    (bh : rmcp.core.hash.BuildHasher S Clause2_Hasher) (borrow : Aeneas.Std.core.borrow.Borrow K Q)
    (hashQ : core.hash.Hash Q) (eqQ : core.cmp.Eq Q)
    (self : std.collections.hash.map.HashMap K V S A) (k : Q) :
    std.collections.hash.map.HashMap.get eqK hashK bh borrow hashQ eqQ self k =
      ExtModel.HashMap.find borrow eqQ k self.entries := rfl

namespace Proofs.External.HashMap

/-- Lookup with the `String` instances is `List.find?` by key equality. -/
theorem find_string {V : Type} (q : String) :
    ∀ entries : List (String × V),
      ExtModel.HashMap.find (Aeneas.Std.core.borrow.Borrow.Blanket String)
        rmcp.alloc.string.String.Insts.CoreCmpEq q entries =
      ok ((entries.find? (fun e => decide (e.1 = q))).map Prod.snd)
  | [] => rfl
  | (k, v) :: rest => by
    simp only [ExtModel.HashMap.find, Aeneas.Std.core.borrow.Borrow.Blanket,
      core.borrow.Borrow.Blanket.borrow, rmcp.alloc.string.String.Insts.CoreCmpEq,
      rmcp.alloc.string.String.Insts.CoreCmpPartialEqString,
      alloc.string.String.Insts.CoreCmpPartialEqString.eq, bind_ok, List.find?_cons]
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
      (Aeneas.Std.core.borrow.Borrow.Blanket String) rmcp.alloc.string.String.Insts.CoreHashHash
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

open rmcp in
/-- **Lookup with a `&str` query** (`HashMap::get`/`contains_key` at `K = String`, `Q = str`, used
by `with_rs1_signing` and `with_rs1_fallback`): the value of the first entry whose key's UTF-8 bytes
are the query's bytes, provided every key has at most `Usize.max` bytes (the Lean model of
`Borrow<str> for String` fails above it; every Rust `String` meets it). -/
theorem find_borrowStr_eq {V : Type} (q : Str) : ∀ entries : List (String × V),
    (∀ e ∈ entries, e.1.utf8ByteSize ≤ Usize.max) →
    ExtModel.HashMap.find alloc.string.String.Insts.CoreBorrowBorrowStr Str.Insts.CoreCmpEq q
      entries = ok ((entries.find? (fun e => decide (utf8 e.1 = q.val))).map Prod.snd)
  | [], _ => rfl
  | (k, v) :: rest, h => by
    have hk : k.utf8ByteSize ≤ Usize.max := h (k, v) List.mem_cons_self
    have hk' : (utf8 k).length ≤ Usize.max := by rw [length_utf8]; exact hk
    have ih := find_borrowStr_eq q rest (fun e he => h e (List.mem_cons_of_mem _ he))
    obtain ⟨kb, hkb, hkbv⟩ := Proofs.External.WP.exists_ok_of_spec
      (alloc.string.String.Insts.CoreOpsDerefDerefStr.deref_spec k hk)
    have hb : alloc.string.String.Insts.CoreBorrowBorrowStr.borrow k = ok kb := hkb
    rw [ExtModel.HashMap.find]
    simp only [alloc.string.String.Insts.CoreBorrowBorrowStr, hb, bind_ok, Str.Insts.CoreCmpEq,
      Str.Insts.CoreCmpPartialEqStr, Str.Insts.CoreCmpPartialEqStr.eq, hkbv, List.find?_cons]
    by_cases hq : utf8 k = q.val
    · simp only [hq, decide_true, ↓reduceIte, Option.map_some]
    · have hq' : ¬ q.val = utf8 k := fun e => hq e.symm
      simp only [hq, hq', decide_false, Bool.false_eq_true, ↓reduceIte]
      exact ih

open rmcp in
/-- The slot lookup of `HashMap::entry` with the `String` equality of the translation is
`List.find?` by key equality. -/
theorem lookupEntry_string_eq {V : Type} (q : String) :
    ∀ entries : List (String × V),
      ExtModel.HashMap.lookupEntry alloc.string.String.Insts.CoreCmpEq q entries =
        ok (entries.find? (fun e => decide (e.1 = q)))
  | [] => rfl
  | (k, v) :: rest => by
    simp only [ExtModel.HashMap.lookupEntry, alloc.string.String.Insts.CoreCmpEq,
      alloc.string.String.Insts.CoreCmpPartialEqString,
      alloc.string.String.Insts.CoreCmpPartialEqString.eq, bind_ok, List.find?_cons]
    by_cases h : k = q
    · simp only [h, decide_true, ↓reduceIte]
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact lookupEntry_string_eq q rest

/-- `ExtModel.HashMap.find` for instances given by functions on the entries: `borrow` returns
`bor key` and `k == ·` returns `eqk` on it. The lookup is `List.find?` by `eqk ∘ bor`. -/
theorem find_eq {K V Q : Type} (borrow : Aeneas.Std.core.borrow.Borrow K Q)
    (eqQ : core.cmp.Eq Q) (k : Q) (bor : K → Q) (eqk : Q → Bool) :
    ∀ entries : List (K × V),
      (∀ e ∈ entries, borrow.borrow e.1 ⦃ (r : Q) => r = bor e.1 ⦄) →
      (∀ e ∈ entries, eqQ.partialEqInst.eq k (bor e.1) ⦃ (r : Bool) => r = eqk (bor e.1) ⦄) →
      ExtModel.HashMap.find borrow eqQ k entries =
        ok ((entries.find? (fun e => eqk (bor e.1))).map Prod.snd)
  | [], _, _ => rfl
  | (key, v) :: rest, hb, he => by
    obtain ⟨kb, hkb, rfl⟩ := Proofs.External.WP.exists_ok_of_spec (hb (key, v) List.mem_cons_self)
    obtain ⟨c, hc, hcv⟩ := Proofs.External.WP.exists_ok_of_spec (he (key, v) List.mem_cons_self)
    have ih := find_eq borrow eqQ k bor eqk rest (fun e h => hb e (List.mem_cons_of_mem _ h))
      (fun e h => he e (List.mem_cons_of_mem _ h))
    rw [ExtModel.HashMap.find, hkb, bind_ok, hc, bind_ok, List.find?_cons]
    dsimp only at hcv
    rw [← hcv]
    cases c
    · simp only [Bool.false_eq_true, ↓reduceIte, ih]
    · simp only [↓reduceIte, Option.map_some]

/-- `ExtModel.HashMap.lookupEntry` for an `Eq` instance given by a function on the entries:
`· == key` returns `eqk`. The slot lookup is `List.find?` by `eqk`. -/
theorem lookupEntry_eq {K V : Type} (eqK : core.cmp.Eq K) (key : K) (eqk : K → Bool) :
    ∀ entries : List (K × V),
      (∀ e ∈ entries, eqK.partialEqInst.eq e.1 key ⦃ (r : Bool) => r = eqk e.1 ⦄) →
      ExtModel.HashMap.lookupEntry eqK key entries = ok (entries.find? (fun e => eqk e.1))
  | [], _ => rfl
  | (k, v) :: rest, he => by
    obtain ⟨c, hc, hcv⟩ := Proofs.External.WP.exists_ok_of_spec (he (k, v) List.mem_cons_self)
    have ih := lookupEntry_eq eqK key eqk rest (fun e h => he e (List.mem_cons_of_mem _ h))
    rw [ExtModel.HashMap.lookupEntry, hc, bind_ok, List.find?_cons]
    dsimp only at hcv
    rw [← hcv]
    cases c
    · simp only [Bool.false_eq_true, ↓reduceIte, ih]
    · simp only [↓reduceIte]

end Proofs.External.HashMap

namespace Proofs.External.List

/-- `List.mapM` in `Result` of a function that returns `r x` on every element: `ok` of
`List.map r`. -/
theorem mapM_eq_ok {α β : Type} (g : α → Result β) (r : α → β) :
    ∀ l : List α, (∀ x ∈ l, g x ⦃ (y : β) => y = r x ⦄) → l.mapM g = ok (l.map r)
  | [], _ => rfl
  | x :: rest, h => by
    obtain ⟨y, hy, hyv⟩ := Proofs.External.WP.exists_ok_of_spec (h x List.mem_cons_self)
    rw [List.mapM_cons, hy, bind_tc_ok,
      mapM_eq_ok g r rest (fun z hz => h z (List.mem_cons_of_mem _ hz)), bind_tc_ok, hyv,
      pure_tc_eq, List.map_cons]

end Proofs.External.List

/-- **Spec theorem for `HashMap::get`**, for every key, value, hasher and allocator type and
every instance: if `borrow` returns `bor key` on the stored keys and `k == bor key` returns
`eqk (bor key)`, the value of the first entry whose key matches (`ExtModel.HashMap.find`). With
pairwise distinct keys (the Rust invariant) and an `Eq` that agrees with `Hash`, it is the value
stored under `k`; `get_string_spec` is the instance of the translation. -/
theorem std.collections.hash.map.HashMap.get_spec
    {K V S A Q Clause2_Hasher : Type} (eqK : core.cmp.Eq K) (hashK : core.hash.Hash K)
    (bh : rmcp.core.hash.BuildHasher S Clause2_Hasher) (borrow : Aeneas.Std.core.borrow.Borrow K Q)
    (hashQ : core.hash.Hash Q) (eqQ : core.cmp.Eq Q)
    (self : std.collections.hash.map.HashMap K V S A) (k : Q) (bor : K → Q) (eqk : Q → Bool)
    (hb : ∀ e ∈ self.entries, borrow.borrow e.1 ⦃ (r : Q) => r = bor e.1 ⦄)
    (he : ∀ e ∈ self.entries,
      eqQ.partialEqInst.eq k (bor e.1) ⦃ (r : Bool) => r = eqk (bor e.1) ⦄) :
    std.collections.hash.map.HashMap.get eqK hashK bh borrow hashQ eqQ self k
      ⦃ (result : Option V) =>
        result = (self.entries.find? (fun e => eqk (bor e.1))).map Prod.snd ⦄ := by
  rw [std.collections.hash.map.HashMap.get_eq,
    Proofs.External.HashMap.find_eq borrow eqQ k bor eqk self.entries hb he, WP.spec_ok]

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

/-- **Spec theorem for `<HashMap<K, V, S, A> as Clone>::clone`**, for every instance whose
`clone` returns `ck`, `cv`, `cs`, `ca` of the value (on the stored keys and values, the hash
builder and the allocator): the map of the clones, entries in the same order (from
`clone_eq`). -/
theorem std.collections.hash.map.HashMap.Insts.CoreCloneClone.clone_spec
    {K V S A : Type} (cK : core.clone.Clone K) (cV : core.clone.Clone V)
    (cS : core.clone.Clone S) (cA : core.clone.Clone A)
    (self : std.collections.hash.map.HashMap K V S A)
    (ck : K → K) (cv : V → V) (cs : S → S) (ca : A → A)
    (hK : ∀ e ∈ self.entries, cK.clone e.1 ⦃ (r : K) => r = ck e.1 ⦄)
    (hV : ∀ e ∈ self.entries, cV.clone e.2 ⦃ (r : V) => r = cv e.2 ⦄)
    (hS : cS.clone self.hash_builder ⦃ (r : S) => r = cs self.hash_builder ⦄)
    (hA : cA.clone self.alloc ⦃ (r : A) => r = ca self.alloc ⦄) :
    std.collections.hash.map.HashMap.Insts.CoreCloneClone.clone cK cV cS cA self
      ⦃ (result : std.collections.hash.map.HashMap K V S A) =>
        result = std.collections.hash.map.HashMap.mk (cs self.hash_builder) (ca self.alloc)
          (self.entries.map (fun e => (ck e.1, cv e.2))) ⦄ := by
  obtain ⟨s, hs, hsv⟩ := Proofs.External.WP.exists_ok_of_spec hS
  obtain ⟨a, ha, hav⟩ := Proofs.External.WP.exists_ok_of_spec hA
  have he := Proofs.External.List.mapM_eq_ok (fun (e : K × V) => do
      let k ← cK.clone e.1
      let v ← cV.clone e.2
      ok (k, v)) (fun e => (ck e.1, cv e.2)) self.entries (fun e he => by
    obtain ⟨k, hk, hkv⟩ := Proofs.External.WP.exists_ok_of_spec (hK e he)
    obtain ⟨v, hv, hvv⟩ := Proofs.External.WP.exists_ok_of_spec (hV e he)
    simp only [hk, hv, bind_ok, WP.spec_ok, hkv, hvv])
  rw [std.collections.hash.map.HashMap.Insts.CoreCloneClone.clone_eq, hs, bind_ok, ha, bind_ok,
    he, bind_ok, hsv, hav, WP.spec_ok]

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

/-- **Spec theorem for `<Zeroizing<Z> as Clone>::clone`**, for every `Clone` instance: the
wrapped value meets every postcondition that the instance's `clone` of the value meets. -/
theorem zeroize.Zeroizing.Insts.CoreCloneClone.clone_spec {Z : Type}
    (inst : rmcp.zeroize.Zeroize Z) (cZ : core.clone.Clone Z) (self : zeroize.Zeroizing Z)
    (P : Z → Prop) (h : cZ.clone self.inner ⦃ P ⦄) :
    zeroize.Zeroizing.Insts.CoreCloneClone.clone inst cZ self
      ⦃ (result : zeroize.Zeroizing Z) => P result.inner ⦄ := by
  obtain ⟨v, hv, hP⟩ := Proofs.External.WP.exists_ok_of_spec h
  simp only [zeroize.Zeroizing.Insts.CoreCloneClone.clone, hv, bind_ok, WP.spec_ok]
  exact hP

/-- `<Z as Zeroize>::zeroize` for `Z: DefaultIsZeroes` is `Z::default()`. -/
theorem zeroize.Zeroize.Blanket.zeroize_eq {Z : Type} (inst : rmcp.zeroize.DefaultIsZeroes Z)
    (self : Z) :
    zeroize.Zeroize.Blanket.zeroize inst self = inst.coredefaultDefaultInst.default := rfl

/-- **Spec theorem for `<Z as Zeroize>::zeroize` for `Z: DefaultIsZeroes`**, for every instance:
the result meets every postcondition that `Z::default()` meets. -/
theorem zeroize.Zeroize.Blanket.zeroize_spec {Z : Type} (inst : rmcp.zeroize.DefaultIsZeroes Z)
    (self : Z) (P : Z → Prop) (h : inst.coredefaultDefaultInst.default ⦃ P ⦄) :
    zeroize.Zeroize.Blanket.zeroize inst self ⦃ P ⦄ := by
  rw [zeroize.Zeroize.Blanket.zeroize_eq]
  exact h

/-- `<Vec<Z> as Zeroize>::zeroize` zeroizes each element and returns the empty vector. -/
theorem alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize_eq {Z : Type} (inst : rmcp.zeroize.Zeroize Z)
    (self : alloc.vec.Vec Z) :
    alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize inst self =
      (do let _ ← self.val.mapM inst.zeroize; ok (alloc.vec.Vec.new Z)) := rfl

/-- **Spec theorem for `<Vec<Z> as Zeroize>::zeroize`**, for every instance whose `zeroize`
succeeds on each element: the empty vector. -/
theorem alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize_spec {Z : Type} (inst : rmcp.zeroize.Zeroize Z)
    (self : alloc.vec.Vec Z) (hz : ∀ x ∈ self.val, inst.zeroize x ⦃ (_ : Z) => True ⦄) :
    alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize inst self ⦃ (result : alloc.vec.Vec Z) =>
      result = alloc.vec.Vec.new Z ⦄ := by
  have hm : ∀ l : List Z, (∀ x ∈ l, inst.zeroize x ⦃ (_ : Z) => True ⦄) →
      ∃ l', l.mapM inst.zeroize = ok l' := by
    intro l
    induction l with
    | nil => intro _; exact ⟨[], rfl⟩
    | cons x rest ih =>
      intro h
      obtain ⟨y, hy, -⟩ := Proofs.External.WP.exists_ok_of_spec (h x List.mem_cons_self)
      obtain ⟨l', hl'⟩ := ih (fun z hz => h z (List.mem_cons_of_mem _ hz))
      exact ⟨y :: l', by rw [List.mapM_cons, hy, bind_tc_ok, hl', bind_tc_ok, pure_tc_eq]⟩
  obtain ⟨l', hl'⟩ := hm self.val hz
  simp only [alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize, hl', bind_ok, WP.spec_ok]

/-! ## Clock

No statement about the function `RequestStateCodec::now_ms` other than its spec theorem (nor the functions `open`,
`open_with`, `open_json`, `open_json_with`, `seal`, `seal_with`; Lean
`rmcp.model.request_state.RequestStateCodec.{now_ms, open, open_with, open_json,
open_json_with, seal, seal_with}`; a variable named `now_ms` is not covered): the clock is one
opaque constant `ExtModel.nowMs`, which makes every reader pure, so a statement about it could
relate readings in a way the Rust code does not guarantee (review rule, `formal/README.md`,
"Trusted base"). Statements about opening use `open_at`, and about sealing `seal_at` (or its
model `sealAt`), with an explicit time, except the spec theorems of the public `open`/`open_with`
(postcondition `resultBytes result = openAt … ExtModel.nowMs.val`), `open_json`/`open_json_with`
(the error of `openAt … ExtModel.nowMs.val` unchanged, otherwise the `serdeJsonFromSlice`
outcome of the opened payload with `Err` mapped to `Deserialization`) and `seal`/`seal_with`
(`sealAt … ExtModel.nowMs.val = some (ExtModel.utf8 result)`), their restatements and the
corollaries `open_with_spec_of_length_le`, `seal_with_spec_of_length_le` and
`seal_spec_of_length_le` (human decisions 2026-11-24, extended 2026-11-25; wording in
`formal/README.md`, "Trusted base"), and the model's own spec theorem
`model.request_state.RequestStateCodec.now_ms_spec` below (`result = ExtModel.nowMs`, nothing
else; human decision 2026-11-25). -/

/-- **Spec theorem for `RequestStateCodec::now_ms`**: the one clock reading `ExtModel.nowMs`
(an opaque constant). The only statement besides the listed exceptions that names `now_ms` or
`nowMs` (human decision 2026-11-25); it says nothing about the value and relates no two
readings. -/
theorem model.request_state.RequestStateCodec.now_ms_spec :
    model.request_state.RequestStateCodec.now_ms ⦃ (result : I64) => result = nowMs ⦄ := by
  simp only [model.request_state.RequestStateCodec.now_ms, WP.spec_ok]

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
  simp only [Array.Insts.CoreSliceSlicePattern.as_slice, Array.to_slice, WP.spec_ok,
    Slice.from_val]

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
        Proofs.External.WP.exists_ok_of_spec (h_ne a List.mem_cons_self b List.mem_cons_self)
      simp only [ExtModel.sliceEqSameLength, hd, bind_ok, List.forall₂_cons]
      cases d with
      | true =>
        simp only [↓reduceIte, WP.spec_ok, Bool.false_eq_true, false_iff, not_and]
        exact fun hR => absurd hR (hP.1 rfl)
      | false =>
        have hR : R a b := by simpa only [Bool.false_eq_true, false_iff, not_not] using hP
        simp only [hR, true_and]
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
  simp only [h_suf, bind_ok]
  split
  · rename_i hle
    have hle' : suf.val.length ≤ self.val.length := by
      have := hle; simp only [UScalar.le_equiv, Slice.len_val] at this; exact this
    obtain ⟨mid, hmid, hmv, -⟩ := Proofs.External.WP.exists_ok_of_spec (Usize.sub_spec hle)
    have hsl : ∀ s : Slice T, s.length = s.val.length := fun _ => rfl
    simp only [Slice.len_val, hsl] at hmv
    have hmle : mid.val ≤ self.length := by rw [hmv, hsl]; omega
    have hdrop : (self.val.drop mid.val).length = suf.val.length := by
      rw [List.length_drop, hmv]; omega
    obtain ⟨⟨head, tail⟩, hsp, hP⟩ :=
      Proofs.External.WP.exists_ok_of_spec (core.slice.Slice.split_at.spec self mid hmle)
    simp only [WP.uncurry'_pair] at hP
    obtain ⟨-, -, hhead, htail⟩ := hP
    have hdrop' : tail.val.length = suf.val.length := by rw [htail]; exact hdrop
    rw [hmid, bind_ok, hsp, bind_ok]
    show (do
      let b ← ExtModel.sliceEq cmpPartialEqInst tail.val suf.val
      if b then ok (some head) else ok none) ⦃ (result : Option (Slice T)) =>
        match result with
        | some head => ∃ tail, self.val = head.val ++ tail ∧ List.Forall₂ R tail suf.val
        | none =>
          ¬ ∃ head tail, self.val = head ++ tail ∧ List.Forall₂ R tail suf.val ⦄
    rw [ExtModel.sliceEq, ite_eq_left hdrop']
    obtain ⟨b, hb, hbP⟩ := Proofs.External.WP.exists_ok_of_spec (Proofs.External.Slice.sliceEqSameLength_spec
      cmpPartialEqInst R _ _ hdrop'
      (fun x hx y hy => h_ne x (by rw [htail] at hx; exact List.mem_of_mem_drop hx) y hy))
    rw [hb, bind_ok]
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
    rw [core.slice.Slice.strip_suffix, h, bind_fail]
  · intro h
    rw [core.slice.Slice.strip_suffix, h, bind_div]

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
`start ≤ item < start` (so never) for an exhausted one; never fails. `contains`
(`core/src/ops/range.rs` lines 539–545) calls `RangeBounds::contains`, `start_bound <= item &&
item <= / < end_bound` (lines 886–900), with bounds `Included(start)` and `Included(end)`, or
`Excluded(start)` when `exhausted` (lines 1142–1157). -/
@[step]
theorem core.ops.range.RangeInclusive.contains_u8_spec
    (self : core.ops.range.RangeInclusive U8) (item : U8) :
    core.ops.range.RangeInclusive.contains core.cmp.PartialOrdU8 core.cmp.PartialOrdU8
        core.cmp.PartialOrdU8 self item ⦃ (result : Bool) =>
      (result = true ↔ self.start.val ≤ item.val ∧
        (if self.exhausted then item.val < self.start.val
         else item.val ≤ self.«end».val)) ⦄ := by
  unfold core.ops.range.RangeInclusive.contains
  cases hx : self.exhausted <;> by_cases h1 : self.start.val ≤ item.val <;>
    simp only [liftFun2, core.cmp.impls.PartialOrdU8.le, h1, decide_true, Bool.false_eq_true,
      ↓reduceIte, true_and, decide_false, false_and,
      iff_false, Bool.not_eq_true, core.cmp.impls.PartialOrdU8.lt, bind_ok, WP.spec_ok,
      decide_eq_true_eq]

/-- **`(a..=b).contains(&x)` for `u8`**: `a ≤ x ≤ b`. -/
theorem core.ops.range.RangeInclusive.new_contains_u8_spec (a b item : U8) :
    (do
      let r ← core.ops.range.RangeInclusive.new a b
      core.ops.range.RangeInclusive.contains core.cmp.PartialOrdU8 core.cmp.PartialOrdU8
        core.cmp.PartialOrdU8 r item) ⦃ (result : Bool) =>
      (result = true ↔ a.val ≤ item.val ∧ item.val ≤ b.val) ⦄ := by
  simp only [core.ops.range.RangeInclusive.new, bind_ok]
  exact core.ops.range.RangeInclusive.contains_u8_spec ⟨a, b, false⟩ item

/-- `RangeInclusive::contains`, for every instance: `start <= item` is evaluated first; if it
fails or diverges that propagates, if it is `false` the result is `false` without a second
call, and if it is `true` the result is `item < start` (exhausted) or `item <= end` (not
exhausted), including its failure. Rust: `RangeBounds::contains` (`core/src/ops/range.rs`
lines 886–900, `&&` short-circuits) with `end_bound` = `Excluded(&self.start)` if `exhausted`,
else `Included(&self.end)` (lines 1142–1157). -/
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
        if self.exhausted then cmpPartialOrdInst2.lt item self.start
        else cmpPartialOrdInst2.le item self.«end») := by
  refine ⟨fun e h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    simp only [core.ops.range.RangeInclusive.contains, h, bind_fail, bind_div, bind_ok,
      Bool.false_eq_true, ↓reduceIte]

/-- **Spec theorem for `RangeInclusive::contains`**, for every index type and every instance:
if `start <= item` returns `lo` and, when `lo` is `true`, the second comparison (`item < start`
for an exhausted range, `item <= end` otherwise) returns `hi`, the result is `lo && hi` (the
second comparison is not made when `lo` is `false`; `contains_eq_match_le` gives the failing
cases, `contains_u8_spec` the instance of the translation). -/
theorem core.ops.range.RangeInclusive.contains_spec {Idx : Type} {U : Type}
    (cmpPartialOrdInst : core.cmp.PartialOrd Idx Idx)
    (cmpPartialOrdInst1 : core.cmp.PartialOrd Idx U)
    (cmpPartialOrdInst2 : core.cmp.PartialOrd U Idx)
    (self : core.ops.range.RangeInclusive Idx) (item : U) (lo hi : Bool)
    (hlo : cmpPartialOrdInst1.le self.start item ⦃ (r : Bool) => r = lo ⦄)
    (hhi : lo = true →
      (if self.exhausted then cmpPartialOrdInst2.lt item self.start
       else cmpPartialOrdInst2.le item self.«end») ⦃ (r : Bool) => r = hi ⦄) :
    core.ops.range.RangeInclusive.contains cmpPartialOrdInst cmpPartialOrdInst1
      cmpPartialOrdInst2 self item ⦃ (result : Bool) => result = (lo && hi) ⦄ := by
  obtain ⟨b, hb, rfl⟩ := Proofs.External.WP.exists_ok_of_spec hlo
  cases b with
  | false =>
    simp only [core.ops.range.RangeInclusive.contains, hb, bind_ok, Bool.false_eq_true,
      ↓reduceIte, WP.spec_ok, Bool.false_and]
  | true =>
    have h := hhi rfl
    simp only [core.ops.range.RangeInclusive.contains, hb, bind_ok, ↓reduceIte, Bool.true_and]
    exact h

/-! ## Public `request_state.rs` API (R09–R15)

Spec theorems for the externals of the section of the same name in
`formal/trusted/Rmcp/FunsExternal.lean` that had none (added 2026-11-25, human decision: every
external reached by the translation has a `_spec` theorem). Where the external takes a closure or
a trait instance whose behaviour is not fixed, the theorem takes that behaviour as a hypothesis
and is not a `step` lemma. `HashMapKVRandomStateGlobal.new_spec` states only the entries: the
review rule at `ExtModel.randomState` forbids a statement about the `hash_builder` of a map built
by `HashMap::new`. `serde_json.de.from_slice_spec` states the opaque outcome
`ExtModel.serdeJsonFromSlice` and nothing about it. -/

/-- **Spec theorem for `Duration::as_millis`**: the whole milliseconds,
`secs * 1000 + nanos / 1_000_000`, exactly (it is below `2^128`); never fails. -/
@[step]
theorem core.time.Duration.as_millis_spec (self : core.time.Duration) :
    core.time.Duration.as_millis self ⦃ (result : U128) =>
      result.val = self.secs.val * 1000 + self.nanos.val / 1000000 ⦄ := by
  simp only [core.time.Duration.as_millis, WP.spec_ok]
  have h1 := self.secs.hBounds
  have h2 := self.nanos_lt
  show (BitVec.ofNat 128 _).toNat = _
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  simp only [UScalarTy.U64_numBits_eq] at h1
  omega

/-- **Spec theorem for `HashMap::contains_key`**, for the instances of `get_spec`: whether an
entry's key matches (`k == key.borrow()`). -/
theorem std.collections.hash.map.HashMap.contains_key_spec
    {K V S A Q Clause2_Hasher : Type} (eqK : core.cmp.Eq K) (hashK : core.hash.Hash K)
    (bh : core.hash.BuildHasher S Clause2_Hasher) (borrow : Aeneas.Std.core.borrow.Borrow K Q)
    (hashQ : core.hash.Hash Q) (eqQ : core.cmp.Eq Q)
    (self : std.collections.hash.map.HashMap K V S A) (k : Q) (bor : K → Q) (eqk : Q → Bool)
    (hb : ∀ e ∈ self.entries, borrow.borrow e.1 ⦃ (r : Q) => r = bor e.1 ⦄)
    (he : ∀ e ∈ self.entries,
      eqQ.partialEqInst.eq k (bor e.1) ⦃ (r : Bool) => r = eqk (bor e.1) ⦄) :
    std.collections.hash.map.HashMap.contains_key eqK hashK bh borrow hashQ eqQ self k
      ⦃ (result : Bool) => result = self.entries.any (fun e => eqk (bor e.1)) ⦄ := by
  simp only [std.collections.hash.map.HashMap.contains_key,
    Proofs.External.HashMap.find_eq borrow eqQ k bor eqk self.entries hb he, bind_ok, WP.spec_ok,
    Option.isSome_map]
  exact Bool.eq_iff_iff.2 (by rw [List.find?_isSome, List.any_eq_true])

/-- **Spec theorem for `HashMap::is_empty`**: `true` exactly for no entries; never fails. -/
@[step]
theorem std.collections.hash.map.HashMap.is_empty_spec {K V S A : Type}
    (self : std.collections.hash.map.HashMap K V S A) :
    std.collections.hash.map.HashMap.is_empty self ⦃ (result : Bool) =>
      (result = true ↔ self.entries = []) ⦄ := by
  simp only [std.collections.hash.map.HashMap.is_empty, WP.spec_ok, List.isEmpty_iff]

/-- **Spec theorem for `HashMap::new`**: a map with no entries; never fails. Its `hash_builder`
(`ExtModel.randomState`) is not stated (review rule at `ExtModel.randomState`). -/
@[step]
theorem std.collections.hash.map.HashMapKVRandomStateGlobal.new_spec (K V : Type) :
    std.collections.hash.map.HashMapKVRandomStateGlobal.new K V
      ⦃ (result : std.collections.hash.map.HashMap K V std.hash.random.RandomState
          alloc.alloc.Global) => result.entries = [] ⦄ := by
  simp only [std.collections.hash.map.HashMapKVRandomStateGlobal.new, WP.spec_ok]

/-- **Spec theorem for `HashMap::entry`**, for every `Eq` instance on the keys whose
`stored == key` returns `eqk stored` on the stored keys: the first entry whose key matches as
an `Occupied` entry (the write-back leaves the map unchanged); otherwise a `Vacant` entry for
`key`, whose write-back appends `(key, v)` once `VacantEntry::insert` has stored `v`. -/
theorem std.collections.hash.map.HashMap.entry_spec
    {K V S A Clause2_Hasher : Type} (eqK : core.cmp.Eq K) (hashK : core.hash.Hash K)
    (bh : core.hash.BuildHasher S Clause2_Hasher)
    (self : std.collections.hash.map.HashMap K V S A) (key : K) (eqk : K → Bool)
    (he : ∀ e ∈ self.entries, eqK.partialEqInst.eq e.1 key ⦃ (r : Bool) => r = eqk e.1 ⦄) :
    std.collections.hash.map.HashMap.entry eqK hashK bh self key
      ⦃ (result : (std.collections.hash.map.Entry K V A) ×
          (std.collections.hash.map.Entry K V A → std.collections.hash.map.HashMap K V S A)) =>
        result = match self.entries.find? (fun e => eqk e.1) with
          | some (k, v) =>
            (std.collections.hash.map.Entry.Occupied { key := k, value := v }, fun _ => self)
          | none =>
            (std.collections.hash.map.Entry.Vacant { key := key, inserted := none },
              fun e => match e with
                | std.collections.hash.map.Entry.Vacant { key := k, inserted := some v } =>
                  { self with entries := self.entries ++ [(k, v)] }
                | _ => self) ⦄ := by
  simp only [std.collections.hash.map.HashMap.entry,
    Proofs.External.HashMap.lookupEntry_eq eqK key eqk self.entries he, bind_ok]
  generalize self.entries.find? (fun e => eqk e.1) = o
  rcases o with _ | ⟨k, v⟩ <;> exact (WP.spec_ok _).2 rfl

/-- **Spec theorem for `VacantEntry::insert`**: returns the value, and the entry's write-back
stores the final value in `inserted`; never fails. -/
@[step]
theorem std.collections.hash.map.VacantEntry.insert_spec {K V A : Type}
    (self : std.collections.hash.map.VacantEntry K V A) (value : V) :
    std.collections.hash.map.VacantEntry.insert self value
      ⦃ (result : V × (V → std.collections.hash.map.VacantEntry K V A)) =>
        result.1 = value ∧ ∀ v, result.2 v = { self with inserted := some v } ⦄ := by
  simp only [std.collections.hash.map.VacantEntry.insert, WP.spec_ok, implies_true, and_self]

/-- **Spec theorem for `serde_json::from_slice`**: the opaque outcome
`ExtModel.serdeJsonFromSlice` of the instance on the bytes; never fails (a panicking or
non-terminating `Deserialize` impl is not modelled). Nothing about the outcome is stated. -/
@[step]
theorem serde_json.de.from_slice_spec {T : Type}
    (serde_coredeDeserializeInst : serde_core.de.Deserialize T) (v : Slice U8) :
    serde_json.de.from_slice serde_coredeDeserializeInst v
      ⦃ (result : core.result.Result T serde_json.error.Error) =>
        result = serdeJsonFromSlice serde_coredeDeserializeInst v.val ⦄ := by
  simp only [serde_json.de.from_slice, WP.spec_ok]

/-- **Spec theorem for the default `Error::source`**: `None`, for every error type; never
fails. -/
@[step]
theorem core.error.Error.source.default_spec {Self : Type} (ErrorInst : core.error.Error Self)
    (self : Self) :
    core.error.Error.source.default ErrorInst self
      ⦃ (result : Option (Dyn (fun _dyn => core.error.Error _dyn))) => result = none ⦄ := by
  simp only [core.error.Error.source.default, WP.spec_ok]

namespace Proofs.External.SliceIter

/-- `ExtModel.sliceIterAny` with a closure that computes `p` without changing its state:
`List.any`, after `findIdx p + 1` elements if an element satisfies `p`, otherwise after the
whole list. -/
theorem sliceIterAny_eq {T F : Type} (inst : core.ops.function.FnMut F T Bool) (p : T → Bool)
    (f : F) (hp : ∀ x, inst.call_mut f x = ok (p x, f)) :
    ∀ l : List T, sliceIterAny inst l f =
      ok (l.any p, if l.any p then l.findIdx p + 1 else l.length)
  | [] => rfl
  | x :: rest => by
    have ih := sliceIterAny_eq inst p f hp rest
    simp only [sliceIterAny, hp, bind_ok, uncurry_apply_pair, List.any_cons, List.findIdx_cons,
      List.length_cons]
    cases hpx : p x
    · simp only [Bool.false_eq_true, ↓reduceIte, ih, bind_ok, Bool.false_or]
      split <;> rfl
    · simp only [↓reduceIte, Bool.true_or]

end Proofs.External.SliceIter

/-- **Spec theorem for `<slice::Iter<'_, T> as Iterator>::any`**, for every closure instance that
computes `p` without changing its state: whether `p` holds for a remaining element, and the
iterator moved past the first such element (or to the end). -/
theorem core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any_spec
    {T : Type} {F : Type} (opsfunctionFnMutFTupleSharedATBoolInst : core.ops.function.FnMut F T Bool)
    (p : T → Bool) (self : core.slice.iter.Iter T) (f : F)
    (hf : ∀ x, opsfunctionFnMutFTupleSharedATBoolInst.call_mut f x = ok (p x, f)) :
    core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any
      opsfunctionFnMutFTupleSharedATBoolInst self f
      ⦃ (result : Bool × core.slice.iter.Iter T) =>
        result.1 = (self.slice.val.drop self.i).any p ∧
        result.2 = { self with i := self.i +
          if (self.slice.val.drop self.i).any p then (self.slice.val.drop self.i).findIdx p + 1
          else (self.slice.val.drop self.i).length } ⦄ := by
  simp only [core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any,
    Proofs.External.SliceIter.sliceIterAny_eq opsfunctionFnMutFTupleSharedATBoolInst p f hf,
    bind_ok]
  exact (WP.spec_ok _).2 ⟨rfl, rfl⟩

/-- **Spec theorem for the default `Iterator::any`**

For an iterator state `self` satisfying a state invariant `inv` whose `next`, on every state
satisfying `inv`, yields the elements of `rest it` in order, keeps `inv`, and on an empty
`rest it` yields no element and a state with no remaining element, and a closure that computes
`p` without changing its state: the result is whether `p` holds for some remaining element, and
the final iterator state satisfies `inv` and has moved past the first element satisfying `p` (or
to the end). (`inv` restricts the hypothesis on `next` to the states the loop reaches; take
`fun _ => True` for an iterator whose `next` behaves so on every state.) -/
theorem core.iter.traits.iterator.Iterator.any.default_spec {Self : Type} {F : Type}
    {Item : Type} (IteratorInst : core.iter.traits.iterator.Iterator Self Item)
    (FnMutInst : core.ops.function.FnMut F Item Bool) (inv : Self → Prop)
    (rest : Self → List Item) (p : Item → Bool) (self : Self) (f : F) (hself : inv self)
    (hnext : ∀ it, inv it → IteratorInst.next it ⦃ (r : Option Item × Self) =>
      inv r.2 ∧ match r.1 with
      | none => rest it = [] ∧ rest r.2 = []
      | some x => rest it = x :: rest r.2 ⦄)
    (hf : ∀ x, FnMutInst.call_mut f x = ok (p x, f)) :
    core.iter.traits.iterator.Iterator.any.default IteratorInst FnMutInst self f
      ⦃ (result : Bool × Self) =>
        result.1 = (rest self).any p ∧ inv result.2 ∧
        rest result.2 = (rest self).drop
          (if (rest self).any p then (rest self).findIdx p + 1 else (rest self).length) ⦄ := by
  unfold core.iter.traits.iterator.Iterator.any.default
  apply loop.spec_decr_nat (fun st : Self × F => (rest st.1).length)
    (fun st => st.2 = f ∧ inv st.1 ∧
      ∃ pre : List Item, pre.any p = false ∧ rest self = pre ++ rest st.1)
  · rintro ⟨it, g⟩ ⟨hg, hinv, pre, hpre, hsplit⟩
    dsimp only at hg hinv hsplit
    subst hg
    obtain ⟨⟨o, it'⟩, hr, hinv', hpost⟩ := Proofs.External.WP.exists_ok_of_spec (hnext it hinv)
    dsimp only
    rw [hr, bind_ok]
    cases o with
    | none =>
      refine (WP.spec_ok _).2 ?_
      dsimp only at hpost hinv' ⊢
      obtain ⟨hnil, hnil'⟩ := hpost
      rw [hnil, List.append_nil] at hsplit
      subst hsplit
      refine ⟨hpre.symm, hinv', ?_⟩
      rw [hnil']
      simp only [hpre, Bool.false_eq_true, ↓reduceIte, List.drop_length]
    | some x =>
      dsimp only at hpost hinv'
      simp only [hf, bind_ok, uncurry_apply_pair]
      cases hpx : p x
      · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        refine ⟨⟨trivial, hinv', pre ++ [x], ?_, ?_⟩, ?_⟩
        · rw [List.any_append, hpre, List.any_cons, List.any_nil, hpx]; rfl
        · rw [hsplit, hpost, List.append_assoc, List.singleton_append]
        · rw [hpost, List.length_cons]; omega
      · simp only [↓reduceIte, WP.spec_ok]
        have hany : (rest self).any p = true := by
          rw [hsplit, hpost, List.any_append, List.any_cons, hpx, Bool.true_or, Bool.or_true]
        have hidx : (rest self).findIdx p = pre.length := by
          rw [hsplit, hpost]
          clear hsplit hpost hinv
          induction pre with
          | nil => rw [List.nil_append, List.findIdx_cons, hpx]; rfl
          | cons y ys ih =>
            rw [List.any_cons, Bool.or_eq_false_iff] at hpre
            rw [List.cons_append, List.findIdx_cons, hpre.1, ih hpre.2, List.length_cons]; rfl
        refine ⟨hany.symm, hinv', ?_⟩
        simp only [hany, ↓reduceIte]
        rw [hidx, hsplit, hpost, List.drop_append, List.drop_eq_nil_of_le (by omega),
          List.nil_append, Nat.add_sub_cancel_left, List.drop_one, List.tail_cons]
  · exact ⟨rfl, hself, [], rfl, rfl⟩
