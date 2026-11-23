/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Aeneas
import Rmcp.Types

/-!
External functions of the `rmcp` translation (`Rmcp.Funs` imports this module).

Started at plan step S04a from the template that Aeneas generated
(`formal/translation/Rmcp/FunsExternal_Template.lean`) for the translation of commit
`9b030c6` with the Charon settings of S04a part 2 (derived `Debug` impls excluded), Aeneas
`nightly-2026.08.20-5d08da4`. Plan steps S08 (HMAC and Base64 `prim` functions) and S09
(standard library, `HashMap`, clock) replaced every placeholder of the template by a
definition with the generated name and signature, keeping the template's `@[rust_fun]` attribute
where it has one (the external functions of other crates; the five opaque `rmcp` functions, the
four `prim` functions and `RequestStateCodec::now_ms`, have none in the template). **This module
declares no axiom.** The two things the models cannot compute are `opaque` constants, which
add no axiom: the HMAC-SHA256 reference function `ExtModel.hmacSha256` and the clock reading
`ExtModel.nowMs` (and, for the unused hasher, `ExtModel.sipHash13`).

Each definition returns `ok` exactly where the Rust function returns and `fail` where it
panics, with the exceptions stated in its docstring. Two conventions apply throughout:

* **Memory.** Allocation failure (out of memory) is not modelled (plan Section 4: unlimited
  memory is not established). A `String` that would grow beyond `isize::MAX` bytes is a
  deterministic Rust panic ("capacity overflow": `RawVec::grow_amortized`, lines 502–533 of
  `alloc/src/raw_vec/mod.rs`, through `finish_grow`, lines 543–568, and
  `RawVec::try_allocate_in`, lines 446–482, compute the layout with `layout_array`, lines
  896–902, which returns `CapacityOverflow` for a layout larger than `isize::MAX`; `handle_error`,
  lines 887–892, turns it into the panic) and is modelled as `fail panic`
  (`ExtModel.growString`). A panic that depends on the capacity history (amortized doubling
  past `isize::MAX` while the length still fits) is not modelled, so `ok` from a `String`
  model means "returns, or aborts or panics for memory reasons".
* **`Str`.** The Aeneas `Str` is `Slice U8` and admits byte sequences that are not UTF-8,
  while a Rust `&str` is always UTF-8. Functions that only read the bytes (`str::len`,
  `str::as_bytes`) are modelled on all of `Str`; `String::push_str`, which builds a `String`
  from the bytes, returns `fail undef` outside the Rust domain (a non-UTF-8 `&str` is undefined
  behaviour in Rust).
* **Size convention.** A `Slice` or `String` of the model may be up to `Usize.max` bytes long,
  more than any machine can hold. The models make no claim about inputs of at least `2^61`
  bytes (2 EiB): such an input cannot exist in a running process on the translated target
  `x86_64-unknown-linux-gnu`, whose virtual address space is at most `2^57` bytes (5-level
  paging), and plan Section 4 does not model memory limits. The only behaviour this convention
  hides is the SHA-256 length overflow of the HMAC functions (section HMAC).

Source paths: `/rustc/library/…` is the `rust-src` of the pinned toolchain `nightly-2026-06-01`;
`/cargo/registry/…` is the crate at the version in the path. `scripts/aeneas-translate.sh`
pins every crate cited here (`PINNED_DEPS`): `hmac 0.13.0`, `sha2 0.11.1`, `base64 0.23.1`,
`digest 0.11.3`, `zeroize 1.9.2`, `chrono 0.4.45` and `serde_json 1.0.154` (plan Section 4). The
Rust tests that check the models are listed in `formal/trusted/evidence/README.md`.
-/
open Aeneas Aeneas.Std Result ControlFlow Error
open rmcp

/-! ## Model functions

Pure functions used by the definitions below. They are root-level names in the namespace
`ExtModel` (never `rmcp`, see `formal/README.md`, "Trusted base"). -/

namespace ExtModel

/-- The byte with value `n % 256`. -/
def byte (n : Nat) : Std.U8 := ⟨BitVec.ofNat _ n⟩

/-- The UTF-8 bytes of a Lean `String` (its `toByteArray`, as `U8` values; the same conversion
as the Aeneas `toStr` for literals). A Lean `String` is always valid UTF-8, as is a Rust
`String`. -/
def utf8 (s : String) : List Std.U8 := s.toByteArray.toList.map (fun x => byte x.toNat)

/-- The `String` whose UTF-8 encoding is `l`, or `none` if `l` is not valid UTF-8 (Lean's
`String.fromUTF8?`, which accepts exactly the encodings of lists of Unicode scalar values: no
surrogates, no overlong forms, nothing above `U+10FFFF`; the same set as Rust's
`core::str::from_utf8`, `core/src/str/validations.rs`, `run_utf8_validation`). -/
def strOfBytes? (l : List Std.U8) : Option String :=
  String.fromUTF8? ⟨(l.map (fun b => b.val.toUInt8)).toArray⟩

/-- The largest byte length of a Rust `String`: `isize::MAX` (`alloc/src/raw_vec/mod.rs`,
`layout_array` fails above it). -/
def maxStringBytes : Nat := Isize.max.toNat

/-- `ok r` if `r` fits in a Rust `String`, otherwise the "capacity overflow" panic of the
reservation that would create it. -/
def growString (r : String) : Result String :=
  if r.utf8ByteSize ≤ maxStringBytes then ok r else fail panic

/-! ### HMAC-SHA256 -/

/-- **HMAC-SHA256 reference function** (opaque): `hmacSha256 key msg` is the 32-byte
HMAC-SHA256 tag of `msg` under `key` (RFC 2104 with SHA-256, FIPS 180-4), for a key of any
length. Opaque because its value is not modelled (plan Section 4; the correctness of the
`hmac`/`sha2` crates is not established). The value given here only shows that the type is
inhabited; an `opaque` constant does not unfold to it. -/
opaque hmacSha256 : List Std.U8 → List Std.U8 → Std.Array Std.U8 32#usize :=
  fun _ _ => ⟨List.replicate 32 (byte 0), by simp⟩

/-! ### Base64url without padding -/

/-- The symbol of the URL-safe alphabet for the 6-bit value `n` (RFC 4648 Section 5, Table 2:
`A`–`Z` = 0–25, `a`–`z` = 26–51, `0`–`9` = 52–61, `-` = 62, `_` = 63; `base64-0.23.1`
`src/alphabet.rs` lines 259–262, `URL_SAFE`). Values above 63 do not occur. -/
def b64Sym (n : Nat) : Std.U8 :=
  if n < 26 then byte (65 + n)
  else if n < 52 then byte (97 + (n - 26))
  else if n < 62 then byte (48 + (n - 52))
  else if n = 62 then byte 45
  else byte 95

/-- The 6-bit value of a symbol of the URL-safe alphabet, `none` for every other byte
(including the padding byte `=` and the standard-alphabet symbols `+` and `/`). -/
def b64Val (c : Std.U8) : Option Nat :=
  if 65 ≤ c.val ∧ c.val ≤ 90 then some (c.val - 65)
  else if 97 ≤ c.val ∧ c.val ≤ 122 then some (c.val - 71)
  else if 48 ≤ c.val ∧ c.val ≤ 57 then some (c.val + 4)
  else if c.val = 45 then some 62
  else if c.val = 95 then some 63
  else none

/-- **Base64url encoding without padding** (RFC 4648 Section 5; Section 3.2 without the `=`
padding): every 3 bytes give 4 symbols, a final 1 or 2 bytes give 2 or 3 symbols whose unused
low bits are zero. This is the output of `base64-0.23.1` `URL_SAFE_NO_PAD`
(`src/engine/general_purpose/mod.rs` line 472: alphabet `URL_SAFE`, config `NO_PAD` =
`encode_padding = false`, lines 499–501), produced by `Engine::encode_string`
(`src/engine/mod.rs` lines 188–201) through `ChunkedEncoder` (`src/chunked_encoder.rs`), which
encodes 768-byte chunks (a multiple of 3, so the chunking does not change the output). -/
def b64 : List Std.U8 → List Std.U8
  | a :: b :: c :: rest =>
    b64Sym (a.val / 4) :: b64Sym (a.val % 4 * 16 + b.val / 16) ::
      b64Sym (b.val % 16 * 4 + c.val / 64) :: b64Sym (c.val % 64) :: b64 rest
  | [a, b] => [b64Sym (a.val / 4), b64Sym (a.val % 4 * 16 + b.val / 16), b64Sym (b.val % 16 * 4)]
  | [a] => [b64Sym (a.val / 4), b64Sym (a.val % 4 * 16)]
  | [] => []

/-- **Strict Base64url decoding without padding**, as `base64-0.23.1` `URL_SAFE_NO_PAD`
decodes (`Engine::decode`, `src/engine/mod.rs` lines 277–301; `decode_helper`,
`src/engine/general_purpose/decode.rs`; `decode_suffix`,
`src/engine/general_purpose/decode_suffix.rs`), with the error collapsed to `none`:

* every byte must be a symbol of the URL-safe alphabet; `=` is rejected in any position
  (config `NO_PAD` has `DecodePaddingMode::RequireNone`, `mod.rs` line 501: padding in the
  final quad is `InvalidPadding` or `InvalidByte`, in an earlier quad `InvalidByte`);
* a length `≡ 1 (mod 4)` is rejected (`InvalidLength`);
* a final group of 2 or 3 symbols must have zero unused low bits (the config default
  `decode_allow_trailing_bits = false`, `mod.rs` line 341; `InvalidLastSymbol` otherwise);
* otherwise the result is the standard decoding (4 symbols give 3 bytes, a final 2 or 3 give
  1 or 2). -/
def b64Decode : List Std.U8 → Option (List Std.U8)
  | [] => some []
  | c0 :: c1 :: c2 :: c3 :: rest => do
    let v0 ← b64Val c0
    let v1 ← b64Val c1
    let v2 ← b64Val c2
    let v3 ← b64Val c3
    let tail ← b64Decode rest
    some (byte (v0 * 4 + v1 / 16) :: byte (v1 % 16 * 16 + v2 / 4) :: byte (v2 % 4 * 64 + v3) ::
      tail)
  | [c0, c1, c2] => do
    let v0 ← b64Val c0
    let v1 ← b64Val c1
    let v2 ← b64Val c2
    if v2 % 4 = 0 then some [byte (v0 * 4 + v1 / 16), byte (v1 % 16 * 16 + v2 / 4)] else none
  | [c0, c1] => do
    let v0 ← b64Val c0
    let v1 ← b64Val c1
    if v1 % 16 = 0 then some [byte (v0 * 4 + v1 / 16)] else none
  | [_] => none

/-- Decoding never produces more bytes than it reads (so the result fits in a `Vec`). -/
theorem b64Decode_length_le :
    ∀ (s l : List Std.U8), b64Decode s = some l → l.length ≤ s.length
  | [], l, h => by simp [b64Decode] at h; simp [← h]
  | _ :: _ :: _ :: _ :: rest, l, h => by
    simp only [b64Decode, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, _, _, _, _, _, _, tail, ht, hl⟩ := h
    have := b64Decode_length_le rest tail ht
    simp at hl; subst hl; simp; omega
  | [_, _, _], l, h => by
    simp only [b64Decode, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, _, _, _, _, hl⟩ := h
    split at hl <;> simp at hl; subst hl; simp
  | [_, _], l, h => by
    simp only [b64Decode, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, _, _, hl⟩ := h
    split at hl <;> simp at hl; subst hl; simp
  | [_], l, h => by simp [b64Decode] at h

/-! ### Hasher and clock -/

/-- **SipHash-1-3 reference function** (opaque): `sipHash13 k0 k1 msg` is the value of
`finish` of a `SipHasher13` with keys `k0`, `k1` after writing the byte stream `msg`
(`core/src/hash/sip.rs`). Opaque because no statement depends on hash values: the
`HashMap::get` model does not hash (see `std.collections.hash.map.HashMap.get`). -/
opaque sipHash13 : Std.U64 → Std.U64 → List Std.U8 → Std.U64

/-- **Clock reading** (opaque): the value of `chrono::Utc::now().timestamp_millis()` that
`RequestStateCodec::now_ms` returns. A single constant cannot model that two readings differ,
and it makes every function that reads the clock (`now_ms`, `open`, `open_with`) pure. Review
rule: no spec statement mentions the functions `rmcp.model.request_state.RequestStateCodec.now_ms`,
`…RequestStateCodec.open` or `…RequestStateCodec.open_with` (a variable named `now_ms`, such as the
time parameter of E01 `open_authenticated_body`, is not covered; `formal/README.md`, "Trusted
base"). -/
opaque nowMs : Std.I64

end ExtModel

/-! ## HMAC -/

/-- [rmcp::model::request_state_wire::prim::hmac_sha256]:
    Source: 'crates/rmcp/src/model/request_state_wire.rs', lines 253:4-258:5
    Visibility: public

**Model:** `ok (hmacSha256 key msg)`. Succeeds: `Hmac::<Sha256>::new_from_slice`
returns `Ok` for every key length (`hmac-0.13.0/src/block_api.rs` lines 53–69: the key is
hashed or padded to the block size by `get_der_key`, `src/utils.rs` lines 9–32, no error path),
so the `expect` never panics; `update` and `finalize` do not fail within the size convention of
this module (module docstring).
Exception (not modelled): SHA-256 finalisation computes the length of the hashed input in bits
as a `u64` (`sha2-0.11.1/src/block_api.rs` line 66, `8 * (buffer.get_pos() as u64 + bs *
self.block_len)`), which overflows, and panics under `overflow-checks`, when the hashed input
reaches `2^61` bytes. This happens for a **message** of at least `2^61 − 64` bytes (the inner
hash covers the 64-byte key block and the message) and for a **key** of at least `2^61` bytes
(`get_der_key` hashes a key longer than the 64-byte block with `D::digest`). The model does not
represent that panic: both inputs lie outside the size convention (at least `2^61` bytes, more
than the at most `2^57`-byte address space of `x86_64`), like out of memory, which plan
Section 4 does not model. -/
def model.request_state_wire.prim.hmac_sha256 (key : Slice Std.U8) (msg : Slice Std.U8) :
    Result (Std.Array Std.U8 32#usize) :=
  ok (ExtModel.hmacSha256 key.val msg.val)

/-- [rmcp::model::request_state_wire::prim::hmac_sha256_verify]:
    Source: 'crates/rmcp/src/model/request_state_wire.rs', lines 261:4-266:5
    Visibility: public

**Model:** `ok (tag = hmacSha256 key msg)`, compared as byte lists, so a tag of any length
other than 32 is rejected. `Mac::verify_slice` (`digest-0.11.3/src/mac.rs` lines 139–146)
returns `Err` if `tag.len() != OutputSize` (32 for SHA-256) and otherwise compares the computed
tag with `tag` (constant-time `ct_eq`; timing is not modelled); `is_ok()` turns that into the
`bool`. Key setup always succeeds, as for `hmac_sha256`, with the same unmodelled
key- and message-length exception (a key of at least `2^61` bytes or a message of at least
`2^61 − 64` bytes, outside the size convention). -/
def model.request_state_wire.prim.hmac_sha256_verify (key : Slice Std.U8) (msg : Slice Std.U8)
    (tag : Slice Std.U8) : Result Bool :=
  ok (decide (tag.val = (ExtModel.hmacSha256 key.val msg.val).val))

/-! ## Base64 -/

/-- [rmcp::model::request_state_wire::prim::b64_encode_into]:
    Source: 'crates/rmcp/src/model/request_state_wire.rs', lines 269:4-271:5
    Visibility: public

**Model:** appends the symbols `b64 input` (ASCII, one `Char` per byte) to `out`.
`URL_SAFE_NO_PAD.encode_string` (`base64-0.23.1/src/engine/mod.rs` lines 188–201) pushes the
encoded chunks with `String::push_str` (`src/chunked_encoder.rs`, `StringSink`); the
`str::from_utf8(..).unwrap()` there cannot fail on ASCII. The result is subject to the
`String` length limit (`ExtModel.growString`). -/
def model.request_state_wire.prim.b64_encode_into (input : Slice Std.U8) (out : String) :
    Result String :=
  ExtModel.growString
    (out ++ String.ofList ((ExtModel.b64 input.val).map (fun b => Char.ofNat b.val)))

/-- [rmcp::model::request_state_wire::prim::b64_decode]:
    Source: 'crates/rmcp/src/model/request_state_wire.rs', lines 274:4-276:5
    Visibility: public

**Model:** `ok (b64Decode input)`, the decoded bytes as a `Vec` (`URL_SAFE_NO_PAD.decode(input)
.ok()`; `Engine::decode` allocates a buffer of the conservative estimate and never reaches its
`unreachable!`). -/
def model.request_state_wire.prim.b64_decode (input : Slice Std.U8) :
    Result (Option (alloc.vec.Vec Std.U8)) :=
  match h : ExtModel.b64Decode input.val with
  | none => ok none
  | some l => ok (some ⟨l, (ExtModel.b64Decode_length_le _ _ h).trans input.property⟩)

/-! ## Standard library -/

/-- [core::borrow::{impl core::borrow::Borrow<T> for T}::borrow]:
    Source: '/rustc/library/core/src/borrow.rs', lines 214:4-214:26
    Name pattern: [core::borrow::{core::borrow::Borrow<@T, @T>}::borrow]
    Visibility: public

**Model:** the identity (`fn borrow(&self) -> &T { self }`, lines 214–216). -/
@[rust_fun "core::borrow::{core::borrow::Borrow<@T, @T>}::borrow"]
def core.borrow.Borrow.Blanket.borrow {T : Type} (self : T) : Result T :=
  ok self

/-- [core::option::{core::option::Option<T>}::ok_or]:
    Source: '/rustc/library/core/src/option.rs', lines 1334:4-1334:73
    Name pattern: [core::option::{core::option::Option<@T>}::ok_or]
    Visibility: public

**Model:** `Some v ↦ Ok v`, `None ↦ Err err` (lines 1334–1339). -/
@[rust_fun "core::option::{core::option::Option<@T>}::ok_or"]
def core.option.Option.ok_or {T : Type} {E : Type} (self : Option T) (err : E) :
    Result (core.result.Result T E) :=
  match self with
  | some v => ok (core.result.Result.Ok v)
  | none => ok (core.result.Result.Err err)

/-- [core::option::{impl core::default::Default for core::option::Option<T>}::default]:
    Source: '/rustc/library/core/src/option.rs', lines 2313:4-2313:29
    Name pattern: [core::option::{core::default::Default<core::option::Option<@T>>}::default]
    Visibility: public

**Model:** `None` (lines 2313–2315). -/
@[rust_fun
  "core::option::{core::default::Default<core::option::Option<@T>>}::default"]
def core.option.Option.Insts.CoreDefaultDefault.default (T : Type) : Result (Option T) :=
  ok none

/-- [core::result::{core::result::Result<T, E>}::is_err]:
    Source: '/rustc/library/core/src/result.rs', lines 646:4-646:38
    Name pattern: [core::result::{core::result::Result<@T, @E>}::is_err]
    Visibility: public

**Model:** `true` exactly for `Err` (`!self.is_ok()`, lines 646–648). -/
@[rust_fun "core::result::{core::result::Result<@T, @E>}::is_err"]
def core.result.Result.is_err {T : Type} {E : Type} (self : core.result.Result T E) :
    Result Bool :=
  match self with
  | core.result.Result.Ok _ => ok false
  | core.result.Result.Err _ => ok true

/-- [core::result::{core::result::Result<T, E>}::map_err]:
    Source: '/rustc/library/core/src/result.rs', lines 962:4-964:53
    Name pattern: [core::result::{core::result::Result<@T, @E>}::map_err]
    Visibility: public

**Model:** `Ok t ↦ Ok t`; `Err e ↦ Err (op e)`, calling the closure through its `FnOnce`
instance, whose failure propagates (lines 962–970). -/
@[rust_fun "core::result::{core::result::Result<@T, @E>}::map_err"]
def core.result.Result.map_err {T : Type} {E : Type} {F : Type} {O : Type}
    (opsfunctionFnOnceOTupleEFInst : core.ops.function.FnOnce O E F)
    (self : core.result.Result T E) (op : O) : Result (core.result.Result T F) :=
  match self with
  | core.result.Result.Ok t => ok (core.result.Result.Ok t)
  | core.result.Result.Err e => do
    let f ← opsfunctionFnOnceOTupleEFInst.call_once op e
    ok (core.result.Result.Err f)

/-- [core::slice::{impl core::default::Default for &'_0 [T]}::default]:
    Source: '/rustc/library/core/src/slice/mod.rs', lines 5637:4-5637:24
    Name pattern: [core::slice::{core::default::Default<&'0 [@T]>}::default]
    Visibility: public

**Model:** the empty slice (`&[]`, lines 5637–5639). -/
@[rust_fun "core::slice::{core::default::Default<&'0 [@T]>}::default"]
def Shared0Slice.Insts.CoreDefaultDefault.default (T : Type) : Result (Slice T) :=
  ok (Slice.new T)

/-- [core::str::{str}::len]:
    Source: '/rustc/library/core/src/str/mod.rs', lines 153:4-153:36
    Name pattern: [core::str::{str}::len]
    Visibility: public

**Model:** the number of bytes (`self.as_bytes().len()`, lines 153–155), for every `Str`. -/
@[rust_fun "core::str::{str}::len"]
def core.str.Str.len (self : Str) : Result Std.Usize :=
  ok (Slice.len (self : Slice Std.U8))

/-- [core::str::{str}::as_bytes]:
    Source: '/rustc/library/core/src/str/mod.rs', lines 498:4-498:41
    Name pattern: [core::str::{str}::as_bytes]
    Visibility: public

**Model:** the same bytes (a `transmute` of `&str` to `&[u8]`, lines 498–501), for every
`Str`. -/
@[rust_fun "core::str::{str}::as_bytes"]
def core.str.Str.as_bytes (self : Str) : Result (Slice Std.U8) :=
  ok self

/-- The value of the first entry of `entries` whose key, borrowed as `Q`, is equal to `k`
(`k == key.borrow()`, through the `Borrow` and `Eq` instances; their failures propagate). -/
def ExtModel.HashMap.find {K V Q : Type} (coreborrowBorrowInst : core.borrow.Borrow K Q)
    (corecmpEqInst : core.cmp.Eq Q) (k : Q) : List (K × V) → Result (Option V)
  | [] => ok none
  | (key, v) :: rest => do
    let kb ← coreborrowBorrowInst.borrow key
    let b ← corecmpEqInst.partialEqInst.eq k kb
    if b then ok (some v) else ExtModel.HashMap.find coreborrowBorrowInst corecmpEqInst k rest

/-- [std::collections::hash::map::{std::collections::hash::map::HashMap<K, V, S, A>}::get]:
    Source: '/rustc/library/std/src/collections/hash/map.rs', lines 1035:4-1038:21
    Name pattern: [std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, @S, @A>}::get]
    Visibility: public

**Model:** lookup by key equality: the value of the first entry whose key `key` satisfies
`k == key.borrow()` (`ExtModel.HashMap.find`). The Rust function is `self.base.get(k)`
(lines 1035–1041), i.e. hashbrown 0.17.1 `HashMap::get` (`src/map.rs`): `None` on an empty
table, otherwise it hashes `k` with `make_hash` and returns the entry for which
`Equivalent::equivalent` (`k == key.borrow()`) holds among the entries with a matching hash.

Why hashing is not modelled: for a `Hash`/`Eq` pair that agree (`a == b → hash a = hash b`,
required by the `HashMap` documentation, lines 37–47, and for the borrowed form `Q`, lines
1019–1021), the probe finds the entry with an
equal key whatever the hash values are, and a map has at most one such entry. For the only
instance in the translation, `K = Q = String`, equality is byte equality and `Hash` writes the
bytes, so they agree; hashing a `String` never panics, and `String` equality does not fail.
The model is therefore faithful for `Hash`/`Eq` instances that agree and do not fail; only
`K = Q = String` occurs. Pairwise distinct keys are needed only to identify *which* value is
returned: `find` returns `some` exactly when an entry with an equal key exists, with or
without duplicates (see `std.collections.hash.map.HashMap`). -/
@[rust_fun
  "std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, @S, @A>}::get"]
def std.collections.hash.map.HashMap.get
    {K : Type} {V : Type} {S : Type} {A : Type} {Q : Type} {Clause2_Hasher : Type}
    (_corecmpEqInst : core.cmp.Eq K) (_corehashHashInst : core.hash.Hash K)
    (_corehashBuildHasherInst : core.hash.BuildHasher S Clause2_Hasher)
    (coreborrowBorrowInst : core.borrow.Borrow K Q) (_corehashHashInst1 : core.hash.Hash Q)
    (corecmpEqInst1 : core.cmp.Eq Q)
    (self : std.collections.hash.map.HashMap K V S A) (k : Q) : Result (Option V) :=
  ExtModel.HashMap.find coreborrowBorrowInst corecmpEqInst1 k self.entries

/-- [std::collections::hash::map::{impl core::clone::Clone for std::collections::hash::map::HashMap<K, V, S, A>}::clone]:
    Source: '/rustc/library/std/src/collections/hash/map.rs', lines 1438:4-1438:27
    Name pattern: [std::collections::hash::map::{core::clone::Clone<std::collections::hash::map::HashMap<@K, @V, @S, @A>>}::clone]
    Visibility: public

**Model:** clones the hash builder, the allocator and every key and value
(`Self { base: self.base.clone() }`, lines 1438–1440; hashbrown 0.17.1 `src/map.rs`
`impl Clone for HashMap`: `hash_builder.clone()`, `table.clone()`). -/
@[rust_fun
  "std::collections::hash::map::{core::clone::Clone<std::collections::hash::map::HashMap<@K, @V, @S, @A>>}::clone"]
def std.collections.hash.map.HashMap.Insts.CoreCloneClone.clone
    {K : Type} {V : Type} {S : Type} {A : Type} (corecloneCloneInst : core.clone.Clone K)
    (corecloneCloneInst1 : core.clone.Clone V) (corecloneCloneInst2 : core.clone.Clone S)
    (corecloneCloneInst3 : core.clone.Clone A)
    (self : std.collections.hash.map.HashMap K V S A) :
    Result (std.collections.hash.map.HashMap K V S A) := do
  let hash_builder ← corecloneCloneInst2.clone self.hash_builder
  let alloc ← corecloneCloneInst3.clone self.alloc
  let entries ← self.entries.mapM (fun (e : K × V) => do
    let k ← corecloneCloneInst.clone e.1
    let v ← corecloneCloneInst1.clone e.2
    ok (k, v))
  ok { hash_builder, alloc, entries }

/-- [std::hash::random::{impl core::clone::Clone for std::hash::random::RandomState}::clone]:
    Source: '/rustc/library/std/src/hash/random.rs', lines 34:9-34:14
    Name pattern: [std::hash::random::{core::clone::Clone<std::hash::random::RandomState>}::clone]
    Visibility: public

**Model:** the same value (derived `Clone` of two `u64` fields). -/
@[rust_fun
  "std::hash::random::{core::clone::Clone<std::hash::random::RandomState>}::clone"]
def std.hash.random.RandomState.Insts.CoreCloneClone.clone
    (self : std.hash.random.RandomState) : Result std.hash.random.RandomState :=
  ok self

/-- [std::hash::random::{impl core::hash::Hasher for std::hash::random::DefaultHasher}::finish]:
    Source: '/rustc/library/std/src/hash/random.rs', lines 140:4-140:27
    Name pattern: [std::hash::random::{core::hash::Hasher<std::hash::random::DefaultHasher>}::finish]
    Visibility: public

**Model:** `ok (sipHash13 k0 k1 written)` (`self.0.finish()`, lines 140–142; SipHash-1-3 of
the keys and the byte stream). -/
@[rust_fun
  "std::hash::random::{core::hash::Hasher<std::hash::random::DefaultHasher>}::finish"]
def std.hash.random.DefaultHasher.Insts.CoreHashHasher.finish
    (self : std.hash.random.DefaultHasher) : Result Std.U64 :=
  ok (ExtModel.sipHash13 self.k0 self.k1 self.written)

/-- [std::hash::random::{impl core::hash::Hasher for std::hash::random::DefaultHasher}::write]:
    Source: '/rustc/library/std/src/hash/random.rs', lines 130:4-130:35
    Name pattern: [std::hash::random::{core::hash::Hasher<std::hash::random::DefaultHasher>}::write]
    Visibility: public

**Model:** appends `msg` to the byte stream (`self.0.write(msg)`, lines 130–132). -/
@[rust_fun
  "std::hash::random::{core::hash::Hasher<std::hash::random::DefaultHasher>}::write"]
def std.hash.random.DefaultHasher.Insts.CoreHashHasher.write
    (self : std.hash.random.DefaultHasher) (msg : Slice Std.U8) :
    Result std.hash.random.DefaultHasher :=
  ok { self with written := self.written ++ msg.val }

/-- [std::hash::random::{impl core::hash::BuildHasher<std::hash::random::DefaultHasher> for std::hash::random::RandomState}::build_hasher]:
    Source: '/rustc/library/std/src/hash/random.rs', lines 83:4-83:43
    Name pattern: [std::hash::random::{core::hash::BuildHasher<std::hash::random::RandomState, std::hash::random::DefaultHasher>}::build_hasher]
    Visibility: public

**Model:** a hasher with the map's keys and an empty byte stream
(`DefaultHasher(SipHasher13::new_with_keys(self.k0, self.k1))`, lines 83–85). -/
@[rust_fun
  "std::hash::random::{core::hash::BuildHasher<std::hash::random::RandomState, std::hash::random::DefaultHasher>}::build_hasher"]
def std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher.build_hasher
    (self : std.hash.random.RandomState) : Result std.hash.random.DefaultHasher :=
  ok { k0 := self.k0, k1 := self.k1, written := [] }

/-- [alloc::string::{impl core::cmp::PartialEq<alloc::string::String> for alloc::string::String}::eq]:
    Source: '/rustc/library/alloc/src/string.rs', lines 350:9-350:18
    Name pattern: [alloc::string::{core::cmp::PartialEq<alloc::string::String, alloc::string::String>}::eq]
    Visibility: public

**Model:** equality (derived `PartialEq` of `String { vec: Vec<u8> }`, line 350: byte
equality, which is equality of the strings). -/
@[rust_fun
  "alloc::string::{core::cmp::PartialEq<alloc::string::String, alloc::string::String>}::eq"]
def alloc.string.String.Insts.CoreCmpPartialEqString.eq (self : String) (other : String) :
    Result Bool :=
  ok (decide (self = other))

/-- [alloc::string::{impl core::cmp::Eq for alloc::string::String}::assert_fields_are_eq]:
    Source: '/rustc/library/alloc/src/string.rs', lines 350:32-350:34
    Name pattern: [alloc::string::{core::cmp::Eq<alloc::string::String>}::assert_fields_are_eq]
    Visibility: public

**Model:** `ok ()` (a derived marker method with an empty body). -/
@[rust_fun
  "alloc::string::{core::cmp::Eq<alloc::string::String>}::assert_fields_are_eq"]
def alloc.string.String.Insts.CoreCmpEq.assert_fields_are_eq (_self : String) : Result Unit :=
  ok ()

/-- [alloc::string::{alloc::string::String}::with_capacity]:
    Source: '/rustc/library/alloc/src/string.rs', lines 493:4-493:51
    Name pattern: [alloc::string::{alloc::string::String}::with_capacity]
    Visibility: public

**Model:** the empty string; `fail panic` if `capacity > isize::MAX`
(`String { vec: Vec::with_capacity(capacity) }`, lines 493–495; `RawVec::try_allocate_in`
rejects the layout and `handle_error` panics with "capacity overflow"). Capacity is not part of
the value model. -/
@[rust_fun "alloc::string::{alloc::string::String}::with_capacity"]
def alloc.string.String.with_capacity (capacity : Std.Usize) : Result String :=
  if capacity.val ≤ ExtModel.maxStringBytes then ok "" else fail panic

/-- [alloc::string::{alloc::string::String}::from_utf8]:
    Source: '/rustc/library/alloc/src/string.rs', lines 569:4-569:67
    Name pattern: [alloc::string::{alloc::string::String}::from_utf8]
    Visibility: public

**Model:** `Ok s` if the bytes are the UTF-8 encoding of a string `s`, otherwise
`Err { bytes := vec }` (lines 569–574: `str::from_utf8(&vec)` decides; see
`ExtModel.strOfBytes?`). -/
@[rust_fun "alloc::string::{alloc::string::String}::from_utf8"]
def alloc.string.String.from_utf8 (vec : alloc.vec.Vec Std.U8) :
    Result (core.result.Result String alloc.string.FromUtf8Error) :=
  match ExtModel.strOfBytes? vec.val with
  | some s => ok (core.result.Result.Ok s)
  | none => ok (core.result.Result.Err { bytes := vec })

/-- [alloc::string::{alloc::string::String}::push_str]:
    Source: '/rustc/library/alloc/src/string.rs', lines 1110:4-1110:44
    Name pattern: [alloc::string::{alloc::string::String}::push_str]
    Visibility: public

**Model:** appends the string whose UTF-8 bytes are `string`
(`self.vec.extend_from_slice(string.as_bytes())`, lines 1110–1112), subject to the `String`
length limit (`ExtModel.growString`). `fail undef` if `string` is not UTF-8, which no Rust
`&str` is. -/
@[rust_fun "alloc::string::{alloc::string::String}::push_str"]
def alloc.string.String.push_str (self : String) (string : Str) : Result String :=
  match ExtModel.strOfBytes? string.val with
  | some t => ExtModel.growString (self ++ t)
  | none => fail undef

/-- [alloc::string::{alloc::string::String}::push]:
    Source: '/rustc/library/alloc/src/string.rs', lines 1425:4-1425:36
    Name pattern: [alloc::string::{alloc::string::String}::push]
    Visibility: public

**Model:** appends the character (its UTF-8 encoding, lines 1425–1435), subject to the
`String` length limit (`ExtModel.growString`). A Lean `Char` is a Unicode scalar value, as a
Rust `char` is. -/
@[rust_fun "alloc::string::{alloc::string::String}::push"]
def alloc.string.String.push (self : String) (ch : Char) : Result String :=
  ExtModel.growString (self.push ch)

/-- [alloc::string::{alloc::string::String}::as_bytes]:
    Source: '/rustc/library/alloc/src/string.rs', lines 1454:4-1454:41
    Name pattern: [alloc::string::{alloc::string::String}::as_bytes]
    Visibility: public

**Model:** the UTF-8 bytes (`self.vec.as_slice()`, lines 1454–1456). A Rust `String` has at
most `isize::MAX` bytes, so the bytes always fit in a slice; a Lean `String` longer than
`Usize.max` bytes, which no Rust `String` is, gives `fail maximumSizeExceeded`. -/
@[rust_fun "alloc::string::{alloc::string::String}::as_bytes"]
def alloc.string.String.as_bytes (self : String) : Result (Slice Std.U8) :=
  if h : (ExtModel.utf8 self).length ≤ Usize.max then ok ⟨ExtModel.utf8 self, h⟩
  else fail maximumSizeExceeded

/-- [alloc::string::{impl core::clone::Clone for alloc::string::String}::clone]:
    Source: '/rustc/library/alloc/src/string.rs', lines 2364:4-2364:27
    Name pattern: [alloc::string::{core::clone::Clone<alloc::string::String>}::clone]
    Visibility: public

**Model:** the same string (`String { vec: self.vec.clone() }`, lines 2364–2366). -/
@[rust_fun "alloc::string::{core::clone::Clone<alloc::string::String>}::clone"]
def alloc.string.String.Insts.CoreCloneClone.clone (self : String) : Result String :=
  ok self

/-- [alloc::string::{impl core::hash::Hash for alloc::string::String}::hash]:
    Source: '/rustc/library/alloc/src/string.rs', lines 2740:4-2740:51
    Name pattern: [alloc::string::{core::hash::Hash<alloc::string::String>}::hash]
    Visibility: public

**Model:** writes the UTF-8 bytes, then the byte `0xff`, through the hasher instance
(`(**self).hash(hasher)`, lines 2740–2742; `impl Hash for str` calls `state.write_str(self)`,
`core/src/hash/mod.rs` lines 862–866, whose default is `self.write(s.as_bytes());
self.write_u8(0xff)`, lines 550–553). For `DefaultHasher` the same bytes are written:
`DefaultHasher::write_str` forwards to `SipHasher13::write_str` (`std/src/hash/random.rs`
lines 135–137, `core/src/hash/sip.rs` lines 237–239), which reaches the override
of `Hasher<S>::write_str`, `core/src/hash/sip.rs` lines 303–308: `self.write(s.as_bytes());
self.write_u8(0xFF)`; `write_u8` is not overridden there (the note at line 248), so it is the
default `self.write(&[i])` (`core/src/hash/mod.rs` lines 362–364). The `Hasher` instance of
the Aeneas library has only `write` and `finish`, so `write_u8(0xff)` is the `write` of the
one-byte slice. -/
@[rust_fun "alloc::string::{core::hash::Hash<alloc::string::String>}::hash"]
def alloc.string.String.Insts.CoreHashHash.hash {H : Type}
    (corehashHasherInst : core.hash.Hasher H) (self : String) (state : H) : Result H := do
  let bytes ← alloc.string.String.as_bytes self
  let state ← corehashHasherInst.write state bytes
  corehashHasherInst.write state ⟨[ExtModel.byte 255], by scalar_tac⟩

/-- [alloc::vec::{alloc::vec::Vec<T>}::is_empty]:
    Source: '/rustc/library/alloc/src/vec/mod.rs', lines 3085:4-3085:40
    Name pattern: [alloc::vec::{alloc::vec::Vec<@T>}::is_empty]
    Visibility: public

**Model:** `len == 0` (lines 3085–3087). -/
@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::is_empty"]
def alloc.vec.Vec.is_empty {T : Type} (_A : Type) (self : alloc.vec.Vec T) : Result Bool :=
  ok (decide (self.val.length = 0))

/-- [zeroize::{impl zeroize::Zeroize for Z}::zeroize]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/zeroize-1.9.2/src/lib.rs', lines 282:4-282:25
    Name pattern: [zeroize::{zeroize::Zeroize<@Z>}::zeroize]
    Visibility: public

**Model:** `Z::default()` (`volatile_write(self, Z::default())`, lines 282–284; the volatile
write is not modelled, only its value). -/
@[rust_fun "zeroize::{zeroize::Zeroize<@Z>}::zeroize"]
def zeroize.Zeroize.Blanket.zeroize {Z : Type}
    (DefaultIsZeroesInst : zeroize.DefaultIsZeroes Z) (_self : Z) : Result Z :=
  DefaultIsZeroesInst.coredefaultDefaultInst.default

/-- [zeroize::{impl zeroize::Zeroize for alloc::vec::Vec<Z>}::zeroize]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/zeroize-1.9.2/src/lib.rs', lines 505:4-505:25
    Name pattern: [zeroize::{zeroize::Zeroize<alloc::vec::Vec<@Z>>}::zeroize]
    Visibility: public

**Model:** zeroizes every element through the element instance (failures propagate) and then
clears the vector, so the result is empty (lines 505–516: spare capacity, which the value
model does not have, then `iter_mut().zeroize()`, then `clear()`). -/
@[rust_fun "zeroize::{zeroize::Zeroize<alloc::vec::Vec<@Z>>}::zeroize"]
def alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize {Z : Type} (ZeroizeInst : zeroize.Zeroize Z)
    (self : alloc.vec.Vec Z) : Result (alloc.vec.Vec Z) := do
  let _ ← self.val.mapM ZeroizeInst.zeroize
  ok (alloc.vec.Vec.new Z)

/-- [zeroize::{zeroize::Zeroizing<Z>}::new]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/zeroize-1.9.2/src/lib.rs', lines 599:4-599:32
    Name pattern: [zeroize::{zeroize::Zeroizing<@Z>}::new]
    Visibility: public

**Model:** wraps the value (`Self(value)`, lines 599–601). -/
@[rust_fun "zeroize::{zeroize::Zeroizing<@Z>}::new"]
def zeroize.Zeroizing.new {Z : Type} (_ZeroizeInst : zeroize.Zeroize Z) (value : Z) :
    Result (zeroize.Zeroizing Z) :=
  ok { inner := value }

/-- [zeroize::{impl core::clone::Clone for zeroize::Zeroizing<Z>}::clone]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/zeroize-1.9.2/src/lib.rs', lines 606:4-606:27
    Name pattern: [zeroize::{core::clone::Clone<zeroize::Zeroizing<@Z>>}::clone]
    Visibility: public

**Model:** wraps a clone of the value (`Self(self.0.clone())`, lines 606–608). -/
@[rust_fun "zeroize::{core::clone::Clone<zeroize::Zeroizing<@Z>>}::clone"]
def zeroize.Zeroizing.Insts.CoreCloneClone.clone {Z : Type} (_ZeroizeInst : zeroize.Zeroize Z)
    (corecloneCloneInst : core.clone.Clone Z) (self : zeroize.Zeroizing Z) :
    Result (zeroize.Zeroizing Z) := do
  let v ← corecloneCloneInst.clone self.inner
  ok { inner := v }

/-- [zeroize::{impl core::ops::deref::Deref<Z> for zeroize::Zeroizing<Z>}::deref]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/zeroize-1.9.2/src/lib.rs', lines 634:4-634:25
    Name pattern: [zeroize::{core::ops::deref::Deref<zeroize::Zeroizing<@Z>, @Z>}::deref]
    Visibility: public

**Model:** the wrapped value (`&self.0`, lines 634–636). -/
@[rust_fun
  "zeroize::{core::ops::deref::Deref<zeroize::Zeroizing<@Z>, @Z>}::deref"]
def zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref {Z : Type}
    (_ZeroizeInst : zeroize.Zeroize Z) (self : zeroize.Zeroizing Z) : Result Z :=
  ok self.inner

/-! ## Clock -/

/-- [rmcp::model::request_state::{rmcp::model::request_state::RequestStateCodec}::now_ms]:
    Source: 'crates/rmcp/src/model/request_state.rs', lines 729:4-731:5

**Model:** `ok nowMs`, an opaque value (`chrono::Utc::now().timestamp_millis()`).
Environmental assumption (stated exception, not modelled): `Utc::now` panics if the system
clock is before 1970 or outside chrono's range (`chrono-0.4.45/src/offset/utc.rs` lines 96–98:
`duration_since(UNIX_EPOCH).expect("system time before Unix epoch")` and
`DateTime::from_timestamp(..).unwrap()`); the model assumes a clock within that range. Called
by the translated wrappers `open` and `open_with` (not targets); `seal_with`, which also reads
the clock, is excluded from the translation. Because `nowMs` is one constant, those wrappers
are pure in the model; no spec statement may mention the functions
`rmcp.model.request_state.RequestStateCodec.now_ms`, `…RequestStateCodec.open` or
`…RequestStateCodec.open_with` (a variable named `now_ms`, such as the time parameter of E01
`open_authenticated_body`, is not covered). -/
def model.request_state.RequestStateCodec.now_ms : Result Std.I64 :=
  ok ExtModel.nowMs
