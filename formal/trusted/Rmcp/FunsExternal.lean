/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Aeneas
public import Rmcp.Types

/-!
External functions of the `rmcp` translation (`Rmcp.Funs` imports this module).

Started at plan step S04a from the template that Aeneas generated
(`formal/translation/Rmcp/FunsExternal_Template.lean`) for the translation of commit
`f8fb6a7` with the Charon settings of S04a part 2 (derived `Debug` impls excluded), Aeneas
`nightly-2026.08.20-5d08da4`. Since the D2 fallback (2026-11-23) the translated source is the
patched copy (patch 01 on origin/main 7caec76), which gives the same translation; the `Source:`
line numbers below refer to it. Plan steps S08 (HMAC and Base64 `prim` functions) and S09
(standard library, `HashMap`, clock) replaced every placeholder of the template by a
definition with the generated name and signature, keeping the template's `@[rust_fun]` attribute
where it has one (the external functions of other crates; the five opaque `rmcp` functions, the
four `prim` functions and `RequestStateCodec::now_ms`, have none in the template). **This module
declares no axiom.** The two things the models cannot compute are `opaque` constants, which
add no axiom: the HMAC-SHA256 reference function `ExtModel.hmacSha256` and the clock reading
`ExtModel.nowMs` (and, for the unused hasher, `ExtModel.sipHash13`). The 26 external functions
that the Phase 2 translation (plan step S21) added were temporary `opaque` placeholders; plan
steps S26/S27 replaced them by definitions (sections "Phase 2", plan Section 18): string and
`Arc` equality and deref; `Option::or_else`, `Option` equality, `Result::ok`, `slice::first`,
`slice::strip_suffix`, slice-array equality, `SlicePattern::as_slice` of arrays and
`RangeInclusive::contains`, each the `core` body transcribed; `str::parse` and
`i64::from_str` (Rust's radix-10 grammar and error kinds); and the `Ipv4Addr`/`Ipv6Addr`
functions transcribed from `core/src/net/ip_addr.rs`. None of them needs an `opaque` constant.
The conventions below apply to all models.

Ordering note (S21): the generated external `core.result.Result.ok` shadows Aeneas' `ok` for
every declaration after it in the namespace `core.result.Result` (and for proofs that open it), so
such code must write `Aeneas.Std.Result.ok`; the models above it (`is_err`, `map_err`) are
unaffected.

Each definition returns `ok` exactly where the Rust function returns and `fail` where it
panics, with the exceptions stated in its docstring. Two conventions apply throughout:

* **Memory.** Allocation failure (out of memory) is not modelled (plan Section 4: unlimited
  memory is not established). A `String` that would grow beyond `isize::MAX` bytes is a
  deterministic Rust panic ("capacity overflow": `RawVec::grow_amortized`, lines 516–547 of
  `alloc/src/raw_vec/mod.rs`, through `finish_grow`, lines 557–580, and
  `RawVec::try_allocate_in`, lines 458–496, compute the layout with `layout_array`, lines
  929–935, which returns `CapacityOverflow` for a layout larger than `isize::MAX`; `handle_error`,
  lines 920–925, turns it into the panic) and is modelled as `fail panic`
  (`ExtModel.growString`). A panic that depends on the capacity history (amortized doubling
  past `isize::MAX` while the length still fits) is not modelled, so `ok` from a `String`
  model means "returns, or aborts or panics for memory reasons".
* **`Str`.** The Aeneas `Str` is `Slice U8` and admits byte sequences that are not UTF-8,
  while a Rust `&str` is always UTF-8. Functions that only read the bytes (`str::len`,
  `str::as_bytes`, `str` equality, `i64::from_str`) are modelled on all of `Str`;
  `String::push_str`, which builds a `String` from the bytes, returns `fail undef` outside the
  Rust domain (a non-UTF-8 `&str` is undefined behaviour in Rust).
* **Size convention.** A `Slice` or `String` of the model may be up to `Usize.max` bytes long,
  more than any machine can hold. The models make no claim about inputs of at least `2^61`
  bytes (2 EiB): such an input cannot exist in a running process on the translated target
  `x86_64-unknown-linux-gnu`, whose virtual address space is at most `2^57` bytes (5-level
  paging), and plan Section 4 does not model memory limits. The only behaviour this convention
  hides is the SHA-256 length overflow of the HMAC functions (section HMAC).

Source paths: `/rustc/library/…` is the `rust-src` of the pinned toolchain `nightly-2026-09-17`
(Aeneas upgrade, 2026-11-24: every cited `rust-src` range was compared with `nightly-2026-06-01`
and renumbered. Behaviour is unchanged except for `core.ops.range.RangeInclusive.contains`
(`RangeBounds::end_bound` of an exhausted `RangeInclusive` is now `Excluded(start)`; changed in
the Aeneas upgrade, human decision 2026-11-24; model reviewed 2026-11-24, re-signed 2026-11-24). Textual changes without a
change of behaviour: `RawVec::finish_grow` uses `map_err` instead of a `match`,
`SlicePartialEq::equal_same_length` a `for` instead of a `while` loop, `i64::from_ascii_radix`
is now `from_ascii_bytes_radix_impl` (same body, renamed panic helper), and comments);
`/cargo/registry/…` is the crate at the version in the path. `scripts/aeneas-translate.sh`
pins every crate cited here (`PINNED_DEPS`): `hmac 0.13.0`, `sha2 0.11.1`, `base64 0.23.1`,
`digest 0.11.3`, `zeroize 1.9.2`, `chrono 0.4.45` and `serde_json 1.0.154` (plan Section 4). The
Rust tests that check the models are listed in `formal/trusted/evidence/README.md`.
-/
@[expose] public section
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
  fun _ _ => Std.Array.from (List.replicate 32 (byte 0)) (by simp)

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
base"). Exception (human decision 2026-11-24; `formal/README.md`, "Trusted base"): only the
spec theorems of `open` and `open_with` and their restatements may name these two functions and
`nowMs`, and only with postcondition `resultBytes result = openAt … nowMs.val`; no other statement
names `nowMs`, no statement has a premise or conclusion about its value or involves two clock
readings, and `now_ms` itself stays unmentioned. -/
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
  | some l => ok (some (alloc.vec.Vec.from l ((ExtModel.b64Decode_length_le _ _ h).trans input.property)))

/-! ## Standard library -/

/-- [core::option::{impl core::default::Default for core::option::Option<T>}::default]:
    Source: '/rustc/library/core/src/option.rs', lines 2314:4-2314:29
    Name pattern: [core::option::{core::default::Default<core::option::Option<@T>>}::default]
    Visibility: public

**Model:** `None` (lines 2314–2316). -/
@[rust_fun
  "core::option::{core::default::Default<core::option::Option<@T>>}::default"]
def core.option.Option.Insts.CoreDefaultDefault.default (T : Type) : Result (Option T) :=
  ok none

/-- [core::result::{core::result::Result<T, E>}::is_err]:
    Source: '/rustc/library/core/src/result.rs', lines 647:4-647:38
    Name pattern: [core::result::{core::result::Result<@T, @E>}::is_err]
    Visibility: public

**Model:** `true` exactly for `Err` (`!self.is_ok()`, lines 647–649). -/
@[rust_fun "core::result::{core::result::Result<@T, @E>}::is_err"]
def core.result.Result.is_err {T : Type} {E : Type} (self : core.result.Result T E) :
    Result Bool :=
  match self with
  | core.result.Result.Ok _ => ok false
  | core.result.Result.Err _ => ok true

/-- [core::slice::{impl core::default::Default for &'_0 [T]}::default]:
    Source: '/rustc/library/core/src/slice/mod.rs', lines 5655:4-5655:24
    Name pattern: [core::slice::{core::default::Default<&'0 [@T]>}::default]
    Visibility: public

**Model:** the empty slice (`&[]`, lines 5655–5657). -/
@[rust_fun "core::slice::{core::default::Default<&'0 [@T]>}::default"]
def Shared0Slice.Insts.CoreDefaultDefault.default (T : Type) : Result (Slice T) :=
  ok (Slice.new T)

/-- [core::str::{str}::len]:
    Source: '/rustc/library/core/src/str/mod.rs', lines 155:4-155:36
    Name pattern: [core::str::{str}::len]
    Visibility: public

**Model:** the number of bytes (`self.as_bytes().len()`, lines 155–157), for every `Str`. -/
@[rust_fun "core::str::{str}::len"]
def core.str.Str.len (self : Str) : Result Std.Usize :=
  ok (Slice.len (self : Slice Std.U8))

/-- [core::str::{str}::as_bytes]:
    Source: '/rustc/library/core/src/str/mod.rs', lines 514:4-514:41
    Name pattern: [core::str::{str}::as_bytes]
    Visibility: public

**Model:** the same bytes (a `transmute` of `&str` to `&[u8]`, lines 514–517), for every
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
    Source: '/rustc/library/std/src/collections/hash/map.rs', lines 1034:4-1037:21
    Name pattern: [std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, @S, @A>}::get]
    Visibility: public

**Model:** lookup by key equality: the value of the first entry whose key `key` satisfies
`k == key.borrow()` (`ExtModel.HashMap.find`). The Rust function is `self.base.get(k)`
(lines 1034–1040), i.e. hashbrown 0.17.1 `HashMap::get` (`src/map.rs`): `None` on an empty
table, otherwise it hashes `k` with `make_hash` and returns the entry for which
`Equivalent::equivalent` (`k == key.borrow()`) holds among the entries with a matching hash.

Why hashing is not modelled: for a `Hash`/`Eq` pair that agree (`a == b → hash a = hash b`,
required by the `HashMap` documentation, lines 37–47, and for the borrowed form `Q`, lines
1018–1020), the probe finds the entry with an
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
    Source: '/rustc/library/std/src/collections/hash/map.rs', lines 1437:4-1437:27
    Name pattern: [std::collections::hash::map::{core::clone::Clone<std::collections::hash::map::HashMap<@K, @V, @S, @A>>}::clone]
    Visibility: public

**Model:** clones the hash builder, the allocator and every key and value
(`Self { base: self.base.clone() }`, lines 1437–1439; hashbrown 0.17.1 `src/map.rs`
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
    Source: '/rustc/library/alloc/src/string.rs', lines 1122:4-1122:44
    Name pattern: [alloc::string::{alloc::string::String}::push_str]
    Visibility: public

**Model:** appends the string whose UTF-8 bytes are `string`
(`self.vec.extend_from_slice(string.as_bytes())`, lines 1122–1124), subject to the `String`
length limit (`ExtModel.growString`). `fail undef` if `string` is not UTF-8, which no Rust
`&str` is. -/
@[rust_fun "alloc::string::{alloc::string::String}::push_str"]
def alloc.string.String.push_str (self : String) (string : Str) : Result String :=
  match ExtModel.strOfBytes? string.val with
  | some t => ExtModel.growString (self ++ t)
  | none => fail undef

/-- [alloc::string::{alloc::string::String}::push]:
    Source: '/rustc/library/alloc/src/string.rs', lines 1451:4-1451:36
    Name pattern: [alloc::string::{alloc::string::String}::push]
    Visibility: public

**Model:** appends the character (its UTF-8 encoding, lines 1451–1461), subject to the
`String` length limit (`ExtModel.growString`). A Lean `Char` is a Unicode scalar value, as a
Rust `char` is. -/
@[rust_fun "alloc::string::{alloc::string::String}::push"]
def alloc.string.String.push (self : String) (ch : Char) : Result String :=
  ExtModel.growString (self.push ch)

/-- [alloc::string::{alloc::string::String}::as_bytes]:
    Source: '/rustc/library/alloc/src/string.rs', lines 1480:4-1480:41
    Name pattern: [alloc::string::{alloc::string::String}::as_bytes]
    Visibility: public

**Model:** the UTF-8 bytes (`self.vec.as_slice()`, lines 1480–1482). A Rust `String` has at
most `isize::MAX` bytes, so the bytes always fit in a slice; a Lean `String` longer than
`Usize.max` bytes, which no Rust `String` is, gives `fail maximumSizeExceeded`. -/
@[rust_fun "alloc::string::{alloc::string::String}::as_bytes"]
def alloc.string.String.as_bytes (self : String) : Result (Slice Std.U8) :=
  if h : (ExtModel.utf8 self).length ≤ Usize.max then ok (Std.Slice.from (ExtModel.utf8 self) h)
  else fail maximumSizeExceeded

/-- [alloc::string::{impl core::clone::Clone for alloc::string::String}::clone]:
    Source: '/rustc/library/alloc/src/string.rs', lines 2425:4-2425:27
    Name pattern: [alloc::string::{core::clone::Clone<alloc::string::String>}::clone]
    Visibility: public

**Model:** the same string (`String { vec: self.vec.clone() }`, lines 2425–2427). -/
@[rust_fun "alloc::string::{core::clone::Clone<alloc::string::String>}::clone"]
def alloc.string.String.Insts.CoreCloneClone.clone (self : String) : Result String :=
  ok self

/-- [alloc::string::{impl core::hash::Hash for alloc::string::String}::hash]:
    Source: '/rustc/library/alloc/src/string.rs', lines 2801:4-2801:51
    Name pattern: [alloc::string::{core::hash::Hash<alloc::string::String>}::hash]
    Visibility: public

**Model:** writes the UTF-8 bytes, then the byte `0xff`, through the hasher instance
(`(**self).hash(hasher)`, lines 2801–2803; `impl Hash for str` calls `state.write_str(self)`,
`core/src/hash/mod.rs` lines 863–867, whose default is `self.write(s.as_bytes());
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
  corehashHasherInst.write state (Std.Slice.from [ExtModel.byte 255] (by scalar_tac))

set_option linter.dupNamespace false in
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
`open_authenticated_body`, is not covered), except as stated at `ExtModel.nowMs` (human decision
2026-11-24). -/
def model.request_state.RequestStateCodec.now_ms : Result Std.I64 :=
  ok ExtModel.nowMs

/-! ## Phase 2: strings and `Arc`

Plan steps S26/S27 replaced the 26 placeholders of plan step S21 by the models of this and the
following sections (plan Section 18). -/

/-- [core::str::traits::{impl core::cmp::PartialEq<str> for str}::eq]:
    Source: '/rustc/library/core/src/str/traits.rs', lines 29:4-29:37
    Name pattern: [core::str::traits::{core::cmp::PartialEq<str, str>}::eq]
    Visibility: public

**Model:** byte-list equality (`self.as_bytes() == other.as_bytes()`, lines 29–31; slice
equality of `u8`: equal lengths and equal bytes, `core/src/slice/cmp.rs` lines 14–29), for every
`Str`. -/
@[rust_fun "core::str::traits::{core::cmp::PartialEq<str, str>}::eq"]
def Str.Insts.CoreCmpPartialEqStr.eq (self : Str) (other : Str) : Result Bool :=
  ok (decide (self.val = other.val))

/-- [alloc::string::{impl core::ops::deref::Deref<str> for alloc::string::String}::deref]:
    Source: '/rustc/library/alloc/src/string.rs', lines 2896:4-2896:27
    Name pattern: [alloc::string::{core::ops::deref::Deref<alloc::string::String, str>}::deref]
    Visibility: public

**Model:** the UTF-8 bytes of the string, the identity on bytes (`self.as_str()`, lines
2835–2837; `String::as_str` is `str::from_utf8_unchecked(self.vec.as_slice())`), defined as the
model of `String::as_bytes`, which returns the same bytes: `fail maximumSizeExceeded` only for a
Lean `String` longer than `Usize.max` bytes, which no Rust `String` is. -/
@[rust_fun
  "alloc::string::{core::ops::deref::Deref<alloc::string::String, str>}::deref"]
def alloc.string.String.Insts.CoreOpsDerefDerefStr.deref (self : String) : Result Str :=
  alloc.string.String.as_bytes self

/-- [alloc::sync::{impl core::ops::deref::Deref<T> for alloc::sync::Arc<T>}::deref]:
    Source: '/rustc/library/alloc/src/sync.rs', lines 2570:4-2570:25
    Name pattern: [alloc::sync::{core::ops::deref::Deref<alloc::sync::Arc<@T>, @T>}::deref]
    Visibility: public

**Model:** the shared value, a projection (`&self.inner().data`, lines 2570–2572). The
allocator parameter `A` is not used. -/
@[rust_fun
  "alloc::sync::{core::ops::deref::Deref<alloc::sync::Arc<@T>, @T>}::deref"]
def alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref {T : Type} (_A : Type)
    (self : alloc.sync.Arc T) : Result T :=
  ok self.data

/-- [alloc::sync::{impl core::cmp::PartialEq<alloc::sync::Arc<T>> for alloc::sync::Arc<T>}::eq]:
    Source: '/rustc/library/alloc/src/sync.rs', lines 3745:4-3745:43
    Name pattern: [alloc::sync::{core::cmp::PartialEq<alloc::sync::Arc<@T>, alloc::sync::Arc<@T>>}::eq]
    Visibility: public

**Model:** value equality, through the instance of `T` (its failure propagates): `**self ==
**other`, the generic `ArcEqIdent::eq` (lines 3745–3747, 3694–3698).
Stated exception: for `T: Eq` Rust specializes to `ptr::eq(self, other) || **self == **other`
(lines 3713–3717). The model has no pointers, so it always compares the values. The two agree
whenever the equality of `T` is reflexive and does not fail; `Eq` asks for reflexivity
(`core/src/cmp.rs` lines 295–304; `MarkerEq`, `alloc/src/rc.rs` lines 2727–2729), not for the
absence of failure. The only instance in the translation, `T = str`, is byte equality, which has
both. -/
@[rust_fun
  "alloc::sync::{core::cmp::PartialEq<alloc::sync::Arc<@T>, alloc::sync::Arc<@T>>}::eq"]
def alloc.sync.Arc.Insts.CoreCmpPartialEqArc.eq {T : Type} (_A : Type)
    (corecmpPartialEqInst : core.cmp.PartialEq T T) (self : alloc.sync.Arc T)
    (other : alloc.sync.Arc T) : Result Bool :=
  corecmpPartialEqInst.eq self.data other.data

/-! ## Phase 2: `Option`, `Result`, slices and ranges -/

/-- [core::option::{core::option::Option<T>}::or_else]:
    Source: '/rustc/library/core/src/option.rs', lines 1645:4-1650:28
    Name pattern: [core::option::{core::option::Option<@T>}::or_else]
    Visibility: public

**Model:** `Some x ↦ Some x`; `None ↦ f()`, calling the closure through its `FnOnce`
instance, whose failure propagates (lines 1645–1656). -/
@[rust_fun "core::option::{core::option::Option<@T>}::or_else"]
def core.option.Option.or_else {T : Type} {F : Type}
    (opsfunctionFnOnceFTupleOptionInst : core.ops.function.FnOnce F Unit (Option T))
    (self : Option T) (f : F) : Result (Option T) :=
  match self with
  | some x => ok (some x)
  | none => opsfunctionFnOnceFTupleOptionInst.call_once f ()

/-- [core::option::{impl core::cmp::PartialEq<core::option::Option<T>> for core::option::Option<T>}::eq]:
    Source: '/rustc/library/core/src/option.rs', lines 2441:4-2441:38
    Name pattern: [core::option::{core::cmp::PartialEq<core::option::Option<@T>, core::option::Option<@T>>}::eq]
    Visibility: public

**Model:** `(Some l, Some r) ↦ l == r` through the instance of `T` (its failure propagates);
`(None, None) ↦ true`; otherwise `false` (lines 2441–2450). -/
@[rust_fun
  "core::option::{core::cmp::PartialEq<core::option::Option<@T>, core::option::Option<@T>>}::eq"]
def core.option.Option.Insts.CoreCmpPartialEqOption.eq {T : Type}
    (cmpPartialEqInst : core.cmp.PartialEq T T) (self : Option T) (other : Option T) :
    Result Bool :=
  match self, other with
  | some l, some r => cmpPartialEqInst.eq l r
  | some _, none => ok false
  | none, some _ => ok false
  | none, none => ok true

/-- [core::result::{core::result::Result<T, E>}::ok]:
    Source: '/rustc/library/core/src/result.rs', lines 709:4-712:28
    Name pattern: [core::result::{core::result::Result<@T, @E>}::ok]
    Visibility: public

**Model:** `Ok x ↦ Some x`, `Err _ ↦ None` (lines 709–718). Inside its own namespace `ok`
names this definition, hence `Aeneas.Std.Result.ok` (module docstring, ordering note). -/
@[rust_fun "core::result::{core::result::Result<@T, @E>}::ok"]
def core.result.Result.ok {T : Type} {E : Type} (self : core.result.Result T E) :
    Result (Option T) :=
  match self with
  | core.result.Result.Ok x => Aeneas.Std.Result.ok (some x)
  | core.result.Result.Err _ => Aeneas.Std.Result.ok none

/-- [core::slice::{[T]}::first]:
    Source: '/rustc/library/core/src/slice/mod.rs', lines 157:4-157:43
    Name pattern: [core::slice::{[@T]}::first]
    Visibility: public

**Model:** the first element, `None` for the empty slice
(`if let [first, ..] = self { Some(first) } else { None }`, lines 157–159). -/
@[rust_fun "core::slice::{[@T]}::first"]
def core.slice.Slice.first {T : Type} (self : Slice T) : Result (Option T) :=
  match self.val with
  | first :: _ => ok (some first)
  | [] => ok none

/-- Slice equality for slices of equal length (`SlicePartialEq::equal_same_length`,
`core/src/slice/cmp.rs` lines 125–137): compares the elements left to right with `ne` of the
instance (`*lhs.add(idx) != *rhs.add(idx)`) and returns `false` at the first pair for which `ne`
holds, `true` at the end; a failure of `ne` propagates. Rust specializes the loop to a byte
comparison for `BytewiseEq` types (lines 143–157; such as `u8`, `u16`), whose `ne` is the
negation of byte equality and does not fail, so the result is the same. On lists of different
lengths it compares the common prefix; the callers below check the lengths first. -/
def ExtModel.sliceEqSameLength {T U : Type} (inst : core.cmp.PartialEq T U) :
    List T → List U → Result Bool
  | a :: l, b :: r => do
    let d ← inst.ne a b
    if d then ok false else ExtModel.sliceEqSameLength inst l r
  | _, _ => ok true

/-- Slice equality `[T] == [U]` (`impl PartialEq<[U]> for [T]`, `core/src/slice/cmp.rs` lines
14–29): `false` if the lengths differ, otherwise `ExtModel.sliceEqSameLength`. -/
def ExtModel.sliceEq {T U : Type} (inst : core.cmp.PartialEq T U) (l : List T) (r : List U) :
    Result Bool :=
  if l.length = r.length then ExtModel.sliceEqSameLength inst l r else ok false

/-- [core::slice::{[T]}::strip_suffix]:
    Source: '/rustc/library/core/src/slice/mod.rs', lines 2731:4-2733:21
    Name pattern: [core::slice::{[@T]}::strip_suffix]
    Visibility: public

**Model:** the Rust body transcribed (lines 2731–2745): take the suffix as a slice through the
`SlicePattern` instance; if `n = suffix.len() ≤ len = self.len()`, split `self` at `len - n`
(`core.slice.Slice.split_at` of the Aeneas library) and return `Some head` if the tail equals
the suffix (`ExtModel.sliceEq`, i.e. `tail == suffix`); otherwise `None`. Failures of
`as_slice` and of the element equality propagate; the subtraction and the split do not fail
since `n ≤ len`. -/
@[rust_fun "core::slice::{[@T]}::strip_suffix"]
def core.slice.Slice.strip_suffix {T : Type} {P : Type}
    (SlicePatternInst : core.slice.SlicePattern P T) (cmpPartialEqInst : core.cmp.PartialEq T T)
    (self : Slice T) (suffix : P) : Result (Option (Slice T)) := do
  let suffix ← SlicePatternInst.as_slice suffix
  let len := Slice.len self
  let n := Slice.len suffix
  if n ≤ len then
    let mid ← len - n
    let (head, tail) ← core.slice.Slice.split_at self mid
    let b ← ExtModel.sliceEq cmpPartialEqInst tail.val suffix.val
    if b then ok (some head) else ok none
  else ok none

/-- [core::array::equality::{impl core::cmp::PartialEq<[U; N]> for [T]}::eq]:
    Source: '/rustc/library/core/src/array/equality.rs', lines 48:4-48:40
    Name pattern: [core::array::equality::{core::cmp::PartialEq<[@T], [@U; @N]>}::eq]
    Visibility: public

**Model:** `false` unless the slice has length `N` (`self.as_array::<N>()` is `None`,
`core/src/slice/mod.rs` lines 855–865); otherwise array equality `[T; N] == [U; N]`
(lines 48–53, then lines 10–12 and `SpecArrayEq::spec_eq`, lines 143–145: `a[..] == b[..]`),
which is slice equality of two slices of length `N` (`ExtModel.sliceEqSameLength`). The
`BytewiseEq` specialization of `spec_eq` (lines 152–158) gives the same result, as for slices
(see `ExtModel.sliceEqSameLength`). -/
@[rust_fun "core::array::equality::{core::cmp::PartialEq<[@T], [@U; @N]>}::eq"]
def Slice.Insts.CoreCmpPartialEqArray.eq {T : Type} {U : Type} {N : Std.Usize}
    (cmpPartialEqInst : core.cmp.PartialEq T U) (self : Slice T) (other : Array U N) :
    Result Bool :=
  if self.val.length = N.val then ExtModel.sliceEqSameLength cmpPartialEqInst self.val other.val
  else ok false

/-- [core::slice::{impl core::slice::SlicePattern<T> for [T; N]}::as_slice]:
    Source: '/rustc/library/core/src/slice/mod.rs', lines 5696:4-5696:39
    Name pattern: [core::slice::{core::slice::SlicePattern<[@T; @N], @T>}::as_slice]
    Visibility: public

**Model:** the same elements as a slice (`self`, an unsizing coercion, lines 5696–5698;
`Array.to_slice` of the Aeneas library). -/
@[rust_fun "core::slice::{core::slice::SlicePattern<[@T; @N], @T>}::as_slice"]
def Array.Insts.CoreSliceSlicePattern.as_slice {T : Type} {N : Std.Usize} (self : Array T N) :
    Result (Slice T) :=
  ok (Aeneas.Std.Array.to_slice self)

/-- [core::ops::range::{core::ops::range::RangeInclusive<Idx>}::contains]:
    Source: '/rustc/library/core/src/ops/range.rs', lines 539:4-542:44
    Name pattern: [core::ops::range::{core::ops::range::RangeInclusive<@Idx>}::contains]
    Visibility: public

**Model:** `start <= item && item <= end`, or `start <= item && item < start` when the range is
exhausted, with `&&` short-circuiting and failures of the comparisons propagating. `contains`
calls `RangeBounds::contains` (lines 539–545), which is `(match start_bound { Included(s) => s
<= item, .. }) && (match end_bound { Included(e) => item <= e, Excluded(e) => item < e, .. })`
(lines 886–900); for `RangeInclusive` the start bound is `Included(start)` and the end bound is
`Excluded(start)` if `exhausted` ("bounds which are always empty: Included(start)..Excluded(start)"),
else `Included(end)` (lines 1142–1157). `start <= item` is `le` of the instance
`Idx: PartialOrd<U>`; `item <= end` and `item < start` are `le` and `lt` of `U: PartialOrd<Idx>`;
the instance `Idx: PartialOrd<Idx>` is not called. For an exhausted range the result is `false`
whenever the two instances are consistent (`start <= item` and `item < start` cannot both hold),
but the model still calls `lt`, as Rust does, so its failure propagates. Changed in the Aeneas
upgrade (human decision 2026-11-24; model reviewed 2026-11-24, re-signed 2026-11-24): up to `nightly-2026-06-01` the end
bound of an exhausted range was `Excluded(end)`. -/
@[rust_fun
  "core::ops::range::{core::ops::range::RangeInclusive<@Idx>}::contains"]
def core.ops.range.RangeInclusive.contains {Idx : Type} {U : Type}
    (_cmpPartialOrdInst : core.cmp.PartialOrd Idx Idx)
    (cmpPartialOrdInst1 : core.cmp.PartialOrd Idx U)
    (cmpPartialOrdInst2 : core.cmp.PartialOrd U Idx)
    (self : core.ops.range.RangeInclusive Idx) (item : U) : Result Bool := do
  let lower ← cmpPartialOrdInst1.le self.start item
  if lower then
    if self.exhausted then cmpPartialOrdInst2.lt item self.start
    else cmpPartialOrdInst2.le item self.«end»
  else ok false

/-! ## Phase 2: integer parsing -/

/-- The value of an ASCII decimal digit, `none` for every other byte: `(*c as char)
.to_digit(10)` (`core/src/char/methods.rs` lines 409–431, `to_digit`: `'0'`–`'9'` only for
radix 10; a byte cast to `char` is `U+0000`–`U+00FF`, so no other byte is a digit). -/
def ExtModel.decDigit? (c : Std.U8) : Option Nat :=
  if 48 ≤ c.val ∧ c.val ≤ 57 then some (c.val - 48) else none

/-- The digit loop of `i64::from_ascii_bytes_radix_impl` for radix 10 (`core/src/num/mod.rs` lines
1810–1862): from the accumulated value `acc`, read the digits left to right; a byte that is not
a digit is `InvalidDigit`; otherwise the next value is `acc * 10 + d` (positive) or
`acc * 10 - d` (negative), and a value outside `[-2^63, 2^63)` is `PosOverflow` (positive) or
`NegOverflow` (negative). This is the checked loop of the source (lines 1834–1860): at each
digit the digit is checked before the overflow of `checked_mul`, then `checked_add` or
`checked_sub` is checked, and for an accumulated value of the right sign the next value is out
of range exactly when the multiplication or the addition overflows. For at most 15 digits Rust
runs an unchecked loop instead (lines 1810–1833; `can_not_overflow`, lines 1575–1577:
`digits.len() <= 2 * 8 - 1`), whose values lie in range, so the checks above never fire there
either. -/
def ExtModel.i64DigitLoop (positive : Bool) (acc : Int) :
    List Std.U8 → Except ExtModel.IntErrorKind Int
  | [] => .ok acc
  | c :: rest =>
    match ExtModel.decDigit? c with
    | none => .error .InvalidDigit
    | some d =>
      let next : Int := if positive then acc * 10 + d else acc * 10 - d
      if -2 ^ 63 ≤ next ∧ next < 2 ^ 63 then ExtModel.i64DigitLoop positive next rest
      else .error (if positive then .PosOverflow else .NegOverflow)

/-- `i64::from_ascii_bytes_radix_impl(src, 10)` (`core/src/num/mod.rs` lines 1775–1863), as an integer or
an error kind: empty input is `Empty`; a single `+` or `-` is `InvalidDigit`; a leading `+` or
`-` is removed and sets the sign (the type is signed); then `ExtModel.i64DigitLoop` from `0`. -/
def ExtModel.i64FromAscii (src : List Std.U8) : Except ExtModel.IntErrorKind Int :=
  match src with
  | [] => .error .Empty
  | [c] =>
    if c.val = 43 ∨ c.val = 45 then .error .InvalidDigit
    else ExtModel.i64DigitLoop true 0 [c]
  | c :: rest =>
    if c.val = 43 then ExtModel.i64DigitLoop true 0 rest
    else if c.val = 45 then ExtModel.i64DigitLoop false 0 rest
    else ExtModel.i64DigitLoop true 0 (c :: rest)

/-- [core::num::{impl core::str::traits::FromStr<core::num::error::ParseIntError> for i64}::from_str]:
    Source: '/rustc/library/core/src/num/mod.rs', lines 1632:12-1632:68
    Name pattern: [core::num::{core::str::traits::FromStr<i64, core::num::error::ParseIntError>}::from_str]
    Visibility: public

**Model:** `Ok v` where `ExtModel.i64FromAscii` gives the integer `v`, `Err { kind }` where it
gives the error kind. Rust: `from_str(src) = i64::from_str_radix(src, 10)` (lines 1632–1634),
which is `i64::from_ascii_bytes_radix_impl(src.as_bytes(), 10)` (lines 1683–1685); radix 10 passes the
radix check, so this never panics. Grammar: an optional single `+` or `-`, then at least one
ASCII digit and nothing else; leading zeros are allowed; whitespace, `_` and non-ASCII digits
are `InvalidDigit`; error kinds as reported by Rust (`Empty`, `InvalidDigit`, `PosOverflow`,
`NegOverflow`; the first error met from the left wins, a non-digit before an overflow at the
same position). The model reads only the bytes, as Rust does, so it is defined on every `Str`.
The integer `v` lies in `[-2^63, 2^63)` (checked by the loop), so it is the value of the
`I64` built from it. -/
@[rust_fun
  "core::num::{core::str::traits::FromStr<i64, core::num::error::ParseIntError>}::from_str"]
def I64.Insts.CoreStrTraitsFromStrParseIntError.from_str (src : Str) :
    Result (core.result.Result Std.I64 core.num.error.ParseIntError) :=
  match ExtModel.i64FromAscii src.val with
  | .ok v => ok (core.result.Result.Ok ⟨BitVec.ofInt 64 v⟩)
  | .error kind => ok (core.result.Result.Err { kind })

/-- [core::str::{str}::parse]:
    Source: '/rustc/library/core/src/str/mod.rs', lines 2781:4-2781:56
    Name pattern: [core::str::{str}::parse]
    Visibility: public

**Model:** dispatches to the `FromStr` instance (`FromStr::from_str(self)`, lines 2781–2783);
its failure propagates. -/
@[rust_fun "core::str::{str}::parse"]
def core.str.Str.parse {F : Type} {Clause0_Err : Type}
    (traitsFromStrInst : core.str.traits.FromStr F Clause0_Err) (self : Str) :
    Result (core.result.Result F Clause0_Err) :=
  traitsFromStrInst.from_str self

/-! ## Phase 2: IP addresses

Transcribed from `library/core/src/net/ip_addr.rs` of the pinned toolchain. An `Ipv4Addr` is
its four octets and an `Ipv6Addr` its eight segments (`Rmcp.TypesExternal`); every function
below is total and never panics, like its Rust source. -/

/-- The number whose big-endian digits in base `b` are `l` (most significant first):
`u32::from_be_bytes` for four octets with `b = 256`, and `u128::from_be_bytes` of the sixteen
octets of an IPv6 address for its eight segments with `b = 65536`. -/
def ExtModel.beNat (b : Nat) (l : List Nat) : Nat :=
  l.foldl (fun acc d => acc * b + d) 0

/-- The octets of an IPv4 address as natural numbers, most significant first. -/
def ExtModel.ipv4Nats (a : core.net.ip_addr.Ipv4Addr) : List Nat :=
  a.addrOctets.val.map (fun o => o.val)

/-- The segments of an IPv6 address as natural numbers, most significant first. -/
def ExtModel.ipv6Nats (a : core.net.ip_addr.Ipv6Addr) : List Nat :=
  a.addrSegments.val.map (fun s => s.val)

/-- [core::net::ip_addr::{core::net::ip_addr::Ipv4Addr}::octets]:
    Source: '/rustc/library/core/src/net/ip_addr.rs', lines 697:4-697:41
    Name pattern: [core::net::ip_addr::{core::net::ip_addr::Ipv4Addr}::octets]
    Visibility: public

**Model:** the four octets (`self.octets`, lines 697–699). -/
@[rust_fun "core::net::ip_addr::{core::net::ip_addr::Ipv4Addr}::octets"]
def core.net.ip_addr.Ipv4Addr.octets (self : core.net.ip_addr.Ipv4Addr) :
    Result (Array Std.U8 4#usize) :=
  ok self.addrOctets

/-- [core::net::ip_addr::{core::net::ip_addr::Ipv4Addr}::is_unspecified]:
    Source: '/rustc/library/core/src/net/ip_addr.rs', lines 757:4-757:46
    Name pattern: [core::net::ip_addr::{core::net::ip_addr::Ipv4Addr}::is_unspecified]
    Visibility: public

**Model:** `u32::from_be_bytes(self.octets) == 0` (lines 757–759), i.e. `0.0.0.0`. -/
@[rust_fun
  "core::net::ip_addr::{core::net::ip_addr::Ipv4Addr}::is_unspecified"]
def core.net.ip_addr.Ipv4Addr.is_unspecified (self : core.net.ip_addr.Ipv4Addr) :
    Result Bool :=
  ok (decide (ExtModel.beNat 256 (ExtModel.ipv4Nats self) = 0))

/-- [core::net::ip_addr::{core::net::ip_addr::Ipv4Addr}::is_loopback]:
    Source: '/rustc/library/core/src/net/ip_addr.rs', lines 779:4-779:43
    Name pattern: [core::net::ip_addr::{core::net::ip_addr::Ipv4Addr}::is_loopback]
    Visibility: public

**Model:** `self.octets()[0] == 127` (lines 779–781), i.e. `127.0.0.0/8`. The index is in
bounds (four octets); the default of `getD` is never used. -/
@[rust_fun "core::net::ip_addr::{core::net::ip_addr::Ipv4Addr}::is_loopback"]
def core.net.ip_addr.Ipv4Addr.is_loopback (self : core.net.ip_addr.Ipv4Addr) : Result Bool :=
  ok (decide ((ExtModel.ipv4Nats self).getD 0 0 = 127))

/-- [core::net::ip_addr::{core::net::ip_addr::Ipv4Addr}::is_private]:
    Source: '/rustc/library/core/src/net/ip_addr.rs', lines 810:4-810:42
    Name pattern: [core::net::ip_addr::{core::net::ip_addr::Ipv4Addr}::is_private]
    Visibility: public

**Model:** the match of lines 810–817: `[10, ..]`, `[172, b, ..]` with `16 ≤ b ≤ 31`, and
`[192, 168, ..]` are private (`10.0.0.0/8`, `172.16.0.0/12`, `192.168.0.0/16`); everything else
is not. -/
@[rust_fun "core::net::ip_addr::{core::net::ip_addr::Ipv4Addr}::is_private"]
def core.net.ip_addr.Ipv4Addr.is_private (self : core.net.ip_addr.Ipv4Addr) : Result Bool :=
  match ExtModel.ipv4Nats self with
  | 10 :: _ => ok true
  | 172 :: b :: _ => ok (decide (b ≥ 16 ∧ b ≤ 31))
  | 192 :: 168 :: _ => ok true
  | _ => ok false

/-- [core::net::ip_addr::{core::net::ip_addr::Ipv4Addr}::is_link_local]:
    Source: '/rustc/library/core/src/net/ip_addr.rs', lines 838:4-838:45
    Name pattern: [core::net::ip_addr::{core::net::ip_addr::Ipv4Addr}::is_link_local]
    Visibility: public

**Model:** `matches!(self.octets(), [169, 254, ..])` (lines 838–840), i.e. `169.254.0.0/16`. -/
@[rust_fun "core::net::ip_addr::{core::net::ip_addr::Ipv4Addr}::is_link_local"]
def core.net.ip_addr.Ipv4Addr.is_link_local (self : core.net.ip_addr.Ipv4Addr) :
    Result Bool :=
  match ExtModel.ipv4Nats self with
  | 169 :: 254 :: _ => ok true
  | _ => ok false

/-- [core::net::ip_addr::{core::net::ip_addr::Ipv4Addr}::is_multicast]:
    Source: '/rustc/library/core/src/net/ip_addr.rs', lines 1039:4-1039:44
    Name pattern: [core::net::ip_addr::{core::net::ip_addr::Ipv4Addr}::is_multicast]
    Visibility: public

**Model:** `self.octets()[0] >= 224 && self.octets()[0] <= 239` (lines 1039–1041), i.e.
`224.0.0.0/4`. The default of `getD` is never used (four octets). -/
@[rust_fun "core::net::ip_addr::{core::net::ip_addr::Ipv4Addr}::is_multicast"]
def core.net.ip_addr.Ipv4Addr.is_multicast (self : core.net.ip_addr.Ipv4Addr) :
    Result Bool :=
  ok (decide ((ExtModel.ipv4Nats self).getD 0 0 ≥ 224 ∧
    (ExtModel.ipv4Nats self).getD 0 0 ≤ 239))

/-- [core::net::ip_addr::{core::net::ip_addr::Ipv4Addr}::is_broadcast]:
    Source: '/rustc/library/core/src/net/ip_addr.rs', lines 1061:4-1061:44
    Name pattern: [core::net::ip_addr::{core::net::ip_addr::Ipv4Addr}::is_broadcast]
    Visibility: public

**Model:** `u32::from_be_bytes(self.octets()) == u32::from_be_bytes(Self::BROADCAST.octets())`
(lines 1061–1063), with `BROADCAST = 255.255.255.255` (line 681). -/
@[rust_fun "core::net::ip_addr::{core::net::ip_addr::Ipv4Addr}::is_broadcast"]
def core.net.ip_addr.Ipv4Addr.is_broadcast (self : core.net.ip_addr.Ipv4Addr) :
    Result Bool :=
  ok (decide (ExtModel.beNat 256 (ExtModel.ipv4Nats self) =
    ExtModel.beNat 256 [255, 255, 255, 255]))

/-- [core::net::ip_addr::{impl core::convert::From<u32> for core::net::ip_addr::Ipv4Addr}::from]:
    Source: '/rustc/library/core/src/net/ip_addr.rs', lines 1318:4-1318:32
    Name pattern: [core::net::ip_addr::{core::convert::From<core::net::ip_addr::Ipv4Addr, u32>}::from]
    Visibility: public

**Model:** the big-endian bytes of `ip` as octets: `Ipv4Addr::from_bits(ip)` (lines 1318–1320),
which is `Ipv4Addr { octets: bits.to_be_bytes() }` (lines 637–639), so the first octet is
`ip / 2^24` and the last `ip mod 256` (`ExtModel.byte` takes the value modulo 256). -/
@[rust_fun
  "core::net::ip_addr::{core::convert::From<core::net::ip_addr::Ipv4Addr, u32>}::from"]
def core.net.ip_addr.Ipv4Addr.Insts.CoreConvertFromU32.from (ip : Std.U32) :
    Result core.net.ip_addr.Ipv4Addr :=
  ok { addrOctets := Std.Array.from [ExtModel.byte (ip.val / 2 ^ 24), ExtModel.byte (ip.val / 2 ^ 16),
                   ExtModel.byte (ip.val / 2 ^ 8), ExtModel.byte ip.val] (by simp) }

/-- [core::net::ip_addr::{core::net::ip_addr::Ipv6Addr}::segments]:
    Source: '/rustc/library/core/src/net/ip_addr.rs', lines 1525:4-1525:44
    Name pattern: [core::net::ip_addr::{core::net::ip_addr::Ipv6Addr}::segments]
    Visibility: public

**Model:** the eight segments, which the model stores (lines 1525–1540 compute them from the
sixteen octets as big-endian `u16` values; see `core.net.ip_addr.Ipv6Addr`). -/
@[rust_fun "core::net::ip_addr::{core::net::ip_addr::Ipv6Addr}::segments"]
def core.net.ip_addr.Ipv6Addr.segments (self : core.net.ip_addr.Ipv6Addr) :
    Result (Array Std.U16 8#usize) :=
  ok self.addrSegments

/-- [core::net::ip_addr::{core::net::ip_addr::Ipv6Addr}::is_unspecified]:
    Source: '/rustc/library/core/src/net/ip_addr.rs', lines 1588:4-1588:46
    Name pattern: [core::net::ip_addr::{core::net::ip_addr::Ipv6Addr}::is_unspecified]
    Visibility: public

**Model:** `u128::from_be_bytes(self.octets()) == u128::from_be_bytes(Ipv6Addr::UNSPECIFIED
.octets())` (lines 1588–1590), with `UNSPECIFIED = ::` (line 1509), i.e. all segments zero. The
`u128` of the octets is `ExtModel.beNat 65536` of the segments. -/
@[rust_fun
  "core::net::ip_addr::{core::net::ip_addr::Ipv6Addr}::is_unspecified"]
def core.net.ip_addr.Ipv6Addr.is_unspecified (self : core.net.ip_addr.Ipv6Addr) :
    Result Bool :=
  ok (decide (ExtModel.beNat 65536 (ExtModel.ipv6Nats self) =
    ExtModel.beNat 65536 [0, 0, 0, 0, 0, 0, 0, 0]))

/-- [core::net::ip_addr::{core::net::ip_addr::Ipv6Addr}::is_loopback]:
    Source: '/rustc/library/core/src/net/ip_addr.rs', lines 1612:4-1612:43
    Name pattern: [core::net::ip_addr::{core::net::ip_addr::Ipv6Addr}::is_loopback]
    Visibility: public

**Model:** `u128::from_be_bytes(self.octets()) == u128::from_be_bytes(Ipv6Addr::LOCALHOST
.octets())` (lines 1612–1614), with `LOCALHOST = ::1` (line 1492). -/
@[rust_fun "core::net::ip_addr::{core::net::ip_addr::Ipv6Addr}::is_loopback"]
def core.net.ip_addr.Ipv6Addr.is_loopback (self : core.net.ip_addr.Ipv6Addr) : Result Bool :=
  ok (decide (ExtModel.beNat 65536 (ExtModel.ipv6Nats self) =
    ExtModel.beNat 65536 [0, 0, 0, 0, 0, 0, 0, 1]))

/-- [core::net::ip_addr::{core::net::ip_addr::Ipv6Addr}::is_multicast]:
    Source: '/rustc/library/core/src/net/ip_addr.rs', lines 1972:4-1972:44
    Name pattern: [core::net::ip_addr::{core::net::ip_addr::Ipv6Addr}::is_multicast]
    Visibility: public

**Model:** `(self.segments()[0] & 0xff00) == 0xff00` (lines 1972–1974), i.e. `ff00::/8`. The
default of `getD` is never used (eight segments). -/
@[rust_fun "core::net::ip_addr::{core::net::ip_addr::Ipv6Addr}::is_multicast"]
def core.net.ip_addr.Ipv6Addr.is_multicast (self : core.net.ip_addr.Ipv6Addr) :
    Result Bool :=
  ok (decide ((self.addrSegments.val.getD 0 0#u16 &&& 0xff00#u16) = 0xff00#u16))
