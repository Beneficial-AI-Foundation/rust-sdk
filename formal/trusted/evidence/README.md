# Evidence for the external models (plan steps S08–S09, S26–S27) and the Phase 2 test map (S34)

`formal/trusted/Rmcp/TypesExternal.lean` and `FunsExternal.lean` model every external of the
translation, i.e. every type and function that Charon did not translate: those of other crates
and of the standard library, and the opaque `rmcp` items (the four `prim` functions and
`RequestStateCodec::now_ms`); 41 externals, inventory in the S04a evidence (git history at 223ff12). Since
S08–S09 **they declare no axiom**: each type is a `structure`, each function a definition with
the generated name and signature, keeping the template's `@[rust_type]` or `@[rust_fun]`
attribute where it has one (the five opaque `rmcp` functions have none). What the models
cannot compute is an `opaque` constant, which adds no axiom (`#print axioms` does not list it):

| Opaque constant | Stands for | Why it is not computed |
|---|---|---|
| `ExtModel.hmacSha256 : List U8 → List U8 → Array U8 32` | HMAC-SHA256 (RFC 2104, FIPS 180-4) | correctness of the `hmac`/`sha2` crates is out of scope (plan Section 4) |
| `ExtModel.sipHash13 : U64 → U64 → List U8 → U64` | SipHash-1-3 of `DefaultHasher` | no statement depends on hash values (`HashMap::get` is modelled without hashing) |
| `ExtModel.nowMs : I64` | the clock reading of `now_ms` | not a function of anything the model has |
| `ExtModel.SerdeJsonErrorImpl : Type` | the boxed content of `serde_json::Error` | never created or inspected |
| `ExtModel.SerdeJsonValue : Type` | `serde_json::Value` (Phase 2, S26/S27) | the translated code only moves values of this type |

This follows the human decision of 2026-11-23 to convert every placeholder axiom into a
definition (plan Section 4). Because there is no axiom, the consistency models of the earlier
design (`formal/proofs/Proofs/Consistency/`) are unnecessary: a definition cannot prove `False`, and
`trusted/axioms.lock` stays empty. The Base64 laws that the plan expected as axioms are theorems
(`formal/proofs/Proofs/External/Base64.lean`). What remains to be trusted about each model is
that it describes the Rust function; the source each one encodes is cited below (and in its
docstring), and the Rust tests that exercise it are listed. The tests catch a mismatched model;
they are not a proof. All tests named in the Phase 1 sections are in the crate's own test modules
and run with
`cargo test -p rmcp --no-default-features --features request-state --lib model::request_state`
(the Phase 2 map below records its own commands).

Source paths: `rust-src` is
`library/` of the pinned toolchain `nightly-2026-09-17` (since the Aeneas upgrade of 2026-11-24;
the runs recorded below used `nightly-2026-06-01`); crate paths are in
`~/.cargo/registry/src/index.crates.io-*/`, at the versions pinned by
`scripts/aeneas-translate.sh` (`hmac 0.13.0`, `sha2 0.11.1`, `base64 0.23.1`, `digest 0.11.3`,
`zeroize 1.9.2`, `chrono 0.4.45`, `serde_json 1.0.154`; plan Section 4), and std's
`hashbrown 0.17.1` per the toolchain's `library/Cargo.lock`. Test files: `wire` = `crates/rmcp/src/model/
request_state_wire.rs`, `codec` = `crates/rmcp/src/model/request_state.rs`, both in the patched
copy (patch 01 on origin/main 7caec76, `formal/trusted/patches/01-request-state-wire.patch`, D2
fallback 2026-11-23): `request_state_wire.rs` and every test named here that the patch adds exist
only there, so run the command above in `.llbc/work/crates/rmcp` after
`scripts/apply-patches.sh` (as `patched-tests.yml` does).

## HMAC (`prim::hmac_sha256`, `prim::hmac_sha256_verify`)

- **Model.** `hmac_sha256 k m = ok (hmacSha256 k m)`; `hmac_sha256_verify k m t = ok (t =
  hmacSha256 k m)` as byte lists.
- **Source.** `Hmac::<Sha256>::new_from_slice` returns `Ok` for every key length
  (`hmac-0.13.0/src/block_api.rs` lines 53–69, key reduced by `get_der_key`), so the `expect`
  never panics. `Mac::verify_slice` (`digest-0.11.3/src/mac.rs` lines 139–146) returns `Err`
  when `tag.len() != 32` and otherwise compares in constant time (timing not modelled).
- **Tests.** `wire::rfc4231_hmac_sha256_vectors` (RFC 4231 cases 1–7 through both functions,
  flipped tag rejected, case 5's truncated tag rejected by `verify`);
  `wire::hmac_sha256_verify_rejects_wrong_length_tags` (empty, 31-byte and 33-byte tags
  rejected; empty key accepted); `wire::transcripts_match_incremental_hmac`;
  `codec::rs1_known_answer_is_unchanged`, `codec::rs2_known_answer_matches_wire_specification`;
  `wire::s16_prim_rfc4231_verify_accepts_only_the_exact_tag` (S16: for RFC 4231 cases 1–4, 6,
  7 only the exact tag is accepted; prefixes, an extension, flipped bytes and the other
  cases' tags are rejected).
- **Stated exception (not modelled).** SHA-256 finalisation computes the bit length as a `u64`
  (`sha2-0.11.1/src/block_api.rs` line 66), which overflows (a panic under `overflow-checks`)
  when the hashed input reaches `2^61` bytes: for a message of at least `2^61 − 64` bytes (inner
  hash of the 64-byte key block and the message) and for a key of at least `2^61` bytes
  (`get_der_key`, `hmac-0.13.0/src/utils.rs` lines 9–32, hashes a key longer than 64 bytes).
  Both lie outside the size convention of `FunsExternal.lean` (no claim about inputs of at least
  `2^61` bytes; unreachable on `x86_64`, whose address space is at most `2^57` bytes).
- **Not established.** That `hmacSha256` is HMAC-SHA256; cryptographic security; constant time.

## Base64url without padding (`prim::b64_encode_into`, `prim::b64_decode`)

- **Model.** Concrete encoder `ExtModel.b64` and strict decoder `ExtModel.b64Decode` over
  `List U8`. `b64_encode_into x out` appends the symbols of `b64 x` to `out` (subject to the
  `String` limit below); `b64_decode x = ok (b64Decode x)`.
- **Source.** `URL_SAFE_NO_PAD = GeneralPurpose::new(&alphabet::URL_SAFE, NO_PAD)`
  (`base64-0.23.1/src/engine/general_purpose/mod.rs` line 472); `URL_SAFE` alphabet
  `A–Z a–z 0–9 - _` (`src/alphabet.rs` lines 259–262); `NO_PAD` = no padding on encode and
  `DecodePaddingMode::RequireNone` (lines 499–501); `decode_allow_trailing_bits = false` by
  default (line 341). Decoding: `decode_helper` and `complete_quads_len`
  (`src/engine/general_purpose/decode.rs`; `=` is not in the decode table, so it is
  `InvalidByte` in a non-final quad) and `decode_suffix`
  (`src/engine/general_purpose/decode_suffix.rs`: padding rejected under `RequireNone`, one
  leftover symbol is `InvalidLength`, set trailing bits are `InvalidLastSymbol`).
  Encoding: `Engine::encode_string` (`src/engine/mod.rs` lines 188–201) through
  `ChunkedEncoder` (`src/chunked_encoder.rs`, 768-byte chunks, `push_str` of ASCII).
- **Proved** (`formal/proofs/Proofs/External/Base64.lean`): `b64Decode (b64 x) = some x`;
  `b64Decode s = some y ↔ b64 y = s` (so padding, foreign bytes, length `≡ 1 (mod 4)` and
  non-canonical trailing bits are rejected); every output byte is in the URL-safe alphabet (in
  particular never `.`); `(b64 x).length = (4n + 2) / 3`, `≤ Defs.Wire.b64Len n`, with equality
  when `3 ∣ n`; the RFC 4648 Section 10 vectors and every case of the Rust tests below, by
  `decide` (kernel evaluation, no `native_decide`).
- **Tests.** `wire::rfc4648_base64url_vectors`, `wire::base64url_alphabet_and_append`,
  `wire::base64url_decode_is_strict`, `wire::base64url_roundtrip` (all 256 prefixes of
  `0..=255`, alphabet and round trip), `wire::b64_len_matches_encoder_output_length`;
  `codec::non_base64_sections_are_invalid_encoding`,
  `codec::parser_rejects_invalid_tokens_and_unavailable_keys`; added by S16 (their cases are
  not, in general, proved by `decide` above): `wire::s16_prim_rfc4648_sec10_padded_forms_rejected`,
  `wire::s16_prim_rfc4648_standard_alphabet_rejected`,
  `wire::s16_prim_rfc4648_noncanonical_trailing_bits_rejected`.
- **Not established.** That the crate has no bug outside the tested inputs (the model is the
  RFC 4648 definition; the tests compare the crate with it on the vectors).

## Differential check (Base64url and UTF-8)

`differential/` compares the Lean models with the Rust crates line by line, outside any build or
CI job: `Diff.lean.in` (run with `lake env lean --run`; the extension keeps it out of the
`formal/` source checks, since it needs a root-level `main`) prints the results of
`b64_encode_into`, `b64_decode`, `String::from_utf8` (with `as_bytes`) and `as_bytes` of Lean
strings; `rdiff/` (`base64 = "=0.23.1"`, std) prints the same for `URL_SAFE_NO_PAD.encode_string`
(into an empty and a non-empty `String`), `URL_SAFE_NO_PAD.decode`, `String::from_utf8` and
`String::as_bytes`; `gen.py` writes the inputs with seed `random.Random(20261123)` (random byte
strings, mutated encodings with padding, foreign bytes, wrong lengths and non-canonical trailing
symbols, random and adversarial UTF-8 including overlong forms, surrogates, code points above
`U+10FFFF` and truncations) and, for the long inputs added in fix round 3, a second stream
`random.Random(20261124)`: encodings of byte strings around the 768-byte chunk of
`ChunkedEncoder` and its double (lengths 760–776 and 1530–1544), of 2300–2309 and 2990–3010
bytes (several chunks), and around the 24-byte (32-symbol) steps of the encoder's fast loop
(`24k − 1`, `24k`, `24k + 1` for `k` = 1..11), each with random, all-`0xff` and all-zero
content; and decoder inputs of up to 400 symbols (encodings of 1–300 bytes, past the decoder's
32-symbol unrolled steps), valid, with padding, an extra or a missing symbol, a changed last
symbol (trailing bits), and a foreign byte replacing or inserted at a position among the last 40
symbols. `run.sh` adds exhaustive ranges (every byte string of length ≤ 3 encoded; every byte
string of length ≤ 2 and every 3-byte string with a lead byte ≥ `0x80` through `from_utf8`). It
copies `rdiff/` into the scratch directory and builds it there with `cargo build --locked` from
the committed `rdiff/Cargo.lock` (`base64 0.23.1`, crates.io checksum), so it writes nothing in
the source tree, and records the `cargo`, `rustc` and `python3` versions in
`<scratch>/toolchain.txt`. Command, from the repository root, after `cd formal && lake build
RmcpExternal`:

```
formal/trusted/evidence/differential/run.sh formal <new scratch directory>
```

Result (2026-11-23, S08/S09 fix round 3, models of this change; `cargo 1.92.0`, `rustc 1.92.0`,
`Python 3.11.8`, Lean `v4.31.0`): 25,682,976 comparisons, 0 mismatches (`enc_prefix` 10,576;
`dec` 261,694; `utf8` 93,286; `cps` 20,011; `enc_exh` 16,843,009; `utf8_exh` 8,454,400); about
2 minutes. Like the tests, it catches a mismatched model on the inputs it tries; it is not a
proof.

What the check executes: `lake env lean --run` runs the models as compiled code, not their
kernel definitions. For the UTF-8 models this matters: `String.fromUTF8?` (through
`String.validateUTF8`, `@[extern "lean_string_validate_utf8"]`), `String.toByteArray`
(`@[extern "lean_string_to_utf8"]`) and `String.utf8ByteSize` are executed by the C
implementations of the Lean runtime, so the UTF-8 comparisons test that runtime code against
Rust, and say something about the Lean definitions the proofs use only through Lean's own
trust that its runtime implements them. The kernel-level facts are the theorems of
`formal/proofs/Proofs/External/String.lean` (for example `strOfBytes?_eq_some_iff`). The Base64
models use no `extern` string function; they run as code compiled from their list definitions,
with `Nat` and bit-vector arithmetic through the runtime's own implementations, so they too are
tested as compiled code (their laws are the theorems of `Proofs/External/Base64.lean`).

## Standard library

Line numbers in this table and the Phase 2 table below are those cited when the models were
written (`rust-src` of `nightly-2026-06-01`); the current citations, re-checked against
`nightly-2026-09-17` in the Aeneas upgrade of 2026-11-24 (lead decision N9), are those in the
docstrings of `formal/trusted/Rmcp/FunsExternal.lean`, which are authoritative. Rows marked
"moved" are no longer project models: since that upgrade the Aeneas library defines them (lead
decision N8; the upgrade review found the semantics identical); the row is kept as history.

| External | Model | Source (`rust-src`) | Tests |
|---|---|---|---|
| `Borrow::borrow` (blanket) — **moved to the Aeneas library** (N8) | identity | `core/src/borrow.rs` 214–216 | through `HashMap::get` below |
| `Option::ok_or` — **moved to the Aeneas library** (N8) | `Some v ↦ Ok v`, `None ↦ Err e` | `core/src/option.rs` 1334–1339 | `codec::non_base64_sections_are_invalid_encoding` |
| `Option` `Default` | `None` | `core/src/option.rs` 2313–2315 | (non-target) |
| `Result::is_err` | `true` iff `Err` | `core/src/result.rs` 646–648 | `codec::maximum_length_kid_roundtrips_and_oversized_wire_kid_is_rejected` |
| `Result::map_err` — **moved to the Aeneas library** (N8) | `Err e ↦ Err (op e)` via `FnOnce` | `core/src/result.rs` 962–970 | `codec::parser_rejects_invalid_tokens_and_unavailable_keys` (non-UTF-8 kid) |
| `&[T]` `Default` | empty slice | `core/src/slice/mod.rs` 5637–5639 | (non-target) |
| `str::len` | byte count (any `Str`) | `core/src/str/mod.rs` 153–155 | `wire::check_kid_len_counts_utf8_bytes`, `codec::constructor_invariants_are_enforced` |
| `str::as_bytes` | same bytes (any `Str`) | `core/src/str/mod.rs` 498–501 | every `codec` open test |
| `String::with_capacity` | `""`; panic if `> isize::MAX` | `alloc/src/string.rs` 493–495; `alloc/src/raw_vec/mod.rs` 446–482 (`try_allocate_in`), 896–902 (`layout_array`) | `codec::rs1_known_answer_is_unchanged`, `codec::rs2_known_answer_matches_wire_specification` |
| `String::push_str` | append; `fail undef` on non-UTF-8 `Str`; panic beyond `isize::MAX` | `alloc/src/string.rs` 1110–1112; `raw_vec/mod.rs` 502–533 | same |
| `String::push` | append char; panic beyond `isize::MAX` | `alloc/src/string.rs` 1425–1435 | same |
| `String::as_bytes` | UTF-8 bytes; `fail` above `Usize.max` (no Rust `String`) | `alloc/src/string.rs` 1454–1456 | `codec::rs2_roundtrips_with_associated_data_and_ttl` |
| `String::from_utf8` | `Ok s` iff bytes are `utf8 s`, else `Err {bytes}` | `alloc/src/string.rs` 569–574 | `codec::parser_rejects_invalid_tokens_and_unavailable_keys` (kid `[0xff]` ↦ `InvalidKeyId`) |
| `String` `PartialEq::eq`, `Eq::assert_fields_are_eq`, `Clone` | equality; `()`; identity | `alloc/src/string.rs` 350, 2364–2366 | through `HashMap::get` |
| `String` `Hash::hash` | write bytes, then `0xff` | `alloc/src/string.rs` 2740–2742; `core/src/hash/mod.rs` 550–553, 862–866; for `DefaultHasher`: `std/src/hash/random.rs` 135–137 → `core/src/hash/sip.rs` 237–239 → override 303–308 (`write(bytes); write_u8(0xFF)`), `write_u8` not overridden (note at 248) so default `write(&[i])` (`core/src/hash/mod.rs` 362–364) | (unused by the `get` model) |
| `Vec::is_empty` — **moved to the Aeneas library** (N8) | `len == 0` | `alloc/src/vec/mod.rs` 3085–3087 | `codec::pinned_tokens_and_open_results_are_unchanged` (case `rs1 ring no fallbacks: UnknownKeyId`) |
| `RandomState` (type, `Clone`, `build_hasher`) | `{k0, k1}`; identity; keys + empty stream | `std/src/hash/random.rs` 34–38, 83–85 | — |
| `DefaultHasher` (type, `write`, `finish`) | keys + written bytes; append; `sipHash13` | `std/src/hash/random.rs` 94, 125–142 | — |
| `HashMap` (type), `HashMap::get` | association list; first entry with an equal key | `std/src/collections/hash/map.rs` 246–251, 1035–1041; hashbrown 0.17.1 `src/map.rs` (`get`, `Equivalent`) | `codec::rotation_keeps_previous_rs2_key_verifiable` (found and `UnknownKeyId`), `codec::multiple_legacy_fallbacks_are_supported`, `codec::kid_is_authenticated_even_when_ids_share_key_bytes` |
| `HashMap` `Clone` | clone builder, allocator, entries | `map.rs` 1438–1440; hashbrown `impl Clone for HashMap` | (non-target) |
| `Duration`, `FromUtf8Error`, `serde_json::Error` (types) | fields `{secs, nanos}`; `{bytes}` (the `error: Utf8Error` field is not modelled); `{err}` with opaque content | `core/src/time.rs` 81–84; `alloc/src/string.rs` 391–394; `serde_json-1.0.154/src/error.rs` 17–22 | — |

`String` conventions (in `FunsExternal.lean`'s module docstring): out-of-memory is not
modelled (plan Section 4, unlimited memory); growth beyond `isize::MAX` bytes is the
deterministic "capacity overflow" panic and is `fail panic`; a panic that depends on the
capacity history (amortized doubling past `isize::MAX` while the length still fits) is not
modelled. Hence `ok` from a `String` model means "returns, or aborts or panics for memory
reasons": out of memory, or `RawVec::grow_amortized` requesting
`max(2·cap, len + additional)` above `isize::MAX` when the capacity is already above
`isize::MAX / 2`. A Lean `String`, like a Rust `String`, is always valid UTF-8 (`String.isValidUTF8`),
and `ExtModel.strOfBytes?` accepts exactly the encodings of Unicode scalar values (Lean
`String.fromUTF8?`), the set Rust's `core::str::from_utf8` accepts.

`HashMap::get` without hashing: hashbrown's `get` returns `None` on an empty table and otherwise
probes the entries whose hash matches `hash(k)`, comparing with `k == key.borrow()`. For a
`Hash`/`Eq` pair that agree (required by the `HashMap` documentation) the probe finds the entry
with an equal key, whatever the hash values; for `String`, equality is byte equality and `Hash`
writes the bytes. The model is faithful for `Hash`/`Eq` instances that agree and do not fail;
only `K = Q = String` occurs. It returns the first entry with an equal key, which is the Rust
result when keys are pairwise distinct; that invariant is not in the type (a generic `clone`
could not preserve it). Distinctness (`Nodup` of the keys) is needed only to identify *which*
value is returned: `find` returns `some` exactly when an equal key exists, with or without
duplicates. Statements at S12 should therefore assume `Nodup` only where they name the value,
not where they only need "found" or "not found": `Proofs.External.HashMap.find?_key_isSome_iff`
(found exactly when `k` is a key) and `find?_key_of_not_mem` have no `Nodup` premise;
`find?_key_of_mem` uses it to name the value.

## `zeroize`

| External | Model | Source (`zeroize-1.9.2/src/lib.rs`) |
|---|---|---|
| `Zeroizing<Z>` (type) | `{inner : Z}` | 582–584 (`repr(transparent)` tuple struct) |
| `Zeroizing::new` | wrap | 599–601 |
| `Zeroizing` `Clone` | wrap a clone | 606–608 |
| `Zeroizing` `Deref` | the inner value | 634–636 |
| `Zeroize` for `Z: DefaultIsZeroes` | `Z::default()` | 282–284 (`volatile_write(self, Z::default())`) |
| `Zeroize` for `Vec<Z>` | zeroize each element, result empty | 505–516 (spare capacity, `iter_mut().zeroize()`, `clear()`) |

Tests: every keyring test of `codec` goes through `Zeroizing::deref` (`two_key_ring`,
`rotation_keeps_previous_rs2_key_verifiable`, ...). **Not established:** zeroisation on drop
(the `Drop` impl has no counterpart in a value model; plan Section 4) and the volatile writes.

## Clock (`RequestStateCodec::now_ms`)

- **Model.** `ok nowMs`, an opaque constant (`chrono::Utc::now().timestamp_millis()`,
  `codec` lines 729–731).
- **Environmental assumption (stated exception, not modelled).** `Utc::now` panics if the
  system clock is before 1970 or outside chrono's range (`chrono-0.4.45/src/offset/utc.rs`
  lines 96–98: `expect("system time before Unix epoch")`, `DateTime::from_timestamp(..)
  .unwrap()`); the model assumes the clock is in range.
- **Limitation.** One constant cannot express that two readings differ, and it makes every
  function that reads the clock pure. The callers of `now_ms` are `open` and `open_with`, which
  are translated (`formal/translation/Rmcp/Funs.lean`, `open_with` and `open`) but are not
  targets, and `seal_with`, which is excluded from the translation (Charon `exclude`, B13).
- **Review rule.** No spec statement mentions the functions
  `rmcp.model.request_state.RequestStateCodec.now_ms`, `…RequestStateCodec.open` or
  `…RequestStateCodec.open_with` (a variable named `now_ms`, such as the time parameter of E01
  `open_authenticated_body`, is not covered); statements about
  opening use `open_at` with an explicit `now` (also in `formal/docs/STATUS.md`). Exception (human
  decision 2026-11-24): the spec theorems of the public `open`/`open_with` and their restatements,
  as worded in `formal/README.md`, "Trusted base".
- **Tests.** `codec::within_ttl_opens`, `codec::past_ttl_is_expired` (through `open`).

## Phase 2 externals (plan steps S26–S27)

The Phase 2 translation (plan step S21) added 26 external functions and 6 external types,
first as `opaque` placeholders that asserted nothing. S26/S27 (stage 1) replaced each by the
model below (plan Section 18); all are definitions, `structure`s or inductive types, and the only
new `opaque` constant is the carrier `ExtModel.SerdeJsonValue`. Sources are `rust-src` of the
pinned toolchain `nightly-2026-09-17` (read in
`~/.rustup/toolchains/nightly-2026-09-17-aarch64-apple-darwin/lib/rustlib/src/rust/library/`;
until the Aeneas upgrade of 2026-11-24, `nightly-2026-06-01`). The line numbers in the table
below are those of `nightly-2026-06-01`, except the `RangeInclusive::contains` row; the current
citations are in the docstrings of `formal/trusted/Rmcp/FunsExternal.lean` (see the note above
the Standard library table).
The model laws (plan Section 18, "Evidence" column): 43 statements, signed off by the spec owner on
2026-11-23, proved (`formal/proofs/Proofs/External/{String,Option,Std,IntParse,Net}.lean`) and
restated in `formal/specs/Specs/External.lean` (Phase 2 part; since 2026-11-24 in
`formal/proofs/Proofs/Internal/External.lean`). **The differential programs of plan
Section 18 were not built: stage 3 was dropped by human decision on 2026-11-23.** The
reproducible evidence for these models is the cited `core`/`alloc` source and (after stage 6)
the proved laws. The spot checks below are unrecorded scratch runs, with no committed harness or
command; they are not reproducible evidence. Phase 2 adds no Rust test to the SDK source (human
decision H3, plan Section 19; the test-only patch 02 adds `#[cfg(test)]` tests to the patched
copy only, S34); the existing upstream tests per target are mapped in "Phase 2
boundary cases: upstream-test map (S34)" below.

New trusted helper definitions (namespace `ExtModel`, in `formal/trusted/Rmcp/`, part of the
trust base like the models that use them): `IntErrorKind` (the six variants of
`core::num::IntErrorKind`), `decDigit?` (value of an ASCII decimal digit), `i64DigitLoop` (the
digit loop of `from_ascii_radix`, radix 10), `i64FromAscii` (sign handling and the loop),
`sliceEq` and `sliceEqSameLength` (element-wise slice equality through `PartialEq`), `beNat`
(big-endian value of a digit list in a base), `ipv4Nats` and `ipv6Nats` (the octets or segments
of an address as natural numbers). The opaque carrier `SerdeJsonValue` is listed above.

### Strings and `Arc`

| External | Model | Source (`rust-src`) |
|---|---|---|
| `str` `PartialEq::eq` | byte-list equality (any `Str`) | `core/src/str/traits.rs` 29–31; `core/src/slice/cmp.rs` 14–29 |
| `String` `Deref<str>` | the UTF-8 bytes (the model of `String::as_bytes`) | `alloc/src/string.rs` 2835–2837 |
| `Arc<T>` (type) | `{data : T}` (reference counts, pointer and allocator not modelled) | `alloc/src/sync.rs` 269–276, `ArcInner` 388–397 |
| `Arc` `Deref` | projection `data` | `alloc/src/sync.rs` 2443–2445 |
| `Arc` `PartialEq::eq` | `data == data` through `T`'s instance | `alloc/src/sync.rs` 3580–3582, 3529–3533 |

- **Stated exception.** For `T: Eq`, Rust's `Arc` equality is `ptr::eq(..) || **self ==
  **other` (`sync.rs` 3548–3552). The model has no pointers and always compares the values; the
  two agree whenever `T`'s equality is reflexive and does not fail; `Eq` asks for reflexivity
  (`core/src/cmp.rs` 280–289; `MarkerEq`, `alloc/src/rc.rs` 2615–2617); `str`, the only
  instance, has both.
- **Planned evidence.** Laws in `Proofs/External/String.lean` (stage 2); the Phase 1 string tests
  above (`String` models) cover `as_bytes`, which `Deref<str>` reuses.

### `Option`, `Result`, slices, ranges, `MaybeUninit`

| External | Model | Source (`rust-src`) |
|---|---|---|
| `Option::or_else` | `Some x ↦ Some x`, `None ↦ f()` via `FnOnce` | `core/src/option.rs` 1644–1655 |
| `Option` `PartialEq::eq` | case split, `Some l, Some r ↦ l == r` | `core/src/option.rs` 2440–2449 |
| `Result::ok` | `Ok x ↦ Some x`, `Err _ ↦ None` | `core/src/result.rs` 708–717 |
| `slice::first` | head or `None` | `core/src/slice/mod.rs` 155–157 |
| `slice::strip_suffix` | `as_slice`, `split_at(len − n)`, `tail == suffix` | `core/src/slice/mod.rs` 2719–2733 |
| `[T] == [U; N]` | `false` unless length `N`, else element-wise `ne` loop | `core/src/array/equality.rs` 48–53, 10–12, 143–145; `core/src/slice/mod.rs` 851–861 (`as_array`); `core/src/slice/cmp.rs` 125–140 |
| `SlicePattern::as_slice` for `[T; N]` | the same elements as a slice | `core/src/slice/mod.rs` 5678–5680 |
| `RangeInclusive::contains` | `start <= item`, then `item <= end` (`item < start` if exhausted, i.e. empty; changed in the Aeneas upgrade, human decision 2026-11-24; one fresh review of model and laws: model exact, one blocking finding (a dropped restatement) fixed; laws re-signed 2026-11-24; up to `nightly-2026-06-01`: `item < end`), short-circuit | `core/src/ops/range.rs` 539–545, 886–900, 1142–1157 (`nightly-2026-09-17`) |
| `MaybeUninit<T>` (type) | `uninit` or `value v` (the two union fields) | `core/src/mem/maybe_uninit.rs` 355–358 |

- **Stated exceptions.** The `BytewiseEq` specializations of slice and array equality
  (`slice/cmp.rs` 146–160, `array/equality.rs` 152–158) compare bytes instead of calling `ne`;
  for the types they apply to (`u8`, `u16` here) `ne` is the negation of byte equality and does
  not fail, so the result is the same. `MaybeUninit` is mentioned by no generated definition (it
  occurs in the LLBC, in the signature of `Box::new_uninit`); a partly initialised value is not
  modelled.
- **Spot check (2026-11-23; an unrecorded scratch run with no committed harness or command,
  not reproducible evidence; Lean `#eval` against `rustc +nightly-2026-06-01`, identical
  results):** `strip_suffix(&[13u8])` of `[1, 2, 13]`, `[1, 2]` and `[]`; `[u8] ==
  [u8; 2]` with equal and unequal lengths; `(64..=127).contains` at `127` (fresh, and exhausted
  by iteration in Rust / `exhausted = true` in Lean) and at `63`. **Run on `nightly-2026-06-01`
  only** (the toolchain before the Aeneas upgrade of 2026-11-24). Its exhausted case does not
  separate the old model (`item < end`) from the new one (`item < start`), and on
  `nightly-2026-09-17` iterating `64u8..=127` to the end leaves `128..=127` with
  `exhausted = false` (`core/src/iter/range.rs` about lines 1538–1546), so that Rust state is no
  longer an exhausted range.
- **Vectors separating the old and new `RangeInclusive::contains` model (2026-11-24, verified on
  `rustc +nightly-2026-09-17` by the reviewer of the changed model; Rust state as printed by
  `{:?}`, model `contains core.cmp.PartialOrdU8 …` on `⟨start, end, exhausted⟩`):**
  - `250u8..=255` iterated to the end → state `0..=255 (exhausted)`; `.contains(&3)` = `false`;
    model `⟨0, 255, true⟩` at `3` → `ok false` (the old model, `item < end`, gave `true`).
  - `(64u8..=127).nth(250)` → state `59..=127 (exhausted)`; `.contains(&100)` = `false`; model
    `⟨59, 127, true⟩` at `100` → `ok false` (the old model gave `true`).
- **Planned evidence.** Laws in `Proofs/External/Option.lean` (`Option`, `Result`) and
  `Proofs/External/Std.lean` (slices, ranges), stage 2.

### Integer parsing (`str::parse`, `i64::from_str`, `ParseIntError`)

- **Model.** `str::parse` calls the `FromStr` instance (`core/src/str/mod.rs` 2765–2767).
  `i64::from_str(src) = from_str_radix(src, 10)` (`core/src/num/mod.rs` 1626–1628) `=
  from_ascii_radix(src.as_bytes(), 10)` (1677–1679), transcribed as `ExtModel.i64FromAscii`
  and `ExtModel.i64DigitLoop` (lines 1756–1844): `""` is `Empty`; a lone `+` or `-` is
  `InvalidDigit`; one leading `+`/`-` sets the sign; each further byte must be `0`–`9`
  (`char::to_digit(10)`, `core/src/char/methods.rs` 402–424), else `InvalidDigit`; a value
  leaving `[-2^63, 2^63)` is `PosOverflow` (positive) or `NegOverflow` (negative), the first
  error from the left winning and a bad digit before an overflow at the same position (checked
  loop, 1815–1841; the unchecked loop for at most 15 digits, 1791–1814, cannot overflow).
  `ParseIntError` is `{kind}` (`core/src/num/error.rs` 74–76) and `IntErrorKind` has its six
  variants (93–129). Never panics (radix 10 passes the radix check).
- **Spot check (2026-11-23; an unrecorded scratch run with no committed harness or command,
  not reproducible evidence; the Lean models evaluated with `#eval` and the same inputs run
  through `str::parse::<i64>` compiled by `rustc +nightly-2026-06-01`; identical results):**
  `""` Empty; `"+"`, `"-"`, `"+-1"`, `"--1"`, `" 1"`, `"1 "`, `"٣"` InvalidDigit; `"007"` 7;
  `"-0"` 0; `i64::MAX`, `i64::MIN` accepted; one past each PosOverflow/NegOverflow;
  `"99999999999999999999a"` PosOverflow; `"1a99999999999999999999"` and
  `"922337203685477580a"` InvalidDigit. Two independent reviewers (S26/S27 review round 1) also
  ran scratch comparisons against `rustc +nightly-2026-06-01` with 0 mismatches over 200,026
  inputs, equally unrecorded.
- **Not built (stage 3 dropped, 2026-11-23).** Planned was a differential
  test against `i64::from_str` over a corpus (signs, empty, `+`/`-` alone, leading zeros, both
  bounds and one past each, non-ASCII digits, whitespace) plus 10^6 random strings over
  `[+\-0-9a ]`. The law `model = Defs.parseI64` (`Proofs/External/IntParse.lean`) was deferred
  until after plan step S24, which defines `Defs.parseI64`; it is now proved as
  `I64.Insts.CoreStrTraitsFromStrParseIntError.from_str_eq_parseI64` (signed off at S24, proved
  at incorporation, 2026-11-24).

### IP addresses (`Ipv4Addr`, `Ipv6Addr`)

| External | Model | Source (`core/src/net/ip_addr.rs`) |
|---|---|---|
| `Ipv4Addr` (type) | `{addrOctets : Array U8 4}` | 74–76 (`octets: [u8; 4]`) |
| `Ipv6Addr` (type) | `{addrSegments : Array U16 8}` (stated change of representation) | 168–170 (`octets: [u8; 16]`); `segments` 1495–1510 |
| `Ipv4Addr::octets` | the octets | 668–670 |
| `Ipv4Addr::is_unspecified` | big-endian value `= 0` | 728–730 |
| `Ipv4Addr::is_loopback` | `octets[0] == 127` | 750–752 |
| `Ipv4Addr::is_private` | `[10, ..]`, `[172, 16..=31, ..]`, `[192, 168, ..]` | 781–788 |
| `Ipv4Addr::is_link_local` | `[169, 254, ..]` | 809–811 |
| `Ipv4Addr::is_multicast` | `224 <= octets[0] <= 239` | 1010–1012 |
| `Ipv4Addr::is_broadcast` | big-endian value `= 0xffffffff` | 1032–1034, `BROADCAST` 652 |
| `From<u32> for Ipv4Addr` | big-endian bytes (`from_bits`, `to_be_bytes`) | 1288–1290, 608–610 |
| `Ipv6Addr::segments` | the segments | 1495–1510 |
| `Ipv6Addr::is_unspecified` | value `= 0` (`::`) | 1558–1560, `UNSPECIFIED` 1479 |
| `Ipv6Addr::is_loopback` | value `= 1` (`::1`) | 1582–1584, `LOCALHOST` 1462 |
| `Ipv6Addr::is_multicast` | `segments[0] & 0xff00 == 0xff00` | 1942–1944 |

- **Stated deviation.** Rust stores an `Ipv6Addr` as 16 octets; the model stores the 8 segments
  `segments()` computes from them (a bijection), as plan Section 18 specifies. The translated
  code reads an address only through the four `Ipv6Addr` functions above, so no result depends
  on the representation. The field names `addrOctets`/`addrSegments` avoid the generated names
  of the methods `octets`/`segments`.
- **Spot check (2026-11-23; an unrecorded scratch run with no committed harness or command,
  not reproducible evidence; Lean `#eval` against the same calls compiled by
  `rustc +nightly-2026-06-01`, identical results):** `From<u32>` of `0x7f000001` gives
  `[127, 0, 0, 1]`; the six IPv4 predicates on `127.0.0.1`, `0.0.0.0`, `255.255.255.255`,
  `10.0.0.1`, `172.16.0.1`, `172.32.0.1`, `192.168.1.1`, `169.254.1.1`, `224.0.0.1`,
  `239.0.0.0`, `240.0.0.0`; the three IPv6 predicates on `::1`, `::`, `ff02::1`, `feff::`,
  `::1:0`. Two independent reviewers (S26/S27 review round 1) also ran scratch comparisons
  against `rustc +nightly-2026-06-01` with 0 mismatches (IPv4: 100,586 addresses; IPv6: 100,011
  addresses), equally unrecorded.
- **Not built (stage 3 dropped, 2026-11-23).** Planned was: IPv4 exhaustive
  over all 2^32 addresses for every predicate, `octets` and `from`; IPv6 every listed prefix
  boundary plus 10^6 random addresses; a Cargo program on the pinned nightly and a compiled Lean
  executable in a separate Lake project, comparing per-function digests (plan Section 18, with
  its fallback to an exhaustive Lean proof if the runtime exceeds a few hours).

### Opaque value (`serde_json::Value`)

- **Model.** `def serde_json.value.Value := ExtModel.SerdeJsonValue`, an `opaque` type
  (`serde_json-1.0.154/src/value/mod.rs` 116–176, `pub enum Value`). The targets only move values
  (`ErrorData.data : Option Value`); no model creates, inspects or compares one. No evidence is
  needed beyond that observation (plan Section 18).

## Phase 2 boundary cases: upstream-test map (S34)

Plan step S34 (plan Sections 21 and 22; human decision H3): for each boundary case of plan
Section 22, the existing upstream Rust tests that exercise it on the target function, either
**direct** (the test calls the target) or **via caller** (the test calls a named caller whose
observed result is determined by the target's result on that input). The Lean proofs cover
every input; these tests are evidence that the translated configuration behaves as the
statements say on the boundary cases, not a proof. Phase 2 adds no Rust test to the SDK source
(H3), and the differential programs were dropped (plan Section 18, amendment). The cases that no
upstream test covered (**uncovered** upstream, 96) or covered only in part (**partial**, 8) are
covered by the test-only patch 02 (`formal/trusted/patches/02-phase2-tests.patch`, human
decision 2026-11-24, H3 follow-up; paragraph "Patch 02" below): the Status column names its test
(`s34_…`, a direct call of the target). **Partial**: only some targets of the row, or some of
the inputs, are exercised by upstream tests. **Equivalent input**: the test uses an input of the
same shape as the listed literal (named).

Paths are relative to `crates/rmcp/`; the number in parentheses is the line of the test function
in the repository's files (upstream `7caec76`; in the patched copy, `model.rs` lines after 19 are
2 higher). Lean regression checks (`decide`, kernel-checked when the module builds):
`Net` = `formal/proofs/Proofs/Defs/Net.lean` lines 187–296; `Sse` =
`formal/proofs/Proofs/Defs/Sse.lean` lines 272–416; `Methods` =
`formal/proofs/Proofs/Defs/Methods.lean` lines 194–262 (list contents only). No `Defs` regression
check evaluates M01–M14, T04 or T07/T08; `Defs.parseI64` (`formal/specs/Defs/IntParse.lean`
lines 80–89) names the M06 strings in its docstring only. The theorems are in
`formal/proofs/Proofs/Model/` and `formal/proofs/Proofs/Transport/`.

**Runs (2026-11-24).** Toolchain `nightly-2026-06-01` (`rustc 1.98.0-nightly (14210df0e
2026-05-31)`, `cargo 1.98.0-nightly (fbb61be30 2026-05-26)`), the pinned nightly of
`patched-tests.yml`; host `aarch64-apple-darwin` (CI: `x86_64-unknown-linux-gnu`). Run in a
scratch copy of `.llbc/work/` (patch 01 applied; its `Cargo.lock` as checked by
`scripts/aeneas-translate.sh --check-deps`), with a separate target directory and the default
`CARGO_HOME` (CI uses an isolated one). `F` is the translated feature list
`request-state,server,client,client-side-sse,transport-streamable-http-server,`
`transport-streamable-http-client,auth`; every command also passes `--locked
--no-default-features --config profile.dev.overflow-checks=true --config
profile.dev.debug-assertions=true`, as `patched-tests.yml` does.

| Command (in `crates/rmcp`) | Exit | Result |
|---|---|---|
| `cargo test --features "$F,macros" --lib` (the `patched-tests.yml` command) | 0 | 801 passed, 0 failed |
| `cargo test --features "$F,macros" --test test_completion --test test_sampling --test test_task --test test_client_initialization --test test_client_lifecycle_modes --test test_async_rw_max_line_length` | 0 | 12, 36, 8, 4, 16, 7 passed (in that order), 0 failed |
| `cargo test --features "$F,macros,transport-streamable-http-client-reqwest" --test test_custom_headers` | 0 | 39 passed, 0 failed |
| `cargo test --features "$F,macros,transport-streamable-http-client-reqwest" --lib clear_stream_response_pending` | 0 | 2 passed, 868 filtered out |

`patched-tests.yml` runs only the first command: the integration tests (`tests/*.rs`) are not
part of the CI evidence job. Tests marked † need `transport-streamable-http-client-reqwest`,
which is outside the translated configuration: all of `tests/test_custom_headers.rs`
(`required-features` in `Cargo.toml`) and the two `clear_stream_response_pending` tests
(`#[cfg(feature = ...)]`). The target functions themselves carry no `cfg` on that feature.

**Patch 02 (S34, 2026-11-24).** Test-only: it adds 34 `#[test]` functions named
`s34_<id>_<case>`, all inside `#[cfg(test)]` modules (at the end of the existing test modules of
`model.rs`, `model/task.rs`, `async_rw.rs`, `auth.rs` and `client_side_sse.rs`, and a new
`#[cfg(test)] mod phase2_boundary_tests` at the end of `tower.rs`); no non-test line, dependency
or `Cargo.toml` changes. Each test cites its plan Section 22 row and the theorem it mirrors; its
expected values are taken from the signed-off statements and their `Defs` (`Defs.parseI64`,
`Defs.Tower.defaultPort`, the `Defs.Methods` lists, the `Defs.Sse` model and checks, the
`Defs.Net` definitions and checks), not from running the code. The tests call the targets
directly, so they also check the limiter state after a call (T01–T03), which no caller exposes,
and need no feature outside the translated configuration plus `macros`. A test of a feature-gated
item carries the item's `cfg`: `s34_m06_numeric_string_value_boundary_strings` has
`#[cfg(any(feature = "client", feature = "server"))]` and the four `s34_m07_*` tests
`#[cfg(feature = "client")]`, as `numeric_string_value` and `matches_response_id` (`model.rs`
lines 321 and 329 at `7caec76`); the other tests call ungated items or sit in modules gated
already (`transport` and its `async_rw`, `auth`, `client_side_sse`, `tower` modules), so the
crate's tests also compile with `request-state` alone (the Phase 1 evidence command, which the
first version of the patch broke). The limiter tests build every start state field by field
(`s34_limiter`), never through `SseEventSizeLimiter::new`, which no signed-off statement
covers. `scripts/apply-patches.sh` applies it after patch 01 to the copy in `.llbc/work/` only
(file-name order, `patch -p1 -F 0`), so `patched-tests.yml` runs these tests; the SDK sources
stay byte-identical to upstream. Every hunk is at the end of its file, so no translated item
moves. As a test-only patch it is a process exception to VERIFICATION.md Section 4 (plan
Section 21, H3), to be recorded in `formal/docs/STATUS.md`, "Documents". No expected value
disagreed with the code.

Runs of patch 02 (2026-11-24; same toolchain and host as above; scratch directories, a separate
target directory; `F` as above):

| Command | Exit | Result |
|---|---|---|
| `RMCP_LLBC_DIR=<scratch>/llbcA scripts/apply-patches.sh` (fresh directory) | 0 | applied `01-request-state-wire.patch`, then `02-phase2-tests.patch` (`patch -F 0`; applied again by hand: no fuzz or offset message) |
| `RMCP_LLBC_DIR=<scratch>/llbcA scripts/aeneas-translate.sh --check-deps` | 0 | dependency checks passed; checked `Cargo.lock` |
| in `<scratch>/llbcA/work/crates/rmcp`, with `CARGO_HOME=<scratch>/llbcA/cargo-home` (isolated, as in CI): `cargo test --locked --no-default-features --features "$F,macros" --lib --config profile.dev.overflow-checks=true --config profile.dev.debug-assertions=true` (the `patched-tests.yml` command) | 0 | 835 passed, 0 failed (the 801 above plus the 34 `s34_*`) |
| same directory and flags, `--features request-state` (the Phase 1 evidence configuration) | 0 | 303 passed, 0 failed (10 `s34_*`: M01–M05, M08, M09–M12; M06/M07 and the transport tests are compiled out) |
| same directory and flags, `--features request-state,server,macros` (M06 compiled, M07 not; `request-state,server` without `macros` fails to compile upstream tests in `tool_traits.rs`, independent of patch 02) | 0 | 399 passed, 0 failed (17 `s34_*`, incl. `s34_m06_numeric_string_value_boundary_strings`, no `s34_m07_*`) |
| `rustfmt --check` (`nightly-2026-06-01`, the repository's `rustfmt.toml`) on the six patched files | 0 | no difference |
| mutation: `64..=127` → `64..=126` in `is_disallowed_metadata_ipv4` (scratch copy, then restored), the `patched-tests.yml` command filtered to `s34_` | 101, then 0 | `s34_a02_range_boundaries` fails (`100.127.255.255 must be blocked`), 33 passed; after restoring, 34 passed |
| `DYLD_FALLBACK_LIBRARY_PATH=/usr/lib RMCP_LLBC_DIR=<scratch>/llbcB RMCP_TRANSLATION_DEST=<scratch>/trans scripts/aeneas-translate.sh`, then `diff -r <scratch>/trans formal/translation` | 0, 0 | the translation with both patches is byte-identical to `formal/translation/` (`Funs.lean`, `Types.lean`, the two `External` templates, `translation.json`); `Funs.lean` matches its pin |
| `DYLD_FALLBACK_LIBRARY_PATH=/usr/lib scripts/check-original-linkage.sh <scratch>/link` | 0 | 41, 27, 30, 9 blocks identical |

### M01–M05 (`JsonRpcMessage::into_*`, `model.rs` 819–849)

The five functions have no caller in the crate, so only direct calls count.

| Case | Upstream test(s) | How | Status |
|---|---|---|---|
| `Request` | `src/model.rs` `tests::test_initial_request_response_serde` (5803); `tests/test_client_initialization.rs` `test_client_init_handles_jsonrpc_error` (118) | M01 direct: `Some (request, Number 1)` (5803); `Some` on the received `initialize` request (118). M02–M05 on a `Request` (`None`): no upstream test | partial upstream (M01 pass); M01–M05 patch 02 `s34_m01_m05_request`: pass |
| `Response` | `tests::test_initial_request_response_serde` (5803) | M02 direct: `Some (result, Number 1)`. M01, M03–M05 on a `Response`: no upstream test | partial upstream (M02 pass); M01–M05 patch 02 `s34_m01_m05_response`: pass |
| `Notification` | none | — | patch 02 `s34_m01_m05_notification`: pass |
| `Error`, `id = Some` | none | the client matches `Error` itself (`service/client.rs` 207–220), not through M04/M05 | patch 02 `s34_m01_m05_error_with_id`: pass |
| `Error`, `id = None` | none | `tests/test_client_lifecycle_modes.rs` `auto_startup_falls_back_for_absent_error_id` (633) sends one, but no target is called on it | patch 02 `s34_m01_m05_error_without_id`: pass |

### M06/M07 (`NumberOrString::numeric_string_value`, `matches_response_id`, `model.rs` 322–338)

Callers: M07 in `expect_response` (`service/client.rs` 183–220; a mismatch fails `serve` with
`ConflictInitResponseId`); M06 in M07, in `remove_pending_request` (`service.rs` 485–494) and in
`clear_stream_response_pending` (`streamable_http_client.rs` 827–837). The first request id of a
fresh client is `Number 0` (`AtomicU32Provider`, `service.rs` 497–507).

| Case | Upstream test(s) | How | Status |
|---|---|---|---|
| M06 `"0"` | `tests/test_client_initialization.rs` `client_initialization_accepts_stringified_numeric_response_id` (27); `tests/test_client_lifecycle_modes.rs` `discover_startup_accepts_stringified_numeric_response_id` (25) | via caller M07 → `expect_response`: `Number 0` matches `String "0"` only if M06 gives `some 0` | pass |
| M06 `"+0"`, `"-0"`, `"007"`, `""`, `"+"`, `"-"`, `" 1"`, `"1 "`, `"9223372036854775807"`, `"9223372036854775808"`, `"-9223372036854775808"`, `"-9223372036854775809"`, `"١"` (13 cases) | none | patch 02 calls M06 directly on all 14 strings (with `"0"`) and on a number | patch 02 `s34_m06_numeric_string_value_boundary_strings`: pass (13) |
| M07 `Number 1` vs `String "1"` | the two tests above | via caller `expect_response`, equivalent input `Number 0` vs `String "0"` (`true`); patch 02 `s34_m07_number_matches_numeric_string` calls M07 on the literal input | pass |
| M07 `String "1"` vs `Number 1` | none | client request ids are numbers; no upstream test sends a string request id and a numeric response | patch 02 `s34_m07_string_does_not_match_number`: pass |
| M07 equal strings | none | — | patch 02 `s34_m07_equal_strings_match`: pass |
| M07 unequal strings | none | patch 02 also `String "1"` vs `String "01"` (`false`) | patch 02 `s34_m07_unequal_strings_do_not_match`: pass |

Not in the Section 22 list, also exercised: M06 `"1"` → `some 1` via `remove_pending_request`
(`tests/test_client_initialization.rs` `client_correlates_stringified_numeric_response_id`
(68)) and via `clear_stream_response_pending` († `src/transport/streamable_http_client.rs`
`tests::clear_stream_response_pending_accepts_stringified_numeric_id` (2834),
`tests::clear_stream_response_pending_prefers_exact_string_id` (2853)); M07 unequal numbers
`Number 0` vs `Number 999` → `false` (`tests/test_client_lifecycle_modes.rs`
`auto_startup_surfaces_uncorrelated_error_id` (592)).

### M08 (`TaskStatus::is_terminal`, `model/task.rs` 38)

| Case | Upstream test(s) | How | Status |
|---|---|---|---|
| `Working` | `src/task_manager.rs` `tests::cancel_is_cooperative_and_lets_the_operation_clean_up` (672) | direct: `!is_terminal()` right after `cancel_task` (line 691); the task is still `Working` (single-threaded test runtime, no pending input) | pass |
| `InputRequired` | none | `tests::cancel_wakes_parked_input_requests` (715) reaches `InputRequired` but compares the status, not `is_terminal`; patch 02 checks all five statuses | patch 02 `s34_m08_is_terminal_each_status`: pass |
| `Completed` | `tests::cancel_is_cooperative_and_lets_the_operation_clean_up` (672); `tests/test_task.rs` `task_lifecycle_create_poll_complete` (128) | direct: the poll loop stops at `is_terminal()` and the status is `Completed` | pass |
| `Failed` | `tests::post_cancel_unrelated_error_settles_as_failed` (634) | direct, as above, status `Failed` | pass |
| `Cancelled` | `tests::cancel_settles_to_cancelled_when_operation_honors_it` (606); `tests/test_task.rs` `task_cancel_acknowledged` (184) | direct, as above, status `Cancelled` | pass |

### M09–M12 (`SamplingContent::{into_vec, is_empty, len, first}`, `model.rs` 2926–2963)

| Case | Upstream test(s) | How | Status |
|---|---|---|---|
| `Single` | `tests/test_sampling.rs` `test_backward_compat_sampling_message_with_image` (518), `test_content_to_sampling_content_conversion` (571), `test_sampling_message_with_tool_use` (408), `test_backward_compat_sampling_message_deserialization` (500) | M11 direct: `len() = 1` (518, 571); M12 direct: `first()` is the item (408, 500, 571). M09 and M10 are called by no upstream test | partial upstream (M11, M12 pass); M09–M12 patch 02 `s34_m09_m12_single`: pass |
| `Multiple []` | none | — | patch 02 `s34_m09_m12_multiple_empty`: pass |
| `Multiple [x]` | none | — | patch 02 `s34_m09_m12_multiple_one`: pass |
| `Multiple [x, y]` | none | `test_validate_rejects_mixed_content_with_tool_result` (639) builds one but reaches only `iter` (not a target) | patch 02 `s34_m09_m12_multiple_two`: pass |

### M13/M14 (`Reference::{as_prompt_name, as_resource_uri}`, `model.rs` 3741–3755)

| Case | Upstream test(s) | How | Status |
|---|---|---|---|
| `Prompt` | `tests/test_completion.rs` `test_reference_convenience_methods` (126) | direct: M13 `Some "test_prompt"`, M14 `None` | pass |
| `Resource` | same test | direct: M14 `Some "file://path/to/resource"`, M13 `None` | pass |

### T01/T02 (`SseEventSizeLimiter::{check_limit, finish_line}`, `client_side_sse.rs` 75–96)

All tests below are in `src/transport/common/client_side_sse.rs` `tests` and reach the targets via
caller: `bounded_sse_stream` (144) → `BoundedSseByteStream::poll_next` (115–141), which calls
`observe` once per chunk and turns its `Err` into `EventTooLarge` and its `Ok` into the
unchanged chunk; `observe` calls `finish_line` at a line end and `check_limit` after every other
byte. The test sees only the result, not the limiter's state.

| Case | Upstream test(s) | How | Status |
|---|---|---|---|
| sum exactly at `max` | `bounded_sse_stream_passes_event_at_exact_limit` (630); `bounded_sse_stream_discards_completed_comment_lines_from_limit` (673) | via caller: `finish_line` reaches `retained = 9 = max` (630); `check_limit` at `0 + 6 = 6 = max` (673); both `Ok` | pass |
| one above `max` | `bounded_sse_stream_rejects_unterminated_event_over_limit` (597); `bounded_sse_stream_counts_multiline_data_join_newlines` (693); `bounded_sse_stream_comments_do_not_reset_accumulated_data` (683) | via caller: `check_limit` `Err` at `17 > 16`, `10 + 9 > 18`, `8 + 7 > 14`. All three fail in `check_limit` after an ordinary byte; no test makes `finish_line` itself fail | pass |
| saturating past `max` | none | needs sizes near `usize::MAX`; patch 02 builds limiter states directly: T01 and T02 at and past `usize::MAX`, the state after `finish_line`, T03 on a line of `usize::MAX` bytes | patch 02 `s34_t01_t02_saturating_past_max`: pass; `Sse`: `satAdd usizeMax64 usizeMax64 1`, `withinLimit` at the cap, all histories with cap 2 |
| empty line | `bounded_sse_stream_resets_limit_after_event_terminator` (613); `skipped_events_do_not_grow_the_stack` (763) | via caller: the second event passes only because the empty line reset `retained` (613); 50,000 events under a 1024-byte limit (763) | pass |
| comment line | `bounded_sse_stream_discards_completed_comment_lines_from_limit` (673); `bounded_sse_stream_comments_do_not_reset_accumulated_data` (683) | via caller: comment lines add nothing (else `7 > 6`, 673) and keep `retained` (683) | pass |
| non-comment line | `bounded_sse_stream_counts_multiline_data_join_newlines` (693); `bounded_sse_stream_passes_event_at_exact_limit` (630) | via caller: `line_size + 1` is added (the error at 693 needs the joining newline) | pass |

### T03/C01/C02 (`SseEventSizeLimiter::observe`, `client_side_sse.rs` 48–73)

Via caller as for T01/T02; the inputs of these eight tests are also replayed in Lean (`Sse`,
lines 299–323).

| Case | Upstream test(s) | How | Status |
|---|---|---|---|
| LF | every test of T01/T02 | via caller | pass |
| CR (a CR not followed by LF) | none | every CR in the upstream tests is followed by LF; patch 02 checks verdict and state on the three `Sse` inputs | patch 02 `s34_t03_cr_line_ends`: pass; `Sse`: `"ab\r"`, `"ab\r\r"`, `"a\rb\n"` |
| CRLF | `bounded_sse_stream_resets_limit_after_event_terminator` (613) | via caller: `"\r\n"` inside the second chunk | pass |
| CRLF split across chunks (C01) | `bounded_sse_stream_handles_crlf_split_across_chunks` (658); `bounded_sse_stream_resets_limit_after_event_terminator` (613) | via caller, result only: both inputs give `Ok` whether or not the split LF counts as a second line end; the state that distinguishes them is pinned by `Sse` (`observeChunks (init 64) ["data: hello\r", "\n"]`), checked directly by patch 02 (the same state as for the unsplit chunk) | pass (result only); state: patch 02 `s34_c01_crlf_split_across_chunks_state`: pass |
| comment that resets nothing | `bounded_sse_stream_comments_do_not_reset_accumulated_data` (683) | via caller | pass |
| blank line resetting | `bounded_sse_stream_resets_limit_after_event_terminator` (613); `skipped_events_do_not_grow_the_stack` (763) | via caller | pass |
| event exactly at the limit | `bounded_sse_stream_passes_event_at_exact_limit` (630) | via caller | pass |
| oversize split across many chunks (C01) | `bounded_sse_stream_rejects_oversize_split_across_many_chunks` (640); `bounded_sse_stream_rejects_unterminated_event_over_limit` (597) | via caller: 20 chunks `"data: x"` under 32; 2 chunks under 16 | pass |
| empty chunk | none | no upstream test yields an empty `Bytes`; patch 02 calls `observe` on an empty chunk from four states, one of them over the bound | patch 02 `s34_t03_empty_chunk`: pass; `Sse`: `observe usizeMax64 st [] = ⟨true, st⟩` |
| error at a CR byte (state afterwards) | none | no test fails at a CR; after an `Err`, `poll_next` ends the stream, so the state is not observable through the caller; patch 02 checks it directly, and that an error stops the fold (`Sse`: `(init 1) "ab\n\n"`) | patch 02 `s34_t03_error_at_cr_state`: pass; `Sse`: `observe usizeMax64 (init 2) (bytesOf "ab\r")` |

C02 (the bound is kept) is a statement about the state and is not observable through the caller;
patch 02 checks concrete states after `Ok` calls (all within the bound) but has no test of C02
as such.

### T04 (`async_rw::without_carriage_return`, `async_rw.rs` 385)

Callers: `JsonRpcMessageCodec::decode` (560) and `decode_eof` (596), `AsyncRwTransport::receive`
(302).

| Case | Upstream test(s) | How | Status |
|---|---|---|---|
| empty | none | `receive` skips an empty line after T04 (305–308), but no test sends one; `test_decode`'s trailing empty line is never decoded (the test reads 10 items) | patch 02 `s34_t04_without_carriage_return`: pass |
| `"\r"` | none | — | patch 02 `s34_t04_without_carriage_return`: pass |
| `"a\r"` | none | no upstream test input contains a CR | patch 02 `s34_t04_without_carriage_return`: pass |
| `"a\r\r"` | none | — | patch 02 `s34_t04_without_carriage_return`: pass |
| `"a"` (no CR) | `src/transport/async_rw.rs` `test::test_decode` (641), `test::receive_ignores_parse_error` (836); `tests/test_async_rw_max_line_length.rs` `message_within_the_limit_is_delivered` (99) | via caller: the line reaches the JSON parser unchanged; dropping its last byte would make it unparsable; patch 02 `s34_t04_without_carriage_return` also calls T04 on `"a"` | pass |

### T05/T06/C05 (`is_standard_notification`, `is_standard_method`, `async_rw.rs` 396–433)

Tests in `src/transport/async_rw.rs` `test`. Caller: `should_ignore_notification` (437–457).

| Case | Upstream test(s) | How | Status |
|---|---|---|---|
| every listed name | `test_standard_notification_check` (717); `test_2026_07_28_standard_method_check` (744); `test_current_standard_notification_is_not_ignored` (755) | T05 direct on all 10 notification names (`true`); T06 direct on 3 of the 18 request names (`elicitation/create`, `server/discover`, `subscriptions/listen`); T06 (C05) via caller on 1 of the 10 notification names (`notifications/subscriptions/acknowledged`: `should_ignore_notification` returns `false` only if T06 is `true`). T06 on the other 15 request and 9 notification names: no upstream test. Patch 02: T05, T06 and C05 on all 22 + 12 core names of `Defs.Methods` (`false` for the six of `codeOmits`; 18 + 10 accepted) | partial upstream; patch 02 `s34_t05_t06_every_listed_name`: pass |
| prefix of a name | none | — | patch 02 `s34_t05_t06_prefix_and_suffix`: pass |
| suffix of a name | none | — | patch 02 `s34_t05_t06_prefix_and_suffix`: pass |
| case variant | none | — | patch 02 `s34_t05_t06_case_variant`: pass |
| `notifications/unknown` | `test_standard_notification_check` (717) | T05 direct, equivalent inputs `notifications/stderr`, `notifications/custom`, `notifications/debug` (`false`); T06 on an unknown notification is not determined: `test_unknown_notification_is_ignored` (766) returns `true` whatever T06 gives | partial upstream (T05 pass); T05 and T06 patch 02 `s34_t05_t06_notifications_unknown`: pass |
| empty | none | — | patch 02 `s34_t05_t06_empty`: pass |

`Methods` pins the list contents (and that the code lists are the core union minus `codeOmits`);
it does not evaluate T05/T06 on any input.

### T07/T08 (`tower::{default_port, AllowedPort::matches}`, `tower.rs` 1146–1171)

All tests are † in `tests/test_custom_headers.rs` `origin_validation` and reach the targets via
caller: `StreamableHttpService::handle` → `validate_dns_rebinding_headers` (1340) →
`validate_origin_header` (1357) → `origin_is_allowed` (1210), which calls T08 when scheme and
host are equal; the test sees `200` or `403`. `parse_origin_value` (1127) lowercases the scheme
before T07/T08.

| Case | Upstream test(s) | How | Status |
|---|---|---|---|
| `"http"` | `explicit_http_default_port_allows_port_less_origin` (1325) | via caller: `Exact 80`, port `None`: allowed only if T07 `"http"` = `some 80` | pass † |
| `"https"` | `explicit_https_default_port_allows_port_less_origin` (1316) | via caller: `Exact 443`, port `None`: needs `some 443` | pass † |
| `"HTTP"` | none | unreachable through the callers (lowercased) | patch 02 `s34_t07_default_port_schemes`: pass |
| `"ftp"` | none | no upstream test uses a scheme other than `http`/`https` | patch 02 `s34_t07_default_port_schemes`: pass |
| `Any` | `wildcard_port_allows_non_default_origin_port` (1370); `wildcard_port_allows_port_less_origin` (1379) | via caller: `true` with port `Some 8443` and `None` | pass † |
| `Unspecified` | `omitted_configured_port_allows_any_origin_port` (1361) | via caller: `true` with port `Some 8443` | pass † |
| `Exact 443` with `None` and `https` | `explicit_https_default_port_allows_port_less_origin` (1316) | via caller: `true` | pass † |
| `Exact 80` with `Some 8080` | `explicit_default_port_forbids_non_default_origin_port` (1343) | via caller, equivalent input `Exact 443` with `Some 8443` and `https` (`false`: an explicit port ignores the scheme default) | pass † |

Patch 02 also calls T07/T08 directly in the translated configuration (no †): `"http"` and
`"https"` (`s34_t07_default_port_schemes`), `Any` and `Unspecified` on every scheme and port tried
(`s34_t08_any_and_unspecified_match_everything`), `Exact 443` with `None` and `https`
(`s34_t08_exact_443_none_https`), and the literal `Exact 80` with `Some 8080`
(`s34_t08_exact_80_some_8080`); all pass.

Also exercised: `Exact 8443` with `None` → `false` (1352); `Exact 443` with `Some 443` → `true`
(1334); `Exact 8080` with `Some 8080` → `true` (`allowlisted_origin_is_allowed`, 1194).

### A01 (`AuthorizationManager::embedded_ipv4`, `auth.rs` 1359)

Tests: `src/transport/auth/metadata_resolver.rs` `tests::classifies_addresses` (294), via caller
`AddressClass::of` (`metadata_resolver.rs` 42–75): an IPv6 address is replaced by A01's IPv4
address when there is one; a class other than `Public` on the IPv6 path needs `::1`, `fc00::/7`
or a blocked prefix, so the class determines A01 where noted.

| Case | Upstream test(s) | How | Status |
|---|---|---|---|
| `::ffff:a.b.c.d` | `classifies_addresses` (294); `src/transport/auth.rs` `tests::metadata_url_checks_bracketed_ipv6_literals` (6817) | via caller: `::ffff:127.0.0.1` → `Loopback`, `::ffff:169.254.169.254` → `Blocked` (each needs `some`); 6817 through `is_allowed_metadata_url` → A03 → A01 | pass |
| `64:ff9b::a.b.c.d` | `classifies_addresses` (294) | via caller: `64:ff9b::a9fe:a9fe` → `Blocked`, `64:ff9b::a00:9` → `Private` (need `some`); `64:ff9b::5db8:d822` → `Public` | pass |
| `::a.b.c.d` | `classifies_addresses` (294) | via caller: `::169.254.169.254` → `Blocked` (needs `some`) | pass |
| `::` | none | — | patch 02 `s34_a01_embedded_ipv4`: pass; `Net`: `embeddedIpv4 (ipv6 [0, …, 0]) = none` |
| `::1` | `classifies_addresses` (294) | via caller: `::1` → `Loopback`; `some 0.0.0.1` would give `Blocked` | pass |
| `2002:abcd:ef01::` | `classifies_addresses` (294) | via caller, equivalent inputs: `2002:7f00:1::` → `Loopback` (needs `some 127.0.0.1` from segments `b`, `c`), `2002:a9fe:a9fe::` → `Blocked` | pass |
| `64:ff9b:1::1` (not embedded) | none | `64:ff9b:1::a9fe:a9fe` → `Blocked` (294) holds whether A01 gives `none` or `some 169.254.169.254`, so it does not determine A01 | patch 02 `s34_a01_embedded_ipv4`: pass; `Net`: `embeddedIpv4 (ipv6 [0x64, 0xff9b, 1, 0, 0, 0, 0, 1]) = none` |

Patch 02 `s34_a01_embedded_ipv4` calls A01 directly on 15 addresses of `Net`'s A01 checks (the
seven cases above, `::2`, the IPv4-translated `::ffff:0:a00:1`, a Teredo address, and the five
addresses next to the four embedding prefixes); all pass.

### A02 (`AuthorizationManager::is_disallowed_metadata_ipv4`, `auth.rs` 1343)

Section 22 asks for the first and last address of each range and the addresses just outside it
(19 inside, 18 outside, as enumerated by `Net`'s two A02 lists), plus a public address: 38 cases.
Via caller `AddressClass::of` (`Public` iff A02 is `false`) and `is_allowed_metadata_url`.
Tested addresses, all in `classifies_addresses` (294), `ip_literal_urls_follow_the_policy` (377)
and `src/transport/auth.rs` `tests::metadata_url_allows_private_literals_only_when_opted_in`
(6840): `0.0.0.0`, `93.184.216.34`, and the interior addresses `10.0.0.9`, `10.0.0.1`,
`127.0.0.1`, `127.0.0.2`, `192.168.1.1`, `100.64.0.1`, `169.254.169.254`.

| Case | Upstream test(s) | How | Status |
|---|---|---|---|
| `0.0.0.0` (first of `0/8`, and the single address `0.0.0.0`) | `classifies_addresses` (294) | via caller: `Blocked` | pass |
| a public address | `classifies_addresses` (294) | via caller: `93.184.216.34` → `Public` | pass |
| `10/8`: `10.0.0.0`, `10.255.255.255`; outside `9.255.255.255`, `11.0.0.0` | none (interior `10.0.0.1`, `10.0.0.9` only) | — | patch 02 `s34_a02_range_boundaries`: pass (4) |
| `172.16/12`: `172.16.0.0`, `172.31.255.255`; `172.15.255.255`, `172.32.0.0` | none (no address in the range) | — | patch 02 `s34_a02_range_boundaries`: pass (4) |
| `192.168/16`: `192.168.0.0`, `192.168.255.255`; `192.167.255.255`, `192.169.0.0` | none (interior `192.168.1.1`) | — | patch 02 `s34_a02_range_boundaries`: pass (4) |
| `127/8`: `127.0.0.0`, `127.255.255.255`; `126.255.255.255`, `128.0.0.0` | none (interior `127.0.0.1`, `127.0.0.2`) | — | patch 02 `s34_a02_range_boundaries`: pass (4) |
| `169.254/16`: `169.254.0.0`, `169.254.255.255`; `169.253.255.255`, `169.255.0.0` | none (interior `169.254.169.254`) | — | patch 02 `s34_a02_range_boundaries`: pass (4) |
| `255.255.255.255`; outside `255.255.255.254` | none | — | patch 02 `s34_a02_range_boundaries`: pass (2) |
| `224/4`: `224.0.0.0`, `239.255.255.255`; `223.255.255.255`, `240.0.0.0` | none | — | patch 02 `s34_a02_range_boundaries`: pass (4) |
| `0/8`: last `0.255.255.255`; outside `1.0.0.0` | none | — | patch 02 `s34_a02_range_boundaries`: pass (2) |
| `100.64/10`: `100.64.0.0`, `100.127.255.255`; `100.63.255.255`, `100.128.0.0` | none (interior `100.64.0.1`) | — | patch 02 `s34_a02_range_boundaries`: pass (4) |
| `198.18/15`: `198.18.0.0`, `198.19.255.255`; `198.17.255.255`, `198.20.0.0` | none | — | patch 02 `s34_a02_range_boundaries`: pass (4) |

Every A02 case uncovered upstream is evaluated by `Net` (A02 lists, lines 219–232) and, with the
same two lists (19 inside; 18 outside plus the public `8.8.8.8`), by patch 02
`s34_a02_range_boundaries` (direct; `240.0.0.0` is not blocked: the bug recorded under H8).

### A03/C04 (`AuthorizationManager::is_disallowed_metadata_ipv6`, `auth.rs` 1370)

Callers: `is_allowed_metadata_url` (`auth.rs` 1412) through `is_disallowed_metadata_host`, and
`AddressClass::of` on its IPv6 path, which it takes only when A01 gives `none`: for an address
that embeds IPv4, `AddressClass::of` calls A01 and A02 directly and never A03. The prefix
boundaries are the 12 inside and 10 outside addresses of `Net`'s two A03 lists (lines 240–263):
22 cases, plus 4 embedded forms and a public address: 27 cases.

| Case | Upstream test(s) | How | Status |
|---|---|---|---|
| `::1` | `classifies_addresses` (294); `tests::metadata_url_checks_bracketed_ipv6_literals` (6817) | via caller: `Loopback`; `[::1]` rejected for a public base | pass |
| `::` | none | — | patch 02 `s34_a03_prefix_boundaries`: pass |
| `ff00::/8`: `ff00::`, `ffff:…:ffff`; outside `feff:ffff:…:ffff` | none (no multicast IPv6 in any test) | — | patch 02 `s34_a03_prefix_boundaries`: pass (3) |
| `fe80::/10`: `fe80::`, `febf:ffff:…:ffff`; outside `fe7f:ffff:…:ffff`, `fec0::` | none (interior `fe80::1`, 294, 6817) | — | patch 02 `s34_a03_prefix_boundaries`: pass (4) |
| `fc00::/7`: `fc00::`, `fdff:ffff:…:ffff`; outside `fbff:ffff:…:ffff`, `fe00::` | none (interior `fd00::1`, 294) | — | patch 02 `s34_a03_prefix_boundaries`: pass (4) |
| `2001::/32`: `2001::`, `2001:0:ffff:…:ffff`; outside `2000:ffff:…:ffff`, `2001:1::` | none (interior `2001:0:4136:e378::1`, 294) | — | patch 02 `s34_a03_prefix_boundaries`: pass (4) |
| `64:ff9b:1::/48`: `64:ff9b:1::`, `64:ff9b:1:ffff:ffff:ffff:808:808`; outside `64:ff9b::1:0:0`, `64:ff9b:2::`, `64:ff9b:0:ffff:ffff:ffff:ffff:ffff` | none (interior `64:ff9b:1::a9fe:a9fe`, 294) | — | patch 02 `s34_a03_prefix_boundaries`: pass (5) |
| embedded blocked IPv4, IPv4-mapped | `tests::metadata_url_checks_bracketed_ipv6_literals` (6817) | via caller `is_allowed_metadata_url`: `[::ffff:127.0.0.1]` rejected only if A03 is `true` (C04: equals A02 of `127.0.0.1`) | pass |
| embedded blocked IPv4, NAT64 | `classifies_addresses` (294) | `64:ff9b::a9fe:a9fe` → `Blocked` exercises A01 and A02 (the right-hand side of C04), not A03 | partial upstream; A03 and C04 patch 02 `s34_a03_c04_embedded_forms`: pass |
| embedded blocked IPv4, IPv4-compatible | `classifies_addresses` (294) | `::169.254.169.254`, as above | partial upstream; A03 and C04 patch 02 `s34_a03_c04_embedded_forms`: pass |
| embedded blocked IPv4, 6to4 | `classifies_addresses` (294) | `2002:a9fe:a9fe::`, as above | partial upstream; A03 and C04 patch 02 `s34_a03_c04_embedded_forms`: pass |
| a public IPv6 address | `classifies_addresses` (294) | via caller: `2606:4700::1111` → `Public` (A01 `none`, A03 `false`) | pass |

Every A03/C04 case uncovered upstream is evaluated by `Net` (A03/C04 lists, lines 240–275).
Patch 02 calls A03 directly on the 12 inside and 11 outside addresses of `Net`'s boundary lists
(`s34_a03_prefix_boundaries`, with the public `2606:4700::1111`) and on 8 blocked and 4 public
embedded forms (`s34_a03_c04_embedded_forms`: `Net`'s two embedded-form lists plus
169.254.169.254 in the NAT64, IPv4-compatible and 6to4 forms of the partial rows), where it also
checks C04 (A03 equals A02 of A01's address) on all 12.

### Summary

141 cases. Upstream tests: 6 pass directly, 31 pass via a caller (3 of them with an equivalent
input: M07 `Number 0`/`String "0"`, T08 `Exact 443`/`Some 8443`, A01 `2002:7f00:1::`), 8
partial, 96 uncovered. Patch 02 (34 tests, direct calls) covers the 96 uncovered cases and the
missing parts of the 8 partial ones (M01–M05 3 + 2 partial, M06/M07 16, M08 1, M09–M12 3 + 1
partial, T01/T02 1, T03/C01/C02 3, T04 4, T05/T06/C05 4 + 2 partial, T07/T08 2, A01 2, A02 36,
A03/C04 21 + 3 partial), so no Section 22 case is left uncovered. No test failed and no expected
value (taken from the statements and `Defs`) disagreed with the code. Before patch 02, the
uncovered cases with no Lean regression check either (only the theorems) were those of M01–M05,
M06/M07, M08 (`InputRequired`), M09–M12, T04, T05/T06/C05 and T07/T08; the uncovered T01–T03,
A01, A02 and A03 cases are also evaluated by `Sse` or `Net`. The tests marked † still need
`transport-streamable-http-client-reqwest`; patch 02 covers the T07/T08 cases directly without it.

## Spec statements and proofs

Phase 1: the facts later proofs needed (72 statements, success and failure cases) are proved in
`formal/proofs/Proofs/External/` (`Base64.lean`, `String.lean`, `Prim.lean`, `Std.lean`);
`formal/specs/Specs/External.lean` restates them as theorems `Theorems.External.*` and checks
their axioms with `#print axioms` (each at most `propext`, `Classical.choice`, `Quot.sound`).
Their draft file (`formal/specs/Drafts/External.lean` at the time) was never committed: the
statements entered git already incorporated, in commit `af41799` (`git show
af41799:formal/specs/Specs/External.lean`).

Phase 2: 43 statements, drafted by an AI agent (Claude Code `mcp-spec`, `claude-opus-5-5`), reviewed
(round 1: two agents, no blocking finding), signed off by the spec owner on 2026-11-23, proved by
separate `mcp-lean` agents and restated in `formal/specs/Specs/External.lean`; the draft file
(uncommitted) was removed at incorporation. Each law depends on at most `propext`,
`Classical.choice` and `Quot.sound`.
