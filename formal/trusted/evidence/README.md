# Evidence for the external models (plan steps S08–S09)

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

This follows the human decision of 2026-11-23 to convert every placeholder axiom into a
definition (plan Section 4). Because there is no axiom, the consistency models of the earlier
design (`formal/proofs/Proofs/Consistency/`) are unnecessary: a definition cannot prove `False`, and
`trusted/axioms.lock` stays empty. The Base64 laws that the plan expected as axioms are theorems
(`formal/proofs/Proofs/External/Base64.lean`). What remains to be trusted about each model is
that it describes the Rust function; the source each one encodes is cited below (and in its
docstring), and the Rust tests that exercise it are listed. The tests catch a mismatched model;
they are not a proof. All tests named here are in the crate's own test modules and run with
`cargo test -p rmcp --no-default-features --features request-state --lib model::request_state`.

Source paths: `rust-src` is
`library/` of the pinned toolchain `nightly-2026-06-01`; crate paths are in
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

| External | Model | Source (`rust-src`) | Tests |
|---|---|---|---|
| `Borrow::borrow` (blanket) | identity | `core/src/borrow.rs` 214–216 | through `HashMap::get` below |
| `Option::ok_or` | `Some v ↦ Ok v`, `None ↦ Err e` | `core/src/option.rs` 1334–1339 | `codec::non_base64_sections_are_invalid_encoding` |
| `Option` `Default` | `None` | `core/src/option.rs` 2313–2315 | (non-target) |
| `Result::is_err` | `true` iff `Err` | `core/src/result.rs` 646–648 | `codec::maximum_length_kid_roundtrips_and_oversized_wire_kid_is_rejected` |
| `Result::map_err` | `Err e ↦ Err (op e)` via `FnOnce` | `core/src/result.rs` 962–970 | `codec::parser_rejects_invalid_tokens_and_unavailable_keys` (non-UTF-8 kid) |
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
| `Vec::is_empty` | `len == 0` | `alloc/src/vec/mod.rs` 3085–3087 | `codec::pinned_tokens_and_open_results_are_unchanged` (case `rs1 ring no fallbacks: UnknownKeyId`) |
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
  opening use `open_at` with an explicit `now` (also in `formal/docs/STATUS.md`).
- **Tests.** `codec::within_ttl_opens`, `codec::past_ttl_is_expired` (through `open`).

## Spec statements and proofs

The facts later proofs need are stated in `formal/specs/Drafts/External.lean` (72 statements,
success and failure cases) and proved in `formal/proofs/Proofs/External/` (`Base64.lean`,
`String.lean`, `Prim.lean`, `Std.lean`); `formal/specs/Drafts/Staged/External.lean` restates
them with `recall` and checks their axioms (each at most `propext`, `Classical.choice`,
`Quot.sound`).
