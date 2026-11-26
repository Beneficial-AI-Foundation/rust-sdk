/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Defs
public import Proofs.Model.RequestState.Public
public import Proofs.Model.RequestState.Keyring
public import Proofs.Model.RequestState.Seal
public import Proofs.Model.RequestState.OpenJson
public import Proofs.Model.RequestState.NewWithKeyring

@[expose] public section

/-!
# Public API of `crates/rmcp/src/model/request_state.rs` (R01–R15)

One row per theorem below; the theorem is `Theorems.request_state.<Theorem>`
(`RequestStateCodec::` is abbreviated `Codec::` in the second column, and `RequestStateCodec.`
as `RSC.` in the third). The keys of the last two columns are explained in "Premises" and "Not
covered" below.

| ID | Function | Theorem | Guarantee | Premises (caller must ensure) | Not covered (Rust may panic or behave otherwise; the model does not) |
|---|---|---|---|---|---|
| R01 | `SealOptions::new` | `SealOptions.new` | no associated data, no time-to-live | none | none |
| R02 | `SealOptions::associated_data` | `SealOptions.associated_data` | sets the associated data, keeps the time-to-live | none | none |
| R03 | `SealOptions::ttl` | `SealOptions.ttl` | sets the time-to-live to `Some(ttl)`, keeps the associated data | none | none |
| R04 | `Codec::new` | `RSC.new` | the single-key codec of `key.into()`, for a key of any length | caller code | (I) |
| R05 | `Codec::new_unchecked` | `RSC.new_unchecked` | the single-key codec of `key.into()`, for a key of any length | caller code | (I) |
| R06 | `Codec::try_new` | `RSC.try_new` | that codec if the key has at least 32 bytes, else `KeyTooShort` | caller code | (I) |
| R07 | `Codec::open` | `RSC.open` | the payload or error of opening the token with no associated data at the clock reading (`openAt`) | (F) | (K), (H) |
| R08 | `Codec::open_with` | `RSC.open_with` | the payload or error of opening the token with associated data `associated_data` at the clock reading (`openAt`) | (T), (F) | (K), (H), (V) |
| R08 cor. | `Codec::open_with` | `RSC.open_with_of_length_le` | as R08 | (L), (F) | (K), (H), (V) |
| R09 | `Codec::seal` | `RSC.seal` | the token sealed with no associated data and no time-to-live at the clock reading (`sealAt`) | (S), (D) | (K), (H) |
| R09 cor. | `Codec::seal` | `RSC.seal_of_length_le` | as R09 | `CodecValid`, (Ls) | (K), (H) |
| R10 | `Codec::seal_with` | `RSC.seal_with` | the token sealed with the options at the clock reading (`sealAt`) | (S), (D) | (K), (H), (V) |
| R10 cor. | `Codec::seal_with` | `RSC.seal_with_of_length_le` | as R10 | `CodecValid`, (Ls) | (K), (H) |
| R11 | `Codec::with_rs1_signing` | `RSC.with_rs1_signing` | seal mode `rs1` with the given key id, the id appended to the rs1 fallbacks unless already there; else `InvalidKeyring` | caller code, (R) | (I), (P) |
| R12 | `Codec::with_rs1_fallback` | `RSC.with_rs1_fallback` | the given key id appended to the rs1 fallbacks unless already there; else `InvalidKeyring` | caller code, (R) | (I), (P) |
| R13 | `Codec::open_json` | `RSC.open_json` | the error of opening as in R07, or the `serde_json::from_slice` outcome on the opened payload, an error mapped to `Deserialization` | (F) | (K), (H), (J) |
| R14 | `Codec::open_json_with` | `RSC.open_json_with` | the error of opening as in R08, or the `serde_json::from_slice` outcome on the opened payload, an error mapped to `Deserialization` | (T), (F) | (K), (H), (V), (J) |
| R15 | `Codec::new_with_keyring` | `RSC.new_with_keyring` | `Err` with the first failure in the Rust order of checks (`keyringCheck`); else a `CodecValid` keyring with exactly the given keys, up to entry order and `hash_builder` | caller code, (U) | (I), (P), (N) |

## What this file promises

`request_state.rs` seals a payload into a tamper-evident string token (`seal`, `seal_with`) and
opens such a token again (`open`, `open_with`, and `open_json`, `open_json_with`, which also
parse the payload as JSON); the codec that does this holds one key or a keyring of named keys
(`new`, `new_unchecked`, `try_new`, `new_with_keyring`, `with_rs1_signing`,
`with_rs1_fallback`), and `SealOptions` carries associated data and a time-to-live. For each of
these 15 public functions, a theorem below states that the call, in the Lean model, terminates
without panicking, and says what it returns (for a `Result`, in the `Ok` case and in every `Err`
case): the options built (R01–R03), the codec built, the token sealed (its UTF-8 bytes are those
`sealAt` describes), the payload or error of opening (that `openAt` describes), or, for
`open_json` and `open_json_with`, that error or the outcome of `serde_json::from_slice` on the
opened payload. Each holds under its premises, only in the translated configuration
("Provenance"); Rust may still panic, or behave otherwise, in the cases under "Not covered".
`formal/specs/README.md` indexes these guarantees in plain English.

## How to read a statement

A statement `f x ⦃ (result : T) => P result ⦄` says that the call `f x` terminates without
panicking in the Lean model and that its value `result` satisfies `P` (plan Section 3, "What a
spec means"). Every postcondition below except the `Ok` case of R15 determines `result`
uniquely: for `open`/`open_with` through the injectivity of `resultBytes` (`Defs.CodecState`);
for `seal`/`seal_with` and the `Ok` cases of R11/R12 through that of `ExtModel.utf8` (proved as
`Proofs.External.Utf8.utf8_injective`, restated as `Theorems.External.Utf8.utf8_injective`);
R13/R14 state `result = …` directly. For R15 the codec's key table is fixed only up to the order
of its entries and its `hash_builder`. When the postcondition is a `match result with`, its arms
give the `Ok` case and the `Err` cases, in the Rust order of checks.

The hypotheses `(h_… : …)` are **premises**: the caller must ensure them, and nothing is
promised when one fails. The **inherited exceptions** ("Not covered") are not premises: inputs
or environments where Rust panics or behaves otherwise but the statement promises a result;
they are recorded at the models (plan Section 4, rows "Clock", "HMAC", "Standard library") or
at the definitions named below.

Translated functions are written in full (`rmcp.model.request_state.…`), as a bare name would
resolve to a restated theorem. Below, `ad` is the associated data (`associated_data`;
`options.associated_data` for `seal_with`; empty for `open`, `open_json`, `seal`), not a binder
name, and `strBytes sealed` is the UTF-8 bytes of the token. `CodecValid codec`
(`Defs.CodecState`) is the codec invariant: a single-key codec is unconstrained; a keyring has
distinct key ids, every rs1 fallback id and the seal-mode id is a key id, every key has at least
32 bytes and every key id from 1 to 255 UTF-8 bytes. Line numbers: "patched" is the copy with
patches 01–03, "upstream" is `7caec76`, "patch-01 copy" is the copy with patch 01 only (see
"Line citations"); E01–E11 are the statements of the private functions in
`formal/proofs/Proofs/Internal/Model/RequestState.lean`.

## Premises (caller must ensure)

* **caller code** (`h_into`, `h_as_ref`, `h_into_iter`, `h_yields`, `h_entries`, `h_active`): a
  conversion or iterator of the caller (`Into`, `AsRef`, `IntoIterator`; user code, which may
  panic) returns the value the hypothesis names.
* **(F)** `h_fallbacks : FallbacksKnownForToken self (strBytes sealed)`: if the token's first
  `.`-component is `rs1`, every rs1 fallback id of the codec is a key id (`CodecFallbacksKnown`).
  It is sufficient, not necessary, for Rust not to panic: the `expect` of the rs1 fallback loop
  (patch-01 copy line 652, upstream 661) panics only for an `rs1` token that parses into three
  components, opened by a keyring with a non-empty fallback list, whose body and tag both decode
  (patch-01 copy lines 613–624), and only when a fallback id is not a key id. A single-key codec
  never reaches the loop (it checks the tag directly, patch-01 copy line 629); any other `rs1`
  token opened by a keyring returns `MalformedFormat` (does not parse), `UnknownKeyId` (no
  fallback) or `InvalidEncoding` (body or tag does not decode) before the loop.
* **(T)** `h_transcript_v1 : TranscriptV1Fits …`, `h_transcript_v2 : TranscriptV2Fits …`: the MAC
  transcript of the token's decoded components and `ad` fits in `usize::MAX` bytes (the bound of
  the Lean model of `Vec::extend_from_slice`). It holds for every token when `ad` is empty, so
  R07 and R13 do not take it.
* **(L)** `h_length : ad.len() + sealed.len() + 36 ≤ usize::MAX`; it implies (T).
* **(S)** `h_seal_key : CodecSealKeyKnown self`: the seal-mode key id is a key id (otherwise the
  `expect` of `seal_at` panics, patched lines 549 and 555).
* **(D)** `h_seal_fits : SealFits …`: the Lean-model domain of sealing (the transcript fits in
  `usize::MAX` bytes and the `String::with_capacity` sum in `isize::MAX`).
* **(Ls)** `h_length : ad.len() + 2 * payload.len() + 512 ≤ isize::MAX` (`ExtModel.maxStringBytes`;
  with `ad` empty for `seal`), taken together with `h_valid : CodecValid self` in place of (S) and
  (D).
* **(R)** `h_keyring_fits : KeyringFits self`: key ids of at most `usize::MAX` bytes and fewer than
  `usize::MAX` rs1 fallbacks; every Rust value meets it.
* **(U)** `h_kids_fit`, `h_active_fits`: the converted key ids of `new_with_keyring` have at most
  `usize::MAX` UTF-8 bytes; every Rust `String` meets it.

## Not covered (inherited exceptions)

* **(K)** Clock: `chrono::Utc::now` panics if the system clock is before 1970 or outside chrono's
  range (`chrono-0.4.45/src/offset/utc.rs` lines 96–98; recorded at the model of `now_ms` in
  `trusted/Rmcp/FunsExternal.lean`). Rust reads the clock first, before opening (patched line
  500, upstream 510; so in such an environment even a malformed token panics) and before sealing
  (patched line 442, upstream 452).
* **(H)** HMAC: the model of HMAC SHA-256 always succeeds, while the `u64` bit counter of SHA-256
  overflows (a panic under `overflow-checks`) for a transcript of at least `2^61 − 64` bytes or a
  key of at least `2^61` bytes (`sha2-0.11.2/src/block_api.rs` line 66, recorded at the model of
  `prim::hmac_sha256`). In opening it is the tag check (the exception stated for E09 and E11); in
  sealing, the tag of `seal_rs1` or `seal_rs2` (patched lines 577 and 590–593; the exception
  stated for E07, E08 and R10a in `formal/proofs/Proofs/Internal/Model/RequestState.lean`).
* **(V)** `open_with`, `open_json_with`, `seal_with` only: the transcript `Vec` is modelled up to
  `usize::MAX` bytes, while Rust panics above `isize::MAX` bytes. It does not arise without
  associated data (`open`, `open_json`: a transcript has at most `42 + 3n/4` bytes for a token of
  `n ≤ isize::MAX` bytes; `seal`: (D) bounds it), nor under (Ls).
* **(J)** `open_json`, `open_json_with`: the stated exceptions of the model of
  `serde_json::from_slice` (`ExtModel.serdeJsonFromSlice`): a `Deserialize` impl that panics,
  does not terminate, is non-deterministic or has side effects.
* **(I)** R04–R06, R11, R12, R15: the caller-code premises, `IterYields` and `ItemsConvert`
  describe the caller's `Into`, `AsRef` and `IntoIterator`/`Iterator` code as functions of their
  argument or state (the Aeneas translation of the traits); code that reads or writes global or
  thread-local state, or does input/output, is not described (stated exception of `IterYields`).
* **(P)** A `Drop` impl of a caller value that panics (R11, R12: the caller's `kid`; R15:
  `active_kid`, the iterator and the items not yet consumed); drops are not translated.
* **(N)** `HashMap::new` panics if the operating system's random source fails (R15; model of
  `HashMap::new`).

## The clock

Human decision 2026-11-24, extended by the spec owner 2026-11-25 (`formal/README.md`, "Trusted
base"; plan Section 4, row "Clock"). `open`, `open_with`, `seal` and `seal_with` read the clock
once (`Self::now_ms()`, patched lines 500 and 442, upstream 510 and 452); `open_json` and
`open_json_with` read it through `open_with`. The model of the private
`RequestStateCodec::now_ms` (patch-01 copy lines 729–731, upstream 784–786) is
`ok ExtModel.nowMs`, one opaque `I64` constant. The review rule of "Trusted base" forbids any
statement to name `now_ms`, the six clock-reading functions or `ExtModel.nowMs`; this file is its
allowed exception for the six functions and `ExtModel.nowMs`, only with the postconditions that
rule lists (those of R07–R10, their corollaries, R13, R14); no statement names `now_ms`.
No statement constrains `nowMs` or involves two readings: as `nowMs` is opaque, each holds at an
arbitrary `I64` reading and says nothing about two calls (in Rust they read different times; in
the model they would see the same constant). The caller does not control the time.

## Provenance

*Scope.* The public API of `request_state.rs` (functions `pub` in upstream rmcp; human decision
2026-11-24). R01–R08 are the eight public functions that are translated but were not Phase 1
targets (plan Section 2.3, "Consequences"), with one corollary of R08; R09–R15 (translation
patch 03) add seven, with corollaries of R09 and R10. Not translated, so not specified here
(`exclude` list of `crates/rmcp/Cargo.toml`, lines 93–103): `seal_json` and `seal_json_with`
(R16, R17; Aeneas does not support the mutually recursive `serde_core::ser` traits, issue record
`formal/trusted/issues/aeneas-serde-ser-mutual-traits.md`), the `Error`, `Debug` and `Display`
impls of `RequestStateError`, and the `Debug` impls of `RequestStateCodec`, `SealOptions` and
`SealMode`. The private functions (E01–E11, E09a, `seal_at` R10a) and the round trips
(R10b and the model round trip of `sealAt` and `openAt`) are in
`formal/proofs/Proofs/Internal/Model/RequestState.lean`.

*Order.* The statements are in ID order (R01–R15, each corollary after its statement). This is a
recorded exception (spec owner, 2026-11-25) to the Rust-source-order rule (`docs/STYLE_GUIDE.md`;
plan Section 5); source order: R01–R06, R15, R11, R12, R09, R10, R07, R08, R13, R14 (patched
lines 153, 163, 170, 278, 286, 298, 319, 373, 410, 436, 441, 476, 495, 509, 521).

*Proofs.* Each statement is restated as a theorem `Theorems.request_state.<Type>.<function>`,
proved by its spec theorem in `Proofs/Model/RequestState/{Public,Seal,Keyring,OpenJson,
NewWithKeyring}.lean` (whose docstrings also name the Rust tests), and followed by the
assumptions its proof depends on, checked by `#print axioms` under `#guard_msgs`. A second
recorded exception (human decision 2026-11-25): the restated statements use the abbreviations of
`Defs.CodecState` and their own binder names, so their text differs from that of the spec
theorems, while Lean checks the types definitionally equal (the restatement's proof is the spec
theorem). Names here ↦ names in the spec theorems: type binders `KeyLike` (R04–R06), `KidLike`
(R11, R12) ↦ `T0`; `ActiveKid`, `Entries`, `EntryIter` (R15) ↦ `T2`, `T3`, `Clause3_IntoIter`;
instance binders `intoBytes` (R04–R06) ↦ `coreconvertIntoT0VecU8Inst`, `asStr` (R11, R12) ↦
`coreconvertAsRefT0StrInst`, `deserializeInst` (R13, R14) ↦ `serde_coredeDeserializeOwnedInst`,
and in R15 `kidInto`, `keyInto`, `activeKidInto`, `entriesIntoIter` ↦
`coreconvertIntoKStringInst`, `coreconvertIntoVVecU8Inst`, `coreconvertIntoT2StringInst`,
`coreitertraitscollectIntoIteratorT3PairClause3_IntoIterInst`; hypotheses `h_transcript_v1`,
`h_transcript_v2` (R08, R14) ↦ `h_len1`, `h_len2`; `h_seal_key`, `h_seal_fits` (R09, R10) ↦
`h_key`, `h_fits`; `h_length` (the corollaries) ↦ `h_len`; `h_keyring_fits` (R11, R12) ↦
`h_fits`; `h_kids_fit`, `h_active_fits` (R15) ↦ `h_fit`, `h_fit_active`; the bound key table
`ring` of R11, R12 ↦ `keys`.

*Sign-off.* R01–R08: signed off by the spec owner on 2026-11-24 (the signed-off text was in
`specs/Drafts/RequestState.lean`, removed at incorporation). R09–R15: signed off on 2026-11-25
(draft outside the repository; `seal`, `seal_with` at `ExtModel.nowMs` by spec-owner decision
of that day). **Readability rewrite of 2026-11-25: signed off by the spec owner on 2026-11-25**
after a spec cycle of 5 review rounds. It changes the text (binder and hypothesis names,
docstrings, abbreviations of `Defs.CodecState`), not the meaning: each type is definitionally
equal to its text at commit `8debe97` (checked by `rfl`, binder kinds unchanged; evidence in
`formal/docs/STATUS.md`, "Readability rewrite of R01–R15").

*Translated configuration* (the proofs hold only for it): target `x86_64-unknown-linux-gnu`,
`--no-default-features` with the features `request-state`, `server`, `client`, `client-side-sse`,
`transport-streamable-http-server`, `transport-streamable-http-client` and `auth` (plan
Section 15), with `overflow-checks=true` and `debug-assertions=true` (plan Section 1). Aeneas
`nightly-2026.11.24-fb44cb4` (until 2026-11-24 `nightly-2026.08.20-5d08da4`). All 18 theorems
are about one translation: that of the copy of origin/main `7caec76` with the patches 01–03 of
`formal/trusted/patches/` applied in order by `scripts/apply-patches.sh`
(`01-request-state-wire.patch`, D2 fallback 2026-11-23; `02-phase2-tests.patch`, test-only;
`03-request-state-public.patch`).

*Line citations.* "patched" is the patches 01–03 copy, "upstream" is `7caec76`. "patch-01 copy"
marks a line of the copy with patch 01 only, as in the E statements; each such line cited here
(all ≥ 565) is four greater in the patched copy (e.g. 652 is 656). The public functions have the
same text upstream and patched (upstream line numbers are ten greater), except the end of
`open_json_with` (R14): patch 03 replaces upstream line 537 by the `match` of patched lines
527–530 (the changes to private code are listed in the patch headers).

*Definitions used* (`formal/specs/Defs/`): those of `Defs.Wire` and `Defs.CodecState` listed in
the `open` lines below and `KeyringFailure.Describes` directly, and through the abbreviations of
`Defs.CodecState` also `Defs.Wire.components`, `versionV1`, `versionV2`, `transcriptV1`,
`transcriptV2`, `Defs.CodecState.CodecFallbacksKnown` and `Defs.RequestState.StrIs`. No
statement names a private Rust function: `openAt` and `sealAt` are the expected results defined in
`Defs.CodecState`, not the translated private `open_at` and `seal_at`.

*External models used* (`trusted/Rmcp/FunsExternal.lean`), the main ones among others (the full
list is that file): `zeroize::Zeroizing::new` (R04–R06, R15; wraps the vector unchanged,
zeroisation on drop is not modelled, plan Section 4); `zeroize::Zeroizing::deref` (R06; returns
the wrapped vector, which `try_new` passes to `validate_key_length`); the clock reading
`ExtModel.nowMs` through the model of `now_ms` (R07–R10, R13, R14);
`ExtModel.serdeJsonFromSlice` (R13, R14); `HashMap::new` and its hash keys
`ExtModel.randomState` (R15); the `HashMap`, `String`, `Vec` and iterator models that R09–R15
call (e.g. `contains_key`, `entry`, `with_capacity`, `push_str`, `Iterator::any`,
`Duration::as_millis`); and, through E11 and the sealing functions, `ExtModel.b64Decode` (also
in the premises (T)), `ExtModel.hmacSha256`, `ExtModel.utf8`, `ExtModel.b64`,
`ExtModel.maxStringBytes` and `ExtModel.strOfBytes?`. The proof of R07 uses the
laws `Proofs.External.Base64.b64_of_b64Decode` and `Proofs.External.Base64.length_b64`, the
corollary of R08 the bound `ExtModel.b64Decode_length_le`.

*Native-code assumptions:* none since the Aeneas upgrade of 2026-11-24 (`native-axioms.lock`
empty). Until then R07, R08 and the R08 corollary reached
`rmcp.model.request_state.RequestStateCodec.rs1_fallbacks_verify_loop.body._native.decide.ax_3`
(through E11); 8 of the 9 `#print axioms` lists of R01–R08 changed in the upgrade (that one
dropped, standard ones added), re-signed by the spec owner on 2026-11-24.
-/

open Aeneas Aeneas.Std Result
open Defs.Wire (minKeyLength)
open Defs.CodecState (CodecValid openAt resultBytes keyIds lookupKey sealAt CodecSealKeyKnown
  SealFits KeyringFits IterYields keyringCheck rs1SigningNeedsKeyringMsg rs1SigningKidMissingMsg
  rs1FallbackNeedsKeyringMsg rs1FallbackKidMissingMsg strBytes FallbacksKnownForToken
  TranscriptV1Fits TranscriptV2Fits appendIfAbsent IsInvalidKeyring IsKeyTooShort entryBytes
  ItemsConvert mapErrDeserialization)
open rmcp.model.request_state (SealOptions RequestStateCodec Keys RequestStateError)

/-- R01 `SealOptions::new`: returns empty options, with no associated data and no time-to-live
(`Self::default()`, patched lines 153–155, upstream 163–165). -/
theorem Theorems.request_state.SealOptions.new :
    rmcp.model.request_state.SealOptions.new ⦃ (result : SealOptions) =>
      result.associated_data.val = [] ∧
      result.ttl = none ⦄ :=
  rmcp.model.request_state.SealOptions.new_spec

/--
info: 'Theorems.request_state.SealOptions.new' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state.SealOptions.new

/-- R02 `SealOptions::associated_data`: returns the options with the associated data set to the
argument and the time-to-live unchanged (patched lines 163–166, upstream 173–176). -/
theorem Theorems.request_state.SealOptions.associated_data (self : SealOptions)
    (associated_data : Slice Std.U8) :
    rmcp.model.request_state.SealOptions.impl.associated_data self associated_data ⦃
      (result : SealOptions) =>
      result.associated_data = associated_data ∧
      result.ttl = self.ttl ⦄ :=
  rmcp.model.request_state.SealOptions.impl.associated_data_spec self associated_data

/--
info: 'Theorems.request_state.SealOptions.associated_data' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state.SealOptions.associated_data

/-- R03 `SealOptions::ttl`: returns the options with the time-to-live set to `Some(ttl)` and the
associated data unchanged (patched lines 170–173, upstream 180–183). -/
theorem Theorems.request_state.SealOptions.ttl (self : SealOptions) (ttl : core.time.Duration) :
    rmcp.model.request_state.SealOptions.impl.ttl self ttl ⦃ (result : SealOptions) =>
      result.associated_data = self.associated_data ∧
      result.ttl = some ttl ⦄ :=
  rmcp.model.request_state.SealOptions.impl.ttl_spec self ttl

/--
info: 'Theorems.request_state.SealOptions.ttl' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state.SealOptions.ttl

/-- R04 `RequestStateCodec::new` (deprecated): returns the single-key codec whose key is the
vector `v` that `key.into()` returns, whatever its length (`Self::new_unchecked(key)`, patched
lines 278–280, upstream 288–290; `Keys::Single(Zeroizing::new(key.into()))`, patched lines
286–290). The codec satisfies `CodecValid` (a single-key codec is unconstrained).

Premise: caller code, `h_into` (the caller's `Into<Vec<u8>>` returns `v`). Not covered: (I). -/
theorem Theorems.request_state.RequestStateCodec.new {KeyLike : Type}
    (intoBytes : core.convert.Into KeyLike (alloc.vec.Vec Std.U8)) (key : KeyLike)
    (v : alloc.vec.Vec Std.U8) (h_into : intoBytes.into key = ok v) :
    rmcp.model.request_state.RequestStateCodec.new intoBytes key ⦃
      (result : RequestStateCodec) =>
      result.keys = Keys.Single { inner := v } ∧
      CodecValid result ⦄ :=
  rmcp.model.request_state.RequestStateCodec.new_spec intoBytes key v h_into

/--
info: 'Theorems.request_state.RequestStateCodec.new' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.new

/-- R05 `RequestStateCodec::new_unchecked`: returns the single-key codec whose key is the vector
`v` that `key.into()` returns, whatever its length (`Keys::Single(Zeroizing::new(key.into()))`,
patched lines 286–290, upstream 296–300). The codec satisfies `CodecValid`.

Premise: caller code, `h_into`. Not covered: (I). -/
theorem Theorems.request_state.RequestStateCodec.new_unchecked {KeyLike : Type}
    (intoBytes : core.convert.Into KeyLike (alloc.vec.Vec Std.U8)) (key : KeyLike)
    (v : alloc.vec.Vec Std.U8) (h_into : intoBytes.into key = ok v) :
    rmcp.model.request_state.RequestStateCodec.new_unchecked intoBytes key ⦃
      (result : RequestStateCodec) =>
      result.keys = Keys.Single { inner := v } ∧
      CodecValid result ⦄ :=
  rmcp.model.request_state.RequestStateCodec.new_unchecked_spec intoBytes key v h_into

/--
info: 'Theorems.request_state.RequestStateCodec.new_unchecked' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.new_unchecked

/-- R06 `RequestStateCodec::try_new`: returns `Ok` of the single-key codec of the vector `v` that
`key.into()` returns (it satisfies `CodecValid`) exactly when `v` has at least
`minKeyLength = 32` bytes, otherwise `Err(KeyTooShort { minimum: 32, actual: v.len() })`
(`IsKeyTooShort e v.val.length`; patched lines 298–304, upstream 308–314; the length check is
`validate_key_length`, E03).

Premise: caller code, `h_into`. Not covered: (I). -/
theorem Theorems.request_state.RequestStateCodec.try_new {KeyLike : Type}
    (intoBytes : core.convert.Into KeyLike (alloc.vec.Vec Std.U8)) (key : KeyLike)
    (v : alloc.vec.Vec Std.U8) (h_into : intoBytes.into key = ok v) :
    rmcp.model.request_state.RequestStateCodec.try_new intoBytes key ⦃
      (result : core.result.Result RequestStateCodec RequestStateError) =>
      match result with
      | .Ok codec =>
        minKeyLength ≤ v.val.length ∧
        codec.keys = Keys.Single { inner := v } ∧
        CodecValid codec
      | .Err e =>
        v.val.length < minKeyLength ∧
        IsKeyTooShort e v.val.length ⦄ :=
  rmcp.model.request_state.RequestStateCodec.try_new_spec intoBytes key v h_into

/--
info: 'Theorems.request_state.RequestStateCodec.try_new' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.try_new

/-- R07 `RequestStateCodec::open`: opens the token `sealed` with no associated data at the clock
reading and returns the payload or the error that the expected opening result
`openAt self (strBytes sealed) [] ExtModel.nowMs.val` gives (`self.open_with(sealed, &[])`,
patched lines 476–478, upstream 486–488). One clock reading, parametric; nothing about two
calls (see "The clock").

Premise: (F) `h_fallbacks`. Not covered: (K), (H). -/
theorem Theorems.request_state.RequestStateCodec.open (self : RequestStateCodec) (sealed : Str)
    (h_fallbacks : FallbacksKnownForToken self (strBytes sealed)) :
    rmcp.model.request_state.RequestStateCodec.open self sealed ⦃
      (result : core.result.Result (alloc.vec.Vec Std.U8) RequestStateError) =>
      resultBytes result = openAt self (strBytes sealed) [] ExtModel.nowMs.val ⦄ :=
  rmcp.model.request_state.RequestStateCodec.open_spec self sealed h_fallbacks

/--
info: 'Theorems.request_state.RequestStateCodec.open' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.open

/-- R08 `RequestStateCodec::open_with`: opens the token `sealed` with the associated data
`associated_data` at the clock reading and returns the payload or the error that
`openAt self (strBytes sealed) associated_data.val ExtModel.nowMs.val` gives
(`self.open_at(sealed, associated_data, Self::now_ms())`, patched lines 495–501, upstream
505–511). One clock reading, parametric; nothing about two calls (see "The clock").

Premises: (T) `h_transcript_v1`, `h_transcript_v2`; (F) `h_fallbacks`. Not covered: (K), (H),
(V). -/
theorem Theorems.request_state.RequestStateCodec.open_with (self : RequestStateCodec)
    (sealed : Str) (associated_data : Slice Std.U8)
    (h_transcript_v1 : TranscriptV1Fits (strBytes sealed) associated_data.val)
    (h_transcript_v2 : TranscriptV2Fits (strBytes sealed) associated_data.val)
    (h_fallbacks : FallbacksKnownForToken self (strBytes sealed)) :
    rmcp.model.request_state.RequestStateCodec.open_with self sealed associated_data ⦃
      (result : core.result.Result (alloc.vec.Vec Std.U8) RequestStateError) =>
      resultBytes result =
        openAt self (strBytes sealed) associated_data.val ExtModel.nowMs.val ⦄ :=
  rmcp.model.request_state.RequestStateCodec.open_with_spec self sealed associated_data
    h_transcript_v1 h_transcript_v2 h_fallbacks

/--
info: 'Theorems.request_state.RequestStateCodec.open_with' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.open_with

/-- R08, corollary: `open_with` returns what R08 says (`openAt … ExtModel.nowMs.val`), with the
transcript premises (T) replaced by the simpler length premise (L):
`associated_data.len() + sealed.len() + 36 ≤ usize::MAX` (via the bound
`ExtModel.b64Decode_length_le`).
One clock reading, parametric; nothing about two calls (see "The clock").

Premises: (L) `h_length`; (F) `h_fallbacks`. Not covered: (K), (H), (V). -/
theorem Theorems.request_state.RequestStateCodec.open_with_of_length_le
    (self : RequestStateCodec) (sealed : Str) (associated_data : Slice Std.U8)
    (h_length : associated_data.val.length + (strBytes sealed).length + 36 ≤ Usize.max)
    (h_fallbacks : FallbacksKnownForToken self (strBytes sealed)) :
    rmcp.model.request_state.RequestStateCodec.open_with self sealed associated_data ⦃
      (result : core.result.Result (alloc.vec.Vec Std.U8) RequestStateError) =>
      resultBytes result =
        openAt self (strBytes sealed) associated_data.val ExtModel.nowMs.val ⦄ :=
  rmcp.model.request_state.RequestStateCodec.open_with_spec_of_length_le self sealed
    associated_data h_length h_fallbacks

/--
info: 'Theorems.request_state.RequestStateCodec.open_with_of_length_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.open_with_of_length_le

/-- R09 `RequestStateCodec::seal`: returns the token that seals `payload` with no associated data
and no time-to-live; its UTF-8 bytes are `sealAt self payload.val [] none ExtModel.nowMs.val`
(`self.seal_with(payload, &SealOptions::default())`, patched lines 436–438, upstream 446–448).
The token does not depend on the clock reading (no time-to-live), but the clock is read.
One clock reading, parametric; nothing about two calls (see "The clock").

Premises: (S) `h_seal_key`; (D) `h_seal_fits` with no associated data. Not covered: (K), (H). -/
theorem Theorems.request_state.RequestStateCodec.seal (self : RequestStateCodec)
    (payload : Slice Std.U8)
    (h_seal_key : CodecSealKeyKnown self)
    (h_seal_fits : SealFits self payload.val.length 0) :
    rmcp.model.request_state.RequestStateCodec.seal self payload ⦃ (result : String) =>
      sealAt self payload.val [] none ExtModel.nowMs.val = some (ExtModel.utf8 result) ⦄ :=
  rmcp.model.request_state.RequestStateCodec.seal_spec self payload h_seal_key h_seal_fits

/--
info: 'Theorems.request_state.RequestStateCodec.seal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.seal

/-- R09, corollary: `seal` returns what R09 says (`sealAt … ExtModel.nowMs.val`), with (S) and
(D) replaced by `CodecValid self` and (Ls) `2 * payload.len() + 512 ≤ isize::MAX`.
One clock reading, parametric; nothing about two calls (see "The clock").

Premises: `h_valid`; (Ls) `h_length`. Not covered: (K), (H). -/
theorem Theorems.request_state.RequestStateCodec.seal_of_length_le (self : RequestStateCodec)
    (payload : Slice Std.U8)
    (h_valid : CodecValid self)
    (h_length : 2 * payload.val.length + 512 ≤ ExtModel.maxStringBytes) :
    rmcp.model.request_state.RequestStateCodec.seal self payload ⦃ (result : String) =>
      sealAt self payload.val [] none ExtModel.nowMs.val = some (ExtModel.utf8 result) ⦄ :=
  rmcp.model.request_state.RequestStateCodec.seal_spec_of_length_le self payload h_valid h_length

/--
info: 'Theorems.request_state.RequestStateCodec.seal_of_length_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.seal_of_length_le

/-- R10 `RequestStateCodec::seal_with`: returns the token that seals `payload` with the options'
associated data and time-to-live at the clock reading; its UTF-8 bytes are
`sealAt self payload.val options.associated_data.val options.ttl ExtModel.nowMs.val`
(`self.seal_at(payload, options, Self::now_ms())`, patched lines 441–443, upstream 451–453); the
reading matters only with a time-to-live.
One clock reading, parametric; nothing about two calls (see "The clock").

Premises: (S) `h_seal_key`; (D) `h_seal_fits`. Not covered: (K), (H), (V). -/
theorem Theorems.request_state.RequestStateCodec.seal_with (self : RequestStateCodec)
    (payload : Slice Std.U8)
    (options : SealOptions)
    (h_seal_key : CodecSealKeyKnown self)
    (h_seal_fits : SealFits self payload.val.length options.associated_data.val.length) :
    rmcp.model.request_state.RequestStateCodec.seal_with self payload options ⦃ (result : String) =>
      sealAt self payload.val options.associated_data.val options.ttl ExtModel.nowMs.val =
        some (ExtModel.utf8 result) ⦄ :=
  rmcp.model.request_state.RequestStateCodec.seal_with_spec self payload options h_seal_key
    h_seal_fits

/--
info: 'Theorems.request_state.RequestStateCodec.seal_with' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.seal_with

/-- R10, corollary: `seal_with` returns what R10 says (`sealAt … ExtModel.nowMs.val`), with (S)
and (D) replaced by `CodecValid self` and (Ls)
`associated_data.len() + 2 * payload.len() + 512 ≤ isize::MAX`.
One clock reading, parametric; nothing about two calls (see "The clock").

Premises: `h_valid`; (Ls) `h_length`. Not covered: (K), (H); (V) does not arise under (Ls). -/
theorem Theorems.request_state.RequestStateCodec.seal_with_of_length_le (self : RequestStateCodec)
    (payload : Slice Std.U8)
    (options : SealOptions)
    (h_valid : CodecValid self)
    (h_length : options.associated_data.val.length + 2 * payload.val.length + 512 ≤
      ExtModel.maxStringBytes) :
    rmcp.model.request_state.RequestStateCodec.seal_with self payload options ⦃ (result : String) =>
      sealAt self payload.val options.associated_data.val options.ttl ExtModel.nowMs.val =
        some (ExtModel.utf8 result) ⦄ :=
  rmcp.model.request_state.RequestStateCodec.seal_with_spec_of_length_le self payload options
    h_valid h_length

/--
info: 'Theorems.request_state.RequestStateCodec.seal_with_of_length_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.seal_with_of_length_le

/-- R11 `RequestStateCodec::with_rs1_signing`: makes a keyring codec seal `rs1` tokens with the
key id `kid`, or rejects the call (patched lines 373–400, upstream 383–410). `kid.as_ref()` is
evaluated first and returns the `&str` `k` (line 374). Then, in the Rust order of checks:

1. single-key codec → `Err(InvalidKeyring(rs1SigningNeedsKeyringMsg))` (lines 376–378);
2. a keyring with no key id whose UTF-8 bytes are `k` (`keys.contains_key(kid)`, line 384) →
   `Err(InvalidKeyring(rs1SigningKidMissingMsg))` (lines 385–387);
3. otherwise `Ok codec`: `k` is the UTF-8 encoding of a key id `kidStr`; `codec` has the same
   key table, seal mode `Rs1 { key_id: kidStr }` (lines 390–393), and the rs1 fallbacks with
   `kidStr` appended unless already present (`appendIfAbsent`, lines 394–396). It preserves
   `CodecValid`.

Premises: caller code `h_as_ref`; (R) `h_keyring_fits`. Not covered: (I), (P). -/
theorem Theorems.request_state.RequestStateCodec.with_rs1_signing {KidLike : Type}
    (asStr : core.convert.AsRef KidLike Str)
    (self : RequestStateCodec) (kid : KidLike) (k : Str)
    (h_as_ref : asStr.as_ref kid = ok k)
    (h_keyring_fits : KeyringFits self) :
    rmcp.model.request_state.RequestStateCodec.with_rs1_signing asStr self kid ⦃
      (result : core.result.Result RequestStateCodec RequestStateError) =>
      match result with
      | .Ok codec =>
        ∃ ring seal_mode rs1_fallbacks kidStr,
          self.keys = .Ring ring seal_mode rs1_fallbacks ∧
          ExtModel.utf8 kidStr = strBytes k ∧ kidStr ∈ keyIds ring ∧
          (∃ fallbacks : alloc.vec.Vec String,
            codec.keys = .Ring ring (.Rs1 kidStr) fallbacks ∧
            fallbacks.val = appendIfAbsent rs1_fallbacks.val kidStr) ∧
          (CodecValid self → CodecValid codec)
      | .Err e =>
        ((∃ key, self.keys = .Single key) ∧
          IsInvalidKeyring e rs1SigningNeedsKeyringMsg) ∨
        ((∃ ring seal_mode rs1_fallbacks, self.keys = .Ring ring seal_mode rs1_fallbacks ∧
            ∀ kidStr ∈ keyIds ring, ExtModel.utf8 kidStr ≠ strBytes k) ∧
          IsInvalidKeyring e rs1SigningKidMissingMsg) ⦄ :=
  rmcp.model.request_state.RequestStateCodec.with_rs1_signing_spec asStr self kid k h_as_ref
    h_keyring_fits

/--
info: 'Theorems.request_state.RequestStateCodec.with_rs1_signing' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.with_rs1_signing

/-- R12 `RequestStateCodec::with_rs1_fallback`: makes a keyring codec also accept `rs1` tokens
signed with the key `kid`, or rejects the call (patched lines 410–432, upstream 420–442).
`kid.as_ref()` is evaluated first and returns the `&str` `k` (line 411). Then, in the Rust order
of checks:

1. single-key codec → `Err(InvalidKeyring(rs1FallbackNeedsKeyringMsg))` (lines 413–415);
2. a keyring with no key id whose UTF-8 bytes are `k` (line 421) →
   `Err(InvalidKeyring(rs1FallbackKidMissingMsg))` (lines 422–424);
3. otherwise `Ok codec`: `k` is the UTF-8 encoding of a key id `kidStr`; `codec` has the same
   key table and seal mode, and the rs1 fallbacks with `kidStr` appended unless already present
   (`appendIfAbsent`, lines 426–428). It preserves `CodecValid`.

Premises: caller code `h_as_ref`; (R) `h_keyring_fits`. Not covered: (I), (P). -/
theorem Theorems.request_state.RequestStateCodec.with_rs1_fallback {KidLike : Type}
    (asStr : core.convert.AsRef KidLike Str)
    (self : RequestStateCodec) (kid : KidLike) (k : Str)
    (h_as_ref : asStr.as_ref kid = ok k)
    (h_keyring_fits : KeyringFits self) :
    rmcp.model.request_state.RequestStateCodec.with_rs1_fallback asStr self kid ⦃
      (result : core.result.Result RequestStateCodec RequestStateError) =>
      match result with
      | .Ok codec =>
        ∃ ring seal_mode rs1_fallbacks kidStr,
          self.keys = .Ring ring seal_mode rs1_fallbacks ∧
          ExtModel.utf8 kidStr = strBytes k ∧ kidStr ∈ keyIds ring ∧
          (∃ fallbacks : alloc.vec.Vec String,
            codec.keys = .Ring ring seal_mode fallbacks ∧
            fallbacks.val = appendIfAbsent rs1_fallbacks.val kidStr) ∧
          (CodecValid self → CodecValid codec)
      | .Err e =>
        ((∃ key, self.keys = .Single key) ∧
          IsInvalidKeyring e rs1FallbackNeedsKeyringMsg) ∨
        ((∃ ring seal_mode rs1_fallbacks, self.keys = .Ring ring seal_mode rs1_fallbacks ∧
            ∀ kidStr ∈ keyIds ring, ExtModel.utf8 kidStr ≠ strBytes k) ∧
          IsInvalidKeyring e rs1FallbackKidMissingMsg) ⦄ :=
  rmcp.model.request_state.RequestStateCodec.with_rs1_fallback_spec asStr self kid k h_as_ref
    h_keyring_fits

/--
info: 'Theorems.request_state.RequestStateCodec.with_rs1_fallback' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.with_rs1_fallback

/-- R13 `RequestStateCodec::open_json`: opens the token `sealed` with no associated data at the
clock reading and parses the payload as JSON of type `T` (`self.open_json_with(sealed, &[])`,
patched lines 509–511, upstream 519–521):

* if opening fails, i.e. `openAt self (strBytes sealed) [] ExtModel.nowMs.val` is an error `e`,
  the result is `Err e`, unchanged (the `?` of patched line 526, in `open_json_with`);
* otherwise, for the opened payload, the result is the outcome of `serde_json::from_slice`
  (`ExtModel.serdeJsonFromSlice`, line 527 of `open_json_with`) with an error mapped to
  `Deserialization` (`mapErrDeserialization`, lines 527–530).

`deserializeInst` is the caller's `T: DeserializeOwned` bound; its field
`deserializeInst.DeserializeInst` is the caller's `Deserialize` impl for `T`, which
`serde_json::from_slice` uses. The statement says only that the result is the opaque outcome
`ExtModel.serdeJsonFromSlice` gives for that impl and the payload, at one clock reading,
parametric; it relates no two calls (neither two parses nor two clock readings; see "The
clock").

Premise: (F) `h_fallbacks`. Not covered: (K), (H), (J). -/
theorem Theorems.request_state.RequestStateCodec.open_json {T : Type}
    (deserializeInst : rmcp.serde_core.de.DeserializeOwned T) (self : RequestStateCodec)
    (sealed : Str)
    (h_fallbacks : FallbacksKnownForToken self (strBytes sealed)) :
    rmcp.model.request_state.RequestStateCodec.open_json deserializeInst self sealed ⦃
      (result : core.result.Result T RequestStateError) =>
      match openAt self (strBytes sealed) [] ExtModel.nowMs.val with
      | .error e => result = .Err e
      | .ok payload =>
        result = mapErrDeserialization
          (ExtModel.serdeJsonFromSlice deserializeInst.DeserializeInst payload) ⦄ :=
  rmcp.model.request_state.RequestStateCodec.open_json_spec deserializeInst self sealed
    h_fallbacks

/--
info: 'Theorems.request_state.RequestStateCodec.open_json' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.open_json

/-- R14 `RequestStateCodec::open_json_with`: opens the token `sealed` with the associated data
`associated_data` at the clock reading and parses the payload as JSON of type `T` (patched lines
521–531, upstream 531–538):

* if opening fails, i.e. `openAt self (strBytes sealed) associated_data.val ExtModel.nowMs.val`
  is an error `e`, the result is `Err e`, unchanged (`self.open_with(sealed,
  associated_data)?`, patched line 526);
* otherwise, for the opened payload, the result is the outcome of `serde_json::from_slice`
  (`ExtModel.serdeJsonFromSlice`, line 527) with an error mapped to `Deserialization`
  (`mapErrDeserialization`, lines 527–530; upstream `.map_err(RequestStateError::Deserialization)`,
  line 537).

`deserializeInst.DeserializeInst` is the caller's `Deserialize` impl for `T`, which
`serde_json::from_slice` uses (as in R13). The statement says only that the result is the opaque
outcome `ExtModel.serdeJsonFromSlice` gives for that impl and the payload, at one clock reading,
parametric; it relates no two calls (neither two parses nor two clock readings; see "The
clock").

Premises: (T) `h_transcript_v1`, `h_transcript_v2`; (F) `h_fallbacks`. Not covered: (K), (H),
(V), (J). -/
theorem Theorems.request_state.RequestStateCodec.open_json_with {T : Type}
    (deserializeInst : rmcp.serde_core.de.DeserializeOwned T) (self : RequestStateCodec)
    (sealed : Str) (associated_data : Slice Std.U8)
    (h_transcript_v1 : TranscriptV1Fits (strBytes sealed) associated_data.val)
    (h_transcript_v2 : TranscriptV2Fits (strBytes sealed) associated_data.val)
    (h_fallbacks : FallbacksKnownForToken self (strBytes sealed)) :
    rmcp.model.request_state.RequestStateCodec.open_json_with deserializeInst self sealed
      associated_data ⦃ (result : core.result.Result T RequestStateError) =>
      match openAt self (strBytes sealed) associated_data.val ExtModel.nowMs.val with
      | .error e => result = .Err e
      | .ok payload =>
        result = mapErrDeserialization
          (ExtModel.serdeJsonFromSlice deserializeInst.DeserializeInst payload) ⦄ :=
  rmcp.model.request_state.RequestStateCodec.open_json_with_spec deserializeInst self sealed
    associated_data h_transcript_v1 h_transcript_v2 h_fallbacks

/--
info: 'Theorems.request_state.RequestStateCodec.open_json_with' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.open_json_with

/-- R15 `RequestStateCodec::new_with_keyring`: builds a keyring codec that seals `rs2` tokens with
the active key id, or returns the error of the first check that fails (patched lines 319–364,
upstream 329–374). Its outcome is decided by `keyringCheck` (`Defs.CodecState`).

`keys` is the caller's iterable; `ring` is the resulting key table.

Hypotheses, in order:

1. `h_into_iter`: `keys.into_iter()` (caller code) returns the iterator `it`.
2. `h_yields`: `it` yields the items `items` and then `None` (`IterYields`; caller code).
3. `h_entries`: each item `(kid, key)` converts, by `kid.into()` and `key.into()` (patched lines
   329–330), to the entry of `entries` at the same position (`ItemsConvert`; caller code).
4. `h_active`: `active_kid.into()` returns `active` (line 349, called only after the loop).
5. (U) `h_kids_fit`, `h_active_fits`: the converted ids have at most `usize::MAX` UTF-8 bytes (the
   Lean model of `String::deref` fails above it).

The caller-code premises are unconditional (lead decision 2026-11-25): they also require code
that Rust never runs to return (every `next` and `into()` after the first rejected entry, and
`active_kid.into()` when Rust returns before line 349); if such code would panic or diverge, the
premises fail and the statement says nothing. An infinite iterator has no finite `items`, so
`h_yields` cannot hold and the statement says nothing about it.

Result, with `entryBytes entries` the entries with each key as its bytes:

* `Err e` exactly when `keyringCheck active (entryBytes entries)` is a failure `f`, and `e` is
  the error of `f` (`KeyringFailure.Describes`): per entry in order, an empty id, an id over 255
  bytes (E04, line 331), a key under 32 bytes (`KeyTooShort`, E03, line 332), a repeated id
  (line 338); then no entry (lines 343–347); then the active id empty or over 255 bytes (line
  350); then the active id not a key id (lines 351–355).
* `Ok codec` exactly when `keyringCheck` succeeds; `codec` is a keyring (lines 357–363) whose
  key ids are, up to order, the configured ids (`List.Perm`), each holding its configured key
  (`lookupKey`), with seal mode `Rs2 { key_id: active }` (the active id is a configured id and
  holds its configured key) and no rs1 fallback, and it satisfies `CodecValid`.

Nothing is said about the map's `hash_builder` (`ExtModel.randomState`) or the order of its
entries, and no two results are compared, so the `Ok` case fixes `codec` only up to these.

Premises: caller code `h_into_iter`, `h_yields`, `h_entries`, `h_active`; (U) `h_kids_fit`,
`h_active_fits`. Not covered: (I), (P), (N). -/
theorem Theorems.request_state.RequestStateCodec.new_with_keyring
    {K V ActiveKid Entries EntryIter : Type}
    (kidInto : core.convert.Into K String)
    (keyInto : core.convert.Into V (alloc.vec.Vec Std.U8))
    (activeKidInto : core.convert.Into ActiveKid String)
    (entriesIntoIter : core.iter.traits.collect.IntoIterator Entries (K × V) EntryIter)
    (active_kid : ActiveKid) (keys : Entries)
    (it : EntryIter) (items : List (K × V))
    (entries : List (String × alloc.vec.Vec Std.U8)) (active : String)
    (h_into_iter : entriesIntoIter.into_iter keys = ok it)
    (h_yields : IterYields entriesIntoIter.iteratorInst.next it items)
    (h_entries : ItemsConvert kidInto keyInto items entries)
    (h_active : activeKidInto.into active_kid = ok active)
    (h_kids_fit : ∀ c ∈ entries, c.1.utf8ByteSize ≤ Usize.max)
    (h_active_fits : active.utf8ByteSize ≤ Usize.max) :
    rmcp.model.request_state.RequestStateCodec.new_with_keyring kidInto keyInto activeKidInto
      entriesIntoIter active_kid keys ⦃
      (result : core.result.Result RequestStateCodec RequestStateError) =>
      match result with
      | .Ok codec =>
        keyringCheck active (entryBytes entries) = .ok () ∧
        (∃ ring rs1_fallbacks, codec.keys = .Ring ring (.Rs2 active) rs1_fallbacks ∧
          rs1_fallbacks.val = [] ∧
          (keyIds ring).Perm (entries.map Prod.fst) ∧
          (∀ c ∈ entries, lookupKey ring c.1 = some c.2.val) ∧
          ∃ c ∈ entries, c.1 = active ∧ lookupKey ring active = some c.2.val) ∧
        CodecValid codec
      | .Err e =>
        ∃ f, keyringCheck active (entryBytes entries) = .error f ∧
          f.Describes e ⦄ :=
  rmcp.model.request_state.RequestStateCodec.new_with_keyring_spec kidInto keyInto activeKidInto
    entriesIntoIter active_kid keys it items entries active h_into_iter h_yields h_entries
    h_active h_kids_fit h_active_fits

/--
info: 'Theorems.request_state.RequestStateCodec.new_with_keyring' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.new_with_keyring
