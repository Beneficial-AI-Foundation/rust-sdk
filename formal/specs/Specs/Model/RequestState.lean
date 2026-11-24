/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Defs
public import Proofs.Model.RequestState.Public

@[expose] public section

/-!
# Spec file for crates/rmcp/src/model/request_state.rs (public API: R01–R08)

Summary (one row per theorem below; index of all guarantees: `formal/specs/README.md`). A row
about a call `f x ⦃ r => P r ⦄` says that the call does not panic and that its result satisfies
the guarantee (`RequestStateCodec::` abbreviated `Codec::`).

| ID | Function | Guarantee | Assumptions |
|---|---|---|---|
| R01 | `SealOptions::new` | no associated data, no time-to-live | none |
| R02 | `SealOptions::associated_data` | sets the associated data, keeps the ttl | none |
| R03 | `SealOptions::ttl` | sets the ttl to `Some ttl`, keeps the associated data | none |
| R04 | `Codec::new` | single-key codec of `key.into()`, any length | `into` returns |
| R05 | `Codec::new_unchecked` | single-key codec of `key.into()`, any length | `into` returns |
| R06 | `Codec::try_new` | that codec if key ≥ 32 bytes, else `KeyTooShort` | `into` returns |
| R07 | `Codec::open` | exactly `openAt` with no associated data at `nowMs` | (F); (K), (H) |
| R08 | `Codec::open_with` | exactly `openAt` at `nowMs` | (T), (F); (K), (H), (V) |
| R08, cor. | `Codec::open_with` | as R08 | (L), (F); (K), (H), (V) |

Assumption keys (those of the internal E11 statement, `proofs/Proofs/Internal/Model/
RequestState.lean`): (T) the MAC transcript fits in `usize::MAX` bytes (the bound of the Lean
model of `Vec::extend_from_slice`); (F) every rs1 fallback id of a keyring codec is a key id
(`Defs.CodecState.CodecFallbacksKnown`), needed only for a token whose first `.`-component is
`rs1` (else the code's `expect` panics, patched line 652, upstream 661); (L) associated data
plus token plus 36 bytes fit in `usize::MAX` (implies (T)). "`into` returns": the caller's
`Into<Vec<u8>>` conversion returns the vector `v` (it is user code, which may panic).
`nowMs` is `ExtModel.nowMs`; (K), (H), (V) are inherited exceptions, not premises (below).

This file holds the public API of `request_state.rs` (functions `pub` in upstream rmcp; human
decision 2026-11-24): the eight public functions that are translated but were not Phase 1
targets (plan Section 2.3, "Consequences"), plus one corollary of R08 with a simpler premise
(`open_with_spec_of_length_le`). The private functions E01–E11, E09a and the round trips are in
`formal/proofs/Proofs/Internal/Model/RequestState.lean`. Each statement is restated as a theorem
`Theorems.request_state.<Type>.<function>` proved by the spec theorem in
`Proofs/Model/RequestState/Public.lean` and followed by the assumptions its proof depends on,
checked by `#print axioms` under `#guard_msgs`. Signed off by the spec owner on 2026-11-24; the
signed-off text was in `specs/Drafts/RequestState.lean`, removed at incorporation.

Translated configuration (the proofs hold only for it): target `x86_64-unknown-linux-gnu`,
`--no-default-features` with the features `request-state`, `server`, `client`, `client-side-sse`,
`transport-streamable-http-server`, `transport-streamable-http-client` and `auth` (plan
Section 15), with `overflow-checks=true` and `debug-assertions=true` (plan Section 1). Aeneas
`nightly-2026.11.24-fb44cb4` (until 2026-11-24 `nightly-2026.08.20-5d08da4`). The translation base is the patched copy (patch 01 on origin/main
`7caec76`, `formal/trusted/patches/01-request-state-wire.patch`, D2 fallback 2026-11-23). Each
clause cites the line in the patched copy ("patched") and at upstream `7caec76` ("upstream").
The eight functions have the same text in both, ten lines lower upstream (patch 01 removes
import lines above them); the tests cited are twelve lines lower upstream; what the eight
functions call differs only below them (`open_at`, `validate_key_length`, `now_ms`, which moves
55 lines).

Definitions used: `Defs.Wire` (`components`, `versionV1`, `versionV2`, `transcriptV1`,
`transcriptV2`, `minKeyLength`) and `Defs.CodecState` (`CodecValid`, `CodecFallbacksKnown`,
`openAt`, `resultBytes`), all in `formal/specs/Defs/`. No private Rust function is named:
`openAt` is the expected result of opening defined in `Defs.CodecState`, not the translated
private `open_at`.

External models used (`trusted/Rmcp/FunsExternal.lean`): `zeroize::Zeroizing::new` (R04–R06;
wraps the vector unchanged, zeroisation on drop is not modelled, plan Section 4);
`zeroize::Zeroizing::deref` (`zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref`, R06; returns the
wrapped vector, which `try_new` passes to `validate_key_length`); the clock
reading `ExtModel.nowMs` through the model of `RequestStateCodec::now_ms` (R07, R08); and,
through E11, `ExtModel.b64Decode` (also in the premises (T)), `ExtModel.hmacSha256`,
`ExtModel.utf8`, `ExtModel.b64`, `ExtModel.maxStringBytes` and `ExtModel.strOfBytes?`. The proof
of R07 uses the laws `Proofs.External.Base64.b64_of_b64Decode` and
`Proofs.External.Base64.length_b64`, the corollary of R08 the bound
`ExtModel.b64Decode_length_le`.

Native-code assumptions: none since the Aeneas upgrade of 2026-11-24 (its `toStr` checks the
length of a literal in the kernel; `formal/trusted/native-axioms.lock` is empty). Until then R07,
R08 and the corollary reached
`rmcp.model.request_state.RequestStateCodec.rs1_fallbacks_verify_loop.body._native.decide.ax_3`
(through E11). 8 of the 9 `#print axioms` lists below changed in that upgrade (native-code assumption
dropped, standard axioms added), re-signed by the spec owner in the batch of 2026-11-24.

**Clock (human decision 2026-11-24; `formal/README.md`, "Trusted base"; plan Section 4, row
"Clock").** This file is the exception to the rule that no statement names
`RequestStateCodec::open`, `RequestStateCodec::open_with` or `ExtModel.nowMs`. `open` and
`open_with` read the clock once (`Self::now_ms()`, patched line 500, upstream line 510) and open
the token at that reading. The model of `RequestStateCodec::now_ms` (patched lines 729–731,
upstream 784–786) is `ok ExtModel.nowMs`, one opaque `I64` constant. Only the spec theorems of
`open` and `open_with` (R07, R08 and the corollary of R08) and their restatements here name these
two functions and `ExtModel.nowMs`, and only with the postcondition
`resultBytes result = openAt … ExtModel.nowMs.val`; no statement constrains the value of `nowMs`
or involves two clock readings. Each statement is parametric in the clock: `nowMs` is opaque, so
it is E11 at an arbitrary `I64` reading, and it says nothing about two calls (in Rust two calls
read different times; in the model they would see the same constant). The time is not a
parameter the caller controls.

Inherited exceptions: inputs or environments where Rust panics but the model, and so the
statement, promises a result. They are not premises; they are recorded at the models
(plan Section 4, rows "Clock", "HMAC" and "Standard library").
(K) Clock: `chrono::Utc::now` panics if the system clock is before 1970 or outside chrono's
range (`chrono-0.4.45/src/offset/utc.rs` lines 96–98; recorded at the model of `now_ms` in
`trusted/Rmcp/FunsExternal.lean`). Rust evaluates `Self::now_ms()` before `open_at` (patched
line 500, upstream 510), so in such an environment even a malformed token panics.
(H) HMAC: the model of HMAC SHA-256 always succeeds, while the `u64` bit counter of SHA-256
overflows (a panic under `overflow-checks`) for a transcript of at least `2^61 − 64` bytes or a
key of at least `2^61` bytes (`sha2-0.11.1/src/block_api.rs` line 66, recorded at the model
of `prim::hmac_sha256` in `trusted/Rmcp/FunsExternal.lean`; the exception stated for E09 and
E11).
(V) `open_with` only: the transcript `Vec` is modelled up to `usize::MAX` bytes, while Rust
panics above `isize::MAX` bytes. It does not arise for `open`: with no
associated data a transcript has at most `42 + 3n/4` bytes for a token of `n ≤ isize::MAX`
bytes.

A statement `f x ⦃ (result : T) => P result ⦄` says that `f x` terminates without panicking and
that its result satisfies `P` (plan Section 3, "What a spec means"). Every postcondition below
determines the result uniquely (for `open`/`open_with` through the injectivity of
`resultBytes`, `Defs.CodecState`).

Statements here, in Rust source order (patched lines): R01 (153), R02 (163), R03 (170), R04
(278), R05 (286), R06 (298), R07 (476), R08 (495), then the corollary of R08. The translated
functions are written with their full names: inside a theorem named
`Theorems.request_state.<Type>.<function>` a bare name would resolve to a restated theorem.

Not translated (plan Section 2.3): the other public items of `request_state.rs`, among them
`seal`, `seal_with` and the excluded `seal_at`, and the keyring constructors
`new_with_keyring`, `with_rs1_signing` and `with_rs1_fallback`.
-/

open Aeneas Aeneas.Std Result
open Defs.Wire (components versionV1 versionV2 transcriptV1 transcriptV2 minKeyLength)
open Defs.CodecState (CodecValid CodecFallbacksKnown openAt resultBytes)
open rmcp.model.request_state (SealOptions RequestStateCodec Keys RequestStateError)

/-- R01 `SealOptions::new`: empty options, no associated data and no time-to-live. -/
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

/-- R02 `SealOptions::associated_data`: sets the associated data and keeps the time-to-live. -/
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

/-- R03 `SealOptions::ttl`: sets the time-to-live to `Some ttl` and keeps the associated
data. -/
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

/-- R04 `RequestStateCodec::new` (deprecated): the single-key codec of the vector `key.into()`
returns, for a key of any length; it satisfies `CodecValid`. -/
theorem Theorems.request_state.RequestStateCodec.new {T0 : Type}
    (coreconvertIntoT0VecU8Inst : core.convert.Into T0 (alloc.vec.Vec Std.U8)) (key : T0)
    (v : alloc.vec.Vec Std.U8) (h_into : coreconvertIntoT0VecU8Inst.into key = ok v) :
    rmcp.model.request_state.RequestStateCodec.new coreconvertIntoT0VecU8Inst key ⦃
      (result : RequestStateCodec) =>
      result.keys = Keys.Single { inner := v } ∧
      CodecValid result ⦄ :=
  rmcp.model.request_state.RequestStateCodec.new_spec coreconvertIntoT0VecU8Inst key v h_into

/--
info: 'Theorems.request_state.RequestStateCodec.new' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.new

/-- R05 `RequestStateCodec::new_unchecked`: the single-key codec of the vector `key.into()`
returns, for a key of any length; it satisfies `CodecValid`. -/
theorem Theorems.request_state.RequestStateCodec.new_unchecked {T0 : Type}
    (coreconvertIntoT0VecU8Inst : core.convert.Into T0 (alloc.vec.Vec Std.U8)) (key : T0)
    (v : alloc.vec.Vec Std.U8) (h_into : coreconvertIntoT0VecU8Inst.into key = ok v) :
    rmcp.model.request_state.RequestStateCodec.new_unchecked coreconvertIntoT0VecU8Inst key ⦃
      (result : RequestStateCodec) =>
      result.keys = Keys.Single { inner := v } ∧
      CodecValid result ⦄ :=
  rmcp.model.request_state.RequestStateCodec.new_unchecked_spec coreconvertIntoT0VecU8Inst key v
    h_into

/--
info: 'Theorems.request_state.RequestStateCodec.new_unchecked' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.new_unchecked

/-- R06 `RequestStateCodec::try_new`: `Ok` of the single-key codec iff the key has at least 32
bytes, else `KeyTooShort { minimum: 32, actual: key.len() }`. -/
theorem Theorems.request_state.RequestStateCodec.try_new {T0 : Type}
    (coreconvertIntoT0VecU8Inst : core.convert.Into T0 (alloc.vec.Vec Std.U8)) (key : T0)
    (v : alloc.vec.Vec Std.U8) (h_into : coreconvertIntoT0VecU8Inst.into key = ok v) :
    rmcp.model.request_state.RequestStateCodec.try_new coreconvertIntoT0VecU8Inst key ⦃
      (result : core.result.Result RequestStateCodec RequestStateError) =>
      match result with
      | .Ok codec =>
        minKeyLength ≤ v.val.length ∧
        codec.keys = Keys.Single { inner := v } ∧
        CodecValid codec
      | .Err e =>
        v.val.length < minKeyLength ∧
        ∃ minimum actual : Std.Usize, e = .KeyTooShort minimum actual ∧
          minimum.val = minKeyLength ∧ actual.val = v.val.length ⦄ :=
  rmcp.model.request_state.RequestStateCodec.try_new_spec coreconvertIntoT0VecU8Inst key v h_into

/--
info: 'Theorems.request_state.RequestStateCodec.try_new' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.try_new

/-- R07 `RequestStateCodec::open`: exactly `openAt` with no associated data at the clock reading
`ExtModel.nowMs` (one reading, parametric; nothing about two calls). Premise (F) only;
inherited exceptions (K), (H). -/
theorem Theorems.request_state.RequestStateCodec.open (self : RequestStateCodec) (sealed : Str)
    (h_fallbacks : (components (sealed : Slice Std.U8).val).head? = some versionV1 →
      CodecFallbacksKnown self) :
    rmcp.model.request_state.RequestStateCodec.open self sealed ⦃ (result :
        core.result.Result (alloc.vec.Vec Std.U8) RequestStateError) =>
      resultBytes result = openAt self (sealed : Slice Std.U8).val [] ExtModel.nowMs.val ⦄ :=
  rmcp.model.request_state.RequestStateCodec.open_spec self sealed h_fallbacks

/--
info: 'Theorems.request_state.RequestStateCodec.open' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.open

/-- R08 `RequestStateCodec::open_with`: exactly `openAt` at the clock reading `ExtModel.nowMs`
(one reading, parametric; nothing about two calls). Premises (T), (F); inherited exceptions
(K), (H), (V). -/
theorem Theorems.request_state.RequestStateCodec.open_with (self : RequestStateCodec)
    (sealed : Str) (associated_data : Slice Std.U8)
    (h_len1 : ∀ b t body, components (sealed : Slice Std.U8).val = [versionV1, b, t] →
      ExtModel.b64Decode b = some body →
      (transcriptV1 associated_data.val body).length ≤ Usize.max)
    (h_len2 : ∀ k b t kid body, components (sealed : Slice Std.U8).val = [versionV2, k, b, t] →
      ExtModel.b64Decode k = some kid → ExtModel.b64Decode b = some body →
      (transcriptV2 kid associated_data.val body).length ≤ Usize.max)
    (h_fallbacks : (components (sealed : Slice Std.U8).val).head? = some versionV1 →
      CodecFallbacksKnown self) :
    rmcp.model.request_state.RequestStateCodec.open_with self sealed associated_data ⦃ (result :
        core.result.Result (alloc.vec.Vec Std.U8) RequestStateError) =>
      resultBytes result =
        openAt self (sealed : Slice Std.U8).val associated_data.val ExtModel.nowMs.val ⦄ :=
  rmcp.model.request_state.RequestStateCodec.open_with_spec self sealed associated_data h_len1
    h_len2 h_fallbacks

/--
info: 'Theorems.request_state.RequestStateCodec.open_with' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.open_with

/-- R08, corollary: `open_with` as in R08, exactly `openAt` at the clock reading
`ExtModel.nowMs` (one reading, parametric; nothing about two calls), with the transcript
premises (T) replaced by (L): `associated_data.len() + sealed.len() + 36 ≤ usize::MAX`.
Premise (F); inherited exceptions (K), (H), (V). -/
theorem Theorems.request_state.RequestStateCodec.open_with_of_length_le
    (self : RequestStateCodec) (sealed : Str) (associated_data : Slice Std.U8)
    (h_len : associated_data.val.length + (sealed : Slice Std.U8).val.length + 36 ≤ Usize.max)
    (h_fallbacks : (components (sealed : Slice Std.U8).val).head? = some versionV1 →
      CodecFallbacksKnown self) :
    rmcp.model.request_state.RequestStateCodec.open_with self sealed associated_data ⦃ (result :
        core.result.Result (alloc.vec.Vec Std.U8) RequestStateError) =>
      resultBytes result =
        openAt self (sealed : Slice Std.U8).val associated_data.val ExtModel.nowMs.val ⦄ :=
  rmcp.model.request_state.RequestStateCodec.open_with_spec_of_length_le self sealed
    associated_data h_len h_fallbacks

/--
info: 'Theorems.request_state.RequestStateCodec.open_with_of_length_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.open_with_of_length_le
