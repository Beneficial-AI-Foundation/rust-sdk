/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Defs
public import Defs.Wire
public import Defs.RequestState
public import Defs.CodecState
public import Proofs.Model.RequestState.OpenAuthenticatedBody
public import Proofs.Model.RequestState.ValidateKeyLength
public import Proofs.Model.RequestState.ValidateConfigKid
public import Proofs.Model.RequestState.B64Len
public import Proofs.Model.RequestState.OpenAt
public import Proofs.Model.RequestState.SealRs1
public import Proofs.Model.RequestState.SealRs2
public import Proofs.Model.RequestState.OpenRs1At
public import Proofs.Model.RequestState.Rs1FallbacksVerify
public import Proofs.Model.RequestState.OpenRs2At
public import Proofs.Model.RequestState.Seal
public import Proofs.Model.RequestState.Roundtrip
public import Proofs.Model.RequestState.Public
public import Proofs.Model.RequestState.OpenJson

@[expose] public section

/-!
# Internal spec file for model/request_state.rs (E01–E11, S15, R10a, R10b, R05, R08, R10, R14)

These are guarantees about private associated functions of `RequestStateCodec` (without `pub`)
and, in the last section, about the intermediate public functions R05 `new_unchecked`, R08
`open_with`, R10 `seal_with` and R14 `open_json_with` (called by a top-level public function),
kept out of `formal/specs/`, which holds only the top-level public API (human decisions
2026-11-24, 2026-11-28); the top-level public functions (`seal`, `open`, `try_new`, …) are in
`formal/specs/Specs/Model/RequestState.lean`. E09a `rs1_fallbacks_verify` is
patch-only: patch 01 moves the rs1 fallback loop of `open_rs1_at` into it, so it has no upstream
counterpart. Index of all guarantees: `formal/specs/README.md`.

| ID | Function | Guarantee | Assumptions |
|---|---|---|---|
| E11 | `open_at` | exactly `openAt`: `rs1` → E09, `rs2` → E10, else `MalformedFormat` | (T), (F) |
| E07 | `seal_rs1` | `rs1.b64(body).b64(tag)`, tag = HMAC of `transcriptV1(ad, body)` | (T), (C) |
| E08 | `seal_rs2` | `rs2.b64(kid).b64(body).b64(tag)`, HMAC of `transcriptV2` | (T), (C) |
| E09 | `open_rs1_at` | exactly `openRs1` (plan Section 3 error order, then E01) | (D), (T), (F) |
| E09a | `rs1_fallbacks_verify` | `true` iff some rs1 fallback key verifies the tag | (F) |
| E10 | `open_rs2_at` | exactly `openRs2` (plan Section 3 error order, then E01) | (D), (T) |
| E01 | `open_authenticated_body` | `MalformedFormat` if under 8 bytes, else (n) | none |
| E03 | `validate_key_length` | `Ok` iff ≥ 32 bytes, else `KeyTooShort { 32, len }` | none |
| E04 | `validate_config_kid` | `Ok` iff 1 to 255 UTF-8 bytes, else `InvalidKeyring(msg)` | none |
| E02 | `b64_len` | `4 * ((len + 2) / 3)`, as W01 | no overflow |
| S15 | `rs1_roundtrip` | `seal_rs1`, then `open_rs1_at` (same `ad`): `Ok(body[8..])` | (R1) |
| S15 | `rs2_roundtrip` | `seal_rs2`, then `open_rs2_at` (same `ad`): `Ok(body[8..])` | (R2) |
| S15 | `open_at_roundtrip_rs1` | `seal_rs1`, then `open_at` (same `ad`): `Ok(body[8..])` | (R1) |
| S15 | `open_at_roundtrip_rs2` | `seal_rs2`, then `open_at` (same `ad`): `Ok(body[8..])` | (R2) |
| R10a | `seal_at` | `sealAt` at an explicit time | (S), (D) (section "R10a, R10b …") |
| R10b | `seal_at_roundtrip` | `seal_at` at `now`, then `open_at` at `now'` (same `ad`): `Ok(payload)` | `CodecValid`, `h_rs1`, (D), not expired |
| R10b model | `openAt_eq_ok_of_sealAt_eq_some` | `openAt` of a `sealAt` token is the payload | `CodecValid`, `h_rs1`, not expired |
| R05, R08, R10, R14 | `new_unchecked`, `open_with`, `seal_with`, `open_json_with` | as stated in the section "Intermediate public functions", with its own table | (last section) |

Each row says that the call (for the round trips: sealing, then opening any `str` holding the
token's bytes) does not panic and that its result satisfies the guarantee, within the HMAC and
allocation exceptions below. HMAC is HMAC-SHA256 under `key` (the opaque model
`ExtModel.hmacSha256`); `b64` is unpadded Base64url; `ad` is the associated data. `openAt`,
`openRs1`, `openRs2` are `Defs.CodecState` definitions; E09: `MalformedFormat` unless the token
is `rs1.b.t`, `UnknownKeyId` for a keyring without rs1 fallback, `InvalidEncoding` for a
non-canonical Base64url `b` or `t`, `IntegrityCheckFailed` unless an accepted key verifies the
tag, then E01. E10: `MalformedFormat`, then `InvalidKeyId` (encoded kid over 340 bytes),
`InvalidEncoding` (kid), `InvalidKeyId` (kid of 0 or over 255 bytes, or not UTF-8),
`UnknownKeyId` (single-key codec or unknown kid), `InvalidEncoding` (body, tag),
`IntegrityCheckFailed`, then E01. E04's two messages are `KID_EMPTY_MSG` (length 0) and
`KID_TOO_LONG_MSG` (over 255). (n) `Expired` if the expiry (the signed big-endian value of the
first 8 bytes) is non-zero and `now_ms` is later, else `Ok` of the bytes after the first 8.

Assumption keys (the same as in `formal/specs/README.md`): (T) the MAC transcript fits in
`usize::MAX` bytes; (C) the `with_capacity` sum (version, dots and the Base64 lengths of kid,
body and a 32-byte tag) is at most `isize::MAX` bytes (`ExtModel.maxStringBytes`, the largest
Rust `String`); (D) the token has fewer than `usize::MAX` `.` bytes; (F) every rs1 fallback id
is a key id: of a keyring codec (`CodecFallbacksKnown`) for E09 and E11 (E11 needs it only for a
token starting with `rs1`), of the arguments (`FallbacksKnown`) for E09a (else the code's
`expect` panics; not proved); (R1) the same associated data in both calls; (T), (C), body of at
least 8 bytes, not expired at `now_ms`, the key is the codec's single key or the key of one of
its rs1 fallback ids, and (F); (R2) the same associated data in both calls; (T), (C), body of at
least 8 bytes, not expired at `now_ms`, the kid is UTF-8 of 1 to 255 bytes and the codec is a
keyring that maps it to the key. Used by (upstream names): `open`/`open_with` (E11 and below; E09a
through E09, in the patched copy), `seal`/`seal_with` through the excluded `seal_at` (E07, E08,
E02), `try_new` and `new_with_keyring` (E03, E04); those public functions are verified too (R01–R15:
top-level ones in `formal/specs/Specs/Model/RequestState.lean`, intermediate ones in the last
section).

Statements of the codec functions of `RequestStateCodec` (plan Section 2.2), in Rust source
order, each restated as a theorem `Theorems.request_state.RequestStateCodec.<function>` proved by
the spec theorem in `Proofs/Model/RequestState/` and followed by
the assumptions its proof depends on, checked by `#print axioms` under `#guard_msgs`. The
statements were signed off by the spec owner on 2026-11-23 (the S05 evidence, git history at
223ff12); their signed-off text is the one restated here (git history at `9bd8144`).

Translated configuration (the proofs hold only for it): target `x86_64-unknown-linux-gnu`,
`--no-default-features` with the features `request-state`, `server`, `client`, `client-side-sse`,
`transport-streamable-http-server`, `transport-streamable-http-client` and `auth` (widened for
Phase 2, plan Section 15; the translation of this file's targets is unchanged), with
`overflow-checks=true` and `debug-assertions=true` (plan Section 1), so arithmetic overflow
panics, which Aeneas models as failure. Aeneas `nightly-2026.11.24-fb44cb4` (until 2026-11-24
`nightly-2026.08.20-5d08da4`); the translation base is the patched copy (patch 01 on origin/main 7caec76,
`formal/trusted/patches/01-request-state-wire.patch`, D2 fallback 2026-11-23; translation
committed at `9bd8144`). Line numbers refer to `request_state.rs` in the patched copy.

Definitions used, in the modules `Defs.Wire`, `Defs.CodecState` and `Defs.RequestState`
(`formal/specs/Defs/`, used by public statements too):
`Defs.Wire` (`expiryLen`, `bodyExpiry`, `Expired`, `minKeyLength`, `maxKidLen`, `b64Len`, `dot`,
`components`, `versionV1`, `versionV2`, `transcriptV1`, `transcriptV2`), `Defs.RequestState`
(`StrIs`, `kidEmptyMsg`, `kidTooLongMsg`) and `Defs.CodecState` (`KeyTable`, `FallbacksKnown`,
`CodecFallbacksKnown`, `Rs1Verifies`, `openRs1`, `openRs2`, `openAt`, `resultBytes`,
`lookupKey`).

External models used (S08–S09, `trusted/Rmcp/FunsExternal.lean`): E04 uses the model of
`core.str.Str.len` (the byte length of the `Str`). Until the Aeneas upgrade of 2026-11-24, E04
also depended on the native-code assumptions `KID_EMPTY_MSG._native.decide.ax_1` and
`KID_TOO_LONG_MSG._native.decide.ax_1`, which the Aeneas `toStr` of `nightly-2026.08.20-5d08da4`
declared for the two message literals of the translation; the `toStr` of
`nightly-2026.11.24-fb44cb4` checks the length in the kernel and declares none
(`trusted/native-axioms.lock` is empty).

External models used by E07–E11 and E09a: `ExtModel.utf8`, `ExtModel.b64`, `ExtModel.b64Decode`,
`ExtModel.hmacSha256`, `ExtModel.maxStringBytes`, `ExtModel.strOfBytes?`. Stated exceptions (plan
Section 4, rows "HMAC" and "Standard library"): HMAC SHA-256 always succeeds in the model, while
its `u64` bit-length counter overflows (a panic under overflow-checks) for a message of at least
`2^61 - 64` bytes or a key of at least `2^61` bytes; allocation failure is not modelled, and the
transcript `Vec` is modelled up to `Usize.max` bytes where Rust panics above `isize::MAX`. For
such inputs a statement promises a result where the Rust code panics. In E07/E08, `h_len` is (T),
the bound of the Lean model of `Vec::extend_from_slice` on the transcript, and `h_cap` is (C), the
`String` capacity limit `isize::MAX` above which `String::with_capacity` panics (capacity
overflow); it also keeps the `usize` sum from overflowing. No statement here reaches a
native-code assumption since the Aeneas upgrade of 2026-11-24. Until then E07 and E08 reached the
locked native-code assumptions `VERSION_V1._native.decide.ax_1` and
`VERSION_V2._native.decide.ax_1`, and E09, E09a and E11 reached
`RequestStateCodec.rs1_fallbacks_verify_loop.body._native.decide.ax_3`; E10 reached none. The 10
`#print axioms` lists below that changed in that upgrade (native-code assumptions dropped) await
the human batch re-sign-off.

Statements here, in Rust source order: E11 (line 559), E07 (572), E08 (585), E09 (607),
E09a (644), E10 (659) (S11, S13, S14), then E01 (695), E03 (704), E04 (714), E02 (725) (S07).
The E07–E11 and E09a statements were signed off by the spec owner on 2026-11-23 after three
review rounds (the S05 evidence, git history at 223ff12, "E batch part 2"); their signed-off
statements are the ones in this project file.

Composition theorems last (S15, proofs in `Proofs/Model/RequestState/Roundtrip.lean`):
`rs1_roundtrip`, `rs2_roundtrip`, `open_at_roundtrip_rs1`, `open_at_roundtrip_rs2`. Each says that
sealing terminates, that some `Str` holds the token's bytes, and that opening any such `Str`
returns `Ok (body[8..])`, under the plan Section 3 round-trip conditions and the seal statements'
own size premises. Signed off by the spec owner on 2026-11-23 after two review rounds
(the S15 evidence, git history at 223ff12). Until the Aeneas upgrade of 2026-11-24 the rs1 ones
reached `VERSION_V1._native.decide.ax_1` and
`RequestStateCodec.rs1_fallbacks_verify_loop.body._native.decide.ax_3`, `rs2_roundtrip`
reached `VERSION_V2._native.decide.ax_1` and `open_at_roundtrip_rs2` both `VERSION_V2…` and
`…ax_3`; since then they reach no native-code assumption.
-/

open Aeneas Aeneas.Std Result
open Defs.Wire
open rmcp.model.request_state  -- for `RequestStateError`; theorems named in full
open Defs.CodecState (KeyTable FallbacksKnown CodecFallbacksKnown Rs1Verifies openRs1 openRs2
  openAt resultBytes lookupKey)

open rmcp.model.request_state.RequestStateCodec (open_at) in
/-- E11 `open_at`: dispatches on the first `.`-component of the token, `"rs1"` to E09 and
`"rs2"` to E10, anything else to `MalformedFormat`; the result is exactly `openAt`. -/
theorem Theorems.request_state.RequestStateCodec.open_at
    (self : RequestStateCodec) (sealed : Str) (associated_data : Slice Std.U8)
    (now_ms : Std.I64)
    (h_len1 : ∀ b t body, components (sealed : Slice Std.U8).val = [versionV1, b, t] →
      ExtModel.b64Decode b = some body →
      (transcriptV1 associated_data.val body).length ≤ Usize.max)
    (h_len2 : ∀ k b t kid body, components (sealed : Slice Std.U8).val = [versionV2, k, b, t] →
      ExtModel.b64Decode k = some kid → ExtModel.b64Decode b = some body →
      (transcriptV2 kid associated_data.val body).length ≤ Usize.max)
    (h_fallbacks : (components (sealed : Slice Std.U8).val).head? = some versionV1 →
      CodecFallbacksKnown self) :
    open_at self sealed associated_data now_ms ⦃ (result :
        core.result.Result (alloc.vec.Vec Std.U8) RequestStateError) =>
      -- lines 565–568; `openAt` (Defs.CodecState) dispatches on `(components _).head?`
      resultBytes result = openAt self (sealed : Slice Std.U8).val associated_data.val
        now_ms.val ⦄ :=
  rmcp.model.request_state.RequestStateCodec.open_at_spec self sealed associated_data now_ms
    h_len1 h_len2 h_fallbacks

/--
info: 'Theorems.request_state.RequestStateCodec.open_at' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.open_at

/-- E07 `seal_rs1`: the token `"rs1." ++ b64 body ++ "." ++ b64 tag` as UTF-8 bytes, where `tag`
is the HMAC SHA-256 of `transcriptV1 associated_data body` under `key`. -/
theorem Theorems.request_state.RequestStateCodec.seal_rs1 (key : Slice Std.U8)
    (associated_data : Slice Std.U8)
    (body : Slice Std.U8)
    (h_len : (transcriptV1 associated_data.val body.val).length ≤ Usize.max)
    (h_cap : versionV1.length + 2 + b64Len body.val.length + b64Len 32 ≤
      ExtModel.maxStringBytes) :
    rmcp.model.request_state.RequestStateCodec.seal_rs1 key associated_data body ⦃
      (result : String) =>
      -- lines 577–582: "rs1", '.', b64(body), '.', b64(tag); tag from line 573
      ExtModel.utf8 result =
        versionV1 ++ [dot] ++ ExtModel.b64 body.val ++ [dot] ++
          ExtModel.b64 (ExtModel.hmacSha256 key.val
            (transcriptV1 associated_data.val body.val)).val ⦄ :=
  rmcp.model.request_state.RequestStateCodec.seal_rs1_spec key associated_data body h_len h_cap

/--
info: 'Theorems.request_state.RequestStateCodec.seal_rs1' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.seal_rs1

/-- E08 `seal_rs2`: the token `"rs2." ++ b64 kid ++ "." ++ b64 body ++ "." ++ b64 tag` as UTF-8
bytes, where `tag` is the HMAC SHA-256 of `transcriptV2 kid associated_data body` under `key`;
any kid is accepted. -/
theorem Theorems.request_state.RequestStateCodec.seal_rs2 (kid : Str) (key : Slice Std.U8)
    (associated_data : Slice Std.U8)
    (body : Slice Std.U8)
    (h_len : (transcriptV2 (kid : Slice Std.U8).val associated_data.val body.val).length ≤
      Usize.max)
    (h_cap : versionV2.length + 3 + b64Len (kid : Slice Std.U8).val.length +
      b64Len body.val.length + b64Len 32 ≤ ExtModel.maxStringBytes) :
    rmcp.model.request_state.RequestStateCodec.seal_rs2 kid key associated_data body ⦃
      (result : String) =>
      -- lines 597–604: "rs2", '.', b64(kid), '.', b64(body), '.', b64(tag); tag from 586–589
      ExtModel.utf8 result =
        versionV2 ++ [dot] ++ ExtModel.b64 (kid : Slice Std.U8).val ++ [dot] ++
          ExtModel.b64 body.val ++ [dot] ++
          ExtModel.b64 (ExtModel.hmacSha256 key.val
            (transcriptV2 (kid : Slice Std.U8).val associated_data.val body.val)).val ⦄ :=
  rmcp.model.request_state.RequestStateCodec.seal_rs2_spec kid key associated_data body h_len
    h_cap

/--
info: 'Theorems.request_state.RequestStateCodec.seal_rs2' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.seal_rs2

/-- E09 `open_rs1_at`: the result is exactly `openRs1` (the error order of plan Section 3, then
E01 on the authenticated body). -/
theorem Theorems.request_state.RequestStateCodec.open_rs1_at (self : RequestStateCodec)
    (sealed : Str) (associated_data : Slice Std.U8) (now_ms : Std.I64)
    (h_count : (sealed : Slice Std.U8).val.count dot < Usize.max)
    (h_len : ∀ b t body, components (sealed : Slice Std.U8).val = [versionV1, b, t] →
      ExtModel.b64Decode b = some body →
      (transcriptV1 associated_data.val body).length ≤ Usize.max)
    (h_fallbacks : CodecFallbacksKnown self) :
    rmcp.model.request_state.RequestStateCodec.open_rs1_at self sealed associated_data now_ms ⦃
        (result : core.result.Result (alloc.vec.Vec Std.U8) RequestStateError) =>
      -- lines 613–640, in the order of plan Section 3 (see `Defs.CodecState.openRs1`)
      resultBytes result = openRs1 self (sealed : Slice Std.U8).val associated_data.val
        now_ms.val ⦄ :=
  rmcp.model.request_state.RequestStateCodec.open_rs1_at_spec self sealed associated_data now_ms
    h_count h_len h_fallbacks

/--
info: 'Theorems.request_state.RequestStateCodec.open_rs1_at' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.open_rs1_at

/-- E09a `rs1_fallbacks_verify`: `true` iff some rs1 fallback key verifies the tag over the
transcript (`Rs1Verifies`). -/
theorem Theorems.request_state.RequestStateCodec.rs1_fallbacks_verify (keys : KeyTable)
    (rs1_fallbacks : Slice String) (transcript : Slice Std.U8) (tag : Slice Std.U8)
    (h_known : FallbacksKnown keys rs1_fallbacks.val) :
    rmcp.model.request_state.RequestStateCodec.rs1_fallbacks_verify keys rs1_fallbacks transcript
        tag ⦃ (result : Bool) =>
      -- lines 650–656: `verified |= hmac_sha256_verify(key, transcript, tag)` over all ids
      result = decide (Rs1Verifies keys rs1_fallbacks.val transcript.val tag.val) ⦄ :=
  rmcp.model.request_state.RequestStateCodec.rs1_fallbacks_verify_spec keys rs1_fallbacks
    transcript tag h_known

/--
info: 'Theorems.request_state.RequestStateCodec.rs1_fallbacks_verify' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.rs1_fallbacks_verify

/-- E10 `open_rs2_at`: the result is exactly `openRs2` (the error order of plan Section 3, then
E01 on the decoded body), for every codec. -/
theorem Theorems.request_state.RequestStateCodec.open_rs2_at (self : RequestStateCodec)
    (sealed : Str)
    (associated_data : Slice Std.U8) (now_ms : Std.I64)
    (h_count : (sealed : Slice Std.U8).val.count dot < Usize.max)
    (h_len : ∀ k b t kid body, components (sealed : Slice Std.U8).val = [versionV2, k, b, t] →
      ExtModel.b64Decode k = some kid → ExtModel.b64Decode b = some body →
      (transcriptV2 kid associated_data.val body).length ≤ Usize.max) :
    rmcp.model.request_state.RequestStateCodec.open_rs2_at self sealed associated_data
        now_ms ⦃ (result :
        core.result.Result (alloc.vec.Vec Std.U8) RequestStateError) =>
      -- lines 665–692, in the order of plan Section 3 (see `Defs.CodecState.openRs2`)
      resultBytes result = openRs2 self (sealed : Slice Std.U8).val associated_data.val
        now_ms.val ⦄ :=
  rmcp.model.request_state.RequestStateCodec.open_rs2_at_spec self sealed associated_data now_ms
    h_count h_len

/--
info: 'Theorems.request_state.RequestStateCodec.open_rs2_at' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.open_rs2_at

/-- E01 `open_authenticated_body`: `MalformedFormat` below 8 bytes, otherwise `Expired` if the
body's expiry has passed, otherwise `Ok` of the bytes after the first 8. -/
theorem Theorems.request_state.RequestStateCodec.open_authenticated_body
    (body : alloc.vec.Vec Std.U8) (now_ms : Std.I64) :
    rmcp.model.request_state.RequestStateCodec.open_authenticated_body body now_ms ⦃ (result :
        core.result.Result (alloc.vec.Vec Std.U8) RequestStateError) =>
      match result with
      | .Ok payload =>
        expiryLen ≤ body.val.length ∧
        ¬ Expired (bodyExpiry body.val) now_ms.val ∧
        payload.val = body.val.drop expiryLen
      | .Err e =>
        (body.val.length < expiryLen ∧ e = .MalformedFormat) ∨
        (expiryLen ≤ body.val.length ∧ Expired (bodyExpiry body.val) now_ms.val ∧
          e = .Expired) ⦄ :=
  rmcp.model.request_state.RequestStateCodec.open_authenticated_body_spec body now_ms

/--
info: 'Theorems.request_state.RequestStateCodec.open_authenticated_body' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.open_authenticated_body

/-- E03 `validate_key_length`: `Ok ()` iff the key has at least `MIN_KEY_LENGTH = 32` bytes,
otherwise `KeyTooShort { minimum: 32, actual: key.len() }`. -/
theorem Theorems.request_state.RequestStateCodec.validate_key_length (key : Slice Std.U8) :
    rmcp.model.request_state.RequestStateCodec.validate_key_length key ⦃ (result :
        core.result.Result Unit RequestStateError) =>
      match result with
      | .Ok _ => minKeyLength ≤ key.val.length
      | .Err e =>
        key.val.length < minKeyLength ∧
        ∃ minimum actual : Std.Usize, e = .KeyTooShort minimum actual ∧
          minimum.val = minKeyLength ∧ actual.val = key.val.length ⦄ :=
  rmcp.model.request_state.RequestStateCodec.validate_key_length_spec key

/--
info: 'Theorems.request_state.RequestStateCodec.validate_key_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.validate_key_length

/-- E04 `validate_config_kid`: `Ok ()` iff the UTF-8 byte length of `kid` is in `1..=255`; a
length of `0` gives `InvalidKeyring` with the text of `KID_EMPTY_MSG`, a length above 255 gives
`InvalidKeyring` with the text of `KID_TOO_LONG_MSG`. -/
theorem Theorems.request_state.RequestStateCodec.validate_config_kid (kid : Str) :
    rmcp.model.request_state.RequestStateCodec.validate_config_kid kid ⦃ (result :
        core.result.Result Unit RequestStateError) =>
      match result with
      | .Ok _ =>
        1 ≤ (kid : Slice Std.U8).val.length ∧ (kid : Slice Std.U8).val.length ≤ maxKidLen
      | .Err e =>
        ((kid : Slice Std.U8).val.length = 0 ∧
          ∃ msg, e = .InvalidKeyring msg ∧ Defs.RequestState.StrIs msg
            Defs.RequestState.kidEmptyMsg) ∨
        (maxKidLen < (kid : Slice Std.U8).val.length ∧
          ∃ msg, e = .InvalidKeyring msg ∧ Defs.RequestState.StrIs msg
            Defs.RequestState.kidTooLongMsg) ⦄ :=
  rmcp.model.request_state.RequestStateCodec.validate_config_kid_spec kid

/--
info: 'Theorems.request_state.RequestStateCodec.validate_config_kid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.validate_config_kid

/-- E02 `b64_len`: equals W01; on the no-overflow domain `b64Len len ≤ Usize.max`, the result is
`b64Len len = 4 * ((len + 2) / 3)`. -/
theorem Theorems.request_state.RequestStateCodec.b64_len (len : Std.Usize)
    (h_no_overflow : b64Len len.val ≤ Usize.max) :
    rmcp.model.request_state.RequestStateCodec.b64_len len ⦃ (result : Std.Usize) =>
      result.val = b64Len len.val ⦄ :=
  rmcp.model.request_state.RequestStateCodec.b64_len_spec len h_no_overflow

/--
info: 'Theorems.request_state.RequestStateCodec.b64_len' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.b64_len

/-- S15 `rs1_roundtrip`: sealing with E07 `seal_rs1` and opening any `Str` holding the token's
bytes with E09 `open_rs1_at` (same associated data, accepted key, body of at least 8 bytes, not
expired) returns `Ok (body[8..])`. -/
theorem Theorems.request_state.RequestStateCodec.rs1_roundtrip (self : RequestStateCodec)
    (key : Slice Std.U8) (associated_data : Slice Std.U8) (body : Slice Std.U8)
    (now_ms : Std.I64)
    (h_len : (transcriptV1 associated_data.val body.val).length ≤ Usize.max)
    (h_cap : versionV1.length + 2 + b64Len body.val.length + b64Len 32 ≤
      ExtModel.maxStringBytes)
    (h_body : expiryLen ≤ body.val.length)
    (h_expiry : ¬ Expired (bodyExpiry body.val) now_ms.val)
    (h_key : (∃ k, self.keys = .Single k ∧ k.inner.val = key.val) ∨
      (∃ keys seal_mode rs1_fallbacks kid, self.keys = .Ring keys seal_mode rs1_fallbacks ∧
        kid ∈ rs1_fallbacks.val ∧ lookupKey keys kid = some key.val))
    (h_fallbacks : CodecFallbacksKnown self) :
    rmcp.model.request_state.RequestStateCodec.seal_rs1 key associated_data body ⦃
      (token : String) =>
      (∃ sealed : Str, (sealed : Slice Std.U8).val = ExtModel.utf8 token) ∧
      ∀ sealed : Str, (sealed : Slice Std.U8).val = ExtModel.utf8 token →
      rmcp.model.request_state.RequestStateCodec.open_rs1_at self sealed associated_data
        now_ms ⦃ (result : core.result.Result (alloc.vec.Vec Std.U8) RequestStateError) =>
        -- line 640 → E01 line 698: `Ok(payload.to_vec())`, payload = body[8..]
        resultBytes result = .ok (body.val.drop expiryLen) ⦄ ⦄ :=
  rmcp.model.request_state.RequestStateCodec.rs1_roundtrip self key associated_data body now_ms
    h_len h_cap h_body h_expiry h_key h_fallbacks

/--
info: 'Theorems.request_state.RequestStateCodec.rs1_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.rs1_roundtrip

/-- S15 `rs2_roundtrip`: sealing with E08 `seal_rs2` and opening any `Str` holding the token's
bytes with E10 `open_rs2_at` (same associated data, UTF-8 kid of 1 to 255 bytes that the ring maps
to the key, body of at least 8 bytes, not expired) returns `Ok (body[8..])`. -/
theorem Theorems.request_state.RequestStateCodec.rs2_roundtrip (self : RequestStateCodec)
    (kid : Str) (key : Slice Std.U8) (associated_data : Slice Std.U8) (body : Slice Std.U8)
    (now_ms : Std.I64) (kidStr : String)
    (h_len : (transcriptV2 (kid : Slice Std.U8).val associated_data.val body.val).length ≤
      Usize.max)
    (h_cap : versionV2.length + 3 + b64Len (kid : Slice Std.U8).val.length +
      b64Len body.val.length + b64Len 32 ≤ ExtModel.maxStringBytes)
    (h_body : expiryLen ≤ body.val.length)
    (h_expiry : ¬ Expired (bodyExpiry body.val) now_ms.val)
    (h_kid_utf8 : (kid : Slice Std.U8).val = ExtModel.utf8 kidStr)
    (h_kid_len : 1 ≤ (kid : Slice Std.U8).val.length ∧
      (kid : Slice Std.U8).val.length ≤ maxKidLen)
    (h_key : ∃ keys seal_mode rs1_fallbacks, self.keys = .Ring keys seal_mode rs1_fallbacks ∧
      lookupKey keys kidStr = some key.val) :
    rmcp.model.request_state.RequestStateCodec.seal_rs2 kid key associated_data body ⦃
      (token : String) =>
      (∃ sealed : Str, (sealed : Slice Std.U8).val = ExtModel.utf8 token) ∧
      ∀ sealed : Str, (sealed : Slice Std.U8).val = ExtModel.utf8 token →
      rmcp.model.request_state.RequestStateCodec.open_rs2_at self sealed associated_data
        now_ms ⦃ (result : core.result.Result (alloc.vec.Vec Std.U8) RequestStateError) =>
        -- line 692 → E01 line 698: `Ok(payload.to_vec())`, payload = body[8..]
        resultBytes result = .ok (body.val.drop expiryLen) ⦄ ⦄ :=
  rmcp.model.request_state.RequestStateCodec.rs2_roundtrip self kid key associated_data body
    now_ms kidStr h_len h_cap h_body h_expiry h_kid_utf8 h_kid_len h_key

/--
info: 'Theorems.request_state.RequestStateCodec.rs2_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.rs2_roundtrip

/-- S15 `open_at_roundtrip_rs1`: sealing with E07 `seal_rs1` and opening any `Str` holding the
token's bytes with E11 `open_at` returns `Ok (body[8..])`, under the premises of
`rs1_roundtrip`. -/
theorem Theorems.request_state.RequestStateCodec.open_at_roundtrip_rs1 (self : RequestStateCodec)
    (key : Slice Std.U8) (associated_data : Slice Std.U8) (body : Slice Std.U8)
    (now_ms : Std.I64)
    (h_len : (transcriptV1 associated_data.val body.val).length ≤ Usize.max)
    (h_cap : versionV1.length + 2 + b64Len body.val.length + b64Len 32 ≤
      ExtModel.maxStringBytes)
    (h_body : expiryLen ≤ body.val.length)
    (h_expiry : ¬ Expired (bodyExpiry body.val) now_ms.val)
    (h_key : (∃ k, self.keys = .Single k ∧ k.inner.val = key.val) ∨
      (∃ keys seal_mode rs1_fallbacks kid, self.keys = .Ring keys seal_mode rs1_fallbacks ∧
        kid ∈ rs1_fallbacks.val ∧ lookupKey keys kid = some key.val))
    (h_fallbacks : CodecFallbacksKnown self) :
    rmcp.model.request_state.RequestStateCodec.seal_rs1 key associated_data body ⦃
      (token : String) =>
      (∃ sealed : Str, (sealed : Slice Std.U8).val = ExtModel.utf8 token) ∧
      ∀ sealed : Str, (sealed : Slice Std.U8).val = ExtModel.utf8 token →
      rmcp.model.request_state.RequestStateCodec.open_at self sealed associated_data now_ms ⦃
        (result : core.result.Result (alloc.vec.Vec Std.U8) RequestStateError) =>
        -- line 566 → line 640 → E01 line 698
        resultBytes result = .ok (body.val.drop expiryLen) ⦄ ⦄ :=
  rmcp.model.request_state.RequestStateCodec.open_at_roundtrip_rs1 self key associated_data body
    now_ms h_len h_cap h_body h_expiry h_key h_fallbacks

/--
info: 'Theorems.request_state.RequestStateCodec.open_at_roundtrip_rs1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.open_at_roundtrip_rs1

/-- S15 `open_at_roundtrip_rs2`: sealing with E08 `seal_rs2` and opening any `Str` holding the
token's bytes with E11 `open_at` returns `Ok (body[8..])`, under the premises of
`rs2_roundtrip`. -/
theorem Theorems.request_state.RequestStateCodec.open_at_roundtrip_rs2 (self : RequestStateCodec)
    (kid : Str) (key : Slice Std.U8) (associated_data : Slice Std.U8) (body : Slice Std.U8)
    (now_ms : Std.I64) (kidStr : String)
    (h_len : (transcriptV2 (kid : Slice Std.U8).val associated_data.val body.val).length ≤
      Usize.max)
    (h_cap : versionV2.length + 3 + b64Len (kid : Slice Std.U8).val.length +
      b64Len body.val.length + b64Len 32 ≤ ExtModel.maxStringBytes)
    (h_body : expiryLen ≤ body.val.length)
    (h_expiry : ¬ Expired (bodyExpiry body.val) now_ms.val)
    (h_kid_utf8 : (kid : Slice Std.U8).val = ExtModel.utf8 kidStr)
    (h_kid_len : 1 ≤ (kid : Slice Std.U8).val.length ∧
      (kid : Slice Std.U8).val.length ≤ maxKidLen)
    (h_key : ∃ keys seal_mode rs1_fallbacks, self.keys = .Ring keys seal_mode rs1_fallbacks ∧
      lookupKey keys kidStr = some key.val) :
    rmcp.model.request_state.RequestStateCodec.seal_rs2 kid key associated_data body ⦃
      (token : String) =>
      (∃ sealed : Str, (sealed : Slice Std.U8).val = ExtModel.utf8 token) ∧
      ∀ sealed : Str, (sealed : Slice Std.U8).val = ExtModel.utf8 token →
      rmcp.model.request_state.RequestStateCodec.open_at self sealed associated_data now_ms ⦃
        (result : core.result.Result (alloc.vec.Vec Std.U8) RequestStateError) =>
        -- line 567 → line 692 → E01 line 698
        resultBytes result = .ok (body.val.drop expiryLen) ⦄ ⦄ :=
  rmcp.model.request_state.RequestStateCodec.open_at_roundtrip_rs2 self kid key associated_data body
    now_ms kidStr h_len h_cap h_body h_expiry h_kid_utf8 h_kid_len h_key

/--
info: 'Theorems.request_state.RequestStateCodec.open_at_roundtrip_rs2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.open_at_roundtrip_rs2

/-! ## R10a, R10b and the model round trip (translation patch 03; signed off 2026-11-25)

Spec theorems: R10a `seal_at_spec` in `Proofs/Model/RequestState/Seal.lean`; R10b
`seal_at_roundtrip` and the model round trip `Proofs.RequestState.Roundtrip.
openAt_eq_ok_of_sealAt_eq_some` in `Proofs/Model/RequestState/Roundtrip.lean`, whose docstrings
give the full statements. Premise keys: (S) `CodecSealKeyKnown`, (D) `SealFits`; `h_rs1`: an
`Rs1` seal-mode id is an rs1 fallback. Inherited exceptions (H) HMAC `2^61`, (V) a transcript
above `isize::MAX` bytes. -/

open rmcp.model.request_state (SealOptions RequestStateCodec)
open Defs.CodecState (CodecValid sealAt sealExpiry CodecSealKeyKnown SealFits)

/-- R10a `seal_at` (private): the UTF-8 bytes of the token are `sealAt` at the explicit time
`now_ms`. Premises (S), (D); inherited exceptions (H), (V). -/
theorem Theorems.request_state.RequestStateCodec.seal_at (self : RequestStateCodec)
    (payload : Slice Std.U8)
    (options : SealOptions) (now_ms : Std.I64)
    (h_key : CodecSealKeyKnown self)
    (h_fits : SealFits self payload.val.length options.associated_data.val.length) :
    rmcp.model.request_state.RequestStateCodec.seal_at self payload options now_ms
      ⦃ (result : String) =>
      sealAt self payload.val options.associated_data.val options.ttl now_ms.val =
        some (ExtModel.utf8 result) ⦄ :=
  rmcp.model.request_state.RequestStateCodec.seal_at_spec self payload options now_ms h_key h_fits

/--
info: 'Theorems.request_state.RequestStateCodec.seal_at' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.seal_at

/-- R10b: sealing with `seal_at` at `now`, then opening any `Str` holding the token with
`open_at` at `now'` (same associated data) gives `Ok` of the payload. Premises `CodecValid`,
`h_rs1`, (D), not expired at `now'`; inherited exceptions (H), (V). -/
theorem Theorems.request_state.RequestStateCodec.seal_at_roundtrip (self : RequestStateCodec)
    (payload : Slice Std.U8)
    (options : SealOptions) (now now' : Std.I64)
    (h_valid : CodecValid self)
    (h_rs1 : ∀ keys kid rs1_fallbacks, self.keys = .Ring keys (.Rs1 kid) rs1_fallbacks →
      kid ∈ rs1_fallbacks.val)
    (h_fits : SealFits self payload.val.length options.associated_data.val.length)
    (h_live : ¬ Expired (sealExpiry options.ttl now.val) now'.val) :
    rmcp.model.request_state.RequestStateCodec.seal_at self payload options now ⦃
      (token : String) =>
      (∃ sealed : Str, (sealed : Slice Std.U8).val = ExtModel.utf8 token) ∧
      ∀ sealed : Str, (sealed : Slice Std.U8).val = ExtModel.utf8 token →
      rmcp.model.request_state.RequestStateCodec.open_at self sealed options.associated_data
        now' ⦃ (result : core.result.Result (alloc.vec.Vec Std.U8) RequestStateError) =>
        resultBytes result = .ok payload.val ⦄ ⦄ :=
  rmcp.model.request_state.RequestStateCodec.seal_at_roundtrip self payload options now now' h_valid
    h_rs1 h_fits h_live

/--
info: 'Theorems.request_state.RequestStateCodec.seal_at_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state.RequestStateCodec.seal_at_roundtrip

/-- Model round trip: `openAt` of a `sealAt` token at a time where it is not expired is the
payload. Premises `CodecValid`, `h_rs1`, not expired. -/
theorem Theorems.request_state.openAt_eq_ok_of_sealAt_eq_some (codec : RequestStateCodec)
    (payload ad : List U8)
    (ttl : Option core.time.Duration) (now now' : Std.I64) (token : List U8)
    (h_valid : CodecValid codec)
    (h_rs1 : ∀ keys kid rs1_fallbacks, codec.keys = .Ring keys (.Rs1 kid) rs1_fallbacks →
      kid ∈ rs1_fallbacks.val)
    (h_live : ¬ Expired (sealExpiry ttl now.val) now'.val)
    (h_seal : sealAt codec payload ad ttl now.val = some token) :
    openAt codec token ad now'.val = .ok payload :=
  Proofs.RequestState.Roundtrip.openAt_eq_ok_of_sealAt_eq_some codec payload ad ttl now now' token
    h_valid h_rs1 h_live h_seal

/--
info: 'Theorems.request_state.openAt_eq_ok_of_sealAt_eq_some' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state.openAt_eq_ok_of_sealAt_eq_some

/-!
## Intermediate public functions (R05, R08, R10, R14)

Four public functions of `request_state.rs` are not top-level: each is called by another public
function that `formal/specs/` states, so their statements are here, not in
`formal/specs/Specs/Model/RequestState.lean`, which holds only the top-level public functions
(human decision 2026-11-28). The statements, their text, IDs, proofs and sign-off (R05, R08 and
its corollary on 2026-11-24, R10, its corollary and R14 on 2026-11-25; readability rewrite
2026-11-25) are unchanged; only their place changed.

| ID | Function | Theorem | Guarantee | Premises (caller must ensure) | Not covered (Rust may panic or behave otherwise; the model does not) |
|---|---|---|---|---|---|
| R05 | `Codec::new_unchecked` | `RSC.new_unchecked` | the single-key codec of `key.into()`, for a key of any length | caller code | (I) |
| R08 | `Codec::open_with` | `RSC.open_with` | the payload or error of opening the token with associated data `associated_data` at the clock reading (`openAt`) | (T), (F) | (K), (H), (V) |
| R08 cor. | `Codec::open_with` | `RSC.open_with_of_length_le` | as R08 | (L), (F) | (K), (H), (V) |
| R10 | `Codec::seal_with` | `RSC.seal_with` | the token sealed with the options at the clock reading (`sealAt`) | (S), (D) | (K), (H), (V) |
| R10 cor. | `Codec::seal_with` | `RSC.seal_with_of_length_le` | as R10 | `CodecValid`, (Ls) | (K), (H) |
| R14 | `Codec::open_json_with` | `RSC.open_json_with` | the error of opening as in R08, or the `serde_json::from_slice` outcome on the opened payload, an error mapped to `Deserialization` | (T), (F) | (K), (H), (V), (J) |

Called by: R05 `new_unchecked` by R04 `new`; R08 `open_with` by R07 `open` and R14 `open_json_with`
(so by R13 `open_json` through R14); R10 `seal_with` by R09 `seal`; R14 `open_json_with` by R13
`open_json` (`Codec::` abbreviates `RequestStateCodec::`, `RSC.` the theorem prefix
`Theorems.request_state.RequestStateCodec.`).

The keys of this section are local to it (the header above gives (D) another meaning and (T) a more
general one, as in the R10a section): (F), (S), (D), (Ls), caller code, (K), (H), (J) and (I) are
those of `formal/specs/Specs/Model/RequestState.lean` ("Premises", "Not covered", "The clock"; the
clock rule there also covers `open_with`, `seal_with` and `open_json_with`). The keys used only
here:

* **(T)** premise `h_transcript_v1 : TranscriptV1Fits …`, `h_transcript_v2 : TranscriptV2Fits …`:
  the MAC transcript of the token's decoded components and `ad` fits in `usize::MAX` bytes (the
  bound of the Lean model of `Vec::extend_from_slice`). It holds for every token when `ad` is
  empty, so R07 and R13 do not take it.
* **(L)** premise `h_length : ad.len() + sealed.len() + 36 ≤ usize::MAX`; it implies (T).
* **(V)** not covered, `open_with`, `open_json_with`, `seal_with` only: the transcript `Vec` is
  modelled up to `usize::MAX` bytes, while Rust panics above `isize::MAX` bytes. It does not arise
  without associated data (`open`, `open_json`: a transcript has at most `42 + 3n/4` bytes for a
  token of `n ≤ isize::MAX` bytes; `seal`: (D) bounds it), nor under (Ls).

Here `ad` is the associated data (`associated_data`; `options.associated_data` for `seal_with`), and
the spec theorems are in `Proofs/Model/RequestState/{Public,Seal,OpenJson}.lean`. Unlike the header
above (patch-01 copy), the translated configuration, line citations ("patched" is the copy with
patches 01–03, "upstream" is `7caec76`, "patch-01 copy" the copy with patch 01 only) of this section
are those of `formal/specs/Specs/Model/RequestState.lean`, "Provenance"; its linkage is R05, R08
`patch-01` and R10, R14 `patch-03` (`formal/README.md`, "Results"). The statements are in ID order
and use the abbreviations of `Defs.CodecState` and readable binder names (renaming map: "Proofs" in
that file), under the two spec-owner exceptions of `formal/CONTRIBUTING.md`, "Spec files", widened
to this section by human decision 2026-11-28. `TranscriptV1Fits` and `TranscriptV2Fits` (premise
(T)) are used only here but stay in `formal/specs/Defs/CodecState.lean` (recorded exception, same
decision).
-/

open Aeneas Aeneas.Std Result
open Defs.CodecState (CodecValid openAt resultBytes sealAt CodecSealKeyKnown SealFits strBytes
  FallbacksKnownForToken TranscriptV1Fits TranscriptV2Fits mapErrDeserialization)
open rmcp.model.request_state (SealOptions RequestStateCodec Keys RequestStateError)

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
