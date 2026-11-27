/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Defs
public import Defs.Wire
public import Proofs.Model.RequestStateWire.B64Len
public import Proofs.Model.RequestStateWire.KeyLengthOk
public import Proofs.Model.RequestStateWire.CheckKidLen
public import Proofs.Model.RequestStateWire.BytesEq
public import Proofs.Model.RequestStateWire.NextDot
public import Proofs.Model.RequestStateWire.ComponentCount
public import Proofs.Model.RequestStateWire.VersionOf
public import Proofs.Model.RequestStateWire.ParseRs1
public import Proofs.Model.RequestStateWire.ParseRs2
public import Proofs.Model.RequestStateWire.TranscriptV1
public import Proofs.Model.RequestStateWire.TranscriptV2
public import Proofs.Model.RequestStateWire.DecodeExpiry
public import Proofs.Model.RequestStateWire.IsExpired
public import Proofs.Model.RequestStateWire.OpenFrame
public import Proofs.Model.RequestStateWire.Frame

@[expose] public section

/-!
# Internal spec file for crates/rmcp/src/model/request_state_wire.rs (patch-only, W01–W15)

These are guarantees about patch-only functions: they are `pub` only in the module
`request_state_wire` that translation patch 01 adds, and are not upstream rmcp API; they are kept
out of `formal/specs/`, which holds only the public API (human decision 2026-11-24). Index of all
guarantees: `formal/specs/README.md`.

| ID | Function | Guarantee | Assumptions |
|---|---|---|---|
| W01 | `b64_len` | `4 * ((len + 2) / 3)` | (a) |
| W02 | `key_length_ok` | `true` iff `len ≥ 32` | none |
| W03 | `check_kid_len` | `Err(Empty)` iff 0, `Err(TooLong)` iff > 255, else `Ok(())` | none |
| W04 | `bytes_eq` | `true` iff the slices are equal byte lists | none |
| W05 | `next_dot` | least index `≥ start` holding `.`, else `s.len()` | none |
| W06 | `component_count` | number of `.`-components = number of `.` bytes + 1 | (b) |
| W07 | `version_of` | `Some(V1)` iff first component `rs1`, `Some(V2)` iff `rs2` | none |
| W08 | `parse_rs1` | `Some {body, tag}` iff the token is `rs1.body.tag` | (b) |
| W09 | `parse_rs2` | `Some {kid, body, tag}` iff the token is `rs2.kid.body.tag` | (b) |
| W10 | `transcript_v1` | `DOMAIN_V1 ++ be64(len ad) ++ ad ++ body` | (c) |
| W11 | `transcript_v2` | `DOMAIN_V2 ++ be64(len kid) ++ kid ++ be64(len ad) ++ ad ++ body` | (c) |
| W12 | `decode_expiry` | the signed (two's-complement) big-endian value of the 8 bytes | none |
| W13 | `is_expired` | `true` iff `expiry ≠ 0` and `now_ms > expiry` | none |
| W14 | `open_frame` | `< 8` bytes: `TooShort`; expired: `Expired`; else `Ok(body[8..])` | none |
| W15 | `frame` | `be64(expiry as u64) ++ payload` | (c) |
| — | `frame_roundtrip` | `open_frame(frame(e, p), now)` is `Ok(p)` | (c), (d) |

Each row says that the call (for `frame_roundtrip`, the two calls in sequence) does not panic and
that its result satisfies the guarantee. W07 gives `None` when the first component is neither;
W08/W09 split on every `.` (exactly three, resp. four, components). Assumptions: (a) the result
fits in `usize` (no overflow); (b) fewer than `usize::MAX` `.` bytes; (c) the result fits in
`usize::MAX` bytes; (d) `e` is `0` or `now ≤ e`. Used by: in the patched copy, the
`RequestStateCodec` functions of `Proofs/Internal/Model/RequestState.lean` and the excluded
`seal_at` (W15), directly or through W04–W06, W12 and W13 (seal and open of request-state
tokens); `formal/specs/README.md` lists the callers of each function.

Statements of the fifteen wire functions (`pub` only inside the module that patch 01 adds; not
upstream API) of `crates/rmcp/src/model/request_state_wire.rs` (plan Section 2.1, W01–W15) and of
the composition theorem `frame_roundtrip`, in Rust source order with the composition theorem
last. Each is restated as a theorem `Theorems.request_state_wire.<function>`, proved by the spec
theorem (for `frame_roundtrip`, the lemma of that name) in `Proofs/Model/RequestStateWire/`, and
followed by the assumptions its proof depends on, checked by
`#print axioms` under `#guard_msgs`. The statements were signed off by the spec owner on
2026-11-23 (the S05 evidence, git history at 223ff12); their signed-off text is the one
restated in this project file (git history at `9bd8144`), incorporated
(the W-batch incorporation procedure, git history at 223ff12).

Translated configuration (the proofs hold only for it): target `x86_64-unknown-linux-gnu`,
`--no-default-features` with the features `request-state`, `server`, `client`, `client-side-sse`,
`transport-streamable-http-server`, `transport-streamable-http-client` and `auth` (widened for
Phase 2, plan Section 15; the translation of this file's targets is unchanged), with
`overflow-checks=true` and `debug-assertions=true` (every cargo call gets
`--config profile.dev.overflow-checks=true` and `--config profile.dev.debug-assertions=true`,
plan Section 1), so arithmetic overflow panics, which Aeneas models as failure. Aeneas
`nightly-2026.11.24-fb44cb4` (until 2026-11-24 `nightly-2026.08.20-5d08da4`); the translation base is the patched copy (patch 01 on origin/main
7caec76, `formal/trusted/patches/01-request-state-wire.patch`, D2 fallback 2026-11-23;
translation committed at `9bd8144`). Line numbers refer to `request_state_wire.rs` in the
patched copy, the only place the file exists.

Definitions used: `Defs.Wire` (`formal/specs/Defs/Wire.lean`, used by public statements too): `b64Len`, `minKeyLength`, `maxKidLen`, `dot`, `components`,
`versionV1`, `versionV2`, `transcriptV1`, `transcriptV2`, `beNat`, `toInt64`, `Expired`,
`expiryLen`, `bodyExpiry`, `frameBytes`.

Opaque functions: the four functions of the module `prim` (`hmac_sha256`, `hmac_sha256_verify`,
`b64_encode_into`, `b64_decode`) are not translated from Rust; they are opaque and modelled in
`trusted/Rmcp/FunsExternal.lean` (plan Sections 2.1 and 4). No statement here mentions them.
No statement here reaches a native-code assumption.

Not translated from this file: the derived `Debug` impls of `KidError`, `Version`, `Rs1Parts`,
`Rs2Parts` and `FrameError` (Charon `exclude` in `crates/rmcp/Cargo.toml`). No function of this
file is in the excluded list of plan Section 2.3.
-/

open Aeneas Aeneas.Std Result
open Defs.Wire
-- for `KidError`, `Version`, `Rs1Parts`, `Rs2Parts` and `FrameError`; theorems named in full
open rmcp.model.request_state_wire

/-- W01 `b64_len`: on the no-overflow domain `b64Len len ≤ Usize.max`, the result is
`b64Len len = 4 * ((len + 2) / 3)`. -/
theorem Theorems.request_state_wire.b64_len (len : Usize)
    (h_no_overflow : b64Len len.val ≤ Usize.max) :
    rmcp.model.request_state_wire.b64_len len ⦃ (result : Usize) =>
      result.val = b64Len len.val ⦄ :=
  rmcp.model.request_state_wire.b64_len_spec len h_no_overflow

/--
info: 'Theorems.request_state_wire.b64_len' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state_wire.b64_len

/-- W02 `key_length_ok`: `true` iff `len ≥ MIN_KEY_LENGTH = 32`. -/
theorem Theorems.request_state_wire.key_length_ok (len : Usize) :
    rmcp.model.request_state_wire.key_length_ok len ⦃ (result : Bool) =>
      result = decide (minKeyLength ≤ len.val) ⦄ :=
  rmcp.model.request_state_wire.key_length_ok_spec len

/--
info: 'Theorems.request_state_wire.key_length_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state_wire.key_length_ok

/-- W03 `check_kid_len`: `Err Empty` iff `len = 0`, `Err TooLong` iff `len > 255`, otherwise
`Ok ()`. -/
theorem Theorems.request_state_wire.check_kid_len (len : Usize) :
    rmcp.model.request_state_wire.check_kid_len len
      ⦃ (result : core.result.Result Unit KidError) =>
      match result with
      | .Err .Empty => len.val = 0
      | .Err .TooLong => maxKidLen < len.val
      | .Ok () => 0 < len.val ∧ len.val ≤ maxKidLen ⦄ :=
  rmcp.model.request_state_wire.check_kid_len_spec len

/--
info: 'Theorems.request_state_wire.check_kid_len' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state_wire.check_kid_len

/-- W04 `bytes_eq`: `true` iff the slices are equal as byte lists. -/
theorem Theorems.request_state_wire.bytes_eq (a : Slice U8) (b : Slice U8) :
    rmcp.model.request_state_wire.bytes_eq a b ⦃ (result : Bool) =>
      result = decide (a.val = b.val) ⦄ :=
  rmcp.model.request_state_wire.bytes_eq_spec a b

/--
info: 'Theorems.request_state_wire.bytes_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state_wire.bytes_eq

/-- W05 `next_dot`: the least index `i ≥ start` with `s[i] = '.'`, otherwise `s.len()`. -/
theorem Theorems.request_state_wire.next_dot (s : Slice U8) (start : Usize) :
    rmcp.model.request_state_wire.next_dot s start ⦃ (result : Usize) =>
      (∀ j, start.val ≤ j → j < result.val → s.val[j]? ≠ some dot) ∧
      (result.val = s.length ∨
        (start.val ≤ result.val ∧ s.val[result.val]? = some dot)) ⦄ :=
  rmcp.model.request_state_wire.next_dot_spec s start

/--
info: 'Theorems.request_state_wire.next_dot' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state_wire.next_dot

/-- W06 `component_count`: the number of `.`-components, one more than the number of `.`
bytes (domain: fewer than `Usize.max` `.` bytes). -/
theorem Theorems.request_state_wire.component_count (s : Slice U8)
    (h_count : s.val.count dot < Usize.max) :
    rmcp.model.request_state_wire.component_count s ⦃ (result : Usize) =>
      result.val = (components s.val).length ∧
      result.val = s.val.count dot + 1 ⦄ :=
  rmcp.model.request_state_wire.component_count_spec s h_count

/--
info: 'Theorems.request_state_wire.component_count' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state_wire.component_count

/-- W07 `version_of`: `Some V1` iff the first `.`-component is `"rs1"`, `Some V2` iff it is
`"rs2"`, `None` otherwise. -/
theorem Theorems.request_state_wire.version_of (s : Slice U8) :
    rmcp.model.request_state_wire.version_of s ⦃ (result : Option Version) =>
      match result with
      | some .V1 => (components s.val).head? = some versionV1
      | some .V2 => (components s.val).head? = some versionV2
      | none =>
        (components s.val).head? ≠ some versionV1 ∧
        (components s.val).head? ≠ some versionV2 ⦄ :=
  rmcp.model.request_state_wire.version_of_spec s

/--
info: 'Theorems.request_state_wire.version_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state_wire.version_of

/-- W08 `parse_rs1`: `Some {body, tag}` iff the token splits on `.` into
`["rs1", body, tag]`, `None` otherwise (domain: fewer than `Usize.max` `.` bytes). -/
theorem Theorems.request_state_wire.parse_rs1 (s : Slice U8)
    (h_count : s.val.count dot < Usize.max) :
    rmcp.model.request_state_wire.parse_rs1 s ⦃ (result : Option Rs1Parts) =>
      match result with
      | some p => components s.val = [versionV1, p.body.val, p.tag.val]
      | none => ∀ body tag, components s.val ≠ [versionV1, body, tag] ⦄ :=
  rmcp.model.request_state_wire.parse_rs1_spec s h_count

/--
info: 'Theorems.request_state_wire.parse_rs1' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state_wire.parse_rs1

/-- W09 `parse_rs2`: `Some {kid, body, tag}` iff the token splits on `.` into
`["rs2", kid, body, tag]`, `None` otherwise (domain: fewer than `Usize.max` `.` bytes). -/
theorem Theorems.request_state_wire.parse_rs2 (s : Slice U8)
    (h_count : s.val.count dot < Usize.max) :
    rmcp.model.request_state_wire.parse_rs2 s ⦃ (result : Option Rs2Parts) =>
      match result with
      | some p => components s.val = [versionV2, p.kid.val, p.body.val, p.tag.val]
      | none => ∀ kid body tag, components s.val ≠ [versionV2, kid, body, tag] ⦄ :=
  rmcp.model.request_state_wire.parse_rs2_spec s h_count

/--
info: 'Theorems.request_state_wire.parse_rs2' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state_wire.parse_rs2

/-- W10 `transcript_v1`: `DOMAIN_V1 ++ be64(len ad) ++ ad ++ body` (domain: the transcript
fits in `Usize.max` bytes). -/
theorem Theorems.request_state_wire.transcript_v1 (associated_data : Slice U8)
    (body : Slice U8)
    (h_len : (transcriptV1 associated_data.val body.val).length ≤ Usize.max) :
    rmcp.model.request_state_wire.transcript_v1 associated_data body
      ⦃ (result : alloc.vec.Vec U8) =>
      result.val = transcriptV1 associated_data.val body.val ⦄ :=
  rmcp.model.request_state_wire.transcript_v1_spec associated_data body h_len

/--
info: 'Theorems.request_state_wire.transcript_v1' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state_wire.transcript_v1

/-- W11 `transcript_v2`: `DOMAIN_V2 ++ be64(len kid) ++ kid ++ be64(len ad) ++ ad ++ body`
(domain: the transcript fits in `Usize.max` bytes). -/
theorem Theorems.request_state_wire.transcript_v2 (kid : Slice U8)
    (associated_data : Slice U8) (body : Slice U8)
    (h_len : (transcriptV2 kid.val associated_data.val body.val).length ≤ Usize.max) :
    rmcp.model.request_state_wire.transcript_v2 kid associated_data body
      ⦃ (result : alloc.vec.Vec U8) =>
      result.val = transcriptV2 kid.val associated_data.val body.val ⦄ :=
  rmcp.model.request_state_wire.transcript_v2_spec kid associated_data body h_len

/--
info: 'Theorems.request_state_wire.transcript_v2' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state_wire.transcript_v2

/-- W12 `decode_expiry`: the two's-complement value of the 8 big-endian bytes. -/
theorem Theorems.request_state_wire.decode_expiry (head : Array U8 8#usize) :
    rmcp.model.request_state_wire.decode_expiry head ⦃ (result : I64) =>
      result.val = toInt64 (beNat head.val) ⦄ :=
  rmcp.model.request_state_wire.decode_expiry_spec head

/--
info: 'Theorems.request_state_wire.decode_expiry' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state_wire.decode_expiry

/-- W13 `is_expired`: `true` iff `expiry ≠ 0 ∧ now_ms > expiry`. -/
theorem Theorems.request_state_wire.is_expired (expiry : I64) (now_ms : I64) :
    rmcp.model.request_state_wire.is_expired expiry now_ms ⦃ (result : Bool) =>
      result = decide (Expired expiry.val now_ms.val) ⦄ :=
  rmcp.model.request_state_wire.is_expired_spec expiry now_ms

/--
info: 'Theorems.request_state_wire.is_expired' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state_wire.is_expired

/-- W14 `open_frame`: `TooShort` below 8 bytes, `Expired` when W13 holds for the W12 value of
the first 8 bytes, otherwise `Ok (body[8..])`. -/
theorem Theorems.request_state_wire.open_frame (body : Slice U8) (now_ms : I64) :
    rmcp.model.request_state_wire.open_frame body now_ms
      ⦃ (result : core.result.Result (Slice U8) FrameError) =>
      match result with
      | .Err .TooShort => body.length < expiryLen
      | .Err .Expired => expiryLen ≤ body.length ∧ Expired (bodyExpiry body.val) now_ms.val
      | .Ok payload =>
        expiryLen ≤ body.length ∧ ¬ Expired (bodyExpiry body.val) now_ms.val ∧
        payload.val = body.val.drop expiryLen ⦄ :=
  rmcp.model.request_state_wire.open_frame_spec body now_ms

/--
info: 'Theorems.request_state_wire.open_frame' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state_wire.open_frame

/-- W15 `frame`: `be64(expiry as u64) ++ payload` (domain: the frame fits in `Usize.max`
bytes). -/
theorem Theorems.request_state_wire.frame (expiry : I64) (payload : Slice U8)
    (h_len : (frameBytes expiry.val payload.val).length ≤ Usize.max) :
    rmcp.model.request_state_wire.frame expiry payload ⦃ (result : alloc.vec.Vec U8) =>
      result.val = frameBytes expiry.val payload.val ⦄ :=
  rmcp.model.request_state_wire.frame_spec expiry payload h_len

/--
info: 'Theorems.request_state_wire.frame' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state_wire.frame

/-- `frame_roundtrip`: for a frame that fits in `Usize.max` bytes and an expiry that is `0` or
not before `now_ms`, `open_frame` of `frame expiry payload` returns `Ok payload`. -/
theorem Theorems.request_state_wire.frame_roundtrip (expiry : I64) (payload : Slice U8)
    (now_ms : I64)
    (h_len : (frameBytes expiry.val payload.val).length ≤ Usize.max)
    (h_live : ¬ Expired expiry.val now_ms.val) :
    (do
      let body ← rmcp.model.request_state_wire.frame expiry payload
      rmcp.model.request_state_wire.open_frame (alloc.vec.Vec.deref body) now_ms)
      ⦃ (result : core.result.Result (Slice U8) FrameError) =>
      result = .Ok payload ⦄ :=
  rmcp.model.request_state_wire.frame_roundtrip expiry payload now_ms h_len h_live

/--
info: 'Theorems.request_state_wire.frame_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state_wire.frame_roundtrip
