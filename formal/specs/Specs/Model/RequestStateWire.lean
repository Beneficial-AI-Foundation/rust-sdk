/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Defs
import Proofs
import Mathlib.Tactic.Recall

/-!
# Spec file for crates/rmcp/src/model/request_state_wire.rs

Statements of the fifteen public wire functions of `crates/rmcp/src/model/request_state_wire.rs`
(plan Section 2.1, W01–W15) and of the composition theorem `frame_roundtrip`, in Rust source
order with the composition theorem last. Each is restated with `recall` from its proof in
`Proofs/Model/RequestStateWire/` and followed by the assumptions its proof depends on, checked by
`#print axioms` under `#guard_msgs`. The statements were signed off by the spec owner on
2026-11-23 (evidence/S05.md); their signed-off text is in `specs/Drafts/RequestStateWire.lean`
at commit `adce319`, removed when they were incorporated (docs/review/W-batch-incorporation.md).

Translated configuration (the proofs hold only for it): target `x86_64-unknown-linux-gnu`,
features `--no-default-features --features request-state`, with `overflow-checks=true` and
`debug-assertions=true` (every cargo call gets `--config profile.dev.overflow-checks=true` and
`--config profile.dev.debug-assertions=true`, plan Section 1), so arithmetic overflow panics,
which Aeneas models as failure. Aeneas `nightly-2026.08.20-5d08da4`; the translation base is
local commit `adce319` (S04a part 2), not yet a pinned fork commit. Line numbers refer to
`request_state_wire.rs` at `adce319`.

Definitions used: `Defs.Wire` (`b64Len`, `minKeyLength`, `maxKidLen`, `dot`, `components`,
`versionV1`, `versionV2`, `transcriptV1`, `transcriptV2`, `beNat`, `toInt64`, `Expired`,
`expiryLen`, `bodyExpiry`, `frameBytes`).

Opaque functions: the four functions of the module `prim` (`hmac_sha256`, `hmac_sha256_verify`,
`b64_encode_into`, `b64_decode`) are not translated from Rust; they are opaque and modelled in
`trusted/Rmcp/FunsExternal.lean` (plan Sections 2.1 and 4). No statement here mentions them.

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
recall rmcp.model.request_state_wire.b64_len_spec (len : Usize)
    (h_no_overflow : b64Len len.val ≤ Usize.max) :
    rmcp.model.request_state_wire.b64_len len ⦃ (result : Usize) =>
      result.val = b64Len len.val ⦄

/--
info: 'rmcp.model.request_state_wire.b64_len_spec' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rmcp.model.request_state_wire.b64_len_spec

/-- W02 `key_length_ok`: `true` iff `len ≥ MIN_KEY_LENGTH = 32`. -/
recall rmcp.model.request_state_wire.key_length_ok_spec (len : Usize) :
    rmcp.model.request_state_wire.key_length_ok len ⦃ (result : Bool) =>
      result = decide (minKeyLength ≤ len.val) ⦄

/--
info: 'rmcp.model.request_state_wire.key_length_ok_spec' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rmcp.model.request_state_wire.key_length_ok_spec

/-- W03 `check_kid_len`: `Err Empty` iff `len = 0`, `Err TooLong` iff `len > 255`, otherwise
`Ok ()`. -/
recall rmcp.model.request_state_wire.check_kid_len_spec (len : Usize) :
    rmcp.model.request_state_wire.check_kid_len len
      ⦃ (result : core.result.Result Unit KidError) =>
      match result with
      | .Err .Empty => len.val = 0
      | .Err .TooLong => maxKidLen < len.val
      | .Ok () => 0 < len.val ∧ len.val ≤ maxKidLen ⦄

/--
info: 'rmcp.model.request_state_wire.check_kid_len_spec' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rmcp.model.request_state_wire.check_kid_len_spec

/-- W04 `bytes_eq`: `true` iff the slices are equal as byte lists. -/
recall rmcp.model.request_state_wire.bytes_eq_spec (a : Slice U8) (b : Slice U8) :
    rmcp.model.request_state_wire.bytes_eq a b ⦃ (result : Bool) =>
      result = decide (a.val = b.val) ⦄

/--
info: 'rmcp.model.request_state_wire.bytes_eq_spec' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rmcp.model.request_state_wire.bytes_eq_spec

/-- W05 `next_dot`: the least index `i ≥ start` with `s[i] = '.'`, otherwise `s.len()`. -/
recall rmcp.model.request_state_wire.next_dot_spec (s : Slice U8) (start : Usize) :
    rmcp.model.request_state_wire.next_dot s start ⦃ (result : Usize) =>
      (∀ j, start.val ≤ j → j < result.val → s.val[j]? ≠ some dot) ∧
      (result.val = s.length ∨
        (start.val ≤ result.val ∧ s.val[result.val]? = some dot)) ⦄

/--
info: 'rmcp.model.request_state_wire.next_dot_spec' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rmcp.model.request_state_wire.next_dot_spec

/-- W06 `component_count`: the number of `.`-components, one more than the number of `.`
bytes (domain: fewer than `Usize.max` `.` bytes). -/
recall rmcp.model.request_state_wire.component_count_spec (s : Slice U8)
    (h_count : s.val.count dot < Usize.max) :
    rmcp.model.request_state_wire.component_count s ⦃ (result : Usize) =>
      result.val = (components s.val).length ∧
      result.val = s.val.count dot + 1 ⦄

/--
info: 'rmcp.model.request_state_wire.component_count_spec' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rmcp.model.request_state_wire.component_count_spec

/-- W07 `version_of`: `Some V1` iff the first `.`-component is `"rs1"`, `Some V2` iff it is
`"rs2"`, `None` otherwise. -/
recall rmcp.model.request_state_wire.version_of_spec (s : Slice U8) :
    rmcp.model.request_state_wire.version_of s ⦃ (result : Option Version) =>
      match result with
      | some .V1 => (components s.val).head? = some versionV1
      | some .V2 => (components s.val).head? = some versionV2
      | none =>
        (components s.val).head? ≠ some versionV1 ∧
        (components s.val).head? ≠ some versionV2 ⦄

/--
info: 'rmcp.model.request_state_wire.version_of_spec' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rmcp.model.request_state_wire.version_of_spec

/-- W08 `parse_rs1`: `Some {body, tag}` iff the token splits on `.` into
`["rs1", body, tag]`, `None` otherwise (domain: fewer than `Usize.max` `.` bytes). -/
recall rmcp.model.request_state_wire.parse_rs1_spec (s : Slice U8)
    (h_count : s.val.count dot < Usize.max) :
    rmcp.model.request_state_wire.parse_rs1 s ⦃ (result : Option Rs1Parts) =>
      match result with
      | some p => components s.val = [versionV1, p.body.val, p.tag.val]
      | none => ∀ body tag, components s.val ≠ [versionV1, body, tag] ⦄

/--
info: 'rmcp.model.request_state_wire.parse_rs1_spec' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rmcp.model.request_state_wire.parse_rs1_spec

/-- W09 `parse_rs2`: `Some {kid, body, tag}` iff the token splits on `.` into
`["rs2", kid, body, tag]`, `None` otherwise (domain: fewer than `Usize.max` `.` bytes). -/
recall rmcp.model.request_state_wire.parse_rs2_spec (s : Slice U8)
    (h_count : s.val.count dot < Usize.max) :
    rmcp.model.request_state_wire.parse_rs2 s ⦃ (result : Option Rs2Parts) =>
      match result with
      | some p => components s.val = [versionV2, p.kid.val, p.body.val, p.tag.val]
      | none => ∀ kid body tag, components s.val ≠ [versionV2, kid, body, tag] ⦄

/--
info: 'rmcp.model.request_state_wire.parse_rs2_spec' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rmcp.model.request_state_wire.parse_rs2_spec

/-- W10 `transcript_v1`: `DOMAIN_V1 ++ be64(len ad) ++ ad ++ body` (domain: the transcript
fits in `Usize.max` bytes). -/
recall rmcp.model.request_state_wire.transcript_v1_spec (associated_data : Slice U8)
    (body : Slice U8)
    (h_len : (transcriptV1 associated_data.val body.val).length ≤ Usize.max) :
    rmcp.model.request_state_wire.transcript_v1 associated_data body
      ⦃ (result : alloc.vec.Vec U8) =>
      result.val = transcriptV1 associated_data.val body.val ⦄

/--
info: 'rmcp.model.request_state_wire.transcript_v1_spec' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rmcp.model.request_state_wire.transcript_v1_spec

/-- W11 `transcript_v2`: `DOMAIN_V2 ++ be64(len kid) ++ kid ++ be64(len ad) ++ ad ++ body`
(domain: the transcript fits in `Usize.max` bytes). -/
recall rmcp.model.request_state_wire.transcript_v2_spec (kid : Slice U8)
    (associated_data : Slice U8) (body : Slice U8)
    (h_len : (transcriptV2 kid.val associated_data.val body.val).length ≤ Usize.max) :
    rmcp.model.request_state_wire.transcript_v2 kid associated_data body
      ⦃ (result : alloc.vec.Vec U8) =>
      result.val = transcriptV2 kid.val associated_data.val body.val ⦄

/--
info: 'rmcp.model.request_state_wire.transcript_v2_spec' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rmcp.model.request_state_wire.transcript_v2_spec

/-- W12 `decode_expiry`: the two's-complement value of the 8 big-endian bytes. -/
recall rmcp.model.request_state_wire.decode_expiry_spec (head : Array U8 8#usize) :
    rmcp.model.request_state_wire.decode_expiry head ⦃ (result : I64) =>
      result.val = toInt64 (beNat head.val) ⦄

/--
info: 'rmcp.model.request_state_wire.decode_expiry_spec' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rmcp.model.request_state_wire.decode_expiry_spec

/-- W13 `is_expired`: `true` iff `expiry ≠ 0 ∧ now_ms > expiry`. -/
recall rmcp.model.request_state_wire.is_expired_spec (expiry : I64) (now_ms : I64) :
    rmcp.model.request_state_wire.is_expired expiry now_ms ⦃ (result : Bool) =>
      result = decide (Expired expiry.val now_ms.val) ⦄

/--
info: 'rmcp.model.request_state_wire.is_expired_spec' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rmcp.model.request_state_wire.is_expired_spec

/-- W14 `open_frame`: `TooShort` below 8 bytes, `Expired` when W13 holds for the W12 value of
the first 8 bytes, otherwise `Ok (body[8..])`. -/
recall rmcp.model.request_state_wire.open_frame_spec (body : Slice U8) (now_ms : I64) :
    rmcp.model.request_state_wire.open_frame body now_ms
      ⦃ (result : core.result.Result (Slice U8) FrameError) =>
      match result with
      | .Err .TooShort => body.length < expiryLen
      | .Err .Expired => expiryLen ≤ body.length ∧ Expired (bodyExpiry body.val) now_ms.val
      | .Ok payload =>
        expiryLen ≤ body.length ∧ ¬ Expired (bodyExpiry body.val) now_ms.val ∧
        payload.val = body.val.drop expiryLen ⦄

/--
info: 'rmcp.model.request_state_wire.open_frame_spec' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rmcp.model.request_state_wire.open_frame_spec

/-- W15 `frame`: `be64(expiry as u64) ++ payload` (domain: the frame fits in `Usize.max`
bytes). -/
recall rmcp.model.request_state_wire.frame_spec (expiry : I64) (payload : Slice U8)
    (h_len : (frameBytes expiry.val payload.val).length ≤ Usize.max) :
    rmcp.model.request_state_wire.frame expiry payload ⦃ (result : alloc.vec.Vec U8) =>
      result.val = frameBytes expiry.val payload.val ⦄

/--
info: 'rmcp.model.request_state_wire.frame_spec' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rmcp.model.request_state_wire.frame_spec

/-- `frame_roundtrip`: for a frame that fits in `Usize.max` bytes and an expiry that is `0` or
not before `now_ms`, `open_frame` of `frame expiry payload` returns `Ok payload`. -/
recall rmcp.model.request_state_wire.frame_roundtrip (expiry : I64) (payload : Slice U8)
    (now_ms : I64)
    (h_len : (frameBytes expiry.val payload.val).length ≤ Usize.max)
    (h_live : ¬ Expired expiry.val now_ms.val) :
    (do
      let body ← rmcp.model.request_state_wire.frame expiry payload
      rmcp.model.request_state_wire.open_frame (alloc.vec.Vec.deref body) now_ms)
      ⦃ (result : core.result.Result (Slice U8) FrameError) =>
      result = .Ok payload ⦄

/--
info: 'rmcp.model.request_state_wire.frame_roundtrip' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rmcp.model.request_state_wire.frame_roundtrip
