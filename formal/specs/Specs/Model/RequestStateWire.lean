/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Defs
import Proofs

/-!
# Spec file for crates/rmcp/src/model/request_state_wire.rs

Statements of the fifteen public wire functions of `crates/rmcp/src/model/request_state_wire.rs`
(plan Section 2.1, W01–W15) and of the composition theorem `frame_roundtrip`, in Rust source
order with the composition theorem last. Each is restated as a theorem
`Theorems.request_state_wire.<function>`, proved by the spec theorem in
`Proofs/Model/RequestStateWire/`, and followed by the assumptions its proof depends on, checked by
`#print axioms` under `#guard_msgs`. The statements were signed off by the spec owner on
2026-11-23 (the S05 evidence (git history at 77d9911)); their signed-off text is in `specs/Drafts/RequestStateWire.lean`
at commit `22b9f13`, removed when they were incorporated (the W-batch incorporation procedure (git history at 77d9911)).

Translated configuration (the proofs hold only for it): target `x86_64-unknown-linux-gnu`,
features `--no-default-features --features request-state`, with `overflow-checks=true` and
`debug-assertions=true` (every cargo call gets `--config profile.dev.overflow-checks=true` and
`--config profile.dev.debug-assertions=true`, plan Section 1), so arithmetic overflow panics,
which Aeneas models as failure. Aeneas `nightly-2026.08.20-5d08da4`; the translation base is
local commit `22b9f13` (S04a part 2), not yet a pinned fork commit. Line numbers refer to
`request_state_wire.rs` at `22b9f13`.

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
