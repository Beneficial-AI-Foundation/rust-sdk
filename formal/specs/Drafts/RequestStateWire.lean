/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Rmcp.Funs
import Defs.Wire

/-!
# Draft statements for `request_state_wire` (W01–W15, `frame_roundtrip`)

Draft specification statements of plan step S05 for the fifteen public functions of
`crates/rmcp/src/model/request_state_wire.rs` (plan Section 2.1) and the composition theorem
`frame_roundtrip` (plan Section 3, "Round-trip"; Section 5, "Theorem names"). They are stated
against the translated functions of `Rmcp.Funs` (Aeneas `nightly-2026.08.20-5d08da4`,
configuration `x86_64-unknown-linux-gnu`, `--no-default-features --features request-state`) and
use only the definitions of `Defs/Wire.lean`. The translation was generated from local commit
`14d2830` plus the working-tree Charon excludes of the seven derived `Debug` impls
(`crates/rmcp/Cargo.toml`); `formal/translation/` is untracked and not yet a pinned fork commit
(S04a not landed). Line numbers refer to `request_state_wire.rs` at `14d2830`.

This file is a draft: it lives in `formal/specs/Drafts/`, belongs to no library and is never
built. Each proof is a placeholder proof, which is allowed only here (STYLE_GUIDE, "Spec
Theorem Style"; WORKFLOW_AND_PR_GUIDE, "Library roots"). None of these statements is signed off.

A statement `f x ⦃ (result : T) => P result ⦄` says that `f x` terminates without panicking
(no failure, no overflow, no out-of-bounds access) and that its result satisfies `P` (plan
Section 3, "What a spec means"). Every postcondition below determines the result uniquely, so
each statement is a full functional characterisation; the `Ok`/`Err` and `some`/`none` arms are
listed in the Rust order of checks.

Lean-model domains (plan Section 3): W06, W08 and W09 assume that the slice has fewer than
`Usize.max` `.` bytes, and W10, W11, W15 and `frame_roundtrip` assume that the output fits in
`Usize.max` bytes. W01 is stated on its no-overflow domain. These hypotheses are the exact
conditions under which the translated function does not fail; each is open for the spec owner
(see the S05 report).
-/

open Aeneas Aeneas.Std Result

namespace rmcp.model.request_state_wire

open Defs.Wire

/-- **Spec theorem for `rmcp::model::request_state_wire::b64_len`** (W01)

On the no-overflow domain `4 * ceil(len / 3) ≤ Usize.max`, `b64_len len` returns
`4 * ceil(len / 3)` (plan Section 2.1, W01; lines 27–36). Overflow is failure in the Aeneas
model, matching debug builds with `overflow-checks` on (plan Section 3, "W01 and the seal
capacities"; Section 1). The hypothesis is also necessary: `len / 3 * 4 ≤ b64Len len`, so the
function fails exactly when `b64Len len > Usize.max`. -/
@[step]
theorem b64_len_spec (len : Usize)
    (h_no_overflow : b64Len len.val ≤ Usize.max) :
    b64_len len ⦃ (result : Usize) =>
      result.val = b64Len len.val ⦄ := by
  sorry

/-- **Spec theorem for `rmcp::model::request_state_wire::key_length_ok`** (W02)

`key_length_ok len` is `true` iff `len ≥ MIN_KEY_LENGTH = 32` (plan Section 2.1, W02;
lines 19 and 38–41). No precondition. -/
@[step]
theorem key_length_ok_spec (len : Usize) :
    key_length_ok len ⦃ (result : Bool) =>
      result = decide (minKeyLength ≤ len.val) ⦄ := by
  sorry

/-- **Spec theorem for `rmcp::model::request_state_wire::check_kid_len`** (W03)

`check_kid_len len` returns `Err Empty` iff `len = 0` (lines 55–57), `Err TooLong` iff
`len > MAX_KID_LEN = 255` (lines 21, 58–60), and `Ok ()` otherwise (line 61); plan Section 2.1,
W03. The arms are in the Rust order of checks. Any length in `1..=255` is accepted, with no
alphabet restriction (plan Section 3, "W03/E04 — kid alphabet"). No precondition. -/
@[step]
theorem check_kid_len_spec (len : Usize) :
    check_kid_len len ⦃ (result : core.result.Result Unit KidError) =>
      match result with
      | .Err .Empty => len.val = 0
      | .Err .TooLong => maxKidLen < len.val
      | .Ok () => 0 < len.val ∧ len.val ≤ maxKidLen ⦄ := by
  sorry

/-- **Spec theorem for `rmcp::model::request_state_wire::bytes_eq`** (W04)

`bytes_eq a b` is `true` iff `a` and `b` are equal as byte lists (plan Section 2.1, W04;
lines 64–77: the length check of lines 66–68, then the bytewise loop of lines 69–76). No
precondition. -/
@[step]
theorem bytes_eq_spec (a : Slice U8) (b : Slice U8) :
    bytes_eq a b ⦃ (result : Bool) =>
      result = decide (a.val = b.val) ⦄ := by
  sorry

/-- **Spec theorem for `rmcp::model::request_state_wire::next_dot`** (W05)

`next_dot s start` is the least index `i ≥ start` with `s[i] = '.'`, or `s.len()` if there is
none (plan Section 2.1, W05; lines 79–89). The first conjunct says that no `.` lies in
`[start, result)`; the second that `result` is `s.len()` or a `.` at or after `start`. Together
they determine `result`. When `start > s.len()` the loop does not run and the result is
`s.len()` (line 88; plan Section 7, `start > len`). No precondition: `i + 1` (line 86) is only
computed for `i < s.len() ≤ Usize.max`. -/
@[step]
theorem next_dot_spec (s : Slice U8) (start : Usize) :
    next_dot s start ⦃ (result : Usize) =>
      (∀ j, start.val ≤ j → j < result.val → s.val[j]? ≠ some dot) ∧
      (result.val = s.length ∨
        (start.val ≤ result.val ∧ s.val[result.val]? = some dot)) ⦄ := by
  sorry

/-- **Spec theorem for `rmcp::model::request_state_wire::component_count`** (W06)

`component_count s` is the number of `.`-components of `s`, `(splitOn '.' s).length`, which is
one more than the number of `.` bytes (plan Section 2.1, W06; plan Section 3, "W06–W09 —
splitting"; lines 91–102).

Lean-model domain (plan Section 3, "Lean-model domains"): the counter starts at 1 and is
incremented once per `.` byte (lines 93, 96–98), so the call fails exactly when the slice has
`Usize.max` or more `.` bytes. `h_count` excludes that; it holds for every Rust slice, whose
length is at most `isize::MAX < usize::MAX`. -/
@[step]
theorem component_count_spec (s : Slice U8)
    (h_count : s.val.count dot < Usize.max) :
    component_count s ⦃ (result : Usize) =>
      result.val = (components s.val).length ∧
      result.val = s.val.count dot + 1 ⦄ := by
  sorry

/-- **Spec theorem for `rmcp::model::request_state_wire::version_of`** (W07)

`version_of s` is `Some V1` iff the first `.`-component of `s` is `"rs1"`, `Some V2` iff it is
`"rs2"`, and `None` otherwise (plan Section 2.1, W07; lines 114–124: the prefix up to the first
`.` (line 116) is compared with `VERSION_V1` (line 117), then `VERSION_V2` (line 119)).
`components s` is never empty, so `head?` is its first component. No precondition. -/
@[step]
theorem version_of_spec (s : Slice U8) :
    version_of s ⦃ (result : Option Version) =>
      match result with
      | some .V1 => (components s.val).head? = some versionV1
      | some .V2 => (components s.val).head? = some versionV2
      | none =>
        (components s.val).head? ≠ some versionV1 ∧
        (components s.val).head? ≠ some versionV2 ⦄ := by
  sorry

/-- **Spec theorem for `rmcp::model::request_state_wire::parse_rs1`** (W08)

`parse_rs1 s` is `Some {body, tag}` iff `splitOn '.' s = ["rs1", body, tag]`, and `None` iff
`s` does not split into `"rs1"` and two further components (plan Section 2.1, W08; plan
Section 3, "W06–W09 — splitting"; lines 136–150: component count `≠ 3` gives `None`
(138–140), first component `≠ "rs1"` gives `None` (143–145), otherwise the two remaining
components (146–149)). The returned slices are determined by their byte lists.

Lean-model domain: `h_count` is the hypothesis of W06, whose `component_count` is called first
(line 138); see `component_count_spec`. -/
@[step]
theorem parse_rs1_spec (s : Slice U8)
    (h_count : s.val.count dot < Usize.max) :
    parse_rs1 s ⦃ (result : Option Rs1Parts) =>
      match result with
      | some p => components s.val = [versionV1, p.body.val, p.tag.val]
      | none => ∀ body tag, components s.val ≠ [versionV1, body, tag] ⦄ := by
  sorry

/-- **Spec theorem for `rmcp::model::request_state_wire::parse_rs2`** (W09)

`parse_rs2 s` is `Some {kid, body, tag}` iff `splitOn '.' s = ["rs2", kid, body, tag]`, and
`None` otherwise (plan Section 2.1, W09; plan Section 3, "W06–W09 — splitting"; lines 164–180:
component count `≠ 4` gives `None` (166–168), first component `≠ "rs2"` gives `None`
(172–174), otherwise the three remaining components (175–179)).

Lean-model domain: `h_count` is the hypothesis of W06 (line 166); see
`component_count_spec`. -/
@[step]
theorem parse_rs2_spec (s : Slice U8)
    (h_count : s.val.count dot < Usize.max) :
    parse_rs2 s ⦃ (result : Option Rs2Parts) =>
      match result with
      | some p => components s.val = [versionV2, p.kid.val, p.body.val, p.tag.val]
      | none => ∀ kid body tag, components s.val ≠ [versionV2, kid, body, tag] ⦄ := by
  sorry

/-- **Spec theorem for `rmcp::model::request_state_wire::transcript_v1`** (W10)

`transcript_v1 associated_data body` is `DOMAIN_V1 ++ be64(len ad) ++ ad ++ body` (plan
Section 2.1, W10; lines 182–190). The length prefix is the byte length of `associated_data`
as a natural number: the cast `usize → u64` (line 186, `UScalar.cast .U64` in the translation)
zero-extends and is exact whether `Usize` has 32 or 64 bits in the Aeneas model, so no
target-width hypothesis is needed (plan Section 3, "W10/W11 — transcripts").

Lean-model domain (plan Section 3, "Lean-model domains"): each `extend_from_slice` fails in the
Aeneas model when the vector would exceed `Usize.max` elements, so the call fails exactly when
the transcript is longer than `Usize.max`. `h_len` excludes that; it holds whenever Rust can
allocate the result, since a `Vec<u8>` holds at most `isize::MAX` bytes (allocation failure is
an explicit assumption, plan Section 3). -/
@[step]
theorem transcript_v1_spec (associated_data : Slice U8) (body : Slice U8)
    (h_len : (transcriptV1 associated_data.val body.val).length ≤ Usize.max) :
    transcript_v1 associated_data body ⦃ (result : alloc.vec.Vec U8) =>
      result.val = transcriptV1 associated_data.val body.val ⦄ := by
  sorry

/-- **Spec theorem for `rmcp::model::request_state_wire::transcript_v2`** (W11)

`transcript_v2 kid associated_data body` is
`DOMAIN_V2 ++ be64(len kid) ++ kid ++ be64(len ad) ++ ad ++ body` (plan Section 2.1, W11;
lines 192–202). Both length prefixes are exact byte lengths (casts on lines 196 and 198; see
`transcript_v1_spec`).

Lean-model domain: `h_len`, as for `transcript_v1_spec`. -/
@[step]
theorem transcript_v2_spec (kid : Slice U8) (associated_data : Slice U8) (body : Slice U8)
    (h_len : (transcriptV2 kid.val associated_data.val body.val).length ≤ Usize.max) :
    transcript_v2 kid associated_data body ⦃ (result : alloc.vec.Vec U8) =>
      result.val = transcriptV2 kid.val associated_data.val body.val ⦄ := by
  sorry

/-- **Spec theorem for `rmcp::model::request_state_wire::decode_expiry`** (W12)

`decode_expiry head` is the two's-complement value of the 8 bytes of `head` read big-endian
(plan Section 2.1, W12; lines 204–207: `u64::from_be_bytes(head) as i64`). No precondition. -/
@[step]
theorem decode_expiry_spec (head : Array U8 8#usize) :
    decode_expiry head ⦃ (result : I64) =>
      result.val = toInt64 (beNat head.val) ⦄ := by
  sorry

/-- **Spec theorem for `rmcp::model::request_state_wire::is_expired`** (W13)

`is_expired expiry now_ms` is `true` iff `expiry ≠ 0 ∧ now_ms > expiry`, compared as signed
integers (plan Section 2.1, W13; plan Section 3, "W14/E01 — expiry"; lines 209–212). No
precondition. -/
@[step]
theorem is_expired_spec (expiry : I64) (now_ms : I64) :
    is_expired expiry now_ms ⦃ (result : Bool) =>
      result = decide (Expired expiry.val now_ms.val) ⦄ := by
  sorry

/-- **Spec theorem for `rmcp::model::request_state_wire::open_frame`** (W14)

`open_frame body now_ms` (plan Section 2.1, W14; lines 224–236), in the Rust order of checks:
`Err TooShort` iff `body` is shorter than `EXPIRY_LEN = 8` bytes (lines 17, 226–228);
`Err Expired` iff it has at least 8 bytes and W13 holds for the W12 value of its first 8 bytes
(lines 229–234); otherwise `Ok (body[8..])` (line 235). `now_ms = expiry` is accepted, and a
negative nonzero expiry is compared as a signed value (plan Section 3, "W14/E01 — expiry").
The returned slice is determined by its byte list. No precondition. -/
@[step]
theorem open_frame_spec (body : Slice U8) (now_ms : I64) :
    open_frame body now_ms ⦃ (result : core.result.Result (Slice U8) FrameError) =>
      match result with
      | .Err .TooShort => body.length < expiryLen
      | .Err .Expired => expiryLen ≤ body.length ∧ Expired (bodyExpiry body.val) now_ms.val
      | .Ok payload =>
        expiryLen ≤ body.length ∧ ¬ Expired (bodyExpiry body.val) now_ms.val ∧
        payload.val = body.val.drop expiryLen ⦄ := by
  sorry

/-- **Spec theorem for `rmcp::model::request_state_wire::frame`** (W15)

`frame expiry payload` is `be64(expiry as u64) ++ payload`: the 8 big-endian bytes of the
two's-complement representation of `expiry`, then the payload (plan Section 2.1, W15;
lines 238–244). The function does no arithmetic (plan Section 3).

Lean-model domain (plan Section 3, "Lean-model domains"): `h_len` says that the output fits in
`Usize.max` bytes, the exact condition under which both `extend_from_slice` calls (lines 241,
242) succeed in the Aeneas model; see `transcript_v1_spec`. -/
@[step]
theorem frame_spec (expiry : I64) (payload : Slice U8)
    (h_len : (frameBytes expiry.val payload.val).length ≤ Usize.max) :
    frame expiry payload ⦃ (result : alloc.vec.Vec U8) =>
      result.val = frameBytes expiry.val payload.val ⦄ := by
  sorry

/-- **Frame round trip** (W15 then W14)

Opening a frame built by `frame expiry payload` at a time `now_ms` at which `expiry` is not
expired returns `Ok payload` (plan Section 3, "Round-trip": `open_frame (frame e p) now = Ok p`
when `¬ is_expired e now`). Premises: the frame fits in `Usize.max` bytes (`h_len`, the domain of
`frame_spec`), and `expiry` is `0` or `now_ms ≤ expiry` (`h_live`, the negation of the W13
predicate). About the translated functions `frame` and `open_frame`; the frame is passed to
`open_frame` as the slice of the returned vector (`Vec::deref`). The statement covers both
calls: it shows that both succeed and gives the final result. -/
theorem frame_roundtrip (expiry : I64) (payload : Slice U8) (now_ms : I64)
    (h_len : (frameBytes expiry.val payload.val).length ≤ Usize.max)
    (h_live : ¬ Expired expiry.val now_ms.val) :
    (do
      let body ← frame expiry payload
      open_frame (alloc.vec.Vec.deref body) now_ms)
      ⦃ (result : core.result.Result (Slice U8) FrameError) =>
      result = .Ok payload ⦄ := by
  sorry

end rmcp.model.request_state_wire
