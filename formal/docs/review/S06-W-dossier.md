# Review dossier — S06 completed specs (W01–W06, W12–W15, frame_roundtrip)

Status: **completed and staged, awaiting your review** (2026-11-23). Statement signed off by the spec owner (S05); proof checked by Lean; reviews finalized with no open error. Nothing is incorporated: proofs are not imported by `formal/proofs/Proofs.lean`, the spec-file content is staged in `formal/specs/Drafts/Staged/RequestStateWire.lean`, statements remain in `formal/specs/Drafts/RequestStateWire.lean`, records say `proof: OPEN` with a `# proof staged` comment. To incorporate, follow `formal/docs/review/W-batch-incorporation.md`, the single procedure for the whole W batch (S06 and S10 share the staged spec file; it supersedes the earlier procedure in `evidence/S06.md`); its step 0 runs the 16-name text-identity check before any file is moved.

## Common to all 11

- `#print axioms`: `[propext, Classical.choice, Quot.sound]` for every theorem (checked by the staged `#guard_msgs` blocks and independently by two reviewers). No trusted (external) or native-code axiom is used.
- Statement identity: draft = staged `recall` = proof, by text (embedded checker, 11/11; it also catches definitionally-equal rewordings) and by elaborated type (`pp.all`, two reviewers).
- Simulated incorporation: `lake build`, `lean-guard.sh sources`, `build-log`, `axioms` (kernel replay of ~899 constants) all pass.
- Shared helpers: `formal/proofs/Proofs/Model/RequestStateWire/Common.lean`, namespace `Proofs.RequestStateWire`, all proved, same three axioms.
- Build: each module 2–6 s, no `maxHeartbeats` change. Proofs use flexible tactics (allowed in phase B; phase C replaces them).
- Translation base: commit `adce319` (Aeneas `nightly-2026.08.20-5d08da4`).

## Review history (arguments and counterarguments)

- **Spec (S05):** 2 rounds + E-side round 3; 3 independent reviews, no blocking. Counterexample searches on the translation found none; domains confirmed exact; a reviewer proved 7 W statements as stated in scratch. Signed off by you 2026-11-23 with the lead defaults.
- **Proof (S06), round 1:** two independent proof reviewers, no blocking. Objections raised and resolved: helpers declared in `Defs.Wire`/`rmcp` namespaces → moved to `Proofs.RequestStateWire`; `recall` checks only definitional equality → text-identity checker added to the incorporation steps; staged reproduction steps missed `lake build Defs` → fixed; incorporation steps incomplete → completed; source references → `adce319`; records/board stale → refreshed; non-Mathlib lemma names → renamed; two reusable lemmas added for S10.
- **Proof (S06), round 2 (confirming):** no blocking; two doc nits (a proof docstring pointing at the S10 theorem; checker location/order) → fixed by the lead and re-verified.
- **Accepted / open (not errors):** E callers must supply W06's `count dot < Usize.max` premise (recorded for S13); the `Mathlib.Tactic.Recall` import in the spec file is a layering-table exception to record at incorporation; some proof steps depend on Aeneas-generated hypothesis names (phase C).

## Per target

### W01 `rmcp.model.request_state_wire.b64_len_spec`

- Rust: `b64_len` — `crates/rmcp/src/model/request_state_wire.rs` lines 33–36 (at `adce319`)
- Proof: `formal/proofs/Proofs/Model/RequestStateWire/B64Len.lean`
- Verification: Premise `b64Len len ≤ Usize.max` is the exact no-overflow domain (largest 64-bit input 13835058055282163709 accepted, +1 fails). Evaluated n = 0…999 and the boundary; matches Rust `div_ceil(3)*4`. Reused by E02 (proved from it in scratch).

```lean
recall rmcp.model.request_state_wire.b64_len_spec (len : Usize)
    (h_no_overflow : b64Len len.val ≤ Usize.max) :
    rmcp.model.request_state_wire.b64_len len ⦃ (result : Usize) =>
      result.val = b64Len len.val ⦄
```

### W02 `rmcp.model.request_state_wire.key_length_ok_spec`

- Rust: `key_length_ok` — `crates/rmcp/src/model/request_state_wire.rs` lines 38–41 (at `adce319`)
- Proof: `formal/proofs/Proofs/Model/RequestStateWire/KeyLengthOk.lean`
- Verification: No premise. Boundary 31/32/33 evaluated. Reused by E03.

```lean
recall rmcp.model.request_state_wire.key_length_ok_spec (len : Usize) :
    rmcp.model.request_state_wire.key_length_ok len ⦃ (result : Bool) =>
      result = decide (minKeyLength ≤ len.val) ⦄
```

### W03 `rmcp.model.request_state_wire.check_kid_len_spec`

- Rust: `check_kid_len` — `crates/rmcp/src/model/request_state_wire.rs` lines 54–62 (at `adce319`)
- Proof: `formal/proofs/Proofs/Model/RequestStateWire/CheckKidLen.lean`
- Verification: No premise; Rust check order (empty before too long). 0/1/255/256 and multibyte UTF-8 crossing 255 evaluated. Reused by E04.

```lean
recall rmcp.model.request_state_wire.check_kid_len_spec (len : Usize) :
    rmcp.model.request_state_wire.check_kid_len len
      ⦃ (result : core.result.Result Unit KidError) =>
      match result with
      | .Err .Empty => len.val = 0
      | .Err .TooLong => maxKidLen < len.val
      | .Ok () => 0 < len.val ∧ len.val ≤ maxKidLen ⦄
```

### W04 `rmcp.model.request_state_wire.bytes_eq_spec`

- Rust: `bytes_eq` — `crates/rmcp/src/model/request_state_wire.rs` lines 64–77 (at `adce319`)
- Proof: `formal/proofs/Proofs/Model/RequestStateWire/BytesEq.lean`
- Verification: No premise; all pairs of strings of length ≤ 3 evaluated.

```lean
recall rmcp.model.request_state_wire.bytes_eq_spec (a : Slice U8) (b : Slice U8) :
    rmcp.model.request_state_wire.bytes_eq a b ⦃ (result : Bool) =>
      result = decide (a.val = b.val) ⦄
```

### W05 `rmcp.model.request_state_wire.next_dot_spec`

- Rust: `next_dot` — `crates/rmcp/src/model/request_state_wire.rs` lines 79–89 (at `adce319`)
- Proof: `formal/proofs/Proofs/Model/RequestStateWire/NextDot.lean`
- Verification: No premise; postcondition pins the result uniquely incl. start > len; checked on all 335,923 byte strings of length ≤ 7 over {. r s 1 2 x} with every start.

```lean
recall rmcp.model.request_state_wire.next_dot_spec (s : Slice U8) (start : Usize) :
    rmcp.model.request_state_wire.next_dot s start ⦃ (result : Usize) =>
      (∀ j, start.val ≤ j → j < result.val → s.val[j]? ≠ some dot) ∧
      (result.val = s.length ∨
        (start.val ≤ result.val ∧ s.val[result.val]? = some dot)) ⦄
```

### W06 `rmcp.model.request_state_wire.component_count_spec`

- Rust: `component_count` — `crates/rmcp/src/model/request_state_wire.rs` lines 91–102 (at `adce319`)
- Proof: `formal/proofs/Proofs/Model/RequestStateWire/ComponentCount.lean`
- Verification: Premise `count dot < Usize.max` (exact no-fail condition, weaker than the plan's `length < Usize.max`); exhaustive small-string check. Callers E09–E11 must supply it (recorded open item).

```lean
recall rmcp.model.request_state_wire.component_count_spec (s : Slice U8)
    (h_count : s.val.count dot < Usize.max) :
    rmcp.model.request_state_wire.component_count s ⦃ (result : Usize) =>
      result.val = (components s.val).length ∧
      result.val = s.val.count dot + 1 ⦄
```

### W12 `rmcp.model.request_state_wire.decode_expiry_spec`

- Rust: `decode_expiry` — `crates/rmcp/src/model/request_state_wire.rs` lines 204–207 (at `adce319`)
- Proof: `formal/proofs/Proofs/Model/RequestStateWire/DecodeExpiry.lean`
- Verification: No premise; signed big-endian (all-0xFF → −1, 0x80… → i64::MIN) evaluated by `rfl` on the translation.

```lean
recall rmcp.model.request_state_wire.decode_expiry_spec (head : Array U8 8#usize) :
    rmcp.model.request_state_wire.decode_expiry head ⦃ (result : I64) =>
      result.val = toInt64 (beNat head.val) ⦄
```

### W13 `rmcp.model.request_state_wire.is_expired_spec`

- Rust: `is_expired` — `crates/rmcp/src/model/request_state_wire.rs` lines 209–212 (at `adce319`)
- Proof: `formal/proofs/Proofs/Model/RequestStateWire/IsExpired.lean`
- Verification: No premise; `expiry ≠ 0 ∧ now > expiry`; now = expiry not expired; negative expiry; i64 extremes.

```lean
recall rmcp.model.request_state_wire.is_expired_spec (expiry : I64) (now_ms : I64) :
    rmcp.model.request_state_wire.is_expired expiry now_ms ⦃ (result : Bool) =>
      result = decide (Expired expiry.val now_ms.val) ⦄
```

### W14 `rmcp.model.request_state_wire.open_frame_spec`

- Rust: `open_frame` — `crates/rmcp/src/model/request_state_wire.rs` lines 224–236 (at `adce319`)
- Proof: `formal/proofs/Proofs/Model/RequestStateWire/OpenFrame.lean`
- Verification: No premise; order TooShort → Expired → Ok(body[8..]); proof uses W12/W13 theorems (no unfolding). Same terms as E01, so E01 follows from it.

```lean
recall rmcp.model.request_state_wire.open_frame_spec (body : Slice U8) (now_ms : I64) :
    rmcp.model.request_state_wire.open_frame body now_ms
      ⦃ (result : core.result.Result (Slice U8) FrameError) =>
      match result with
      | .Err .TooShort => body.length < expiryLen
      | .Err .Expired => expiryLen ≤ body.length ∧ Expired (bodyExpiry body.val) now_ms.val
      | .Ok payload =>
        expiryLen ≤ body.length ∧ ¬ Expired (bodyExpiry body.val) now_ms.val ∧
        payload.val = body.val.drop expiryLen ⦄
```

### W15 `rmcp.model.request_state_wire.frame_spec`

- Rust: `frame` — `crates/rmcp/src/model/request_state_wire.rs` lines 238–244 (at `adce319`)
- Proof: `formal/proofs/Proofs/Model/RequestStateWire/Frame.lean`
- Verification: Premise: output length ≤ Usize.max (exact `extend_from_slice` condition).

```lean
recall rmcp.model.request_state_wire.frame_spec (expiry : I64) (payload : Slice U8)
    (h_len : (frameBytes expiry.val payload.val).length ≤ Usize.max) :
    rmcp.model.request_state_wire.frame expiry payload ⦃ (result : alloc.vec.Vec U8) =>
      result.val = frameBytes expiry.val payload.val ⦄
```

### — `rmcp.model.request_state_wire.frame_roundtrip`

- Rust: `frame + open_frame` — `crates/rmcp/src/model/request_state_wire.rs` lines plan §3 round trip (at `adce319`)
- Proof: `formal/proofs/Proofs/Model/RequestStateWire/Frame.lean`
- Verification: Premises satisfiable (instantiated with expiry 5, payload [1,2], now 5; and expiry 0/now 7); uses W14/W15 theorems via `step`; helper `bodyExpiry_frameBytes` (i64 range).

```lean
recall rmcp.model.request_state_wire.frame_roundtrip (expiry : I64) (payload : Slice U8)
    (now_ms : I64)
    (h_len : (frameBytes expiry.val payload.val).length ≤ Usize.max)
    (h_live : ¬ Expired expiry.val now_ms.val) :
    (do
      let body ← rmcp.model.request_state_wire.frame expiry payload
      rmcp.model.request_state_wire.open_frame (alloc.vec.Vec.deref body) now_ms)
      ⦃ (result : core.result.Result (Slice U8) FrameError) =>
      result = .Ok payload ⦄
```

