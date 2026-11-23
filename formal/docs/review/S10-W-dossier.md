# Review dossier — S10 completed specs (W07–W11)

Status: **completed and staged, awaiting your review** (2026-11-23). Statements signed off by the spec owner (S05); proofs checked by Lean; reviews finalized with no open error. Not incorporated (staged in `formal/proofs/Proofs/Model/RequestStateWire/` and `formal/specs/Drafts/Staged/RequestStateWire.lean`; statements still in `formal/specs/Drafts/RequestStateWire.lean`; records `proof: OPEN` with `# proof staged`).

**Incorporation:** together with the 11 S06 specs, in one change — `formal/docs/review/W-batch-incorporation.md` (step 0 text-identity check 16/16 and step 0b guard pre-check before any move; executed literally in a fresh git copy by two agents, all steps exit 0).

## Common to all five

- `#print axioms`: `[propext, Classical.choice, Quot.sound]` for every theorem; all 28 helpers print subsets of that set.
- Statement identity: draft = staged `recall` = proof, by text (16/16) and by elaborated type (pp.all, 443 lines identical).
- Proofs use W04/W05/W06 theorems via `step`; no W05/W06 definition unfolded (checked on the proof terms); generated constants `VERSION_V1/2`, `DOMAIN_V1/2` unfolded only in helpers.
- Build 2–4 s per module, no heartbeat changes; flexible tactics allowed in phase B (some `rename_i` after `split`, to tidy in phase C).

## Review history (arguments and counterarguments)

- **Spec (S05):** signed off by you 2026-11-23 (exhaustive small-string checks of the parsers, 335,923 strings).
- **Proof round 1:** two independent reviewers; proofs clean; **blocking** in the incorporation procedure (check after move; build with 16 recalls but 11 modules; shared staged file broke S06's standalone route) → one combined W-batch procedure, simulated literally. Also: helper lemmas for E09–E11 (`length_transcriptV1/V2`, `count_dot_lt_of_length_lt`), unused premise dropped, names aligned, "fails exactly" overclaims reworded (only the excluding direction is proved).
- **Proof round 2 (confirming):** no blocking; reran the whole procedure literally (incl. pre-commit hook), negative tests for steps 0/0b fail as they should. Remaining doc nits (one more "exact condition" phrase, S06's old 11-module recipe not marked historical, procedure notes) → fixed by the lead and re-verified (16/16).
- **Open (not errors):** E09–E11 must supply W08/W09 `h_count` and W10/W11 `h_len`; for decoded bodies this needs an S08/S09 choice (Base64 length law vs a premise on decoded parts) — recorded in STATUS.

## Per target

### W07 `rmcp.model.request_state_wire.version_of_spec`

- Rust: `version_of` — `crates/rmcp/src/model/request_state_wire.rs` lines 115–124 (at `adce319`)
- Proof: `formal/proofs/Proofs/Model/RequestStateWire/VersionOf.lean`
- Verification: No premise. First `.`-component `rs1` → V1, `rs2` → V2, else none; evaluated on `rs1`, `rs2`, `rs3`, `rs1x`, empty, no dot, and exhaustively on short strings; concrete check `"rs10"` → none. Reused by E11.

```lean
recall rmcp.model.request_state_wire.version_of_spec (s : Slice U8) :
    rmcp.model.request_state_wire.version_of s ⦃ (result : Option Version) =>
      match result with
      | some .V1 => (components s.val).head? = some versionV1
      | some .V2 => (components s.val).head? = some versionV2
      | none =>
        (components s.val).head? ≠ some versionV1 ∧
        (components s.val).head? ≠ some versionV2 ⦄
```

### W08 `rmcp.model.request_state_wire.parse_rs1_spec`

- Rust: `parse_rs1` — `crates/rmcp/src/model/request_state_wire.rs` lines 137–150 (at `adce319`)
- Proof: `formal/proofs/Proofs/Model/RequestStateWire/ParseRs1.lean`
- Verification: Premise `count dot < Usize.max` (exact Lean-model condition; holds for every Rust slice). Accepting and rejecting tokens instantiated (`rs1.ab.cd` → some; `rs2.ab.cd`, `rs1.ab` → none). Uses W05/W06 theorems via `step`. Reused by E09.

```lean
recall rmcp.model.request_state_wire.parse_rs1_spec (s : Slice U8)
    (h_count : s.val.count dot < Usize.max) :
    rmcp.model.request_state_wire.parse_rs1 s ⦃ (result : Option Rs1Parts) =>
      match result with
      | some p => components s.val = [versionV1, p.body.val, p.tag.val]
      | none => ∀ body tag, components s.val ≠ [versionV1, body, tag] ⦄
```

### W09 `rmcp.model.request_state_wire.parse_rs2_spec`

- Rust: `parse_rs2` — `crates/rmcp/src/model/request_state_wire.rs` lines 165–180 (at `adce319`)
- Proof: `formal/proofs/Proofs/Model/RequestStateWire/ParseRs2.lean`
- Verification: Same premise; `rs2.k.b.t` → some, `rs1.k.b.t` → none. Reused by E10.

```lean
recall rmcp.model.request_state_wire.parse_rs2_spec (s : Slice U8)
    (h_count : s.val.count dot < Usize.max) :
    rmcp.model.request_state_wire.parse_rs2 s ⦃ (result : Option Rs2Parts) =>
      match result with
      | some p => components s.val = [versionV2, p.kid.val, p.body.val, p.tag.val]
      | none => ∀ kid body tag, components s.val ≠ [versionV2, kid, body, tag] ⦄
```

### W10 `rmcp.model.request_state_wire.transcript_v1_spec`

- Rust: `transcript_v1` — `crates/rmcp/src/model/request_state_wire.rs` lines 183–190 (at `adce319`)
- Proof: `formal/proofs/Proofs/Model/RequestStateWire/TranscriptV1.lean`
- Verification: Premise: transcript length ≤ Usize.max (excludes the Aeneas failure of `extend_from_slice`; only this direction proved). Concrete: ad=[1,2], body=[3] gives `domainV1 ++ be64 2 ++ [1,2,3]`. Helper `length_transcriptV1` = 34 + ad + body for callers.

```lean
recall rmcp.model.request_state_wire.transcript_v1_spec (associated_data : Slice U8)
    (body : Slice U8)
    (h_len : (transcriptV1 associated_data.val body.val).length ≤ Usize.max) :
    rmcp.model.request_state_wire.transcript_v1 associated_data body
      ⦃ (result : alloc.vec.Vec U8) =>
      result.val = transcriptV1 associated_data.val body.val ⦄
```

### W11 `rmcp.model.request_state_wire.transcript_v2_spec`

- Rust: `transcript_v2` — `crates/rmcp/src/model/request_state_wire.rs` lines 193–202 (at `adce319`)
- Proof: `formal/proofs/Proofs/Model/RequestStateWire/TranscriptV2.lean`
- Verification: Same kind of premise; helper `length_transcriptV2` = 42 + kid + ad + body; concrete kid/ad/body instance checked.

```lean
recall rmcp.model.request_state_wire.transcript_v2_spec (kid : Slice U8)
    (associated_data : Slice U8) (body : Slice U8)
    (h_len : (transcriptV2 kid.val associated_data.val body.val).length ≤ Usize.max) :
    rmcp.model.request_state_wire.transcript_v2 kid associated_data body
      ⦃ (result : alloc.vec.Vec U8) =>
      result.val = transcriptV2 kid.val associated_data.val body.val ⦄
```

