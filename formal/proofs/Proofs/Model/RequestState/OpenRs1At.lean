/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Rmcp.Funs
import Defs.Wire
import Defs.CodecState
import Proofs.External.Base64
import Proofs.External.String
import Proofs.External.Std
import Proofs.External.Prim
import Proofs.Model.RequestStateWire.Common
import Proofs.Model.RequestStateWire.ParseRs1
import Proofs.Model.RequestStateWire.TranscriptV1
import Proofs.Model.RequestState.OpenAuthenticatedBody
import Proofs.Model.RequestState.Rs1FallbacksVerify

/-!
# Spec theorem for `RequestStateCodec::open_rs1_at` (E09)

Opens an `rs1` token: parses it into body and tag (W08), rejects a keyring codec without rs1
fallback ids, decodes body and tag from Base64, verifies the tag over the W10 transcript (single
key directly, keyring through `rs1_fallbacks_verify`, E09a), then opens the body (E01).

Source: "crates/rmcp/src/model/request_state.rs", line 607 at local commit `46cfb02`
(the translation base; not yet a pinned fork commit).

Proof: one case per check in Rust order, each closed against the matching branch of
`Defs.CodecState.openRs1`; the callees are used through their spec theorems.
-/

open Aeneas Aeneas.Std Result
open rmcp
open rmcp.model.request_state
open Defs.Wire (dot versionV1 components transcriptV1)
open Defs.CodecState (CodecFallbacksKnown openRs1 resultBytes)

namespace rmcp.model.request_state.RequestStateCodec

/-- **Spec theorem for `rmcp::model::request_state::RequestStateCodec::open_rs1_at`** (E09)

`resultBytes result = openRs1 …`: the result is exactly the expected result of
`Defs.CodecState.openRs1` (module `Defs.CodecState`; `resultBytes` is injective, so this fixes
the whole result value), which fixes the complete error order of plan Section 3 ("E09 —
error order"): `MalformedFormat` (W08, lines 613–615); keyring with no rs1 fallback →
`UnknownKeyId` before any decoding (lines 617–621); body, then tag not Base64 →
`InvalidEncoding` (lines 623–624); no configured key verifies the tag over
`transcriptV1 associated_data body` → `IntegrityCheckFailed` (lines 627–638; single key: its
key; keyring: some rs1 fallback key, `Rs1Verifies`, without saying which); otherwise E01 on the
decoded body (line 640). The statement says nothing about timing.

Preconditions:

* `h_count`: fewer than `Usize.max` `.` bytes in the token, for every token (W08 is called on
  every token, line 613; W08 domain, plan Section 3, "Lean-model domains"). Not dischargeable
  from the input: a `Slice` gives only `count ≤ length ≤ Usize.max`.
* `h_len`: for a token `["rs1", b, t]` whose body `b` decodes to `body` (line 623), the
  transcript `transcriptV1 associated_data body` built on line 627 fits in `Usize.max` bytes
  (W10 domain). Vacuous for tokens of another shape or with a body that does not decode; it is
  still required for tokens that fail before line 627 (no fallback, tag not Base64), so it is
  not the exact weakest condition.
* `h_fallbacks`: every rs1 fallback id of a keyring codec is a key id, so that
  `keys.get(kid).expect(..)` (line 652) does not panic (plan Section 3, step 4; the clause of the
  codec-state predicate of plan Section 4 that E09 needs; a hypothesis, plan Section 2.3). It is
  a premise on the codec alone and is required for every token, although line 652 is reached
  only for a keyring codec with a nonempty fallback list and a token that passes lines 613–624.
  The other clauses of `Defs.CodecState.CodecValid` (distinct ids, the seal-mode key, key
  lengths, kid validity) are not needed: HMAC accepts keys of any length.

Stated exceptions. Under plan Section 4, assumption "Unlimited memory" (row "Standard
library"), allocation failure is not modelled and the transcript `Vec` of line 627 is modelled
up to `Usize.max` bytes, whereas a Rust `Vec<u8>` panics above `isize::MAX` bytes. Under the size
convention of `formal/trusted/Rmcp/FunsExternal.lean` (plan Section 4, row "HMAC"),
`hmac_sha256_verify` (line 629, and line 653 through E09a) is modelled as always succeeding,
whereas the `u64` bit-length counter of SHA-256 overflows, a panic under `overflow-checks`, for a
transcript of at least `2^61 − 64` bytes or a key (the single key, or a key tried by E09a) of at
least `2^61` bytes. For such inputs the statement promises a result where the Rust code panics.

Assumptions: through E09a (lines 628–635) the statement reaches the locked native-code assumption
`rmcp.model.request_state.RequestStateCodec.rs1_fallbacks_verify_loop.body._native.decide.ax_3`
(`toStr "validated rs1 fallback key"`, the `expect` message of line 652;
`formal/trusted/native-axioms.lock`), so its `#print axioms` list will include it. -/
@[step]
theorem open_rs1_at_spec (self : RequestStateCodec) (sealed : Str)
    (associated_data : Slice Std.U8) (now_ms : Std.I64)
    (h_count : (sealed : Slice Std.U8).val.count dot < Usize.max)
    (h_len : ∀ b t body, components (sealed : Slice Std.U8).val = [versionV1, b, t] →
      ExtModel.b64Decode b = some body →
      (transcriptV1 associated_data.val body).length ≤ Usize.max)
    (h_fallbacks : CodecFallbacksKnown self) :
    open_rs1_at self sealed associated_data now_ms ⦃ (result :
        core.result.Result (alloc.vec.Vec Std.U8) RequestStateError) =>
      -- lines 613–640, in the order of plan Section 3 (see `Defs.CodecState.openRs1`)
      resultBytes result = openRs1 self (sealed : Slice Std.U8).val associated_data.val
        now_ms.val ⦄ := by
  unfold open_rs1_at
  simp only [core.str.Str.as_bytes, bind_tc_ok]
  apply WP.spec_bind (rmcp.model.request_state_wire.parse_rs1_spec _ h_count)
  intro o ho
  cases o with
  | none =>
    rw [WP.spec_ok]
    unfold openRs1
    split
    · rename_i v b t hc
      have : v ≠ Defs.Wire.versionV1 := fun hv => ho b t (hv ▸ hc)
      simp [resultBytes, this]
    · simp [resultBytes]
  | some rp =>
    simp only at ho
    have hrs : openRs1 self (sealed : Slice Std.U8).val associated_data.val now_ms.val =
        (if Defs.CodecState.NoRs1Fallback self then .error .UnknownKeyId else
          match ExtModel.b64Decode rp.body.val, ExtModel.b64Decode rp.tag.val with
          | none, _ => .error .InvalidEncoding
          | some _, none => .error .InvalidEncoding
          | some body, some tag =>
            if Defs.CodecState.Rs1Accepts self (transcriptV1 associated_data.val body) tag
            then Defs.CodecState.openBody body now_ms.val
            else .error .IntegrityCheckFailed) := by
      unfold openRs1; rw [ho]; simp only [ne_eq, not_true_eq_false, if_false]; rfl
    rw [hrs]
    rcases self with ⟨keys⟩
    cases keys with
    | Single key =>
      simp only [Defs.CodecState.NoRs1Fallback, Bool.false_eq_true, if_false]
      apply WP.spec_bind (model.request_state_wire.prim.b64_decode_spec rp.body)
      intro o1 ho1
      cases o1 with
      | none =>
        simp only [Option.map_none] at ho1
        simp [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          ← ho1, resultBytes]
      | some body =>
        simp only [Option.map_some] at ho1
        simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
          bind_tc_ok]
        apply WP.spec_bind (model.request_state_wire.prim.b64_decode_spec rp.tag)
        intro o2 ho2
        cases o2 with
        | none =>
          simp only [Option.map_none] at ho2
          simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            ← ho1, ← ho2, resultBytes]
        | some tag =>
          simp only [Option.map_some] at ho2
          simp only [bind_tc_ok]
          have hl := h_len rp.body.val rp.tag.val body.val ho ho1.symm
          apply WP.spec_bind (rmcp.model.request_state_wire.transcript_v1_spec _ _ hl)
          intro tr htr
          step as ⟨kv, hkv⟩
          rw [hkv]
          apply WP.spec_bind (model.request_state_wire.prim.hmac_sha256_verify_spec _ _ _)
          intro ver hver
          rw [← ho1, ← ho2]
          simp only [alloc.vec.Vec.deref, htr] at hver
          by_cases hacc : Defs.CodecState.Rs1Accepts ⟨.Single key⟩
            (transcriptV1 associated_data.val body.val) tag.val
          · have hv : ver = true := by
              simp only [Defs.CodecState.Rs1Accepts, Defs.CodecState.TagVerifies] at hacc
              simp [hver, hacc]
            simp only [hv, if_true, if_pos hacc]
            apply WP.spec_mono
              (rmcp.model.request_state.RequestStateCodec.open_authenticated_body_spec body now_ms)
            intro r hr
            unfold Defs.CodecState.openBody
            cases r with
            | Ok p =>
              obtain ⟨h1, h2, h3⟩ := hr
              simp [resultBytes, Defs.Wire.expiryLen] at *
              simp [show ¬ body.val.length < 8 by omega, h2, h3]
            | Err e =>
              rcases hr with ⟨h1, he⟩ | ⟨h1, h2, he⟩
              · simp [resultBytes, he, Defs.Wire.expiryLen] at *; simp [h1]
              · simp [resultBytes, he, Defs.Wire.expiryLen] at *
                simp [show ¬ body.val.length < 8 by omega, h2]
          · have hv : ver = false := by
              simp only [Defs.CodecState.Rs1Accepts, Defs.CodecState.TagVerifies] at hacc
              simp [hver, hacc]
            simp [hv, if_neg hacc, resultBytes]
    | Ring keys mode fbs =>
      apply WP.spec_bind (alloc.vec.Vec.is_empty_spec _ fbs)
      intro b hb
      by_cases hemp : fbs.val = []
      · have hnf : Defs.CodecState.NoRs1Fallback ⟨.Ring keys mode fbs⟩ = true := by
          simp [Defs.CodecState.NoRs1Fallback, hemp]
        simp [hb, hemp, hnf, resultBytes]
      have hnf : Defs.CodecState.NoRs1Fallback ⟨.Ring keys mode fbs⟩ = false := by
        simp [Defs.CodecState.NoRs1Fallback, hemp]
      simp only [hb, hemp, decide_false, Bool.false_eq_true, if_false, hnf]
      apply WP.spec_bind (model.request_state_wire.prim.b64_decode_spec rp.body)
      intro o1 ho1
      cases o1 with
      | none =>
        simp only [Option.map_none] at ho1
        simp [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          ← ho1, resultBytes]
      | some body =>
        simp only [Option.map_some] at ho1
        simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
          bind_tc_ok]
        apply WP.spec_bind (model.request_state_wire.prim.b64_decode_spec rp.tag)
        intro o2 ho2
        cases o2 with
        | none =>
          simp only [Option.map_none] at ho2
          simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            ← ho1, ← ho2, resultBytes]
        | some tag =>
          simp only [Option.map_some] at ho2
          simp only [bind_tc_ok]
          have hl := h_len rp.body.val rp.tag.val body.val ho ho1.symm
          apply WP.spec_bind (rmcp.model.request_state_wire.transcript_v1_spec _ _ hl)
          intro tr htr
          apply WP.spec_bind (rs1_fallbacks_verify_spec keys _ _ _ h_fallbacks)
          intro ver hver
          rw [← ho1, ← ho2]
          simp only [alloc.vec.Vec.deref, htr] at hver
          by_cases hacc : Defs.CodecState.Rs1Accepts ⟨.Ring keys mode fbs⟩
            (transcriptV1 associated_data.val body.val) tag.val
          · have hv : ver = true := by
              simp only [Defs.CodecState.Rs1Accepts] at hacc
              simp [hver, hacc]
            simp only [hv, if_true, if_pos hacc]
            apply WP.spec_mono
              (rmcp.model.request_state.RequestStateCodec.open_authenticated_body_spec body now_ms)
            intro r hr
            unfold Defs.CodecState.openBody
            cases r with
            | Ok p =>
              obtain ⟨h1, h2, h3⟩ := hr
              simp [resultBytes, Defs.Wire.expiryLen] at *
              simp [show ¬ body.val.length < 8 by omega, h2, h3]
            | Err e =>
              rcases hr with ⟨h1, he⟩ | ⟨h1, h2, he⟩
              · simp [resultBytes, he, Defs.Wire.expiryLen] at *; simp [h1]
              · simp [resultBytes, he, Defs.Wire.expiryLen] at *
                simp [show ¬ body.val.length < 8 by omega, h2]
          · have hv : ver = false := by
              simp only [Defs.CodecState.Rs1Accepts] at hacc
              simp [hver, hacc]
            simp [hv, if_neg hacc, resultBytes]

end rmcp.model.request_state.RequestStateCodec
