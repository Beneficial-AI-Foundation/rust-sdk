/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Rmcp.Funs
public import Defs.Wire
public import Defs.CodecState
public import Proofs.External.Base64
public import Proofs.Model.RequestStateWire.Common
public import Proofs.Model.RequestState.ValidateKeyLength
public import Proofs.Model.RequestState.OpenAt

@[expose] public section

/-!
# Spec theorems for the public API of `request_state.rs` (R01–R08)

The builders of `SealOptions` (R01 `new`, R02 `associated_data`, R03 `ttl`), the constructors of
`RequestStateCodec` (R04 `new`, R05 `new_unchecked`, R06 `try_new`) and the opening wrappers
(R07 `open`, R08 `open_with`, and the corollary `open_with_spec_of_length_le` of R08). The
builders and constructors are proved by unfolding; `try_new` uses E03 `validate_key_length_spec`;
`open_with` is E11 `open_at_spec` at the clock reading `ExtModel.nowMs`; `open` is `open_with`
with empty associated data, whose transcript premises hold for every token because a decoded
Base64 component has at most three quarters of the bytes of its text.

Source: "crates/rmcp/src/model/request_state.rs", lines 145–173 (`SealOptions`), 278–304
(constructors) and 476–501 (`open`, `open_with`) in the patched copy (patch 01 on origin/main
`7caec76`, D2 fallback 2026-11-23); ten lines lower at upstream `7caec76`.
-/

open Aeneas Aeneas.Std Result
open Defs.Wire (components versionV1 versionV2 transcriptV1 transcriptV2 minKeyLength)
open Defs.CodecState (CodecValid CodecFallbacksKnown openAt resultBytes)
open rmcp.model.request_state (SealOptions RequestStateCodec Keys RequestStateError)

/-! ## `SealOptions` (patched lines 145–173, upstream 155–183)

`SealOptions<'a>` has the two private fields `associated_data: &'a [u8]` and
`ttl: Option<Duration>` (patched lines 145–149, upstream 155–159), translated to the structure
`rmcp.model.request_state.SealOptions`. No premise: the builders only move values. -/

namespace rmcp.model.request_state.SealOptions

/-- **R01. Spec theorem for `rmcp::model::request_state::SealOptions::new`**

Empty options: no associated data and no time-to-live. `new` is `Self::default()` (patched lines
153–155, upstream 163–165), and the derived `Default` (patched line 145, upstream 155) gives the
empty slice `<&[u8]>::default()` and `Option::<Duration>::default() = None`. The two fields
determine the result (a `Slice` is determined by its `val`). -/
@[step]
theorem new_spec :
    new ⦃ (result : SealOptions) =>
      result.associated_data.val = [] ∧
      result.ttl = none ⦄ := by
  simp only [new, Insts.CoreDefaultDefault.default, Shared0Slice.Insts.CoreDefaultDefault.default,
    Slice.new_val, core.option.Option.Insts.CoreDefaultDefault.default, bind_ok, WP.spec_ok,
    and_self]

/-- **R02. Spec theorem for `rmcp::model::request_state::SealOptions::associated_data`**

Sets the associated data to the given slice and keeps the time-to-live (patched lines 163–166,
upstream 173–176: `self.associated_data = associated_data; self`). -/
@[step]
theorem impl.associated_data_spec (self : SealOptions) (associated_data : Slice Std.U8) :
    impl.associated_data self associated_data ⦃ (result : SealOptions) =>
      result.associated_data = associated_data ∧
      result.ttl = self.ttl ⦄ := by
  simp only [impl.associated_data, WP.spec_ok, and_self]

/-- **R03. Spec theorem for `rmcp::model::request_state::SealOptions::ttl`**

Sets the time-to-live to `Some ttl` and keeps the associated data (patched lines 170–173,
upstream 180–183: `self.ttl = Some(ttl); self`). Any `Duration` is accepted; the conversion to
an expiry happens in the excluded `seal_at` (plan Section 2.3). -/
@[step]
theorem impl.ttl_spec (self : SealOptions) (ttl : core.time.Duration) :
    impl.ttl self ttl ⦃ (result : SealOptions) =>
      result.associated_data = self.associated_data ∧
      result.ttl = some ttl ⦄ := by
  simp only [impl.ttl, WP.spec_ok, and_self]

end rmcp.model.request_state.SealOptions

/-! ## Constructors (patched lines 278–304, upstream 288–314)

`impl Into<Vec<u8>>` is translated as a type `T0` with an `Into T0 (Vec U8)` instance, whose
`into` is the caller's conversion (for `Vec<u8>` the identity, for `&[u8]` a copy). The premise
`h_into` names the vector it returns; if the conversion panics, so does the constructor, and the
statements say nothing about that case. `Zeroizing::new` wraps the vector unchanged
(`trusted/Rmcp/FunsExternal.lean`, model of `zeroize::Zeroizing::new`; zeroisation on drop is not
modelled, plan Section 4). -/

namespace rmcp.model.request_state.RequestStateCodec

/-- **R04. Spec theorem for `rmcp::model::request_state::RequestStateCodec::new`** (deprecated)

The single-key codec whose key is the vector `v` that `key.into()` returns, **for a key of any
length**: `new` is `Self::new_unchecked(key)` (patched lines 278–280, upstream 288–290), with no
length check and no panic. The result satisfies the codec-state predicate `CodecValid`, which
does not constrain single-key codecs (plan Section 4, "Codec state"). Rust test:
`new_accepts_short_key_for_backward_compatibility` (patched lines 805–811, upstream 817–823)
builds a codec from a 3-byte key. -/
@[step]
theorem new_spec {T0 : Type} (coreconvertIntoT0VecU8Inst : core.convert.Into T0
    (alloc.vec.Vec Std.U8)) (key : T0) (v : alloc.vec.Vec Std.U8)
    (h_into : coreconvertIntoT0VecU8Inst.into key = ok v) :
    new coreconvertIntoT0VecU8Inst key ⦃ (result : RequestStateCodec) =>
      result.keys = Keys.Single { inner := v } ∧
      CodecValid result ⦄ := by
  simp only [new, new_unchecked, h_into, zeroize.Zeroizing.new, bind_ok, CodecValid,
    WP.spec_ok, and_self]

/-- **R05. Spec theorem for `rmcp::model::request_state::RequestStateCodec::new_unchecked`**

The single-key codec whose key is the vector `v` that `key.into()` returns, for a key of any
length (patched lines 286–290, upstream 296–300:
`Self { keys: Keys::Single(Zeroizing::new(key.into())) }`). The result satisfies
`CodecValid`, which does not constrain single-key codecs (plan Section 4, "Codec state"). -/
@[step]
theorem new_unchecked_spec {T0 : Type} (coreconvertIntoT0VecU8Inst : core.convert.Into T0
    (alloc.vec.Vec Std.U8)) (key : T0) (v : alloc.vec.Vec Std.U8)
    (h_into : coreconvertIntoT0VecU8Inst.into key = ok v) :
    new_unchecked coreconvertIntoT0VecU8Inst key ⦃ (result : RequestStateCodec) =>
      result.keys = Keys.Single { inner := v } ∧
      CodecValid result ⦄ := by
  simp only [new_unchecked, h_into, zeroize.Zeroizing.new, bind_ok, CodecValid, WP.spec_ok,
    and_self]

/-- **R06. Spec theorem for `rmcp::model::request_state::RequestStateCodec::try_new`**

Converts the key (`key.into()`, wrapped in `Zeroizing`), then checks its length with
`validate_key_length` (E03; patched lines 298–304, upstream 308–314), the only check:

* `Ok codec` iff the key has at least `MIN_KEY_LENGTH = 32` bytes (`minKeyLength`; patched
  line 270 and `request_state_wire.rs` line 19, upstream line 280); `codec` is the single-key
  codec of that key, as for `new_unchecked`, and satisfies `CodecValid`;
* otherwise `Err (KeyTooShort { minimum: 32, actual: key.len() })` (`?` on E03's error,
  patched line 300, upstream 310; E03 at patched lines 704–712, upstream 755–763).

Rust tests: `try_new_accepts_key_at_minimum_length` and `try_new_rejects_key_below_minimum_length`
(patched lines 781–803, upstream 793–815). -/
@[step]
theorem try_new_spec {T0 : Type} (coreconvertIntoT0VecU8Inst : core.convert.Into T0
    (alloc.vec.Vec Std.U8)) (key : T0) (v : alloc.vec.Vec Std.U8)
    (h_into : coreconvertIntoT0VecU8Inst.into key = ok v) :
    try_new coreconvertIntoT0VecU8Inst key ⦃ (result :
        core.result.Result RequestStateCodec RequestStateError) =>
      match result with
      | .Ok codec =>
        minKeyLength ≤ v.val.length ∧
        codec.keys = Keys.Single { inner := v } ∧
        CodecValid codec
      | .Err e =>
        v.val.length < minKeyLength ∧
        ∃ minimum actual : Std.Usize, e = .KeyTooShort minimum actual ∧
          minimum.val = minKeyLength ∧ actual.val = v.val.length ⦄ := by
  unfold try_new
  simp only [h_into, zeroize.Zeroizing.new, zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
    bind_ok, alloc.vec.Vec.deref]
  step as ⟨r, hr⟩
  rcases r with _ | e
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, WP.spec_ok]
    simp only [Slice.from_val] at hr
    simp only [hr, CodecValid, and_self]
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, WP.spec_ok]
    simp only [Slice.from_val] at hr
    exact hr

/-! ## Opening (patched lines 476–501, upstream 486–511)

`open_with` reads the clock once (`Self::now_ms()`, modelled as `ok ExtModel.nowMs`) and calls
`open_at` (E11) at that reading; `open` calls `open_with` with the empty associated data. -/

/-- **R08. Spec theorem for `rmcp::model::request_state::RequestStateCodec::open_with`**

Opens `sealed` against `associated_data` at the clock reading: the result is exactly
`openAt self sealed associated_data t` for `t = ExtModel.nowMs`, the time the call reads
(`self.open_at(sealed, associated_data, Self::now_ms())`, patched lines 495–501, upstream
505–511; `now_ms` patched lines 729–731, upstream 784–786). Clock: `nowMs` is opaque, so the
statement is E11 at an arbitrary `I64` reading; it says nothing about two calls (in Rust two
calls read different times); it does not constrain the value of `nowMs`.

Premises, as in E11: `h_len1`/`h_len2` (T), the `rs1`/`rs2` transcript of the decoded body (and
kid) with `associated_data` has at most `usize::MAX` bytes; `h_fallbacks` (F), for a token whose
first component is `rs1`, every rs1 fallback id of a keyring codec is a key id (else the
`expect` at patched line 652, upstream 661, panics). (F) is justified for every codec built
through the public API: the keyring constructors `with_rs1_signing` and `with_rs1_fallback` add
an id to the fallbacks only after checking that the keyring contains it (patched lines 384–396
and 421–428, upstream 394–406 and 431–438), and `new_with_keyring` starts with no fallbacks
(patched line 361, upstream 371). These constructors are excluded from the translation, so (F)
stays a premise.

Inherited exceptions (module docstring), where Rust panics and this statement promises a
result: (K) the clock is before 1970 or outside chrono's range (`chrono::Utc::now`, evaluated
before `open_at`, so even for a malformed token); (H) a transcript of at least `2^61 − 64` bytes
or a key of at least `2^61` bytes (SHA-256 bit counter); (V) a transcript above `isize::MAX`
bytes (the `Vec` is modelled up to `usize::MAX`).

Native-code assumptions: none since the Aeneas upgrade of 2026-11-24; until then (through E11)
`rmcp.model.request_state.RequestStateCodec.rs1_fallbacks_verify_loop.body._native.decide.ax_3`. -/
@[step]
theorem open_with_spec (self : RequestStateCodec) (sealed : Str)
    (associated_data : Slice Std.U8)
    (h_len1 : ∀ b t body, components (sealed : Slice Std.U8).val = [versionV1, b, t] →
      ExtModel.b64Decode b = some body →
      (transcriptV1 associated_data.val body).length ≤ Usize.max)
    (h_len2 : ∀ k b t kid body, components (sealed : Slice Std.U8).val = [versionV2, k, b, t] →
      ExtModel.b64Decode k = some kid → ExtModel.b64Decode b = some body →
      (transcriptV2 kid associated_data.val body).length ≤ Usize.max)
    (h_fallbacks : (components (sealed : Slice Std.U8).val).head? = some versionV1 →
      CodecFallbacksKnown self) :
    open_with self sealed associated_data ⦃ (result :
        core.result.Result (alloc.vec.Vec Std.U8) RequestStateError) =>
      resultBytes result =
        openAt self (sealed : Slice Std.U8).val associated_data.val ExtModel.nowMs.val ⦄ := by
  unfold open_with model.request_state.RequestStateCodec.now_ms
  simp only [bind_ok]
  exact open_at_spec self sealed associated_data ExtModel.nowMs h_len1 h_len2 h_fallbacks

/-- **R08, corollary. `open_with` under a length premise on its arguments**

The conclusion of `open_with_spec` (R08), with the clock as in R08 (one reading, parametric; says
nothing about two calls), and with the transcript premises (T) replaced by the
simpler (L): the associated data, the token and 36 bytes together fit in `usize::MAX`
(`associated_data.len() + sealed.len() + 36 ≤ usize::MAX`). Source: R08 and the transcript
lengths of `Defs.Wire` (`transcriptV1`, `transcriptV2`; `transcript_v1`/`transcript_v2`,
`request_state_wire.rs`, plan Section 2.1, W10–W11). The constant: an `rs2` transcript has
`26 + 8 + |kid| + 8 + |ad| + |body| = 42 + |ad| + |kid| + |body|` bytes, and an `rs2` token
`rs2.k.b.t` has `6 + |k| + |b| + |t|` bytes (three for `rs2`, three dots), with
`|kid| ≤ |k|` and `|body| ≤ |b|` (`ExtModel.b64Decode_length_le`); so the transcript is at most
`|ad| + |sealed| + 36` bytes. For `rs1` the same count gives `34 + |ad| + |body|` and a token of
`5 + |b| + |t|` bytes, so at most `|ad| + |sealed| + 29`. With this coarse length law 36 is the
least constant that works for `rs2`. Premise (F), the inherited exceptions (K), (H), (V) and
the (until 2026-11-24) native-code assumption are those of R08.

Not tagged `@[step]`, so that `step` keeps selecting R08 for `open_with`. -/
theorem open_with_spec_of_length_le (self : RequestStateCodec) (sealed : Str)
    (associated_data : Slice Std.U8)
    (h_len : associated_data.val.length + (sealed : Slice Std.U8).val.length + 36 ≤ Usize.max)
    (h_fallbacks : (components (sealed : Slice Std.U8).val).head? = some versionV1 →
      CodecFallbacksKnown self) :
    open_with self sealed associated_data ⦃ (result :
        core.result.Result (alloc.vec.Vec Std.U8) RequestStateError) =>
      resultBytes result =
        openAt self (sealed : Slice Std.U8).val associated_data.val ExtModel.nowMs.val ⦄ := by
  refine open_with_spec self sealed associated_data ?_ ?_ h_fallbacks
  · intro b t body hc hb
    have h1 := Proofs.RequestStateWire.length_eq_sum_map_length_components
      (sealed : Slice Std.U8).val
    rw [hc] at h1
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at h1
    have h2 := ExtModel.b64Decode_length_le b body hb
    have hv : versionV1.length = 3 := rfl
    rw [Proofs.RequestStateWire.length_transcriptV1]
    omega
  · intro k b t kid body hc hk hb
    have h1 := Proofs.RequestStateWire.length_eq_sum_map_length_components
      (sealed : Slice Std.U8).val
    rw [hc] at h1
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at h1
    have h2 := ExtModel.b64Decode_length_le b body hb
    have h3 := ExtModel.b64Decode_length_le k kid hk
    have hv : versionV2.length = 3 := rfl
    rw [Proofs.RequestStateWire.length_transcriptV2]
    omega

/-- **R07. Spec theorem for `rmcp::model::request_state::RequestStateCodec::open`**

Opens `sealed` with no associated data at the clock reading: the result is exactly
`openAt self sealed [] t` for `t = ExtModel.nowMs`, the time the call reads
(`self.open_with(sealed, &[])`, patched lines 476–478, upstream 486–488; then `open_with` as
above). Clock: `nowMs` is opaque, so the statement is E11 at an arbitrary `I64` reading; it says
nothing about two calls (in Rust two calls read different times); it does not constrain the
value of `nowMs`.

Premise: only (F), `h_fallbacks`, for a token whose first component is `rs1`, justified as for
R08 (public keyring constructors, patched lines 384–396 and 421–428, upstream 394–406 and
431–438; excluded from the translation, so it stays a premise). The transcript premises (T) of
`open_with` are dropped because they hold for every token when the associated data is empty:
a transcript has `26 + 8 + |body|` (rs1) or `26 + 8 + |kid| + 8 + |body|` (rs2) bytes. By
`Proofs.External.Base64.b64_of_b64Decode` (`b64Decode s = some y → b64 y = s`) and
`Proofs.External.Base64.length_b64` (`(b64 y).length = (4|y| + 2) / 3`), a decoded component has
`4|y| ≤ 3|s|`; by `List.intercalate_splitOn` the components with their dots make up the token,
so `|k| + |b| ≤ |sealed|`; the token is a `Str` of at most `Usize.max` bytes (`sealed.property`);
so a transcript has at most `42 + 3 · Usize.max / 4` bytes, which is at most `Usize.max` as
`Usize.max ≥ 2^32 − 1`. (The weaker law `ExtModel.b64Decode_length_le`, `|y| ≤ |s|`, does not
suffice.)

Inherited exceptions (module docstring), where Rust panics and this statement promises a
result: (K) the clock is before 1970 or outside chrono's range (`chrono::Utc::now`, evaluated
before `open_at`, so even for a malformed token); (H) a transcript of at least `2^61 − 64` bytes
or a key of at least `2^61` bytes (SHA-256 bit counter). (V) does not arise: the transcript has
at most `42 + 3n/4` bytes for a token of `n ≤ isize::MAX` bytes.

Native-code assumptions: none since the Aeneas upgrade of 2026-11-24; until then (through E11)
`rmcp.model.request_state.RequestStateCodec.rs1_fallbacks_verify_loop.body._native.decide.ax_3`. -/
@[step]
theorem open_spec (self : RequestStateCodec) (sealed : Str)
    (h_fallbacks : (components (sealed : Slice Std.U8).val).head? = some versionV1 →
      CodecFallbacksKnown self) :
    RequestStateCodec.open self sealed ⦃ (result :
        core.result.Result (alloc.vec.Vec Std.U8) RequestStateError) =>
      resultBytes result = openAt self (sealed : Slice Std.U8).val [] ExtModel.nowMs.val ⦄ := by
  unfold RequestStateCodec.open
  simp only [lift, bind_ok]
  have hU := Usize.cMax_bound_concrete.1
  have hs : (sealed : Slice Std.U8).val.length ≤ Usize.max := sealed.property
  have had : (Array.to_slice (Std.Array.empty Std.U8)).val = [] := rfl
  rw [← had]
  refine open_with_spec self sealed _ ?_ ?_ h_fallbacks
  · intro b t body hc hb
    have h1 := Proofs.RequestStateWire.length_eq_sum_map_length_components
      (sealed : Slice Std.U8).val
    rw [hc] at h1
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at h1
    have h2 := Proofs.External.Base64.four_mul_length_le_of_b64Decode b body hb
    rw [Proofs.RequestStateWire.length_transcriptV1, had, List.length_nil]
    omega
  · intro k b t kid body hc hk hb
    have h1 := Proofs.RequestStateWire.length_eq_sum_map_length_components
      (sealed : Slice Std.U8).val
    rw [hc] at h1
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at h1
    have h2 := Proofs.External.Base64.four_mul_length_le_of_b64Decode b body hb
    have h3 := Proofs.External.Base64.four_mul_length_le_of_b64Decode k kid hk
    rw [Proofs.RequestStateWire.length_transcriptV2, had, List.length_nil]
    omega

end rmcp.model.request_state.RequestStateCodec
