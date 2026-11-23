/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Rmcp.Funs
import Defs.Wire
import Defs.RequestState

/-!
# Draft statements for the `request_state` codec functions E01–E04

Plan step S05, batch E. Draft statements of the spec theorems of the codec functions
`open_authenticated_body` (E01), `b64_len` (E02), `validate_key_length` (E03) and
`validate_config_kid` (E04) of `RequestStateCodec`, against the translated functions in
`formal/translation/Rmcp/Funs.lean`. They are listed in Rust source order (E01 line 695, E03
line 704, E04 line 714, E02 line 725).

Rust source: `crates/rmcp/src/model/request_state.rs` (and `request_state_wire.rs`, which the
targets call) at local commit `14d2830`. The translation (Aeneas `nightly-2026.08.20-5d08da4`)
was generated from `14d2830` plus the working-tree Charon excludes of the seven derived `Debug`
impls (`crates/rmcp/Cargo.toml`); `formal/translation/` is untracked and not yet a pinned fork
commit (S04a not landed). Translated configuration: `x86_64-unknown-linux-gnu`,
`--no-default-features --features request-state`, `overflow-checks=true` (plan Section 1).

Status: `spec: DRAFT`, not signed off. This file is in no library and is never built; every proof
is the unproved placeholder, which is allowed only under `formal/specs/Drafts/`.

What a statement means (plan Section 3): `f x ⦃ r => P r ⦄` says that `f x` terminates without
panicking and that its result satisfies `P`.
-/

open Aeneas Aeneas.Std Result
open rmcp
open rmcp.model.request_state
open Defs.Wire (bodyExpiry Expired expiryLen b64Len minKeyLength maxKidLen)

namespace rmcp.model.request_state.RequestStateCodec

/-- **Spec theorem for `rmcp::model::request_state::RequestStateCodec::open_authenticated_body`**
(E01)

Checks the framing and the expiry of an authenticated body and returns its payload, with no
precondition (the function never panics):

* a body shorter than `expiryLen = 8` bytes gives `MalformedFormat` (W14 `TooShort`);
* otherwise, a body that is expired at `now_ms` gives `Expired` (W14 `Expired`): with
  `Defs.Wire.bodyExpiry` (the signed big-endian value of the first 8 bytes) and
  `Defs.Wire.Expired` (nonzero and strictly before `now_ms`), the same terms as the W14
  statement of `open_frame`, so that it applies without conversion;
* otherwise the result is `Ok` of the bytes after the first 8 (`payload.to_vec()`).

The three cases are exclusive and exhaustive, so the result is determined exactly. The function
performs no authentication (plan Section 3, "W14/E01 — expiry"). -/
@[step]
theorem open_authenticated_body_spec (body : alloc.vec.Vec Std.U8) (now_ms : Std.I64) :
    open_authenticated_body body now_ms ⦃ (result :
        core.result.Result (alloc.vec.Vec Std.U8) RequestStateError) =>
      match result with
      -- request_state.rs l. 698 (`Ok(payload) => Ok(payload.to_vec())`), with
      -- request_state_wire.rs l. 226 and 232 (not too short, not expired) and l. 235
      -- (`payload = &body[EXPIRY_LEN..]`, `EXPIRY_LEN = 8`, l. 17)
      | .Ok payload =>
        expiryLen ≤ body.val.length ∧
        ¬ Expired (bodyExpiry body.val) now_ms.val ∧
        payload.val = body.val.drop expiryLen
      | .Err e =>
        -- request_state.rs l. 699 (`TooShort => MalformedFormat`), with
        -- request_state_wire.rs l. 226–228 (`body.len() < EXPIRY_LEN`); checked first
        (body.val.length < expiryLen ∧ e = .MalformedFormat) ∨
        -- request_state.rs l. 700 (`Expired => Expired`), with request_state_wire.rs
        -- l. 229–234 (`is_expired(decode_expiry(head), now_ms)`); checked second
        (expiryLen ≤ body.val.length ∧ Expired (bodyExpiry body.val) now_ms.val ∧
          e = .Expired) ⦄ := by
  sorry

/-- **Spec theorem for `rmcp::model::request_state::RequestStateCodec::validate_key_length`**
(E03)

With no precondition (the function never panics): `Ok ()` iff the key has at least 32 bytes
(`minKeyLength`, `MIN_KEY_LENGTH`); otherwise `KeyTooShort { minimum: 32, actual: key.len() }`. -/
@[step]
theorem validate_key_length_spec (key : Slice Std.U8) :
    validate_key_length key ⦃ (result : core.result.Result Unit RequestStateError) =>
      match result with
      -- request_state.rs l. 705 and 711 (`key_length_ok(key.len())` holds, `Ok(())`), with
      -- request_state_wire.rs l. 39–41 (`len >= MIN_KEY_LENGTH`) and l. 19 (`= 32`)
      | .Ok _ => minKeyLength ≤ key.val.length
      -- request_state.rs l. 705–710 (`KeyTooShort { minimum: Self::MIN_KEY_LENGTH,
      -- actual: key.len() }`), with request_state.rs l. 270 (`MIN_KEY_LENGTH =
      -- wire::MIN_KEY_LENGTH`) and request_state_wire.rs l. 19 (`= 32`)
      | .Err e =>
        key.val.length < minKeyLength ∧
        ∃ minimum actual : Std.Usize, e = .KeyTooShort minimum actual ∧
          minimum.val = minKeyLength ∧ actual.val = key.val.length ⦄ := by
  sorry

/-- **Spec theorem for `rmcp::model::request_state::RequestStateCodec::validate_config_kid`**
(E04)

With no precondition (the function never panics), on the UTF-8 byte length of `kid` (the length
of the byte list that the translated `Str` is):

* `Ok ()` iff the length is in `1..=maxKidLen` (`MAX_KID_LEN = 255`);
* a length of `0` gives `InvalidKeyring` with the text of `KID_EMPTY_MSG`;
* a length above 255 gives `InvalidKeyring` with the text of `KID_TOO_LONG_MSG`.

The two message texts differ. Any bytes are accepted: there is no alphabet restriction (plan
Section 3, "W03/E04 — kid alphabet"). -/
@[step]
theorem validate_config_kid_spec (kid : Str) :
    validate_config_kid kid ⦃ (result : core.result.Result Unit RequestStateError) =>
      match result with
      -- request_state.rs l. 715–716 (`check_kid_len(kid.len())` is `Ok`), with
      -- request_state_wire.rs l. 54–62 (`len != 0`, `len <= MAX_KID_LEN`) and l. 21 (`= 255`)
      | .Ok _ =>
        1 ≤ (kid : Slice Std.U8).val.length ∧ (kid : Slice Std.U8).val.length ≤ maxKidLen
      | .Err e =>
        -- request_state.rs l. 717 (`Empty => InvalidKeyring(KID_EMPTY_MSG)`), with
        -- request_state_wire.rs l. 55–57 (`len == 0`); checked first. Message text:
        -- request_state.rs l. 86
        ((kid : Slice Std.U8).val.length = 0 ∧
          ∃ msg, e = .InvalidKeyring msg ∧ Defs.RequestState.StrIs msg
            Defs.RequestState.kidEmptyMsg) ∨
        -- request_state.rs l. 718–720 (`TooLong => InvalidKeyring(KID_TOO_LONG_MSG)`), with
        -- request_state_wire.rs l. 58–60 (`len > MAX_KID_LEN`, `MAX_KID_LEN = 255`, l. 21);
        -- checked second. Message text: request_state.rs l. 88
        (maxKidLen < (kid : Slice Std.U8).val.length ∧
          ∃ msg, e = .InvalidKeyring msg ∧ Defs.RequestState.StrIs msg
            Defs.RequestState.kidTooLongMsg) ⦄ := by
  sorry

/-- **Spec theorem for `rmcp::model::request_state::RequestStateCodec::b64_len`** (E02)

The unpadded Base64url length bound `Defs.Wire.b64Len len = 4 * ceil(len / 3)`, the same value
and the same premise as the W01 statement of `request_state_wire::b64_len` (plan Section 2.2,
"equals W01"; lead decision at S05: use the `Defs.Wire` definitions).

Domain: `h_no_overflow : b64Len len ≤ Usize.max`. This is exactly the set of inputs on which
the Rust code does not overflow: `len / 3 * 4` overflows only if `4 * (len / 3)` exceeds
`usize::MAX`, and `full + 4` (taken iff `len % 3 ≠ 0`, when `len / 3 + 1 = (len + 2) / 3`)
only if `4 * ((len + 2) / 3)` does. Overflow is failure in the Lean model, which matches debug
builds (`overflow-checks=true`, plan Sections 1 and 3); release builds would wrap. -/
@[step]
theorem b64_len_spec (len : Std.Usize)
    (h_no_overflow : b64Len len.val ≤ Usize.max) :
    b64_len len ⦃ (result : Std.Usize) =>
      -- request_state.rs l. 725–727 (`wire::b64_len(len)`), with request_state_wire.rs
      -- l. 33–36 (`full = len / 3 * 4`; `full` if `len % 3 == 0`, else `full + 4`)
      result.val = b64Len len.val ⦄ := by
  sorry

end rmcp.model.request_state.RequestStateCodec
