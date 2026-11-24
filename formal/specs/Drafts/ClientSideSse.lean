/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Rmcp.Funs
import Defs.Sse

/-!
# Draft statements for the SSE event-size limiter (T01–T03, C01, C02)

Drafted by AI (Claude Code `mcp-spec`, model `claude-opus-5-5`) on 2026-11-24, plan step S25.
**spec: DRAFT.** Spec owner: Hoang Le Truong. None of these statements is signed off; each
needs at least two independent `mcp-review` runs and the spec owner's sign-off (plan Section 21).
The prover of a statement must not be its drafter (docs/WORKFLOW_AND_PR_GUIDE.md, "AI
contributions", rule 4).

Draft specification statements for the Phase 2 targets of
`crates/rmcp/src/transport/common/client_side_sse.rs`: T03 `SseEventSizeLimiter::observe`, T02
`SseEventSizeLimiter::finish_line`, T01 `SseEventSizeLimiter::check_limit` (in Rust source order),
and the composition theorems C01 and C02 (plan Section 16.4; former plan names
`sse_observe_append` and `sse_observe_bound`), named after their statements:
`SseEventSizeLimiter.observe_append` with its corollary
`SseEventSizeLimiter.observe_append_of_observe_eq_ok` (C01), and
`SseEventSizeLimiter.max_size_eq_and_satAdd_le_of_observe_eq_ok` with its corollary
`SseEventSizeLimiter.exists_observe_eq_ok_and_max_size_eq_and_satAdd_le_of_observe_append_eq_ok`
(C02). They are stated against the translated functions of `Rmcp.Funs` (Aeneas
`nightly-2026.08.20-5d08da4`; target `x86_64-unknown-linux-gnu`,
`--no-default-features --features <list>`, where `<list>` joins with commas the features
`request-state`, `server`, `client`, `client-side-sse`, `transport-streamable-http-server`,
`transport-streamable-http-client` and `auth`; plan Section 15) and use only `Defs.Sse` and
plain Lean. Line numbers refer to upstream `7caec76`, unmodified (the file is not touched by
patch 01). `SseEventSizeLimiter::new` (lines 38–46), `bounded_sse_stream` (line 144) and
`BoundedSseByteStream::poll_next` (lines 115–141) are not translated targets (plan Section 23:
`async`/`Pin` is outside the Aeneas scope); C01 and C02 are the contract a wrapper
argument cites.

**The model** is `Defs.Sse` (plan Section 20): the limiter state, `step` on one byte, `finishLine`,
and `observe` as a left fold of `step` that stops at the first failing byte (the plan-prescribed
shape, Section 16.2, T03), with saturating sums `Defs.Sse.satAdd`, `min (a + b) cap`; the statements
take `cap = Usize.max` (plan Section 17, "T01–T03"). Its independent part is
`Defs.Sse.historyOutcome`, which reads the state of a fresh limiter off the lines of the whole byte
history; regression checks in `Defs.Sse` show that it agrees with `Defs.Sse.observe`. Line ends
follow the WHATWG HTML Standard, 9.2.5 (CR, LF and CR LF; a CR LF split across two chunks is one
line end), and comment lines start with `:` (9.2.6). What the limiter counts (every non-comment line
plus one byte for its line end, whatever its field name) is the choice of the code and of the plan
(Section 16.2, T02), a conservative over-approximation of the WHATWG `data` buffer; see the module
docstring of `Defs.Sse`.

**What is specified.** `Defs.Sse.ofLimiter` reads a translated limiter as a model state; it is
injective, so each postcondition that gives `ofLimiter result.2` determines the returned state
uniquely, and the verdict is given by `Defs.Sse.toResult` (`Ok(())` for `true`, `Err(())` for
`false`). T02 and T03 specify both the result and the final `self`, because `self` is mutated
before an error returns (plan Section 16.2, T03; Section 17). No spec theorem has a premise:
all arithmetic saturates, so no call fails. The composition theorems take successful calls as
hypotheses (the general form of C01 has none), and C02 the bound before the call (plan Section
17: after an LF that completes a CR LF and on an empty chunk, no bound is checked).

Proof names follow plan Section 20: `<generated name>_spec`, restated later as
`Theorems.client_side_sse.SseEventSizeLimiter.<function>`. The C01 and C02 theorems follow the
Mathlib naming convention (project rule, 2026-11-24): their names describe the statement, and
the plan IDs are in the docstrings.

This file is a draft: it lives in `formal/specs/Drafts/`, belongs to no library and is never
built by `lake build`. Each proof is a placeholder, allowed only here. A statement
`f x ⦃ (result : T) => P result ⦄` says that `f x` terminates without panicking and that its
result satisfies `P` (plan Section 3, "What a spec means").
-/

open Aeneas Aeneas.Std Result

namespace rmcp.transport.common.client_side_sse.SseEventSizeLimiter

/-! ## T03, T02, T01 (`client_side_sse.rs` lines 48–96), in Rust source order -/

/-- **Spec theorem for
`rmcp::transport::common::client_side_sse::SseEventSizeLimiter::observe`** (T03)

The call never fails. Its result and its final `self` are those of `Defs.Sse.observe`: the left
fold of `Defs.Sse.step` over the bytes of `chunk`, from the state of `self`, stopping at the
first byte whose step fails (plan Section 16.2, T03; `client_side_sse.rs` lines 48–73,
`for &byte in chunk` with `?` on `finish_line` and `check_limit`). So CR, LF and CR LF each end
one line; a CR at the end of one call and an LF at the start of the next are one line end
(`previous_was_cr`, lines 50–55); a line whose first byte is `:` is a comment (line 65); an
empty chunk returns `Ok(())` with `self` unchanged; on `Err(())`, `self` is the state reached
at the failing byte, with the bytes after it unread, and when a CR byte fails,
`previous_was_cr` is `false` (plan Section 17). `max_size` never changes. No premise. -/
@[step]
theorem observe_spec (self : SseEventSizeLimiter) (chunk : Slice U8) :
    observe self chunk ⦃ (result : core.result.Result Unit Unit × SseEventSizeLimiter) =>
      Defs.Sse.ofLimiter result.2 =
        (Defs.Sse.observe Usize.max (Defs.Sse.ofLimiter self) chunk.val).state ∧
      result.1 = Defs.Sse.toResult
        (Defs.Sse.observe Usize.max (Defs.Sse.ofLimiter self) chunk.val).ok ⦄ := by
  sorry

/-- **Spec theorem for
`rmcp::transport::common::client_side_sse::SseEventSizeLimiter::finish_line`** (T02)

The call never fails. The new `self` is `Defs.Sse.finishLine` of the old one: an empty line
(`line_size = 0`) resets `retained_size` to 0; a non-comment line adds `line_size + 1` to it,
saturating at `usize::MAX` (the `+ 1` is the newline that joins `data` values; a line end
counts one byte whatever its form, so this is not the raw byte size); a comment line
leaves it unchanged; then `line_size := 0` and `line_is_comment := false`; `max_size` and
`previous_was_cr` are unchanged (plan Section 16.2, T02; `client_side_sse.rs` lines 75–86). The
result is T01 on the new state: `Err(())` exactly when the saturating sum of the new
`retained_size` and `line_size` (which is 0) exceeds `max_size` (line 87). No premise. -/
@[step]
theorem finish_line_spec (self : SseEventSizeLimiter) :
    finish_line self ⦃ (result : core.result.Result Unit Unit × SseEventSizeLimiter) =>
      Defs.Sse.ofLimiter result.2 =
        (Defs.Sse.finishLine Usize.max (Defs.Sse.ofLimiter self)).state ∧
      result.1 =
        Defs.Sse.toResult (Defs.Sse.withinLimit Usize.max (Defs.Sse.ofLimiter result.2)) ⦄ := by
  sorry

/-- **Spec theorem for
`rmcp::transport::common::client_side_sse::SseEventSizeLimiter::check_limit`** (T01)

The call never fails. `Err(())` exactly when `sat(retained_size + line_size) > max_size`, with
`sat` the sum saturating at `usize::MAX`; `Ok(())` otherwise, so a sum exactly at `max_size`
passes (plan Section 16.2, T01; Section 22; `client_side_sse.rs` lines 90–96). Stated as
`Defs.Sse.toResult` of `Defs.Sse.withinLimit` (`decide (satAdd Usize.max retained_size
line_size ≤ max_size)`) on the state of `self`, the form in which T02 and T03 use the verdict.
It takes `&self`, so it returns no state. No premise. -/
@[step]
theorem check_limit_spec (self : SseEventSizeLimiter) :
    check_limit self ⦃ (result : core.result.Result Unit Unit) =>
      result = Defs.Sse.toResult (Defs.Sse.withinLimit Usize.max (Defs.Sse.ofLimiter self)) ⦄ := by
  sorry

end rmcp.transport.common.client_side_sse.SseEventSizeLimiter

namespace rmcp.transport.common.client_side_sse.SseEventSizeLimiter

/-! ## Composition theorems C01, C02 (plan Section 16.4) -/

/-- **C01** (former plan name `sse_observe_append`), general form: chunk boundaries do not change
the limiter. `observe` on the concatenation `ab = a ++ b` from `self` is `observe` on `a` from
`self`, followed, if that returns `Ok(())` with state `s`, by `observe` on `b` from `s`; if it
returns `Err(())` with state `s`, the call on `ab` returns `Err(())` with the same state `s`
(the bytes of `b` are not read). Result and state, including when a CR LF is split between `a`
and `b` (plan Section 16.4, C01; uses T03; `client_side_sse.rs` lines 48–73: `for &byte in
chunk` with `?`). The model-level fact is `Defs.Sse.observe_append`. About the translated
function `SseEventSizeLimiter::observe`. No call is assumed to succeed. The premise `h_ab`
names the concatenation as a slice, since `Slice U8` is bounded by `Usize.max`. Not tagged
`@[step]`. -/
theorem observe_append (self : SseEventSizeLimiter) (a b ab : Slice U8)
    (h_ab : ab.val = a.val ++ b.val) :
    observe self ab = (do
      let (r, s) ← observe self a
      match r with
      | .Ok () => observe s b
      | .Err () => ok (.Err (), s)) := by
  sorry

/-- **C01** (former plan name `sse_observe_append`), in the plan's form: if `observe` on `a` from
`self` returns `Ok(())` with state `self'`, then `observe` on the concatenation `ab = a ++ b`
from `self` returns exactly what `observe` on `b` from `self'` returns, result and state (plan
Section 16.4, C01; uses T03; `client_side_sse.rs` lines 48–73). A corollary of
`observe_append`. About the translated function `SseEventSizeLimiter::observe`. It takes a
successful call on `a` as its hypothesis and covers only that case; it does not show that any
call succeeds (T03 shows that every call returns). Not tagged `@[step]`. -/
theorem observe_append_of_observe_eq_ok (self self' : SseEventSizeLimiter) (a b ab : Slice U8)
    (h_ab : ab.val = a.val ++ b.val)
    (h_a : observe self a = ok (.Ok (), self')) :
    observe self ab = observe self' b := by
  sorry

/-- **C02** (former plan name `sse_observe_bound`): the limiter's memory guarantee at each chunk
boundary. If the bound `sat(retained_size + line_size) ≤ max_size` (saturating at
`usize::MAX`) holds for `self` and `observe` on `chunk` returns `Ok(())` with state `self'`,
then it holds for `self'`, and `max_size` is unchanged; so at the end of every accepted chunk
the limiter retains at most `max_size` counted bytes of the current event (plan Section 16.4,
C02; uses T01–T03; `client_side_sse.rs` lines 48–96). The theorem says nothing about the
states inside the chunk; the corollary below covers every prefix of an accepted chunk. The
premise `h_bound` is needed: an empty chunk and an LF that completes a CR LF check nothing
(plan Section 17), so without it a state over the bound would be accepted with its sizes
unchanged (an absorbed LF still clears `previous_was_cr`, lines 50–55). It matters only when
`chunk` is `[]`, or is a single LF and `self` has a pending CR: every other accepted chunk ends
with a checked byte that passed, or with an absorbed LF whose CR came earlier in the same chunk
and passed its check, with no size change in between. A fresh
limiter (`new`, lines 38–46: both sizes 0) satisfies it. About the translated function
`SseEventSizeLimiter::observe`. It takes a successful call as its hypothesis and covers only
that case; it does not show that any call succeeds. Not tagged `@[step]`. -/
theorem max_size_eq_and_satAdd_le_of_observe_eq_ok (self self' : SseEventSizeLimiter)
    (chunk : Slice U8)
    (h_bound :
      Defs.Sse.satAdd Usize.max self.retained_size.val self.line_size.val ≤ self.max_size.val)
    (h_ok : observe self chunk = ok (.Ok (), self')) :
    self'.max_size = self.max_size ∧
    Defs.Sse.satAdd Usize.max self'.retained_size.val self'.line_size.val ≤
      self'.max_size.val := by
  sorry

/-- **C02, prefix form** (plan Section 16.4, C02 and C01): if the bound holds for `self` and
`observe` on `ab = a ++ b` returns `Ok(())`, then `observe` on the prefix `a` also returns
`Ok(())`, with a state `self'` that keeps `max_size` and satisfies the bound. So every prefix of
an accepted chunk is accepted and leaves the bound holding; the chunk can be cut anywhere.
Follows from `observe_append` and `max_size_eq_and_satAdd_le_of_observe_eq_ok`
(`client_side_sse.rs` lines 48–96). About the translated function
`SseEventSizeLimiter::observe`. It takes a successful call on `ab` as its hypothesis and
covers only that case. Not tagged `@[step]`. -/
theorem exists_observe_eq_ok_and_max_size_eq_and_satAdd_le_of_observe_append_eq_ok
    (self self'' : SseEventSizeLimiter) (a b ab : Slice U8)
    (h_ab : ab.val = a.val ++ b.val)
    (h_bound :
      Defs.Sse.satAdd Usize.max self.retained_size.val self.line_size.val ≤ self.max_size.val)
    (h_ok : observe self ab = ok (.Ok (), self'')) :
    ∃ self', observe self a = ok (.Ok (), self') ∧ self'.max_size = self.max_size ∧
      Defs.Sse.satAdd Usize.max self'.retained_size.val self'.line_size.val ≤
        self'.max_size.val := by
  sorry

end rmcp.transport.common.client_side_sse.SseEventSizeLimiter
