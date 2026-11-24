/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Aeneas
import Rmcp.Types

/-!
# Definitions for the SSE event-size limiter statements (T01–T03, C01, C02)

A model of the limiter that bounds the size of one server-sent event, written from the plan
(Section 16.2, rows T01–T03; Section 17, "T01–T03 (SSE limiter)") and from the event-stream
line rules of the WHATWG HTML Standard, Section 9.2.5 "Parsing an event stream" and 9.2.6
"Interpreting an event stream":
- a line ends at CR (`0x0D`), at LF (`0x0A`) or at the pair CR LF, which is one line end;
- an empty line dispatches the event (here: the retained size returns to 0);
- a line whose first character is `:` is a comment and is ignored;
- every other line is a field line; the parser joins consecutive `data` values with one LF.

The limiter is incremental: the byte stream arrives in chunks, so a CR at the end of one chunk
and an LF at the start of the next are still one line end (the flag `previousWasCr`).

**What is counted** (plan Section 16.2, T02; the code's doc comment at `client_side_sse.rs`
line 17, "Maximum raw size of one SSE event"; its comment at line 79). The counted size of an
event is the sum, over its completed non-comment lines, of the line length plus one for the
joining newline; the current line counts with its length so far. This is not the raw byte size
of the event: a line end counts one byte whatever its form (so CR LF counts 1, not 2), and
finished comment lines and the blank line that ends the event count 0. It counts every
non-comment line, whatever its field name (`event:`, `id:`, `retry:`, unknown fields, `data:`
with its field name and colon), so it over-approximates the `data` buffer of the WHATWG parser:
a conservative choice of the code and the plan, not a WHATWG rule. The WHATWG parser also
strips one leading U+FEFF byte-order mark; the limiter counts its three bytes as part of the
first line (again conservative), and since the first byte of that line is then `0xEF`, not `:`,
a BOM in front of `:` makes the first line a non-comment line that counts (conservative too).
The bound is `retainedSize + lineSize ≤ maxSize`; an event of one line of length `n` passes
exactly when `n + 1 ≤ maxSize` (upstream test `bounded_sse_stream_passes_event_at_exact_limit`,
`client_side_sse.rs` lines 629–637).

**Saturation** (plan Section 17, "T01–T03"). The code adds with `usize::saturating_add`. Every
sum here is `satAdd cap a b = min (a + b) cap`, on `Nat`; the statements take `cap = Usize.max`,
so no overflow premise is needed and no overflow failure is possible. The cap is a parameter
because `Usize.max` is an irreducible constant of the Aeneas library that the kernel cannot
evaluate; the regression checks at the end of the file use `cap = 2^64 - 1`, its value on the
translated target `x86_64-unknown-linux-gnu`.

**Error states** (plan Section 17). The code mutates the limiter before it reports an error, so
the model returns a state together with the verdict: `Outcome.ok = false` with the state reached
at the failing byte. When a CR byte makes `finishLine` fail, `previousWasCr` stays `false`.

**Two descriptions.** `step`, `finishLine` and `observe` follow the plan-prescribed shape
(Section 16.2, T03: a left fold of `step` that stops at the first failing byte), so they mirror
the branches of the code. The section "Declarative description" is the independent part: it
splits the whole byte history into lines by the WHATWG rules, takes the lines of the current
event and adds up their sizes, without a byte-by-byte state machine; the regression checks show
that both descriptions agree on representative and on all short histories. The bound itself,
`withinLimit` (T01's test, `sat(retained_size + line_size) ≤ max_size`), is shared by both
descriptions and is not part of the independent one; the choice of `≤` (failure on `>`, not on
`≥`) is pinned by the checks of the upstream exact-limit test and of the same event one byte
over the limit. The agreement is checked on finite cases only; the general statement (for every
`cap ≥ 1`, `observe cap (init m) h = historyOutcome cap m h`) is a candidate lemma for the
proofs of plan step S31, not stated here.

Rust source: `crates/rmcp/src/transport/common/client_side_sse.rs` at upstream `7caec76`,
unmodified (plan Section 13); line numbers below refer to it (struct `SseEventSizeLimiter` lines
28–35, `new` 38–46, `observe` 48–73, `finish_line` 75–88, `check_limit` 90–96). Everything lives
in the namespace `Defs.Sse`. Not imported from the `Defs` root until sign-off.
-/

namespace Defs.Sse

open Aeneas.Std

/-- **Limiter state**, as natural numbers and flags (the five fields of `SseEventSizeLimiter`,
`client_side_sse.rs` lines 29–35, with the same names): `maxSize` the bound, `retainedSize` the
counted size of the completed lines of the current event, `lineSize` the length of the current
line so far, `lineIsComment` whether the current line is a comment (its first byte is `:`),
`previousWasCr` whether the previous byte was a CR that ended a line (so that a following LF
completes a CR LF pair). -/
structure State where
  maxSize : Nat
  retainedSize : Nat
  lineSize : Nat
  lineIsComment : Bool
  previousWasCr : Bool
  deriving DecidableEq, Repr

/-- The state of a fresh limiter with bound `maxSize`: nothing retained, no current line, no
pending CR (`SseEventSizeLimiter::new`, `client_side_sse.rs` lines 38–46). -/
def init (maxSize : Nat) : State :=
  { maxSize, retainedSize := 0, lineSize := 0, lineIsComment := false, previousWasCr := false }

/-- The model state of a translated limiter: the values of its three `usize` fields and its two
flags (`client_side_sse.rs` lines 29–35; translated `SseEventSizeLimiter`, `Rmcp/Types.lean`
lines 302–307). Injective, since a `Usize` is determined by its value. -/
def ofLimiter (s : rmcp.transport.common.client_side_sse.SseEventSizeLimiter) : State :=
  { maxSize := s.max_size.val, retainedSize := s.retained_size.val, lineSize := s.line_size.val,
    lineIsComment := s.line_is_comment, previousWasCr := s.previous_was_cr }

/-- **Saturating sum**: `a + b`, capped at `cap` (`usize::saturating_add` with
`cap = usize::MAX`, used at `client_side_sse.rs` lines 67, 82–83 and 91; plan Section 17). -/
def satAdd (cap a b : Nat) : Nat := min (a + b) cap

/-- **The size bound holds**: the saturating sum of the retained size and the current line is
at most `maxSize` (plan Section 16.2, T01: `Err ()` iff `sat(retained_size + line_size) >
max_size`; `check_limit`, `client_side_sse.rs` lines 90–96). -/
def withinLimit (cap : Nat) (st : State) : Bool :=
  decide (satAdd cap st.retainedSize st.lineSize ≤ st.maxSize)

/-- The verdict of a limiter operation and the state it leaves: `ok = true` for `Ok(())`,
`ok = false` for `Err(())`. The state is meaningful in both cases, because the code mutates
`self` before it returns an error (plan Section 16.2, T03; Section 17). -/
structure Outcome where
  ok : Bool
  state : State
  deriving DecidableEq, Repr

/-- The Rust result `Result<(), ()>` of a verdict: `Ok(())` for `true`, `Err(())` for
`false` (the return type of `observe`, `finish_line` and `check_limit`, `client_side_sse.rs`
lines 48, 75 and 90). -/
def toResult (ok : Bool) : core.result.Result Unit Unit :=
  if ok then .Ok () else .Err ()

/-- **End of a line** (plan Section 16.2, T02; WHATWG HTML 9.2.6). An empty line ends the
event, so the retained size returns to 0. A non-comment line adds its length and one byte for
the newline that joins it to the next `data` value (saturating; `client_side_sse.rs` lines
76–84). A comment line adds nothing. Then the current line is empty and not a comment (lines
85–86). The verdict is the bound on the new state (`self.check_limit()`, line 87).
`previousWasCr` and `maxSize` are unchanged. -/
def finishLine (cap : Nat) (st : State) : Outcome :=
  let retainedSize :=
    if st.lineSize = 0 then 0
    else if st.lineIsComment then st.retainedSize
    else satAdd cap (satAdd cap st.retainedSize st.lineSize) 1
  let st' := { st with retainedSize, lineSize := 0, lineIsComment := false }
  ⟨withinLimit cap st', st'⟩

/-- **One byte** (plan Section 16.2, T03; WHATWG HTML 9.2.5 line ends; `observe` body,
`client_side_sse.rs` lines 50–71).
- An LF right after a line-ending CR completes the CR LF pair: it only clears `previousWasCr`,
  and no bound is checked (lines 50–55; plan Section 17).
- Otherwise `previousWasCr` is cleared first (line 51), and then:
  - a CR ends the line (`finishLine`); if that succeeds, `previousWasCr` is set (lines 58–61);
    if it fails, the failing state keeps `previousWasCr = false` (plan Section 17);
  - an LF ends the line (line 62);
  - any other byte extends the line by one (saturating); the first byte of a line decides
    whether it is a comment (`:`, `0x3A`, WHATWG HTML 9.2.6); the verdict is the bound on the
    new state (lines 63–69). -/
def step (cap : Nat) (st : State) (b : U8) : Outcome :=
  if st.previousWasCr ∧ b.val = 10 then
    ⟨true, { st with previousWasCr := false }⟩
  else
    let st := { st with previousWasCr := false }
    if b.val = 13 then
      let o := finishLine cap st
      if o.ok then ⟨true, { o.state with previousWasCr := true }⟩ else o
    else if b.val = 10 then
      finishLine cap st
    else
      let st' := { st with
        lineIsComment := if st.lineSize = 0 then decide (b.val = 58) else st.lineIsComment,
        lineSize := satAdd cap st.lineSize 1 }
      ⟨withinLimit cap st', st'⟩

/-- **A chunk**: the left fold of `step` over the bytes, stopping at the first byte whose step
fails; an empty chunk changes nothing and succeeds (plan Section 16.2, T03; `for &byte in chunk`
with `?` on each failure and `Ok(())` at the end, `client_side_sse.rs` lines 48–73). On failure
the state is the one reached at the failing byte; the remaining bytes are not examined. -/
def observe (cap : Nat) (st : State) : List U8 → Outcome
  | [] => ⟨true, st⟩
  | b :: bs =>
    let o := step cap st b
    if o.ok then observe cap o.state bs else o

/-- **Chunk boundaries do not matter** (plan Section 16.4, C01, at the level of the model):
`observe` on `a ++ b` is `observe` on `a`, followed, if that succeeds, by `observe` on `b` from
the state it reached; if it fails, its outcome. Follows from the definition of `observe` as a
fold that stops at the first failure (`client_side_sse.rs` lines 48–73). A regression reference
for the translated statement of C01; the translated statement is proved separately. -/
theorem observe_append (cap : Nat) (st : State) (a b : List U8) :
    observe cap st (a ++ b) =
      let o := observe cap st a
      if o.ok then observe cap o.state b else o := by
  induction a generalizing st with
  | nil => simp [observe]
  | cons x xs ih =>
    simp only [List.cons_append, observe]
    split <;> simp_all

/-! ## Declarative description

The independent part of this file (see the module docstring, "Two descriptions"): the state
and the verdict of a fresh limiter after a whole byte history, read off the lines of the
history by the WHATWG line rules (HTML 9.2.5, `end-of-line = ( cr lf / cr / lf )`; 9.2.6:
an empty line dispatches the event, a line starting with `:` is a comment) and the counting
rule of plan Section 16.2, T02, without the byte-by-byte branches of `step`. -/

/-- **The lines of a byte history** (WHATWG HTML 9.2.5: a line ends at CR LF, CR or LF, the
CR LF alternative taken first): the history split at its line ends, in order. The last element
is the current, unfinished line (empty if the history ends with a line end); the others are the
completed lines. The result is never empty. -/
def splitLines : List U8 → List (List U8)
  | [] => [[]]
  | [b] => if b.val = 13 ∨ b.val = 10 then [[], []] else [[b]]
  | b :: c :: rest =>
    if b.val = 13 ∧ c.val = 10 then [] :: splitLines rest
    else if b.val = 13 ∨ b.val = 10 then [] :: splitLines (c :: rest)
    else
      match splitLines (c :: rest) with
      | l :: ls => (b :: l) :: ls
      | [] => [[b]]

/-- **A comment line**: its first byte is `:` (`0x3A`; WHATWG HTML 9.2.6). -/
def isCommentLine : List U8 → Bool
  | b :: _ => decide (b.val = 58)
  | [] => false

/-- The completed lines of the current event: the completed lines of the history after its
last empty line (an empty line dispatches the event, WHATWG HTML 9.2.6). -/
def eventLines (h : List U8) : List (List U8) :=
  (((splitLines h).dropLast.reverse).takeWhile (fun l => !l.isEmpty)).reverse

/-- The current, unfinished line of the history (the last element of `splitLines`). -/
def currentLine (h : List U8) : List U8 :=
  (splitLines h).getLast?.getD []

/-- **The state of a fresh limiter with bound `maxSize` after the history `h`**, read off the
lines (plan Section 16.2, T02, counting rule): `retainedSize` is the sum of `length + 1` over the
non-comment lines of the current event, `lineSize` the length of the current line, both capped
at `cap` (for `cap ≥ 1` a chain of saturating additions of naturals is the capped sum); the
current line is a comment if it starts with `:`; `previousWasCr` holds if the last byte is a CR
(every CR ends a line, and an LF right after it is absorbed). For `cap = 0`, a degenerate case
the statements (with `cap = Usize.max`) do not meet, the description does not match the code:
the code's `line_size` never leaves 0, so every byte of a line looks like its first byte and
decides the comment flag anew. The first disagreement is `(maxSize 0, ":a")` (a shortest one;
`"a:"` is the other), where the code ends with `lineIsComment = false` and this description
with `true` (pinned by a check below). -/
def historyState (cap maxSize : Nat) (h : List U8) : State :=
  { maxSize,
    retainedSize :=
      min (((eventLines h).filter (fun l => !isCommentLine l)).map (fun l => l.length + 1)).sum
        cap,
    lineSize := min (currentLine h).length cap,
    lineIsComment := isCommentLine (currentLine h),
    previousWasCr := decide ((h.getLast?.map (fun b => b.val)) = some 13) }

/-- **The outcome of a fresh limiter with bound `maxSize` on the history `h`**: if the bound
(T01, `withinLimit`) holds after every byte, success with `historyState` of `h`; otherwise
failure at the first byte after which it does not hold, with the state after that byte and no
pending CR (plan Section 17: on `Err` the state is the one at the failing byte, and a failing
CR leaves `previous_was_cr` false; after any other byte it is false anyway).

The code checks no bound at an LF that completes a CR LF (`client_side_sse.rs` lines 50–55;
plan Section 17). From a fresh limiter, checking the bound there too gives the same outcome:
the absorbed LF changes neither line nor size (`h.take (i + 1)` and `h.take i` have the same
lines), and the CR before it was checked and passed, or the outcome would have failed there.
So this description checks every byte, and does not test that rule. The rule is pinned by the
regression check of `observe` from a state over the bound with a pending CR. No state returned
by `step` (from any state) distinguishes the rule from "the absorbed LF checks the bound": a
state that `step` returns with `previousWasCr = true` comes from a CR whose `finishLine` passed
the bound, so it satisfies the bound, and nothing else changes before the LF; a failing `step`
returns `previousWasCr = false`. So for the absorbed LF, C02's bound premise matters only for
states that `step` did not produce, such as an arbitrary translated limiter; for the empty chunk
it matters also for a state left by a failed call, which is over the bound. -/
def historyOutcome (cap maxSize : Nat) (h : List U8) : Outcome :=
  match (List.range h.length).find?
      (fun i => !withinLimit cap (historyState cap maxSize (h.take (i + 1))))
  with
  | none => ⟨true, historyState cap maxSize h⟩
  | some i => ⟨false, { historyState cap maxSize (h.take (i + 1)) with previousWasCr := false }⟩

/-! ## Regression checks

Kernel-checked evaluations of `observe` with `cap = 2^64 - 1` (the value of `Usize.max` on
`x86_64-unknown-linux-gnu`) on the inputs of the eight upstream limiter tests of
`client_side_sse.rs` (lines 596–704; each test feeds `bounded_sse_stream`, which calls `observe`
once per chunk on a limiter built by `new`, lines 144–155) and on boundary cases of plan
Section 22 (rows T01/T02 and T03/C01/C02). `observeChunks` folds `observe` over a list of
chunks, stopping at the first failing chunk, as `BoundedSseByteStream::poll_next` does (lines
115–141: a failing `observe` sets `failed`, lines 126–127, and a `failed` stream ends at
line 120). The last checks compare
`observe` from `init` with the declarative `historyOutcome`. -/

/-- `2^64 - 1`, `Usize.max` on the translated 64-bit target (used only by the checks). -/
private def usizeMax64 : Nat := 2 ^ 64 - 1

/-- The bytes of an ASCII string literal (used only by the checks). -/
private def bytesOf (s : String) : List U8 :=
  s.toList.map (fun c => ⟨BitVec.ofNat 8 c.toNat⟩)

/-- `observe` over successive chunks, stopping at the first failing one (used only by the
checks; `poll_next`, `client_side_sse.rs` lines 115–141). -/
private def observeChunks (st : State) : List String → Outcome
  | [] => ⟨true, st⟩
  | c :: cs =>
    let o := observe usizeMax64 st (bytesOf c)
    if o.ok then observeChunks o.state cs else o

-- `bounded_sse_stream_rejects_unterminated_event_over_limit` (lines 596–610): limit 16.
example : (observeChunks (init 16) ["data: aaaaa", "aaaaaa"]).ok = false := by decide
-- `bounded_sse_stream_resets_limit_after_event_terminator` (lines 612–627): limit 8.
example : (observeChunks (init 8) ["data: a\r", "\n\r\ndata: b\n\n"]).ok = true := by decide
-- `bounded_sse_stream_passes_event_at_exact_limit` (lines 629–637): limit 9.
example : (observeChunks (init 9) ["data: ab\n\n"]).ok = true := by decide
-- The same event one byte over the limit.
example : (observeChunks (init 8) ["data: ab\n\n"]).ok = false := by decide
-- `bounded_sse_stream_rejects_oversize_split_across_many_chunks` (lines 639–655): limit 32.
example : (observeChunks (init 32) (List.replicate 20 "data: x")).ok = false := by decide
-- `bounded_sse_stream_handles_crlf_split_across_chunks` (lines 657–670): limit 64; the LF
-- that completes the split CR LF does not end a second (empty) line.
example : observeChunks (init 64) ["data: hello\r", "\n"] =
    ⟨true,
      { maxSize := 64, retainedSize := 12, lineSize := 0, lineIsComment := false,
        previousWasCr := false }⟩ := by
  decide
example : (observeChunks (init 64) ["data: hello\r", "\n\ndata: world\n\n"]).ok = true := by
  decide
-- `bounded_sse_stream_discards_completed_comment_lines_from_limit` (lines 672–680): limit 6.
example : (observeChunks (init 6) [": ping\n: ping\n: ping\n"]).ok = true := by decide
-- `bounded_sse_stream_comments_do_not_reset_accumulated_data` (lines 682–690): limit 14.
example : (observeChunks (init 14) ["data: a\n: ping\ndata: b\n"]).ok = false := by decide
-- `bounded_sse_stream_counts_multiline_data_join_newlines` (lines 692–704): limit 18.
example : (observeChunks (init 18) ["data: aaa\ndata: bbb\n\n"]).ok = false := by decide
-- A blank line resets the retained size; an empty chunk changes nothing.
example : observe usizeMax64 (init 4) (bytesOf "abc\n\n") =
    ⟨true,
      { maxSize := 4, retainedSize := 0, lineSize := 0, lineIsComment := false,
        previousWasCr := false }⟩ := by
  decide
example (st : State) : observe usizeMax64 st [] = ⟨true, st⟩ := rfl
-- CR, LF and CR LF each end one line; CR CR is two line ends (the second one empty).
example : observe usizeMax64 (init 9) (bytesOf "ab\r") =
    ⟨true,
      { maxSize := 9, retainedSize := 3, lineSize := 0, lineIsComment := false,
        previousWasCr := true }⟩ := by
  decide
example : observe usizeMax64 (init 9) (bytesOf "ab\r\r") =
    ⟨true,
      { maxSize := 9, retainedSize := 0, lineSize := 0, lineIsComment := false,
        previousWasCr := true }⟩ := by
  decide
-- An ordinary byte after a CR clears the pending CR, so a later LF ends a line of its own.
example : observe usizeMax64 (init 9) (bytesOf "a\rb\n") =
    ⟨true,
      { maxSize := 9, retainedSize := 4, lineSize := 0, lineIsComment := false,
        previousWasCr := false }⟩ := by
  decide
-- A finished comment line counts nothing and does not leave the comment flag set.
example : observe usizeMax64 (init 9) (bytesOf ":a\n") =
    ⟨true,
      { maxSize := 9, retainedSize := 0, lineSize := 0, lineIsComment := false,
        previousWasCr := false }⟩ := by
  decide
-- The LF that completes a CR LF checks no bound, even from a state over the bound. This pins
-- the rule of lines 50–55: `historyOutcome` does not test it, and no state reached by `step`
-- has a pending CR and is over the bound (see the docstring of `historyOutcome`).
example : observe usizeMax64
    { maxSize := 2, retainedSize := 5, lineSize := 0, lineIsComment := false,
      previousWasCr := true }
    [⟨10⟩] =
    ⟨true,
      { maxSize := 2, retainedSize := 5, lineSize := 0, lineIsComment := false,
        previousWasCr := false }⟩ := by
  decide
-- An error at a CR byte leaves `previousWasCr = false` and the updated sizes.
example : observe usizeMax64 (init 2) (bytesOf "ab\r") =
    ⟨false,
      { maxSize := 2, retainedSize := 3, lineSize := 0, lineIsComment := false,
        previousWasCr := false }⟩ := by
  decide
-- An error stops the fold: the bytes after the failing one are not examined.
example : observe usizeMax64 (init 1) (bytesOf "ab\n\n") =
    ⟨false,
      { maxSize := 1, retainedSize := 0, lineSize := 2, lineIsComment := false,
        previousWasCr := false }⟩ := by
  decide
-- Saturation: `satAdd` caps at `cap`, so a limiter whose bound is the cap never fails.
example : satAdd usizeMax64 usizeMax64 1 = usizeMax64 := by decide
example : withinLimit usizeMax64 ⟨usizeMax64, usizeMax64, usizeMax64, false, false⟩ = true := by
  decide

-- The declarative description agrees with `observe` from a fresh limiter: on the inputs of
-- the upstream tests (as one history) and on the boundary cases above.
example : [(16, "data: aaaaaaaaaaa"), (8, "data: a\r\n\r\ndata: b\n\n"), (9, "data: ab\n\n"),
    (8, "data: ab\n\n"), (64, "data: hello\r\n\ndata: world\n\n"), (6, ": ping\n: ping\n: ping\n"),
    (14, "data: a\n: ping\ndata: b\n"), (18, "data: aaa\ndata: bbb\n\n"), (4, "abc\n\n"),
    (9, "ab\r"), (9, "ab\r\r"), (9, "a\rb\n"), (9, ":a\n"), (2, "ab\r"), (1, "ab\n\n"),
    (3, "a\r\n:bc\r\rx"), (0, ""), (0, "\n\r\n\r")].all
    (fun (m, s) => decide (observe usizeMax64 (init m) (bytesOf s) =
      historyOutcome usizeMax64 m (bytesOf s))) = true := by
  decide

/-- All byte strings of length exactly `n` over `a`, `:`, CR and LF (used only by the
checks). -/
private def historiesOfLength : Nat → List (List U8)
  | 0 => [[]]
  | n + 1 => (historiesOfLength n).flatMap (fun h => [⟨97⟩, ⟨58⟩, ⟨13⟩, ⟨10⟩].map (· :: h))

-- ... and on every history of length at most 5 over `a`, `:`, CR and LF, for bounds 0 to 4,
-- with the cap of the target and with the small cap 2 (which exercises the saturation).
example : ((List.range 6).flatMap historiesOfLength).all (fun h => [2, usizeMax64].all
    (fun cap => (List.range 5).all (fun m =>
      decide (observe cap (init m) h = historyOutcome cap m h)))) = true := by
  decide +kernel

-- With the degenerate cap 0 the two descriptions differ, first on `(maxSize 0, ":a")`, in the
-- comment flag (see the docstring of `historyState`).
example : observe 0 (init 0) (bytesOf ":a") =
    ⟨true,
      { maxSize := 0, retainedSize := 0, lineSize := 0, lineIsComment := false,
        previousWasCr := false }⟩ ∧
    historyOutcome 0 0 (bytesOf ":a") =
    ⟨true,
      { maxSize := 0, retainedSize := 0, lineSize := 0, lineIsComment := true,
        previousWasCr := false }⟩ := by
  decide

end Defs.Sse
