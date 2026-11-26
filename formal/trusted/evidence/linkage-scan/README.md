# Negative controls for the linkage text pre-check (shadow scan)

Since 2026-11-26 (human decisions after the round-5 review a5: "compare elaborated Lean" and
"refuse committed-only instances"; plan Section 19, amendment "elaborated comparison") the
`ORIGINAL` linkage is decided by step 5 of `scripts/check-original-linkage.sh`, the elaborated
comparison (negative controls in `../linkage-elab/`). The text comparison and shadow scan of
step 4, described here, stay as a fail-closed pre-check; they are not the guarantee. These cases
are the pre-check's negative controls.

`run.sh <scratch-dir>` extracts the comparison step (step 4) of `scripts/check-original-linkage.sh`
and runs it on synthetic translations. `<scratch-dir>` must be new or empty and outside the
repository.

- `cases/<id>.mine.lean` is a block of the "unmodified-source" `Funs.lean` that uses a free
  identifier; the "committed" `Funs.lean` is the same block plus `cases/<id>.extra.lean`, a
  committed-only declaration that this identifier would resolve to. The scan must reject every
  case (the run exits 1 if one is accepted, or rejected for another reason).
- `limits/<id>.{mine,extra}.lean` are forms the pre-check does not read: the identifier
  resolves through the type of a term, which a token scan cannot see. They are reported as
  accepted and do not change the exit status; step 5 covers them (a committed-only `T.a` changes
  what the unmodified block elaborates to).

## The scan (plan Section 19, amendment 2026-11-25, patch 05)

Human decisions 2026-11-25 (the scan), 2026-11-26 ("fix + one extra review round", after reviews
a3-1 and b3-1) and 2026-11-26 ("fail closed + one fresh reviewer", after reviews a4-1, b4-1 and
b4-2). The scan reads the layout Aeneas emits (line by line; it does not read code after a head line, so these are the rules of a pre-check, reviews a5-1, a5-2, a5-6; step 5 decides). It reads the four compared files of both sides
(the committed and the unmodified-source translation) and stops with `error: cannot be scanned`
(exit 1) on each of these forms:

- a block (text between blank lines) that is neither a header block nor a declaration block. A
  header block: every code line (comments and docstrings blanked) is exactly one header command:
  `module`, `import M`, `public import M`, `@[expose] public section`, `open` of plain names
  (no `in`, `renaming` or `hiding`), `set_option o v`, `namespace N`, `end` or `end N`,
  `section`, `noncomputable section`. A declaration block holds exactly one declaration head the
  scan reads, and only docstrings or comments precede it: attributes `@[…]`, then only the
  modifiers `noncomputable`, `private`, `partial`, `unsafe`, then one of the keywords `def`,
  `theorem`, `axiom`, `opaque`, `structure`, `inductive`, `class`, `instance`, `abbrev`,
  `impl_def`, then the full name (dotted segments, a segment possibly `«…»` with spaces; the
  name may stand on the next line). So a block with two declarations, a declaration with any
  other modifier or command (`protected`, `scoped`, `nonrec`, `public`, `irreducible_def`,
  `notation`, …), a command on the line of a comment or before a head (`/-- … -/ def …`,
  `open X in def …`, `set_option … in def …`, `section def …`, `open a.b.c` above `def …`) are
  refused;
- a header block of a committed file that is not a header block of the matching
  unmodified-source file (`open a.b.c`, `open X renaming a → g`, …: it would change name
  resolution);
- a declaration other than an `instance` whose name is not read;
- a `def`, `theorem`, `abbrev`, `opaque` or `impl_def` containing the token `where` or `let rec`
  (auxiliary declarations `<name>.<aux>`);
- a `structure` or `class` whose head contains `extends` (its generated parent projections are
  not read);
- a `structure`, `class` or `inductive` whose head is not ended by `where` at the end of a line,
  or with a member line at the member indent that is not `  f g : T` (fields, several names per
  line) or `  C ::` (renamed constructor) for a structure or class, or `| C : T` or `| C` (one
  constructor) for an inductive; deeper-indented lines continue the member above. So one-line
  forms (`structure S where x : Nat`, `inductive T | A | B`), fields with binders
  (`h (n : Nat) : Nat`) and a `deriving` line at the member indent are refused;
- an interpolated string: a `!` directly before a string literal (`s!"…"`, `m!"…"`, …, also
  before a raw string);
- a non-ASCII letter or digit that Lean does not read as an identifier character (below), or an
  unterminated `«`.

On what it reads:

1. One left-to-right lexer pass drops string literals (also raw strings `r#"…"#`), char
   literals, `--` line comments and nested `/- … -/` comments (docstrings included).
   Identifiers follow Lean's `isIdFirst`/`isIdRest`/`isLetterLike`/`isSubScriptAlnum`: ASCII
   letters, `_` and the letter-like ranges (Greek U+0391–U+03A9 and U+03B1–U+03C9 except `λ`,
   `Π`, `Σ`; Coptic U+03CA–U+03FB; polytonic Greek U+1F00–U+1FFE; the Letterlike Symbols block
   U+2100–U+214F; mathematical alphanumerics U+1D49C–U+1D59F) begin a segment; digits, `'`, `!`,
   `?` and the subscripts (U+2080–U+2089, U+2090–U+209C, U+1D62–U+1D6A, U+2C7C) may follow; a
   segment may also be `«…»`. Names are compared without guillemets (`«x»` and `x` are one name).
2. `EXTRA` holds the names declared only in the committed translation (any of the four files),
   and for a committed-only structure, inductive or class `T` the generated `T.mk`, `T.mk.injEq`,
   `T.mk.inj`, `T.rec`, `T.recOn`, `T.casesOn`, `T.noConfusion`, `T.noConfusionType`, `T.below`,
   `T.brecOn`, `T.ctorIdx`, `T.toCtorIdx`, and for each member read as above the projection
   `T.f` or the constructor `T.C` with `T.C.injEq` and `T.C.inj`.
3. In each unmodified-source block with a declaration, every identifier is a lookup except: the
   block's own declared name (and so a recursive call); the binding occurrence of a parameter of
   the declaration's own signature; and an identifier whose first segment is such a parameter,
   after the parameter's binder group has closed. The signature parameters are the names before
   the `:` of each binder group at bracket depth 0 after the declared name and before the
   signature's type colon at depth 0, and only when a depth-0 `:=` follows. A parameter is not
   exempted in earlier binders, in its own type or in its default value; a binder of the result
   type or of a definition by equations exempts nothing; `fun`, `let`, `match` and pattern
   binders, type ascriptions and structure-literal fields exempt nothing (checked like free
   identifiers, which is conservative).
4. A lookup `a.b.c` fails if `<ns>.a`, `<ns>.a.b` or `<ns>.a.b.c` is in `EXTRA`, for the root or
   a namespace `<ns>` enclosing the block's declaration.

Not read by the pre-check, and covered by step 5:

- names resolved through the type of a term (generalized field notation `t.a`, `(e).a`,
  `e |>.a`, the leading-dot `.a` resolved against the expected type; `limits/l1`, `limits/l2`);
- generated names beyond those of item 2 (e.g. anonymous instance names);
- the forms of review a5 (2026-11-26): code after a head line (an indented or same-line `def`,
  `local notation`, `open`; a5-1), `_root_` names and instances with unread names (a5-2),
  instance resolution (a5-3); cases e1–e6 of `../linkage-elab/`.

Outside both the pre-check and step 5 (its stated limits): the hand-written
`formal/trusted/Rmcp/*.lean` (the trusted base), and entries that committed code attaches to
existing constants in extensions that grow with new declarations (`attribute [simp]`, `[inline]`,
…; narrowed in practice by `scripts/lean-guard.sh sources`, which bans `implemented_by`; plan Section 19, amendment "elaborated comparison"). Of the other round-5 findings, a5-4 (`s! "…"` with a space was not read as an interpolated
string) is fixed in the pre-check, and a5-5 (an expected outcome per case in `run.sh`, which accepts
either "shadowing" or "cannot be scanned" for every case) is deferred.

## Cases

Reviews a2-1 and b2-1 of 2026-11-25 found these false negatives in the first version of the scan
(it stripped comments before string literals, and exempted identifiers bound by `fun`, `let` or
any `(x :` in the block):

| Case | What could hide the lookup |
|---|---|
| a1 | `(core::` inside an `@[rust_fun "…"]` string, read as a binder `(core :` |
| b0 | none (control) |
| b1 | a type ascription `ok (g : Nat)` |
| b2 | `fun g => g` in one `match` arm, a free `g` in another arm |
| b3 | `let g ← …` in one arm, a free `g` in another arm |
| b4 | `toStr "/-"` … `toStr "-/"`, which made the comment stripping delete the code between them |
| b5 | a structure literal `{ g := 1, h := g }` |
| b6 | a Pi binder `(g : Nat) → Nat` in the result type |
| b7, b7b | the H7 situation: `url.Url.host` with a later, out-of-scope `fun url => …` |

Reviews a3-1 and b3-1 of 2026-11-26 found these in the second version (which removed only
`"…"` strings, by a regular expression, before docstrings and `/- … -/` comments, kept `--`
comments, ignored char literals and guillemet or non-ASCII names, and exempted any binder
`(x :` or `{x :` beginning a line before the first `:=`); it accepted all ten. Human decision
2026-11-26: fix the scan, plus one extra review round.

| Case | What could hide the lookup |
|---|---|
| c1 | a `--` comment containing `/-`, which opened a block comment over the code below |
| c2 | the char literal `'"'`, read as the start of a string |
| c3 | the char literal `'\"'`, read as the start of a string |
| c4 | a Pi binder `(g : Nat) →` beginning a line of the result type |
| c5 | a definition by equations (no `:=`), with an ascription `(g : Nat)` beginning a line |
| c6 | a guillemet definition `«end»` used as `«end»` |
| c7 | a guillemet structure field `«meta»` (projection `S.meta`) |
| c8 | a non-ASCII name `gα` |
| c9 | a raw string `r#"a"b"#` containing a `"` |
| c10 | a `"` inside a block comment `/- say " -/` |

Reviews a4-1 (reviewer a4), b4-1 and b4-2 (reviewer b4) of 2026-11-26 found these in the third
version (the scan after the fixes of round 3, without the fail-closed rules above), which
accepted all 26. Human decision 2026-11-26: fail closed, plus one fresh reviewer. `a4-e18` (`macro …`) is not a case because `scripts/lean-guard.sh sources` bans `macro`
in Lean files; `a4-e16` and `a4-e17` exercise the same refusal (no readable head).

| Case | Reviewer | Form | Outcome |
|---|---|---|---|
| a4-d1 | a4 | `s!"{g}"`: the lookup inside an interpolated string | cannot be scanned (interpolated string) |
| a4-d2 | a4 | `(h : Fin g) (g : Nat)`: a parameter used in an earlier binder | rejected (shadowing) |
| a4-d3 | a4 | `(g : g)`: a parameter used in its own type | rejected (shadowing) |
| a4-d4 | a4 | `«g h»`: a guillemet name with a space | rejected (shadowing) |
| a4-d6 | a4 | `protected def a.b.g` | cannot be scanned (no readable head) |
| a4-d7 | a4 | `def a.b.h … where g := 1`: an auxiliary declaration `a.b.h.g` | cannot be scanned (auxiliary declaration) |
| a4-d8 | a4 | `gλ x => x`: `λ` is not an identifier character | cannot be scanned (character `λ`) |
| a4-e1 | a4 | `(g : Nat := g)`: a parameter used in its own default value | rejected (shadowing) |
| a4-e2 | a4 | `g℘`: a letter-like symbol inside a name | rejected (shadowing) |
| a4-e3 | a4 | `℘g`: a letter-like symbol beginning a name | rejected (shadowing) |
| a4-e4 | a4 | `gΠ`: `Π` is not an identifier character | cannot be scanned (character `Π`) |
| a4-e5 | a4 | `m!"{g}"`: another interpolation prefix | cannot be scanned (interpolated string) |
| a4-e6 | a4 | `scoped instance a.b.g` | cannot be scanned (no readable head) |
| a4-e7 | a4 | `nonrec def a.b.g` | cannot be scanned (no readable head) |
| a4-e8 | a4 | `public def a.b.g` | cannot be scanned (no readable head) |
| a4-e9 | a4 | `@[simp] protected def a.b.g` | cannot be scanned (no readable head) |
| a4-e16 | a4 | `irreducible_def a.b.g` | cannot be scanned (no readable head) |
| a4-e17 | a4 | `notation "g" => …` | cannot be scanned (no readable head) |
| b4-d01 | b4 | `s!"v={g}"` | cannot be scanned (interpolated string) |
| b4-d02 | b4 | `(y : Fin g) (g : Nat)`: a parameter used in an earlier binder | rejected (shadowing) |
| b4-d04 | b4 | `«g h»`: a guillemet name with a space | rejected (shadowing) |
| b4-d05 | b4 | `inductive a.b.T \| A \| B` on one line (constructor `T.B`) | cannot be scanned (`where` must end a head line) |
| b4-d06 | b4 | structure field with a binder, `h (n : Nat) : Nat` (projection `S.h`) | cannot be scanned (field line not read) |
| b4-d07 | b4 | `℘`: a one-character letter-like name | rejected (shadowing) |
| b4-d17 | b4 | `s!"{"}"}{g}"`: a string nested in an interpolation | cannot be scanned (interpolated string) |
| b4-d21 | b4 | `structure a.b.S where x : Nat` on one line (projection `S.x`) | cannot be scanned (`where` must end a head line) |

The records fix of round 4 (2026-11-26) found these in the fourth version (the fail-closed scan
before the header and `extends` rules; probes of the lead's agent while recording), which
accepted 9 of them; r4-p4 and r4-p22 were already rejected and are kept as regression controls.
Lead decision 2026-11-26, under the human decision "fail closed": strict header lines, head
first in its block, committed header blocks compared, `extends` refused.

| Case | Form | Outcome |
|---|---|---|
| r4-p1 | `/- -/ def a.b.g …` (comment and declaration on one line, read as a header) | cannot be scanned (not a header) |
| r4-p2 | `open Nat in def a.b.g …` | cannot be scanned (not a header) |
| r4-p3 | `set_option pp.all true in def a.b.g …` | cannot be scanned (not a header) |
| r4-p4 | `-- x`, `open Nat in`, `def a.b.g …` on three lines (previously rejected as shadowing) | cannot be scanned (head not first) |
| r4-p5 | `section def a.b.g …` | cannot be scanned (not a header) |
| r4-p11 | `/-- doc -/ def a.b.g …` on one line | cannot be scanned (not a header) |
| r4-p12 | committed-only `open Nat renaming succ → g` | cannot be scanned (not a header) |
| r4-p13 | committed-only header block `open a.b.c` | cannot be scanned (committed header block not in the unmodified source) |
| r4-p21 | `structure a.b.S extends T where` (parent projection `S.toT`) | cannot be scanned (`extends`) |
| r4-p22 | inductive with a `deriving Repr` line (previously refused) | cannot be scanned (constructor line not read) |
| r4-p31 | `open a.b.c` above `def a.b.k …` in one block | cannot be scanned (head not first) |

| Limit | Not read by the pre-check (covered by step 5) |
|---|---|
| l1 | field notation `t.a` on a parameter `t : T`, resolved to the committed-only `T.a` |
| l2 | the leading dot `.x` resolved against the expected type `T` to the committed-only `T.x` |

## Results

- 2026-11-25 (first fix): 10 cases (a1, b0–b7, b7b), all rejected.
- 2026-11-26 (second fix): 20 cases, all rejected; l1 and l2 accepted (then stated limitations;
  covered by step 5 since 2026-11-26).
- 2026-11-26 (fail-closed scan, before the header and `extends` rules): 46 cases, all rejected
  (29 as shadowing, 17 as "cannot be scanned"); the 11 r4-p cases were probed then, 9 accepted.
- 2026-11-26 (current scan): 57 cases (a1, a4-d1–a4-d4, a4-d6–a4-d8, a4-e1–a4-e9, a4-e16,
  a4-e17, b0–b7, b4-d01, b4-d02, b4-d04–b4-d07, b4-d17, b4-d21, b7b, c1–c10, r4-p1–r4-p5,
  r4-p11–r4-p13, r4-p21, r4-p22, r4-p31), all rejected: 29 as shadowing, 28 as "cannot be
  scanned" (the 17 above and the 11 r4-p cases); l1 and l2 accepted (not read by the pre-check);
  exit 0. `run.sh` counts "cannot be scanned" as a rejection. On the real translation
  (scratch commit `005e743`; `formal/trusted/evidence/README.md`, "Linkage of the address-policy targets") the
  comparison still passes: `Funs.lean` 65/65, `Types.lean` 42/42, templates 37/37 and 10/10,
  nothing refused; the parameter exemption is still needed (the parameters of `is_allowed` are
  `base_classes` and `class`, and `base_classes` would otherwise match the committed-only
  projection `MetadataAddressResolver.base_classes`).
- 2026-11-26 (final linkage run, scratch commit `960d6ce`, with step 5): the text comparison of
  the real translation still passes (65/65, 42/42, 37/37, 10/10) and step 5 passes (520
  constants and 41 externals identical; `formal/trusted/evidence/README.md`).
- 2026-11-26 (final linkage run after round 6, scratch commit `c400112`): 57 cases rejected; the
  real text comparison passes (65/65, 42/42, 37/37, 10/10) and step 5 passes.
- 2026-11-26 (final linkage run after round 7, scratch commit `5bb9384`): 57 cases rejected; the
  real text comparison passes (65/65, 42/42, 37/37, 10/10) and step 5 passes.
