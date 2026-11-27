/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Aeneas
public import Rmcp.FunsExternal
public import Defs.Bytes

@[expose] public section

/-!
# Definitions for the SEP-2243 header-value encoding statements (G01–G04)

**Signed off by the human spec owner on 2026-11-28** with the statements that use these
definitions (proved in `Proofs.Transport.McpHeaders`, restated in
`Proofs.Internal.Transport.Common.McpHeaders`). The vocabulary of the statements about the private
functions of `crates/rmcp/src/transport/common/mcp_headers.rs` that translation patch 07 makes
translatable (human decisions GD1–GD3, `formal/README.md`):

- G02 `is_tchar`: `isTchar` (the RFC 9110 §5.6.2 `tchar` grammar), with `isVchar`,
  `isDelimiter` (the RFC's prose reading "any VCHAR, except delimiters") and the list `tchars`;
- G01 `requires_base64`: `isSpaceOrTab`, `isPrintableAscii`, `base64Prefix`, `base64Suffix`,
  `requiresBase64`;
- G03 `encode_header_value`: `wrapSentinel`, `encodeHeaderValue`;
- G04 `decode_header_value`: `sentinelInner?`, `decodeHeaderValue`;
- the size premises `EncodeFits` (G03) and `DecodeFits` (G04);
- header safety (RFC 9110 §5.5): `IsFieldValue`, `IsBareHeaderValue`, `IsVisibleAscii`.

The targets are private (`fn` without `pub`), so these definitions live in `Proofs/Defs/` (human
decision 2026-11-24); module `Proofs.Defs.McpHeaders`, Lean namespace `Defs.McpHeaders`.

**Values are bytes.** A Rust `&str` or `String` is described by its UTF-8 bytes
(`Defs.utf8Bytes`); the functions below take and return `List U8`. They are defined on every
byte list, as the byte-level external models of patch 07 are
(`formal/trusted/Rmcp/FunsExternal.lean`, section "`mcp_headers.rs` header-value encoding");
the statements add the UTF-8 premise (`ExtModel.IsUtf8`) only where the Rust code would
otherwise reach a model's `fail undef`.

**Base64.** Standard padded Base64 (RFC 4648 §4, `base64-0.23.1` `BASE64_STANDARD`) is the
trusted model `ExtModel.b64StdPad`, its strict decoder `ExtModel.b64StdPadDecode`; their laws
(round trip, the decoder accepts exactly the padded encodings, every encoded byte is in
`0x21`–`0x7E`) are theorems of `Proofs.External.Base64Std`. Nothing else is assumed about them.

**Line citations.** "upstream" is `mcp_headers.rs` (or `http_header.rs`) at `7caec76`
(unmodified in the repository); "patched" is the copy with translation patches 01–07 (blob
`a8f6185`), from which the translation is made (the `Source:` lines of `Rmcp.Funs`: G01 62–76,
G02 80–98, G03 240–246, G04 250–261). `http_header.rs` is not patched (lines 13–14 in both).
Other rmcp files are cited the same way: `model.rs` as "upstream lines … (patched …)", since
the patches shift its lines; the cited `tower.rs` lines are the same in both copies (patch 02
only appends tests after line 2613), so they are given once.

**External references** (for the docstrings; the definitions describe the code):
- RFC 9110 §5.5 (field values: `field-value = *field-content`, `field-content = field-vchar
  [ 1*( SP / HTAB / field-vchar ) field-vchar ]`, `field-vchar = VCHAR / obs-text`, `obs-text =
  %x80-FF`) and §5.6.2 (tokens: `` tchar = "!" / "#" / "$" / "%" / "&" / "'" / "*" / "+" / "-" /
  "." / "^" / "_" / "`" / "|" / "~" / DIGIT / ALPHA ``, "any VCHAR, except delimiters";
  delimiters are `DQUOTE` and the 16 characters `(`, `)`, `,`, `/`, `:`, `;`, `<`, `=`, `>`,
  `?`, `@`, `[`, `\`, `]`, `{`, `}`); RFC 5234 Appendix B.1 (`VCHAR = %x21-7E`,
  `SP = %x20`, `HTAB = %x09`, `DIGIT`, `ALPHA`).
- SEP-2243 (MCP standard HTTP headers), as the rmcp comments describe it (module docstring,
  upstream lines 1–6; `requires_base64` doc, lines 58–60; `http_header.rs` line 12): a value
  that cannot travel as a bare header value (leading/trailing space or tab, control or non-ASCII
  characters, or a value that already looks like the sentinel) is sent as
  `=?base64?<standard Base64 of its UTF-8 bytes>?=`.
-/

namespace Defs.McpHeaders

open Aeneas.Std

/-! ## Tokens (G02) -/

/-- **A visible ASCII character** (RFC 5234 Appendix B.1, `VCHAR = %x21-7E`). -/
def isVchar (c : Char) : Bool := decide (0x21 ≤ c.toNat ∧ c.toNat ≤ 0x7E)

/-- **An RFC 9110 delimiter** (§5.6.2: delimiters are "the set of US-ASCII visual characters
not allowed in a token", namely `DQUOTE` and the 16 characters listed in the module docstring):
17 characters, written below in the order `"`, `(`, `)`, `,`, `/`, `:`, `;`, `<`, `=`, `>`, `?`,
`[`, `\`, `]`, `{`, `}`, `@`. -/
def isDelimiter (c : Char) : Bool := decide (c ∈ "\"(),/:;<=>?[\\]{}@".toList)

/-- **An RFC 9110 token character** (§5.6.2, the ABNF rule `tchar`): one of the fifteen
characters `` !#$%&'*+-.^_`|~ ``, an ASCII digit (`DIGIT = %x30-39`) or an ASCII letter
(`ALPHA = %x41-5A / %x61-7A`). Lean's `Char.isDigit` and `Char.isAlpha` test exactly these ASCII
ranges. The Rust function G02 (upstream lines 81–100, patched 80–98) documents itself as
"RFC 9110 §5.6.2 token character" (doc comment: upstream line 79, patched 78); it tests
`char::is_ascii_alphanumeric` (the same ASCII ranges) or one of the same fifteen characters. -/
def isTchar (c : Char) : Bool :=
  c.isDigit || c.isAlpha || decide (c ∈ "!#$%&'*+-.^_`|~".toList)

/-- **The 77 token characters** in ASCII order of their classes: the fifteen punctuation
characters of `tchar`, the ten digits, the 26 upper-case and the 26 lower-case letters. Used by
the characterisation laws (`isTchar c = true ↔ c ∈ tchars`, `tchars.length = 77`). -/
def tchars : List Char :=
  "!#$%&'*+-.^_`|~0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz".toList

/-! ## Header-value bytes (G01) -/

/-- **`SP` or `HTAB`** (RFC 5234 Appendix B.1: `SP = %x20`, `HTAB = %x09`): the bytes `b' '`
and `b'\t'` that G01 tests at both ends of the value (upstream line 67, patched 67–68). -/
def isSpaceOrTab (b : U8) : Bool := decide (b.val = 0x20 ∨ b.val = 0x09)

/-- **A printable ASCII byte**, `0x20`–`0x7E` (`SP` or `VCHAR`). G01 wraps a value with any
other byte: upstream lines 70–75 test `value.chars().any(|c| (c as u32) < 0x20 ||
(c as u32) > 0x7E)` on chars; on the UTF-8 bytes of a string, some byte is outside
`0x20`–`0x7E` exactly when some char is
(`Proofs.External.Base64Std.any_isControlOrNonAsciiByte_utf8`; a char above `U+007E` is
`U+007F`, one byte, or non-ASCII, all of whose bytes are at least `0x80`). -/
def isPrintableAscii (b : U8) : Bool := decide (0x20 ≤ b.val ∧ b.val ≤ 0x7E)

/-- **The sentinel prefix** `=?base64?` (9 bytes; `BASE64_HEADER_PREFIX`, `http_header.rs`
line 13). -/
def base64Prefix : List U8 := Defs.utf8Bytes "=?base64?"

/-- **The sentinel suffix** `?=` (2 bytes; `BASE64_HEADER_SUFFIX`, `http_header.rs` line 14). -/
def base64Suffix : List U8 := Defs.utf8Bytes "?="

/-- **The value must be Base64-wrapped** (G01 `requires_base64`, upstream lines 62–77, patched
62–76), in the Rust order of the checks:
1. the empty value is not wrapped (lines 63–65); it has no first or last byte, no byte at all,
   and the 9-byte prefix is not a prefix of it, so each disjunct below is `false` for it;
2. the first or the last byte is `SP` or `HTAB` (lines 66–69, patched 66–71);
3. some byte is outside `0x20`–`0x7E` (lines 70–75, patched 72–74; `isPrintableAscii`);
4. the value starts with `=?base64?` and ends with `?=` (line 76, patched 75; `str::starts_with`
   and `str::ends_with` compare bytes). The two may overlap: `=?base64?=` (10 bytes) satisfies
   this test, although it is too short to be a sentinel for G04 (`sentinelInner?`); it is the
   only such value (law `prefix_and_suffix_and_sentinelInner?_eq_none_iff`).

The checks have no side effect, so their order does not change the value.

Intended behaviour (spec owner, 2026-11-27, CD3/CD4): this is the SEP-2243 sender rule as the
rmcp doc states it (upstream lines 58–60): wrap a value with leading or trailing SP/HTAB, a
non-ASCII char, a control char (`0x00`–`0x1F`, `0x7F`), or a plain value matching the sentinel
pattern; the markers are lowercase and compared case-sensitively. The rule is stricter than
RFC 9110 §5.5, which allows an interior HTAB and `obs-text` in a field value. `,` and `"` are
not wrapped (`requiresBase64 (utf8Bytes "a, b") = false`; CD7, low-severity upstream candidate
"H18"): under RFC 9110 §5.3 a recipient or proxy may combine duplicate field lines into one value
joined by `, `, and a merged duplicate pair cannot be told apart from a single bare value that
contains `, `; `header_str` rejects a duplicated field (upstream lines 394–413) but cannot see
one an intermediary already merged. The empty value is not wrapped; SEP-2243 does not say how
to send it (CD6). -/
def requiresBase64 (s : List U8) : Bool :=
  s.head?.any isSpaceOrTab || s.getLast?.any isSpaceOrTab ||
    s.any (fun b => !isPrintableAscii b) ||
    (decide (base64Prefix <+: s) && decide (base64Suffix <:+ s))

/-! ## Encoding and decoding (G03, G04) -/

/-- **The sentinel around a Base64 text**: `=?base64?` ++ `inner` ++ `?=` (the `format!` of
upstream lines 245–248, `"{BASE64_HEADER_PREFIX}{}{BASE64_HEADER_SUFFIX}"`; patched line 242,
`prim::wrap_sentinel`). -/
def wrapSentinel (inner : List U8) : List U8 := base64Prefix ++ inner ++ base64Suffix

/-- **The header value sent for `s`** (G03 `encode_header_value`, upstream lines 242–252, patched
240–246): if `requiresBase64 s`, the sentinel around the padded standard Base64 encoding of the
bytes of `s` (`BASE64_STANDARD.encode(value)`, line 247; `ExtModel.b64StdPad`); otherwise `s`
unchanged (`value.to_owned()`, line 250). -/
def encodeHeaderValue (s : List U8) : List U8 :=
  if requiresBase64 s then wrapSentinel (ExtModel.b64StdPad s) else s

/-- **The Base64 text inside a sentinel**, as G04 finds it (upstream lines 258–261, patched
251–253): `some inner` if the value starts with `=?base64?` and what follows ends with `?=`
(`strip_prefix`, then `strip_suffix` on the rest; byte comparisons), `inner` being the bytes
between the two; `none` otherwise. So a sentinel has at least 11 bytes, and prefix and suffix do
not overlap (law `sentinelInner?_eq_some_iff`: `s = wrapSentinel inner`). The markers are
compared case-sensitively (CD4, intended). -/
def sentinelInner? (s : List U8) : Option (List U8) :=
  if base64Prefix <+: s ∧ base64Suffix <:+ s.drop base64Prefix.length then
    some ((s.drop base64Prefix.length).take
      ((s.drop base64Prefix.length).length - base64Suffix.length))
  else none

/-- **The value G04 recovers from a header value `s`** (G04 `decode_header_value`, upstream lines
256–268, patched 250–261), as bytes:
- not a sentinel (`sentinelInner? s = none`): `some s`, the value unchanged
  (`Some(value.to_owned())`, line 266, patched 257 and 259);
- a sentinel around `inner`: `some y` if `inner` decodes as strict padded standard Base64 to `y`
  (`BASE64_STANDARD.decode(inner).ok()?`, line 263; `ExtModel.b64StdPadDecode`, which is `some y`
  exactly when `ExtModel.b64StdPad y = inner`) and `y` is UTF-8 (`String::from_utf8(bytes).ok()`,
  line 264; `ExtModel.strOfBytes?`, Rust's `str::from_utf8`); `none` otherwise.

Not injective (CD1, CD2; low-severity upstream candidate "H17"), so an intermediary that
filters on the raw header value can be bypassed:
- CD1: the sentinel around the Base64 of a value that G03 sends bare decodes to that value, as
  the bare value does (`=?base64?dXMtd2VzdDE=?=` and `us-west1` both give `us-west1`);
- CD2: a non-sentinel value that G03 would wrap is returned unchanged, as its G03 encoding
  decodes to it (`a⇥b` and `=?base64?YQli?=` both give `a⇥b`, an interior HTAB passing
  `HeaderValue::to_str`, `http-1.5.0/src/header/value.rs` lines 243–256, which applies
  `is_visible_ascii` (lines 558–560) to every byte at line 249; `=?base64?=` and
  `=?base64?PT9iYXNlNjQ/PQ==?=` both give `=?base64?=`).
Making G04 the exact inverse of G03 needs both: reject a sentinel whose decoded value `y` has
`requiresBase64 y = false` (CD1), and reject a non-sentinel value `s` with
`requiresBase64 s = true` (CD2); and the two together suffice: for a UTF-8 header value `s`, the
fixed decoder gives `Some(y)` exactly when `s = encode_header_value(y)`, for UTF-8 `y` (a Rust
`String`). This follows from `decodeHeaderValue_eq_some_iff`,
`sentinelInner?_eq_some_iff`,
`sentinelInner?_eq_none_of_requiresBase64_eq_false` and the two G03 forms
`encodeHeaderValue_eq_wrapSentinel_of_requiresBase64_eq_true` and
`encodeHeaderValue_eq_self_of_requiresBase64_eq_false` (laws restated in
`Proofs.Internal.Transport.Common.McpHeaders`); a Rust probe on the patched copy agreed on all
strings of up to 6 characters over SP, HTAB, `a`, `=`, `?`, `é`, DEL and LF, on their encodings
and on their unneeded Base64 wraps; each rejection alone leaves CD1 or CD2 witnesses.
`requires_base64` is compiled only with feature `client-side-sse` (upstream line 61) and
`decode_header_value` with `server-side-http` (line 255), so such a fix would also have to compile
`requires_base64` for the server.
SEP-2243 does not say whether a receiver must accept an unneeded wrap, which Base64 alphabet and
padding apply, or what to do with a non-UTF-8 payload; the code requires the standard alphabet
with canonical padding (CD4) and UTF-8 (CD5). For `none`, the caller `validate_request_headers`
returns `Err("… is not valid Base64")` (upstream lines 347–348, 380–381; its doc, lines 320–321,
says the caller maps this to `-32020`, HTTP 400). Its caller `validate_standard_headers`
(`transport/streamable_http_server/tower.rs`, upstream lines 1055–1056) returns
`header_mismatch_jsonrpc_response(request_id, reason)` (`tower.rs` lines 968–979): the error is
built at line 972 with `ErrorData::header_mismatch` (upstream `model.rs` lines 688–690, patched
690–692), whose code is `ErrorCode::HEADER_MISMATCH` = `-32020` (upstream `model.rs` line 639,
patched 641), and the response status HTTP 400 is set at `tower.rs` line 975 (`tower.rs` lines
are the same in both copies). -/
def decodeHeaderValue (s : List U8) : Option (List U8) :=
  match sentinelInner? s with
  | none => some s
  | some inner =>
    (ExtModel.b64StdPadDecode inner).filter (fun y => (ExtModel.strOfBytes? y).isSome)

/-! ## Size premises -/

/-- **The wrapped value fits in a `String`** (premise of G03): if the value is wrapped, its padded
Base64 encoding (`4 ⌈n / 3⌉` bytes for `n` bytes, `Proofs.External.Base64Std.length_b64StdPad`)
plus the 11 sentinel bytes is at most `isize::MAX` bytes. Exact: otherwise Rust panics, in
`BASE64_STANDARD.encode` (`vec![0; encoded_size]`, "capacity overflow") or in the `format!` of the
sentinel (`String` growth), and so does the model (`encode_header_value_fail`). A Rust `&str` of
at most `isize::MAX / 2` bytes meets it
(`Proofs.External.Base64Std.add_two_div_three_mul_four_add_eleven_le`); one of more than about
`3/4 · isize::MAX` bytes that must be wrapped does not, and Rust panics. -/
def EncodeFits (s : List U8) : Prop :=
  requiresBase64 s = true → (s.length + 2) / 3 * 4 + 11 ≤ ExtModel.maxStringBytes

/-- **The decode buffer fits** (premise of G04): for a sentinel around `inner`, the buffer that
`BASE64_STANDARD.decode` allocates before reading (`ExtModel.b64StdDecodedLenEstimate`,
`3 ⌈n / 4⌉` bytes; `base64-0.23.1/src/engine/mod.rs` line 283) is at most `isize::MAX` bytes.
Exact: otherwise the model panics (`decode_header_value_fail`), as `vec!` would. Every Rust `&str`
meets it, having at most `isize::MAX` bytes
(`Proofs.External.Base64Std.b64StdDecodedLenEstimate_le_of_le`). -/
def DecodeFits (s : List U8) : Prop :=
  ∀ inner, sentinelInner? s = some inner →
    ExtModel.b64StdDecodedLenEstimate inner.length ≤ ExtModel.maxStringBytes

/-! ## Header safety (RFC 9110 §5.5) -/

/-- **An RFC 9110 field value** (§5.5: `field-value = *field-content`, `field-content =
field-vchar [ 1*( SP / HTAB / field-vchar ) field-vchar ]`, `field-vchar = VCHAR / obs-text`,
`obs-text = %x80-FF`): every byte is `VCHAR`, `obs-text`, `SP` or `HTAB`, and the value neither
starts nor ends with `SP` or `HTAB` (a concatenation of `field-content`s starts and ends with a
`field-vchar`). In particular it has no `CR`, `LF` or `NUL`. -/
def IsFieldValue (s : List U8) : Prop :=
  (∀ b ∈ s, (0x21 ≤ b.val ∧ b.val ≤ 0x7E) ∨ 0x80 ≤ b.val ∨ isSpaceOrTab b = true) ∧
    s.head?.all (fun b => !isSpaceOrTab b) = true ∧
    s.getLast?.all (fun b => !isSpaceOrTab b) = true

/-- **A value that may travel bare**, the stricter form of `IsFieldValue` that G03 produces:
every byte is printable ASCII (`0x20`–`0x7E`: `SP` or `VCHAR`; no `HTAB`, no `obs-text`, no
control byte), and the value neither starts nor ends with `SP` or `HTAB`. Every byte is also
accepted by `http::HeaderValue::from_str` (`http-1.5.0/src/header/value.rs` lines 563–565:
`b >= 32 && b != 127 || b == b'\t'`), which the caller `standard_request_headers` applies
(upstream lines 287–294), so an encoded value is never rejected by `HeaderValue::from_str`. -/
def IsBareHeaderValue (s : List U8) : Prop :=
  (∀ b ∈ s, isPrintableAscii b = true) ∧
    s.head?.all (fun b => !isSpaceOrTab b) = true ∧
    s.getLast?.all (fun b => !isSpaceOrTab b) = true

/-- **Visible ASCII only** (`VCHAR`, `0x21`–`0x7E`: no `SP`, no `HTAB`, no control byte, no
`obs-text`): the form of a Base64-wrapped value. -/
def IsVisibleAscii (s : List U8) : Prop := ∀ b ∈ s, 0x21 ≤ b.val ∧ b.val ≤ 0x7E

/-! ## Kernel-checked examples

The values agree with the scratch Rust probe on the patched copy (2026-11-27,
`cargo test --lib --no-default-features --features request-state,server,client,client-side-sse,
transport-streamable-http-server,transport-streamable-http-client,auth,macros`):
`encode_header_value` and `decode_header_value` on the same inputs. -/

-- G02: the 77 token characters; `"`, `(`, `,`, `/`, `:`, `@`, `{`, SP, DEL and `é` are not.
example : tchars.all isTchar = true ∧ tchars.length = 77 ∧
    ['"', '(', ',', '/', ':', '@', '{', ' ', '\x7f', 'é'].all (fun c => !isTchar c) = true := by
  decide +kernel

-- G01: plain ASCII with inner spaces is bare; a leading or trailing SP or HTAB, an inner HTAB,
-- DEL, a non-ASCII char and the sentinel shape (also overlapping, `=?base64?=`) are wrapped;
-- `=?base64?` alone (no `?=` at the end) and the empty value are bare.
example :
    [requiresBase64 (utf8Bytes "us-west1"), requiresBase64 (utf8Bytes "a  b"),
     requiresBase64 [], requiresBase64 (utf8Bytes "=?base64?"),
     requiresBase64 (utf8Bytes " a"), requiresBase64 (utf8Bytes "a\t"),
     requiresBase64 (utf8Bytes "a\tb"), requiresBase64 (utf8Bytes "\x7f"),
     requiresBase64 (utf8Bytes "é"), requiresBase64 (utf8Bytes "=?base64?x?="),
     requiresBase64 (utf8Bytes "=?base64?=")] =
    [false, false, false, false, true, true, true, true, true, true, true] := by
  decide +kernel

-- G03: bare values unchanged; `" "` (one SP) ↦ `=?base64?IA==?=`, `é` ↦ `=?base64?w6k=?=`,
-- `a⇥b` ↦ `=?base64?YQli?=`, `a\r\nEvil: 1` ↦ `=?base64?YQ0KRXZpbDogMQ==?=`,
-- `=?base64?=` ↦ `=?base64?PT9iYXNlNjQ/PQ==?=` (Rust probe values).
example :
    encodeHeaderValue (utf8Bytes "us-west1") = utf8Bytes "us-west1" ∧
    encodeHeaderValue [] = [] ∧
    encodeHeaderValue (utf8Bytes " ") = utf8Bytes "=?base64?IA==?=" ∧
    encodeHeaderValue (utf8Bytes "é") = utf8Bytes "=?base64?w6k=?=" ∧
    encodeHeaderValue (utf8Bytes "a\tb") = utf8Bytes "=?base64?YQli?=" ∧
    encodeHeaderValue (utf8Bytes "a\r\nEvil: 1") = utf8Bytes "=?base64?YQ0KRXZpbDogMQ==?=" ∧
    encodeHeaderValue (utf8Bytes "=?base64?=") = utf8Bytes "=?base64?PT9iYXNlNjQ/PQ==?=" := by
  decide +kernel

-- G01/G04: `=?base64?=` passes G01's sentinel-shape test (prefix and suffix, overlapping) but is
-- no sentinel for G04; `=?base64?x?=` is both; `a, b` (CD7) is bare.
example :
    (decide (base64Prefix <+: utf8Bytes "=?base64?=") &&
      decide (base64Suffix <:+ utf8Bytes "=?base64?=")) = true ∧
    sentinelInner? (utf8Bytes "=?base64?=") = none ∧
    sentinelInner? (utf8Bytes "=?base64?x?=") = some (utf8Bytes "x") ∧
    requiresBase64 (utf8Bytes "a, b") = false ∧ requiresBase64 (utf8Bytes "\"a\"") = false ∧
    encodeHeaderValue (utf8Bytes "a, b") = utf8Bytes "a, b" := by
  decide +kernel

-- G04: sentinels decode; a non-sentinel is returned unchanged (also `=?base64?=`, too short,
-- and `=?BASE64?…?=`, other case); unpadded, URL-safe, non-zero trailing bits and a decoded
-- non-UTF-8 byte give `none`; `=?base64??=` gives the empty value and
-- `=?base64?dXMtd2VzdDE=?=` gives `us-west1`, which the encoder sends bare (Rust probe values).
example :
    decodeHeaderValue (utf8Bytes "=?base64?w6k=?=") = some (utf8Bytes "é") ∧
    decodeHeaderValue (utf8Bytes "us-west1") = some (utf8Bytes "us-west1") ∧
    decodeHeaderValue (utf8Bytes "=?base64?=") = some (utf8Bytes "=?base64?=") ∧
    decodeHeaderValue (utf8Bytes "=?BASE64?dXM=?=") = some (utf8Bytes "=?BASE64?dXM=?=") ∧
    decodeHeaderValue (utf8Bytes "a\tb") = some (utf8Bytes "a\tb") ∧
    decodeHeaderValue (utf8Bytes "=?base64?dXM?=") = none ∧
    decodeHeaderValue (utf8Bytes "=?base64?-_8=?=") = none ∧
    decodeHeaderValue (utf8Bytes "=?base64?Zh==?=") = none ∧
    decodeHeaderValue (utf8Bytes "=?base64?/w==?=") = none ∧
    decodeHeaderValue (utf8Bytes "=?base64??=") = some [] ∧
    decodeHeaderValue (utf8Bytes "=?base64?dXMtd2VzdDE=?=") = some (utf8Bytes "us-west1") := by
  decide +kernel

-- G04 not injective, CD2 (H17): a value G03 wraps, sent bare, decodes as its G03 encoding does.
example :
    requiresBase64 (utf8Bytes "a\tb") = true ∧
    decodeHeaderValue (utf8Bytes "a\tb") = some (utf8Bytes "a\tb") ∧
    decodeHeaderValue (encodeHeaderValue (utf8Bytes "a\tb")) = some (utf8Bytes "a\tb") ∧
    requiresBase64 (utf8Bytes "=?base64?=") = true ∧
    decodeHeaderValue (utf8Bytes "=?base64?=") = some (utf8Bytes "=?base64?=") ∧
    decodeHeaderValue (utf8Bytes "=?base64?PT9iYXNlNjQ/PQ==?=") =
      some (utf8Bytes "=?base64?=") := by
  decide +kernel

end Defs.McpHeaders
