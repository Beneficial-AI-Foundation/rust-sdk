/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Defs
public import Proofs.Transport.McpHeaders

@[expose] public section

/-!
# Internal spec file for the SEP-2243 header-value encoding of `mcp_headers.rs` (G01–G04)

These are guarantees about private functions of
`crates/rmcp/src/transport/common/mcp_headers.rs`, kept out of `formal/specs/`, which holds only
the public API (human decision 2026-11-24; precedent `Proofs.Internal.Transport.Auth.AuthMetadata`).
Index of all guarantees: `formal/specs/README.md`. Drafted by AI (Claude Code, model
`claude-opus-5-5`) on 2026-11-27, revised in spec cycle rounds 2–5 (2026-11-27 to 2026-11-28);
signed off by the human spec owner (Hoang Le Truong) on 2026-11-28.

The targets are private functions of `crates/rmcp/src/transport/common/mcp_headers.rs`, made
translatable by translation patch 07 (human decisions GD1–GD3, `formal/README.md`): G01
`requires_base64`, G02 `is_tchar`, G03 `encode_header_value`, G04 `decode_header_value` (Rust
source order). One row per theorem below; the theorem is `Theorems.mcp_headers.<Theorem>`, both
for the spec theorems with their companions and for the laws of `Defs.McpHeaders` (statements
about the definitions only, with no Rust call). Linkage `patch-07` for all four.

| ID | Function | Theorem | Guarantee | Assumptions |
|---|---|---|---|---|
| G01 | `requires_base64` | `requires_base64` | never fails; `requiresBase64` | none |
| G02 | `is_tchar` | `is_tchar` | never fails; `isTchar` (RFC 9110 `tchar`) | none |
| G03 | `encode_header_value` | `encode_header_value` | never fails; `encodeHeaderValue` | (E) |
| G03 | same | `encode_header_value_fail` | wrapped value over `isize::MAX` bytes: `panic` | none |
| G03 | same | `encode_header_value_spec_of_length_le` | as the spec | (E') |
| G04 | `decode_header_value` | `decode_header_value` | never fails; `decodeHeaderValue` | (U), (D) |
| G04 | same | `decode_header_value_fail_undef` | non-sentinel, not UTF-8: `undef` | none |
| G04 | same | `decode_header_value_fail` | decode buffer over `isize::MAX`: `panic` | none |
| G04 | same | `decode_header_value_spec_of_isUtf8` | as the spec | (U*), (D') |
| law | G02 | `isTchar_eq_true_iff_isVchar_and_not_isDelimiter` | `tchar` = VCHAR minus the 17 delimiters | none |
| law | G02 | `isTchar_eq_true_iff_mem_tchars` | `tchar` = the 77 listed chars | none |
| law | G02 | `length_tchars`, `nodup_tchars` | the list has 77 distinct chars | none |
| law | G01 | `requiresBase64_utf8Bytes` | on UTF-8: the char-level test of the Rust doc | none |
| law | G01 | `isUtf8_of_requiresBase64_eq_false` | a bare value is ASCII, hence UTF-8 | none |
| law | G01/G04 | `sentinelInner?_eq_none_of_requiresBase64_eq_false` | a bare value is no sentinel for G04 | none |
| law | G01/G04 | `prefix_and_suffix_and_sentinelInner?_eq_none_iff` | G01's sentinel test and G04's disagree only on `=?base64?=` | none |
| law | G04 | `sentinelInner?_eq_some_iff` | G04's sentinel is `=?base64?` ++ inner ++ `?=` | none |
| law | G04 | `decodeHeaderValue_eq_some_iff` | what G04 accepts, and returns | none |
| law | G04 | `decodeHeaderValue_eq_none_iff` | G04 rejects exactly a sentinel with no UTF-8 preimage | none |
| law | G03 | `encodeHeaderValue_eq_self_iff` | unchanged exactly when not wrapped | none |
| law | G03 | `isBareHeaderValue_encodeHeaderValue` | bytes `0x20`–`0x7E`, no SP/HTAB at either end | none |
| law | G03 | `encodeHeaderValue_eq_wrapSentinel_of_requiresBase64_eq_true` | the wrapped form is the sentinel around the Base64 | wrapped |
| law | G03 | `encodeHeaderValue_eq_self_of_requiresBase64_eq_false` | a bare value is sent unchanged | bare |
| law | G03 | `isVisibleAscii_encodeHeaderValue_of_requiresBase64_eq_true` | a wrapped value has only bytes `0x21`–`0x7E` | wrapped |
| law | — | `isFieldValue_of_isBareHeaderValue` | such a value is an RFC 9110 field value | none |
| law | G03/G04 | `decodeHeaderValue_encodeHeaderValue` | round trip on UTF-8 | UTF-8 |
| law | G03 | `encodeHeaderValue_injective` | distinct values give distinct header values | none |
| law | G04 | `decodeHeaderValue_wrapSentinel_b64StdPad` | every wrapped UTF-8 value decodes, also an unneeded wrap (CD1) | UTF-8 |
| law | G03/G04 | `decodeHeaderValue_eq_some_iff_encodeHeaderValue` | G04 accepts exactly the G03 output and two lenient forms (CD1, CD2) | UTF-8 |
| (a) | G03, G04 | `decode_header_value_encode_header_value` | round trip of the translated functions | (E) |
| (b) | G03 | `isBareHeaderValue_encode_header_value` | header safety, bytes `0x20`–`0x7E` form | (E) |
| (b) | G01, G03 | `encode_header_value_eq_wrapSentinel_of_requires_base64_eq_true` | wrapped form: sentinel around the Base64 | (E), wrapped |
| (b) | G01, G03 | `isVisibleAscii_encode_header_value_of_requires_base64_eq_true` | header safety, wrapped form `0x21`–`0x7E` | (E), wrapped |
| (c) | G01, G03 | `encode_header_value_eq_self_iff` | unchanged exactly when `requires_base64` is `false` | (E) |
| (d) | G02 | `is_tchar_eq_true_iff_mem_tchars` | `true` exactly for the 77 chars of `tchars` | none |
| (d) | G02 | `is_tchar_eq_true_iff_isVchar_and_not_isDelimiter` | `true` exactly for VCHAR minus the 17 RFC 9110 delimiters | none |
| (e) | G04 | `decode_header_value_eq_some_iff` | accepts exactly: non-sentinel unchanged, canonical Base64 of UTF-8 | (U), (D) |
| (e) | G04 | `decode_header_value_eq_none_iff` | `None` exactly for a sentinel with no canonical UTF-8 preimage | (U), (D) |

Keys. (E) `EncodeFits value.val`: if the value is wrapped, its encoding plus the 11 sentinel
bytes fits in `isize::MAX` bytes (exact, `encode_header_value_fail`); (E') `value.val.length ≤
isize::MAX / 2`, which implies (E); (U) if the value is not a sentinel for G04
(`sentinelInner? value.val = none`), it is UTF-8 (`ExtModel.IsUtf8`, rule (ii)(a); exact,
`decode_header_value_fail_undef`, so this conditional form is the weakest premise under which G04
never fails; the spec owner approved this form of the UTF-8 rule on 2026-11-27); (U*) the value
is UTF-8 (rule (ii)(a); implies (U)); (D)
`DecodeFits value.val`: the decode buffer of a sentinel's inner text fits in `isize::MAX` bytes
(exact, `decode_header_value_fail`); (D') `value.val.length ≤ isize::MAX`, which implies (D).
"wrapped": `requiresBase64 value.val = true`; "bare": `requiresBase64 value.val = false`;
"UTF-8": the bytes are UTF-8 (premise of a law
about the model, not about a Rust value).

What the premises restrict. (U), (U*), (D) and (D') hold for every Rust `&str` (UTF-8, at most
`isize::MAX` bytes), so `decode_header_value_fail_undef` and `decode_header_value_fail` describe
the Lean model only. (E) and (E') are domain restrictions: a Rust `&str` of more than about
`3/4 · isize::MAX` bytes that must be wrapped makes Rust panic too (capacity overflow), as
`encode_header_value_fail` states. G03 needs no UTF-8 premise: a value that is not UTF-8 has a
byte of at least `0x80`, so it is wrapped, and the wrapping branch reads only bytes
(`isUtf8_of_requiresBase64_eq_false`). G01 and G02 have no premise.

**Candidate disagreements** (what the code does, for the human to judge; scratch Rust probe on the
patched copy, 2026-11-27, `cargo test --lib --no-default-features --features request-state,server,
client,client-side-sse,transport-streamable-http-server,transport-streamable-http-client,auth,
macros`; each value below is also kernel-checked in `Proofs.Defs.McpHeaders`):
- CD1 (non-canonical wrapping accepted; decode not injective): G04 decodes the Base64 form of
  every UTF-8 value, also one that G03 sends bare: `decode_header_value("=?base64?dXMtd2VzdDE=?=")
  = Some("us-west1")` and `decode_header_value("us-west1") = Some("us-west1")`;
  `decode_header_value("=?base64??=") = Some("")`. A server therefore accepts two header values
  for the same body value. An intermediary that routes or filters on the raw `Mcp-Name` /
  `Mcp-Param-*` value without decoding sees a different string from the one the server
  validates (the concern the doc of `header_str`, upstream lines 396–399, raises for
  duplicates). SEP-2243 does not say whether a sender may wrap a value that needs no wrapping,
  nor whether a receiver must accept it. Spec owner (2026-11-27): recorded as low-severity
  upstream candidate "H17", together with CD2, which also makes G04 not injective
  (`decode_header_value("a\tb") = decode_header_value("=?base64?YQli?=") = Some("a\tb")`;
  `decode_header_value("=?base64?=") = decode_header_value("=?base64?PT9iYXNlNjQ/PQ==?=") =
  Some("=?base64?=")`; kernel-checked). Making G04 the exact inverse of G03 needs both: reject a
  sentinel whose decoded value has `requires_base64 = false` (CD1), and reject a non-sentinel
  value with `requires_base64 = true` (CD2); and the two together suffice: for a UTF-8 header
  value `s`, the fixed decoder gives `Some(y)` exactly when `s = encode_header_value(y)`, for
  UTF-8 `y` (a Rust `String`). This follows from `decodeHeaderValue_eq_some_iff`,
  `sentinelInner?_eq_some_iff`,
  `sentinelInner?_eq_none_of_requiresBase64_eq_false` and the two G03 forms
  `encodeHeaderValue_eq_wrapSentinel_of_requiresBase64_eq_true` and
  `encodeHeaderValue_eq_self_of_requiresBase64_eq_false`; a Rust probe on the patched copy agreed
  on all strings of up to 6 characters over SP, HTAB, `a`, `=`, `?`, `é`, DEL and LF, on their
  encodings and on their unneeded Base64 wraps; each rejection alone leaves CD1 or CD2 witnesses.
  `requires_base64` is compiled only with feature
  `client-side-sse` (upstream line 61) and `decode_header_value` with `server-side-http` (line
  255), so such a fix would also have to compile `requires_base64` for the server. The
  statements stay exact (they describe the code).
- CD2 (bare values the encoder would wrap are accepted): G04 returns every non-sentinel value
  unchanged, also one that G01 says must be wrapped: `decode_header_value("a\tb") =
  Some("a\tb")` (interior HTAB passes `HeaderValue::to_str`, `http-1.5.0/src/header/value.rs`
  lines 243–256, which applies `is_visible_ascii`, lines 558–560, to every byte at line 249; and
  RFC 9110 §5.5 allows it), and `decode_header_value("=?base64?=") =
  Some("=?base64?=")` (G01 wraps it: the encoder's sentinel test lets prefix and suffix
  overlap, line 76; the decoder's does not, lines 259–260). The G03 encodings of these values
  decode to the same results, so G04 is not injective (part of "H17", see CD1). Values with
  control bytes other than HTAB, non-ASCII bytes or leading/trailing SP/HTAB cannot reach G04
  through `header_str` (`to_str` rejects the first two); leading/trailing SP/HTAB are stripped
  by hyper's HTTP/1 parser (`httparse-1.10.1/src/lib.rs` lines 1173–1195 skip leading
  whitespace, lines 1228–1239 trim trailing whitespace), which was checked; HTTP/2 (`h2`) and
  other server stacks were not checked. Spec owner (2026-11-27): note only. The round trip is
  not affected (`decodeHeaderValue_encodeHeaderValue`: no value decodes differently from how
  it was encoded).
- CD3 (stricter than RFC 9110, not a defect of the round trip): G01 wraps a value with an
  interior HTAB (`encode_header_value("a\tb") = "=?base64?YQli?="`) or `obs-text` bytes
  (`0x80`–`0xFF`, every non-ASCII char), both allowed in a field value by RFC 9110 §5.5;
  this matches the rmcp doc (upstream lines 58–60, "control/non-ASCII characters"). Spec owner
  (2026-11-27): intended; it matches the SEP-2243 sender rule (wrap leading/trailing SP/HTAB,
  non-ASCII, control `0x00`–`0x1F`/`0x7F`, and plain values matching the sentinel pattern).
- CD4 (sentinel form): the sentinel is case-sensitive and is not an RFC 2047 encoded word
  (`=?charset?B?text?=`): `decode_header_value("=?BASE64?dXM=?=")` returns the value unchanged,
  and an RFC 2047 word such as `=?utf-8?B?w6k=?=` is a bare value. Unpadded Base64
  (`=?base64?dXM?=`), the URL-safe alphabet (`=?base64?-_8=?=`) and non-zero trailing bits
  (`=?base64?Zh==?=`) give `None` (strict `BASE64_STANDARD`, `RequireCanonical`). Spec owner
  (2026-11-27): intended; SEP-2243 markers are lowercase and case-sensitive. SEP-2243 does not
  specify the Base64 alphabet or padding; the code uses the standard alphabet, padded.
- CD5 (error text): a sentinel whose Base64 is valid but whose bytes are not UTF-8
  (`=?base64?/w==?=`) gives `None`, which `validate_request_headers` reports as "… is not valid
  Base64" (upstream lines 347–348, 380–381); the doc of G04 (line 254) says "invalid
  Base64/UTF-8". The caller maps the error to JSON-RPC `-32020` with HTTP 400 (doc, upstream
  lines 320–321): `validate_standard_headers` (`transport/streamable_http_server/tower.rs`,
  upstream lines 1055–1056) returns `header_mismatch_jsonrpc_response(request_id, reason)`
  (`tower.rs` lines 968–979; error built at line 972 with `ErrorData::header_mismatch`,
  upstream `model.rs` lines 688–690 (patched 690–692), code `ErrorCode::HEADER_MISMATCH` =
  `-32020` at upstream `model.rs` line 639 (patched 641); HTTP 400 set at `tower.rs` line 975;
  `tower.rs` lines are the same in both copies), the code of the SEP-2243 spec page. SEP-2243
  does not specify non-UTF-8 payloads.
  Spec owner (2026-11-27): note only.
- CD6 (empty value): `encode_header_value("") = ""` (G01, lines 63–65): an empty header value,
  which RFC 9110 allows (`*field-content`) but some intermediaries drop; the server would then
  report a missing header. SEP-2243 does not specify empty values. Spec owner (2026-11-27): note
  only.
- CD7 (list delimiters travel bare): `,` and `"` are printable ASCII, so G01 does not wrap them:
  `requires_base64("a, b") = false` and `encode_header_value("a, b") = "a, b"` (kernel-checked).
  Under RFC 9110 §5.3 a recipient or proxy may combine duplicate field lines into one value
  joined by `, `, and a merged duplicate pair cannot be told apart from a single bare value that
  contains `, `. `header_str` rejects a duplicated field (upstream lines 394–413) but cannot see
  one an intermediary already merged. Spec owner (2026-11-27): low-severity upstream candidate
  "H18".
No value `v` was found with `decode(encode v) ≠ Some(v)`: the round trip holds for every UTF-8
string (`decode_header_value_encode_header_value`).

**Translated configuration** (the statements are about it): target `x86_64-unknown-linux-gnu`,
`--no-default-features` with the features of Phase 2 (plan Section 15), `overflow-checks=true`,
`debug-assertions=true`, through translation patch 07. "upstream" line numbers refer to
`mcp_headers.rs` at `7caec76`; "patched" to the copy with patches 01–07 (blob `a8f6185`).
Other rmcp files are cited the same way: `model.rs` as "upstream lines … (patched …)", since the
patches shift its lines; the cited `tower.rs` lines are the same in both copies (patch 02 only
appends tests after line 2613), so they are given once.

**Definitions used:** `Defs.McpHeaders` (`proofs/Proofs/Defs/McpHeaders.lean`) and
`Defs.utf8Bytes`. External models: section "`mcp_headers.rs` header-value encoding" of
`trusted/Rmcp/FunsExternal.lean` (`ExtModel.b64StdPad`, `ExtModel.b64StdPadDecode`,
`ExtModel.b64StdDecodedLenEstimate`, the byte-level `prim` models) and the string models
(`str::to_owned`, `String::from_utf8`, `ExtModel.strOfBytes?`, `ExtModel.IsUtf8`). Laws of the
models used by the proofs: `Proofs.External.Base64Std`.

Each statement is restated as a theorem proved by the theorem of the same name (with `_spec`
for the spec theorems) in `Proofs/Transport/McpHeaders.lean` (namespaces
`rmcp.transport.common.mcp_headers` and, for the laws, `Defs.McpHeaders`), and followed by the
assumptions its proof depends on, checked by `#print axioms` under `#guard_msgs`. The statement
text is the signed-off text, with one difference of form: the translated functions are written
with their full names `rmcp.transport.common.mcp_headers.…` (inside
`theorem Theorems.mcp_headers.…` a short name would resolve to the restated theorem of that
name), and some long lines are wrapped differently; each restated type was checked equal, as a
kernel term, to the signed-off one.
-/

open Aeneas Aeneas.Std Result
open rmcp
open Defs (utf8Bytes)
open Defs.McpHeaders

/-! ## G01–G04 (upstream lines 62–268, patched 62–261), in Rust source order -/

/-- **Spec theorem for `rmcp::transport::common::mcp_headers::requires_base64`** (G01; upstream
lines 62–77, patched 62–76)

Never fails, on every `Str` (all checks read bytes; the control/non-ASCII test is the byte-level
model, equal to Rust's char-level test on UTF-8, law `requiresBase64_utf8Bytes`). `true` exactly
when the value is non-empty and its first or last byte is SP or HTAB (lines 66–69), or some byte
is outside `0x20`–`0x7E` (lines 70–75), or it starts with `=?base64?` and ends with `?=` (line 76,
possibly overlapping) (`Defs.McpHeaders.requiresBase64`; the empty value gives `false`, lines
63–65). No premise. -/
theorem Theorems.mcp_headers.requires_base64 (value : Str) :
    rmcp.transport.common.mcp_headers.requires_base64 value ⦃ (result : Bool) =>
      result = requiresBase64 value.val ⦄ :=
  @rmcp.transport.common.mcp_headers.requires_base64_spec value

/--
info: 'Theorems.mcp_headers.requires_base64' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.mcp_headers.requires_base64

/-- **Spec theorem for `rmcp::transport::common::mcp_headers::is_tchar`** (G02; upstream lines
81–100, patched 80–98)

Never fails. `true` exactly for an RFC 9110 §5.6.2 token character: an ASCII letter or digit
(`is_ascii_alphanumeric`, line 82) or one of `` !#$%&'*+-.^_`|~ `` (lines 83–99; patched 82–97, the
quote compared as `char::from(b'\'')`) (`Defs.McpHeaders.isTchar`). No premise. -/
theorem Theorems.mcp_headers.is_tchar (c : Char) :
    rmcp.transport.common.mcp_headers.is_tchar c ⦃ (result : Bool) =>
      result = isTchar c ⦄ :=
  @rmcp.transport.common.mcp_headers.is_tchar_spec c

/--
info: 'Theorems.mcp_headers.is_tchar' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.mcp_headers.is_tchar

/-- **Spec theorem for `rmcp::transport::common::mcp_headers::encode_header_value`** (G03;
upstream lines 242–252, patched 240–246)

Never fails under (E). The bytes of the result are `Defs.McpHeaders.encodeHeaderValue value.val`:
if `requires_base64(value)` (line 244), `=?base64?` ++ the padded standard Base64 encoding of the
bytes of `value` ++ `?=` (lines 245–248); otherwise the bytes of `value` (`value.to_owned()`,
line 250). Premise (E) `EncodeFits value.val`: a wrapped value fits in `isize::MAX` bytes;
exact (`encode_header_value_fail`). No UTF-8 premise: a value that is not UTF-8 is wrapped
(`Defs.McpHeaders.isUtf8_of_requiresBase64_eq_false`), and the wrapping branch reads only bytes;
for such a value the result is the wrapped Base64 of its bytes. -/
theorem Theorems.mcp_headers.encode_header_value (value : Str)
    (h_fits : EncodeFits value.val) :
    rmcp.transport.common.mcp_headers.encode_header_value value ⦃ (result : String) =>
      utf8Bytes result = encodeHeaderValue value.val ⦄ :=
  @rmcp.transport.common.mcp_headers.encode_header_value_spec value h_fits

/--
info: 'Theorems.mcp_headers.encode_header_value' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.mcp_headers.encode_header_value

/-- G03 without (E): a value that must be wrapped and whose wrapped form exceeds `isize::MAX`
bytes makes the call panic (in `base64_encode` if the Base64 text alone is too long, otherwise in
`wrap_sentinel`; Rust panics there too, "capacity overflow"). -/
theorem Theorems.mcp_headers.encode_header_value_fail (value : Str)
    (h_req : requiresBase64 value.val = true)
    (h_len : ExtModel.maxStringBytes < (value.val.length + 2) / 3 * 4 + 11) :
    rmcp.transport.common.mcp_headers.encode_header_value value = fail Error.panic :=
  @rmcp.transport.common.mcp_headers.encode_header_value_fail value h_req h_len

/--
info: 'Theorems.mcp_headers.encode_header_value_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.mcp_headers.encode_header_value_fail

/-- G03 for a value of at most `isize::MAX / 2` bytes (E'), which implies (E)
(`Proofs.External.Base64Std.add_two_div_three_mul_four_add_eleven_le`). -/
theorem Theorems.mcp_headers.encode_header_value_spec_of_length_le (value : Str)
    (h_len : value.val.length ≤ ExtModel.maxStringBytes / 2) :
    rmcp.transport.common.mcp_headers.encode_header_value value ⦃ (result : String) =>
      utf8Bytes result = encodeHeaderValue value.val ⦄ :=
  @rmcp.transport.common.mcp_headers.encode_header_value_spec_of_length_le value h_len

/--
info: 'Theorems.mcp_headers.encode_header_value_spec_of_length_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.mcp_headers.encode_header_value_spec_of_length_le

/-- **Spec theorem for `rmcp::transport::common::mcp_headers::decode_header_value`** (G04;
upstream lines 256–268, patched 250–261)

Never fails under (U) and (D). `result.map utf8Bytes = Defs.McpHeaders.decodeHeaderValue value.val`
(the bytes determine the `String`): if `value` is `=?base64?` ++ `inner` ++ `?=` (lines 258–261),
`Some` of the string whose bytes `inner` encodes in strict padded standard Base64 (line 263),
`None` if `inner` is not such an encoding (`.ok()?`, line 263) or the decoded bytes are not UTF-8
(`String::from_utf8(bytes).ok()`, line 264); otherwise `Some(value.to_owned())` (line 266).
Premises: (U) a value that is no sentinel is UTF-8 (rule (ii)(a); a sentinel needs none, its
path reads only bytes). (U) is the exact, weakest form of the UTF-8 premise:
`decode_header_value_fail_undef` shows that without it the model fails. The spec owner approved
this conditional form of the UTF-8 rule on 2026-11-27. (D)
`DecodeFits value.val` (exact, `decode_header_value_fail`). -/
theorem Theorems.mcp_headers.decode_header_value (value : Str)
    (h_utf8 : sentinelInner? value.val = none → ExtModel.IsUtf8 value.val)
    (h_fits : DecodeFits value.val) :
    rmcp.transport.common.mcp_headers.decode_header_value value ⦃ (result : Option String) =>
      result.map utf8Bytes = decodeHeaderValue value.val ⦄ :=
  @rmcp.transport.common.mcp_headers.decode_header_value_spec value h_utf8 h_fits

/--
info: 'Theorems.mcp_headers.decode_header_value' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.mcp_headers.decode_header_value

/-- G04 without (U): a value that is no sentinel and not UTF-8 (no Rust `&str`) reaches the
`fail undef` of the `str::to_owned` model. -/
theorem Theorems.mcp_headers.decode_header_value_fail_undef (value : Str)
    (h_sentinel : sentinelInner? value.val = none)
    (h_utf8 : ¬ ExtModel.IsUtf8 value.val) :
    rmcp.transport.common.mcp_headers.decode_header_value value = fail Error.undef :=
  @rmcp.transport.common.mcp_headers.decode_header_value_fail_undef value h_sentinel h_utf8

/--
info: 'Theorems.mcp_headers.decode_header_value_fail_undef' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.mcp_headers.decode_header_value_fail_undef

/-- G04 without (D): for a sentinel whose decode buffer exceeds `isize::MAX` bytes, the model of
`BASE64_STANDARD.decode` panics before reading (`vec![0; estimate]`, "capacity overflow"). No
Rust `&str` is that long (it would need more than `4/3 · isize::MAX` bytes), so this describes
the Lean model only. -/
theorem Theorems.mcp_headers.decode_header_value_fail (value : Str) (inner : List U8)
    (h_sentinel : sentinelInner? value.val = some inner)
    (h_len : ExtModel.maxStringBytes < ExtModel.b64StdDecodedLenEstimate inner.length) :
    rmcp.transport.common.mcp_headers.decode_header_value value = fail Error.panic :=
  @rmcp.transport.common.mcp_headers.decode_header_value_fail value inner h_sentinel h_len

/--
info: 'Theorems.mcp_headers.decode_header_value_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.mcp_headers.decode_header_value_fail

/-- G04 under the invariants of every Rust `&str`: UTF-8 (U*, implies (U)) and at most
`isize::MAX` bytes (D', implies (D) by
`Proofs.External.Base64Std.b64StdDecodedLenEstimate_le_of_le`, the inner text being shorter). -/
theorem Theorems.mcp_headers.decode_header_value_spec_of_isUtf8 (value : Str)
    (h_utf8 : ExtModel.IsUtf8 value.val)
    (h_len : value.val.length ≤ ExtModel.maxStringBytes) :
    rmcp.transport.common.mcp_headers.decode_header_value value ⦃ (result : Option String) =>
      result.map utf8Bytes = decodeHeaderValue value.val ⦄ :=
  @rmcp.transport.common.mcp_headers.decode_header_value_spec_of_isUtf8 value h_utf8 h_len

/--
info: 'Theorems.mcp_headers.decode_header_value_spec_of_isUtf8' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.mcp_headers.decode_header_value_spec_of_isUtf8

/-! ## Laws of `Defs.McpHeaders` -/

/-- **`tchar` is VCHAR except the delimiters** (RFC 9110 §5.6.2: "any VCHAR, except
delimiters"): the ABNF list and the prose of the RFC agree. In particular every token character
is visible ASCII (`0x21`–`0x7E`): no SP, no control, nothing non-ASCII. -/
theorem Theorems.mcp_headers.isTchar_eq_true_iff_isVchar_and_not_isDelimiter (c : Char) :
    isTchar c = true ↔ isVchar c = true ∧ isDelimiter c = false :=
  @Defs.McpHeaders.isTchar_eq_true_iff_isVchar_and_not_isDelimiter c

/--
info: 'Theorems.mcp_headers.isTchar_eq_true_iff_isVchar_and_not_isDelimiter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.mcp_headers.isTchar_eq_true_iff_isVchar_and_not_isDelimiter

/-- **The token characters are the 77 chars of `tchars`.** -/
theorem Theorems.mcp_headers.isTchar_eq_true_iff_mem_tchars
    (c : Char) : isTchar c = true ↔ c ∈ tchars :=
  @Defs.McpHeaders.isTchar_eq_true_iff_mem_tchars c

/--
info: 'Theorems.mcp_headers.isTchar_eq_true_iff_mem_tchars' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.mcp_headers.isTchar_eq_true_iff_mem_tchars

/-- `tchars` has 77 elements (94 VCHAR minus 17 delimiters). -/
theorem Theorems.mcp_headers.length_tchars : tchars.length = 77 :=
  Defs.McpHeaders.length_tchars

/--
info: 'Theorems.mcp_headers.length_tchars' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.mcp_headers.length_tchars

/-- `tchars` has no repetition, so it lists 77 distinct characters. -/
theorem Theorems.mcp_headers.nodup_tchars : tchars.Nodup :=
  Defs.McpHeaders.nodup_tchars

/--
info: 'Theorems.mcp_headers.nodup_tchars' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.mcp_headers.nodup_tchars

/-- **G01 at the char level, on UTF-8** (the reading of the Rust doc, upstream lines 58–60 and
the code of lines 63–76): for the bytes of a string `v`, wrapping is required exactly when the
first or the last char is SP or HTAB, or some char has a code point below `0x20` or above
`0x7E` (`(c as u32) < 0x20 || (c as u32) > 0x7E`, lines 70–75), or `v` starts with `=?base64?`
and ends with `?=`. (The first byte of a UTF-8 string is SP or HTAB exactly when its first char
is, and likewise for the last; `Proofs.External.Base64Std.any_isControlOrNonAsciiByte_utf8` for
the middle test.) -/
theorem Theorems.mcp_headers.requiresBase64_utf8Bytes (v : String) :
    requiresBase64 (utf8Bytes v) =
      (v.toList.head?.any (fun c => decide (c = ' ' ∨ c = '\t')) ||
        v.toList.getLast?.any (fun c => decide (c = ' ' ∨ c = '\t')) ||
        v.toList.any (fun c => decide (c.toNat < 0x20 ∨ 0x7E < c.toNat)) ||
        (decide ("=?base64?".toList <+: v.toList) && decide ("?=".toList <:+ v.toList))) :=
  @Defs.McpHeaders.requiresBase64_utf8Bytes v

/--
info: 'Theorems.mcp_headers.requiresBase64_utf8Bytes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.mcp_headers.requiresBase64_utf8Bytes

/-- **A value that is not wrapped is UTF-8**: its bytes are printable ASCII. So G03 never reaches
the `fail undef` of the `str::to_owned` model, and needs no UTF-8 premise. -/
theorem Theorems.mcp_headers.isUtf8_of_requiresBase64_eq_false
    (s : List U8) (h : requiresBase64 s = false) :
    ExtModel.IsUtf8 s :=
  @Defs.McpHeaders.isUtf8_of_requiresBase64_eq_false s h

/--
info: 'Theorems.mcp_headers.isUtf8_of_requiresBase64_eq_false' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.mcp_headers.isUtf8_of_requiresBase64_eq_false

/-- **A value that is not wrapped is no sentinel for G04**: G01's sentinel test (prefix and
suffix, line 76) is implied by G04's (prefix, then suffix of the rest, lines 259–260). This is
why the round trip has no gap. -/
theorem Theorems.mcp_headers.sentinelInner?_eq_none_of_requiresBase64_eq_false (s : List U8)
    (h : requiresBase64 s = false) : sentinelInner? s = none :=
  @Defs.McpHeaders.sentinelInner?_eq_none_of_requiresBase64_eq_false s h

/--
info: 'Theorems.mcp_headers.sentinelInner?_eq_none_of_requiresBase64_eq_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.mcp_headers.sentinelInner?_eq_none_of_requiresBase64_eq_false

/-- **G01's sentinel-shape test and G04's sentinel test disagree only on `=?base64?=`**: a value
that starts with `=?base64?` and ends with `?=` (G01, line 76; the fourth disjunct of
`requiresBase64`) and yet is no sentinel for G04 (lines 258–261: the suffix is looked for after
the prefix) is exactly the 10-byte `=?base64?=`, where prefix and suffix overlap in one `=`.
Every other value passing G01's test is `=?base64?` ++ `inner` ++ `?=` (CD2). -/
theorem Theorems.mcp_headers.prefix_and_suffix_and_sentinelInner?_eq_none_iff (s : List U8) :
    base64Prefix <+: s ∧ base64Suffix <:+ s ∧ sentinelInner? s = none ↔
      s = utf8Bytes "=?base64?=" :=
  @Defs.McpHeaders.prefix_and_suffix_and_sentinelInner?_eq_none_iff s

/--
info: 'Theorems.mcp_headers.prefix_and_suffix_and_sentinelInner?_eq_none_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.mcp_headers.prefix_and_suffix_and_sentinelInner?_eq_none_iff

/-- **G04's sentinel**: `sentinelInner? s = some inner` exactly when `s` is `=?base64?` ++
`inner` ++ `?=` (`strip_prefix` then `strip_suffix`, upstream lines 258–261). -/
theorem Theorems.mcp_headers.sentinelInner?_eq_some_iff (s inner : List U8) :
    sentinelInner? s = some inner ↔ s = wrapSentinel inner :=
  @Defs.McpHeaders.sentinelInner?_eq_some_iff s inner

/--
info: 'Theorems.mcp_headers.sentinelInner?_eq_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.mcp_headers.sentinelInner?_eq_some_iff

/-- **What G04 accepts** (property (e), on the model): `decodeHeaderValue s = some y` exactly when
`s` is no sentinel and `y = s` (returned unchanged, upstream line 266, patched lines 257 and
259), or `s` is the sentinel around the canonical padded standard Base64 encoding of `y` and `y`
is UTF-8
(`Proofs.External.Base64Std.b64StdPadDecode_eq_some_iff`: the strict decoder accepts exactly the
outputs of the encoder). -/
theorem Theorems.mcp_headers.decodeHeaderValue_eq_some_iff (s y : List U8) :
    decodeHeaderValue s = some y ↔
      (sentinelInner? s = none ∧ y = s) ∨
        (s = wrapSentinel (ExtModel.b64StdPad y) ∧ ExtModel.IsUtf8 y) :=
  @Defs.McpHeaders.decodeHeaderValue_eq_some_iff s y

/--
info: 'Theorems.mcp_headers.decodeHeaderValue_eq_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.mcp_headers.decodeHeaderValue_eq_some_iff

/-- **What G04 rejects**: `none` exactly for a sentinel whose inner text is the padded standard
Base64 encoding of no UTF-8 byte string (invalid Base64, non-canonical padding or trailing bits,
or decoded bytes that are not UTF-8; "Returns `None` if the sentinel wraps invalid
Base64/UTF-8", line 254). -/
theorem Theorems.mcp_headers.decodeHeaderValue_eq_none_iff (s : List U8) :
    decodeHeaderValue s = none ↔
      ∃ inner, s = wrapSentinel inner ∧
        ∀ y, ExtModel.IsUtf8 y → ExtModel.b64StdPad y ≠ inner :=
  @Defs.McpHeaders.decodeHeaderValue_eq_none_iff s

/--
info: 'Theorems.mcp_headers.decodeHeaderValue_eq_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.mcp_headers.decodeHeaderValue_eq_none_iff

/-- **G03 leaves a value unchanged exactly when it does not wrap it** (property (c), on the
model; the wrapped form is longer than the value: `4 ⌈n / 3⌉ + 11 > n`). -/
theorem Theorems.mcp_headers.encodeHeaderValue_eq_self_iff (s : List U8) :
    encodeHeaderValue s = s ↔ requiresBase64 s = false :=
  @Defs.McpHeaders.encodeHeaderValue_eq_self_iff s

/--
info: 'Theorems.mcp_headers.encodeHeaderValue_eq_self_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.mcp_headers.encodeHeaderValue_eq_self_iff

/-- **Header safety, `0x20`–`0x7E` form** (property (b), on the model): every byte of the encoded
value is printable ASCII and it neither starts nor ends with SP or HTAB. So it contains no CR,
LF, NUL or other control byte (no header injection, no response splitting) and no `obs-text`. -/
theorem Theorems.mcp_headers.isBareHeaderValue_encodeHeaderValue (s : List U8) :
    IsBareHeaderValue (encodeHeaderValue s) :=
  @Defs.McpHeaders.isBareHeaderValue_encodeHeaderValue s

/--
info: 'Theorems.mcp_headers.isBareHeaderValue_encodeHeaderValue' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.mcp_headers.isBareHeaderValue_encodeHeaderValue

/-- **The wrapped form** (G03, upstream lines 244–248): a value that must be wrapped is sent as
`=?base64?` ++ the padded standard Base64 of its bytes ++ `?=`. -/
theorem Theorems.mcp_headers.encodeHeaderValue_eq_wrapSentinel_of_requiresBase64_eq_true
    (s : List U8)
    (h : requiresBase64 s = true) :
    encodeHeaderValue s = wrapSentinel (ExtModel.b64StdPad s) :=
  @Defs.McpHeaders.encodeHeaderValue_eq_wrapSentinel_of_requiresBase64_eq_true s h

/--
info: 'Theorems.mcp_headers.encodeHeaderValue_eq_wrapSentinel_of_requiresBase64_eq_true' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.mcp_headers.encodeHeaderValue_eq_wrapSentinel_of_requiresBase64_eq_true

/-- **The bare form** (G03, upstream line 250): a value that need not be wrapped is sent
unchanged. -/
theorem Theorems.mcp_headers.encodeHeaderValue_eq_self_of_requiresBase64_eq_false (s : List U8)
    (h : requiresBase64 s = false) : encodeHeaderValue s = s :=
  @Defs.McpHeaders.encodeHeaderValue_eq_self_of_requiresBase64_eq_false s h

/--
info: 'Theorems.mcp_headers.encodeHeaderValue_eq_self_of_requiresBase64_eq_false' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.mcp_headers.encodeHeaderValue_eq_self_of_requiresBase64_eq_false

/-- **Header safety, wrapped form** (property (b)): a wrapped value is `=?base64?`, the padded
Base64 symbols and `?=`, all visible ASCII `0x21`–`0x7E` (no SP either;
`Proofs.External.Base64Std.visible_of_mem_b64StdPad`). -/
theorem Theorems.mcp_headers.isVisibleAscii_encodeHeaderValue_of_requiresBase64_eq_true
    (s : List U8)
    (h : requiresBase64 s = true) : IsVisibleAscii (encodeHeaderValue s) :=
  @Defs.McpHeaders.isVisibleAscii_encodeHeaderValue_of_requiresBase64_eq_true s h

/--
info: 'Theorems.mcp_headers.isVisibleAscii_encodeHeaderValue_of_requiresBase64_eq_true' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.mcp_headers.isVisibleAscii_encodeHeaderValue_of_requiresBase64_eq_true

/-- **A bare header value is an RFC 9110 field value** (§5.5). -/
theorem Theorems.mcp_headers.isFieldValue_of_isBareHeaderValue
    (s : List U8) (h : IsBareHeaderValue s) :
    IsFieldValue s :=
  @Defs.McpHeaders.isFieldValue_of_isBareHeaderValue s h

/--
info: 'Theorems.mcp_headers.isFieldValue_of_isBareHeaderValue' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.mcp_headers.isFieldValue_of_isBareHeaderValue

/-- **Round trip on the model** (property (a)): decoding the encoding of UTF-8 bytes gives them
back. A bare value is no sentinel (`sentinelInner?_eq_none_of_requiresBase64_eq_false`); a
wrapped one decodes by the Base64 round trip
(`Proofs.External.Base64Std.b64StdPadDecode_b64StdPad`) and is UTF-8 by premise. -/
theorem Theorems.mcp_headers.decodeHeaderValue_encodeHeaderValue
    (s : List U8) (h : ExtModel.IsUtf8 s) :
    decodeHeaderValue (encodeHeaderValue s) = some s :=
  @Defs.McpHeaders.decodeHeaderValue_encodeHeaderValue s h

/--
info: 'Theorems.mcp_headers.decodeHeaderValue_encodeHeaderValue' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.mcp_headers.decodeHeaderValue_encodeHeaderValue

/-- **G03 is injective** on all byte strings: distinct values give distinct header values (a
bare value is never of the wrapped form, which is a sentinel shape; two wrapped forms are equal
only for equal Base64, hence equal values). -/
theorem Theorems.mcp_headers.encodeHeaderValue_injective : Function.Injective encodeHeaderValue :=
  Defs.McpHeaders.encodeHeaderValue_injective

/--
info: 'Theorems.mcp_headers.encodeHeaderValue_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.mcp_headers.encodeHeaderValue_injective

/-- **Every wrapped UTF-8 value decodes, whether or not G03 would wrap it** (CD1): for a value
that G03 sends bare (`requiresBase64 s = false`), both `s` and this sentinel decode to `s`. -/
theorem Theorems.mcp_headers.decodeHeaderValue_wrapSentinel_b64StdPad
    (s : List U8) (h : ExtModel.IsUtf8 s) :
    decodeHeaderValue (wrapSentinel (ExtModel.b64StdPad s)) = some s :=
  @Defs.McpHeaders.decodeHeaderValue_wrapSentinel_b64StdPad s h

/--
info: 'Theorems.mcp_headers.decodeHeaderValue_wrapSentinel_b64StdPad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.mcp_headers.decodeHeaderValue_wrapSentinel_b64StdPad

/-- **G04 against G03** (CD1, CD2): for a header value `s` that is UTF-8 (every value
`header_str` passes on), `decodeHeaderValue s = some y` exactly when `y` is UTF-8 and either `s`
is G03's encoding of `y`, or `s` is a form G03 never sends for `y`: the sentinel around the
Base64 of a `y` that G03 sends bare (CD1), or `y` itself, bare, although G03 wraps it, provided
`y` is no sentinel for G04 (CD2). -/
theorem Theorems.mcp_headers.decodeHeaderValue_eq_some_iff_encodeHeaderValue (s y : List U8)
    (hs : ExtModel.IsUtf8 s) :
    decodeHeaderValue s = some y ↔
      ExtModel.IsUtf8 y ∧
        (s = encodeHeaderValue y ∨
          (requiresBase64 y = false ∧ s = wrapSentinel (ExtModel.b64StdPad y)) ∨
          (requiresBase64 y = true ∧ sentinelInner? s = none ∧ s = y)) :=
  @Defs.McpHeaders.decodeHeaderValue_eq_some_iff_encodeHeaderValue s y hs

/--
info: 'Theorems.mcp_headers.decodeHeaderValue_eq_some_iff_encodeHeaderValue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.mcp_headers.decodeHeaderValue_eq_some_iff_encodeHeaderValue

/-! ## Compositions -/

/-- **(a) Round trip** (G03 then G04): for the bytes of any string `v` meeting (E),
`encode_header_value` succeeds, its result is a valid `&str`, and `decode_header_value` of any
`Str` holding the result's bytes returns `Some(v)`. So no value decodes differently from how it
was encoded, and every encoded value is accepted by the decoder. About the translated
`encode_header_value` and `decode_header_value`; premises: `value` holds the bytes of `v`, and
(E). -/
theorem Theorems.mcp_headers.decode_header_value_encode_header_value (value : Str) (v : String)
    (h_value : value.val = utf8Bytes v) (h_fits : EncodeFits value.val) :
    rmcp.transport.common.mcp_headers.encode_header_value value ⦃ (encoded : String) =>
      (∃ s : Str, s.val = utf8Bytes encoded) ∧
      ∀ s : Str, s.val = utf8Bytes encoded →
        rmcp.transport.common.mcp_headers.decode_header_value s ⦃ (result : Option String) =>
          result = some v ⦄ ⦄ :=
  @rmcp.transport.common.mcp_headers.decode_header_value_encode_header_value value v h_value h_fits

/--
info: 'Theorems.mcp_headers.decode_header_value_encode_header_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.mcp_headers.decode_header_value_encode_header_value

/-- **(b) Header safety, `0x20`–`0x7E` form**: under (E), every byte of the result of
`encode_header_value` is printable ASCII (`0x20`–`0x7E`) and the result neither starts nor ends
with SP or HTAB (`IsBareHeaderValue`); hence it is an RFC 9110 §5.5 field value
(`IsFieldValue`) with no CR, LF, NUL or other control byte: no header injection, and
`HeaderValue::from_str` in `standard_request_headers` (upstream lines 287–294) accepts it. For
every `Str`, UTF-8 or not. The second conjunct follows from the first
(`isFieldValue_of_isBareHeaderValue`); it is kept so that the statement names the RFC 9110
property. About the translated `encode_header_value`; premise (E). -/
theorem Theorems.mcp_headers.isBareHeaderValue_encode_header_value (value : Str)
    (h_fits : EncodeFits value.val) :
    rmcp.transport.common.mcp_headers.encode_header_value value ⦃ (result : String) =>
      IsBareHeaderValue (utf8Bytes result) ∧ IsFieldValue (utf8Bytes result) ⦄ :=
  @rmcp.transport.common.mcp_headers.isBareHeaderValue_encode_header_value value h_fits

/--
info: 'Theorems.mcp_headers.isBareHeaderValue_encode_header_value' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.mcp_headers.isBareHeaderValue_encode_header_value

/-- **(b) The wrapped form**: when `requires_base64(value)` is `true`, under (E) the result of
`encode_header_value(value)` is `=?base64?` ++ the padded standard Base64 of the bytes of `value`
++ `?=` (upstream lines 244–248). About the translated `requires_base64` and
`encode_header_value`; premise (E). -/
theorem Theorems.mcp_headers.encode_header_value_eq_wrapSentinel_of_requires_base64_eq_true
    (value : Str)
    (h_fits : EncodeFits value.val) :
    rmcp.transport.common.mcp_headers.requires_base64 value ⦃ (b : Bool) =>
      b = true →
        rmcp.transport.common.mcp_headers.encode_header_value value ⦃ (result : String) =>
          utf8Bytes result = wrapSentinel (ExtModel.b64StdPad value.val) ⦄ ⦄ :=
  @rmcp.transport.common.mcp_headers.encode_header_value_eq_wrapSentinel_of_requires_base64_eq_true
    value h_fits

/--
info: 'Theorems.mcp_headers.encode_header_value_eq_wrapSentinel_of_requires_base64_eq_true' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.mcp_headers.encode_header_value_eq_wrapSentinel_of_requires_base64_eq_true

/-- **(b) Header safety, wrapped form**: when `requires_base64(value)` is `true`, under (E) every
byte of the result of `encode_header_value(value)` is visible ASCII `0x21`–`0x7E` (no SP, no
HTAB, no control byte, no `obs-text`). About the translated `requires_base64` and
`encode_header_value`; premise (E). -/
theorem Theorems.mcp_headers.isVisibleAscii_encode_header_value_of_requires_base64_eq_true
    (value : Str)
    (h_fits : EncodeFits value.val) :
    rmcp.transport.common.mcp_headers.requires_base64 value ⦃ (b : Bool) =>
      b = true →
        rmcp.transport.common.mcp_headers.encode_header_value value ⦃ (result : String) =>
          IsVisibleAscii (utf8Bytes result) ⦄ ⦄ :=
  @rmcp.transport.common.mcp_headers.isVisibleAscii_encode_header_value_of_requires_base64_eq_true
    value h_fits

/--
info: 'Theorems.mcp_headers.isVisibleAscii_encode_header_value_of_requires_base64_eq_true' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.mcp_headers.isVisibleAscii_encode_header_value_of_requires_base64_eq_true

/-- **(c) Bare exactly when not required**: `encode_header_value(value)` has the bytes of `value`
exactly when `requires_base64(value)` is `false`. About the translated `requires_base64` and
`encode_header_value`; premise (E). -/
theorem Theorems.mcp_headers.encode_header_value_eq_self_iff (value : Str)
    (h_fits : EncodeFits value.val) :
    rmcp.transport.common.mcp_headers.requires_base64 value ⦃ (b : Bool) =>
      rmcp.transport.common.mcp_headers.encode_header_value value ⦃ (result : String) =>
        (utf8Bytes result = value.val ↔ b = false) ⦄ ⦄ :=
  @rmcp.transport.common.mcp_headers.encode_header_value_eq_self_iff value h_fits

/--
info: 'Theorems.mcp_headers.encode_header_value_eq_self_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.mcp_headers.encode_header_value_eq_self_iff

/-- **(d) The token characters, listed**: `is_tchar(c)` is `true` exactly for the 77 characters
of `Defs.McpHeaders.tchars` (77 distinct chars: `length_tchars`, `nodup_tchars`; the RFC 9110
§5.6.2 `tchar` list, upstream lines 81–100). About the translated `is_tchar`; no premise. -/
theorem Theorems.mcp_headers.is_tchar_eq_true_iff_mem_tchars (c : Char) :
    rmcp.transport.common.mcp_headers.is_tchar c ⦃ (result : Bool) =>
      (result = true ↔ c ∈ tchars) ⦄ :=
  @rmcp.transport.common.mcp_headers.is_tchar_eq_true_iff_mem_tchars c

/--
info: 'Theorems.mcp_headers.is_tchar_eq_true_iff_mem_tchars' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.mcp_headers.is_tchar_eq_true_iff_mem_tchars

/-- **(d) The token characters, RFC 9110 prose**: `is_tchar(c)` is `true` exactly for the visible
ASCII characters (`0x21`–`0x7E`) other than the 17 RFC 9110 delimiters (§5.6.2, "any VCHAR,
except delimiters"); no non-ASCII character, no control, no SP. About the translated
`is_tchar`; no premise. -/
theorem Theorems.mcp_headers.is_tchar_eq_true_iff_isVchar_and_not_isDelimiter (c : Char) :
    rmcp.transport.common.mcp_headers.is_tchar c ⦃ (result : Bool) =>
      (result = true ↔ isVchar c = true ∧ isDelimiter c = false) ⦄ :=
  @rmcp.transport.common.mcp_headers.is_tchar_eq_true_iff_isVchar_and_not_isDelimiter c

/--
info: 'Theorems.mcp_headers.is_tchar_eq_true_iff_isVchar_and_not_isDelimiter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.mcp_headers.is_tchar_eq_true_iff_isVchar_and_not_isDelimiter

/-- **(e) What the decoder accepts**: under (U) and (D), `decode_header_value(value)` is
`Some(v)` exactly when `value` is no sentinel and holds the bytes of `v` (returned unchanged), or
`value` is `=?base64?` ++ the canonical padded standard Base64 encoding of the UTF-8 bytes of `v`
++ `?=`. (A sentinel is `=?base64?` ++ `inner` ++ `?=` with the two not overlapping.) About the
translated `decode_header_value`; premises (U), (D). -/
theorem Theorems.mcp_headers.decode_header_value_eq_some_iff (value : Str)
    (h_utf8 : sentinelInner? value.val = none → ExtModel.IsUtf8 value.val)
    (h_fits : DecodeFits value.val) :
    rmcp.transport.common.mcp_headers.decode_header_value value ⦃ (result : Option String) =>
      ∀ v : String, result = some v ↔
        (sentinelInner? value.val = none ∧ utf8Bytes v = value.val) ∨
          value.val = wrapSentinel (ExtModel.b64StdPad (utf8Bytes v)) ⦄ :=
  @rmcp.transport.common.mcp_headers.decode_header_value_eq_some_iff value h_utf8 h_fits

/--
info: 'Theorems.mcp_headers.decode_header_value_eq_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.mcp_headers.decode_header_value_eq_some_iff

/-- **(e) What the decoder rejects**: under (U) and (D), `decode_header_value(value)` is `None`
exactly when `value` is a sentinel `=?base64?` ++ `inner` ++ `?=` and `inner` is the padded
standard Base64 encoding of no string's UTF-8 bytes. About the translated `decode_header_value`;
premises (U), (D). -/
theorem Theorems.mcp_headers.decode_header_value_eq_none_iff (value : Str)
    (h_utf8 : sentinelInner? value.val = none → ExtModel.IsUtf8 value.val)
    (h_fits : DecodeFits value.val) :
    rmcp.transport.common.mcp_headers.decode_header_value value ⦃ (result : Option String) =>
      (result = none ↔
        ∃ inner, value.val = wrapSentinel inner ∧
          ∀ v : String, ExtModel.b64StdPad (utf8Bytes v) ≠ inner) ⦄ :=
  @rmcp.transport.common.mcp_headers.decode_header_value_eq_none_iff value h_utf8 h_fits

/--
info: 'Theorems.mcp_headers.decode_header_value_eq_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.mcp_headers.decode_header_value_eq_none_iff
