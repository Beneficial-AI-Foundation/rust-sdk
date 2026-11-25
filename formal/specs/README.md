# What is verified: index of the guarantees

> **At a glance.** Lean proves, for 25 Phase 1 and 25 Phase 2 Rust functions of `rmcp` and 15
> public functions of `request_state.rs` (R01–R15), that the translated call does not panic and
> returns what the statement says. Phase 2 is upstream `7caec76` unmodified; Phase 1 and R01–R08
> are about a patched copy (translation patch 01), R09–R15 about the copy with translation
> patches 01 and 03. 37 guarantees are about the public API
> (`Specs/`), 53 about private, crate-internal or patch-only functions and 116 are laws of the
> trusted models (`../proofs/Proofs/Internal/`): 206 restated theorems. The public
> `request_state.rs` API is covered except 2 of its 17 public functions (R16–R17 `seal_json*`,
> excluded, blocked upstream); R09–R15 were signed off by the spec owner on 2026-11-25. Main
> trust items: Charon/Aeneas/Lean, the translated
> configuration, patches 01 and 03, the hand-written models (including the one clock reading of
> `open`, `open_json` and `seal`);
> no native-code assumption remains (35 were locked until the Aeneas upgrade of 2026-11-24, which is
> reviewed and re-signed by the spec owner 2026-11-24). Two bugs found: H7 (`async_rw` method lists) and H8 (`240.0.0.0/4` not blocked).

**What, against what.** Each guarantee below is a Lean theorem about the
[Aeneas](https://github.com/AeneasVerif/aeneas) translation of the Rust code of `rmcp` (Charon
`0.1.324`, Aeneas `nightly-2026.11.24-fb44cb4`, Lean `v4.36.0`; until 2026-11-24 Charon
`0.1.235`, Aeneas `nightly-2026.08.20-5d08da4`, Lean `v4.31.0`). Phase 2 (IDs M, T, A, C) is
about upstream rmcp commit `7caec76`, **unmodified**. This rests on
`scripts/check-original-linkage.sh`, which checks that the committed translation, generated from
the patched copy, equals block for block the translation of unmodified `7caec76` for the Phase 2
targets; it passes locally, and its CI run (step S22) is pending (the records say "pending S22").
Phase 1 (IDs W, E, S15) and the public `request_state.rs` statements (IDs R; R01–R15 except
`seal_at` and `open_json_with` have the same text upstream, ten lines lower) are about a
**patched copy**: `7caec76` plus translation patch 01
([`../trusted/patches/01-request-state-wire.patch`](../trusted/patches/01-request-state-wire.patch)),
which refactors `RequestStateCodec` onto a new module `request_state_wire`, and for R09–R15
translation patch 03
([`../trusted/patches/03-request-state-public.patch`](../trusted/patches/03-request-state-public.patch),
+6/−2 lines in `seal_at` and `open_json_with` so that they translate); their link to the
unpatched code is tested, not proved. **How to read a statement.** `f x ⦃ r => P r ⦄` means
"the call `f x` does not panic (no failure, overflow or out-of-bounds access) and its result `r`
satisfies `P`"; the premises (`h_…`) are the assumptions; a statement `f x = (do …)` says that
two computations of the translated code are equal, failure included. Theorems about one function
are named `Theorems.<module>.<Type>.<function>` and most are proved by its `…_spec` theorem in
[`../proofs/`](../proofs/); the failing-case companions (`…_fail`), the joint lemmas and the
compositions are named after their statement (e.g. `Theorems.model.into_result_eq`) and proved by
the lemma of the same name. Under each theorem, `#guard_msgs in #print axioms` pins the logical
assumptions it uses: Lean's standard `propext`, `Classical.choice`, `Quot.sound` and nothing
else (until the Aeneas upgrade of 2026-11-24 some statements also listed native-code assumptions,
see "What you must trust"). Status and history:
[`../docs/STATUS.md`](../docs/STATUS.md).

This directory holds only the **public API** (functions `pub` in upstream rmcp); guarantees about
private, crate-internal and patch-only functions are in
[`../proofs/Proofs/Internal/`](../proofs/Proofs/Internal/) (human decision 2026-11-24). Every
guarantee assumes the translated configuration and the trusted models listed at the end.

## Public guarantees

File [`Specs/Model.lean`](Specs/Model.lean) (`crates/rmcp/src/model.rs`) unless noted. The only
premises in this first table are the size premises of M13/M14 (met by every Rust `String`) and
of their failing-case companions; the request-state table below has its own.

| ID | Rust function | Guarantee | Assumptions | Lean theorem |
|---|---|---|---|---|
| M01 | `JsonRpcMessage::into_request` | Returns `Some((req, id))` exactly when the message is the request `req` with id `id`, `None` for every other kind. | none | [`Theorems.model.JsonRpcMessage.into_request`](Specs/Model.lean) |
| M02 | `JsonRpcMessage::into_response` | Returns `Some((resp, id))` exactly when the message is the response `resp` with id `id`, `None` otherwise. | none | [`Theorems.model.JsonRpcMessage.into_response`](Specs/Model.lean) |
| M03 | `JsonRpcMessage::into_notification` | Returns `Some(n)` exactly when the message is the notification `n`, `None` otherwise. | none | [`Theorems.model.JsonRpcMessage.into_notification`](Specs/Model.lean) |
| M04 | `JsonRpcMessage::into_error` | Returns `Some((err, id))` exactly when the message is the error `err` with optional id `id`, `None` otherwise. | none | [`Theorems.model.JsonRpcMessage.into_error`](Specs/Model.lean) |
| M05 | `JsonRpcMessage::into_result` | Returns `Some((Ok(resp), Some(id)))` for a response, `Some((Err(err), id))` for an error, `None` for a request or a notification; never `Some((Ok(_), None))`. | none | [`Theorems.model.JsonRpcMessage.into_result`](Specs/Model.lean) |
| M09 | `SamplingContent::into_vec` | `Single(x)` gives `vec![x]`; `Multiple(v)` gives `v`. | none | [`Theorems.model.SamplingContent.into_vec`](Specs/Model.lean) |
| M10 | `SamplingContent::is_empty` | `false` for `Single`; for `Multiple(v)`, `true` exactly when `v` is empty. | none | [`Theorems.model.SamplingContent.is_empty`](Specs/Model.lean) |
| M11 | `SamplingContent::len` | 1 for `Single`; `v.len()` for `Multiple(v)`. | none | [`Theorems.model.SamplingContent.len`](Specs/Model.lean) |
| M12 | `SamplingContent::first` | `Some(x)` for `Single(x)`; the first element of `v` (`None` if `v` is empty) for `Multiple(v)`. | none | [`Theorems.model.SamplingContent.first`](Specs/Model.lean) |
| M13 | `Reference::as_prompt_name` | For a prompt reference, `Some(s)` where `s` has the UTF-8 bytes of the prompt's name; `None` for a resource reference. | name of at most `usize::MAX` bytes | [`Theorems.model.Reference.as_prompt_name`](Specs/Model.lean) |
| M13 | (failing case) | A Lean string over `usize::MAX` bytes makes the translated call fail; this describes the Lean model only (no Rust `String` is that long). | name over `usize::MAX` bytes | [`Theorems.model.Reference.as_prompt_name_fail`](Specs/Model.lean) |
| M14 | `Reference::as_resource_uri` | For a resource reference, `Some(s)` where `s` has the UTF-8 bytes of its URI; `None` for a prompt reference. | URI of at most `usize::MAX` bytes | [`Theorems.model.Reference.as_resource_uri`](Specs/Model.lean) |
| M14 | (failing case) | As for M13, for a URI over `usize::MAX` bytes (Lean model only). | URI over `usize::MAX` bytes | [`Theorems.model.Reference.as_resource_uri_fail`](Specs/Model.lean) |
| joint lemma | `is_empty`, `len` | `is_empty()` is the same computation as `len() == 0`. | none | [`Theorems.model.SamplingContent.is_empty_eq_len_eq_zero`](Specs/Model.lean) |
| joint lemma | `first`, `into_vec` | `first()` is the same computation as the head of `into_vec()`. | none | [`Theorems.model.SamplingContent.first_eq_head?_into_vec`](Specs/Model.lean) |
| joint lemma | `len`, `into_vec` | `len()` is the same computation as `into_vec().len()`. | none | [`Theorems.model.SamplingContent.len_eq_len_into_vec`](Specs/Model.lean) |
| joint lemma | `into_request` … `into_error` | On every message the four calls succeed and exactly one of them returns `Some`. | none | [`Theorems.model.JsonRpcMessage.exactly_one_some`](Specs/Model.lean) |
| C03 | `into_result`, `into_response`, `into_error` | `into_result` is the same computation as `into_response` mapped to `(Ok(r), Some(id))`, or else `into_error` mapped to `(Err(e), id)`. | none | [`Theorems.model.into_result_eq`](Specs/Model.lean) |
| M08 | `rmcp::model::TaskStatus::is_terminal` (in `model/task.rs`, re-exported by `pub use task::*`) | `true` exactly for `Completed`, `Failed` and `Cancelled`. | none | [`Theorems.task.TaskStatus.is_terminal`](Specs/Model/Task.lean) |

"Same computation" rows are equations of the translated code: equal results and equal failure.
"Joint lemma" rows are the joint lemmas of plan Section 16.1.

**Request-state codec, public API** — [`Specs/Model/RequestState.lean`](Specs/Model/RequestState.lean)
(`crates/rmcp/src/model/request_state.rs`, patched copy; R01–R15 and corollaries of R08, R09
and R10).
Rust functions are `rmcp::model::request_state::…`. Premise keys (the same in the file's
docstring): **`h_into`** the caller's `Into<Vec<u8>>` conversion of `key` returns the vector `v`
(user code, which may panic); **(F)** for a token whose first `.`-component is `rs1`, every rs1
fallback id of the codec is a key id (`CodecFallbacksKnown`; sufficient, not necessary, for the
code's `expect` not to panic);
**(T)** the MAC transcript (`transcriptV1`/`transcriptV2` of the decoded components and `ad`)
fits in `usize::MAX` bytes; **(L)** `ad.len() + sealed.len() + 36 ≤ usize::MAX` (implies (T));
**(S)** the seal-mode key id is a key id (`CodecSealKeyKnown`; else the code's `expect` panics);
**(D)** the Lean-model domain of sealing (`SealFits`: transcript within `usize::MAX`, `with_capacity`
sum within `isize::MAX`); **(Ls)** `ad.len() + 2 * payload.len() + 512 ≤ isize::MAX`; **(R)** the
Lean-model domain of the keyring builders (`KeyringFits`: key ids within `usize::MAX` bytes, fewer
than `usize::MAX` fallbacks; met by every Rust value); **(U)** the converted key ids of
`new_with_keyring` have at most `usize::MAX` bytes (met by every Rust `String`); **caller code**
(`as_ref`, `into`, the caller's iterator) returns the named values.
`ad` is the associated data; "exactly `openAt`" means the result is `Ok` of the bytes, or the
error, that `Defs.CodecState.openAt` gives (the expected result of E11 `open_at`, internal table
below); "`sealAt`" means the token's UTF-8 bytes are those `Defs.CodecState.sealAt` gives (the
expected result of the private `seal_at`, R10a below). R07–R10, R13, R14 and the corollaries are
specified at the clock reading `ExtModel.nowMs`, one opaque
`i64`: each statement holds for that one reading and says nothing about two calls (in Rust two
calls read different times). Inherited exceptions, **not premises** (inputs where Rust panics but
the statement promises a result; "What you must trust"): **(K)** the system clock is before 1970
or outside chrono's range (`Utc::now` panics, even for a malformed token, as the clock is read
first); **(H)** HMAC's bit counter overflows for a transcript of at least `2^61 − 64` bytes or a
key of at least `2^61` bytes; **(V)** `open_with`, `open_json_with`, `seal_with` only: a transcript
`Vec` above `isize::MAX` bytes; **(J)** `open_json*`: the `serde_json::from_slice` model (a
`Deserialize` impl that panics, does not terminate, is non-deterministic or has side effects);
**(I)** R04–R06, R11, R12, R15: a caller conversion or iterator (`Into`, `AsRef`,
`IntoIterator`) with side effects outside its argument or state (global or thread-local state,
input/output), which the premises do not describe; **(P)** a caller `Drop` impl that panics
(R11, R12, R15); **(N)** `HashMap::new` panics if the operating system's random source fails
(R15).

| ID | Rust function | Guarantee | Assumptions | Lean theorem |
|---|---|---|---|---|
| R01 | `SealOptions::new` | Returns options with no associated data (empty) and no time-to-live (`None`). | none | [`Theorems.request_state.SealOptions.new`](Specs/Model/RequestState.lean) |
| R02 | `SealOptions::associated_data` | Returns the options with the associated data set to the argument and the time-to-live unchanged. | none | [`Theorems.request_state.SealOptions.associated_data`](Specs/Model/RequestState.lean) |
| R03 | `SealOptions::ttl` | Returns the options with the time-to-live set to `Some(ttl)` and the associated data unchanged. | none | [`Theorems.request_state.SealOptions.ttl`](Specs/Model/RequestState.lean) |
| R04 | `RequestStateCodec::new` (deprecated) | Returns the single-key codec of `v`, for a key of any length; it satisfies `CodecValid`. | `h_into`; inherited exception (I) | [`Theorems.request_state.RequestStateCodec.new`](Specs/Model/RequestState.lean) |
| R05 | `RequestStateCodec::new_unchecked` | Returns the single-key codec of `v`, for a key of any length; it satisfies `CodecValid`. | `h_into`; inherited exception (I) | [`…RequestStateCodec.new_unchecked`](Specs/Model/RequestState.lean) |
| R06 | `RequestStateCodec::try_new` | `Ok` of the single-key codec of `v` (satisfying `CodecValid`) exactly when `v` has at least 32 bytes, otherwise `KeyTooShort { minimum: 32, actual: v.len() }`. | `h_into`; inherited exception (I) | [`…RequestStateCodec.try_new`](Specs/Model/RequestState.lean) |
| R07 | `RequestStateCodec::open` | Returns exactly `openAt` of the token with no associated data at the clock reading (one reading; says nothing about two calls). | (F); inherited exceptions (K) clock range, (H) HMAC `2^61` | [`…RequestStateCodec.open`](Specs/Model/RequestState.lean) |
| R08 | `RequestStateCodec::open_with` | Returns exactly `openAt` of the token with associated data `ad` at the clock reading (one reading; says nothing about two calls). | (T), (F); inherited exceptions (K) clock range, (H) HMAC `2^61`, (V) `Vec` above `isize::MAX` | [`…RequestStateCodec.open_with`](Specs/Model/RequestState.lean) |
| R08 | `open_with` (corollary) | As R08, with the length premise (L) in place of (T). | (L), (F); inherited exceptions (K) clock range, (H) HMAC `2^61`, (V) `Vec` above `isize::MAX` | [`…RequestStateCodec.open_with_of_length_le`](Specs/Model/RequestState.lean) |
| R09 | `RequestStateCodec::seal` | Returns the token `sealAt` gives with no associated data and no time-to-live at the clock reading (the token does not depend on the reading, but the clock is read). | (S), (D); inherited exceptions (K), (H) | [`…RequestStateCodec.seal`](Specs/Model/RequestState.lean) |
| R09 | `seal` (corollary) | As R09, with `CodecValid` and `2 * payload.len() + 512 ≤ isize::MAX` in place of (S), (D). | `CodecValid`, (Ls); inherited exceptions (K), (H) | [`…RequestStateCodec.seal_of_length_le`](Specs/Model/RequestState.lean) |
| R10 | `RequestStateCodec::seal_with` | Returns the token `sealAt` gives with the options' associated data and time-to-live at the clock reading (one reading; says nothing about two calls). | (S), (D); inherited exceptions (K), (H), (V) | [`…RequestStateCodec.seal_with`](Specs/Model/RequestState.lean) |
| R10 | `seal_with` (corollary) | As R10, with `CodecValid` and (Ls) in place of (S), (D). | `CodecValid`, (Ls); inherited exceptions (K), (H) | [`…RequestStateCodec.seal_with_of_length_le`](Specs/Model/RequestState.lean) |
| R11 | `RequestStateCodec::with_rs1_signing` | On a keyring, for a configured key id: `Ok` of the codec with the same keys, seal mode `Rs1 { key_id }` and the id appended to the rs1 fallbacks unless already there; preserves `CodecValid`. Otherwise `InvalidKeyring` with the exact message (single-key codec; unknown id). | caller code, (R); inherited exceptions (I), (P) | [`…RequestStateCodec.with_rs1_signing`](Specs/Model/RequestState.lean) |
| R12 | `RequestStateCodec::with_rs1_fallback` | On a keyring, for a configured key id: `Ok` of the codec with the same keys and seal mode and the id appended to the rs1 fallbacks unless already there; preserves `CodecValid`. Otherwise `InvalidKeyring` with the exact message (single-key codec; unknown id). | caller code, (R); inherited exceptions (I), (P) | [`…RequestStateCodec.with_rs1_fallback`](Specs/Model/RequestState.lean) |
| R13 | `RequestStateCodec::open_json` | If `openAt` of the token with no associated data at the clock reading is an error, that error; otherwise the `serde_json::from_slice` outcome of the payload, an error mapped to `Deserialization`. | (F); inherited exceptions (K), (H), (J) | [`…RequestStateCodec.open_json`](Specs/Model/RequestState.lean) |
| R14 | `RequestStateCodec::open_json_with` | As R13, with associated data `ad`. | (T), (F); inherited exceptions (K), (H), (V), (J) | [`…RequestStateCodec.open_json_with`](Specs/Model/RequestState.lean) |
| R15 | `RequestStateCodec::new_with_keyring` | `Err` exactly when the Rust checks reject the entries or the active id (`keyringCheck`), with the exact error of the first failure in the Rust order (per entry: empty id, id over 255 bytes, key under 32 bytes, duplicate id; then no entry, active id invalid, active id absent). Otherwise `Ok` of a keyring with exactly the configured keys (ids up to order), seal mode `Rs2 { key_id: active }`, no rs1 fallback, satisfying `CodecValid`. | caller code (iterator, conversions), (U); inherited exceptions (I), (P), (N) | [`…RequestStateCodec.new_with_keyring`](Specs/Model/RequestState.lean) |

## Internal guarantees

Statements about functions that are not public rmcp API. "Used by" names the public functions or
features whose code calls them (from `crates/rmcp/src`, or the patched copy for Phase 1); those
callers are **not** verified, so the guarantee covers only the called function. Where one caller
covers every row of a section, the section says it once and the table has no "Used by" column.
Every row about a call also says that it does not panic.

**Model, crate-internal** — [`Internal/Model.lean`](../proofs/Proofs/Internal/Model.lean)
(`model.rs`, `pub(crate)`).

| ID | Rust function | Guarantee | Assumptions | Lean theorem | Used by |
| --- | --- | --- | --- | --- | --- |
| M06 | `NumberOrString::numeric_string_value` | `None` for a numeric id; for a string id, the value that `Defs.parseI64` (the `i64::from_str` grammar: optional `+`/`-`, one or more ASCII digits, `i64` range) gives its bytes, `None` if rejected. | none | [`Theorems.model.NumberOrString.numeric_string_value`](../proofs/Proofs/Internal/Model.lean) | matching responses to pending requests in the service loop (`remove_pending_request`) and in the streamable HTTP client |
| M07 | `NumberOrString::matches_response_id` | `true` exactly when the ids are equal, or `self` is `Number(n)` and the response id is a string that `Defs.parseI64` reads as `n`. | none | [`Theorems.model.NumberOrString.matches_response_id`](../proofs/Proofs/Internal/Model.lean) | the client's check of the `initialize` response id |

**SSE event-size limiter** — [`Internal/Transport/Common/ClientSideSse.lean`](../proofs/Proofs/Internal/Transport/Common/ClientSideSse.lean)
(private struct `SseEventSizeLimiter`). `sat(a + b)` is addition saturating at `usize::MAX`;
"the model" is `Defs.Sse` (line ends CR, LF or CR LF; comment lines start with `:`; an empty
line ends the event). What the limit counts (`Defs.Sse`, "What is counted"): each completed
non-comment line of the current event counts its length + 1, the current line its length so
far; completed comment lines and the blank line that ends the event count 0. This is not the raw
byte size of the event (a CR LF counts 1). Used by (all rows): the SSE event-size limit
`max_sse_event_size` of the reqwest streamable HTTP client
(`transport/common/reqwest/streamable_http_client.rs`, lines 205 and 482) and of the Unix-socket
streamable HTTP client (`transport/common/unix_socket.rs`, lines 384 and 589, feature
`transport-streamable-http-client-unix-socket`), both through `bounded_sse_stream` and
`BoundedSseByteStream` (`async`, not translated).

| ID | Rust function | Guarantee | Assumptions | Lean theorem |
| --- | --- | --- | --- | --- |
| T03 | `observe` | The result and the new state are those of the model: the bytes of the chunk are processed one by one, stopping at the first byte whose step fails the bound check (an LF completing CR LF is not checked). | none | [`Theorems.client_side_sse.SseEventSizeLimiter.observe`](../proofs/Proofs/Internal/Transport/Common/ClientSideSse.lean) |
| T02 | `finish_line` | The new state is the model's `finishLine` of the old one, and the result is T01's verdict on the new state. | none | [`…SseEventSizeLimiter.finish_line`](../proofs/Proofs/Internal/Transport/Common/ClientSideSse.lean) |
| T01 | `check_limit` | `Err(())` exactly when `sat(retained_size + line_size) > max_size`, `Ok(())` otherwise. | none | [`…SseEventSizeLimiter.check_limit`](../proofs/Proofs/Internal/Transport/Common/ClientSideSse.lean) |
| C01 | `observe` on `a ++ b` | Same computation as `observe` on `a` followed, on `Ok(())`, by `observe` on `b` from the state reached; on `Err(())` the same error and state. | none | [`…SseEventSizeLimiter.observe_append`](../proofs/Proofs/Internal/Transport/Common/ClientSideSse.lean) |
| C01 | `observe` (plan form) | `observe` on `a ++ b` is `observe` on `b` from the state after `a`. | `observe` on `a` returned `Ok(())` | [`…SseEventSizeLimiter.observe_append_of_observe_eq_ok`](../proofs/Proofs/Internal/Transport/Common/ClientSideSse.lean) |
| C02 | `observe` | The bound `sat(retained_size + line_size) ≤ max_size` is kept and `max_size` is unchanged. | bound holds before; the call returned `Ok(())` | [`…SseEventSizeLimiter.max_size_eq_and_satAdd_le_of_observe_eq_ok`](../proofs/Proofs/Internal/Transport/Common/ClientSideSse.lean) |
| C02 | `observe` (prefix form) | `observe` on the prefix `a` returns `Ok(())` with a state that keeps `max_size` and the bound. | bound holds before; `observe` on `a ++ b` returned `Ok(())` | [`…exists_observe_eq_ok_and_max_size_eq_and_satAdd_le_of_observe_append_eq_ok`](../proofs/Proofs/Internal/Transport/Common/ClientSideSse.lean) |

**Line codec** — [`Internal/Transport/AsyncRw.lean`](../proofs/Proofs/Internal/Transport/AsyncRw.lean)
(private `fn`s of `async_rw.rs`). Used by (all rows): `AsyncRwTransport::receive` and the
`Decoder` of `JsonRpcMessageCodec`, i.e. the stdio and child-process transports (T04 on every
line; T05/T06 decide, in `should_ignore_notification`, whether a line that fails to deserialize
is dropped). "Core" names: the request and notification names of the official MCP schemas
(`Defs.Methods`, human decision H6), compared byte for byte.

| ID | Rust function | Guarantee | Assumptions | Lean theorem |
| --- | --- | --- | --- | --- |
| T04 | `without_carriage_return` | Drops exactly one trailing `\r` if there is one; otherwise returns the slice unchanged. | none | [`Theorems.async_rw.without_carriage_return`](../proofs/Proofs/Internal/Transport/AsyncRw.lean) |
| T06 | `is_standard_method` | `true` exactly for the core request and notification names, minus the six names the code omits (bug H7). | none | [`Theorems.async_rw.is_standard_method`](../proofs/Proofs/Internal/Transport/AsyncRw.lean) |
| T05 | `is_standard_notification` | `true` exactly for the core notification names, minus those the code omits (bug H7). | none | [`Theorems.async_rw.is_standard_notification`](../proofs/Proofs/Internal/Transport/AsyncRw.lean) |
| C05 | both | A name that `is_standard_notification` accepts, `is_standard_method` accepts. | the first call returned `true` | [`Theorems.async_rw.is_standard_method_of_is_standard_notification`](../proofs/Proofs/Internal/Transport/AsyncRw.lean) |

**Origin check** — [`Internal/Transport/StreamableHttpServer/Tower.lean`](../proofs/Proofs/Internal/Transport/StreamableHttpServer/Tower.lean)
(private `fn` and enum of `tower.rs`). Used by (all rows): `origin_is_allowed`, the `Origin`
check of the DNS-rebinding protection of `StreamableHttpService` (`allowed_origins` of
`StreamableHttpServerConfig`); the origin parsing is not verified.

| ID | Rust function | Guarantee | Assumptions | Lean theorem |
| --- | --- | --- | --- | --- |
| T07 | `default_port` | `Some(80)` for exactly `"http"`, `Some(443)` for exactly `"https"` (case-sensitive bytes), `None` otherwise. | none | [`Theorems.tower.default_port`](../proofs/Proofs/Internal/Transport/StreamableHttpServer/Tower.lean) |
| T08 | `AllowedPort::matches` | `Any` and `Unspecified` match everything; `Exact(p)` matches exactly when the explicit port, or else the scheme's default port (T07), is `p`. | none | [`Theorems.tower.AllowedPort.matches`](../proofs/Proofs/Internal/Transport/StreamableHttpServer/Tower.lean) |

**SSRF address guard** — [`Internal/Transport/Auth.lean`](../proofs/Proofs/Internal/Transport/Auth.lean)
(private associated functions of `AuthorizationManager`). Used by (all rows): the OAuth
metadata-URL SSRF check `is_allowed_metadata_url` (discovery in `AuthorizationManager`) and the
resolved-address filter `AddressClass::of` (`auth/metadata_resolver.rs`); neither is translated.

| ID | Rust function | Guarantee | Assumptions | Lean theorem |
| --- | --- | --- | --- | --- |
| A02 | `is_disallowed_metadata_ipv4` | `true` exactly for addresses in `10/8`, `172.16/12`, `192.168/16`, `127/8`, `169.254/16`, `255.255.255.255`, `0.0.0.0`, `224/4`, `0/8`, `100.64/10`, `198.18/15`; `240.0.0.0/4` is not blocked (bug H8). | none | [`Theorems.auth.AuthorizationManager.is_disallowed_metadata_ipv4`](../proofs/Proofs/Internal/Transport/Auth.lean) |
| A01 | `embedded_ipv4` | `Some` of the IPv4 address carried in IPv4-mapped `::ffff:0:0/96`, NAT64 `64:ff9b::/96`, IPv4-compatible `::/96` (except `::`, `::1`) or 6to4 `2002::/16` form; `None` otherwise. | none | [`…AuthorizationManager.embedded_ipv4`](../proofs/Proofs/Internal/Transport/Auth.lean) |
| A03 | `is_disallowed_metadata_ipv6` | A02's verdict on the carried IPv4 address if A01 finds one; otherwise `true` exactly for `::1`, `::`, `ff00::/8`, `fe80::/10`, `fc00::/7`, `2001::/32`, `64:ff9b:1::/48`. | none | [`…AuthorizationManager.is_disallowed_metadata_ipv6`](../proofs/Proofs/Internal/Transport/Auth.lean) |
| C04 | A01, A03, A02 | `is_disallowed_metadata_ipv6(a)` is the same computation as `is_disallowed_metadata_ipv4(v)`. | `embedded_ipv4(a)` returned `Some(v)` | [`…is_disallowed_metadata_ipv6_eq_of_embedded_ipv4_eq_ok_some`](../proofs/Proofs/Internal/Transport/Auth.lean) |
| C04 | A03 (corollary) | An IPv6 address that writes a blocked IPv4 address in mapped, NAT64, compatible or 6to4 form is blocked. | the IPv4 address is blocked (A02 list); the form | [`…is_disallowed_metadata_ipv6_of_ipv4Disallowed`](../proofs/Proofs/Internal/Transport/Auth.lean) |

**Request-state codec, Phase 1 (patched copy)** —
[`Internal/Model/RequestState.lean`](../proofs/Proofs/Internal/Model/RequestState.lean)
(private associated functions of `RequestStateCodec`; E09a `rs1_fallbacks_verify` exists only in
the patched copy: patch 01 moves the rs1 fallback loop of `open_rs1_at` into it). The callers in
"Used by" are the public wrappers `open`/`open_with` (through `open_at`; verified as R07, R08),
`try_new` (verified as R06), `seal`/`seal_with` (through the private `seal_at`, translated with
patch 03; verified as R09, R10 through R10a) and `new_with_keyring` (verified as R15).
Assumption keys (the same in the file's docstring): **(T)** the MAC transcript fits in
`usize::MAX` bytes; **(C)** the `with_capacity` sum of the token (version, dots, Base64 lengths)
is at most `isize::MAX` bytes, the largest Rust `String` (`ExtModel.maxStringBytes`); **(D)** the
token has fewer than `usize::MAX` dots; **(F)** every rs1 fallback id is a key id: of the codec
(`CodecFallbacksKnown`, a keyring invariant that the keyring constructors establish: R15, R11,
R12 preserve `CodecValid`) for E09 and
E11, of the arguments (`FallbacksKnown`) for E09a; **(R1)**, **(R2)** the round-trip premises in
the S15 rows. `ad` is the associated data. HMAC means HMAC-SHA256 under `key` (opaque model).

| ID | Rust function | Guarantee | Assumptions | Lean theorem | Used by |
| --- | --- | --- | --- | --- | --- |
| E11 | `open_at` | Exactly `Defs.CodecState.openAt`: a token whose first `.`-component is `rs1` goes to E09, `rs2` to E10, anything else gives `MalformedFormat`. | (T); (F) for `rs1` tokens | [`Theorems.request_state.RequestStateCodec.open_at`](../proofs/Proofs/Internal/Model/RequestState.lean) | `open`, `open_with` |
| E07 | `seal_rs1` | Returns `"rs1." + b64(body) + "." + b64(tag)`, `tag` the HMAC of `transcriptV1(ad, body)`. | (T), (C) | [`…RequestStateCodec.seal_rs1`](../proofs/Proofs/Internal/Model/RequestState.lean) | `seal`, `seal_with` |
| E08 | `seal_rs2` | Returns `"rs2." + b64(kid) + "." + b64(body) + "." + b64(tag)`, `tag` the HMAC of `transcriptV2(kid, ad, body)`; any kid is accepted. | (T), (C) | [`…RequestStateCodec.seal_rs2`](../proofs/Proofs/Internal/Model/RequestState.lean) | `seal`, `seal_with` |
| E09 | `open_rs1_at` | Exactly `openRs1`: `MalformedFormat`, `UnknownKeyId` (keyring without rs1 fallback), `InvalidEncoding`, `IntegrityCheckFailed`, in the error order of plan Section 3, then E01 on the body. | (D), (T), (F) | [`…RequestStateCodec.open_rs1_at`](../proofs/Proofs/Internal/Model/RequestState.lean) | `open`, `open_with` |
| E09a | `rs1_fallbacks_verify` (patch-only, no upstream counterpart) | `true` exactly when some rs1 fallback key verifies the tag over the transcript. | (F) (else the code's `expect` panics; not proved) | [`…RequestStateCodec.rs1_fallbacks_verify`](../proofs/Proofs/Internal/Model/RequestState.lean) | `open_rs1_at` (E09) in the patched copy, hence `open`, `open_with` |
| E10 | `open_rs2_at` | Exactly `openRs2` (malformed token, kid checks, unknown kid, encoding, integrity, in the error order of plan Section 3, then E01), for every codec. | (D), (T) | [`…RequestStateCodec.open_rs2_at`](../proofs/Proofs/Internal/Model/RequestState.lean) | `open`, `open_with` |
| E01 | `open_authenticated_body` | `MalformedFormat` below 8 bytes; otherwise `Expired` if the expiry (first 8 bytes, signed big-endian) is non-zero and `now_ms` is later; otherwise `Ok` of the bytes after the first 8. | none | [`…RequestStateCodec.open_authenticated_body`](../proofs/Proofs/Internal/Model/RequestState.lean) | `open`, `open_with` |
| E03 | `validate_key_length` | `Ok(())` exactly when the key has at least 32 bytes, otherwise `KeyTooShort { minimum: 32, actual: key.len() }`. | none | [`…RequestStateCodec.validate_key_length`](../proofs/Proofs/Internal/Model/RequestState.lean) | `try_new`, `new_with_keyring` |
| E04 | `validate_config_kid` | `Ok(())` exactly when the kid has 1 to 255 UTF-8 bytes; `InvalidKeyring` with `KID_EMPTY_MSG` for 0 bytes, with `KID_TOO_LONG_MSG` above 255. | none | [`…RequestStateCodec.validate_config_kid`](../proofs/Proofs/Internal/Model/RequestState.lean) | `new_with_keyring` |
| E02 | `b64_len` | Returns `4 * ((len + 2) / 3)`. | that value fits in `usize` | [`…RequestStateCodec.b64_len`](../proofs/Proofs/Internal/Model/RequestState.lean) | `seal`, `seal_with` |
| S15 | `rs1_roundtrip` | `seal_rs1(key, ad, body)` does not panic, and opening its token (any `str` with its bytes) with `open_rs1_at(self, ·, ad, now_ms)`, with the same associated data `ad`, gives `Ok(body[8..])`. | (R1): (T), (C), body ≥ 8 bytes and not expired at `now_ms`, `key` is the codec's single key or the key of one of its rs1 fallback ids, (F) | [`…RequestStateCodec.rs1_roundtrip`](../proofs/Proofs/Internal/Model/RequestState.lean) | `seal` then `open` |
| S15 | `rs2_roundtrip` | `seal_rs2(kid, key, ad, body)` does not panic, and opening its token (any `str` with its bytes) with `open_rs2_at(self, ·, ad, now_ms)`, with the same associated data `ad`, gives `Ok(body[8..])`. | (R2): (T), (C), body ≥ 8 bytes and not expired at `now_ms`, `kid` is UTF-8 of 1–255 bytes and the codec is a keyring that maps it to `key` | [`…RequestStateCodec.rs2_roundtrip`](../proofs/Proofs/Internal/Model/RequestState.lean) | `seal` then `open` |
| S15 | `open_at_roundtrip_rs1` | As `rs1_roundtrip`, opening with `open_at(self, ·, ad, now_ms)`, with the same associated data `ad`. | (R1) | [`…RequestStateCodec.open_at_roundtrip_rs1`](../proofs/Proofs/Internal/Model/RequestState.lean) | `seal` then `open` |
| S15 | `open_at_roundtrip_rs2` | As `rs2_roundtrip`, opening with `open_at(self, ·, ad, now_ms)`, with the same associated data `ad`. | (R2) | [`…RequestStateCodec.open_at_roundtrip_rs2`](../proofs/Proofs/Internal/Model/RequestState.lean) | `seal` then `open` |
| R10a | `seal_at` (private; translated with patch 03) | At an explicit time `now_ms`, the token's UTF-8 bytes are `Defs.CodecState.sealAt` of the payload, associated data and time-to-live (expiry `now_ms` plus the TTL in whole milliseconds, clamped to `i64`; `rs1` for a single key or an rs1 seal mode, `rs2` otherwise). | the seal-mode key id is a key id; `SealFits` (transcript within `usize::MAX`, capacity within `isize::MAX`); inherited exceptions (H), (V) | [`…RequestStateCodec.seal_at`](../proofs/Proofs/Internal/Model/RequestState.lean) | `seal`, `seal_with` |
| R10b | `seal_at_roundtrip` | `seal_at(self, payload, options, now)` does not panic, and opening its token (any `str` with its bytes) with `open_at(self, ·, ad, now')`, with the same associated data, gives `Ok(payload)`. | `CodecValid`; an rs1 seal-mode id is an rs1 fallback; `SealFits`; not expired at `now'`; inherited exceptions (H), (V) | [`…RequestStateCodec.seal_at_roundtrip`](../proofs/Proofs/Internal/Model/RequestState.lean) | `seal` then `open` |
| — | `openAt_eq_ok_of_sealAt_eq_some` (model round trip, no translated function) | `openAt` of a `sealAt` token with the same associated data at a time where it has not expired is `Ok(payload)`. | `CodecValid`; an rs1 seal-mode id is an rs1 fallback; not expired | [`Theorems.request_state.openAt_eq_ok_of_sealAt_eq_some`](../proofs/Proofs/Internal/Model/RequestState.lean) | — |

**Wire functions, Phase 1 (patch-only)** —
[`Internal/Model/RequestStateWire.lean`](../proofs/Proofs/Internal/Model/RequestStateWire.lean)
(`pub` only in the module `request_state_wire` that patch 01 adds; not upstream API). "Used by"
names the callers in the patched copy (patch 01); through them the wire functions serve seal and
open of request-state tokens. Theorem names are `Theorems.request_state_wire.<function>`.

| ID | Rust function | Guarantee | Assumptions | Lean theorem | Used by |
| --- | --- | --- | --- | --- | --- |
| W01 | `b64_len` | Returns `4 * ((len + 2) / 3)`. | that value fits in `usize` | [`Theorems.request_state_wire.b64_len`](../proofs/Proofs/Internal/Model/RequestStateWire.lean) | `b64_len` (E02): `seal_rs1`, `seal_rs2` (patched copy) |
| W02 | `key_length_ok` | `true` exactly when `len ≥ 32`. | none | [`Theorems.request_state_wire.key_length_ok`](../proofs/Proofs/Internal/Model/RequestStateWire.lean) | `validate_key_length` (E03): `try_new`, `new_with_keyring` (patched copy) |
| W03 | `check_kid_len` | `Err(Empty)` exactly for 0, `Err(TooLong)` exactly above 255, `Ok(())` otherwise. | none | [`Theorems.request_state_wire.check_kid_len`](../proofs/Proofs/Internal/Model/RequestStateWire.lean) | `open_rs2_at`, `validate_config_kid` (patched copy) |
| W04 | `bytes_eq` | `true` exactly when the two slices are equal byte lists. | none | [`Theorems.request_state_wire.bytes_eq`](../proofs/Proofs/Internal/Model/RequestStateWire.lean) | `version_of`, `parse_rs1`, `parse_rs2` (W07–W09) |
| W05 | `next_dot` | The least index `≥ start` holding `.`, or `s.len()` if there is none. | none | [`Theorems.request_state_wire.next_dot`](../proofs/Proofs/Internal/Model/RequestStateWire.lean) | `version_of`, `parse_rs1`, `parse_rs2` (W07–W09) |
| W06 | `component_count` | The number of `.`-separated components, one more than the number of `.` bytes. | fewer than `usize::MAX` dots | [`Theorems.request_state_wire.component_count`](../proofs/Proofs/Internal/Model/RequestStateWire.lean) | `parse_rs1`, `parse_rs2` (W08, W09) |
| W07 | `version_of` | `Some(V1)` exactly when the first component is `rs1`, `Some(V2)` when it is `rs2`, `None` otherwise. | none | [`Theorems.request_state_wire.version_of`](../proofs/Proofs/Internal/Model/RequestStateWire.lean) | `open_at` (E11, patched copy) |
| W08 | `parse_rs1` | `Some {body, tag}` exactly when the token splits on `.` into `["rs1", body, tag]`. | fewer than `usize::MAX` dots | [`Theorems.request_state_wire.parse_rs1`](../proofs/Proofs/Internal/Model/RequestStateWire.lean) | `open_rs1_at` (E09, patched copy) |
| W09 | `parse_rs2` | `Some {kid, body, tag}` exactly when the token splits on `.` into `["rs2", kid, body, tag]`. | fewer than `usize::MAX` dots | [`Theorems.request_state_wire.parse_rs2`](../proofs/Proofs/Internal/Model/RequestStateWire.lean) | `open_rs2_at` (E10, patched copy) |
| W10 | `transcript_v1` | Returns `DOMAIN_V1 ++ be64(len ad) ++ ad ++ body`. | result fits in `usize::MAX` bytes | [`Theorems.request_state_wire.transcript_v1`](../proofs/Proofs/Internal/Model/RequestStateWire.lean) | `seal_rs1`, `open_rs1_at` (E07, E09, patched copy) |
| W11 | `transcript_v2` | Returns `DOMAIN_V2 ++ be64(len kid) ++ kid ++ be64(len ad) ++ ad ++ body`. | result fits in `usize::MAX` bytes | [`Theorems.request_state_wire.transcript_v2`](../proofs/Proofs/Internal/Model/RequestStateWire.lean) | `seal_rs2`, `open_rs2_at` (E08, E10, patched copy) |
| W12 | `decode_expiry` | The signed (two's-complement) big-endian value of the 8 bytes. | none | [`Theorems.request_state_wire.decode_expiry`](../proofs/Proofs/Internal/Model/RequestStateWire.lean) | `open_frame` (W14) |
| W13 | `is_expired` | `true` exactly when `expiry ≠ 0` and `now_ms > expiry`. | none | [`Theorems.request_state_wire.is_expired`](../proofs/Proofs/Internal/Model/RequestStateWire.lean) | `open_frame` (W14) |
| W14 | `open_frame` | `TooShort` below 8 bytes; otherwise `Expired` if W13 holds for the first 8 bytes' value; otherwise `Ok(body[8..])`. | none | [`Theorems.request_state_wire.open_frame`](../proofs/Proofs/Internal/Model/RequestStateWire.lean) | `open_authenticated_body` (E01, patched copy) |
| W15 | `frame` | Returns `be64(expiry as u64) ++ payload`. | result fits in `usize::MAX` bytes | [`Theorems.request_state_wire.frame`](../proofs/Proofs/Internal/Model/RequestStateWire.lean) | `seal_at` (R10a; patched copy): `seal`, `seal_with` |
| — | `frame_roundtrip` | `open_frame(frame(expiry, payload), now_ms)` is `Ok(payload)`. | frame fits in `usize::MAX` bytes; `expiry` is 0 or `now_ms ≤ expiry` | [`Theorems.request_state_wire.frame_roundtrip`](../proofs/Proofs/Internal/Model/RequestStateWire.lean) | `seal_at` then `open_authenticated_body` (patched copy) |

**Laws of the trusted models** — [`Internal/External.lean`](../proofs/Proofs/Internal/External.lean)
(116 theorems `Theorems.External.*`). They state what the models in `formal/trusted/` compute
(Base64url round trip and canonicity, UTF-8, the HMAC/Base64 `prim` functions, `Option`,
`Result`, `str`, `String`, `HashMap`, `zeroize`, slices and ranges, `i64::from_str` equal to
`Defs.parseI64`, `Ipv4Addr`/`Ipv6Addr` predicates), so that a reviewer can compare them with the
Rust documentation. Used by: the proofs of all statements above.

## What you must trust

> - **Tools:** Charon `0.1.324`, Aeneas `nightly-2026.11.24-fb44cb4` and the Lean `v4.36.0`
>   kernel (since the Aeneas upgrade of 2026-11-24, reviewed and re-signed by the spec owner 2026-11-24);
>   the prebuilt Aeneas Lean library (archive digest checked) and Mathlib oleans (not
>   digest-checked).
> - **The translated configuration:** target `x86_64-unknown-linux-gnu`,
>   `--no-default-features --features request-state,server,client,client-side-sse,transport-streamable-http-server,transport-streamable-http-client,auth`,
>   `overflow-checks=true` and `debug-assertions=true` (overflow panics), Rust
>   `nightly-2026-09-17`, the Charon settings in `crates/rmcp/Cargo.toml`. Other targets,
>   features or release builds without overflow checks are not covered.
> - **Translation patch 01** (Phase 1 and R01–R08): the `request_state_wire` refactor on
>   `7caec76`, reviewed and signed off; its equivalence with the unpatched code is tested
>   (regression tests, about 2.9M differential `open` calls), not proved. Phase 2 uses no patch;
>   this rests on `scripts/check-original-linkage.sh` (the committed translation, generated from
>   the patched copy, equals block for block the translation of unmodified `7caec76` for the
>   Phase 2 targets): passes locally, CI pending (S22).
> - **Translation patch 03** (R09–R15): +6/−2 lines on the patch-01 copy (`let ttl = options.ttl;`
>   in `seal_at`, an explicit `match` in place of `.map_err(RequestStateError::Deserialization)`
>   in `open_json_with`), reviewed and signed off 2026-11-24; same computation, covered by the
>   existing tests and the boundary tests of the test-only patch 02, not proved.
> - **The models in [`formal/trusted/`](../trusted/)** of the external functions (standard
>   library, `core::net`, integer parsing, HMAC-SHA256, Base64url, `zeroize`): definitions,
>   structures and seven `opaque` constants (five until translation patch 03), no trusted axiom (`axioms.lock` is empty). They do
>   not appear in `#print axioms`; their fidelity rests on review and their cited sources.
>   Stated exceptions (`formal/trusted/Rmcp/FunsExternal.lean`, module docstring, "Memory" and
>   "Size convention"): the models make no claim about inputs of `2^61` bytes or more, which
>   cannot exist on `x86_64` (address space at most `2^57` bytes); in particular HMAC's
>   bit-length counter overflow (a message of at least `2^61 − 64` bytes or a key of at least
>   `2^61` bytes, equally impossible) and a `Vec` above `isize::MAX` bytes are not modelled;
>   allocation failure is not modelled. For such inputs a statement may promise a result where
>   Rust panics.
>   The models also state representation choices that change no result of the targets (`Arc`
>   equality checks pointer equality first; `Ipv6Addr` as eight segments; `MaybeUninit` partial
>   initialisation; non-UTF-8 `Str` bytes; `HashMap::get` assumes `Hash`/`Eq` agree; the clock is
>   opaque): complete list in [`../docs/STATUS.md`](../docs/STATUS.md), "Stated exceptions of the
>   external models".
> - **The clock** (human decisions 2026-11-24, extended 2026-11-25; [`../README.md`](../README.md),
>   "Trusted base"): the clock is one opaque reading `ExtModel.nowMs`, which makes `open`,
>   `open_with`, `open_json`, `open_json_with`, `seal` and `seal_with` pure in the model. Only
>   their spec theorems (R07–R10, R13, R14), restatements and the corollaries of R08, R09 and R10
>   may name these functions and `ExtModel.nowMs`, and only with the postconditions
>   `resultBytes result = openAt … nowMs` (`open*`), the `openAt … nowMs` error unchanged or else
>   the `from_slice` outcome mapped `Err` → `Deserialization` (`open_json*`), and
>   `sealAt … nowMs = some (utf8 result)` (`seal*`; `sealAt` is the model of `seal_at`); no
>   statement constrains the value of the reading or relates two readings (R10a and R10b use
>   explicit times). The model of
>   `now_ms` always returns, while Rust's `Utc::now` panics for a clock before 1970 or outside
>   chrono's range (exception (K)).
> - **No native-code assumption** since the Aeneas upgrade of 2026-11-24:
>   [`formal/trusted/native-axioms.lock`](../trusted/native-axioms.lock) is empty, because the
>   `toStr` of `nightly-2026.11.24-fb44cb4` checks the length of a string literal in the kernel.
>   Until then 35 were locked: the side conditions of the Aeneas `toStr` of string literals,
>   decided by compiled code (5 for Phase 1, one of which R07, R08 and the R08 corollary also
>   reached; 30 for the method names and `"http"`/`"https"` of T05–T08 and C05).
> - **The translation pin** [`formal/trusted/translation-pins.txt`](../trusted/translation-pins.txt)
>   (S21): the sha256 of the generated `Funs.lean` and the one line where `lean-guard.sh sources`
>   excuses a metaprogramming word (the T06 literal `"initialize"`); a trusted file.
> - **The statements themselves** (this directory, `../proofs/Proofs/Internal/`) and the
>   definitions they use (`Defs/`, `../proofs/Proofs/Defs/`). `Specs` imports `Proofs`, so a
>   reviewer also checks `proofs/` for instances or notation that change a statement's meaning.
>
> Details: [`../docs/STATUS.md`](../docs/STATUS.md), "Trusted base", and
> [`../README.md`](../README.md), "Trusted base".

## Not covered

- The callers of the verified functions: the service loop, the client handshake, the SSE stream
  wrapper `bounded_sse_stream`, `AsyncRwTransport` and `JsonRpcMessageCodec`,
  `origin_is_allowed`, `is_allowed_metadata_url`, `AddressClass::of`,
  `MetadataAddressResolver::is_allowed`.
- URL and HTTP parsing (`Origin` and `Host` headers, `url::Url`), `async` code, DNS resolution.
- 2 of the 17 public functions of `request_state.rs` (status in
  [`../docs/STATUS.md`](../docs/STATUS.md), "Public request_state.rs API"):
  `seal_json`, `seal_json_with` (R16–R17, excluded, blocked upstream: Aeneas does not support the
  mutually recursive `serde_core::ser` traits; once that is fixed they would additionally need the
  variant-constructor workaround of patch 03 hunk 2, since
  `.map_err(RequestStateError::Serialization)` hits "Arrow types are not supported yet" at
  `request_state.rs` 133:4-133:46 / 461:4-468:5 of the patched copy).
- Statements relating two clock readings (for example `seal` then `open` at a later time: R10b
  and the model round trip state it at explicit times only). The codec-state premises (F) and
  `CodecValid` are derived for the codecs the verified constructors build (R04–R06, R15, and
  R11/R12 preserve them), but stay premises of the internal statements.
- Cryptographic security (HMAC unforgeability), constant-time behaviour, the correctness of the
  `hmac`, `sha2`, `base64` and `zeroize` crates; negative round trips (a tampered token is
  rejected).
- Allocation failure, and inputs covered by the stated exceptions above (for those a statement
  may promise a result where Rust panics).
- The full MCP protocol: the method lists are core protocol only (extensions are out of scope),
  and the other functions of the touched files, including those measured and not taken (plan
  Section 16.5).

**Bugs found** (recorded in [`../docs/STATUS.md`, "Bugs found"](../docs/STATUS.md#bugs-found);
the statements describe the code as it is):

- **H7:** `is_standard_method` / `is_standard_notification` (`async_rw.rs`) miss six core MCP
  names (`tasks/get`, `tasks/result`, `tasks/cancel`, `tasks/list`,
  `notifications/tasks/status`, `notifications/elicitation/complete`): when such a line fails
  to deserialize but parses as JSON with a string `method`, it is dropped instead of reported:
  always for the two notifications, and for the four `tasks/*` requests when the line has no
  `id`.
- **H8:** `is_disallowed_metadata_ipv4` (`auth.rs`) does not block the reserved range
  `240.0.0.0/4` (except `255.255.255.255`), so such an address passes the metadata-URL SSRF
  check and the resolved-address filter.
