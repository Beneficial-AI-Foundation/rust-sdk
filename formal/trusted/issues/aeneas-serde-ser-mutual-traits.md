# Translation blocker: `RequestStateCodec::seal_json` and `seal_json_with` (R16–R17)

Status: **open, blocked upstream (Aeneas)**. No upstream issue filed as of 2026-11-25.
Written 2026-11-25 from the project records; not re-measured for this note (see "Evidence and its
limits").

## Affected functions

| ID | Rust item | Upstream line (`crates/rmcp/src/model/request_state.rs`, base `7caec76`) |
|---|---|---|
| R16 | `rmcp::model::request_state::RequestStateCodec::seal_json<T: Serialize>(&self, value: &T) -> Result<String, RequestStateError>` | 461–463 |
| R17 | `rmcp::model::request_state::RequestStateCodec::seal_json_with<T: Serialize>(&self, value: &T, options: &SealOptions<'_>) -> Result<String, RequestStateError>` | 471–478 |

```rust
pub fn seal_json<T: Serialize>(&self, value: &T) -> Result<String, RequestStateError> {
    self.seal_json_with(value, &SealOptions::default())
}

pub fn seal_json_with<T: Serialize>(
    &self,
    value: &T,
    options: &SealOptions<'_>,
) -> Result<String, RequestStateError> {
    let payload = serde_json::to_vec(value).map_err(RequestStateError::Serialization)?;
    Ok(self.seal_with(&payload, options))
}
```

They are the only two of the 17 public functions of `request_state.rs` without a specification
(R01–R15 are specified and proved, `formal/specs/Specs/Model/RequestState.lean`). Both are
excluded from the translation in the Charon settings (`crates/rmcp/Cargo.toml`,
`[package.metadata.charon]`, `exclude`):

```toml
"rmcp::model::request_state::_::seal_json",
"rmcp::model::request_state::_::seal_json_with",
```

Toolchain: Aeneas `nightly-2026.11.24-fb44cb4` (`formal/lakefile.toml`), Charon 0.1.324, Rust
`nightly-2026-09-17`, target `x86_64-unknown-linux-gnu`; translated copy = upstream `7caec76`
plus `formal/trusted/patches/01`–`03`. `serde_core 1.0.229` is pinned; the crate `serde_core` is
`opaque` (signatures and trait declarations only), the facade crate `serde` is `exclude`d.

## Issue 1 (blocking): mutually recursive trait declarations of `serde_core::ser`

**Symptom (recorded).** With the two `exclude` entries removed, Aeneas does not translate the
`serde_core::ser` trait declarations that the bound `T: Serialize` pulls in, because they are
mutually recursive and Aeneas does not support mutually recursive trait declarations (records:
`formal/docs/STATUS.md` "Amendment (translation patch 03 v2, 2026-11-24)", plan
`docs/MCP_SDK_Verification_Master_Plan_EN.md` Section 9 amendment, blocker B9 "narrowed").

**Cause.** The `Serialize` / `Serializer` traits of `serde_core::ser` refer to each other through
method-level bounds (paraphrased, see `serde_core-1.0.229/src/ser/mod.rs`):

```rust
pub trait Serialize {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error>;
}

pub trait Serializer: Sized {
    type Ok;
    type Error: Error;
    type SerializeSeq: SerializeSeq<Ok = Self::Ok, Error = Self::Error>;
    // … six more associated compound-serializer types …
    fn serialize_some<T: ?Sized + Serialize>(self, value: &T) -> Result<Self::Ok, Self::Error>;
    fn serialize_newtype_struct<T: ?Sized + Serialize>(/* … */) -> Result<Self::Ok, Self::Error>;
    // …
}

pub trait SerializeSeq {
    type Ok; type Error: Error;
    fn serialize_element<T: ?Sized + Serialize>(&mut self, value: &T) -> Result<(), Self::Error>;
    // …
}
```

`Serialize` needs `Serializer`, `Serializer` (and its associated `SerializeSeq`, `SerializeMap`,
… traits) need `Serialize`: one strongly connected group of trait declarations. Because
`serde_core` is `opaque`, Charon still emits these trait *declarations* (that is what made
`DeserializeOwned` available for `open_json`/`open_json_with`), and Aeneas then has to translate
the group, which it cannot.

**What does not work around it on our side.**
- `exclude`ing `serde_core` removes the trait the signature needs ("Could not find:
  trait_decl_id", measured for the `Deserialize` side when patch 03 was made).
- A translation patch cannot remove the bound: `T: Serialize` is the public signature, and
  `serde_json::to_vec` requires it.

## Issue 2 (latent, appears once Issue 1 is fixed): variant constructor used as a function

`.map_err(RequestStateError::Serialization)` passes the enum variant constructor as an
`FnOnce`. Aeneas fails on the `FnOnce` impl rustc generates for it: **"[Error] Arrow types are
not supported yet"** followed by "[Error] Internal error: please file an issue" (recorded at
`request_state.rs` 133:4–133:46 and 461:4–468:5 of the patched copy). The same error on
`open_json_with` (`RequestStateError::Deserialization`) is worked around by hunk 2 of
`formal/trusted/patches/03-request-state-public.patch`; `seal_json_with` would need the same
behaviour-preserving rewrite:

```rust
let payload = match serde_json::to_vec(value) {
    Ok(payload) => payload,
    Err(error) => return Err(RequestStateError::Serialization(error)),
};
```

(A closure `|e| RequestStateError::Serialization(e)` is not used because clippy's
`redundant_closure` lint rejects it.) This one is reportable to Aeneas independently of Issue 1.

## Evidence and its limits

- Recorded in: `formal/docs/STATUS.md` (sections "Amendment (translation patch 03 v2,
  2026-11-24)" and the 2026-11-24 update), plan Section 2.3 table and Section 9 amendment (B9),
  the header of `formal/trusted/patches/03-request-state-public.patch`, and the comments in
  `crates/rmcp/Cargo.toml`.
- The minimal reproducers made on 2026-11-24 were kept outside the repository and are lost; the
  exact Aeneas error text and source location for Issue 1 were not preserved. Issue 2's text is
  recorded verbatim above.
- Open question for whoever reproduces: the `serde_core::de` side (`Deserialize` /
  `Deserializer` / `Visitor` / `SeqAccess`) also has cyclic method bounds, yet `open_json` and
  `open_json_with` translate with only `DeserializeOwned` in their signatures. Which part of the
  `ser` group (associated types with trait bounds on `Serializer`? the `T: ?Sized + Serialize`
  method bounds?) triggers the failure should be confirmed and stated in the upstream report.

## How to reproduce (in a scratch copy, never in `crates/`)

1. In a scratch clone, delete the two `seal_json*` lines from `exclude` in
   `crates/rmcp/Cargo.toml` (`[package.metadata.charon]`).
2. Run `scripts/aeneas-translate.sh` with `RMCP_TRANSLATION_DEST` pointing to a scratch directory
   (the script refuses destinations holding anything other than a translation output).
3. Record the Charon and Aeneas logs: the Issue 1 error, then (after adding the rewrite above as
   a scratch patch) check whether only Issue 1 remains.
4. For the upstream report, reduce to a standalone crate: two traits `A { fn f<B: Bt>(&self, b: B); }`
   and `Bt { type S: Ct; fn g<T: ?Sized + A>(self, t: &T); }` plus `Ct { fn h<T: ?Sized + A>(&mut self, t: &T); }`,
   and one generic function `fn use_it<T: A>(t: &T)`; run Charon and Aeneas on it.

## What is needed to verify R16–R17 once Aeneas supports it

1. Upstream: Aeneas support for mutually recursive trait declarations (Issue 1); optionally the
   `FnOnce`-of-variant-constructor fix (Issue 2), else a patch-03-style hunk.
2. Charon settings: remove the two `exclude` entries (reviewed trust-base change).
3. A new opaque outcome model for `serde_json::to_vec::<T>` (analogous to
   `ExtModel.serdeJsonFromSlice`, `formal/trusted/evidence/README.md`), with a review rule that no
   statement relates two calls or states its value.
4. Specs R16/R17 through the spec cycle: the error of `to_vec` mapped to `Serialization`, else
   exactly R10 (`seal_with`) on the encoded payload (`seal_json` with default options = R09).

## Draft upstream issue (AeneasVerif/aeneas)

> **Title:** Mutually recursive trait declarations (serde `Serialize`/`Serializer`) are not supported
>
> Translating a function with a bound `T: serde::Serialize` (here `serde_json::to_vec(value)`
> inside a crate whose `serde_core` dependency is marked `opaque` in Charon) fails because the
> trait declarations `Serialize`, `Serializer`, `SerializeSeq`, … form a mutually recursive group
> (each `Serializer` method is generic over `T: ?Sized + Serialize`, and
> `Serialize::serialize` is generic over `S: Serializer`). Versions: Aeneas
> nightly-2026.11.24-fb44cb4, Charon 0.1.324, rustc nightly-2026-09-17. Minimal reproducer: <attach>.
> Expected: the trait group is translated (e.g. as mutually defined structures) or the opaque
> declarations are emitted without bodies so that signatures referencing them can be translated.
>
> Related: passing an enum variant constructor as a function (`.map_err(MyError::Variant)`)
> fails with "Arrow types are not supported yet" / "Internal error: please file an issue" on the
> generated `FnOnce` impl.

(Before filing: attach the reproducer and the exact error output from step 3; do not include
project-private details.)
