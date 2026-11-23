/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Aeneas

/-!
External types of the `rmcp` translation (`Rmcp.Types` imports this module).

Started at plan step S04a from the template that Aeneas generated
(`formal/translation/Rmcp/TypesExternal_Template.lean`) for the translation of commit
`9b030c6` with the Charon settings of S04a part 2 (derived `Debug` impls excluded), Aeneas
`nightly-2026.08.20-5d08da4`. Plan steps S08–S09 replaced every placeholder of the template:
each type is now a `structure` that models the fields of the Rust type; the one field that
no translated code and no model looks inside (`serde_json`'s boxed `ErrorImpl`) has an
`opaque` type. This module declares no axiom.

The `@[rust_type]` names and the source lines in the docstrings are those Aeneas generated.
Source paths: `/rustc/library/…` is the `rust-src` of the pinned toolchain `nightly-2026-06-01`;
`/cargo/registry/…` is the crate at the version in the path. The justification of each model is
also recorded in `formal/trusted/evidence/README.md`.
-/
open Aeneas Aeneas.Std Result ControlFlow Error

/-- [core::time::Duration]
    Source: '/rustc/library/core/src/time.rs', lines 81:0-81:19

**Model: the two fields of the Rust struct** `pub struct Duration { secs: u64, nanos:
Nanoseconds }` (`time.rs` lines 81–84), with its documented invariant `nanos < 10^9` ("Always
0 <= nanos < NANOS_PER_SEC"; `Nanoseconds` is a `u32` restricted to that range). Used only by
the non-target `SealOptions::ttl : Option<Duration>`; no target and no external model reads
one. -/
@[rust_type "core::time::Duration"]
structure core.time.Duration : Type where
  /-- Whole seconds. -/
  secs : Std.U64
  /-- Sub-second nanoseconds. -/
  nanos : Std.U32
  /-- `nanos < NANOS_PER_SEC`. -/
  nanos_lt : nanos.val < 1000000000

/-- [std::collections::hash::map::HashMap]
    Source: '/rustc/library/std/src/collections/hash/map.rs', lines 246:0-251:1

**Model: association list.** `entries` lists the key-value pairs of the map; `hash_builder`
is the `S` value the Rust map stores and `alloc` the allocator of its table (std wraps
`hashbrown::HashMap { hash_builder: S, table: RawTable<(K, V), A> }`, hashbrown 0.17.1 as
pinned by the toolchain's `library/Cargo.lock`, `src/map.rs`). The order of `entries` carries
no meaning: the translated code only calls `get` and `clone`, which do not reveal the table
order.

The Rust invariant "no two keys are equal" is not part of the type: a generic `clone` could not
preserve a proof of it (`K::clone` is an arbitrary function), and no translated function
constructs a map (the constructors are excluded, plan Section 2.3). A statement that needs it
takes it as a hypothesis (the codec-state invariant, plan Section 4).
`std.collections.hash.map.HashMap.get` returns the value of the first entry whose key equals
the query, which is the Rust result whenever the keys are pairwise distinct. -/
@[rust_type "std::collections::hash::map::HashMap"]
structure std.collections.hash.map.HashMap (K : Type) (V : Type) (S : Type) (A : Type) :
    Type where
  /-- The `BuildHasher` value of the map (`hash_builder` in hashbrown). -/
  hash_builder : S
  /-- The allocator of the table. -/
  alloc : A
  /-- The key-value pairs. -/
  entries : List (K × V)

/-- [std::hash::random::RandomState]
    Source: '/rustc/library/std/src/hash/random.rs', lines 35:0-35:22

**Model: the two fields of the Rust struct** `pub struct RandomState { k0: u64, k1: u64 }`
(`random.rs` lines 35–38), the SipHash keys. -/
@[rust_type "std::hash::random::RandomState"]
structure std.hash.random.RandomState : Type where
  /-- First SipHash key. -/
  k0 : Std.U64
  /-- Second SipHash key. -/
  k1 : Std.U64

/-- [std::hash::random::DefaultHasher]
    Source: '/rustc/library/std/src/hash/random.rs', lines 94:0-94:24

**Model: the keys and the bytes written so far.** The Rust value is
`DefaultHasher(SipHasher13)` (`random.rs` line 94). `SipHasher13` treats successive `write`
calls as one byte stream, and `finish` depends only on the keys and that stream
(`core/src/hash/sip.rs`, `impl Hasher for Hasher<S>`). The state is therefore modelled as the
keys and the concatenation of the written bytes; `finish` applies the opaque function
`ExtModel.sipHash13` (`Rmcp.FunsExternal`). -/
@[rust_type "std::hash::random::DefaultHasher"]
structure std.hash.random.DefaultHasher : Type where
  /-- First SipHash key. -/
  k0 : Std.U64
  /-- Second SipHash key. -/
  k1 : Std.U64
  /-- All bytes written so far, in order. -/
  written : List Std.U8

/-- [alloc::string::FromUtf8Error]
    Source: '/rustc/library/alloc/src/string.rs', lines 391:0-391:24

**Model: the `bytes` field.** The Rust struct is `FromUtf8Error { bytes: Vec<u8>, error:
Utf8Error }` (`string.rs` lines 391–394). The `error` field (the position of the first invalid
sequence) is not modelled: no translated code reads it (its only use, in `open_rs2_at`, maps
the error to `RequestStateError::InvalidKeyId` without inspecting it). -/
@[rust_type "alloc::string::FromUtf8Error"]
structure alloc.string.FromUtf8Error : Type where
  /-- The bytes that `String::from_utf8` rejected. -/
  bytes : alloc.vec.Vec Std.U8

/-- The content of a `serde_json` error (`serde_json-1.0.154/src/error.rs`, `struct ErrorImpl`
behind the `Box`). **Opaque**: no translated function and no external model creates or inspects
one. -/
opaque ExtModel.SerdeJsonErrorImpl : Type

/-- [serde_json::error::Error]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/serde_json-1.0.154/src/error.rs', lines 17:0-17:16

**Model: the one field of the Rust struct** `pub struct Error { err: Box<ErrorImpl> }`
(`error.rs` lines 17–22), with the boxed content opaque (`ExtModel.SerdeJsonErrorImpl`). It
occurs only as the payload of `RequestStateError::{Serialization, Deserialization}`. -/
@[rust_type "serde_json::error::Error"]
structure serde_json.error.Error : Type where
  /-- The boxed error content. -/
  err : ExtModel.SerdeJsonErrorImpl

/-- [zeroize::Zeroizing]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/zeroize-1.9.2/src/lib.rs', lines 584:0-584:41

**Model: a wrapper around the value.** The Rust type is the `repr(transparent)` tuple struct
`pub struct Zeroizing<Z: Zeroize + ?Sized>(Z)` (`lib.rs` lines 582–584). Its `Drop` impl,
which zeroizes the value when it goes out of scope, has no counterpart in the value model
(plan Section 4: zeroisation on drop is not established). -/
@[rust_type "zeroize::Zeroizing"]
structure zeroize.Zeroizing (Z : Type) : Type where
  /-- The wrapped value (the tuple field `.0`). -/
  inner : Z
