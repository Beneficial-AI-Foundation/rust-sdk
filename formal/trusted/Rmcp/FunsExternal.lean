/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Aeneas
import Rmcp.Types

/-!
External functions of the `rmcp` translation (`Rmcp.Funs` imports this module).

Started at plan step S04a from the template that Aeneas generated
(`formal/translation/Rmcp/FunsExternal_Template.lean`) for the translation of commit
`14d2830` with the Charon settings of S04a part 2 (derived `Debug` impls excluded), Aeneas
`nightly-2026.08.20-5d08da4`. Every declaration below is the placeholder `axiom` of the
template, with the name, signature and doc comment Aeneas generated.

Plan steps S08 (HMAC and Base64 `prim` functions) and S09 (standard-library models, `HashMap`,
the external types) replace or remove them: functions become exact models or `ok` of opaque
values, as plan Section 4 requires, and types become reviewed opaque types or definitions.
None of them is reviewed or trusted yet.
-/
open Aeneas Aeneas.Std Result ControlFlow Error
open rmcp

/-- [core::borrow::{impl core::borrow::Borrow<T> for T}::borrow]:
    Source: '/rustc/library/core/src/borrow.rs', lines 214:4-214:26
    Name pattern: [core::borrow::{core::borrow::Borrow<@T, @T>}::borrow]
    Visibility: public -/
@[rust_fun "core::borrow::{core::borrow::Borrow<@T, @T>}::borrow"]
axiom core.borrow.Borrow.Blanket.borrow {T : Type} : T → Result T

/-- [core::option::{core::option::Option<T>}::ok_or]:
    Source: '/rustc/library/core/src/option.rs', lines 1334:4-1334:73
    Name pattern: [core::option::{core::option::Option<@T>}::ok_or]
    Visibility: public -/
@[rust_fun "core::option::{core::option::Option<@T>}::ok_or"]
axiom core.option.Option.ok_or
  {T : Type} {E : Type} : Option T → E → Result (core.result.Result T E)

/-- [core::option::{impl core::default::Default for core::option::Option<T>}::default]:
    Source: '/rustc/library/core/src/option.rs', lines 2313:4-2313:29
    Name pattern: [core::option::{core::default::Default<core::option::Option<@T>>}::default]
    Visibility: public -/
@[rust_fun
  "core::option::{core::default::Default<core::option::Option<@T>>}::default"]
axiom core.option.Option.Insts.CoreDefaultDefault.default
  (T : Type) : Result (Option T)

/-- [core::result::{core::result::Result<T, E>}::is_err]:
    Source: '/rustc/library/core/src/result.rs', lines 646:4-646:38
    Name pattern: [core::result::{core::result::Result<@T, @E>}::is_err]
    Visibility: public -/
@[rust_fun "core::result::{core::result::Result<@T, @E>}::is_err"]
axiom core.result.Result.is_err
  {T : Type} {E : Type} : core.result.Result T E → Result Bool

/-- [core::result::{core::result::Result<T, E>}::map_err]:
    Source: '/rustc/library/core/src/result.rs', lines 962:4-964:53
    Name pattern: [core::result::{core::result::Result<@T, @E>}::map_err]
    Visibility: public -/
@[rust_fun "core::result::{core::result::Result<@T, @E>}::map_err"]
axiom core.result.Result.map_err
  {T : Type} {E : Type} {F : Type} {O : Type} (opsfunctionFnOnceOTupleEFInst :
  core.ops.function.FnOnce O E F) :
  core.result.Result T E → O → Result (core.result.Result T F)

/-- [core::slice::{impl core::default::Default for &'_0 [T]}::default]:
    Source: '/rustc/library/core/src/slice/mod.rs', lines 5637:4-5637:24
    Name pattern: [core::slice::{core::default::Default<&'0 [@T]>}::default]
    Visibility: public -/
@[rust_fun "core::slice::{core::default::Default<&'0 [@T]>}::default"]
axiom Shared0Slice.Insts.CoreDefaultDefault.default
  (T : Type) : Result (Slice T)

/-- [core::str::{str}::len]:
    Source: '/rustc/library/core/src/str/mod.rs', lines 153:4-153:36
    Name pattern: [core::str::{str}::len]
    Visibility: public -/
@[rust_fun "core::str::{str}::len"]
axiom core.str.Str.len : Str → Result Std.Usize

/-- [core::str::{str}::as_bytes]:
    Source: '/rustc/library/core/src/str/mod.rs', lines 498:4-498:41
    Name pattern: [core::str::{str}::as_bytes]
    Visibility: public -/
@[rust_fun "core::str::{str}::as_bytes"]
axiom core.str.Str.as_bytes : Str → Result (Slice Std.U8)

/-- [std::collections::hash::map::{std::collections::hash::map::HashMap<K, V, S, A>}::get]:
    Source: '/rustc/library/std/src/collections/hash/map.rs', lines 1035:4-1038:21
    Name pattern: [std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, @S, @A>}::get]
    Visibility: public -/
@[rust_fun
  "std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, @S, @A>}::get"]
axiom std.collections.hash.map.HashMap.get
  {K : Type} {V : Type} {S : Type} {A : Type} {Q : Type} {Clause2_Hasher :
  Type} (corecmpEqInst : core.cmp.Eq K) (corehashHashInst : core.hash.Hash K)
  (corehashBuildHasherInst : core.hash.BuildHasher S Clause2_Hasher)
  (coreborrowBorrowInst : core.borrow.Borrow K Q) (corehashHashInst1 :
  core.hash.Hash Q) (corecmpEqInst1 : core.cmp.Eq Q) :
  std.collections.hash.map.HashMap K V S A → Q → Result (Option V)

/-- [std::collections::hash::map::{impl core::clone::Clone for std::collections::hash::map::HashMap<K, V, S, A>}::clone]:
    Source: '/rustc/library/std/src/collections/hash/map.rs', lines 1438:4-1438:27
    Name pattern: [std::collections::hash::map::{core::clone::Clone<std::collections::hash::map::HashMap<@K, @V, @S, @A>>}::clone]
    Visibility: public -/
@[rust_fun
  "std::collections::hash::map::{core::clone::Clone<std::collections::hash::map::HashMap<@K, @V, @S, @A>>}::clone"]
axiom std.collections.hash.map.HashMap.Insts.CoreCloneClone.clone
  {K : Type} {V : Type} {S : Type} {A : Type} (corecloneCloneInst :
  core.clone.Clone K) (corecloneCloneInst1 : core.clone.Clone V)
  (corecloneCloneInst2 : core.clone.Clone S) (corecloneCloneInst3 :
  core.clone.Clone A) :
  std.collections.hash.map.HashMap K V S A → Result
    (std.collections.hash.map.HashMap K V S A)

/-- [std::hash::random::{impl core::clone::Clone for std::hash::random::RandomState}::clone]:
    Source: '/rustc/library/std/src/hash/random.rs', lines 34:9-34:14
    Name pattern: [std::hash::random::{core::clone::Clone<std::hash::random::RandomState>}::clone]
    Visibility: public -/
@[rust_fun
  "std::hash::random::{core::clone::Clone<std::hash::random::RandomState>}::clone"]
axiom std.hash.random.RandomState.Insts.CoreCloneClone.clone
  : std.hash.random.RandomState → Result std.hash.random.RandomState

/-- [std::hash::random::{impl core::hash::Hasher for std::hash::random::DefaultHasher}::finish]:
    Source: '/rustc/library/std/src/hash/random.rs', lines 140:4-140:27
    Name pattern: [std::hash::random::{core::hash::Hasher<std::hash::random::DefaultHasher>}::finish]
    Visibility: public -/
@[rust_fun
  "std::hash::random::{core::hash::Hasher<std::hash::random::DefaultHasher>}::finish"]
axiom std.hash.random.DefaultHasher.Insts.CoreHashHasher.finish
  : std.hash.random.DefaultHasher → Result Std.U64

/-- [std::hash::random::{impl core::hash::Hasher for std::hash::random::DefaultHasher}::write]:
    Source: '/rustc/library/std/src/hash/random.rs', lines 130:4-130:35
    Name pattern: [std::hash::random::{core::hash::Hasher<std::hash::random::DefaultHasher>}::write]
    Visibility: public -/
@[rust_fun
  "std::hash::random::{core::hash::Hasher<std::hash::random::DefaultHasher>}::write"]
axiom std.hash.random.DefaultHasher.Insts.CoreHashHasher.write
  :
  std.hash.random.DefaultHasher → Slice Std.U8 → Result
    std.hash.random.DefaultHasher

/-- [std::hash::random::{impl core::hash::BuildHasher<std::hash::random::DefaultHasher> for std::hash::random::RandomState}::build_hasher]:
    Source: '/rustc/library/std/src/hash/random.rs', lines 83:4-83:43
    Name pattern: [std::hash::random::{core::hash::BuildHasher<std::hash::random::RandomState, std::hash::random::DefaultHasher>}::build_hasher]
    Visibility: public -/
@[rust_fun
  "std::hash::random::{core::hash::BuildHasher<std::hash::random::RandomState, std::hash::random::DefaultHasher>}::build_hasher"]
axiom
  std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher.build_hasher
  : std.hash.random.RandomState → Result std.hash.random.DefaultHasher

/-- [alloc::string::{impl core::cmp::PartialEq<alloc::string::String> for alloc::string::String}::eq]:
    Source: '/rustc/library/alloc/src/string.rs', lines 350:9-350:18
    Name pattern: [alloc::string::{core::cmp::PartialEq<alloc::string::String, alloc::string::String>}::eq]
    Visibility: public -/
@[rust_fun
  "alloc::string::{core::cmp::PartialEq<alloc::string::String, alloc::string::String>}::eq"]
axiom alloc.string.String.Insts.CoreCmpPartialEqString.eq
  : String → String → Result Bool

/-- [alloc::string::{impl core::cmp::Eq for alloc::string::String}::assert_fields_are_eq]:
    Source: '/rustc/library/alloc/src/string.rs', lines 350:32-350:34
    Name pattern: [alloc::string::{core::cmp::Eq<alloc::string::String>}::assert_fields_are_eq]
    Visibility: public -/
@[rust_fun
  "alloc::string::{core::cmp::Eq<alloc::string::String>}::assert_fields_are_eq"]
axiom alloc.string.String.Insts.CoreCmpEq.assert_fields_are_eq
  : String → Result Unit

/-- [alloc::string::{alloc::string::String}::with_capacity]:
    Source: '/rustc/library/alloc/src/string.rs', lines 493:4-493:51
    Name pattern: [alloc::string::{alloc::string::String}::with_capacity]
    Visibility: public -/
@[rust_fun "alloc::string::{alloc::string::String}::with_capacity"]
axiom alloc.string.String.with_capacity : Std.Usize → Result String

/-- [alloc::string::{alloc::string::String}::from_utf8]:
    Source: '/rustc/library/alloc/src/string.rs', lines 569:4-569:67
    Name pattern: [alloc::string::{alloc::string::String}::from_utf8]
    Visibility: public -/
@[rust_fun "alloc::string::{alloc::string::String}::from_utf8"]
axiom alloc.string.String.from_utf8
  :
  alloc.vec.Vec Std.U8 → Result (core.result.Result String
    alloc.string.FromUtf8Error)

/-- [alloc::string::{alloc::string::String}::push_str]:
    Source: '/rustc/library/alloc/src/string.rs', lines 1110:4-1110:44
    Name pattern: [alloc::string::{alloc::string::String}::push_str]
    Visibility: public -/
@[rust_fun "alloc::string::{alloc::string::String}::push_str"]
axiom alloc.string.String.push_str : String → Str → Result String

/-- [alloc::string::{alloc::string::String}::push]:
    Source: '/rustc/library/alloc/src/string.rs', lines 1425:4-1425:36
    Name pattern: [alloc::string::{alloc::string::String}::push]
    Visibility: public -/
@[rust_fun "alloc::string::{alloc::string::String}::push"]
axiom alloc.string.String.push : String → Char → Result String

/-- [alloc::string::{alloc::string::String}::as_bytes]:
    Source: '/rustc/library/alloc/src/string.rs', lines 1454:4-1454:41
    Name pattern: [alloc::string::{alloc::string::String}::as_bytes]
    Visibility: public -/
@[rust_fun "alloc::string::{alloc::string::String}::as_bytes"]
axiom alloc.string.String.as_bytes : String → Result (Slice Std.U8)

/-- [alloc::string::{impl core::clone::Clone for alloc::string::String}::clone]:
    Source: '/rustc/library/alloc/src/string.rs', lines 2364:4-2364:27
    Name pattern: [alloc::string::{core::clone::Clone<alloc::string::String>}::clone]
    Visibility: public -/
@[rust_fun "alloc::string::{core::clone::Clone<alloc::string::String>}::clone"]
axiom alloc.string.String.Insts.CoreCloneClone.clone : String → Result String

/-- [alloc::string::{impl core::hash::Hash for alloc::string::String}::hash]:
    Source: '/rustc/library/alloc/src/string.rs', lines 2740:4-2740:51
    Name pattern: [alloc::string::{core::hash::Hash<alloc::string::String>}::hash]
    Visibility: public -/
@[rust_fun "alloc::string::{core::hash::Hash<alloc::string::String>}::hash"]
axiom alloc.string.String.Insts.CoreHashHash.hash
  {H : Type} (corehashHasherInst : core.hash.Hasher H) :
  String → H → Result H

/-- [alloc::vec::{alloc::vec::Vec<T>}::is_empty]:
    Source: '/rustc/library/alloc/src/vec/mod.rs', lines 3085:4-3085:40
    Name pattern: [alloc::vec::{alloc::vec::Vec<@T>}::is_empty]
    Visibility: public -/
@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::is_empty"]
axiom alloc.vec.Vec.is_empty
  {T : Type} (A : Type) : alloc.vec.Vec T → Result Bool

/-- [zeroize::{impl zeroize::Zeroize for Z}::zeroize]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/zeroize-1.9.2/src/lib.rs', lines 282:4-282:25
    Name pattern: [zeroize::{zeroize::Zeroize<@Z>}::zeroize]
    Visibility: public -/
@[rust_fun "zeroize::{zeroize::Zeroize<@Z>}::zeroize"]
axiom zeroize.Zeroize.Blanket.zeroize
  {Z : Type} (DefaultIsZeroesInst : zeroize.DefaultIsZeroes Z) : Z → Result Z

/-- [zeroize::{impl zeroize::Zeroize for alloc::vec::Vec<Z>}::zeroize]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/zeroize-1.9.2/src/lib.rs', lines 505:4-505:25
    Name pattern: [zeroize::{zeroize::Zeroize<alloc::vec::Vec<@Z>>}::zeroize]
    Visibility: public -/
@[rust_fun "zeroize::{zeroize::Zeroize<alloc::vec::Vec<@Z>>}::zeroize"]
axiom alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize
  {Z : Type} (ZeroizeInst : zeroize.Zeroize Z) :
  alloc.vec.Vec Z → Result (alloc.vec.Vec Z)

/-- [zeroize::{zeroize::Zeroizing<Z>}::new]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/zeroize-1.9.2/src/lib.rs', lines 599:4-599:32
    Name pattern: [zeroize::{zeroize::Zeroizing<@Z>}::new]
    Visibility: public -/
@[rust_fun "zeroize::{zeroize::Zeroizing<@Z>}::new"]
axiom zeroize.Zeroizing.new
  {Z : Type} (ZeroizeInst : zeroize.Zeroize Z) :
  Z → Result (zeroize.Zeroizing Z)

/-- [zeroize::{impl core::clone::Clone for zeroize::Zeroizing<Z>}::clone]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/zeroize-1.9.2/src/lib.rs', lines 606:4-606:27
    Name pattern: [zeroize::{core::clone::Clone<zeroize::Zeroizing<@Z>>}::clone]
    Visibility: public -/
@[rust_fun "zeroize::{core::clone::Clone<zeroize::Zeroizing<@Z>>}::clone"]
axiom zeroize.Zeroizing.Insts.CoreCloneClone.clone
  {Z : Type} (ZeroizeInst : zeroize.Zeroize Z) (corecloneCloneInst :
  core.clone.Clone Z) :
  zeroize.Zeroizing Z → Result (zeroize.Zeroizing Z)

/-- [zeroize::{impl core::ops::deref::Deref<Z> for zeroize::Zeroizing<Z>}::deref]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/zeroize-1.9.2/src/lib.rs', lines 634:4-634:25
    Name pattern: [zeroize::{core::ops::deref::Deref<zeroize::Zeroizing<@Z>, @Z>}::deref]
    Visibility: public -/
@[rust_fun
  "zeroize::{core::ops::deref::Deref<zeroize::Zeroizing<@Z>, @Z>}::deref"]
axiom zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
  {Z : Type} (ZeroizeInst : zeroize.Zeroize Z) :
  zeroize.Zeroizing Z → Result Z

/-- [rmcp::model::request_state::{rmcp::model::request_state::RequestStateCodec}::now_ms]:
    Source: 'crates/rmcp/src/model/request_state.rs', lines 729:4-731:5 -/
axiom model.request_state.RequestStateCodec.now_ms : Result Std.I64

/-- [rmcp::model::request_state_wire::prim::b64_decode]:
    Source: 'crates/rmcp/src/model/request_state_wire.rs', lines 274:4-276:5
    Visibility: public -/
axiom model.request_state_wire.prim.b64_decode
  : Slice Std.U8 → Result (Option (alloc.vec.Vec Std.U8))

/-- [rmcp::model::request_state_wire::prim::hmac_sha256_verify]:
    Source: 'crates/rmcp/src/model/request_state_wire.rs', lines 261:4-266:5
    Visibility: public -/
axiom model.request_state_wire.prim.hmac_sha256_verify
  : Slice Std.U8 → Slice Std.U8 → Slice Std.U8 → Result Bool

/-- [rmcp::model::request_state_wire::prim::b64_encode_into]:
    Source: 'crates/rmcp/src/model/request_state_wire.rs', lines 269:4-271:5
    Visibility: public -/
axiom model.request_state_wire.prim.b64_encode_into
  : Slice Std.U8 → String → Result String

/-- [rmcp::model::request_state_wire::prim::hmac_sha256]:
    Source: 'crates/rmcp/src/model/request_state_wire.rs', lines 253:4-258:5
    Visibility: public -/
axiom model.request_state_wire.prim.hmac_sha256
  : Slice Std.U8 → Slice Std.U8 → Result (Array Std.U8 32#usize)

