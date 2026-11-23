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
`14d2830` with the Charon settings of S04a part 2 (derived `Debug` impls excluded), Aeneas
`nightly-2026.08.20-5d08da4`. Every declaration below is the placeholder `axiom` of the
template, with the name, signature and doc comment Aeneas generated.

Plan steps S08 (HMAC and Base64 `prim` functions) and S09 (standard-library models, `HashMap`,
the external types) replace or remove them: functions become exact models or `ok` of opaque
values, as plan Section 4 requires, and types become reviewed opaque types or definitions.
None of them is reviewed or trusted yet.
-/
open Aeneas Aeneas.Std Result ControlFlow Error

/-- [core::time::Duration]
    Source: '/rustc/library/core/src/time.rs', lines 81:0-81:19
    Name pattern: [core::time::Duration]
    Visibility: public -/
@[rust_type "core::time::Duration"]
axiom core.time.Duration : Type

/-- [std::collections::hash::map::HashMap]
    Source: '/rustc/library/std/src/collections/hash/map.rs', lines 246:0-251:1
    Name pattern: [std::collections::hash::map::HashMap]
    Visibility: public -/
@[rust_type "std::collections::hash::map::HashMap"]
axiom std.collections.hash.map.HashMap (K : Type) (V : Type) (S : Type) (A :
  Type) : Type

/-- [std::hash::random::RandomState]
    Source: '/rustc/library/std/src/hash/random.rs', lines 35:0-35:22
    Name pattern: [std::hash::random::RandomState]
    Visibility: public -/
@[rust_type "std::hash::random::RandomState"]
axiom std.hash.random.RandomState : Type

/-- [std::hash::random::DefaultHasher]
    Source: '/rustc/library/std/src/hash/random.rs', lines 94:0-94:24
    Name pattern: [std::hash::random::DefaultHasher]
    Visibility: public -/
@[rust_type "std::hash::random::DefaultHasher"]
axiom std.hash.random.DefaultHasher : Type

/-- [alloc::string::FromUtf8Error]
    Source: '/rustc/library/alloc/src/string.rs', lines 391:0-391:24
    Name pattern: [alloc::string::FromUtf8Error]
    Visibility: public -/
@[rust_type "alloc::string::FromUtf8Error"]
axiom alloc.string.FromUtf8Error : Type

/-- [serde_json::error::Error]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/serde_json-1.0.154/src/error.rs', lines 17:0-17:16
    Name pattern: [serde_json::error::Error]
    Visibility: public -/
@[rust_type "serde_json::error::Error"]
axiom serde_json.error.Error : Type

/-- [zeroize::Zeroizing]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/zeroize-1.9.2/src/lib.rs', lines 584:0-584:41
    Name pattern: [zeroize::Zeroizing]
    Visibility: public -/
@[rust_type "zeroize::Zeroizing"]
axiom zeroize.Zeroizing (Z : Type) : Type

