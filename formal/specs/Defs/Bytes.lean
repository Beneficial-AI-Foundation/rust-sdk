/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Aeneas
import Rmcp.FunsExternal

/-!
# UTF-8 bytes of a Lean string

`Defs.utf8Bytes`, the one encoding of a Lean string as a byte list that the Phase 2 definitions
and drafts share (`Defs.Methods`, `Defs.Tower`, `Drafts/Model.lean`, `Drafts/Transport.lean`;
lead decision 2026-11-24, S24 fix round 1). Not imported from the `Defs` root until sign-off.
-/

namespace Defs

open Aeneas.Std

/-- **The UTF-8 bytes of a Lean string**, as `U8` values (Lean's `String.toByteArray`). A Rust
`&str` is translated to the Aeneas `Str`, the list of its UTF-8 bytes, so a string slice `m`
holds exactly the text `s` when `m.val = utf8Bytes s`; this is equivalent to
`Defs.RequestState.StrIs m s`, which compares the same bytes as natural numbers (lemma at
incorporation, see below). The kernel evaluates it on a literal, so
`utf8Bytes "http" = [104#u8, 116#u8, 116#u8, 112#u8]` holds by `decide +kernel`.

It is the same function as the trusted model's `ExtModel.utf8` (`trusted/Rmcp/FunsExternal.lean`
line 86): `Defs.utf8Bytes s = ExtModel.utf8 s` holds by `rfl` (checked at the end of this file),
so statements about the external models and statements written with `utf8Bytes` meet without a
lemma. The equivalence lemma with `Defs.RequestState.StrIs` is not proved here; it comes at
incorporation, when `Defs.Bytes` is imported from the `Defs` root. -/
def utf8Bytes (s : String) : List U8 :=
  s.toByteArray.toList.map (fun b => ⟨BitVec.ofNat 8 b.toNat⟩)

/-- `utf8Bytes` is the trusted model's UTF-8 conversion, by definition. -/
example (s : String) : utf8Bytes s = ExtModel.utf8 s := rfl

end Defs
