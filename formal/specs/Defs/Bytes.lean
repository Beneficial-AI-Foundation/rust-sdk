/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Aeneas

@[expose] public section

/-!
# UTF-8 bytes of a Lean string

`Defs.utf8Bytes`, the one encoding of a Lean string as a byte list that the Phase 2 definitions
and statements share (`Defs.Methods`, `Defs.Tower`, `Specs.Model`, `Proofs.Internal.Transport`;
lead decision 2026-11-24, S24 fix round 1). Imported from the `Defs` root since incorporation of
S24. It imports only `Aeneas`; its link with the trusted model is a lemma in `Proofs`.
-/

namespace Defs

open Aeneas.Std

/-- **The UTF-8 bytes of a Lean string**, as `U8` values (Lean's `String.toByteArray`). A Rust
`&str` is translated to the Aeneas `Str`, the list of its UTF-8 bytes, so a string slice `m`
holds exactly the text `s` when `m.val = utf8Bytes s`; this is equivalent to
`Defs.RequestState.StrIs m s`, which compares the same bytes as natural numbers
(`Proofs.RequestState.strIs_iff_val_eq_utf8Bytes`). The kernel evaluates it on a literal, so
`utf8Bytes "http" = [104#u8, 116#u8, 116#u8, 112#u8]` holds by `decide +kernel`.

It is the same function as the trusted model's `ExtModel.utf8` (`trusted/Rmcp/FunsExternal.lean`):
`Proofs.External.Utf8.utf8Bytes_eq_utf8` proves `Defs.utf8Bytes s = ExtModel.utf8 s` by `rfl`,
so statements about the external models and statements written with `utf8Bytes` meet by
rewriting with that lemma. -/
def utf8Bytes (s : String) : List U8 :=
  s.toByteArray.toList.map (fun b => ⟨BitVec.ofNat 8 b.toNat⟩)

end Defs
