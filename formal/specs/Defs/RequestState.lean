/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Aeneas

/-!
# Definitions for the `request_state` codec statements

Definitions that the statements of the codec functions E01–E04 (plan Section 2.2) need beyond
those of `Defs/Wire.lean`: the two `InvalidKeyring` message texts of E04 and the relation
between a translated `&str` and a Lean `String`. E01–E04 otherwise use the `Defs.Wire`
definitions (`bodyExpiry`, `Expired`, `expiryLen`, `b64Len`, `minKeyLength`, `maxKidLen`), so
that the W theorems apply to them without conversion (plan Section 5, "Lean libraries").

Rust source: `crates/rmcp/src/model/request_state.rs` at local commit `9b030c6` (the
translation was generated from it plus the working-tree Charon excludes of the seven derived
`Debug` impls; `formal/translation/` is untracked and not yet a pinned fork commit). Everything
lives in the namespace `Defs.RequestState`.
-/

namespace Defs.RequestState

open Aeneas.Std

/-- The message of `InvalidKeyring` for an empty key id: the text of the constant
`KID_EMPTY_MSG` (request_state.rs, line 86), as at the base commit (checked by the test
`codec_constants_agree_with_wire`, request_state.rs, lines 748–779). -/
def kidEmptyMsg : String := "key id must not be empty"

/-- The message of `InvalidKeyring` for a key id longer than 255 bytes: the text of the
constant `KID_TOO_LONG_MSG` (request_state.rs, line 88), as at the base commit (checked by the
test `codec_constants_agree_with_wire`, request_state.rs, lines 748–779). -/
def kidTooLongMsg : String := "key id exceeds 255 UTF-8 bytes"

/-- The string slice `msg` holds exactly the UTF-8 bytes of the text `s`.

A Rust `&str` is translated to the Aeneas `Str`, the list of its UTF-8 bytes; this relates such a
value to a Lean `String` without going through Aeneas `toStr`. -/
def StrIs (msg : Str) (s : String) : Prop :=
  (msg : Slice U8).val.map UScalar.val = s.toByteArray.toList.map UInt8.toNat

end Defs.RequestState
