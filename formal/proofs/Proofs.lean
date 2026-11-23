/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Defs
import Proofs.Model.RequestStateWire.Common
import Proofs.Model.RequestStateWire.B64Len
import Proofs.Model.RequestStateWire.KeyLengthOk
import Proofs.Model.RequestStateWire.CheckKidLen
import Proofs.Model.RequestStateWire.BytesEq
import Proofs.Model.RequestStateWire.NextDot
import Proofs.Model.RequestStateWire.ComponentCount
import Proofs.Model.RequestStateWire.VersionOf
import Proofs.Model.RequestStateWire.ParseRs1
import Proofs.Model.RequestStateWire.ParseRs2
import Proofs.Model.RequestStateWire.TranscriptV1
import Proofs.Model.RequestStateWire.TranscriptV2
import Proofs.Model.RequestStateWire.DecodeExpiry
import Proofs.Model.RequestStateWire.IsExpired
import Proofs.Model.RequestStateWire.OpenFrame
import Proofs.Model.RequestStateWire.Frame
import Proofs.External.Base64
import Proofs.External.String
import Proofs.External.Prim
import Proofs.External.Std
import Proofs.Model.RequestState.Common
import Proofs.Model.RequestState.OpenAuthenticatedBody
import Proofs.Model.RequestState.ValidateKeyLength
import Proofs.Model.RequestState.ValidateConfigKid
import Proofs.Model.RequestState.B64Len

/-!
# Proofs

Root of the `Proofs` library: spec theorems and the laws of the external models (plan Section 5).
Maintained by hand; a proof module is added here only once its proof is complete
(docs/WORKFLOW_AND_PR_GUIDE.md, "Library roots"). Imports the `request_state_wire`
proofs (S06, S10): `Common` and the 15 target modules; the laws of the
external models (S08, S09: `Proofs.External.*`); and the `request_state` proofs of E01–E04
(S07).
-/
