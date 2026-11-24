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
import Proofs.External.Option
import Proofs.External.Net
import Proofs.External.IntParse
import Proofs.External.Prim
import Proofs.External.Std
import Proofs.External.Iter
import Proofs.External.Byte
import Proofs.External.WP
import Proofs.Model.RequestState.Common
import Proofs.Model.RequestState.OpenAuthenticatedBody
import Proofs.Model.RequestState.ValidateKeyLength
import Proofs.Model.RequestState.ValidateConfigKid
import Proofs.Model.RequestState.B64Len
import Proofs.Model.RequestState.OpenAt
import Proofs.Model.RequestState.SealRs1
import Proofs.Model.RequestState.SealRs2
import Proofs.Model.RequestState.OpenRs1At
import Proofs.Model.RequestState.Rs1FallbacksVerify
import Proofs.Model.RequestState.OpenRs2At
import Proofs.Model.RequestState.Roundtrip
import Proofs.Model.JsonRpcMessage
import Proofs.Model.NumberOrString
import Proofs.Model.Task
import Proofs.Model.SamplingContent
import Proofs.Model.Reference
import Proofs.Transport.ClientSideSse
import Proofs.Transport.AsyncRw
import Proofs.Transport.Tower
import Proofs.Transport.Auth
import Proofs.Defs.Wire
import Proofs.Defs.CodecState
import Proofs.Defs.RequestState
import Proofs.Defs.Sse
import Proofs.Defs.Net
import Proofs.Defs.Methods
import Proofs.Defs.Tower
import Proofs.Internal.External
import Proofs.Internal.Model
import Proofs.Internal.Model.RequestState
import Proofs.Internal.Model.RequestStateWire
import Proofs.Internal.Transport.Common.ClientSideSse
import Proofs.Internal.Transport.AsyncRw
import Proofs.Internal.Transport.StreamableHttpServer.Tower
import Proofs.Internal.Transport.Auth

/-!
# Proofs

Root of the `Proofs` library: spec theorems and the laws of the external models (plan Section 5).
Maintained by hand; a proof module is added here only once its proof is complete
(docs/WORKFLOW_AND_PR_GUIDE.md, "Library roots"). Imports the `request_state_wire`
proofs (S06, S10): `Common` and the 15 target modules; the laws of the
external models (S08, S09: `Proofs.External.*`); and the `request_state` proofs of E01–E04
(S07), E07/E08 (S11), E09a/E09/E10 (S13), E11 (S14) and the round trips (S15, `Roundtrip`), with the
slice-iterator helper `Proofs.External.Iter`.

Phase 2 (2026-11-24, S28–S32): `Proofs.Model.{JsonRpcMessage, NumberOrString, Task,
SamplingContent, Reference}` (M01–M14, the joint lemmas, C03), `Proofs.Transport.{ClientSideSse,
AsyncRw, Tower, Auth}` (T01–T08, A01–A03, C01, C02, C04, C05); the S27 law relating the integer
parser model to `Defs.parseI64` is in `Proofs.External.IntParse`.

Since 2026-11-24 it also imports the definitions used only by internal statements
(`Proofs.Defs.*`) and the internal spec files (`Proofs.Internal.*`: statements about private,
crate-internal and patch-only functions and the model laws, in the format of `formal/specs/Specs/`).
-/
