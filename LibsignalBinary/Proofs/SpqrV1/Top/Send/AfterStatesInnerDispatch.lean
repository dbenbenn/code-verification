/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesEncodedLen -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesInnerHeader -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Auth.Encode1
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.CalleeBridges
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParams1
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Ct1Sent1
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EkSentCt1Received1
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirection1
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesChunkedHeaderSent
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesPoly
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked59_71
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1StateHelpers
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesChainEncode
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesEncode
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesInnerChunked1
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesInnerChunked2
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesInnerChunked3
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesInnerChunked3a
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesPolyDecExact
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesPolyExact
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesVnEncode
import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint2
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked82_93

/-!
# `spqr::send`: `InnerState` Jump-Table Dispatch & `PqRatchetState` Encode Assembly

`[local#1]` callee `subroutine_ok` bridges, `.rodata` jump-table loader, 11-variant
`V1State.InnerState` dispatch at `+6616` (`0x32234 -> 0x320a4`), and full `PqRatchetState`
serialization (`step_send_encode_from_vn_len`, `+4288/+4364 -> +6216`) in `spqr::send::<HookRng>`.
-/

public section

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.Auth hiding SepWPp.pure_elim
open CryptoVerification.SpqrV1.Prost.MessageEncode
open CryptoVerification.SpqrV1.Prost.EncodeToVec hiding allowPanic_not_exited

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  ProofLib.truncate32_ofNat64
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero

/-! ## 1. `.rodata` Jump-Table Loader and `[local#1]` Callee `subroutine_ok` Bridges -/

end CryptoVerification.SpqrV1.Top.Send
