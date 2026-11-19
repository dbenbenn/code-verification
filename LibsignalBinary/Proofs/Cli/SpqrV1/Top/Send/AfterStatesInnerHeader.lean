/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesInnerHeader -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.SpqrV1.Auth.Repr -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.Base
public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.UnchunkedBase
public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.Defs
public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.Defs
public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.DefsChunkedV1 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.DefsV1State -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Decodes -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2Base
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.ChainEncodedLen
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.V1State
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EpochEncodedLen
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesVnEncode
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodedLenVn
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateHeader
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesVnEncode
import ProofLib.SepLogic.WPp

/-!
# `spqr::send::<signal_session_ratchet::Coins>` Phase 3d Header & Jump-Table Dispatch

Proves `.rodata` encode jump-table unpacking (`+0x9d506`), `[local#3]` callee bridges,
and `PqRatchetState.inner` header and jump-table dispatch steps (`+6140..+6616`).
-/

public section

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec

open CryptoVerification.CodeLayout

open CryptoVerification.LibsignalSession

open CryptoVerification.LibsignalTripleRatchet (spqrSendName AllocContracts)

open CryptoVerification.LibsignalSpqrV1

open CryptoVerification.SpqrV1.Alloc

open CryptoVerification.SpqrV1.ProtoRepr

open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen

open CryptoVerification.SpqrV1.Varint

open CryptoVerification.SpqrV1.Auth (authEncodeLocal1Name authEncodePinnedSpecOf)

open CryptoVerification.SpqrV1.Prost.MessageEncode

open CryptoVerification.SpqrV1.Prost.EncodeToVec

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

set_option linter.unusedVariables false

set_option linter.unusedSimpArgs false

/-! ## 1. Unpacked `.rodata` Jump Table at `b + 0x9d506#64` and `HasSendEncodeJumpTableAddr` -/

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  Prost.EncodeToVec.noneCap2_add_two_beq_zero Prost.EncodeToVec.noneCap2_add_two_bne_zero
  ProtoRepr.noneCap_add_two_beq_zero ProtoRepr.noneCap_add_two_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 ule_self_64 ult_self_64

end CryptoVerification.SpqrV1.Top.Send
