/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.AllocContracts4KExt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.ChainClone4KBase
import LibsignalBinary.Proofs.Cli.SpqrV1.M4.ChainClone4KSteps
import LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordChainClone.Defs
import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.ChainClone3.ChainCloneCk
import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.ChainClone3.ChainCloneEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs -- shake: keep
import LibsignalBinary.Proofs.CodeLayout

public section

set_option autoImplicit false

/-!
# 4K-Stack `FromRecordChainClone` (`Chain::clone [local#3]`) — `priv`, Entry, and Top-Level Contracts

Proves `priv = []` (`+88..+92` / `+228..+240`), `0 < priv.length` (`+88..+144`), function entry and
`srk` clone (`+0..+84`), and top-level `FromRecordChainClone.ChainCloneOkExt` and
`FromRecordChainClone.SenderChainCloneOkExt` under 4K-stack `AllocContracts4K b A ext` and
`CliExternsOk P A ext` for `<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#3]`.
-/

namespace CryptoVerification.Cli.LibsignalSpqrV1.M4.ChainClone4K

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  sessionShimSpec sessionMemcpySpec allocFailedIn_of_eq
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.ChainClone3

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

attribute [local arm64_norm, local wp_norm]
  fp_neg_48 fp_neg_40 fp_neg_32 fp_neg_24 fp_neg_12 fp_neg_8
  fp_neg_48_int fp_neg_40_int fp_neg_32_int fp_neg_24_int fp_neg_12_int fp_neg_8_int

attribute [local arm64_norm ↓, local wp_norm ↓]
  BS5.sp_setPC_pre BS5.sp_setMem_setPC_pre
  BS5.readReg64_setPC_pre BS5.readReg64_setMem_setPC_pre
  BS5.readReg32_setPC_pre BS5.readReg32_setMem_setPC_pre
  BS5.readReg_setPC_pre BS5.readReg_setMem_setPC_pre

attribute [local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite calleeSavedVRegs_writeVReg64_ite
  calleeSavedVRegs_writeVReg32_ite isCalleeSavedVReg updateCalleeSavedVRegs

/-! ## `priv = []` (`+88..+92` / `+228..+240`) and `0 < priv.length` (`+88..+144`) -/

end CryptoVerification.Cli.LibsignalSpqrV1.M4.ChainClone4K

namespace CryptoVerification.Cli.LibsignalSpqrV1.M4

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Slots (AgreeOnCliHooks)

/-! ## Top-Level 4K-Stack `ChainCloneOkExt` and `SenderChainCloneOkExt` (`[local#3]`) -/

end CryptoVerification.Cli.LibsignalSpqrV1.M4
