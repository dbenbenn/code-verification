/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.ChainClone4KBase
import LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordChainClone.Defs
import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.ChainClone3.ChainCloneCk
import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.ChainClone3.ChainCloneMk
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs -- shake: keep
import LibsignalBinary.Proofs.CodeLayout

public section

set_option autoImplicit false

/-!
# 4K-Stack `FromRecordChainClone` (`Chain::clone [local#3]`) — Non-Empty `message_keys` & `chain_key`

Non-empty `message_keys` allocation/loop wrapper (`+260..+712`), `chain_key = none` (`+244..+256`),
and `chain_key = some ck` (`+148..+212`) segments for `FromRecordChainClone.chainCloneName`
(`[local#3]`) on `tripleRatchetProgAtExt b ext` under `ChainClone4KHooks b A ext`.
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

/-! ## Non-Empty `message_keys` Allocation, Loop Wrapper, and Register Reload (`+260..+712`) -/

end CryptoVerification.Cli.LibsignalSpqrV1.M4.ChainClone4K
