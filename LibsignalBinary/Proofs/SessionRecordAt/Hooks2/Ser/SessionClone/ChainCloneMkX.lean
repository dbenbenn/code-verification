/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SepWPpIn -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneBaseX -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsX -- proof-setup: allow-public-import
import ProofLib
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.ChainCloneMk
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneEpilogueX
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

public section

set_option autoImplicit false

/-!
# `Chain::clone [local#1]` `message_keys` Clone Loop (`0x38570..0x38748`)

Verifies the empty fast path and non-empty `Vec<MessageKey>` allocation and per-element seed-cloning
loop of `<session_structure::Chain as Clone>::clone [local#1]` (`0x24848`) on `SP2Ext`.
-/

namespace CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open Proofs.libsignal
open Proofs.libsignal.Hooks2
open Proofs.libsignal.Stage1X

set_option maxRecDepth 500000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  fp_neg_48 fp_neg_40 fp_neg_32 fp_neg_24 fp_neg_12 fp_neg_8
  fp_neg_48_int fp_neg_40_int fp_neg_32_int fp_neg_24_int fp_neg_12_int fp_neg_8_int
attribute [local arm64_norm ↓, local wp_norm ↓]
  ChainCloneStateSimp.sp_setPC_pre ChainCloneStateSimp.sp_setMem_setPC_pre
  ChainCloneStateSimp.readReg64_setPC_pre ChainCloneStateSimp.readReg64_setMem_setPC_pre
  ChainCloneStateSimp.readReg32_setPC_pre ChainCloneStateSimp.readReg32_setMem_setPC_pre
  ChainCloneStateSimp.readReg_setPC_pre ChainCloneStateSimp.readReg_setMem_setPC_pre
attribute [local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite calleeSavedVRegs_writeVReg64_ite
  calleeSavedVRegs_writeVReg32_ite isCalleeSavedVReg updateCalleeSavedVRegs

theorem L1_ChainCloneMkX : True := trivial

end CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1
