/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.Defs
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdRegIdHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.PollCommon
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
public import LibsignalBinary.Specifications.AsmConstants -- shake: keep
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

/-!
# `IdentityFiles::get_local_registration_id::{closure#0}` Poll Verification

Verifies `get_local_registration_id::{closure#0}` against `idRegIdPollSpec`, reading
`"registration-id"` via `Dir::get`, parsing a 4-byte little-endian `u32` on length `4`, and
allocating `"malformed file"` (`InvalidState`) otherwise.
-/

public section

set_option autoImplicit false
set_option warningAsError false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.IdRegIdPoll

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.LibsignalSession
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.StoreDefs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.PollCommon

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace RegNorm

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem fs_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).fs = s.fs := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem fs_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).fs = s.fs := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem fs_setPState_pre (s : State) (ps : PState) :
    (s.setPState ps).fs = s.fs := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem fs_writeReg64_pre (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).fs = s.fs := by cases s; cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem fs_writeReg32_pre (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).fs = s.fs := by cases s; cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem fs_writeReg_pre (s : State) (w : RegWidth) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).fs = s.fs := by cases s; cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem trace_writeReg32_pre (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).trace = s.trace := by cases s; cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem trace_writeReg_pre (s : State) (w : RegWidth) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).trace = s.trace := by cases s; cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory)
    (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readVReg128_setPC_pre (s : State) (pc : BitVec 64) (idx : BitVec 5) :
    (s.setPC pc).readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readVReg128_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (idx : BitVec 5) :
    ((s.setPC pc).setMem m).readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readVReg128_setMem_pre (s : State) (m : Memory) (idx : BitVec 5) :
    (s.setMem m).readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readVReg128_setPState_pre (s : State) (ps : PState) (idx : BitVec 5) :
    (s.setPState ps).readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readVReg128_writeReg64_pre (s : State) (r : Reg) (v : BitVec 64) (idx : BitVec 5) :
    (s.writeReg64 r v).readVReg128 idx = s.readVReg128 idx := by
  cases s; cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readVReg128_writeReg32_pre (s : State) (r : Reg) (v : BitVec 32) (idx : BitVec 5) :
    (s.writeReg32 r v).readVReg128 idx = s.readVReg128 idx := by
  cases s; cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readVReg128_writeReg_pre (s : State) (w : RegWidth) (r : Reg) (v : BitVec 64)
    (idx : BitVec 5) :
    (s.writeReg w r v).readVReg128 idx = s.readVReg128 idx := by
  cases s; cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem cap_reconstruct_norm (cap : BitVec 64) :
    ((cap.truncate 32).zeroExtend 64 |||
      (((cap >>> 32).truncate 32).zeroExtend 64 <<< 32)) = cap :=
  PollCommon.cap_reconstruct_u32_pair cap

@[local arm64_norm ↓, local wp_norm ↓]
theorem speWord_one_eq : speWord 1 = asm64% speNicheBase + 1#64 := rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem okTagVec_eq_neg2 : okTagVec = -2#64 := rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem awc_speWord1_two :
    (AddWithCarry64 (speWord 1) 2#64 false).2.z = false := by decide +kernel

@[local arm64_norm ↓, local wp_norm ↓]
theorem awc_okTagVec_two :
    (AddWithCarry64 okTagVec 2#64 false).2.z = true := by decide +kernel

@[local arm64_norm ↓, local wp_norm ↓]
theorem truncate32_zeroExtend64 (v : BitVec 32) :
    (v.zeroExtend 64).truncate 32 = v := by bv_bits

end RegNorm

open RegNorm

/-! ## Inner Specification and Symbolic Execution -/

abbrev regCalleeStk (getStk : Nat) : Nat :=
  max getStk extHookStack

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.IdRegIdPoll
