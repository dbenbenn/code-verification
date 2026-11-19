/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Record.SegCloneBase
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import Aesop.BuiltinRules
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Simps
import Mathlib.Tactic.ToAdditive
import Mathlib.Tactic.ToDual
import ProofLib.RegChain
import ProofLib.SepLogic.WPp
public meta import ProofLib.SepLogic.CodeLookup
public meta import ProofLib.VCGen
import LibsignalBinary.Proofs.CodeLayout

/-!
# Receiver-Chain and Pre-Key Cloning Segments for `SegClone`

Verifies the `receiver_chains` loop (`+0x544 / +0x300 → +0x548 / +0x390`) and the optional
`pending_pre_key` and `pending_kyber_pre_key` clone segments (`→ +0x56c / +0x1920 / +0x430`).
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record
open ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Fast side-condition closer that clears large continuation/spec hypotheses before simplifying. -/
macro "segCloneChains_close" : tactic =>
  `(tactic| (
    try clear hnext
    try clear hshim
    try clear halloc
    try clear hmemcpy
    try clear hcall
    try clear hpanic
    try clear hsub
    try clear hexpose
    try clear htail_pts
    try clear h_at_39c
    try clear h_at_3f8
    try clear h_at_444
    try clear h_at_478
    first
    | rfl
    | (dsimp only [State.spAligned, Reg.x0, Reg.x1, Reg.x2, Reg.x8, Reg.x9, Reg.x10,
        Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
        Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.fp] at *
       try simp (config := { decide := true }) only [reduceStateReadReg64,
        State.pc_writeReg64, State.pc_writeReg32,
        State.status_writeReg64, State.status_writeReg32,
        State.sp_writeReg64_gpr,
        State.readReg64_setPC, State.readReg64_setPState, State.readReg64_writeReg64,
        calleeSavedVRegs_setPC, calleeSavedVRegs_setMem, calleeSavedVRegs_setPState,
        calleeSavedVRegs_writeReg64, calleeSavedVRegs_writeReg32,
        calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg]
       simp (config := { decide := true }) only [*, reduceStateReadReg64,
        State.pc_writeReg64, State.pc_writeReg32,
        State.status_writeReg64, State.status_writeReg32,
        State.sp_writeReg64_gpr,
        State.readReg64_setPC, State.readReg64_setPState, State.readReg64_writeReg64,
        calleeSavedVRegs_setPC, calleeSavedVRegs_setMem, calleeSavedVRegs_setPState,
        calleeSavedVRegs_writeReg64, calleeSavedVRegs_writeReg32,
        calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg,
        State.setPC, State.setPState,
        BitVec.add_assoc, BitVec.reduceAdd, BitVec.zero_add, List.length_cons]
       done)
    | (dsimp only [State.spAligned, Reg.x0, Reg.x1, Reg.x2, Reg.x8, Reg.x9, Reg.x10,
        Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
        Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.fp] at *
       try simp (config := { decide := true }) only [reduceStateReadReg64,
        State.pc_writeReg64, State.pc_writeReg32,
        State.status_writeReg64, State.status_writeReg32,
        State.sp_writeReg64_gpr,
        State.readReg64_setPC, State.readReg64_setPState, State.readReg64_writeReg64,
        calleeSavedVRegs_setPC, calleeSavedVRegs_setMem, calleeSavedVRegs_setPState,
        calleeSavedVRegs_writeReg64, calleeSavedVRegs_writeReg32,
        calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg]
       simp [*, State.setPC, State.setPState, State.writeReg64, State.writeReg32]
       done)
    | (dsimp only [State.spAligned, Reg.x0, Reg.x1, Reg.x2, Reg.x8, Reg.x9, Reg.x10,
        Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
        Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.fp] at *
       subst_vars
       simp [*, State.setPC, State.setPState, State.writeReg64, State.writeReg32]
       done)))

end CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
