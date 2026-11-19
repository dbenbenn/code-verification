/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.KeyDefs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Code
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.ChainMessageKeysG
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Pure
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

/-!
# `message::merge<Chain> [local#5]`: ChainKey Index Field (`Chain3Seg3bStmt`)

Verifies segment 3b (`+0x368 → +0x368`) for inner field 1 (`pbVarint 1 i.toNat`) of `ChainKey`:
no-op when `i = 0`, and inner key `0x08` + varint decode + store to `[a + 0x60]` when `i ≠ 0`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3

open Arm64 ProofLib SepProp ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
  (sliceCursorAt sliceCursorAfter DecodeVarintSlowGhost)
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed
open CryptoVerification.E2E.Record.DeserializeGeneral
open Proofs.libsignal.Hooks2
open CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainMessageKeysG

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  Arm64.calleeSavedVRegs_advancePC Arm64.calleeSavedVRegs_setPC Arm64.calleeSavedVRegs_setMem
  Arm64.calleeSavedVRegs_setPState Arm64.calleeSavedVRegs_writeReg64 Arm64.calleeSavedVRegs_writeReg32
  Arm64.calleeSavedVRegs_writeReg Arm64.calleeSavedVRegs_writeVReg128_ite Arm64.isCalleeSavedVReg
attribute [local arm64_norm ↓, local wp_norm ↓]
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.calleeSavedVRegs_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.calleeSavedVRegs_setMem_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.sp_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.sp_setMem_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg64_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg64_setMem_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg32_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg32_setMem_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg_setMem_setPC_pre_seedChain
attribute [local simp, local arm64_norm]
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.getLsbD_63_eq_seedChain

/-! ## 1. Small helpers -/

set_option maxHeartbeats 400000 in
theorem c3ck_spAligned {s : State} {sp0 : BitVec 64} (hsp : s.sp = sp0 - 0xf0#64)
    (halign : sp0 &&& 15#64 = 0#64) : s.spAligned = true := by
  simp only [State.spAligned, hsp, beq_iff_eq]
  exact sp_sub_240_aligned halign

set_option maxHeartbeats 400000 in
theorem c3ck_zeroExtend64_setWidth32 (i : BitVec 32) :
    (i.zeroExtend 64).setWidth 32 = i := by
  bv_bits

set_option maxHeartbeats 400000 in
theorem c3ck_pbVarint1_eq (n : Nat) (hn : n ≠ 0) :
    pbVarint 1 n = 0x08#8 :: pbVarintBody 5 n := by
  unfold pbVarint; simp [hn]; rfl

set_option maxHeartbeats 400000 in
theorem c3ck_pbVarint1_ptr_advance (ptr : BitVec 64) (n : Nat) (hn : n ≠ 0) :
    ptr + 1#64 + BitVec.ofNat 64 (pbVarintBody 5 n).length =
      ptr + BitVec.ofNat 64 (pbVarint 1 n).length := by
  rw [c3ck_pbVarint1_eq n hn]
  simp only [List.length_cons]
  bv_omega

set_option maxHeartbeats 400000 in
theorem c3ck_pointsTo_08_combine (ptr : BitVec 64) (n : Nat) (hn : n ≠ 0) :
    (ptr ↦ₛ [0x08#8]) ∗ ((ptr + 1#64) ↦ₛ pbVarintBody 5 n) =
      (ptr ↦ₛ pbVarint 1 n) := by
  simp only [c3ck_pbVarint1_eq n hn, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]

/-! ## 2. `decode_varint [local#3]` call helper -/

set_option maxHeartbeats 400000 in
/-- `Chain3InnerLoopRegs` and `calleeSavedVRegs` across a call that preserves the callee-saved
registers and returns with `sp` unchanged. -/
theorem c3ck_regs_after_call {sp0 bufRef a : BitVec 64} {outerTailLen innerTailLen : Nat}
    {s_init s1 sm : State}
    (hregs : Chain3InnerLoopRegs sp0 bufRef a outerTailLen innerTailLen s_init s1)
    (hvregs : calleeSavedVRegs s1 = calleeSavedVRegs s_init)
    (hsp : sm.sp = sp0 - 0xf0#64) (hcs : CalleeSavedPreserved s1 sm) :
    Chain3InnerLoopRegs sp0 bufRef a outerTailLen innerTailLen s_init sm ∧
      calleeSavedVRegs sm = calleeSavedVRegs s_init :=
  ⟨Chain3InnerLoopRegs.of_calleeSaved hregs hsp hcs, hcs.2.2.2.2.2.2.2.2.2.2.2.trans hvregs⟩

/-! ## 3. Straight-line segments -/

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3
