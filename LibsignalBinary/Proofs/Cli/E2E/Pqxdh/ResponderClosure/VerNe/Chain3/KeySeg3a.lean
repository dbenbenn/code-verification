/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.KeyDefs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Code
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.VarintBridge
import ProofLib.SepLogic.WPp

/-!
# `message::merge<Chain> [local#5]`: ChainKey Segment 3a (`Chain3Seg3aStmt`)

Verifies segment 3a (`+0x0a8 → +0x368`): outer key `0x1a` decode, niche check `[a + 0x48] == noneCap`
and default `ChainKey` initialization at `a + 0x48..0x64`, body-length varint decode, and inner-loop
limit computation `x25 = |afterCk|`.
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

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  Arm64.calleeSavedVRegs_advancePC Arm64.calleeSavedVRegs_setPC Arm64.calleeSavedVRegs_setMem
  Arm64.calleeSavedVRegs_setPState Arm64.calleeSavedVRegs_writeReg64 Arm64.calleeSavedVRegs_writeReg32
  Arm64.calleeSavedVRegs_writeReg
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

/-! ## 1. Register preservation and pure helpers -/

/-- Registers kept across segment 3a: `x19..x24`, `x26..x29`, and `calleeSavedVRegs`
(`x25` is written at `+0x348`). -/
@[expose] def C3aKeep (s0 s1 : State) : Prop :=
  s1.readReg64 .x19 = s0.readReg64 .x19 ∧
  s1.readReg64 .x20 = s0.readReg64 .x20 ∧
  s1.readReg64 .x21 = s0.readReg64 .x21 ∧
  s1.readReg64 .x22 = s0.readReg64 .x22 ∧
  s1.readReg64 .x23 = s0.readReg64 .x23 ∧
  s1.readReg64 .x24 = s0.readReg64 .x24 ∧
  s1.readReg64 .x26 = s0.readReg64 .x26 ∧
  s1.readReg64 .x27 = s0.readReg64 .x27 ∧
  s1.readReg64 .x28 = s0.readReg64 .x28 ∧
  s1.readReg64 .x29 = s0.readReg64 .x29 ∧
  calleeSavedVRegs s1 = calleeSavedVRegs s0

set_option maxHeartbeats 400000 in
theorem C3aKeep.trans {s0 s1 s2 : State}
    (h01 : C3aKeep s0 s1) (h12 : C3aKeep s1 s2) : C3aKeep s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
   h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
   h12.2.2.2.2.2.1.trans h01.2.2.2.2.2.1, h12.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.2.2.2.trans h01.2.2.2.2.2.2.2.2.2.2⟩

set_option maxHeartbeats 400000 in
theorem C3aKeep.of_calleeSaved {s0 s1 : State}
    (h : CalleeSavedPreserved s0 s1) : C3aKeep s0 s1 :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2⟩

set_option maxHeartbeats 400000 in
theorem c3a_decodeVarint_1a (rest : List (BitVec 8)) :
    decodeVarint (0x1a#8 :: rest) = some (0x1a#64, rest) := rfl

set_option maxHeartbeats 400000 in
theorem c3a_decodeVarint_lt128 (n : Nat) (hn : n < 128) (rest : List (BitVec 8)) :
    decodeVarint (BitVec.ofNat 8 n :: rest) = some (BitVec.ofNat 64 n, rest) := by
  have hb0 : (BitVec.ofNat 8 n).toNat < 128 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hn
  have hdv : decodeVarint (BitVec.ofNat 8 n :: rest) =
      some (((BitVec.ofNat 8 n).setWidth 64 &&& 127#64) ||| 0#64, rest) := by
    unfold decodeVarint decodeVarintAux
    simp
    exact fun h => absurd h (by omega)
  rw [hdv]
  have h64 : ((BitVec.ofNat 8 n).setWidth 64 &&& 127#64) ||| 0#64 = BitVec.ofNat 64 n := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    change (n % 256 % 2 ^ 64 &&& 127) ||| 0 = n % 2 ^ 64
    rw [Nat.or_zero, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.and_two_pow_sub_one_eq_mod n 7, Nat.mod_eq_of_lt hn,
      Nat.mod_eq_of_lt (by omega)]
  rw [h64]

set_option maxHeartbeats 400000 in
theorem c3a_hdr_combine (ptr : BitVec 64) (n : Nat) :
    (ptr ↦₈ 0x1a#8) ∗ ((ptr + 1#64) ↦₈ BitVec.ofNat 8 n) =
      (ptr ↦ₛ [0x1a#8, BitVec.ofNat 8 n]) := by
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]

set_option maxHeartbeats 400000 in
theorem c3a_ofNat_add_sub_left (m k : Nat) :
    BitVec.ofNat 64 (m + k) - BitVec.ofNat 64 m = BitVec.ofNat 64 k := by
  rw [BitVec.ofNat_add, BitVec.add_comm, BitVec.add_sub_cancel]

set_option maxHeartbeats 400000 in
theorem c3a_ule_ofNat_add_right {m k : Nat} (hlt : m + k < 2 ^ 62) :
    (BitVec.ofNat 64 m).ule (BitVec.ofNat 64 (m + k)) = true := by
  simp only [BitVec.ule, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : m + k < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : m < 2 ^ 64),
    decide_eq_true_eq]
  omega

/-! ## 2. `decode_varint [local#3]` call step (`Qp` = `chainMerge3SpecAtW` panic) -/

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3
