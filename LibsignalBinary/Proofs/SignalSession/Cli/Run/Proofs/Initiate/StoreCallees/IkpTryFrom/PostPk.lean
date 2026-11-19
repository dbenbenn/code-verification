/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IkpTryFrom.Defs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IkpTryFrom.PostPrivAndOk
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostRkSome
import ProofLib.SepLogic.WPp

/-!
# `IdentityKeyPair::try_from` Post-Loop `PublicKey::try_from` Dispatch

Verifies post-loop `PublicKey::try_from` validation and error dispatch (`+344..+392`, `+688..+756`).
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.IkpTryFrom



open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.RecordCodecs
open CryptoVerification.RecordCodecsBinary

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

section PostPkStateSimp

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pk (s : State) (pc : BitVec 64) : (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_pk (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPState_pk (s : State) (ps : PState) : (s.setPState ps).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_advancePC_pk (s : State) : s.advancePC.sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_writeReg64_gpr_pk (s : State) (idx : BitVec 5) (val : BitVec 64) :
    (s.writeReg64 (Reg.gpr idx) val).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_writeReg32_gpr_pk (s : State) (idx : BitVec 5) (val : BitVec 32) :
    (s.writeReg32 (Reg.gpr idx) val).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_writeReg_gpr_pk (s : State) (w : Width) (idx : BitVec 5) (val : BitVec 64) :
    (s.writeReg w (Reg.gpr idx) val).sp = s.sp := by cases w <;> cases s <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pk (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r := State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_pk (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPState_pk (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg64 r = s.readReg64 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_pk (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_pk (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPState_pk (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg32 r = s.readReg32 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_pk (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_pk (s : State) (m : Memory) (w : RegWidth) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPState_pk (s : State) (ps : PState) (w : RegWidth) (r : Reg) :
    (s.setPState ps).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl

end PostPkStateSimp

/-! ## Post-loop `PublicKey::try_from` & error dispatch (`+344 .. +392`, `+688 .. +756`) -/

private theorem pkErr_fold_spe7 (sp' : BitVec 64) (b9 : BitVec 8) :
    ((sp' + 96#64) ↦₈ 1#8) ∗ memRegion (sp' + 97#64) 7 ∗
      ((sp' + 104#64) ↦₈ 0#8) ∗ ((sp' + 105#64) ↦₈ b9) ∗
      memRegion (sp' + 106#64) 30 ∗ memRegion (sp' + 136#64) 8 ⊢
      memRegion (sp' + 96#64) 48 := by
  have hm96 : ((sp' + 96#64) ↦₈ 1#8) ⊢ memRegion (sp' + 96#64) 1 := by
    rw [memRegion_one]; exact sepExists_intro _ 1#8
  have hm104 : ((sp' + 104#64) ↦₈ 0#8) ⊢ memRegion (sp' + 104#64) 1 := by
    rw [memRegion_one]; exact sepExists_intro _ 0#8
  have hm105 : ((sp' + 105#64) ↦₈ b9) ⊢ memRegion (sp' + 105#64) 1 := by
    rw [memRegion_one]; exact sepExists_intro _ b9
  rw [show (48 : Nat) = 1 + (7 + (1 + (1 + (30 + 8)))) by decide,
    Prost.memRegion_split (sp' + 96#64) 1 47 (by decide),
    Prost.memRegion_split (sp' + 96#64 + 1#64) 7 40 (by decide),
    Prost.memRegion_split (sp' + 96#64 + 1#64 + 7#64) 1 39 (by decide),
    Prost.memRegion_split (sp' + 96#64 + 1#64 + 7#64 + 1#64) 1 38 (by decide),
    Prost.memRegion_split (sp' + 96#64 + 1#64 + 7#64 + 1#64 + 1#64) 30 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono hm96
    (sepConj_mono_right (sepConj_mono hm104 (sepConj_mono_left hm105)))

private theorem pkErr_fold_spe8 (sp' : BitVec 64) (t : BitVec 8) :
    ((sp' + 96#64) ↦₈ 1#8) ∗ memRegion (sp' + 97#64) 7 ∗
      ((sp' + 104#64) ↦₈ 1#8) ∗ ((sp' + 105#64) ↦₈ t) ∗
      memRegion (sp' + 106#64) 30 ∗ memRegion (sp' + 136#64) 8 ⊢
      memRegion (sp' + 96#64) 48 := by
  have hm96 : ((sp' + 96#64) ↦₈ 1#8) ⊢ memRegion (sp' + 96#64) 1 := by
    rw [memRegion_one]; exact sepExists_intro _ 1#8
  have hm104 : ((sp' + 104#64) ↦₈ 1#8) ⊢ memRegion (sp' + 104#64) 1 := by
    rw [memRegion_one]; exact sepExists_intro _ 1#8
  have hm105 : ((sp' + 105#64) ↦₈ t) ⊢ memRegion (sp' + 105#64) 1 := by
    rw [memRegion_one]; exact sepExists_intro _ t
  rw [show (48 : Nat) = 1 + (7 + (1 + (1 + (30 + 8)))) by decide,
    Prost.memRegion_split (sp' + 96#64) 1 47 (by decide),
    Prost.memRegion_split (sp' + 96#64 + 1#64) 7 40 (by decide),
    Prost.memRegion_split (sp' + 96#64 + 1#64 + 7#64) 1 39 (by decide),
    Prost.memRegion_split (sp' + 96#64 + 1#64 + 7#64 + 1#64) 1 38 (by decide),
    Prost.memRegion_split (sp' + 96#64 + 1#64 + 7#64 + 1#64 + 1#64) 30 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono hm96
    (sepConj_mono_right (sepConj_mono hm104 (sepConj_mono_left hm105)))

private theorem pkErr_fold_spe9 (sp' : BitVec 64) (b9 : BitVec 8) (n : Nat) :
    ((sp' + 96#64) ↦₈ 1#8) ∗ memRegion (sp' + 97#64) 7 ∗
      ((sp' + 104#64) ↦₈ 2#8) ∗ ((sp' + 105#64) ↦₈ b9) ∗
      memRegion (sp' + 106#64) 6 ∗ ((sp' + 112#64) ↦₆₄ BitVec.ofNat 64 n) ∗
      memRegion (sp' + 120#64) 16 ∗ memRegion (sp' + 136#64) 8 ⊢
      memRegion (sp' + 96#64) 48 := by
  have hm96 : ((sp' + 96#64) ↦₈ 1#8) ⊢ memRegion (sp' + 96#64) 1 := by
    rw [memRegion_one]; exact sepExists_intro _ 1#8
  have hm104 : ((sp' + 104#64) ↦₈ 2#8) ⊢ memRegion (sp' + 104#64) 1 := by
    rw [memRegion_one]; exact sepExists_intro _ 2#8
  have hm105 : ((sp' + 105#64) ↦₈ b9) ⊢ memRegion (sp' + 105#64) 1 := by
    rw [memRegion_one]; exact sepExists_intro _ b9
  rw [show (48 : Nat) = 1 + (7 + (1 + (1 + (6 + (8 + (16 + 8)))))) by decide,
    Prost.memRegion_split (sp' + 96#64) 1 47 (by decide),
    Prost.memRegion_split (sp' + 96#64 + 1#64) 7 40 (by decide),
    Prost.memRegion_split (sp' + 96#64 + 1#64 + 7#64) 1 39 (by decide),
    Prost.memRegion_split (sp' + 96#64 + 1#64 + 7#64 + 1#64) 1 38 (by decide),
    Prost.memRegion_split (sp' + 96#64 + 1#64 + 7#64 + 1#64 + 1#64) 6 32 (by decide),
    Prost.memRegion_split (sp' + 96#64 + 1#64 + 7#64 + 1#64 + 1#64 + 6#64) 8 24 (by decide),
    Prost.memRegion_split (sp' + 96#64 + 1#64 + 7#64 + 1#64 + 1#64 + 6#64 + 8#64) 16 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono hm96
    (sepConj_mono_right (sepConj_mono hm104
      (sepConj_mono hm105
        (sepConj_mono_right (sepConj_mono_left
          (pointsTo64_entails_memRegion (sp' + 112#64) (BitVec.ofNat 64 n)))))))

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.IkpTryFrom
