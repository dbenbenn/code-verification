/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IkpTryFrom.LoopError -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
import ProofLib.SepLogic.WPp

/-!
# `IdentityKeyPair::try_from` Field Merge Branches

Verifies the per-tag field merge branches for `publicKey` (tag 1, `+264`), `privateKey` (tag 2,
`+92`), unknown tags (`skip_field`, `+284`), and tag dispatch (`+248..+260`).
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

section LoopMergeStateSimp

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_lm (s : State) (pc : BitVec 64) : (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_lm (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPState_lm (s : State) (ps : PState) : (s.setPState ps).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_advancePC_lm (s : State) : s.advancePC.sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_writeReg64_gpr_lm (s : State) (idx : BitVec 5) (val : BitVec 64) :
    (s.writeReg64 (Reg.gpr idx) val).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_writeReg32_gpr_lm (s : State) (idx : BitVec 5) (val : BitVec 32) :
    (s.writeReg32 (Reg.gpr idx) val).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_writeReg_gpr_lm (s : State) (w : Width) (idx : BitVec 5) (val : BitVec 64) :
    (s.writeReg w (Reg.gpr idx) val).sp = s.sp := by cases w <;> cases s <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_lm (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r := State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_lm (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPState_lm (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg64 r = s.readReg64 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_lm (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_lm (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPState_lm (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg32 r = s.readReg32 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_lm (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_lm (s : State) (m : Memory) (w : RegWidth) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPState_lm (s : State) (ps : PState) (w : RegWidth) (r : Reg) :
    (s.setPState ps).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl

end LoopMergeStateSimp

/-! ## Helper lemmas for loop invariants and frame splitting -/

theorem vecU8Buf_cap_lt63 (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Buf A cap ptr bs ⊢ ⌜cap.toNat < 2 ^ 63⌝ ∗ vecU8Buf A cap ptr bs := by
  unfold vecU8Buf
  refine Entails.pure_left fun h => ?_
  rw [pure_true_emp h.2.1, emp_sepConj, pure_true_emp h, emp_sepConj]
  exact Entails.refl _

theorem ikpStructAt_entails_of (A : RustAlloc) (pk sk : VecPin) (a : BitVec 64)
    (m : IdentityKeyPairStructure) :
    ikpStructAt A pk sk a m ⊢ ikpStructOf A a m :=
  Entails.trans (sepExists_intro (fun sk' => ikpStructAt A pk sk' a m) sk)
    (sepExists_intro (fun pk' => ∃∗ sk', ikpStructAt A pk' sk' a m) pk)

theorem ikpMem144_prologue_cells (sp' : BitVec 64) :
    memRegion sp' 144 ⊢
      ∃∗ w88 : BitVec 64, ∃∗ w80 : BitVec 64, ∃∗ w72 : BitVec 64, ∃∗ w64 : BitVec 64,
      ∃∗ w56 : BitVec 64, ∃∗ w48 : BitVec 64, ∃∗ w40 : BitVec 64, ∃∗ w32 : BitVec 64,
        memRegion sp' 32 ∗
        ((sp' + 32#64) ↦₆₄ w32) ∗ ((sp' + 40#64) ↦₆₄ w40) ∗
        ((sp' + 48#64) ↦₆₄ w48) ∗ ((sp' + 56#64) ↦₆₄ w56) ∗
        ((sp' + 64#64) ↦₆₄ w64) ∗ ((sp' + 72#64) ↦₆₄ w72) ∗
        ((sp' + 80#64) ↦₆₄ w80) ∗ ((sp' + 88#64) ↦₆₄ w88) ∗
        memRegion (sp' + 96#64) 48 := by
  rw [show (144 : Nat) = 32 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + 48)))))))) by decide,
    Prost.memRegion_split sp' 32 112 (by decide),
    Prost.memRegion_split (sp' + 32#64) 8 104 (by decide),
    Prost.memRegion_split (sp' + 32#64 + 8#64) 8 96 (by decide),
    Prost.memRegion_split (sp' + 32#64 + 8#64 + 8#64) 8 88 (by decide),
    Prost.memRegion_split (sp' + 32#64 + 8#64 + 8#64 + 8#64) 8 80 (by decide),
    Prost.memRegion_split (sp' + 32#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 72 (by decide),
    Prost.memRegion_split (sp' + 32#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 64 (by decide),
    Prost.memRegion_split (sp' + 32#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 56 (by decide),
    Prost.memRegion_split (sp' + 32#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 48 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.refl _

theorem ikpEmptyCells_entails_structAt (A : RustAlloc) (sp' : BitVec 64) :
    ((sp' + 48#64) ↦₆₄ 0#64) ∗ ((sp' + 56#64) ↦₆₄ 1#64) ∗ ((sp' + 64#64) ↦₆₄ 0#64) ∗
      ((sp' + 72#64) ↦₆₄ 0#64) ∗ ((sp' + 80#64) ↦₆₄ 1#64) ∗ ((sp' + 88#64) ↦₆₄ 0#64) ⊢
      ikpStructAt A ⟨0#64, 1#64⟩ ⟨0#64, 1#64⟩ (sp' + 48#64) IdentityKeyPairStructure.empty := by
  unfold ikpStructAt IdentityKeyPairStructure.empty
  have h1ne : (1#64 : BitVec 64) ≠ 0 := by decide
  simp only [vecU8At_eq_header_buf, vecHeader, vecU8Buf_zero,
    BitVec.add_assoc, BitVec.reduceAdd, List.length_nil,
    pure_true_emp (And.intro trivial h1ne), sepConj_emp, sepConj_assoc]
  exact Entails.refl _

theorem tag_ge3_conds (tag : ℕ) (hge : 3 ≤ tag) (hlt : tag < 2 ^ 32) :
    let w1 := (BitVec.ofNat 64 tag).setWidth 32
    ((w1 == 2#32) = false) ∧ ((w1 == 1#32) = false) ∧ ((w1 != 1#32) = true) := by
  dsimp only
  rw [setWidth32_ofNat64]
  have h2 : BitVec.ofNat 32 tag ≠ 2#32 := by bv_omega
  have h1 : BitVec.ofNat 32 tag ≠ 1#32 := by bv_omega
  exact ⟨beq_eq_false_iff_ne.mpr h2, beq_eq_false_iff_ne.mpr h1, bne_iff_ne.mpr h1⟩

/-! ## Field merge branches: `publicKey` (`+264`), `privateKey` (`+92`), `skipField` (`+284`) -/

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.IkpTryFrom
