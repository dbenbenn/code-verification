/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IkpTryFrom.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanup
import ProofLib.SepLogic.WPp

/-!
# `IdentityKeyPair::try_from` DecodeError Cleanup Tail

Convergence invariant at `+812`, scratch-frame folding helpers, and `DecodeError` cleanup paths
(`+616..+684 → +812`).
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

section LoopHelpersStateSimp

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_lh (s : State) (pc : BitVec 64) : (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_lh (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPState_lh (s : State) (ps : PState) : (s.setPState ps).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_advancePC_lh (s : State) : s.advancePC.sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_writeReg64_gpr_lh (s : State) (idx : BitVec 5) (val : BitVec 64) :
    (s.writeReg64 (Reg.gpr idx) val).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_writeReg32_gpr_lh (s : State) (idx : BitVec 5) (val : BitVec 32) :
    (s.writeReg32 (Reg.gpr idx) val).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_writeReg_gpr_lh (s : State) (w : Width) (idx : BitVec 5) (val : BitVec 64) :
    (s.writeReg w (Reg.gpr idx) val).sp = s.sp := by cases w <;> cases s <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_lh (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r := State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_lh (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPState_lh (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg64 r = s.readReg64 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_lh (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_lh (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPState_lh (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg32 r = s.readReg32 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_lh (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_lh (s : State) (m : Memory) (w : RegWidth) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPState_lh (s : State) (ps : PState) (w : RegWidth) (r : Reg) :
    (s.setPState ps).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl

end LoopHelpersStateSimp

/-! ## Single convergence invariant at `+812` & cursor advancement -/

theorem pointsToBytes_take_drop :
    ∀ (k : Nat) (bs : List (BitVec 8)) (ptr : BitVec 64),
      k ≤ bs.length →
      (ptr ↦ₛ bs) =
        (ptr ↦ₛ bs.take k) ∗ ((ptr + BitVec.ofNat 64 k) ↦ₛ bs.drop k)
  | 0, bs, ptr, _ => by
    simp [pointsToBytes_nil, BitVec.ofNat]
  | k + 1, [], _, hk => by simp at hk
  | k + 1, b :: bs, ptr, hk => by
    rw [List.take_succ_cons, List.drop_succ_cons,
      pointsToBytes_cons ptr b bs,
      pointsToBytes_cons ptr b (bs.take k),
      pointsToBytes_take_drop k bs (ptr + 1#64) (by simp at hk; omega)]
    have ha : ptr + 1#64 + BitVec.ofNat 64 k = ptr + BitVec.ofNat 64 (k + 1) := by
      rw [BitVec.ofNat_add k 1]; bv_omega
    rw [ha, sepConj_assoc]

theorem ikpMem48_split24 (sp' : BitVec 64) :
    memRegion (sp' + 96#64) 48 =
      memRegion (sp' + 96#64) 24 ∗ memRegion (sp' + 120#64) 24 := by
  have hs := Prost.memRegion_split (sp' + 96#64) 24 24 (by decide)
  have ha : sp' + 96#64 + 24#64 = sp' + 120#64 := by bv_omega
  rw [ha] at hs; exact hs

theorem ikpMem48_split8 (sp' : BitVec 64) :
    memRegion (sp' + 96#64) 48 =
      memRegion (sp' + 96#64) 8 ∗ memRegion (sp' + 104#64) 40 := by
  have hs := Prost.memRegion_split (sp' + 96#64) 8 40 (by decide)
  have ha : sp' + 96#64 + 8#64 = sp' + 104#64 := by bv_omega
  rw [ha] at hs; exact hs

theorem ikpMem48_split_96_104_112 (sp' : BitVec 64) :
    memRegion (sp' + 96#64) 48 =
      (∃∗ w0 : BitVec 64, (sp' + 96#64) ↦₆₄ w0) ∗
      (∃∗ w1 : BitVec 64, (sp' + 104#64) ↦₆₄ w1) ∗
      memRegion (sp' + 112#64) 32 := by
  rw [Prost.memRegion_split (sp' + 96#64) 8 40 (by decide),
    Prost.memRegion_split (sp' + 96#64 + 8#64) 8 32 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  have ha1 : sp' + 96#64 + 8#64 = sp' + 104#64 := by bv_omega
  have ha2 : sp' + 104#64 + 8#64 = sp' + 112#64 := by bv_omega
  rw [ha1, ha2]

theorem ikpPointsTo64_104_mem32_entails_mem40 (sp' v : BitVec 64) :
    ((sp' + 104#64) ↦₆₄ v) ∗ memRegion (sp' + 112#64) 32 ⊢ memRegion (sp' + 104#64) 40 := by
  rw [Prost.memRegion_split (sp' + 104#64) 8 32 (by decide)]
  have ha : sp' + 104#64 + 8#64 = sp' + 112#64 := by bv_omega
  rw [ha]
  exact sepConj_mono_left (pointsTo64_entails_memRegion (sp' + 104#64) v)

theorem ikpPointsTo64_96_mem40_entails_mem48 (sp' v : BitVec 64) :
    ((sp' + 96#64) ↦₆₄ v) ∗ memRegion (sp' + 104#64) 40 ⊢ memRegion (sp' + 96#64) 48 := by
  rw [ikpMem48_split8 sp']
  exact sepConj_mono_left (pointsTo64_entails_memRegion (sp' + 96#64) v)

theorem ikpScratch24_ok_entails_mem48 (sp' v w : BitVec 64) :
    ((sp' + 96#64) ↦₃₂ 0#32) ∗ ((sp' + 100#64) ↦₃₂ 0#32) ∗
      ((sp' + 104#64) ↦₆₄ v) ∗ ((sp' + 112#64) ↦₆₄ w) ∗
      memRegion (sp' + 120#64) 24 ⊢
      memRegion (sp' + 96#64) 48 := by
  have h0 : ((sp' + 96#64) ↦₃₂ 0#32) ∗ ((sp' + 100#64) ↦₃₂ 0#32) =
      ((sp' + 96#64) ↦₆₄ 0#64) := by
    have hs := (pointsTo64_zero_split32 (sp' + 96#64)).symm
    have ha : sp' + 96#64 + 4#64 = sp' + 100#64 := by bv_omega
    rw [ha] at hs; exact hs
  rw [← sepConj_assoc, h0, ikpMem48_split24 sp',
    Prost.memRegion_split (sp' + 96#64) 8 16 (by decide),
    Prost.memRegion_split (sp' + 96#64 + 8#64) 8 8 (by decide)]
  have ha1 : sp' + 96#64 + 8#64 = sp' + 104#64 := by bv_omega
  have ha2 : sp' + 104#64 + 8#64 = sp' + 112#64 := by bv_omega
  rw [ha1, ha2]
  refine Entails.trans ?_
    (sepConj_mono
      (sepConj_mono (pointsTo64_entails_memRegion (sp' + 96#64) 0#64)
        (sepConj_mono (pointsTo64_entails_memRegion (sp' + 104#64) v)
          (pointsTo64_entails_memRegion (sp' + 112#64) w)))
      (Entails.refl _))
  apply entails_of_eq; ac_rfl

theorem ikpScratch24_err_entails_mem48 (sp' e : BitVec 64) :
    ((sp' + 96#64) ↦₃₂ 1#32) ∗ ((sp' + 100#64) ↦₃₂ 0#32) ∗
      ((sp' + 104#64) ↦₆₄ e) ∗ memRegion (sp' + 112#64) 8 ∗
      memRegion (sp' + 120#64) 24 ⊢
      memRegion (sp' + 96#64) 48 := by
  have h1 : ((sp' + 96#64) ↦₃₂ 1#32) ∗ ((sp' + 100#64) ↦₃₂ 0#32) =
      ((sp' + 96#64) ↦₆₄ 1#64) := by
    have hs := (pointsTo64_one_split32 (sp' + 96#64)).symm
    have ha : sp' + 96#64 + 4#64 = sp' + 100#64 := by bv_omega
    rw [ha] at hs; exact hs
  rw [← sepConj_assoc, h1, ikpMem48_split24 sp',
    Prost.memRegion_split (sp' + 96#64) 8 16 (by decide),
    Prost.memRegion_split (sp' + 96#64 + 8#64) 8 8 (by decide)]
  have ha1 : sp' + 96#64 + 8#64 = sp' + 104#64 := by bv_omega
  have ha2 : sp' + 104#64 + 8#64 = sp' + 112#64 := by bv_omega
  rw [ha1, ha2]
  refine Entails.trans ?_
    (sepConj_mono
      (sepConj_mono (pointsTo64_entails_memRegion (sp' + 96#64) 1#64)
        (sepConj_mono (pointsTo64_entails_memRegion (sp' + 104#64) e)
          (Entails.refl _)))
      (Entails.refl _))
  apply entails_of_eq; ac_rfl

theorem vecHeader_entails_memRegion24 (a cap ptr len : BitVec 64) :
    vecHeader a cap ptr len ⊢ memRegion a 24 := by
  unfold vecHeader
  rw [Prost.memRegion_split a 8 16 (by decide),
    Prost.memRegion_split (a + 8#64) 8 8 (by decide)]
  have ha : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
  rw [ha]
  exact sepConj_mono (pointsTo64_entails_memRegion a cap)
    (sepConj_mono (pointsTo64_entails_memRegion (a + 8#64) ptr)
      (pointsTo64_entails_memRegion (a + 16#64) len))

theorem vecU8At_eq_header_buf (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A a cap ptr bs = vecHeader a cap ptr (BitVec.ofNat 64 bs.length) ∗ vecU8Buf A cap ptr bs :=
  rfl

theorem ikpFold144 (sp' pkCap pkPtr pkLen skCap skPtr skLen : BitVec 64) :
    memRegion sp' 32 ∗
      memRegion (sp' + 32#64) 16 ∗
      vecHeader (sp' + 48#64) pkCap pkPtr pkLen ∗
      vecHeader (sp' + 72#64) skCap skPtr skLen ∗
      memRegion (sp' + 96#64) 48 ⊢
      memRegion sp' 144 := by
  rw [Prost.memRegion_split sp' 32 112 (by decide),
    Prost.memRegion_split (sp' + 32#64) 16 96 (by decide),
    Prost.memRegion_split (sp' + 32#64 + 16#64) 24 72 (by decide),
    Prost.memRegion_split (sp' + 32#64 + 16#64 + 24#64) 24 48 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (Entails.refl _)
    (sepConj_mono (Entails.refl _)
      (sepConj_mono (vecHeader_entails_memRegion24 (sp' + 48#64) pkCap pkPtr pkLen)
        (sepConj_mono (vecHeader_entails_memRegion24 (sp' + 72#64) skCap skPtr skLen)
          (Entails.refl _))))

/-! ## DecodeError cleanup tail (`+616 .. +684` → `+812`) & `DecodeError::from` / `push` -/

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.IkpTryFrom
