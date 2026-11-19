/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Defs
import ProofLib
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.MergeSenderChainAux.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.RegChain
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# Tag-6 Leaf (`mergeFieldGenSenderChain_ok`) for `SessionStructure::merge_field`

Proves `mergeFieldGenSenderChain_ok` for `sender_chain` (tag `6`), writing `Chain::default()` at
`ss + 0x90` when `sender = none` and invoking `message::merge<Chain>`.
-/

public section

namespace CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenSenderChain

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.Serialization (allocPanic)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite isCalleeSavedVReg

@[local arm64_norm, local wp_norm]
private theorem calleeSavedVRegs_setPC_pre_mf6g (s : State) (v : BitVec 64) :
    calleeSavedVRegs (s.setPC v) = calleeSavedVRegs s := rfl

@[local arm64_norm, local wp_norm]
private theorem calleeSavedVRegs_setMem_setPC_pre_mf6g (s : State) (v : BitVec 64) (m : Memory) :
    calleeSavedVRegs ((s.setPC v).setMem m) = calleeSavedVRegs s := rfl

@[local arm64_norm]
private theorem bv_add_neg240_mf6g (sp0 : BitVec 64) :
    sp0 + bv% (2 ^ 64 - 240) = sp0 - 240#64 := by
  simp only [BitVec.sub_eq_add_neg]
  rfl

-- Pre-indexed load (`ldr x8, [x1, #0x90]!` at +0x10c) applies `setPC` before reading/writing
-- registers; commute register/SP reads past `setPC` and `setMem`.
@[local arm64_norm, local wp_norm]
private theorem sp_setPC_pre_mf6g (s : State) (v : BitVec 64) : (s.setPC v).sp = s.sp := rfl

@[local arm64_norm, local wp_norm]
private theorem sp_setMem_setPC_pre_mf6g (s : State) (v : BitVec 64) (m : Memory) :
    ((s.setPC v).setMem m).sp = s.sp := rfl

@[local arm64_norm, local wp_norm]
private theorem readReg64_setPC_pre_mf6g (s : State) (v : BitVec 64) (r : Reg) :
    (s.setPC v).readReg64 r = s.readReg64 r := rfl

@[local arm64_norm, local wp_norm]
private theorem readReg64_setMem_setPC_pre_mf6g (s : State) (v : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC v).setMem m).readReg64 r = s.readReg64 r := rfl

@[local arm64_norm, local wp_norm]
private theorem readReg32_setPC_pre_mf6g (s : State) (v : BitVec 64) (r : Reg) :
    (s.setPC v).readReg32 r = s.readReg32 r := rfl

@[local arm64_norm, local wp_norm]
private theorem readReg32_setMem_setPC_pre_mf6g (s : State) (v : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC v).setMem m).readReg32 r = s.readReg32 r := rfl

@[local arm64_norm, local wp_norm]
private theorem readReg_setPC_pre_mf6g (s : State) (v : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC v).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm, local wp_norm]
private theorem readReg_setMem_setPC_pre_mf6g (s : State) (v : BitVec 64) (m : Memory)
    (w : RegWidth) (r : Reg) :
    ((s.setPC v).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

private theorem sepWPp_mono_pre_mf6g {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop}
    (hent : P ⊢ P') (h : SepWPp prog ret s P' Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  exact h R (Satisfies.mono (sepConj_mono_left hent) hm) hL

private theorem sepWPp_drop_left_mf6g {prog : Program} {ret : BitVec 64} {s : State}
    {P1 P2 : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P2 Q Qp) :
    SepWPp prog ret s (P1 ∗ P2) Q Qp := by
  intro R hm hL
  rw [sepConj_assoc] at hm
  exact h _ (Satisfies.of_sep_right hm) hL

private theorem setWidth8_setWidth64_setWidth32_mf6g (v : BitVec 64) :
    (((v.setWidth 32).setWidth 64).setWidth 8) = v.setWidth 8 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  omega

private theorem genField_eq_sender_of_tag_eq_6 {fl : GenField} (h : fl.tag = 6) :
    ∃ c : ChainG, fl = .sender c := by
  cases fl <;> simp [GenField.tag] at h
  rename_i c
  exact ⟨c, rfl⟩

/-- All fields of `prostSSGAt A ss v` except `sender` at `ss + 0x90`. -/
@[expose] def prostSSGRest (A : RustAlloc) (ss : BitVec 64) (v : SSG) : SepProp :=
  vecU8 A ss v.lik ∗ vecU8 A (ss + 0x18#64) v.rik ∗ vecU8 A (ss + 0x30#64) v.root ∗
    vecOf A 104 8 (fun c a => prostChainGAt A a c) (ss + 0x48#64) v.recv ∗
    vecU8 A (ss + 0x60#64) [] ∗ vecU8 A (ss + 0x78#64) [] ∗
    (match v.pending with
     | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
     | some k => vecU8 A (ss + 0xf8#64) k ∗ ((ss + 0x110#64) ↦₃₂ 0#32) ∗
         memRegion (ss + 0x114#64) 4 ∗ ((ss + 0x118#64) ↦₆₄ 0#64) ∗
         ((ss + 0x120#64) ↦₃₂ 0#32) ∗ memRegion (ss + 0x124#64) 4) ∗
    ((ss + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x130#64) 24 ∗
    ((ss + 0x148#64) ↦₃₂ v.version) ∗ ((ss + 0x14c#64) ↦₃₂ v.prevCounter) ∗
    ((ss + 0x150#64) ↦₆₄ 0#64)

theorem prostSSGAt_sender_none_eq (A : RustAlloc) (ss : BitVec 64) (v : SSG)
    (hnone : v.sender = none) :
    prostSSGAt A ss v =
      ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96 ∗ prostSSGRest A ss v := by
  unfold prostSSGAt prostSSGRest
  rw [hnone]
  dsimp only
  ac_rfl

theorem prostSSGAt_sender_some_eq (A : RustAlloc) (ss : BitVec 64) (v : SSG) (c : ChainG) :
    prostSSGAt A ss (v.apply (.sender c)) =
      prostChainGAt A (ss + 0x90#64) c ∗ prostSSGRest A ss v := by
  rcases v with ⟨ver, lik, rik, root, prevCounter, recv, sender, pending⟩
  unfold prostSSGAt prostSSGRest SSG.apply
  dsimp only
  ac_rfl

theorem empty_vecOf_msgKey_entails (A : RustAlloc) (v a8 a16 : BitVec 64)
    (h8 : v + 8#64 = a8) (h16 : v + 16#64 = a16) :
    (v ↦₆₄ 0#64) ∗ (a8 ↦₆₄ 8#64) ∗ (a16 ↦₆₄ 0#64) ⊢
      vecOf A 104 8 (fun mk b => prostMsgKeyAt A mk b) v [] := by
  unfold vecOf
  refine Entails.sepExists_right 0#64 (Entails.sepExists_right 8#64 ?_)
  unfold vecAt vecHeader vecBuf
  subst h8 h16
  have hp : (⌜([] : List MessageKeyGenerator).length ≤ (0#64 : BitVec 64).toNat ∧
      (0#64 : BitVec 64).toNat * 104 < 2 ^ 63 ∧ (8#64 : BitVec 64) ≠ 0⌝ : SepProp) = emp := by
    simp
  rw [hp]
  simp only [emp_sepConj]
  exact Entails.of_eq (by ac_rfl)

theorem default_cells_entail_prostChainGAt (A : RustAlloc) (ss : BitVec 64) :
    ((ss + 144#64) ↦₆₄ 0#64) ∗ ((ss + 152#64) ↦₆₄ 1#64) ∗ ((ss + 160#64) ↦₆₄ 0#64) ∗
    ((ss + 168#64) ↦₆₄ 0#64) ∗ ((ss + 176#64) ↦₆₄ 1#64) ∗ ((ss + 184#64) ↦₆₄ 0#64) ∗
    ((ss + 192#64) ↦₆₄ 0#64) ∗ ((ss + 200#64) ↦₆₄ 8#64) ∗ ((ss + 208#64) ↦₆₄ 0#64) ∗
    ((ss + 216#64) ↦₆₄ noneCap) ∗ memRegion (ss + 224#64) 24 ⊢
      prostChainGAt A (ss + 0x90#64) ChainG.empty := by
  unfold prostChainGAt ChainG.empty
  dsimp only
  have hv1 := empty_vecU8_entails_senderChain A (ss + 144#64) (ss + 152#64) (ss + 160#64)
    (by rw [BitVec.add_assoc]; rfl) (by rw [BitVec.add_assoc]; rfl)
  have hv2 := empty_vecU8_entails_senderChain A (ss + 144#64 + 0x18#64) (ss + 176#64) (ss + 184#64)
    (by simp only [BitVec.add_assoc]; rfl) (by simp only [BitVec.add_assoc]; rfl)
  have hv3 := empty_vecOf_msgKey_entails A (ss + 144#64 + 0x30#64) (ss + 200#64) (ss + 208#64)
    (by simp only [BitVec.add_assoc]; rfl) (by simp only [BitVec.add_assoc]; rfl)
  have ha2 : ss + 144#64 + 0x18#64 = ss + 168#64 := by rw [BitVec.add_assoc]; rfl
  have ha3 : ss + 144#64 + 0x30#64 = ss + 192#64 := by rw [BitVec.add_assoc]; rfl
  have ha4 : ss + 0x90#64 + 0x48#64 = ss + 216#64 := by rw [BitVec.add_assoc]; rfl
  have ha5 : ss + 0x90#64 + 0x50#64 = ss + 224#64 := by rw [BitVec.add_assoc]; rfl
  rw [ha2] at hv2
  rw [ha3] at hv3
  rw [ha2, ha3, ha4, ha5]
  refine Entails.trans ?_
    (sepConj_mono hv1 (sepConj_mono hv2 (sepConj_mono hv3 (Entails.refl _))))
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenSenderChain
