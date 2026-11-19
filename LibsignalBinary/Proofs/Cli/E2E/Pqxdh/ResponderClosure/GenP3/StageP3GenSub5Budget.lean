/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropSessionStructure3 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.AllocContractsMem4KBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenSub5
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyBase
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.SetState4KBudget
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Drops.Common
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- shake: keep

/-!
# Budget-Threaded Stage P3 Substage P3.5 (`Ok` and Duplicate Error)

Proves `RustCliAllocBudget M` / `VmPreserved` Substage P3.5 theorems on
`tripleRatchetProgAtExt b ext`, composing the post-`tryDecrypt` basic blocks with
`set_session_state_ok_ext_4k` and `drop_session_structure3_ok_ext_4k` for the `Ok pt` path
(`+0x1cd8 → +0x34dc`) and duplicate-message error exit (`+0x1cd8 → s0.readReg64 .x30`).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenSub5Budget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters hiding
  dropChainSpec dropProtoChainSpec dropVecMessageKeySpec dropVecChainSpec
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees hiding
  dropSessionStructureLocal1Spec dropSessionStructureLocal2Spec setSessionStateSpec growOneSpeSpec
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.DropsCommon
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget
  VmPreserved rustAllocEvents
)

open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtBudget (dropSessionStructureLocal2SpecBase)


open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  GrowOneSpeEnv growOneSpeSpec setSessionStateSpec
)

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem sepWP_swap_vm {prog : Program} {target_pc : BitVec 64} {s : State} {P : SepProp}
    {P_post : SepProp} {Q_regs : State → Prop}
    (h : SepWP prog target_pc s P (fun sm Pf => VmPreserved s sm ∧ (Pf ⊢ P_post) ∧ Q_regs sm)) :
    SepWP prog target_pc s P (fun sm Pf => (Pf ⊢ P_post) ∧ VmPreserved s sm ∧ Q_regs sm) :=
  SepWP.mono h (fun _ _ _ _ ⟨hvm, hent, hrest⟩ => ⟨hent, hvm, hrest⟩)

private theorem ret_sepWPp_frame_evs {prog : Program} {ret : BitVec 64} {s0 s : State}
    {P P_stage F : SepProp} {P_stage_post : List AllocEvent → State → SepProp}
    {Q_regs : List AllocEvent → State → Prop} {Q : State → SepProp → Prop}
    (hstage : SepWPp prog ret s P_stage
      (fun sf P_m => ∃ evs : List AllocEvent,
        FreeOnlyEvs evs ∧ (P_m ⊢ P_stage_post evs sf) ∧ Q_regs evs sf)
      (PanicOomProp s0))
    (hP : P = P_stage ∗ F)
    (hret : ∀ (sf : State) (P_m : SepProp) (evs : List AllocEvent),
      sf.pc = ret → sf.status = .Running → FreeOnlyEvs evs →
      (P_m ∗ F ⊢ P_stage_post evs sf ∗ F) → Q_regs evs sf → Q sf (P_m ∗ F)) :
    SepWPp prog ret s P Q (PanicOomProp s0) :=
  P3P4.SepWPp.bind_sepWPp_frame_raw hstage hP
    fun sf P_m hpc hrun ⟨evs, hevs, hent, hregs⟩ =>
      SepWPp.done hpc hrun (hret sf P_m evs hpc hrun hevs (sepConj_mono_left hent) hregs)

theorem growOneSpe_pre_zero_eq (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (v ptr : BitVec 64)
    (hx0 : s.readReg64 .x0 = v) (hptr : ptr ≠ 0)
    (hfits : FitsEnv M lim st (GrowOneSpeEnv 0#64)) :
    (growOneSpeSpec M A lim).pre ((v, 0#64, ptr, []), st) s =
      (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ A.pool lim st s ∗ stackAt s.sp growOneSpeStack := by
  dsimp only [growOneSpeSpec]
  have hp : (s.readReg64 .x0 = v ∧ ([] : List (BitVec 8)).length = (0#64 : BitVec 64).toNat * 48 ∧
      ptr ≠ 0 ∧ max (2 * (0#64 : BitVec 64).toNat) 4 * 48 + 8 ≤ 2 ^ 63 ∧
      FitsEnv M lim st (GrowOneSpeEnv 0#64)) = True :=
    propext ⟨fun _ => trivial, fun _ => ⟨hx0, rfl, hptr, by decide, hfits⟩⟩
  have hif : ((0#64 : BitVec 64) = 0) = True := propext ⟨fun _ => trivial, fun _ => rfl⟩
  simp only [hp, pure_true, hif, ite_true, emp_sepConj, sepConj_emp, sepConj_assoc]

theorem growOneSpe_post_zero_eq (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s0 sf : State) (v ptr : BitVec 64) :
    (growOneSpeSpec M A lim).post ((v, 0#64, ptr, []), st) s0 sf =
      ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ p' : BitVec 64,
        ⌜p' ≠ 0 ∧ p'.toNat % 8 = 0⌝ ∗ (v ↦₆₄ 4#64) ∗ ((v + 8#64) ↦₆₄ p') ∗
        A.live p' 192 8 ∗ memRegion p' 192) ∗
      A.pool lim (M.stepEvents (rustAllocEvents 192 8) st) sf ∗
      stackAt s0.sp growOneSpeStack := by
  dsimp only [growOneSpeSpec]
  have h0 : (0#64 : BitVec 64).toNat = 0 := rfl
  simp only [h0, Nat.mul_zero, Nat.sub_zero, show max 0 4 = 4 from rfl,
    show 4 * 48 = 192 from rfl, show ([] : List (BitVec 8)).length = 0 from rfl,
    BitVec.ofNat_eq_ofNat, BitVec.add_zero, pointsToBytes_nil,
    emp_sepConj, sepConj_emp]
  apply Entails.antisymm
  · apply Entails.sepExists_elim
    intro evs
    apply Entails.pure_left
    rintro ⟨htr, ⟨_, rfl⟩ | ⟨hne, _⟩⟩
    · exact Entails.pure_right htr (Entails.refl _)
    · exact False.elim (hne rfl)
  · apply Entails.pure_left
    intro htr
    refine Entails.sepExists_right (rustAllocEvents 192 8) ?_
    exact Entails.pure_right ⟨htr, Or.inl ⟨rfl, rfl⟩⟩ (Entails.refl _)

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenSub5Budget
