/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.Phase -- proof-setup: allow-public-import
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep -- proof-setup: allow-public-import
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp
public import Arm64.Trusted.Object.Labels
public import ProofLib.Placed
public import ProofLib.Placed.LabelsCheck
public import ProofLib.Placed.LabelsCoverage
public import ProofLib.Placed.LabelsInterned
public import ProofLib.Placed.SharedCode
public import ProofLib.Process.FsLemmas
public import ProofLib.StdStartup.MemOps
public import VerifiedLibraries.RustStd.Proofs.ExecSegSym

/-!
# Budget-Threaded Phase Composition for `<spqr::encoding::polynomial::Poly>::compute_at`

Threads `RustCliAllocBudget M` and `VmPreserved` through the power-table phase, dot-product phase,
and `__rust_dealloc` epilogue on Block `371`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.PhaseBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkLib_eq_371 blkPC_371 blkPl_371
   lsmpl lsρ sepWP_seq_lscl withMemEq)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalSpqrV1 (GF16 tokenName tokenStorageName)
open CryptoVerification.SpqrV1.Alloc (growOneStack)
open CryptoVerification.SpqrV1.GF.Mul2U16
  (OnceCallHookOk tokenInitPlacedAt zeroExtend_16_truncate_32_64)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
  (reduceTablePlacedAt reduceTableSym sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre
   readReg64_setMem_setPC_pre readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre
   readReg_setMem_setPC_pre)
open CryptoVerification.SpqrV1.Poly (gf16SliceAt)
open CryptoVerification.SpqrV1.Poly.LagrangePrepare (aligned16_add_mul_two)
open CryptoVerification.SpqrV1.Poly.ComputeAt
  (ComputeAtArgs combine_two_gf16 computeAtPowersPure computeAtPowersPure_length computeAtPure
   computeAtPure_nil computeAtStack dot_from_61ab4_placed_vm_sepWP
   gf16Slice2_rest4_entails_memRegion8 gf16SliceAt_entails_memRegion
   insert_emp_memRegion_after_w1 ofNat_beq_false_of_lt ofNat_shl_one ofNat_shl_one_bv
   ofNat_two_mul_toNat powersLoopPure powersLoop_placed_vm_sepWP
   readReg32_setMem_pre readReg64_setMem_pre readReg_setMem_pre sp_setMem_pre spqrRustDeallocSym
   stackAt_computeAt_merge stackAt_growOne_eq_allocHook stackAt_growOne_merge_allocHook
   truncate16_zext64_trunc32 ult_three_false_of_ge ult_three_of_lt zext16_xor_trunc32)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved
   rustCliDeallocBudgetSpec rustDeallocEvents)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

private theorem pc_setMem_pre (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by cases s; rfl
private theorem status_setMem_pre (s : State) (m : Memory) : (s.setMem m).status = s.status := by
  cases s; rfl
private theorem pstate_setMem_pre (s : State) (m : Memory) : (s.setMem m).pstate = s.pstate := by
  cases s; rfl
private theorem trace_setMem_pre (s : State) (m : Memory) : (s.setMem m).trace = s.trace := by
  cases s; rfl
private theorem calleeSavedVRegs_setMem_pre (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by cases s; rfl

private theorem sepWP_expose_state {prog : Program} {tgt : BitVec 64} {s : State}
    {P : SepProp} {Q : State → SepProp → Prop}
    (h : ∀ s', s' = s → SepWP prog tgt s' P Q) : SepWP prog tgt s P Q :=
  h s rfl

private theorem sepWP_grab_acp {prog : Program} {tgt : BitVec 64} {s0 s_call sf_call : State}
    {P : SepProp} {Q : State → SepProp → Prop}
    (hacp : AllocCallPreserved s_call sf_call) (htr : s_call.trace = s0.trace)
    (h : sf_call.trace = s0.trace → SepWP prog tgt sf_call P Q) :
    SepWP prog tgt sf_call P Q :=
  h (hacp.2.1.trans htr)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre
  pc_setMem_pre status_setMem_pre pstate_setMem_pre trace_setMem_pre calleeSavedVRegs_setMem_pre
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre
attribute [local arm64_norm, local wp_norm]
  zeroExtend_16_truncate_32_64
  ofNat_shl_one ofNat_shl_one_bv zext16_xor_trunc32
  Arm64.Obj.pageOf_add_lo12Of

/-- Sequence a zero-panic, zero-OOM `subroutine_ok` call under `LibsignalCodeLoaded` before a
`SepWP` continuation into `SepWPp` (budget counterpart of `SepWPp.call_panic_to_sepWP_lscl`). -/
theorem call_noPanic_to_sepWP_lscl [LibsignalPlacement]
    {α : Type} {prog : Program} {entry ret_pc ret : BitVec 64}
    {s : State} {spec : Spec α} {x : α} {φ : Prop} {T F P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hcall : subroutine_ok prog entry (withMemEq s.mem spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan : ∀ sf R', sf.status = .Panicked → (sf.mem ⊨ spec.onPanic x s sf ∗ R') → False)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → False)
    (hnext : ∀ sf : State, LibsignalCodeLoaded lsmpl sf.mem →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWP prog ret sf (spec.post x s sf ∗ F) Q) :
    SepWPp prog ret s P Q Qp := by
  intro R' hm hL
  have hpre : s.mem ⊨ (withMemEq s.mem spec).pre x s ∗ (F ∗ R') := by
    dsimp only [withMemEq]
    rw [hspec, show ((⌜φ⌝ ∗ T) ∗ ⌜s.mem = s.mem⌝) ∗ (F ∗ R') =
      ⌜φ ∧ s.mem = s.mem⌝ ∗ ((T ∗ F) ∗ R') by rw [← pure_sepConj_pure]; sep_ac_rfl,
      ← hP, satisfies_pure_sepConj]
    exact ⟨⟨hφ, rfl⟩, hm⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R') s hpc hrun hpre hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom_st, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hclm := hcl.of_keepsFrozen hsteps.keepsFrozen
    obtain ⟨sf, hsteps', hout'⟩ :=
      SepWPp.of_sepWP_ret (Qp := Qp) (hnext sm hclm hpcm hrunm hspm hcsm) R' hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact (hpan sm (F ∗ R') hpan_st hpost).elim
  · exact (hexit sm code (F ∗ R') hex hpost).elim
  · exact (hoom sm R' hoom_st hpost).elim

set_option maxHeartbeats 1600000 in
/-- Deallocation epilogue (`+0x268..+0x2a0`) on Block `371`, stepping `st` by `rustDeallocEvents (2 * cap_xs) 2`. -/
theorem epilogue_dealloc_placed_sepWP [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (a : ComputeAtArgs) (R : SepProp) (s0 sf : State)
    (cap_xs : Nat) (hcap_pos : 0 < cap_xs) (hcap_bound : 2 * cap_xs + 2 ≤ 2 ^ 63)
    (p_xs : BitVec 64) (_hp_xs_ne : p_xs ≠ 0#64)
    (v120 : BitVec 64)
    (hpc : sf.pc = (blkPl_371).base + 616#64)
    (hrun : sf.status = .Running)
    (hsp : sf.sp = s0.sp - 144#64)
    (hsp0 : s0.sp &&& 0xf#64 = 0#64)
    (htr : sf.trace = s0.trace)
    (hvregs0 : calleeSavedVRegs sf = calleeSavedVRegs s0)
    (hx20 : BitVec.truncate 16 (sf.readReg64 .x20) = (computeAtPure a.poly a.x).value) :
    SepWP ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) sf
      (memRegion p_xs (2 * cap_xs) ∗
       gf16SliceAt a.p_coeffs a.poly.coefficients ∗
       tokenInitPlacedAt ∗
       reduceTablePlacedAt ∗
       A.live p_xs (2 * cap_xs) 2 ∗
       A.pool lim st sf ∗
       stackAt (s0.sp - 144#64) growOneStack ∗
       memRegion (s0.sp - 144#64) 8 ∗
       ((s0.sp - 136#64) ↦₆₄ BitVec.ofNat 64 cap_xs) ∗
       ((s0.sp - 128#64) ↦₆₄ p_xs) ∗
       ((s0.sp - 120#64) ↦₆₄ v120) ∗
       memRegion (s0.sp - 112#64) 16 ∗
       ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
       ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
      (fun sf1 P_f =>
        ((sf1.mem ⊨ P_f ∗ R) →
          (sf1.mem ⊨
            ⌜sf1.trace = s0.trace ∧
              BitVec.truncate 16 (sf1.readReg64 .x0) = (computeAtPure a.poly a.x).value ∧
              M.liveBytes (M.stepEvents (rustDeallocEvents (2 * cap_xs) 2) st) ≤ M.liveBytes st⌝ ∗
             gf16SliceAt a.p_coeffs a.poly.coefficients ∗
             tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
             A.pool lim (M.stepEvents (rustDeallocEvents (2 * cap_xs) 2) st) sf1 ∗
             stackAt s0.sp computeAtStack ∗ R)) ∧
          sf1.sp = s0.sp ∧ CalleeSavedPreserved s0 sf1) := by
  rcases ofNat_beq_false_of_lt hcap_pos (by omega) with ⟨_, _, hcap_ne0, _⟩
  have htoNat_cap : (BitVec.ofNat 64 (2 * cap_xs)).toNat = 2 * cap_xs :=
    ofNat_two_mul_toNat cap_xs (by omega)
  dsimp only [rustCliDeallocBudgetSpec] at hdealloc
  wp_conv_pre => rw [stackAt_growOne_eq_allocHook (s0.sp - 144#64), ← hsp]
  wp_steps 6
  wp_call hdealloc (p_xs, 2 * cap_xs, 2, st)
  have hlive_le :
      M.liveBytes (M.stepEvents (rustDeallocEvents (2 * cap_xs) 2) st) ≤ M.liveBytes st :=
    hpost
  refine sepWP_grab_acp (s0 := s0) (by assumption)
    (by simpa [wp_norm, arm64_norm] using htr) fun htr_ret => ?_
  wp_conv_pre => rw [hsp, stackAt_growOne_merge_allocHook (s0.sp - 144#64)]
  wp_steps 9
  apply SepWP.fold
    (stackAt_computeAt_merge s0.sp (s0.sp - 144#64)
      (BitVec.ofNat 64 cap_xs) p_xs v120
      (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28) (s0.readReg64 .x27)
      (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24) (s0.readReg64 .x23)
      (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19) rfl)
    (by sep_focus)
  have hsp_ret : sf_1.sp + 144#64 = s0.sp := by
    rw [hsp_sf, hsp, BitVec.sub_add_cancel]
  have hx0_ret :
      BitVec.truncate 16 (BitVec.zeroExtend 64 (BitVec.truncate 32 (sf_1.readReg64 .x20))) =
        (computeAtPure a.poly a.x).value := by
    rw [truncate16_zext64_trunc32, h_1, hx20]
  have hvregs_ret : calleeSavedVRegs sf_1 = calleeSavedVRegs s0 := by
    rw [hvregs, hvregs0]
  wp_done

/-! ## Budget-Threaded Relocatable `[LibsignalPlacement]` Phase Lemmas -/

set_option maxHeartbeats 1600000 in
/-- Power-table phase (`+0x60..+0x1a0`) on Block `371` preserving `VmPreserved s sf`. -/
theorem powers_from_61974_placed_sepWP [LibsignalPlacement]
    (ext : String → Option (State → State))
    (hOnce : OnceCallHookOk (Rust.withPanics ext))
    (a : ComputeAtArgs) (hlen_bound : 2 * a.poly.coefficients.length + 2 ≤ 2 ^ 63)
    (sp0 p_xs : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64) (hp_xs : p_xs &&& 1#64 = 0#64)
    (v_cap : BitVec 64)
    (hcap_ge3 : 3 ≤ a.poly.coefficients.length →
      v_cap = BitVec.ofNat 64 a.poly.coefficients.length)
    (v1 : BitVec 16) (v120 : BitVec 64)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop)
    (s : State) (F : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_371).base + 96#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 144#64)
    (hx0 : s.readReg64 .x0 = p_xs)
    (hx19 : s.readReg64 .x19 = a.p_coeffs)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 a.poly.coefficients.length)
    (hx21 : BitVec.truncate 16 (s.readReg64 .x21) = a.x.value)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hnext : ∀ sf : State,
      LibsignalCodeLoaded lsmpl sf.mem →
      sf.pc = (blkPl_371).base + 416#64 →
      sf.status = .Running →
      sf.sp = sp0 - 144#64 →
      sf.trace = s.trace →
      VmPreserved s sf →
      sf.readReg64 .x1 = BitVec.ofNat 64 (max 2 a.poly.coefficients.length) →
      sf.readReg64 .x19 = a.p_coeffs →
      sf.readReg64 .x20 = BitVec.ofNat 64 a.poly.coefficients.length →
      sf.readReg64 .x23 = lsρ tokenName + 8#64 →
      sf.readReg64 .x24 = lsρ reduceTableSym →
      sf.readReg64 .x25 = Arm64.Obj.pageOf (lsρ tokenStorageName) →
      sf.readReg64 .x27 = p_xs →
      sf.readReg64 .x29 = sp0 - 96#64 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext)) ret_pc sf
        (gf16SliceAt p_xs (computeAtPowersPure a.poly.coefficients.length a.x) ∗
         ((sp0 - 136#64) ↦₆₄ v_cap) ∗
         ((sp0 - 128#64) ↦₆₄ p_xs) ∗
         ((sp0 - 120#64) ↦₆₄ BitVec.ofNat 64 (max 2 a.poly.coefficients.length)) ∗
         memRegion (sp0 - 112#64) 16 ∗
         stackAt (sp0 - 144#64) growOneStack ∗
         tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ F) Q) :
    SepWP ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext)) ret_pc s
      ((p_xs ↦₁₆ 1#16) ∗
       ((p_xs + 2#64) ↦₁₆ v1) ∗
       memRegion (p_xs + 4#64) (2 * (a.poly.coefficients.length - 2)) ∗
       ((sp0 - 136#64) ↦₆₄ v_cap) ∗
       ((sp0 - 128#64) ↦₆₄ p_xs) ∗
       ((sp0 - 120#64) ↦₆₄ v120) ∗
       memRegion (sp0 - 112#64) 16 ∗
       stackAt (sp0 - 144#64) growOneStack ∗
       tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ F) Q := by
  have hal_p2 : MemWidth.isAligned .W16 (p_xs + 2#64) = true :=
    aligned16_add_mul_two p_xs hp_xs 1
  have hsp_al : (s.sp &&& 15#64 == 0#64) = true := by
    rw [hsp, beq_iff_eq]; revert hsp0; bv_bits
  by_cases hlt3 : a.poly.coefficients.length < 3
  · have hult3 : (BitVec.ofNat 64 a.poly.coefficients.length).ult 3#64 = true :=
      ult_three_of_lt a.poly.coefficients.length hlt3
    apply sepWP_seq_lscl (by exact hcl) (mid := (blkPl_371).base + 416#64)
    apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
      (Q := (blkPC_371).rebase (blkPl_371).base
        (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException (Rust.withPanics ext)))
      blkLib_eq_371 (mid := (blkPl_371).base + 416#64)
    intro m_strip
    wp_steps 12
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun m_real hnsp => ?_
    have hvm_f : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro hcl_f
    have hmax2 : max 2 a.poly.coefficients.length = 2 := by omega
    have hsub2 : a.poly.coefficients.length - 2 = 0 := by omega
    have hle2 : a.poly.coefficients.length ≤ 2 := by omega
    have hpow_le2 : computeAtPowersPure a.poly.coefficients.length a.x = [GF16.ONE, a.x] := by
      unfold computeAtPowersPure
      simp [hle2]
    wp_conv_pre =>
      rw [hsub2, Nat.mul_zero, memRegion_zero, emp_sepConj,
          combine_two_gf16 p_xs a.x, ← hpow_le2]
    rw [hmax2] at hnext
    apply hnext _ hcl_f
    · wp_norm_lhs
    · wp_norm_lhs
    · simpa [arm64_norm, wp_norm] using hsp
    · wp_norm_lhs
    · exact hvm_f
    · wp_norm_lhs
    · simpa [arm64_norm, wp_norm] using hx19
    · simpa [arm64_norm, wp_norm] using hx20
    · wp_norm_lhs
    · wp_norm_lhs
    · wp_norm_lhs
    · wp_norm_lhs
    · simpa [arm64_norm, wp_norm] using hx29
    · wp_norm_lhs
  · have hge3 : 3 ≤ a.poly.coefficients.length := by omega
    have hult3 : (BitVec.ofNat 64 a.poly.coefficients.length).ult 3#64 = false :=
      ult_three_false_of_ge a.poly.coefficients.length hge3 hlen_bound
    have hv_cap := hcap_ge3 hge3
    subst hv_cap
    apply sepWP_seq_lscl (by exact hcl) (mid := (blkPl_371).base + 216#64)
    apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
      (Q := (blkPC_371).rebase (blkPl_371).base
        (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException (Rust.withPanics ext)))
      blkLib_eq_371 (mid := (blkPl_371).base + 216#64)
    intro m_strip
    wp_steps 19
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun m_real hnsp => ?_
    have hvm_mid : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro hcl_mid
    have hrem_eq : a.poly.coefficients.length - 2 = (a.poly.coefficients.length - 3) + 1 := by omega
    wp_conv_pre =>
      rw [combine_two_gf16 p_xs a.x, hrem_eq,
          show p_xs + 4#64 = p_xs + BitVec.ofNat 64 (2 * 2) from rfl]
    apply powersLoop_placed_vm_sepWP ext hOnce sp0 p_xs hsp0 hp_xs
      a.poly.coefficients.length hlen_bound ret_pc Q
      (a.poly.coefficients.length - 3) 2 [GF16.ONE, a.x]
      (by omega) (by omega) (by rfl) _ F (by exact hcl_mid)
      (by wp_norm_lhs)
      (by wp_norm_lhs)
      (by simpa [arm64_norm, wp_norm] using hsp)
      (by wp_norm_lhs)
      (by simpa [arm64_norm, wp_norm] using hx20)
      (by wp_norm_lhs)
      (by wp_norm_lhs)
      (by wp_norm_lhs)
      (by wp_norm_lhs)
      (by wp_norm_lhs)
      (by wp_norm_lhs)
      (by simpa [arm64_norm, wp_norm] using hx29)
    intro sf hcl_f hpc_f hrun_f hsp_f htr_f hvm_f hx1_f hx19_f hx20_f hx23_f hx24_f hx25_f hx27_f hx29_f hvregs_f
    have hmax_ge3 : max 2 a.poly.coefficients.length = a.poly.coefficients.length := by omega
    have hnot_le2 : ¬ a.poly.coefficients.length ≤ 2 := by omega
    have hpow_ge3 :
        powersLoopPure 2 (a.poly.coefficients.length - 3 + 1) [GF16.ONE, a.x] =
          computeAtPowersPure a.poly.coefficients.length a.x := by
      unfold computeAtPowersPure
      simp only [hnot_le2, ↓reduceIte,
        show a.poly.coefficients.length - 2 = a.poly.coefficients.length - 3 + 1 by omega]
    wp_conv_pre => rw [hpow_ge3]
    rw [hmax_ge3] at hnext
    exact hnext sf hcl_f hpc_f hrun_f hsp_f
      (by simpa [arm64_norm, wp_norm] using htr_f)
      (hvm_mid.trans hvm_f)
      hx1_f
      (by rw [hx19_f]; simpa [arm64_norm, wp_norm] using hx19)
      hx20_f hx23_f
      (by rw [hx24_f]; wp_norm_lhs)
      hx25_f hx27_f hx29_f
      (by simpa [arm64_norm, wp_norm] using hvregs_f)

set_option maxHeartbeats 1600000 in
/-- Budget-threaded phase composition from `+0x60` to return on Block `371` for `len ≤ 1` (`cap_xs = 4`). -/
theorem from_61974_cap4_placed_sepWP [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    (hOnce : OnceCallHookOk (Rust.withPanics ext))
    (hdealloc : subroutine_ok ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (a : ComputeAtArgs) (R : SepProp) (s0 s : State)
    (hlen_le1 : a.poly.coefficients.length ≤ 1)
    (p_xs : BitVec 64) (hp_xs_ne : p_xs ≠ 0#64) (hp_xs_al : p_xs &&& 1#64 = 0#64)
    (w1 : BitVec 16) (v120 : BitVec 64)
    (hsp0 : s0.sp &&& 0xf#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_371).base + 96#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 144#64)
    (htr : s.trace = s0.trace)
    (hvregs0 : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx0 : s.readReg64 .x0 = p_xs)
    (hx19 : s.readReg64 .x19 = a.p_coeffs)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 a.poly.coefficients.length)
    (hx21 : BitVec.truncate 16 (s.readReg64 .x21) = a.x.value)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) :
    SepWP ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s
      ((p_xs ↦₁₆ 1#16) ∗
       ((p_xs + 2#64) ↦₁₆ w1) ∗
       ((s0.sp - 136#64) ↦₆₄ 4#64) ∗
       ((s0.sp - 128#64) ↦₆₄ p_xs) ∗
       ((s0.sp - 120#64) ↦₆₄ v120) ∗
       tokenInitPlacedAt ∗
       reduceTablePlacedAt ∗
       gf16SliceAt a.p_coeffs a.poly.coefficients ∗
       memRegion (p_xs + 4#64) 4 ∗
       A.live p_xs 8 2 ∗
       A.pool lim st s ∗
       stackAt (s0.sp - 144#64) growOneStack ∗
       memRegion (s0.sp - 144#64) 8 ∗
       memRegion (s0.sp - 112#64) 16 ∗
       ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
       ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
      (fun sf1 P_f =>
        ((sf1.mem ⊨ P_f ∗ R) →
          (sf1.mem ⊨
            ⌜sf1.trace = s0.trace ∧
              BitVec.truncate 16 (sf1.readReg64 .x0) = (computeAtPure a.poly a.x).value ∧
              M.liveBytes (M.stepEvents (rustDeallocEvents 8 2) st) ≤ M.liveBytes st⌝ ∗
             gf16SliceAt a.p_coeffs a.poly.coefficients ∗
             tokenInitPlacedAt ∗
             reduceTablePlacedAt ∗
             A.pool lim (M.stepEvents (rustDeallocEvents 8 2) st) sf1 ∗
             stackAt s0.sp computeAtStack ∗ R)) ∧
        sf1.sp = s0.sp ∧ CalleeSavedPreserved s0 sf1) := by
  wp_conv_pre =>
    rw [insert_emp_memRegion_after_w1 p_xs w1 a.poly.coefficients.length (by omega)]
  apply SepWP.fold (Entails.refl
    ((p_xs ↦₁₆ 1#16) ∗ ((p_xs + 2#64) ↦₁₆ w1) ∗
     memRegion (p_xs + 4#64) (2 * (a.poly.coefficients.length - 2)) ∗
     ((s0.sp - 136#64) ↦₆₄ 4#64) ∗ ((s0.sp - 128#64) ↦₆₄ p_xs) ∗ ((s0.sp - 120#64) ↦₆₄ v120) ∗
     memRegion (s0.sp - 112#64) 16 ∗ stackAt (s0.sp - 144#64) growOneStack ∗
     tokenInitPlacedAt ∗ reduceTablePlacedAt)) (by sep_focus)
  wp_conv_pre => simp only [sepConj_assoc]
  apply powers_from_61974_placed_sepWP ext hOnce a (by omega) s0.sp p_xs hsp0 hp_xs_al
    4#64 (fun h => by omega) w1 v120 (s0.readReg64 Reg.lr) _ s _
    hcl hpc hrun hsp hx0 hx19 hx20 hx21 hx29
  intro sf1 hcl1 hpc1 hrun1 hsp1 htr1 hvm1 hx1_1 hx19_1 hx20_1 hx23_1 hx24_1 hx25_1 hx27_1 hx29_1 hvregs1
  have htr1' : sf1.trace = s0.trace := by rw [htr1, htr]
  have hvregs1' : calleeSavedVRegs sf1 = calleeSavedVRegs s0 := by rw [hvregs1, hvregs0]
  have hlen_pow : (computeAtPowersPure a.poly.coefficients.length a.x).length = 2 := by
    rw [computeAtPowersPure_length]; omega
  by_cases hnil : a.poly.coefficients = []
  · have hlen0 : a.poly.coefficients.length = 0 := by simp [hnil]
    rw [hlen0] at hx1_1 hx20_1
    change sf1.readReg64 .x1 = 2#64 at hx1_1
    change sf1.readReg64 .x20 = 0#64 at hx20_1
    wp_steps 4
    refine sepWP_expose_state fun s2 hs2 => ?_
    have hvm_sf2 : VmPreserved s s2 := by
      rw [hs2]; exact hvm1.trans (by simp only [wp_norm, arm64_norm])
    subst hs2
    apply SepWP.fold
      (gf16Slice2_rest4_entails_memRegion8 p_xs
        (computeAtPowersPure a.poly.coefficients.length a.x) hlen_pow)
      (by sep_focus)
    wp_conv_pre =>
      rw [← A.pool_of_vmPreserved hvm_sf2,
          show memRegion p_xs 8 = memRegion p_xs (2 * 4) from rfl,
          show A.live p_xs 8 2 = A.live p_xs (2 * 4) 2 from rfl,
          show ((s0.sp - 136#64) ↦₆₄ 4#64) = ((s0.sp - 136#64) ↦₆₄ BitVec.ofNat 64 4) from rfl]
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (epilogue_dealloc_placed_sepWP M A lim st ext hdealloc a R s0 _ 4 (by omega) (by omega)
        p_xs hp_xs_ne (BitVec.ofNat 64 (max 2 a.poly.coefficients.length))
        (by wp_norm_lhs) (by wp_norm_lhs) (by simpa [arm64_norm, wp_norm] using hsp1)
        hsp0 (by simpa [arm64_norm, wp_norm] using htr1')
        (by simpa [arm64_norm, wp_norm] using hvregs1') ?_)
    have hp_nil : a.poly = ⟨[]⟩ := by
      cases hp : a.poly with
      | mk cs =>
        have : cs = [] := by simpa [hp] using hnil
        subst this; rfl
    rw [hp_nil, computeAtPure_nil a.x]
    rfl
  · have hlen_pos : 0 < a.poly.coefficients.length := List.length_pos_iff.mpr hnil
    apply SepWP.fold (Entails.refl
      (gf16SliceAt a.p_coeffs a.poly.coefficients ∗
       gf16SliceAt p_xs (computeAtPowersPure a.poly.coefficients.length a.x) ∗
       memRegion (s0.sp - 144#64) 8 ∗ memRegion (s0.sp - 112#64) 16 ∗
       stackAt (s0.sp - 144#64) growOneStack ∗
       tokenInitPlacedAt ∗ reduceTablePlacedAt)) (by sep_focus)
    wp_conv_pre => simp only [sepConj_assoc]
    apply dot_from_61ab4_placed_vm_sepWP ext hOnce a hlen_pos (by omega)
      s0.sp p_xs hsp0 hp_xs_al (s0.readReg64 Reg.lr) _ sf1 _
      (by exact hcl1) hpc1 hrun1 hsp1 hx1_1 hx19_1 hx20_1 hx23_1 hx24_1 hx25_1 hx27_1 hx29_1
    intro sf2 _hcl2 hpc2 hrun2 hsp2 htr2 hvm2 hx20_2 _hx29_2 hvregs2
    have hvm_sf2 : VmPreserved s sf2 := hvm1.trans hvm2
    apply SepWP.fold
      (gf16Slice2_rest4_entails_memRegion8 p_xs
        (computeAtPowersPure a.poly.coefficients.length a.x) hlen_pow)
      (by sep_focus)
    wp_conv_pre =>
      rw [← A.pool_of_vmPreserved hvm_sf2,
          show memRegion p_xs 8 = memRegion p_xs (2 * 4) from rfl,
          show A.live p_xs 8 2 = A.live p_xs (2 * 4) 2 from rfl,
          show ((s0.sp - 136#64) ↦₆₄ 4#64) = ((s0.sp - 136#64) ↦₆₄ BitVec.ofNat 64 4) from rfl]
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (epilogue_dealloc_placed_sepWP M A lim st ext hdealloc a R s0 sf2 4 (by omega) (by omega)
        p_xs hp_xs_ne (BitVec.ofNat 64 (max 2 a.poly.coefficients.length))
        hpc2 hrun2 hsp2 hsp0 (by rw [htr2, htr1']) (by rw [hvregs2, hvregs1']) hx20_2)

set_option maxHeartbeats 1600000 in
/-- Budget-threaded phase composition from `+0x60` to return on Block `371` for `2 ≤ len` (`cap_xs = len`). -/
theorem from_61974_ge2_placed_sepWP [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    (hOnce : OnceCallHookOk (Rust.withPanics ext))
    (hdealloc : subroutine_ok ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (a : ComputeAtArgs) (R : SepProp) (s0 s : State)
    (hlen_ge2 : 2 ≤ a.poly.coefficients.length)
    (hlen_bound : 2 * a.poly.coefficients.length + 2 ≤ 2 ^ 63)
    (p_xs : BitVec 64) (hp_xs_ne : p_xs ≠ 0#64) (hp_xs_al : p_xs &&& 1#64 = 0#64)
    (w1 : BitVec 16) (v120 : BitVec 64)
    (hsp0 : s0.sp &&& 0xf#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_371).base + 96#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 144#64)
    (htr : s.trace = s0.trace)
    (hvregs0 : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx0 : s.readReg64 .x0 = p_xs)
    (hx19 : s.readReg64 .x19 = a.p_coeffs)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 a.poly.coefficients.length)
    (hx21 : BitVec.truncate 16 (s.readReg64 .x21) = a.x.value)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) :
    SepWP ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s
      ((p_xs ↦₁₆ 1#16) ∗
       ((p_xs + 2#64) ↦₁₆ w1) ∗
       memRegion (p_xs + 4#64) (2 * (a.poly.coefficients.length - 2)) ∗
       ((s0.sp - 136#64) ↦₆₄ BitVec.ofNat 64 a.poly.coefficients.length) ∗
       ((s0.sp - 128#64) ↦₆₄ p_xs) ∗
       ((s0.sp - 120#64) ↦₆₄ v120) ∗
       tokenInitPlacedAt ∗
       reduceTablePlacedAt ∗
       gf16SliceAt a.p_coeffs a.poly.coefficients ∗
       A.live p_xs (2 * a.poly.coefficients.length) 2 ∗
       A.pool lim st s ∗
       stackAt (s0.sp - 144#64) growOneStack ∗
       memRegion (s0.sp - 144#64) 8 ∗
       memRegion (s0.sp - 112#64) 16 ∗
       ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
       ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
      (fun sf1 P_f =>
        ((sf1.mem ⊨ P_f ∗ R) →
          (sf1.mem ⊨
            ⌜sf1.trace = s0.trace ∧
              BitVec.truncate 16 (sf1.readReg64 .x0) = (computeAtPure a.poly a.x).value ∧
              M.liveBytes (M.stepEvents (rustDeallocEvents (2 * a.poly.coefficients.length) 2) st) ≤
                M.liveBytes st⌝ ∗
             gf16SliceAt a.p_coeffs a.poly.coefficients ∗
             tokenInitPlacedAt ∗
             reduceTablePlacedAt ∗
             A.pool lim (M.stepEvents (rustDeallocEvents (2 * a.poly.coefficients.length) 2) st) sf1 ∗
             stackAt s0.sp computeAtStack ∗ R)) ∧
        sf1.sp = s0.sp ∧ CalleeSavedPreserved s0 sf1) := by
  apply SepWP.fold (Entails.refl
    ((p_xs ↦₁₆ 1#16) ∗ ((p_xs + 2#64) ↦₁₆ w1) ∗
     memRegion (p_xs + 4#64) (2 * (a.poly.coefficients.length - 2)) ∗
     ((s0.sp - 136#64) ↦₆₄ BitVec.ofNat 64 a.poly.coefficients.length) ∗
     ((s0.sp - 128#64) ↦₆₄ p_xs) ∗ ((s0.sp - 120#64) ↦₆₄ v120) ∗
     memRegion (s0.sp - 112#64) 16 ∗ stackAt (s0.sp - 144#64) growOneStack ∗
     tokenInitPlacedAt ∗ reduceTablePlacedAt)) (by sep_focus)
  wp_conv_pre => simp only [sepConj_assoc]
  apply powers_from_61974_placed_sepWP ext hOnce a hlen_bound s0.sp p_xs hsp0 hp_xs_al
    (BitVec.ofNat 64 a.poly.coefficients.length) (fun _ => rfl) w1 v120
    (s0.readReg64 Reg.lr) _ s _
    hcl hpc hrun hsp hx0 hx19 hx20 hx21 hx29
  intro sf1 hcl1 hpc1 hrun1 hsp1 htr1 hvm1 hx1_1 hx19_1 hx20_1 hx23_1 hx24_1 hx25_1 hx27_1 hx29_1 hvregs1
  have htr1' : sf1.trace = s0.trace := by rw [htr1, htr]
  have hvregs1' : calleeSavedVRegs sf1 = calleeSavedVRegs s0 := by rw [hvregs1, hvregs0]
  have hlen_pow :
      (computeAtPowersPure a.poly.coefficients.length a.x).length =
        a.poly.coefficients.length := by
    rw [computeAtPowersPure_length]; omega
  apply SepWP.fold (Entails.refl
    (gf16SliceAt a.p_coeffs a.poly.coefficients ∗
     gf16SliceAt p_xs (computeAtPowersPure a.poly.coefficients.length a.x) ∗
     memRegion (s0.sp - 144#64) 8 ∗ memRegion (s0.sp - 112#64) 16 ∗
     stackAt (s0.sp - 144#64) growOneStack ∗
     tokenInitPlacedAt ∗ reduceTablePlacedAt)) (by sep_focus)
  wp_conv_pre => simp only [sepConj_assoc]
  apply dot_from_61ab4_placed_vm_sepWP ext hOnce a (by omega) hlen_bound
    s0.sp p_xs hsp0 hp_xs_al (s0.readReg64 Reg.lr) _ sf1 _
    (by exact hcl1) hpc1 hrun1 hsp1 hx1_1 hx19_1 hx20_1 hx23_1 hx24_1 hx25_1 hx27_1 hx29_1
  intro sf2 _hcl2 hpc2 hrun2 hsp2 htr2 hvm2 hx20_2 _hx29_2 hvregs2
  have hvm_sf2 : VmPreserved s sf2 := hvm1.trans hvm2
  have hent_ge2 :
      gf16SliceAt p_xs (computeAtPowersPure a.poly.coefficients.length a.x) ⊢
        memRegion p_xs (2 * a.poly.coefficients.length) := by
    have h := gf16SliceAt_entails_memRegion p_xs
      (computeAtPowersPure a.poly.coefficients.length a.x) (by rw [hlen_pow]; omega)
    rwa [hlen_pow] at h
  apply SepWP.fold hent_ge2 (by sep_focus)
  wp_conv_pre => rw [← A.pool_of_vmPreserved hvm_sf2]
  exact SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (epilogue_dealloc_placed_sepWP M A lim st ext hdealloc a R s0 sf2 a.poly.coefficients.length
      (by omega) hlen_bound p_xs hp_xs_ne
      (BitVec.ofNat 64 (max 2 a.poly.coefficients.length))
      hpc2 hrun2 hsp2 hsp0 (by rw [htr2, htr1']) (by rw [hvregs2, hvregs1']) hx20_2)

end LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.PhaseBudget
