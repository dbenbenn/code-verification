/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.GF.Mul2U16 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.PolyPart1CodeSym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.DefsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget -- proof-setup: allow-public-import
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep -- proof-setup: allow-public-import
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep -- proof-setup: allow-public-import
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Proof
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<Poly>::lagrange_interpolate_prepare`: Budget-Threaded Verification

Relocatable `[LibsignalPlacement]` verification of
`<spqr::encoding::polynomial::Poly>::lagrange_interpolate_prepare` (Block `372`) against
`lagrangePreparePlacedSpec M A lim`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.ProofBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkLib_eq_372 blkPC_372 blkPl_372 lsmpl lsρ
   sepWP_seq_lscl withLsCodeLoaded)
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalSpqrV1 (GF16)
open CryptoVerification.LibsignalTripleRatchet (memsetName)
open CryptoVerification.SpqrV1.Alloc
  (spqrRustAllocSym spqrRustNoAllocShimSym spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.GF.Mul2U16
  (OnceCallHookOk tokenInitPlacedAt zeroExtend_16_truncate_32_64)
open scoped CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open scoped CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.Poly (gf16SliceAt polyOf ptSliceAt)
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
  (LagrangePrepareArgs aligned16_add_mul_two and_65535_zext64_16 and_one_of_mod_two
   combine_init_slice gf16SliceAt_replicate_zero lagrangePreparePure lagrangePreparePure_length
   lagrangePrepareStack len_succ_bit62_false memRegion_24 memRegion_alloc_split
   ofNat_add_one_shl_one ofNat_add_one_shl_one_nat ofNat_shl_one ofNat_shl_one_nat ofNat_shl_two
   ofNat_succ_sub_one_shl_one ofNat_two_mul_succ_toNat ofNat_two_mul_toNat
   outerLoop_placed_vm_sepWP polyOf_of_exact_cap prepareLoopPure prepare_polyReduce_xor_eq
   ptr_sub_two_succ readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre
   readReg64_setPC_pre readReg_setMem_setPC_pre readReg_setPC_pre sbfx64_one_eq sp_setMem_setPC_pre
   sp_setPC_pre stackAt_lagrangePrepare_merge stackAt_lagrangePrepare_split sub_two_toNat_eq
   truncate32_if_all_ones truncate32_sext64_16 truncate32_zext64 zext64_zext32_16)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEvents RustCliAllocBudget RustLayoutOk
   rustAllocEvents rustCliAllocBudgetSpec rustCliAllocNoOomSpec
   subroutine_ok_allocNoOom_of_budget)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.DefsBudget
  (LagrangePrepareEnv lagrangePreparePlacedSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemsetRegionBudgetSpec sessionShimBudgetSpec)

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

private theorem sp_setMem_pre (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by cases s; rfl
private theorem pc_setMem_pre (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by cases s; rfl
private theorem status_setMem_pre (s : State) (m : Memory) : (s.setMem m).status = s.status := by
  cases s; rfl
private theorem pstate_setMem_pre (s : State) (m : Memory) : (s.setMem m).pstate = s.pstate := by
  cases s; rfl
private theorem trace_setMem_pre (s : State) (m : Memory) : (s.setMem m).trace = s.trace := by
  cases s; rfl
private theorem readReg64_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases s; rfl
private theorem readReg32_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by cases s; rfl
private theorem readReg_setMem_pre (s : State) (m : Memory) (w : Width) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by cases s; rfl
private theorem calleeSavedVRegs_setMem_pre (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by cases s; rfl

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre pc_setMem_pre status_setMem_pre pstate_setMem_pre trace_setMem_pre
  readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre calleeSavedVRegs_setMem_pre
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
attribute [local wp_norm] zeroExtend_16_truncate_32_64
attribute [local arm64_norm, local wp_norm]
  ofNat_shl_two truncate32_sext64_16 sbfx64_one_eq
  truncate32_if_all_ones truncate32_zext64 zext64_zext32_16
  and_65535_zext64_16 prepare_polyReduce_xor_eq

/-! ## Budget-Threaded Epilogue & Entry Contract (Block `372`) -/

private theorem epilogue_placed_sepWP [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    (a : LagrangePrepareArgs) (R : SepProp) (s0 s : State)
    (ptr o0 o1 o2 : BitVec 64)
    (v168 v160 v152 v144 : BitVec 64)
    (w132 w128 w124 w120 w116 : BitVec 32)
    (hsp_align : s0.sp &&& 0xf#64 = 0#64)
    (hptr_ne : ptr ≠ 0#64)
    (hpc : s.pc = (blkPl_372).base + 608#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (A.pool lim (M.stepEvents (rustAllocEvents (2 * (a.pts.length + 1)) 2) st) s ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        A.live ptr (2 * (a.pts.length + 1)) 2 ∗
        gf16SliceAt ptr (lagrangePreparePure a.pts).coefficients ∗
        (a.out ↦₆₄ o0) ∗ ((a.out + 8#64) ↦₆₄ o1) ∗ ((a.out + 16#64) ↦₆₄ o2) ∗
        ptSliceAt a.ptsPtr a.pts ∗
        reduceTablePlacedAt ∗
        tokenInitPlacedAt ∗
        memRegion (s0.sp - 208#64) 16 ∗
        ((s0.sp - 192#64) ↦₆₄ ptr) ∗
        ((s0.sp - 184#64) ↦₆₄ a.out) ∗
        ((s0.sp - 176#64) ↦₆₄ BitVec.ofNat 64 (a.pts.length + 1)) ∗
        ((s0.sp - 168#64) ↦₆₄ v168) ∗
        ((s0.sp - 160#64) ↦₆₄ v160) ∗
        ((s0.sp - 152#64) ↦₆₄ v152) ∗
        ((s0.sp - 144#64) ↦₆₄ v144) ∗
        memRegion (s0.sp - 136#64) 4 ∗
        ((s0.sp - 132#64) ↦₃₂ w132) ∗
        ((s0.sp - 128#64) ↦₃₂ w128) ∗
        ((s0.sp - 124#64) ↦₃₂ w124) ∗
        ((s0.sp - 120#64) ↦₃₂ w120) ∗
        ((s0.sp - 116#64) ↦₃₂ w116) ∗
        memRegion (s0.sp - 112#64) 16 ∗
        ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
        ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
        ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
        ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            ∃∗ evs : List AllocEvent,
              ⌜LagrangePrepareEnv a evs ∧ sf.trace = s0.trace⌝ ∗
              polyOf A.repAlloc a.out (lagrangePreparePure a.pts) ∗
              ptSliceAt a.ptsPtr a.pts ∗
              reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
              A.pool lim (M.stepEvents evs st) sf ∗
              stackAt s0.sp lagrangePrepareStack ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  have hbound : 4 * (a.pts.length + 1) < 2 ^ 63 := a.hlen_bound
  have hev : LagrangePrepareEnv a (rustAllocEvents (2 * (a.pts.length + 1)) 2) := rfl
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  simp only [State.setMem_setMem]
  refine SepWP.fold
    (stackAt_lagrangePrepare_merge s0.sp (s0.sp - 208#64)
      ptr a.out (BitVec.ofNat 64 (a.pts.length + 1)) v168 v160 v152 v144
      w132 w128 w124 w120 w116
      (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28) (s0.readReg64 .x27)
      (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24) (s0.readReg64 .x23)
      (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)
      rfl)
    (by sep_focus) ?_
  refine SepWP.fold
    (polyOf_of_exact_cap A.repAlloc a.out ptr (lagrangePreparePure a.pts) (a.pts.length + 1)
      (by omega) (lagrangePreparePure_length a.pts) (by omega) hptr_ne)
    (by dsimp only [RustCliAllocBudget.repAlloc]; sep_focus) ?_
  wp_done

set_option hygiene false in
local macro "wp_steps_rw_pool " mid:term:max stTerm:term:max : tactic => `(tactic| (
  apply sepWP_seg_ls_vm
    (Q := (blkPC_372).rebase (blkPl_372).base (hooksException (Rust.withPanics ext)))
    blkLib_eq_372 (mid := $mid)
  intro _m_strip
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  have _hp := (A.pool_transport lim $stTerm _ _
    (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))).symm
  wp_conv_pre => rw [_hp]
  clear _hp))

set_option maxHeartbeats 800000 in
/-- Relocatable (`[LibsignalPlacement]`) `<spqr::encoding::polynomial::Poly>::lagrange_interpolate_prepare`
(Block `372`) satisfies `lagrangePreparePlacedSpec M A lim`. -/
theorem lagrangePrepare_placed_ok [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (hshim : subroutine_ok ((blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) sessionShimBudgetSpec)
    (halloc : subroutine_ok ((blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hmemset : subroutine_ok ((blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext))
      (lsρ memsetName) sessionMemsetRegionBudgetSpec)
    (hOnce : OnceCallHookOk (Rust.withPanics ext)) :
    subroutine_ok ((blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext))
      (blkPl_372).base (withLsCodeLoaded lsmpl (lagrangePreparePlacedSpec M A lim)) := by
  have halloc' : subroutine_ok ((blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustCliAllocNoOomSpec M A lim false) :=
    subroutine_ok_allocNoOom_of_budget halloc
  dsimp only [sessionShimBudgetSpec] at hshim
  dsimp only [sessionMemsetRegionBudgetSpec] at hmemset
  dsimp only [rustCliAllocNoOomSpec, RustLayoutOk, CryptoVerification.RustHeap.LayoutOk,
    ↓reduceIte] at halloc'
  simp only [withLsCodeLoaded, lagrangePreparePlacedSpec]
  wp_init g s0
  have hcl0 := h; have h := h_1; have h_1 := h_2; have h_2 := h_3; have h_3 := h_4; clear h_4
  rcases g with ⟨a, st⟩
  dsimp only at *
  have hsp0 : s0.sp &&& 0xf#64 = 0#64 := beq_iff_eq.mp hsp_align
  have hbound : 4 * (a.pts.length + 1) < 2 ^ 63 := a.hlen_bound
  have hfits_ev : FitsEvents M lim st (rustAllocEvents (2 * (a.pts.length + 1)) 2) :=
    h _ rfl
  have hfe_raw : FitsEvents M lim st [.alloc (2 * (a.pts.length + 1))] := by
    simpa [rustAllocEvents] using hfits_ev
  rcases hfe_raw with ⟨⟨hwma, henf, hram, hva⟩, -⟩
  have hbit62 : (((BitVec.ofNat 64 a.pts.length + 1#64) &&& 4611686018427387904#64) != 0#64) = false :=
    len_succ_bit62_false a.pts.length hbound
  have hshl_succ : (BitVec.ofNat 64 a.pts.length + 1#64) <<< 1#64 = BitVec.ofNat 64 (2 * (a.pts.length + 1)) :=
    ofNat_add_one_shl_one a.pts.length
  have hshl_succ_nat : (BitVec.ofNat 64 a.pts.length + 1#64) <<< (1 : Nat) = BitVec.ofNat 64 (2 * (a.pts.length + 1)) :=
    ofNat_add_one_shl_one_nat a.pts.length
  have htoNat_succ : (BitVec.ofNat 64 (2 * (a.pts.length + 1))).toNat = 2 * (a.pts.length + 1) :=
    ofNat_two_mul_succ_toNat a.pts.length hbound
  have hpow2 : ∃ k, 2 = 2 ^ k := ⟨1, rfl⟩
  have hpos : 0 < 2 * (a.pts.length + 1) := by omega
  have hal : (2 : Nat) ≤ 2 ^ 31 := by decide
  have hsum : 2 * (a.pts.length + 1) + 2 ≤ 2 ^ 63 := by omega
  have hn_bound : a.pts.length + 1 < 2 ^ 63 := by omega
  have hn_lt64 : a.pts.length < 2 ^ 64 := by omega
  have halloc_le64 : 2 * (a.pts.length + 1) ≤ 2 ^ 64 := by omega
  wp_simp_pre only [memRegion_24 a.out, stackAt_lagrangePrepare_split s0.sp]
  wp_pull_exists
  apply sepWP_seq_lscl hcl0 (mid := (blkPl_372).base + 68#64)
  wp_steps_rw_pool (lsρ spqrRustNoAllocShimSym) st
  simp only [State.setMem_setMem]
  wp_call hshim ()
  have hsp_sf0 : sf.sp = s0.sp - 208#64 := h_6
  have htr_sf0 : sf.trace = s0.trace := h_4
  have hvregs_sf0 : calleeSavedVRegs sf = calleeSavedVRegs s0 := hvregs
  have hp0 := (A.pool_transport lim st _ sf h_5).symm
  wp_conv_pre => rw [hp0]
  clear hp0
  wp_steps_rw_pool (lsρ spqrRustAllocSym) st
  simp only [State.setMem_setMem]
  wp_call halloc' (2 * (a.pts.length + 1), 2, st)
  apply SepWP.done hpc_sf_1 hrun_sf_1
  intro hcl_sf1
  let st1 : M.σ := M.stepEvents (rustAllocEvents (2 * (a.pts.length + 1)) 2) st
  have hsp_sf1 : sf_1.sp = s0.sp - 208#64 := hsp_sf.trans hsp_sf0
  have htr_sf1 : sf_1.trace = s0.trace := by
    refine Eq.trans h_27.2.1 ?_
    simp only [arm64_norm, wp_norm, htr_sf0]
  have hvregs_sf1 : calleeSavedVRegs sf_1 = calleeSavedVRegs s0 := hvregs_1.trans hvregs_sf0
  wp_conv_pre => simp only [hsp_sf0, hsp_sf1]
  have hptr0 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := h_28
  have hptr_mod : (sf_1.readReg64 (Reg.gpr 0#5)).toNat % 2 = 0 := hpost
  have hcbz : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hptr0
  have hptr_al : sf_1.readReg64 (Reg.gpr 0#5) &&& 1#64 = 0#64 :=
    and_one_of_mod_two hptr_mod
  have hlen_add1 : BitVec.ofNat 64 a.pts.length + 1#64 = BitVec.ofNat 64 (a.pts.length + 1) := by
    rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
  by_cases hpts_nil : a.pts = []
  · have hx20_0 : (BitVec.ofNat 64 a.pts.length == 0#64) = true := by rw [hpts_nil]; rfl
    have hmem2 :
        memRegion (sf_1.readReg64 (Reg.gpr 0#5)) (2 * (a.pts.length + 1)) =
          ∃∗ v0 : BitVec 16, (sf_1.readReg64 (Reg.gpr 0#5)) ↦₁₆ v0 := by
      rw [hpts_nil, List.length_nil, Nat.zero_add, Nat.mul_one, memRegion_two]
    wp_conv_pre => rw [hmem2]
    wp_pull_exists
    wp_steps_rw_pool ((blkPl_372).base + 608#64) st1
    simp only [State.setMem_setMem]
    have hslice_nil :
        ((sf_1.readReg64 (Reg.gpr 0#5)) ↦₁₆ 1#16) =
          gf16SliceAt (sf_1.readReg64 (Reg.gpr 0#5)) (lagrangePreparePure a.pts).coefficients := by
      rw [hpts_nil]
      simp [lagrangePreparePure, prepareLoopPure, gf16SliceAt, CryptoVerification.RustHeap.arrayAt,
        CryptoVerification.SpqrV1.Poly.gf16At, GF16.ONE]
    have h176_nil :
        ((s0.sp - 176#64) ↦₆₄ 1#64) =
          ((s0.sp - 176#64) ↦₆₄ BitVec.ofNat 64 (a.pts.length + 1)) := by
      rw [hpts_nil]; rfl
    wp_conv_pre => rw [hslice_nil, h176_nil]
    refine epilogue_placed_sepWP M A lim st ext a R s0 _ (sf_1.readReg64 (Reg.gpr 0#5))
      _ _ _ a.ptsPtr _ _ _ _ _ _ _ _ hsp0 hptr0 ?_ ?_ ?_ ?_ ?_
    · wp_norm_lhs
    · simp only [arm64_norm, wp_norm]; exact hrun_sf_1
    · simp only [arm64_norm, wp_norm, hsp_sf1]
    · simp only [arm64_norm, wp_norm, htr_sf1]
    · simp only [arm64_norm, wp_norm, hvregs_sf1]
  · have hlen_pos : 0 < a.pts.length := List.length_pos_iff.mpr hpts_nil
    have hx20_ne0 : (BitVec.ofNat 64 a.pts.length == 0#64) = false := by
      rw [beq_eq_false_iff_ne]; intro h0
      have ht := congrArg BitVec.toNat h0
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn_lt64] at ht
      exact Nat.ne_of_gt hlen_pos ht
    have hsub_shl :
        (BitVec.ofNat 64 (a.pts.length + 1) + 0xffffffff_ffffffff#64) <<< (1 : Nat) =
          BitVec.ofNat 64 (2 * a.pts.length) :=
      ofNat_succ_sub_one_shl_one a.pts.length
    have htoNat_len : (BitVec.ofNat 64 (2 * a.pts.length)).toNat = 2 * a.pts.length :=
      ofNat_two_mul_toNat a.pts.length hbound
    have hsplit_alloc :
        memRegion (sf_1.readReg64 (Reg.gpr 0#5)) (2 * (a.pts.length + 1)) =
          memRegion (sf_1.readReg64 (Reg.gpr 0#5)) (2 * a.pts.length) ∗
            (∃∗ v_last : BitVec 16,
              (sf_1.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 (2 * a.pts.length)) ↦₁₆ v_last) :=
      memRegion_alloc_split (sf_1.readReg64 (Reg.gpr 0#5)) a.pts.length halloc_le64
    wp_conv_pre => rw [hsplit_alloc]
    wp_pull_exists
    apply sepWP_seq_lscl hcl_sf1 (mid := (blkPl_372).base + 132#64)
    wp_steps_rw_pool (lsρ memsetName) st1
    simp only [State.setMem_setMem]
    wp_call hmemset
    have hsp_sf2 : sf_2.sp = s0.sp - 208#64 := hsp_sf_1.trans hsp_sf1
    have htr_sf2 : sf_2.trace = s0.trace := hpost_1.trans htr_sf1
    have hvregs_sf2 : calleeSavedVRegs sf_2 = calleeSavedVRegs s0 := hvregs_2.trans hvregs_sf1
    have hx20_sf2 : sf_2.readReg64 (Reg.gpr 20#5) = BitVec.ofNat 64 a.pts.length :=
      (h_30.trans h_18).trans h_8
    have hx29_sf2 : sf_2.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64 :=
      (hcs_sf_1.trans hcs_sf).trans hpost_sf
    have hp2 := (A.pool_transport lim st1 _ sf_2 h_39).symm
    wp_conv_pre => rw [hp2]
    clear hp2
    have hrep_zero :
        (sf_1.readReg64 (Reg.gpr 0#5) ↦ₛ
          List.replicate (BitVec.ofNat 64 (2 * (a.pts.length + 1)) - 2#64).toNat 0#8) =
          gf16SliceAt (sf_1.readReg64 (Reg.gpr 0#5)) (List.replicate a.pts.length GF16.ZERO) := by
      rw [sub_two_toNat_eq a.pts.length hbound, gf16SliceAt_replicate_zero]
    have hshl_len : BitVec.ofNat 64 a.pts.length <<< (1 : Nat) = BitVec.ofNat 64 (2 * a.pts.length) :=
      ofNat_shl_one_nat a.pts.length
    have hshl_len' : BitVec.ofNat 64 a.pts.length <<< 1#64 = BitVec.ofNat 64 (2 * a.pts.length) :=
      ofNat_shl_one a.pts.length
    have hal_last :
        MemWidth.isAligned .W16
          (sf_1.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 (2 * a.pts.length)) = true :=
      aligned16_add_mul_two (sf_1.readReg64 (Reg.gpr 0#5)) hptr_al a.pts.length
    wp_steps_rw_pool ((blkPl_372).base + 132#64) st1
    simp only [State.setMem_setMem]
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro hcl_132
    wp_conv_pre => rw [hrep_zero, combine_init_slice]
    apply SepWP.fold (Entails.refl
      (tokenInitPlacedAt ∗
       memRegion (s0.sp - 208#64) 16 ∗
       memRegion (s0.sp - 112#64) 16 ∗
       stackAt (s0.sp - 208#64) allocHookStack ∗
       ((s0.sp - 132#64) ↦₃₂ _) ∗
       ((s0.sp - 128#64) ↦₃₂ _) ∗
       ((s0.sp - 124#64) ↦₃₂ _) ∗
       ((s0.sp - 120#64) ↦₃₂ _) ∗
       ((s0.sp - 116#64) ↦₃₂ _) ∗
       gf16SliceAt (sf_1.readReg64 (Reg.gpr 0#5))
         (List.replicate a.pts.length GF16.ZERO ++ [GF16.ONE]) ∗
       reduceTablePlacedAt ∗
       ((s0.sp - 168#64) ↦₆₄ a.ptsPtr) ∗
       ((s0.sp - 160#64) ↦₆₄ _) ∗
       ((s0.sp - 152#64) ↦₆₄ _) ∗
       ((s0.sp - 144#64) ↦₆₄ _) ∗
       ptSliceAt a.ptsPtr a.pts)) (by sep_focus)
    wp_conv_pre => simp only [sepConj_assoc]
    have hx19_init :
        sf_1.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 (2 * a.pts.length) - 2#64 =
          sf_1.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 (2 * (a.pts.length - 1)) := by
      have hlen_eq : a.pts.length = (a.pts.length - 1) + 1 := (Nat.sub_add_cancel hlen_pos).symm
      conv => lhs; arg 1; arg 2; rw [hlen_eq]
      exact ptr_sub_two_succ (sf_1.readReg64 (Reg.gpr 0#5)) (a.pts.length - 1)
    apply outerLoop_placed_vm_sepWP ext hOnce
      s0.sp (sf_1.readReg64 (Reg.gpr 0#5)) a.ptsPtr
      hsp0 hptr_al a.pts hn_bound (s0.readReg64 Reg.lr) _
      (a.pts.length - 1) 0 ⟨List.replicate a.pts.length GF16.ZERO ++ [GF16.ONE]⟩
      (by rw [Nat.zero_add]; exact Nat.sub_add_cancel hlen_pos) (by simp)
      _ _ _ _ _ _ _ _ _ _ hcl_132
      (by wp_norm_lhs)
      (by wp_norm_lhs)
      (by simp only [arm64_norm, wp_norm, hsp_sf2])
      (by wp_norm_lhs)
      (by simpa [arm64_norm, wp_norm] using hx19_init)
      (by simp only [arm64_norm, wp_norm]; exact hx20_sf2)
      (by wp_norm_lhs)
      (by wp_norm_lhs)
      (by simp only [arm64_norm, wp_norm]; exact hx29_sf2)
    intro v160' v152' v144' w132' w128' w124' w120' w116' sf_loop
      hpc_loop hrun_loop hsp_loop htr_loop hvm_loop hvregs_loop
    have hloop_eq :
        prepareLoopPure a.pts a.pts.length 0 (a.pts.length - 1 + 1)
          ⟨List.replicate a.pts.length GF16.ZERO ++ [GF16.ONE]⟩ =
          lagrangePreparePure a.pts := by
      rw [Nat.sub_add_cancel hlen_pos]; rfl
    have hp_loop := (A.pool_transport lim st1 _ sf_loop hvm_loop).symm
    wp_conv_pre => rw [hp_loop, hloop_eq]
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (epilogue_placed_sepWP M A lim st ext a R s0 sf_loop
        (sf_1.readReg64 (Reg.gpr 0#5))
        _ _ _ a.ptsPtr v160' v152' v144' w132' w128' w124' w120' w116' hsp0 hptr0
        hpc_loop hrun_loop hsp_loop
        (by simp only [arm64_norm, wp_norm, htr_loop, htr_sf2])
        (by simp only [arm64_norm, wp_norm, hvregs_loop, hvregs_sf2]))

theorem lagrangePrepare_placed_ok_of_hookSat [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym
      (rustCliAllocBudgetSpec M A lim false))
    (hmemset : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionBudgetSpec)
    (hOnce : OnceCallHookOk (Rust.withPanics ext)) :
    subroutine_ok ((blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext))
      (blkPl_372).base (withLsCodeLoaded lsmpl (lagrangePreparePlacedSpec M A lim)) :=
  lagrangePrepare_placed_ok M A lim ext
    (spqr_hook_ok_of_mem hshim)
    (spqr_hook_ok_of_mem halloc)
    (spqr_hook_ok_of_mem hmemset)
    hOnce

end LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.ProofBudget
