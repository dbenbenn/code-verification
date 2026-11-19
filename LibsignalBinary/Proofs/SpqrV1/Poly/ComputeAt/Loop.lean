/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.Defs
public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.PolyPart1CodeSym -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SpqrV1.GF.AcceleratedMul
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangeComplete.Defs
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::encoding::polynomial::Poly>::compute_at`: Loop Proofs

Relocatable `[LibsignalPlacement]` (Block `371`) `VmPreserved`-threaded symbolic execution of
the power-table loop (`powersLoopPure`) and dot-product loop (`dotLoopPure`), handling both
probed and unprobed `tokenInitPlacedAt` states via `OnceCallHookOk`.
-/

public section

namespace CryptoVerification.SpqrV1.Poly.ComputeAt

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.AcceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.LagrangeComplete
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
open CryptoVerification.SpqrV1.Alloc
open LibsignalBinary.Heap (VmPreserved)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

private theorem pc_setMem_loc (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by cases s; rfl
private theorem status_setMem_loc (s : State) (m : Memory) : (s.setMem m).status = s.status := by
  cases s; rfl
private theorem pstate_setMem_loc (s : State) (m : Memory) : (s.setMem m).pstate = s.pstate := by
  cases s; rfl
private theorem trace_setMem_loc (s : State) (m : Memory) : (s.setMem m).trace = s.trace := by
  cases s; rfl
private theorem calleeSavedVRegs_setMem_loc (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by cases s; rfl

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre
  pc_setMem_loc status_setMem_loc pstate_setMem_loc trace_setMem_loc calleeSavedVRegs_setMem_loc
  LagrangePrepare.sp_setPC_pre LagrangePrepare.sp_setMem_setPC_pre
  LagrangePrepare.readReg64_setPC_pre LagrangePrepare.readReg64_setMem_setPC_pre
  LagrangePrepare.readReg32_setPC_pre LagrangePrepare.readReg32_setMem_setPC_pre
  LagrangePrepare.readReg_setPC_pre LagrangePrepare.readReg_setMem_setPC_pre
attribute [local wp_norm] zeroExtend_16_truncate_32_64
attribute [local arm64_norm, local wp_norm]
  ofNat_shl_one ofNat_shl_one_bv truncate16_zext64_trunc32 zext16_xor_trunc32
  Arm64.Obj.pageOf_add_lo12Of
  LagrangePrepare.truncate16_zext64
  polyReduce_setWidth16_eq polyReduce_setWidth16_comm_eq mul2UnreducedWord_truncate32

@[local arm64_norm, local wp_norm]
private theorem zext64_trunc32_shr32_mul2Unreduced (a b1 b2 : BitVec 16) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (mul2UnreducedWord a b1 b2 >>> 32)) =
      (unaccelerated.polyMul a b1).zeroExtend 64 := by
  rw [mul2UnreducedWord_shr32]; bv_bits

@[local arm64_norm, local wp_norm]
private theorem trunc32_shr32_mul2Unreduced (a b1 b2 : BitVec 16) :
    BitVec.truncate 32 (mul2UnreducedWord a b1 b2 >>> 32) =
      unaccelerated.polyMul a b1 := by
  rw [mul2UnreducedWord_shr32]; bv_bits

@[local arm64_norm, local wp_norm]
private theorem polyReduce_asm_eq_trunc_computeAt (a b_arg : BitVec 16) :
    BitVec.truncate 16
      (BitVec.zeroExtend 64
          (reduce.reduceByteEntry
            (BitVec.truncate 8
              ((unaccelerated.polyMul a b_arg ^^^
                  BitVec.zeroExtend 32
                      (reduce.reduceByteEntry
                        (BitVec.truncate 8 (unaccelerated.polyMul a b_arg >>> 24))) <<< 8) >>> 16))) ^^^
        (unaccelerated.polyMul a b_arg ^^^
          BitVec.zeroExtend 32
              (reduce.reduceByteEntry
                (BitVec.truncate 8 (unaccelerated.polyMul a b_arg >>> 24))) <<< 8).zeroExtend 64) =
      unaccelerated.mul a b_arg := by
  rw [← zeroExtend_16_truncate_32_64]
  exact polyReduce_asm_eq a b_arg

private theorem sepWP_grab_vm {prog : Program} {tgt : BitVec 64} {s0 s_call sf_call : State}
    {P : SepProp} {Q : State → SepProp → Prop}
    (hcall : VmPreserved s_call sf_call) (htr_call : sf_call.trace = s_call.trace)
    (hpre : VmPreserved s0 s_call) (htr0 : s_call.trace = s0.trace)
    (h : VmPreserved s0 sf_call → sf_call.trace = s0.trace → SepWP prog tgt sf_call P Q) :
    SepWP prog tgt sf_call P Q :=
  h (hpre.trans hcall) (htr_call.trans htr0)

private theorem growOneStack_split_once (sp' : BitVec 64) :
    stackAt sp' growOneStack =
      memRegion (sp' - 4208#64) 4048 ∗ stackAt sp' 0xa0 := by
  show stackAt sp' (0xa0 + 4048) = _
  rw [ProofLib.stackAt_split_bottom sp' 0xa0 4048 (by decide)]

private theorem growOneStack_merge_once (sp' : BitVec 64) :
    memRegion (sp' - 4208#64) 4048 ∗ stackAt sp' 0xa0 ⊢
      stackAt sp' growOneStack := by
  rw [growOneStack_split_once sp']
  exact Entails.refl _

private theorem scratch16_split (sp0 : BitVec 64) :
    memRegion (sp0 - 112#64) 16 =
      (∃∗ v0 : BitVec 64, (sp0 - 112#64) ↦₆₄ v0) ∗
      (∃∗ v1 : BitVec 64, (sp0 - 104#64) ↦₆₄ v1) := by
  rw [ProofLib.memRegion_split' (b := sp0 - 112#64) (n := 8) (k := 8) (b' := sp0 - 104#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_eight (sp0 - 112#64), ProofLib.memRegion_eight (sp0 - 104#64)]

private theorem scratch16_merge (sp0 : BitVec 64) (v0 v1 : BitVec 64) :
    ((sp0 - 112#64) ↦₆₄ v0) ∗ ((sp0 - 104#64) ↦₆₄ v1) ⊢ memRegion (sp0 - 112#64) 16 := by
  rw [scratch16_split sp0]
  exact sepConj_mono (Entails.sepExists_intro v0) (Entails.sepExists_intro v1)

private theorem scratch8_split32 (sp0 : BitVec 64) :
    memRegion (sp0 - 144#64) 8 =
      (∃∗ v0 : BitVec 32, (sp0 - 144#64) ↦₃₂ v0) ∗
      (∃∗ v1 : BitVec 32, (sp0 - 140#64) ↦₃₂ v1) := by
  rw [ProofLib.memRegion_split' (b := sp0 - 144#64) (n := 4) (k := 4) (b' := sp0 - 140#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_four (sp0 - 144#64), ProofLib.memRegion_four (sp0 - 140#64)]

private theorem scratch8_merge32 (sp0 : BitVec 64) (v0 v1 : BitVec 32) :
    ((sp0 - 144#64) ↦₃₂ v0) ∗ ((sp0 - 140#64) ↦₃₂ v1) ⊢ memRegion (sp0 - 144#64) 8 := by
  rw [scratch8_split32 sp0]
  exact sepConj_mono (Entails.sepExists_intro v0) (Entails.sepExists_intro v1)

set_option maxHeartbeats 1600000 in
theorem powersStep_placed_vm_sepWP [LibsignalPlacement]
    (ext : String → Option (State → State))
    (hOnce : OnceCallHookOk (Rust.withPanics ext))
    (sp0 p_xs : BitVec 64) (hp_xs : p_xs &&& 1#64 = 0#64)
    (len i : Nat) (_hi2 : 2 ≤ i) (hi_lt : i < len) (hlen_bound : 2 * len + 2 ≤ 2 ^ 63)
    (xs : List GF16) (hxs_len : xs.length = i)
    (h1 : i / 2 < xs.length) (h2 : (i / 2) + (i % 2) < xs.length)
    (v_slot : BitVec 16)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop)
    (s : State) (F : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_371).base + 216#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 144#64)
    (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 i)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 len)
    (hx21 : s.readReg64 .x21 = lsρ spqrLazyLockVtableSym)
    (hx23 : s.readReg64 .x23 = lsρ tokenName + 8#64)
    (hx24 : s.readReg64 .x24 = lsρ reduceTableSym)
    (hx25 : s.readReg64 .x25 = Arm64.Obj.pageOf (lsρ tokenStorageName))
    (hx27 : s.readReg64 .x27 = p_xs)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 i)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hnext : ∀ sf : State,
      LibsignalCodeLoaded lsmpl sf.mem →
      sf.pc = (blkPl_371).base + 212#64 →
      sf.status = .Running →
      sf.sp = sp0 - 144#64 →
      sf.trace = s.trace →
      VmPreserved s sf →
      sf.pstate = subsPState64 (BitVec.ofNat 64 len) (BitVec.ofNat 64 (i + 1)) →
      sf.readReg64 .x1 = BitVec.ofNat 64 (i + 1) →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = BitVec.ofNat 64 len →
      sf.readReg64 .x21 = lsρ spqrLazyLockVtableSym →
      sf.readReg64 .x23 = lsρ tokenName + 8#64 →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = Arm64.Obj.pageOf (lsρ tokenStorageName) →
      sf.readReg64 .x27 = p_xs →
      sf.readReg64 .x28 = BitVec.ofNat 64 (i + 1) →
      sf.readReg64 .x29 = sp0 - 96#64 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext)) ret_pc sf
        (gf16SliceAt p_xs (xs ++ [GF16.mul (xs[i / 2]'h1) (xs[(i / 2) + (i % 2)]'h2)]) ∗
         ((sp0 - 136#64) ↦₆₄ BitVec.ofNat 64 len) ∗
         ((sp0 - 128#64) ↦₆₄ p_xs) ∗
         ((sp0 - 120#64) ↦₆₄ BitVec.ofNat 64 (i + 1)) ∗
         memRegion (sp0 - 112#64) 16 ∗
         stackAt (sp0 - 144#64) growOneStack ∗
         tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ F) Q) :
    SepWP ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext)) ret_pc s
      (gf16SliceAt p_xs xs ∗
       ((p_xs + BitVec.ofNat 64 (2 * i)) ↦₁₆ v_slot) ∗
       ((sp0 - 136#64) ↦₆₄ BitVec.ofNat 64 len) ∗
       ((sp0 - 128#64) ↦₆₄ p_xs) ∗
       ((sp0 - 120#64) ↦₆₄ BitVec.ofNat 64 i) ∗
       memRegion (sp0 - 112#64) 16 ∗
       stackAt (sp0 - 144#64) growOneStack ∗
       tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ F) Q := by
  have halign_tok := aligned_tokenOnce_placed
  have hshr := ofNat_ushr_one (i := i) (by omega)
  have hshr_bv := ofNat_ushr_one_bv (i := i) (by omega)
  have hule1 := ofNat_ule_false_of_lt (m := i / 2) (n := i) (by omega) (by omega)
  have hand1 := ofNat_and_one i
  have hadd1 := ofNat_add_ofNat (i / 2) (i % 2)
  have hule2 := ofNat_ule_false_of_lt (m := (i / 2) + (i % 2)) (n := i) (by omega) (by omega)
  have hal1 := aligned16_add_mul_two p_xs hp_xs (i / 2)
  have hal2 := aligned16_add_mul_two p_xs hp_xs ((i / 2) + (i % 2))
  have hal_i := aligned16_add_mul_two p_xs hp_xs i
  rcases ofNat_beq_false_of_lt hi_lt (by omega) with ⟨hneq1, hneq2, hneq3, hneq4⟩
  have hadd_i := ofNat_add_one i
  have h_fetch_ldar := blkPC_371_rebase_fetch_0xfc (blkPl_371).base (Rust.withPanics ext)
  have hmul := lscall_blk (callerProg := (blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext))
    (acceleratedMul2Unreduced_vm_placed_ok (Rust.withPanics ext)) hcl
  simp only [withMemEq, acceleratedMul2UnreducedPlacedSpec] at hmul
  have honce : subroutine_ok ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext))
      (lsρ spqrOnceCallSym) spqrOnceCallGhostSpec :=
    spqr_onceCall_ok hOnce
  have hval_eq : unaccelerated.mul (xs[i / 2]'h1).value (xs[(i / 2) + (i % 2)]'h2).value =
      (GF16.mul (xs[i / 2]'h1) (xs[(i / 2) + (i % 2)]'h2)).value := rfl
  let a1 := (xs[i / 2]'h1).value
  let b1 := (xs[(i / 2) + (i % 2)]'h2).value
  apply sepWP_seq_lscl (by exact hcl) (mid := (blkPl_371).base + 212#64)
  wp_steps 7
  wp_conv_pre => rw [LagrangeComplete.gf16SliceAt_focus_assoc h1 p_xs]
  wp_steps 1
  wp_conv_pre => rw [← LagrangeComplete.gf16SliceAt_focus_assoc h1 p_xs, LagrangeComplete.gf16SliceAt_focus_assoc h2 p_xs]
  wp_steps 1
  wp_conv_pre => rw [← LagrangeComplete.gf16SliceAt_focus_assoc h2 p_xs]
  wp_simp_pre [tokenInitPlacedAt]
  wp_pull_exists
  rename_i probed
  cases probed
  · -- Unprobed slow path (`probed = false`)
    have _hsp_al : (sp0 &&& 15#64 == 0#64) = true := beq_iff_eq.mpr hsp0
    wp_simp_pre [tokenUnprobedPlacedAt, scratch16_split sp0, growOneStack_split_once]
    wp_pull_exists
    apply sepWP_seq_lscl (by exact hcl) (mid := (blkPl_371).base + 272#64)
    apply step_ldar32
    · wp_norm_lhs
    · wp_norm_lhs
    · exact h_fetch_ldar
    · wp_norm_lhs
    · wp_norm_lhs
    · exact halign_tok
    · wp_sep_access
    · wp_norm_lhs
    apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
      (Q := (blkPC_371).rebase (blkPl_371).base
        (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException (Rust.withPanics ext)))
      blkLib_eq_371 (mid := (blkPl_371).base + 388#64)
    intro _m_strip
    wp_steps 12
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
    have hvm_once0 : VmPreserved s _ :=
      (by simp only [wp_norm, arm64_norm] : VmPreserved s _).trans
        (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]))
    wp_steps 1
    wp_call honce
    have hvm_once1 : VmPreserved s sf :=
      (hvm_once0.trans (by
        unfold VmPreserved LibsignalBinary.Heap.PoolPreserved LibsignalBinary.Heap.FdsHiFrame
        exact ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, fun _ _ _ => rfl⟩)).trans (by assumption)
    have htr_once1 : sf.trace = s.trace :=
      (by assumption : sf.trace = _).trans (by simp only [wp_norm, arm64_norm])
    wp_steps 6
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro hcl_once
    apply SepWP.fold (growOneStack_merge_once (sp0 - 144#64)) (by sep_focus)
    apply SepWP.fold (scratch16_merge sp0 _ _) (by sep_focus)
    apply SepWP.fold tokenInitPlacedAt_fold (by sep_focus)
    have hmul_after := lscall_blk (callerProg := (blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext))
      (acceleratedMul2Unreduced_vm_placed_ok (Rust.withPanics ext)) hcl_once
    simp only [withMemEq, acceleratedMul2UnreducedPlacedSpec] at hmul_after
    wp_steps 1
    wp_call hmul_after (a1, b1, 0#16)
    refine sepWP_grab_vm (s0 := s) (by assumption) (by assumption)
      (hvm_once1.trans (by simp only [wp_norm, arm64_norm]))
      (by simpa [wp_norm, arm64_norm] using htr_once1)
      fun hvm_pre htr_mul => ?_
    have _hsp_mul : sf_1.sp = sp0 - 144#64 := by simp only [arm64_norm, wp_norm, *]
    have _hx24_mul : sf_1.readReg64 .x24 = lsρ reduceTableSym := by simp only [arm64_norm, wp_norm, *]
    apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
      (Q := (blkPC_371).rebase (blkPl_371).base
        (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException (Rust.withPanics ext)))
      blkLib_eq_371 (mid := (blkPl_371).base + 212#64)
    intro _m_strip2
    wp_steps 2
    wp_conv_pre =>
      rw [reduceTablePlacedAt_focus16 (BitVec.truncate 8 (unaccelerated.polyMul a1 b1 >>> 24)),
          uxtx1_hi_idx1_nomask_eq a1 b1 0#16]
    wp_steps 1
    wp_conv_pre =>
      rw [← uxtx1_hi_idx1_nomask_eq a1 b1 0#16,
          ← reduceTablePlacedAt_focus16 (BitVec.truncate 8 (unaccelerated.polyMul a1 b1 >>> 24))]
    wp_steps 2
    wp_conv_pre =>
      rw [reduceTablePlacedAt_focus16
            (BitVec.truncate 8
              ((unaccelerated.polyMul a1 b1 ^^^
                  BitVec.zeroExtend 32
                      (reduce.reduceByteEntry
                        (BitVec.truncate 8 (unaccelerated.polyMul a1 b1 >>> 24))) <<<
                    8) >>>
                16)),
          uxtw1_idx2_eq]
    wp_steps 1
    wp_conv_pre =>
      rw [← uxtw1_idx2_eq,
          ← reduceTablePlacedAt_focus16
            (BitVec.truncate 8
              ((unaccelerated.polyMul a1 b1 ^^^
                  BitVec.zeroExtend 32
                      (reduce.reduceByteEntry
                        (BitVec.truncate 8 (unaccelerated.polyMul a1 b1 >>> 24))) <<<
                    8) >>>
                16))]
    wp_steps 11
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real2 _hnsp2 => ?_
    have hvm_tot : VmPreserved s _ :=
      hvm_pre.trans (_hnsp2.toVmPreserved (by simp only [wp_norm, arm64_norm]))
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro hcl_next
    wp_conv_pre =>
      rw [show p_xs + BitVec.ofNat 64 (2 * i) = p_xs + BitVec.ofNat 64 (2 * xs.length) by rw [hxs_len],
          hval_eq,
          gf16SliceAt_append_singleton_assoc p_xs xs
            (GF16.mul (xs[i / 2]'h1) (xs[(i / 2) + (i % 2)]'h2))]
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext _ hcl_next (by wp_norm_lhs) (by wp_norm_lhs)
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
        hvm_tot
        (by wp_norm_lhs)
        (by wp_norm_lhs)
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
        (by wp_norm_lhs)
        (by wp_norm_lhs)
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *]))
  · -- Probed fast path (`probed = true`)
    have _hsp_al : (sp0 &&& 15#64 == 0#64) = true := beq_iff_eq.mpr hsp0
    wp_simp_pre [tokenProbedPlacedAt]
    apply step_ldar32
    · wp_norm_lhs
    · wp_norm_lhs
    · exact h_fetch_ldar
    · wp_norm_lhs
    · wp_norm_lhs
    · exact halign_tok
    · wp_sep_access
    · wp_norm_lhs
    wp_steps 5
    apply SepWP.fold tokenInitPlacedAt_fold (by sep_focus)
    wp_call hmul (a1, b1, 0#16)
    refine sepWP_grab_vm (s0 := s) (by assumption) (by assumption)
      (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm])
      fun hvm_pre htr_mul => ?_
    have _hsp_mul : sf.sp = sp0 - 144#64 := by simp only [arm64_norm, wp_norm, *]
    have _hx24_mul : sf.readReg64 .x24 = lsρ reduceTableSym := by simp only [arm64_norm, wp_norm, *]
    apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
      (Q := (blkPC_371).rebase (blkPl_371).base
        (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException (Rust.withPanics ext)))
      blkLib_eq_371 (mid := (blkPl_371).base + 212#64)
    intro _m_strip
    wp_steps 2
    wp_conv_pre =>
      rw [reduceTablePlacedAt_focus16 (BitVec.truncate 8 (unaccelerated.polyMul a1 b1 >>> 24)),
          uxtx1_hi_idx1_nomask_eq a1 b1 0#16]
    wp_steps 1
    wp_conv_pre =>
      rw [← uxtx1_hi_idx1_nomask_eq a1 b1 0#16,
          ← reduceTablePlacedAt_focus16 (BitVec.truncate 8 (unaccelerated.polyMul a1 b1 >>> 24))]
    wp_steps 2
    wp_conv_pre =>
      rw [reduceTablePlacedAt_focus16
            (BitVec.truncate 8
              ((unaccelerated.polyMul a1 b1 ^^^
                  BitVec.zeroExtend 32
                      (reduce.reduceByteEntry
                        (BitVec.truncate 8 (unaccelerated.polyMul a1 b1 >>> 24))) <<<
                    8) >>>
                16)),
          uxtw1_idx2_eq]
    wp_steps 1
    wp_conv_pre =>
      rw [← uxtw1_idx2_eq,
          ← reduceTablePlacedAt_focus16
            (BitVec.truncate 8
              ((unaccelerated.polyMul a1 b1 ^^^
                  BitVec.zeroExtend 32
                      (reduce.reduceByteEntry
                        (BitVec.truncate 8 (unaccelerated.polyMul a1 b1 >>> 24))) <<<
                    8) >>>
                16))]
    wp_steps 11
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
    have hvm_tot : VmPreserved s _ :=
      hvm_pre.trans (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]))
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro hcl_next
    wp_conv_pre =>
      rw [show p_xs + BitVec.ofNat 64 (2 * i) = p_xs + BitVec.ofNat 64 (2 * xs.length) by rw [hxs_len],
          hval_eq,
          gf16SliceAt_append_singleton_assoc p_xs xs
            (GF16.mul (xs[i / 2]'h1) (xs[(i / 2) + (i % 2)]'h2))]
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext _ hcl_next (by wp_norm_lhs) (by wp_norm_lhs)
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
        hvm_tot
        (by wp_norm_lhs)
        (by wp_norm_lhs)
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
        (by wp_norm_lhs)
        (by wp_norm_lhs)
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *]))

set_option maxHeartbeats 1600000 in
theorem powersLoop_placed_vm_sepWP [LibsignalPlacement]
    (ext : String → Option (State → State))
    (hOnce : OnceCallHookOk (Rust.withPanics ext))
    (sp0 p_xs : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64) (hp_xs : p_xs &&& 1#64 = 0#64)
    (len : Nat) (hlen_bound : 2 * len + 2 ≤ 2 ^ 63)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop) :
    ∀ (r i : Nat) (xs : List GF16)
      (_hi2 : 2 ≤ i) (_hir : i + (r + 1) = len) (_hxs_len : xs.length = i)
      (s : State) (F : SepProp),
      LibsignalCodeLoaded lsmpl s.mem →
      s.pc = (blkPl_371).base + 216#64 →
      s.status = .Running →
      s.sp = sp0 - 144#64 →
      s.readReg64 .x1 = BitVec.ofNat 64 i →
      s.readReg64 .x20 = BitVec.ofNat 64 len →
      s.readReg64 .x21 = lsρ spqrLazyLockVtableSym →
      s.readReg64 .x23 = lsρ tokenName + 8#64 →
      s.readReg64 .x24 = lsρ reduceTableSym →
      s.readReg64 .x25 = Arm64.Obj.pageOf (lsρ tokenStorageName) →
      s.readReg64 .x27 = p_xs →
      s.readReg64 .x28 = BitVec.ofNat 64 i →
      s.readReg64 .x29 = sp0 - 96#64 →
      (∀ sf : State,
        LibsignalCodeLoaded lsmpl sf.mem →
        sf.pc = (blkPl_371).base + 416#64 →
        sf.status = .Running →
        sf.sp = sp0 - 144#64 →
        sf.trace = s.trace →
        VmPreserved s sf →
        sf.readReg64 .x1 = BitVec.ofNat 64 len →
        sf.readReg64 .x19 = s.readReg64 .x19 →
        sf.readReg64 .x20 = BitVec.ofNat 64 len →
        sf.readReg64 .x23 = lsρ tokenName + 8#64 →
        sf.readReg64 .x24 = s.readReg64 .x24 →
        sf.readReg64 .x25 = Arm64.Obj.pageOf (lsρ tokenStorageName) →
        sf.readReg64 .x27 = p_xs →
        sf.readReg64 .x29 = sp0 - 96#64 →
        calleeSavedVRegs sf = calleeSavedVRegs s →
        SepWP ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext)) ret_pc sf
          (gf16SliceAt p_xs (powersLoopPure i (r + 1) xs) ∗
           ((sp0 - 136#64) ↦₆₄ BitVec.ofNat 64 len) ∗
           ((sp0 - 128#64) ↦₆₄ p_xs) ∗
           ((sp0 - 120#64) ↦₆₄ BitVec.ofNat 64 len) ∗
           memRegion (sp0 - 112#64) 16 ∗
           stackAt (sp0 - 144#64) growOneStack ∗
           tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ F) Q) →
      SepWP ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext)) ret_pc s
        (gf16SliceAt p_xs xs ∗
         memRegion (p_xs + BitVec.ofNat 64 (2 * i)) (2 * (r + 1)) ∗
         ((sp0 - 136#64) ↦₆₄ BitVec.ofNat 64 len) ∗
         ((sp0 - 128#64) ↦₆₄ p_xs) ∗
         ((sp0 - 120#64) ↦₆₄ BitVec.ofNat 64 i) ∗
         memRegion (sp0 - 112#64) 16 ∗
         stackAt (sp0 - 144#64) growOneStack ∗
         tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ F) Q := by
  intro r
  induction r with
  | zero =>
    intro i xs hi2 hir hxs_len s F hcl hpc hrun hsp hx1 hx20 hx21 hx23 hx24 hx25 hx27 hx28 hx29 hnext
    have h1 : i / 2 < xs.length := by omega
    have h2 : (i / 2) + (i % 2) < xs.length := by omega
    have hi_lt : i < len := by omega
    have hlen_eq : i + 1 = len := by omega
    rw [memRegion_two_succ (p_xs + BitVec.ofNat 64 (2 * i)) 0 (by omega),
        memRegion_zero, sepConj_emp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWP.exists_left fun v_slot => ?_
    apply powersStep_placed_vm_sepWP ext hOnce sp0 p_xs hp_xs len i hi2 hi_lt hlen_bound xs hxs_len h1 h2 v_slot
      ret_pc Q s F hcl hpc hrun hsp hsp0 hx1 hx20 hx21 hx23 hx24 hx25 hx27 hx28 hx29
    intro s1 hcl1 hpc1 hrun1 hsp1 htr1 hvm1 hpst1 hx1_1 hx19_1 hx20_1 _hx21_1 hx23_1 hx24_1 hx25_1 hx27_1 hx28_1 hx29_1 hvregs1
    rw [hlen_eq] at hpst1 hx1_1 hx28_1 ⊢
    wp_steps 1
    rw [powersLoopPure_succ i 0 xs h1 h2] at hnext
    dsimp only [powersLoopPure] at hnext
    exact hnext _ hcl1 (by wp_norm_lhs) (by wp_norm_lhs) (by simpa [arm64_norm, wp_norm] using hsp1)
      (by simpa [arm64_norm, wp_norm] using htr1)
      (hvm1.trans (by simp only [wp_norm, arm64_norm]))
      (by simpa [arm64_norm, wp_norm] using hx1_1)
      (by simpa [arm64_norm, wp_norm] using hx19_1)
      (by simpa [arm64_norm, wp_norm] using hx20_1)
      (by simpa [arm64_norm, wp_norm] using hx23_1)
      (by simpa [arm64_norm, wp_norm] using hx24_1)
      (by simpa [arm64_norm, wp_norm] using hx25_1)
      (by simpa [arm64_norm, wp_norm] using hx27_1)
      (by simpa [arm64_norm, wp_norm] using hx29_1)
      (by simpa [arm64_norm, wp_norm] using hvregs1)
  | succ r' ih =>
    intro i xs hi2 hir hxs_len s F hcl hpc hrun hsp hx1 hx20 hx21 hx23 hx24 hx25 hx27 hx28 hx29 hnext
    have h1 : i / 2 < xs.length := by omega
    have h2 : (i / 2) + (i % 2) < xs.length := by omega
    have hi_lt : i < len := by omega
    have hi1_lt : i + 1 < len := by omega
    rcases ofNat_beq_false_of_lt hi1_lt (by omega) with ⟨hneq1, hneq2, hneq3, hneq4⟩
    rw [memRegion_two_succ (p_xs + BitVec.ofNat 64 (2 * i)) (r' + 1) (by omega),
        ptr_add_two_step p_xs i]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWP.exists_left fun v_slot => ?_
    wp_conv_pre =>
      rw [show gf16SliceAt p_xs xs ∗
            (((p_xs + BitVec.ofNat 64 (2 * i)) ↦₁₆ v_slot) ∗
             memRegion (p_xs + BitVec.ofNat 64 (2 * (i + 1))) (2 * (r' + 1))) ∗
            ((sp0 - 136#64) ↦₆₄ BitVec.ofNat 64 len) ∗
            ((sp0 - 128#64) ↦₆₄ p_xs) ∗
            ((sp0 - 120#64) ↦₆₄ BitVec.ofNat 64 i) ∗
            memRegion (sp0 - 112#64) 16 ∗
            stackAt (sp0 - 144#64) growOneStack ∗
            tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ F =
          gf16SliceAt p_xs xs ∗
            ((p_xs + BitVec.ofNat 64 (2 * i)) ↦₁₆ v_slot) ∗
            ((sp0 - 136#64) ↦₆₄ BitVec.ofNat 64 len) ∗
            ((sp0 - 128#64) ↦₆₄ p_xs) ∗
            ((sp0 - 120#64) ↦₆₄ BitVec.ofNat 64 i) ∗
            memRegion (sp0 - 112#64) 16 ∗
            stackAt (sp0 - 144#64) growOneStack ∗
            tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
            (memRegion (p_xs + BitVec.ofNat 64 (2 * (i + 1))) (2 * (r' + 1)) ∗ F) by ac_rfl]
    apply powersStep_placed_vm_sepWP ext hOnce sp0 p_xs hp_xs len i hi2 hi_lt hlen_bound xs hxs_len h1 h2 v_slot
      ret_pc Q s (memRegion (p_xs + BitVec.ofNat 64 (2 * (i + 1))) (2 * (r' + 1)) ∗ F)
      hcl hpc hrun hsp hsp0 hx1 hx20 hx21 hx23 hx24 hx25 hx27 hx28 hx29
    intro s1 hcl1 hpc1 hrun1 hsp1 htr1 hvm1 hpst1 hx1_1 hx19_1 hx20_1 hx21_1 hx23_1 hx24_1 hx25_1 hx27_1 hx28_1 hx29_1 hvregs1
    wp_steps 1
    wp_conv_pre =>
      rw [show gf16SliceAt p_xs (xs ++ [GF16.mul (xs[i / 2]'h1) (xs[(i / 2) + (i % 2)]'h2)]) ∗
            ((sp0 - 136#64) ↦₆₄ BitVec.ofNat 64 len) ∗
            ((sp0 - 128#64) ↦₆₄ p_xs) ∗
            ((sp0 - 120#64) ↦₆₄ BitVec.ofNat 64 (i + 1)) ∗
            memRegion (sp0 - 112#64) 16 ∗
            stackAt (sp0 - 144#64) growOneStack ∗
            tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
            (memRegion (p_xs + BitVec.ofNat 64 (2 * (i + 1))) (2 * (r' + 1)) ∗ F) =
          gf16SliceAt p_xs (xs ++ [GF16.mul (xs[i / 2]'h1) (xs[(i / 2) + (i % 2)]'h2)]) ∗
            memRegion (p_xs + BitVec.ofNat 64 (2 * (i + 1))) (2 * (r' + 1)) ∗
            ((sp0 - 136#64) ↦₆₄ BitVec.ofNat 64 len) ∗
            ((sp0 - 128#64) ↦₆₄ p_xs) ∗
            ((sp0 - 120#64) ↦₆₄ BitVec.ofNat 64 (i + 1)) ∗
            memRegion (sp0 - 112#64) 16 ∗
            stackAt (sp0 - 144#64) growOneStack ∗
            tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ F by ac_rfl]
    apply ih (i + 1) (xs ++ [GF16.mul (xs[i / 2]'h1) (xs[(i / 2) + (i % 2)]'h2)])
      (by omega) (by omega) (by simp [hxs_len]) _ F (by exact hcl1)
      (by wp_norm_lhs) (by wp_norm_lhs)
      (by simpa [arm64_norm, wp_norm] using hsp1)
      (by simpa [arm64_norm, wp_norm] using hx1_1)
      (by simpa [arm64_norm, wp_norm] using hx20_1)
      (by simpa [arm64_norm, wp_norm] using hx21_1)
      (by simpa [arm64_norm, wp_norm] using hx23_1)
      (by simpa [arm64_norm, wp_norm, hx24] using hx24_1)
      (by simpa [arm64_norm, wp_norm] using hx25_1)
      (by simpa [arm64_norm, wp_norm] using hx27_1)
      (by simpa [arm64_norm, wp_norm] using hx28_1)
      (by simpa [arm64_norm, wp_norm] using hx29_1)
    intro sf hcl_f hpc_f hrun_f hsp_f htr_f hvm_f hx1_f hx19_f hx20_f hx23_f hx24_f hx25_f hx27_f hx29_f hvregs_f
    rw [powersLoopPure_succ i (r' + 1) xs h1 h2] at hnext
    exact hnext sf hcl_f hpc_f hrun_f hsp_f
      (by rw [htr_f]; simpa [arm64_norm, wp_norm] using htr1)
      ((hvm1.trans (by simp only [wp_norm, arm64_norm])).trans hvm_f)
      hx1_f
      (by rw [hx19_f]; simpa [arm64_norm, wp_norm] using hx19_1)
      hx20_f hx23_f
      (by rw [hx24_f]; simpa [arm64_norm, wp_norm] using hx24_1)
      hx25_f hx27_f hx29_f
      (by rw [hvregs_f]; simpa [arm64_norm, wp_norm] using hvregs1)

set_option maxHeartbeats 1600000 in
theorem dotStep_placed_vm_sepWP [LibsignalPlacement]
    (ext : String → Option (State → State))
    (hOnce : OnceCallHookOk (Rust.withPanics ext))
    (sp0 p_coeffs p_xs : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64) (hpx_al : p_xs &&& 1#64 = 0#64)
    (coeffs xs : List GF16)
    (r k : Nat) (acc : GF16)
    (hkc : k < coeffs.length) (hkx : k < xs.length)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop)
    (s : State) (F : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_371).base + 472#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 144#64)
    (hx19 : s.readReg64 .x19 = p_coeffs + BitVec.ofNat 64 (2 * k))
    (hx20 : BitVec.truncate 16 (s.readReg64 .x20) = acc.value)
    (hx21 : s.readReg64 .x21 = lsρ spqrLazyLockVtableSym)
    (hx23 : s.readReg64 .x23 = lsρ tokenName + 8#64)
    (hx24 : s.readReg64 .x24 = lsρ reduceTableSym)
    (hx25 : s.readReg64 .x25 = Arm64.Obj.pageOf (lsρ tokenStorageName))
    (hx26 : s.readReg64 .x26 = sp0 - 112#64)
    (hx27 : s.readReg64 .x27 = p_xs + BitVec.ofNat 64 (2 * k))
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 (r + 1))
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hnext : ∀ sf : State,
      LibsignalCodeLoaded lsmpl sf.mem →
      sf.pc = (blkPl_371).base + 544#64 →
      sf.status = .Running →
      sf.sp = sp0 - 144#64 →
      sf.trace = s.trace →
      VmPreserved s sf →
      sf.pstate = subsPState64 (BitVec.ofNat 64 (r + 1)) 1#64 →
      sf.readReg64 .x19 = p_coeffs + BitVec.ofNat 64 (2 * (k + 1)) →
      BitVec.truncate 16 (sf.readReg64 .x20) = (GF16.add acc (GF16.mul (coeffs[k]'hkc) (xs[k]'hkx))).value →
      sf.readReg64 .x21 = lsρ spqrLazyLockVtableSym →
      sf.readReg64 .x23 = lsρ tokenName + 8#64 →
      sf.readReg64 .x24 = lsρ reduceTableSym →
      sf.readReg64 .x25 = Arm64.Obj.pageOf (lsρ tokenStorageName) →
      sf.readReg64 .x26 = sp0 - 112#64 →
      sf.readReg64 .x27 = p_xs + BitVec.ofNat 64 (2 * (k + 1)) →
      sf.readReg64 .x28 = BitVec.ofNat 64 r →
      sf.readReg64 .x29 = sp0 - 96#64 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext)) ret_pc sf
        (gf16SliceAt p_coeffs coeffs ∗
         gf16SliceAt p_xs xs ∗
         memRegion (sp0 - 144#64) 8 ∗
         memRegion (sp0 - 112#64) 16 ∗
         stackAt (sp0 - 144#64) growOneStack ∗
         tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ F) Q) :
    SepWP ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext)) ret_pc s
      (gf16SliceAt p_coeffs coeffs ∗
       gf16SliceAt p_xs xs ∗
       memRegion (sp0 - 144#64) 8 ∗
       memRegion (sp0 - 112#64) 16 ∗
       stackAt (sp0 - 144#64) growOneStack ∗
       tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ F) Q := by
  have halign_tok := aligned_tokenOnce_placed
  have hal_x := aligned16_add_mul_two p_xs hpx_al k
  have hstep_c := ptr_add_two_step p_coeffs k
  have hstep_x := ptr_add_two_step p_xs k
  have hsub_r := ofNat_sub_one_succ r
  have h_fetch_ldar := blkPC_371_rebase_fetch_0x1e0 (blkPl_371).base (Rust.withPanics ext)
  have hmul := lscall_blk (callerProg := (blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext))
    (acceleratedMul2Unreduced_vm_placed_ok (Rust.withPanics ext)) hcl
  simp only [withMemEq, acceleratedMul2UnreducedPlacedSpec] at hmul
  have honce : subroutine_ok ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext))
      (lsρ spqrOnceCallSym) spqrOnceCallGhostSpec :=
    spqr_onceCall_ok hOnce
  let ck := (coeffs[k]'hkc).value
  let xk := (xs[k]'hkx).value
  apply sepWP_seq_lscl (by exact hcl) (mid := (blkPl_371).base + 544#64)
  wp_conv_pre => rw [LagrangeComplete.gf16SliceAt_focus_assoc hkc p_coeffs]
  wp_steps 1
  wp_conv_pre =>
    rw [← LagrangeComplete.gf16SliceAt_focus_assoc hkc p_coeffs,
        LagrangeComplete.gf16SliceAt_focus_assoc hkx p_xs]
  wp_steps 1
  wp_conv_pre =>
    rw [← LagrangeComplete.gf16SliceAt_focus_assoc hkx p_xs]
  wp_simp_pre [tokenInitPlacedAt]
  wp_pull_exists
  rename_i probed
  cases probed
  · -- Unprobed slow path (`probed = false`)
    have _hsp_al : (sp0 &&& 15#64 == 0#64) = true := beq_iff_eq.mpr hsp0
    wp_simp_pre [tokenUnprobedPlacedAt, scratch8_split32 sp0, scratch16_split sp0, growOneStack_split_once]
    wp_pull_exists
    apply sepWP_seq_lscl (by exact hcl) (mid := (blkPl_371).base + 500#64)
    apply step_ldar32
    · wp_norm_lhs
    · wp_norm_lhs
    · exact h_fetch_ldar
    · wp_norm_lhs
    · wp_norm_lhs
    · exact halign_tok
    · wp_sep_access
    · wp_norm_lhs
    apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
      (Q := (blkPC_371).rebase (blkPl_371).base
        (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException (Rust.withPanics ext)))
      blkLib_eq_371 (mid := (blkPl_371).base + 588#64)
    intro _m_strip
    wp_steps 10
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
    have hvm_once0 : VmPreserved s _ :=
      (by simp only [wp_norm, arm64_norm] : VmPreserved s _).trans
        (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]))
    wp_steps 1
    wp_call honce
    have hvm_once1 : VmPreserved s sf :=
      (hvm_once0.trans (by
        unfold VmPreserved LibsignalBinary.Heap.PoolPreserved LibsignalBinary.Heap.FdsHiFrame
        exact ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, fun _ _ _ => rfl⟩)).trans (by assumption)
    have htr_once1 : sf.trace = s.trace :=
      (by assumption : sf.trace = _).trans (by simp only [wp_norm, arm64_norm])
    wp_steps 5
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro hcl_once
    apply SepWP.fold (growOneStack_merge_once (sp0 - 144#64)) (by sep_focus)
    apply SepWP.fold (scratch16_merge sp0 _ _) (by sep_focus)
    apply SepWP.fold (scratch8_merge32 sp0 _ _) (by sep_focus)
    apply SepWP.fold tokenInitPlacedAt_fold (by sep_focus)
    have hmul_after := lscall_blk (callerProg := (blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext))
      (acceleratedMul2Unreduced_vm_placed_ok (Rust.withPanics ext)) hcl_once
    simp only [withMemEq, acceleratedMul2UnreducedPlacedSpec] at hmul_after
    wp_steps 1
    wp_call hmul_after (ck, xk, 0#16)
    refine sepWP_grab_vm (s0 := s) (by assumption) (by assumption)
      (hvm_once1.trans (by simp only [wp_norm, arm64_norm]))
      (by simpa [wp_norm, arm64_norm] using htr_once1)
      fun hvm_pre htr_mul => ?_
    have _hx24_mul : sf_1.readReg64 .x24 = lsρ reduceTableSym := by simp only [arm64_norm, wp_norm, *]
    wp_steps 2
    wp_conv_pre =>
      rw [reduceTablePlacedAt_focus16 (BitVec.truncate 8 (unaccelerated.polyMul ck xk >>> 24)),
          uxtx1_hi_idx1_nomask_eq ck xk 0#16]
    wp_steps 1
    wp_conv_pre =>
      rw [← uxtx1_hi_idx1_nomask_eq ck xk 0#16,
          ← reduceTablePlacedAt_focus16 (BitVec.truncate 8 (unaccelerated.polyMul ck xk >>> 24))]
    wp_steps 2
    wp_conv_pre =>
      rw [reduceTablePlacedAt_focus16
            (BitVec.truncate 8
              ((unaccelerated.polyMul ck xk ^^^
                  BitVec.zeroExtend 32
                      (reduce.reduceByteEntry
                        (BitVec.truncate 8 (unaccelerated.polyMul ck xk >>> 24))) <<<
                    8) >>>
                16)),
          uxtw1_idx2_eq]
    wp_steps 1
    wp_conv_pre =>
      rw [← uxtw1_idx2_eq,
          ← reduceTablePlacedAt_focus16
            (BitVec.truncate 8
              ((unaccelerated.polyMul ck xk ^^^
                  BitVec.zeroExtend 32
                      (reduce.reduceByteEntry
                        (BitVec.truncate 8 (unaccelerated.polyMul ck xk >>> 24))) <<<
                    8) >>>
                16))]
    wp_steps 3
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro hcl_next
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext _ hcl_next (by wp_norm_lhs) (by wp_norm_lhs)
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
        (hvm_pre.trans (by simp only [wp_norm, arm64_norm]))
        (by wp_norm_lhs)
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *]
            exact eor_gf16_add_comm acc (GF16.mul (coeffs[k]'hkc) (xs[k]'hkx)))
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
        (by wp_norm_lhs)
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *]))
  · -- Probed fast path (`probed = true`)
    have _hsp_al : (sp0 &&& 15#64 == 0#64) = true := beq_iff_eq.mpr hsp0
    wp_simp_pre [tokenProbedPlacedAt]
    apply step_ldar32
    · wp_norm_lhs
    · wp_norm_lhs
    · exact h_fetch_ldar
    · wp_norm_lhs
    · wp_norm_lhs
    · exact halign_tok
    · wp_sep_access
    · wp_norm_lhs
    wp_steps 5
    apply SepWP.fold tokenInitPlacedAt_fold (by sep_focus)
    wp_call hmul (ck, xk, 0#16)
    refine sepWP_grab_vm (s0 := s) (by assumption) (by assumption)
      (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm])
      fun hvm_pre htr_mul => ?_
    have _hx24_mul : sf.readReg64 .x24 = lsρ reduceTableSym := by simp only [arm64_norm, wp_norm, *]
    wp_steps 2
    wp_conv_pre =>
      rw [reduceTablePlacedAt_focus16 (BitVec.truncate 8 (unaccelerated.polyMul ck xk >>> 24)),
          uxtx1_hi_idx1_nomask_eq ck xk 0#16]
    wp_steps 1
    wp_conv_pre =>
      rw [← uxtx1_hi_idx1_nomask_eq ck xk 0#16,
          ← reduceTablePlacedAt_focus16 (BitVec.truncate 8 (unaccelerated.polyMul ck xk >>> 24))]
    wp_steps 2
    wp_conv_pre =>
      rw [reduceTablePlacedAt_focus16
            (BitVec.truncate 8
              ((unaccelerated.polyMul ck xk ^^^
                  BitVec.zeroExtend 32
                      (reduce.reduceByteEntry
                        (BitVec.truncate 8 (unaccelerated.polyMul ck xk >>> 24))) <<<
                    8) >>>
                16)),
          uxtw1_idx2_eq]
    wp_steps 1
    wp_conv_pre =>
      rw [← uxtw1_idx2_eq,
          ← reduceTablePlacedAt_focus16
            (BitVec.truncate 8
              ((unaccelerated.polyMul ck xk ^^^
                  BitVec.zeroExtend 32
                      (reduce.reduceByteEntry
                        (BitVec.truncate 8 (unaccelerated.polyMul ck xk >>> 24))) <<<
                    8) >>>
                16))]
    wp_steps 3
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro hcl_next
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext _ hcl_next (by wp_norm_lhs) (by wp_norm_lhs)
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
        (hvm_pre.trans (by simp only [wp_norm, arm64_norm]))
        (by wp_norm_lhs)
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *]
            exact eor_gf16_add_comm acc (GF16.mul (coeffs[k]'hkc) (xs[k]'hkx)))
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
        (by wp_norm_lhs)
        (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *]))

set_option maxHeartbeats 1600000 in
theorem dotLoop_placed_vm_sepWP [LibsignalPlacement]
    (ext : String → Option (State → State))
    (hOnce : OnceCallHookOk (Rust.withPanics ext))
    (sp0 p_coeffs p_xs : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64) (hpx_al : p_xs &&& 1#64 = 0#64)
    (coeffs xs : List GF16)
    (hlen_le : coeffs.length ≤ xs.length) (hlen_bound : 2 * coeffs.length + 2 ≤ 2 ^ 63)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop) :
    ∀ (r k : Nat) (acc : GF16)
      (_hkr : k + (r + 1) = coeffs.length)
      (s : State) (F : SepProp),
      LibsignalCodeLoaded lsmpl s.mem →
      s.pc = (blkPl_371).base + 472#64 →
      s.status = .Running →
      s.sp = sp0 - 144#64 →
      s.readReg64 .x19 = p_coeffs + BitVec.ofNat 64 (2 * k) →
      BitVec.truncate 16 (s.readReg64 .x20) = acc.value →
      s.readReg64 .x21 = lsρ spqrLazyLockVtableSym →
      s.readReg64 .x23 = lsρ tokenName + 8#64 →
      s.readReg64 .x24 = lsρ reduceTableSym →
      s.readReg64 .x25 = Arm64.Obj.pageOf (lsρ tokenStorageName) →
      s.readReg64 .x26 = sp0 - 112#64 →
      s.readReg64 .x27 = p_xs + BitVec.ofNat 64 (2 * k) →
      s.readReg64 .x28 = BitVec.ofNat 64 (r + 1) →
      s.readReg64 .x29 = sp0 - 96#64 →
      (∀ sf : State,
        LibsignalCodeLoaded lsmpl sf.mem →
        sf.pc = (blkPl_371).base + 616#64 →
        sf.status = .Running →
        sf.sp = sp0 - 144#64 →
        sf.trace = s.trace →
        VmPreserved s sf →
        BitVec.truncate 16 (sf.readReg64 .x20) = (dotLoopPure k (r + 1) coeffs xs acc).value →
        sf.readReg64 .x29 = sp0 - 96#64 →
        calleeSavedVRegs sf = calleeSavedVRegs s →
        SepWP ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext)) ret_pc sf
          (gf16SliceAt p_coeffs coeffs ∗
           gf16SliceAt p_xs xs ∗
           memRegion (sp0 - 144#64) 8 ∗
           memRegion (sp0 - 112#64) 16 ∗
           stackAt (sp0 - 144#64) growOneStack ∗
           tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ F) Q) →
      SepWP ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext)) ret_pc s
        (gf16SliceAt p_coeffs coeffs ∗
         gf16SliceAt p_xs xs ∗
         memRegion (sp0 - 144#64) 8 ∗
         memRegion (sp0 - 112#64) 16 ∗
         stackAt (sp0 - 144#64) growOneStack ∗
         tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ F) Q := by
  intro r
  induction r with
  | zero =>
    intro k acc hkr s F hcl hpc hrun hsp hx19 hx20 hx21 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hnext
    have hkc : k < coeffs.length := by omega
    have hkx : k < xs.length := by omega
    apply dotStep_placed_vm_sepWP ext hOnce sp0 p_coeffs p_xs hsp0 hpx_al coeffs xs 0 k acc hkc hkx
      ret_pc Q s F hcl hpc hrun hsp hx19 hx20 hx21 hx23 hx24 hx25 hx26 hx27 hx28 hx29
    intro s1 hcl1 hpc1 hrun1 hsp1 htr1 hvm1 hpst1 _hx19_1 hx20_1 _hx21_1 _hx23_1 _hx24_1 _hx25_1 _hx26_1 _hx27_1 _hx28_1 hx29_1 hvregs1
    wp_steps 2
    rw [dotLoopPure_succ k 0 coeffs xs acc hkc hkx] at hnext
    dsimp only [dotLoopPure] at hnext
    exact hnext _ hcl1 (by wp_norm_lhs) (by wp_norm_lhs) (by simpa [arm64_norm, wp_norm] using hsp1)
      (by simpa [arm64_norm, wp_norm] using htr1)
      (hvm1.trans (by simp only [wp_norm, arm64_norm]))
      (by simpa [arm64_norm, wp_norm] using hx20_1)
      (by simpa [arm64_norm, wp_norm] using hx29_1)
      (by simpa [arm64_norm, wp_norm] using hvregs1)
  | succ r' ih =>
    intro k acc hkr s F hcl hpc hrun hsp hx19 hx20 hx21 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hnext
    have hkc : k < coeffs.length := by omega
    have hkx : k < xs.length := by omega
    rcases subs_succ_one_ne_zero (r := r') (by omega) with ⟨hneq1, hneq2⟩
    apply dotStep_placed_vm_sepWP ext hOnce sp0 p_coeffs p_xs hsp0 hpx_al coeffs xs (r' + 1) k acc hkc hkx
      ret_pc Q s F hcl hpc hrun hsp hx19 hx20 hx21 hx23 hx24 hx25 hx26 hx27 hx28 hx29
    intro s1 hcl1 hpc1 hrun1 hsp1 htr1 hvm1 hpst1 hx19_1 hx20_1 hx21_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs1
    wp_steps 1
    apply ih (k + 1) (GF16.add acc (GF16.mul (coeffs[k]'hkc) (xs[k]'hkx)))
      (by omega) _ F (by exact hcl1)
      (by simp only [arm64_norm, wp_norm, bne, hneq2]) (by wp_norm_lhs)
      (by simpa [arm64_norm, wp_norm] using hsp1)
      (by simpa [arm64_norm, wp_norm] using hx19_1)
      (by simpa [arm64_norm, wp_norm] using hx20_1)
      (by simpa [arm64_norm, wp_norm] using hx21_1)
      (by simpa [arm64_norm, wp_norm] using hx23_1)
      (by simpa [arm64_norm, wp_norm] using hx24_1)
      (by simpa [arm64_norm, wp_norm] using hx25_1)
      (by simpa [arm64_norm, wp_norm] using hx26_1)
      (by simpa [arm64_norm, wp_norm] using hx27_1)
      (by simpa [arm64_norm, wp_norm] using hx28_1)
      (by simpa [arm64_norm, wp_norm] using hx29_1)
    intro sf hcl_f hpc_f hrun_f hsp_f htr_f hvm_f hx20_f hx29_f hvregs_f
    rw [dotLoopPure_succ k (r' + 1) coeffs xs acc hkc hkx] at hnext
    exact hnext sf hcl_f hpc_f hrun_f hsp_f
      (by rw [htr_f]; simpa [arm64_norm, wp_norm] using htr1)
      ((hvm1.trans (by simp only [wp_norm, arm64_norm])).trans hvm_f)
      hx20_f hx29_f
      (by rw [hvregs_f]; simpa [arm64_norm, wp_norm] using hvregs1)

set_option maxHeartbeats 1600000 in
theorem dot_from_61ab4_placed_vm_sepWP [LibsignalPlacement]
    (ext : String → Option (State → State))
    (hOnce : OnceCallHookOk (Rust.withPanics ext))
    (a : ComputeAtArgs) (hlen_pos : 0 < a.poly.coefficients.length)
    (hlen_bound : 2 * a.poly.coefficients.length + 2 ≤ 2 ^ 63)
    (sp0 p_xs : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64) (hp_xs : p_xs &&& 1#64 = 0#64)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop)
    (s : State) (F : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_371).base + 416#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 144#64)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (max 2 a.poly.coefficients.length))
    (hx19 : s.readReg64 .x19 = a.p_coeffs)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 a.poly.coefficients.length)
    (hx23 : s.readReg64 .x23 = lsρ tokenName + 8#64)
    (hx24 : s.readReg64 .x24 = lsρ reduceTableSym)
    (hx25 : s.readReg64 .x25 = Arm64.Obj.pageOf (lsρ tokenStorageName))
    (hx27 : s.readReg64 .x27 = p_xs)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hnext : ∀ sf : State,
      LibsignalCodeLoaded lsmpl sf.mem →
      sf.pc = (blkPl_371).base + 616#64 →
      sf.status = .Running →
      sf.sp = sp0 - 144#64 →
      sf.trace = s.trace →
      VmPreserved s sf →
      BitVec.truncate 16 (sf.readReg64 .x20) = (computeAtPure a.poly a.x).value →
      sf.readReg64 .x29 = sp0 - 96#64 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext)) ret_pc sf
        (gf16SliceAt a.p_coeffs a.poly.coefficients ∗
         gf16SliceAt p_xs (computeAtPowersPure a.poly.coefficients.length a.x) ∗
         memRegion (sp0 - 144#64) 8 ∗
         memRegion (sp0 - 112#64) 16 ∗
         stackAt (sp0 - 144#64) growOneStack ∗
         tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ F) Q) :
    SepWP ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext)) ret_pc s
      (gf16SliceAt a.p_coeffs a.poly.coefficients ∗
       gf16SliceAt p_xs (computeAtPowersPure a.poly.coefficients.length a.x) ∗
       memRegion (sp0 - 144#64) 8 ∗
       memRegion (sp0 - 112#64) 16 ∗
       stackAt (sp0 - 144#64) growOneStack ∗
       tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ F) Q := by
  rcases ofNat_beq_false_of_lt hlen_pos (by omega) with ⟨_, _, hlen_ne0, _⟩
  have hult_false :
      (BitVec.ofNat 64 (max 2 a.poly.coefficients.length)).ult
        (BitVec.ofNat 64 a.poly.coefficients.length) = false :=
    ult_max_two_false a.poly.coefficients.length hlen_bound
  wp_steps 10
  have hle_powers :
      a.poly.coefficients.length ≤
        (computeAtPowersPure a.poly.coefficients.length a.x).length := by
    rw [computeAtPowersPure_length]; omega
  have hr_eq :
      BitVec.ofNat 64 a.poly.coefficients.length =
        BitVec.ofNat 64 (a.poly.coefficients.length - 1 + 1) := by
    congr 1; omega
  apply dotLoop_placed_vm_sepWP ext hOnce sp0 a.p_coeffs p_xs hsp0 hp_xs
    a.poly.coefficients (computeAtPowersPure a.poly.coefficients.length a.x)
    hle_powers hlen_bound ret_pc Q
    (a.poly.coefficients.length - 1) 0 GF16.ZERO (by omega)
    _ F (by exact hcl)
    (by wp_norm_lhs)
    (by wp_norm_lhs)
    (by simpa [arm64_norm, wp_norm] using hsp)
    (by simpa [arm64_norm, wp_norm] using hx19)
    (by rfl)
    (by wp_norm_lhs)
    (by simpa [arm64_norm, wp_norm] using hx23)
    (by simpa [arm64_norm, wp_norm] using hx24)
    (by simpa [arm64_norm, wp_norm] using hx25)
    (by simp only [arm64_norm, wp_norm])
    (by simpa [arm64_norm, wp_norm] using hx27)
    (by simp only [arm64_norm, wp_norm, hr_eq])
    (by simpa [arm64_norm, wp_norm] using hx29)
  intro sf hcl_f hpc_f hrun_f hsp_f htr_f hvm_f hx20_f hx29_f hvregs_f
  have hdot_eq :
      dotLoopPure 0 (a.poly.coefficients.length - 1 + 1)
        a.poly.coefficients (computeAtPowersPure a.poly.coefficients.length a.x) GF16.ZERO =
        computeAtPure a.poly a.x := by
    rw [Nat.sub_add_cancel hlen_pos, ← computeAtPure_eq_dotLoopPure]
  rw [hdot_eq] at hx20_f
  exact hnext sf hcl_f hpc_f hrun_f hsp_f
    (by simpa [arm64_norm, wp_norm] using htr_f)
    ((by simp only [wp_norm, arm64_norm] : VmPreserved s _).trans hvm_f)
    hx20_f hx29_f
    (by simpa [arm64_norm, wp_norm] using hvregs_f)

end CryptoVerification.SpqrV1.Poly.ComputeAt
