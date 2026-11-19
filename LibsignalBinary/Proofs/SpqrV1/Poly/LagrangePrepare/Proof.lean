/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.PolyPart1CodeSym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Defs
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp
public meta import ProofLib.GenDecodes
public meta import ProofLib.SepLogic.CodeLookup
public meta import ProofLib.VCGen
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<Poly>::lagrange_interpolate_prepare`: Binary Verification

Verifies `<spqr::encoding::polynomial::Poly>::lagrange_interpolate_prepare` (`0x61c1c`,
Block `372`) against `lagrangePrepareSpec` and `lagrangePreparePlacedSpec`.
-/

public section

namespace CryptoVerification.SpqrV1.Poly.LagrangePrepare

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open LibsignalBinary.Heap (VmPreserved)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

private theorem sp_setMem_lp (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by cases s; rfl
private theorem pc_setMem_lp (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by cases s; rfl
private theorem status_setMem_lp (s : State) (m : Memory) : (s.setMem m).status = s.status := by
  cases s; rfl
private theorem pstate_setMem_lp (s : State) (m : Memory) : (s.setMem m).pstate = s.pstate := by
  cases s; rfl
private theorem trace_setMem_lp (s : State) (m : Memory) : (s.setMem m).trace = s.trace := by
  cases s; rfl
private theorem readReg64_setMem_lp (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases s; cases r <;> rfl
private theorem readReg32_setMem_lp (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by cases s; cases r <;> rfl
private theorem readReg_setMem_lp (s : State) (m : Memory) (w : RegWidth) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by cases w <;> cases s <;> cases r <;> rfl
private theorem calleeSavedVRegs_setMem_lp (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by cases s; rfl

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_lp pc_setMem_lp status_setMem_lp pstate_setMem_lp trace_setMem_lp
  readReg64_setMem_lp readReg32_setMem_lp readReg_setMem_lp calleeSavedVRegs_setMem_lp
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
attribute [local wp_norm] zeroExtend_16_truncate_32_64
attribute [local arm64_norm, local wp_norm]
  ofNat_shl_two truncate32_sext64_16 sbfx64_one_eq
  truncate32_if_all_ones truncate32_zext64 zext64_zext32_16
  and_65535_zext64_16 prepare_polyReduce_xor_eq

private theorem sepWPp_seq_lscl_lp [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => LibsignalCodeLoaded lsmpl sm.mem → SepWPp prog ret sm Pm Q Qp oom) oom) :
    SepWPp prog ret s P Q Qp oom :=
  SepWPp.seq_frozen (fun _ _ => LibsignalCodeLoaded.of_keepsFrozen) hcl h1

set_option maxHeartbeats 1600000 in
private theorem outerStep_placed_vm_sepWP [LibsignalPlacement]
    (ext : String → Option (State → State))
    (hOnce : OnceCallHookOk (Rust.withPanics ext))
    (sp0 ptr ptsPtr : BitVec 64)
    (hsp0 : sp0 &&& 0xf#64 = 0#64) (hptr_al : ptr &&& 1#64 = 0#64)
    (pts : List Pt) (hn_bound : pts.length + 1 < 2 ^ 63)
    (r_out i : Nat) (p : Poly)
    (hi_rem : i + (r_out + 1) = pts.length) (hp_len : p.coefficients.length = pts.length + 1)
    (hi : i < pts.length)
    (v160 v152 v144 : BitVec 64)
    (w132 w128 w124 w120 w116 : BitVec 32)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop)
    (s : State) (F : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_372).base + 132#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 208#64)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 i)
    (hx19 : s.readReg64 .x19 = ptr + BitVec.ofNat 64 (2 * r_out))
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 pts.length)
    (hx23 : s.readReg64 .x23 = lsρ reduceTableSym)
    (hx27 : s.readReg64 .x27 = 0#64 - BitVec.ofNat 64 (i + 1))
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hnext : ∀ sf : State,
      LibsignalCodeLoaded lsmpl sf.mem →
      sf.pc = (blkPl_372).base + 588#64 →
      sf.status = .Running →
      sf.sp = sp0 - 208#64 →
      sf.trace = s.trace →
      VmPreserved s sf →
      sf.pstate = subsPState64 (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 pts.length) →
      sf.readReg64 .x9 = BitVec.ofNat 64 (i + 1) →
      sf.readReg64 .x19 = ptr + BitVec.ofNat 64 (2 * r_out) - 2#64 →
      sf.readReg64 .x20 = BitVec.ofNat 64 pts.length →
      sf.readReg64 .x23 = lsρ reduceTableSym →
      sf.readReg64 .x27 = 0#64 - BitVec.ofNat 64 (i + 1) - 1#64 →
      sf.readReg64 .x29 = sp0 - 96#64 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP ((blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext)) ret_pc sf
        (tokenInitPlacedAt ∗
         memRegion (sp0 - 208#64) 16 ∗
         memRegion (sp0 - 112#64) 16 ∗
         stackAt (sp0 - 208#64) allocHookStack ∗
         ((sp0 - 132#64) ↦₃₂ sbfxMask32 (pts[i]'hi).x.value 10) ∗
         ((sp0 - 128#64) ↦₃₂ sbfxMask32 (pts[i]'hi).x.value 11) ∗
         ((sp0 - 124#64) ↦₃₂ sbfxMask32 (pts[i]'hi).x.value 12) ∗
         ((sp0 - 120#64) ↦₃₂ sbfxMask32 (pts[i]'hi).x.value 13) ∗
         ((sp0 - 116#64) ↦₃₂ sbfxMask32 (pts[i]'hi).x.value 14) ∗
         gf16SliceAt ptr
           (multXdiffLoopPure (pts[i]'hi).x (r_out + 1) (i + 1) p.coefficients) ∗
         reduceTablePlacedAt ∗
         ((sp0 - 168#64) ↦₆₄ ptsPtr) ∗
         ((sp0 - 160#64) ↦₆₄ BitVec.ofNat 64 (i + 1)) ∗
         ((sp0 - 152#64) ↦₆₄ (0#64 - BitVec.ofNat 64 (i + 1))) ∗
         ((sp0 - 144#64) ↦₆₄ (ptr + BitVec.ofNat 64 (2 * r_out))) ∗
         ptSliceAt ptsPtr pts ∗ F) Q) :
    SepWP ((blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext)) ret_pc s
      (tokenInitPlacedAt ∗
       memRegion (sp0 - 208#64) 16 ∗
       memRegion (sp0 - 112#64) 16 ∗
       stackAt (sp0 - 208#64) allocHookStack ∗
       ((sp0 - 132#64) ↦₃₂ w132) ∗
       ((sp0 - 128#64) ↦₃₂ w128) ∗
       ((sp0 - 124#64) ↦₃₂ w124) ∗
       ((sp0 - 120#64) ↦₃₂ w120) ∗
       ((sp0 - 116#64) ↦₃₂ w116) ∗
       gf16SliceAt ptr p.coefficients ∗
       reduceTablePlacedAt ∗
       ((sp0 - 168#64) ↦₆₄ ptsPtr) ∗
       ((sp0 - 160#64) ↦₆₄ v160) ∗
       ((sp0 - 152#64) ↦₆₄ v152) ∗
       ((sp0 - 144#64) ↦₆₄ v144) ∗
       ptSliceAt ptsPtr pts ∗ F) Q := by
  have hi_succ : BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := by
    rw [← BitVec.ofNat_add]
  apply sepWP_seq_lscl (by exact hcl) (mid := (blkPl_372).base + 212#64)
  apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
    (Q := (blkPC_372).rebase (blkPl_372).base
      (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException (Rust.withPanics ext)))
    blkLib_eq_372 (mid := (blkPl_372).base + 212#64)
  intro _m_strip
  wp_conv_pre => rw [ptSliceAt_focus_x_assoc hi ptsPtr]
  wp_steps 20
  wp_conv_pre => rw [← ptSliceAt_focus_x_assoc hi ptsPtr]
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  have hvm_pre : VmPreserved s _ := _hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  intro hcl_mid
  apply innerLoop_placed_sepWP ext hOnce sp0 ptr hsp0 hptr_al pts.length hn_bound (pts[i]'hi).x.value
    ret_pc Q i (r_out + 1) p.coefficients (by omega) (by omega) hp_len _
    (((sp0 - 168#64) ↦₆₄ ptsPtr) ∗
     ((sp0 - 160#64) ↦₆₄ BitVec.ofNat 64 (i + 1)) ∗
     ((sp0 - 152#64) ↦₆₄ (0#64 - BitVec.ofNat 64 (i + 1))) ∗
     ((sp0 - 144#64) ↦₆₄ (ptr + BitVec.ofNat 64 (2 * r_out))) ∗
     ptSliceAt ptsPtr pts ∗ F)
    hcl_mid
    (by wp_norm_lhs) (by wp_norm_lhs)
    (by simpa [arm64_norm, wp_norm] using hsp)
    (by simpa [arm64_norm, wp_norm] using hx19)
    (by simpa [arm64_norm, wp_norm] using hx20)
    (by simp only [arm64_norm, wp_norm]; exact sbfxMask64_from_if _ _)
    (by simp only [arm64_norm, wp_norm]; exact sbfxMask64_from_if _ _)
    (by simpa [arm64_norm, wp_norm] using hx23)
    (by wp_norm_lhs) (by wp_norm_lhs)
    (by simp only [arm64_norm, wp_norm]; exact sbfxMask64_from_if _ _)
    (by simpa [arm64_norm, wp_norm] using hx27)
    (by simp only [arm64_norm, wp_norm]; exact sbfxMask64_from_if _ _)
    (by simpa [arm64_norm, wp_norm] using hx29)
  intro s1 hcl1 hpc1 hrun1 hsp1 htrace1 hvm1 hx20_1 hx23_1 hx29_1 hvregs1
  have htrace1' : s1.trace = s.trace := by simpa [arm64_norm, wp_norm] using htrace1
  have hvregs1' : calleeSavedVRegs s1 = calleeSavedVRegs s := by simpa [arm64_norm, wp_norm] using hvregs1
  apply sepWP_seq_lscl (by exact hcl1) (mid := (blkPl_372).base + 588#64)
  wp_steps 5
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  intro hcl_f
  apply hnext _ hcl_f (by wp_norm_lhs) (by wp_norm_lhs)
    (by simpa [arm64_norm, wp_norm] using hsp1)
    (by simpa [arm64_norm, wp_norm] using htrace1')
    ((hvm_pre.trans hvm1).trans (by simp only [wp_norm, arm64_norm]))
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    (by simpa [arm64_norm, wp_norm] using hx20_1)
    (by simpa [arm64_norm, wp_norm] using hx23_1)
    (by wp_norm_lhs)
    (by simpa [arm64_norm, wp_norm] using hx29_1)
    (by simpa [arm64_norm, wp_norm] using hvregs1')

set_option maxHeartbeats 1600000 in
theorem outerLoop_placed_vm_sepWP [LibsignalPlacement]
    (ext : String → Option (State → State))
    (hOnce : OnceCallHookOk (Rust.withPanics ext))
    (sp0 ptr ptsPtr : BitVec 64)
    (hsp0 : sp0 &&& 0xf#64 = 0#64) (hptr_al : ptr &&& 1#64 = 0#64)
    (pts : List Pt) (hn_bound : pts.length + 1 < 2 ^ 63)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop) :
    ∀ (r_out i : Nat) (p : Poly)
      (_hi_rem : i + (r_out + 1) = pts.length) (_hp_len : p.coefficients.length = pts.length + 1)
      (v160 v152 v144 : BitVec 64)
      (w132 w128 w124 w120 w116 : BitVec 32)
      (s : State) (F : SepProp),
      LibsignalCodeLoaded lsmpl s.mem →
      s.pc = (blkPl_372).base + 132#64 →
      s.status = .Running →
      s.sp = sp0 - 208#64 →
      s.readReg64 .x9 = BitVec.ofNat 64 i →
      s.readReg64 .x19 = ptr + BitVec.ofNat 64 (2 * r_out) →
      s.readReg64 .x20 = BitVec.ofNat 64 pts.length →
      s.readReg64 .x23 = lsρ reduceTableSym →
      s.readReg64 .x27 = 0#64 - BitVec.ofNat 64 (i + 1) →
      s.readReg64 .x29 = sp0 - 96#64 →
      (∀ (v160' v152' v144' : BitVec 64) (w132' w128' w124' w120' w116' : BitVec 32) (sf : State),
        sf.pc = (blkPl_372).base + 608#64 →
        sf.status = .Running →
        sf.sp = sp0 - 208#64 →
        sf.trace = s.trace →
        VmPreserved s sf →
        calleeSavedVRegs sf = calleeSavedVRegs s →
        SepWP ((blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext)) ret_pc sf
          (tokenInitPlacedAt ∗
           memRegion (sp0 - 208#64) 16 ∗
           memRegion (sp0 - 112#64) 16 ∗
           stackAt (sp0 - 208#64) allocHookStack ∗
           ((sp0 - 132#64) ↦₃₂ w132') ∗
           ((sp0 - 128#64) ↦₃₂ w128') ∗
           ((sp0 - 124#64) ↦₃₂ w124') ∗
           ((sp0 - 120#64) ↦₃₂ w120') ∗
           ((sp0 - 116#64) ↦₃₂ w116') ∗
           gf16SliceAt ptr (prepareLoopPure pts pts.length i (r_out + 1) p).coefficients ∗
           reduceTablePlacedAt ∗
           ((sp0 - 168#64) ↦₆₄ ptsPtr) ∗
           ((sp0 - 160#64) ↦₆₄ v160') ∗
           ((sp0 - 152#64) ↦₆₄ v152') ∗
           ((sp0 - 144#64) ↦₆₄ v144') ∗
           ptSliceAt ptsPtr pts ∗ F) Q) →
      SepWP ((blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext)) ret_pc s
        (tokenInitPlacedAt ∗
         memRegion (sp0 - 208#64) 16 ∗
         memRegion (sp0 - 112#64) 16 ∗
         stackAt (sp0 - 208#64) allocHookStack ∗
         ((sp0 - 132#64) ↦₃₂ w132) ∗
         ((sp0 - 128#64) ↦₃₂ w128) ∗
         ((sp0 - 124#64) ↦₃₂ w124) ∗
         ((sp0 - 120#64) ↦₃₂ w120) ∗
         ((sp0 - 116#64) ↦₃₂ w116) ∗
         gf16SliceAt ptr p.coefficients ∗
         reduceTablePlacedAt ∗
         ((sp0 - 168#64) ↦₆₄ ptsPtr) ∗
         ((sp0 - 160#64) ↦₆₄ v160) ∗
         ((sp0 - 152#64) ↦₆₄ v152) ∗
         ((sp0 - 144#64) ↦₆₄ v144) ∗
         ptSliceAt ptsPtr pts ∗ F) Q := by
  intro r_out
  induction r_out with
  | zero =>
    intro i p hi_rem hp_len v160 v152 v144 w132 w128 w124 w120 w116 s F
      hcl hpc hrun hsp hx9 hx19 hx20 hx23 hx27 hx29 hnext
    have hi : i < pts.length := by omega
    apply outerStep_placed_vm_sepWP ext hOnce sp0 ptr ptsPtr hsp0 hptr_al pts hn_bound
      0 i p hi_rem hp_len hi v160 v152 v144 w132 w128 w124 w120 w116 ret_pc Q s F
      hcl hpc hrun hsp hx9 hx19 hx20 hx23 hx27 hx29
    intro s1 _hcl1 hpc1 hrun1 hsp1 htrace1 hvm1 hpstate1 _hx9_1 _hx19_1 _hx20_1 _hx23_1 _hx27_1 _hx29_1 hvregs1
    have heq_len : i + 1 = pts.length := by omega
    rw [heq_len] at hpstate1
    wp_steps 2
    rw [prepareLoopPure_succ pts i 0 p hi_rem hp_len hi] at hnext
    dsimp only [prepareLoopPure] at hnext
    exact hnext
      (BitVec.ofNat 64 (i + 1)) (0#64 - BitVec.ofNat 64 (i + 1)) (ptr + BitVec.ofNat 64 (2 * 0))
      (sbfxMask32 (pts[i]'hi).x.value 10) (sbfxMask32 (pts[i]'hi).x.value 11)
      (sbfxMask32 (pts[i]'hi).x.value 12) (sbfxMask32 (pts[i]'hi).x.value 13)
      (sbfxMask32 (pts[i]'hi).x.value 14) _
      (by wp_norm_lhs) (by wp_norm_lhs)
      (by simpa [arm64_norm, wp_norm] using hsp1)
      (by simpa [arm64_norm, wp_norm] using htrace1)
      (hvm1.trans (by simp only [wp_norm, arm64_norm]))
      (by simpa [arm64_norm, wp_norm] using hvregs1)
  | succ r_out' ih =>
    intro i p hi_rem hp_len v160 v152 v144 w132 w128 w124 w120 w116 s F
      hcl hpc hrun hsp hx9 hx19 hx20 hx23 hx27 hx29 hnext
    have hi : i < pts.length := by omega
    apply outerStep_placed_vm_sepWP ext hOnce sp0 ptr ptsPtr hsp0 hptr_al pts hn_bound
      (r_out' + 1) i p hi_rem hp_len hi v160 v152 v144 w132 w128 w124 w120 w116 ret_pc Q s F
      hcl hpc hrun hsp hx9 hx19 hx20 hx23 hx27 hx29
    intro s1 hcl1 hpc1 hrun1 hsp1 htrace1 hvm1 hpstate1 hx9_1 hx19_1 hx20_1 hx23_1 hx27_1 hx29_1 hvregs1
    have hne_len := ofNat_bne_true_of_lt (a := i + 1) (b := pts.length) (by omega) (by omega)
    apply sepWP_seq_lscl (by exact hcl1) (mid := (blkPl_372).base + 132#64)
    wp_steps 1
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro hcl_next
    apply ih (i + 1) ⟨multXdiffLoopPure (pts[i]'hi).x (r_out' + 1 + 1) (i + 1) p.coefficients⟩
      (by omega) (by simp [multXdiffLoopPure_length, hp_len])
      (BitVec.ofNat 64 (i + 1)) (0#64 - BitVec.ofNat 64 (i + 1)) (ptr + BitVec.ofNat 64 (2 * (r_out' + 1)))
      (sbfxMask32 (pts[i]'hi).x.value 10) (sbfxMask32 (pts[i]'hi).x.value 11)
      (sbfxMask32 (pts[i]'hi).x.value 12) (sbfxMask32 (pts[i]'hi).x.value 13)
      (sbfxMask32 (pts[i]'hi).x.value 14) _ F hcl_next
      (by wp_norm_lhs) (by wp_norm_lhs)
      (by simpa [arm64_norm, wp_norm] using hsp1)
      (by simpa [arm64_norm, wp_norm] using hx9_1)
      (by simpa [arm64_norm, wp_norm, ptr_sub_two_succ ptr r_out'] using hx19_1)
      (by simpa [arm64_norm, wp_norm] using hx20_1)
      (by simpa [arm64_norm, wp_norm] using hx23_1)
      (by simpa [arm64_norm, wp_norm, neg_sub_one (i + 1)] using hx27_1)
      (by simpa [arm64_norm, wp_norm] using hx29_1)
    intro v160' v152' v144' w132' w128' w124' w120' w116' sf hpc_f hrun_f hsp_f htrace_f hvm_f hvregs_f
    rw [prepareLoopPure_succ pts i (r_out' + 1) p hi_rem hp_len hi] at hnext
    exact hnext v160' v152' v144' w132' w128' w124' w120' w116' sf hpc_f hrun_f hsp_f
      (by rw [htrace_f]; simpa [arm64_norm, wp_norm] using htrace1)
      ((hvm1.trans (by simp only [wp_norm, arm64_norm])).trans hvm_f)
      (by rw [hvregs_f]; simpa [arm64_norm, wp_norm] using hvregs1)

private theorem epilogue_placed_sepWP [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State))
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
      (A.pool ∗
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
            ⌜sf.trace = s0.trace⌝ ∗
              polyOf A a.out (lagrangePreparePure a.pts) ∗
                ptSliceAt a.ptsPtr a.pts ∗
                  reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗ stackAt s0.sp lagrangePrepareStack ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  have hbound : 4 * (a.pts.length + 1) < 2 ^ 63 := a.hlen_bound
  wp_steps
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
    (polyOf_of_exact_cap A a.out ptr (lagrangePreparePure a.pts) (a.pts.length + 1)
      (by omega) (lagrangePreparePure_length a.pts) (by omega) hptr_ne)
    (by sep_focus) ?_
  wp_done

/-- Relocatable (`[LibsignalPlacement]`) `<spqr::encoding::polynomial::Poly>::lagrange_interpolate_prepare`
(Block `372`) satisfies `lagrangePreparePlacedSpec A`. -/
theorem lagrangePrepare_placed_ok [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State))
    (h_panic : (Rust.withPanics ext) SpqrV1.Alloc.spqrHandleErrorSym = some Rust.panicked)
    (hshim : subroutine_ok ((blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext))
      (lsρ SpqrV1.Alloc.spqrRustNoAllocShimSym) sessionShimSpec)
    (halloc : subroutine_ok ((blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext))
      (lsρ SpqrV1.Alloc.spqrRustAllocSym) (rustAllocSpec A))
    (hmemset : subroutine_ok ((blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext))
      (lsρ memsetName) sessionMemsetRegionSpec)
    (hOnce : OnceCallHookOk (Rust.withPanics ext)) :
    subroutine_ok ((blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext))
      (blkPl_372).base (withLsCodeLoaded lsmpl (lagrangePreparePlacedSpec A)) := by
  have hpan_err :
      ((blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext)).externAt?
        (lsρ SpqrV1.Alloc.spqrHandleErrorSym) = some Rust.panicked :=
    (SpqrV1.Alloc.spqr_externAt?_of_mem).trans h_panic
  simp only [withLsCodeLoaded, lagrangePreparePlacedSpec]
  wpp_init a s0
  have hcl0 := h; have h := h_1; have h_1 := h_2; have h_2 := h_3; clear h_3
  have hsp0 : s0.sp &&& 0xf#64 = 0#64 := beq_iff_eq.mp hsp_align
  have hbound : 4 * (a.pts.length + 1) < 2 ^ 63 := a.hlen_bound
  have hbit62 : (((BitVec.ofNat 64 a.pts.length + 1#64) &&& 4611686018427387904#64) != 0#64) = false :=
    len_succ_bit62_false a.pts.length hbound
  have hshl_succ : (BitVec.ofNat 64 a.pts.length + 1#64) <<< 1#64 = BitVec.ofNat 64 (2 * (a.pts.length + 1)) :=
    ofNat_add_one_shl_one a.pts.length
  have hshl_succ_nat : (BitVec.ofNat 64 a.pts.length + 1#64) <<< (1 : Nat) = BitVec.ofNat 64 (2 * (a.pts.length + 1)) :=
    ofNat_add_one_shl_one_nat a.pts.length
  have htoNat_succ : (BitVec.ofNat 64 (2 * (a.pts.length + 1))).toNat = 2 * (a.pts.length + 1) :=
    ofNat_two_mul_succ_toNat a.pts.length hbound
  have hpow2 : ∃ k, 2 = 2 ^ k := ⟨1, rfl⟩
  apply sepWPp_seq_lscl_lp hcl0 (mid := (blkPl_372).base + 68#64)
  wp_simp_pre only [memRegion_24 a.out, stackAt_lagrangePrepare_split s0.sp]
  wp_pull_exists
  wp_steps 14
  wp_call hshim
  wp_steps 3
  wp_call halloc
  apply SepWP.done hpc_sf_1 (by wp_norm_lhs)
  intro hcl_sf1
  by_cases hptr0 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · have hcbz : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = true := beq_iff_eq.mpr hptr0
    wp_conv_pre => rw [alloc_post_pos hptr0]
    apply SepWPp.pure_left
    intro htr_fail
    apply SepWPp.of_sepWP (mid := lsρ SpqrV1.Alloc.spqrHandleErrorSym)
    wp_steps 4
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    have htr_panic_eq :
        (Rust.panicked ((((sf_1.writeReg64 (Reg.gpr 0#5) 2#64).writeReg64 (Reg.gpr 1#5)
          (BitVec.ofNat 64 (2 * (a.pts.length + 1)))).writeReg64 (Reg.gpr 30#5)
          ((blkPl_372).base + 680#64)).setPC
          (lsρ SpqrV1.Alloc.spqrHandleErrorSym))).trace = s0.trace ++ [allocFailedEvent] := by
      change sf_1.trace = s0.trace ++ [allocFailedEvent]
      rw [htr_fail, h_3]
    refine SepWPp.panic (by wp_norm_lhs)
      (by simpa [arm64_norm, wp_norm] using hpan_err)
      (fun hm => ?_)
    rw [← sepConj_assoc]
    refine allowPanic_panicked (φ := allocFailedIn s0 _ ∧ s0.trace <+: _) ⟨?_, ?_⟩ hm
    · exact allocFailedIn_of_trace_eq htr_panic_eq
    · rw [htr_panic_eq]; exact List.prefix_append s0.trace [allocFailedEvent]
  · have hcbz : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hptr0
    wp_conv_pre => rw [alloc_post_neg hptr0]
    apply SepWPp.pure_left
    rintro ⟨hptr_mod, htr_ok⟩
    apply SepWPp.of_sepWP_ret
    have hptr_al : sf_1.readReg64 (Reg.gpr 0#5) &&& 1#64 = 0#64 :=
      and_one_of_mod_two hptr_mod
    have hlen_add1 : BitVec.ofNat 64 a.pts.length + 1#64 = BitVec.ofNat 64 (a.pts.length + 1) := by
      rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
    wp_conv_pre => rw [h_4]
    apply sepWP_seq_lscl hcl_sf1 (mid := (blkPl_372).base + 84#64)
    wp_steps 4
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro hcl_84
    by_cases hpts_nil : a.pts = []
    · have hx20_0 : (BitVec.ofNat 64 a.pts.length == 0#64) = true := by rw [hpts_nil]; rfl
      have hmem2 :
          memRegion (sf_1.readReg64 (Reg.gpr 0#5)) (2 * (a.pts.length + 1)) =
            ∃∗ v0 : BitVec 16, (sf_1.readReg64 (Reg.gpr 0#5)) ↦₁₆ v0 := by
        rw [hpts_nil, List.length_nil, Nat.zero_add, Nat.mul_one, memRegion_two]
      wp_conv_pre => rw [hmem2]
      wp_pull_exists
      wp_steps 4
      have hslice_nil :
          ((sf_1.readReg64 (Reg.gpr 0#5)) ↦₁₆ 1#16) =
            gf16SliceAt (sf_1.readReg64 (Reg.gpr 0#5)) (lagrangePreparePure a.pts).coefficients := by
        rw [hpts_nil]
        simp [lagrangePreparePure, prepareLoopPure, gf16SliceAt, arrayAt, gf16At, GF16.ONE]
      wp_conv_pre => rw [hslice_nil]
      refine epilogue_placed_sepWP A ext a R s0 _ (sf_1.readReg64 (Reg.gpr 0#5))
        _ _ _ a.ptsPtr _ _ _ _ _ _ _ _ hsp0 hptr0 ?_ ?_ ?_ ?_ ?_
      · wp_norm_lhs
      · wp_norm_lhs
      · change sf_1.sp = s0.sp - 208#64; rw [hsp_sf, h_4]
      · change sf_1.trace = s0.trace; rw [htr_ok, h_3]
      · change calleeSavedVRegs sf_1 = calleeSavedVRegs s0; rw [hvregs_1, hvregs]
    · have hlen_pos : 0 < a.pts.length := List.length_pos_iff.mpr hpts_nil
      have hx20_ne0 : (BitVec.ofNat 64 a.pts.length == 0#64) = false := by
        rw [beq_eq_false_iff_ne]; intro h0
        have ht := congrArg BitVec.toNat h0
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
        change a.pts.length = 0 at ht; omega
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
        memRegion_alloc_split (sf_1.readReg64 (Reg.gpr 0#5)) a.pts.length (by omega)
      wp_conv_pre => rw [hsplit_alloc]
      wp_pull_exists
      apply sepWP_seq_lscl hcl_84 (mid := (blkPl_372).base + 132#64)
      wp_steps 5
      wp_call hmemset
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
      wp_conv_pre => rw [hrep_zero]
      wp_steps 7
      apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
      intro hcl_132
      wp_conv_pre => rw [combine_init_slice]
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
        have hlen_eq : a.pts.length = (a.pts.length - 1) + 1 := by omega
        conv => lhs; arg 1; arg 2; rw [hlen_eq]
        exact ptr_sub_two_succ (sf_1.readReg64 (Reg.gpr 0#5)) (a.pts.length - 1)
      apply outerLoop_placed_vm_sepWP ext hOnce s0.sp (sf_1.readReg64 (Reg.gpr 0#5)) a.ptsPtr
        hsp0 hptr_al a.pts (by omega) (s0.readReg64 Reg.lr) _
        (a.pts.length - 1) 0 ⟨List.replicate a.pts.length GF16.ZERO ++ [GF16.ONE]⟩
        (by omega) (by simp)
        _ _ _ _ _ _ _ _ _ _ hcl_132
        (by wp_norm_lhs)
        (by wp_norm_lhs)
        (by change sf_2.sp = s0.sp - 208#64; rw [hsp_sf_1, hsp_sf, h_4])
        (by wp_norm_lhs)
        (by simpa [arm64_norm, wp_norm] using hx19_init)
        (by simp only [arm64_norm, wp_norm, h_26, h_16, h_6])
        (by wp_norm_lhs)
        (by wp_norm_lhs)
        (by simp only [arm64_norm, wp_norm, hcs_sf_1, hcs_sf, hpost_sf])
      intro v160' v152' v144' w132' w128' w124' w120' w116' sf_loop hpc_loop hrun_loop hsp_loop htr_loop _hvm_loop hvregs_loop
      have hloop_eq :
          prepareLoopPure a.pts a.pts.length 0 (a.pts.length - 1 + 1)
            ⟨List.replicate a.pts.length GF16.ZERO ++ [GF16.ONE]⟩ =
            lagrangePreparePure a.pts := by
        rw [Nat.sub_add_cancel hlen_pos]; rfl
      wp_conv_pre => rw [hloop_eq]
      refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
        (epilogue_placed_sepWP A ext a R s0 sf_loop (sf_1.readReg64 (Reg.gpr 0#5))
          _ _ _ a.ptsPtr v160' v152' v144' w132' w128' w124' w120' w116' hsp0 hptr0
          hpc_loop hrun_loop hsp_loop
          (by rw [htr_loop]; change sf_2.trace = s0.trace; rw [hpost, htr_ok, h_3])
          (by rw [hvregs_loop]; change calleeSavedVRegs sf_2 = calleeSavedVRegs s0; rw [hvregs_2, hvregs_1, hvregs]))

theorem lagrangePrepare_placed_ok_of_hookSat [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State))
    (h_panic : (Rust.withPanics ext) SpqrV1.Alloc.spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) SpqrV1.Alloc.spqrRustNoAllocShimSym sessionShimSpec)
    (halloc : HookSat (Rust.withPanics ext) SpqrV1.Alloc.spqrRustAllocSym (rustAllocSpec A))
    (hmemset : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionSpec)
    (hOnce : OnceCallHookOk (Rust.withPanics ext)) :
    subroutine_ok ((blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext))
      (blkPl_372).base (withLsCodeLoaded lsmpl (lagrangePreparePlacedSpec A)) :=
  lagrangePrepare_placed_ok A ext h_panic
    (SpqrV1.Alloc.spqr_hook_ok_of_mem hshim)
    (SpqrV1.Alloc.spqr_hook_ok_of_mem halloc)
    (SpqrV1.Alloc.spqr_hook_ok_of_mem hmemset)
    hOnce

end CryptoVerification.SpqrV1.Poly.LagrangePrepare
