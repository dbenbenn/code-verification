/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SpillMem -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Arith
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1b

/-!
# `decapsulate_compressed_key` (`B04`) — Segment 3b (`+0x3860 → +0x3948`)

Proves the middle of Segment 3:
1. `B28(memcpy)` copying `inv` (`512` B) from `sp + 20704` to `sp + 11856` (`+0x3860 → +0x3864`),
2. 16-iteration `vPoly - to_std(inv)` + Barrett loop (`+0x3864 → +0x3908`),
3. Dual `B28(memcpy)` staging (`sp + 11856 → sp + 20704 → sp + 11856`, `+0x3908 → +0x3948`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3b

open Arm64 Arm64.Obj ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly16 neonBarrettReduce16 neonMontgomeryMul16 neonMontgomeryReduce16 sqdmulh16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (
  dup8x16 ext_lane16 lane16 lane16_dup8x16 lane16_pack8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  lane16_simdAdd8h lane16_simdMla8h lane16_simdMul8h lane16_simdSqdmulh8h
  lane16_simdSshr8h lane16_simdSub8h simdAdd8h simdMla8h simdMul8h
  simdSqdmulh8h simdSshr8h simdSub8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Arith (
  barrett_mla_0xf2ff montgomery_precomp_mul)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (entails_sub spAligned_of_chk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc (
  svc_simdAdd_8h svc_simdDup_8h_gpr svc_simdMla_8h svc_simdMovi_8h_1024
  svc_simdMul_8h svc_simdMvni_8h_f2ff svc_simdSqdmulh_8h svc_simdSshr_8h_1
  svc_simdSshr_8h_11 svc_simdSub_8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  PolyMem SepLoad128 SepStore128 polyVecNat step_ldpQ128 step_ldrQ128 step_stpQ128
  vecRangeBytes vecRangeBytes_length vecRangeMem_congr vecRangeMem_entails_memRegion
  vecRangeMem_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base (
  blk04_code_eq blk04_tree_size blkLib04 blkPC04 blkPl04 blkPlaceable04 blkTree04)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SpillMem (
  SepLoad128.spill21 Spill21 Spill21Mem)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1b (blk28_memcpy_04)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC04 blkLib04 blkTree04 blk04_code_eq blk04_tree_size
  via_placement blkPl04 blkPlaceable04 [0x3860 → 0x3944]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl04_ρ [MlKemPlacement] (sym : String) :
    blkPl04.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

@[simp, arm64_norm, wp_norm] private theorem readReg64_orFpsr' (s : State) (fl : BitVec 32) (r : Reg) :
    (s.orFpsr fl).readReg64 r = s.readReg64 r := State.readReg64_orFpsr s fl r
@[simp, arm64_norm, wp_norm] private theorem readVReg128_orFpsr' (s : State) (fl : BitVec 32) (r : BitVec 5) :
    (s.orFpsr fl).readVReg128 r = s.readVReg128 r := State.readVReg128_orFpsr s fl r
@[simp, arm64_norm, wp_norm] private theorem status_orFpsr' (s : State) (fl : BitVec 32) :
    (s.orFpsr fl).status = s.status := rfl
@[simp, arm64_norm, wp_norm] private theorem pc_orFpsr' (s : State) (fl : BitVec 32) :
    (s.orFpsr fl).pc = s.pc := rfl
@[simp, arm64_norm, wp_norm] private theorem sp_orFpsr' (s : State) (fl : BitVec 32) :
    (s.orFpsr fl).sp = s.sp := rfl
@[simp, arm64_norm, wp_norm] private theorem spAligned_orFpsr' (s : State) (fl : BitVec 32) :
    (s.orFpsr fl).spAligned = s.spAligned := rfl
@[simp, arm64_norm, wp_norm] private theorem pstate_orFpsr' (s : State) (fl : BitVec 32) :
    (s.orFpsr fl).pstate = s.pstate := rfl
@[simp, arm64_norm, wp_norm] private theorem mem_orFpsr' (s : State) (fl : BitVec 32) :
    (s.orFpsr fl).mem = s.mem := rfl

attribute [local wp_norm ↓ high]
  svc_simdAdd_8h svc_simdSub_8h svc_simdMul_8h svc_simdMla_8h
  svc_simdSqdmulh_8h svc_simdSshr_8h_1 svc_simdSshr_8h_11
  svc_simdMovi_8h_1024 svc_simdMvni_8h_f2ff svc_simdDup_8h_gpr

abbrev offSeg3bStart : BitVec 64 := 14432#64
abbrev offSeg3bEnd : BitVec 64 := 14664#64
private abbrev off3864 : BitVec 64 := 14436#64
private abbrev off3888 : BitVec 64 := 14472#64
private abbrev off3904 : BitVec 64 := 14596#64
private abbrev off3908 : BitVec 64 := 14600#64
private abbrev off3930 : BitVec 64 := 14640#64

/-- Difference polynomial `neonBarrettReduce16 (vPoly[i] - neonMontgomeryMul16 inv[i] 1441)` (`B04 +0x3888..+0x3904`). -/
@[expose] def seg3SubPoly (inv vPoly : Poly16) : Poly16 :=
  Array.ofFn (n := 256) fun ⟨i, _⟩ =>
    neonBarrettReduce16 (vPoly.getD i 0#16 - neonMontgomeryMul16 (inv.getD i 0#16) 1441#16)

@[simp] theorem seg3SubPoly_size (inv vPoly : Poly16) :
    (seg3SubPoly inv vPoly).size = 256 := by simp [seg3SubPoly]

private theorem seg3SubLoop_vec_eq (inv vPoly : Poly16) (idx : Nat) (hidx : idx < 32) (commSum : Bool) :
    let qx := polyVecNat inv idx
    let qv := polyVecNat vPoly idx
    let negNormal := simdSub8h
      (simdSshr8h (simdSqdmulh8h (simdMul8h qx (dup8x16 55457#16)) (dup8x16 3329#16)) 1)
      (simdSshr8h (simdSqdmulh8h qx (dup8x16 1441#16)) 1)
    let diff := if commSum then simdAdd8h qv negNormal else simdAdd8h negNormal qv
    let quot := simdSshr8h (simdAdd8h (simdSqdmulh8h diff (dup8x16 20159#16)) (dup8x16 1024#16)) 11
    simdMla8h diff quot (dup8x16 62207#16) = polyVecNat (seg3SubPoly inv vPoly) idx := by
  dsimp only
  apply ext_lane16; intro i
  have hi256 : 8 * idx + i.val < 256 := by omega
  have hmont (x : BitVec 16) :
      (sqdmulh16 (x * 55457#16) 3329#16).sshiftRight 1 -
        (sqdmulh16 x 1441#16).sshiftRight 1 = -(neonMontgomeryMul16 x 1441#16) := by
    unfold neonMontgomeryMul16 neonMontgomeryReduce16; dsimp only
    rw [montgomery_precomp_mul x 1441#16, show (1441#16 * 62209#16) = 55457#16 from rfl]
    bv_omega
  have hget : (seg3SubPoly inv vPoly).getD (8 * idx + i.val) 0#16 =
      neonBarrettReduce16
        (vPoly.getD (8 * idx + i.val) 0#16 -
          neonMontgomeryMul16 (inv.getD (8 * idx + i.val) 0#16) 1441#16) := by
    simp [seg3SubPoly, Array.getD, hi256]
  have hd0 (a b : BitVec 16) : -b + a = a - b := by bv_omega
  have hd1 (a b : BitVec 16) : a + -b = a - b := by bv_omega
  cases commSum
  · simp only [Bool.false_eq_true, ↓reduceIte, polyVecNat, lane16_pack8x16, lane16_simdMla8h,
      lane16_simdSshr8h, lane16_simdAdd8h, lane16_simdSqdmulh8h, lane16_simdSub8h,
      lane16_simdMul8h, lane16_dup8x16, hmont, hd0, hget]
    rw [barrett_mla_0xf2ff]; rfl
  · simp only [↓reduceIte, polyVecNat, lane16_pack8x16, lane16_simdMla8h,
      lane16_simdSshr8h, lane16_simdAdd8h, lane16_simdSqdmulh8h, lane16_simdSub8h,
      lane16_simdMul8h, lane16_dup8x16, hmont, hd1, hget]
    rw [barrett_mla_0xf2ff]; rfl


attribute [local irreducible]
  blkPC04 polyVecNat dup8x16 simdAdd8h simdSub8h simdMul8h simdMla8h
  simdSqdmulh8h simdSshr8h seg3SubPoly

/-! ## 1. `memcpy` In (`+0x3860`) & Loop Setup (`+0x3864 → +0x3888`) -/

private theorem seg3b_memcpy_in [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) (inv : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offSeg3bStart) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = sp + 11856#64) (hx1 : s.readReg64 .x1 = sp + 20704#64)
    (hx2 : s.readReg64 .x2 = 512#64) (hx20 : s.readReg64 .x20 = sp + 11856#64)
    (_hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + off3864) s
      (memRegion (sp + 11856#64) 512 ∗ PolyMem (sp + 20704#64) (polyVecNat inv) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .x20 = sp + 11856#64 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .fp = s.readReg64 .fp ∧
        Pf = (PolyMem (sp + 11856#64) (polyVecNat inv) ∗
          PolyMem (sp + 20704#64) (polyVecNat inv) ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  generalize hbs_def : vecRangeBytes 32 (polyVecNat inv) = bsInv
  have hbs : bsInv.length = 512 := by rw [← hbs_def, vecRangeBytes_length]
  have hp20704 : PolyMem (sp + 20704#64) (polyVecNat inv) = ((sp + 20704#64) ↦ₛ bsInv) := by
    rw [← hbs_def]; exact vecRangeMem_eq_pointsToBytes 32 _ _
  have hp11856 : ((sp + 11856#64) ↦ₛ bsInv) = PolyMem (sp + 11856#64) (polyVecNat inv) := by
    rw [← hbs_def]; exact (vecRangeMem_eq_pointsToBytes 32 _ _).symm
  rw [hp20704]
  wp_call (blk28_memcpy_04 blkPl04.base) (sp + 11856#64, sp + 20704#64, bsInv)
  rw [← hp20704, hp11856]
  have hsp_sf : sf.sp = sp := by simp [*]
  exact SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨hsp_sf, spAligned_of_chk hsp_sf hsp_chk, by simp [*],
      by simp [*], by simp [*], by simp [*], by simp [*],
      sepProp_ext (by sep_frame) (by sep_frame)⟩

private theorem seg3b_setup [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl04 b)
    (s : State) (sp : BitVec 64) (tOut : Spill21) (Rest : SepProp)
    (hpc : s.pc = b + off3864) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = sp + 11856#64)
    (hs14 : tOut.s14 = dup8x16 20159#16) (hs19 : tOut.s19 = dup8x16 3329#16) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + off3888) s
      (Spill21Mem (sp + 1920#64) tOut ∗ Rest)
      (fun s1 P1 =>
        s1.sp = sp ∧ s1.spAligned = true ∧
        s1.readReg64 .x8 = 0#64 ∧ s1.readReg64 .x9 = 1441#64 ∧
        s1.readReg64 .x10 = 55457#64 ∧ s1.readReg64 .x11 = sp + 19168#64 ∧
        s1.readReg64 .x20 = sp + 11856#64 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧ s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧ s1.readReg64 .fp = s.readReg64 .fp ∧
        s1.readVReg128 5#5 = dup8x16 3329#16 ∧ s1.readVReg128 6#5 = dup8x16 20159#16 ∧
        s1.readVReg128 7#5 = dup8x16 1024#16 ∧ s1.readVReg128 16#5 = dup8x16 62207#16 ∧
        P1 = (Spill21Mem (sp + 1920#64) tOut ∗ Rest)) := by
  have _ : b = blkPl04.base := _hb
  wp_steps 2
  refine step_ldrQ128 (wb := none) (ea := sp + 2144#64) (v := dup8x16 20159#16)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simpa [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned] using hspA)
    (by simp [evalAddrMode, hsp])
    (SepLoad128.left (SepLoad128.spill21 (ptr := sp + 1920#64) (ea := sp + 2144#64) (k := 14)
      (by decide) (by clear * -; bv_omega) (by simpa [Spill21.get] using hs14)))
    (by wp_norm_lhs) ?_
  refine step_ldrQ128 (wb := none) (ea := sp + 2224#64) (v := dup8x16 3329#16)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simpa [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned] using hspA)
    (by simp [evalAddrMode, hsp])
    (SepLoad128.left (SepLoad128.spill21 (ptr := sp + 1920#64) (ea := sp + 2224#64) (k := 19)
      (by decide) (by clear * -; bv_omega) (by simpa [Spill21.get] using hs19)))
    (by wp_norm_lhs) ?_
  wp_steps 5
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
      by simp, by simp, by simp, by simp, by simp [hx20],
      by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp, rfl⟩

/-! ## 2. 16-Iteration `vPoly - to_std(inv)` + Barrett Loop (`+0x3888 → +0x3908`) -/

private theorem update2_split {f g0 g1 : Nat → BitVec 128} {r : Nat}
    (hlo : ∀ j, j < 2 * r → f j = g1 j)
    (hhi : ∀ j, 2 * r ≤ j → j < 32 → f j = g0 j) :
    let f' := Function.update (Function.update f (2 * r) (g1 (2 * r)))
      (2 * r + 1) (g1 (2 * r + 1))
    (∀ j, j < 2 * (r + 1) → f' j = g1 j) ∧
    (∀ j, 2 * (r + 1) ≤ j → j < 32 → f' j = g0 j) := by
  refine ⟨fun j hj => ?_, fun j hj1 hj2 => ?_⟩
  · by_cases h1 : j = 2 * r + 1
    · subst h1; simp
    · rw [Function.update_of_ne h1]
      by_cases h0 : j = 2 * r
      · subst h0; simp
      · rw [Function.update_of_ne h0]; exact hlo j (by omega)
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact hhi j (by omega) hj2

private theorem polyMem_congr {ptr : BitVec 64} {f g : Nat → BitVec 128}
    (h : ∀ i, i < 32 → f i = g i) : PolyMem ptr f = PolyMem ptr g :=
  vecRangeMem_congr h

private theorem seg3b_cond_eq (r : Fin 16) :
    ConditionHolds .NE (subsPState64 (BitVec.ofNat 64 (32 * (r.val + 1))) 512#64) =
      decide (r.val < 15) := by
  revert r; decide +kernel

private theorem step_bCond_taken {P : Program} {target_pc pc off dst : BitVec 64}
    {c : CondCode} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : P.fetch pc = some (.bCond c off))
    (hcond : ConditionHolds c s.pstate = true) (hdst : pc + off = dst)
    (hnext : SepWP P target_pc (s.setPC dst) Pre post oom) :
    SepWP P target_pc s Pre post oom :=
  SepWP.step_pure (s' := s.setPC dst) hpc hrun hfetch
    (by rw [_root_.Arm64.Program.evalInst_of_isSvc0Instr_false _ (.bCond c off) _ rfl]
        simp [wp_norm, arm64_norm, hcond, hdst])
    rfl hnext

private theorem step_bCond_not_taken {P : Program} {target_pc pc off dst : BitVec 64}
    {c : CondCode} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : P.fetch pc = some (.bCond c off))
    (hcond : ConditionHolds c s.pstate = false) (hdst : pc + 4#64 = dst)
    (hnext : SepWP P target_pc (s.setPC dst) Pre post oom) :
    SepWP P target_pc s Pre post oom :=
  SepWP.step_pure (s' := s.setPC dst) hpc hrun hfetch
    (by rw [_root_.Arm64.Program.evalInst_of_isSvc0Instr_false _ (.bCond c off) _ rfl]
        cases s; subst hpc; subst hdst
        simp [wp_norm, arm64_norm, hcond, State.advancePC, State.setPC])
    rfl hnext

private theorem seg3b_branch [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl04 b)
    {r : Nat} (hr : r < 16) (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = b + off3904) (hrun : s.status = .Running)
    (hpst : s.pstate = subsPState64 (BitVec.ofNat 64 (32 * (r + 1))) 512#64)
    (hpost : ∀ s', s'.sp = s.sp → s'.spAligned = s.spAligned →
      (∀ g : Reg, s'.readReg64 g = s.readReg64 g) →
      (∀ v : BitVec 5, s'.readVReg128 v = s.readVReg128 v) → post s' P) :
    SepWP (blkPC04.rebase b (fun _ => none))
      (if r < 15 then b + off3888 else b + off3908) s P post := by
  have _ : b = blkPl04.base := _hb
  have hcond := seg3b_cond_eq ⟨r, hr⟩
  by_cases hr15 : r < 15
  · simp only [hr15, ↓reduceIte]
    refine step_bCond_taken (pc := b + off3904) (dst := b + off3888) hpc hrun
      (by wp_norm_lhs) (by rw [hpst, hcond]; simp [hr15]) (by clear * -; bv_omega) ?_
    exact SepWP.done (by simp) (by simp [hrun])
      (hpost _ (by simp) (by simp [State.spAligned]) (fun _ => by simp) (fun _ => by simp))
  · simp only [hr15, ↓reduceIte]
    refine step_bCond_not_taken (pc := b + off3904) (dst := b + off3908) hpc hrun
      (by wp_norm_lhs) (by rw [hpst, hcond]; simp [hr15]) (by clear * -; bv_omega) ?_
    exact SepWP.done (by simp) (by simp [hrun])
      (hpost _ (by simp) (by simp [State.spAligned]) (fun _ => by simp) (fun _ => by simp))

private theorem seg3b_iter [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl04 b)
    (s : State) (sp : BitVec 64) (inv vPoly : Poly16)
    {r : Nat} (hr : r < 16) (f : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + off3888) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (32 * r))
    (hx9 : s.readReg64 .x9 = 1441#64) (hx10 : s.readReg64 .x10 = 55457#64)
    (hx11 : s.readReg64 .x11 = sp + 19168#64) (hx20 : s.readReg64 .x20 = sp + 11856#64)
    (hv5 : s.readVReg128 5#5 = dup8x16 3329#16) (hv6 : s.readVReg128 6#5 = dup8x16 20159#16)
    (hv7 : s.readVReg128 7#5 = dup8x16 1024#16) (hv16 : s.readVReg128 16#5 = dup8x16 62207#16)
    (hhi0 : f (2 * r) = polyVecNat inv (2 * r))
    (hhi1 : f (2 * r + 1) = polyVecNat inv (2 * r + 1)) :
    SepWP (blkPC04.rebase b (fun _ => none))
      (if r < 15 then b + off3888 else b + off3908) s
      (PolyMem (sp + 11856#64) f ∗ PolyMem (sp + 19168#64) (polyVecNat vPoly) ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x8 = BitVec.ofNat 64 (32 * (r + 1)) ∧
        s'.readReg64 .x9 = 1441#64 ∧ s'.readReg64 .x10 = 55457#64 ∧
        s'.readReg64 .x11 = sp + 19168#64 ∧ s'.readReg64 .x20 = sp + 11856#64 ∧
        s'.readReg64 .x23 = s.readReg64 .x23 ∧ s'.readReg64 .x26 = s.readReg64 .x26 ∧
        s'.readReg64 .x28 = s.readReg64 .x28 ∧ s'.readReg64 .fp = s.readReg64 .fp ∧
        s'.readVReg128 5#5 = dup8x16 3329#16 ∧ s'.readVReg128 6#5 = dup8x16 20159#16 ∧
        s'.readVReg128 7#5 = dup8x16 1024#16 ∧ s'.readVReg128 16#5 = dup8x16 62207#16 ∧
        P' = (PolyMem (sp + 11856#64)
          (Function.update
            (Function.update f (2 * r) (polyVecNat (seg3SubPoly inv vPoly) (2 * r)))
            (2 * r + 1) (polyVecNat (seg3SubPoly inv vPoly) (2 * r + 1))) ∗
          PolyMem (sp + 19168#64) (polyVecNat vPoly) ∗ Rest)) := by
  have _ : b = blkPl04.base := _hb
  wp_steps 3
  refine step_ldpQ128 (wb := none)
    (ea := (sp + 11856#64) + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := (sp + 11856#64) + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v1 := polyVecNat inv (2 * r)) (v2 := polyVecNat inv (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]; clear * - hr; bv_omega) (by clear * -; bv_omega)
    (hhi0 ▸ SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r) (by omega) rfl))
    (hhi1 ▸ SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r + 1) (by omega) rfl))
    (by wp_norm_lhs) ?_
  wp_steps 15
  refine step_ldpQ128 (wb := none)
    (ea := (sp + 19168#64) + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := (sp + 19168#64) + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v1 := polyVecNat vPoly (2 * r)) (v2 := polyVecNat vPoly (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]; clear * - hr; bv_omega) (by clear * -; bv_omega)
    (SepLoad128.right (SepLoad128.left
      (SepLoad128.vecRange (n := 32) (k := 2 * r) (by omega) rfl)))
    (SepLoad128.right (SepLoad128.left
      (SepLoad128.vecRange (n := 32) (k := 2 * r + 1) (by omega) rfl)))
    (by wp_norm_lhs) ?_
  wp_steps 10
  have hv1_eq := seg3SubLoop_vec_eq inv vPoly (2 * r) (by omega) true
  have hv0_eq := seg3SubLoop_vec_eq inv vPoly (2 * r + 1) (by omega) false
  simp only [↓reduceIte, Bool.false_eq_true] at hv1_eq hv0_eq
  refine step_stpQ128 (wb := none)
    (ea := (sp + 11856#64) + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := (sp + 11856#64) + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v1 := polyVecNat (seg3SubPoly inv vPoly) (2 * r))
    (v2 := polyVecNat (seg3SubPoly inv vPoly) (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]; clear * - hr; bv_omega) (by clear * -; bv_omega)
    (by simp [← hv1_eq])
    (by simp [← hv0_eq])
    (SepStore128.left (SepStore128.vecRange (n := 32) (k := 2 * r) (by omega) rfl))
    (SepStore128.left (SepStore128.vecRange (n := 32) (k := 2 * r + 1) (by omega) rfl))
    (by wp_norm_lhs) ?_
  intro m'
  refine seg3b_branch _hb hr _ _ _ (by wp_norm_lhs) (by simp [hrun])
    (by simp; congr 2; clear * - hr; bv_omega) ?_
  intro s' hsp' hspA' hr' hv'
  refine ⟨by rw [hsp']; simp [hsp], by rw [hspA']; simpa [State.spAligned] using hspA,
    by rw [hr']; simp; clear * - hr; bv_omega,
    by rw [hr']; simp [hx9], by rw [hr']; simp [hx10],
    by rw [hr']; simp [hx11], by rw [hr']; simp [hx20],
    by rw [hr']; simp, by rw [hr']; simp, by rw [hr']; simp, by rw [hr']; simp,
    by rw [hv']; simp [hv5], by rw [hv']; simp [hv6],
    by rw [hv']; simp [hv7], by rw [hv']; simp [hv16], rfl⟩

private theorem seg3b_loop [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl04 b)
    (sp x23v x26v x28v fpv : BitVec 64) (inv vPoly : Poly16) (Rest : SepProp) :
    ∀ rem r, rem + r = 15 →
    ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + off3888 → s.status = .Running →
      s.sp = sp → s.spAligned = true →
      mlkemMultiLib.CodeLoaded mlkemMpl s.mem → MlKemRoOk mlkemMpl s.mem →
      s.readReg64 .x8 = BitVec.ofNat 64 (32 * r) →
      s.readReg64 .x9 = 1441#64 → s.readReg64 .x10 = 55457#64 →
      s.readReg64 .x11 = sp + 19168#64 → s.readReg64 .x20 = sp + 11856#64 →
      s.readReg64 .x23 = x23v → s.readReg64 .x26 = x26v →
      s.readReg64 .x28 = x28v → s.readReg64 .fp = fpv →
      s.readVReg128 5#5 = dup8x16 3329#16 → s.readVReg128 6#5 = dup8x16 20159#16 →
      s.readVReg128 7#5 = dup8x16 1024#16 → s.readVReg128 16#5 = dup8x16 62207#16 →
      (∀ j, j < 2 * r → f j = polyVecNat (seg3SubPoly inv vPoly) j) →
      (∀ j, 2 * r ≤ j → j < 32 → f j = polyVecNat inv j) →
      SepWP (blkPC04.rebase b (fun _ => none)) (b + off3908) s
        (PolyMem (sp + 11856#64) f ∗ PolyMem (sp + 19168#64) (polyVecNat vPoly) ∗ Rest)
        (fun s' P' =>
          s'.sp = sp ∧ s'.spAligned = true ∧
          s'.readReg64 .x23 = x23v ∧ s'.readReg64 .x26 = x26v ∧
          s'.readReg64 .x28 = x28v ∧ s'.readReg64 .fp = fpv ∧
          P' = (PolyMem (sp + 11856#64) (polyVecNat (seg3SubPoly inv vPoly)) ∗
            PolyMem (sp + 19168#64) (polyVecNat vPoly) ∗ Rest)) := by
  intro rem; induction rem with
  | zero =>
    intro r hrem s f hpc hrun hsp hspA _hcl _hro hx8 hx9 hx10 hx11 hx20
      hx23 hx26 hx28 hfp hv5 hv6 hv7 hv16 hlo hhi
    have hr15 : r = 15 := by omega
    subst hr15
    have hstep := seg3b_iter hb s sp inv vPoly (r := 15) (by decide) f Rest
      hpc hrun hsp hspA hx8 hx9 hx10 hx11 hx20 hv5 hv6 hv7 hv16
      (hhi 30 (by decide) (by decide)) (hhi 31 (by decide) (by decide))
    simp only [show ¬ (15 < 15) by decide, ↓reduceIte] at hstep
    refine SepWP.mono hstep ?_
    rintro s' P' _ _ ⟨hsp', hspA', _, _, _, _, _, hx23', hx26', hx28', hfp', _, _, _, _, hP'⟩
    refine ⟨hsp', hspA', hx23'.trans hx23, hx26'.trans hx26, hx28'.trans hx28, hfp'.trans hfp, ?_⟩
    rw [hP', polyMem_congr (update2_split (r := 15) hlo hhi).1]
  | succ rem ih =>
    intro r hrem s f hpc hrun hsp hspA hcl hro hx8 hx9 hx10 hx11 hx20
      hx23 hx26 hx28 hfp hv5 hv6 hv7 hv16 hlo hhi
    have hr_lt : r < 15 := by omega
    have hstep := seg3b_iter hb s sp inv vPoly (r := r) (by omega) f Rest
      hpc hrun hsp hspA hx8 hx9 hx10 hx11 hx20 hv5 hv6 hv7 hv16
      (hhi (2 * r) (by omega) (by omega)) (hhi (2 * r + 1) (by omega) (by omega))
    simp only [hr_lt, ↓reduceIte] at hstep
    refine sepWP_seq_env hcl hro hstep ?_
    rintro sm _ hpc' hrun' hcl' hro'
      ⟨hsp', hspA', hx8', hx9', hx10', hx11', hx20', hx23', hx26', hx28', hfp',
        hv5', hv6', hv7', hv16', rfl⟩
    have ⟨hlo', hhi'⟩ := update2_split (r := r) hlo hhi
    exact ih (r + 1) (by omega) sm _ hpc' hrun' hsp' hspA' hcl' hro'
      hx8' hx9' hx10' hx11' hx20' (hx23'.trans hx23) (hx26'.trans hx26)
      (hx28'.trans hx28) (hfp'.trans hfp) hv5' hv6' hv7' hv16' hlo' hhi'

/-! ## 3. Dual `B28(memcpy)` Staging (`+0x3908 → +0x3948`) & Composed `seg3b_ok` -/

private theorem seg3b_memcpy_out [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) (w : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + off3908) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hro : MlKemRoOk mlkemMpl s.mem) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg3bEnd) s
      (PolyMem (sp + 11856#64) (polyVecNat w) ∗ memRegion (sp + 20704#64) 512 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x20 = sp + 20704#64 ∧ sf.readReg64 .x21 = sp + 11856#64 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .fp = s.readReg64 .fp ∧
        (Pf ⊢ PolyMem (sp + 11856#64) (polyVecNat w) ∗
          PolyMem (sp + 20704#64) (polyVecNat w) ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  generalize hbs_def : vecRangeBytes 32 (polyVecNat w) = bsW
  have hbs : bsW.length = 512 := by rw [← hbs_def, vecRangeBytes_length]
  have hp11856 : PolyMem (sp + 11856#64) (polyVecNat w) = ((sp + 11856#64) ↦ₛ bsW) := by
    rw [← hbs_def]; exact vecRangeMem_eq_pointsToBytes 32 _ _
  have hp20704 : ((sp + 20704#64) ↦ₛ bsW) = PolyMem (sp + 20704#64) (polyVecNat w) := by
    rw [← hbs_def]; exact (vecRangeMem_eq_pointsToBytes 32 _ _).symm
  have hstep1 : SepWP (blkPC04.rebase blkPl04.base (fun _ => none)) (blkPl04.base + off3930) s
      (PolyMem (sp + 11856#64) (polyVecNat w) ∗ memRegion (sp + 20704#64) 512 ∗ Rest)
      (fun s1 P1 =>
        s1.sp = sp ∧ s1.spAligned = true ∧
        s1.readReg64 .x20 = sp + 20704#64 ∧ s1.readReg64 .x21 = sp + 11856#64 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧ s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧ s1.readReg64 .fp = s.readReg64 .fp ∧
        P1 = (((sp + 20704#64) ↦ₛ bsW) ∗ ((sp + 11856#64) ↦ₛ bsW) ∗ Rest)) := by
    rw [hp11856]
    wp_steps 9
    wp_call (blk28_memcpy_04 blkPl04.base) (sp + 20704#64, sp + 11856#64, bsW)
    have hsp_s1 : sf.sp = sp := by simp [*]
    exact SepWP.done (by wp_norm_lhs) (by simp [*])
      ⟨hsp_s1, spAligned_of_chk hsp_s1 hsp_chk,
        by simp [*], by simp [*],
        by simp [*], by simp [*], by simp [*], by simp [*],
        sepProp_ext (by sep_frame) (by sep_frame)⟩
  refine sepWP_seq_env hcl hro hstep1 ?_
  rintro s1 _ hpc1 hrun1 hcl1 _ ⟨hsp1, hspA1, hx20_1, hx21_1, hx23_1, hx26_1, hx28_1, hfp1, rfl⟩
  have hm11 : ((sp + 20704#64) ↦ₛ bsW) ∗ ((sp + 11856#64) ↦ₛ bsW) ∗ Rest ⊢
      memRegion (sp + 11856#64) 512 ∗ ((sp + 20704#64) ↦ₛ bsW) ∗ Rest := by
    have hm : ((sp + 11856#64) ↦ₛ bsW) ⊢ memRegion (sp + 11856#64) 512 := by
      rw [← hbs]; exact pointsToBytes_entails_memRegion _ _
    exact entails_sub hm (by sep_frame) (by sep_frame)
  refine SepWP.weaken_pre hm11 ?_
  wp_steps 5
  wp_call (blk28_memcpy_04 blkPl04.base) (sp + 11856#64, sp + 20704#64, bsW)
  rw [← hp11856, hp20704]
  have hsp_sf : sf.sp = sp := by simp [*]
  exact SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨hsp_sf, spAligned_of_chk hsp_sf hsp_chk,
      by simp [*], by simp [*],
      by simp [*], by simp [*], by simp [*], by simp [*],
      by sep_frame⟩

/-- Segment 3b (`+0x3860 → +0x3948`): `memcpy` in + `vPoly - to_std(inv)` + Barrett + dual `memcpy` out. -/
theorem seg3b_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) (tOut : Spill21) (inv vPoly : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offSeg3bStart) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = sp + 11856#64) (hx1 : s.readReg64 .x1 = sp + 20704#64)
    (hx2 : s.readReg64 .x2 = 512#64) (hx20 : s.readReg64 .x20 = sp + 11856#64)
    (hs14 : tOut.s14 = dup8x16 20159#16) (hs19 : tOut.s19 = dup8x16 3329#16)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hro : MlKemRoOk mlkemMpl s.mem) :
    let w := seg3SubPoly inv vPoly
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg3bEnd) s
      (Spill21Mem (sp + 1920#64) tOut ∗ memRegion (sp + 11856#64) 512 ∗
        PolyMem (sp + 19168#64) (polyVecNat vPoly) ∗
        PolyMem (sp + 20704#64) (polyVecNat inv) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x20 = sp + 20704#64 ∧ sf.readReg64 .x21 = sp + 11856#64 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .fp = s.readReg64 .fp ∧
        (Pf ⊢ Spill21Mem (sp + 1920#64) tOut ∗
          PolyMem (sp + 11856#64) (polyVecNat w) ∗
          PolyMem (sp + 19168#64) (polyVecNat vPoly) ∗
          PolyMem (sp + 20704#64) (polyVecNat w) ∗ Rest)) := by
  intro w
  set R1 := Spill21Mem (sp + 1920#64) tOut ∗ PolyMem (sp + 19168#64) (polyVecNat vPoly) ∗ Rest
  have hpre1 : Spill21Mem (sp + 1920#64) tOut ∗ memRegion (sp + 11856#64) 512 ∗
      PolyMem (sp + 19168#64) (polyVecNat vPoly) ∗ PolyMem (sp + 20704#64) (polyVecNat inv) ∗ Rest ⊢
      memRegion (sp + 11856#64) 512 ∗ PolyMem (sp + 20704#64) (polyVecNat inv) ∗ R1 := by
    dsimp only [R1]; sep_frame
  refine SepWP.weaken_pre hpre1 (sepWP_seq_env hcl hro
    (seg3b_memcpy_in hb hbase s sp inv R1 hpc hrun hsp hspA hx0 hx1 hx2 hx20 hcl) ?_)
  rintro s1 _ hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hx20_1, hx23_1, hx26_1, hx28_1, hfp1, rfl⟩
  set R2 := PolyMem (sp + 11856#64) (polyVecNat inv) ∗ PolyMem (sp + 20704#64) (polyVecNat inv) ∗
    PolyMem (sp + 19168#64) (polyVecNat vPoly) ∗ Rest
  have hpre2 : PolyMem (sp + 11856#64) (polyVecNat inv) ∗
      PolyMem (sp + 20704#64) (polyVecNat inv) ∗ R1 ⊢
      Spill21Mem (sp + 1920#64) tOut ∗ R2 := by dsimp only [R1, R2]; sep_frame
  refine SepWP.weaken_pre hpre2 (sepWP_seq_env hcl1 hro1
    (seg3b_setup hb s1 sp tOut R2 hpc1 hrun1 hsp1 hspA1 hx20_1 hs14 hs19) ?_)
  rintro s2 _ hpc2 hrun2 hcl2 hro2
    ⟨hsp2, hspA2, hx8_2, hx9_2, hx10_2, hx11_2, hx20_2, hx23_2, hx26_2, hx28_2, hfp2,
      hv5_2, hv6_2, hv7_2, hv16_2, rfl⟩
  set R3 := Spill21Mem (sp + 1920#64) tOut ∗ PolyMem (sp + 20704#64) (polyVecNat inv) ∗ Rest
  have hpre3 : Spill21Mem (sp + 1920#64) tOut ∗ R2 ⊢
      PolyMem (sp + 11856#64) (polyVecNat inv) ∗ PolyMem (sp + 19168#64) (polyVecNat vPoly) ∗ R3 := by
    dsimp only [R2, R3]; sep_frame
  refine SepWP.weaken_pre hpre3 (sepWP_seq_env hcl2 hro2
    (seg3b_loop hb sp (s.readReg64 .x23) (s.readReg64 .x26) (s.readReg64 .x28) (s.readReg64 .fp)
      inv vPoly R3 15 0 rfl s2 (polyVecNat inv) hpc2 hrun2 hsp2 hspA2 hcl2 hro2
      (by simpa using hx8_2) hx9_2 hx10_2 hx11_2 hx20_2
      (hx23_2.trans hx23_1) (hx26_2.trans hx26_1) (hx28_2.trans hx28_1) (hfp2.trans hfp1)
      hv5_2 hv6_2 hv7_2 hv16_2 (fun _ hj => by omega) (fun _ _ _ => rfl)) ?_)
  rintro s3 _ hpc3 hrun3 hcl3 hro3 ⟨hsp3, hspA3, hx23_3, hx26_3, hx28_3, hfp3, rfl⟩
  set R4 := Spill21Mem (sp + 1920#64) tOut ∗ PolyMem (sp + 19168#64) (polyVecNat vPoly) ∗ Rest
  have hpre4 : PolyMem (sp + 11856#64) (polyVecNat w) ∗
      PolyMem (sp + 19168#64) (polyVecNat vPoly) ∗ R3 ⊢
      PolyMem (sp + 11856#64) (polyVecNat w) ∗ memRegion (sp + 20704#64) 512 ∗ R4 := by
    dsimp only [R3, R4]
    have hm20 : PolyMem (sp + 20704#64) (polyVecNat inv) ⊢ memRegion (sp + 20704#64) 512 :=
      vecRangeMem_entails_memRegion 32 (sp + 20704#64) (polyVecNat inv)
    exact entails_sub hm20 (by sep_frame) (by sep_frame)
  refine SepWP.weaken_pre hpre4
    (SepWP.mono (seg3b_memcpy_out hb hbase s3 sp w R4 hpc3 hrun3 hsp3 hspA3 hcl3 hro3) ?_)
  rintro sf Pf _ _ ⟨hsp_f, hspA_f, hx20_f, hx21_f, hx23_f, hx26_f, hx28_f, hfp_f, hPf⟩
  refine ⟨hsp_f, hspA_f, hx20_f, hx21_f,
    hx23_f.trans hx23_3, hx26_f.trans hx26_3, hx28_f.trans hx28_3, hfp_f.trans hfp3,
    Entails.trans hPf ?_⟩
  dsimp only [R4]; sep_frame

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3b
