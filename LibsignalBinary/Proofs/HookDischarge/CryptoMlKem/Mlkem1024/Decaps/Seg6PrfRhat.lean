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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6CbdPure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6RhatNtt -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6RhatSym1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6Cbd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6Prf
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6E1Prf
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6E1Loop
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6E2

/-!
# `kyber_decapsulate` (`B06`) — Segment 6 Full Composition (`+0x76a8 .. +0x9380`)

Composes `seg6_entry_ops`, `seg6_prf_calls`, `seg6_copy_and_zetas`, the 4-iteration `rHat[0..3]`
loop (`seg6_rhat_loop_ok`), `e1[0..3]` (`Seg6E1Prf` + `Seg6E1Loop`), and `e2` + `uVec[0..3]`
zeroing (`Seg6E2`) into `seg6_ok` (`+0x76a8 → +0x9380`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6PrfRhat
open Arm64 Arm64.Obj ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (shake256List)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd (neonCbd2Poly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  PolyMem polyVecNat vecRangeMem_entails_memRegion)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (entails_sub)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base (blkPC06 blkPl06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs (
  Spill40 SpillSliceMem evalSExpr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6RhatSym1a (
  symSeg6FwdInit)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6CbdPure (
  PublicKeyStateAt shake256List_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6Cbd (
  off76a8 off7718 offRhatCbdStart seg6_entry_ops)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6Prf (
  off7868 ro00Sym seg6_copy_and_zetas seg6_prf_calls)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6RhatNtt (
  offSeg6RhatEnd rHatPoly16 seg6_rhat_iter)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6E1Prf (
  seg6_e1_copy_prf seg6_e1_prf_calls seg6_memset_e1)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6E1Loop (seg6_e1_loop_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6E2 (seg6_e2_ok)

/-- Segment 7 entry byte offset (`+0x9380`). -/
@[simp, arm64_norm, wp_norm] abbrev offSeg7Start : BitVec 64 := BitVec.ofNat 64 37760

private theorem split_1488_304 (sp : BitVec 64) :
    memRegion (sp + 1488#64) 944 = memRegion (sp + 1488#64) 304 ∗ memRegion (sp + 1792#64) 640 :=
  memRegion_split' (b := sp + 1488#64) (b' := sp + 1792#64) (n := 304) (k := (640 : Nat))
    rfl (by bv_omega) (by decide)

private theorem split_1488_512 (sp : BitVec 64) :
    memRegion (sp + 1488#64) 944 = memRegion (sp + 1488#64) 512 ∗ memRegion (sp + 2000#64) 432 :=
  memRegion_split' (b := sp + 1488#64) (b' := sp + 2000#64) (n := 512) (k := (432 : Nat))
    rfl (by bv_omega) (by decide)

private theorem split_14432_512 (sp : BitVec 64) :
    memRegion (sp + 14432#64) 10272 =
      memRegion (sp + 14432#64) 512 ∗ memRegion (sp + 14944#64) 9760 :=
  memRegion_split' (b := sp + 14432#64) (b' := sp + 14944#64) (n := 512) (k := (9760 : Nat))
    rfl (by bv_omega) (by decide)

private theorem split_14432_128 (sp : BitVec 64) :
    memRegion (sp + 14432#64) 512 = memRegion (sp + 14432#64) 128 ∗ memRegion (sp + 14560#64) 384 :=
  memRegion_split' (b := sp + 14432#64) (b' := sp + 14560#64) (n := 128) (k := (384 : Nat))
    rfl (by bv_omega) (by decide)

private theorem split_28368_132 (sp : BitVec 64) :
    memRegion (sp + 28368#64) 2048 =
      memRegion (sp + 28368#64) 132 ∗ memRegion (sp + 28500#64) 1916 :=
  memRegion_split' (b := sp + 28368#64) (b' := sp + 28500#64) (n := 132) (k := (1916 : Nat))
    rfl (by bv_omega) (by decide)

private theorem split_30448_32 (sp : BitVec 64) :
    memRegion (sp + 30448#64) 512 = memRegion (sp + 30448#64) 32 ∗ memRegion (sp + 30480#64) 480 :=
  memRegion_split' (b := sp + 30448#64) (b' := sp + 30480#64) (n := 32) (k := (480 : Nat))
    rfl (by bv_omega) (by decide)

private theorem split_30448_512 (sp : BitVec 64) :
    memRegion (sp + 30448#64) 2048 =
      memRegion (sp + 30448#64) 512 ∗ memRegion (sp + 30960#64) 1536 :=
  memRegion_split' (b := sp + 30448#64) (b' := sp + 30960#64) (n := 512) (k := (1536 : Nat))
    rfl (by bv_omega) (by decide)

private theorem split_33008_32 (sp : BitVec 64) :
    memRegion (sp + 33008#64) 132 = memRegion (sp + 33008#64) 32 ∗ memRegion (sp + 33040#64) 100 :=
  memRegion_split' (b := sp + 33008#64) (b' := sp + 33040#64) (n := 32) (k := (100 : Nat))
    rfl (by bv_omega) (by decide)

private theorem split_33008_128 (sp : BitVec 64) :
    memRegion (sp + 33008#64) 132 = memRegion (sp + 33008#64) 128 ∗ memRegion (sp + 33136#64) 4 :=
  memRegion_split' (b := sp + 33008#64) (b' := sp + 33136#64) (n := 128) (k := (4 : Nat))
    rfl (by bv_omega) (by decide)

private theorem spill40_entails_memRegion640 (sp : BitVec 64) (t : Spill40) :
    SpillSliceMem 40 (sp + 1792#64) t ⊢ memRegion (sp + 1792#64) 640 := by
  dsimp only [SpillSliceMem]
  exact vecRangeMem_entails_memRegion 40 (sp + 1792#64) (fun i => t.get i)

attribute [local irreducible] blkPC06 shake256List neonCbd2Poly16 polyVecNat PublicKeyStateAt

/-! ## 1. Four-Iteration `rHat[0..3]` Loop (`+0x7ad4 → +0x8bd8`) -/

private theorem ha_26832 (sp : BitVec 64) :
    sp + 26320#64 + BitVec.ofNat 64 512 = sp + 26832#64 := by bv_omega
private theorem ha_27344 (sp : BitVec 64) :
    sp + 26320#64 + BitVec.ofNat 64 (512 * 2) = sp + 27344#64 := by bv_omega
private theorem ha_27856 (sp : BitVec 64) :
    sp + 26320#64 + BitVec.ofNat 64 (512 * 3) = sp + 27856#64 := by bv_omega

private theorem prf4_entails_memRegion512 (sp : BitVec 64)
    {p0 p1 p2 p3 : List (BitVec 8)}
    (h0 : p0.length = 128) (h1 : p1.length = 128) (h2 : p2.length = 128) (h3 : p3.length = 128) :
    ((sp + 30448#64) ↦ₛ p0) ∗ ((sp + 30576#64) ↦ₛ p1) ∗
    ((sp + 30704#64) ↦ₛ p2) ∗ ((sp + 30832#64) ↦ₛ p3) ⊢ memRegion (sp + 30448#64) 512 := by
  rw [memRegion_split' (b' := sp + 30576#64) (n := 128) (k := (384 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp + 30704#64) (n := 128) (k := (256 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp + 30832#64) (n := 128) (k := (128 : Nat)) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (by simpa [h0] using pointsToBytes_entails_memRegion (sp + 30448#64) p0)
    (sepConj_mono (by simpa [h1] using pointsToBytes_entails_memRegion (sp + 30576#64) p1)
      (sepConj_mono (by simpa [h2] using pointsToBytes_entails_memRegion (sp + 30704#64) p2)
        (by simpa [h3] using pointsToBytes_entails_memRegion (sp + 30832#64) p3)))

attribute [local irreducible] PolyMem SpillSliceMem

set_option maxHeartbeats 1200000 in
private theorem seg6_rhat_loop_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp : BitVec 64)
    (prf0 prf1 prf2 prf3 : List (BitVec 8))
    (t0 : Spill40) (ht0 : ∀ env i, i < 24 → t0.get i = evalSExpr env (symSeg6FwdInit.spill.get i))
    (fDst0 fDst1 fDst2 fDst3 : Nat → BitVec 128) (Rest : SepProp)
    (h0 : prf0.length = 128) (h1 : prf1.length = 128)
    (h2 : prf2.length = 128) (h3 : prf3.length = 128)
    (hpc : s.pc = b + offRhatCbdStart) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx0 : s.readReg64 .x0 = mlkemMpl.ρ ro00Sym + 66#64) (hx1 : s.readReg64 .x1 = 0xf301#64)
    (hx2 : s.readReg64 .x2 = mlkemMpl.ρ ro00Sym + 134#64) (hx3 : s.readReg64 .x3 = 0x4ebf#64)
    (hx5 : s.readReg64 .x5 = 0#64) (hx7 : s.readReg64 .x7 = sp + 30449#64)
    (hx9 : s.readReg64 .x9 = sp + 26336#64) (hx10 : s.readReg64 .x10 = 16#64)
    (hx12 : s.readReg64 .x12 = 0xf9fa#64) (hx13 : s.readReg64 .x13 = 0x47fa#64)
    (hx14 : s.readReg64 .x14 = 0x019b#64) (hx15 : s.readReg64 .x15 = 0x229b#64)
    (hx16 : s.readReg64 .x16 = 0x6833#64) (hx17 : s.readReg64 .x17 = 0xf9dd#64)
    (hx18 : s.readReg64 .x18 = 0xc0dd#64) (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx21 : s.readReg64 .x21 = sp + 14432#64) (hx22 : s.readReg64 .x22 = sp + 26320#64)
    (hv3 : s.readVReg128 3#5 = dup8x16 0x0d01#16) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + offSeg6RhatEnd) s
      (((sp + 30448#64) ↦ₛ prf0) ∗ ((sp + 30576#64) ↦ₛ prf1) ∗
       ((sp + 30704#64) ↦ₛ prf2) ∗ ((sp + 30832#64) ↦ₛ prf3) ∗
       memRegion (sp + 14432#64) 512 ∗ SpillSliceMem 40 (sp + 1792#64) t0 ∗
       PolyMem (sp + 26320#64) fDst0 ∗ PolyMem (sp + 26832#64) fDst1 ∗
       PolyMem (sp + 27344#64) fDst2 ∗ PolyMem (sp + 27856#64) fDst3 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x19 = 0x55555555#64 ∧
        sf.readReg64 .x21 = sp + 14432#64 ∧
        sf.readReg64 .x22 = sp + 26320#64 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        (Pf ⊢ memRegion (sp + 30448#64) 512 ∗
          memRegion (sp + 14432#64) 512 ∗ memRegion (sp + 1792#64) 640 ∗
          PolyMem (sp + 26320#64) (polyVecNat (rHatPoly16 prf0)) ∗
          PolyMem (sp + 26832#64) (polyVecNat (rHatPoly16 prf1)) ∗
          PolyMem (sp + 27344#64) (polyVecNat (rHatPoly16 prf2)) ∗
          PolyMem (sp + 27856#64) (polyVecNat (rHatPoly16 prf3)) ∗ Rest)) := by
  have hP0' : (((sp + 30448#64) ↦ₛ prf0) ∗ ((sp + 30576#64) ↦ₛ prf1) ∗
      ((sp + 30704#64) ↦ₛ prf2) ∗ ((sp + 30832#64) ↦ₛ prf3) ∗
      memRegion (sp + 14432#64) 512 ∗ SpillSliceMem 40 (sp + 1792#64) t0 ∗
      PolyMem (sp + 26320#64) fDst0 ∗ PolyMem (sp + 26832#64) fDst1 ∗
      PolyMem (sp + 27344#64) fDst2 ∗ PolyMem (sp + 27856#64) fDst3 ∗ Rest) ⊢
      ((sp + BitVec.ofNat 64 (30448 + 128 * 0)) ↦ₛ prf0) ∗ memRegion (sp + 14432#64) 512 ∗
      SpillSliceMem 40 (sp + 1792#64) t0 ∗
      PolyMem (sp + 26320#64 + BitVec.ofNat 64 (512 * 0)) fDst0 ∗
      (((sp + 30576#64) ↦ₛ prf1) ∗ ((sp + 30704#64) ↦ₛ prf2) ∗ ((sp + 30832#64) ↦ₛ prf3) ∗
        PolyMem (sp + 26832#64) fDst1 ∗ PolyMem (sp + 27344#64) fDst2 ∗
        PolyMem (sp + 27856#64) fDst3 ∗ Rest) := by
    simp only [Nat.mul_zero, Nat.add_zero, BitVec.add_zero]; sep_frame
  refine SepWP.weaken_pre hP0'
    (sepWP_seq_env hcl hro
      (seg6_rhat_iter hb hbase s sp (idx := 0) (by decide) prf0 h0 t0 ht0 fDst0 _
        hpc hrun hsp hspA hcl hro hx0 hx1 hx2 hx3 hx5 (by simpa using hx7)
        (by simpa using hx9) (by simpa using hx10)
        hx12 hx13 hx14 hx15 hx16 hx17 hx18 hx19 hx21 hx22 hv3) ?_)
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, r0_1, r1_1, r2_1, r3_1, r5_1, r7_1, r9_1, r10_1, r12_1, r13_1,
      r14_1, r15_1, r16_1, r17_1, r18_1, r19_1, r21_1, r22_1, rfp_1, rv3_1, _, _, t1, ht1, hP1⟩
  simp only [show (0 : Nat) < 3 by decide, ↓reduceIte] at hpc1
  have hP1' : P1 ⊢ ((sp + BitVec.ofNat 64 (30448 + 128 * 1)) ↦ₛ prf1) ∗
      memRegion (sp + 14432#64) 512 ∗ SpillSliceMem 40 (sp + 1792#64) t1 ∗
      PolyMem (sp + 26320#64 + BitVec.ofNat 64 (512 * 1)) fDst1 ∗
      (((sp + 30448#64) ↦ₛ prf0) ∗ ((sp + 30704#64) ↦ₛ prf2) ∗ ((sp + 30832#64) ↦ₛ prf3) ∗
        PolyMem (sp + 26320#64) (polyVecNat (rHatPoly16 prf0)) ∗
        PolyMem (sp + 27344#64) fDst2 ∗ PolyMem (sp + 27856#64) fDst3 ∗ Rest) := by
    refine Entails.trans hP1 ?_
    simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero, BitVec.add_zero, ha_26832]; sep_frame
  refine SepWP.weaken_pre hP1'
    (sepWP_seq_env hcl1 hro1
      (seg6_rhat_iter hb hbase s1 sp (idx := 1) (by decide) prf1 h1 t1 ht1 fDst1 _
        hpc1 hrun1 hsp1 hspA1 hcl1 hro1 r0_1 r1_1 r2_1 r3_1 r5_1 r7_1 r9_1 r10_1
        r12_1 r13_1 r14_1 r15_1 r16_1 r17_1 r18_1 r19_1 r21_1 r22_1 rv3_1) ?_)
  rintro s2 P2 hpc2 hrun2 hcl2 hro2
    ⟨hsp2, hspA2, r0_2, r1_2, r2_2, r3_2, r5_2, r7_2, r9_2, r10_2, r12_2, r13_2,
      r14_2, r15_2, r16_2, r17_2, r18_2, r19_2, r21_2, r22_2, rfp_2, rv3_2, _, _, t2, ht2, hP2⟩
  simp only [show (1 : Nat) < 3 by decide, ↓reduceIte] at hpc2
  have hP2' : P2 ⊢ ((sp + BitVec.ofNat 64 (30448 + 128 * 2)) ↦ₛ prf2) ∗
      memRegion (sp + 14432#64) 512 ∗ SpillSliceMem 40 (sp + 1792#64) t2 ∗
      PolyMem (sp + 26320#64 + BitVec.ofNat 64 (512 * 2)) fDst2 ∗
      (((sp + 30448#64) ↦ₛ prf0) ∗ ((sp + 30576#64) ↦ₛ prf1) ∗ ((sp + 30832#64) ↦ₛ prf3) ∗
        PolyMem (sp + 26320#64) (polyVecNat (rHatPoly16 prf0)) ∗
        PolyMem (sp + 26832#64) (polyVecNat (rHatPoly16 prf1)) ∗
        PolyMem (sp + 27856#64) fDst3 ∗ Rest) := by
    refine Entails.trans hP2 ?_
    simp only [Nat.mul_one, ha_26832, ha_27344]; sep_frame
  refine SepWP.weaken_pre hP2'
    (sepWP_seq_env hcl2 hro2
      (seg6_rhat_iter hb hbase s2 sp (idx := 2) (by decide) prf2 h2 t2 ht2 fDst2 _
        hpc2 hrun2 hsp2 hspA2 hcl2 hro2 r0_2 r1_2 r2_2 r3_2 r5_2 r7_2 r9_2 r10_2
        r12_2 r13_2 r14_2 r15_2 r16_2 r17_2 r18_2 r19_2 r21_2 r22_2 rv3_2) ?_)
  rintro s3 P3 hpc3 hrun3 hcl3 hro3
    ⟨hsp3, hspA3, r0_3, r1_3, r2_3, r3_3, r5_3, r7_3, r9_3, r10_3, r12_3, r13_3,
      r14_3, r15_3, r16_3, r17_3, r18_3, r19_3, r21_3, r22_3, rfp_3, rv3_3, _, _, t3, ht3, hP3⟩
  simp only [show (2 : Nat) < 3 by decide, ↓reduceIte] at hpc3
  have hP3' : P3 ⊢ ((sp + BitVec.ofNat 64 (30448 + 128 * 3)) ↦ₛ prf3) ∗
      memRegion (sp + 14432#64) 512 ∗ SpillSliceMem 40 (sp + 1792#64) t3 ∗
      PolyMem (sp + 26320#64 + BitVec.ofNat 64 (512 * 3)) fDst3 ∗
      (((sp + 30448#64) ↦ₛ prf0) ∗ ((sp + 30576#64) ↦ₛ prf1) ∗ ((sp + 30704#64) ↦ₛ prf2) ∗
        PolyMem (sp + 26320#64) (polyVecNat (rHatPoly16 prf0)) ∗
        PolyMem (sp + 26832#64) (polyVecNat (rHatPoly16 prf1)) ∗
        PolyMem (sp + 27344#64) (polyVecNat (rHatPoly16 prf2)) ∗ Rest) := by
    refine Entails.trans hP3 ?_
    simp only [ha_27344, ha_27856]; sep_frame
  refine SepWP.weaken_pre hP3'
    (sepWP_seq_env hcl3 hro3
      (seg6_rhat_iter hb hbase s3 sp (idx := 3) (by decide) prf3 h3 t3 ht3 fDst3 _
        hpc3 hrun3 hsp3 hspA3 hcl3 hro3 r0_3 r1_3 r2_3 r3_3 r5_3 r7_3 r9_3 r10_3
        r12_3 r13_3 r14_3 r15_3 r16_3 r17_3 r18_3 r19_3 r21_3 r22_3 rv3_3) ?_)
  rintro sf Pf hpcf hrunf hclf hrof
    ⟨hspf, hspAf, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      r19_f, r21_f, r22_f, rfp_f, _, _, _, t4, _, hPf⟩
  simp only [Nat.lt_irrefl, ↓reduceIte] at hpcf
  have hsp640 := spill40_entails_memRegion640 sp t4
  refine SepWP.done hpcf hrunf
    ⟨hspf, hspAf, r19_f, r21_f, r22_f, rfp_f.trans (rfp_3.trans (rfp_2.trans rfp_1)), hclf, hrof, ?_⟩
  refine Entails.trans hPf ?_
  simp only [ha_27856, show sp + BitVec.ofNat 64 (30448 + 128 * 3) = sp + 30832#64 by bv_omega]
  exact entails_sub hsp640 (by sep_frame)
    (entails_sub (prf4_entails_memRegion512 sp h0 h1 h2 h3) (by sep_frame) (by sep_frame))

/-! ## 2. `Seg6` First Half: Entry + `rHat[0..3]` (`+0x76a8 → +0x8bd8`) -/

set_option maxHeartbeats 1200000 in
private theorem seg6_rhat_part [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp : BitVec 64) (pk hashed : List (BitVec 8)) (Rest : SepProp)
    (hh : hashed.length = 64)
    (hpc : s.pc = b + off76a8) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx25 : s.readReg64 .x25 = sp + 28368#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem) :
    let coins := hashed.drop 32
    let prf0 := shake256List 128 (coins ++ [0#8])
    let prf1 := shake256List 128 (coins ++ [1#8])
    let prf2 := shake256List 128 (coins ++ [2#8])
    let prf3 := shake256List 128 (coins ++ [3#8])
    SepWP (blkPC06.rebase b (fun _ => none)) (b + offSeg6RhatEnd) s
      (((sp + 2496#64) ↦ₛ hashed) ∗ memRegion (sp + 1792#64) 640 ∗
       memRegion (sp + 4160#64) 10272 ∗ PublicKeyStateAt (sp + 14432#64) pk ∗
       memRegion (sp + 24704#64) 1568 ∗ memRegion (sp + 26272#64) 33 ∗
       memRegion (sp + 26320#64) 2048 ∗ memRegion (sp + 28368#64) 132 ∗
       memRegion (sp + 30448#64) 512 ∗ memRegion (sp + 33008#64) 128 ∗
       memRegion (sp + 33536#64) 128 ∗ memRegion (sp + 33888#64) 128 ∗
       stackAt sp 1136 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x19 = 0x55555555#64 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        (Pf ⊢ ((sp + 2496#64) ↦ₛ hashed) ∗ memRegion (sp + 1792#64) 640 ∗
          PublicKeyStateAt (sp + 4160#64) pk ∗ memRegion (sp + 14432#64) 10272 ∗
          memRegion (sp + 24704#64) 1568 ∗ ((sp + 26272#64) ↦ₛ coins) ∗
          ((sp + 26304#64) ↦₈ 0#8) ∗
          PolyMem (sp + 26320#64) (polyVecNat (rHatPoly16 prf0)) ∗
          PolyMem (sp + 26832#64) (polyVecNat (rHatPoly16 prf1)) ∗
          PolyMem (sp + 27344#64) (polyVecNat (rHatPoly16 prf2)) ∗
          PolyMem (sp + 27856#64) (polyVecNat (rHatPoly16 prf3)) ∗
          memRegion (sp + 28368#64) 132 ∗ memRegion (sp + 30448#64) 512 ∗
          memRegion (sp + 33008#64) 128 ∗ memRegion (sp + 33536#64) 128 ∗
          memRegion (sp + 33888#64) 128 ∗ stackAt sp 1136 ∗ Rest)) := by
  intro coins prf0 prf1 prf2 prf3
  have hc : coins.length = 32 := by simp [coins, hh]
  have h0 : prf0.length = 128 := shake256List_length 128 _
  have h1 : prf1.length = 128 := shake256List_length 128 _
  have h2 : prf2.length = 128 := shake256List_length 128 _
  have h3 : prf3.length = 128 := shake256List_length 128 _
  refine SepWP.weaken_pre
    (P' := ((sp + 2496#64) ↦ₛ hashed) ∗ memRegion (sp + 4160#64) 10272 ∗
      PublicKeyStateAt (sp + 14432#64) pk ∗ memRegion (sp + 24704#64) 1568 ∗
      memRegion (sp + 26272#64) 33 ∗ memRegion (sp + 26320#64) 2048 ∗ stackAt sp 1136 ∗
      (memRegion (sp + 1792#64) 640 ∗ memRegion (sp + 28368#64) 132 ∗
        memRegion (sp + 30448#64) 512 ∗ memRegion (sp + 33008#64) 128 ∗
        memRegion (sp + 33536#64) 128 ∗ memRegion (sp + 33888#64) 128 ∗ Rest)) (by sep_frame) ?_
  refine sepWP_seq_env hcl hro (seg6_entry_ops hb hbase s sp pk hashed _ hh hpc hrun hsp hspA hcl) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hx19_1, hx21_1, hx22_1, hx25_1, hfp1, hP1⟩
  refine SepWP.weaken_pre hP1 ?_
  rw [split_14432_512 sp, split_14432_128 sp, split_30448_32 sp]
  refine SepWP.weaken_pre
    (P' := ((sp + 26272#64) ↦ₛ coins) ∗ memRegion (sp + 14432#64) 128 ∗
      memRegion (sp + 28368#64) 132 ∗ memRegion (sp + 30448#64) 32 ∗
      memRegion (sp + 33008#64) 128 ∗ memRegion (sp + 33536#64) 128 ∗
      memRegion (sp + 33888#64) 128 ∗ stackAt sp 1136 ∗
      (((sp + 2496#64) ↦ₛ hashed) ∗ memRegion (sp + 1792#64) 640 ∗
        PublicKeyStateAt (sp + 4160#64) pk ∗ memRegion (sp + 14560#64) 384 ∗
        memRegion (sp + 14944#64) 9760 ∗ memRegion (sp + 24704#64) 1568 ∗
        ((sp + 26304#64) ↦₈ 0#8) ∗
        PolyMem (sp + 26320#64) (fun _ => 0#128) ∗ PolyMem (sp + 26832#64) (fun _ => 0#128) ∗
        PolyMem (sp + 27344#64) (fun _ => 0#128) ∗ PolyMem (sp + 27856#64) (fun _ => 0#128) ∗
        memRegion (sp + 30480#64) 480 ∗ Rest)) (by sep_frame) ?_
  refine sepWP_seq_env hcl1 hro1
    (seg6_prf_calls hb hbase s1 sp coins _ hc hpc1 hrun1 hsp1 hspA1
      hx19_1 hx21_1 hx22_1 (hx25_1.trans hx25) hcl1 hro1) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2
    ⟨hsp2, hspA2, hx19_2, hx20_2, hx21_2, hx22_2, hx25_2, hfp2, hP2⟩
  refine SepWP.weaken_pre hP2 ?_
  have hm30_512 := (split_30448_32 sp).symm
  refine SepWP.weaken_pre
    (P' := ((sp + 33536#64) ↦ₛ prf0) ∗ ((sp + 33888#64) ↦ₛ prf1) ∗
      ((sp + 33008#64) ↦ₛ prf2) ∗ ((sp + 14432#64) ↦ₛ prf3) ∗
      memRegion (sp + 30448#64) 512 ∗ memRegion (sp + 1792#64) 640 ∗
      (((sp + 2496#64) ↦ₛ hashed) ∗ PublicKeyStateAt (sp + 4160#64) pk ∗
        memRegion (sp + 14560#64) 384 ∗ memRegion (sp + 14944#64) 9760 ∗
        memRegion (sp + 24704#64) 1568 ∗ ((sp + 26272#64) ↦ₛ coins) ∗
        ((sp + 26304#64) ↦₈ 0#8) ∗
        PolyMem (sp + 26320#64) (fun _ => 0#128) ∗ PolyMem (sp + 26832#64) (fun _ => 0#128) ∗
        PolyMem (sp + 27344#64) (fun _ => 0#128) ∗ PolyMem (sp + 27856#64) (fun _ => 0#128) ∗
        memRegion (sp + 28368#64) 132 ∗ stackAt sp 1136 ∗ Rest))
    (entails_sub (Entails.of_eq hm30_512) (by sep_frame) (by sep_frame)) ?_
  refine sepWP_seq_env hcl2 hro2
    (seg6_copy_and_zetas hb hbase s2 sp prf0 prf1 prf2 prf3 _ h0 h1 h2 h3
      hpc2 hrun2 hsp2 hspA2 hx19_2 hx20_2 hx21_2 hx22_2 hx25_2) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 hro3
    ⟨hsp3, hspA3, r0, r1, r2, r3, r5, r7, r9, r10, r12, r13, r14, r15, r16, r17, r18,
      r19, _, r21, r22, _, hfp3, rv3, t0, ht0, hP3⟩
  refine SepWP.weaken_pre hP3 ?_
  have hm14_512 := (split_14432_128 sp).symm
  refine SepWP.weaken_pre
    (P' := ((sp + 30448#64) ↦ₛ prf0) ∗ ((sp + 30576#64) ↦ₛ prf1) ∗
      ((sp + 30704#64) ↦ₛ prf2) ∗ ((sp + 30832#64) ↦ₛ prf3) ∗
      memRegion (sp + 14432#64) 512 ∗ SpillSliceMem 40 (sp + 1792#64) t0 ∗
      PolyMem (sp + 26320#64) (fun _ => 0#128) ∗ PolyMem (sp + 26832#64) (fun _ => 0#128) ∗
      PolyMem (sp + 27344#64) (fun _ => 0#128) ∗ PolyMem (sp + 27856#64) (fun _ => 0#128) ∗
      (((sp + 2496#64) ↦ₛ hashed) ∗ PublicKeyStateAt (sp + 4160#64) pk ∗
        memRegion (sp + 14944#64) 9760 ∗ memRegion (sp + 24704#64) 1568 ∗
        ((sp + 26272#64) ↦ₛ coins) ∗ ((sp + 26304#64) ↦₈ 0#8) ∗
        memRegion (sp + 28368#64) 132 ∗ memRegion (sp + 33008#64) 128 ∗
        memRegion (sp + 33536#64) 128 ∗ memRegion (sp + 33888#64) 128 ∗ stackAt sp 1136 ∗ Rest))
    (entails_sub (Entails.of_eq hm14_512) (by sep_frame) (by sep_frame)) ?_
  refine sepWP_seq_env hcl3 hro3
    (seg6_rhat_loop_ok hb hbase s3 sp prf0 prf1 prf2 prf3 t0 ht0 _ _ _ _ _
      h0 h1 h2 h3 hpc3 hrun3 hsp3 hspA3 hcl3 hro3 r0 r1 r2 r3 r5 r7 r9 r10
      r12 r13 r14 r15 r16 r17 r18 r19 r21 r22 rv3) ?_
  rintro sf Pf hpcf hrunf hclf hrof ⟨hspf, hspAf, hx19f, _, _, hfpf, _, _, hPf⟩
  have hm14_10272 := (split_14432_512 sp).symm
  exact SepWP.done hpcf hrunf
    ⟨hspf, hspAf, hx19f, hfpf.trans (hfp3.trans (hfp2.trans hfp1)), hclf, hrof,
      Entails.trans hPf (entails_sub (Entails.of_eq hm14_10272) (by sep_frame) (by sep_frame))⟩

/-! ## 3. `Seg6` Second Half: `e1[0..3]` + `e2` (`+0x8bd8 → +0x9380`) & Full `seg6_ok` -/

set_option maxHeartbeats 1200000 in
private theorem seg6_e1_e2_part [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp : BitVec 64) (coins : List (BitVec 8)) (b0 : BitVec 8) (Rest : SepProp)
    (hc : coins.length = 32)
    (hpc : s.pc = b + offSeg6RhatEnd) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem) :
    let prf4 := shake256List 128 (coins ++ [4#8])
    let prf5 := shake256List 128 (coins ++ [5#8])
    let prf6 := shake256List 128 (coins ++ [6#8])
    let prf7 := shake256List 128 (coins ++ [7#8])
    let prf8 := shake256List 128 (coins ++ [8#8])
    SepWP (blkPC06.rebase b (fun _ => none)) (b + offSeg7Start) s
      (((sp + 26272#64) ↦ₛ coins) ∗ ((sp + 26304#64) ↦₈ b0) ∗
       memRegion (sp + 1488#64) 512 ∗ memRegion (sp + 14432#64) 512 ∗
       memRegion (sp + 28368#64) 2048 ∗ memRegion (sp + 30448#64) 2048 ∗
       memRegion (sp + 33008#64) 132 ∗ memRegion (sp + 33536#64) 128 ∗
       memRegion (sp + 33888#64) 128 ∗ memRegion (sp + 34464#64) 128 ∗
       stackAt sp 1136 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x20 = sp + 30448#64 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        (Pf ⊢ PolyMem (sp + 1488#64) (polyVecNat (neonCbd2Poly16 prf8)) ∗
          PolyMem (sp + 28368#64) (polyVecNat (neonCbd2Poly16 prf4)) ∗
          PolyMem (sp + 28880#64) (polyVecNat (neonCbd2Poly16 prf5)) ∗
          PolyMem (sp + 29392#64) (polyVecNat (neonCbd2Poly16 prf6)) ∗
          PolyMem (sp + 29904#64) (polyVecNat (neonCbd2Poly16 prf7)) ∗
          PolyMem (sp + 30448#64) (fun _ => 0#128) ∗
          PolyMem (sp + 30960#64) (fun _ => 0#128) ∗
          PolyMem (sp + 31472#64) (fun _ => 0#128) ∗
          PolyMem (sp + 31984#64) (fun _ => 0#128) ∗
          memRegion (sp + 14432#64) 512 ∗ memRegion (sp + 26272#64) 33 ∗
          memRegion (sp + 33008#64) 132 ∗ memRegion (sp + 33536#64) 128 ∗
          memRegion (sp + 33888#64) 128 ∗ memRegion (sp + 34464#64) 128 ∗
          stackAt sp 1136 ∗ Rest)) := by
  intro prf4 prf5 prf6 prf7 prf8
  have h4 : prf4.length = 128 := shake256List_length 128 _
  have h5 : prf5.length = 128 := shake256List_length 128 _
  have h6 : prf6.length = 128 := shake256List_length 128 _
  have h7 : prf7.length = 128 := shake256List_length 128 _
  refine SepWP.weaken_pre
    (P' := memRegion (sp + 28368#64) 2048 ∗ stackAt sp 1136 ∗
      (((sp + 26272#64) ↦ₛ coins) ∗ ((sp + 26304#64) ↦₈ b0) ∗
        memRegion (sp + 1488#64) 512 ∗ memRegion (sp + 14432#64) 512 ∗
        memRegion (sp + 30448#64) 2048 ∗ memRegion (sp + 33008#64) 132 ∗
        memRegion (sp + 33536#64) 128 ∗ memRegion (sp + 33888#64) 128 ∗
        memRegion (sp + 34464#64) 128 ∗ Rest)) (by sep_frame) ?_
  refine sepWP_seq_env hcl hro (seg6_memset_e1 hb hbase s sp _ hpc hrun hsp hspA hx19 hcl) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hx19_1, hx20_1, hfp1, hP1⟩
  refine SepWP.weaken_pre hP1 ?_
  rw [split_14432_128 sp, split_30448_512 sp, split_30448_32 sp]
  refine SepWP.weaken_pre
    (P' := ((sp + 26272#64) ↦ₛ coins) ∗ memRegion (sp + 33008#64) 132 ∗
      memRegion (sp + 30448#64) 32 ∗ memRegion (sp + 14432#64) 128 ∗
      memRegion (sp + 34464#64) 128 ∗ memRegion (sp + 33536#64) 128 ∗
      memRegion (sp + 33888#64) 128 ∗ stackAt sp 1136 ∗
      (((sp + 26304#64) ↦₈ b0) ∗ memRegion (sp + 1488#64) 512 ∗
        memRegion (sp + 14560#64) 384 ∗ memRegion (sp + 30480#64) 480 ∗
        memRegion (sp + 30960#64) 1536 ∗
        PolyMem (sp + 28368#64) (fun _ => 0#128) ∗ PolyMem (sp + 28880#64) (fun _ => 0#128) ∗
        PolyMem (sp + 29392#64) (fun _ => 0#128) ∗ PolyMem (sp + 29904#64) (fun _ => 0#128) ∗
        Rest)) (by sep_frame) ?_
  refine sepWP_seq_env hcl1 hro1
    (seg6_e1_prf_calls hb hbase s1 sp hc _ hpc1 hrun1 hsp1 hspA1 hx19_1 hx20_1 hcl1 hro1) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hx19_2, hx20_2, hx21_2, hx22_2, hfp2, hP2⟩
  refine SepWP.weaken_pre hP2 ?_
  have hm30_512 := (split_30448_32 sp).symm
  refine SepWP.weaken_pre
    (P' := ((sp + 34464#64) ↦ₛ prf4) ∗ ((sp + 33536#64) ↦ₛ prf5) ∗
      ((sp + 33888#64) ↦ₛ prf6) ∗ ((sp + 14432#64) ↦ₛ prf7) ∗
      memRegion (sp + 30448#64) 512 ∗
      (((sp + 26272#64) ↦ₛ coins) ∗ ((sp + 26304#64) ↦₈ b0) ∗
        memRegion (sp + 1488#64) 512 ∗ memRegion (sp + 14560#64) 384 ∗
        memRegion (sp + 30960#64) 1536 ∗ memRegion (sp + 33008#64) 132 ∗
        PolyMem (sp + 28368#64) (fun _ => 0#128) ∗ PolyMem (sp + 28880#64) (fun _ => 0#128) ∗
        PolyMem (sp + 29392#64) (fun _ => 0#128) ∗ PolyMem (sp + 29904#64) (fun _ => 0#128) ∗
        stackAt sp 1136 ∗ Rest))
    (entails_sub (Entails.of_eq hm30_512) (by sep_frame) (by sep_frame)) ?_
  refine sepWP_seq_env hcl2 hro2
    (seg6_e1_copy_prf hb hbase s2 sp h4 h5 h6 h7 _ hpc2 hrun2 hsp2 hspA2
      hx19_2 hx20_2 hx21_2 hx22_2) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 hro3
    ⟨hsp3, hspA3, hx8_3, hx9_3, hx19_3, hx20_3, hx21_3, _, hfp3, hv3_3, hP3⟩
  refine SepWP.weaken_pre hP3 ?_
  have hm14_512 := (split_14432_128 sp).symm
  refine SepWP.weaken_pre
    (P' := ((sp + 30448#64) ↦ₛ prf4) ∗ ((sp + 30576#64) ↦ₛ prf5) ∗
      ((sp + 30704#64) ↦ₛ prf6) ∗ ((sp + 30832#64) ↦ₛ prf7) ∗
      memRegion (sp + 14432#64) 512 ∗
      PolyMem (sp + 28368#64) (fun _ => 0#128) ∗ PolyMem (sp + 28880#64) (fun _ => 0#128) ∗
      PolyMem (sp + 29392#64) (fun _ => 0#128) ∗ PolyMem (sp + 29904#64) (fun _ => 0#128) ∗
      (((sp + 26272#64) ↦ₛ coins) ∗ ((sp + 26304#64) ↦₈ b0) ∗
        memRegion (sp + 1488#64) 512 ∗ memRegion (sp + 30960#64) 1536 ∗
        memRegion (sp + 33008#64) 132 ∗ memRegion (sp + 33536#64) 128 ∗
        memRegion (sp + 33888#64) 128 ∗ memRegion (sp + 34464#64) 128 ∗
        stackAt sp 1136 ∗ Rest))
    (entails_sub (Entails.of_eq hm14_512) (by sep_frame) (by sep_frame)) ?_
  refine sepWP_seq_env hcl3 hro3
    (seg6_e1_loop_ok hb hbase s3 sp coins _ _ _ _ _
      hpc3 hrun3 hsp3 hspA3 hx8_3 hx9_3 hx19_3 hx20_3 hx21_3 hv3_3) ?_
  rintro s4 P4 hpc4 hrun4 hcl4 hro4 ⟨hsp4, hspA4, hx19_4, hfp4, _, hP4⟩
  refine SepWP.weaken_pre hP4 ?_
  have hm30_2048 := (split_30448_512 sp).symm
  rw [split_33008_32 sp]
  refine SepWP.weaken_pre
    (P' := ((sp + 26304#64) ↦₈ b0) ∗ ((sp + 26272#64) ↦ₛ coins) ∗
      memRegion (sp + 1488#64) 512 ∗ memRegion (sp + 14432#64) 512 ∗
      memRegion (sp + 30448#64) 2048 ∗ memRegion (sp + 33008#64) 32 ∗
      memRegion (sp + 34464#64) 128 ∗ stackAt sp 1136 ∗
      (PolyMem (sp + 28368#64) (polyVecNat (neonCbd2Poly16 prf4)) ∗
        PolyMem (sp + 28880#64) (polyVecNat (neonCbd2Poly16 prf5)) ∗
        PolyMem (sp + 29392#64) (polyVecNat (neonCbd2Poly16 prf6)) ∗
        PolyMem (sp + 29904#64) (polyVecNat (neonCbd2Poly16 prf7)) ∗
        memRegion (sp + 33040#64) 100 ∗ memRegion (sp + 33536#64) 128 ∗
        memRegion (sp + 33888#64) 128 ∗ Rest))
    (entails_sub (Entails.of_eq hm30_2048) (by sep_frame) (by sep_frame)) ?_
  refine sepWP_seq_env hcl4 hro4
    (seg6_e2_ok hb hbase s4 sp coins b0 _ hc hpc4 hrun4 hsp4 hspA4 hx19_4 hcl4 hro4) ?_
  rintro sf Pf hpcf hrunf hclf hrof ⟨hspf, hspAf, hx20f, hfpf, _, _, hPf⟩
  have hm33_132 := (split_33008_32 sp).symm
  exact SepWP.done hpcf hrunf
    ⟨hspf, hspAf, hx20f, hfpf.trans (hfp4.trans (hfp3.trans (hfp2.trans hfp1))), hclf, hrof,
      Entails.trans hPf (entails_sub (Entails.of_eq hm33_132) (by sep_frame) (by sep_frame))⟩

set_option maxHeartbeats 1200000 in
theorem seg6_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp : BitVec 64) (pk hashed : List (BitVec 8)) (Rest : SepProp)
    (hh : hashed.length = 64)
    (hpc : s.pc = b + off76a8) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx25 : s.readReg64 .x25 = sp + 28368#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem) :
    let coins := hashed.drop 32
    let prf0 := shake256List 128 (coins ++ [0#8])
    let prf1 := shake256List 128 (coins ++ [1#8])
    let prf2 := shake256List 128 (coins ++ [2#8])
    let prf3 := shake256List 128 (coins ++ [3#8])
    let prf4 := shake256List 128 (coins ++ [4#8])
    let prf5 := shake256List 128 (coins ++ [5#8])
    let prf6 := shake256List 128 (coins ++ [6#8])
    let prf7 := shake256List 128 (coins ++ [7#8])
    let prf8 := shake256List 128 (coins ++ [8#8])
    SepWP (blkPC06.rebase b (fun _ => none)) (b + offSeg7Start) s
      (memRegion (sp + 1488#64) 944 ∗ ((sp + 2496#64) ↦ₛ hashed) ∗
       memRegion (sp + 4160#64) 10272 ∗ PublicKeyStateAt (sp + 14432#64) pk ∗
       memRegion (sp + 24704#64) 1568 ∗ memRegion (sp + 26272#64) 33 ∗
       memRegion (sp + 26320#64) 2048 ∗ memRegion (sp + 28368#64) 2048 ∗
       memRegion (sp + 30448#64) 2048 ∗ memRegion (sp + 33008#64) 132 ∗
       memRegion (sp + 33536#64) 128 ∗ memRegion (sp + 33888#64) 128 ∗
       memRegion (sp + 34464#64) 128 ∗ stackAt sp 1136 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x20 = sp + 30448#64 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        (Pf ⊢ PolyMem (sp + 1488#64) (polyVecNat (neonCbd2Poly16 prf8)) ∗
          memRegion (sp + 2000#64) 432 ∗ ((sp + 2496#64) ↦ₛ hashed) ∗
          PublicKeyStateAt (sp + 4160#64) pk ∗ memRegion (sp + 14432#64) 10272 ∗
          memRegion (sp + 24704#64) 1568 ∗ memRegion (sp + 26272#64) 33 ∗
          PolyMem (sp + 26320#64) (polyVecNat (rHatPoly16 prf0)) ∗
          PolyMem (sp + 26832#64) (polyVecNat (rHatPoly16 prf1)) ∗
          PolyMem (sp + 27344#64) (polyVecNat (rHatPoly16 prf2)) ∗
          PolyMem (sp + 27856#64) (polyVecNat (rHatPoly16 prf3)) ∗
          PolyMem (sp + 28368#64) (polyVecNat (neonCbd2Poly16 prf4)) ∗
          PolyMem (sp + 28880#64) (polyVecNat (neonCbd2Poly16 prf5)) ∗
          PolyMem (sp + 29392#64) (polyVecNat (neonCbd2Poly16 prf6)) ∗
          PolyMem (sp + 29904#64) (polyVecNat (neonCbd2Poly16 prf7)) ∗
          PolyMem (sp + 30448#64) (fun _ => 0#128) ∗
          PolyMem (sp + 30960#64) (fun _ => 0#128) ∗
          PolyMem (sp + 31472#64) (fun _ => 0#128) ∗
          PolyMem (sp + 31984#64) (fun _ => 0#128) ∗
          memRegion (sp + 33008#64) 132 ∗ memRegion (sp + 33536#64) 128 ∗
          memRegion (sp + 33888#64) 128 ∗ memRegion (sp + 34464#64) 128 ∗
          stackAt sp 1136 ∗ Rest)) := by
  intro coins prf0 prf1 prf2 prf3 prf4 prf5 prf6 prf7 prf8
  have hc : coins.length = 32 := by simp [coins, hh]
  rw [split_1488_304 sp, split_28368_132 sp, split_30448_512 sp, split_33008_128 sp]
  refine SepWP.weaken_pre
    (P' := ((sp + 2496#64) ↦ₛ hashed) ∗ memRegion (sp + 1792#64) 640 ∗
      memRegion (sp + 4160#64) 10272 ∗ PublicKeyStateAt (sp + 14432#64) pk ∗
      memRegion (sp + 24704#64) 1568 ∗ memRegion (sp + 26272#64) 33 ∗
      memRegion (sp + 26320#64) 2048 ∗ memRegion (sp + 28368#64) 132 ∗
      memRegion (sp + 30448#64) 512 ∗ memRegion (sp + 33008#64) 128 ∗
      memRegion (sp + 33536#64) 128 ∗ memRegion (sp + 33888#64) 128 ∗ stackAt sp 1136 ∗
      (memRegion (sp + 1488#64) 304 ∗ memRegion (sp + 28500#64) 1916 ∗
        memRegion (sp + 30960#64) 1536 ∗ memRegion (sp + 33136#64) 4 ∗
        memRegion (sp + 34464#64) 128 ∗ Rest)) (by sep_frame) ?_
  refine sepWP_seq_env hcl hro
    (seg6_rhat_part hb hbase s sp pk hashed _ hh hpc hrun hsp hspA hx25 hcl hro) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hx19_1, hfp1, _, _, hP1⟩
  refine SepWP.weaken_pre hP1 ?_
  have hm1488_944 : memRegion (sp + 1488#64) 304 ∗ memRegion (sp + 1792#64) 640 =
      memRegion (sp + 1488#64) 512 ∗ memRegion (sp + 2000#64) 432 :=
    (split_1488_304 sp).symm.trans (split_1488_512 sp)
  have hm28_2048 := (split_28368_132 sp).symm
  have hm30_2048 := (split_30448_512 sp).symm
  have hm33_132 := (split_33008_128 sp).symm
  rw [split_14432_512 sp]
  refine SepWP.weaken_pre
    (P' := ((sp + 26272#64) ↦ₛ coins) ∗ ((sp + 26304#64) ↦₈ 0#8) ∗
      memRegion (sp + 1488#64) 512 ∗ memRegion (sp + 14432#64) 512 ∗
      memRegion (sp + 28368#64) 2048 ∗ memRegion (sp + 30448#64) 2048 ∗
      memRegion (sp + 33008#64) 132 ∗ memRegion (sp + 33536#64) 128 ∗
      memRegion (sp + 33888#64) 128 ∗ memRegion (sp + 34464#64) 128 ∗ stackAt sp 1136 ∗
      (memRegion (sp + 2000#64) 432 ∗ ((sp + 2496#64) ↦ₛ hashed) ∗
        PublicKeyStateAt (sp + 4160#64) pk ∗ memRegion (sp + 14944#64) 9760 ∗
        memRegion (sp + 24704#64) 1568 ∗
        PolyMem (sp + 26320#64) (polyVecNat (rHatPoly16 prf0)) ∗
        PolyMem (sp + 26832#64) (polyVecNat (rHatPoly16 prf1)) ∗
        PolyMem (sp + 27344#64) (polyVecNat (rHatPoly16 prf2)) ∗
        PolyMem (sp + 27856#64) (polyVecNat (rHatPoly16 prf3)) ∗ Rest))
    (entails_sub (Entails.of_eq hm1488_944) (by sep_frame)
      (entails_sub (Entails.of_eq hm28_2048) (by sep_frame)
        (entails_sub (Entails.of_eq hm30_2048) (by sep_frame)
          (entails_sub (Entails.of_eq hm33_132) (by sep_frame) (by sep_frame))))) ?_
  refine sepWP_seq_env hcl1 hro1
    (seg6_e1_e2_part hb hbase s1 sp coins 0#8 _ hc hpc1 hrun1 hsp1 hspA1 hx19_1 hcl1 hro1) ?_
  rintro sf Pf hpcf hrunf hclf hrof ⟨hspf, hspAf, hx20f, hfpf, _, _, hPf⟩
  have hm14_10272 := (split_14432_512 sp).symm
  exact SepWP.done hpcf hrunf
    ⟨hspf, hspAf, hx20f, hfpf.trans hfp1, hclf, hrof,
      Entails.trans hPf (entails_sub (Entails.of_eq hm14_10272) (by sep_frame) (by sep_frame))⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6PrfRhat
