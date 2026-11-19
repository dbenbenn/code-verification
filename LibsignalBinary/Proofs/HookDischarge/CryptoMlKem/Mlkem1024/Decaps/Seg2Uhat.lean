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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg1b -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg2UhatIter -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a

/-!
# `kyber_decapsulate` (`B06`) — Segment 2 (`uHat[0..3]` Loop & Copy, `+0x05dc .. +0x1858`)

Composes the 4 iterations of `seg2_uhat_iter` (`+0x05dc .. +0x1840`) with the `2048`-byte
`B28` (`memcpy`) copy from `[sp + 14432, sp + 16480)` to `[sp + 4160, sp + 6208)`
(`+0x1840 .. +0x1858`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg2Uhat

open Arm64 Arm64.Obj ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (Poly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  PolyMem polyVecNat vecRangeBytes vecRangeBytes_length vecRangeMem_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  entails_sub spAligned_of_chk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base (
  blk06_code_eq blk06_tree_size blkLib06 blkPC06 blkPl06 blkPlaceable06 blkTree06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs (SpillSliceMem)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg1b (
  blk28_memcpy_06 uHatZetaSpill40)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg2UhatIter (
  seg2_uhat_iter uHatPoly16)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC06 blkLib06 blkTree06 blk06_code_eq blk06_tree_size
  via_placement blkPl06 blkPlaceable06 [0x1840 → 0x1854]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl06_ρ [MlKemPlacement] (sym : String) :
    blkPl06.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

attribute [local irreducible] blkPC06 polyVecNat uHatZetaSpill40

theorem ct_pointsTo_split (ctA : BitVec 64) {ct : List (BitVec 8)} (hct : ct.length = 1568) :
    (ctA ↦ₛ ct) =
      (ctA ↦ₛ ct.take 352) ∗
      ((ctA + 352#64) ↦ₛ (ct.drop 352).take 352) ∗
      ((ctA + 704#64) ↦ₛ (ct.drop 704).take 352) ∗
      ((ctA + 1056#64) ↦ₛ (ct.drop 1056).take 352) ∗
      ((ctA + 1408#64) ↦ₛ ct.drop 1408) := by
  have h0 : ct = ct.take 352 ++ ct.drop 352 := (List.take_append_drop 352 ct).symm
  have h1 : ct.drop 352 = (ct.drop 352).take 352 ++ ct.drop 704 := by
    simpa [List.drop_drop] using (List.take_append_drop 352 (ct.drop 352)).symm
  have h2 : ct.drop 704 = (ct.drop 704).take 352 ++ ct.drop 1056 := by
    simpa [List.drop_drop] using (List.take_append_drop 352 (ct.drop 704)).symm
  have h3 : ct.drop 1056 = (ct.drop 1056).take 352 ++ ct.drop 1408 := by
    simpa [List.drop_drop] using (List.take_append_drop 352 (ct.drop 1056)).symm
  have hl0 : (ct.take 352).length = 352 := by simp [hct]
  have hl1 : ((ct.drop 352).take 352).length = 352 := by simp [hct]
  have hl2 : ((ct.drop 704).take 352).length = 352 := by simp [hct]
  have hl3 : ((ct.drop 1056).take 352).length = 352 := by simp [hct]
  conv_lhs => rw [h0]
  rw [pointsToBytes_append, hl0, show BitVec.ofNat 64 352 = 352#64 from rfl]
  conv_lhs => rhs; rw [h1]
  rw [pointsToBytes_append, hl1, show ctA + 352#64 + BitVec.ofNat 64 352 = ctA + 704#64 by bv_omega]
  conv_lhs => rhs; rhs; rw [h2]
  rw [pointsToBytes_append, hl2, show ctA + 704#64 + BitVec.ofNat 64 352 = ctA + 1056#64 by bv_omega]
  conv_lhs => rhs; rhs; rhs; rw [h3]
  rw [pointsToBytes_append, hl3, show ctA + 1056#64 + BitVec.ofNat 64 352 = ctA + 1408#64 by bv_omega]

private theorem fourPolys_eq_pointsToBytes (ptr : BitVec 64) (u0 u1 u2 u3 : Poly16) :
    PolyMem ptr (polyVecNat u0) ∗
      PolyMem (ptr + 512#64) (polyVecNat u1) ∗
      PolyMem (ptr + 1024#64) (polyVecNat u2) ∗
      PolyMem (ptr + 1536#64) (polyVecNat u3) =
      (ptr ↦ₛ (vecRangeBytes 32 (polyVecNat u0) ++ vecRangeBytes 32 (polyVecNat u1) ++
        vecRangeBytes 32 (polyVecNat u2) ++ vecRangeBytes 32 (polyVecNat u3))) := by
  set b0 := vecRangeBytes 32 (polyVecNat u0)
  set b1 := vecRangeBytes 32 (polyVecNat u1)
  set b2 := vecRangeBytes 32 (polyVecNat u2)
  set b3 := vecRangeBytes 32 (polyVecNat u3)
  have h0 : b0.length = 512 := vecRangeBytes_length 32 _
  have h1 : b1.length = 512 := vecRangeBytes_length 32 _
  have h2 : b2.length = 512 := vecRangeBytes_length 32 _
  rw [List.append_assoc, List.append_assoc,
    pointsToBytes_append, h0, show BitVec.ofNat 64 512 = 512#64 from rfl,
    pointsToBytes_append, h1, show ptr + 512#64 + BitVec.ofNat 64 512 = ptr + 1024#64 by bv_omega,
    pointsToBytes_append, h2, show ptr + 1024#64 + BitVec.ofNat 64 512 = ptr + 1536#64 by bv_omega,
    ← vecRangeMem_eq_pointsToBytes 32 ptr (polyVecNat u0),
    ← vecRangeMem_eq_pointsToBytes 32 (ptr + 512#64) (polyVecNat u1),
    ← vecRangeMem_eq_pointsToBytes 32 (ptr + 1024#64) (polyVecNat u2),
    ← vecRangeMem_eq_pointsToBytes 32 (ptr + 1536#64) (polyVecNat u3)]
  rfl

private theorem seg2_copy_uhat [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp : BitVec 64) (u0 u1 u2 u3 : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + 0x1840#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (_hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + 0x1858#64) s
      (memRegion (sp + 4160#64) 2048 ∗
        PolyMem (sp + 14432#64) (polyVecNat u0) ∗
        PolyMem (sp + 14944#64) (polyVecNat u1) ∗
        PolyMem (sp + 15456#64) (polyVecNat u2) ∗
        PolyMem (sp + 15968#64) (polyVecNat u3) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        (Pf ⊢ PolyMem (sp + 4160#64) (polyVecNat u0) ∗
          PolyMem (sp + 4672#64) (polyVecNat u1) ∗
          PolyMem (sp + 5184#64) (polyVecNat u2) ∗
          PolyMem (sp + 5696#64) (polyVecNat u3) ∗
          memRegion (sp + 14432#64) 2048 ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  generalize hbs_def :
    vecRangeBytes 32 (polyVecNat u0) ++ vecRangeBytes 32 (polyVecNat u1) ++
      vecRangeBytes 32 (polyVecNat u2) ++ vecRangeBytes 32 (polyVecNat u3) = bs
  have hbs_len : bs.length = 2048 := by
    rw [← hbs_def]; simp only [List.length_append, vecRangeBytes_length]
  have hsrc : PolyMem (sp + 14432#64) (polyVecNat u0) ∗
      PolyMem (sp + 14944#64) (polyVecNat u1) ∗
      PolyMem (sp + 15456#64) (polyVecNat u2) ∗
      PolyMem (sp + 15968#64) (polyVecNat u3) = ((sp + 14432#64) ↦ₛ bs) := by
    rw [← hbs_def,
      show sp + 14944#64 = sp + 14432#64 + 512#64 by clear * -; bv_omega,
      show sp + 15456#64 = sp + 14432#64 + 1024#64 by clear * -; bv_omega,
      show sp + 15968#64 = sp + 14432#64 + 1536#64 by clear * -; bv_omega]
    exact fourPolys_eq_pointsToBytes (sp + 14432#64) u0 u1 u2 u3
  have hdst : ((sp + 4160#64) ↦ₛ bs) =
      PolyMem (sp + 4160#64) (polyVecNat u0) ∗
      PolyMem (sp + 4672#64) (polyVecNat u1) ∗
      PolyMem (sp + 5184#64) (polyVecNat u2) ∗
      PolyMem (sp + 5696#64) (polyVecNat u3) := by
    rw [← hbs_def,
      show sp + 4672#64 = sp + 4160#64 + 512#64 by clear * -; bv_omega,
      show sp + 5184#64 = sp + 4160#64 + 1024#64 by clear * -; bv_omega,
      show sp + 5696#64 = sp + 4160#64 + 1536#64 by clear * -; bv_omega]
    exact (fourPolys_eq_pointsToBytes (sp + 4160#64) u0 u1 u2 u3).symm
  have h14432_reg : ((sp + 14432#64) ↦ₛ bs) ⊢ memRegion (sp + 14432#64) 2048 := by
    simpa [hbs_len] using pointsToBytes_entails_memRegion (sp + 14432#64) bs
  refine SepWP.weaken_pre
    (show _ ⊢ memRegion (sp + 4160#64) 2048 ∗ ((sp + 14432#64) ↦ₛ bs) ∗ Rest by
      rw [← hsrc]; sep_frame) ?_
  wp_cut_codeLoaded
  wp_steps 5
  apply SepWP.done (by wp_norm_lhs) (by assumption)
  intro _hcl2
  wp_call (blk28_memcpy_06 blkPl06.base) (sp + 4160#64, sp + 14432#64, bs)
  rw [hdst]
  have hsp_sf : sf.sp = sp := by simp [*]
  refine SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨hsp_sf, spAligned_of_chk hsp_sf hsp_chk,
      by simp [*], by simp [*], by simp [*], by simp [*], by simp [*], ?_⟩
  exact entails_sub h14432_reg (by sep_frame) (by sep_frame)

/-- Composed Segment 2 contract (`+0x05dc → +0x1858`). -/
theorem seg2_uhat_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp ctA : BitVec 64) (ct : List (BitVec 8)) (Rest : SepProp)
    (hpc : s.pc = b + 0x05dc#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx0 : s.readReg64 .x0 = ctA)
    (hx19 : s.readReg64 .x19 = sp + 14432#64)
    (hx22 : s.readReg64 .x22 = 0#64)
    (hx23 : s.readReg64 .x23 = sp + 14448#64)
    (hx24 : s.readReg64 .x24 = 16#64)
    (hx27 : s.readReg64 .x27 = sp + 4160#64)
    (hx28 : s.readReg64 .x28 = 62209#64)
    (hv8 : (s.readVReg128 8#5).truncate 64 = 0x0d010d010d010d01#64)
    (hct : ct.length = 1568) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + 0x1858#64) s
      (stackAt sp 1136 ∗ SpillSliceMem 21 (sp + 2064#64) uHatZetaSpill40 ∗
        memRegion (sp + 2400#64) 8 ∗ memRegion (sp + 2416#64) 8 ∗
        memRegion (sp + 4160#64) 2048 ∗ memRegion (sp + 14432#64) 2048 ∗
        memRegion (sp + 28368#64) 32 ∗ (ctA ↦ₛ ct) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = sp + 4160#64 ∧
        sf.readReg64 .x28 = 62209#64 ∧
        (Pf ⊢ stackAt sp 1136 ∗ SpillSliceMem 21 (sp + 2064#64) uHatZetaSpill40 ∗
          memRegion (sp + 2400#64) 8 ∗ memRegion (sp + 2416#64) 8 ∗
          PolyMem (sp + 4160#64) (polyVecNat (uHatPoly16 (ct.take 352))) ∗
          PolyMem (sp + 4672#64) (polyVecNat (uHatPoly16 ((ct.drop 352).take 352))) ∗
          PolyMem (sp + 5184#64) (polyVecNat (uHatPoly16 ((ct.drop 704).take 352))) ∗
          PolyMem (sp + 5696#64) (polyVecNat (uHatPoly16 ((ct.drop 1056).take 352))) ∗
          memRegion (sp + 14432#64) 2048 ∗ memRegion (sp + 28368#64) 32 ∗
          (ctA ↦ₛ ct) ∗ Rest)) := by
  have hsplit4160 : memRegion (sp + 4160#64) 2048 =
      memRegion (sp + 4160#64) 512 ∗ memRegion (sp + 4672#64) 1536 :=
    memRegion_split' rfl (by bv_omega) (by decide)
  have hsplit14432 : memRegion (sp + 14432#64) 2048 =
      (memRegion (sp + 14432#64) 512 ∗ memRegion (sp + 14944#64) 512 ∗
        memRegion (sp + 15456#64) 512 ∗ memRegion (sp + 15968#64) 512) := by
    rw [memRegion_split' (b := sp + 14432#64) (b' := sp + 14944#64) (n := 512) (k := (1536 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 14944#64) (b' := sp + 15456#64) (n := 512) (k := (1024 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 15456#64) (b' := sp + 15968#64) (n := 512) (k := (512 : Nat)) rfl (by bv_omega) (by decide)]
  have hl0 : (ct.take 352).length = 352 := by simp [hct]
  have hl1 : ((ct.drop 352).take 352).length = 352 := by simp [hct]
  have hl2 : ((ct.drop 704).take 352).length = 352 := by simp [hct]
  have hl3 : ((ct.drop 1056).take 352).length = 352 := by simp [hct]
  set R0 := memRegion (sp + 4672#64) 1536 ∗ memRegion (sp + 14944#64) 512 ∗
    memRegion (sp + 15456#64) 512 ∗ memRegion (sp + 15968#64) 512 ∗
    ((ctA + 352#64) ↦ₛ (ct.drop 352).take 352) ∗
    ((ctA + 704#64) ↦ₛ (ct.drop 704).take 352) ∗
    ((ctA + 1056#64) ↦ₛ (ct.drop 1056).take 352) ∗
    ((ctA + 1408#64) ↦ₛ ct.drop 1408) ∗ Rest
  have hP0 : stackAt sp 1136 ∗ SpillSliceMem 21 (sp + 2064#64) uHatZetaSpill40 ∗
      memRegion (sp + 2400#64) 8 ∗ memRegion (sp + 2416#64) 8 ∗
      memRegion (sp + 4160#64) 2048 ∗ memRegion (sp + 14432#64) 2048 ∗
      memRegion (sp + 28368#64) 32 ∗ (ctA ↦ₛ ct) ∗ Rest ⊢
      stackAt sp 1136 ∗ SpillSliceMem 21 (sp + 2064#64) uHatZetaSpill40 ∗
      memRegion (sp + 2400#64) 8 ∗ memRegion (sp + 2416#64) 8 ∗
      memRegion (sp + 4160#64) 512 ∗ memRegion (sp + 28368#64) 32 ∗
      memRegion (sp + 14432#64 + BitVec.ofNat 64 (512 * 0)) 512 ∗ (ctA ↦ₛ ct.take 352) ∗ R0 := by
    dsimp only [R0]
    rw [hsplit4160, hsplit14432, ct_pointsTo_split ctA hct, BitVec.add_zero]; sep_frame
  have it0 := seg2_uhat_iter hb hbase s sp ctA (idx := 0) (by decide) (ct.take 352) hl0 R0
    hpc hrun hsp hspA hcl hro hx0 hx19 hx22
    (by simpa using hx23) (by simpa using hx24) hx27 hx28 hv8
  simp only [show (0 : Nat) < 3 by decide, ↓reduceIte] at it0
  refine SepWP.weaken_pre hP0 (sepWP_seq_env hcl hro it0 ?_)
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hfp_1, hx0_1, hx19_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hv8_1, hP1⟩
  set R1 := memRegion (sp + 4672#64) 1536 ∗
    PolyMem (sp + 14432#64) (polyVecNat (uHatPoly16 (ct.take 352))) ∗
    memRegion (sp + 15456#64) 512 ∗ memRegion (sp + 15968#64) 512 ∗
    (ctA ↦ₛ ct.take 352) ∗
    ((ctA + 704#64) ↦ₛ (ct.drop 704).take 352) ∗
    ((ctA + 1056#64) ↦ₛ (ct.drop 1056).take 352) ∗
    ((ctA + 1408#64) ↦ₛ ct.drop 1408) ∗ Rest
  have hP1' : P1 ⊢ stackAt sp 1136 ∗ SpillSliceMem 21 (sp + 2064#64) uHatZetaSpill40 ∗
      memRegion (sp + 2400#64) 8 ∗ memRegion (sp + 2416#64) 8 ∗
      memRegion (sp + 4160#64) 512 ∗ memRegion (sp + 28368#64) 32 ∗
      memRegion (sp + 14432#64 + BitVec.ofNat 64 (512 * 1)) 512 ∗
      ((ctA + 352#64) ↦ₛ (ct.drop 352).take 352) ∗ R1 := by
    refine Entails.trans hP1 ?_
    dsimp only [R0, R1]
    rw [BitVec.add_zero, show sp + 14432#64 + BitVec.ofNat 64 (512 * 1) = sp + 14944#64 by clear * -; bv_omega]
    sep_frame
  have it1 := seg2_uhat_iter hb hbase s1 sp (ctA + 352#64) (idx := 1) (by decide)
    ((ct.drop 352).take 352) hl1 R1 hpc1 hrun1 hsp1 hspA1 hcl1 hro1 hx0_1 hx19_1 hx22_1
    hx23_1 hx24_1 hx27_1 hx28_1 hv8_1
  simp only [show (1 : Nat) < 3 by decide, ↓reduceIte] at it1
  refine SepWP.weaken_pre hP1' (sepWP_seq_env hcl1 hro1 it1 ?_)
  rintro s2 P2 hpc2 hrun2 hcl2 hro2
    ⟨hsp2, hspA2, hfp_2, hx0_2, hx19_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hv8_2, hP2⟩
  set R2 := memRegion (sp + 4672#64) 1536 ∗
    PolyMem (sp + 14432#64) (polyVecNat (uHatPoly16 (ct.take 352))) ∗
    PolyMem (sp + 14944#64) (polyVecNat (uHatPoly16 ((ct.drop 352).take 352))) ∗
    memRegion (sp + 15968#64) 512 ∗
    (ctA ↦ₛ ct.take 352) ∗ ((ctA + 352#64) ↦ₛ (ct.drop 352).take 352) ∗
    ((ctA + 1056#64) ↦ₛ (ct.drop 1056).take 352) ∗
    ((ctA + 1408#64) ↦ₛ ct.drop 1408) ∗ Rest
  have hP2' : P2 ⊢ stackAt sp 1136 ∗ SpillSliceMem 21 (sp + 2064#64) uHatZetaSpill40 ∗
      memRegion (sp + 2400#64) 8 ∗ memRegion (sp + 2416#64) 8 ∗
      memRegion (sp + 4160#64) 512 ∗ memRegion (sp + 28368#64) 32 ∗
      memRegion (sp + 14432#64 + BitVec.ofNat 64 (512 * 2)) 512 ∗
      ((ctA + 704#64) ↦ₛ (ct.drop 704).take 352) ∗ R2 := by
    refine Entails.trans hP2 ?_
    dsimp only [R1, R2]
    rw [show sp + 14432#64 + BitVec.ofNat 64 (512 * 1) = sp + 14944#64 by clear * -; bv_omega,
      show sp + 14432#64 + BitVec.ofNat 64 (512 * 2) = sp + 15456#64 by clear * -; bv_omega]
    sep_frame
  have it2 := seg2_uhat_iter hb hbase s2 sp (ctA + 704#64) (idx := 2) (by decide)
    ((ct.drop 704).take 352) hl2 R2 hpc2 hrun2 hsp2 hspA2 hcl2 hro2
    (by rw [hx0_2]; clear * -; bv_omega) hx19_2 hx22_2 hx23_2 hx24_2 hx27_2 hx28_2 hv8_2
  simp only [show (2 : Nat) < 3 by decide, ↓reduceIte] at it2
  refine SepWP.weaken_pre hP2' (sepWP_seq_env hcl2 hro2 it2 ?_)
  rintro s3 P3 hpc3 hrun3 hcl3 hro3
    ⟨hsp3, hspA3, hfp_3, hx0_3, hx19_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hv8_3, hP3⟩
  set R3 := memRegion (sp + 4672#64) 1536 ∗
    PolyMem (sp + 14432#64) (polyVecNat (uHatPoly16 (ct.take 352))) ∗
    PolyMem (sp + 14944#64) (polyVecNat (uHatPoly16 ((ct.drop 352).take 352))) ∗
    PolyMem (sp + 15456#64) (polyVecNat (uHatPoly16 ((ct.drop 704).take 352))) ∗
    (ctA ↦ₛ ct.take 352) ∗ ((ctA + 352#64) ↦ₛ (ct.drop 352).take 352) ∗
    ((ctA + 704#64) ↦ₛ (ct.drop 704).take 352) ∗
    ((ctA + 1408#64) ↦ₛ ct.drop 1408) ∗ Rest
  have hP3' : P3 ⊢ stackAt sp 1136 ∗ SpillSliceMem 21 (sp + 2064#64) uHatZetaSpill40 ∗
      memRegion (sp + 2400#64) 8 ∗ memRegion (sp + 2416#64) 8 ∗
      memRegion (sp + 4160#64) 512 ∗ memRegion (sp + 28368#64) 32 ∗
      memRegion (sp + 14432#64 + BitVec.ofNat 64 (512 * 3)) 512 ∗
      ((ctA + 1056#64) ↦ₛ (ct.drop 1056).take 352) ∗ R3 := by
    refine Entails.trans hP3 ?_
    dsimp only [R2, R3]
    rw [show sp + 14432#64 + BitVec.ofNat 64 (512 * 2) = sp + 15456#64 by clear * -; bv_omega,
      show sp + 14432#64 + BitVec.ofNat 64 (512 * 3) = sp + 15968#64 by clear * -; bv_omega]
    sep_frame
  have it3 := seg2_uhat_iter hb hbase s3 sp (ctA + 1056#64) (idx := 3) (by decide)
    ((ct.drop 1056).take 352) hl3 R3 hpc3 hrun3 hsp3 hspA3 hcl3 hro3
    (by rw [hx0_3]; clear * -; bv_omega) hx19_3 hx22_3 hx23_3 hx24_3 hx27_3 hx28_3 hv8_3
  simp only [Nat.lt_irrefl, ↓reduceIte] at it3
  refine SepWP.weaken_pre hP3' (sepWP_seq_env hcl3 hro3 it3 ?_)
  rintro s4 P4 hpc4 hrun4 hcl4 _
    ⟨hsp4, hspA4, hfp_4, _, _, _, _, _, hx25_4, hx26_4, hx27_4, hx28_4, _, hP4⟩
  have hP4' : P4 ⊢ memRegion (sp + 4160#64) 2048 ∗
      PolyMem (sp + 14432#64) (polyVecNat (uHatPoly16 (ct.take 352))) ∗
      PolyMem (sp + 14944#64) (polyVecNat (uHatPoly16 ((ct.drop 352).take 352))) ∗
      PolyMem (sp + 15456#64) (polyVecNat (uHatPoly16 ((ct.drop 704).take 352))) ∗
      PolyMem (sp + 15968#64) (polyVecNat (uHatPoly16 ((ct.drop 1056).take 352))) ∗
      (stackAt sp 1136 ∗ SpillSliceMem 21 (sp + 2064#64) uHatZetaSpill40 ∗
        memRegion (sp + 2400#64) 8 ∗ memRegion (sp + 2416#64) 8 ∗
        memRegion (sp + 28368#64) 32 ∗ (ctA ↦ₛ ct) ∗ Rest) := by
    refine Entails.trans hP4 ?_
    dsimp only [R3]
    rw [show sp + 14432#64 + BitVec.ofNat 64 (512 * 3) = sp + 15968#64 by clear * -; bv_omega,
      hsplit4160, ct_pointsTo_split ctA hct]; sep_frame
  refine SepWP.weaken_pre hP4'
    (SepWP.mono (seg2_copy_uhat hb hbase s4 sp _ _ _ _ _ hpc4 hrun4 hsp4 hspA4 hcl4) ?_)
  rintro sf Pf _ _ ⟨hsp_f, hspA_f, hfp_f, hx25_f, hx26_f, hx27_f, hx28_f, hPf⟩
  exact ⟨hsp_f, hspA_f,
    hfp_f.trans (hfp_4.trans (hfp_3.trans (hfp_2.trans hfp_1))),
    hx25_f.trans (hx25_4.trans (hx25_3.trans (hx25_2.trans hx25_1))),
    hx26_f.trans (hx26_4.trans (hx26_3.trans (hx26_2.trans hx26_1))),
    hx27_f.trans hx27_4, hx28_f.trans hx28_4, Entails.trans hPf (by sep_frame)⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg2Uhat
