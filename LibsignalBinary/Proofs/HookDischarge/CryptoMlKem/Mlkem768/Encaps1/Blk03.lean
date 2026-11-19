/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLift
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg4
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg5
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg6

/-!
# `B03`: `encapsulate1_serialized` (`Mlkem768.Encaps1.Blk03`)

Composes `Seg1`..`Seg6` of `mlkemBlk03` (`7114` words, tight stack `18,160` B) into:
- `blk03_encaps1_safe_ok : MlKemBlockSafeOk 3 mlkemBlk03CoreSpec`
- `blk03_encaps1_ok : MlKemBlockOk 3 mlkemBlk03TermCoreSpec`
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Blk03

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemBlockOk MlKemBlockSafeOk MlKemPlacement
  mlkemCaller_ok mlkemMpl mlkemSafeCaller_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLift (
  mlkemBlockOk_withNonSyscallPreserved mlkemBlockSafeOk_withNonSyscallPreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLiftBase (
  mlkemKeep mlkemRoOk_stripExecOutside stripS_mem stripS_readReg64 stripS_sp)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Shake128MatrixTerminates sha3_512List shake256List)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd (neonCbd2Poly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  cell_entails_memRegion8 sepWP_seq_env withMlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  PolyMem Vec128At polyVecNat vecRangeMem_entails_memRegion)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (entails_sub)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base (
  MlkemBlk03Args SavedFrame03 blkPC03 blkPl03 encaps1OutCt1 encaps1OutEs encaps1OutSs
  mlkemBlk03CoreSpec mlkemBlk03RawSpec mlkemBlk03TermCoreSpec mlkemBlk03TermRawSpec
  safeSepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a (
  SavedArgs03 Seg2ConstsLo Seg2Preserved Seg2RegInv Seg2SeedConsts sha3_512List_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1 (seg1_wp)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2 (
  ATransMem ATransRowMem Seg2Exit seg2_safeSepWP seg2_sepWP)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd (shake256List_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3 (rHatPoly16 seg3_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg4 (seg4_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg5 (uVecPoly16 seg5_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg6 (
  encaps1Out_lengths seg6_ok)

private theorem vec128At_entails_memRegion16 (p : BitVec 64) (v : BitVec 128) :
    Vec128At p v ⊢ memRegion p 16 := by
  unfold Vec128At
  rw [memRegion_split' (b' := p + 8#64) (n := 8) (k := (8 : Nat)) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (cell_entails_memRegion8 _ _) (cell_entails_memRegion8 _ _)

private theorem seg2ConstsLo_entails (sp : BitVec 64) :
    Seg2ConstsLo sp ∗ memRegion (sp + 80#64) 8 ⊢ memRegion (sp + 40#64) 56 := by
  unfold Seg2ConstsLo
  rw [memRegion_split' (b := sp + 40#64) (b' := sp + 48#64) (n := 8) (k := (48 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 48#64) (b' := sp + 64#64) (n := 16) (k := (32 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 64#64) (b' := sp + 80#64) (n := 16) (k := (16 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 80#64) (b' := sp + 88#64) (n := 8) (k := (8 : Nat)) rfl (by bv_omega) (by decide)]
  refine Entails.trans (sepConj_mono
    (sepConj_mono (cell_entails_memRegion8 _ _)
      (sepConj_mono (vec128At_entails_memRegion16 _ _)
        (sepConj_mono (vec128At_entails_memRegion16 _ _)
          (cell_entails_memRegion8 _ _))))
    (Entails.refl _)) (by sep_frame)

private theorem aTransRowMem_entails (sp : BitVec 64) (rho : List (BitVec 8)) {row : Nat}
    (hrow : row < 3) :
    ATransRowMem sp rho row ⊢ memRegion (sp + BitVec.ofNat 64 (6832 + 1536 * row)) 1536 := by
  unfold ATransRowMem PolyMem
  have h1 : sp + BitVec.ofNat 64 (6832 + 1536 * row) + 512#64 =
      sp + BitVec.ofNat 64 (6832 + 1536 * row + 512) := by
    rcases (show row = 0 ∨ row = 1 ∨ row = 2 by omega) with rfl | rfl | rfl <;> bv_omega
  have h2 : sp + BitVec.ofNat 64 (6832 + 1536 * row + 512) + 512#64 =
      sp + BitVec.ofNat 64 (6832 + 1536 * row + 1024) := by
    rcases (show row = 0 ∨ row = 1 ∨ row = 2 by omega) with rfl | rfl | rfl <;> bv_omega
  rw [memRegion_split' (b' := sp + BitVec.ofNat 64 (6832 + 1536 * row + 512))
        (n := 512) (k := (1024 : Nat)) rfl (by rw [← h1]) (by decide),
      memRegion_split' (b' := sp + BitVec.ofNat 64 (6832 + 1536 * row + 1024))
        (n := 512) (k := (512 : Nat)) rfl (by rw [← h2]) (by decide)]
  exact sepConj_mono (vecRangeMem_entails_memRegion 32 _ _)
    (sepConj_mono (vecRangeMem_entails_memRegion 32 _ _)
      (vecRangeMem_entails_memRegion 32 _ _))

private theorem aTransMem_entails (sp : BitVec 64) (rho : List (BitVec 8)) :
    ATransMem sp rho ⊢ memRegion (sp + 6832#64) 4608 := by
  unfold ATransMem
  rw [memRegion_split' (b := sp + 6832#64) (b' := sp + BitVec.ofNat 64 (6832 + 1536 * 1))
        (n := 1536) (k := (3072 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + BitVec.ofNat 64 (6832 + 1536 * 1))
        (b' := sp + BitVec.ofNat 64 (6832 + 1536 * 2))
        (n := 1536) (k := (1536 : Nat)) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (aTransRowMem_entails sp rho (row := 0) (by decide))
    (sepConj_mono (aTransRowMem_entails sp rho (row := 1) (by decide))
      (aTransRowMem_entails sp rho (row := 2) (by decide)))

private noncomputable def RestSeg3 (s0 : State) (sp : BitVec 64) (a : MlkemBlk03Args) : SepProp :=
  SavedArgs03 sp a ∗
  memRegion (sp + 40#64) 1208 ∗ memRegion (sp + 1248#64) 304 ∗
  memRegion (sp + 2576#64) 1152 ∗ memRegion (sp + 3728#64) 544 ∗
  memRegion (sp + 4784#64) 1984 ∗ ATransMem sp (a.hdr64.take 32) ∗
  memRegion (sp + 12433#64) 15 ∗ memRegion (sp + 14112#64) 1408 ∗
  memRegion (sp + 15520#64) 128 ∗ memRegion (sp + 15648#64) 32 ∗
  memRegion (sp + 15808#64) 392 ∗ memRegion (sp + 16200#64) 8 ∗
  memRegion (sp + 16307#64) 29 ∗ memRegion (sp + 16336#64) 192 ∗
  memRegion (sp + 16656#64) 192 ∗ memRegion (sp + 16848#64) 16 ∗
  SavedFrame03 (s0.sp - 160#64) s0 ∗
  (a.hdrA ↦ₛ a.hdr64) ∗ (a.randA ↦ₛ a.rand) ∗
  memRegion a.ret 961 ∗ memRegion a.esA 2080 ∗ memRegion a.ssA 32

private theorem seg2_to_seg3_entails (s0 : State) (a : MlkemBlk03Args) :
    let sp := s0.sp - 17024#64
    let rho := a.hdr64.take 32
    let hashed := sha3_512List (a.rand ++ a.hdr64.drop 32)
    Seg2ConstsLo sp ∗ memRegion (sp + 96#64) 2096 ∗
      memRegion (sp + 2192#64) 1512 ∗ memRegion (sp + 4272#64) 1632 ∗
      memRegion (sp + 12448#64) 24 ∗ memRegion (sp + 13984#64) 504 ∗
      ATransMem sp rho ∗ Seg2Preserved s0 a emp ⊢
    ((sp + 6768#64) ↦ₛ hashed) ∗
      memRegion (sp + 1552#64) 640 ∗ memRegion (sp + 2192#64) 384 ∗
      memRegion (sp + 4272#64) 512 ∗ memRegion (sp + 11440#64) 960 ∗
      memRegion (sp + 12400#64) 33 ∗ memRegion (sp + 12448#64) 1536 ∗
      memRegion (sp + 13984#64) 128 ∗ memRegion (sp + 15680#64) 128 ∗
      memRegion (sp + 16208#64) 99 ∗ memRegion (sp + 16528#64) 128 ∗
      stackAt sp 1136 ∗ RestSeg3 s0 sp a := by
  intro sp rho hashed
  dsimp only [Seg2Preserved, RestSeg3]
  have hsp160 : sp + 16864#64 = s0.sp - 160#64 := by dsimp only [sp]; bv_omega
  rw [hsp160, sepConj_emp]
  have hm40 : memRegion (sp + 40#64) 56 ∗ memRegion (sp + 96#64) 2096 =
      memRegion (sp + 40#64) 1208 ∗ memRegion (sp + 1248#64) 304 ∗ memRegion (sp + 1552#64) 640 := by
    rw [← memRegion_split' (b := sp + 40#64) (b' := sp + 96#64) (n := 56) (k := (2096 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 40#64) (b' := sp + 1248#64) (n := 1208) (k := (944 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 1248#64) (b' := sp + 1552#64) (n := 304) (k := (640 : Nat)) rfl (by bv_omega) (by decide)]
  have hm2192 : memRegion (sp + 2192#64) 1512 ∗ memRegion (sp + 3704#64) 568 =
      memRegion (sp + 2192#64) 384 ∗ memRegion (sp + 2576#64) 1152 ∗ memRegion (sp + 3728#64) 544 := by
    rw [← memRegion_split' (b := sp + 2192#64) (b' := sp + 3704#64) (n := 1512) (k := (568 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 2192#64) (b' := sp + 2576#64) (n := 384) (k := (1696 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 2576#64) (b' := sp + 3728#64) (n := 1152) (k := (544 : Nat)) rfl (by bv_omega) (by decide)]
  have hm4272 : memRegion (sp + 4272#64) 1632 ∗ memRegion (sp + 5904#64) 864 =
      memRegion (sp + 4272#64) 512 ∗ memRegion (sp + 4784#64) 1984 := by
    rw [← memRegion_split' (b := sp + 4272#64) (b' := sp + 5904#64) (n := 1632) (k := (864 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 4272#64) (b' := sp + 4784#64) (n := 512) (k := (1984 : Nat)) rfl (by bv_omega) (by decide)]
  have hm11440 : memRegion (sp + 11440#64) 1008 =
      memRegion (sp + 11440#64) 960 ∗ memRegion (sp + 12400#64) 33 ∗ memRegion (sp + 12433#64) 15 := by
    rw [memRegion_split' (b := sp + 11440#64) (b' := sp + 12400#64) (n := 960) (k := (48 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 12400#64) (b' := sp + 12433#64) (n := 33) (k := (15 : Nat)) rfl (by bv_omega) (by decide)]
  have hm12448 : memRegion (sp + 12448#64) 24 ∗ memRegion (sp + 12472#64) 1512 =
      memRegion (sp + 12448#64) 1536 :=
    (memRegion_split' (b := sp + 12448#64) (b' := sp + 12472#64) (n := 24) (k := (1512 : Nat)) rfl (by bv_omega) (by decide)).symm
  have hm13984 : memRegion (sp + 13984#64) 504 ∗ memRegion (sp + 14488#64) 2376 =
      memRegion (sp + 13984#64) 128 ∗ memRegion (sp + 14112#64) 1408 ∗
      memRegion (sp + 15520#64) 128 ∗ memRegion (sp + 15648#64) 32 ∗
      memRegion (sp + 15680#64) 128 ∗ memRegion (sp + 15808#64) 392 ∗
      memRegion (sp + 16200#64) 8 ∗ memRegion (sp + 16208#64) 99 ∗
      memRegion (sp + 16307#64) 29 ∗ memRegion (sp + 16336#64) 192 ∗
      memRegion (sp + 16528#64) 128 ∗ memRegion (sp + 16656#64) 192 ∗
      memRegion (sp + 16848#64) 16 := by
    rw [← memRegion_split' (b := sp + 13984#64) (b' := sp + 14488#64) (n := 504) (k := (2376 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 13984#64) (b' := sp + 14112#64) (n := 128) (k := (2752 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 14112#64) (b' := sp + 15520#64) (n := 1408) (k := (1344 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 15520#64) (b' := sp + 15648#64) (n := 128) (k := (1216 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 15648#64) (b' := sp + 15680#64) (n := 32) (k := (1184 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 15680#64) (b' := sp + 15808#64) (n := 128) (k := (1056 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 15808#64) (b' := sp + 16200#64) (n := 392) (k := (664 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 16200#64) (b' := sp + 16208#64) (n := 8) (k := (656 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 16208#64) (b' := sp + 16307#64) (n := 99) (k := (557 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 16307#64) (b' := sp + 16336#64) (n := 29) (k := (528 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 16336#64) (b' := sp + 16528#64) (n := 192) (k := (336 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 16528#64) (b' := sp + 16656#64) (n := 128) (k := (208 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 16656#64) (b' := sp + 16848#64) (n := 192) (k := (16 : Nat)) rfl (by bv_omega) (by decide)]
  rw [hm11440]
  refine Entails.trans (entails_sub (Rest := memRegion (sp + 96#64) 2096 ∗
      memRegion (sp + 2192#64) 1512 ∗ memRegion (sp + 3704#64) 568 ∗
      memRegion (sp + 4272#64) 1632 ∗ memRegion (sp + 5904#64) 864 ∗
      memRegion (sp + 12448#64) 24 ∗ memRegion (sp + 12472#64) 1512 ∗
      memRegion (sp + 13984#64) 504 ∗ memRegion (sp + 14488#64) 2376 ∗
      SavedArgs03 sp a ∗ ((sp + 6768#64) ↦ₛ hashed) ∗ ATransMem sp rho ∗
      memRegion (sp + 11440#64) 960 ∗ memRegion (sp + 12400#64) 33 ∗ memRegion (sp + 12433#64) 15 ∗
      SavedFrame03 (s0.sp - 160#64) s0 ∗ stackAt sp 1136 ∗
      (a.hdrA ↦ₛ a.hdr64) ∗ (a.randA ↦ₛ a.rand) ∗
      memRegion a.ret 961 ∗ memRegion a.esA 2080 ∗ memRegion a.ssA 32)
    (seg2ConstsLo_entails sp) (by sep_frame) (by sep_frame)) ?_
  refine Entails.trans (entails_sub (Rest := memRegion (sp + 2192#64) 1512 ∗ memRegion (sp + 3704#64) 568 ∗
      memRegion (sp + 4272#64) 1632 ∗ memRegion (sp + 5904#64) 864 ∗
      memRegion (sp + 12448#64) 24 ∗ memRegion (sp + 12472#64) 1512 ∗
      memRegion (sp + 13984#64) 504 ∗ memRegion (sp + 14488#64) 2376 ∗
      SavedArgs03 sp a ∗ ((sp + 6768#64) ↦ₛ hashed) ∗ ATransMem sp rho ∗
      memRegion (sp + 11440#64) 960 ∗ memRegion (sp + 12400#64) 33 ∗ memRegion (sp + 12433#64) 15 ∗
      SavedFrame03 (s0.sp - 160#64) s0 ∗ stackAt sp 1136 ∗
      (a.hdrA ↦ₛ a.hdr64) ∗ (a.randA ↦ₛ a.rand) ∗
      memRegion a.ret 961 ∗ memRegion a.esA 2080 ∗ memRegion a.ssA 32)
    (Entails.of_eq hm40) (by sep_frame) (by sep_frame)) ?_
  refine Entails.trans (entails_sub (Rest := memRegion (sp + 40#64) 1208 ∗ memRegion (sp + 1248#64) 304 ∗
      memRegion (sp + 1552#64) 640 ∗
      memRegion (sp + 4272#64) 1632 ∗ memRegion (sp + 5904#64) 864 ∗
      memRegion (sp + 12448#64) 24 ∗ memRegion (sp + 12472#64) 1512 ∗
      memRegion (sp + 13984#64) 504 ∗ memRegion (sp + 14488#64) 2376 ∗
      SavedArgs03 sp a ∗ ((sp + 6768#64) ↦ₛ hashed) ∗ ATransMem sp rho ∗
      memRegion (sp + 11440#64) 960 ∗ memRegion (sp + 12400#64) 33 ∗ memRegion (sp + 12433#64) 15 ∗
      SavedFrame03 (s0.sp - 160#64) s0 ∗ stackAt sp 1136 ∗
      (a.hdrA ↦ₛ a.hdr64) ∗ (a.randA ↦ₛ a.rand) ∗
      memRegion a.ret 961 ∗ memRegion a.esA 2080 ∗ memRegion a.ssA 32)
    (Entails.of_eq hm2192) (by sep_frame) (by sep_frame)) ?_
  refine Entails.trans (entails_sub (Rest := memRegion (sp + 40#64) 1208 ∗ memRegion (sp + 1248#64) 304 ∗
      memRegion (sp + 1552#64) 640 ∗ memRegion (sp + 2192#64) 384 ∗
      memRegion (sp + 2576#64) 1152 ∗ memRegion (sp + 3728#64) 544 ∗
      memRegion (sp + 12448#64) 24 ∗ memRegion (sp + 12472#64) 1512 ∗
      memRegion (sp + 13984#64) 504 ∗ memRegion (sp + 14488#64) 2376 ∗
      SavedArgs03 sp a ∗ ((sp + 6768#64) ↦ₛ hashed) ∗ ATransMem sp rho ∗
      memRegion (sp + 11440#64) 960 ∗ memRegion (sp + 12400#64) 33 ∗ memRegion (sp + 12433#64) 15 ∗
      SavedFrame03 (s0.sp - 160#64) s0 ∗ stackAt sp 1136 ∗
      (a.hdrA ↦ₛ a.hdr64) ∗ (a.randA ↦ₛ a.rand) ∗
      memRegion a.ret 961 ∗ memRegion a.esA 2080 ∗ memRegion a.ssA 32)
    (Entails.of_eq hm4272) (by sep_frame) (by sep_frame)) ?_
  refine Entails.trans (entails_sub (Rest := memRegion (sp + 40#64) 1208 ∗ memRegion (sp + 1248#64) 304 ∗
      memRegion (sp + 1552#64) 640 ∗ memRegion (sp + 2192#64) 384 ∗
      memRegion (sp + 2576#64) 1152 ∗ memRegion (sp + 3728#64) 544 ∗
      memRegion (sp + 4272#64) 512 ∗ memRegion (sp + 4784#64) 1984 ∗
      memRegion (sp + 13984#64) 504 ∗ memRegion (sp + 14488#64) 2376 ∗
      SavedArgs03 sp a ∗ ((sp + 6768#64) ↦ₛ hashed) ∗ ATransMem sp rho ∗
      memRegion (sp + 11440#64) 960 ∗ memRegion (sp + 12400#64) 33 ∗ memRegion (sp + 12433#64) 15 ∗
      SavedFrame03 (s0.sp - 160#64) s0 ∗ stackAt sp 1136 ∗
      (a.hdrA ↦ₛ a.hdr64) ∗ (a.randA ↦ₛ a.rand) ∗
      memRegion a.ret 961 ∗ memRegion a.esA 2080 ∗ memRegion a.ssA 32)
    (Entails.of_eq hm12448) (by sep_frame) (by sep_frame)) ?_
  exact entails_sub (Rest := memRegion (sp + 40#64) 1208 ∗ memRegion (sp + 1248#64) 304 ∗
      memRegion (sp + 1552#64) 640 ∗ memRegion (sp + 2192#64) 384 ∗
      memRegion (sp + 2576#64) 1152 ∗ memRegion (sp + 3728#64) 544 ∗
      memRegion (sp + 4272#64) 512 ∗ memRegion (sp + 4784#64) 1984 ∗
      memRegion (sp + 12448#64) 1536 ∗
      SavedArgs03 sp a ∗ ((sp + 6768#64) ↦ₛ hashed) ∗ ATransMem sp rho ∗
      memRegion (sp + 11440#64) 960 ∗ memRegion (sp + 12400#64) 33 ∗ memRegion (sp + 12433#64) 15 ∗
      SavedFrame03 (s0.sp - 160#64) s0 ∗ stackAt sp 1136 ∗
      (a.hdrA ↦ₛ a.hdr64) ∗ (a.randA ↦ₛ a.rand) ∗
      memRegion a.ret 961 ∗ memRegion a.esA 2080 ∗ memRegion a.ssA 32)
    (Entails.of_eq hm13984) (by sep_frame) (by sep_frame)

private noncomputable def RestSeg4 (s0 : State) (sp : BitVec 64) (a : MlkemBlk03Args) : SepProp :=
  let rho := a.hdr64.take 32
  let hashed := sha3_512List (a.rand ++ a.hdr64.drop 32)
  let coins := hashed.drop 32
  let prf0 := shake256List 128 (coins ++ [0#8])
  let prf1 := shake256List 128 (coins ++ [1#8])
  let prf2 := shake256List 128 (coins ++ [2#8])
  SavedArgs03 sp a ∗
  memRegion (sp + 40#64) 1208 ∗ memRegion (sp + 1760#64) 432 ∗
  memRegion (sp + 3728#64) 544 ∗ memRegion (sp + 4784#64) 1984 ∗
  ((sp + 6768#64) ↦ₛ hashed) ∗ ATransMem sp rho ∗
  memRegion (sp + 11440#64) 960 ∗ memRegion (sp + 12433#64) 15 ∗
  PolyMem (sp + 12448#64) (polyVecNat (rHatPoly16 prf0)) ∗
  PolyMem (sp + 12960#64) (polyVecNat (rHatPoly16 prf1)) ∗
  PolyMem (sp + 13472#64) (polyVecNat (rHatPoly16 prf2)) ∗
  memRegion (sp + 15648#64) 32 ∗ memRegion (sp + 15808#64) 392 ∗
  memRegion (sp + 16200#64) 8 ∗ memRegion (sp + 16336#64) 192 ∗
  memRegion (sp + 16656#64) 192 ∗ memRegion (sp + 16848#64) 16 ∗
  SavedFrame03 (s0.sp - 160#64) s0 ∗
  (a.hdrA ↦ₛ a.hdr64) ∗ (a.randA ↦ₛ a.rand) ∗
  memRegion a.ret 961 ∗ memRegion a.esA 2080 ∗ memRegion a.ssA 32

private theorem seg3_to_seg4_entails (s0 : State) (sp : BitVec 64) (a : MlkemBlk03Args) :
    let hashed := sha3_512List (a.rand ++ a.hdr64.drop 32)
    let coins := hashed.drop 32
    let prf0 := shake256List 128 (coins ++ [0#8])
    let prf1 := shake256List 128 (coins ++ [1#8])
    let prf2 := shake256List 128 (coins ++ [2#8])
    ((sp + 6768#64) ↦ₛ hashed) ∗ memRegion (sp + 1552#64) 640 ∗
      ((sp + 2192#64) ↦ₛ prf0) ∗ ((sp + 2320#64) ↦ₛ prf1) ∗ ((sp + 2448#64) ↦ₛ prf2) ∗
      memRegion (sp + 4272#64) 512 ∗ memRegion (sp + 11440#64) 960 ∗
      ((sp + 12400#64) ↦ₛ coins) ∗ ((sp + 12432#64) ↦₈ 0#8) ∗
      PolyMem (sp + 12448#64) (polyVecNat (rHatPoly16 prf0)) ∗
      PolyMem (sp + 12960#64) (polyVecNat (rHatPoly16 prf1)) ∗
      PolyMem (sp + 13472#64) (polyVecNat (rHatPoly16 prf2)) ∗
      memRegion (sp + 13984#64) 128 ∗ memRegion (sp + 15680#64) 128 ∗
      memRegion (sp + 16208#64) 99 ∗ memRegion (sp + 16528#64) 128 ∗
      stackAt sp 1136 ∗ RestSeg3 s0 sp a ⊢
    ((sp + 12400#64) ↦ₛ coins) ∗ ((sp + 12432#64) ↦₈ 0#8) ∗
      memRegion (sp + 1248#64) 512 ∗ memRegion (sp + 2192#64) 1536 ∗
      memRegion (sp + 4272#64) 512 ∗ memRegion (sp + 13984#64) 1536 ∗
      memRegion (sp + 15520#64) 128 ∗ memRegion (sp + 15680#64) 128 ∗
      memRegion (sp + 16208#64) 128 ∗ memRegion (sp + 16528#64) 128 ∗
      stackAt sp 1136 ∗ RestSeg4 s0 sp a := by
  intro hashed coins prf0 prf1 prf2
  dsimp only [RestSeg3, RestSeg4]
  have hp {p : BitVec 64} {l : List (BitVec 8)} (hl : l.length = 128) :
      (p ↦ₛ l) ⊢ memRegion p 128 := hl ▸ pointsToBytes_entails_memRegion p l
  rw [memRegion_split' (b := sp + 1552#64) (b' := sp + 1760#64) (n := 208) (k := (432 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 1248#64) (b' := sp + 1552#64) (n := 304) (k := (208 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 2192#64) (b' := sp + 2320#64) (n := 128) (k := (1408 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 2320#64) (b' := sp + 2448#64) (n := 128) (k := (1280 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 2448#64) (b' := sp + 2576#64) (n := 128) (k := (1152 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 13984#64) (b' := sp + 14112#64) (n := 128) (k := (1408 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 16208#64) (b' := sp + 16307#64) (n := 99) (k := (29 : Nat)) rfl (by bv_omega) (by decide)]
  exact Entails.trans (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono (hp (shake256List_length 128 _))
      (sepConj_mono (hp (shake256List_length 128 _))
        (sepConj_mono_left (hp (shake256List_length 128 _))))))) (by sep_frame)

private def RestSeg5 (s0 : State) (sp : BitVec 64) (a : MlkemBlk03Args) : SepProp :=
  let hashed := sha3_512List (a.rand ++ a.hdr64.drop 32)
  let coins := hashed.drop 32
  let prf6 := shake256List 128 (coins ++ [6#8])
  SavedArgs03 sp a ∗ SavedFrame03 (s0.sp - 160#64) s0 ∗
  (a.hdrA ↦ₛ a.hdr64) ∗ (a.randA ↦ₛ a.rand) ∗
  memRegion a.ret 961 ∗ memRegion a.esA 2080 ∗ memRegion a.ssA 32 ∗
  memRegion (sp + 40#64) 1208 ∗
  PolyMem (sp + 1248#64) (fun i => polyVecNat (neonCbd2Poly16 prf6) (31 - i)) ∗
  memRegion (sp + 3728#64) 544 ∗ memRegion (sp + 4784#64) 1984 ∗
  ((sp + 6768#64) ↦ₛ hashed) ∗ memRegion (sp + 11440#64) 960 ∗
  memRegion (sp + 12400#64) 33 ∗ memRegion (sp + 12433#64) 15 ∗
  memRegion (sp + 15520#64) 128 ∗ memRegion (sp + 15648#64) 32 ∗
  memRegion (sp + 15680#64) 128 ∗ memRegion (sp + 15808#64) 392 ∗
  memRegion (sp + 16200#64) 8 ∗ memRegion (sp + 16208#64) 128 ∗
  memRegion (sp + 16336#64) 192 ∗ memRegion (sp + 16528#64) 128 ∗
  memRegion (sp + 16656#64) 192 ∗ memRegion (sp + 16848#64) 16 ∗ stackAt sp 1136

private def RestSeg6 (sp : BitVec 64) (a : MlkemBlk03Args) : SepProp :=
  memRegion (sp + 40#64) 1208 ∗ memRegion (sp + 1760#64) 368 ∗
  memRegion (sp + 7792#64) 3648 ∗ memRegion (sp + 12400#64) 33 ∗
  memRegion (sp + 12433#64) 15 ∗ memRegion (sp + 14016#64) 480 ∗
  memRegion (sp + 14496#64) 512 ∗ memRegion (sp + 15008#64) 512 ∗
  memRegion (sp + 15520#64) 128 ∗ memRegion (sp + 15648#64) 32 ∗
  memRegion (sp + 16200#64) 8 ∗ memRegion (sp + 16848#64) 16 ∗
  stackAt sp 1136 ∗ (a.hdrA ↦ₛ a.hdr64)

private theorem seg5_to_seg6_entails (s0 : State) (sp : BitVec 64) (a : MlkemBlk03Args) :
    let rho := a.hdr64.take 32
    let hashed := sha3_512List (a.rand ++ a.hdr64.drop 32)
    let coins := hashed.drop 32
    let prf0 := shake256List 128 (coins ++ [0#8])
    let prf1 := shake256List 128 (coins ++ [1#8])
    let prf2 := shake256List 128 (coins ++ [2#8])
    let prf6 := shake256List 128 (coins ++ [6#8])
    let e1_0 := neonCbd2Poly16 (shake256List 128 (coins ++ [3#8]))
    let e1_1 := neonCbd2Poly16 (shake256List 128 (coins ++ [4#8]))
    let e1_2 := neonCbd2Poly16 (shake256List 128 (coins ++ [5#8]))
    PolyMem (sp + 2192#64) (polyVecNat (uVecPoly16 rho coins 0)) ∗
      PolyMem (sp + 2704#64) (polyVecNat (uVecPoly16 rho coins 1)) ∗
      PolyMem (sp + 3216#64) (polyVecNat (uVecPoly16 rho coins 2)) ∗
      ATransMem sp rho ∗
      PolyMem (sp + 12448#64) (polyVecNat (rHatPoly16 prf0)) ∗
      PolyMem (sp + 12960#64) (polyVecNat (rHatPoly16 prf1)) ∗
      PolyMem (sp + 13472#64) (polyVecNat (rHatPoly16 prf2)) ∗
      PolyMem (sp + 13984#64) (polyVecNat e1_0) ∗
      PolyMem (sp + 14496#64) (polyVecNat e1_1) ∗
      PolyMem (sp + 15008#64) (polyVecNat e1_2) ∗
      memRegion (sp + 1760#64) 432 ∗ memRegion (sp + 4272#64) 512 ∗
      RestSeg5 s0 sp a ⊢
    SavedArgs03 sp a ∗ SavedFrame03 (s0.sp - 160#64) s0 ∗
      (a.randA ↦ₛ a.rand) ∗ memRegion a.ret 961 ∗ memRegion a.esA 2080 ∗ memRegion a.ssA 32 ∗
      PolyMem (sp + 1248#64) (fun i => polyVecNat (neonCbd2Poly16 prf6) (31 - i)) ∗
      memRegion (sp + 2128#64) 64 ∗
      PolyMem (sp + 2192#64) (polyVecNat (uVecPoly16 rho coins 0)) ∗
      PolyMem (sp + 2704#64) (polyVecNat (uVecPoly16 rho coins 1)) ∗
      PolyMem (sp + 3216#64) (polyVecNat (uVecPoly16 rho coins 2)) ∗
      memRegion (sp + 3728#64) 544 ∗ memRegion (sp + 4272#64) 2496 ∗
      ((sp + 6768#64) ↦ₛ hashed) ∗ memRegion (sp + 6832#64) 960 ∗
      memRegion (sp + 11440#64) 960 ∗
      PolyMem (sp + 12448#64) (polyVecNat (rHatPoly16 prf0)) ∗
      PolyMem (sp + 12960#64) (polyVecNat (rHatPoly16 prf1)) ∗
      PolyMem (sp + 13472#64) (polyVecNat (rHatPoly16 prf2)) ∗
      memRegion (sp + 13984#64) 32 ∗ memRegion (sp + 15680#64) 520 ∗
      memRegion (sp + 16208#64) 640 ∗ RestSeg6 sp a := by
  intro rho hashed coins prf0 prf1 prf2 prf6 e1_0 e1_1 e1_2
  dsimp only [RestSeg5, RestSeg6]
  have hp (p : BitVec 64) (f : Nat → BitVec 128) : PolyMem p f ⊢ memRegion p 512 :=
    vecRangeMem_entails_memRegion 32 p f
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono (aTransMem_entails sp rho) (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono (hp _ _) (sepConj_mono (hp _ _) (sepConj_mono_left (hp _ _))))))))))) ?_
  rw [memRegion_split' (b := sp + 6832#64) (b' := sp + 7792#64) (n := 960) (k := (3648 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 13984#64) (b' := sp + 14016#64) (n := 32) (k := (480 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 1760#64) (b' := sp + 2128#64) (n := 368) (k := (64 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 4272#64) (b' := sp + 4784#64) (n := 512) (k := (1984 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 15680#64) (b' := sp + 15808#64) (n := 128) (k := (392 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 16208#64) (b' := sp + 16336#64) (n := 128) (k := (512 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 16336#64) (b' := sp + 16528#64) (n := 192) (k := (320 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 16528#64) (b' := sp + 16656#64) (n := 128) (k := (192 : Nat)) rfl (by bv_omega) (by decide)]
  sep_frame

private theorem seg6_to_stackAt18160 (s0 : State) (a : MlkemBlk03Args) :
    let sp := s0.sp - BitVec.ofNat 64 17024
    (a.randA ↦ₛ a.rand) ∗ (a.ret ↦₈ 0#8) ∗
      ((a.ret + 1#64) ↦ₛ encaps1OutCt1 a.hdr64 a.rand) ∗
      (a.esA ↦ₛ encaps1OutEs a.hdr64 a.rand) ∗
      (a.ssA ↦ₛ encaps1OutSs a.hdr64 a.rand) ∗
      memRegion sp 40 ∗ memRegion (sp + 1248#64) 512 ∗
      memRegion (sp + 2128#64) 5664 ∗ memRegion (sp + 11440#64) 960 ∗
      memRegion (sp + 12448#64) 1568 ∗ memRegion (sp + 15680#64) 520 ∗
      memRegion (sp + 16208#64) 640 ∗ memRegion (s0.sp - 160#64) 160 ∗ RestSeg6 sp a ⊢
    (a.hdrA ↦ₛ a.hdr64) ∗ (a.randA ↦ₛ a.rand) ∗
      (a.ret ↦₈ 0#8) ∗ ((a.ret + 1#64) ↦ₛ encaps1OutCt1 a.hdr64 a.rand) ∗
      (a.esA ↦ₛ encaps1OutEs a.hdr64 a.rand) ∗
      (a.ssA ↦ₛ encaps1OutSs a.hdr64 a.rand) ∗
      stackAt s0.sp 18160 := by
  intro sp
  dsimp only [RestSeg6]
  unfold stackAt
  have hbase : s0.sp - BitVec.ofNat 64 18160 = sp - BitVec.ofNat 64 1136 := by
    dsimp only [sp]; bv_omega
  rw [hbase,
    memRegion_split' (b' := sp) (n := (1136 : Nat)) (k := (17024 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp) (b' := sp + 40#64) (n := 40) (k := (16984 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 1248#64) (n := (1208 : Nat)) (k := (15776 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 1760#64) (n := 512) (k := (15264 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 2128#64) (n := 368) (k := (14896 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 7792#64) (n := (5664 : Nat)) (k := (9232 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 11440#64) (n := (3648 : Nat)) (k := (5584 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 12400#64) (n := 960) (k := (4624 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 12433#64) (n := 33) (k := (4591 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 12448#64) (n := 15) (k := (4576 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 14016#64) (n := (1568 : Nat)) (k := (3008 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 14496#64) (n := 480) (k := (2528 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 15008#64) (n := 512) (k := (2016 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 15520#64) (n := 512) (k := (1504 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 15648#64) (n := 128) (k := (1376 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 15680#64) (n := 32) (k := (1344 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 16200#64) (n := 520) (k := (824 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 16208#64) (n := 8) (k := (816 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 16848#64) (n := 640) (k := (176 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := s0.sp - 160#64) (n := 16) (k := (160 : Nat)) rfl (by dsimp only [sp]; bv_omega) (by decide)]
  sep_frame

private theorem blk03_postSeg2_wp [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s0 s2 : State) (a : MlkemBlk03Args) (R P2 : SepProp)
    (hhdr : a.hdr64.length = 64) (hrand : a.rand.length = 32)
    (hsp0 : s0.spAligned = true)
    (hexit : Seg2Exit b (s0.sp - BitVec.ofNat 64 17024) (a.hdr64.take 32)
      (Seg2Preserved s0 a emp) s2 P2) :
    SepWP (blkPC03.rebase b (fun _ => none)) (s0.readReg64 .lr) s2 P2
      (fun sf Pf =>
        (sf.mem ⊨ Pf ∗ R → sf.mem ⊨ mlkemBlk03RawSpec.post a s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  rcases hexit with ⟨hpc2, hrun2, hcl2, hro2, hreg2, _, hP2⟩
  set sp := s0.sp - BitVec.ofNat 64 17024
  set hashed := sha3_512List (a.rand ++ a.hdr64.drop 32)
  have hh_len : hashed.length = 64 := sha3_512List_length _
  have hc_len : (hashed.drop 32).length = 32 := by simp [hashed, hh_len]
  have hc_take : (hashed.drop 32).take 32 = hashed.drop 32 :=
    List.take_of_length_le (Nat.le_of_eq hc_len)
  refine SepWP.weaken_pre (Entails.trans hP2 (seg2_to_seg3_entails s0 a))
    (sepWP_seq_env hcl2 hro2
      (seg3_ok hb hbase s2 sp hashed (RestSeg3 s0 sp a) hh_len
        hpc2 hrun2 hreg2.1 hreg2.2.1 hcl2 hro2) ?_)
  rintro s3 P3 hpc3 hrun3 hcl3 hro3 ⟨hsp3, hspA3, hx19_3, _, _, _, _, hP3⟩
  refine SepWP.weaken_pre (Entails.trans hP3 (seg3_to_seg4_entails s0 sp a))
    (sepWP_seq_env hcl3 hro3
      (seg4_ok hb hbase s3 sp (hashed.drop 32) 0#8 (RestSeg4 s0 sp a) hc_len
        hpc3 hrun3 hsp3 hspA3 hx19_3 hcl3 hro3) ?_)
  rintro s4 P4 hpc4 hrun4 hcl4 hro4 ⟨hsp4, hspA4, hx19_4, _, _, hP4⟩
  refine SepWP.weaken_pre (Entails.trans hP4 (by dsimp only [RestSeg4, RestSeg5]; sep_frame))
    (sepWP_seq_env hcl4 hro4
      (seg5_ok hb s4 sp (a.hdr64.take 32) (hashed.drop 32) (RestSeg5 s0 sp a)
        hpc4 hrun4 hsp4 hspA4 hx19_4 hcl4 hro4) ?_)
  rintro s5 P5 hpc5 hrun5 hcl5 hro5 ⟨hsp5, hspA5, _, _, hP5⟩
  have h6 := seg6_ok hb hbase s0 s5 sp a (RestSeg6 sp a) hhdr hrand
    (by simpa [State.spAligned] using hsp0) hpc5 hrun5 hsp5 rfl hspA5 hcl5 hro5
  dsimp only at h6
  rw [hc_take] at h6
  refine SepWP.weaken_pre (Entails.trans hP5 (seg5_to_seg6_entails s0 sp a))
    (SepWP.mono h6 fun sf Pf _ _ ⟨hspf, hcs, hPf⟩ => ⟨fun hm => ?_, hspf, hcs⟩)
  have hm1 := Satisfies.mono (sepConj_mono_left (Entails.trans hPf (seg6_to_stackAt18160 s0 a))) hm
  dsimp only [mlkemBlk03RawSpec]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨encaps1Out_lengths hhdr hrand, Satisfies.mono (by sep_frame) hm1⟩

theorem blk03_encaps1_raw_safe_ok :
    MlKemBlockSafeOk 3 (fun mpl => withMlKemRoOk mpl mlkemBlk03RawSpec) := by
  intro _
  refine mlkemSafeCaller_ok blkPC03 blkPl03 rfl rfl fun b hb hbase => ?_
  apply safe_subroutine_ok_of_safeSepWP
  intro a R s0 hpc hrun hpre hsp0
  dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, withMlKemRoOk,
    mlkemBlk03RawSpec] at hpre ⊢
  rw [sepConj_comm _ ⌜mlkemMultiLib.CodeLoaded mlkemMpl s0.mem⌝, sepConj_assoc,
      satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hro0, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hhdr, hrand⟩, hspat⟩ := hpre
  have hrho : (a.hdr64.take 32).length = 32 := by simp [hhdr]
  refine ⟨(a.hdrA ↦ₛ a.hdr64) ∗ (a.randA ↦ₛ a.rand) ∗ memRegion a.ret 961 ∗
      memRegion a.esA 2080 ∗ memRegion a.ssA 32 ∗ stackAt s0.sp 18160 ∗ emp,
    Satisfies.mono (by sep_frame) hspat, ?_⟩
  refine safeSepWP_seq_env hcl0 hro0
    (seg1_wp hb hbase s0 a emp hhdr hrand hpc hrun hsp0 hcl0 hro0 hx0 hx1 hx2 hx3 hx4 hx5 hx6) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hreg1, hx8_1, hP1⟩
  refine SafeSepWP.weaken_pre
    (SafeSepWP.bind (seg2_safeSepWP hb hbase hrho hpc1 hrun1 hcl1 hro1 hreg1 hx8_1)
      fun s2 P2 hexit => SafeSepWP.ret_of_sepWP
        (spec := mlkemMultiLib.withCodeLoaded mlkemMpl (withMlKemRoOk mlkemMpl mlkemBlk03RawSpec))
        (blk03_postSeg2_wp hb hbase s0 s2 a R P2 hhdr hrand hsp0 hexit))
    hP1

theorem blk03_encaps1_safe_ok : MlKemBlockSafeOk 3 mlkemBlk03CoreSpec :=
  mlkemBlockSafeOk_withNonSyscallPreserved (j := 3)
    (spec := fun mpl => withMlKemRoOk mpl mlkemBlk03RawSpec)
    blk03_encaps1_raw_safe_ok (by decide)
    (h_pre := fun mpl _a _R _s0 h => by
      dsimp only [withMlKemRoOk, mlkemBlk03RawSpec] at h ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
      refine ⟨mlkemRoOk_stripExecOutside (mlkemKeep mpl) h.1, ?_⟩
      simpa only [stripS_readReg64, stripS_sp] using h.2)
    (h_post := fun _mpl _a _R _s0 _sf _ h => by
      dsimp only [withMlKemRoOk, mlkemBlk03RawSpec] at h ⊢
      simpa only [stripS_sp] using h)

theorem blk03_encaps1_raw_ok :
    MlKemBlockOk 3 (fun mpl => withMlKemRoOk mpl mlkemBlk03TermRawSpec) := by
  intro _
  refine mlkemCaller_ok blkPC03 blkPl03 rfl rfl fun b hb hbase => ?_
  apply subroutine_ok_of_sepWP_init
  intro a R s0 hpc hrun hpre hsp0
  dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, withMlKemRoOk,
    mlkemBlk03TermRawSpec, mlkemBlk03RawSpec] at hpre ⊢
  rw [sepConj_comm _ ⌜mlkemMultiLib.CodeLoaded mlkemMpl s0.mem⌝, sepConj_assoc,
      satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hro0, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hTerm, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hhdr, hrand⟩, hspat⟩ := hpre
  have hrho : (a.hdr64.take 32).length = 32 := by simp [hhdr]
  refine ⟨(a.hdrA ↦ₛ a.hdr64) ∗ (a.randA ↦ₛ a.rand) ∗ memRegion a.ret 961 ∗
      memRegion a.esA 2080 ∗ memRegion a.ssA 32 ∗ stackAt s0.sp 18160 ∗ emp,
    Satisfies.mono (by sep_frame) hspat, ?_⟩
  refine sepWP_seq_env hcl0 hro0
    (seg1_wp hb hbase s0 a emp hhdr hrand hpc hrun hsp0 hcl0 hro0 hx0 hx1 hx2 hx3 hx4 hx5 hx6) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hreg1, hx8_1, hP1⟩
  refine SepWP.weaken_pre hP1
    (SepWP.seq (seg2_sepWP hb hbase hrho hTerm hpc1 hrun1 hcl1 hro1 hreg1 hx8_1) ?_)
  rintro s2 P2 _ _ hexit
  exact blk03_postSeg2_wp hb hbase s0 s2 a R P2 hhdr hrand hsp0 hexit

theorem blk03_encaps1_ok : MlKemBlockOk 3 mlkemBlk03TermCoreSpec :=
  mlkemBlockOk_withNonSyscallPreserved (j := 3)
    (spec := fun mpl => withMlKemRoOk mpl mlkemBlk03TermRawSpec)
    blk03_encaps1_raw_ok (by decide)
    (h_pre := fun mpl _a _R _s0 h => by
      dsimp only [withMlKemRoOk, mlkemBlk03TermRawSpec, mlkemBlk03RawSpec] at h ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
      refine ⟨mlkemRoOk_stripExecOutside (mlkemKeep mpl) h.1, ?_⟩
      simpa only [stripS_readReg64, stripS_sp] using h.2)
    (h_post := fun _mpl _a _R _s0 _sf _ h => by
      dsimp only [withMlKemRoOk, mlkemBlk03TermRawSpec, mlkemBlk03RawSpec] at h ⊢
      simpa only [stripS_sp] using h)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Blk03
