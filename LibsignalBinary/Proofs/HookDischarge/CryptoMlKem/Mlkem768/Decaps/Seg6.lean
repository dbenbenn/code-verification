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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg6b -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg6d -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SpillMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg6a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg6c

/-!
# `decapsulate_compressed_key` (`B04`) — Segment 6 Composition (`+0x7134 → +0x8d00`)

Composes `Seg6b` (`rHat[0..2]`), `Seg6c` (`e1[0..2]`), and `Seg6d` (`e2` + zeroed `u'[0..2]`)
from `Seg5Spatial` into `Seg6Spatial`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg6

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  indCpaDecrypt sha3_512List shake256List)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd (neonCbd2Poly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a (sha3_512List_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd (shake256List_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  PolyMem Spill13Mem polyVecNat spill13Mem_entails_memRegion)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base (
  SavedFrame04 blkPC04 blkPl04)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SpillMem (
  Spill21Mem Spill6Mem spill21Mem_entails_memRegion spill6Mem_entails_memRegion)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure (
  WordRangeMem modTHatPoly16 msgWordFn)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5 (
  ATransMemAt Seg5Spatial offSeg5End)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg6a (
  fwd2Spill13 fwd2Spill6 offSeg6Start setFwd2Spill21)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg6b (
  rHatPoly16 seg6_rhat_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg6c (seg6c_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg6d (
  offSeg7Start seg6d_ok)

attribute [local irreducible] blkPC04 sha3_512List shake256List neonCbd2Poly16 polyVecNat rHatPoly16

@[expose] noncomputable def Seg6Spatial (s0 : State) (ret dkA ct1A ct2A : BitVec 64)
    (dk ct1 ct2 : List (BitVec 8)) (F : SepProp) : SepProp :=
  let sp := s0.sp - 25824#64
  let ct := ct1 ++ ct2
  let m' := indCpaDecrypt 3 10 4 (dk.take 1152) ct
  let rho := (dk.drop 2304).take 32
  let hPk := (dk.drop 2336).take 32
  let z := (dk.drop 2368).take 32
  let pk0 := (dk.drop 1152).take 384
  let pk1 := (dk.drop 1536).take 384
  let pk2 := (dk.drop 1920).take 384
  let coins := (sha3_512List (m' ++ hPk)).drop 32
  let prf0 := shake256List 128 (coins ++ [0#8])
  let prf1 := shake256List 128 (coins ++ [1#8])
  let prf2 := shake256List 128 (coins ++ [2#8])
  let prf3 := shake256List 128 (coins ++ [3#8])
  let prf4 := shake256List 128 (coins ++ [4#8])
  let prf5 := shake256List 128 (coins ++ [5#8])
  let prf6 := shake256List 128 (coins ++ [6#8])
  stackAt sp 1136 ∗ SavedFrame04 s0.sp s0 ∗
  memRegion sp 8 ∗ WordRangeMem 32 (sp + 8#64) (msgWordFn m') ∗
  ((sp + 136#64) ↦₆₄ ret) ∗
  memRegion (sp + 144#64) 1168 ∗
  PolyMem (sp + 1312#64) (polyVecNat (neonCbd2Poly16 prf6)) ∗
  memRegion (sp + 1824#64) 432 ∗
  ((sp + 2256#64) ↦ₛ ct) ∗ ((sp + 3344#64) ↦ₛ ct) ∗ memRegion (sp + 4432#64) 64 ∗
  ((sp + 4496#64) ↦ₛ sha3_512List (m' ++ hPk)) ∗
  memRegion (sp + 4560#64) 1120 ∗
  PolyMem (sp + 5680#64) (polyVecNat (modTHatPoly16 pk0)) ∗
  PolyMem (sp + 6192#64) (polyVecNat (modTHatPoly16 pk1)) ∗
  PolyMem (sp + 6704#64) (polyVecNat (modTHatPoly16 pk2)) ∗
  ATransMemAt sp 7216 rho ∗
  memRegion (sp + 11824#64) 7344 ∗
  PolyMem (sp + 19168#64) (polyVecNat (rHatPoly16 prf0)) ∗
  PolyMem (sp + 19680#64) (polyVecNat (rHatPoly16 prf1)) ∗
  PolyMem (sp + 20192#64) (polyVecNat (rHatPoly16 prf2)) ∗
  PolyMem (sp + 20704#64) (polyVecNat (neonCbd2Poly16 prf3)) ∗
  PolyMem (sp + 21216#64) (polyVecNat (neonCbd2Poly16 prf4)) ∗
  PolyMem (sp + 21728#64) (polyVecNat (neonCbd2Poly16 prf5)) ∗
  memRegion (sp + 22240#64) 160 ∗
  PolyMem (sp + 22400#64) (fun _ => 0#128) ∗
  PolyMem (sp + 22912#64) (fun _ => 0#128) ∗
  PolyMem (sp + 23424#64) (fun _ => 0#128) ∗
  memRegion (sp + 23936#64) 1680 ∗
  ((sp + 25616#64) ↦ₛ shake256List 32 (z ++ ct)) ∗
  memRegion (sp + 25648#64) 16 ∗
  (dkA ↦ₛ dk) ∗ (ct1A ↦ₛ ct1) ∗ (ct2A ↦ₛ ct2) ∗ F

private theorem split_144_2112 (sp : BitVec 64) :
    memRegion (sp + 144#64) 2112 =
      memRegion (sp + 144#64) 1168 ∗ memRegion (sp + 1312#64) 304 ∗
        memRegion (sp + 1616#64) 640 := by
  rw [memRegion_split' (b := sp + 144#64) (b' := sp + 1312#64) (n := 1168) (k := (944 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 1312#64) (b' := sp + 1616#64) (n := 304) (k := (640 : Nat))
        rfl (by bv_omega) (by decide)]

private theorem split_11824_7344 (sp : BitVec 64) :
    memRegion (sp + 11824#64) 7344 =
      memRegion (sp + 11856#64) 512 ∗ memRegion (sp + 18032#64) 1088 ∗
      memRegion (sp + 19120#64) 33 ∗
      (memRegion (sp + 11824#64) 32 ∗ memRegion (sp + 12368#64) 5664 ∗
        memRegion (sp + 19153#64) 15) := by
  rw [memRegion_split' (b := sp + 11824#64) (b' := sp + 11856#64) (n := 32) (k := (7312 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 11856#64) (b' := sp + 12368#64) (n := 512) (k := (6800 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 12368#64) (b' := sp + 18032#64) (n := 5664) (k := (1136 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 18032#64) (b' := sp + 19120#64) (n := 1088) (k := (48 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 19120#64) (b' := sp + 19153#64) (n := 33) (k := (15 : Nat)) rfl (by bv_omega) (by decide)]
  apply sepProp_ext <;> sep_frame

private theorem split_23936_1680 (sp : BitVec 64) :
    memRegion (sp + 23936#64) 1680 =
      memRegion (sp + 24448#64) 128 ∗ memRegion (sp + 24976#64) 128 ∗
      memRegion (sp + 25296#64) 128 ∗
      (memRegion (sp + 23936#64) 512 ∗ memRegion (sp + 24576#64) 400 ∗
        memRegion (sp + 25104#64) 192 ∗ memRegion (sp + 25424#64) 192) := by
  rw [memRegion_split' (b := sp + 23936#64) (b' := sp + 24448#64) (n := 512) (k := (1168 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 24448#64) (b' := sp + 24576#64) (n := 128) (k := (1040 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 24576#64) (b' := sp + 24976#64) (n := 400) (k := (640 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 24976#64) (b' := sp + 25104#64) (n := 128) (k := (512 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 25104#64) (b' := sp + 25296#64) (n := 192) (k := (320 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 25296#64) (b' := sp + 25424#64) (n := 128) (k := (192 : Nat)) rfl (by bv_omega) (by decide)]
  apply sepProp_ext <;> sep_frame

private theorem split_11824_13792 (sp : BitVec 64) :
    memRegion (sp + 11824#64) 13792 =
      memRegion (sp + 11824#64) 7344 ∗ memRegion (sp + 19168#64) 1536 ∗
      memRegion (sp + 20704#64) 1536 ∗ memRegion (sp + 22240#64) 160 ∗
      memRegion (sp + 22400#64) 1536 ∗ memRegion (sp + 23936#64) 1680 := by
  rw [memRegion_split' (b := sp + 11824#64) (b' := sp + 19168#64) (n := 7344) (k := (6448 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 19168#64) (b' := sp + 20704#64) (n := 1536) (k := (4912 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 20704#64) (b' := sp + 22240#64) (n := 1536) (k := (3376 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 22240#64) (b' := sp + 22400#64) (n := 160) (k := (3216 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 22400#64) (b' := sp + 23936#64) (n := 1536) (k := (1680 : Nat)) rfl (by bv_omega) (by decide)]

private theorem prfs012_entails_384 (sp : BitVec 64) {p0 p1 p2 : List (BitVec 8)}
    (h0 : p0.length = 128) (h1 : p1.length = 128) (h2 : p2.length = 128) :
    ((sp + 22400#64) ↦ₛ p0) ∗ ((sp + 22528#64) ↦ₛ p1) ∗ ((sp + 22656#64) ↦ₛ p2) ⊢
      memRegion (sp + 22400#64) 384 := by
  rw [memRegion_split' (b' := sp + 22528#64) (n := 128) (k := (256 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp + 22656#64) (n := 128) (k := (128 : Nat)) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (by simpa [h0] using pointsToBytes_entails_memRegion (sp + 22400#64) p0)
    (sepConj_mono (by simpa [h1] using pointsToBytes_entails_memRegion (sp + 22528#64) p1)
      (by simpa [h2] using pointsToBytes_entails_memRegion (sp + 22656#64) p2))

private theorem seg6_core_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) (hashed : List (BitVec 8)) (Rest : SepProp)
    (hh : hashed.length = 64)
    (hpc : s.pc = b + offSeg6Start) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 11856#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hro : MlKemRoOk mlkemMpl s.mem) :
    let coins := hashed.drop 32
    let prf0 := shake256List 128 (coins ++ [0#8])
    let prf1 := shake256List 128 (coins ++ [1#8])
    let prf2 := shake256List 128 (coins ++ [2#8])
    let prf3 := shake256List 128 (coins ++ [3#8])
    let prf4 := shake256List 128 (coins ++ [4#8])
    let prf5 := shake256List 128 (coins ++ [5#8])
    let prf6 := shake256List 128 (coins ++ [6#8])
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg7Start) s
      (((sp + 4496#64) ↦ₛ hashed) ∗ memRegion (sp + 1312#64) 304 ∗
       memRegion (sp + 1616#64) 640 ∗ memRegion (sp + 11824#64) 13792 ∗
       stackAt sp 1136 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readReg64 .x19 = 1536#64 ∧
        sf.readReg64 .x20 = sp + 22400#64 ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        (Pf ⊢ ((sp + 4496#64) ↦ₛ hashed) ∗
          PolyMem (sp + 1312#64) (polyVecNat (neonCbd2Poly16 prf6)) ∗
          memRegion (sp + 1824#64) 432 ∗
          memRegion (sp + 11824#64) 7344 ∗
          PolyMem (sp + 19168#64) (polyVecNat (rHatPoly16 prf0)) ∗
          PolyMem (sp + 19680#64) (polyVecNat (rHatPoly16 prf1)) ∗
          PolyMem (sp + 20192#64) (polyVecNat (rHatPoly16 prf2)) ∗
          PolyMem (sp + 20704#64) (polyVecNat (neonCbd2Poly16 prf3)) ∗
          PolyMem (sp + 21216#64) (polyVecNat (neonCbd2Poly16 prf4)) ∗
          PolyMem (sp + 21728#64) (polyVecNat (neonCbd2Poly16 prf5)) ∗
          memRegion (sp + 22240#64) 160 ∗
          PolyMem (sp + 22400#64) (fun _ => 0#128) ∗
          PolyMem (sp + 22912#64) (fun _ => 0#128) ∗
          PolyMem (sp + 23424#64) (fun _ => 0#128) ∗
          memRegion (sp + 23936#64) 1680 ∗
          stackAt sp 1136 ∗ Rest)) := by
  intro coins prf0 prf1 prf2 prf3 prf4 prf5 prf6
  have hc : coins.length = 32 := by simp [coins, hh]
  rw [split_11824_13792 sp, split_11824_7344 sp, split_23936_1680 sp,
      memRegion_split' (b := sp + 20704#64) (b' := sp + 20832#64) (n := 128) (k := (1408 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 22400#64) (b' := sp + 22784#64) (n := 384) (k := (1152 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 24976#64) (b' := sp + 25075#64) (n := 99) (k := (29 : Nat)) rfl (by bv_omega) (by decide)]
  refine SepWP.weaken_pre
    (P' := ((sp + 4496#64) ↦ₛ hashed) ∗ memRegion (sp + 1616#64) 640 ∗
      memRegion (sp + 11856#64) 512 ∗ memRegion (sp + 18032#64) 1088 ∗
      memRegion (sp + 19120#64) 33 ∗ memRegion (sp + 19168#64) 1536 ∗
      memRegion (sp + 20704#64) 128 ∗ memRegion (sp + 22400#64) 384 ∗
      memRegion (sp + 24448#64) 128 ∗ memRegion (sp + 24976#64) 99 ∗
      memRegion (sp + 25296#64) 128 ∗ stackAt sp 1136 ∗
      (memRegion (sp + 1312#64) 304 ∗
        (memRegion (sp + 11824#64) 32 ∗ memRegion (sp + 12368#64) 5664 ∗ memRegion (sp + 19153#64) 15) ∗
        memRegion (sp + 20832#64) 1408 ∗ memRegion (sp + 22240#64) 160 ∗
        memRegion (sp + 22784#64) 1152 ∗ memRegion (sp + 25075#64) 29 ∗
        (memRegion (sp + 23936#64) 512 ∗ memRegion (sp + 24576#64) 400 ∗
          memRegion (sp + 25104#64) 192 ∗ memRegion (sp + 25424#64) 192) ∗ Rest))
    (by sep_frame) ?_
  refine sepWP_seq_env hcl hro
    (seg6_rhat_ok hb hbase s sp hashed _ hh hpc hrun hsp hspA hx19 hx20 hcl hro) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hfp1, hx19_1, t21, hP1⟩
  refine SepWP.weaken_pre hP1 ?_
  have hm20704 : memRegion (sp + 20704#64) 128 ∗ memRegion (sp + 20832#64) 1408 =
      memRegion (sp + 20704#64) 1536 :=
    (memRegion_split' (b := sp + 20704#64) (b' := sp + 20832#64) (n := 128) (k := (1408 : Nat)) rfl (by bv_omega) (by decide)).symm
  have hm24976 : memRegion (sp + 24976#64) 99 ∗ memRegion (sp + 25075#64) 29 =
      memRegion (sp + 24976#64) 128 :=
    (memRegion_split' (b := sp + 24976#64) (b' := sp + 25075#64) (n := 99) (k := (29 : Nat)) rfl (by bv_omega) (by decide)).symm
  have hm384 := prfs012_entails_384 sp (p0 := prf0) (p1 := prf1) (p2 := prf2)
    (shake256List_length 128 _) (shake256List_length 128 _) (shake256List_length 128 _)
  have hm1312 : memRegion (sp + 1312#64) 304 ∗ Spill13Mem (sp + 1616#64) fwd2Spill13 ⊢
      memRegion (sp + 1312#64) 512 := by
    rw [memRegion_split' (b := sp + 1312#64) (b' := sp + 1616#64) (n := 304) (k := (208 : Nat)) rfl (by bv_omega) (by decide)]
    exact sepConj_mono (Entails.refl _) (spill13Mem_entails_memRegion _ _)
  have hm1824 : Spill6Mem (sp + 1824#64) fwd2Spill6 ∗ Spill21Mem (sp + 1920#64) (setFwd2Spill21 t21) ⊢
      memRegion (sp + 1824#64) 432 := by
    rw [memRegion_split' (b := sp + 1824#64) (b' := sp + 1920#64) (n := 96) (k := (336 : Nat)) rfl (by bv_omega) (by decide)]
    exact sepConj_mono (spill6Mem_entails_memRegion _ _) (spill21Mem_entails_memRegion _ _)
  refine SepWP.weaken_pre
    (P' := ((sp + 19120#64) ↦ₛ coins) ∗
      memRegion (sp + 11856#64) 512 ∗ memRegion (sp + 20704#64) 1536 ∗
      memRegion (sp + 22240#64) 99 ∗ memRegion (sp + 22400#64) 384 ∗
      memRegion (sp + 24448#64) 128 ∗ memRegion (sp + 24976#64) 128 ∗
      memRegion (sp + 25296#64) 128 ∗ stackAt sp 1136 ∗
      (((sp + 4496#64) ↦ₛ hashed) ∗ ((sp + 19152#64) ↦₈ 0#8) ∗
        memRegion (sp + 1312#64) 512 ∗ memRegion (sp + 1824#64) 432 ∗
        memRegion (sp + 18032#64) 1088 ∗
        PolyMem (sp + 19168#64) (polyVecNat (rHatPoly16 prf0)) ∗
        PolyMem (sp + 19680#64) (polyVecNat (rHatPoly16 prf1)) ∗
        PolyMem (sp + 20192#64) (polyVecNat (rHatPoly16 prf2)) ∗
        memRegion (sp + 22339#64) 29 ∗ memRegion (sp + 22368#64) 32 ∗
        memRegion (sp + 22784#64) 1152 ∗
        (memRegion (sp + 11824#64) 32 ∗ memRegion (sp + 12368#64) 5664 ∗ memRegion (sp + 19153#64) 15) ∗
        (memRegion (sp + 23936#64) 512 ∗ memRegion (sp + 24576#64) 400 ∗
          memRegion (sp + 25104#64) 192 ∗ memRegion (sp + 25424#64) 192) ∗ Rest))
    (by
      rw [memRegion_split' (b := sp + 22240#64) (b' := sp + 22339#64) (n := 99) (k := (61 : Nat)) rfl (by bv_omega) (by decide),
          memRegion_split' (b := sp + 22339#64) (b' := sp + 22368#64) (n := 29) (k := (32 : Nat)) rfl (by bv_omega) (by decide),
          ← hm20704, ← hm24976]
      let Tail1 := ((sp + 4496#64) ↦ₛ hashed) ∗ memRegion (sp + 11856#64) 512 ∗
        memRegion (sp + 18032#64) 1088 ∗ ((sp + 19120#64) ↦ₛ coins) ∗ ((sp + 19152#64) ↦₈ 0#8) ∗
        PolyMem (sp + 19168#64) (polyVecNat (rHatPoly16 prf0)) ∗
        PolyMem (sp + 19680#64) (polyVecNat (rHatPoly16 prf1)) ∗
        PolyMem (sp + 20192#64) (polyVecNat (rHatPoly16 prf2)) ∗
        (memRegion (sp + 20704#64) 128 ∗ memRegion (sp + 20832#64) 1408) ∗
        memRegion (sp + 24448#64) 128 ∗
        (memRegion (sp + 24976#64) 99 ∗ memRegion (sp + 25075#64) 29) ∗
        memRegion (sp + 25296#64) 128 ∗ stackAt sp 1136 ∗
        (memRegion (sp + 11824#64) 32 ∗ memRegion (sp + 12368#64) 5664 ∗ memRegion (sp + 19153#64) 15) ∗
        (memRegion (sp + 22240#64) 99 ∗ memRegion (sp + 22339#64) 29 ∗ memRegion (sp + 22368#64) 32) ∗
        memRegion (sp + 22784#64) 1152 ∗
        (memRegion (sp + 23936#64) 512 ∗ memRegion (sp + 24576#64) 400 ∗
          memRegion (sp + 25104#64) 192 ∗ memRegion (sp + 25424#64) 192) ∗ Rest
      have hmAll := sepConj_mono hm1312 (sepConj_mono hm1824 hm384)
      exact Entails.trans (by sep_frame)
        (Entails.trans (sepConj_mono_left (Q := Tail1) hmAll) (by sep_frame))) ?_
  refine sepWP_seq_env hcl1 hro1
    (seg6c_ok hb hbase s1 sp coins _ hc hpc1 hrun1 hsp1 hspA1 hx19_1 hcl1 hro1) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hfp2, hx19_2, _, _, _, hP2⟩
  refine SepWP.weaken_pre hP2 ?_
  have hm22240_128 : memRegion (sp + 22240#64) 99 ∗ memRegion (sp + 22339#64) 29 =
      memRegion (sp + 22240#64) 128 :=
    (memRegion_split' (b := sp + 22240#64) (b' := sp + 22339#64) (n := 99) (k := (29 : Nat)) rfl (by bv_omega) (by decide)).symm
  have hm22400_1536 : memRegion (sp + 22400#64) 384 ∗ memRegion (sp + 22784#64) 1152 =
      memRegion (sp + 22400#64) 1536 :=
    (memRegion_split' (b := sp + 22400#64) (b' := sp + 22784#64) (n := 384) (k := (1152 : Nat)) rfl (by bv_omega) (by decide)).symm
  refine SepWP.weaken_pre
    (P' := ((sp + 19152#64) ↦₈ 0#8) ∗ ((sp + 19120#64) ↦ₛ coins) ∗
      memRegion (sp + 1312#64) 512 ∗ memRegion (sp + 11856#64) 512 ∗
      memRegion (sp + 22240#64) 128 ∗ memRegion (sp + 22400#64) 1536 ∗
      memRegion (sp + 24448#64) 32 ∗ stackAt sp 1136 ∗
      (((sp + 4496#64) ↦ₛ hashed) ∗ memRegion (sp + 1824#64) 432 ∗
        memRegion (sp + 18032#64) 1088 ∗
        PolyMem (sp + 19168#64) (polyVecNat (rHatPoly16 prf0)) ∗
        PolyMem (sp + 19680#64) (polyVecNat (rHatPoly16 prf1)) ∗
        PolyMem (sp + 20192#64) (polyVecNat (rHatPoly16 prf2)) ∗
        PolyMem (sp + 20704#64) (polyVecNat (neonCbd2Poly16 prf3)) ∗
        PolyMem (sp + 21216#64) (polyVecNat (neonCbd2Poly16 prf4)) ∗
        PolyMem (sp + 21728#64) (polyVecNat (neonCbd2Poly16 prf5)) ∗
        memRegion (sp + 22368#64) 32 ∗ memRegion (sp + 24480#64) 96 ∗
        memRegion (sp + 24976#64) 128 ∗ memRegion (sp + 25296#64) 128 ∗
        (memRegion (sp + 11824#64) 32 ∗ memRegion (sp + 12368#64) 5664 ∗ memRegion (sp + 19153#64) 15) ∗
        (memRegion (sp + 23936#64) 512 ∗ memRegion (sp + 24576#64) 400 ∗
          memRegion (sp + 25104#64) 192 ∗ memRegion (sp + 25424#64) 192) ∗ Rest))
    (by
      rw [← hm22240_128, ← hm22400_1536,
          memRegion_split' (b := sp + 24448#64) (b' := sp + 24480#64) (n := 32) (k := (96 : Nat)) rfl (by bv_omega) (by decide)]
      sep_frame) ?_
  refine SepWP.mono (seg6d_ok hb hbase s2 sp coins 0#8 _ hc hpc2 hrun2 hsp2 hspA2 hx19_2 hcl2 hro2) ?_
  rintro sf Pf _ _ ⟨hspf, hspAf, hfpf, hx19f, hx20f, hclf, hrof, hPf⟩
  refine ⟨hspf, hspAf, hfpf.trans (hfp2.trans hfp1), hx19f, hx20f, hclf, hrof, Entails.trans hPf ?_⟩
  have hm22240_160 : memRegion (sp + 22240#64) 128 ∗ memRegion (sp + 22368#64) 32 =
      memRegion (sp + 22240#64) 160 :=
    (memRegion_split' (b := sp + 22240#64) (b' := sp + 22368#64) (n := 128) (k := (32 : Nat)) rfl (by bv_omega) (by decide)).symm
  have hm24448_128 : memRegion (sp + 24448#64) 32 ∗ memRegion (sp + 24480#64) 96 =
      memRegion (sp + 24448#64) 128 :=
    (memRegion_split' (b := sp + 24448#64) (b' := sp + 24480#64) (n := 32) (k := (96 : Nat)) rfl (by bv_omega) (by decide)).symm
  rw [hm24976, ← hm22240_160, ← hm24448_128]
  sep_frame

@[expose] def Seg6Post [MlKemPlacement] (b : BitVec 64) (s0 : State)
    (ret dkA ct1A ct2A : BitVec 64) (dk ct1 ct2 : List (BitVec 8)) (F : SepProp)
    (sf : State) (Pf : SepProp) : Prop :=
  let sp := s0.sp - 25824#64
  sf.pc = b + offSeg7Start ∧
  sf.status = .Running ∧
  mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧
  MlKemRoOk mlkemMpl sf.mem ∧
  sf.sp = sp ∧ sf.spAligned = true ∧
  sf.readReg64 .fp = s0.sp - 96#64 ∧
  sf.readReg64 .x19 = 1536#64 ∧
  sf.readReg64 .x20 = sp + 22400#64 ∧
  (Pf ⊢ Seg6Spatial s0 ret dkA ct1A ct2A dk ct1 ct2 F)

theorem seg6_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s0 s : State) (ret dkA ct1A ct2A : BitVec 64)
    (dk ct1 ct2 : List (BitVec 8)) (F : SepProp)
    (hpc : s.pc = b + offSeg5End) (hrun : s.status = .Running)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hsp : s.sp = s0.sp - 25824#64) (hspA : s.spAligned = true)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = (s0.sp - 25824#64) + 11856#64) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg7Start) s
      (Seg5Spatial s0 ret dkA ct1A ct2A dk ct1 ct2 F)
      (Seg6Post b s0 ret dkA ct1A ct2A dk ct1 ct2 F) := by
  set sp := s0.sp - 25824#64
  set ct := ct1 ++ ct2
  set m' := indCpaDecrypt 3 10 4 (dk.take 1152) ct
  set rho := (dk.drop 2304).take 32
  set hPk := (dk.drop 2336).take 32
  set z := (dk.drop 2368).take 32
  set pk0 := (dk.drop 1152).take 384
  set pk1 := (dk.drop 1536).take 384
  set pk2 := (dk.drop 1920).take 384
  set hashed := sha3_512List (m' ++ hPk)
  have hh : hashed.length = 64 := sha3_512List_length (m' ++ hPk)
  set Rest := SavedFrame04 s0.sp s0 ∗
    memRegion sp 8 ∗ WordRangeMem 32 (sp + 8#64) (msgWordFn m') ∗
    ((sp + 136#64) ↦₆₄ ret) ∗ memRegion (sp + 144#64) 1168 ∗
    ((sp + 2256#64) ↦ₛ ct) ∗ ((sp + 3344#64) ↦ₛ ct) ∗ memRegion (sp + 4432#64) 64 ∗
    memRegion (sp + 4560#64) 1120 ∗
    PolyMem (sp + 5680#64) (polyVecNat (modTHatPoly16 pk0)) ∗
    PolyMem (sp + 6192#64) (polyVecNat (modTHatPoly16 pk1)) ∗
    PolyMem (sp + 6704#64) (polyVecNat (modTHatPoly16 pk2)) ∗
    ATransMemAt sp 7216 rho ∗
    ((sp + 25616#64) ↦ₛ shake256List 32 (z ++ ct)) ∗
    memRegion (sp + 25648#64) 16 ∗
    (dkA ↦ₛ dk) ∗ (ct1A ↦ₛ ct1) ∗ (ct2A ↦ₛ ct2) ∗ F
  refine SepWP.weaken_pre
    (P' := ((sp + 4496#64) ↦ₛ hashed) ∗ memRegion (sp + 1312#64) 304 ∗
      memRegion (sp + 1616#64) 640 ∗ memRegion (sp + 11824#64) 13792 ∗
      stackAt sp 1136 ∗ Rest)
    (by
      dsimp only [Seg5Spatial]
      rw [split_144_2112 sp]
      sep_frame) ?_
  refine SepWP.mono (seg6_core_ok hb hbase s sp hashed Rest hh hpc hrun hsp hspA hx19 hx20 hcl hro) ?_
  rintro sf Pf hpcf hrunf ⟨hspf, hspAf, hfpf, hx19f, hx20f, hclf, hrof, hPf⟩
  exact ⟨hpcf, hrunf, hclf, hrof, hspf, hspAf, hfpf.trans hfp, hx19f, hx20f,
    Entails.trans hPf (by dsimp only [Seg6Spatial]; sep_frame)⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg6
