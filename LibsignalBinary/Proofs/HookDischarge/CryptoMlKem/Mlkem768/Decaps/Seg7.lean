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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg6 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg6b -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg6d -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg7b -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg7a

/-!
# `decapsulate_compressed_key` (`B04`) — Segment 7 Composition (`+0x8d00 .. +0xabd8`)

Composes `Seg7a.seg7a_ok` (`u'[0..2] = InvNTT(Âᵀ · r̂) + e₁`) and `Seg7b.seg7b_ok`
(`compress_and_serialize_10` writing `c₁'` at `[sp + 18032, sp + 18992)` and copying `r̂[0..2]`
to `[sp + 11856, sp + 13392)`) with `Seg7b.decapsCt1_eq`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg7

open Arm64 ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  indCpaDecrypt indCpaEncryptWith sampleNtt sha3_512List shake256List)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd (neonCbd2Poly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  PolyMem polyVecNat vecRangeMem_entails_memRegion)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (entails_sub)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a (sha3_512List_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base (
  SavedFrame04 blkPC04 blkPl04)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure (
  WordRangeMem modTHatPoly16 msgWordFn)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5 (ATransMemAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg6 (Seg6Spatial)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg6b (rHatPoly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg6d (offSeg7Start)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg7a (seg7a_ok uVecPoly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg7b (
  decapsCt1_eq offSeg8Start seg7b_ok)

attribute [local irreducible]
  blkPC04 sha3_512List shake256List neonCbd2Poly16 polyVecNat rHatPoly16
  ATransMemAt WordRangeMem SavedFrame04

@[expose] noncomputable def Seg7Spatial (s0 : State) (ret dkA ct1A ct2A : BitVec 64)
    (dk ct1 ct2 : List (BitVec 8)) (F : SepProp) : SepProp :=
  let sp := s0.sp - 25824#64
  let ct := ct1 ++ ct2
  let m' := indCpaDecrypt 3 10 4 (dk.take 1152) ct
  let pk := (dk.drop 1152).take 1184
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
  let prf6 := shake256List 128 (coins ++ [6#8])
  let ct1' := (indCpaEncryptWith sampleNtt 3 10 4 pk m' coins).1
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
  memRegion (sp + 11824#64) 32 ∗
  PolyMem (sp + 11856#64) (polyVecNat (rHatPoly16 prf0)) ∗
  PolyMem (sp + 12368#64) (polyVecNat (rHatPoly16 prf1)) ∗
  PolyMem (sp + 12880#64) (polyVecNat (rHatPoly16 prf2)) ∗
  memRegion (sp + 13392#64) 4640 ∗
  ((sp + 18032#64) ↦ₛ ct1') ∗
  memRegion (sp + 18992#64) 176 ∗
  PolyMem (sp + 19168#64) (polyVecNat (rHatPoly16 prf0)) ∗
  PolyMem (sp + 19680#64) (polyVecNat (rHatPoly16 prf1)) ∗
  PolyMem (sp + 20192#64) (polyVecNat (rHatPoly16 prf2)) ∗
  memRegion (sp + 20704#64) 4912 ∗
  ((sp + 25616#64) ↦ₛ shake256List 32 (z ++ ct)) ∗
  memRegion (sp + 25648#64) 16 ∗
  (dkA ↦ₛ dk) ∗ (ct1A ↦ₛ ct1) ∗ (ct2A ↦ₛ ct2) ∗ F

private theorem split_7344_seg7 (sp : BitVec 64) :
    memRegion (sp + 11824#64) 7344 =
      memRegion (sp + 11824#64) 32 ∗ memRegion (sp + 11856#64) 1552 ∗
      memRegion (sp + 13408#64) 8 ∗ memRegion (sp + 13416#64) 4616 ∗
      memRegion (sp + 18032#64) 960 ∗ memRegion (sp + 18992#64) 176 := by
  rw [memRegion_split' (b := sp + 11824#64) (b' := sp + 11856#64) (n := 32) (k := (7312 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 11856#64) (b' := sp + 13408#64) (n := 1552) (k := (5760 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 13408#64) (b' := sp + 13416#64) (n := 8) (k := (5752 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 13416#64) (b' := sp + 18032#64) (n := 4616) (k := (1136 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 18032#64) (b' := sp + 18992#64) (n := 960) (k := (176 : Nat)) rfl (by bv_omega) (by decide)]

private theorem split_432_seg7 (sp : BitVec 64) :
    memRegion (sp + 1824#64) 432 = memRegion (sp + 1824#64) 368 ∗ memRegion (sp + 2192#64) 64 :=
  memRegion_split' (b := sp + 1824#64) (b' := sp + 2192#64) (n := 368) (k := (64 : Nat)) rfl (by bv_omega) (by decide)

private theorem split_1680_seg7 (sp : BitVec 64) :
    memRegion (sp + 23936#64) 1680 = memRegion (sp + 23936#64) 512 ∗ memRegion (sp + 24448#64) 1168 :=
  memRegion_split' (b := sp + 23936#64) (b' := sp + 24448#64) (n := 512) (k := (1168 : Nat)) rfl (by bv_omega) (by decide)

private theorem prep_22400_seg7b (sp : BitVec 64) (f0 f1 : Nat → BitVec 128) :
    PolyMem (sp + 22400#64) f0 ∗ PolyMem (sp + 22912#64) f1 ⊢
      memRegion (sp + 22400#64) 520 ∗ memRegion (sp + 22920#64) 504 := by
  refine Entails.trans (sepConj_mono (vecRangeMem_entails_memRegion 32 _ _) (vecRangeMem_entails_memRegion 32 _ _)) ?_
  change memRegion (sp + 22400#64) 512 ∗ memRegion (sp + 22912#64) 512 ⊢
    memRegion (sp + 22400#64) 520 ∗ memRegion (sp + 22920#64) 504
  rw [memRegion_split' (b := sp + 22400#64) (b' := sp + 22912#64) (n := 512) (k := (8 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 22912#64) (b' := sp + 22920#64) (n := 8) (k := (504 : Nat)) rfl (by bv_omega) (by decide)]
  sep_frame

private theorem join_13392_4640 (sp : BitVec 64) :
    memRegion (sp + 13392#64) 24 ∗ memRegion (sp + 13416#64) 4616 = memRegion (sp + 13392#64) 4640 :=
  (memRegion_split' (b := sp + 13392#64) (b' := sp + 13416#64) (n := 24) (k := (4616 : Nat)) rfl (by bv_omega) (by decide)).symm

private theorem join_20704_4912 (sp : BitVec 64) (fe0 fe1 fe2 fu2 : Nat → BitVec 128) :
    PolyMem (sp + 20704#64) fe0 ∗ PolyMem (sp + 21216#64) fe1 ∗ PolyMem (sp + 21728#64) fe2 ∗
      memRegion (sp + 22240#64) 160 ∗ memRegion (sp + 22400#64) 520 ∗ memRegion (sp + 22920#64) 504 ∗
      PolyMem (sp + 23424#64) fu2 ∗ memRegion (sp + 23936#64) 512 ∗ memRegion (sp + 24448#64) 1168 ⊢
      memRegion (sp + 20704#64) 4912 := by
  refine Entails.trans (sepConj_mono (vecRangeMem_entails_memRegion 32 _ _)
    (sepConj_mono (vecRangeMem_entails_memRegion 32 _ _)
      (sepConj_mono (vecRangeMem_entails_memRegion 32 _ _)
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (vecRangeMem_entails_memRegion 32 _ _)))))))) ?_
  change memRegion (sp + 20704#64) 512 ∗ memRegion (sp + 21216#64) 512 ∗ memRegion (sp + 21728#64) 512 ∗
    memRegion (sp + 22240#64) 160 ∗ memRegion (sp + 22400#64) 520 ∗ memRegion (sp + 22920#64) 504 ∗
    memRegion (sp + 23424#64) 512 ∗ memRegion (sp + 23936#64) 512 ∗ memRegion (sp + 24448#64) 1168 ⊢
    memRegion (sp + 20704#64) 4912
  rw [memRegion_split' (b := sp + 20704#64) (b' := sp + 21216#64) (n := 512) (k := (4400 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 21216#64) (b' := sp + 21728#64) (n := 512) (k := (3888 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 21728#64) (b' := sp + 22240#64) (n := 512) (k := (3376 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 22240#64) (b' := sp + 22400#64) (n := 160) (k := (3216 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 22400#64) (b' := sp + 22920#64) (n := 520) (k := (2696 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 22920#64) (b' := sp + 23424#64) (n := 504) (k := (2192 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 23424#64) (b' := sp + 23936#64) (n := 512) (k := (1680 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 23936#64) (b' := sp + 24448#64) (n := 512) (k := (1168 : Nat)) rfl (by bv_omega) (by decide)]
  sep_frame

@[expose] def Seg7Post [MlKemPlacement] (b : BitVec 64)
    (s0 : State) (ret dkA ct1A ct2A : BitVec 64)
    (dk ct1 ct2 : List (BitVec 8)) (F : SepProp) : State → SepProp → Prop :=
  let sp := s0.sp - 25824#64
  fun sf Pf =>
  sf.pc = b + offSeg8Start ∧
  sf.status = .Running ∧
  mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧
  MlKemRoOk mlkemMpl sf.mem ∧
  sf.sp = sp ∧ sf.spAligned = true ∧
  sf.readReg64 .fp = s0.sp - 96#64 ∧
  sf.readReg64 .x19 = sp + 11856#64 ∧
  (Pf ⊢ Seg7Spatial s0 ret dkA ct1A ct2A dk ct1 ct2 F)

theorem seg7_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s0 s : State) (ret dkA ct1A ct2A : BitVec 64)
    (dk ct1 ct2 : List (BitVec 8)) (F : SepProp) (hdk : dk.length = 2400)
    (hpc : s.pc = b + offSeg7Start) (hrun : s.status = .Running)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hsp : s.sp = s0.sp - 25824#64) (hspA : s.spAligned = true)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = 1536#64)
    (hx20 : s.readReg64 .x20 = (s0.sp - 25824#64) + 22400#64) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg8Start) s
      (Seg6Spatial s0 ret dkA ct1A ct2A dk ct1 ct2 F)
      (Seg7Post b s0 ret dkA ct1A ct2A dk ct1 ct2 F) := by
  set sp := s0.sp - 25824#64
  set ct := ct1 ++ ct2
  set m' := indCpaDecrypt 3 10 4 (dk.take 1152) ct
  set pk := (dk.drop 1152).take 1184
  set rho := (dk.drop 2304).take 32
  set hPk := (dk.drop 2336).take 32
  set coins := (sha3_512List (m' ++ hPk)).drop 32
  set z := (dk.drop 2368).take 32
  set pk0 := (dk.drop 1152).take 384
  set pk1 := (dk.drop 1536).take 384
  set pk2 := (dk.drop 1920).take 384
  have hpk : pk.length = 1184 := by simp [pk, List.length_take, List.length_drop, hdk]
  have hcoins : coins.length = 32 := by
    simp [coins, List.length_drop, sha3_512List_length]
  have hrho_pk : (pk.drop 1152).take 32 = rho := by
    simp [pk, rho, List.drop_take, List.drop_drop, List.take_take]
  set RestCore := SavedFrame04 s0.sp s0 ∗
    memRegion sp 8 ∗ WordRangeMem 32 (sp + 8#64) (msgWordFn m') ∗
    ((sp + 136#64) ↦₆₄ ret) ∗ memRegion (sp + 144#64) 1168 ∗
    PolyMem (sp + 1312#64) (polyVecNat (neonCbd2Poly16 (shake256List 128 (coins ++ [6#8])))) ∗
    ((sp + 2256#64) ↦ₛ ct) ∗ ((sp + 3344#64) ↦ₛ ct) ∗ memRegion (sp + 4432#64) 64 ∗
    ((sp + 4496#64) ↦ₛ sha3_512List (m' ++ hPk)) ∗ memRegion (sp + 4560#64) 1120 ∗
    PolyMem (sp + 5680#64) (polyVecNat (modTHatPoly16 pk0)) ∗
    PolyMem (sp + 6192#64) (polyVecNat (modTHatPoly16 pk1)) ∗
    PolyMem (sp + 6704#64) (polyVecNat (modTHatPoly16 pk2)) ∗
    memRegion (sp + 11824#64) 32 ∗ memRegion (sp + 13416#64) 4616 ∗
    memRegion (sp + 18992#64) 176 ∗
    ((sp + 25616#64) ↦ₛ shake256List 32 (z ++ ct)) ∗ memRegion (sp + 25648#64) 16 ∗
    (dkA ↦ₛ dk) ∗ (ct1A ↦ₛ ct1) ∗ (ct2A ↦ₛ ct2) ∗ stackAt sp 1136 ∗ F
  set Rest := memRegion (sp + 13408#64) 8 ∗ memRegion (sp + 18032#64) 960 ∗
    memRegion (sp + 22240#64) 160 ∗ memRegion (sp + 23936#64) 512 ∗
    memRegion (sp + 24448#64) 1168 ∗ RestCore
  refine SepWP.weaken_pre
    (P' := memRegion (sp + 1824#64) 432 ∗ ATransMemAt sp 7216 rho ∗
      memRegion (sp + 11856#64) 1552 ∗
      PolyMem (sp + 19168#64) (polyVecNat (rHatPoly16 (shake256List 128 (coins ++ [0#8])))) ∗
      PolyMem (sp + 19680#64) (polyVecNat (rHatPoly16 (shake256List 128 (coins ++ [1#8])))) ∗
      PolyMem (sp + 20192#64) (polyVecNat (rHatPoly16 (shake256List 128 (coins ++ [2#8])))) ∗
      PolyMem (sp + 20704#64) (polyVecNat (neonCbd2Poly16 (shake256List 128 (coins ++ [3#8])))) ∗
      PolyMem (sp + 21216#64) (polyVecNat (neonCbd2Poly16 (shake256List 128 (coins ++ [4#8])))) ∗
      PolyMem (sp + 21728#64) (polyVecNat (neonCbd2Poly16 (shake256List 128 (coins ++ [5#8])))) ∗
      PolyMem (sp + 22400#64) (fun _ => 0#128) ∗
      PolyMem (sp + 22912#64) (fun _ => 0#128) ∗
      PolyMem (sp + 23424#64) (fun _ => 0#128) ∗ Rest)
    (by
      dsimp only [Seg6Spatial, Rest, RestCore]
      rw [split_7344_seg7 sp, split_1680_seg7 sp]
      set_option maxRecDepth 4000 in sep_frame) ?_
  refine sepWP_seq_env hcl hro
    (seg7a_ok hb hbase s sp (s0.sp - 96#64) rho coins Rest hpc hrun hsp hspA hfp hx19 hx20 hcl hro) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hfp1, hx19_1, hx20_1, _, _, hP1⟩
  set RestB := memRegion (sp + 1824#64) 368 ∗ ATransMemAt sp 7216 rho ∗
    PolyMem (sp + 20704#64) (polyVecNat (neonCbd2Poly16 (shake256List 128 (coins ++ [3#8])))) ∗
    PolyMem (sp + 21216#64) (polyVecNat (neonCbd2Poly16 (shake256List 128 (coins ++ [4#8])))) ∗
    PolyMem (sp + 21728#64) (polyVecNat (neonCbd2Poly16 (shake256List 128 (coins ++ [5#8])))) ∗
    memRegion (sp + 22240#64) 160 ∗ memRegion (sp + 22920#64) 504 ∗
    PolyMem (sp + 23424#64) (polyVecNat (uVecPoly16 rho coins 2)) ∗
    memRegion (sp + 23936#64) 512 ∗ RestCore
  have hprep : P1 ⊢
      memRegion (sp + 2192#64) 64 ∗ memRegion (sp + 11856#64) 16 ∗
      PolyMem (sp + 11872#64) (polyVecNat (uVecPoly16 rho coins 0)) ∗
      PolyMem (sp + 12384#64) (polyVecNat (uVecPoly16 rho coins 1)) ∗
      PolyMem (sp + 12896#64) (polyVecNat (uVecPoly16 rho coins 2)) ∗
      memRegion (sp + 13408#64) 8 ∗ memRegion (sp + 18032#64) 960 ∗
      PolyMem (sp + 19168#64) (polyVecNat (rHatPoly16 (shake256List 128 (coins ++ [0#8])))) ∗
      PolyMem (sp + 19680#64) (polyVecNat (rHatPoly16 (shake256List 128 (coins ++ [1#8])))) ∗
      PolyMem (sp + 20192#64) (polyVecNat (rHatPoly16 (shake256List 128 (coins ++ [2#8])))) ∗
      memRegion (sp + 22400#64) 520 ∗ memRegion (sp + 24448#64) 1168 ∗ RestB := by
    refine Entails.trans hP1 ?_
    dsimp only [Rest, RestB]
    rw [split_432_seg7 sp]
    exact entails_sub (prep_22400_seg7b sp _ _) (by sep_frame) (by sep_frame)
  refine SepWP.weaken_pre hprep ?_
  refine sepWP_seq_env hcl1 hro1
    (seg7b_ok hb hbase s1 sp (s0.sp - 96#64)
      (uVecPoly16 rho coins 0) (uVecPoly16 rho coins 1) (uVecPoly16 rho coins 2)
      (rHatPoly16 (shake256List 128 (coins ++ [0#8])))
      (rHatPoly16 (shake256List 128 (coins ++ [1#8])))
      (rHatPoly16 (shake256List 128 (coins ++ [2#8])))
      RestB hpc1 hrun1 hsp1 hspA1 hfp1 hx19_1 hx20_1 hcl1 hro1) ?_
  rintro sf Pf hpcf hrunf _ _ ⟨hspf, hspAf, hfpf, hx19f, hclf, hrof, hPf⟩
  refine SepWP.done hpcf hrunf ⟨hpcf, hrunf, hclf, hrof, hspf, hspAf, hfpf, hx19f, Entails.trans hPf ?_⟩
  have hct1_eq := decapsCt1_eq (m := m') hpk hcoins
  dsimp only at hct1_eq
  rw [hrho_pk] at hct1_eq
  dsimp only [Seg7Spatial, RestB, RestCore]
  rw [hct1_eq, split_432_seg7 sp, ← join_13392_4640 sp]
  set_option maxRecDepth 4000 in
  exact entails_sub
    (join_20704_4912 sp
      (polyVecNat (neonCbd2Poly16 (shake256List 128 (coins ++ [3#8]))))
      (polyVecNat (neonCbd2Poly16 (shake256List 128 (coins ++ [4#8]))))
      (polyVecNat (neonCbd2Poly16 (shake256List 128 (coins ++ [5#8]))))
      (polyVecNat (uVecPoly16 rho coins 2)))
    (by sep_frame) (by sep_frame)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg7
