/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4b -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1b
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3c
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4a

/-!
# `decapsulate_compressed_key` (`B04`) — Composed Segments 1–4 (`+0x0000 → +0x4058`)

Composes `seg3_ok`, `seg4a_prep1`, `seg4a_prep2`, `seg4a_hashes_a`, `seg4a_prep_b01`,
`seg4a_call_b01`, and `seg4b_ok`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4

open Arm64 ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  indCpaDecrypt keccakSponge sha3_512List shake256List)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a (sha3_512List_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  cell_entails_memRegion8 sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (sepWP_elim_region32)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  PolyMem SepWP.of_memRegion_vecRangeMem Vec128At VecRangeMem bytesToVecNat
  pointsToBytes_eq_vecRangeMem polyVecNat unpack128_length vec128At_eq_pointsToBytes
  vecRangeMem_entails_memRegion)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base (
  SavedFrame04 blkPC04 blkPl04)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1b (cst16_3_val)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3 (Seg3Spatial seg3_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3c (offSeg3cEnd)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure (
   WordRangeMem dk_seg4_split modTHatPoly16 msgWordFn sepWP_elim_byteRangeMem
   sepWP_elim_wordRangeMem)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4a (
  offSeg4Start seg4a_call_b01 seg4a_hashes_a seg4a_prep1 seg4a_prep2 seg4a_prep_b01)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4b (
  offSeg4End seg4b_ok)

/-! ## 1. `Seg4Spatial` & Stack Region Split/Join Helpers -/

@[expose] def Seg4Spatial (s0 : State) (ret dkA ct1A ct2A : BitVec 64)
    (dk ct1 ct2 : List (BitVec 8)) (F : SepProp) : SepProp :=
  let sp := s0.sp - 25824#64
  let ct := ct1 ++ ct2
  let m' := indCpaDecrypt 3 10 4 (dk.take 1152) ct
  let hPk := (dk.drop 2336).take 32
  let z := (dk.drop 2368).take 32
  let pk0 := (dk.drop 1152).take 384
  let pk1 := (dk.drop 1536).take 384
  let pk2 := (dk.drop 1920).take 384
  stackAt sp 1136 ∗ SavedFrame04 s0.sp s0 ∗
  memRegion sp 8 ∗ WordRangeMem 32 (sp + 8#64) (msgWordFn m') ∗
  ((sp + 136#64) ↦₆₄ ret) ∗ memRegion (sp + 144#64) 48 ∗
  ((sp + 192#64) ↦₆₄ (sp + 13392#64)) ∗ ((sp + 200#64) ↦₆₄ (sp + 22664#64)) ∗
  memRegion (sp + 208#64) 2048 ∗ ((sp + 2256#64) ↦ₛ ct) ∗
  ((sp + 3344#64) ↦ₛ ct) ∗ memRegion (sp + 4432#64) 64 ∗
  ((sp + 4496#64) ↦ₛ sha3_512List (m' ++ hPk)) ∗
  memRegion (sp + 4560#64) 1120 ∗ memRegion (sp + 5680#64) 6176 ∗
  PolyMem (sp + 11856#64) (polyVecNat (modTHatPoly16 pk0)) ∗
  PolyMem (sp + 12368#64) (polyVecNat (modTHatPoly16 pk1)) ∗
  PolyMem (sp + 12880#64) (polyVecNat (modTHatPoly16 pk2)) ∗
  memRegion (sp + 13392#64) 12224 ∗
  ((sp + 25616#64) ↦ₛ shake256List 32 (z ++ ct)) ∗
  memRegion (sp + 25648#64) 16 ∗
  (dkA ↦ₛ dk) ∗ (ct1A ↦ₛ ct1) ∗ (ct2A ↦ₛ ct2) ∗ F

private theorem cell64_entails_memRegion8 (a v : BitVec 64) :
    (a ↦₆₄ v) ⊢ memRegion a 8 :=
  cell_entails_memRegion8 a v

private theorem indCpaDecrypt_len32 (sk ct : List (BitVec 8)) :
    (indCpaDecrypt 3 10 4 sk ct).length = 32 := by
  simp [indCpaDecrypt, LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.compressAndEncode,
    LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.byteEncode,
    LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.bitsToBytes]

private theorem memRegion_136_split (sp : BitVec 64) :
    memRegion sp 136 = memRegion sp 8 ∗ memRegion (sp + 8#64) 128 :=
  memRegion_split' (b := sp) (b' := sp + 8#64) (n := 8) (k := (128 : Nat))
    rfl (by bv_omega) (by decide)

private theorem memRegion_56_split (sp : BitVec 64) :
    memRegion (sp + 144#64) 56 = memRegion (sp + 144#64) 48 ∗ memRegion (sp + 192#64) 8 :=
  memRegion_split' (b := sp + 144#64) (b' := sp + 192#64) (n := 48) (k := (8 : Nat))
    rfl (by bv_omega) (by decide)

private theorem memRegion_16272_seg4_split (sp : BitVec 64) :
    memRegion (sp + 4432#64) 16272 =
      memRegion (sp + 4432#64) 32 ∗ memRegion (sp + 4464#64) 32 ∗
      memRegion (sp + 4496#64) 1184 ∗ memRegion (sp + 5680#64) 64 ∗
      memRegion (sp + 5744#64) 448 ∗ memRegion (sp + 6192#64) 5664 ∗
      memRegion (sp + 11856#64) 1120 ∗ memRegion (sp + 12976#64) 7728 := by
  rw [memRegion_split' (b := sp + 4432#64) (b' := sp + 4464#64) (n := 32) (k := (16240 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 4464#64) (b' := sp + 4496#64) (n := 32) (k := (16208 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 4496#64) (b' := sp + 5680#64) (n := 1184) (k := (15024 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 5680#64) (b' := sp + 5744#64) (n := 64) (k := (14960 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 5744#64) (b' := sp + 6192#64) (n := 448) (k := (14512 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 6192#64) (b' := sp + 11856#64) (n := 5664) (k := (8848 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 11856#64) (b' := sp + 12976#64) (n := 1120) (k := (7728 : Nat)) rfl (by bv_omega) (by decide)]

private theorem memRegion_4928_seg4_split (sp : BitVec 64) :
    memRegion (sp + 20736#64) 4928 =
      memRegion (sp + 20736#64) 1664 ∗ memRegion (sp + 22400#64) 32 ∗
      memRegion (sp + 22432#64) 3184 ∗ memRegion (sp + 25616#64) 32 ∗
      memRegion (sp + 25648#64) 16 := by
  rw [memRegion_split' (b := sp + 20736#64) (b' := sp + 22400#64) (n := 1664) (k := (3264 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 22400#64) (b' := sp + 22432#64) (n := 32) (k := (3232 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 22432#64) (b' := sp + 25616#64) (n := 3184) (k := (48 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 25616#64) (b' := sp + 25648#64) (n := 32) (k := (16 : Nat)) rfl (by bv_omega) (by decide)]

private theorem memRegion_mid_b01_split (sp : BitVec 64) :
    memRegion (sp + 5680#64) 64 ∗ memRegion (sp + 11856#64) 1120 ∗
      memRegion (sp + 12976#64) 7728 =
      memRegion (sp + 5680#64) 32 ∗ memRegion (sp + 5712#64) 32 ∗
      memRegion (sp + 11856#64) 32 ∗ memRegion (sp + 11888#64) 480 ∗
      memRegion (sp + 12368#64) 5664 ∗ memRegion (sp + 18032#64) 2672 := by
  have h5680 : memRegion (sp + 5680#64) 64 =
      memRegion (sp + 5680#64) 32 ∗ memRegion (sp + 5712#64) 32 :=
    memRegion_split' (b := sp + 5680#64) (b' := sp + 5712#64) (n := 32) (k := (32 : Nat))
      rfl (by bv_omega) (by decide)
  have h8848 : memRegion (sp + 11856#64) 8848 =
      memRegion (sp + 11856#64) 1120 ∗ memRegion (sp + 12976#64) 7728 :=
    memRegion_split' (b := sp + 11856#64) (b' := sp + 12976#64) (n := 1120) (k := (7728 : Nat))
      rfl (by bv_omega) (by decide)
  have h8848' : memRegion (sp + 11856#64) 8848 =
      memRegion (sp + 11856#64) 32 ∗ memRegion (sp + 11888#64) 480 ∗
      memRegion (sp + 12368#64) 5664 ∗ memRegion (sp + 18032#64) 2672 := by
    rw [memRegion_split' (b := sp + 11856#64) (b' := sp + 11888#64) (n := 32) (k := (8816 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 11888#64) (b' := sp + 12368#64) (n := 480) (k := (8336 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 12368#64) (b' := sp + 18032#64) (n := 5664) (k := (2672 : Nat)) rfl (by bv_omega) (by decide)]
  have hlhs : memRegion (sp + 5680#64) 64 ∗ memRegion (sp + 11856#64) 8848 =
      memRegion (sp + 5680#64) 64 ∗ memRegion (sp + 11856#64) 1120 ∗
        memRegion (sp + 12976#64) 7728 := by
    rw [h8848]
  rw [← hlhs, h5680, h8848']
  exact sepProp_ext (by sep_frame) (by sep_frame)

private theorem memRegion_post_b01_split (sp : BitVec 64) :
    memRegion (sp + 4560#64) 1152 ∗ memRegion (sp + 5712#64) 32 ∗
      memRegion (sp + 5744#64) 448 ∗ memRegion (sp + 11856#64) 32 ∗
      memRegion (sp + 11888#64) 480 ∗ memRegion (sp + 12368#64) 5664 =
      memRegion (sp + 4560#64) 1120 ∗ memRegion (sp + 5680#64) 512 ∗
      memRegion (sp + 11856#64) 1536 ∗ memRegion (sp + 13392#64) 4640 := by
  have h1632a : memRegion (sp + 4560#64) 1632 =
      memRegion (sp + 4560#64) 1152 ∗ memRegion (sp + 5712#64) 32 ∗ memRegion (sp + 5744#64) 448 := by
    rw [memRegion_split' (b := sp + 4560#64) (b' := sp + 5712#64) (n := 1152) (k := (480 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 5712#64) (b' := sp + 5744#64) (n := 32) (k := (448 : Nat)) rfl (by bv_omega) (by decide)]
  have h1632b : memRegion (sp + 4560#64) 1632 =
      memRegion (sp + 4560#64) 1120 ∗ memRegion (sp + 5680#64) 512 :=
    memRegion_split' (b := sp + 4560#64) (b' := sp + 5680#64) (n := 1120) (k := (512 : Nat))
      rfl (by bv_omega) (by decide)
  have h6176a : memRegion (sp + 11856#64) 6176 =
      memRegion (sp + 11856#64) 32 ∗ memRegion (sp + 11888#64) 480 ∗ memRegion (sp + 12368#64) 5664 := by
    rw [memRegion_split' (b := sp + 11856#64) (b' := sp + 11888#64) (n := 32) (k := (6144 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 11888#64) (b' := sp + 12368#64) (n := 480) (k := (5664 : Nat)) rfl (by bv_omega) (by decide)]
  have h6176b : memRegion (sp + 11856#64) 6176 =
      memRegion (sp + 11856#64) 1536 ∗ memRegion (sp + 13392#64) 4640 :=
    memRegion_split' (b := sp + 11856#64) (b' := sp + 13392#64) (n := 1536) (k := (4640 : Nat))
      rfl (by bv_omega) (by decide)
  have hlhs : memRegion (sp + 4560#64) 1632 ∗ memRegion (sp + 11856#64) 6176 =
      memRegion (sp + 4560#64) 1152 ∗ memRegion (sp + 5712#64) 32 ∗
      memRegion (sp + 5744#64) 448 ∗ memRegion (sp + 11856#64) 32 ∗
      memRegion (sp + 11888#64) 480 ∗ memRegion (sp + 12368#64) 5664 := by
    rw [h1632a, h6176a]; exact sepProp_ext (by sep_frame) (by sep_frame)
  rw [← hlhs, h1632b, h6176b]
  exact sepProp_ext (by sep_frame) (by sep_frame)

private theorem memRegion_2048_seg4_join (sp : BitVec 64) (v1 v2 v3 v4 : BitVec 64) (q : BitVec 128) :
    memRegion (sp + 208#64) 1632 ∗
      ((sp + 1840#64) ↦₆₄ v1) ∗ memRegion (sp + 1848#64) 8 ∗
      ((sp + 1856#64) ↦₆₄ v2) ∗ memRegion (sp + 1864#64) 8 ∗
      ((sp + 1872#64) ↦₆₄ v3) ∗ memRegion (sp + 1880#64) 8 ∗
      ((sp + 1888#64) ↦₆₄ v4) ∗ memRegion (sp + 1896#64) 8 ∗
      Vec128At (sp + 1904#64) q ∗ memRegion (sp + 1920#64) 336 ⊢
      memRegion (sp + 208#64) 2048 := by
  have hvec : Vec128At (sp + 1904#64) q ⊢ memRegion (sp + 1904#64) 16 := by
    rw [vec128At_eq_pointsToBytes]
    have hp := pointsToBytes_entails_memRegion (sp + 1904#64) (Encaps2.VecMem.unpack128 q)
    rwa [unpack128_length] at hp
  have hsub : memRegion (sp + 208#64) 1632 ∗
      ((sp + 1840#64) ↦₆₄ v1) ∗ memRegion (sp + 1848#64) 8 ∗
      ((sp + 1856#64) ↦₆₄ v2) ∗ memRegion (sp + 1864#64) 8 ∗
      ((sp + 1872#64) ↦₆₄ v3) ∗ memRegion (sp + 1880#64) 8 ∗
      ((sp + 1888#64) ↦₆₄ v4) ∗ memRegion (sp + 1896#64) 8 ∗
      Vec128At (sp + 1904#64) q ∗ memRegion (sp + 1920#64) 336 ⊢
      memRegion (sp + 208#64) 1632 ∗
      memRegion (sp + 1840#64) 8 ∗ memRegion (sp + 1848#64) 8 ∗
      memRegion (sp + 1856#64) 8 ∗ memRegion (sp + 1864#64) 8 ∗
      memRegion (sp + 1872#64) 8 ∗ memRegion (sp + 1880#64) 8 ∗
      memRegion (sp + 1888#64) 8 ∗ memRegion (sp + 1896#64) 8 ∗
      memRegion (sp + 1904#64) 16 ∗ memRegion (sp + 1920#64) 336 := by
    refine sepConj_mono_right (sepConj_mono (cell64_entails_memRegion8 _ _) (sepConj_mono_right ?_))
    refine sepConj_mono (cell64_entails_memRegion8 _ _) (sepConj_mono_right ?_)
    refine sepConj_mono (cell64_entails_memRegion8 _ _) (sepConj_mono_right ?_)
    refine sepConj_mono (cell64_entails_memRegion8 _ _) (sepConj_mono_right ?_)
    exact sepConj_mono_left hvec
  refine Entails.trans hsub ?_
  rw [memRegion_split' (b := sp + 208#64) (b' := sp + 1840#64) (n := 1632) (k := (416 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 1840#64) (b' := sp + 1848#64) (n := 8) (k := (408 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 1848#64) (b' := sp + 1856#64) (n := 8) (k := (400 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 1856#64) (b' := sp + 1864#64) (n := 8) (k := (392 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 1864#64) (b' := sp + 1872#64) (n := 8) (k := (384 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 1872#64) (b' := sp + 1880#64) (n := 8) (k := (376 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 1880#64) (b' := sp + 1888#64) (n := 8) (k := (368 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 1888#64) (b' := sp + 1896#64) (n := 8) (k := (360 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 1896#64) (b' := sp + 1904#64) (n := 8) (k := (352 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 1904#64) (b' := sp + 1920#64) (n := 16) (k := (336 : Nat)) rfl (by bv_omega) (by decide)]
  sep_frame

private theorem memRegion_6176_seg4_join (sp : BitVec 64) :
    memRegion (sp + 5680#64) 512 ∗ memRegion (sp + 6192#64) 5664 = memRegion (sp + 5680#64) 6176 :=
  (memRegion_split' (b := sp + 5680#64) (b' := sp + 6192#64) (n := 512) (k := (5664 : Nat))
    rfl (by bv_omega) (by decide)).symm

private theorem memRegion_12224_seg4_join (sp : BitVec 64) {m' : List (BitVec 8)} (hm' : m'.length = 32) :
    memRegion (sp + 13392#64) 4640 ∗ memRegion (sp + 18032#64) 2672 ∗
      ((sp + 20704#64) ↦ₛ m') ∗ memRegion (sp + 20736#64) 1664 ∗
      memRegion (sp + 22400#64) 32 ∗ memRegion (sp + 22432#64) 3184 ⊢
      memRegion (sp + 13392#64) 12224 := by
  have hm : ((sp + 20704#64) ↦ₛ m') ⊢ memRegion (sp + 20704#64) 32 := by
    have h := pointsToBytes_entails_memRegion (sp + 20704#64) m'; rwa [hm'] at h
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hm))) ?_
  rw [memRegion_split' (b := sp + 13392#64) (b' := sp + 18032#64) (n := 4640) (k := (7584 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 18032#64) (b' := sp + 20704#64) (n := 2672) (k := (4912 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 20704#64) (b' := sp + 20736#64) (n := 32) (k := (4880 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 20736#64) (b' := sp + 22400#64) (n := 1664) (k := (3216 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 22400#64) (b' := sp + 22432#64) (n := 32) (k := (3184 : Nat)) rfl (by bv_omega) (by decide)]
  sep_frame

/-! ## 2. Composed Segments 1–4 Contract (`+0x0000 → +0x4058`) -/

/-- Composed Segments 1–4 contract (`+0x0000 → +0x4058`). -/
theorem seg4_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s0 : State) (ret dkA ct1A ct2A : BitVec 64)
    (dk ct1 ct2 : List (BitVec 8)) (F : SepProp)
    (hpc : s0.pc = b) (hrun : s0.status = .Running) (hsp0 : s0.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s0.mem) (hro : MlKemRoOk mlkemMpl s0.mem)
    (hx0 : s0.readReg64 .x0 = ret) (hx1 : s0.readReg64 .x1 = dkA)
    (hx2 : s0.readReg64 .x2 = ct1A) (hx3 : s0.readReg64 .x3 = ct2A)
    (hdk : dk.length = 2400) (hct1 : ct1.length = 960) (hct2 : ct2.length = 128) :
    let sp := s0.sp - 25824#64
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg4End) s0
      (stackAt s0.sp 26960 ∗ (dkA ↦ₛ dk) ∗ (ct1A ↦ₛ ct1) ∗ (ct2A ↦ₛ ct2) ∗ F)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = s0.sp - 96#64 ∧
        sf.readReg64 .x9 = dkA ∧
        sf.readReg64 .x10 = 11#64 ∧
        sf.readReg64 .x23 = sp + 16384#64 ∧
        sf.readReg64 .x26 = sp + 20704#64 ∧
        sf.readReg64 .x27 = sp + 5680#64 ∧
        sf.readReg64 .x28 = sp + 20968#64 ∧
        (Pf ⊢ Seg4Spatial s0 ret dkA ct1A ct2A dk ct1 ct2 F)) := by
  intro sp
  refine sepWP_seq_env hcl hro
    (seg3_ok hb hbase s0 ret dkA ct1A ct2A dk ct1 ct2 F hpc hrun hsp0 hcl hro hx0 hx1 hx2 hx3 hdk hct1 hct2) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 hro3 ⟨hsp3, hspA3, hfp3, hx23_3, hx26_3, hx28_3, hP3⟩
  set ct := ct1 ++ ct2
  set m' := indCpaDecrypt 3 10 4 (dk.take 1152) ct
  set pk0 := (dk.drop 1152).take 384
  set pk1 := (dk.drop 1536).take 384
  set pk2 := (dk.drop 1920).take 384
  set rho := (dk.drop 2304).take 32
  set hPk := (dk.drop 2336).take 32
  set z := (dk.drop 2368).take 32
  have hct_len : ct.length = 1088 := by simp [ct, hct1, hct2]
  have hm'_len : m'.length = 32 := indCpaDecrypt_len32 _ _
  have hpk0_len : pk0.length = 384 := by simp [pk0, hdk]
  have hpk1_len : pk1.length = 384 := by simp [pk1, hdk]
  have hpk2_len : pk2.length = 384 := by simp [pk2, hdk]
  have hhPk_len : hPk.length = 32 := by simp [hPk, hdk]
  have hz_len : z.length = 32 := by simp [z, hdk]
  have hmsg_len : (m' ++ hPk).length = 64 := by simp [hm'_len, hhPk_len]
  have hzct_len : (z ++ ct).length = 1120 := by simp [hz_len, hct_len]
  have hfp_sp : s0.sp - 96#64 = sp + 25728#64 := by dsimp only [sp]; clear * -; bv_omega
  have hhPk_vec : ((dkA + 2336#64) ↦ₛ hPk) = VecRangeMem 2 (dkA + 2336#64) (bytesToVecNat hPk) :=
    pointsToBytes_eq_vecRangeMem 2 (dkA + 2336#64) (by omega)
  set R_common := SavedFrame04 s0.sp s0 ∗ memRegion sp 8 ∗ ((sp + 136#64) ↦₆₄ ret) ∗
    memRegion (sp + 144#64) 48 ∗ ((sp + 200#64) ↦₆₄ (sp + 22664#64)) ∗ memRegion (sp + 208#64) 1632 ∗
    memRegion (sp + 1848#64) 8 ∗ memRegion (sp + 1864#64) 8 ∗
    memRegion (sp + 1880#64) 8 ∗ ((sp + 1888#64) ↦₆₄ (dkA + 384#64)) ∗ memRegion (sp + 1896#64) 8 ∗
    memRegion (sp + 1920#64) 336 ∗ ((sp + 2256#64) ↦ₛ ct) ∗
    memRegion (sp + 6192#64) 5664 ∗ memRegion (sp + 20736#64) 1664 ∗
    memRegion (sp + 22432#64) 3184 ∗ memRegion (sp + 25648#64) 16 ∗
    (dkA ↦ₛ dk.take 1152) ∗ ((dkA + 2304#64) ↦ₛ rho) ∗ (ct1A ↦ₛ ct1) ∗ (ct2A ↦ₛ ct2) ∗ F
  have hP3' : P3 ⊢ memRegion (sp + 8#64) 128 ∗ memRegion (sp + 4432#64) 32 ∗
      (((sp + 20704#64) ↦ₛ m') ∗ ((sp + 1840#64) ↦₆₄ (dkA + 2336#64)) ∗
        VecRangeMem 2 (dkA + 2336#64) (bytesToVecNat hPk) ∗
        memRegion (sp + 4464#64) 32 ∗ memRegion (sp + 5680#64) 64 ∗
        memRegion (sp + 22400#64) 32 ∗ memRegion (sp + 4496#64) 1184 ∗
        memRegion (sp + 11856#64) 1120 ∗ ((sp + 1856#64) ↦₆₄ (dkA + 2368#64)) ∗
        ((sp + 3344#64) ↦ₛ ct) ∗ ((dkA + 2368#64) ↦ₛ z) ∗ stackAt sp 1136 ∗
        memRegion (sp + 192#64) 8 ∗ memRegion (sp + 5744#64) 448 ∗
        memRegion (sp + 12976#64) 7728 ∗ memRegion (sp + 25616#64) 32 ∗
        ((sp + 1872#64) ↦₆₄ dkA) ∗ Vec128At (sp + 1904#64) cst16_3_val ∗
        ((dkA + 1152#64) ↦ₛ pk0) ∗ ((dkA + 1536#64) ↦ₛ pk1) ∗ ((dkA + 1920#64) ↦ₛ pk2) ∗
        R_common) := by
    refine Entails.trans hP3 ?_
    dsimp only [Seg3Spatial, R_common, sp, ct, m', pk0, pk1, pk2, rho, hPk, z]
    rw [dk_seg4_split dkA hdk, hhPk_vec, memRegion_136_split (s0.sp - 25824#64),
      memRegion_56_split (s0.sp - 25824#64), memRegion_16272_seg4_split (s0.sp - 25824#64),
      memRegion_4928_seg4_split (s0.sp - 25824#64)]
    sep_frame
  refine SepWP.weaken_pre hP3' ?_
  refine sepWP_elim_wordRangeMem 32 (sp + 8#64) (by decide) fun fw => ?_
  refine SepWP.weaken_pre (show _ ⊢ memRegion (sp + 4432#64) 32 ∗ (WordRangeMem 32 (sp + 8#64) fw ∗ _)
    by sep_frame) ?_
  refine sepWP_elim_byteRangeMem 32 (sp + 4432#64) (by decide) fun fb => ?_
  refine SepWP.weaken_pre (show _ ⊢ ((sp + 20704#64) ↦ₛ m') ∗ WordRangeMem 32 (sp + 8#64) fw ∗
      Seg4Pure.ByteRangeMem 32 (sp + 4432#64) fb ∗ ((sp + 1840#64) ↦₆₄ (dkA + 2336#64)) ∗
      VecRangeMem 2 (dkA + 2336#64) (bytesToVecNat hPk) ∗ _ by sep_frame) ?_
  refine sepWP_seq_env hcl3 hro3
    (seg4a_prep1 hb hbase s3 sp dkA m' hPk fw fb _ hm'_len hpc3 hrun3 hsp3 hspA3) ?_
  rintro s4p1 P4p1 hpc4p1 hrun4p1 hcl4p1 hro4p1
    ⟨hsp4p1, hspA4p1, hx0_p1, hx1_p1, hx2_p1, hx10_p1, hx20_p1, hx21_p1, hx23_p1,
      hx26_p1, hx28_p1, hfp_p1, hx8_p1, hx12_p1, hq0_p1, hq1_p1, fw1, fb1, hfw1, hfb1, hP4p1⟩
  refine SepWP.weaken_pre hP4p1 ?_
  refine SepWP.of_memRegion_vecRangeMem 2 (sp + 4464#64) (by decide)
    (sepProp_ext (by sep_frame) (by sep_frame)) fun fh => ?_
  refine SepWP.of_memRegion_vecRangeMem 4 (sp + 5680#64) (by decide)
    (sepProp_ext (by sep_frame) (by sep_frame)) fun fz => ?_
  refine SepWP.weaken_pre (show _ ⊢ memRegion (sp + 22400#64) 32 ∗ _ by sep_frame) ?_
  refine sepWP_elim_region32 fun v0 v1 v2 v3 => ?_
  refine SepWP.weaken_pre (show _ ⊢ ((sp + 20704#64) ↦ₛ m') ∗ WordRangeMem 32 (sp + 8#64) fw1 ∗
      Seg4Pure.ByteRangeMem 32 (sp + 4432#64) fb1 ∗ VecRangeMem 2 (sp + 4464#64) fh ∗
      VecRangeMem 4 (sp + 5680#64) fz ∗ ((sp + 22400#64) ↦₆₄ v0) ∗ ((sp + 22408#64) ↦₆₄ v1) ∗
      ((sp + 22416#64) ↦₆₄ v2) ∗ ((sp + 22424#64) ↦₆₄ v3) ∗ _ by sep_frame) ?_
  refine sepWP_seq_env hcl4p1 hro4p1
    (seg4a_prep2 hb hbase s4p1 sp m' hPk fw1 fb1 fh fz v0 v1 v2 v3 _ hm'_len hhPk_len
      hpc4p1 hrun4p1 hsp4p1 hspA4p1 hx0_p1 hx1_p1 hx2_p1 hx10_p1 hx20_p1 hx21_p1
      hx8_p1 hx12_p1 hq0_p1 hq1_p1 hfw1 hfb1) ?_
  rintro s4p2 P4p2 hpc4p2 hrun4p2 hcl4p2 hro4p2
    ⟨hsp4p2, hspA4p2, hx0_p2, hx1_p2, hx2_p2, hx20_p2, hx21_p2, hx23_p2,
      hx26_p2, hx28_p2, hfp_p2, hP4p2⟩
  refine SepWP.weaken_pre (Entails.trans hP4p2 (show _ ⊢
      CommonBase.Keccak2SlicesRW (sp + 22400#64) (sp + 4432#64) (sp + 4432#64)
        (m' ++ hPk).length (m' ++ hPk).length ∗
      ((sp + 4432#64) ↦ₛ (m' ++ hPk)) ∗ memRegion (sp + 4496#64) 1184 ∗
      memRegion (sp + 5680#64) 64 ∗ memRegion (sp + 11856#64) 1120 ∗
      ((sp + 1856#64) ↦₆₄ (dkA + 2368#64)) ∗ ((sp + 3344#64) ↦ₛ ct) ∗
      ((dkA + 2368#64) ↦ₛ z) ∗ stackAt sp 1136 ∗ _ by sep_frame)) ?_
  refine sepWP_seq_env hcl4p2 hro4p2
    (seg4a_hashes_a hb hbase s4p2 sp (dkA + 2368#64) (m' ++ hPk) z ct _
      hmsg_len hz_len hct_len hpc4p2 hrun4p2 hsp4p2 hspA4p2 hx0_p2 hx1_p2 hx2_p2 hx21_p2
      hcl4p2 hro4p2) ?_
  rintro s4h P4h hpc4h hrun4h hcl4h hro4h
    ⟨hsp4h, hspA4h, hx20_h, hx21_h, hx23_h, hx26_h, hx28_h, hfp_h, hP4h⟩
  have hP4h' : P4h ⊢ memRegion (sp + 11856#64) 32 ∗ memRegion (sp + 25616#64) 32 ∗
      (((sp + 4496#64) ↦ₛ sha3_512List (m' ++ hPk)) ∗ ((sp + 4560#64) ↦ₛ (z ++ ct)) ∗
        memRegion (sp + 4432#64) 64 ∗ memRegion (sp + 5680#64) 32 ∗
        memRegion (sp + 5712#64) 32 ∗ memRegion (sp + 11888#64) 480 ∗
        memRegion (sp + 12368#64) 5664 ∗ memRegion (sp + 18032#64) 2672 ∗
        memRegion (sp + 22400#64) 32 ∗ ((sp + 1856#64) ↦₆₄ (dkA + 2368#64)) ∗
        ((sp + 3344#64) ↦ₛ ct) ∗ ((dkA + 2368#64) ↦ₛ z) ∗ stackAt sp 1136 ∗
        WordRangeMem 32 (sp + 8#64) (msgWordFn m') ∗ ((sp + 20704#64) ↦ₛ m') ∗
        ((sp + 1840#64) ↦₆₄ (dkA + 2336#64)) ∗ VecRangeMem 2 (dkA + 2336#64) (bytesToVecNat hPk) ∗
        memRegion (sp + 192#64) 8 ∗ memRegion (sp + 5744#64) 448 ∗
        ((sp + 1872#64) ↦₆₄ dkA) ∗ Vec128At (sp + 1904#64) cst16_3_val ∗
        ((dkA + 1152#64) ↦ₛ pk0) ∗ ((dkA + 1536#64) ↦ₛ pk1) ∗ ((dkA + 1920#64) ↦ₛ pk2) ∗
        R_common) := by
    refine Entails.trans hP4h ?_
    have hsplit := memRegion_mid_b01_split sp
    refine Entails.trans (show _ ⊢ (memRegion (sp + 5680#64) 64 ∗ memRegion (sp + 11856#64) 1120 ∗
        memRegion (sp + 12976#64) 7728) ∗ _ by sep_frame) ?_
    rw [hsplit]; sep_frame
  refine SepWP.weaken_pre hP4h' ?_
  refine sepWP_seq_env hcl4h hro4h
    (seg4a_prep_b01 hb hbase s4h sp (z ++ ct) _ hzct_len hpc4h hrun4h hsp4h hspA4h hx21_h
      ((hfp_h.trans (hfp_p2.trans (hfp_p1.trans hfp3))).trans hfp_sp)) ?_
  rintro s4pb P4pb hpc4pb hrun4pb hcl4pb hro4pb
    ⟨hsp4pb, hspA4pb, hx0_pb, hx1_pb, hx2_pb, hx3_pb, hx4_pb, hx20_pb, hx21_pb,
      hx23_pb, hx26_pb, hx28_pb, hfp_pb, hP4pb⟩
  refine SepWP.weaken_pre (Entails.trans hP4pb (show _ ⊢
      CommonBase.Keccak2SlicesRW (sp + 11856#64) (sp + 4560#64) (sp + 4560#64)
        (z ++ ct).length (z ++ ct).length ∗
      ((sp + 4560#64) ↦ₛ (z ++ ct)) ∗ memRegion (sp + 25616#64) 32 ∗
      memRegion (sp + 5680#64) 32 ∗ memRegion (sp + 192#64) 8 ∗
      memRegion (sp + 12368#64) 5664 ∗ stackAt sp 1136 ∗ _ by sep_frame)) ?_
  refine sepWP_seq_env hcl4pb hro4pb
    (seg4a_call_b01 hb hbase s4pb sp (z ++ ct) _ hzct_len hpc4pb hrun4pb hsp4pb hspA4pb
      hx0_pb hx1_pb hx2_pb hx3_pb hx4_pb hx21_pb hcl4pb hro4pb) ?_
  rintro s4cb P4cb hpc4cb hrun4cb hcl4cb _
    ⟨hsp4cb, hspA4cb, hx20_cb, hx23_cb, hx26_cb, hx28_cb, hfp_cb, hP4cb⟩
  have hP4cb' : P4cb ⊢ ((sp + 1872#64) ↦₆₄ dkA) ∗ Vec128At (sp + 1904#64) cst16_3_val ∗
      memRegion (sp + 5680#64) 512 ∗ memRegion (sp + 11856#64) 1536 ∗
      ((dkA + 1152#64) ↦ₛ pk0) ∗ ((dkA + 1536#64) ↦ₛ pk1) ∗ ((dkA + 1920#64) ↦ₛ pk2) ∗
      (memRegion (sp + 4560#64) 1120 ∗ memRegion (sp + 13392#64) 4640 ∗
        ((sp + 192#64) ↦₆₄ (sp + 13392#64)) ∗ ((sp + 25616#64) ↦ₛ shake256List 32 (z ++ ct)) ∗
        stackAt sp 1136 ∗ ((sp + 4496#64) ↦ₛ sha3_512List (m' ++ hPk)) ∗
        memRegion (sp + 4432#64) 64 ∗ memRegion (sp + 18032#64) 2672 ∗
        memRegion (sp + 22400#64) 32 ∗ ((sp + 1856#64) ↦₆₄ (dkA + 2368#64)) ∗
        ((sp + 3344#64) ↦ₛ ct) ∗ ((dkA + 2368#64) ↦ₛ z) ∗
        WordRangeMem 32 (sp + 8#64) (msgWordFn m') ∗ ((sp + 20704#64) ↦ₛ m') ∗
        ((sp + 1840#64) ↦₆₄ (dkA + 2336#64)) ∗ VecRangeMem 2 (dkA + 2336#64) (bytesToVecNat hPk) ∗
        R_common) := by
    refine Entails.trans hP4cb ?_
    have hsplit := memRegion_post_b01_split sp
    refine Entails.trans (show _ ⊢ (memRegion (sp + 4560#64) 1152 ∗ memRegion (sp + 5712#64) 32 ∗
        memRegion (sp + 5744#64) 448 ∗ memRegion (sp + 11856#64) 32 ∗
        memRegion (sp + 11888#64) 480 ∗ memRegion (sp + 12368#64) 5664) ∗ _ by sep_frame) ?_
    rw [hsplit]; dsimp only [cst16_3_val]; sep_frame
  refine SepWP.weaken_pre hP4cb' ?_
  refine SepWP.mono
    (seg4b_ok hb hbase s4cb sp dkA pk0 pk1 pk2 _ hpk0_len hpk1_len hpk2_len
      hpc4cb hrun4cb hsp4cb hspA4cb hcl4cb
      (hx20_cb.trans (hx20_pb.trans (hx20_h.trans hx20_p2)))
      (hx23_cb.trans (hx23_pb.trans (hx23_h.trans (hx23_p2.trans (hx23_p1.trans hx23_3)))))) ?_
  rintro sf Pf _ _ ⟨hsp_f, hspA_f, hx9_f, hx10_f, hx23_f, hx26_f, hx27_f, hx28_f, hfp_f, hPf⟩
  refine ⟨hsp_f, hspA_f,
    (hfp_f.trans (hfp_cb.trans hfp_pb)).trans hfp_sp.symm,
    hx9_f, hx10_f, hx23_f,
    hx26_f.trans (hx26_cb.trans (hx26_pb.trans (hx26_h.trans (hx26_p2.trans (hx26_p1.trans hx26_3))))),
    hx27_f,
    hx28_f.trans (hx28_cb.trans (hx28_pb.trans (hx28_h.trans (hx28_p2.trans (hx28_p1.trans hx28_3))))),
    ?_⟩
  refine Entails.trans hPf ?_
  dsimp only [Seg4Spatial, R_common, sp, ct, m', pk0, pk1, pk2, rho, hPk, z]
  rw [← hhPk_vec, dk_seg4_split dkA hdk, ← memRegion_6176_seg4_join (s0.sp - 25824#64)]
  have hj2048 := memRegion_2048_seg4_join (s0.sp - 25824#64)
    (dkA + 2336#64) (dkA + 2368#64) dkA (dkA + 384#64) cst16_3_val
  have hj12224 := memRegion_12224_seg4_join (s0.sp - 25824#64) hm'_len
  refine Entails.trans (show _ ⊢
      (memRegion (s0.sp - 25824#64 + 208#64) 1632 ∗
        ((s0.sp - 25824#64 + 1840#64) ↦₆₄ (dkA + 2336#64)) ∗ memRegion (s0.sp - 25824#64 + 1848#64) 8 ∗
        ((s0.sp - 25824#64 + 1856#64) ↦₆₄ (dkA + 2368#64)) ∗ memRegion (s0.sp - 25824#64 + 1864#64) 8 ∗
        ((s0.sp - 25824#64 + 1872#64) ↦₆₄ dkA) ∗ memRegion (s0.sp - 25824#64 + 1880#64) 8 ∗
        ((s0.sp - 25824#64 + 1888#64) ↦₆₄ (dkA + 384#64)) ∗ memRegion (s0.sp - 25824#64 + 1896#64) 8 ∗
        Vec128At (s0.sp - 25824#64 + 1904#64) cst16_3_val ∗ memRegion (s0.sp - 25824#64 + 1920#64) 336) ∗
      (memRegion (s0.sp - 25824#64 + 13392#64) 4640 ∗ memRegion (s0.sp - 25824#64 + 18032#64) 2672 ∗
        ((s0.sp - 25824#64 + 20704#64) ↦ₛ indCpaDecrypt 3 10 4 (dk.take 1152) (ct1 ++ ct2)) ∗
        memRegion (s0.sp - 25824#64 + 20736#64) 1664 ∗ memRegion (s0.sp - 25824#64 + 22400#64) 32 ∗
        memRegion (s0.sp - 25824#64 + 22432#64) 3184) ∗ _ by sep_frame) ?_
  refine Entails.trans (sepConj_mono hj2048 (sepConj_mono_left hj12224)) ?_
  sep_frame

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4
