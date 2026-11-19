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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1b

/-!
# `encapsulate2` (`B20`) — Segment 1 (`+0x0000 .. +0x04b8`)

Composes `Seg1a` (`+0x0000 .. +0x0188`) and `Seg1b` (`+0x0188 .. +0x04b8`) into `seg1_ok`,
delivering `Seg1Post` and `Seg1Spatial` at `+0x04b8`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1

open Arm64 Arm64.Obj ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase
  MlKemPlacement
  mlkemMpl
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (bytesToPoly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  SavedFrame20
  UnspilledSaved20
  blkPC20
  blkPl20
  sepWP_seq_env
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Oct8
  Oct8Mem
  Poly32Mem
  PolyMem
  SepWP.of_memRegion_vecRangeMem
  Vec128At
  Vec32
  VecRangeMem
  bytesToVecNat
  oct8Mem_entails_memRegion
  oct8Mem_ofFn
  pointsToBytes_eq_vecRangeMem
  poly32Mem_entails_memRegion
  poly32Mem_ofFn
  polyMem_bytesToPoly16
  polyVecNat
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  entails_sub
  seg1_copy_r0
  seg1_copy_r1
  seg1_prologue
  seg1_setup
  trans_unspilled
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1b (
  seg1_copy_e2a
  seg1_copy_e2b
  seg1_copy_r2a
  seg1_copy_r2b
  seg1_zero1
  seg1_zero2
)

/-! ## 1. `es` (`2080`B) & Stack (`6000`B) Decompositions -/

@[expose] def esVec0 (es : List (BitVec 8)) : Vec32 :=
  Vec32.ofFn (polyVecNat (bytesToPoly16 (es.take 512)))

@[expose] def esVec1 (es : List (BitVec 8)) : Vec32 :=
  Vec32.ofFn (polyVecNat (bytesToPoly16 ((es.drop 512).take 512)))

@[expose] def esVec2 (es : List (BitVec 8)) : Vec32 :=
  Vec32.ofFn (polyVecNat (bytesToPoly16 ((es.drop 1024).take 512)))

@[expose] def esVec3 (es : List (BitVec 8)) : Vec32 :=
  Vec32.ofFn (polyVecNat (bytesToPoly16 ((es.drop 1536).take 512)))

@[expose] def esMsg0 (es : List (BitVec 8)) : BitVec 128 :=
  bytesToVecNat ((es.drop 2048).take 32) 0

@[expose] def esMsg1 (es : List (BitVec 8)) : BitVec 128 :=
  bytesToVecNat ((es.drop 2048).take 32) 1

private theorem list_split_2080 {α : Type} {xs : List α} (h : xs.length = 2080) :
    xs = xs.take 512 ++ ((xs.drop 512).take 512 ++
      ((xs.drop 1024).take 512 ++ ((xs.drop 1536).take 512 ++ (xs.drop 2048).take 32))) := by
  have h4 : (xs.drop 1536).take 512 ++ (xs.drop 2048).take 32 = xs.drop 1536 := by
    have hd : xs.drop 2048 = (xs.drop 1536).drop 512 := by rw [List.drop_drop]
    have ht : (xs.drop 2048).take 32 = xs.drop 2048 :=
      List.take_of_length_le (by simp [h])
    rw [ht, hd, List.take_append_drop]
  have h3 : (xs.drop 1024).take 512 ++ xs.drop 1536 = xs.drop 1024 := by
    have hd : xs.drop 1536 = (xs.drop 1024).drop 512 := by rw [List.drop_drop]
    rw [hd, List.take_append_drop]
  have h2 : (xs.drop 512).take 512 ++ xs.drop 1024 = xs.drop 512 := by
    have hd : xs.drop 1024 = (xs.drop 512).drop 512 := by rw [List.drop_drop]
    rw [hd, List.take_append_drop]
  rw [h4, h3, h2, List.take_append_drop]

private theorem vecRangeMem2_eq (ptr : BitVec 64) (f : Nat → BitVec 128) :
    VecRangeMem 2 ptr f = Vec128At ptr (f 0) ∗ Vec128At (ptr + 16#64) (f 1) := by
  simp [VecRangeMem]

theorem es_pointsTo_split (esA : BitVec 64) {es : List (BitVec 8)} (hes : es.length = 2080) :
    (esA ↦ₛ es) =
      Poly32Mem esA (esVec0 es) ∗
      Poly32Mem (esA + 512#64) (esVec1 es) ∗
      Poly32Mem (esA + 1024#64) (esVec2 es) ∗
      Poly32Mem (esA + 1536#64) (esVec3 es) ∗
      Vec128At (esA + 2048#64) (esMsg0 es) ∗
      Vec128At (esA + 2064#64) (esMsg1 es) := by
  have l0 : (es.take 512).length = 512 := by simp [hes]
  have l1 : ((es.drop 512).take 512).length = 512 := by simp [hes]
  have l2 : ((es.drop 1024).take 512).length = 512 := by simp [hes]
  have l3 : ((es.drop 1536).take 512).length = 512 := by simp [hes]
  have lm : ((es.drop 2048).take 32).length = 32 := by simp [hes]
  conv_lhs => rw [list_split_2080 hes]
  rw [pointsToBytes_append, l0,
    pointsToBytes_append, l1,
    pointsToBytes_append, l2,
    pointsToBytes_append, l3]
  have a1 : esA + BitVec.ofNat 64 512 = esA + 512#64 := rfl
  have a2 : esA + 512#64 + BitVec.ofNat 64 512 = esA + 1024#64 := by bv_omega
  have a3 : esA + 1024#64 + BitVec.ofNat 64 512 = esA + 1536#64 := by bv_omega
  have a4 : esA + 1536#64 + BitVec.ofNat 64 512 = esA + 2048#64 := by bv_omega
  have a5 : esA + 2048#64 + 16#64 = esA + 2064#64 := by bv_omega
  rw [a1, a2, a3, a4,
    polyMem_bytesToPoly16 esA l0, ← poly32Mem_ofFn,
    polyMem_bytesToPoly16 (esA + 512#64) l1, ← poly32Mem_ofFn,
    polyMem_bytesToPoly16 (esA + 1024#64) l2, ← poly32Mem_ofFn,
    polyMem_bytesToPoly16 (esA + 1536#64) l3, ← poly32Mem_ofFn,
    pointsToBytes_eq_vecRangeMem 2 (esA + 2048#64) lm, vecRangeMem2_eq, a5]
  rfl

theorem msg_vec128_eq_pointsTo (ptr : BitVec 64) {es : List (BitVec 8)} (hes : es.length = 2080) :
    Vec128At ptr (esMsg0 es) ∗ Vec128At (ptr + 16#64) (esMsg1 es) =
      (ptr ↦ₛ ((es.drop 2048).take 32)) := by
  have lm : ((es.drop 2048).take 32).length = 32 := by simp [hes]
  rw [pointsToBytes_eq_vecRangeMem 2 ptr lm, vecRangeMem2_eq]
  rfl

private theorem frame6000_seg1_split (sp : BitVec 64) :
    memRegion sp 6000 =
      memRegion (sp + 208#64) 512 ∗
      memRegion (sp + 720#64) 512 ∗
      memRegion (sp + 1232#64) 512 ∗
      memRegion (sp + 1744#64) 512 ∗
      memRegion (sp + 2256#64) 32 ∗
      memRegion (sp + 2288#64) 128 ∗
      memRegion (sp + 4976#64) 512 ∗
      memRegion (sp + 5488#64) 512 ∗
      memRegion sp 208 ∗
      memRegion (sp + 2416#64) 2560 := by
  rw [memRegion_split' (b' := sp + 208#64) (n := 208) (k := (5792 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 720#64) (n := 512) (k := (5280 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 1232#64) (n := 512) (k := (4768 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 1744#64) (n := 512) (k := (4256 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 2256#64) (n := 512) (k := (3744 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 2288#64) (n := 32) (k := (3712 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 2416#64) (n := 128) (k := (3584 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 4976#64) (n := 2560) (k := (1024 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 5488#64) (n := 512) (k := 512) rfl (by bv_omega) (by decide)]
  exact sepProp_ext (by sep_frame) (by sep_frame)

/-! ## 2. Exported Segment 1 Contract (`+0x0000 → +0x04b8`) -/

@[expose] def Seg1Post (s0 s1 : State) (ret ekA : BitVec 64) : Prop :=
  let sp := s0.sp - 6128#64
  s1.sp = sp ∧
  s1.spAligned = true ∧
  s1.readReg64 .x1 = ekA ∧
  s1.readReg64 .x8 = 0#64 ∧
  s1.readReg64 .x9 = sp + 5488#64 ∧
  s1.readReg64 .x19 = ret ∧
  s1.readReg64 .x20 = ekA + 384#64 ∧
  s1.readReg64 .x21 = sp + 3952#64 ∧
  s1.readReg64 .x22 = ekA + 384#64 ∧
  s1.readVReg128 0#5 = 0#128 ∧
  s1.readVReg128 1#5 = 0xfffc0000fffc0000fffc0000fffc0000#128 ∧
  s1.readVReg128 3#5 = 0x0b0a0a09080707060504040302010100#128 ∧
  UnspilledSaved20 s0 s1

@[expose] def Seg1Spatial (s0 : State) (esA : BitVec 64) (es : List (BitVec 8))
    (F : SepProp) : SepProp :=
  let sp := s0.sp - 6128#64
  (esA ↦ₛ es) ∗
  SavedFrame20 s0.sp s0 ∗
  memRegion sp 208 ∗
  PolyMem (sp + 208#64) (polyVecNat (bytesToPoly16 (es.take 512))) ∗
  PolyMem (sp + 720#64) (polyVecNat (bytesToPoly16 ((es.drop 512).take 512))) ∗
  PolyMem (sp + 1232#64) (polyVecNat (bytesToPoly16 ((es.drop 1024).take 512))) ∗
  PolyMem (sp + 1744#64) (polyVecNat (bytesToPoly16 ((es.drop 1536).take 512))) ∗
  ((sp + 2256#64) ↦ₛ ((es.drop 2048).take 32)) ∗
  memRegion (sp + 2288#64) 128 ∗
  memRegion (sp + 2416#64) 2560 ∗
  memRegion (sp + 4976#64) 512 ∗
  Poly32Mem (sp + 5488#64) Vec32.zero ∗ F

private theorem seg1_final_entails (s0 : State) (esA : BitVec 64) {es : List (BitVec 8)}
    (hes : es.length = 2080) (F : SepProp) :
    let sp := s0.sp - 6128#64
    Poly32Mem (sp + 5488#64) Vec32.zero ∗
      Oct8Mem (sp + 2288#64) Oct8.zero ∗
      Poly32Mem (sp + 4976#64) Vec32.zero ∗
      Poly32Mem (esA + 1536#64) (esVec3 es) ∗
      Poly32Mem (sp + 1744#64) (esVec3 es) ∗
      Vec128At (sp + 2256#64) (esMsg0 es) ∗
      Vec128At (sp + 2272#64) (esMsg1 es) ∗
      Poly32Mem (esA + 1024#64) (esVec2 es) ∗
      Poly32Mem (sp + 1232#64) (esVec2 es) ∗
      Poly32Mem (esA + 512#64) (esVec1 es) ∗
      Poly32Mem (sp + 720#64) (esVec1 es) ∗
      Poly32Mem esA (esVec0 es) ∗
      Poly32Mem (sp + 208#64) (esVec0 es) ∗
      Vec128At (esA + 2048#64) (esMsg0 es) ∗
      Vec128At (esA + 2064#64) (esMsg1 es) ∗
      SavedFrame20 s0.sp s0 ∗
      memRegion sp 208 ∗
      memRegion (sp + 2416#64) 2560 ∗ F ⊢
      Seg1Spatial s0 esA es F := by
  intro sp
  unfold Seg1Spatial
  rw [es_pointsTo_split esA hes]
  have hm_eq : Vec128At (sp + 2256#64) (esMsg0 es) ∗ Vec128At (sp + 2272#64) (esMsg1 es) =
      ((sp + 2256#64) ↦ₛ ((es.drop 2048).take 32)) := by
    have ha : sp + 2256#64 + 16#64 = sp + 2272#64 := by bv_omega
    rw [← ha, msg_vec128_eq_pointsTo (sp + 2256#64) hes]
  have hr0 : Poly32Mem (sp + 208#64) (esVec0 es) =
      PolyMem (sp + 208#64) (polyVecNat (bytesToPoly16 (es.take 512))) := poly32Mem_ofFn _ _
  have hr1 : Poly32Mem (sp + 720#64) (esVec1 es) =
      PolyMem (sp + 720#64) (polyVecNat (bytesToPoly16 ((es.drop 512).take 512))) :=
    poly32Mem_ofFn _ _
  have hr2 : Poly32Mem (sp + 1232#64) (esVec2 es) =
      PolyMem (sp + 1232#64) (polyVecNat (bytesToPoly16 ((es.drop 1024).take 512))) :=
    poly32Mem_ofFn _ _
  have he2 : Poly32Mem (sp + 1744#64) (esVec3 es) =
      PolyMem (sp + 1744#64) (polyVecNat (bytesToPoly16 ((es.drop 1536).take 512))) :=
    poly32Mem_ofFn _ _
  rw [hr0, hr1, hr2, he2]
  have hz8 := oct8Mem_entails_memRegion (sp + 2288#64) Oct8.zero
  have hz4976 := poly32Mem_entails_memRegion (sp + 4976#64) Vec32.zero
  exact entails_sub (Entails.of_eq hm_eq) (by sep_frame)
    (entails_sub hz8 (by sep_frame)
      (entails_sub hz4976 (by sep_frame) (by sep_frame)))

theorem seg1_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl20 b) (hbase : blkPl20.base = b)
    (s0 : State) (ret esA ekA : BitVec 64) (es : List (BitVec 8)) (F : SepProp)
    (hpc : s0.pc = b)
    (hrun : s0.status = .Running)
    (hsp0 : s0.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s0.mem)
    (hro : MlKemRoOk mlkemMpl s0.mem)
    (hx8 : s0.readReg64 .x8 = ret)
    (hx0 : s0.readReg64 .x0 = esA)
    (hx1 : s0.readReg64 .x1 = ekA)
    (hes : es.length = 2080) :
    SepWP (blkPC20.rebase b (fun _ => none)) (b + 0x04b8#64) s0
      ((esA ↦ₛ es) ∗ stackAt s0.sp 6128 ∗ F)
      (fun s1 P1 => Seg1Post s0 s1 ret ekA ∧ (P1 ⊢ Seg1Spatial s0 esA es F)) := by
  let sp := s0.sp - 6128#64
  refine SepWP.weaken_pre (P' := stackAt s0.sp 6128 ∗ (esA ↦ₛ es) ∗ F) (by sep_frame) ?_
  refine sepWP_seq_env hcl hro
    (seg1_prologue hb hbase s0 ret esA ekA ((esA ↦ₛ es) ∗ F) hpc hrun hsp0 hx8 hx0 hx1) ?_
  intro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspal1, hx0_1, hx1_1, hx9_1, hx19_1, hus1, hP1⟩
  refine SepWP.weaken_pre hP1 ?_
  rw [es_pointsTo_split esA hes, frame6000_seg1_split sp]
  refine SepWP.of_memRegion_vecRangeMem 32 (sp + 208#64) (by decide) (by sep_focus) fun f208 => ?_
  refine SepWP.of_memRegion_vecRangeMem 32 (sp + 720#64) (by decide) (by sep_focus) fun f720 => ?_
  refine SepWP.of_memRegion_vecRangeMem 32 (sp + 1232#64) (by decide) (by sep_focus) fun f1232 => ?_
  refine SepWP.of_memRegion_vecRangeMem 32 (sp + 1744#64) (by decide) (by sep_focus) fun f1744 => ?_
  refine SepWP.of_memRegion_vecRangeMem 2 (sp + 2256#64) (by decide) (by sep_focus) fun f2256 => ?_
  refine SepWP.of_memRegion_vecRangeMem 8 (sp + 2288#64) (by decide) (by sep_focus) fun f2288 => ?_
  refine SepWP.of_memRegion_vecRangeMem 32 (sp + 4976#64) (by decide) (by sep_focus) fun f4976 => ?_
  refine SepWP.of_memRegion_vecRangeMem 32 (sp + 5488#64) (by decide) (by sep_focus) fun f5488 => ?_
  have hw208 : VecRangeMem 32 (sp + 208#64) f208 = Poly32Mem (sp + 208#64) (Vec32.ofFn f208) :=
    (poly32Mem_ofFn _ _).symm
  have hw720 : VecRangeMem 32 (sp + 720#64) f720 = Poly32Mem (sp + 720#64) (Vec32.ofFn f720) :=
    (poly32Mem_ofFn _ _).symm
  have hw1232 : VecRangeMem 32 (sp + 1232#64) f1232 =
      Poly32Mem (sp + 1232#64) (Vec32.ofFn f1232) := (poly32Mem_ofFn _ _).symm
  have hw1744 : VecRangeMem 32 (sp + 1744#64) f1744 =
      Poly32Mem (sp + 1744#64) (Vec32.ofFn f1744) := (poly32Mem_ofFn _ _).symm
  have hw2256 : VecRangeMem 2 (sp + 2256#64) f2256 =
      Vec128At (sp + 2256#64) (f2256 0) ∗ Vec128At (sp + 2272#64) (f2256 1) := by
    have ha : sp + 2256#64 + 16#64 = sp + 2272#64 := by bv_omega
    rw [vecRangeMem2_eq, ha]
  have hw2288 : VecRangeMem 8 (sp + 2288#64) f2288 = Oct8Mem (sp + 2288#64) (Oct8.ofFn f2288) :=
    (oct8Mem_ofFn _ _).symm
  have hw4976 : VecRangeMem 32 (sp + 4976#64) f4976 =
      Poly32Mem (sp + 4976#64) (Vec32.ofFn f4976) := (poly32Mem_ofFn _ _).symm
  have hw5488 : VecRangeMem 32 (sp + 5488#64) f5488 =
      Poly32Mem (sp + 5488#64) (Vec32.ofFn f5488) := (poly32Mem_ofFn _ _).symm
  rw [hw208, hw720, hw1232, hw1744, hw2256, hw2288, hw4976, hw5488]
  have stepf : ∀ {prog : Program} {pc1 pc2 : BitVec 64} {s : State} {P P1 : SepProp}
      {Q1 Q2 : State → SepProp → Prop},
      mlkemMultiLib.CodeLoaded mlkemMpl s.mem → MlKemRoOk mlkemMpl s.mem →
      SepWP prog pc1 s P1 Q1 → (P ⊢ P1) →
      (∀ s' P', s'.pc = pc1 → s'.status = .Running →
        mlkemMultiLib.CodeLoaded mlkemMpl s'.mem → MlKemRoOk mlkemMpl s'.mem →
        Q1 s' P' → SepWP prog pc2 s' P' Q2) →
      SepWP prog pc2 s P Q2 :=
    fun hcl' hro' h1 hP' h2 => SepWP.weaken_pre hP' (sepWP_seq_env hcl' hro' h1 h2)
  refine stepf hcl1 hro1
    (seg1_setup hb hbase s1 sp esA ekA (esVec0 es) (Vec32.ofFn f5488) (esMsg0 es) (esMsg1 es) _
      hpc1 hrun1 hsp1 hspal1 hro1 hx0_1 hx1_1 hx9_1) (by sep_frame) ?_
  intro s2 P2 hpc2 hrun2 hcl2 hro2
    ⟨hsp2, hspal2, hx0_2, hx1_2, hx8_2, hx9_2, hx19_2, hx20_2, hx21_2, hx22_2,
      hq0_2, hq2_2, hq3_2, hus2, hP2⟩
  refine stepf hcl2 hro2
    (seg1_copy_r0 hb hbase s2 esA sp (esVec0 es) (Vec32.ofFn f208) _
      hpc2 hrun2 hsp2 hspal2 hx0_2 hq0_2 hq2_2) (Entails.trans hP2 (by sep_frame)) ?_
  intro s3 P3 hpc3 hrun3 hcl3 hro3
    ⟨hsp3, hspal3, hx0_3, hx1_3, hx8_3, hx9_3, hx19_3, hx20_3, hx21_3, hx22_3, hq3_3, hus3, hP3⟩
  refine stepf hcl3 hro3
    (seg1_copy_r1 hb hbase s3 esA sp (esVec1 es) (esVec2 es) (Vec32.ofFn f720) _
      hpc3 hrun3 hsp3 hspal3 hx0_3) (Entails.trans hP3 (by sep_frame)) ?_
  intro s4 P4 hpc4 hrun4 hcl4 hro4
    ⟨hsp4, hspal4, hx0_4, hx1_4, hx8_4, hx9_4, hx19_4, hx20_4, hx21_4, hx22_4,
      hq1_4, hq2_4, hq3_4, hus4, hP4⟩
  refine stepf hcl4 hro4
    (seg1_copy_r2a hb hbase s4 esA sp (esVec2 es) (Vec32.ofFn f1232) _
      hpc4 hrun4 hsp4 hspal4 hx0_4 hq1_4 hq2_4) (Entails.trans hP4 (by sep_frame)) ?_
  intro s5 P5 hpc5 hrun5 hcl5 hro5
    ⟨hsp5, hspal5, hx0_5, hx1_5, hx8_5, hx9_5, hx19_5, hx20_5, hx21_5, hx22_5,
      hq0_5, hq1_5, hq3_5, hus5, t2m,
      ht0, ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9, ht10, ht11, ht12, ht13, ht14, ht15, ht17,
      hP5⟩
  refine stepf hcl5 hro5
    (seg1_copy_r2b hb hbase s5 esA sp (esVec2 es) (esVec3 es) t2m (Vec32.ofFn f1744) _
      hpc5 hrun5 hsp5 hspal5 hx0_5 hq0_5 hq1_5
      ⟨ht0, ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9, ht10, ht11, ht12, ht13, ht14, ht15, ht17⟩)
    (Entails.trans hP5 (by sep_frame)) ?_
  intro s6 P6 hpc6 hrun6 hcl6 hro6
    ⟨hsp6, hspal6, hx0_6, hx1_6, hx8_6, hx9_6, hx19_6, hx20_6, hx21_6, hx22_6,
      hq1_6, hq2_6, hq3_6, hus6, hP6⟩
  refine stepf hcl6 hro6
    (seg1_copy_e2a hb hbase s6 esA sp (esVec3 es) ((Vec32.ofFn f1744).set 0 (esVec3 es).v0) _
      hpc6 hrun6 hsp6 hspal6 hx0_6 hq1_6 hq2_6 rfl) (Entails.trans hP6 (by sep_frame)) ?_
  intro s7 P7 hpc7 hrun7 hcl7 hro7
    ⟨hsp7, hspal7, hx0_7, hx1_7, hx8_7, hx9_7, hx19_7, hx20_7, hx21_7, hx22_7,
      hq0_7, hq1_7, hq3_7, hus7, e2m,
      he0, he1, he2, he3, he4, he5, he6, he7, he8, he9, he10, he11, he12, he13, he14, he15, he16, he18,
      hP7⟩
  refine stepf hcl7 hro7
    (seg1_copy_e2b hb hbase s7 esA sp (esVec3 es) e2m
      (((Vec32.ofFn f5488).set 0 (esMsg0 es)).set 1 (esMsg1 es))
      (f2256 0) (f2256 1) (esMsg0 es) (esMsg1 es) _
      hpc7 hrun7 hsp7 hspal7 hx0_7 hq0_7 hq1_7 rfl rfl
      ⟨he0, he1, he2, he3, he4, he5, he6, he7, he8, he9, he10, he11, he12, he13, he14, he15, he16, he18⟩)
    (Entails.trans hP7 (by sep_frame)) ?_
  intro s8 P8 hpc8 hrun8 hcl8 hro8
    ⟨hsp8, hspal8, hx1_8, hx8_8, hx9_8, hx19_8, hx20_8, hx21_8, hx22_8,
      hq0_8, hq1_8, hq3_8, hus8, hP8⟩
  refine stepf hcl8 hro8
    (seg1_zero1 hb hbase s8 sp (Oct8.ofFn f2288) (Vec32.ofFn f4976) _
      hpc8 hrun8 hsp8 hspal8 hq0_8) (Entails.trans hP8 (by sep_frame)) ?_
  intro s9 P9 hpc9 hrun9 hcl9 hro9
    ⟨hsp9, hspal9, hx1_9, hx8_9, hx9_9, hx19_9, hx20_9, hx21_9, hx22_9,
      hq0_9, hq1_9, hq3_9, hus9, hP9⟩
  refine stepf hcl9 hro9
    (seg1_zero2 hb hbase s9 sp (((Vec32.ofFn f5488).set 0 (esMsg0 es)).set 1 (esMsg1 es)) _
      hpc9 hrun9 hsp9 hspal9 hq0_9) (Entails.trans hP9 (by sep_frame)) ?_
  intro sf Pf hpcf hrunf _ _
    ⟨hspf, hspalf, hx1_f, hx8_f, hx9_f, hx19_f, hx20_f, hx21_f, hx22_f,
      hq0_f, hq1_f, hq3_f, husf, hPf⟩
  refine SepWP.done hpcf hrunf ⟨?_, ?_⟩
  · refine ⟨hspf, hspalf, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hq0_f, ?_, ?_, ?_⟩
    · exact hx1_f.trans (hx1_9.trans (hx1_8.trans (hx1_7.trans (hx1_6.trans (hx1_5.trans
        (hx1_4.trans (hx1_3.trans hx1_2)))))))
    · exact hx8_f.trans (hx8_9.trans (hx8_8.trans (hx8_7.trans (hx8_6.trans (hx8_5.trans
        (hx8_4.trans (hx8_3.trans hx8_2)))))))
    · exact hx9_f.trans (hx9_9.trans (hx9_8.trans (hx9_7.trans (hx9_6.trans (hx9_5.trans
        (hx9_4.trans (hx9_3.trans hx9_2)))))))
    · exact hx19_f.trans (hx19_9.trans (hx19_8.trans (hx19_7.trans (hx19_6.trans (hx19_5.trans
        (hx19_4.trans (hx19_3.trans (hx19_2.trans hx19_1))))))))
    · exact hx20_f.trans (hx20_9.trans (hx20_8.trans (hx20_7.trans (hx20_6.trans (hx20_5.trans
        (hx20_4.trans (hx20_3.trans hx20_2)))))))
    · exact hx21_f.trans (hx21_9.trans (hx21_8.trans (hx21_7.trans (hx21_6.trans (hx21_5.trans
        (hx21_4.trans (hx21_3.trans hx21_2)))))))
    · exact hx22_f.trans (hx22_9.trans (hx22_8.trans (hx22_7.trans (hx22_6.trans (hx22_5.trans
        (hx22_4.trans (hx22_3.trans hx22_2)))))))
    · exact hq1_f.trans (hq1_9.trans hq1_8)
    · exact hq3_f.trans (hq3_9.trans (hq3_8.trans (hq3_7.trans (hq3_6.trans (hq3_5.trans
        (hq3_4.trans (hq3_3.trans hq3_2)))))))
    · exact trans_unspilled hus1 (trans_unspilled hus2 (trans_unspilled hus3
        (trans_unspilled hus4 (trans_unspilled hus5 (trans_unspilled hus6
          (trans_unspilled hus7 (trans_unspilled hus8 (trans_unspilled hus9 husf))))))))
  · exact Entails.trans hPf (Entails.trans (by sep_frame) (seg1_final_entails s0 esA hes F))

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1
