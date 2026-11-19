/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a

/-!
# `encapsulate2` (`B20`) — Segment 1b (`+0x0188 .. +0x04b8`)

Copying `rHat[2]` (`+0x0188 .. +0x0290`), `e2` & `m` (`+0x0290 .. +0x0398`), and zeroing the
scratch stack regions `[sp + 2288 .. sp + 2416)` and `[sp + 4976 .. sp + 6000)` (`+0x0398 .. +0x04b8`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1b

open Arm64 Arm64.Obj ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase
  MlKemPlacement
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  UnspilledSaved20
  blk20_code_eq
  blk20_tree_size
  blkLib20
  blkPC20
  blkPl20
  blkPlaceable20
  blkTree20
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Oct8
  Oct8Mem
  Poly32Mem
  SepLoad128
  SepStore128
  Vec128At
  Vec32
  step_ldrQ128
  step_strQ128
)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC20 blkLib20 blkTree20 blk20_code_eq blk20_tree_size
  via_placement blkPl20 blkPlaceable20 [0x0188 → 0x04b4]
end

attribute [local irreducible] blkPC20

@[simp, arm64_norm, wp_norm]
private theorem applySimdResult_ok (s : State) (rd : BitVec 5) (v : BitVec 128) :
    applySimdResult s rd (.ok v) = (s.writeVReg128 rd v).advancePC := rfl

@[simp, arm64_norm, wp_norm]
private theorem evalSimdModImmExt_mvni_4s_3_msl16 (vd : BitVec 128) :
    evalSimdModImmExt true true 0#3 26#5 3#5 vd =
      .ok 0xfffc0000fffc0000fffc0000fffc0000#128 := rfl

theorem seg1_copy_r2a [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl20 b) (_hbase : blkPl20.base = b)
    (s : State) (esA sp : BitVec 64) (r2 t2 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + 0x0188#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_al : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = esA)
    (hq1 : s.readVReg128 1#5 = r2.v2)
    (hq2 : s.readVReg128 2#5 = r2.v0) :
    SepWP (blkPC20.rebase b (fun _ => none)) (b + 0x0210#64) s
      (Poly32Mem (esA + 1024#64) r2 ∗ Poly32Mem (sp + 1232#64) t2 ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧
        s'.spAligned = true ∧
        s'.readReg64 .x0 = esA ∧
        s'.readReg64 .x1 = s.readReg64 .x1 ∧
        s'.readReg64 .x8 = s.readReg64 .x8 ∧
        s'.readReg64 .x9 = s.readReg64 .x9 ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x20 = s.readReg64 .x20 ∧
        s'.readReg64 .x21 = s.readReg64 .x21 ∧
        s'.readReg64 .x22 = s.readReg64 .x22 ∧
        s'.readVReg128 0#5 = r2.v16 ∧
        s'.readVReg128 1#5 = r2.v20 ∧
        s'.readVReg128 3#5 = s.readVReg128 3#5 ∧
        UnspilledSaved20 s s' ∧
        (∃ t2m : Vec32,
          t2m.v0 = r2.v0 ∧ t2m.v1 = r2.v1 ∧ t2m.v2 = r2.v2 ∧ t2m.v3 = r2.v3 ∧
          t2m.v4 = r2.v4 ∧ t2m.v5 = r2.v5 ∧ t2m.v6 = r2.v6 ∧ t2m.v7 = r2.v7 ∧
          t2m.v8 = r2.v8 ∧ t2m.v9 = r2.v9 ∧ t2m.v10 = r2.v10 ∧ t2m.v11 = r2.v11 ∧
          t2m.v12 = r2.v12 ∧ t2m.v13 = r2.v13 ∧ t2m.v14 = r2.v14 ∧ t2m.v15 = r2.v15 ∧
          t2m.v17 = r2.v17 ∧
          (P' ⊢ Poly32Mem (esA + 1024#64) r2 ∗ Poly32Mem (sp + 1232#64) t2m ∗ Rest))) := by
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hsp_al
  step_ldrQ 0 1; step_strQ 1 2; step_ldrQ 0 5; step_strQ 1 0
  step_ldrQ 0 3; step_strQ 1 1; step_ldrQ 0 4; step_strQ 1 5
  step_ldrQ 0 8; step_strQ 1 3; step_ldrQ 0 6; step_strQ 1 4
  step_ldrQ 0 7; step_strQ 1 8; step_ldrQ 0 11; step_strQ 1 6
  step_ldrQ 0 9; step_strQ 1 7; step_ldrQ 0 10; step_strQ 1 11
  step_ldrQ 0 14; step_strQ 1 9; step_ldrQ 0 12; step_strQ 1 10
  step_ldrQ 0 13; step_strQ 1 14; step_ldrQ 0 17; step_strQ 1 12
  step_ldrQ 0 15; step_strQ 1 13; step_ldrQ 0 16; step_strQ 1 17
  step_ldrQ 0 20; step_strQ 1 15
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simp [State.spAligned, hsp, hsp_chk],
      by simp [hx0], by simp, by simp, by simp, by simp, by simp, by simp, by simp,
      by simp [Vec32.get], by simp [Vec32.get], by simp,
      ⟨by simp, by simp, by simp, by simp⟩,
      ⟨_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Entails.refl _⟩⟩ <;>
    simp [Vec32.set, Vec32.get]

theorem seg1_copy_r2b [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl20 b) (_hbase : blkPl20.base = b)
    (s : State) (esA sp : BitVec 64) (r2 e2 t2m e2t : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + 0x0210#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_al : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = esA)
    (hq0 : s.readVReg128 0#5 = r2.v16)
    (hq1 : s.readVReg128 1#5 = r2.v20)
    (ht2m :
      t2m.v0 = r2.v0 ∧ t2m.v1 = r2.v1 ∧ t2m.v2 = r2.v2 ∧ t2m.v3 = r2.v3 ∧
      t2m.v4 = r2.v4 ∧ t2m.v5 = r2.v5 ∧ t2m.v6 = r2.v6 ∧ t2m.v7 = r2.v7 ∧
      t2m.v8 = r2.v8 ∧ t2m.v9 = r2.v9 ∧ t2m.v10 = r2.v10 ∧ t2m.v11 = r2.v11 ∧
      t2m.v12 = r2.v12 ∧ t2m.v13 = r2.v13 ∧ t2m.v14 = r2.v14 ∧ t2m.v15 = r2.v15 ∧
      t2m.v17 = r2.v17) :
    SepWP (blkPC20.rebase b (fun _ => none)) (b + 0x0290#64) s
      (Poly32Mem (esA + 1024#64) r2 ∗ Poly32Mem (esA + 1536#64) e2 ∗
        Poly32Mem (sp + 1232#64) t2m ∗ Poly32Mem (sp + 1744#64) e2t ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧
        s'.spAligned = true ∧
        s'.readReg64 .x0 = esA ∧
        s'.readReg64 .x1 = s.readReg64 .x1 ∧
        s'.readReg64 .x8 = s.readReg64 .x8 ∧
        s'.readReg64 .x9 = s.readReg64 .x9 ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x20 = s.readReg64 .x20 ∧
        s'.readReg64 .x21 = s.readReg64 .x21 ∧
        s'.readReg64 .x22 = s.readReg64 .x22 ∧
        s'.readVReg128 1#5 = e2.v3 ∧
        s'.readVReg128 2#5 = e2.v1 ∧
        s'.readVReg128 3#5 = s.readVReg128 3#5 ∧
        UnspilledSaved20 s s' ∧
        (P' ⊢ Poly32Mem (esA + 1024#64) r2 ∗ Poly32Mem (esA + 1536#64) e2 ∗
          Poly32Mem (sp + 1232#64) r2 ∗ Poly32Mem (sp + 1744#64) (e2t.set 0 e2.v0) ∗ Rest)) := by
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hsp_al
  step_ldrQ 0 18; step_strQ 2 16; step_ldrQ 0 19; step_strQ 2 20
  step_ldrQ 0 23; step_strQ 2 18; step_ldrQ 0 21; step_strQ 2 19
  step_ldrQ 0 22; step_strQ 2 23; step_ldrQ 0 26; step_strQ 2 21
  step_ldrQ 0 24; step_strQ 2 22; step_ldrQ 0 25; step_strQ 2 26
  step_ldrQ 0 29; step_strQ 2 24; step_ldrQ 0 27; step_strQ 2 25
  step_ldrQ 0 28; step_strQ 2 29; step_ldrQ 1 0; step_strQ 2 27
  step_ldrQ 0 30; step_strQ 2 28; step_ldrQ 0 31; step_strQ 3 0
  step_ldrQ 1 3; step_strQ 2 30; step_ldrQ 1 1; step_strQ 2 31
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simp [State.spAligned, hsp, hsp_chk],
      by simp [hx0], by simp, by simp, by simp, by simp, by simp, by simp, by simp,
      by simp [Vec32.get], by simp [Vec32.get], by simp,
      ⟨by simp, by simp, by simp, by simp⟩,
      ?_⟩
  rcases ht2m with ⟨e0, e1, e2', e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e17⟩
  simp only [Vec32.set, Vec32.get,
    e0, e1, e2', e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e17]
  exact Entails.refl _

theorem seg1_copy_e2a [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl20 b) (_hbase : blkPl20.base = b)
    (s : State) (esA sp : BitVec 64) (e2 e2t : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + 0x0290#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_al : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = esA)
    (hq1 : s.readVReg128 1#5 = e2.v3)
    (hq2 : s.readVReg128 2#5 = e2.v1)
    (he0 : e2t.v0 = e2.v0) :
    SepWP (blkPC20.rebase b (fun _ => none)) (b + 0x0318#64) s
      (Poly32Mem (esA + 1536#64) e2 ∗ Poly32Mem (sp + 1744#64) e2t ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧
        s'.spAligned = true ∧
        s'.readReg64 .x0 = esA ∧
        s'.readReg64 .x1 = s.readReg64 .x1 ∧
        s'.readReg64 .x8 = s.readReg64 .x8 ∧
        s'.readReg64 .x9 = s.readReg64 .x9 ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x20 = s.readReg64 .x20 ∧
        s'.readReg64 .x21 = s.readReg64 .x21 ∧
        s'.readReg64 .x22 = s.readReg64 .x22 ∧
        s'.readVReg128 0#5 = e2.v17 ∧
        s'.readVReg128 1#5 = e2.v21 ∧
        s'.readVReg128 3#5 = s.readVReg128 3#5 ∧
        UnspilledSaved20 s s' ∧
        (∃ e2m : Vec32,
          e2m.v0 = e2.v0 ∧ e2m.v1 = e2.v1 ∧ e2m.v2 = e2.v2 ∧ e2m.v3 = e2.v3 ∧
          e2m.v4 = e2.v4 ∧ e2m.v5 = e2.v5 ∧ e2m.v6 = e2.v6 ∧ e2m.v7 = e2.v7 ∧
          e2m.v8 = e2.v8 ∧ e2m.v9 = e2.v9 ∧ e2m.v10 = e2.v10 ∧ e2m.v11 = e2.v11 ∧
          e2m.v12 = e2.v12 ∧ e2m.v13 = e2.v13 ∧ e2m.v14 = e2.v14 ∧ e2m.v15 = e2.v15 ∧
          e2m.v16 = e2.v16 ∧ e2m.v18 = e2.v18 ∧
          (P' ⊢ Poly32Mem (esA + 1536#64) e2 ∗ Poly32Mem (sp + 1744#64) e2m ∗ Rest))) := by
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hsp_al
  step_ldrQ 0 2; step_strQ 1 3; step_ldrQ 0 6; step_strQ 1 1
  step_ldrQ 0 4; step_strQ 1 2; step_ldrQ 0 5; step_strQ 1 6
  step_ldrQ 0 9; step_strQ 1 4; step_ldrQ 0 7; step_strQ 1 5
  step_ldrQ 0 8; step_strQ 1 9; step_ldrQ 0 12; step_strQ 1 7
  step_ldrQ 0 10; step_strQ 1 8; step_ldrQ 0 11; step_strQ 1 12
  step_ldrQ 0 15; step_strQ 1 10; step_ldrQ 0 13; step_strQ 1 11
  step_ldrQ 0 14; step_strQ 1 15; step_ldrQ 0 18; step_strQ 1 13
  step_ldrQ 0 16; step_strQ 1 14; step_ldrQ 0 17; step_strQ 1 18
  step_ldrQ 0 21; step_strQ 1 16
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simp [State.spAligned, hsp, hsp_chk],
      by simp [hx0], by simp, by simp, by simp, by simp, by simp, by simp, by simp,
      by simp [Vec32.get], by simp [Vec32.get], by simp,
      ⟨by simp, by simp, by simp, by simp⟩,
      ⟨_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Entails.refl _⟩⟩ <;>
    simp [he0, Vec32.set, Vec32.get]

theorem seg1_copy_e2b [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl20 b) (_hbase : blkPl20.base = b)
    (s : State) (esA sp : BitVec 64) (e2 e2m s5488 : Vec32) (m0t m1t m0 m1 : BitVec 128)
    (Rest : SepProp)
    (hpc : s.pc = b + 0x0318#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_al : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = esA)
    (hq0 : s.readVReg128 0#5 = e2.v17)
    (hq1 : s.readVReg128 1#5 = e2.v21)
    (hm0 : s5488.v0 = m0)
    (hm1 : s5488.v1 = m1)
    (he2m :
      e2m.v0 = e2.v0 ∧ e2m.v1 = e2.v1 ∧ e2m.v2 = e2.v2 ∧ e2m.v3 = e2.v3 ∧
      e2m.v4 = e2.v4 ∧ e2m.v5 = e2.v5 ∧ e2m.v6 = e2.v6 ∧ e2m.v7 = e2.v7 ∧
      e2m.v8 = e2.v8 ∧ e2m.v9 = e2.v9 ∧ e2m.v10 = e2.v10 ∧ e2m.v11 = e2.v11 ∧
      e2m.v12 = e2.v12 ∧ e2m.v13 = e2.v13 ∧ e2m.v14 = e2.v14 ∧ e2m.v15 = e2.v15 ∧
      e2m.v16 = e2.v16 ∧ e2m.v18 = e2.v18) :
    SepWP (blkPC20.rebase b (fun _ => none)) (b + 0x0398#64) s
      (Poly32Mem (esA + 1536#64) e2 ∗ Poly32Mem (sp + 1744#64) e2m ∗
        Poly32Mem (sp + 5488#64) s5488 ∗
        Vec128At (sp + 2256#64) m0t ∗ Vec128At (sp + 2272#64) m1t ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧
        s'.spAligned = true ∧
        s'.readReg64 .x1 = s.readReg64 .x1 ∧
        s'.readReg64 .x8 = s.readReg64 .x8 ∧
        s'.readReg64 .x9 = s.readReg64 .x9 ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x20 = s.readReg64 .x20 ∧
        s'.readReg64 .x21 = s.readReg64 .x21 ∧
        s'.readReg64 .x22 = s.readReg64 .x22 ∧
        s'.readVReg128 0#5 = 0#128 ∧
        s'.readVReg128 1#5 = 0xfffc0000fffc0000fffc0000fffc0000#128 ∧
        s'.readVReg128 3#5 = s.readVReg128 3#5 ∧
        UnspilledSaved20 s s' ∧
        (P' ⊢ Poly32Mem (esA + 1536#64) e2 ∗ Poly32Mem (sp + 1744#64) e2 ∗
          Poly32Mem (sp + 5488#64) s5488 ∗
          Vec128At (sp + 2256#64) m0 ∗ Vec128At (sp + 2272#64) m1 ∗ Rest)) := by
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hsp_al
  step_ldrQ 0 19; step_strQ 1 17; step_ldrQ 0 20; step_strQ 1 21
  step_ldrQ 0 24; step_strQ 1 19; step_ldrQ 0 22; step_strQ 1 20
  step_ldrQ 0 23; step_strQ 1 24; step_ldrQ 0 27; step_strQ 1 22
  step_ldrQ 0 25; step_strQ 1 23; step_ldrQ 0 26; step_strQ 1 27
  step_ldrQ 0 30; step_strQ 1 25; step_ldrQ 0 28; step_strQ 1 26
  step_ldrQ 0 29; step_strQ 1 30; step_ldrQ 2 1; step_strQ 1 28
  step_ldrQ 0 31; step_strQ 1 29
  wp_step
  step_strQ 4 0
  wp_step
  step_strQ 1 31
  step_ldrQ 2 0
  step_strQ 3 0
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simp [State.spAligned, hsp, hsp_chk],
      by simp, by simp, by simp, by simp, by simp, by simp, by simp,
      by simp, by simp, by simp,
      ⟨by simp, by simp, by simp, by simp⟩,
      ?_⟩
  rcases he2m with
    ⟨e0, e1, e2', e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e18⟩
  simp only [hm0, hm1, Vec32.set, Vec32.get,
    e0, e1, e2', e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e18]
  exact Entails.refl _

theorem seg1_zero1 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl20 b) (_hbase : blkPl20.base = b)
    (s : State) (sp : BitVec 64) (z8 : Oct8) (z4976 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + 0x0398#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_al : s.spAligned = true)
    (hq0 : s.readVReg128 0#5 = 0#128) :
    SepWP (blkPC20.rebase b (fun _ => none)) (b + 0x0438#64) s
      (Oct8Mem (sp + 2288#64) z8 ∗ Poly32Mem (sp + 4976#64) z4976 ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧
        s'.spAligned = true ∧
        s'.readReg64 .x1 = s.readReg64 .x1 ∧
        s'.readReg64 .x8 = s.readReg64 .x8 ∧
        s'.readReg64 .x9 = s.readReg64 .x9 ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x20 = s.readReg64 .x20 ∧
        s'.readReg64 .x21 = s.readReg64 .x21 ∧
        s'.readReg64 .x22 = s.readReg64 .x22 ∧
        s'.readVReg128 0#5 = 0#128 ∧
        s'.readVReg128 1#5 = s.readVReg128 1#5 ∧
        s'.readVReg128 3#5 = s.readVReg128 3#5 ∧
        UnspilledSaved20 s s' ∧
        (P' ⊢ Oct8Mem (sp + 2288#64) Oct8.zero ∗ Poly32Mem (sp + 4976#64) Vec32.zero ∗ Rest)) := by
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hsp_al
  step_strQ 0 7; step_strQ 0 6; step_strQ 0 5; step_strQ 0 4
  step_strQ 0 3; step_strQ 0 2; step_strQ 0 1; step_strQ 0 0
  step_strQ 1 31; step_strQ 1 30; step_strQ 1 29; step_strQ 1 28
  step_strQ 1 27; step_strQ 1 26; step_strQ 1 25; step_strQ 1 24
  step_strQ 1 23; step_strQ 1 22; step_strQ 1 21; step_strQ 1 20
  step_strQ 1 19; step_strQ 1 18; step_strQ 1 17; step_strQ 1 16
  step_strQ 1 15; step_strQ 1 14; step_strQ 1 13; step_strQ 1 12
  step_strQ 1 11; step_strQ 1 10; step_strQ 1 9; step_strQ 1 8
  step_strQ 1 7; step_strQ 1 6; step_strQ 1 5; step_strQ 1 4
  step_strQ 1 3; step_strQ 1 2; step_strQ 1 1; step_strQ 1 0
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simp [State.spAligned, hsp, hsp_chk],
      by simp, by simp, by simp, by simp, by simp, by simp, by simp,
      by simp [hq0], by simp, by simp,
      ⟨by simp, by simp, by simp, by simp⟩,
      ?_⟩
  simp only [Oct8.set, Oct8.zero, Oct8.ofFn, Vec32.set, Vec32.zero, Vec32.ofFn]
  exact Entails.refl _

theorem seg1_zero2 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl20 b) (_hbase : blkPl20.base = b)
    (s : State) (sp : BitVec 64) (s5488 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + 0x0438#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_al : s.spAligned = true)
    (hq0 : s.readVReg128 0#5 = 0#128) :
    SepWP (blkPC20.rebase b (fun _ => none)) (b + 0x04b8#64) s
      (Poly32Mem (sp + 5488#64) s5488 ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧
        s'.spAligned = true ∧
        s'.readReg64 .x1 = s.readReg64 .x1 ∧
        s'.readReg64 .x8 = s.readReg64 .x8 ∧
        s'.readReg64 .x9 = s.readReg64 .x9 ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x20 = s.readReg64 .x20 ∧
        s'.readReg64 .x21 = s.readReg64 .x21 ∧
        s'.readReg64 .x22 = s.readReg64 .x22 ∧
        s'.readVReg128 0#5 = 0#128 ∧
        s'.readVReg128 1#5 = s.readVReg128 1#5 ∧
        s'.readVReg128 3#5 = s.readVReg128 3#5 ∧
        UnspilledSaved20 s s' ∧
        (P' ⊢ Poly32Mem (sp + 5488#64) Vec32.zero ∗ Rest)) := by
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hsp_al
  step_strQ 0 31; step_strQ 0 30; step_strQ 0 29; step_strQ 0 28
  step_strQ 0 27; step_strQ 0 26; step_strQ 0 25; step_strQ 0 24
  step_strQ 0 23; step_strQ 0 22; step_strQ 0 21; step_strQ 0 20
  step_strQ 0 19; step_strQ 0 18; step_strQ 0 17; step_strQ 0 16
  step_strQ 0 15; step_strQ 0 14; step_strQ 0 13; step_strQ 0 12
  step_strQ 0 11; step_strQ 0 10; step_strQ 0 9; step_strQ 0 8
  step_strQ 0 7; step_strQ 0 6; step_strQ 0 5; step_strQ 0 4
  step_strQ 0 3; step_strQ 0 2; step_strQ 0 1; step_strQ 0 0
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simp [State.spAligned, hsp, hsp_chk],
      by simp, by simp, by simp, by simp, by simp, by simp, by simp,
      by simp [hq0], by simp, by simp,
      ⟨by simp, by simp, by simp, by simp⟩,
      ?_⟩
  simp only [Vec32.set, Vec32.zero, Vec32.ofFn]
  exact Entails.refl _

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1b
