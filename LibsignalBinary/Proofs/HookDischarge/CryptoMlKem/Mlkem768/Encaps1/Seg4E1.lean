/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.GenPlacedFetches
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base
public meta import ProofLib.GenPlacedFetches
meta import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3Pure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd

/-!
# `encapsulate1_serialized` (`B03`) — Segment 4b `e1[0..2]` `cbd2` Loop (`+0x4938 .. +0x4b38`)

Proves the 3-iteration outer loop at `+0x4938..+0x4b38`: zeroes `[sp + 4272, sp + 4784)`, runs the
32-iteration SWAR `cbd2` loop reading `prf_{3 + idx}` at `sp + 2192 + 128 * idx`, and copies the
resulting 512-byte polynomial via 16 `stp q, q` pairs into `e1[idx]` at `sp + 13984 + 512 * idx`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg4E1

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement add_off_reloc_cancel mbase)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (shake256List)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd (
  cbd2CoeffFromWord neonCbd2Poly16 readU32LE)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (lane16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2 (
  setPC_setMem_collapse)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Poly32Mem PolyMem SepLoad128 SepStore128 SepWP.of_memRegion_vecRangeMem
  Vec128At Vec32 VecRangeMem poly32Mem_entails_memRegion poly32Mem_ofFn polyVecNat
  step_ldrQ128 step_stpQ128 step_strQ128 vecRangeMem_congr vecRangeMem_entails_memRegion)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  entails_sub spAligned_of_sp_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3Pure (
  HalfRangeMem SepStore16.halfRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure (
  SepLoad32.wordRange WordRangeMem)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base (
  blk03_code_eq blk03_tree_size blkLib03 blkPC03 blkPl03 blkPlaceable03 blkTree03)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a (blkPl03_ρ)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd (
  cbd2_j3_eq cbd2_j7_eq cbd2_swar_eq halfRangeMem8_cbd2_eq setMem_setMem setPC_setMem_setPC
  setWidth32_shr_zext64 shake256List_length step_bCond_not_taken step_bCond_taken
  truncate32_zext64 ubfx2_w32_norm vec128At_eq_halfRangeMem8 vecRangeMem_focus
  wordRangeMem32_eq_pointsToBytes)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC03 blkLib03 blkTree03 blk03_code_eq blk03_tree_size
  via_placement blkPl03 blkPlaceable03 [0x4938 → 0x4b34]
end

attribute [local irreducible] blkPC03 shake256List neonCbd2Poly16 polyVecNat

@[simp, arm64_norm, wp_norm] abbrev offSeg4E1     : BitVec 64 := BitVec.ofNat 64 18744
@[simp, arm64_norm, wp_norm] abbrev offSeg4E1Body : BitVec 64 := BitVec.ofNat 64 18884
@[simp, arm64_norm, wp_norm] abbrev offSeg4E1Br   : BitVec 64 := BitVec.ofNat 64 19040
@[simp, arm64_norm, wp_norm] abbrev offSeg4E1Copy : BitVec 64 := BitVec.ofNat 64 19044
@[simp, arm64_norm, wp_norm] abbrev offSeg4E1Out  : BitVec 64 := BitVec.ofNat 64 19252
@[simp, arm64_norm, wp_norm] abbrev offSeg4E2     : BitVec 64 := BitVec.ofNat 64 19256

local macro "step_strQ4272 " k:num : tactic => `(tactic| (
  apply step_strQ128 (wb := none)
  · wp_norm_lhs
  · first | wp_norm_lhs | simp [*]
  · wp_norm_lhs
  · first | rfl | wp_norm_lhs | wp_norm_goal | simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, *]
  · wp_norm_lhs
  · wp_norm_lhs
  · apply SepStore128.left; apply SepStore128.vec32 (k := $k)
    · decide
    · bv_omega
    · rfl
  · wp_norm_lhs
  intro _
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))

private theorem seg4_e1_zero [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = b + offSeg4E1) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + offSeg4E1Body) s
      (memRegion (sp + 4272#64) 512 ∗ Rest)
      (fun s1 P1 =>
        s1.sp = sp ∧ s1.spAligned = true ∧
        s1.readReg64 .x8 = s.readReg64 .x8 ∧
        s1.readReg64 .x9 = s.readReg64 .x9 ∧
        s1.readReg64 .x10 = s.readReg64 .x8 + 1#64 ∧
        s1.readReg64 .x11 = 0#64 ∧
        s1.readReg64 .x12 = s.readReg64 .x9 ∧
        s1.readReg64 .x19 = s.readReg64 .x19 ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x21 = s.readReg64 .x21 ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readVReg128 3#5 = s.readVReg128 3#5 ∧
        (P1 ⊢ memRegion (sp + 4272#64) 512 ∗ Rest)) := by
  subst hbase
  have hal_sp : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  wp_steps 3
  apply SepWP.of_memRegion_vecRangeMem 32 (sp + 4272#64) (by decide) rfl
  intro f
  rw [show VecRangeMem 32 (sp + 4272#64) f = PolyMem (sp + 4272#64) f from rfl, ← poly32Mem_ofFn]
  step_strQ4272 31; step_strQ4272 30; step_strQ4272 29; step_strQ4272 28
  step_strQ4272 27; step_strQ4272 26; step_strQ4272 25; step_strQ4272 24
  step_strQ4272 23; step_strQ4272 22; step_strQ4272 21; step_strQ4272 20
  step_strQ4272 19; step_strQ4272 18; step_strQ4272 17; step_strQ4272 16
  step_strQ4272 15; step_strQ4272 14; step_strQ4272 13; step_strQ4272 12
  step_strQ4272 11; step_strQ4272 10; step_strQ4272 9;  step_strQ4272 8
  step_strQ4272 7;  step_strQ4272 6;  step_strQ4272 5;  step_strQ4272 4
  step_strQ4272 3;  step_strQ4272 2;  step_strQ4272 1;  step_strQ4272 0
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], spAligned_of_sp_eq hspA hsp (by simp [hsp]),
      by simp, by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp, by simp,
      sepConj_mono_left (poly32Mem_entails_memRegion _ _)⟩

local macro "step_e1_strh " cellPtr:ident c:num
    valTerm:term:arg valPrf:term:arg hrunId:term:arg : tactic => `(tactic| (
  refine SepWP.step_str16 (wb := none)
    (ea := $cellPtr + BitVec.ofNat 64 (2 * $c)) (val := $valTerm)
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]; first | rfl | (dsimp only [$cellPtr:ident]; clear * -; bv_omega))
    $valPrf
    (SepStore16.left (SepStore16.halfRange (n := 8) (c := $c) (by decide) rfl))
    (by wp_norm_lhs) ?_
  intro _
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))

private theorem seg4_e1_cbd2_iter [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp prfPtr dstPtr : BitVec 64) (prf : List (BitVec 8))
    {k : Nat} (hk : k < 32) (f : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + offSeg4E1Body) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx11 : s.readReg64 .x11 = BitVec.ofNat 64 (16 * k))
    (hx12 : s.readReg64 .x12 = prfPtr + 1#64 + BitVec.ofNat 64 (4 * k))
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx21 : s.readReg64 .x21 = dstPtr) :
    SepWP (blkPC03.rebase b (fun _ => none))
      (if k < 31 then b + offSeg4E1Body else b + offSeg4E1Copy) s
      (WordRangeMem 32 prfPtr (readU32LE prf) ∗ VecRangeMem 32 dstPtr f ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x8 = s.readReg64 .x8 ∧
        s'.readReg64 .x9 = s.readReg64 .x9 ∧
        s'.readReg64 .x10 = s.readReg64 .x10 ∧
        s'.readReg64 .x11 = BitVec.ofNat 64 (16 * (k + 1)) ∧
        s'.readReg64 .x12 = prfPtr + 1#64 + BitVec.ofNat 64 (4 * (k + 1)) ∧
        s'.readReg64 .x19 = 0x55555555#64 ∧
        s'.readReg64 .x20 = s.readReg64 .x20 ∧
        s'.readReg64 .x21 = dstPtr ∧
        s'.readReg64 .x22 = s.readReg64 .x22 ∧
        s'.readVReg128 3#5 = s.readVReg128 3#5 ∧
        P' = (WordRangeMem 32 prfPtr (readU32LE prf) ∗
          VecRangeMem 32 dstPtr (Function.update f k (polyVecNat (neonCbd2Poly16 prf) k)) ∗ Rest)) := by
  subst hbase
  obtain ⟨Fk, hsplit, hupd⟩ := vecRangeMem_focus hk dstPtr f
  let cellPtr := dstPtr + BitVec.ofNat 64 (16 * k)
  let w := readU32LE prf k
  rw [hsplit, vec128At_eq_halfRangeMem8 cellPtr (f k),
    show WordRangeMem 32 prfPtr (readU32LE prf) ∗
        (HalfRangeMem 8 cellPtr (fun j => lane16 (f k) ⟨j % 8, Nat.mod_lt _ (by decide)⟩) ∗ Fk) ∗ Rest =
      HalfRangeMem 8 cellPtr (fun j => lane16 (f k) ⟨j % 8, Nat.mod_lt _ (by decide)⟩) ∗
        WordRangeMem 32 prfPtr (readU32LE prf) ∗ Fk ∗ Rest by
      simp only [sepConj_assoc]; rw [sepConj_left_comm (WordRangeMem 32 prfPtr (readU32LE prf))]]
  refine SepWP.step_ldur32 (wb := none) (ea := prfPtr + BitVec.ofNat 64 (4 * k)) (v := w)
    hpc hrun (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx12]; clear * -; bv_omega)
    (SepLoad32.right (SepLoad32.left (SepLoad32.wordRange (n := 32) (k := k) hk rfl)))
    (by wp_norm_lhs) ?_
  wp_steps 20
  step_e1_strh cellPtr 0 (cbd2CoeffFromWord w 0)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  wp_step
  step_e1_strh cellPtr 1 (cbd2CoeffFromWord w 1)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  wp_steps 2
  step_e1_strh cellPtr 3 (cbd2CoeffFromWord w 3)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]; exact cbd2_j3_eq _) hrun
  wp_steps 2
  step_e1_strh cellPtr 4 (cbd2CoeffFromWord w 4)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  wp_steps 3
  step_e1_strh cellPtr 5 (cbd2CoeffFromWord w 5)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  wp_step
  step_e1_strh cellPtr 2 (cbd2CoeffFromWord w 2)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  wp_step
  step_e1_strh cellPtr 7 (cbd2CoeffFromWord w 7)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]; exact cbd2_j7_eq _) hrun
  step_e1_strh cellPtr 6 (cbd2CoeffFromWord w 6)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  have hmem_eq : ∀ hFin : Nat → BitVec 16,
      (∀ j (hj : j < 8), hFin j = cbd2CoeffFromWord w ⟨j, hj⟩) →
      HalfRangeMem 8 cellPtr hFin ∗ WordRangeMem 32 prfPtr (readU32LE prf) ∗ Fk ∗ Rest =
        WordRangeMem 32 prfPtr (readU32LE prf) ∗
          VecRangeMem 32 dstPtr (Function.update f k (polyVecNat (neonCbd2Poly16 prf) k)) ∗ Rest := by
    intro hFin hhFin
    rw [halfRangeMem8_cbd2_eq cellPtr prf k hk hFin hhFin,
      sepConj_left_comm (Vec128At cellPtr _), ← sepConj_assoc (Vec128At cellPtr _) Fk Rest,
      hupd]
  by_cases hk31 : k < 31
  · simp only [hk31, ↓reduceIte]
    refine step_bCond_taken (dst := blkPl03.base + offSeg4E1Body)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp; clear * - hk31
          rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
            _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;> first | decide | omega)
      (by clear * -; dsimp [offSeg4E1Br, offSeg4E1Body]; bv_omega) ?_
    refine SepWP.done (by simp [State.setPC]) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp, by simp, by simp,
        by simp; clear * -; bv_omega,
        by simp; clear * -; bv_omega,
        by simp [hx19], by simp, by simp [hx21], by simp, by simp,
        hmem_eq _ fun j hj => by rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;> first | rfl | omega⟩
  · have hk_eq : k = 31 := by omega
    subst hk_eq
    simp only [show ¬(31 < 31) by omega, ↓reduceIte]
    refine step_bCond_not_taken (dst := blkPl03.base + offSeg4E1Copy)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp)
      (by clear * -; dsimp [offSeg4E1Br, offSeg4E1Copy]; bv_omega) ?_
    refine SepWP.done (by simp [State.setPC]) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp, by simp, by simp,
        by simp, by simp,
        by simp [hx19], by simp, by simp [hx21], by simp, by simp,
        hmem_eq _ fun j hj => by rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;> first | rfl | omega⟩

private theorem seg4_e1_cbd2_steps [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (sp prfPtr dstPtr : BitVec 64) (prf : List (BitVec 8)) (Rest : SepProp) :
    ∀ (rem k : Nat), rem + k = 32 → ∀ (s : State) (f : Nat → BitVec 128),
      (∀ i, i < k → f i = polyVecNat (neonCbd2Poly16 prf) i) →
      s.pc = (if k < 32 then b + offSeg4E1Body else b + offSeg4E1Copy) →
      s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x11 = BitVec.ofNat 64 (16 * k) →
      s.readReg64 .x12 = prfPtr + 1#64 + BitVec.ofNat 64 (4 * k) →
      s.readReg64 .x19 = 0x55555555#64 → s.readReg64 .x21 = dstPtr →
      SepWP (blkPC03.rebase b (fun _ => none)) (b + offSeg4E1Copy) s
        (WordRangeMem 32 prfPtr (readU32LE prf) ∗ VecRangeMem 32 dstPtr f ∗ Rest)
        (fun s' P' =>
          s'.sp = sp ∧ s'.spAligned = true ∧
          s'.readReg64 .x8 = s.readReg64 .x8 ∧
          s'.readReg64 .x9 = s.readReg64 .x9 ∧
          s'.readReg64 .x10 = s.readReg64 .x10 ∧
          s'.readReg64 .x19 = 0x55555555#64 ∧
          s'.readReg64 .x20 = s.readReg64 .x20 ∧
          s'.readReg64 .x21 = dstPtr ∧
          s'.readReg64 .x22 = s.readReg64 .x22 ∧
          s'.readVReg128 3#5 = s.readVReg128 3#5 ∧
          P' = (WordRangeMem 32 prfPtr (readU32LE prf) ∗
            PolyMem dstPtr (polyVecNat (neonCbd2Poly16 prf)) ∗ Rest)) := by
  intro rem; induction rem with
  | zero =>
    intro k hsum s f hf hpc hrun hsp hspA _ _ hx19 hx21
    have hk : k = 32 := by omega
    subst hk
    simp only [show ¬(32 < 32) by omega, ↓reduceIte] at hpc
    exact SepWP.done hpc hrun
      ⟨hsp, hspA, rfl, rfl, rfl, hx19, rfl, hx21, rfl, rfl, by
        dsimp only [PolyMem]
        rw [vecRangeMem_congr hf]⟩
  | succ rem ih =>
    intro k hsum s f hf hpc hrun hsp hspA hx11 hx12 hx19 hx21
    have hk : k < 32 := by omega
    simp only [hk, ↓reduceIte] at hpc
    refine SepWP.seq
      (seg4_e1_cbd2_iter hb hbase s sp prfPtr dstPtr prf hk f Rest
        hpc hrun hsp hspA hx11 hx12 hx19 hx21) ?_
    rintro s1 P1 hpc1 hrun1 ⟨hsp1, hspA1, r8, r9, r10, hx11_1, hx12_1, hx19_1, r20, hx21_1, r22, rv3, hP1⟩
    subst hP1
    refine SepWP.seq
      (ih (k + 1) (by omega) s1 _
        (fun i hi => by
          by_cases hik : i = k
          · subst hik; exact Function.update_self i _ f
          · rw [Function.update_of_ne hik]; exact hf i (by omega))
        (by by_cases hk31 : k < 31 <;> simp [hk31, show (k + 1 < 32) ↔ k < 31 by omega] at hpc1 ⊢ <;> exact hpc1)
        hrun1 hsp1 hspA1 hx11_1 hx12_1 hx19_1 hx21_1) ?_
    rintro s2 P2 hpc2 hrun2 ⟨hsp2, hspA2, g8, g9, g10, gx19, g20, gx21, g22, gv3, hP2⟩
    exact SepWP.done hpc2 hrun2 ⟨hsp2, hspA2, g8.trans r8, g9.trans r9, g10.trans r10,
      gx19, g20.trans r20, gx21, g22.trans r22, gv3.trans rv3, hP2⟩

local macro "ldr_src4272 " k:num : tactic => `(tactic| (
  apply step_ldrQ128 (wb := none)
  · wp_norm_lhs
  · first | wp_norm_lhs | simp [*]
  · wp_norm_lhs
  · first | rfl | wp_norm_lhs | wp_norm_goal | simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, *]
  · wp_norm_lhs
  · apply SepLoad128.left; exact SepLoad128.vec32 (by decide : $k < 32) (by bv_omega) rfl
  · wp_norm_lhs))

local macro "stp_dst_e1 " m:num : tactic => `(tactic| (
  apply step_stpQ128 (wb := none)
  · wp_norm_lhs
  · first | wp_norm_lhs | simp [*]
  · wp_norm_lhs
  · rfl
  · wp_norm_lhs
  · rfl
  · wp_norm_lhs
  · wp_norm_lhs
  · apply SepStore128.right; apply SepStore128.left
    exact SepStore128.vec32 (by decide : 2 * $m < 32) (by bv_omega) (by dsimp only [Vec32.set])
  · apply SepStore128.right; apply SepStore128.left
    exact SepStore128.vec32 (by decide : 2 * $m + 1 < 32) (by bv_omega) (by dsimp only [Vec32.set])
  · wp_norm_lhs
  intro _
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))

private theorem seg4_e1_copy [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp : BitVec 64) {idx : Nat} (hidx : idx < 3)
    (src dst : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + offSeg4E1Copy) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 idx)
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 (idx + 1))
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 13984#64)
    (hx21 : s.readReg64 .x21 = sp + 4272#64) :
    let dstPtr := sp + 13984#64 + BitVec.ofNat 64 (512 * idx)
    SepWP (blkPC03.rebase b (fun _ => none))
      (if idx < 2 then b + offSeg4E1 else b + offSeg4E2) s
      (Poly32Mem (sp + 4272#64) src ∗ Poly32Mem dstPtr dst ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x8 = BitVec.ofNat 64 (idx + 1) ∧
        s'.readReg64 .x9 = s.readReg64 .x9 + 128#64 ∧
        s'.readReg64 .x19 = 0x55555555#64 ∧
        s'.readReg64 .x20 = sp + 13984#64 ∧
        s'.readReg64 .x21 = sp + 4272#64 ∧
        s'.readReg64 .x22 = s.readReg64 .x22 ∧
        s'.readVReg128 3#5 = s.readVReg128 3#5 ∧
        P' = (Poly32Mem (sp + 4272#64) src ∗ Poly32Mem dstPtr src ∗ Rest)) := by
  intro dstPtr
  subst hbase
  have hal_sp : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  have hx11_eq : (sp + 13984#64) + (BitVec.ofNat 64 idx <<< 9) = dstPtr := by
    dsimp only [dstPtr]; clear * - hidx
    rcases (show idx = 0 ∨ idx = 1 ∨ idx = 2 by omega) with rfl | rfl | rfl <;> bv_omega
  wp_step
  ldr_src4272 0; ldr_src4272 1; ldr_src4272 3
  wp_steps 2
  stp_dst_e1 0
  ldr_src4272 2; ldr_src4272 5
  wp_step
  stp_dst_e1 1
  ldr_src4272 4;  ldr_src4272 7;  stp_dst_e1 2
  ldr_src4272 6;  ldr_src4272 9;  stp_dst_e1 3
  ldr_src4272 8;  ldr_src4272 11; stp_dst_e1 4
  ldr_src4272 10; ldr_src4272 13; stp_dst_e1 5
  ldr_src4272 12; ldr_src4272 15; stp_dst_e1 6
  ldr_src4272 14; ldr_src4272 17; stp_dst_e1 7
  ldr_src4272 16; ldr_src4272 19; stp_dst_e1 8
  ldr_src4272 18; ldr_src4272 21; stp_dst_e1 9
  ldr_src4272 20; ldr_src4272 23; stp_dst_e1 10
  ldr_src4272 22; ldr_src4272 25; stp_dst_e1 11
  ldr_src4272 24; ldr_src4272 27; stp_dst_e1 12
  ldr_src4272 26; ldr_src4272 29; stp_dst_e1 13
  ldr_src4272 28; ldr_src4272 31; stp_dst_e1 14
  ldr_src4272 30; stp_dst_e1 15
  by_cases hidx2 : idx < 2
  · simp only [hidx2, ↓reduceIte]
    refine step_bCond_taken (dst := blkPl03.base + offSeg4E1)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp; clear * - hidx2; rcases idx with _ | _ | idx <;> first | decide | omega)
      (by clear * -; dsimp [offSeg4E1Out, offSeg4E1]; bv_omega) ?_
    refine SepWP.done (by simp [State.setPC]) (by simp [hrun])
      ⟨by simp [hsp], spAligned_of_sp_eq hspA hsp (by simp [hsp]),
        by simp, by simp, by simp [hx19], by simp [hx20], by simp [hx21], by simp, by simp,
        by clear * -; cases src; rfl⟩
  · have hidx_eq : idx = 2 := by omega
    subst hidx_eq
    simp only [show ¬(2 < 2) by omega, ↓reduceIte]
    refine step_bCond_not_taken (dst := blkPl03.base + offSeg4E2)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp)
      (by clear * -; dsimp [offSeg4E1Out, offSeg4E2]; bv_omega) ?_
    refine SepWP.done (by simp [State.setPC]) (by simp [hrun])
      ⟨by simp [hsp], spAligned_of_sp_eq hspA hsp (by simp [hsp]),
        by simp, by simp, by simp [hx19], by simp [hx20], by simp [hx21], by simp, by simp,
        by clear * -; cases src; rfl⟩


private theorem seg4_e1_iter [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp : BitVec 64) {idx : Nat} (hidx : idx < 3)
    (prf : List (BitVec 8)) (hprf : prf.length = 128)
    (prev : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + offSeg4E1) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 idx)
    (hx9 : s.readReg64 .x9 = sp + 2193#64 + BitVec.ofNat 64 (128 * idx))
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 13984#64)
    (hx21 : s.readReg64 .x21 = sp + 4272#64) :
    let prfPtr := sp + 2192#64 + BitVec.ofNat 64 (128 * idx)
    let dstPtr := sp + 13984#64 + BitVec.ofNat 64 (512 * idx)
    SepWP (blkPC03.rebase b (fun _ => none))
      (if idx < 2 then b + offSeg4E1 else b + offSeg4E2) s
      ((prfPtr ↦ₛ prf) ∗ memRegion (sp + 4272#64) 512 ∗ PolyMem dstPtr prev ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x8 = BitVec.ofNat 64 (idx + 1) ∧
        sf.readReg64 .x9 = sp + 2193#64 + BitVec.ofNat 64 (128 * (idx + 1)) ∧
        sf.readReg64 .x19 = 0x55555555#64 ∧
        sf.readReg64 .x20 = sp + 13984#64 ∧
        sf.readReg64 .x21 = sp + 4272#64 ∧
        sf.readVReg128 3#5 = s.readVReg128 3#5 ∧
        (Pf ⊢ (prfPtr ↦ₛ prf) ∗ memRegion (sp + 4272#64) 512 ∗
          PolyMem dstPtr (polyVecNat (neonCbd2Poly16 prf)) ∗ Rest)) := by
  intro prfPtr dstPtr
  rw [← wordRangeMem32_eq_pointsToBytes prfPtr hprf]
  refine SepWP.weaken_pre
    (P' := memRegion (sp + 4272#64) 512 ∗
      (WordRangeMem 32 prfPtr (readU32LE prf) ∗ PolyMem dstPtr prev ∗ Rest)) (by sep_frame) ?_
  refine SepWP.seq (seg4_e1_zero hb hbase s sp _ hpc hrun hsp hspA) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hsp1, hspA1, hx8_1, hx9_1, hx10_1, hx11_1, hx12_1,
    hx19_1, hx20_1, hx21_1, _, hv3_1, hP1⟩
  refine SepWP.weaken_pre hP1 ?_
  apply SepWP.of_memRegion_vecRangeMem 32 (sp + 4272#64) (hf := by sep_focus); intro f4272
  refine SepWP.weaken_pre
    (P' := WordRangeMem 32 prfPtr (readU32LE prf) ∗ VecRangeMem 32 (sp + 4272#64) f4272 ∗
      (PolyMem dstPtr prev ∗ Rest)) (by sep_frame) ?_
  refine SepWP.seq
    (seg4_e1_cbd2_steps hb hbase sp prfPtr (sp + 4272#64) prf _ 32 0 rfl s1 f4272
      (fun _ h => by omega) (by simpa using hpc1) hrun1 hsp1 hspA1 hx11_1
      (by rw [hx12_1, hx9]; dsimp only [prfPtr]; clear * -; bv_omega)
      (hx19_1.trans hx19) (hx21_1.trans hx21)) ?_
  rintro s2 P2 hpc2 hrun2 ⟨hsp2, hspA2, hx8_2, hx9_2, hx10_2, hx19_2, hx20_2, hx21_2, _, hv3_2, hP2⟩
  subst hP2
  rw [← poly32Mem_ofFn (sp + 4272#64), ← poly32Mem_ofFn dstPtr prev]
  refine SepWP.weaken_pre
    (P' := Poly32Mem (sp + 4272#64) (Vec32.ofFn (polyVecNat (neonCbd2Poly16 prf))) ∗
      Poly32Mem dstPtr (Vec32.ofFn prev) ∗ (WordRangeMem 32 prfPtr (readU32LE prf) ∗ Rest))
    (by sep_frame) ?_
  have hx10_eq : s2.readReg64 .x10 = BitVec.ofNat 64 (idx + 1) := by
    rw [hx10_2, hx10_1, hx8]; clear * - hidx; rcases idx with _ | _ | _ | idx <;> first | decide | omega
  refine SepWP.seq
    (seg4_e1_copy hb hbase s2 sp hidx _ _ _ hpc2 hrun2 hsp2 hspA2
      (hx8_2.trans (hx8_1.trans hx8)) hx10_eq hx19_2
      (hx20_2.trans (hx20_1.trans hx20)) hx21_2) ?_
  rintro sf Pf hpcf hrunf ⟨hspf, hspAf, r8, r9, r19, r20, r21, _, rv3, hPf⟩
  refine SepWP.done hpcf hrunf
    ⟨hspf, hspAf, r8, by rw [r9, hx9_2, hx9_1, hx9]; clear * -; bv_omega,
      r19, r20, r21, rv3.trans (hv3_2.trans hv3_1), ?_⟩
  rw [hPf, poly32Mem_ofFn dstPtr, wordRangeMem32_eq_pointsToBytes prfPtr hprf]
  exact entails_sub (poly32Mem_entails_memRegion (sp + 4272#64) _) (by sep_frame) (by sep_frame)

theorem seg4_e1_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp : BitVec 64) (coins : List (BitVec 8))
    (z0 z1 z2 : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + offSeg4E1) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = 0#64)
    (hx9 : s.readReg64 .x9 = sp + 2193#64)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 13984#64)
    (hx21 : s.readReg64 .x21 = sp + 4272#64)
    (hv3 : s.readVReg128 3#5 = 0#128) :
    let prf3 := shake256List 128 (coins ++ [3#8])
    let prf4 := shake256List 128 (coins ++ [4#8])
    let prf5 := shake256List 128 (coins ++ [5#8])
    SepWP (blkPC03.rebase b (fun _ => none)) (b + offSeg4E2) s
      (((sp + 2192#64) ↦ₛ prf3) ∗ ((sp + 2320#64) ↦ₛ prf4) ∗ ((sp + 2448#64) ↦ₛ prf5) ∗
       memRegion (sp + 4272#64) 512 ∗
       PolyMem (sp + 13984#64) z0 ∗ PolyMem (sp + 14496#64) z1 ∗ PolyMem (sp + 15008#64) z2 ∗
       Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x19 = 0x55555555#64 ∧
        sf.readVReg128 3#5 = 0#128 ∧
        (Pf ⊢ memRegion (sp + 2192#64) 384 ∗ memRegion (sp + 4272#64) 512 ∗
          PolyMem (sp + 13984#64) (polyVecNat (neonCbd2Poly16 prf3)) ∗
          PolyMem (sp + 14496#64) (polyVecNat (neonCbd2Poly16 prf4)) ∗
          PolyMem (sp + 15008#64) (polyVecNat (neonCbd2Poly16 prf5)) ∗ Rest)) := by
  intro prf3 prf4 prf5
  have h3 : prf3.length = 128 := shake256List_length 128 _
  have h4 : prf4.length = 128 := shake256List_length 128 _
  have h5 : prf5.length = 128 := shake256List_length 128 _
  have ha_2320  : sp + 2192#64 + 128#64 = sp + 2320#64 := by clear * -; bv_omega
  have ha_2448  : sp + 2192#64 + 256#64 = sp + 2448#64 := by clear * -; bv_omega
  have ha_14496 : sp + 13984#64 + 512#64 = sp + 14496#64 := by clear * -; bv_omega
  have ha_15008 : sp + 13984#64 + 1024#64 = sp + 15008#64 := by clear * -; bv_omega
  refine SepWP.weaken_pre
    (P' := ((sp + 2192#64 + 0#64) ↦ₛ prf3) ∗ memRegion (sp + 4272#64) 512 ∗
      PolyMem (sp + 13984#64 + 0#64) z0 ∗
      (((sp + 2320#64) ↦ₛ prf4) ∗ ((sp + 2448#64) ↦ₛ prf5) ∗
        PolyMem (sp + 14496#64) z1 ∗ PolyMem (sp + 15008#64) z2 ∗ Rest))
    (by simp only [BitVec.add_zero]; sep_frame) ?_
  refine SepWP.seq
    (seg4_e1_iter hb hbase s sp (idx := 0) (by decide) prf3 h3 z0 _
      hpc hrun hsp hspA hx8 (by simpa using hx9) hx19 hx20 hx21) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hsp1, hspA1, hx8_1, hx9_1, hx19_1, hx20_1, hx21_1, hv3_1, hP1⟩
  refine SepWP.weaken_pre (Entails.trans hP1
    (show (((sp + 2192#64 + 0#64) ↦ₛ prf3) ∗ memRegion (sp + 4272#64) 512 ∗
        PolyMem (sp + 13984#64 + 0#64) (polyVecNat (neonCbd2Poly16 prf3)) ∗
        (((sp + 2320#64) ↦ₛ prf4) ∗ ((sp + 2448#64) ↦ₛ prf5) ∗
          PolyMem (sp + 14496#64) z1 ∗ PolyMem (sp + 15008#64) z2 ∗ Rest)) ⊢
      ((sp + 2192#64 + 128#64) ↦ₛ prf4) ∗ memRegion (sp + 4272#64) 512 ∗
        PolyMem (sp + 13984#64 + 512#64) z1 ∗
        (((sp + 2192#64) ↦ₛ prf3) ∗ ((sp + 2448#64) ↦ₛ prf5) ∗
          PolyMem (sp + 13984#64) (polyVecNat (neonCbd2Poly16 prf3)) ∗
          PolyMem (sp + 15008#64) z2 ∗ Rest) by
      simp only [BitVec.add_zero, ha_2320, ha_14496]; sep_frame)) ?_
  refine SepWP.seq
    (seg4_e1_iter hb hbase s1 sp (idx := 1) (by decide) prf4 h4 z1 _
      (by simpa using hpc1) hrun1 hsp1 hspA1 hx8_1 hx9_1 hx19_1 hx20_1 hx21_1) ?_
  rintro s2 P2 hpc2 hrun2 ⟨hsp2, hspA2, hx8_2, hx9_2, hx19_2, hx20_2, hx21_2, hv3_2, hP2⟩
  refine SepWP.weaken_pre (Entails.trans hP2
    (show (((sp + 2192#64 + 128#64) ↦ₛ prf4) ∗ memRegion (sp + 4272#64) 512 ∗
        PolyMem (sp + 13984#64 + 512#64) (polyVecNat (neonCbd2Poly16 prf4)) ∗
        (((sp + 2192#64) ↦ₛ prf3) ∗ ((sp + 2448#64) ↦ₛ prf5) ∗
          PolyMem (sp + 13984#64) (polyVecNat (neonCbd2Poly16 prf3)) ∗
          PolyMem (sp + 15008#64) z2 ∗ Rest)) ⊢
      ((sp + 2192#64 + 256#64) ↦ₛ prf5) ∗ memRegion (sp + 4272#64) 512 ∗
        PolyMem (sp + 13984#64 + 1024#64) z2 ∗
        (((sp + 2192#64) ↦ₛ prf3) ∗ ((sp + 2320#64) ↦ₛ prf4) ∗
          PolyMem (sp + 13984#64) (polyVecNat (neonCbd2Poly16 prf3)) ∗
          PolyMem (sp + 14496#64) (polyVecNat (neonCbd2Poly16 prf4)) ∗ Rest) by
      simp only [ha_2320, ha_2448, ha_14496, ha_15008]; sep_frame)) ?_
  refine SepWP.seq
    (seg4_e1_iter hb hbase s2 sp (idx := 2) (by decide) prf5 h5 z2 _
      (by simpa using hpc2) hrun2 hsp2 hspA2 hx8_2 hx9_2 hx19_2 hx20_2 hx21_2) ?_
  rintro sf Pf hpcf hrunf ⟨hspf, hspAf, _, _, hx19f, _, _, hv3f, hPf⟩
  refine SepWP.done (by simpa using hpcf) hrunf
    ⟨hspf, hspAf, hx19f, hv3f.trans (hv3_2.trans (hv3_1.trans hv3)), Entails.trans hPf ?_⟩
  simp only [ha_2448, ha_15008]
  have hm384 : ((sp + 2192#64) ↦ₛ prf3) ∗ ((sp + 2320#64) ↦ₛ prf4) ∗ ((sp + 2448#64) ↦ₛ prf5) ⊢
      memRegion (sp + 2192#64) 384 := by
    rw [memRegion_split' (b' := sp + 2320#64) (n := 128) (k := (256 : Nat)) rfl (by clear * -; bv_omega) (by decide),
        memRegion_split' (b' := sp + 2448#64) (n := 128) (k := (128 : Nat)) rfl (by clear * -; bv_omega) (by decide)]
    exact sepConj_mono (by simpa [h3] using pointsToBytes_entails_memRegion (sp + 2192#64) prf3)
      (sepConj_mono (by simpa [h4] using pointsToBytes_entails_memRegion (sp + 2320#64) prf4)
        (by simpa [h5] using pointsToBytes_entails_memRegion (sp + 2448#64) prf5))
  exact entails_sub hm384 (by sep_frame) (by sep_frame)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg4E1
