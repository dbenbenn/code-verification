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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base
public meta import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3Pure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6CbdPure

/-!
# `kyber_decapsulate` (`B06`) — Segment 6 `e1[0..3]` `cbd2` Loop (`+0x8e64 .. +0x9064`)

Proves the 4-iteration outer loop at `+0x8e64..+0x9064`: zeroes `[sp + 14432, sp + 14944)`, runs the
32-iteration SWAR `cbd2` loop reading `prf_{4 + idx}` at `sp + 30448 + 128 * idx`, and copies the
resulting 512-byte polynomial via 16 `stp q, q` pairs into `e1[idx]` at `sp + 28368 + 512 * idx`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6E1Loop
open Arm64 Arm64.Obj ProofLib SepProp BitVec
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemBlockPlacement_ρ mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (shake256List)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd (
  cbd2CoeffFromWord neonCbd2Poly16 readU32LE)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (lane16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2 (
  setPC_setMem_collapse)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Poly32Mem PolyMem SepLoad128 SepStore128 SepWP.of_memRegion_vecRangeMem
  Vec128At Vec32 VecRangeMem poly32Mem_entails_memRegion poly32Mem_ofFn polyVecNat
  step_ldrQ128 step_stpQ128 step_strQ128 vecRangeMem_congr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  entails_sub spAligned_of_sp_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3Pure (
  HalfRangeMem SepStore16.halfRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure (
  SepLoad32.wordRange WordRangeMem)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base (
  blk06_code_eq blk06_tree_size blkLib06 blkPC06 blkPl06 blkPlaceable06 blkTree06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6CbdPure (
  cbd2_j3_eq cbd2_j7_eq cbd2_swar_eq halfRangeMem8_cbd2_eq setMem_setMem setPC_setMem_setPC
  setWidth32_shr_zext64 shake256List_length step_bCond_not_taken step_bCond_taken
  truncate32_zext64 ubfx2_w32_norm vec128At_eq_halfRangeMem8 vecRangeMem_focus
  wordRangeMem32_eq_pointsToBytes)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC06 blkLib06 blkTree06 blk06_code_eq blk06_tree_size
  via_placement blkPl06 blkPlaceable06 [0x8e64 → 0x9060]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl06_ρ [MlKemPlacement] (sym : String) :
    blkPl06.ρ sym = mlkemMultiLib.resolve mlkemMpl sym :=
  mlkemBlockPlacement_ρ 6 sym

attribute [local irreducible] blkPC06 shake256List neonCbd2Poly16 polyVecNat
attribute [local wp_norm ↓ high] ubfx2_w32_norm truncate32_zext64 setWidth32_shr_zext64

@[simp, arm64_norm, wp_norm] abbrev offSeg6E1Loop : BitVec 64 := BitVec.ofNat 64 36452
@[simp, arm64_norm, wp_norm] private abbrev offSeg6E1Body : BitVec 64 := BitVec.ofNat 64 36592
@[simp, arm64_norm, wp_norm] private abbrev offSeg6E1Br   : BitVec 64 := BitVec.ofNat 64 36748
@[simp, arm64_norm, wp_norm] private abbrev offSeg6E1Copy : BitVec 64 := BitVec.ofNat 64 36752
@[simp, arm64_norm, wp_norm] private abbrev offSeg6E1Out  : BitVec 64 := BitVec.ofNat 64 36960
@[simp, arm64_norm, wp_norm] abbrev offSeg6E2     : BitVec 64 := BitVec.ofNat 64 36964
local macro "step_strQ14432 " k:num : tactic => `(tactic| (
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

private theorem seg6_e1_zero [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = b + offSeg6E1Loop) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + offSeg6E1Body) s
      (memRegion (sp + 14432#64) 512 ∗ Rest)
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
        s1.readReg64 .fp = s.readReg64 .fp ∧
        s1.readVReg128 3#5 = s.readVReg128 3#5 ∧
        (P1 ⊢ memRegion (sp + 14432#64) 512 ∗ Rest)) := by
  subst hbase
  have hal_sp : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  wp_steps 3
  apply SepWP.of_memRegion_vecRangeMem 32 (sp + 14432#64) (by decide) rfl
  intro f
  rw [show VecRangeMem 32 (sp + 14432#64) f = PolyMem (sp + 14432#64) f from rfl, ← poly32Mem_ofFn]
  step_strQ14432 31; step_strQ14432 30; step_strQ14432 29; step_strQ14432 28
  step_strQ14432 27; step_strQ14432 26; step_strQ14432 25; step_strQ14432 24
  step_strQ14432 23; step_strQ14432 22; step_strQ14432 21; step_strQ14432 20
  step_strQ14432 19; step_strQ14432 18; step_strQ14432 17; step_strQ14432 16
  step_strQ14432 15; step_strQ14432 14; step_strQ14432 13; step_strQ14432 12
  step_strQ14432 11; step_strQ14432 10; step_strQ14432 9;  step_strQ14432 8
  step_strQ14432 7;  step_strQ14432 6;  step_strQ14432 5;  step_strQ14432 4
  step_strQ14432 3;  step_strQ14432 2;  step_strQ14432 1;  step_strQ14432 0
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], spAligned_of_sp_eq hspA hsp (by simp [hsp]),
      by simp, by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp, by simp, by simp,
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

private theorem seg6_e1_cbd2_iter [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp prfPtr dstPtr : BitVec 64) (prf : List (BitVec 8))
    {k : Nat} (hk : k < 32) (f : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + offSeg6E1Body) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx11 : s.readReg64 .x11 = BitVec.ofNat 64 (16 * k))
    (hx12 : s.readReg64 .x12 = prfPtr + 1#64 + BitVec.ofNat 64 (4 * k))
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx21 : s.readReg64 .x21 = dstPtr) :
    SepWP (blkPC06.rebase b (fun _ => none))
      (if k < 31 then b + offSeg6E1Body else b + offSeg6E1Copy) s
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
        s'.readReg64 .fp = s.readReg64 .fp ∧
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
    refine step_bCond_taken (dst := blkPl06.base + offSeg6E1Body)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp; clear * - hk31
          rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
            _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;> first | decide | omega)
      (by clear * -; dsimp [offSeg6E1Br, offSeg6E1Body]; bv_omega) ?_
    refine SepWP.done (by simp [State.setPC]) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp, by simp, by simp,
        by simp; clear * -; bv_omega,
        by simp; clear * -; bv_omega,
        by simp [hx19], by simp, by simp [hx21], by simp, by simp, by simp,
        hmem_eq _ fun j hj => by rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;> first | rfl | omega⟩
  · have hk_eq : k = 31 := by omega
    subst hk_eq
    simp only [show ¬(31 < 31) by omega, ↓reduceIte]
    refine step_bCond_not_taken (dst := blkPl06.base + offSeg6E1Copy)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp)
      (by clear * -; dsimp [offSeg6E1Br, offSeg6E1Copy]; bv_omega) ?_
    refine SepWP.done (by simp [State.setPC]) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp, by simp, by simp,
        by simp, by simp,
        by simp [hx19], by simp, by simp [hx21], by simp, by simp, by simp,
        hmem_eq _ fun j hj => by rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;> first | rfl | omega⟩
private theorem seg6_e1_cbd2_steps [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (sp prfPtr dstPtr : BitVec 64) (prf : List (BitVec 8)) (Rest : SepProp) :
    ∀ (rem k : Nat), rem + k = 32 → ∀ (s : State) (f : Nat → BitVec 128),
      (∀ i, i < k → f i = polyVecNat (neonCbd2Poly16 prf) i) →
      s.pc = (if k < 32 then b + offSeg6E1Body else b + offSeg6E1Copy) →
      s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x11 = BitVec.ofNat 64 (16 * k) →
      s.readReg64 .x12 = prfPtr + 1#64 + BitVec.ofNat 64 (4 * k) →
      s.readReg64 .x19 = 0x55555555#64 → s.readReg64 .x21 = dstPtr →
      SepWP (blkPC06.rebase b (fun _ => none)) (b + offSeg6E1Copy) s
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
          s'.readReg64 .fp = s.readReg64 .fp ∧
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
      ⟨hsp, hspA, rfl, rfl, rfl, hx19, rfl, hx21, rfl, rfl, rfl, by
        dsimp only [PolyMem]
        rw [vecRangeMem_congr hf]⟩
  | succ rem ih =>
    intro k hsum s f hf hpc hrun hsp hspA hx11 hx12 hx19 hx21
    have hk : k < 32 := by omega
    simp only [hk, ↓reduceIte] at hpc
    refine SepWP.seq
      (seg6_e1_cbd2_iter hb hbase s sp prfPtr dstPtr prf hk f Rest
        hpc hrun hsp hspA hx11 hx12 hx19 hx21) ?_
    rintro s1 P1 hpc1 hrun1 ⟨hsp1, hspA1, r8, r9, r10, hx11_1, hx12_1, hx19_1, r20, hx21_1, r22, rfp, rv3, hP1⟩
    subst hP1
    refine SepWP.seq
      (ih (k + 1) (by omega) s1 _
        (fun i hi => by
          by_cases hik : i = k
          · subst hik; exact Function.update_self i _ f
          · rw [Function.update_of_ne hik]; exact hf i (by omega))
        (by by_cases hk31 : k < 31 <;> simp [hk31, show (k + 1 < 32) ↔ k < 31 by omega] at hpc1 ⊢ <;> exact hpc1)
        hrun1 hsp1 hspA1 hx11_1 hx12_1 hx19_1 hx21_1) ?_
    rintro s2 P2 hpc2 hrun2 ⟨hsp2, hspA2, g8, g9, g10, gx19, g20, gx21, g22, gfp, gv3, hP2⟩
    exact SepWP.done hpc2 hrun2 ⟨hsp2, hspA2, g8.trans r8, g9.trans r9, g10.trans r10,
      gx19, g20.trans r20, gx21, g22.trans r22, gfp.trans rfp, gv3.trans rv3, hP2⟩
local macro "ldr_src14432 " k:num : tactic => `(tactic| (
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

private theorem seg6_e1_copy [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp : BitVec 64) {idx : Nat} (hidx : idx < 4)
    (src dst : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + offSeg6E1Copy) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 idx)
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 (idx + 1))
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 28368#64)
    (hx21 : s.readReg64 .x21 = sp + 14432#64) :
    let dstPtr := sp + 28368#64 + BitVec.ofNat 64 (512 * idx)
    SepWP (blkPC06.rebase b (fun _ => none))
      (if idx < 3 then b + offSeg6E1Loop else b + offSeg6E2) s
      (Poly32Mem (sp + 14432#64) src ∗ Poly32Mem dstPtr dst ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x8 = BitVec.ofNat 64 (idx + 1) ∧
        s'.readReg64 .x9 = s.readReg64 .x9 + 128#64 ∧
        s'.readReg64 .x19 = 0x55555555#64 ∧
        s'.readReg64 .x20 = sp + 28368#64 ∧
        s'.readReg64 .x21 = sp + 14432#64 ∧
        s'.readReg64 .x22 = s.readReg64 .x22 ∧
        s'.readReg64 .fp = s.readReg64 .fp ∧
        s'.readVReg128 3#5 = s.readVReg128 3#5 ∧
        P' = (Poly32Mem (sp + 14432#64) src ∗ Poly32Mem dstPtr src ∗ Rest)) := by
  intro dstPtr
  subst hbase
  have hal_sp : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  have hx11_eq : (sp + 28368#64) + (BitVec.ofNat 64 idx <<< 9) = dstPtr := by
    dsimp only [dstPtr]; clear * - hidx
    rcases (show idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 by omega) with rfl | rfl | rfl | rfl <;> bv_omega
  wp_step
  ldr_src14432 0; ldr_src14432 1; ldr_src14432 3
  wp_steps 2
  stp_dst_e1 0
  ldr_src14432 2; ldr_src14432 5
  wp_step
  stp_dst_e1 1
  ldr_src14432 4;  ldr_src14432 7;  stp_dst_e1 2
  ldr_src14432 6;  ldr_src14432 9;  stp_dst_e1 3
  ldr_src14432 8;  ldr_src14432 11; stp_dst_e1 4
  ldr_src14432 10; ldr_src14432 13; stp_dst_e1 5
  ldr_src14432 12; ldr_src14432 15; stp_dst_e1 6
  ldr_src14432 14; ldr_src14432 17; stp_dst_e1 7
  ldr_src14432 16; ldr_src14432 19; stp_dst_e1 8
  ldr_src14432 18; ldr_src14432 21; stp_dst_e1 9
  ldr_src14432 20; ldr_src14432 23; stp_dst_e1 10
  ldr_src14432 22; ldr_src14432 25; stp_dst_e1 11
  ldr_src14432 24; ldr_src14432 27; stp_dst_e1 12
  ldr_src14432 26; ldr_src14432 29; stp_dst_e1 13
  ldr_src14432 28; ldr_src14432 31; stp_dst_e1 14
  ldr_src14432 30; stp_dst_e1 15
  by_cases hidx3 : idx < 3
  · simp only [hidx3, ↓reduceIte]
    refine step_bCond_taken (dst := blkPl06.base + offSeg6E1Loop)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp; clear * - hidx3; rcases idx with _ | _ | _ | idx <;> first | decide | omega)
      (by clear * -; dsimp [offSeg6E1Out, offSeg6E1Loop]; bv_omega) ?_
    refine SepWP.done (by simp [State.setPC]) (by simp [hrun])
      ⟨by simp [hsp], spAligned_of_sp_eq hspA hsp (by simp [hsp]),
        by simp, by simp, by simp [hx19], by simp [hx20], by simp [hx21], by simp, by simp, by simp,
        by clear * -; cases src; rfl⟩
  · have hidx_eq : idx = 3 := by omega
    subst hidx_eq
    simp only [show ¬(3 < 3) by omega, ↓reduceIte]
    refine step_bCond_not_taken (dst := blkPl06.base + offSeg6E2)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp)
      (by clear * -; dsimp [offSeg6E1Out, offSeg6E2]; bv_omega) ?_
    refine SepWP.done (by simp [State.setPC]) (by simp [hrun])
      ⟨by simp [hsp], spAligned_of_sp_eq hspA hsp (by simp [hsp]),
        by simp, by simp, by simp [hx19], by simp [hx20], by simp [hx21], by simp, by simp, by simp,
        by clear * -; cases src; rfl⟩
private theorem seg6_e1_iter [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp : BitVec 64) {idx : Nat} (hidx : idx < 4)
    (prf : List (BitVec 8)) (hprf : prf.length = 128)
    (prev : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + offSeg6E1Loop) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 idx)
    (hx9 : s.readReg64 .x9 = sp + 30449#64 + BitVec.ofNat 64 (128 * idx))
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 28368#64)
    (hx21 : s.readReg64 .x21 = sp + 14432#64) :
    let prfPtr := sp + 30448#64 + BitVec.ofNat 64 (128 * idx)
    let dstPtr := sp + 28368#64 + BitVec.ofNat 64 (512 * idx)
    SepWP (blkPC06.rebase b (fun _ => none))
      (if idx < 3 then b + offSeg6E1Loop else b + offSeg6E2) s
      ((prfPtr ↦ₛ prf) ∗ memRegion (sp + 14432#64) 512 ∗ PolyMem dstPtr prev ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x8 = BitVec.ofNat 64 (idx + 1) ∧
        sf.readReg64 .x9 = sp + 30449#64 + BitVec.ofNat 64 (128 * (idx + 1)) ∧
        sf.readReg64 .x19 = 0x55555555#64 ∧
        sf.readReg64 .x20 = sp + 28368#64 ∧
        sf.readReg64 .x21 = sp + 14432#64 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readVReg128 3#5 = s.readVReg128 3#5 ∧
        (Pf ⊢ (prfPtr ↦ₛ prf) ∗ memRegion (sp + 14432#64) 512 ∗
          PolyMem dstPtr (polyVecNat (neonCbd2Poly16 prf)) ∗ Rest)) := by
  intro prfPtr dstPtr
  rw [← wordRangeMem32_eq_pointsToBytes prfPtr hprf]
  refine SepWP.weaken_pre
    (P' := memRegion (sp + 14432#64) 512 ∗
      (WordRangeMem 32 prfPtr (readU32LE prf) ∗ PolyMem dstPtr prev ∗ Rest)) (by sep_frame) ?_
  refine SepWP.seq (seg6_e1_zero hb hbase s sp _ hpc hrun hsp hspA) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hsp1, hspA1, hx8_1, hx9_1, hx10_1, hx11_1, hx12_1,
    hx19_1, hx20_1, hx21_1, _, hfp1, hv3_1, hP1⟩
  refine SepWP.weaken_pre hP1 ?_
  apply SepWP.of_memRegion_vecRangeMem 32 (sp + 14432#64) (hf := by sep_focus); intro f14432
  refine SepWP.weaken_pre
    (P' := WordRangeMem 32 prfPtr (readU32LE prf) ∗ VecRangeMem 32 (sp + 14432#64) f14432 ∗
      (PolyMem dstPtr prev ∗ Rest)) (by sep_frame) ?_
  refine SepWP.seq
    (seg6_e1_cbd2_steps hb hbase sp prfPtr (sp + 14432#64) prf _ 32 0 rfl s1 f14432
      (fun _ h => by omega) (by simpa using hpc1) hrun1 hsp1 hspA1 hx11_1
      (by rw [hx12_1, hx9]; dsimp only [prfPtr]; clear * -; bv_omega)
      (hx19_1.trans hx19) (hx21_1.trans hx21)) ?_
  rintro s2 P2 hpc2 hrun2 ⟨hsp2, hspA2, hx8_2, hx9_2, hx10_2, hx19_2, hx20_2, hx21_2, _, hfp2, hv3_2, hP2⟩
  subst hP2
  rw [← poly32Mem_ofFn (sp + 14432#64), ← poly32Mem_ofFn dstPtr prev]
  refine SepWP.weaken_pre
    (P' := Poly32Mem (sp + 14432#64) (Vec32.ofFn (polyVecNat (neonCbd2Poly16 prf))) ∗
      Poly32Mem dstPtr (Vec32.ofFn prev) ∗ (WordRangeMem 32 prfPtr (readU32LE prf) ∗ Rest))
    (by sep_frame) ?_
  have hx10_eq : s2.readReg64 .x10 = BitVec.ofNat 64 (idx + 1) := by
    rw [hx10_2, hx10_1, hx8]; clear * - hidx; rcases idx with _ | _ | _ | _ | idx <;> first | decide | omega
  refine SepWP.seq
    (seg6_e1_copy hb hbase s2 sp hidx _ _ _ hpc2 hrun2 hsp2 hspA2
      (hx8_2.trans (hx8_1.trans hx8)) hx10_eq hx19_2
      (hx20_2.trans (hx20_1.trans hx20)) hx21_2) ?_
  rintro sf Pf hpcf hrunf ⟨hspf, hspAf, r8, r9, r19, r20, r21, _, rfp, rv3, hPf⟩
  refine SepWP.done hpcf hrunf
    ⟨hspf, hspAf, r8, by rw [r9, hx9_2, hx9_1, hx9]; clear * -; bv_omega,
      r19, r20, r21, rfp.trans (hfp2.trans hfp1), rv3.trans (hv3_2.trans hv3_1), ?_⟩
  rw [hPf, poly32Mem_ofFn dstPtr, wordRangeMem32_eq_pointsToBytes prfPtr hprf]
  exact entails_sub (poly32Mem_entails_memRegion (sp + 14432#64) _) (by sep_frame) (by sep_frame)
theorem seg6_e1_loop_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp : BitVec 64) (coins : List (BitVec 8))
    (z0 z1 z2 z3 : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + offSeg6E1Loop) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = 0#64)
    (hx9 : s.readReg64 .x9 = sp + 30449#64)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 28368#64)
    (hx21 : s.readReg64 .x21 = sp + 14432#64)
    (hv3 : s.readVReg128 3#5 = 0#128) :
    let prf4 := shake256List 128 (coins ++ [4#8])
    let prf5 := shake256List 128 (coins ++ [5#8])
    let prf6 := shake256List 128 (coins ++ [6#8])
    let prf7 := shake256List 128 (coins ++ [7#8])
    SepWP (blkPC06.rebase b (fun _ => none)) (b + offSeg6E2) s
      (((sp + 30448#64) ↦ₛ prf4) ∗ ((sp + 30576#64) ↦ₛ prf5) ∗
       ((sp + 30704#64) ↦ₛ prf6) ∗ ((sp + 30832#64) ↦ₛ prf7) ∗
       memRegion (sp + 14432#64) 512 ∗
       PolyMem (sp + 28368#64) z0 ∗ PolyMem (sp + 28880#64) z1 ∗
       PolyMem (sp + 29392#64) z2 ∗ PolyMem (sp + 29904#64) z3 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x19 = 0x55555555#64 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readVReg128 3#5 = 0#128 ∧
        (Pf ⊢ memRegion (sp + 30448#64) 512 ∗ memRegion (sp + 14432#64) 512 ∗
          PolyMem (sp + 28368#64) (polyVecNat (neonCbd2Poly16 prf4)) ∗
          PolyMem (sp + 28880#64) (polyVecNat (neonCbd2Poly16 prf5)) ∗
          PolyMem (sp + 29392#64) (polyVecNat (neonCbd2Poly16 prf6)) ∗
          PolyMem (sp + 29904#64) (polyVecNat (neonCbd2Poly16 prf7)) ∗ Rest)) := by
  intro prf4 prf5 prf6 prf7
  have h4 : prf4.length = 128 := shake256List_length 128 _
  have h5 : prf5.length = 128 := shake256List_length 128 _
  have h6 : prf6.length = 128 := shake256List_length 128 _
  have h7 : prf7.length = 128 := shake256List_length 128 _
  have ha_30576 : sp + 30448#64 + 128#64 = sp + 30576#64 := by clear * -; bv_omega
  have ha_30704 : sp + 30448#64 + 256#64 = sp + 30704#64 := by clear * -; bv_omega
  have ha_30832 : sp + 30448#64 + 384#64 = sp + 30832#64 := by clear * -; bv_omega
  have ha_28880 : sp + 28368#64 + 512#64 = sp + 28880#64 := by clear * -; bv_omega
  have ha_29392 : sp + 28368#64 + 1024#64 = sp + 29392#64 := by clear * -; bv_omega
  have ha_29904 : sp + 28368#64 + 1536#64 = sp + 29904#64 := by clear * -; bv_omega
  refine SepWP.weaken_pre
    (P' := ((sp + 30448#64 + 0#64) ↦ₛ prf4) ∗ memRegion (sp + 14432#64) 512 ∗
      PolyMem (sp + 28368#64 + 0#64) z0 ∗
      (((sp + 30576#64) ↦ₛ prf5) ∗ ((sp + 30704#64) ↦ₛ prf6) ∗ ((sp + 30832#64) ↦ₛ prf7) ∗
        PolyMem (sp + 28880#64) z1 ∗ PolyMem (sp + 29392#64) z2 ∗ PolyMem (sp + 29904#64) z3 ∗ Rest))
    (by simp only [BitVec.add_zero]; sep_frame) ?_
  refine SepWP.seq
    (seg6_e1_iter hb hbase s sp (idx := 0) (by decide) prf4 h4 z0 _
      hpc hrun hsp hspA hx8 (by simpa using hx9) hx19 hx20 hx21) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hsp1, hspA1, hx8_1, hx9_1, hx19_1, hx20_1, hx21_1, hfp1, hv3_1, hP1⟩
  refine SepWP.weaken_pre (Entails.trans hP1
    (show (((sp + 30448#64 + 0#64) ↦ₛ prf4) ∗ memRegion (sp + 14432#64) 512 ∗
        PolyMem (sp + 28368#64 + 0#64) (polyVecNat (neonCbd2Poly16 prf4)) ∗
        (((sp + 30576#64) ↦ₛ prf5) ∗ ((sp + 30704#64) ↦ₛ prf6) ∗ ((sp + 30832#64) ↦ₛ prf7) ∗
          PolyMem (sp + 28880#64) z1 ∗ PolyMem (sp + 29392#64) z2 ∗ PolyMem (sp + 29904#64) z3 ∗ Rest)) ⊢
      ((sp + 30448#64 + 128#64) ↦ₛ prf5) ∗ memRegion (sp + 14432#64) 512 ∗
        PolyMem (sp + 28368#64 + 512#64) z1 ∗
        (((sp + 30448#64) ↦ₛ prf4) ∗ ((sp + 30704#64) ↦ₛ prf6) ∗ ((sp + 30832#64) ↦ₛ prf7) ∗
          PolyMem (sp + 28368#64) (polyVecNat (neonCbd2Poly16 prf4)) ∗
          PolyMem (sp + 29392#64) z2 ∗ PolyMem (sp + 29904#64) z3 ∗ Rest) by
      simp only [BitVec.add_zero, ha_30576, ha_28880]; sep_frame)) ?_
  refine SepWP.seq
    (seg6_e1_iter hb hbase s1 sp (idx := 1) (by decide) prf5 h5 z1 _
      (by simpa using hpc1) hrun1 hsp1 hspA1 hx8_1 hx9_1 hx19_1 hx20_1 hx21_1) ?_
  rintro s2 P2 hpc2 hrun2 ⟨hsp2, hspA2, hx8_2, hx9_2, hx19_2, hx20_2, hx21_2, hfp2, hv3_2, hP2⟩
  refine SepWP.weaken_pre (Entails.trans hP2
    (show (((sp + 30448#64 + 128#64) ↦ₛ prf5) ∗ memRegion (sp + 14432#64) 512 ∗
        PolyMem (sp + 28368#64 + 512#64) (polyVecNat (neonCbd2Poly16 prf5)) ∗
        (((sp + 30448#64) ↦ₛ prf4) ∗ ((sp + 30704#64) ↦ₛ prf6) ∗ ((sp + 30832#64) ↦ₛ prf7) ∗
          PolyMem (sp + 28368#64) (polyVecNat (neonCbd2Poly16 prf4)) ∗
          PolyMem (sp + 29392#64) z2 ∗ PolyMem (sp + 29904#64) z3 ∗ Rest)) ⊢
      ((sp + 30448#64 + 256#64) ↦ₛ prf6) ∗ memRegion (sp + 14432#64) 512 ∗
        PolyMem (sp + 28368#64 + 1024#64) z2 ∗
        (((sp + 30448#64) ↦ₛ prf4) ∗ ((sp + 30576#64) ↦ₛ prf5) ∗ ((sp + 30832#64) ↦ₛ prf7) ∗
          PolyMem (sp + 28368#64) (polyVecNat (neonCbd2Poly16 prf4)) ∗
          PolyMem (sp + 28880#64) (polyVecNat (neonCbd2Poly16 prf5)) ∗
          PolyMem (sp + 29904#64) z3 ∗ Rest) by
      simp only [ha_30576, ha_30704, ha_28880, ha_29392]; sep_frame)) ?_
  refine SepWP.seq
    (seg6_e1_iter hb hbase s2 sp (idx := 2) (by decide) prf6 h6 z2 _
      (by simpa using hpc2) hrun2 hsp2 hspA2 hx8_2 hx9_2 hx19_2 hx20_2 hx21_2) ?_
  rintro s3 P3 hpc3 hrun3 ⟨hsp3, hspA3, hx8_3, hx9_3, hx19_3, hx20_3, hx21_3, hfp3, hv3_3, hP3⟩
  refine SepWP.weaken_pre (Entails.trans hP3
    (show (((sp + 30448#64 + 256#64) ↦ₛ prf6) ∗ memRegion (sp + 14432#64) 512 ∗
        PolyMem (sp + 28368#64 + 1024#64) (polyVecNat (neonCbd2Poly16 prf6)) ∗
        (((sp + 30448#64) ↦ₛ prf4) ∗ ((sp + 30576#64) ↦ₛ prf5) ∗ ((sp + 30832#64) ↦ₛ prf7) ∗
          PolyMem (sp + 28368#64) (polyVecNat (neonCbd2Poly16 prf4)) ∗
          PolyMem (sp + 28880#64) (polyVecNat (neonCbd2Poly16 prf5)) ∗
          PolyMem (sp + 29904#64) z3 ∗ Rest)) ⊢
      ((sp + 30448#64 + 384#64) ↦ₛ prf7) ∗ memRegion (sp + 14432#64) 512 ∗
        PolyMem (sp + 28368#64 + 1536#64) z3 ∗
        (((sp + 30448#64) ↦ₛ prf4) ∗ ((sp + 30576#64) ↦ₛ prf5) ∗ ((sp + 30704#64) ↦ₛ prf6) ∗
          PolyMem (sp + 28368#64) (polyVecNat (neonCbd2Poly16 prf4)) ∗
          PolyMem (sp + 28880#64) (polyVecNat (neonCbd2Poly16 prf5)) ∗
          PolyMem (sp + 29392#64) (polyVecNat (neonCbd2Poly16 prf6)) ∗ Rest) by
      simp only [ha_30704, ha_30832, ha_29392, ha_29904]; sep_frame)) ?_
  refine SepWP.seq
    (seg6_e1_iter hb hbase s3 sp (idx := 3) (by decide) prf7 h7 z3 _
      (by simpa using hpc3) hrun3 hsp3 hspA3 hx8_3 hx9_3 hx19_3 hx20_3 hx21_3) ?_
  rintro sf Pf hpcf hrunf ⟨hspf, hspAf, _, _, hx19f, _, _, hfpf, hv3f, hPf⟩
  refine SepWP.done (by simpa using hpcf) hrunf
    ⟨hspf, hspAf, hx19f, hfpf.trans (hfp3.trans (hfp2.trans hfp1)),
      hv3f.trans (hv3_3.trans (hv3_2.trans (hv3_1.trans hv3))), Entails.trans hPf ?_⟩
  simp only [ha_30832, ha_29904]
  have hm512 : ((sp + 30448#64) ↦ₛ prf4) ∗ ((sp + 30576#64) ↦ₛ prf5) ∗
      ((sp + 30704#64) ↦ₛ prf6) ∗ ((sp + 30832#64) ↦ₛ prf7) ⊢ memRegion (sp + 30448#64) 512 := by
    rw [memRegion_split' (b' := sp + 30576#64) (n := 128) (k := (384 : Nat)) rfl (by clear * -; bv_omega) (by decide),
        memRegion_split' (b' := sp + 30704#64) (n := 128) (k := (256 : Nat)) rfl (by clear * -; bv_omega) (by decide),
        memRegion_split' (b' := sp + 30832#64) (n := 128) (k := (128 : Nat)) rfl (by clear * -; bv_omega) (by decide)]
    exact sepConj_mono (by simpa [h4] using pointsToBytes_entails_memRegion (sp + 30448#64) prf4)
      (sepConj_mono (by simpa [h5] using pointsToBytes_entails_memRegion (sp + 30576#64) prf5)
        (sepConj_mono (by simpa [h6] using pointsToBytes_entails_memRegion (sp + 30704#64) prf6)
          (by simpa [h7] using pointsToBytes_entails_memRegion (sp + 30832#64) prf7)))
  exact entails_sub hm512 (by sep_frame) (by sep_frame)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6E1Loop
