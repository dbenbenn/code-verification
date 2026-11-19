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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymBridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakLoop -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Defs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2InitA -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Defs
public meta import ProofLib.GenPlacedFetches
meta import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1bPure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Keccak06

/-!
# `kyber_decapsulate` (`B06`) — Segment 5 Row Init Slice A (`+0x4170 .. +0x4944`)

Row entry `memset(sp+4160, 0, 2176)`, 4-lane SHAKE-128 absorb + 24-round `L1`/`L2` permutations,
and `memset(sp+31752, 0, 712)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5InitA

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemData01Bytes mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl resolve_blk29 seq_codeLoaded_lr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak (keccakAbsorb keccakF1600)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem (
  MultiLaneSampled MultiLaneSlots)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (entails_sub)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  SepStore128.left step_strQ128)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base (
  blk06_code_eq blk06_tree_size blkLib06 blkPC06 blkPl06 blkPlaceable06 blkTree06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1bPure (
  exec_simdMovi_2d_0 rhoW)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymDefs (
  BTree KCfg KEnv KExpr KSlot KState evalKExpr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymBridge (
  BTreeMem KSpatial KStateMatches SepWP.of_memRegion_btreeMem evalMemTree sepStore128_btreeMem)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakLoop (
  btree_ext_get slotHolds vreg128_repack)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Base (
  KProgStep evalExprList25 eval_checked_gpr eval_checked_memA exprVarsOk
  extendLoopVars keccakAbsorb_rowSeed preAbsorbState rowSeed specEnvSteps)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Defs (
  btreeMem4_zero_eq_multiLaneSampled4 memset2176_eq_multiLaneSlots4
  slotsFa8_01 slotsFa8_23 slotsL1 slotsL2)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2InitA (
  btreeMem_zero checkOutSlots checked_outSlots evalExprList25_preAbsorb expPreAbsorb
  headerIdxs slotHolds_spill_transfer)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Defs (
  MemAHeaderOk06 RowCalleeGprs06 blk29_memset_06 cfgA06 cfgA06_valid cfgB06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Keccak06 (
  runAndCheckKProg06 sepWP_of_runAndCheckKProg06)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC06 blkLib06 blkTree06 blk06_code_eq blk06_tree_size
  via_placement blkPl06 blkPlaceable06 [0x4170 → 0x4194, 0x4940 → 0x4944]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl06_ρ [MlKemPlacement] (sym : String) :
    blkPl06.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

/-! ## 1. Row Init Slice A Pre/Post Predicates & Symbolic Certificate -/

@[expose] def RowEntryGprs06 (sp rcBase fpVal : BitVec 64) (s : State) : Prop :=
  s.readReg64 .x19 = 544#64 ∧ s.readReg64 .x20 = sp + 28379#64 ∧
  s.readReg64 .x22 = sp + 4160#64 ∧ s.readReg64 .x23 = sp + 26320#64 ∧
  s.readReg64 .x24 = 256#64 ∧ s.readReg64 .x25 = sp + 28368#64 ∧
  s.readReg64 .x26 = sp + 28632#64 ∧ s.readReg64 .x28 = rcBase ∧
  s.readReg64 .fp = fpVal

@[expose] def RowInitAPre06 [MlKemPlacement] (sp rcBase fpVal : BitVec 64)
    (rho : List (BitVec 8)) (row : Nat) (Rest : SepProp) (s : State) (P : SepProp) : Prop :=
  s.sp = sp ∧ s.spAligned = true ∧ (sp &&& 15#64 == 0#64) = true ∧
  mlkemMultiLib.CodeLoaded mlkemMpl s.mem ∧ MlKemRoOk mlkemMpl s.mem ∧
  RowEntryGprs06 sp rcBase fpVal s ∧ s.readReg64 .x1 = BitVec.ofNat 64 row ∧
  ∃ tA : BTree (BitVec 64) 9, MemAHeaderOk06 sp rho tA ∧
    (P ⊢ (rcBase ↦ᵣ mlkemData01Bytes) ∗ BTreeMem (sp + 144#64) 286 tA ∗
      memRegion (sp + 26320#64) 32 ∗ memRegion (sp + 4160#64) 2176 ∗
      memRegion (sp + 28368#64) 672 ∗ memRegion (sp + 30448#64) 2016 ∗ Rest)

@[expose] def RowInitAPost06 [MlKemPlacement] (sp rcBase fpVal : BitVec 64)
    (rho : List (BitVec 8)) (row : Nat) (Rest : SepProp) (sf : State) (Pf : SepProp) : Prop :=
  sf.sp = sp ∧ sf.spAligned = true ∧ (sp &&& 15#64 == 0#64) = true ∧
  mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
  RowCalleeGprs06 sp rcBase fpVal row sf ∧
  ∃ tA : BTree (BitVec 64) 9, MemAHeaderOk06 sp rho tA ∧
    (∀ idx, idx < 25 → slotHolds cfgB06 sf tA (slotsFa8_01.getD idx (.vreg 0))
      ((keccakAbsorb 21 0x1f#8 (rowSeed rho row 0)).getD idx 0#64)
      ((keccakAbsorb 21 0x1f#8 (rowSeed rho row 1)).getD idx 0#64)) ∧
    (∀ idx, idx < 25 → slotHolds cfgB06 sf tA (slotsFa8_23.getD idx (.vreg 0))
      ((keccakAbsorb 21 0x1f#8 (rowSeed rho row 2)).getD idx 0#64)
      ((keccakAbsorb 21 0x1f#8 (rowSeed rho row 3)).getD idx 0#64)) ∧
    (Pf ⊢ (rcBase ↦ᵣ mlkemData01Bytes) ∗ BTreeMem (sp + 144#64) 286 tA ∗
      MultiLaneSampled (sp + 26320#64) 4 (fun _ => 0) ∗
      MultiLaneSlots (sp + 4160#64) 544 4 (fun _ => List.replicate 272 0#16) ∗
      memRegion (sp + 28368#64) 672 ∗ memRegion (sp + 30448#64) 2016 ∗ Rest)

@[expose] def headerMemAExpr06 (i : Nat) : KExpr :=
  if i == 0 then .const64 0x00000000001f0300#64 else if i == 1 then .const64 0#64
  else if i == 2 then .const64 0x00000000001f0200#64 else if i == 3 then .const64 0#64
  else if i == 4 then .const64 0x00000000001f0100#64 else if i == 5 then .const64 0#64
  else if i == 7 then .spAdd 28379#64 else if i == 8 then .spAdd 30459#64
  else if i == 9 then .spAdd 30712#64 else if i == 14 then .const64 0xffffffffff0000ff#64
  else if i == 15 then .const64 0xffffffffffffffff#64 else if i == 16 || i == 17 then .var 103
  else if i == 18 || i == 19 then .var 102 else if i == 20 || i == 21 then .var 101
  else if i == 22 || i == 23 then .var 100 else .var (200 + i)

@[expose] def calleeGprExpr06 (g : Nat) : KExpr :=
  if g == 19 then .const64 544#64 else if g == 20 then .spAdd 28379#64
  else if g == 21 then .var 64 else if g == 22 then .spAdd 4160#64
  else if g == 23 then .spAdd 26320#64 else if g == 24 then .const64 256#64
  else if g == 25 then .spAdd 28368#64 else if g == 26 then .spAdd 28632#64
  else if g == 28 then .rcAdd 0#64 else if g == 29 then .var 99
  else .var (65 + g)

@[expose] def calleeGprIdxs06 : List Nat :=
  [19, 20, 21, 22, 23, 24, 25, 26, 28, 29]

@[expose] def stInitA06 : KState :=
  { vregs := BTree.ofFn 5 (fun vr => (.var (2 * vr), .var (2 * vr + 1)))
    gprs  := BTree.ofFn 5 calleeGprExpr06
    memA  := BTree.ofFn 9 headerMemAExpr06
    memB  := BTree.ofFn 9 (fun _ => .const64 0#64)
    zFlag := none }

private def stepsA06 : List KProgStep :=
  [.range 4197 34,
   .loop 4231 197 8#5 slotsL1 (expPreAbsorb 0) (expPreAbsorb 1) 1000,
   .range 4429 49,
   .loop 4478 190 8#5 slotsL2 (expPreAbsorb 2) (expPreAbsorb 3) 2000,
   .range 4669 19]

@[expose] def checkHeaderPreserved06 (ok : Nat → Bool) (st : KState) : Bool :=
  headerIdxs.all fun i =>
    (st.memA.get i).beq (headerMemAExpr06 i) && exprVarsOk ok (headerMemAExpr06 i)

@[expose] def checkCalleeGprsPreserved06 (ok : Nat → Bool) (st : KState) : Bool :=
  calleeGprIdxs06.all fun g =>
    (st.gprs.get g).beq (calleeGprExpr06 g) && exprVarsOk ok (calleeGprExpr06 g)

private def chkSliceA06 (ok : Nat → Bool) (st : KState) : Bool :=
  (st.gprs.get 0).beq (.spAdd 31752#64) && exprVarsOk ok (.spAdd 31752#64) &&
  (st.gprs.get 1).beq (.const64 0#64) && exprVarsOk ok (.const64 0#64) &&
  (st.gprs.get 2).beq (.const64 712#64) && exprVarsOk ok (.const64 712#64) &&
  checkHeaderPreserved06 ok st && checkCalleeGprsPreserved06 ok st &&
  checkOutSlots cfgA06 ok st slotsFa8_01 1000 && checkOutSlots cfgA06 ok st slotsFa8_23 2000

private theorem cert_sliceA06 :
    runAndCheckKProg06 cfgA06 4197 4688 4197 4688 800 stepsA06 stInitA06 chkSliceA06 = true := by
  decide +kernel

attribute [local irreducible] blkPC06 keccakF1600 keccakAbsorb BTreeMem
attribute [local wp_norm ↓ high] exec_simdMovi_2d_0

/-! ## 2. Environment Matching & Checked Extractors -/

@[expose] def envInitA06 (sp rcBase fpVal : BitVec 64) (rho : List (BitVec 8)) (row : Nat)
    (s : State) (tA : BTree (BitVec 64) 9) : KEnv :=
  { sp := sp, rcBase := rcBase, rLoop := 0
    vars := fun id =>
      if id < 64 then
        let v := s.readVReg128 (BitVec.ofNat 5 (id / 2))
        if id % 2 == 0 then v.truncate 64 else (v >>> 64).truncate 64
      else if id == 64 then BitVec.ofNat 64 row
      else if id < 97 then s.readReg64 (.gpr (BitVec.ofNat 5 (id - 65)))
      else if id == 99 then fpVal
      else if id == 100 then rhoW rho 0 else if id == 101 then rhoW rho 1
      else if id == 102 then rhoW rho 2 else if id == 103 then rhoW rho 3
      else if id < 712 then tA.get (id - 200) else 0#64 }

theorem eval_headerMemAExpr06 {sp rcBase fpVal : BitVec 64} {rho : List (BitVec 8)} {row : Nat}
    {s : State} {tA : BTree (BitVec 64) 9} (hhdr : MemAHeaderOk06 sp rho tA) :
    ∀ i, i < 2 ^ 9 →
      evalKExpr (envInitA06 sp rcBase fpVal rho row s tA) (headerMemAExpr06 i) = tA.get i := by
  rcases hhdr with ⟨h0, h1, h2, h3, h4, h5, h7, h8, h9, h14, h15,
    h16, h17, h18, h19, h20, h21, h22, h23⟩
  intro i hi
  by_cases hlt24 : i < 24
  · rcases (by omega :
        i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
        i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨
        i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [headerMemAExpr06, evalKExpr, envInitA06,
        h0, h1, h2, h3, h4, h5, h7, h8, h9, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23]
  · have hne : headerMemAExpr06 i = .var (200 + i) := by
      unfold headerMemAExpr06
      simp [beq_false_of_ne (by omega : i ≠ 0), beq_false_of_ne (by omega : i ≠ 1),
        beq_false_of_ne (by omega : i ≠ 2), beq_false_of_ne (by omega : i ≠ 3),
        beq_false_of_ne (by omega : i ≠ 4), beq_false_of_ne (by omega : i ≠ 5),
        beq_false_of_ne (by omega : i ≠ 7), beq_false_of_ne (by omega : i ≠ 8),
        beq_false_of_ne (by omega : i ≠ 9), beq_false_of_ne (by omega : i ≠ 14),
        beq_false_of_ne (by omega : i ≠ 15), beq_false_of_ne (by omega : i ≠ 16),
        beq_false_of_ne (by omega : i ≠ 17), beq_false_of_ne (by omega : i ≠ 18),
        beq_false_of_ne (by omega : i ≠ 19), beq_false_of_ne (by omega : i ≠ 20),
        beq_false_of_ne (by omega : i ≠ 21), beq_false_of_ne (by omega : i ≠ 22),
        beq_false_of_ne (by omega : i ≠ 23)]
    rw [hne]
    simp [evalKExpr, envInitA06, show ¬(200 + i < 64) by omega, show 200 + i ≠ 64 by omega,
      show ¬(200 + i < 97) by omega, show 200 + i ≠ 99 by omega, show 200 + i ≠ 100 by omega,
      show 200 + i ≠ 101 by omega, show 200 + i ≠ 102 by omega, show 200 + i ≠ 103 by omega,
      show 200 + i < 712 by omega]

theorem stInitA06_matches {sp rcBase fpVal : BitVec 64} {rho : List (BitVec 8)} {row : Nat}
    {s : State} {tA : BTree (BitVec 64) 9}
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hgprs : RowCalleeGprs06 sp rcBase fpVal row s) (hhdr : MemAHeaderOk06 sp rho tA) :
    KStateMatches (envInitA06 sp rcBase fpVal rho row s tA) stInitA06 s ∧
      BTreeMem (sp + 144#64) 286
        (evalMemTree (envInitA06 sp rcBase fpVal rho row s tA) stInitA06.memA) =
        BTreeMem (sp + 144#64) 286 tA := by
  rcases hgprs with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx28, hfp⟩
  refine ⟨⟨hsp, hspA, ?_, ?_, trivial⟩, ?_⟩
  · intro vr
    have hlt := vr.isLt
    simp only [stInitA06]; rw [BTree.get_ofFn 5 _ vr.toNat hlt]
    have h0lt : 2 * vr.toNat < 64 := by omega
    have h1lt : 2 * vr.toNat + 1 < 64 := by omega
    have hd0 : 2 * vr.toNat / 2 = vr.toNat := by omega
    have hm0 : (2 * vr.toNat % 2 == 0) = true := beq_iff_eq.mpr (by omega)
    have hd1 : (2 * vr.toNat + 1) / 2 = vr.toNat := by omega
    have hm1 : ((2 * vr.toNat + 1) % 2 == 0) = false := beq_false_of_ne (by omega)
    simp only [evalKExpr, envInitA06, h0lt, h1lt, ↓reduceIte, hd0, hm0, hd1, hm1,
      Bool.false_eq_true, BitVec.ofNat_toNat]
    exact (vreg128_repack (s.readVReg128 vr)).symm
  · intro g _hg31
    have hlt := g.isLt
    simp only [stInitA06]; rw [BTree.get_ofFn 5 _ g.toNat hlt]
    by_cases h19 : g = 19#5
    · subst h19; simpa [Reg.x19, calleeGprExpr06, evalKExpr, envInitA06] using hx19
    by_cases h20 : g = 20#5
    · subst h20; simpa [Reg.x20, calleeGprExpr06, evalKExpr, envInitA06] using hx20
    by_cases h21 : g = 21#5
    · subst h21; simpa [Reg.x21, calleeGprExpr06, evalKExpr, envInitA06] using hx21
    by_cases h22 : g = 22#5
    · subst h22; simpa [Reg.x22, calleeGprExpr06, evalKExpr, envInitA06] using hx22
    by_cases h23 : g = 23#5
    · subst h23; simpa [Reg.x23, calleeGprExpr06, evalKExpr, envInitA06] using hx23
    by_cases h24 : g = 24#5
    · subst h24; simpa [Reg.x24, calleeGprExpr06, evalKExpr, envInitA06] using hx24
    by_cases h25 : g = 25#5
    · subst h25; simpa [Reg.x25, calleeGprExpr06, evalKExpr, envInitA06] using hx25
    by_cases h26 : g = 26#5
    · subst h26; simpa [Reg.x26, calleeGprExpr06, evalKExpr, envInitA06] using hx26
    by_cases h28 : g = 28#5
    · subst h28; simpa [Reg.x28, calleeGprExpr06, evalKExpr, envInitA06] using hx28
    by_cases h29 : g = 29#5
    · subst h29; simpa [Reg.fp, calleeGprExpr06, evalKExpr, envInitA06] using hfp
    have hc : calleeGprExpr06 g.toNat = .var (65 + g.toNat) := by
      simp [calleeGprExpr06,
        show g.toNat ≠ 19 from fun e => h19 (BitVec.eq_of_toNat_eq e),
        show g.toNat ≠ 20 from fun e => h20 (BitVec.eq_of_toNat_eq e),
        show g.toNat ≠ 21 from fun e => h21 (BitVec.eq_of_toNat_eq e),
        show g.toNat ≠ 22 from fun e => h22 (BitVec.eq_of_toNat_eq e),
        show g.toNat ≠ 23 from fun e => h23 (BitVec.eq_of_toNat_eq e),
        show g.toNat ≠ 24 from fun e => h24 (BitVec.eq_of_toNat_eq e),
        show g.toNat ≠ 25 from fun e => h25 (BitVec.eq_of_toNat_eq e),
        show g.toNat ≠ 26 from fun e => h26 (BitVec.eq_of_toNat_eq e),
        show g.toNat ≠ 28 from fun e => h28 (BitVec.eq_of_toNat_eq e),
        show g.toNat ≠ 29 from fun e => h29 (BitVec.eq_of_toNat_eq e)]
    rw [hc]
    simp [evalKExpr, envInitA06, show ¬(65 + g.toNat < 64) by omega,
      show 65 + g.toNat ≠ 64 by omega, show 65 + g.toNat < 97 by omega, BitVec.ofNat_toNat]
  · congr 1; apply btree_ext_get; intro i hi
    simp only [evalMemTree, stInitA06]; rw [BTree.get_map, BTree.get_ofFn 9 _ i hi]
    exact eval_headerMemAExpr06 hhdr i hi

theorem checked_headerOk06 {ok : Nat → Bool} {envFinal envSpec : KEnv} {stEnd : KState}
    {sp : BitVec 64} {rho : List (BitVec 8)}
    (heval : ∀ e, exprVarsOk ok e = true → evalKExpr envFinal e = evalKExpr envSpec e)
    (hsp : envSpec.sp = sp)
    (h100 : envSpec.vars 100 = rhoW rho 0) (h101 : envSpec.vars 101 = rhoW rho 1)
    (h102 : envSpec.vars 102 = rhoW rho 2) (h103 : envSpec.vars 103 = rhoW rho 3)
    (hchk : checkHeaderPreserved06 ok stEnd = true) :
    MemAHeaderOk06 sp rho (evalMemTree envFinal stEnd.memA) := by
  have hall := List.all_eq_true.mp hchk
  have getH (i : Nat) (hmem : i ∈ headerIdxs) :
      (evalMemTree envFinal stEnd.memA).get i = evalKExpr envSpec (headerMemAExpr06 i) := by
    have hi := hall i hmem
    simp only [Bool.and_eq_true] at hi
    exact eval_checked_memA heval i (headerMemAExpr06 i) hi.1 hi.2
  refine ⟨by simpa [headerMemAExpr06, evalKExpr] using getH 0 (by decide),
    by simpa [headerMemAExpr06, evalKExpr] using getH 1 (by decide),
    by simpa [headerMemAExpr06, evalKExpr] using getH 2 (by decide),
    by simpa [headerMemAExpr06, evalKExpr] using getH 3 (by decide),
    by simpa [headerMemAExpr06, evalKExpr] using getH 4 (by decide),
    by simpa [headerMemAExpr06, evalKExpr] using getH 5 (by decide),
    by simpa [headerMemAExpr06, evalKExpr, hsp] using getH 7 (by decide),
    by simpa [headerMemAExpr06, evalKExpr, hsp] using getH 8 (by decide),
    by simpa [headerMemAExpr06, evalKExpr, hsp] using getH 9 (by decide),
    by simpa [headerMemAExpr06, evalKExpr] using getH 14 (by decide),
    by simpa [headerMemAExpr06, evalKExpr] using getH 15 (by decide),
    by simpa [headerMemAExpr06, evalKExpr, h103] using getH 16 (by decide),
    by simpa [headerMemAExpr06, evalKExpr, h103] using getH 17 (by decide),
    by simpa [headerMemAExpr06, evalKExpr, h102] using getH 18 (by decide),
    by simpa [headerMemAExpr06, evalKExpr, h102] using getH 19 (by decide),
    by simpa [headerMemAExpr06, evalKExpr, h101] using getH 20 (by decide),
    by simpa [headerMemAExpr06, evalKExpr, h101] using getH 21 (by decide),
    by simpa [headerMemAExpr06, evalKExpr, h100] using getH 22 (by decide),
    by simpa [headerMemAExpr06, evalKExpr, h100] using getH 23 (by decide)⟩

theorem checked_calleeGprs06 {ok : Nat → Bool} {envFinal envSpec : KEnv} {stEnd : KState}
    {sf : State} {sp rcBase fpVal : BitVec 64} {row : Nat}
    (hm : KStateMatches envFinal stEnd sf)
    (heval : ∀ e, exprVarsOk ok e = true → evalKExpr envFinal e = evalKExpr envSpec e)
    (hsp : envSpec.sp = sp) (hrc : envSpec.rcBase = rcBase)
    (h64 : envSpec.vars 64 = BitVec.ofNat 64 row)
    (h99 : envSpec.vars 99 = fpVal)
    (hchk : checkCalleeGprsPreserved06 ok stEnd = true) :
    RowCalleeGprs06 sp rcBase fpVal row sf := by
  have hall := List.all_eq_true.mp hchk
  have getG (r : BitVec 5) (hr : r ≠ 31#5) (hmem : r.toNat ∈ calleeGprIdxs06) :
      sf.readReg64 (.gpr r) = evalKExpr envSpec (calleeGprExpr06 r.toNat) := by
    have hg := hall r.toNat hmem
    simp only [Bool.and_eq_true] at hg
    exact eval_checked_gpr hm heval r hr (calleeGprExpr06 r.toNat) hg.1 hg.2
  refine ⟨by simpa [calleeGprExpr06, evalKExpr] using getG 19#5 (by decide) (by decide),
    by simpa [calleeGprExpr06, evalKExpr, hsp] using getG 20#5 (by decide) (by decide),
    by simpa [calleeGprExpr06, evalKExpr, h64] using getG 21#5 (by decide) (by decide),
    by simpa [calleeGprExpr06, evalKExpr, hsp] using getG 22#5 (by decide) (by decide),
    by simpa [calleeGprExpr06, evalKExpr, hsp] using getG 23#5 (by decide) (by decide),
    by simpa [calleeGprExpr06, evalKExpr] using getG 24#5 (by decide) (by decide),
    by simpa [calleeGprExpr06, evalKExpr, hsp] using getG 25#5 (by decide) (by decide),
    by simpa [calleeGprExpr06, evalKExpr, hsp] using getG 26#5 (by decide) (by decide),
    by simpa [calleeGprExpr06, evalKExpr, hrc, BitVec.add_zero] using getG 28#5 (by decide) (by decide),
    by simpa [calleeGprExpr06, evalKExpr, h99] using getG 29#5 (by decide) (by decide)⟩

/-! ## 3. Slice A Symbolic Execution (`+0x4194 → +0x4940`) & Full Row Init A (`+0x4170 → +0x4944`) -/

private theorem slotsFa8_01_all_spill :
    ∀ idx, idx < 25 →
      (match slotsFa8_01.getD idx (.vreg 0) with | .spillQ _ => true | .vreg _ => false) = true := by
  have hc : ((List.range 25).all fun idx =>
      match slotsFa8_01.getD idx (.vreg 0) with | .spillQ _ => true | .vreg _ => false) = true := by decide
  exact fun idx hidx => List.all_eq_true.mp hc idx (List.mem_range.mpr hidx)

private theorem slotsFa8_23_all_spill :
    ∀ idx, idx < 25 →
      (match slotsFa8_23.getD idx (.vreg 0) with | .spillQ _ => true | .vreg _ => false) = true := by
  have hc : ((List.range 25).all fun idx =>
      match slotsFa8_23.getD idx (.vreg 0) with | .spillQ _ => true | .vreg _ => false) = true := by decide
  exact fun idx hidx => List.all_eq_true.mp hc idx (List.mem_range.mpr hidx)

theorem seg5_sliceA_ok [MlKemPlacement] {b sp rcBase fpVal : BitVec 64}
    {rho : List (BitVec 8)} {row : Nat}
    (hrho : rho.length = 32) (hrow : row < 4) {s0 : State} {tA0 : BTree (BitVec 64) 9} {F : SepProp}
    (hpc0 : s0.pc = b + BitVec.ofNat 64 (4 * 4197)) (hrun0 : s0.status = .Running)
    (hsp0 : s0.sp = sp) (hspA0 : s0.spAligned = true)
    (hgprs0 : RowCalleeGprs06 sp rcBase fpVal row s0) (hhdr0 : MemAHeaderOk06 sp rho tA0) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + BitVec.ofNat 64 (4 * 4688)) s0
      ((rcBase ↦ᵣ mlkemData01Bytes) ∗ BTreeMem (sp + 144#64) 286 tA0 ∗ F)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .x0 = sp + 31752#64 ∧
        sf.readReg64 .x1 = 0#64 ∧ sf.readReg64 .x2 = 712#64 ∧
        RowCalleeGprs06 sp rcBase fpVal row sf ∧
        ∃ tA : BTree (BitVec 64) 9, MemAHeaderOk06 sp rho tA ∧
          (∀ idx, idx < 25 → slotHolds cfgA06 sf tA (slotsFa8_01.getD idx (.vreg 0))
            ((keccakAbsorb 21 0x1f#8 (rowSeed rho row 0)).getD idx 0#64)
            ((keccakAbsorb 21 0x1f#8 (rowSeed rho row 1)).getD idx 0#64)) ∧
          (∀ idx, idx < 25 → slotHolds cfgA06 sf tA (slotsFa8_23.getD idx (.vreg 0))
            ((keccakAbsorb 21 0x1f#8 (rowSeed rho row 2)).getD idx 0#64)
            ((keccakAbsorb 21 0x1f#8 (rowSeed rho row 3)).getD idx 0#64)) ∧
          (Pf ⊢ (rcBase ↦ᵣ mlkemData01Bytes) ∗ BTreeMem (sp + 144#64) 286 tA ∗ F)) := by
  let env0 := envInitA06 sp rcBase fpVal rho row s0 tA0
  obtain ⟨hm0, hmemEq0⟩ := stInitA06_matches hsp0 hspA0 hgprs0 hhdr0
  have henvSp : env0.sp = sp := rfl
  have henvRc : env0.rcBase = rcBase := rfl
  have hspEq : ((rcBase ↦ᵣ mlkemData01Bytes) ∗ BTreeMem (sp + 144#64) 286 tA0 ∗ F) =
      KSpatial cfgA06 env0 stInitA06 F := by
    simp only [KSpatial, cfgA06, henvSp, henvRc, btreeMem_zero, emp_sepConj]
    rw [hmemEq0]
  rw [hspEq]
  refine sepWP_of_runAndCheckKProg06 cfgA06_valid (env0 := env0) (show 0 < 24 by decide)
    cert_sliceA06 hm0 hpc0 hrun0 ?_
  intro sf envFinal stEnd hpcF hrunF hspF hrcF _hrlF heval hmF hchk
  simp only [chkSliceA06, Bool.and_eq_true] at hchk
  rcases hchk with ⟨⟨⟨⟨⟨⟨⟨⟨⟨hx0_eq, hx0_ok⟩, hx1_eq⟩, hx1_ok⟩, hx2_eq⟩, hx2_ok⟩,
    hhdr_chk⟩, hgpr_chk⟩, hout01⟩, hout23⟩
  have hp0 : ∀ col, col < 4 → evalExprList25 env0 (expPreAbsorb col) = preAbsorbState rho row col :=
    fun col hcol => evalExprList25_preAbsorb hrow hcol rfl rfl rfl rfl rfl
  let env1 := extendLoopVars env0 1000 (preAbsorbState rho row 0) (preAbsorbState rho row 1)
  have hp1 : ∀ col, col < 4 → evalExprList25 env1 (expPreAbsorb col) = preAbsorbState rho row col :=
    fun col hcol => evalExprList25_preAbsorb hrow hcol
      (by simp [env1, extendLoopVars]; rfl) (by simp [env1, extendLoopVars]; rfl)
      (by simp [env1, extendLoopVars]; rfl) (by simp [env1, extendLoopVars]; rfl)
      (by simp [env1, extendLoopVars]; rfl)
  have hspecEq : specEnvSteps env0 stepsA06 =
      extendLoopVars env1 2000 (preAbsorbState rho row 2) (preAbsorbState rho row 3) := by
    simp only [stepsA06, specEnvSteps, hp0 0 (by decide), hp0 1 (by decide)]
    change specEnvSteps env1 [.range 4429 49,
      .loop 4478 190 8#5 slotsL2 (expPreAbsorb 2) (expPreAbsorb 3) 2000, .range 4669 19] = _
    simp only [specEnvSteps, hp1 2 (by decide), hp1 3 (by decide)]
  have hspecSp : (specEnvSteps env0 stepsA06).sp = sp := by rw [hspecEq]; rfl
  have hspecRc : (specEnvSteps env0 stepsA06).rcBase = rcBase := by rw [hspecEq]; rfl
  have hspec64 : (specEnvSteps env0 stepsA06).vars 64 = BitVec.ofNat 64 row := by
    rw [hspecEq]; simp [extendLoopVars, env1, env0, envInitA06]
  have hspec99 : (specEnvSteps env0 stepsA06).vars 99 = fpVal := by
    rw [hspecEq]; simp [extendLoopVars, env1, env0, envInitA06]
  have hspec100 : (specEnvSteps env0 stepsA06).vars 100 = rhoW rho 0 := by
    rw [hspecEq]; simp [extendLoopVars, env1, env0, envInitA06]
  have hspec101 : (specEnvSteps env0 stepsA06).vars 101 = rhoW rho 1 := by
    rw [hspecEq]; simp [extendLoopVars, env1, env0, envInitA06]
  have hspec102 : (specEnvSteps env0 stepsA06).vars 102 = rhoW rho 2 := by
    rw [hspecEq]; simp [extendLoopVars, env1, env0, envInitA06]
  have hspec103 : (specEnvSteps env0 stepsA06).vars 103 = rhoW rho 3 := by
    rw [hspecEq]; simp [extendLoopVars, env1, env0, envInitA06]
  have hx0 := eval_checked_gpr hmF heval 0#5 (by decide) (.spAdd 31752#64) hx0_eq hx0_ok
  have hx1 := eval_checked_gpr hmF heval 1#5 (by decide) (.const64 0#64) hx1_eq hx1_ok
  have hx2 := eval_checked_gpr hmF heval 2#5 (by decide) (.const64 712#64) hx2_eq hx2_ok
  have hhdrF := checked_headerOk06 heval hspecSp hspec100 hspec101 hspec102 hspec103 hhdr_chk
  have hgprsF := checked_calleeGprs06 hmF heval hspecSp hspecRc hspec64 hspec99 hgpr_chk
  have hsl01 := checked_outSlots hmF heval (by decide) (by decide) hout01
  have hsl23 := checked_outSlots hmF heval (by decide) (by decide) hout23
  refine SepWP.done hpcF hrunF ⟨hmF.hsp.trans hspF, hmF.hsp_al,
    by simpa [Reg.x0, evalKExpr, hspecSp] using hx0, by simpa [Reg.x1, evalKExpr] using hx1,
    by simpa [Reg.x2, evalKExpr] using hx2, hgprsF, evalMemTree envFinal stEnd.memA, hhdrF, ?_, ?_, ?_⟩
  · intro idx hidx
    have hvLo : (specEnvSteps env0 stepsA06).vars (1000 + idx) =
        (keccakAbsorb 21 0x1f#8 (rowSeed rho row 0)).getD idx 0#64 := by
      rw [hspecEq, keccakAbsorb_rowSeed hrho row 0]
      simp [extendLoopVars, env1, show 1000 + idx < 2000 by omega,
        show ¬(1000 + idx < 1000) by omega, show 1000 + idx < 1000 + 25 by omega]
    have hvHi : (specEnvSteps env0 stepsA06).vars (1000 + 25 + idx) =
        (keccakAbsorb 21 0x1f#8 (rowSeed rho row 1)).getD idx 0#64 := by
      rw [hspecEq, keccakAbsorb_rowSeed hrho row 1]
      simp [extendLoopVars, env1, show 1000 + 25 + idx < 2000 by omega,
        show ¬(1000 + 25 + idx < 1000) by omega, show ¬(1000 + 25 + idx < 1000 + 25) by omega,
        show 1000 + 25 + idx < 1000 + 50 by omega]
    simpa [hvLo, hvHi] using hsl01 idx hidx
  · intro idx hidx
    have hvLo : (specEnvSteps env0 stepsA06).vars (2000 + idx) =
        (keccakAbsorb 21 0x1f#8 (rowSeed rho row 2)).getD idx 0#64 := by
      rw [hspecEq, keccakAbsorb_rowSeed hrho row 2]
      simp [extendLoopVars, show ¬(2000 + idx < 2000) by omega, show 2000 + idx < 2000 + 25 by omega]
    have hvHi : (specEnvSteps env0 stepsA06).vars (2000 + 25 + idx) =
        (keccakAbsorb 21 0x1f#8 (rowSeed rho row 3)).getD idx 0#64 := by
      rw [hspecEq, keccakAbsorb_rowSeed hrho row 3]
      simp [extendLoopVars, show ¬(2000 + 25 + idx < 2000) by omega,
        show ¬(2000 + 25 + idx < 2000 + 25) by omega, show 2000 + 25 + idx < 2000 + 50 by omega]
    simpa [hvLo, hvHi] using hsl23 idx hidx
  · simp only [KSpatial, cfgA06, hspF, hrcF, henvSp, henvRc, btreeMem_zero, emp_sepConj]; sep_frame

theorem seg5_initA_ok [MlKemPlacement] {b sp rcBase fpVal : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    {rho : List (BitVec 8)} {row : Nat} {Rest : SepProp} (hrho : rho.length = 32) (hrow : row < 4)
    {s : State} {P : SepProp} (hpc : s.pc = b + BitVec.ofNat 64 (4 * 4188)) (hrun : s.status = .Running)
    (hpre : RowInitAPre06 sp rcBase fpVal rho row Rest s P) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + BitVec.ofNat 64 (4 * 4689)) s P
      (RowInitAPost06 sp rcBase fpVal rho row Rest) := by
  subst hbase
  rcases hpre with ⟨hsp, hspA, hsp_chk, hcl, hro,
    ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx28, hfp⟩, hx1, tA0, hhdr0, hP⟩
  refine SepWP.weaken_pre hP ?_
  have hprep : SepWP (blkPC06.rebase blkPl06.base (fun _ => none))
      (blkPl06.base + BitVec.ofNat 64 (4 * 4196)) s
      ((rcBase ↦ᵣ mlkemData01Bytes) ∗ BTreeMem (sp + 144#64) 286 tA0 ∗
        memRegion (sp + 26320#64) 32 ∗ memRegion (sp + 4160#64) 2176 ∗
        memRegion (sp + 28368#64) 672 ∗ memRegion (sp + 30448#64) 2016 ∗ Rest)
      (fun s1 P1 =>
        s1.sp = sp ∧ s1.spAligned = true ∧
        s1.readReg64 .x0 = sp + 4160#64 ∧ (s1.readReg32 .x1).truncate 8 = 0#8 ∧
        s1.readReg64 .x2 = 2176#64 ∧ RowCalleeGprs06 sp rcBase fpVal row s1 ∧
        (P1 ⊢ memRegion (sp + 4160#64) 2176 ∗ ((rcBase ↦ᵣ mlkemData01Bytes) ∗
          BTreeMem (sp + 144#64) 286 tA0 ∗ MultiLaneSampled (sp + 26320#64) 4 (fun _ => 0) ∗
          memRegion (sp + 28368#64) 672 ∗ memRegion (sp + 30448#64) 2016 ∗ Rest))) := by
    refine SepWP.of_memRegion_btreeMem 4 (sp + 26320#64) (by decide) (by decide)
      (sepProp_ext (by sep_frame) (by sep_frame)) fun tS => ?_
    wp_steps 6
    refine step_strQ128 (wb := none) (ea := sp + 26336#64) (val := 0#128)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
      (by simp [evalAddrMode, hsp]) (by simp)
      (SepStore128.left (sepStore128_btreeMem (k := 2) (vHi := 0#64) (vLo := 0#64) (by decide) (by decide) (by bv_omega)))
      (by wp_norm_lhs) fun _ => ?_
    refine step_strQ128 (wb := none) (ea := sp + 26320#64) (val := 0#128)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
      (by simp [evalAddrMode, hsp]) (by simp)
      (SepStore128.left (sepStore128_btreeMem (k := 0) (vHi := 0#64) (vLo := 0#64) (by decide) (by decide) (by bv_omega)))
      (by wp_norm_lhs) fun _ => ?_
    have hzeroS : BTreeMem (sp + 26320#64) 4 ((((tS.set 2 0#64).set 3 0#64).set 0 0#64).set 1 0#64) =
        MultiLaneSampled (sp + 26320#64) 4 (fun _ => 0) :=
      btreeMem4_zero_eq_multiLaneSampled4 _ (by simp [BTree.get_set]) (by simp [BTree.get_set])
        (by simp [BTree.get_set]) (by simp [BTree.get_set])
    refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp [hsp], by simp [State.spAligned, hsp, hsp_chk],
        by simp, by simp [State.readReg32], by simp,
        ⟨by simp [hx19], by simp [hx20], by simp, by simp [hx22], by simp [hx23],
          by simp [hx24], by simp [hx25], by simp [hx26], by simp [hx28], by simp [hfp]⟩, ?_⟩
    rw [hzeroS]; sep_frame
  refine sepWP_seq_env hcl hro hprep fun s1 P1 hpc1 hrun1 hcl1 hro1 ⟨_, _, hx0_1, hx1_1, hx2_1, hgprs1, hP1⟩ => ?_
  have hcall1 : SepWP (blkPC06.rebase blkPl06.base (fun _ => none))
      (blkPl06.base + BitVec.ofNat 64 (4 * 4197)) s1 P1
      (fun s2 P2 => s2.sp = sp ∧ s2.spAligned = true ∧ RowCalleeGprs06 sp rcBase fpVal row s2 ∧
        (P2 ⊢ (rcBase ↦ᵣ mlkemData01Bytes) ∗ BTreeMem (sp + 144#64) 286 tA0 ∗
          (MultiLaneSampled (sp + 26320#64) 4 (fun _ => 0) ∗
            MultiLaneSlots (sp + 4160#64) 544 4 (fun _ => List.replicate 272 0#16) ∗
            memRegion (sp + 28368#64) 672 ∗ memRegion (sp + 30448#64) 2016 ∗ Rest))) := by
    refine SepWP.weaken_pre hP1 ?_; rcases hgprs1 with ⟨g19, g20, g21, g22, g23, g24, g25, g26, g28, gfp⟩
    wp_call (blk29_memset_06 blkPl06.base) (sp + 4160#64, 0#8, 2176)
    have hsp2 : sf.sp = sp := by simp [*]
    refine SepWP.done (by wp_norm_lhs) (by assumption) ⟨hsp2, by simp [State.spAligned, hsp2, hsp_chk],
      ⟨by simp [*], by simp [*], by simp [*], by simp [*], by simp [*],
        by simp [*], by simp [*], by simp [*], by simp [*], by simp [*]⟩, ?_⟩
    rw [memset2176_eq_multiLaneSlots4]; sep_frame
  refine sepWP_seq_env hcl1 hro1 hcall1 fun s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hgprs2, hP2⟩ => ?_
  refine sepWP_seq_env hcl2 hro2
    (SepWP.weaken_pre hP2 (seg5_sliceA_ok hrho hrow hpc2 hrun2 hsp2 hspA2 hgprs2 hhdr0)) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 hro3 ⟨_, _, hx0_3, hx1_3, hx2_3, hgprs3, tA, hhdr, hsl01, hsl23, hP3⟩
  have hcall2 : SepWP (blkPC06.rebase blkPl06.base (fun _ => none))
      (blkPl06.base + BitVec.ofNat 64 (4 * 4689)) s3 P3
      (fun s4 P4 => s4.sp = sp ∧ s4.spAligned = true ∧ RowCalleeGprs06 sp rcBase fpVal row s4 ∧
        (P4 ⊢ (rcBase ↦ᵣ mlkemData01Bytes) ∗ BTreeMem (sp + 144#64) 286 tA ∗
          MultiLaneSampled (sp + 26320#64) 4 (fun _ => 0) ∗
          MultiLaneSlots (sp + 4160#64) 544 4 (fun _ => List.replicate 272 0#16) ∗
          memRegion (sp + 28368#64) 672 ∗ memRegion (sp + 30448#64) 2016 ∗ Rest)) := by
    have hsp30448 : memRegion (sp + 30448#64) 2016 =
        memRegion (sp + 30448#64) 1304 ∗ memRegion (sp + 31752#64) 712 :=
      memRegion_split' (b := sp + 30448#64) (b' := sp + 31752#64) (n := 1304) (k := (712 : Nat))
        rfl (by bv_omega) (by decide)
    refine SepWP.weaken_pre hP3 (SepWP.weaken_pre (by rw [hsp30448]; sep_frame : _ ⊢
      memRegion (sp + 31752#64) 712 ∗ ((rcBase ↦ᵣ mlkemData01Bytes) ∗ BTreeMem (sp + 144#64) 286 tA ∗
        MultiLaneSampled (sp + 26320#64) 4 (fun _ => 0) ∗
        MultiLaneSlots (sp + 4160#64) 544 4 (fun _ => List.replicate 272 0#16) ∗
        memRegion (sp + 28368#64) 672 ∗ memRegion (sp + 30448#64) 1304 ∗ Rest)) ?_)
    rcases hgprs3 with ⟨g19, g20, g21, g22, g23, g24, g25, g26, g28, gfp⟩
    have hx1_8 : (s3.readReg32 .x1).truncate 8 = 0#8 := by
      simp [State.readReg32, State.readReg64] at hx1_3 ⊢; rw [hx1_3]; rfl
    wp_call (blk29_memset_06 blkPl06.base) (sp + 31752#64, 0#8, 712)
    have hsp4 : sf.sp = sp := by simp [*]
    refine SepWP.done (by wp_norm_lhs) (by assumption) ⟨hsp4, by simp [State.spAligned, hsp4, hsp_chk],
      ⟨by simp [*], by simp [*], by simp [*], by simp [*], by simp [*],
        by simp [*], by simp [*], by simp [*], by simp [*], by simp [*]⟩, ?_⟩
    have h712 : ((sp + 31752#64) ↦ₛ List.replicate 712 0#8) ⊢ memRegion (sp + 31752#64) 712 := by
      have hp := pointsToBytes_entails_memRegion (sp + 31752#64) (List.replicate 712 0#8)
      rwa [List.length_replicate] at hp
    rw [hsp30448]; exact entails_sub h712 (by sep_frame) (by sep_frame)
  refine sepWP_seq_env hcl3 hro3 hcall2 fun sf Pf hpcF hrunF hclF hroF ⟨hspF, hspAF, hgprsF, hPf⟩ => ?_
  exact SepWP.done hpcF hrunF ⟨hspF, hspAF, hsp_chk, hclF, hroF, hgprsF, tA, hhdr,
    fun idx hidx => slotHolds_spill_transfer rfl (slotsFa8_01_all_spill idx hidx) (hsl01 idx hidx),
    fun idx hidx => slotHolds_spill_transfer rfl (slotsFa8_23_all_spill idx hidx) (hsl23 idx hidx), hPf⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5InitA
