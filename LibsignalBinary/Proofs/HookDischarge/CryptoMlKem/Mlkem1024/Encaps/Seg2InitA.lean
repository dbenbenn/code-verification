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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymBridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakLoop -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Defs
public meta import ProofLib.GenPlacedFetches
meta import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Round
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1bPure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakAnf
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymEval
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSym
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakProg
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakFast

/-!
# `kyber_encapsulate` (`B07`) — Segment 2 Row Init Slice A (`+0x07d8 .. +0x0fa8`, `Seg2InitA`)

Proves the symbolic certificate `cert_sliceA`, environment-matching and pre-absorb extractors,
and row-initialization slice A (`seg2_initA_ok`, `+0x07d8 → +0x0fa8`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2InitA

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemData01Bytes mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemBlockPlacement_ρ mlkemMpl resolve_blk29 seq_codeLoaded_lr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak (keccakAbsorb keccakF1600)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem (MultiLaneSampled MultiLaneSlots)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (entails_sub)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (SepStore128.left step_strQ128)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base (
  blk07_code_eq blk07_tree_size blkLib07 blkPC07 blkPl07 blkPlaceable07 blkTree07)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1bPure (exec_simdMovi_2d_0 rhoW)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymDefs (
  BTree KCfg KEnv KExpr KSlot KState evalKExpr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymBridge (
  BTreeMem KSpatial KStateMatches SepWP.of_memRegion_btreeMem evalMemTree sepStore128_btreeMem)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakLoop (
  btree_ext_get readSlot slotHolds slotValid vreg128_repack)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Base (
  KProgStep evalExprList25 eval_checked_gpr eval_checked_memA eval_checked_slot exprVarsOk
  extendLoopVars keccakAbsorb_rowSeed preAbsorbLane preAbsorbState progBases rowSeed
  runAndCheckKProg sepWP_of_runAndCheckKProg specEnvSteps validSpecVar)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Defs (
  MemAHeaderOk RowCalleeGprs blk29_memset_07 btreeMem4_zero_eq_multiLaneSampled4 cfgA cfgA_valid cfgB
  memset2176_eq_multiLaneSlots4 slotsFa8_01 slotsFa8_23 slotsL1 slotsL2)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakFast (
  runAndCheckKProgFast runAndCheckKProg_of_fast)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC07 blkLib07 blkTree07 blk07_code_eq blk07_tree_size
  via_placement blkPl07 blkPlaceable07 [0x07d8 → 0x07f8, 0x0fa4 → 0x0fa8]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl07_ρ [MlKemPlacement] (sym : String) :
    blkPl07.ρ sym = mlkemMultiLib.resolve mlkemMpl sym :=
  mlkemBlockPlacement_ρ 7 sym

/-! ## 1. Row Init Slice A Pre/Post Predicates & Symbolic Certificate -/

@[expose] def RowEntryGprs (sp rcBase : BitVec 64) (s : State) : Prop :=
  s.readReg64 .x19 = sp + 2560#64 ∧ s.readReg64 .x21 = rcBase ∧
  s.readReg64 .x22 = sp + 26768#64 ∧ s.readReg64 .x23 = sp + 26779#64 ∧
  s.readReg64 .x24 = sp + 27032#64 ∧ s.readReg64 .x25 = 256#64 ∧
  s.readReg64 .x26 = sp + 24720#64 ∧ s.readReg64 .x27 = 544#64 ∧
  s.readReg64 .fp = sp + 33008#64

@[expose] def RowInitAPre [MlKemPlacement] (sp rcBase : BitVec 64)
    (rho : List (BitVec 8)) (row : Nat) (Rest : SepProp) (s : State) (P : SepProp) : Prop :=
  s.sp = sp ∧ s.spAligned = true ∧ (sp &&& 15#64 == 0#64) = true ∧
  mlkemMultiLib.CodeLoaded mlkemMpl s.mem ∧ MlKemRoOk mlkemMpl s.mem ∧
  RowEntryGprs sp rcBase s ∧ s.readReg64 .x1 = BitVec.ofNat 64 row ∧
  ∃ tA : BTree (BitVec 64) 9, MemAHeaderOk sp rho tA ∧
    (P ⊢ (rcBase ↦ᵣ mlkemData01Bytes) ∗ BTreeMem (sp + 144#64) 286 tA ∗
      memRegion (sp + 24720#64) 32 ∗ memRegion (sp + 2560#64) 2176 ∗
      memRegion (sp + 26768#64) 672 ∗ memRegion (sp + 28848#64) 2016 ∗ Rest)

@[expose] def RowInitAPost [MlKemPlacement] (sp rcBase : BitVec 64)
    (rho : List (BitVec 8)) (row : Nat) (Rest : SepProp) (sf : State) (Pf : SepProp) : Prop :=
  sf.sp = sp ∧ sf.spAligned = true ∧ (sp &&& 15#64 == 0#64) = true ∧
  mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
  RowCalleeGprs sp rcBase row sf ∧
  ∃ tA : BTree (BitVec 64) 9, MemAHeaderOk sp rho tA ∧
    (∀ idx, idx < 25 → slotHolds cfgB sf tA (slotsFa8_01.getD idx (.vreg 0))
      ((keccakAbsorb 21 0x1f#8 (rowSeed rho row 0)).getD idx 0#64)
      ((keccakAbsorb 21 0x1f#8 (rowSeed rho row 1)).getD idx 0#64)) ∧
    (∀ idx, idx < 25 → slotHolds cfgB sf tA (slotsFa8_23.getD idx (.vreg 0))
      ((keccakAbsorb 21 0x1f#8 (rowSeed rho row 2)).getD idx 0#64)
      ((keccakAbsorb 21 0x1f#8 (rowSeed rho row 3)).getD idx 0#64)) ∧
    (Pf ⊢ (rcBase ↦ᵣ mlkemData01Bytes) ∗ BTreeMem (sp + 144#64) 286 tA ∗
      MultiLaneSampled (sp + 24720#64) 4 (fun _ => 0) ∗
      MultiLaneSlots (sp + 2560#64) 544 4 (fun _ => List.replicate 272 0#16) ∗
      memRegion (sp + 26768#64) 672 ∗ memRegion (sp + 28848#64) 2016 ∗ Rest)

theorem slotHolds_spill_transfer {cfg1 cfg2 : KCfg} (hoff : cfg1.offA = cfg2.offA)
    {s1 s2 : State} {tA : BTree (BitVec 64) 9} {sl : KSlot} {vLo vHi : BitVec 64}
    (hsp : (match sl with | .spillQ _ => true | .vreg _ => false) = true)
    (h : slotHolds cfg1 s1 tA sl vLo vHi) :
    slotHolds cfg2 s2 tA sl vLo vHi := by
  cases sl with
  | vreg _ => simp at hsp
  | spillQ off => simpa [slotHolds, hoff] using h

@[expose] def headerMemAExpr (i : Nat) : KExpr :=
  if i == 0 then .const64 0x00000000001f0300#64 else if i == 1 then .const64 0#64
  else if i == 2 then .const64 0x00000000001f0200#64 else if i == 3 then .const64 0#64
  else if i == 4 then .const64 0x00000000001f0100#64 else if i == 5 then .const64 0#64
  else if i == 7 then .spAdd 26779#64 else if i == 8 then .spAdd 28859#64
  else if i == 9 then .spAdd 29112#64 else if i == 14 then .const64 0xffffffffff0000ff#64
  else if i == 15 then .const64 0xffffffffffffffff#64 else if i == 16 || i == 17 then .var 103
  else if i == 18 || i == 19 then .var 102 else if i == 20 || i == 21 then .var 101
  else if i == 22 || i == 23 then .var 100 else .var (200 + i)

@[expose] def calleeGprExpr (g : Nat) : KExpr :=
  if g == 19 then .spAdd 2560#64 else if g == 20 then .var 64 else if g == 21 then .rcAdd 0#64
  else if g == 22 then .spAdd 26768#64 else if g == 23 then .spAdd 26779#64
  else if g == 24 then .spAdd 27032#64 else if g == 25 then .const64 256#64
  else if g == 26 then .spAdd 24720#64 else if g == 27 then .const64 544#64
  else if g == 29 then .spAdd 33008#64 else .var (65 + g)

@[expose] def stInitA : KState :=
  { vregs := BTree.ofFn 5 (fun vr => (.var (2 * vr), .var (2 * vr + 1)))
    gprs  := BTree.ofFn 5 calleeGprExpr
    memA  := BTree.ofFn 9 headerMemAExpr
    memB  := BTree.ofFn 9 (fun _ => .const64 0#64)
    zFlag := none }

@[expose] def expPreAbsorbItem (col idx : Nat) : KExpr :=
  if idx < 4 then .var (100 + idx)
  else if idx == 4 then
    let rByte : KExpr := KExpr.insByte0 (.const64 0#64) (.var 64)
    if col == 0 then
      KExpr.bsl (.const64 0xffffffffff0000ff#64) rByte (.const64 0x001f001f001f001f#64)
    else if col == 1 then
      KExpr.bsl (.const64 0xffffffffff0000ff#64) rByte (.const64 0x00000000001f0100#64)
    else if col == 2 then
      KExpr.bitOp (.const64 0x00000000001f0200#64) rByte (.const64 0xffffffffff0000ff#64)
    else
      KExpr.bsl (.const64 0xffffffffff0000ff#64) rByte (.const64 0x00000000001f0300#64)
  else if idx == 5 then
    if col == 2 then KExpr.bitOp (.const64 0#64) (.const64 0#64) (.const64 0xffffffffffffffff#64)
    else if col == 3 then KExpr.bsl (.const64 0xffffffffffffffff#64) (.const64 0#64) (.const64 0#64)
    else .const64 0#64
  else if idx == 20 then KExpr.xor (.const64 0#64) (.const64 0x8000000000000000#64)
  else .const64 0#64

@[expose] def expPreAbsorb (col : Nat) : List KExpr :=
  (List.range 25).map (expPreAbsorbItem col)

@[expose] def stepsA : List KProgStep :=
  [.range 510 34,
   .loop 544 197 8#5 slotsL1 (expPreAbsorb 0) (expPreAbsorb 1) 1000,
   .range 742 49,
   .loop 791 190 8#5 slotsL2 (expPreAbsorb 2) (expPreAbsorb 3) 2000,
   .range 982 19]

@[expose] def headerIdxs : List Nat :=
  [0, 1, 2, 3, 4, 5, 7, 8, 9, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

@[expose] def calleeGprIdxs : List Nat :=
  [19, 20, 21, 22, 23, 24, 25, 26, 27, 29]

@[expose] def checkHeaderPreserved (ok : Nat → Bool) (st : KState) : Bool :=
  headerIdxs.all fun i =>
    (st.memA.get i).beq (headerMemAExpr i) && exprVarsOk ok (headerMemAExpr i)

@[expose] def checkCalleeGprsPreserved (ok : Nat → Bool) (st : KState) : Bool :=
  calleeGprIdxs.all fun g =>
    (st.gprs.get g).beq (calleeGprExpr g) && exprVarsOk ok (calleeGprExpr g)

@[expose] def checkOutSlots (cfg : KCfg) (ok : Nat → Bool) (st : KState)
    (slots : List KSlot) (baseOut : Nat) : Bool :=
  (List.range 25).all fun idx =>
    let p := readSlot cfg st (slots.getD idx (.vreg 0))
    p.1.beq (.var (baseOut + idx)) && p.2.beq (.var (baseOut + 25 + idx)) &&
      exprVarsOk ok (.var (baseOut + idx)) && exprVarsOk ok (.var (baseOut + 25 + idx))

@[expose] def chkSliceA (ok : Nat → Bool) (st : KState) : Bool :=
  (st.gprs.get 0).beq (.spAdd 30152#64) && exprVarsOk ok (.spAdd 30152#64) &&
  (st.gprs.get 1).beq (.const64 0#64) && exprVarsOk ok (.const64 0#64) &&
  (st.gprs.get 2).beq (.const64 712#64) && exprVarsOk ok (.const64 712#64) &&
  checkHeaderPreserved ok st && checkCalleeGprsPreserved ok st &&
  checkOutSlots cfgA ok st slotsFa8_01 1000 && checkOutSlots cfgA ok st slotsFa8_23 2000

theorem cert_sliceA :
    runAndCheckKProg cfgA 510 1001 510 1001 800 stepsA stInitA chkSliceA = true :=
  runAndCheckKProg_of_fast (by decide +kernel)

theorem btreeMem_zero (ptr : BitVec 64) (t : BTree (BitVec 64) 9) : BTreeMem ptr 0 t = emp := rfl

attribute [local irreducible] blkPC07 keccakF1600 keccakAbsorb BTreeMem
attribute [local wp_norm ↓ high] exec_simdMovi_2d_0
/-! ## 2. Environment Matching, Pre-Absorb Evaluation, & Checked Extractors -/

@[expose] def envInitA (sp rcBase : BitVec 64) (rho : List (BitVec 8)) (row : Nat)
    (s : State) (tA : BTree (BitVec 64) 9) : KEnv :=
  { sp := sp, rcBase := rcBase, rLoop := 0
    vars := fun id =>
      if id < 64 then
        let v := s.readVReg128 (BitVec.ofNat 5 (id / 2))
        if id % 2 == 0 then v.truncate 64 else (v >>> 64).truncate 64
      else if id == 64 then BitVec.ofNat 64 row
      else if id < 97 then s.readReg64 (.gpr (BitVec.ofNat 5 (id - 65)))
      else if id == 100 then rhoW rho 0 else if id == 101 then rhoW rho 1
      else if id == 102 then rhoW rho 2 else if id == 103 then rhoW rho 3
      else if id < 712 then tA.get (id - 200) else 0#64 }

theorem eval_headerMemAExpr {sp rcBase : BitVec 64} {rho : List (BitVec 8)} {row : Nat}
    {s : State} {tA : BTree (BitVec 64) 9} (hhdr : MemAHeaderOk sp rho tA) :
    ∀ i, i < 2 ^ 9 → evalKExpr (envInitA sp rcBase rho row s tA) (headerMemAExpr i) = tA.get i := by
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
      simp [headerMemAExpr, evalKExpr, envInitA,
        h0, h1, h2, h3, h4, h5, h7, h8, h9, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23]
  · have hne : headerMemAExpr i = .var (200 + i) := by
      unfold headerMemAExpr
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
    simp [evalKExpr, envInitA, show ¬(200 + i < 64) by omega, show 200 + i ≠ 64 by omega,
      show ¬(200 + i < 97) by omega, show 200 + i ≠ 100 by omega, show 200 + i ≠ 101 by omega,
      show 200 + i ≠ 102 by omega, show 200 + i ≠ 103 by omega, show 200 + i < 712 by omega]

theorem stInitA_matches {sp rcBase : BitVec 64} {rho : List (BitVec 8)} {row : Nat}
    {s : State} {tA : BTree (BitVec 64) 9}
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hgprs : RowCalleeGprs sp rcBase row s) (hhdr : MemAHeaderOk sp rho tA) :
    KStateMatches (envInitA sp rcBase rho row s tA) stInitA s ∧
      BTreeMem (sp + 144#64) 286 (evalMemTree (envInitA sp rcBase rho row s tA) stInitA.memA) =
        BTreeMem (sp + 144#64) 286 tA := by
  rcases hgprs with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hfp⟩
  refine ⟨⟨hsp, hspA, ?_, ?_, trivial⟩, ?_⟩
  · intro vr
    have hlt := vr.isLt
    simp only [stInitA]
    rw [BTree.get_ofFn 5 _ vr.toNat hlt]
    have h0lt : 2 * vr.toNat < 64 := by omega
    have h1lt : 2 * vr.toNat + 1 < 64 := by omega
    have hd0 : 2 * vr.toNat / 2 = vr.toNat := by omega
    have hm0 : (2 * vr.toNat % 2 == 0) = true := beq_iff_eq.mpr (by omega)
    have hd1 : (2 * vr.toNat + 1) / 2 = vr.toNat := by omega
    have hm1 : ((2 * vr.toNat + 1) % 2 == 0) = false := beq_false_of_ne (by omega)
    simp only [evalKExpr, envInitA, h0lt, h1lt, ↓reduceIte, hd0, hm0, hd1, hm1,
      Bool.false_eq_true, BitVec.ofNat_toNat]
    exact (vreg128_repack (s.readVReg128 vr)).symm
  · intro g _hg31
    have hlt := g.isLt
    simp only [stInitA]
    rw [BTree.get_ofFn 5 _ g.toNat hlt]
    by_cases h19 : g = 19#5
    · subst h19; simpa [Reg.x19, calleeGprExpr, evalKExpr, envInitA] using hx19
    by_cases h20 : g = 20#5
    · subst h20; simpa [Reg.x20, calleeGprExpr, evalKExpr, envInitA] using hx20
    by_cases h21 : g = 21#5
    · subst h21; simpa [Reg.x21, calleeGprExpr, evalKExpr, envInitA] using hx21
    by_cases h22 : g = 22#5
    · subst h22; simpa [Reg.x22, calleeGprExpr, evalKExpr, envInitA] using hx22
    by_cases h23 : g = 23#5
    · subst h23; simpa [Reg.x23, calleeGprExpr, evalKExpr, envInitA] using hx23
    by_cases h24 : g = 24#5
    · subst h24; simpa [Reg.x24, calleeGprExpr, evalKExpr, envInitA] using hx24
    by_cases h25 : g = 25#5
    · subst h25; simpa [Reg.x25, calleeGprExpr, evalKExpr, envInitA] using hx25
    by_cases h26 : g = 26#5
    · subst h26; simpa [Reg.x26, calleeGprExpr, evalKExpr, envInitA] using hx26
    by_cases h27 : g = 27#5
    · subst h27; simpa [Reg.x27, calleeGprExpr, evalKExpr, envInitA] using hx27
    by_cases h29 : g = 29#5
    · subst h29; simpa [Reg.fp, calleeGprExpr, evalKExpr, envInitA] using hfp
    have hc : calleeGprExpr g.toNat = .var (65 + g.toNat) := by
      simp [calleeGprExpr,
        show g.toNat ≠ 19 from fun e => h19 (BitVec.eq_of_toNat_eq e),
        show g.toNat ≠ 20 from fun e => h20 (BitVec.eq_of_toNat_eq e),
        show g.toNat ≠ 21 from fun e => h21 (BitVec.eq_of_toNat_eq e),
        show g.toNat ≠ 22 from fun e => h22 (BitVec.eq_of_toNat_eq e),
        show g.toNat ≠ 23 from fun e => h23 (BitVec.eq_of_toNat_eq e),
        show g.toNat ≠ 24 from fun e => h24 (BitVec.eq_of_toNat_eq e),
        show g.toNat ≠ 25 from fun e => h25 (BitVec.eq_of_toNat_eq e),
        show g.toNat ≠ 26 from fun e => h26 (BitVec.eq_of_toNat_eq e),
        show g.toNat ≠ 27 from fun e => h27 (BitVec.eq_of_toNat_eq e),
        show g.toNat ≠ 29 from fun e => h29 (BitVec.eq_of_toNat_eq e)]
    rw [hc]
    simp [evalKExpr, envInitA, show ¬(65 + g.toNat < 64) by omega,
      show 65 + g.toNat ≠ 64 by omega, show 65 + g.toNat < 97 by omega, BitVec.ofNat_toNat]
  · congr 1; apply btree_ext_get; intro i hi
    simp only [evalMemTree, stInitA]; rw [BTree.get_map, BTree.get_ofFn 9 _ i hi]
    exact eval_headerMemAExpr hhdr i hi
@[expose] def envRowOnly (row : Nat) : KEnv :=
  { sp := 0#64, rcBase := 0#64, rLoop := 0
    vars := fun id => if id == 64 then BitVec.ofNat 64 row else 0#64 }

private theorem evalPreAbsorbGe4_chk :
    ((List.range 4).all fun r => (List.range 4).all fun c => (List.range 25).all fun i =>
      decide (i < 4) || (evalKExpr (envRowOnly r) (expPreAbsorbItem c i) == preAbsorbLane [] r c i)) = true := by
  decide

private theorem evalKExpr_rowOnly {env : KEnv} {row : Nat} (h64 : env.vars 64 = BitVec.ofNat 64 row) :
    ∀ (col idx : Nat), 4 ≤ idx → idx < 25 →
      evalKExpr env (expPreAbsorbItem col idx) = evalKExpr (envRowOnly row) (expPreAbsorbItem col idx) := by
  intro col idx hge _hlt
  have hlt4 : ¬(idx < 4) := by omega
  by_cases h4 : idx = 4
  · subst h4
    by_cases hc0 : col = 0
    · subst hc0; simp [expPreAbsorbItem, evalKExpr, envRowOnly, h64]
    · by_cases hc1 : col = 1
      · subst hc1; simp [expPreAbsorbItem, evalKExpr, envRowOnly, h64]
      · by_cases hc2 : col = 2
        · subst hc2; simp [expPreAbsorbItem, evalKExpr, envRowOnly, h64]
        · simp [expPreAbsorbItem, hc0, hc1, hc2, evalKExpr, envRowOnly, h64]
  · by_cases h5 : idx = 5
    · subst h5
      by_cases hc2 : col = 2
      · subst hc2; simp [expPreAbsorbItem, evalKExpr, envRowOnly]
      · by_cases hc3 : col = 3
        · subst hc3; simp [expPreAbsorbItem, evalKExpr, envRowOnly]
        · simp [expPreAbsorbItem, hc2, hc3, evalKExpr, envRowOnly]
    · by_cases h20 : idx = 20
      · subst h20; simp [expPreAbsorbItem, evalKExpr, envRowOnly]
      · simp [expPreAbsorbItem, hlt4, h4, h5, h20, evalKExpr, envRowOnly]

theorem evalExprList25_preAbsorb {env : KEnv} {rho : List (BitVec 8)} {row col : Nat}
    (hrow : row < 4) (hcol : col < 4)
    (h64 : env.vars 64 = BitVec.ofNat 64 row)
    (h100 : env.vars 100 = rhoW rho 0) (h101 : env.vars 101 = rhoW rho 1)
    (h102 : env.vars 102 = rhoW rho 2) (h103 : env.vars 103 = rhoW rho 3) :
    evalExprList25 env (expPreAbsorb col) = preAbsorbState rho row col := by
  apply Array.ext
  · simp [evalExprList25, preAbsorbState]
  · intro idx h1 _
    have hidx : idx < 25 := by simpa [evalExprList25] using h1
    have hget : (expPreAbsorb col).getD idx (.const64 0#64) = expPreAbsorbItem col idx := by
      simp [expPreAbsorb, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hidx]
    simp only [evalExprList25, preAbsorbState, Array.getElem_ofFn, hget]
    by_cases hlt4 : idx < 4
    · rcases (by omega : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3) with rfl | rfl | rfl | rfl
      · simp [expPreAbsorbItem, evalKExpr, preAbsorbLane, h100]
      · simp [expPreAbsorbItem, evalKExpr, preAbsorbLane, h101]
      · simp [expPreAbsorbItem, evalKExpr, preAbsorbLane, h102]
      · simp [expPreAbsorbItem, evalKExpr, preAbsorbLane, h103]
    · have hr := List.all_eq_true.mp evalPreAbsorbGe4_chk row (List.mem_range.mpr hrow)
      have hc := List.all_eq_true.mp hr col (List.mem_range.mpr hcol)
      have hi := List.all_eq_true.mp hc idx (List.mem_range.mpr hidx)
      simp only [decide_eq_false hlt4, Bool.false_or] at hi
      rw [evalKExpr_rowOnly h64 col idx (by omega) hidx, beq_iff_eq.mp hi]
      simp [preAbsorbLane, hlt4]

theorem checked_headerOk {ok : Nat → Bool} {envFinal envSpec : KEnv} {stEnd : KState}
    {sp : BitVec 64} {rho : List (BitVec 8)}
    (heval : ∀ e, exprVarsOk ok e = true → evalKExpr envFinal e = evalKExpr envSpec e)
    (hsp : envSpec.sp = sp)
    (h100 : envSpec.vars 100 = rhoW rho 0) (h101 : envSpec.vars 101 = rhoW rho 1)
    (h102 : envSpec.vars 102 = rhoW rho 2) (h103 : envSpec.vars 103 = rhoW rho 3)
    (hchk : checkHeaderPreserved ok stEnd = true) :
    MemAHeaderOk sp rho (evalMemTree envFinal stEnd.memA) := by
  have hall := List.all_eq_true.mp hchk
  have getH (i : Nat) (hmem : i ∈ headerIdxs) :
      (evalMemTree envFinal stEnd.memA).get i = evalKExpr envSpec (headerMemAExpr i) := by
    have hi := hall i hmem
    simp only [Bool.and_eq_true] at hi
    exact eval_checked_memA heval i (headerMemAExpr i) hi.1 hi.2
  refine ⟨by simpa [headerMemAExpr, evalKExpr] using getH 0 (by decide), by simpa [headerMemAExpr, evalKExpr] using getH 1 (by decide),
    by simpa [headerMemAExpr, evalKExpr] using getH 2 (by decide), by simpa [headerMemAExpr, evalKExpr] using getH 3 (by decide),
    by simpa [headerMemAExpr, evalKExpr] using getH 4 (by decide), by simpa [headerMemAExpr, evalKExpr] using getH 5 (by decide),
    by simpa [headerMemAExpr, evalKExpr, hsp] using getH 7 (by decide), by simpa [headerMemAExpr, evalKExpr, hsp] using getH 8 (by decide),
    by simpa [headerMemAExpr, evalKExpr, hsp] using getH 9 (by decide), by simpa [headerMemAExpr, evalKExpr] using getH 14 (by decide),
    by simpa [headerMemAExpr, evalKExpr] using getH 15 (by decide), by simpa [headerMemAExpr, evalKExpr, h103] using getH 16 (by decide),
    by simpa [headerMemAExpr, evalKExpr, h103] using getH 17 (by decide), by simpa [headerMemAExpr, evalKExpr, h102] using getH 18 (by decide),
    by simpa [headerMemAExpr, evalKExpr, h102] using getH 19 (by decide), by simpa [headerMemAExpr, evalKExpr, h101] using getH 20 (by decide),
    by simpa [headerMemAExpr, evalKExpr, h101] using getH 21 (by decide), by simpa [headerMemAExpr, evalKExpr, h100] using getH 22 (by decide),
    by simpa [headerMemAExpr, evalKExpr, h100] using getH 23 (by decide)⟩

theorem checked_calleeGprs {ok : Nat → Bool} {envFinal envSpec : KEnv} {stEnd : KState}
    {sf : State} {sp rcBase : BitVec 64} {row : Nat}
    (hm : KStateMatches envFinal stEnd sf)
    (heval : ∀ e, exprVarsOk ok e = true → evalKExpr envFinal e = evalKExpr envSpec e)
    (hsp : envSpec.sp = sp) (hrc : envSpec.rcBase = rcBase)
    (h64 : envSpec.vars 64 = BitVec.ofNat 64 row)
    (hchk : checkCalleeGprsPreserved ok stEnd = true) :
    RowCalleeGprs sp rcBase row sf := by
  have hall := List.all_eq_true.mp hchk
  have getG (r : BitVec 5) (hr : r ≠ 31#5) (hmem : r.toNat ∈ calleeGprIdxs) :
      sf.readReg64 (.gpr r) = evalKExpr envSpec (calleeGprExpr r.toNat) := by
    have hg := hall r.toNat hmem
    simp only [Bool.and_eq_true] at hg
    exact eval_checked_gpr hm heval r hr (calleeGprExpr r.toNat) hg.1 hg.2
  refine ⟨by simpa [calleeGprExpr, evalKExpr, hsp] using getG 19#5 (by decide) (by decide),
    by simpa [calleeGprExpr, evalKExpr, h64] using getG 20#5 (by decide) (by decide),
    by simpa [calleeGprExpr, evalKExpr, hrc, BitVec.add_zero] using getG 21#5 (by decide) (by decide),
    by simpa [calleeGprExpr, evalKExpr, hsp] using getG 22#5 (by decide) (by decide),
    by simpa [calleeGprExpr, evalKExpr, hsp] using getG 23#5 (by decide) (by decide),
    by simpa [calleeGprExpr, evalKExpr, hsp] using getG 24#5 (by decide) (by decide),
    by simpa [calleeGprExpr, evalKExpr] using getG 25#5 (by decide) (by decide),
    by simpa [calleeGprExpr, evalKExpr, hsp] using getG 26#5 (by decide) (by decide),
    by simpa [calleeGprExpr, evalKExpr] using getG 27#5 (by decide) (by decide),
    by simpa [calleeGprExpr, evalKExpr, hsp] using getG 29#5 (by decide) (by decide)⟩

theorem checked_outSlots {cfg : KCfg} {ok : Nat → Bool} {envFinal envSpec : KEnv}
    {stEnd : KState} {sf : State} {slots : List KSlot} {baseOut : Nat}
    (hm : KStateMatches envFinal stEnd sf)
    (heval : ∀ e, exprVarsOk ok e = true → evalKExpr envFinal e = evalKExpr envSpec e)
    (hvalid : slots.all (slotValid cfg) = true)
    (hlen : slots.length = 25)
    (hchk : checkOutSlots cfg ok stEnd slots baseOut = true) :
    ∀ idx, idx < 25 →
      slotHolds cfg sf (evalMemTree envFinal stEnd.memA) (slots.getD idx (.vreg 0))
        (envSpec.vars (baseOut + idx)) (envSpec.vars (baseOut + 25 + idx)) := by
  intro idx hidx
  have hall := List.all_eq_true.mp hchk idx (List.mem_range.mpr hidx)
  simp only [Bool.and_eq_true] at hall
  rcases hall with ⟨⟨⟨heqLo, heqHi⟩, hokLo⟩, hokHi⟩
  have hmem : slots.getD idx (.vreg 0) ∈ slots := by
    have hlt : idx < slots.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    exact List.getElem_mem hlt
  have hsl : slotValid cfg (slots.getD idx (.vreg 0)) = true :=
    List.all_eq_true.mp hvalid _ hmem
  simpa [evalKExpr] using eval_checked_slot hm heval (slots.getD idx (.vreg 0)) hsl
    (.var (baseOut + idx)) (.var (baseOut + 25 + idx)) heqLo heqHi hokLo hokHi
/-! ## 3. Slice A Symbolic Execution (`+0x07f8 → +0x0fa4`) & Full Row Init A (`+0x07d8 → +0x0fa8`) -/

private theorem slotsFa8_01_all_spill :
    ∀ idx, idx < 25 → (match slotsFa8_01.getD idx (.vreg 0) with | .spillQ _ => true | .vreg _ => false) = true := by
  have hc : ((List.range 25).all fun idx =>
      match slotsFa8_01.getD idx (.vreg 0) with | .spillQ _ => true | .vreg _ => false) = true := by decide
  exact fun idx hidx => List.all_eq_true.mp hc idx (List.mem_range.mpr hidx)

private theorem slotsFa8_23_all_spill :
    ∀ idx, idx < 25 → (match slotsFa8_23.getD idx (.vreg 0) with | .spillQ _ => true | .vreg _ => false) = true := by
  have hc : ((List.range 25).all fun idx =>
      match slotsFa8_23.getD idx (.vreg 0) with | .spillQ _ => true | .vreg _ => false) = true := by decide
  exact fun idx hidx => List.all_eq_true.mp hc idx (List.mem_range.mpr hidx)

theorem seg2_sliceA_ok [MlKemPlacement] {b sp rcBase : BitVec 64} {rho : List (BitVec 8)} {row : Nat}
    (hrho : rho.length = 32) (hrow : row < 4) {s0 : State} {tA0 : BTree (BitVec 64) 9} {F : SepProp}
    (hpc0 : s0.pc = b + 2040#64) (hrun0 : s0.status = .Running)
    (hsp0 : s0.sp = sp) (hspA0 : s0.spAligned = true)
    (hgprs0 : RowCalleeGprs sp rcBase row s0) (hhdr0 : MemAHeaderOk sp rho tA0) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + 4004#64) s0
      ((rcBase ↦ᵣ mlkemData01Bytes) ∗ BTreeMem (sp + 144#64) 286 tA0 ∗ F)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .x0 = sp + 30152#64 ∧
        sf.readReg64 .x1 = 0#64 ∧ sf.readReg64 .x2 = 712#64 ∧ RowCalleeGprs sp rcBase row sf ∧
        ∃ tA : BTree (BitVec 64) 9, MemAHeaderOk sp rho tA ∧
          (∀ idx, idx < 25 → slotHolds cfgA sf tA (slotsFa8_01.getD idx (.vreg 0))
            ((keccakAbsorb 21 0x1f#8 (rowSeed rho row 0)).getD idx 0#64)
            ((keccakAbsorb 21 0x1f#8 (rowSeed rho row 1)).getD idx 0#64)) ∧
          (∀ idx, idx < 25 → slotHolds cfgA sf tA (slotsFa8_23.getD idx (.vreg 0))
            ((keccakAbsorb 21 0x1f#8 (rowSeed rho row 2)).getD idx 0#64)
            ((keccakAbsorb 21 0x1f#8 (rowSeed rho row 3)).getD idx 0#64)) ∧
          (Pf ⊢ (rcBase ↦ᵣ mlkemData01Bytes) ∗ BTreeMem (sp + 144#64) 286 tA ∗ F)) := by
  let env0 := envInitA sp rcBase rho row s0 tA0
  obtain ⟨hm0, hmemEq0⟩ := stInitA_matches hsp0 hspA0 hgprs0 hhdr0
  have henvSp : env0.sp = sp := rfl
  have henvRc : env0.rcBase = rcBase := rfl
  have hspEq : ((rcBase ↦ᵣ mlkemData01Bytes) ∗ BTreeMem (sp + 144#64) 286 tA0 ∗ F) =
      KSpatial cfgA env0 stInitA F := by
    simp only [KSpatial, cfgA, henvSp, henvRc, btreeMem_zero, emp_sepConj]
    rw [hmemEq0]
  rw [hspEq]
  refine sepWP_of_runAndCheckKProg cfgA_valid (env0 := env0) (show 0 < 24 by decide) cert_sliceA hm0
    hpc0 hrun0 ?_
  intro sf envFinal stEnd hpcF hrunF hspF hrcF _hrlF heval hmF hchk
  simp only [chkSliceA, Bool.and_eq_true] at hchk
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
  have hspecEq : specEnvSteps env0 stepsA =
      extendLoopVars env1 2000 (preAbsorbState rho row 2) (preAbsorbState rho row 3) := by
    simp only [stepsA, specEnvSteps, hp0 0 (by decide), hp0 1 (by decide)]
    change specEnvSteps env1 [.range 742 49,
      .loop 791 190 8#5 slotsL2 (expPreAbsorb 2) (expPreAbsorb 3) 2000, .range 982 19] = _
    simp only [specEnvSteps, hp1 2 (by decide), hp1 3 (by decide)]
  have hspecSp : (specEnvSteps env0 stepsA).sp = sp := by rw [hspecEq]; rfl
  have hspecRc : (specEnvSteps env0 stepsA).rcBase = rcBase := by rw [hspecEq]; rfl
  have hspec64 : (specEnvSteps env0 stepsA).vars 64 = BitVec.ofNat 64 row := by rw [hspecEq]; simp [extendLoopVars, env1, env0, envInitA]
  have hspec100 : (specEnvSteps env0 stepsA).vars 100 = rhoW rho 0 := by rw [hspecEq]; simp [extendLoopVars, env1, env0, envInitA]
  have hspec101 : (specEnvSteps env0 stepsA).vars 101 = rhoW rho 1 := by rw [hspecEq]; simp [extendLoopVars, env1, env0, envInitA]
  have hspec102 : (specEnvSteps env0 stepsA).vars 102 = rhoW rho 2 := by rw [hspecEq]; simp [extendLoopVars, env1, env0, envInitA]
  have hspec103 : (specEnvSteps env0 stepsA).vars 103 = rhoW rho 3 := by rw [hspecEq]; simp [extendLoopVars, env1, env0, envInitA]
  have hx0 := eval_checked_gpr hmF heval 0#5 (by decide) (.spAdd 30152#64) hx0_eq hx0_ok
  have hx1 := eval_checked_gpr hmF heval 1#5 (by decide) (.const64 0#64) hx1_eq hx1_ok
  have hx2 := eval_checked_gpr hmF heval 2#5 (by decide) (.const64 712#64) hx2_eq hx2_ok
  have hhdrF := checked_headerOk heval hspecSp hspec100 hspec101 hspec102 hspec103 hhdr_chk
  have hgprsF := checked_calleeGprs hmF heval hspecSp hspecRc hspec64 hgpr_chk
  have hsl01 := checked_outSlots hmF heval (by decide) (by decide) hout01
  have hsl23 := checked_outSlots hmF heval (by decide) (by decide) hout23
  refine SepWP.done hpcF hrunF ⟨hmF.hsp.trans hspF, hmF.hsp_al,
    by simpa [Reg.x0, evalKExpr, hspecSp] using hx0, by simpa [Reg.x1, evalKExpr] using hx1,
    by simpa [Reg.x2, evalKExpr] using hx2, hgprsF, evalMemTree envFinal stEnd.memA, hhdrF, ?_, ?_, ?_⟩
  · intro idx hidx
    have hvLo : (specEnvSteps env0 stepsA).vars (1000 + idx) = (keccakAbsorb 21 0x1f#8 (rowSeed rho row 0)).getD idx 0#64 := by
      rw [hspecEq, keccakAbsorb_rowSeed hrho row 0]
      simp [extendLoopVars, env1, show 1000 + idx < 2000 by omega, show ¬(1000 + idx < 1000) by omega, show 1000 + idx < 1000 + 25 by omega]
    have hvHi : (specEnvSteps env0 stepsA).vars (1000 + 25 + idx) = (keccakAbsorb 21 0x1f#8 (rowSeed rho row 1)).getD idx 0#64 := by
      rw [hspecEq, keccakAbsorb_rowSeed hrho row 1]
      simp [extendLoopVars, env1, show 1000 + 25 + idx < 2000 by omega, show ¬(1000 + 25 + idx < 1000) by omega,
        show ¬(1000 + 25 + idx < 1000 + 25) by omega, show 1000 + 25 + idx < 1000 + 50 by omega]
    simpa [hvLo, hvHi] using hsl01 idx hidx
  · intro idx hidx
    have hvLo : (specEnvSteps env0 stepsA).vars (2000 + idx) = (keccakAbsorb 21 0x1f#8 (rowSeed rho row 2)).getD idx 0#64 := by
      rw [hspecEq, keccakAbsorb_rowSeed hrho row 2]
      simp [extendLoopVars, show ¬(2000 + idx < 2000) by omega, show 2000 + idx < 2000 + 25 by omega]
    have hvHi : (specEnvSteps env0 stepsA).vars (2000 + 25 + idx) = (keccakAbsorb 21 0x1f#8 (rowSeed rho row 3)).getD idx 0#64 := by
      rw [hspecEq, keccakAbsorb_rowSeed hrho row 3]
      simp [extendLoopVars, show ¬(2000 + 25 + idx < 2000) by omega, show ¬(2000 + 25 + idx < 2000 + 25) by omega,
        show 2000 + 25 + idx < 2000 + 50 by omega]
    simpa [hvLo, hvHi] using hsl23 idx hidx
  · simp only [KSpatial, cfgA, hspF, hrcF, henvSp, henvRc, btreeMem_zero, emp_sepConj]; sep_frame

theorem seg2_initA_ok [MlKemPlacement] {b sp rcBase : BitVec 64}
    (_hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    {rho : List (BitVec 8)} {row : Nat} {Rest : SepProp} (hrho : rho.length = 32) (hrow : row < 4)
    {s : State} {P : SepProp} (hpc : s.pc = b + 2008#64) (hrun : s.status = .Running)
    (hpre : RowInitAPre sp rcBase rho row Rest s P) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + 4008#64) s P (RowInitAPost sp rcBase rho row Rest) := by
  subst hbase
  rcases hpre with ⟨hsp, hspA, hsp_chk, hcl, hro, ⟨hx19, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hfp⟩, hx1, tA0, hhdr0, hP⟩
  refine SepWP.weaken_pre hP ?_
  have hprep : SepWP (blkPC07.rebase blkPl07.base (fun _ => none)) (blkPl07.base + 2036#64) s
      ((rcBase ↦ᵣ mlkemData01Bytes) ∗ BTreeMem (sp + 144#64) 286 tA0 ∗
        memRegion (sp + 24720#64) 32 ∗ memRegion (sp + 2560#64) 2176 ∗
        memRegion (sp + 26768#64) 672 ∗ memRegion (sp + 28848#64) 2016 ∗ Rest)
      (fun s1 P1 =>
        s1.sp = sp ∧ s1.spAligned = true ∧
        s1.readReg64 .x0 = sp + 2560#64 ∧ (s1.readReg32 .x1).truncate 8 = 0#8 ∧
        s1.readReg64 .x2 = 2176#64 ∧ RowCalleeGprs sp rcBase row s1 ∧
        (P1 ⊢ memRegion (sp + 2560#64) 2176 ∗ ((rcBase ↦ᵣ mlkemData01Bytes) ∗
          BTreeMem (sp + 144#64) 286 tA0 ∗ MultiLaneSampled (sp + 24720#64) 4 (fun _ => 0) ∗
          memRegion (sp + 26768#64) 672 ∗ memRegion (sp + 28848#64) 2016 ∗ Rest))) := by
    refine SepWP.of_memRegion_btreeMem 4 (sp + 24720#64) (by decide) (by decide)
      (sepProp_ext (by sep_frame) (by sep_frame)) fun tS => ?_
    wp_steps 5
    refine step_strQ128 (wb := none) (ea := sp + 24736#64) (val := 0#128) (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
      (by simp [evalAddrMode, hsp]) (by simp)
      (SepStore128.left (sepStore128_btreeMem (k := 2) (vHi := 0#64) (vLo := 0#64) (by decide) (by decide) (by bv_omega)))
      (by wp_norm_lhs) fun _ => ?_
    refine step_strQ128 (wb := none) (ea := sp + 24720#64) (val := 0#128) (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
      (by simp [evalAddrMode, hsp]) (by simp)
      (SepStore128.left (sepStore128_btreeMem (k := 0) (vHi := 0#64) (vLo := 0#64) (by decide) (by decide) (by bv_omega)))
      (by wp_norm_lhs) fun _ => ?_
    have hzeroS : BTreeMem (sp + 24720#64) 4 ((((tS.set 2 0#64).set 3 0#64).set 0 0#64).set 1 0#64) =
        MultiLaneSampled (sp + 24720#64) 4 (fun _ => 0) :=
      btreeMem4_zero_eq_multiLaneSampled4 _ (by simp [BTree.get_set]) (by simp [BTree.get_set])
        (by simp [BTree.get_set]) (by simp [BTree.get_set])
    refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp [hsp], by simp [State.spAligned, hsp, hsp_chk], by simp, by simp [State.readReg32], by simp,
        ⟨by simp [hx19], by simp, by simp [hx21], by simp [hx22], by simp [hx23],
          by simp [hx24], by simp [hx25], by simp [hx26], by simp [hx27], by simp [hfp]⟩, ?_⟩
    rw [hzeroS]; sep_frame
  refine sepWP_seq_env hcl hro hprep fun s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, _, hx0_1, hx1_1, hx2_1, hgprs1, hP1⟩ => ?_
  have hcall1 : SepWP (blkPC07.rebase blkPl07.base (fun _ => none)) (blkPl07.base + 2040#64) s1 P1
      (fun s2 P2 => s2.sp = sp ∧ s2.spAligned = true ∧ RowCalleeGprs sp rcBase row s2 ∧
        (P2 ⊢ (rcBase ↦ᵣ mlkemData01Bytes) ∗ BTreeMem (sp + 144#64) 286 tA0 ∗
          (MultiLaneSampled (sp + 24720#64) 4 (fun _ => 0) ∗
            MultiLaneSlots (sp + 2560#64) 544 4 (fun _ => List.replicate 272 0#16) ∗
            memRegion (sp + 26768#64) 672 ∗ memRegion (sp + 28848#64) 2016 ∗ Rest))) := by
    refine SepWP.weaken_pre hP1 ?_; rcases hgprs1 with ⟨g19, g20, g21, g22, g23, g24, g25, g26, g27, gfp⟩
    wp_call (blk29_memset_07 blkPl07.base) (sp + 2560#64, 0#8, 2176)
    have hsp2 : sf.sp = sp := by simp [*]
    refine SepWP.done (by wp_norm_lhs) (by assumption) ⟨hsp2, by simp [State.spAligned, hsp2, hsp_chk],
      ⟨by simp [*], by simp [*], by simp [*], by simp [*], by simp [*], by simp [*], by simp [*], by simp [*], by simp [*], by simp [*]⟩, ?_⟩
    rw [memset2176_eq_multiLaneSlots4]; sep_frame
  refine sepWP_seq_env hcl1 hro1 hcall1 fun s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hgprs2, hP2⟩ => ?_
  refine sepWP_seq_env hcl2 hro2 (SepWP.weaken_pre hP2 (seg2_sliceA_ok hrho hrow hpc2 hrun2 hsp2 hspA2 hgprs2 hhdr0)) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 hro3 ⟨hsp3, _, hx0_3, hx1_3, hx2_3, hgprs3, tA, hhdr, hsl01, hsl23, hP3⟩
  have hcall2 : SepWP (blkPC07.rebase blkPl07.base (fun _ => none)) (blkPl07.base + 4008#64) s3 P3
      (fun s4 P4 => s4.sp = sp ∧ s4.spAligned = true ∧ RowCalleeGprs sp rcBase row s4 ∧
        (P4 ⊢ (rcBase ↦ᵣ mlkemData01Bytes) ∗ BTreeMem (sp + 144#64) 286 tA ∗
          MultiLaneSampled (sp + 24720#64) 4 (fun _ => 0) ∗ MultiLaneSlots (sp + 2560#64) 544 4 (fun _ => List.replicate 272 0#16) ∗
          memRegion (sp + 26768#64) 672 ∗ memRegion (sp + 28848#64) 2016 ∗ Rest)) := by
    have hsp28848 : memRegion (sp + 28848#64) 2016 = memRegion (sp + 28848#64) 1304 ∗ memRegion (sp + 30152#64) 712 :=
      memRegion_split' (b := sp + 28848#64) (b' := sp + 30152#64) (n := (1304 : Nat)) (k := (712 : Nat)) rfl (by bv_omega) (by decide)
    refine SepWP.weaken_pre hP3 (SepWP.weaken_pre (by rw [hsp28848]; sep_frame : _ ⊢
      memRegion (sp + 30152#64) 712 ∗ ((rcBase ↦ᵣ mlkemData01Bytes) ∗ BTreeMem (sp + 144#64) 286 tA ∗
        MultiLaneSampled (sp + 24720#64) 4 (fun _ => 0) ∗ MultiLaneSlots (sp + 2560#64) 544 4 (fun _ => List.replicate 272 0#16) ∗
        memRegion (sp + 26768#64) 672 ∗ memRegion (sp + 28848#64) 1304 ∗ Rest)) ?_)
    rcases hgprs3 with ⟨g19, g20, g21, g22, g23, g24, g25, g26, g27, gfp⟩
    wp_call (blk29_memset_07 blkPl07.base) (sp + 30152#64, 0#8, 712)
    have hsp4 : sf.sp = sp := by simp [*]
    refine SepWP.done (by wp_norm_lhs) (by assumption) ⟨hsp4, by simp [State.spAligned, hsp4, hsp_chk],
      ⟨by simp [*], by simp [*], by simp [*], by simp [*], by simp [*], by simp [*], by simp [*], by simp [*], by simp [*], by simp [*]⟩, ?_⟩
    have h712 : ((sp + 30152#64) ↦ₛ List.replicate 712 0#8) ⊢ memRegion (sp + 30152#64) 712 := by
      have hp := pointsToBytes_entails_memRegion (sp + 30152#64) (List.replicate 712 0#8)
      rwa [List.length_replicate] at hp
    rw [hsp28848]; exact entails_sub h712 (by sep_frame) (by sep_frame)
  refine sepWP_seq_env hcl3 hro3 hcall2 fun sf Pf hpcF hrunF hclF hroF ⟨hspF, hspAF, hgprsF, hPf⟩ => ?_
  exact SepWP.done hpcF hrunF ⟨hspF, hspAF, hsp_chk, hclF, hroF, hgprsF, tA, hhdr,
    fun idx hidx => slotHolds_spill_transfer rfl (slotsFa8_01_all_spill idx hidx) (hsl01 idx hidx),
    fun idx hidx => slotHolds_spill_transfer rfl (slotsFa8_23_all_spill idx hidx) (hsl23 idx hidx), hPf⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2InitA
