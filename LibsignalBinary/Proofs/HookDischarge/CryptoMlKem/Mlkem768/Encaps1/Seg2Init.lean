/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.GenPlacedFetches
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.XofDeterminism -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkWords -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.SiteStep -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Mem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymBridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Loop -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Prog -- proof-setup: allow-public-import
public meta import ProofLib.GenPlacedFetches
meta import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Round
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Step
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a

/-!
# `encapsulate1_serialized` (`B03`) — `Seg2` Row Init Symbolic States & Helpers (`Seg2Init`)

Row-level state predicates (`Seg2LoopState`, `Seg2RowExit`), `Seg2RegInv` non-vacuity witness,
`+0x0524 → +0x0528` (`B29` `memset`), spatial & branch helpers, pre-computed symbolic states for
6-permutation SHAKE-128 absorb+squeeze (`L1..L6`, `+0x0504 → +0x21cc`) and clamp/branch dispatch
(`+0x2500 → +0x026c / +0x2580`), and pre-absorb byte-packing lemmas.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Init

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (
  mlkemData01Bytes mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement add_off_reloc_cancel add_reloc_cancel add_zero_reloc_cancel mbase
  mlkemBlockPlacement_ρ mlkemCall_of_blockOk mlkemMpl resolve_blk29 seq_codeLoaded_lr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk SepWP.roDataAt_intro)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (mlkemMemsetSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps (blk29_memset_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  KeccakState keccakAbsorb keccakExtractRate keccakF1600 keccakPermuteN keccakZeroState
  packLane64 shake128BlockAt shake128FirstBlocks)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Round (
  keccakF1600_size)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge (
  keccakLastBlock readLE_8_eq_packLane64)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec (
  clampSampled keccakPermuteN_succ_right packHalfwordsLE packHalfwordsLE_replicate_zero
  shake128FirstBlocks_three)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.XofDeterminism (
  keccakAbsorb_21_lt168 keccakXorRate21)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem (
  MultiLaneSampled MultiLaneSepFrom MultiLaneSlots)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.SiteStep (RejSiteConfig)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework (
  MultiLaneRawXofInv MultiLaneXofInv allLanesDone)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (spAligned_of_sp_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base (
  blk03_code_eq blk03_tree_size blkLib03 blkPC03 blkPl03 blkPlaceable03 blkTree03)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a (
  Seg2ConstsLo Seg2RegInv Seg2SeedConsts blkPl03_ρ)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymDefs (
  BTree KCfg KEnv KExpr KPFlag KSlot KState clampWord64 evalKExpr fetchWordTree03 runKRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Mem (
  TreeMem TreeMem_eq_pointsToWords64 btreeOfWords btreeOfWords_get fetch_blk03_seg2a
  fetch_blk03_seg2b seg2SeedConsts_eq_treeMem seedConstsWords treeMem_join zeroTree9)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymBridge (
  KCfgWf KStateMatches KSpatial evalMemTree setPC_self)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Step (
  sepWP_runKRange_seg2b)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Loop (
  readSlot slotHolds slotValid truncate64_append)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Prog (
  evalSlotsHi evalSlotsLo inv01Slots inv2Slots kpflagOptBeq kpflagOptBeq_eq_true
  sepWP_of_stepKLoop stepKLoopSym)

/-! ## 1. `Seg2RegInv` Witness, `rowSeeds` / `rowPermState`, & Row State Predicates -/

theorem Seg2RegInv_nonvacuous [MlKemPlacement] : ∃ s : State, Seg2RegInv 0#64 s := by
  let s0 : State := { (default : State) with sp := 0#64, status := .Running }
  let sBase : State :=
    (((((((((s0
      |>.writeReg64 .x19
          (mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29"))
      |>.writeReg64 .x20 4272#64) |>.writeReg64 .x21 12448#64) |>.writeReg64 .x23 2456#64)
      |>.writeReg64 (.gpr 24#5) 544#64) |>.writeReg64 (.gpr 25#5) 14248#64)
      |>.writeReg64 (.gpr 26#5) (13984#64 + 11#64)) |>.writeReg64 (.gpr 27#5) 256#64)
      |>.writeReg64 .x28 13984#64)
  refine ⟨sBase, ?_⟩
  dsimp only [Seg2RegInv, sBase, s0, State.spAligned, State.writeReg64,
    State.readReg64, RegFile.read, RegFile.write]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

@[expose] def rowSeeds (rho : List (BitVec 8)) (row : Nat) : Nat → List (BitVec 8) :=
  fun c => rho ++ [BitVec.ofNat 8 row, BitVec.ofNat 8 c]

@[expose] def rowPermState (rho : List (BitVec 8)) (row c n : Nat) : KeccakState :=
  keccakPermuteN n (keccakAbsorb 21 0x1f#8 (rowSeeds rho row c))

theorem rowPermState_zero (rho : List (BitVec 8)) (hrho : rho.length = 32) (row c : Nat) :
    rowPermState rho row c 0 =
      keccakF1600 (keccakXorRate21 keccakZeroState (keccakLastBlock 168 0x1f#8 (rowSeeds rho row c))) := by
  unfold rowPermState keccakPermuteN
  exact keccakAbsorb_21_lt168 0x1f#8 (rowSeeds rho row c) (by simp [rowSeeds, hrho])

theorem rowPermState_succ (rho : List (BitVec 8)) (row c n : Nat) :
    keccakF1600 (rowPermState rho row c n) = rowPermState rho row c (n + 1) :=
  (keccakPermuteN_succ_right n _).symm

theorem shake128BlockAt_rowSeeds_eq (rho : List (BitVec 8)) (row c n : Nat) :
    keccakExtractRate 21 (rowPermState rho row c n) = shake128BlockAt (rowSeeds rho row c) n := rfl

theorem shake128FirstBlocks_rowSeeds_three (rho : List (BitVec 8)) (row c : Nat) :
    keccakExtractRate 21 (rowPermState rho row c 0) ++
        (keccakExtractRate 21 (rowPermState rho row c 1) ++
          keccakExtractRate 21 (rowPermState rho row c 2)) =
      shake128FirstBlocks (rowSeeds rho row c) 3 := by
  rw [← List.append_assoc, shake128BlockAt_rowSeeds_eq, shake128BlockAt_rowSeeds_eq,
      shake128BlockAt_rowSeeds_eq, ← shake128FirstBlocks_three]

@[expose] def cfgInit : KCfg := { offA := 96, lenA := 262, offB := 2192, lenB := 189, hasConstsLo := true }
@[expose] def cfgClamp : KCfg := { offA := 96, lenA := 262, offB := 12448, lenB := 3, hasConstsLo := false }
@[expose] def cfgExtra : KCfg := { offA := 96, lenA := 262, offB := 13984, lenB := 63, hasConstsLo := false }

@[expose] def cfgRejInit3 : RejSiteConfig :=
  { v := .varA, nLanes := 3, nChunks := 21, slotStride := 544,
    rIdx := .x9, rSqPtr := .x10, rPrevIdx := .x11,
    rSampArr := .x21, rSlotStride := .gpr 24#5, rSlotsBase := .x20 }

@[expose] def Seg2LoopState [MlKemPlacement] (b sp : BitVec 64) (rho : List (BitVec 8))
    (row : Nat) (F : SepProp) (extra : Nat) (s : State) (P : SepProp) : Prop :=
  s.pc = b + 0x2580#64 ∧ s.status = .Running ∧
  mlkemMultiLib.CodeLoaded mlkemMpl s.mem ∧ MlKemRoOk mlkemMpl s.mem ∧ Seg2RegInv sp s ∧
  s.readReg64 .x8 = BitVec.ofNat 64 (row + 1) ∧ s.readReg64 .x22 = BitVec.ofNat 64 row ∧
  ∃ (tA : BTree (BitVec 64) 9) (sampled : Nat → Nat) (hws : Nat → List (BitVec 16)),
    (∀ i, i < 10 → tA.get (30 + i) = (seedConstsWords rho).getD i 0#64) ∧
    (∀ idx, idx < 25 →
      slotHolds cfgClamp s tA (inv01Slots.getD idx (.vreg 0))
        ((rowPermState rho row 0 (extra + 2)).getD idx 0#64)
        ((rowPermState rho row 1 (extra + 2)).getD idx 0#64)) ∧
    (∀ idx, idx < 25 →
      slotHolds cfgClamp s tA (inv2Slots.getD idx (.vreg 0))
        ((rowPermState rho row 2 (extra + 2)).getD idx 0#64) 0#64) ∧
    MultiLaneXofInv 3 (rowSeeds rho row) extra sampled hws ∧
    (P ⊢ Seg2ConstsLo sp ∗ TreeMem (sp + 96#64) 262 tA ∗ memRegion (sp + 2192#64) 1512 ∗
      MultiLaneSlots (sp + 4272#64) 544 3 hws ∗ MultiLaneSampled (sp + 12448#64) 3 sampled ∗
      memRegion (sp + 13984#64) 504 ∗ F)

@[expose] def Seg2RowExit [MlKemPlacement] (b sp : BitVec 64) (rho : List (BitVec 8))
    (row : Nat) (F : SepProp) (s : State) (P : SepProp) : Prop :=
  s.pc = b + 0x026c#64 ∧ s.status = .Running ∧
  mlkemMultiLib.CodeLoaded mlkemMpl s.mem ∧ MlKemRoOk mlkemMpl s.mem ∧ Seg2RegInv sp s ∧
  s.readReg64 .x8 = BitVec.ofNat 64 (row + 1) ∧ s.readReg64 .x22 = BitVec.ofNat 64 row ∧
  ∃ (extra : Nat) (tA : BTree (BitVec 64) 9) (sampled : Nat → Nat) (hws : Nat → List (BitVec 16)),
    allLanesDone 3 (rowSeeds rho row) extra = true ∧
    MultiLaneXofInv 3 (rowSeeds rho row) extra sampled hws ∧
    (∀ i, i < 10 → tA.get (30 + i) = (seedConstsWords rho).getD i 0#64) ∧
    (P ⊢ Seg2ConstsLo sp ∗ TreeMem (sp + 96#64) 262 tA ∗ memRegion (sp + 2192#64) 1512 ∗
      MultiLaneSlots (sp + 4272#64) 544 3 hws ∗ memRegion (sp + 12448#64) 24 ∗
      memRegion (sp + 13984#64) 504 ∗ F)

/-! ## 2. `+0x0524 → +0x0528` (`B29` `memset`), Spatial Bridges, & Clamp/Branch Helpers -/

section
set_option linter.literalFetch false
gen_placed_fetches blkPC03 blkLib03 blkTree03 blk03_code_eq blk03_tree_size
  via_placement blkPl03 blkPlaceable03 [0x0524 → 0x0528]
end

theorem seg2_bl_memset [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = b + 0x0524#64) (hrun : s.status = .Running) (hreg : Seg2RegInv sp s)
    (hx0 : s.readReg64 .x0 = sp + 4272#64) (hx1 : s.readReg32 .x1 = 0#32)
    (hx2 : s.readReg64 .x2 = 1632#64) (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + 0x0528#64) s
      (memRegion (sp + 4272#64) 1632 ∗ Rest)
      (fun sf Pf => Seg2RegInv sp sf ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        (Pf ⊢ ((sp + 4272#64) ↦ₛ List.replicate 1632 0#8) ∗ Rest)) := by
  subst hbase
  rcases hreg with ⟨hsp, hsp_al, hx19, hx20, hx21, hx23, hx24, hx25, hx26, hx27, hx28⟩
  wp_cut_codeLoaded; wp_step
  wp_mlkem_call blk29_memset_ok (sp + 4272#64, 0#8, (1632 : Nat))
  refine SepWP.done (by wp_norm_lhs) ‹_›
    ⟨⟨hsp_sf.trans hsp, spAligned_of_sp_eq hsp_al hsp (hsp_sf.trans hsp),
      Eq.trans ‹_› hx19, Eq.trans ‹_› hx20, Eq.trans ‹_› hx21, Eq.trans ‹_› hx23,
      Eq.trans ‹_› hx24, Eq.trans ‹_› hx25, Eq.trans ‹_› hx26, Eq.trans ‹_› hx27,
      Eq.trans ‹_› hx28⟩, ‹_›, by sep_frame⟩

attribute [local irreducible] keccakF1600 blkPC03

theorem keccakRc_intro [MlKemPlacement] {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hro : MlKemRoOk mlkemMpl s.mem)
    (h : SepWP prog target_pc s
      (((mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29") ↦ᵣ
        mlkemData01Bytes) ∗ P) post oom) :
    SepWP prog target_pc s P post oom :=
  SepWP.roDataAt_intro hro.keccakRc (by decide +kernel) h

theorem multiLaneSampled3_eq_treeMem (sp : BitVec 64) (sampled : Nat → Nat)
    (t : BTree (BitVec 64) 9)
    (h0 : t.get 0 = BitVec.ofNat 64 (sampled 0)) (h1 : t.get 1 = BitVec.ofNat 64 (sampled 1))
    (h2 : t.get 2 = BitVec.ofNat 64 (sampled 2)) :
    MultiLaneSampled (sp + 12448#64) 3 sampled = TreeMem (sp + 12448#64) 3 t := by
  rw [TreeMem_eq_pointsToWords64]
  change MultiLaneSepFrom
      (fun i s => (sp + 12448#64 + BitVec.ofNat 64 (8 * i)) ↦₆₄ BitVec.ofNat 64 s) 0 3 sampled =
    pointsToWords64 (sp + 12448#64) [t.get 0, t.get 1, t.get 2]
  rw [h0, h1, h2]
  simp only [MultiLaneSepFrom, pointsToWords64_cons, pointsToWords64_nil,
    sepConj_emp, BitVec.add_assoc]; rfl

theorem replicate1632_eq_multiLaneSlots0 (sp : BitVec 64) :
    ((sp + 4272#64) ↦ₛ List.replicate 1632 0#8) =
      MultiLaneSlots (sp + 4272#64) 544 3 (fun _ => List.replicate 272 0#16) := by
  have h544 : packHalfwordsLE (List.replicate 272 0#16) = List.replicate 544 0#8 :=
    packHalfwordsLE_replicate_zero 272
  have hsplit : List.replicate 1632 (0#8) =
      List.replicate 544 0#8 ++ (List.replicate 544 0#8 ++ List.replicate 544 0#8) := by
    rw [← List.replicate_add, ← List.replicate_add]
  rw [hsplit, pointsToBytes_append, pointsToBytes_append]
  simp only [MultiLaneSlots, MultiLaneSepFrom, h544, List.length_replicate,
    sepConj_emp, BitVec.add_assoc]; rfl

theorem entry_memA_join (sp : BitVec 64) (rho : List (BitVec 8)) (tLo tHi : BTree (BitVec 64) 9) :
    ∃ tA : BTree (BitVec 64) 9,
      (∀ i, i < 10 → tA.get (30 + i) = (seedConstsWords rho).getD i 0#64) ∧
      TreeMem (sp + 96#64) 30 tLo ∗ Seg2SeedConsts sp rho ∗ TreeMem (sp + 416#64) 222 tHi =
        TreeMem (sp + 96#64) 262 tA := by
  have h512 : (2 ^ 9 : Nat) = 512 := by decide
  let tMid := btreeOfWords 0 (seedConstsWords rho) zeroTree9
  have htMid : ∀ i, i < 10 → tMid.get i = (seedConstsWords rho).getD i 0#64 := fun i hi => by
    have hlen : (seedConstsWords rho).length = 10 := rfl
    simpa [Nat.zero_add] using btreeOfWords_get 0 (seedConstsWords rho) zeroTree9 i (by omega) (by omega)
  let t01 := BTree.ofFn 9 fun i => if i < 30 then tLo.get i else tMid.get (i - 30)
  let tA := BTree.ofFn 9 fun i => if i < 40 then t01.get i else tHi.get (i - 40)
  refine ⟨tA, fun i hi => ?_, ?_⟩
  · rw [BTree.get_ofFn 9 _ (30 + i) (by omega)]
    simp only [show 30 + i < 40 by omega, ↓reduceIte]
    rw [BTree.get_ofFn 9 _ (30 + i) (by omega)]
    simp only [show ¬(30 + i < 30) by omega, ↓reduceIte, show 30 + i - 30 = i by omega]
    exact htMid i hi
  · rw [seg2SeedConsts_eq_treeMem sp rho tMid htMid,
        show sp + 336#64 = (sp + 96#64) + BitVec.ofNat 64 (8 * 30) by bv_omega, ← sepConj_assoc,
        treeMem_join (t := t01)
          (fun i hi => by rw [BTree.get_ofFn 9 _ i (by omega)]; simp [hi])
          (fun i hi => by rw [BTree.get_ofFn 9 _ (30 + i) (by omega)]; simp [show ¬(30 + i < 30) by omega]),
        show sp + 416#64 = (sp + 96#64) + BitVec.ofNat 64 (8 * 40) by bv_omega,
        treeMem_join (n1 := 40) (n2 := 222) (t := tA)
          (fun i hi => by rw [BTree.get_ofFn 9 _ i (by omega)]; simp [hi])
          (fun i hi => by rw [BTree.get_ofFn 9 _ (40 + i) (by omega)]; simp [show ¬(40 + i < 40) by omega])]

private theorem clampWord64_fin :
    ∀ s : Fin 272, clampWord64 (BitVec.ofNat 64 s.val) = BitVec.ofNat 64 (clampSampled s.val) := by
  decide +kernel

theorem clampWord64_of_le271 {s : Nat} (hs : s ≤ 271) :
    clampWord64 (BitVec.ofNat 64 s) = BitVec.ofNat 64 (clampSampled s) := clampWord64_fin ⟨s, by omega⟩

private theorem condCC_256_fin :
    ∀ s : Fin 272, ConditionHolds .CC (subsPState64 (BitVec.ofNat 64 s.val) 256#64) = decide (s.val < 256) := by
  decide +kernel

theorem condCC_256_of_le271 {s : Nat} (hs : s ≤ 271) :
    ConditionHolds .CC (subsPState64 (BitVec.ofNat 64 s) 256#64) = decide (s < 256) := condCC_256_fin ⟨s, by omega⟩

private theorem condCS_256_fin :
    ∀ s : Fin 272, ConditionHolds .CS (subsPState64 (BitVec.ofNat 64 s.val) 256#64) = decide (256 ≤ s.val) := by
  decide +kernel

theorem condCS_256_of_le271 {s : Nat} (hs : s ≤ 271) :
    ConditionHolds .CS (subsPState64 (BitVec.ofNat 64 s) 256#64) = decide (256 ≤ s) := condCS_256_fin ⟨s, by omega⟩

private theorem condHI_255_fin :
    ∀ s : Fin 272, ConditionHolds .HI (subsPState64 (BitVec.ofNat 64 s.val) 255#64) = decide (256 ≤ s.val) := by
  decide +kernel

theorem condHI_255_of_le271 {s : Nat} (hs : s ≤ 271) :
    ConditionHolds .HI (subsPState64 (BitVec.ofNat 64 s) 255#64) = decide (256 ≤ s) := condHI_255_fin ⟨s, by omega⟩

theorem raw_sampled_le271 {N : Nat} {seeds : Nat → List (BitVec 8)} {extra : Nat}
    {sampled : Nat → Nat} {hws : Nat → List (BitVec 16)}
    (hraw : MultiLaneRawXofInv N seeds extra sampled hws) {i : Nat} (hi : i < N) :
    sampled i ≤ 271 := by
  rcases (hraw i hi).2.1 with ⟨h, _⟩ | ⟨_, h, _⟩ <;> omega

theorem step_b_seg2b [MlKemPlacement] {b tgt : BitVec 64} {w : Nat} {disp : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hlo : 330 ≤ w) (hhi : w < 3237) (hfw : fetchWordTree03 w = some (.b disp))
    (hpc : s.pc = b + BitVec.ofNat 64 (4 * w)) (hrun : s.status = .Running)
    (hnext : SepWP (blkPC03.rebase b (fun _ => none)) tgt
      (s.setPC (b + BitVec.ofNat 64 (4 * w) + disp)) P post oom) :
    SepWP (blkPC03.rebase b (fun _ => none)) tgt s P post oom := by
  refine SepWP.step_pure hpc hrun (fetch_blk03_seg2b hlo hhi hfw)
    (s' := s.setPC (b + BitVec.ofNat 64 (4 * w) + disp)) ?_ rfl hnext
  rw [setPC_self hpc]; simp [Program.evalInst, execInstWithSvc, hpc]

theorem step_bCond_seg2b [MlKemPlacement] {b tgt : BitVec 64} {w : Nat}
    {cond : CondCode} {disp : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hlo : 330 ≤ w) (hhi : w < 3237) (hfw : fetchWordTree03 w = some (.bCond cond disp))
    (hpc : s.pc = b + BitVec.ofNat 64 (4 * w)) (hrun : s.status = .Running)
    (hTaken : ConditionHolds cond s.pstate = true →
      SepWP (blkPC03.rebase b (fun _ => none)) tgt
        (s.setPC (b + BitVec.ofNat 64 (4 * w) + disp)) P post oom)
    (hFall : ConditionHolds cond s.pstate = false →
      SepWP (blkPC03.rebase b (fun _ => none)) tgt
        (s.setPC (b + BitVec.ofNat 64 (4 * (w + 1)))) P post oom) :
    SepWP (blkPC03.rebase b (fun _ => none)) tgt s P post oom := by
  by_cases hc : ConditionHolds cond s.pstate = true
  · refine SepWP.step_pure hpc hrun (fetch_blk03_seg2b hlo hhi hfw)
      (s' := s.setPC (b + BitVec.ofNat 64 (4 * w) + disp)) ?_ rfl (hTaken hc)
    rw [setPC_self hpc]; simp [Program.evalInst, execInstWithSvc, hc, hpc]
  · have hcF : ConditionHolds cond s.pstate = false := Bool.eq_false_iff.mpr hc
    have hpcAdv : s.advancePC = s.setPC (b + BitVec.ofNat 64 (4 * (w + 1))) := by
      cases s; simp only [State.advancePC, State.setPC] at hpc ⊢; congr 1; rw [hpc]; bv_omega
    refine SepWP.step_pure hpc hrun (fetch_blk03_seg2b hlo hhi hfw)
      (s' := s.advancePC) ?_ rfl (by rw [hpcAdv]; exact hFall hcF)
    rw [setPC_self hpc]; simp [Program.evalInst, execInstWithSvc, hcF]


theorem cfgInit_wf : KCfgWf cfgInit := by decide +kernel
theorem cfgClamp_wf : KCfgWf cfgClamp := by decide +kernel
theorem cfgExtra_wf : KCfgWf cfgExtra := by decide +kernel

@[expose] def cfgRejExtra1 : RejSiteConfig :=
  { v := .varA, nLanes := 3, nChunks := 7, slotStride := 544,
    rIdx := .x11, rSqPtr := .x9, rPrevIdx := .x10,
    rSampArr := .x21, rSlotStride := .gpr 24#5, rSlotsBase := .x20 }

theorem cfgRejInit3_valid : cfgRejInit3.Valid := by decide +kernel
theorem cfgRejExtra1_valid : cfgRejExtra1.Valid := by decide +kernel

theorem step_bCond_seg2a [MlKemPlacement] {b tgt : BitVec 64} {w : Nat}
    {cond : CondCode} {disp : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hlo : 155 ≤ w) (hhi : w < 329) (hfw : fetchWordTree03 w = some (.bCond cond disp))
    (hpc : s.pc = b + BitVec.ofNat 64 (4 * w)) (hrun : s.status = .Running)
    (hTaken : ConditionHolds cond s.pstate = true →
      SepWP (blkPC03.rebase b (fun _ => none)) tgt
        (s.setPC (b + BitVec.ofNat 64 (4 * w) + disp)) P post oom)
    (hFall : ConditionHolds cond s.pstate = false →
      SepWP (blkPC03.rebase b (fun _ => none)) tgt
        (s.setPC (b + BitVec.ofNat 64 (4 * (w + 1)))) P post oom) :
    SepWP (blkPC03.rebase b (fun _ => none)) tgt s P post oom := by
  by_cases hc : ConditionHolds cond s.pstate = true
  · refine SepWP.step_pure hpc hrun (fetch_blk03_seg2a hlo hhi hfw)
      (s' := s.setPC (b + BitVec.ofNat 64 (4 * w) + disp)) ?_ rfl (hTaken hc)
    rw [setPC_self hpc]; simp [Program.evalInst, execInstWithSvc, hc, hpc]
  · have hcF : ConditionHolds cond s.pstate = false := Bool.eq_false_iff.mpr hc
    have hpcAdv : s.advancePC = s.setPC (b + BitVec.ofNat 64 (4 * (w + 1))) := by
      cases s; simp only [State.advancePC, State.setPC] at hpc ⊢; congr 1; rw [hpc]; bv_omega
    refine SepWP.step_pure hpc hrun (fetch_blk03_seg2a hlo hhi hfw)
      (s' := s.advancePC) ?_ rfl (by rw [hpcAdv]; exact hFall hcF)
    rw [setPC_self hpc]; simp [Program.evalInst, execInstWithSvc, hcF]

/-! ## 3. Pre-Absorb Byte-Packing & Multi-Step Symbolic Keccak Runner (`runAndCheckKProg`) -/

theorem rowPermState_size {rho : List (BitVec 8)} (hrho : rho.length = 32) (row c n : Nat) :
    (rowPermState rho row c n).size = 25 := by
  cases n with
  | zero => rw [rowPermState_zero rho hrho row c]; exact keccakF1600_size _
  | succ k => rw [← rowPermState_succ]; exact keccakF1600_size _

@[expose] def exprOnlyVar96 : KExpr → Bool
  | .var id => id == 96
  | .const64 _ | .rcVal _ => true
  | .xor a b | .bic a b | .and64 a b | .or64 a b | .add64 a b | .insByte0 a b =>
      exprOnlyVar96 a && exprOnlyVar96 b
  | .bsl m a b => exprOnlyVar96 m && exprOnlyVar96 a && exprOnlyVar96 b
  | .shl a _ | .ushr a _ | .rotl a _ | .clamp64 a => exprOnlyVar96 a
  | _ => false

@[expose] def envRow (row : Nat) : KEnv :=
  { sp := 0#64, rcBase := 0#64, rLoop := 0,
    vars := fun id => if id == 96 then BitVec.ofNat 64 row else 0#64 }

theorem evalKExpr_eq_envRow {env : KEnv} {row : Nat} (h96 : env.vars 96 = BitVec.ofNat 64 row) :
    ∀ {e : KExpr}, exprOnlyVar96 e = true → evalKExpr env e = evalKExpr (envRow row) e
  | .var id, h => by have hid : id = 96 := beq_iff_eq.mp h; subst hid; simp [evalKExpr, envRow, h96]
  | .const64 _, _ | .rcVal _, _ => rfl
  | .spAdd _, h | .rcAdd _, h | .rcLoopOff, h | .rcLoopPtr, h | .rcLoopNext, h | .rcLoopVal, h =>
      nomatch h
  | .xor _ _, h | .bic _ _, h | .and64 _ _, h | .or64 _ _, h | .add64 _ _, h | .insByte0 _ _, h => by
      simp only [exprOnlyVar96, Bool.and_eq_true] at h
      simp [evalKExpr, evalKExpr_eq_envRow h96 h.1, evalKExpr_eq_envRow h96 h.2]
  | .bsl _ _ _, h => by
      simp only [exprOnlyVar96, Bool.and_eq_true] at h
      simp [evalKExpr, evalKExpr_eq_envRow h96 h.1.1, evalKExpr_eq_envRow h96 h.1.2, evalKExpr_eq_envRow h96 h.2]
  | .shl _ _, h | .ushr _ _, h | .rotl _ _, h | .clamp64 _, h => by
      simp only [exprOnlyVar96] at h
      simp [evalKExpr, evalKExpr_eq_envRow h96 h]

private theorem lastBlock168_rowSeeds_getD {rho : List (BitVec 8)} (hrho : rho.length = 32)
    (row c j : Nat) (hj : j < 168) :
    (keccakLastBlock 168 0x1f#8 (rowSeeds rho row c)).getD j 0#8 =
      if j < 32 then rho.getD j 0#8
      else if j = 32 then BitVec.ofNat 8 row
      else if j = 33 then BitVec.ofNat 8 c
      else if j = 34 then 0x1f#8
      else if j = 167 then 0x80#8
      else 0#8 := by
  have hlen : (rowSeeds rho row c).length = 34 := by simp [rowSeeds, hrho]
  rw [keccakLastBlock, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
  simp only [Option.map_some, Option.getD_some, hlen,
    show 34 / 168 = 0 by decide, show 34 % 168 = 34 by decide, Nat.zero_mul, List.drop_zero,
    show 168 - 1 = 167 by decide]
  by_cases hj32 : j < 32
  · have hj34 : j < 34 := by omega
    have hj167 : (j == 167) = false := beq_false_of_ne (by omega)
    simp only [hj32, hj34, hj167, ↓reduceIte, Bool.false_eq_true]
    rw [rowSeeds, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by omega)]
  · by_cases heq32 : j = 32
    · subst heq32
      simp only [hj32, show (32 : Nat) < 34 by decide, show ((32 : Nat) == 167) = false by decide,
        ↓reduceIte, Bool.false_eq_true]
      rw [rowSeeds, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hrho]; rfl
    · by_cases heq33 : j = 33
      · subst heq33
        simp only [hj32, heq32, show (33 : Nat) < 34 by decide,
          show ((33 : Nat) == 167) = false by decide, ↓reduceIte, Bool.false_eq_true]
        rw [rowSeeds, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hrho]; rfl
      · by_cases heq34 : j = 34
        · subst heq34; rfl
        · by_cases heq167 : j = 167
          · subst heq167; simp
          · simp only [hj32, heq32, heq33, heq34, heq167, show ¬(j < 34) by omega,
              beq_false_of_ne heq34, beq_false_of_ne heq167, ↓reduceIte, Bool.false_eq_true]

theorem lastBlock_rowSeeds_pack_lt4 {rho : List (BitVec 8)} (hrho : rho.length = 32)
    (row c : Nat) {k : Nat} (hk : k < 4) :
    packLane64 (keccakLastBlock 168 0x1f#8 (rowSeeds rho row c)) (8 * k) =
      ByteSlice.readLE rho (8 * k) 8 := by
  rw [readLE_8_eq_packLane64]
  have hget : ∀ j, j < 8 →
      (keccakLastBlock 168 0x1f#8 (rowSeeds rho row c)).getD (8 * k + j) 0#8 =
        rho.getD (8 * k + j) 0#8 := fun j hj => by
    rw [lastBlock168_rowSeeds_getD hrho row c (8 * k + j) (by omega)]
    simp [show 8 * k + j < 32 by omega]
  unfold packLane64
  rw [show (keccakLastBlock 168 0x1f#8 (rowSeeds rho row c)).getD (8 * k) 0#8 =
        (keccakLastBlock 168 0x1f#8 (rowSeeds rho row c)).getD (8 * k + 0) 0#8 by simp,
      hget 0 (by decide), hget 1 (by decide), hget 2 (by decide), hget 3 (by decide),
      hget 4 (by decide), hget 5 (by decide), hget 6 (by decide), hget 7 (by decide), Nat.add_zero]

theorem lastBlock_rowSeeds_pack_ge4 {rho : List (BitVec 8)} (hrho : rho.length = 32)
    (row c : Nat) {k : Nat} (hk : 4 ≤ k) :
    packLane64 (keccakLastBlock 168 0x1f#8 (rowSeeds rho row c)) (8 * k) =
      packLane64 (keccakLastBlock 168 0x1f#8 (rowSeeds (List.replicate 32 0#8) row c)) (8 * k) := by
  have hrep : (List.replicate 32 0#8).length = 32 := List.length_replicate
  have hget : ∀ j, j < 8 →
      (keccakLastBlock 168 0x1f#8 (rowSeeds rho row c)).getD (8 * k + j) 0#8 =
        (keccakLastBlock 168 0x1f#8 (rowSeeds (List.replicate 32 0#8) row c)).getD (8 * k + j) 0#8 :=
    fun j _ => by
      by_cases h168 : 8 * k + j < 168
      · rw [lastBlock168_rowSeeds_getD hrho row c (8 * k + j) h168,
            lastBlock168_rowSeeds_getD hrep row c (8 * k + j) h168]
        simp [show ¬(8 * k + j < 32) by omega]
      · simp [keccakLastBlock, List.getD_eq_getElem?_getD, h168]
  unfold packLane64
  rw [show (keccakLastBlock 168 0x1f#8 (rowSeeds rho row c)).getD (8 * k) 0#8 =
        (keccakLastBlock 168 0x1f#8 (rowSeeds rho row c)).getD (8 * k + 0) 0#8 by simp,
      hget 0 (by decide), hget 1 (by decide), hget 2 (by decide), hget 3 (by decide),
      hget 4 (by decide), hget 5 (by decide), hget 6 (by decide), hget 7 (by decide), Nat.add_zero]

inductive KProgStep where
  | range (w count : Nat)
  | loop (isPair : Bool) (wHead nBody : Nat) (rCnt : BitVec 5) (slots : List KSlot)
      (expLo expHi : List KExpr) (baseOut : Nat)
  deriving Repr

@[expose] def validSpecVar (initBnd : Nat) (bases : List Nat) (id : Nat) : Bool :=
  Nat.blt id initBnd || bases.any (fun b => Nat.ble b id && Nat.blt id (b + 50))

@[expose] def exprVarsOk (ok : Nat → Bool) : KExpr → Bool
  | .var id => ok id
  | .const64 _ | .spAdd _ | .rcAdd _ | .rcVal _
  | .rcLoopOff | .rcLoopPtr | .rcLoopNext | .rcLoopVal => true
  | .xor a b | .bic a b | .and64 a b | .or64 a b | .add64 a b | .insByte0 a b =>
      exprVarsOk ok a && exprVarsOk ok b
  | .bsl x y z => exprVarsOk ok x && exprVarsOk ok y && exprVarsOk ok z
  | .shl a _ | .ushr a _ | .rotl a _ | .clamp64 a => exprVarsOk ok a

theorem evalKExpr_congr_ok {ok : Nat → Bool} {env1 env2 : KEnv}
    (hsp : env1.sp = env2.sp) (hrc : env1.rcBase = env2.rcBase) (hrl : env1.rLoop = env2.rLoop)
    (hvars : ∀ id, ok id = true → env1.vars id = env2.vars id) :
    ∀ (e : KExpr), exprVarsOk ok e = true → evalKExpr env1 e = evalKExpr env2 e
  | .var id, h => hvars id h
  | .const64 _, _ | .rcVal _, _ => rfl
  | .spAdd _, _ => by simp [evalKExpr, hsp]
  | .rcAdd _, _ => by simp [evalKExpr, hrc]
  | .rcLoopOff, _ | .rcLoopNext, _ | .rcLoopVal, _ => by simp [evalKExpr, hrl]
  | .rcLoopPtr, _ => by simp [evalKExpr, hrc, hrl]
  | .xor a b, h | .bic a b, h | .and64 a b, h | .or64 a b, h | .add64 a b, h | .insByte0 a b, h => by
      simp only [exprVarsOk, Bool.and_eq_true] at h
      simp [evalKExpr, evalKExpr_congr_ok hsp hrc hrl hvars a h.1,
        evalKExpr_congr_ok hsp hrc hrl hvars b h.2]
  | .bsl x y z, h => by
      simp only [exprVarsOk, Bool.and_eq_true] at h
      simp [evalKExpr, evalKExpr_congr_ok hsp hrc hrl hvars x h.1.1,
        evalKExpr_congr_ok hsp hrc hrl hvars y h.1.2, evalKExpr_congr_ok hsp hrc hrl hvars z h.2]
  | .shl a _, h | .ushr a _, h | .rotl a _, h | .clamp64 a, h => by
      simp [evalKExpr, evalKExpr_congr_ok hsp hrc hrl hvars a h]

@[expose] def evalExprList25 (env : KEnv) (es : List KExpr) : KeccakState :=
  Array.ofFn fun idx : Fin 25 => evalKExpr env (es.getD idx.1 (.const64 0#64))

@[expose] def extendLoopVars (env : KEnv) (baseOut : Nat) (sLo sHi : KeccakState) : KEnv :=
  { env with
    vars := fun id =>
      if id < baseOut then env.vars id
      else if id < baseOut + 25 then (keccakF1600 sLo).getD (id - baseOut) 0#64
      else if id < baseOut + 50 then (keccakF1600 sHi).getD (id - (baseOut + 25)) 0#64
      else env.vars id }

@[expose] def specEnvSteps : KEnv → List KProgStep → KEnv
  | env, [] => env
  | env, .range _ _ :: rest => specEnvSteps env rest
  | env, .loop _ _ _ _ _ expLo expHi baseOut :: rest =>
      specEnvSteps (extendLoopVars env baseOut (evalExprList25 env expLo) (evalExprList25 env expHi)) rest

@[expose] def progBasesAux (acc : List Nat) : List KProgStep → List Nat
  | [] => acc
  | .range _ _ :: rest => progBasesAux acc rest
  | .loop _ _ _ _ _ _ _ baseOut :: rest => progBasesAux (baseOut :: acc) rest

@[expose] def progBases (steps : List KProgStep) : List Nat := progBasesAux [] steps

@[expose] def checkLoopInputs (cfg : KCfg) (ok : Nat → Bool) (st : KState)
    (slots : List KSlot) (expLo expHi : List KExpr) : Bool :=
  (List.range 25).all fun idx =>
    let p := readSlot cfg st (slots.getD idx (.vreg 0))
    let eLo := expLo.getD idx (.const64 0#64)
    let eHi := expHi.getD idx (.const64 0#64)
    p.1.beq eLo && p.2.beq eHi && exprVarsOk ok eLo && exprVarsOk ok eHi

@[expose] def runKProgSteps (cfg : KCfg) (wLo wHi initBnd : Nat) :
    Nat → List Nat → List KProgStep → KState → Option (Nat × List Nat × KState)
  | wCur, bases, [], st => some (wCur, bases, st)
  | wCur, bases, .range w count :: rest, st =>
      if Nat.beq wCur w && Nat.ble wLo w && Nat.ble (w + count) wHi then
        match runKRange cfg w count st with
        | none => none
        | some st' => runKProgSteps cfg wLo wHi initBnd (w + count) bases rest st'
      else none
  | wCur, bases, .loop isPair wHead nBody rCnt slots expLo expHi baseOut :: rest, st =>
      if Nat.beq wCur wHead && Nat.ble initBnd baseOut &&
         bases.all (fun b => Nat.ble (b + 658) baseOut) &&
         checkLoopInputs cfg (validSpecVar initBnd bases) st slots expLo expHi then
        match stepKLoopSym cfg isPair wHead nBody rCnt slots baseOut st with
        | none => none
        | some st' =>
            runKProgSteps cfg wLo wHi initBnd (wHead + nBody + 1) (baseOut :: bases) rest st'
      else none

@[expose] def runAndCheckKProg (cfg : KCfg) (wLo wHi wStart wEnd initBnd : Nat)
    (steps : List KProgStep) (st0 : KState) (chk : (Nat → Bool) → KState → Bool) : Bool :=
  Nat.ble 330 wLo && Nat.ble wHi 3237 &&
  match runKProgSteps cfg wLo wHi initBnd wStart [] steps st0 with
  | none => false
  | some (wFinal, finalBases, stEnd) =>
      Nat.beq wFinal wEnd && chk (validSpecVar initBnd finalBases) stEnd

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Init
