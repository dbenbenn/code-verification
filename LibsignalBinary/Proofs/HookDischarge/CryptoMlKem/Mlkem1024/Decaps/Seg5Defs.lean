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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkInstrs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.SiteStep -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymBridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakLoop -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Defs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymBridge -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkWords
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1bPure

/-!
# `kyber_decapsulate` (`B06`) — Segment 5 Configurations, Sites, and Row States

Configurations (`cfgA06..cfgD06`, `cfgClamp06`), rejection-sampling site certificates
(`rejCfgInit3_06`, `rejCfgExtra1_06`), and row loop states (`RowExtraState06`, `RowMidState06`,
`RowExitState06`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Defs

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (
  mlkemData01Bytes mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemPlacement mlkemCall_of_blockOk mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (
  mlkemMemcpySpec mlkemMemsetSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps (
  blk28_memcpy_ok blk29_memset_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak (
  keccakAbsorb keccakPermuteN)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (shake128BlockAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem (
  MultiLaneSampled MultiLaneSlots)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkInstrs (
  FetchesInstrsAt pcAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkWords (
  checkWordsAtTree fetchesInstrsAt_of_wordTree rejInnerInstrs rejInnerWords)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.SiteStep (
  RejSiteConfig rejOuterInstrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework (
  MultiLaneRawXofInv MultiLaneXofInv allLanesDone)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base (
  blk06_code_eq blk06_tree_size blkLib06 blkPC06 blkPlaceable06 blkTree06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs (
  fetchWordTree06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymBridge (
  blk06NoRelocInRange fetch_blk06_range)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1bPure (rhoW)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymDefs (
  BTree KCfg)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymBridge (
  BTreeMem KCfgValid btreeBytesFrom)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakLoop (slotHolds)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Base (rowSeed)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Defs (
  slotsInv01 slotsInv23 slotsMidExtra01 slotsMidExtra23)

/-! ## 1. `B28`/`B29` Call Specs & `KCfg` Instances on `B06` -/

theorem blk28_memcpy_06 [MlKemPlacement] (b : BitVec 64) :
    subroutine_ok (blkPC06.rebase b (fun _ => none)) (mlkemMpl.base 28)
      (mlkemMultiLib.withCodeLoaded mlkemMpl mlkemMemcpySpec) :=
  mlkemCall_of_blockOk (blkPC06.rebase b (fun _ => none)) blk28_memcpy_ok

theorem blk29_memset_06 [MlKemPlacement] (b : BitVec 64) :
    subroutine_ok (blkPC06.rebase b (fun _ => none)) (mlkemMpl.base 29)
      (mlkemMultiLib.withCodeLoaded mlkemMpl mlkemMemsetSpec) :=
  mlkemCall_of_blockOk (blkPC06.rebase b (fun _ => none)) blk29_memset_ok

@[expose] def cfgA06 : KCfg := { offA := 144, lenA := 286, offB := 30448, lenB := 0 }
@[expose] def cfgB06 : KCfg := { offA := 144, lenA := 286, offB := 30448, lenB := 252 }
@[expose] def cfgC06 : KCfg := { offA := 144, lenA := 286, offB := 28368, lenB := 84 }
@[expose] def cfgD06 : KCfg := { offA := 4160, lenA := 272, offB := 28368, lenB := 0 }
@[expose] def cfgClamp06 : KCfg := { offA := 144, lenA := 286, offB := 26320, lenB := 4 }

theorem cfgA06_valid : KCfgValid cfgA06 := by decide
theorem cfgB06_valid : KCfgValid cfgB06 := by decide
theorem cfgC06_valid : KCfgValid cfgC06 := by decide
theorem cfgD06_valid : KCfgValid cfgD06 := by decide
theorem cfgClamp06_valid : KCfgValid cfgClamp06 := by decide

/-! ## 2. Instruction-List Fetch Bridge & `RejSiteConfig` Certificates on `B06` -/

@[expose] def checkInstrsAt06 (wStart : Nat) : List Instr → Bool
  | [] => true
  | inst :: rest => (fetchWordTree06 wStart == some inst) && checkInstrsAt06 (wStart + 1) rest

theorem checkInstrsAt06_get? :
    ∀ {instrs : List Instr} {wStart k : Nat} {inst : Instr},
      checkInstrsAt06 wStart instrs = true →
      instrs[k]? = some inst →
      fetchWordTree06 (wStart + k) = some inst
  | [], _, _, _, _, hk => by simp at hk
  | _ :: _, _, 0, _, hc, hk => by
      simp only [checkInstrsAt06, Bool.and_eq_true] at hc
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk; exact beq_iff_eq.mp hc.1
  | _ :: _, wStart, k + 1, _, hc, hk => by
      simp only [checkInstrsAt06, Bool.and_eq_true] at hc
      simp only [List.getElem?_cons_succ] at hk
      simpa [Nat.add_right_comm, Nat.add_assoc] using checkInstrsAt06_get? hc.2 hk

theorem fetchesInstrsAt_blk06_range [MlKemPlacement] {b : BitVec 64}
    {wSite baseIdx wHi : Nat} {instrs : List Instr}
    (hnr : blk06NoRelocInRange (wSite + baseIdx) wHi = true)
    (hmax : wHi ≤ 13979)
    (hlen : wSite + baseIdx + instrs.length ≤ wHi)
    (hc : checkInstrsAt06 (wSite + baseIdx) instrs = true) :
    FetchesInstrsAt (blkPC06.rebase b (fun _ => none))
      (b + BitVec.ofNat 64 (4 * wSite)) baseIdx instrs := by
  intro k inst hk
  have hk_lt : k < instrs.length := by
    by_contra hge
    simp [List.getElem?_eq_none (Nat.le_of_not_lt hge)] at hk
  have hfw := checkInstrsAt06_get? hc hk
  have hpc : pcAt (b + BitVec.ofNat 64 (4 * wSite)) (baseIdx + k) =
      b + BitVec.ofNat 64 (4 * (wSite + baseIdx + k)) := by
    unfold pcAt; rw [BitVec.add_assoc]; congr 1; rw [← BitVec.ofNat_add]; congr 1; omega
  rw [hpc]
  exact fetch_blk06_range hnr hmax (by omega) (by omega) (by simpa [Nat.add_assoc] using hfw)

@[expose] def rejCfgInit3_06 : RejSiteConfig :=
  { v := .varB, nLanes := 4, nChunks := 21, slotStride := 544,
    rIdx := .x8, rSqPtr := .x9, rPrevIdx := .x10,
    rSampArr := .x23, rSlotStride := .x19, rSlotsBase := .x22 }

@[expose] def rejCfgExtra1_06 : RejSiteConfig :=
  { v := .varC, nLanes := 4, nChunks := 7, slotStride := 544,
    rIdx := .x10, rSqPtr := .x8, rPrevIdx := .x9,
    rSampArr := .x23, rSlotStride := .x19, rSlotsBase := .x22 }

theorem rejCfgInit3_06_valid : rejCfgInit3_06.Valid := by decide
theorem rejCfgExtra1_06_valid : rejCfgExtra1_06.Valid := by decide

private theorem chk_rejInit3_06_outer :
    checkInstrsAt06 6104 (rejOuterInstrs rejCfgInit3_06) = true := by decide +kernel
private theorem chk_rejInit3_06_inner :
    checkWordsAtTree blkTree06 blkLib06 (4 * 6104 + 44) (rejInnerWords .varB) = true := by
  decide +kernel
private theorem chk_rejExtra1_06_outer :
    checkInstrsAt06 6976 (rejOuterInstrs rejCfgExtra1_06) = true := by decide +kernel
private theorem chk_rejExtra1_06_inner :
    checkWordsAtTree blkTree06 blkLib06 (4 * 6976 + 44) (rejInnerWords .varC) = true := by
  decide +kernel

theorem fetches_rejInit3_06_outer [MlKemPlacement] (b : BitVec 64) :
    FetchesInstrsAt (blkPC06.rebase b (fun _ => none))
      (b + BitVec.ofNat 64 (4 * 6104)) 0 (rejOuterInstrs rejCfgInit3_06) :=
  fetchesInstrsAt_blk06_range (b := b) (wSite := 6104) (baseIdx := 0) (wHi := 6117)
    (by decide +kernel) (by decide) (by decide) chk_rejInit3_06_outer

theorem fetches_rejInit3_06_inner [MlKemPlacement] (b : BitVec 64) :
    FetchesInstrsAt (blkPC06.rebase b (fun _ => none))
      (b + BitVec.ofNat 64 (4 * 6104)) 11 (rejInnerInstrs .varB) :=
  fetchesInstrsAt_of_wordTree blk06_code_eq blk06_tree_size blkPlaceable06
    (siteOff := 4 * 6104) (b := b) (X := fun _ => none) (v := .varB)
    (by decide) (by decide) (by decide) chk_rejInit3_06_inner

theorem fetches_rejExtra1_06_outer [MlKemPlacement] (b : BitVec 64) :
    FetchesInstrsAt (blkPC06.rebase b (fun _ => none))
      (b + BitVec.ofNat 64 (4 * 6976)) 0 (rejOuterInstrs rejCfgExtra1_06) :=
  fetchesInstrsAt_blk06_range (b := b) (wSite := 6976) (baseIdx := 0) (wHi := 6989)
    (by decide +kernel) (by decide) (by decide) chk_rejExtra1_06_outer

theorem fetches_rejExtra1_06_inner [MlKemPlacement] (b : BitVec 64) :
    FetchesInstrsAt (blkPC06.rebase b (fun _ => none))
      (b + BitVec.ofNat 64 (4 * 6976)) 11 (rejInnerInstrs .varC) :=
  fetchesInstrsAt_of_wordTree blk06_code_eq blk06_tree_size blkPlaceable06
    (siteOff := 4 * 6976) (b := b) (X := fun _ => none) (v := .varC)
    (by decide) (by decide) (by decide) chk_rejExtra1_06_inner

/-! ## 3. Row Header, Callee GPRs, & Row Loop States on `B06` -/

@[expose] def MemAHeaderOk06 (sp : BitVec 64) (rho : List (BitVec 8))
    (tA : BTree (BitVec 64) 9) : Prop :=
  tA.get 0 = 0x00000000001f0300#64 ∧
  tA.get 1 = 0#64 ∧
  tA.get 2 = 0x00000000001f0200#64 ∧
  tA.get 3 = 0#64 ∧
  tA.get 4 = 0x00000000001f0100#64 ∧
  tA.get 5 = 0#64 ∧
  tA.get 7 = sp + 28379#64 ∧
  tA.get 8 = sp + 30459#64 ∧
  tA.get 9 = sp + 30712#64 ∧
  tA.get 14 = 0xffffffffff0000ff#64 ∧
  tA.get 15 = 0xffffffffffffffff#64 ∧
  tA.get 16 = rhoW rho 3 ∧
  tA.get 17 = rhoW rho 3 ∧
  tA.get 18 = rhoW rho 2 ∧
  tA.get 19 = rhoW rho 2 ∧
  tA.get 20 = rhoW rho 1 ∧
  tA.get 21 = rhoW rho 1 ∧
  tA.get 22 = rhoW rho 0 ∧
  tA.get 23 = rhoW rho 0

@[expose] def RowCalleeGprs06 (sp rcBase fpVal : BitVec 64) (row : Nat) (s : State) : Prop :=
  s.readReg64 .x19 = 544#64 ∧
  s.readReg64 .x20 = sp + 28379#64 ∧
  s.readReg64 .x21 = BitVec.ofNat 64 row ∧
  s.readReg64 .x22 = sp + 4160#64 ∧
  s.readReg64 .x23 = sp + 26320#64 ∧
  s.readReg64 .x24 = 256#64 ∧
  s.readReg64 .x25 = sp + 28368#64 ∧
  s.readReg64 .x26 = sp + 28632#64 ∧
  s.readReg64 .x28 = rcBase ∧
  s.readReg64 .fp = fpVal

@[expose] def RowExtraState06 [MlKemPlacement] (b sp rcBase fpVal : BitVec 64)
    (rho : List (BitVec 8)) (row : Nat) (Rest : SepProp)
    (extra : Nat) (st : State) (P : SepProp) : Prop :=
  st.pc = b + BitVec.ofNat 64 (4 * 6354) ∧
  st.status = .Running ∧
  st.sp = sp ∧
  st.spAligned = true ∧
  (sp &&& 15#64 == 0#64) = true ∧
  mlkemMultiLib.CodeLoaded mlkemMpl st.mem ∧
  MlKemRoOk mlkemMpl st.mem ∧
  RowCalleeGprs06 sp rcBase fpVal row st ∧
  st.readReg64 .x1 = BitVec.ofNat 64 (row + 1) ∧
  ∃ (tA : BTree (BitVec 64) 9) (sampled : Nat → Nat) (hws : Nat → List (BitVec 16)),
    MemAHeaderOk06 sp rho tA ∧
    (∀ idx, idx < 25 →
      slotHolds cfgC06 st tA (slotsInv01.getD idx (.vreg 0))
        ((keccakPermuteN (extra + 2) (keccakAbsorb 21 0x1f#8 (rowSeed rho row 0))).getD idx 0#64)
        ((keccakPermuteN (extra + 2) (keccakAbsorb 21 0x1f#8 (rowSeed rho row 1))).getD idx 0#64)) ∧
    (∀ idx, idx < 25 →
      slotHolds cfgC06 st tA (slotsInv23.getD idx (.vreg 0))
        ((keccakPermuteN (extra + 2) (keccakAbsorb 21 0x1f#8 (rowSeed rho row 2))).getD idx 0#64)
        ((keccakPermuteN (extra + 2) (keccakAbsorb 21 0x1f#8 (rowSeed rho row 3))).getD idx 0#64)) ∧
    MultiLaneXofInv 4 (fun c => rowSeed rho row c) extra sampled hws ∧
    (P ⊢ (rcBase ↦ᵣ mlkemData01Bytes) ∗
      BTreeMem (sp + 144#64) 286 tA ∗
      MultiLaneSampled (sp + 26320#64) 4 sampled ∗
      MultiLaneSlots (sp + 4160#64) 544 4 hws ∗
      memRegion (sp + 28368#64) 672 ∗
      memRegion (sp + 30448#64) 2016 ∗
      Rest)

@[expose] def RowMidState06 [MlKemPlacement] (sp rcBase fpVal : BitVec 64)
    (rho : List (BitVec 8)) (row : Nat) (Rest : SepProp)
    (extra : Nat) (sm : State) (Pm : SepProp) : Prop :=
  sm.sp = sp ∧
  sm.spAligned = true ∧
  (sp &&& 15#64 == 0#64) = true ∧
  mlkemMultiLib.CodeLoaded mlkemMpl sm.mem ∧
  MlKemRoOk mlkemMpl sm.mem ∧
  RowCalleeGprs06 sp rcBase fpVal row sm ∧
  sm.readReg64 .x1 = BitVec.ofNat 64 (row + 1) ∧
  sm.readReg64 .x10 = 0#64 ∧
  sm.readReg64 .x8 = sp + 28379#64 ∧
  ∃ (tA tB : BTree (BitVec 64) 9) (sampled : Nat → Nat) (hws : Nat → List (BitVec 16)),
    MemAHeaderOk06 sp rho tA ∧
    (∀ c, c < 4 → btreeBytesFrom (21 * c) 21 tB = shake128BlockAt (rowSeed rho row c) (extra + 3)) ∧
    (∀ idx, idx < 25 →
      slotHolds cfgC06 sm tA (slotsMidExtra01.getD idx (.vreg 0))
        ((keccakPermuteN (extra + 3) (keccakAbsorb 21 0x1f#8 (rowSeed rho row 0))).getD idx 0#64)
        ((keccakPermuteN (extra + 3) (keccakAbsorb 21 0x1f#8 (rowSeed rho row 1))).getD idx 0#64)) ∧
    (∀ idx, idx < 25 →
      slotHolds cfgC06 sm tA (slotsMidExtra23.getD idx (.vreg 0))
        ((keccakPermuteN (extra + 3) (keccakAbsorb 21 0x1f#8 (rowSeed rho row 2))).getD idx 0#64)
        ((keccakPermuteN (extra + 3) (keccakAbsorb 21 0x1f#8 (rowSeed rho row 3))).getD idx 0#64)) ∧
    MultiLaneRawXofInv 4 (fun c => rowSeed rho row c) extra sampled hws ∧
    (Pm ⊢ (rcBase ↦ᵣ mlkemData01Bytes) ∗
      BTreeMem (sp + 144#64) 286 tA ∗
      BTreeMem (sp + 28368#64) 84 tB ∗
      MultiLaneSampled (sp + 26320#64) 4 sampled ∗
      MultiLaneSlots (sp + 4160#64) 544 4 hws ∗
      memRegion (sp + 30448#64) 2016 ∗
      Rest)

@[expose] def RowExitState06 [MlKemPlacement] (sp rcBase fpVal : BitVec 64)
    (rho : List (BitVec 8)) (row : Nat) (Rest : SepProp)
    (sf : State) (Pf : SepProp) : Prop :=
  sf.sp = sp ∧
  sf.spAligned = true ∧
  (sp &&& 15#64 == 0#64) = true ∧
  mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧
  MlKemRoOk mlkemMpl sf.mem ∧
  RowCalleeGprs06 sp rcBase fpVal row sf ∧
  sf.readReg64 .x1 = BitVec.ofNat 64 (row + 1) ∧
  ∃ (extra : Nat) (tA : BTree (BitVec 64) 9)
    (sampled : Nat → Nat) (hws : Nat → List (BitVec 16)),
    MemAHeaderOk06 sp rho tA ∧
    MultiLaneXofInv 4 (fun c => rowSeed rho row c) extra sampled hws ∧
    allLanesDone 4 (fun c => rowSeed rho row c) extra = true ∧
    (Pf ⊢ (rcBase ↦ᵣ mlkemData01Bytes) ∗
      BTreeMem (sp + 144#64) 286 tA ∗
      MultiLaneSampled (sp + 26320#64) 4 sampled ∗
      MultiLaneSlots (sp + 4160#64) 544 4 hws ∗
      memRegion (sp + 28368#64) 672 ∗
      memRegion (sp + 30448#64) 2016 ∗
      Rest)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Defs
