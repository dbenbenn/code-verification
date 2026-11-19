/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import Arm64.Trusted.Spec.SepLogic
public import ProofLib.Placed.Multi
public import ProofLib.Placed.OpcodeExclusion
public import LibsignalBinary.Heap.SpecBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.ConsumerBridgesBase -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4ActiveLocality -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.RustStd.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemPlaceable -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.OpcodeSafety
import ProofLib.MallocngBridge
import ProofLib.SepLogic.HeapIntro
import ProofLib.SepLogic.Model

/-!
# Active-Block Two-Window Phantom Relocation for `mlkemMultiLib` (`ElfSampleNttStuckDivergeMlKemLocality`)

Relocates the 5 `SampleNTT` entrypoint wrapper blocks `mlkemS5Blocks := [10, 19, 22, 23, 24]`
(`260` bytes total) of `mlkemMultiLib` into two disjoint 64 KiB phantom windows inside
`[0x01000000, 0x01100000)` while keeping all 27 remaining blocks `mlkemActiveBlocks` and all 11
`.rodata` tables fixed at `mpl`. Cancelling phantom accesses via `AgreeOutsideDisjoint` upgrades any
`MlKemBlockOk j` (`j ∈ mlkemActiveBlocks`) execution to an explicit `h2fsgen_StepsVisitedIn
(mlkemActiveKeep mpl) emptyStdProg s0 sf` run that strictly avoids all 5 `SampleNTT` entrypoints.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeMlKemLocality

open Arm64 Arm64.Obj ProofLib SepProp
open LibsignalBinary.Heap (FdsHiFrame PoolPreserved VmPreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.ConsumerBridgesBase (
  externAt?_mlkemBlockProgram_ext_none withMlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.OpcodeSafety (
  mlkemMultiLib_blocks_all_externs_empty mlkemMultiLib_blocks_all_msr mlkemMultiLib_blocks_all_svc0)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBlockOk MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (
  mlkemData00Bytes mlkemData01Bytes mlkemData02Bytes mlkemData03Bytes mlkemData04Bytes
  mlkemData05Bytes mlkemData06Bytes mlkemData07Bytes mlkemData08Bytes mlkemData09Bytes
  mlkemData10Bytes mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (
  MlKemRoOk mlkemData00Bytes_length mlkemData01Bytes_length mlkemData02Bytes_length
  mlkemData03Bytes_length mlkemData04Bytes_length mlkemData05Bytes_length mlkemData06Bytes_length
  mlkemData07Bytes_length mlkemData08Bytes_length mlkemData09Bytes_length mlkemData10Bytes_length)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4ActiveLocality (
  AgreeOutsideDisjoint AgreeState AgreeStep AllInDom BoundedHeapIntervals RwOnlyHeap
  phantomWindowBase phantomWindowLen)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (RoDataAt SpecSimulates)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemPlaceable (
  c2MlkemKeep c2MlkemMpl c2_mlkem_placeable)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK (emptyStdProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric (
  h2fsgen_StepsVisitedIn)

/-! ## 1. Block Partition, `extendMlkemMpl`, & `MlKemActivePlaceable` -/

/-- The 5 `SampleNTT` entrypoint wrapper blocks of `mlkemMultiLib` (`B10, B19, B22, B23, B24`). -/
@[expose] def mlkemS5Blocks : List Nat := [10, 19, 22, 23, 24]

/-- The 27 remaining blocks of `mlkemMultiLib` (all cores, helpers, `B20`, `B21`, and `musl`
    `memcpy`/`memset`/`bcmp`/`memcmp`). -/
@[expose] def mlkemActiveBlocks : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 25, 26, 27, 28, 29, 30, 31]

/-- Execute-keep mask covering the 27 blocks in `mlkemActiveBlocks`. -/
@[expose] def mlkemActiveKeep (mpl : MultiPlacement) (a : BitVec 64) : Bool :=
  mlkemActiveBlocks.any fun k => ProofLib.progKeep (mlkemMultiLib.blockProgram mpl k) a

/-- Per-block `CodeLoaded` over `mlkemActiveBlocks`. -/
@[expose] def MlKemActiveCodeLoaded (mpl : MultiPlacement) (m : Memory) : Prop :=
  ∀ j ∈ mlkemActiveBlocks, (mlkemMultiLib.blockProgram mpl j).CodeLoaded m

theorem mlkemActiveCodeLoaded_of_codeLoaded {mpl : MultiPlacement} {m : Memory}
    (hcl : mlkemMultiLib.CodeLoaded mpl m) : MlKemActiveCodeLoaded mpl m := by
  have hall : (mlkemActiveBlocks.all (· < mlkemMultiLib.blocks.length)) = true := by decide
  exact fun j hj => hcl j (List.all_eq_true.mp hall j hj |> of_decide_eq_true)

theorem mlkemActiveKeep_sub_c2MlkemKeep {mpl : MultiPlacement} {a : BitVec 64}
    (hk : mlkemActiveKeep mpl a = true) : c2MlkemKeep mpl a = true := by
  have hall : (mlkemActiveBlocks.all (· < mlkemMultiLib.blocks.length)) = true := by decide
  unfold mlkemActiveKeep at hk; rw [List.any_eq_true] at hk
  obtain ⟨j, hj, hpk⟩ := hk
  unfold c2MlkemKeep; rw [List.any_eq_true]
  exact ⟨j, List.mem_range.mpr (of_decide_eq_true (List.all_eq_true.mp hall j hj)), hpk⟩

private theorem mlkemActiveKeep_of_block_offset (mpl : MultiPlacement) {j k : Nat}
    (hj : j ∈ mlkemActiveBlocks)
    (hno : (mlkemMultiLib.blockProgram mpl j).base.toNat +
      (mlkemMultiLib.blockProgram mpl j).code.length ≤ 2 ^ 64)
    (hk : k < (mlkemMultiLib.blockProgram mpl j).code.length) :
    mlkemActiveKeep mpl ((mlkemMultiLib.blockProgram mpl j).base + BitVec.ofNat 64 k) = true := by
  let Pj := mlkemMultiLib.blockProgram mpl j
  have hsub : Pj.base + BitVec.ofNat 64 k - Pj.base = BitVec.ofNat 64 k := by bv_omega
  have hin : (Pj.base + BitVec.ofNat 64 k - Pj.base).toNat < Pj.code.length := by
    rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hk
  unfold mlkemActiveKeep; rw [List.any_eq_true]; exact ⟨j, hj, decide_eq_true hin⟩

@[expose] def s5BlockOff : Nat → Option Nat
  | 10 => some 0x0
  | 19 => some 0x400
  | 22 => some 0x800
  | 23 => some 0xc00
  | 24 => some 0x1000
  | _  => none

@[expose] def extendMlkemMpl (mpl : MultiPlacement) (t : Nat) : MultiPlacement where
  base i := match s5BlockOff i with
    | some off => phantomWindowBase t + BitVec.ofNat 64 off
    | none => mpl.base i
  ρ := mpl.ρ
  relax i := match s5BlockOff i with | some _ => fun _ => false | none => mpl.relax i
  b2b i := match s5BlockOff i with | some _ => fun _ => false | none => mpl.b2b i
  undefWeak := mpl.undefWeak

@[expose] def mlkemRoRegions (mpl : MultiPlacement) : List (BitVec 64 × Nat) :=
  [(mpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", 256),
   (mpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29", 192),
   (mpl.ρ "libcrux_ml_kem:.rodata.cst16.0", 16),
   (mpl.ρ "libcrux_ml_kem:.rodata.cst16.1", 16),
   (mpl.ρ "libcrux_ml_kem:.rodata.cst16.2", 16),
   (mpl.ρ "libcrux_ml_kem:.rodata.cst16.3", 16),
   (mpl.ρ "libcrux_ml_kem:.rodata.cst16.4", 16),
   (mpl.ρ "libcrux_ml_kem:.rodata.cst16.5", 16),
   (mpl.ρ "libcrux_ml_kem:.rodata.cst16.6", 16),
   (mpl.ρ "libcrux_ml_kem:.rodata.cst16.7", 16),
   (mpl.ρ "libcrux_ml_kem:.rodata.cst16.8", 16)]

@[expose] def mlkemRoKeep (mpl : MultiPlacement) (a : BitVec 64) : Bool :=
  (mlkemRoRegions mpl).any fun p => decide (InRegion p.1 p.2 a)

@[expose] def mlkemActiveDom (mpl : MultiPlacement) (a : BitVec 64) : Bool :=
  mlkemActiveKeep mpl a || mlkemRoKeep mpl a

structure MlKemActivePlaceable (mpl : MultiPlacement) : Prop where
  placeable_ext : ∀ t ∈ List.range 8, mlkemMultiLib.Placeable (extendMlkemMpl mpl t)
  active_blocks_disj : ∀ j ∈ mlkemActiveBlocks,
    RangesDisjoint (mpl.base j).toNat (mlkemMultiLib.blockLib j).text.code.length
      0x01000000 0x100000
  active_ro_disj : ∀ p ∈ mlkemRoRegions mpl,
    RangesDisjoint p.1.toNat p.2 0x01000000 0x100000

@[expose] def mlkemActiveInvMem (mpl : MultiPlacement) (m : Memory) : Prop :=
  MlKemActivePlaceable mpl ∧ MlKemActiveCodeLoaded mpl m ∧ MlKemRoOk mpl m

private def symUnchangedByExtend (sym : String) : Bool :=
  match lookupBlockSym sym mlkemMultiLib.blocks with
  | some (i, _) => (s5BlockOff i).isNone
  | none => true

private theorem mlkemActiveBlocks_relocs_unchanged :
    (mlkemActiveBlocks.all fun j =>
      (s5BlockOff j).isNone &&
      (mlkemMultiLib.blockLib j).text.externs.isEmpty &&
      ((mlkemMultiLib.blockLib j).text.relocs.all fun r => symUnchangedByExtend r.sym)) = true := by
  decide +kernel

private theorem resolve_extendMlkemMpl_eq_of_unchanged (mpl : MultiPlacement) (t : Nat)
    {sym : String} (hu : symUnchangedByExtend sym = true) :
    mlkemMultiLib.resolve (extendMlkemMpl mpl t) sym = mlkemMultiLib.resolve mpl sym := by
  unfold symUnchangedByExtend at hu; unfold MultiPlacedLib.resolve
  cases hl : lookupBlockSym sym mlkemMultiLib.blocks with
  | some p =>
    rcases p with ⟨i, off⟩; rw [hl] at hu
    cases hio : s5BlockOff i with
    | none => simp [extendMlkemMpl, hio]
    | some _ => simp [hio] at hu
  | none => simp [extendMlkemMpl]

private theorem relocTarget_eq_of_relocs_eq (blk : CodeBlock) {pl₁ pl₂ : Placement}
    (hbase : pl₁.base = pl₂.base) (hb2b : pl₁.b2b = pl₂.b2b)
    (hrho : ∀ r ∈ blk.relocs, pl₁.ρ r.sym = pl₂.ρ r.sym) :
    (∀ r ∈ blk.relocs, blk.target pl₁ r = blk.target pl₂ r) ∧
    (∀ off r, r ∈ blk.relocs → blk.relocTarget pl₁ off r = blk.relocTarget pl₂ off r) := by
  have htgt : ∀ r ∈ blk.relocs, blk.target pl₁ r = blk.target pl₂ r := fun r hr => by
    unfold CodeBlock.target CodeBlock.resolve
    cases lookup r.sym blk.symbols <;> simp [hbase, hrho r hr]
  refine ⟨htgt, fun off r hr => ?_⟩
  unfold CodeBlock.relocTarget; rw [hb2b]
  cases hb : (if pl₂.b2b off then blk.b2bNext? r else none) with
  | none => exact htgt r hr
  | some r2 =>
    have hr2 : r2 ∈ blk.relocs := by
      by_cases hc : pl₂.b2b off = true
      · simp only [hc, ↓reduceIte] at hb
        unfold CodeBlock.b2bNext? at hb; dsimp only at hb
        split at hb <;> try cases hb
        split at hb <;> try cases hb
        split at hb <;> try cases hb
        split at hb <;> try cases hb
        split at hb <;> try cases hb
        rename_i hfind _; exact List.mem_of_find?_eq_some hfind
      · simp [hc] at hb
    exact htgt r2 hr2

private theorem patched_eq_of_relocs_eq (blk : CodeBlock) {pl₁ pl₂ : Placement}
    (hbase : pl₁.base = pl₂.base) (hrel : pl₁.relax = pl₂.relax)
    (hb2b : pl₁.b2b = pl₂.b2b) (huw : pl₁.undefWeak = pl₂.undefWeak)
    (hrho : ∀ r ∈ blk.relocs, pl₁.ρ r.sym = pl₂.ρ r.sym) :
    blk.patched pl₁ = blk.patched pl₂ := by
  obtain ⟨htgt, hrt⟩ := relocTarget_eq_of_relocs_eq blk hbase hb2b hrho
  have hword : ∀ off, blk.patchedWord pl₁ off = blk.patchedWord pl₂ off := fun off => by
    unfold CodeBlock.patchedWord
    cases hrel_at : blk.relocAt? off with
    | none => rfl
    | some r =>
      have hr : r ∈ blk.relocs := List.mem_of_find?_eq_some hrel_at
      dsimp only
      simp only [CodeBlock.relaxedAt, CodeBlock.undefWeakBranch, hbase, hrel, huw,
        htgt r hr, hrt off r hr]
      rfl
  unfold CodeBlock.patched
  exact List.flatMap_congr fun j _ => by rw [hword]

private theorem placeable_of_relocs_eq (blk : CodeBlock) {pl₁ pl₂ : Placement}
    (hp : blk.Placeable pl₁)
    (hbase : pl₁.base = pl₂.base) (hrel : pl₁.relax = pl₂.relax)
    (hb2b : pl₁.b2b = pl₂.b2b) (hext : blk.externs = [])
    (hrho : ∀ r ∈ blk.relocs, pl₁.ρ r.sym = pl₂.ρ r.sym) :
    blk.Placeable pl₂ := by
  obtain ⟨htgt, hrt⟩ := relocTarget_eq_of_relocs_eq blk hbase hb2b hrho
  refine ⟨hp.align_pos, hbase ▸ hp.base_aligned, hbase ▸ hp.no_wrap, hp.len_aligned,
    hp.relocs_nodup, fun r hr => ?_, fun off r hrel_at hrat => ?_, hp.symbols_ok,
    fun e he => by rw [hext] at he; cases he⟩
  · obtain ⟨h1, h2, h3⟩ := hp.relocs_ok r hr
    refine ⟨h1, h2, ?_⟩
    unfold CodeBlock.relocInRange at h3 ⊢
    rw [← hbase, ← hrel, ← hrt r.off r hr]
    exact h3
  · rw [CodeBlock.relaxedAt, ← hrel, ← CodeBlock.relaxedAt] at hrel_at
    have hr : r ∈ blk.relocs := List.mem_of_find?_eq_some hrat
    rw [← hbase, ← htgt r hr]
    exact hp.relaxed_ok off r hrel_at hrat

theorem blockProgram_extendMlkemMpl_eq (mpl : MultiPlacement) (t : Nat) {j : Nat}
    (hj : j ∈ mlkemActiveBlocks)
    (externs : String → Option (State → State) := fun _ => none)
    (overrides : String → Option (State → State) := fun _ => none)
    (svc : State → State := Syscall.standard) :
    mlkemMultiLib.blockProgram (extendMlkemMpl mpl t) j externs overrides svc =
      mlkemMultiLib.blockProgram mpl j externs overrides svc := by
  have hall := (List.all_eq_true.mp mlkemActiveBlocks_relocs_unchanged) j hj
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, List.isEmpty_iff, List.all_eq_true] at hall
  rcases hall with ⟨⟨hio, hext⟩, hrels⟩
  unfold MultiPlacedLib.blockProgram PlacedLib.program
  have hbase : (mlkemMultiLib.blockPlacement (extendMlkemMpl mpl t) j).base =
      (mlkemMultiLib.blockPlacement mpl j).base := by
    simp [MultiPlacedLib.blockPlacement, extendMlkemMpl, hio]
  have hpat : (mlkemMultiLib.blockLib j).text.patched
      (mlkemMultiLib.blockPlacement (extendMlkemMpl mpl t) j) =
      (mlkemMultiLib.blockLib j).text.patched (mlkemMultiLib.blockPlacement mpl j) :=
    patched_eq_of_relocs_eq _ hbase
      (by simp [MultiPlacedLib.blockPlacement, extendMlkemMpl, hio])
      (by simp [MultiPlacedLib.blockPlacement, extendMlkemMpl, hio])
      rfl
      (fun r hr => resolve_extendMlkemMpl_eq_of_unchanged mpl t (hrels r hr))
  simp [hbase, hpat, hext]

theorem extendMlkemMpl_base_eq (mpl : MultiPlacement) (t : Nat) {j : Nat}
    (hj : j ∈ mlkemActiveBlocks) :
    (extendMlkemMpl mpl t).base j = mpl.base j := by
  have hall := (List.all_eq_true.mp mlkemActiveBlocks_relocs_unchanged) j hj
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hall
  simp [extendMlkemMpl, hall.1.1]

private theorem block_active_or_s5 :
    ((List.range mlkemMultiLib.blocks.length).all fun j =>
      decide (j ∈ mlkemActiveBlocks ∨ j ∈ mlkemS5Blocks)) = true := by decide +kernel

private theorem c2_extend_s5_blocks_placeable :
    ((List.range 8).all fun t =>
      mlkemS5Blocks.all fun i =>
        match mlkemMultiLib.blocks[i]? with
        | some blk => blk.checkPlaceable (mlkemMultiLib.blockPlacement (extendMlkemMpl c2MlkemMpl t) i)
        | none => false) = true := by
  decide +kernel

private theorem c2_extend_blocks_disjoint :
    ((List.range 8).all fun t =>
      mlkemMultiLib.checkBlocksDisjoint (extendMlkemMpl c2MlkemMpl t)) = true := by
  decide +kernel

private theorem c2_extend_data_placeable :
    ((List.range 8).all fun t =>
      mlkemMultiLib.checkDataPlaceable (extendMlkemMpl c2MlkemMpl t)) = true := by
  decide +kernel

private def checkRangesDisjointB (b1 n1 b2 n2 : Nat) : Bool :=
  Nat.ble (b1 + n1) b2 || Nat.ble (b2 + n2) b1

private theorem rangesDisjoint_of_checkB {b1 n1 b2 n2 : Nat}
    (h : checkRangesDisjointB b1 n1 b2 n2 = true) : RangesDisjoint b1 n1 b2 n2 := by
  unfold checkRangesDisjointB at h; unfold RangesDisjoint
  simp only [Bool.or_eq_true, Nat.ble_eq] at h; exact h

private theorem c2_active_disj_band :
    (mlkemActiveBlocks.all (fun j =>
      checkRangesDisjointB (c2MlkemMpl.base j).toNat
        (mlkemMultiLib.blockLib j).text.code.length 0x01000000 0x100000) &&
    (mlkemRoRegions c2MlkemMpl).all (fun p =>
      checkRangesDisjointB p.1.toNat p.2 0x01000000 0x100000)) = true := by
  decide +kernel

theorem c2_mlkemActivePlaceable : MlKemActivePlaceable c2MlkemMpl := by
  have hd := c2_active_disj_band
  simp only [Bool.and_eq_true, List.all_eq_true] at hd
  refine ⟨fun t ht => ?_, fun j hj => rangesDisjoint_of_checkB (hd.1 j hj),
    fun p hp => rangesDisjoint_of_checkB (hd.2 p hp)⟩
  have hs5 := List.all_eq_true.mp (List.all_eq_true.mp c2_extend_s5_blocks_placeable t ht)
  have hdisj := List.all_eq_true.mp c2_extend_blocks_disjoint t ht
  have hdata := List.all_eq_true.mp c2_extend_data_placeable t ht
  simp only [MultiPlacedLib.checkDataPlaceable, List.all_eq_true, Bool.and_eq_true,
    Option.isNone_iff_eq_none, Nat.blt_eq, Nat.beq_eq, Nat.ble_eq] at hdata
  refine ⟨fun i hi => ?_, fun i j hi hj hij => ?_,
    c2_mlkem_placeable.symbols_nodup, c2_mlkem_placeable.data_nodup,
    fun d hd => ?_, fun d hd r hr => ?_⟩
  · rcases of_decide_eq_true (List.all_eq_true.mp block_active_or_s5 i (List.mem_range.mpr hi))
      with hact | hinact
    · have hall := (List.all_eq_true.mp mlkemActiveBlocks_relocs_unchanged) i hact
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, List.isEmpty_iff,
        List.all_eq_true] at hall
      rcases hall with ⟨⟨hio, hext⟩, hrels⟩
      rw [mlkemMultiLib.blockLib_text hi] at hext hrels
      exact placeable_of_relocs_eq _ (c2_mlkem_placeable.blocks_ok i hi)
        (by simp [MultiPlacedLib.blockPlacement, extendMlkemMpl, hio])
        (by simp [MultiPlacedLib.blockPlacement, extendMlkemMpl, hio])
        (by simp [MultiPlacedLib.blockPlacement, extendMlkemMpl, hio])
        hext
        (fun r hr => (resolve_extendMlkemMpl_eq_of_unchanged c2MlkemMpl t (hrels r hr)).symm)
    · have hchk := hs5 i hinact
      rw [List.getElem?_eq_getElem hi] at hchk
      exact CodeBlock.placeable_of_checkPlaceable hchk
  · have h1 := allIdx_spec hdisj i hi; rw [Nat.zero_add] at h1
    have h2 := allIdx_spec h1 j hj; rw [Nat.zero_add] at h2
    simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, Nat.blt_eq] at h2
    rcases h2 with hnot | hok
    · exact absurd hij hnot
    · exact rangesDisjoint_of_check hok
  · have h := (hdata d hd).1
    exact ⟨h.1.1.1, h.1.1.2, h.1.2, by simpa using h.2⟩
  · have h := (hdata d hd).2 r hr
    simp only [MultiPlacedLib.checkDataReloc, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at h
    obtain ⟨⟨hw, hlen⟩, hk⟩ := h
    refine ⟨hw, hlen, fun h32 => ?_, fun hp32 => ?_⟩
    · rw [h32] at hk; have := Interned.sInRange_iff.1 hk; exact ⟨this.1, this.2⟩
    · rw [hp32] at hk; have := Interned.sInRange_iff.1 hk; exact ⟨this.1, this.2⟩

theorem c2_mlkemActiveInvMem_of_codeLoaded_roOk {m : Memory}
    (hcl : mlkemMultiLib.CodeLoaded c2MlkemMpl m)
    (hro : MlKemRoOk c2MlkemMpl m) :
    mlkemActiveInvMem c2MlkemMpl m :=
  ⟨c2_mlkemActivePlaceable, mlkemActiveCodeLoaded_of_codeLoaded hcl, hro⟩

private theorem c2_active_disjoint_s5 :
    (mlkemActiveBlocks.all fun j =>
      Nat.beq ((mlkemMultiLib.blockLib j).text.code.length % 4) 0 &&
      Nat.ble ((c2MlkemMpl.base j).toNat + (mlkemMultiLib.blockLib j).text.code.length)
        (2 ^ 64) &&
      mlkemS5Blocks.all fun k =>
        checkRangesDisjointB (c2MlkemMpl.base j).toNat
          (mlkemMultiLib.blockLib j).text.code.length
          (c2MlkemMpl.base k).toNat 4) = true := by
  decide +kernel

theorem c2_mlkemActiveKeep_ne_s5Base {a : BitVec 64}
    (hk : mlkemActiveKeep c2MlkemMpl a = true) {k : Nat} (hk_s5 : k ∈ mlkemS5Blocks) :
    a ≠ c2MlkemMpl.base k := by
  intro heq; subst heq
  unfold mlkemActiveKeep at hk; rw [List.any_eq_true] at hk
  obtain ⟨j, hj, hpk⟩ := hk
  have hall := List.all_eq_true.mp c2_active_disjoint_s5 j hj
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, List.all_eq_true] at hall
  rcases hall with ⟨⟨hal, hnw⟩, hdisj_all⟩
  have hdisj := rangesDisjoint_of_checkB (hdisj_all k hk_s5)
  have hplen : (mlkemMultiLib.blockProgram c2MlkemMpl j).code.length =
      (mlkemMultiLib.blockLib j).text.code.length :=
    CodeBlock.length_patched_of_aligned _ hal
  unfold ProofLib.progKeep at hpk
  have hin : (c2MlkemMpl.base k - c2MlkemMpl.base j).toNat <
      (mlkemMultiLib.blockLib j).text.code.length := by
    rw [← hplen]; exact of_decide_eq_true hpk
  unfold RangesDisjoint at hdisj
  bv_omega

/-! ## 2. `AgreeOutsideDisjoint` & Multi-Step `h2fsgen_StepsVisitedIn` Locality -/

private theorem allInDom_add (D : BitVec 64 → Bool) :
    ∀ (a b : Nat) (ea : BitVec 64),
      AllInDom D ea (a + b) ↔ AllInDom D ea a ∧ AllInDom D (ea + BitVec.ofNat 64 a) b
  | 0, b, ea => by
    have h0 : ea + BitVec.ofNat 64 0 = ea := by bv_omega
    simp [AllInDom, h0]
  | a + 1, b, ea => by
    have hstep : ea + 1#64 + BitVec.ofNat 64 a = ea + BitVec.ofNat 64 (a + 1) := by bv_omega
    have hadd : a + 1 + b = (a + b) + 1 := by omega
    rw [hadd]; simp only [AllInDom]
    rw [allInDom_add D a b (ea + 1#64), hstep, and_assoc]

private theorem dom_of_perm_some {D : BitVec 64 → Bool} {m₁ m₂ m : Memory}
    (h : AgreeOutsideDisjoint D m₁ m₂ m) {a : BitVec 64}
    (h1 : m₁.perm a ≠ none) (h2 : m₂.perm a ≠ none) : D a = true := by
  cases hd : D a with
  | true => rfl
  | false => rcases h.2 a hd with hp | hp <;> contradiction

private theorem aod_read8 {D : BitVec 64 → Bool} {m₁ m₂ m : Memory}
    (h : AgreeOutsideDisjoint D m₁ m₂ m) {a : BitVec 64} (hd : D a = true) :
    m₁.read8 a = m.read8 a ∧ m₂.read8 a = m.read8 a := by
  obtain ⟨c1, c2⟩ := h.1 a hd; simp [Memory.read8, c1, c2]

private theorem aod_perm_lf {D : BitVec 64 → Bool} {m₁ m₂ m : Memory}
    (h : AgreeOutsideDisjoint D m₁ m₂ m) {a : BitVec 64} (hd : D a = true) :
    m₁.perm a = m.perm a ∧ m₂.perm a = m.perm a ∧
    m₁.isLazyFree a = m.isLazyFree a ∧ m₂.isLazyFree a = m.isLazyFree a := by
  obtain ⟨c1, c2⟩ := h.1 a hd; simp [Memory.perm, Memory.isLazyFree, c1, c2]


private theorem allInDom_of_allPerm {D : BitVec 64 → Bool} {m₁ m₂ m : Memory}
    (h : AgreeOutsideDisjoint D m₁ m₂ m) {p : Option Perm → Bool} (hnone : p none = false) :
    ∀ (n : Nat) (ea : BitVec 64),
      m₁.allPerm p ea n = true → m₂.allPerm p ea n = true →
      m.allPerm p ea n = true ∧ AllInDom D ea n
  | 0, _, _, _ => ⟨rfl, trivial⟩
  | n + 1, ea, h1, h2 => by
    simp only [Memory.allPerm, Bool.and_eq_true] at h1 h2 ⊢
    have hd : D ea = true := dom_of_perm_some h
      (fun hn => by rw [hn, hnone] at h1; cases h1.1)
      (fun hn => by rw [hn, hnone] at h2; cases h2.1)
    obtain ⟨hp1, _, _, _⟩ := aod_perm_lf h hd
    obtain ⟨hm_rest, hdom_rest⟩ := allInDom_of_allPerm h hnone n (ea + 1#64) h1.2 h2.2
    exact ⟨⟨hp1 ▸ h1.1, hm_rest⟩, hd, hdom_rest⟩

private theorem allNoLazyFree_of_allInDom {D : BitVec 64 → Bool} {m₁ m₂ m : Memory}
    (h : AgreeOutsideDisjoint D m₁ m₂ m) :
    ∀ (n : Nat) (ea : BitVec 64), AllInDom D ea n →
      m₁.allNoLazyFree ea n = true → m.allNoLazyFree ea n = true
  | 0, _, _, _ => rfl
  | n + 1, ea, ⟨hd, hrest⟩, h1 => by
    simp only [Memory.allNoLazyFree, Bool.and_eq_true] at h1 ⊢
    exact ⟨(aod_perm_lf h hd).2.2.1 ▸ h1.1, allNoLazyFree_of_allInDom h n (ea + 1#64) hrest h1.2⟩

private theorem aod_canRead {D : BitVec 64 → Bool} {m₁ m₂ m : Memory}
    (h : AgreeOutsideDisjoint D m₁ m₂ m) {ea : BitVec 64} {n : Nat}
    (h1 : m₁.canRead ea n = true) (h2 : m₂.canRead ea n = true) :
    m.canRead ea n = true ∧ AllInDom D ea n := by
  simp only [Memory.canRead, Bool.and_eq_true] at h1 h2 ⊢
  obtain ⟨hp, hdom⟩ := allInDom_of_allPerm h rfl n ea h1.1 h2.1
  exact ⟨⟨hp, allNoLazyFree_of_allInDom h n ea hdom h1.2⟩, hdom⟩

private theorem aod_canWrite {D : BitVec 64 → Bool} {m₁ m₂ m : Memory}
    (h : AgreeOutsideDisjoint D m₁ m₂ m) {ea : BitVec 64} {n : Nat}
    (h1 : m₁.canWrite ea n = true) (h2 : m₂.canWrite ea n = true) :
    m.canWrite ea n = true ∧ AllInDom D ea n :=
  allInDom_of_allPerm h rfl n ea h1 h2

private theorem aod_canExec {D : BitVec 64 → Bool} {m₁ m₂ m : Memory}
    (h : AgreeOutsideDisjoint D m₁ m₂ m) {ea : BitVec 64} {n : Nat}
    (h1 : m₁.canExec ea n = true) (h2 : m₂.canExec ea n = true) :
    m.canExec ea n = true ∧ AllInDom D ea n :=
  allInDom_of_allPerm h rfl n ea h1 h2

private theorem aod_read16 {D : BitVec 64 → Bool} {m₁ m₂ m : Memory}
    (h : AgreeOutsideDisjoint D m₁ m₂ m) {ea : BitVec 64} (hd : AllInDom D ea 2) :
    m₁.read16 ea = m.read16 ea ∧ m₂.read16 ea = m.read16 ea := by
  have h0 : ea + 0#64 = ea := by bv_omega
  refine ⟨?_, ?_⟩ <;>
    simp only [Memory.read16, h0, (aod_read8 h hd.1).1, (aod_read8 h hd.1).2,
      (aod_read8 h hd.2.1).1, (aod_read8 h hd.2.1).2]

private theorem aod_read32 {D : BitVec 64 → Bool} {m₁ m₂ m : Memory}
    (h : AgreeOutsideDisjoint D m₁ m₂ m) {ea : BitVec 64} (hd : AllInDom D ea 4) :
    m₁.read32 ea = m.read32 ea ∧ m₂.read32 ea = m.read32 ea := by
  have h0 : ea + 0#64 = ea := by bv_omega
  have h2 : ea + 2#64 = ea + 1#64 + 1#64 := by bv_omega
  have h3 : ea + 3#64 = ea + 1#64 + 1#64 + 1#64 := by bv_omega
  refine ⟨?_, ?_⟩ <;>
    simp only [Memory.read32, h0, h2, h3, (aod_read8 h hd.1).1, (aod_read8 h hd.1).2,
      (aod_read8 h hd.2.1).1, (aod_read8 h hd.2.1).2,
      (aod_read8 h hd.2.2.1).1, (aod_read8 h hd.2.2.1).2,
      (aod_read8 h hd.2.2.2.1).1, (aod_read8 h hd.2.2.2.1).2]

private theorem aod_read64 {D : BitVec 64 → Bool} {m₁ m₂ m : Memory}
    (h : AgreeOutsideDisjoint D m₁ m₂ m) {ea : BitVec 64} (hd : AllInDom D ea 8) :
    m₁.read64 ea = m.read64 ea ∧ m₂.read64 ea = m.read64 ea := by
  obtain ⟨hd0, hd4⟩ := (allInDom_add D 4 4 ea).mp hd
  have h0 : ea + 0#64 = ea := by bv_omega
  have h2 : ea + 2#64 = ea + 1#64 + 1#64 := by bv_omega
  have h3 : ea + 3#64 = ea + 1#64 + 1#64 + 1#64 := by bv_omega
  have h5 : ea + 5#64 = ea + BitVec.ofNat 64 4 + 1#64 := by bv_omega
  have h6 : ea + 6#64 = ea + BitVec.ofNat 64 4 + 1#64 + 1#64 := by bv_omega
  have h7 : ea + 7#64 = ea + BitVec.ofNat 64 4 + 1#64 + 1#64 + 1#64 := by bv_omega
  refine ⟨?_, ?_⟩ <;>
    simp only [Memory.read64, h0, h2, h3, h5, h6, h7,
      (aod_read8 h hd0.1).1, (aod_read8 h hd0.1).2,
      (aod_read8 h hd0.2.1).1, (aod_read8 h hd0.2.1).2,
      (aod_read8 h hd0.2.2.1).1, (aod_read8 h hd0.2.2.1).2,
      (aod_read8 h hd0.2.2.2.1).1, (aod_read8 h hd0.2.2.2.1).2,
      (aod_read8 h hd4.1).1, (aod_read8 h hd4.1).2,
      (aod_read8 h hd4.2.1).1, (aod_read8 h hd4.2.1).2,
      (aod_read8 h hd4.2.2.1).1, (aod_read8 h hd4.2.2.1).2,
      (aod_read8 h hd4.2.2.2.1).1, (aod_read8 h hd4.2.2.2.1).2]

private theorem aod_read128 {D : BitVec 64 → Bool} {m₁ m₂ m : Memory}
    (h : AgreeOutsideDisjoint D m₁ m₂ m) {ea : BitVec 64} (hd : AllInDom D ea 16) :
    m₁.read128 ea = m.read128 ea ∧ m₂.read128 ea = m.read128 ea := by
  obtain ⟨hd0, hd8⟩ := (allInDom_add D 8 8 ea).mp hd
  refine ⟨?_, ?_⟩ <;>
    simp only [Memory.read128, (aod_read64 h hd0).1, (aod_read64 h hd0).2,
      (aod_read64 h hd8).1, (aod_read64 h hd8).2]

private theorem aod_readSized {D : BitVec 64 → Bool} {m₁ m₂ m : Memory}
    (h : AgreeOutsideDisjoint D m₁ m₂ m) {sz : MemWidth} {signed : Bool} {ea : BitVec 64}
    (hd : AllInDom D ea sz.bytes) :
    m₁.readSized sz signed ea = m.readSized sz signed ea ∧
    m₂.readSized sz signed ea = m.readSized sz signed ea := by
  cases sz with
  | B8 => refine ⟨?_, ?_⟩ <;> simp only [Memory.readSized, (aod_read8 h hd.1).1, (aod_read8 h hd.1).2]
  | H16 => refine ⟨?_, ?_⟩ <;> simp only [Memory.readSized, (aod_read16 h hd).1, (aod_read16 h hd).2]
  | W32 => refine ⟨?_, ?_⟩ <;> simp only [Memory.readSized, (aod_read32 h hd).1, (aod_read32 h hd).2]
  | X64 => exact aod_read64 h hd

private theorem aod_readSimdSized {D : BitVec 64 → Bool} {m₁ m₂ m : Memory}
    (h : AgreeOutsideDisjoint D m₁ m₂ m) {sz : SimdMemSize} {ea : BitVec 64}
    (hd : AllInDom D ea sz.bytes) :
    m₁.readSimdSized sz ea = m.readSimdSized sz ea ∧
    m₂.readSimdSized sz ea = m.readSimdSized sz ea := by
  cases sz with
  | B8 => refine ⟨?_, ?_⟩ <;> simp only [Memory.readSimdSized, (aod_read8 h hd.1).1, (aod_read8 h hd.1).2]
  | H16 => refine ⟨?_, ?_⟩ <;> simp only [Memory.readSimdSized, (aod_read16 h hd).1, (aod_read16 h hd).2]
  | S32 => refine ⟨?_, ?_⟩ <;> simp only [Memory.readSimdSized, (aod_read32 h hd).1, (aod_read32 h hd).2]
  | D64 => refine ⟨?_, ?_⟩ <;> simp only [Memory.readSimdSized, (aod_read64 h hd).1, (aod_read64 h hd).2]
  | Q128 => exact aod_read128 h hd

private theorem astep_write8 {D : BitVec 64 → Bool} {m₀ m₁ m₂ m : Memory}
    (h : AgreeStep D m₀ m₁ m₂ m) {addr : BitVec 64} (hd : D addr = true) (val : BitVec 8) :
    AgreeStep D m₀ (m₁.write8 addr val) (m₂.write8 addr val) (m.write8 addr val) := by
  refine ⟨⟨fun a ha => ?_, fun a ha => ?_⟩, fun a ha => ?_, ?_⟩
  · by_cases heq : a = addr
    · subst heq; obtain ⟨c1, c2⟩ := h.1.1 a ha; simp [Memory.write8, Memory.rawPerm, c1, c2]
    · simp [Memory.write8, heq, (h.1.1 a ha).1, (h.1.1 a ha).2]
  · have hne : a ≠ addr := fun heq => by subst heq; rw [hd] at ha; cases ha
    have hp1 : (m₁.write8 addr val).perm a = m₁.perm a := by simp [Memory.write8, Memory.perm, hne]
    have hp2 : (m₂.write8 addr val).perm a = m₂.perm a := by simp [Memory.write8, Memory.perm, hne]
    rw [hp1, hp2]; exact h.1.2 a ha
  · have hne : a ≠ addr := fun heq => by subst heq; rw [hd] at ha; cases ha
    simp [Memory.write8, hne, h.2.1 a ha]
  · funext a; exact (Memory.isAnon_write8_apply m addr a val).trans (congrFun h.2.2 a)

private theorem astep_write16 {D : BitVec 64 → Bool} {m₀ m₁ m₂ m : Memory}
    (h : AgreeStep D m₀ m₁ m₂ m) {ea : BitVec 64} (hd : AllInDom D ea 2) (val : BitVec 16) :
    AgreeStep D m₀ (m₁.write16 ea val) (m₂.write16 ea val) (m.write16 ea val) := by
  have h0 : ea + 0#64 = ea := by bv_omega
  unfold Memory.write16; rw [h0]; exact astep_write8 (astep_write8 h hd.1 _) hd.2.1 _

private theorem astep_write32 {D : BitVec 64 → Bool} {m₀ m₁ m₂ m : Memory}
    (h : AgreeStep D m₀ m₁ m₂ m) {ea : BitVec 64} (hd : AllInDom D ea 4) (val : BitVec 32) :
    AgreeStep D m₀ (m₁.write32 ea val) (m₂.write32 ea val) (m.write32 ea val) := by
  have h0 : ea + 0#64 = ea := by bv_omega
  have h2 : ea + 2#64 = ea + 1#64 + 1#64 := by bv_omega
  have h3 : ea + 3#64 = ea + 1#64 + 1#64 + 1#64 := by bv_omega
  unfold Memory.write32; rw [h0, h2, h3]
  exact astep_write8 (astep_write8 (astep_write8 (astep_write8 h hd.1 _) hd.2.1 _) hd.2.2.1 _) hd.2.2.2.1 _

private theorem astep_write64 {D : BitVec 64 → Bool} {m₀ m₁ m₂ m : Memory}
    (h : AgreeStep D m₀ m₁ m₂ m) {ea : BitVec 64} (hd : AllInDom D ea 8) (val : BitVec 64) :
    AgreeStep D m₀ (m₁.write64 ea val) (m₂.write64 ea val) (m.write64 ea val) := by
  obtain ⟨hd0, hd4⟩ := (allInDom_add D 4 4 ea).mp hd
  have h0 : ea + 0#64 = ea := by bv_omega
  have h2 : ea + 2#64 = ea + 1#64 + 1#64 := by bv_omega
  have h3 : ea + 3#64 = ea + 1#64 + 1#64 + 1#64 := by bv_omega
  have h5 : ea + 5#64 = ea + BitVec.ofNat 64 4 + 1#64 := by bv_omega
  have h6 : ea + 6#64 = ea + BitVec.ofNat 64 4 + 1#64 + 1#64 := by bv_omega
  have h7 : ea + 7#64 = ea + BitVec.ofNat 64 4 + 1#64 + 1#64 + 1#64 := by bv_omega
  unfold Memory.write64; rw [h0, h2, h3, h5, h6, h7]
  exact astep_write8 (astep_write8 (astep_write8 (astep_write8
    (astep_write8 (astep_write8 (astep_write8 (astep_write8 h hd0.1 _) hd0.2.1 _) hd0.2.2.1 _) hd0.2.2.2.1 _)
    hd4.1 _) hd4.2.1 _) hd4.2.2.1 _) hd4.2.2.2.1 _

private theorem astep_write128 {D : BitVec 64 → Bool} {m₀ m₁ m₂ m : Memory}
    (h : AgreeStep D m₀ m₁ m₂ m) {ea : BitVec 64} (hd : AllInDom D ea 16) (val : BitVec 128) :
    AgreeStep D m₀ (m₁.write128 ea val) (m₂.write128 ea val) (m.write128 ea val) := by
  obtain ⟨hd0, hd8⟩ := (allInDom_add D 8 8 ea).mp hd
  unfold Memory.write128
  exact astep_write64 (astep_write64 h hd0 _) hd8 _

private theorem astep_writeSized {D : BitVec 64 → Bool} {m₀ m₁ m₂ m : Memory}
    (h : AgreeStep D m₀ m₁ m₂ m) {sz : MemWidth} {ea : BitVec 64}
    (hd : AllInDom D ea sz.bytes) (val : BitVec 64) :
    AgreeStep D m₀ (m₁.writeSized sz ea val) (m₂.writeSized sz ea val) (m.writeSized sz ea val) := by
  cases sz with
  | B8 => exact astep_write8 h hd.1 _
  | H16 => exact astep_write16 h hd _
  | W32 => exact astep_write32 h hd _
  | X64 => exact astep_write64 h hd _

private theorem astep_writeSimdSized {D : BitVec 64 → Bool} {m₀ m₁ m₂ m : Memory}
    (h : AgreeStep D m₀ m₁ m₂ m) {sz : SimdMemSize} {ea : BitVec 64}
    (hd : AllInDom D ea sz.bytes) (val : BitVec 128) :
    AgreeStep D m₀ (m₁.writeSimdSized sz ea val) (m₂.writeSimdSized sz ea val) (m.writeSimdSized sz ea val) := by
  cases sz with
  | B8 => exact astep_write8 h hd.1 _
  | H16 => exact astep_write16 h hd _
  | S32 => exact astep_write32 h hd _
  | D64 => exact astep_write64 h hd _
  | Q128 => exact astep_write128 h hd _

private theorem astep_simdStoreRegs {D : BitVec 64 → Bool} {m₀ : Memory}
    (sz : SimdMemSize) (vals : BitVec 5 → BitVec 128) :
    ∀ (n : Nat) (vt : BitVec 5) (ea : BitVec 64) {m₁ m₂ m : Memory},
      AgreeStep D m₀ m₁ m₂ m → AllInDom D ea (n * sz.bytes) →
      AgreeStep D m₀ (simdStoreRegs sz vals n vt ea m₁)
        (simdStoreRegs sz vals n vt ea m₂) (simdStoreRegs sz vals n vt ea m)
  | 0, _, _, _, _, _, h, _ => h
  | n + 1, vt, ea, _, _, _, h, hd => by
    have hmul : (n + 1) * sz.bytes = sz.bytes + n * sz.bytes := Nat.succ_mul n sz.bytes ▸ Nat.add_comm _ _
    obtain ⟨hd0, hdn⟩ := (allInDom_add D sz.bytes (n * sz.bytes) ea).mp (hmul ▸ hd)
    exact astep_simdStoreRegs sz vals n _ _ (astep_writeSimdSized h hd0 _) hdn

private theorem sm_mem (s : State) (m : Memory) : (s.setMem m).mem = m := by cases s; rfl
private theorem sm_regs (s : State) (m : Memory) : (s.setMem m).regs = s.regs := by cases s; rfl
private theorem sm_vregs (s : State) (m : Memory) : (s.setMem m).vregs = s.vregs := by cases s; rfl
private theorem sm_sp (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by cases s; rfl
private theorem sm_pc (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by cases s; rfl
private theorem sm_ps (s : State) (m : Memory) : (s.setMem m).pstate = s.pstate := by cases s; rfl
private theorem sm_tp (s : State) (m : Memory) : (s.setMem m).tpidrEl0 = s.tpidrEl0 := by cases s; rfl
private theorem sm_fp (s : State) (m : Memory) : (s.setMem m).fpsr = s.fpsr := by cases s; rfl
private theorem sm_st (s : State) (m : Memory) : (s.setMem m).status = s.status := by cases s; rfl
private theorem sm_spa (s : State) (m : Memory) : (s.setMem m).spAligned = s.spAligned := by cases s; rfl
private theorem sm_r64 (s : State) (m : Memory) (r : Reg) : (s.setMem m).readReg64 r = s.readReg64 r := by cases s; rfl
private theorem sm_r32 (s : State) (m : Memory) (r : Reg) : (s.setMem m).readReg32 r = s.readReg32 r := by cases s; rfl
private theorem sm_rr (s : State) (m : Memory) (w : Width) (r : Reg) : (s.setMem m).readReg w r = s.readReg w r := by cases s; rfl
private theorem sm_rv128 (s : State) (m : Memory) (r : BitVec 5) : (s.setMem m).readVReg128 r = s.readVReg128 r := by cases s; rfl
private theorem sm_rv128_eta (s : State) (m : Memory) : (s.setMem m).readVReg128 = s.readVReg128 := by funext r; cases s; rfl
private theorem sm_rv64 (s : State) (m : Memory) (r : BitVec 5) : (s.setMem m).readVReg64 r = s.readVReg64 r := by cases s; rfl
private theorem sm_rv32 (s : State) (m : Memory) (r : BitVec 5) : (s.setMem m).readVReg32 r = s.readVReg32 r := by cases s; rfl
private theorem sm_ewf (s : State) (m : Memory) : (s.setMem m).exclWillFail = s.exclWillFail := by cases s; rfl
private theorem sm_csp (s : State) (m : Memory) (r : Reg) : checkRegSPAligned (s.setMem m) r = checkRegSPAligned s r := by
  cases s; cases r <;> rfl
private theorem sm_casp (s : State) (m : Memory) (a : AddrMode) : checkAddrSPAligned (s.setMem m) a = checkAddrSPAligned s a := by
  cases s; cases a <;> rfl
private theorem sm_eam (s : State) (m : Memory) (a : AddrMode) : evalAddrMode (s.setMem m) a = evalAddrMode s a := by
  cases s; cases a <;> rfl
private theorem sm_smem (s : State) (m m' : Memory) : (s.setMem m).setMem m' = s.setMem m' := by cases s; rfl
private theorem sm_adv (s : State) (m : Memory) : (s.setMem m).advancePC = s.advancePC.setMem m := by cases s; rfl
private theorem sm_spc (s : State) (m : Memory) (q : BitVec 64) : (s.setMem m).setPC q = (s.setPC q).setMem m := by cases s; rfl
private theorem sm_w64 (s : State) (m : Memory) (r : Reg) (v : BitVec 64) :
    (s.setMem m).writeReg64 r v = (s.writeReg64 r v).setMem m := by cases s; cases r <;> rfl
private theorem sm_w32 (s : State) (m : Memory) (r : Reg) (v : BitVec 32) :
    (s.setMem m).writeReg32 r v = (s.writeReg32 r v).setMem m := sm_w64 s m r _
private theorem sm_w (s : State) (m : Memory) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.setMem m).writeReg w r v = (s.writeReg w r v).setMem m := sm_w64 s m r _
private theorem sm_wv128 (s : State) (m : Memory) (r : BitVec 5) (v : BitVec 128) :
    (s.setMem m).writeVReg128 r v = (s.writeVReg128 r v).setMem m := by cases s; rfl
private theorem sm_wv64 (s : State) (m : Memory) (r : BitVec 5) (v : BitVec 64) :
    (s.setMem m).writeVReg64 r v = (s.writeVReg64 r v).setMem m := sm_wv128 s m r _
private theorem sm_wv32 (s : State) (m : Memory) (r : BitVec 5) (v : BitVec 32) :
    (s.setMem m).writeVReg32 r v = (s.writeVReg32 r v).setMem m := sm_wv128 s m r _
private theorem sm_sps (s : State) (m : Memory) (q : PState) : (s.setMem m).setPState q = (s.setPState q).setMem m := by cases s; rfl
private theorem sm_sfp (s : State) (m : Memory) (f : BitVec 32) : (s.setMem m).setFpsr f = (s.setFpsr f).setMem m := by cases s; rfl
private theorem sm_sofp (s : State) (m : Memory) (f : BitVec 32) : (s.setMem m).orFpsr f = (s.orFpsr f).setMem m := by cases s; rfl
private theorem sm_sst (s : State) (m : Memory) (st : ExecStatus) : (s.setMem m).setStatus st = (s.setStatus st).setMem m := by cases s; rfl
private theorem sm_wst (s : State) (m : Memory) (st : ExecStatus) :
    { s.setMem m with status := st } = ({ s with status := st }).setMem m := by cases s; rfl
private theorem sm_wtp (s : State) (m : Memory) (v : BitVec 64) :
    { s.setMem m with tpidrEl0 := v } = ({ s with tpidrEl0 := v }).setMem m := by cases s; rfl
private theorem sm_sex (s : State) (m : Memory) : (s.setMem m).stepExclOracle = s.stepExclOracle.setMem m := by cases s; rfl
private theorem sm_as (s : State) (m : Memory) (rd : BitVec 5) (r : Except String (BitVec 128)) :
    applySimdResult (s.setMem m) rd r = (applySimdResult s rd r).setMem m := by cases s; cases r <;> rfl
private theorem sm_ass (s : State) (m : Memory) (rd : BitVec 5) (r : Except String (BitVec 128)) (sat : Option (BitVec 32)) :
    applySimdSatResult (s.setMem m) rd r sat = (applySimdSatResult s rd r sat).setMem m := by cases s; cases r <;> cases sat <;> rfl
private theorem sm_ite (c : Prop) [Decidable c] (a b : State) (m : Memory) :
    (if c then a.setMem m else b.setMem m) = (if c then a else b).setMem m := by split <;> rfl

private theorem sm_simdLoadRegs (sz : SimdMemSize) (m : Memory) :
    ∀ (n : Nat) (vt : BitVec 5) (ea : BitVec 64) (s : State) (m' : Memory),
      simdLoadRegs sz m n vt ea (s.setMem m') = (simdLoadRegs sz m n vt ea s).setMem m'
  | 0, _, _, _, _ => rfl
  | n + 1, _, _, s, m' => by simp only [simdLoadRegs, sm_wv128, sm_simdLoadRegs sz m n]

private theorem aod_simdLoadRegs {D : BitVec 64 → Bool} {m₁ m₂ m : Memory}
    (h : AgreeOutsideDisjoint D m₁ m₂ m) (sz : SimdMemSize) :
    ∀ (n : Nat) (vt : BitVec 5) (ea : BitVec 64) (s : State),
      AllInDom D ea (n * sz.bytes) →
      simdLoadRegs sz m₁ n vt ea s = simdLoadRegs sz m n vt ea s ∧
      simdLoadRegs sz m₂ n vt ea s = simdLoadRegs sz m n vt ea s
  | 0, _, _, _, _ => ⟨rfl, rfl⟩
  | n + 1, vt, ea, s, hd => by
    have hmul : (n + 1) * sz.bytes = sz.bytes + n * sz.bytes := Nat.succ_mul n sz.bytes ▸ Nat.add_comm _ _
    obtain ⟨hd0, hdn⟩ := (allInDom_add D sz.bytes (n * sz.bytes) ea).mp (hmul ▸ hd)
    obtain ⟨hr1, hr2⟩ := aod_readSimdSized h hd0
    simp only [simdLoadRegs, hr1, hr2]
    exact aod_simdLoadRegs h sz n _ _ _ hdn

private theorem mem_adv (s : State) : s.advancePC.mem = s.mem := by cases s; rfl
private theorem mem_w64 (s : State) (r : Reg) (v : BitVec 64) : (s.writeReg64 r v).mem = s.mem := by cases s; cases r <;> rfl
private theorem mem_w32 (s : State) (r : Reg) (v : BitVec 32) : (s.writeReg32 r v).mem = s.mem := mem_w64 s r _
private theorem mem_w (s : State) (w : Width) (r : Reg) (v : BitVec 64) : (s.writeReg w r v).mem = s.mem := mem_w64 s r _
private theorem mem_wv128 (s : State) (r : BitVec 5) (v : BitVec 128) : (s.writeVReg128 r v).mem = s.mem := by cases s; rfl
private theorem mem_sex (s : State) : s.stepExclOracle.mem = s.mem := by cases s; rfl
private theorem mem_simdLoadRegs (sz : SimdMemSize) (m : Memory) :
    ∀ (n : Nat) (vt : BitVec 5) (ea : BitVec 64) (s : State),
      (simdLoadRegs sz m n vt ea s).mem = s.mem
  | 0, _, _, _ => rfl
  | n + 1, _, _, s => by simp only [simdLoadRegs, mem_wv128, mem_simdLoadRegs sz m n]

private theorem agreeState_setMem {D : BitVec 64 → Bool} {m₀ m₁' m₂' m' : Memory} (s' : State)
    (hm : AgreeStep D m₀ m₁' m₂' m') :
    AgreeState D m₀ (s'.setMem m₁') (s'.setMem m₂') (s'.setMem m') :=
  ⟨by cases s'; rfl, by cases s'; rfl, by simpa [sm_mem] using hm⟩

private theorem agreeState_load {D : BitVec 64 → Bool} {m₀ m₁ m₂ : Memory} {s s' : State}
    (hm : AgreeStep D m₀ m₁ m₂ s.mem) (hmem : s'.mem = s.mem) :
    AgreeState D m₀ (s'.setMem m₁) (s'.setMem m₂) s' := by
  have h0 : s' = s'.setMem s.mem := by rw [← hmem]; cases s'; rfl
  conv_rhs => rw [h0]
  exact agreeState_setMem s' hm

private theorem agreeState_of_comm {D : BitVec 64 → Bool} {m₀ m₁ m₂ : Memory} {s : State}
    (hm : AgreeStep D m₀ m₁ m₂ s.mem) {F : State → State}
    (hF : ∀ m, F (s.setMem m) = (F s).setMem m) :
    AgreeState D m₀ (F (s.setMem m₁)) (F (s.setMem m₂)) (F s) := by
  have h0 : F s = (F s).setMem s.mem := by
    have := hF s.mem; rwa [show s.setMem s.mem = s from by cases s; rfl] at this
  rw [hF m₁, hF m₂]; conv_rhs => rw [h0]
  exact agreeState_setMem (F s) hm

private theorem ite_not_fault_running {b : Bool} {s rest : State} {msg : String}
    (h : (if !b then s.setStatus (.Exception msg) else rest).status = .Running) :
    b = true ∧ rest.status = .Running := by
  cases b with
  | false => cases s; simp [State.setStatus] at h
  | true => exact ⟨rfl, h⟩

private theorem elim_pure_guard {D : BitVec 64 → Bool} {m₀ : Memory} {b : Bool}
    {s : State} {m₁ m₂ : Memory} {r1 r2 r0 : State} {msg : String}
    (h1 : (if !b then (s.setMem m₁).setStatus (.Exception msg) else r1).status = .Running)
    (h2 : (if !b then (s.setMem m₂).setStatus (.Exception msg) else r2).status = .Running)
    (k : r1.status = .Running → r2.status = .Running → AgreeState D m₀ r1 r2 r0) :
    AgreeState D m₀
      (if !b then (s.setMem m₁).setStatus (.Exception msg) else r1)
      (if !b then (s.setMem m₂).setStatus (.Exception msg) else r2)
      (if !b then s.setStatus (.Exception msg) else r0) := by
  obtain ⟨hb, hr1⟩ := ite_not_fault_running h1
  simp only [hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h2 ⊢
  exact k hr1 h2

private theorem elim_pure_wst {D : BitVec 64 → Bool} {m₀ : Memory} {b : Bool}
    {s : State} {m₁ m₂ : Memory} {r1 r2 r0 : State} {msg : String}
    (h1 : (if b then { s.setMem m₁ with status := .Exception msg } else r1).status = .Running)
    (h2 : (if b then { s.setMem m₂ with status := .Exception msg } else r2).status = .Running)
    (k : r1.status = .Running → r2.status = .Running → AgreeState D m₀ r1 r2 r0) :
    AgreeState D m₀
      (if b then { s.setMem m₁ with status := .Exception msg } else r1)
      (if b then { s.setMem m₂ with status := .Exception msg } else r2)
      (if b then { s with status := .Exception msg } else r0) := by
  cases b with
  | true => cases s; simp at h1
  | false => simp only [Bool.false_eq_true, ↓reduceIte] at h1 h2 ⊢; exact k h1 h2

private theorem elim_canRead {D : BitVec 64 → Bool} {m₀ m₁ m₂ : Memory} {s : State}
    (hm : AgreeStep D m₀ m₁ m₂ s.mem) {ea : BitVec 64} {n : Nat} {msg : String}
    {r1 r2 r0 : State}
    (h1 : (if !m₁.canRead ea n then (s.setMem m₁).setStatus (.Exception msg) else r1).status = .Running)
    (h2 : (if !m₂.canRead ea n then (s.setMem m₂).setStatus (.Exception msg) else r2).status = .Running)
    (k : AllInDom D ea n → r1.status = .Running → r2.status = .Running → AgreeState D m₀ r1 r2 r0) :
    AgreeState D m₀
      (if !m₁.canRead ea n then (s.setMem m₁).setStatus (.Exception msg) else r1)
      (if !m₂.canRead ea n then (s.setMem m₂).setStatus (.Exception msg) else r2)
      (if !s.mem.canRead ea n then s.setStatus (.Exception msg) else r0) := by
  obtain ⟨hc1, hr1⟩ := ite_not_fault_running h1
  obtain ⟨hc2, hr2⟩ := ite_not_fault_running h2
  obtain ⟨hcm, hdom⟩ := aod_canRead hm.1 hc1 hc2
  simp only [hc1, hc2, hcm, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  exact k hdom hr1 hr2

private theorem elim_canWrite {D : BitVec 64 → Bool} {m₀ m₁ m₂ : Memory} {s : State}
    (hm : AgreeStep D m₀ m₁ m₂ s.mem) {ea : BitVec 64} {n : Nat} {msg : String}
    {r1 r2 r0 : State}
    (h1 : (if !m₁.canWrite ea n then (s.setMem m₁).setStatus (.Exception msg) else r1).status = .Running)
    (h2 : (if !m₂.canWrite ea n then (s.setMem m₂).setStatus (.Exception msg) else r2).status = .Running)
    (k : AllInDom D ea n → r1.status = .Running → r2.status = .Running → AgreeState D m₀ r1 r2 r0) :
    AgreeState D m₀
      (if !m₁.canWrite ea n then (s.setMem m₁).setStatus (.Exception msg) else r1)
      (if !m₂.canWrite ea n then (s.setMem m₂).setStatus (.Exception msg) else r2)
      (if !s.mem.canWrite ea n then s.setStatus (.Exception msg) else r0) := by
  obtain ⟨hc1, hr1⟩ := ite_not_fault_running h1
  obtain ⟨hc2, hr2⟩ := ite_not_fault_running h2
  obtain ⟨hcm, hdom⟩ := aod_canWrite hm.1 hc1 hc2
  simp only [hc1, hc2, hcm, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  exact k hdom hr1 hr2

private theorem elim_canRead2 {D : BitVec 64 → Bool} {m₀ m₁ m₂ : Memory} {s : State}
    (hm : AgreeStep D m₀ m₁ m₂ s.mem) {ea ea' : BitVec 64} {n : Nat} {msg : String}
    {r1 r2 r0 : State}
    (h1 : (if !(m₁.canRead ea n && m₁.canRead ea' n) then (s.setMem m₁).setStatus (.Exception msg) else r1).status = .Running)
    (h2 : (if !(m₂.canRead ea n && m₂.canRead ea' n) then (s.setMem m₂).setStatus (.Exception msg) else r2).status = .Running)
    (k : AllInDom D ea n → AllInDom D ea' n → r1.status = .Running → r2.status = .Running → AgreeState D m₀ r1 r2 r0) :
    AgreeState D m₀
      (if !(m₁.canRead ea n && m₁.canRead ea' n) then (s.setMem m₁).setStatus (.Exception msg) else r1)
      (if !(m₂.canRead ea n && m₂.canRead ea' n) then (s.setMem m₂).setStatus (.Exception msg) else r2)
      (if !(s.mem.canRead ea n && s.mem.canRead ea' n) then s.setStatus (.Exception msg) else r0) := by
  obtain ⟨hc1, hr1⟩ := ite_not_fault_running h1; simp only [Bool.and_eq_true] at hc1
  obtain ⟨hc2, hr2⟩ := ite_not_fault_running h2; simp only [Bool.and_eq_true] at hc2
  obtain ⟨hcm, hdom⟩ := aod_canRead hm.1 hc1.1 hc2.1
  obtain ⟨hcm', hdom'⟩ := aod_canRead hm.1 hc1.2 hc2.2
  simp only [hc1.1, hc1.2, hc2.1, hc2.2, hcm, hcm', Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  exact k hdom hdom' hr1 hr2

private theorem elim_canWrite2 {D : BitVec 64 → Bool} {m₀ m₁ m₂ : Memory} {s : State}
    (hm : AgreeStep D m₀ m₁ m₂ s.mem) {ea ea' : BitVec 64} {n : Nat} {msg : String}
    {r1 r2 r0 : State}
    (h1 : (if !(m₁.canWrite ea n && m₁.canWrite ea' n) then (s.setMem m₁).setStatus (.Exception msg) else r1).status = .Running)
    (h2 : (if !(m₂.canWrite ea n && m₂.canWrite ea' n) then (s.setMem m₂).setStatus (.Exception msg) else r2).status = .Running)
    (k : AllInDom D ea n → AllInDom D ea' n → r1.status = .Running → r2.status = .Running → AgreeState D m₀ r1 r2 r0) :
    AgreeState D m₀
      (if !(m₁.canWrite ea n && m₁.canWrite ea' n) then (s.setMem m₁).setStatus (.Exception msg) else r1)
      (if !(m₂.canWrite ea n && m₂.canWrite ea' n) then (s.setMem m₂).setStatus (.Exception msg) else r2)
      (if !(s.mem.canWrite ea n && s.mem.canWrite ea' n) then s.setStatus (.Exception msg) else r0) := by
  obtain ⟨hc1, hr1⟩ := ite_not_fault_running h1; simp only [Bool.and_eq_true] at hc1
  obtain ⟨hc2, hr2⟩ := ite_not_fault_running h2; simp only [Bool.and_eq_true] at hc2
  obtain ⟨hcm, hdom⟩ := aod_canWrite hm.1 hc1.1 hc2.1
  obtain ⟨hcm', hdom'⟩ := aod_canWrite hm.1 hc1.2 hc2.2
  simp only [hc1.1, hc1.2, hc2.1, hc2.2, hcm, hcm', Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  exact k hdom hdom' hr1 hr2

private theorem elim_canReadWrite {D : BitVec 64 → Bool} {m₀ m₁ m₂ : Memory} {s : State}
    (hm : AgreeStep D m₀ m₁ m₂ s.mem) {ea : BitVec 64} {n : Nat} {msg : String}
    {r1 r2 r0 : State}
    (h1 : (if !(m₁.canRead ea n && m₁.canWrite ea n) then (s.setMem m₁).setStatus (.Exception msg) else r1).status = .Running)
    (h2 : (if !(m₂.canRead ea n && m₂.canWrite ea n) then (s.setMem m₂).setStatus (.Exception msg) else r2).status = .Running)
    (k : AllInDom D ea n → r1.status = .Running → r2.status = .Running → AgreeState D m₀ r1 r2 r0) :
    AgreeState D m₀
      (if !(m₁.canRead ea n && m₁.canWrite ea n) then (s.setMem m₁).setStatus (.Exception msg) else r1)
      (if !(m₂.canRead ea n && m₂.canWrite ea n) then (s.setMem m₂).setStatus (.Exception msg) else r2)
      (if !(s.mem.canRead ea n && s.mem.canWrite ea n) then s.setStatus (.Exception msg) else r0) := by
  obtain ⟨hc1, hr1⟩ := ite_not_fault_running h1; simp only [Bool.and_eq_true] at hc1
  obtain ⟨hc2, hr2⟩ := ite_not_fault_running h2; simp only [Bool.and_eq_true] at hc2
  obtain ⟨hcm, hdom⟩ := aod_canRead hm.1 hc1.1 hc2.1
  obtain ⟨hwm, _⟩ := aod_canWrite hm.1 hc1.2 hc2.2
  simp only [hc1.1, hc1.2, hc2.1, hc2.2, hcm, hwm, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  exact k hdom hr1 hr2

private theorem execLdp_agreeState {D : BitVec 64 → Bool} {m₀ m₁ m₂ : Memory} {s : State}
    (hm : AgreeStep D m₀ m₁ m₂ s.mem) (w : Width) (signed : Bool) (rt1 rt2 : Reg) (addr : AddrMode)
    (h1 : (execLdp w signed rt1 rt2 addr (s.setMem m₁)).status = .Running)
    (h2 : (execLdp w signed rt1 rt2 addr (s.setMem m₂)).status = .Running) :
    AgreeState D m₀ (execLdp w signed rt1 rt2 addr (s.setMem m₁))
      (execLdp w signed rt1 rt2 addr (s.setMem m₂)) (execLdp w signed rt1 rt2 addr s) := by
  dsimp only [execLdp] at h1 h2 ⊢
  rw [sm_casp, sm_eam] at h1 h2; rw [sm_casp, sm_casp, sm_eam, sm_eam]
  rcases heam : evalAddrMode s addr with ⟨ea, wb⟩; simp only [heam, sm_mem] at h1 h2 ⊢
  refine elim_pure_guard h1 h2 fun h1 h2 => elim_canRead2 hm h1 h2 fun hd1 hd2 _ _ => ?_
  rw [(aod_readSized hm.1 hd1).1, (aod_readSized hm.1 hd1).2,
      (aod_readSized hm.1 hd2).1, (aod_readSized hm.1 hd2).2]
  rcases wb with _ | ⟨base, newBase⟩ <;> simp only [sm_w64, sm_w, sm_adv] <;>
    exact agreeState_load hm (by simp only [mem_w64, mem_w, mem_adv])

private theorem execStp_agreeState {D : BitVec 64 → Bool} {m₀ m₁ m₂ : Memory} {s : State}
    (hm : AgreeStep D m₀ m₁ m₂ s.mem) (w : Width) (rt1 rt2 : Reg) (addr : AddrMode)
    (h1 : (execStp w rt1 rt2 addr (s.setMem m₁)).status = .Running)
    (h2 : (execStp w rt1 rt2 addr (s.setMem m₂)).status = .Running) :
    AgreeState D m₀ (execStp w rt1 rt2 addr (s.setMem m₁))
      (execStp w rt1 rt2 addr (s.setMem m₂)) (execStp w rt1 rt2 addr s) := by
  dsimp only [execStp] at h1 h2 ⊢
  rw [sm_casp, sm_eam] at h1 h2; rw [sm_casp, sm_casp, sm_eam, sm_eam]
  rcases heam : evalAddrMode s addr with ⟨ea, wb⟩; simp only [heam, sm_mem, sm_r64, sm_smem] at h1 h2 ⊢
  refine elim_pure_guard h1 h2 fun h1 h2 => elim_canWrite2 hm h1 h2 fun hd1 hd2 _ _ => ?_
  rcases wb with _ | ⟨base, newBase⟩ <;> simp only [sm_w64, sm_adv] <;>
    exact agreeState_setMem _ (astep_writeSized (astep_writeSized hm hd1 _) hd2 _)

private theorem execSt1SinglePost_agreeState {D : BitVec 64 → Bool} {m₀ m₁ m₂ : Memory} {s : State}
    (hm : AgreeStep D m₀ m₁ m₂ s.mem)
    (q : Bool) (rm : BitVec 5) (opcode : BitVec 3) (sBit : Bool) (size : BitVec 2)
    (rn : Reg) (vt : BitVec 5)
    (h1 : (execInst (.st1SinglePost q rm opcode sBit size rn vt) (s.setMem m₁)).status = .Running)
    (h2 : (execInst (.st1SinglePost q rm opcode sBit size rn vt) (s.setMem m₂)).status = .Running) :
    AgreeState D m₀ (execInst (.st1SinglePost q rm opcode sBit size rn vt) (s.setMem m₁))
      (execInst (.st1SinglePost q rm opcode sBit size rn vt) (s.setMem m₂))
      (execInst (.st1SinglePost q rm opcode sBit size rn vt) s) := by
  dsimp only [execInst, execInstWithSvc] at h1 h2 ⊢
  refine elim_pure_wst h1 h2 fun h1 h2 => ?_
  rw [sm_csp] at h1 h2; rw [sm_csp, sm_csp]
  refine elim_pure_guard h1 h2 fun h1 h2 => ?_
  simp only [sm_r64, sm_rv128, sm_mem, sm_smem] at h1 h2 ⊢
  by_cases h0 : opcode.extractLsb' 1 2 == 0#2
  · simp only [h0, ↓reduceIte] at h1 h2 ⊢
    refine elim_canWrite hm h1 h2 fun hd _ _ => ?_
    simp only [sm_w64, sm_adv]; exact agreeState_setMem _ (astep_write8 hm hd.1 _)
  · simp only [h0, Bool.false_eq_true, ↓reduceIte] at h1 h2 ⊢
    by_cases h1b : opcode.extractLsb' 1 2 == 1#2
    · simp only [h1b, ↓reduceIte] at h1 h2 ⊢
      refine elim_canWrite hm h1 h2 fun hd _ _ => ?_
      simp only [sm_w64, sm_adv]; exact agreeState_setMem _ (astep_write16 hm hd _)
    · simp only [h1b, Bool.false_eq_true, ↓reduceIte] at h1 h2 ⊢
      by_cases hs0 : size.extractLsb' 0 1 == 0#1
      · simp only [hs0, ↓reduceIte] at h1 h2 ⊢
        refine elim_canWrite hm h1 h2 fun hd _ _ => ?_
        simp only [sm_w64, sm_adv]; exact agreeState_setMem _ (astep_write32 hm hd _)
      · simp only [hs0, Bool.false_eq_true, ↓reduceIte] at h1 h2 ⊢
        refine elim_canWrite hm h1 h2 fun hd _ _ => ?_
        simp only [sm_w64, sm_adv]; exact agreeState_setMem _ (astep_write64 hm hd _)

private theorem execSimdLdStMulti_agreeState {D : BitVec 64 → Bool} {m₀ m₁ m₂ : Memory} {s : State}
    (hm : AgreeStep D m₀ m₁ m₂ s.mem)
    (isLoad q : Bool) (size : BitVec 2) (selem : Nat) (rn : Reg) (postIdx : Bool) (rm vt : BitVec 5)
    (h1 : (execInst (.simdLdStMulti isLoad q size selem rn postIdx rm vt) (s.setMem m₁)).status = .Running)
    (h2 : (execInst (.simdLdStMulti isLoad q size selem rn postIdx rm vt) (s.setMem m₂)).status = .Running) :
    AgreeState D m₀ (execInst (.simdLdStMulti isLoad q size selem rn postIdx rm vt) (s.setMem m₁))
      (execInst (.simdLdStMulti isLoad q size selem rn postIdx rm vt) (s.setMem m₂))
      (execInst (.simdLdStMulti isLoad q size selem rn postIdx rm vt) s) := by
  have hsel : selem = 2 ∨ selem = 3 ∨ selem = 4 := by
    by_cases hb : ((size == 3#2 && !q) || !(selem == 2 || selem == 3 || selem == 4)) = true
    · dsimp only [execInst, execInstWithSvc] at h1; simp only [hb, ↓reduceIte] at h1; cases s; cases h1
    · simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, not_or, Bool.not_eq_false] at hb
      exact or_assoc.mp hb.2
  dsimp only [execInst, execInstWithSvc] at h1 h2 ⊢
  refine elim_pure_wst h1 h2 fun h1 h2 => ?_
  rw [sm_csp] at h1 h2; rw [sm_csp, sm_csp]
  refine elim_pure_guard h1 h2 fun h1 h2 => ?_
  simp only [sm_r64, sm_rv128_eta, sm_mem, sm_smem] at h1 h2 ⊢
  cases isLoad with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h1 h2 ⊢
    refine elim_canWrite hm h1 h2 fun hd _ _ => ?_
    simp only [sm_w64, sm_adv, sm_ite]
    exact agreeState_setMem _ (astep_simdStoreRegs _ _ selem vt _ hm hd)
  | true =>
    simp only [↓reduceIte] at h1 h2 ⊢
    refine elim_canRead hm h1 h2 fun hd _ _ => ?_
    set sz := SimdMemSize.ofQ q
    set ea := s.readReg64 rn
    rcases hsel with rfl | rfl | rfl
    · have hm2 : 2 * sz.bytes = sz.bytes + sz.bytes := Nat.two_mul sz.bytes
      obtain ⟨hd0, hd1⟩ := (allInDom_add D sz.bytes sz.bytes ea).mp (hm2 ▸ hd)
      cases postIdx <;>
        simp only [Bool.false_eq_true, ↓reduceIte,
          show ¬(2 ≥ 3) from by decide, show ¬(2 ≥ 4) from by decide,
          (aod_readSimdSized hm.1 hd0).1, (aod_readSimdSized hm.1 hd0).2,
          (aod_readSimdSized hm.1 hd1).1, (aod_readSimdSized hm.1 hd1).2,
          sm_wv128, sm_w64, sm_adv] <;>
        exact agreeState_load hm (by simp only [mem_wv128, mem_w64, mem_adv])
    · have hm3 : 3 * sz.bytes = sz.bytes + (sz.bytes + sz.bytes) := by omega
      obtain ⟨hd0, hd12⟩ := (allInDom_add D sz.bytes (sz.bytes + sz.bytes) ea).mp (hm3 ▸ hd)
      obtain ⟨hd1, hd2⟩ := (allInDom_add D sz.bytes sz.bytes _).mp hd12
      cases postIdx <;>
        simp only [Bool.false_eq_true, ↓reduceIte,
          show (3 ≥ 3) from by decide, show ¬(3 ≥ 4) from by decide,
          (aod_readSimdSized hm.1 hd0).1, (aod_readSimdSized hm.1 hd0).2,
          (aod_readSimdSized hm.1 hd1).1, (aod_readSimdSized hm.1 hd1).2,
          (aod_readSimdSized hm.1 hd2).1, (aod_readSimdSized hm.1 hd2).2,
          sm_wv128, sm_w64, sm_adv] <;>
        exact agreeState_load hm (by simp only [mem_wv128, mem_w64, mem_adv])
    · have hm4 : 4 * sz.bytes = sz.bytes + (sz.bytes + (sz.bytes + sz.bytes)) := by omega
      obtain ⟨hd0, hd123⟩ := (allInDom_add D sz.bytes _ ea).mp (hm4 ▸ hd)
      obtain ⟨hd1, hd23⟩ := (allInDom_add D sz.bytes _ _).mp hd123
      obtain ⟨hd2, hd3⟩ := (allInDom_add D sz.bytes sz.bytes _).mp hd23
      cases postIdx <;>
        simp only [Bool.false_eq_true, ↓reduceIte,
          show (4 ≥ 3) from by decide, show (4 ≥ 4) from by decide,
          (aod_readSimdSized hm.1 hd0).1, (aod_readSimdSized hm.1 hd0).2,
          (aod_readSimdSized hm.1 hd1).1, (aod_readSimdSized hm.1 hd1).2,
          (aod_readSimdSized hm.1 hd2).1, (aod_readSimdSized hm.1 hd2).2,
          (aod_readSimdSized hm.1 hd3).1, (aod_readSimdSized hm.1 hd3).2,
          sm_wv128, sm_w64, sm_adv] <;>
        exact agreeState_load hm (by simp only [mem_wv128, mem_w64, mem_adv])

private theorem execLdr_agreeState {D : BitVec 64 → Bool} {m₀ m₁ m₂ : Memory} {s : State}
    (hm : AgreeStep D m₀ m₁ m₂ s.mem) (w : Width) (sz : MemWidth) (signed : Bool) (rt : Reg) (addr : AddrMode)
    (h1 : (execLdr w sz signed rt addr (s.setMem m₁)).status = .Running)
    (h2 : (execLdr w sz signed rt addr (s.setMem m₂)).status = .Running) :
    AgreeState D m₀ (execLdr w sz signed rt addr (s.setMem m₁))
      (execLdr w sz signed rt addr (s.setMem m₂)) (execLdr w sz signed rt addr s) := by
  dsimp only [execLdr] at h1 h2 ⊢
  rw [sm_casp, sm_eam] at h1 h2; rw [sm_casp, sm_casp, sm_eam, sm_eam]
  rcases heam : evalAddrMode s addr with ⟨ea, wb⟩; simp only [heam, sm_mem] at h1 h2 ⊢
  refine elim_pure_guard h1 h2 fun h1 h2 => elim_canRead hm h1 h2 fun hd _ _ => ?_
  rw [(aod_readSized hm.1 hd).1, (aod_readSized hm.1 hd).2]
  rcases wb with _ | ⟨base, newBase⟩ <;> simp only [sm_w64, sm_w, sm_adv] <;>
    exact agreeState_load hm (by simp only [mem_w64, mem_w, mem_adv])

private theorem execLdrLit_agreeState {D : BitVec 64 → Bool} {m₀ m₁ m₂ : Memory} {s : State}
    (hm : AgreeStep D m₀ m₁ m₂ s.mem) (w : Width) (sz : MemWidth) (signed : Bool) (rt : Reg) (offset : BitVec 64)
    (h1 : (execLdrLit w sz signed rt offset (s.setMem m₁)).status = .Running)
    (h2 : (execLdrLit w sz signed rt offset (s.setMem m₂)).status = .Running) :
    AgreeState D m₀ (execLdrLit w sz signed rt offset (s.setMem m₁))
      (execLdrLit w sz signed rt offset (s.setMem m₂)) (execLdrLit w sz signed rt offset s) := by
  dsimp only [execLdrLit] at h1 h2 ⊢; simp only [sm_pc, sm_mem] at h1 h2 ⊢
  refine elim_canRead hm h1 h2 fun hd _ _ => ?_
  rw [(aod_readSized hm.1 hd).1, (aod_readSized hm.1 hd).2]
  simp only [sm_w, sm_adv]; exact agreeState_load hm (by simp only [mem_w, mem_adv])

private theorem execStr_agreeState {D : BitVec 64 → Bool} {m₀ m₁ m₂ : Memory} {s : State}
    (hm : AgreeStep D m₀ m₁ m₂ s.mem) (sz : MemWidth) (rt : Reg) (addr : AddrMode)
    (h1 : (execStr sz rt addr (s.setMem m₁)).status = .Running)
    (h2 : (execStr sz rt addr (s.setMem m₂)).status = .Running) :
    AgreeState D m₀ (execStr sz rt addr (s.setMem m₁))
      (execStr sz rt addr (s.setMem m₂)) (execStr sz rt addr s) := by
  dsimp only [execStr] at h1 h2 ⊢
  rw [sm_casp, sm_eam] at h1 h2; rw [sm_casp, sm_casp, sm_eam, sm_eam]
  rcases heam : evalAddrMode s addr with ⟨ea, wb⟩; simp only [heam, sm_mem, sm_r64, sm_smem] at h1 h2 ⊢
  refine elim_pure_guard h1 h2 fun h1 h2 => elim_canWrite hm h1 h2 fun hd _ _ => ?_
  rcases wb with _ | ⟨base, newBase⟩ <;> simp only [sm_w64, sm_adv] <;>
    exact agreeState_setMem _ (astep_writeSized hm hd _)

private theorem execSimdLdSt1Single_agreeState {D : BitVec 64 → Bool} {m₀ m₁ m₂ : Memory} {s : State}
    (hm : AgreeStep D m₀ m₁ m₂ s.mem)
    (isLoad q postIdx : Bool) (rm : BitVec 5) (opcode : BitVec 3) (sBit : Bool) (size : BitVec 2) (rn : Reg) (vt : BitVec 5)
    (h1 : (execInst (.simdLdSt1Single isLoad q postIdx rm opcode sBit size rn vt) (s.setMem m₁)).status = .Running)
    (h2 : (execInst (.simdLdSt1Single isLoad q postIdx rm opcode sBit size rn vt) (s.setMem m₂)).status = .Running) :
    AgreeState D m₀ (execInst (.simdLdSt1Single isLoad q postIdx rm opcode sBit size rn vt) (s.setMem m₁))
      (execInst (.simdLdSt1Single isLoad q postIdx rm opcode sBit size rn vt) (s.setMem m₂))
      (execInst (.simdLdSt1Single isLoad q postIdx rm opcode sBit size rn vt) s) := by
  dsimp only [execInst, execInstWithSvc] at h1 h2 ⊢
  refine elim_pure_wst h1 h2 fun h1 h2 => ?_
  rw [sm_csp] at h1 h2; rw [sm_csp, sm_csp]
  refine elim_pure_guard h1 h2 fun h1 h2 => ?_
  simp only [sm_r64, sm_rv128, sm_mem, sm_smem] at h1 h2 ⊢
  cases isLoad with
  | true =>
    simp only [↓reduceIte] at h1 h2 ⊢
    refine elim_canRead hm h1 h2 fun hd _ _ => ?_
    rw [(aod_readSized hm.1 hd).1, (aod_readSized hm.1 hd).2]
    cases postIdx <;> simp only [Bool.false_eq_true, ↓reduceIte, sm_wv128, sm_w64, sm_adv] <;>
      exact agreeState_load hm (by simp only [mem_wv128, mem_w64, mem_adv])
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h1 h2 ⊢
    refine elim_canWrite hm h1 h2 fun hd _ _ => ?_
    cases postIdx <;> simp only [Bool.false_eq_true, ↓reduceIte, sm_w64, sm_adv] <;>
      exact agreeState_setMem _ (astep_writeSized hm hd _)

private theorem execSimdLdSt1Multi_agreeState {D : BitVec 64 → Bool} {m₀ m₁ m₂ : Memory} {s : State}
    (hm : AgreeStep D m₀ m₁ m₂ s.mem)
    (isLoad q : Bool) (size : BitVec 2) (nregs : Nat) (rn : Reg) (postIdx : Bool) (rm vt : BitVec 5)
    (h1 : (execInst (.simdLdSt1Multi isLoad q size nregs rn postIdx rm vt) (s.setMem m₁)).status = .Running)
    (h2 : (execInst (.simdLdSt1Multi isLoad q size nregs rn postIdx rm vt) (s.setMem m₂)).status = .Running) :
    AgreeState D m₀ (execInst (.simdLdSt1Multi isLoad q size nregs rn postIdx rm vt) (s.setMem m₁))
      (execInst (.simdLdSt1Multi isLoad q size nregs rn postIdx rm vt) (s.setMem m₂))
      (execInst (.simdLdSt1Multi isLoad q size nregs rn postIdx rm vt) s) := by
  dsimp only [execInst, execInstWithSvc] at h1 h2 ⊢
  rw [sm_csp] at h1 h2; rw [sm_csp, sm_csp]
  refine elim_pure_guard h1 h2 fun h1 h2 => ?_
  simp only [sm_r64, sm_rv128_eta, sm_mem, sm_smem] at h1 h2 ⊢
  cases isLoad with
  | true =>
    simp only [↓reduceIte] at h1 h2 ⊢
    refine elim_canRead hm h1 h2 fun hd _ _ => ?_
    rw [sm_simdLoadRegs, sm_simdLoadRegs,
        (aod_simdLoadRegs hm.1 _ _ _ _ s hd).1, (aod_simdLoadRegs hm.1 _ _ _ _ s hd).2]
    cases postIdx <;> simp only [Bool.false_eq_true, ↓reduceIte, sm_w64, sm_adv] <;>
      exact agreeState_load hm (by simp only [mem_w64, mem_adv, mem_simdLoadRegs])
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h1 h2 ⊢
    refine elim_canWrite hm h1 h2 fun hd _ _ => ?_
    cases postIdx <;> simp only [Bool.false_eq_true, ↓reduceIte, sm_w64, sm_adv] <;>
      exact agreeState_setMem _ (astep_simdStoreRegs _ _ nregs vt _ hm hd)

private theorem elim_guard_b {D : BitVec 64 → Bool} {m₀ : Memory} {b : Bool}
    {s : State} {m₁ m₂ : Memory} {r1 r2 r0 : State} {msg : String}
    (h1 : (if b then (s.setMem m₁).setStatus (.Exception msg) else r1).status = .Running)
    (h2 : (if b then (s.setMem m₂).setStatus (.Exception msg) else r2).status = .Running)
    (k : r1.status = .Running → r2.status = .Running → AgreeState D m₀ r1 r2 r0) :
    AgreeState D m₀
      (if b then (s.setMem m₁).setStatus (.Exception msg) else r1)
      (if b then (s.setMem m₂).setStatus (.Exception msg) else r2)
      (if b then s.setStatus (.Exception msg) else r0) := by
  cases b with
  | true => cases s; simp [State.setStatus] at h1
  | false => simp only [Bool.false_eq_true, ↓reduceIte] at h1 h2 ⊢; exact k h1 h2

private theorem sm_opt {α : Type} (o : Option α) (f : α → State) (b : State) (m : Memory) :
    (match o with | some x => (f x).setMem m | none => b.setMem m) =
      (match o with | some x => f x | none => b).setMem m := by cases o <;> rfl

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 600000 in
private theorem execInst_agreeState {D : BitVec 64 → Bool} {m₀ m₁ m₂ : Memory} {s : State}
    (hm : AgreeStep D m₀ m₁ m₂ s.mem) {inst : Instr} (hno : inst.isSvc0 = false)
    (h1 : (execInst inst (s.setMem m₁)).status = .Running)
    (h2 : (execInst inst (s.setMem m₂)).status = .Running) :
    AgreeState D m₀ (execInst inst (s.setMem m₁)) (execInst inst (s.setMem m₂)) (execInst inst s) := by
  cases inst
  case ldr w sz signed rt addr => exact execLdr_agreeState hm w sz signed rt addr h1 h2
  case ldrLit w signed rt offset =>
    exact execLdrLit_agreeState hm w (if signed then .W32 else (w : MemWidth)) signed rt offset h1 h2
  case str sz rt addr => exact execStr_agreeState hm sz rt addr h1 h2
  case ldp w signed rt1 rt2 addr => exact execLdp_agreeState hm w signed rt1 rt2 addr h1 h2
  case stp w rt1 rt2 addr => exact execStp_agreeState hm w rt1 rt2 addr h1 h2
  case ldnp sz rn rt rt2 offset =>
    dsimp only [execInst, execInstWithSvc] at h1 h2 ⊢
    cases sz <;> exact execLdp_agreeState hm _ false rt rt2 (.Offset rn offset) h1 h2
  case stnp sz rn rt rt2 offset =>
    dsimp only [execInst, execInstWithSvc] at h1 h2 ⊢
    cases sz <;> exact execStp_agreeState hm _ rt rt2 (.Offset rn offset) h1 h2
  case st1SinglePost q rm opcode sBit size rn vt =>
    exact execSt1SinglePost_agreeState hm q rm opcode sBit size rn vt h1 h2
  case simdLdSt1Single isLoad q postIdx rm opcode sBit size rn vt =>
    exact execSimdLdSt1Single_agreeState hm isLoad q postIdx rm opcode sBit size rn vt h1 h2
  case simdLdSt1Multi isLoad q sz nregs rn postIdx rm vt =>
    exact execSimdLdSt1Multi_agreeState hm isLoad q sz nregs rn postIdx rm vt h1 h2
  case simdLdStMulti isLoad q size selem rn postIdx rm vt =>
    exact execSimdLdStMulti_agreeState hm isLoad q size selem rn postIdx rm vt h1 h2
  case ldarStlr sz isLoad rn rt =>
    dsimp only [execInst, execInstWithSvc] at h1 h2 ⊢
    rw [sm_csp] at h1 h2; rw [sm_csp, sm_csp]
    refine elim_guard_b h1 h2 fun h1 h2 => ?_
    simp only [sm_r64, sm_mem, sm_smem] at h1 h2 ⊢
    refine elim_guard_b h1 h2 fun h1 h2 => ?_
    cases isLoad with
    | true =>
      simp only [↓reduceIte] at h1 h2 ⊢
      refine elim_canRead hm h1 h2 fun hd _ _ => ?_
      rw [(aod_readSized hm.1 hd).1, (aod_readSized hm.1 hd).2]
      simp only [sm_w, sm_adv]; exact agreeState_load hm (by simp only [mem_w, mem_adv])
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h1 h2 ⊢
      refine elim_canWrite hm h1 h2 fun hd _ _ => ?_
      simp only [sm_adv]; exact agreeState_setMem _ (astep_writeSized hm hd _)
  case ldxr sz _ rn rt | ldapr sz rn rt =>
    dsimp only [execInst, execInstWithSvc] at h1 h2 ⊢
    rw [sm_csp] at h1 h2; rw [sm_csp, sm_csp]
    refine elim_guard_b h1 h2 fun h1 h2 => ?_
    simp only [sm_r64, sm_mem] at h1 h2 ⊢
    refine elim_guard_b h1 h2 fun h1 h2 => elim_canRead hm h1 h2 fun hd _ _ => ?_
    rw [(aod_readSized hm.1 hd).1, (aod_readSized hm.1 hd).2]
    simp only [sm_w, sm_adv]; exact agreeState_load hm (by simp only [mem_w, mem_adv])
  case stxr sz _ rs rn rt =>
    dsimp only [execInst, execInstWithSvc] at h1 h2 ⊢
    rw [sm_csp] at h1 h2; rw [sm_csp, sm_csp]
    refine elim_guard_b h1 h2 fun h1 h2 => ?_
    simp only [sm_r64, sm_ewf, sm_mem] at h1 h2 ⊢
    refine elim_guard_b h1 h2 fun h1 h2 => elim_canWrite hm h1 h2 fun hd _ _ => ?_
    cases s.exclWillFail with
    | true =>
      simp only [↓reduceIte, sm_sex, sm_w, sm_adv]
      exact agreeState_load hm (by simp only [mem_sex, mem_w, mem_adv])
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, sm_sex, sm_smem, sm_w, sm_adv]
      exact agreeState_setMem _ (astep_writeSized hm hd _)
  case ldpSimd sz vt1 vt2 addr =>
    dsimp only [execInst, execInstWithSvc] at h1 h2 ⊢
    rw [sm_casp, sm_eam] at h1 h2; rw [sm_casp, sm_casp, sm_eam, sm_eam]
    rcases heam : evalAddrMode s addr with ⟨ea, wb⟩; simp only [heam, sm_mem] at h1 h2 ⊢
    refine elim_guard_b h1 h2 fun h1 h2 => elim_canRead2 hm h1 h2 fun hd1 hd2 _ _ => ?_
    rw [(aod_readSimdSized hm.1 hd1).1, (aod_readSimdSized hm.1 hd1).2,
        (aod_readSimdSized hm.1 hd2).1, (aod_readSimdSized hm.1 hd2).2]
    rcases wb with _ | ⟨base, newBase⟩ <;> simp only [sm_w64, sm_wv128, sm_adv] <;>
      exact agreeState_load hm (by simp only [mem_w64, mem_wv128, mem_adv])
  case stpSimd sz vt1 vt2 addr =>
    dsimp only [execInst, execInstWithSvc] at h1 h2 ⊢
    rw [sm_casp, sm_eam] at h1 h2; rw [sm_casp, sm_casp, sm_eam, sm_eam]
    rcases heam : evalAddrMode s addr with ⟨ea, wb⟩; simp only [heam, sm_mem, sm_rv128, sm_smem] at h1 h2 ⊢
    refine elim_guard_b h1 h2 fun h1 h2 => elim_canWrite2 hm h1 h2 fun hd1 hd2 _ _ => ?_
    rcases wb with _ | ⟨base, newBase⟩ <;> simp only [sm_w64, sm_adv] <;>
      exact agreeState_setMem _ (astep_writeSimdSized (astep_writeSimdSized hm hd1 _) hd2 _)
  case ldrSimd sz vt addr =>
    dsimp only [execInst, execInstWithSvc] at h1 h2 ⊢
    rw [sm_casp, sm_eam] at h1 h2; rw [sm_casp, sm_casp, sm_eam, sm_eam]
    rcases heam : evalAddrMode s addr with ⟨ea, wb⟩; simp only [heam, sm_mem] at h1 h2 ⊢
    refine elim_guard_b h1 h2 fun h1 h2 => elim_canRead hm h1 h2 fun hd _ _ => ?_
    rw [(aod_readSimdSized hm.1 hd).1, (aod_readSimdSized hm.1 hd).2]
    rcases wb with _ | ⟨base, newBase⟩ <;> simp only [sm_w64, sm_wv128, sm_adv] <;>
      exact agreeState_load hm (by simp only [mem_w64, mem_wv128, mem_adv])
  case strSimd sz vt addr =>
    dsimp only [execInst, execInstWithSvc] at h1 h2 ⊢
    rw [sm_casp, sm_eam] at h1 h2; rw [sm_casp, sm_casp, sm_eam, sm_eam]
    rcases heam : evalAddrMode s addr with ⟨ea, wb⟩; simp only [heam, sm_mem, sm_rv128, sm_smem] at h1 h2 ⊢
    refine elim_guard_b h1 h2 fun h1 h2 => elim_canWrite hm h1 h2 fun hd _ _ => ?_
    rcases wb with _ | ⟨base, newBase⟩ <;> simp only [sm_w64, sm_adv] <;>
      exact agreeState_setMem _ (astep_writeSimdSized hm hd _)
  case ldrSimdLit sz vt offset =>
    dsimp only [execInst, execInstWithSvc] at h1 h2 ⊢; simp only [sm_pc, sm_mem] at h1 h2 ⊢
    refine elim_canRead hm h1 h2 fun hd _ _ => ?_
    rw [(aod_readSimdSized hm.1 hd).1, (aod_readSimdSized hm.1 hd).2]
    simp only [sm_wv128, sm_adv]; exact agreeState_load hm (by simp only [mem_wv128, mem_adv])
  case ldnpSimd sz vt1 vt2 rn offset =>
    dsimp only [execInst, execInstWithSvc] at h1 h2 ⊢
    rw [sm_csp] at h1 h2; rw [sm_csp, sm_csp]; simp only [sm_r64, sm_mem] at h1 h2 ⊢
    refine elim_guard_b h1 h2 fun h1 h2 => elim_canRead2 hm h1 h2 fun hd1 hd2 _ _ => ?_
    rw [(aod_readSimdSized hm.1 hd1).1, (aod_readSimdSized hm.1 hd1).2,
        (aod_readSimdSized hm.1 hd2).1, (aod_readSimdSized hm.1 hd2).2]
    simp only [sm_wv128, sm_adv]; exact agreeState_load hm (by simp only [mem_wv128, mem_adv])
  case stnpSimd sz vt1 vt2 rn offset =>
    dsimp only [execInst, execInstWithSvc] at h1 h2 ⊢
    rw [sm_csp] at h1 h2; rw [sm_csp, sm_csp]; simp only [sm_r64, sm_rv128, sm_mem, sm_smem] at h1 h2 ⊢
    refine elim_guard_b h1 h2 fun h1 h2 => elim_canWrite2 hm h1 h2 fun hd1 hd2 _ _ => ?_
    simp only [sm_adv]; exact agreeState_setMem _ (astep_writeSimdSized (astep_writeSimdSized hm hd1 _) hd2 _)
  case ldxp sz _ rn rt rt2 =>
    dsimp only [execInst, execInstWithSvc] at h1 h2 ⊢
    rw [sm_csp] at h1 h2; rw [sm_csp, sm_csp]; simp only [sm_r64, sm_mem] at h1 h2 ⊢
    refine elim_guard_b h1 h2 fun h1 h2 => elim_guard_b h1 h2 fun h1 h2 => elim_canRead hm h1 h2 fun hd _ _ => ?_
    have hm2 : 2 * sz.bytes = sz.bytes + sz.bytes := Nat.two_mul sz.bytes
    obtain ⟨hd1, hd2⟩ := (allInDom_add D sz.bytes sz.bytes _).mp (hm2 ▸ hd)
    rw [(aod_readSized hm.1 hd1).1, (aod_readSized hm.1 hd1).2,
        (aod_readSized hm.1 hd2).1, (aod_readSized hm.1 hd2).2]
    simp only [sm_w, sm_adv]; exact agreeState_load hm (by simp only [mem_w, mem_adv])
  case stxp sz _ rs rn rt rt2 =>
    dsimp only [execInst, execInstWithSvc] at h1 h2 ⊢
    rw [sm_csp] at h1 h2; rw [sm_csp, sm_csp]; simp only [sm_r64, sm_ewf, sm_mem] at h1 h2 ⊢
    refine elim_guard_b h1 h2 fun h1 h2 => elim_guard_b h1 h2 fun h1 h2 => elim_canWrite hm h1 h2 fun hd _ _ => ?_
    have hm2 : 2 * sz.bytes = sz.bytes + sz.bytes := Nat.two_mul sz.bytes
    obtain ⟨hd1, hd2⟩ := (allInDom_add D sz.bytes sz.bytes _).mp (hm2 ▸ hd)
    cases s.exclWillFail with
    | true =>
      simp only [↓reduceIte, sm_sex, sm_w, sm_adv]
      exact agreeState_load hm (by simp only [mem_sex, mem_w, mem_adv])
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, sm_sex, sm_smem, sm_w, sm_adv]
      exact agreeState_setMem _ (astep_writeSized (astep_writeSized hm hd1 _) hd2 _)
  case cas sz _ _ rs rn rt =>
    dsimp only [execInst, execInstWithSvc] at h1 h2 ⊢
    rw [sm_csp] at h1 h2; rw [sm_csp, sm_csp]; simp only [sm_r64, sm_mem, sm_smem] at h1 h2 ⊢
    refine elim_guard_b h1 h2 fun h1 h2 => elim_guard_b h1 h2 fun h1 h2 => elim_canReadWrite hm h1 h2 fun hd _ _ => ?_
    rw [(aod_readSized hm.1 hd).1, (aod_readSized hm.1 hd).2]
    cases sz <;> dsimp only <;>
      (split
       · simp only [sm_w, sm_adv]; exact agreeState_setMem _ (astep_writeSized hm hd _)
       · simp only [sm_w, sm_adv]; exact agreeState_load hm (by simp only [mem_w, mem_adv]))
  case casp sz _ _ rs rs2 rn rt rt2 =>
    dsimp only [execInst, execInstWithSvc] at h1 h2 ⊢
    rw [sm_csp] at h1 h2; rw [sm_csp, sm_csp]; simp only [sm_r64, sm_rr, sm_mem, sm_smem] at h1 h2 ⊢
    refine elim_guard_b h1 h2 fun h1 h2 => elim_guard_b h1 h2 fun h1 h2 => elim_canReadWrite hm h1 h2 fun hd _ _ => ?_
    have hm2 : 2 * sz.bytes = sz.bytes + sz.bytes := Nat.two_mul sz.bytes
    obtain ⟨hd1, hd2⟩ := (allInDom_add D sz.bytes sz.bytes _).mp (hm2 ▸ hd)
    rw [(aod_readSized hm.1 hd1).1, (aod_readSized hm.1 hd1).2,
        (aod_readSized hm.1 hd2).1, (aod_readSized hm.1 hd2).2]
    cases sz <;> dsimp only <;>
      (split
       · simp only [sm_w, sm_adv]; exact agreeState_setMem _ (astep_writeSized (astep_writeSized hm hd1 _) hd2 _)
       · simp only [sm_w, sm_adv]; exact agreeState_load hm (by simp only [mem_w, mem_adv]))
  case atomicRmw op sz _ _ rs rn rt =>
    dsimp only [execInst, execInstWithSvc] at h1 h2 ⊢
    rw [sm_csp] at h1 h2; rw [sm_csp, sm_csp]; simp only [sm_r64, sm_mem, sm_smem] at h1 h2 ⊢
    refine elim_guard_b h1 h2 fun h1 h2 => elim_guard_b h1 h2 fun h1 h2 => elim_canReadWrite hm h1 h2 fun hd _ _ => ?_
    rw [(aod_readSized hm.1 hd).1, (aod_readSized hm.1 hd).2]
    simp only [sm_w, sm_adv]; exact agreeState_setMem _ (astep_writeSized hm hd _)
  case ldapurStlur sz opc rn rt offset =>
    dsimp only [execInst, execInstWithSvc] at h1 h2 ⊢
    rw [sm_csp] at h1 h2; rw [sm_csp, sm_csp]; simp only [sm_r64, sm_mem, sm_smem] at h1 h2 ⊢
    refine elim_guard_b h1 h2 fun h1 h2 => elim_guard_b h1 h2 fun h1 h2 => ?_
    by_cases hopc : opc == 0#2
    · simp only [hopc, ↓reduceIte] at h1 h2 ⊢
      refine elim_canWrite hm h1 h2 fun hd _ _ => ?_
      simp only [sm_adv]; exact agreeState_setMem _ (astep_writeSized hm hd _)
    · simp only [hopc, Bool.false_eq_true, ↓reduceIte] at h1 h2 ⊢
      refine elim_canRead hm h1 h2 fun hd _ _ => ?_
      by_cases h1b : opc == 1#2
      · rw [(aod_readSized hm.1 hd).1, (aod_readSized hm.1 hd).2]
        simp only [h1b, ↓reduceIte, sm_w64, sm_w, sm_adv]; exact agreeState_load hm (by simp only [mem_w64, mem_w, mem_adv])
      · rw [(aod_readSized hm.1 hd (signed := true)).1, (aod_readSized hm.1 hd (signed := true)).2]
        simp only [h1b, Bool.false_eq_true, ↓reduceIte]
        by_cases h2b : opc == 2#2 <;>
          simp only [h2b, Bool.false_eq_true, ↓reduceIte, sm_w64, sm_w32, sm_w, sm_adv] <;>
          exact agreeState_load hm (by simp only [mem_w64, mem_w32, mem_w, mem_adv])
  case simdLd1r q size rn postIdx rm vt =>
    dsimp only [execInst, execInstWithSvc] at h1 h2 ⊢
    rw [sm_csp] at h1 h2; rw [sm_csp, sm_csp]; simp only [sm_r64, sm_mem] at h1 h2 ⊢
    refine elim_guard_b h1 h2 fun h1 h2 => elim_canRead hm h1 h2 fun hd _ _ => ?_
    rw [(aod_readSized hm.1 hd).1, (aod_readSized hm.1 hd).2]
    cases postIdx <;> simp only [Bool.false_eq_true, ↓reduceIte, sm_wv128, sm_w64, sm_adv] <;>
      exact agreeState_load hm (by simp only [mem_wv128, mem_w64, mem_adv])
  case dcZva rt =>
    dsimp only [execInst, execInstWithSvc] at h1 h2 ⊢; simp only [sm_r64, sm_mem, sm_smem] at h1 h2 ⊢
    refine elim_canWrite hm h1 h2 fun hd _ _ => ?_
    simp only [sm_adv]
    exact agreeState_setMem _ (astep_simdStoreRegs .Q128 (fun _ => 0#128) 4 0#5 _ hm hd)
  case system isHalt imm =>
    exact agreeState_of_comm hm fun m => by
      cases isHalt
      · by_cases himm : imm == 0#16
        · have heq : imm = 0#16 := of_decide_eq_true himm; subst heq; simp [Instr.isSvc0] at hno
        · dsimp only [execInst, execInstWithSvc]; simp only [himm, Bool.false_eq_true, ↓reduceIte, sm_sst]
      · dsimp only [execInst, execInstWithSvc]; by_cases himm : imm == 1#16 <;>
          simp only [himm, Bool.false_eq_true, ↓reduceIte, sm_sst]
  case simdThreeSame q u size rm opcode rn rd =>
    exact agreeState_of_comm hm fun m => by
      dsimp only [execInst, execInstWithSvc]; try simp only [sm_wst]
      simp only [sm_rv128]
      by_cases hop : opcode == 0b00011#5
      · simp only [hop, ↓reduceIte]; split <;> simp only [sm_wv128, sm_adv, sm_ass]
      · simp only [hop, Bool.false_eq_true, ↓reduceIte, sm_wv128, sm_adv, sm_sst, sm_as, sm_ass, sm_ite]
  case addSubImm | logicalImm | moveWide | bitfield | logicalShift | addSubShift | addSubExt | addSubCarry
     | condCompareReg | condCompareImm | condSelect | dataProc1 | dataProc2 | dataProc3 =>
    exact agreeState_of_comm hm fun m => by
      dsimp only [execInst, execInstWithSvc, execAddSubImm, execLogicalImm, execMoveWide, execBitfield,
        execLogicalShift, execAddSubShift, execAddSubExt, execAddSubCarry, execCondCompare, execCondSelect,
        execDataProc1, execDataProc2, execDataProc3]
      simp only [sm_ps, sm_r64, sm_r32, sm_rr, sm_w64, sm_w32, sm_w, sm_sps, sm_adv, sm_ite]
      try (split <;> (try split) <;> simp only [sm_sps, sm_adv, sm_ite])
  all_goals
    exact agreeState_of_comm hm fun m => by
      dsimp only [execInst, execInstWithSvc]
      try simp only [sm_wst, sm_wtp]
      simp only [sm_pc, sm_sp, sm_ps, sm_fp, sm_tp, sm_r64, sm_r32, sm_rr, sm_rv128, sm_rv64, sm_rv32,
        sm_csp, sm_opt, sm_adv, sm_spc, sm_w64, sm_w32, sm_w, sm_wv128, sm_wv64, sm_wv32, sm_sps,
        sm_sfp, sm_sofp, sm_sst, sm_as, sm_ass, sm_ite]

private theorem evalInst_eq_execInst_of_not_isSvc0_local (prog : Program) {inst : Instr}
    (hno : inst.isSvc0 = false) (s : State) :
    prog.evalInst inst s = execInst inst s := by
  cases inst with
  | system isHalt imm =>
    cases isHalt
    · by_cases himm : imm == 0#16
      · have heq : imm = 0#16 := of_decide_eq_true himm; subst heq; simp [Instr.isSvc0] at hno
      · simp [Program.evalInst, execInst, execInstWithSvc, himm]
    · rfl
  | _ => rfl

private theorem step_agreeState {prog : Program} (hext : ∀ pc, prog.externAt? pc = none)
    {D : BitVec 64 → Bool} {m₀ m₁₀ m₂₀ : Memory}
    (hno : ∀ m pc inst, m₁₀.KeepsFrozen m → m.perm = m₁₀.perm → prog.fetchMem m pc = some inst →
      inst.isSvc0 = false ∧ inst.isMsrTpidrEl0 = false)
    {s₁ s₁' s₂ s₂' s : State}
    (hag : AgreeState D m₀ s₁ s₂ s)
    (hkf1 : m₁₀.KeepsFrozen s₁.mem)
    (hp1 : s₁.mem.perm = m₁₀.perm) (hp2 : s₂.mem.perm = m₂₀.perm)
    (hstep1 : Step prog s₁ s₁') (hstep2 : Step prog s₂ s₂')
    (hrun1' : s₁'.status = .Running) (hrun2' : s₂'.status = .Running) :
    D s.pc = true ∧
    (s.mem.perm s.pc).x = true ∧
    ∃ s' : State,
      Step emptyStdProg s s' ∧
      AgreeState D m₀ s₁' s₂' s' ∧
      m₁₀.KeepsFrozen s₁'.mem ∧
      s₁'.mem.perm = m₁₀.perm ∧ s₂'.mem.perm = m₂₀.perm ∧
      s.mem.KeepsFrozen s'.mem ∧
      ProofLib.NonSyscallPreserved s s' ∧
      s'.tpidrEl0 = s.tpidrEl0 := by
  obtain ⟨hs1_eq, hs2_eq, hm⟩ := hag
  cases hstep1 with
  | halt_unmapped _ _ _ => simp at hrun1'
  | extern _ he _ _ => rw [hext] at he; cases he
  | extern_fault _ he _ => rw [hext] at he; cases he
  | @exec inst1 hrun1 hfetch1 =>
    cases hstep2 with
    | halt_unmapped _ _ _ => simp at hrun2'
    | extern _ he _ _ => rw [hext] at he; cases he
    | extern_fault _ he _ => rw [hext] at he; cases he
    | @exec inst2 _ hfetch2 =>
      have hpc1 : s₁.pc = s.pc := by rw [hs1_eq]; exact sm_pc s s₁.mem
      have hpc2 : s₂.pc = s.pc := by rw [hs2_eq]; exact sm_pc s s₂.mem
      have hrun : s.status = .Running := by rw [hs1_eq, sm_st] at hrun1; exact hrun1
      obtain ⟨hsvc0, hmsr⟩ := hno s₁.mem s₁.pc inst1 hkf1 hp1 hfetch1
      rw [hpc1] at hfetch1; rw [hpc2] at hfetch2
      have hf_eq : ∀ (mx : Memory), prog.fetchMem mx s.pc =
          if s.pc.toNat % 4 ≠ 0 then none else if !mx.canExec s.pc 4 then none else decode (mx.read32 s.pc) := by
        intro mx; unfold Program.fetchMem; simp [hext s.pc]
      have hce1 : s₁.mem.canExec s.pc 4 = true := by
        rw [hf_eq] at hfetch1; by_cases h4 : s.pc.toNat % 4 ≠ 0
        · simp [h4] at hfetch1
        · by_cases hc : s₁.mem.canExec s.pc 4 = true
          · exact hc
          · simp [h4, hc] at hfetch1
      have hce2 : s₂.mem.canExec s.pc 4 = true := by
        rw [hf_eq] at hfetch2; by_cases h4 : s.pc.toNat % 4 ≠ 0
        · simp [h4] at hfetch2
        · by_cases hc : s₂.mem.canExec s.pc 4 = true
          · exact hc
          · simp [h4, hc] at hfetch2
      obtain ⟨hcem, hdom⟩ := aod_canExec hm.1 hce1 hce2
      obtain ⟨hr1, hr2⟩ := aod_read32 hm.1 hdom
      have hxs : (s.mem.perm s.pc).x = true := by
        simp only [Memory.canExec, Memory.allPerm, Bool.and_eq_true] at hcem; exact hcem.1
      have hfetch_s : prog.fetchMem s.mem s.pc = some inst1 := by
        rw [hf_eq, hcem]; rw [hf_eq, hce1, hr1] at hfetch1; exact hfetch1
      have hinst_eq : inst2 = inst1 := by
        rw [hf_eq, hce2, hr2] at hfetch2; rw [hf_eq, hcem] at hfetch_s
        by_cases h4 : s.pc.toNat % 4 ≠ 0
        · simp [h4] at hfetch_s
        · simp only [h4, ↓reduceIte, Bool.not_true, Bool.false_eq_true] at hfetch2 hfetch_s
          exact Option.some.inj (hfetch2.symm.trans hfetch_s)
      subst inst2
      have hfetch_emp : emptyStdProg.fetchMem s.mem s.pc = some inst1 := by
        have hf_emp : emptyStdProg.fetchMem s.mem s.pc = prog.fetchMem s.mem s.pc := by
          unfold Program.fetchMem; rw [hext s.pc]; rfl
        rw [hf_emp]; exact hfetch_s
      simp only [evalInst_eq_execInst_of_not_isSvc0_local prog hsvc0] at hrun1' hrun2' ⊢
      refine ⟨hdom.1, hxs, execInst inst1 s,
        evalInst_eq_execInst_of_not_isSvc0_local emptyStdProg hsvc0 s ▸ Step.exec hrun hfetch_emp,
        ?_, hkf1.trans (execInst_keepsFrozen inst1 s₁),
        (ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hsvc0 s₁).2.1.trans hp1,
        (ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hsvc0 s₂).2.1.trans hp2,
        execInst_keepsFrozen inst1 s,
        ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hsvc0 s,
        execInst_tpidrEl0_of_not_isMsrTpidrEl0 hmsr s⟩
      rw [hs1_eq] at hrun1' ⊢; rw [hs2_eq] at hrun2' ⊢
      exact execInst_agreeState hm hsvc0 hrun1' hrun2'

private theorem steps_two_runs_locality {prog : Program} (hext : ∀ pc, prog.externAt? pc = none)
    {D keep : BitVec 64 → Bool} {m₀ m₁₀ m₂₀ : Memory}
    (hD_exec_keep : ∀ pc, D pc = true → (m₀.perm pc).x = true → keep pc = true)
    (hno : ∀ m pc inst, m₁₀.KeepsFrozen m → m.perm = m₁₀.perm → prog.fetchMem m pc = some inst →
      inst.isSvc0 = false ∧ inst.isMsrTpidrEl0 = false) :
    ∀ {s₁ sf₁ s₂ sf₂ s : State},
      AgreeState D m₀ s₁ s₂ s →
      s.mem.perm = m₀.perm →
      m₁₀.KeepsFrozen s₁.mem →
      s₁.mem.perm = m₁₀.perm → s₂.mem.perm = m₂₀.perm →
      Steps prog s₁ sf₁ → sf₁.status = .Running →
      Steps prog s₂ sf₂ → sf₂.status = .Running →
      ∃ sf : State,
        h2fsgen_StepsVisitedIn keep emptyStdProg s sf ∧
        s.mem.KeepsFrozen sf.mem ∧
        ProofLib.NonSyscallPreserved s sf ∧
        sf.tpidrEl0 = s.tpidrEl0 ∧
        sf.mem.isAnon = m₀.isAnon ∧
        (∀ a, D a = false → sf.mem.cells a = m₀.cells a) ∧
        ((sf₁ = sf.setMem sf₁.mem ∧ sf₁.mem.perm = m₁₀.perm ∧
            ∀ a, D a = true → sf₁.mem.cells a = sf.mem.cells a) ∨
         (sf₂ = sf.setMem sf₂.mem ∧ sf₂.mem.perm = m₂₀.perm ∧
            ∀ a, D a = true → sf₂.mem.cells a = sf.mem.cells a)) := by
  intro s₁ sf₁ s₂ sf₂ s hag hps hkf1 hp1 hp2 hsteps1 hrun1 hsteps2 hrun2
  induction hsteps1 generalizing s₂ s with
  | refl _ =>
    exact ⟨s, .refl s, Memory.KeepsFrozen.refl s.mem,
      ProofLib.NonSyscallPreserved.refl s, rfl, hag.2.2.2.2, hag.2.2.2.1,
      Or.inl ⟨hag.1, hp1, fun a ha => (hag.2.2.1.1 a ha).1⟩⟩
  | @step s₁ s₁' sf₁ hstep1 hrest1 ih =>
    cases hsteps2 with
    | refl _ =>
      exact ⟨s, .refl s, Memory.KeepsFrozen.refl s.mem,
        ProofLib.NonSyscallPreserved.refl s, rfl, hag.2.2.2.2, hag.2.2.2.1,
        Or.inr ⟨hag.2.1, hp2, fun a ha => (hag.2.2.1.1 a ha).2⟩⟩
    | @step _ s₂' _ hstep2 hrest2 =>
      have hrun1' : s₁'.status = .Running := by
        cases hrest1 with | refl _ => exact hrun1 | step hs _ => exact hs.status_running
      have hrun2' : s₂'.status = .Running := by
        cases hrest2 with | refl _ => exact hrun2 | step hs _ => exact hs.status_running
      obtain ⟨hd_pc, hxs, s', hstep_s, hag', hkf1', hp1', hp2', hkf_s, hnsp_s, htp_s⟩ :=
        step_agreeState hext hno hag hkf1 hp1 hp2 hstep1 hstep2 hrun1' hrun2'
      have hkeep_pc : keep s.pc = true := hD_exec_keep s.pc hd_pc (hps ▸ hxs)
      obtain ⟨sf, hvis_sf, hkf_sf, hnsp_sf, htp_sf, hanon, hout_dom, hbranch⟩ :=
        ih hag' (hnsp_s.2.1.trans hps) hkf1' hp1' hp2' hrun1 hrest2
      exact ⟨sf, .step hkeep_pc hstep_s hvis_sf, hkf_s.trans hkf_sf, hnsp_s.trans hnsp_sf,
        htp_sf.trans htp_s, hanon, hout_dom, hbranch⟩

/-! ## 3. 8-Window Pigeonhole, Phantom Painting, & `mlkemActive_run_visitedIn` -/

private def windowDisjointDom (D : BitVec 64 → Bool) (t : Nat) : Prop :=
  ∀ a, InRegion (phantomWindowBase t) phantomWindowLen a → D a = false

private theorem phantomWindowBase_toNat {t : Nat} (ht : t < 8) :
    (phantomWindowBase t).toNat = 0x01000000 + t * 0x20000 := by
  unfold phantomWindowBase; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

private theorem inRegion_toNat_of_no_wrap {base a : BitVec 64} {len : Nat}
    (hnw : base.toNat + len ≤ 2 ^ 64) (ha : InRegion base len a) :
    base.toNat ≤ a.toNat ∧ a.toNat < base.toNat + len := by
  unfold InRegion at ha; bv_omega

private theorem inRegion_phantomWindow_bounds {t : Nat} (ht : t < 8) {a : BitVec 64}
    (ha : InRegion (phantomWindowBase t) phantomWindowLen a) :
    0x01000000 + t * 0x20000 ≤ a.toNat ∧ a.toNat < 0x01010000 + t * 0x20000 := by
  have hb := phantomWindowBase_toNat ht
  have hbounds := inRegion_toNat_of_no_wrap (len := phantomWindowLen)
    (by unfold phantomWindowLen; omega) ha
  unfold phantomWindowLen at hbounds; omega

private theorem phantomWindows_disjoint {t₁ t₂ : Nat} (ht1 : t₁ < 8) (ht2 : t₂ < 8) (hne : t₁ ≠ t₂)
    {a : BitVec 64} (h1 : InRegion (phantomWindowBase t₁) phantomWindowLen a)
    (h2 : InRegion (phantomWindowBase t₂) phantomWindowLen a) : False := by
  have b1 := inRegion_phantomWindow_bounds ht1 h1
  have b2 := inRegion_phantomWindow_bounds ht2 h2
  omega

private theorem not_inRegion_both_of_gap {base a₁ a₂ : BitVec 64} {len : Nat}
    (hlen : len ≤ 0x10000) (h1 : InRegion base len a₁) (h2 : InRegion base len a₂)
    (hgap : a₁.toNat + 0x10000 < a₂.toNat ∧ a₂.toNat < a₁.toNat + 0x100000) : False := by
  unfold InRegion at h1 h2; bv_omega

private theorem inRegion_hits_at_most_one_window {base a₁ a₂ : BitVec 64} {len t₁ t₂ : Nat}
    (hlen : len ≤ 0x10000) (ht1 : t₁ < 8) (ht2 : t₂ < 8) (hne : t₁ ≠ t₂)
    (h1 : InRegion base len a₁) (hw1 : InRegion (phantomWindowBase t₁) phantomWindowLen a₁)
    (h2 : InRegion base len a₂) (hw2 : InRegion (phantomWindowBase t₂) phantomWindowLen a₂) : False := by
  have b1 := inRegion_phantomWindow_bounds ht1 hw1
  have b2 := inRegion_phantomWindow_bounds ht2 hw2
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · exact not_inRegion_both_of_gap hlen h1 h2 (by omega)
  · exact not_inRegion_both_of_gap hlen h2 h1 (by omega)

private theorem not_inRegion_of_band_disj {base a : BitVec 64} {len : Nat}
    (hlen : len ≤ 0x01000000)
    (hdisj : RangesDisjoint base.toNat len 0x01000000 0x100000)
    (hband : 0x01000000 ≤ a.toNat ∧ a.toNat < 0x01100000)
    (hin : InRegion base len a) : False := by
  unfold InRegion at hin; unfold RangesDisjoint at hdisj; bv_omega

private theorem mlkemActiveBlocks_len_ok :
    (mlkemActiveBlocks.all fun j =>
      decide ((mlkemMultiLib.blockLib j).text.code.length % 4 = 0 ∧
        (mlkemMultiLib.blockLib j).text.code.length ≤ 0x01000000)) = true := by
  decide +kernel

private theorem mlkemActiveDom_disjoint_window {mpl : MultiPlacement}
    (hplA : MlKemActivePlaceable mpl) {t : Nat} (ht : t < 8) {a : BitVec 64}
    (ha : InRegion (phantomWindowBase t) phantomWindowLen a) :
    mlkemActiveDom mpl a = false := by
  have hb := inRegion_phantomWindow_bounds ht ha
  have hband : 0x01000000 ≤ a.toNat ∧ a.toNat < 0x01100000 := by omega
  by_cases hd : mlkemActiveDom mpl a = true
  · exfalso
    unfold mlkemActiveDom at hd; rw [Bool.or_eq_true] at hd
    rcases hd with hkeep | hro
    · unfold mlkemActiveKeep at hkeep; rw [List.any_eq_true] at hkeep
      obtain ⟨j, hj, hpk⟩ := hkeep
      have hl := of_decide_eq_true ((List.all_eq_true.mp mlkemActiveBlocks_len_ok) j hj)
      have hplen : (mlkemMultiLib.blockProgram mpl j).code.length =
          (mlkemMultiLib.blockLib j).text.code.length :=
        CodeBlock.length_patched_of_aligned _ hl.1
      unfold ProofLib.progKeep at hpk
      have hin : InRegion (mpl.base j) (mlkemMultiLib.blockLib j).text.code.length a := by
        unfold InRegion; rw [← hplen]; exact of_decide_eq_true hpk
      exact not_inRegion_of_band_disj hl.2 (hplA.active_blocks_disj j hj) hband hin
    · unfold mlkemRoKeep at hro; rw [List.any_eq_true] at hro
      obtain ⟨p, hp, hin_dec⟩ := hro
      have hlen : p.2 ≤ 0x01000000 := by
        unfold mlkemRoRegions at hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          (dsimp only; decide)
      exact not_inRegion_of_band_disj hlen (hplA.active_ro_disj p hp) hband (of_decide_eq_true hin_dec)
  · exact Bool.not_eq_true _ |>.mp hd

private theorem filter_not_mem_length_ge (bads l : List Nat) (hnd : l.Nodup) :
    l.length ≤ (l.filter (fun x => decide (x ∉ bads))).length + bads.length := by
  induction bads with
  | nil => simp
  | cons b bs ih =>
    suffices hstep : (l.filter (fun x => decide (x ∉ bs))).length ≤
        (l.filter (fun x => decide (x ∉ b :: bs))).length + 1 by
      simp only [List.length_cons]; omega
    clear ih
    induction l with
    | nil => simp
    | cons x xs ihx =>
      rcases List.nodup_cons.mp hnd with ⟨hx_not_mem, hnd_xs⟩
      by_cases hxb : x = b
      · subst hxb
        have hsame : xs.filter (fun y => decide (y ∉ x :: bs)) = xs.filter (fun y => decide (y ∉ bs)) :=
          List.filter_congr fun y hy => by
            have hne : y ≠ x := fun h => hx_not_mem (h ▸ hy)
            simp [List.mem_cons, hne]
        have hd0 : decide (x ∉ x :: bs) = false := by simp
        simp only [List.filter_cons, hd0, Bool.false_eq_true, ↓reduceIte, hsame]
        cases decide (x ∉ bs) <;> simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons] <;> omega
      · have step := ihx hnd_xs
        have hd1 : decide (x ∉ b :: bs) = decide (x ∉ bs) := by simp [List.mem_cons, hxb]
        simp only [List.filter_cons, hd1]
        cases decide (x ∉ bs) <;> simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons] <;> omega

private theorem exists_two_disjoint_windows {mpl : MultiPlacement} {h_pre : Heap}
    (hplA : MlKemActivePlaceable mpl)
    (hbdd : BoundedHeapIntervals 6 0x10000 h_pre) :
    let D := fun a => mlkemActiveDom mpl a || (h_pre.phys a).isSome
    ∃ t₁ t₂ : Nat, t₁ < 8 ∧ t₂ < 8 ∧ t₁ ≠ t₂ ∧
      windowDisjointDom D t₁ ∧ windowDisjointDom D t₂ := by
  classical
  intro D
  rcases hbdd with ⟨ivs, hivs_len, hivs_max, hivs_cov⟩
  let badOf (p : BitVec 64 × Nat) : Nat :=
    if h : ∃ t < 8, ∃ a, InRegion p.1 p.2 a ∧ InRegion (phantomWindowBase t) phantomWindowLen a
    then Classical.choose h else 8
  let bads := ivs.map badOf
  let good := (List.range 8).filter (fun t => decide (t ∉ bads))
  have hnd_r : (List.range 8).Nodup := List.nodup_range
  have hnd_g : good.Nodup := hnd_r.filter _
  have hlen_g : 2 ≤ good.length := by
    have hge := filter_not_mem_length_ge bads (List.range 8) hnd_r
    have hbl : bads.length = ivs.length := List.length_map _
    have hrl : (List.range 8).length = 8 := List.length_range
    dsimp only [good]; omega
  have hdisj_of_good : ∀ t ∈ good, windowDisjointDom D t := fun t ht a ha => by
    obtain ⟨ht_mem, hnot_bad⟩ := List.mem_filter.mp ht
    have ht_lt : t < 8 := List.mem_range.mp ht_mem
    have hda := mlkemActiveDom_disjoint_window hplA ht_lt ha
    dsimp only [D]; rw [hda, Bool.false_or]
    by_cases hp : (h_pre.phys a).isSome = true
    · exfalso
      obtain ⟨p, hp_mem, hin_p⟩ := hivs_cov a hp
      have hex : ∃ t' < 8, ∃ a', InRegion p.1 p.2 a' ∧ InRegion (phantomWindowBase t') phantomWindowLen a' :=
        ⟨t, ht_lt, a, hin_p, ha⟩
      obtain ⟨ht0_lt, a', hin_p', ha'⟩ := Classical.choose_spec hex
      have heq_t : t = badOf p := by
        dsimp only [badOf]; simp only [hex, ↓reduceDIte]
        by_contra hne
        exact inRegion_hits_at_most_one_window (hivs_max p hp_mem) ht_lt ht0_lt hne hin_p ha hin_p' ha'
      exact (of_decide_eq_true hnot_bad) (heq_t ▸ List.mem_map_of_mem hp_mem)
    · exact Bool.not_eq_true _ |>.mp hp
  match hg : good with
  | [] => simp at hlen_g
  | [_] => simp at hlen_g
  | t₁ :: t₂ :: rest =>
    rcases List.nodup_cons.mp hnd_g with ⟨ht1_not, _⟩
    have hne : t₁ ≠ t₂ := fun h => ht1_not (h ▸ List.mem_cons_self)
    have ht1_g : t₁ ∈ t₁ :: t₂ :: rest := List.mem_cons_self
    have ht2_g : t₂ ∈ t₁ :: t₂ :: rest := List.mem_cons_of_mem _ List.mem_cons_self
    have ht1_m : t₁ ∈ good := hg ▸ ht1_g
    have ht2_m : t₂ ∈ good := hg ▸ ht2_g
    exact ⟨t₁, t₂, List.mem_range.mp (List.mem_filter.mp ht1_m).1,
      List.mem_range.mp (List.mem_filter.mp ht2_m).1, hne,
      hdisj_of_good t₁ ht1_g, hdisj_of_good t₂ ht2_g⟩

private theorem readBytes_eq_of_inRegion {m m' : Memory} :
    ∀ (n : Nat) (base : BitVec 64), (hn : n ≤ 2 ^ 64) →
      (∀ a, InRegion base n a → m'.read8 a = m.read8 a) →
      m'.readBytes base n = m.readBytes base n
  | 0, _, _, _ => rfl
  | n + 1, base, hn, h => by
    have h0 : InRegion base (n + 1) base := by
      unfold InRegion; rw [BitVec.sub_self]; exact Nat.zero_lt_succ n
    have hrec := readBytes_eq_of_inRegion n (base + 1#64) (by omega) fun a ha => h a (by
      unfold InRegion at ha ⊢
      have : (a - base).toNat = (a - (base + 1#64)).toNat + 1 := by bv_omega
      omega)
    simp only [Memory.readBytes, h base h0, hrec]

private theorem roDataAt_of_cells_eq {m m' : Memory} {addr : BitVec 64} {bs : List (BitVec 8)}
    (hro : RoDataAt m addr bs) (hlen : bs.length ≤ 2 ^ 64)
    (heq : ∀ a, InRegion addr bs.length a → m'.cells a = m.cells a) : RoDataAt m' addr bs := by
  refine ⟨fun a ha => ?_, (readBytes_eq_of_inRegion bs.length addr hlen fun a ha => by
    unfold Memory.read8; rw [heq a ha]).trans hro.2⟩
  unfold Memory.perm Memory.isLazyFree; rw [heq a ha]; exact hro.1 a ha

private def restrictDom (D : BitVec 64 → Bool) (m : Memory) : Memory :=
  ⟨fun a => if D a then m.cells a else none⟩

private def paintRegion (p : Perm) (base : BitVec 64) (bs : List (BitVec 8)) (m : Memory) : Memory :=
  ⟨fun a => if h : InRegion base bs.length a then some (some p, bs[(a - base).toNat]'h) else m.cells a⟩

private def paintWindowItems (w : BitVec 64) : List (Perm × Nat × List (BitVec 8)) → Memory → Memory
  | [], m => m
  | (p, off, bs) :: rest, m => paintRegion p (w + BitVec.ofNat 64 off) bs (paintWindowItems w rest m)

private def specsOrdered : Nat → List (Nat × Nat) → Bool
  | cur, [] => decide (cur ≤ 0x10000)
  | cur, (off, len) :: rest => decide (cur ≤ off ∧ off % 4 = 0) && specsOrdered (off + len) rest

private theorem specsOrdered_le {cur : Nat} {l : List (Nat × Nat)}
    (h : specsOrdered cur l = true) : cur ≤ 0x10000 := by
  induction l generalizing cur with
  | nil => exact of_decide_eq_true h
  | cons p rest ih =>
    rcases p with ⟨off, len⟩
    simp only [specsOrdered, Bool.and_eq_true, decide_eq_true_eq] at h
    have hrec := ih h.2; omega

private theorem specsOrdered_mem_bounds : ∀ {cur : Nat} {l : List (Nat × Nat)},
    specsOrdered cur l = true → ∀ p ∈ l, cur ≤ p.1 ∧ p.1 + p.2 ≤ 0x10000
  | _, [], _, _, hp => nomatch hp
  | cur, (off, len) :: rest, h, p, hp => by
    simp only [specsOrdered, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.mp hp with rfl | hmem
    · exact ⟨h.1.1, specsOrdered_le h.2⟩
    · obtain ⟨h1, h2⟩ := specsOrdered_mem_bounds h.2 p hmem
      exact ⟨by omega, h2⟩

private theorem add_ofNat_toNat {b : BitVec 64} {n : Nat} (h : b.toNat + n < 2 ^ 64) :
    (b + BitVec.ofNat 64 n).toNat = b.toNat + n := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

private theorem codeLoaded_paintRegion {prog : Program} (m : Memory)
    (hal : prog.base.toNat % 4 = 0) (hnw : prog.base.toNat + prog.code.length ≤ 2 ^ 64) :
    prog.CodeLoaded (paintRegion .rx prog.base prog.code m) := by
  refine Program.CodeLoaded.intro hal hnw fun k hk => ?_
  have hsub : (prog.base + BitVec.ofNat 64 k - prog.base).toNat = k := by bv_omega
  have hin : InRegion prog.base prog.code.length (prog.base + BitVec.ofNat 64 k) := by
    unfold InRegion; omega
  unfold paintRegion Memory.read8 Memory.perm Memory.isLazyFree; simp only [hin, ↓reduceDIte]
  exact ⟨by simp [hsub], rfl, rfl⟩

private theorem codeLoaded_of_cells_eq {prog : Program} {m m' : Memory}
    (hcl : prog.CodeLoaded m)
    (heq : ∀ k < prog.code.length,
      m'.cells (prog.base + BitVec.ofNat 64 k) = m.cells (prog.base + BitVec.ofNat 64 k)) :
    prog.CodeLoaded m' := by
  refine Program.CodeLoaded.intro hcl.aligned hcl.no_wrap fun k hk => ?_
  unfold Memory.read8 Memory.perm Memory.isLazyFree; rw [heq k hk]
  exact ⟨hcl.byte_eq k hk, hcl.perm_eq k hk, hcl.isLazyFree_eq k hk⟩

private theorem paintWindowItems_rx_ok {w : BitVec 64} (hnw : w.toNat + 0x10000 < 2 ^ 64)
    (hal : w.toNat % 4 = 0)
    (specs : List (Perm × Nat × List (BitVec 8))) (cur : Nat) (m : Memory)
    (hord : specsOrdered cur (specs.map fun s => (s.2.1, s.2.2.length)) = true) :
    (∀ a, (paintWindowItems w specs m).cells a ≠ m.cells a →
      w.toNat + cur ≤ a.toNat ∧ a.toNat < w.toNat + 0x10000 ∧ InRegion w 0x10000 a) ∧
    (∀ off bs (prog : Program), (.rx, off, bs) ∈ specs →
      prog.base = w + BitVec.ofNat 64 off → prog.code = bs →
      prog.CodeLoaded (paintWindowItems w specs m)) := by
  induction specs generalizing cur with
  | nil => simp [paintWindowItems]
  | cons hd rest ih =>
    rcases hd with ⟨p, off, bs⟩
    simp only [List.map_cons, specsOrdered, Bool.and_eq_true, decide_eq_true_eq] at hord
    rcases hord with ⟨⟨hcur_le, hoff4⟩, hord_rest⟩
    have hend_le : off + bs.length ≤ 0x10000 := specsOrdered_le hord_rest
    have hbase_nat : (w + BitVec.ofNat 64 off).toNat = w.toNat + off := add_ofNat_toNat (by omega)
    have hbase_nw : (w + BitVec.ofNat 64 off).toNat + bs.length ≤ 2 ^ 64 := by omega
    have hbase_al : (w + BitVec.ofNat 64 off).toNat % 4 = 0 := by omega
    obtain ⟨hmod_rest, hcl_rest⟩ := ih (off + bs.length) hord_rest
    have hnot_head : ∀ a, w.toNat + (off + bs.length) ≤ a.toNat →
        ¬ InRegion (w + BitVec.ofNat 64 off) bs.length a :=
      fun a hge hin => by have hb := inRegion_toNat_of_no_wrap hbase_nw hin; omega
    refine ⟨fun a hne => ?_, fun o b prog hmem hpb hpc => ?_⟩
    · dsimp only [paintWindowItems, paintRegion] at hne
      by_cases hin : InRegion (w + BitVec.ofNat 64 off) bs.length a
      · have hb := inRegion_toNat_of_no_wrap hbase_nw hin
        exact ⟨by omega, by omega, by unfold InRegion; bv_omega⟩
      · simp only [hin, ↓reduceDIte] at hne
        obtain ⟨hlo, hhi, hwin⟩ := hmod_rest a hne
        exact ⟨by omega, hhi, hwin⟩
    · rcases List.mem_cons.mp hmem with heq | hmem_r
      · injection heq with hp hrest; injection hrest with ho hb; subst hp ho hb
        dsimp only [paintWindowItems]
        have h1 : w + BitVec.ofNat 64 o = prog.base := hpb.symm
        have h2 : b = prog.code := hpc.symm
        rw [h1, h2]
        exact codeLoaded_paintRegion _ (hpb ▸ hbase_al) (hpb ▸ hpc ▸ hbase_nw)
      · have hbds := specsOrdered_mem_bounds hord_rest (o, b.length)
          (List.mem_map_of_mem (f := fun s : Perm × Nat × List (BitVec 8) => (s.2.1, s.2.2.length)) hmem_r)
        dsimp only at hbds
        refine codeLoaded_of_cells_eq (hcl_rest o b prog hmem_r hpb hpc) fun k hk => ?_
        have hk_len : k < b.length := hpc ▸ hk
        have hob_nat : (w + BitVec.ofNat 64 o).toNat = w.toNat + o := add_ofNat_toNat (by omega)
        have hk_nat : (prog.base + BitVec.ofNat 64 k).toNat = w.toNat + o + k := by
          rw [hpb, add_ofNat_toNat (by omega), hob_nat]
        have hnh := hnot_head (prog.base + BitVec.ofNat 64 k) (by omega)
        dsimp only [paintWindowItems, paintRegion]; simp only [hnh, ↓reduceDIte]

private theorem paintWindowItems_perm {w : BitVec 64} {keep : BitVec 64 → Bool}
    (specs : List (Perm × Nat × List (BitVec 8))) (m : Memory)
    (hp_ok : ∀ it ∈ specs, it.1 = .rx)
    (hrx_keep : ∀ it ∈ specs, ∀ a, InRegion (w + BitVec.ofNat 64 it.2.1) it.2.2.length a → keep a = true) :
    (∀ a, m.perm a ≠ some .rw → (paintWindowItems w specs m).perm a ≠ some .rw) ∧
    (∀ a, ((m.perm a).x = true → keep a = true) → ((paintWindowItems w specs m).perm a).x = true → keep a = true) := by
  induction specs with
  | nil => exact ⟨fun _ h => h, fun _ h hx => h hx⟩
  | cons hd rest ih =>
    rcases hd with ⟨p, off, bs⟩
    obtain ⟨hnrw_r, hx_r⟩ := ih
      (fun it hit => hp_ok it (List.mem_cons_of_mem _ hit))
      (fun it hit => hrx_keep it (List.mem_cons_of_mem _ hit))
    have hp_head := hp_ok (p, off, bs) List.mem_cons_self
    subst hp_head
    refine ⟨fun a hnrw => ?_, fun a hmx hx => ?_⟩
    · dsimp only [paintWindowItems, paintRegion, Memory.perm]
      by_cases hin : InRegion (w + BitVec.ofNat 64 off) bs.length a
      · simp only [hin, ↓reduceDIte]; decide
      · simp only [hin, ↓reduceDIte]; exact hnrw_r a hnrw
    · dsimp only [paintWindowItems, paintRegion, Memory.perm] at hx
      by_cases hin : InRegion (w + BitVec.ofNat 64 off) bs.length a
      · exact hrx_keep (.rx, off, bs) List.mem_cons_self a hin
      · simp only [hin, ↓reduceDIte] at hx; exact hx_r a hmx hx

private def phantomSpecs (mpl : MultiPlacement) (t : Nat) : List (Perm × Nat × List (BitVec 8)) :=
  mlkemS5Blocks.map fun i =>
    (.rx, (s5BlockOff i).getD 0, (mlkemMultiLib.blockProgram (extendMlkemMpl mpl t) i).code)

private def phantomSpecShape : List (Nat × Nat) :=
  mlkemS5Blocks.map fun i => ((s5BlockOff i).getD 0, (mlkemMultiLib.blockLib i).text.code.length)

private theorem phantomSpecShape_ordered : specsOrdered 0 phantomSpecShape = true := by decide +kernel

private theorem mlkemS5Blocks_ok :
    (mlkemS5Blocks.all fun i =>
      decide (i < mlkemMultiLib.blocks.length ∧
        (mlkemMultiLib.blockLib i).text.code.length % 4 = 0 ∧
        (s5BlockOff i).isSome = true)) = true := by decide +kernel

private theorem phantomSpecs_map_eq (mpl : MultiPlacement) (t : Nat) :
    (phantomSpecs mpl t).map (fun s => (s.2.1, s.2.2.length)) = phantomSpecShape := by
  unfold phantomSpecs phantomSpecShape
  rw [List.map_map]
  refine List.map_congr_left fun i hi => ?_
  have hok := of_decide_eq_true ((List.all_eq_true.mp mlkemS5Blocks_ok) i hi)
  exact Prod.ext rfl (CodeBlock.length_patched_of_aligned _ hok.2.1)

private def paintPhantom (mpl : MultiPlacement) (D : BitVec 64 → Bool) (t : Nat) (m : Memory) : Memory :=
  paintWindowItems (phantomWindowBase t) (phantomSpecs mpl t) (restrictDom D m)

private theorem mlkemRoKeep_perm_ro {mpl : MultiPlacement} {m : Memory}
    (hro : MlKemRoOk mpl m) {a : BitVec 64} (hrk : mlkemRoKeep mpl a = true) :
    m.perm a = some .ro := by
  unfold mlkemRoKeep at hrk; rw [List.any_eq_true] at hrk
  obtain ⟨p, hp_mem, hin_p⟩ := hrk
  have hin := of_decide_eq_true hin_p
  unfold mlkemRoRegions at hp_mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp_mem
  rcases hp_mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (hro.zetaTable.1 a (by rwa [mlkemData00Bytes_length])).1
  · exact (hro.keccakRc.1 a (by rwa [mlkemData01Bytes_length])).1
  · exact (hro.cst16_0.1 a (by rwa [mlkemData02Bytes_length])).1
  · exact (hro.cst16_1.1 a (by rwa [mlkemData03Bytes_length])).1
  · exact (hro.cst16_2.1 a (by rwa [mlkemData04Bytes_length])).1
  · exact (hro.cst16_3.1 a (by rwa [mlkemData05Bytes_length])).1
  · exact (hro.cst16_4.1 a (by rwa [mlkemData06Bytes_length])).1
  · exact (hro.cst16_5.1 a (by rwa [mlkemData07Bytes_length])).1
  · exact (hro.cst16_6.1 a (by rwa [mlkemData08Bytes_length])).1
  · exact (hro.cst16_7.1 a (by rwa [mlkemData09Bytes_length])).1
  · exact (hro.cst16_8.1 a (by rwa [mlkemData10Bytes_length])).1

private theorem paintPhantom_ok {mpl : MultiPlacement} {D : BitVec 64 → Bool} {t : Nat} {m : Memory}
    (ht : t < 8) (hw_disj : windowDisjointDom D t) (hInvA : mlkemActiveInvMem mpl m)
    (hD_act : ∀ a, mlkemActiveDom mpl a = true → D a = true) :
    let m_t := paintPhantom mpl D t m
    (∀ a, D a = true → m_t.cells a = m.cells a) ∧
    (∀ a, D a = false → ¬ InRegion (phantomWindowBase t) phantomWindowLen a → m_t.perm a = none) ∧
    (∀ a, D a = false → m_t.perm a ≠ some .rw) ∧
    mlkemMultiLib.CodeLoaded (extendMlkemMpl mpl t) m_t ∧
    MlKemRoOk (extendMlkemMpl mpl t) m_t ∧
    ((∀ a, D a = true → mlkemActiveDom mpl a = false → m.perm a = some .rw) →
      ∀ a, (m_t.perm a).x = true → c2MlkemKeep (extendMlkemMpl mpl t) a = true) := by
  intro m_t
  rcases hInvA with ⟨_, hclA, hroA⟩
  have hwb := phantomWindowBase_toNat ht
  have hnw_w : (phantomWindowBase t).toNat + 0x10000 < 2 ^ 64 := by omega
  have hal_w : (phantomWindowBase t).toNat % 4 = 0 := by omega
  have hord : specsOrdered 0 ((phantomSpecs mpl t).map fun s => (s.2.1, s.2.2.length)) = true := by
    rw [phantomSpecs_map_eq]; exact phantomSpecShape_ordered
  obtain ⟨hmod, hcl_win⟩ := paintWindowItems_rx_ok hnw_w hal_w (phantomSpecs mpl t) 0 (restrictDom D m) hord
  have hcells_dom : ∀ a, D a = true → m_t.cells a = m.cells a := fun a hda => by
    by_contra hne
    have hdom_eq : (restrictDom D m).cells a = m.cells a := by unfold restrictDom; simp [hda]
    obtain ⟨_, _, hwin⟩ := hmod a (by dsimp [m_t, paintPhantom]; rwa [hdom_eq])
    have hdf := hw_disj a hwin; rw [hda] at hdf; cases hdf
  have hperm_out : ∀ a, D a = false → ¬ InRegion (phantomWindowBase t) phantomWindowLen a → m_t.perm a = none :=
    fun a hdf hnw_a => by
      have hce : m_t.cells a = (restrictDom D m).cells a := by
        by_contra hne; exact hnw_a (hmod a hne).2.2
      unfold Memory.perm; rw [hce]; unfold restrictDom; simp [hdf]
  have hp_specs : ∀ it ∈ phantomSpecs mpl t, it.1 = .rx := fun it hit => by
    unfold phantomSpecs at hit; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hit; rfl
  have hrx_keep : ∀ it ∈ phantomSpecs mpl t,
      ∀ a, InRegion (phantomWindowBase t + BitVec.ofNat 64 it.2.1) it.2.2.length a →
        c2MlkemKeep (extendMlkemMpl mpl t) a = true := fun it hit a hin => by
    unfold phantomSpecs at hit
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hit
    have hok := of_decide_eq_true ((List.all_eq_true.mp mlkemS5Blocks_ok) i hi)
    rcases Option.isSome_iff_exists.mp hok.2.2 with ⟨off, hoff⟩
    have hbase_i : (extendMlkemMpl mpl t).base i = phantomWindowBase t + BitVec.ofNat 64 ((s5BlockOff i).getD 0) := by
      simp [extendMlkemMpl, hoff]
    unfold c2MlkemKeep; rw [List.any_eq_true]
    refine ⟨i, List.mem_range.mpr hok.1, ?_⟩
    unfold ProofLib.progKeep
    rw [show (mlkemMultiLib.blockProgram (extendMlkemMpl mpl t) i).base =
      (extendMlkemMpl mpl t).base i from rfl, hbase_i]
    exact decide_eq_true hin
  obtain ⟨hnrw_p, hx_p⟩ := paintWindowItems_perm (w := phantomWindowBase t)
    (keep := c2MlkemKeep (extendMlkemMpl mpl t)) (phantomSpecs mpl t) (restrictDom D m) hp_specs hrx_keep
  refine ⟨hcells_dom, hperm_out, fun a hdf => hnrw_p a (by unfold Memory.perm restrictDom; simp [hdf]), ?_, ?_, ?_⟩
  · intro j hj
    rcases of_decide_eq_true ((List.all_eq_true.mp block_active_or_s5) j (List.mem_range.mpr hj)) with hact | hinact
    · rw [blockProgram_extendMlkemMpl_eq mpl t hact]
      have hL := hclA j hact
      exact codeLoaded_of_cells_eq hL fun k hk =>
        hcells_dom _ (hD_act _ (Bool.or_eq_true _ _ |>.mpr (Or.inl (mlkemActiveKeep_of_block_offset mpl hact hL.no_wrap hk))))
    · have hok := of_decide_eq_true ((List.all_eq_true.mp mlkemS5Blocks_ok) j hinact)
      rcases Option.isSome_iff_exists.mp hok.2.2 with ⟨off, hoff⟩
      exact hcl_win ((s5BlockOff j).getD 0) _ _
        (List.mem_map_of_mem hinact)
        (by change (extendMlkemMpl mpl t).base j = _; simp [extendMlkemMpl, hoff]) rfl
  · have hro_lift : ∀ {addr : BitVec 64} {bs : List (BitVec 8)},
        RoDataAt m addr bs → (addr, bs.length) ∈ mlkemRoRegions mpl → bs.length ≤ 2 ^ 64 →
        RoDataAt m_t addr bs := fun {addr bs} hr hmem hlen =>
      roDataAt_of_cells_eq hr hlen fun a ha => hcells_dom a (hD_act a (Bool.or_eq_true _ _ |>.mpr (Or.inr (by
        unfold mlkemRoKeep; rw [List.any_eq_true]; exact ⟨(addr, bs.length), hmem, decide_eq_true ha⟩))))
    have hro_m : MlKemRoOk mpl m_t := ⟨
      hro_lift hroA.zetaTable (by simp [mlkemRoRegions, mlkemData00Bytes_length]) (by decide +kernel),
      hro_lift hroA.keccakRc  (by simp [mlkemRoRegions, mlkemData01Bytes_length]) (by decide +kernel),
      hro_lift hroA.cst16_0   (by simp [mlkemRoRegions, mlkemData02Bytes_length]) (by decide +kernel),
      hro_lift hroA.cst16_1   (by simp [mlkemRoRegions, mlkemData03Bytes_length]) (by decide +kernel),
      hro_lift hroA.cst16_2   (by simp [mlkemRoRegions, mlkemData04Bytes_length]) (by decide +kernel),
      hro_lift hroA.cst16_3   (by simp [mlkemRoRegions, mlkemData05Bytes_length]) (by decide +kernel),
      hro_lift hroA.cst16_4   (by simp [mlkemRoRegions, mlkemData06Bytes_length]) (by decide +kernel),
      hro_lift hroA.cst16_5   (by simp [mlkemRoRegions, mlkemData07Bytes_length]) (by decide +kernel),
      hro_lift hroA.cst16_6   (by simp [mlkemRoRegions, mlkemData08Bytes_length]) (by decide +kernel),
      hro_lift hroA.cst16_7   (by simp [mlkemRoRegions, mlkemData09Bytes_length]) (by decide +kernel),
      hro_lift hroA.cst16_8   (by simp [mlkemRoRegions, mlkemData10Bytes_length]) (by decide +kernel)⟩
    exact ⟨hro_m.1, hro_m.2, hro_m.3, hro_m.4, hro_m.5, hro_m.6, hro_m.7, hro_m.8, hro_m.9,
      hro_m.10, hro_m.11⟩
  · intro hrw_out a hx
    refine hx_p a (fun hxr => ?_) hx
    unfold Memory.perm restrictDom at hxr
    by_cases hda : D a = true
    · simp only [hda, ↓reduceIte] at hxr
      change (m.perm a).x = true at hxr
      by_cases hact : mlkemActiveDom mpl a = true
      · unfold mlkemActiveDom at hact; rw [Bool.or_eq_true] at hact
        rcases hact with hk | hrk
        · unfold mlkemActiveKeep at hk; rw [List.any_eq_true] at hk
          obtain ⟨k, hk_mem, hpk⟩ := hk
          have hkl := of_decide_eq_true ((List.all_eq_true.mp (by decide : (mlkemActiveBlocks.all (· < mlkemMultiLib.blocks.length)) = true)) k hk_mem)
          unfold c2MlkemKeep; rw [List.any_eq_true]
          refine ⟨k, List.mem_range.mpr hkl, ?_⟩
          rwa [blockProgram_extendMlkemMpl_eq mpl t hk_mem]
        · rw [mlkemRoKeep_perm_ro hroA hrk] at hxr; simp [Perm.ro] at hxr
      · rw [hrw_out a hda (Bool.not_eq_true _ |>.mp hact)] at hxr; simp [Perm.rw] at hxr
    · simp [hda] at hxr

private theorem fetch_in_mlkem_not_svc0_msr_local {mpl : MultiPlacement} {P : Program}
    (hpl : mlkemMultiLib.Placeable mpl) (hext : ∀ pc, P.externAt? pc = none)
    {m0 m : Memory} (hcl0 : mlkemMultiLib.CodeLoaded mpl m0)
    (hx_keep : ∀ a, (m0.perm a).x = true → c2MlkemKeep mpl a = true)
    (hkf : m0.KeepsFrozen m) (hperm : m.perm = m0.perm)
    {pc : BitVec 64} {inst : Instr} (hfm : P.fetchMem m pc = some inst) :
    inst.isSvc0 = false ∧ inst.isMsrTpidrEl0 = false := by
  unfold Program.fetchMem at hfm; rw [hext pc] at hfm
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfm
  have hal_pc : pc.toNat % 4 = 0 := by
    by_cases h4 : pc.toNat % 4 = 0
    · exact h4
    · simp [h4] at hfm
  have hce : m.canExec pc 4 = true := by
    by_cases hc : m.canExec pc 4 = true
    · exact hc
    · simp [hal_pc, hc] at hfm
  have hdec : decode (m.read32 pc) = some inst := by simp [hal_pc, hce] at hfm; exact hfm
  have hx_pc : (m0.perm pc).x = true := by
    rw [← hperm]; simp only [Memory.canExec, Memory.allPerm, Bool.and_eq_true] at hce; exact hce.1
  have hk := hx_keep pc hx_pc
  unfold c2MlkemKeep at hk; rw [List.any_eq_true] at hk
  obtain ⟨j, hj_mem, hkp⟩ := hk
  have hj : j < mlkemMultiLib.blocks.length := List.mem_range.mp hj_mem
  let Pj := mlkemMultiLib.blockProgram mpl j
  have hcl_m : Pj.CodeLoaded m := (hcl0 j hj).of_keepsFrozen hkf
  have hPj_al : Pj.base.toNat % 4 = 0 := hcl_m.aligned
  have hPj_nw : Pj.base.toNat + Pj.code.length ≤ 2 ^ 64 := hcl_m.no_wrap
  have hin : (pc - Pj.base).toNat < Pj.code.length := of_decide_eq_true hkp
  have hPj_len4 : Pj.code.length % 4 = 0 := by
    have hbt := (hpl.blocks_ok j hj).len_aligned
    have hplen := CodeBlock.length_patched_of_aligned (mlkemMultiLib.blockPlacement mpl j)
      (blk := (mlkemMultiLib.blockLib j).text) (by rw [mlkemMultiLib.blockLib_text hj]; exact hbt)
    change ((mlkemMultiLib.blockLib j).text.patched (mlkemMultiLib.blockPlacement mpl j)).length % 4 = 0
    rw [hplen, mlkemMultiLib.blockLib_text hj]; exact hbt
  let off := (pc - Pj.base).toNat
  have hpc_eq : pc = Pj.base + BitVec.ofNat 64 off := by dsimp [off]; bv_omega
  have hoff_nat : off = pc.toNat - Pj.base.toNat := by dsimp [off]; bv_omega
  have hoff4 : off % 4 = 0 := by omega
  have hrw : Pj.readWordOff off = some (m.read32 pc) := by
    have hb0 := hcl_m.byte_eq off (by omega); have hb1 := hcl_m.byte_eq (off + 1) (by omega)
    have hb2 := hcl_m.byte_eq (off + 2) (by omega); have hb3 := hcl_m.byte_eq (off + 3) (by omega)
    have ha0 : pc + 0#64 = Pj.base + BitVec.ofNat 64 off := by rw [hpc_eq]; bv_omega
    have ha1 : pc + 1#64 = Pj.base + BitVec.ofNat 64 (off + 1) := by rw [hpc_eq]; bv_omega
    have ha2 : pc + 2#64 = Pj.base + BitVec.ofNat 64 (off + 2) := by rw [hpc_eq]; bv_omega
    have ha3 : pc + 3#64 = Pj.base + BitVec.ofNat 64 (off + 3) := by rw [hpc_eq]; bv_omega
    unfold Program.readWordOff; simp only [hoff4, ne_eq, not_true_eq_false, ↓reduceIte]
    rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega),
      List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega)]
    dsimp only [Memory.read32]; rw [ha0, hb0, ha1, hb1, ha2, hb2, ha3, hb3]
  have hfetch_Pj : Pj.fetch (Pj.base + BitVec.ofNat 64 off) = some inst := by
    have hf := Program.fetch_of_readWordOff (prog := Pj) (off := off) (by omega)
      (by simp [Pj, MultiPlacedLib.blockProgram, PlacedLib.program, Program.hookAtOff?]) hrw
    rwa [hdec] at hf
  have hps_svc : (mlkemMultiLib.blockLib j).text.patchSafe svc0Pat = true := by
    rw [mlkemMultiLib.blockLib_text hj]
    exact (List.all_eq_true.mp mlkemMultiLib_blocks_all_svc0) mlkemMultiLib.blocks[j] (List.getElem_mem hj)
  have hps_msr : (mlkemMultiLib.blockLib j).text.patchSafe msrTpidrEl0Pat = true := by
    rw [mlkemMultiLib.blockLib_text hj]
    exact (List.all_eq_true.mp mlkemMultiLib_blocks_all_msr) mlkemMultiLib.blocks[j] (List.getElem_mem hj)
  have hall_svc := PlacedLib.program_noSvc0_of_patchSafe hps_svc (mlkemMultiLib.blockPlacement mpl j)
  have hall_msr := PlacedLib.program_noMsrTpidrEl0_of_patchSafe hps_msr (mlkemMultiLib.blockPlacement mpl j)
  exact ⟨by simpa using Program.fetch_of_allInstrs hall_svc _ _ hfetch_Pj,
    by simpa using Program.fetch_of_allInstrs hall_msr _ _ hfetch_Pj⟩

private theorem mlkemActiveDom_frozen_ne_rw {mpl : MultiPlacement} {m : Memory}
    (hInvA : mlkemActiveInvMem mpl m) {a : BitVec 64}
    (ha : mlkemActiveDom mpl a = true) :
    m.Frozen a ∧ m.perm a ≠ some .rw := by
  rcases hInvA with ⟨_, hclA, hroA⟩
  unfold mlkemActiveDom at ha; rw [Bool.or_eq_true] at ha
  rcases ha with hk | hrk
  · unfold mlkemActiveKeep at hk; rw [List.any_eq_true] at hk
    obtain ⟨j, hj, hpk⟩ := hk
    have hL := hclA j hj
    have hin : (a - (mlkemMultiLib.blockProgram mpl j).base).toNat <
        (mlkemMultiLib.blockProgram mpl j).code.length := of_decide_eq_true hpk
    have hnw := hL.no_wrap
    have ha_eq : a = (mlkemMultiLib.blockProgram mpl j).base +
        BitVec.ofNat 64 (a - (mlkemMultiLib.blockProgram mpl j).base).toNat := by bv_omega
    have hp := hL.perm_eq _ hin; rw [← ha_eq] at hp
    unfold Memory.Frozen; rw [hp]; exact ⟨rfl, by decide⟩
  · have hp := mlkemRoKeep_perm_ro hroA hrk
    unfold Memory.Frozen; rw [hp]; exact ⟨rfl, by decide⟩

private def ghostOnlyHeap (hf : Heap) : Heap where
  phys _ := none
  auth := hf.auth
  frag := hf.frag
  mapped _ := false

private theorem matches_paint_ghost {h_pre hf : Heap} {m₀ m_t : Memory}
    (hrw : RwOnlyHeap h_pre) (hdisj : h_pre.Disjoint hf) (hmat : (h_pre.union hf).Matches m₀)
    (hcells : ∀ a, (h_pre.phys a).isSome = true → m_t.cells a = m₀.cells a) :
    h_pre.Disjoint (ghostOnlyHeap hf) ∧
    (h_pre.union (ghostOnlyHeap hf)).Matches m_t ∧
    (∀ a, (h_pre.phys a).isSome = true → m₀.perm a = some .rw) := by
  unfold Heap.Disjoint at hdisj ⊢; unfold Heap.Matches at hmat ⊢
  refine ⟨⟨fun _ => Or.inr (Or.inl rfl), hdisj.2.1, hdisj.2.2.1, hdisj.2.2.2.1,
      fun _ => Or.inr rfl⟩, ⟨fun a c hc => ?_, ?_, fun a hm => ?_⟩, fun a hs => ?_⟩
  · unfold Heap.union ghostOnlyHeap at hc; dsimp only at hc
    cases hp : h_pre.phys a with
    | none => rw [hp] at hc; cases hc
    | some cp =>
      rw [hp] at hc; injection hc with hc'; subst hc'
      obtain ⟨b, rfl⟩ := hrw.1 a cp hp
      have hu : (h_pre.union hf).phys a = some (.rw b) := by unfold Heap.union; simp [hp]
      have hm0 := hmat.1 a (.rw b) hu
      have hca := hcells a (by simp [hp])
      simp only [Memory.read8, Memory.perm, Memory.isLazyFree, hca]; exact hm0
  · obtain ⟨bound, hb⟩ := hmat.2.1
    exact ⟨bound, fun γ hγ k => by simpa [Heap.union, ghostOnlyHeap] using hb γ hγ k⟩
  · unfold Heap.union ghostOnlyHeap at hm; dsimp only at hm
    rw [hrw.2 a] at hm; cases hm
  · cases hp : h_pre.phys a with
    | none => simp [hp] at hs
    | some cp =>
      obtain ⟨b, rfl⟩ := hrw.1 a cp hp
      have hu : (h_pre.union hf).phys a = some (.rw b) := by unfold Heap.union; simp [hp]
      exact (hmat.1 a (.rw b) hu).2.1

private theorem rejoin_post_frame {mpl : MultiPlacement} {h_pre h_post hf : Heap}
    {m₀ m_i mf_i mf : Memory}
    (hrw_pre : RwOnlyHeap h_pre) (hdisj_pre : h_pre.Disjoint hf)
    (hmat_pre : (h_pre.union hf).Matches m₀) (hInvA : mlkemActiveInvMem mpl m₀)
    (hrw_post : RwOnlyHeap h_post) (hdisj_post : h_post.Disjoint (ghostOnlyHeap hf))
    (hmat_post : (h_post.union (ghostOnlyHeap hf)).Matches mf_i)
    (hperm_i : mf_i.perm = m_i.perm)
    (hne_rw_out : ∀ a, (mlkemActiveDom mpl a || (h_pre.phys a).isSome) = false → m_i.perm a ≠ some .rw)
    (hcells_in : ∀ a, (mlkemActiveDom mpl a || (h_pre.phys a).isSome) = true → mf_i.cells a = mf.cells a)
    (hcells_out : ∀ a, (mlkemActiveDom mpl a || (h_pre.phys a).isSome) = false → mf.cells a = m₀.cells a)
    (hkf_mf : m₀.KeepsFrozen mf) (hperm_mf : mf.perm = m₀.perm) (hanon_mf : mf.isAnon = m₀.isAnon) :
    h_post.Disjoint hf ∧ (h_post.union hf).Matches mf := by
  unfold Heap.Disjoint at hdisj_pre hdisj_post ⊢
  unfold Heap.Matches at hmat_pre hmat_post ⊢
  have hpost_dom : ∀ a c, h_post.phys a = some c →
      ∃ b, c = .rw b ∧ (mf.read8 a = b ∧ mf.perm a = some .rw ∧ mf.isLazyFree a = false) ∧ hf.phys a = none := by
    intro a c hpc
    obtain ⟨b, rfl⟩ := hrw_post.1 a c hpc
    have hu : (h_post.union (ghostOnlyHeap hf)).phys a = some (.rw b) := by unfold Heap.union; simp [hpc]
    have hmi := hmat_post.1 a (.rw b) hu
    have hpi : m_i.perm a = some .rw := hperm_i ▸ hmi.2.1
    have hD : (mlkemActiveDom mpl a || (h_pre.phys a).isSome) = true := by
      cases hd : mlkemActiveDom mpl a || (h_pre.phys a).isSome
      · exact absurd hpi (hne_rw_out a hd)
      · rfl
    have hcm : mf_i.cells a = mf.cells a := hcells_in a hD
    have hmf_a : mf.read8 a = b ∧ mf.perm a = some .rw ∧ mf.isLazyFree a = false := by
      simpa only [Memory.read8, Memory.perm, Memory.isLazyFree, hcm] using hmi
    have hp0 : m₀.perm a = some .rw := hperm_mf ▸ hmf_a.2.1
    have hact_f : mlkemActiveDom mpl a = false := by
      cases ha : mlkemActiveDom mpl a
      · rfl
      · exact absurd hp0 (mlkemActiveDom_frozen_ne_rw hInvA ha).2
    rw [hact_f, Bool.false_or] at hD
    cases hpre_a : h_pre.phys a with
    | none => simp [hpre_a] at hD
    | some cp =>
      obtain ⟨bp, rfl⟩ := hrw_pre.1 a cp hpre_a
      have hhf_none : hf.phys a = none := by
        rcases hdisj_pre.1 a with h1 | h2 | ⟨_, h1, _⟩
        · rw [hpre_a] at h1; cases h1
        · exact h2
        · rw [hpre_a] at h1; cases h1
      exact ⟨b, rfl, hmf_a, hhf_none⟩
  refine ⟨⟨fun a => ?_, hdisj_post.2.1, hdisj_post.2.2.1, hdisj_post.2.2.2.1,
      fun a => Or.inl (hrw_post.2 a)⟩, ⟨fun a c hc => ?_, ?_, fun a hm => ?_⟩⟩
  · cases hpc : h_post.phys a with
    | none => exact Or.inl rfl
    | some c => exact Or.inr (Or.inl (hpost_dom a c hpc).choose_spec.2.2)
  · unfold Heap.union at hc; dsimp only at hc
    cases hpc : h_post.phys a with
    | some cp =>
      rw [hpc] at hc; injection hc with hc'; subst hc'
      obtain ⟨b, rfl, hmf_a, _⟩ := hpost_dom a cp hpc
      exact hmf_a
    | none =>
      rw [hpc] at hc; dsimp only at hc
      have hpre_none : h_pre.phys a = none := by
        cases hp : h_pre.phys a with
        | none => rfl
        | some cp =>
          obtain ⟨bp, rfl⟩ := hrw_pre.1 a cp hp
          rcases hdisj_pre.1 a with h1 | h2 | ⟨_, h1, _⟩
          · rw [hp] at h1; cases h1
          · rw [hc] at h2; cases h2
          · rw [hp] at h1; cases h1
      have hu0 : (h_pre.union hf).phys a = some c := by unfold Heap.union; simp [hpre_none, hc]
      have hm0 := hmat_pre.1 a c hu0
      have heq : mf.read8 a = m₀.read8 a ∧ mf.perm a = m₀.perm a ∧ mf.isLazyFree a = m₀.isLazyFree a := by
        cases ha : mlkemActiveDom mpl a
        · have hD : (mlkemActiveDom mpl a || (h_pre.phys a).isSome) = false := by simp [ha, hpre_none]
          have hco := hcells_out a hD
          simp [Memory.read8, Memory.perm, Memory.isLazyFree, hco]
        · obtain ⟨hb', hp', hlf', _⟩ := hkf_mf a (mlkemActiveDom_frozen_ne_rw hInvA ha).1
          exact ⟨hb', hp', hlf'⟩
      cases c <;> simpa only [heq.1, heq.2.1, heq.2.2] using hm0
  · obtain ⟨bound, hb⟩ := hmat_post.2.1
    exact ⟨bound, fun γ hγ k => by simpa [Heap.union, ghostOnlyHeap] using hb γ hγ k⟩
  · unfold Heap.union at hm; dsimp only at hm
    rw [hrw_post.2 a, Bool.false_or] at hm
    have hm0 : (h_pre.union hf).mapped a = true := by
      unfold Heap.union; dsimp only; rw [hrw_pre.2 a, Bool.false_or]; exact hm
    obtain ⟨hpm, han⟩ := hmat_pre.2.2 a hm0
    exact ⟨(congrFun hperm_mf a).symm ▸ hpm, (congrFun hanon_mf a).symm ▸ han⟩

private theorem vmPreserved_of_nonSyscall_tpidr_local {s0 sf : State}
    (hnsp : ProofLib.NonSyscallPreserved s0 sf) (htp : sf.tpidrEl0 = s0.tpidrEl0) :
    VmPreserved s0 sf := by
  have hpool : PoolPreserved s0 sf := ⟨hnsp.2.2.2.1, hnsp.2.2.1, htp⟩
  have hfds : FdsHiFrame s0 sf := fun _ _ _ => by rw [hnsp.2.2.2.2.2.2]
  exact ⟨hpool, hnsp.2.2.2.2.1, fun a => congrFun hnsp.2.1 a, hfds⟩

private theorem run_single_phantom {j : Nat} (hj : j ∈ mlkemActiveBlocks)
    (hj_lt : j < mlkemMultiLib.blocks.length)
    {α β : Type} {blockSpec : MultiPlacement → Spec β} {master : Spec α}
    (mpl : MultiPlacement) (blk_ok : MlKemBlockOk j blockSpec)
    (sim : ∀ mpl', SpecSimulates (blockSpec mpl') (withMlKemRoOk mpl' master))
    (m_pan : master.onPanic = fun _ _ _ => ⌜False⌝)
    (m_ex : master.onExit = fun _ _ _ _ => ⌜False⌝)
    (m_oom : master.onOom = fun _ _ _ => ⌜False⌝)
    (m_pre_mem : ∀ x (s : State) (m : Memory), master.pre x (s.setMem m) = master.pre x s)
    {x : α} {s0 : State} {h_pre hf : Heap}
    (hpc : s0.pc = mpl.base j) (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hInvA : mlkemActiveInvMem mpl s0.mem) (hrw_pre : RwOnlyHeap h_pre)
    (hdisj_pre : h_pre.Disjoint hf) (hmat_pre : (h_pre.union hf).Matches s0.mem)
    (hpre_holds : (master.pre x s0).holds h_pre)
    {t : Nat} (ht : t < 8)
    (hw : windowDisjointDom (fun a => mlkemActiveDom mpl a || (h_pre.phys a).isSome) t) :
    let D := fun a => mlkemActiveDom mpl a || (h_pre.phys a).isSome
    let m_t := paintPhantom mpl D t s0.mem
    let R_g : SepProp := ⟨fun h => h = ghostOnlyHeap hf⟩
    (∀ a, D a = true → m_t.cells a = s0.mem.cells a) ∧
    (∀ a, D a = false → ¬ InRegion (phantomWindowBase t) phantomWindowLen a → m_t.perm a = none) ∧
    (∀ a, D a = false → m_t.perm a ≠ some .rw) ∧
    mlkemMultiLib.Placeable (extendMlkemMpl mpl t) ∧
    mlkemMultiLib.CodeLoaded (extendMlkemMpl mpl t) m_t ∧
    (∀ a, (m_t.perm a).x = true → c2MlkemKeep (extendMlkemMpl mpl t) a = true) ∧
    ∃ sf_t : State,
      Steps (mlkemMultiLib.blockProgram mpl j) (s0.setMem m_t) sf_t ∧
      Returned (s0.setMem m_t) sf_t ∧
      CallingConventionPreserved (s0.setMem m_t) sf_t ∧
      (sf_t.mem ⊨ master.post x (s0.setMem m_t) sf_t ∗ R_g) := by
  intro D m_t R_g
  obtain ⟨hcells_t, hnone_t, hne_rw_t, hcl_t, hro_t, hx_fn⟩ :=
    paintPhantom_ok ht hw hInvA (fun _ ha => (Bool.or_eq_true _ _).mpr (Or.inl ha))
  obtain ⟨hdisj_g, hmat_g, hpre_rw0⟩ := matches_paint_ghost hrw_pre hdisj_pre hmat_pre
    (fun a hs => hcells_t a ((Bool.or_eq_true _ _).mpr (Or.inr hs)))
  have hx_t : ∀ a, (m_t.perm a).x = true → c2MlkemKeep (extendMlkemMpl mpl t) a = true :=
    hx_fn fun a hda hact => hpre_rw0 a
      ((Bool.or_eq_true _ _).mp hda |>.resolve_left (by rw [hact]; decide))
  let mpl_t := extendMlkemMpl mpl t
  have hpl_t : mlkemMultiLib.Placeable mpl_t := hInvA.1.placeable_ext t (List.mem_range.mpr ht)
  let _ : MlKemPlacement := ⟨mpl_t, hpl_t⟩
  have hSubBlk : subroutine_ok (mlkemMultiLib.blockProgram mpl j) (mpl.base j)
      (mlkemMultiLib.withCodeLoaded mpl_t (blockSpec mpl_t)) := by
    have h0 := @blk_ok ⟨mpl_t, hpl_t⟩
    dsimp only [ToBaseSpec.toSpec, mlkemMpl] at h0
    rwa [blockProgram_extendMlkemMpl_eq mpl t hj, extendMlkemMpl_base_eq mpl t hj] at h0
  let s0_t := s0.setMem m_t
  have hpre_t : s0_t.mem ⊨ (withMlKemRoOk mpl_t master).pre x s0_t ∗ R_g := by
    dsimp only [withMlKemRoOk, s0_t]; rw [sm_mem, m_pre_mem, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hro_t, SepProp.satisfies_iff.mpr ⟨h_pre.union (ghostOnlyHeap hf),
      SepProp.holds_sepConj_iff.mpr ⟨h_pre, ghostOnlyHeap hf, hdisj_g, rfl, hpre_holds, rfl⟩, hmat_g⟩⟩
  obtain ⟨y, R₁, hyPre, hyMap⟩ := sim mpl_t x R_g s0_t hpre_t
  have hyPreC : s0_t.mem ⊨ (mlkemMultiLib.withCodeLoaded mpl_t (blockSpec mpl_t)).pre y s0_t ∗ R₁ := by
    dsimp only [MultiPlacedLib.withCodeLoaded]
    rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨by dsimp only [s0_t]; rw [sm_mem]; exact hcl_t, hyPre⟩
  have hLi_t : (mlkemMultiLib.blockProgram mpl j).CodeLoaded s0_t.mem := by
    dsimp only [s0_t]; rw [sm_mem, ← blockProgram_extendMlkemMpl_eq mpl t hj]; exact hcl_t j hj_lt
  obtain ⟨sf_t, hsteps_t, hout_blk⟩ :=
    subroutine_ok_elim_steps_outcome hSubBlk y R₁ s0_t
      (by dsimp only [s0_t]; rw [sm_pc]; exact hpc)
      (by dsimp only [s0_t]; rw [sm_st]; exact hrun)
      hyPreC (by dsimp only [s0_t]; rw [sm_spa]; exact hsp) hLi_t
  refine ⟨hcells_t, hnone_t, hne_rw_t, hpl_t, hcl_t, hx_t, ?_⟩
  rcases hyMap sf_t hout_blk with ⟨hr, hc, hp⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · exact ⟨sf_t, hsteps_t, hr, hc, hp⟩
  · dsimp only [withMlKemRoOk] at hp; rw [m_pan] at hp; exact False.elim (not_satisfies_false_sepConj hp)
  · dsimp only [withMlKemRoOk] at he; rw [m_ex] at he; exact False.elim (not_satisfies_false_sepConj he)
  · dsimp only [withMlKemRoOk] at ho; rw [m_oom] at ho; exact False.elim (not_satisfies_false_sepConj ho)

/-- Execute any `MlKemBlockOk j` (`j ∈ mlkemActiveBlocks`) on `emptyStdProg` under
    `mlkemActiveInvMem mpl s0.mem` (without requiring `mlkemS5Blocks` to be placed away from
    caller buffers), obtaining `h2fsgen_StepsVisitedIn (mlkemActiveKeep mpl) emptyStdProg s0 sf`
    together with full postcondition, `KeepsFrozen`, `NonSyscallPreserved`, and `VmPreserved`. -/
theorem mlkemActive_run_visitedIn {j : Nat} (hj : j ∈ mlkemActiveBlocks)
    {α β : Type} {blockSpec : MultiPlacement → Spec β} {master : Spec α}
    (mpl : MultiPlacement)
    (blk_ok : MlKemBlockOk j blockSpec)
    (sim : ∀ mpl', SpecSimulates (blockSpec mpl') (withMlKemRoOk mpl' master))
    (m_pan : master.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (m_ex : master.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (m_oom : master.onOom = fun _ _ _ => ⌜False⌝ := by rfl)
    (m_pre_mem : ∀ x (s : State) (m : Memory),
      master.pre x (s.setMem m) = master.pre x s := by intro _ s _; cases s; rfl)
    (m_post_mem : ∀ x (s0 sf : State) (m0 mf : Memory),
      master.post x (s0.setMem m0) (sf.setMem mf) = master.post x s0 sf := by
      intro _ s0 sf _ _; cases s0; cases sf; rfl)
    (m_pre_rw : ∀ x s h, (master.pre x s).holds h → RwOnlyHeap h)
    (m_pre_bdd : ∀ x s h, (master.pre x s).holds h → BoundedHeapIntervals 6 0x10000 h)
    (m_post_rw : ∀ x s0 sf h, (master.post x s0 sf).holds h → RwOnlyHeap h)
    {x : α} {R : SepProp} {s0 : State}
    (hpc : s0.pc = mpl.base j) (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hInvA : mlkemActiveInvMem mpl s0.mem)
    (hpreM : s0.mem ⊨ master.pre x s0 ∗ R) :
    ∃ sf : State,
      h2fsgen_StepsVisitedIn (mlkemActiveKeep mpl) emptyStdProg s0 sf ∧
      Returned s0 sf ∧
      CallingConventionPreserved s0 sf ∧
      (sf.mem ⊨ master.post x s0 sf ∗ R) ∧
      s0.mem.KeepsFrozen sf.mem ∧
      ProofLib.NonSyscallPreserved s0 sf ∧
      sf.tpidrEl0 = s0.tpidrEl0 ∧
      VmPreserved s0 sf := by
  have hall_lt : (mlkemActiveBlocks.all (· < mlkemMultiLib.blocks.length)) = true := by decide
  have hj_lt : j < mlkemMultiLib.blocks.length := of_decide_eq_true (List.all_eq_true.mp hall_lt j hj)
  rcases SepProp.satisfies_iff.mp hpreM with ⟨_, h_tot_holds, hmat_pre⟩
  rcases SepProp.holds_sepConj_iff.mp h_tot_holds with ⟨h_pre, hf, hdisj_pre, rfl, hpre_holds, hf_holds⟩
  have hrw_pre : RwOnlyHeap h_pre := m_pre_rw x s0 h_pre hpre_holds
  obtain ⟨t₁, t₂, ht₁, ht₂, hne_t, hw₁, hw₂⟩ :=
    exists_two_disjoint_windows hInvA.1 (m_pre_bdd x s0 h_pre hpre_holds)
  obtain ⟨hcells₁, hnone₁, hne_rw₁, hpl₁, hcl₁, hx₁, sf₁, hsteps₁, hret₁, hcc₁, hpost₁⟩ :=
    run_single_phantom hj hj_lt mpl blk_ok sim m_pan m_ex m_oom m_pre_mem
      hpc hrun hsp hInvA hrw_pre hdisj_pre hmat_pre hpre_holds ht₁ hw₁
  obtain ⟨hcells₂, hnone₂, hne_rw₂, _, _, _, sf₂, hsteps₂, hret₂, hcc₂, hpost₂⟩ :=
    run_single_phantom hj hj_lt mpl blk_ok sim m_pan m_ex m_oom m_pre_mem
      hpc hrun hsp hInvA hrw_pre hdisj_pre hmat_pre hpre_holds ht₂ hw₂
  let D := fun a => mlkemActiveDom mpl a || (h_pre.phys a).isSome
  let m₁ := paintPhantom mpl D t₁ s0.mem
  let m₂ := paintPhantom mpl D t₂ s0.mem
  have hag : AgreeState D s0.mem (s0.setMem m₁) (s0.setMem m₂) s0 := by
    refine ⟨by rw [sm_mem], by rw [sm_mem], ?_⟩
    rw [sm_mem, sm_mem]
    refine ⟨⟨fun a ha => ⟨hcells₁ a ha, hcells₂ a ha⟩, fun a ha => ?_⟩, fun _ _ => rfl, rfl⟩
    by_cases hin1 : InRegion (phantomWindowBase t₁) phantomWindowLen a
    · exact Or.inr (hnone₂ a ha fun hin2 => phantomWindows_disjoint ht₁ ht₂ hne_t hin1 hin2)
    · exact Or.inl (hnone₁ a ha hin1)
  obtain ⟨_, _, hpre_rw0⟩ := matches_paint_ghost hrw_pre hdisj_pre hmat_pre
    (fun a hs => hcells₁ a (by dsimp only; rw [hs, Bool.or_true]))
  have hD_exec_keep : ∀ pc, D pc = true → (s0.mem.perm pc).x = true → mlkemActiveKeep mpl pc = true := by
    intro pc hd hx0
    cases hk : mlkemActiveKeep mpl pc
    · exfalso
      dsimp only [D, mlkemActiveDom] at hd
      rw [hk, Bool.false_or, Bool.or_eq_true] at hd
      rcases hd with hrk | hph
      · rw [mlkemRoKeep_perm_ro hInvA.2.2 hrk] at hx0; simp [Perm.ro] at hx0
      · rw [hpre_rw0 pc hph] at hx0; simp [Perm.rw] at hx0
    · rfl
  have hext := externAt?_mlkemBlockProgram_ext_none mpl hj_lt (fun _ => none)
  obtain ⟨sf, hvis_sf, hkf_sf, hnsp_sf, htp_sf, hanon_sf, hout_dom, hbranch⟩ :=
    steps_two_runs_locality (m₁₀ := m₁) (m₂₀ := m₂) hext hD_exec_keep
      (fun m pc inst hkf hperm hfm => fetch_in_mlkem_not_svc0_msr_local hpl₁ hext hcl₁ hx₁ hkf hperm hfm)
      hag rfl (by rw [sm_mem]; exact Memory.KeepsFrozen.refl m₁) (by rw [sm_mem]) (by rw [sm_mem])
      hsteps₁ hret₁.2.2 hsteps₂ hret₂.2.2
  have finish_branch : ∀ {m_i : Memory} {sfi : State},
      Returned (s0.setMem m_i) sfi → CallingConventionPreserved (s0.setMem m_i) sfi →
      (sfi.mem ⊨ master.post x (s0.setMem m_i) sfi ∗ ⟨fun h => h = ghostOnlyHeap hf⟩) →
      (∀ a, D a = false → m_i.perm a ≠ some .rw) →
      sfi = sf.setMem sfi.mem → sfi.mem.perm = m_i.perm →
      (∀ a, D a = true → sfi.mem.cells a = sf.mem.cells a) →
      Returned s0 sf ∧ CallingConventionPreserved s0 sf ∧ (sf.mem ⊨ master.post x s0 sf ∗ R) := by
    intro m_i sfi hret_i hcc_i hpost_i hne_rw_i hsfi hperm_i hcells_in
    have hret_sf : Returned s0 sf := by
      rcases hret_i with ⟨r1, r2, r3⟩; rw [hsfi] at r1 r2 r3
      exact ⟨by cases s0; cases sf; exact r1, by cases s0; cases sf; exact r2, by cases sf; exact r3⟩
    have hcc_sf : CallingConventionPreserved s0 sf := by
      rcases hcc_i with ⟨c1, c2⟩; rw [hsfi] at c1 c2
      exact ⟨by cases s0; cases sf; exact c1, by cases s0; cases sf; exact c2⟩
    have hpost_eq : master.post x (s0.setMem m_i) sfi = master.post x s0 sf := by
      rw [hsfi, m_post_mem]
    rw [hpost_eq] at hpost_i
    rcases SepProp.satisfies_iff.mp hpost_i with ⟨_, hp_holds, hmat_post⟩
    rcases SepProp.holds_sepConj_iff.mp hp_holds with ⟨h_post, hg', hdisj_post, rfl, hpost_holds, hg_holds⟩
    have hge : hg' = ghostOnlyHeap hf := hg_holds
    subst hge
    obtain ⟨hdisj_re, hmat_re⟩ := rejoin_post_frame hrw_pre hdisj_pre hmat_pre hInvA
      (m_post_rw x s0 sf h_post hpost_holds) hdisj_post hmat_post hperm_i hne_rw_i hcells_in
      hout_dom hkf_sf hnsp_sf.2.1 hanon_sf
    exact ⟨hret_sf, hcc_sf, SepProp.satisfies_iff.mpr ⟨h_post.union hf,
      SepProp.holds_sepConj_iff.mpr ⟨h_post, hf, hdisj_re, rfl, hpost_holds, hf_holds⟩, hmat_re⟩⟩
  have hvm : VmPreserved s0 sf := vmPreserved_of_nonSyscall_tpidr_local hnsp_sf htp_sf
  rcases hbranch with ⟨hsf1, hp1, hc1⟩ | ⟨hsf2, hp2, hc2⟩
  · obtain ⟨hret, hcc, hpost⟩ := finish_branch hret₁ hcc₁ hpost₁ hne_rw₁ hsf1 hp1 hc1
    exact ⟨sf, hvis_sf, hret, hcc, hpost, hkf_sf, hnsp_sf, htp_sf, hvm⟩
  · obtain ⟨hret, hcc, hpost⟩ := finish_branch hret₂ hcc₂ hpost₂ hne_rw₂ hsf2 hp2 hc2
    exact ⟨sf, hvis_sf, hret, hcc, hpost, hkf_sf, hnsp_sf, htp_sf, hvm⟩

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeMlKemLocality
