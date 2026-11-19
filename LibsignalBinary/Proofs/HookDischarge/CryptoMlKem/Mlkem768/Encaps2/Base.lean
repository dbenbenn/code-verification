/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.GenPlacedFetches
public import ProofLib.ProgramReflection
public import LibsignalBinary.Specifications.LibsignalSpqrV1.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import LibsignalBinary.Proofs.HookDischarge.Libc.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.RustStd.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 -- proof-setup: allow-public-import
public meta import ProofLib.ProgramReflection
public meta import ProofLib.GenDecodes
public meta import ProofLib.GenPlacedFetches
import ProofLib.SepLogic.WP.StepsProcess
import ProofLib.SepLogic.WPFrozen

/-!
# `encapsulate2` (`B20`) — Block Setup, Specifications, Callee-Saved Frame, & `.rodata` Steps

1. Block 20 (`mlkem768::incremental::encapsulate2`, `2,769` words) `PlacedLib` & `WordTree`.
2. `sepWP_seq_env` segment composition combinator preserving `CodeLoaded` and `MlKemRoOk`.
3. Core & caller-projection specifications (`mlkemEncaps2RawSpec`, `mlkemEncaps2CoreSpec`,
   `mlkemEncaps2ProjSpec`) and `SpecSimulates` bridge.
4. Spilled callee-saved frame (`SavedFrame20`, `UnspilledSaved20`) at `[sp0 - 128, sp0)`.
5. `ZETA_TABLE` lookup agreement (`zetaTableAt_eq`, `zetaTableAt_zext32_ne_32768`) and `.rodata`
   read step lemmas (`step_ldrQ128_ro`, `step_ldrh16_ro`, `step_ld1r4h_ro`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open scoped ProofLib.ProgramReflection
open ProofLib.ProgramReflection (WordTree)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (RoDataAt SpecSimulates)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (
  mlkemData00Bytes
  mlkemMultiLib
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (
  MlKemRoOk
  cst16Vec
  zetaTableAt
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemPlacement
  mlkemMpl
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (withNonSyscallPreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  bitRev7
  bitsToBytes
  byteEncode
  fipsZetas
  mlkem768Encaps2List
  mlkemQ
  neonCompressSerialize4
  toByteVec
  zetasTimesMontgomeryR
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (
  dup4hLow
  getLsbD_readLE
)

/-! ## 1. Block 20 (`encapsulate2`) `PlacedLib` & `WordTree` Setup -/

@[expose] def blkLib20 : PlacedLib := mlkemMultiLib.blockLib 20
@[expose] def blkPl20 [MlKemPlacement] : Placement := mlkemMultiLib.blockPlacement mlkemMpl 20
theorem blkPlaceable20 [MlKemPlacement] : blkLib20.Placeable blkPl20 :=
  mlkemMultiLib.placeable_blockLib (by decide) MlKemPlacement.placeable
@[expose] def blkPC20 [MlKemPlacement] : Program := blkLib20.program blkPl20
@[expose] def blkProg20 : Program := { code := blkLib20.text.code, symbols := blkLib20.text.symbols }
@[expose] def blkTree20 : WordTree := word_tree_of% blkProg20

set_option maxRecDepth 30000 in
theorem blk20_code_eq : blkLib20.text.code = blkTree20.toBytes := by rfl_kernel

theorem blk20_tree_size : blkTree20.checkSize? = some 2769 := by rfl_kernel

/-! ## 2. Segment Composition Combinator -/

/-- Sequence two `SepWP` segments while preserving `CodeLoaded` and `MlKemRoOk` across `KeepsFrozen`
    transitions. -/
theorem sepWP_seq_env {prog : Program} {mid target : BitVec 64} {s : State}
    {P : SepProp} {post1 post2 : State → SepProp → Prop} {mpl : MultiPlacement}
    (hcl : mlkemMultiLib.CodeLoaded mpl s.mem)
    (hro : MlKemRoOk mpl s.mem)
    (h1 : SepWP prog mid s P post1)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running →
      mlkemMultiLib.CodeLoaded mpl sm.mem → MlKemRoOk mpl sm.mem →
      post1 sm Pm → SepWP prog target sm Pm post2) :
    SepWP prog target s P post2 :=
  SepWP.seq
    (SepWP.mono_frozen
      (post' := fun sm Pm =>
        mlkemMultiLib.CodeLoaded mpl sm.mem ∧ MlKemRoOk mpl sm.mem ∧ post1 sm Pm)
      (Φ := fun m => mlkemMultiLib.CodeLoaded mpl m ∧ MlKemRoOk mpl m)
      (fun _ _ ⟨hc, hr⟩ hkf => ⟨hc.of_keepsFrozen hkf, hr.of_keepsFrozen hkf⟩)
      ⟨hcl, hro⟩ h1
      (fun _ _ _ _ ⟨hc, hr⟩ hp1 => ⟨hc, hr, hp1⟩))
    (fun sm Pm hpc hrun ⟨hc, hr, hp1⟩ => h2 sm Pm hpc hrun hc hr hp1)

/-! ## 3. Core & Caller-Projection Specifications -/

@[expose] def withMlKemRoOk {α : Type} (mpl : MultiPlacement) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s0 => ⌜MlKemRoOk mpl s0.mem⌝ ∗ spec.pre x s0 }

/-- Tight-stack (`6128 = 6000 + 128` bytes) raw contract for `B20` (`encapsulate2`) prior to
    `NonSyscallPreserved` lifting. -/
@[expose] def mlkemEncaps2RawSpec (mpl : MultiPlacement) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8)) where
  pre := fun (ret, esA, es, ekA, ek) s0 =>
    ⌜s0.readReg64 .x8 = ret ∧
      s0.readReg64 .x0 = esA ∧
      s0.readReg64 .x1 = ekA ∧
      es.length = 2080 ∧
      ek.length = 1152 ∧
      MlKemRoOk mpl s0.mem⌝ ∗
      (esA ↦ₛ es) ∗ (ekA ↦ₛ ek) ∗ memRegion ret 128 ∗ stackAt s0.sp 6128
  post := fun (ret, esA, es, ekA, ek) s0 _sf =>
    (esA ↦ₛ es) ∗ (ekA ↦ₛ ek) ∗ (ret ↦ₛ mlkem768Encaps2List es ek) ∗ stackAt s0.sp 6128
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Tight-stack (`6128` bytes) core contract for `B20` (`encapsulate2`) with `NonSyscallPreserved`. -/
@[expose] def mlkemEncaps2CoreSpec (mpl : MultiPlacement) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8)) :=
  withNonSyscallPreserved (mlkemEncaps2RawSpec mpl)

@[simp] theorem mlkem768Encaps2List_length (es ek : List (BitVec 8)) :
    (mlkem768Encaps2List es ek).length = 128 := by
  simp [mlkem768Encaps2List, neonCompressSerialize4, byteEncode, bitsToBytes]

theorem toByteVec_toList_of_length {n : Nat} {bs : List (BitVec 8)} (h : bs.length = n) :
    (toByteVec n bs).toList = bs := by
  apply List.ext_getElem
  · simp [toByteVec, List.Vector.toList, h]
  · intro i h1 h2
    simp [toByteVec, List.Vector.toList, List.getD_eq_getElem?_getD, h2]

/-- Polymorphic caller-struct projection spec matching `Hooks.mlkemEncaps2Spec K` by `rfl`
    when instantiated with `MlkemEncaps2Call` projections. -/
@[expose] def mlkemEncaps2ProjSpec (K : MlKem) {C : Type}
    (ret : C → BitVec 64)
    (esA : C → BitVec 64) (es : C → List.Vector (BitVec 8) 2080)
    (ekA : C → BitVec 64) (ek : C → List.Vector (BitVec 8) 1152) : Spec C where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = ret x ∧ s.readReg64 .x0 = esA x ∧ s.readReg64 .x1 = ekA x⌝ ∗
      (esA x ↦ₛ (es x).toList) ∗ (ekA x ↦ₛ (ek x).toList) ∗
      memRegion (ret x) 128 ∗ stackAt s.sp extHookStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (esA x ↦ₛ (es x).toList) ∗ (ekA x ↦ₛ (ek x).toList) ∗
      (ret x ↦ₛ (K.encaps2 (es x) (ek x)).toList) ∗
      stackAt s0.sp extHookStack

theorem mlkemEncaps2Core_simulates_proj (K : MlKem)
    (hK : ∀ es ek, K.encaps2 es ek = toByteVec 128 (mlkem768Encaps2List es.toList ek.toList))
    {C : Type}
    (ret : C → BitVec 64)
    (esA : C → BitVec 64) (es : C → List.Vector (BitVec 8) 2080)
    (ekA : C → BitVec 64) (ek : C → List.Vector (BitVec 8) 1152) (mpl : MultiPlacement) :
    SpecSimulates (mlkemEncaps2CoreSpec mpl)
      (withMlKemRoOk mpl (keepsFs (mlkemEncaps2ProjSpec K ret esA es ekA ek))) := by
  refine SpecSimulates.of_map ?_
  intro y R s0 hm
  dsimp only [withMlKemRoOk, keepsFs, mlkemEncaps2ProjSpec] at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hro, hm⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hx8, hx0, hx1⟩, hm⟩
  rw [stackAt_shrink s0.sp extHookStack 6128 (by decide)] at hm
  set slack := memRegion (s0.sp - BitVec.ofNat 64 extHookStack) (extHookStack - 6128)
  refine ⟨(ret y, esA y, (es y).toList, ekA y, (ek y).toList), slack ∗ R, ?_, ?_⟩
  · dsimp only [mlkemEncaps2CoreSpec, withNonSyscallPreserved, mlkemEncaps2RawSpec]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx8, hx0, hx1, (es y).toList_length, (ek y).toList_length, hro⟩, ?_⟩
    rw [sepConj_comm slack (stackAt s0.sp 6128),
      sepConj_assoc (stackAt s0.sp 6128) slack R] at hm
    exact hm
  · intro sf _ _ hpost
    dsimp only [mlkemEncaps2CoreSpec, withNonSyscallPreserved, mlkemEncaps2RawSpec] at hpost
    dsimp only [withMlKemRoOk, keepsFs, mlkemEncaps2ProjSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hnsp, hpost⟩
    have htr : sf.trace = s0.trace := hnsp.1
    have hfs : sf.fs = s0.fs := hnsp.2.2.2.2.2.2
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hfs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    rw [hK, toByteVec_toList_of_length (mlkem768Encaps2List_length _ _)]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc] at hpost ⊢
    rw [← sepConj_assoc (stackAt s0.sp 6128) slack R,
      sepConj_comm (stackAt s0.sp 6128) slack,
      ← stackAt_shrink s0.sp extHookStack 6128 (by decide)] at hpost
    exact hpost

/-! ## 4. Spilled Callee-Saved Frame (`[sp0 - 128, sp0)`) -/

/-- Spilled callee-saved registers (`d15..d8`, `x29, x30`, `x28, x23..x19`) at `[sp0 - 128, sp0)`. -/
@[expose] def SavedFrame20 (sp0 : BitVec 64) (s0 : State) : SepProp :=
  ((sp0 - 128#64) ↦₆₄ (s0.readVReg128 15#5).truncate 64) ∗
  ((sp0 - 120#64) ↦₆₄ (s0.readVReg128 14#5).truncate 64) ∗
  ((sp0 - 112#64) ↦₆₄ (s0.readVReg128 13#5).truncate 64) ∗
  ((sp0 - 104#64) ↦₆₄ (s0.readVReg128 12#5).truncate 64) ∗
  ((sp0 - 96#64)  ↦₆₄ (s0.readVReg128 11#5).truncate 64) ∗
  ((sp0 - 88#64)  ↦₆₄ (s0.readVReg128 10#5).truncate 64) ∗
  ((sp0 - 80#64)  ↦₆₄ (s0.readVReg128 9#5).truncate 64) ∗
  ((sp0 - 72#64)  ↦₆₄ (s0.readVReg128 8#5).truncate 64) ∗
  ((sp0 - 64#64)  ↦₆₄ s0.readReg64 .fp) ∗
  ((sp0 - 56#64)  ↦₆₄ s0.readReg64 .lr) ∗
  ((sp0 - 48#64)  ↦₆₄ s0.readReg64 .x28) ∗
  ((sp0 - 40#64)  ↦₆₄ s0.readReg64 .x23) ∗
  ((sp0 - 32#64)  ↦₆₄ s0.readReg64 .x22) ∗
  ((sp0 - 24#64)  ↦₆₄ s0.readReg64 .x21) ∗
  ((sp0 - 16#64)  ↦₆₄ s0.readReg64 .x20) ∗
  ((sp0 - 8#64)   ↦₆₄ s0.readReg64 .x19)

/-- Unspilled callee-saved registers (`x24..x27`) never modified by `B20`. -/
@[expose] def UnspilledSaved20 (s0 s : State) : Prop :=
  s.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5) ∧
  s.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5) ∧
  s.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) ∧
  s.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5)

theorem UnspilledSaved20.refl (s0 : State) : UnspilledSaved20 s0 s0 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem UnspilledSaved20.of_calleeSavedPreserved {s0 s1 s2 : State}
    (h01 : UnspilledSaved20 s0 s1) (h12 : CalleeSavedPreserved s1 s2) :
    UnspilledSaved20 s0 s2 :=
  ⟨h12.2.2.2.2.2.1.trans h01.1,
   h12.2.2.2.2.2.2.1.trans h01.2.1,
   h12.2.2.2.2.2.2.2.1.trans h01.2.2.1,
   h12.2.2.2.2.2.2.2.2.1.trans h01.2.2.2⟩

theorem cell_entails_memRegion8 (a v : BitVec 64) : (a ↦₆₄ v) ⊢ memRegion a 8 := by
  rw [pointsTo64_eq_pointsToBytes]
  simpa using pointsToBytes_entails_memRegion a (unpack64 v)

theorem savedFrame20_entails_memRegion128 (sp0 : BitVec 64) (s0 : State) :
    SavedFrame20 sp0 s0 ⊢ memRegion (sp0 - 128#64) 128 := by
  unfold SavedFrame20
  have hsplit :
      memRegion (sp0 - 128#64) 128 =
        memRegion (sp0 - 128#64) 8 ∗ memRegion (sp0 - 120#64) 8 ∗
        memRegion (sp0 - 112#64) 8 ∗ memRegion (sp0 - 104#64) 8 ∗
        memRegion (sp0 - 96#64) 8 ∗ memRegion (sp0 - 88#64) 8 ∗
        memRegion (sp0 - 80#64) 8 ∗ memRegion (sp0 - 72#64) 8 ∗
        memRegion (sp0 - 64#64) 8 ∗ memRegion (sp0 - 56#64) 8 ∗
        memRegion (sp0 - 48#64) 8 ∗ memRegion (sp0 - 40#64) 8 ∗
        memRegion (sp0 - 32#64) 8 ∗ memRegion (sp0 - 24#64) 8 ∗
        memRegion (sp0 - 16#64) 8 ∗ memRegion (sp0 - 8#64) 8 := by
    rw [memRegion_split' (b' := sp0 - 120#64) (n := 8) (k := 120) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 120#64) (b' := sp0 - 112#64) (n := 8) (k := 112) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 112#64) (b' := sp0 - 104#64) (n := 8) (k := 104) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 104#64) (b' := sp0 - 96#64) (n := 8) (k := 96) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 96#64) (b' := sp0 - 88#64) (n := 8) (k := 88) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 88#64) (b' := sp0 - 80#64) (n := 8) (k := 80) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 80#64) (b' := sp0 - 72#64) (n := 8) (k := 72) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 72#64) (b' := sp0 - 64#64) (n := 8) (k := 64) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 64#64) (b' := sp0 - 56#64) (n := 8) (k := 56) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 56#64) (b' := sp0 - 48#64) (n := 8) (k := 48) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 48#64) (b' := sp0 - 40#64) (n := 8) (k := 40) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 40#64) (b' := sp0 - 32#64) (n := 8) (k := 32) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 32#64) (b' := sp0 - 24#64) (n := 8) (k := 24) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 24#64) (b' := sp0 - 16#64) (n := 8) (k := 16) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 16#64) (b' := sp0 - 8#64) (n := 8) (k := 8) rfl (by bv_omega) (by decide)]
  rw [hsplit]
  refine sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
      (cell_entails_memRegion8 _ _)))))))))))))))

/-! ## 5. `ZETA_TABLE` Agreement & `.rodata` Read Step Lemmas -/

private theorem zetaTable_all_eq :
    (List.range 128).all (fun k =>
      let u := (((17 ^ bitRev7 k) % mlkemQ) * 65536) % mlkemQ
      let s : Int := if u ≤ 1664 then (u : Int) else (u : Int) - 3329
      zetaTableAt k == BitVec.ofInt 16 s) = true := by
  decide +kernel

theorem zetaTableAt_eq (k : Nat) (hk : k < 128) :
    zetaTableAt k = zetasTimesMontgomeryR.getD k 0#16 := by
  have h := beq_iff_eq.mp ((List.all_eq_true.mp zetaTable_all_eq) k (List.mem_range.mpr hk))
  rw [h]
  simp [zetasTimesMontgomeryR, fipsZetas, Array.getD, hk]

private theorem zetaTable_all_ne_0x8000 :
    (List.range 128).all (fun k => ((zetaTableAt k).zeroExtend 32 != 32768#32)) = true := by
  decide +kernel

theorem zetaTableAt_zext32_ne_32768 (k : Nat) (hk : k < 128) :
    (zetaTableAt k).zeroExtend 32 ≠ 32768#32 := by
  have h := (List.all_eq_true.mp zetaTable_all_ne_0x8000) k (List.mem_range.mpr hk)
  simpa [bne_iff_ne] using h

private theorem pack16_eq_readLE_2 (bs : List (BitVec 8)) (off : Nat) :
    pack16 (bs.getD off 0#8) (bs.getD (off + 1) 0#8) =
      (ByteSlice.readLE bs off 2).setWidth 16 := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  rw [BitVec.getLsbD_setWidth, getLsbD_readLE bs off 2 b (by omega)]
  unfold pack16
  rw [BitVec.getLsbD_append]
  have h16 : b < 16 := hb
  by_cases h8 : b < 8
  · have hdiv : b / 8 = 0 := by omega
    have hmod : b % 8 = b := by omega
    simp [h16, h8, hdiv, hmod]
  · have hdiv : b / 8 = 1 := by omega
    have hmod : b % 8 = b - 8 := by omega
    simp [h16, h8, hdiv, hmod]

/-- Step `LDR Qt, [addr]` against a 16-byte `.rodata` item (`RoDataAt s.mem roAddr bs`) without
    adding `.rodata` atoms to `P`. -/
theorem step_ldrQ128_ro {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc roAddr : BitVec 64} {vt : BitVec 5} {addr : AddrMode}
    {wb : Option (Reg × BitVec 64)} {bs : List (BitVec 8)} {v : BitVec 128}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldrSimd .Q128 vt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (roAddr, wb))
    (hro : RoDataAt s.mem roAddr bs)
    (hlen : bs.length = 16 := by simp)
    (hv : cst16Vec bs = v)
    (hexec : ((applyWriteback s wb).writeVReg128 vt v).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom := by
  unfold SepWP at hnext ⊢
  intro R hm
  have hm_ro : s.mem ⊨ ((roAddr ↦ᵣ bs) ∗ P) ∗ R := by
    rw [sepConj_assoc]
    exact Satisfies.rodata_intro hro.1 hro.2 (by omega) hm
  have hl0 := SepLoad64.of_pointsToBytesRO (a := roAddr) (F := P) (P := (roAddr ↦ᵣ bs) ∗ P)
    (off := 0) rfl (by omega) (by simp)
  have hl8 := SepLoad64.of_pointsToBytesRO (a := roAddr + 8#64) (F := P) (P := (roAddr ↦ᵣ bs) ∗ P)
    (off := 8) rfl (by omega) rfl
  have hr0 : s.mem.read64 roAddr = ByteSlice.readLE bs 0 8 := by
    rw [← ByteSlice.pack64_eq_readLE_8]; exact hl0.load hm_ro
  have hr8 : s.mem.read64 (roAddr + 8#64) = ByteSlice.readLE bs 8 8 := by
    rw [← ByteSlice.pack64_eq_readLE_8]; exact hl8.load hm_ro
  have hcan : s.mem.canRead roAddr 16 = true :=
    Memory.canRead_16_of_8_8 (hl0.readable hm_ro) (hl8.readable hm_ro)
  have hfetch' : prog.fetch s.pc = some (.ldrSimd .Q128 vt addr) := hpc.symm ▸ hfetch
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.ldrSimd .Q128 vt addr) s = s' := by
    rw [← hexec, ← hv]
    unfold cst16Vec
    cases wb <;> simp [Program.evalInst, execInstWithSvc, Memory.readSimdSized, Memory.read128,
      applyWriteback, State.advancePC, State.setPC, hsp, haddr, hr0, hr8, hcan,
      SimdMemSize.bytes, hpc]
  rw [hstep]
  have hmem : s'.mem = s.mem := by rw [← hexec]; cases wb <;> rfl
  apply hnext R
  rwa [hmem]

/-- Step `LDRH`/`LDURH Wt, [addr]` against `ZETA_TABLE` (`RoDataAt s.mem zAddr mlkemData00Bytes`)
    at entry `k < 128` without adding `.rodata` atoms to `P`. -/
theorem step_ldrh16_ro {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc zAddr ea : BitVec 64} {rt : Reg} {addr : AddrMode}
    {wb : Option (Reg × BitVec 64)} {k : Nat}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldr .W32 .H16 false rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hro : RoDataAt s.mem zAddr mlkemData00Bytes)
    (hk : k < 128)
    (hea : zAddr + BitVec.ofNat 64 (2 * k) = ea)
    (hexec : ((applyWriteback s wb).writeReg64 rt ((zetaTableAt k).zeroExtend 64)).setPC
      (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom := by
  unfold SepWP at hnext ⊢
  intro R hm
  have hlen : mlkemData00Bytes.length = 256 := by decide +kernel
  have hm_ro : s.mem ⊨ ((zAddr ↦ᵣ mlkemData00Bytes) ∗ P) ∗ R := by
    rw [sepConj_assoc]
    exact Satisfies.rodata_intro hro.1 hro.2 (by omega) hm
  have hl := SepLoad16.of_pointsToBytesRO (F := P) (P := (zAddr ↦ᵣ mlkemData00Bytes) ∗ P)
    (off := 2 * k) rfl (by omega) hea
  have hread : s.mem.read16 ea = zetaTableAt k := by
    rw [hl.load hm_ro, pack16_eq_readLE_2]; rfl
  have hcan : s.mem.canRead ea 2 = true := hl.readable hm_ro
  have hfetch' : prog.fetch s.pc = some (.ldr .W32 .H16 false rt addr) := hpc.symm ▸ hfetch
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.ldr .W32 .H16 false rt addr) s = s' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execLdr, Memory.readSized,
      MemWidth.bytes, applyWriteback, State.writeReg, State.advancePC,
      State.setPC, hsp, haddr, hread, hcan, hpc]
  rw [hstep]
  have hmem : s'.mem = s.mem := by rw [← hexec]; cases wb <;> rfl
  apply hnext R
  rwa [hmem]

/-- Step `LD1R {Vt.4H}, [Xn]` against `ZETA_TABLE` (`RoDataAt s.mem zAddr mlkemData00Bytes`)
    at entry `k < 128` without adding `.rodata` atoms to `P`. -/
theorem step_ld1r4h_ro {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc zAddr ea : BitVec 64} {rn : Reg} {rm vt : BitVec 5} {k : Nat}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.simdLd1r false 0x1#2 rn false rm vt))
    (hsp : checkRegSPAligned s rn = true)
    (hea_rn : s.readReg64 rn = ea)
    (hro : RoDataAt s.mem zAddr mlkemData00Bytes)
    (hk : k < 128)
    (hea : zAddr + BitVec.ofNat 64 (2 * k) = ea)
    (hexec : (s.writeVReg128 vt (dup4hLow (zetaTableAt k))).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom := by
  unfold SepWP at hnext ⊢
  intro R hm
  have hlen : mlkemData00Bytes.length = 256 := by decide +kernel
  have hm_ro : s.mem ⊨ ((zAddr ↦ᵣ mlkemData00Bytes) ∗ P) ∗ R := by
    rw [sepConj_assoc]
    exact Satisfies.rodata_intro hro.1 hro.2 (by omega) hm
  have hl := SepLoad16.of_pointsToBytesRO (F := P) (P := (zAddr ↦ᵣ mlkemData00Bytes) ∗ P)
    (off := 2 * k) rfl (by omega) hea
  have hread : s.mem.read16 ea = zetaTableAt k := by
    rw [hl.load hm_ro, pack16_eq_readLE_2]; rfl
  have hcan : s.mem.canRead ea 2 = true := hl.readable hm_ro
  have hzext : (((zetaTableAt k).zeroExtend 64 : BitVec 64).zeroExtend 128 : BitVec 128) =
      (zetaTableAt k).zeroExtend 128 := by bv_bits
  have hrep : mapLanes 16 0#128 (fun _ => ((zetaTableAt k).zeroExtend 128 : BitVec 128)) 4 =
      dup4hLow (zetaTableAt k) := by
    simp only [mapLanes, laneMask_16, dup4hLow]
    bv_bits
  have hfetch' : prog.fetch s.pc = some (.simdLd1r false 0x1#2 rn false rm vt) := hpc.symm ▸ hfetch
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.simdLd1r false 0x1#2 rn false rm vt) s = s' := by
    rw [← hexec]
    simp [Program.evalInst, execInstWithSvc, MemWidth.ofBits, MemWidth.bytes, Memory.readSized,
      hsp, hea_rn, hcan, hread, hzext, hrep, State.advancePC, State.setPC, hpc]
  rw [hstep]
  have hmem : s'.mem = s.mem := by rw [← hexec]; rfl
  apply hnext R
  rwa [hmem]

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
