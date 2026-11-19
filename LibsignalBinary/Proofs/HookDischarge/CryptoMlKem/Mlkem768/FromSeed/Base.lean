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
import ProofLib.Hoare.SafeReaches
import ProofLib.SepLogic.WP.StepsProcess
import ProofLib.SepLogic.WPFrozen

/-!
# `from_seed` (`B10` + `B05`) — Block Setup, Specifications, & Callee-Saved Frames

1. Block 05 (`generate_keypair_compressed`, `7,112` words) & Block 10 (`from_seed`, `24` words)
   `PlacedLib` and `WordTree` reflection.
2. `sepWP_seq_env` and `safe_subroutine_ok_of_simulates` combinators.
3. Pure `mlkem768KeyPairWith` length and `MlKem.fromSeed` bridge lemmas.
4. Core & caller-projection specifications (`mlkemGenKeypairRawSpec`, `mlkemGenKeypairTermRawSpec`,
   `mlkemFromSeedRawSpec`, `mlkemFromSeedCoreSpec`, `mlkemFromSeedTermRawSpec`,
   `mlkemFromSeedTermCoreSpec`, `mlkemFromSeedProjSpec`) and `SpecSimulates` bridges.
5. Spilled callee-saved frames (`SavedFrame05`, `SavedFrame10`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open scoped ProofLib.ProgramReflection
open ProofLib.ProgramReflection (WordTree)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (RoDataAt SpecSimulates)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (
  mlkemData00Bytes
  mlkemData01Bytes
  mlkemMultiLib
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (
  MlKemRoOk
  cst16Vec
  keccakRcAt
  zetaTableAt
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemPlacement
  mlkemMpl
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (withNonSyscallPreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Mlkem768FromSeedTerminates
  Poly
  Shake128MatrixTerminates
  bitsToBytes
  byteEncode
  mlkem768Incremental
  mlkem768KeyPairWith
  sampleNtt
  sha3_256
  sha3_256List
  sha3_512
  sha3_512List
  toByteVec
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (
  dup4hLow
  getLsbD_readLE
)

/-! ## 1. Block 05 (`generate_keypair_compressed`) & Block 10 (`from_seed`) `WordTree` Setup -/

@[expose] def blkLib05 : PlacedLib := mlkemMultiLib.blockLib 5
@[expose] def blkPl05 [MlKemPlacement] : Placement := mlkemMultiLib.blockPlacement mlkemMpl 5
theorem blkPlaceable05 [MlKemPlacement] : blkLib05.Placeable blkPl05 :=
  mlkemMultiLib.placeable_blockLib (by decide) MlKemPlacement.placeable
@[expose] def blkPC05 [MlKemPlacement] : Program := blkLib05.program blkPl05
@[expose] def blkProg05 : Program := { code := blkLib05.text.code, symbols := blkLib05.text.symbols }
set_option maxRecDepth 120000 in
@[expose] def blkTree05 : WordTree := word_tree_of% blkProg05

set_option maxRecDepth 120000 in
theorem blk05_code_eq : blkLib05.text.code = blkTree05.toBytes := by rfl_kernel

theorem blk05_tree_size : blkTree05.checkSize? = some 7112 := by rfl_kernel

@[expose] def blkLib10 : PlacedLib := mlkemMultiLib.blockLib 10
@[expose] def blkPl10 [MlKemPlacement] : Placement := mlkemMultiLib.blockPlacement mlkemMpl 10
theorem blkPlaceable10 [MlKemPlacement] : blkLib10.Placeable blkPl10 :=
  mlkemMultiLib.placeable_blockLib (by decide) MlKemPlacement.placeable
@[expose] def blkPC10 [MlKemPlacement] : Program := blkLib10.program blkPl10
@[expose] def blkProg10 : Program := { code := blkLib10.text.code, symbols := blkLib10.text.symbols }
@[expose] def blkTree10 : WordTree := word_tree_of% blkProg10

theorem blk10_code_eq : blkLib10.text.code = blkTree10.toBytes := by rfl_kernel

theorem blk10_tree_size : blkTree10.checkSize? = some 24 := by rfl_kernel

/-! ## 2. Segment Composition & Safe Simulation Combinators -/

/-- Sequence two `SepWP` segments while preserving `CodeLoaded` and `MlKemRoOk` across
    `KeepsFrozen` transitions. -/
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

/-- Transport `safe_subroutine_ok` along `SpecSimulates`. -/
theorem safe_subroutine_ok_of_simulates {α β : Type} {spec₁ : Spec α} {spec₂ : Spec β}
    (hsim : SpecSimulates spec₁ spec₂) {prog : Program} {entry : BitVec 64}
    (h : Arm64.safe_subroutine_ok prog entry spec₁) :
    Arm64.safe_subroutine_ok prog entry spec₂ := by
  intro y R s0 hentry hpre
  obtain ⟨x, R₁, hpre₁, hm⟩ := hsim y R s0 hpre
  exact (h x R₁ s0 hentry hpre₁).mono hm

/-! ## 3. Pure `mlkem768KeyPairWith` Length & `MlKem.fromSeed` Bridge -/

@[simp] theorem mlkem768KeyPairWith_length (sampler : List (BitVec 8) → Poly)
    {seed64 : List (BitVec 8)} (hseed : seed64.length = 64) :
    (mlkem768KeyPairWith sampler seed64).length = 2400 := by
  have hg : (sha3_512List (seed64.take 32 ++ [3#8])).length = 64 :=
    (sha3_512 (seed64.take 32 ++ [3#8])).2
  have hh : ∀ m, (sha3_256List m).length = 32 := fun m => (sha3_256 m).2
  have hrange : List.range 3 = [0, 1, 2] := rfl
  unfold mlkem768KeyPairWith
  dsimp only
  rw [hrange]
  simp [byteEncode, bitsToBytes, hg, hh, hseed]

theorem toByteVec_toList_of_length {n : Nat} {bs : List (BitVec 8)} (h : bs.length = n) :
    (toByteVec n bs).toList = bs := by
  apply List.ext_getElem
  · simp [toByteVec, List.Vector.toList, h]
  · intro i h1 h2
    simp [toByteVec, List.Vector.toList, List.getD_eq_getElem?_getD, h2]

theorem mlkem768Incremental_fromSeed_dk_toList (seed : List.Vector (BitVec 8) 64) :
    (mlkem768Incremental.fromSeed seed).2.2.toList =
      mlkem768KeyPairWith sampleNtt seed.toList := by
  rw [MlKem.fromSeed_dk]
  dsimp only [mlkem768Incremental]
  exact toByteVec_toList_of_length (mlkem768KeyPairWith_length sampleNtt seed.toList_length)

theorem mlkem768FromSeedTerminates_iff_list {seed : List.Vector (BitVec 8) 64} :
    Mlkem768FromSeedTerminates seed ↔
      Shake128MatrixTerminates ((sha3_512List (seed.toList.take 32 ++ [3#8])).take 32) 3 :=
  Iff.rfl

theorem toByteVec_64_terminates {seed : List (BitVec 8)} (hseed : seed.length = 64) :
    Mlkem768FromSeedTerminates (toByteVec 64 seed) ↔
      Shake128MatrixTerminates ((sha3_512List (seed.take 32 ++ [3#8])).take 32) 3 := by
  unfold Mlkem768FromSeedTerminates
  rw [toByteVec_toList_of_length hseed]

/-! ## 4. Core & Caller-Projection Specifications (`B05` & `B10`) -/

@[expose] def withMlKemRoOk {α : Type} (mpl : MultiPlacement) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s0 => ⌜MlKemRoOk mpl s0.mem⌝ ∗ spec.pre x s0 }

/-- Tight-stack (`31216 = 30080 + 1136` bytes) raw contract for `B05`
    (`generate_keypair_compressed`), unconditional for `Safe` (`MlKemBlockSafeOk 5`). -/
@[expose] noncomputable def mlkemGenKeypairRawSpec (mpl : MultiPlacement) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (seedA, seed, outPtr) s0 =>
    ⌜s0.readReg64 .x0 = seedA ∧
      s0.readReg64 .x1 = outPtr ∧
      seed.length = 64 ∧
      MlKemRoOk mpl s0.mem⌝ ∗
      (seedA ↦ₛ seed) ∗ memRegion outPtr 2400 ∗ stackAt s0.sp 31216
  post := fun (seedA, seed, outPtr) s0 _sf =>
    (seedA ↦ₛ seed) ∗ (outPtr ↦ₛ mlkem768KeyPairWith sampleNtt seed) ∗ stackAt s0.sp 31216
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Tight-stack (`31216` bytes) raw contract for `B05` restricted to inputs whose matrix
    `SampleNTT` loops terminate (`MlKemBlockOk 5`). -/
@[expose] noncomputable def mlkemGenKeypairTermRawSpec (mpl : MultiPlacement) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (seedA, seed, outPtr) s0 =>
    ⌜s0.readReg64 .x0 = seedA ∧
      s0.readReg64 .x1 = outPtr ∧
      seed.length = 64 ∧
      Shake128MatrixTerminates ((sha3_512List (seed.take 32 ++ [3#8])).take 32) 3 ∧
      MlKemRoOk mpl s0.mem⌝ ∗
      (seedA ↦ₛ seed) ∗ memRegion outPtr 2400 ∗ stackAt s0.sp 31216
  post := fun (seedA, seed, outPtr) s0 _sf =>
    (seedA ↦ₛ seed) ∗ (outPtr ↦ₛ mlkem768KeyPairWith sampleNtt seed) ∗ stackAt s0.sp 31216
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Tight-stack (`33664 = 2448 + 31216` bytes) raw contract for `B10` (`from_seed`) prior to
    `NonSyscallPreserved` lifting (unconditional for `Safe`). -/
@[expose] noncomputable def mlkemFromSeedRawSpec (mpl : MultiPlacement) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (seedA, seed, kpA) s0 =>
    ⌜s0.readReg64 .x0 = seedA ∧
      s0.readReg64 .x8 = kpA ∧
      seed.length = 64 ∧
      MlKemRoOk mpl s0.mem⌝ ∗
      (seedA ↦ₛ seed) ∗ memRegion kpA 2400 ∗ stackAt s0.sp 33664
  post := fun (seedA, seed, kpA) s0 _sf =>
    (seedA ↦ₛ seed) ∗ (kpA ↦ₛ mlkem768KeyPairWith sampleNtt seed) ∗ stackAt s0.sp 33664
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Tight-stack (`33664` bytes) core contract for `B10` (`from_seed`) with `NonSyscallPreserved`. -/
@[expose] noncomputable def mlkemFromSeedCoreSpec (mpl : MultiPlacement) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64) :=
  withNonSyscallPreserved (mlkemFromSeedRawSpec mpl)

/-- Tight-stack (`33664` bytes) raw contract for `B10` (`from_seed`) restricted to terminating
    64-byte seeds (`Mlkem768FromSeedTerminates (toByteVec 64 seed)`). -/
@[expose] noncomputable def mlkemFromSeedTermRawSpec (mpl : MultiPlacement) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (seedA, seed, kpA) s0 =>
    ⌜s0.readReg64 .x0 = seedA ∧
      s0.readReg64 .x8 = kpA ∧
      seed.length = 64 ∧
      Mlkem768FromSeedTerminates (toByteVec 64 seed) ∧
      MlKemRoOk mpl s0.mem⌝ ∗
      (seedA ↦ₛ seed) ∗ memRegion kpA 2400 ∗ stackAt s0.sp 33664
  post := fun (seedA, seed, kpA) s0 _sf =>
    (seedA ↦ₛ seed) ∗ (kpA ↦ₛ mlkem768KeyPairWith sampleNtt seed) ∗ stackAt s0.sp 33664
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Tight-stack (`33664` bytes) terminating core contract for `B10` (`from_seed`) with
    `NonSyscallPreserved`. -/
@[expose] noncomputable def mlkemFromSeedTermCoreSpec (mpl : MultiPlacement) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64) :=
  withNonSyscallPreserved (mlkemFromSeedTermRawSpec mpl)

/-- Polymorphic caller-struct projection spec parameterized by stack size `stk : Nat`,
    matching `Hooks.mlkemFromSeedSpec K` by `rfl` at `stk = extHookStack` (`65536`). -/
@[expose] def mlkemFromSeedProjSpec (stk : Nat) (K : MlKem) {C : Type}
    (seedA : C → BitVec 64) (seed : C → List.Vector (BitVec 8) 64)
    (kpA : C → BitVec 64) : Spec C where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = seedA x ∧ s.readReg64 .x8 = kpA x⌝ ∗
      (seedA x ↦ₛ (seed x).toList) ∗ memRegion (kpA x) 2400 ∗ stackAt s.sp stk
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (seedA x ↦ₛ (seed x).toList) ∗
      (kpA x ↦ₛ (K.fromSeed (seed x)).2.2.toList) ∗
      stackAt s0.sp stk

theorem mlkemFromSeedCore_simulates_proj {stk : Nat} (hstk : 33664 ≤ stk)
    (hstk_fit : stk ≤ 2 ^ 64 := by decide) (K : MlKem)
    (hK : ∀ s, (K.fromSeed s).2.2.toList = mlkem768KeyPairWith sampleNtt s.toList)
    {C : Type}
    (seedA : C → BitVec 64) (seed : C → List.Vector (BitVec 8) 64)
    (kpA : C → BitVec 64) (mpl : MultiPlacement) :
    SpecSimulates (mlkemFromSeedCoreSpec mpl)
      (withMlKemRoOk mpl (keepsFs (mlkemFromSeedProjSpec stk K seedA seed kpA))) := by
  refine SpecSimulates.of_map ?_
  intro y R s0 hm
  dsimp only [withMlKemRoOk, keepsFs, mlkemFromSeedProjSpec] at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hro, hm⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hx0, hx8⟩, hm⟩
  rw [stackAt_shrink s0.sp stk 33664 hstk hstk_fit] at hm
  set slack := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - 33664)
  refine ⟨(seedA y, (seed y).toList, kpA y), slack ∗ R, ?_, ?_⟩
  · dsimp only [mlkemFromSeedCoreSpec, withNonSyscallPreserved, mlkemFromSeedRawSpec]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, (seed y).toList_length, hro⟩, ?_⟩
    rw [sepConj_comm slack (stackAt s0.sp 33664),
      sepConj_assoc (stackAt s0.sp 33664) slack R] at hm
    exact hm
  · intro sf _ _ hpost
    dsimp only [mlkemFromSeedCoreSpec, withNonSyscallPreserved, mlkemFromSeedRawSpec] at hpost
    dsimp only [withMlKemRoOk, keepsFs, mlkemFromSeedProjSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hnsp, hpost⟩
    have htr : sf.trace = s0.trace := hnsp.1
    have hfs : sf.fs = s0.fs := hnsp.2.2.2.2.2.2
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hfs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    rw [hK]
    rw [sepConj_assoc, sepConj_assoc] at hpost ⊢
    rw [← sepConj_assoc (stackAt s0.sp 33664) slack R,
      sepConj_comm (stackAt s0.sp 33664) slack,
      ← stackAt_shrink s0.sp stk 33664 hstk hstk_fit] at hpost
    exact hpost

theorem mlkemFromSeedTermCore_simulates_proj {stk : Nat} (hstk : 33664 ≤ stk)
    (hstk_fit : stk ≤ 2 ^ 64 := by decide) (K : MlKem)
    (hK : ∀ s, (K.fromSeed s).2.2.toList = mlkem768KeyPairWith sampleNtt s.toList)
    {C : Type}
    (seedA : C → BitVec 64) (seed : C → List.Vector (BitVec 8) 64)
    (kpA : C → BitVec 64)
    (hterm : ∀ x, Mlkem768FromSeedTerminates (seed x)) (mpl : MultiPlacement) :
    SpecSimulates (mlkemFromSeedTermCoreSpec mpl)
      (withMlKemRoOk mpl (keepsFs (mlkemFromSeedProjSpec stk K seedA seed kpA))) := by
  refine SpecSimulates.of_map ?_
  intro y R s0 hm
  dsimp only [withMlKemRoOk, keepsFs, mlkemFromSeedProjSpec] at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hro, hm⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hx0, hx8⟩, hm⟩
  rw [stackAt_shrink s0.sp stk 33664 hstk hstk_fit] at hm
  set slack := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - 33664)
  have ht_y : Mlkem768FromSeedTerminates (toByteVec 64 (seed y).toList) := by
    have hvec : toByteVec 64 (seed y).toList = seed y := by
      apply Subtype.ext
      exact toByteVec_toList_of_length (seed y).toList_length
    rw [hvec]
    exact hterm y
  refine ⟨(seedA y, (seed y).toList, kpA y), slack ∗ R, ?_, ?_⟩
  · dsimp only [mlkemFromSeedTermCoreSpec, withNonSyscallPreserved, mlkemFromSeedTermRawSpec]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, (seed y).toList_length, ht_y, hro⟩, ?_⟩
    rw [sepConj_comm slack (stackAt s0.sp 33664),
      sepConj_assoc (stackAt s0.sp 33664) slack R] at hm
    exact hm
  · intro sf _ _ hpost
    dsimp only [mlkemFromSeedTermCoreSpec, withNonSyscallPreserved,
      mlkemFromSeedTermRawSpec] at hpost
    dsimp only [withMlKemRoOk, keepsFs, mlkemFromSeedProjSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hnsp, hpost⟩
    have htr : sf.trace = s0.trace := hnsp.1
    have hfs : sf.fs = s0.fs := hnsp.2.2.2.2.2.2
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hfs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    rw [hK]
    rw [sepConj_assoc, sepConj_assoc] at hpost ⊢
    rw [← sepConj_assoc (stackAt s0.sp 33664) slack R,
      sepConj_comm (stackAt s0.sp 33664) slack,
      ← stackAt_shrink s0.sp stk 33664 hstk hstk_fit] at hpost
    exact hpost

/-! ## 5. Spilled Callee-Saved Frames (`B05` `[sp0 - 160, sp0)` & `B10` `[sp0 - 48, sp0)`) -/

/-- All 20 callee-saved 64-bit slots (`d15..d8`, `x29, x30`, `x28..x19`) spilled by `B05`
    at `[sp0 - 160, sp0)`. -/
@[expose] def SavedFrame05 (sp0 : BitVec 64) (s0 : State) : SepProp :=
  ((sp0 - 160#64) ↦₆₄ (s0.readVReg128 15#5).truncate 64) ∗
  ((sp0 - 152#64) ↦₆₄ (s0.readVReg128 14#5).truncate 64) ∗
  ((sp0 - 144#64) ↦₆₄ (s0.readVReg128 13#5).truncate 64) ∗
  ((sp0 - 136#64) ↦₆₄ (s0.readVReg128 12#5).truncate 64) ∗
  ((sp0 - 128#64) ↦₆₄ (s0.readVReg128 11#5).truncate 64) ∗
  ((sp0 - 120#64) ↦₆₄ (s0.readVReg128 10#5).truncate 64) ∗
  ((sp0 - 112#64) ↦₆₄ (s0.readVReg128 9#5).truncate 64) ∗
  ((sp0 - 104#64) ↦₆₄ (s0.readVReg128 8#5).truncate 64) ∗
  ((sp0 - 96#64)  ↦₆₄ s0.readReg64 .fp) ∗
  ((sp0 - 88#64)  ↦₆₄ s0.readReg64 .lr) ∗
  ((sp0 - 80#64)  ↦₆₄ s0.readReg64 .x28) ∗
  ((sp0 - 72#64)  ↦₆₄ s0.readReg64 .x27) ∗
  ((sp0 - 64#64)  ↦₆₄ s0.readReg64 .x26) ∗
  ((sp0 - 56#64)  ↦₆₄ s0.readReg64 .x25) ∗
  ((sp0 - 48#64)  ↦₆₄ s0.readReg64 .x24) ∗
  ((sp0 - 40#64)  ↦₆₄ s0.readReg64 .x23) ∗
  ((sp0 - 32#64)  ↦₆₄ s0.readReg64 .x22) ∗
  ((sp0 - 24#64)  ↦₆₄ s0.readReg64 .x21) ∗
  ((sp0 - 16#64)  ↦₆₄ s0.readReg64 .x20) ∗
  ((sp0 - 8#64)   ↦₆₄ s0.readReg64 .x19)

theorem cell_entails_memRegion8 (a v : BitVec 64) : (a ↦₆₄ v) ⊢ memRegion a 8 := by
  rw [pointsTo64_eq_pointsToBytes]
  simpa using pointsToBytes_entails_memRegion a (unpack64 v)

theorem savedFrame05_entails_memRegion160 (sp0 : BitVec 64) (s0 : State) :
    SavedFrame05 sp0 s0 ⊢ memRegion (sp0 - 160#64) 160 := by
  unfold SavedFrame05
  have hsplit :
      memRegion (sp0 - 160#64) 160 =
        memRegion (sp0 - 160#64) 8 ∗ memRegion (sp0 - 152#64) 8 ∗
        memRegion (sp0 - 144#64) 8 ∗ memRegion (sp0 - 136#64) 8 ∗
        memRegion (sp0 - 128#64) 8 ∗ memRegion (sp0 - 120#64) 8 ∗
        memRegion (sp0 - 112#64) 8 ∗ memRegion (sp0 - 104#64) 8 ∗
        memRegion (sp0 - 96#64) 8 ∗ memRegion (sp0 - 88#64) 8 ∗
        memRegion (sp0 - 80#64) 8 ∗ memRegion (sp0 - 72#64) 8 ∗
        memRegion (sp0 - 64#64) 8 ∗ memRegion (sp0 - 56#64) 8 ∗
        memRegion (sp0 - 48#64) 8 ∗ memRegion (sp0 - 40#64) 8 ∗
        memRegion (sp0 - 32#64) 8 ∗ memRegion (sp0 - 24#64) 8 ∗
        memRegion (sp0 - 16#64) 8 ∗ memRegion (sp0 - 8#64) 8 := by
    rw [memRegion_split' (b' := sp0 - 152#64) (n := 8) (k := 152) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 152#64) (b' := sp0 - 144#64) (n := 8) (k := 144) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 144#64) (b' := sp0 - 136#64) (n := 8) (k := 136) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 136#64) (b' := sp0 - 128#64) (n := 8) (k := 128) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 128#64) (b' := sp0 - 120#64) (n := 8) (k := 120) rfl (by bv_omega) (by decide),
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
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
      (cell_entails_memRegion8 _ _)))))))))))))))))))

/-- Callee-saved registers (`x29, x30, x28`, 8-byte pad, `x20, x19`) spilled by `B10`
    at `[sp0 - 48, sp0)`. -/
@[expose] def SavedFrame10 (sp0 : BitVec 64) (s0 : State) : SepProp :=
  ((sp0 - 48#64) ↦₆₄ s0.readReg64 .fp) ∗
  ((sp0 - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
  ((sp0 - 32#64) ↦₆₄ s0.readReg64 .x28) ∗
  memRegion (sp0 - 24#64) 8 ∗
  ((sp0 - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((sp0 - 8#64)  ↦₆₄ s0.readReg64 .x19)

theorem savedFrame10_entails_memRegion48 (sp0 : BitVec 64) (s0 : State) :
    SavedFrame10 sp0 s0 ⊢ memRegion (sp0 - 48#64) 48 := by
  unfold SavedFrame10
  have hsplit :
      memRegion (sp0 - 48#64) 48 =
        memRegion (sp0 - 48#64) 8 ∗ memRegion (sp0 - 40#64) 8 ∗
        memRegion (sp0 - 32#64) 8 ∗ memRegion (sp0 - 24#64) 8 ∗
        memRegion (sp0 - 16#64) 8 ∗ memRegion (sp0 - 8#64) 8 := by
    rw [memRegion_split' (b' := sp0 - 40#64) (n := 8) (k := 40) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 40#64) (b' := sp0 - 32#64) (n := 8) (k := 32) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 32#64) (b' := sp0 - 24#64) (n := 8) (k := 24) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 24#64) (b' := sp0 - 16#64) (n := 8) (k := 16) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 16#64) (b' := sp0 - 8#64) (n := 8) (k := 8) rfl (by bv_omega) (by decide)]
  rw [hsplit]
  refine sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
      (cell_entails_memRegion8 _ _)))))

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base
