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
public import ProofLib.SepLogic.SafeSepWP
public import LibsignalBinary.Specifications.LibsignalSpqrV1.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Libc.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.RustStd.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
public meta import ProofLib.ProgramReflection
public meta import ProofLib.GenDecodes
public meta import ProofLib.GenPlacedFetches

/-!
# `decapsulate_compressed_key` (`B22` → `B04`) — Block Setup, Specs, & Callee-Saved Frame

1. Block 04 (`neon::decapsulate_compressed_key`, `13,411` words) and Block 22 (`5`-word tail-jump
   wrapper) `PlacedLib` & `WordTree` definitions.
2. `SafeSepWP` + `SpecSimulates` lifting combinators (`safe_subroutine_ok_simulates`,
   `mlkemBlockSafeOk_simulates`, `mlkemBlockOk_simulates`, `safeSepWP_of_sepWP_env`).
3. Tight-stack (`26,960` B) core contracts (`mlkemBlk04RawSpec`, `mlkemBlk04CoreSpec`,
   `mlkemDecapsRawSpec`, `mlkemDecapsCoreSpec`, plus `Term*` total-correctness variants) and
   `stk`-parameterized caller-projection contract (`mlkemDecapsProjSpec`) with `SpecSimulates`
   bridges.
4. Spilled callee-saved frame (`SavedFrame04`) at `[sp0 - 160, sp0)` (`20` 8-byte slots saving all
   callee-saved SIMD `d8..d15` and GPR `x19..x30` registers).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open scoped ProofLib.ProgramReflection
open ProofLib.ProgramReflection (WordTree)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (SpecSimulates)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBlockOk
  MlKemBlockSafeOk
  MlKemPlacement
  mlkemMpl
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (withNonSyscallPreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Mlkem768DecapsTerminates
  Poly
  keccakSponge
  mlkem768DecapsWith
  sampleNtt
  sha3_512List
  shake256List
  toByteVec
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  cell_entails_memRegion8
  toByteVec_toList_of_length
  withMlKemRoOk
)

/-! ## 1. Block 04 (`13,411` Words) & Block 22 (`5` Words) `PlacedLib` & `WordTree` Setup -/

@[expose] def blkLib04 : PlacedLib := mlkemMultiLib.blockLib 4
@[expose] def blkPl04 [MlKemPlacement] : Placement := mlkemMultiLib.blockPlacement mlkemMpl 4
theorem blkPlaceable04 [MlKemPlacement] : blkLib04.Placeable blkPl04 :=
  mlkemMultiLib.placeable_blockLib (by decide) MlKemPlacement.placeable
@[expose] def blkPC04 [MlKemPlacement] : Program := blkLib04.program blkPl04
@[expose] def blkProg04 : Program := { code := blkLib04.text.code, symbols := blkLib04.text.symbols }
set_option maxRecDepth 150000 in
@[expose] def blkTree04 : WordTree := word_tree_of% blkProg04

set_option maxRecDepth 150000 in
theorem blk04_code_eq : blkLib04.text.code = blkTree04.toBytes := by rfl_kernel

theorem blk04_tree_size : blkTree04.checkSize? = some 13411 := by rfl_kernel

@[expose] def blkLib22 : PlacedLib := mlkemMultiLib.blockLib 22
@[expose] def blkPl22 [MlKemPlacement] : Placement := mlkemMultiLib.blockPlacement mlkemMpl 22
theorem blkPlaceable22 [MlKemPlacement] : blkLib22.Placeable blkPl22 :=
  mlkemMultiLib.placeable_blockLib (by decide) MlKemPlacement.placeable
@[expose] def blkPC22 [MlKemPlacement] : Program := blkLib22.program blkPl22
@[expose] def blkProg22 : Program := { code := blkLib22.text.code, symbols := blkLib22.text.symbols }
@[expose] def blkTree22 : WordTree := word_tree_of% blkProg22

theorem blk22_code_eq : blkLib22.text.code = blkTree22.toBytes := by rfl_kernel

theorem blk22_tree_size : blkTree22.checkSize? = some 5 := by rfl_kernel

/-! ## 2. `SafeSepWP` & `SpecSimulates` Lifting Combinators -/

/-- Transport `safe_subroutine_ok` along `SpecSimulates`. -/
theorem safe_subroutine_ok_simulates {α β : Type} {spec₁ : Spec α} {spec₂ : Spec β}
    (hsim : SpecSimulates spec₁ spec₂) {prog : Program} {entry : BitVec 64}
    (h : Arm64.safe_subroutine_ok prog entry spec₁) :
    Arm64.safe_subroutine_ok prog entry spec₂ := fun y R s0 hentry hpre =>
  let ⟨x, R₁, hpre₁, hm⟩ := hsim y R s0 hpre
  (h x R₁ s0 hentry hpre₁).mono fun sf hout => hm sf hout

/-- Lift a placement-indexed `SpecSimulates` family across `MlKemBlockOk`. -/
theorem mlkemBlockOk_simulates {j : Nat} {α β : Type}
    {spec₁ : MultiPlacement → Spec α} {spec₂ : MultiPlacement → Spec β}
    (hsim : ∀ mpl, SpecSimulates (spec₁ mpl) (spec₂ mpl))
    (h : MlKemBlockOk j spec₁) :
    MlKemBlockOk j spec₂ :=
  fun [MlKemPlacement] =>
    ((hsim mlkemMpl).withCodeLoaded mlkemMultiLib mlkemMpl).subroutine_ok h

/-- Lift a placement-indexed `SpecSimulates` family across `MlKemBlockSafeOk`. -/
theorem mlkemBlockSafeOk_simulates {j : Nat} {α β : Type}
    {spec₁ : MultiPlacement → Spec α} {spec₂ : MultiPlacement → Spec β}
    (hsim : ∀ mpl, SpecSimulates (spec₁ mpl) (spec₂ mpl))
    (h : MlKemBlockSafeOk j spec₁) :
    MlKemBlockSafeOk j spec₂ :=
  fun [MlKemPlacement] =>
    safe_subroutine_ok_simulates
      ((hsim mlkemMpl).withCodeLoaded mlkemMultiLib mlkemMpl) h

/-- Sequence a total `SepWP` prefix before a `SafeSepWP` continuation while preserving
    `CodeLoaded` and `MlKemRoOk` across `KeepsFrozen`. -/
theorem safeSepWP_of_sepWP_env {prog : Program} {mid : BitVec 64} {s : State}
    {P : SepProp} {post1 Q : State → SepProp → Prop} {mpl : MultiPlacement}
    (hcl : mlkemMultiLib.CodeLoaded mpl s.mem)
    (hro : MlKemRoOk mpl s.mem)
    (h1 : SepWP prog mid s P post1)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running →
      mlkemMultiLib.CodeLoaded mpl sm.mem → MlKemRoOk mpl sm.mem →
      post1 sm Pm → SafeSepWP prog sm Pm Q) :
    SafeSepWP prog s P Q :=
  SafeSepWP.of_sepWP
    (SepWP.mono_frozen
      (post' := fun sm Pm => SafeSepWP prog sm Pm Q)
      (Φ := fun m => mlkemMultiLib.CodeLoaded mpl m ∧ MlKemRoOk mpl m)
      (fun _ _ ⟨hc, hr⟩ hkf => ⟨hc.of_keepsFrozen hkf, hr.of_keepsFrozen hkf⟩)
      ⟨hcl, hro⟩ h1
      (fun sm Pm hpc hrun ⟨hc, hr⟩ hp1 => h2 sm Pm hpc hrun hc hr hp1))

/-! ## 3. Core (`26,960` B Tight Stack) & Caller-Projection Specifications -/

@[simp] theorem mlkem768DecapsWith_length (sampler : List (BitVec 8) → Poly)
    (dk ct1 ct2 : List (BitVec 8)) :
    (mlkem768DecapsWith sampler dk ct1 ct2).length = 32 := by
  dsimp only [mlkem768DecapsWith]
  split <;> simp [sha3_512List, shake256List, keccakSponge]

theorem toByteVec_of_vector {n : Nat} (v : List.Vector (BitVec 8) n) :
    toByteVec n v.toList = v := by
  apply Subtype.ext
  exact toByteVec_toList_of_length v.toList_length

/-- Tight-stack (`26,960` B) raw contract for `B04` (`x0 = ret, x1 = dkA, x2 = ct1A, x3 = ct2A`). -/
@[expose] noncomputable def mlkemBlk04RawSpec (mpl : MultiPlacement) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) ×
      BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8)) where
  pre := fun (ret, dkA, dk, ct1A, ct1, ct2A, ct2) s0 =>
    ⌜s0.readReg64 .x0 = ret ∧
      s0.readReg64 .x1 = dkA ∧
      s0.readReg64 .x2 = ct1A ∧
      s0.readReg64 .x3 = ct2A ∧
      dk.length = 2400 ∧
      ct1.length = 960 ∧
      ct2.length = 128 ∧
      MlKemRoOk mpl s0.mem⌝ ∗
      (dkA ↦ₛ dk) ∗ (ct1A ↦ₛ ct1) ∗ (ct2A ↦ₛ ct2) ∗ memRegion ret 32 ∗ stackAt s0.sp 26960
  post := fun (ret, dkA, dk, ct1A, ct1, ct2A, ct2) s0 _sf =>
    (dkA ↦ₛ dk) ∗ (ct1A ↦ₛ ct1) ∗ (ct2A ↦ₛ ct2) ∗
      (ret ↦ₛ mlkem768DecapsWith sampleNtt dk ct1 ct2) ∗ stackAt s0.sp 26960
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Conditional total-correctness raw contract for `B04` (adjoining `Mlkem768DecapsTerminates`). -/
@[expose] noncomputable def mlkemBlk04TermRawSpec (mpl : MultiPlacement) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) ×
      BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8)) where
  pre := fun args s0 =>
    ⌜Mlkem768DecapsTerminates (toByteVec 2400 args.2.2.1)⌝ ∗ (mlkemBlk04RawSpec mpl).pre args s0
  post := (mlkemBlk04RawSpec mpl).post
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Tight-stack (`26,960` B) core contract for `B04` with `NonSyscallPreserved`. -/
@[expose] noncomputable def mlkemBlk04CoreSpec (mpl : MultiPlacement) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) ×
      BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8)) :=
  withNonSyscallPreserved (mlkemBlk04RawSpec mpl)

/-- Conditional total-correctness core contract for `B04` with `NonSyscallPreserved`. -/
@[expose] noncomputable def mlkemBlk04TermCoreSpec (mpl : MultiPlacement) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) ×
      BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8)) :=
  withNonSyscallPreserved (mlkemBlk04TermRawSpec mpl)

/-- Tight-stack (`26,960` B) raw contract for `B22` (`x8 = ret, x0 = dkA, x1 = ct1A, x2 = ct2A`). -/
@[expose] noncomputable def mlkemDecapsRawSpec (mpl : MultiPlacement) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) ×
      BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8)) where
  pre := fun (ret, dkA, dk, ct1A, ct1, ct2A, ct2) s0 =>
    ⌜s0.readReg64 .x8 = ret ∧
      s0.readReg64 .x0 = dkA ∧
      s0.readReg64 .x1 = ct1A ∧
      s0.readReg64 .x2 = ct2A ∧
      dk.length = 2400 ∧
      ct1.length = 960 ∧
      ct2.length = 128 ∧
      MlKemRoOk mpl s0.mem⌝ ∗
      (dkA ↦ₛ dk) ∗ (ct1A ↦ₛ ct1) ∗ (ct2A ↦ₛ ct2) ∗ memRegion ret 32 ∗ stackAt s0.sp 26960
  post := fun (ret, dkA, dk, ct1A, ct1, ct2A, ct2) s0 _sf =>
    (dkA ↦ₛ dk) ∗ (ct1A ↦ₛ ct1) ∗ (ct2A ↦ₛ ct2) ∗
      (ret ↦ₛ mlkem768DecapsWith sampleNtt dk ct1 ct2) ∗ stackAt s0.sp 26960
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Conditional total-correctness raw contract for `B22` (adjoining `Mlkem768DecapsTerminates`). -/
@[expose] noncomputable def mlkemDecapsTermRawSpec (mpl : MultiPlacement) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) ×
      BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8)) where
  pre := fun args s0 =>
    ⌜Mlkem768DecapsTerminates (toByteVec 2400 args.2.2.1)⌝ ∗ (mlkemDecapsRawSpec mpl).pre args s0
  post := (mlkemDecapsRawSpec mpl).post
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Tight-stack (`26,960` B) core contract for `B22` with `NonSyscallPreserved`. -/
@[expose] noncomputable def mlkemDecapsCoreSpec (mpl : MultiPlacement) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) ×
      BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8)) :=
  withNonSyscallPreserved (mlkemDecapsRawSpec mpl)

/-- Conditional total-correctness core contract for `B22` with `NonSyscallPreserved`. -/
@[expose] noncomputable def mlkemDecapsTermCoreSpec (mpl : MultiPlacement) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) ×
      BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8)) :=
  withNonSyscallPreserved (mlkemDecapsTermRawSpec mpl)

/-- Polymorphic caller-struct projection spec parameterized by stack size `stk` and `K : MlKem`,
    matching `Hooks.mlkemDecapsSpec K` by `rfl` when instantiated with `MlkemDecapsCall`
    projections and `stk = extHookStack`. -/
@[expose] def mlkemDecapsProjSpec (stk : Nat) (K : MlKem) {C : Type}
    (ret : C → BitVec 64)
    (dkA : C → BitVec 64) (dk : C → List.Vector (BitVec 8) 2400)
    (ct1A : C → BitVec 64) (ct1 : C → List.Vector (BitVec 8) 960)
    (ct2A : C → BitVec 64) (ct2 : C → List.Vector (BitVec 8) 128) : Spec C where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = ret x ∧ s.readReg64 .x0 = dkA x ∧
      s.readReg64 .x1 = ct1A x ∧ s.readReg64 .x2 = ct2A x⌝ ∗
      (dkA x ↦ₛ (dk x).toList) ∗ (ct1A x ↦ₛ (ct1 x).toList) ∗ (ct2A x ↦ₛ (ct2 x).toList) ∗
      memRegion (ret x) 32 ∗ stackAt s.sp stk
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (dkA x ↦ₛ (dk x).toList) ∗ (ct1A x ↦ₛ (ct1 x).toList) ∗ (ct2A x ↦ₛ (ct2 x).toList) ∗
      (ret x ↦ₛ (K.decaps (dk x) (ct1 x) (ct2 x)).toList) ∗
      stackAt s0.sp stk

theorem mlkemDecapsCore_simulates_proj (stk : Nat) (hstk : 26960 ≤ stk)
    (hstk_fit : stk ≤ 2 ^ 64 := by decide) (K : MlKem)
    (hK : ∀ d c1 c2, K.decaps d c1 c2 =
      toByteVec 32 (mlkem768DecapsWith sampleNtt d.toList c1.toList c2.toList))
    {C : Type} (ret : C → BitVec 64)
    (dkA : C → BitVec 64) (dk : C → List.Vector (BitVec 8) 2400)
    (ct1A : C → BitVec 64) (ct1 : C → List.Vector (BitVec 8) 960)
    (ct2A : C → BitVec 64) (ct2 : C → List.Vector (BitVec 8) 128) (mpl : MultiPlacement) :
    SpecSimulates (mlkemDecapsCoreSpec mpl)
      (withMlKemRoOk mpl (keepsFs (mlkemDecapsProjSpec stk K ret dkA dk ct1A ct1 ct2A ct2))) := by
  refine SpecSimulates.of_map ?_
  intro y R s0 hm
  dsimp only [withMlKemRoOk, keepsFs, mlkemDecapsProjSpec] at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hro, hm⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
    satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hx8, hx0, hx1, hx2⟩, hm⟩
  rw [stackAt_shrink s0.sp stk 26960 hstk hstk_fit] at hm
  set slack := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - 26960)
  refine ⟨(ret y, dkA y, (dk y).toList, ct1A y, (ct1 y).toList, ct2A y, (ct2 y).toList),
    slack ∗ R, ?_, ?_⟩
  · dsimp only [mlkemDecapsCoreSpec, withNonSyscallPreserved, mlkemDecapsRawSpec]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
      satisfies_pure_sepConj]
    refine ⟨⟨hx8, hx0, hx1, hx2, (dk y).toList_length, (ct1 y).toList_length,
      (ct2 y).toList_length, hro⟩, ?_⟩
    rw [sepConj_comm slack (stackAt s0.sp 26960),
      sepConj_assoc (stackAt s0.sp 26960) slack R] at hm
    exact hm
  · intro sf _ _ hpost
    dsimp only [mlkemDecapsCoreSpec, withNonSyscallPreserved, mlkemDecapsRawSpec] at hpost
    dsimp only [withMlKemRoOk, keepsFs, mlkemDecapsProjSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hnsp, hpost⟩
    have htr : sf.trace = s0.trace := hnsp.1
    have hfs : sf.fs = s0.fs := hnsp.2.2.2.2.2.2
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hfs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    rw [hK, toByteVec_toList_of_length (mlkem768DecapsWith_length _ _ _ _)]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc] at hpost ⊢
    rw [← sepConj_assoc (stackAt s0.sp 26960) slack R,
      sepConj_comm (stackAt s0.sp 26960) slack,
      ← stackAt_shrink s0.sp stk 26960 hstk hstk_fit] at hpost
    exact hpost

theorem mlkemDecapsTermCore_simulates_proj (stk : Nat) (hstk : 26960 ≤ stk)
    (hstk_fit : stk ≤ 2 ^ 64 := by decide) (K : MlKem)
    (hK : ∀ d c1 c2, K.decaps d c1 c2 =
      toByteVec 32 (mlkem768DecapsWith sampleNtt d.toList c1.toList c2.toList))
    {C : Type} (ret : C → BitVec 64)
    (dkA : C → BitVec 64) (dk : C → List.Vector (BitVec 8) 2400)
    (ct1A : C → BitVec 64) (ct1 : C → List.Vector (BitVec 8) 960)
    (ct2A : C → BitVec 64) (ct2 : C → List.Vector (BitVec 8) 128)
    (hTerm : ∀ x, Mlkem768DecapsTerminates (dk x)) (mpl : MultiPlacement) :
    SpecSimulates (mlkemDecapsTermCoreSpec mpl)
      (withMlKemRoOk mpl (keepsFs (mlkemDecapsProjSpec stk K ret dkA dk ct1A ct1 ct2A ct2))) := by
  refine SpecSimulates.of_map ?_
  intro y R s0 hm
  dsimp only [withMlKemRoOk, keepsFs, mlkemDecapsProjSpec] at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hro, hm⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
    satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hx8, hx0, hx1, hx2⟩, hm⟩
  rw [stackAt_shrink s0.sp stk 26960 hstk hstk_fit] at hm
  set slack := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - 26960)
  refine ⟨(ret y, dkA y, (dk y).toList, ct1A y, (ct1 y).toList, ct2A y, (ct2 y).toList),
    slack ∗ R, ?_, ?_⟩
  · dsimp only [mlkemDecapsTermCoreSpec, withNonSyscallPreserved, mlkemDecapsTermRawSpec,
      mlkemDecapsRawSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨by rw [toByteVec_of_vector]; exact hTerm y, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
      satisfies_pure_sepConj]
    refine ⟨⟨hx8, hx0, hx1, hx2, (dk y).toList_length, (ct1 y).toList_length,
      (ct2 y).toList_length, hro⟩, ?_⟩
    rw [sepConj_comm slack (stackAt s0.sp 26960),
      sepConj_assoc (stackAt s0.sp 26960) slack R] at hm
    exact hm
  · intro sf _ _ hpost
    dsimp only [mlkemDecapsTermCoreSpec, withNonSyscallPreserved, mlkemDecapsTermRawSpec,
      mlkemDecapsRawSpec] at hpost
    dsimp only [withMlKemRoOk, keepsFs, mlkemDecapsProjSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hnsp, hpost⟩
    have htr : sf.trace = s0.trace := hnsp.1
    have hfs : sf.fs = s0.fs := hnsp.2.2.2.2.2.2
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hfs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    rw [hK, toByteVec_toList_of_length (mlkem768DecapsWith_length _ _ _ _)]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc] at hpost ⊢
    rw [← sepConj_assoc (stackAt s0.sp 26960) slack R,
      sepConj_comm (stackAt s0.sp 26960) slack,
      ← stackAt_shrink s0.sp stk 26960 hstk hstk_fit] at hpost
    exact hpost

/-! ## 4. Spilled Callee-Saved Frame (`[sp0 - 160, sp0)`) -/

/-- Spilled callee-saved registers (`d15..d8`, `x29, x30`, `x28..x19`) at `[sp0 - 160, sp0)`. -/
@[expose] def SavedFrame04 (sp0 : BitVec 64) (s0 : State) : SepProp :=
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

theorem savedFrame04_entails_memRegion160 (sp0 : BitVec 64) (s0 : State) :
    SavedFrame04 sp0 s0 ⊢ memRegion (sp0 - 160#64) 160 := by
  unfold SavedFrame04
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

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base
