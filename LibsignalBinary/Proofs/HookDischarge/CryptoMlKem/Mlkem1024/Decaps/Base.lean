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
public import LibsignalBinary.Proofs.HookDischarge.Libc.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.RustStd.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
public meta import ProofLib.ProgramReflection
public meta import ProofLib.GenDecodes
public meta import ProofLib.GenPlacedFetches
import ProofLib.SepLogic.WPFrozen

/-!
# `mlkem1024::kyber::decapsulate` (`B23` → `B06`): Block Setup, Specs, and Callee-Saved Frame

1. `PlacedLib` and `WordTree` setup for Block 06 (`kyber_decapsulate` inner core, 13,979 words)
   and Block 23 (`kyber::decapsulate` wrapper, 4 words).
2. `safeSepWP_of_sepWP_env` combinator preserving `CodeLoaded` and `MlKemRoOk`.
3. Spilled callee-saved frame `SavedFrame06` (160 bytes at `[sp0 - 160, sp0)`).
4. Tight-stack (`35968`-byte) raw and core contracts (`kyberDecapsInnerRawSpec`,
   `kyberDecapsRawSpec`, `kyberDecapsCoreSpec`) and `stk`-parameterized caller-struct projection
   specifications (`kyberDecapsProjLenSpec`, `kyberDecapsProjSpec`, `kyberDecapsCliProjSpec`)
   with `SpecSimulates` bridges for both `subroutine_ok` and `safe_subroutine_ok`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open scoped ProofLib.ProgramReflection
open ProofLib.ProgramReflection (WordTree)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (SpecSimulates)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemPlacement
  mlkemMpl
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (withNonSyscallPreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  kyber1024Decaps
  kyber1024Decaps_len
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  cell_entails_memRegion8
  withMlKemRoOk
)

/-! ## 1. Block 06 (`kyber_decapsulate`) & Block 23 (`kyber::decapsulate`) Setup -/

@[expose] def blkLib06 : PlacedLib := mlkemMultiLib.blockLib 6
@[expose] def blkPl06 [MlKemPlacement] : Placement := mlkemMultiLib.blockPlacement mlkemMpl 6
theorem blkPlaceable06 [MlKemPlacement] : blkLib06.Placeable blkPl06 :=
  mlkemMultiLib.placeable_blockLib (by decide) MlKemPlacement.placeable
@[expose] def blkPC06 [MlKemPlacement] : Program := blkLib06.program blkPl06
@[expose] def blkProg06 : Program := { code := blkLib06.text.code, symbols := blkLib06.text.symbols }
set_option maxRecDepth 200000 in
@[expose] def blkTree06 : WordTree := word_tree_of% blkProg06

set_option maxRecDepth 200000 in
theorem blk06_code_eq : blkLib06.text.code = blkTree06.toBytes := by rfl_kernel

theorem blk06_tree_size : blkTree06.checkSize? = some 13979 := by rfl_kernel

@[expose] def blkLib23 : PlacedLib := mlkemMultiLib.blockLib 23
@[expose] def blkPl23 [MlKemPlacement] : Placement := mlkemMultiLib.blockPlacement mlkemMpl 23
theorem blkPlaceable23 [MlKemPlacement] : blkLib23.Placeable blkPl23 :=
  mlkemMultiLib.placeable_blockLib (by decide) MlKemPlacement.placeable
@[expose] def blkPC23 [MlKemPlacement] : Program := blkLib23.program blkPl23
@[expose] def blkProg23 : Program := { code := blkLib23.text.code, symbols := blkLib23.text.symbols }
@[expose] def blkTree23 : WordTree := word_tree_of% blkProg23

theorem blk23_code_eq : blkLib23.text.code = blkTree23.toBytes := by rfl_kernel

theorem blk23_tree_size : blkTree23.checkSize? = some 4 := by rfl_kernel

/-! ## 2. Partial-Correctness Segment Composition & Simulation Combinators -/

/-- Compose a total `SepWP` segment to `mid` with a `SafeSepWP` continuation while preserving
    `CodeLoaded` and `MlKemRoOk` across `KeepsFrozen` transitions. -/
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
      (post' := fun sf Pf => SafeSepWP prog sf Pf Q)
      (Φ := fun m => mlkemMultiLib.CodeLoaded mpl m ∧ MlKemRoOk mpl m)
      (fun _ _ ⟨hc, hr⟩ hkf => ⟨hc.of_keepsFrozen hkf, hr.of_keepsFrozen hkf⟩)
      ⟨hcl, hro⟩ h1
      (fun sm Pm hpc hrun ⟨hc, hr⟩ hp1 => h2 sm Pm hpc hrun hc hr hp1))

/-- Transport `safe_subroutine_ok` along `SpecSimulates`. -/
theorem SpecSimulates.safe_subroutine_ok {α β : Type} {spec₁ : Spec α} {spec₂ : Spec β}
    (hsim : SpecSimulates spec₁ spec₂) {prog : Program} {entry : BitVec 64}
    (h : Arm64.safe_subroutine_ok prog entry spec₁) :
    Arm64.safe_subroutine_ok prog entry spec₂ := fun y R s0 hentry hpre =>
  let ⟨x, R₁, hpre₁, hm⟩ := hsim y R s0 hpre
  (h x R₁ s0 hentry hpre₁).mono fun sf hout => hm sf hout

/-! ## 3. Spilled Callee-Saved Frame (`[sp0 - 160, sp0)`) -/

/-- All 20 AAPCS64 callee-saved registers (`d15..d8`, `x29, x30`, `x28..x19`) spilled by `B06`
    at `[sp0 - 160, sp0)` (`= [sp + 34672, sp + 34832)`). -/
@[expose] def SavedFrame06 (sp0 : BitVec 64) (s0 : State) : SepProp :=
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

theorem savedFrame06_entails_memRegion160 (sp0 : BitVec 64) (s0 : State) :
    SavedFrame06 sp0 s0 ⊢ memRegion (sp0 - 160#64) 160 := by
  unfold SavedFrame06
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
    rw [memRegion_split' (b' := sp0 - 152#64) (n := 8) (k := (152 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 152#64) (b' := sp0 - 144#64) (n := 8) (k := (144 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 144#64) (b' := sp0 - 136#64) (n := 8) (k := (136 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 136#64) (b' := sp0 - 128#64) (n := 8) (k := (128 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 128#64) (b' := sp0 - 120#64) (n := 8) (k := (120 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 120#64) (b' := sp0 - 112#64) (n := 8) (k := (112 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 112#64) (b' := sp0 - 104#64) (n := 8) (k := (104 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 104#64) (b' := sp0 - 96#64) (n := 8) (k := (96 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 96#64) (b' := sp0 - 88#64) (n := 8) (k := (88 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 88#64) (b' := sp0 - 80#64) (n := 8) (k := (80 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 80#64) (b' := sp0 - 72#64) (n := 8) (k := (72 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 72#64) (b' := sp0 - 64#64) (n := 8) (k := (64 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 64#64) (b' := sp0 - 56#64) (n := 8) (k := (56 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 56#64) (b' := sp0 - 48#64) (n := 8) (k := (48 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 48#64) (b' := sp0 - 40#64) (n := 8) (k := (40 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 40#64) (b' := sp0 - 32#64) (n := 8) (k := (32 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 32#64) (b' := sp0 - 24#64) (n := 8) (k := (24 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 24#64) (b' := sp0 - 16#64) (n := 8) (k := (16 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 16#64) (b' := sp0 - 8#64) (n := 8) (k := (8 : Nat)) rfl (by bv_omega) (by decide)]
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

/-! ## 4. Core & Caller-Projection Specifications (`35968` B tight, `stk : Nat` general) -/

/-- Tight-stack (`35968 = 34832 + 1136` bytes) raw contract for `B06` (`kyber_decapsulate` inner
    core, ABI `x0 = ret`, `x1 = skA`, `x2 = ctA`). -/
@[expose] noncomputable def kyberDecapsInnerRawSpec (mpl : MultiPlacement) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8)) where
  pre := fun (ret, skA, sk, ctA, ct) s0 =>
    ⌜s0.readReg64 .x0 = ret ∧
      s0.readReg64 .x1 = skA ∧
      s0.readReg64 .x2 = ctA ∧
      sk.length = 3168 ∧
      ct.length = 1568 ∧
      MlKemRoOk mpl s0.mem⌝ ∗
      (skA ↦ₛ sk) ∗ (ctA ↦ₛ ct) ∗ memRegion ret 32 ∗ stackAt s0.sp 35968
  post := fun (ret, skA, sk, ctA, ct) s0 _sf =>
    (skA ↦ₛ sk) ∗ (ctA ↦ₛ ct) ∗ (ret ↦ₛ kyber1024Decaps sk ct) ∗ stackAt s0.sp 35968
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Tight-stack (`35968` bytes) raw contract for `B23` (`mlkem1024::kyber::decapsulate`, Rust sret
    ABI `x8 = ret`, `x0 = skA`, `x1 = ctA`) prior to `NonSyscallPreserved` lifting. -/
@[expose] noncomputable def kyberDecapsRawSpec (mpl : MultiPlacement) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8)) where
  pre := fun (ret, skA, sk, ctA, ct) s0 =>
    ⌜s0.readReg64 .x8 = ret ∧
      s0.readReg64 .x0 = skA ∧
      s0.readReg64 .x1 = ctA ∧
      sk.length = 3168 ∧
      ct.length = 1568 ∧
      MlKemRoOk mpl s0.mem⌝ ∗
      (skA ↦ₛ sk) ∗ (ctA ↦ₛ ct) ∗ memRegion ret 32 ∗ stackAt s0.sp 35968
  post := fun (ret, skA, sk, ctA, ct) s0 _sf =>
    (skA ↦ₛ sk) ∗ (ctA ↦ₛ ct) ∗ (ret ↦ₛ kyber1024Decaps sk ct) ∗ stackAt s0.sp 35968
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Tight-stack (`35968` bytes) core contract for `B23` with `NonSyscallPreserved`. -/
@[expose] noncomputable def kyberDecapsCoreSpec (mpl : MultiPlacement) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8)) :=
  withNonSyscallPreserved (kyberDecapsRawSpec mpl)

/-- Caller-struct projection spec parameterized by `stk : Nat` with pure length conjuncts in `pre`. -/
@[expose] def kyberDecapsProjLenSpec
    (decaps : List (BitVec 8) → List (BitVec 8) → List (BitVec 8)) (stk : Nat)
    {C : Type} (ret skA : C → BitVec 64) (sk : C → List (BitVec 8))
    (ctA : C → BitVec 64) (ct : C → List (BitVec 8)) : Spec C where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = ret x ∧ s.readReg64 .x0 = skA x ∧ s.readReg64 .x1 = ctA x ∧
      (sk x).length = 3168 ∧ (ct x).length = 1568⌝ ∗
      (skA x ↦ₛ sk x) ∗ (ctA x ↦ₛ ct x) ∗ memRegion (ret x) 32 ∗ stackAt s.sp stk
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (skA x ↦ₛ sk x) ∗ (ctA x ↦ₛ ct x) ∗ (ret x ↦ₛ decaps (sk x) (ct x)) ∗ stackAt s0.sp stk

/-- Caller-struct projection spec parameterized by `stk : Nat` without pure length conjuncts in
    `pre` (when byte lengths are carried as external hypotheses or `List.Vector` types). -/
@[expose] def kyberDecapsProjSpec
    (decaps : List (BitVec 8) → List (BitVec 8) → List (BitVec 8)) (stk : Nat)
    {C : Type} (ret skA : C → BitVec 64) (sk : C → List (BitVec 8))
    (ctA : C → BitVec 64) (ct : C → List (BitVec 8)) : Spec C where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = ret x ∧ s.readReg64 .x0 = skA x ∧ s.readReg64 .x1 = ctA x⌝ ∗
      (skA x ↦ₛ sk x) ∗ (ctA x ↦ₛ ct x) ∗ memRegion (ret x) 32 ∗ stackAt s.sp stk
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (skA x ↦ₛ sk x) ∗ (ctA x ↦ₛ ct x) ∗ (ret x ↦ₛ decaps (sk x) (ct x)) ∗ stackAt s0.sp stk

/-- `List.Vector` caller-struct projection spec matching `CliExt.kemDecapsSpec` (`withStack`
    associativity and `x0, x1, x8` order) by `rfl`. -/
@[expose] def kyberDecapsCliProjSpec
    (decaps : List.Vector (BitVec 8) 3168 → List.Vector (BitVec 8) 1568 → List.Vector (BitVec 8) 32)
    (stk : Nat) {C : Type}
    (skA : C → BitVec 64) (sk : C → List.Vector (BitVec 8) 3168)
    (ctA : C → BitVec 64) (ct : C → List.Vector (BitVec 8) 1568)
    (ret : C → BitVec 64) : Spec C where
  pre := fun x s =>
    (⌜s.readReg64 .x0 = skA x ∧ s.readReg64 .x1 = ctA x ∧ s.readReg64 .x8 = ret x⌝ ∗
      (skA x ↦ₛ (sk x).toList) ∗ (ctA x ↦ₛ (ct x).toList) ∗ memRegion (ret x) 32) ∗
      stackAt s.sp stk
  post := fun x s0 sf =>
    (⌜sf.trace = s0.trace⌝ ∗
      (skA x ↦ₛ (sk x).toList) ∗ (ctA x ↦ₛ (ct x).toList) ∗
      (ret x ↦ₛ (decaps (sk x) (ct x)).toList)) ∗
      stackAt s0.sp stk

theorem kyberDecapsCore_simulates_projLen_nsp
    (decaps : List (BitVec 8) → List (BitVec 8) → List (BitVec 8))
    (hdec : ∀ sk ct, sk.length = 3168 → ct.length = 1568 → decaps sk ct = kyber1024Decaps sk ct)
    (stk : Nat) (hstk : 35968 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    {C : Type} (ret skA : C → BitVec 64) (sk : C → List (BitVec 8))
    (ctA : C → BitVec 64) (ct : C → List (BitVec 8)) (mpl : MultiPlacement) :
    SpecSimulates (kyberDecapsCoreSpec mpl)
      (withMlKemRoOk mpl (withNonSyscallPreserved
        (kyberDecapsProjLenSpec decaps stk ret skA sk ctA ct))) := by
  refine SpecSimulates.of_map ?_
  intro y R s0 hm
  dsimp only [withMlKemRoOk, withNonSyscallPreserved, kyberDecapsProjLenSpec] at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hro, hm⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hx8, hx0, hx1, hsk, hct⟩, hm⟩
  rw [stackAt_shrink s0.sp stk 35968 hstk hstk_fit] at hm
  set slack := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - 35968)
  refine ⟨(ret y, skA y, sk y, ctA y, ct y), slack ∗ R, ?_, ?_⟩
  · dsimp only [kyberDecapsCoreSpec, withNonSyscallPreserved, kyberDecapsRawSpec]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, hx0, hx1, hsk, hct, hro⟩, Satisfies.mono (by sep_frame) hm⟩
  · intro sf _ _ hpost
    dsimp only [kyberDecapsCoreSpec, withNonSyscallPreserved, kyberDecapsRawSpec] at hpost
    dsimp only [withMlKemRoOk, withNonSyscallPreserved, kyberDecapsProjLenSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hnsp, hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hnsp, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hnsp.1, ?_⟩
    rw [hdec (sk y) (ct y) hsk hct, stackAt_shrink s0.sp stk 35968 hstk hstk_fit]
    exact Satisfies.mono (by sep_frame) hpost

theorem kyberDecapsCore_simulates_projLen
    (decaps : List (BitVec 8) → List (BitVec 8) → List (BitVec 8))
    (hdec : ∀ sk ct, sk.length = 3168 → ct.length = 1568 → decaps sk ct = kyber1024Decaps sk ct)
    (stk : Nat) (hstk : 35968 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    {C : Type} (ret skA : C → BitVec 64) (sk : C → List (BitVec 8))
    (ctA : C → BitVec 64) (ct : C → List (BitVec 8)) (mpl : MultiPlacement) :
    SpecSimulates (kyberDecapsCoreSpec mpl)
      (withMlKemRoOk mpl (keepsFs (kyberDecapsProjLenSpec decaps stk ret skA sk ctA ct))) := by
  intro y R s0 hm
  obtain ⟨x, R₁, hpre₁, hpost₁⟩ :=
    kyberDecapsCore_simulates_projLen_nsp decaps hdec stk hstk hstk_fit ret skA sk ctA ct mpl y R s0 hm
  refine ⟨x, R₁, hpre₁, fun sf hout => ?_⟩
  rcases hpost₁ sf hout with ⟨hret, hcc, hp⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withMlKemRoOk, withNonSyscallPreserved, keepsFs] at hp ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
    exact ⟨hp.1.2.2.2.2.2.2, hp.2⟩
  · exact Or.inr hrest

theorem kyberDecapsCore_simulates_proj_nsp
    (decaps : List (BitVec 8) → List (BitVec 8) → List (BitVec 8))
    (hdec : ∀ sk ct, sk.length = 3168 → ct.length = 1568 → decaps sk ct = kyber1024Decaps sk ct)
    (stk : Nat) (hstk : 35968 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    {C : Type} (ret skA : C → BitVec 64) (sk : C → List (BitVec 8))
    (ctA : C → BitVec 64) (ct : C → List (BitVec 8))
    (hsk : ∀ x, (sk x).length = 3168) (hct : ∀ x, (ct x).length = 1568)
    (mpl : MultiPlacement) :
    SpecSimulates (kyberDecapsCoreSpec mpl)
      (withMlKemRoOk mpl (withNonSyscallPreserved
        (kyberDecapsProjSpec decaps stk ret skA sk ctA ct))) := by
  intro y R s0 hm
  dsimp only [withMlKemRoOk, withNonSyscallPreserved, kyberDecapsProjSpec] at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hro, hm⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hx8, hx0, hx1⟩, hm⟩
  have hm_len : s0.mem ⊨ (withMlKemRoOk mpl (withNonSyscallPreserved
      (kyberDecapsProjLenSpec decaps stk ret skA sk ctA ct))).pre y s0 ∗ R := by
    dsimp only [withMlKemRoOk, withNonSyscallPreserved, kyberDecapsProjLenSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hro, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, hx0, hx1, hsk y, hct y⟩, hm⟩
  exact kyberDecapsCore_simulates_projLen_nsp decaps hdec stk hstk hstk_fit ret skA sk ctA ct mpl y R s0 hm_len

theorem kyberDecapsCore_simulates_proj
    (decaps : List (BitVec 8) → List (BitVec 8) → List (BitVec 8))
    (hdec : ∀ sk ct, sk.length = 3168 → ct.length = 1568 → decaps sk ct = kyber1024Decaps sk ct)
    (stk : Nat) (hstk : 35968 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    {C : Type} (ret skA : C → BitVec 64) (sk : C → List (BitVec 8))
    (ctA : C → BitVec 64) (ct : C → List (BitVec 8))
    (hsk : ∀ x, (sk x).length = 3168) (hct : ∀ x, (ct x).length = 1568)
    (mpl : MultiPlacement) :
    SpecSimulates (kyberDecapsCoreSpec mpl)
      (withMlKemRoOk mpl (keepsFs (kyberDecapsProjSpec decaps stk ret skA sk ctA ct))) := by
  intro y R s0 hm
  dsimp only [withMlKemRoOk, keepsFs, kyberDecapsProjSpec] at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hro, hm⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hx8, hx0, hx1⟩, hm⟩
  have hm_len : s0.mem ⊨ (withMlKemRoOk mpl (keepsFs
      (kyberDecapsProjLenSpec decaps stk ret skA sk ctA ct))).pre y s0 ∗ R := by
    dsimp only [withMlKemRoOk, keepsFs, kyberDecapsProjLenSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hro, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, hx0, hx1, hsk y, hct y⟩, hm⟩
  exact kyberDecapsCore_simulates_projLen decaps hdec stk hstk hstk_fit ret skA sk ctA ct mpl y R s0 hm_len

theorem kyberDecapsCore_simulates_cliProj
    (decaps : List.Vector (BitVec 8) 3168 → List.Vector (BitVec 8) 1568 → List.Vector (BitVec 8) 32)
    (hdec : ∀ sk ct, (decaps sk ct).toList = kyber1024Decaps sk.toList ct.toList)
    (stk : Nat) (hstk : 35968 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    {C : Type} (skA : C → BitVec 64) (sk : C → List.Vector (BitVec 8) 3168)
    (ctA : C → BitVec 64) (ct : C → List.Vector (BitVec 8) 1568)
    (ret : C → BitVec 64) (mpl : MultiPlacement) :
    SpecSimulates (kyberDecapsCoreSpec mpl)
      (withMlKemRoOk mpl (keepsFs (kyberDecapsCliProjSpec decaps stk skA sk ctA ct ret))) := by
  refine SpecSimulates.of_map ?_
  intro y R s0 hm
  dsimp only [withMlKemRoOk, keepsFs, kyberDecapsCliProjSpec] at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hro, hm⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hx0, hx1, hx8⟩, hm⟩
  rw [stackAt_shrink s0.sp stk 35968 hstk hstk_fit] at hm
  set slack := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - 35968)
  refine ⟨(ret y, skA y, (sk y).toList, ctA y, (ct y).toList), slack ∗ R, ?_, ?_⟩
  · dsimp only [kyberDecapsCoreSpec, withNonSyscallPreserved, kyberDecapsRawSpec]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, hx0, hx1, (sk y).toList_length, (ct y).toList_length, hro⟩,
      Satisfies.mono (by sep_frame) hm⟩
  · intro sf _ _ hpost
    dsimp only [kyberDecapsCoreSpec, withNonSyscallPreserved, kyberDecapsRawSpec] at hpost
    dsimp only [withMlKemRoOk, keepsFs, kyberDecapsCliProjSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hnsp, hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hnsp.2.2.2.2.2.2, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hnsp.1, ?_⟩
    rw [hdec (sk y) (ct y), stackAt_shrink s0.sp stk 35968 hstk hstk_fit]
    exact Satisfies.mono (by sep_frame) hpost

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base
