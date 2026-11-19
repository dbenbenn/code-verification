/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.ProgramReflection
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Hooks
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhHooksCommon
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.HookDischarge.Libc.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.RustStd.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.ConsumerBridgesBase -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.MlKemCorrectProofs -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps
public meta import ProofLib.ProgramReflection -- proof-setup: allow-public-import

/-!
# Consumer Bridges for All 7 `libcrux_ml_kem` Stock-ELF Hooks (`ConsumerBridges`)

1. Generic precondition combinators `withPremise` (per-call termination predicate adjoining,
   avoiding `correctWith_one`), `withKeepsFrozen`, and bundled load-time `.rodata` witness
   `MlKemRoHoldsBytes mpl m₀` discharging `MlKemRoOk mpl s0.mem`.
2. Layout-generic `mlkemSafeSubroutineOk` (unconditional partial correctness) and
   `mlkemMultiLib.subroutineOk` (per-input `withPremise *CallTerminates` total correctness for the
   5 `SampleNTT` hooks and unconditional total correctness for Hooks #5 and #7), with
   `keepsFs + withVmPreserved`, `withVmPreserved`, and non-budget variants across general `stk`,
   `65536`, `extHookStack`, and concrete `mlkem768Incremental` / `kyber1024EncapsVec` /
   `kyber1024DecapsVec` specializations:
   - Hook #1 (`kemEncapsName`, `B24`, `34240 ≤ stk`): `kemEncapsAtSpec` and `kemEncapsPreservedAtSpec`
   - Hook #2 (`kemDecapsName`, `B23`, `35968 ≤ stk`): `kemDecapsAtSpec`
   - Hook #3 (`mlkemFromSeedName`, `B10`, `33664 ≤ stk`): `mlkemFromSeedAtSpec`
   - Hook #4 (`mlkemEncaps1Name`, `B19`, `18304 ≤ stk`): `mlkemEncaps1AtSpec`
   - Hook #5 (`mlkemEncaps2Name`, `B20`, `6128 ≤ stk`): `mlkemEncaps2AtSpec` (unconditional)
   - Hook #6 (`mlkemDecapsName`, `B22`, `26960 ≤ stk`): `mlkemDecapsAtSpec`
   - Hook #7 (`mlkemValidatePkName`, `B21`, `5824 ≤ stk`): `mlkemValidatePkAtSpec` (unconditional)
3. Generic and per-hook `*_of_holdsBytes_keepsFrozen` bridges discharging `MlKemRoOk` for all
   7 hooks from `MlKemRoHoldsBytes mpl m₀` and `m₀.KeepsFrozen s0.mem`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.ConsumerBridges

open Arm64 Arm64.Obj ProofLib SepProp
open scoped ProofLib.ProgramReflection
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalSpqrV1 (
  MlKem
  MlkemDecapsCall
  MlkemEncaps1Call
  MlkemEncaps2Call
  MlkemFromSeedCall
  MlkemValidatePkCall
  mlkemDecapsName
  mlkemDecapsSpec
  mlkemEncaps1Name
  mlkemEncaps1Spec
  mlkemEncaps2Name
  mlkemEncaps2Spec
  mlkemFromSeedName
  mlkemFromSeedSpec
  mlkemValidatePkName
  mlkemValidatePkSpec
)
open CryptoVerification.E2E (PqxdhPrims)
open CryptoVerification.SignalSession.CliExt (kemDecapsSpec kemEncapsSpec)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs withStack)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (SpecSimulates)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (
  mlkemData00Bytes
  mlkemData01Bytes
  mlkemData02Bytes
  mlkemData03Bytes
  mlkemData04Bytes
  mlkemData05Bytes
  mlkemData06Bytes
  mlkemData07Bytes
  mlkemData08Bytes
  mlkemData09Bytes
  mlkemData10Bytes
  mlkemMultiLib
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (MlKemBlockOk MlKemBlockSafeOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Kyber1024DecapsTerminates
  Kyber1024EncapsTerminates
  Mlkem768DecapsTerminates
  Mlkem768Encaps1Terminates
  Mlkem768FromSeedTerminates
  kyber1024Decaps
  kyber1024Encaps
  mlkem768DecapsWith
  mlkem768Encaps2List
  mlkem768Incremental
  mlkem768KeyPairWith
  mlkem768ValidPk
  sampleNtt
  toByteVec
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.MlKemCorrectProofs (
  kyber1024DecapsVec
  kyber1024DecapsVec_toList
  kyber1024EncapsVec
  kyber1024EncapsVec_fst_toList
  kyber1024EncapsVec_snd_toList
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.ConsumerBridgesBase (
  kemDecapsAtSpec
  kemDecapsName
  kemEncapsAtSpec
  kemEncapsName
  kemEncapsPreservedAtSpec
  mlkemBlockOk_withMlKemRoOk_withVmPreserved
  mlkemBlockSafeOk_withMlKemRoOk_withVmPreserved
  mlkemDecapsAtSpec
  mlkemEncaps1AtSpec
  mlkemEncaps2AtSpec
  mlkemEncaps2_65536_vm_subroutineOk
  mlkemEncaps2_at_keepsFs_vm_subroutineOk
  mlkemEncaps2_at_subroutineOk
  mlkemEncaps2_at_vm_subroutineOk
  mlkemEncaps2_inc_vm_subroutineOk
  mlkemEncaps2_subroutineOk
  mlkemEncaps2_vm_subroutineOk
  mlkemFromSeedAtSpec
  mlkemRoOk_of_holdsBytes_keepsFrozen
  mlkemSafeSubroutineOk
  mlkemSafeSubroutineOk_of_blockSafeOk_ext
  mlkemSafeSubroutineOk_of_subroutineOk
  mlkemSubroutineOk_of_blockOk_ext
  mlkemValidatePkAtSpec
  mlkemValidatePk_65536_vm_subroutineOk
  mlkemValidatePk_at_keepsFs_vm_subroutineOk
  mlkemValidatePk_at_subroutineOk
  mlkemValidatePk_at_vm_subroutineOk
  mlkemValidatePk_inc_vm_subroutineOk
  mlkemValidatePk_subroutineOk
  mlkemValidatePk_vm_subroutineOk
  specSimulates_drop_withVmPreserved
  specSimulates_keepsFs_withVmPreserved
  specSimulates_mlkemBlockOk
  specSimulates_mlkemBlockSafeOk
  specSimulates_mlkemSafeSubroutineOk
  specSimulates_safe_subroutine_ok
  specSimulates_withMlKemRoOk_map
  withMlKemRoOk
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed (
  blk10_from_seed_proj_ok
  blk10_from_seed_proj_safe_ok
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base (
  mlkem768Incremental_fromSeed_dk_toList
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1 (
  blk19_encaps1_proj_ok
  blk19_encaps1_proj_safe_ok
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps (
  blk22_decaps_proj_ok
  blk22_decaps_proj_safe_ok
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps (
  blk24_keepRand_proj_ok
  blk24_keepRand_proj_safe_ok
  blk24_kemEncapsVec_proj_ok
  blk24_kemEncapsVec_proj_safe_ok
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base (
  kemEncapsVecProjSpec
  kyberEncapsKeepRandProjSpec
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps (
  blk23_cliProj_ok
  blk23_cliProj_safe_ok
)

/-! ## 1. `withPremise`, `withKeepsFrozen`, `MlKemRoHoldsBytes`, & Generic Transport -/

/-- Adjoin a pure call-argument premise `⌜P x⌝` to `spec.pre` (used for per-input `SampleNTT`
    rejection-loop termination predicates, avoiding any `correctWith_one` or global `∀` premise). -/
@[expose] def withPremise {α : Type} (P : α → Prop) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s0 => ⌜P x⌝ ∗ spec.pre x s0 }

/-- Adjoin load-time `⌜m₀.KeepsFrozen s0.mem⌝` to `spec.pre`. -/
@[expose] def withKeepsFrozen {α : Type} (m₀ : Memory) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s0 => ⌜m₀.KeepsFrozen s0.mem⌝ ∗ spec.pre x s0 }

/-- Bundled load-time `Obj.HoldsBytes` witness for all 11 `libcrux_ml_kem` `.rodata` tables in
    initial memory `m₀`. -/
structure MlKemRoHoldsBytes (mpl : MultiPlacement) (m₀ : Memory) : Prop where
  h00 : HoldsBytes m₀ (mpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0")
    mlkemData00Bytes (fun _ => Perm.ro)
  h01 : HoldsBytes m₀ (mpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29")
    mlkemData01Bytes (fun _ => Perm.ro)
  h02 : HoldsBytes m₀ (mpl.ρ "libcrux_ml_kem:.rodata.cst16.0") mlkemData02Bytes (fun _ => Perm.ro)
  h03 : HoldsBytes m₀ (mpl.ρ "libcrux_ml_kem:.rodata.cst16.1") mlkemData03Bytes (fun _ => Perm.ro)
  h04 : HoldsBytes m₀ (mpl.ρ "libcrux_ml_kem:.rodata.cst16.2") mlkemData04Bytes (fun _ => Perm.ro)
  h05 : HoldsBytes m₀ (mpl.ρ "libcrux_ml_kem:.rodata.cst16.3") mlkemData05Bytes (fun _ => Perm.ro)
  h06 : HoldsBytes m₀ (mpl.ρ "libcrux_ml_kem:.rodata.cst16.4") mlkemData06Bytes (fun _ => Perm.ro)
  h07 : HoldsBytes m₀ (mpl.ρ "libcrux_ml_kem:.rodata.cst16.5") mlkemData07Bytes (fun _ => Perm.ro)
  h08 : HoldsBytes m₀ (mpl.ρ "libcrux_ml_kem:.rodata.cst16.6") mlkemData08Bytes (fun _ => Perm.ro)
  h09 : HoldsBytes m₀ (mpl.ρ "libcrux_ml_kem:.rodata.cst16.7") mlkemData09Bytes (fun _ => Perm.ro)
  h10 : HoldsBytes m₀ (mpl.ρ "libcrux_ml_kem:.rodata.cst16.8") mlkemData10Bytes (fun _ => Perm.ro)

theorem MlKemRoHoldsBytes.roOk {mpl : MultiPlacement} {m₀ m : Memory}
    (h : MlKemRoHoldsBytes mpl m₀) (hkf : m₀.KeepsFrozen m) : MlKemRoOk mpl m :=
  mlkemRoOk_of_holdsBytes_keepsFrozen h.h00 h.h01 h.h02 h.h03 h.h04 h.h05
    h.h06 h.h07 h.h08 h.h09 h.h10 hkf

/-- Discharge `withMlKemRoOk mpl spec` to `withKeepsFrozen m₀ spec` from `MlKemRoHoldsBytes mpl m₀`. -/
theorem specSimulates_holdsBytes_keepsFrozen {α : Type} {mpl : MultiPlacement} {m₀ : Memory}
    (hro : MlKemRoHoldsBytes mpl m₀) (spec : Spec α) :
    SpecSimulates (withMlKemRoOk mpl spec) (withKeepsFrozen m₀ spec) := by
  intro x R s0 hpre
  dsimp only [withKeepsFrozen] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hkf, hpre'⟩ := hpre
  refine ⟨x, R, ?_, fun _ hout => hout⟩
  dsimp only [withMlKemRoOk]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hro.roOk hkf, hpre'⟩

/-- Generic `mlkemMultiLib.subroutineOk` transport from `withMlKemRoOk` to `withKeepsFrozen m₀`
    given load-time `MlKemRoHoldsBytes`. -/
theorem subroutineOk_of_holdsBytes_keepsFrozen {α : Type} {fnName : String}
    {spec : MultiPlacement → Spec α} {m₀ : Memory}
    (hro : ∀ mpl, mlkemMultiLib.Placeable mpl → MlKemRoHoldsBytes mpl m₀)
    {externs : String → Option (State → State)}
    (hok : mlkemMultiLib.subroutineOk fnName (fun mpl => withMlKemRoOk mpl (spec mpl)) externs) :
    mlkemMultiLib.subroutineOk fnName (fun mpl => withKeepsFrozen m₀ (spec mpl)) externs := by
  obtain ⟨hexp, i, off, hsym, hsub⟩ := hok
  refine ⟨hexp, i, off, hsym, fun mpl hpl => ?_⟩
  exact ((specSimulates_holdsBytes_keepsFrozen (hro mpl hpl) (spec mpl)).withCodeLoaded
    mlkemMultiLib mpl).subroutine_ok (hsub mpl hpl)

/-- Generic `mlkemSafeSubroutineOk` transport from `withMlKemRoOk` to `withKeepsFrozen m₀`
    given load-time `MlKemRoHoldsBytes`. -/
theorem safeSubroutineOk_of_holdsBytes_keepsFrozen {α : Type} {fnName : String}
    {spec : MultiPlacement → Spec α} {m₀ : Memory}
    (hro : ∀ mpl, mlkemMultiLib.Placeable mpl → MlKemRoHoldsBytes mpl m₀)
    {externs : String → Option (State → State)}
    (hok : mlkemSafeSubroutineOk fnName (fun mpl => withMlKemRoOk mpl (spec mpl)) externs) :
    mlkemSafeSubroutineOk fnName (fun mpl => withKeepsFrozen m₀ (spec mpl)) externs := by
  obtain ⟨hexp, i, off, hsym, hsub⟩ := hok
  refine ⟨hexp, i, off, hsym, fun mpl hpl => ?_⟩
  exact specSimulates_safe_subroutine_ok
    ((specSimulates_holdsBytes_keepsFrozen (hro mpl hpl) (spec mpl)).withCodeLoaded mlkemMultiLib mpl)
    (hsub mpl hpl)

theorem keepsFs_withPremise {α : Type} (P : α → Prop) (spec : Spec α) :
    keepsFs (withPremise P spec) = withPremise P (keepsFs spec) := rfl

theorem withVmPreserved_withPremise {α : Type} (P : α → Prop) (spec : Spec α) :
    withVmPreserved (withPremise P spec) = withPremise P (withVmPreserved spec) := rfl

theorem specSimulates_withPremise_of_forall {α : Type} {P : α → Prop}
    (hP : ∀ x, P x) (spec : Spec α) :
    SpecSimulates (withPremise P spec) spec := by
  intro x R s0 hpre
  refine ⟨x, R, ?_, fun _ hout => hout⟩
  dsimp only [withPremise]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hP x, hpre⟩

private def pullbackSpec {α β : Type} (f : β → α) (spec : Spec α) : Spec β where
  pre := fun y s0 => spec.pre (f y) s0
  post := fun y s0 sf => spec.post (f y) s0 sf
  onPanic := fun y s0 sf => spec.onPanic (f y) s0 sf
  onExit := fun y code s0 sf => spec.onExit (f y) code s0 sf
  onOom := fun y s0 sf => spec.onOom (f y) s0 sf

private theorem specSimulates_subtype_withPremise {α : Type} (P : α → Prop) (spec : Spec α) :
    SpecSimulates (pullbackSpec (Subtype.val (p := P)) spec) (withPremise P spec) := by
  intro x R s0 hpre
  dsimp only [withPremise] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hP, hpre'⟩ := hpre
  exact ⟨⟨x, hP⟩, R, hpre', fun _ hout => hout⟩

/-! ## 2. Call Types, Per-Input Termination Predicates, & Generic Export Lifters -/

/-- Call tuple type for Hook #1 (`kemEncapsName`, `B24`). -/
abbrev KemEncapsCall : Type :=
  BitVec 64 × List.Vector (BitVec 8) 1568 × BitVec 64 × List.Vector (BitVec 8) 32 × BitVec 64

/-- Call tuple type for Hook #2 (`kemDecapsName`, `B23`). -/
abbrev KemDecapsCall : Type :=
  BitVec 64 × List.Vector (BitVec 8) 3168 × BitVec 64 × List.Vector (BitVec 8) 1568 × BitVec 64

/-- Per-call matrix `SampleNTT` termination predicate for Hook #1 (`kemEncapsName`, `B24`). -/
@[expose] def KemEncapsCallTerminates (x : KemEncapsCall) : Prop :=
  Kyber1024EncapsTerminates x.2.1.toList

/-- Per-call matrix `SampleNTT` termination predicate for Hook #2 (`kemDecapsName`, `B23`). -/
@[expose] def KemDecapsCallTerminates (x : KemDecapsCall) : Prop :=
  Kyber1024DecapsTerminates x.2.1.toList

/-- Per-call matrix `SampleNTT` termination predicate for Hook #3 (`mlkemFromSeedName`, `B10`). -/
@[expose] def MlkemFromSeedCallTerminates (x : MlkemFromSeedCall) : Prop :=
  Mlkem768FromSeedTerminates x.seed

/-- Per-call matrix `SampleNTT` termination predicate for Hook #4 (`mlkemEncaps1Name`, `B19`). -/
@[expose] def MlkemEncaps1CallTerminates (x : MlkemEncaps1Call) : Prop :=
  Mlkem768Encaps1Terminates x.hdr

/-- Per-call matrix `SampleNTT` termination predicate for Hook #6 (`mlkemDecapsName`, `B22`). -/
@[expose] def MlkemDecapsCallTerminates (x : MlkemDecapsCall) : Prop :=
  Mlkem768DecapsTerminates x.dk

private theorem export_keepsFs_vm_subroutineOk {j : Nat} {sym : String} {α : Type}
    {spec : Spec α}
    (hok : MlKemBlockOk j (fun mpl => withMlKemRoOk mpl (keepsFs spec)))
    (externs : String → Option (State → State))
    (hj : j < mlkemMultiLib.blocks.length := by decide)
    (hexp : sym ∈ mlkemMultiLib.exports := by decide)
    (hsym : lookupBlockSym sym mlkemMultiLib.blocks = some (j, 0) := by rfl_kernel)
    (hpan : (keepsFs spec).onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hex : (keepsFs spec).onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom : (keepsFs spec).onOom = fun _ _ _ => ⌜False⌝ := by rfl)
    (h_pre_mem : ∀ x (s : State) (m : Memory),
      (keepsFs spec).pre x (s.setMem m) = (keepsFs spec).pre x s := by
        intro _ s _; cases s; rfl)
    (h_post_mem : ∀ x (s0 sf : State) (m0 mf : Memory),
      (keepsFs spec).post x (s0.setMem m0) (sf.setMem mf) = (keepsFs spec).post x s0 sf := by
        intro _ s0 sf _ _; cases s0; cases sf; rfl) :
    mlkemMultiLib.subroutineOk sym
      (fun mpl => withMlKemRoOk mpl (keepsFs (withVmPreserved spec))) externs :=
  mlkemSubroutineOk_of_blockOk_ext
    (specSimulates_mlkemBlockOk
      (fun mpl => specSimulates_withMlKemRoOk_map mpl specSimulates_keepsFs_withVmPreserved)
      (mlkemBlockOk_withMlKemRoOk_withVmPreserved hok hj hpan hex hoom h_pre_mem h_post_mem))
    externs hj hexp hsym

private theorem export_keepsFs_vm_safeSubroutineOk {j : Nat} {sym : String} {α : Type}
    {spec : Spec α}
    (hok : MlKemBlockSafeOk j (fun mpl => withMlKemRoOk mpl (keepsFs spec)))
    (externs : String → Option (State → State))
    (hj : j < mlkemMultiLib.blocks.length := by decide)
    (hexp : sym ∈ mlkemMultiLib.exports := by decide)
    (hsym : lookupBlockSym sym mlkemMultiLib.blocks = some (j, 0) := by rfl_kernel)
    (hpan : (keepsFs spec).onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hex : (keepsFs spec).onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom : (keepsFs spec).onOom = fun _ _ _ => ⌜False⌝ := by rfl)
    (h_pre_mem : ∀ x (s : State) (m : Memory),
      (keepsFs spec).pre x (s.setMem m) = (keepsFs spec).pre x s := by
        intro _ s _; cases s; rfl)
    (h_post_mem : ∀ x (s0 sf : State) (m0 mf : Memory),
      (keepsFs spec).post x (s0.setMem m0) (sf.setMem mf) = (keepsFs spec).post x s0 sf := by
        intro _ s0 sf _ _; cases s0; cases sf; rfl) :
    mlkemSafeSubroutineOk sym
      (fun mpl => withMlKemRoOk mpl (keepsFs (withVmPreserved spec))) externs :=
  mlkemSafeSubroutineOk_of_blockSafeOk_ext
    (specSimulates_mlkemBlockSafeOk
      (fun mpl => specSimulates_withMlKemRoOk_map mpl specSimulates_keepsFs_withVmPreserved)
      (mlkemBlockSafeOk_withMlKemRoOk_withVmPreserved hok hj hpan hex hoom h_pre_mem h_post_mem))
    externs hj hexp hsym

/-! ## 3. Hook #1 (`kemEncapsName`, `B24`, `34,240` B Tight Stack) -/

private theorem kemEncapsVecProj_simulates_atSpec (stk : Nat) (Q : PqxdhPrims) {C : Type}
    (f : C → KemEncapsCall) :
    SpecSimulates
      (keepsFs (kemEncapsVecProjSpec stk Q.encaps
        (fun u => (f u).2.2.2.2) (fun u => (f u).1) (fun u => (f u).2.1)
        (fun u => (f u).2.2.1) (fun u => (f u).2.2.2.1)))
      (pullbackSpec f (keepsFs (kemEncapsAtSpec stk Q))) := by
  refine SpecSimulates.of_map fun u R s0 hpre => ?_
  rcases h : f u with ⟨pkA, pk, rA, rnd, ret⟩
  refine ⟨u, R, ?_, fun sf _ _ hpost => ?_⟩
  · dsimp only [pullbackSpec, keepsFs, kemEncapsAtSpec, withStack] at hpre
    rw [h] at hpre
    dsimp only [keepsFs, kemEncapsVecProjSpec]
    rw [h]
    dsimp only at hpre ⊢
    simpa only [sepConj_assoc] using hpre
  · dsimp only [keepsFs, kemEncapsVecProjSpec] at hpost
    dsimp only [pullbackSpec, keepsFs, kemEncapsAtSpec, withStack]
    rw [h] at hpost ⊢
    dsimp only at hpost ⊢
    simpa only [sepConj_assoc] using hpost

private theorem keepRandProj_simulates_preservedAtSpec (stk : Nat) (Q : PqxdhPrims)
    (hQ : ∀ pk rand,
      (Q.encaps pk rand).1.toList = (kyber1024Encaps pk.toList rand.toList).1 ∧
      (Q.encaps pk rand).2.toList = (kyber1024Encaps pk.toList rand.toList).2)
    {C : Type} (f : C → KemEncapsCall) :
    SpecSimulates
      (keepsFs (kyberEncapsKeepRandProjSpec stk kyber1024Encaps
        (fun u => (f u).2.2.2.2) (fun u => (f u).1) (fun u => (f u).2.1.toList)
        (fun u => (f u).2.2.1) (fun u => (f u).2.2.2.1.toList)))
      (pullbackSpec f (keepsFs (kemEncapsPreservedAtSpec stk Q))) := by
  refine SpecSimulates.of_map fun u R s0 hpre => ?_
  rcases h : f u with ⟨pkA, pk, rA, rnd, ret⟩
  refine ⟨u, R, ?_, fun sf _ _ hpost => ?_⟩
  · dsimp only [pullbackSpec, keepsFs, kemEncapsPreservedAtSpec, withStack] at hpre
    rw [h] at hpre
    dsimp only at hpre
    simp only [sepConj_assoc] at hpre
    rw [satisfies_pure_sepConj] at hpre
    obtain ⟨⟨hx0, hx1, hx8⟩, hspat⟩ := hpre
    dsimp only [keepsFs, kyberEncapsKeepRandProjSpec]
    rw [h]
    dsimp only
    simp only [sepConj_assoc]
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx8, pk.toList_length, rnd.toList_length⟩, hspat⟩
  · dsimp only [keepsFs, kyberEncapsKeepRandProjSpec] at hpost
    dsimp only [pullbackSpec, keepsFs, kemEncapsPreservedAtSpec, withStack]
    rw [h] at hpost ⊢
    dsimp only at hpost ⊢
    rw [(hQ pk rnd).1, (hQ pk rnd).2]
    simpa only [sepConj_assoc] using hpost

/-- Hook #1 (`kemEncapsName`, `B24`): unconditional partial-correctness `keepsFs + withVmPreserved`
    bridge (`34240 ≤ stk`). -/
theorem kemEncaps_at_keepsFs_vm_safeSubroutineOk (Q : PqxdhPrims)
    (hQ : ∀ pk rand,
      (Q.encaps pk rand).1.toList = (kyber1024Encaps pk.toList rand.toList).1 ∧
      (Q.encaps pk rand).2.toList = (kyber1024Encaps pk.toList rand.toList).2)
    (stk : Nat) (hstk : 34240 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemSafeSubroutineOk kemEncapsName
      (fun mpl => withMlKemRoOk mpl (keepsFs (withVmPreserved (kemEncapsAtSpec stk Q))))
      externs :=
  export_keepsFs_vm_safeSubroutineOk
    (specSimulates_mlkemBlockSafeOk
      (fun mpl => specSimulates_withMlKemRoOk_map mpl (kemEncapsVecProj_simulates_atSpec stk Q id))
      (blk24_kemEncapsVec_proj_safe_ok stk hstk hstk_fit Q.encaps hQ
        (C := KemEncapsCall) (fun x => x.2.2.2.2) (fun x => x.1) (fun x => x.2.1)
        (fun x => x.2.2.1) (fun x => x.2.2.2.1)))
    externs

/-- Hook #1 (`kemEncapsName`, `B24`): unconditional partial-correctness `withVmPreserved` bridge. -/
theorem kemEncaps_at_vm_safeSubroutineOk (Q : PqxdhPrims)
    (hQ : ∀ pk rand,
      (Q.encaps pk rand).1.toList = (kyber1024Encaps pk.toList rand.toList).1 ∧
      (Q.encaps pk rand).2.toList = (kyber1024Encaps pk.toList rand.toList).2)
    (stk : Nat) (hstk : 34240 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemSafeSubroutineOk kemEncapsName
      (fun mpl => withMlKemRoOk mpl (withVmPreserved (kemEncapsAtSpec stk Q))) externs :=
  specSimulates_mlkemSafeSubroutineOk
    (fun mpl => specSimulates_withMlKemRoOk_map mpl SpecSimulates.drop_keepsFs)
    (kemEncaps_at_keepsFs_vm_safeSubroutineOk Q hQ stk hstk hstk_fit externs)

/-- Hook #1 (`kemEncapsName`, `B24`): per-input `withPremise KemEncapsCallTerminates`
    total-correctness `keepsFs + withVmPreserved` bridge (`34240 ≤ stk`). -/
theorem kemEncaps_at_keepsFs_vm_premise_subroutineOk (Q : PqxdhPrims)
    (hQ : ∀ pk rand,
      (Q.encaps pk rand).1.toList = (kyber1024Encaps pk.toList rand.toList).1 ∧
      (Q.encaps pk rand).2.toList = (kyber1024Encaps pk.toList rand.toList).2)
    (stk : Nat) (hstk : 34240 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk kemEncapsName
      (fun mpl => withMlKemRoOk mpl
        (withPremise KemEncapsCallTerminates (keepsFs (withVmPreserved (kemEncapsAtSpec stk Q)))))
      externs :=
  export_keepsFs_vm_subroutineOk (j := 24)
    (spec := withPremise KemEncapsCallTerminates (kemEncapsAtSpec stk Q))
    (specSimulates_mlkemBlockOk
      (fun mpl => specSimulates_withMlKemRoOk_map mpl
        (specSimulates_subtype_withPremise KemEncapsCallTerminates (keepsFs (kemEncapsAtSpec stk Q))))
      (specSimulates_mlkemBlockOk
        (fun mpl => specSimulates_withMlKemRoOk_map mpl
          (kemEncapsVecProj_simulates_atSpec stk Q Subtype.val))
        (blk24_kemEncapsVec_proj_ok stk hstk hstk_fit Q.encaps hQ
          (C := { x : KemEncapsCall // KemEncapsCallTerminates x })
          (fun u => u.1.2.2.2.2) (fun u => u.1.1) (fun u => u.1.2.1)
          (fun u => u.1.2.2.1) (fun u => u.1.2.2.2.1) (fun u => u.2))))
    externs

/-- Hook #1 (`kemEncapsName`, `B24`): per-input `withPremise KemEncapsCallTerminates`
    total-correctness `withVmPreserved` bridge (`34240 ≤ stk`). -/
theorem kemEncaps_at_vm_premise_subroutineOk (Q : PqxdhPrims)
    (hQ : ∀ pk rand,
      (Q.encaps pk rand).1.toList = (kyber1024Encaps pk.toList rand.toList).1 ∧
      (Q.encaps pk rand).2.toList = (kyber1024Encaps pk.toList rand.toList).2)
    (stk : Nat) (hstk : 34240 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk kemEncapsName
      (fun mpl => withMlKemRoOk mpl
        (withPremise KemEncapsCallTerminates (withVmPreserved (kemEncapsAtSpec stk Q))))
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl => specSimulates_withMlKemRoOk_map mpl
      (SpecSimulates.drop_keepsFs (spec := withVmPreserved
        (withPremise KemEncapsCallTerminates (kemEncapsAtSpec stk Q)))))
    (kemEncaps_at_keepsFs_vm_premise_subroutineOk Q hQ stk hstk hstk_fit externs)

/-- Hook #1 (`kemEncapsName`, `B24`): per-input `withPremise KemEncapsCallTerminates`
    non-budget `subroutineOk` bridge (`34240 ≤ stk`). -/
theorem kemEncaps_at_premise_subroutineOk (Q : PqxdhPrims)
    (hQ : ∀ pk rand,
      (Q.encaps pk rand).1.toList = (kyber1024Encaps pk.toList rand.toList).1 ∧
      (Q.encaps pk rand).2.toList = (kyber1024Encaps pk.toList rand.toList).2)
    (stk : Nat) (hstk : 34240 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk kemEncapsName
      (fun mpl => withMlKemRoOk mpl
        (withPremise KemEncapsCallTerminates (kemEncapsAtSpec stk Q)))
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl => specSimulates_withMlKemRoOk_map mpl specSimulates_drop_withVmPreserved)
    (kemEncaps_at_vm_premise_subroutineOk Q hQ stk hstk hstk_fit externs)

/-- Hook #1 (`kemEncapsName`, `B24`): convenience `subroutineOk` corollary under
    `∀ x, KemEncapsCallTerminates x`. -/
theorem kemEncaps_at_vm_subroutineOk (Q : PqxdhPrims)
    (hQ : ∀ pk rand,
      (Q.encaps pk rand).1.toList = (kyber1024Encaps pk.toList rand.toList).1 ∧
      (Q.encaps pk rand).2.toList = (kyber1024Encaps pk.toList rand.toList).2)
    (stk : Nat) (hstk : 34240 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (hTerm : ∀ x, KemEncapsCallTerminates x)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk kemEncapsName
      (fun mpl => withMlKemRoOk mpl (withVmPreserved (kemEncapsAtSpec stk Q))) externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl => specSimulates_withMlKemRoOk_map mpl
      (specSimulates_withPremise_of_forall hTerm _))
    (kemEncaps_at_vm_premise_subroutineOk Q hQ stk hstk hstk_fit externs)

/-- Hook #1 (`kemEncapsName`, `B24`): stronger `kemEncapsPreservedAtSpec` (preserving
    `(rA ↦ₛ rnd.toList)`) unconditional partial-correctness `keepsFs + withVmPreserved` bridge. -/
theorem kemEncapsPreserved_at_keepsFs_vm_safeSubroutineOk (Q : PqxdhPrims)
    (hQ : ∀ pk rand,
      (Q.encaps pk rand).1.toList = (kyber1024Encaps pk.toList rand.toList).1 ∧
      (Q.encaps pk rand).2.toList = (kyber1024Encaps pk.toList rand.toList).2)
    (stk : Nat) (hstk : 34240 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemSafeSubroutineOk kemEncapsName
      (fun mpl => withMlKemRoOk mpl (keepsFs (withVmPreserved (kemEncapsPreservedAtSpec stk Q))))
      externs :=
  export_keepsFs_vm_safeSubroutineOk
    (specSimulates_mlkemBlockSafeOk
      (fun mpl => specSimulates_withMlKemRoOk_map mpl
        (keepRandProj_simulates_preservedAtSpec stk Q hQ id))
      (blk24_keepRand_proj_safe_ok stk hstk hstk_fit kyber1024Encaps (fun _ _ => rfl)
        (C := KemEncapsCall) (fun x => x.2.2.2.2) (fun x => x.1) (fun x => x.2.1.toList)
        (fun x => x.2.2.1) (fun x => x.2.2.2.1.toList)))
    externs

/-- Hook #1 (`kemEncapsName`, `B24`): stronger `kemEncapsPreservedAtSpec` per-input
    `withPremise KemEncapsCallTerminates` total-correctness `keepsFs + withVmPreserved` bridge. -/
theorem kemEncapsPreserved_at_keepsFs_vm_premise_subroutineOk (Q : PqxdhPrims)
    (hQ : ∀ pk rand,
      (Q.encaps pk rand).1.toList = (kyber1024Encaps pk.toList rand.toList).1 ∧
      (Q.encaps pk rand).2.toList = (kyber1024Encaps pk.toList rand.toList).2)
    (stk : Nat) (hstk : 34240 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk kemEncapsName
      (fun mpl => withMlKemRoOk mpl
        (withPremise KemEncapsCallTerminates
          (keepsFs (withVmPreserved (kemEncapsPreservedAtSpec stk Q)))))
      externs :=
  export_keepsFs_vm_subroutineOk (j := 24)
    (spec := withPremise KemEncapsCallTerminates (kemEncapsPreservedAtSpec stk Q))
    (specSimulates_mlkemBlockOk
      (fun mpl => specSimulates_withMlKemRoOk_map mpl
        (specSimulates_subtype_withPremise KemEncapsCallTerminates
          (keepsFs (kemEncapsPreservedAtSpec stk Q))))
      (specSimulates_mlkemBlockOk
        (fun mpl => specSimulates_withMlKemRoOk_map mpl
          (keepRandProj_simulates_preservedAtSpec stk Q hQ Subtype.val))
        (blk24_keepRand_proj_ok stk hstk hstk_fit kyber1024Encaps (fun _ _ => rfl)
          (C := { x : KemEncapsCall // KemEncapsCallTerminates x })
          (fun u => u.1.2.2.2.2) (fun u => u.1.1) (fun u => u.1.2.1.toList)
          (fun u => u.1.2.2.1) (fun u => u.1.2.2.2.1.toList) (fun u => u.2))))
    externs

/-- Hook #1 (`kemEncapsName`, `B24`): `stk = 65536` `withVmPreserved` per-input bridge. -/
theorem kemEncaps_65536_vm_premise_subroutineOk (Q : PqxdhPrims)
    (hQ : ∀ pk rand,
      (Q.encaps pk rand).1.toList = (kyber1024Encaps pk.toList rand.toList).1 ∧
      (Q.encaps pk rand).2.toList = (kyber1024Encaps pk.toList rand.toList).2)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk kemEncapsName
      (fun mpl => withMlKemRoOk mpl
        (withPremise KemEncapsCallTerminates (withVmPreserved (kemEncapsAtSpec 65536 Q))))
      externs :=
  kemEncaps_at_vm_premise_subroutineOk Q hQ 65536 (by decide) (by decide) externs

/-- Hook #1 (`kemEncapsName`, `B24`): `extHookStack` (`34240 ≤ extHookStack`) `kemEncapsSpec Q`
    per-input `withVmPreserved` bridge. -/
theorem kemEncaps_vm_premise_subroutineOk (hstk : 34240 ≤ extHookStack) (Q : PqxdhPrims)
    (hQ : ∀ pk rand,
      (Q.encaps pk rand).1.toList = (kyber1024Encaps pk.toList rand.toList).1 ∧
      (Q.encaps pk rand).2.toList = (kyber1024Encaps pk.toList rand.toList).2)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk kemEncapsName
      (fun mpl => withMlKemRoOk mpl
        (withPremise KemEncapsCallTerminates (withVmPreserved (kemEncapsSpec Q))))
      externs :=
  kemEncaps_at_vm_premise_subroutineOk Q hQ extHookStack hstk (by decide) externs

/-! ## 4. Hook #2 (`kemDecapsName`, `B23`, `35,968` B Tight Stack) -/

/-- Hook #2 (`kemDecapsName`, `B23`): unconditional partial-correctness `keepsFs + withVmPreserved`
    bridge (`35968 ≤ stk`). -/
theorem kemDecaps_at_keepsFs_vm_safeSubroutineOk (Q : PqxdhPrims)
    (hQ : ∀ sk ct, (Q.decaps sk ct).toList = kyber1024Decaps sk.toList ct.toList)
    (stk : Nat) (hstk : 35968 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemSafeSubroutineOk kemDecapsName
      (fun mpl => withMlKemRoOk mpl (keepsFs (withVmPreserved (kemDecapsAtSpec stk Q))))
      externs :=
  export_keepsFs_vm_safeSubroutineOk
    (blk23_cliProj_safe_ok Q.decaps hQ stk hstk hstk_fit
      (C := KemDecapsCall) (fun x => x.1) (fun x => x.2.1)
      (fun x => x.2.2.1) (fun x => x.2.2.2.1) (fun x => x.2.2.2.2))
    externs

/-- Hook #2 (`kemDecapsName`, `B23`): unconditional partial-correctness `withVmPreserved` bridge. -/
theorem kemDecaps_at_vm_safeSubroutineOk (Q : PqxdhPrims)
    (hQ : ∀ sk ct, (Q.decaps sk ct).toList = kyber1024Decaps sk.toList ct.toList)
    (stk : Nat) (hstk : 35968 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemSafeSubroutineOk kemDecapsName
      (fun mpl => withMlKemRoOk mpl (withVmPreserved (kemDecapsAtSpec stk Q))) externs :=
  specSimulates_mlkemSafeSubroutineOk
    (fun mpl => specSimulates_withMlKemRoOk_map mpl SpecSimulates.drop_keepsFs)
    (kemDecaps_at_keepsFs_vm_safeSubroutineOk Q hQ stk hstk hstk_fit externs)

/-- Hook #2 (`kemDecapsName`, `B23`): per-input `withPremise KemDecapsCallTerminates`
    total-correctness `keepsFs + withVmPreserved` bridge (`35968 ≤ stk`). -/
theorem kemDecaps_at_keepsFs_vm_premise_subroutineOk (Q : PqxdhPrims)
    (hQ : ∀ sk ct, (Q.decaps sk ct).toList = kyber1024Decaps sk.toList ct.toList)
    (stk : Nat) (hstk : 35968 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk kemDecapsName
      (fun mpl => withMlKemRoOk mpl
        (withPremise KemDecapsCallTerminates (keepsFs (withVmPreserved (kemDecapsAtSpec stk Q)))))
      externs := by
  have hsub0 : MlKemBlockOk 23 (fun mpl => withMlKemRoOk mpl
      (pullbackSpec (Subtype.val (p := KemDecapsCallTerminates))
        (keepsFs (kemDecapsAtSpec stk Q)))) :=
    blk23_cliProj_ok Q.decaps hQ stk hstk hstk_fit
      (C := { x : KemDecapsCall // KemDecapsCallTerminates x })
      (fun u => u.1.1) (fun u => u.1.2.1) (fun u => u.1.2.2.1)
      (fun u => u.1.2.2.2.1) (fun u => u.1.2.2.2.2) (fun u => u.2)
  have hblk : MlKemBlockOk 23 (fun mpl => withMlKemRoOk mpl
      (keepsFs (withPremise KemDecapsCallTerminates (kemDecapsAtSpec stk Q)))) :=
    specSimulates_mlkemBlockOk
      (fun mpl => specSimulates_withMlKemRoOk_map mpl
        (specSimulates_subtype_withPremise KemDecapsCallTerminates (keepsFs (kemDecapsAtSpec stk Q))))
      hsub0
  exact export_keepsFs_vm_subroutineOk hblk externs

/-- Hook #2 (`kemDecapsName`, `B23`): per-input `withPremise KemDecapsCallTerminates`
    total-correctness `withVmPreserved` bridge (`35968 ≤ stk`). -/
theorem kemDecaps_at_vm_premise_subroutineOk (Q : PqxdhPrims)
    (hQ : ∀ sk ct, (Q.decaps sk ct).toList = kyber1024Decaps sk.toList ct.toList)
    (stk : Nat) (hstk : 35968 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk kemDecapsName
      (fun mpl => withMlKemRoOk mpl
        (withPremise KemDecapsCallTerminates (withVmPreserved (kemDecapsAtSpec stk Q))))
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl => specSimulates_withMlKemRoOk_map mpl
      (SpecSimulates.drop_keepsFs (spec := withVmPreserved
        (withPremise KemDecapsCallTerminates (kemDecapsAtSpec stk Q)))))
    (kemDecaps_at_keepsFs_vm_premise_subroutineOk Q hQ stk hstk hstk_fit externs)

/-- Hook #2 (`kemDecapsName`, `B23`): per-input `withPremise KemDecapsCallTerminates`
    non-budget `subroutineOk` bridge (`35968 ≤ stk`). -/
theorem kemDecaps_at_premise_subroutineOk (Q : PqxdhPrims)
    (hQ : ∀ sk ct, (Q.decaps sk ct).toList = kyber1024Decaps sk.toList ct.toList)
    (stk : Nat) (hstk : 35968 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk kemDecapsName
      (fun mpl => withMlKemRoOk mpl
        (withPremise KemDecapsCallTerminates (kemDecapsAtSpec stk Q)))
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl => specSimulates_withMlKemRoOk_map mpl specSimulates_drop_withVmPreserved)
    (kemDecaps_at_vm_premise_subroutineOk Q hQ stk hstk hstk_fit externs)

/-- Hook #2 (`kemDecapsName`, `B23`): convenience `subroutineOk` corollary under
    `∀ x, KemDecapsCallTerminates x`. -/
theorem kemDecaps_at_vm_subroutineOk (Q : PqxdhPrims)
    (hQ : ∀ sk ct, (Q.decaps sk ct).toList = kyber1024Decaps sk.toList ct.toList)
    (stk : Nat) (hstk : 35968 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (hTerm : ∀ x, KemDecapsCallTerminates x)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk kemDecapsName
      (fun mpl => withMlKemRoOk mpl (withVmPreserved (kemDecapsAtSpec stk Q))) externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl => specSimulates_withMlKemRoOk_map mpl
      (specSimulates_withPremise_of_forall hTerm _))
    (kemDecaps_at_vm_premise_subroutineOk Q hQ stk hstk hstk_fit externs)

/-- Hook #2 (`kemDecapsName`, `B23`): `stk = 65536` `withVmPreserved` per-input bridge. -/
theorem kemDecaps_65536_vm_premise_subroutineOk (Q : PqxdhPrims)
    (hQ : ∀ sk ct, (Q.decaps sk ct).toList = kyber1024Decaps sk.toList ct.toList)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk kemDecapsName
      (fun mpl => withMlKemRoOk mpl
        (withPremise KemDecapsCallTerminates (withVmPreserved (kemDecapsAtSpec 65536 Q))))
      externs :=
  kemDecaps_at_vm_premise_subroutineOk Q hQ 65536 (by decide) (by decide) externs

/-- Hook #2 (`kemDecapsName`, `B23`): `extHookStack` (`35968 ≤ extHookStack`) `kemDecapsSpec Q`
    per-input `withVmPreserved` bridge. -/
theorem kemDecaps_vm_premise_subroutineOk (hstk : 35968 ≤ extHookStack) (Q : PqxdhPrims)
    (hQ : ∀ sk ct, (Q.decaps sk ct).toList = kyber1024Decaps sk.toList ct.toList)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk kemDecapsName
      (fun mpl => withMlKemRoOk mpl
        (withPremise KemDecapsCallTerminates (withVmPreserved (kemDecapsSpec Q))))
      externs :=
  kemDecaps_at_vm_premise_subroutineOk Q hQ extHookStack hstk (by decide) externs

/-! ## 5. Hook #3 (`mlkemFromSeedName`, `B10`, `33,664` B Tight Stack) -/

/-- Hook #3 (`mlkemFromSeedName`, `B10`): unconditional partial-correctness
    `keepsFs + withVmPreserved` bridge (`33664 ≤ stk`). -/
theorem mlkemFromSeed_at_keepsFs_vm_safeSubroutineOk (K : MlKem)
    (hK : ∀ s, (K.fromSeed s).2.2.toList = mlkem768KeyPairWith sampleNtt s.toList)
    (stk : Nat) (hstk : 33664 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemSafeSubroutineOk mlkemFromSeedName
      (fun mpl => withMlKemRoOk mpl (keepsFs (withVmPreserved (mlkemFromSeedAtSpec stk K))))
      externs :=
  export_keepsFs_vm_safeSubroutineOk
    (blk10_from_seed_proj_safe_ok stk hstk hstk_fit K hK
      MlkemFromSeedCall.seedA MlkemFromSeedCall.seed MlkemFromSeedCall.kpA)
    externs

/-- Hook #3 (`mlkemFromSeedName`, `B10`): unconditional partial-correctness `withVmPreserved`
    bridge (`33664 ≤ stk`). -/
theorem mlkemFromSeed_at_vm_safeSubroutineOk (K : MlKem)
    (hK : ∀ s, (K.fromSeed s).2.2.toList = mlkem768KeyPairWith sampleNtt s.toList)
    (stk : Nat) (hstk : 33664 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemSafeSubroutineOk mlkemFromSeedName
      (fun mpl => withMlKemRoOk mpl (withVmPreserved (mlkemFromSeedAtSpec stk K))) externs :=
  specSimulates_mlkemSafeSubroutineOk
    (fun mpl => specSimulates_withMlKemRoOk_map mpl SpecSimulates.drop_keepsFs)
    (mlkemFromSeed_at_keepsFs_vm_safeSubroutineOk K hK stk hstk hstk_fit externs)

/-- Hook #3 (`mlkemFromSeedName`, `B10`): per-input `withPremise MlkemFromSeedCallTerminates`
    total-correctness `keepsFs + withVmPreserved` bridge (`33664 ≤ stk`). -/
theorem mlkemFromSeed_at_keepsFs_vm_premise_subroutineOk (K : MlKem)
    (hK : ∀ s, (K.fromSeed s).2.2.toList = mlkem768KeyPairWith sampleNtt s.toList)
    (stk : Nat) (hstk : 33664 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk mlkemFromSeedName
      (fun mpl => withMlKemRoOk mpl
        (withPremise MlkemFromSeedCallTerminates
          (keepsFs (withVmPreserved (mlkemFromSeedAtSpec stk K)))))
      externs := by
  have hsub0 : MlKemBlockOk 10 (fun mpl => withMlKemRoOk mpl
      (pullbackSpec (Subtype.val (p := MlkemFromSeedCallTerminates))
        (keepsFs (mlkemFromSeedAtSpec stk K)))) :=
    blk10_from_seed_proj_ok stk hstk hstk_fit K hK
      (C := { x : MlkemFromSeedCall // MlkemFromSeedCallTerminates x })
      (fun u => u.1.seedA) (fun u => u.1.seed) (fun u => u.1.kpA) (fun u => u.2)
  have hblk : MlKemBlockOk 10 (fun mpl => withMlKemRoOk mpl
      (keepsFs (withPremise MlkemFromSeedCallTerminates (mlkemFromSeedAtSpec stk K)))) :=
    specSimulates_mlkemBlockOk
      (fun mpl => specSimulates_withMlKemRoOk_map mpl
        (specSimulates_subtype_withPremise MlkemFromSeedCallTerminates
          (keepsFs (mlkemFromSeedAtSpec stk K))))
      hsub0
  exact export_keepsFs_vm_subroutineOk hblk externs

/-- Hook #3 (`mlkemFromSeedName`, `B10`): per-input `withPremise MlkemFromSeedCallTerminates`
    total-correctness `withVmPreserved` bridge (`33664 ≤ stk`). -/
theorem mlkemFromSeed_at_vm_premise_subroutineOk (K : MlKem)
    (hK : ∀ s, (K.fromSeed s).2.2.toList = mlkem768KeyPairWith sampleNtt s.toList)
    (stk : Nat) (hstk : 33664 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk mlkemFromSeedName
      (fun mpl => withMlKemRoOk mpl
        (withPremise MlkemFromSeedCallTerminates (withVmPreserved (mlkemFromSeedAtSpec stk K))))
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl => specSimulates_withMlKemRoOk_map mpl
      (SpecSimulates.drop_keepsFs (spec := withVmPreserved
        (withPremise MlkemFromSeedCallTerminates (mlkemFromSeedAtSpec stk K)))))
    (mlkemFromSeed_at_keepsFs_vm_premise_subroutineOk K hK stk hstk hstk_fit externs)

/-- Hook #3 (`mlkemFromSeedName`, `B10`): per-input `withPremise MlkemFromSeedCallTerminates`
    non-budget `subroutineOk` bridge (`33664 ≤ stk`). -/
theorem mlkemFromSeed_at_premise_subroutineOk (K : MlKem)
    (hK : ∀ s, (K.fromSeed s).2.2.toList = mlkem768KeyPairWith sampleNtt s.toList)
    (stk : Nat) (hstk : 33664 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk mlkemFromSeedName
      (fun mpl => withMlKemRoOk mpl
        (withPremise MlkemFromSeedCallTerminates (mlkemFromSeedAtSpec stk K)))
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl => specSimulates_withMlKemRoOk_map mpl specSimulates_drop_withVmPreserved)
    (mlkemFromSeed_at_vm_premise_subroutineOk K hK stk hstk hstk_fit externs)

/-- Hook #3 (`mlkemFromSeedName`, `B10`): convenience `subroutineOk` corollary under
    `∀ x, MlkemFromSeedCallTerminates x`. -/
theorem mlkemFromSeed_at_vm_subroutineOk (K : MlKem)
    (hK : ∀ s, (K.fromSeed s).2.2.toList = mlkem768KeyPairWith sampleNtt s.toList)
    (stk : Nat) (hstk : 33664 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (hTerm : ∀ x, MlkemFromSeedCallTerminates x)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk mlkemFromSeedName
      (fun mpl => withMlKemRoOk mpl (withVmPreserved (mlkemFromSeedAtSpec stk K))) externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl => specSimulates_withMlKemRoOk_map mpl
      (specSimulates_withPremise_of_forall hTerm _))
    (mlkemFromSeed_at_vm_premise_subroutineOk K hK stk hstk hstk_fit externs)

/-- Hook #3 (`mlkemFromSeedName`, `B10`): `stk = 65536` `withVmPreserved` per-input bridge. -/
theorem mlkemFromSeed_65536_vm_premise_subroutineOk (K : MlKem)
    (hK : ∀ s, (K.fromSeed s).2.2.toList = mlkem768KeyPairWith sampleNtt s.toList)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk mlkemFromSeedName
      (fun mpl => withMlKemRoOk mpl
        (withPremise MlkemFromSeedCallTerminates (withVmPreserved (mlkemFromSeedAtSpec 65536 K))))
      externs :=
  mlkemFromSeed_at_vm_premise_subroutineOk K hK 65536 (by decide) (by decide) externs

/-- Hook #3 (`mlkemFromSeedName`, `B10`): `extHookStack` (`33664 ≤ extHookStack`)
    `mlkemFromSeedSpec K` per-input `withVmPreserved` bridge. -/
theorem mlkemFromSeed_vm_premise_subroutineOk (hstk : 33664 ≤ extHookStack) (K : MlKem)
    (hK : ∀ s, (K.fromSeed s).2.2.toList = mlkem768KeyPairWith sampleNtt s.toList)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk mlkemFromSeedName
      (fun mpl => withMlKemRoOk mpl
        (withPremise MlkemFromSeedCallTerminates (withVmPreserved (mlkemFromSeedSpec K))))
      externs :=
  mlkemFromSeed_at_vm_premise_subroutineOk K hK extHookStack hstk (by decide) externs

/-- Hook #3 (`mlkemFromSeedName`, `B10`): concrete `mlkem768Incremental` per-input bridge
    (`33664 ≤ stk`). -/
theorem mlkemFromSeed_inc_at_vm_premise_subroutineOk (stk : Nat) (hstk : 33664 ≤ stk)
    (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk mlkemFromSeedName
      (fun mpl => withMlKemRoOk mpl
        (withPremise MlkemFromSeedCallTerminates
          (withVmPreserved (mlkemFromSeedAtSpec stk mlkem768Incremental))))
      externs :=
  mlkemFromSeed_at_vm_premise_subroutineOk mlkem768Incremental
    mlkem768Incremental_fromSeed_dk_toList stk hstk hstk_fit externs

/-! ## 6. Hook #4 (`mlkemEncaps1Name`, `B19`, `18,304` B Tight Stack) -/

/-- Hook #4 (`mlkemEncaps1Name`, `B19`): unconditional partial-correctness
    `keepsFs + withVmPreserved` bridge (`18304 ≤ stk`). -/
theorem mlkemEncaps1_at_keepsFs_vm_safeSubroutineOk (K : MlKem)
    (hK : ∀ h r, K.encaps1 h r = mlkem768Incremental.encaps1 h r)
    (stk : Nat) (hstk : 18304 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemSafeSubroutineOk mlkemEncaps1Name
      (fun mpl => withMlKemRoOk mpl (keepsFs (withVmPreserved (mlkemEncaps1AtSpec stk K))))
      externs :=
  export_keepsFs_vm_safeSubroutineOk
    (blk19_encaps1_proj_safe_ok stk hstk hstk_fit K hK
      MlkemEncaps1Call.ret MlkemEncaps1Call.hdrA MlkemEncaps1Call.hdr
      MlkemEncaps1Call.randA MlkemEncaps1Call.rand MlkemEncaps1Call.esA MlkemEncaps1Call.ssA)
    externs

/-- Hook #4 (`mlkemEncaps1Name`, `B19`): unconditional partial-correctness `withVmPreserved`
    bridge (`18304 ≤ stk`). -/
theorem mlkemEncaps1_at_vm_safeSubroutineOk (K : MlKem)
    (hK : ∀ h r, K.encaps1 h r = mlkem768Incremental.encaps1 h r)
    (stk : Nat) (hstk : 18304 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemSafeSubroutineOk mlkemEncaps1Name
      (fun mpl => withMlKemRoOk mpl (withVmPreserved (mlkemEncaps1AtSpec stk K))) externs :=
  specSimulates_mlkemSafeSubroutineOk
    (fun mpl => specSimulates_withMlKemRoOk_map mpl SpecSimulates.drop_keepsFs)
    (mlkemEncaps1_at_keepsFs_vm_safeSubroutineOk K hK stk hstk hstk_fit externs)

/-- Hook #4 (`mlkemEncaps1Name`, `B19`): per-input `withPremise MlkemEncaps1CallTerminates`
    total-correctness `keepsFs + withVmPreserved` bridge (`18304 ≤ stk`). -/
theorem mlkemEncaps1_at_keepsFs_vm_premise_subroutineOk (K : MlKem)
    (hK : ∀ h r, K.encaps1 h r = mlkem768Incremental.encaps1 h r)
    (stk : Nat) (hstk : 18304 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk mlkemEncaps1Name
      (fun mpl => withMlKemRoOk mpl
        (withPremise MlkemEncaps1CallTerminates
          (keepsFs (withVmPreserved (mlkemEncaps1AtSpec stk K)))))
      externs := by
  have hsub0 : MlKemBlockOk 19 (fun mpl => withMlKemRoOk mpl
      (pullbackSpec (Subtype.val (p := MlkemEncaps1CallTerminates))
        (keepsFs (mlkemEncaps1AtSpec stk K)))) :=
    blk19_encaps1_proj_ok stk hstk hstk_fit K hK
      (C := { x : MlkemEncaps1Call // MlkemEncaps1CallTerminates x })
      (fun u => u.1.ret) (fun u => u.1.hdrA) (fun u => u.1.hdr)
      (fun u => u.1.randA) (fun u => u.1.rand) (fun u => u.1.esA) (fun u => u.1.ssA)
      (fun u => u.2)
  have hblk : MlKemBlockOk 19 (fun mpl => withMlKemRoOk mpl
      (keepsFs (withPremise MlkemEncaps1CallTerminates (mlkemEncaps1AtSpec stk K)))) :=
    specSimulates_mlkemBlockOk
      (fun mpl => specSimulates_withMlKemRoOk_map mpl
        (specSimulates_subtype_withPremise MlkemEncaps1CallTerminates
          (keepsFs (mlkemEncaps1AtSpec stk K))))
      hsub0
  exact export_keepsFs_vm_subroutineOk hblk externs

/-- Hook #4 (`mlkemEncaps1Name`, `B19`): per-input `withPremise MlkemEncaps1CallTerminates`
    total-correctness `withVmPreserved` bridge (`18304 ≤ stk`). -/
theorem mlkemEncaps1_at_vm_premise_subroutineOk (K : MlKem)
    (hK : ∀ h r, K.encaps1 h r = mlkem768Incremental.encaps1 h r)
    (stk : Nat) (hstk : 18304 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk mlkemEncaps1Name
      (fun mpl => withMlKemRoOk mpl
        (withPremise MlkemEncaps1CallTerminates (withVmPreserved (mlkemEncaps1AtSpec stk K))))
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl => specSimulates_withMlKemRoOk_map mpl
      (SpecSimulates.drop_keepsFs (spec := withVmPreserved
        (withPremise MlkemEncaps1CallTerminates (mlkemEncaps1AtSpec stk K)))))
    (mlkemEncaps1_at_keepsFs_vm_premise_subroutineOk K hK stk hstk hstk_fit externs)

/-- Hook #4 (`mlkemEncaps1Name`, `B19`): per-input `withPremise MlkemEncaps1CallTerminates`
    non-budget `subroutineOk` bridge (`18304 ≤ stk`). -/
theorem mlkemEncaps1_at_premise_subroutineOk (K : MlKem)
    (hK : ∀ h r, K.encaps1 h r = mlkem768Incremental.encaps1 h r)
    (stk : Nat) (hstk : 18304 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk mlkemEncaps1Name
      (fun mpl => withMlKemRoOk mpl
        (withPremise MlkemEncaps1CallTerminates (mlkemEncaps1AtSpec stk K)))
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl => specSimulates_withMlKemRoOk_map mpl specSimulates_drop_withVmPreserved)
    (mlkemEncaps1_at_vm_premise_subroutineOk K hK stk hstk hstk_fit externs)

/-- Hook #4 (`mlkemEncaps1Name`, `B19`): convenience `subroutineOk` corollary under
    `∀ x, MlkemEncaps1CallTerminates x`. -/
theorem mlkemEncaps1_at_vm_subroutineOk (K : MlKem)
    (hK : ∀ h r, K.encaps1 h r = mlkem768Incremental.encaps1 h r)
    (stk : Nat) (hstk : 18304 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (hTerm : ∀ x, MlkemEncaps1CallTerminates x)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk mlkemEncaps1Name
      (fun mpl => withMlKemRoOk mpl (withVmPreserved (mlkemEncaps1AtSpec stk K))) externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl => specSimulates_withMlKemRoOk_map mpl
      (specSimulates_withPremise_of_forall hTerm _))
    (mlkemEncaps1_at_vm_premise_subroutineOk K hK stk hstk hstk_fit externs)

/-- Hook #4 (`mlkemEncaps1Name`, `B19`): `stk = 65536` `withVmPreserved` per-input bridge. -/
theorem mlkemEncaps1_65536_vm_premise_subroutineOk (K : MlKem)
    (hK : ∀ h r, K.encaps1 h r = mlkem768Incremental.encaps1 h r)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk mlkemEncaps1Name
      (fun mpl => withMlKemRoOk mpl
        (withPremise MlkemEncaps1CallTerminates (withVmPreserved (mlkemEncaps1AtSpec 65536 K))))
      externs :=
  mlkemEncaps1_at_vm_premise_subroutineOk K hK 65536 (by decide) (by decide) externs

/-- Hook #4 (`mlkemEncaps1Name`, `B19`): `extHookStack` (`18304 ≤ extHookStack`)
    `mlkemEncaps1Spec K` per-input `withVmPreserved` bridge. -/
theorem mlkemEncaps1_vm_premise_subroutineOk (hstk : 18304 ≤ extHookStack) (K : MlKem)
    (hK : ∀ h r, K.encaps1 h r = mlkem768Incremental.encaps1 h r)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk mlkemEncaps1Name
      (fun mpl => withMlKemRoOk mpl
        (withPremise MlkemEncaps1CallTerminates (withVmPreserved (mlkemEncaps1Spec K))))
      externs :=
  mlkemEncaps1_at_vm_premise_subroutineOk K hK extHookStack hstk (by decide) externs

/-- Hook #4 (`mlkemEncaps1Name`, `B19`): concrete `mlkem768Incremental` per-input bridge
    (`18304 ≤ stk`). -/
theorem mlkemEncaps1_inc_at_vm_premise_subroutineOk (stk : Nat) (hstk : 18304 ≤ stk)
    (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk mlkemEncaps1Name
      (fun mpl => withMlKemRoOk mpl
        (withPremise MlkemEncaps1CallTerminates
          (withVmPreserved (mlkemEncaps1AtSpec stk mlkem768Incremental))))
      externs :=
  mlkemEncaps1_at_vm_premise_subroutineOk mlkem768Incremental (fun _ _ => rfl) stk hstk hstk_fit
    externs

/-! ## 7. Hook #6 (`mlkemDecapsName`, `B22`, `26,960` B Tight Stack) -/

/-- Hook #6 (`mlkemDecapsName`, `B22`): unconditional partial-correctness
    `keepsFs + withVmPreserved` bridge (`26960 ≤ stk`). -/
theorem mlkemDecaps_at_keepsFs_vm_safeSubroutineOk (K : MlKem)
    (hK : ∀ d c1 c2, K.decaps d c1 c2 =
      toByteVec 32 (mlkem768DecapsWith sampleNtt d.toList c1.toList c2.toList))
    (stk : Nat) (hstk : 26960 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemSafeSubroutineOk mlkemDecapsName
      (fun mpl => withMlKemRoOk mpl (keepsFs (withVmPreserved (mlkemDecapsAtSpec stk K))))
      externs :=
  export_keepsFs_vm_safeSubroutineOk
    (blk22_decaps_proj_safe_ok stk hstk hstk_fit K hK
      MlkemDecapsCall.ret MlkemDecapsCall.dkA MlkemDecapsCall.dk
      MlkemDecapsCall.ct1A MlkemDecapsCall.ct1 MlkemDecapsCall.ct2A MlkemDecapsCall.ct2)
    externs

/-- Hook #6 (`mlkemDecapsName`, `B22`): unconditional partial-correctness `withVmPreserved`
    bridge (`26960 ≤ stk`). -/
theorem mlkemDecaps_at_vm_safeSubroutineOk (K : MlKem)
    (hK : ∀ d c1 c2, K.decaps d c1 c2 =
      toByteVec 32 (mlkem768DecapsWith sampleNtt d.toList c1.toList c2.toList))
    (stk : Nat) (hstk : 26960 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemSafeSubroutineOk mlkemDecapsName
      (fun mpl => withMlKemRoOk mpl (withVmPreserved (mlkemDecapsAtSpec stk K))) externs :=
  specSimulates_mlkemSafeSubroutineOk
    (fun mpl => specSimulates_withMlKemRoOk_map mpl SpecSimulates.drop_keepsFs)
    (mlkemDecaps_at_keepsFs_vm_safeSubroutineOk K hK stk hstk hstk_fit externs)

/-- Hook #6 (`mlkemDecapsName`, `B22`): per-input `withPremise MlkemDecapsCallTerminates`
    total-correctness `keepsFs + withVmPreserved` bridge (`26960 ≤ stk`). -/
theorem mlkemDecaps_at_keepsFs_vm_premise_subroutineOk (K : MlKem)
    (hK : ∀ d c1 c2, K.decaps d c1 c2 =
      toByteVec 32 (mlkem768DecapsWith sampleNtt d.toList c1.toList c2.toList))
    (stk : Nat) (hstk : 26960 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk mlkemDecapsName
      (fun mpl => withMlKemRoOk mpl
        (withPremise MlkemDecapsCallTerminates
          (keepsFs (withVmPreserved (mlkemDecapsAtSpec stk K)))))
      externs := by
  have hsub0 : MlKemBlockOk 22 (fun mpl => withMlKemRoOk mpl
      (pullbackSpec (Subtype.val (p := MlkemDecapsCallTerminates))
        (keepsFs (mlkemDecapsAtSpec stk K)))) :=
    blk22_decaps_proj_ok stk hstk hstk_fit K hK
      (C := { x : MlkemDecapsCall // MlkemDecapsCallTerminates x })
      (fun u => u.1.ret) (fun u => u.1.dkA) (fun u => u.1.dk)
      (fun u => u.1.ct1A) (fun u => u.1.ct1) (fun u => u.1.ct2A) (fun u => u.1.ct2)
      (fun u => u.2)
  have hblk : MlKemBlockOk 22 (fun mpl => withMlKemRoOk mpl
      (keepsFs (withPremise MlkemDecapsCallTerminates (mlkemDecapsAtSpec stk K)))) :=
    specSimulates_mlkemBlockOk
      (fun mpl => specSimulates_withMlKemRoOk_map mpl
        (specSimulates_subtype_withPremise MlkemDecapsCallTerminates
          (keepsFs (mlkemDecapsAtSpec stk K))))
      hsub0
  exact export_keepsFs_vm_subroutineOk hblk externs

/-- Hook #6 (`mlkemDecapsName`, `B22`): per-input `withPremise MlkemDecapsCallTerminates`
    total-correctness `withVmPreserved` bridge (`26960 ≤ stk`). -/
theorem mlkemDecaps_at_vm_premise_subroutineOk (K : MlKem)
    (hK : ∀ d c1 c2, K.decaps d c1 c2 =
      toByteVec 32 (mlkem768DecapsWith sampleNtt d.toList c1.toList c2.toList))
    (stk : Nat) (hstk : 26960 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk mlkemDecapsName
      (fun mpl => withMlKemRoOk mpl
        (withPremise MlkemDecapsCallTerminates (withVmPreserved (mlkemDecapsAtSpec stk K))))
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl => specSimulates_withMlKemRoOk_map mpl
      (SpecSimulates.drop_keepsFs (spec := withVmPreserved
        (withPremise MlkemDecapsCallTerminates (mlkemDecapsAtSpec stk K)))))
    (mlkemDecaps_at_keepsFs_vm_premise_subroutineOk K hK stk hstk hstk_fit externs)

/-- Hook #6 (`mlkemDecapsName`, `B22`): per-input `withPremise MlkemDecapsCallTerminates`
    non-budget `subroutineOk` bridge (`26960 ≤ stk`). -/
theorem mlkemDecaps_at_premise_subroutineOk (K : MlKem)
    (hK : ∀ d c1 c2, K.decaps d c1 c2 =
      toByteVec 32 (mlkem768DecapsWith sampleNtt d.toList c1.toList c2.toList))
    (stk : Nat) (hstk : 26960 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk mlkemDecapsName
      (fun mpl => withMlKemRoOk mpl
        (withPremise MlkemDecapsCallTerminates (mlkemDecapsAtSpec stk K)))
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl => specSimulates_withMlKemRoOk_map mpl specSimulates_drop_withVmPreserved)
    (mlkemDecaps_at_vm_premise_subroutineOk K hK stk hstk hstk_fit externs)

/-- Hook #6 (`mlkemDecapsName`, `B22`): convenience `subroutineOk` corollary under
    `∀ x, MlkemDecapsCallTerminates x`. -/
theorem mlkemDecaps_at_vm_subroutineOk (K : MlKem)
    (hK : ∀ d c1 c2, K.decaps d c1 c2 =
      toByteVec 32 (mlkem768DecapsWith sampleNtt d.toList c1.toList c2.toList))
    (stk : Nat) (hstk : 26960 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (hTerm : ∀ x, MlkemDecapsCallTerminates x)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk mlkemDecapsName
      (fun mpl => withMlKemRoOk mpl (withVmPreserved (mlkemDecapsAtSpec stk K))) externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl => specSimulates_withMlKemRoOk_map mpl
      (specSimulates_withPremise_of_forall hTerm _))
    (mlkemDecaps_at_vm_premise_subroutineOk K hK stk hstk hstk_fit externs)

/-- Hook #6 (`mlkemDecapsName`, `B22`): `stk = 65536` `withVmPreserved` per-input bridge. -/
theorem mlkemDecaps_65536_vm_premise_subroutineOk (K : MlKem)
    (hK : ∀ d c1 c2, K.decaps d c1 c2 =
      toByteVec 32 (mlkem768DecapsWith sampleNtt d.toList c1.toList c2.toList))
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk mlkemDecapsName
      (fun mpl => withMlKemRoOk mpl
        (withPremise MlkemDecapsCallTerminates (withVmPreserved (mlkemDecapsAtSpec 65536 K))))
      externs :=
  mlkemDecaps_at_vm_premise_subroutineOk K hK 65536 (by decide) (by decide) externs

/-- Hook #6 (`mlkemDecapsName`, `B22`): `extHookStack` (`26960 ≤ extHookStack`)
    `mlkemDecapsSpec K` per-input `withVmPreserved` bridge. -/
theorem mlkemDecaps_vm_premise_subroutineOk (hstk : 26960 ≤ extHookStack) (K : MlKem)
    (hK : ∀ d c1 c2, K.decaps d c1 c2 =
      toByteVec 32 (mlkem768DecapsWith sampleNtt d.toList c1.toList c2.toList))
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk mlkemDecapsName
      (fun mpl => withMlKemRoOk mpl
        (withPremise MlkemDecapsCallTerminates (withVmPreserved (mlkemDecapsSpec K))))
      externs :=
  mlkemDecaps_at_vm_premise_subroutineOk K hK extHookStack hstk (by decide) externs

/-- Hook #6 (`mlkemDecapsName`, `B22`): concrete `mlkem768Incremental` per-input bridge
    (`26960 ≤ stk`). -/
theorem mlkemDecaps_inc_at_vm_premise_subroutineOk (stk : Nat) (hstk : 26960 ≤ stk)
    (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk mlkemDecapsName
      (fun mpl => withMlKemRoOk mpl
        (withPremise MlkemDecapsCallTerminates
          (withVmPreserved (mlkemDecapsAtSpec stk mlkem768Incremental))))
      externs :=
  mlkemDecaps_at_vm_premise_subroutineOk mlkem768Incremental (fun _ _ _ => rfl) stk hstk hstk_fit
    externs

/-! ## 8. Unconditional Hooks #5 (`mlkemEncaps2Name`, `B20`) & #7 (`mlkemValidatePkName`, `B21`) -/

/-- Hook #5 (`mlkemEncaps2Name`, `B20`): unconditional `mlkemSafeSubroutineOk` (`6128 ≤ stk`). -/
theorem mlkemEncaps2_at_keepsFs_vm_safeSubroutineOk (K : MlKem)
    (hK : ∀ es ek, K.encaps2 es ek = toByteVec 128 (mlkem768Encaps2List es.toList ek.toList))
    (stk : Nat) (hstk : 6128 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemSafeSubroutineOk mlkemEncaps2Name
      (fun mpl => withMlKemRoOk mpl (keepsFs (withVmPreserved (mlkemEncaps2AtSpec stk K))))
      externs :=
  mlkemSafeSubroutineOk_of_subroutineOk
    (mlkemEncaps2_at_keepsFs_vm_subroutineOk K hK stk hstk hstk_fit externs)

/-- Hook #7 (`mlkemValidatePkName`, `B21`): unconditional `mlkemSafeSubroutineOk` (`5824 ≤ stk`). -/
theorem mlkemValidatePk_at_keepsFs_vm_safeSubroutineOk (K : MlKem)
    (hK : ∀ hdr ek, K.validPk hdr ek = mlkem768ValidPk hdr ek)
    (stk : Nat) (hstk : 5824 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemSafeSubroutineOk mlkemValidatePkName
      (fun mpl => withMlKemRoOk mpl (keepsFs (withVmPreserved (mlkemValidatePkAtSpec stk K))))
      externs :=
  mlkemSafeSubroutineOk_of_subroutineOk
    (mlkemValidatePk_at_keepsFs_vm_subroutineOk K hK stk hstk hstk_fit externs)

/-! ## 9. Load-Time `MlKemRoHoldsBytes` + `KeepsFrozen` Bridges for All 7 Hooks -/

/-- Hook #1 (`kemEncapsName`, `B24`): `withKeepsFrozen m₀` `mlkemSafeSubroutineOk` bridge. -/
theorem kemEncaps_at_keepsFs_vm_safeSubroutineOk_of_holdsBytes_keepsFrozen (Q : PqxdhPrims)
    (hQ : ∀ pk rand,
      (Q.encaps pk rand).1.toList = (kyber1024Encaps pk.toList rand.toList).1 ∧
      (Q.encaps pk rand).2.toList = (kyber1024Encaps pk.toList rand.toList).2)
    (stk : Nat) (hstk : 34240 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    {m₀ : Memory} (hro : ∀ mpl, mlkemMultiLib.Placeable mpl → MlKemRoHoldsBytes mpl m₀)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemSafeSubroutineOk kemEncapsName
      (fun _mpl => withKeepsFrozen m₀ (keepsFs (withVmPreserved (kemEncapsAtSpec stk Q))))
      externs :=
  safeSubroutineOk_of_holdsBytes_keepsFrozen hro
    (kemEncaps_at_keepsFs_vm_safeSubroutineOk Q hQ stk hstk hstk_fit externs)

/-- Hook #1 (`kemEncapsName`, `B24`): `withKeepsFrozen m₀` per-input `subroutineOk` bridge. -/
theorem kemEncaps_at_keepsFs_vm_premise_subroutineOk_of_holdsBytes_keepsFrozen (Q : PqxdhPrims)
    (hQ : ∀ pk rand,
      (Q.encaps pk rand).1.toList = (kyber1024Encaps pk.toList rand.toList).1 ∧
      (Q.encaps pk rand).2.toList = (kyber1024Encaps pk.toList rand.toList).2)
    (stk : Nat) (hstk : 34240 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    {m₀ : Memory} (hro : ∀ mpl, mlkemMultiLib.Placeable mpl → MlKemRoHoldsBytes mpl m₀)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk kemEncapsName
      (fun _mpl => withKeepsFrozen m₀
        (withPremise KemEncapsCallTerminates (keepsFs (withVmPreserved (kemEncapsAtSpec stk Q)))))
      externs :=
  subroutineOk_of_holdsBytes_keepsFrozen hro
    (kemEncaps_at_keepsFs_vm_premise_subroutineOk Q hQ stk hstk hstk_fit externs)

/-- Hook #1 (`kemEncapsName`, `B24`): stronger `kemEncapsPreservedAtSpec` `withKeepsFrozen m₀`
    per-input `subroutineOk` bridge. -/
theorem kemEncapsPreserved_at_keepsFs_vm_premise_subroutineOk_of_holdsBytes_keepsFrozen
    (Q : PqxdhPrims)
    (hQ : ∀ pk rand,
      (Q.encaps pk rand).1.toList = (kyber1024Encaps pk.toList rand.toList).1 ∧
      (Q.encaps pk rand).2.toList = (kyber1024Encaps pk.toList rand.toList).2)
    (stk : Nat) (hstk : 34240 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    {m₀ : Memory} (hro : ∀ mpl, mlkemMultiLib.Placeable mpl → MlKemRoHoldsBytes mpl m₀)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk kemEncapsName
      (fun _mpl => withKeepsFrozen m₀
        (withPremise KemEncapsCallTerminates
          (keepsFs (withVmPreserved (kemEncapsPreservedAtSpec stk Q)))))
      externs :=
  subroutineOk_of_holdsBytes_keepsFrozen hro
    (kemEncapsPreserved_at_keepsFs_vm_premise_subroutineOk Q hQ stk hstk hstk_fit externs)

/-- Hook #2 (`kemDecapsName`, `B23`): `withKeepsFrozen m₀` `mlkemSafeSubroutineOk` bridge. -/
theorem kemDecaps_at_keepsFs_vm_safeSubroutineOk_of_holdsBytes_keepsFrozen (Q : PqxdhPrims)
    (hQ : ∀ sk ct, (Q.decaps sk ct).toList = kyber1024Decaps sk.toList ct.toList)
    (stk : Nat) (hstk : 35968 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    {m₀ : Memory} (hro : ∀ mpl, mlkemMultiLib.Placeable mpl → MlKemRoHoldsBytes mpl m₀)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemSafeSubroutineOk kemDecapsName
      (fun _mpl => withKeepsFrozen m₀ (keepsFs (withVmPreserved (kemDecapsAtSpec stk Q))))
      externs :=
  safeSubroutineOk_of_holdsBytes_keepsFrozen hro
    (kemDecaps_at_keepsFs_vm_safeSubroutineOk Q hQ stk hstk hstk_fit externs)

/-- Hook #2 (`kemDecapsName`, `B23`): `withKeepsFrozen m₀` per-input `subroutineOk` bridge. -/
theorem kemDecaps_at_keepsFs_vm_premise_subroutineOk_of_holdsBytes_keepsFrozen (Q : PqxdhPrims)
    (hQ : ∀ sk ct, (Q.decaps sk ct).toList = kyber1024Decaps sk.toList ct.toList)
    (stk : Nat) (hstk : 35968 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    {m₀ : Memory} (hro : ∀ mpl, mlkemMultiLib.Placeable mpl → MlKemRoHoldsBytes mpl m₀)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk kemDecapsName
      (fun _mpl => withKeepsFrozen m₀
        (withPremise KemDecapsCallTerminates (keepsFs (withVmPreserved (kemDecapsAtSpec stk Q)))))
      externs :=
  subroutineOk_of_holdsBytes_keepsFrozen hro
    (kemDecaps_at_keepsFs_vm_premise_subroutineOk Q hQ stk hstk hstk_fit externs)

/-- Hook #3 (`mlkemFromSeedName`, `B10`): `withKeepsFrozen m₀` `mlkemSafeSubroutineOk` bridge. -/
theorem mlkemFromSeed_at_keepsFs_vm_safeSubroutineOk_of_holdsBytes_keepsFrozen (K : MlKem)
    (hK : ∀ s, (K.fromSeed s).2.2.toList = mlkem768KeyPairWith sampleNtt s.toList)
    (stk : Nat) (hstk : 33664 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    {m₀ : Memory} (hro : ∀ mpl, mlkemMultiLib.Placeable mpl → MlKemRoHoldsBytes mpl m₀)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemSafeSubroutineOk mlkemFromSeedName
      (fun _mpl => withKeepsFrozen m₀ (keepsFs (withVmPreserved (mlkemFromSeedAtSpec stk K))))
      externs :=
  safeSubroutineOk_of_holdsBytes_keepsFrozen hro
    (mlkemFromSeed_at_keepsFs_vm_safeSubroutineOk K hK stk hstk hstk_fit externs)

/-- Hook #3 (`mlkemFromSeedName`, `B10`): `withKeepsFrozen m₀` per-input `subroutineOk` bridge. -/
theorem mlkemFromSeed_at_keepsFs_vm_premise_subroutineOk_of_holdsBytes_keepsFrozen (K : MlKem)
    (hK : ∀ s, (K.fromSeed s).2.2.toList = mlkem768KeyPairWith sampleNtt s.toList)
    (stk : Nat) (hstk : 33664 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    {m₀ : Memory} (hro : ∀ mpl, mlkemMultiLib.Placeable mpl → MlKemRoHoldsBytes mpl m₀)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk mlkemFromSeedName
      (fun _mpl => withKeepsFrozen m₀
        (withPremise MlkemFromSeedCallTerminates
          (keepsFs (withVmPreserved (mlkemFromSeedAtSpec stk K)))))
      externs :=
  subroutineOk_of_holdsBytes_keepsFrozen hro
    (mlkemFromSeed_at_keepsFs_vm_premise_subroutineOk K hK stk hstk hstk_fit externs)

/-- Hook #4 (`mlkemEncaps1Name`, `B19`): `withKeepsFrozen m₀` `mlkemSafeSubroutineOk` bridge. -/
theorem mlkemEncaps1_at_keepsFs_vm_safeSubroutineOk_of_holdsBytes_keepsFrozen (K : MlKem)
    (hK : ∀ h r, K.encaps1 h r = mlkem768Incremental.encaps1 h r)
    (stk : Nat) (hstk : 18304 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    {m₀ : Memory} (hro : ∀ mpl, mlkemMultiLib.Placeable mpl → MlKemRoHoldsBytes mpl m₀)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemSafeSubroutineOk mlkemEncaps1Name
      (fun _mpl => withKeepsFrozen m₀ (keepsFs (withVmPreserved (mlkemEncaps1AtSpec stk K))))
      externs :=
  safeSubroutineOk_of_holdsBytes_keepsFrozen hro
    (mlkemEncaps1_at_keepsFs_vm_safeSubroutineOk K hK stk hstk hstk_fit externs)

/-- Hook #4 (`mlkemEncaps1Name`, `B19`): `withKeepsFrozen m₀` per-input `subroutineOk` bridge. -/
theorem mlkemEncaps1_at_keepsFs_vm_premise_subroutineOk_of_holdsBytes_keepsFrozen (K : MlKem)
    (hK : ∀ h r, K.encaps1 h r = mlkem768Incremental.encaps1 h r)
    (stk : Nat) (hstk : 18304 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    {m₀ : Memory} (hro : ∀ mpl, mlkemMultiLib.Placeable mpl → MlKemRoHoldsBytes mpl m₀)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk mlkemEncaps1Name
      (fun _mpl => withKeepsFrozen m₀
        (withPremise MlkemEncaps1CallTerminates
          (keepsFs (withVmPreserved (mlkemEncaps1AtSpec stk K)))))
      externs :=
  subroutineOk_of_holdsBytes_keepsFrozen hro
    (mlkemEncaps1_at_keepsFs_vm_premise_subroutineOk K hK stk hstk hstk_fit externs)

/-- Hook #5 (`mlkemEncaps2Name`, `B20`): unconditional `withKeepsFrozen m₀` `subroutineOk` bridge. -/
theorem mlkemEncaps2_at_keepsFs_vm_subroutineOk_of_holdsBytes_keepsFrozen (K : MlKem)
    (hK : ∀ es ek, K.encaps2 es ek = toByteVec 128 (mlkem768Encaps2List es.toList ek.toList))
    (stk : Nat) (hstk : 6128 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    {m₀ : Memory} (hro : ∀ mpl, mlkemMultiLib.Placeable mpl → MlKemRoHoldsBytes mpl m₀)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk mlkemEncaps2Name
      (fun _mpl => withKeepsFrozen m₀ (keepsFs (withVmPreserved (mlkemEncaps2AtSpec stk K))))
      externs :=
  subroutineOk_of_holdsBytes_keepsFrozen hro
    (mlkemEncaps2_at_keepsFs_vm_subroutineOk K hK stk hstk hstk_fit externs)

/-- Hook #5 (`mlkemEncaps2Name`, `B20`): unconditional `withKeepsFrozen m₀`
    `mlkemSafeSubroutineOk` bridge. -/
theorem mlkemEncaps2_at_keepsFs_vm_safeSubroutineOk_of_holdsBytes_keepsFrozen (K : MlKem)
    (hK : ∀ es ek, K.encaps2 es ek = toByteVec 128 (mlkem768Encaps2List es.toList ek.toList))
    (stk : Nat) (hstk : 6128 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    {m₀ : Memory} (hro : ∀ mpl, mlkemMultiLib.Placeable mpl → MlKemRoHoldsBytes mpl m₀)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemSafeSubroutineOk mlkemEncaps2Name
      (fun _mpl => withKeepsFrozen m₀ (keepsFs (withVmPreserved (mlkemEncaps2AtSpec stk K))))
      externs :=
  mlkemSafeSubroutineOk_of_subroutineOk
    (mlkemEncaps2_at_keepsFs_vm_subroutineOk_of_holdsBytes_keepsFrozen K hK stk hstk hstk_fit
      hro externs)

/-- Hook #6 (`mlkemDecapsName`, `B22`): `withKeepsFrozen m₀` `mlkemSafeSubroutineOk` bridge. -/
theorem mlkemDecaps_at_keepsFs_vm_safeSubroutineOk_of_holdsBytes_keepsFrozen (K : MlKem)
    (hK : ∀ d c1 c2, K.decaps d c1 c2 =
      toByteVec 32 (mlkem768DecapsWith sampleNtt d.toList c1.toList c2.toList))
    (stk : Nat) (hstk : 26960 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    {m₀ : Memory} (hro : ∀ mpl, mlkemMultiLib.Placeable mpl → MlKemRoHoldsBytes mpl m₀)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemSafeSubroutineOk mlkemDecapsName
      (fun _mpl => withKeepsFrozen m₀ (keepsFs (withVmPreserved (mlkemDecapsAtSpec stk K))))
      externs :=
  safeSubroutineOk_of_holdsBytes_keepsFrozen hro
    (mlkemDecaps_at_keepsFs_vm_safeSubroutineOk K hK stk hstk hstk_fit externs)

/-- Hook #6 (`mlkemDecapsName`, `B22`): `withKeepsFrozen m₀` per-input `subroutineOk` bridge. -/
theorem mlkemDecaps_at_keepsFs_vm_premise_subroutineOk_of_holdsBytes_keepsFrozen (K : MlKem)
    (hK : ∀ d c1 c2, K.decaps d c1 c2 =
      toByteVec 32 (mlkem768DecapsWith sampleNtt d.toList c1.toList c2.toList))
    (stk : Nat) (hstk : 26960 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    {m₀ : Memory} (hro : ∀ mpl, mlkemMultiLib.Placeable mpl → MlKemRoHoldsBytes mpl m₀)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk mlkemDecapsName
      (fun _mpl => withKeepsFrozen m₀
        (withPremise MlkemDecapsCallTerminates
          (keepsFs (withVmPreserved (mlkemDecapsAtSpec stk K)))))
      externs :=
  subroutineOk_of_holdsBytes_keepsFrozen hro
    (mlkemDecaps_at_keepsFs_vm_premise_subroutineOk K hK stk hstk hstk_fit externs)

/-- Hook #7 (`mlkemValidatePkName`, `B21`): unconditional `withKeepsFrozen m₀` `subroutineOk`
    bridge. -/
theorem mlkemValidatePk_at_keepsFs_vm_subroutineOk_of_holdsBytes_keepsFrozen (K : MlKem)
    (hK : ∀ hdr ek, K.validPk hdr ek = mlkem768ValidPk hdr ek)
    (stk : Nat) (hstk : 5824 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    {m₀ : Memory} (hro : ∀ mpl, mlkemMultiLib.Placeable mpl → MlKemRoHoldsBytes mpl m₀)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk mlkemValidatePkName
      (fun _mpl => withKeepsFrozen m₀ (keepsFs (withVmPreserved (mlkemValidatePkAtSpec stk K))))
      externs :=
  subroutineOk_of_holdsBytes_keepsFrozen hro
    (mlkemValidatePk_at_keepsFs_vm_subroutineOk K hK stk hstk hstk_fit externs)

/-- Hook #7 (`mlkemValidatePkName`, `B21`): unconditional `withKeepsFrozen m₀`
    `mlkemSafeSubroutineOk` bridge. -/
theorem mlkemValidatePk_at_keepsFs_vm_safeSubroutineOk_of_holdsBytes_keepsFrozen (K : MlKem)
    (hK : ∀ hdr ek, K.validPk hdr ek = mlkem768ValidPk hdr ek)
    (stk : Nat) (hstk : 5824 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    {m₀ : Memory} (hro : ∀ mpl, mlkemMultiLib.Placeable mpl → MlKemRoHoldsBytes mpl m₀)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemSafeSubroutineOk mlkemValidatePkName
      (fun _mpl => withKeepsFrozen m₀ (keepsFs (withVmPreserved (mlkemValidatePkAtSpec stk K))))
      externs :=
  mlkemSafeSubroutineOk_of_subroutineOk
    (mlkemValidatePk_at_keepsFs_vm_subroutineOk_of_holdsBytes_keepsFrozen K hK stk hstk hstk_fit
      hro externs)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.ConsumerBridges
