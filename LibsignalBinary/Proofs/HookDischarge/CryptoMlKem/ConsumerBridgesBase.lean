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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
import ProofLib.Hoare.Model
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.OpcodeSafety
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLiftBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk
public meta import ProofLib.ProgramReflection -- proof-setup: allow-public-import

/-!
# Shared `VmPreserved` Lifting, Partial-Correctness Exports, and Consumer Specs (`ConsumerBridgesBase`)

1. `withMlKemRoOk`, `mlkemSafeSubroutineOk` (`safe_subroutine_ok` counterpart of
   `mlkemMultiLib.subroutineOk`), `externs`-generalized export combinators, `SpecSimulates`
   transport rules, and `MlKemRoOk` load-time discharge helpers.
2. Generic `withVmPreserved` lifting (`mlkemBlockOk_withVmPreserved`,
   `mlkemBlockSafeOk_withVmPreserved`, and `withMlKemRoOk` specializations) proved via
   `OpcodeSafety.mlkemMultiLib_blocks_all_svc0` and `mlkemMultiLib_blocks_all_msr`.
3. Stack-parameterized (`stk : Nat`) consumer `Spec` definitions `rfl`-equal to `SpqrHooks` and
   `CliExt` contracts at `stk = extHookStack`.
4. Unconditional consumer bridges (`mlkemMultiLib.subroutineOk` and `mlkemSafeSubroutineOk`,
   with `withVmPreserved` and `keepsFs`) for Hooks #5 (`mlkemEncaps2Name`, `B20`) and #7
   (`mlkemValidatePkName`, `B21`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.ConsumerBridgesBase

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
open LibsignalBinary.Heap (FdsHiFrame PoolPreserved VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs withStack)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (RoDataAt SpecSimulates)
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
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBlockOk
  MlKemBlockSafeOk
  MlKemPlacement
  mlkemMpl
  safe_reaches_of_sameHooks
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (withNonSyscallPreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.OpcodeSafety (
  mlkemMultiLib_blocks_all_externs_empty
  mlkemMultiLib_blocks_all_msr
  mlkemMultiLib_blocks_all_svc0
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLiftBase (
  mlkemRoOk_stripExecOutside
  stripS_mem
  stripS_pc
  stripS_readReg64
  stripS_sp
  stripS_spAligned
  stripS_status
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  mlkem768Encaps2List
  mlkem768Incremental
  mlkem768ValidPk
  toByteVec
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2 (blk20_encaps2_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (mlkemEncaps2CoreSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk (
  blk21_validate_pk_validPk_ok
  mlkemValidatePkValidCoreSpec
  mlkemValidatePkValidRawSpec
  validPkBytes_eq_mlkem768ValidPk
)

/-- `mlkem1024::kyber::encapsulate(pk = x0, randomness = x1) -> (ct, ss)` (sret `x8`). -/
abbrev kemEncapsName : String := "libcrux_ml_kem::mlkem1024::kyber::encapsulate"

/-- `mlkem1024::kyber::decapsulate(sk = x0, ct = x1) -> ss` (sret `x8`). -/
abbrev kemDecapsName : String := "libcrux_ml_kem::mlkem1024::kyber::decapsulate"

/-! ## 1. `withMlKemRoOk`, `mlkemSafeSubroutineOk`, & `SpecSimulates` Combinators -/

/-- Adjoin `⌜MlKemRoOk mpl s0.mem⌝` to `spec.pre`. -/
@[expose] def withMlKemRoOk {α : Type} (mpl : MultiPlacement) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s0 => ⌜MlKemRoOk mpl s0.mem⌝ ∗ spec.pre x s0 }

/-- Layout-generic partial-correctness (`safe_subroutine_ok`) contract for an exported function
    `fnName` of `mlkemMultiLib`, matching `mlkemMultiLib.subroutineOk` point-for-point with
    `safe_subroutine_ok` in place of `subroutine_ok`. -/
@[expose] def mlkemSafeSubroutineOk {S α : Type} [ToBaseSpec S α]
    (fnName : String) (spec : MultiPlacement → S)
    (externs : String → Option (State → State) := fun _ => none)
    (overrides : String → Option (State → State) := fun _ => none) : Prop :=
  fnName ∈ mlkemMultiLib.exports ∧
    ∃ i off, lookupBlockSym fnName mlkemMultiLib.blocks = some (i, off) ∧
      ∀ mpl : MultiPlacement, mlkemMultiLib.Placeable mpl →
        safe_subroutine_ok (mlkemMultiLib.blockProgram mpl i externs overrides)
          (mlkemMultiLib.fnAddr mpl fnName)
          (mlkemMultiLib.withCodeLoaded mpl (ToBaseSpec.toSpec (spec mpl) (mpl.base i)))

/-- Every `mlkemMultiLib.subroutineOk` theorem weakens unconditionally to `mlkemSafeSubroutineOk`. -/
theorem mlkemSafeSubroutineOk_of_subroutineOk {S α : Type} [ToBaseSpec S α]
    {fnName : String} {spec : MultiPlacement → S}
    {externs overrides : String → Option (State → State)}
    (h : mlkemMultiLib.subroutineOk fnName spec externs overrides) :
    mlkemSafeSubroutineOk fnName spec externs overrides := by
  obtain ⟨hexp, i, off, hsym, hsub⟩ := h
  exact ⟨hexp, i, off, hsym, fun mpl hpl => (hsub mpl hpl).to_safe⟩

/-- Because every block of `mlkemMultiLib` has `b.externs = []`, its placed program has no external
    stub hooks under any external hook table `externs`. -/
theorem externAt?_mlkemBlockProgram_ext_none (mpl : MultiPlacement) {j : Nat}
    (hj : j < mlkemMultiLib.blocks.length)
    (externs : String → Option (State → State)) (pc : BitVec 64) :
    (mlkemMultiLib.blockProgram mpl j externs).externAt? pc = none := by
  have hext : (mlkemMultiLib.blockLib j).text.externs = [] := by
    rw [mlkemMultiLib.blockLib_text hj]
    exact mlkemMultiLib_blocks_all_externs_empty mlkemMultiLib.blocks[j] (List.getElem_mem hj)
  have hfs : ∀ l : List (String × Nat),
      l.findSome? (fun (_ : String × Nat) => (none : Option (State → State))) = none := by
    intro l
    induction l with
    | nil => rfl
    | cons _ _ ih => exact ih
  dsimp only [MultiPlacedLib.blockProgram, PlacedLib.program, Program.externAt?, Program.hookAtOff?]
  rw [hext]
  simp only [ite_self, List.map_nil, List.findSome?_nil]
  exact hfs _

/-- Export a `MlKemBlockOk j spec` proof to `mlkemMultiLib.subroutineOk sym spec externs` for any
    external hook table `externs`. -/
theorem mlkemSubroutineOk_of_blockOk_ext {j : Nat} {sym : String}
    {α S : Type} [ToBaseSpec S α] {spec : MultiPlacement → S}
    (hok : MlKemBlockOk j spec)
    (externs : String → Option (State → State) := fun _ => none)
    (hj : j < mlkemMultiLib.blocks.length := by decide)
    (hexp : sym ∈ mlkemMultiLib.exports := by decide)
    (hsym : lookupBlockSym sym mlkemMultiLib.blocks = some (j, 0) := by rfl_kernel) :
    mlkemMultiLib.subroutineOk sym spec externs := by
  refine ⟨hexp, j, 0, hsym, fun mpl hpl => ?_⟩
  have hfn : mlkemMultiLib.fnAddr mpl sym = mpl.base j := by
    simp [MultiPlacedLib.fnAddr, hsym]
  rw [hfn]
  exact mlkemMultiLib.subroutine_ok_of_block hj (@hok ⟨mpl, hpl⟩)
    (externAt?_mlkemBlockProgram_ext_none mpl hj externs) rfl

/-- Export a `MlKemBlockSafeOk j spec` proof to `mlkemSafeSubroutineOk sym spec externs` for any
    external hook table `externs`. -/
theorem mlkemSafeSubroutineOk_of_blockSafeOk_ext {j : Nat} {sym : String}
    {α S : Type} [ToBaseSpec S α] {spec : MultiPlacement → S}
    (hok : MlKemBlockSafeOk j spec)
    (externs : String → Option (State → State) := fun _ => none)
    (hj : j < mlkemMultiLib.blocks.length := by decide)
    (hexp : sym ∈ mlkemMultiLib.exports := by decide)
    (hsym : lookupBlockSym sym mlkemMultiLib.blocks = some (j, 0) := by rfl_kernel) :
    mlkemSafeSubroutineOk sym spec externs := by
  refine ⟨hexp, j, 0, hsym, fun mpl hpl => ?_⟩
  have hfn : mlkemMultiLib.fnAddr mpl sym = mpl.base j := by
    simp [MultiPlacedLib.fnAddr, hsym]
  rw [hfn]
  exact PlacedCodeBase.safe_subroutine_ok_of_block hj (@hok ⟨mpl, hpl⟩)
    (externAt?_mlkemBlockProgram_ext_none mpl hj externs) rfl

/-- Transport `safe_subroutine_ok` along `SpecSimulates`. -/
theorem specSimulates_safe_subroutine_ok {α β : Type} {spec₁ : Spec α} {spec₂ : Spec β}
    (hsim : SpecSimulates spec₁ spec₂) {prog : Program} {entry : BitVec 64}
    (h : safe_subroutine_ok prog entry spec₁) :
    safe_subroutine_ok prog entry spec₂ := by
  intro y R s0 hentry hpre
  obtain ⟨x, R₁, hpre₁, hm⟩ := hsim y R s0 hpre
  exact (h x R₁ s0 hentry hpre₁).mono hm

/-- Transport `mlkemSafeSubroutineOk` along a placement-indexed `SpecSimulates` family. -/
theorem specSimulates_mlkemSafeSubroutineOk {α β : Type}
    {fnName : String} {spec₁ : MultiPlacement → Spec α} {spec₂ : MultiPlacement → Spec β}
    {externs overrides : String → Option (State → State)}
    (hsim : ∀ mpl, SpecSimulates (spec₁ mpl) (spec₂ mpl))
    (h : mlkemSafeSubroutineOk fnName spec₁ externs overrides) :
    mlkemSafeSubroutineOk fnName spec₂ externs overrides := by
  obtain ⟨hexp, i, off, hfn, hsub⟩ := h
  exact ⟨hexp, i, off, hfn, fun mpl hpl =>
    specSimulates_safe_subroutine_ok ((hsim mpl).withCodeLoaded mlkemMultiLib mpl) (hsub mpl hpl)⟩

/-- Transport `MlKemBlockOk` along `SpecSimulates`. -/
theorem specSimulates_mlkemBlockOk {j : Nat} {α β : Type}
    {spec₁ : MultiPlacement → Spec α} {spec₂ : MultiPlacement → Spec β}
    (hsim : ∀ mpl, SpecSimulates (spec₁ mpl) (spec₂ mpl))
    (hok : MlKemBlockOk j spec₁) : MlKemBlockOk j spec₂ :=
  fun [MlKemPlacement] => ((hsim mlkemMpl).withCodeLoaded mlkemMultiLib mlkemMpl).subroutine_ok hok

/-- Transport `MlKemBlockSafeOk` along `SpecSimulates`. -/
theorem specSimulates_mlkemBlockSafeOk {j : Nat} {α β : Type}
    {spec₁ : MultiPlacement → Spec α} {spec₂ : MultiPlacement → Spec β}
    (hsim : ∀ mpl, SpecSimulates (spec₁ mpl) (spec₂ mpl))
    (hok : MlKemBlockSafeOk j spec₁) : MlKemBlockSafeOk j spec₂ :=
  fun [MlKemPlacement] =>
    specSimulates_safe_subroutine_ok
      ((hsim mlkemMpl).withCodeLoaded mlkemMultiLib mlkemMpl) hok

theorem keepsFs_withMlKemRoOk {α : Type} (mpl : MultiPlacement) (spec : Spec α) :
    keepsFs (withMlKemRoOk mpl spec) = withMlKemRoOk mpl (keepsFs spec) := rfl

theorem withVmPreserved_withMlKemRoOk {α : Type} (mpl : MultiPlacement) (spec : Spec α) :
    withVmPreserved (withMlKemRoOk mpl spec) = withMlKemRoOk mpl (withVmPreserved spec) := rfl

theorem specSimulates_withMlKemRoOk_map {α β : Type} (mpl : MultiPlacement)
    {spec₁ : Spec α} {spec₂ : Spec β} (hsim : SpecSimulates spec₁ spec₂) :
    SpecSimulates (withMlKemRoOk mpl spec₁) (withMlKemRoOk mpl spec₂) := by
  intro y R s0 hpre
  dsimp only [withMlKemRoOk] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hro, hpre₂⟩ := hpre
  obtain ⟨x, R₁, hpre₁, hm⟩ := hsim y R s0 hpre₂
  refine ⟨x, R₁, ?_, hm⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hro, hpre₁⟩

theorem specSimulates_lift_withVmPreserved {α β : Type} {spec₁ : Spec α} {spec₂ : Spec β}
    (hsim : SpecSimulates spec₁ spec₂)
    (hpan₁ : spec₁.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hex₁ : spec₁.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom₁ : spec₁.onOom = fun _ _ _ => ⌜False⌝ := by rfl)
    (hpan₂ : spec₂.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hex₂ : spec₂.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom₂ : spec₂.onOom = fun _ _ _ => ⌜False⌝ := by rfl) :
    SpecSimulates (withVmPreserved spec₁) (withVmPreserved spec₂) := by
  intro y R s0 hpre
  obtain ⟨x, R₁, hpre₁, hm⟩ := hsim y R s0 hpre
  refine ⟨x, R₁, hpre₁, fun sf hout => ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · dsimp only [withVmPreserved] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨hvm, hpost₁⟩ := hpost
    rcases hm sf (Or.inl ⟨hret, hcc, hpost₁⟩) with ⟨_, _, hpost₂⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withVmPreserved]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hvm, hpost₂⟩
    · rw [hpan₂] at hp; exact False.elim (not_satisfies_false_sepConj hp)
    · rw [hex₂] at he; exact False.elim (not_satisfies_false_sepConj he)
    · rw [hoom₂] at ho; exact False.elim (not_satisfies_false_sepConj ho)
  · dsimp only [withVmPreserved] at hp
    rw [hpan₁] at hp; exact False.elim (not_satisfies_false_sepConj hp)
  · dsimp only [withVmPreserved] at he
    rw [hex₁] at he; exact False.elim (not_satisfies_false_sepConj he)
  · dsimp only [withVmPreserved] at ho
    rw [hoom₁] at ho; exact False.elim (not_satisfies_false_sepConj ho)

theorem specSimulates_keepsFs_withVmPreserved {α : Type} {spec : Spec α} :
    SpecSimulates (withVmPreserved (keepsFs spec)) (keepsFs (withVmPreserved spec)) := by
  intro x R s0 hpre
  refine ⟨x, R, hpre, fun sf hout => ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hout_abn
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withVmPreserved, keepsFs] at hpost ⊢
    rw [sepConj_left_comm ⌜VmPreserved s0 sf⌝ ⌜sf.fs = s0.fs⌝] at hpost
    exact hpost
  · exact Or.inr hout_abn

theorem specSimulates_drop_withVmPreserved {α : Type} {spec : Spec α} :
    SpecSimulates (withVmPreserved spec) spec := by
  intro x R s0 hpre
  refine ⟨x, R, hpre, fun sf hout => ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hout_abn
  · dsimp only [withVmPreserved] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact Or.inl ⟨hret, hcc, hpost.2⟩
  · exact Or.inr hout_abn

/-- Discharge `MlKemRoOk mpl m` from load-time `Obj.HoldsBytes` of all 11 `.rodata` tables in `m₀`
    together with `m₀.KeepsFrozen m`. -/
theorem mlkemRoOk_of_holdsBytes_keepsFrozen {mpl : MultiPlacement} {m₀ m : Memory}
    (h00 : HoldsBytes m₀ (mpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0") mlkemData00Bytes (fun _ => Perm.ro))
    (h01 : HoldsBytes m₀ (mpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29") mlkemData01Bytes (fun _ => Perm.ro))
    (h02 : HoldsBytes m₀ (mpl.ρ "libcrux_ml_kem:.rodata.cst16.0") mlkemData02Bytes (fun _ => Perm.ro))
    (h03 : HoldsBytes m₀ (mpl.ρ "libcrux_ml_kem:.rodata.cst16.1") mlkemData03Bytes (fun _ => Perm.ro))
    (h04 : HoldsBytes m₀ (mpl.ρ "libcrux_ml_kem:.rodata.cst16.2") mlkemData04Bytes (fun _ => Perm.ro))
    (h05 : HoldsBytes m₀ (mpl.ρ "libcrux_ml_kem:.rodata.cst16.3") mlkemData05Bytes (fun _ => Perm.ro))
    (h06 : HoldsBytes m₀ (mpl.ρ "libcrux_ml_kem:.rodata.cst16.4") mlkemData06Bytes (fun _ => Perm.ro))
    (h07 : HoldsBytes m₀ (mpl.ρ "libcrux_ml_kem:.rodata.cst16.5") mlkemData07Bytes (fun _ => Perm.ro))
    (h08 : HoldsBytes m₀ (mpl.ρ "libcrux_ml_kem:.rodata.cst16.6") mlkemData08Bytes (fun _ => Perm.ro))
    (h09 : HoldsBytes m₀ (mpl.ρ "libcrux_ml_kem:.rodata.cst16.7") mlkemData09Bytes (fun _ => Perm.ro))
    (h10 : HoldsBytes m₀ (mpl.ρ "libcrux_ml_kem:.rodata.cst16.8") mlkemData10Bytes (fun _ => Perm.ro))
    (hkf : m₀.KeepsFrozen m) : MlKemRoOk mpl m :=
  let mk {addr bytes} (h : HoldsBytes m₀ addr bytes (fun _ => Perm.ro)) : RoDataAt m addr bytes :=
    ProofLib.ObjectLoad.holdsBytes_ro (ProofLib.ObjectLoad.holdsBytes_ro_of_keepsFrozen h hkf)
  ⟨mk h00, mk h01, mk h02, mk h03, mk h04, mk h05, mk h06, mk h07, mk h08, mk h09, mk h10⟩

/-! ## 2. Generic `withVmPreserved` Lifting (`MlKemBlockOk` & `MlKemBlockSafeOk`) -/

private theorem vmPreserved_of_nonSyscall_tpidr {s0 sf : State}
    (hnsp : ProofLib.NonSyscallPreserved s0 sf) (htp : sf.tpidrEl0 = s0.tpidrEl0) :
    VmPreserved s0 sf := by
  have hpool : PoolPreserved s0 sf := ⟨hnsp.2.2.2.1, hnsp.2.2.1, htp⟩
  have hfds : FdsHiFrame s0 sf := fun _ _ _ => by rw [hnsp.2.2.2.2.2.2]
  exact ⟨hpool, hnsp.2.2.2.2.1, fun a => congrFun hnsp.2.1 a, hfds⟩

private def mlkemKeepV (mpl : MultiPlacement) (a : BitVec 64) : Bool :=
  (List.range mlkemMultiLib.blocks.length).any fun k =>
    progKeep (mlkemMultiLib.blockProgram mpl k) a

private theorem strip_codeLoaded_mlkemV {mpl : MultiPlacement} {m : Memory}
    (hcl : mlkemMultiLib.CodeLoaded mpl m) :
    mlkemMultiLib.CodeLoaded mpl (stripExecOutside (mlkemKeepV mpl) m) := by
  intro k hk
  have hL := hcl k hk
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
  let Pk := mlkemMultiLib.blockProgram mpl k
  have hno := hL.no_wrap
  have hsub : Pk.base + BitVec.ofNat 64 i - Pk.base = BitVec.ofNat 64 i := by bv_omega
  have hin : (Pk.base + BitVec.ofNat 64 i - Pk.base).toNat < Pk.code.length := by
    rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hi
  have hkp : progKeep Pk (Pk.base + BitVec.ofNat 64 i) = true := decide_eq_true hin
  have hmk : mlkemKeepV mpl (Pk.base + BitVec.ofNat 64 i) = true := by
    unfold mlkemKeepV
    rw [List.any_eq_true]
    exact ⟨k, List.mem_range.mpr hk, hkp⟩
  rw [strip_read8, strip_perm_of_keep hmk, strip_isLazyFree]
  exact ⟨hL.byte_eq i hi, hL.perm_eq i hi, hL.isLazyFree_eq i hi⟩

private theorem externAt?_mlkemBlockProgram_none (mpl : MultiPlacement) (j : Nat)
    (pc : BitVec 64) :
    (mlkemMultiLib.blockProgram mpl j).externAt? pc = none := by
  have h0 : ∀ L : List (String × Nat),
      L.findSome? (fun (_ : String × Nat) => (none : Option (State → State))) = none := by
    intro L
    induction L with
    | nil => rfl
    | cons _ _ ih => exact ih
  dsimp only [MultiPlacedLib.blockProgram, PlacedLib.program,
    Program.externAt?, Program.hookAtOff?]
  simp only [ite_self, h0]
  rfl

private theorem fetch_in_mlkem_not_svc0_msr {mpl : MultiPlacement}
    (hpl : mlkemMultiLib.Placeable mpl)
    {m0 m : Memory} (hcl0 : mlkemMultiLib.CodeLoaded mpl m0) (hkf : m0.KeepsFrozen m)
    {pc : BitVec 64} {inst : Instr}
    (hk : mlkemKeepV mpl pc = true)
    (hfm : Program.pureMem.fetchMem m pc = some inst) :
    inst.isSvc0 = false ∧ inst.isMsrTpidrEl0 = false := by
  unfold mlkemKeepV at hk
  rw [List.any_eq_true] at hk
  obtain ⟨k, hk_mem, hkp⟩ := hk
  have hk_lt : k < mlkemMultiLib.blocks.length := List.mem_range.mp hk_mem
  have hcl_m : (mlkemMultiLib.blockProgram mpl k).CodeLoaded m :=
    (hcl0 k hk_lt).of_keepsFrozen hkf
  have hal_pc : pc.toNat % 4 = 0 := by
    unfold Program.fetchMem at hfm
    by_cases h4 : pc.toNat % 4 = 0
    · exact h4
    · simp [h4] at hfm
  let Pk := mlkemMultiLib.blockProgram mpl k
  have hPk_al : Pk.base.toNat % 4 = 0 := hcl_m.aligned
  have hPk_nw : Pk.base.toNat + Pk.code.length ≤ 2 ^ 64 := hcl_m.no_wrap
  have hin : (pc - Pk.base).toNat < Pk.code.length := of_decide_eq_true hkp
  have hPk_len4 : Pk.code.length % 4 = 0 := by
    have hbt := (hpl.blocks_ok k hk_lt).len_aligned
    have hplen : ((mlkemMultiLib.blockLib k).text.patched
        (mlkemMultiLib.blockPlacement mpl k)).length =
        (mlkemMultiLib.blockLib k).text.code.length :=
      CodeBlock.length_patched_of_aligned _
        (by rw [mlkemMultiLib.blockLib_text hk_lt]; exact hbt)
    change ((mlkemMultiLib.blockLib k).text.patched
      (mlkemMultiLib.blockPlacement mpl k)).length % 4 = 0
    rw [hplen, mlkemMultiLib.blockLib_text hk_lt]
    exact hbt
  let off := (pc - Pk.base).toNat
  have hpc_eq : pc = Pk.base + BitVec.ofNat 64 off := by dsimp [off]; bv_omega
  have hoff_lt : off < Pk.code.length := hin
  have hoff4 : off % 4 = 0 := by
    have hoff_nat : off = pc.toNat - Pk.base.toNat := by
      change (pc - Pk.base).toNat < Pk.code.length at hin
      dsimp [off]; bv_omega
    omega
  have hoff_end : off + 4 ≤ Pk.code.length := by omega
  have hoff_end' : off + 4 ≤ (mlkemMultiLib.blockProgram mpl k).code.length := hoff_end
  have hrw : Pk.readWordOff off = some (m.read32 pc) := by
    have hb0 := hcl_m.byte_eq off (by omega)
    have hb1 := hcl_m.byte_eq (off + 1) (by omega)
    have hb2 := hcl_m.byte_eq (off + 2) (by omega)
    have hb3 := hcl_m.byte_eq (off + 3) (by omega)
    have ha0 : pc + 0#64 = Pk.base + BitVec.ofNat 64 off := by rw [hpc_eq]; bv_omega
    have ha1 : pc + 1#64 = Pk.base + BitVec.ofNat 64 (off + 1) := by rw [hpc_eq]; bv_omega
    have ha2 : pc + 2#64 = Pk.base + BitVec.ofNat 64 (off + 2) := by rw [hpc_eq]; bv_omega
    have ha3 : pc + 3#64 = Pk.base + BitVec.ofNat 64 (off + 3) := by rw [hpc_eq]; bv_omega
    unfold Program.readWordOff
    simp only [hoff4, ne_eq, not_true_eq_false, ↓reduceIte]
    have hd0 : Pk.code.drop off =
        Pk.code[off]'(by omega) :: Pk.code[off + 1]'(by omega) ::
        Pk.code[off + 2]'(by omega) :: Pk.code[off + 3]'(by omega) :: Pk.code.drop (off + 4) := by
      rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega),
        List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega)]
    rw [hd0]
    dsimp only [Memory.read32]
    rw [ha0, hb0, ha1, hb1, ha2, hb2, ha3, hb3]
  have hdec : decode (m.read32 pc) = some inst := by
    unfold Program.fetchMem at hfm
    split at hfm
    · simp at hfm
    · split at hfm
      · simp at hfm
      · split at hfm
        · simp at hfm
        · exact hfm
  have hfetch_Pk : Pk.fetch (Pk.base + BitVec.ofNat 64 off) = some inst := by
    have hf := Program.fetch_of_readWordOff (prog := Pk) (off := off) (by omega)
      (by simp [Pk, MultiPlacedLib.blockProgram, PlacedLib.program, Program.hookAtOff?]) hrw
    rwa [hdec] at hf
  have hps_svc : (mlkemMultiLib.blockLib k).text.patchSafe svc0Pat = true := by
    rw [mlkemMultiLib.blockLib_text hk_lt]
    exact (List.all_eq_true.mp mlkemMultiLib_blocks_all_svc0)
      mlkemMultiLib.blocks[k] (List.getElem_mem hk_lt)
  have hps_msr : (mlkemMultiLib.blockLib k).text.patchSafe msrTpidrEl0Pat = true := by
    rw [mlkemMultiLib.blockLib_text hk_lt]
    exact (List.all_eq_true.mp mlkemMultiLib_blocks_all_msr)
      mlkemMultiLib.blocks[k] (List.getElem_mem hk_lt)
  have hall_svc := PlacedLib.program_noSvc0_of_patchSafe hps_svc
    (mlkemMultiLib.blockPlacement mpl k)
  have hall_msr := PlacedLib.program_noMsrTpidrEl0_of_patchSafe hps_msr
    (mlkemMultiLib.blockPlacement mpl k)
  exact ⟨by simpa using Program.fetch_of_allInstrs hall_svc _ _ hfetch_Pk,
    by simpa using Program.fetch_of_allInstrs hall_msr _ _ hfetch_Pk⟩

private theorem step_lift_stripS_mlkemV {mpl : MultiPlacement} {j : Nat}
    (hpl : mlkemMultiLib.Placeable mpl)
    {m0 : Memory} (hcl0 : mlkemMultiLib.CodeLoaded mpl m0)
    {s s2' : State} (hkf : m0.KeepsFrozen s.mem)
    (hstep : Step (mlkemMultiLib.blockProgram mpl j) (stripS (mlkemKeepV mpl) s) s2')
    (hnot_halt : s2'.status ≠ .Halted) :
    ∃ inst : Instr,
      (mlkemMultiLib.blockProgram mpl j).fetchMem s.mem s.pc = some inst ∧
      inst.isSvc0 = false ∧
      Step (mlkemMultiLib.blockProgram mpl j) s (execInst inst s) ∧
      s2' = stripS (mlkemKeepV mpl) (execInst inst s) ∧
      ProofLib.NonSyscallPreserved s (execInst inst s) ∧
      (execInst inst s).tpidrEl0 = s.tpidrEl0 ∧
      m0.KeepsFrozen (execInst inst s).mem := by
  let P := mlkemMultiLib.blockProgram mpl j
  cases hstep with
  | halt_unmapped _ _ _ => exact False.elim (hnot_halt rfl)
  | extern _ h_ext _ _ =>
    rw [externAt?_mlkemBlockProgram_none] at h_ext
    cases h_ext
  | extern_fault _ h_ext _ =>
    rw [externAt?_mlkemBlockProgram_none] at h_ext
    cases h_ext
  | exec hrun' hfetch' =>
    rename_i inst
    have hrun : s.status = .Running := by simpa using hrun'
    rw [stripS_pc, stripS_mem] at hfetch'
    unfold Program.fetchMem at hfetch'
    rw [externAt?_mlkemBlockProgram_none] at hfetch'
    by_cases hce' : (stripExecOutside (mlkemKeepV mpl) s.mem).canExec s.pc 4 = true
    · have hr32 : (stripExecOutside (mlkemKeepV mpl) s.mem).read32 s.pc = s.mem.read32 s.pc := by
        simp [Memory.read32, strip_read8]
      have hx4 :
          ((stripExecOutside (mlkemKeepV mpl) s.mem).perm s.pc).x = true ∧
          ((stripExecOutside (mlkemKeepV mpl) s.mem).perm (s.pc + 1#64)).x = true ∧
          ((stripExecOutside (mlkemKeepV mpl) s.mem).perm (s.pc + 2#64)).x = true ∧
          ((stripExecOutside (mlkemKeepV mpl) s.mem).perm (s.pc + 3#64)).x = true := by
        simpa [Memory.canExec, Memory.allPerm, Bool.and_eq_true, BitVec.add_assoc] using hce'
      obtain ⟨hx0, hk0⟩ := strip_perm_x_imp hx4.1
      obtain ⟨hx1, _⟩ := strip_perm_x_imp hx4.2.1
      obtain ⟨hx2, _⟩ := strip_perm_x_imp hx4.2.2.1
      obtain ⟨hx3, _⟩ := strip_perm_x_imp hx4.2.2.2
      have hce : s.mem.canExec s.pc 4 = true := by
        simp [Memory.canExec, Memory.allPerm, BitVec.add_assoc, hx0, hx1, hx2, hx3]
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hce', Bool.not_true, hr32]
        at hfetch'
      have hfetch_pm : Program.pureMem.fetchMem s.mem s.pc = some inst := by
        unfold Program.fetchMem
        have hpure_ext : Program.pureMem.externAt? s.pc = none := rfl
        simp only [hpure_ext, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hce, Bool.not_true]
        exact hfetch'
      have hfetch_P : P.fetchMem s.mem s.pc = some inst := by
        unfold Program.fetchMem
        rw [externAt?_mlkemBlockProgram_none]
        simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hce, Bool.not_true]
        exact hfetch'
      obtain ⟨hns, hmsr⟩ := fetch_in_mlkem_not_svc0_msr hpl hcl0 hkf hk0 hfetch_pm
      have heval_P : P.evalInst inst s = execInst inst s :=
        evalInst_eq_execInst_of_not_isSvc0 hns s
      have heval_P' :
          P.evalInst inst (stripS (mlkemKeepV mpl) s) =
            execInst inst (stripS (mlkemKeepV mpl) s) :=
        evalInst_eq_execInst_of_not_isSvc0 hns (stripS (mlkemKeepV mpl) s)
      have hstep_s : Step P s (execInst inst s) :=
        heval_P ▸ Step.exec hrun hfetch_P
      refine ⟨inst, hfetch_P, hns, hstep_s, ?_,
        ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hns s,
        execInst_tpidrEl0_of_not_isMsrTpidrEl0 hmsr s,
        hkf.trans hstep_s.keepsFrozen⟩
      rw [heval_P', execInst_stripS hns (mlkemKeepV mpl) s]
    · simp [hce'] at hfetch'

private theorem steps_lift_stripS_mlkemV {mpl : MultiPlacement} {j : Nat}
    (hpl : mlkemMultiLib.Placeable mpl)
    {m0 : Memory} (hcl0 : mlkemMultiLib.CodeLoaded mpl m0) :
    ∀ {s0 s' sf' : State},
      s' = stripS (mlkemKeepV mpl) s0 →
      m0.KeepsFrozen s0.mem →
      Steps (mlkemMultiLib.blockProgram mpl j) s' sf' →
      sf'.status ≠ .Halted →
      ∃ sf : State,
        sf' = stripS (mlkemKeepV mpl) sf ∧
        Steps (mlkemMultiLib.blockProgram mpl j) s0 sf ∧
        ProofLib.NonSyscallPreserved s0 sf ∧
        sf.tpidrEl0 = s0.tpidrEl0 := by
  intro s0 s' sf' hs' hkf hsteps hnh
  induction hsteps generalizing s0 with
  | refl _ =>
    subst hs'
    exact ⟨s0, rfl, Steps.refl s0, ProofLib.NonSyscallPreserved.refl s0, rfl⟩
  | @step s1' s2' sf' hstep hrest ih =>
    subst hs'
    have hnh2 : s2'.status ≠ .Halted := by
      cases hrest with
      | refl _ => exact hnh
      | step hs _ => rw [hs.status_running]; decide
    obtain ⟨_, _, _, hstep_s, hs2_eq, hnsp1, htp1, hkf2⟩ :=
      step_lift_stripS_mlkemV hpl hcl0 hkf hstep hnh2
    obtain ⟨sf, hsf_eq, hsteps_rest, hnsp_rest, htp_rest⟩ := ih hs2_eq hkf2 hnh
    exact ⟨sf, hsf_eq, Steps.step hstep_s hsteps_rest, hnsp1.trans hnsp_rest, htp_rest.trans htp1⟩

private theorem steps_diverge_stripS_mlkemV {mpl : MultiPlacement} {j : Nat}
    (hpl : mlkemMultiLib.Placeable mpl)
    {m0 : Memory} (hcl0 : mlkemMultiLib.CodeLoaded mpl m0) :
    ∀ {s u : State},
      Steps (mlkemMultiLib.blockProgram mpl j) s u →
      m0.KeepsFrozen s.mem →
      (∀ u', Steps (mlkemMultiLib.blockProgram mpl j) (stripS (mlkemKeepV mpl) s) u' →
        u'.status = .Running ∧ ∃ v', Step (mlkemMultiLib.blockProgram mpl j) u' v') →
      u.status = .Running ∧ ∃ v, Step (mlkemMultiLib.blockProgram mpl j) u v := by
  intro s u hsteps
  induction hsteps with
  | refl s =>
    intro hkf hall'
    obtain ⟨hrun', v', hv'⟩ := hall' _ (Steps.refl _)
    have hrun_v' : v'.status = .Running := (hall' v' (Steps.step hv' (Steps.refl _))).1
    obtain ⟨inst, _, _, hstep_s, _, _, _, _⟩ :=
      step_lift_stripS_mlkemV hpl hcl0 hkf hv' (by rw [hrun_v']; decide)
    exact ⟨by simpa using hrun', execInst inst s, hstep_s⟩
  | @step s s1 u hstep0 hrest ih =>
    intro hkf hall'
    obtain ⟨_, v', hv'⟩ := hall' _ (Steps.refl _)
    have hrun_v' : v'.status = .Running := (hall' v' (Steps.step hv' (Steps.refl _))).1
    obtain ⟨inst, hfetch_P, hns, _, hv'_eq, _, _, hkf1⟩ :=
      step_lift_stripS_mlkemV hpl hcl0 hkf hv' (by rw [hrun_v']; decide)
    have hs1_eq : s1 = execInst inst s := by
      cases hstep0 with
      | halt_unmapped _ hfn _ => rw [hfetch_P] at hfn; cases hfn
      | extern _ hex _ _ => rw [externAt?_mlkemBlockProgram_none] at hex; cases hex
      | extern_fault _ hex _ => rw [externAt?_mlkemBlockProgram_none] at hex; cases hex
      | exec _ hfm =>
        rw [hfetch_P] at hfm
        injection hfm with hinst
        subst hinst
        exact evalInst_eq_execInst_of_not_isSvc0 hns s
    subst hs1_eq
    exact ih hkf1 fun u' hu' => hall' u' (Steps.step (hv'_eq ▸ hv') hu')

/-- Lift any `MlKemBlockOk j (fun mpl => withMlKemRoOk mpl spec)` (`j < 32`, memory-field-independent
    `spec` with `False` abnormal exits) to `withMlKemRoOk mpl (withVmPreserved spec)`. -/
theorem mlkemBlockOk_withMlKemRoOk_withVmPreserved {j : Nat} {α : Type}
    {spec : Spec α}
    (hok : MlKemBlockOk j (fun mpl => withMlKemRoOk mpl spec))
    (hj : j < mlkemMultiLib.blocks.length := by decide)
    (hpan : spec.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hex : spec.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom : spec.onOom = fun _ _ _ => ⌜False⌝ := by rfl)
    (h_pre_mem : ∀ x (s : State) (m : Memory),
      spec.pre x (s.setMem m) = spec.pre x s := by intro _ s _; cases s; rfl)
    (h_post_mem : ∀ x (s0 sf : State) (m0 mf : Memory),
      spec.post x (s0.setMem m0) (sf.setMem mf) = spec.post x s0 sf := by
        intro _ s0 sf _ _; cases s0; cases sf; rfl) :
    MlKemBlockOk j (fun mpl => withMlKemRoOk mpl (withVmPreserved spec)) := by
  intro _
  simp only [subroutine_ok_iff, reaches_outcome_iff]
  intro x R s0 hpc hrun hpre hsp _hLj
  dsimp only [ToBaseSpec.toSpec, MultiPlacedLib.withCodeLoaded, withMlKemRoOk,
    withVmPreserved] at hpre
  rw [sepConj_comm (⌜MlKemRoOk mlkemMpl s0.mem⌝ ∗ spec.pre x s0) ⌜_⌝,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre_ro⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_ro
  obtain ⟨hro0, hpre_spec⟩ := hpre_ro
  let keep := mlkemKeepV mlkemMpl
  obtain ⟨R_view, hpre_strip, hunstrip⟩ := strip_frame keep hpre_spec
  let s0' := stripS keep s0
  have hcl_strip : mlkemMultiLib.CodeLoaded mlkemMpl s0'.mem := strip_codeLoaded_mlkemV hcl0
  have hro_strip : MlKemRoOk mlkemMpl s0'.mem := by
    simpa [s0', stripS_mem] using mlkemRoOk_stripExecOutside keep hro0
  have hpre' : s0'.mem ⊨
      (mlkemMultiLib.withCodeLoaded mlkemMpl (withMlKemRoOk mlkemMpl spec)).pre x s0' ∗ R_view := by
    dsimp only [MultiPlacedLib.withCodeLoaded, withMlKemRoOk]
    rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, pure_sepConj_of_true hcl_strip,
      sepConj_assoc, pure_sepConj_of_true hro_strip]
    have hs0_set : s0' = s0.setMem (stripExecOutside keep s0.mem) := by cases s0; rfl
    rw [hs0_set, h_pre_mem]
    simpa [State.setMem] using hpre_strip
  obtain ⟨sf', hsteps_blk, hout'⟩ := reaches_outcome_iff.1
    (subroutine_ok_iff.1 hok x R_view s0'
      (by simpa [s0', stripS_pc] using hpc)
      (by simpa [s0', stripS_status] using hrun)
      hpre'
      (by simpa [s0', stripS_spAligned] using hsp))
    (hcl_strip j hj)
  rcases hout' with ⟨hret', hcc', hpost'⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · obtain ⟨sf, hsf_eq, hsteps_P, hnsp, htp⟩ :=
      steps_lift_stripS_mlkemV MlKemPlacement.placeable hcl0
        rfl (Memory.KeepsFrozen.refl s0.mem) hsteps_blk (by rw [hret'.2.2]; decide)
    have hvm : VmPreserved s0 sf := vmPreserved_of_nonSyscall_tpidr hnsp htp
    refine ⟨sf, hsteps_P, Or.inl ⟨?_, ?_, ?_⟩⟩
    · rcases hret' with ⟨hr_pc, hr_sp, hr_st⟩
      rw [hsf_eq] at hr_pc hr_sp hr_st
      exact ⟨by simpa [s0', stripS_pc, stripS_readReg64] using hr_pc,
        by simpa [s0', stripS_sp] using hr_sp,
        by simpa [stripS_status] using hr_st⟩
    · rw [hsf_eq] at hcc'
      rcases hcc' with ⟨hsp_cc, hcs⟩
      exact ⟨by simpa [s0', stripS_sp] using hsp_cc, by cases s0; cases sf; exact hcs⟩
    · rw [hsf_eq] at hpost'
      dsimp only [MultiPlacedLib.withCodeLoaded, withMlKemRoOk] at hpost'
      have hs0_set : s0' = s0.setMem (stripExecOutside keep s0.mem) := by cases s0; rfl
      have hsf_set : stripS keep sf = sf.setMem (stripExecOutside keep sf.mem) := by cases sf; rfl
      rw [hs0_set, hsf_set, h_post_mem] at hpost'
      have hpost_sf : sf.mem ⊨ spec.post x s0 sf ∗ R :=
        hunstrip (fun a => congrFun hnsp.2.1 a) (by simpa [State.setMem] using hpost')
      dsimp only [ToBaseSpec.toSpec, MultiPlacedLib.withCodeLoaded, withMlKemRoOk, withVmPreserved]
      rw [sepConj_assoc, pure_sepConj_of_true hvm]
      exact hpost_sf
  · dsimp only [MultiPlacedLib.withCodeLoaded, withMlKemRoOk] at hp
    rw [hpan] at hp; exact False.elim (not_satisfies_false_sepConj hp)
  · dsimp only [MultiPlacedLib.withCodeLoaded, withMlKemRoOk] at he
    rw [hex] at he; exact False.elim (not_satisfies_false_sepConj he)
  · dsimp only [MultiPlacedLib.withCodeLoaded, withMlKemRoOk] at ho
    rw [hoom] at ho; exact False.elim (not_satisfies_false_sepConj ho)

/-- Lift any partial-correctness `MlKemBlockSafeOk j (fun mpl => withMlKemRoOk mpl spec)` (`j < 32`,
    memory-field-independent `spec` with `False` abnormal exits) to
    `withMlKemRoOk mpl (withVmPreserved spec)`. -/
theorem mlkemBlockSafeOk_withMlKemRoOk_withVmPreserved {j : Nat} {α : Type}
    {spec : Spec α}
    (hok : MlKemBlockSafeOk j (fun mpl => withMlKemRoOk mpl spec))
    (hj : j < mlkemMultiLib.blocks.length := by decide)
    (hpan : spec.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hex : spec.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom : spec.onOom = fun _ _ _ => ⌜False⌝ := by rfl)
    (h_pre_mem : ∀ x (s : State) (m : Memory),
      spec.pre x (s.setMem m) = spec.pre x s := by intro _ s _; cases s; rfl)
    (h_post_mem : ∀ x (s0 sf : State) (m0 mf : Memory),
      spec.post x (s0.setMem m0) (sf.setMem mf) = spec.post x s0 sf := by
        intro _ s0 sf _ _; cases s0; cases sf; rfl) :
    MlKemBlockSafeOk j (fun mpl => withMlKemRoOk mpl (withVmPreserved spec)) := by
  intro _ x R s0 hentry hpre _hLj
  dsimp only [ToBaseSpec.toSpec, MultiPlacedLib.withCodeLoaded, withMlKemRoOk,
    withVmPreserved] at hpre
  rw [sepConj_comm (⌜MlKemRoOk mlkemMpl s0.mem⌝ ∗ spec.pre x s0) ⌜_⌝,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre_ro⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_ro
  obtain ⟨hro0, hpre_spec⟩ := hpre_ro
  let keep := mlkemKeepV mlkemMpl
  obtain ⟨R_view, hpre_strip, hunstrip⟩ := strip_frame keep hpre_spec
  let s0' := stripS keep s0
  have hcl_strip : mlkemMultiLib.CodeLoaded mlkemMpl s0'.mem := strip_codeLoaded_mlkemV hcl0
  have hro_strip : MlKemRoOk mlkemMpl s0'.mem := by
    simpa [s0', stripS_mem] using mlkemRoOk_stripExecOutside keep hro0
  have hpre' : s0'.mem ⊨
      (mlkemMultiLib.withCodeLoaded mlkemMpl (withMlKemRoOk mlkemMpl spec)).pre x s0' ∗ R_view := by
    dsimp only [MultiPlacedLib.withCodeLoaded, withMlKemRoOk]
    rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, pure_sepConj_of_true hcl_strip,
      sepConj_assoc, pure_sepConj_of_true hro_strip]
    have hs0_set : s0' = s0.setMem (stripExecOutside keep s0.mem) := by cases s0; rfl
    rw [hs0_set, h_pre_mem]
    simpa [State.setMem] using hpre_strip
  have hentry' : AapcsEntry s0' (mlkemMpl.base j) :=
    ⟨by simpa [s0', stripS_pc] using hentry.1,
     by simpa [s0', stripS_status] using hentry.2.1,
     by simpa [s0', stripS_spAligned] using hentry.2.2⟩
  rcases hok x R_view s0' hentry' hpre' (hcl_strip j hj) with ⟨sf', hsteps_blk, hout'⟩ | hall'
  · rcases hout' with ⟨hret', hcc', hpost'⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
    · obtain ⟨sf, hsf_eq, hsteps_P, hnsp, htp⟩ :=
        steps_lift_stripS_mlkemV MlKemPlacement.placeable hcl0
          rfl (Memory.KeepsFrozen.refl s0.mem) hsteps_blk (by rw [hret'.2.2]; decide)
      have hvm : VmPreserved s0 sf := vmPreserved_of_nonSyscall_tpidr hnsp htp
      refine Or.inl ⟨sf, hsteps_P, Or.inl ⟨?_, ?_, ?_⟩⟩
      · rcases hret' with ⟨hr_pc, hr_sp, hr_st⟩
        rw [hsf_eq] at hr_pc hr_sp hr_st
        exact ⟨by simpa [s0', stripS_pc, stripS_readReg64] using hr_pc,
          by simpa [s0', stripS_sp] using hr_sp,
          by simpa [stripS_status] using hr_st⟩
      · rw [hsf_eq] at hcc'
        rcases hcc' with ⟨hsp_cc, hcs⟩
        exact ⟨by simpa [s0', stripS_sp] using hsp_cc, by cases s0; cases sf; exact hcs⟩
      · rw [hsf_eq] at hpost'
        dsimp only [MultiPlacedLib.withCodeLoaded, withMlKemRoOk] at hpost'
        have hs0_set : s0' = s0.setMem (stripExecOutside keep s0.mem) := by cases s0; rfl
        have hsf_set : stripS keep sf = sf.setMem (stripExecOutside keep sf.mem) := by cases sf; rfl
        rw [hs0_set, hsf_set, h_post_mem] at hpost'
        have hpost_sf : sf.mem ⊨ spec.post x s0 sf ∗ R :=
          hunstrip (fun a => congrFun hnsp.2.1 a) (by simpa [State.setMem] using hpost')
        dsimp only [ToBaseSpec.toSpec, MultiPlacedLib.withCodeLoaded, withMlKemRoOk,
          withVmPreserved]
        rw [sepConj_assoc, pure_sepConj_of_true hvm]
        exact hpost_sf
    · dsimp only [MultiPlacedLib.withCodeLoaded, withMlKemRoOk] at hp
      rw [hpan] at hp; exact False.elim (not_satisfies_false_sepConj hp)
    · dsimp only [MultiPlacedLib.withCodeLoaded, withMlKemRoOk] at he
      rw [hex] at he; exact False.elim (not_satisfies_false_sepConj he)
    · dsimp only [MultiPlacedLib.withCodeLoaded, withMlKemRoOk] at ho
      rw [hoom] at ho; exact False.elim (not_satisfies_false_sepConj ho)
  · exact Or.inr fun u hu =>
      steps_diverge_stripS_mlkemV MlKemPlacement.placeable hcl0 hu
        (Memory.KeepsFrozen.refl s0.mem) hall'

/-! ## 3. Stack-Parameterized Consumer Specifications (`rfl`-Equal at `extHookStack`) -/

/-- Stack-parameterized `<KeyPairCompressedBytes>::from_seed` consumer spec (`B10`, Hook #3). -/
@[expose] def mlkemFromSeedAtSpec (stk : Nat) (K : MlKem) : Spec MlkemFromSeedCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.seedA ∧ s.readReg64 .x8 = x.kpA⌝ ∗
      (x.seedA ↦ₛ x.seed.toList) ∗ memRegion x.kpA 2400 ∗ stackAt s.sp stk
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (x.seedA ↦ₛ x.seed.toList) ∗
      (x.kpA ↦ₛ (K.fromSeed x.seed).2.2.toList) ∗
      stackAt s0.sp stk

theorem mlkemFromSeedAtSpec_extHookStack (K : MlKem) :
    mlkemFromSeedAtSpec extHookStack K = mlkemFromSeedSpec K := rfl

/-- Stack-parameterized `mlkem768::incremental::encapsulate1` consumer spec (`B19`, Hook #4). -/
@[expose] def mlkemEncaps1AtSpec (stk : Nat) (K : MlKem) : Spec MlkemEncaps1Call where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.ret ∧ s.readReg64 .x0 = x.hdrA ∧
      (s.readReg64 .x1).toNat = x.hdr.length ∧ s.readReg64 .x2 = x.randA ∧
      s.readReg64 .x3 = x.esA ∧ s.readReg64 .x4 = 2080#64 ∧
      s.readReg64 .x5 = x.ssA ∧ s.readReg64 .x6 = 32#64⌝ ∗
      (x.hdrA ↦ₛ x.hdr) ∗ (x.randA ↦ₛ x.rand.toList) ∗
      memRegion x.ret 961 ∗ memRegion x.esA 2080 ∗ memRegion x.ssA 32 ∗
      stackAt s.sp stk
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (x.hdrA ↦ₛ x.hdr) ∗ (x.randA ↦ₛ x.rand.toList) ∗
      (match K.encaps1 x.hdr x.rand with
       | some (ct1, es, ss) =>
           (x.ret ↦₈ 0#8) ∗ ((x.ret + 1#64) ↦ₛ ct1.toList) ∗
           (x.esA ↦ₛ es.toList) ∗ (x.ssA ↦ₛ ss.toList)
       | none =>
           (x.ret ↦₈ 1#8) ∗ (∃∗ (err : BitVec 8), ((x.ret + 1#64) ↦₈ err)) ∗
           memRegion (x.ret + 2#64) 959 ∗
           memRegion x.esA 2080 ∗ memRegion x.ssA 32) ∗
      stackAt s0.sp stk

theorem mlkemEncaps1AtSpec_extHookStack (K : MlKem) :
    mlkemEncaps1AtSpec extHookStack K = mlkemEncaps1Spec K := rfl

/-- Stack-parameterized `mlkem768::incremental::encapsulate2` consumer spec (`B20`, Hook #5). -/
@[expose] def mlkemEncaps2AtSpec (stk : Nat) (K : MlKem) : Spec MlkemEncaps2Call where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.ret ∧ s.readReg64 .x0 = x.esA ∧ s.readReg64 .x1 = x.ekA⌝ ∗
      (x.esA ↦ₛ x.es.toList) ∗ (x.ekA ↦ₛ x.ek.toList) ∗
      memRegion x.ret 128 ∗ stackAt s.sp stk
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (x.esA ↦ₛ x.es.toList) ∗ (x.ekA ↦ₛ x.ek.toList) ∗
      (x.ret ↦ₛ (K.encaps2 x.es x.ek).toList) ∗
      stackAt s0.sp stk

theorem mlkemEncaps2AtSpec_extHookStack (K : MlKem) :
    mlkemEncaps2AtSpec extHookStack K = mlkemEncaps2Spec K := rfl

/-- Stack-parameterized `mlkem768::incremental::decapsulate_compressed_key` consumer spec (`B22`,
    Hook #6). -/
@[expose] def mlkemDecapsAtSpec (stk : Nat) (K : MlKem) : Spec MlkemDecapsCall where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.ret ∧ s.readReg64 .x0 = x.dkA ∧
      s.readReg64 .x1 = x.ct1A ∧ s.readReg64 .x2 = x.ct2A⌝ ∗
      (x.dkA ↦ₛ x.dk.toList) ∗ (x.ct1A ↦ₛ x.ct1.toList) ∗ (x.ct2A ↦ₛ x.ct2.toList) ∗
      memRegion x.ret 32 ∗ stackAt s.sp stk
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (x.dkA ↦ₛ x.dk.toList) ∗ (x.ct1A ↦ₛ x.ct1.toList) ∗ (x.ct2A ↦ₛ x.ct2.toList) ∗
      (x.ret ↦ₛ (K.decaps x.dk x.ct1 x.ct2).toList) ∗
      stackAt s0.sp stk

theorem mlkemDecapsAtSpec_extHookStack (K : MlKem) :
    mlkemDecapsAtSpec extHookStack K = mlkemDecapsSpec K := rfl

/-- Stack-parameterized `mlkem768::incremental::validate_pk_bytes` consumer spec (`B21`, Hook #7). -/
@[expose] def mlkemValidatePkAtSpec (stk : Nat) (K : MlKem) : Spec MlkemValidatePkCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.hdrA ∧ (s.readReg64 .x1).toNat = x.hdr.length ∧
      s.readReg64 .x2 = x.ekA ∧ (s.readReg64 .x3).toNat = x.ek.length⌝ ∗
      (x.hdrA ↦ₛ x.hdr) ∗ (x.ekA ↦ₛ x.ek) ∗ stackAt s.sp stk
  post := fun x s0 sf =>
    ⌜((sf.readReg64 .x0).setWidth 8 = 0xff#8 ↔ K.validPkBytes x.hdr x.ek = true) ∧
      sf.trace = s0.trace⌝ ∗
      (x.hdrA ↦ₛ x.hdr) ∗ (x.ekA ↦ₛ x.ek) ∗ stackAt s0.sp stk

theorem mlkemValidatePkAtSpec_extHookStack (K : MlKem) :
    mlkemValidatePkAtSpec extHookStack K = mlkemValidatePkSpec K := rfl

/-- Stack-parameterized `CliExt.kemEncapsSpec` (`mlkem1024::kyber::encapsulate`, `B24`, Hook #1). -/
@[expose] def kemEncapsAtSpec (stk : Nat) (Q : PqxdhPrims) :
    Spec (BitVec 64 × List.Vector (BitVec 8) 1568 × BitVec 64 × List.Vector (BitVec 8) 32 ×
      BitVec 64) :=
  withStack
    { pre := fun (pkA, pk, rA, rnd, ret) s =>
        ⌜s.readReg64 .x0 = pkA ∧ s.readReg64 .x1 = rA ∧ s.readReg64 .x8 = ret⌝ ∗
          (pkA ↦ₛ pk.toList) ∗ (rA ↦ₛ rnd.toList) ∗ memRegion ret 1600
      post := fun (_pkA, pk, rA, rnd, ret) s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗ (_pkA ↦ₛ pk.toList) ∗ memRegion rA 32 ∗
          (ret ↦ₛ (Q.encaps pk rnd).1.toList) ∗
          ((ret + 1568#64) ↦ₛ (Q.encaps pk rnd).2.toList) }
    stk

theorem kemEncapsAtSpec_extHookStack (Q : PqxdhPrims) :
    kemEncapsAtSpec extHookStack Q = kemEncapsSpec Q := rfl

/-- Stronger `mlkem1024::kyber::encapsulate` (`B24`, Hook #1) consumer contract preserving
    `(rA ↦ₛ rnd.toList)` (for `InitializeAliceStage1Common.kyberEncapsStubSpec`). -/
@[expose] def kemEncapsPreservedAtSpec (stk : Nat) (Q : PqxdhPrims) :
    Spec (BitVec 64 × List.Vector (BitVec 8) 1568 × BitVec 64 × List.Vector (BitVec 8) 32 ×
      BitVec 64) :=
  withStack
    { pre := fun (pkA, pk, rA, rnd, ret) s =>
        ⌜s.readReg64 .x0 = pkA ∧ s.readReg64 .x1 = rA ∧ s.readReg64 .x8 = ret⌝ ∗
          (pkA ↦ₛ pk.toList) ∗ (rA ↦ₛ rnd.toList) ∗ memRegion ret 1600
      post := fun (pkA, pk, rA, rnd, ret) s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗ (pkA ↦ₛ pk.toList) ∗ (rA ↦ₛ rnd.toList) ∗
          (ret ↦ₛ (Q.encaps pk rnd).1.toList) ∗
          ((ret + 1568#64) ↦ₛ (Q.encaps pk rnd).2.toList) }
    stk

/-- Stack-parameterized `CliExt.kemDecapsSpec` (`mlkem1024::kyber::decapsulate`, `B23`, Hook #2). -/
@[expose] def kemDecapsAtSpec (stk : Nat) (Q : PqxdhPrims) :
    Spec (BitVec 64 × List.Vector (BitVec 8) 3168 × BitVec 64 × List.Vector (BitVec 8) 1568 ×
      BitVec 64) :=
  withStack
    { pre := fun (skA, sk, ctA, ct, ret) s =>
        ⌜s.readReg64 .x0 = skA ∧ s.readReg64 .x1 = ctA ∧ s.readReg64 .x8 = ret⌝ ∗
          (skA ↦ₛ sk.toList) ∗ (ctA ↦ₛ ct.toList) ∗ memRegion ret 32
      post := fun (skA, sk, ctA, ct, ret) s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗ (skA ↦ₛ sk.toList) ∗ (ctA ↦ₛ ct.toList) ∗
          (ret ↦ₛ (Q.decaps sk ct).toList) }
    stk

theorem kemDecapsAtSpec_extHookStack (Q : PqxdhPrims) :
    kemDecapsAtSpec extHookStack Q = kemDecapsSpec Q := rfl

/-! ## 4. Unconditional Consumer Bridges: Hooks #5 (`mlkemEncaps2`) and #7 (`mlkemValidatePk`) -/

/-- Forward simulation from `mlkemEncaps2CoreSpec` (`6128` B tight stack) to
    `withMlKemRoOk mpl (keepsFs (mlkemEncaps2AtSpec stk K))` for any `6128 ≤ stk ≤ 2 ^ 64`. -/
private theorem mlkemEncaps2Core_simulates_atSpec (K : MlKem)
    (hK : ∀ es ek, K.encaps2 es ek = toByteVec 128 (mlkem768Encaps2List es.toList ek.toList))
    (stk : Nat) (hstk : 6128 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (mpl : MultiPlacement) :
    SpecSimulates (mlkemEncaps2CoreSpec mpl)
      (withMlKemRoOk mpl (keepsFs (mlkemEncaps2AtSpec stk K))) := by
  refine SpecSimulates.of_map ?_
  intro y R s0 hm
  dsimp only [withMlKemRoOk, keepsFs, mlkemEncaps2AtSpec] at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hro, hm⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hx8, hx0, hx1⟩, hm⟩
  rw [stackAt_shrink s0.sp stk 6128 hstk hstk_fit] at hm
  set slack := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - 6128)
  refine ⟨(y.ret, y.esA, y.es.toList, y.ekA, y.ek.toList), slack ∗ R, ?_, ?_⟩
  · dsimp only [mlkemEncaps2CoreSpec, withNonSyscallPreserved,
      Mlkem768.Encaps2.Base.mlkemEncaps2RawSpec]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx8, hx0, hx1, y.es.toList_length, y.ek.toList_length, hro⟩, ?_⟩
    rw [sepConj_comm slack (stackAt s0.sp 6128),
      sepConj_assoc (stackAt s0.sp 6128) slack R] at hm
    exact hm
  · intro sf _ _ hpost
    dsimp only [mlkemEncaps2CoreSpec, withNonSyscallPreserved,
      Mlkem768.Encaps2.Base.mlkemEncaps2RawSpec] at hpost
    dsimp only [withMlKemRoOk, keepsFs, mlkemEncaps2AtSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hnsp, hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hnsp.2.2.2.2.2.2, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hnsp.1, ?_⟩
    rw [hK, Mlkem768.Encaps2.Base.toByteVec_toList_of_length
      (Mlkem768.Encaps2.Base.mlkem768Encaps2List_length _ _)]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc] at hpost ⊢
    rw [← sepConj_assoc (stackAt s0.sp 6128) slack R,
      sepConj_comm (stackAt s0.sp 6128) slack,
      ← stackAt_shrink s0.sp stk 6128 hstk hstk_fit] at hpost
    exact hpost

/-- Hook #5 (`mlkemEncaps2Name`, `B20`): stack-parameterized `withVmPreserved` + `keepsFs`
    real-code `subroutineOk` (`6128 ≤ stk ≤ 2 ^ 64`). -/
theorem mlkemEncaps2_at_keepsFs_vm_subroutineOk (K : MlKem)
    (hK : ∀ es ek, K.encaps2 es ek = toByteVec 128 (mlkem768Encaps2List es.toList ek.toList))
    (stk : Nat) (hstk : 6128 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk mlkemEncaps2Name
      (fun mpl => withMlKemRoOk mpl (keepsFs (withVmPreserved (mlkemEncaps2AtSpec stk K))))
      externs := by
  have hblk_kfs : MlKemBlockOk 20
      (fun mpl => withMlKemRoOk mpl (keepsFs (mlkemEncaps2AtSpec stk K))) :=
    specSimulates_mlkemBlockOk
      (mlkemEncaps2Core_simulates_atSpec K hK stk hstk hstk_fit) blk20_encaps2_ok
  have hblk_vm : MlKemBlockOk 20
      (fun mpl => withMlKemRoOk mpl (withVmPreserved (keepsFs (mlkemEncaps2AtSpec stk K)))) :=
    mlkemBlockOk_withMlKemRoOk_withVmPreserved hblk_kfs
  have hblk : MlKemBlockOk 20
      (fun mpl => withMlKemRoOk mpl (keepsFs (withVmPreserved (mlkemEncaps2AtSpec stk K)))) :=
    specSimulates_mlkemBlockOk
      (fun mpl => specSimulates_withMlKemRoOk_map mpl specSimulates_keepsFs_withVmPreserved)
      hblk_vm
  exact mlkemSubroutineOk_of_blockOk_ext hblk externs

/-- Hook #5 (`mlkemEncaps2Name`, `B20`): stack-parameterized `withVmPreserved` real-code
    `subroutineOk` (`6128 ≤ stk ≤ 2 ^ 64`). -/
theorem mlkemEncaps2_at_vm_subroutineOk (K : MlKem)
    (hK : ∀ es ek, K.encaps2 es ek = toByteVec 128 (mlkem768Encaps2List es.toList ek.toList))
    (stk : Nat) (hstk : 6128 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk mlkemEncaps2Name
      (fun mpl => withMlKemRoOk mpl (withVmPreserved (mlkemEncaps2AtSpec stk K)))
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl => specSimulates_withMlKemRoOk_map mpl SpecSimulates.drop_keepsFs)
    (mlkemEncaps2_at_keepsFs_vm_subroutineOk K hK stk hstk hstk_fit externs)

/-- Hook #5 (`mlkemEncaps2Name`, `B20`): stack-parameterized non-budget real-code `subroutineOk`. -/
theorem mlkemEncaps2_at_subroutineOk (K : MlKem)
    (hK : ∀ es ek, K.encaps2 es ek = toByteVec 128 (mlkem768Encaps2List es.toList ek.toList))
    (stk : Nat) (hstk : 6128 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk mlkemEncaps2Name
      (fun mpl => withMlKemRoOk mpl (mlkemEncaps2AtSpec stk K))
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl => specSimulates_withMlKemRoOk_map mpl specSimulates_drop_withVmPreserved)
    (mlkemEncaps2_at_vm_subroutineOk K hK stk hstk hstk_fit externs)

/-- Hook #5 (`mlkemEncaps2Name`, `B20`): `SpqrHooksBudget.encaps2` real-code bridge at
    `extHookStack` (`16384` B). -/
theorem mlkemEncaps2_vm_subroutineOk (K : MlKem)
    (hK : ∀ es ek, K.encaps2 es ek = toByteVec 128 (mlkem768Encaps2List es.toList ek.toList))
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk mlkemEncaps2Name
      (fun mpl => withMlKemRoOk mpl (withVmPreserved (mlkemEncaps2Spec K)))
      externs :=
  mlkemEncaps2_at_vm_subroutineOk K hK extHookStack (by decide) (by decide) externs

/-- Hook #5 (`mlkemEncaps2Name`, `B20`): `SpqrHooks.encaps2` real-code bridge at `extHookStack`. -/
theorem mlkemEncaps2_subroutineOk (K : MlKem)
    (hK : ∀ es ek, K.encaps2 es ek = toByteVec 128 (mlkem768Encaps2List es.toList ek.toList))
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk mlkemEncaps2Name
      (fun mpl => withMlKemRoOk mpl (mlkemEncaps2Spec K))
      externs :=
  mlkemEncaps2_at_subroutineOk K hK extHookStack (by decide) (by decide) externs

/-- Hook #5 (`mlkemEncaps2Name`, `B20`): `stk = 65536` `withVmPreserved` specialization. -/
theorem mlkemEncaps2_65536_vm_subroutineOk (K : MlKem)
    (hK : ∀ es ek, K.encaps2 es ek = toByteVec 128 (mlkem768Encaps2List es.toList ek.toList))
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk mlkemEncaps2Name
      (fun mpl => withMlKemRoOk mpl (withVmPreserved (mlkemEncaps2AtSpec 65536 K)))
      externs :=
  mlkemEncaps2_at_vm_subroutineOk K hK 65536 (by decide) (by decide) externs

/-- Hook #5 (`mlkemEncaps2Name`, `B20`): `mlkem768Incremental` concrete `withVmPreserved` bridge. -/
theorem mlkemEncaps2_inc_vm_subroutineOk
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk mlkemEncaps2Name
      (fun mpl => withMlKemRoOk mpl (withVmPreserved (mlkemEncaps2Spec mlkem768Incremental)))
      externs :=
  mlkemEncaps2_vm_subroutineOk mlkem768Incremental (fun _ _ => rfl) externs

/-- Forward simulation from `mlkemValidatePkValidCoreSpec` (`5824` B tight stack) to
    `withMlKemRoOk mpl (keepsFs (mlkemValidatePkAtSpec stk K))` for any `5824 ≤ stk ≤ 2 ^ 64`. -/
private theorem mlkemValidatePkValidCore_simulates_atSpec (K : MlKem)
    (hK : ∀ hdr ek, K.validPk hdr ek = mlkem768ValidPk hdr ek)
    (stk : Nat) (hstk : 5824 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (mpl : MultiPlacement) :
    SpecSimulates (mlkemValidatePkValidCoreSpec mpl)
      (withMlKemRoOk mpl (keepsFs (mlkemValidatePkAtSpec stk K))) := by
  refine SpecSimulates.of_map ?_
  intro y R s0 hm
  dsimp only [withMlKemRoOk, keepsFs, mlkemValidatePkAtSpec] at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hro, hm⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hx0, hx1, hx2, hx3⟩, hm⟩
  rw [stackAt_shrink s0.sp stk 5824 hstk hstk_fit] at hm
  set slack := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - 5824)
  refine ⟨(y.hdrA, y.hdr, y.ekA, y.ek), slack ∗ R, ?_, ?_⟩
  · dsimp only [mlkemValidatePkValidCoreSpec, withNonSyscallPreserved, mlkemValidatePkValidRawSpec]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hro⟩, ?_⟩
    rw [sepConj_comm slack (stackAt s0.sp 5824),
      sepConj_assoc (stackAt s0.sp 5824) slack R] at hm
    exact hm
  · intro sf _ _ hpost
    dsimp only [mlkemValidatePkValidCoreSpec, withNonSyscallPreserved,
      mlkemValidatePkValidRawSpec] at hpost
    dsimp only [withMlKemRoOk, keepsFs, mlkemValidatePkAtSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hnsp, hpost⟩
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hiff, hpost⟩
    rw [validPkBytes_eq_mlkem768ValidPk K hK y.hdr y.ek]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hnsp.2.2.2.2.2.2, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hiff, hnsp.1⟩, ?_⟩
    rw [← sepConj_assoc (stackAt s0.sp 5824) slack R,
      sepConj_comm (stackAt s0.sp 5824) slack,
      ← stackAt_shrink s0.sp stk 5824 hstk hstk_fit] at hpost
    exact hpost

/-- Hook #7 (`mlkemValidatePkName`, `B21`): stack-parameterized `withVmPreserved` + `keepsFs`
    real-code `subroutineOk` (`5824 ≤ stk ≤ 2 ^ 64`). -/
theorem mlkemValidatePk_at_keepsFs_vm_subroutineOk (K : MlKem)
    (hK : ∀ hdr ek, K.validPk hdr ek = mlkem768ValidPk hdr ek)
    (stk : Nat) (hstk : 5824 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk mlkemValidatePkName
      (fun mpl => withMlKemRoOk mpl (keepsFs (withVmPreserved (mlkemValidatePkAtSpec stk K))))
      externs := by
  have hblk_kfs : MlKemBlockOk 21
      (fun mpl => withMlKemRoOk mpl (keepsFs (mlkemValidatePkAtSpec stk K))) :=
    specSimulates_mlkemBlockOk
      (mlkemValidatePkValidCore_simulates_atSpec K hK stk hstk hstk_fit) blk21_validate_pk_validPk_ok
  have hblk_vm : MlKemBlockOk 21
      (fun mpl => withMlKemRoOk mpl (withVmPreserved (keepsFs (mlkemValidatePkAtSpec stk K)))) :=
    mlkemBlockOk_withMlKemRoOk_withVmPreserved hblk_kfs
  have hblk : MlKemBlockOk 21
      (fun mpl => withMlKemRoOk mpl (keepsFs (withVmPreserved (mlkemValidatePkAtSpec stk K)))) :=
    specSimulates_mlkemBlockOk
      (fun mpl => specSimulates_withMlKemRoOk_map mpl specSimulates_keepsFs_withVmPreserved)
      hblk_vm
  exact mlkemSubroutineOk_of_blockOk_ext hblk externs

/-- Hook #7 (`mlkemValidatePkName`, `B21`): stack-parameterized `withVmPreserved` real-code
    `subroutineOk` (`5824 ≤ stk ≤ 2 ^ 64`). -/
theorem mlkemValidatePk_at_vm_subroutineOk (K : MlKem)
    (hK : ∀ hdr ek, K.validPk hdr ek = mlkem768ValidPk hdr ek)
    (stk : Nat) (hstk : 5824 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk mlkemValidatePkName
      (fun mpl => withMlKemRoOk mpl (withVmPreserved (mlkemValidatePkAtSpec stk K)))
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl => specSimulates_withMlKemRoOk_map mpl SpecSimulates.drop_keepsFs)
    (mlkemValidatePk_at_keepsFs_vm_subroutineOk K hK stk hstk hstk_fit externs)

/-- Hook #7 (`mlkemValidatePkName`, `B21`): stack-parameterized non-budget real-code `subroutineOk`. -/
theorem mlkemValidatePk_at_subroutineOk (K : MlKem)
    (hK : ∀ hdr ek, K.validPk hdr ek = mlkem768ValidPk hdr ek)
    (stk : Nat) (hstk : 5824 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk mlkemValidatePkName
      (fun mpl => withMlKemRoOk mpl (mlkemValidatePkAtSpec stk K))
      externs :=
  SpecSimulates.multiSubroutineOk
    (fun mpl => specSimulates_withMlKemRoOk_map mpl specSimulates_drop_withVmPreserved)
    (mlkemValidatePk_at_vm_subroutineOk K hK stk hstk hstk_fit externs)

/-- Hook #7 (`mlkemValidatePkName`, `B21`): `SpqrHooksBudget.validatePk` real-code bridge at
    `extHookStack` (`16384` B). -/
theorem mlkemValidatePk_vm_subroutineOk (K : MlKem)
    (hK : ∀ hdr ek, K.validPk hdr ek = mlkem768ValidPk hdr ek)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk mlkemValidatePkName
      (fun mpl => withMlKemRoOk mpl (withVmPreserved (mlkemValidatePkSpec K)))
      externs :=
  mlkemValidatePk_at_vm_subroutineOk K hK extHookStack (by decide) (by decide) externs

/-- Hook #7 (`mlkemValidatePkName`, `B21`): `SpqrHooks.validatePk` real-code bridge at
    `extHookStack`. -/
theorem mlkemValidatePk_subroutineOk (K : MlKem)
    (hK : ∀ hdr ek, K.validPk hdr ek = mlkem768ValidPk hdr ek)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk mlkemValidatePkName
      (fun mpl => withMlKemRoOk mpl (mlkemValidatePkSpec K))
      externs :=
  mlkemValidatePk_at_subroutineOk K hK extHookStack (by decide) (by decide) externs

/-- Hook #7 (`mlkemValidatePkName`, `B21`): `stk = 65536` `withVmPreserved` specialization. -/
theorem mlkemValidatePk_65536_vm_subroutineOk (K : MlKem)
    (hK : ∀ hdr ek, K.validPk hdr ek = mlkem768ValidPk hdr ek)
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk mlkemValidatePkName
      (fun mpl => withMlKemRoOk mpl (withVmPreserved (mlkemValidatePkAtSpec 65536 K)))
      externs :=
  mlkemValidatePk_at_vm_subroutineOk K hK 65536 (by decide) (by decide) externs

/-- Hook #7 (`mlkemValidatePkName`, `B21`): `mlkem768Incremental` concrete `withVmPreserved`
    bridge. -/
theorem mlkemValidatePk_inc_vm_subroutineOk
    (externs : String → Option (State → State) := fun _ => none) :
    mlkemMultiLib.subroutineOk mlkemValidatePkName
      (fun mpl => withMlKemRoOk mpl (withVmPreserved (mlkemValidatePkSpec mlkem768Incremental)))
      externs :=
  mlkemValidatePk_vm_subroutineOk mlkem768Incremental (fun _ _ => rfl) externs

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.ConsumerBridgesBase
