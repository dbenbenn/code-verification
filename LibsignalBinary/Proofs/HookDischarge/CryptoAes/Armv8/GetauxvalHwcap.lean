/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.AllocZeroedFine
public import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.GetauxvalCode -- proof-setup: allow-public-import
import ProofLib.Hoare.OutcomeSteps
import VerifiedLibraries.Mallocng.Proofs.Common
import LibsignalBinary.Heap.Fine.Inv
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `PoolAesInitSplit` and Budget-Pool Discharge of `features_aes::init_get::init_inner`

Re-exports `GetauxvalCode` and lifts `features_aes::init_get::init_inner` to `RustCliAllocBudget M`
via `PoolAesInitSplit` so AES-CBC proofs retain `(storageAddr ↦₈ v)` across `base` allocator calls.
-/

public section
set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.GetauxvalHwcap

open Arm64 SepProp
open ProofLib hiding MallocngAddrs MallocngIface
open ProofLib.StdStartup (hasInstrs)
open CryptoVerification.RustHeap (allocHookStack)
open VerifiedLibraries.Mallocng (MallocngAddrs MallocngAuxvAt MallocngRuntime mallocngAddrsOfPlacement)
open VerifiedLibraries.Mallocng.Proofs
  (ByteMap MallocngAuxvPtrCell MallocngAuxvRoAt MallocngAuxvStateRo
   MallocngCoreStInflightModeA MallocngLiveAuth MallocngRoTablesA MallocngSt MallocngWFInflight
   MappedSet OwnedMappedByte OwnedProtNoneByte OwnedRwByte ProgContainsMallocng ProtNoneByteMap)
open VerifiedLibraries.RustStd (RustStdRdlShimCode RustStdThunkCode mallocngPlacedCAddrs)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits FdsHiFrame MallocngCostModelIface MallocngCostModelSound PoolPreserved RustAllocAddrs
   RustCliAllocBudget RustCliAllocBudgetEntriesBase VmPreserved mallocngBudgetPool
   mallocngBudgetPoolAt_split_runtime mallocngBudgetPoolAt_transport_mem mallocngBudgetPoolAt_zero_transport
   mallocngBudgetPoolInv mallocngBudgetPoolInv_transport_mem mallocngLiveM mallocngRustCliAllocBudget
   mallocngRustCliAllocBudgetAt rustCliAllocBudgetSpecBase rustCliDeallocBudgetSpecBase
   rustCliReallocBudgetSpecBase zeroBudgetLimits)
open LibsignalBinary.Heap.SpecBudget (rustAllocZeroedBudgetSpecBase)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec)
open LibsignalBinary.Heap.Fine
  (FineBudget FineCoreImpl FineCoreImpl_eq FineCoreStInflightA MallocngFineInv allocMemsetVmSpec fineAlignGam fineBaseGam
   fineCostModel fineCostModelIface fineCostModelSound fineRdlAllocZeroed_budget_placed_ok fineRustCliAllocBudget
   fineRustCliAllocBudgetEntries fineRustCliAllocBudgetEntries_thunks fineRustCliAllocZeroedBudget_thunk_ok rdlAllocZeroedInstrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase
  (CodeBlocksPermRX aesStorageCell codeBlocksPermRX_of_keepsFrozen codeBlocksPermRX_of_perm_eq
   fineHookRustCliAllocBudget mallocngHookBudgetPool mallocngHookRustCliAllocBudget)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon (PureStepPreserved)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon.Simp

export LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.GetauxvalCode
  (errnoLocationWords errnoLocationInstrs getauxvalInstrsAt getauxvalHwcapInstrs aesInitInnerInstrs)
export LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.GetauxvalCode
  (AesInitInnerCode auxvEntryWords auxvLookupVal auxvLookupErrno aesHwcapDetectByte)
export LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.GetauxvalCode
  (aesHwcapDetectByte_mem step_str32_perm errnoLocationSpec getauxvalNonSecureSpec getauxvalHwcapRawSpec)
export LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.GetauxvalCode
  (aesInitInnerRawSpec errnoLocation_ok getauxval_nonSecure_ok getauxvalHwcap_ok aesInitInnerRaw_ok)

/-! ## 1. Pool-Level `init_inner` Specifications, `PoolAesInitSplit`, and `bl` Combinators -/

/-- Pool-level contract for `features_aes::init_get::init_inner` over `(storageAddr ↦₈ oldVal)` and `base.pool`. -/
@[expose] def aesInitInnerSpec (M : AllocCostModel) (base : RustCliAllocBudget M)
    (storageAddr : BitVec 64) (lim : BudgetLimits) : Spec (BitVec 8 × M.σ) where
  pre := fun (oldVal, st) s0 => (storageAddr ↦₈ oldVal) ∗ base.pool lim st s0 ∗ stackFrameAt s0.sp 0x30
  post := fun (_, st) s0 sf => ∃∗ b : BitVec 8,
    ⌜(b = 0#8 ∨ b = 1#8) ∧ sf.readReg64 .x0 = b.zeroExtend 64 ∧ PureStepPreserved s0 sf⌝ ∗
      ((storageAddr ↦₈ b) ∗ base.pool lim st sf ∗ stackFrameAt s0.sp 0x30)
  onPanic := fun _ _ _ => ⌜False⌝; onExit := fun _ _ _ _ => ⌜False⌝; onOom := fun _ _ _ => ⌜False⌝

theorem allocHookStack_split_48 (sp : BitVec 64) :
    stackAt sp allocHookStack = stackFrameAt sp 0x30 ∗ stackFrameAt (sp - 0x30#64) 4048 := by
  unfold stackAt allocHookStack
  rw [← stackFrameAt_eq_memRegion sp 4096 (by decide), show (4096 : Nat) = 0x30 + 4048 from rfl,
      stackFrameAt_split sp 0x30 4048 (by decide)]

/-- Decomposes `A : RustCliAllocBudget M` into `(storageAddr ↦₈ v)` and storage-free `base`, plus `initInner_ok`. -/
class PoolAesInitSplit {M : AllocCostModel} (A : RustCliAllocBudget M) (storageAddr : BitVec 64) where
  base : RustCliAllocBudget M
  libcAddr : BitVec 64
  live_eq : A.live = base.live
  pool_eq : ∀ (lim : BudgetLimits) (st : M.σ) (s : State),
    A.pool lim st s = ∃∗ v : BitVec 8, (storageAddr ↦₈ v) ∗ base.pool lim st s
  initInner_ok :
    ∀ {P : Program} {initInnerAddr getauxvalHwcapAddr getauxvalAddr errnoLocationAddr : BitVec 64} (lim : BudgetLimits),
      AesInitInnerCode P initInnerAddr getauxvalHwcapAddr getauxvalAddr errnoLocationAddr libcAddr storageAddr →
      subroutine_ok P initInnerAddr (aesInitInnerSpec M base storageAddr lim)

namespace PoolAesInitSplit
variable {M : AllocCostModel} {A : RustCliAllocBudget M} {storageAddr : BitVec 64}
@[simp] theorem repAlloc_eq (h : PoolAesInitSplit A storageAddr) : A.repAlloc = h.base.repAlloc := by
  simp only [RustCliAllocBudget.repAlloc, h.live_eq]
theorem pool_out (h : PoolAesInitSplit A storageAddr) (lim : BudgetLimits) (st : M.σ) (s : State) :
    A.pool lim st s ⊢ ∃∗ v : BitVec 8, (storageAddr ↦₈ v) ∗ h.base.pool lim st s := Entails.of_eq (h.pool_eq lim st s)
theorem pool_in (h : PoolAesInitSplit A storageAddr) (lim : BudgetLimits) (st : M.σ) (s : State) (v : BitVec 8) :
    (storageAddr ↦₈ v) ∗ h.base.pool lim st s ⊢ A.pool lim st s := by
  rw [h.pool_eq lim st s]; exact Entails.sepExists_right v (Entails.refl _)
theorem pool_split (h : PoolAesInitSplit A storageAddr) (lim : BudgetLimits) (st : M.σ) (s : State) :
    (A.pool lim st s ⊢ ∃∗ v : BitVec 8, (storageAddr ↦₈ v) ∗ h.base.pool lim st s) ∧
    (∀ v : BitVec 8, (storageAddr ↦₈ v) ∗ h.base.pool lim st s ⊢ A.pool lim st s) :=
  ⟨h.pool_out lim st s, h.pool_in lim st s⟩
@[expose, instance_reducible] def castStorage {storageAddr' : BitVec 64} (heq : storageAddr = storageAddr')
    (h : PoolAesInitSplit A storageAddr) : PoolAesInitSplit A storageAddr' := heq ▸ h
end PoolAesInitSplit

/-- `SepWP` call combinator for `bl initInnerAddr` over `(storageAddr ↦₈ oldVal) ∗ base.pool ∗ stackFrameAt s.sp 0x30`. -/
theorem step_bl_aesInitInner {M : AllocCostModel} {base : RustCliAllocBudget M}
    {P : Program} {pc_bl initInnerAddr target_pc storageAddr : BitVec 64} {lim : BudgetLimits}
    (oldVal : BitVec 8) (st : M.σ) (hf : P.fetch pc_bl = some (.bl (initInnerAddr - pc_bl)))
    (hcall : subroutine_ok P initInnerAddr (aesInitInnerSpec M base storageAddr lim))
    {s : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc_bl) (hrun : s.status = .Running) (hsp_al : s.spAligned = true)
    (hent : Pre ⊢ ((storageAddr ↦₈ oldVal) ∗ base.pool lim st s ∗ stackFrameAt s.sp 0x30) ∗ F)
    (hnext : ∀ (sf : State) (b : BitVec 8), (b = 0#8 ∨ b = 1#8) → sf.readReg64 .x0 = b.zeroExtend 64 →
      sf.pc = pc_bl + 4#64 → sf.status = .Running → sf.sp = s.sp → CalleeSavedPreserved s sf → PureStepPreserved s sf →
      SepWP P target_pc sf (((storageAddr ↦₈ b) ∗ base.pool lim st sf ∗ stackFrameAt s.sp 0x30) ∗ F) post oom) :
    SepWP P target_pc s Pre post oom := by
  let s_call := P.evalInst (.bl (initInnerAddr - pc_bl)) (s.setPC pc_bl)
  have ⟨hmem_sc, hrun_sc, hsp_sc_eq, hlr_sc⟩ :
      s_call.mem = s.mem ∧ s_call.status = .Running ∧ s_call.sp = s.sp ∧ s_call.readReg64 Reg.lr = pc_bl + 4#64 := by
    simp [s_call, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm, hrun]
  have hpc_sc : s_call.pc = initInnerAddr := by simp [s_call, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]; bv_omega
  have hsp_sc : s_call.spAligned = true := by simp only [State.spAligned, hsp_sc_eq]; exact hsp_al
  have hp_sc : PureStepPreserved s s_call := PureStepPreserved.of_proj_perm
    (by simp [s_call, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]) (by simp [hmem_sc])
  have hcs_sc : CalleeSavedPreserved s s_call := by
    rw [CalleeSavedPreserved.iff_regs]; simp [s_call, Program.evalInst, execInstWithSvc, arm64_norm, wp_norm]
  apply SepWP.step_pure hpc hrun hf rfl hmem_sc
  refine SepWP.call_subroutine_frame hcall (x := (oldVal, st)) (F := F) hpc_sc hrun_sc hsp_sc hlr_sc
    (fun R hm => ?_) (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h) (fun sf hpc_f hrun_f hsp_f hcs_f => ?_)
    (fun _ _ _ h => (not_satisfies_false_sepConj h).elim)
  · dsimp only [aesInitInnerSpec]; rw [base.pool_transport lim st s s_call hp_sc.vmPreserved, hsp_sc_eq, ← sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left hent) hm
  · dsimp only [aesInitInnerSpec]; rw [hsp_sc_eq, sepExists_sepConj_left]
    apply SepWP.exists_elim; intro b; rw [sepConj_assoc]; apply SepWP.pure_elim; rintro ⟨hb, hx0, hp_f⟩
    exact hnext sf b hb hx0 hpc_f hrun_f (hsp_f.trans hsp_sc_eq) (hcs_sc.trans hcs_f) (hp_sc.trans hp_f)

/-- Convenience `SepWP` call combinator for `bl initInnerAddr` over `stackAt s.sp allocHookStack`. -/
theorem step_bl_aesInitInner_allocStack {M : AllocCostModel} {base : RustCliAllocBudget M}
    {P : Program} {pc_bl initInnerAddr target_pc storageAddr : BitVec 64} {lim : BudgetLimits}
    (oldVal : BitVec 8) (st : M.σ) (hf : P.fetch pc_bl = some (.bl (initInnerAddr - pc_bl)))
    (hcall : subroutine_ok P initInnerAddr (aesInitInnerSpec M base storageAddr lim))
    {s : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc_bl) (hrun : s.status = .Running) (hsp_al : s.spAligned = true)
    (hent : Pre ⊢ ((storageAddr ↦₈ oldVal) ∗ base.pool lim st s ∗ stackAt s.sp allocHookStack) ∗ F)
    (hnext : ∀ (sf : State) (b : BitVec 8), (b = 0#8 ∨ b = 1#8) → sf.readReg64 .x0 = b.zeroExtend 64 →
      sf.pc = pc_bl + 4#64 → sf.status = .Running → sf.sp = s.sp → CalleeSavedPreserved s sf → PureStepPreserved s sf →
      SepWP P target_pc sf (((storageAddr ↦₈ b) ∗ base.pool lim st sf ∗ stackAt s.sp allocHookStack) ∗ F) post oom) :
    SepWP P target_pc s Pre post oom :=
  step_bl_aesInitInner oldVal st hf hcall hpc hrun hsp_al (F := stackFrameAt (s.sp - 0x30#64) 4048 ∗ F)
    (Entails.trans hent (Entails.of_eq (by rw [allocHookStack_split_48 s.sp]; sep_ac_rfl)))
    fun sf b hb hx0 hpc_f hrun_f hsp_f hcs_f hp_f =>
      SepWP.weaken_pre (Entails.of_eq (by rw [allocHookStack_split_48 s.sp]; sep_ac_rfl))
        (hnext sf b hb hx0 hpc_f hrun_f hsp_f hcs_f hp_f)

theorem aesInitInner_lift_pool {M : AllocCostModel}
    {base base' : RustCliAllocBudget M} {P : Program} {initInnerAddr storageAddr : BitVec 64} {lim : BudgetLimits}
    (hSplit : ∀ (s0 : State) (st : M.σ) (m : Memory) (R : SepProp), m ⊨ base'.pool lim st s0 ∗ R →
      ∃ F_extra : SepProp, (m ⊨ base.pool lim st s0 ∗ (F_extra ∗ R)) ∧
        (∀ (sf : State) (m' : Memory) (R' : SepProp), PureStepPreserved s0 sf →
          m' ⊨ base.pool lim st sf ∗ (F_extra ∗ R') → m' ⊨ base'.pool lim st sf ∗ R'))
    (hok : subroutine_ok P initInnerAddr (aesInitInnerSpec M base storageAddr lim)) :
    subroutine_ok P initInnerAddr (aesInitInnerSpec M base' storageAddr lim) := by
  apply subroutine_ok.of_codeLoaded; rintro ⟨oldVal, st⟩ R s0 hpc hrun hpre hsp _; dsimp only [aesInitInnerSpec] at hpre
  obtain ⟨F_extra, hpre_b, hReasm⟩ := hSplit s0 st s0.mem (((storageAddr ↦₈ oldVal) ∗ stackFrameAt s0.sp 0x30) ∗ R)
    (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre)
  have hpre0 : s0.mem ⊨ (aesInitInnerSpec M base storageAddr lim).pre (oldVal, st) s0 ∗ (F_extra ∗ R) :=
    Satisfies.mono (Entails.of_eq (by dsimp only [aesInitInnerSpec]; sep_ac_rfl)) hpre_b
  refine (hok.to_outcome (oldVal, st) (F_extra ∗ R) s0 hpc hrun hpre0 hsp).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [aesInitInnerSpec] at hpost ⊢; simp only [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨b, hb_sat⟩; rw [sepConj_assoc, satisfies_pure_sepConj] at hb_sat
    rcases hb_sat with ⟨⟨hb, hx0, hpure⟩, hm_f⟩; refine ⟨b, ?_⟩; rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hb, hx0, hpure⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl))
      (hReasm sf sf.mem (((storageAddr ↦₈ b) ∗ stackFrameAt s0.sp 0x30) ∗ R) hpure
        (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm_f))⟩
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

private theorem aesInitInner_lift_frame_pure {M : AllocCostModel}
    {base base' : RustCliAllocBudget M} {P : Program} {initInnerAddr storageAddr : BitVec 64} {lim : BudgetLimits}
    (F_ro : SepProp) (φ : State → Prop) (hB : ∀ st s, base'.pool lim st s = F_ro ∗ base.pool lim st s ∗ ⌜φ s⌝)
    (hpres : ∀ s0 sf, PureStepPreserved s0 sf → φ s0 → φ sf)
    (hok : subroutine_ok P initInnerAddr (aesInitInnerSpec M base storageAddr lim)) :
    subroutine_ok P initInnerAddr (aesInitInnerSpec M base' storageAddr lim) := by
  refine aesInitInner_lift_pool (fun s0 st m R hm => ?_) hok; rw [hB st s0] at hm
  have hm1 : m ⊨ ⌜φ s0⌝ ∗ (base.pool lim st s0 ∗ (F_ro ∗ R)) := Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  rw [satisfies_pure_sepConj] at hm1; rcases hm1 with ⟨hφ0, hm1⟩
  refine ⟨F_ro, hm1, fun sf m' R' hp hm' => ?_⟩; rw [hB st sf]
  exact Satisfies.mono (Entails.trans (Entails.pure_right (hpres s0 sf hp hφ0) (Entails.refl _))
    (Entails.of_eq (by sep_ac_rfl))) hm'

/-! ## 2. Borrowing `__libc.auxv` and `errno` from `mallocngBudgetPool` -/

class MallocngCoreAuxvBorrow (M : AllocCostModel) (I : MallocngCostModelIface M) : Prop where
  borrow_auxv :
    ∀ (γ : GhostName) (mAddrs : MallocngAddrs) (brkStart brk : BitVec 64)
      (st : M.σ) (ivs : List (BitVec 64 × Nat)) (m : Memory) (R : SepProp),
      m ⊨ I.CoreM γ mAddrs brkStart brk st ivs ∗ R →
      ∃ (auxvPtr : BitVec 64) (entries : List (BitVec 64 × BitVec 64)) (nullVal : BitVec 64) (R_core : SepProp),
        (∀ e ∈ entries, e.1 ≠ 0#64) ∧
        (m ⊨ (((mAddrs.libc + 0x08#64) ↦₆₄ᵣ auxvPtr) ∗ (auxvPtr ↦₆₄ᵣ* auxvEntryWords entries nullVal)) ∗ (R_core ∗ R)) ∧
        (∀ (m' : Memory) (R' : SepProp),
          m' ⊨ (((mAddrs.libc + 0x08#64) ↦₆₄ᵣ auxvPtr) ∗ (auxvPtr ↦₆₄ᵣ* auxvEntryWords entries nullVal)) ∗ (R_core ∗ R') →
          m' ⊨ I.CoreM γ mAddrs brkStart brk st ivs ∗ R')

private theorem auxvEntries_nonull {preEntries sufEntries : List (BitVec 64 × BitVec 64)} {randPtr : BitVec 64}
    (hpre : ∀ e ∈ preEntries, e.1 ≠ 0#64 ∧ e.1 ≠ 25#64) (hsuf : ∀ e ∈ sufEntries, e.1 ≠ 0#64 ∧ e.1 ≠ 25#64) :
    ∀ e ∈ preEntries ++ [(25#64, randPtr)] ++ sufEntries, e.1 ≠ 0#64 := by
  intro e he; simp only [List.mem_append, List.mem_singleton] at he
  rcases he with (he | rfl) | he; exacts [(hpre e he).1, by simp, (hsuf e he).1]

private theorem auxvEntryWords_split_eq (preEntries sufEntries : List (BitVec 64 × BitVec 64)) (randPtr nullVal : BitVec 64) :
    ((preEntries ++ [(25#64, randPtr)] ++ sufEntries ++ [(0#64, nullVal)]).flatMap fun (t, v) => [t, v]) =
      auxvEntryWords (preEntries ++ [(25#64, randPtr)] ++ sufEntries) nullVal := by
  simp [auxvEntryWords, List.append_assoc]

private theorem borrow_mallocngAuxvRoAt {auxvPtr : BitVec 64}
    {m : Memory} {R : SepProp} (hm : m ⊨ MallocngAuxvRoAt auxvPtr ∗ R) :
    ∃ (entries : List (BitVec 64 × BitVec 64)) (nullVal : BitVec 64) (R_aux : SepProp),
      (∀ e ∈ entries, e.1 ≠ 0#64) ∧ (m ⊨ (auxvPtr ↦₆₄ᵣ* auxvEntryWords entries nullVal) ∗ (R_aux ∗ R)) ∧
      (∀ (m' : Memory) (R' : SepProp),
        m' ⊨ (auxvPtr ↦₆₄ᵣ* auxvEntryWords entries nullVal) ∗ (R_aux ∗ R') → m' ⊨ MallocngAuxvRoAt auxvPtr ∗ R') := by
  unfold MallocngAuxvRoAt at hm ⊢
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨preEntries, sufEntries, randPtr, nullVal, secretBytes, hm⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm; rcases hm with ⟨hwf, hm⟩; rw [auxvEntryWords_split_eq] at hm
  refine ⟨preEntries ++ [(25#64, randPtr)] ++ sufEntries, nullVal,
    ((randPtr + 8#64) ↦ᵣ secretBytes),
    auxvEntries_nonull hwf.1 hwf.2.1, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm, fun m' R' hm' => ?_⟩
  refine Satisfies.mono (sepConj_mono_left
    (Entails.sepExists_right preEntries (Entails.sepExists_right sufEntries
      (Entails.sepExists_right randPtr (Entails.sepExists_right nullVal
        (Entails.sepExists_right secretBytes (Entails.pure_right hwf (Entails.refl _)))))))) ?_
  rw [auxvEntryWords_split_eq]; exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm'

private theorem borrow_mallocngCoreStInflightModeATrue {inflight : Nat} {γ : GhostName}
    {mAddrs : MallocngAddrs} {brkStart brk : BitVec 64} {liveCost peakCost : Nat} {st : MallocngSt} {m : Memory} {R : SepProp}
    (hm : m ⊨ MallocngCoreStInflightModeA true inflight γ mAddrs brkStart brk liveCost peakCost st ∗ R) :
    ∃ (entries : List (BitVec 64 × BitVec 64)) (nullVal : BitVec 64) (R_st : SepProp),
      (∀ e ∈ entries, e.1 ≠ 0#64) ∧
      (m ⊨ (((mAddrs.libc + 0x08#64) ↦₆₄ᵣ st.auxvPtr) ∗ (st.auxvPtr ↦₆₄ᵣ* auxvEntryWords entries nullVal)) ∗ (R_st ∗ R)) ∧
      (∀ (m' : Memory) (R' : SepProp),
        m' ⊨ (((mAddrs.libc + 0x08#64) ↦₆₄ᵣ st.auxvPtr) ∗ (st.auxvPtr ↦₆₄ᵣ* auxvEntryWords entries nullVal)) ∗ (R_st ∗ R') →
        m' ⊨ MallocngCoreStInflightModeA true inflight γ mAddrs brkStart brk liveCost peakCost st ∗ R') := by
  let CoreRest : SepProp :=
    ⌜MallocngWFInflight inflight mAddrs.base brkStart brk liveCost peakCost st⌝ ∗
      MallocngLiveAuth γ st.liveMap ∗ (mAddrs.ctx ↦ₛ st.ctx.toBytes) ∗ (mAddrs.lock ↦₃₂ 0#32) ∗
      (mAddrs.replaced ↦₃₂ 0#32) ∗ (mAddrs.aaReplaced ↦₃₂ 0#32) ∗ ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
      ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗ MappedSet st.masterDom (OwnedMappedByte st)
  have hEq : MallocngCoreStInflightModeA true inflight γ mAddrs brkStart brk liveCost peakCost st =
      MallocngAuxvRoAt st.auxvPtr ∗ (((mAddrs.libc + 0x08#64) ↦₆₄ᵣ st.auxvPtr) ∗ CoreRest) := by
    simp only [MallocngCoreStInflightModeA, MallocngAuxvPtrCell, MallocngAuxvStateRo, ↓reduceIte, CoreRest]; sep_ac_rfl
  rw [hEq, sepConj_assoc] at hm
  obtain ⟨entries, nullVal, R_aux, hnonull, hm_aux, hReasm⟩ := borrow_mallocngAuxvRoAt hm
  refine ⟨entries, nullVal, CoreRest ∗ R_aux, hnonull,
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm_aux, fun m' R' hm' => ?_⟩
  rw [hEq, sepConj_assoc, sepConj_assoc]
  exact hReasm m' (((mAddrs.libc + 0x08#64) ↦₆₄ᵣ st.auxvPtr) ∗ CoreRest ∗ R')
    (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm')

theorem mallocngCoreAuxvBorrow_fine : MallocngCoreAuxvBorrow fineCostModel fineCostModelIface := by
  constructor; intro γ mAddrs brkStart brk (b : FineBudget) ivs m R hm
  dsimp only [fineCostModelIface] at hm ⊢
  simp only [FineCoreImpl_eq, sepConj_comm (MallocngRoTablesA mAddrs), sepConj_assoc,
    sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨st, alignMap, liveCost, peakCost, hm⟩; dsimp only [FineCoreStInflightA] at hm
  obtain ⟨entries, nullVal, R_st, hnonull, hm_st, hReasm⟩ := borrow_mallocngCoreStInflightModeATrue
    (R := ⌜MallocngFineInv 0 b ivs alignMap st⌝ ∗ ghostMapAuth (fineAlignGam γ) alignMap ∗ MallocngRoTablesA mAddrs ∗ R)
    (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm)
  refine ⟨st.auxvPtr, entries, nullVal,
    MallocngRoTablesA mAddrs ∗ ⌜MallocngFineInv 0 b ivs alignMap st⌝ ∗ ghostMapAuth (fineAlignGam γ) alignMap ∗ R_st,
    hnonull, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm_st, fun m' R' hm' => ?_⟩
  rw [FineCoreImpl_eq]
  exact Satisfies.mono (Entails.trans (by dsimp only [FineCoreStInflightA]; exact Entails.of_eq (by sep_ac_rfl))
    (sepConj_mono_left (sepConj_mono_right (Entails.sepExists_right st
      (Entails.sepExists_right alignMap (Entails.sepExists_right liveCost
        (Entails.sepExists_right peakCost (Entails.refl _))))))))
    (hReasm m' (⌜MallocngFineInv 0 b ivs alignMap st⌝ ∗ ghostMapAuth (fineAlignGam γ) alignMap ∗
      MallocngRoTablesA mAddrs ∗ R') (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm'))

instance instMallocngCoreAuxvBorrowFine : MallocngCoreAuxvBorrow fineCostModel fineCostModelIface :=
  mallocngCoreAuxvBorrow_fine

/-- Discharge `features_aes::init_get::init_inner` against `mallocngRustCliAllocBudget`. -/
theorem aesInitInner_mallocng_ok {M : AllocCostModel} {I : MallocngCostModelIface M}
    [hAuxv : MallocngCoreAuxvBorrow M I] (hS : MallocngCostModelSound M I)
    (γ : GhostName) (mpl : Obj.MultiPlacement) (tp brkStart : BitVec 64) (lim : BudgetLimits) {P : Program}
    {initInnerAddr getauxvalHwcapAddr getauxvalAddr errnoLocationAddr storageAddr : BitVec 64}
    (hCode : AesInitInnerCode P initInnerAddr getauxvalHwcapAddr getauxvalAddr
      errnoLocationAddr (mallocngAddrsOfPlacement mpl).libc storageAddr) :
    subroutine_ok P initInnerAddr
      (aesInitInnerSpec M (mallocngRustCliAllocBudget M I hS γ mpl tp brkStart) storageAddr lim) := by
  let mAddrs := mallocngAddrsOfPlacement mpl; have hRaw := aesInitInnerRaw_ok hCode
  apply subroutine_ok.of_codeLoaded; rintro ⟨oldVal, st⟩ R s0 hpc hrun hpre hsp _
  dsimp only [aesInitInnerSpec, mallocngRustCliAllocBudget, mallocngRustCliAllocBudgetAt, mallocngBudgetPool] at hpre
  rw [← sepConj_assoc (storageAddr ↦₈ oldVal), sepConj_comm (storageAddr ↦₈ oldVal),
      mallocngBudgetPoolAt_split_runtime hS γ mAddrs tp brkStart lim st s0] at hpre
  simp only [sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists] at hpre
  rcases hpre with ⟨staticIvs, ivs, hpre⟩; rw [satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hInv0, htp0, hbrkS0⟩, hpre⟩; dsimp only [MallocngRuntime] at hpre
  rw [← sepConj_assoc (I.CoreM _ _ _ _ _ _), sepConj_comm (I.CoreM _ _ _ _ _ _)] at hpre
  simp only [sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists] at hpre
  rcases hpre with ⟨errno0, hpre⟩
  obtain ⟨auxvPtr, entries, nullVal, R_core, hnonull, hm_aux, hReasm⟩ :=
    hAuxv.borrow_auxv γ mAddrs brkStart s0.brk st ivs s0.mem _ (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre)
  let R_frame : SepProp := R_core ∗ ((mAddrs.libc + 3#64) ↦₈ 0#8) ∗ ((mAddrs.libc + 48#64) ↦₆₄ 4096#64) ∗ R
  have hpre_raw : s0.mem ⊨ (aesInitInnerRawSpec mAddrs.libc storageAddr).pre
      (oldVal, auxvPtr, entries, nullVal, errno0) s0 ∗ R_frame := by
    dsimp only [aesInitInnerRawSpec, R_frame]; rw [htp0, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hnonull, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm_aux⟩
  refine (hRaw.to_outcome (oldVal, auxvPtr, entries, nullVal, errno0) R_frame s0 hpc hrun hpre_raw hsp
    ).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [aesInitInnerRawSpec, R_frame] at hpost; rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hb, hx0, hpure⟩, hm_f⟩; have hvm : VmPreserved s0 sf := hpure.vmPreserved
    have hInv_f : mallocngBudgetPoolInv lim staticIvs ivs sf := by
      rwa [mallocngBudgetPoolInv_transport_mem hvm.toVmMemPreserved]
    rw [htp0] at hm_f
    have hm_core := hReasm sf.mem
      (((tp - 0xa4#64) ↦₃₂ auxvLookupErrno 16#64 entries errno0) ∗ ((mAddrs.libc + 3#64) ↦₈ 0#8) ∗
        ((mAddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
        (storageAddr ↦₈ aesHwcapDetectByte (auxvLookupVal 16#64 entries)) ∗ stackFrameAt s0.sp 0x30 ∗ R)
      (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm_f)
    rw [← hvm.1.2.1] at hm_core
    dsimp only [aesInitInnerSpec, mallocngRustCliAllocBudget, mallocngRustCliAllocBudgetAt, mallocngBudgetPool]
    rw [sepExists_sepConj_left]; refine (satisfies_sepExists _ _).mpr ⟨aesHwcapDetectByte (auxvLookupVal 16#64 entries), ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨⟨hb, hx0, hpure⟩, ?_⟩
    rw [mallocngBudgetPoolAt_split_runtime hS γ mAddrs tp brkStart lim st sf]; dsimp only [MallocngRuntime]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    have hInvAll : mallocngBudgetPoolInv lim staticIvs ivs sf ∧ sf.tpidrEl0 = tp ∧ sf.brkStart = brkStart :=
      ⟨hInv_f, hvm.1.2.2.trans htp0, hvm.1.1.trans hbrkS0⟩
    refine ⟨auxvLookupErrno 16#64 entries errno0, staticIvs, ivs, Satisfies.mono
      (Entails.trans (Entails.pure_right hInvAll (Entails.refl _)) (Entails.of_eq (by sep_ac_rfl))) hm_core⟩
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

/-! ## 3. Storage-Free Shared-Pool Allocator (`*HookNoAes*`) -/

@[expose] def mallocngHookNoAesBudgetPool (M : AllocCostModel) (I : MallocngCostModelIface M)
    (γ : GhostName) (mpl : Obj.MultiPlacement) (tp brkStart : BitVec 64) (lim : BudgetLimits) (st : M.σ) (s : State) : SepProp :=
  VerifiedLibraries.mallocngLib.codeRO mpl ∗ mallocngBudgetPool M I γ mpl tp brkStart lim st s ∗ ⌜lim.enforced = true → CodeBlocksPermRX mpl s⌝

theorem mallocngHookNoAesBudgetPool_transport (M : AllocCostModel) (I : MallocngCostModelIface M)
    (γ : GhostName) (mpl : Obj.MultiPlacement) (tp brkStart : BitVec 64) (lim : BudgetLimits) (st : M.σ) {s s' : State} (hvm : VmPreserved s s') :
    mallocngHookNoAesBudgetPool M I γ mpl tp brkStart lim st s' = mallocngHookNoAesBudgetPool M I γ mpl tp brkStart lim st s := by
  simp only [mallocngHookNoAesBudgetPool, mallocngBudgetPool,
    mallocngBudgetPoolAt_transport_mem M I γ (mallocngAddrsOfPlacement mpl) tp brkStart lim st hvm.toVmMemPreserved,
    codeBlocksPermRX_of_perm_eq (mpl := mpl) hvm.toVmMemPreserved.2.2]

theorem mallocngHookNoAesBudgetPool_zero_transport (M : AllocCostModel) (I : MallocngCostModelIface M)
    (γ : GhostName) (mpl : Obj.MultiPlacement) (tp brkStart : BitVec 64) (st : M.σ) {s s' : State} (hp : PoolPreserved s s') :
    mallocngHookNoAesBudgetPool M I γ mpl tp brkStart zeroBudgetLimits st s' =
      mallocngHookNoAesBudgetPool M I γ mpl tp brkStart zeroBudgetLimits st s := by
  have hrx : ∀ u : State, (zeroBudgetLimits.enforced = true → CodeBlocksPermRX mpl u) = True :=
    fun _ => propext ⟨fun _ => trivial, fun _ h => Bool.noConfusion h⟩
  simp only [mallocngHookNoAesBudgetPool, mallocngBudgetPool,
    mallocngBudgetPoolAt_zero_transport M I γ (mallocngAddrsOfPlacement mpl) tp brkStart st hp, hrx]

@[expose] def mallocngHookNoAesRustCliAllocBudget (M : AllocCostModel) (I : MallocngCostModelIface M)
    (hS : MallocngCostModelSound M I) (γ : GhostName) (mpl : Obj.MultiPlacement) (tp brkStart : BitVec 64) : RustCliAllocBudget M where
  pool := mallocngHookNoAesBudgetPool M I γ mpl tp brkStart
  live := mallocngLiveM M I γ; block_valid := (mallocngRustCliAllocBudget M I hS γ mpl tp brkStart).block_valid
  pool_transport lim st _ _ hvm := mallocngHookNoAesBudgetPool_transport M I γ mpl tp brkStart lim st hvm
  pool_zero_transport st _ _ hp := mallocngHookNoAesBudgetPool_zero_transport M I γ mpl tp brkStart st hp

@[expose] noncomputable def fineHookNoAesRustCliAllocBudget
    (γ : GhostName) (mpl : Obj.MultiPlacement) (tp brkStart : BitVec 64) : RustCliAllocBudget fineCostModel :=
  mallocngHookNoAesRustCliAllocBudget fineCostModel fineCostModelIface fineCostModelSound γ mpl tp brkStart
@[simp] theorem mallocngHookNoAesRustCliAllocBudget_repAlloc (M : AllocCostModel) (I : MallocngCostModelIface M)
    (hS : MallocngCostModelSound M I) (γ : GhostName) (mpl : Obj.MultiPlacement) (tp brkStart : BitVec 64) :
    (mallocngHookNoAesRustCliAllocBudget M I hS γ mpl tp brkStart).repAlloc = (mallocngRustCliAllocBudget M I hS γ mpl tp brkStart).repAlloc := rfl
@[simp] theorem fineHookNoAesRustCliAllocBudget_repAlloc (γ : GhostName) (mpl : Obj.MultiPlacement) (tp brkStart : BitVec 64) :
    (fineHookNoAesRustCliAllocBudget γ mpl tp brkStart).repAlloc = (fineRustCliAllocBudget γ mpl tp brkStart).repAlloc := rfl

private theorem subroutine_ok_lift_codeRO_rx {α : Type} {mpl : Obj.MultiPlacement}
    {lim : BudgetLimits} {P : Program} {entry : BitVec 64} {spec₀ spec₁ : Spec α} (h : subroutine_ok P entry spec₀)
    (hpre_eq : ∀ x s0, spec₁.pre x s0 = ⌜lim.enforced = true → CodeBlocksPermRX mpl s0⌝ ∗ (spec₀.pre x s0 ∗ VerifiedLibraries.mallocngLib.codeRO mpl))
    (hpost_imp : ∀ x s0 sf, (lim.enforced = true → CodeBlocksPermRX mpl sf) → spec₀.post x s0 sf ∗ VerifiedLibraries.mallocngLib.codeRO mpl ⊢ spec₁.post x s0 sf)
    (hpan : ∀ x s0 sf, spec₀.onPanic x s0 sf = ⌜False⌝) (hex : ∀ x c s0 sf, spec₀.onExit x c s0 sf = ⌜False⌝)
    (hoom_eq : spec₁.onOom = spec₀.onOom) : subroutine_ok P entry spec₁ := by
  apply subroutine_ok.of_codeLoaded; intro x R s0 hpc hrun hpre hsp _
  have hpre1 : s0.mem ⊨ ⌜lim.enforced = true → CodeBlocksPermRX mpl s0⌝ ∗ (spec₀.pre x s0 ∗ (VerifiedLibraries.mallocngLib.codeRO mpl ∗ R)) := by
    rw [hpre_eq x s0] at hpre; exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre1; obtain ⟨hrx0, hpre₀⟩ := hpre1
  refine (h.to_outcome x (VerifiedLibraries.mallocngLib.codeRO mpl ∗ R) s0 hpc hrun hpre₀ hsp).mono_outcome_steps fun sf hsteps hout => ?_
  have hrxf : lim.enforced = true → CodeBlocksPermRX mpl sf := fun henf => codeBlocksPermRX_of_keepsFrozen (hrx0 henf) hsteps.keepsFrozen
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨c, _, he⟩ | ⟨ho, hoom⟩
  · rw [← sepConj_assoc] at hpost; exact Or.inl ⟨hret, hcc, Satisfies.mono (sepConj_mono_left (hpost_imp x s0 sf hrxf)) hpost⟩
  · rw [hpan x s0 sf] at hp; exact False.elim (not_satisfies_false_sepConj hp)
  · rw [hex x c s0 sf] at he; exact False.elim (not_satisfies_false_sepConj he)
  · refine Or.inr (Or.inr (Or.inr ⟨ho, ?_⟩)); rw [hoom_eq]
    exact Satisfies.of_sep_right (P := VerifiedLibraries.mallocngLib.codeRO mpl) (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hoom)

private theorem hookNoAes_pool_eq {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) {γ : GhostName} {mpl : Obj.MultiPlacement} {tp brkStart : BitVec 64} {lim : BudgetLimits} (st' : M.σ) (u : State) :
    (mallocngHookNoAesRustCliAllocBudget M I hS γ mpl tp brkStart).pool lim st' u =
      VerifiedLibraries.mallocngLib.codeRO mpl ∗ (mallocngRustCliAllocBudget M I hS γ mpl tp brkStart).pool lim st' u ∗
        ⌜lim.enforced = true → CodeBlocksPermRX mpl u⌝ := rfl
private theorem hookNoAes_live_eq {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) {γ : GhostName} {mpl : Obj.MultiPlacement} {tp brkStart : BitVec 64} :
    (mallocngHookNoAesRustCliAllocBudget M I hS γ mpl tp brkStart).live = (mallocngRustCliAllocBudget M I hS γ mpl tp brkStart).live := rfl

theorem mallocngHookNoAesAllocBudget_of_raw {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) {γ : GhostName} {mpl : Obj.MultiPlacement}
    {tp brkStart : BitVec 64} {lim : BudgetLimits} {zeroed : Bool} {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry (rustCliAllocBudgetSpecBase M (mallocngRustCliAllocBudget M I hS γ mpl tp brkStart) lim zeroed)) :
    subroutine_ok P entry (rustCliAllocBudgetSpecBase M (mallocngHookNoAesRustCliAllocBudget M I hS γ mpl tp brkStart) lim zeroed) :=
  subroutine_ok_lift_codeRO_rx (mpl := mpl) (lim := lim) h
    (fun ⟨_, _, _⟩ _ => by dsimp only [rustCliAllocBudgetSpecBase]; rw [hookNoAes_pool_eq hS (mpl := mpl) (lim := lim)]; sep_ac_rfl)
    (fun ⟨_, _, _⟩ _ _ hrxf => by
      dsimp only [rustCliAllocBudgetSpecBase]; rw [hookNoAes_pool_eq hS (mpl := mpl) (lim := lim), hookNoAes_live_eq hS (mpl := mpl)]
      exact Entails.trans (Entails.pure_right hrxf (Entails.refl _)) (Entails.of_eq (by sep_ac_rfl)))
    (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) rfl

theorem mallocngHookNoAesDeallocBudget_of_raw {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) {γ : GhostName} {mpl : Obj.MultiPlacement}
    {tp brkStart : BitVec 64} {lim : BudgetLimits} {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry (rustCliDeallocBudgetSpecBase M (mallocngRustCliAllocBudget M I hS γ mpl tp brkStart) lim)) :
    subroutine_ok P entry (rustCliDeallocBudgetSpecBase M (mallocngHookNoAesRustCliAllocBudget M I hS γ mpl tp brkStart) lim) :=
  subroutine_ok_lift_codeRO_rx (mpl := mpl) (lim := lim) h
    (fun ⟨_, _, _, _⟩ _ => by dsimp only [rustCliDeallocBudgetSpecBase]; rw [hookNoAes_pool_eq hS (mpl := mpl) (lim := lim), hookNoAes_live_eq hS (mpl := mpl)]; sep_ac_rfl)
    (fun ⟨_, _, _, _⟩ _ _ hrxf => by
      dsimp only [rustCliDeallocBudgetSpecBase]; rw [hookNoAes_pool_eq hS (mpl := mpl) (lim := lim)]
      exact Entails.trans (Entails.pure_right hrxf (Entails.refl _)) (Entails.of_eq (by sep_ac_rfl)))
    (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) rfl

theorem mallocngHookNoAesReallocBudget_of_raw {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) {γ : GhostName} {mpl : Obj.MultiPlacement}
    {tp brkStart : BitVec 64} {lim : BudgetLimits} {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry (rustCliReallocBudgetSpecBase M (mallocngRustCliAllocBudget M I hS γ mpl tp brkStart) lim)) :
    subroutine_ok P entry (rustCliReallocBudgetSpecBase M (mallocngHookNoAesRustCliAllocBudget M I hS γ mpl tp brkStart) lim) :=
  subroutine_ok_lift_codeRO_rx (mpl := mpl) (lim := lim) h
    (fun ⟨_, _, _, _, _, _⟩ _ => by dsimp only [rustCliReallocBudgetSpecBase]; rw [hookNoAes_pool_eq hS (mpl := mpl) (lim := lim), hookNoAes_live_eq hS (mpl := mpl)]; sep_ac_rfl)
    (fun ⟨_, _, _, _, _, _⟩ _ _ hrxf => by
      dsimp only [rustCliReallocBudgetSpecBase]; rw [hookNoAes_pool_eq hS (mpl := mpl) (lim := lim), hookNoAes_live_eq hS (mpl := mpl)]
      exact Entails.trans (Entails.pure_right hrxf (Entails.refl _)) (Entails.of_eq (by sep_ac_rfl)))
    (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) rfl

theorem mallocngHookNoAesRustCliAllocBudgetEntries_of_raw {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hS : MallocngCostModelSound M I) {γ : GhostName} {mpl : Obj.MultiPlacement} {tp brkStart : BitVec 64} {P : Program} {addrs : RustAllocAddrs}
    (h : RustCliAllocBudgetEntriesBase M (mallocngRustCliAllocBudget M I hS γ mpl tp brkStart) P addrs) :
    RustCliAllocBudgetEntriesBase M (mallocngHookNoAesRustCliAllocBudget M I hS γ mpl tp brkStart) P addrs :=
  ⟨fun lim => mallocngHookNoAesAllocBudget_of_raw hS (h.alloc lim),
   fun lim => mallocngHookNoAesDeallocBudget_of_raw hS (h.dealloc lim),
   fun lim => mallocngHookNoAesReallocBudget_of_raw hS (h.realloc lim)⟩

theorem fineHookNoAesRustCliAllocBudgetEntries {P : Program} {mpl : Obj.MultiPlacement}
    (hP : ProgContainsMallocng P mpl) (γ : GhostName) (tp brkStart : BitVec 64) {rdlAddrs : RustAllocAddrs} {memcpyAddr : BitVec 64}
    (hShims : RustStdRdlShimCode P rdlAddrs.toRustStd (mallocngPlacedCAddrs mpl) memcpyAddr) (hMemcpy : subroutine_ok P memcpyAddr allocMemcpyVmSpec) :
    RustCliAllocBudgetEntriesBase fineCostModel (fineHookNoAesRustCliAllocBudget γ mpl tp brkStart) P rdlAddrs :=
  mallocngHookNoAesRustCliAllocBudgetEntries_of_raw fineCostModelSound (fineRustCliAllocBudgetEntries hP γ tp brkStart hShims hMemcpy)

theorem fineHookNoAesRustCliAllocBudgetEntries_thunks {P : Program} {mpl : Obj.MultiPlacement}
    (hP : ProgContainsMallocng P mpl) (γ : GhostName) (tp brkStart : BitVec 64) {thunkAddrs rdlAddrs : RustAllocAddrs} {memcpyAddr : BitVec 64}
    (hThunks : RustStdThunkCode P thunkAddrs.toRustStd rdlAddrs.toRustStd)
    (hShims : RustStdRdlShimCode P rdlAddrs.toRustStd (mallocngPlacedCAddrs mpl) memcpyAddr) (hMemcpy : subroutine_ok P memcpyAddr allocMemcpyVmSpec) :
    RustCliAllocBudgetEntriesBase fineCostModel (fineHookNoAesRustCliAllocBudget γ mpl tp brkStart) P thunkAddrs :=
  mallocngHookNoAesRustCliAllocBudgetEntries_of_raw fineCostModelSound (fineRustCliAllocBudgetEntries_thunks hP γ tp brkStart hThunks hShims hMemcpy)

theorem fineHookNoAesRdlAllocZeroed_budget_placed_ok {P : Program} {mpl : Obj.MultiPlacement}
    (hP : ProgContainsMallocng P mpl) (γ : GhostName) (tp brkStart allocZeroedAddr memsetAddr : BitVec 64) (lim : BudgetLimits)
    (hCode : hasInstrs P allocZeroedAddr (rdlAllocZeroedInstrs allocZeroedAddr
      (VerifiedLibraries.mallocngLib.fnAddr mpl "calloc") (mallocngPlacedCAddrs mpl).posixMemalign memsetAddr))
    (hMemset : subroutine_ok P memsetAddr allocMemsetVmSpec) :
    subroutine_ok P allocZeroedAddr (rustAllocZeroedBudgetSpecBase fineCostModel (fineHookNoAesRustCliAllocBudget γ mpl tp brkStart) lim) :=
  mallocngHookNoAesAllocBudget_of_raw fineCostModelSound (fineRdlAllocZeroed_budget_placed_ok hP γ tp brkStart allocZeroedAddr memsetAddr lim hCode hMemset)

theorem fineHookNoAesRustCliAllocZeroedBudget_thunk_ok {P : Program} {mpl : Obj.MultiPlacement}
    (hP : ProgContainsMallocng P mpl) (γ : GhostName) (tp brkStart thunkAddr rdlAddr memsetAddr : BitVec 64)
    (lim : BudgetLimits) (hThunk : hasInstrs P thunkAddr [ .b (rdlAddr - thunkAddr) ])
    (hCode : hasInstrs P rdlAddr (rdlAllocZeroedInstrs rdlAddr
      (VerifiedLibraries.mallocngLib.fnAddr mpl "calloc") (mallocngPlacedCAddrs mpl).posixMemalign memsetAddr))
    (hMemset : subroutine_ok P memsetAddr allocMemsetVmSpec) :
    subroutine_ok P thunkAddr (rustAllocZeroedBudgetSpecBase fineCostModel (fineHookNoAesRustCliAllocBudget γ mpl tp brkStart) lim) :=
  mallocngHookNoAesAllocBudget_of_raw fineCostModelSound (fineRustCliAllocZeroedBudget_thunk_ok hP γ tp brkStart thunkAddr rdlAddr memsetAddr lim hThunk hCode hMemset)

theorem aesInitInner_mallocngHookNoAes_ok {M : AllocCostModel} {I : MallocngCostModelIface M}
    [MallocngCoreAuxvBorrow M I] (hS : MallocngCostModelSound M I)
    (γ : GhostName) (mpl : Obj.MultiPlacement) (tp brkStart : BitVec 64) (lim : BudgetLimits) {P : Program}
    {initInnerAddr getauxvalHwcapAddr getauxvalAddr errnoLocationAddr storageAddr : BitVec 64}
    (hCode : AesInitInnerCode P initInnerAddr getauxvalHwcapAddr getauxvalAddr
      errnoLocationAddr (mallocngAddrsOfPlacement mpl).libc storageAddr) :
    subroutine_ok P initInnerAddr (aesInitInnerSpec M (mallocngHookNoAesRustCliAllocBudget M I hS γ mpl tp brkStart) storageAddr lim) :=
  aesInitInner_lift_frame_pure (VerifiedLibraries.mallocngLib.codeRO mpl)
    (fun s => lim.enforced = true → CodeBlocksPermRX mpl s) (fun _ _ => rfl)
    (fun _ _ hp h0 he => by dsimp only [CodeBlocksPermRX]; rw [codeBlocksPermRX_of_perm_eq (mpl := mpl) hp.vmPreserved.toVmMemPreserved.2.2]; exact h0 he)
    (aesInitInner_mallocng_ok hS γ mpl tp brkStart lim hCode)

/-! ## 4. `PoolAesInitSplit` Instances (`mallocngHook`, `fineHook`, `liftPure`, `withFds`) -/

theorem mallocngHookBudgetPool_eq_split (M : AllocCostModel) (I : MallocngCostModelIface M)
    (γ : GhostName) (mpl : Obj.MultiPlacement) (tp brkStart : BitVec 64) (lim : BudgetLimits) (st : M.σ) (s : State) :
    mallocngHookBudgetPool M I γ mpl tp brkStart lim st s =
      ∃∗ v : BitVec 8, ((brkStart - 8160#64) ↦₈ v) ∗ mallocngHookNoAesBudgetPool M I γ mpl tp brkStart lim st s := by
  simp only [mallocngHookBudgetPool, mallocngHookNoAesBudgetPool, aesStorageCell, sepExists_sepConj_left, sepExists_sepConj_right]
  exact congrArg sepExists (funext fun _ => by sep_ac_rfl)

instance instPoolAesInitSplitMallocngHook {M : AllocCostModel}
    {I : MallocngCostModelIface M} [MallocngCoreAuxvBorrow M I] (hS : MallocngCostModelSound M I)
    (γ : GhostName) (mpl : Obj.MultiPlacement) (tp brkStart : BitVec 64) :
    PoolAesInitSplit (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart) (brkStart - 8160#64) :=
  ⟨mallocngHookNoAesRustCliAllocBudget M I hS γ mpl tp brkStart, (mallocngAddrsOfPlacement mpl).libc, rfl,
   mallocngHookBudgetPool_eq_split M I γ mpl tp brkStart,
   fun lim hCode => aesInitInner_mallocngHookNoAes_ok hS γ mpl tp brkStart lim hCode⟩

noncomputable instance instPoolAesInitSplitFineHook (γ : GhostName) (mpl : Obj.MultiPlacement) (tp brkStart : BitVec 64) :
    PoolAesInitSplit (fineHookRustCliAllocBudget γ mpl tp brkStart) (brkStart - 8160#64) :=
  instPoolAesInitSplitMallocngHook fineCostModelSound γ mpl tp brkStart

theorem liftPure_pool_eq {M : AllocCostModel} {A A' : RustCliAllocBudget M} {storageAddr : BitVec 64}
    (h : PoolAesInitSplit A storageAddr) (base' : RustCliAllocBudget M) (φ : BudgetLimits → State → Prop)
    (hA : ∀ lim st s, A'.pool lim st s = A.pool lim st s ∗ ⌜φ lim s⌝)
    (hB : ∀ lim st s, base'.pool lim st s = h.base.pool lim st s ∗ ⌜φ lim s⌝) (lim : BudgetLimits) (st : M.σ) (s : State) :
    A'.pool lim st s = ∃∗ v : BitVec 8, (storageAddr ↦₈ v) ∗ base'.pool lim st s := by
  rw [hA lim st s, h.pool_eq lim st s, sepExists_sepConj_left]
  exact congrArg sepExists (funext fun _ => by rw [hB lim st s]; sep_ac_rfl)

theorem liftPure_initInner_ok {M : AllocCostModel} {A : RustCliAllocBudget M} {storageAddr : BitVec 64}
    (h : PoolAesInitSplit A storageAddr) (base' : RustCliAllocBudget M) (φ : BudgetLimits → State → Prop)
    (hB : ∀ lim st s, base'.pool lim st s = h.base.pool lim st s ∗ ⌜φ lim s⌝)
    (hpres : ∀ lim s0 sf, PureStepPreserved s0 sf → φ lim s0 → φ lim sf)
    {P : Program} {initInnerAddr getauxvalHwcapAddr getauxvalAddr errnoLocationAddr : BitVec 64} (lim : BudgetLimits)
    (hCode : AesInitInnerCode P initInnerAddr getauxvalHwcapAddr getauxvalAddr errnoLocationAddr h.libcAddr storageAddr) :
    subroutine_ok P initInnerAddr (aesInitInnerSpec M base' storageAddr lim) :=
  aesInitInner_lift_frame_pure emp (φ lim) (fun st s => by rw [hB lim st s, emp_sepConj]) (hpres lim) (h.initInner_ok lim hCode)

@[expose, instance_reducible] def PoolAesInitSplit.liftPure {M : AllocCostModel} {A A' : RustCliAllocBudget M} {storageAddr : BitVec 64}
    (h : PoolAesInitSplit A storageAddr) (base' : RustCliAllocBudget M) (φ : BudgetLimits → State → Prop)
    (hlive : A'.live = base'.live) (hA : ∀ lim st s, A'.pool lim st s = A.pool lim st s ∗ ⌜φ lim s⌝)
    (hB : ∀ lim st s, base'.pool lim st s = h.base.pool lim st s ∗ ⌜φ lim s⌝)
    (hpres : ∀ lim s0 sf, PureStepPreserved s0 sf → φ lim s0 → φ lim sf) : PoolAesInitSplit A' storageAddr :=
  ⟨base', h.libcAddr, hlive, liftPure_pool_eq h base' φ hA hB, fun lim hCode => liftPure_initInner_ok h base' φ hB hpres lim hCode⟩

@[expose] def FdsGe3Closed (fs : FsState) : Prop := ∀ fd : Nat, 3 ≤ fd → fd < 2 ^ 31 → fs.fds (BitVec.ofNat 64 fd) = none
theorem fdsGe3Closed_iff_of_fdsHiFrame {s s' : State} (hfr : FdsHiFrame s s') : FdsGe3Closed s'.fs ↔ FdsGe3Closed s.fs :=
  ⟨fun h fd hlo hhi => (hfr fd hlo hhi).symm.trans (h fd hlo hhi), fun h fd hlo hhi => (hfr fd hlo hhi).trans (h fd hlo hhi)⟩

theorem withFdsOf_pool_transport {M : AllocCostModel} (hfr : ∀ s s' : State, VmPreserved s s' → FdsHiFrame s s')
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) {s s' : State} (hvm : VmPreserved s s') :
    (if lim.enforced then (⌜FdsGe3Closed s'.fs⌝ ∗ A.pool lim st s') else A.pool lim st s') =
      if lim.enforced then (⌜FdsGe3Closed s.fs⌝ ∗ A.pool lim st s) else A.pool lim st s := by
  cases lim.enforced <;> simp [fdsGe3Closed_iff_of_fdsHiFrame (hfr s s' hvm), A.pool_transport lim st s s' hvm]

@[expose] def withFdsOf {M : AllocCostModel}
    (hfr : ∀ s s' : State, VmPreserved s s' → FdsHiFrame s s') (A : RustCliAllocBudget M) : RustCliAllocBudget M where
  pool lim st s := if lim.enforced then (⌜FdsGe3Closed s.fs⌝ ∗ A.pool lim st s) else A.pool lim st s
  live := A.live; block_valid := A.block_valid
  pool_transport lim st _ _ hvm := withFdsOf_pool_transport hfr A lim st hvm
  pool_zero_transport st s s' hp := A.pool_zero_transport st s s' hp

@[expose] def withFds {M : AllocCostModel} (A : RustCliAllocBudget M) : RustCliAllocBudget M := withFdsOf (fun _ _ h => h.fdsHiFrame) A
@[simp] theorem withFds_repAlloc {M : AllocCostModel} (A : RustCliAllocBudget M) : (withFds A).repAlloc = A.repAlloc := rfl

theorem withFds_pool_eq_pure {M : AllocCostModel} (B : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) :
    (withFds B).pool lim st s = B.pool lim st s ∗ ⌜lim.enforced = true → FdsGe3Closed s.fs⌝ := by
  dsimp only [withFds, withFdsOf]; cases lim.enforced <;> simp [sepConj_comm]

instance instPoolAesInitSplitWithFds {M : AllocCostModel} {A : RustCliAllocBudget M}
    {storageAddr : BitVec 64} [h : PoolAesInitSplit A storageAddr] : PoolAesInitSplit (withFds A) storageAddr :=
  h.liftPure (withFds h.base) (fun lim s => lim.enforced = true → FdsGe3Closed s.fs)
    h.live_eq (withFds_pool_eq_pure A) (withFds_pool_eq_pure h.base)
    fun _ _ _ hp h0 he => (fdsGe3Closed_iff_of_fdsHiFrame hp.vmPreserved.fdsHiFrame).mpr (h0 he)

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.GetauxvalHwcap
