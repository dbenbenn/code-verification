/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtPlacedObj -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtRow.Externs -- proof-setup: allow-public-import
import LibsignalBinary.Heap.MuslMemOpsRunsTo
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.PrePanicMngLift
import ProofLib.ProgramReflection
meta import ProofLib.ProgramReflection

/-!
# `withExecFrozenBudget` & `f3TrialRxProg` → `c2FmtProgTrap lr` Callee Lifts (`CliFmtRow.TrapStubs`)
-/

set_option autoImplicit false
set_option maxRecDepth 4000000

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtRow.TrapStubs

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection ProofLib.SepLogic
open ProofLib.StdStartup (checkWordsAt hasInstrs hasWords_of_wordTree)
open CryptoVerification.RustHeap (allocHookStack)
open VerifiedLibraries (mallocngLib)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement)
open VerifiedLibraries.Mallocng.Proofs (memcpySymWords)
open VerifiedLibraries.RustStd
  (budgetAllocShimSpec budgetMemcpySpec fmtSrcBytes mallocngPlacedCAddrs rustBudgetAllocSpec
   rustBudgetReallocSpec)
open CryptoVerification.SignalSession (cliElfBytes)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget rustCliAllocBudgetSpecBase
   rustCliReallocBudgetSpecBase zeroBudgetLimits)
open LibsignalBinary.Heap.Fine
  (f3MallocngMpl f3RdlAddrs f3RxWordCount f3StdLayout f3StubAddrs fineCostModel fineCostModelIface
   fineHookRustCliAllocBudget)
open LibsignalBinary.Heap.MuslMemOpsRunsTo
  (BlockExternFree codeLoaded_pureWordsProg_of_hasWords
   subroutine_ok_lift_pureWords_blockExternFree)
open LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtPlacedObj
  (PoolMemTransport budgetAllocShim_of_hasInstrs budgetMemcpy_all_of_hasWords
   rustBudgetAlloc_of_cliBase rustBudgetRealloc_of_cliBase toRustAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (ExecFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.AesCbc
  (keepRxSeg keepRxSeg_eq_lt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtRow.Code
  (rxCode_of_c2FmtProg_codeLoaded)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtRow.Defs
  (c2FmtProg c2FmtProgTrap c2FmtProgTrap_codeLoaded_iff c2FmtProgTrap_svc)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtRow.Externs
  (c2FmtProgTrap_blockExternFree_of_pre_lib2 c2FmtProgTrap_externAt_none_of_keepRxSeg_not_panic)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.PrePanicMngLift
  (c2_alloc_withExecFrozen_ok c2_realloc_withExecFrozen_ok f3PrePanicRxProg
   f3PrePanicRxProg_codeLoaded_of_f3Trial f3PrePanicWordCount keepPrePanic)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
  (isLinkedPanicAddr isLinkedPanicAddr_false_of_lt)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
  (f3RxSegBase f3TrialRxProg f3TrialRxProg_base f3TrialRxProg_stubs
   f3TrialRxProg_svc f3TrialRxProg_symbols f3TrialRxWordTree f3TrialRxWordTree_eq
   f3TrialRxWordTree_size)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen
  (c2FirstExternStubAddr wp4MemcpyRealAddr wp4NoShimV2Addr)

attribute [local irreducible] c2FmtProg c2FmtProgTrap f3TrialRxProg

/-- Enrich `A.pool lim st s` with `⌜lim ≠ zeroBudgetLimits → ExecFrozen s.mem⌝` so allocator
    calls inside `c2FmtProgTrap lr` can strip to `f3TrialRxProg` and lift back to unstripped
    memory while preserving `ExecFrozen`. -/
@[expose] def withExecFrozenBudget {M : AllocCostModel} (A : RustCliAllocBudget M) :
    RustCliAllocBudget M where
  pool lim st s := A.pool lim st s ∗ ⌜lim ≠ zeroBudgetLimits → ExecFrozen s.mem⌝
  live := A.live
  block_valid := A.block_valid
  pool_transport lim st s s' hvm := by
    have hp := A.pool_transport lim st s s' hvm
    have hfr : ExecFrozen s'.mem = ExecFrozen s.mem := by
      apply propext
      exact ⟨fun h => ExecFrozen.of_perm_eq h (fun a => (hvm.perm_eq a).symm),
             fun h => ExecFrozen.of_perm_eq h hvm.perm_eq⟩
    simp only [hp, hfr]
  pool_zero_transport st s s' hp := by
    have hp0 := A.pool_zero_transport st s s' hp
    simp only [hp0, ne_eq, not_true_eq_false, IsEmpty.forall_iff]

theorem withExecFrozenBudget_repAlloc {M : AllocCostModel} (A : RustCliAllocBudget M) :
    (withExecFrozenBudget A).repAlloc = A.repAlloc := rfl

instance instPoolMemTransportWithExecFrozen {M : AllocCostModel} (A : RustCliAllocBudget M)
    [PoolMemTransport A] : PoolMemTransport (withExecFrozenBudget A) where
  pool_transport_mem lim st {s s'} hvm := by
    dsimp only [withExecFrozenBudget]
    have hp := PoolMemTransport.pool_transport_mem (A := A) lim st hvm
    have hfr : ExecFrozen s'.mem = ExecFrozen s.mem := by
      apply propext
      exact ⟨fun h => ExecFrozen.of_perm_eq h (fun a => (hvm.2.2 a).symm),
             fun h => ExecFrozen.of_perm_eq h hvm.2.2⟩
    simp only [hp, hfr]

@[expose] def dummyUnenforcedLim : BudgetLimits :=
  { staticCount := 1, staticBytes := 0, physCap := 0, enforced := false }

private theorem dummyUnenforcedLim_ne_zero : dummyUnenforcedLim ≠ zeroBudgetLimits := by
  decide

@[expose] def nonZeroEquivLim (lim : BudgetLimits) : BudgetLimits :=
  if lim = zeroBudgetLimits then dummyUnenforcedLim else lim

theorem nonZeroEquivLim_ne_zero (lim : BudgetLimits) :
    nonZeroEquivLim lim ≠ zeroBudgetLimits := by
  unfold nonZeroEquivLim
  split
  · exact dummyUnenforcedLim_ne_zero
  · assumption

private theorem fitsEvents_nonZeroEquivLim (M : AllocCostModel)
    (lim : BudgetLimits) (st : M.σ) (evs : List AllocEvent) :
    LibsignalBinary.Heap.FitsEvents M (nonZeroEquivLim lim) st evs =
      LibsignalBinary.Heap.FitsEvents M lim st evs := by
  unfold nonZeroEquivLim
  split
  · rename_i h; subst h
    cases evs with
    | nil => rfl
    | cons ev rest =>
      apply propext
      constructor <;> (rintro ⟨⟨_, henf, _⟩, _⟩; cases henf)
  · rfl

theorem fitsEnv_nonZeroEquivLim (M : AllocCostModel)
    (lim : BudgetLimits) (st : M.σ) (E : List AllocEvent → Prop) :
    FitsEnv M (nonZeroEquivLim lim) st E = FitsEnv M lim st E := by
  dsimp only [FitsEnv]
  simp only [fitsEvents_nonZeroEquivLim]

theorem fineHookPool_nonZeroEquivLim (γ : GhostName) (mpl : MultiPlacement)
    (tp brkStart : BitVec 64) (lim : BudgetLimits) (st : fineCostModel.σ) (s : State) :
    (fineHookRustCliAllocBudget γ mpl tp brkStart).pool (nonZeroEquivLim lim) st s =
      (fineHookRustCliAllocBudget γ mpl tp brkStart).pool lim st s := by
  unfold nonZeroEquivLim
  split
  · rename_i h; subst h
    have hinv : ∀ staticIvs ivs,
        LibsignalBinary.Heap.mallocngBudgetPoolInv dummyUnenforcedLim staticIvs ivs s =
          LibsignalBinary.Heap.mallocngBudgetPoolInv zeroBudgetLimits staticIvs ivs s := by
      intro _ _
      unfold LibsignalBinary.Heap.mallocngBudgetPoolInv
      apply propext
      constructor <;> (intro _ henf; cases henf)
    have hpool :
        LibsignalBinary.Heap.mallocngBudgetPoolAt fineCostModel fineCostModelIface γ
          (mallocngAddrsOfPlacement mpl) tp brkStart dummyUnenforcedLim st s =
        LibsignalBinary.Heap.mallocngBudgetPoolAt fineCostModel fineCostModelIface γ
          (mallocngAddrsOfPlacement mpl) tp brkStart zeroBudgetLimits st s := by
      unfold LibsignalBinary.Heap.mallocngBudgetPoolAt
      simp only [hinv]
    have hrx :
        (dummyUnenforcedLim.enforced = true →
          LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase.CodeBlocksPermRX mpl s) =
        (zeroBudgetLimits.enforced = true →
          LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase.CodeBlocksPermRX mpl s) :=
      rfl
    change mallocngLib.codeRO mpl ∗
        LibsignalBinary.Heap.mallocngBudgetPoolAt fineCostModel fineCostModelIface γ
          (mallocngAddrsOfPlacement mpl) tp brkStart dummyUnenforcedLim st s ∗
        LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase.aesStorageCell brkStart ∗
        ⌜dummyUnenforcedLim.enforced = true →
          LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase.CodeBlocksPermRX mpl s⌝ =
      mallocngLib.codeRO mpl ∗
        LibsignalBinary.Heap.mallocngBudgetPoolAt fineCostModel fineCostModelIface γ
          (mallocngAddrsOfPlacement mpl) tp brkStart zeroBudgetLimits st s ∗
        LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase.aesStorageCell brkStart ∗
        ⌜zeroBudgetLimits.enforced = true →
          LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase.CodeBlocksPermRX mpl s⌝
    rw [hpool, hrx]
  · rfl

/-! ### Unstripped Callee Discharges on `c2FmtProgTrap lr` -/

private theorem f3Trial_memcpy_hasWords :
    f3TrialRxProg.hasWords f3StdLayout.memcpyAddr memcpySymWords := by
  have hoff_lt : (f3StdLayout.memcpyAddr - f3RxSegBase).toNat < 2 ^ 32 := by decide
  have hlen : memcpySymWords.length ≤ 1024 :=
    Nat.le_of_ble_eq_true (by rfl_kernel : Nat.ble memcpySymWords.length 1024 = true)
  exact hasWords_of_wordTree f3RxWordCount f3TrialRxWordTree_eq f3TrialRxWordTree_size
    (by rw [f3TrialRxProg_base]) (by omega) f3TrialRxProg_stubs f3TrialRxProg_symbols
    (by rfl_kernel : checkWordsAt f3TrialRxWordTree
      (f3StdLayout.memcpyAddr - f3RxSegBase).toNat memcpySymWords = true)

private theorem pureWordsProg_memcpy_hasWords (addr : BitVec 64) :
    (pureWordsProg addr memcpySymWords).hasWords addr memcpySymWords :=
  pureWordsProg_hasWords (base := addr) (words := memcpySymWords)
    (Nat.le_of_ble_eq_true (by rfl_kernel : Nat.ble (4 * memcpySymWords.length) (2 ^ 64) = true))
    (by rfl_kernel : ((List.range memcpySymWords.length).all fun i =>
      (pureWordsProg 0#64 memcpySymWords).readWordOff (4 * i) == memcpySymWords[i]?) = true)

private theorem pureWordsProg_memcpy_noSvcMsr (addr : BitVec 64) :
    (pureWordsProg addr memcpySymWords).allInstrs (fun i => !i.isSvc && !i.isMsrTpidrEl0) = true :=
  (by rfl_kernel :
    (pureWordsProg 0#64 memcpySymWords).allInstrs (fun i => !i.isSvc && !i.isMsrTpidrEl0) = true)

private def pureMemcpyNoVmSpec (ro : Bool) : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := (budgetMemcpySpec ro).pre
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ VerifiedLibraries.RustStd.AllocCallPreserved s0 sf⌝ ∗
      ((dst ↦ₛ bs) ∗ fmtSrcBytes ro src bs)

theorem c2FmtProgTrap_memcpy_ok {lr : BitVec 64}
    (hlr : lr.toNat < c2FirstExternStubAddr.toNat) (ro : Bool) :
    subroutine_ok (c2FmtProgTrap lr) wp4MemcpyRealAddr (budgetMemcpySpec ro) := by
  have haddrEq : wp4MemcpyRealAddr = f3StdLayout.memcpyAddr := by decide
  rw [haddrEq]
  have hPureVm :
      subroutine_ok (pureWordsProg f3StdLayout.memcpyAddr memcpySymWords)
        f3StdLayout.memcpyAddr (budgetMemcpySpec ro) :=
    budgetMemcpy_all_of_hasWords
      (pureWordsProg f3StdLayout.memcpyAddr memcpySymWords)
      f3StdLayout.memcpyAddr rfl
      (fun _ _ _ _ _ h => absurd rfl h)
      (pureWordsProg_memcpy_hasWords f3StdLayout.memcpyAddr) ro
  have hPureOk :
      subroutine_ok (pureWordsProg f3StdLayout.memcpyAddr memcpySymWords)
        f3StdLayout.memcpyAddr (pureMemcpyNoVmSpec ro) := by
    apply subroutine_ok.of_codeLoaded
    intro x R s0 hpc hrun hpre hsp _hL
    refine hPureVm.mono_outcome x R s0 hpc hrun hpre hsp fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp_st, hp⟩ | ⟨code, he_st, he⟩ | ⟨ho_st, ho⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [budgetMemcpySpec, pureMemcpyNoVmSpec] at hpost ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      exact ⟨⟨hpost.1.1, hpost.1.2.1⟩, hpost.2⟩
    · exact Or.inr (Or.inl ⟨hp_st, hp⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨code, he_st, he⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ho_st, ho⟩))
  have hcl_pure : ∀ m : Memory, (c2FmtProgTrap lr).CodeLoaded m →
      (pureWordsProg f3StdLayout.memcpyAddr memcpySymWords).CodeLoaded m :=
    fun m hm =>
      codeLoaded_pureWordsProg_of_hasWords
        (rxCode_of_c2FmtProg_codeLoaded ((c2FmtProgTrap_codeLoaded_iff lr m).mp hm))
        f3Trial_memcpy_hasWords (by decide)
  have hlen_w : 4 * memcpySymWords.length = 396 := by rfl_kernel
  have hext : BlockExternFree (c2FmtProgTrap lr) f3StdLayout.memcpyAddr (4 * memcpySymWords.length) :=
    c2FmtProgTrap_blockExternFree_of_pre_lib2 hlr (by decide) (by rw [hlen_w]; decide)
  have hLift := subroutine_ok_lift_pureWords_blockExternFree
    (P := c2FmtProgTrap lr)
    hPureOk
    (c2FmtProgTrap_svc lr)
    (pureWordsProg_memcpy_noSvcMsr f3StdLayout.memcpyAddr)
    hcl_pure hext
    (h_pre_mem := by rintro ⟨_, _, _⟩ s _; cases s; rfl)
    (h_post_mem := by rintro ⟨_, _, _⟩ s0 sf _ _; cases s0; cases sf; rfl)
  apply subroutine_ok.of_codeLoaded
  rintro x R s0 hpc hrun hpre hsp _hL
  refine hLift.mono_outcome x R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp_st, hp⟩ | ⟨code, he_st, he⟩ | ⟨ho_st, ho⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    refine Satisfies.mono (sepConj_mono_left ?_) hpost
    dsimp only [pureMemcpyNoVmSpec, budgetMemcpySpec]
    refine Entails.pure_left fun hpf => Entails.pure_left fun ⟨hx0f, hacp⟩ => ?_
    rcases hpf with ⟨_, _, htp, _, hbrk, hbrks, hphys, hperm⟩
    exact Entails.pure_right ⟨hx0f, hacp, ⟨⟨hbrks, hbrk, htp⟩, hphys, hperm⟩⟩ (Entails.refl _)
  · exact Or.inr (Or.inl ⟨hp_st, hp⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, he_st, he⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho_st, ho⟩))

private def retX30Words : List (BitVec 32) := [3596551104#32]

private theorem f3Trial_shim_hasWords :
    f3TrialRxProg.hasWords wp4NoShimV2Addr retX30Words := by
  have hoff_lt : (wp4NoShimV2Addr - f3RxSegBase).toNat < 2 ^ 32 := by decide
  have hrl : retX30Words.length = 1 := rfl
  exact hasWords_of_wordTree f3RxWordCount f3TrialRxWordTree_eq f3TrialRxWordTree_size
    (by rw [f3TrialRxProg_base]) (by omega) f3TrialRxProg_stubs f3TrialRxProg_symbols
    (by rfl_kernel : checkWordsAt f3TrialRxWordTree
      (wp4NoShimV2Addr - f3RxSegBase).toNat retX30Words = true)

private def pureAllocShimNoVmSpec : Spec Unit where
  pre := budgetAllocShimSpec.pre
  post := fun () s0 sf =>
    ⌜VerifiedLibraries.RustStd.AllocCallPreserved s0 sf⌝ ∗ Rust.hookFrame s0.sp

theorem c2FmtProgTrap_allocShim_ok {lr : BitVec 64}
    (hlr : lr.toNat < c2FirstExternStubAddr.toNat) :
    subroutine_ok (c2FmtProgTrap lr) wp4NoShimV2Addr budgetAllocShimSpec := by
  have hPureHas : hasInstrs (pureWordsProg wp4NoShimV2Addr retX30Words) wp4NoShimV2Addr [.ret .x30] := by
    intro i hi
    match i, hi with
    | 0, _ => rfl
  have hPureVm := budgetAllocShim_of_hasInstrs hPureHas
  have hPureOk :
      subroutine_ok (pureWordsProg wp4NoShimV2Addr retX30Words) wp4NoShimV2Addr
        pureAllocShimNoVmSpec := by
    apply subroutine_ok.of_codeLoaded
    intro () R s0 hpc hrun hpre hsp _hL
    refine hPureVm.mono_outcome () R s0 hpc hrun hpre hsp fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp_st, hp⟩ | ⟨code, he_st, he⟩ | ⟨ho_st, ho⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [budgetAllocShimSpec, pureAllocShimNoVmSpec] at hpost ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      exact ⟨hpost.1.1, hpost.2⟩
    · exact Or.inr (Or.inl ⟨hp_st, hp⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨code, he_st, he⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ho_st, ho⟩))
  have hcl_pure : ∀ m : Memory, (c2FmtProgTrap lr).CodeLoaded m →
      (pureWordsProg wp4NoShimV2Addr retX30Words).CodeLoaded m :=
    fun m hm =>
      codeLoaded_pureWordsProg_of_hasWords
        (rxCode_of_c2FmtProg_codeLoaded ((c2FmtProgTrap_codeLoaded_iff lr m).mp hm))
        f3Trial_shim_hasWords (by decide)
  have hext : BlockExternFree (c2FmtProgTrap lr) wp4NoShimV2Addr (4 * retX30Words.length) :=
    c2FmtProgTrap_blockExternFree_of_pre_lib2 hlr (by decide) (by decide)
  have hLift := subroutine_ok_lift_pureWords_blockExternFree
    (P := c2FmtProgTrap lr)
    hPureOk
    (c2FmtProgTrap_svc lr)
    (by rfl_kernel :
      (pureWordsProg wp4NoShimV2Addr retX30Words).allInstrs
        (fun i => !i.isSvc && !i.isMsrTpidrEl0) = true)
    hcl_pure hext
    (h_pre_mem := by intro _ s _; cases s; rfl)
    (h_post_mem := by intro _ s0 sf _ _; cases s0; cases sf; rfl)
  apply subroutine_ok.of_codeLoaded
  intro () R s0 hpc hrun hpre hsp _hL
  refine hLift.mono_outcome () R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp_st, hp⟩ | ⟨code, he_st, he⟩ | ⟨ho_st, ho⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    refine Satisfies.mono (sepConj_mono_left ?_) hpost
    dsimp only [pureAllocShimNoVmSpec, budgetAllocShimSpec]
    refine Entails.pure_left fun hpf => Entails.pure_left fun hacp => ?_
    rcases hpf with ⟨_, _, htp, _, hbrk, hbrks, hphys, hperm⟩
    exact Entails.pure_right ⟨hacp, ⟨⟨hbrks, hbrk, htp⟩, hphys, hperm⟩⟩ (Entails.refl _)
  · exact Or.inr (Or.inl ⟨hp_st, hp⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, he_st, he⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho_st, ho⟩))

theorem step_running {P : Program} {s s' : State} (h : Step P s s') :
    s.status = .Running := by
  cases h <;> assumption

theorem steps_preserves_halted {P : Program} {u v : State}
    (hs : Steps P u v) (hu : u.status = .Halted) : v.status = .Halted := by
  induction hs with
  | refl => exact hu
  | step hs1 _ ihs => cases hs1 <;> simp_all

theorem steps_preserves_exception {P : Program} {u v : State} {msg : String}
    (hs : Steps P u v) (hu : u.status = .Exception msg) : v.status = .Exception msg := by
  induction hs with
  | refl => exact hu
  | step hs1 _ ihs => cases hs1 <;> simp_all

private theorem strip_read32 (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) :
    (stripExecOutside keep m).read32 a = m.read32 a := by
  simp [Memory.read32, strip_read8]

theorem execInst_preserves_execFrozen {inst : Instr} (h : inst.isSvc0 = false)
    {s : State} (hfr : ExecFrozen s.mem) :
    ExecFrozen (execInst inst s).mem := by
  have hpf := ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 h s
  exact ExecFrozen.of_perm_eq hfr (congrFun hpf.2.1)

private theorem stripS_status (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).status = s.status := by cases s; rfl

private theorem stripS_pc (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).pc = s.pc := by cases s; rfl

private theorem stripS_mem (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).mem = stripExecOutside keep s.mem := by cases s; rfl

private theorem stripS_sp (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).sp = s.sp := by cases s; rfl

private theorem stripS_readReg64 (keep : BitVec 64 → Bool) (s : State) (r : Reg) :
    (stripS keep s).readReg64 r = s.readReg64 r := by cases s; rfl

private theorem satisfies_add_execFrozen_imp {P Q : SepProp} {m : Memory}
    {lim : BudgetLimits} (hfr : ExecFrozen m)
    (heq : (⌜lim ≠ zeroBudgetLimits → ExecFrozen m⌝ ∗ P) = Q)
    (hp : m ⊨ P) : m ⊨ Q := by
  rw [← heq, satisfies_pure_sepConj]
  exact ⟨fun _ => hfr, hp⟩

private theorem c2FmtProgTrap_codeLoaded_f3PrePanic {lr : BitVec 64} {m : Memory}
    (hLP : (c2FmtProgTrap lr).CodeLoaded m) :
    f3PrePanicRxProg.CodeLoaded m :=
  f3PrePanicRxProg_codeLoaded_of_f3Trial
    (rxCode_of_c2FmtProg_codeLoaded ((c2FmtProgTrap_codeLoaded_iff lr m).mp hLP))

private theorem c2FmtProgTrap_externAt_none_of_keepPrePanic {lr : BitVec 64}
    (hlr : lr.toNat < c2FirstExternStubAddr.toNat)
    {pc : BitVec 64} (hk : keepPrePanic pc = true) :
    (c2FmtProgTrap lr).externAt? pc = none := by
  unfold keepPrePanic at hk
  rw [decide_eq_true_eq] at hk
  have hlo : f3RxSegBase.toNat = 0x474000 := rfl
  have hlen : 4 * f3PrePanicWordCount = 0x5798 := rfl
  have hle_rx : 4 * f3PrePanicWordCount ≤ 4 * f3RxWordCount := by decide
  have hkp : keepRxSeg pc = true := by
    rw [keepRxSeg_eq_lt]
    exact decide_eq_true (by omega)
  have hlt : pc.toNat < 0x479798 := by
    by_contra hge
    have hsub : (pc - f3RxSegBase).toNat = pc.toNat - f3RxSegBase.toNat :=
      BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
    omega
  exact c2FmtProgTrap_externAt_none_of_keepRxSeg_not_panic hlr hkp
    (isLinkedPanicAddr_false_of_lt hlt)

theorem c2FmtProgTrap_rustAlloc_ok {lr : BitVec 64}
    (hlr : lr.toNat < c2FirstExternStubAddr.toNat)
    (mmpl : MultiPlacement) (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp brkStart : BitVec 64)
    {lim : BudgetLimits} (hlim : lim ≠ zeroBudgetLimits) :
    let A' := withExecFrozenBudget (fineHookRustCliAllocBudget γ mmpl tp brkStart)
    subroutine_ok (c2FmtProgTrap lr) (wp4NoShimV2Addr - 16#64)
      (rustBudgetAllocSpec (toRustAllocBudget fineCostModel A' lim)) := by
  intro A'
  apply rustBudgetAlloc_of_cliBase
  have hAddr : wp4NoShimV2Addr - 16#64 = f3StubAddrs.alloc := by decide
  rw [hAddr]
  exact c2_alloc_withExecFrozen_ok hMm γ tp brkStart hlim
    (c2FmtProgTrap_svc lr)
    (fun _ => c2FmtProgTrap_codeLoaded_f3PrePanic)
    (fun _ => c2FmtProgTrap_externAt_none_of_keepPrePanic hlr)

theorem c2FmtProgTrap_rustRealloc_ok {lr : BitVec 64}
    (hlr : lr.toNat < c2FirstExternStubAddr.toNat)
    (mmpl : MultiPlacement) (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp brkStart : BitVec 64)
    {lim : BudgetLimits} (hlim : lim ≠ zeroBudgetLimits) :
    let A' := withExecFrozenBudget (fineHookRustCliAllocBudget γ mmpl tp brkStart)
    subroutine_ok (c2FmtProgTrap lr) (wp4NoShimV2Addr - 8#64)
      (rustBudgetReallocSpec (toRustAllocBudget fineCostModel A' lim)) := by
  intro A'
  apply rustBudgetRealloc_of_cliBase
  have hAddr : wp4NoShimV2Addr - 8#64 = f3StubAddrs.realloc := by decide
  rw [hAddr]
  exact c2_realloc_withExecFrozen_ok hMm γ tp brkStart hlim
    (c2FmtProgTrap_svc lr)
    (fun _ => c2FmtProgTrap_codeLoaded_f3PrePanic)
    (fun _ => c2FmtProgTrap_externAt_none_of_keepPrePanic hlr)

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtRow.TrapStubs
