/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.FromRecordCalleesCodeSym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Drops.Local1
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep -- proof-setup: allow-public-import
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Drops.Common
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.Chain.VecExtBudget
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.ExtBudget
import ProofLib.Sep
meta import Lean
import ProofLib.SepLogic.WP.Apply
import LibsignalBinary.Proofs.CodeLayout

/-!
# Budget-Threaded Relocatable Contract for `drop_glue<SessionStructure> [local#1]` (Block `6`)

Verifies `core::ptr::drop_glue::<SessionStructure> [local#1]` against
`dropSessionStructureLocal1Spec M A lim` under `[LibsignalPlacement]` over `RustCliAllocBudget M`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Drops.Local1Budget

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession (SenderChain)
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement blkPC_6 blkPl_6 lsRustDeallocSym
  lsmpl lsρ sepWP_seq_lscl withLsCodeLoaded
  subroutine_ok_withLsCodeLoaded_of_plain ls_subroutine_ok_of_block
)
open CryptoVerification.RustHeap (RustAlloc allocHookStack vecAt)
open CryptoVerification.LibsignalSessionRepr (chainAt messageKeyAt)
open CryptoVerification.LibsignalTripleRatchetRepr (
  SenderChainGhost SessionGhost noneCap optSenderChainAt
)
open CryptoVerification.LibsignalTripleRatchet.Getters (
  blkPC_3 blkPl_3 dropVecChainStack dropVecMessageKeyStack ls_hook_ok_rustDealloc
)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (
  dropSessionStructureLocal1Stack
  sender_none_entails_memRegion_104_shared_lb
  ssFirst3HeadersAt_shared_lb ssSender1HeadersAt_shared_lb ssTail3HeadersAt_shared_lb
)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.DropsCommon (
  SepWP.false_elim_left
  optSenderChainAt_some_entails_dealloc1 sessionStateAt_entails_dealloc sgnPinDealloc
  ssFirst3HeadersAt_entails_memRegions ssTail3HeadersAt_entails_memRegions
  stackAt_split_bottom' vecPinDealloc
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs PoolPreserved
  RustCliAllocBudget VmPreserved rustDeallocEvents rustCliDeallocBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (
  dropVecChainSpec dropVecMessageKeySpec
)
open LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.Chain.VecExtBudget (
  drop_vec_chain_placed_ok
)
open LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.ExtBudget (
  drop_vec_message_key_placed_ok
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal1Spec
)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

run_meta do
  let env ← Lean.getEnv
  for (h, ks) in #[(``RustAlloc.live, #[1]), (``stackAt, #[0]), (``vecPinDealloc, #[1]), (``sgnPinDealloc, #[1, 2]), (``vecAt, #[5]), (``optSenderChainAt, #[1]), (``RustCliAllocBudget.pool, #[1])] do
    let n := Lean.mkPrivateName env (((ks.foldl Lean.Name.mkNum ProofLib.Sep.sepKeyMarker).str "_TARGET_") ++ h)
    unless env.contains n do
      Lean.withExporting (isExporting := false) do
        Lean.addDecl <| .defnDecl { name := n, levelParams := [], type := .const ``Unit [], value := .const ``Unit.unit [], hints := .abbrev, safety := .safe }

private def freeOnlyPool {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) : SepProp :=
  ∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) s

register_sep_key freeOnlyPool [1]

private theorem weaken_pre_mid {prog : Program} {target : BitVec 64} {sf : State}
    {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    (hent : P ⊢ P_mid sf)
    (h : SepWP prog target sf (P_mid sf) (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm)) :
    SepWP prog target sf P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm) :=
  SepWP.weaken_pre hent h

private theorem freeOnlyPool_intro {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    A.pool lim st s ⊢ freeOnlyPool A lim st s :=
  Entails.sepExists_right [] (Entails.pure_right FreeOnlyEvs.nil (Entails.refl _))

private theorem freeOnlyPool_keep {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {evs : List AllocEvent} (hevs : FreeOnlyEvs evs)
    {s sm : State}
    (hvm : VmPreserved s sm := by simp [VmPreserved, PoolPreserved, wp_norm, arm64_norm]) :
    A.pool lim (M.stepEvents evs st) s ⊢ freeOnlyPool A lim st sm := by
  rw [← A.pool_of_vmPreserved hvm]
  exact Entails.sepExists_right evs (Entails.pure_right hevs (Entails.refl _))

private theorem freeOnlyPool_append {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {evs₁ evs₂ : List AllocEvent}
    (h1 : FreeOnlyEvs evs₁) (h2 : FreeOnlyEvs evs₂) {s sm : State}
    (hvm : VmPreserved s sm := by simp [VmPreserved, PoolPreserved, wp_norm, arm64_norm]) :
    A.pool lim (M.stepEvents evs₂ (M.stepEvents evs₁ st)) s ⊢
      freeOnlyPool A lim st sm := by
  rw [← A.pool_of_vmPreserved hvm, ← M.stepEvents_append evs₁ evs₂ st]
  exact Entails.sepExists_right (evs₁ ++ evs₂)
    (Entails.pure_right (FreeOnlyEvs.append h1 h2) (Entails.refl _))

private theorem freeOnlyPool_dealloc {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {evs : List AllocEvent} (hevs : FreeOnlyEvs evs)
    (sz al : Nat) {s sm : State}
    (hvm : VmPreserved s sm := by simp [VmPreserved, PoolPreserved, wp_norm, arm64_norm]) :
    A.pool lim (M.stepEvents (rustDeallocEvents sz al) (M.stepEvents evs st)) s ⊢
      freeOnlyPool A lim st sm :=
  freeOnlyPool_append A lim st hevs (FreeOnlyEvs.singleton al sz) hvm

private theorem SepWP.seq_state {prog : Program} {mid target : BitVec 64} {s : State}
    {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q sm →
      SepWP prog target sm (P_mid sm) post) :
    SepWP prog target s P post :=
  SepWP.seq h1 (fun sm _Pm hpcm hrunm ⟨hent, hq⟩ =>
    SepWP.weaken_pre hent (h2 sm hpcm hrunm hq))

private theorem seq_state_lscl [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → LibsignalCodeLoaded lsmpl sm.mem → Q sm →
      SepWP prog target sm (P_mid sm) post) :
    SepWP prog target s P post := by
  apply sepWP_seq_lscl hcl (mid := mid)
  refine SepWP.mono h1 ?_
  rintro sm Pm hpcm hrunm ⟨hent, hQ⟩ hclm
  exact SepWP.weaken_pre hent (h2 sm hpcm hrunm hclm hQ)

private theorem SepWP.unpack_freeOnlyPool {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {prog : Program} {target : BitVec 64} {s : State} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hf : P = freeOnlyPool A lim st s ∗ Frame := by sep_focus)
    (hk : ∀ evs : List AllocEvent, FreeOnlyEvs evs →
      SepWP prog target s (A.pool lim (M.stepEvents evs st) s ∗ Frame) post) :
    SepWP prog target s P post := by
  rw [hf]; unfold freeOnlyPool
  wp_pull_exists
  rename_i evs
  exact SepWP.pure_elim (hk evs)

private theorem SepWP.fold_keep {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {evs : List AllocEvent} (hevs : FreeOnlyEvs evs)
    {prog : Program} {target : BitVec 64} {s sm : State} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hf : P = A.pool lim (M.stepEvents evs st) s ∗ Frame := by sep_focus)
    (hvm : VmPreserved s sm := by simp [VmPreserved, PoolPreserved, wp_norm, arm64_norm])
    (hk : SepWP prog target sm (freeOnlyPool A lim st sm ∗ Frame) post) :
    SepWP prog target sm P post :=
  SepWP.focus_weaken (freeOnlyPool_keep A lim st hevs hvm) hf hk

private theorem SepWP.fold_append {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {evs₁ evs₂ : List AllocEvent} (h1 : FreeOnlyEvs evs₁)
    {prog : Program} {target : BitVec 64} {s sm : State} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hf : P = A.pool lim (M.stepEvents evs₂ (M.stepEvents evs₁ st)) s ∗ Frame := by sep_focus)
    (h2 : FreeOnlyEvs evs₂ := by assumption)
    (hvm : VmPreserved s sm := by simp [VmPreserved, PoolPreserved, wp_norm, arm64_norm])
    (hk : SepWP prog target sm (freeOnlyPool A lim st sm ∗ Frame) post) :
    SepWP prog target sm P post :=
  SepWP.focus_weaken (freeOnlyPool_append A lim st h1 h2 hvm) hf hk

private theorem SepWP.fold_dealloc {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {evs : List AllocEvent} (hevs : FreeOnlyEvs evs) (sz al : Nat)
    {prog : Program} {target : BitVec 64} {s sm : State} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hf : P = A.pool lim (M.stepEvents (rustDeallocEvents sz al) (M.stepEvents evs st)) s ∗ Frame := by sep_focus)
    (hvm : VmPreserved s sm := by simp [VmPreserved, PoolPreserved, wp_norm, arm64_norm])
    (hk : SepWP prog target sm (freeOnlyPool A lim st sm ∗ Frame) post) :
    SepWP prog target sm P post :=
  SepWP.focus_weaken (freeOnlyPool_dealloc A lim st hevs sz al hvm) hf hk

private theorem SepWP.sync_pool {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {prog : Program} {target : BitVec 64} {s sm : State} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hf : P = A.pool lim st s ∗ Frame := by sep_focus)
    (hvm : VmPreserved s sm := by simp [VmPreserved, PoolPreserved, wp_norm, arm64_norm])
    (hk : SepWP prog target sm (A.pool lim st sm ∗ Frame) post) :
    SepWP prog target sm P post := by
  rw [hf, ← A.pool_of_vmPreserved hvm]
  exact hk

@[reducible]
private def Saved32Preserved (s0 s : State) (fsp : BitVec 64) : Prop :=
  s.readReg64 .x20 = s0.readReg64 .x20 ∧
  s.readReg64 .x21 = s0.readReg64 .x21 ∧
  s.readReg64 .x22 = s0.readReg64 .x22 ∧
  s.readReg64 .x23 = s0.readReg64 .x23 ∧
  s.readReg64 .x24 = s0.readReg64 .x24 ∧
  s.readReg64 .x25 = s0.readReg64 .x25 ∧
  s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x28 = s0.readReg64 .x28 ∧
  s.sp = fsp ∧
  s.trace = s0.trace ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

private theorem stackAt_ss_local1_split (sp : BitVec 64) :
    stackAt sp dropSessionStructureLocal1Stack =
      stackAt (sp - 32#64) dropVecChainStack ∗ cells (sp - 32#64) 4 :=
  stackAt_split_cells sp dropVecChainStack 4 (by decide)

private theorem stackAt_dropVecChain_split_alloc (fsp : BitVec 64) :
    stackAt fsp dropVecChainStack =
      memRegion (fsp - 4192#64) 96 ∗ stackAt fsp allocHookStack := by
  rw [show dropVecChainStack = allocHookStack + 96 from rfl,
      stackAt_split_bottom' fsp allocHookStack 96 (by decide)]

private theorem stackAt_dropVecChain_split_mk (fsp : BitVec 64) :
    stackAt fsp dropVecChainStack =
      memRegion (fsp - 4192#64) 48 ∗ stackAt fsp dropVecMessageKeyStack := by
  rw [show dropVecChainStack = dropVecMessageKeyStack + 48 from rfl,
      stackAt_split_bottom' fsp dropVecMessageKeyStack 48 (by decide)]
  rfl

private theorem stackAt_dropVecMessageKey_split_alloc (fsp : BitVec 64) :
    stackAt fsp dropVecMessageKeyStack =
      memRegion (fsp - 4144#64) 48 ∗ stackAt fsp allocHookStack := by
  rw [show dropVecMessageKeyStack = allocHookStack + 48 from rfl,
      stackAt_split_bottom' fsp allocHookStack 48 (by decide)]

private theorem stack_128_eq_ss_local1 (sp : BitVec 64) :
    memRegion (sp - 4224#64) 128 ∗ stackAt sp allocHookStack =
      stackAt sp dropSessionStructureLocal1Stack := by
  rw [← stackAt_split_bottom' sp allocHookStack 128 (by decide)]
  rfl

private theorem tail_stack_128_from_bottom (sp : BitVec 64) :
    memRegion (sp - 4224#64) 128 ∗ stackAt sp allocHookStack =
      stackAt (sp - 32#64) dropVecChainStack ∗ cells (sp - 32#64) 4 := by
  rw [stack_128_eq_ss_local1 sp, stackAt_ss_local1_split sp]

private theorem ss_local1_post_entails {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ast : M.σ) {s0 sf : State} (htr : sf.trace = s0.trace)
    (ss sp : BitVec 64) :
    memRegion ss 344 ∗ freeOnlyPool A lim ast sf ∗ stackAt sp dropSessionStructureLocal1Stack ⊢
      ∃∗ evs : List AllocEvent,
        ⌜sf.trace = s0.trace ∧ FreeOnlyEvs evs⌝ ∗
          memRegion ss 344 ∗ A.pool lim (M.stepEvents evs ast) sf ∗
          stackAt sp dropSessionStructureLocal1Stack := by
  unfold freeOnlyPool
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro evs
  refine Entails.sepExists_right evs ?_
  have hpure :
      memRegion ss 344 ∗ (⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs ast) sf) ∗
        stackAt sp dropSessionStructureLocal1Stack ⊢
      ⌜FreeOnlyEvs evs⌝ ∗
        (memRegion ss 344 ∗ A.pool lim (M.stepEvents evs ast) sf ∗
          stackAt sp dropSessionStructureLocal1Stack) := by bi_entail
  refine Entails.trans hpure ?_
  apply Entails.pure_left; intro hevs
  exact Entails.pure_right ⟨htr, hevs⟩ (Entails.refl _)

private theorem SepWP.finish_ss_local1 {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ast : M.σ) {prog : Program} {target : BitVec 64}
    {s0 sf : State} {P : SepProp} {post : State → SepProp → Prop}
    (ss sp : BitVec 64)
    (hP : P ⊢ memRegion ss 344 ∗ freeOnlyPool A lim ast sf ∗ stackAt sp dropSessionStructureLocal1Stack)
    (htr : sf.trace = s0.trace)
    (hk : ∀ evs : List AllocEvent, sf.trace = s0.trace ∧ FreeOnlyEvs evs →
      SepWP prog target sf
        (memRegion ss 344 ∗ A.pool lim (M.stepEvents evs ast) sf ∗
          stackAt sp dropSessionStructureLocal1Stack) post) :
    SepWP prog target sf P post := by
  refine SepWP.weaken_pre (Entails.trans hP (ss_local1_post_entails A lim ast htr ss sp)) ?_
  wp_pull_exists
  rename_i evs
  exact SepWP.pure_elim (hk evs)

private theorem ssSender1HeadersAt_entails_memRegions (ss : BitVec 64) (sg : SenderChainGhost)
    (ckCap ckPtr : BitVec 64) :
    ssSender1HeadersAt_shared_lb ss sg ckCap ckPtr ⊢
      memRegion (ss + 144#64) 48 ∗ memRegion (ss + 216#64) 32 := by
  unfold ssSender1HeadersAt_shared_lb
  sep_interval

private theorem ssSender1_memRegions_entails_104 (ss : BitVec 64) :
    memRegion (ss + 192#64) 24 ∗ memRegion (ss + 144#64) 48 ∗ memRegion (ss + 216#64) 32 ⊢
      memRegion (ss + 144#64) 104 := by
  sep_interval

private theorem optSenderChainAt_some_entails_ss_local1 (A : RustAlloc) (ss : BitVec 64)
    (sg : SenderChainGhost) (sc : SenderChain) :
    optSenderChainAt A (ss + 144#64) (some sg) (some sc) ⊢
      ∃∗ ckCap : BitVec 64, ∃∗ ckPtr : BitVec 64,
        ⌜sg.srk.cap + 1#64 ≠ 0#64⌝ ∗
        (ssSender1HeadersAt_shared_lb ss sg ckCap ckPtr ∗
          vecPinDealloc A ⟨sg.srk.cap, sg.srk.ptr⟩ ∗
          vecPinDealloc A ⟨sg.priv.cap, sg.priv.ptr⟩ ∗
          sgnPinDealloc A ckCap ckPtr) ∗
        vecAt A 104 8 (messageKeyAt A) (ss + 192#64) sg.mkCap sg.mkPtr [] := by
  refine Entails.trans (optSenderChainAt_some_entails_dealloc1 A (ss + 144#64) sg sc) ?_
  unfold ssSender1HeadersAt_shared_lb
  bi_entail

private theorem drop_ss_local1_placed_first3 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ast : M.σ}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_6).rebase (blkPl_6).base H)
      (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (fsp ss : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (G : SessionGhost) (s : State) (Frame : SepProp),
      s.pc = (blkPl_6).base + 12#64 →
      s.status = .Running →
      Saved32Preserved s0 s fsp →
      s.readReg64 .x0 = ss →
      SepWP ((blkPC_6).rebase (blkPl_6).base H)
        ((blkPl_6).base + 76#64)
        s
        ((ssFirst3HeadersAt_shared_lb ss G ∗
          vecPinDealloc A.repAlloc ⟨G.localIk.cap, G.localIk.ptr⟩ ∗
          vecPinDealloc A.repAlloc ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
          vecPinDealloc A.repAlloc G.root) ∗
          freeOnlyPool A lim ast s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ (memRegion ss 24 ∗ memRegion (ss + 24#64) 24 ∗ memRegion (ss + 48#64) 24) ∗
            freeOnlyPool A lim ast sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved32Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ss) := by
  simp only [rustCliDeallocBudgetSpec] at hdealloc
  intro G s Frame hpc hrun hpres hx0
  rcases hpres with ⟨hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine SepWP.seq_state (mid := (blkPl_6).base + 36#64) (P_mid := fun sm =>
    (ssFirst3HeadersAt_shared_lb ss G ∗
      vecPinDealloc A.repAlloc ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
      vecPinDealloc A.repAlloc G.root) ∗
    freeOnlyPool A lim ast sm ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => Saved32Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss)
    ?_ ?_
  · refine SepWP.unpack_freeOnlyPool (by sep_focus) fun evs hevs => ?_
    dsimp only [ssFirst3HeadersAt_shared_lb, vecPinDealloc]
    by_cases hcap : (G.localIk.cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
    · wp_steps
      refine SepWP.fold_keep hevs (hk := ?_)
      wp_done
    · wp_steps
      refine SepWP.sync_pool (hk := ?_)
      rw [← hsp]
      wp_call hdealloc (G.localIk.ptr, G.localIk.cap.toNat, 1, M.stepEvents evs ast)
      have htr_d : sf.trace = s0.trace := (‹AllocCallPreserved _ sf›.2.1).trans htrace
      refine SepWP.fold_dealloc hevs G.localIk.cap.toNat 1 (hk := ?_)
      refine weaken_pre_mid (by rw [hsp]; bi_entail) ?_
      wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine SepWP.seq_state (mid := (blkPl_6).base + 56#64) (P_mid := fun sm =>
      (ssFirst3HeadersAt_shared_lb ss G ∗ vecPinDealloc A.repAlloc G.root) ∗
      freeOnlyPool A lim ast sm ∗ stackAt fsp allocHookStack ∗ Frame)
      (Q := fun sm => Saved32Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss)
      ?_ ?_
    · refine SepWP.unpack_freeOnlyPool (by sep_focus) fun evs hevs => ?_
      dsimp only [ssFirst3HeadersAt_shared_lb, vecPinDealloc]
      by_cases hcap : (G.remoteIk.cap == 0#64) = true <;>
        simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
      · wp_steps
        refine SepWP.fold_keep hevs (hk := ?_)
        wp_done
      · wp_steps
        refine SepWP.sync_pool (hk := ?_)
        rw [← hsp_1]
        wp_call hdealloc (G.remoteIk.ptr, G.remoteIk.cap.toNat, 1, M.stepEvents evs ast)
        have htr_d : sf.trace = s0.trace := (‹AllocCallPreserved _ sf›.2.1).trans htrace_1
        refine SepWP.fold_dealloc hevs G.remoteIk.cap.toNat 1 (hk := ?_)
        refine weaken_pre_mid (by rw [hsp_1]; bi_entail) ?_
        wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      have hstep3 : SepWP ((blkPC_6).rebase (blkPl_6).base H) ((blkPl_6).base + 76#64) s2
          ((ssFirst3HeadersAt_shared_lb ss G ∗ vecPinDealloc A.repAlloc G.root) ∗
            freeOnlyPool A lim ast s2 ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ ssFirst3HeadersAt_shared_lb ss G ∗ freeOnlyPool A lim ast sm ∗
              stackAt fsp allocHookStack ∗ Frame) ∧
            Saved32Preserved s0 sm fsp ∧
            sm.readReg64 .x19 = ss) := by
        refine SepWP.unpack_freeOnlyPool (by sep_focus) fun evs hevs => ?_
        dsimp only [ssFirst3HeadersAt_shared_lb, vecPinDealloc]
        by_cases hcap : (G.root.cap == 0#64) = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
        · wp_steps
          refine SepWP.fold_keep hevs (hk := ?_)
          wp_done
        · wp_steps
          refine SepWP.sync_pool (hk := ?_)
          rw [← hsp_2]
          wp_call hdealloc (G.root.ptr, G.root.cap.toNat, 1, M.stepEvents evs ast)
          have htr_d : sf.trace = s0.trace := (‹AllocCallPreserved _ sf›.2.1).trans htrace_2
          refine SepWP.fold_dealloc hevs G.root.cap.toNat 1 (hk := ?_)
          refine weaken_pre_mid (by rw [hsp_2]; bi_entail) ?_
          wp_done
      exact SepWP.mono hstep3 (fun sm Pm _ _ h =>
        ⟨Entails.trans h.1 (sepConj_mono_left (ssFirst3HeadersAt_entails_memRegions ss G)), h.2⟩)

private theorem drop_ss_local1_placed_sender [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ast : M.σ}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_6).rebase (blkPl_6).base H)
      (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hdrop_mk : subroutine_ok ((blkPC_6).rebase (blkPl_6).base H)
      (lsmpl.base 3) (withLsCodeLoaded lsmpl (dropVecMessageKeySpec M A lim)))
    (s0 : State) (fsp ss : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (senderG : Option SenderChainGhost) (senderSt : Option SenderChain)
      (s : State) (Frame : SepProp),
      s.pc = (blkPl_6).base + 76#64 →
      s.status = .Running →
      LibsignalCodeLoaded lsmpl s.mem →
      Saved32Preserved s0 s fsp →
      s.readReg64 .x19 = ss →
      SepWP ((blkPC_6).rebase (blkPl_6).base H)
        ((blkPl_6).base + 156#64)
        s
        (optSenderChainAt A.repAlloc (ss + 144#64) senderG senderSt ∗
          freeOnlyPool A lim ast s ∗ stackAt fsp dropVecMessageKeyStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion (ss + 144#64) 104 ∗ freeOnlyPool A lim ast sm ∗
            stackAt fsp dropVecMessageKeyStack ∗ Frame) ∧
          Saved32Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ss) := by
  simp only [rustCliDeallocBudgetSpec] at hdealloc
  simp only [withLsCodeLoaded, dropVecMessageKeySpec] at hdrop_mk
  intro senderG senderSt s Frame hpc hrun hcl hpres hx19
  rcases hpres with ⟨hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  cases senderG with
  | none =>
    cases senderSt with
    | none =>
      unfold optSenderChainAt
      have hstep : SepWP ((blkPC_6).rebase (blkPl_6).base H) ((blkPl_6).base + 156#64) s
          ((((ss + 144#64) ↦₆₄ noneCap) ∗ memRegion ((ss + 144#64) + 8#64) 96) ∗
            freeOnlyPool A lim ast s ∗ stackAt fsp dropVecMessageKeyStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ (((ss + 144#64) ↦₆₄ noneCap) ∗ memRegion ((ss + 144#64) + 8#64) 96) ∗
              freeOnlyPool A lim ast sm ∗ stackAt fsp dropVecMessageKeyStack ∗ Frame) ∧
            Saved32Preserved s0 sm fsp ∧
            sm.readReg64 .x19 = ss) := by
        refine SepWP.unpack_freeOnlyPool (by sep_focus) fun evs hevs => ?_
        dsimp only [noneCap]
        wp_steps
        refine SepWP.fold_keep hevs (hk := ?_)
        wp_done
      exact SepWP.mono hstep (fun sm Pm _ _ h =>
        ⟨Entails.trans h.1 (sepConj_mono_left (sender_none_entails_memRegion_104_shared_lb (ss + 144#64))), h.2⟩)
    | some _ => simp only [optSenderChainAt]; exact SepWP.false_elim_left
  | some sg =>
    cases senderSt with
    | none => simp only [optSenderChainAt]; exact SepWP.false_elim_left
    | some sc =>
      refine SepWP.weaken_pre
        (sepConj_mono_left (optSenderChainAt_some_entails_ss_local1 A.repAlloc ss sg sc)) ?_
      wp_pull_exists
      rename_i ckCap ckPtr
      refine SepWP.pure_elim fun hcmn => ?_
      have hcmn_beq : (sg.srk.cap + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hcmn
      rw [stackAt_dropVecMessageKey_split_alloc fsp]
      refine SepWP.weaken_pre (P' :=
        (ssSender1HeadersAt_shared_lb ss sg ckCap ckPtr ∗
          vecPinDealloc A.repAlloc ⟨sg.srk.cap, sg.srk.ptr⟩ ∗
          vecPinDealloc A.repAlloc ⟨sg.priv.cap, sg.priv.ptr⟩ ∗
          sgnPinDealloc A.repAlloc ckCap ckPtr) ∗
        freeOnlyPool A lim ast s ∗ stackAt fsp allocHookStack ∗
        (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
          memRegion (fsp - 4144#64) 48 ∗ Frame))
        (by dsimp only [ssSender1HeadersAt_shared_lb]; bi_entail) ?_
      refine seq_state_lscl hcl (mid := (blkPl_6).base + 104#64) (P_mid := fun sm =>
        (ssSender1HeadersAt_shared_lb ss sg ckCap ckPtr ∗
          vecPinDealloc A.repAlloc ⟨sg.priv.cap, sg.priv.ptr⟩ ∗
          sgnPinDealloc A.repAlloc ckCap ckPtr) ∗
        freeOnlyPool A lim ast sm ∗ stackAt fsp allocHookStack ∗
        (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
          memRegion (fsp - 4144#64) 48 ∗ Frame))
        (Q := fun sm => Saved32Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss)
        ?_ ?_
      · refine SepWP.unpack_freeOnlyPool (by sep_focus) fun evs hevs => ?_
        dsimp only [ssSender1HeadersAt_shared_lb, vecPinDealloc, sgnPinDealloc]
        by_cases hcap : (sg.srk.cap == 0#64) = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
        · wp_steps
          refine SepWP.fold_keep hevs (hk := ?_)
          wp_done
        · wp_steps
          refine SepWP.sync_pool (hk := ?_)
          rw [← hsp]
          wp_call hdealloc (sg.srk.ptr, sg.srk.cap.toNat, 1, M.stepEvents evs ast)
          have htr_d : sf.trace = s0.trace := (‹AllocCallPreserved _ sf›.2.1).trans htrace
          refine SepWP.fold_dealloc hevs sg.srk.cap.toNat 1 (hk := ?_)
          refine weaken_pre_mid (by rw [hsp]; bi_entail) ?_
          wp_done
      · intro s1 hpc1 hrun1 hcl1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
        refine seq_state_lscl hcl1 (mid := (blkPl_6).base + 124#64) (P_mid := fun sm =>
          (ssSender1HeadersAt_shared_lb ss sg ckCap ckPtr ∗ sgnPinDealloc A.repAlloc ckCap ckPtr) ∗
          freeOnlyPool A lim ast sm ∗ stackAt fsp allocHookStack ∗
          (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
            memRegion (fsp - 4144#64) 48 ∗ Frame))
          (Q := fun sm => Saved32Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss)
          ?_ ?_
        · refine SepWP.unpack_freeOnlyPool (by sep_focus) fun evs hevs => ?_
          dsimp only [ssSender1HeadersAt_shared_lb, vecPinDealloc, sgnPinDealloc]
          by_cases hcap : (sg.priv.cap == 0#64) = true <;>
            simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
          · wp_steps
            refine SepWP.fold_keep hevs (hk := ?_)
            wp_done
          · wp_steps
            refine SepWP.sync_pool (hk := ?_)
            rw [← hsp_1]
            wp_call hdealloc (sg.priv.ptr, sg.priv.cap.toNat, 1, M.stepEvents evs ast)
            have htr_d : sf.trace = s0.trace := (‹AllocCallPreserved _ sf›.2.1).trans htrace_1
            refine SepWP.fold_dealloc hevs sg.priv.cap.toNat 1 (hk := ?_)
            refine weaken_pre_mid (by rw [hsp_1]; bi_entail) ?_
            wp_done
        · intro s2 hpc2 hrun2 hcl2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
          refine seq_state_lscl hcl2 (mid := (blkPl_6).base + 148#64) (P_mid := fun sm =>
            vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
            freeOnlyPool A lim ast sm ∗ stackAt fsp dropVecMessageKeyStack ∗
            ((memRegion (ss + 144#64) 48 ∗ memRegion (ss + 216#64) 32) ∗ Frame))
            (Q := fun sm => Saved32Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss)
            ?_ ?_
          · have hstep3 : SepWP ((blkPC_6).rebase (blkPl_6).base H) ((blkPl_6).base + 148#64) s2
                ((ssSender1HeadersAt_shared_lb ss sg ckCap ckPtr ∗ sgnPinDealloc A.repAlloc ckCap ckPtr) ∗
                  freeOnlyPool A lim ast s2 ∗ stackAt fsp allocHookStack ∗
                  (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
                    memRegion (fsp - 4144#64) 48 ∗ Frame))
                (fun sm Pm =>
                  (Pm ⊢ ssSender1HeadersAt_shared_lb ss sg ckCap ckPtr ∗
                    freeOnlyPool A lim ast sm ∗ stackAt fsp allocHookStack ∗
                    (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
                      memRegion (fsp - 4144#64) 48 ∗ Frame)) ∧
                  Saved32Preserved s0 sm fsp ∧
                  sm.readReg64 .x19 = ss) := by
              refine SepWP.unpack_freeOnlyPool (by sep_focus) fun evs hevs => ?_
              dsimp only [ssSender1HeadersAt_shared_lb, sgnPinDealloc]
              by_cases hcap : ckCap.slt 1#64 = true <;>
                simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
              · wp_steps
                refine SepWP.fold_keep hevs (hk := ?_)
                wp_done
              · wp_steps
                refine SepWP.sync_pool (hk := ?_)
                rw [← hsp_2]
                wp_call hdealloc (ckPtr, ckCap.toNat, 1, M.stepEvents evs ast)
                have htr_d : sf.trace = s0.trace := (‹AllocCallPreserved _ sf›.2.1).trans htrace_2
                refine SepWP.fold_dealloc hevs ckCap.toNat 1 (hk := ?_)
                refine weaken_pre_mid (by rw [hsp_2]; bi_entail) ?_
                wp_done
            refine SepWP.mono hstep3 (fun sm Pm _ _ h => ⟨Entails.trans h.1 ?_, h.2⟩)
            refine Entails.trans (sepConj_mono_left (ssSender1HeadersAt_entails_memRegions ss sg ckCap ckPtr)) ?_
            rw [stackAt_dropVecMessageKey_split_alloc fsp]
            bi_entail
          · intro s3 hpc3 hrun3 hcl3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
            have hstep4 : SepWP ((blkPC_6).rebase (blkPl_6).base H) ((blkPl_6).base + 156#64) s3
                (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
                  freeOnlyPool A lim ast s3 ∗ stackAt fsp dropVecMessageKeyStack ∗
                  ((memRegion (ss + 144#64) 48 ∗ memRegion (ss + 216#64) 32) ∗ Frame))
                (fun sm Pm =>
                  (Pm ⊢ (memRegion (ss + 192#64) 24 ∗ memRegion (ss + 144#64) 48 ∗ memRegion (ss + 216#64) 32) ∗
                    freeOnlyPool A lim ast sm ∗ stackAt fsp dropVecMessageKeyStack ∗ Frame) ∧
                  Saved32Preserved s0 sm fsp ∧
                  sm.readReg64 .x19 = ss) := by
              refine SepWP.unpack_freeOnlyPool (by sep_focus) fun evs hevs => ?_
              wp_steps
              refine SepWP.sync_pool (hk := ?_)
              rw [← hsp_3]
              wp_call hdrop_mk (⟨ss + 192#64, sg.mkCap, sg.mkPtr, []⟩, M.stepEvents evs ast)
              have htr_m : sf.trace = s0.trace := (by assumption : sf.trace = _).trans htrace_3
              refine SepWP.fold_append hevs (hk := ?_)
              refine weaken_pre_mid (by rw [hsp_3]; bi_entail) ?_
              wp_done
            refine SepWP.mono hstep4 (fun sm Pm _ _ h => ⟨Entails.trans h.1 ?_, h.2⟩)
            rw [← stackAt_dropVecMessageKey_split_alloc fsp]
            exact sepConj_mono_left (ssSender1_memRegions_entails_104 ss)

private theorem drop_ss_local1_placed_tail3 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ast : M.σ}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_6).rebase (blkPl_6).base H)
      (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (fsp ss : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (pCap pPtr kCap kPtr : BitVec 64) (G : SessionGhost) (s : State) (Frame : SepProp),
      s.pc = (blkPl_6).base + 164#64 →
      s.status = .Running →
      Saved32Preserved s0 s fsp →
      s.readReg64 .x19 = ss →
      SepWP ((blkPC_6).rebase (blkPl_6).base H)
        ((blkPl_6).base + 232#64)
        s
        ((ssTail3HeadersAt_shared_lb ss pCap pPtr kCap kPtr G ∗
          sgnPinDealloc A.repAlloc pCap pPtr ∗
          sgnPinDealloc A.repAlloc kCap kPtr ∗
          vecPinDealloc A.repAlloc ⟨G.alice.cap, G.alice.ptr⟩) ∗
          freeOnlyPool A lim ast s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ (memRegion (ss + 248#64) 48 ∗ memRegion (ss + 296#64) 32 ∗ memRegion (ss + 96#64) 24) ∗
            freeOnlyPool A lim ast sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved32Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ss) := by
  simp only [rustCliDeallocBudgetSpec] at hdealloc
  intro pCap pPtr kCap kPtr G s Frame hpc hrun hpres hx19
  rcases hpres with ⟨hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine SepWP.seq_state (mid := (blkPl_6).base + 188#64) (P_mid := fun sm =>
    (ssTail3HeadersAt_shared_lb ss pCap pPtr kCap kPtr G ∗
      sgnPinDealloc A.repAlloc kCap kPtr ∗
      vecPinDealloc A.repAlloc ⟨G.alice.cap, G.alice.ptr⟩) ∗
    freeOnlyPool A lim ast sm ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => Saved32Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss)
    ?_ ?_
  · refine SepWP.unpack_freeOnlyPool (by sep_focus) fun evs hevs => ?_
    dsimp only [ssTail3HeadersAt_shared_lb, sgnPinDealloc, vecPinDealloc]
    by_cases hcap : pCap.slt 1#64 = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
    · wp_steps
      refine SepWP.fold_keep hevs (hk := ?_)
      wp_done
    · wp_steps
      refine SepWP.sync_pool (hk := ?_)
      rw [← hsp]
      wp_call hdealloc (pPtr, pCap.toNat, 1, M.stepEvents evs ast)
      have htr_d : sf.trace = s0.trace := (‹AllocCallPreserved _ sf›.2.1).trans htrace
      refine SepWP.fold_dealloc hevs pCap.toNat 1 (hk := ?_)
      refine weaken_pre_mid (by rw [hsp]; bi_entail) ?_
      wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine SepWP.seq_state (mid := (blkPl_6).base + 212#64) (P_mid := fun sm =>
      (ssTail3HeadersAt_shared_lb ss pCap pPtr kCap kPtr G ∗
        vecPinDealloc A.repAlloc ⟨G.alice.cap, G.alice.ptr⟩) ∗
      freeOnlyPool A lim ast sm ∗ stackAt fsp allocHookStack ∗ Frame)
      (Q := fun sm => Saved32Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss)
      ?_ ?_
    · refine SepWP.unpack_freeOnlyPool (by sep_focus) fun evs hevs => ?_
      dsimp only [ssTail3HeadersAt_shared_lb, sgnPinDealloc, vecPinDealloc]
      by_cases hcap : kCap.slt 1#64 = true <;>
        simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
      · wp_steps
        refine SepWP.fold_keep hevs (hk := ?_)
        wp_done
      · wp_steps
        refine SepWP.sync_pool (hk := ?_)
        rw [← hsp_1]
        wp_call hdealloc (kPtr, kCap.toNat, 1, M.stepEvents evs ast)
        have htr_d : sf.trace = s0.trace := (‹AllocCallPreserved _ sf›.2.1).trans htrace_1
        refine SepWP.fold_dealloc hevs kCap.toNat 1 (hk := ?_)
        refine weaken_pre_mid (by rw [hsp_1]; bi_entail) ?_
        wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      have hstep3 : SepWP ((blkPC_6).rebase (blkPl_6).base H) ((blkPl_6).base + 232#64) s2
          ((ssTail3HeadersAt_shared_lb ss pCap pPtr kCap kPtr G ∗
            vecPinDealloc A.repAlloc ⟨G.alice.cap, G.alice.ptr⟩) ∗
            freeOnlyPool A lim ast s2 ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ ssTail3HeadersAt_shared_lb ss pCap pPtr kCap kPtr G ∗
              freeOnlyPool A lim ast sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
            Saved32Preserved s0 sm fsp ∧
            sm.readReg64 .x19 = ss) := by
        refine SepWP.unpack_freeOnlyPool (by sep_focus) fun evs hevs => ?_
        dsimp only [ssTail3HeadersAt_shared_lb, vecPinDealloc]
        by_cases hcap : (G.alice.cap == 0#64) = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
        · wp_steps
          refine SepWP.fold_keep hevs (hk := ?_)
          wp_done
        · wp_steps
          refine SepWP.sync_pool (hk := ?_)
          rw [← hsp_2]
          wp_call hdealloc (G.alice.ptr, G.alice.cap.toNat, 1, M.stepEvents evs ast)
          have htr_d : sf.trace = s0.trace := (‹AllocCallPreserved _ sf›.2.1).trans htrace_2
          refine SepWP.fold_dealloc hevs G.alice.cap.toNat 1 (hk := ?_)
          refine weaken_pre_mid (by rw [hsp_2]; bi_entail) ?_
          wp_done
      exact SepWP.mono hstep3 (fun sm Pm _ _ h =>
        ⟨Entails.trans h.1 (sepConj_mono_left (ssTail3HeadersAt_entails_memRegions ss pCap pPtr kCap kPtr G)), h.2⟩)

/-- Block `6` (`core::ptr::drop_glue::<SessionStructure> [local#1]`) meets
`dropSessionStructureLocal1Spec M A lim` under `[LibsignalPlacement]`, given `subroutine_ok` for
`__rust_dealloc`, `drop_glue<Vec<MessageKey>>`, and `drop_glue<Vec<Chain>>`. -/
theorem drop_session_structure_local1_placed_ok_of_dealloc_and_drops [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc_raw : subroutine_ok ((blkPC_6).rebase (blkPl_6).base H)
      (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hdrop_mk_raw : subroutine_ok ((blkPC_6).rebase (blkPl_6).base H)
      (lsmpl.base 3) (withLsCodeLoaded lsmpl (dropVecMessageKeySpec M A lim)))
    (hdrop_vc_raw : subroutine_ok ((blkPC_6).rebase (blkPl_6).base H)
      (lsmpl.base 2) (withLsCodeLoaded lsmpl (dropVecChainSpec M A lim))) :
    subroutine_ok ((blkPC_6).rebase (blkPl_6).base H) (blkPl_6).base
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal1Spec M A lim)) := by
  simp only [withLsCodeLoaded, dropSessionStructureLocal1Spec]
  have hdealloc := hdealloc_raw
  simp only [rustCliDeallocBudgetSpec] at hdealloc
  have hdrop_vc := hdrop_vc_raw
  simp only [withLsCodeLoaded, dropVecChainSpec] at hdrop_vc
  wp_init x s0
  rcases x with ⟨⟨ss, G, st⟩, ast⟩
  have hfirst3 := drop_ss_local1_placed_first3 (ast := ast) hdealloc_raw
  have hsender := drop_ss_local1_placed_sender (ast := ast) hdealloc_raw hdrop_mk_raw
  have htail3 := drop_ss_local1_placed_tail3 (ast := ast) hdealloc_raw
  clear hdealloc_raw hdrop_mk_raw hdrop_vc_raw
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hx0 : s0.readReg64 (Reg.gpr 0#5) = ss := by assumption
  subst hx0
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_ss_local1_split s0.sp]
  cells_unfold
  wp_pull_exists
  rename_i v0 v1 v2 v3
  refine SepWP.weaken_pre
    (sepConj_mono_left (sessionStateAt_entails_dealloc A.repAlloc (s0.readReg64 (Reg.gpr 0#5)) G st)) ?_
  wp_pull_exists
  rename_i pCap pPtr kCap kPtr
  refine seq_state_lscl hcl0 (mid := (blkPl_6).base + 12#64)
    (P_mid := fun sm =>
      (ssFirst3HeadersAt_shared_lb (s0.readReg64 (Reg.gpr 0#5)) G ∗
        vecPinDealloc A.repAlloc ⟨G.localIk.cap, G.localIk.ptr⟩ ∗
        vecPinDealloc A.repAlloc ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
        vecPinDealloc A.repAlloc G.root) ∗
      freeOnlyPool A lim ast sm ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
      (optSenderChainAt A.repAlloc (s0.readReg64 (Reg.gpr 0#5) + 144#64) G.sender st.senderChain ∗
        vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (s0.readReg64 (Reg.gpr 0#5) + 72#64) G.chainsCap G.chainsPtr
          (G.chains.zip st.receiverChains) ∗
        (ssTail3HeadersAt_shared_lb (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
          sgnPinDealloc A.repAlloc pCap pPtr ∗ sgnPinDealloc A.repAlloc kCap kPtr ∗
          vecPinDealloc A.repAlloc ⟨G.alice.cap, G.alice.ptr⟩) ∗
        (((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
          ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ vecPinDealloc A.repAlloc G.pq) ∗
        memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗ memRegion (s0.sp - 4224#64) 96 ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v3)))
    (Q := fun sm => Saved32Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x0 = s0.readReg64 (Reg.gpr 0#5))
    ?_ ?_
  · rw [stackAt_dropVecChain_split_alloc (s0.sp - 32#64)]
    wp_steps_sync_pool ((blkPl_6).base + 12#64)
    simp only [State.setMem_setMem]
    apply SepWP.fold (freeOnlyPool_intro A lim ast _) (by sep_focus)
    refine weaken_pre_mid (by dsimp only [ssFirst3HeadersAt_shared_lb, ssTail3HeadersAt_shared_lb, Reg.x19, Reg.lr, Reg.fp]; sep_interval) ?_
    wp_done
  · intro s1 hpc1 hrun1 hcl1 ⟨hpres1, hx0_1⟩
    refine seq_state_lscl hcl1 (mid := (blkPl_6).base + 76#64)
      (P_mid := fun sm =>
        optSenderChainAt A.repAlloc (s0.readReg64 (Reg.gpr 0#5) + 144#64) G.sender st.senderChain ∗
        freeOnlyPool A lim ast sm ∗ stackAt (s0.sp - 32#64) dropVecMessageKeyStack ∗
        (vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (s0.readReg64 (Reg.gpr 0#5) + 72#64) G.chainsCap G.chainsPtr
          (G.chains.zip st.receiverChains) ∗
        (ssTail3HeadersAt_shared_lb (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
          sgnPinDealloc A.repAlloc pCap pPtr ∗ sgnPinDealloc A.repAlloc kCap kPtr ∗
          vecPinDealloc A.repAlloc ⟨G.alice.cap, G.alice.ptr⟩) ∗
        (((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
          ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ vecPinDealloc A.repAlloc G.pq) ∗
        (memRegion (s0.readReg64 (Reg.gpr 0#5)) 24 ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 24#64) 24 ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 48#64) 24) ∗
        memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗ memRegion (s0.sp - 4224#64) 48 ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v3)))
      (Q := fun sm => Saved32Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = s0.readReg64 (Reg.gpr 0#5))
      ?_ ?_
    · refine SepWP.mono
        (hfirst3 s0 (s0.sp - 32#64) (s0.readReg64 (Reg.gpr 0#5)) hfsp_align G s1 _
          hpc1 hrun1 hpres1 hx0_1) ?_
      intro sm Pm _ _ h
      refine ⟨Entails.trans h.1 ?_, h.2⟩
      rw [stackAt_dropVecMessageKey_split_alloc (s0.sp - 32#64)]
      sep_interval
    · intro s2 hpc2 hrun2 hcl2 ⟨hpres2, hx19_2⟩
      refine seq_state_lscl hcl2 (mid := (blkPl_6).base + 156#64)
        (P_mid := fun sm =>
          vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (s0.readReg64 (Reg.gpr 0#5) + 72#64) G.chainsCap G.chainsPtr
            (G.chains.zip st.receiverChains) ∗
          freeOnlyPool A lim ast sm ∗ stackAt (s0.sp - 32#64) dropVecChainStack ∗
          ((ssTail3HeadersAt_shared_lb (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
            sgnPinDealloc A.repAlloc pCap pPtr ∗ sgnPinDealloc A.repAlloc kCap kPtr ∗
            vecPinDealloc A.repAlloc ⟨G.alice.cap, G.alice.ptr⟩) ∗
          (((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
            ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ vecPinDealloc A.repAlloc G.pq) ∗
          (memRegion (s0.readReg64 (Reg.gpr 0#5)) 24 ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 24#64) 24 ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 48#64) 24) ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 144#64) 104 ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v3)))
        (Q := fun sm => Saved32Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = s0.readReg64 (Reg.gpr 0#5))
        ?_ ?_
      · refine SepWP.mono
          (hsender s0 (s0.sp - 32#64) (s0.readReg64 (Reg.gpr 0#5)) hfsp_align G.sender st.senderChain s2 _
            hpc2 hrun2 hcl2 hpres2 hx19_2) ?_
        intro sm Pm _ _ h
        refine ⟨Entails.trans h.1 ?_, h.2⟩
        rw [stackAt_dropVecChain_split_mk (s0.sp - 32#64)]
        bi_entail
      · intro s3 hpc3 hrun3 hcl3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
        refine seq_state_lscl hcl3 (mid := (blkPl_6).base + 164#64)
          (P_mid := fun sm =>
            (ssTail3HeadersAt_shared_lb (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
              sgnPinDealloc A.repAlloc pCap pPtr ∗ sgnPinDealloc A.repAlloc kCap kPtr ∗
              vecPinDealloc A.repAlloc ⟨G.alice.cap, G.alice.ptr⟩) ∗
            freeOnlyPool A lim ast sm ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
            ((((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
              ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
              memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ vecPinDealloc A.repAlloc G.pq) ∗
            (memRegion (s0.readReg64 (Reg.gpr 0#5)) 24 ∗
              memRegion (s0.readReg64 (Reg.gpr 0#5) + 24#64) 24 ∗
              memRegion (s0.readReg64 (Reg.gpr 0#5) + 48#64) 24) ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 72#64) 24 ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 144#64) 104 ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗ memRegion (s0.sp - 4224#64) 96 ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v3)))
          (Q := fun sm => Saved32Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = s0.readReg64 (Reg.gpr 0#5))
          ?_ ?_
        · refine SepWP.unpack_freeOnlyPool (by sep_focus) fun evs hevs => ?_
          wp_steps
          refine SepWP.sync_pool (hk := ?_)
          rw [← hsp_3]
          wp_call hdrop_vc (⟨s0.readReg64 (Reg.gpr 0#5) + 72#64, G.chainsCap, G.chainsPtr, G.chains.zip st.receiverChains⟩, M.stepEvents evs ast)
          have htr_c : sf.trace = s0.trace := (by assumption : sf.trace = _).trans htrace_3
          refine SepWP.fold_append hevs (hk := ?_)
          refine weaken_pre_mid (by
            rw [hsp_3, stackAt_dropVecChain_split_alloc (s0.sp - 32#64)]
            dsimp only [ssTail3HeadersAt_shared_lb]; sep_interval) ?_
          wp_done
        · intro s4 hpc4 hrun4 hcl4 ⟨hpres4, hx19_4⟩
          refine seq_state_lscl hcl4 (mid := (blkPl_6).base + 232#64)
            (P_mid := fun sm =>
              ((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
              ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
              memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ vecPinDealloc A.repAlloc G.pq ∗
              (memRegion (s0.readReg64 (Reg.gpr 0#5)) 24 ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 24#64) 24 ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 48#64) 24 ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 72#64) 24 ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 96#64) 24 ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 144#64) 104 ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 248#64) 48 ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 296#64) 32 ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16) ∗
              freeOnlyPool A lim ast sm ∗ stackAt (s0.sp - 32#64) dropVecChainStack ∗
              ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
              ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v3))
            (Q := fun sm => Saved32Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = s0.readReg64 (Reg.gpr 0#5))
            ?_ ?_
          · refine SepWP.mono
              (htail3 s0 (s0.sp - 32#64) (s0.readReg64 (Reg.gpr 0#5)) hfsp_align pCap pPtr kCap kPtr G s4 _
                hpc4 hrun4 hpres4 hx19_4) ?_
            intro sm Pm _ _ h
            refine ⟨Entails.trans h.1 ?_, h.2⟩
            rw [stackAt_dropVecChain_split_alloc (s0.sp - 32#64)]
            sep_interval
          · intro s5 hpc5 hrun5 _ ⟨⟨hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hsp_5, htrace_5, hvregs_5⟩, hx19_5⟩
            refine SepWP.unpack_freeOnlyPool (by sep_focus) fun evs hevs => ?_
            dsimp only [vecPinDealloc]
            cases hcap : (G.pq.cap == 0#64) <;>
              simp only [Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
            · wp_steps
              refine SepWP.sync_pool (hk := ?_)
              refine SepWP.weaken_pre (P' :=
                memRegion (s0.readReg64 (Reg.gpr 0#5)) 344 ∗
                A.pool lim (M.stepEvents evs ast) _ ∗
                memRegion (s0.sp - 4224#64) 128 ∗ stackAt s0.sp allocHookStack ∗
                (A.live G.pq.ptr G.pq.cap.toNat 1 ∗ memRegion G.pq.ptr G.pq.cap.toNat))
                (by
                  rw [show memRegion (s0.sp - 4224#64) 128 ∗ (stackAt s0.sp allocHookStack ∗
                        (A.live G.pq.ptr G.pq.cap.toNat 1 ∗ memRegion G.pq.ptr G.pq.cap.toNat)) =
                      (memRegion (s0.sp - 4224#64) 128 ∗ stackAt s0.sp allocHookStack) ∗
                        (A.live G.pq.ptr G.pq.cap.toNat 1 ∗ memRegion G.pq.ptr G.pq.cap.toNat) from
                      (sepConj_assoc _ _ _).symm,
                    tail_stack_128_from_bottom s0.sp]
                  sep_interval) ?_
              wp_call hdealloc (G.pq.ptr, G.pq.cap.toNat, 1, M.stepEvents evs ast)
              have htr_d : sf.trace = s0.trace := (‹AllocCallPreserved _ sf›.2.1).trans htrace_5
              refine SepWP.fold_dealloc hevs G.pq.cap.toNat 1 (hk := ?_)
              refine SepWP.finish_ss_local1 A lim ast (s0 := s0) (s0.readReg64 (Reg.gpr 0#5)) s0.sp ?_ htr_d fun evs_f ⟨htr_f, hevs_f⟩ => ?_
              · rw [← stack_128_eq_ss_local1 s0.sp]
                bi_entail
              · wp_done
            · wp_steps
              refine SepWP.fold_keep hevs (hk := ?_)
              refine SepWP.finish_ss_local1 A lim ast (s0 := s0) (s0.readReg64 (Reg.gpr 0#5)) s0.sp ?_
                (by simpa [wp_norm, arm64_norm] using htrace_5) fun evs_f ⟨htr_f, hevs_f⟩ => ?_
              · rw [stackAt_ss_local1_split s0.sp]
                sep_interval
              · wp_done

/-- Block `6` (`core::ptr::drop_glue::<SessionStructure> [local#1]`) meets
`dropSessionStructureLocal1Spec M A lim` under `[LibsignalPlacement]`. -/
theorem drop_session_structure_local1_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_6).rebase (blkPl_6).base H) (blkPl_6).base
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal1Spec M A lim)) := by
  have hmk0 : subroutine_ok ((blkPC_3).rebase (blkPl_3).base H)
      (blkPl_3).base (dropVecMessageKeySpec M A lim) :=
    drop_vec_message_key_placed_ok h_dealloc
  have hmk := ls_subroutine_ok_of_block (callerProg := (blkPC_6).rebase (blkPl_6).base H)
    (subroutine_ok_withLsCodeLoaded_of_plain hmk0)
  have hvc := ls_subroutine_ok_of_block (callerProg := (blkPC_6).rebase (blkPl_6).base H)
    (drop_vec_chain_placed_ok h_dealloc)
  exact drop_session_structure_local1_placed_ok_of_dealloc_and_drops
    (ls_hook_ok_rustDealloc h_dealloc) hmk hvc

end LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Drops.Local1Budget
