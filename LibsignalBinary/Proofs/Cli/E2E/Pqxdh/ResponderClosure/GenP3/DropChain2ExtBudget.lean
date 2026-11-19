/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetBase
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropChain2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.AllocContractsMem4KBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropChain2Ext
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget -- proof-setup: allow-public-import
public meta import Lean.Elab.Tactic -- shake: keep
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.Chain.Common
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Placed.PlacedCallSym

/-!
# Budget-Threaded `ext`-Parameterized `drop_chain2` on `tripleRatchetProgAtExt`

Proves `drop_proto_chain2_of_dealloc_ext`, `drop_chain2_of_dealloc_ext`, and
`drop_chain2_ok_ext` against `dropProtoChainSpec M A lim` and `dropChainSpec M A lim` on
`tripleRatchetProgAtExt b ext`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropChain2ExtBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters hiding dropChainSpec dropProtoChainSpec
open DropGlueFacts
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs PoolPreserved
  RustCliAllocBudget VmPreserved rustDeallocEvents rustCliDeallocBudgetSpecBase
)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (sepWP_rebase_vmPreserved trapHooks)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (
  dropChainSpecBase dropProtoChainSpecBase
)

attribute [local irreducible] Program.fetch Program.externAt?

private theorem sepWP_seg_rebase_vm {P : Program} {b : BitVec 64}
    {Hk : String → Option (State → State)}
    {mid target : BitVec 64} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop}
    (hseg : SepWP ((P.rebase b trapHooks).withSvc noSyscalls) mid s Pre
      (fun sm Pm => sm.tpidrEl0 = s.tpidrEl0 ∧
        (VmPreserved s sm → sm.pc = mid → sm.status = .Running →
          SepWP (P.rebase b Hk) target sm Pm post))) :
    SepWP (P.rebase b Hk) target s Pre post := by
  apply SepWP.of_reaches_pc
  intro R hm hL
  obtain ⟨sm, hsteps1, ⟨hpcm, hrunm, Pm, hPm, hvm, hcont⟩ | ⟨_, hoom⟩⟩ :=
    SepWP.to_reaches_pc (sepWP_rebase_vmPreserved hseg) hm hL
  · obtain ⟨sf, hsteps2, hout2⟩ :=
      SepWP.to_reaches_pc (hcont hvm hpcm hrunm) hPm (hsteps1.codeLoaded hL)
    exact ⟨sf, hsteps1.trans hsteps2, hout2⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

private theorem pool_sync {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {s sm : State} (hvm : VmPreserved s sm) :
    A.pool lim st s = A.pool lim st sm :=
  (A.pool_of_vmPreserved hvm).symm

private def freeOnlyPool {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) : SepProp :=
  ∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) s

private theorem freeOnlyPool_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) s) =
      freeOnlyPool A lim st s := rfl

private theorem freeOnlyPool_sync {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {s sm : State} (hvm : VmPreserved s sm) :
    freeOnlyPool A lim st s = freeOnlyPool A lim st sm := by
  dsimp only [freeOnlyPool]
  congr 1
  funext evs
  rw [pool_sync A lim (M.stepEvents evs st) hvm]

private theorem freeOnlyPool_intro {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    A.pool lim st s ⊢ freeOnlyPool A lim st s :=
  Entails.sepExists_right [] (Entails.pure_right FreeOnlyEvs.nil (Entails.refl _))

private theorem freeOnlyPool_dealloc_here {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {evs : List AllocEvent} (hevs : FreeOnlyEvs evs)
    (sz al : Nat) (s : State) :
    A.pool lim (M.stepEvents (rustDeallocEvents sz al) (M.stepEvents evs st)) s ⊢
      freeOnlyPool A lim st s := by
  dsimp only [freeOnlyPool]
  rw [← M.stepEvents_append evs (rustDeallocEvents sz al) st]
  exact Entails.sepExists_right (evs ++ rustDeallocEvents sz al)
    (Entails.pure_right (FreeOnlyEvs.append hevs (FreeOnlyEvs.singleton al sz)) (Entails.refl _))

private theorem sepWP_open_freeOnlyPool {prog : Program} {target : BitVec 64} {s : State}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {P R : SepProp} {post : State → SepProp → Prop}
    (hfoc : P = freeOnlyPool A lim st s ∗ R)
    (hk : ∀ evs : List AllocEvent, FreeOnlyEvs evs →
      SepWP prog target s (A.pool lim (M.stepEvents evs st) s ∗ R) post) :
    SepWP prog target s P post := by
  rw [hfoc]
  dsimp only [freeOnlyPool]
  apply SepWP.of_sepExists_left
  intro evs
  rw [sepConj_assoc]
  exact SepWP.pure_elim (hk evs)

attribute [local irreducible] freeOnlyPool

private theorem SepWP.seq_state {prog : Program} {mid target : BitVec 64} {s : State}
    {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q sm →
      SepWP prog target sm (P_mid sm) post) :
    SepWP prog target s P post := by
  apply SepWP.of_reaches_pc
  intro R hm hL
  obtain ⟨sm, hsteps1, ⟨hpcm, hrunm, Pm, hPm, hent, hq⟩ | ⟨_, hoom⟩⟩ :=
    SepWP.to_reaches_pc h1 hm hL
  · obtain ⟨sf, hsteps2, hout2⟩ :=
      SepWP.to_reaches_pc (SepWP.weaken_pre hent (h2 sm hpcm hrunm hq)) hPm (hsteps1.codeLoaded hL)
    exact ⟨sf, hsteps1.trans hsteps2, hout2⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

private theorem align_pre_state {prog : Program} {target : BitVec 64} {s : State}
    {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    (heq : P = P_mid s)
    (h : SepWP prog target s (P_mid s) (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm) :=
  heq ▸ h

private theorem chainOuterHeadersAt_entails_memRegions (a : BitVec 64) (g : ChainGhost)
    (ckCap ckPtr : BitVec 64) :
    chainOuterHeadersAt a g ckCap ckPtr ⊢ memRegion a 48 ∗ memRegion (a + 72#64) 32 :=
  DropGlueFacts.chainOuterHeadersAt_entails_memRegions a g ckCap ckPtr

private theorem vecAt_expose_loop_at_48 {α : Type} (A : RustAlloc) (sz align : Nat)
    (elem : α → BitVec 64 → SepProp) (a cap ptr : BitVec 64) (xs : List α) :
    vecAt A sz align elem (a + 48#64) cap ptr xs ⊢
      ⌜xs.length ≤ cap.toNat ∧ cap.toNat * sz < 2 ^ 63 ∧ xs.length * sz < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((a + 48#64) ↦₆₄ cap) ∗ ((a + 56#64) ↦₆₄ ptr) ∗
      ((a + 64#64) ↦₆₄ BitVec.ofNat 64 xs.length) ∗
      arrayAt elem sz ptr xs ∗
      (if cap = 0 then emp
       else A.live ptr (cap.toNat * sz) align ∗
         memRegion (ptr + BitVec.ofNat 64 (xs.length * sz)) ((cap.toNat - xs.length) * sz)) := by
  have h := vecAt_expose_loop A sz align elem (a + 48#64) cap ptr xs
  have h1 : (a + 48#64) + 8#64 = a + 56#64 := by bv_omega
  have h2 : (a + 48#64) + 16#64 = a + 64#64 := by bv_omega
  rwa [h1, h2] at h

private theorem post_loop_weaken_at_48 (A : RustAlloc) (a cap ptr : BitVec 64) (n : Nat)
    (hle : n ≤ cap.toNat) (hcap_lt : cap.toNat * 104 < 2 ^ 63) (Rest : SepProp) :
    ((a + 48#64) ↦₆₄ cap) ∗ ((a + 56#64) ↦₆₄ ptr) ∗ ((a + 64#64) ↦₆₄ BitVec.ofNat 64 n) ∗
      memRegion ptr (n * 104) ∗
      (if cap = 0 then emp
       else A.live ptr (cap.toNat * 104) 8 ∗
         memRegion (ptr + BitVec.ofNat 64 (n * 104)) ((cap.toNat - n) * 104)) ∗
      Rest ⊢
    ((a + 48#64) ↦₆₄ cap) ∗ (((a + 48#64) + 8#64) ↦₆₄ ptr) ∗ memRegion ((a + 48#64) + 16#64) 8 ∗
      (if cap == 0#64 then emp
       else A.live ptr (cap.toNat * 104) 8 ∗ memRegion ptr (cap.toNat * 104)) ∗
      Rest := by
  have h := post_loop_weaken A (a + 48#64) cap ptr n hle hcap_lt Rest
  have h1 : (a + 48#64) + 8#64 = a + 56#64 := by bv_omega
  have h2 : (a + 48#64) + 16#64 = a + 64#64 := by bv_omega
  rw [h1, h2] at h
  rw [h1, h2]
  exact h

private theorem tail_dealloc_chain_pre_weaken (v cap ptr : BitVec 64)
    (live outer pool : SepProp) (sp : BitVec 64) (fp lr x22 x21 x20 x19 : BitVec 64) :
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ memRegion (v + 16#64) 8 ∗
      live ∗ outer ∗ pool ∗
      stackAt (sp - 48#64) allocHookStack ∗
      ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
      ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    memRegion v 24 ∗ outer ∗ pool ∗
      memRegion (sp - 4144#64) 48 ∗ stackAt sp allocHookStack ∗ live := by
  have h1 := header_cells_entails_memRegion_24 v cap ptr
  have h2 :
      stackAt (sp - 48#64) allocHookStack ∗
        ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
        ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
      memRegion (sp - 4144#64) 48 ∗ stackAt sp allocHookStack := by
    rw [tail_stack_48_from_bottom sp]
    exact sepConj_mono_right (cells6_sub48_entails sp fp lr x22 x21 x20 x19)
  have hreord :
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ memRegion (v + 16#64) 8 ∗
        live ∗ outer ∗ pool ∗
        stackAt (sp - 48#64) allocHookStack ∗
        ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
        ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) =
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ memRegion (v + 16#64) 8) ∗
        (live ∗ outer ∗ pool ∗
         (stackAt (sp - 48#64) allocHookStack ∗
          ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
          ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
          ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19))) := by sep_ac_rfl
  rw [hreord]
  refine Entails.trans (sepConj_mono h1 (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right h2)))) ?_
  exact Entails.of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropChain2ExtBudget
