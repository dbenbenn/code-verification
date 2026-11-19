/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.AllocContractsMem4KBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Hooks2
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropLocal1Ext4KBudget -- proof-setup: allow-public-import
import ProofLib.SepLogic.WP
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public meta import Lean.Elab.Tactic -- shake: keep
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.ErrExit
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Drops.Common
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

/-!
# Budget-Threaded 4K-Stack `set_session_state` & Post-`tryDecrypt` Closure Blocks

1. Verifies `<SessionRecord>::set_session_state` against `setSessionStateSpec M A lim` on
   `tripleRatchetProgAtExt b ext` under `AllocContractsMem4KBudget b M A lim ext`.
2. Proves `VmPreserved`-strengthened post-`tryDecrypt` closure basic-block steps
   (`p3_seg7a_x24_ext_4k_vm_wp`, `p3_seg7b_x24_ext_vm_wp`, `p3_err_dup_ext_vm_wp`,
   `p3_err_tail_dup_a_ext_vm_wp`, `p3_err_tail_b_ext_vm_wp`).
-/

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.SetState4KBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees hiding
  dropSessionStructureLocal1Spec dropSessionStructureLocal2Spec setSessionStateSpec growOneSpeSpec
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.DropsCommon
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure

open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (sepWP_rebase_vmPreserved trapHooks)

open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropLocal1Ext4KBudget (dropSessionStructureLocal1SpecBase)

open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  setSessionStateSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyBudgetSpec)

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local wp_norm] sessionMemcpyBudgetSpec sessionMemcpySpec libcMemcpySpec

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

private theorem freeOnlyPool_sync {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {s sm : State} (hvm : VmPreserved s sm) :
    freeOnlyPool A lim st s = freeOnlyPool A lim st sm := by
  dsimp only [freeOnlyPool]
  congr 1
  funext evs
  rw [pool_sync A lim (M.stepEvents evs st) hvm]

private theorem freeOnlyPool_step_here {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {evs : List AllocEvent} (hevs : FreeOnlyEvs evs)
    (s : State) :
    A.pool lim (M.stepEvents evs st) s ⊢ freeOnlyPool A lim st s :=
  Entails.sepExists_right evs (Entails.pure_right hevs (Entails.refl _))

private theorem sepWP_sync_and_fold_freeOnlyPool {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {evs : List AllocEvent} (hevs : FreeOnlyEvs evs)
    {prev s : State} (hvm : VmPreserved prev s) :
    A.pool lim (M.stepEvents evs st) prev ⊢ freeOnlyPool A lim st s := by
  rw [pool_sync A lim (M.stepEvents evs st) hvm]
  exact freeOnlyPool_step_here A lim st hevs s

attribute [local irreducible] freeOnlyPool

private theorem stackAt_setSessionState_4k (sp : BitVec 64) :
    stackAt sp setSessionStateStack =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        stackAt (sp - 32#64) dropSessionStructureLocal1Stack ∗
        ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
        ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3)) := by
  have h1 := ProofLib.stackAt_split_cells sp dropSessionStructureLocal1Stack 4 (by decide)
  change stackAt sp setSessionStateStack =
    stackAt (sp - 32#64) dropSessionStructureLocal1Stack ∗ cells (sp - 32#64) 4 at h1
  have hc4 : cells (sp - 32#64) 4 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
        ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3)) := by
    cells_unfold
  rw [h1, hc4]
  simp only [sepExists_sepConj_right]

private theorem stackAt_setSessionState_split_alloc_4k (sp : BitVec 64) :
    stackAt sp setSessionStateStack =
      memRegion (sp - 4256#64) 160 ∗ stackAt sp allocHookStack := by
  rw [show setSessionStateStack = allocHookStack + 160 from rfl,
      stackAt_split_bottom' sp allocHookStack 160 (by decide)]

private theorem cells4_local1_entails_setSessionState_split_4k (sp v0 v1 v2 v3 : BitVec 64) :
    stackAt (sp - 32#64) dropSessionStructureLocal1Stack ∗
      ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
      ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3) ⊢
    memRegion (sp - 4256#64) 160 ∗ stackAt sp allocHookStack := by
  rw [← stackAt_setSessionState_split_alloc_4k sp, stackAt_setSessionState_4k sp]
  exact Entails.sepExists_right v0 (Entails.sepExists_right v1
    (Entails.sepExists_right v2 (Entails.sepExists_right v3 (Entails.refl _))))

private theorem pointsTo64_memRegion_336_eq_344_4k (r : BitVec 64) :
    (∃∗ v : BitVec 64, ((r + 24#64) ↦₆₄ v)) ∗ memRegion (r + 32#64) 336 =
      memRegion (r + 24#64) 344 := by
  have h := memRegion_split (r + 24#64) 8 336 (by decide)
  have hadd : r + 24#64 + 8#64 = r + 32#64 := by
    rw [BitVec.add_assoc]; rfl
  rw [show (8 + 336 : Nat) = 344 by rfl, hadd, ProofLib.memRegion_eight] at h
  exact h.symm

private theorem pointsTo64_memRegion_336_entails_344_4k (r v : BitVec 64) :
    ((r + 24#64) ↦₆₄ v) ∗ memRegion (r + 32#64) 336 ⊢ memRegion (r + 24#64) 344 := by
  rw [← pointsTo64_memRegion_336_eq_344_4k r]
  exact sepConj_mono_left (Entails.sepExists_intro v)

private theorem cap_add_one_beq_zero_eq_false_4k {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
  change cap.toNat + 1 = 0 at ht
  omega

private def vecGhostTailAt4K (A : RustAlloc) (g : VecGhost) (v : BitVec 64) : SepProp :=
  ((v + 8#64) ↦₆₄ g.ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length) ∗
  (if g.cap = 0 then emp
   else A.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗
     memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length))

private theorem vecGhostAt_unfold_cap_4k (A : RustAlloc) (g : VecGhost) (v : BitVec 64) :
    vecGhostAt A g v =
      ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
      (v ↦₆₄ g.cap) ∗ vecGhostTailAt4K A g v := by
  simp only [vecGhostAt, vecU8At, vecHeader, vecGhostTailAt4K]
  ac_rfl

private def sessionStateAfterLocalIk4K (A : RustAlloc) (ss : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) : SepProp :=
  ⌜PublicKey.deserialize G.localIk.bytes = Except.ok st.localIdentity.publicKey ∧
    (match st.remoteIdentity with
      | none => G.remoteIk.bytes = []
      | some ik => PublicKey.deserialize G.remoteIk.bytes = Except.ok ik.publicKey) ∧
    G.chains.length = st.receiverChains.length ∧
    G.pending.isSome = st.pendingPreKey ∧
    G.regIds.length = 8 ∧
    G.localIk.bytes.length = 33 ∧
    (st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)⌝ ∗
  vecGhostAt A G.remoteIk (ss + 24#64) ∗
  vecU8At A (ss + 48#64) G.root.cap G.root.ptr (CryptoGames.HMAC.keyToBytes32 st.rootKey) ∗
  vecAt A 104 8 (chainAt A) (ss + 72#64) G.chainsCap G.chainsPtr (G.chains.zip st.receiverChains) ∗
  vecGhostAt A G.alice (ss + 96#64) ∗
  vecU8At A (ss + 120#64) G.pq.cap G.pq.ptr st.pqRatchetState ∗
  optSenderChainAt A (ss + 144#64) G.sender st.senderChain ∗
  optTailVecAt A 48 (ss + 248#64) G.pending ∗
  optTailVecAt A 32 (ss + 296#64) G.kyber ∗
  ((ss + 328#64) ↦₃₂ st.sessionVersion) ∗
  ((ss + 332#64) ↦₃₂ st.previousCounter) ∗
  ((ss + 336#64) ↦ₛ G.regIds)

private theorem sessionStateAt_unfold_cap_4k (A : RustAlloc) (ss : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    sessionStateAt A ss G st =
      ⌜G.localIk.bytes.length ≤ G.localIk.cap.toNat ∧ G.localIk.cap.toNat < 2 ^ 63 ∧ G.localIk.ptr ≠ 0⌝ ∗
      (ss ↦₆₄ G.localIk.cap) ∗ vecGhostTailAt4K A G.localIk ss ∗
      sessionStateAfterLocalIk4K A ss G st := by
  unfold sessionStateAt sessionStateAfterLocalIk4K
  rw [vecGhostAt_unfold_cap_4k]
  ac_rfl

private def dropSessionStructureLocal1HeadSpec4K (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (DropSessionStructureGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.ss ∧
      x.G.localIk.bytes.length ≤ x.G.localIk.cap.toNat ∧
      x.G.localIk.cap.toNat < 2 ^ 63 ∧
      x.G.localIk.ptr ≠ 0⌝ ∗
      (x.ss ↦₆₄ x.G.localIk.cap) ∗ vecGhostTailAt4K A.repAlloc x.G.localIk x.ss ∗
      sessionStateAfterLocalIk4K A.repAlloc x.ss x.G x.st ∗
      A.pool lim st s ∗ stackAt s.sp dropSessionStructureLocal1Stack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ FreeOnlyEvs evs⌝ ∗
        memRegion x.ss 344 ∗ A.pool lim (M.stepEvents evs st) sf ∗
        stackAt s0.sp dropSessionStructureLocal1Stack

private def setSessionStateNoneSpec4K (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec ((BitVec 64 × BitVec 64 × List (BitVec 8)) × M.σ) where
  pre := fun ((record, src, bs), st) s =>
    ⌜s.readReg64 .x0 = record ∧ s.readReg64 .x1 = src ∧ bs.length = 344⌝ ∗
      ((record + 0x18#64) ↦₆₄ noneCap) ∗ memRegion (record + 0x20#64) 336 ∗
      (src ↦ₛ bs) ∗ A.pool lim st s ∗ stackAt s.sp setSessionStateStack
  post := fun ((record, src, bs), st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ((record + 0x18#64) ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ A.pool lim st sf ∗
      stackAt s0.sp setSessionStateStack

private def setSessionStateSomeStack4K (sp : BitVec 64) : SepProp :=
  ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
    stackAt (sp - 32#64) dropSessionStructureLocal1Stack ∗
    ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
    ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3)

private def setSessionStateSomeSpec4K (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec ((BitVec 64 × BitVec 64 × SessionGhost ×
      SessionState (List (BitVec 8)) × List (BitVec 8)) × M.σ) where
  pre := fun ((record, src, G, sessSt, bs), st) s =>
    ⌜s.readReg64 .x0 = record ∧ s.readReg64 .x1 = src ∧ bs.length = 344⌝ ∗
      sessionStateAt A.repAlloc (record + 0x18#64) G sessSt ∗
      (src ↦ₛ bs) ∗ A.pool lim st s ∗ setSessionStateSomeStack4K s.sp
  post := fun ((record, src, _G, _sessSt, bs), st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ((record + 0x18#64) ↦ₛ bs) ∗ (src ↦ₛ bs) ∗
      freeOnlyPool A lim st sf ∗ stackAt s0.sp setSessionStateStack

section ClosureVmBlocks

attribute [local irreducible] Program.fnOff

end ClosureVmBlocks

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.SetState4KBudget
