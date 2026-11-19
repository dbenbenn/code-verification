/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.CommonBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.LoadRatchetProof -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.LoadRatchetSymBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.OnPanicTightBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatchBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244PlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatch
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Main

/-!
# Budget-Threaded Relocatable Segment S1 (`LoadRatchet`) Proofs

Proves relocatable `[LibsignalPlacement]` Segment S1 (`LoadRatchet`) seam contracts, tight-panic
epilogue-to-outcome combinators, and pinned free-envelope S1 theorems on block `130` over
`RustCliAllocBudget M`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.LoadRatchetProofBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
  (Crypto Mut SessionState SignalProtocolError TripleRatchet)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement LibsignalRoLoaded blkPC_57 blkPl_57 lsmpl)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalSessionRepr
  (RatchetGhost chainAt msgTypeByte ratchetAt)
open CryptoVerification.LibsignalTripleRatchetRepr
  (SessionGhost SignalMessageGhost UuidParser decryptDraws errResultAt errTag
   protocolAddressAt sessionStateAt signalMessageAt speAt speAt_entails_speFnAt speFnAt
   tapeAfter utf8 uuidTryParse vecResultAt)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel TrGhost TryDecryptGhost decResultFnAt logOff rootStack trAt trResultAt withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Decrypt
  (speTag tryDecryptCommonHeap tryDecryptSavedRegs tryDecryptSubStack)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup (blkPC_131 blkPl_131 decRel_afterTrFrom fromSessionState_error_imp fromSessionState_error_imp_fn loadRatchet_err_stack_recombine loadRatchet_ok_stack_recombine reaches_pc_lsro retEpiloguePC_placed segFindChainPC_placed sepWP_to_reaches_pc sepWP_to_reaches_pc_with_midMeta_placed signalMessageAt_eq_counter_rest signalMessageNoCounterAt trAt_eq_cap_body_heap trBodyAt trHeapAt trHeapAt_facts tryDecryptDummyImg tryDecryptMidMeta_placed words4At words5At words32At)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup.ChainLookupFacts
  (elim_exists_words32_of_trBodyAt elim_s1_ok_stack_extract)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
  (SeamBudget TryDecryptEnvArgs tryDecryptEnvArgs)
open LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatchBudget
  (chainAt_atState_fn invalidMessageStrAt_atState optBoxU8At_atState
   protocolAddressAt_atState sessionStateAt_atState signalMessageAt_atState
   speAt_atState vecResultAt_atState vecU8_atState)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget
  (FindChainStatePlaced LoadRatchetStatePlaced
   tryDecryptFnRawSpecPlaced tryDecryptFnSpecPlaced
   tryDecryptRawSpecPlaced tryDecryptSpecPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.OnPanicTightBudget
  (reaches_outcome_fn_tight_weaken_placed reaches_outcome_tight_weaken_placed
   tryDecryptFnRawSpecTightPlaced tryDecryptFnSpecTightPlaced
   tryDecryptRawSpecTightPlaced tryDecryptSpecTightPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux
  (s1InitCaps trGhostCaps)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.CommonBudget
  (FindChainStatePlaced_of_placed FindChainState_placed
   LoadRatchetStatePlaced_to_placed LoadRatchetState_placed
   tryDecryptDummyImg_eq_placedImg tryDecrypt_epilogue_394_wp_placed)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.LoadRatchetSymBudget
  (loadRatchet_call_trFrom_reaches_placed loadRatchet_err_wp_placed loadRatchet_ok_wp_placed)
open LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244PlacedBudget
  (trFromPlacedSpec)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. `A.atState lim st s ↦ A.repAlloc` Representation Normalizers -/

theorem signalMessageNoCounterAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (g : SignalMessageGhost) (a : BitVec 64) (m : CryptoGames.LibsignalSession.SignalMessage) :
    signalMessageNoCounterAt (A.atState lim st s) g a m =
      signalMessageNoCounterAt A.repAlloc g a m := by
  unfold signalMessageNoCounterAt; rw [optBoxU8At_atState]; rfl

theorem ratchetAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (self : BitVec 64) (G : RatchetGhost) (rst : CryptoGames.LibsignalSession.RatchetState) :
    ratchetAt (A.atState lim st s) self G rst = ratchetAt A.repAlloc self G rst := by
  unfold ratchetAt; rw [chainAt_atState_fn]; rfl

theorem trAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (t : BitVec 64) (G : TrGhost) (tr : TripleRatchet (List (BitVec 8))) :
    trAt (A.atState lim st s) t G tr = trAt A.repAlloc t G tr := by
  unfold trAt; rw [ratchetAt_atState]; rfl

theorem errResultAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (fnName : List (BitVec 8)) (size : Nat) (r : BitVec 64) (e : SignalProtocolError) :
    errResultAt (A.atState lim st s) fnName size r e = errResultAt A.repAlloc fnName size r e := by
  unfold errResultAt; rw [speAt_atState]

theorem trResultAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (r : BitVec 64) (G : SessionGhost)
    (res : Except SignalProtocolError (TripleRatchet (List (BitVec 8)))) :
    trResultAt (A.atState lim st s) r G res = trResultAt A.repAlloc r G res := by
  cases res with
  | ok _ => unfold trResultAt; simp only [trAt_atState]
  | error e => exact errResultAt_atState A lim st s (utf8 "decrypt") 264 r e

theorem speFnAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (fnName : List (BitVec 8)) (a : BitVec 64) (e : SignalProtocolError) :
    speFnAt (A.atState lim st s) fnName a e = speFnAt A.repAlloc fnName a e := by
  cases e <;> simp only [speFnAt, speAt_atState, invalidMessageStrAt_atState, vecU8_atState]

theorem decResultFnAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (r : BitVec 64) (res : Except SignalProtocolError (List (BitVec 8))) :
    decResultFnAt (A.atState lim st s) r res = decResultFnAt A.repAlloc r res := by
  cases res with
  | ok _ => simp only [decResultFnAt, vecU8_atState]
  | error e => exact speFnAt_atState A lim st s _ _ e

/-! ## 2. Tight-Panic Epilogue-to-Outcome Combinators (Block `130`) -/

theorem loadRatchet_after_call_ok_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {ctl : BitVec 64}
    {H : String → Option (State → State)}
    {x : TryDecryptGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {R : SepProp} {s0 s : State}
    (hpc : s.pc = (blkPl_131).base + 484#64) (hmeta : tryDecryptMidMeta_placed s0 s)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64)
    (hx21 : s.readReg64 .x21 = x.ss)
    (hx22 : s.readReg64 .x22 = x.msgA)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 0x500#64)
    (hx24 : (s.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s.readReg64 .x25 = x.locA)
    (hm : s.mem ⊨
      sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
      trResultAt A.repAlloc ((s0.sp - 1504#64) + 0x190#64) x.G (.ok tr) ∗
      memRegion x.ret 48 ∗ memRegion (s0.sp - 1504#64) 0x30 ∗
      (((s0.sp - 1504#64) + 0x30#64) ↦₆₄ x.remA) ∗
      memRegion ((s0.sp - 1504#64) + 0x38#64) 0x158 ∗
      memRegion ((s0.sp - 1504#64) + 0x298#64) 0x2e8 ∗
      tryDecryptCommonHeap (A.atState lim st s) ctl tryDecryptDummyImg x 0 s0 ∗ R) :
    reaches_pc ((blkPC_131).rebase (blkPl_131).base H) segFindChainPC_placed s
      (fun s' => ∃ trG, trGhostCaps trG = s1InitCaps x.G ∧
        FindChainState_placed A lim st ctl x trG tr st1 R s0 s') := by
  let sp := s0.sp - 1504#64
  set A_s : RustAlloc := A.atState lim st s
  have hm_as : s.mem ⊨
      sessionStateAt A_s x.ss x.G.afterTrFrom st1 ∗
      trResultAt A_s (sp + 0x190#64) x.G (.ok tr) ∗
      memRegion x.ret 48 ∗ memRegion sp 0x30 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
      memRegion (sp + 0x38#64) 0x158 ∗ memRegion (sp + 0x298#64) 0x2e8 ∗
      tryDecryptCommonHeap A_s ctl tryDecryptDummyImg x 0 s0 ∗ R := by
    dsimp only [A_s, sp]
    rw [sessionStateAt_atState, trResultAt_atState]
    exact hm
  change s.mem ⊨
    sessionStateAt A_s x.ss x.G.afterTrFrom st1 ∗
    (∃∗ senderPad : List (BitVec 8),
      trAt A_s (sp + 0x190#64) ⟨⟨x.G.chainsCap, x.G.chainsPtr, x.G.chains, senderPad⟩, x.G.pq⟩ tr) ∗
    memRegion x.ret 48 ∗ memRegion sp 0x30 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
    memRegion (sp + 0x38#64) 0x158 ∗ memRegion (sp + 0x298#64) 0x2e8 ∗
    tryDecryptCommonHeap A_s ctl tryDecryptDummyImg x 0 s0 ∗ R at hm_as
  have hm_ex : s.mem ⊨
      (∃∗ senderPad : List (BitVec 8),
        trAt A_s (sp + 0x190#64) ⟨⟨x.G.chainsCap, x.G.chainsPtr, x.G.chains, senderPad⟩, x.G.pq⟩ tr) ∗
      (sessionStateAt A_s x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗ memRegion sp 0x30 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x38#64) 0x158 ∗
       memRegion (sp + 0x298#64) 0x2e8 ∗ tryDecryptCommonHeap A_s ctl tryDecryptDummyImg x 0 s0 ∗ R) := by
    convert hm_as using 1; sep_ac_rfl
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm_ex
  rcases hm_ex with ⟨senderPad, hm_tr⟩
  let trG : TrGhost := ⟨⟨x.G.chainsCap, x.G.chainsPtr, x.G.chains, senderPad⟩, x.G.pq⟩
  change s.mem ⊨ trAt A_s (sp + 0x190#64) trG tr ∗
    (sessionStateAt A_s x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗ memRegion sp 0x30 ∗
     ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x38#64) 0x158 ∗
     memRegion (sp + 0x298#64) 0x2e8 ∗ tryDecryptCommonHeap A_s ctl tryDecryptDummyImg x 0 s0 ∗ R) at hm_tr
  rw [trAt_eq_cap_body_heap, show sp + 0x190#64 + 8#64 = sp + 0x198#64 by bv_omega] at hm_tr
  have hm_heap : s.mem ⊨ trHeapAt A_s trG tr ∗
      (((sp + 0x190#64) ↦₆₄ trG.ratchet.chainsCap) ∗ trBodyAt (sp + 0x198#64) trG tr ∗
       sessionStateAt A_s x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗ memRegion sp 0x30 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x38#64) 0x158 ∗
       memRegion (sp + 0x298#64) 0x2e8 ∗ tryDecryptCommonHeap A_s ctl tryDecryptDummyImg x 0 s0 ∗ R) := by
    convert hm_tr using 1; sep_ac_rfl
  obtain ⟨hpad, hcap⟩ := trHeapAt_facts hm_heap
  have hm_body : s.mem ⊨ trBodyAt (sp + 0x198#64) trG tr ∗
      (trHeapAt A_s trG tr ∗ ((sp + 0x190#64) ↦₆₄ trG.ratchet.chainsCap) ∗
       sessionStateAt A_s x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗ memRegion sp 0x30 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x38#64) 0x158 ∗
       memRegion (sp + 0x298#64) 0x2e8 ∗ tryDecryptCommonHeap A_s ctl tryDecryptDummyImg x 0 s0 ∗ R) := by
    convert hm_heap using 1; sep_ac_rfl
  refine elim_exists_words32_of_trBodyAt hpad hm_body
    fun w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
        w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 H_tr hm_w hent_tr => ?_
  have hm_stk : s.mem ⊨
      (memRegion sp 0x30 ∗ memRegion (sp + 0x38#64) 0x158 ∗ memRegion (sp + 0x298#64) 0x2e8) ∗
      (words32At (sp + 0x198#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
         w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗
       H_tr ∗ trHeapAt A_s trG tr ∗ ((sp + 0x190#64) ↦₆₄ trG.ratchet.chainsCap) ∗
       sessionStateAt A_s x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗ tryDecryptCommonHeap A_s ctl tryDecryptDummyImg x 0 s0 ∗ R) := by
    convert hm_w using 1; sep_ac_rfl
  refine elim_s1_ok_stack_extract hm_stk
    fun g20 d_cap g2a0 t0 t1 t2 t3 t4 t5
        d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
        d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 g28 g2ac hm_stk2 => ?_
  unfold tryDecryptCommonHeap at hm_stk2
  rw [signalMessageAt_eq_counter_rest] at hm_stk2
  let F_ok : SepProp :=
    H_tr ∗ trHeapAt A_s trG tr ∗ sessionStateAt A_s x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗
    memRegion sp 0x20 ∗ memRegion (sp + 0x2c#64) 4 ∗ memRegion (sp + 0x140#64) 0x50 ∗
    memRegion (sp + 0x298#64) 8 ∗ memRegion (sp + 0x2a8#64) 4 ∗ memRegion (sp + 0x2ad#64) 0x253 ∗
    memRegion (sp + 0x530#64) 0x50 ∗ protocolAddressAt A_s x.rem x.remA ∗
    protocolAddressAt A_s x.loc x.locA ∗ signalMessageNoCounterAt A_s x.msgG x.msgA x.msg ∗
    tapeAfter ctl x.cur x.rest 0 ∗ logOff tryDecryptDummyImg ∗
    stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗ tryDecryptSavedRegs s0.sp s0 ∗ A_s.pool ∗ R
  have hm_pre : s.mem ⊨
      (((sp + 0x20#64) ↦₆₄ g20) ∗ ((sp + 0x28#64) ↦₃₂ g28) ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
       ((sp + 0x38#64) ↦₆₄ d_cap) ∗
       words32At (sp + 0x40#64) d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
         d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 ∗
       ((sp + 0x190#64) ↦₆₄ trG.ratchet.chainsCap) ∗
       words32At (sp + 0x198#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
         w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗
       ((sp + 0x2a0#64) ↦₆₄ g2a0) ∗ ((sp + 0x2ac#64) ↦₈ g2ac) ∗
       words4At (sp + 0x500#64) t0 t1 t2 t3 ∗ ((sp + 0x520#64) ↦₆₄ t4) ∗ ((sp + 0x528#64) ↦₆₄ t5) ∗
       ((x.msgA + 0x68#64) ↦₃₂ x.msg.counter)) ∗ F_ok := by
    dsimp only [F_ok, sp] at hm_stk2 ⊢; convert hm_stk2 using 1; sep_ac_rfl
  have hwp := loadRatchet_ok_wp_placed (H := H)
    (cap := trG.ratchet.chainsCap) (locA := x.locA) (remA := x.remA) (msgA := x.msgA)
    (g20 := g20) (d_cap := d_cap) (g2a0 := g2a0)
    (t0 := t0) (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) (t5 := t5)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4) (w5 := w5) (w6 := w6) (w7 := w7)
    (w8 := w8) (w9 := w9) (w10 := w10) (w11 := w11) (w12 := w12) (w13 := w13) (w14 := w14) (w15 := w15)
    (w16 := w16) (w17 := w17) (w18 := w18) (w19 := w19) (w20 := w20) (w21 := w21) (w22 := w22) (w23 := w23)
    (w24 := w24) (w25 := w25) (w26 := w26) (w27 := w27) (w28 := w28) (w29 := w29) (w30 := w30) (w31 := w31)
    (d0 := d0) (d1 := d1) (d2 := d2) (d3 := d3) (d4 := d4) (d5 := d5) (d6 := d6) (d7 := d7)
    (d8 := d8) (d9 := d9) (d10 := d10) (d11 := d11) (d12 := d12) (d13 := d13) (d14 := d14) (d15 := d15)
    (d16 := d16) (d17 := d17) (d18 := d18) (d19 := d19) (d20 := d20) (d21 := d21) (d22 := d22) (d23 := d23)
    (d24 := d24) (d25 := d25) (d26 := d26) (d27 := d27) (d28 := d28) (d29 := d29) (d30 := d30) (d31 := d31)
    (counter := x.msg.counter) (g28 := g28) (g2ac := g2ac)
    hcap hpc (tryDecryptMidMeta_placed.to_wpInv hmeta) hx20 hx22 hx23 hx25
  refine sepWP_to_reaches_pc_with_midMeta_placed hmeta hwp hm_pre ?_
  intro sf Pf hpcf ⟨b2ac, hPf, hvm_f, hwpInv_f, hx0_f, hx1_f, hx8_f,
    hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx27_f, hx28_f⟩ hcl_f hmf
  subst hPf
  have hcaps : trGhostCaps trG = s1InitCaps x.G := rfl
  have hA_eq : A.atState lim st sf = A_s := A.atState_eq_of_vmPreserved lim st hvm_f
  refine ⟨trG, hcaps, ?_⟩
  dsimp only [FindChainState_placed]
  rw [hA_eq]
  refine ⟨hpcf, hwpInv_f.to_midMeta_placed hcl_f, hx0_f, hx1_f, hx8_f,
    hx19_f.trans hx19, hx20_f.trans hx20, hx21_f.trans hx21, hx22_f.trans hx22, hx23_f.trans hx23,
    by change (sf.readReg64 (Reg.gpr 24#5)).setWidth 8 = _; rw [hx24_f]; exact hx24,
    hx25_f, hx27_f, hx28_f, ?_⟩
  unfold tryDecryptCommonHeap
  rw [trAt_eq_cap_body_heap, show sp + 0x38#64 + 8#64 = sp + 0x40#64 by bv_omega,
      signalMessageAt_eq_counter_rest]
  have hmf_re : sf.mem ⊨
      (words32At (sp + 0x40#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
         w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗ H_tr) ∗
      (memRegion (sp + 0x140#64) 0x50 ∗ ((sp + 0x190#64) ↦₆₄ trG.ratchet.chainsCap) ∗
       words32At (sp + 0x198#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
         w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗
       memRegion (sp + 0x298#64) 8 ∗ ((sp + 0x2a0#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x2a8#64) 4 ∗
       ((sp + 0x2ac#64) ↦₈ b2ac) ∗ memRegion (sp + 0x2ad#64) 0x253 ∗
       words4At (sp + 0x500#64) w0 w1 w2 w3 ∗ ((sp + 0x520#64) ↦₆₄ w4) ∗ ((sp + 0x528#64) ↦₆₄ w5) ∗
       memRegion (sp + 0x530#64) 0x50) ∗
      (sessionStateAt A_s x.ss x.G.afterTrFrom st1 ∗ ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
       trHeapAt A_s trG tr ∗ memRegion x.ret 48 ∗ memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗
       ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
       protocolAddressAt A_s x.rem x.remA ∗ protocolAddressAt A_s x.loc x.locA ∗
       ((x.msgA + 0x68#64) ↦₃₂ x.msg.counter) ∗ signalMessageNoCounterAt A_s x.msgG x.msgA x.msg ∗
       tapeAfter ctl x.cur x.rest 0 ∗ logOff tryDecryptDummyImg ∗
       stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗ tryDecryptSavedRegs s0.sp s0 ∗ A_s.pool ∗ R) := by
    dsimp only [F_ok, sp] at hmf ⊢; convert hmf using 1; sep_ac_rfl
  have hmf2 := Satisfies.mono
    (sepConj_mono (hent_tr (sp + 0x40#64))
      (sepConj_mono_left
        (loadRatchet_ok_stack_recombine sp trG.ratchet.chainsCap x.remA b2ac
          w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31))) hmf_re
  dsimp only [sp] at hmf2 ⊢; convert hmf2 using 1; sep_ac_rfl

/-! ## 4. Budget-Threaded Segment `S1` (`LoadRatchet`) Seam Contracts & Theorems -/

@[expose] def S1SeamGenPlaced [LibsignalPlacement] {M : AllocCostModel} (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (s1ErrEnv : List AllocEvent → Prop) (s1OkEnv : TryDecryptGhost → List AllocEvent → Prop) : Prop :=
  ∀ (x : TryDecryptGhost) (st_init st : M.σ) (R : SepProp) (s0 s : State),
    LoadRatchetStatePlaced entry A lim st ctl x R s0 s → prog.CodeLoaded s.mem →
    match Mut.exec TripleRatchet.fromSessionState x.st with
    | (.error _, _) => SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st s1ErrEnv →
      reaches_outcome prog (tryDecryptSpecPlaced C A lim ctl parse S tdEnv) (x, st_init) R s0 s
    | (.ok tr, st1) => FitsEnv M lim st (s1OkEnv x) →
      ∃ s', Steps prog s s' ∧ ∃ evs trG, s1OkEnv x evs ∧
        FindChainStatePlaced entry A lim (M.stepEvents evs st) ctl x trG tr st1 R s0 s'

@[expose] def S1SeamTightGenPlaced [LibsignalPlacement] {M : AllocCostModel} (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (s1ErrEnv : List AllocEvent → Prop) (s1OkEnv : TryDecryptGhost → List AllocEvent → Prop) : Prop :=
  ∀ (x : TryDecryptGhost) (st_init st : M.σ) (R : SepProp) (s0 s : State),
    LoadRatchetStatePlaced entry A lim st ctl x R s0 s → prog.CodeLoaded s.mem →
    match Mut.exec TripleRatchet.fromSessionState x.st with
    | (.error _, _) => SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st s1ErrEnv →
      reaches_outcome prog (tryDecryptSpecTightPlaced C A lim ctl parse S tdEnv) (x, st_init) R s0 s
    | (.ok tr, st1) => FitsEnv M lim st (s1OkEnv x) →
      ∃ s', Steps prog s s' ∧ ∃ evs trG, s1OkEnv x evs ∧
        FindChainStatePlaced entry A lim (M.stepEvents evs st) ctl x trG tr st1 R s0 s'

@[expose] def S1SeamPinnedGenPlaced [LibsignalPlacement] {M : AllocCostModel} (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (s1ErrEnv : List AllocEvent → Prop) (s1OkEnv : TryDecryptGhost → List AllocEvent → Prop) : Prop :=
  ∀ (x : TryDecryptGhost) (st_init st : M.σ) (R : SepProp) (s0 s : State),
    LoadRatchetStatePlaced entry A lim st ctl x R s0 s → prog.CodeLoaded s.mem →
    match Mut.exec TripleRatchet.fromSessionState x.st with
    | (.error _, _) => SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st s1ErrEnv →
      reaches_outcome prog (tryDecryptSpecPlaced C A lim ctl parse S tdEnv) (x, st_init) R s0 s
    | (.ok tr, st1) => FitsEnv M lim st (s1OkEnv x) →
      ∃ s', Steps prog s s' ∧ ∃ evs trG, s1OkEnv x evs ∧ trGhostCaps trG = s1InitCaps x.G ∧
        FindChainStatePlaced entry A lim (M.stepEvents evs st) ctl x trG tr st1 R s0 s'

@[expose] def S1SeamTightPinnedGenPlaced [LibsignalPlacement] {M : AllocCostModel} (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (s1ErrEnv : List AllocEvent → Prop) (s1OkEnv : TryDecryptGhost → List AllocEvent → Prop) : Prop :=
  ∀ (x : TryDecryptGhost) (st_init st : M.σ) (R : SepProp) (s0 s : State),
    LoadRatchetStatePlaced entry A lim st ctl x R s0 s → prog.CodeLoaded s.mem →
    match Mut.exec TripleRatchet.fromSessionState x.st with
    | (.error _, _) => SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st s1ErrEnv →
      reaches_outcome prog (tryDecryptSpecTightPlaced C A lim ctl parse S tdEnv) (x, st_init) R s0 s
    | (.ok tr, st1) => FitsEnv M lim st (s1OkEnv x) →
      ∃ s', Steps prog s s' ∧ ∃ evs trG, s1OkEnv x evs ∧ trGhostCaps trG = s1InitCaps x.G ∧
        FindChainStatePlaced entry A lim (M.stepEvents evs st) ctl x trG tr st1 R s0 s'

@[expose] def S1SeamGenXPlaced [LibsignalPlacement] {M : AllocCostModel} (prog : Program) (entry : BitVec 64)
    (C : Crypto) (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) (s1ErrEnv : List AllocEvent → Prop)
    (s1OkEnv : TryDecryptGhost → List AllocEvent → Prop) : Prop :=
  ∀ (x : TryDecryptGhost) (st_init st : M.σ) (R : SepProp) (s0 s : State),
    LoadRatchetStatePlaced entry A lim st ctl x R s0 s → prog.CodeLoaded s.mem →
    match Mut.exec TripleRatchet.fromSessionState x.st with
    | (.error _, _) => SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st s1ErrEnv →
      reaches_outcome prog (tryDecryptFnSpecPlaced C decFn A lim ctl parse S tdEnv) (x, st_init) R s0 s
    | (.ok tr, st1) => FitsEnv M lim st (s1OkEnv x) →
      ∃ s', Steps prog s s' ∧ ∃ evs trG, s1OkEnv x evs ∧
        FindChainStatePlaced entry A lim (M.stepEvents evs st) ctl x trG tr st1 R s0 s'

@[expose] def S1SeamTightGenXPlaced [LibsignalPlacement] {M : AllocCostModel} (prog : Program) (entry : BitVec 64)
    (C : Crypto) (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) (s1ErrEnv : List AllocEvent → Prop)
    (s1OkEnv : TryDecryptGhost → List AllocEvent → Prop) : Prop :=
  ∀ (x : TryDecryptGhost) (st_init st : M.σ) (R : SepProp) (s0 s : State),
    LoadRatchetStatePlaced entry A lim st ctl x R s0 s → prog.CodeLoaded s.mem →
    match Mut.exec TripleRatchet.fromSessionState x.st with
    | (.error _, _) => SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st s1ErrEnv →
      reaches_outcome prog (tryDecryptFnSpecTightPlaced C decFn A lim ctl parse S tdEnv) (x, st_init) R s0 s
    | (.ok tr, st1) => FitsEnv M lim st (s1OkEnv x) →
      ∃ s', Steps prog s s' ∧ ∃ evs trG, s1OkEnv x evs ∧
        FindChainStatePlaced entry A lim (M.stepEvents evs st) ctl x trG tr st1 R s0 s'

@[expose] def S1SeamPinnedGenXPlaced [LibsignalPlacement] {M : AllocCostModel} (prog : Program) (entry : BitVec 64)
    (C : Crypto) (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) (s1ErrEnv : List AllocEvent → Prop)
    (s1OkEnv : TryDecryptGhost → List AllocEvent → Prop) : Prop :=
  ∀ (x : TryDecryptGhost) (st_init st : M.σ) (R : SepProp) (s0 s : State),
    LoadRatchetStatePlaced entry A lim st ctl x R s0 s → prog.CodeLoaded s.mem →
    match Mut.exec TripleRatchet.fromSessionState x.st with
    | (.error _, _) => SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st s1ErrEnv →
      reaches_outcome prog (tryDecryptFnSpecPlaced C decFn A lim ctl parse S tdEnv) (x, st_init) R s0 s
    | (.ok tr, st1) => FitsEnv M lim st (s1OkEnv x) →
      ∃ s', Steps prog s s' ∧ ∃ evs trG, s1OkEnv x evs ∧ trGhostCaps trG = s1InitCaps x.G ∧
        FindChainStatePlaced entry A lim (M.stepEvents evs st) ctl x trG tr st1 R s0 s'

@[expose] def S1SeamTightPinnedGenXPlaced [LibsignalPlacement] {M : AllocCostModel} (prog : Program) (entry : BitVec 64)
    (C : Crypto) (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) (s1ErrEnv : List AllocEvent → Prop)
    (s1OkEnv : TryDecryptGhost → List AllocEvent → Prop) : Prop :=
  ∀ (x : TryDecryptGhost) (st_init st : M.σ) (R : SepProp) (s0 s : State),
    LoadRatchetStatePlaced entry A lim st ctl x R s0 s → prog.CodeLoaded s.mem →
    match Mut.exec TripleRatchet.fromSessionState x.st with
    | (.error _, _) => SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st s1ErrEnv →
      reaches_outcome prog (tryDecryptFnSpecTightPlaced C decFn A lim ctl parse S tdEnv) (x, st_init) R s0 s
    | (.ok tr, st1) => FitsEnv M lim st (s1OkEnv x) →
      ∃ s', Steps prog s s' ∧ ∃ evs trG, s1OkEnv x evs ∧ trGhostCaps trG = s1InitCaps x.G ∧
        FindChainStatePlaced entry A lim (M.stepEvents evs st) ctl x trG tr st1 R s0 s'

abbrev S1SeamFreePlaced [LibsignalPlacement] {M : AllocCostModel} (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (s1OkEnv : TryDecryptGhost → List AllocEvent → Prop) : Prop :=
  S1SeamGenPlaced prog entry C A lim ctl parse S tdEnv FreeOnlyEvs s1OkEnv

abbrev S1SeamTightFreePlaced [LibsignalPlacement] {M : AllocCostModel} (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (s1OkEnv : TryDecryptGhost → List AllocEvent → Prop) : Prop :=
  S1SeamTightGenPlaced prog entry C A lim ctl parse S tdEnv FreeOnlyEvs s1OkEnv

abbrev S1SeamPinnedFreePlaced [LibsignalPlacement] {M : AllocCostModel} (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (s1OkEnv : TryDecryptGhost → List AllocEvent → Prop) : Prop :=
  S1SeamPinnedGenPlaced prog entry C A lim ctl parse S tdEnv FreeOnlyEvs s1OkEnv

abbrev S1SeamFreeXPlaced [LibsignalPlacement] {M : AllocCostModel} (prog : Program) (entry : BitVec 64)
    (C : Crypto) (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (s1OkEnv : TryDecryptGhost → List AllocEvent → Prop) : Prop :=
  S1SeamGenXPlaced prog entry C decFn A lim ctl parse S tdEnv FreeOnlyEvs s1OkEnv

abbrev S1SeamTightFreeXPlaced [LibsignalPlacement] {M : AllocCostModel} (prog : Program) (entry : BitVec 64)
    (C : Crypto) (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (s1OkEnv : TryDecryptGhost → List AllocEvent → Prop) : Prop :=
  S1SeamTightGenXPlaced prog entry C decFn A lim ctl parse S tdEnv FreeOnlyEvs s1OkEnv

abbrev S1SeamPinnedFreeXPlaced [LibsignalPlacement] {M : AllocCostModel} (prog : Program) (entry : BitVec 64)
    (C : Crypto) (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (s1OkEnv : TryDecryptGhost → List AllocEvent → Prop) : Prop :=
  S1SeamPinnedGenXPlaced prog entry C decFn A lim ctl parse S tdEnv FreeOnlyEvs s1OkEnv

end LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.LoadRatchetProofBudget
