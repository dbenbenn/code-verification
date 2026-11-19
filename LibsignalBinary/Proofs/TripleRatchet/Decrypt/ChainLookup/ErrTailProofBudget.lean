/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.CommonBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.ErrTailProof
import LibsignalBinary.Proofs.TripleRatchet.Getters.ClearUnacknowledgedPreKeyMessageBudget
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.ErrTailSymBudget
import LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatchBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.Getters.ClearUnacknowledgedPreKeyMessage -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatch

/-!
# Budget-Threaded Relocatable `ErrTail` Contracts

Proves budget-threaded `[LibsignalPlacement]` `ErrTail` contracts (`errTail_all_steps_wp_placed`,
`errTail_placed_ok`, `errTail_placed_ok_x`) over `RustCliAllocBudget M`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.ErrTailProofBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession
  (Crypto SessionState SignalProtocolError TripleRatchet)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement lsmpl)
open CryptoVerification.RustHeap (RustAlloc arrayAt)
open CryptoVerification.LibsignalSessionRepr (chainAt)
open CryptoVerification.LibsignalTripleRatchetRepr
  (decryptDraws protocolAddressAt sessionStateAt signalMessageAt speFnAt speWord tapeAfter
   utf8 uuidTryParse vecResultAt)
open CryptoVerification.LibsignalTripleRatchet
  (SpqrModel TrGhost TryDecryptGhost decResultFnAt logOff trAt)
open CryptoVerification.LibsignalTripleRatchet.Getters
  (dropChainStack lsRustDeallocSym)
open CryptoVerification.LibsignalTripleRatchet.Decrypt
  (speBodyAt speTag tryDecryptCommonHeap tryDecryptSavedRegs tryDecryptSubStack)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
  (SepWP.bind_framed SepWP.bind_framed_lscl SepWP.mono_pre
   blkPC_131 blkPl_131 chains_recombine_entails decRel_afterTrFrom
   errTailPC_placed errTail_stack_recombine
   exists_words3_of_memRegion_24 exists_words5_of_errTailBody exists_words5_of_speBodyAt
   exists_words6_of_memRegion_48 retEpiloguePC_placed
   sepWP_to_reaches_pc_midMeta_placed stackAt_dropChainStack_sub
   stackAt_tryDecryptSubStack_sub trAt_expose_errTail
   tryDecryptDummyImg tryDecryptMidMeta_placed tryDecryptWPInv words5At)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget
   rustCliDeallocBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget
  (tryDecryptFnSpecPlaced tryDecryptSpecPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.CommonBudget (ErrTailStateX_placed ErrTailState_placed)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.ErrTailSymBudget
  (errTail_copy_spe_wp_placed errTail_dealloc_chains_freeOnly_wp_placed
   errTail_dealloc_pq_freeOnly_wp_placed errTail_drop_chains_wp_placed)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
  (SeamBudget TryDecryptEnvArgs tryDecryptEnvArgs)
open LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatchBudget
  (chainAt_atState_fn invalidMessageStrAt_atState live_atState
   protocolAddressAt_atState sessionStateAt_atState signalMessageAt_atState
   speAt_atState vecResultAt_atState vecU8_atState)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem speFnAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (fnName : List (BitVec 8)) (a : BitVec 64) (e : SignalProtocolError) :
    speFnAt (A.atState lim st s) fnName a e = speFnAt A.repAlloc fnName a e := by
  cases e <;> simp only [speFnAt, speAt_atState, invalidMessageStrAt_atState, vecU8_atState]

private theorem decResultFnAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (r : BitVec 64) (res : Except SignalProtocolError (List (BitVec 8))) :
    decResultFnAt (A.atState lim st s) r res = decResultFnAt A.repAlloc r res := by
  cases res with
  | ok _ => simp only [decResultFnAt, vecU8_atState]
  | error e => exact speFnAt_atState A lim st s _ _ e

private theorem errTail_chains_re_entails {A : RustAlloc} {P_pool : SepProp}
    {sp : BitVec 64} {S_in S_out : Nat} {R_rem : SepProp}
    (hstack : stackAt sp S_in = stackAt sp S_out ∗ R_rem)
    {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {w0 w1 w2 w3 w4 ret tag : BitVec 64}
    (hcs_le : (trG.ratchet.chains.zip tr.ratchet.receiverChains).length ≤ trG.ratchet.chainsCap.toNat)
    (hcs_lt : trG.ratchet.chainsCap.toNat * 104 < 2 ^ 63) :
    let cs := trG.ratchet.chains.zip tr.ratchet.receiverChains
    (((memRegion trG.ratchet.chainsPtr (cs.length * 104) ∗ P_pool ∗ stackAt sp S_in) ∗
      (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
       ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
       ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗
       ((sp + 0x150#64) ↦₆₄ w2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
       words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗
       (if trG.ratchet.chainsCap = 0#64 then emp
        else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
          memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
       (if trG.pq.cap = 0#64 then emp
        else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat)))) ⊢
    ((((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
      (if trG.ratchet.chainsCap = 0#64 then emp
       else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
         memRegion trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104)) ∗
      P_pool ∗ stackAt sp S_out) ∗
     (R_rem ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
      ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
      ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗
      ((sp + 0x150#64) ↦₆₄ w2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
      words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗
      (if trG.pq.cap = 0#64 then emp
       else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat))) := by
  dsimp only; set cs := trG.ratchet.chains.zip tr.ratchet.receiverChains
  rw [hstack]
  have hcomm1 :
      (((memRegion trG.ratchet.chainsPtr (cs.length * 104) ∗ P_pool ∗ (stackAt sp S_out ∗ R_rem)) ∗
        (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
         ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗
         ((sp + 0x150#64) ↦₆₄ w2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
         words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat)))) =
      (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
       (memRegion trG.ratchet.chainsPtr (cs.length * 104) ∗
        (if trG.ratchet.chainsCap = 0#64 then emp
         else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
           memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((trG.ratchet.chainsCap.toNat - cs.length) * 104))) ∗
       (P_pool ∗ stackAt sp S_out ∗ R_rem ∗
        ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗ ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
        ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗ ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
        ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗ ((sp + 0x150#64) ↦₆₄ w2) ∗
        words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
        words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗
        (if trG.pq.cap = 0#64 then emp
         else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat))) := by sep_ac_rfl
  have hcomm2 :
      ((((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
        (if trG.ratchet.chainsCap = 0#64 then emp
         else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
           memRegion trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104)) ∗
        P_pool ∗ stackAt sp S_out) ∗
       (R_rem ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
        ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
        ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗
        ((sp + 0x150#64) ↦₆₄ w2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
        words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗
        (if trG.pq.cap = 0#64 then emp
         else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat))) =
      (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
       (if trG.ratchet.chainsCap = 0#64 then emp
        else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
          memRegion trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104)) ∗
       (P_pool ∗ stackAt sp S_out ∗ R_rem ∗
        ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗ ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
        ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗ ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
        ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗ ((sp + 0x150#64) ↦₆₄ w2) ∗
        words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
        words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗
        (if trG.pq.cap = 0#64 then emp
         else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat))) := by sep_ac_rfl
  rw [hcomm1, hcomm2]
  exact sepConj_mono_right (sepConj_mono_left (chains_recombine_entails hcs_le hcs_lt))

/-! ## Multi-Placed (`[LibsignalPlacement]`) Budget-Threaded `ErrTail` Contracts -/

theorem errTail_all_steps_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ast : M.σ}
    {H : String → Option (State → State)}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    {ret tag : BitVec 64} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {w0 w1 w2 w3 w4 r0 r1 r2 r3 r4 r5 t0 t1 t2 : BitVec 64} {s0 s : State}
    (hcs_le : (trG.ratchet.chains.zip tr.ratchet.receiverChains).length ≤ trG.ratchet.chainsCap.toNat)
    (hcs_lt : trG.ratchet.chainsCap.toNat * 104 < 2 ^ 63)
    (hpc : s.pc = errTailPC_placed)
    (hmeta : tryDecryptWPInv s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64)
    (hx26 : s.readReg64 .x26 = tag) :
    let sp := s0.sp - 1504#64
    let cs := trG.ratchet.chains.zip tr.ratchet.receiverChains
    SepWP ((blkPC_131).rebase (blkPl_131).base H) retEpiloguePC_placed s
      (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
       ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
       ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ t0) ∗ ((sp + 0x148#64) ↦₆₄ t1) ∗
       ((sp + 0x150#64) ↦₆₄ t2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ r0) ∗
       words5At (ret + 8#64) r1 r2 r3 r4 r5 ∗ arrayAt (chainAt A.repAlloc) 104 trG.ratchet.chainsPtr cs ∗
       (if trG.ratchet.chainsCap = 0#64 then emp
        else A.repAlloc.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
          memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
            ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
       (if trG.pq.cap = 0#64 then emp
        else A.repAlloc.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
       A.pool lim ast s ∗ stackAt sp dropChainStack)
      (fun sf P =>
        P = (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
             ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
             ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗
             ((sp + 0x150#64) ↦₆₄ w2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
             words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗
             (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs ast) sf) ∗
             stackAt sp dropChainStack) ∧
        tryDecryptWPInv s0 sf) := by
  dsimp only; let sp := s0.sp - 1504#64; set cs := trG.ratchet.chains.zip tr.ratchet.receiverChains
  have hcopy := errTail_copy_spe_wp_placed (A := A) (lim := lim) (ast := ast) (H := H)
    (chainsPtr := trG.ratchet.chainsPtr) (chainsLen := BitVec.ofNat 64 cs.length)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4)
    (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3) (r4 := r4) (r5 := r5)
    (t0 := t0) (t1 := t1) (t2 := t2) hpc hmeta hx19 hx20 hx26
  refine SepWP.bind_framed_lscl
    (F := ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
          ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ arrayAt (chainAt A.repAlloc) 104 trG.ratchet.chainsPtr cs ∗
          (if trG.ratchet.chainsCap = 0#64 then emp
           else A.repAlloc.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
             memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
               ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
          (if trG.pq.cap = 0#64 then emp
           else A.repAlloc.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
          stackAt sp dropChainStack) hcl hcopy ?_ ?_
  · dsimp only [sp]; sep_ac_rfl
  intro s1 P1 ⟨hP1, hmeta1, hx20_1, hx21_1⟩ hpc1 hcl1; subst hP1
  have hcs_lt' : cs.length * 104 < 2 ^ 63 := Nat.lt_of_le_of_lt (Nat.mul_le_mul_right 104 hcs_le) hcs_lt
  have hdrop_cs := errTail_drop_chains_wp_placed (A := A) (lim := lim) (ast := ast) (H := H)
    hdealloc hcs_lt' hpc1 hmeta1 hcl1 hx20_1 hx21_1
  refine SepWP.bind_framed
    (F := ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
          ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
          ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗
          ((sp + 0x150#64) ↦₆₄ w2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
          words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗
          (if trG.ratchet.chainsCap = 0#64 then emp
           else A.repAlloc.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
             memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
               ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
          (if trG.pq.cap = 0#64 then emp
           else A.repAlloc.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat))
    hdrop_cs ?_ ?_
  · dsimp only [sp]; sep_ac_rfl
  intro s2 P2 ⟨hP2, hmeta2, hx20_2⟩ hpc2; subst hP2
  refine SepWP.mono_pre
    (errTail_chains_re_entails (A := A.repAlloc)
      (P_pool := ∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs ast) s2)
      (stackAt_dropChainStack_sub sp) hcs_le hcs_lt) ?_
  have hdealloc_cs := errTail_dealloc_chains_freeOnly_wp_placed (A := A) (lim := lim) (ast := ast) (H := H)
    hdealloc hcs_lt hpc2 hmeta2 hx20_2
  refine SepWP.bind_framed
    (F := memRegion (sp - 4144#64) 48 ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
          ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
          ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗
          ((sp + 0x150#64) ↦₆₄ w2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
          words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗
          (if trG.pq.cap = 0#64 then emp
           else A.repAlloc.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat))
    hdealloc_cs ?_ ?_
  · dsimp only [sp]
  intro s3 P3 ⟨hP3, hmeta3⟩ hpc3; subst hP3
  have hdealloc_pq := errTail_dealloc_pq_freeOnly_wp_placed (A := A) (lim := lim) (ast := ast) (H := H)
    (pqCap := trG.pq.cap) (pqPtr := trG.pq.ptr) hdealloc hpc3 hmeta3
  refine SepWP.bind_framed
    (F := memRegion (sp - 4144#64) 48 ∗ ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
          ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗ ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
          ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗ ((sp + 0x150#64) ↦₆₄ w2) ∗
          words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
          words5At (ret + 8#64) w0 w1 w2 w3 w4) hdealloc_pq ?_ ?_
  · dsimp only [sp]; sep_ac_rfl
  intro sf Pf ⟨hPf, hmeta_f⟩ hpcf; subst hPf
  refine SepWP.done hpcf hmeta_f.1 ⟨?_, hmeta_f⟩
  rw [stackAt_dropChainStack_sub sp]; dsimp only [sp]; sep_ac_rfl

end LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.ErrTailProofBudget
