/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Getters.ClearUnacknowledgedPreKeyMessage -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.ErrTailSym
import ProofLib.Sep
import ProofLib.SepLogic.WPp

/-!
# `ErrTail` Error-Cleanup Contracts for `try_decrypt_with_state`

Proves `errTail_ok_ext`, `errTail_ok_x`, and relocatable `[LibsignalPlacement]` `ErrTail` contracts
(`+0x30c → +0x394 → +0x3b0`), writing the error result to `x.ret`, dropping `receiver_chains` and
`pqr_state`, and returning via the shared epilogue.
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Decrypt

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Expose the fields of `trAt A (sp + 0x38#64) trG tr` needed by `ErrTail`:
- `receiver_chains` header at `sp + 0x38..0x50`, its `arrayAt` elements, and its spare/live block;
- `pqr_state` header `(cap, ptr)` at `sp + 0xe8..0xf8` and its heap allocation;
- the remaining `152 + 72 = 224` bytes of `trAt` collapsed into `memRegion (sp + 0x50#64) 0x98 ∗
  memRegion (sp + 0xf8#64) 0x48`. -/
theorem trAt_expose_errTail {A : RustAlloc} {sp : BitVec 64} {trG : TrGhost}
    {tr : TripleRatchet (List (BitVec 8))} {R : SepProp} {m : Memory}
    (hm : m ⊨ trAt A (sp + 0x38#64) trG tr ∗ R) :
    let cs := trG.ratchet.chains.zip tr.ratchet.receiverChains
    cs.length ≤ trG.ratchet.chainsCap.toNat ∧
    trG.ratchet.chainsCap.toNat * 104 < 2 ^ 63 ∧
    trG.ratchet.chainsPtr ≠ 0#64 ∧
    tr.pqrState.length ≤ trG.pq.cap.toNat ∧
    trG.pq.cap.toNat < 2 ^ 63 ∧
    trG.pq.ptr ≠ 0#64 ∧
    (m ⊨
      (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
       ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
       ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
       memRegion (sp + 0x50#64) 0x98 ∗
       ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
       ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
       memRegion (sp + 0xf8#64) 0x48 ∗
       arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
       (if trG.ratchet.chainsCap = 0#64 then emp
        else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
          memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
            ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
       (if trG.pq.cap = 0#64 then emp
        else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
          memRegion trG.pq.ptr trG.pq.cap.toNat)) ∗ R) := by
  dsimp only
  unfold trAt ratchetAt vecU8At vecAt vecBuf vecHeader at hm
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨_, ⟨_, hpad, _⟩, hm⟩
  have hm_cs :
      m ⊨ ⌜(trG.ratchet.chains.zip tr.ratchet.receiverChains).length ≤ trG.ratchet.chainsCap.toNat ∧
            trG.ratchet.chainsCap.toNat * 104 < 2 ^ 63 ∧ trG.ratchet.chainsPtr ≠ 0#64⌝ ∗
        (⌜tr.pqrState.length ≤ trG.pq.cap.toNat ∧ trG.pq.cap.toNat < 2 ^ 63 ∧ trG.pq.ptr ≠ 0#64⌝ ∗
         (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x38#64 + 8#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
          ((sp + 0x38#64 + 16#64) ↦₆₄ BitVec.ofNat 64 (trG.ratchet.chains.zip tr.ratchet.receiverChains).length) ∗
          (if trG.ratchet.chainsCap = 0#64 then emp
           else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
             arrayAt (chainAt A) 104 trG.ratchet.chainsPtr (trG.ratchet.chains.zip tr.ratchet.receiverChains) ∗
             memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 ((trG.ratchet.chains.zip tr.ratchet.receiverChains).length * 104))
               ((trG.ratchet.chainsCap.toNat - (trG.ratchet.chains.zip tr.ratchet.receiverChains).length) * 104)) ∗
          ((sp + 0x38#64 + 24#64) ↦ₛ optSenderChainBytes tr.ratchet.senderChain trG.ratchet.senderPad) ∗
          ((sp + 0x38#64 + 128#64) ↦ₛ keyToBytes32 tr.ratchet.rootKey) ∗
          ((sp + 0x38#64 + 160#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.maxForwardJumps) ∗
          ((sp + 0x38#64 + 168#64) ↦₃₂ tr.ratchet.previousCounter) ∗ memRegion (sp + 0x38#64 + 172#64) 4 ∗
          ((sp + 0x38#64 + 0xb0#64) ↦₆₄ trG.pq.cap) ∗ ((sp + 0x38#64 + 0xb0#64 + 8#64) ↦₆₄ trG.pq.ptr) ∗
          ((sp + 0x38#64 + 0xb0#64 + 16#64) ↦₆₄ BitVec.ofNat 64 tr.pqrState.length) ∗
          (if trG.pq.cap = 0#64 then emp
           else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ (trG.pq.ptr ↦ₛ tr.pqrState) ∗
             memRegion (trG.pq.ptr + BitVec.ofNat 64 tr.pqrState.length) (trG.pq.cap.toNat - tr.pqrState.length)) ∗
          ((sp + 0x38#64 + 0xc8#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
          ((sp + 0x38#64 + 0xe8#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList) ∗ R)) := by
    convert hm using 1; sep_ac_rfl
  rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hm_cs
  rcases hm_cs with ⟨⟨hcs_le, hcs_lt, hcs_ptr⟩, ⟨hpq_le, hpq_lt, hpq_ptr⟩, hm⟩
  refine ⟨hcs_le, hcs_lt, hcs_ptr, hpq_le, hpq_lt, hpq_ptr, ?_⟩
  simp only [BitVec.add_assoc, BitVec.reduceAdd, ← sepConj_assoc] at hm ⊢
  refine Satisfies.mono (sepConj_mono_left ?_) hm
  have hsc_len := optSenderChainBytes_length tr.ratchet.senderChain trG.ratchet.senderPad hpad
  have hrk_len : (keyToBytes32 tr.ratchet.rootKey).length = 32 := by simp [keyToBytes32]
  have hloc_len : tr.localIdentityKey.publicKey.bytes.toList.length = 32 := List.Vector.toList_length _
  have hrem_len : tr.remoteIdentityKey.publicKey.bytes.toList.length = 32 := List.Vector.toList_length _
  have hmr_pq : memRegion trG.pq.ptr trG.pq.cap.toNat =
      memRegion trG.pq.ptr tr.pqrState.length ∗
      memRegion (trG.pq.ptr + BitVec.ofNat 64 tr.pqrState.length) (trG.pq.cap.toNat - tr.pqrState.length) := by
    rw [← memRegion_split trG.pq.ptr tr.pqrState.length _ (by omega), Nat.add_sub_of_le hpq_le]
  by_cases hc1 : trG.ratchet.chainsCap = 0#64 <;> by_cases hc2 : trG.pq.cap = 0#64 <;>
    simp only [hc1, hc2, ↓reduceIte]
  · have hlen0 : (trG.ratchet.chains.zip tr.ratchet.receiverChains).length = 0 := by simpa [hc1] using hcs_le
    rw [List.eq_nil_of_length_eq_zero hlen0, arrayAt]; sep_interval
  · have hlen0 : (trG.ratchet.chains.zip tr.ratchet.receiverChains).length = 0 := by simpa [hc1] using hcs_le
    rw [List.eq_nil_of_length_eq_zero hlen0, arrayAt, hmr_pq]
    refine Entails.trans (by bi_frame)
      (Entails.trans (sepConj_mono_left (pointsToBytes_entails_memRegion trG.pq.ptr tr.pqrState)) ?_)
    generalize memRegion trG.pq.ptr tr.pqrState.length = pq1,
      memRegion (trG.pq.ptr + BitVec.ofNat 64 tr.pqrState.length) (trG.pq.cap.toNat - tr.pqrState.length) = pq2
    sep_interval
  · sep_interval
  · rw [hmr_pq]
    refine Entails.trans (by bi_frame)
      (Entails.trans (sepConj_mono_left (pointsToBytes_entails_memRegion trG.pq.ptr tr.pqrState)) ?_)
    generalize memRegion trG.pq.ptr tr.pqrState.length = pq1,
      memRegion (trG.pq.ptr + BitVec.ofNat 64 tr.pqrState.length) (trG.pq.cap.toNat - tr.pqrState.length) = pq2
    sep_interval

theorem chains_recombine_entails {A : RustAlloc} {chainsCap chainsPtr : BitVec 64} {n : Nat}
    (hle : n ≤ chainsCap.toNat) (hlt : chainsCap.toNat * 104 < 2 ^ 63) :
    (memRegion chainsPtr (n * 104) ∗
     (if chainsCap = 0#64 then emp
      else A.live chainsPtr (chainsCap.toNat * 104) 8 ∗
        memRegion (chainsPtr + BitVec.ofNat 64 (n * 104)) ((chainsCap.toNat - n) * 104))) ⊢
    (if chainsCap = 0#64 then emp
     else A.live chainsPtr (chainsCap.toNat * 104) 8 ∗
       memRegion chainsPtr (chainsCap.toNat * 104)) := by
  split
  · next hcap0 =>
    have hn0 : n = 0 := by simpa [hcap0] using hle
    subst hn0
    rw [Nat.zero_mul, memRegion_zero, emp_sepConj]
    exact Entails.refl _
  · have hre :
        (memRegion chainsPtr (n * 104) ∗
          (A.live chainsPtr (chainsCap.toNat * 104) 8 ∗
           memRegion (chainsPtr + BitVec.ofNat 64 (n * 104)) ((chainsCap.toNat - n) * 104))) =
        (A.live chainsPtr (chainsCap.toNat * 104) 8 ∗
          (memRegion chainsPtr (n * 104) ∗
           memRegion (chainsPtr + BitVec.ofNat 64 (n * 104)) ((chainsCap.toNat - n) * 104))) := by
      sep_ac_rfl
    rw [hre, ← memRegion_split chainsPtr (n * 104) ((chainsCap.toNat - n) * 104) (by omega),
        show n * 104 + (chainsCap.toNat - n) * 104 = chainsCap.toNat * 104 by
          rw [← Nat.add_mul, Nat.add_sub_of_le hle]]
    exact Entails.refl _

theorem errTail_stack_recombine (sp c0 c1 c2 p0 p1 w0 w1 w2 w3 w4 : BitVec 64) :
    (memRegion sp 0x38 ∗
     ((sp + 0x38#64) ↦₆₄ c0) ∗
     ((sp + 0x40#64) ↦₆₄ c1) ∗
     ((sp + 0x48#64) ↦₆₄ c2) ∗
     memRegion (sp + 0x50#64) 0x98 ∗
     ((sp + 0xe8#64) ↦₆₄ p0) ∗
     ((sp + 0xf0#64) ↦₆₄ p1) ∗
     memRegion (sp + 0xf8#64) 0x48 ∗
     ((sp + 0x140#64) ↦₆₄ w0) ∗
     ((sp + 0x148#64) ↦₆₄ w1) ∗
     ((sp + 0x150#64) ↦₆₄ w2) ∗
     memRegion (sp + 0x158#64) 16 ∗
     words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
     memRegion (sp + 0x190#64) 0x3f0) ⊢
    memRegion sp 1408 := by
  sep_interval

private theorem errTail_chains_re_entails {A : RustAlloc}
    {sp : BitVec 64} {S_in S_out : Nat} {R_rem : SepProp}
    (hstack : stackAt sp S_in = stackAt sp S_out ∗ R_rem)
    {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {w0 w1 w2 w3 w4 ret tag : BitVec 64}
    (hcs_le : (trG.ratchet.chains.zip tr.ratchet.receiverChains).length ≤ trG.ratchet.chainsCap.toNat)
    (hcs_lt : trG.ratchet.chainsCap.toNat * 104 < 2 ^ 63) :
    let cs := trG.ratchet.chains.zip tr.ratchet.receiverChains
    (((memRegion trG.ratchet.chainsPtr (cs.length * 104) ∗ A.pool ∗ stackAt sp S_in) ∗
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
      A.pool ∗ stackAt sp S_out) ∗
     (R_rem ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
      ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
      ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗
      ((sp + 0x150#64) ↦₆₄ w2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
      words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗
      (if trG.pq.cap = 0#64 then emp
       else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat))) := by
  dsimp only; set cs := trG.ratchet.chains.zip tr.ratchet.receiverChains
  rw [hstack]
  by_cases hc : trG.ratchet.chainsCap = 0#64
  · have hn0 : cs.length = 0 := by simpa [hc] using hcs_le
    simp only [hc, hn0, Nat.zero_mul, memRegion_zero, ↓reduceIte]; bi_entail
  · simp only [hc, ↓reduceIte]
    rw [show trG.ratchet.chainsCap.toNat * 104 =
          cs.length * 104 + (trG.ratchet.chainsCap.toNat - cs.length) * 104 by
          rw [← Nat.add_mul, Nat.add_sub_of_le hcs_le],
        memRegion_split trG.ratchet.chainsPtr (cs.length * 104) _ (by omega)]
    bi_entail

theorem errTail_all_steps_wp_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
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
       words5At (ret + 8#64) r1 r2 r3 r4 r5 ∗ arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
       (if trG.ratchet.chainsCap = 0#64 then emp
        else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
          memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
       (if trG.pq.cap = 0#64 then emp
        else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
       A.pool ∗ stackAt sp dropChainStack)
      (fun sf P =>
        P = (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
             ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
             ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗
             ((sp + 0x150#64) ↦₆₄ w2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
             words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗ A.pool ∗ stackAt sp dropChainStack) ∧
        tryDecryptWPInv s0 sf) := by
  dsimp only; let sp := s0.sp - 1504#64; set cs := trG.ratchet.chains.zip tr.ratchet.receiverChains
  have hcopy := errTail_copy_spe_wp_placed (H := H)
    (chainsPtr := trG.ratchet.chainsPtr) (chainsLen := BitVec.ofNat 64 cs.length)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4)
    (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3) (r4 := r4) (r5 := r5)
    (t0 := t0) (t1 := t1) (t2 := t2) hpc hmeta hx19 hx20 hx26
  refine SepWP.bind_framed_lscl
    (F := ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
          ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
          (if trG.ratchet.chainsCap = 0#64 then emp
           else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
             memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
          (if trG.pq.cap = 0#64 then emp
           else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
          A.pool ∗ stackAt sp dropChainStack) hcl hcopy ?_ ?_
  · dsimp only [sp]; sep_ac_rfl
  intro s1 P1 ⟨hP1, hmeta1, hx20_1, hx21_1⟩ hpc1 hcl1; subst hP1
  have hcs_lt' : cs.length * 104 < 2 ^ 63 := Nat.lt_of_le_of_lt (Nat.mul_le_mul_right 104 hcs_le) hcs_lt
  have hdrop_cs := errTail_drop_chains_wp_placed (A := A) (H := H)
    hdealloc hcs_lt' hpc1 hmeta1 hcl1 hx20_1 hx21_1
  refine SepWP.bind_framed
    (F := ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
          ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
          ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗
          ((sp + 0x150#64) ↦₆₄ w2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
          words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗
          (if trG.ratchet.chainsCap = 0#64 then emp
           else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
             memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
          (if trG.pq.cap = 0#64 then emp
           else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat)) hdrop_cs ?_ ?_
  · dsimp only [sp]; sep_ac_rfl
  intro s2 P2 ⟨hP2, hmeta2, hx20_2⟩ hpc2; subst hP2
  refine SepWP.mono_pre (errTail_chains_re_entails (stackAt_dropChainStack_sub sp) hcs_le hcs_lt) ?_
  have hdealloc_cs := errTail_dealloc_chains_wp_placed (A := A) (H := H)
    hdealloc hcs_lt hpc2 hmeta2 hx20_2
  refine SepWP.bind_framed
    (F := memRegion (sp - 4144#64) 48 ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
          ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
          ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗
          ((sp + 0x150#64) ↦₆₄ w2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
          words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗
          (if trG.pq.cap = 0#64 then emp
           else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat)) hdealloc_cs ?_ ?_
  · dsimp only [sp]
  intro s3 P3 ⟨hP3, hmeta3⟩ hpc3; subst hP3
  have hdealloc_pq := errTail_dealloc_pq_wp_placed (A := A) (H := H)
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

end CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
