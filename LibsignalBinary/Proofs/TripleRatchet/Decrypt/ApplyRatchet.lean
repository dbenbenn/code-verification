/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DecryptCodeSym130 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DecryptCodeSym433 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Defs
import ProofLib
import ProofLib.Sep
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.AuthDecryptDefs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

public section

namespace CryptoVerification.LibsignalTripleRatchet.Decrypt.AuthDecrypt

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Decrypt
open CryptoVerification.LibsignalSession
open ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] BitVec.toNat_zero

/-!
# Segment 9 (`apply_to_session_state`) Proofs for `try_decrypt_with_state`

Verifies Segment 9 (`+0x6a4 → +0x4b8 → +0x394 → +0x3b0`) of `try_decrypt_with_state`, replacing
`tr.pqr_state`, writing `Ok(pt)`, applying the updated `TripleRatchet` to `SessionState`, clearing
any unacknowledged pre-key message, and returning via the shared epilogue.
-/

theorem length_optSenderChainBytes (o : Option SenderChain) {pad : List (BitVec 8)}
    (hpad : pad.length = 100) : (optSenderChainBytes o pad).length = 104 := by
  cases o with
  | none => simp [optSenderChainBytes, leBytes, hpad]
  | some sc =>
    have hpub : sc.ratchetKey.publicKey.bytes.toList.length = 32 := sc.ratchetKey.publicKey.bytes.2
    have hpriv : sc.ratchetKey.privateKey.bytes.toList.length = 32 := sc.ratchetKey.privateKey.bytes.2
    simp [optSenderChainBytes, senderChainBytes, chainKeyBytes, keyToBytes32, leBytes, hpub, hpriv]

@[expose] def trStackBytes (G : TrGhost) (tr : TripleRatchet (List (BitVec 8))) (pad : BitVec 32) :
    List (BitVec 8) :=
  unpack64 G.ratchet.chainsCap ++
  (unpack64 G.ratchet.chainsPtr ++
  (unpack64 (BitVec.ofNat 64 (G.ratchet.chains.zip tr.ratchet.receiverChains).length) ++
  (optSenderChainBytes tr.ratchet.senderChain G.ratchet.senderPad ++
  (keyToBytes32 tr.ratchet.rootKey ++
  (unpack64 (BitVec.ofNat 64 tr.ratchet.maxForwardJumps) ++
  (unpack32 tr.ratchet.previousCounter ++
  (unpack32 pad ++
  (unpack64 G.pq.cap ++
  (unpack64 G.pq.ptr ++
  (unpack64 (BitVec.ofNat 64 tr.pqrState.length) ++
  (tr.localIdentityKey.publicKey.bytes.toList ++
   tr.remoteIdentityKey.publicKey.bytes.toList)))))))))))

theorem length_trStackBytes (G : TrGhost) (tr : TripleRatchet (List (BitVec 8))) (pad : BitVec 32)
    (hpad : G.ratchet.senderPad.length = 100) :
    (trStackBytes G tr pad).length = 264 := by
  have hloc : tr.localIdentityKey.publicKey.bytes.toList.length = 32 :=
    tr.localIdentityKey.publicKey.bytes.2
  have hrem : tr.remoteIdentityKey.publicKey.bytes.toList.length = 32 :=
    tr.remoteIdentityKey.publicKey.bytes.2
  simp [trStackBytes, length_optSenderChainBytes _ hpad, length_keyToBytes32, hloc, hrem]

@[expose] def trHeapPart (A : RustAlloc) (G : TrGhost) (tr : TripleRatchet (List (BitVec 8))) : SepProp :=
  ⌜∀ sc, tr.ratchet.senderChain = some sc →
    Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes⌝ ∗
  ⌜G.ratchet.chains.length = tr.ratchet.receiverChains.length ∧
    G.ratchet.senderPad.length = 100 ∧
    tr.ratchet.maxForwardJumps < 2 ^ 64⌝ ∗
  vecBuf A 104 8 (chainAt A) G.ratchet.chainsCap G.ratchet.chainsPtr
    (G.ratchet.chains.zip tr.ratchet.receiverChains) ∗
  ⌜tr.pqrState.length ≤ G.pq.cap.toNat ∧ G.pq.cap.toNat < 2 ^ 63 ∧ G.pq.ptr ≠ 0⌝ ∗
  (if G.pq.cap = 0 then emp
   else (A.live G.pq.ptr G.pq.cap.toNat 1 ∗
     (G.pq.ptr ↦ₛ tr.pqrState)) ∗
     memRegion (G.pq.ptr + BitVec.ofNat 64 tr.pqrState.length) (G.pq.cap.toNat - tr.pqrState.length))

theorem pointsToBytes_trStackBytes (t : BitVec 64) (G : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (pad : BitVec 32)
    (hpad : G.ratchet.senderPad.length = 100) :
    (t ↦ₛ trStackBytes G tr pad) =
      ((t ↦₆₄ G.ratchet.chainsCap) ∗
       ((t + 8#64) ↦₆₄ G.ratchet.chainsPtr) ∗
       ((t + 16#64) ↦₆₄ BitVec.ofNat 64 (G.ratchet.chains.zip tr.ratchet.receiverChains).length) ∗
       ((t + 24#64) ↦ₛ optSenderChainBytes tr.ratchet.senderChain G.ratchet.senderPad) ∗
       ((t + 128#64) ↦ₛ keyToBytes32 tr.ratchet.rootKey) ∗
       ((t + 160#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.maxForwardJumps) ∗
       ((t + 168#64) ↦₃₂ tr.ratchet.previousCounter) ∗
       ((t + 172#64) ↦₃₂ pad) ∗
       ((t + 0xb0#64) ↦₆₄ G.pq.cap) ∗
       ((t + 0xb8#64) ↦₆₄ G.pq.ptr) ∗
       ((t + 0xc0#64) ↦₆₄ BitVec.ofNat 64 tr.pqrState.length) ∗
       ((t + 0xc8#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
       ((t + 0xe8#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList)) := by
  have hloc : tr.localIdentityKey.publicKey.bytes.toList.length = 32 :=
    tr.localIdentityKey.publicKey.bytes.2
  unfold trStackBytes
  repeat rw [pointsToBytes_append]
  simp only [unpack64_length, unpack32_length, length_optSenderChainBytes _ hpad,
    length_keyToBytes32, hloc,
    ← pointsTo64_eq_pointsToBytes, ← pointsTo32_eq_pointsToBytes,
    BitVec.add_assoc, BitVec.reduceAdd]

theorem trAt_eq_stack_heap (A : RustAlloc) (t : BitVec 64) (G : TrGhost)
    (tr : TripleRatchet (List (BitVec 8)))
    (hpad : G.ratchet.senderPad.length = 100) :
    trAt A t G tr =
      ∃∗ pad : BitVec 32, (t ↦ₛ trStackBytes G tr pad) ∗ trHeapPart A G tr := by
  unfold trAt ratchetAt vecAt vecU8At vecHeader trHeapPart
  rw [memRegion_four (t + 172#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  congr 1; funext pad
  rw [pointsToBytes_trStackBytes t G tr pad hpad,
      show t + 0xb0#64 + 8#64 = t + 0xb8#64 by bv_omega,
      show t + 0xb0#64 + 16#64 = t + 0xc0#64 by bv_omega]
  ac_rfl

theorem trAt_of_stack_heap (A : RustAlloc) (t : BitVec 64) (G : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (pad : BitVec 32)
    (hpad : G.ratchet.senderPad.length = 100) :
    (t ↦ₛ trStackBytes G tr pad) ∗ trHeapPart A G tr ⊢ trAt A t G tr := by
  rw [trAt_eq_stack_heap A t G tr hpad]
  exact Entails.sepExists_intro (P := fun p => (t ↦ₛ trStackBytes G tr p) ∗ trHeapPart A G tr) pad

@[expose] def trWithoutPqAt (A : RustAlloc) (t : BitVec 64) (G : RatchetGhost)
    (tr : TripleRatchet (List (BitVec 8))) : SepProp :=
  ⌜∀ sc, tr.ratchet.senderChain = some sc →
    Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes⌝ ∗
  ratchetAt A t G tr.ratchet ∗
  ((t + 0xc8#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
  ((t + 0xe8#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList)

theorem trAt_senderPad_len {A : RustAlloc} {t : BitVec 64} {G : TrGhost}
    {tr : TripleRatchet (List (BitVec 8))} {R : SepProp} {m : Memory}
    (h : m ⊨ trAt A t G tr ∗ R) : G.ratchet.senderPad.length = 100 := by
  unfold trAt ratchetAt at h
  simp only [sepConj_assoc, satisfies_pure_sepConj] at h
  exact h.2.1.2.1

theorem trAt_eq_withoutPq (A : RustAlloc) (sp : BitVec 64) (G : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) :
    trAt A (sp - 1504#64 + 0x38#64) G tr =
      (trWithoutPqAt A (sp - 1448#64) G.ratchet tr ∗
       ⌜tr.pqrState.length ≤ G.pq.cap.toNat ∧ G.pq.cap.toNat < 2 ^ 63 ∧ G.pq.ptr ≠ 0⌝ ∗
       ((sp - 1272#64) ↦₆₄ G.pq.cap) ∗
       ((sp - 1264#64) ↦₆₄ G.pq.ptr) ∗
       ((sp - 1256#64) ↦₆₄ BitVec.ofNat 64 tr.pqrState.length) ∗
       (if G.pq.cap = 0 then emp else (A.live G.pq.ptr G.pq.cap.toNat 1 ∗
         (G.pq.ptr ↦ₛ tr.pqrState)) ∗
         memRegion (G.pq.ptr + BitVec.ofNat 64 tr.pqrState.length) (G.pq.cap.toNat - tr.pqrState.length))) := by
  unfold trAt trWithoutPqAt vecU8At vecHeader
  rw [show sp - 1504#64 + 0x38#64 = sp - 1448#64 by bv_omega,
      show sp - 1448#64 + 0xb0#64 = sp - 1272#64 by bv_omega,
      show sp - 1272#64 + 8#64 = sp - 1264#64 by bv_omega,
      show sp - 1272#64 + 16#64 = sp - 1256#64 by bv_omega]
  ac_rfl

theorem trAt_of_withoutPq (A : RustAlloc) (sp : BitVec 64) (G : TrGhost)
    (tr : TripleRatchet (List (BitVec 8)))
    (newPqrCap newPqrPtr : BitVec 64) (newPqrState : List (BitVec 8))
    (hle : newPqrState.length ≤ newPqrCap.toNat)
    (hlt : newPqrCap.toNat < 2 ^ 63)
    (hnz : newPqrPtr ≠ 0) :
    trWithoutPqAt A (sp - 1448#64) G.ratchet tr ∗
    ((sp - 1272#64) ↦₆₄ newPqrCap) ∗
    ((sp - 1264#64) ↦₆₄ newPqrPtr) ∗
    ((sp - 1256#64) ↦₆₄ BitVec.ofNat 64 newPqrState.length) ∗
    (if newPqrCap = 0 then emp else (A.live newPqrPtr newPqrCap.toNat 1 ∗
      (newPqrPtr ↦ₛ newPqrState)) ∗
      memRegion (newPqrPtr + BitVec.ofNat 64 newPqrState.length) (newPqrCap.toNat - newPqrState.length)) ⊢
    trAt A (sp - 1448#64) { G with pq := ⟨newPqrCap, newPqrPtr⟩ } { tr with pqrState := newPqrState } := by
  rw [show sp - 1448#64 = sp - 1504#64 + 0x38#64 by bv_omega, trAt_eq_withoutPq]
  rw [show sp - 1504#64 + 0x38#64 = sp - 1448#64 by bv_omega]
  bi_entail

theorem applyRatchet_scr_split (sp : BitVec 64) :
    memRegion (sp - 1504#64 + 0x140#64) 0x290 =
      (memRegion (sp - 1184#64) 8 ∗
       memRegion (sp - 1176#64) 8 ∗
       memRegion (sp - 1168#64) 8 ∗
       memRegion (sp - 1160#64) 16 ∗
       memRegion (sp - 1144#64) 8 ∗
       memRegion (sp - 1136#64) 8 ∗
       memRegion (sp - 1128#64) 8 ∗
       memRegion (sp - 1120#64) 16 ∗
       memRegion (sp - 1104#64) 264 ∗
       memRegion (sp - 840#64) 120 ∗
       memRegion (sp - 720#64) 8 ∗
       memRegion (sp - 712#64) 8 ∗
       memRegion (sp - 704#64) 8 ∗
       memRegion (sp - 696#64) 168) := by
  sep_interval_eq

theorem applyRatchet_ret_split (ret : BitVec 64) :
    memRegion ret 48 =
      (memRegion ret 8 ∗ memRegion (ret + 8#64) 8 ∗ memRegion (ret + 16#64) 8 ∗
       memRegion (ret + 24#64) 8 ∗ memRegion (ret + 32#64) 16) := by
  sep_interval_eq

theorem decResultAt_ok_of_parts (A : RustAlloc) (ret : BitVec 64) (pt : List (BitVec 8))
    (ptCap ptPtr : BitVec 64)
    (hle : pt.length ≤ ptCap.toNat) (hlt : ptCap.toNat < 2 ^ 63) (hnz : ptPtr ≠ 0) :
    (ret ↦₆₄ okTagVec) ∗
    (((ret + 8#64) ↦₆₄ ptCap) ∗
     ((ret + 16#64) ↦₆₄ ptPtr) ∗
     ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
     (if ptCap = 0 then emp else (A.live ptPtr ptCap.toNat 1 ∗ (ptPtr ↦ₛ pt)) ∗
       memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length))) ∗
    memRegion (ret + 32#64) 16 ⊢
    vecResultAt A ret (.ok pt) := by
  unfold vecResultAt
  refine sepConj_mono_right (sepConj_mono_left ?_)
  have hv := vecU8At_parts_entails_vecU8' A (ret + 8#64) ptCap ptPtr pt hle hlt hnz
  rwa [show ret + 8#64 + 8#64 = ret + 16#64 by bv_omega,
       show ret + 8#64 + 16#64 = ret + 24#64 by bv_omega] at hv

theorem decRel_of_trApplyRel {G G1 : SessionGhost} {trG : TrGhost}
    (h : G.afterTrFrom.TrApplyRel trG G1) :
    G.AfterTryDecrypt true { G1 with pending := none, kyber := none } := by
  rcases h with ⟨⟨h1, h2, h3, h4⟩, -⟩
  exact ⟨⟨h1, h2, h3, h4⟩, rfl, rfl⟩

theorem tryDecryptSavedRegs_entails_memRegion (sp0 : BitVec 64) (s0 : State) :
    tryDecryptSavedRegs sp0 s0 ⊢ memRegion (sp0 - 96#64) 96 := by
  dsimp only [tryDecryptSavedRegs]; sep_interval

theorem applyRatchet_local_frame_entails_memRegion (sp : BitVec 64)
    (v1496 v1464 v1184 v1176 v1168 v1144 v1136 v1128
     v720 v712 v704 v528 v520 v512 : BitVec 64)
    (bs : List (BitVec 8)) (hbs : bs.length = 264) :
    memRegion (sp - 1504#64) 8 ∗
    ((sp - 1496#64) ↦₆₄ v1496) ∗
    memRegion (sp - 1488#64) 24 ∗
    ((sp - 1464#64) ↦₆₄ v1464) ∗
    memRegion (sp - 1456#64) 8 ∗
    ((sp - 1448#64) ↦ₛ bs) ∗
    ((sp - 1184#64) ↦₆₄ v1184) ∗
    ((sp - 1176#64) ↦₆₄ v1176) ∗
    ((sp - 1168#64) ↦₆₄ v1168) ∗
    memRegion (sp - 1160#64) 16 ∗
    ((sp - 1144#64) ↦₆₄ v1144) ∗
    ((sp - 1136#64) ↦₆₄ v1136) ∗
    ((sp - 1128#64) ↦₆₄ v1128) ∗
    memRegion (sp - 1120#64) 16 ∗
    memRegion (sp - 1104#64) 264 ∗
    memRegion (sp - 840#64) 120 ∗
    ((sp - 720#64) ↦₆₄ v720) ∗
    ((sp - 712#64) ↦₆₄ v712) ∗
    ((sp - 704#64) ↦₆₄ v704) ∗
    memRegion (sp - 696#64) 168 ∗
    ((sp - 528#64) ↦₆₄ v528) ∗
    ((sp - 520#64) ↦₆₄ v520) ∗
    ((sp - 512#64) ↦₆₄ v512) ∗
    memRegion (sp - 504#64) 0x198 ⊢
    memRegion (sp - 1504#64) 1408 := by
  sep_interval

theorem stackAt_rootStack_of_parts (sp0 : BitVec 64) :
    stackAt (sp0 - 1504#64) tryDecryptSubStack ∗
    memRegion (sp0 - 1504#64) 1408 ∗
    memRegion (sp0 - 96#64) 96 ⊢
    stackAt sp0 rootStack := by
  simp only [stackAt, tryDecryptSubStack, tryDecryptFrameSize, rootStack,
    Nat.reducePow, Nat.reduceSub]
  sep_interval

private theorem subStack_split_eq (sp : BitVec 64) (k : Nat) (hk : k ≤ tryDecryptSubStack) :
    stackAt (sp - 1504#64) k ∗ memRegion (sp - 262144#64) (tryDecryptSubStack - k) =
      stackAt (sp - 1504#64) tryDecryptSubStack := by
  have h := stackAt_sub_split (sp - 1504#64) k hk
  rw [show sp - 1504#64 - BitVec.ofNat 64 tryDecryptSubStack = sp - 262144#64 by
        dsimp only [tryDecryptSubStack, rootStack, tryDecryptFrameSize]; bv_omega] at h
  rw [sepConj_comm, ← h]

theorem trApplyStack_to_clearUpkStack (sp : BitVec 64) :
    stackAt (sp - 1504#64) trApplyStack ∗
    memRegion (sp - 262144#64) (tryDecryptSubStack - trApplyStack) ⊢
    stackAt (sp - 1504#64) clearUpkStack ∗
    memRegion (sp - 262144#64) (tryDecryptSubStack - clearUpkStack) := by
  rw [subStack_split_eq sp trApplyStack (by decide), subStack_split_eq sp clearUpkStack (by decide)]
  exact Entails.refl _

theorem clearUpkStack_to_subStack (sp : BitVec 64) :
    stackAt (sp - 1504#64) clearUpkStack ∗
    memRegion (sp - 262144#64) (tryDecryptSubStack - clearUpkStack) ⊢
    stackAt (sp - 1504#64) tryDecryptSubStack := by
  rw [subStack_split_eq sp clearUpkStack (by decide)]; exact Entails.refl _

theorem allocHookStack_to_subStack (sp : BitVec 64) :
    stackAt (sp - 1504#64) allocHookStack ∗
    memRegion (sp - 262144#64) (tryDecryptSubStack - allocHookStack) ⊢
    stackAt (sp - 1504#64) tryDecryptSubStack := by
  rw [subStack_split_eq sp allocHookStack (by decide)]; exact Entails.refl _

theorem SepWP.setPC_setMem_ite_true {prog : Program} {target_pc : BitVec 64}
    {s : State} {m : Memory} {P : SepProp} {post : State → SepProp → Prop}
    {c : Prop} [inst : Decidable c] {pc1 pc2 : BitVec 64} (hc : c)
    (hthen : SepWP prog target_pc ((s.setPC pc1).setMem m) P post) :
    SepWP prog target_pc ((s.setPC (@ite _ c inst pc1 pc2)).setMem m) P post := by
  rw [ite_eq_left_iff.mpr fun hnc => (hnc hc).elim]; exact hthen

theorem SepWP.setPC_setMem_ite_false {prog : Program} {target_pc : BitVec 64}
    {s : State} {m : Memory} {P : SepProp} {post : State → SepProp → Prop}
    {c : Prop} [inst : Decidable c] {pc1 pc2 : BitVec 64} (hnc : ¬ c)
    (helse : SepWP prog target_pc ((s.setPC pc2).setMem m) P post) :
    SepWP prog target_pc ((s.setPC (@ite _ c inst pc1 pc2)).setMem m) P post := by
  rw [ite_eq_right_iff.mpr fun hc => (hnc hc).elim]; exact helse

theorem SepWPp.congr_pre {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop}
    (h : P = P' ∗ emp) (hwp : SepWPp prog ret s P' Q Qp) :
    SepWPp prog ret s P Q Qp := by
  rw [h, sepConj_emp]; exact hwp

theorem extHookStack_to_trApplyStackX (sp : BitVec 64) :
    stackAt (sp - 1504#64) extHookStack ∗
    memRegion (sp - 262144#64) (tryDecryptSubStack - extHookStack) ⊢
    stackAt (sp - 1504#64) trApplyStackX ∗
    memRegion (sp - 262144#64) (tryDecryptSubStack - trApplyStackX) := by
  rw [subStack_split_eq sp extHookStack (by decide), subStack_split_eq sp trApplyStackX (by decide)]
  exact Entails.refl _

theorem trApplyStackX_to_clearUpkStackX (sp : BitVec 64) :
    stackAt (sp - 1504#64) trApplyStackX ∗
    memRegion (sp - 262144#64) (tryDecryptSubStack - trApplyStackX) ⊢
    stackAt (sp - 1504#64) clearUpkStackX ∗
    memRegion (sp - 262144#64) (tryDecryptSubStack - clearUpkStackX) := by
  rw [subStack_split_eq sp trApplyStackX (by decide), subStack_split_eq sp clearUpkStackX (by decide)]
  exact Entails.refl _

theorem clearUpkStackX_to_subStack (sp : BitVec 64) :
    stackAt (sp - 1504#64) clearUpkStackX ∗
    memRegion (sp - 262144#64) (tryDecryptSubStack - clearUpkStackX) ⊢
    stackAt (sp - 1504#64) tryDecryptSubStack := by
  rw [subStack_split_eq sp clearUpkStackX (by decide)]; exact Entails.refl _

theorem extHookStack_to_subStack (sp : BitVec 64) :
    stackAt (sp - 1504#64) extHookStack ∗
    memRegion (sp - 262144#64) (tryDecryptSubStack - extHookStack) ⊢
    stackAt (sp - 1504#64) tryDecryptSubStack := by
  rw [subStack_split_eq sp extHookStack (by decide)]; exact Entails.refl _

end CryptoVerification.LibsignalTripleRatchet.Decrypt.AuthDecrypt
