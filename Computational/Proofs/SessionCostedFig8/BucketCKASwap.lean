/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.FsAtomicBSwap -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.Bundles -- proof-setup: allow-public-import
import Computational.Proofs.SessionCostedFig8.BundlesEval
import Computational.Proofs.Fig8SchemeBridge

/-!
# Atomic Evaluation and `dhSchemeFb` + `fsAtomicB → dhScheme` + `lFS` Bridges for Stage-2 Bucket CKA-/

open Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth (bucketAuthCfg hooksCKABucket implCKABucket redCKAAuthBucket runCKAAuthBucket)
open CryptoGames (CKAScheme FSAEADScheme PRFPRNG Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun dhScheme)
open CryptoGames.FSAEAD (RatchetReceiverState RatchetSenderState)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey maxForwardJumps)
open CryptoGames.Ratchet (rootPRNG)
open CryptoGames.Ratchet.LibsignalInst (LibsignalCiphertextWithSalt32 LibsignalMsgPublicPart lAead lChainPRG lFS lPubOf)
open CryptoGames.SM (Record)
open CryptoGames.SM.Construction (CKAState Header Mode PartyState SchemeAdversary hooksCKA hooksCKA_commit_vR hooksCKA_startRecv_rs initCKA initCKARaw initCKARaw_inv initCKARaw_vrInv sampleT)
open CryptoGames.SM.Engine (Ctx EState Hooks HooksVRInv Policy RSReach SMEngineInv SMVRInv VP abortE challE coinsE commitE corrE deliverE epMgmt_st_eq implE implE_inv implE_vrInv injectE run_liftH_bind transmitE vRecv vSend)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSession.Fig8SchemeBridge (CkaStateInv OptCKASync OptPartySync badSendMsg_query_bind_step badSendMsg_transmit_false ckaBranch_dhSchemeFb_eq ckaFullImpl ckaStateInv_init commitE_ckaSync ddhRoleOk_initA ddhRoleOk_initB liftC_corrQuery_support optPartySync_of_epoch_eq record_st_eq simulateQ_ckaFullImpl_liftProb vRecv_hooksCKA_pure_eq vSend_ckaSync_eq)

namespace Computational.Proofs.SessionCostedFig8.BucketCKASwap

public section

set_option autoImplicit false
set_option linter.dupNamespace false

open OracleSpec OracleComp
open _root_.CryptoGames (Party CKAScheme PRFPRNG FSAEADScheme)
open _root_.CryptoGames.CKA (DHFun dhScheme ckaIface ckaSMCodec)
open _root_.CryptoGames.Ratchet (rootPRNG)
open _root_.CryptoGames.FSAEAD (RatchetSenderState RatchetReceiverState)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.LibsignalSession (Crypto PublicKey IdentityKey maxForwardJumps)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart LibsignalCiphertextWithSalt32
  lFS lAead lPubOf lChainPRG)
open _root_.CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open _root_.CryptoGames.SM (Record Config authLosingConditionsAvoided)
open _root_.CryptoGames.SM.Engine (Policy VP Ctx EState Hooks HooksVRInv SMEngineInv SMVRInv
  RSReach TComp vSend vRecv commitE abortE transmitE challE deliverE injectE corrE coinsE implE
  run_liftH_bind epMgmt_st_eq implE_inv implE_vrInv)
open _root_.CryptoGames.SM.Construction (PartyState SchemeAdversary Header Mode CKAState
  sampleT mkParties hooksCKA hooksCKA_startRecv_rs hooksCKA_commit_vR
  initCKA initCKARaw initCKARaw_inv initCKARaw_vrInv
  hooksCKABucketC bucketAuthCfgEC ckaStartRecvBucketAnsE redCKAAuthBucketProg)
open Computational.Proofs.ReductionDsl.Fig8Atomic (dhSchemeFb aeadAtomic atomicShortPubB
  fsAtomicB fsAtomicB_send_eq fsAtomicB_receive_eq RSReachB)
open Computational.Proofs.SessionCostedFig8.Bundles (fig8CkaOpsShallow)
open Computational.Proofs.SessionCostedFig8.BundlesEval (fsAtomicB_receive_rsReach)
open Computational.Proofs.SessionCostedFig8.FsAtomicBSwap (HooksLocalFsAgree vSend_localFs_eq
  vRecv_localFs_eq)
open _root_.CryptoVerification.LibsignalSession.Fig8SchemeBridge (ddhRoleOk_initA
  ddhRoleOk_initB badSendMsg_query_bind_step badSendMsg_transmit_false
  CkaStateInv OptPartySync OptCKASync ckaFullImpl
  ckaBranch_dhSchemeFb_eq ckaStateInv_init simulateQ_ckaFullImpl_liftProb
  vSend_ckaSync_eq vRecv_hooksCKA_pure_eq commitE_ckaSync liftC_corrQuery_support
  optPartySync_of_epoch_eq record_st_eq)

section CKABucketAtomicSwap

private def noDoomPolicy : Policy := ⟨false, none, 0⟩

@[local simp] private lemma noDoomPolicy_leakDoom {St Msg C : Type}
    (g g' : CryptoGames.SM.GameState St Msg C) :
    noDoomPolicy.leakDoom g g' = false := by
  simp [noDoomPolicy, CryptoGames.SM.Engine.Policy.leakDoom]

@[local simp] private lemma noDoomPolicy_corrDoom {St Msg C : Type}
    (g : CryptoGames.SM.GameState St Msg C) (P : Party) :
    noDoomPolicy.corrDoom g P = false := by
  simp [noDoomPolicy, CryptoGames.SM.Engine.Policy.corrDoom]

private lemma implE_bucketAuth_localFs_eq {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {HS Γ Pt RSt CCoins γV σV : Type} [DecidableEq Pt]
    {ℓ B0 B_q q' Δcka qep : ℕ} {tL : Option ℕ}
    {hk₁ hk₂ : Hooks TSpec HS Γ Pt RSt
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
      CCoins γV σV (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))}
    (hAg : HooksLocalFsAgree ℓ B0 hk₁ hk₂)
    (hVRHk : HooksVRInv (RSReachB maxForwardJumps) hk₂)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (es : EState (VP γV Pt σV (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)) HS)
    (t_sm : (CryptoGames.SM.spec (PartyState Γ Pt RSt (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)))
      (LibsignalMsgPublicPart × Plain ℓ) CCoins
      (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))).Domain)
    (hBad : CryptoGames.LibsignalSM.Proofs.SessionShort.badSendMsg
      (St := PartyState Γ Pt RSt (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256)))
      (Coins := CCoins) (C := Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (fun m => atomicShortPubB m.1) (.inr t_sm) = false)
    (hVR : SMVRInv (RSReachB maxForwardJumps) B_q (q' + 1) es.g) :
    (implE hk₁ (2 + Δcka) qep maxForwardJumps (bucketAuthCfg Δcka tL) noDoomPolicy (.inr t_sm)).run es =
      (implE hk₂ (2 + Δcka) qep maxForwardJumps (bucketAuthCfg Δcka tL) noDoomPolicy (.inr t_sm)).run es := by
  have hkB : (B_q - (q' + 1) + 1) * (maxForwardJumps + 1) ≤ B0 :=
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.sub_le _ _) 1)).trans hB0
  rcases t_sm with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
  · change (transmitE hk₁ (2 + Δcka) qep noDoomPolicy (P, m, r)).run es =
      (transmitE hk₂ (2 + Δcka) qep noDoomPolicy (P, m, r)).run es
    unfold transmitE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win) = true
    · simp [hab]
    · simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁
      · rfl
      · have hm : atomicShortPubB m.1 = true :=
          badSendMsg_transmit_false
            (ok := fun (x : LibsignalMsgPublicPart × Plain ℓ) => atomicShortPubB x.1) hBad
        simp only [noDoomPolicy_leakDoom, Bool.false_eq_true, ↓reduceIte, run_liftH_bind]
        exact congrArg (· >>= _) (vSend_localFs_eq hAg s₁ P (s₁.st P) m none r hm es.h)
  · change (challE hk₁ (2 + Δcka) qep (bucketAuthCfg Δcka tL) noDoomPolicy (P, m₀, m₁, r)).run es =
      (challE hk₂ (2 + Δcka) qep (bucketAuthCfg Δcka tL) noDoomPolicy (P, m₀, m₁, r)).run es
    unfold challE bucketAuthCfg
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win) = true
    · simp [hab]
    · simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁ <;> simp
  · change (deliverE hk₁ maxForwardJumps (bucketAuthCfg Δcka tL) (P, c)).run es =
      (deliverE hk₂ maxForwardJumps (bucketAuthCfg Δcka tL) (P, c)).run es
    have hCommit : commitE hk₁ = commitE hk₂ := by unfold commitE; rw [hAg.commit_eq]
    unfold deliverE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win) = true
    · simp [hab]
    · simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases es.g.inTransit P.other c with _ | r
      · rfl
      · simp only [run_liftH_bind,
          vRecv_localFs_eq hAg hVRHk hkB es.g P (es.g.st P) c (some r) es.h (hVR P), hCommit]
  · change (injectE hk₁ (2 + Δcka) qep (bucketAuthCfg Δcka tL) (P, c)).run es =
      (injectE hk₂ (2 + Δcka) qep (bucketAuthCfg Δcka tL) (P, c)).run es
    have hCommit : commitE hk₁ = commitE hk₂ := by unfold commitE; rw [hAg.commit_eq]
    unfold injectE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases href :
        (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj (2 + Δcka))) = true
    · simp [href]
    · simp only [href, Bool.false_eq_true, ↓reduceIte, run_liftH_bind,
        vRecv_localFs_eq hAg hVRHk hkB es.g P (es.g.st P) c none es.h (hVR P), hCommit]
  · change (corrE hk₁ noDoomPolicy P).run es = (corrE hk₂ noDoomPolicy P).run es
    unfold corrE; rw [hAg.reveal_eq]

private lemma startRecv_hooksCKABucket_eq
    {KC Γ CCoins T I KR Sig K SS RS M E : Type} [DecidableEq T] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (tL : Option ℕ)
    (ctx : Ctx (Option Γ) T Sig SS RS M E) (P : Party) (t : ℕ)
    (γv : Option Γ) (σ : Sig) (Tn : T) :
    (hooksCKABucket cka prng fs Δcka tL).startRecv ctx P t γv σ Tn =
      (hooksCKA cka prng fs Δcka
        ⟨true, tL, if CryptoGames.SM.lastLeakGuessAdmissible (2 + Δcka) tL t then t else t + 1⟩).startRecv
        ctx P t γv σ Tn := by
  ext h
  simp only [hooksCKABucket, hooksCKA, StateT.run_bind, StateT.run_get, pure_bind]
  cases h.cache t with
  | none =>
    cases hb : CryptoGames.SM.lastLeakGuessAdmissible (2 + Δcka) tL t
    · simp
    · simp; rfl
  | some pair =>
    rcases pair with ⟨Tc, Ik⟩
    by_cases hTc : Tc = Tn
    · simp [hTc]
    · cases hb : CryptoGames.SM.lastLeakGuessAdmissible (2 + Δcka) tL t
      · simp [hTc]
      · simp [hTc]; rfl

private lemma vRecv_hooksCKABucket_eq
    {KC Γ CCoins T I KR Sig K SS RS M E : Type} [DecidableEq T] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (tL : Option ℕ)
    (ctx : Ctx (Option Γ) T Sig SS RS M E) (P : Party)
    (vp : PartyState (Option Γ) T Sig SS RS) (c : Header T × E)
    (rec : Option (Record M (Header T × E))) :
    vRecv (hooksCKABucket cka prng fs Δcka tL) ctx P vp c rec =
      vRecv (hooksCKA cka prng fs Δcka
        ⟨true, tL, if CryptoGames.SM.lastLeakGuessAdmissible (2 + Δcka) tL c.1.1 then c.1.1 else c.1.1 + 1⟩)
        ctx P vp c rec := by
  unfold vRecv
  by_cases h1 : (vp.id.sendsIn c.1.1 || decide (vp.tcur + 1 < c.1.1)) = true
  · simp only [h1, ↓reduceIte]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : c.1.1 = vp.tcur + 1
    · simp only [h2, ↓reduceIte, startRecv_hooksCKABucket_eq]; rfl
    · simp only [h2, ↓reduceIte]; rfl

theorem hooksCKABucket_startRecv_rs
    {KC Γ CCoins T I KR RSt K SS RS M E : Type} [DecidableEq T] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (tL : Option ℕ)
    {VROk : RS → Prop} (hInitR : ∀ k, VROk (fs.initReceiver k))
    (ctx : Ctx (Option Γ) T RSt SS RS M E) (P : Party) (t0 : ℕ)
    (γ0 : Option Γ) (σ0 : RSt) (tn0 : T) (h : CKAState T I)
    (res : Option (Option (Option Γ × RSt × RS)) × CKAState T I)
    (hmem : res ∈ support ((hooksCKABucket cka prng fs Δcka tL).startRecv
      ctx P t0 γ0 σ0 tn0 |>.run h))
    (γ' : Option Γ) (σ' : RSt) (rs : RS) (hEq : res.1 = some (some (γ', σ', rs))) :
    VROk rs := by
  rw [startRecv_hooksCKABucket_eq] at hmem
  exact hooksCKA_startRecv_rs cka prng fs Δcka _ hInitR ctx P t0 γ0 σ0 tn0 h res hmem γ' σ' rs hEq

private lemma hooksCKABucket_vrInv_lFS {KC Γ CCoins Pt I KR RSt : Type}
    [DecidableEq Pt] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (Δcka : ℕ) (tL : Option ℕ) :
    HooksVRInv (RSReachB maxForwardJumps)
      (hooksCKABucket cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka tL) where
  mono hle hv := hv.mono hle
  startRecv_step ctx P t γ σ Tn h :=
    hooksCKABucket_startRecv_rs cka prng
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka tL
      (Computational.Proofs.ReductionDsl.Fig8Atomic.RSReachB.init ((lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD
        (lPubOf protoSignalCodec)) (lChainPRG C.F) maxForwardJumps)
      ctx P t γ σ Tn h
  fsRecv_step _ _ _ rs hdr e _ _ res hVR hmem v' i' m' hEq := by
    rcases res with ⟨ans, h'⟩
    dsimp only at hEq; subst hEq
    dsimp only [hooksCKABucket, hooksCKA] at hmem
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq, Option.some.injEq] at hmem
    exact (Computational.Proofs.ReductionDsl.Fig8Atomic.RSReachB.receive_fromAEADPRG
      ((lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
      (lChainPRG C.F) maxForwardJumps _ hVR hmem.1.symm).2
  commit_vR :=
    hooksCKA_commit_vR cka prng
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka ⟨true, tL, 0⟩

private lemma hooksCKABucket_localFsAgree {KC Γ CCoins Pt I KR RSt : Type}
    [DecidableEq Pt] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (B0 Δcka : ℕ) (tL : Option ℕ) :
    HooksLocalFsAgree ℓ B0
      (hooksCKABucket cka prng (fsAtomicB C ℓ encT idOf B0) Δcka tL)
      (hooksCKABucket cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka tL) where
  startSend_eq := by unfold hooksCKABucket hooksCKA fsAtomicB lFS CryptoGames.FSAEAD.fromAEADPRG; rfl
  startRecv_eq := by unfold hooksCKABucket fsAtomicB lFS CryptoGames.FSAEAD.fromAEADPRG; rfl
  fsSend_eq _ _ _ ss hdr m _ hm := by
    dsimp only [hooksCKABucket, hooksCKA]
    rw [fsAtomicB_send_eq C ℓ encT idOf B0 ss hdr m hm]
  fsRecv_eq _ _ _ rs hdr e _ hlen := by
    dsimp only [hooksCKABucket, hooksCKA]
    rw [fsAtomicB_receive_eq C ℓ encT idOf B0 rs hdr e hlen]
  commit_eq := by unfold hooksCKABucket hooksCKA; rfl
  reveal_eq := by unfold hooksCKABucket hooksCKA; rfl

private def ckaBucketUpdateWinEp {Γ T Sig SS RS M E I CCoins : Type}
    (es0 es' : EState (VP (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I))
    (qy : (unifSpec + CryptoGames.SM.spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Domain)
    (winEp0 : Option ℕ) : Option ℕ :=
  match qy with
  | .inr (.inl (.inr x)) => if !es0.g.win && es'.g.win then some x.2.1.1 else winEp0
  | _ => winEp0

private lemma implCKABucket_run_eq_implE
    {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ)
    (qy : (unifSpec + CryptoGames.SM.spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Domain)
    (es0 : EState (VP (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I))
    (winEp0 : Option ℕ) :
    (implCKABucket cka prng fs Δcka qep tL qy).run (es0, winEp0) =
      ((implE (hooksCKABucket cka prng fs Δcka tL) (2 + Δcka) qep fs.maxSkip
          (bucketAuthCfg Δcka tL) noDoomPolicy qy).run es0 >>=
        fun res => pure (res.1,
          (res.2, ckaBucketUpdateWinEp es0 res.2 qy winEp0))) := by
  rcases qy with n | ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
  · dsimp only [implCKABucket, implE, QueryImpl.add_apply, coinsE, ckaBucketUpdateWinEp]
    simp [StateT.run_lift]
  · dsimp only [implCKABucket, implE, QueryImpl.add_apply, transmitE, ckaBucketUpdateWinEp]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hcond : (es0.abort || es0.g.win) = true
    · simp [hcond]
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte]
      cases hep : es0.g.epMgmt (2 + Δcka) qep P r.isSome with
      | none => simp
      | some s₁ =>
        simp only [noDoomPolicy_leakDoom, Bool.false_eq_true, ↓reduceIte]
        rw [StateT.run_bind, StateT.run_lift, run_liftH_bind]
        simp only [bind_assoc, pure_bind]
        refine bind_congr fun ⟨res, h'⟩ => ?_
        rcases res with _ | ⟨st', ct⟩ <;> simp [abortE]
  · dsimp only [implCKABucket, implE, QueryImpl.add_apply, challE,
      bucketAuthCfg, ckaBucketUpdateWinEp]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hcond : (es0.abort || es0.g.win) = true
    · simp [hcond]
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte]
      cases hep : es0.g.epMgmt (2 + Δcka) qep P r.isSome <;> simp
  · dsimp only [implCKABucket, implE, QueryImpl.add_apply, ckaBucketUpdateWinEp]
    simp [StateT.run_lift]
  · dsimp only [implCKABucket, implE, QueryImpl.add_apply, ckaBucketUpdateWinEp]
    simp only [StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set,
      StateT.run_pure, bind_assoc, pure_bind]
    refine bind_congr fun ⟨out, es'⟩ => rfl
  · dsimp only [implCKABucket, implE, QueryImpl.add_apply, corrE, ckaBucketUpdateWinEp]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hcond : (es0.abort || es0.g.win || !es0.g.corrAllowed P) = true
    · simp [hcond]
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte,
        noDoomPolicy_leakDoom, noDoomPolicy_corrDoom, Bool.or_self]
      rw [StateT.run_bind, StateT.run_lift, run_liftH_bind]
      simp only [bind_assoc, pure_bind]
      refine bind_congr fun ⟨res, h'⟩ => ?_
      cases res <;> simp [abortE]

private lemma simulateQ_implCKABucket_localFs_eq
    {KC Γ CCoins Pt I KR RSt α : Type} [DecidableEq Pt] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (B0 B_q q Δcka qep : ℕ) (tL : Option ℕ)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    {oa : OracleComp (unifSpec + CryptoGames.SM.spec
      (PartyState Γ Pt RSt (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256)))
      (LibsignalMsgPublicPart × Plain ℓ) CCoins
      (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))) α}
    (hq : oa.IsQueryBoundP
      (ReductionDsl.isGameQuery (G := CryptoGames.SM.spec
        (PartyState Γ Pt RSt (RatchetSenderState (BitVec 256))
          (RatchetReceiverState (BitVec 256) (BitVec 256)))
        (LibsignalMsgPublicPart × Plain ℓ) CCoins
        (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)))) q)
    (hSendOk : oa.IsQueryBoundP
      (fun t => CryptoGames.LibsignalSM.Proofs.SessionShort.badSendMsg
        (St := PartyState Γ Pt RSt (RatchetSenderState (BitVec 256))
          (RatchetReceiverState (BitVec 256) (BitVec 256)))
        (Coins := CCoins) (C := Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
        (fun m => atomicShortPubB m.1) t = true) 0)
    (es : EState (VP (Option Γ) Pt RSt (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (CKAState Pt I))
    (winEp : Option ℕ)
    (hInv : SMEngineInv (B_q + 1) B_q q es.g)
    (hVR : SMVRInv (RSReachB maxForwardJumps) B_q q es.g) :
    (simulateQ (implCKABucket cka prng (fsAtomicB C ℓ encT idOf B0) Δcka qep tL) oa).run (es, winEp) =
      (simulateQ (implCKABucket cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka qep tL)
        oa).run (es, winEp) := by
  let hk₁ := hooksCKABucket cka prng (fsAtomicB C ℓ encT idOf B0) Δcka tL
  let hk₂ := hooksCKABucket cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka tL
  have hAg := hooksCKABucket_localFsAgree cka prng C ℓ encT idOf B0 Δcka tL
  have hVRHk := hooksCKABucket_vrInv_lFS cka prng C ℓ encT idOf Δcka tL
  induction oa using OracleComp.inductionOn generalizing q es winEp with
  | pure _ => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind qy mx ih =>
    obtain ⟨hq0, hmx⟩ := (OracleComp.isQueryBoundP_query_bind_iff _ _ _ _).mp hq
    obtain ⟨hBad, hSendMx⟩ := badSendMsg_query_bind_step
      (fun (m : LibsignalMsgPublicPart × Plain ℓ) => atomicShortPubB m.1) qy mx hSendOk
    rw [simulateQ_query_bind, simulateQ_query_bind, StateT.run_bind, StateT.run_bind]
    have hLift : ∀ {M' : Type → Type} [Monad M'] {σ' α' : Type} (m : StateT σ' M' α') (s : σ'),
        (liftM m : StateT σ' M' α').run s = m.run s := fun _ _ => rfl
    rw [hLift, hLift]
    simp only [OracleQuery.input_query, OracleQuery.cont_query]
    have hFsMax1 : (fsAtomicB C ℓ encT idOf B0).maxSkip = maxForwardJumps := rfl
    have hFsMax2 : (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip = maxForwardJumps := rfl
    rw [implCKABucket_run_eq_implE, implCKABucket_run_eq_implE, hFsMax1, hFsMax2]
    rcases qy with n | t_sm
    · have hInl₁ : (implE hk₁ (2 + Δcka) qep maxForwardJumps (bucketAuthCfg Δcka tL)
          noDoomPolicy (.inl n)).run es = (coinsE n).run es := rfl
      have hInl₂ : (implE hk₂ (2 + Δcka) qep maxForwardJumps (bucketAuthCfg Δcka tL)
          noDoomPolicy (.inl n)).run es = (coinsE n).run es := rfl
      rw [hInl₁, hInl₂, bind_assoc, bind_assoc]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, es'⟩ hmem => ?_
      simp only [coinsE, StateT.run_lift, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hmem
      obtain ⟨_, _, hEq⟩ := hmem
      rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
      simp only [pure_bind, ckaBucketUpdateWinEp]
      exact ih u q (by simpa [ReductionDsl.isGameQuery] using hmx u) (hSendMx u) es' winEp hInv hVR
    · simp only [ReductionDsl.isGameQuery, ↓reduceIte] at hq0 hmx
      have hqp : 0 < q := hq0.resolve_left (by decide)
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      rw [implE_bucketAuth_localFs_eq hAg hVRHk hB0 es t_sm hBad hVR, bind_assoc, bind_assoc]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, es'⟩ hmem => ?_
      simp only [pure_bind]
      have hInv' := implE_inv hk₂ (bucketAuthCfg Δcka tL) noDoomPolicy es t_sm hInv (u, es') hmem
      have hVR' := implE_vrInv hk₂ hVRHk (bucketAuthCfg Δcka tL) noDoomPolicy es t_sm
        hInv hVR (u, es') hmem
      exact ih u q' (by simpa using hmx u) (hSendMx u) es' _ hInv' hVR'

private lemma runCKAAuthBucket_eq_bind_initCKARaw
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ) (tL : Option ℕ)
    (A : SchemeAdversary Γ T RSt SS RS M CCoins E) :
    runCKAAuthBucket cka prng fs lam Δcka qep tL A =
      (do
        let es₀ ← initCKARaw cka prng fs lam ⟨true, tL, 0⟩ false
        let res ← (simulateQ (implCKABucket cka prng fs Δcka qep tL) A).run (es₀, none)
        return some (res.1, res.2.1, res.2.2)) := by
  unfold runCKAAuthBucket initCKA initCKARaw
  simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  refine bind_congr fun kr => ?_
  rcases tL with _ | l
  · simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind,
      bind_map_left]; rfl
  · simp only [StateT.run_pure, pure_bind]; rfl

theorem redCKAAuthBucket_fsAtomicB_eq_lFS
    {KC Γ CCoins Pt I KR RSt : Type} [DecidableEq Pt]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : I) (B0 B_q Δcka qep : ℕ) (tL : Option ℕ)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (A : SchemeAdversary Γ Pt RSt
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) CCoins (ℕ × LibsignalCiphertextWithSalt32))
    (qAdv : ℕ) (hA : CryptoGames.SM.MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q)
    (hSendOk : CryptoGames.LibsignalSM.Proofs.SessionShort.SendMsgsOk
      (fun (m : LibsignalMsgPublicPart × Plain ℓ) => atomicShortPubB m.1) A) :
    redCKAAuthBucket cka prng (fsAtomicB C ℓ encT idOf B0) lam Δcka qep tL A =
      redCKAAuthBucket cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep tL A := by
  have hA' : A.IsQueryBoundP
      (ReductionDsl.isGameQuery (G := CryptoGames.SM.spec
        (PartyState Γ Pt RSt (RatchetSenderState (BitVec 256))
          (RatchetReceiverState (BitVec 256) (BitVec 256)))
        (LibsignalMsgPublicPart × Plain ℓ) CCoins
        (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)))) qAdv := by
    refine hA.of_imp fun x hx => ?_
    rcases x with _ | _ <;> simp_all [ReductionDsl.isGameQuery]
  unfold redCKAAuthBucket
  rw [runCKAAuthBucket_eq_bind_initCKARaw, runCKAAuthBucket_eq_bind_initCKARaw]
  have hInitEq :
      initCKARaw cka prng (fsAtomicB C ℓ encT idOf B0) lam ⟨true, tL, 0⟩ false =
        initCKARaw cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
          lam ⟨true, tL, 0⟩ false := by
    unfold initCKARaw fsAtomicB lFS CryptoGames.FSAEAD.fromAEADPRG; rfl
  rw [hInitEq]
  simp only [bind_assoc]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun es₀ hes₀ => ?_
  have hB1 : B_q + 1 ≤ B_q + 1 := le_rfl
  have hBB : B_q * B_q ≤ (B_q + 1) * (B_q + 1) :=
    Nat.mul_le_mul (Nat.le_succ _) (Nat.le_succ _)
  have ⟨hInv₀, _⟩ := initCKARaw_inv cka prng
    (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam ⟨true, tL, 0⟩ false
    hqB hB1 hBB es₀ hes₀
  have hVRHk := hooksCKABucket_vrInv_lFS cka prng C ℓ encT idOf Δcka tL
  have hVR₀ := initCKARaw_vrInv (B := B_q) (qAdv := qAdv) cka prng
    (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam ⟨true, tL, 0⟩ false
    (fun k => hVRHk.mono (Nat.zero_le _)
      (Computational.Proofs.ReductionDsl.Fig8Atomic.RSReachB.init ((lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD
        (lPubOf protoSignalCodec)) (lChainPRG C.F) maxForwardJumps k)) es₀ hes₀
  rw [simulateQ_implCKABucket_localFs_eq cka prng C ℓ encT idOf B0 B_q qAdv Δcka qep tL
    hB0 hA' hSendOk es₀ none hInv₀ hVR₀]

private lemma implE_hooksCKABucket_ckaSync_eq
    {Pt KR RSt K SS RS M E : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [SampleableType K]
    [DecidableEq M] [DecidableEq E] [Inhabited E]
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E) (Δcka tStar qep maxSkip : ℕ) (tL : Option ℕ)
    (es : EState (VP (Option (CryptoGames.CKA.DDH.State (BitVec 256) Pt)) Pt RSt SS RS)
      M (Header Pt × E) (CKAState Pt Pt))
    (sc : CryptoGames.CKA.GameState (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt)
    (t : (CryptoGames.SM.spec
      (PartyState (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt SS RS) M (BitVec 256)
      (Header Pt × E)).Domain)
    (hSync : OptCKASync es sc) :
    (simulateQ (ckaFullImpl (dhScheme Dh) Δcka tStar)
      ((implE (hooksCKABucket (dhSchemeFb Dh) prng fs Δcka tL) (2 + Δcka) qep maxSkip
        (bucketAuthCfg Δcka tL) noDoomPolicy (.inr t)).run es)).run sc =
    (simulateQ (ckaFullImpl (dhScheme Dh) Δcka tStar)
      ((implE (hooksCKABucket (dhScheme Dh) prng fs Δcka tL) (2 + Δcka) qep maxSkip
        (bucketAuthCfg Δcka tL) noDoomPolicy (.inr t)).run es)).run sc ∧
    ∀ z ∈ support ((simulateQ (ckaFullImpl (dhScheme Dh) Δcka tStar)
      ((implE (hooksCKABucket (dhScheme Dh) prng fs Δcka tL) (2 + Δcka) qep maxSkip
        (bucketAuthCfg Δcka tL) noDoomPolicy (.inr t)).run es)).run sc),
      OptCKASync z.1.2 z.2 := by
  let hk₁ := hooksCKABucket (dhSchemeFb Dh) prng fs Δcka tL
  let hk₂ := hooksCKABucket (dhScheme Dh) prng fs Δcka tL
  let mo₀ : Mode := ⟨true, tL, 0⟩
  rcases t with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
  · have hI₁ : implE hk₁ (2 + Δcka) qep maxSkip (bucketAuthCfg Δcka tL) noDoomPolicy
        (.inr (.inl (.inl (.inl (.inl (P, m, r)))))) =
        transmitE hk₁ (2 + Δcka) qep noDoomPolicy (P, m, r) := rfl
    have hI₂ : implE hk₂ (2 + Δcka) qep maxSkip (bucketAuthCfg Δcka tL) noDoomPolicy
        (.inr (.inl (.inl (.inl (.inl (P, m, r)))))) =
        transmitE hk₂ (2 + Δcka) qep noDoomPolicy (P, m, r) := rfl
    rw [hI₁, hI₂]; unfold transmitE abortE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win) = true
    · simp only [hab, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
      exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
    · have habF : es.abort = false := (Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hab)).1
      simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases hep : es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
        exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
      · have hs₁All : ∀ Q, OptPartySync sc Q (s₁.st Q) := fun Q => by
          rw [epMgmt_st_eq hep]; exact hSync.2 habF Q
        have hvs := vSend_ckaSync_eq Dh prng fs Δcka tStar mo₀ s₁ P (s₁.st P) m none r es.h sc
          hSync.1 (hs₁All P)
        have hvs₁ : vSend hk₁ = vSend (hooksCKA (dhSchemeFb Dh) prng fs Δcka mo₀) := rfl
        have hvs₂ : vSend hk₂ = vSend (hooksCKA (dhScheme Dh) prng fs Δcka mo₀) := rfl
        simp only [noDoomPolicy_leakDoom, Bool.false_eq_true, ↓reduceIte, hvs₁, hvs₂]
        rw [run_liftH_bind, run_liftH_bind]
        simp only [simulateQ_bind, StateT.run_bind]
        rw [hvs.1]
        refine ⟨rfl, fun z hz => ?_⟩
        rw [mem_support_bind_iff] at hz
        obtain ⟨⟨⟨vsRes, h'⟩, sc₁⟩, hvsMem, hz⟩ := hz
        have ⟨hsc₁, hvsPost⟩ := hvs.2 _ hvsMem
        rcases vsRes with _ | ⟨st', ct⟩
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact ⟨hsc₁, fun h' => nomatch h'⟩
        · obtain ⟨hst'P, hepQ⟩ := hvsPost st' ct rfl
          simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz
          refine ⟨hsc₁, fun _ Q => ?_⟩
          by_cases hQP : Q = P
          · subst hQP; simp [record_st_eq, hst'P]
          · simp [record_st_eq, Function.update_of_ne hQP]
            exact optPartySync_of_epoch_eq (hs₁All Q) (hepQ Q hQP)
  · have hI₁ : implE hk₁ (2 + Δcka) qep maxSkip (bucketAuthCfg Δcka tL) noDoomPolicy
        (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r)))))) =
        challE hk₁ (2 + Δcka) qep (bucketAuthCfg Δcka tL) noDoomPolicy (P, m₀, m₁, r) := rfl
    have hI₂ : implE hk₂ (2 + Δcka) qep maxSkip (bucketAuthCfg Δcka tL) noDoomPolicy
        (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r)))))) =
        challE hk₂ (2 + Δcka) qep (bucketAuthCfg Δcka tL) noDoomPolicy (P, m₀, m₁, r) := rfl
    rw [hI₁, hI₂]; unfold challE bucketAuthCfg
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win) = true
    · simp only [hab, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
      exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
    · simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases hep : es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁ <;>
        (simp only [Bool.not_false, Bool.or_true, ↓reduceIte, StateT.run_pure, simulateQ_pure,
          support_pure, Set.mem_singleton_iff];
         exact ⟨trivial, fun _ h => by subst h; exact hSync⟩)
  · have hI₁ : implE hk₁ (2 + Δcka) qep maxSkip (bucketAuthCfg Δcka tL) noDoomPolicy
        (.inr (.inl (.inl (.inr (P, c))))) =
        deliverE hk₁ maxSkip (bucketAuthCfg Δcka tL) (P, c) := rfl
    have hI₂ : implE hk₂ (2 + Δcka) qep maxSkip (bucketAuthCfg Δcka tL) noDoomPolicy
        (.inr (.inl (.inl (.inr (P, c))))) =
        deliverE hk₂ maxSkip (bucketAuthCfg Δcka tL) (P, c) := rfl
    rw [hI₁, hI₂]; unfold deliverE abortE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win) = true
    · simp only [hab, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
      exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
    · have habF : es.abort = false := (Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hab)).1
      simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases htr : es.g.inTransit P.other c with _ | r
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
        exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
      · let moC : Mode :=
          ⟨true, tL, if CryptoGames.SM.lastLeakGuessAdmissible (2 + Δcka) tL c.1.1 then c.1.1 else c.1.1 + 1⟩
        obtain ⟨hvrEq, ⟨⟨vrRes, h'⟩, hvrPure, hvrPost⟩⟩ :=
          vRecv_hooksCKA_pure_eq Dh prng fs Δcka moC es.g P (es.g.st P) c (some r) es.h sc
            (hSync.2 habF P)
        rw [run_liftH_bind, run_liftH_bind]
        dsimp only [hk₁, hk₂]
        rw [vRecv_hooksCKABucket_eq, vRecv_hooksCKABucket_eq, hvrEq, hvrPure]
        simp only [pure_bind]
        rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            simulateQ_pure, support_pure, Set.mem_singleton_iff]
          exact ⟨trivial, fun _ h => by subst h; exact ⟨hSync.1, fun h' => nomatch h'⟩⟩
        · split_ifs <;>
            (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
               simulateQ_pure, support_pure, Set.mem_singleton_iff];
             exact ⟨trivial, fun _ h => by subst h; exact hSync⟩)
        · have hcm₁ : commitE (hooksCKABucket (dhSchemeFb Dh) prng fs Δcka tL) =
              commitE (hooksCKA (dhSchemeFb Dh) prng fs Δcka mo₀) := rfl
          have hcm₂ : commitE (hooksCKABucket (dhScheme Dh) prng fs Δcka tL) =
              commitE (hooksCKA (dhScheme Dh) prng fs Δcka mo₀) := rfl
          have hcm := commitE_ckaSync Dh prng fs Δcka tStar mo₀ es.g P (es.g.st P) st' r.pos
            { es with h := h' } sc hSync.1 (hSync.2 habF) hSync.2 (hvrPost st' t' i' m' rfl)
          simp only [StateT.run_bind, simulateQ_bind, hcm₁, hcm₂]
          rw [hcm.1]
          refine ⟨rfl, fun z hz => ?_⟩
          rw [mem_support_bind_iff] at hz
          obtain ⟨⟨⟨cmRes, es₁⟩, sc₁⟩, hcmMem, hz⟩ := hz
          obtain ⟨hsc₁, hcmNone, hcmSome⟩ := hcm.2 _ hcmMem
          rcases cmRes with _ | s₁
          · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact hcmNone rfl
          · obtain ⟨_, hs₁Sync⟩ := hcmSome s₁ rfl
            simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz
            refine ⟨hsc₁, fun _ Q => ?_⟩
            split_ifs <;> exact hs₁Sync Q
  · have hI₁ : implE hk₁ (2 + Δcka) qep maxSkip (bucketAuthCfg Δcka tL) noDoomPolicy
        (.inr (.inl (.inr (P, c)))) =
        injectE hk₁ (2 + Δcka) qep (bucketAuthCfg Δcka tL) (P, c) := rfl
    have hI₂ : implE hk₂ (2 + Δcka) qep maxSkip (bucketAuthCfg Δcka tL) noDoomPolicy
        (.inr (.inl (.inr (P, c)))) =
        injectE hk₂ (2 + Δcka) qep (bucketAuthCfg Δcka tL) (P, c) := rfl
    rw [hI₁, hI₂]; unfold injectE abortE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases href :
        (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj (2 + Δcka))) = true
    · simp only [href, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
      exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
    · have habF : es.abort = false := by
        rcases Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr href) with ⟨h1, _⟩
        rcases Bool.or_eq_false_iff.mp h1 with ⟨h2, _⟩
        exact (Bool.or_eq_false_iff.mp h2).1
      let moC : Mode :=
        ⟨true, tL, if CryptoGames.SM.lastLeakGuessAdmissible (2 + Δcka) tL c.1.1 then c.1.1 else c.1.1 + 1⟩
      obtain ⟨hvrEq, ⟨⟨vrRes, h'⟩, hvrPure, hvrPost⟩⟩ :=
        vRecv_hooksCKA_pure_eq Dh prng fs Δcka moC es.g P (es.g.st P) c none es.h sc
          (hSync.2 habF P)
      simp only [href, Bool.false_eq_true, ↓reduceIte]
      rw [run_liftH_bind, run_liftH_bind]
      dsimp only [hk₁, hk₂]
      rw [vRecv_hooksCKABucket_eq, vRecv_hooksCKABucket_eq, hvrEq, hvrPure]
      simp only [pure_bind]
      rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          simulateQ_pure, support_pure, Set.mem_singleton_iff]
        exact ⟨trivial, fun _ h => by subst h; exact ⟨hSync.1, fun h' => nomatch h'⟩⟩
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
        exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
      · by_cases hqep : qep + 1 < t'
        · simp only [hqep, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
            Set.mem_singleton_iff]
          exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
        · simp only [hqep, ↓reduceIte]
          by_cases htriv : es.g.trivial (2 + Δcka) ⟨P.other, t', i'⟩ = true
          · have hcm₁ : commitE (hooksCKABucket (dhSchemeFb Dh) prng fs Δcka tL) =
                commitE (hooksCKA (dhSchemeFb Dh) prng fs Δcka mo₀) := rfl
            have hcm₂ : commitE (hooksCKABucket (dhScheme Dh) prng fs Δcka tL) =
                commitE (hooksCKA (dhScheme Dh) prng fs Δcka mo₀) := rfl
            have hcm := commitE_ckaSync Dh prng fs Δcka tStar mo₀ es.g P (es.g.st P) st'
              ⟨P.other, t', i'⟩ { es with h := h' } sc hSync.1 (hSync.2 habF) hSync.2
              (hvrPost st' t' i' m' rfl)
            simp only [htriv, ↓reduceIte, StateT.run_bind, simulateQ_bind, hcm₁, hcm₂]
            rw [hcm.1]
            refine ⟨rfl, fun z hz => ?_⟩
            rw [mem_support_bind_iff] at hz
            obtain ⟨⟨⟨cmRes, es₁⟩, sc₁⟩, hcmMem, hz⟩ := hz
            obtain ⟨hsc₁, hcmNone, hcmSome⟩ := hcm.2 _ hcmMem
            rcases cmRes with _ | s₁
            · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
              subst hz; exact hcmNone rfl
            · obtain ⟨_, hs₁Sync⟩ := hcmSome s₁ rfl
              simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
              subst hz; exact ⟨hsc₁, fun _ => hs₁Sync⟩
          · simp only [htriv, Bool.false_eq_true, ↓reduceIte]
            split_ifs <;>
              (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                 simulateQ_pure, support_pure, Set.mem_singleton_iff];
               exact ⟨trivial, fun _ h => by subst h; exact hSync⟩)
  · have hI₁ : implE hk₁ (2 + Δcka) qep maxSkip (bucketAuthCfg Δcka tL) noDoomPolicy
        (.inr (.inr P)) = corrE hk₁ noDoomPolicy P := rfl
    have hI₂ : implE hk₂ (2 + Δcka) qep maxSkip (bucketAuthCfg Δcka tL) noDoomPolicy
        (.inr (.inr P)) = corrE hk₂ noDoomPolicy P := rfl
    rw [hI₁, hI₂]
    have hRevEq : hk₁.reveal = hk₂.reveal := rfl
    unfold corrE abortE
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hRevEq]
    refine ⟨trivial, fun z hz => ?_⟩
    by_cases href : (es.abort || es.g.win || !(es.g.corrAllowed P)) = true
    · simp only [href, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz; exact hSync
    · simp only [href, Bool.false_eq_true, ↓reduceIte, noDoomPolicy_leakDoom,
        noDoomPolicy_corrDoom, Bool.or_self] at hz
      rw [run_liftH_bind] at hz
      simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨⟨⟨revRes, h'⟩, sc₁⟩, hrev, hz⟩ := hz
      have hsc₁_eq : sc₁ = sc := by
        dsimp only [hk₂, hooksCKABucket, hooksCKA] at hrev
        rcases hγ : (es.g.st P).γ with _ | γ
        · simp only [hγ, StateT.run_bind, simulateQ_bind, mem_support_bind_iff] at hrev
          obtain ⟨⟨⟨corrAns, h₂⟩, sc₂⟩, hcorr, hrev⟩ := hrev
          have ⟨heq, _⟩ := liftC_corrQuery_support Dh Δcka tStar P es.h sc hSync.1 hcorr
          subst heq
          rcases corrAns with _ | γ' <;>
            (simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hrev;
             exact (Prod.mk.inj hrev).2)
        · simp only [hγ, pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at hrev
          exact (Prod.mk.inj hrev).2
      subst hsc₁_eq
      rcases revRes with _ | stP
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact ⟨hSync.1, fun h' => nomatch h'⟩
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hSync

private lemma simulateQ_implCKABucket_ckaSync_eq
    {Pt KR RSt K SS RS M E α : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [SampleableType K]
    [DecidableEq M] [DecidableEq E] [Inhabited E]
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E) (Δcka tStar qep : ℕ) (tL : Option ℕ)
    (oa : OracleComp (unifSpec + CryptoGames.SM.spec
      (PartyState (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt SS RS)
      M (BitVec 256) (Header Pt × E)) α)
    (es : EState (VP (Option (CryptoGames.CKA.DDH.State (BitVec 256) Pt)) Pt RSt SS RS)
      M (Header Pt × E) (CKAState Pt Pt))
    (winEp : Option ℕ)
    (sc : CryptoGames.CKA.GameState (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt)
    (hSync : OptCKASync es sc) :
    (simulateQ (ckaFullImpl (dhScheme Dh) Δcka tStar)
      ((simulateQ (implCKABucket (dhSchemeFb Dh) prng fs Δcka qep tL) oa).run (es, winEp))).run sc =
    (simulateQ (ckaFullImpl (dhScheme Dh) Δcka tStar)
      ((simulateQ (implCKABucket (dhScheme Dh) prng fs Δcka qep tL) oa).run (es, winEp))).run sc := by
  induction oa using OracleComp.inductionOn generalizing es winEp sc with
  | pure x => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind qy mx ih =>
    rw [simulateQ_query_bind, simulateQ_query_bind, StateT.run_bind, StateT.run_bind,
      simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind]
    have hLift : ∀ {M' : Type → Type} [Monad M'] {σ' α' : Type} (m : StateT σ' M' α') (s : σ'),
        (liftM m : StateT σ' M' α').run s = m.run s := fun _ _ => rfl
    rw [hLift, hLift]
    simp only [OracleQuery.input_query, OracleQuery.cont_query]
    rw [implCKABucket_run_eq_implE, implCKABucket_run_eq_implE]
    simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, bind_assoc]
    rcases qy with n | t_sm
    · have hInl₁ :
          (implE (hooksCKABucket (dhSchemeFb Dh) prng fs Δcka tL) (2 + Δcka) qep fs.maxSkip
            (bucketAuthCfg Δcka tL) noDoomPolicy (.inl n)).run es = (coinsE n).run es := rfl
      have hInl₂ :
          (implE (hooksCKABucket (dhScheme Dh) prng fs Δcka tL) (2 + Δcka) qep fs.maxSkip
            (bucketAuthCfg Δcka tL) noDoomPolicy (.inl n)).run es = (coinsE n).run es := rfl
      rw [hInl₁, hInl₂]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨u, es'⟩, sc'⟩ hmem => ?_
      simp only [coinsE, StateT.run_lift, simulateQ_bind, simulateQ_HasQuery_query,
        simulateQ_pure, StateT.run_bind, StateT.run_pure] at hmem
      have hInlQ : ckaFullImpl (dhScheme Dh) Δcka tStar (Sum.inl n) =
          StateT.lift ($ᵗ (Fin (n + 1)) : ProbComp (Fin (n + 1))) := rfl
      rw [hInlQ, StateT.run_lift] at hmem
      simp only [bind_assoc, pure_bind, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hmem
      obtain ⟨_, _, hEq⟩ := hmem
      rcases Prod.mk.inj hEq with ⟨hEq1, hscEq⟩
      rcases Prod.mk.inj hEq1 with ⟨rfl, hesEq⟩
      simp only [pure_bind, ckaBucketUpdateWinEp]
      rw [hesEq, hscEq]
      exact ih u es winEp sc hSync
    · obtain ⟨hEq, hPost⟩ :=
        implE_hooksCKABucket_ckaSync_eq Dh prng fs Δcka tStar qep fs.maxSkip tL es sc t_sm hSync
      rw [hEq]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨u, es'⟩, sc'⟩ hmem => ?_
      simp only [pure_bind]
      exact ih u es' _ sc' (hPost _ hmem)

theorem ckaBranch_redCKAAuthBucket_dhSchemeFb_eq
    {Pt KR RSt K SS RS M E : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [SampleableType KR] [SampleableType K]
    [DecidableEq M] [DecidableEq E] [Inhabited E]
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E) (lam : Pt) (Δcka tStar qep : ℕ)
    (tL : Option ℕ) (b : Bool)
    (A : SchemeAdversary (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt SS RS M (BitVec 256) E) :
    CryptoGames.CKA.branch (dhSchemeFb Dh) Δcka tStar b
      (redCKAAuthBucket (dhSchemeFb Dh) prng fs lam Δcka qep tL A) =
    CryptoGames.CKA.branch (dhScheme Dh) Δcka tStar b
      (redCKAAuthBucket (dhScheme Dh) prng fs lam Δcka qep tL A) := by
  rw [ckaBranch_dhSchemeFb_eq]
  unfold CryptoGames.CKA.branch redCKAAuthBucket runCKAAuthBucket
  refine bind_congr fun k => ?_
  rw [StateT.run'_eq, StateT.run'_eq]
  refine congrArg (Prod.fst <$> ·) ?_
  let mo₀ : Mode := ⟨true, tL, 0⟩
  have hInit : initCKA (dhSchemeFb Dh) prng fs lam mo₀ = initCKA (dhScheme Dh) prng fs lam mo₀ := rfl
  simp only [simulateQ_bind, StateT.run_bind, bind_assoc]
  rw [hInit]
  let sc := CryptoGames.CKA.initState (dhScheme Dh) k b
  have hsc : CkaStateInv sc := ckaStateInv_init Dh k b
  have hep₀ : ∀ P, sc.epoch P = 0 := fun _ => rfl
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨vs, h⟩, sc₁⟩ hmem => ?_
  have hSyncInit : sc₁ = sc ∧ ∀ vA vB, vs = some (vA, vB) →
      OptCKASync (M := M) (E := Header Pt × E)
        { g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := h } sc := by
    unfold initCKA at hmem
    simp only [StateT.run_bind, StateT.run_lift, simulateQ_bind, bind_assoc, pure_bind] at hmem
    rw [sampleT, simulateQ_ckaFullImpl_liftProb] at hmem
    simp only [bind_assoc, pure_bind, mem_support_bind_iff] at hmem
    obtain ⟨kr, _, hmem⟩ := hmem
    rcases htL : mo₀.tL with _ | tLv
    · simp only [htL, StateT.run_bind, StateT.run_lift, StateT.run_pure,
        simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind] at hmem
      rw [sampleT, simulateQ_ckaFullImpl_liftProb] at hmem
      simp only [bind_assoc, pure_bind, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hmem
      obtain ⟨kc, _, hmem⟩ := hmem
      rcases Prod.mk.inj hmem with ⟨hEq1, hscEq⟩
      rcases Prod.mk.inj hEq1 with ⟨hvs, _⟩
      refine ⟨hscEq, fun vA vB hEq => ?_⟩
      rw [hvs, Option.some.injEq] at hEq; cases hEq
      refine ⟨hsc, fun _ P => ?_⟩
      cases P
      · exact ⟨rfl, ddhRoleOk_initA Dh kc⟩
      · exact ⟨rfl, ddhRoleOk_initB Dh kc⟩
    · simp only [htL, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hmem
      rcases Prod.mk.inj hmem with ⟨hEq1, hscEq⟩
      rcases Prod.mk.inj hEq1 with ⟨hvs, _⟩
      refine ⟨hscEq, fun vA vB hEq => ?_⟩
      rw [hvs, Option.some.injEq] at hEq; cases hEq
      refine ⟨hsc, fun _ P => ?_⟩
      cases P <;> exact ⟨rfl, (hep₀ _).symm⟩
  obtain ⟨hscEq, hSyncInit⟩ := hSyncInit
  rw [hscEq]
  rcases vs with _ | ⟨vA, vB⟩
  · rfl
  · dsimp only
    simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, bind_assoc]
    exact congrArg (· >>= _)
      (simulateQ_implCKABucket_ckaSync_eq Dh prng fs Δcka tStar qep tL A _ none sc
        (hSyncInit vA vB rfl))

theorem ckaBranch_redCKAAuthBucket_atomic_eq
    {Pt KR RSt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [SampleableType KR]
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (B0 B_q Δcka tStar qep : ℕ) (tL : Option ℕ) (b : Bool)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (A : SchemeAdversary (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (ℕ × LibsignalCiphertextWithSalt32))
    (qAdv : ℕ) (hA : CryptoGames.SM.MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q)
    (hSendOk : CryptoGames.LibsignalSM.Proofs.SessionShort.SendMsgsOk
      (fun (m : LibsignalMsgPublicPart × Plain ℓ) => atomicShortPubB m.1) A) :
    CryptoGames.CKA.branch (dhSchemeFb Dh) Δcka tStar b
      (redCKAAuthBucket (dhSchemeFb Dh) prng (fsAtomicB C ℓ encT idOf B0) lam Δcka qep tL A) =
    CryptoGames.CKA.branch (dhScheme Dh) Δcka tStar b
      (redCKAAuthBucket (dhScheme Dh) prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
        lam Δcka qep tL A) := by
  rw [ckaBranch_redCKAAuthBucket_dhSchemeFb_eq Dh prng (fsAtomicB C ℓ encT idOf B0)
      lam Δcka tStar qep tL b A,
    redCKAAuthBucket_fsAtomicB_eq_lFS (dhScheme Dh) prng C ℓ encT idOf lam B0 B_q Δcka qep tL
      hB0 A qAdv hA hqB hSendOk]

end CKABucketAtomicSwap


end

end Computational.Proofs.SessionCostedFig8.BucketCKASwap
