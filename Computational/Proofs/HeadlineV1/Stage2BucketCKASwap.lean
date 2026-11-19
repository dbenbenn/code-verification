/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SessionCostedFig8.DFProgBucketBounds -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperCKA -- proof-setup: allow-public-import
public import Computational.Proofs.HeadlineV1.SendShortC -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperSim
import Computational.Proofs.SessionCostedFig8.DFFsAtomicBSwapPaper
import Computational.Proofs.CryptoGames.CKA.DHProof
import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperBucketFS
import Computational.Proofs.ReductionDsl.SM.DeliverForgeBucketSimEval
import Computational.Proofs.SessionCostedFig8.BucketCKAEval
import Computational.Proofs.SessionCostedFig8.BucketCKASwap
import Computational.Proofs.Fig8SchemeBridge
import Computational.Proofs.SessionCostedFig8.BundlesEval

set_option autoImplicit false

open scoped BigOperators ENNReal
open OracleSpec OracleComp
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open Computational.Proofs.ReductionDsl.Fig8Atomic (dhSchemeFb aeadAtomic atomicShortPubB
  fsAtomicB fsAtomicB_send_eq fsAtomicB_receive_eq RSReachB)
open Computational.Proofs.ReductionDsl.PureAuxMacroLift (CoinSimEquiv ckaAdvantage_congr prngAdvantage_congr)

open scoped MeasureTheory
open Computational.Proofs.SessionCostedFig8.Bundles (fig8CkaOpsShallow)
open Computational.Proofs.SessionCostedFig8.BundlesEval (compileCkaDFAtomic_coinSimEquiv fsAtomicB_receive_rsReach hooksCKA_vrInv_fsAtomicB)
open Computational.Proofs.SessionCostedFig8.FsAtomicBSwap (HooksLocalFsAgree hooksCKA_vrInv_lFS vRecv_localFs_eq vSend_localFs_eq)
open CryptoGames (CKAScheme FSAEADScheme PRFPRNG Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun ckaIface ckaOps ckaSchemeOps dhScheme)
open CryptoGames.FSAEAD (RatchetReceiverState RatchetSenderState)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey maxForwardJumps)
open CryptoGames.Ratchet (rootPRNG)
open CryptoGames.Ratchet.LibsignalInst (LibsignalCiphertextWithSalt32 LibsignalMsgPublicPart lAead lChainPRG lFS lPubOf)
open CryptoGames.Ratchet.LibsignalSim (Fig8C Fig8St)
open CryptoGames.SM (Config Record ite_eval letE_eval pair_eval senderOfE_eval validGuessE_eval)
open CryptoGames.SM.Construction (CKAState Header Mode PartyState bucketParPaperAuthCfgEC ckaBucketEsTy ckaCommitC_eval ckaEsTy ckaFsRecvC ckaFsSendC ckaHsEnc ckaHsTy ckaRevealC_eval ckaStartRecvBucketParPaperAnsE ckaStartSendC_eval ckaVpEnc hooksCKA hooksCKABucketParPaperC hooksCKA_startRecv_rs inStage2BucketGen initCKA initCKAEStateC_eval initCKARaw initCKARaw_inv initCKARaw_vrInv redCKAAuthDFPaperBucketProg redCKAAuthDFPaperBucketProgGen sampleT validGuessBucketParPaperE)
open CryptoGames.SM.Engine (ConfigECAgrees Ctx EState Hooks HooksCAgrees HooksVRInv RSReach SMEngineInv SMVRInv TComp VP abortE authOut cAuthOKE_eval cGsTy cGsWin coinsE commitE corrEPaperBucket_eq_corrEPaper deliverE esAbort esEnc esG eval_bind eval_bind_ret eval_caseOpt eval_ret implEDFPaperBucketRaw_inv implEDFPaperBucketRaw_vrInv injectE optNatLit run_liftH_bind simulateQ_implEDFPaperBucket_vr_eq vRecv vSend vpTblEnc vpTblTy)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSession.Fig8SchemeBridge (CkaStateInv OptCKASync OptPartySync badSendMsg_transmit_false ckaBranch_dhSchemeFb_eq ckaFullImpl ckaStateInv_init commitE_ckaSync ddhRoleOk_initA ddhRoleOk_initB liftC_corrQuery_support optPartySync_of_epoch_eq record_st_eq simulateQ_ckaFullImpl_liftProb vRecv_hooksCKA_pure_eq vSend_ckaSync_eq)
open CryptoVerification.LibsignalSession.HeadlineV1 (SendMsgsOkDF badSendMsgDF)
open ReductionDsl (CostedReduction Env Expr Ops Sig Ty handlerImpl)

namespace Computational.Proofs.HeadlineV1.Stage2BucketCKASwap

public section
local instance {Pt : Type} [Zero Pt] : Inhabited Pt := ⟨0⟩
private abbrev vpEncCKA {KC Γ CCoins T I KR RSt K SS RS M E : Type} :=
  vpTblEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I) (KR := KR) (RSt := RSt)
    (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
    (γvT := .opt (.base .γ)) (svT := .base .sig) (ssvT := .base .ss) (rsvT := .base .rs)
private theorem startRecv_hooksCKABucket_df_eq {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [SampleableType CCoins] (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (tL : Option ℕ) (par : Bool)
    (ctx : Ctx (Option Γ) T Sig SS RS M E) (P : Party) (t0 : ℕ) (γ0 : Option Γ) (σ0 : Sig) (tn0 : T) :
    (CryptoGames.SM.Construction.DeliverForge.hooksCKABucket cka prng fs Δcka tL par).startRecv ctx P t0 γ0 σ0 tn0 =
      (hooksCKA cka prng fs Δcka
        ⟨true, tL, if CryptoGames.SM.Construction.DeliverForge.inStage2Bucket Δcka tL par t0 then t0 else t0 + 1⟩).startRecv
        ctx P t0 γ0 σ0 tn0 := by
  ext h; simp only [CryptoGames.SM.Construction.DeliverForge.hooksCKABucket, hooksCKA, StateT.run_bind, StateT.run_get, pure_bind]
  cases h.cache t0 with
  | none => cases hb : CryptoGames.SM.Construction.DeliverForge.inStage2Bucket Δcka tL par t0 <;> (simp; try rfl)
  | some pair =>
    rcases pair with ⟨Tc, Ik⟩
    by_cases hTc : Tc = tn0
    · simp [hTc]
    · cases hb : CryptoGames.SM.Construction.DeliverForge.inStage2Bucket Δcka tL par t0 <;> (simp [hTc]; try rfl)
private theorem hooksCKABucket_df_vrInv_fsAtomicB {Pt : Type} [DecidableEq Pt] [Zero Pt]
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (C : Crypto) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (B0 Δcka : ℕ) (tL : Option ℕ) (par : Bool) :
    HooksVRInv (CryptoGames.SM.Engine.RSReach maxForwardJumps)
      (CryptoGames.SM.Construction.DeliverForge.hooksCKABucket (dhSchemeFb Dh) (rootPRNG C.F encPt)
        (fsAtomicB C ℓ encT idOf B0) Δcka tL par) where
  mono hle hv := hv.mono hle
  startRecv_step ctx P t0 γ0 σ0 tn0 h res hmem γ' σ' rs hEq := by
    rw [startRecv_hooksCKABucket_df_eq] at hmem
    exact (hooksCKA_vrInv_fsAtomicB Dh encPt C ℓ encT idOf B0 Δcka
      ⟨true, tL, if CryptoGames.SM.Construction.DeliverForge.inStage2Bucket Δcka tL par t0 then t0 else t0 + 1⟩).startRecv_step
      ctx P t0 γ0 σ0 tn0 h res hmem γ' σ' rs hEq
  fsRecv_step ctx P t0 rs hdr e n h res hVR hmem v' i' m' hEq :=
    (hooksCKA_vrInv_fsAtomicB Dh encPt C ℓ encT idOf B0 Δcka ⟨true, tL, 0⟩).fsRecv_step
      ctx P t0 rs hdr e n h res hVR hmem v' i' m' hEq
  commit_vR ctx P t0 new h res hmem new' hEq :=
    (hooksCKA_vrInv_fsAtomicB Dh encPt C ℓ encT idOf B0 Δcka ⟨true, tL, 0⟩).commit_vR
      ctx P t0 new h res hmem new' hEq
private theorem hooksCKABucket_df_vrInv_lFS {Pt KC Γ CCoins I KR RSt : Type} [DecidableEq Pt] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256)) (C : Crypto) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (Δcka : ℕ) (tL : Option ℕ) (par : Bool) :
    HooksVRInv (RSReachB maxForwardJumps)
      (CryptoGames.SM.Construction.DeliverForge.hooksCKABucket cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka tL par) where
  mono hle hv := hv.mono hle
  startRecv_step ctx P t0 γ0 σ0 tn0 h res hmem γ' σ' rs hEq := by
    rw [startRecv_hooksCKABucket_df_eq] at hmem
    exact (hooksCKA_vrInv_lFS cka prng C ℓ encT idOf Δcka
      ⟨true, tL, if CryptoGames.SM.Construction.DeliverForge.inStage2Bucket Δcka tL par t0 then t0 else t0 + 1⟩).startRecv_step
      ctx P t0 γ0 σ0 tn0 h res hmem γ' σ' rs hEq
  fsRecv_step ctx P t0 rs hdr e n h res hVR hmem v' i' m' hEq :=
    (hooksCKA_vrInv_lFS cka prng C ℓ encT idOf Δcka ⟨true, tL, 0⟩).fsRecv_step
      ctx P t0 rs hdr e n h res hVR hmem v' i' m' hEq
  commit_vR ctx P t0 new h res hmem new' hEq :=
    (hooksCKA_vrInv_lFS cka prng C ℓ encT idOf Δcka ⟨true, tL, 0⟩).commit_vR
      ctx P t0 new h res hmem new' hEq
private theorem hooksCKABucket_df_localFsAgree {Pt KC Γ CCoins I KR RSt : Type} [DecidableEq Pt] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256)) (C : Crypto) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (B0 Δcka : ℕ) (tL : Option ℕ) (par : Bool) :
    HooksLocalFsAgree ℓ B0 (CryptoGames.SM.Construction.DeliverForge.hooksCKABucket cka prng (fsAtomicB C ℓ encT idOf B0) Δcka tL par)
      (CryptoGames.SM.Construction.DeliverForge.hooksCKABucket cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka tL par) where
  startSend_eq := by unfold CryptoGames.SM.Construction.DeliverForge.hooksCKABucket hooksCKA fsAtomicB lFS CryptoGames.FSAEAD.fromAEADPRG; rfl
  startRecv_eq := by unfold CryptoGames.SM.Construction.DeliverForge.hooksCKABucket fsAtomicB lFS CryptoGames.FSAEAD.fromAEADPRG; rfl
  fsSend_eq _ _ _ ss hdr m _ hm := by
    dsimp only [CryptoGames.SM.Construction.DeliverForge.hooksCKABucket, hooksCKA]; rw [fsAtomicB_send_eq C ℓ encT idOf B0 ss hdr m hm]
  fsRecv_eq _ _ _ rs hdr e _ hlen := by
    dsimp only [CryptoGames.SM.Construction.DeliverForge.hooksCKABucket, hooksCKA]; rw [fsAtomicB_receive_eq C ℓ encT idOf B0 rs hdr e hlen]
  commit_eq := by unfold CryptoGames.SM.Construction.DeliverForge.hooksCKABucket hooksCKA; rfl
  reveal_eq := by unfold CryptoGames.SM.Construction.DeliverForge.hooksCKABucket hooksCKA; rfl
private lemma badSendMsgDF_query_bind_step' {St Msg Coins C α : Type} (Pmsg : Msg → Bool)
    (qy : (unifSpec + CryptoGames.SM.specDF St Msg Coins C).Domain)
    (mx : (unifSpec + CryptoGames.SM.specDF St Msg Coins C).Range qy → CryptoGames.SM.Construction.DeliverForge.AdversaryCompDF St Msg Coins C α)
    (h : IsQueryBoundP ((liftM (OracleSpec.query qy) : OracleComp (unifSpec + CryptoGames.SM.specDF St Msg Coins C) _) >>= mx)
      (fun t => badSendMsgDF (St := St) (Coins := Coins) (C := C) Pmsg t = true) 0) :
    badSendMsgDF (St := St) (Coins := Coins) (C := C) Pmsg qy = false ∧
      ∀ u, IsQueryBoundP (mx u) (fun t => badSendMsgDF (St := St) (Coins := Coins) (C := C) Pmsg t = true) 0 := by
  rw [isQueryBoundP_query_bind_iff] at h; rcases h with ⟨hq0, hmx⟩
  have hbf : badSendMsgDF (St := St) (Coins := Coins) (C := C) Pmsg qy = false :=
    Bool.eq_false_iff.mpr (hq0.resolve_right (by omega))
  refine ⟨hbf, fun u => ?_⟩
  have hu := hmx u; simp only [hbf, Bool.false_eq_true, ↓reduceIte] at hu; exact hu
private lemma badSendMsgDF_inl_to_badSendMsg' {St Msg Coins C : Type} (Pmsg : Msg → Bool)
    (t5 : (CryptoGames.SM.spec St Msg Coins C).Domain)
    (h : badSendMsgDF (St := St) (Coins := Coins) (C := C) Pmsg (.inr (.inl t5)) = false) :
    CryptoGames.LibsignalSM.Proofs.SessionShort.badSendMsg (St := St) (Coins := Coins) (C := C) Pmsg (.inr t5) = false := by
  rcases t5 with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P <;> exact h
private theorem implEDFPaperBucketRaw_localFs_eq {Pt ι : Type} [DecidableEq Pt] {TSpec : OracleSpec.{0, 0} ι}
    {HS Γ RSt CCoins γV σV : Type} {ℓ B0 B_q q' Δ qep : ℕ} {cfg : Config (LibsignalMsgPublicPart × Plain ℓ)}
    {hk₁ hk₂ : Hooks TSpec HS Γ Pt RSt (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32) CCoins γV σV
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))}
    (hAg : HooksLocalFsAgree ℓ B0 hk₁ hk₂) (hVRHk : HooksVRInv (RSReachB maxForwardJumps) hk₂)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (es : EState (VP γV Pt σV (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256)))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)) HS)
    (t_sm : (CryptoGames.SM.Construction.DeliverForge.specDF (PartyState Γ Pt RSt (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)))
      (LibsignalMsgPublicPart × Plain ℓ) CCoins (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))).Domain)
    (hBad : badSendMsgDF (St := PartyState Γ Pt RSt (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256))) (Coins := CCoins)
      (C := Header Pt × (ℕ × LibsignalCiphertextWithSalt32)) (fun m => atomicShortPubB m.1) (.inr t_sm) = false)
    (hVR : SMVRInv (RSReachB maxForwardJumps) B_q (q' + 1) es.g) :
    (CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketRaw hk₁ Δ qep maxForwardJumps cfg (.inr t_sm)).run es =
      (CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketRaw hk₂ Δ qep maxForwardJumps cfg (.inr t_sm)).run es := by
  have hkB : (B_q - (q' + 1) + 1) * (maxForwardJumps + 1) ≤ B0 :=
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.sub_le _ _) 1)).trans hB0
  rcases t_sm with t5 | ⟨P, c, c'⟩
  · have hBad5 := badSendMsgDF_inl_to_badSendMsg' (fun m => atomicShortPubB m.1) t5 hBad
    rcases t5 with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
    · change (CryptoGames.SM.Construction.DeliverForge.transmitEBucket hk₁ Δ qep (P, m, r)).run es =
        (CryptoGames.SM.Construction.DeliverForge.transmitEBucket hk₂ Δ qep (P, m, r)).run es
      unfold CryptoGames.SM.Construction.DeliverForge.transmitEBucket
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      by_cases hab : (es.abort || es.g.win) = true
      · simp [hab]
      · simp only [hab, Bool.false_eq_true, ↓reduceIte]
        rcases es.g.epMgmt Δ qep P r.isSome with _ | s₁
        · rfl
        · have hm : atomicShortPubB m.1 = true :=
            badSendMsg_transmit_false
              (ok := fun (x : LibsignalMsgPublicPart × Plain ℓ) => atomicShortPubB x.1) hBad5
          simp only [run_liftH_bind]
          exact congrArg (· >>= _) (vSend_localFs_eq hAg s₁ P (s₁.st P) m none r hm es.h)
    · rfl
    · change (deliverE hk₁ maxForwardJumps cfg (P, c)).run es =
        (deliverE hk₂ maxForwardJumps cfg (P, c)).run es
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
    · change (injectE hk₁ Δ qep cfg (P, c)).run es =
        (injectE hk₂ Δ qep cfg (P, c)).run es
      have hCommit : commitE hk₁ = commitE hk₂ := by unfold commitE; rw [hAg.commit_eq]
      unfold injectE
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      by_cases href :
          (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj Δ)) = true
      · simp [href]
      · simp only [href, Bool.false_eq_true, ↓reduceIte, run_liftH_bind,
          vRecv_localFs_eq hAg hVRHk hkB es.g P (es.g.st P) c none es.h (hVR P), hCommit]
    · change (CryptoGames.SM.Construction.DeliverForge.corrEPaperBucket hk₁ P).run es =
        (CryptoGames.SM.Construction.DeliverForge.corrEPaperBucket hk₂ P).run es
      rw [corrEPaperBucket_eq_corrEPaper, corrEPaperBucket_eq_corrEPaper]
      unfold CryptoGames.SM.Construction.DeliverForge.corrEPaper; rw [hAg.reveal_eq]
  · change (CryptoGames.SM.Construction.DeliverForge.deliverForgeE hk₁ Δ qep cfg (P, c, c')).run es =
      (CryptoGames.SM.Construction.DeliverForge.deliverForgeE hk₂ Δ qep cfg (P, c, c')).run es
    have hCommit : commitE hk₁ = commitE hk₂ := by unfold commitE; rw [hAg.commit_eq]
    unfold CryptoGames.SM.Construction.DeliverForge.deliverForgeE; simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win) = true
    · simp [hab]
    · simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases es.g.inTransit P.other c with _ | r
      · rfl
      · dsimp only; split_ifs
        · rfl
        · simp only [run_liftH_bind,
            vRecv_localFs_eq hAg hVRHk hkB es.g P (es.g.st P) c' none es.h (hVR P), hCommit]
private theorem simulateQ_implEDFPaperBucket_localFs_eq {Pt ι : Type} [DecidableEq Pt] {TSpec : OracleSpec.{0, 0} ι}
    {HS Γ RSt CCoins γV σV α : Type} {ℓ L B0 B_q q Δ qep : ℕ}
    {cfg : Config (LibsignalMsgPublicPart × Plain ℓ)}
    {hk₁ hk₂ : Hooks TSpec HS Γ Pt RSt (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32) CCoins γV σV
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))}
    (hAg : HooksLocalFsAgree ℓ B0 hk₁ hk₂) (hVRHk : HooksVRInv (RSReachB maxForwardJumps) hk₂)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    {oa : CryptoGames.SM.Construction.DeliverForge.AdversaryCompDF (PartyState Γ Pt RSt (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)))
      (LibsignalMsgPublicPart × Plain ℓ) CCoins (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)) α}
    (hoa : oa.IsQueryBoundP (ReductionDsl.isGameQuery (G := CryptoGames.SM.Construction.DeliverForge.specDF
      (PartyState Γ Pt RSt (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256)))
      (LibsignalMsgPublicPart × Plain ℓ) CCoins (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)))) q)
    (hSendOk : IsQueryBoundP oa (fun t => badSendMsgDF
      (St := PartyState Γ Pt RSt (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256)))
      (Coins := CCoins) (C := Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (fun m => atomicShortPubB m.1) t = true) 0)
    (es : EState (VP γV Pt σV (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)))
      (LibsignalMsgPublicPart × Plain ℓ) (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)) HS)
    (winEp : Option ℕ)
    (hInv : SMEngineInv L B_q q es.g) (hVR : SMVRInv (RSReachB maxForwardJumps) B_q q es.g) :
    (simulateQ (CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucket hk₁ Δ qep maxForwardJumps cfg) oa).run (es, winEp) =
      (simulateQ (CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucket hk₂ Δ qep maxForwardJumps cfg) oa).run (es, winEp) := by
  have hLift : ∀ {M' : Type → Type} [Monad M'] {σ' α' : Type} (m : StateT σ' M' α') (s : σ'),
      (liftM m : StateT σ' M' α').run s = m.run s := fun _ _ => rfl
  induction oa using OracleComp.inductionOn generalizing q es winEp with
  | pure _ => rfl
  | query_bind qy mx ih =>
    obtain ⟨hBadQ, hBadMx⟩ := badSendMsgDF_query_bind_step' (fun m => atomicShortPubB m.1) qy mx hSendOk
    rw [isQueryBoundP_query_bind_iff] at hoa
    rw [simulateQ_query_bind, simulateQ_query_bind, StateT.run_bind, StateT.run_bind, hLift, hLift]
    simp only [OracleQuery.input_query, OracleQuery.cont_query]
    unfold CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucket CryptoGames.SM.Construction.DeliverForge.withWinEpDF
    dsimp only [StateT.run_mk]
    simp only [bind_assoc]
    rcases qy with n | t_sm
    · have hq0 : ¬ ReductionDsl.isGameQuery (G := CryptoGames.SM.Construction.DeliverForge.specDF
          (PartyState Γ Pt RSt (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256)))
          (LibsignalMsgPublicPart × Plain ℓ) CCoins (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))) (Sum.inl n) := by
        simp [ReductionDsl.isGameQuery]
      have hmx : ∀ u, (mx u).IsQueryBoundP _ q := fun u => by
        have hu := hoa.2 u; simp only [hq0, ↓reduceIte] at hu; exact hu
      have hInl₁ : (CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketRaw hk₁ Δ qep maxForwardJumps cfg (.inl n)).run es =
          (coinsE n).run es := rfl
      have hInl₂ : (CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketRaw hk₂ Δ qep maxForwardJumps cfg (.inl n)).run es =
          (coinsE n).run es := rfl
      rw [hInl₁, hInl₂]; simp only [coinsE, StateT.run_lift, bind_assoc, pure_bind]
      exact bind_congr fun u => ih u (hmx u) (hBadMx u) es _ hInv hVR
    · have hq1 : ReductionDsl.isGameQuery (G := CryptoGames.SM.Construction.DeliverForge.specDF
          (PartyState Γ Pt RSt (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256)))
          (LibsignalMsgPublicPart × Plain ℓ) CCoins (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))) (Sum.inr t_sm) := by
        simp [ReductionDsl.isGameQuery]
      rcases q with _ | q'
      · exact absurd (hoa.1.resolve_left (not_not.mpr hq1)) (by omega)
      have hmx : ∀ u, (mx u).IsQueryBoundP _ q' := fun u => by
        have hu := hoa.2 u; simp only [hq1, ↓reduceIte] at hu; exact hu
      rw [implEDFPaperBucketRaw_localFs_eq hAg hVRHk hB0 es t_sm hBadQ hVR]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, es'⟩ hr => ?_
      simp only [pure_bind]
      exact ih u (hmx u) (hBadMx u) es' _
        (implEDFPaperBucketRaw_inv hk₂ cfg es t_sm hInv (u, es') hr)
        (implEDFPaperBucketRaw_vrInv hk₂ hVRHk cfg es t_sm hInv hVR (u, es') hr)
/-! ### Stage-2 Bucket CKA (`hU_cka`) Evaluation & Swap Bridges -/
section Stage2BucketCKA
private theorem hooksCKABucket_df_startRecv_rs {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [SampleableType CCoins] (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (tL : Option ℕ) (par : Bool)
    {VROk : RS → Prop} (hInitR : ∀ k, VROk (fs.initReceiver k))
    (ctx : Ctx (Option Γ) T RSt SS RS M E) (P : Party) (t : ℕ) (γv : Option Γ) (σ : RSt) (Tn : T) (h : CKAState T I) :
    ∀ res ∈ support (((CryptoGames.SM.Construction.DeliverForge.hooksCKABucket cka prng fs Δcka tL par).startRecv ctx P t γv σ Tn).run h),
      ∀ γ' σ' rs, res.1 = some (some (γ', σ', rs)) → VROk rs := by
  intro res hmem γ' σ' rs hEq; rw [startRecv_hooksCKABucket_df_eq] at hmem
  exact hooksCKA_startRecv_rs cka prng fs Δcka _ hInitR ctx P t γv σ Tn h res hmem γ' σ' rs hEq
private lemma caseOpt_eval' {S' : Sig} {O' : Ops S'} {Γ' : List (Ty S')} {a b : Ty S'}
    (e : Expr O' Γ' (.opt a)) (n : Expr O' Γ' b) (s : Expr O' (a :: Γ') b) (ρ : Env Γ') :
    (ReductionDsl.Expr.caseOpt e n s).eval ρ = match e.eval ρ with | none => n.eval ρ | some x => s.eval (.cons x ρ) := rfl
private lemma validGuessBucketParPaperE_eval' {S' : Sig} {O' : Ops S'} (Δbucket : ℕ)
    (tL : Option ℕ) (par : Bool) {Γ'} (tE : Expr O' Γ' .nat) (ρ : Env Γ') :
    (validGuessBucketParPaperE Δbucket tL par tE).eval ρ = inStage2BucketGen Δbucket tL par (tE.eval ρ) := by
  unfold validGuessBucketParPaperE inStage2BucketGen
  have htL : (optNatLit (O' := O') tL).eval ρ = tL := by cases tL <;> rfl
  simp only [ReductionDsl.Expr.eval, validGuessE_eval, senderOfE_eval, htL]
  congr 1; cases par <;> cases CryptoGames.Party.senderOf (tE.eval ρ) <;> rfl
private lemma ckaStartRecvBucketParPaperC_eval {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [SampleableType CCoins] {ckaInitA : KC → Γ} {ckaInitB : KC → Γ}
    {ckaSend : Γ → CCoins → Γ × T × I} {ckaReceive : Γ → T → Γ × I}
    {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K} {fsInitSender : K → SS} {fsInitReceiver : K → RS}
    {fsSend : SS → Header T → M → SS × E} {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
    {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
    {lam : I} {defaultE : E} {sampKR : ProbComp KR} {sampKC : ProbComp KC}
    {sampCCoins : ProbComp CCoins} {sampI : ProbComp I} {sampK : ProbComp K}
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (hRecv : ckaReceive = cka.receive) (hPrngUp : prngUp = prng.up)
    (hFsInitR : fsInitReceiver = fs.initReceiver) (heqT : eqT = (· == ·))
    (B Δcka : ℕ) (tL : Option ℕ) (par : Bool) {Γ'}
    (hE : Expr (ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp fsInitSender
      fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE) Γ'
      (@ckaHsTy KC Γ CCoins T I KR RSt K SS RS M E))
    (ctxE : Expr (ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp fsInitSender
      fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE) Γ'
      (cGsTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E
        (.opt (.base CryptoGames.CKA.CKASort.γ)) (.base .sig) (.base .ss) (.base .rs))))
    (pE : Expr (ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp fsInitSender
      fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE) Γ' .bool)
    (tE : Expr (ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp fsInitSender
      fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE) Γ' .nat)
    (γvE : Expr (ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp fsInitSender
      fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE) Γ' (.opt (.base .γ)))
    (σE : Expr (ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp fsInitSender
      fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE) Γ' (.base .sig))
    (tnE : Expr (ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp fsInitSender
      fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE) Γ' (.base .t))
    (ρ : Env Γ') (h : CKAState T I) (ctx : Ctx (Option Γ) T RSt SS RS M E) (P : Party)
    (hh : hE.eval ρ = ckaHsEnc h) :
    ((hooksCKABucketParPaperC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B Δcka (3 + Δcka) tL par).startRecv
        hE ctxE pE tE γvE σE tnE).eval ρ =
      Prod.map id ckaHsEnc <$>
        ((CryptoGames.SM.Construction.DeliverForge.hooksCKABucket cka prng fs Δcka tL par).startRecv ctx P
          (tE.eval ρ) (γvE.eval ρ) (σE.eval ρ) (tnE.eval ρ)).run h := by
  let OO := ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp fsInitSender
    fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE
  dsimp only [hooksCKABucketParPaperC, ckaStartRecvBucketParPaperAnsE, CryptoGames.SM.Construction.DeliverForge.hooksCKABucket]
  simp only [eval_ret, pair_eval, letE_eval, hh, StateT.run_bind, StateT.run_get, pure_bind]
  set t : ℕ := tE.eval ρ
  set γv : Option Γ := γvE.eval ρ
  set σ : RSt := σE.eval ρ
  set Tn : T := tnE.eval ρ
  set ρ₁ := ReductionDsl.Env.cons
    (t := .prod (@ckaHsTy KC Γ CCoins T I KR RSt K SS RS M E)
      (.prod .nat (.prod (.opt (.base CryptoGames.CKA.CKASort.γ))
        (.prod (.base CryptoGames.CKA.CKASort.sig) (.base CryptoGames.CKA.CKASort.t)))))
    (ckaHsEnc h, t, γv, σ, Tn) ρ
  change (pure ((ReductionDsl.Expr.caseOpt _ _ _).eval ρ₁, ckaHsEnc h) :
      TComp (CryptoGames.CKA.spec Γ CCoins T I) _) = _
  have hHonest :
      (ReductionDsl.Expr.caseOpt (.tget (.fst (ReductionDsl.Expr.v0 (O := OO))) (.fst (.snd .v0))) .none
        (.ite (ReductionDsl.Expr.op (O := OO) CryptoGames.CKA.CKAOp.eqT (.pair (.fst .v0) (.snd (.snd (.snd (.snd .v1))))))
          (.some (.snd .v0)) .none)).eval ρ₁ =
      (match h.cache t with
        | some (Tc, Ik) => if Tc = Tn then some Ik else none
        | none => none) := by
    have hGet : (ReductionDsl.Expr.tget (.fst (ReductionDsl.Expr.v0 (O := OO))) (.fst (.snd .v0))).eval ρ₁ = h.cache t := rfl
    rw [caseOpt_eval', hGet]
    rcases h.cache t with _ | ⟨Tc, Ik⟩
    · rfl
    · simp only [ρ₁, OO, ckaOps, heqT, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, BEq.beq]
      by_cases hEq : Tc = Tn <;> simp [hEq]
  rw [caseOpt_eval', hHonest]
  have hCond :
      (validGuessBucketParPaperE (O' := OO) (3 + Δcka) tL par
        (.fst (.snd (ReductionDsl.Expr.v0 (O := OO))))).eval ρ₁ =
      CryptoGames.SM.Construction.DeliverForge.inStage2Bucket Δcka tL par t := by
    have hEq := validGuessBucketParPaperE_eval' (O' := OO) (3 + Δcka) tL par
      (.fst (.snd (ReductionDsl.Expr.v0 (O := OO)))) ρ₁
    have ht₁ : (ReductionDsl.Expr.fst (.snd (ReductionDsl.Expr.v0 (O := OO)))).eval ρ₁ = t := rfl
    rw [ht₁] at hEq
    simpa [CryptoGames.SM.Construction.DeliverForge.inStage2Bucket, inStage2BucketGen] using hEq
  rcases h.cache t with _ | ⟨Tc, Ik⟩
  · dsimp only
    rw [ite_eval, hCond]
    by_cases hAdm : CryptoGames.SM.Construction.DeliverForge.inStage2Bucket Δcka tL par t = true
    · simp only [hAdm, ↓reduceIte]
      rcases γv with _ | γ
      · simp only [StateT.run_pure, map_pure]; rfl
      · simp only [StateT.run_pure, map_pure, Prod.map, id_eq]
        congr 1; congr 1
        simp [ρ₁, ckaOps, hRecv, hPrngUp, hFsInitR, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1]
    · simp only [hAdm, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, map_pure]; rfl
  · dsimp only
    by_cases hEq : Tc = Tn
    · simp only [hEq, ↓reduceIte]
      rcases γv with _ | γ <;>
      · simp only [StateT.run_pure, map_pure, Prod.map, id_eq]
        congr 1; congr 1
        simp [ρ₁, ckaOps, hRecv, hPrngUp, hFsInitR, ReductionDsl.Expr.eval,
          ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, ReductionDsl.Expr.v2]
    · simp only [hEq, ↓reduceIte]
      rw [ite_eval, hCond]
      by_cases hAdm : CryptoGames.SM.Construction.DeliverForge.inStage2Bucket Δcka tL par t = true
      · simp only [hAdm, ↓reduceIte]
        rcases γv with _ | γ
        · simp only [StateT.run_pure, map_pure]; rfl
        · simp only [StateT.run_pure, map_pure, Prod.map, id_eq]
          congr 1; congr 1
          simp [ρ₁, ckaOps, hRecv, hPrngUp, hFsInitR, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1]
      · simp only [hAdm, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, map_pure]; rfl
private lemma hooksCKABucketParPaperC_agrees_vr
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [SampleableType CCoins]
    {ckaInitA : KC → Γ} {ckaInitB : KC → Γ}
    {ckaSend : Γ → CCoins → Γ × T × I} {ckaReceive : Γ → T → Γ × I}
    {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
    {fsInitSender : K → SS} {fsInitReceiver : K → RS}
    {fsSend : SS → Header T → M → SS × E} {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
    {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
    {lam : I} {defaultE : E}
    {sampKR : ProbComp KR} {sampKC : ProbComp KC} {sampCCoins : ProbComp CCoins}
    {sampI : ProbComp I} {sampK : ProbComp K}
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (B Δcka : ℕ) (tL : Option ℕ) (par : Bool) {VROk : RS → Prop}
    (hSend : ckaSend = cka.send) (hRecv : ckaReceive = cka.receive)
    (hPrngUp : prngUp = prng.up) (hFsInitS : fsInitSender = fs.initSender)
    (hFsInitR : fsInitReceiver = fs.initReceiver) (hFsSend : fsSend = fs.send)
    (hFsRecv : fsReceive = fs.receive) (heqT : eqT = (· == ·))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hInitR : ∀ k, VROk (fs.initReceiver k))
    (hFsB : ∀ rs hdr e rs' i m, VROk rs → fs.receive rs hdr e = some (rs', i, m) → i ≤ B) :
    HooksCAgrees (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      ckaHsEnc (fun _ => True) (HBoundedPost := fun _ => True) (VROk := VROk)
      (hooksCKABucketParPaperC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B Δcka (3 + Δcka) tL par)
      (CryptoGames.SM.Construction.DeliverForge.hooksCKABucket cka prng fs Δcka tL par) where
  hBounded_post _ _ := trivial
  startSend_eval hE ctxE pE tE γE σE rE ρ h ctx P _ hh _ hp :=
    ckaStartSendC_eval cka prng fs hSend hPrngUp hFsInitS hSampCCoins Δcka ⟨true, tL, 0⟩
      hE ctxE pE tE γE σE rE ρ h ctx P hh hp
  startSend_bounded _ _ _ _ _ _ _ _ _ _ := trivial
  startRecv_eval hE ctxE pE tE γvE σE tnE ρ h ctx P _ hh _ _ :=
    ckaStartRecvBucketParPaperC_eval cka prng fs hRecv hPrngUp hFsInitR heqT B Δcka tL par
      hE ctxE pE tE γvE σE tnE ρ h ctx P hh
  startRecv_bounded _ _ _ _ _ _ _ _ _ _ := trivial
  startRecv_vrOk ctx P t γ σ Tn h _ :=
    hooksCKABucket_df_startRecv_rs cka prng fs Δcka tL par hInitR ctx P t γ σ Tn h
  fsSend_eval hE _ _ _ ssE hdrE mE _ ρ h _ _ _ hh _ _ := by
    simp [hooksCKABucketParPaperC, ckaFsSendC, CryptoGames.SM.Construction.DeliverForge.hooksCKABucket, hooksCKA, ckaOps,
      hFsSend, hh, StateT.run_pure, Prod.map, ReductionDsl.Expr.eval]
  fsRecv_eval hE _ _ _ rsE hdrE eE _ ρ h _ _ _ _ hVR hh _ _ _ := by
    simp only [hooksCKABucketParPaperC, ckaFsRecvC, CryptoGames.SM.Construction.DeliverForge.hooksCKABucket, hooksCKA, eval_ret,
      ckaOps, hFsRecv, hh, StateT.run_pure, map_pure, Prod.map, id_eq, ReductionDsl.Expr.eval]
    congr 2
    rcases hrc : fs.receive (rsE.eval ρ) (hdrE.eval ρ) (eE.eval ρ) with _ | ⟨rs', i, m⟩
    · rfl
    · simp [Nat.min_eq_left (hFsB _ _ _ _ _ _ hVR hrc)]
  fsRecv_bounded _ _ _ _ _ _ _ _ _ _ _ := trivial
  commit_eval hE ctxE pE oldE newE ρ h ctx P old new _ hh _ hp hold hnew :=
    ckaCommitC_eval cka prng fs Δcka ⟨true, tL, 0⟩ hE ctxE pE oldE newE ρ h ctx P old new hh hp hold hnew
  reveal_eval hE ctxE pE vpE ρ h ctx P vp _ hh _ hp hvp :=
    ckaRevealC_eval cka prng fs Δcka ⟨true, tL, 0⟩ hE ctxE pE vpE ρ h ctx P vp hh hp hvp
private lemma runCKADFPaperBucket_eq_bind_initCKARaw
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (A : CryptoGames.SM.Construction.DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) :
    CryptoGames.SM.Construction.DeliverForge.redCKAAuthDFPaperBucket cka prng fs lam Δcka qep tL par A =
      (do
        let es₀ ← (initCKARaw cka prng fs lam ⟨true, tL, 0⟩ false :
          OracleComp (unifSpec + CryptoGames.CKA.spec Γ CCoins T I) _)
        let (_, st) ←
          (simulateQ (CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucket
            (CryptoGames.SM.Construction.DeliverForge.hooksCKABucket cka prng fs Δcka tL par)
            (2 + Δcka) qep fs.maxSkip (CryptoGames.SM.Construction.DeliverForge.bucketAuthCfg Δcka tL par)) A).run (es₀, none)
        return CryptoGames.SM.Construction.DeliverForge.authOutBucketPaper (2 + Δcka) tL st :
          OracleComp (unifSpec + CryptoGames.CKA.spec Γ CCoins T I) Bool) := by
  unfold CryptoGames.SM.Construction.DeliverForge.redCKAAuthDFPaperBucket CryptoGames.SM.Construction.DeliverForge.engRunDFPaperBucket initCKARaw initCKA
  cases tL <;>
    simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind,
      map_eq_bind_pure_comp, Function.comp_def] <;>
    rfl
private theorem redCKAAuthDFPaperBucketProg_eval_atomic
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep q : ℕ) (tL : Option ℕ) (par : Bool)
    (A : CryptoGames.SM.Construction.DeliverForge.SchemeAdversaryDF (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (ℕ × LibsignalCiphertextWithSalt32))
    (hqA : CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF A q) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    (redCKAAuthDFPaperBucketProg (q + 1) B0 1 qep maxForwardJumps tL par :
      CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
        (ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
          (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
        _ _ .unit .unit .bool .bool).eval (fun _ => A) () =
      CryptoGames.SM.Construction.DeliverForge.redCKAAuthDFPaperBucket (dhSchemeFb Dh) (rootPRNG C.F encPt)
        (fsAtomicB C ℓ encT idOf B0) lam 1 qep tL par A := by
  intro B0
  let cka := dhSchemeFb Dh
  let prng := rootPRNG C.F encPt
  let fs := fsAtomicB C ℓ encT idOf B0
  let eqM0 : (LibsignalMsgPublicPart × Plain ℓ) → (LibsignalMsgPublicPart × Plain ℓ) → Bool :=
    @BEq.beq _ instBEqOfDecidableEq
  let eqE0 : (ℕ × LibsignalCiphertextWithSalt32) → (ℕ × LibsignalCiphertextWithSalt32) → Bool :=
    @BEq.beq _ instBEqOfDecidableEq
  have hA' : A.IsQueryBoundP (ReductionDsl.isGameQuery (G := CryptoGames.SM.Construction.DeliverForge.specDF
      (PartyState (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256)))
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
      (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)))) q := by
    refine hqA.of_imp fun x hx => ?_; rcases x with _ | _ <;> simp_all [ReductionDsl.isGameQuery]
  have hVRHk := hooksCKABucket_df_vrInv_fsAtomicB Dh encPt C ℓ encT idOf B0 1 tL par
  have hInitR : ∀ k, RSReach maxForwardJumps 0 (fs.initReceiver k) :=
    CryptoGames.SM.Engine.RSReach.init ((aeadAtomic C ℓ encT idOf).movePubPartToAD
      (lPubOf protoSignalCodec)) (lChainPRG C.F) maxForwardJumps
  have hHk := hooksCKABucketParPaperC_agrees_vr
    (ckaInitA := cka.initA) (ckaInitB := cka.initB) (ckaSend := cka.send) (ckaReceive := cka.receive)
    (prngInit := prng.init) (prngUp := prng.up) (fsInitSender := fs.initSender)
    (fsInitReceiver := fs.initReceiver) (fsSend := fs.send) (fsReceive := fs.receive)
    (eqT := (· == ·)) (eqI := (· == ·)) (eqM := eqM0) (eqE := eqE0)
    (lam := lam) (defaultE := (0, default))
    (sampKR := ($ᵗ (BitVec 256))) (sampKC := ($ᵗ (BitVec 256)))
    (sampCCoins := ($ᵗ (BitVec 256))) (sampI := ($ᵗ Pt)) (sampK := ($ᵗ (BitVec 256)))
    cka prng fs B0 1 tL par rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun k => hVRHk.mono (Nat.zero_le q) (hInitR k))
    (fun _ _ _ _ _ _ hVR hrec => (fsAtomicB_receive_rsReach C ℓ encT idOf B0 q hVR hrec).1)
  have hCfg : ConfigECAgrees
      (bucketParPaperAuthCfgEC (ckaInitA := cka.initA) (ckaInitB := cka.initB) (ckaSend := cka.send)
        (ckaReceive := cka.receive) (prngInit := prng.init) (prngUp := prng.up)
        (fsInitSender := fs.initSender) (fsInitReceiver := fs.initReceiver)
        (fsSend := fs.send) (fsReceive := fs.receive) (eqT := (· == ·)) (eqI := (· == ·))
        (eqM := eqM0) (eqE := eqE0) (lam := lam) (defaultE := (0, default)) (3 + 1) tL par)
      (CryptoGames.SM.Construction.DeliverForge.bucketAuthCfg 1 tL par) := by
    refine ⟨rfl, fun e ρ => ?_, fun _ _ => rfl, fun _ b m₀ m₁ ρ => ?_⟩
    · simpa [bucketParPaperAuthCfgEC, CryptoGames.SM.Construction.DeliverForge.bucketAuthCfg,
        CryptoGames.SM.Construction.DeliverForge.inStage2Bucket, inStage2BucketGen] using
        validGuessBucketParPaperE_eval' (3 + 1) tL par e ρ
    · simp [bucketParPaperAuthCfgEC, CryptoGames.SM.Construction.DeliverForge.bucketAuthCfg, ite_eval]
  let prog : CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      _ _ .unit .unit .bool .bool :=
    redCKAAuthDFPaperBucketProg (q + 1) B0 1 qep maxForwardJumps tL par
  have hInit := initCKAEStateC_eval
    (ckaSend := cka.send) (ckaReceive := cka.receive)
    (fsSend := fs.send) (fsReceive := fs.receive) (eqT := (· == ·)) (eqI := (· == ·))
    (eqM := eqM0) (eqE := eqE0) (lam := lam) (defaultE := (0, default))
    (sampCCoins := ($ᵗ (BitVec 256))) (sampI := ($ᵗ Pt)) (sampK := ($ᵗ (BitVec 256)))
    cka prng fs rfl rfl rfl rfl rfl rfl rfl rfl ⟨true, tL, 0⟩
    (ReductionDsl.Expr.bool (O := ckaOps cka.initA cka.initB cka.send cka.receive prng.init prng.up
      fs.initSender fs.initReceiver fs.send fs.receive (· == ·) (· == ·) eqM0 eqE0 lam (0, default)) false)
    (ReductionDsl.Env.cons (t := .unit) () .nil)
  have hVp : @ckaVpEnc (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
      (BitVec 256) (BitVec 256) (BitVec 256) (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32) = vpEncCKA := rfl
  have hInitP : (prog.init.eval (ReductionDsl.Env.cons (t := .unit) () .nil) :
      OracleComp (unifSpec + CryptoGames.CKA.spec
        (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt)
        (ReductionDsl.Ty.unit.denote × prog.σ.denote)) =
      ((initCKARaw cka prng fs lam ⟨true, tL, 0⟩ false :
          OracleComp (unifSpec + CryptoGames.CKA.spec
            (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt) _) >>= fun es₀ =>
        pure ((), (esEnc vpEncCKA ckaHsEnc es₀, none))) := by
    dsimp only [prog, redCKAAuthDFPaperBucketProg, redCKAAuthDFPaperBucketProgGen, fig8CkaOpsShallow, ckaSchemeOps]
    rw [eval_bind, hInit, hVp]
    simp only [eval_ret, ReductionDsl.Expr.eval, bind_assoc, pure_bind,
      map_eq_bind_pure_comp, Function.comp_def]
    rfl
  have hStep1 : (prog.eval (fun _ => A) () :
      OracleComp (unifSpec + CryptoGames.CKA.spec
        (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt) Bool) =
      ((initCKARaw cka prng fs lam ⟨true, tL, 0⟩ false :
          OracleComp (unifSpec + CryptoGames.CKA.spec
            (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt) _) >>= fun es₀ =>
        ((simulateQ (handlerImpl prog.handle) A).run
            ((esEnc vpEncCKA ckaHsEnc es₀, none) : prog.σ.denote) :
          OracleComp (unifSpec + CryptoGames.CKA.spec
            (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt) _) >>= fun x_1 =>
          (prog.finish.eval (.cons x_1.2 (.cons (t := .bool) x_1.1 .nil)) :
            OracleComp (unifSpec + CryptoGames.CKA.spec
              (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt) Bool)) := by
    unfold ReductionDsl.CostedReduction.eval ReductionDsl.CostedReduction.impl
    dsimp only
    refine (congrArg (fun m => (m : OracleComp _ _) >>= _) hInitP).trans ?_
    refine (bind_assoc (m := OracleComp _) _ _ _).trans ?_
    refine bind_congr fun es₀ => ?_
    exact pure_bind _ _
  rw [hStep1, runCKADFPaperBucket_eq_bind_initCKARaw]
  refine OracleComp.bind_congr_of_forall_mem_support
    (initCKARaw cka prng fs lam ⟨true, tL, 0⟩ false :
      OracleComp (unifSpec + CryptoGames.CKA.spec
        (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt) _) fun es₀ hes₀ => ?_
  have ⟨hInv₀, _⟩ := initCKARaw_inv cka prng fs lam ⟨true, tL, 0⟩ false
    (Nat.le_refl q) (Nat.le_refl (q + 1)) (Nat.mul_le_mul (Nat.le_succ q) (Nat.le_succ q)) es₀ hes₀
  have hVR₀ := initCKARaw_vrInv (B := q) (qAdv := q) cka prng fs lam ⟨true, tL, 0⟩ false
    (fun k => hVRHk.mono (Nat.zero_le _) (hInitR k)) es₀ hes₀
  have ⟨hSim, hSimInv⟩ := simulateQ_implEDFPaperBucket_vr_eq
    (KC := BitVec 256) (CCoins := BitVec 256) (KR := BitVec 256) (K := BitVec 256) (I := Pt)
    (eqT := (· == ·)) (eqI := (· == ·)) (eqM := eqM0) (eqE := eqE0)
    (defaultE := (0, default))
    rfl (fun _ => rfl) ckaHsEnc (fun _ _ => True) (fun _ h => h)
    (hooksCKABucketParPaperC B0 1 (3 + 1) tL par)
    (CryptoGames.SM.Construction.DeliverForge.hooksCKABucket cka prng fs 1 tL par)
    (q + 1) q (2 + 1) qep maxForwardJumps hHk hVRHk
    (bucketParPaperAuthCfgEC (3 + 1) tL par) (CryptoGames.SM.Construction.DeliverForge.bucketAuthCfg 1 tL par)
    hCfg rfl rfl rfl rfl (fun _ _ _ _ _ _ => trivial) hA' es₀ none trivial hInv₀ hVR₀
  refine (congrArg (fun m => (m : OracleComp _ _) >>= _) hSim).trans ?_
  refine (bind_map_left (m := OracleComp _) _ _ _).trans ?_
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨b', es', winEp'⟩ hes' => ?_
  have hBnd' := (hSimInv (b', es', winEp') hes').2.1.toBoundedEngine
  let OO0 := ckaOps cka.initA cka.initB cka.send cka.receive prng.init prng.up
    fs.initSender fs.initReceiver fs.send fs.receive (· == ·) (· == ·) eqM0 eqE0 lam (0, default)
  dsimp only [Prod.map, id_eq, prog, redCKAAuthDFPaperBucketProg, redCKAAuthDFPaperBucketProgGen,
    fig8CkaOpsShallow, ckaSchemeOps, CryptoGames.SM.Construction.DeliverForge.authOutBucketPaper, CryptoGames.SM.Construction.DeliverForge.authOutBucket]
  rw [eval_bind_ret]
  have hEnvEq : (ReductionDsl.Expr.pair (.fst (ReductionDsl.Expr.v0 (O := OO0))) (.snd .v0)).eval
      (ReductionDsl.Env.cons (t := ckaBucketEsTy) (esEnc vpEncCKA ckaHsEnc es', winEp')
        (ReductionDsl.Env.cons (t := .bool) b' .nil)) =
      (esEnc vpEncCKA ckaHsEnc es', winEp') := rfl
  rw [hEnvEq, eval_caseOpt]
  rcases winEp' with _ | tWin
  · rfl
  · set ρ_fin := ReductionDsl.Env.cons (t := .nat) tWin
      (ReductionDsl.Env.cons (t := .prod ckaEsTy (.opt .nat)) (esEnc vpEncCKA ckaHsEnc es', some tWin)
        (ReductionDsl.Env.cons (t := ckaBucketEsTy) (esEnc vpEncCKA ckaHsEnc es', some tWin)
          (ReductionDsl.Env.cons (t := .bool) b' .nil)))
    change (ReductionDsl.Comp.ret _).eval ρ_fin = _
    rw [eval_ret]
    congr 1
    have hAuth := cAuthOKE_eval vpEncCKA (O' := OO0) (q + 1) (2 + 1)
      (optNatLit tL) .v0 (esG (.fst .v1)) ρ_fin es'.g hBnd'.leaks_le hBnd'.corrs_le rfl
    have htL : (optNatLit (O' := OO0) tL).eval ρ_fin = tL := by cases tL <;> rfl
    have hAb : (esAbort (O' := OO0) (.fst .v1)).eval ρ_fin = es'.abort := rfl
    have hW : (cGsWin (O' := OO0) (esG (.fst .v1))).eval ρ_fin = es'.g.win := rfl
    have hV0 : (ReductionDsl.Expr.v0 (O := OO0)).eval ρ_fin = tWin := rfl
    simp only [ReductionDsl.Expr.eval, authOut, hAb, hW, hAuth, htL, hV0, Bool.and_assoc]
private theorem redCKAAuthDFPaperBucket_fsAtomicB_eq_lFS
    {Pt KC Γ CCoins I KR RSt : Type} [DecidableEq Pt] [DecidableEq I]
    [SampleableType KC] [SampleableType CCoins] [SampleableType KR]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : I) (B0 B_q Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (A : CryptoGames.SM.Construction.DeliverForge.SchemeAdversaryDF Γ Pt RSt
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) CCoins (ℕ × LibsignalCiphertextWithSalt32))
    (qAdv : ℕ) (hA : CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF A qAdv) (hqB : qAdv ≤ B_q)
    (hSendOk : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    CryptoGames.SM.Construction.DeliverForge.redCKAAuthDFPaperBucket cka prng (fsAtomicB C ℓ encT idOf B0)
        lam Δcka qep tL par A =
      CryptoGames.SM.Construction.DeliverForge.redCKAAuthDFPaperBucket cka prng
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep tL par A := by
  have hA' : A.IsQueryBoundP (ReductionDsl.isGameQuery (G := CryptoGames.SM.Construction.DeliverForge.specDF
      (PartyState Γ Pt RSt (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256)))
      (LibsignalMsgPublicPart × Plain ℓ) CCoins (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)))) qAdv := by
    refine hA.of_imp fun x hx => ?_; rcases x with _ | _ <;> simp_all [ReductionDsl.isGameQuery]
  rw [runCKADFPaperBucket_eq_bind_initCKARaw, runCKADFPaperBucket_eq_bind_initCKARaw]
  have hInitEq :
      (initCKARaw cka prng (fsAtomicB C ℓ encT idOf B0) lam ⟨true, tL, 0⟩ false :
        OracleComp (unifSpec + CryptoGames.CKA.spec Γ CCoins Pt I) _) =
      initCKARaw cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam ⟨true, tL, 0⟩ false := rfl
  have hms1 : (fsAtomicB C ℓ encT idOf B0).maxSkip = maxForwardJumps := rfl
  have hms2 : (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip = maxForwardJumps := rfl
  rw [hInitEq, hms1, hms2]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun es₀ hes₀ => ?_
  have ⟨hInv₀, _⟩ := initCKARaw_inv cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
    lam ⟨true, tL, 0⟩ false hqB (Nat.le_refl (B_q + 1))
    (Nat.mul_le_mul (Nat.le_succ B_q) (Nat.le_succ B_q)) es₀ hes₀
  have hVRHk := hooksCKABucket_df_vrInv_lFS cka prng C ℓ encT idOf Δcka tL par
  have hVR₀ := initCKARaw_vrInv (B := B_q) (qAdv := qAdv) cka prng
    (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam ⟨true, tL, 0⟩ false
    (fun k => hVRHk.mono (Nat.zero_le _) (Computational.Proofs.ReductionDsl.Fig8Atomic.RSReachB.init
      ((lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
      (lChainPRG C.F) maxForwardJumps k)) es₀ hes₀
  rw [simulateQ_implEDFPaperBucket_localFs_eq (Δ := 2 + Δcka) (qep := qep)
    (cfg := CryptoGames.SM.Construction.DeliverForge.bucketAuthCfg Δcka tL par)
    (hooksCKABucket_df_localFsAgree cka prng C ℓ encT idOf B0 Δcka tL par)
    hVRHk hB0 hA' hSendOk es₀ none hInv₀ hVR₀]
private lemma implEDFPaperBucketRaw_ckaSync_eq
    {Pt KR RSt K SS RS M E : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [SampleableType K]
    [DecidableEq M] [DecidableEq E] [Inhabited E]
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E) (Δcka tStar qep maxSkip : ℕ)
    (tL : Option ℕ) (par : Bool)
    (es : EState (VP (Option (CryptoGames.CKA.DDH.State (BitVec 256) Pt)) Pt RSt SS RS)
      M (Header Pt × E) (CKAState Pt Pt))
    (sc : CryptoGames.CKA.GameState (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt)
    (t : (CryptoGames.SM.Construction.DeliverForge.specDF
      (PartyState (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt SS RS) M (BitVec 256)
      (Header Pt × E)).Domain)
    (hSync : OptCKASync es sc) :
    (simulateQ (ckaFullImpl (dhScheme Dh) Δcka tStar)
      ((CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketRaw (CryptoGames.SM.Construction.DeliverForge.hooksCKABucket (dhSchemeFb Dh) prng fs Δcka tL par)
        (2 + Δcka) qep maxSkip (CryptoGames.SM.Construction.DeliverForge.bucketAuthCfg Δcka tL par) (.inr t)).run es)).run sc =
    (simulateQ (ckaFullImpl (dhScheme Dh) Δcka tStar)
      ((CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketRaw (CryptoGames.SM.Construction.DeliverForge.hooksCKABucket (dhScheme Dh) prng fs Δcka tL par)
        (2 + Δcka) qep maxSkip (CryptoGames.SM.Construction.DeliverForge.bucketAuthCfg Δcka tL par) (.inr t)).run es)).run sc ∧
    ∀ z ∈ support ((simulateQ (ckaFullImpl (dhScheme Dh) Δcka tStar)
      ((CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketRaw (CryptoGames.SM.Construction.DeliverForge.hooksCKABucket (dhScheme Dh) prng fs Δcka tL par)
        (2 + Δcka) qep maxSkip (CryptoGames.SM.Construction.DeliverForge.bucketAuthCfg Δcka tL par) (.inr t)).run es)).run sc),
      OptCKASync z.1.2 z.2 := by
  let hk₁ := CryptoGames.SM.Construction.DeliverForge.hooksCKABucket (dhSchemeFb Dh) prng fs Δcka tL par
  let hk₂ := CryptoGames.SM.Construction.DeliverForge.hooksCKABucket (dhScheme Dh) prng fs Δcka tL par
  let mo₀ : Mode := ⟨true, tL, 0⟩
  have hvRecvEq : ∀ (Scheme : CKAScheme (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt)
      (ctx : Ctx (Option (CryptoGames.CKA.DDH.State (BitVec 256) Pt)) Pt RSt SS RS M E)
      (P : Party) (vp : PartyState (Option (CryptoGames.CKA.DDH.State (BitVec 256) Pt)) Pt RSt SS RS)
      (c : Header Pt × E) (rec : Option (Record M (Header Pt × E))),
      vRecv (CryptoGames.SM.Construction.DeliverForge.hooksCKABucket Scheme prng fs Δcka tL par) ctx P vp c rec =
        vRecv (hooksCKA Scheme prng fs Δcka
          ⟨true, tL, if CryptoGames.SM.Construction.DeliverForge.inStage2Bucket Δcka tL par c.1.1 then c.1.1 else c.1.1 + 1⟩)
          ctx P vp c rec := by
    intro Scheme ctx P vp c rec
    unfold vRecv
    by_cases h1 : (vp.id.sendsIn c.1.1 || decide (vp.tcur + 1 < c.1.1)) = true
    · simp only [h1, ↓reduceIte]
    · simp only [h1, Bool.false_eq_true, ↓reduceIte]
      by_cases h2 : c.1.1 = vp.tcur + 1
      · simp only [h2, ↓reduceIte, startRecv_hooksCKABucket_df_eq]; rfl
      · simp only [h2, ↓reduceIte]; rfl
  rcases t with t5 | ⟨P, c, c'⟩
  · rcases t5 with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
    · have hI₁ : (CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketRaw hk₁ (2 + Δcka) qep maxSkip
          (CryptoGames.SM.Construction.DeliverForge.bucketAuthCfg Δcka tL par) (.inr (.inl (.inl (.inl (.inl (.inl (P, m, r)))))))).run es =
          (CryptoGames.SM.Construction.DeliverForge.transmitEBucket hk₁ (2 + Δcka) qep (P, m, r)).run es := rfl
      have hI₂ : (CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketRaw hk₂ (2 + Δcka) qep maxSkip
          (CryptoGames.SM.Construction.DeliverForge.bucketAuthCfg Δcka tL par) (.inr (.inl (.inl (.inl (.inl (.inl (P, m, r)))))))).run es =
          (CryptoGames.SM.Construction.DeliverForge.transmitEBucket hk₂ (2 + Δcka) qep (P, m, r)).run es := rfl
      rw [hI₁, hI₂]
      unfold CryptoGames.SM.Construction.DeliverForge.transmitEBucket abortE
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
            rw [CryptoGames.SM.Engine.epMgmt_st_eq hep]; exact hSync.2 habF Q
          have hvs := vSend_ckaSync_eq Dh prng fs Δcka tStar mo₀ s₁ P (s₁.st P) m none r es.h sc
            hSync.1 (hs₁All P)
          have hvs₁ : vSend hk₁ = vSend (hooksCKA (dhSchemeFb Dh) prng fs Δcka mo₀) := rfl
          have hvs₂ : vSend hk₂ = vSend (hooksCKA (dhScheme Dh) prng fs Δcka mo₀) := rfl
          simp only [hvs₁, hvs₂]
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
    · have hI₁ : (CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketRaw hk₁ (2 + Δcka) qep maxSkip
          (CryptoGames.SM.Construction.DeliverForge.bucketAuthCfg Δcka tL par) (.inr (.inl (.inl (.inl (.inl (.inr (P, m₀, m₁, r)))))))).run es =
          pure (none, es) := rfl
      have hI₂ : (CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketRaw hk₂ (2 + Δcka) qep maxSkip
          (CryptoGames.SM.Construction.DeliverForge.bucketAuthCfg Δcka tL par) (.inr (.inl (.inl (.inl (.inl (.inr (P, m₀, m₁, r)))))))).run es =
          pure (none, es) := rfl
      rw [hI₁, hI₂]
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
    · have hI₁ : (CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketRaw hk₁ (2 + Δcka) qep maxSkip
          (CryptoGames.SM.Construction.DeliverForge.bucketAuthCfg Δcka tL par) (.inr (.inl (.inl (.inl (.inr (P, c))))))).run es =
          (deliverE hk₁ maxSkip (CryptoGames.SM.Construction.DeliverForge.bucketAuthCfg Δcka tL par) (P, c)).run es := rfl
      have hI₂ : (CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketRaw hk₂ (2 + Δcka) qep maxSkip
          (CryptoGames.SM.Construction.DeliverForge.bucketAuthCfg Δcka tL par) (.inr (.inl (.inl (.inl (.inr (P, c))))))).run es =
          (deliverE hk₂ maxSkip (CryptoGames.SM.Construction.DeliverForge.bucketAuthCfg Δcka tL par) (P, c)).run es := rfl
      rw [hI₁, hI₂]
      unfold deliverE abortE
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
            ⟨true, tL, if CryptoGames.SM.Construction.DeliverForge.inStage2Bucket Δcka tL par c.1.1 then c.1.1 else c.1.1 + 1⟩
          obtain ⟨hvrEq, ⟨⟨vrRes, h'⟩, hvrPure, hvrPost⟩⟩ :=
            vRecv_hooksCKA_pure_eq Dh prng fs Δcka moC es.g P (es.g.st P) c (some r) es.h sc
              (hSync.2 habF P)
          rw [run_liftH_bind, run_liftH_bind]
          dsimp only [hk₁, hk₂]
          rw [hvRecvEq, hvRecvEq, hvrEq, hvrPure]
          simp only [pure_bind]
          rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              simulateQ_pure, support_pure, Set.mem_singleton_iff]
            exact ⟨trivial, fun _ h => by subst h; exact ⟨hSync.1, fun h' => nomatch h'⟩⟩
          · split_ifs <;>
              (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                 simulateQ_pure, support_pure, Set.mem_singleton_iff];
               exact ⟨trivial, fun _ h => by subst h; exact hSync⟩)
          · have hcm₁ : commitE (CryptoGames.SM.Construction.DeliverForge.hooksCKABucket (dhSchemeFb Dh) prng fs Δcka tL par) =
                commitE (hooksCKA (dhSchemeFb Dh) prng fs Δcka mo₀) := rfl
            have hcm₂ : commitE (CryptoGames.SM.Construction.DeliverForge.hooksCKABucket (dhScheme Dh) prng fs Δcka tL par) =
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
    · have hI₁ : (CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketRaw hk₁ (2 + Δcka) qep maxSkip
          (CryptoGames.SM.Construction.DeliverForge.bucketAuthCfg Δcka tL par) (.inr (.inl (.inl (.inr (P, c)))))).run es =
          (injectE hk₁ (2 + Δcka) qep (CryptoGames.SM.Construction.DeliverForge.bucketAuthCfg Δcka tL par) (P, c)).run es := rfl
      have hI₂ : (CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketRaw hk₂ (2 + Δcka) qep maxSkip
          (CryptoGames.SM.Construction.DeliverForge.bucketAuthCfg Δcka tL par) (.inr (.inl (.inl (.inr (P, c)))))).run es =
          (injectE hk₂ (2 + Δcka) qep (CryptoGames.SM.Construction.DeliverForge.bucketAuthCfg Δcka tL par) (P, c)).run es := rfl
      rw [hI₁, hI₂]
      unfold injectE abortE
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
          ⟨true, tL, if CryptoGames.SM.Construction.DeliverForge.inStage2Bucket Δcka tL par c.1.1 then c.1.1 else c.1.1 + 1⟩
        obtain ⟨hvrEq, ⟨⟨vrRes, h'⟩, hvrPure, hvrPost⟩⟩ :=
          vRecv_hooksCKA_pure_eq Dh prng fs Δcka moC es.g P (es.g.st P) c none es.h sc
            (hSync.2 habF P)
        simp only [href, Bool.false_eq_true, ↓reduceIte]
        rw [run_liftH_bind, run_liftH_bind]
        dsimp only [hk₁, hk₂]
        rw [hvRecvEq, hvRecvEq, hvrEq, hvrPure]
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
            · have hcm₁ : commitE (CryptoGames.SM.Construction.DeliverForge.hooksCKABucket (dhSchemeFb Dh) prng fs Δcka tL par) =
                  commitE (hooksCKA (dhSchemeFb Dh) prng fs Δcka mo₀) := rfl
              have hcm₂ : commitE (CryptoGames.SM.Construction.DeliverForge.hooksCKABucket (dhScheme Dh) prng fs Δcka tL par) =
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
    · have hI₁ : (CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketRaw hk₁ (2 + Δcka) qep maxSkip
          (CryptoGames.SM.Construction.DeliverForge.bucketAuthCfg Δcka tL par) (.inr (.inl (.inr P)))).run es =
          (CryptoGames.SM.Construction.DeliverForge.corrEPaperBucket hk₁ P).run es := rfl
      have hI₂ : (CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketRaw hk₂ (2 + Δcka) qep maxSkip
          (CryptoGames.SM.Construction.DeliverForge.bucketAuthCfg Δcka tL par) (.inr (.inl (.inr P)))).run es =
          (CryptoGames.SM.Construction.DeliverForge.corrEPaperBucket hk₂ P).run es := rfl
      rw [hI₁, hI₂]
      have hRevEq : hk₁.reveal = hk₂.reveal := rfl
      unfold CryptoGames.SM.Construction.DeliverForge.corrEPaperBucket abortE
      simp only [StateT.run_bind, StateT.run_get, pure_bind, hRevEq]
      refine ⟨trivial, fun z hz => ?_⟩
      by_cases href : (es.abort || es.g.win || !(es.g.corrAllowedPaper P)) = true
      · simp only [href, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at hz
        subst hz; exact hSync
      · simp only [href, Bool.false_eq_true, ↓reduceIte] at hz
        rw [run_liftH_bind] at hz
        simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
        obtain ⟨⟨⟨revRes, h'⟩, sc₁⟩, hrev, hz⟩ := hz
        have hsc₁_eq : sc₁ = sc := by
          dsimp only [hk₂, CryptoGames.SM.Construction.DeliverForge.hooksCKABucket, hooksCKA] at hrev
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
          subst hz
          exact ⟨hSync.1, hSync.2⟩
  · have hI₁ : (CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketRaw hk₁ (2 + Δcka) qep maxSkip
        (CryptoGames.SM.Construction.DeliverForge.bucketAuthCfg Δcka tL par) (.inr (.inr (P, c, c')))).run es =
        (CryptoGames.SM.Construction.DeliverForge.deliverForgeE hk₁ (2 + Δcka) qep (CryptoGames.SM.Construction.DeliverForge.bucketAuthCfg Δcka tL par) (P, c, c')).run es := rfl
    have hI₂ : (CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketRaw hk₂ (2 + Δcka) qep maxSkip
        (CryptoGames.SM.Construction.DeliverForge.bucketAuthCfg Δcka tL par) (.inr (.inr (P, c, c')))).run es =
        (CryptoGames.SM.Construction.DeliverForge.deliverForgeE hk₂ (2 + Δcka) qep (CryptoGames.SM.Construction.DeliverForge.bucketAuthCfg Δcka tL par) (P, c, c')).run es := rfl
    rw [hI₁, hI₂]
    unfold CryptoGames.SM.Construction.DeliverForge.deliverForgeE abortE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win) = true
    · simp only [hab, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
      exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
    · have habF : es.abort = false := (Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hab)).1
      simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases htr : es.g.inTransit P.other c with _ | r
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
        exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
      · dsimp only
        by_cases hchk : ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos || c.1 != c'.1) = true
        · simp only [hchk, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
          exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
        · let moC : Mode :=
            ⟨true, tL, if CryptoGames.SM.Construction.DeliverForge.inStage2Bucket Δcka tL par c'.1.1 then c'.1.1 else c'.1.1 + 1⟩
          obtain ⟨hvrEq, ⟨⟨vrRes, h'⟩, hvrPure, hvrPost⟩⟩ :=
            vRecv_hooksCKA_pure_eq Dh prng fs Δcka moC es.g P (es.g.st P) c' none es.h sc
              (hSync.2 habF P)
          simp only [hchk, Bool.false_eq_true, ↓reduceIte]
          rw [run_liftH_bind, run_liftH_bind]
          dsimp only [hk₁, hk₂]
          rw [hvRecvEq, hvRecvEq, hvrEq, hvrPure]
          simp only [pure_bind]
          rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              simulateQ_pure, support_pure, Set.mem_singleton_iff]
            exact ⟨trivial, fun _ h => by subst h; exact ⟨hSync.1, fun h' => nomatch h'⟩⟩
          · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
            exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
          · by_cases hqep : (decide (qep + 1 < t') || t' != r.pos.epoch) = true
            · simp only [hqep, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
              exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
            · simp only [hqep, Bool.false_eq_true, ↓reduceIte]
              by_cases htriv : es.g.trivial (2 + Δcka) ⟨P.other, t', i'⟩ = true
              · have hcm₁ : commitE (CryptoGames.SM.Construction.DeliverForge.hooksCKABucket (dhSchemeFb Dh) prng fs Δcka tL par) =
                    commitE (hooksCKA (dhSchemeFb Dh) prng fs Δcka mo₀) := rfl
                have hcm₂ : commitE (CryptoGames.SM.Construction.DeliverForge.hooksCKABucket (dhScheme Dh) prng fs Δcka tL par) =
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
private lemma simulateQ_implEDFPaperBucket_ckaSync_eq
    {Pt KR RSt K SS RS M E α : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [SampleableType K]
    [DecidableEq M] [DecidableEq E] [Inhabited E]
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E) (Δcka tStar qep : ℕ)
    (tL : Option ℕ) (par : Bool)
    (oa : CryptoGames.SM.Construction.DeliverForge.AdversaryCompDF
      (PartyState (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt SS RS)
      M (BitVec 256) (Header Pt × E) α)
    (es : EState (VP (Option (CryptoGames.CKA.DDH.State (BitVec 256) Pt)) Pt RSt SS RS)
      M (Header Pt × E) (CKAState Pt Pt))
    (winEp : Option ℕ)
    (sc : CryptoGames.CKA.GameState (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt)
    (hSync : OptCKASync es sc) :
    (simulateQ (ckaFullImpl (dhScheme Dh) Δcka tStar)
      ((simulateQ (CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucket
        (CryptoGames.SM.Construction.DeliverForge.hooksCKABucket (dhSchemeFb Dh) prng fs Δcka tL par)
        (2 + Δcka) qep fs.maxSkip (CryptoGames.SM.Construction.DeliverForge.bucketAuthCfg Δcka tL par)) oa).run (es, winEp))).run sc =
    (simulateQ (ckaFullImpl (dhScheme Dh) Δcka tStar)
      ((simulateQ (CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucket
        (CryptoGames.SM.Construction.DeliverForge.hooksCKABucket (dhScheme Dh) prng fs Δcka tL par)
        (2 + Δcka) qep fs.maxSkip (CryptoGames.SM.Construction.DeliverForge.bucketAuthCfg Δcka tL par)) oa).run (es, winEp))).run sc := by
  induction oa using OracleComp.inductionOn generalizing es winEp sc with
  | pure x => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind qy mx ih =>
    rw [simulateQ_query_bind, simulateQ_query_bind, StateT.run_bind, StateT.run_bind,
      simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind]
    have hLift : ∀ {M' : Type → Type} [Monad M'] {σ' α' : Type} (m : StateT σ' M' α') (s : σ'),
        (liftM m : StateT σ' M' α').run s = m.run s := fun _ _ => rfl
    rw [hLift, hLift]
    simp only [OracleQuery.input_query, OracleQuery.cont_query]
    unfold CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucket CryptoGames.SM.Construction.DeliverForge.withWinEpDF
    dsimp only [StateT.run_mk]
    simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, bind_assoc]
    rcases qy with n | t_sm
    · have hInl₁ :
          (CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketRaw
            (CryptoGames.SM.Construction.DeliverForge.hooksCKABucket (dhSchemeFb Dh) prng fs Δcka tL par)
            (2 + Δcka) qep fs.maxSkip (CryptoGames.SM.Construction.DeliverForge.bucketAuthCfg Δcka tL par) (.inl n)).run es =
          (coinsE n).run es := rfl
      have hInl₂ :
          (CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketRaw
            (CryptoGames.SM.Construction.DeliverForge.hooksCKABucket (dhScheme Dh) prng fs Δcka tL par)
            (2 + Δcka) qep fs.maxSkip (CryptoGames.SM.Construction.DeliverForge.bucketAuthCfg Δcka tL par) (.inl n)).run es =
          (coinsE n).run es := rfl
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
      simp only [pure_bind]
      rw [hesEq, hscEq]
      exact ih u es _ sc hSync
    · obtain ⟨hEq, hPost⟩ :=
        implEDFPaperBucketRaw_ckaSync_eq Dh prng fs Δcka tStar qep fs.maxSkip tL par es sc t_sm hSync
      rw [hEq]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨u, es'⟩, sc'⟩ hmem => ?_
      simp only [pure_bind]
      exact ih u es' _ sc' (hPost _ hmem)
private theorem ckaBranch_redCKAAuthDFPaperBucket_dhSchemeFb_eq
    {Pt KR RSt K SS RS M E : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [SampleableType KR] [SampleableType K]
    [DecidableEq M] [DecidableEq E] [Inhabited E]
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E) (lam : Pt) (Δcka tStar qep : ℕ)
    (tL : Option ℕ) (par : Bool) (b : Bool)
    (A : CryptoGames.SM.Construction.DeliverForge.SchemeAdversaryDF (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
      Pt RSt SS RS M (BitVec 256) E) :
    CryptoGames.CKA.branch (dhSchemeFb Dh) Δcka tStar b
      (CryptoGames.SM.Construction.DeliverForge.redCKAAuthDFPaperBucket (dhSchemeFb Dh) prng fs lam Δcka qep tL par A) =
    CryptoGames.CKA.branch (dhScheme Dh) Δcka tStar b
      (CryptoGames.SM.Construction.DeliverForge.redCKAAuthDFPaperBucket (dhScheme Dh) prng fs lam Δcka qep tL par A) := by
  rw [ckaBranch_dhSchemeFb_eq]
  unfold CryptoGames.CKA.branch CryptoGames.SM.Construction.DeliverForge.redCKAAuthDFPaperBucket CryptoGames.SM.Construction.DeliverForge.engRunDFPaperBucket
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
        { g := { st := (fun P => match P with | .A => vA | .B => vB), b := false }, h := h } sc := by
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
      (simulateQ_implEDFPaperBucket_ckaSync_eq Dh prng fs Δcka tStar qep tL par A _ none sc
        (hSyncInit vA vB rfl))
theorem compileCkaDFAtomic_paperBucket_advantage {Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (tStar qep q : ℕ) (tL : Option ℕ) (par : Bool)
    (A : CryptoGames.SM.Construction.DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (hqA : CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF A q)
    (hshA : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    CryptoGames.CKA.advantage (dhScheme Dh) 1 tStar
      ((Computational.Proofs.SessionCostedFig8.DFProgBucketBounds.redCKAAuthDFPaperBucketAtomicProg
          Dh encPt C ℓ encT idOf lam qep q tL par).eval (fun _ => A) ()) =
    CryptoGames.CKA.advantage (dhScheme Dh) 1 tStar
      (CryptoGames.SM.Construction.DeliverForge.redCKAAuthDFPaperBucket (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam 1 qep tL par A) := by
  have hDhEq : ∀ B, CryptoGames.CKA.advantage (dhScheme Dh) 1 tStar B =
      CryptoGames.CKA.advantage (dhSchemeFb Dh) 1 tStar B := fun B => by
    rw [CryptoGames.CKA.advantage_eq_boolDist, CryptoGames.CKA.advantage_eq_boolDist,
      ckaBranch_dhSchemeFb_eq, ckaBranch_dhSchemeFb_eq]
  rw [hDhEq]
  unfold Computational.Proofs.SessionCostedFig8.DFProgBucketBounds.redCKAAuthDFPaperBucketAtomicProg
  dsimp only
  let B0 := (q + 1) * (maxForwardJumps + 1)
  rw [ckaAdvantage_congr (dhSchemeFb Dh) 1 tStar
      (compileCkaDFAtomic_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam hℓ B0
        (CryptoGames.SM.Construction.redCKAAuthDFPaperBucketProg (q + 1) B0 1 qep maxForwardJumps tL par) A),
    redCKAAuthDFPaperBucketProg_eval_atomic Dh encPt C ℓ encT idOf lam qep q tL par A hqA,
    CryptoGames.CKA.advantage_eq_boolDist, CryptoGames.CKA.advantage_eq_boolDist,
    ckaBranch_redCKAAuthDFPaperBucket_dhSchemeFb_eq Dh (rootPRNG C.F encPt)
      (fsAtomicB C ℓ encT idOf B0) lam 1 tStar qep tL par true A,
    ckaBranch_redCKAAuthDFPaperBucket_dhSchemeFb_eq Dh (rootPRNG C.F encPt)
      (fsAtomicB C ℓ encT idOf B0) lam 1 tStar qep tL par false A,
    redCKAAuthDFPaperBucket_fsAtomicB_eq_lFS (dhScheme Dh) (rootPRNG C.F encPt) C ℓ encT idOf lam
      B0 q 1 qep tL par (Nat.le_refl _) A q hqA (Nat.le_refl q) hshA]
end Stage2BucketCKA
end

end Computational.Proofs.HeadlineV1.Stage2BucketCKASwap
