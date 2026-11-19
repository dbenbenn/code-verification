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
# Atomic Evaluation and `dhSchemeFb` + `fsAtomicB → dhScheme` + `lFS` Bridges for Stage-2 Bucket CKA & PRNG-/

open Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth (PRNGBucketAuthState bucketAuthCfg hooksPRNGBucketAuthForgedHdr hooksPRNGBucketAuthHybrid hooksPRNGBucketAuthMain implPRNGBucketAuthGen initPRNGBucketAuthHybrid isHonestHdrPRNGBucket postLeak redPRNGAuthBucketHybrid redPRNGAuthBucketHybridForgedHdr redPRNGAuthBucketHybridMain redPRNGAuthBucketHybridProg redPRNGAuthBucketHybridProg_branch_eval_vr resolveCorrRoot rootPRNGBucketAuthHybrid runPRNGAuthBucketHybridGen)
open CryptoGames (CKAScheme FSAEADScheme PRFPRNG Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun dhScheme)
open CryptoGames.FSAEAD (RatchetReceiverState RatchetSenderState)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey maxForwardJumps)
open CryptoGames.PRFPRNG (prngIface)
open CryptoGames.Ratchet (rootPRNG)
open CryptoGames.Ratchet.LibsignalInst (LibsignalCiphertextWithSalt32 LibsignalMsgPublicPart lAead lChainPRG lFS lPubOf)
open CryptoGames.SM.Construction (Header PartyState SchemeAdversary)
open CryptoGames.SM.Engine (Ctx EState Hooks HooksVRInv Policy RSReach SMEngineInv SMVRInv VP abortE challE coinsE commitE corrE deliverE implE implE_inv implE_vrInv injectE run_liftH_bind transmitE)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSession.Fig8SchemeBridge (AllPartiesInv DdhRoleOk HooksLocalCKAAgree badSendMsg_query_bind_step badSendMsg_transmit_false ddhRoleOk_initA ddhRoleOk_initB dhSchemeFb_receive_of_roleOk dhSchemeFb_send_of_roleOk implE_localCKA_eq)

namespace Computational.Proofs.SessionCostedFig8.BucketPRNGSwap

public section

set_option autoImplicit false
set_option linter.dupNamespace false

open OracleSpec OracleComp
open _root_.CryptoGames (Party CKAScheme PRFPRNG FSAEADScheme)
open _root_.CryptoGames.CKA (DHFun dhScheme)
open _root_.CryptoGames.Ratchet (rootPRNG)
open _root_.CryptoGames.FSAEAD (RatchetSenderState RatchetReceiverState)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.LibsignalSession (Crypto PublicKey IdentityKey maxForwardJumps)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart LibsignalCiphertextWithSalt32
  lFS lAead lPubOf lChainPRG)
open _root_.CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open _root_.CryptoGames.LibsignalSM (Fig8Adv)
open _root_.CryptoGames.SM (Record Config)
open _root_.CryptoGames.SM.Engine (Policy VP Ctx EState Hooks HooksVRInv SMEngineInv SMVRInv
  RSReach TComp vSend vSendStep1 vSend_eq_bind vRecv vRecvStep1 vRecv_eq_bind
  commitE abortE transmitE challE deliverE injectE corrE coinsE implE engRun
  run_liftH_bind epMgmt_st_eq implE_inv implE_vrInv)
open _root_.CryptoGames.SM.Construction (PartyState SchemeAdversary Header Mode CKAState PRNGState
  sampleT mkParties liftC hooksCKA hooksCKA_startRecv_rs hooksCKA_commit_vR
  initCKA initCKARaw initCKARaw_inv initCKARaw_vrInv runCKA
  hooksCKABucketC bucketAuthCfgEC ckaStartRecvBucketAnsE redCKAAuthBucketProg)
open Computational.Proofs.ReductionDsl.Fig8Atomic (dhSchemeFb aeadAtomic atomicShortPubB
  fsAtomicB fsAtomicB_send_eq fsAtomicB_receive_eq RSReachB)
open Computational.Proofs.SessionCostedFig8.Bundles (fig8CkaOpsShallow)
open Computational.Proofs.SessionCostedFig8.BundlesEval (fsAtomicB_receive_rsReach)
open Computational.Proofs.SessionCostedFig8.FsAtomicBSwap (HooksLocalFsAgree vSend_localFs_eq
  vRecv_localFs_eq)
open _root_.CryptoVerification.LibsignalSession.Fig8SchemeBridge (DdhRoleOk ddhRoleOk_initA
  ddhRoleOk_initB dhSchemeFb_send_of_roleOk dhSchemeFb_receive_of_roleOk
  HooksLocalCKAAgree AllPartiesInv implE_localCKA_eq badSendMsg_query_bind_step
  badSendMsg_transmit_false CkaStateInv OptPartySync OptCKASync ckaFullImpl
  ckaBranch_dhSchemeFb_eq ckaStateInv_init simulateQ_ckaFullImpl_liftProb
  vSend_ckaSync_eq vRecv_hooksCKA_pure_eq commitE_ckaSync liftC_corrQuery_support
  optPartySync_of_epoch_eq record_st_eq)
open _root_.CryptoGames.CKA (ckaIface ckaSMCodec)
open _root_.CryptoGames.PRFPRNG (prngIface prngSMCodec)

section PRNGAtomicEval

theorem hooksPRNGBucketAuthHybrid_startRecv_rs
    {KC Γ CCoins T I KR RSt K SS RS M E : Type} [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    {VROk : RS → Prop} (hInitR : ∀ k, VROk (fs.initReceiver k))
    (ctx : Ctx Γ T (Option RSt) SS RS M E) (P : Party) (t0 : ℕ)
    (γ0 : Γ) (σ0 : Option RSt) (tn0 : T) (h : PRNGBucketAuthState T RSt K I)
    (res : Option (Option (Γ × Option RSt × RS)) × PRNGBucketAuthState T RSt K I)
    (hmem : res ∈ support ((hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL t).startRecv
      ctx P t0 γ0 σ0 tn0 |>.run h))
    (γ' : Γ) (σ' : Option RSt) (rs : RS) (hEq : res.1 = some (some (γ', σ', rs))) :
    VROk rs := by
  unfold hooksPRNGBucketAuthHybrid at hmem
  dsimp only at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  split at hmem
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rcases Prod.mk.inj hmem.symm with ⟨hres, _⟩
    rw [← hres, Option.some.injEq, Option.some.injEq] at hEq
    rcases Prod.mk.inj hEq with ⟨_, hEq2⟩
    rcases Prod.mk.inj hEq2 with ⟨_, rfl⟩
    exact hInitR _
  · by_cases hAdmiss : (!decide (qep + 1 < t0) && CryptoGames.SM.lastLeakGuessAdmissible (2 + Δcka) tL t0) = true
    · simp only [hAdmiss, ↓reduceIte] at hmem
      by_cases htH : (tL.isSome && decide (t0 = CryptoGames.SM.Construction.healEpoch tL)) = true
      · simp only [htH, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
        rcases Prod.mk.inj hmem.symm with ⟨hres, _⟩
        rw [← hres] at hEq; cases hEq
      · simp only [htH, Bool.false_eq_true, ↓reduceIte] at hmem
        by_cases hPl : (postLeak tL ctx || h.corrRoot.isSome || decide (t < t0)) = true
        · simp only [hPl, ↓reduceIte] at hmem
          rcases hrc : resolveCorrRoot h (t0 - 1) σ0 with _ | σ
          · simp only [hrc, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
            rcases Prod.mk.inj hmem.symm with ⟨hres, _⟩
            rw [← hres] at hEq; cases hEq
          · simp only [hrc, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
            rcases Prod.mk.inj hmem.symm with ⟨hres, _⟩
            rw [← hres, Option.some.injEq, Option.some.injEq] at hEq
            rcases Prod.mk.inj hEq with ⟨_, hEq2⟩
            rcases Prod.mk.inj hEq2 with ⟨_, rfl⟩
            exact hInitR _
        · simp only [hPl, Bool.false_eq_true, ↓reduceIte] at hmem
          by_cases htEq : t0 = t
          · simp only [htEq, ↓reduceIte, StateT.run_bind, mem_support_bind_iff] at hmem
            obtain ⟨⟨qOut, h1⟩, _, hmem⟩ := hmem
            rcases qOut with _ | ⟨σOut, kOut⟩
            · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
              rcases Prod.mk.inj hmem.symm with ⟨hres, _⟩
              rw [← hres] at hEq; cases hEq
            · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
              rcases Prod.mk.inj hmem.symm with ⟨hres, _⟩
              rw [← hres, Option.some.injEq, Option.some.injEq] at hEq
              rcases Prod.mk.inj hEq with ⟨_, hEq2⟩
              rcases Prod.mk.inj hEq2 with ⟨_, rfl⟩
              exact hInitR _
          · simp only [htEq, ↓reduceIte] at hmem
            by_cases hGeH : (!decide (t0 < CryptoGames.SM.Construction.healEpoch tL)) = true
            · simp only [hGeH, ↓reduceIte, StateT.run_bind, mem_support_bind_iff] at hmem
              obtain ⟨⟨kLookup, h1⟩, _, hmem⟩ := hmem
              simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
              rcases Prod.mk.inj hmem.symm with ⟨hres, _⟩
              rw [← hres, Option.some.injEq, Option.some.injEq] at hEq
              rcases Prod.mk.inj hEq with ⟨_, hEq2⟩
              rcases Prod.mk.inj hEq2 with ⟨_, rfl⟩
              exact hInitR _
            · simp only [hGeH, Bool.false_eq_true, ↓reduceIte,
                StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
              rcases Prod.mk.inj hmem.symm with ⟨hres, _⟩
              rw [← hres] at hEq; cases hEq
    · simp only [hAdmiss, Bool.false_eq_true, ↓reduceIte,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      rcases Prod.mk.inj hmem.symm with ⟨hres, _⟩
      rw [← hres] at hEq; cases hEq

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

omit [Zero Pt] [SampleableType Pt] in
theorem hooksPRNGBucketAuthHybrid_vrInv_fsAtomicB
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (B0 Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) :
    HooksVRInv (RSReach maxForwardJumps)
      (hooksPRNGBucketAuthHybrid (dhSchemeFb Dh) (rootPRNG C.F encPt)
        (fsAtomicB C ℓ encT idOf B0) Δcka qep tL t) where
  mono hle hv := hv.mono hle
  startRecv_step ctx P t0 γ0 σ0 tn0 h res hmem γ' σ' rs hEq :=
    hooksPRNGBucketAuthHybrid_startRecv_rs (dhSchemeFb Dh) (rootPRNG C.F encPt)
      (fsAtomicB C ℓ encT idOf B0) Δcka qep tL t
      (CryptoGames.SM.Engine.RSReach.init ((aeadAtomic C ℓ encT idOf).movePubPartToAD
        (lPubOf protoSignalCodec)) (lChainPRG C.F) maxForwardJumps)
      ctx P t0 γ0 σ0 tn0 h res hmem γ' σ' rs hEq
  fsRecv_step _ _ _ rs hdr e _ _ res hVR hmem v' i' m' hEq := by
    rcases res with ⟨ans, h'⟩
    dsimp only at hEq
    subst hEq
    unfold hooksPRNGBucketAuthHybrid at hmem
    dsimp only at hmem
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq, Option.some.injEq] at hmem
    exact (fsAtomicB_receive_rsReach C ℓ encT idOf B0 _ hVR hmem.1.symm).2
  commit_vR _ _ _ new _ res hmem new' hEq := by
    unfold hooksPRNGBucketAuthHybrid at hmem
    dsimp only at hmem
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rcases Prod.mk.inj hmem.symm with ⟨hres, _⟩
    rw [← hres, Option.some.injEq] at hEq
    subst hEq; rfl

omit [Zero Pt] in
theorem redPRNGAuthBucketHybridProg_branch_eval_atomic
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep q : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversary (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (ℕ × LibsignalCiphertextWithSalt32))
    (hqA : CryptoGames.SM.MakesAtMostQueries A q) (b_prng : Bool) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    CryptoGames.PRFPRNG.branch (rootPRNG C.F encPt) b_prng
      (((redPRNGAuthBucketHybridProg (q + 1) B0 1 qep maxForwardJumps tL t :
        ReductionDsl.CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
          (prngIface (BitVec 256)
            (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
            (BitVec 256) (BitVec 256) (BitVec 256)
            (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
            (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
            ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
          _ _ .unit .unit .bool .bool).eval (fun _ => A) ())) =
      CryptoGames.PRFPRNG.branch (rootPRNG C.F encPt) b_prng
        (redPRNGAuthBucketHybrid (dhSchemeFb Dh) (rootPRNG C.F encPt)
          (fsAtomicB C ℓ encT idOf B0) lam 1 qep tL t A) := by
  intro B0
  exact redPRNGAuthBucketHybridProg_branch_eval_vr
    (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsAtomicB C ℓ encT idOf B0)
    (q + 1) B0 q 1 qep tL t
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (hooksPRNGBucketAuthHybrid_vrInv_fsAtomicB Dh encPt C ℓ encT idOf B0 1 qep tL t)
    (CryptoGames.SM.Engine.RSReach.init ((aeadAtomic C ℓ encT idOf).movePubPartToAD
      (lPubOf protoSignalCodec)) (lChainPRG C.F) maxForwardJumps)
    (fun _ _ _ _ _ _ hVR hrec =>
      (fsAtomicB_receive_rsReach C ℓ encT idOf B0 q hVR hrec).1)
    (Nat.le_refl _) (Nat.mul_le_mul (Nat.le_succ q) (Nat.le_succ q))
    A q hqA (Nat.le_refl q) b_prng

end PRNGAtomicEval

section PRNGAtomicSwap

def noDoomPolicy : Policy := ⟨false, none, 0⟩

@[simp] lemma noDoomPolicy_leakDoom {St Msg C : Type}
    (g g' : CryptoGames.SM.GameState St Msg C) :
    noDoomPolicy.leakDoom g g' = false := by
  simp [noDoomPolicy, CryptoGames.SM.Engine.Policy.leakDoom]

@[simp] lemma noDoomPolicy_corrDoom {St Msg C : Type}
    (g : CryptoGames.SM.GameState St Msg C) (P : Party) :
    noDoomPolicy.corrDoom g P = false := by
  simp [noDoomPolicy, CryptoGames.SM.Engine.Policy.corrDoom]

private def prngUpdateWinEp {Γ T Sig SS RS M E K I CCoins : Type} [DecidableEq T]
    (onlyNewForged : Bool)
    (es0 es' : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I))
    (qy : (unifSpec + CryptoGames.SM.spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Domain)
    (winEp0 : Option ℕ) : Option ℕ :=
  match qy with
  | .inr (.inl (.inr x)) =>
    let okWin :=
      if onlyNewForged then
        !es0.g.win && es'.g.win && decide (x.2.1.1 = (es0.g.st x.1).tcur + 1) &&
          !isHonestHdrPRNGBucket es0.h x.2.1
      else
        !es0.g.win && es'.g.win
    if okWin then some x.2.1.1 else winEp0
  | _ => winEp0

private lemma implPRNGBucketAuthGen_run_eq_implE
    {Γ T Sig SS RS M E K I CCoins : Type} [DecidableEq T] [DecidableEq M] [DecidableEq E]
    [Inhabited E]
    (hk : Hooks (CryptoGames.PRFPRNG.spec Sig I K) (PRNGBucketAuthState T Sig K I)
      Γ T Sig SS RS M E CCoins Γ (Option Sig) SS RS)
    (Δcka qep maxSkip : ℕ) (tL : Option ℕ) (onlyNewForged : Bool)
    (qy : (unifSpec + CryptoGames.SM.spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Domain)
    (es0 : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I))
    (winEp0 : Option ℕ) :
    (implPRNGBucketAuthGen hk Δcka qep maxSkip tL onlyNewForged qy).run (es0, winEp0) =
      ((implE hk (2 + Δcka) qep maxSkip (bucketAuthCfg Δcka tL) noDoomPolicy qy).run es0 >>=
        fun res => pure (res.1,
          (res.2, prngUpdateWinEp onlyNewForged es0 res.2 qy winEp0))) := by
  rcases qy with n | ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
  · dsimp only [implPRNGBucketAuthGen, implE, QueryImpl.add_apply, coinsE, prngUpdateWinEp]
    simp [StateT.run_lift]
  · dsimp only [implPRNGBucketAuthGen, implE, QueryImpl.add_apply, transmitE, prngUpdateWinEp]
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
  · dsimp only [implPRNGBucketAuthGen, implE, QueryImpl.add_apply, challE,
      bucketAuthCfg, prngUpdateWinEp]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hcond : (es0.abort || es0.g.win) = true
    · simp [hcond]
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte]
      cases hep : es0.g.epMgmt (2 + Δcka) qep P r.isSome <;> simp
  · dsimp only [implPRNGBucketAuthGen, implE, QueryImpl.add_apply, prngUpdateWinEp]
    simp [StateT.run_lift]
  · dsimp only [implPRNGBucketAuthGen, implE, QueryImpl.add_apply, prngUpdateWinEp]
    simp only [StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set,
      StateT.run_pure, bind_assoc, pure_bind]
    refine bind_congr fun ⟨out, es'⟩ => ?_
    cases onlyNewForged <;> simp [and_assoc]
  · dsimp only [implPRNGBucketAuthGen, implE, QueryImpl.add_apply, corrE, prngUpdateWinEp]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hcond : (es0.abort || es0.g.win || !es0.g.corrAllowed P) = true
    · simp [hcond]
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte,
        noDoomPolicy_leakDoom, noDoomPolicy_corrDoom, Bool.or_self]
      rw [StateT.run_bind, StateT.run_lift, run_liftH_bind]
      simp only [bind_assoc, pure_bind]
      refine bind_congr fun ⟨res, h'⟩ => ?_
      cases res <;> simp [abortE]

lemma implE_bucketAuth_localFs_eq {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
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

private lemma simulateQ_implPRNGBucketAuthGen_localFs_eq
    {Γ Pt I RSt CCoins α : Type} [DecidableEq Pt]
    {ℓ L B0 B_q q Δcka qep : ℕ} {tL : Option ℕ} {onlyNewForged : Bool}
    {hk₁ hk₂ : Hooks (CryptoGames.PRFPRNG.spec RSt I (BitVec 256))
      (PRNGBucketAuthState Pt RSt (BitVec 256) I) Γ Pt RSt
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
      CCoins Γ (Option RSt)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))}
    (hAg : HooksLocalFsAgree ℓ B0 hk₁ hk₂)
    (hVRHk : HooksVRInv (RSReachB maxForwardJumps) hk₂)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    {oa : OracleComp (unifSpec + CryptoGames.SM.spec
      (PartyState Γ Pt RSt (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256)))
      (LibsignalMsgPublicPart × Plain ℓ) CCoins
      (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))) α}
    (hoa : oa.IsQueryBoundP
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
    (es : EState (VP Γ Pt (Option RSt) (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)))
      (LibsignalMsgPublicPart × Plain ℓ)
      (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (PRNGBucketAuthState Pt RSt (BitVec 256) I))
    (winEp : Option ℕ)
    (hInv : SMEngineInv L B_q q es.g)
    (hVR : SMVRInv (RSReachB maxForwardJumps) B_q q es.g) :
    (simulateQ (implPRNGBucketAuthGen hk₁ Δcka qep maxForwardJumps tL onlyNewForged) oa).run (es, winEp) =
      (simulateQ (implPRNGBucketAuthGen hk₂ Δcka qep maxForwardJumps tL onlyNewForged) oa).run (es, winEp) := by
  induction oa using OracleComp.inductionOn generalizing q es winEp with
  | pure _ => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind qy mx ih =>
    rw [isQueryBoundP_query_bind_iff] at hoa; rcases hoa with ⟨hq0, hmx⟩
    obtain ⟨hBad, hSendMx⟩ := badSendMsg_query_bind_step
      (fun (m : LibsignalMsgPublicPart × Plain ℓ) => atomicShortPubB m.1) qy mx hSendOk
    rw [simulateQ_query_bind, simulateQ_query_bind, StateT.run_bind, StateT.run_bind]
    have hLift : ∀ {M' : Type → Type} [Monad M'] {σ' α' : Type} (m : StateT σ' M' α') (s : σ'),
        (liftM m : StateT σ' M' α').run s = m.run s := fun _ _ => rfl
    rw [hLift, hLift]; simp only [OracleQuery.input_query, OracleQuery.cont_query]
    rw [implPRNGBucketAuthGen_run_eq_implE, implPRNGBucketAuthGen_run_eq_implE]
    simp only [bind_assoc, pure_bind]
    rcases qy with n | t_sm
    · simp only [ReductionDsl.isGameQuery, ↓reduceIte] at hmx
      have hInl1 : (implE hk₁ (2 + Δcka) qep maxForwardJumps (bucketAuthCfg Δcka tL) noDoomPolicy (.inl n)).run es =
          (coinsE n).run es := rfl
      have hInl2 : (implE hk₂ (2 + Δcka) qep maxForwardJumps (bucketAuthCfg Δcka tL) noDoomPolicy (.inl n)).run es =
          (coinsE n).run es := rfl
      rw [hInl1, hInl2]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, es'⟩ hmem => ?_
      simp only [coinsE, StateT.run_lift, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      obtain ⟨_, _, _, rfl⟩ := hmem
      exact ih u (hmx u) (hSendMx u) _ _ hInv hVR
    · simp only [ReductionDsl.isGameQuery, ↓reduceIte] at hq0 hmx
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by have := hq0.resolve_left (by decide); omega⟩
      rw [implE_bucketAuth_localFs_eq hAg hVRHk hB0 es t_sm hBad hVR]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, es'⟩ hmem =>
        ih u (by simpa using hmx u) (hSendMx u) es' _
          (implE_inv hk₂ (bucketAuthCfg Δcka tL) noDoomPolicy es t_sm hInv (u, es') hmem)
          (implE_vrInv hk₂ hVRHk (bucketAuthCfg Δcka tL) noDoomPolicy es t_sm hInv hVR (u, es') hmem)

private lemma hooksPRNGBucketAuthMain_vrInv_lFS
    {KC Γ CCoins Pt I KR RSt : Type} [DecidableEq Pt] [DecidableEq I] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) :
    HooksVRInv (RSReachB maxForwardJumps)
      (hooksPRNGBucketAuthMain cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
        Δcka qep tL t) where
  mono hle hv := hv.mono hle
  startRecv_step _ _ t0 γ0 _ tn0 h res hmem _ _ rs hEq := by
    unfold hooksPRNGBucketAuthMain at hmem
    dsimp only at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    split at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      rcases Prod.mk.inj hmem.symm with ⟨hres, _⟩
      rw [← hres, Option.some.injEq, Option.some.injEq] at hEq
      rcases Prod.mk.inj hEq with ⟨_, hEq2⟩
      rcases Prod.mk.inj hEq2 with ⟨_, rfl⟩
      exact Computational.Proofs.ReductionDsl.Fig8Atomic.RSReachB.init
        ((lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
        (lChainPRG C.F) maxForwardJumps _
    · split_ifs at hmem <;>
        (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
         rcases Prod.mk.inj hmem.symm with ⟨hres, _⟩
         rw [← hres] at hEq; cases hEq)
  fsRecv_step _ _ _ rs hdr e _ _ res hVR hmem _ _ _ hEq := by
    rcases res with ⟨ans, h'⟩; dsimp only at hEq; subst hEq
    unfold hooksPRNGBucketAuthMain hooksPRNGBucketAuthHybrid at hmem; dsimp only at hmem
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq, Option.some.injEq] at hmem
    exact (Computational.Proofs.ReductionDsl.Fig8Atomic.RSReachB.receive_fromAEADPRG
      ((lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
      (lChainPRG C.F) maxForwardJumps _ hVR hmem.1.symm).2
  commit_vR _ _ _ new _ res hmem new' hEq := by
    unfold hooksPRNGBucketAuthMain hooksPRNGBucketAuthHybrid at hmem; dsimp only at hmem
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rcases Prod.mk.inj hmem.symm with ⟨hres, _⟩
    rw [← hres, Option.some.injEq] at hEq; subst hEq; rfl

private lemma hooksPRNGBucketAuthForgedHdr_vrInv_lFS
    {KC Γ CCoins Pt I KR RSt : Type} [DecidableEq Pt] [DecidableEq I] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) :
    HooksVRInv (RSReachB maxForwardJumps)
      (hooksPRNGBucketAuthForgedHdr cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
        Δcka qep tL t) where
  mono hle hv := hv.mono hle
  startRecv_step ctx P t0 γ0 σ0 tn0 h res hmem γ' σ' rs hEq :=
    hooksPRNGBucketAuthHybrid_startRecv_rs cka prng
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka qep tL t
      (Computational.Proofs.ReductionDsl.Fig8Atomic.RSReachB.init
        ((lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
        (lChainPRG C.F) maxForwardJumps)
      ctx P t0 γ0 σ0 tn0 h res hmem γ' σ' rs hEq
  fsRecv_step _ _ _ rs hdr e _ _ res hVR hmem _ _ _ hEq := by
    rcases res with ⟨ans, h'⟩; dsimp only at hEq; subst hEq
    unfold hooksPRNGBucketAuthForgedHdr hooksPRNGBucketAuthHybrid at hmem; dsimp only at hmem
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq, Option.some.injEq] at hmem
    exact (Computational.Proofs.ReductionDsl.Fig8Atomic.RSReachB.receive_fromAEADPRG
      ((lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
      (lChainPRG C.F) maxForwardJumps _ hVR hmem.1.symm).2
  commit_vR _ _ _ new _ res hmem new' hEq := by
    unfold hooksPRNGBucketAuthForgedHdr hooksPRNGBucketAuthHybrid at hmem; dsimp only at hmem
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rcases Prod.mk.inj hmem.symm with ⟨hres, _⟩
    rw [← hres, Option.some.injEq] at hEq; subst hEq; rfl

private lemma hooksPRNGBucketAuthMain_localFsAgree
    {KC Γ CCoins Pt I KR RSt : Type} [DecidableEq Pt] [DecidableEq I] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (B0 Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) :
    HooksLocalFsAgree ℓ B0
      (hooksPRNGBucketAuthMain cka prng (fsAtomicB C ℓ encT idOf B0) Δcka qep tL t)
      (hooksPRNGBucketAuthMain cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
        Δcka qep tL t) where
  startSend_eq := by
    have hS : (fsAtomicB C ℓ encT idOf B0).initSender =
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initSender := rfl
    simp only [hooksPRNGBucketAuthMain, hooksPRNGBucketAuthHybrid, hS]
  startRecv_eq := by
    have hR : (fsAtomicB C ℓ encT idOf B0).initReceiver =
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initReceiver := rfl
    simp only [hooksPRNGBucketAuthMain, hR]
  fsSend_eq _ _ _ ss hdr m _ hm := by
    dsimp only [hooksPRNGBucketAuthMain, hooksPRNGBucketAuthHybrid]
    rw [fsAtomicB_send_eq C ℓ encT idOf B0 ss hdr m hm]
  fsRecv_eq _ _ _ rs hdr e _ hlen := by
    dsimp only [hooksPRNGBucketAuthMain, hooksPRNGBucketAuthHybrid]
    rw [fsAtomicB_receive_eq C ℓ encT idOf B0 rs hdr e hlen]
  commit_eq := by unfold hooksPRNGBucketAuthMain hooksPRNGBucketAuthHybrid; rfl
  reveal_eq := by unfold hooksPRNGBucketAuthMain hooksPRNGBucketAuthHybrid; rfl

private lemma hooksPRNGBucketAuthForgedHdr_localFsAgree
    {KC Γ CCoins Pt I KR RSt : Type} [DecidableEq Pt] [DecidableEq I] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (B0 Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) :
    HooksLocalFsAgree ℓ B0
      (hooksPRNGBucketAuthForgedHdr cka prng (fsAtomicB C ℓ encT idOf B0) Δcka qep tL t)
      (hooksPRNGBucketAuthForgedHdr cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
        Δcka qep tL t) where
  startSend_eq := by
    have hS : (fsAtomicB C ℓ encT idOf B0).initSender =
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initSender := rfl
    simp only [hooksPRNGBucketAuthForgedHdr, hooksPRNGBucketAuthHybrid, hS]
  startRecv_eq := by
    have hR : (fsAtomicB C ℓ encT idOf B0).initReceiver =
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initReceiver := rfl
    simp only [hooksPRNGBucketAuthForgedHdr, hooksPRNGBucketAuthHybrid, hR]
  fsSend_eq _ _ _ ss hdr m _ hm := by
    dsimp only [hooksPRNGBucketAuthForgedHdr, hooksPRNGBucketAuthHybrid]
    rw [fsAtomicB_send_eq C ℓ encT idOf B0 ss hdr m hm]
  fsRecv_eq _ _ _ rs hdr e _ hlen := by
    dsimp only [hooksPRNGBucketAuthForgedHdr, hooksPRNGBucketAuthHybrid]
    rw [fsAtomicB_receive_eq C ℓ encT idOf B0 rs hdr e hlen]
  commit_eq := by unfold hooksPRNGBucketAuthForgedHdr hooksPRNGBucketAuthHybrid; rfl
  reveal_eq := by unfold hooksPRNGBucketAuthForgedHdr hooksPRNGBucketAuthHybrid; rfl

private lemma runPRNGAuthBucketHybridGen_fsAtomicB_eq_lFS
    {KC Γ CCoins Pt I KR RSt : Type} [DecidableEq Pt] [DecidableEq I]
    [SampleableType KC] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : I) (B0 B_q Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) (onlyNewForged : Bool)
    (hk₁ : Hooks (CryptoGames.PRFPRNG.spec RSt I (BitVec 256))
      (PRNGBucketAuthState Pt RSt (BitVec 256) I) Γ Pt RSt
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
      CCoins Γ (Option RSt)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256)))
    (hk₂ : Hooks (CryptoGames.PRFPRNG.spec RSt I (BitVec 256))
      (PRNGBucketAuthState Pt RSt (BitVec 256) I) Γ Pt RSt
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
      CCoins Γ (Option RSt)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256)))
    (hAg : HooksLocalFsAgree ℓ B0 hk₁ hk₂)
    (hVRHk : HooksVRInv (RSReachB maxForwardJumps) hk₂)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (A : SchemeAdversary Γ Pt RSt
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) CCoins (ℕ × LibsignalCiphertextWithSalt32))
    (qAdv : ℕ) (hA : CryptoGames.SM.MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q)
    (hSendOk : CryptoGames.LibsignalSM.Proofs.SessionShort.SendMsgsOk (fun m => atomicShortPubB m.1) A) :
    runPRNGAuthBucketHybridGen cka prng (fsAtomicB C ℓ encT idOf B0) hk₁ lam Δcka qep tL t onlyNewForged A =
      runPRNGAuthBucketHybridGen cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) hk₂
        lam Δcka qep tL t onlyNewForged A := by
  have hA' : A.IsQueryBoundP
      (ReductionDsl.isGameQuery (G := CryptoGames.SM.spec
        (PartyState Γ Pt RSt (RatchetSenderState (BitVec 256))
          (RatchetReceiverState (BitVec 256) (BitVec 256)))
        (LibsignalMsgPublicPart × Plain ℓ) CCoins
        (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)))) qAdv := by
    refine hA.of_imp fun x hx => ?_
    rcases x with _ | _ <;> simp_all [ReductionDsl.isGameQuery]
  unfold runPRNGAuthBucketHybridGen
  have hS : (fsAtomicB C ℓ encT idOf B0).initSender =
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initSender := rfl
  have hR : (fsAtomicB C ℓ encT idOf B0).initReceiver =
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initReceiver := rfl
  have hInitEq :
      initPRNGBucketAuthHybrid cka prng (fsAtomicB C ℓ encT idOf B0) lam tL t =
        initPRNGBucketAuthHybrid cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam tL t := by
    simp only [initPRNGBucketAuthHybrid, hS, hR]
  rw [hInitEq]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨vs, h⟩ hmem => ?_
  rcases vs with _ | ⟨vA, vB⟩
  · rfl
  · let es₀ : EState (VP Γ Pt (Option RSt) (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256)))
        (LibsignalMsgPublicPart × Plain ℓ)
        (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
        (PRNGBucketAuthState Pt RSt (BitVec 256) I) :=
      { g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := h }
    have hInv₀ : SMEngineInv (B_q + 1) B_q qAdv es₀.g :=
      (CryptoGames.SM.Engine.SMEngineInv.init _ false le_rfl
        (Nat.mul_le_mul (Nat.le_succ _) (Nat.le_succ _))).mono hqB
    have hVR₀ : SMVRInv (RSReachB maxForwardJumps) B_q qAdv es₀.g := by
      intro P t₀ v hv
      unfold initPRNGBucketAuthHybrid at hmem
      simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, mem_support_bind_iff] at hmem
      obtain ⟨kc, _, ⟨rtRes, _⟩, _, hmem⟩ := hmem
      rcases rtRes with _ | ⟨σ, k⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        cases hmem.1
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
          Option.some.injEq] at hmem
        rcases Prod.mk.inj hmem.1.symm with ⟨rfl, rfl⟩
        cases P <;> simp only [es₀] at hv
        · split_ifs at hv with ht0
          · cases hv
            exact hVRHk.mono (Nat.zero_le _)
              (Computational.Proofs.ReductionDsl.Fig8Atomic.RSReachB.init
                ((lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
                (lChainPRG C.F) maxForwardJumps k)
        · cases hv
    have hms1 : (fsAtomicB C ℓ encT idOf B0).maxSkip = maxForwardJumps := rfl
    have hms2 : (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip = maxForwardJumps := rfl
    rw [hms1, hms2]
    dsimp only
    exact congrArg (· >>= fun res => pure (some res))
      (simulateQ_implPRNGBucketAuthGen_localFs_eq hAg hVRHk hB0 hA' hSendOk es₀ none hInv₀ hVR₀)

theorem redPRNGAuthBucketHybrid_fsAtomicB_eq_lFS
    {KC Γ CCoins Pt I KR RSt : Type} [DecidableEq Pt] [DecidableEq I]
    [SampleableType KC] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : I) (B0 B_q Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (A : SchemeAdversary Γ Pt RSt
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) CCoins (ℕ × LibsignalCiphertextWithSalt32))
    (qAdv : ℕ) (hA : CryptoGames.SM.MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q)
    (hSendOk : CryptoGames.LibsignalSM.Proofs.SessionShort.SendMsgsOk (fun m => atomicShortPubB m.1) A) :
    redPRNGAuthBucketHybrid cka prng (fsAtomicB C ℓ encT idOf B0) lam Δcka qep tL t A =
      redPRNGAuthBucketHybrid cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
        lam Δcka qep tL t A := by
  unfold redPRNGAuthBucketHybrid redPRNGAuthBucketHybridForgedHdr redPRNGAuthBucketHybridMain
  refine bind_congr fun forgedMode => ?_
  cases forgedMode
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [runPRNGAuthBucketHybridGen_fsAtomicB_eq_lFS cka prng C ℓ encT idOf lam B0 B_q Δcka qep tL t false
      (hooksPRNGBucketAuthMain cka prng (fsAtomicB C ℓ encT idOf B0) Δcka qep tL t)
      (hooksPRNGBucketAuthMain cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka qep tL t)
      (hooksPRNGBucketAuthMain_localFsAgree cka prng C ℓ encT idOf B0 Δcka qep tL t)
      (hooksPRNGBucketAuthMain_vrInv_lFS cka prng C ℓ encT idOf Δcka qep tL t)
      hB0 A qAdv hA hqB hSendOk]
  · simp only [↓reduceIte]
    rw [runPRNGAuthBucketHybridGen_fsAtomicB_eq_lFS cka prng C ℓ encT idOf lam B0 B_q Δcka qep tL t true
      (hooksPRNGBucketAuthForgedHdr cka prng (fsAtomicB C ℓ encT idOf B0) Δcka qep tL t)
      (hooksPRNGBucketAuthForgedHdr cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka qep tL t)
      (hooksPRNGBucketAuthForgedHdr_localFsAgree cka prng C ℓ encT idOf B0 Δcka qep tL t)
      (hooksPRNGBucketAuthForgedHdr_vrInv_lFS cka prng C ℓ encT idOf Δcka qep tL t)
      hB0 A qAdv hA hqB hSendOk]

private lemma hooksPRNGBucketAuthHybrid_startSend_localCKA
    {Pt KR RSt K SS RS M E : Type} [DecidableEq Pt] [Zero Pt] [SampleableType K]
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E) (Δcka qep : ℕ) (tL : Option ℕ) (t0 : ℕ)
    (ctx : Ctx (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (Option RSt) SS RS M E)
    (P : Party) (t : ℕ) (γ : CryptoGames.CKA.DDH.State (BitVec 256) Pt) (σv : Option RSt)
    (r : Option (BitVec 256)) (h : PRNGBucketAuthState Pt RSt K Pt)
    (ht : 1 ≤ t) (hSend : P.sendsIn t = true) (hRole : DdhRoleOk P (t - 1) γ) :
    ((hooksPRNGBucketAuthHybrid (dhSchemeFb Dh) prng fs Δcka qep tL t0).startSend ctx P t γ σv r).run h =
      ((hooksPRNGBucketAuthHybrid (dhScheme Dh) prng fs Δcka qep tL t0).startSend ctx P t γ σv r).run h ∧
    ∀ q ∈ support (((hooksPRNGBucketAuthHybrid (dhScheme Dh) prng fs Δcka qep tL t0).startSend
        ctx P t γ σv r).run h),
      ∀ γ' T' σ' ss, q.1 = some (γ', T', σ', ss) → DdhRoleOk P t γ' := by
  have ht1 : (t - 1) + 1 = t := Nat.sub_add_cancel ht
  have hSend' : P.sendsIn ((t - 1) + 1) = true := ht1.symm ▸ hSend
  dsimp only [hooksPRNGBucketAuthHybrid]
  have hCoins : ∀ coins : BitVec 256,
      (do
        let rtRes ← rootPRNGBucketAuthHybrid prng tL t0 t (postLeak tL ctx)
          ((dhSchemeFb Dh).send γ coins).2.2 σv
        match rtRes with
        | none => pure none
        | some (σ', k) => do
          modify fun (s : PRNGBucketAuthState Pt RSt K Pt) =>
            { s with cache := Function.update s.cache t (some (((dhSchemeFb Dh).send γ coins).2.1, σ', k)) }
          pure (some (((dhSchemeFb Dh).send γ coins).1, ((dhSchemeFb Dh).send γ coins).2.1, σ', fs.initSender k))).run h =
      (do
        let rtRes ← rootPRNGBucketAuthHybrid prng tL t0 t (postLeak tL ctx)
          ((dhScheme Dh).send γ coins).2.2 σv
        match rtRes with
        | none => pure none
        | some (σ', k) => do
          modify fun (s : PRNGBucketAuthState Pt RSt K Pt) =>
            { s with cache := Function.update s.cache t (some (((dhScheme Dh).send γ coins).2.1, σ', k)) }
          pure (some (((dhScheme Dh).send γ coins).1, ((dhScheme Dh).send γ coins).2.1, σ', fs.initSender k))).run h ∧
      ∀ q ∈ support ((do
        let rtRes ← rootPRNGBucketAuthHybrid prng tL t0 t (postLeak tL ctx)
          ((dhScheme Dh).send γ coins).2.2 σv
        match rtRes with
        | none => pure none
        | some (σ', k) => do
          modify fun (s : PRNGBucketAuthState Pt RSt K Pt) =>
            { s with cache := Function.update s.cache t (some (((dhScheme Dh).send γ coins).2.1, σ', k)) }
          pure (some (((dhScheme Dh).send γ coins).1, ((dhScheme Dh).send γ coins).2.1, σ', fs.initSender k))).run h),
        ∀ γ' T' σ' ss, q.1 = some (γ', T', σ', ss) → DdhRoleOk P t γ' := by
    intro coins
    have hsnd := dhSchemeFb_send_of_roleOk Dh hRole hSend' coins
    have hRole' : DdhRoleOk P t ((dhScheme Dh).send γ coins).1 := ht1 ▸ hsnd.2
    simp only [hsnd.1]
    refine ⟨trivial, fun q hq γ' T' σ' ss hEq => ?_⟩
    rw [StateT.run_bind, mem_support_bind_iff] at hq
    obtain ⟨⟨rtRes, h₂⟩, _, hq⟩ := hq
    rcases rtRes with _ | ⟨σ₁, k₁⟩ <;>
      (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
         support_pure, Set.mem_singleton_iff] at hq
       subst hq; cases hEq)
    exact hRole'
  rcases r with _ | c
  · simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
    refine ⟨bind_congr fun coins => (hCoins coins).1, fun q hq γ' T' σ' ss hEq => ?_⟩
    rw [mem_support_bind_iff] at hq
    obtain ⟨coins, _, hq⟩ := hq
    exact (hCoins coins).2 q hq γ' T' σ' ss hEq
  · simp only [pure_bind]
    exact hCoins c

private lemma hooksPRNGBucketAuthMain_localCKAAgree
    {Pt KR RSt K SS RS M E : Type} [DecidableEq Pt] [Zero Pt] [SampleableType K]
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E) (Δcka qep : ℕ) (tL : Option ℕ) (t0 : ℕ) :
    HooksLocalCKAAgree (fun P γ t => DdhRoleOk P t γ)
      (hooksPRNGBucketAuthMain (dhSchemeFb Dh) prng fs Δcka qep tL t0)
      (hooksPRNGBucketAuthMain (dhScheme Dh) prng fs Δcka qep tL t0) where
  startSend_eq ctx P t γ σv r h ht hSend hRole :=
    hooksPRNGBucketAuthHybrid_startSend_localCKA Dh prng fs Δcka qep tL t0 ctx P t γ σv r h ht hSend hRole
  startRecv_eq ctx P t γ σv Tn h ht hRecv hRole := by
    have ht1 : (t - 1) + 1 = t := Nat.sub_add_cancel ht
    have hRecv' : P.sendsIn ((t - 1) + 1) = false := ht1.symm ▸ hRecv
    have hrcv := dhSchemeFb_receive_of_roleOk Dh hRole hRecv' Tn
    have hRole' : DdhRoleOk P t ((dhScheme Dh).receive γ Tn).1 := ht1 ▸ hrcv.2
    dsimp only [hooksPRNGBucketAuthMain]
    simp only [hrcv.1]
    refine ⟨trivial, fun q hq γ' σ' rs hEq => ?_⟩
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hq
    split at hq
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hq
      subst hq; cases hEq; exact hRole'
    · split_ifs at hq <;>
        (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hq
         subst hq; cases hEq)
  fsSend_eq := rfl
  fsRecv_eq := rfl
  commit_eq _ _ _ _ := ⟨rfl, rfl⟩
  reveal_eq := rfl

private lemma hooksPRNGBucketAuthForgedHdr_localCKAAgree
    {Pt KR RSt K SS RS M E : Type} [DecidableEq Pt] [Zero Pt] [SampleableType K]
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E) (Δcka qep : ℕ) (tL : Option ℕ) (t0 : ℕ) :
    HooksLocalCKAAgree (fun P γ t => DdhRoleOk P t γ)
      (hooksPRNGBucketAuthForgedHdr (dhSchemeFb Dh) prng fs Δcka qep tL t0)
      (hooksPRNGBucketAuthForgedHdr (dhScheme Dh) prng fs Δcka qep tL t0) where
  startSend_eq ctx P t γ σv r h ht hSend hRole :=
    hooksPRNGBucketAuthHybrid_startSend_localCKA Dh prng fs Δcka qep tL t0 ctx P t γ σv r h ht hSend hRole
  startRecv_eq ctx P t γ σv Tn h ht hRecv hRole := by
    have ht1 : (t - 1) + 1 = t := Nat.sub_add_cancel ht
    have hRecv' : P.sendsIn ((t - 1) + 1) = false := ht1.symm ▸ hRecv
    have hrcv := dhSchemeFb_receive_of_roleOk Dh hRole hRecv' Tn
    have hRole' : DdhRoleOk P t ((dhScheme Dh).receive γ Tn).1 := ht1 ▸ hrcv.2
    dsimp only [hooksPRNGBucketAuthForgedHdr, hooksPRNGBucketAuthHybrid]
    simp only [hrcv.1]
    refine ⟨trivial, fun q hq γ' σ' rs hEq => ?_⟩
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hq
    split at hq
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hq
      subst hq; cases hEq; exact hRole'
    · by_cases hAdmiss : (!decide (qep + 1 < t) && CryptoGames.SM.lastLeakGuessAdmissible (2 + Δcka) tL t) = true
      · simp only [hAdmiss, ↓reduceIte] at hq
        by_cases htH : (tL.isSome && decide (t = CryptoGames.SM.Construction.healEpoch tL)) = true
        · simp only [htH, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hq
          subst hq; cases hEq
        · simp only [htH, Bool.false_eq_true, ↓reduceIte] at hq
          by_cases hPl : (postLeak tL ctx || h.corrRoot.isSome || decide (t0 < t)) = true
          · simp only [hPl, ↓reduceIte] at hq
            rcases hrc : resolveCorrRoot h (t - 1) σv with _ | σ <;>
              (simp only [hrc, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hq
               subst hq; cases hEq)
            exact hRole'
          · simp only [hPl, Bool.false_eq_true, ↓reduceIte] at hq
            by_cases htEq : t = t0
            · simp only [htEq, ↓reduceIte, StateT.run_bind, mem_support_bind_iff] at hq
              obtain ⟨⟨qOut, h1⟩, _, hq⟩ := hq
              rcases qOut with _ | ⟨σOut, kOut⟩ <;>
                (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hq
                 subst hq; cases hEq)
              exact hRole'
            · simp only [htEq, ↓reduceIte] at hq
              by_cases hGeH : (!decide (t < CryptoGames.SM.Construction.healEpoch tL)) = true
              · simp only [hGeH, ↓reduceIte, StateT.run_bind, mem_support_bind_iff] at hq
                obtain ⟨⟨kLookup, h1⟩, _, hq⟩ := hq
                simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hq
                subst hq; cases hEq; exact hRole'
              · simp only [hGeH, Bool.false_eq_true, ↓reduceIte,
                  StateT.run_pure, support_pure, Set.mem_singleton_iff] at hq
                subst hq; cases hEq
      · simp only [hAdmiss, Bool.false_eq_true, ↓reduceIte,
          StateT.run_pure, support_pure, Set.mem_singleton_iff] at hq
        subst hq; cases hEq
  fsSend_eq := rfl
  fsRecv_eq := rfl
  commit_eq _ _ _ _ := ⟨rfl, rfl⟩
  reveal_eq := rfl

private lemma simulateQ_implPRNGBucketAuthGen_localCKA_eq
    {Pt RSt K SS RS M E α : Type} [DecidableEq Pt] [DecidableEq M] [DecidableEq E] [Inhabited E]
    {hk₁ hk₂ : Hooks (CryptoGames.PRFPRNG.spec RSt Pt K) (PRNGBucketAuthState Pt RSt K Pt)
      (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt SS RS M E (BitVec 256)
      (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (Option RSt) SS RS}
    (hAg : HooksLocalCKAAgree (fun P γ t => DdhRoleOk P t γ) hk₁ hk₂)
    (Δcka qep maxSkip : ℕ) (tL : Option ℕ) (onlyNewForged : Bool)
    (oa : OracleComp (unifSpec + CryptoGames.SM.spec
      (PartyState (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt SS RS) M (BitVec 256)
      (Header Pt × E)) α)
    (es : EState (VP (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (Option RSt) SS RS)
      M (Header Pt × E) (PRNGBucketAuthState Pt RSt K Pt))
    (winEp : Option ℕ) (hEs : AllPartiesInv es) :
    (simulateQ (implPRNGBucketAuthGen hk₁ Δcka qep maxSkip tL onlyNewForged) oa).run (es, winEp) =
      (simulateQ (implPRNGBucketAuthGen hk₂ Δcka qep maxSkip tL onlyNewForged) oa).run (es, winEp) := by
  induction oa using OracleComp.inductionOn generalizing es winEp with
  | pure _ => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind qy mx ih =>
    rw [simulateQ_query_bind, simulateQ_query_bind, StateT.run_bind, StateT.run_bind]
    have hLift : ∀ {M' : Type → Type} [Monad M'] {σ' α' : Type} (m : StateT σ' M' α') (s : σ'),
        (liftM m : StateT σ' M' α').run s = m.run s := fun _ _ => rfl
    rw [hLift, hLift]; simp only [OracleQuery.input_query, OracleQuery.cont_query]
    rw [implPRNGBucketAuthGen_run_eq_implE, implPRNGBucketAuthGen_run_eq_implE]
    simp only [bind_assoc, pure_bind]
    rcases qy with n | t_sm
    · have hInl1 : (implE hk₁ (2 + Δcka) qep maxSkip (bucketAuthCfg Δcka tL) noDoomPolicy (.inl n)).run es =
          (coinsE n).run es := rfl
      have hInl2 : (implE hk₂ (2 + Δcka) qep maxSkip (bucketAuthCfg Δcka tL) noDoomPolicy (.inl n)).run es =
          (coinsE n).run es := rfl
      rw [hInl1, hInl2]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, es'⟩ hmem => ?_
      simp only [coinsE, StateT.run_lift, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      obtain ⟨_, _, _, rfl⟩ := hmem
      exact ih u _ _ hEs
    · have hStep := implE_localCKA_eq hAg (2 + Δcka) qep maxSkip (bucketAuthCfg Δcka tL) noDoomPolicy es t_sm hEs
      rw [hStep.1]
      exact OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, es'⟩ hmem =>
        ih u es' _ (hStep.2 (u, es') hmem)

theorem redPRNGAuthBucketHybrid_dhSchemeFb_eq
    {Pt KR RSt K SS RS M E : Type} [DecidableEq Pt] [Zero Pt] [DecidableEq M] [DecidableEq E]
    [Inhabited E] [SampleableType K]
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E) (lam : Pt) (Δcka qep : ℕ)
    (tL : Option ℕ) (t0 : ℕ)
    (A : SchemeAdversary (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt SS RS M (BitVec 256) E) :
    redPRNGAuthBucketHybrid (dhSchemeFb Dh) prng fs lam Δcka qep tL t0 A =
      redPRNGAuthBucketHybrid (dhScheme Dh) prng fs lam Δcka qep tL t0 A := by
  have hGen : ∀ (hk₁ hk₂ : Hooks (CryptoGames.PRFPRNG.spec RSt Pt K) (PRNGBucketAuthState Pt RSt K Pt)
      (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt SS RS M E (BitVec 256)
      (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (Option RSt) SS RS) (onlyNewForged : Bool),
      HooksLocalCKAAgree (fun P γ t => DdhRoleOk P t γ) hk₁ hk₂ →
      runPRNGAuthBucketHybridGen (dhSchemeFb Dh) prng fs hk₁ lam Δcka qep tL t0 onlyNewForged A =
        runPRNGAuthBucketHybridGen (dhScheme Dh) prng fs hk₂ lam Δcka qep tL t0 onlyNewForged A := by
    intro hk₁ hk₂ onlyNewForged hAg
    unfold runPRNGAuthBucketHybridGen
    have hInit : initPRNGBucketAuthHybrid (dhSchemeFb Dh) prng fs lam tL t0 =
        initPRNGBucketAuthHybrid (dhScheme Dh) prng fs lam tL t0 := rfl
    rw [hInit]
    refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨vs, h⟩ hmem => ?_
    rcases vs with _ | ⟨vA, vB⟩
    · rfl
    · have hAll : AllPartiesInv (M := M) (E := E) (HS := PRNGBucketAuthState Pt RSt K Pt)
          { g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := h } := by
        unfold initPRNGBucketAuthHybrid at hmem
        simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, mem_support_bind_iff] at hmem
        obtain ⟨kc, _, ⟨rtRes, _⟩, _, hmem⟩ := hmem
        rcases rtRes with _ | ⟨σ, k⟩
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          cases hmem.1
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
            Option.some.injEq] at hmem
          rcases Prod.mk.inj hmem.1.symm with ⟨rfl, rfl⟩
          intro P; cases P
          · exact ⟨rfl, ddhRoleOk_initA Dh kc⟩
          · exact ⟨rfl, ddhRoleOk_initB Dh kc⟩
      dsimp only
      exact congrArg (· >>= fun res => pure (some res))
        (simulateQ_implPRNGBucketAuthGen_localCKA_eq hAg Δcka qep fs.maxSkip tL onlyNewForged A _ none hAll)
  unfold redPRNGAuthBucketHybrid redPRNGAuthBucketHybridForgedHdr redPRNGAuthBucketHybridMain
  refine bind_congr fun forgedMode => ?_
  cases forgedMode
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hGen _ _ false (hooksPRNGBucketAuthMain_localCKAAgree Dh prng fs Δcka qep tL t0)]
  · simp only [↓reduceIte]
    rw [hGen _ _ true (hooksPRNGBucketAuthForgedHdr_localCKAAgree Dh prng fs Δcka qep tL t0)]

theorem redPRNGAuthBucketHybrid_atomic_eq
    {Pt KR RSt : Type} [DecidableEq Pt] [Zero Pt]
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (B0 B_q Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (A : SchemeAdversary (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (ℕ × LibsignalCiphertextWithSalt32))
    (qAdv : ℕ) (hA : CryptoGames.SM.MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q)
    (hSendOk : CryptoGames.LibsignalSM.Proofs.SessionShort.SendMsgsOk (fun m => atomicShortPubB m.1) A) :
    redPRNGAuthBucketHybrid (dhSchemeFb Dh) prng (fsAtomicB C ℓ encT idOf B0) lam Δcka qep tL t A =
      redPRNGAuthBucketHybrid (dhScheme Dh) prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
        lam Δcka qep tL t A := by
  rw [redPRNGAuthBucketHybrid_dhSchemeFb_eq Dh prng (fsAtomicB C ℓ encT idOf B0) lam Δcka qep tL t A,
    redPRNGAuthBucketHybrid_fsAtomicB_eq_lFS (dhScheme Dh) prng C ℓ encT idOf lam B0 B_q Δcka qep
      tL t hB0 A qAdv hA hqB hSendOk]

end PRNGAtomicSwap

end

end Computational.Proofs.SessionCostedFig8.BucketPRNGSwap
