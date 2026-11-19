/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.HeadlineV1.DeliverForgePaperMultiPotOK -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.DFProgFsStage2Defs
public import Computational.Proofs.SessionCostedFig8.DFProgBucketBounds -- proof-setup: allow-public-import
import Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedPotOK
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGPotOK
import Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks

/-!
# Bucket & Atomic Stage-2 Query Bounds for Paper `DeliverForge` Reductions (`[B7]` × `[B8]`)

Establishes per-session `2 * q` query bounds on `redFSAuthDFPaperMultiBucketProg`
and lifts the shallow Stage-2 query bounds across `compileFsMultiDFAtomic`, `compileFsDFAtomic`,
and `compilePrngDFAtomic`.-/

set_option autoImplicit false

open Computational.Proofs.HeadlineV1.DeliverForgePaperMultiPotOK (HooksPotSpec bkPot bkPot_eq_one_of_get_false bkPot_le_one costedReduction_multi_isQueryBoundP costedReduction_multi_isQueryBoundP_min deliverEC_gen_potOKInv deliverForgeEC_gen_potOKInv esPot injectEC_gen_potOKInv ite_eq_proj_book mbHPot multiIface_fwdU_zero potInvMultiFS_query potInvMultiFS_zero redFSAuthDFPaperMultiProg_sess_isQueryBoundP_of_eq redFSAuthDFPaperMultiProg_sess_isQueryBoundP_of_eq_min redFSAuthDFShiftedPaperMultiGenProg_sess_isQueryBoundP_of_eq redFSAuthDFShiftedPaperMultiGenProg_sess_isQueryBoundP_of_eq_min sessPred vSendC_gen_potOKInv)
open Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2 (redFSAuthDFShiftedDir2PaperMultiProg redFSAuthDFShiftedPaperMultiProg)
open Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks (PotOKInvFS potInvFS_caseOpt potInvFS_caseSum potInvFS_ite potInvFS_ret)
open Computational.Proofs.SessionCostedFig8.BundlesMultiFs (compileFsMultiDFAtomic_makesAtMostQueries)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun ckaHdrCtTy ckaHdrTy)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey maxForwardJumps)
open CryptoGames.PRFPRNG (prngOps prngSMCodecDF prngSig)
open CryptoGames.Ratchet.LibsignalSim (Fig8C Fig8St)
open CryptoGames.SM.Construction (Header PartyState fsMultiDFBucketCommitC fsMultiDFBucketEsTy fsMultiDFBucketFsRecvC fsMultiDFBucketFsSendC fsMultiDFBucketHsBook fsMultiDFBucketHsGetBookAt fsMultiDFBucketHsMk fsMultiDFBucketHsSetBookAt fsMultiDFBucketHsSetCache fsMultiDFBucketHsSetLfWin fsMultiDFBucketHsSetSessionsAt fsMultiDFBucketHsSetTableAt fsMultiDFBucketHsTy bucketModeHandleDFPaperC fsMultiDFBucketForgedHdrRevealC fsMultiDFBucketModeRevealC fsMultiDFBucketPaperFsRecvC fsMultiDFBucketPaperMainStartRecvC fsMultiDFBucketPaperModeStartRecvC fsMultiDFBucketPaperStartRecvC fsMultiDFBucketPaperStartSendC fsMultiDFBucketRevealC hooksFSMultiDFBucketPaperModeC redFSAuthDFPaperMultiBucketModeProgGen fsMultiEsTy fsMultiHsTy fsMultiSessBookTy fsMultiVpTy fsaeadMultiHeaderAdIface hooksFSMultiDFBucketPaperC initFSMultiDFBucketPaperEStateC_queries lookupMultiDFBucketFC postLeakDFBucketE rangeListC_multiDF_queries redFSAuthDFPaperMultiBucketModeProg redFSAuthDFPaperMultiBucketModeProg_totalQueries redFSAuthDFPaperMultiBucketProg redFSAuthDFPaperMultiBucketProgGen redFSAuthDFPaperMultiBucketProg_totalQueries redFSAuthDFPaperMultiProg regSessMultiDFBucketE regSessOptMultiDFBucketE rootFSMultiDFBucketPaperC)
open CryptoGames.SM.Engine (cGsTy cRecTy esMk eval_bind eval_bind_ret)
open ReductionDsl (CostedReduction Env Expr Ty)

namespace Computational.Proofs.HeadlineV1.DeliverForgePaperMultiBucketPotOK

public section

section MultiBucketPotOK

open OracleSpec OracleComp

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}
  {ckaInitA : KC → Γ} {ckaInitB : KC → Γ}
  {ckaSend : Γ → CCoins → Γ × T × I} {ckaReceive : Γ → T → Γ × I}
  {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS} {fsInitReceiver : K → RS}
  {fsSend : SS → Header T → M → SS × E}
  {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
  {lam : I} {defaultE : E}
  {sampKR : ProbComp KR} {sampKC : ProbComp KC} {sampCCoins : ProbComp CCoins}
  {sampI : ProbComp I} {sampK : ProbComp K}

local notation "SP" => prngSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "OO" =>
  prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE
local notation "IIM" =>
  fsaeadMultiHeaderAdIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK
local notation "hdrTy" => ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrCtTy" => ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "mVpTy" => fsMultiVpTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "mHsTy" => fsMultiHsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "mEsTy" => fsMultiEsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "mBookTy" => fsMultiSessBookTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "mbHsTy" => fsMultiDFBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "mbEsTy" => fsMultiDFBucketEsTy KC Γ CCoins T I KR RSt K SS RS M E


private theorem regSessMultiDFBucketE_book (L : ℕ) (tL : Option ℕ) {Γ' : List (Ty SP)}
    (hE : Expr OO Γ' mbHsTy) (tE : Expr OO Γ' .nat) (ikE : Expr OO Γ' (.base .i)) (ρ : Env Γ') :
    ((regSessMultiDFBucketE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) L tL hE tE ikE).eval ρ).2.2.2.2.1 = (hE.eval ρ).2.2.2.1 := by
  simp only [regSessMultiDFBucketE, fsMultiDFBucketHsSetSessionsAt, fsMultiDFBucketHsMk,
    fsMultiDFBucketHsBook, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero]
  exact ite_eq_proj_book _ _ rfl rfl

private theorem regSessOptMultiDFBucketE_book (L : ℕ) (tL : Option ℕ) {Γ' : List (Ty SP)}
    (hE : Expr OO Γ' mbHsTy) (tE : Expr OO Γ' .nat) (sidE : Expr OO Γ' (.opt (.base .i))) (ρ : Env Γ') :
    ((regSessOptMultiDFBucketE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) L tL hE tE sidE).eval ρ).2.2.2.2.1 = (hE.eval ρ).2.2.2.1 := by
  simp only [regSessOptMultiDFBucketE, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero]
  cases h : sidE.eval ρ with
  | none => rfl
  | some ik =>
    have hSub := regSessMultiDFBucketE_book L tL (.fst (ReductionDsl.Expr.v1 (O := OO))) (.fst (.snd .v1)) .v0
      (.cons ik (.cons ((hE.pair (tE.pair sidE)).eval ρ) ρ))
    simpa [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, ReductionDsl.Env.get_cons_zero, ReductionDsl.Env.get_cons_succ, h] using hSub

private theorem lookupMultiDFBucketFC_potOKInv (j L : ℕ) {Γ' : List (Ty SP)}
    (hE : Expr OO Γ' mbHsTy) (tE : Expr OO Γ' .nat) (ikE : Expr OO Γ' (.base .i)) (ρ : Env Γ') (m : ℕ) :
    PotOKInvFS (sessPred j) (fun _ => True) (fun res => m + mbHPot j res.2)
      ((lookupMultiDFBucketFC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L hE tE ikE).eval ρ) (m + mbHPot j (hE.eval ρ)) := by
  unfold lookupMultiDFBucketFC; rw [eval_bind_ret]
  refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => potInvFS_ret trivial (by simp [mbHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v1]))
  rw [eval_bind]
  exact Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot
    (potInvMultiFS_zero j _ _ (m + mbHPot j (hE.eval ρ)) (fun _ => Nat.le_refl _) rfl)
    (fun _ _ => potInvFS_ret trivial
      (by simp [mbHPot, fsMultiDFBucketHsSetTableAt, fsMultiDFBucketHsMk, fsMultiDFBucketHsBook, ReductionDsl.Expr.eval, ReductionDsl.Expr.v1]))

private theorem rootFSMultiDFBucketPaperC_potOKInv (j L Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool)
    {Γ' : List (Ty SP)} (hE : Expr OO Γ' mbHsTy) (tE : Expr OO Γ' .nat) (plE : Expr OO Γ' .bool)
    (ikE : Expr OO Γ' (.base .i)) (σE : Expr OO Γ' (.base .sig)) (ρ : Env Γ') (m : ℕ) :
    PotOKInvFS (sessPred j) (fun _ => True) (fun res => m + mbHPot j res.2)
      ((rootFSMultiDFBucketPaperC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L Δbucket qep tL par hE tE plE ikE σE).eval ρ) (m + mbHPot j (hE.eval ρ)) := by
  unfold rootFSMultiDFBucketPaperC; rw [eval_bind_ret]
  refine potInvFS_ite (fun _ => potInvFS_ret trivial (by simp [mbHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))
    (fun _ => potInvFS_ite (fun _ => potInvFS_ite (fun _ => ?_) (fun _ => ?_))
      (fun _ => potInvFS_ite (fun _ => ?_)
        (fun _ => potInvFS_ret trivial (by simp [mbHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))))
  · rw [eval_bind]
    refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot
      (potInvMultiFS_zero j _ _ (m + mbHPot j (hE.eval ρ)) (fun _ => Nat.le_refl _) rfl) (fun _ _ => ?_)
    rw [eval_bind]
    exact Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot
      (potInvMultiFS_zero j _ _ (m + mbHPot j (hE.eval ρ)) (fun _ => Nat.le_refl _) rfl)
      (fun _ _ => potInvFS_ret trivial (by simp [mbHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v2]))
  · rw [eval_bind]
    have hL := lookupMultiDFBucketFC_potOKInv (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) j L (.fst (ReductionDsl.Expr.v0 (O := OO))) (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))
      (.cons ((hE.pair (tE.pair (ikE.pair (σE.pair plE)))).eval ρ) ρ) m
    simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero] at hL
    exact Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot hL (fun _ _ => potInvFS_ret trivial (by simp [mbHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))
  · rw [eval_bind]
    refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot
      (potInvMultiFS_zero j _ _ (m + mbHPot j (hE.eval ρ)) (fun _ => Nat.le_refl _) rfl) (fun _ _ => ?_)
    rw [eval_bind]
    exact Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot
      (potInvMultiFS_zero j _ _ (m + mbHPot j (hE.eval ρ)) (fun _ => Nat.le_refl _) rfl)
      (fun _ _ => potInvFS_ret trivial (by simp [mbHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v2]))

private theorem fsMultiDFBucketFsSendC_potOKInv (j Δcka : ℕ) (la : Bool) {Γ' : List (Ty SP)}
    (hE : Expr OO Γ' mbHsTy) (ctxE : Expr OO Γ' (cGsTy mVpTy)) (pE : Expr OO Γ' .bool)
    (tE : Expr OO Γ' .nat) (ssvE : Expr OO Γ' (.sum (.base .ss) .nat)) (hdrE : Expr OO Γ' hdrTy)
    (mE : Expr OO Γ' (.base .msg)) (pairE : Expr OO Γ' (.opt (.prod (.base .msg) (.base .msg))))
    (ρ : Env Γ') (m : ℕ) :
    PotOKInvFS (sessPred j) (fun _ => True) (fun res => m + mbHPot j res.2)
      ((fsMultiDFBucketFsSendC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) Δcka la hE ctxE pE tE ssvE hdrE mE pairE).eval ρ)
      (1 + m + mbHPot j (hE.eval ρ)) := by
  unfold fsMultiDFBucketFsSendC; rw [eval_bind_ret]
  refine potInvFS_caseSum
    (fun _ _ => potInvFS_ret trivial (by simp only [mbHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v1, ReductionDsl.Env.get_cons_succ, ReductionDsl.Env.get_cons_zero]; omega))
    (fun sIdx _ => ?_)
  rw [eval_bind]
  refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot (Inv₁ := fun _ => True)
    (B₁ := fun oh => (if oh.1 then 1 else 0) + m + mbHPot j oh.2) ?_ (fun oh _ => ?_)
  · refine potInvFS_ite (fun hCond => ?_) (fun _ => ?_)
    · rw [eval_bind]
      have hCorrF : ((match (hE.eval ρ).2.2.2.1 sIdx with | none => (false, (0, [])) | some b => b : (mBookTy).denote)).1 = false := by
        simp only [fsMultiDFBucketHsGetBookAt, fsMultiDFBucketHsBook, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1,
          ReductionDsl.Env.get_cons_zero, ReductionDsl.Env.get_cons_succ, Bool.and_eq_true, Bool.not_eq_true'] at hCond
        cases hB : (hE.eval ρ).2.2.2.1 sIdx <;> simp [hB] at hCond ⊢; exact hCond.2
      refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot
        (potInvMultiFS_query j _ _ _ ((if sIdx = j then 0 else 1) + m + mbHPot j (hE.eval ρ))
          (1 + m + mbHPot j (hE.eval ρ)) (by simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero]; split <;> omega))
        (fun _ _ => ?_)
      refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => ?_)
      · exact potInvFS_ret trivial (by simp [mbHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v2])
      · refine potInvFS_ret trivial ?_
        simp only [mbHPot, fsMultiDFBucketHsSetBookAt, fsMultiDFBucketHsMk, fsMultiDFBucketHsBook,
          fsMultiDFBucketHsGetBookAt, ReductionDsl.Expr.eval, ReductionDsl.Expr.v2, ReductionDsl.Expr.v3, ReductionDsl.Env.get_cons_zero, ReductionDsl.Env.get_cons_succ]
        by_cases hsj : sIdx = j
        · subst hsj; have h1 := bkPot_eq_one_of_get_false sIdx _ hCorrF; rw [h1]; unfold bkPot; simp; omega
        · have hjs : j ≠ sIdx := Ne.symm hsj; unfold bkPot; simp [hsj, hjs]
    · exact potInvFS_ret trivial (by simp [mbHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v1])
  · refine potInvFS_ite (fun hNotOk => ?_) (fun hOk => ?_)
    · exact potInvFS_ret trivial (by simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero] at hNotOk ⊢; cases oh.1 <;> simp_all)
    · have hOkT : oh.1 = true := by simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero] at hOk; cases h : oh.1 <;> simp_all
      simp only [hOkT, ↓reduceIte]; rw [eval_bind]
      refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot (Inv₁ := fun _ => True) (B₁ := fun _ => m + mbHPot j oh.2) ?_ (fun _ _ => ?_)
      · refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => ?_)
        · refine potInvMultiFS_query (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) j .tr _ _ _ _ ?_; split <;> omega
        · refine potInvMultiFS_query (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) j .ch _ _ _ _ ?_; split <;> omega
      · refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => ?_)
        · exact potInvFS_ret trivial (by simp [mbHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v1])
        · refine potInvFS_ret trivial ?_
          simp only [mbHPot, fsMultiDFBucketHsSetBookAt, fsMultiDFBucketHsMk, fsMultiDFBucketHsBook,
            fsMultiDFBucketHsGetBookAt, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v2, ReductionDsl.Expr.v3, ReductionDsl.Env.get_cons_zero, ReductionDsl.Env.get_cons_succ]
          unfold bkPot; dsimp only
          by_cases hsj : j = sIdx
          · subst hsj; cases oh.2.2.2.2.1 j <;> simp
          · simp [hsj]

theorem redFSAuthDFPaperMultiBucketProg_sess_isQueryBoundP
    (L B Δcka Δbucket qep maxSkip : ℕ) (la : Bool) (tL : Option ℕ) (par : Bool) (j q : ℕ)
    (A : OracleComp (unifSpec + _root_.CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) Bool)
    (hA : A.IsQueryBoundP (· matches .inr _) q) :
    ((redFSAuthDFPaperMultiBucketProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
        L B Δcka Δbucket qep maxSkip la tL par).eval (fun _ => A) ()).IsQueryBoundP
      (fun x => (match x with | .inl _ => false | .inr ⟨s, _⟩ => decide (s = j)) = true)
      (2 * q) := by
  let R := redFSAuthDFPaperMultiBucketProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
    (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B Δcka Δbucket qep maxSkip la tL par
  have hTot := redFSAuthDFPaperMultiBucketProg_totalQueries (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
    (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    L B Δcka Δbucket qep maxSkip la tL par q
  have hSyn := ReductionDsl.CostedReduction.queryBound_eval R (sessPred j) (fun _ => 1) (fun _ => 0)
    (fun _ _ _ => Nat.le_refl 1) (multiIface_fwdU_zero j)
    (fun _ => A) q (fun _ => hA.of_imp (fun x hx => by cases x <;> [cases hx; rfl])) ()
  exact hSyn.mono (hTot.trans (Nat.mul_comm q 2).le)

private theorem redFSAuthDFPaperMultiBucketModeProg_sess_isQueryBoundP
    (L B Δcka Δbucket qep maxSkip : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool) (j q : ℕ)
    (A : OracleComp (unifSpec + _root_.CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) Bool)
    (hA : A.IsQueryBoundP (· matches .inr _) q) :
    ((redFSAuthDFPaperMultiBucketModeProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
        L B Δcka Δbucket qep maxSkip gMain la tL par).eval (fun _ => A) ()).IsQueryBoundP
      (fun x => (match x with | .inl _ => false | .inr ⟨s, _⟩ => decide (s = j)) = true)
      (2 * q) := by
  let R := redFSAuthDFPaperMultiBucketModeProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
    (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B Δcka Δbucket qep maxSkip gMain la tL par
  have hTot := redFSAuthDFPaperMultiBucketModeProg_totalQueries (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
    (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    L B Δcka Δbucket qep maxSkip gMain la tL par q
  have hSyn := ReductionDsl.CostedReduction.queryBound_eval R (sessPred j) (fun _ => 1) (fun _ => 0)
    (fun _ _ _ => Nat.le_refl 1) (multiIface_fwdU_zero j)
    (fun _ => A) q (fun _ => hA.of_imp (fun x hx => by cases x <;> [cases hx; rfl])) ()
  exact hSyn.mono (hTot.trans (Nat.mul_comm q 2).le)

private theorem redFSAuthDFPaperMultiBucketModeProg_sess_isQueryBoundP_of_eq
    (L B Δcka Δbucket qep maxSkip : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool) (j q : ℕ)
    (R : CostedReduction OO IIM
      (_root_.CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E) .unit .unit .bool .bool)
    (hR : R = redFSAuthDFPaperMultiBucketModeProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      L B Δcka Δbucket qep maxSkip gMain la tL par)
    (A : OracleComp (unifSpec + _root_.CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) Bool)
    (hA : A.IsQueryBoundP (· matches .inr _) q) :
    (R.eval (fun _ => A) ()).IsQueryBoundP
      (fun x => (match x with | .inl _ => false | .inr ⟨s, _⟩ => decide (s = j)) = true)
      (2 * q) := by
  subst hR
  exact redFSAuthDFPaperMultiBucketModeProg_sess_isQueryBoundP L B Δcka Δbucket qep maxSkip gMain la tL par j q A hA

private theorem fsMultiDFBucketPaperFsRecvC_potOKInv (j L B Δcka : ℕ) (la : Bool) {Γ' : List (Ty SP)}
    (hE : Expr OO Γ' mbHsTy) (ctxE : Expr OO Γ' (cGsTy mVpTy)) (pE : Expr OO Γ' .bool)
    (tE : Expr OO Γ' .nat) (rsvE : Expr OO Γ' (.sum (.base .rs) .nat))
    (hdrE : Expr OO Γ' hdrTy) (eE : Expr OO Γ' (.base .ct)) (recE : Expr OO Γ' (.opt cRecTy))
    (ρ : Env Γ') (m : ℕ) :
    PotOKInvFS (sessPred j) (fun _ => True) (fun res => m + mbHPot j res.2)
      ((fsMultiDFBucketPaperFsRecvC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L B la Δcka hE ctxE pE tE rsvE hdrE eE recE).eval ρ)
      (1 + m + mbHPot j (hE.eval ρ)) := by
  unfold fsMultiDFBucketPaperFsRecvC; rw [eval_bind_ret]
  refine potInvFS_caseSum (fun _ _ => ?_) (fun sIdx _ => ?_)
  · refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => ?_)
    · exact potInvFS_ret trivial (by simp only [mbHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v1, ReductionDsl.Env.get_cons_succ, ReductionDsl.Env.get_cons_zero]; omega)
    · exact potInvFS_ret trivial (by simp only [mbHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v2, ReductionDsl.Env.get_cons_succ, ReductionDsl.Env.get_cons_zero]; omega)
  · rw [eval_bind]
    refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot (Inv₁ := fun _ => True)
      (B₁ := fun oh => (if oh.1 then 1 else 0) + m + mbHPot j oh.2) ?_ (fun oh _ => ?_)
    · refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => potInvFS_ret trivial (by simp [mbHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v2]))
      refine potInvFS_ite (fun hCond => ?_) (fun _ => potInvFS_ret trivial (by simp [mbHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v1]))
      rw [eval_bind]
      have hCorrF : ((match (hE.eval ρ).2.2.2.1 sIdx with | none => (false, (0, [])) | some b => b : (mBookTy).denote)).1 = false := by
        simp only [fsMultiDFBucketHsGetBookAt, fsMultiDFBucketHsBook, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1,
          ReductionDsl.Env.get_cons_zero, ReductionDsl.Env.get_cons_succ, Bool.and_eq_true, Bool.not_eq_true'] at hCond
        cases hB : (hE.eval ρ).2.2.2.1 sIdx <;> simp [hB] at hCond ⊢; exact hCond.2
      refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot
        (potInvMultiFS_query (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
          (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
          (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
          (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
          (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) j .cs _ _
          ((if sIdx = j then 0 else 1) + m + mbHPot j (hE.eval ρ))
          (1 + m + mbHPot j (hE.eval ρ)) (by simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero]; split <;> omega))
        (fun _ _ => ?_)
      refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => ?_)
      · exact potInvFS_ret trivial (by simp [mbHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v2])
      · refine potInvFS_ret trivial ?_
        simp only [mbHPot, fsMultiDFBucketHsSetBookAt, fsMultiDFBucketHsMk, fsMultiDFBucketHsBook,
          fsMultiDFBucketHsGetBookAt, ReductionDsl.Expr.eval, ReductionDsl.Expr.v2, ReductionDsl.Expr.v3, ReductionDsl.Env.get_cons_zero, ReductionDsl.Env.get_cons_succ]
        by_cases hsj : sIdx = j
        · subst hsj; have h1 := bkPot_eq_one_of_get_false sIdx _ hCorrF; rw [h1]; unfold bkPot; simp; omega
        · have hjs : j ≠ sIdx := Ne.symm hsj; unfold bkPot; simp [hsj, hjs]
    · refine potInvFS_ite (fun hNotOk => ?_) (fun hOk => ?_)
      · exact potInvFS_ret trivial (by simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero] at hNotOk ⊢; cases oh.1 <;> simp_all)
      · have hOkT : oh.1 = true := by simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero] at hOk; cases h : oh.1 <;> simp_all
        simp only [hOkT, ↓reduceIte]; rw [eval_bind]
        refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot (Inv₁ := fun _ => True) (B₁ := fun _ => m + mbHPot j oh.2) ?_ (fun _ _ => ?_)
        · refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => ?_)
          · refine potInvMultiFS_query (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) j .ij _ _ _ _ ?_; split <;> omega
          · refine potInvMultiFS_query (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) j .dl _ _ _ _ ?_; split <;> omega
        · refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => ?_)
          · exact potInvFS_ret trivial (by simp [mbHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v1])
          · refine potInvFS_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
            · exact potInvFS_ret trivial (by simp [mbHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v3])
            · refine potInvFS_ite (fun _ => ?_) (fun _ => ?_)
              · exact potInvFS_ret trivial (by simp [mbHPot, fsMultiDFBucketHsSetLfWin, fsMultiDFBucketHsMk, fsMultiDFBucketHsBook, ReductionDsl.Expr.eval, ReductionDsl.Expr.v3])
              · refine potInvFS_ret trivial ?_
                simp only [mbHPot, fsMultiDFBucketHsSetBookAt, fsMultiDFBucketHsMk, fsMultiDFBucketHsBook,
                  fsMultiDFBucketHsGetBookAt, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v3, ReductionDsl.Expr.v4,
                  ReductionDsl.Env.get_cons_zero, ReductionDsl.Env.get_cons_succ]
                unfold bkPot; dsimp only
                by_cases hsj : j = sIdx
                · subst hsj; cases oh.2.2.2.2.1 j <;> simp
                · simp [hsj]

private theorem fsMultiDFBucketRevealC_potOKInv (j L : ℕ) (la : Bool) {Γ' : List (Ty SP)}
    (hE : Expr OO Γ' mbHsTy) (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (pE : Expr OO Γ' .bool) (vpE : Expr OO Γ' mVpTy) (ρ : Env Γ') (m : ℕ) :
    PotOKInvFS (sessPred j) (fun _ => True) (fun res => m + mbHPot j res.2)
      ((fsMultiDFBucketRevealC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L la hE ctxE pE vpE).eval ρ)
      (1 + m + mbHPot j (hE.eval ρ)) := by
  unfold fsMultiDFBucketRevealC; rw [eval_bind_ret, eval_bind]
  refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot (Inv₁ := fun _ => True) (B₁ := fun sh => m + mbHPot j sh.2) ?_ (fun sh _ => ?_)
  · refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => ?_)
    · exact potInvFS_ret trivial (by simp only [mbHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero]; omega)
    · refine potInvFS_caseSum (fun _ _ => ?_) (fun sIdx _ => ?_)
      · exact potInvFS_ret trivial (by simp only [mbHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v2, ReductionDsl.Env.get_cons_succ, ReductionDsl.Env.get_cons_zero]; omega)
      · rw [eval_bind]
        refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot
          (potInvMultiFS_query (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) j .cs _ _ (m + mbHPot j (hE.eval ρ)) (1 + m + mbHPot j (hE.eval ρ)) (by split <;> omega))
          (fun _ _ => ?_)
        refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => ?_)
        · exact potInvFS_ret trivial (by simp [mbHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v3])
        · refine potInvFS_ret trivial ?_
          simp only [mbHPot, fsMultiDFBucketHsSetBookAt, fsMultiDFBucketHsMk, fsMultiDFBucketHsBook,
            ReductionDsl.Expr.eval, ReductionDsl.Expr.v2, ReductionDsl.Expr.v4, ReductionDsl.Env.get_cons_zero, ReductionDsl.Env.get_cons_succ]
          unfold bkPot; dsimp only; by_cases hsj : j = sIdx <;> simp [hsj]
  · refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => ?_)
    · exact potInvFS_ret trivial (by simp [mbHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0])
    · rw [eval_bind]
      refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot
        (potInvMultiFS_zero j _ _ (m + mbHPot j sh.2) (fun _ => Nat.le_refl _) (rangeListC_multiDF_queries L (fun _ => 1)))
        (fun _ _ => ?_)
      refine potInvFS_ite (fun _ => ?_) (fun _ => ?_) <;>
        exact potInvFS_ret trivial (by simp [mbHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v2])

private theorem fsMultiDFBucketModeRevealC_potOKInv (j L : ℕ) (gMain la : Bool) (tL : Option ℕ) {Γ' : List (Ty SP)}
    (hE : Expr OO Γ' mbHsTy) (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (pE : Expr OO Γ' .bool) (vpE : Expr OO Γ' mVpTy) (ρ : Env Γ') (m : ℕ) :
    PotOKInvFS (sessPred j) (fun _ => True) (fun res => m + mbHPot j res.2)
      ((fsMultiDFBucketModeRevealC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L gMain la tL hE ctxE pE vpE).eval ρ)
      (1 + m + mbHPot j (hE.eval ρ)) := by
  unfold fsMultiDFBucketModeRevealC
  cases gMain
  · simp only [Bool.false_eq_true, ↓reduceIte]
    unfold fsMultiDFBucketForgedHdrRevealC; dsimp only; rw [eval_bind_ret]
    refine potInvFS_ite
      (fun _ => potInvFS_ret trivial (by simp only [mbHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero]; omega))
      (fun _ => ?_)
    have hSub := fsMultiDFBucketRevealC_potOKInv (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) j L la (.fst (ReductionDsl.Expr.v0 (O := OO))) (.fst (.snd .v0))
      (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0))) (.cons ((hE.pair (ctxE.pair (pE.pair vpE))).eval ρ) ρ) m
    simpa only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero] using hSub
  · simp only [↓reduceIte]
    exact fsMultiDFBucketRevealC_potOKInv j L la hE ctxE pE vpE ρ m

private theorem hooksFSMultiDFBucketPaperModeC_potSpec (j L B Δcka Δbucket qep : ℕ)
    (gMain : Bool) (tL : Option ℕ) (par la : Bool) :
    HooksPotSpec j
      (hooksFSMultiDFBucketPaperModeC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B Δcka Δbucket qep gMain tL par la) (mbHPot j) where
  startSend hE ctxE _ tE γE σE rE ρ m := by
    unfold hooksFSMultiDFBucketPaperModeC fsMultiDFBucketPaperStartSendC; dsimp only; rw [eval_bind_ret, eval_bind]
    refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot
      (potInvFS_caseOpt (fun _ => potInvMultiFS_zero j _ _ (m + mbHPot j (hE.eval ρ)) (fun _ => Nat.le_refl _) rfl)
        (fun _ _ => potInvFS_ret trivial (Nat.le_refl _))) (fun coins _ => ?_)
    rw [eval_bind]
    have hR := rootFSMultiDFBucketPaperC_potOKInv (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) j L Δbucket qep tL par (.fst (ReductionDsl.Expr.v1 (O := OO))) (.fst (.snd .v1))
      (.snd (.snd (.snd (.snd (.snd .v1)))))
      (.snd (.snd (ReductionDsl.Expr.op (O := OO) CryptoGames.CKA.CKAOp.ckaSend (.pair (.fst (.snd (.snd .v1))) .v0))))
      (.fst (.snd (.snd (.snd .v1)))) (.cons coins (.cons ((hE.pair (tE.pair (γE.pair (σE.pair (rE.pair (postLeakDFBucketE tL ctxE)))))).eval ρ) ρ)) m
    simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v1, ReductionDsl.Env.get_cons_zero, ReductionDsl.Env.get_cons_succ] at hR
    refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot hR (fun rOut _ => potInvFS_ret trivial ?_)
    have hReg := regSessOptMultiDFBucketE_book L tL (.snd (ReductionDsl.Expr.v0 (O := OO))) (.fst (.snd .v2)) (.snd (.snd (.fst .v0)))
      (.cons rOut (.cons coins (.cons ((hE.pair (tE.pair (γE.pair (σE.pair (rE.pair (postLeakDFBucketE tL ctxE)))))).eval ρ) ρ)))
    dsimp only [mbHPot, fsMultiDFBucketHsSetCache, fsMultiDFBucketHsMk, fsMultiDFBucketHsBook,
      ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v2, ReductionDsl.Env.get_cons_zero, ReductionDsl.Env.get_cons_succ] at hReg ⊢; rw [hReg]
  startRecv hE ctxE _ tE γE σE tnE ρ m := by
    unfold hooksFSMultiDFBucketPaperModeC fsMultiDFBucketPaperModeStartRecvC; dsimp only
    cases gMain
    · simp only [Bool.false_eq_true, ↓reduceIte]
      unfold fsMultiDFBucketPaperStartRecvC; rw [eval_bind_ret]
      refine potInvFS_caseOpt
        (fun _ => potInvFS_ite
          (fun _ => potInvFS_ite
            (fun _ => potInvFS_ret trivial (by simp [mbHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))
            (fun _ => potInvFS_ite
              (fun _ => potInvFS_ret trivial (by simp [mbHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))
              (fun _ => ?_)))
          (fun _ => potInvFS_ret trivial (by simp [mbHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0])))
        (fun _ _ => potInvFS_ret trivial (by simp [mbHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v1]))
      rw [eval_bind]
      have hL := lookupMultiDFBucketFC_potOKInv (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) j L (.fst (ReductionDsl.Expr.v0 (O := OO))) (.fst (.snd .v0))
        (.snd (ReductionDsl.Expr.op (O := OO) CryptoGames.CKA.CKAOp.ckaReceive (.pair (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd (.snd .v0))))))))
        (.cons ((hE.pair (tE.pair (γE.pair (σE.pair (tnE.pair (postLeakDFBucketE tL ctxE)))))).eval ρ) ρ) m
      simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero] at hL
      refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot hL (fun lOut _ => potInvFS_ret trivial ?_)
      have hReg := regSessMultiDFBucketE_book L tL (.snd (ReductionDsl.Expr.v0 (O := OO))) (.fst (.snd .v1))
        (.snd (ReductionDsl.Expr.op (O := OO) CryptoGames.CKA.CKAOp.ckaReceive (.pair (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd (.snd .v1))))))))
        (.cons lOut (.cons ((hE.pair (tE.pair (γE.pair (σE.pair (tnE.pair (postLeakDFBucketE tL ctxE)))))).eval ρ) ρ))
      dsimp only [mbHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, ReductionDsl.Env.get_cons_zero, ReductionDsl.Env.get_cons_succ] at hReg ⊢; rw [hReg]
    · simp only [↓reduceIte]
      unfold fsMultiDFBucketPaperMainStartRecvC; rw [eval_bind_ret]
      refine potInvFS_caseOpt
        (fun _ => potInvFS_ite
          (fun _ => potInvFS_ret trivial (by simp [mbHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))
          (fun _ => potInvFS_ret trivial (by simp [mbHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0])))
        (fun _ _ => potInvFS_ret trivial (by simp [mbHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v1]))
  fsSend := fsMultiDFBucketFsSendC_potOKInv j Δcka la
  fsRecv := fsMultiDFBucketPaperFsRecvC_potOKInv j L B Δcka la
  commit _ _ _ _ _ _ _ := by unfold hooksFSMultiDFBucketPaperModeC fsMultiDFBucketCommitC; dsimp only; exact potInvFS_ret trivial (Nat.le_refl _)
  reveal := fsMultiDFBucketModeRevealC_potOKInv j L gMain la tL

private theorem redFSAuthDFPaperMultiBucketModeProg_sess_isQueryBoundP_min
    (L B Δcka Δbucket qep maxSkip : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool) (j q : ℕ)
    (A : OracleComp (unifSpec + _root_.CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) Bool)
    (hA : A.IsQueryBoundP (· matches .inr _) q) :
    ((redFSAuthDFPaperMultiBucketModeProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
        L B Δcka Δbucket qep maxSkip gMain la tL par).eval (fun _ => A) ()).IsQueryBoundP
      (fun x => (match x with | .inl _ => false | .inr ⟨s, _⟩ => decide (s = j)) = true)
      (min (2 * q) (q + 2)) := by
  let R := redFSAuthDFPaperMultiBucketModeProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
    (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B Δcka Δbucket qep maxSkip gMain la tL par
  have hSpec := hooksFSMultiDFBucketPaperModeC_potSpec (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
    (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) j L B Δcka Δbucket qep gMain tL par la
  refine costedReduction_multi_isQueryBoundP_min j R (fun st => esPot (mbHPot j) st.1) q A
    (hA.of_imp (fun x hx => by cases x <;> [cases hx; rfl]))
    (redFSAuthDFPaperMultiBucketModeProg_totalQueries L B Δcka Δbucket qep maxSkip gMain la tL par q) ?_ ?_
    (by simp [R, redFSAuthDFPaperMultiBucketModeProg, redFSAuthDFPaperMultiBucketModeProgGen, ReductionDsl.Comp.queries])
  · refine potInvMultiFS_zero j _ _ (q + 2) (fun as => ?_)
      (by simp [R, redFSAuthDFPaperMultiBucketModeProg, redFSAuthDFPaperMultiBucketModeProgGen, ReductionDsl.Comp.queries, initFSMultiDFBucketPaperEStateC_queries])
    have h1 := bkPot_le_one j as.2.1.2.1.2.2.2.1; dsimp only [esPot, mbHPot]; omega
  · intro m qv sv
    dsimp only [R, redFSAuthDFPaperMultiBucketModeProg, redFSAuthDFPaperMultiBucketModeProgGen, bucketModeHandleDFPaperC] at sv qv ⊢
    rw [eval_bind_ret]
    refine potInvFS_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
    · refine potInvFS_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
      · refine potInvFS_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
        · refine potInvFS_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
          · refine potInvFS_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
            · rw [eval_bind_ret]
              refine potInvFS_ite (fun _ => ?_) (fun _ => ?_)
              · exact potInvFS_ret trivial (by simp only [esPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v6, ReductionDsl.Env.get_cons_succ, ReductionDsl.Env.get_cons_zero]; omega)
              · refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => ?_)
                · exact potInvFS_ret trivial (by simp only [esPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v6, ReductionDsl.Env.get_cons_succ, ReductionDsl.Env.get_cons_zero]; omega)
                · rw [eval_bind]
                  refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot (vSendC_gen_potOKInv hSpec _ _ _ _ _ _ _ _ m) (fun _ _ => ?_)
                  refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => ?_)
                  · exact potInvFS_ret trivial (by simp [esPot, esMk, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0])
                  · exact potInvFS_ret trivial (by simp [esPot, esMk, ReductionDsl.Expr.eval, ReductionDsl.Expr.v1])
            · exact potInvFS_ret trivial (by simp only [esPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v5, ReductionDsl.Env.get_cons_succ, ReductionDsl.Env.get_cons_zero]; omega)
          · rw [eval_bind]
            exact Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot (deliverEC_gen_potOKInv hSpec L maxSkip _ _ _ _ m)
              (fun _ _ => potInvFS_ret trivial (by simp [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))
        · rw [eval_bind]
          exact Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot (injectEC_gen_potOKInv hSpec L (2 + Δcka) qep _ _ _ _ m)
            (fun _ _ => potInvFS_ret trivial (by simp [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))
      · refine potInvFS_ite (fun _ => ?_) (fun _ => ?_)
        · exact potInvFS_ret trivial (by simp only [esPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v2, ReductionDsl.Env.get_cons_succ, ReductionDsl.Env.get_cons_zero]; omega)
        · rw [eval_bind]
          refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot (fsMultiDFBucketModeRevealC_potOKInv j L gMain la tL _ _ _ _ _ m) (fun _ _ => ?_)
          refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => ?_)
          · exact potInvFS_ret trivial (by simp [esPot, esMk, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0])
          · exact potInvFS_ret trivial (by simp [esPot, esMk, ReductionDsl.Expr.eval, ReductionDsl.Expr.v1])
    · rw [eval_bind]
      exact Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot (deliverForgeEC_gen_potOKInv hSpec L (2 + Δcka) qep _ _ _ _ m)
        (fun _ _ => potInvFS_ret trivial (by simp [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))

theorem redFSAuthDFPaperMultiBucketModeProg_sess_isQueryBoundP_of_eq_min
    (L B Δcka Δbucket qep maxSkip : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool) (j q : ℕ)
    (R : CostedReduction OO IIM
      (_root_.CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E) .unit .unit .bool .bool)
    (hR : R = redFSAuthDFPaperMultiBucketModeProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      L B Δcka Δbucket qep maxSkip gMain la tL par)
    (A : OracleComp (unifSpec + _root_.CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) Bool)
    (hA : A.IsQueryBoundP (· matches .inr _) q) :
    (R.eval (fun _ => A) ()).IsQueryBoundP
      (fun x => (match x with | .inl _ => false | .inr ⟨s, _⟩ => decide (s = j)) = true)
      (min (2 * q) (q + 2)) := by
  subst hR
  exact redFSAuthDFPaperMultiBucketModeProg_sess_isQueryBoundP_min L B Δcka Δbucket qep maxSkip gMain la tL par j q A hA


end MultiBucketPotOK

section AtomicLifts

open _root_.Computational.Proofs.HeadlineV1.DeliverForgePaperMultiPotOK (redFSAuthDFPaperMultiProg_sess_isQueryBoundP_of_eq redFSAuthDFPaperMultiProg_sess_isQueryBoundP_of_eq_min redFSAuthDFShiftedPaperMultiGenProg_sess_isQueryBoundP_of_eq redFSAuthDFShiftedPaperMultiGenProg_sess_isQueryBoundP_of_eq_min)

open _root_.CryptoGames (Party)
open _root_.ReductionDsl (CostedReduction fsaeadHeaderIface fig8SmCodecDF)
open _root_.CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey maxForwardJumps)
local notation "Bytes" => List (BitVec 8)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.CKA (DHFun)
open _root_.CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C)
open Computational.Proofs.SessionCostedFig8.BundlesMultiFs (compileFsMultiDFAtomic
  compileFsMultiDFAtomic_makesAtMostQueries)
open Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2 (
  redFSAuthDFShiftedPaperMultiProg redFSAuthDFShiftedDir2PaperMultiProg)
open _root_.CryptoGames.SM.Construction (redFSAuthDFPaperMultiProg
  redFSAuthDFPaperMultiBucketModeProg healEpoch)
open OracleSpec OracleComp

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

local instance {α : Type} [Zero α] : Nonempty α := ⟨0⟩

private abbrev ShallowMultiDFRed
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (B0 : ℕ) :=
  CostedReduction (Computational.Proofs.SessionCostedFig8.Bundles.fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
    (CryptoGames.SM.Construction.fsaeadMultiHeaderAdIface (BitVec 256)
      (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt (BitVec 256)
      (BitVec 256) (BitVec 256) (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)
      ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
    (CryptoGames.SM.specDF (Fig8St Pt)
      (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (CryptoGames.PRFPRNG.prngSMCodecDF (BitVec 256)
      (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt (BitVec 256)
      (BitVec 256) (BitVec 256) (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32))
    .unit .unit .bool .bool

theorem dummyFsStage2AtomicProg_makesAtMostQueries
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (C : Crypto) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (q qOut : ℕ)
    (A : OracleComp (unifSpec + CryptoGames.SM.specDF (Fig8St Pt)
      (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)) Bool)
    (hA : A.IsQueryBoundP (· matches .inr _) q) :
    CryptoGames.FSAEAD.MakesAtMostQueries
      ((Computational.Proofs.SessionCostedFig8.DFProgBucketBounds.dummyFsStage2AtomicProg
        Dh encPt C ℓ encT idOf lam).eval (fun _ => A) ()) qOut := by
  dsimp only [Computational.Proofs.SessionCostedFig8.DFProgBucketBounds.dummyFsStage2AtomicProg]
  refine Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedPotOK.compileFsDFAtomic_makesAtMostQueries
    ℓ C Dh encPt encT idOf lam 0 qOut
    (Computational.Proofs.SessionCostedFig8.DFProgBucketBounds.dummyFsDFShallowProg Dh encPt C ℓ encT idOf lam) A ?_
  have hSyn := ReductionDsl.CostedReduction.queryBound_eval
    (Computational.Proofs.SessionCostedFig8.DFProgBucketBounds.dummyFsDFShallowProg Dh encPt C ℓ encT idOf lam)
    (ReductionDsl.isGameQuery (G := CryptoGames.FSAEAD.spec
      (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (_root_.CryptoGames.SM.Construction.Header Pt)
      (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)))
    (fun _ => 1) (fun _ => 0)
    (fun _ _ _ => Nat.le_refl 1)
    (Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.fsIface_fwdU_zero
      (KC := BitVec 256) (I := Pt) (KR := BitVec 256) (K := BitVec 256)
      (sampKR := ($ᵗ (BitVec 256))) (sampKC := ($ᵗ (BitVec 256)))
      (sampCCoins := ($ᵗ (BitVec 256))) (sampI := ($ᵗ Pt)) (sampK := ($ᵗ (BitVec 256))))
    (fun _ => A) q (fun _ => hA.of_imp (by rintro (_ | _) <;> simp [ReductionDsl.isGameQuery])) ()
  unfold CryptoGames.FSAEAD.MakesAtMostQueries
  exact (hSyn.mono (by simp [Computational.Proofs.SessionCostedFig8.DFProgBucketBounds.dummyFsDFShallowProg,
    ReductionDsl.CostedReduction.totalQueries, ReductionDsl.Comp.queries])).of_imp
    (fun x hx => by rcases x with _ | _ <;> simp_all [ReductionDsl.isGameQuery])

theorem redPRNGAuthDFPaperBucketHybridAtomicProg_makesAtMostQueries
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (C : Crypto) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep q : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (A : OracleComp (unifSpec + CryptoGames.SM.specDF (Fig8St Pt)
      (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)) Bool)
    (hA : A.IsQueryBoundP (· matches .inr _) q) :
    (fun X n => X.IsQueryBoundP (· matches .inr _) n)
      ((Computational.Proofs.SessionCostedFig8.DFProgBucketBounds.redPRNGAuthDFPaperBucketHybridAtomicProg
        Dh encPt C ℓ encT idOf lam qep q tL par t).eval (fun _ => A) ())
      (min (2 + 2 * q) (q + 3)) := by
  dsimp only [Computational.Proofs.SessionCostedFig8.DFProgBucketBounds.redPRNGAuthDFPaperBucketHybridAtomicProg]
  split_ifs
  · exact Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedPotOK.compilePrngDFAtomic_makesAtMostQueries
      ℓ C Dh encPt encT idOf lam ((q + 1) * (maxForwardJumps + 1)) (min (2 + 2 * q) (q + 3)) _ A
      (CryptoGames.SM.Construction.redPRNGAuthDFPaperBucketSplitProg_makesAtMostQueries_impl
        (q + 1) ((q + 1) * (maxForwardJumps + 1)) 1 qep maxForwardJumps tL par false t q A
        (hA.of_imp (by rintro (_ | _) <;> simp)))
  · exact Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedPotOK.compilePrngDFAtomic_makesAtMostQueries
      ℓ C Dh encPt encT idOf lam ((q + 1) * (maxForwardJumps + 1)) (min (2 + 2 * q) (q + 3)) _ A
      (CryptoGames.SM.Construction.redPRNGAuthDFPaperBucketSplitProg_makesAtMostQueries_impl
        (q + 1) ((q + 1) * (maxForwardJumps + 1)) 1 qep maxForwardJumps tL par true (t - 1) q A
        (hA.of_imp (by rintro (_ | _) <;> simp)))
  · dsimp only [Computational.Proofs.SessionCostedFig8.DFProgBucketBounds.dummyPrngStage2AtomicProg]
    refine Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedPotOK.compilePrngDFAtomic_makesAtMostQueries
      ℓ C Dh encPt encT idOf lam 0 (min (2 + 2 * q) (q + 3))
      (Computational.Proofs.SessionCostedFig8.DFProgBucketBounds.dummyPrngDFShallowProg Dh encPt C ℓ encT idOf lam) A ?_
    have hSyn := ReductionDsl.CostedReduction.queryBound_eval
      (Computational.Proofs.SessionCostedFig8.DFProgBucketBounds.dummyPrngDFShallowProg Dh encPt C ℓ encT idOf lam)
      (ReductionDsl.isGameQuery (G := CryptoGames.PRFPRNG.spec (BitVec 256) Pt (BitVec 256)))
      (fun _ => 1) (fun _ => 0)
      (fun _ _ _ => Nat.le_refl 1)
      (fun n => by
        change OracleComp.IsQueryBoundP
          (liftM (OracleSpec.query (spec := unifSpec + CryptoGames.PRFPRNG.spec (BitVec 256) Pt (BitVec 256)) (.inl n)))
          (ReductionDsl.isGameQuery (G := CryptoGames.PRFPRNG.spec (BitVec 256) Pt (BitVec 256))) 0
        rw [← bind_pure (liftM _), isQueryBoundP_query_bind_iff]
        exact ⟨Or.inl (by simp [ReductionDsl.isGameQuery]), fun _ => by simp⟩)
      (fun _ => A) q (fun _ => hA.of_imp (by rintro (_ | _) <;> simp [ReductionDsl.isGameQuery])) ()
    exact (hSyn.mono (by simp [Computational.Proofs.SessionCostedFig8.DFProgBucketBounds.dummyPrngDFShallowProg,
      ReductionDsl.CostedReduction.totalQueries, ReductionDsl.Comp.queries])).of_imp
      (fun x hx => by rcases x with _ | _ <;> simp_all [ReductionDsl.isGameQuery])

theorem redFSAuthDFCasePaperMultiAtomicProg_makesAtMostQueries
    (ℓ : ℕ) (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (stage la : Bool) (j qR q qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : OracleComp (unifSpec + CryptoGames.SM.specDF (Fig8St Pt)
      (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)) Bool)
    (hA : A.IsQueryBoundP (· matches .inr _) q) :
    CryptoGames.FSAEAD.MakesAtMostQueries
      ((Computational.Proofs.SessionCostedFig8.DFProgFsStage2Defs.redFSAuthDFCasePaperMultiAtomicProg
        ℓ Pt C Dh encPt encT idOf lam stage la j qR q qep tL t).eval (fun _ => A) ())
      (2 * q) := by
  dsimp only [Computational.Proofs.SessionCostedFig8.DFProgFsStage2Defs.redFSAuthDFCasePaperMultiAtomicProg,
    Computational.Proofs.SessionCostedFig8.DFProgFsStage2Defs.redFSAuthDFShiftedDir2PaperMultiAtomicProg,
    Computational.Proofs.SessionCostedFig8.DFProgFsStage2Defs.redFSAuthDFShiftedPaperMultiAtomicProg,
    Computational.Proofs.SessionCostedFig8.DFProgFsStage2Defs.redFSAuthDFPaperMultiAtomicProg]
  split_ifs
  · apply compileFsMultiDFAtomic_makesAtMostQueries
    exact (redFSAuthDFShiftedPaperMultiGenProg_sess_isQueryBoundP_of_eq (q + 1) ((q + 1) * (maxForwardJumps + 1))
      0 qep maxForwardJumps (t - 1) _ false la j q
      (_ : ShallowMultiDFRed ℓ Pt C Dh encPt encT idOf lam ((q + 1) * (maxForwardJumps + 1)))
      (by unfold redFSAuthDFShiftedDir2PaperMultiProg; rfl) A (hA.of_imp (by rintro (_ | _) <;> simp))).of_imp
      (by rintro (_ | ⟨_, _⟩) <;> simp)
  · exact dummyFsStage2AtomicProg_makesAtMostQueries Dh encPt C ℓ encT idOf lam q (2 * q) A hA
  · apply compileFsMultiDFAtomic_makesAtMostQueries
    exact (redFSAuthDFShiftedPaperMultiGenProg_sess_isQueryBoundP_of_eq (q + 1) ((q + 1) * (maxForwardJumps + 1))
      1 qep maxForwardJumps (t - 2) _ true la j q
      (_ : ShallowMultiDFRed ℓ Pt C Dh encPt encT idOf lam ((q + 1) * (maxForwardJumps + 1)))
      (by unfold redFSAuthDFShiftedPaperMultiProg; rfl) A (hA.of_imp (by rintro (_ | _) <;> simp))).of_imp
      (by rintro (_ | ⟨_, _⟩) <;> simp)
  · exact dummyFsStage2AtomicProg_makesAtMostQueries Dh encPt C ℓ encT idOf lam q (2 * q) A hA
  · apply compileFsMultiDFAtomic_makesAtMostQueries
    exact (redFSAuthDFPaperMultiProg_sess_isQueryBoundP_of_eq (q + 1) ((q + 1) * (maxForwardJumps + 1))
      1 qep maxForwardJumps la tL t j q
      (redFSAuthDFPaperMultiProg (q + 1) ((q + 1) * (maxForwardJumps + 1))
        1 qep maxForwardJumps la tL t :
        ShallowMultiDFRed ℓ Pt C Dh encPt encT idOf lam ((q + 1) * (maxForwardJumps + 1)))
      rfl A (hA.of_imp (by rintro (_ | _) <;> simp))).of_imp
      (by rintro (_ | ⟨_, _⟩) <;> simp)
  · exact dummyFsStage2AtomicProg_makesAtMostQueries Dh encPt C ℓ encT idOf lam q (2 * q) A hA

theorem redFSAuthDFPaperMultiBucketAtomicProg_makesAtMostQueries
    (ℓ : ℕ) (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (stage la : Bool) (j qR q qep : ℕ) (tL : Option ℕ) (par : Bool)
    (A : OracleComp (unifSpec + CryptoGames.SM.specDF (Fig8St Pt)
      (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)) Bool)
    (hA : A.IsQueryBoundP (· matches .inr _) q) :
    CryptoGames.FSAEAD.MakesAtMostQueries
      ((Computational.Proofs.SessionCostedFig8.DFProgFsStage2Defs.redFSAuthDFPaperMultiBucketAtomicProg
        ℓ Pt C Dh encPt encT idOf lam stage la j qR q qep tL par).eval (fun _ => A) ())
      (2 * q) := by
  dsimp only [Computational.Proofs.SessionCostedFig8.DFProgFsStage2Defs.redFSAuthDFPaperMultiBucketAtomicProg]
  split_ifs
  · apply compileFsMultiDFAtomic_makesAtMostQueries
    refine (Computational.Proofs.SessionCostedFig8.DFProgFsStage2Defs.ckaCoinBranchDFRed_isQueryBoundP
      ℓ Pt C Dh encPt encT idOf lam ((q + 1) * (maxForwardJumps + 1)) _ _ (fun _ => A) ()
      (fun x => (match x with | .inl _ => false | .inr ⟨s, _⟩ => decide (s = j)) = true)
      (2 * q) (by intro n; simp) ?_ ?_).of_imp (by rintro (_ | ⟨_, _⟩) <;> simp)
    · exact (redFSAuthDFPaperMultiBucketModeProg_sess_isQueryBoundP_of_eq
        (q + 1) ((q + 1) * (maxForwardJumps + 1)) 1 4 (min qep (q + 11)) maxForwardJumps true la tL par j q
        (_ : ShallowMultiDFRed ℓ Pt C Dh encPt encT idOf lam ((q + 1) * (maxForwardJumps + 1)))
        rfl A (hA.of_imp (by rintro (_ | _) <;> simp))).of_imp (by rintro (_ | ⟨_, _⟩) <;> simp)
    · exact (redFSAuthDFPaperMultiBucketModeProg_sess_isQueryBoundP_of_eq
        (q + 1) ((q + 1) * (maxForwardJumps + 1)) 1 4 (min qep (q + 11)) maxForwardJumps false la tL par j q
        (_ : ShallowMultiDFRed ℓ Pt C Dh encPt encT idOf lam ((q + 1) * (maxForwardJumps + 1)))
        rfl A (hA.of_imp (by rintro (_ | _) <;> simp))).of_imp (by rintro (_ | ⟨_, _⟩) <;> simp)
  · exact dummyFsStage2AtomicProg_makesAtMostQueries Dh encPt C ℓ encT idOf lam q (2 * q) A hA

theorem redFSAuthDFCasePaperMultiAtomicProg_makesAtMostQueries_min
    (ℓ : ℕ) (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (stage la : Bool) (j qR q qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : OracleComp (unifSpec + CryptoGames.SM.specDF (Fig8St Pt)
      (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)) Bool)
    (hA : A.IsQueryBoundP (· matches .inr _) q) :
    CryptoGames.FSAEAD.MakesAtMostQueries
      ((Computational.Proofs.SessionCostedFig8.DFProgFsStage2Defs.redFSAuthDFCasePaperMultiAtomicProg
        ℓ Pt C Dh encPt encT idOf lam stage la j qR q qep tL t).eval (fun _ => A) ())
      (min (2 * q) (q + 2)) := by
  dsimp only [Computational.Proofs.SessionCostedFig8.DFProgFsStage2Defs.redFSAuthDFCasePaperMultiAtomicProg,
    Computational.Proofs.SessionCostedFig8.DFProgFsStage2Defs.redFSAuthDFShiftedDir2PaperMultiAtomicProg,
    Computational.Proofs.SessionCostedFig8.DFProgFsStage2Defs.redFSAuthDFShiftedPaperMultiAtomicProg,
    Computational.Proofs.SessionCostedFig8.DFProgFsStage2Defs.redFSAuthDFPaperMultiAtomicProg]
  split_ifs
  · apply compileFsMultiDFAtomic_makesAtMostQueries
    exact (redFSAuthDFShiftedPaperMultiGenProg_sess_isQueryBoundP_of_eq_min (q + 1) ((q + 1) * (maxForwardJumps + 1))
      0 qep maxForwardJumps (t - 1) _ false la j q
      (_ : ShallowMultiDFRed ℓ Pt C Dh encPt encT idOf lam ((q + 1) * (maxForwardJumps + 1)))
      (by unfold redFSAuthDFShiftedDir2PaperMultiProg; rfl) A (hA.of_imp (by rintro (_ | _) <;> simp))).of_imp
      (by rintro (_ | ⟨_, _⟩) <;> simp)
  · exact dummyFsStage2AtomicProg_makesAtMostQueries Dh encPt C ℓ encT idOf lam q (min (2 * q) (q + 2)) A hA
  · apply compileFsMultiDFAtomic_makesAtMostQueries
    exact (redFSAuthDFShiftedPaperMultiGenProg_sess_isQueryBoundP_of_eq_min (q + 1) ((q + 1) * (maxForwardJumps + 1))
      1 qep maxForwardJumps (t - 2) _ true la j q
      (_ : ShallowMultiDFRed ℓ Pt C Dh encPt encT idOf lam ((q + 1) * (maxForwardJumps + 1)))
      (by unfold redFSAuthDFShiftedPaperMultiProg; rfl) A (hA.of_imp (by rintro (_ | _) <;> simp))).of_imp
      (by rintro (_ | ⟨_, _⟩) <;> simp)
  · exact dummyFsStage2AtomicProg_makesAtMostQueries Dh encPt C ℓ encT idOf lam q (min (2 * q) (q + 2)) A hA
  · apply compileFsMultiDFAtomic_makesAtMostQueries
    exact (redFSAuthDFPaperMultiProg_sess_isQueryBoundP_of_eq_min (q + 1) ((q + 1) * (maxForwardJumps + 1))
      1 qep maxForwardJumps la tL t j q
      (redFSAuthDFPaperMultiProg (q + 1) ((q + 1) * (maxForwardJumps + 1))
        1 qep maxForwardJumps la tL t :
        ShallowMultiDFRed ℓ Pt C Dh encPt encT idOf lam ((q + 1) * (maxForwardJumps + 1)))
      rfl A (hA.of_imp (by rintro (_ | _) <;> simp))).of_imp
      (by rintro (_ | ⟨_, _⟩) <;> simp)
  · exact dummyFsStage2AtomicProg_makesAtMostQueries Dh encPt C ℓ encT idOf lam q (min (2 * q) (q + 2)) A hA

theorem redFSAuthDFPaperMultiBucketAtomicProg_makesAtMostQueries_min
    (ℓ : ℕ) (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (stage la : Bool) (j qR q qep : ℕ) (tL : Option ℕ) (par : Bool)
    (A : OracleComp (unifSpec + CryptoGames.SM.specDF (Fig8St Pt)
      (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)) Bool)
    (hA : A.IsQueryBoundP (· matches .inr _) q) :
    CryptoGames.FSAEAD.MakesAtMostQueries
      ((Computational.Proofs.SessionCostedFig8.DFProgFsStage2Defs.redFSAuthDFPaperMultiBucketAtomicProg
        ℓ Pt C Dh encPt encT idOf lam stage la j qR q qep tL par).eval (fun _ => A) ())
      (min (2 * q) (q + 2)) := by
  dsimp only [Computational.Proofs.SessionCostedFig8.DFProgFsStage2Defs.redFSAuthDFPaperMultiBucketAtomicProg]
  split_ifs
  · apply compileFsMultiDFAtomic_makesAtMostQueries
    refine (Computational.Proofs.SessionCostedFig8.DFProgFsStage2Defs.ckaCoinBranchDFRed_isQueryBoundP
      ℓ Pt C Dh encPt encT idOf lam ((q + 1) * (maxForwardJumps + 1)) _ _ (fun _ => A) ()
      (fun x => (match x with | .inl _ => false | .inr ⟨s, _⟩ => decide (s = j)) = true)
      (min (2 * q) (q + 2)) (by intro n; simp) ?_ ?_).of_imp (by rintro (_ | ⟨_, _⟩) <;> simp)
    · exact (redFSAuthDFPaperMultiBucketModeProg_sess_isQueryBoundP_of_eq_min
        (q + 1) ((q + 1) * (maxForwardJumps + 1)) 1 4 (min qep (q + 11)) maxForwardJumps true la tL par j q
        (_ : ShallowMultiDFRed ℓ Pt C Dh encPt encT idOf lam ((q + 1) * (maxForwardJumps + 1)))
        rfl A (hA.of_imp (by rintro (_ | _) <;> simp))).of_imp (by rintro (_ | ⟨_, _⟩) <;> simp)
    · exact (redFSAuthDFPaperMultiBucketModeProg_sess_isQueryBoundP_of_eq_min
        (q + 1) ((q + 1) * (maxForwardJumps + 1)) 1 4 (min qep (q + 11)) maxForwardJumps false la tL par j q
        (_ : ShallowMultiDFRed ℓ Pt C Dh encPt encT idOf lam ((q + 1) * (maxForwardJumps + 1)))
        rfl A (hA.of_imp (by rintro (_ | _) <;> simp))).of_imp (by rintro (_ | ⟨_, _⟩) <;> simp)
  · exact dummyFsStage2AtomicProg_makesAtMostQueries Dh encPt C ℓ encT idOf lam q (min (2 * q) (q + 2)) A hA

end AtomicLifts

end

end Computational.Proofs.HeadlineV1.DeliverForgePaperMultiBucketPotOK
