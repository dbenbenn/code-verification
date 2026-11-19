/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2 -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperBucketFS -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks -- proof-setup: allow-public-import
import Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedPotOK

/-!
# Per-Session Query Bounds for Multi-Session Paper `DeliverForge` Reductions (`[B7]`)

Establishes `PotOKInvFS` potential invariants on generic `HooksC` and `fsMulti` hooks, proving
per-session `2 * q` query bounds on `redFSAuthDFPaperMultiProg` and
`redFSAuthDFShiftedPaperMultiGenProg`.-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2 (redFSAuthDFShiftedPaperMultiGenProg redFSAuthDFShiftedPaperMultiGenProg_totalQueries)
open Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks (PotOKInvFS isQueryBoundP_min_fs potInvFS_caseOpt potInvFS_caseSum potInvFS_ite potInvFS_ret potOKInvFS_simulateQ_handlerImpl_step1)
open CryptoGames.CKA (ckaHdrCtTy ckaHdrTy ckaSMQ ckaSMQDF)
open CryptoGames.PRFPRNG (prngOps prngSMCodecDF prngSig)
open CryptoGames.SM (otherE pGet posTy)
open CryptoGames.SM.Construction (Header Mode PartyState fsMultiCommitC fsMultiDFBucketEsTy fsMultiDFBucketHsTy fsMultiEsTy fsMultiFsRecvC fsMultiFsSendC fsMultiHsBook fsMultiHsGetBookAt fsMultiHsMk fsMultiHsSetBookAt fsMultiHsSetCache fsMultiHsSetLfWin fsMultiHsSetSessions fsMultiHsSetTable fsMultiHsTy fsMultiRevealC fsMultiSessBookTy fsMultiStartRecvC fsMultiStartSendC fsMultiVpTy fsaeadMultiHeaderAdIface hooksFSMultiC rangeListC_queries lookupMultiFC redFSAuthDFPaperMultiProg redFSAuthDFPaperMultiProg_totalQueries regSessMultiE regSessOptMultiE rootFSMultiC)
open CryptoGames.SM.Engine (ConfigEC HooksC Policy cAcceptE cGsB cGsEpoch cGsSt cGsTy cRecPos cRecTy challEC commitEC corrECPaper corrECShiftedPaper deliverEC deliverForgeEC deliverForgeECB1 deliverForgeECGen esG esH esMk esSetAbort esSetG esSetH esTy eval_bind eval_bind_ret implECDFPaper implECDFShiftedPaperGen implECPaper implECShiftedPaperGen injectEC injectECB1 injectECGen modeCfgEC transmitEC vRecvC vRecvStep1C vSendC vSendStep1C vpRoot vpTcur vpTcurNat vpΓ)
open ReductionDsl (Comp CostedReduction Env Expr GameCodec Ty isGameQuery)

namespace Computational.Proofs.HeadlineV1.DeliverForgePaperMultiPotOK

public section
open OracleSpec OracleComp
open _root_.Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2 (
  redFSAuthDFShiftedPaperMultiGenProg redFSAuthDFShiftedPaperMultiGenProg_totalQueries
  redFSAuthDFShiftedPaperMultiProg redFSAuthDFShiftedDir2PaperMultiProg)

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

abbrev sessPred (j : ℕ) :
    (unifSpec + OracleSpec.sigma
      (fun _ : ℕ => CryptoGames.FSAEAD.spec SS RS (Header T) M E)).Domain → Prop :=
  fun t => (match t with
    | .inl _ => false
    | .inr ⟨s, _⟩ => decide (s = j)) = true

theorem multiIface_fwdU_zero (j n : ℕ) :
    ((IIM).fwdU n).IsQueryBoundP (sessPred (SS := SS) (RS := RS) (T := T) (M := M) (E := E) j) 0 := by
  change OracleComp.IsQueryBoundP
    (liftM (OracleSpec.query
      (spec := unifSpec + OracleSpec.sigma (fun _ : ℕ => CryptoGames.FSAEAD.spec SS RS (Header T) M E))
      (.inl n)))
    (sessPred j) 0
  rw [← bind_pure (liftM _), isQueryBoundP_query_bind_iff]
  exact ⟨Or.inl (by simp [sessPred]), fun _ => by simp⟩

theorem potInvMultiFS_zero (j : ℕ) {α : Ty SP} {Γ' : List (Ty SP)}
    (c : Comp OO IIM Γ' α) (ρ : Env Γ') (n : ℕ)
    {B : α.denote → ℕ} (hB : ∀ a, B a ≤ n)
    (hq : c.queries (fun _ => 1) (fun _ => 0) = 0) :
    PotOKInvFS (sessPred j) (fun _ => True) B (c.eval ρ) n := by
  refine ⟨fun k hk => ?_⟩
  have hc := ReductionDsl.Comp.queryBound_eval (sessPred j) (fun _ => 1) (fun _ => 0)
    (fun _ _ _ => Nat.le_refl 1) (multiIface_fwdU_zero j) c ρ
  rw [hq] at hc
  exact (isQueryBoundP_bind hc (fun a _ => (hk a trivial).mono (hB a))).mono (by omega)

theorem potInvMultiFS_query (j : ℕ) (g : (IIM).Tag) {Γ' : List (Ty SP)}
    (argE : Expr OO Γ' ((IIM).dom g)) (ρ : Env Γ') (r n : ℕ)
    (hn : (if (argE.eval ρ).1 = j then 1 else 0) + r ≤ n) :
    PotOKInvFS (sessPred j) (fun _ => True) (fun _ => r)
      ((ReductionDsl.Comp.query (I := IIM) g argE).eval ρ) n := by
  refine ⟨fun k hk => ?_⟩
  have hQ : ((ReductionDsl.Comp.query (I := IIM) g argE).eval ρ).IsQueryBoundP (sessPred j)
      (if (argE.eval ρ).1 = j then 1 else 0) := by
    simp only [ReductionDsl.Comp.eval, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
    cases g <;> by_cases h : (argE.eval ρ).1 = j <;> simp [sessPred, h]
  exact (isQueryBoundP_bind hQ (fun a _ => hk a trivial)).mono hn

structure HooksPotSpec (j : ℕ) {hsT : Ty SP}
    (H : HooksC OO IIM (.base .γ) (.base .sig)
      (.sum (.base .ss) .nat) (.sum (.base .rs) .nat) hsT)
    (hPot : hsT.denote → ℕ) : Prop where
  startSend : ∀ {Γ' : List (Ty SP)} (hE : Expr OO Γ' hsT) (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat) (γE : Expr OO Γ' (.base .γ))
    (σE : Expr OO Γ' (.base .sig)) (rE : Expr OO Γ' (.opt (.base .ccoins))) (ρ : Env Γ') (m : ℕ),
    PotOKInvFS (sessPred j) (fun _ => True) (fun res => m + hPot res.2)
      ((H.startSend hE ctxE pE tE γE σE rE).eval ρ) (m + hPot (hE.eval ρ))
  startRecv : ∀ {Γ' : List (Ty SP)} (hE : Expr OO Γ' hsT) (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat) (γE : Expr OO Γ' (.base .γ))
    (σE : Expr OO Γ' (.base .sig)) (tnE : Expr OO Γ' (.base .t)) (ρ : Env Γ') (m : ℕ),
    PotOKInvFS (sessPred j) (fun _ => True) (fun res => m + hPot res.2)
      ((H.startRecv hE ctxE pE tE γE σE tnE).eval ρ) (m + hPot (hE.eval ρ))
  fsSend : ∀ {Γ' : List (Ty SP)} (hE : Expr OO Γ' hsT) (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat) (ssvE : Expr OO Γ' (.sum (.base .ss) .nat))
    (hdrE : Expr OO Γ' hdrTy) (mE : Expr OO Γ' (.base .msg))
    (pairE : Expr OO Γ' (.opt (.prod (.base .msg) (.base .msg)))) (ρ : Env Γ') (m : ℕ),
    PotOKInvFS (sessPred j) (fun _ => True) (fun res => m + hPot res.2)
      ((H.fsSend hE ctxE pE tE ssvE hdrE mE pairE).eval ρ) (1 + m + hPot (hE.eval ρ))
  fsRecv : ∀ {Γ' : List (Ty SP)} (hE : Expr OO Γ' hsT) (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (pE : Expr OO Γ' .bool) (tE : Expr OO Γ' .nat) (rsvE : Expr OO Γ' (.sum (.base .rs) .nat))
    (hdrE : Expr OO Γ' hdrTy) (eE : Expr OO Γ' (.base .ct)) (recE : Expr OO Γ' (.opt cRecTy))
    (ρ : Env Γ') (m : ℕ),
    PotOKInvFS (sessPred j) (fun _ => True) (fun res => m + hPot res.2)
      ((H.fsRecv hE ctxE pE tE rsvE hdrE eE recE).eval ρ) (1 + m + hPot (hE.eval ρ))
  commit : ∀ {Γ' : List (Ty SP)} (hE : Expr OO Γ' hsT) (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (pE : Expr OO Γ' .bool) (oldE newE : Expr OO Γ' mVpTy) (ρ : Env Γ') (m : ℕ),
    PotOKInvFS (sessPred j) (fun _ => True) (fun res => m + hPot res.2)
      ((H.commit hE ctxE pE oldE newE).eval ρ) (m + hPot (hE.eval ρ))
  reveal : ∀ {Γ' : List (Ty SP)} (hE : Expr OO Γ' hsT) (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (pE : Expr OO Γ' .bool) (vpE : Expr OO Γ' mVpTy) (ρ : Env Γ') (m : ℕ),
    PotOKInvFS (sessPred j) (fun _ => True) (fun res => m + hPot res.2)
      ((H.reveal hE ctxE pE vpE).eval ρ) (1 + m + hPot (hE.eval ρ))

private theorem vSendStep1C_gen_potOKInv {j : ℕ} {hsT : Ty SP}
    {H : HooksC OO IIM (.base .γ) (.base .sig) (.sum (.base .ss) .nat) (.sum (.base .rs) .nat) hsT}
    {hPot : hsT.denote → ℕ} (hH : HooksPotSpec j H hPot) {Γ' : List (Ty SP)}
    (hE : Expr OO Γ' hsT) (ctxE : Expr OO Γ' (cGsTy mVpTy)) (pE : Expr OO Γ' .bool)
    (sE : Expr OO Γ' mVpTy) (rE : Expr OO Γ' (.opt (.base .ccoins))) (ρ : Env Γ') (m : ℕ) :
    PotOKInvFS (sessPred j) (fun _ => True) (fun res => m + hPot res.2)
      ((vSendStep1C H hE ctxE pE sE rE).eval ρ) (m + hPot (hE.eval ρ)) := by
  unfold vSendStep1C; rw [eval_bind_ret]
  refine potInvFS_ite (fun _ => ?_) (fun _ => potInvFS_ret trivial (by simp [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))
  rw [eval_bind]
  have hSS := hH.startSend (.fst (ReductionDsl.Expr.v0 (O := OO))) (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))
    (.add (vpTcurNat (.fst (.snd (.snd (.snd .v0))))) (.nat 1))
    (vpΓ (.fst (.snd (.snd (.snd .v0))))) (vpRoot (.fst (.snd (.snd (.snd .v0)))))
    (.snd (.snd (.snd (.snd .v0))))
    (.cons (hE.eval ρ, ctxE.eval ρ, pE.eval ρ, sE.eval ρ, rE.eval ρ) ρ) m
  simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero] at hSS
  refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot hSS (fun _ _ => ?_)
  exact potInvFS_caseOpt
    (fun _ => potInvFS_ret trivial (by simp [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))
    (fun _ _ => potInvFS_ret trivial (by simp [ReductionDsl.Expr.eval, ReductionDsl.Expr.v1]))

theorem vSendC_gen_potOKInv {j : ℕ} {hsT : Ty SP}
    {H : HooksC OO IIM (.base .γ) (.base .sig) (.sum (.base .ss) .nat) (.sum (.base .rs) .nat) hsT}
    {hPot : hsT.denote → ℕ} (hH : HooksPotSpec j H hPot) {Γ' : List (Ty SP)}
    (hE : Expr OO Γ' hsT) (ctxE : Expr OO Γ' (cGsTy mVpTy)) (pE : Expr OO Γ' .bool)
    (sE : Expr OO Γ' mVpTy) (mE : Expr OO Γ' (.base .msg))
    (pairE : Expr OO Γ' (.opt (.prod (.base .msg) (.base .msg))))
    (rE : Expr OO Γ' (.opt (.base .ccoins))) (ρ : Env Γ') (m : ℕ) :
    PotOKInvFS (sessPred j) (fun _ => True) (fun res => m + hPot res.2)
      ((vSendC H hE ctxE pE sE mE pairE rE).eval ρ) (1 + m + hPot (hE.eval ρ)) := by
  unfold vSendC; rw [eval_bind_ret, eval_bind]
  have h1 := vSendStep1C_gen_potOKInv hH (.fst (ReductionDsl.Expr.v0 (O := OO)))
    (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0))))
    (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))
    (.cons (hE.eval ρ, ctxE.eval ρ, pE.eval ρ, sE.eval ρ, mE.eval ρ, pairE.eval ρ, rE.eval ρ) ρ) (1 + m)
  simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero] at h1
  refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot h1 (fun step1Out _ => ?_)
  refine potInvFS_caseOpt
    (fun _ => potInvFS_ret trivial (by simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero]; omega))
    (fun s1 _ => potInvFS_caseOpt
      (fun _ => potInvFS_ret trivial (by simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v1, ReductionDsl.Env.get_cons_succ, ReductionDsl.Env.get_cons_zero]; omega))
      (fun v _ => ?_))
  rw [eval_bind]
  have hFS := hH.fsSend (.snd (ReductionDsl.Expr.v2 (O := OO))) (.fst (.snd .v3)) (.fst (.snd (.snd .v3)))
    (vpTcurNat .v1) .v0 (.pair (vpTcurNat .v1) (vpTcur .v1))
    (.fst (.snd (.snd (.snd (.snd .v3))))) (.fst (.snd (.snd (.snd (.snd (.snd .v3))))))
    (.cons v (.cons s1 (.cons step1Out
      (.cons (hE.eval ρ, ctxE.eval ρ, pE.eval ρ, sE.eval ρ, mE.eval ρ, pairE.eval ρ, rE.eval ρ) ρ)))) m
  simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v2, ReductionDsl.Env.get_cons_zero, ReductionDsl.Env.get_cons_succ] at hFS
  refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot hFS (fun _ _ => ?_)
  exact potInvFS_caseOpt
    (fun _ => potInvFS_ret trivial (by simp [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))
    (fun _ _ => potInvFS_ret trivial (by simp [ReductionDsl.Expr.eval, ReductionDsl.Expr.v1]))

private theorem vRecvStep1C_gen_potOKInv {j : ℕ} {hsT : Ty SP}
    {H : HooksC OO IIM (.base .γ) (.base .sig) (.sum (.base .ss) .nat) (.sum (.base .rs) .nat) hsT}
    {hPot : hsT.denote → ℕ} (hH : HooksPotSpec j H hPot) {Γ' : List (Ty SP)}
    (hE : Expr OO Γ' hsT) (ctxE : Expr OO Γ' (cGsTy mVpTy)) (pE : Expr OO Γ' .bool)
    (sE : Expr OO Γ' mVpTy) (cE : Expr OO Γ' hdrCtTy) (ρ : Env Γ') (m : ℕ) :
    PotOKInvFS (sessPred j) (fun _ => True) (fun res => m + hPot res.2)
      ((vRecvStep1C H hE ctxE pE sE cE).eval ρ) (m + hPot (hE.eval ρ)) := by
  unfold vRecvStep1C; rw [eval_bind_ret]
  refine potInvFS_ite (fun _ => ?_) (fun _ => potInvFS_ret trivial (by simp [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))
  refine potInvFS_caseOpt
    (fun _ => potInvFS_ret trivial (by simp [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))
    (fun Tn _ => ?_)
  rw [eval_bind]
  have hSR := hH.startRecv (.fst (ReductionDsl.Expr.v1 (O := OO))) (.fst (.snd .v1)) (.fst (.snd (.snd .v1)))
    (.fst (.fst (.snd (.snd (.snd (.snd .v1))))))
    (vpΓ (.fst (.snd (.snd (.snd .v1))))) (vpRoot (.fst (.snd (.snd (.snd .v1))))) .v0
    (.cons Tn (.cons (hE.eval ρ, ctxE.eval ρ, pE.eval ρ, sE.eval ρ, cE.eval ρ) ρ)) m
  simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v1, ReductionDsl.Env.get_cons_zero, ReductionDsl.Env.get_cons_succ] at hSR
  refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot hSR (fun _ _ => ?_)
  exact potInvFS_caseOpt
    (fun _ => potInvFS_ret trivial (by simp [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))
    (fun _ _ => potInvFS_caseOpt
      (fun _ => potInvFS_ret trivial (by simp [ReductionDsl.Expr.eval, ReductionDsl.Expr.v1]))
      (fun _ _ => potInvFS_ret trivial (by simp [ReductionDsl.Expr.eval, ReductionDsl.Expr.v2])))

private theorem vRecvC_gen_potOKInv {j : ℕ} {hsT : Ty SP}
    {H : HooksC OO IIM (.base .γ) (.base .sig) (.sum (.base .ss) .nat) (.sum (.base .rs) .nat) hsT}
    {hPot : hsT.denote → ℕ} (hH : HooksPotSpec j H hPot) {Γ' : List (Ty SP)}
    (hE : Expr OO Γ' hsT) (ctxE : Expr OO Γ' (cGsTy mVpTy)) (pE : Expr OO Γ' .bool)
    (sE : Expr OO Γ' mVpTy) (cE : Expr OO Γ' hdrCtTy)
    (recE : Expr OO Γ' (.opt cRecTy)) (ρ : Env Γ') (m : ℕ) :
    PotOKInvFS (sessPred j) (fun _ => True) (fun res => m + hPot res.2)
      ((vRecvC H hE ctxE pE sE cE recE).eval ρ) (1 + m + hPot (hE.eval ρ)) := by
  unfold vRecvC; rw [eval_bind_ret]
  refine potInvFS_ite
    (fun _ => potInvFS_ret trivial (by simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero]; omega))
    (fun _ => ?_)
  rw [eval_bind]
  have hStep1 := vRecvStep1C_gen_potOKInv hH (.fst (ReductionDsl.Expr.v0 (O := OO)))
    (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0))))
    (.fst (.snd (.snd (.snd (.snd .v0)))))
    (.cons (hE.eval ρ, ctxE.eval ρ, pE.eval ρ, sE.eval ρ, cE.eval ρ, recE.eval ρ) ρ) (1 + m)
  simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero] at hStep1
  refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot hStep1 (fun step1Out _ => ?_)
  refine potInvFS_caseOpt
    (fun _ => potInvFS_ret trivial (by simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero]; omega))
    (fun step1In _ => potInvFS_caseOpt
      (fun _ => potInvFS_ret trivial (by simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v1, ReductionDsl.Env.get_cons_succ, ReductionDsl.Env.get_cons_zero]; omega))
      (fun s1 _ => potInvFS_caseOpt
        (fun _ => potInvFS_ret trivial (by simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v2, ReductionDsl.Env.get_cons_succ, ReductionDsl.Env.get_cons_zero]; omega))
        (fun v _ => ?_)))
  rw [eval_bind]
  have hFR := hH.fsRecv (.snd (ReductionDsl.Expr.v3 (O := OO))) (.fst (.snd .v4)) (.fst (.snd (.snd .v4)))
    (.fst (.fst (.fst (.snd (.snd (.snd (.snd .v4))))))) .v0
    (.fst (.fst (.snd (.snd (.snd (.snd .v4)))))) (.snd (.fst (.snd (.snd (.snd (.snd .v4))))))
    (.snd (.snd (.snd (.snd (.snd .v4)))))
    (.cons v (.cons s1 (.cons step1In (.cons step1Out
      (.cons (hE.eval ρ, ctxE.eval ρ, pE.eval ρ, sE.eval ρ, cE.eval ρ, recE.eval ρ) ρ))))) m
  simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v3, ReductionDsl.Env.get_cons_zero, ReductionDsl.Env.get_cons_succ] at hFR
  refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot hFR (fun _ _ => ?_)
  exact potInvFS_caseOpt
    (fun _ => potInvFS_ret trivial (by simp [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))
    (fun _ _ => potInvFS_caseOpt
      (fun _ => potInvFS_ret trivial (by simp [ReductionDsl.Expr.eval, ReductionDsl.Expr.v1]))
      (fun _ _ => potInvFS_ret trivial (by simp [ReductionDsl.Expr.eval, ReductionDsl.Expr.v2])))

@[expose] def esPot {hsT : Ty SP} (hPot : hsT.denote → ℕ) (es : (esTy mVpTy hsT).denote) : ℕ :=
  hPot es.2.1

private theorem commitEC_gen_potOKInv {j : ℕ} {hsT : Ty SP}
    {H : HooksC OO IIM (.base .γ) (.base .sig) (.sum (.base .ss) .nat) (.sum (.base .rs) .nat) hsT}
    {hPot : hsT.denote → ℕ} (hH : HooksPotSpec j H hPot) (L : ℕ)
    {Γ' : List (Ty SP)} (esE : Expr OO Γ' (esTy mVpTy hsT))
    (sE : Expr OO Γ' (cGsTy mVpTy)) (pE : Expr OO Γ' .bool)
    (oldE newE : Expr OO Γ' mVpTy) (posE : Expr OO Γ' posTy)
    (ρ : Env Γ') (m : ℕ) :
    PotOKInvFS (sessPred j) (fun _ => True) (fun res => m + esPot hPot res.2)
      ((commitEC H L esE sE pE oldE newE posE).eval ρ)
      (m + esPot hPot (esE.eval ρ)) := by
  unfold commitEC; rw [eval_bind_ret, eval_bind]
  have hFC := hH.commit (esH (.fst (ReductionDsl.Expr.v0 (O := OO)))) (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))
    (.fst (.snd (.snd (.snd .v0)))) (.snd (.snd (.snd (.snd .v0))))
    (.cons ((esE.pair ((cAcceptE L sE pE newE posE).pair (pE.pair (oldE.pair newE)))).eval ρ) ρ) m
  have hEq : m + hPot ((esH (.fst (ReductionDsl.Expr.v0 (O := OO)))).eval
      (.cons ((esE.pair ((cAcceptE L sE pE newE posE).pair
        (pE.pair (oldE.pair newE)))).eval ρ) ρ)) = m + esPot hPot (esE.eval ρ) := rfl
  rw [hEq] at hFC
  refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot hFC (fun _ _ => ?_)
  exact potInvFS_caseOpt
    (fun _ => potInvFS_ret trivial (by simp [esPot, esMk, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))
    (fun _ _ => potInvFS_ret trivial (by simp [esPot, esMk, ReductionDsl.Expr.eval, ReductionDsl.Expr.v1]))

private theorem transmitEC_gen_potOKInv {j : ℕ} {hsT : Ty SP}
    {H : HooksC OO IIM (.base .γ) (.base .sig) (.sum (.base .ss) .nat) (.sum (.base .rs) .nat) hsT}
    {hPot : hsT.denote → ℕ} (hH : HooksPotSpec j H hPot) (L Δ qep : ℕ) (π : Policy)
    {Γ' : List (Ty SP)} (esE : Expr OO Γ' (esTy mVpTy hsT))
    (argE : Expr OO Γ' (.prod .bool (.prod (.base .msg) (.opt (.base .ccoins)))))
    (ρ : Env Γ') (m : ℕ) :
    PotOKInvFS (sessPred j) (fun _ => True) (fun x => m + esPot hPot x.2)
      ((transmitEC H L Δ qep π esE argE).eval ρ) (1 + m + esPot hPot (esE.eval ρ)) := by
  unfold transmitEC; rw [eval_bind_ret]
  refine potInvFS_ite
    (fun _ => potInvFS_ret trivial (by simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero]; omega))
    (fun _ => potInvFS_caseOpt
      (fun _ => potInvFS_ret trivial (by simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero]; omega))
      (fun s1 _ => ?_))
  refine potInvFS_ite
    (fun _ => potInvFS_ret trivial (by simp only [esPot, esSetAbort, esMk, esH, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1,
      ReductionDsl.Env.get_cons_zero, ReductionDsl.Env.get_cons_succ]; omega))
    (fun _ => ?_)
  rw [eval_bind]
  have hSend := vSendC_gen_potOKInv hH (esH (.fst (ReductionDsl.Expr.v1 (O := OO)))) .v0 (.fst (.snd .v1))
    (pGet (cGsSt .v0) (.fst (.snd .v1))) (.fst (.snd (.snd .v1))) .none (.snd (.snd (.snd .v1)))
    (.cons s1 (.cons (esE.eval ρ, argE.eval ρ) ρ)) m
  simp only [esH, ReductionDsl.Expr.eval, ReductionDsl.Expr.v1, ReductionDsl.Env.get_cons_zero, ReductionDsl.Env.get_cons_succ] at hSend
  refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot hSend (fun _ _ => ?_)
  exact potInvFS_caseOpt
    (fun _ => potInvFS_ret trivial (by simp [esPot, esMk, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))
    (fun _ _ => potInvFS_ret trivial (by simp [esPot, esMk, ReductionDsl.Expr.eval, ReductionDsl.Expr.v1]))

private theorem challEC_gen_potOKInv {j : ℕ} {hsT : Ty SP}
    {H : HooksC OO IIM (.base .γ) (.base .sig) (.sum (.base .ss) .nat) (.sum (.base .rs) .nat) hsT}
    {hPot : hsT.denote → ℕ} (hH : HooksPotSpec j H hPot) (L Δ qep : ℕ)
    (cfg : ConfigEC OO) (π : Policy)
    {Γ' : List (Ty SP)} (esE : Expr OO Γ' (esTy mVpTy hsT))
    (argE : Expr OO Γ' (.prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .ccoins))))))
    (ρ : Env Γ') (m : ℕ) :
    PotOKInvFS (sessPred j) (fun _ => True) (fun x => m + esPot hPot x.2)
      ((challEC H L Δ qep cfg π esE argE).eval ρ) (1 + m + esPot hPot (esE.eval ρ)) := by
  unfold challEC; rw [eval_bind_ret]
  refine potInvFS_ite
    (fun _ => potInvFS_ret trivial (by simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero]; omega))
    (fun _ => potInvFS_caseOpt
      (fun _ => potInvFS_ret trivial (by simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero]; omega))
      (fun s1 _ => ?_))
  refine potInvFS_ite
    (fun _ => potInvFS_ret trivial (by simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v1, ReductionDsl.Env.get_cons_succ, ReductionDsl.Env.get_cons_zero]; omega))
    (fun _ => potInvFS_ite
      (fun _ => potInvFS_ret trivial (by simp only [esPot, esSetAbort, esMk, esH, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1,
        ReductionDsl.Env.get_cons_zero, ReductionDsl.Env.get_cons_succ]; omega))
      (fun _ => ?_))
  rw [eval_bind]
  have hSend := vSendC_gen_potOKInv hH (esH (.fst (ReductionDsl.Expr.v1 (O := OO)))) .v0 (.fst (.snd .v1))
    (pGet (cGsSt .v0) (.fst (.snd .v1)))
    (cfg.challMsgE (pGet (cGsEpoch .v0) (.fst (.snd .v1))) (cGsB (esG (.fst .v1)))
      (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1)))))
    (.some (.pair (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1))))))
    (.snd (.snd (.snd (.snd .v1)))) (.cons s1 (.cons (esE.eval ρ, argE.eval ρ) ρ)) m
  simp only [esH, ReductionDsl.Expr.eval, ReductionDsl.Expr.v1, ReductionDsl.Env.get_cons_zero, ReductionDsl.Env.get_cons_succ] at hSend
  refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot hSend (fun _ _ => ?_)
  exact potInvFS_caseOpt
    (fun _ => potInvFS_ret trivial (by simp [esPot, esMk, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))
    (fun _ _ => potInvFS_ret trivial (by simp [esPot, esMk, ReductionDsl.Expr.eval, ReductionDsl.Expr.v1]))

theorem deliverEC_gen_potOKInv {j : ℕ} {hsT : Ty SP}
    {H : HooksC OO IIM (.base .γ) (.base .sig) (.sum (.base .ss) .nat) (.sum (.base .rs) .nat) hsT}
    {hPot : hsT.denote → ℕ} (hH : HooksPotSpec j H hPot) (L maxSkip : ℕ) (cfg : ConfigEC OO)
    {Γ' : List (Ty SP)} (esE : Expr OO Γ' (esTy mVpTy hsT)) (argE : Expr OO Γ' (.prod .bool hdrCtTy))
    (ρ : Env Γ') (m : ℕ) :
    PotOKInvFS (sessPred j) (fun _ => True) (fun x => m + esPot hPot x.2)
      ((deliverEC H L maxSkip cfg esE argE).eval ρ) (1 + m + esPot hPot (esE.eval ρ)) := by
  unfold deliverEC; rw [eval_bind_ret]
  refine potInvFS_ite
    (fun _ => potInvFS_ret trivial (by simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero]; omega))
    (fun _ => potInvFS_caseOpt
      (fun _ => potInvFS_ret trivial (by simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero]; omega))
      (fun r1 _ => ?_))
  rw [eval_bind]
  have hRecv := vRecvC_gen_potOKInv hH (esH (.fst (ReductionDsl.Expr.v1 (O := OO)))) (esG (.fst .v1))
    (.fst (.snd .v1)) (pGet (cGsSt (esG (.fst .v1))) (.fst (.snd .v1))) (.snd (.snd .v1)) (.some .v0)
    (.cons r1 (.cons (esE.eval ρ, argE.eval ρ) ρ)) m
  simp only [esH, ReductionDsl.Expr.eval, ReductionDsl.Expr.v1, ReductionDsl.Env.get_cons_zero, ReductionDsl.Env.get_cons_succ] at hRecv
  refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot hRecv (fun recvOut _ => ?_)
  refine potInvFS_caseOpt
    (fun _ => potInvFS_ret trivial (by simp [esPot, esMk, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))
    (fun resIn _ => potInvFS_caseOpt
      (fun _ => potInvFS_ret trivial (by simp [esPot, esMk, ReductionDsl.Expr.eval, ReductionDsl.Expr.v1]))
      (fun tup _ => ?_))
  rw [eval_bind]
  have hCom := commitEC_gen_potOKInv hH L (esSetH (.fst (ReductionDsl.Expr.v4 (O := OO))) (.snd .v2))
    (esG (.fst .v4)) (.fst (.snd .v4)) (pGet (cGsSt (esG (.fst .v4))) (.fst (.snd .v4)))
    (.fst .v0) (cRecPos .v3)
    (.cons tup (.cons resIn (.cons recvOut (.cons r1 (.cons (esE.eval ρ, argE.eval ρ) ρ))))) m
  simp only [esPot, esSetH, esMk, ReductionDsl.Expr.eval, ReductionDsl.Expr.v2, ReductionDsl.Env.get_cons_zero, ReductionDsl.Env.get_cons_succ] at hCom
  refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot hCom (fun _ _ => ?_)
  exact potInvFS_caseOpt
    (fun _ => potInvFS_ret trivial (by simp [esPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))
    (fun _ _ => potInvFS_ret trivial (by simp [esPot, esSetG, esMk, esH, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1]))

theorem injectEC_gen_potOKInv {j : ℕ} {hsT : Ty SP}
    {H : HooksC OO IIM (.base .γ) (.base .sig) (.sum (.base .ss) .nat) (.sum (.base .rs) .nat) hsT}
    {hPot : hsT.denote → ℕ} (hH : HooksPotSpec j H hPot) (L Δ qep : ℕ) (cfg : ConfigEC OO)
    {Γ' : List (Ty SP)} (esE : Expr OO Γ' (esTy mVpTy hsT)) (argE : Expr OO Γ' (.prod .bool hdrCtTy))
    (ρ : Env Γ') (m : ℕ) :
    PotOKInvFS (sessPred j) (fun _ => True) (fun x => m + esPot hPot x.2)
      ((injectEC H L Δ qep cfg esE argE).eval ρ) (1 + m + esPot hPot (esE.eval ρ)) := by
  unfold injectEC; rw [eval_bind_ret]
  refine potInvFS_ite
    (fun _ => potInvFS_ret trivial (by simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero]; omega))
    (fun _ => ?_)
  rw [eval_bind]
  have hRecv := vRecvC_gen_potOKInv hH (esH (.fst (ReductionDsl.Expr.v0 (O := OO)))) (esG (.fst .v0))
    (.fst (.snd .v0)) (pGet (cGsSt (esG (.fst .v0))) (.fst (.snd .v0))) (.snd (.snd .v0)) .none
    (.cons (esE.eval ρ, argE.eval ρ) ρ) m
  simp only [esH, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero] at hRecv
  refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot hRecv (fun recvOut _ => ?_)
  refine potInvFS_caseOpt
    (fun _ => potInvFS_ret trivial (by simp [esPot, esMk, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))
    (fun resIn _ => potInvFS_caseOpt
      (fun _ => potInvFS_ret trivial (by simp [esPot, esSetH, esMk, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1]))
      (fun tup _ => potInvFS_ite
        (fun _ => potInvFS_ret trivial (by simp [esPot, esSetH, esMk, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v2]))
        (fun _ => potInvFS_ite (fun _ => ?_)
          (fun _ => potInvFS_ret trivial
            (by simp [esPot, esSetG, esSetH, esMk, esH, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v2])))))
  rw [eval_bind]
  have hCom := commitEC_gen_potOKInv hH L (esSetH (.fst (ReductionDsl.Expr.v3 (O := OO))) (.snd .v2))
    (esG (.fst .v3)) (.fst (.snd .v3)) (pGet (cGsSt (esG (.fst .v3))) (.fst (.snd .v3)))
    (.fst .v0) (.pair (otherE (.fst (.snd .v3))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
    (.cons tup (.cons resIn (.cons recvOut (.cons (esE.eval ρ, argE.eval ρ) ρ)))) m
  simp only [esPot, esSetH, esMk, ReductionDsl.Expr.eval, ReductionDsl.Expr.v2, ReductionDsl.Env.get_cons_zero, ReductionDsl.Env.get_cons_succ] at hCom
  refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot hCom (fun _ _ => ?_)
  exact potInvFS_caseOpt
    (fun _ => potInvFS_ret trivial (by simp [esPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))
    (fun _ _ => potInvFS_ret trivial (by simp [esPot, esSetG, esMk, esH, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1]))

private theorem injectECB1_gen_potOKInv {j : ℕ} {hsT : Ty SP}
    {H : HooksC OO IIM (.base .γ) (.base .sig) (.sum (.base .ss) .nat) (.sum (.base .rs) .nat) hsT}
    {hPot : hsT.denote → ℕ} (hH : HooksPotSpec j H hPot) (L qep tStar : ℕ) (cfg : ConfigEC OO)
    {Γ' : List (Ty SP)} (esE : Expr OO Γ' (esTy mVpTy hsT)) (argE : Expr OO Γ' (.prod .bool hdrCtTy))
    (ρ : Env Γ') (m : ℕ) :
    PotOKInvFS (sessPred j) (fun _ => True) (fun x => m + esPot hPot x.2)
      ((injectECB1 H L qep tStar cfg esE argE).eval ρ) (1 + m + esPot hPot (esE.eval ρ)) := by
  unfold injectECB1; rw [eval_bind_ret]
  refine potInvFS_ite
    (fun _ => potInvFS_ret trivial (by simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero]; omega))
    (fun _ => ?_)
  rw [eval_bind]
  have hRecv := vRecvC_gen_potOKInv hH (esH (.fst (ReductionDsl.Expr.v0 (O := OO)))) (esG (.fst .v0))
    (.fst (.snd .v0)) (pGet (cGsSt (esG (.fst .v0))) (.fst (.snd .v0))) (.snd (.snd .v0)) .none
    (.cons (esE.eval ρ, argE.eval ρ) ρ) m
  simp only [esH, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero] at hRecv
  refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot hRecv (fun recvOut _ => ?_)
  refine potInvFS_caseOpt
    (fun _ => potInvFS_ret trivial (by simp [esPot, esMk, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))
    (fun resIn _ => potInvFS_caseOpt
      (fun _ => potInvFS_ret trivial (by simp [esPot, esSetH, esMk, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1]))
      (fun tup _ => potInvFS_ite
        (fun _ => potInvFS_ret trivial (by simp [esPot, esSetH, esMk, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v2]))
        (fun _ => potInvFS_ite (fun _ => ?_)
          (fun _ => potInvFS_ret trivial
            (by simp [esPot, esSetG, esSetH, esMk, esH, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v2])))))
  rw [eval_bind]
  have hCom := commitEC_gen_potOKInv hH L (esSetH (.fst (ReductionDsl.Expr.v3 (O := OO))) (.snd .v2))
    (esG (.fst .v3)) (.fst (.snd .v3)) (pGet (cGsSt (esG (.fst .v3))) (.fst (.snd .v3)))
    (.fst .v0) (.pair (otherE (.fst (.snd .v3))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
    (.cons tup (.cons resIn (.cons recvOut (.cons (esE.eval ρ, argE.eval ρ) ρ)))) m
  simp only [esPot, esSetH, esMk, ReductionDsl.Expr.eval, ReductionDsl.Expr.v2, ReductionDsl.Env.get_cons_zero, ReductionDsl.Env.get_cons_succ] at hCom
  refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot hCom (fun _ _ => ?_)
  exact potInvFS_caseOpt
    (fun _ => potInvFS_ret trivial (by simp [esPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))
    (fun _ _ => potInvFS_ret trivial (by simp [esPot, esSetG, esMk, esH, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1]))

private theorem corrECPaper_gen_potOKInv {j : ℕ} {hsT : Ty SP}
    {H : HooksC OO IIM (.base .γ) (.base .sig) (.sum (.base .ss) .nat) (.sum (.base .rs) .nat) hsT}
    {hPot : hsT.denote → ℕ} (hH : HooksPotSpec j H hPot) (L : ℕ) (π : Policy)
    {Γ' : List (Ty SP)} (esE : Expr OO Γ' (esTy mVpTy hsT)) (pE : Expr OO Γ' .bool)
    (ρ : Env Γ') (m : ℕ) :
    PotOKInvFS (sessPred j) (fun _ => True) (fun x => m + esPot hPot x.2)
      ((corrECPaper H L π esE pE).eval ρ) (1 + m + esPot hPot (esE.eval ρ)) := by
  unfold corrECPaper; rw [eval_bind_ret]
  refine potInvFS_ite
    (fun _ => potInvFS_ret trivial (by simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero]; omega))
    (fun _ => potInvFS_ite
      (fun _ => potInvFS_ret trivial
        (by simp only [esPot, esSetAbort, esMk, esH, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero]; omega))
      (fun _ => ?_))
  rw [eval_bind]
  have hRev := hH.reveal (esH (.fst (ReductionDsl.Expr.v0 (O := OO)))) (esG (.fst .v0)) (.snd .v0)
    (pGet (cGsSt (esG (.fst .v0))) (.snd .v0)) (.cons (esE.eval ρ, pE.eval ρ) ρ) m
  simp only [esH, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero] at hRev
  refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot hRev (fun _ _ => ?_)
  exact potInvFS_caseOpt (fun _ => potInvFS_ret trivial (by simp [esPot, esMk, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))
    (fun _ _ => potInvFS_ret trivial (by simp [esPot, esMk, ReductionDsl.Expr.eval, ReductionDsl.Expr.v1]))

private theorem corrECShiftedPaper_gen_potOKInv {j : ℕ} {hsT : Ty SP}
    {H : HooksC OO IIM (.base .γ) (.base .sig) (.sum (.base .ss) .nat) (.sum (.base .rs) .nat) hsT}
    {hPot : hsT.denote → ℕ} (hH : HooksPotSpec j H hPot) (L l : ℕ) (π : Policy)
    {Γ' : List (Ty SP)} (esE : Expr OO Γ' (esTy mVpTy hsT)) (pE : Expr OO Γ' .bool)
    (ρ : Env Γ') (m : ℕ) :
    PotOKInvFS (sessPred j) (fun _ => True) (fun x => m + esPot hPot x.2)
      ((corrECShiftedPaper H L l π esE pE).eval ρ) (1 + m + esPot hPot (esE.eval ρ)) := by
  unfold corrECShiftedPaper; rw [eval_bind_ret]
  refine potInvFS_ite
    (fun _ => potInvFS_ret trivial (by simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero]; omega))
    (fun _ => potInvFS_ite
      (fun _ => potInvFS_ret trivial
        (by simp only [esPot, esSetAbort, esMk, esH, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero]; omega))
      (fun _ => ?_))
  rw [eval_bind]
  have hRev := hH.reveal (esH (.fst (ReductionDsl.Expr.v0 (O := OO)))) (esG (.fst .v0)) (.snd .v0)
    (pGet (cGsSt (esG (.fst .v0))) (.snd .v0)) (.cons (esE.eval ρ, pE.eval ρ) ρ) m
  simp only [esH, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero] at hRev
  refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot hRev (fun _ _ => ?_)
  exact potInvFS_caseOpt (fun _ => potInvFS_ret trivial (by simp [esPot, esMk, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))
    (fun _ _ => potInvFS_ret trivial (by simp [esPot, esMk, ReductionDsl.Expr.eval, ReductionDsl.Expr.v1]))

theorem deliverForgeEC_gen_potOKInv {j : ℕ} {hsT : Ty SP}
    {H : HooksC OO IIM (.base .γ) (.base .sig) (.sum (.base .ss) .nat) (.sum (.base .rs) .nat) hsT}
    {hPot : hsT.denote → ℕ} (hH : HooksPotSpec j H hPot) (L Δ qep : ℕ) (cfg : ConfigEC OO)
    {Γ' : List (Ty SP)} (esE : Expr OO Γ' (esTy mVpTy hsT))
    (argE : Expr OO Γ' (.prod .bool (.prod hdrCtTy hdrCtTy))) (ρ : Env Γ') (m : ℕ) :
    PotOKInvFS (sessPred j) (fun _ => True) (fun x => m + esPot hPot x.2)
      ((deliverForgeEC H L Δ qep cfg esE argE).eval ρ) (1 + m + esPot hPot (esE.eval ρ)) := by
  unfold deliverForgeEC; rw [eval_bind_ret]
  refine potInvFS_ite
    (fun _ => potInvFS_ret trivial (by simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero]; omega))
    (fun _ => potInvFS_caseOpt
      (fun _ => potInvFS_ret trivial (by simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero]; omega))
      (fun r1 _ => potInvFS_ite
        (fun _ => potInvFS_ret trivial (by simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v1, ReductionDsl.Env.get_cons_succ, ReductionDsl.Env.get_cons_zero]; omega))
        (fun _ => ?_)))
  rw [eval_bind]
  have hRecv := vRecvC_gen_potOKInv hH (esH (.fst (ReductionDsl.Expr.v1 (O := OO)))) (esG (.fst .v1))
    (.fst (.snd .v1)) (pGet (cGsSt (esG (.fst .v1))) (.fst (.snd .v1))) (.snd (.snd (.snd .v1))) .none
    (.cons r1 (.cons (esE.eval ρ, argE.eval ρ) ρ)) m
  simp only [esH, ReductionDsl.Expr.eval, ReductionDsl.Expr.v1, ReductionDsl.Env.get_cons_zero, ReductionDsl.Env.get_cons_succ] at hRecv
  refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot hRecv (fun recvOut _ => ?_)
  refine potInvFS_caseOpt (fun _ => potInvFS_ret trivial (by simp [esPot, esMk, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))
    (fun resIn _ => potInvFS_caseOpt
      (fun _ => potInvFS_ret trivial (by simp [esPot, esSetH, esMk, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1]))
      (fun tup _ => potInvFS_ite
        (fun _ => potInvFS_ret trivial (by simp [esPot, esSetH, esMk, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v2]))
        (fun _ => potInvFS_ite (fun _ => ?_)
          (fun _ => potInvFS_ret trivial (by simp [esPot, esSetG, esSetH, esMk, esH, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v2])))))
  rw [eval_bind]
  have hCom := commitEC_gen_potOKInv hH L (esSetH (.fst (ReductionDsl.Expr.v4 (O := OO))) (.snd .v2))
    (esG (.fst .v4)) (.fst (.snd .v4)) (pGet (cGsSt (esG (.fst .v4))) (.fst (.snd .v4)))
    (.fst .v0) (.pair (otherE (.fst (.snd .v4))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
    (.cons tup (.cons resIn (.cons recvOut (.cons r1 (.cons (esE.eval ρ, argE.eval ρ) ρ))))) m
  simp only [esPot, esSetH, esMk, ReductionDsl.Expr.eval, ReductionDsl.Expr.v2, ReductionDsl.Env.get_cons_zero, ReductionDsl.Env.get_cons_succ] at hCom
  refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot hCom (fun _ _ => ?_)
  exact potInvFS_caseOpt (fun _ => potInvFS_ret trivial (by simp [esPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))
    (fun _ _ => potInvFS_ret trivial (by simp [esPot, esSetG, esMk, esH, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1]))

private theorem deliverForgeECB1_gen_potOKInv {j : ℕ} {hsT : Ty SP}
    {H : HooksC OO IIM (.base .γ) (.base .sig) (.sum (.base .ss) .nat) (.sum (.base .rs) .nat) hsT}
    {hPot : hsT.denote → ℕ} (hH : HooksPotSpec j H hPot) (L qep tStar : ℕ) (cfg : ConfigEC OO)
    {Γ' : List (Ty SP)} (esE : Expr OO Γ' (esTy mVpTy hsT))
    (argE : Expr OO Γ' (.prod .bool (.prod hdrCtTy hdrCtTy))) (ρ : Env Γ') (m : ℕ) :
    PotOKInvFS (sessPred j) (fun _ => True) (fun x => m + esPot hPot x.2)
      ((deliverForgeECB1 H L qep tStar cfg esE argE).eval ρ) (1 + m + esPot hPot (esE.eval ρ)) := by
  unfold deliverForgeECB1; rw [eval_bind_ret]
  refine potInvFS_ite
    (fun _ => potInvFS_ret trivial (by simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero]; omega))
    (fun _ => potInvFS_caseOpt
      (fun _ => potInvFS_ret trivial (by simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero]; omega))
      (fun r1 _ => potInvFS_ite
        (fun _ => potInvFS_ret trivial (by simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v1, ReductionDsl.Env.get_cons_succ, ReductionDsl.Env.get_cons_zero]; omega))
        (fun _ => ?_)))
  rw [eval_bind]
  have hRecv := vRecvC_gen_potOKInv hH (esH (.fst (ReductionDsl.Expr.v1 (O := OO)))) (esG (.fst .v1))
    (.fst (.snd .v1)) (pGet (cGsSt (esG (.fst .v1))) (.fst (.snd .v1))) (.snd (.snd (.snd .v1))) .none
    (.cons r1 (.cons (esE.eval ρ, argE.eval ρ) ρ)) m
  simp only [esH, ReductionDsl.Expr.eval, ReductionDsl.Expr.v1, ReductionDsl.Env.get_cons_zero, ReductionDsl.Env.get_cons_succ] at hRecv
  refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot hRecv (fun recvOut _ => ?_)
  refine potInvFS_caseOpt (fun _ => potInvFS_ret trivial (by simp [esPot, esMk, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))
    (fun resIn _ => potInvFS_caseOpt
      (fun _ => potInvFS_ret trivial (by simp [esPot, esSetH, esMk, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1]))
      (fun tup _ => potInvFS_ite
        (fun _ => potInvFS_ret trivial (by simp [esPot, esSetH, esMk, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v2]))
        (fun _ => potInvFS_ite (fun _ => ?_)
          (fun _ => potInvFS_ret trivial (by simp [esPot, esSetG, esSetH, esMk, esH, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v2])))))
  rw [eval_bind]
  have hCom := commitEC_gen_potOKInv hH L (esSetH (.fst (ReductionDsl.Expr.v4 (O := OO))) (.snd .v2))
    (esG (.fst .v4)) (.fst (.snd .v4)) (pGet (cGsSt (esG (.fst .v4))) (.fst (.snd .v4)))
    (.fst .v0) (.pair (otherE (.fst (.snd .v4))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
    (.cons tup (.cons resIn (.cons recvOut (.cons r1 (.cons (esE.eval ρ, argE.eval ρ) ρ))))) m
  simp only [esPot, esSetH, esMk, ReductionDsl.Expr.eval, ReductionDsl.Expr.v2, ReductionDsl.Env.get_cons_zero, ReductionDsl.Env.get_cons_succ] at hCom
  refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot hCom (fun _ _ => ?_)
  exact potInvFS_caseOpt (fun _ => potInvFS_ret trivial (by simp [esPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))
    (fun _ _ => potInvFS_ret trivial (by simp [esPot, esSetG, esMk, esH, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1]))

private theorem implECPaper_gen_potOKInv {j : ℕ} {hsT : Ty SP}
    {H : HooksC OO IIM (.base .γ) (.base .sig) (.sum (.base .ss) .nat) (.sum (.base .rs) .nat) hsT}
    {hPot : hsT.denote → ℕ} (hH : HooksPotSpec j H hPot) (L Δ qep maxSkip : ℕ) (cfg : ConfigEC OO) (π : Policy)
    {Γ' : List (Ty SP)} (esE : Expr OO Γ' (esTy mVpTy hsT))
    (qE : Expr OO Γ' (ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E)) (ρ : Env Γ') (m : ℕ) :
    PotOKInvFS (sessPred j) (fun _ => True) (fun x => m + esPot hPot x.2)
      ((implECPaper H L Δ qep maxSkip cfg π esE qE).eval ρ) (1 + m + esPot hPot (esE.eval ρ)) := by
  unfold implECPaper; rw [eval_bind_ret]
  refine potInvFS_caseSum (fun _ _ => potInvFS_caseSum (fun _ _ => potInvFS_caseSum
    (fun _ _ => potInvFS_caseSum (fun _ _ => ?_) (fun _ _ => ?_)) (fun _ _ => ?_)) (fun _ _ => ?_)) (fun _ _ => ?_)
  · rw [eval_bind]; exact Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot (transmitEC_gen_potOKInv hH L Δ qep π (.fst (ReductionDsl.Expr.v4 (O := OO))) .v0 _ m)
      (fun _ _ => potInvFS_ret trivial (by simp [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))
  · rw [eval_bind]; exact Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot (challEC_gen_potOKInv hH L Δ qep cfg π (.fst (ReductionDsl.Expr.v4 (O := OO))) .v0 _ m)
      (fun _ _ => potInvFS_ret trivial (by simp [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))
  · rw [eval_bind]; exact Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot (deliverEC_gen_potOKInv hH L maxSkip cfg (.fst (ReductionDsl.Expr.v3 (O := OO))) .v0 _ m)
      (fun _ _ => potInvFS_ret trivial (by simp [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))
  · rw [eval_bind]; exact Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot (injectEC_gen_potOKInv hH L Δ qep cfg (.fst (ReductionDsl.Expr.v2 (O := OO))) .v0 _ m)
      (fun _ _ => potInvFS_ret trivial (by simp [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))
  · rw [eval_bind]; exact Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot (corrECPaper_gen_potOKInv hH L π (.fst (ReductionDsl.Expr.v1 (O := OO))) .v0 _ m)
      (fun _ _ => potInvFS_ret trivial (by simp [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))

private theorem implECDFPaper_gen_potOKInv {j : ℕ} {hsT : Ty SP}
    {H : HooksC OO IIM (.base .γ) (.base .sig) (.sum (.base .ss) .nat) (.sum (.base .rs) .nat) hsT}
    {hPot : hsT.denote → ℕ} (hH : HooksPotSpec j H hPot) (L Δ qep maxSkip : ℕ) (cfg : ConfigEC OO) (π : Policy)
    {Γ' : List (Ty SP)} (esE : Expr OO Γ' (esTy mVpTy hsT))
    (qE : Expr OO Γ' (ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E)) (ρ : Env Γ') (m : ℕ) :
    PotOKInvFS (sessPred j) (fun _ => True) (fun x => m + esPot hPot x.2)
      ((implECDFPaper H L Δ qep maxSkip cfg π esE qE).eval ρ) (1 + m + esPot hPot (esE.eval ρ)) := by
  unfold implECDFPaper; rw [eval_bind_ret]
  refine potInvFS_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
  · rw [eval_bind]; exact Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot (implECPaper_gen_potOKInv hH L Δ qep maxSkip cfg π (.fst (ReductionDsl.Expr.v1 (O := OO))) .v0 _ m)
      (fun _ _ => potInvFS_ret trivial (by simp [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))
  · rw [eval_bind]; exact Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot (deliverForgeEC_gen_potOKInv hH L Δ qep cfg (.fst (ReductionDsl.Expr.v1 (O := OO))) .v0 _ m)
      (fun _ _ => potInvFS_ret trivial (by simp [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))

private theorem implECShiftedPaperGen_gen_potOKInv {j : ℕ} {hsT : Ty SP}
    {H : HooksC OO IIM (.base .γ) (.base .sig) (.sum (.base .ss) .nat) (.sum (.base .rs) .nat) hsT}
    {hPot : hsT.denote → ℕ} (hH : HooksPotSpec j H hPot) (b1 : Bool) (L l Δ qep maxSkip tStar : ℕ)
    (cfg : ConfigEC OO) (π : Policy) {Γ' : List (Ty SP)} (esE : Expr OO Γ' (esTy mVpTy hsT))
    (qE : Expr OO Γ' (ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E)) (ρ : Env Γ') (m : ℕ) :
    PotOKInvFS (sessPred j) (fun _ => True) (fun x => m + esPot hPot x.2)
      ((implECShiftedPaperGen b1 H L l Δ qep maxSkip tStar cfg π esE qE).eval ρ)
      (1 + m + esPot hPot (esE.eval ρ)) := by
  unfold implECShiftedPaperGen; rw [eval_bind_ret]
  refine potInvFS_caseSum (fun _ _ => potInvFS_caseSum (fun _ _ => potInvFS_caseSum
    (fun _ _ => potInvFS_caseSum (fun _ _ => ?_) (fun _ _ => ?_)) (fun _ _ => ?_)) (fun _ _ => ?_)) (fun _ _ => ?_)
  · rw [eval_bind]; exact Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot (transmitEC_gen_potOKInv hH L Δ qep π (.fst (ReductionDsl.Expr.v4 (O := OO))) .v0 _ m)
      (fun _ _ => potInvFS_ret trivial (by simp [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))
  · rw [eval_bind]; exact Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot (challEC_gen_potOKInv hH L Δ qep cfg π (.fst (ReductionDsl.Expr.v4 (O := OO))) .v0 _ m)
      (fun _ _ => potInvFS_ret trivial (by simp [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))
  · rw [eval_bind]; exact Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot (deliverEC_gen_potOKInv hH L maxSkip cfg (.fst (ReductionDsl.Expr.v3 (O := OO))) .v0 _ m)
      (fun _ _ => potInvFS_ret trivial (by simp [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))
  · rw [eval_bind]; cases b1
    · dsimp only [injectECGen]; simp only [Bool.false_eq_true, ↓reduceIte]
      exact Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot (injectEC_gen_potOKInv hH L Δ qep cfg (.fst (ReductionDsl.Expr.v2 (O := OO))) .v0 _ m)
        (fun _ _ => potInvFS_ret trivial (by simp [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))
    · dsimp only [injectECGen]; simp only [↓reduceIte]
      exact Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot (injectECB1_gen_potOKInv hH L qep tStar cfg (.fst (ReductionDsl.Expr.v2 (O := OO))) .v0 _ m)
        (fun _ _ => potInvFS_ret trivial (by simp [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))
  · rw [eval_bind]; exact Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot (corrECShiftedPaper_gen_potOKInv hH L l π (.fst (ReductionDsl.Expr.v1 (O := OO))) .v0 _ m)
      (fun _ _ => potInvFS_ret trivial (by simp [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))

private theorem implECDFShiftedPaperGen_gen_potOKInv {j : ℕ} {hsT : Ty SP}
    {H : HooksC OO IIM (.base .γ) (.base .sig) (.sum (.base .ss) .nat) (.sum (.base .rs) .nat) hsT}
    {hPot : hsT.denote → ℕ} (hH : HooksPotSpec j H hPot) (b1 : Bool) (L l Δ qep maxSkip tStar : ℕ)
    (cfg : ConfigEC OO) (π : Policy) {Γ' : List (Ty SP)} (esE : Expr OO Γ' (esTy mVpTy hsT))
    (qE : Expr OO Γ' (ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E)) (ρ : Env Γ') (m : ℕ) :
    PotOKInvFS (sessPred j) (fun _ => True) (fun x => m + esPot hPot x.2)
      ((implECDFShiftedPaperGen b1 H L l Δ qep maxSkip tStar cfg π esE qE).eval ρ)
      (1 + m + esPot hPot (esE.eval ρ)) := by
  unfold implECDFShiftedPaperGen; rw [eval_bind_ret]
  refine potInvFS_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
  · rw [eval_bind]; exact Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot
      (implECShiftedPaperGen_gen_potOKInv hH b1 L l Δ qep maxSkip tStar cfg π (.fst (ReductionDsl.Expr.v1 (O := OO))) .v0 _ m)
      (fun _ _ => potInvFS_ret trivial (by simp [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))
  · rw [eval_bind]; cases b1
    · dsimp only [deliverForgeECGen]; simp only [Bool.false_eq_true, ↓reduceIte]
      exact Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot (deliverForgeEC_gen_potOKInv hH L Δ qep cfg (.fst (ReductionDsl.Expr.v1 (O := OO))) .v0 _ m)
        (fun _ _ => potInvFS_ret trivial (by simp [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))
    · dsimp only [deliverForgeECGen]; simp only [↓reduceIte]
      exact Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot (deliverForgeECB1_gen_potOKInv hH L qep tStar cfg (.fst (ReductionDsl.Expr.v1 (O := OO))) .v0 _ m)
        (fun _ _ => potInvFS_ret trivial (by simp [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))

theorem costedReduction_multi_isQueryBoundP
    {κ : Type} {G : OracleSpec.{0, 0} κ} {C : GameCodec SP G}
    (j : ℕ) (R : CostedReduction OO IIM G C .unit .unit .bool .bool)
    (pot : R.σ.denote → ℕ) (q : ℕ)
    (A : OracleComp (unifSpec + G) Bool)
    (hA' : A.IsQueryBoundP (isGameQuery (G := G)) q)
    (hTot : R.totalQueries (fun _ => 1) (fun _ => 0) q ≤ q * 2)
    (hInit : PotOKInvFS (sessPred j) (fun _ : (ReductionDsl.Ty.prod .unit R.σ : Ty SP).denote => True)
      (fun as : (ReductionDsl.Ty.prod .unit R.σ : Ty SP).denote => q + pot as.2)
      (R.init.eval (ReductionDsl.Env.cons (t := .unit) () .nil)) (q + 2))
    (hStep : ∀ (m : ℕ) qv sv,
      PotOKInvFS (sessPred j) (fun _ => True) (fun x => m + pot x.2)
        (R.handle.eval (.cons sv (.cons qv .nil))) (1 + m + pot sv))
    (hFin : R.finish.queries (fun _ => 1) (fun _ => 0) = 0) :
    (R.eval (fun _ => A) ()).IsQueryBoundP (sessPred j) (2 * q) := by
  have h2q : (R.eval (fun _ => A) ()).IsQueryBoundP (sessPred j) (2 * q) := by
    have hSyn := ReductionDsl.CostedReduction.queryBound_eval R (sessPred j) (fun _ => 1) (fun _ => 0)
      (fun _ _ _ => Nat.le_refl 1) (multiIface_fwdU_zero j) (fun _ => A) q (fun _ => hA') ()
    exact hSyn.mono (by omega)
  have hq2 : (R.eval (fun _ => A) ()).IsQueryBoundP (sessPred j) (q + 2) := by
    unfold ReductionDsl.CostedReduction.eval ReductionDsl.CostedReduction.impl
    refine hInit.run _ ?_
    rintro ⟨_, s0⟩ _
    have hSim := potOKInvFS_simulateQ_handlerImpl_step1 (fun _ => True) pot
      (multiIface_fwdU_zero j) R.handle (fun m qv sv _ => hStep m qv sv) hA' s0 trivial
    refine hSim.run _ ?_
    rintro ⟨bOut, sOut⟩ _
    have hF := ReductionDsl.Comp.queryBound_eval (sessPred j) (fun _ => 1) (fun _ => 0)
      (fun _ _ _ => Nat.le_refl 1) (multiIface_fwdU_zero j) R.finish (.cons sOut (.cons bOut .nil))
    exact hF.mono (by simp [hFin])
  exact (isQueryBoundP_min_fs h2q hq2).mono (Nat.min_le_left _ _)

@[expose] def bkPot (j : ℕ) (bk : ℕ → Option ((mBookTy).denote)) : ℕ :=
  match bk j with | none => 1 | some b => if b.1 then 0 else 1

abbrev mbHPot (j : ℕ) (h : (mbHsTy).denote) : ℕ := bkPot j h.2.2.2.1

theorem bkPot_le_one (j : ℕ) (bk : ℕ → Option ((mBookTy).denote)) : bkPot j bk ≤ 1 := by
  unfold bkPot; cases bk j with
  | none => exact Nat.le_refl 1
  | some b => dsimp only; cases b.1 <;> decide

theorem bkPot_eq_one_of_get_false (j : ℕ) (bk : ℕ → Option ((mBookTy).denote))
    (hf : ((match bk j with | none => (false, (0, [])) | some b => b : (mBookTy).denote)).1 = false) :
    bkPot j bk = 1 := by
  unfold bkPot; cases h : bk j with
  | none => rfl
  | some b => simp [h] at hf; simp [hf]

theorem ite_eq_proj_book {α β γ δ ε ζ : Type} {c : Prop} [Decidable c]
    (x y : α × β × γ × δ × ε × ζ) {z : ε} (hx : x.2.2.2.2.1 = z) (hy : y.2.2.2.2.1 = z) :
    (if c then x else y).2.2.2.2.1 = z := by
  by_cases hc : c <;> simp [hc, hx, hy]


private theorem costedReduction_multi_isQueryBoundP_of_totalQueries
    {κ : Type} {G : OracleSpec.{0, 0} κ} {C : GameCodec SP G}
    (j : ℕ) (R : CostedReduction OO IIM G C .unit .unit .bool .bool)
    (q : ℕ)
    (A : OracleComp (unifSpec + G) Bool)
    (hA' : A.IsQueryBoundP (isGameQuery (G := G)) q)
    (hTot : R.totalQueries (fun _ => 1) (fun _ => 0) q ≤ q * 2) :
    (R.eval (fun _ => A) ()).IsQueryBoundP (sessPred j) (2 * q) := by
  have hSyn := ReductionDsl.CostedReduction.queryBound_eval R (sessPred j) (fun _ => 1) (fun _ => 0)
    (fun _ _ _ => Nat.le_refl 1) (multiIface_fwdU_zero j) (fun _ => A) q (fun _ => hA') ()
  exact hSyn.mono (by omega)

private theorem redFSAuthDFPaperMultiProg_sess_isQueryBoundP
    (L B Δcka qep maxSkip : ℕ) (la : Bool) (tL : Option ℕ) (t j q : ℕ)
    (A : OracleComp (unifSpec + _root_.CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) Bool)
    (hA : A.IsQueryBoundP (· matches .inr _) q) :
    ((redFSAuthDFPaperMultiProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
        L B Δcka qep maxSkip la tL t).eval (fun _ => A) ()).IsQueryBoundP
      (fun x => (match x with | .inl _ => false | .inr ⟨s, _⟩ => decide (s = j)) = true)
      (2 * q) := by
  exact costedReduction_multi_isQueryBoundP_of_totalQueries j _ q A
    (hA.of_imp (fun x hx => by cases x <;> [cases hx; rfl]))
    (redFSAuthDFPaperMultiProg_totalQueries L B Δcka qep maxSkip la tL t q)

private theorem redFSAuthDFShiftedPaperMultiGenProg_sess_isQueryBoundP
    (L B Δcka qep maxSkip l tStar : ℕ) (authH la : Bool) (j q : ℕ)
    (A : OracleComp (unifSpec + _root_.CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) Bool)
    (hA : A.IsQueryBoundP (· matches .inr _) q) :
    ((redFSAuthDFShiftedPaperMultiGenProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
        L B Δcka qep maxSkip l tStar authH la).eval (fun _ => A) ()).IsQueryBoundP
      (fun x => (match x with | .inl _ => false | .inr ⟨s, _⟩ => decide (s = j)) = true)
      (2 * q) := by
  exact costedReduction_multi_isQueryBoundP_of_totalQueries j _ q A
    (hA.of_imp (fun x hx => by cases x <;> [cases hx; rfl]))
    (redFSAuthDFShiftedPaperMultiGenProg_totalQueries L B Δcka qep maxSkip l tStar authH la q)

theorem redFSAuthDFPaperMultiProg_sess_isQueryBoundP_of_eq
    (L B Δcka qep maxSkip : ℕ) (la : Bool) (tL : Option ℕ) (t j q : ℕ)
    (R : CostedReduction OO IIM
      (_root_.CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E) .unit .unit .bool .bool)
    (hR : R = redFSAuthDFPaperMultiProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      L B Δcka qep maxSkip la tL t)
    (A : OracleComp (unifSpec + _root_.CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) Bool)
    (hA : A.IsQueryBoundP (· matches .inr _) q) :
    (R.eval (fun _ => A) ()).IsQueryBoundP
      (fun x => (match x with | .inl _ => false | .inr ⟨s, _⟩ => decide (s = j)) = true)
      (2 * q) := by
  subst hR
  exact redFSAuthDFPaperMultiProg_sess_isQueryBoundP L B Δcka qep maxSkip la tL t j q A hA

theorem redFSAuthDFShiftedPaperMultiGenProg_sess_isQueryBoundP_of_eq
    (L B Δcka qep maxSkip l tStar : ℕ) (authH la : Bool) (j q : ℕ)
    (R : CostedReduction OO IIM
      (_root_.CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E) .unit .unit .bool .bool)
    (hR : R = redFSAuthDFShiftedPaperMultiGenProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      L B Δcka qep maxSkip l tStar authH la)
    (A : OracleComp (unifSpec + _root_.CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) Bool)
    (hA : A.IsQueryBoundP (· matches .inr _) q) :
    (R.eval (fun _ => A) ()).IsQueryBoundP
      (fun x => (match x with | .inl _ => false | .inr ⟨s, _⟩ => decide (s = j)) = true)
      (2 * q) := by
  subst hR
  exact redFSAuthDFShiftedPaperMultiGenProg_sess_isQueryBoundP L B Δcka qep maxSkip l tStar authH la j q A hA

theorem costedReduction_multi_isQueryBoundP_min
    {κ : Type} {G : OracleSpec.{0, 0} κ} {C : GameCodec SP G}
    (j : ℕ) (R : CostedReduction OO IIM G C .unit .unit .bool .bool)
    (pot : R.σ.denote → ℕ) (q : ℕ)
    (A : OracleComp (unifSpec + G) Bool)
    (hA' : A.IsQueryBoundP (isGameQuery (G := G)) q)
    (hTot : R.totalQueries (fun _ => 1) (fun _ => 0) q ≤ q * 2)
    (hInit : PotOKInvFS (sessPred j) (fun _ : (ReductionDsl.Ty.prod .unit R.σ : Ty SP).denote => True)
      (fun as : (ReductionDsl.Ty.prod .unit R.σ : Ty SP).denote => q + pot as.2)
      (R.init.eval (ReductionDsl.Env.cons (t := .unit) () .nil)) (q + 2))
    (hStep : ∀ (m : ℕ) qv sv,
      PotOKInvFS (sessPred j) (fun _ => True) (fun x => m + pot x.2)
        (R.handle.eval (.cons sv (.cons qv .nil))) (1 + m + pot sv))
    (hFin : R.finish.queries (fun _ => 1) (fun _ => 0) = 0) :
    (R.eval (fun _ => A) ()).IsQueryBoundP (sessPred j) (min (2 * q) (q + 2)) := by
  have h2q : (R.eval (fun _ => A) ()).IsQueryBoundP (sessPred j) (2 * q) := by
    have hSyn := ReductionDsl.CostedReduction.queryBound_eval R (sessPred j) (fun _ => 1) (fun _ => 0)
      (fun _ _ _ => Nat.le_refl 1) (multiIface_fwdU_zero j) (fun _ => A) q (fun _ => hA') ()
    exact hSyn.mono (by omega)
  have hq2 : (R.eval (fun _ => A) ()).IsQueryBoundP (sessPred j) (q + 2) := by
    unfold ReductionDsl.CostedReduction.eval ReductionDsl.CostedReduction.impl
    refine hInit.run _ ?_
    rintro ⟨_, s0⟩ _
    have hSim := potOKInvFS_simulateQ_handlerImpl_step1 (fun _ => True) pot
      (multiIface_fwdU_zero j) R.handle (fun m qv sv _ => hStep m qv sv) hA' s0 trivial
    refine hSim.run _ ?_
    rintro ⟨bOut, sOut⟩ _
    have hF := ReductionDsl.Comp.queryBound_eval (sessPred j) (fun _ => 1) (fun _ => 0)
      (fun _ _ _ => Nat.le_refl 1) (multiIface_fwdU_zero j) R.finish (.cons sOut (.cons bOut .nil))
    exact hF.mono (by simp [hFin])
  exact isQueryBoundP_min_fs h2q hq2

private abbrev mHPot (j : ℕ) (h : (mHsTy).denote) : ℕ := bkPot j h.2.2.2.1

private theorem regSessMultiE_book (L : ℕ) {Γ' : List (Ty SP)}
    (hE : Expr OO Γ' mHsTy) (ikE : Expr OO Γ' (.base .i)) (ρ : Env Γ') :
    ((regSessMultiE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) L hE ikE).eval ρ).2.2.2.2.1 = (hE.eval ρ).2.2.2.1 := by
  simp only [regSessMultiE, fsMultiHsSetSessions, fsMultiHsMk, fsMultiHsBook,
    ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero]
  exact ite_eq_proj_book _ _ rfl rfl

private theorem regSessOptMultiE_book (L : ℕ) {Γ' : List (Ty SP)}
    (hE : Expr OO Γ' mHsTy) (sidE : Expr OO Γ' (.opt (.base .i))) (ρ : Env Γ') :
    ((regSessOptMultiE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) L hE sidE).eval ρ).2.2.2.2.1 = (hE.eval ρ).2.2.2.1 := by
  simp only [regSessOptMultiE, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero]
  cases h : sidE.eval ρ with
  | none => rfl
  | some ik =>
    have hSub := regSessMultiE_book L (.fst (ReductionDsl.Expr.v1 (O := OO))) .v0 (.cons ik (.cons ((hE.pair sidE).eval ρ) ρ))
    simpa [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, ReductionDsl.Env.get_cons_zero, ReductionDsl.Env.get_cons_succ, h] using hSub

private theorem lookupMultiFC_potOKInv (j L : ℕ) {Γ' : List (Ty SP)}
    (hE : Expr OO Γ' mHsTy) (ikE : Expr OO Γ' (.base .i)) (ρ : Env Γ') (m : ℕ) :
    PotOKInvFS (sessPred j) (fun _ => True) (fun res => m + mHPot j res.2)
      ((lookupMultiFC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L hE ikE).eval ρ) (m + mHPot j (hE.eval ρ)) := by
  unfold lookupMultiFC; rw [eval_bind_ret]
  refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => potInvFS_ret trivial (by simp [mHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v1]))
  rw [eval_bind]
  exact Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot
    (potInvMultiFS_zero j _ _ (m + mHPot j (hE.eval ρ)) (fun _ => Nat.le_refl _) rfl)
    (fun _ _ => potInvFS_ret trivial
      (by simp [mHPot, fsMultiHsSetTable, fsMultiHsMk, fsMultiHsBook, ReductionDsl.Expr.eval, ReductionDsl.Expr.v1]))

private theorem rootFSMultiC_potOKInv (j L : ℕ) (mo : Mode) {Γ' : List (Ty SP)}
    (hE : Expr OO Γ' mHsTy) (tE : Expr OO Γ' .nat)
    (ikE : Expr OO Γ' (.base .i)) (σE : Expr OO Γ' (.base .sig)) (ρ : Env Γ') (m : ℕ) :
    PotOKInvFS (sessPred j) (fun _ => True) (fun res => m + mHPot j res.2)
      ((rootFSMultiC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L mo hE tE ikE σE).eval ρ) (m + mHPot j (hE.eval ρ)) := by
  unfold rootFSMultiC; rw [eval_bind_ret]
  refine potInvFS_ite (fun _ => potInvFS_ret trivial (by simp [mHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))
    (fun _ => potInvFS_ite (fun _ => potInvFS_ite (fun _ => ?_) (fun _ => ?_))
      (fun _ => potInvFS_ite (fun _ => ?_)
        (fun _ => potInvFS_ret trivial (by simp [mHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))))
  · rw [eval_bind]
    refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot
      (potInvMultiFS_zero j _ _ (m + mHPot j (hE.eval ρ)) (fun _ => Nat.le_refl _) rfl) (fun _ _ => ?_)
    rw [eval_bind]
    exact Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot
      (potInvMultiFS_zero j _ _ (m + mHPot j (hE.eval ρ)) (fun _ => Nat.le_refl _) rfl)
      (fun _ _ => potInvFS_ret trivial (by simp [mHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v2]))
  · rw [eval_bind]
    have hL := lookupMultiFC_potOKInv (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) j L (.fst (ReductionDsl.Expr.v0 (O := OO)))
      (.fst (.snd (.snd .v0))) (.cons ((hE.pair (tE.pair (ikE.pair σE))).eval ρ) ρ) m
    simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero] at hL
    exact Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot hL (fun _ _ => potInvFS_ret trivial (by simp [mHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))
  · rw [eval_bind]
    exact Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot
      (potInvMultiFS_zero j _ _ (m + mHPot j (hE.eval ρ)) (fun _ => Nat.le_refl _) rfl)
      (fun _ _ => potInvFS_ret trivial (by simp [mHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v1]))

private theorem fsMultiFsSendC_potOKInv (j Δcka : ℕ) (la : Bool) {Γ' : List (Ty SP)}
    (hE : Expr OO Γ' mHsTy) (ctxE : Expr OO Γ' (cGsTy mVpTy)) (pE : Expr OO Γ' .bool)
    (tE : Expr OO Γ' .nat) (ssvE : Expr OO Γ' (.sum (.base .ss) .nat)) (hdrE : Expr OO Γ' hdrTy)
    (mE : Expr OO Γ' (.base .msg)) (pairE : Expr OO Γ' (.opt (.prod (.base .msg) (.base .msg))))
    (ρ : Env Γ') (m : ℕ) :
    PotOKInvFS (sessPred j) (fun _ => True) (fun res => m + mHPot j res.2)
      ((fsMultiFsSendC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) Δcka la hE ctxE pE tE ssvE hdrE mE pairE).eval ρ)
      (1 + m + mHPot j (hE.eval ρ)) := by
  unfold fsMultiFsSendC
  cases la
  · simp only [Bool.false_eq_true, ↓reduceIte]; rw [eval_bind_ret]
    refine potInvFS_caseSum
      (fun _ _ => potInvFS_ret trivial (by simp only [mHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v1, ReductionDsl.Env.get_cons_succ, ReductionDsl.Env.get_cons_zero]; omega))
      (fun sIdx _ => ?_)
    rw [eval_bind]
    refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot (Inv₁ := fun _ => True)
      (B₁ := fun oh => (if oh.1 then 1 else 0) + m + mHPot j oh.2) ?_ (fun oh _ => ?_)
    · refine potInvFS_ite (fun hCond => ?_) (fun _ => ?_)
      · rw [eval_bind]
        have hCorrF : ((match (hE.eval ρ).2.2.2.1 sIdx with | none => (false, (0, [])) | some b => b : (mBookTy).denote)).1 = false := by
          simp only [fsMultiHsGetBookAt, fsMultiHsBook, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1,
            ReductionDsl.Env.get_cons_zero, ReductionDsl.Env.get_cons_succ, Bool.and_eq_true, Bool.not_eq_true'] at hCond
          cases hB : (hE.eval ρ).2.2.2.1 sIdx <;> simp [hB] at hCond ⊢; exact hCond.2
        refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot
          (potInvMultiFS_query (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
            (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
            (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
            (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
            (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
            (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) j .cs _ _
            ((if sIdx = j then 0 else 1) + m + mHPot j (hE.eval ρ))
            (1 + m + mHPot j (hE.eval ρ)) (by simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero]; split <;> omega))
          (fun _ _ => ?_)
        refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => ?_)
        · exact potInvFS_ret trivial (by simp [mHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v2])
        · refine potInvFS_ret trivial ?_
          simp only [mHPot, fsMultiHsSetBookAt, fsMultiHsMk, fsMultiHsBook, fsMultiHsGetBookAt,
            ReductionDsl.Expr.eval, ReductionDsl.Expr.v2, ReductionDsl.Expr.v3, ReductionDsl.Env.get_cons_zero, ReductionDsl.Env.get_cons_succ]
          by_cases hsj : sIdx = j
          · subst hsj; have h1 := bkPot_eq_one_of_get_false sIdx _ hCorrF; rw [h1]; unfold bkPot; simp; omega
          · have hjs : j ≠ sIdx := Ne.symm hsj; unfold bkPot; simp [hsj, hjs]
      · exact potInvFS_ret trivial (by simp [mHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v1])
    · refine potInvFS_ite (fun hNotOk => ?_) (fun hOk => ?_)
      · exact potInvFS_ret trivial (by simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero] at hNotOk ⊢; cases oh.1 <;> simp_all)
      · have hOkT : oh.1 = true := by simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero] at hOk; cases h : oh.1 <;> simp_all
        simp only [hOkT, ↓reduceIte]; rw [eval_bind]
        refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot (Inv₁ := fun _ => True) (B₁ := fun _ => m + mHPot j oh.2) ?_ (fun _ _ => ?_)
        · refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => ?_)
          · refine potInvMultiFS_query (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) j .tr _ _ _ _ ?_; split <;> omega
          · refine potInvMultiFS_query (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) j .ch _ _ _ _ ?_; split <;> omega
        · refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => ?_)
          · exact potInvFS_ret trivial (by simp [mHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v1])
          · refine potInvFS_ret trivial ?_
            simp only [mHPot, fsMultiHsSetBookAt, fsMultiHsMk, fsMultiHsBook, fsMultiHsGetBookAt,
              ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v2, ReductionDsl.Expr.v3, ReductionDsl.Env.get_cons_zero, ReductionDsl.Env.get_cons_succ]
            unfold bkPot; dsimp only
            by_cases hsj : j = sIdx
            · subst hsj; cases oh.2.2.2.2.1 j <;> simp
            · simp [hsj]
  · simp only [↓reduceIte]; rw [eval_bind_ret]
    refine potInvFS_caseSum
      (fun _ _ => potInvFS_ret trivial (by simp only [mHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v1, ReductionDsl.Env.get_cons_succ, ReductionDsl.Env.get_cons_zero]; omega))
      (fun sIdx _ => ?_)
    refine potInvFS_ite
      (fun _ => potInvFS_ret trivial (by simp only [mHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v1, ReductionDsl.Env.get_cons_succ, ReductionDsl.Env.get_cons_zero]; omega))
      (fun _ => ?_)
    rw [eval_bind]
    refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot (Inv₁ := fun _ => True) (B₁ := fun _ => m + mHPot j (hE.eval ρ)) ?_ (fun _ _ => ?_)
    · refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => ?_)
      · refine potInvMultiFS_query (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) j .tr _ _ _ _ ?_; split <;> omega
      · refine potInvMultiFS_query (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) j .ch _ _ _ _ ?_; split <;> omega
    · refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => ?_)
      · exact potInvFS_ret trivial (by simp [mHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v2])
      · refine potInvFS_ret trivial ?_
        simp only [mHPot, fsMultiHsSetBookAt, fsMultiHsMk, fsMultiHsBook, fsMultiHsGetBookAt,
          ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v2, ReductionDsl.Expr.v3, ReductionDsl.Env.get_cons_zero, ReductionDsl.Env.get_cons_succ]
        unfold bkPot; dsimp only
        by_cases hsj : j = sIdx
        · subst hsj; cases (hE.eval ρ).2.2.2.1 j <;> simp
        · simp [hsj]

private theorem fsMultiFsRecvC_potOKInv (j L B Δcka : ℕ) (la : Bool) {Γ' : List (Ty SP)}
    (hE : Expr OO Γ' mHsTy) (ctxE : Expr OO Γ' (cGsTy mVpTy)) (pE : Expr OO Γ' .bool)
    (tE : Expr OO Γ' .nat) (rsvE : Expr OO Γ' (.sum (.base .rs) .nat))
    (hdrE : Expr OO Γ' hdrTy) (eE : Expr OO Γ' (.base .ct)) (recE : Expr OO Γ' (.opt cRecTy))
    (ρ : Env Γ') (m : ℕ) :
    PotOKInvFS (sessPred j) (fun _ => True) (fun res => m + mHPot j res.2)
      ((fsMultiFsRecvC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L B la Δcka hE ctxE pE tE rsvE hdrE eE recE).eval ρ)
      (1 + m + mHPot j (hE.eval ρ)) := by
  unfold fsMultiFsRecvC
  cases la
  · -- la = false: pre-heal !sCorr0 triggers FSHdrTag.cs and flips book[sIdx].1 := true
    simp only [Bool.false_eq_true, ↓reduceIte]; rw [eval_bind_ret]
    refine potInvFS_caseSum (fun _ _ => ?_) (fun sIdx _ => ?_)
    · refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => ?_)
      · exact potInvFS_ret trivial (by simp only [mHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v1, ReductionDsl.Env.get_cons_succ, ReductionDsl.Env.get_cons_zero]; omega)
      · exact potInvFS_ret trivial (by simp only [mHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v2, ReductionDsl.Env.get_cons_succ, ReductionDsl.Env.get_cons_zero]; omega)
    · rw [eval_bind]
      refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot (Inv₁ := fun _ => True)
        (B₁ := fun oh => (if oh.1 then 1 else 0) + m + mHPot j oh.2) ?_ (fun oh _ => ?_)
      · refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => potInvFS_ret trivial (by simp [mHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v2]))
        refine potInvFS_ite (fun hCond => ?_) (fun _ => potInvFS_ret trivial (by simp [mHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v1]))
        rw [eval_bind]
        have hCorrF : ((match (hE.eval ρ).2.2.2.1 sIdx with | none => (false, (0, [])) | some b => b : (mBookTy).denote)).1 = false := by
          simp only [fsMultiHsGetBookAt, fsMultiHsBook, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1,
            ReductionDsl.Env.get_cons_zero, ReductionDsl.Env.get_cons_succ, Bool.and_eq_true, Bool.not_eq_true'] at hCond
          cases hB : (hE.eval ρ).2.2.2.1 sIdx <;> simp [hB] at hCond ⊢; exact hCond.2
        refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot
          (potInvMultiFS_query (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
            (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
            (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
            (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
            (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
            (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) j .cs _ _
            ((if sIdx = j then 0 else 1) + m + mHPot j (hE.eval ρ))
            (1 + m + mHPot j (hE.eval ρ)) (by simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero]; split <;> omega))
          (fun _ _ => ?_)
        refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => ?_)
        · exact potInvFS_ret trivial (by simp [mHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v2])
        · refine potInvFS_ret trivial ?_
          simp only [mHPot, fsMultiHsSetBookAt, fsMultiHsMk, fsMultiHsBook, fsMultiHsGetBookAt,
            ReductionDsl.Expr.eval, ReductionDsl.Expr.v2, ReductionDsl.Expr.v3, ReductionDsl.Env.get_cons_zero, ReductionDsl.Env.get_cons_succ]
          by_cases hsj : sIdx = j
          · subst hsj; have h1 := bkPot_eq_one_of_get_false sIdx _ hCorrF; rw [h1]; unfold bkPot; simp; omega
          · have hjs : j ≠ sIdx := Ne.symm hsj; unfold bkPot; simp [hsj, hjs]
      · refine potInvFS_ite (fun hNotOk => ?_) (fun hOk => ?_)
        · exact potInvFS_ret trivial (by simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero] at hNotOk ⊢; cases oh.1 <;> simp_all)
        · have hOkT : oh.1 = true := by simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero] at hOk; cases h : oh.1 <;> simp_all
          simp only [hOkT, ↓reduceIte]; rw [eval_bind]
          refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot (Inv₁ := fun _ => True) (B₁ := fun _ => m + mHPot j oh.2) ?_ (fun _ _ => ?_)
          · refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => ?_)
            · refine potInvMultiFS_query (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) j .ij _ _ _ _ ?_; split <;> omega
            · refine potInvMultiFS_query (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) j .dl _ _ _ _ ?_; split <;> omega
          · refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => ?_)
            · exact potInvFS_ret trivial (by simp [mHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v1])
            · refine potInvFS_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
              · exact potInvFS_ret trivial (by simp [mHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v3])
              · refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => ?_)
                · refine potInvFS_ret trivial ?_
                  simp only [mHPot, fsMultiHsSetBookAt, fsMultiHsMk, fsMultiHsBook, fsMultiHsGetBookAt,
                    ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v3, ReductionDsl.Expr.v4,
                    ReductionDsl.Env.get_cons_zero, ReductionDsl.Env.get_cons_succ]
                  unfold bkPot; dsimp only
                  by_cases hsj : j = sIdx
                  · subst hsj; cases oh.2.2.2.2.1 j <;> simp
                  · simp [hsj]
                · refine potInvFS_ret trivial ?_
                  simp only [mHPot, fsMultiHsSetBookAt, fsMultiHsMk, fsMultiHsBook, fsMultiHsGetBookAt,
                    ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v4, ReductionDsl.Expr.v5,
                    ReductionDsl.Env.get_cons_zero, ReductionDsl.Env.get_cons_succ]
                  unfold bkPot; dsimp only
                  by_cases hsj : j = sIdx
                  · subst hsj; cases oh.2.2.2.2.1 j <;> simp
                  · simp [hsj]
  · -- la = true: blocked check then single .ij / .dl query
    simp only [↓reduceIte]; rw [eval_bind_ret]
    refine potInvFS_caseSum (fun _ _ => ?_) (fun sIdx _ => ?_)
    · refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => ?_)
      · exact potInvFS_ret trivial (by simp only [mHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v1, ReductionDsl.Env.get_cons_succ, ReductionDsl.Env.get_cons_zero]; omega)
      · exact potInvFS_ret trivial (by simp only [mHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v2, ReductionDsl.Env.get_cons_succ, ReductionDsl.Env.get_cons_zero]; omega)
    · refine potInvFS_ite
        (fun _ => potInvFS_ret trivial (by simp only [mHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v1, ReductionDsl.Env.get_cons_succ, ReductionDsl.Env.get_cons_zero]; omega))
        (fun _ => ?_)
      rw [eval_bind]
      refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot (Inv₁ := fun _ => True) (B₁ := fun _ => m + mHPot j (hE.eval ρ)) ?_ (fun _ _ => ?_)
      · refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => ?_)
        · refine potInvMultiFS_query (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) j .ij _ _ _ _ ?_; split <;> omega
        · refine potInvMultiFS_query (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) j .dl _ _ _ _ ?_; split <;> omega
      · refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => ?_)
        · exact potInvFS_ret trivial (by simp [mHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v2])
        · refine potInvFS_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
          · exact potInvFS_ret trivial (by simp [mHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v4])
          · refine potInvFS_ite (fun _ => ?_) (fun _ => ?_)
            · exact potInvFS_ret trivial (by simp [mHPot, fsMultiHsSetLfWin, fsMultiHsMk, fsMultiHsBook, ReductionDsl.Expr.eval, ReductionDsl.Expr.v4])
            · refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => ?_) <;>
              · refine potInvFS_ret trivial ?_
                simp only [mHPot, fsMultiHsSetBookAt, fsMultiHsMk, fsMultiHsBook, fsMultiHsGetBookAt,
                  ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v3, ReductionDsl.Expr.v4, ReductionDsl.Expr.v5,
                  ReductionDsl.Env.get_cons_zero, ReductionDsl.Env.get_cons_succ]
                unfold bkPot; dsimp only
                by_cases hsj : j = sIdx
                · subst hsj; cases (hE.eval ρ).2.2.2.1 j <;> simp
                · simp [hsj]

private theorem fsMultiRevealC_potOKInv (j L : ℕ) (mo : Mode) (la : Bool) {Γ' : List (Ty SP)}
    (hE : Expr OO Γ' mHsTy) (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (pE : Expr OO Γ' .bool) (vpE : Expr OO Γ' mVpTy) (ρ : Env Γ') (m : ℕ) :
    PotOKInvFS (sessPred j) (fun _ => True) (fun res => m + mHPot j res.2)
      ((fsMultiRevealC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L mo la hE ctxE pE vpE).eval ρ)
      (1 + m + mHPot j (hE.eval ρ)) := by
  unfold fsMultiRevealC
  cases la
  · simp only [Bool.false_eq_true, ↓reduceIte]; rw [eval_bind_ret, eval_bind]
    refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot (Inv₁ := fun _ => True)
      (B₁ := fun sh => m + mHPot j sh.2) ?_ (fun sh _ => ?_)
    · refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => ?_)
      · exact potInvFS_ret trivial (by simp only [mHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero]; omega)
      · refine potInvFS_caseSum (fun _ _ => ?_) (fun sIdx _ => ?_)
        · exact potInvFS_ret trivial (by simp only [mHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v2, ReductionDsl.Env.get_cons_succ, ReductionDsl.Env.get_cons_zero]; omega)
        · rw [eval_bind]
          refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot
            (potInvMultiFS_query (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
              (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
              (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
              (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
              (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
              (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) j .cs _ _
              (m + mHPot j (hE.eval ρ)) (1 + m + mHPot j (hE.eval ρ)) (by split <;> omega))
            (fun _ _ => ?_)
          refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => ?_)
          · exact potInvFS_ret trivial (by simp [mHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v3])
          · refine potInvFS_ret trivial ?_
            simp only [mHPot, fsMultiHsSetBookAt, fsMultiHsMk, fsMultiHsBook, ReductionDsl.Expr.eval, ReductionDsl.Expr.v2, ReductionDsl.Expr.v4,
              ReductionDsl.Env.get_cons_zero, ReductionDsl.Env.get_cons_succ]
            unfold bkPot; dsimp only; by_cases hsj : j = sIdx <;> simp [hsj]
    · refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => ?_)
      · exact potInvFS_ret trivial (by simp [mHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0])
      · refine potInvFS_ite (fun _ => ?_) (fun _ => ?_)
        · exact potInvFS_ret trivial (by simp [mHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v1])
        · rw [eval_bind]
          exact Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot
            (potInvMultiFS_zero j _ _ (m + mHPot j sh.2) (fun _ => Nat.le_refl _) (rangeListC_queries L (fun _ => 1) (fun _ => 0)))
            (fun _ _ => potInvFS_ret trivial (by simp [mHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v2]))
  · simp only [↓reduceIte]; rw [eval_bind_ret]
    refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => ?_)
    · exact potInvFS_ret trivial (by simp only [mHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero]; omega)
    · refine potInvFS_ite (fun _ => ?_) (fun _ => ?_)
      · exact potInvFS_ret trivial (by simp only [mHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v1, ReductionDsl.Env.get_cons_succ, ReductionDsl.Env.get_cons_zero]; omega)
      · rw [eval_bind]
        exact Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot
          (potInvMultiFS_zero j _ _ (1 + m + mHPot j (hE.eval ρ)) (fun _ => Nat.le_refl _)
            (rangeListC_queries L (fun _ => 1) (fun _ => 0)))
          (fun _ _ => potInvFS_ret trivial
            (by simp only [mHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v2, ReductionDsl.Env.get_cons_succ, ReductionDsl.Env.get_cons_zero]; omega))

private theorem hooksFSMultiC_potSpec (j L B Δcka : ℕ) (mo : Mode) (gMain la : Bool) :
    HooksPotSpec j
      (hooksFSMultiC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B Δcka mo gMain la) (mHPot j) where
  startSend hE _ _ tE γE σE rE ρ m := by
    unfold hooksFSMultiC fsMultiStartSendC; dsimp only; rw [eval_bind_ret, eval_bind]
    refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot
      (potInvFS_caseOpt (fun _ => potInvMultiFS_zero j _ _ (m + mHPot j (hE.eval ρ)) (fun _ => Nat.le_refl _) rfl)
        (fun _ _ => potInvFS_ret trivial (Nat.le_refl _))) (fun coins _ => ?_)
    rw [eval_bind]
    have hR := rootFSMultiC_potOKInv (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) j L mo (.fst (ReductionDsl.Expr.v1 (O := OO))) (.fst (.snd .v1))
      (.snd (.snd (ReductionDsl.Expr.op (O := OO) CryptoGames.CKA.CKAOp.ckaSend (.pair (.fst (.snd (.snd .v1))) .v0))))
      (.fst (.snd (.snd (.snd .v1)))) (.cons coins (.cons ((hE.pair (tE.pair (γE.pair (σE.pair rE)))).eval ρ) ρ)) m
    simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v1, ReductionDsl.Env.get_cons_zero, ReductionDsl.Env.get_cons_succ] at hR
    refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot hR (fun rOut _ => potInvFS_ret trivial ?_)
    have hReg := regSessOptMultiE_book L (.snd (ReductionDsl.Expr.v0 (O := OO))) (.snd (.snd (.fst .v0)))
      (.cons rOut (.cons coins (.cons ((hE.pair (tE.pair (γE.pair (σE.pair rE)))).eval ρ) ρ)))
    dsimp only [mHPot, fsMultiHsSetCache, fsMultiHsMk, fsMultiHsBook, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero] at hReg ⊢
    rw [hReg]
  startRecv hE _ _ tE γE σE tnE ρ m := by
    unfold hooksFSMultiC fsMultiStartRecvC; dsimp only; rw [eval_bind_ret]
    refine potInvFS_caseOpt
      (fun _ => potInvFS_ite (fun _ => potInvFS_ret trivial (by simp [mHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))
        (fun _ => potInvFS_ite
          (fun _ => potInvFS_ite (fun _ => potInvFS_ret trivial (by simp [mHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0])) (fun _ => ?_))
          (fun _ => potInvFS_ret trivial (by simp [mHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0]))))
      (fun _ _ => potInvFS_ret trivial (by simp [mHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v1]))
    rw [eval_bind]
    have hL := lookupMultiFC_potOKInv (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) j L (.fst (ReductionDsl.Expr.v0 (O := OO)))
      (.snd (ReductionDsl.Expr.op (O := OO) CryptoGames.CKA.CKAOp.ckaReceive (.pair (.fst (.snd (.snd .v0))) (.snd (.snd (.snd (.snd .v0)))))))
      (.cons ((hE.pair (tE.pair (γE.pair (σE.pair tnE)))).eval ρ) ρ) m
    simp only [ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Env.get_cons_zero] at hL
    refine Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks.PotOKInvFS.bindPot hL (fun lOut _ => potInvFS_ret trivial ?_)
    have hReg := regSessMultiE_book L (.snd (ReductionDsl.Expr.v0 (O := OO)))
      (.snd (ReductionDsl.Expr.op (O := OO) CryptoGames.CKA.CKAOp.ckaReceive (.pair (.fst (.snd (.snd .v1))) (.snd (.snd (.snd (.snd .v1)))))))
      (.cons lOut (.cons ((hE.pair (tE.pair (γE.pair (σE.pair tnE)))).eval ρ) ρ))
    dsimp only [mHPot, ReductionDsl.Expr.eval, ReductionDsl.Expr.v0, ReductionDsl.Expr.v1, ReductionDsl.Env.get_cons_zero, ReductionDsl.Env.get_cons_succ] at hReg ⊢
    rw [hReg]
  fsSend := fsMultiFsSendC_potOKInv j Δcka la
  fsRecv := fsMultiFsRecvC_potOKInv j L B Δcka la
  commit _ _ _ _ _ _ _ := by unfold hooksFSMultiC fsMultiCommitC; dsimp only; exact potInvFS_ret trivial (Nat.le_refl _)
  reveal := fsMultiRevealC_potOKInv j L mo la

private theorem initFSMultiEStateC_queries (L : ℕ) (mo : Mode) {Γ' : List (Ty SP)}
    (bE : Expr OO Γ' .bool) :
    (CryptoGames.SM.Construction.initFSMultiEStateC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L mo bE).queries
      (fun _ => 1) (fun _ => 0) = 0 := by
  simp [CryptoGames.SM.Construction.initFSMultiEStateC, CryptoGames.SM.Construction.rootFSMultiC,
    lookupMultiFC, ReductionDsl.Comp.queries]

private theorem redFSAuthDFPaperMultiProg_sess_isQueryBoundP_min
    (L B Δcka qep maxSkip : ℕ) (la : Bool) (tL : Option ℕ) (t j q : ℕ)
    (A : OracleComp (unifSpec + _root_.CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) Bool)
    (hA : A.IsQueryBoundP (· matches .inr _) q) :
    ((redFSAuthDFPaperMultiProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
        L B Δcka qep maxSkip la tL t).eval (fun _ => A) ()).IsQueryBoundP
      (fun x => (match x with | .inl _ => false | .inr ⟨s, _⟩ => decide (s = j)) = true)
      (min (2 * q) (q + 2)) := by
  refine costedReduction_multi_isQueryBoundP_min j _ (esPot (mHPot j)) q A
    (hA.of_imp (fun x hx => by cases x <;> [cases hx; rfl]))
    (redFSAuthDFPaperMultiProg_totalQueries L B Δcka qep maxSkip la tL t q) ?_ ?_
    (by simp [redFSAuthDFPaperMultiProg, ReductionDsl.Comp.queries])
  · refine potInvMultiFS_zero j _ _ (q + 2) (fun as => ?_)
      (by simp [redFSAuthDFPaperMultiProg, ReductionDsl.Comp.queries, initFSMultiEStateC_queries])
    have h1 := bkPot_le_one j as.2.2.1.2.2.2.1; dsimp only [esPot, mHPot]; omega
  · intro m qv sv
    exact implECDFPaper_gen_potOKInv (hooksFSMultiC_potSpec j L B Δcka ⟨true, tL, t⟩ false la)
      L (2 + Δcka) qep maxSkip (modeCfgEC OO ⟨true, tL, t⟩) (⟨true, tL, t⟩ : Mode).policy
      .v0 .v1 (.cons sv (.cons qv .nil)) m

private theorem redFSAuthDFShiftedPaperMultiGenProg_sess_isQueryBoundP_min
    (L B Δcka qep maxSkip l tStar : ℕ) (authH la : Bool) (j q : ℕ)
    (A : OracleComp (unifSpec + _root_.CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) Bool)
    (hA : A.IsQueryBoundP (· matches .inr _) q) :
    ((redFSAuthDFShiftedPaperMultiGenProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
        L B Δcka qep maxSkip l tStar authH la).eval (fun _ => A) ()).IsQueryBoundP
      (fun x => (match x with | .inl _ => false | .inr ⟨s, _⟩ => decide (s = j)) = true)
      (min (2 * q) (q + 2)) := by
  refine costedReduction_multi_isQueryBoundP_min j _ (esPot (mHPot j)) q A
    (hA.of_imp (fun x hx => by cases x <;> [cases hx; rfl]))
    (redFSAuthDFShiftedPaperMultiGenProg_totalQueries L B Δcka qep maxSkip l tStar authH la q) ?_ ?_
    (by simp [redFSAuthDFShiftedPaperMultiGenProg, ReductionDsl.Comp.queries])
  · refine potInvMultiFS_zero j _ _ (q + 2) (fun as => ?_)
      (by simp [redFSAuthDFShiftedPaperMultiGenProg, ReductionDsl.Comp.queries, initFSMultiEStateC_queries])
    have h1 := bkPot_le_one j as.2.2.1.2.2.2.1; dsimp only [esPot, mHPot]; omega
  · intro m qv sv
    exact implECDFShiftedPaperGen_gen_potOKInv
      (hooksFSMultiC_potSpec j L B Δcka ⟨authH, some (l - 1), tStar⟩ false la)
      (!authH) L l (2 + Δcka) qep maxSkip tStar
      (modeCfgEC OO ⟨true, some (l - 1), tStar⟩) (⟨true, some (l - 1), tStar⟩ : Mode).policy
      .v0 .v1 (.cons sv (.cons qv .nil)) m

theorem redFSAuthDFPaperMultiProg_sess_isQueryBoundP_of_eq_min
    (L B Δcka qep maxSkip : ℕ) (la : Bool) (tL : Option ℕ) (t j q : ℕ)
    (R : CostedReduction OO IIM
      (_root_.CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E) .unit .unit .bool .bool)
    (hR : R = redFSAuthDFPaperMultiProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      L B Δcka qep maxSkip la tL t)
    (A : OracleComp (unifSpec + _root_.CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) Bool)
    (hA : A.IsQueryBoundP (· matches .inr _) q) :
    (R.eval (fun _ => A) ()).IsQueryBoundP
      (fun x => (match x with | .inl _ => false | .inr ⟨s, _⟩ => decide (s = j)) = true)
      (min (2 * q) (q + 2)) := by
  subst hR
  exact redFSAuthDFPaperMultiProg_sess_isQueryBoundP_min L B Δcka qep maxSkip la tL t j q A hA

theorem redFSAuthDFShiftedPaperMultiGenProg_sess_isQueryBoundP_of_eq_min
    (L B Δcka qep maxSkip l tStar : ℕ) (authH la : Bool) (j q : ℕ)
    (R : CostedReduction OO IIM
      (_root_.CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E) .unit .unit .bool .bool)
    (hR : R = redFSAuthDFShiftedPaperMultiGenProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      L B Δcka qep maxSkip l tStar authH la)
    (A : OracleComp (unifSpec + _root_.CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) Bool)
    (hA : A.IsQueryBoundP (· matches .inr _) q) :
    (R.eval (fun _ => A) ()).IsQueryBoundP
      (fun x => (match x with | .inl _ => false | .inr ⟨s, _⟩ => decide (s = j)) = true)
      (min (2 * q) (q + 2)) := by
  subst hR
  exact redFSAuthDFShiftedPaperMultiGenProg_sess_isQueryBoundP_min L B Δcka qep maxSkip l tStar authH la j q A hA


end

end Computational.Proofs.HeadlineV1.DeliverForgePaperMultiPotOK
