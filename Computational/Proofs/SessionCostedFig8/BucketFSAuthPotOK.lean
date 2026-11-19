/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks
import Computational.Proofs.ReductionDsl.Notation

/-!
# Per-Session `min (2 * q) (q + 2)` Query Bound for `redFSAuthMultiBucketProg`

Proves `redFSAuthMultiBucketProg_sess_isQueryBoundP_gen`: per-session `min (2 * q) (q + 2)` FS-AEAD
query bound on `redFSAuthMultiBucketProg.eval` for every session index `j`, by combining the `2 * q`
bound (at most `2` FS-AEAD queries per game query via `PotOKInvFS`) with the `q + 2` bound (each
session slot `j` has at most `1` send query using `bkPot` plus `1` receive query per game step).
Status: done. Falsification: boundary `q = 0` (`min 0 2 = 0` queries when adversary makes `0`
queries) and `q = 1` (`min 2 3 = 2` queries via root-init send + `vRecv`); no counterexample.-/

namespace Computational.Proofs.SessionCostedFig8.BucketFSAuthPotOK

public section

set_option autoImplicit false

open OracleSpec OracleComp
open _root_.ReductionDsl
  (Ty Env Expr Comp CostedReduction GameCodec handlerImpl isGameQuery)
open _root_.CryptoGames (Party)
open _root_.CryptoGames.CKA (CKAOp ckaSMQ ckaHdrTy ckaHdrCtTy)
open _root_.CryptoGames.PRFPRNG (FSHdrTag prngSig prngOps)
open _root_.CryptoGames.SM
  (MakesAtMostQueries pGet pSet otherE posTy)
open _root_.CryptoGames.SM.Engine
  (HooksC ConfigEC cGsTy cRecTy esTy
   cGsSt cGsEpoch cGsMk cGsSetStP cGsSetWin
   esG esH esAbort esMk esSetG esSetH cRecPos
   cEpMgmtE cDeleteE cAcceptE cRecordE cAfterCorrE
   mkPartiesE cGsInitE
   vpMk vpId vpTcur vpTcurNat vpΓ vpRoot vpVS vpVR vpSetVS vpSetVR
   vSendStep1C vSendC vRecvStep1C vRecvC
   commitEC deliverEC injectEC
   eval_bind eval_bind_ret eval_ret)
open _root_.CryptoGames.SM.Construction
  (Header PartyState healEpoch fsaeadMultiHeaderAdIface)
open Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth
  (fsMultiBucketSessBookTy fsMultiBucketHsTy fsMultiBucketVpTy
   mbHsBook mbHsMk
   mbHsGetBookAt mbHsSetBookAt mbHsSetCache mbHsSetTableAt
   mbHsSetSessionsAt mbHsSetLfWin
   lookupMultiBucketFC regSessMultiBucketE regSessOptMultiBucketE rootFSMultiBucketAuthC
   fsMultiBucketAuthStartSendC fsMultiBucketAuthStartRecvC
   fsMultiBucketAuthFsSendC fsMultiBucketAuthFsRecvC fsMultiBucketAuthCommitC
   rangeListBucketC fsMultiBucketAuthRevealC
   hooksFSMultiBucketAuthC initFSMultiBucketAuthEStateC
   redFSAuthMultiBucketProg redFSAuthMultiBucketProg_totalQueries)
open Computational.Proofs.ReductionDsl.SM.RedFSPotOKHooks
  (PotOKInvFS PotOKInvFS.bind' potInvFS_ret potInvFS_ite potInvFS_caseOpt potInvFS_caseSum
   potOKInvFS_simulateQ_handlerImpl_step1 isQueryBoundP_min_fs
   pGet_eval_st_fs pSet_eval_st_fs cEpMgmtE_some_st_fs cDeleteE_st_fs cAcceptE_st_fs
   cGsSetStP_st_fs cGsSetWin_st_fs cRecordE_st_fs cAfterCorrE_st_fs ite_fst_eq_fs)

section MultiBucketPotOK

variable
  {KC Γ CCoins T I KR RSt K SS RS M E : Type}
  {ckaInitA ckaInitB : KC → Γ} {ckaSend : Γ → CCoins → Γ × T × I} {ckaReceive : Γ → T → Γ × I}
  {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS} {fsInitReceiver : K → RS}
  {fsSend : SS → Header T → M → SS × E} {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
  {lam : I} {defaultE : E}
  {sampKR : ProbComp KR} {sampKC : ProbComp KC} {sampCCoins : ProbComp CCoins}
  {sampI : ProbComp I} {sampK : ProbComp K}

local notation "SP" => prngSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "OO" =>
  prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE
local notation "IIM" =>
  fsaeadMultiHeaderAdIface KC Γ CCoins T I KR RSt K SS RS M E
    sampKR sampKC sampCCoins sampI sampK
local notation "mVpTy" => @fsMultiBucketVpTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "mbHsTy" => @fsMultiBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "mBookTy" => @fsMultiBucketSessBookTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrTy" => ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrCtTy" => ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E

private abbrev sessPred (j : ℕ) :
    (unifSpec + OracleSpec.sigma
      (fun _ : ℕ => CryptoGames.FSAEAD.spec SS RS (Header T) M E)).Domain → Prop :=
  fun t => (match t with
    | .inl _ => false
    | .inr ⟨s, _⟩ => decide (s = j)) = true

private theorem multiIface_fwdU_zero (j n : ℕ) :
    ((IIM).fwdU n).IsQueryBoundP (sessPred (SS := SS) (RS := RS) (T := T) (M := M) (E := E) j) 0 := by
  change OracleComp.IsQueryBoundP
    (liftM (OracleSpec.query
      (spec := unifSpec + OracleSpec.sigma (fun _ : ℕ => CryptoGames.FSAEAD.spec SS RS (Header T) M E))
      (.inl n)))
    (sessPred j) 0
  rw [← bind_pure (liftM _), isQueryBoundP_query_bind_iff]
  exact ⟨Or.inl (by simp [sessPred]), fun _ => by simp⟩

private theorem potInvMultiFS_zero {Γ' : List (Ty SP)} {τ : Ty SP}
    (j : ℕ) (c : Comp OO IIM Γ' τ) (ρ : Env Γ') {B : τ.denote → ℕ} (n : ℕ)
    (hB : ∀ a, B a ≤ n) (hq : c.queries (fun _ => 1) (fun _ => 0) = 0) :
    PotOKInvFS (sessPred j) (fun _ => True) B (c.eval ρ) n :=
  ⟨fun _k hk =>
    (isQueryBoundP_bind
      (Comp.queryBound_eval (sessPred j) (fun _ => 1) (fun _ => 0)
        (fun _ _ _ => Nat.le_refl 1) (multiIface_fwdU_zero j) c ρ)
      (fun a _ => (hk a trivial).mono (hB a))).mono (by omega)⟩

private theorem potInvMultiFS_query (j : ℕ) (g : (IIM).Tag) {Γ' : List (Ty SP)}
    (argE : Expr OO Γ' ((IIM).dom g)) (ρ : Env Γ') (r n : ℕ)
    (hn : (if (argE.eval ρ).1 = j then 1 else 0) + r ≤ n) :
    PotOKInvFS (sessPred j) (fun _ => True) (fun _ => r)
      ((Comp.query (I := IIM) g argE).eval ρ) n := by
  refine ⟨fun k hk => ?_⟩
  have hQ : ((Comp.query (I := IIM) g argE).eval ρ).IsQueryBoundP (sessPred j)
      (if (argE.eval ρ).1 = j then 1 else 0) := by
    simp only [Comp.eval, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
    cases g <;> by_cases h : (argE.eval ρ).1 = j <;>
      simp [sessPred, h]
  exact (isQueryBoundP_bind hQ (fun a _ => hk a trivial)).mono hn

private structure HooksPotSpec (j : ℕ) {hsT : Ty SP}
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
  refine potInvFS_ite (fun _ => ?_) (fun _ => potInvFS_ret trivial (by simp [Expr.eval, Expr.v0]))
  rw [eval_bind]
  have hSS := hH.startSend (.fst (Expr.v0 (O := OO))) (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))
    (.add (CryptoGames.SM.Engine.vpTcurNat (.fst (.snd (.snd (.snd .v0))))) (.nat 1))
    (CryptoGames.SM.Engine.vpΓ (.fst (.snd (.snd (.snd .v0)))))
    (CryptoGames.SM.Engine.vpRoot (.fst (.snd (.snd (.snd .v0)))))
    (.snd (.snd (.snd (.snd .v0))))
    (.cons (hE.eval ρ, ctxE.eval ρ, pE.eval ρ, sE.eval ρ, rE.eval ρ) ρ) m
  simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSS
  refine PotOKInvFS.bindPot hSS (fun _ _ => ?_)
  refine potInvFS_caseOpt
    (fun _ => potInvFS_ret trivial (by simp [Expr.eval, Expr.v0]))
    (fun _ _ => potInvFS_ret trivial (by simp [Expr.eval, Expr.v1]))

private theorem vSendC_gen_potOKInv {j : ℕ} {hsT : Ty SP}
    {H : HooksC OO IIM (.base .γ) (.base .sig) (.sum (.base .ss) .nat) (.sum (.base .rs) .nat) hsT}
    {hPot : hsT.denote → ℕ} (hH : HooksPotSpec j H hPot) {Γ' : List (Ty SP)}
    (hE : Expr OO Γ' hsT) (ctxE : Expr OO Γ' (cGsTy mVpTy)) (pE : Expr OO Γ' .bool)
    (sE : Expr OO Γ' mVpTy) (mE : Expr OO Γ' (.base .msg))
    (pairE : Expr OO Γ' (.opt (.prod (.base .msg) (.base .msg))))
    (rE : Expr OO Γ' (.opt (.base .ccoins))) (ρ : Env Γ') (m : ℕ) :
    PotOKInvFS (sessPred j) (fun _ => True) (fun res => m + hPot res.2)
      ((vSendC H hE ctxE pE sE mE pairE rE).eval ρ) (1 + m + hPot (hE.eval ρ)) := by
  unfold vSendC; rw [eval_bind_ret, eval_bind]
  have h1 := vSendStep1C_gen_potOKInv hH (.fst (Expr.v0 (O := OO)))
    (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0))))
    (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))
    (.cons (hE.eval ρ, ctxE.eval ρ, pE.eval ρ, sE.eval ρ, mE.eval ρ, pairE.eval ρ, rE.eval ρ) ρ)
    (1 + m)
  simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at h1
  refine PotOKInvFS.bindPot h1 (fun step1Out _ => ?_)
  refine potInvFS_caseOpt
    (fun _ => potInvFS_ret trivial (by simp only [Expr.eval, Expr.v0, Env.get_cons_zero]; omega))
    (fun s1 _ => potInvFS_caseOpt
      (fun _ => potInvFS_ret trivial
        (by simp only [Expr.eval, Expr.v1, Env.get_cons_succ, Env.get_cons_zero]; omega))
      (fun v _ => ?_))
  rw [eval_bind]
  have hFS := hH.fsSend (.snd (Expr.v2 (O := OO))) (.fst (.snd .v3)) (.fst (.snd (.snd .v3)))
    (CryptoGames.SM.Engine.vpTcurNat .v1) .v0
    (.pair (CryptoGames.SM.Engine.vpTcurNat .v1) (CryptoGames.SM.Engine.vpTcur .v1))
    (.fst (.snd (.snd (.snd (.snd .v3))))) (.fst (.snd (.snd (.snd (.snd (.snd .v3))))))
    (.cons v (.cons s1 (.cons step1Out
      (.cons (hE.eval ρ, ctxE.eval ρ, pE.eval ρ, sE.eval ρ, mE.eval ρ, pairE.eval ρ, rE.eval ρ) ρ)))) m
  simp only [Expr.eval, Expr.v0, Expr.v2, Env.get_cons_zero, Env.get_cons_succ] at hFS
  refine PotOKInvFS.bindPot hFS (fun _ _ => ?_)
  refine potInvFS_caseOpt
    (fun _ => potInvFS_ret trivial (by simp [Expr.eval, Expr.v0]))
    (fun _ _ => potInvFS_ret trivial (by simp [Expr.eval, Expr.v1]))

private theorem vRecvStep1C_gen_potOKInv {j : ℕ} {hsT : Ty SP}
    {H : HooksC OO IIM (.base .γ) (.base .sig) (.sum (.base .ss) .nat) (.sum (.base .rs) .nat) hsT}
    {hPot : hsT.denote → ℕ} (hH : HooksPotSpec j H hPot) {Γ' : List (Ty SP)}
    (hE : Expr OO Γ' hsT) (ctxE : Expr OO Γ' (cGsTy mVpTy)) (pE : Expr OO Γ' .bool)
    (sE : Expr OO Γ' mVpTy) (cE : Expr OO Γ' hdrCtTy) (ρ : Env Γ') (m : ℕ) :
    PotOKInvFS (sessPred j) (fun _ => True) (fun res => m + hPot res.2)
      ((vRecvStep1C H hE ctxE pE sE cE).eval ρ) (m + hPot (hE.eval ρ)) := by
  unfold vRecvStep1C; rw [eval_bind_ret]
  refine potInvFS_ite (fun _ => ?_) (fun _ => potInvFS_ret trivial (by simp [Expr.eval, Expr.v0]))
  refine potInvFS_caseOpt
    (fun _ => potInvFS_ret trivial (by simp [Expr.eval, Expr.v0]))
    (fun Tn _ => ?_)
  rw [eval_bind]
  have hSR := hH.startRecv (.fst (Expr.v1 (O := OO))) (.fst (.snd .v1)) (.fst (.snd (.snd .v1)))
    (.fst (.fst (.snd (.snd (.snd (.snd .v1))))))
    (CryptoGames.SM.Engine.vpΓ (.fst (.snd (.snd (.snd .v1)))))
    (CryptoGames.SM.Engine.vpRoot (.fst (.snd (.snd (.snd .v1))))) .v0
    (.cons Tn (.cons (hE.eval ρ, ctxE.eval ρ, pE.eval ρ, sE.eval ρ, cE.eval ρ) ρ)) m
  simp only [Expr.eval, Expr.v1, Env.get_cons_zero, Env.get_cons_succ] at hSR
  refine PotOKInvFS.bindPot hSR (fun _ _ => ?_)
  refine potInvFS_caseOpt
    (fun _ => potInvFS_ret trivial (by simp [Expr.eval, Expr.v0]))
    (fun _ _ => potInvFS_caseOpt
      (fun _ => potInvFS_ret trivial (by simp [Expr.eval, Expr.v1]))
      (fun _ _ => potInvFS_ret trivial (by simp [Expr.eval, Expr.v2])))

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
    (fun _ => potInvFS_ret trivial (by simp only [Expr.eval, Expr.v0, Env.get_cons_zero]; omega))
    (fun _ => ?_)
  rw [eval_bind]
  have hStep1 := vRecvStep1C_gen_potOKInv hH (.fst (Expr.v0 (O := OO)))
    (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0))))
    (.fst (.snd (.snd (.snd (.snd .v0)))))
    (.cons (hE.eval ρ, ctxE.eval ρ, pE.eval ρ, sE.eval ρ, cE.eval ρ, recE.eval ρ) ρ) (1 + m)
  simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hStep1
  refine PotOKInvFS.bindPot hStep1 (fun step1Out _ => ?_)
  refine potInvFS_caseOpt
    (fun _ => potInvFS_ret trivial (by simp only [Expr.eval, Expr.v0, Env.get_cons_zero]; omega))
    (fun step1In _ => potInvFS_caseOpt
      (fun _ => potInvFS_ret trivial
        (by simp only [Expr.eval, Expr.v1, Env.get_cons_succ, Env.get_cons_zero]; omega))
      (fun s1 _ => potInvFS_caseOpt
        (fun _ => potInvFS_ret trivial
          (by simp only [Expr.eval, Expr.v2, Env.get_cons_succ, Env.get_cons_zero]; omega))
        (fun v _ => ?_)))
  rw [eval_bind]
  have hFR := hH.fsRecv (.snd (Expr.v3 (O := OO))) (.fst (.snd .v4)) (.fst (.snd (.snd .v4)))
    (.fst (.fst (.fst (.snd (.snd (.snd (.snd .v4))))))) .v0
    (.fst (.fst (.snd (.snd (.snd (.snd .v4)))))) (.snd (.fst (.snd (.snd (.snd (.snd .v4))))))
    (.snd (.snd (.snd (.snd (.snd .v4)))))
    (.cons v (.cons s1 (.cons step1In (.cons step1Out
      (.cons (hE.eval ρ, ctxE.eval ρ, pE.eval ρ, sE.eval ρ, cE.eval ρ, recE.eval ρ) ρ))))) m
  simp only [Expr.eval, Expr.v3, Env.get_cons_zero, Env.get_cons_succ] at hFR
  refine PotOKInvFS.bindPot hFR (fun _ _ => ?_)
  refine potInvFS_caseOpt
    (fun _ => potInvFS_ret trivial (by simp [Expr.eval, Expr.v0]))
    (fun _ _ => potInvFS_caseOpt
      (fun _ => potInvFS_ret trivial (by simp [Expr.eval, Expr.v1]))
      (fun _ _ => potInvFS_ret trivial (by simp [Expr.eval, Expr.v2])))

private def esPot {hsT : Ty SP} (hPot : hsT.denote → ℕ) (es : (esTy mVpTy hsT).denote) : ℕ :=
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
  have hFC := hH.commit (esH (.fst (Expr.v0 (O := OO)))) (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))
    (.fst (.snd (.snd (.snd .v0)))) (.snd (.snd (.snd (.snd .v0))))
    (.cons ((esE.pair ((CryptoGames.SM.Engine.cAcceptE L sE pE newE posE).pair
      (pE.pair (oldE.pair newE)))).eval ρ) ρ) m
  have hEq : m + hPot ((esH (.fst (Expr.v0 (O := OO)))).eval
      (.cons ((esE.pair ((CryptoGames.SM.Engine.cAcceptE L sE pE newE posE).pair
        (pE.pair (oldE.pair newE)))).eval ρ) ρ)) = m + esPot hPot (esE.eval ρ) := rfl
  rw [hEq] at hFC
  refine PotOKInvFS.bindPot hFC (fun _ _ => ?_)
  exact potInvFS_caseOpt
    (fun _ => potInvFS_ret trivial (by simp [esPot, esMk, Expr.eval, Expr.v0]))
    (fun _ _ => potInvFS_ret trivial (by simp [esPot, esMk, Expr.eval, Expr.v1]))

private theorem deliverEC_gen_potOKInv {j : ℕ} {hsT : Ty SP}
    {H : HooksC OO IIM (.base .γ) (.base .sig) (.sum (.base .ss) .nat) (.sum (.base .rs) .nat) hsT}
    {hPot : hsT.denote → ℕ} (hH : HooksPotSpec j H hPot) (L maxSkip : ℕ) (cfg : ConfigEC OO)
    {Γ' : List (Ty SP)} (esE : Expr OO Γ' (esTy mVpTy hsT)) (argE : Expr OO Γ' (.prod .bool hdrCtTy))
    (ρ : Env Γ') (m : ℕ) :
    PotOKInvFS (sessPred j) (fun _ => True) (fun x => m + esPot hPot x.2)
      ((deliverEC H L maxSkip cfg esE argE).eval ρ)
      (1 + m + esPot hPot (esE.eval ρ)) := by
  unfold deliverEC; rw [eval_bind_ret]
  refine potInvFS_ite
    (fun _ => potInvFS_ret trivial (by simp only [Expr.eval, Expr.v0, Env.get_cons_zero]; omega))
    (fun _ => potInvFS_caseOpt
      (fun _ => potInvFS_ret trivial (by simp only [Expr.eval, Expr.v0, Env.get_cons_zero]; omega))
      (fun r1 _ => ?_))
  rw [eval_bind]
  have hRecv := vRecvC_gen_potOKInv hH (esH (.fst (Expr.v1 (O := OO)))) (esG (.fst .v1))
    (.fst (.snd .v1)) (pGet (cGsSt (esG (.fst .v1))) (.fst (.snd .v1))) (.snd (.snd .v1)) (.some .v0)
    (.cons r1 (.cons (esE.eval ρ, argE.eval ρ) ρ)) m
  simp only [esH, Expr.eval, Expr.v1, Env.get_cons_zero, Env.get_cons_succ] at hRecv
  refine PotOKInvFS.bindPot hRecv (fun recvOut _ => ?_)
  refine potInvFS_caseOpt
    (fun _ => potInvFS_ret trivial (by simp [esPot, esMk, Expr.eval, Expr.v0]))
    (fun resIn _ => potInvFS_caseOpt
      (fun _ => potInvFS_ret trivial (by simp [esPot, esMk, Expr.eval, Expr.v1]))
      (fun tup _ => ?_))
  rw [eval_bind]
  have hCom := commitEC_gen_potOKInv hH L (esSetH (.fst (Expr.v4 (O := OO))) (.snd .v2))
    (esG (.fst .v4)) (.fst (.snd .v4)) (pGet (cGsSt (esG (.fst .v4))) (.fst (.snd .v4)))
    (.fst .v0) (cRecPos .v3)
    (.cons tup (.cons resIn (.cons recvOut (.cons r1 (.cons (esE.eval ρ, argE.eval ρ) ρ))))) m
  simp only [esPot, esSetH, esMk, Expr.eval, Expr.v2, Env.get_cons_zero, Env.get_cons_succ] at hCom
  refine PotOKInvFS.bindPot hCom (fun _ _ => ?_)
  exact potInvFS_caseOpt
    (fun _ => potInvFS_ret trivial (by simp [esPot, Expr.eval, Expr.v0]))
    (fun _ _ => potInvFS_ret trivial (by simp [esPot, esSetG, esMk, esH, Expr.eval, Expr.v0, Expr.v1]))

private theorem injectEC_gen_potOKInv {j : ℕ} {hsT : Ty SP}
    {H : HooksC OO IIM (.base .γ) (.base .sig) (.sum (.base .ss) .nat) (.sum (.base .rs) .nat) hsT}
    {hPot : hsT.denote → ℕ} (hH : HooksPotSpec j H hPot) (L Δ qep : ℕ) (cfg : ConfigEC OO)
    {Γ' : List (Ty SP)} (esE : Expr OO Γ' (esTy mVpTy hsT)) (argE : Expr OO Γ' (.prod .bool hdrCtTy))
    (ρ : Env Γ') (m : ℕ) :
    PotOKInvFS (sessPred j) (fun _ => True) (fun x => m + esPot hPot x.2)
      ((injectEC H L Δ qep cfg esE argE).eval ρ)
      (1 + m + esPot hPot (esE.eval ρ)) := by
  unfold injectEC; rw [eval_bind_ret]
  refine potInvFS_ite
    (fun _ => potInvFS_ret trivial (by simp only [Expr.eval, Expr.v0, Env.get_cons_zero]; omega))
    (fun _ => ?_)
  rw [eval_bind]
  have hRecv := vRecvC_gen_potOKInv hH (esH (.fst (Expr.v0 (O := OO)))) (esG (.fst .v0))
    (.fst (.snd .v0)) (pGet (cGsSt (esG (.fst .v0))) (.fst (.snd .v0))) (.snd (.snd .v0)) .none
    (.cons (esE.eval ρ, argE.eval ρ) ρ) m
  simp only [esH, Expr.eval, Expr.v0, Env.get_cons_zero] at hRecv
  refine PotOKInvFS.bindPot hRecv (fun recvOut _ => ?_)
  refine potInvFS_caseOpt
    (fun _ => potInvFS_ret trivial (by simp [esPot, esMk, Expr.eval, Expr.v0]))
    (fun resIn _ => potInvFS_caseOpt
      (fun _ => potInvFS_ret trivial (by simp [esPot, esSetH, esMk, Expr.eval, Expr.v0, Expr.v1]))
      (fun tup _ => potInvFS_ite
        (fun _ => potInvFS_ret trivial (by simp [esPot, esSetH, esMk, Expr.eval, Expr.v0, Expr.v2]))
        (fun _ => potInvFS_ite (fun _ => ?_)
          (fun _ => potInvFS_ret trivial
            (by simp [esPot, esSetG, esSetH, esMk, esH, Expr.eval, Expr.v0, Expr.v2])))))
  rw [eval_bind]
  have hCom := commitEC_gen_potOKInv hH L (esSetH (.fst (Expr.v3 (O := OO))) (.snd .v2))
    (esG (.fst .v3)) (.fst (.snd .v3)) (pGet (cGsSt (esG (.fst .v3))) (.fst (.snd .v3)))
    (.fst .v0) (.pair (otherE (.fst (.snd .v3)))
      (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
    (.cons tup (.cons resIn (.cons recvOut (.cons (esE.eval ρ, argE.eval ρ) ρ)))) m
  simp only [esPot, esSetH, esMk, Expr.eval, Expr.v2, Env.get_cons_zero, Env.get_cons_succ] at hCom
  refine PotOKInvFS.bindPot hCom (fun _ _ => ?_)
  exact potInvFS_caseOpt
    (fun _ => potInvFS_ret trivial (by simp [esPot, Expr.eval, Expr.v0]))
    (fun _ _ => potInvFS_ret trivial (by simp [esPot, esSetG, esMk, esH, Expr.eval, Expr.v0, Expr.v1]))

private theorem costedReduction_multi_isQueryBoundP
    {κ : Type} {G : OracleSpec.{0, 0} κ} {C : GameCodec SP G}
    (j : ℕ) (R : CostedReduction OO IIM G C .unit .unit .bool .bool)
    (pot : R.σ.denote → ℕ) (q : ℕ)
    (A : OracleComp (unifSpec + G) Bool)
    (hA' : A.IsQueryBoundP (isGameQuery (G := G)) q)
    (hTot : R.totalQueries (fun _ => 1) (fun _ => 0) q ≤ 2 * q)
    (hInit : PotOKInvFS (sessPred j) (fun _ : (Ty.prod .unit R.σ : Ty SP).denote => True)
      (fun as : (Ty.prod .unit R.σ : Ty SP).denote => q + pot as.2)
      (R.init.eval (Env.cons (t := .unit) () .nil)) (q + 2))
    (hStep : ∀ (m : ℕ) qv sv,
      PotOKInvFS (sessPred j) (fun _ => True) (fun x => m + pot x.2)
        (R.handle.eval (.cons sv (.cons qv .nil))) (1 + m + pot sv))
    (hFin : R.finish.queries (fun _ => 1) (fun _ => 0) = 0) :
    (R.eval (fun _ => A) ()).IsQueryBoundP (sessPred j) (min (2 * q) (q + 2)) := by
  have h2q : (R.eval (fun _ => A) ()).IsQueryBoundP (sessPred j) (2 * q) := by
    have hSyn := CostedReduction.queryBound_eval R (sessPred j) (fun _ => 1) (fun _ => 0)
      (fun _ _ _ => Nat.le_refl 1) (multiIface_fwdU_zero j) (fun _ => A) q (fun _ => hA') ()
    exact hSyn.mono (by omega)
  have hq2 : (R.eval (fun _ => A) ()).IsQueryBoundP (sessPred j) (q + 2) := by
    unfold CostedReduction.eval CostedReduction.impl
    refine hInit.run _ ?_
    rintro ⟨_, s0⟩ _
    have hSim := potOKInvFS_simulateQ_handlerImpl_step1 (fun _ => True) pot
      (multiIface_fwdU_zero j) R.handle (fun m qv sv _ => hStep m qv sv) hA' s0 trivial
    refine hSim.run _ ?_
    rintro ⟨bOut, sOut⟩ _
    have hF := Comp.queryBound_eval (sessPred j) (fun _ => 1) (fun _ => 0)
      (fun _ _ _ => Nat.le_refl 1) (multiIface_fwdU_zero j) R.finish (.cons sOut (.cons bOut .nil))
    exact hF.mono (by simp [hFin])
  exact isQueryBoundP_min_fs h2q hq2

private def bkPot (j : ℕ) (bk : ℕ → Option ((mBookTy).denote)) : ℕ :=
  match bk j with | none => 1 | some b => if b.1 then 0 else 1

private abbrev mbHPot (j : ℕ) (h : (mbHsTy).denote) : ℕ := bkPot j h.2.2.2.1

private theorem bkPot_le_one (j : ℕ) (bk : ℕ → Option ((mBookTy).denote)) : bkPot j bk ≤ 1 := by
  unfold bkPot; cases bk j with
  | none => exact Nat.le_refl 1
  | some b => dsimp only; cases b.1 <;> decide

private theorem bkPot_eq_one_of_get_false (j : ℕ) (bk : ℕ → Option ((mBookTy).denote))
    (hf : ((match bk j with | none => (false, (0, [])) | some b => b : (mBookTy).denote)).1 = false) :
    bkPot j bk = 1 := by
  unfold bkPot; cases h : bk j with
  | none => rfl
  | some b => simp [h] at hf; simp [hf]

private theorem ite_eq_proj_book {α β γ δ ε ζ : Type} {c : Prop} [Decidable c]
    (x y : α × β × γ × δ × ε × ζ) {z : ε} (hx : x.2.2.2.2.1 = z) (hy : y.2.2.2.2.1 = z) :
    (if c then x else y).2.2.2.2.1 = z := by
  by_cases hc : c <;> simp [hc, hx, hy]

private theorem regSessMultiBucketE_book (L : ℕ) (gMain : Bool) (tL : Option ℕ) {Γ' : List (Ty SP)}
    (hE : Expr OO Γ' mbHsTy) (tE : Expr OO Γ' .nat) (ikE : Expr OO Γ' (.base .i)) (ρ : Env Γ') :
    ((regSessMultiBucketE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) L gMain tL hE tE ikE).eval ρ).2.2.2.2.1 =
      (hE.eval ρ).2.2.2.1 := by
  simp only [regSessMultiBucketE, mbHsSetSessionsAt, mbHsMk, mbHsBook,
    Expr.eval, Expr.v0, Env.get_cons_zero]
  exact ite_eq_proj_book _ _ rfl rfl

private theorem regSessOptMultiBucketE_book (L : ℕ) (gMain : Bool) (tL : Option ℕ) {Γ' : List (Ty SP)}
    (hE : Expr OO Γ' mbHsTy) (tE : Expr OO Γ' .nat) (sidE : Expr OO Γ' (.opt (.base .i)))
    (ρ : Env Γ') :
    ((regSessOptMultiBucketE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) L gMain tL hE tE sidE).eval ρ).2.2.2.2.1 =
      (hE.eval ρ).2.2.2.1 := by
  simp only [regSessOptMultiBucketE, Expr.eval, Expr.v0, Env.get_cons_zero]
  cases h : sidE.eval ρ with
  | none => rfl
  | some ik =>
    have hSub := regSessMultiBucketE_book L gMain tL (.fst (Expr.v1 (O := OO))) (.fst (.snd .v1)) .v0
      (.cons ik (.cons ((hE.pair (tE.pair sidE)).eval ρ) ρ))
    simpa [Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ, h] using hSub

private theorem lookupMultiBucketFC_potOKInv (j L : ℕ) {Γ' : List (Ty SP)}
    (hE : Expr OO Γ' mbHsTy) (tE : Expr OO Γ' .nat) (ikE : Expr OO Γ' (.base .i)) (ρ : Env Γ') (m : ℕ) :
    PotOKInvFS (sessPred j) (fun _ => True) (fun res => m + mbHPot j res.2)
      ((lookupMultiBucketFC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L hE tE ikE).eval ρ) (m + mbHPot j (hE.eval ρ)) := by
  unfold lookupMultiBucketFC; rw [eval_bind_ret]
  refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => potInvFS_ret trivial (by simp [mbHPot, Expr.eval, Expr.v1]))
  rw [eval_bind]
  exact PotOKInvFS.bindPot
    (potInvMultiFS_zero j _ _ (m + mbHPot j (hE.eval ρ)) (fun _ => Nat.le_refl _) rfl)
    (fun _ _ => potInvFS_ret trivial
      (by simp [mbHPot, mbHsSetTableAt, mbHsMk, mbHsBook, Expr.eval, Expr.v1]))

private theorem rootFSMultiBucketAuthC_potOKInv (j L Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    {Γ' : List (Ty SP)} (hE : Expr OO Γ' mbHsTy) (tE : Expr OO Γ' .nat) (plE : Expr OO Γ' .bool)
    (ikE : Expr OO Γ' (.base .i)) (σE : Expr OO Γ' (.base .sig)) (ρ : Env Γ') (m : ℕ) :
    PotOKInvFS (sessPred j) (fun _ => True) (fun res => m + mbHPot j res.2)
      ((rootFSMultiBucketAuthC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L Δcka qep tL par hE tE plE ikE σE).eval ρ)
      (m + mbHPot j (hE.eval ρ)) := by
  unfold rootFSMultiBucketAuthC; rw [eval_bind_ret]
  refine potInvFS_ite (fun _ => potInvFS_ret trivial (by simp [mbHPot, Expr.eval, Expr.v0]))
    (fun _ => potInvFS_ite (fun _ => potInvFS_ite (fun _ => ?_) (fun _ => ?_))
      (fun _ => potInvFS_ite (fun _ => ?_)
        (fun _ => potInvFS_ite (fun _ => ?_)
          (fun _ => potInvFS_ret trivial (by simp [mbHPot, Expr.eval, Expr.v0])))))
  · rw [eval_bind]
    refine PotOKInvFS.bindPot
      (potInvMultiFS_zero j _ _ (m + mbHPot j (hE.eval ρ)) (fun _ => Nat.le_refl _) rfl) (fun _ _ => ?_)
    rw [eval_bind]
    exact PotOKInvFS.bindPot
      (potInvMultiFS_zero j _ _ (m + mbHPot j (hE.eval ρ)) (fun _ => Nat.le_refl _) rfl)
      (fun _ _ => potInvFS_ret trivial (by simp [mbHPot, Expr.eval, Expr.v2]))
  · rw [eval_bind]
    have hL := lookupMultiBucketFC_potOKInv (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) j L (.fst (Expr.v0 (O := OO)))
      (.fst (.snd .v0)) (.fst (.snd (.snd (.snd .v0))))
      (.cons ((hE.pair (tE.pair (plE.pair (ikE.pair σE)))).eval ρ) ρ) m
    simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hL
    exact PotOKInvFS.bindPot hL (fun _ _ => potInvFS_ret trivial (by simp [mbHPot, Expr.eval, Expr.v0]))
  · rw [eval_bind]
    refine PotOKInvFS.bindPot
      (potInvMultiFS_zero j _ _ (m + mbHPot j (hE.eval ρ)) (fun _ => Nat.le_refl _) rfl) (fun _ _ => ?_)
    rw [eval_bind]
    exact PotOKInvFS.bindPot
      (potInvMultiFS_zero j _ _ (m + mbHPot j (hE.eval ρ)) (fun _ => Nat.le_refl _) rfl)
      (fun _ _ => potInvFS_ret trivial (by simp [mbHPot, Expr.eval, Expr.v2]))
  · rw [eval_bind]
    have hL := lookupMultiBucketFC_potOKInv (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) j L (.fst (Expr.v0 (O := OO)))
      (.fst (.snd .v0)) (.fst (.snd (.snd (.snd .v0))))
      (.cons ((hE.pair (tE.pair (plE.pair (ikE.pair σE)))).eval ρ) ρ) m
    simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hL
    exact PotOKInvFS.bindPot hL (fun _ _ => potInvFS_ret trivial (by simp [mbHPot, Expr.eval, Expr.v0]))

private theorem fsMultiBucketAuthFsSendC_potOKInv (j Δcka : ℕ) (la : Bool) {Γ' : List (Ty SP)}
    (hE : Expr OO Γ' mbHsTy) (ctxE : Expr OO Γ' (cGsTy mVpTy)) (pE : Expr OO Γ' .bool)
    (tE : Expr OO Γ' .nat) (ssvE : Expr OO Γ' (.sum (.base .ss) .nat)) (hdrE : Expr OO Γ' hdrTy)
    (mE : Expr OO Γ' (.base .msg)) (pairE : Expr OO Γ' (.opt (.prod (.base .msg) (.base .msg))))
    (ρ : Env Γ') (m : ℕ) :
    PotOKInvFS (sessPred j) (fun _ => True) (fun res => m + mbHPot j res.2)
      ((fsMultiBucketAuthFsSendC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) Δcka la hE ctxE pE tE ssvE hdrE mE pairE).eval ρ)
      (1 + m + mbHPot j (hE.eval ρ)) := by
  unfold fsMultiBucketAuthFsSendC; rw [eval_bind_ret]
  refine potInvFS_caseSum
    (fun _ _ => potInvFS_ret trivial
      (by simp only [mbHPot, Expr.eval, Expr.v1, Env.get_cons_succ, Env.get_cons_zero]; omega))
    (fun sIdx _ => ?_)
  rw [eval_bind]
  refine PotOKInvFS.bindPot (Inv₁ := fun _ => True)
    (B₁ := fun oh => (if oh.1 then 1 else 0) + m + mbHPot j oh.2) ?_ (fun oh _ => ?_)
  · refine potInvFS_ite (fun hCond => ?_) (fun _ => ?_)
    · rw [eval_bind]
      have hCorrF :
          ((match (hE.eval ρ).2.2.2.1 sIdx with
            | none => (false, (0, []))
            | some b => b : (mBookTy).denote)).1 = false := by
        simp only [mbHsGetBookAt, mbHsBook, Expr.eval, Expr.v0, Expr.v1,
          Env.get_cons_zero, Env.get_cons_succ, Bool.and_eq_true, Bool.not_eq_true'] at hCond
        cases hB : (hE.eval ρ).2.2.2.1 sIdx <;> simp [hB] at hCond ⊢; exact hCond.2
      refine PotOKInvFS.bindPot
        (potInvMultiFS_query j _ _ _ ((if sIdx = j then 0 else 1) + m + mbHPot j (hE.eval ρ))
          (1 + m + mbHPot j (hE.eval ρ))
          (by simp only [Expr.eval, Expr.v0, Env.get_cons_zero]; split <;> omega))
        (fun _ _ => ?_)
      refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => ?_)
      · exact potInvFS_ret trivial (by simp [mbHPot, Expr.eval, Expr.v2])
      · refine potInvFS_ret trivial ?_
        simp only [mbHPot, mbHsSetBookAt, mbHsMk, mbHsBook, mbHsGetBookAt,
          Expr.eval, Expr.v2, Expr.v3, Env.get_cons_zero, Env.get_cons_succ]
        by_cases hsj : sIdx = j
        · subst hsj; have h1 := bkPot_eq_one_of_get_false sIdx _ hCorrF; rw [h1]; unfold bkPot; simp; omega
        · have hjs : j ≠ sIdx := Ne.symm hsj; unfold bkPot; simp [hsj, hjs]
    · exact potInvFS_ret trivial (by simp [mbHPot, Expr.eval, Expr.v1])
  · refine potInvFS_ite (fun hNotOk => ?_) (fun hOk => ?_)
    · exact potInvFS_ret trivial
        (by simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hNotOk ⊢; cases oh.1 <;> simp_all)
    · have hOkT : oh.1 = true := by
        simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hOk; cases h : oh.1 <;> simp_all
      simp only [hOkT, ↓reduceIte]; rw [eval_bind]
      refine PotOKInvFS.bindPot (Inv₁ := fun _ => True) (B₁ := fun _ => m + mbHPot j oh.2)
        ?_ (fun _ _ => ?_)
      · refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => ?_)
        · refine potInvMultiFS_query (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
            (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
            (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
            (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
            (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (sampKR := sampKR)
            (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
            j FSHdrTag.tr _ _ _ _ ?_; split <;> omega
        · refine potInvMultiFS_query (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
            (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
            (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
            (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
            (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (sampKR := sampKR)
            (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
            j FSHdrTag.ch _ _ _ _ ?_; split <;> omega
      · refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => ?_)
        · exact potInvFS_ret trivial (by simp [mbHPot, Expr.eval, Expr.v1])
        · refine potInvFS_ret trivial ?_
          simp only [mbHPot, mbHsSetBookAt, mbHsMk, mbHsBook, mbHsGetBookAt,
            Expr.eval, Expr.v0, Expr.v2, Expr.v3, Env.get_cons_zero, Env.get_cons_succ]
          unfold bkPot; dsimp only
          by_cases hsj : j = sIdx
          · subst hsj; cases oh.2.2.2.2.1 j <;> simp
          · simp [hsj]

private theorem fsMultiBucketAuthFsRecvC_potOKInv (j L B : ℕ) (la : Bool) (Δcka : ℕ := 1)
    {Γ' : List (Ty SP)}
    (hE : Expr OO Γ' mbHsTy) (ctxE : Expr OO Γ' (cGsTy mVpTy)) (pE : Expr OO Γ' .bool)
    (tE : Expr OO Γ' .nat) (rsvE : Expr OO Γ' (.sum (.base .rs) .nat))
    (hdrE : Expr OO Γ' hdrTy) (eE : Expr OO Γ' (.base .ct)) (recE : Expr OO Γ' (.opt cRecTy))
    (ρ : Env Γ') (m : ℕ) :
    PotOKInvFS (sessPred j) (fun _ => True) (fun res => m + mbHPot j res.2)
      ((fsMultiBucketAuthFsRecvC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L B la Δcka hE ctxE pE tE rsvE hdrE eE recE).eval ρ)
      (1 + m + mbHPot j (hE.eval ρ)) := by
  unfold fsMultiBucketAuthFsRecvC; rw [eval_bind_ret]
  refine potInvFS_caseSum (fun _ _ => ?_) (fun sIdx _ => ?_)
  · refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => ?_)
    · exact potInvFS_ret trivial
        (by simp only [mbHPot, Expr.eval, Expr.v1, Env.get_cons_succ, Env.get_cons_zero]; omega)
    · exact potInvFS_ret trivial
        (by simp only [mbHPot, Expr.eval, Expr.v2, Env.get_cons_succ, Env.get_cons_zero]; omega)
  · rw [eval_bind]
    refine PotOKInvFS.bindPot (Inv₁ := fun _ => True)
      (B₁ := fun oh => (if oh.1 then 1 else 0) + m + mbHPot j oh.2) ?_ (fun oh _ => ?_)
    · refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => ?_)
      · refine potInvFS_ite (fun hCond => ?_) (fun _ => ?_)
        · rw [eval_bind]
          have hCorrF :
              ((match (hE.eval ρ).2.2.2.1 sIdx with
                | none => (false, (0, []))
                | some b => b : (mBookTy).denote)).1 = false := by
            simp only [mbHsGetBookAt, mbHsBook, Expr.eval, Expr.v0, Expr.v1,
              Env.get_cons_zero, Env.get_cons_succ, Bool.and_eq_true, Bool.not_eq_true'] at hCond
            cases hB : (hE.eval ρ).2.2.2.1 sIdx <;> simp [hB] at hCond ⊢; exact hCond.2
          refine PotOKInvFS.bindPot
            (potInvMultiFS_query j _ _ _ ((if sIdx = j then 0 else 1) + m + mbHPot j (hE.eval ρ))
              (1 + m + mbHPot j (hE.eval ρ))
              (by simp only [Expr.eval, Expr.v0, Env.get_cons_zero]; split <;> omega))
            (fun _ _ => ?_)
          refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => ?_)
          · exact potInvFS_ret trivial (by simp [mbHPot, Expr.eval, Expr.v2])
          · refine potInvFS_ret trivial ?_
            simp only [mbHPot, mbHsSetBookAt, mbHsMk, mbHsBook, mbHsGetBookAt,
              Expr.eval, Expr.v2, Expr.v3, Env.get_cons_zero, Env.get_cons_succ]
            by_cases hsj : sIdx = j
            · subst hsj; have h1 := bkPot_eq_one_of_get_false sIdx _ hCorrF; rw [h1]; unfold bkPot; simp; omega
            · have hjs : j ≠ sIdx := Ne.symm hsj; unfold bkPot; simp [hsj, hjs]
        · exact potInvFS_ret trivial (by simp [mbHPot, Expr.eval, Expr.v1])
      · exact potInvFS_ret trivial (by simp [mbHPot, Expr.eval, Expr.v2])
    · refine potInvFS_ite (fun hNotOk => ?_) (fun hOk => ?_)
      · exact potInvFS_ret trivial
          (by simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hNotOk ⊢; cases oh.1 <;> simp_all)
      · have hOkT : oh.1 = true := by
          simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hOk; cases h : oh.1 <;> simp_all
        simp only [hOkT, ↓reduceIte]; rw [eval_bind]
        refine PotOKInvFS.bindPot (Inv₁ := fun _ => True) (B₁ := fun _ => m + mbHPot j oh.2)
          ?_ (fun _ _ => ?_)
        · refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => ?_)
          · refine potInvMultiFS_query (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
              (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
              (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
              (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
              (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (sampKR := sampKR)
              (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
              j FSHdrTag.ij _ _ _ _ ?_; split <;> omega
          · refine potInvMultiFS_query (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
              (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
              (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
              (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
              (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (sampKR := sampKR)
              (sampKC := sampKC) (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
              j FSHdrTag.dl _ _ _ _ ?_; split <;> omega
        · refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => ?_)
          · exact potInvFS_ret trivial (by simp [mbHPot, Expr.eval, Expr.v1])
          · refine potInvFS_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
            · exact potInvFS_ret trivial (by simp [mbHPot, Expr.eval, Expr.v3])
            · refine potInvFS_ite (fun _ => ?_) (fun _ => ?_)
              · exact potInvFS_ret trivial
                  (by simp [mbHPot, mbHsSetLfWin, mbHsMk, mbHsBook, Expr.eval, Expr.v3])
              · refine potInvFS_ret trivial ?_
                simp only [mbHPot, mbHsSetBookAt, mbHsMk, mbHsBook, mbHsGetBookAt,
                  Expr.eval, Expr.v0, Expr.v3, Expr.v4, Env.get_cons_zero, Env.get_cons_succ]
                unfold bkPot; dsimp only
                by_cases hsj : j = sIdx
                · subst hsj; cases oh.2.2.2.2.1 j <;> simp
                · simp [hsj]

private theorem rangeListBucketC_queries (L : ℕ) (w : FSHdrTag → ℕ) {Γ' : List (Ty SP)} :
    (rangeListBucketC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) (Γ' := Γ') L).queries
      w (fun _ => 0) = 0 := by
  simp [rangeListBucketC, Comp.queries]

private theorem fsMultiBucketAuthRevealC_potOKInv (j L : ℕ) (gMain la : Bool) (tL : Option ℕ)
    {Γ' : List (Ty SP)} (hE : Expr OO Γ' mbHsTy) (ctxE : Expr OO Γ' (cGsTy mVpTy))
    (pE : Expr OO Γ' .bool) (vpE : Expr OO Γ' mVpTy) (ρ : Env Γ') (m : ℕ) :
    PotOKInvFS (sessPred j) (fun _ => True) (fun res => m + mbHPot j res.2)
      ((fsMultiBucketAuthRevealC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L gMain la tL hE ctxE pE vpE).eval ρ)
      (1 + m + mbHPot j (hE.eval ρ)) := by
  unfold fsMultiBucketAuthRevealC; rw [eval_bind_ret]
  refine potInvFS_ite
    (fun _ => potInvFS_ret trivial
      (by simp only [mbHPot, Expr.eval, Expr.v0, Env.get_cons_zero]; omega))
    (fun _ => ?_)
  rw [eval_bind]
  refine PotOKInvFS.bindPot (Inv₁ := fun _ => True) (B₁ := fun sh => m + mbHPot j sh.2)
    ?_ (fun sh _ => ?_)
  · refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => ?_)
    · exact potInvFS_ret trivial
        (by simp only [mbHPot, Expr.eval, Expr.v0, Env.get_cons_zero]; omega)
    · refine potInvFS_caseSum (fun _ _ => ?_) (fun sIdx _ => ?_)
      · exact potInvFS_ret trivial
          (by simp only [mbHPot, Expr.eval, Expr.v2, Env.get_cons_succ, Env.get_cons_zero]; omega)
      · rw [eval_bind]
        refine PotOKInvFS.bindPot
          (potInvMultiFS_query j _ _ _ (m + mbHPot j (hE.eval ρ)) (1 + m + mbHPot j (hE.eval ρ))
            (by split <;> omega))
          (fun _ _ => ?_)
        refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => ?_)
        · exact potInvFS_ret trivial (by simp [mbHPot, Expr.eval, Expr.v3])
        · refine potInvFS_ret trivial ?_
          simp only [mbHPot, mbHsSetBookAt, mbHsMk, mbHsBook,
            Expr.eval, Expr.v2, Expr.v4, Env.get_cons_zero, Env.get_cons_succ]
          unfold bkPot; dsimp only; by_cases hsj : j = sIdx <;> simp [hsj]
  · refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => ?_)
    · exact potInvFS_ret trivial (by simp [mbHPot, Expr.eval, Expr.v0])
    · rw [eval_bind]
      refine PotOKInvFS.bindPot
        (potInvMultiFS_zero j _ _ (m + mbHPot j sh.2) (fun _ => Nat.le_refl _)
          (rangeListBucketC_queries L (fun _ => 1)))
        (fun _ _ => ?_)
      refine potInvFS_ite (fun _ => ?_) (fun _ => ?_) <;>
        exact potInvFS_ret trivial (by simp [mbHPot, Expr.eval, Expr.v2])

private theorem hooksFSMultiBucketAuthC_potSpec
    (j L B Δcka qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par la : Bool) :
    HooksPotSpec j
      (hooksFSMultiBucketAuthC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
        L B Δcka qep gMain tL par la) (mbHPot j) where
  startSend hE ctxE _ tE γE σE rE ρ m := by
    unfold hooksFSMultiBucketAuthC fsMultiBucketAuthStartSendC; dsimp only; rw [eval_bind_ret, eval_bind]
    refine PotOKInvFS.bindPot
      (potInvFS_caseOpt
        (fun _ => potInvMultiFS_zero j _ _ (m + mbHPot j (hE.eval ρ)) (fun _ => Nat.le_refl _) rfl)
        (fun _ _ => potInvFS_ret trivial (Nat.le_refl _))) (fun coins _ => ?_)
    rw [eval_bind]
    have hR := rootFSMultiBucketAuthC_potOKInv (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      j L Δcka qep tL par (.fst (Expr.v1 (O := OO))) (.fst (.snd (.snd .v1)))
      (Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.postLeakBucketE tL (.fst (.snd .v1)))
      (.snd (.snd (Expr.op (O := OO) CKAOp.ckaSend
        (.pair (.fst (.snd (.snd (.snd .v1)))) .v0))))
      (.fst (.snd (.snd (.snd (.snd .v1)))))
      (.cons coins (.cons ((hE.pair (ctxE.pair (tE.pair (γE.pair (σE.pair rE))))).eval ρ) ρ)) m
    simp only [Expr.eval, Expr.v1, Env.get_cons_zero, Env.get_cons_succ] at hR
    refine PotOKInvFS.bindPot hR (fun rOut _ => potInvFS_ret trivial ?_)
    have hReg := regSessOptMultiBucketE_book L gMain tL (.snd (Expr.v0 (O := OO)))
      (.fst (.snd (.snd .v2))) (.snd (.snd (.fst .v0)))
      (.cons rOut (.cons coins
        (.cons ((hE.pair (ctxE.pair (tE.pair (γE.pair (σE.pair rE))))).eval ρ) ρ)))
    dsimp only [mbHPot, mbHsSetCache, mbHsMk, mbHsBook,
      Expr.eval, Expr.v0, Expr.v2, Env.get_cons_zero, Env.get_cons_succ] at hReg ⊢
    rw [hReg]
  startRecv hE ctxE _ tE γE σE tnE ρ m := by
    unfold hooksFSMultiBucketAuthC fsMultiBucketAuthStartRecvC; dsimp only; rw [eval_bind_ret]
    refine potInvFS_caseOpt (fun _ => ?_)
      (fun _ _ => potInvFS_ret trivial (by simp [mbHPot, Expr.eval, Expr.v1]))
    refine potInvFS_ite (fun _ => ?_) (fun _ => ?_)
    · refine potInvFS_ite
        (fun _ => potInvFS_ret trivial (by simp [mbHPot, Expr.eval, Expr.v0]))
        (fun _ => potInvFS_ret trivial (by simp [mbHPot, Expr.eval, Expr.v0]))
    · refine potInvFS_ite (fun _ => ?_)
        (fun _ => potInvFS_ret trivial (by simp [mbHPot, Expr.eval, Expr.v0]))
      refine potInvFS_ite
        (fun _ => potInvFS_ret trivial (by simp [mbHPot, Expr.eval, Expr.v0]))
        (fun _ => potInvFS_ite
          (fun _ => potInvFS_ret trivial (by simp [mbHPot, Expr.eval, Expr.v0]))
          (fun _ => potInvFS_ite (fun _ => ?_) (fun _ => ?_)))
      · rw [eval_bind]
        have hL := lookupMultiBucketFC_potOKInv (sampKR := sampKR) (sampKC := sampKC)
          (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
          j L (.fst (Expr.v0 (O := OO))) (.fst (.snd (.snd .v0)))
          (.snd (Expr.op (O := OO) CKAOp.ckaReceive
            (.pair (.fst (.snd (.snd (.snd .v0)))) (.snd (.snd (.snd (.snd (.snd .v0))))))))
          (.cons ((hE.pair (ctxE.pair (tE.pair (γE.pair (σE.pair tnE))))).eval ρ) ρ) m
        simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hL
        refine PotOKInvFS.bindPot hL (fun lOut _ => potInvFS_ret trivial ?_)
        have hReg := regSessMultiBucketE_book L false tL (.snd (Expr.v0 (O := OO)))
          (.fst (.snd (.snd .v1)))
          (.snd (Expr.op (O := OO) CKAOp.ckaReceive
            (.pair (.fst (.snd (.snd (.snd .v1)))) (.snd (.snd (.snd (.snd (.snd .v1))))))))
          (.cons lOut (.cons ((hE.pair (ctxE.pair (tE.pair (γE.pair (σE.pair tnE))))).eval ρ) ρ))
        dsimp only [mbHPot, Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ] at hReg ⊢
        rw [hReg]
      · refine potInvFS_ite (fun _ => ?_)
          (fun _ => potInvFS_ret trivial (by simp [mbHPot, Expr.eval, Expr.v0]))
        rw [eval_bind]
        have hL := lookupMultiBucketFC_potOKInv (sampKR := sampKR) (sampKC := sampKC)
          (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
          j L (.fst (Expr.v0 (O := OO))) (.fst (.snd (.snd .v0)))
          (.snd (Expr.op (O := OO) CKAOp.ckaReceive
            (.pair (.fst (.snd (.snd (.snd .v0)))) (.snd (.snd (.snd (.snd (.snd .v0))))))))
          (.cons ((hE.pair (ctxE.pair (tE.pair (γE.pair (σE.pair tnE))))).eval ρ) ρ) m
        simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hL
        exact PotOKInvFS.bindPot hL (fun _ _ => potInvFS_ret trivial (by simp [mbHPot, Expr.eval, Expr.v0]))
  fsSend := fsMultiBucketAuthFsSendC_potOKInv j Δcka la
  fsRecv := fsMultiBucketAuthFsRecvC_potOKInv j L B la Δcka
  commit _ _ _ _ _ _ _ := by
    unfold hooksFSMultiBucketAuthC fsMultiBucketAuthCommitC; dsimp only
    exact potInvFS_ret trivial (Nat.le_refl _)
  reveal := fsMultiBucketAuthRevealC_potOKInv j L gMain la tL

/-- Per-session `min (2 * q) (q + 2)` FS-AEAD query bound for `redFSAuthMultiBucketProg`. -/
theorem redFSAuthMultiBucketProg_sess_isQueryBoundP_gen
    (L B Δcka qep maxSkip : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool) (j q : ℕ)
    (A : OracleComp (unifSpec + _root_.CryptoGames.SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) Bool)
    (hA : MakesAtMostQueries A q) :
    ((redFSAuthMultiBucketProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
        L B Δcka qep maxSkip gMain la tL par).eval (fun _ => A) ()).IsQueryBoundP
      (fun x => (match x with | .inl _ => false | .inr ⟨s, _⟩ => decide (s = j)) = true)
      (min (2 * q) (q + 2)) := by
  let R := redFSAuthMultiBucketProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    L B Δcka qep maxSkip gMain la tL par
  have hSpec := hooksFSMultiBucketAuthC_potSpec (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    j L B Δcka qep gMain tL par la
  refine costedReduction_multi_isQueryBoundP j R (fun st => esPot (mbHPot j) st.1) q A
    (hA.of_imp (fun x hx => by cases x <;> [cases hx; rfl]))
    (redFSAuthMultiBucketProg_totalQueries L B Δcka qep maxSkip gMain la tL par q) ?_ ?_
    (by simp [R, redFSAuthMultiBucketProg, Comp.queries])
  · refine potInvMultiFS_zero j _ _ (q + 2) (fun as => ?_)
      (by cases gMain <;> simp [R, redFSAuthMultiBucketProg, initFSMultiBucketAuthEStateC,
        rootFSMultiBucketAuthC, lookupMultiBucketFC, Comp.queries])
    have h1 := bkPot_le_one j as.2.1.2.1.2.2.2.1; dsimp only [esPot, mbHPot]; omega
  · intro m qv sv
    dsimp only [R, redFSAuthMultiBucketProg] at sv qv ⊢; rw [eval_bind_ret]
    refine potInvFS_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
    · refine potInvFS_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
      · refine potInvFS_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
        · refine potInvFS_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
          · rw [eval_bind_ret]
            refine potInvFS_ite (fun _ => ?_) (fun _ => ?_)
            · exact potInvFS_ret trivial
                (by simp only [esPot, Expr.eval, Expr.v0, Expr.v5, Env.get_cons_succ, Env.get_cons_zero]; omega)
            · refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => ?_)
              · exact potInvFS_ret trivial
                  (by simp only [esPot, Expr.eval, Expr.v0, Expr.v5, Env.get_cons_succ, Env.get_cons_zero]; omega)
              · rw [eval_bind]
                refine PotOKInvFS.bindPot (vSendC_gen_potOKInv hSpec _ _ _ _ _ _ _ _ m) (fun _ _ => ?_)
                refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => ?_)
                · exact potInvFS_ret trivial (by simp [esPot, esMk, Expr.eval, Expr.v0])
                · exact potInvFS_ret trivial (by simp [esPot, esMk, Expr.eval, Expr.v1])
          · exact potInvFS_ret trivial
              (by simp only [esPot, Expr.eval, Expr.v0, Expr.v4, Env.get_cons_succ, Env.get_cons_zero]; omega)
        · rw [eval_bind]
          exact PotOKInvFS.bindPot (deliverEC_gen_potOKInv hSpec L maxSkip _ _ _ _ m)
            (fun _ _ => potInvFS_ret trivial (by simp [Expr.eval, Expr.v0]))
      · rw [eval_bind]
        exact PotOKInvFS.bindPot (injectEC_gen_potOKInv hSpec L (2 + Δcka) qep _ _ _ _ m)
          (fun _ _ => potInvFS_ret trivial (by simp [Expr.eval, Expr.v0]))
    · refine potInvFS_ite (fun _ => ?_) (fun _ => ?_)
      · exact potInvFS_ret trivial
          (by simp only [esPot, Expr.eval, Expr.v0, Expr.v1, Env.get_cons_succ, Env.get_cons_zero]; omega)
      · rw [eval_bind]
        refine PotOKInvFS.bindPot (fsMultiBucketAuthRevealC_potOKInv j L gMain la tL _ _ _ _ _ m)
          (fun _ _ => ?_)
        refine potInvFS_caseOpt (fun _ => ?_) (fun _ _ => ?_)
        · exact potInvFS_ret trivial (by simp [esPot, esMk, Expr.eval, Expr.v0])
        · exact potInvFS_ret trivial (by simp [esPot, esMk, Expr.eval, Expr.v1])

end MultiBucketPotOK

end

end Computational.Proofs.SessionCostedFig8.BucketFSAuthPotOK
