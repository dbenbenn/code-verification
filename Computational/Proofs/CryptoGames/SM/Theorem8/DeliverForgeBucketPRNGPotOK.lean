/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGDefs -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.SM.RedPRNGPotOK
import Computational.Proofs.ReductionDsl.Notation

set_option autoImplicit false

public section

open OracleSpec OracleComp

namespace CryptoGames.SM.Construction

open ReductionDsl
open scoped Computational.Proofs.ReductionDsl.Notation
open CryptoGames.CKA
open CryptoGames.PRFPRNG
open CryptoGames.SM.Engine

section HooksPRNGBucketCDF

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}

local notation "Spb" => prngSig KC Γ CCoins T I KR RSt K SS RS M E

variable
  {ckaInitA : KC → Γ}
  {ckaInitB : KC → Γ}
  {ckaSend : Γ → CCoins → Γ × T × I}
  {ckaReceive : Γ → T → Γ × I}
  {prngInit : KR → RSt}
  {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS}
  {fsInitReceiver : K → RS}
  {fsSend : SS → Header T → M → SS × E}
  {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool}
  {eqI : I → I → Bool}
  {eqM : M → M → Bool}
  {eqE : E → E → Bool}
  {lam : I}
  {defaultE : E}
  {sampKR : ProbComp KR}
  {sampKC : ProbComp KC}
  {sampCCoins : ProbComp CCoins}
  {sampI : ProbComp I}
  {sampK : ProbComp K}

local notation "OOpb" =>
  prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE

local notation "IIpb" =>
  prngIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK

local notation "hdrTyPb" => ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrCtTyPb" => ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "psTyPb" => ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "pbHsTyPb" => @prngBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "pbVpTyPb" => @prngVpTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "pbEsTyPb" => @prngBucketEsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "pbRedEsTyPb" => @prngBucketRedEsTy KC Γ CCoins T I KR RSt K SS RS M E


section PbPotOK

open Computational.Proofs.ReductionDsl.SM.RedPRNGPotOK
open CryptoGames.SM
  (partyDec partyDec_partyEnc sendsInE otherE pGet
   orE isSomeE letE_eval orE_eval sendsInE_eval)

local notation "P_prng" => isGameQuery (G := CryptoGames.PRFPRNG.spec RSt I K)

private def pbPot (mo : Mode) (es : (Ty.denote pbEsTyPb)) : ℕ :=
  if es.2.2 then 0 else prngVpReady mo es.1.1.1 + prngVpReady mo es.1.1.2

private theorem pbPot_mk_eq (mo : Mode)
    {g1 g2 : (@cGsTy KC Γ CCoins T I KR RSt K SS RS M E pbVpTyPb).denote}
    {h1 h2 : (Ty.denote pbHsTyPb)} {ab : Bool} (hst : g1.1 = g2.1) :
    pbPot mo (g1, h1, ab) = pbPot mo (g2, h2, ab) := by
  simp only [pbPot, hst]

private theorem rootPRNGBucketHybridC_potOKS (L Δbucket : ℕ) (tL : Option ℕ) (par : Bool)
    (t : ℕ) {Γ' : List (Ty Spb)}
    (hE : Expr OOpb Γ' pbHsTyPb) (tE : Expr OOpb Γ' .nat) (plE : Expr OOpb Γ' .bool)
    (ikE : Expr OOpb Γ' (.base .i)) (σvE : Expr OOpb Γ' (.opt (.base .sig)))
    (ρ : Env Γ') (r : ℕ) :
    PotOKSPrng P_prng (fun _ => r)
      ((rootPRNGBucketHybridC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L Δbucket tL par t hE tE plE ikE σvE).eval ρ)
      ((if decide (tE.eval ρ ≤ t) then 2 else 0) + r) := by
  unfold rootPRNGBucketHybridC; rw [eval_bind_ret]
  refine potSPrng_ite (fun _ => ?_) (fun hle => ?_)
  · exact potSPrng_comp_const _ _ r _ (fun _ => Nat.le_refl r) (by simp [Comp.queries])
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hle
    have hleTrue : decide (tE.eval ρ ≤ t) = true :=
      decide_eq_true (Nat.le_of_not_lt (of_decide_eq_false hle))
    exact potSPrng_comp_const _ _ r _ (fun _ => Nat.le_refl r)
      (by simp [prngProcessCorrC, Comp.queries, hleTrue])

private theorem prngBucketStartSendC_potOKS (L Δbucket : ℕ) (tL : Option ℕ) (par : Bool)
    (t : ℕ) {Γ' : List (Ty Spb)}
    (hE : Expr OOpb Γ' pbHsTyPb) (ctxE : Expr OOpb Γ' (cGsTy pbVpTyPb))
    (pE : Expr OOpb Γ' .bool) (tE : Expr OOpb Γ' .nat) (γE : Expr OOpb Γ' (.base .γ))
    (σvE : Expr OOpb Γ' (.opt (.base .sig))) (rE : Expr OOpb Γ' (.opt (.base .ccoins)))
    (ρ : Env Γ') (r : ℕ) :
    PotOKSPrng P_prng (fun _ => r)
      ((prngBucketStartSendC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L Δbucket tL par t hE ctxE pE tE γE σvE rE).eval ρ)
      ((if decide (tE.eval ρ ≤ t) then 2 else 0) + r) := by
  unfold prngBucketStartSendC; rw [eval_bind_ret, eval_bind]
  refine PotOKSPrng.bindPot
    (potSPrng_comp_const _ _ ((if decide (tE.eval ρ ≤ t) then 2 else 0) + r)
      ((if decide (tE.eval ρ ≤ t) then 2 else 0) + r)
      (fun _ => Nat.le_refl _) (by simp [Comp.queries])) (fun coins => ?_)
  rw [eval_bind]
  refine PotOKSPrng.bindPot ?_ (fun _ =>
    potSPrng_caseOpt (fun _ => potSPrng_ret (Nat.le_refl r))
      (fun _ _ => potSPrng_ret (Nat.le_refl r)))
  simpa only [Expr.eval, Expr.v1, Env.get_cons_zero, Env.get_cons_succ] using
    rootPRNGBucketHybridC_potOKS (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L Δbucket tL par t
      _ (.fst (.snd (.snd .v1)))
      (postLeakBucketE tL (.fst (.snd .v1)))
      (.snd (.snd (Expr.op (O := OOpb) CKAOp.ckaSend (.pair (.fst (.snd (.snd (.snd .v1)))) .v0))))
      (.fst (.snd (.snd (.snd (.snd .v1)))))
      (.cons coins (.cons (hE.eval ρ, ctxE.eval ρ, tE.eval ρ, γE.eval ρ, σvE.eval ρ, rE.eval ρ) ρ)) r

private theorem prngBucketStartRecvC_potOKS (L Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool)
    (t : ℕ) {Γ' : List (Ty Spb)}
    (hE : Expr OOpb Γ' pbHsTyPb) (ctxE : Expr OOpb Γ' (cGsTy pbVpTyPb))
    (pE : Expr OOpb Γ' .bool) (tE : Expr OOpb Γ' .nat) (γE : Expr OOpb Γ' (.base .γ))
    (σvE : Expr OOpb Γ' (.opt (.base .sig))) (tnE : Expr OOpb Γ' (.base .t))
    (ρ : Env Γ') (r : ℕ) :
    PotOKSPrng P_prng (fun _ => r)
      ((prngBucketStartRecvC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L Δbucket qep tL par t hE ctxE pE tE γE σvE tnE).eval ρ)
      ((if decide (tE.eval ρ = t) then 1 else 0) + r) := by
  unfold prngBucketStartRecvC; rw [eval_bind_ret]
  refine potSPrng_caseOpt (fun _ => ?_) (fun _ _ => potSPrng_ret (by omega))
  refine potSPrng_ite (fun _ => ?_) (fun _ => potSPrng_ret (by omega))
  refine potSPrng_ite (fun _ => potSPrng_ret (by omega)) (fun _ => ?_)
  refine potSPrng_ite
    (fun _ => potSPrng_comp_const _ _ r _ (fun _ => Nat.le_refl r) (by simp [Comp.queries]))
    (fun _ => ?_)
  refine potSPrng_ite (fun hEq => ?_)
    (fun _ => potSPrng_comp_const _ _ r _ (fun _ => Nat.le_refl r) (by simp [Comp.queries]))
  have hEq' : decide (tE.eval ρ = t) = true := by
    simpa [Expr.eval, Expr.v0, Env.get_cons_zero] using hEq
  exact potSPrng_comp_const _ _ r _ (fun _ => Nat.le_refl r) (by simp [Comp.queries, hEq'])

private def pbVpOptPost (mo : Mode) (m m_other : ℕ)
    (res : (Ty.prod (.opt pbVpTyPb) pbHsTyPb : Ty Spb).denote) : ℕ :=
  match res.1 with
  | none => m
  | some vp' => m + m_other + prngVpReady mo vp'

private theorem pb_vSendStep1C_potOKS (L B Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    {Γ' : List (Ty Spb)} (hE : Expr OOpb Γ' pbHsTyPb) (ctxE : Expr OOpb Γ' (cGsTy pbVpTyPb))
    (pE : Expr OOpb Γ' .bool) (sE : Expr OOpb Γ' pbVpTyPb) (rE : Expr OOpb Γ' (.opt (.base .ccoins)))
    (ρ : Env Γ') (m m_other : ℕ) :
    PotOKSPrng P_prng (pbVpOptPost (Mode.mk true tL t) m m_other)
      ((vSendStep1C (hooksPRNGBucketParPaperC (sampKR := sampKR) (sampKC := sampKC)
          (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B Δbucket qep tL par t)
        hE ctxE pE sE rE).eval ρ)
      (1 + m + m_other + prngVpReady (Mode.mk true tL t) (sE.eval ρ)) := by
  unfold vSendStep1C; rw [eval_bind_ret]
  refine potSPrng_ite (fun hs => ?_) (fun _ => potSPrng_ret (by simp [pbVpOptPost, Expr.eval, Expr.v0]))
  rw [sendsInE_eval _ _ _ (partyDec (sE.eval ρ).1) (by simp [vpId, Expr.eval, Expr.v0])] at hs
  simp only [vpTcurNat, Expr.eval, Expr.v0, Env.get_cons_zero] at hs
  dsimp only [hooksPRNGBucketParPaperC]; rw [eval_bind]
  have hSS := prngBucketStartSendC_potOKS (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    L Δbucket tL par t (.fst (Expr.v0 (O := OOpb))) (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))
    (.add (vpTcurNat (.fst (.snd (.snd (.snd .v0))))) (.nat 1))
    (vpΓ (.fst (.snd (.snd (.snd .v0))))) (vpRoot (.fst (.snd (.snd (.snd .v0)))))
    (.snd (.snd (.snd (.snd .v0))))
    (.cons (hE.eval ρ, ctxE.eval ρ, pE.eval ρ, sE.eval ρ, rE.eval ρ) ρ) (m + m_other)
  simp only [vpTcurNat, Expr.eval, Expr.v0, Env.get_cons_zero] at hSS
  have hBud :
      (if decide ((sE.eval ρ).2.2.2.2.2.2 + 1 ≤ t) then 2 else 0) + (m + m_other) ≤
        1 + m + m_other + prngVpReady (Mode.mk true tL t) (sE.eval ρ) := by
    simp only [prngVpReady, prngReady, hs, Bool.true_and]; split <;> omega
  refine ⟨fun {_} k hk' => (PotOKSPrng.bindPot hSS (fun _ => ?_)).run k hk' |>.mono hBud⟩
  refine potSPrng_caseOpt (fun _ => potSPrng_ret (by simp [pbVpOptPost, Expr.eval])) (fun _ _ => ?_)
  have hNextFalse := party_sendsIn_succ_false _ _ hs
  exact potSPrng_ret (by
    simp [pbVpOptPost, prngVpReady, prngReady, vpMk, vpId, vpTcurNat,
      Expr.eval, Expr.v0, Expr.v2, hNextFalse])

private def pbVSendPost (mo : Mode) (m m_other : ℕ)
    (res : (Ty.prod (.opt (.prod pbVpTyPb hdrCtTyPb)) pbHsTyPb : Ty Spb).denote) : ℕ :=
  match res.1 with
  | none => m
  | some (vp', _) => m + m_other + prngVpReady mo vp'

private theorem pb_vSendC_potOKS (L B Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    {Γ' : List (Ty Spb)} (hE : Expr OOpb Γ' pbHsTyPb) (ctxE : Expr OOpb Γ' (cGsTy pbVpTyPb))
    (pE : Expr OOpb Γ' .bool) (sE : Expr OOpb Γ' pbVpTyPb) (mE : Expr OOpb Γ' (.base .msg))
    (pairE : Expr OOpb Γ' (.opt (.prod (.base .msg) (.base .msg))))
    (rE : Expr OOpb Γ' (.opt (.base .ccoins))) (ρ : Env Γ') (m m_other : ℕ) :
    PotOKSPrng P_prng (pbVSendPost (Mode.mk true tL t) m m_other)
      ((vSendC (hooksPRNGBucketParPaperC (sampKR := sampKR) (sampKC := sampKC)
          (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B Δbucket qep tL par t)
        hE ctxE pE sE mE pairE rE).eval ρ)
      (1 + m + m_other + prngVpReady (Mode.mk true tL t) (sE.eval ρ)) := by
  unfold vSendC; rw [eval_bind_ret, eval_bind]
  have h1 := pb_vSendStep1C_potOKS (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B Δbucket qep tL par t
    (.fst (Expr.v0 (O := OOpb))) (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))
    (.fst (.snd (.snd (.snd .v0)))) (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))
    (.cons (hE.eval ρ, ctxE.eval ρ, pE.eval ρ, sE.eval ρ, mE.eval ρ, pairE.eval ρ, rE.eval ρ) ρ)
    m m_other
  simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at h1
  refine PotOKSPrng.bindPot h1 (fun _ => ?_)
  refine potSPrng_caseOpt (fun hNone => ?_) (fun _ hSome => ?_)
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hNone
    exact potSPrng_ret (by simp [pbVSendPost, pbVpOptPost, hNone, Expr.eval])
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSome
    refine potSPrng_caseOpt
      (fun _ => potSPrng_ret (by simp [pbVSendPost, pbVpOptPost, hSome, Expr.eval, Expr.v0]))
      (fun _ _ => ?_)
    dsimp only [hooksPRNGBucketParPaperC, prngBucketFsSendC]; rw [eval_bind, eval_ret, pure_bind]
    exact potSPrng_caseOpt (fun hFNone => by simp [Expr.eval, Expr.v0] at hFNone)
      (fun _ _ => potSPrng_ret (by
        simp [pbVSendPost, pbVpOptPost, hSome, prngVpReady, vpSetVS, vpMk, vpId, vpTcurNat,
          letE_eval, Expr.eval, Expr.v0, Expr.v3]))

private theorem prngBucketStartRecvSplitC_potOKS (L Δbucket qep : ℕ) (tL : Option ℕ)
    (par gMain : Bool) (t : ℕ) {Γ' : List (Ty Spb)}
    (hE : Expr OOpb Γ' pbHsTyPb) (ctxE : Expr OOpb Γ' (cGsTy pbVpTyPb))
    (pE : Expr OOpb Γ' .bool) (tE : Expr OOpb Γ' .nat) (γE : Expr OOpb Γ' (.base .γ))
    (σvE : Expr OOpb Γ' (.opt (.base .sig))) (tnE : Expr OOpb Γ' (.base .t))
    (ρ : Env Γ') (r : ℕ) :
    PotOKSPrng P_prng (fun _ => r)
      ((prngBucketStartRecvSplitC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L Δbucket qep tL par gMain t hE ctxE pE tE γE σvE tnE).eval ρ)
      ((if decide (tE.eval ρ = t) then 1 else 0) + r) := by
  cases gMain
  · exact prngBucketStartRecvC_potOKS L Δbucket qep tL par t hE ctxE pE tE γE σvE tnE ρ r
  · exact potSPrng_comp_const _ _ r _ (fun _ => Nat.le_refl r)
      (by simp [prngBucketStartRecvSplitC, prngBucketStartRecvMainC_queries])

private def pbVRecvStep1Post (mo : Mode) (m m_other : ℕ) (s0 : (Ty.denote pbVpTyPb))
    (res : (Ty.prod (.opt (.opt pbVpTyPb)) pbHsTyPb : Ty Spb).denote) : ℕ :=
  match res.1 with
  | none => m
  | some none => m + m_other + prngVpReady mo s0
  | some (some s1) => m + m_other + max (prngVpReady mo s0) (prngVpReady mo s1)

private theorem pb_vRecvStep1C_potOKS (L B Δbucket qep : ℕ) (tL : Option ℕ) (par gMain : Bool) (t : ℕ)
    {Γ' : List (Ty Spb)} (hE : Expr OOpb Γ' pbHsTyPb) (ctxE : Expr OOpb Γ' (cGsTy pbVpTyPb))
    (pE : Expr OOpb Γ' .bool) (sE : Expr OOpb Γ' pbVpTyPb) (cE : Expr OOpb Γ' hdrCtTyPb)
    (ρ : Env Γ') (m m_other : ℕ)
    (hNotSends : (partyDec (sE.eval ρ).1).sendsIn (cE.eval ρ).1.1 = false) :
    PotOKSPrng P_prng (pbVRecvStep1Post (Mode.mk true tL t) m m_other (sE.eval ρ))
      ((vRecvStep1C (hooksPRNGBucketSplitPaperC (sampKR := sampKR) (sampKC := sampKC)
          (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B Δbucket qep tL par gMain t)
        hE ctxE pE sE cE).eval ρ)
      (1 + m + m_other + prngVpReady (Mode.mk true tL t) (sE.eval ρ)) := by
  unfold vRecvStep1C; rw [eval_bind_ret]
  refine potSPrng_ite (fun ht => ?_)
    (fun _ => potSPrng_ret (by simp [pbVRecvStep1Post, Expr.eval, Expr.v0]))
  have ht' : (cE.eval ρ).1.1 = (sE.eval ρ).2.2.2.2.2.2 + 1 := of_decide_eq_true ht
  have hReady0 : prngVpReady (Mode.mk true tL t) (sE.eval ρ) = 0 := by
    rw [ht'] at hNotSends; simp [prngVpReady, prngReady, hNotSends]
  refine potSPrng_caseOpt (fun _ => potSPrng_ret (by simp [pbVRecvStep1Post, Expr.eval]))
    (fun Tn _ => ?_)
  dsimp only [hooksPRNGBucketSplitPaperC]; rw [eval_bind]
  have hSR := prngBucketStartRecvSplitC_potOKS (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L Δbucket qep tL par gMain t
    (.fst (Expr.v1 (O := OOpb))) (.fst (.snd .v1)) (.fst (.snd (.snd .v1)))
    (.fst (.fst (.snd (.snd (.snd (.snd .v1))))))
    (vpΓ (.fst (.snd (.snd (.snd .v1))))) (vpRoot (.fst (.snd (.snd (.snd .v1))))) .v0
    (.cons Tn (.cons (hE.eval ρ, ctxE.eval ρ, pE.eval ρ, sE.eval ρ, cE.eval ρ) ρ))
    (m + m_other + prngReady (Mode.mk true tL t) (partyDec (sE.eval ρ).1) ((sE.eval ρ).2.2.2.2.2.2 + 1))
  simp only [Expr.eval, Expr.v1, Env.get_cons_zero, Env.get_cons_succ, ht'] at hSR
  have hBud :
      (if decide ((sE.eval ρ).2.2.2.2.2.2 + 1 = t) then 1 else 0) +
        (m + m_other + prngReady (Mode.mk true tL t) (partyDec (sE.eval ρ).1) ((sE.eval ρ).2.2.2.2.2.2 + 1)) ≤
        1 + m + m_other + prngVpReady (Mode.mk true tL t) (sE.eval ρ) := by
    by_cases hEq : ((sE.eval ρ).2.2.2.2.2.2 : ℕ) + 1 = t
    · rw [hReady0, hEq]; simp [prngReady, Nat.add_assoc]
    · rw [hReady0]
      simp only [hEq, decide_false, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      have hLe1 := prngReady_le_one (Mode.mk true tL t) (partyDec (sE.eval ρ).1) ((sE.eval ρ).2.2.2.2.2.2 + 1)
      omega
  refine ⟨fun {_} k hk' => (PotOKSPrng.bindPot hSR (fun _ => ?_)).run k hk' |>.mono hBud⟩
  refine potSPrng_caseOpt (fun _ => potSPrng_ret (by simp [pbVRecvStep1Post, Expr.eval]; omega))
    (fun _ _ => potSPrng_caseOpt
      (fun _ => potSPrng_ret (by simp [pbVRecvStep1Post, hReady0, Expr.eval]))
      (fun _ _ => potSPrng_ret (by
        rw [pbVRecvStep1Post, hReady0]
        simp [prngVpReady, vpMk, vpId, ht', Expr.eval, Expr.v0, Expr.v4])))

private def pbVRecvPost (mo : Mode) (m m_other : ℕ) (s0 : (Ty.denote pbVpTyPb))
    (res : (Ty.prod (.opt (.opt (.prod pbVpTyPb (.prod .nat (.prod .nat (.base .msg))))))
      pbHsTyPb : Ty Spb).denote) : ℕ :=
  match res.1 with
  | none => m
  | some none => m + m_other + prngVpReady mo s0
  | some (some (st', _, _, _)) => m + m_other + max (prngVpReady mo s0) (prngVpReady mo st')

private theorem pb_vRecvC_potOKS (L B Δbucket qep : ℕ) (tL : Option ℕ) (par gMain : Bool) (t : ℕ)
    {Γ' : List (Ty Spb)} (hE : Expr OOpb Γ' pbHsTyPb) (ctxE : Expr OOpb Γ' (cGsTy pbVpTyPb))
    (pE : Expr OOpb Γ' .bool) (sE : Expr OOpb Γ' pbVpTyPb) (cE : Expr OOpb Γ' hdrCtTyPb)
    (recE : Expr OOpb Γ' (.opt cRecTy)) (ρ : Env Γ') (m m_other : ℕ) :
    PotOKSPrng P_prng (pbVRecvPost (Mode.mk true tL t) m m_other (sE.eval ρ))
      ((vRecvC (hooksPRNGBucketSplitPaperC (sampKR := sampKR) (sampKC := sampKC)
          (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B Δbucket qep tL par gMain t)
        hE ctxE pE sE cE recE).eval ρ)
      (1 + m + m_other + prngVpReady (Mode.mk true tL t) (sE.eval ρ)) := by
  unfold vRecvC; rw [eval_bind_ret]
  refine potSPrng_ite (fun _ => potSPrng_ret (by simp [pbVRecvPost, Expr.eval])) (fun hGuard => ?_)
  have hNotSends : (partyDec (sE.eval ρ).1).sendsIn (cE.eval ρ).1.1 = false := by
    simp only [orE_eval, Bool.or_eq_false_iff] at hGuard
    have h1 := hGuard.1
    rw [sendsInE_eval _ _ _ (partyDec (sE.eval ρ).1) (by simp [vpId, Expr.eval, Expr.v0])] at h1
    simpa [Expr.eval, Expr.v0] using h1
  rw [eval_bind]
  have hStep1 := pb_vRecvStep1C_potOKS (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B Δbucket qep tL par gMain t
    (.fst (Expr.v0 (O := OOpb))) (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))
    (.fst (.snd (.snd (.snd .v0)))) (.fst (.snd (.snd (.snd (.snd .v0)))))
    (.cons (hE.eval ρ, ctxE.eval ρ, pE.eval ρ, sE.eval ρ, cE.eval ρ, recE.eval ρ) ρ)
    m m_other (by simpa [Expr.eval, Expr.v0, Env.get_cons_zero] using hNotSends)
  simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hStep1
  refine PotOKSPrng.bindPot hStep1 (fun _ => ?_)
  refine potSPrng_caseOpt (fun hNone => ?_) (fun _ hSome => ?_)
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hNone
    exact potSPrng_ret (by simp [pbVRecvPost, pbVRecvStep1Post, hNone, Expr.eval])
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSome
    refine potSPrng_caseOpt (fun hInNone => ?_) (fun _ hInSome => ?_)
    · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hInNone
      exact potSPrng_ret (by simp [pbVRecvPost, pbVRecvStep1Post, hSome, hInNone, Expr.eval])
    · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hInSome
      refine potSPrng_caseOpt
        (fun _ => potSPrng_ret (by simp [pbVRecvPost, pbVRecvStep1Post, hSome, hInSome, Expr.eval]))
        (fun _ _ => ?_)
      dsimp only [hooksPRNGBucketSplitPaperC, prngBucketFsRecvC]; rw [eval_bind, eval_ret, pure_bind]
      exact potSPrng_caseOpt (fun hFNone => by simp [Expr.eval, Expr.v0] at hFNone)
        (fun _ _ => potSPrng_caseOpt
          (fun _ => potSPrng_ret (by
            simp [pbVRecvPost, pbVRecvStep1Post, hSome, hInSome, Expr.eval]))
          (fun _ _ => potSPrng_ret (by
            simp [pbVRecvPost, pbVRecvStep1Post, hSome, hInSome, prngVpReady,
              vpSetVR, vpMk, vpId, vpTcurNat, letE_eval, Expr.eval, Expr.v0, Expr.v4])))

private def pbCommitECPost (mo : Mode) (m : ℕ)
    (res : (Ty.prod (.opt (cGsTy pbVpTyPb)) pbEsTyPb : Ty Spb).denote) : ℕ :=
  match res.1 with
  | none => m + pbPot mo res.2
  | some s_acc => m + pbPot mo (s_acc, res.2.2.1, res.2.2.2)

private theorem pb_commitEC_potOKS (L B Δbucket qep : ℕ) (tL : Option ℕ) (par gMain : Bool) (t : ℕ)
    {Γ' : List (Ty Spb)} (esE : Expr OOpb Γ' pbEsTyPb)
    (sE : Expr OOpb Γ' (cGsTy pbVpTyPb)) (pE : Expr OOpb Γ' .bool)
    (oldE newE : Expr OOpb Γ' pbVpTyPb) (posE : Expr OOpb Γ' posTy)
    (ρ : Env Γ') (m : ℕ) (hNoAbort : (esE.eval ρ).2.2 = false) :
    PotOKSPrng P_prng (pbCommitECPost (Mode.mk true tL t) m)
      ((commitEC (hooksPRNGBucketSplitPaperC (sampKR := sampKR) (sampKC := sampKC)
          (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B Δbucket qep tL par gMain t)
        L esE sE pE oldE newE posE).eval ρ)
      (m + prngOtherPot (Mode.mk true tL t) (sE.eval ρ).1 (pE.eval ρ) + prngVpReady (Mode.mk true tL t) (newE.eval ρ)) := by
  unfold commitEC; rw [eval_bind_ret]
  dsimp only [hooksPRNGBucketSplitPaperC, prngBucketCommitC]; rw [eval_bind, eval_ret, pure_bind]
  refine potSPrng_caseOpt (fun hCNone => by simp [Expr.eval, Expr.v0] at hCNone) (fun _ hCSome => ?_)
  simp only [Expr.eval, Expr.v0, Env.get_cons_zero, Option.some.injEq] at hCSome
  subst hCSome; refine potSPrng_ret ?_
  simp only [pbCommitECPost, pbPot, esMk, esAbort, cGsSetStP_st_prng, cAcceptE_st_prng,
    Expr.eval, Expr.v0, Expr.v2, Env.get_cons_zero, Env.get_cons_succ, hNoAbort,
    Bool.false_eq_true, ↓reduceIte]
  cases (pE.eval ρ : Bool) <;> (simp only [prngOtherPot, ↓reduceIte, Bool.false_eq_true]; omega)

private theorem pb_deliverEC_potOKS (L B Δbucket qep maxSkip : ℕ) (tL : Option ℕ) (par gMain : Bool)
    (t : ℕ) (cfg : ConfigEC OOpb)
    {Γ' : List (Ty Spb)} (esE : Expr OOpb Γ' pbEsTyPb) (argE : Expr OOpb Γ' (.prod .bool hdrCtTyPb))
    (ρ : Env Γ') (m : ℕ) :
    PotOKSPrng P_prng (fun x => m + pbPot (Mode.mk true tL t) x.2)
      ((deliverEC (hooksPRNGBucketSplitPaperC (sampKR := sampKR) (sampKC := sampKC)
          (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B Δbucket qep tL par gMain t)
        L maxSkip cfg esE argE).eval ρ)
      (1 + m + pbPot (Mode.mk true tL t) (esE.eval ρ)) := by
  unfold deliverEC; rw [eval_bind_ret]
  refine potSPrng_ite (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0])) (fun hNotAbWin => ?_)
  have hab : (esE.eval ρ).2.2 = false := by
    simp [orE_eval, esAbort, Expr.eval, Expr.v0] at hNotAbWin; exact hNotAbWin.1
  refine potSPrng_caseOpt (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0])) (fun r1 _ => ?_)
  rw [eval_bind]
  set m_other := prngOtherPot (Mode.mk true tL t) (esE.eval ρ).1.1 (argE.eval ρ).1
  have hRecv := pb_vRecvC_potOKS (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B Δbucket qep tL par gMain t
    (esH (.fst (Expr.v1 (O := OOpb)))) (esG (.fst .v1))
    (.fst (.snd .v1)) (pGet (cGsSt (esG (.fst .v1))) (.fst (.snd .v1))) (.snd (.snd .v1)) (.some .v0)
    (.cons r1 (.cons (esE.eval ρ, argE.eval ρ) ρ)) m m_other
  simp only [pGet_eval_st_prng, cGsSt, esG, Expr.eval, Expr.v0, Expr.v1,
    Env.get_cons_zero, Env.get_cons_succ] at hRecv
  change PotOKSPrng P_prng
    (pbVRecvPost (Mode.mk true tL t) m m_other
      (if ((argE.eval ρ).1 : Bool) then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1)) _ _ at hRecv
  have hSum : m_other +
      prngVpReady (Mode.mk true tL t) (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) =
      pbPot (Mode.mk true tL t) (esE.eval ρ) := by
    rw [prngOtherPot_add_pGet]; simp [pbPot, hab]
  rw [show 1 + m + pbPot (Mode.mk true tL t) (esE.eval ρ) =
      1 + m + m_other +
        prngVpReady (Mode.mk true tL t) (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) by omega]
  refine PotOKSPrng.bindPot hRecv (fun recvOut => ?_)
  refine potSPrng_caseOpt (fun hNone => ?_) (fun resInner hSome => ?_)
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hNone
    exact potSPrng_ret (by simp [pbVRecvPost, hNone, pbPot, esMk, Expr.eval])
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSome
    refine potSPrng_caseOpt (fun hInNone => ?_) (fun tup hInSome => ?_)
    · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hInNone
      refine potSPrng_ret ?_
      simp only [pbVRecvPost, hSome, hInNone, esMk, esAbort, esG,
        Expr.eval, Expr.v1, Expr.v2, Expr.v3, Env.get_cons_zero, Env.get_cons_succ, hab]
      refine Nat.le_trans
        (Nat.add_le_add_left (Nat.le_of_eq
          (pbPot_mk_eq (Mode.mk true tL t) (g2 := (esE.eval ρ).1) (h2 := (esE.eval ρ).2.1)
            (ite_fst_eq_prng (by rw [cGsSetWin_st_prng]; rfl) rfl))) m) ?_
      simp only [pbPot, Bool.false_eq_true, ↓reduceIte]
      have hEqSum : prngVpReady (Mode.mk true tL t) (esE.eval ρ).1.1.1 + prngVpReady (Mode.mk true tL t) (esE.eval ρ).1.1.2 =
          m_other + prngVpReady (Mode.mk true tL t)
            (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) := by
        simpa [pbPot, hab] using hSum.symm
      omega
    · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hInSome
      rw [eval_bind]
      have hCom := pb_commitEC_potOKS (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B Δbucket qep tL par gMain t
        (esSetH (.fst (Expr.v4 (O := OOpb))) (.snd .v2))
        (esG (.fst .v4)) (.fst (.snd .v4)) (pGet (cGsSt (esG (.fst .v4))) (.fst (.snd .v4)))
        (.fst .v0) (cRecPos .v3)
        (.cons tup (.cons resInner (.cons recvOut (.cons r1 (.cons (esE.eval ρ, argE.eval ρ) ρ))))) m
        (by simp [esSetH, letE_eval, esMk, esAbort, Expr.eval, Expr.v0, Expr.v4, hab])
      simp only [esG, Expr.eval, Expr.v0, Expr.v4, Env.get_cons_zero, Env.get_cons_succ] at hCom
      have hPre :
          m + prngOtherPot (Mode.mk true tL t) (esE.eval ρ).1.1 (argE.eval ρ).1 + prngVpReady (Mode.mk true tL t) tup.1 ≤
            pbVRecvPost (Mode.mk true tL t) m m_other
              (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) recvOut := by
        simp [pbVRecvPost, hSome, hInSome, m_other]
      refine ⟨fun {_} k hk' => (PotOKSPrng.bindPot hCom (fun comOut => ?_)).run k hk' |>.mono hPre⟩
      refine potSPrng_caseOpt (fun hCNone => ?_) (fun s_acc hCSome => ?_)
      · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hCNone
        exact potSPrng_ret (by simp [pbCommitECPost, hCNone, Expr.eval, Expr.v0])
      · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hCSome
        refine potSPrng_ret ?_
        simp only [pbCommitECPost, hCSome, esSetG, letE_eval, esMk, esAbort,
          Expr.eval, Expr.v0, Expr.v1, Expr.v5, Expr.v6, Env.get_cons_zero, Env.get_cons_succ]
        exact Nat.add_le_add_left (Nat.le_of_eq
          (pbPot_mk_eq (Mode.mk true tL t) (g2 := s_acc) (h2 := comOut.2.2.1)
            (ite_fst_eq_prng (by rw [cGsSetWin_st_prng]; rfl) rfl))) m

private theorem pb_injectEC_potOKS (L B Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par gMain : Bool)
    (t : ℕ) (cfg : ConfigEC OOpb)
    {Γ' : List (Ty Spb)} (esE : Expr OOpb Γ' pbEsTyPb) (argE : Expr OOpb Γ' (.prod .bool hdrCtTyPb))
    (ρ : Env Γ') (m : ℕ) :
    PotOKSPrng P_prng (fun x => m + pbPot (Mode.mk true tL t) x.2)
      ((injectEC (hooksPRNGBucketSplitPaperC (sampKR := sampKR) (sampKC := sampKC)
          (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B Δbucket qep tL par gMain t)
        L (2 + Δcka) qep cfg esE argE).eval ρ)
      (1 + m + pbPot (Mode.mk true tL t) (esE.eval ρ)) := by
  unfold injectEC; rw [eval_bind_ret]
  refine potSPrng_ite (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0])) (fun hNotRef => ?_)
  have hab : (esE.eval ρ).2.2 = false := by
    simp [orE_eval, esAbort, Expr.eval, Expr.v0] at hNotRef; exact hNotRef.1
  rw [eval_bind]
  set m_other := prngOtherPot (Mode.mk true tL t) (esE.eval ρ).1.1 (argE.eval ρ).1
  have hRecv := pb_vRecvC_potOKS (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B Δbucket qep tL par gMain t
    (esH (.fst (Expr.v0 (O := OOpb)))) (esG (.fst .v0))
    (.fst (.snd .v0)) (pGet (cGsSt (esG (.fst .v0))) (.fst (.snd .v0))) (.snd (.snd .v0)) .none
    (.cons (esE.eval ρ, argE.eval ρ) ρ) m m_other
  simp only [pGet_eval_st_prng, cGsSt, esG, Expr.eval, Expr.v0, Env.get_cons_zero] at hRecv
  change PotOKSPrng P_prng
    (pbVRecvPost (Mode.mk true tL t) m m_other
      (if ((argE.eval ρ).1 : Bool) then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1)) _ _ at hRecv
  have hSum : m_other +
      prngVpReady (Mode.mk true tL t) (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) =
      pbPot (Mode.mk true tL t) (esE.eval ρ) := by
    rw [prngOtherPot_add_pGet]; simp [pbPot, hab]
  rw [show 1 + m + pbPot (Mode.mk true tL t) (esE.eval ρ) =
      1 + m + m_other +
        prngVpReady (Mode.mk true tL t) (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) by omega]
  refine PotOKSPrng.bindPot hRecv (fun recvOut => ?_)
  refine potSPrng_caseOpt (fun hNone => ?_) (fun resInner hSome => ?_)
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hNone
    exact potSPrng_ret (by simp [pbVRecvPost, hNone, pbPot, esMk, Expr.eval])
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSome
    refine potSPrng_caseOpt (fun hInNone => ?_) (fun tup hInSome => ?_)
    · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hInNone
      refine potSPrng_ret ?_
      simp only [pbVRecvPost, hSome, hInNone, pbPot, esSetH, letE_eval, esMk, esAbort, esG,
        Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get_cons_zero, Env.get_cons_succ, hab,
        Bool.false_eq_true, ↓reduceIte]
      have hEqSum : prngVpReady (Mode.mk true tL t) (esE.eval ρ).1.1.1 + prngVpReady (Mode.mk true tL t) (esE.eval ρ).1.1.2 =
          m_other + prngVpReady (Mode.mk true tL t)
            (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) := by
        simpa [pbPot, hab] using hSum.symm
      omega
    · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hInSome
      refine potSPrng_ite (fun _ => ?_) (fun _ => ?_)
      · refine potSPrng_ret ?_
        simp only [pbVRecvPost, hSome, hInSome, pbPot, esSetH, letE_eval, esMk, esAbort, esG,
          Expr.eval, Expr.v0, Expr.v2, Expr.v3, Env.get_cons_zero, Env.get_cons_succ, hab,
          Bool.false_eq_true, ↓reduceIte]
        have hEqSum : prngVpReady (Mode.mk true tL t) (esE.eval ρ).1.1.1 + prngVpReady (Mode.mk true tL t) (esE.eval ρ).1.1.2 =
            m_other + prngVpReady (Mode.mk true tL t)
              (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) := by
          simpa [pbPot, hab] using hSum.symm
        omega
      · refine potSPrng_ite (fun _ => ?_) (fun _ => ?_)
        · rw [eval_bind]
          have hCom := pb_commitEC_potOKS (sampKR := sampKR) (sampKC := sampKC)
            (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B Δbucket qep tL par gMain t
            (esSetH (.fst (Expr.v3 (O := OOpb))) (.snd .v2))
            (esG (.fst .v3)) (.fst (.snd .v3)) (pGet (cGsSt (esG (.fst .v3))) (.fst (.snd .v3)))
            (.fst .v0) (.pair (otherE (.fst (.snd .v3)))
              (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
            (.cons tup (.cons resInner (.cons recvOut (.cons (esE.eval ρ, argE.eval ρ) ρ)))) m
            (by simp [esSetH, letE_eval, esMk, esAbort, Expr.eval, Expr.v0, Expr.v3, hab])
          simp only [esG, Expr.eval, Expr.v0, Expr.v3, Env.get_cons_zero, Env.get_cons_succ] at hCom
          have hPre :
              m + prngOtherPot (Mode.mk true tL t) (esE.eval ρ).1.1 (argE.eval ρ).1 + prngVpReady (Mode.mk true tL t) tup.1 ≤
                pbVRecvPost (Mode.mk true tL t) m m_other
                  (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) recvOut := by
            simp [pbVRecvPost, hSome, hInSome, m_other]
          refine ⟨fun {_} k hk' => (PotOKSPrng.bindPot hCom (fun comOut => ?_)).run k hk' |>.mono hPre⟩
          refine potSPrng_caseOpt (fun hCNone => ?_) (fun _ hCSome => ?_)
          · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hCNone
            exact potSPrng_ret (by simp [pbCommitECPost, hCNone, Expr.eval, Expr.v0])
          · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hCSome
            exact potSPrng_ret (by
              simp [pbCommitECPost, hCSome, pbPot, esSetG, letE_eval, esMk, esH, esAbort,
                Expr.eval, Expr.v0, Expr.v1])
        · refine potSPrng_ret ?_
          simp only [pbVRecvPost, hSome, hInSome, esSetG, esSetH, letE_eval, esMk, esAbort, esG,
            Expr.eval, Expr.v0, Expr.v2, Expr.v3, Env.get_cons_zero, Env.get_cons_succ, hab]
          refine Nat.le_trans
            (Nat.add_le_add_left (Nat.le_of_eq
              (pbPot_mk_eq (Mode.mk true tL t) (g2 := (esE.eval ρ).1) (h2 := (esE.eval ρ).2.1)
                (ite_fst_eq_prng (by rw [cGsSetWin_st_prng]; rfl) rfl))) m) ?_
          simp only [pbPot, Bool.false_eq_true, ↓reduceIte]
          have hEqSum : prngVpReady (Mode.mk true tL t) (esE.eval ρ).1.1.1 + prngVpReady (Mode.mk true tL t) (esE.eval ρ).1.1.2 =
              m_other + prngVpReady (Mode.mk true tL t)
                (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) := by
            simpa [pbPot, hab] using hSum.symm
          omega

private theorem pb_deliverForgeEC_potOKS (L B Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par gMain : Bool)
    (t : ℕ) (cfg : ConfigEC OOpb)
    {Γ' : List (Ty Spb)} (esE : Expr OOpb Γ' pbEsTyPb)
    (argE : Expr OOpb Γ' (.prod .bool (.prod hdrCtTyPb hdrCtTyPb)))
    (ρ : Env Γ') (m : ℕ) :
    PotOKSPrng P_prng (fun x => m + pbPot (Mode.mk true tL t) x.2)
      ((deliverForgeEC (hooksPRNGBucketSplitPaperC (sampKR := sampKR) (sampKC := sampKC)
          (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B Δbucket qep tL par gMain t)
        L (2 + Δcka) qep cfg esE argE).eval ρ)
      (1 + m + pbPot (Mode.mk true tL t) (esE.eval ρ)) := by
  unfold deliverForgeEC; rw [eval_bind_ret]
  refine potSPrng_ite (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0])) (fun hNotRef => ?_)
  have hab : (esE.eval ρ).2.2 = false := by
    simp only [orE, esAbort, Expr.eval, Expr.v0, Env.get_cons_zero] at hNotRef
    cases h : (esE.eval ρ).2.2 <;> simp_all
  refine potSPrng_caseOpt (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0])) (fun r1 _ => ?_)
  refine potSPrng_ite (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v1])) (fun _ => ?_)
  rw [eval_bind]
  set m_other := prngOtherPot (Mode.mk true tL t) (esE.eval ρ).1.1 (argE.eval ρ).1
  have hRecv := pb_vRecvC_potOKS (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B Δbucket qep tL par gMain t
    (esH (.fst (Expr.v1 (O := OOpb)))) (esG (.fst .v1))
    (.fst (.snd .v1)) (pGet (cGsSt (esG (.fst .v1))) (.fst (.snd .v1))) (.snd (.snd (.snd .v1))) .none
    (.cons r1 (.cons (esE.eval ρ, argE.eval ρ) ρ)) m m_other
  simp only [pGet_eval_st_prng, cGsSt, esG, Expr.eval, Expr.v1,
    Env.get_cons_zero, Env.get_cons_succ] at hRecv
  change PotOKSPrng P_prng
    (pbVRecvPost (Mode.mk true tL t) m m_other
      (if ((argE.eval ρ).1 : Bool) then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1)) _ _ at hRecv
  have hSum : m_other +
      prngVpReady (Mode.mk true tL t) (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) =
      pbPot (Mode.mk true tL t) (esE.eval ρ) := by
    rw [prngOtherPot_add_pGet]; simp [pbPot, hab]
  rw [show 1 + m + pbPot (Mode.mk true tL t) (esE.eval ρ) =
      1 + m + m_other +
        prngVpReady (Mode.mk true tL t) (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) by omega]
  refine PotOKSPrng.bindPot hRecv (fun recvOut => ?_)
  refine potSPrng_caseOpt (fun hNone => ?_) (fun resInner hSome => ?_)
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hNone
    exact potSPrng_ret (by simp [pbVRecvPost, hNone, pbPot, esMk, Expr.eval])
  · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSome
    refine potSPrng_caseOpt (fun hInNone => ?_) (fun tup hInSome => ?_)
    · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hInNone
      refine potSPrng_ret ?_
      simp only [pbVRecvPost, hSome, hInNone, pbPot, esSetH, letE_eval, esMk, esAbort, esG,
        Expr.eval, Expr.v0, Expr.v1, Expr.v3, Env.get_cons_zero, Env.get_cons_succ, hab,
        Bool.false_eq_true, ↓reduceIte]
      have hEqSum : prngVpReady (Mode.mk true tL t) (esE.eval ρ).1.1.1 + prngVpReady (Mode.mk true tL t) (esE.eval ρ).1.1.2 =
          m_other + prngVpReady (Mode.mk true tL t)
            (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) := by
        simpa [pbPot, hab] using hSum.symm
      omega
    · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hInSome
      refine potSPrng_ite (fun _ => ?_) (fun _ => ?_)
      · refine potSPrng_ret ?_
        simp only [pbVRecvPost, hSome, hInSome, pbPot, esSetH, letE_eval, esMk, esAbort, esG,
          Expr.eval, Expr.v0, Expr.v2, Expr.v4, Env.get_cons_zero, Env.get_cons_succ, hab,
          Bool.false_eq_true, ↓reduceIte]
        have hEqSum : prngVpReady (Mode.mk true tL t) (esE.eval ρ).1.1.1 + prngVpReady (Mode.mk true tL t) (esE.eval ρ).1.1.2 =
            m_other + prngVpReady (Mode.mk true tL t)
              (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) := by
          simpa [pbPot, hab] using hSum.symm
        omega
      · refine potSPrng_ite (fun _ => ?_) (fun _ => ?_)
        · rw [eval_bind]
          have hCom := pb_commitEC_potOKS (sampKR := sampKR) (sampKC := sampKC)
            (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B Δbucket qep tL par gMain t
            (esSetH (.fst (Expr.v4 (O := OOpb))) (.snd .v2))
            (esG (.fst .v4)) (.fst (.snd .v4))
            (pGet (cGsSt (esG (.fst .v4))) (.fst (.snd .v4)))
            (.fst .v0) (.pair (otherE (.fst (.snd .v4)))
              (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
            (.cons tup (.cons resInner (.cons recvOut
              (.cons r1 (.cons (esE.eval ρ, argE.eval ρ) ρ))))) m
            (by simp [esSetH, letE_eval, esMk, esAbort, Expr.eval, Expr.v0, Expr.v4, hab])
          simp only [esG, Expr.eval, Expr.v0, Expr.v4, Env.get_cons_zero, Env.get_cons_succ] at hCom
          have hPre :
              m + prngOtherPot (Mode.mk true tL t) (esE.eval ρ).1.1 (argE.eval ρ).1 + prngVpReady (Mode.mk true tL t) tup.1 ≤
                pbVRecvPost (Mode.mk true tL t) m m_other
                  (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) recvOut := by
            simp [pbVRecvPost, hSome, hInSome, m_other]
          refine ⟨fun {_} k hk' => (PotOKSPrng.bindPot hCom (fun comOut => ?_)).run k hk' |>.mono hPre⟩
          refine potSPrng_caseOpt (fun hCNone => ?_) (fun _ hCSome => ?_)
          · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hCNone
            exact potSPrng_ret (by simp [pbCommitECPost, hCNone, Expr.eval, Expr.v0])
          · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hCSome
            exact potSPrng_ret (by
              simp [pbCommitECPost, hCSome, pbPot, esSetG, letE_eval, esMk, esH, esAbort,
                Expr.eval, Expr.v0, Expr.v1])
        · refine potSPrng_ret ?_
          simp only [pbVRecvPost, hSome, hInSome, esSetG, esSetH, letE_eval, esMk, esAbort, esG,
            Expr.eval, Expr.v0, Expr.v2, Expr.v4, Env.get_cons_zero, Env.get_cons_succ, hab]
          refine Nat.le_trans
            (Nat.add_le_add_left (Nat.le_of_eq
              (pbPot_mk_eq (Mode.mk true tL t) (g2 := (esE.eval ρ).1) (h2 := (esE.eval ρ).2.1)
                (ite_fst_eq_prng (by rw [cGsSetWin_st_prng]; rfl) rfl))) m) ?_
          simp only [pbPot, Bool.false_eq_true, ↓reduceIte]
          have hEqSum : prngVpReady (Mode.mk true tL t) (esE.eval ρ).1.1.1 + prngVpReady (Mode.mk true tL t) (esE.eval ρ).1.1.2 =
              m_other + prngVpReady (Mode.mk true tL t)
                (if (argE.eval ρ).1 then (esE.eval ρ).1.1.2 else (esE.eval ρ).1.1.1) := by
            simpa [pbPot, hab] using hSum.symm
          omega

private theorem initPRNGBucketHybridEStateC_potOKS (L Δbucket : ℕ) (tL : Option ℕ) (par : Bool)
    (t : ℕ) {Γ' : List (Ty Spb)} (bE : Expr OOpb Γ' .bool) (ρ : Env Γ') (m : ℕ) :
    PotOKSPrng P_prng (fun es => m + pbPot (Mode.mk true tL t) es)
      ((initPRNGBucketHybridEStateC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L Δbucket tL par t bE).eval ρ) (m + 3) := by
  unfold initPRNGBucketHybridEStateC; rw [eval_bind_ret, eval_bind]
  refine PotOKSPrng.bindPot
    (potSPrng_comp_const _ _ (m + 3) (m + 3) (fun _ => Nat.le_refl _) (by simp [Comp.queries]))
    (fun _ => ?_)
  rw [eval_bind]
  refine PotOKSPrng.bindPot
    (potSPrng_comp_const _ _ (m + 1) (m + 3) (fun _ => Nat.le_refl _)
      (by simp [rootPRNGBucketHybridC_queries]; omega)) (fun _ => ?_)
  refine potSPrng_caseOpt (fun _ => potSPrng_ret (by simp [pbPot, esMk, Expr.eval])) (fun _ _ => ?_)
  refine potSPrng_ret ?_
  simp only [pbPot, esMk, cGsInitE, cGsMk, mkPartiesE, vpMk, Expr.eval,
    Bool.false_eq_true, ↓reduceIte]
  have hB : prngReady (Mode.mk true tL t) Party.B 0 = 0 := by simp [prngReady, Party.sendsIn]
  simp only [prngVpReady, partyDec_partyEnc, hB, Nat.add_zero]
  exact Nat.add_le_add_left (prngReady_le_one (Mode.mk true tL t) _ _) m

private theorem pb_handle_potOKS_aux (L B Δcka Δbucket qep maxSkip : ℕ) (tL : Option ℕ)
    (par : Bool) (t : ℕ) (corrGuard : ∀ {Γ'}, Expr OOpb Γ' (cGsTy pbVpTyPb) → Expr OOpb Γ' .bool → Expr OOpb Γ' .bool)
    (m : ℕ)
    (qv : (prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).Q.denote)
    (sv : (Ty.denote pbRedEsTyPb)) :
    let hComp : Comp OOpb IIpb [pbRedEsTyPb, (prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).Q]
        (.prod (prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).R pbRedEsTyPb) :=
      rdsl [st, q] do
        (es0, winEp0, q0) ← return (st.1, st.2, q)
        match q0 with
        | .inl qBase =>
          match qBase with
          | .inl (.inl (.inl (.inl x))) =>
            (p0, m0, r0) ← return x
            if orE (esAbort es0) (cGsWin (esG es0)) then
              return (.inl (inl (inl (inl (inl none)))), (es0, winEp0))
            else
              match cEpMgmtE (raw (2 + Δcka)) (raw qep) (esG es0) p0 (isSomeE r0) with
              | none => return (.inl (inl (inl (inl (inl none)))), (es0, winEp0))
              | some s1 =>
                (res, h') ← vSendC (raw (hooksPRNGBucketParPaperC L B Δbucket qep tL par t))
                  (esH es0) s1 p0 (pGet (cGsSt s1) p0) m0 none r0
                match res with
                | none =>
                  return (.inl (inl (inl (inl (inl none)))),
                    (esMk (esG es0) h' true, winEp0))
                | some (st', ct) =>
                  let recE := ((p0, pGet (cGsEpoch s1) p0, pGet (cGsIdx s1) p0 + 1), m0, ct)
                  let g' := cRecordE (raw L) (raw (2 + Δcka)) s1 p0 st' recE false
                  return (.inl (inl (inl (inl (inl (some ct))))),
                    (esMk g' h' (esAbort es0), winEp0))
          | .inl (.inl (.inl (.inr _))) =>
            return (.inl (inl (inl (inl (inr none)))), (es0, winEp0))
          | .inl (.inl (.inr x)) =>
            (out, es') ← deliverEC (raw (hooksPRNGBucketParPaperC L B Δbucket qep tL par t))
              L maxSkip (raw (bucketParPaperAuthCfgEC Δbucket tL par)) es0 x
            return (.inl (inl (inl (inr out))), (es', winEp0))
          | .inl (.inr x) =>
            let wasWin := cGsWin (esG es0)
            (out, es') ← injectEC (raw (hooksPRNGBucketParPaperC L B Δbucket qep tL par t))
              L (raw (2 + Δcka)) qep (raw (bucketParPaperAuthCfgEC Δbucket tL par)) es0 x
            let winEp' := if !wasWin && cGsWin (esG es') then some x.2.1.1 else winEp0
            return (.inl (inl (inr out)), (es', winEp'))
          | .inr p0 =>
            let s0 := esG es0
            if orE (esAbort es0) (orE (cGsWin s0) (!(corrGuard s0 p0))) then
              return (.inl (inr none), (es0, winEp0))
            else
              let s1 := cAfterCorrE (raw L) s0 p0
              (res, h') ← prngBucketRevealC (raw tL) (esH es0) s0 p0 (pGet (cGsSt s0) p0)
              match res with
              | none => return (.inl (inr none), (esMk s0 h' true, winEp0))
              | some stOut =>
                return (.inl (inr (some stOut)), (esMk s1 h' (esAbort es0), winEp0))
        | .inr x =>
          let wasWin := cGsWin (esG es0)
          (out, es') ← deliverForgeEC (raw (hooksPRNGBucketParPaperC L B Δbucket qep tL par t))
            L (raw (2 + Δcka)) qep (raw (bucketParPaperAuthCfgEC Δbucket tL par)) es0 x
          let winEp' := if !wasWin && cGsWin (esG es') then some x.2.2.1.1 else winEp0
          return (.inr out, (es', winEp'))
    PotOKSPrng P_prng (fun x => m + pbPot (Mode.mk true tL t) x.2.1)
      (hComp.eval (.cons sv (.cons qv .nil))) (1 + m + pbPot (Mode.mk true tL t) sv.1) := by
  intro hComp
  dsimp only [hComp]; rw [eval_bind_ret]
  refine potSPrng_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
  · refine potSPrng_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
    · refine potSPrng_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
      · refine potSPrng_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
        · refine potSPrng_caseSum (fun x _ => ?_) (fun _ _ => ?_)
          · rw [eval_bind_ret]
            refine potSPrng_ite (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0, Expr.v1, Expr.v6]))
              (fun hNotAbWin => ?_)
            have hab : sv.1.2.2 = false := by
              simp [orE_eval, esAbort, Expr.eval, Expr.v0, Expr.v6] at hNotAbWin; exact hNotAbWin.1
            refine potSPrng_caseOpt
              (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0, Expr.v1, Expr.v6]))
              (fun s1 hs1 => ?_)
            rw [eval_bind]
            have hs1_st : s1.1 = sv.1.1.1 := by
              have hs1' := cEpMgmtE_some_st_prng (2 + Δcka) qep (esG (.fst .v6))
                (.fst .v0) (isSomeE (.snd (.snd .v0))) _ hs1
              simpa [esG, Expr.eval, Expr.v0, Expr.v6, Env.get_cons_zero, Env.get_cons_succ] using hs1'
            set p0 := x.1
            set m_other := prngOtherPot (Mode.mk true tL t) s1.1 p0
            have hSum : m_other + prngVpReady (Mode.mk true tL t) (if p0 then s1.1.2 else s1.1.1) = pbPot (Mode.mk true tL t) sv.1 := by
              rw [prngOtherPot_add_pGet, hs1_st]; simp [pbPot, hab]
            refine ⟨fun {_} k hk' => (PotOKSPrng.bindPot
              (pb_vSendC_potOKS (sampKR := sampKR) (sampKC := sampKC)
                (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B Δbucket qep tL par t
                _ _ _ _ _ _ _ _ m m_other) (fun _ => ?_)).run k hk' |>.mono ?_⟩
            swap
            · dsimp only [p0] at hSum
              simp only [pGet_eval_st_prng, cGsSt, Expr.eval, Expr.v0, Expr.v1,
                Env.get_cons_zero, Env.get_cons_succ]
              exact Nat.le_of_eq (by rw [← hSum]; ac_rfl)
            refine potSPrng_caseOpt (fun hNone => ?_) (fun stCt hSome => ?_)
            · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hNone
              exact potSPrng_ret (by simp [pbVSendPost, hNone, pbPot, esMk, Expr.eval])
            · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSome
              refine potSPrng_ret ?_
              simp only [pbVSendPost, hSome, pbPot, esMk, esAbort, cRecordE_st_prng,
                Expr.eval, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Env.get_cons_zero, Env.get_cons_succ,
                hab, Bool.false_eq_true, ↓reduceIte]
              have hEq := prngPot_pSet_eq (Mode.mk true tL t) s1.1 p0 stCt.1; dsimp only at hEq
              change m + (let st' := if p0 then (s1.1.1, stCt.1) else (stCt.1, s1.1.2);
                          prngVpReady (Mode.mk true tL t) st'.1 + prngVpReady (Mode.mk true tL t) st'.2) ≤
                m + m_other + prngVpReady (Mode.mk true tL t) stCt.1
              rw [hEq]; omega
          · exact potSPrng_ret (by simp [Expr.eval, Expr.v0, Expr.v5])
        · rw [eval_bind]
          exact PotOKSPrng.bindPot
            (pb_deliverEC_potOKS L B Δbucket qep maxSkip tL par false t _ (.fst (Expr.v4 (O := OOpb))) .v0 _ m)
            (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0]))
      · rw [eval_bind]
        exact PotOKSPrng.bindPot
          (pb_injectEC_potOKS L B Δcka Δbucket qep tL par false t _ (.fst (Expr.v3 (O := OOpb))) .v0 _ m)
          (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0]))
    · refine potSPrng_ite (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0, Expr.v2])) (fun _ => ?_)
      rw [eval_bind]
      refine PotOKSPrng.bindPot
        (potSPrng_comp_const _ _ (m + pbPot (Mode.mk true tL t) sv.1) (1 + m + pbPot (Mode.mk true tL t) sv.1)
          (fun _ => Nat.le_refl _) (by simp [prngBucketRevealC_queries]; omega)) (fun _ => ?_)
      exact potSPrng_caseOpt (fun _ => potSPrng_ret (by simp [pbPot, esMk, Expr.eval]))
        (fun _ _ => potSPrng_ret (by
          simp [pbPot, esMk, esAbort, esG, cAfterCorrE_st_prng, Expr.eval, Expr.v0, Expr.v4]))
  · rw [eval_bind]
    exact PotOKSPrng.bindPot
      (pb_deliverForgeEC_potOKS L B Δcka Δbucket qep tL par false t _ (.fst (Expr.v1 (O := OOpb))) .v0 _ m)
      (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0]))

private theorem pb_split_handle_potOKS_aux (L B Δcka Δbucket qep maxSkip : ℕ) (tL : Option ℕ)
    (par gMain : Bool) (t0 m : ℕ)
    (qv : (prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).Q.denote)
    (sv : (Ty.denote pbRedEsTyPb)) :
    PotOKSPrng P_prng (fun x => m + pbPot (Mode.mk true tL t0) x.2.1)
      ((redPRNGAuthDFPaperBucketSplitProgGen (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
          (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK)
          L B Δcka Δbucket qep maxSkip tL par gMain t0).handle.eval (.cons sv (.cons qv .nil)))
      (1 + m + pbPot (Mode.mk true tL t0) sv.1) := by
  dsimp only [redPRNGAuthDFPaperBucketSplitProgGen]; rw [eval_bind_ret]
  refine potSPrng_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
  · refine potSPrng_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
    · refine potSPrng_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
      · refine potSPrng_caseSum (fun _ _ => ?_) (fun _ _ => ?_)
        · refine potSPrng_caseSum (fun x _ => ?_) (fun _ _ => ?_)
          · rw [eval_bind_ret]
            refine potSPrng_ite (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0, Expr.v1, Expr.v6]))
              (fun hNotAbWin => ?_)
            have hab : sv.1.2.2 = false := by
              simp [orE_eval, esAbort, Expr.eval, Expr.v0, Expr.v6] at hNotAbWin; exact hNotAbWin.1
            refine potSPrng_caseOpt
              (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0, Expr.v1, Expr.v6]))
              (fun s1 hs1 => ?_)
            rw [eval_bind]
            have hs1_st : s1.1 = sv.1.1.1 := by
              have hs1' := cEpMgmtE_some_st_prng (2 + Δcka) qep (esG (.fst .v6))
                (.fst .v0) (isSomeE (.snd (.snd .v0))) _ hs1
              simpa [esG, Expr.eval, Expr.v0, Expr.v6, Env.get_cons_zero, Env.get_cons_succ] using hs1'
            set p0 := x.1
            set m_other := prngOtherPot (Mode.mk true tL t0) s1.1 p0
            have hSum : m_other + prngVpReady (Mode.mk true tL t0) (if p0 then s1.1.2 else s1.1.1) =
                pbPot (Mode.mk true tL t0) sv.1 := by
              rw [prngOtherPot_add_pGet, hs1_st]; simp [pbPot, hab]
            refine ⟨fun {_} k hk' => (PotOKSPrng.bindPot
              (pb_vSendC_potOKS (sampKR := sampKR) (sampKC := sampKC)
                (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B Δbucket qep tL par t0
                _ _ _ _ _ _ _ _ m m_other) (fun _ => ?_)).run k hk' |>.mono ?_⟩
            swap
            · dsimp only [p0] at hSum
              simp only [pGet_eval_st_prng, cGsSt, Expr.eval, Expr.v0, Expr.v1,
                Env.get_cons_zero, Env.get_cons_succ]
              exact Nat.le_of_eq (by rw [← hSum]; ac_rfl)
            refine potSPrng_caseOpt (fun hNone => ?_) (fun stCt hSome => ?_)
            · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hNone
              exact potSPrng_ret (by simp [pbVSendPost, hNone, pbPot, esMk, Expr.eval])
            · simp only [Expr.eval, Expr.v0, Env.get_cons_zero] at hSome
              refine potSPrng_ret ?_
              simp only [pbVSendPost, hSome, pbPot, esMk, esAbort, cRecordE_st_prng,
                Expr.eval, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Env.get_cons_zero, Env.get_cons_succ,
                hab, Bool.false_eq_true, ↓reduceIte]
              have hEq := prngPot_pSet_eq (Mode.mk true tL t0) s1.1 p0 stCt.1; dsimp only at hEq
              change m + (let st' := if p0 then (s1.1.1, stCt.1) else (stCt.1, s1.1.2);
                          prngVpReady (Mode.mk true tL t0) st'.1 + prngVpReady (Mode.mk true tL t0) st'.2) ≤
                m + m_other + prngVpReady (Mode.mk true tL t0) stCt.1
              rw [hEq]; omega
          · exact potSPrng_ret (by simp [Expr.eval, Expr.v0, Expr.v5])
        · rw [eval_bind]
          exact PotOKSPrng.bindPot
            (pb_deliverEC_potOKS L B Δbucket qep maxSkip tL par gMain t0 _ (.fst (Expr.v4 (O := OOpb))) .v0 _ m)
            (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0]))
      · rw [eval_bind]
        exact PotOKSPrng.bindPot
          (pb_injectEC_potOKS L B Δcka Δbucket qep tL par gMain t0 _ (.fst (Expr.v3 (O := OOpb))) .v0 _ m)
          (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0]))
    · refine potSPrng_ite (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0, Expr.v2])) (fun _ => ?_)
      rw [eval_bind]
      refine PotOKSPrng.bindPot
        (potSPrng_comp_const _ _ (m + pbPot (Mode.mk true tL t0) sv.1) (1 + m + pbPot (Mode.mk true tL t0) sv.1)
          (fun _ => Nat.le_refl _)
          (by cases gMain <;> simp [prngBucketRevealSplitC, prngBucketRevealC_queries,
                prngBucketRevealForgedHdrC_queries]; omega)) (fun _ => ?_)
      exact potSPrng_caseOpt (fun _ => potSPrng_ret (by simp [pbPot, esMk, Expr.eval]))
        (fun _ _ => potSPrng_ret (by
          simp [pbPot, esMk, esAbort, esG, cAfterCorrE_st_prng, Expr.eval, Expr.v0, Expr.v4]))
  · rw [eval_bind]
    exact PotOKSPrng.bindPot
      (pb_deliverForgeEC_potOKS L B Δcka Δbucket qep tL par gMain t0 _ (.fst (Expr.v1 (O := OOpb))) .v0 _ m)
      (fun _ => potSPrng_ret (by simp [Expr.eval, Expr.v0]))

end PbPotOK

/-- Combined syntactic + potential PRF-PRNG query bound `min (2 + 2 * q) (q + 3)` for
`redPRNGAuthDFPaperBucketSplitProg` (`gMain : Bool`). -/
theorem redPRNGAuthDFPaperBucketSplitProg_makesAtMostQueries_impl
    (L B Δcka qep maxSkip : ℕ) (tL : Option ℕ) (par gMain : Bool) (t0 q : ℕ)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E)
    (hA : DeliverForge.MakesAtMostQueriesDF A q) :
    (((redPRNGAuthDFPaperBucketSplitProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L B Δcka qep maxSkip tL par gMain t0).eval (fun _ => A) ())).IsQueryBoundP
      (· matches .inr _) (min (2 + 2 * q) (q + 3)) := by
  refine Computational.Proofs.ReductionDsl.SM.RedPRNGPotOK.costedReduction_makesAtMostQueries_prng
    _ (fun st : (Ty.denote pbRedEsTyPb) => pbPot (Mode.mk true tL t0) st.1) q A
    (hA.of_imp (fun x hx => by cases x <;> [cases hx; rfl]))
    (redPRNGAuthDFPaperBucketSplitProgGen_totalQueries L B Δcka (3 + Δcka) qep maxSkip tL par gMain t0 q)
    ?_
    (fun m qv sv => pb_split_handle_potOKS_aux L B Δcka (3 + Δcka) qep maxSkip tL par gMain t0 m qv sv)
    (by simp [redPRNGAuthDFPaperBucketSplitProg, redPRNGAuthDFPaperBucketSplitProgGen, Comp.queries])
  dsimp only [redPRNGAuthDFPaperBucketSplitProg, redPRNGAuthDFPaperBucketSplitProgGen]
  rw [eval_bind]
  exact Computational.Proofs.ReductionDsl.SM.RedPRNGPotOK.PotOKSPrng.bindPot
    (initPRNGBucketHybridEStateC_potOKS L (3 + Δcka) tL par t0 (.bool false) _ q)
    (fun _ => Computational.Proofs.ReductionDsl.SM.RedPRNGPotOK.potSPrng_ret
      (by simp [Expr.eval, Expr.v0]))

/-- Combined syntactic + potential PRF-PRNG query bound `min (2 + 2 * q) (q + 3)` for
`redPRNGAuthDFBucketHybridProg`. -/
theorem redPRNGAuthDFBucketHybridProg_makesAtMostQueries_impl
    (L B Δcka qep maxSkip : ℕ) (tL : Option ℕ) (par : Bool) (t q : ℕ)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E)
    (hA : DeliverForge.MakesAtMostQueriesDF A q) :
    (((redPRNGAuthDFBucketHybridProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L B Δcka qep maxSkip tL par t).eval (fun _ => A) ())).IsQueryBoundP
      (· matches .inr _) (min (2 + 2 * q) (q + 3)) := by
  refine Computational.Proofs.ReductionDsl.SM.RedPRNGPotOK.costedReduction_makesAtMostQueries_prng
    _ (fun st : (Ty.denote pbRedEsTyPb) => pbPot (Mode.mk true tL t) st.1) q A
    (hA.of_imp (fun x hx => by cases x <;> [cases hx; rfl]))
    (redPRNGAuthDFBucketHybridProg_totalQueries L B Δcka qep maxSkip tL par t q)
    ?_
    (fun m qv sv => pb_handle_potOKS_aux L B Δcka (3 + Δcka) qep maxSkip tL par t
      (fun s0 p0 => cCorrAllowedE L s0 p0) m qv sv)
    (by simp [redPRNGAuthDFBucketHybridProg, redPRNGAuthDFBucketHybridProgGen, Comp.queries])
  dsimp only [redPRNGAuthDFBucketHybridProg, redPRNGAuthDFBucketHybridProgGen]
  rw [eval_bind]
  exact Computational.Proofs.ReductionDsl.SM.RedPRNGPotOK.PotOKSPrng.bindPot
    (initPRNGBucketHybridEStateC_potOKS L (3 + Δcka) tL par t (.bool false) _ q)
    (fun _ => Computational.Proofs.ReductionDsl.SM.RedPRNGPotOK.potSPrng_ret
      (by simp [Expr.eval, Expr.v0]))

/-- Combined syntactic + potential PRF-PRNG query bound `min (2 + 2 * q) (q + 3)` for
`redPRNGAuthDFPaperBucketHybridProg`. -/
theorem redPRNGAuthDFPaperBucketHybridProg_makesAtMostQueries_impl
    (L B Δcka qep maxSkip : ℕ) (tL : Option ℕ) (par : Bool) (t q : ℕ)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E)
    (hA : DeliverForge.MakesAtMostQueriesDF A q) :
    (((redPRNGAuthDFPaperBucketHybridProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L B Δcka qep maxSkip tL par t).eval (fun _ => A) ())).IsQueryBoundP
      (· matches .inr _) (min (2 + 2 * q) (q + 3)) := by
  refine Computational.Proofs.ReductionDsl.SM.RedPRNGPotOK.costedReduction_makesAtMostQueries_prng
    _ (fun st : (Ty.denote pbRedEsTyPb) => pbPot (Mode.mk true tL t) st.1) q A
    (hA.of_imp (fun x hx => by cases x <;> [cases hx; rfl]))
    (redPRNGAuthDFPaperBucketHybridProg_totalQueries L B Δcka qep maxSkip tL par t q)
    ?_
    (fun m qv sv => pb_handle_potOKS_aux L B Δcka (3 + Δcka) qep maxSkip tL par t
      (fun s0 p0 => cCorrAllowedPaperE L s0 p0) m qv sv)
    (by simp [redPRNGAuthDFPaperBucketHybridProg, redPRNGAuthDFPaperBucketHybridProgGen, Comp.queries])
  dsimp only [redPRNGAuthDFPaperBucketHybridProg, redPRNGAuthDFPaperBucketHybridProgGen]
  rw [eval_bind]
  exact Computational.Proofs.ReductionDsl.SM.RedPRNGPotOK.PotOKSPrng.bindPot
    (initPRNGBucketHybridEStateC_potOKS L (3 + Δcka) tL par t (.bool false) _ q)
    (fun _ => Computational.Proofs.ReductionDsl.SM.RedPRNGPotOK.potSPrng_ret
      (by simp [Expr.eval, Expr.v0]))

end HooksPRNGBucketCDF

end CryptoGames.SM.Construction
