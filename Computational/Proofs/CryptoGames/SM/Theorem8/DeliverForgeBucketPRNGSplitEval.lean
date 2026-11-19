/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGDefs -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGEvalHooks
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGSplitEvalHooks
import Computational.Proofs.ReductionDsl.SM.DeliverForgeBucketSimEval
import Computational.Proofs.ReductionDsl.Bridge
import Computational.Proofs.ReductionDsl.Notation

set_option autoImplicit false
set_option linter.unusedSectionVars false
open CryptoGames (CKAScheme FSAEADScheme PRFPRNG Party)
open CryptoGames.CKA (ckaSMCodecDF ckaSMQDF ckaSMRDF)
open CryptoGames.PRFPRNG (prngIface prngOps prngSig)
open CryptoGames.SM (Config and_eval authLosingConditionsAvoided ite_eval not_eval orE_eval pair_eval smRrEnc)
open CryptoGames.SM.Construction (Header PartyState bucketParPaperAuthCfgEC bucketParPaperAuthCfgEC_agrees eval_caseSum_inl eval_caseSum_inr hooksPRNGBucketSplitPaperC prngBucketEsTy prngBucketHsEnc prngBucketHsLc prngBucketHsTy prngBucketRedEsTy prngVpEnc prngVpTy redPRNGAuthDFPaperBucketSplitProg redPRNGAuthDFPaperBucketSplitProgGen)
open CryptoGames.SM.Engine (ConfigECAgrees EState Hooks HooksCAgrees HooksVRInv SMEngineInv SMStateBoundedEngine SMVRInv VP authOut cAuthOKE_eval cGsWin coinsE deliverForgeEC_eval esAbort esEnc esG esH eval_bind eval_bind_ret eval_caseOpt eval_ret injectEC_eval optNatLit vpTblEnc)
open ReductionDsl (Comp Env Expr Ty handlerImpl isGameQuery)

open Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGSplitEvalHooks (hooksPRNGBucketSplitGen hooksPRNGBucketSplitPaperC_agrees_vr hooksPRNGBucketSplit_vrInv implEDFPaperBucketRaw_split_bounded initPRNGBucketHybridEStateC_eval initPRNGBucketRaw initPRNGBucketRaw_inv initPRNGBucketRaw_vrInv isHonestHdrPRNGBucketE_eval prngBucketHBoundedStep prngBucketHBoundedStep_mono rootPRNGBucketHybrid_zero_support_some simulateQ_sampleT_run_bucket)

namespace Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGSplitEval

public section

open OracleSpec OracleComp


open scoped Computational.Proofs.ReductionDsl.Notation

section HooksPRNGBucketEval

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}
local notation "Sev" => prngSig KC Γ CCoins T I KR RSt K SS RS M E
variable {ckaInitA ckaInitB : KC → Γ} {ckaSend : Γ → CCoins → Γ × T × I}
  {ckaReceive : Γ → T → Γ × I} {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS} {fsInitReceiver : K → RS} {fsSend : SS → Header T → M → SS × E}
  {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
  {lam : I} {defaultE : E} {sampKR : ProbComp KR} {sampKC : ProbComp KC}
  {sampCCoins : ProbComp CCoins} {sampI : ProbComp I} {sampK : ProbComp K}

local notation "OOev" =>
  prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE

local notation "IIev" =>
  prngIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK

local notation "pbHsTyEv" => @prngBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "pbVpTyEv" => @prngVpTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "pbEsTyEv" => @prngBucketEsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "pbRedEsTyEv" => @prngBucketRedEsTy KC Γ CCoins T I KR RSt K SS RS M E

private theorem mem_support_implEDFPaperBucketMode
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hk : Hooks (_root_.CryptoGames.PRFPRNG.spec RSt I K) (_root_.CryptoGames.SM.Construction.DeliverForge.PRNGBucketState T RSt K I)
      Γ T RSt SS RS M E CCoins Γ (Option RSt) SS RS)
    (Δ qep maxSkip : ℕ) (cfg : Config M) (gMain : Bool)
    (q : (unifSpec + _root_.CryptoGames.SM.Construction.DeliverForge.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (s : EState (VP Γ T (Option RSt) SS RS) M (Header T × E)
      (_root_.CryptoGames.SM.Construction.DeliverForge.PRNGBucketState T RSt K I)) (winEp : Option ℕ)
    (u : (unifSpec + _root_.CryptoGames.SM.Construction.DeliverForge.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Range q)
    (s₁ : EState (VP Γ T (Option RSt) SS RS) M (Header T × E)
      (_root_.CryptoGames.SM.Construction.DeliverForge.PRNGBucketState T RSt K I)) (winEp₁ : Option ℕ)
    (hmem : (u, (s₁, winEp₁)) ∈
      support ((_root_.CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketMode hk Δ qep maxSkip cfg gMain
        _root_.CryptoGames.SM.Construction.DeliverForge.isHonestHdrPRNGBucket q).run (s, winEp))) :
    (u, s₁) ∈ support ((_root_.CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketRaw hk Δ qep maxSkip cfg q).run s) := by
  unfold _root_.CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketMode _root_.CryptoGames.SM.Construction.DeliverForge.withWinEpDFMode
    _root_.CryptoGames.SM.Construction.DeliverForge.withWinEpDF at hmem
  cases gMain <;>
  · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_mk] at hmem
    rw [mem_support_bind_iff] at hmem
    obtain ⟨⟨r', s'⟩, hr, hp⟩ := hmem
    simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hp
    rcases hp with ⟨rfl, rfl, _⟩
    exact hr

private theorem rdecDF_splitHandle_inject_eval
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B Δcka Δbucket qep maxSkip : ℕ) (tL : Option ℕ) (par gMain : Bool) (t0 : ℕ)
    (cfg : Config M)
    (hCfg : ConfigECAgrees (bucketParPaperAuthCfgEC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) Δbucket tL par) cfg)
    (heqT : eqT = (· == ·)) (heqE : eqE = (· == ·))
    {m : ℕ} {VROk : RS → Prop}
    (hHk : HooksCAgrees prngBucketHsEnc (prngBucketHBoundedStep L (m + 1))
      (HBoundedPost := prngBucketHBoundedStep L m) (VROk := VROk)
      (hooksPRNGBucketSplitPaperC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δbucket qep tL par gMain t0)
      (hooksPRNGBucketSplitGen cka prng fs Δbucket qep tL par gMain t0))
    (es : EState (VP Γ T (Option RSt) SS RS) M (Header T × E)
      (_root_.CryptoGames.SM.Construction.DeliverForge.PRNGBucketState T RSt K I))
    (winEp : Option ℕ) (P : Party) (c : Header T × E)
    (hHB : prngBucketHBoundedStep L (m + 1) es.h)
    (hBound : SMStateBoundedEngine L es.g)
    (hVR : ∀ t v, (es.g.st P).vR t = some v → VROk v) :
    ((fun p =>
      ((ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).rdec
        (.inl (.inl (.inr (P, c)))) p.1, p.2)) <$>
      ((redPRNGAuthDFPaperBucketSplitProgGen (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L B Δcka Δbucket qep maxSkip tL par gMain t0).handle).eval
        (.cons (esEnc prngVpEnc prngBucketHsEnc es, winEp)
          (.cons ((ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).qenc
            (.inl (.inl (.inr (P, c))))) .nil))) =
      Prod.map id (Prod.map (esEnc prngVpEnc prngBucketHsEnc) id) <$>
        ((_root_.CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketMode
          (hooksPRNGBucketSplitGen cka prng fs Δbucket qep tL par gMain t0)
          (2 + Δcka) qep maxSkip cfg gMain _root_.CryptoGames.SM.Construction.DeliverForge.isHonestHdrPRNGBucket)
          (.inr (.inl (.inl (.inr (P, c)))))).run (es, winEp) := by
  let hkC := hooksPRNGBucketSplitPaperC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) L B Δbucket qep tL par gMain t0
  let hk := hooksPRNGBucketSplitGen cka prng fs Δbucket qep tL par gMain t0
  let cfgC := bucketParPaperAuthCfgEC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) Δbucket tL par
  let ρ₀ : Env [.prod pbEsTyEv (.opt .nat), ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E] :=
    .cons (esEnc prngVpEnc prngBucketHsEnc es, winEp)
      (.cons ((ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).qenc
        (.inl (.inl (.inr (P, c))))) .nil)
  dsimp only [redPRNGAuthDFPaperBucketSplitProgGen]
  rw [eval_bind_ret]
  have h0 : (_root_.ReductionDsl.Expr.pair (.fst (_root_.ReductionDsl.Expr.v0 (O := OOev))) (.pair (.snd .v0) .v1)).eval ρ₀ =
      (esEnc prngVpEnc prngBucketHsEnc es, winEp,
       (ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).qenc (.inl (.inl (.inr (P, c))))) := rfl
  rw [h0]; clear h0
  rw [eval_caseSum_inl rfl, eval_caseSum_inl rfl, eval_caseSum_inr rfl, eval_bind]
  have hVpEnc :
      @vpTblEnc KC Γ CCoins T I KR RSt K SS RS M E
        (.base .γ) (.opt (.base .sig)) (.base .ss) (.base .rs) = prngVpEnc := rfl
  rw [injectEC_eval prngBucketHsEnc (prngBucketHBoundedStep L (m + 1)) hkC hk hHk
    L (2 + Δcka) qep cfgC cfg hCfg heqT heqE _ _ _ es P c hHB hBound hVR rfl rfl, hVpEnc]
  unfold _root_.CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketMode _root_.CryptoGames.SM.Construction.DeliverForge.withWinEpDFMode _root_.CryptoGames.SM.Construction.DeliverForge.withWinEpDF
  cases gMain <;>
  · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_mk,
      map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
    refine bind_congr fun ⟨out, es'⟩ => ?_
    have hOut :
        (ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).rdec
          (.inl (.inl (.inr (P, c)))) (.inl (.inl (.inr (Option.map smRrEnc out)))) = out := by
      rcases out with _ | (_ | ⟨m1, i1, m2⟩) <;> rfl
    rw [eval_ret, pure_bind]
    dsimp only [Function.comp_apply, Prod.map]
    rw [pair_eval, pair_eval,
      show (_root_.ReductionDsl.Expr.inl (.inl (.inr (.fst (_root_.ReductionDsl.Expr.v0 (O := OOev)))))).eval _ =
        Sum.inl (Sum.inl (Sum.inr (Option.map smRrEnc out))) from rfl,
      show (_root_.ReductionDsl.Expr.snd (_root_.ReductionDsl.Expr.v0 (O := OOev))).eval _ = esEnc prngVpEnc prngBucketHsEnc es' from rfl]
    refine congrArg pure (Prod.ext hOut (Prod.ext rfl ?_))
    rw [ite_eval, and_eval, and_eval, not_eval, orE_eval, and_eval, not_eval,
      isHonestHdrPRNGBucketE_eval heqT (esH (.fst (_root_.ReductionDsl.Expr.v4 (O := OOev)))) (.fst (.snd .v1))
        _ es.h c.1 rfl rfl]
    cases P
    · change (if ((!es.g.win && es'.g.win) &&
          (_ || (decide (c.1.1 = (es.g.st .A).tcur + 1) &&
            !_root_.CryptoGames.SM.Construction.DeliverForge.isHonestHdrPRNGBucket es.h c.1))) = true
        then some c.1.1 else winEp) = _
      cases (!es.g.win && es'.g.win) <;>
        cases (decide (c.1.1 = (es.g.st .A).tcur + 1) &&
          !_root_.CryptoGames.SM.Construction.DeliverForge.isHonestHdrPRNGBucket es.h c.1) <;> rfl
    · change (if ((!es.g.win && es'.g.win) &&
          (_ || (decide (c.1.1 = (es.g.st .B).tcur + 1) &&
            !_root_.CryptoGames.SM.Construction.DeliverForge.isHonestHdrPRNGBucket es.h c.1))) = true
        then some c.1.1 else winEp) = _
      cases (!es.g.win && es'.g.win) <;>
        cases (decide (c.1.1 = (es.g.st .B).tcur + 1) &&
          !_root_.CryptoGames.SM.Construction.DeliverForge.isHonestHdrPRNGBucket es.h c.1) <;> rfl

private theorem rdecDF_splitHandle_eval
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType K]
    (hDefaultE : defaultE = default)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B Δcka Δbucket qep maxSkip : ℕ) (tL : Option ℕ) (par gMain : Bool) (t0 : ℕ)
    (cfg : Config M)
    (hCfg : ConfigECAgrees (bucketParPaperAuthCfgEC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) Δbucket tL par) cfg)
    (hCfgWin : cfg.deliverWin = false)
    (heqT : eqT = (· == ·)) (heqM : eqM = (· == ·)) (heqE : eqE = (· == ·))
    {m : ℕ} {VROk : RS → Prop}
    (hHk : HooksCAgrees prngBucketHsEnc (prngBucketHBoundedStep L (m + 1))
      (HBoundedPost := prngBucketHBoundedStep L m) (VROk := VROk)
      (hooksPRNGBucketSplitPaperC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δbucket qep tL par gMain t0)
      (hooksPRNGBucketSplitGen cka prng fs Δbucket qep tL par gMain t0))
    (es : EState (VP Γ T (Option RSt) SS RS) M (Header T × E)
      (_root_.CryptoGames.SM.Construction.DeliverForge.PRNGBucketState T RSt K I))
    (winEp : Option ℕ)
    (q : (_root_.CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hHB : prngBucketHBoundedStep L (m + 1) es.h)
    (hBound : SMStateBoundedEngine L es.g)
    (hVR : ∀ P t v, (es.g.st P).vR t = some v → VROk v) :
    ((fun p =>
      ((ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).rdec q p.1, p.2)) <$>
      ((redPRNGAuthDFPaperBucketSplitProgGen (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L B Δcka Δbucket qep maxSkip tL par gMain t0).handle).eval
        (.cons (esEnc prngVpEnc prngBucketHsEnc es, winEp)
          (.cons ((ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).qenc q) .nil))) =
      Prod.map id (Prod.map (esEnc prngVpEnc prngBucketHsEnc) id) <$>
        ((_root_.CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketMode
          (hooksPRNGBucketSplitGen cka prng fs Δbucket qep tL par gMain t0)
          (2 + Δcka) qep maxSkip cfg gMain _root_.CryptoGames.SM.Construction.DeliverForge.isHonestHdrPRNGBucket)
          (.inr q)).run (es, winEp) := by
  let hkC := hooksPRNGBucketSplitPaperC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) L B Δbucket qep tL par gMain t0
  let hk := hooksPRNGBucketSplitGen cka prng fs Δbucket qep tL par gMain t0
  let cfgC := bucketParPaperAuthCfgEC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) Δbucket tL par
  let splitH := (redPRNGAuthDFPaperBucketSplitProgGen (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)
    L B Δcka Δbucket qep maxSkip tL par gMain t0).handle
  let ρ₀ : Env [.prod pbEsTyEv (.opt .nat), ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E] :=
    .cons (esEnc prngVpEnc prngBucketHsEnc es, winEp)
      (.cons ((ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).qenc q) .nil)
  have hPaper := _root_.CryptoGames.SM.Engine.rdecDF_bucketHandleDFPaperC_eval hDefaultE prngBucketHsEnc
    (prngBucketHBoundedStep L (m + 1)) hkC hk hHk L (2 + Δcka) qep maxSkip cfgC cfg hCfg hCfgWin
    heqT heqM heqE .v0 .v1 ρ₀ es winEp q hHB hBound hVR rfl rfl
  rcases q with ((((⟨P, msg, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩
  · -- `.transmit`
    have hL : splitH.eval ρ₀ =
        (_root_.CryptoGames.SM.Engine.bucketHandleDFPaperC hkC L (2 + Δcka) qep maxSkip cfgC .v0 .v1).eval ρ₀ := by
      dsimp only [splitH, redPRNGAuthDFPaperBucketSplitProgGen, _root_.CryptoGames.SM.Engine.bucketHandleDFPaperC,
        _root_.CryptoGames.SM.Engine.bucketHandleDFByCorrC, hkC, cfgC]
      rw [eval_bind_ret, eval_bind_ret]
      have h0 : (_root_.ReductionDsl.Expr.pair (.fst (_root_.ReductionDsl.Expr.v0 (O := OOev))) (.pair (.snd .v0) .v1)).eval ρ₀ =
          (esEnc prngVpEnc prngBucketHsEnc es, winEp,
           (ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).qenc (.inl (.inl (.inl (.inl (.inl (P, msg, r))))))) := rfl
      rw [h0]
      rw [eval_caseSum_inl rfl, eval_caseSum_inl rfl, eval_caseSum_inl rfl,
        eval_caseSum_inl rfl, eval_caseSum_inl rfl,
        eval_caseSum_inl rfl, eval_caseSum_inl rfl, eval_caseSum_inl rfl,
        eval_caseSum_inl rfl, eval_caseSum_inl rfl]
    refine (congrArg _ hL).trans (hPaper.trans ?_)
    cases gMain
    · unfold _root_.CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketMode _root_.CryptoGames.SM.Construction.DeliverForge.withWinEpDFMode
        _root_.CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucket _root_.CryptoGames.SM.Construction.DeliverForge.withWinEpDF
      simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_mk,
        map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨out, es'⟩ hmem => ?_
      have hwin := _root_.CryptoGames.SM.Engine.transmitEBucket_win_eq hk (2 + Δcka) qep es (P, msg, r) (out, es') hmem
      have hnf : (!es.g.win && es'.g.win) = false := by rw [hwin]; cases es.g.win <;> rfl
      simp [hnf]
    · rfl
  · -- `.chall`
    have hL : splitH.eval ρ₀ =
        (_root_.CryptoGames.SM.Engine.bucketHandleDFPaperC hkC L (2 + Δcka) qep maxSkip cfgC .v0 .v1).eval ρ₀ := by
      dsimp only [splitH, redPRNGAuthDFPaperBucketSplitProgGen, _root_.CryptoGames.SM.Engine.bucketHandleDFPaperC,
        _root_.CryptoGames.SM.Engine.bucketHandleDFByCorrC, hkC, cfgC]
      rw [eval_bind_ret, eval_bind_ret]
      have h0 : (_root_.ReductionDsl.Expr.pair (.fst (_root_.ReductionDsl.Expr.v0 (O := OOev))) (.pair (.snd .v0) .v1)).eval ρ₀ =
          (esEnc prngVpEnc prngBucketHsEnc es, winEp,
           (ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).qenc (.inl (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))))) := rfl
      rw [h0]
      rw [eval_caseSum_inl rfl, eval_caseSum_inl rfl, eval_caseSum_inl rfl,
        eval_caseSum_inl rfl, eval_caseSum_inr rfl,
        eval_caseSum_inl rfl, eval_caseSum_inl rfl, eval_caseSum_inl rfl,
        eval_caseSum_inl rfl, eval_caseSum_inr rfl]
    refine (congrArg _ hL).trans (hPaper.trans ?_)
    cases gMain
    · unfold _root_.CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketMode _root_.CryptoGames.SM.Construction.DeliverForge.withWinEpDFMode
        _root_.CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucket _root_.CryptoGames.SM.Construction.DeliverForge.withWinEpDF
      simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_mk]
      simp [_root_.CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketRaw, _root_.CryptoGames.SM.Construction.DeliverForge.challEBucket]
    · rfl
  · -- `.deliver`
    have hL : splitH.eval ρ₀ =
        (_root_.CryptoGames.SM.Engine.bucketHandleDFPaperC hkC L (2 + Δcka) qep maxSkip cfgC .v0 .v1).eval ρ₀ := by
      dsimp only [splitH, redPRNGAuthDFPaperBucketSplitProgGen, _root_.CryptoGames.SM.Engine.bucketHandleDFPaperC,
        _root_.CryptoGames.SM.Engine.bucketHandleDFByCorrC, hkC, cfgC]
      rw [eval_bind_ret, eval_bind_ret]
      have h0 : (_root_.ReductionDsl.Expr.pair (.fst (_root_.ReductionDsl.Expr.v0 (O := OOev))) (.pair (.snd .v0) .v1)).eval ρ₀ =
          (esEnc prngVpEnc prngBucketHsEnc es, winEp,
           (ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).qenc (.inl (.inl (.inl (.inr (P, c)))))) := rfl
      rw [h0]
      rw [eval_caseSum_inl rfl, eval_caseSum_inl rfl, eval_caseSum_inl rfl,
        eval_caseSum_inr rfl,
        eval_caseSum_inl rfl, eval_caseSum_inl rfl, eval_caseSum_inl rfl,
        eval_caseSum_inr rfl]
    refine (congrArg _ hL).trans (hPaper.trans ?_)
    cases gMain
    · unfold _root_.CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketMode _root_.CryptoGames.SM.Construction.DeliverForge.withWinEpDFMode
        _root_.CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucket _root_.CryptoGames.SM.Construction.DeliverForge.withWinEpDF
      simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_mk,
        map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨out, es'⟩ hmem => ?_
      have hwin := _root_.CryptoGames.SM.Engine.deliverE_win_eq_of_deliverWin_false hk cfg hCfgWin es (P, c) (out, es') hmem
      have hnf : (!es.g.win && es'.g.win) = false := by rw [hwin]; cases es.g.win <;> rfl
      simp [hnf]
    · rfl
  · -- `.inject`
    exact rdecDF_splitHandle_inject_eval cka prng fs L B Δcka Δbucket qep maxSkip tL par gMain t0
      cfg hCfg heqT heqE hHk es winEp P c hHB hBound (hVR P)
  · -- `.corr`
    have hL : splitH.eval ρ₀ =
        (_root_.CryptoGames.SM.Engine.bucketHandleDFPaperC hkC L (2 + Δcka) qep maxSkip cfgC .v0 .v1).eval ρ₀ := by
      dsimp only [splitH, redPRNGAuthDFPaperBucketSplitProgGen, _root_.CryptoGames.SM.Engine.bucketHandleDFPaperC,
        _root_.CryptoGames.SM.Engine.bucketHandleDFByCorrC, hkC, cfgC, hooksPRNGBucketSplitPaperC]
      rw [eval_bind_ret, eval_bind_ret]
      have h0 : (_root_.ReductionDsl.Expr.pair (.fst (_root_.ReductionDsl.Expr.v0 (O := OOev))) (.pair (.snd .v0) .v1)).eval ρ₀ =
          (esEnc prngVpEnc prngBucketHsEnc es, winEp,
           (ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).qenc (.inl (.inr P))) := rfl
      rw [h0]
      rw [eval_caseSum_inl rfl, eval_caseSum_inr rfl,
        eval_caseSum_inl rfl, eval_caseSum_inr rfl]
    refine (congrArg _ hL).trans (hPaper.trans ?_)
    cases gMain
    · unfold _root_.CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketMode _root_.CryptoGames.SM.Construction.DeliverForge.withWinEpDFMode
        _root_.CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucket _root_.CryptoGames.SM.Construction.DeliverForge.withWinEpDF
      simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_mk,
        map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨out, es'⟩ hmem => ?_
      have hwin := _root_.CryptoGames.SM.Engine.corrEPaperBucket_win_eq hk es P (out, es') hmem
      have hnf : (!es.g.win && es'.g.win) = false := by rw [hwin]; cases es.g.win <;> rfl
      simp [hnf]
    · rfl
  · -- `.deliverForge`
    dsimp only [redPRNGAuthDFPaperBucketSplitProgGen]
    rw [eval_bind_ret]
    have h0 : (_root_.ReductionDsl.Expr.pair (.fst (_root_.ReductionDsl.Expr.v0 (O := OOev))) (.pair (.snd .v0) .v1)).eval ρ₀ =
        (esEnc prngVpEnc prngBucketHsEnc es, winEp,
         (ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).qenc (.inr (P, c, c'))) := rfl
    rw [h0]; clear h0
    rw [eval_caseSum_inr rfl, eval_bind]
    have hVpEnc :
        @vpTblEnc KC Γ CCoins T I KR RSt K SS RS M E
          (.base .γ) (.opt (.base .sig)) (.base .ss) (.base .rs) = prngVpEnc := rfl
    rw [deliverForgeEC_eval prngBucketHsEnc (prngBucketHBoundedStep L (m + 1)) hkC hk hHk
      L (2 + Δcka) qep cfgC cfg hCfg heqT heqE _ _ _ es P c c' hHB hBound (hVR P) rfl rfl, hVpEnc]
    unfold _root_.CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketMode _root_.CryptoGames.SM.Construction.DeliverForge.withWinEpDFMode _root_.CryptoGames.SM.Construction.DeliverForge.withWinEpDF
    cases gMain <;>
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_mk,
        map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
      refine bind_congr fun ⟨out, es'⟩ => ?_
      have hOut :
          (ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).rdec
            (.inr (P, c, c')) (.inr (Option.map smRrEnc out)) = out := by
        rcases out with _ | (_ | ⟨m1, i1, m2⟩) <;> rfl
      rw [eval_ret, pure_bind]
      dsimp only [Function.comp_apply, Prod.map]
      rw [pair_eval, pair_eval,
        show (_root_.ReductionDsl.Expr.inr (.fst (_root_.ReductionDsl.Expr.v0 (O := OOev)))).eval _ =
          Sum.inr (Option.map smRrEnc out) from rfl,
        show (_root_.ReductionDsl.Expr.snd (_root_.ReductionDsl.Expr.v0 (O := OOev))).eval _ = esEnc prngVpEnc prngBucketHsEnc es' from rfl]
      refine congrArg pure (Prod.ext hOut (Prod.ext rfl ?_))
      change (if ((!es.g.win && es'.g.win) && _) = true then some c'.1.1 else winEp) = _
      cases (!es.g.win && es'.g.win) <;> rfl

private theorem simulateQ_splitHandle_vr_eq
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType K]
    (hDefaultE : defaultE = default)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B B_q Δcka qep : ℕ) (tL : Option ℕ) (par gMain : Bool) (t0 : ℕ)
    {VROkStep : ℕ → RS → Prop}
    (hHk : ∀ {m : ℕ}, HooksCAgrees prngBucketHsEnc (prngBucketHBoundedStep L (m + 1))
      (HBoundedPost := prngBucketHBoundedStep L m) (VROk := VROkStep B_q)
      (hooksPRNGBucketSplitPaperC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B (3 + Δcka) qep tL par gMain t0)
      (hooksPRNGBucketSplitGen cka prng fs (3 + Δcka) qep tL par gMain t0))
    (hVRHk : HooksVRInv VROkStep
      (hooksPRNGBucketSplitGen cka prng fs (3 + Δcka) qep tL par gMain t0))
    (heqT : eqT = (· == ·)) (heqM : eqM = (· == ·)) (heqE : eqE = (· == ·)) :
    ∀ {α : Type}
      {oa : OracleComp (unifSpec + _root_.CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) α}
      {qAdv : ℕ},
      oa.IsQueryBoundP
        (isGameQuery (G := _root_.CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) qAdv →
      ∀ (es : EState (VP Γ T (Option RSt) SS RS) M (Header T × E)
          (_root_.CryptoGames.SM.Construction.DeliverForge.PRNGBucketState T RSt K I))
        (winEp : Option ℕ),
        prngBucketHBoundedStep L qAdv es.h → SMEngineInv L B_q qAdv es.g →
          SMVRInv VROkStep B_q qAdv es.g →
        (simulateQ
          (handlerImpl (C := ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E)
            ((redPRNGAuthDFPaperBucketSplitProgGen (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
              (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
              (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
              (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
              (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
              (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
              (sampI := sampI) (sampK := sampK)
              L B Δcka (3 + Δcka) qep fs.maxSkip tL par gMain t0).handle)) oa).run
          (esEnc prngVpEnc prngBucketHsEnc es, winEp) =
          (Prod.map id (Prod.map (esEnc prngVpEnc prngBucketHsEnc) id) <$>
            (simulateQ
              (_root_.CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketMode
                (hooksPRNGBucketSplitGen cka prng fs (3 + Δcka) qep tL par gMain t0)
                (2 + Δcka) qep fs.maxSkip (_root_.CryptoGames.SM.Construction.DeliverForge.bucketAuthCfg Δcka tL par)
                gMain _root_.CryptoGames.SM.Construction.DeliverForge.isHonestHdrPRNGBucket) oa).run (es, winEp)) ∧
        ∀ res ∈ support ((simulateQ
            (_root_.CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketMode
              (hooksPRNGBucketSplitGen cka prng fs (3 + Δcka) qep tL par gMain t0)
              (2 + Δcka) qep fs.maxSkip (_root_.CryptoGames.SM.Construction.DeliverForge.bucketAuthCfg Δcka tL par)
              gMain _root_.CryptoGames.SM.Construction.DeliverForge.isHonestHdrPRNGBucket) oa).run (es, winEp)),
          prngBucketHBoundedStep L 0 res.2.1.h ∧ SMEngineInv L B_q 0 res.2.1.g ∧
            res.2.1.g.b = es.g.b := by
  let hk := hooksPRNGBucketSplitGen cka prng fs (3 + Δcka) qep tL par gMain t0
  let cfg := _root_.CryptoGames.SM.Construction.DeliverForge.bucketAuthCfg (Msg := M) Δcka tL par
  let handleComp : Comp OOev IIev
      [.prod pbEsTyEv (.opt .nat), ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E]
      (.prod (ckaSMRDF KC Γ CCoins T I KR RSt K SS RS M E) (.prod pbEsTyEv (.opt .nat))) :=
    (redPRNGAuthDFPaperBucketSplitProgGen (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B Δcka (3 + Δcka) qep fs.maxSkip tL par gMain t0).handle
  change ∀ {α : Type}
    {oa : OracleComp (unifSpec + _root_.CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) α}
    {qAdv : ℕ},
    oa.IsQueryBoundP
      (isGameQuery (G := _root_.CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) qAdv →
    ∀ (es : EState (VP Γ T (Option RSt) SS RS) M (Header T × E)
        (_root_.CryptoGames.SM.Construction.DeliverForge.PRNGBucketState T RSt K I))
      (winEp : Option ℕ),
      prngBucketHBoundedStep L qAdv es.h → SMEngineInv L B_q qAdv es.g →
        SMVRInv VROkStep B_q qAdv es.g →
      (simulateQ
        (handlerImpl (C := ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E) handleComp) oa).run
        (esEnc prngVpEnc prngBucketHsEnc es, winEp) =
        (Prod.map id (Prod.map (esEnc prngVpEnc prngBucketHsEnc) id) <$>
          (simulateQ
            (_root_.CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketMode hk (2 + Δcka) qep fs.maxSkip cfg
              gMain _root_.CryptoGames.SM.Construction.DeliverForge.isHonestHdrPRNGBucket) oa).run (es, winEp)) ∧
      ∀ res ∈ support ((simulateQ
          (_root_.CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketMode hk (2 + Δcka) qep fs.maxSkip cfg
            gMain _root_.CryptoGames.SM.Construction.DeliverForge.isHonestHdrPRNGBucket) oa).run (es, winEp)),
        prngBucketHBoundedStep L 0 res.2.1.h ∧ SMEngineInv L B_q 0 res.2.1.g ∧
          res.2.1.g.b = es.g.b
  intro α oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro qAdv _ es winEp hHB hInv _
    refine ⟨by simp [simulateQ_pure, Prod.map], ?_⟩
    intro res hmem
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    exact ⟨prngBucketHBoundedStep_mono (Nat.zero_le qAdv) hHB, hInv.mono (Nat.zero_le qAdv), rfl⟩
  | query_bind q mx ih =>
    intro qAdv hq es winEp hHB hInv hVR
    rw [isQueryBoundP_query_bind_iff] at hq
    rw [OracleComp.run_simulateQ_query_bind, OracleComp.run_simulateQ_query_bind]
    cases q with
    | inl n =>
      have hCoinL :
          ((handlerImpl (C := ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E) handleComp)
            (.inl n)).run (esEnc prngVpEnc prngBucketHsEnc es, winEp) =
          (fun u => (u, (esEnc prngVpEnc prngBucketHsEnc es, winEp))) <$>
            query (spec := unifSpec + _root_.CryptoGames.PRFPRNG.spec RSt I K) (.inl n) := by
        simp [handlerImpl, StateT.run_lift, map_eq_bind_pure_comp]
      have hCoinR :
          ((_root_.CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketMode hk (2 + Δcka) qep fs.maxSkip cfg
            gMain _root_.CryptoGames.SM.Construction.DeliverForge.isHonestHdrPRNGBucket) (.inl n)).run (es, winEp) =
          (fun u => (u, (es, winEp))) <$>
            query (spec := unifSpec + _root_.CryptoGames.PRFPRNG.spec RSt I K) (.inl n) := by
        have hw : (!es.g.win && es.g.win) = false := by cases es.g.win <;> rfl
        cases gMain <;>
        · unfold _root_.CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketMode _root_.CryptoGames.SM.Construction.DeliverForge.withWinEpDFMode
            _root_.CryptoGames.SM.Construction.DeliverForge.withWinEpDF
          dsimp only [Bool.false_eq_true, ↓reduceIte, StateT.run_mk]
          change (do
            let x ← (coinsE n).run es
            pure _) = _
          simp only [coinsE, StateT.run_lift, map_eq_bind_pure_comp,
            bind_assoc, pure_bind, hw, Bool.false_eq_true, ↓reduceIte]
          rfl
      rw [hCoinL, hCoinR, bind_map_left, bind_map_left, map_bind]
      refine ⟨bind_congr fun u => (ih u (hq.2 u) es winEp hHB hInv hVR).1, ?_⟩
      intro res hmem
      rw [mem_support_bind_iff] at hmem
      obtain ⟨u, _, hmem⟩ := hmem
      exact (ih u (hq.2 u) es winEp hHB hInv hVR).2 res hmem
    | inr t =>
      have hpos : 0 < qAdv := hq.1.resolve_left (by simp [isGameQuery])
      obtain ⟨m, rfl⟩ : ∃ m, qAdv = m + 1 := ⟨qAdv - 1, by omega⟩
      have hqm : ∀ u, (mx u).IsQueryBoundP
          (isGameQuery (G := _root_.CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) m := by
        intro u; simpa [isGameQuery] using hq.2 u
      have hVRB : ∀ P t₁ v, (es.g.st P).vR t₁ = some v → VROkStep B_q v :=
        fun P t₁ v hv => hVRHk.mono (Nat.sub_le B_q (m + 1)) (hVR P t₁ v hv)
      have hStepEval := rdecDF_splitHandle_eval hDefaultE cka prng fs
        L B Δcka (3 + Δcka) qep fs.maxSkip tL par gMain t0 cfg
        (bucketParPaperAuthCfgEC_agrees Δcka tL par) rfl heqT heqM heqE
        hHk es winEp t hHB hInv.toBoundedEngine hVRB
      have hStep :
          ((handlerImpl (C := ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E) handleComp)
            (.inr t)).run (esEnc prngVpEnc prngBucketHsEnc es, winEp) =
          Prod.map id (Prod.map (esEnc prngVpEnc prngBucketHsEnc) id) <$>
            ((_root_.CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketMode hk (2 + Δcka) qep fs.maxSkip cfg
              gMain _root_.CryptoGames.SM.Construction.DeliverForge.isHonestHdrPRNGBucket) (.inr t)).run (es, winEp) := by
        unfold handlerImpl
        dsimp only [StateT.run_mk, handleComp]
        rw [← hStepEval, map_eq_bind_pure_comp]
        rfl
      rw [hStep, bind_map_left, map_bind]
      refine ⟨OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, es₁, winEp₁⟩ hmem => ?_, ?_⟩
      · have hmemRaw := mem_support_implEDFPaperBucketMode hk (2 + Δcka) qep fs.maxSkip cfg
          gMain (.inr t) es winEp u es₁ winEp₁ hmem
        exact (ih u (hqm u) es₁ winEp₁
          (implEDFPaperBucketRaw_split_bounded cka prng fs L B (2 + Δcka) (3 + Δcka)
            qep fs.maxSkip tL par gMain t0 cfg hHk t es hHB (u, es₁) hmemRaw)
          (_root_.CryptoGames.SM.Engine.implEDFPaperBucketRaw_inv hk cfg es t hInv (u, es₁) hmemRaw)
          (_root_.CryptoGames.SM.Engine.implEDFPaperBucketRaw_vrInv hk hVRHk cfg es t hInv hVR (u, es₁) hmemRaw)).1
      · intro res hmem
        rw [mem_support_bind_iff] at hmem
        obtain ⟨⟨u, es₁, winEp₁⟩, hmem₁, hmem₂⟩ := hmem
        have hmemRaw := mem_support_implEDFPaperBucketMode hk (2 + Δcka) qep fs.maxSkip cfg
          gMain (.inr t) es winEp u es₁ winEp₁ hmem₁
        obtain ⟨hHB₂, hInv₂, hb₂⟩ := (ih u (hqm u) es₁ winEp₁
          (implEDFPaperBucketRaw_split_bounded cka prng fs L B (2 + Δcka) (3 + Δcka)
            qep fs.maxSkip tL par gMain t0 cfg hHk t es hHB (u, es₁) hmemRaw)
          (_root_.CryptoGames.SM.Engine.implEDFPaperBucketRaw_inv hk cfg es t hInv (u, es₁) hmemRaw)
          (_root_.CryptoGames.SM.Engine.implEDFPaperBucketRaw_vrInv hk hVRHk cfg es t hInv hVR (u, es₁) hmemRaw)).2
            res hmem₂
        exact ⟨hHB₂, hInv₂, hb₂.trans (_root_.CryptoGames.SM.Engine.implEDFPaperBucketRaw_b_eq hk cfg es t (u, es₁) hmemRaw)⟩

private theorem redPRNGAuthDFPaperBucketSplitProg_eval_eq_bind_initPRNGBucketRaw_vr
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KC] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B B_q Δcka qep : ℕ) (tL : Option ℕ) (par gMain : Bool) (t0 : ℕ)
    {VROkStep : ℕ → RS → Prop}
    (hInitA : ckaInitA = cka.initA) (hInitB : ckaInitB = cka.initB)
    (hSend : ckaSend = cka.send) (hRecv : ckaReceive = cka.receive) (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender) (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send) (hFsRecv : fsReceive = fs.receive)
    (heqT : eqT = (· == ·)) (heqI : eqI = (· == ·)) (heqM : eqM = (· == ·)) (heqE : eqE = (· == ·))
    (hDefaultE : defaultE = default)
    (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hSampK : sampK = ($ᵗ K : ProbComp K))
    (hVRHk : HooksVRInv VROkStep (_root_.CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t0))
    (hInitR : ∀ k, VROkStep 0 (fs.initReceiver k))
    (hFsB : ∀ rs hdr e rs' i m, VROkStep B_q rs → fs.receive rs hdr e = some (rs', i, m) → i ≤ B)
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : _root_.CryptoGames.SM.Construction.DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) (qAdv : ℕ)
    (hA : _root_.CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF A qAdv) (hqB : qAdv ≤ B_q) :
    ((redPRNGAuthDFPaperBucketSplitProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L B Δcka qep fs.maxSkip tL par gMain t0).eval (fun _ => A) ()) =
      (do
        let es₀ ← initPRNGBucketRaw cka prng fs lam (3 + Δcka) tL par t0 false
        let (_, st) ←
          (simulateQ
            (_root_.CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketMode
              (hooksPRNGBucketSplitGen cka prng fs (3 + Δcka) qep tL par gMain t0)
              (2 + Δcka) qep fs.maxSkip (_root_.CryptoGames.SM.Construction.DeliverForge.bucketAuthCfg Δcka tL par)
              gMain _root_.CryptoGames.SM.Construction.DeliverForge.isHonestHdrPRNGBucket)
            A).run (es₀, none)
        return if gMain then
          _root_.CryptoGames.SM.Construction.DeliverForge.authOutBucketPaperAt (2 + Δcka) tL t0 st
        else
          _root_.CryptoGames.SM.Construction.DeliverForge.authOutBucketPaper (2 + Δcka) tL st) := by
  have hA' : A.IsQueryBoundP
      (isGameQuery (G := _root_.CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) qAdv := by
    refine hA.of_imp (fun x hx => ?_)
    rcases x with _ | _ <;> simp_all [isGameQuery]
  have hHk : ∀ {m : ℕ}, HooksCAgrees prngBucketHsEnc (prngBucketHBoundedStep L (m + 1))
      (HBoundedPost := prngBucketHBoundedStep L m) (VROk := VROkStep B_q)
      (hooksPRNGBucketSplitPaperC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B (3 + Δcka) qep tL par gMain t0)
      (hooksPRNGBucketSplitGen cka prng fs (3 + Δcka) qep tL par gMain t0) :=
    fun {m} => hooksPRNGBucketSplitPaperC_agrees_vr
      (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (prngInit := prngInit)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampI := sampI)
      cka prng fs L B (3 + Δcka) qep tL par gMain t0
      hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend hFsRecv heqT heqI hSampCCoins hSampK
      (fun k => hVRHk.mono (Nat.zero_le B_q) (hInitR k)) hFsB
  have hVRHkSplit := hooksPRNGBucketSplit_vrInv cka prng fs Δcka qep tL par gMain t0 hVRHk hInitR
  have hInit := initPRNGBucketHybridEStateC_eval
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampCCoins := sampCCoins)
    (sampI := sampI)
    cka prng fs hInitA hInitB hPrngUp heqI hFsInitS hFsInitR hSampKC hSampK
    L (3 + Δcka) tL par t0 (_root_.ReductionDsl.Expr.bool (O := OOev) false) (_root_.ReductionDsl.Env.cons (t := (.unit : Ty Sev)) () .nil)
  unfold _root_.ReductionDsl.CostedReduction.eval redPRNGAuthDFPaperBucketSplitProg
    redPRNGAuthDFPaperBucketSplitProgGen _root_.ReductionDsl.CostedReduction.impl
  dsimp only
  rw [eval_bind, hInit]
  simp only [bind_map_left, eval_ret, _root_.ReductionDsl.Expr.eval, _root_.ReductionDsl.Expr.v0, _root_.ReductionDsl.Env.get_cons_zero,
    bind_assoc, pure_bind]
  refine OracleComp.bind_congr_of_forall_mem_support
    (initPRNGBucketRaw cka prng fs lam (3 + Δcka) tL par t0 false) fun es₀ hes₀ => ?_
  have ⟨hInv₀, _, hHB₀⟩ :=
    initPRNGBucketRaw_inv cka prng fs lam (3 + Δcka) tL par t0 false hqB hB1 hBB es₀ hes₀
  have hVR₀ := initPRNGBucketRaw_vrInv (B := B_q) (qAdv := qAdv)
    cka prng fs lam (3 + Δcka) tL par t0 false
    (fun k => hVRHk.mono (Nat.zero_le _) (hInitR k)) es₀ hes₀
  have ⟨hSim, hSimInv⟩ := simulateQ_splitHandle_vr_eq hDefaultE cka prng fs
    L B B_q Δcka qep tL par gMain t0 hHk hVRHkSplit heqT heqM heqE
    hA' es₀ none hHB₀ hInv₀ hVR₀
  refine Eq.trans (congrArg (fun m => m >>= _) hSim) ?_
  rw [bind_map_left]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨b', es', winEp'⟩ hes' => ?_
  obtain ⟨_, hInv', _⟩ := hSimInv (b', es', winEp') hes'
  have hBnd' := hInv'.toBoundedEngine
  dsimp only [Prod.map, id]
  rw [eval_bind_ret, eval_caseOpt]
  rcases winEp' with _ | tWin
  · cases gMain <;> rfl
  · set ρ₂ := _root_.ReductionDsl.Env.cons (t := .nat) tWin
      (_root_.ReductionDsl.Env.cons (t := pbRedEsTyEv) (esEnc prngVpEnc prngBucketHsEnc es', some tWin)
        (_root_.ReductionDsl.Env.cons (t := pbRedEsTyEv) (esEnc prngVpEnc prngBucketHsEnc es', some tWin)
          (_root_.ReductionDsl.Env.cons (t := (.bool : Ty Sev)) b' .nil)))
    change (_root_.ReductionDsl.Comp.ret _).eval ρ₂ = _
    rw [eval_ret]
    congr 1
    have hAuth := cAuthOKE_eval (vpEncFn := vpTblEnc) (O' := OOev) L (2 + Δcka)
      (optNatLit tL) (.var _root_.ReductionDsl.Var.zero) (esG (.fst .v1)) ρ₂ es'.g hBnd'.leaks_le hBnd'.corrs_le rfl
    have htL : (optNatLit (O' := OOev) tL).eval ρ₂ = tL := by cases tL <;> rfl
    have hAb : (esAbort (O' := OOev) (.fst .v1)).eval ρ₂ = es'.abort := rfl
    have hW : (cGsWin (O' := OOev) (esG (.fst .v1))).eval ρ₂ = es'.g.win := rfl
    have hLc : (prngBucketHsLc (O := OOev) (esH (.fst .v1))).eval ρ₂ = es'.h.lc := rfl
    cases gMain
    · unfold _root_.CryptoGames.SM.Construction.DeliverForge.authOutBucketPaper _root_.CryptoGames.SM.Construction.DeliverForge.authOutBucket authOut
      simp only [_root_.ReductionDsl.Expr.eval, hAb, hW, hAuth, htL, Bool.and_true, Bool.and_assoc, ↓reduceIte,
        Bool.false_eq_true]
      rfl
    · unfold _root_.CryptoGames.SM.Construction.DeliverForge.authOutBucketPaperAt _root_.CryptoGames.SM.Construction.DeliverForge.authOutBucketPaper
        _root_.CryptoGames.SM.Construction.DeliverForge.authOutBucket authOut
      simp only [_root_.ReductionDsl.Expr.eval, hAb, hW, hAuth, htL, hLc, ↓reduceIte]
      rcases es'.h.lc with _ | e
      · simp only [Bool.and_assoc]; rfl
      · change (!es'.abort && es'.g.win &&
            authLosingConditionsAvoided (2 + Δcka) tL tWin es'.g && !decide (e < t0)) =
          (!es'.abort && es'.g.win &&
            authLosingConditionsAvoided (2 + Δcka) tL tWin es'.g && decide (t0 ≤ e))
        have hle : (!decide (e < t0)) = decide (t0 ≤ e) := by
          by_cases h : e < t0
          · simp [h]
          · simp [h]; omega
        rw [hle]

private theorem redPRNGAuthDFPaperBucketSplitProg_branch_eval_vr
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B B_q Δcka qep : ℕ) (tL : Option ℕ) (par gMain : Bool) (t0 : ℕ)
    {VROkStep : ℕ → RS → Prop}
    (hInitA : ckaInitA = cka.initA) (hInitB : ckaInitB = cka.initB)
    (hSend : ckaSend = cka.send) (hRecv : ckaReceive = cka.receive) (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender) (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send) (hFsRecv : fsReceive = fs.receive)
    (heqT : eqT = (· == ·)) (heqI : eqI = (· == ·)) (heqM : eqM = (· == ·)) (heqE : eqE = (· == ·))
    (hDefaultE : defaultE = default) (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins)) (hSampK : sampK = ($ᵗ K : ProbComp K))
    (hVRHk : HooksVRInv VROkStep (_root_.CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t0))
    (hInitR : ∀ k, VROkStep 0 (fs.initReceiver k))
    (hFsB : ∀ rs hdr e rs' i m, VROkStep B_q rs → fs.receive rs hdr e = some (rs', i, m) → i ≤ B)
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : _root_.CryptoGames.SM.Construction.DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) (qAdv : ℕ)
    (hA : _root_.CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF A qAdv) (hqB : qAdv ≤ B_q) (b_prng : Bool) :
    _root_.CryptoGames.PRFPRNG.branch prng b_prng
      ((redPRNGAuthDFPaperBucketSplitProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
          (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK)
          L B Δcka qep fs.maxSkip tL par gMain t0).eval (fun _ => A) ()) =
      _root_.CryptoGames.PRFPRNG.branch prng b_prng
        (_root_.CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFPaperBucketSplit cka prng fs lam Δcka qep tL par gMain t0 A) := by
  rw [redPRNGAuthDFPaperBucketSplitProg_eval_eq_bind_initPRNGBucketRaw_vr cka prng fs L B B_q Δcka qep
    tL par gMain t0 hInitA hInitB hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend hFsRecv heqT heqI heqM
    heqE hDefaultE hSampKC hSampCCoins hSampK hVRHk hInitR hFsB hB1 hBB A qAdv hA hqB]
  cases gMain
  · simp only [_root_.CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFPaperBucketSplit, hooksPRNGBucketSplitGen,
      Bool.false_eq_true, ↓reduceIte]
    unfold _root_.CryptoGames.PRFPRNG.branch _root_.CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFPaperBucketForgedHdr
      _root_.CryptoGames.SM.Construction.DeliverForge.engRunDFPaperBucketMode _root_.CryptoGames.SM.Construction.DeliverForge.initPRNGBucketHybrid initPRNGBucketRaw
    refine bind_congr fun kr => ?_
    rw [StateT.run'_eq, StateT.run'_eq]
    refine congrArg (fun m : ProbComp _ => Prod.fst <$> m) ?_
    simp only [StateT.run_bind, StateT.run_lift, simulateQ_bind,
      simulateQ_sampleT_run_bucket, bind_assoc, pure_bind]
    refine bind_congr fun kc => ?_
    refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨step, h₀⟩, sp⟩ hmem => ?_
    obtain ⟨σv, k, rfl⟩ := rootPRNGBucketHybrid_zero_support_some (T := T)
      prng (3 + Δcka) tL par t0 lam kr b_prng step h₀ sp hmem
    simp [StateT.run_pure, simulateQ_pure]; rfl
  · simp only [_root_.CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFPaperBucketSplit, ↓reduceIte]
    unfold _root_.CryptoGames.PRFPRNG.branch _root_.CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFPaperBucketMain
      _root_.CryptoGames.SM.Construction.DeliverForge.engRunDFPaperBucket _root_.CryptoGames.SM.Construction.DeliverForge.initPRNGBucketHybrid initPRNGBucketRaw
    refine bind_congr fun kr => ?_
    rw [StateT.run'_eq, StateT.run'_eq]
    refine congrArg (fun m : ProbComp _ => Prod.fst <$> m) ?_
    simp only [StateT.run_bind, StateT.run_lift, simulateQ_bind,
      simulateQ_sampleT_run_bucket, bind_assoc, pure_bind]
    refine bind_congr fun kc => ?_
    refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨step, h₀⟩, sp⟩ hmem => ?_
    obtain ⟨σv, k, rfl⟩ := rootPRNGBucketHybrid_zero_support_some (T := T)
      prng (3 + Δcka) tL par t0 lam kr b_prng step h₀ sp hmem
    simp [StateT.run_pure, simulateQ_pure]; rfl

theorem redPRNGAuthDFPaperBucketSplitProg_advantage_vr_impl
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B B_q Δcka qep : ℕ) (tL : Option ℕ) (par gMain : Bool) (t0 : ℕ)
    {VROkStep : ℕ → RS → Prop}
    (hInitA : ckaInitA = cka.initA) (hInitB : ckaInitB = cka.initB)
    (hSend : ckaSend = cka.send) (hRecv : ckaReceive = cka.receive) (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender) (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send) (hFsRecv : fsReceive = fs.receive)
    (heqT : eqT = (· == ·)) (heqI : eqI = (· == ·)) (heqM : eqM = (· == ·)) (heqE : eqE = (· == ·))
    (hDefaultE : defaultE = default)
    (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hSampK : sampK = ($ᵗ K : ProbComp K))
    (hVRHk : HooksVRInv VROkStep (_root_.CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t0))
    (hInitR : ∀ k, VROkStep 0 (fs.initReceiver k))
    (hFsB : ∀ rs hdr e rs' i m, VROkStep B_q rs → fs.receive rs hdr e = some (rs', i, m) → i ≤ B)
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : _root_.CryptoGames.SM.Construction.DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) (qAdv : ℕ)
    (hA : _root_.CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF A qAdv) (hqB : qAdv ≤ B_q) :
    _root_.CryptoGames.PRFPRNG.advantage prng
      ((redPRNGAuthDFPaperBucketSplitProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
          (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK)
          L B Δcka qep fs.maxSkip tL par gMain t0).eval (fun _ => A) ()) =
      _root_.CryptoGames.PRFPRNG.advantage prng
        (_root_.CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFPaperBucketSplit cka prng fs lam Δcka qep tL par gMain t0 A) := by
  have hGame : _root_.CryptoGames.PRFPRNG.game prng
      ((redPRNGAuthDFPaperBucketSplitProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
          (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK)
          L B Δcka qep fs.maxSkip tL par gMain t0).eval (fun _ => A) ()) =
      _root_.CryptoGames.PRFPRNG.game prng
        (_root_.CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFPaperBucketSplit cka prng fs lam Δcka qep tL par gMain t0 A) := by
    unfold _root_.CryptoGames.PRFPRNG.game
    refine bind_congr fun b_prng => ?_
    have hBr := redPRNGAuthDFPaperBucketSplitProg_branch_eval_vr
      (prngInit := prngInit) (lam := lam) (sampKR := sampKR) (sampI := sampI)
      cka prng fs L B B_q Δcka qep tL par gMain t0
      hInitA hInitB hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend hFsRecv
      heqT heqI heqM heqE hDefaultE hSampKC hSampCCoins hSampK
      hVRHk hInitR hFsB hB1 hBB A qAdv hA hqB b_prng
    unfold _root_.CryptoGames.PRFPRNG.branch at hBr
    simp only [← bind_assoc]
    exact congrArg (· >>= fun b' => pure (b_prng == b')) hBr
  unfold _root_.CryptoGames.PRFPRNG.advantage
  rw [hGame]

end HooksPRNGBucketEval

end

end Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGSplitEval
