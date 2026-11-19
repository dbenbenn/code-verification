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
import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.ProgramLogic.Unary.HoareTriple

set_option autoImplicit false

public section

open OracleSpec OracleComp

namespace CryptoGames.SM.Construction

open ReductionDsl
open scoped Computational.Proofs.ReductionDsl.Notation
open CryptoGames.CKA
open CryptoGames.PRFPRNG
open CryptoGames.FSAEAD
open CryptoGames.SM
open CryptoGames.SM.Engine

section HooksPRNGBucketEvalHooks

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}

local notation "Sevh" => prngSig KC Γ CCoins T I KR RSt K SS RS M E

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

local notation "OOevh" =>
  prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE

local notation "IIevh" =>
  prngIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK

local notation "pbHsTyEvh" => @prngBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "pbVpTyEvh" => @prngVpTy KC Γ CCoins T I KR RSt K SS RS M E

private theorem postLeakBucketE_eval (tL : Option ℕ) {Γ'}
    (ctxE : Expr OOevh Γ' (cGsTy pbVpTyEvh)) (ρ : Env Γ')
    (ctx : Ctx Γ T (Option RSt) SS RS M E)
    (hctx : ctxE.eval ρ = cGsEnc prngVpEnc ctx) :
    (postLeakBucketE tL ctxE).eval ρ = DeliverForge.postLeak tL ctx := by
  unfold postLeakBucketE DeliverForge.postLeak
  have hTL : (cGsTL ctxE).eval ρ = ctx.tL := by
    simp [cGsTL, cGsEnc, Expr.eval, hctx]
  simp only [Expr.eval, hTL]
  rcases ctx.tL with _ | cur
  · rfl
  · have hOpt : (Engine.optNatLit (O' := OOevh) tL).eval (Env.cons (t := (.nat : Ty Sevh)) cur ρ) = tL := by
      cases tL <;> rfl
    simp [ltOptE_eval, hOpt, Expr.eval, Expr.v0]

private theorem resolveCorrRootE_eval {Γ'}
    (hE : Expr OOevh Γ' pbHsTyEvh) (epE : Expr OOevh Γ' .nat)
    (σvE : Expr OOevh Γ' (.opt (.base .sig))) (ρ : Env Γ')
    (h : DeliverForge.PRNGBucketState T RSt K I)
    (hh : hE.eval ρ = prngBucketHsEnc h) :
    (resolveCorrRootE hE epE σvE).eval ρ =
      DeliverForge.resolveCorrRoot h (epE.eval ρ) (σvE.eval ρ) := by
  unfold resolveCorrRootE DeliverForge.resolveCorrRoot
  simp only [Expr.eval, hh, prngBucketHsEnc, prngBucketHsCorrRoot, Expr.v0]
  rcases σvE.eval ρ with _ | σ
  · rcases h.corrRoot with _ | ⟨eC, σC⟩
    · rfl
    · dsimp only [Env.get_cons_zero, Env.get_cons_succ]
      by_cases hEq : epE.eval ρ = eC <;> simp [hEq, Expr.eval, Expr.v1]
  · rfl

theorem lookupPRNGBucketFC_eval [DecidableEq I] [SampleableType K]
    (heqI : eqI = (· == ·))
    (hSampK : sampK = ($ᵗ K : ProbComp K))
    (L : ℕ) {Γ'} (hE : Expr OOevh Γ' pbHsTyEvh) (tE : Expr OOevh Γ' .nat)
    (ikE : Expr OOevh Γ' (.base .i))
    (ρ : Env Γ') (h : DeliverForge.PRNGBucketState T RSt K I)
    (hh : hE.eval ρ = prngBucketHsEnc h) (hL : (h.fTable (tE.eval ρ)).length ≤ L) :
    (lookupPRNGBucketFC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L hE tE ikE).eval ρ =
      Prod.map id prngBucketHsEnc <$>
        (DeliverForge.lookupPRNGBucketF (T := T) (Sig := RSt) (K := K) (I := I)
          (tE.eval ρ) (ikE.eval ρ)).run h ∧
    ∀ res ∈ support ((DeliverForge.lookupPRNGBucketF (T := T) (Sig := RSt) (K := K) (I := I)
        (tE.eval ρ) (ikE.eval ρ)).run h),
      (∀ τ, (res.2.fTable τ).length ≤ (h.fTable τ).length + 1) ∧
      res.2.cache = h.cache := by
  unfold lookupPRNGBucketFC DeliverForge.lookupPRNGBucketF
  rw [eval_bind_ret]
  set t0 : ℕ := tE.eval ρ
  set Ik : I := ikE.eval ρ
  have h0 : (Expr.pair hE (Expr.pair tE ikE)).eval ρ = (prngBucketHsEnc h, t0, Ik) := by
    simp [Expr.eval, hh, t0, Ik]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod pbHsTyEvh (.prod .nat (.base CKASort.i)))
    (prngBucketHsEnc h, t0, Ik) ρ
  have hTbl : (tableLookupE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      L (.tget (prngBucketHsFTbl (.fst .v0)) (.fst (.snd .v0))) (.snd (.snd .v0))).eval ρ₁ =
      (h.fTable t0).lookup Ik := by
    rw [tableLookupE_eval heqI L (.tget (prngBucketHsFTbl (.fst .v0)) (.fst (.snd .v0)))
      (.snd (.snd .v0)) ρ₁
      (by simpa [ρ₁, prngBucketHsFTbl, prngBucketHsEnc, Expr.eval, Expr.v0] using hL)]
    rfl
  rw [eval_caseOpt, hTbl]
  rcases hlk : (h.fTable t0).lookup Ik with _ | k
  · refine ⟨?_, ?_⟩
    · simp only [hlk, eval_bind, StateT.run_bind, StateT.run_get,
        StateT.run_lift, StateT.run_modify, StateT.run_pure, pure_bind, bind_assoc, map_bind]
      have hSamp : (@Comp.sample _ _ _ OOevh IIevh _ CKASamp.k .unit).eval ρ₁ =
          (sampleT K : TComp (PRFPRNG.spec RSt I K) K) := by
        simp only [Comp.eval, prngIface, prngSamplers, ckaSamplers, hSampK, sampleT]
        exact liftP_eq_liftM IIevh (fun _ => rfl) ($ᵗ K)
      rw [hSamp]
      refine bind_congr fun k' => ?_
      simp [ρ₁, Comp.eval, prngBucketHsSetFTblAt, prngBucketHsCache, prngBucketHsFTbl,
        prngBucketHsCorrRoot, prngBucketHsLc, prngBucketHsEnc, Prod.map, Expr.eval, Expr.v0, Expr.v1]
      ext j
      by_cases hj : j = t0 <;> simp [hj]
    · intro res hmem
      simp only [hlk, StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_modify,
        StateT.run_pure, pure_bind, bind_assoc, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hmem
      obtain ⟨k', _, rfl⟩ := hmem
      refine ⟨fun τ => ?_, rfl⟩
      by_cases hτ : τ = t0
      · subst hτ; simp [Function.update_self]
      · simp [Function.update_of_ne hτ]
  · refine ⟨?_, ?_⟩
    · simp [ρ₁, hlk, Comp.eval, StateT.run_bind, StateT.run_get,
        StateT.run_pure, pure_bind, Prod.map, Expr.eval, Expr.v0, Expr.v1]
    · intro res hmem
      simp only [hlk, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff] at hmem
      subst hmem
      exact ⟨fun _ => Nat.le_add_right _ _, rfl⟩

theorem validGuessBucketParPaperE_eval {S' : Sig} {O' : Ops S'}
    (Δbucket : ℕ) (tL : Option ℕ) (par : Bool) {Γ'} (tE : Expr O' Γ' .nat) (ρ : Env Γ') :
    (validGuessBucketParPaperE Δbucket tL par tE).eval ρ =
      (lastLeakGuessAdmissible Δbucket tL (tE.eval ρ) &&
        (DeliverForge.partyPar (Party.senderOf (tE.eval ρ)) == par)) := by
  have hOpt : (Engine.optNatLit (O' := O') (Γ' := Γ') tL).eval ρ = tL := by
    cases tL <;> rfl
  simp only [validGuessBucketParPaperE, Expr.eval, validGuessE_eval, senderOfE_eval, hOpt]
  congr 1
  cases Party.senderOf (tE.eval ρ) <;> cases par <;> rfl

theorem bucketParPaperAuthCfgEC_agrees (Δcka : ℕ) (tL : Option ℕ) (par : Bool) :
    ConfigECAgrees (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (bucketParPaperAuthCfgEC (3 + Δcka) tL par)
      (DeliverForge.bucketAuthCfg Δcka tL par) where
  deliverWin_eq := rfl
  injectFull_eq t' ρ := by
    simp [bucketParPaperAuthCfgEC, DeliverForge.bucketAuthCfg, DeliverForge.inStage2Bucket,
      validGuessBucketParPaperE_eval]
  challOK_eq _ _ := rfl
  challMsg_eq _ _ _ _ _ := by
    simp [bucketParPaperAuthCfgEC, DeliverForge.bucketAuthCfg, Expr.eval]

theorem rootPRNGBucketHybrid_fTable_len [DecidableEq I] [SampleableType K]
    (prng : PRFPRNG KR RSt I K) (Δbucket : ℕ) (tL : Option ℕ) (par : Bool) (t t0 : ℕ)
    (pl : Bool) (Ik : I) (σv0 : Option RSt)
    (h : DeliverForge.PRNGBucketState T RSt K I) :
    ∀ res ∈ support ((DeliverForge.rootPRNGBucketHybrid (T := T) prng Δbucket tL par t t0 pl Ik σv0).run h),
      (∀ τ, (res.2.fTable τ).length ≤ (h.fTable τ).length + 1) ∧ res.2.cache = h.cache := by
  intro res hmem
  unfold DeliverForge.rootPRNGBucketHybrid at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  split_ifs at hmem
  · rcases hR : DeliverForge.resolveCorrRoot h (t0 - 1) σv0 with _ | σ <;>
    · simp only [hR, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact ⟨fun _ => Nat.le_add_right _ _, rfl⟩
  · rcases hR : DeliverForge.resolveCorrRoot h (t0 - 1) σv0 with _ | σ
    · simp only [hR, StateT.run_bind, DeliverForge.liftPBucket, StateT.run_lift, bind_assoc,
        pure_bind, mem_support_bind_iff] at hmem
      obtain ⟨σ?, _, hmem⟩ := hmem
      rcases σ? with _ | σOut
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; exact ⟨fun _ => Nat.le_add_right _ _, rfl⟩
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; exact ⟨fun _ => Nat.le_add_right _ _, rfl⟩
    · simp only [hR, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact ⟨fun _ => Nat.le_add_right _ _, rfl⟩
  · simp only [StateT.run_bind, DeliverForge.liftPBucket, StateT.run_lift, bind_assoc, pure_bind,
      mem_support_bind_iff] at hmem
    obtain ⟨k?, _, hmem⟩ := hmem
    rcases k? with _ | kOut
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact ⟨fun _ => Nat.le_add_right _ _, rfl⟩
    · simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨σ?, _, hmem⟩ := hmem
      rcases σ? with _ | σOut <;>
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; exact ⟨fun _ => Nat.le_add_right _ _, rfl⟩
  · simp only [StateT.run_bind, DeliverForge.liftPBucket, StateT.run_lift, bind_assoc, pure_bind,
      mem_support_bind_iff] at hmem
    obtain ⟨ans, _, hmem⟩ := hmem
    rcases ans with _ | ⟨σOut, kOut⟩ <;>
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact ⟨fun _ => Nat.le_add_right _ _, rfl⟩
  · simp only [StateT.run_bind, DeliverForge.liftPBucket, StateT.run_lift, bind_assoc, pure_bind,
      mem_support_bind_iff] at hmem
    obtain ⟨k?, _, hmem⟩ := hmem
    rcases k? with _ | kOut
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact ⟨fun _ => Nat.le_add_right _ _, rfl⟩
    · simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨σ?, _, hmem⟩ := hmem
      rcases σ? with _ | σOut <;>
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; exact ⟨fun _ => Nat.le_add_right _ _, rfl⟩
  · simp only [StateT.run_bind, DeliverForge.liftPBucket, StateT.run_lift, bind_assoc, pure_bind,
      mem_support_bind_iff] at hmem
    obtain ⟨k?, _, hmem⟩ := hmem
    rcases k? with _ | kProc
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact ⟨fun _ => Nat.le_add_right _ _, rfl⟩
    · simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hmem
      obtain ⟨kRand, _, rfl⟩ := hmem
      exact ⟨fun _ => Nat.le_add_right _ _, rfl⟩
  · simp only [StateT.run_bind, DeliverForge.liftPBucket, StateT.run_lift, bind_assoc, pure_bind,
      mem_support_bind_iff] at hmem
    obtain ⟨k?, _, hmem⟩ := hmem
    rcases k? with _ | kProc
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact ⟨fun _ => Nat.le_add_right _ _, rfl⟩
    · simp only [StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨kRand, h1⟩, hmemLk, hmem⟩ := hmem
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem
      unfold DeliverForge.lookupPRNGBucketF at hmemLk
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmemLk
      rcases hlk : (h.fTable t0).lookup Ik with _ | k
      · simp only [hlk, StateT.run_bind, StateT.run_lift, StateT.run_modify, StateT.run_pure,
          pure_bind, bind_assoc, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hmemLk
        obtain ⟨k', _, hEq⟩ := hmemLk
        rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
        refine ⟨fun τ => ?_, rfl⟩
        by_cases hτ : τ = t0
        · subst hτ; simp [Function.update_self]
        · simp [Function.update_of_ne hτ]
      · simp only [hlk, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmemLk
        rcases hmemLk with ⟨_, rfl⟩
        exact ⟨fun _ => Nat.le_add_right _ _, rfl⟩
  · simp only [StateT.run_bind, DeliverForge.liftPBucket, StateT.run_lift, bind_assoc, pure_bind,
      mem_support_bind_iff] at hmem
    obtain ⟨k?, _, hmem⟩ := hmem
    rcases k? with _ | kOut <;>
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact ⟨fun _ => Nat.le_add_right _ _, rfl⟩
  · simp only [StateT.run_bind, DeliverForge.liftPBucket, StateT.run_lift, bind_assoc, pure_bind,
      mem_support_bind_iff] at hmem
    obtain ⟨k?, _, hmem⟩ := hmem
    rcases k? with _ | kOut
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact ⟨fun _ => Nat.le_add_right _ _, rfl⟩
    · simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨σ?, _, hmem⟩ := hmem
      rcases σ? with _ | σOut <;>
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; exact ⟨fun _ => Nat.le_add_right _ _, rfl⟩

theorem rootPRNGBucketHybridC_eval [DecidableEq I] [SampleableType K]
    (prng : PRFPRNG KR RSt I K)
    (hPrngUp : prngUp = prng.up)
    (heqI : eqI = (· == ·))
    (hSampK : sampK = ($ᵗ K : ProbComp K))
    (L Δbucket : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) {Γ'}
    (hE : Expr OOevh Γ' pbHsTyEvh)
    (tE : Expr OOevh Γ' .nat)
    (plE : Expr OOevh Γ' .bool)
    (ikE : Expr OOevh Γ' (.base .i))
    (σvE : Expr OOevh Γ' (.opt (.base .sig)))
    (ρ : Env Γ') (h : DeliverForge.PRNGBucketState T RSt K I)
    (hh : hE.eval ρ = prngBucketHsEnc h)
    (hL : (h.fTable (tE.eval ρ)).length ≤ L) :
    (rootPRNGBucketHybridC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L Δbucket tL par t hE tE plE ikE σvE).eval ρ =
      Prod.map id prngBucketHsEnc <$>
        (DeliverForge.rootPRNGBucketHybrid (T := T) prng Δbucket tL par t
          (tE.eval ρ) (plE.eval ρ) (ikE.eval ρ) (σvE.eval ρ)).run h ∧
    ∀ res ∈ support ((DeliverForge.rootPRNGBucketHybrid (T := T) prng Δbucket tL par t
        (tE.eval ρ) (plE.eval ρ) (ikE.eval ρ) (σvE.eval ρ)).run h),
      (∀ τ, (res.2.fTable τ).length ≤ (h.fTable τ).length + 1) ∧
      res.2.cache = h.cache := by
  refine ⟨?_, rootPRNGBucketHybrid_fTable_len prng Δbucket tL par t (tE.eval ρ) (plE.eval ρ) (ikE.eval ρ) (σvE.eval ρ) h⟩
  unfold rootPRNGBucketHybridC DeliverForge.rootPRNGBucketHybrid
  dsimp only
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [eval_bind_ret]
  set tH : ℕ := healEpoch tL
  set t0 : ℕ := tE.eval ρ
  set pl0 : Bool := plE.eval ρ
  set Ik : I := ikE.eval ρ
  set σv0 : Option RSt := σvE.eval ρ
  have h0 : (Expr.pair hE (.pair tE (.pair plE (.pair ikE σvE)))).eval ρ =
      (prngBucketHsEnc h, t0, pl0, Ik, σv0) := by
    simp [Expr.eval, hh, t0, pl0, Ik, σv0]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := (.prod pbHsTyEvh (.prod .nat (.prod .bool (.prod (.base .i) (.opt (.base .sig))))) : Ty Sevh))
    (prngBucketHsEnc h, t0, pl0, Ik, σv0) ρ
  have hRes :
      (resolveCorrRootE (O := OOevh) (.fst .v0) (.sub (.fst (.snd .v0)) (.nat 1))
        (.snd (.snd (.snd (.snd .v0))))).eval ρ₁ =
      DeliverForge.resolveCorrRoot h (t0 - 1) σv0 :=
    resolveCorrRootE_eval _ _ _ ρ₁ h rfl
  rw [eval_ite]
  have hlt1 : (Expr.lt (.nat t) (.fst (.snd (Expr.v0 (O := OOevh))))).eval ρ₁ = decide (t < t0) := rfl
  rw [hlt1]
  by_cases hgt : t < t0
  · simp only [hgt, decide_true, ↓reduceIte, eval_caseOpt, hRes]
    rcases DeliverForge.resolveCorrRoot h (t0 - 1) σv0 with _ | σ
    · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
    · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, hPrngUp,
        Expr.eval, Expr.v0, Expr.v1]
  · simp only [hgt, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [eval_ite]
    have hcondPl :
        (orE (O' := OOevh) (.fst (.snd (.snd .v0)))
          (isSomeE (prngBucketHsCorrRoot (.fst .v0)))).eval ρ₁ =
        (pl0 || h.corrRoot.isSome) := by
      dsimp only [ρ₁, orE, isSomeE, prngBucketHsCorrRoot, prngBucketHsEnc, Expr.eval, Expr.v0]
      cases pl0 <;> cases h.corrRoot <;> rfl
    rw [hcondPl]
    by_cases hpl : (pl0 || h.corrRoot.isSome) = true
    · simp only [hpl, ↓reduceIte, eval_caseOpt, hRes]
      rcases DeliverForge.resolveCorrRoot h (t0 - 1) σv0 with _ | σ
      · simp only [eval_bind, query_prngCorr_eval, DeliverForge.liftPBucket,
          StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind]
        refine bind_congr fun σ? => ?_
        rcases σ? with _ | σOut
        · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v1]
        · simp [ρ₁, Comp.eval, StateT.run_modify,
            prngBucketHsSetCorrRoot, prngBucketHsCache, prngBucketHsFTbl, prngBucketHsLc,
            prngBucketHsEnc, Prod.map, hPrngUp, Expr.eval, Expr.v0, Expr.v2]
      · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, hPrngUp,
          Expr.eval, Expr.v0, Expr.v1]
    · simp only [hpl, Bool.false_eq_true, ↓reduceIte]
      rw [eval_ite]
      have heq1 : (Expr.eqN (.fst (.snd (Expr.v0 (O := OOevh)))) (.nat t)).eval ρ₁ =
          decide (t0 = t) := rfl
      rw [heq1]
      by_cases hts : t0 = t
      · have htsIf : (t0 = t) ↔ True := by simp [hts]
        simp only [htsIf, decide_true, ↓reduceIte]
        rw [eval_ite]
        have hcond2 : (Expr.and (.bool tL.isSome)
            (.eqN (.fst (.snd (Expr.v0 (O := OOevh)))) (.nat tH))).eval ρ₁ =
            (tL.isSome && decide (t0 = tH)) := rfl
        rw [hcond2]
        by_cases htH : (tL.isSome && decide (t0 = tH)) = true
        · simp only [htH, ↓reduceIte, eval_bind, query_challPrng_eval,
            DeliverForge.liftPBucket, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind]
          refine bind_congr fun k? => ?_
          rcases k? with _ | kOut
          · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v1]
          · simp only [eval_caseOpt, Expr.eval, Expr.v0, Env.get_cons_zero, eval_bind,
              query_prngCorr_eval, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind]
            refine bind_congr fun σ? => ?_
            rcases σ? with _ | σOut
            · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v3]
            · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v2, Expr.v4]
        · simp only [htH, Bool.false_eq_true, ↓reduceIte]
          rw [eval_ite]
          have hvg1 :
              (validGuessBucketParPaperE (O' := OOevh) Δbucket tL par (.fst (.snd .v0))).eval ρ₁ =
              DeliverForge.inStage2BucketGen Δbucket tL par t0 := by
            simp [ρ₁, validGuessBucketParPaperE_eval, DeliverForge.inStage2BucketGen, Expr.eval, Expr.v0]
          rw [hvg1]
          by_cases hbg1 : DeliverForge.inStage2BucketGen Δbucket tL par t0 = true
          · simp only [hbg1, ↓reduceIte, eval_bind, query_challPrf_eval,
              DeliverForge.liftPBucket, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind]
            have hIk : (Expr.fst (.snd (.snd (.snd (Expr.v0 (O := OOevh)))))).eval ρ₁ = Ik := rfl
            rw [hIk]
            refine bind_congr fun ans => ?_
            rcases ans with _ | ⟨σOut, kOut⟩
            · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v1]
            · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v2]
          · simp only [hbg1, Bool.false_eq_true, ↓reduceIte]
            unfold prngProcessCorrC
            simp only [eval_bind, query_process_eval, DeliverForge.liftPBucket,
              StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind]
            have hSomeIk : (Expr.some (.fst (.snd (.snd (.snd (Expr.v0 (O := OOevh))))))).eval ρ₁ = some Ik := rfl
            rw [hSomeIk]
            refine bind_congr fun k? => ?_
            rcases k? with _ | kOut
            · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v1]
            · simp only [eval_caseOpt, eval_bind, query_prngCorr_eval,
                StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind,
                Expr.eval, Expr.v0, Env.get_cons_zero]
              refine bind_congr fun σ? => ?_
              rcases σ? with _ | σOut
              · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v1]
              · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v1, Expr.v2]
      · simp only [hts, decide_false, Bool.false_eq_true, ↓reduceIte]
        rw [eval_ite]
        have hcond3 : (Expr.not (.lt (.fst (.snd (Expr.v0 (O := OOevh)))) (.nat tH))).eval ρ₁ =
            (!decide (t0 < tH)) := rfl
        rw [hcond3]
        by_cases hgeH : (!decide (t0 < tH)) = true
        · simp only [hgeH, ↓reduceIte]
          rw [eval_ite]
          have hcond4 : (Expr.and (.bool tL.isSome)
              (.eqN (.fst (.snd (Expr.v0 (O := OOevh)))) (.nat tH))).eval ρ₁ =
              (tL.isSome && decide (t0 = tH)) := rfl
          rw [hcond4]
          by_cases htH : (tL.isSome && decide (t0 = tH)) = true
          · simp only [htH, ↓reduceIte, eval_bind, query_process_eval,
              DeliverForge.liftPBucket, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind]
            have hNone : (Expr.none (O := OOevh) (t := .base .i)).eval ρ₁ = none := rfl
            rw [hNone]
            refine bind_congr fun k? => ?_
            rcases k? with _ | kProc
            · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v1]
            · simp only [eval_caseOpt, Expr.eval, Expr.v0, Env.get_cons_zero, eval_bind,
                StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind]
              set ρ₂ := Env.cons (t := (.base .k : Ty Sevh)) kProc
                (Env.cons (t := (.opt (.base .k) : Ty Sevh)) (some kProc) ρ₁)
              have hSamp : (@Comp.sample _ _ _ OOevh IIevh _ CKASamp.k .unit).eval ρ₂ =
                  (sampleT K : TComp (PRFPRNG.spec RSt I K) K) := by
                simp only [Comp.eval, prngIface, prngSamplers, ckaSamplers, hSampK, sampleT]
                exact liftP_eq_liftM IIevh (fun _ => rfl) ($ᵗ K)
              rw [hSamp]
              refine bind_congr fun kRand => ?_
              simp [ρ₂, ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v3]
          · simp only [htH, Bool.false_eq_true, ↓reduceIte]
            rw [eval_ite]
            have hvg2 :
                (validGuessBucketParPaperE (O' := OOevh) Δbucket tL par (.fst (.snd .v0))).eval ρ₁ =
                DeliverForge.inStage2BucketGen Δbucket tL par t0 := by
              simp [ρ₁, validGuessBucketParPaperE_eval, DeliverForge.inStage2BucketGen, Expr.eval, Expr.v0]
            rw [hvg2]
            by_cases hbg2 : DeliverForge.inStage2BucketGen Δbucket tL par t0 = true
            · simp only [hbg2, ↓reduceIte, eval_bind, query_process_eval,
                DeliverForge.liftPBucket, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind]
              have hSomeIk : (Expr.some (.fst (.snd (.snd (.snd (Expr.v0 (O := OOevh))))))).eval ρ₁ = some Ik := rfl
              rw [hSomeIk]
              refine bind_congr fun k? => ?_
              rcases k? with _ | kProc
              · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v1]
              · simp only [eval_caseOpt, Expr.eval, Expr.v0, Env.get_cons_zero, eval_bind,
                  StateT.run_bind, map_bind]
                set ρ₂ := Env.cons (t := (.base .k : Ty Sevh)) kProc
                  (Env.cons (t := (.opt (.base .k) : Ty Sevh)) (some kProc) ρ₁)
                have ⟨hLk, _⟩ := lookupPRNGBucketFC_eval
                  (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
                  (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
                  (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
                  (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT)
                  (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
                  (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
                  (sampI := sampI) (sampK := sampK) (T := T) (RSt := RSt) heqI hSampK L
                  (.fst .v2) (.fst (.snd .v2)) (.fst (.snd (.snd (.snd .v2)))) ρ₂ h rfl
                  (by simpa [ρ₂, ρ₁, Expr.eval, Expr.v2] using hL)
                have ht0_eq : (Expr.fst (.snd (Expr.v2 (O := OOevh)))).eval ρ₂ = t0 := rfl
                have hIk_eq : (Expr.fst (.snd (.snd (.snd (Expr.v2 (O := OOevh)))))).eval ρ₂ = Ik := rfl
                rw [ht0_eq, hIk_eq] at hLk
                rw [hLk, bind_map_left]
                refine bind_congr fun ⟨kRand, h1⟩ => ?_
                simp [ρ₂, ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval]
            · simp only [hbg2, Bool.false_eq_true, ↓reduceIte, eval_bind, query_process_eval,
                DeliverForge.liftPBucket, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind]
              have hSomeIk : (Expr.some (.fst (.snd (.snd (.snd (Expr.v0 (O := OOevh))))))).eval ρ₁ = some Ik := rfl
              rw [hSomeIk]
              refine bind_congr fun k? => ?_
              rcases k? with _ | kOut
              · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v1]
              · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v2]
        · simp only [hgeH, Bool.false_eq_true, ↓reduceIte]
          unfold prngProcessCorrC
          simp only [eval_bind, query_process_eval, DeliverForge.liftPBucket,
            StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind]
          have hSomeIk : (Expr.some (.fst (.snd (.snd (.snd (Expr.v0 (O := OOevh))))))).eval ρ₁ = some Ik := rfl
          rw [hSomeIk]
          refine bind_congr fun k? => ?_
          rcases k? with _ | kOut
          · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v1]
          · simp only [eval_caseOpt, eval_bind, query_prngCorr_eval,
              StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind,
              Expr.eval, Expr.v0, Env.get_cons_zero]
            refine bind_congr fun σ? => ?_
            rcases σ? with _ | σOut
            · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v1]
            · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v1, Expr.v2]

private theorem startSend_run_eq [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (ctx : Ctx Γ T (Option RSt) SS RS M E) (P : Party)
    (t0 : ℕ) (γ0 : Γ) (σv0 : Option RSt) (r0 : Option CCoins)
    (h : DeliverForge.PRNGBucketState T RSt K I) :
    ((DeliverForge.hooksPRNGBucketHybridGen cka prng fs Δbucket qep tL par t).startSend ctx P
      t0 γ0 σv0 r0).run h =
    ((match r0 with
        | some c => pure c
        | none => (sampleT CCoins : TComp (PRFPRNG.spec RSt I K) CCoins)) >>= fun coins =>
      (do
        let x ← DeliverForge.rootPRNGBucketHybrid (T := T) prng Δbucket tL par t t0
          (DeliverForge.postLeak tL ctx) (cka.send γ0 coins).2.2 σv0
        match x with
        | none => return none
        | some (σ', kVal) =>
          modify fun (s : DeliverForge.PRNGBucketState T RSt K I) =>
            { s with cache := Function.update s.cache t0 (some ((cka.send γ0 coins).2.1, σ', kVal)) }
          return some ((cka.send γ0 coins).1, (cka.send γ0 coins).2.1, σ',
            fs.initSender kVal)).run
        (if (DeliverForge.postLeak tL ctx && h.lc.isNone && decide (healEpoch tL < t0)) = true then
          { h with lc := some (t0 - 1) } else h)) := by
  dsimp only [DeliverForge.hooksPRNGBucketHybridGen]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hcond : (DeliverForge.postLeak tL ctx && h.lc.isNone && decide (healEpoch tL < t0)) = true <;>
    rcases r0 with _ | c <;>
    simp only [hcond, ↓reduceIte, Bool.false_eq_true, StateT.run_modify,
      StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind] <;>
    rfl

theorem prngBucketStartSend_fTable_len [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (ctx : Ctx Γ T (Option RSt) SS RS M E) (P : Party)
    (t0 : ℕ) (γ0 : Γ) (σv0 : Option RSt) (r0 : Option CCoins)
    (h : DeliverForge.PRNGBucketState T RSt K I) :
    ∀ res ∈ support (((DeliverForge.hooksPRNGBucketHybridGen cka prng fs Δbucket qep tL par t).startSend
        ctx P t0 γ0 σv0 r0).run h),
      ∀ τ, (res.2.fTable τ).length ≤ (h.fTable τ).length + 1 := by
  rw [startSend_run_eq]
  set hLc : DeliverForge.PRNGBucketState T RSt K I :=
    if (DeliverForge.postLeak tL ctx && h.lc.isNone && decide (healEpoch tL < t0)) = true then
      { h with lc := some (t0 - 1) } else h
  intro res hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨coins, _, hmem⟩ := hmem
  simp only [StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨step, h1⟩, hmemRt, hmem⟩ := hmem
  have ⟨hLen1, _⟩ := rootPRNGBucketHybrid_fTable_len prng Δbucket tL par t t0
    (DeliverForge.postLeak tL ctx) (cka.send γ0 coins).2.2 σv0 hLc (step, h1) hmemRt
  have hFT : hLc.fTable = h.fTable := by dsimp only [hLc]; split_ifs <;> rfl
  rcases step with _ | ⟨σ', kVal⟩
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; intro τ; simpa [hFT] using hLen1 τ
  · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; intro τ; simpa [hFT] using hLen1 τ

theorem prngBucketStartSendC_eval [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (hSend : ckaSend = cka.send) (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender) (heqI : eqI = (· == ·))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hSampK : sampK = ($ᵗ K : ProbComp K))
    (L Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    {Γ'} (hE : Expr OOevh Γ' pbHsTyEvh) (ctxE : Expr OOevh Γ' (cGsTy pbVpTyEvh))
    (pE : Expr OOevh Γ' .bool) (tE : Expr OOevh Γ' .nat)
    (γE : Expr OOevh Γ' (.base .γ)) (σvE : Expr OOevh Γ' (.opt (.base .sig)))
    (rE : Expr OOevh Γ' (.opt (.base .ccoins))) (ρ : Env Γ')
    (h : DeliverForge.PRNGBucketState T RSt K I)
    (ctx : Ctx Γ T (Option RSt) SS RS M E) (P : Party)
    (hHB : ∀ τ, (h.fTable τ).length ≤ L)
    (hh : hE.eval ρ = prngBucketHsEnc h)
    (hctx : ctxE.eval ρ = cGsEnc prngVpEnc ctx) :
    (prngBucketStartSendC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L Δbucket tL par t hE ctxE pE tE γE σvE rE).eval ρ =
      Prod.map id prngBucketHsEnc <$>
        ((DeliverForge.hooksPRNGBucketHybridGen cka prng fs Δbucket qep tL par t).startSend ctx P
          (tE.eval ρ) (γE.eval ρ) (σvE.eval ρ) (rE.eval ρ)).run h := by
  unfold prngBucketStartSendC
  rw [startSend_run_eq, eval_bind_ret]
  set t0 : ℕ := tE.eval ρ
  set γ0 : Γ := γE.eval ρ
  set σv0 : Option RSt := σvE.eval ρ
  set r0 : Option CCoins := rE.eval ρ
  have h0 : (Expr.pair hE (.pair ctxE (.pair tE (.pair γE (.pair σvE rE))))).eval ρ =
      (prngBucketHsEnc h, cGsEnc prngVpEnc ctx, t0, γ0, σv0, r0) := by
    simp [Expr.eval, hh, hctx, t0, γ0, σv0, r0]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := (.prod pbHsTyEvh (.prod (cGsTy pbVpTyEvh) (.prod .nat (.prod (.base .γ)
      (.prod (.opt (.base .sig)) (.opt (.base .ccoins)))))) : Ty Sevh))
    (prngBucketHsEnc h, cGsEnc prngVpEnc ctx, t0, γ0, σv0, r0) ρ
  have hStep1 :
      (Comp.caseOpt (O := OOevh) (I := IIevh) (.snd (.snd (.snd (.snd (.snd .v0)))))
        (@Comp.sample _ _ _ OOevh IIevh _ CKASamp.ccoins .unit) (.ret .v0)).eval ρ₁ =
      (match r0 with
        | some c => pure c
        | none => (sampleT CCoins : TComp (PRFPRNG.spec RSt I K) CCoins)) := by
    rcases r0 with _ | c
    · simp only [ρ₁, Comp.eval, Expr.eval, Expr.v0, Env.get_cons_zero,
        prngIface, prngSamplers, ckaSamplers, hSampCCoins, sampleT]
      exact liftP_eq_liftM IIevh (fun _ => rfl) ($ᵗ CCoins)
    · rfl
  set hLc : DeliverForge.PRNGBucketState T RSt K I :=
    if (DeliverForge.postLeak tL ctx && h.lc.isNone && decide (healEpoch tL < t0)) = true then
      { h with lc := some (t0 - 1) } else h
  rw [eval_bind, hStep1, map_bind]
  refine bind_congr fun coins => ?_
  set ρ₂ := Env.cons (t := (.base .ccoins : Ty Sevh)) coins ρ₁
  rw [eval_bind]
  have hPl : (postLeakBucketE (O := OOevh) tL (.fst (.snd .v1))).eval ρ₂ =
      DeliverForge.postLeak tL ctx :=
    postLeakBucketE_eval tL (.fst (.snd .v1)) ρ₂ ctx rfl
  have hLcEval :
      (Expr.ite (O := OOevh)
        (.and (.and (postLeakBucketE tL (.fst (.snd .v1)))
          (.not (isSomeE (prngBucketHsLc (.fst .v1)))))
          (.lt (.nat (healEpoch tL)) (.fst (.snd (.snd .v1)))))
        (prngBucketHsSetLc (.fst .v1) (.some (.sub (.fst (.snd (.snd .v1))) (.nat 1))))
        (.fst .v1)).eval ρ₂ = prngBucketHsEnc hLc := by
    have hIsSomeLc :
        (isSomeE (O' := OOevh) (prngBucketHsLc (.fst .v1))).eval ρ₂ = h.lc.isSome := by
      dsimp only [ρ₂, ρ₁, isSomeE, prngBucketHsLc, prngBucketHsEnc, Expr.eval, Expr.v1]
      cases h.lc <;> rfl
    have hCondLc :
        (Expr.and (O := OOevh) (.and (postLeakBucketE tL (.fst (.snd .v1)))
          (.not (isSomeE (prngBucketHsLc (.fst .v1)))))
          (.lt (.nat (healEpoch tL)) (.fst (.snd (.snd .v1))))).eval ρ₂ =
        (DeliverForge.postLeak tL ctx && h.lc.isNone && decide (healEpoch tL < t0)) := by
      simp only [Expr.eval, hPl, hIsSomeLc]
      cases h.lc <;> rfl
    dsimp only [hLc]
    change (if (Expr.and (O := OOevh) (.and (postLeakBucketE tL (.fst (.snd .v1)))
        (.not (isSomeE (prngBucketHsLc (.fst .v1)))))
        (.lt (.nat (healEpoch tL)) (.fst (.snd (.snd .v1))))).eval ρ₂ = true
      then _ else _) = _
    rw [hCondLc]
    by_cases hc : (DeliverForge.postLeak tL ctx && h.lc.isNone && decide (healEpoch tL < t0)) = true <;>
      simp [hc, ρ₂, ρ₁, prngBucketHsSetLc, prngBucketHsCache, prngBucketHsFTbl,
        prngBucketHsCorrRoot, prngBucketHsEnc, Expr.eval, Expr.v1]
  have hHBLc : (hLc.fTable t0).length ≤ L := by
    have hFT : hLc.fTable = h.fTable := by dsimp only [hLc]; split_ifs <;> rfl
    simpa [hFT] using hHB t0
  have ⟨hRoot, _⟩ := rootPRNGBucketHybridC_eval
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) (T := T) prng hPrngUp heqI hSampK L Δbucket tL par t
    (.ite (.and (.and (postLeakBucketE tL (.fst (.snd .v1)))
        (.not (isSomeE (prngBucketHsLc (.fst .v1)))))
        (.lt (.nat (healEpoch tL)) (.fst (.snd (.snd .v1)))))
      (prngBucketHsSetLc (.fst .v1) (.some (.sub (.fst (.snd (.snd .v1))) (.nat 1)))) (.fst .v1))
    (.fst (.snd (.snd .v1))) (postLeakBucketE tL (.fst (.snd .v1)))
    (.snd (.snd (Expr.op (O := OOevh) CKAOp.ckaSend (.pair (.fst (.snd (.snd (.snd .v1)))) .v0))))
    (.fst (.snd (.snd (.snd (.snd .v1))))) ρ₂ hLc hLcEval hHBLc
  have hRootArgs :
      ((Expr.fst (.snd (.snd (Expr.v1 (O := OOevh))))).eval ρ₂ = t0) ∧
      ((Expr.snd (.snd (Expr.op (O := OOevh) CKAOp.ckaSend
        (.pair (.fst (.snd (.snd (.snd .v1)))) .v0)))).eval ρ₂ = (cka.send γ0 coins).2.2) ∧
      ((Expr.fst (.snd (.snd (.snd (.snd (Expr.v1 (O := OOevh))))))).eval ρ₂ = σv0) := by
    refine ⟨rfl, ?_, rfl⟩
    simp [ρ₂, ρ₁, hSend, Expr.eval, Expr.v0, Expr.v1]
  rw [hRootArgs.1, hPl, hRootArgs.2.1, hRootArgs.2.2] at hRoot
  rw [StateT.run_bind, hRoot, bind_map_left, map_bind]
  refine bind_congr fun ⟨step, h1⟩ => ?_
  rcases step with _ | ⟨σ', kVal⟩
  · simp [ρ₂, ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
  · simp only [eval_caseOpt, StateT.run_bind, StateT.run_modify, StateT.run_pure,
      pure_bind, map_pure, Prod.map, id_eq]
    simp [ρ₂, ρ₁, hSend, hFsInitS, prngBucketHsSetCache, prngBucketHsCache,
      prngBucketHsEnc, Comp.eval, Expr.eval, Expr.v0, Expr.v1, Expr.v2, Expr.v3]
    ext j
    by_cases hj : j = t0 <;> simp [hj]

private def honestCacheLookup [DecidableEq T]
    (h : DeliverForge.PRNGBucketState T RSt K I) (t0 : ℕ) (tn0 : T) :
    Option (Option RSt × K) :=
  match h.cache t0 with
  | some (tCached, σc, kVal) => if tCached = tn0 then some (σc, kVal) else none
  | none => none

private theorem startRecv_run_eq [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (ctx : Ctx Γ T (Option RSt) SS RS M E) (P : Party)
    (t0 : ℕ) (γ0 : Γ) (σv0 : Option RSt) (tn0 : T)
    (h : DeliverForge.PRNGBucketState T RSt K I) :
    ((DeliverForge.hooksPRNGBucketHybridGen cka prng fs Δbucket qep tL par t).startRecv
        ctx P t0 γ0 σv0 tn0).run h =
      match honestCacheLookup h t0 tn0 with
      | some (σc, kVal) =>
        pure (some (some ((cka.receive γ0 tn0).1,
          DeliverForge.resolveCorrRoot h t0 σc, fs.initReceiver kVal)), h)
      | none =>
        StateT.run (do
          if !(qep + 1 < t0) && (lastLeakGuessAdmissible Δbucket tL t0 && (DeliverForge.partyPar (Party.senderOf t0) == par)) then
            if tL.isSome && t0 = healEpoch tL then
              return none
            else if DeliverForge.postLeak tL ctx || h.corrRoot.isSome || t < t0 then
              match DeliverForge.resolveCorrRoot h (t0 - 1) σv0 with
              | none => return none
              | some σ =>
                let kk := cka.receive γ0 tn0
                let p := prng.up σ kk.2
                return some (some (kk.1, some p.1, fs.initReceiver p.2))
            else if t0 = t then
              let kk := cka.receive γ0 tn0
              match ← DeliverForge.liftPBucket (PRFPRNG.challPrfQuery (State := RSt) (Input := I) (Output := K) kk.2) with
              | none => return none
              | some (σOut, kOut) =>
                return some (some (kk.1, some σOut, fs.initReceiver kOut))
            else if !(t0 < healEpoch tL) then
              let kk := cka.receive γ0 tn0
              let kOut ← DeliverForge.lookupPRNGBucketF t0 kk.2
              return some (some (kk.1, none, fs.initReceiver kOut))
            else
              return some none
          else
            return some none) h := by
  unfold DeliverForge.hooksPRNGBucketHybridGen
  dsimp only
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rcases hc : h.cache t0 with _ | ⟨tCached, σc, kVal⟩
  · simp only [honestCacheLookup, hc]
    rfl
  · by_cases hEq : tCached = tn0
    · simp only [honestCacheLookup, hc, hEq, ↓reduceIte, StateT.run_pure]
    · simp only [honestCacheLookup, hc, hEq, ↓reduceIte]
      rfl

theorem prngBucketStartRecv_fTable_len [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (ctx : Ctx Γ T (Option RSt) SS RS M E) (P : Party)
    (t0 : ℕ) (γ0 : Γ) (σv0 : Option RSt) (tn0 : T)
    (h : DeliverForge.PRNGBucketState T RSt K I) :
    ∀ res ∈ support (((DeliverForge.hooksPRNGBucketHybridGen cka prng fs Δbucket qep tL par t).startRecv
        ctx P t0 γ0 σv0 tn0).run h),
      ∀ τ, (res.2.fTable τ).length ≤ (h.fTable τ).length + 1 := by
  rw [startRecv_run_eq]
  rcases honestCacheLookup h t0 tn0 with _ | ⟨σc, kVal⟩
  · intro res hmem
    split_ifs at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact fun _ => Nat.le_add_right _ _
    · rcases hR : DeliverForge.resolveCorrRoot h (t0 - 1) σv0 with _ | σ <;>
      · simp only [hR, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; exact fun _ => Nat.le_add_right _ _
    · simp only [StateT.run_bind, DeliverForge.liftPBucket, StateT.run_lift, bind_assoc, pure_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨ans, _, hmem⟩ := hmem
      rcases ans with _ | ⟨σOut, kOut⟩ <;>
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; exact fun _ => Nat.le_add_right _ _
    · simp only [StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨kOut, h1⟩, hmemLk, hmem⟩ := hmem
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem
      unfold DeliverForge.lookupPRNGBucketF at hmemLk
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmemLk
      rcases hlk : (h.fTable t0).lookup (cka.receive γ0 tn0).2 with _ | k
      · simp only [hlk, StateT.run_bind, StateT.run_lift, StateT.run_modify, StateT.run_pure,
          pure_bind, bind_assoc, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hmemLk
        obtain ⟨k', _, hEq⟩ := hmemLk
        rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
        intro τ
        by_cases hτ : τ = t0
        · subst hτ; simp [Function.update_self]
        · simp [Function.update_of_ne hτ]
      · simp only [hlk, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmemLk
        rcases hmemLk with ⟨_, rfl⟩
        exact fun _ => Nat.le_add_right _ _
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact fun _ => Nat.le_add_right _ _
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact fun _ => Nat.le_add_right _ _
  · intro res hmem
    simp only [support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; exact fun _ => Nat.le_add_right _ _

theorem prngBucketStartRecvC_eval [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (hRecv : ckaReceive = cka.receive)
    (hPrngUp : prngUp = prng.up)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (heqT : eqT = (· == ·))
    (heqI : eqI = (· == ·))
    (hSampK : sampK = ($ᵗ K : ProbComp K))
    (L Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    {Γ'} (hE : Expr OOevh Γ' pbHsTyEvh) (ctxE : Expr OOevh Γ' (cGsTy pbVpTyEvh))
    (pE : Expr OOevh Γ' .bool) (tE : Expr OOevh Γ' .nat)
    (γE : Expr OOevh Γ' (.base .γ)) (σvE : Expr OOevh Γ' (.opt (.base .sig)))
    (tnE : Expr OOevh Γ' (.base .t)) (ρ : Env Γ')
    (h : DeliverForge.PRNGBucketState T RSt K I)
    (ctx : Ctx Γ T (Option RSt) SS RS M E) (P : Party)
    (hHB : ∀ τ, (h.fTable τ).length ≤ L)
    (hh : hE.eval ρ = prngBucketHsEnc h)
    (hctx : ctxE.eval ρ = cGsEnc prngVpEnc ctx) :
    (prngBucketStartRecvC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L Δbucket qep tL par t hE ctxE pE tE γE σvE tnE).eval ρ =
      Prod.map id prngBucketHsEnc <$>
        ((DeliverForge.hooksPRNGBucketHybridGen cka prng fs Δbucket qep tL par t).startRecv ctx P
          (tE.eval ρ) (γE.eval ρ) (σvE.eval ρ) (tnE.eval ρ)).run h := by
  unfold prngBucketStartRecvC
  rw [startRecv_run_eq, eval_bind_ret]
  set tH : ℕ := healEpoch tL
  set t0 : ℕ := tE.eval ρ
  set γ0 : Γ := γE.eval ρ
  set σv0 : Option RSt := σvE.eval ρ
  set tn0 : T := tnE.eval ρ
  have h0 : (Expr.pair hE (.pair ctxE (.pair tE (.pair γE (.pair σvE tnE))))).eval ρ =
      (prngBucketHsEnc h, cGsEnc prngVpEnc ctx, t0, γ0, σv0, tn0) := by
    simp [Expr.eval, hh, hctx, t0, γ0, σv0, tn0]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := (.prod pbHsTyEvh (.prod (cGsTy pbVpTyEvh) (.prod .nat (.prod (.base .γ)
      (.prod (.opt (.base .sig)) (.base .t))))) : Ty Sevh))
    (prngBucketHsEnc h, cGsEnc prngVpEnc ctx, t0, γ0, σv0, tn0) ρ
  rw [eval_caseOpt]
  have hHonest :
      (Expr.caseOpt (.tget (prngBucketHsCache (.fst (Expr.v0 (O := OOevh)))) (.fst (.snd (.snd .v0)))) .none
        (.ite (Expr.op (O := OOevh) CKAOp.eqT (.pair (.fst .v0) (.snd (.snd (.snd (.snd (.snd .v1)))))))
          (.some (.snd .v0)) .none)).eval ρ₁ =
      honestCacheLookup h t0 tn0 := by
    simp only [honestCacheLookup, ρ₁, prngBucketHsCache, prngBucketHsEnc, heqT, Expr.eval,
      Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ, BEq.beq]
    rcases h.cache t0 with _ | ⟨tCached, σc, kVal⟩
    · rfl
    · by_cases hEq : tCached = tn0 <;> simp [hEq]
  rw [hHonest]; clear hHonest
  rcases honestCacheLookup h t0 tn0 with _ | ⟨σc, kVal⟩
  · rw [eval_ite]
    have hBucketCond :
        (Expr.and (.not (.lt (.nat (qep + 1)) (.fst (.snd (.snd (Expr.v0 (O := OOevh)))))))
          (validGuessBucketParPaperE Δbucket tL par (.fst (.snd (.snd .v0))))).eval ρ₁ =
        (!(decide (qep + 1 < t0)) &&
          (lastLeakGuessAdmissible Δbucket tL t0 &&
            (DeliverForge.partyPar (Party.senderOf t0) == par))) := by
      simp [ρ₁, validGuessBucketParPaperE_eval, Expr.eval, Expr.v0]
    rw [hBucketCond]
    by_cases hBuck : (!(decide (qep + 1 < t0)) &&
        (lastLeakGuessAdmissible Δbucket tL t0 &&
          (DeliverForge.partyPar (Party.senderOf t0) == par))) = true
    · simp only [hBuck, ↓reduceIte]
      rw [eval_ite]
      have hCond1 : (Expr.and (.bool tL.isSome)
          (.eqN (.fst (.snd (.snd (Expr.v0 (O := OOevh))))) (.nat tH))).eval ρ₁ =
          (tL.isSome && decide (t0 = tH)) := rfl
      rw [hCond1]
      by_cases htH1 : (tL.isSome && decide (t0 = tH)) = true
      · simp [htH1, ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
      · simp only [htH1, Bool.false_eq_true, ↓reduceIte]
        rw [eval_ite]
        have hPl : (postLeakBucketE (O := OOevh) tL (.fst (.snd .v0))).eval ρ₁ =
            DeliverForge.postLeak tL ctx :=
          postLeakBucketE_eval tL (.fst (.snd .v0)) ρ₁ ctx rfl
        have hCond2 :
            (orE (O' := OOevh) (postLeakBucketE tL (.fst (.snd .v0)))
              (orE (isSomeE (prngBucketHsCorrRoot (.fst .v0)))
                (.lt (.nat t) (.fst (.snd (.snd .v0)))))).eval ρ₁ =
            (DeliverForge.postLeak tL ctx || h.corrRoot.isSome || decide (t < t0)) := by
          have hIsSome : (isSomeE (O' := OOevh) (prngBucketHsCorrRoot (.fst .v0))).eval ρ₁ =
              h.corrRoot.isSome := by
            dsimp only [ρ₁, isSomeE, prngBucketHsCorrRoot, prngBucketHsEnc, Expr.eval, Expr.v0]
            cases h.corrRoot <;> rfl
          have hOr2 :
              (orE (O' := OOevh) (isSomeE (prngBucketHsCorrRoot (.fst .v0)))
                (.lt (.nat t) (.fst (.snd (.snd .v0))))).eval ρ₁ =
              (h.corrRoot.isSome || decide (t < t0)) := by
            change (if (isSomeE (O' := OOevh) (prngBucketHsCorrRoot (.fst .v0))).eval ρ₁ = true
              then true else (Expr.lt (.nat t) (.fst (.snd (.snd .v0)))).eval ρ₁) = _
            rw [hIsSome]
            cases h.corrRoot.isSome <;> rfl
          change (if (postLeakBucketE (O := OOevh) tL (.fst (.snd .v0))).eval ρ₁ = true
            then true
            else (orE (isSomeE (prngBucketHsCorrRoot (.fst .v0)))
              (.lt (.nat t) (.fst (.snd (.snd .v0))))).eval ρ₁) = _
          rw [hPl, hOr2]
          cases DeliverForge.postLeak tL ctx <;> rfl
        rw [hCond2]
        by_cases hgt : (DeliverForge.postLeak tL ctx || h.corrRoot.isSome || decide (t < t0)) = true
        · have hRes :
              (resolveCorrRootE (O := OOevh) (.fst .v0) (.sub (.fst (.snd (.snd .v0))) (.nat 1))
                (.fst (.snd (.snd (.snd (.snd .v0)))))).eval ρ₁ =
              DeliverForge.resolveCorrRoot h (t0 - 1) σv0 :=
            resolveCorrRootE_eval _ _ _ ρ₁ h rfl
          simp only [hgt, ↓reduceIte, eval_caseOpt, hRes]
          rcases DeliverForge.resolveCorrRoot h (t0 - 1) σv0 with _ | σ
          · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
          · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, hRecv, hPrngUp, hFsInitR,
              Expr.eval, Expr.v0, Expr.v1]
        · simp only [hgt, Bool.false_eq_true, ↓reduceIte]
          rw [eval_ite]
          have hCond3 : (Expr.eqN (.fst (.snd (.snd (Expr.v0 (O := OOevh))))) (.nat t)).eval ρ₁ =
              decide (t0 = t) := rfl
          rw [hCond3]
          by_cases hts : t0 = t
          · have htsIf : (t0 = t) ↔ True := by simp [hts]
            simp only [htsIf, decide_true, ↓reduceIte, eval_bind, query_challPrf_eval,
              DeliverForge.liftPBucket, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind]
            have hkk : (Expr.snd (Expr.op (O := OOevh) CKAOp.ckaReceive
                (.pair (.fst (.snd (.snd (.snd (Expr.v0 (O := OOevh))))))
                  (.snd (.snd (.snd (.snd (.snd .v0)))))))).eval ρ₁ =
                (cka.receive γ0 tn0).2 := by
              simp [ρ₁, hRecv, Expr.eval, Expr.v0]
            rw [hkk]
            refine bind_congr fun ans => ?_
            rcases ans with _ | ⟨σOut, kOut⟩
            · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v1]
            · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, hRecv, hFsInitR,
                Expr.eval, Expr.v0, Expr.v2]
          · simp only [hts, decide_false, Bool.false_eq_true, ↓reduceIte]
            rw [eval_ite]
            have hCond4 : (Expr.not (.lt (.fst (.snd (.snd (Expr.v0 (O := OOevh))))) (.nat tH))).eval ρ₁ =
                (!decide (t0 < tH)) := rfl
            rw [hCond4]
            by_cases hgeH : (!decide (t0 < tH)) = true
            · simp only [hgeH, ↓reduceIte, eval_bind, StateT.run_bind, map_bind]
              have ⟨hLk, _⟩ := lookupPRNGBucketFC_eval
                (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
                (sampI := sampI) (sampK := sampK) (T := T) (RSt := RSt) heqI hSampK L
                (.fst .v0) (.fst (.snd (.snd .v0)))
                (.snd (Expr.op (O := OOevh) CKAOp.ckaReceive
                  (.pair (.fst (.snd (.snd (.snd .v0)))) (.snd (.snd (.snd (.snd (.snd .v0))))))))
                ρ₁ h rfl (hHB t0)
              have hArgs :
                  ((Expr.fst (.snd (.snd (Expr.v0 (O := OOevh))))).eval ρ₁ = t0) ∧
                  ((Expr.snd (Expr.op (O := OOevh) CKAOp.ckaReceive
                    (.pair (.fst (.snd (.snd (.snd (Expr.v0 (O := OOevh))))))
                      (.snd (.snd (.snd (.snd (.snd .v0)))))))).eval ρ₁ = (cka.receive γ0 tn0).2) := by
                refine ⟨rfl, ?_⟩
                simp [ρ₁, hRecv, Expr.eval, Expr.v0]
              rw [hArgs.1, hArgs.2] at hLk
              rw [hLk, bind_map_left]
              refine bind_congr fun ⟨kOut, h1⟩ => ?_
              simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, hRecv, hFsInitR,
                Expr.eval, Expr.v0, Expr.v1]
            · simp [hgeH, ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
    · simp [hBuck, ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
  · set ρ₂ := Env.cons (t := (.prod (.opt (.base .sig)) (.base .k) : Ty Sevh)) (σc, kVal) ρ₁
    have hResC :
        (resolveCorrRootE (O := OOevh) (.fst .v1) (.fst (.snd (.snd .v1))) (.fst .v0)).eval ρ₂ =
        DeliverForge.resolveCorrRoot h t0 σc :=
      resolveCorrRootE_eval _ _ _ ρ₂ h rfl
    change (Comp.ret _).eval ρ₂ = _
    simp only [eval_ret, map_pure, Prod.map, id_eq, pair_eval, some_eval, hResC]
    simp [ρ₂, ρ₁, hRecv, hFsInitR, Expr.eval, Expr.v0, Expr.v1]

theorem hooksPRNGBucketHybridGen_startRecv_rs [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    {VROk : RS → Prop} (hInitR : ∀ k, VROk (fs.initReceiver k))
    (ctx : Ctx Γ T (Option RSt) SS RS M E) (P : Party)
    (t0 : ℕ) (γ0 : Γ) (σv0 : Option RSt) (tn0 : T)
    (h : DeliverForge.PRNGBucketState T RSt K I) :
    ∀ res ∈ support (((DeliverForge.hooksPRNGBucketHybridGen cka prng fs Δbucket qep tL par t).startRecv
        ctx P t0 γ0 σv0 tn0).run h),
      ∀ γ' σ' rs, res.1 = some (some (γ', σ', rs)) → VROk rs := by
  rw [startRecv_run_eq]
  rcases honestCacheLookup h t0 tn0 with _ | ⟨σc, kVal⟩
  · intro res hmem γ' σ' rs hst
    split_ifs at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; simp at hst
    · rcases hR : DeliverForge.resolveCorrRoot h (t0 - 1) σv0 with _ | σ
      · simp only [hR, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; simp at hst
      · simp only [hR, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; cases hst; exact hInitR _
    · simp only [StateT.run_bind, DeliverForge.liftPBucket, StateT.run_lift, bind_assoc, pure_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨ans, _, hmem⟩ := hmem
      rcases ans with _ | ⟨σOut, kOut⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; simp at hst
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; cases hst; exact hInitR _
    · simp only [StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨kOut, h1⟩, _, hmem⟩ := hmem
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; cases hst; exact hInitR _
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; simp at hst
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; simp at hst
  · intro res hmem γ' σ' rs hst
    simp only [support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; cases hst; exact hInitR _

theorem prngBucketRevealC_eval [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    {Γ'} (hE : Expr OOevh Γ' pbHsTyEvh) (ctxE : Expr OOevh Γ' (cGsTy pbVpTyEvh))
    (pE : Expr OOevh Γ' .bool) (vpE : Expr OOevh Γ' pbVpTyEvh) (ρ : Env Γ')
    (h : DeliverForge.PRNGBucketState T RSt K I)
    (ctx : Ctx Γ T (Option RSt) SS RS M E) (P : Party)
    (vp : VP Γ T (Option RSt) SS RS)
    (hh : hE.eval ρ = prngBucketHsEnc h)
    (hctx : ctxE.eval ρ = cGsEnc prngVpEnc ctx)
    (hvp : vpE.eval ρ = prngVpEnc vp) :
    (prngBucketRevealC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) tL hE ctxE pE vpE).eval ρ =
      Prod.map (Option.map ckaPsEnc) prngBucketHsEnc <$>
        ((DeliverForge.hooksPRNGBucketHybridGen cka prng fs Δbucket qep tL par t).reveal ctx P vp).run h := by
  unfold prngBucketRevealC DeliverForge.hooksPRNGBucketHybridGen
  dsimp only
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [eval_bind_ret]
  have h0 : (Expr.pair hE (.pair ctxE vpE)).eval ρ =
      (prngBucketHsEnc h, cGsEnc prngVpEnc ctx, prngVpEnc vp) := by
    simp [Expr.eval, hh, hctx, hvp]
  rw [h0]; clear h0
  set ρ₁ := Env.cons
    (t := (.prod pbHsTyEvh (.prod (cGsTy pbVpTyEvh) pbVpTyEvh) : Ty Sevh))
    (prngBucketHsEnc h, cGsEnc prngVpEnc ctx, prngVpEnc vp) ρ
  set tH : ℕ := healEpoch tL
  rw [eval_caseOpt]
  have hRes :
      (resolveCorrRootE (O := OOevh) (.fst .v0) (vpTcurNat (.snd (.snd .v0)))
        (vpRoot (.snd (.snd .v0)))).eval ρ₁ =
      DeliverForge.resolveCorrRoot h vp.tcur vp.root :=
    resolveCorrRootE_eval _ _ _ ρ₁ h rfl
  rw [hRes]
  rcases DeliverForge.resolveCorrRoot h vp.tcur vp.root with _ | σ
  · rw [eval_ite]
    have hPl : (postLeakBucketE (O := OOevh) tL (.fst (.snd .v0))).eval ρ₁ =
        DeliverForge.postLeak tL ctx :=
      postLeakBucketE_eval tL (.fst (.snd .v0)) ρ₁ ctx rfl
    have hIsSome :
        (isSomeE (O' := OOevh) (prngBucketHsCorrRoot (.fst .v0))).eval ρ₁ =
        h.corrRoot.isSome := by
      dsimp only [ρ₁, isSomeE, prngBucketHsCorrRoot, prngBucketHsEnc, Expr.eval, Expr.v0]
      cases h.corrRoot <;> rfl
    have hMax :
        (maxN (O' := OOevh) (.fst (cGsEpoch (.fst (.snd .v0))))
          (.snd (cGsEpoch (.fst (.snd .v0))))).eval ρ₁ =
        max (ctx.epoch .A) (ctx.epoch .B) := by
      rw [Nat.max_def]
      simp only [ρ₁, maxN, leN, cGsEpoch, cGsEnc, Expr.eval, Expr.v0]
      by_cases hlt : ctx.epoch .B < ctx.epoch .A <;> simp [hlt]
    have hCond :
        (Expr.and (O := OOevh)
          (.and (.and (.not (postLeakBucketE tL (.fst (.snd .v0))))
            (.not (isSomeE (prngBucketHsCorrRoot (.fst .v0)))))
            (.not (.lt (vpTcurNat (.snd (.snd .v0))) (.nat tH))))
          (.eqN (vpTcurNat (.snd (.snd .v0)))
            (maxN (.fst (cGsEpoch (.fst (.snd .v0)))) (.snd (cGsEpoch (.fst (.snd .v0))))))).eval ρ₁ =
        (!DeliverForge.postLeak tL ctx && h.corrRoot.isNone && !(decide (vp.tcur < tH)) &&
          (vp.tcur == max (ctx.epoch .A) (ctx.epoch .B))) := by
      have hE : (vpTcurNat (O' := OOevh) (.snd (.snd .v0))).eval ρ₁ = vp.tcur := rfl
      simp only [Expr.eval, hPl, hIsSome, hMax, hE, BEq.beq]
      cases h.corrRoot <;> rfl
    rw [hCond]
    by_cases hC :
        (!DeliverForge.postLeak tL ctx && h.corrRoot.isNone && !(decide (vp.tcur < tH)) &&
          (vp.tcur == max (ctx.epoch .A) (ctx.epoch .B))) = true
    · simp only [hC, ↓reduceIte, eval_bind, query_prngCorr_eval, DeliverForge.liftPBucket,
        StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind]
      refine bind_congr fun σ? => ?_
      rcases σ? with _ | σOut
      · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v1]
      · simp only [eval_caseOpt, Expr.eval, Expr.v0, Env.get_cons_zero]
        set ρ₃ := Env.cons (t := (.base .sig : Ty Sevh)) σOut
          (Env.cons (t := (.opt (.base .sig) : Ty Sevh)) (some σOut) ρ₁)
        change (Comp.ret _).eval ρ₃ = _
        have hReal := realPartyE_eval (O' := OOevh)
          (.snd (.snd .v2)) (vpΓ (.snd (.snd .v2))) (Expr.var Var.zero)
          (vpVS (.snd (.snd .v2))) (vpVR (.snd (.snd .v2))) ρ₃ vp rfl
        have hΓ3 : (vpΓ (O' := OOevh) (.snd (.snd .v2))).eval ρ₃ = vp.γ := rfl
        have hVS3 : (vpVS (O' := OOevh) (.snd (.snd .v2))).eval ρ₃ = vp.vS := rfl
        have hVR3 : (vpVR (O' := OOevh) (.snd (.snd .v2))).eval ρ₃ = vp.vR := rfl
        simp only [eval_ret, pair_eval, some_eval]
        rw [hReal, hΓ3, hVS3, hVR3]
        cases hlc : h.lc <;>
          simp [ρ₃, ρ₁, hlc, isSomeE, prngBucketHsSetCorrRoot, prngBucketHsSetLc,
            prngBucketHsCache, prngBucketHsFTbl, prngBucketHsCorrRoot, prngBucketHsLc,
            prngBucketHsEnc, vpTcurNat, prngVpEnc, vpTblEnc, vpEnc,
            StateT.run_bind, StateT.run_modify, map_pure,
            Prod.map, Option.map_some, Expr.eval, Expr.v2]
    · simp [hC, ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
  · set ρ₂ := Env.cons (t := (.base .sig : Ty Sevh)) σ ρ₁
    change (Comp.ret _).eval ρ₂ = _
    have hReal := realPartyE_eval (O' := OOevh)
      (.snd (.snd .v1)) (vpΓ (.snd (.snd .v1))) .v0
      (vpVS (.snd (.snd .v1))) (vpVR (.snd (.snd .v1))) ρ₂ vp rfl
    have hPl2 : (postLeakBucketE (O := OOevh) tL (.fst (.snd .v1))).eval ρ₂ =
        DeliverForge.postLeak tL ctx :=
      postLeakBucketE_eval tL (.fst (.snd .v1)) ρ₂ ctx rfl
    simp only [eval_ret, pair_eval, some_eval]
    rw [hReal]
    have hIsSomeCr :
        (isSomeE (O' := OOevh) (prngBucketHsCorrRoot (.fst .v1))).eval ρ₂ = h.corrRoot.isSome := by
      dsimp only [ρ₂, ρ₁, isSomeE, prngBucketHsCorrRoot, prngBucketHsEnc, Expr.eval, Expr.v1]
      cases h.corrRoot <;> rfl
    have hIsSomeLc :
        (isSomeE (O' := OOevh) (prngBucketHsLc (.fst .v1))).eval ρ₂ = h.lc.isSome := by
      dsimp only [ρ₂, ρ₁, isSomeE, prngBucketHsLc, prngBucketHsEnc, Expr.eval, Expr.v1]
      cases h.lc <;> rfl
    have he2 : (vpTcurNat (O' := OOevh) (.snd (.snd .v1))).eval ρ₂ = vp.tcur := rfl
    change pure (some (ckaPsEnc (realParty vp vp.γ σ vp.vS vp.vR)),
      (Expr.ite _ _ _).eval ρ₂) = _
    simp only [Expr.eval, hPl2, hIsSomeCr, hIsSomeLc, he2]
    by_cases hlt : vp.tcur < tH <;> cases hcr : h.corrRoot <;> cases hlc : h.lc <;>
      cases hplb : DeliverForge.postLeak tL ctx <;>
      simp [ρ₂, ρ₁, hlt, hcr, hlc, prngBucketHsSetCorrRoot, prngBucketHsSetLc,
        prngBucketHsCache, prngBucketHsFTbl, prngBucketHsCorrRoot, prngBucketHsLc, prngBucketHsEnc,
        vpTcurNat, prngVpEnc, vpTblEnc, vpEnc, StateT.run_bind, StateT.run_modify, StateT.run_pure,
        map_pure, Prod.map, Option.map_some, Expr.eval, Expr.v0, Expr.v1]

theorem hooksPRNGBucketParPaperC_agrees_vr [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    {m : ℕ} {VROk : RS → Prop}
    (hSend : ckaSend = cka.send)
    (hRecv : ckaReceive = cka.receive)
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send)
    (hFsRecv : fsReceive = fs.receive)
    (heqT : eqT = (· == ·))
    (heqI : eqI = (· == ·))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hSampK : sampK = ($ᵗ K : ProbComp K))
    (hInitR : ∀ k, VROk (fs.initReceiver k))
    (hFsB : ∀ rs hdr e rs' i m', VROk rs → fs.receive rs hdr e = some (rs', i, m') → i ≤ B) :
    HooksCAgrees (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      prngBucketHsEnc
      (fun h => ∀ τ, (h.fTable τ).length + (m + 1) ≤ L)
      (HBoundedPost := fun h => ∀ τ, (h.fTable τ).length + m ≤ L)
      (VROk := VROk)
      (hooksPRNGBucketParPaperC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δbucket qep tL par t)
      (DeliverForge.hooksPRNGBucketHybridGen cka prng fs Δbucket qep tL par t) where
  hBounded_post _ hHB τ := by have := hHB τ; omega
  startSend_eval hE ctxE pE tE γE σE rE ρ h ctx P hHB hh hctx _ :=
    prngBucketStartSendC_eval cka prng fs hSend hPrngUp hFsInitS heqI hSampCCoins hSampK
      L Δbucket qep tL par t hE ctxE pE tE γE σE rE ρ h ctx P
      (fun τ => by have := hHB τ; omega) hh hctx
  startSend_bounded ctx P t0 γ0 σ0 r0 h hHB res hmem τ := by
    have h1 := prngBucketStartSend_fTable_len cka prng fs Δbucket qep tL par t ctx P t0 γ0 σ0 r0 h res hmem τ
    have h2 := hHB τ
    omega
  startRecv_eval hE ctxE pE tE γE σE tnE ρ h ctx P hHB hh hctx _ :=
    prngBucketStartRecvC_eval cka prng fs hRecv hPrngUp hFsInitR heqT heqI hSampK
      L Δbucket qep tL par t hE ctxE pE tE γE σE tnE ρ h ctx P
      (fun τ => by have := hHB τ; omega) hh hctx
  startRecv_bounded ctx P t0 γ0 σ0 tn0 h hHB res hmem τ := by
    have h1 := prngBucketStartRecv_fTable_len cka prng fs Δbucket qep tL par t ctx P t0 γ0 σ0 tn0 h res hmem τ
    have h2 := hHB τ
    omega
  startRecv_vrOk ctx P t0 γ σv Tn h _ :=
    hooksPRNGBucketHybridGen_startRecv_rs cka prng fs Δbucket qep tL par t hInitR ctx P t0 γ σv Tn h
  fsSend_eval hE _ _ _ ssE hdrE mE _ ρ h _ _ _ hh _ _ := by
    simp [hooksPRNGBucketParPaperC, prngBucketFsSendC, DeliverForge.hooksPRNGBucketHybridGen,
      prngOps, ckaOps, hFsSend, hh, StateT.run_pure, Prod.map, Expr.eval]
  fsRecv_eval hE _ _ _ rsE hdrE eE _ ρ h _ _ _ _ hVR hh _ _ _ := by
    simp only [hooksPRNGBucketParPaperC, prngBucketFsRecvC, DeliverForge.hooksPRNGBucketHybridGen,
      eval_ret, prngOps, ckaOps, hFsRecv, hh, StateT.run_pure, map_pure, Prod.map, id_eq, Expr.eval]
    congr 2
    rcases hrc : fs.receive (rsE.eval ρ) (hdrE.eval ρ) (eE.eval ρ) with _ | ⟨rs', i, m'⟩
    · rfl
    · simp [Nat.min_eq_left (hFsB _ _ _ _ _ _ hVR hrc)]
  fsRecv_bounded _ _ _ _ _ _ _ h hHB res hmem := by
    simp only [DeliverForge.hooksPRNGBucketHybridGen, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hmem
    subst hmem; exact hHB
  commit_eval hE _ _ _ newE ρ h _ _ _ new _ hh _ _ _ hnew := by
    simp [hooksPRNGBucketParPaperC, prngBucketCommitC, DeliverForge.hooksPRNGBucketHybridGen,
      hh, hnew, StateT.run_pure, Prod.map, Expr.eval]
  reveal_eval hE ctxE pE vpE ρ h ctx P vp _ hh hctx _ hvp :=
    prngBucketRevealC_eval cka prng fs Δbucket qep tL par t hE ctxE pE vpE ρ h ctx P vp hh hctx hvp

end HooksPRNGBucketEvalHooks

end CryptoGames.SM.Construction
