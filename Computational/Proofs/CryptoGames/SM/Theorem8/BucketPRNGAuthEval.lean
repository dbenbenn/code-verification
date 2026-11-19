/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs
import Computational.Proofs.ReductionDsl.SM.RedPRNGPotOK
import Computational.Proofs.ReductionDsl.Notation
import VCVio.OracleComp.EvalDist.Measure

namespace Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthEval

public section

set_option autoImplicit false

open scoped ENNReal
open OracleComp OracleSpec
open _root_.ReductionDsl (Sig Ty Ops Iface Env Expr Comp CostedReduction)
open scoped _root_.Computational.Proofs.ReductionDsl.Notation
open _root_.CryptoGames (Party CKAScheme PRFPRNG FSAEADScheme SMScheme)
open _root_.CryptoGames.CKA (CKASamp CKAOp ckaHdrTy ckaHdrCtTy ckaPsTy)
open _root_.CryptoGames.PRFPRNG
  (PRNGTag FSHdrTag prngSig prngOps prngIface fsaeadHeaderAdIface fsHdrRrEnc prngSamplers
   prngSMCodec)
open _root_.CryptoGames.SM
  (Config GameState Pos Record RecvResult
   MakesAtMostQueries admissibleLastLeakGuesses authLosingConditionsAvoided
   healedBy lastLeakGuessAdmissible ltOpt ltOptE maxN orE isSomeE pGet senderOfE validGuessE
   spec)
open _root_.CryptoGames.SM.Engine
  (VP Ctx HM EState EM Hooks HooksC HooksVRInv ConfigEC Policy
   mkPartiesE realPartyE
   vpTblTy cRecTy cRecMsg hdrCtEqE cSafeChE cGsTy esTy esG esH esAbort esMk esSetG
   cGsSt cGsEpoch cGsIdx cGsTL cGsWin cGsSetWin cGsInitE
   cEpMgmtE cRecordE cCorrAllowedE cAfterCorrE cAuthOKE optNatLit
   vpΓ vpRoot vpVS vpVR vpTcurNat
   vSend vSendC deliverE deliverEC injectE injectEC
   eval_ret)
open _root_.CryptoGames.SM.Construction
  (Header PartyState healEpoch realParty mkParties sampleT
   SchemeAdversary CKAState hooksCKA initCKA scheme
   prngHsTy prngVpTy abortedPartiesE bucketAuthCfgEC)
open Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs
  (postLeak bucketAuthCfg PRNGBucketAuthState resolveCorrRoot liftPBucketAuth
   lookupPRNGBucketAuthF rootPRNGBucketAuthHybrid hooksPRNGBucketAuthHybrid
   initPRNGBucketAuthHybrid PRNGBucketAuthEState isHonestHdrPRNGBucket
   hooksPRNGBucketAuthMain hooksPRNGBucketAuthForgedHdr implPRNGBucketAuthGen
   runPRNGAuthBucketHybridGen redPRNGAuthBucketHybridMain redPRNGAuthBucketHybridForgedHdr
   redPRNGAuthBucketHybrid pbaTableEntryTy prngBucketAuthHsTy prngBucketAuthEsTy
   prngBucketAuthRedEsTy prngBucketAuthStage2RedEsTy fsaeadMultiBucketIface
   fsMultiBucketTransEntryTy fsMultiBucketSessBookTy fsMultiBucketHsTy fsMultiBucketVpTy
   prngBucketAuthHsEnc postLeakBucketE pbaHsCache pbaHsFTbl pbaHsCorrRoot pbaHsEmptyE
   pbaHsSetCache pbaHsSetFTblAt pbaHsSetCorrRoot resolveCorrRootE pbaTableLookupE
   lookupPRNGBucketAuthFC rootPRNGBucketAuthHybridC prngBucketAuthStartSendC
   prngBucketAuthStartRecvC prngBucketAuthFsSendC prngBucketAuthFsRecvC
   prngBucketAuthCommitC prngBucketAuthRevealC hooksPRNGBucketAuthC isHonestHdrPRNGBucketE
   prngBucketAuthMainStartRecvC prngBucketAuthForgedHdrRevealC hooksPRNGBucketAuthMainC
   hooksPRNGBucketAuthForgedHdrC initPRNGBucketAuthEStateC redPRNGAuthBucketHybridProg)

section CostedBucketAuth

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}

local notation "S" => prngSig KC Γ CCoins T I KR RSt K SS RS M E

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

local notation "OO" =>
  prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE

local notation "II" =>
  prngIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK

local notation "IIM" =>
  @fsaeadMultiBucketIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK

local notation "hdrTy" => ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "hdrCtTy" => ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "psTy" => ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "pbaHsTy" => @prngBucketAuthHsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "pbaVpTy" => @prngVpTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "pbaEsTy" => @prngBucketAuthEsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "pbaRedEsTy" => @prngBucketAuthRedEsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "pbaStage2RedEsTy" => @prngBucketAuthStage2RedEsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "mbHsTy" => @fsMultiBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "mVpTy" => @fsMultiBucketVpTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "mBookTy" => @fsMultiBucketSessBookTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "transEntryTy" => @fsMultiBucketTransEntryTy KC Γ CCoins T I KR RSt K SS RS M E


private def PBAInv (L k : ℕ) (h : PRNGBucketAuthState T RSt K I) : Prop :=
  ∀ t0, (h.fTable t0).length + k ≤ L

private theorem PBAInv.mono {L k k' : ℕ} (hk : k' ≤ k) {h : PRNGBucketAuthState T RSt K I}
    (hInv : PBAInv L k h) : PBAInv L k' h := by
  intro t0; have := hInv t0; omega

private theorem PBAInv.len_le {L k : ℕ} {h : PRNGBucketAuthState T RSt K I}
    (hInv : PBAInv L k h) (t0 : ℕ) : (h.fTable t0).length ≤ L := by
  have := hInv t0; omega

private theorem PBAInv.step {L k : ℕ} {h h' : PRNGBucketAuthState T RSt K I}
    (hInv : PBAInv L (k + 1) h)
    (hlen : ∀ t0, (h'.fTable t0).length ≤ (h.fTable t0).length + 1) :
    PBAInv L k h' := by
  intro t0; have := hInv t0; have := hlen t0; omega

private theorem pba_foldr_lookup_eq [DecidableEq I] (ik : I) (tbl : List (I × K)) :
    tbl.foldr (fun x (acc : Option K) => if (ik == x.1) = true then some x.2 else acc) none =
      tbl.lookup ik := by
  induction tbl with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    simp only [List.foldr_cons, List.lookup_cons, ih]
    cases ik == k <;> rfl

open _root_.CryptoGames.SM (ltOptE_eval) in
open _root_.CryptoGames.SM.Engine (cGsEnc optNatLit_eval) in
private theorem postLeakBucketE_eval {O : Ops S} {vpT : Ty S} {VPt : Type}
    (vpEncFn : VPt → vpT.denote) (tL : Option ℕ) {Γ'}
    (ctxE : Expr O Γ' (cGsTy vpT)) (ρ : Env Γ')
    (ctx : GameState VPt M (Header T × E))
    (hctx : ctxE.eval ρ = cGsEnc (vpT := vpT) vpEncFn ctx) :
    (postLeakBucketE tL ctxE).eval ρ = postLeak tL ctx := by
  unfold postLeakBucketE postLeak
  have hTL : (cGsTL ctxE).eval ρ = ctx.tL := by
    simp [cGsTL, hctx, cGsEnc, Expr.eval]
  rcases hcur : ctx.tL with _ | cur
  · simp [Expr.eval, hTL, hcur]
  · simp only [Expr.eval, hTL, hcur]
    have hlt := ltOptE_eval (O' := O) (optNatLit tL) .v0 (Env.cons (t := .nat) cur ρ)
    rw [hlt]
    simp [optNatLit_eval, Expr.eval, Expr.v0]

open _root_.CryptoGames.SM (letE_eval) in
private theorem resolveCorrRootE_eval {O : Ops S} {Γ'}
    (hE : Expr O Γ' pbaHsTy) (epE : Expr O Γ' .nat) (σvE : Expr O Γ' (.opt (.base .sig)))
    (ρ : Env Γ') (h : PRNGBucketAuthState T RSt K I)
    (hh : hE.eval ρ = prngBucketAuthHsEnc h) :
    (resolveCorrRootE hE epE σvE).eval ρ =
      resolveCorrRoot h (epE.eval ρ) (σvE.eval ρ) := by
  unfold resolveCorrRootE resolveCorrRoot
  rw [letE_eval]
  set ep := epE.eval ρ
  set σv := σvE.eval ρ
  have h0 : (Expr.pair hE (.pair epE σvE)).eval ρ = (prngBucketAuthHsEnc h, ep, σv) := by
    simp [Expr.eval, hh, ep, σv]
  rw [h0]; clear h0
  rcases σv with _ | σ
  · rcases hcr : h.corrRoot with _ | ⟨eC, σC⟩
    · simp [prngBucketAuthHsEnc, pbaHsCorrRoot, hcr, Expr.eval, Expr.v0]
    · by_cases hEq : ep = eC <;>
        simp [prngBucketAuthHsEnc, pbaHsCorrRoot, hcr, hEq, BEq.beq,
          Expr.eval, Expr.v0, Expr.v1]
  · simp [Expr.eval, Expr.v0]

open _root_.CryptoGames.SM (letE_eval) in
open _root_.CryptoGames.CKA (ckaOps) in
private theorem pbaTableLookupE_eval [DecidableEq I] (heqI : eqI = (· == ·))
    (L : ℕ) {Γ'}
    (tblE : Expr OO Γ' (.list (@pbaTableEntryTy KC Γ CCoins T I KR RSt K SS RS M E)))
    (ikE : Expr OO Γ' (.base .i)) (ρ : Env Γ')
    (hL : (tblE.eval ρ).length ≤ L) :
    (pbaTableLookupE L tblE ikE).eval ρ = (tblE.eval ρ).lookup (ikE.eval ρ) := by
  unfold pbaTableLookupE
  rw [letE_eval]
  have htake : (tblE.eval ρ).take L = tblE.eval ρ := List.take_of_length_le hL
  simp only [prngOps, ckaOps, heqI, Expr.eval, Env.get, Expr.v0, Expr.v1, Expr.v2, htake]
  exact pba_foldr_lookup_eq (ikE.eval ρ) (tblE.eval ρ)

open _root_.CryptoGames.CKA (CKASort ckaSamplers) in
open _root_.CryptoGames.SM.Engine
  (eval_bind_ret eval_caseOpt eval_bind eval_ret tset_eval_eq_update) in
open _root_.CryptoGames.SM.Engine.RedPRNG (liftP_eq_liftM) in
private theorem lookupPRNGBucketAuthFC_eval [DecidableEq I] [SampleableType K]
    (heqI : eqI = (· == ·))
    (hSampK : sampK = ($ᵗ K : ProbComp K))
    (L : ℕ) {Γ'} (hE : Expr OO Γ' pbaHsTy) (tE : Expr OO Γ' .nat) (ikE : Expr OO Γ' (.base .i))
    (ρ : Env Γ') (h : PRNGBucketAuthState T RSt K I)
    (hh : hE.eval ρ = prngBucketAuthHsEnc h)
    (hL : (h.fTable (tE.eval ρ)).length ≤ L) :
    (lookupPRNGBucketAuthFC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L hE tE ikE).eval ρ =
      Prod.map id prngBucketAuthHsEnc <$>
        (lookupPRNGBucketAuthF (T := T) (Sig := RSt) (tE.eval ρ) (ikE.eval ρ)).run h ∧
    ∀ res ∈ support ((lookupPRNGBucketAuthF (T := T) (Sig := RSt) (tE.eval ρ) (ikE.eval ρ)).run h),
      ∀ t', (res.2.fTable t').length ≤ (h.fTable t').length + 1 := by
  unfold lookupPRNGBucketAuthFC lookupPRNGBucketAuthF
  rw [eval_bind_ret]
  set t0 : ℕ := tE.eval ρ
  set ik0 : I := ikE.eval ρ
  have h0 : (Expr.pair hE (.pair tE ikE)).eval ρ = (prngBucketAuthHsEnc h, t0, ik0) := by
    simp [Expr.eval, hh, t0, ik0]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod pbaHsTy (.prod .nat (.base CKASort.i)))
    (prngBucketAuthHsEnc h, t0, ik0) ρ
  have hTbl : (pbaTableLookupE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      L (.tget (pbaHsFTbl (.fst .v0)) (.fst (.snd .v0))) (.snd (.snd .v0))).eval ρ₁ =
      (h.fTable t0).lookup ik0 := by
    rw [pbaTableLookupE_eval heqI L _ _ ρ₁
      (by simpa [ρ₁, pbaHsFTbl, prngBucketAuthHsEnc, Expr.eval, Expr.v0] using hL)]
    rfl
  rw [eval_caseOpt, hTbl]
  rcases hlk : (h.fTable t0).lookup ik0 with _ | k
  · refine ⟨?_, ?_⟩
    · simp only [hlk, eval_bind, StateT.run_bind, StateT.run_get,
        StateT.run_lift, StateT.run_modify, StateT.run_pure, pure_bind, bind_assoc, map_bind]
      have hSamp : (@Comp.sample _ _ _ OO II _ CKASamp.k .unit).eval ρ₁ =
          (sampleT K : _root_.CryptoGames.PRFPRNG.AdversaryComp RSt I K K) := by
        simp only [Comp.eval, prngIface, prngSamplers, ckaSamplers, hSampK, sampleT]
        exact liftP_eq_liftM II (fun _ => rfl) ($ᵗ K)
      rw [hSamp]
      refine bind_congr fun k' => ?_
      set ρ₂ := Env.cons (t := .base CKASort.k) k' ρ₁
      change (Comp.ret _).eval ρ₂ = _
      simp only [eval_ret, pbaHsSetFTblAt, pbaHsCache, pbaHsFTbl, pbaHsCorrRoot,
        prngBucketAuthHsEnc, Prod.map, map_pure, ρ₂, ρ₁,
        Expr.eval, Env.get, Expr.v0, Expr.v1]
      have hUpd : (fun j => if j = t0 then (ik0, k') :: h.fTable t0 else h.fTable j) =
          Function.update h.fTable t0 ((ik0, k') :: h.fTable t0) := by
        ext j; by_cases hj : j = t0 <;> simp [hj, Function.update]
      rw [hUpd]; rfl
    · intro res hmem t'
      simp only [hlk, StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_modify,
        StateT.run_pure, pure_bind, bind_assoc, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hmem
      obtain ⟨k', _, rfl⟩ := hmem
      by_cases ht' : t' = t0
      · subst ht'; simp
      · simp [Function.update_of_ne ht']
  · refine ⟨?_, ?_⟩
    · simp [ρ₁, hlk, Comp.eval, StateT.run_bind, StateT.run_get,
        StateT.run_pure, pure_bind, Prod.map, Expr.eval, Expr.v0, Expr.v1]
    · intro res hmem t'
      simp only [hlk, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff] at hmem
      subst hmem
      exact Nat.le_add_right _ _


open _root_.CryptoGames.CKA (CKASort ckaOps ckaSamplers) in
open _root_.CryptoGames.SM (orE_eval isSomeE_eval) in
open _root_.CryptoGames.SM.Engine (eval_bind_ret eval_ite eval_caseOpt eval_bind eval_ret) in
open _root_.CryptoGames.SM.Engine.RedPRNG (liftP_eq_liftM) in
open _root_.CryptoGames.SM.Construction
  (query_process_eval query_challPrng_eval query_challPrf_eval query_prngCorr_eval) in
private theorem rootPRNGBucketAuthHybridC_eval [DecidableEq I] [SampleableType K]
    (prng : PRFPRNG KR RSt I K)
    (hPrngUp : prngUp = prng.up)
    (heqI : eqI = (· == ·))
    (hSampK : sampK = ($ᵗ K : ProbComp K))
    (L : ℕ) (tL : Option ℕ) (t : ℕ) {Γ'}
    (hE : Expr OO Γ' pbaHsTy) (tE : Expr OO Γ' .nat) (plE : Expr OO Γ' .bool)
    (ikE : Expr OO Γ' (.base .i)) (σvE : Expr OO Γ' (.opt (.base .sig)))
    (ρ : Env Γ') (h : PRNGBucketAuthState T RSt K I)
    (hh : hE.eval ρ = prngBucketAuthHsEnc h)
    (hL : (h.fTable (tE.eval ρ)).length ≤ L) :
    (rootPRNGBucketAuthHybridC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L tL t hE tE plE ikE σvE).eval ρ =
      Prod.map id prngBucketAuthHsEnc <$>
        (rootPRNGBucketAuthHybrid (T := T) prng tL t
          (tE.eval ρ) (plE.eval ρ) (ikE.eval ρ) (σvE.eval ρ)).run h ∧
    ∀ res ∈ support ((rootPRNGBucketAuthHybrid (T := T) prng tL t
        (tE.eval ρ) (plE.eval ρ) (ikE.eval ρ) (σvE.eval ρ)).run h),
      ∀ t', (res.2.fTable t').length ≤ (h.fTable t').length + 1 := by
  unfold rootPRNGBucketAuthHybridC rootPRNGBucketAuthHybrid liftPBucketAuth
  dsimp only
  rw [eval_bind_ret]
  set t0 : ℕ := tE.eval ρ
  set pl0 : Bool := plE.eval ρ
  set ik0 : I := ikE.eval ρ
  set σv0 : Option RSt := σvE.eval ρ
  have h0 : (Expr.pair hE (.pair tE (.pair plE (.pair ikE σvE)))).eval ρ =
      (prngBucketAuthHsEnc h, t0, pl0, ik0, σv0) := by
    simp [Expr.eval, hh, t0, pl0, ik0, σv0]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod pbaHsTy (.prod .nat (.prod .bool
      (.prod (.base CKASort.i) (.opt (.base CKASort.sig))))))
    (prngBucketAuthHsEnc h, t0, pl0, ik0, σv0) ρ
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  have hRes := resolveCorrRootE_eval (O := OO) (.fst .v0) (.sub (.fst (.snd .v0)) (.nat 1))
    (.snd (.snd (.snd (.snd .v0)))) ρ₁ h rfl
  change (resolveCorrRootE _ _ _).eval ρ₁ = resolveCorrRoot h (t0 - 1) σv0 at hRes
  rw [eval_ite]
  have hCond0 : (Expr.lt (.nat t) (.fst (.snd (Expr.v0 (O := OO))))).eval ρ₁ = decide (t < t0) := rfl
  rw [hCond0]; clear hCond0
  by_cases hc0 : t < t0
  · have hc0If : (t < t0) ↔ True := by simp [hc0]
    simp only [hc0If, decide_true, ↓reduceIte, eval_caseOpt, hRes]
    rcases resolveCorrRoot h (t0 - 1) σv0 with _ | σ
    · refine ⟨by simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0], ?_⟩
      intro res hmem t'; simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact Nat.le_add_right _ _
    · refine ⟨by simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, hPrngUp,
          Expr.eval, Expr.v0, Expr.v1], ?_⟩
      intro res hmem t'; simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact Nat.le_add_right _ _
  · simp only [hc0, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [eval_ite]
    have hCond1 :
        (orE (.fst (.snd (.snd (Expr.v0 (O := OO)))))
          (isSomeE (pbaHsCorrRoot (.fst .v0)))).eval ρ₁ =
        (pl0 || h.corrRoot.isSome) := by
      simp [ρ₁, orE_eval, isSomeE_eval, pbaHsCorrRoot, prngBucketAuthHsEnc, Expr.eval, Expr.v0]
    rw [hCond1]; clear hCond1
    by_cases hc1 : (pl0 || h.corrRoot.isSome) = true
    · simp only [hc1, ↓reduceIte, eval_caseOpt, hRes]
      rcases resolveCorrRoot h (t0 - 1) σv0 with _ | σ
      · refine ⟨?_, ?_⟩
        · simp only [eval_bind, query_prngCorr_eval,
            StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind]
          refine bind_congr fun σOpt => ?_
          rw [eval_caseOpt]
          rcases σOpt with _ | σOut
          · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v1]
          · simp [ρ₁, Comp.eval, StateT.run_modify,
              pbaHsSetCorrRoot, pbaHsCache, pbaHsFTbl, prngBucketAuthHsEnc,
              prngOps, ckaOps, hPrngUp, Prod.map, Expr.eval, Expr.v0, Expr.v2]
        · intro res hmem t'
          simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
            mem_support_bind_iff] at hmem
          obtain ⟨σOpt, _, hmem⟩ := hmem
          rcases σOpt with _ | σOut
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
            subst hmem; exact Nat.le_add_right _ _
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff] at hmem
            subst hmem; exact Nat.le_add_right _ _
      · refine ⟨by simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, hPrngUp,
            Expr.eval, Expr.v0, Expr.v1], ?_⟩
        intro res hmem t'; simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; exact Nat.le_add_right _ _
    · clear hRes
      simp only [hc1, Bool.false_eq_true, ↓reduceIte]
      rw [eval_ite]
      have hCond2 : (Expr.eqN (.fst (.snd (Expr.v0 (O := OO)))) (.nat t)).eval ρ₁ =
          decide (t0 = t) := rfl
      rw [hCond2]; clear hCond2
      by_cases hc2 : t0 = t
      · have hc2If : (t0 = t) ↔ True := by simp [hc2]
        simp only [hc2If, decide_true, ↓reduceIte]
        rw [eval_ite]
        have hCond2a : (Expr.and (.bool tL.isSome)
            (.eqN (.fst (.snd (Expr.v0 (O := OO)))) (.nat (healEpoch tL)))).eval ρ₁ =
            (tL.isSome && decide (t0 = healEpoch tL)) := rfl
        rw [hCond2a]; clear hCond2a
        by_cases hc2a : (tL.isSome && decide (t0 = healEpoch tL)) = true
        · refine ⟨?_, ?_⟩
          · simp only [hc2a, ↓reduceIte, eval_bind, query_challPrng_eval,
              StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind]
            have hNone : (Expr.none (O := OO) (t := .base CKASort.i)).eval ρ₁ = none := rfl
            rw [hNone]
            refine bind_congr fun kOpt => ?_
            rw [eval_caseOpt]
            rcases kOpt with _ | kOut
            · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v1]
            · simp only [Expr.eval, Expr.v0, eval_bind,
                query_prngCorr_eval, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind]
              refine bind_congr fun σOpt => ?_
              rw [eval_caseOpt]
              rcases σOpt with _ | σOut
              · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v3]
              · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v2, Expr.v4]
          · intro res hmem t'
            simp only [hc2a, ↓reduceIte, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
              mem_support_bind_iff] at hmem
            obtain ⟨kOpt, _, hmem⟩ := hmem
            rcases kOpt with _ | kOut
            · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
              subst hmem; exact Nat.le_add_right _ _
            · simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
                mem_support_bind_iff] at hmem
              obtain ⟨σOpt, _, hmem⟩ := hmem
              rcases σOpt with _ | σOut <;>
                (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem;
                 subst hmem; exact Nat.le_add_right _ _)
        · refine ⟨?_, ?_⟩
          · simp only [hc2a, Bool.false_eq_true, ↓reduceIte, eval_bind, query_challPrf_eval,
              StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind]
            have hIk : (Expr.fst (.snd (.snd (.snd (Expr.v0 (O := OO)))))).eval ρ₁ = ik0 := rfl
            rw [hIk]
            refine bind_congr fun skOpt => ?_
            rw [eval_caseOpt]
            rcases skOpt with _ | ⟨σOut, kOut⟩
            · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v1]
            · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v2]
          · intro res hmem t'
            simp only [hc2a, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
              bind_assoc, pure_bind, mem_support_bind_iff] at hmem
            obtain ⟨skOpt, _, hmem⟩ := hmem
            rcases skOpt with _ | ⟨σOut, kOut⟩ <;>
              (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem;
               subst hmem; exact Nat.le_add_right _ _)
      · simp only [hc2, decide_false, Bool.false_eq_true, ↓reduceIte]
        rw [eval_ite]
        have hCond3 : (Expr.not (.lt (.fst (.snd (Expr.v0 (O := OO)))) (.nat (healEpoch tL)))).eval ρ₁ =
            (!decide (t0 < healEpoch tL)) := rfl
        rw [hCond3]; clear hCond3
        by_cases hc3 : (!decide (t0 < healEpoch tL)) = true
        · simp only [hc3, ↓reduceIte]
          rw [eval_ite]
          have hCond3a : (Expr.and (.bool tL.isSome)
              (.eqN (.fst (.snd (Expr.v0 (O := OO)))) (.nat (healEpoch tL)))).eval ρ₁ =
              (tL.isSome && decide (t0 = healEpoch tL)) := rfl
          rw [hCond3a]; clear hCond3a
          by_cases hc3a : (tL.isSome && decide (t0 = healEpoch tL)) = true
          · refine ⟨?_, ?_⟩
            · simp only [hc3a, ↓reduceIte, eval_bind, query_process_eval,
                StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind]
              have hNone : (Expr.none (O := OO) (t := .base CKASort.i)).eval ρ₁ = none := rfl
              rw [hNone]
              refine bind_congr fun pOpt => ?_
              rw [eval_caseOpt]
              rcases pOpt with _ | u
              · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v1]
              · simp only [Expr.eval, Env.get, Expr.v0, eval_bind,
                  StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind]
                set ρ₂ := Env.cons (t := .base CKASort.k) u
                  (Env.cons (t := .opt (.base CKASort.k)) (some u) ρ₁)
                have hSamp : (@Comp.sample _ _ _ OO II _ CKASamp.k .unit).eval ρ₂ =
                    (sampleT K : _root_.CryptoGames.PRFPRNG.AdversaryComp RSt I K K) := by
                  simp only [Comp.eval, prngIface, prngSamplers, ckaSamplers, hSampK, sampleT]
                  exact liftP_eq_liftM II (fun _ => rfl) ($ᵗ K)
                rw [hSamp]
                refine bind_congr fun kRand => ?_
                simp [ρ₂, ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval,
                  Expr.v3]
            · intro res hmem t'
              simp only [hc3a, ↓reduceIte, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
                mem_support_bind_iff] at hmem
              obtain ⟨pOpt, _, hmem⟩ := hmem
              rcases pOpt with _ | u
              · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
                subst hmem; exact Nat.le_add_right _ _
              · simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
                  mem_support_bind_iff, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
                obtain ⟨kRand, _, rfl⟩ := hmem
                exact Nat.le_add_right _ _
          · refine ⟨?_, ?_⟩
            · simp only [hc3a, Bool.false_eq_true, ↓reduceIte, eval_bind, query_process_eval,
                StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind]
              have hSomeIk : (Expr.some (.fst (.snd (.snd (.snd (Expr.v0 (O := OO))))))).eval ρ₁ =
                  some ik0 := rfl
              rw [hSomeIk]
              refine bind_congr fun pOpt => ?_
              rw [eval_caseOpt]
              rcases pOpt with _ | u
              · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v1]
              · simp only [Expr.eval, Env.get, Expr.v0, eval_bind,
                  StateT.run_bind, map_bind]
                set ρ₂ := Env.cons (t := .base CKASort.k) u
                  (Env.cons (t := .opt (.base CKASort.k)) (some u) ρ₁)
                have hLk := (lookupPRNGBucketAuthFC_eval
                  (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
                  (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
                  (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
                  (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
                  (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
                  (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
                  (sampI := sampI) (sampK := sampK)
                  heqI hSampK L (.fst .v2) (.fst (.snd .v2)) (.fst (.snd (.snd (.snd .v2))))
                  ρ₂ h rfl hL).1
                change (lookupPRNGBucketAuthFC _ _ _ _).eval ρ₂ =
                  Prod.map id prngBucketAuthHsEnc <$>
                    (lookupPRNGBucketAuthF (T := T) (Sig := RSt) t0 ik0).run h at hLk
                rw [hLk, bind_map_left]
                refine bind_congr fun ⟨kRand, h1⟩ => ?_
                simp [ρ₂, Comp.eval, StateT.run_pure, Prod.map, Expr.eval]
            · intro res hmem t'
              simp only [hc3a, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
                bind_assoc, pure_bind, mem_support_bind_iff] at hmem
              obtain ⟨pOpt, _, hmem⟩ := hmem
              rcases pOpt with _ | u
              · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
                subst hmem; exact Nat.le_add_right _ _
              · simp only [StateT.run_bind, mem_support_bind_iff] at hmem
                obtain ⟨⟨kRand, h1⟩, hh1, hmem⟩ := hmem
                simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
                subst hmem
                exact (lookupPRNGBucketAuthFC_eval
                  (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
                  (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
                  (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
                  (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
                  (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
                  (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
                  (sampI := sampI) (sampK := sampK)
                  heqI hSampK L hE tE ikE ρ h hh hL).2 (kRand, h1) hh1 t'
        · refine ⟨?_, ?_⟩
          · simp only [hc3, Bool.false_eq_true, ↓reduceIte, eval_bind, query_process_eval,
              StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind]
            have hSomeIk : (Expr.some (.fst (.snd (.snd (.snd (Expr.v0 (O := OO))))))).eval ρ₁ =
                some ik0 := rfl
            rw [hSomeIk]
            refine bind_congr fun pOpt => ?_
            rw [eval_caseOpt]
            rcases pOpt with _ | kOut
            · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v1]
            · simp only [Expr.eval, Expr.v0, eval_bind,
                query_prngCorr_eval, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind]
              refine bind_congr fun σOpt => ?_
              rw [eval_caseOpt]
              rcases σOpt with _ | σOut
              · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v3]
              · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v2, Expr.v4]
          · intro res hmem t'
            simp only [hc3, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
              bind_assoc, pure_bind, mem_support_bind_iff] at hmem
            obtain ⟨pOpt, _, hmem⟩ := hmem
            rcases pOpt with _ | kOut
            · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
              subst hmem; exact Nat.le_add_right _ _
            · simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
                mem_support_bind_iff] at hmem
              obtain ⟨σOpt, _, hmem⟩ := hmem
              rcases σOpt with _ | σOut <;>
                (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem;
                 subst hmem; exact Nat.le_add_right _ _)

private abbrev pbaVpEnc : VP Γ T (Option RSt) SS RS → Ty.denote pbaVpTy :=
  _root_.CryptoGames.SM.Engine.vpTblEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
    (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
    (γvT := .base .γ) (svT := .opt (.base .sig)) (ssvT := .base .ss) (rsvT := .base .rs)

open _root_.CryptoGames.CKA (CKASort ckaOps ckaSamplers) in
open _root_.CryptoGames.SM.Engine
  (eval_bind_ret eval_caseOpt eval_bind eval_ret cGsEnc tset_eval_eq_update) in
open _root_.CryptoGames.SM.Engine.RedPRNG (liftP_eq_liftM) in
private theorem prngBucketAuthStartSendC_eval [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (hSend : ckaSend = cka.send)
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender)
    (heqI : eqI = (· == ·))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hSampK : sampK = ($ᵗ K : ProbComp K))
    (L k Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) {Γ'}
    (hE : Expr OO Γ' pbaHsTy)
    (ctxE : Expr OO Γ' (cGsTy pbaVpTy))
    (pE : Expr OO Γ' .bool)
    (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' (.base .γ))
    (σvE : Expr OO Γ' (.opt (.base .sig)))
    (rE : Expr OO Γ' (.opt (.base .ccoins)))
    (ρ : Env Γ') (h : PRNGBucketAuthState T RSt K I)
    (ctx : Ctx Γ T (Option RSt) SS RS M E) (P : Party)
    (hInv : PBAInv L (k + 1) h)
    (hh : hE.eval ρ = prngBucketAuthHsEnc h)
    (hctx : ctxE.eval ρ = cGsEnc (vpT := pbaVpTy) pbaVpEnc ctx) :
    (prngBucketAuthStartSendC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L tL t hE ctxE pE tE γE σvE rE).eval ρ =
      Prod.map id prngBucketAuthHsEnc <$>
        ((hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL t).startSend
          ctx P (tE.eval ρ) (γE.eval ρ) (σvE.eval ρ) (rE.eval ρ)).run h := by
  unfold prngBucketAuthStartSendC hooksPRNGBucketAuthHybrid
  dsimp only
  rw [eval_bind_ret]
  set t0 : ℕ := tE.eval ρ
  set γ0 : Γ := γE.eval ρ
  set σv0 : Option RSt := σvE.eval ρ
  set r0 : Option CCoins := rE.eval ρ
  have h0 : (Expr.pair hE (.pair ctxE (.pair tE (.pair γE (.pair σvE rE))))).eval ρ =
      (prngBucketAuthHsEnc h, cGsEnc (vpT := pbaVpTy) pbaVpEnc ctx, t0, γ0, σv0, r0) := by
    simp [Expr.eval, hh, hctx, t0, γ0, σv0, r0]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod pbaHsTy (.prod (cGsTy pbaVpTy)
      (.prod .nat (.prod (.base CKASort.γ) (.prod (.opt (.base CKASort.sig))
        (.opt (.base CKASort.ccoins)))))))
    (prngBucketAuthHsEnc h, cGsEnc (vpT := pbaVpTy) pbaVpEnc ctx, t0, γ0, σv0, r0) ρ
  have hCoins :
      (Comp.caseOpt (.snd (.snd (.snd (.snd (.snd (Expr.v0 (O := OO)))))))
        (@Comp.sample _ _ _ OO II _ CKASamp.ccoins .unit)
        (Comp.ret .v0)).eval ρ₁ =
      (match r0 with
       | some c => pure c
       | none => (sampleT CCoins : _root_.CryptoGames.PRFPRNG.AdversaryComp RSt I K CCoins)) := by
    rw [eval_caseOpt]
    simp only [ρ₁, Expr.eval, Expr.v0]
    rcases r0 with _ | c
    · simp only [Comp.eval, prngIface, prngSamplers, ckaSamplers, hSampCCoins, sampleT]
      exact liftP_eq_liftM II (fun _ => rfl) ($ᵗ CCoins)
    · simp [Comp.eval, Expr.eval]
  rw [eval_bind, hCoins]
  trans (Prod.map id prngBucketAuthHsEnc <$>
    (((match r0 with
      | some c => pure c
      | none => (sampleT CCoins : _root_.CryptoGames.PRFPRNG.AdversaryComp RSt I K CCoins)) >>=
      fun coins =>
        (do
          let c := cka.send γ0 coins
          match ← rootPRNGBucketAuthHybrid prng tL t t0 (postLeak tL ctx) c.2.2 σv0 with
          | none => pure none
          | some (σ', kVal) => do
            modify fun (s : PRNGBucketAuthState T RSt K I) =>
              { s with cache := Function.update s.cache t0 (some (c.2.1, σ', kVal)) }
            pure (some (c.1, c.2.1, σ', fs.initSender kVal))).run h)))
  swap
  · congr 1
    clear_value r0
    rcases r0 with _ | c
    · dsimp only
      simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
      refine bind_congr fun coins => ?_
      refine bind_congr fun ⟨stepOpt, h1⟩ => ?_
      rcases stepOpt with _ | ⟨σ', kVal⟩ <;> rfl
    · dsimp only
      simp only [StateT.run_bind, pure_bind]
      refine bind_congr fun ⟨stepOpt, h1⟩ => ?_
      rcases stepOpt with _ | ⟨σ', kVal⟩ <;> rfl
  rw [map_bind]
  refine bind_congr fun coins => ?_
  set ρ₂ := Env.cons (t := .base CKASort.ccoins) coins ρ₁
  rw [eval_bind]
  have hPl : (postLeakBucketE (O := OO) tL (.fst (.snd .v1))).eval ρ₂ = postLeak tL ctx :=
    postLeakBucketE_eval pbaVpEnc tL (.fst (.snd .v1)) ρ₂ ctx rfl
  have hIk : (Expr.snd (.snd (.op (O := OO) CKAOp.ckaSend
      (.pair (.fst (.snd (.snd (.snd .v1)))) .v0)))).eval ρ₂ = (cka.send γ0 coins).2.2 := by
    simp [ρ₂, ρ₁, prngOps, ckaOps, hSend, Expr.eval, Expr.v0, Expr.v1]
  have hRoot := (rootPRNGBucketAuthHybridC_eval
    (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)
    prng hPrngUp heqI hSampK L tL t
    (.fst .v1) (.fst (.snd (.snd .v1))) (postLeakBucketE tL (.fst (.snd .v1)))
    (.snd (.snd (.op (O := OO) CKAOp.ckaSend (.pair (.fst (.snd (.snd (.snd .v1)))) .v0))))
    (.fst (.snd (.snd (.snd (.snd .v1))))) ρ₂ h rfl
    (by simpa [ρ₂, ρ₁, Expr.eval, Expr.v1] using hInv.len_le t0)).1
  rw [hPl, hIk] at hRoot
  change (rootPRNGBucketAuthHybridC _ _ _ _ _ _ _ _).eval ρ₂ =
    Prod.map id prngBucketAuthHsEnc <$>
      (rootPRNGBucketAuthHybrid (T := T) prng tL t t0 (postLeak tL ctx)
        (cka.send γ0 coins).2.2 σv0).run h at hRoot
  rw [hRoot, bind_map_left, StateT.run_bind, map_bind]
  refine bind_congr fun ⟨stepOpt, h1⟩ => ?_
  set ρ₃ := Env.cons
    (t := (.prod (.opt (.prod (.opt (.base CKASort.sig)) (.base CKASort.k))) pbaHsTy : Ty S))
    (stepOpt, prngBucketAuthHsEnc h1) ρ₂
  change (Comp.caseOpt _ _ _).eval ρ₃ = _
  rw [eval_caseOpt]
  rcases stepOpt with _ | ⟨σ', kVal⟩
  · simp [ρ₃, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
  · simp only [Expr.eval, Expr.v0]
    set ρ₄ := Env.cons (t := .prod (.opt (.base CKASort.sig)) (.base CKASort.k)) (σ', kVal) ρ₃
    change (Comp.ret _).eval ρ₄ = _
    simp only [eval_ret, pbaHsSetCache, pbaHsCache, prngBucketAuthHsEnc, prngOps, ckaOps,
      hSend, hFsInitS, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
      Prod.map, map_pure, ρ₄, ρ₃, ρ₂, ρ₁,
      Expr.eval, Expr.v1, Expr.v2, Expr.v3]
    congr 2; congr 1; ext j; by_cases hj : j = t0 <;> simp [hj, Function.update]

private theorem lookupPRNGBucketAuthF_fTable_le [DecidableEq I] [SampleableType K]
    (t0 : ℕ) (ik : I) (h : PRNGBucketAuthState T RSt K I) :
    ∀ res ∈ support ((lookupPRNGBucketAuthF (T := T) (Sig := RSt) t0 ik).run h),
      ∀ t', (res.2.fTable t').length ≤ (h.fTable t').length + 1 := by
  intro res hmem t'
  unfold lookupPRNGBucketAuthF at hmem
  rcases hlk : (h.fTable t0).lookup ik with _ | k
  · simp only [hlk, StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_modify,
      StateT.run_pure, pure_bind, bind_assoc, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hmem
    obtain ⟨k', _, rfl⟩ := hmem
    by_cases ht' : t' = t0
    · subst ht'; simp
    · simp [Function.update_of_ne ht']
  · simp only [hlk, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; exact Nat.le_add_right _ _


private theorem rootPRNGBucketAuthHybrid_fTable_le [DecidableEq I] [SampleableType K]
    (prng : PRFPRNG KR RSt I K) (tL : Option ℕ) (t t0 : ℕ) (pl : Bool)
    (ik0 : I) (σv0 : Option RSt) (h : PRNGBucketAuthState T RSt K I) :
    ∀ res ∈ support ((rootPRNGBucketAuthHybrid (T := T) prng tL t t0 pl ik0 σv0).run h),
      ∀ t', (res.2.fTable t').length ≤ (h.fTable t').length + 1 := by
  intro res hmem t'
  unfold rootPRNGBucketAuthHybrid liftPBucketAuth at hmem
  dsimp only at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases hc0 : t < t0
  · simp only [hc0, ↓reduceIte] at hmem
    rcases hres : resolveCorrRoot h (t0 - 1) σv0 with _ | σ <;>
      (simp only [hres, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem;
       subst hmem; exact Nat.le_add_right _ _)
  · simp only [hc0, ↓reduceIte] at hmem
    by_cases hc1 : (pl || h.corrRoot.isSome) = true
    · simp only [hc1, ↓reduceIte] at hmem
      rcases hres : resolveCorrRoot h (t0 - 1) σv0 with _ | σ
      · simp only [hres, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
          mem_support_bind_iff] at hmem
        obtain ⟨σOpt, _, hmem⟩ := hmem
        rcases σOpt with _ | σOut
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
          subst hmem; exact Nat.le_add_right _ _
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff] at hmem
          subst hmem; exact Nat.le_add_right _ _
      · simp only [hres, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; exact Nat.le_add_right _ _
    · simp only [hc1, Bool.false_eq_true, ↓reduceIte] at hmem
      by_cases hc2 : t0 = t
      · subst hc2
        simp only [↓reduceIte] at hmem
        by_cases hc2a : (tL.isSome && decide (t0 = healEpoch tL)) = true
        · simp only [hc2a, ↓reduceIte, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
            mem_support_bind_iff] at hmem
          obtain ⟨kOpt, _, hmem⟩ := hmem
          rcases kOpt with _ | kOut
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
            subst hmem; exact Nat.le_add_right _ _
          · simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
              mem_support_bind_iff] at hmem
            obtain ⟨σOpt, _, hmem⟩ := hmem
            rcases σOpt with _ | σOut <;>
              (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem;
               subst hmem; exact Nat.le_add_right _ _)
        · simp only [hc2a, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
            bind_assoc, pure_bind, mem_support_bind_iff] at hmem
          obtain ⟨skOpt, _, hmem⟩ := hmem
          rcases skOpt with _ | ⟨σOut, kOut⟩ <;>
            (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem;
             subst hmem; exact Nat.le_add_right _ _)
      · simp only [hc2, ↓reduceIte] at hmem
        by_cases hc3 : (!decide (t0 < healEpoch tL)) = true
        · simp only [hc3, ↓reduceIte] at hmem
          by_cases hc3a : (tL.isSome && decide (t0 = healEpoch tL)) = true
          · simp only [hc3a, ↓reduceIte, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
              mem_support_bind_iff] at hmem
            obtain ⟨pOpt, _, hmem⟩ := hmem
            rcases pOpt with _ | u
            · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
              subst hmem; exact Nat.le_add_right _ _
            · simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
                mem_support_bind_iff, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
              obtain ⟨kRand, _, rfl⟩ := hmem
              exact Nat.le_add_right _ _
          · simp only [hc3a, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
              bind_assoc, pure_bind, mem_support_bind_iff] at hmem
            obtain ⟨pOpt, _, hmem⟩ := hmem
            rcases pOpt with _ | u
            · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
              subst hmem; exact Nat.le_add_right _ _
            · simp only [StateT.run_bind, mem_support_bind_iff] at hmem
              obtain ⟨⟨kRand, h1⟩, hh1, hmem⟩ := hmem
              simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
              subst hmem
              exact lookupPRNGBucketAuthF_fTable_le t0 ik0 h (kRand, h1) hh1 t'
        · simp only [hc3, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
            bind_assoc, pure_bind, mem_support_bind_iff] at hmem
          obtain ⟨pOpt, _, hmem⟩ := hmem
          rcases pOpt with _ | kOut
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
            subst hmem; exact Nat.le_add_right _ _
          · simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
              mem_support_bind_iff] at hmem
            obtain ⟨σOpt, _, hmem⟩ := hmem
            rcases σOpt with _ | σOut <;>
              (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem;
               subst hmem; exact Nat.le_add_right _ _)

private theorem prngBucketAuthStartSend_bounded [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L k Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (ctx : Ctx Γ T (Option RSt) SS RS M E) (P : Party) (t0 : ℕ) (γ0 : Γ)
    (σv0 : Option RSt) (r0 : Option CCoins) (h : PRNGBucketAuthState T RSt K I)
    (hInv : PBAInv L (k + 1) h) :
    ∀ res ∈ support (((hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL t).startSend
        ctx P t0 γ0 σv0 r0).run h),
      PBAInv L k res.2 := by
  intro res hmem
  unfold hooksPRNGBucketAuthHybrid at hmem; dsimp only at hmem
  rcases r0 with _ | c
  · simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
      mem_support_bind_iff] at hmem
    obtain ⟨coins, _, ⟨stepOpt, h1⟩, hh1, hmem⟩ := hmem
    rcases stepOpt with _ | ⟨σ', kVal⟩
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem
      exact hInv.step (rootPRNGBucketAuthHybrid_fTable_le prng tL t t0 (postLeak tL ctx)
        (cka.send γ0 coins).2.2 σv0 h (none, h1) hh1)
    · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff] at hmem
      subst hmem
      exact hInv.step (rootPRNGBucketAuthHybrid_fTable_le prng tL t t0 (postLeak tL ctx)
        (cka.send γ0 coins).2.2 σv0 h (some (σ', kVal), h1) hh1)
  · simp only [StateT.run_bind, pure_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨stepOpt, h1⟩, hh1, hmem⟩ := hmem
    rcases stepOpt with _ | ⟨σ', kVal⟩
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem
      exact hInv.step (rootPRNGBucketAuthHybrid_fTable_le prng tL t t0 (postLeak tL ctx)
        (cka.send γ0 c).2.2 σv0 h (none, h1) hh1)
    · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff] at hmem
      subst hmem
      exact hInv.step (rootPRNGBucketAuthHybrid_fTable_le prng tL t t0 (postLeak tL ctx)
        (cka.send γ0 c).2.2 σv0 h (some (σ', kVal), h1) hh1)

private theorem hooksPRNGBucketAuthHybrid_startRecv_run_eq [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (ctx : Ctx Γ T (Option RSt) SS RS M E) (P : Party) (t0 : ℕ) (γ0 : Γ)
    (σv0 : Option RSt) (tn0 : T) (h : PRNGBucketAuthState T RSt K I) :
    (((hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL t).startRecv
        ctx P t0 γ0 σv0 tn0).run h) =
      (StateT.run
        (match (match h.cache t0 with
          | some (tCached, σc, kVal) => if tCached = tn0 then some (σc, kVal) else none
          | none => none) with
        | some (σc, kVal) =>
          pure (some (some ((cka.receive γ0 tn0).1, resolveCorrRoot h t0 σc, fs.initReceiver kVal)))
        | none =>
          if (!(decide (qep + 1 < t0)) && lastLeakGuessAdmissible (2 + Δcka) tL t0) = true then
            if (tL.isSome && decide (t0 = healEpoch tL)) = true then
              pure none
            else if (postLeak tL ctx || h.corrRoot.isSome || decide (t < t0)) = true then
              match resolveCorrRoot h (t0 - 1) σv0 with
              | none => pure none
              | some σ =>
                pure (some (some ((cka.receive γ0 tn0).1,
                  some (prng.up σ (cka.receive γ0 tn0).2).1,
                  fs.initReceiver (prng.up σ (cka.receive γ0 tn0).2).2)))
            else if t0 = t then do
              let skOpt ← StateT.lift (PRFPRNG.challPrfQuery (State := RSt) (Input := I)
                (Output := K) (cka.receive γ0 tn0).2)
              match skOpt with
              | none => pure none
              | some (σOut, kOut) =>
                pure (some (some ((cka.receive γ0 tn0).1, some σOut, fs.initReceiver kOut)))
            else if (!decide (t0 < healEpoch tL)) = true then do
              let kOut ← lookupPRNGBucketAuthF t0 (cka.receive γ0 tn0).2
              pure (some (some ((cka.receive γ0 tn0).1, none, fs.initReceiver kOut)))
            else
              pure (some none)
          else
            pure (some none)) h) := by
  unfold hooksPRNGBucketAuthHybrid liftPBucketAuth; dsimp only
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rcases hcache : h.cache t0 with _ | ⟨tCached, σc, kVal⟩ <;> rfl

private theorem prngBucketAuthStartRecv_bounded [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L k Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (ctx : Ctx Γ T (Option RSt) SS RS M E) (P : Party) (t0 : ℕ) (γ0 : Γ)
    (σv0 : Option RSt) (tn0 : T) (h : PRNGBucketAuthState T RSt K I)
    (hInv : PBAInv L (k + 1) h) :
    ∀ res ∈ support (((hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL t).startRecv
        ctx P t0 γ0 σv0 tn0).run h),
      PBAInv L k res.2 := by
  intro res hmem
  rw [hooksPRNGBucketAuthHybrid_startRecv_run_eq] at hmem
  rcases hhon : (match h.cache t0 with
    | some (tCached, σc, kVal) => if tCached = tn0 then some (σc, kVal) else none
    | none => none) with _ | ⟨σc, kVal⟩
  · simp only [hhon] at hmem
    by_cases hc0 : (!(decide (qep + 1 < t0)) && lastLeakGuessAdmissible (2 + Δcka) tL t0) = true
    · simp only [hc0, ↓reduceIte] at hmem
      by_cases hc1 : (tL.isSome && decide (t0 = healEpoch tL)) = true
      · simp only [hc1, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; exact hInv.mono (Nat.le_succ k)
      · simp only [hc1, Bool.false_eq_true, ↓reduceIte] at hmem
        by_cases hc2 : (postLeak tL ctx || h.corrRoot.isSome || decide (t < t0)) = true
        · simp only [hc2, ↓reduceIte] at hmem
          rcases hres : resolveCorrRoot h (t0 - 1) σv0 with _ | σ <;>
            (simp only [hres, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem;
             subst hmem; exact hInv.mono (Nat.le_succ k))
        · simp only [hc2, Bool.false_eq_true, ↓reduceIte] at hmem
          by_cases hc3 : t0 = t
          · simp only [hc3, ↓reduceIte, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
              mem_support_bind_iff] at hmem
            obtain ⟨skOpt, _, hmem⟩ := hmem
            rcases skOpt with _ | ⟨σOut, kOut⟩ <;>
              (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem;
               subst hmem; exact hInv.mono (Nat.le_succ k))
          · simp only [hc3, ↓reduceIte] at hmem
            by_cases hc4 : (!decide (t0 < healEpoch tL)) = true
            · simp only [hc4, ↓reduceIte, StateT.run_bind, mem_support_bind_iff] at hmem
              obtain ⟨⟨kOut, h1⟩, hh1, hmem⟩ := hmem
              simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
              subst hmem
              exact hInv.step (lookupPRNGBucketAuthF_fTable_le t0 (cka.receive γ0 tn0).2 h
                (kOut, h1) hh1)
            · simp only [hc4, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, support_pure,
                Set.mem_singleton_iff] at hmem
              subst hmem; exact hInv.mono (Nat.le_succ k)
    · simp only [hc0, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hmem
      subst hmem; exact hInv.mono (Nat.le_succ k)
  · simp only [hhon, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; exact hInv.mono (Nat.le_succ k)

open _root_.CryptoGames.CKA (CKASort ckaOps) in
open _root_.CryptoGames.SM (orE_eval isSomeE_eval validGuessE_eval) in
open _root_.CryptoGames.SM.Engine
  (eval_bind_ret eval_ite eval_caseOpt eval_bind eval_ret cGsEnc optNatLit_eval) in
open _root_.CryptoGames.SM.Construction (query_challPrf_eval) in
private theorem prngBucketAuthStartRecvC_eval [DecidableEq T] [DecidableEq I]
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
    (L k Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) {Γ'}
    (hE : Expr OO Γ' pbaHsTy)
    (ctxE : Expr OO Γ' (cGsTy pbaVpTy))
    (pE : Expr OO Γ' .bool)
    (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' (.base .γ))
    (σvE : Expr OO Γ' (.opt (.base .sig)))
    (tnE : Expr OO Γ' (.base .t))
    (ρ : Env Γ') (h : PRNGBucketAuthState T RSt K I)
    (ctx : Ctx Γ T (Option RSt) SS RS M E) (P : Party)
    (hInv : PBAInv L (k + 1) h)
    (hh : hE.eval ρ = prngBucketAuthHsEnc h)
    (hctx : ctxE.eval ρ = cGsEnc (vpT := pbaVpTy) pbaVpEnc ctx) :
    (prngBucketAuthStartRecvC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L Δcka qep tL t hE ctxE pE tE γE σvE tnE).eval ρ =
      Prod.map id prngBucketAuthHsEnc <$>
        ((hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL t).startRecv
          ctx P (tE.eval ρ) (γE.eval ρ) (σvE.eval ρ) (tnE.eval ρ)).run h := by
  rw [hooksPRNGBucketAuthHybrid_startRecv_run_eq]
  unfold prngBucketAuthStartRecvC
  dsimp only
  rw [eval_bind_ret]
  set t0 : ℕ := tE.eval ρ
  set γ0 : Γ := γE.eval ρ
  set σv0 : Option RSt := σvE.eval ρ
  set tn0 : T := tnE.eval ρ
  have h0 : (Expr.pair hE (.pair ctxE (.pair tE (.pair γE (.pair σvE tnE))))).eval ρ =
      (prngBucketAuthHsEnc h, cGsEnc (vpT := pbaVpTy) pbaVpEnc ctx, t0, γ0, σv0, tn0) := by
    simp [Expr.eval, hh, hctx, t0, γ0, σv0, tn0]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod pbaHsTy (.prod (cGsTy pbaVpTy)
      (.prod .nat (.prod (.base CKASort.γ) (.prod (.opt (.base CKASort.sig)) (.base CKASort.t))))))
    (prngBucketAuthHsEnc h, cGsEnc (vpT := pbaVpTy) pbaVpEnc ctx, t0, γ0, σv0, tn0) ρ
  rw [eval_caseOpt]
  have hHon :
      (match (pbaHsCache (.fst (Expr.v0 (O := OO)))).eval ρ₁ t0 with
       | none => none
       | some (tCached, entry) =>
         if (tCached == tn0) = true then some entry else none) =
      (match h.cache t0 with
       | some (tCached, σc, kVal) => if tCached = tn0 then some (σc, kVal) else none
       | none => none) := by
    rcases hcache : h.cache t0 with _ | ⟨tCached, σc, kVal⟩
    · simp [ρ₁, pbaHsCache, prngBucketAuthHsEnc, hcache, Expr.eval, Expr.v0]
    · by_cases hEqT : tCached = tn0 <;>
        simp [ρ₁, pbaHsCache, prngBucketAuthHsEnc, hcache, hEqT, BEq.beq, Expr.eval, Expr.v0]
  have hHonVal :
      (Expr.caseOpt (.tget (pbaHsCache (.fst (Expr.v0 (O := OO)))) (.fst (.snd (.snd .v0)))) .none
        (.ite (.op (O := OO) CKAOp.eqT (.pair (.fst .v0) (.snd (.snd (.snd (.snd (.snd .v1)))))))
          (.some (.snd .v0)) .none)).eval ρ₁ =
      (match h.cache t0 with
         | some (tCached, σc, kVal) => if tCached = tn0 then some (σc, kVal) else none
         | none => none) := by
    rw [← hHon]
    rcases hcache : h.cache t0 with _ | ⟨tCached, σc, kVal⟩
    · simp [ρ₁, pbaHsCache, prngBucketAuthHsEnc, hcache, Expr.eval, Expr.v0]
    · simp [ρ₁, pbaHsCache, prngBucketAuthHsEnc, prngOps, ckaOps, heqT, hcache,
        Expr.eval, Expr.v0, Expr.v1]
  rw [hHonVal]; clear hHon hHonVal
  rcases hhon : (match h.cache t0 with
    | some (tCached, σc, kVal) => if tCached = tn0 then some (σc, kVal) else none
    | none => none) with _ | ⟨σc, kVal⟩ <;> (rw [hhon]; dsimp only)
  · rw [eval_ite]
    have hCond0 :
        (Expr.and (.not (.lt (.nat (qep + 1)) (.fst (.snd (.snd (Expr.v0 (O := OO)))))))
          (validGuessE (2 + Δcka) (optNatLit tL) (.fst (.snd (.snd .v0))))).eval ρ₁ =
        (!decide (qep + 1 < t0) && lastLeakGuessAdmissible (2 + Δcka) tL t0) := by
      simp [ρ₁, validGuessE_eval, optNatLit_eval, Expr.eval, Expr.v0]
    rw [hCond0]; clear hCond0
    by_cases hc0 : (!decide (qep + 1 < t0) && lastLeakGuessAdmissible (2 + Δcka) tL t0) = true
    · simp only [hc0, ↓reduceIte]
      rw [eval_ite]
      have hCond1 :
          (Expr.and (.bool tL.isSome)
            (.eqN (.fst (.snd (.snd (Expr.v0 (O := OO))))) (.nat (healEpoch tL)))).eval ρ₁ =
          (tL.isSome && decide (t0 = healEpoch tL)) := rfl
      rw [hCond1]; clear hCond1
      by_cases hc1 : (tL.isSome && decide (t0 = healEpoch tL)) = true
      · simp [ρ₁, hc1, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
      · simp only [hc1, Bool.false_eq_true, ↓reduceIte]
        rw [eval_ite]
        have hPl := postLeakBucketE_eval (O := OO) pbaVpEnc tL (.fst (.snd .v0)) ρ₁ ctx rfl
        have hCond2 :
            (orE (postLeakBucketE tL (.fst (.snd (Expr.v0 (O := OO)))))
              (orE (isSomeE (pbaHsCorrRoot (.fst .v0))) (.lt (.nat t) (.fst (.snd (.snd .v0)))))).eval ρ₁ =
            (postLeak tL ctx || h.corrRoot.isSome || decide (t < t0)) := by
          simp only [orE_eval, isSomeE_eval, hPl, Bool.or_assoc]
          simp [ρ₁, pbaHsCorrRoot, prngBucketAuthHsEnc, Expr.eval, Expr.v0]
        rw [hCond2]; clear hCond2 hPl
        by_cases hc2 : (postLeak tL ctx || h.corrRoot.isSome || decide (t < t0)) = true
        · simp only [hc2, ↓reduceIte, eval_caseOpt]
          have hRes := resolveCorrRootE_eval (O := OO) (.fst .v0)
            (.sub (.fst (.snd (.snd .v0))) (.nat 1))
            (.fst (.snd (.snd (.snd (.snd .v0))))) ρ₁ h rfl
          change (resolveCorrRootE _ _ _).eval ρ₁ = resolveCorrRoot h (t0 - 1) σv0 at hRes
          rw [hRes]
          rcases resolveCorrRoot h (t0 - 1) σv0 with _ | σ
          · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
          · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, prngOps, ckaOps,
              hRecv, hPrngUp, hFsInitR, Expr.eval, Expr.v0, Expr.v1]
        · simp only [hc2, Bool.false_eq_true, ↓reduceIte]
          rw [eval_ite]
          have hCond3 :
              (Expr.eqN (.fst (.snd (.snd (Expr.v0 (O := OO))))) (.nat t)).eval ρ₁ =
              decide (t0 = t) := rfl
          rw [hCond3]; clear hCond3
          by_cases hc3 : t0 = t
          · have hc3If : (t0 = t) ↔ True := by simp [hc3]
            simp only [hc3If, decide_true, ↓reduceIte, eval_bind, query_challPrf_eval,
              StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind]
            have hIk : (Expr.snd (.op (O := OO) CKAOp.ckaReceive
                (.pair (.fst (.snd (.snd (.snd .v0))))
                  (.snd (.snd (.snd (.snd (.snd .v0)))))))).eval ρ₁ =
                (cka.receive γ0 tn0).2 := by
              simp [ρ₁, prngOps, ckaOps, hRecv, Expr.eval, Expr.v0]
            rw [hIk]
            refine bind_congr fun skOpt => ?_
            rw [eval_caseOpt]
            rcases skOpt with _ | ⟨σOut, kOut⟩
            · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v1]
            · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, prngOps, ckaOps,
                hRecv, hFsInitR, Expr.eval, Expr.v0, Expr.v2]
          · simp only [hc3, decide_false, Bool.false_eq_true, ↓reduceIte]
            rw [eval_ite]
            have hCond4 :
                (Expr.not (.lt (.fst (.snd (.snd (Expr.v0 (O := OO))))) (.nat (healEpoch tL)))).eval ρ₁ =
                (!decide (t0 < healEpoch tL)) := rfl
            rw [hCond4]; clear hCond4
            by_cases hc4 : (!decide (t0 < healEpoch tL)) = true
            · simp only [hc4, ↓reduceIte, eval_bind, StateT.run_bind, map_bind]
              have hLk := (lookupPRNGBucketAuthFC_eval
                (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
                (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
                (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
                (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
                (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
                (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
                (sampI := sampI) (sampK := sampK)
                heqI hSampK L (.fst .v0) (.fst (.snd (.snd .v0)))
                (.snd (.op (O := OO) CKAOp.ckaReceive (.pair (.fst (.snd (.snd (.snd .v0))))
                  (.snd (.snd (.snd (.snd (.snd .v0))))))))
                ρ₁ h rfl (hInv.len_le t0)).1
              have hIk : (Expr.snd (.op (O := OO) CKAOp.ckaReceive
                  (.pair (.fst (.snd (.snd (.snd .v0))))
                    (.snd (.snd (.snd (.snd (.snd .v0)))))))).eval ρ₁ =
                  (cka.receive γ0 tn0).2 := by
                simp [ρ₁, prngOps, ckaOps, hRecv, Expr.eval, Expr.v0]
              rw [hIk] at hLk
              change (lookupPRNGBucketAuthFC _ _ _ _).eval ρ₁ =
                Prod.map id prngBucketAuthHsEnc <$>
                  (lookupPRNGBucketAuthF (T := T) (Sig := RSt) t0 (cka.receive γ0 tn0).2).run h at hLk
              rw [hLk, bind_map_left]
              refine bind_congr fun ⟨kOut, h1⟩ => ?_
              simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, prngOps, ckaOps,
                hRecv, hFsInitR, Expr.eval, Expr.v0, Expr.v1]
            · simp [ρ₁, hc4, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
    · simp [ρ₁, hc0, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
  · set ρ₂ := Env.cons (t := .prod (.opt (.base CKASort.sig)) (.base CKASort.k)) (σc, kVal) ρ₁
    change (Comp.ret _).eval ρ₂ = _
    have hRes := resolveCorrRootE_eval (O := OO) (.fst .v1) (.fst (.snd (.snd .v1)))
      (.fst .v0) ρ₂ h rfl
    change (resolveCorrRootE _ _ _).eval ρ₂ = resolveCorrRoot h t0 σc at hRes
    simp only [eval_ret, Expr.eval, hRes]
    simp [ρ₂, ρ₁, prngOps, ckaOps, hRecv, hFsInitR, StateT.run_pure, Prod.map,
      Expr.eval, Expr.v0, Expr.v1]

open _root_.CryptoGames.CKA (CKASort ckaOps ckaPsEnc) in
open _root_.CryptoGames.SM (isSomeE_eval maxN_eval validGuessE_eval) in
open _root_.CryptoGames.SM.Engine
  (eval_bind_ret eval_ite eval_caseOpt eval_bind eval_ret cGsEnc vpTblEnc vpEnc
   cGsEpoch vpTcurNat vpRoot vpΓ vpVS vpVR realPartyE_eval) in
open _root_.CryptoGames.SM.Construction (query_prngCorr_eval) in
private theorem prngBucketAuthRevealC_eval [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) {Γ'}
    (hE : Expr OO Γ' pbaHsTy)
    (ctxE : Expr OO Γ' (cGsTy pbaVpTy))
    (pE : Expr OO Γ' .bool)
    (vpE : Expr OO Γ' pbaVpTy)
    (ρ : Env Γ') (h : PRNGBucketAuthState T RSt K I)
    (ctx : Ctx Γ T (Option RSt) SS RS M E)
    (P : Party) (vp : VP Γ T (Option RSt) SS RS)
    (hh : hE.eval ρ = prngBucketAuthHsEnc h)
    (hctx : ctxE.eval ρ = cGsEnc (vpT := pbaVpTy) pbaVpEnc ctx)
    (hvp : vpE.eval ρ = pbaVpEnc vp) :
    (prngBucketAuthRevealC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) tL hE ctxE pE vpE).eval ρ =
      Prod.map (Option.map ckaPsEnc) prngBucketAuthHsEnc <$>
        ((hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL t).reveal ctx P vp).run h ∧
    ∀ res ∈ support (((hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL t).reveal ctx P vp).run h),
      res.2.fTable = h.fTable := by
  unfold prngBucketAuthRevealC hooksPRNGBucketAuthHybrid liftPBucketAuth
  dsimp only
  rw [eval_bind_ret]
  have h0 : (Expr.pair hE (.pair ctxE vpE)).eval ρ =
      (prngBucketAuthHsEnc h, cGsEnc (vpT := pbaVpTy) pbaVpEnc ctx, pbaVpEnc vp) := by
    simp [Expr.eval, hh, hctx, hvp]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod pbaHsTy (.prod (cGsTy pbaVpTy) pbaVpTy))
    (prngBucketAuthHsEnc h, cGsEnc (vpT := pbaVpTy) pbaVpEnc ctx, pbaVpEnc vp) ρ
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [eval_caseOpt]
  have hRes := resolveCorrRootE_eval (O := OO) (.fst .v0) (vpTcurNat (.snd (.snd .v0)))
    (vpRoot (.snd (.snd .v0))) ρ₁ h rfl
  have hTcur : (vpTcurNat (.snd (.snd (Expr.v0 (O := OO))))).eval ρ₁ = vp.tcur := by
    simp [ρ₁, vpTcurNat, pbaVpEnc, vpTblEnc, vpEnc, Expr.eval, Expr.v0]
  have hRoot : (vpRoot (.snd (.snd (Expr.v0 (O := OO))))).eval ρ₁ = vp.root := by
    simp [ρ₁, vpRoot, pbaVpEnc, vpTblEnc, vpEnc, Expr.eval, Expr.v0]
  rw [hTcur, hRoot] at hRes
  rw [hRes]; clear hRes
  have hNotIsSome : (!h.corrRoot.isSome) = h.corrRoot.isNone := by cases h.corrRoot <;> rfl
  rcases resolveCorrRoot h vp.tcur vp.root with _ | σ
  · refine ⟨?_, ?_⟩
    · rw [eval_ite]
      have hPl := postLeakBucketE_eval (O := OO) pbaVpEnc tL (.fst (.snd .v0)) ρ₁ ctx rfl
      have hMax : (maxN (.fst (cGsEpoch (.fst (.snd (Expr.v0 (O := OO))))))
          (.snd (cGsEpoch (.fst (.snd .v0))))).eval ρ₁ = max (ctx.epoch .A) (ctx.epoch .B) := by
        simp [ρ₁, maxN_eval, cGsEpoch, cGsEnc, Expr.eval, Expr.v0]
      have hCond :
          (Expr.and (.and (.and (.not (postLeakBucketE tL (.fst (.snd (Expr.v0 (O := OO))))))
              (.not (isSomeE (pbaHsCorrRoot (.fst .v0)))))
              (.not (.lt (vpTcurNat (.snd (.snd .v0))) (.nat (healEpoch tL)))))
            (.eqN (vpTcurNat (.snd (.snd .v0)))
              (maxN (.fst (cGsEpoch (.fst (.snd .v0)))) (.snd (cGsEpoch (.fst (.snd .v0))))))).eval ρ₁ =
          (!postLeak tL ctx && h.corrRoot.isNone && !decide (vp.tcur < healEpoch tL) &&
            (vp.tcur == max (ctx.epoch .A) (ctx.epoch .B))) := by
        simp only [Expr.eval, hPl, hTcur, hMax, isSomeE_eval]
        simp [ρ₁, pbaHsCorrRoot, prngBucketAuthHsEnc, hNotIsSome, BEq.beq,
          Expr.eval, Expr.v0]
      rw [hCond]; clear hCond
      by_cases hc : (!postLeak tL ctx && h.corrRoot.isNone && !decide (vp.tcur < healEpoch tL) &&
          (vp.tcur == max (ctx.epoch .A) (ctx.epoch .B))) = true
      · simp only [hc, ↓reduceIte, eval_bind, query_prngCorr_eval,
          StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind]
        refine bind_congr fun σOpt => ?_
        rw [eval_caseOpt]
        rcases σOpt with _ | σOut
        · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0, Expr.v1]
        · simp only [Expr.eval, Expr.v0]
          set ρ₂ := Env.cons (t := .base CKASort.sig) σOut
            (Env.cons (t := .opt (.base CKASort.sig)) (some σOut) ρ₁)
          change (Comp.ret _).eval ρ₂ = _
          have hRP := realPartyE_eval (O' := OO) (.snd (.snd .v2)) (vpΓ (.snd (.snd .v2))) .v0
            (vpVS (.snd (.snd .v2))) (vpVR (.snd (.snd .v2))) ρ₂ vp rfl
          have hΓ : (vpΓ (.snd (.snd (Expr.v2 (O := OO))))).eval ρ₂ = vp.γ := by
            simp [ρ₂, ρ₁, vpΓ, pbaVpEnc, vpTblEnc, vpEnc, Expr.eval, Expr.v2]
          have hVS : (vpVS (.snd (.snd (Expr.v2 (O := OO))))).eval ρ₂ = vp.vS := by
            simp [ρ₂, ρ₁, vpVS, pbaVpEnc, vpTblEnc, vpEnc, Expr.eval, Expr.v2]
          have hVR : (vpVR (.snd (.snd (Expr.v2 (O := OO))))).eval ρ₂ = vp.vR := by
            simp [ρ₂, ρ₁, vpVR, pbaVpEnc, vpTblEnc, vpEnc, Expr.eval, Expr.v2]
          have hTcur2 : (vpTcurNat (.snd (.snd (Expr.v2 (O := OO))))).eval ρ₂ = vp.tcur := by
            simp [ρ₂, ρ₁, vpTcurNat, pbaVpEnc, vpTblEnc, vpEnc, Expr.eval, Expr.v2]
          dsimp only [Expr.v0, Expr.v1, Expr.v2] at hRP hΓ hVS hVR hTcur2
          rw [hΓ, hVS, hVR] at hRP
          rw [eval_ret]
          simp [ρ₂, ρ₁,
            pbaHsSetCorrRoot, pbaHsCache, pbaHsFTbl, prngBucketAuthHsEnc,
            StateT.run_modify, Prod.map,
            Expr.eval, Expr.v2]
          exact ⟨hRP, hTcur2⟩
      · simp [ρ₁, hc, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
    · intro res hmem
      by_cases hc : (!postLeak tL ctx && h.corrRoot.isNone && !decide (vp.tcur < healEpoch tL) &&
          (vp.tcur == max (ctx.epoch .A) (ctx.epoch .B))) = true
      · simp only [hc, ↓reduceIte, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
          mem_support_bind_iff] at hmem
        obtain ⟨σOpt, _, hmem⟩ := hmem
        rcases σOpt with _ | σOut
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
          subst hmem; rfl
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff] at hmem
          subst hmem; rfl
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at hmem
        subst hmem; rfl
  · refine ⟨?_, ?_⟩
    · set ρ₂ := Env.cons (t := .base CKASort.sig) σ ρ₁
      change (Comp.ret _).eval ρ₂ = _
      have hRP := realPartyE_eval (O' := OO) (.snd (.snd .v1)) (vpΓ (.snd (.snd .v1))) .v0
        (vpVS (.snd (.snd .v1))) (vpVR (.snd (.snd .v1))) ρ₂ vp rfl
      have hΓ : (vpΓ (.snd (.snd (Expr.v1 (O := OO))))).eval ρ₂ = vp.γ := by
        simp [ρ₂, ρ₁, vpΓ, pbaVpEnc, vpTblEnc, vpEnc, Expr.eval, Expr.v1]
      have hVS : (vpVS (.snd (.snd (Expr.v1 (O := OO))))).eval ρ₂ = vp.vS := by
        simp [ρ₂, ρ₁, vpVS, pbaVpEnc, vpTblEnc, vpEnc, Expr.eval, Expr.v1]
      have hVR : (vpVR (.snd (.snd (Expr.v1 (O := OO))))).eval ρ₂ = vp.vR := by
        simp [ρ₂, ρ₁, vpVR, pbaVpEnc, vpTblEnc, vpEnc, Expr.eval, Expr.v1]
      have hTcur2 : (vpTcurNat (.snd (.snd (Expr.v1 (O := OO))))).eval ρ₂ = vp.tcur := by
        simp [ρ₂, ρ₁, vpTcurNat, pbaVpEnc, vpTblEnc, vpEnc, Expr.eval, Expr.v1]
      dsimp only [Expr.v0, Expr.v1] at hRP hΓ hVS hVR hTcur2
      rw [hΓ, hVS, hVR] at hRP
      rw [eval_ret]
      rcases hcr : h.corrRoot with _ | cr
      · simp only [ρ₂, ρ₁, prngBucketAuthHsEnc, hcr] at hRP hTcur2
        by_cases hlt : vp.tcur < healEpoch tL
        · simp [ρ₂, ρ₁, isSomeE_eval, hcr, hlt,
            pbaHsSetCorrRoot, pbaHsCache, pbaHsFTbl, pbaHsCorrRoot,
            prngBucketAuthHsEnc, StateT.run_pure,
            Prod.map, Expr.eval, Expr.v0, Expr.v1]
          exact ⟨hRP, hTcur2.symm ▸ hlt⟩
        · simp [ρ₂, ρ₁, isSomeE_eval, hcr, hlt,
            pbaHsSetCorrRoot, pbaHsCache, pbaHsFTbl, pbaHsCorrRoot,
            prngBucketAuthHsEnc, StateT.run_modify,
            Prod.map, Expr.eval, Expr.v0, Expr.v1]
          rw [hTcur2]
          refine ⟨hRP, ?_⟩
          have hle : healEpoch tL ≤ vp.tcur := Nat.le_of_not_lt hlt
          simp [hle]
      · simp only [ρ₂, ρ₁, prngBucketAuthHsEnc, hcr] at hRP
        simp [ρ₂, ρ₁, isSomeE_eval, hcr,
          pbaHsCorrRoot,
          prngBucketAuthHsEnc, StateT.run_pure,
          Prod.map, Expr.eval, Expr.v0, Expr.v1]
        exact hRP
    · intro res hmem
      by_cases hc : (!decide (vp.tcur < healEpoch tL) && h.corrRoot.isNone) = true
      · simp only [hc, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
          pure_bind, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; rfl
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at hmem
        subst hmem; rfl

open _root_.CryptoGames.CKA (ckaOps) in
open _root_.CryptoGames.SM (letE_eval) in
private theorem isHonestHdrPRNGBucketE_eval [DecidableEq T]
    (heqT : eqT = (· == ·)) {Γ'}
    (hE : Expr OO Γ' pbaHsTy) (hdrE : Expr OO Γ' hdrTy)
    (ρ : Env Γ') (h : PRNGBucketAuthState T RSt K I) (hdr : Header T)
    (hh : hE.eval ρ = prngBucketAuthHsEnc h)
    (hhdr : hdrE.eval ρ = hdr) :
    (isHonestHdrPRNGBucketE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) hE hdrE).eval ρ =
      isHonestHdrPRNGBucket h hdr := by
  unfold isHonestHdrPRNGBucketE isHonestHdrPRNGBucket
  rw [letE_eval]
  rcases hdr with ⟨ep0, _ | tn0⟩
  · rcases hcache : h.cache ep0 with _ | ⟨tCached, σc, kVal⟩ <;>
      simp [hhdr, Expr.eval, Expr.v0]
  · rcases hcache : h.cache ep0 with _ | ⟨tCached, σc, kVal⟩ <;>
      simp [prngBucketAuthHsEnc, pbaHsCache, prngOps, ckaOps, heqT, hh, hhdr, hcache,
        Expr.eval, Expr.v0, Expr.v1]

private theorem hooksPRNGBucketAuthMain_startRecv_run_eq [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (ctx : Ctx Γ T (Option RSt) SS RS M E) (P : Party) (t0 : ℕ) (γ0 : Γ)
    (σv0 : Option RSt) (tn0 : T) (h : PRNGBucketAuthState T RSt K I) :
    (((hooksPRNGBucketAuthMain cka prng fs Δcka qep tL t).startRecv
        ctx P t0 γ0 σv0 tn0).run h) =
      (StateT.run
        (match (match h.cache t0 with
          | some (tCached, σc, kVal) => if tCached = tn0 then some (σc, kVal) else none
          | none => none) with
        | some (σc, kVal) =>
          pure (some (some ((cka.receive γ0 tn0).1, resolveCorrRoot h t0 σc, fs.initReceiver kVal)))
        | none =>
          if (!decide (qep + 1 < t0) && lastLeakGuessAdmissible (2 + Δcka) tL t0 &&
              (tL.isSome && decide (t0 = healEpoch tL))) = true then
            pure none
          else
            pure (some none)) h) := by
  unfold hooksPRNGBucketAuthMain; dsimp only
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rcases hcache : h.cache t0 with _ | ⟨tCached, σc, kVal⟩ <;> rfl

open _root_.CryptoGames.CKA (CKASort ckaOps) in
open _root_.CryptoGames.SM (validGuessE_eval) in
open _root_.CryptoGames.SM.Engine
  (eval_bind_ret eval_ite eval_caseOpt eval_ret cGsEnc optNatLit_eval) in
private theorem prngBucketAuthMainStartRecvC_eval [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (hRecv : ckaReceive = cka.receive)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (heqT : eqT = (· == ·))
    (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) {Γ'}
    (hE : Expr OO Γ' pbaHsTy)
    (ctxE : Expr OO Γ' (cGsTy pbaVpTy))
    (pE : Expr OO Γ' .bool)
    (tE : Expr OO Γ' .nat)
    (γE : Expr OO Γ' (.base .γ))
    (σvE : Expr OO Γ' (.opt (.base .sig)))
    (tnE : Expr OO Γ' (.base .t))
    (ρ : Env Γ') (h : PRNGBucketAuthState T RSt K I)
    (ctx : Ctx Γ T (Option RSt) SS RS M E) (P : Party)
    (hh : hE.eval ρ = prngBucketAuthHsEnc h) :
    (prngBucketAuthMainStartRecvC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) Δcka qep tL hE ctxE pE tE γE σvE tnE).eval ρ =
      Prod.map id prngBucketAuthHsEnc <$>
        ((hooksPRNGBucketAuthMain cka prng fs Δcka qep tL t).startRecv
          ctx P (tE.eval ρ) (γE.eval ρ) (σvE.eval ρ) (tnE.eval ρ)).run h := by
  rw [hooksPRNGBucketAuthMain_startRecv_run_eq]
  unfold prngBucketAuthMainStartRecvC
  dsimp only
  rw [eval_bind_ret]
  set t0 : ℕ := tE.eval ρ
  set γ0 : Γ := γE.eval ρ
  set tn0 : T := tnE.eval ρ
  have h0 : (Expr.pair hE (.pair tE (.pair γE tnE))).eval ρ =
      (prngBucketAuthHsEnc h, t0, γ0, tn0) := by
    simp [Expr.eval, hh, t0, γ0, tn0]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod pbaHsTy (.prod .nat (.prod (.base CKASort.γ) (.base CKASort.t))))
    (prngBucketAuthHsEnc h, t0, γ0, tn0) ρ
  rw [eval_caseOpt]
  have hHon :
      (match (pbaHsCache (.fst (Expr.v0 (O := OO)))).eval ρ₁ t0 with
       | none => none
       | some (tCached, entry) =>
         if (tCached == tn0) = true then some entry else none) =
      (match h.cache t0 with
       | some (tCached, σc, kVal) => if tCached = tn0 then some (σc, kVal) else none
       | none => none) := by
    rcases hcache : h.cache t0 with _ | ⟨tCached, σc, kVal⟩
    · simp [ρ₁, pbaHsCache, prngBucketAuthHsEnc, hcache, Expr.eval, Expr.v0]
    · by_cases hEqT : tCached = tn0 <;>
        simp [ρ₁, pbaHsCache, prngBucketAuthHsEnc, hcache, hEqT, BEq.beq, Expr.eval, Expr.v0]
  have hHonVal :
      (Expr.caseOpt (.tget (pbaHsCache (.fst (Expr.v0 (O := OO)))) (.fst (.snd .v0))) .none
        (.ite (.op (O := OO) CKAOp.eqT (.pair (.fst .v0) (.snd (.snd (.snd .v1)))))
          (.some (.snd .v0)) .none)).eval ρ₁ =
      (match h.cache t0 with
         | some (tCached, σc, kVal) => if tCached = tn0 then some (σc, kVal) else none
         | none => none) := by
    rw [← hHon]
    rcases hcache : h.cache t0 with _ | ⟨tCached, σc, kVal⟩
    · simp [ρ₁, pbaHsCache, prngBucketAuthHsEnc, hcache, Expr.eval, Expr.v0]
    · simp [ρ₁, pbaHsCache, prngBucketAuthHsEnc, prngOps, ckaOps, heqT, hcache,
        Expr.eval, Expr.v0, Expr.v1]
  rw [hHonVal]; clear hHon hHonVal
  rcases hhon : (match h.cache t0 with
    | some (tCached, σc, kVal) => if tCached = tn0 then some (σc, kVal) else none
    | none => none) with _ | ⟨σc, kVal⟩ <;> (rw [hhon]; dsimp only)
  · rw [eval_ite]
    have hCond :
        (Expr.and
          (.and (.not (.lt (.nat (qep + 1)) (.fst (.snd (Expr.v0 (O := OO))))))
            (validGuessE (2 + Δcka) (optNatLit tL) (.fst (.snd .v0))))
          (.and (.bool tL.isSome) (.eqN (.fst (.snd .v0)) (.nat (healEpoch tL))))).eval ρ₁ =
        (!decide (qep + 1 < t0) && lastLeakGuessAdmissible (2 + Δcka) tL t0 &&
          (tL.isSome && decide (t0 = healEpoch tL))) := by
      simp [ρ₁, validGuessE_eval, optNatLit_eval, Expr.eval, Expr.v0]
    rw [hCond]; clear hCond
    by_cases hc : (!decide (qep + 1 < t0) && lastLeakGuessAdmissible (2 + Δcka) tL t0 &&
        (tL.isSome && decide (t0 = healEpoch tL))) = true
    · simp only [hc, ↓reduceIte]
      simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
  · set ρ₂ := Env.cons (t := .prod (.opt (.base CKASort.sig)) (.base CKASort.k)) (σc, kVal) ρ₁
    change (Comp.ret _).eval ρ₂ = _
    have hRes := resolveCorrRootE_eval (O := OO) (.fst .v1) (.fst (.snd .v1))
      (.fst .v0) ρ₂ h rfl
    change (resolveCorrRootE _ _ _).eval ρ₂ = resolveCorrRoot h t0 σc at hRes
    simp only [eval_ret, Expr.eval, hRes]
    simp [ρ₂, ρ₁, prngOps, ckaOps, hRecv, hFsInitR, StateT.run_pure, Prod.map,
      Expr.eval, Expr.v0, Expr.v1]

open _root_.CryptoGames.CKA (CKASort ckaPsEnc) in
open _root_.CryptoGames.SM (orE_eval maxN_eval) in
open _root_.CryptoGames.SM.Engine
  (eval_bind_ret eval_ite eval_caseOpt eval_ret cGsEnc vpTblEnc vpEnc
   cGsEpoch vpTcurNat vpRoot vpΓ vpVS vpVR realPartyE_eval) in
private theorem prngBucketAuthForgedHdrRevealC_eval [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) {Γ'}
    (hE : Expr OO Γ' pbaHsTy)
    (ctxE : Expr OO Γ' (cGsTy pbaVpTy))
    (pE : Expr OO Γ' .bool)
    (vpE : Expr OO Γ' pbaVpTy)
    (ρ : Env Γ') (h : PRNGBucketAuthState T RSt K I)
    (ctx : Ctx Γ T (Option RSt) SS RS M E)
    (P : Party) (vp : VP Γ T (Option RSt) SS RS)
    (hh : hE.eval ρ = prngBucketAuthHsEnc h)
    (hctx : ctxE.eval ρ = cGsEnc (vpT := pbaVpTy) pbaVpEnc ctx)
    (hvp : vpE.eval ρ = pbaVpEnc vp) :
    (prngBucketAuthForgedHdrRevealC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) tL hE ctxE pE vpE).eval ρ =
      Prod.map (Option.map ckaPsEnc) prngBucketAuthHsEnc <$>
        ((hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep tL t).reveal ctx P vp).run h := by
  unfold prngBucketAuthForgedHdrRevealC hooksPRNGBucketAuthForgedHdr
  dsimp only
  rw [eval_bind_ret]
  have h0 : (Expr.pair hE (.pair ctxE vpE)).eval ρ =
      (prngBucketAuthHsEnc h, cGsEnc (vpT := pbaVpTy) pbaVpEnc ctx, pbaVpEnc vp) := by
    simp [Expr.eval, hh, hctx, hvp]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod pbaHsTy (.prod (cGsTy pbaVpTy) pbaVpTy))
    (prngBucketAuthHsEnc h, cGsEnc (vpT := pbaVpTy) pbaVpEnc ctx, pbaVpEnc vp) ρ
  rw [eval_ite]
  have hTcur : (vpTcurNat (.snd (.snd (Expr.v0 (O := OO))))).eval ρ₁ = vp.tcur := by
    simp [ρ₁, vpTcurNat, pbaVpEnc, vpTblEnc, vpEnc, Expr.eval, Expr.v0]
  have hMax : (maxN (.fst (cGsEpoch (.fst (.snd (Expr.v0 (O := OO))))))
      (.snd (cGsEpoch (.fst (.snd .v0))))).eval ρ₁ = max (ctx.epoch .A) (ctx.epoch .B) := by
    simp [ρ₁, maxN_eval, cGsEpoch, cGsEnc, Expr.eval, Expr.v0]
  have hCond :
      (orE (.not (.lt (vpTcurNat (.snd (.snd (Expr.v0 (O := OO))))) (.nat (healEpoch tL))))
        (.not (.lt (maxN (.fst (cGsEpoch (.fst (.snd .v0))))
          (.snd (cGsEpoch (.fst (.snd .v0))))) (.nat (healEpoch tL))))).eval ρ₁ =
      (!decide (vp.tcur < healEpoch tL) ||
        !decide (max (ctx.epoch .A) (ctx.epoch .B) < healEpoch tL)) := by
    simp [orE_eval, hTcur, hMax, Expr.eval]
  rw [hCond]; clear hCond
  by_cases hc : (!decide (vp.tcur < healEpoch tL) ||
      !decide (max (ctx.epoch .A) (ctx.epoch .B) < healEpoch tL)) = true
  · simp only [hc, ↓reduceIte]
    simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]
    rw [eval_caseOpt]
    have hRoot : (vpRoot (.snd (.snd (Expr.v0 (O := OO))))).eval ρ₁ = vp.root := by
      simp [ρ₁, vpRoot, pbaVpEnc, vpTblEnc, vpEnc, Expr.eval, Expr.v0]
    rw [hRoot]
    rcases hvr : vp.root with _ | σ
    · simp [ρ₁, Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v0]
    · set ρ₂ := Env.cons (t := .base CKASort.sig) σ ρ₁
      change (Comp.ret _).eval ρ₂ = _
      have hRP := realPartyE_eval (O' := OO) (.snd (.snd .v1)) (vpΓ (.snd (.snd .v1))) .v0
        (vpVS (.snd (.snd .v1))) (vpVR (.snd (.snd .v1))) ρ₂ vp rfl
      have hΓ : (vpΓ (.snd (.snd (Expr.v1 (O := OO))))).eval ρ₂ = vp.γ := by
        simp [ρ₂, ρ₁, vpΓ, pbaVpEnc, vpTblEnc, vpEnc, Expr.eval, Expr.v1]
      have hVS : (vpVS (.snd (.snd (Expr.v1 (O := OO))))).eval ρ₂ = vp.vS := by
        simp [ρ₂, ρ₁, vpVS, pbaVpEnc, vpTblEnc, vpEnc, Expr.eval, Expr.v1]
      have hVR : (vpVR (.snd (.snd (Expr.v1 (O := OO))))).eval ρ₂ = vp.vR := by
        simp [ρ₂, ρ₁, vpVR, pbaVpEnc, vpTblEnc, vpEnc, Expr.eval, Expr.v1]
      dsimp only [Expr.v0, Expr.v1] at hRP hΓ hVS hVR
      rw [hΓ, hVS, hVR] at hRP
      rw [eval_ret]
      simp [ρ₂, ρ₁, StateT.run_pure, Prod.map, Expr.eval, Expr.v1]
      exact hRP

open _root_.CryptoGames.SM (validGuessE_eval) in
open _root_.CryptoGames.SM.Engine (ConfigECAgrees optNatLit_eval) in
private theorem bucketAuthCfgEC_agrees (Δcka : ℕ) (tL : Option ℕ) :
    ConfigECAgrees
      (bucketAuthCfgEC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) Δcka tL)
      (bucketAuthCfg (M := M) Δcka tL) where
  deliverWin_eq := rfl
  injectFull_eq {_} e ρ := by
    simp [bucketAuthCfgEC, bucketAuthCfg, validGuessE_eval, optNatLit_eval]
  challOK_eq {_} _ _ := rfl
  challMsg_eq {_} _ _ _ _ _ := by
    simp only [bucketAuthCfgEC, bucketAuthCfg, Expr.eval, Option.getD_none]

private def hkPbaMode [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) :
    Bool → Hooks (PRFPRNG.spec RSt I K) (PRNGBucketAuthState T RSt K I)
      Γ T RSt SS RS M E CCoins Γ (Option RSt) SS RS
  | true => hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep tL t
  | false => hooksPRNGBucketAuthMain cka prng fs Δcka qep tL t

private def hkPbaModeC (L B Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) :
    Bool → HooksC OO II (.base .γ) (.opt (.base .sig)) (.base .ss) (.base .rs) pbaHsTy
  | true =>
    hooksPRNGBucketAuthForgedHdrC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B Δcka qep tL t
  | false =>
    hooksPRNGBucketAuthMainC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B Δcka qep tL t

private theorem hkPbaMode_vrInv [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) (fm : Bool)
    {VROkStep : ℕ → RS → Prop}
    (hVRHk : HooksVRInv VROkStep (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL t))
    (hInitR : ∀ k, VROkStep 0 (fs.initReceiver k)) :
    HooksVRInv VROkStep (hkPbaMode cka prng fs Δcka qep tL t fm) := by
  cases fm
  · refine ⟨hVRHk.mono, ?_, hVRHk.fsRecv_step, hVRHk.commit_vR⟩
    intro ctx P t0 γ0 σv0 tn0 h res hmem γ' σ' rs hrs
    dsimp only [hkPbaMode] at hmem
    rw [hooksPRNGBucketAuthMain_startRecv_run_eq] at hmem
    rcases hhon : (match h.cache t0 with
      | some (tCached, σc, kVal) => if tCached = tn0 then some (σc, kVal) else none
      | none => none) with _ | ⟨σc, kVal⟩ <;> simp only [hhon] at hmem
    · split_ifs at hmem <;>
        (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem;
         subst hmem; cases hrs)
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem
      simp only [Option.some.injEq, Prod.mk.injEq] at hrs
      rcases hrs with ⟨_, _, rfl⟩
      exact hInitR kVal
  · exact ⟨hVRHk.mono, hVRHk.startRecv_step, hVRHk.fsRecv_step, hVRHk.commit_vR⟩

open _root_.CryptoGames.CKA (ckaOps) in
open _root_.CryptoGames.SM.Engine (HooksCAgrees eval_ret) in
private theorem hkPbaModeC_agrees_vr [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L k B B_q Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) (fm : Bool)
    {VROkStep : ℕ → RS → Prop}
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
    (hVRHk : HooksVRInv VROkStep (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL t))
    (hInitR : ∀ k0, VROkStep 0 (fs.initReceiver k0))
    (hFsB : ∀ rs hdr e rs' i m, VROkStep B_q rs → fs.receive rs hdr e = some (rs', i, m) → i ≤ B) :
    HooksCAgrees (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      prngBucketAuthHsEnc (PBAInv L (k + 1)) (HBoundedPost := PBAInv L k)
      (VROk := VROkStep B_q)
      (hkPbaModeC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δcka qep tL t fm)
      (hkPbaMode cka prng fs Δcka qep tL t fm) := by
  have hVRMode := hkPbaMode_vrInv cka prng fs Δcka qep tL t fm hVRHk hInitR
  cases fm
  · refine
      { hBounded_post := fun _ h => h.mono (Nat.le_succ k)
        startSend_eval := fun hE ctxE pE tE γE σE rE ρ h ctx P hInv hh hctx _ =>
          prngBucketAuthStartSendC_eval cka prng fs hSend hPrngUp hFsInitS heqI hSampCCoins hSampK
            L k Δcka qep tL t hE ctxE pE tE γE σE rE ρ h ctx P hInv hh hctx
        startSend_bounded := fun ctx P t0 γ0 σv0 r0 h hInv =>
          prngBucketAuthStartSend_bounded cka prng fs L k Δcka qep tL t ctx P t0 γ0 σv0 r0 h hInv
        startRecv_eval := fun hE ctxE pE tE γE σE tnE ρ h ctx P _ hh _ _ =>
          prngBucketAuthMainStartRecvC_eval cka prng fs hRecv hFsInitR heqT
            Δcka qep tL t hE ctxE pE tE γE σE tnE ρ h ctx P hh
        startRecv_bounded := fun ctx P t0 γ0 σv0 tn0 h hInv res hmem => by
          dsimp only [hkPbaMode] at hmem
          rw [hooksPRNGBucketAuthMain_startRecv_run_eq] at hmem
          rcases hhon : (match h.cache t0 with
            | some (tCached, σc, kVal) => if tCached = tn0 then some (σc, kVal) else none
            | none => none) with _ | ⟨σc, kVal⟩ <;> simp only [hhon] at hmem
          · split_ifs at hmem <;>
              (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem;
               subst hmem; exact hInv.mono (Nat.le_succ k))
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
            subst hmem; exact hInv.mono (Nat.le_succ k)
        startRecv_vrOk := fun ctx P t0 γ0 σv0 tn0 h _ res hmem γ' σ' rs hrs =>
          hVRMode.mono (Nat.zero_le B_q)
            (hVRMode.startRecv_step ctx P t0 γ0 σv0 tn0 h res hmem γ' σ' rs hrs)
        fsSend_eval := fun hE _ _ _ ssE hdrE mE _ ρ h _ _ _ hh _ _ => by
          simp [hkPbaModeC, hooksPRNGBucketAuthMainC, hooksPRNGBucketAuthC, prngBucketAuthFsSendC,
            hkPbaMode, hooksPRNGBucketAuthMain, hooksPRNGBucketAuthHybrid,
            prngOps, ckaOps, hFsSend, hh, StateT.run_pure, Prod.map, Expr.eval]
        fsRecv_eval := fun hE _ _ _ rsE hdrE eE _ ρ h _ _ _ _ hVR hh _ _ _ => by
          dsimp only [hkPbaModeC, hkPbaMode]
          simp only [hooksPRNGBucketAuthMainC, hooksPRNGBucketAuthC, prngBucketAuthFsRecvC,
            hooksPRNGBucketAuthMain, hooksPRNGBucketAuthHybrid, eval_ret,
            prngOps, ckaOps, hFsRecv, hh, StateT.run_pure, map_pure, Prod.map, id_eq, Expr.eval]
          congr 2
          rcases hrc : fs.receive (rsE.eval ρ) (hdrE.eval ρ) (eE.eval ρ) with _ | ⟨rs', i, m⟩
          · rfl
          · simp [Nat.min_eq_left (hFsB _ _ _ _ _ _ hVR hrc)]
        fsRecv_bounded := fun _ _ _ _ _ _ _ h hInv res hmem => by
          dsimp only [hkPbaMode, hooksPRNGBucketAuthMain, hooksPRNGBucketAuthHybrid] at hmem
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
          subst hmem; exact hInv
        commit_eval := fun hE _ _ _ newE ρ h _ _ _ new _ hh _ _ _ hnew => by
          simp [hkPbaModeC, hooksPRNGBucketAuthMainC, hooksPRNGBucketAuthC, prngBucketAuthCommitC,
            hkPbaMode, hooksPRNGBucketAuthMain, hooksPRNGBucketAuthHybrid,
            hh, hnew, StateT.run_pure, Prod.map, Expr.eval]
        reveal_eval := fun hE ctxE pE vpE ρ h ctx P vp _ hh hctx _ hvp =>
          (prngBucketAuthRevealC_eval cka prng fs Δcka qep tL t hE ctxE pE vpE ρ h ctx P vp
            hh hctx hvp).1 }
  · refine
      { hBounded_post := fun _ h => h.mono (Nat.le_succ k)
        startSend_eval := fun hE ctxE pE tE γE σE rE ρ h ctx P hInv hh hctx _ =>
          prngBucketAuthStartSendC_eval cka prng fs hSend hPrngUp hFsInitS heqI hSampCCoins hSampK
            L k Δcka qep tL t hE ctxE pE tE γE σE rE ρ h ctx P hInv hh hctx
        startSend_bounded := fun ctx P t0 γ0 σv0 r0 h hInv =>
          prngBucketAuthStartSend_bounded cka prng fs L k Δcka qep tL t ctx P t0 γ0 σv0 r0 h hInv
        startRecv_eval := fun hE ctxE pE tE γE σE tnE ρ h ctx P hInv hh hctx _ =>
          prngBucketAuthStartRecvC_eval cka prng fs hRecv hPrngUp hFsInitR heqT heqI hSampK
            L k Δcka qep tL t hE ctxE pE tE γE σE tnE ρ h ctx P hInv hh hctx
        startRecv_bounded := fun ctx P t0 γ0 σv0 tn0 h hInv =>
          prngBucketAuthStartRecv_bounded cka prng fs L k Δcka qep tL t ctx P t0 γ0 σv0 tn0 h hInv
        startRecv_vrOk := fun ctx P t0 γ0 σv0 tn0 h _ res hmem γ' σ' rs hrs =>
          hVRMode.mono (Nat.zero_le B_q)
            (hVRMode.startRecv_step ctx P t0 γ0 σv0 tn0 h res hmem γ' σ' rs hrs)
        fsSend_eval := fun hE _ _ _ ssE hdrE mE _ ρ h _ _ _ hh _ _ => by
          simp [hkPbaModeC, hooksPRNGBucketAuthForgedHdrC, hooksPRNGBucketAuthC,
            prngBucketAuthFsSendC, hkPbaMode, hooksPRNGBucketAuthForgedHdr,
            hooksPRNGBucketAuthHybrid, prngOps, ckaOps, hFsSend, hh,
            StateT.run_pure, Prod.map, Expr.eval]
        fsRecv_eval := fun hE _ _ _ rsE hdrE eE _ ρ h _ _ _ _ hVR hh _ _ _ => by
          dsimp only [hkPbaModeC, hkPbaMode]
          simp only [hooksPRNGBucketAuthForgedHdrC, hooksPRNGBucketAuthC,
            prngBucketAuthFsRecvC, hooksPRNGBucketAuthForgedHdr,
            hooksPRNGBucketAuthHybrid, eval_ret,
            prngOps, ckaOps, hFsRecv, hh, StateT.run_pure, map_pure, Prod.map, id_eq, Expr.eval]
          congr 2
          rcases hrc : fs.receive (rsE.eval ρ) (hdrE.eval ρ) (eE.eval ρ) with _ | ⟨rs', i, m⟩
          · rfl
          · simp [Nat.min_eq_left (hFsB _ _ _ _ _ _ hVR hrc)]
        fsRecv_bounded := fun _ _ _ _ _ _ _ h hInv res hmem => by
          dsimp only [hkPbaMode, hooksPRNGBucketAuthForgedHdr, hooksPRNGBucketAuthHybrid] at hmem
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
          subst hmem; exact hInv
        commit_eval := fun hE _ _ _ newE ρ h _ _ _ new _ hh _ _ _ hnew => by
          simp [hkPbaModeC, hooksPRNGBucketAuthForgedHdrC, hooksPRNGBucketAuthC,
            prngBucketAuthCommitC, hkPbaMode, hooksPRNGBucketAuthForgedHdr,
            hooksPRNGBucketAuthHybrid, hh, hnew, StateT.run_pure, Prod.map, Expr.eval]
        reveal_eval := fun hE ctxE pE vpE ρ h ctx P vp _ hh hctx _ hvp =>
          prngBucketAuthForgedHdrRevealC_eval cka prng fs Δcka qep tL t hE ctxE pE vpE ρ h ctx P vp
            hh hctx hvp }

open _root_.CryptoGames.SM.Engine (commitE abortE run_liftH_bind) in
private theorem commitE_pbaMode_h_eq [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) (fm : Bool)
    (s : Ctx Γ T (Option RSt) SS RS M E) (P : Party)
    (old new : VP Γ T (Option RSt) SS RS) (pos : Pos)
    (es : EState (VP Γ T (Option RSt) SS RS) M (Header T × E) (PRNGBucketAuthState T RSt K I)) :
    ∀ res ∈ support ((commitE (hkPbaMode cka prng fs Δcka qep tL t fm)
        s P old new pos).run es),
      res.2.h = es.h := by
  intro ⟨cmRes, es'⟩ hmem
  unfold commitE abortE at hmem
  rw [run_liftH_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨ans, h'⟩, hcm, hmem⟩ := hmem
  cases fm <;>
    (dsimp only [hkPbaMode, hooksPRNGBucketAuthMain, hooksPRNGBucketAuthForgedHdr,
       hooksPRNGBucketAuthHybrid] at hcm;
     simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hcm;
     rcases hcm with ⟨rfl, rfl⟩;
     simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
     rcases hmem with ⟨_, rfl⟩; rfl)

open _root_.CryptoGames.SM.Engine (HooksCAgrees deliverE abortE run_liftH_bind vRecv_bounded) in
private theorem deliverE_pbaModeInv [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L k B B_q Δcka qep maxSkip : ℕ) (tL : Option ℕ) (t : ℕ) (fm : Bool) (cfg : Config M)
    {VROkStep : ℕ → RS → Prop}
    (hHk : HooksCAgrees (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      prngBucketAuthHsEnc (PBAInv L (k + 1)) (HBoundedPost := PBAInv L k)
      (VROk := VROkStep B_q)
      (hkPbaModeC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δcka qep tL t fm)
      (hkPbaMode cka prng fs Δcka qep tL t fm))
    (es : EState (VP Γ T (Option RSt) SS RS) M (Header T × E) (PRNGBucketAuthState T RSt K I))
    (arg : Party × (Header T × E))
    (hInv : PBAInv L (k + 1) es.h) :
    ∀ res ∈ support ((deliverE (hkPbaMode cka prng fs Δcka qep tL t fm)
        maxSkip cfg arg).run es),
      PBAInv L k res.2.h := by
  rcases arg with ⟨P, c⟩
  intro ⟨out, es'⟩ hmem
  unfold deliverE abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases hab : (es.abort || es.g.win)
  · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hInv.mono (Nat.le_succ k)
  · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
    rcases htr : es.g.inTransit P.other c with _ | r
    · simp only [htr, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInv.mono (Nat.le_succ k)
    · simp only [htr, run_liftH_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨vrRes, h'⟩, hvr, hmem⟩ := hmem
      have hInv' := vRecv_bounded prngBucketAuthHsEnc (PBAInv L (k + 1))
        (hkPbaModeC L B Δcka qep tL t fm)
        (hkPbaMode cka prng fs Δcka qep tL t fm) hHk
        es.g P (es.g.st P) c (some r) es.h hInv (vrRes, h') hvr
      rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hInv'
      · split_ifs at hmem <;>
          (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
             support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
           rcases hmem with ⟨_, rfl⟩; exact hInv')
      · simp only [StateT.run_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨cmRes, es1⟩, hcm, hmem⟩ := hmem
        have hEqH := commitE_pbaMode_h_eq cka prng fs Δcka qep tL t fm es.g P (es.g.st P) st'
          r.pos { es with h := h' } (cmRes, es1) hcm
        rcases cmRes with _ | s₁
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, hEs⟩; subst hEs; exact hEqH ▸ hInv'
        · by_cases hcmp : (r.msg != m')
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure,
              pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, hEs⟩; subst hEs; exact hEqH ▸ hInv'
          · simp only [StateT.run_bind, StateT.run_modify,
              StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, hEs⟩; subst hEs; exact hEqH ▸ hInv'

open _root_.CryptoGames.SM.Engine (HooksCAgrees injectE abortE run_liftH_bind vRecv_bounded) in
private theorem injectE_pbaModeInv [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L k B B_q Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) (fm : Bool) (cfg : Config M)
    {VROkStep : ℕ → RS → Prop}
    (hHk : HooksCAgrees (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      prngBucketAuthHsEnc (PBAInv L (k + 1)) (HBoundedPost := PBAInv L k)
      (VROk := VROkStep B_q)
      (hkPbaModeC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δcka qep tL t fm)
      (hkPbaMode cka prng fs Δcka qep tL t fm))
    (es : EState (VP Γ T (Option RSt) SS RS) M (Header T × E) (PRNGBucketAuthState T RSt K I))
    (arg : Party × (Header T × E))
    (hInv : PBAInv L (k + 1) es.h) :
    ∀ res ∈ support ((injectE (hkPbaMode cka prng fs Δcka qep tL t fm)
        (2 + Δcka) qep cfg arg).run es),
      PBAInv L k res.2.h := by
  rcases arg with ⟨P, c⟩
  intro ⟨out, es'⟩ hmem
  unfold injectE abortE at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases href :
      (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj (2 + Δcka)))
  · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hInv.mono (Nat.le_succ k)
  · simp only [href, Bool.false_eq_true, ↓reduceIte, run_liftH_bind,
      mem_support_bind_iff] at hmem
    obtain ⟨⟨vrRes, h'⟩, hvr, hmem⟩ := hmem
    have hInv' := vRecv_bounded prngBucketAuthHsEnc (PBAInv L (k + 1))
      (hkPbaModeC L B Δcka qep tL t fm)
      (hkPbaMode cka prng fs Δcka qep tL t fm) hHk
      es.g P (es.g.st P) c none es.h hInv (vrRes, h') hvr
    rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
    · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInv'
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInv'
    · by_cases hqep : qep + 1 < t'
      · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hInv'
      · simp only [hqep, ↓reduceIte] at hmem
        by_cases htriv : es.g.trivial (2 + Δcka) ⟨P.other, t', i'⟩
        · simp only [htriv, ↓reduceIte, StateT.run_bind, mem_support_bind_iff] at hmem
          obtain ⟨⟨cmRes, es1⟩, hcm, hmem⟩ := hmem
          have hEqH := commitE_pbaMode_h_eq cka prng fs Δcka qep tL t fm es.g P (es.g.st P) st'
            ⟨P.other, t', i'⟩ { es with h := h' } (cmRes, es1) hcm
          rcases cmRes with _ | s₁
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
              Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, hEs⟩; subst hEs; exact hEqH ▸ hInv'
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, hEs⟩; subst hEs; exact hEqH ▸ hInv'
        · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem
          by_cases hfull : cfg.injectFull t'
          · simp only [hfull, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hInv'
          · simp only [hfull, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hInv'

private def pbaNoDoomPolicy : Policy where
  auth := false
  tL := none
  tStar := 0

@[local simp] private theorem pbaNoDoomPolicy_leakDoom {St Msg C : Type}
    (g g' : GameState St Msg C) : pbaNoDoomPolicy.leakDoom g g' = false := by
  simp [pbaNoDoomPolicy, Policy.leakDoom]

@[local simp] private theorem pbaNoDoomPolicy_corrDoom {St Msg C : Type}
    (g : GameState St Msg C) (P : Party) : pbaNoDoomPolicy.corrDoom g P = false := by
  simp [pbaNoDoomPolicy, Policy.corrDoom]

open _root_.CryptoGames.SM.Engine (esEnc) in
private abbrev pbaRedEsEnc
    (st : PRNGBucketAuthEState Γ T RSt SS RS M E K I) :
    Ty.denote pbaRedEsTy :=
  (esEnc pbaVpEnc prngBucketAuthHsEnc st.1, st.2)

open _root_.CryptoGames.SM.Construction (abortedParties) in
private def initPRNGBucketAuthRaw [DecidableEq I] [SampleableType KC] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (tL : Option ℕ) (t : ℕ) (b : Bool) :
    PRFPRNG.AdversaryComp RSt I K
      (EState (VP Γ T (Option RSt) SS RS) M (Header T × E) (PRNGBucketAuthState T RSt K I)) := do
  let kc ← sampleT KC
  let (step, h₀) ← (rootPRNGBucketAuthHybrid (T := T) prng tL t 0 false lam none).run {}
  match step with
  | none =>
    let (vA, vB) := abortedParties (T := T) (RSt := RSt) (SS := SS) (RS := RS)
      (cka.initA kc) (cka.initB kc)
    pure { g := { st := fun | .A => vA | .B => vB, b := b }, h := h₀, abort := true }
  | some (σv, k) =>
    let (vA, vB) := mkParties (T := T) (cka.initA kc) (cka.initB kc) σv
      (fs.initSender k) (fs.initReceiver k)
    pure { g := { st := fun | .A => vA | .B => vB, b := b }, h := h₀, abort := false }

open _root_.CryptoGames.CKA (CKASort ckaOps ckaSamplers) in
open _root_.CryptoGames.SM (pair_eval) in
open _root_.CryptoGames.SM.Engine
  (eval_bind_ret eval_bind eval_caseOpt eval_ret esEnc esMk vpTblEnc
   cGsInitE_eval mkPartiesE mkPartiesE_eval) in
open _root_.CryptoGames.SM.Engine.RedPRNG (liftP_eq_liftM) in
open _root_.CryptoGames.SM.Construction (abortedParties abortedPartiesE abortedPartiesE_eval) in
private theorem initPRNGBucketAuthEStateC_eval [DecidableEq I]
    [SampleableType KC] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (hInitA : ckaInitA = cka.initA)
    (hInitB : ckaInitB = cka.initB)
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (heqI : eqI = (· == ·))
    (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (hSampK : sampK = ($ᵗ K : ProbComp K))
    (L : ℕ) (tL : Option ℕ) (t : ℕ) {Γ'} (bE : Expr OO Γ' .bool) (ρ : Env Γ') :
    (initPRNGBucketAuthEStateC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L tL t bE).eval ρ =
      esEnc pbaVpEnc prngBucketAuthHsEnc <$>
        initPRNGBucketAuthRaw cka prng fs lam tL t (bE.eval ρ) := by
  unfold initPRNGBucketAuthEStateC initPRNGBucketAuthRaw
  rw [eval_bind_ret]
  set b := bE.eval ρ
  set ρ₁ := Env.cons (t := (.bool : Ty S)) b ρ
  rw [eval_bind, map_bind]
  have hKC : (@Comp.sample _ _ _ OO II _ CKASamp.kc .unit).eval ρ₁ = sampleT KC := by
    simp only [Comp.eval, prngIface, prngSamplers, ckaSamplers, hSampKC, sampleT]
    exact liftP_eq_liftM II (fun _ => rfl) ($ᵗ KC)
  rw [hKC]
  refine bind_congr fun kc => ?_
  set ρ₂ := Env.cons (t := (.base .kc : Ty S)) kc ρ₁
  rw [eval_bind, map_bind]
  have hEmpty : (pbaHsEmptyE (O := OO)).eval ρ₂ =
      prngBucketAuthHsEnc ({} : PRNGBucketAuthState T RSt K I) := by
    simp [pbaHsEmptyE, prngBucketAuthHsEnc, Expr.eval]
  have hRoot := (rootPRNGBucketAuthHybridC_eval
    (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)
    prng hPrngUp heqI hSampK L tL t
    pbaHsEmptyE (.nat 0) (.bool false) (Expr.op (O := OO) CKAOp.lamI .unit) .none
    ρ₂ ({} : PRNGBucketAuthState T RSt K I) hEmpty (Nat.zero_le L)).1
  simp only [Expr.eval, prngOps, ckaOps] at hRoot
  rw [hRoot, bind_map_left]
  refine bind_congr fun ⟨step, h₀⟩ => ?_
  set ρ₃ := Env.cons
    (t := (.prod (.opt (.prod (.opt (.base .sig)) (.base .k))) pbaHsTy : Ty S))
    (step, prngBucketAuthHsEnc h₀) ρ₂
  change (Comp.caseOpt _ _ _).eval ρ₃ = _
  rw [eval_caseOpt]
  rcases step with _ | ⟨σv, k⟩
  · simp only [Expr.eval, Expr.v0, map_pure]
    change (Comp.ret _).eval ρ₃ = _
    rw [eval_ret]
    set pAB := abortedParties (T := T) (RSt := RSt) (SS := SS) (RS := RS)
      (cka.initA kc) (cka.initB kc)
    have hAbP := abortedPartiesE_eval
      (Expr.op (O := OO) CKAOp.ckaInitA .v1) (Expr.op (O := OO) CKAOp.ckaInitB .v1) ρ₃
    have hAbP' :
        (abortedPartiesE
          (Expr.op (O := OO) CKAOp.ckaInitA .v1)
          (Expr.op (O := OO) CKAOp.ckaInitB .v1)).eval ρ₃ =
          (pbaVpEnc pAB.1, pbaVpEnc pAB.2) := by
      rw [hAbP]
      simp [ρ₃, ρ₂, ρ₁, prngOps, ckaOps, hInitA, hInitB, pAB, Prod.map, Expr.eval, Expr.v1]
    have hGs := cGsInitE_eval pbaVpEnc (O' := OO)
      (.fst (abortedPartiesE
        (Expr.op (O := OO) CKAOp.ckaInitA .v1) (Expr.op (O := OO) CKAOp.ckaInitB .v1)))
      (.snd (abortedPartiesE
        (Expr.op (O := OO) CKAOp.ckaInitA .v1) (Expr.op (O := OO) CKAOp.ckaInitB .v1)))
      .v2 ρ₃ pAB.1 pAB.2
      (by simp [Expr.eval, hAbP']) (by simp [Expr.eval, hAbP'])
    simp only [esMk, pair_eval, hGs]
    rfl
  · simp only [Expr.eval, Expr.v0, map_pure]
    set ρ₄ := Env.cons (t := (.prod (.opt (.base .sig)) (.base .k) : Ty S)) (σv, k) ρ₃
    change (Comp.ret _).eval ρ₄ = _
    rw [eval_ret]
    set pAB := mkParties (T := T) (cka.initA kc) (cka.initB kc) σv
      (fs.initSender k) (fs.initReceiver k)
    have hMkP := mkPartiesE_eval (O' := OO)
      (Expr.op (O := OO) CKAOp.ckaInitA .v2) (Expr.op (O := OO) CKAOp.ckaInitB .v2)
      (.fst .v0)
      (Expr.op (O := OO) CKAOp.fsInitSender (.snd .v0))
      (Expr.op (O := OO) CKAOp.fsInitReceiver (.snd .v0)) ρ₄
    have hMkP' :
        (mkPartiesE (O' := OO)
          (Expr.op (O := OO) CKAOp.ckaInitA .v2)
          (Expr.op (O := OO) CKAOp.ckaInitB .v2)
          (.fst .v0)
          (Expr.op (O := OO) CKAOp.fsInitSender (.snd .v0))
          (Expr.op (O := OO) CKAOp.fsInitReceiver (.snd .v0))).eval ρ₄ =
          (pbaVpEnc pAB.1, pbaVpEnc pAB.2) := by
      rw [hMkP]
      simp [ρ₄, ρ₃, ρ₂, ρ₁, prngOps, ckaOps, hInitA, hInitB, hFsInitS, hFsInitR, pAB, Prod.map,
        Expr.eval, Expr.v0, Expr.v2]
    have hGs := cGsInitE_eval pbaVpEnc (O' := OO)
      (.fst (mkPartiesE
        (Expr.op (O := OO) CKAOp.ckaInitA .v2)
        (Expr.op (O := OO) CKAOp.ckaInitB .v2)
        (.fst .v0)
        (Expr.op (O := OO) CKAOp.fsInitSender (.snd .v0))
        (Expr.op (O := OO) CKAOp.fsInitReceiver (.snd .v0))))
      (.snd (mkPartiesE
        (Expr.op (O := OO) CKAOp.ckaInitA .v2)
        (Expr.op (O := OO) CKAOp.ckaInitB .v2)
        (.fst .v0)
        (Expr.op (O := OO) CKAOp.fsInitSender (.snd .v0))
        (Expr.op (O := OO) CKAOp.fsInitReceiver (.snd .v0))))
      .v3 ρ₄ pAB.1 pAB.2
      (by simp [Expr.eval, hMkP']) (by simp [Expr.eval, hMkP'])
    dsimp only [Expr.v0, Expr.v1, Expr.v2, Expr.v3] at hGs ⊢
    simp only [esMk, pair_eval, hGs]
    rfl

open _root_.CryptoGames.SM.Engine (SMEngineInv SMVRInv) in
open _root_.CryptoGames.SM.Construction (abortedParties) in
private theorem initPRNGBucketAuthRaw_inv [DecidableEq I]
    [SampleableType KC] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (tL : Option ℕ) (t : ℕ) (b : Bool)
    {VROkStep : ℕ → RS → Prop} {L B_q qAdv : ℕ}
    (hqB : qAdv ≤ B_q) (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (hInitR : ∀ k, VROkStep (B_q - qAdv) (fs.initReceiver k)) :
    ∀ es₀ ∈ support (initPRNGBucketAuthRaw cka prng fs lam tL t b),
      PBAInv L qAdv es₀.h ∧ SMEngineInv L B_q qAdv es₀.g ∧ SMVRInv VROkStep B_q qAdv es₀.g := by
  intro es₀ hmem
  unfold initPRNGBucketAuthRaw at hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨kc, _, hmem⟩ := hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨⟨step, h₀⟩, hh₀, hmem⟩ := hmem
  have hPBA : PBAInv L qAdv h₀ := by
    intro t'
    have hle := rootPRNGBucketAuthHybrid_fTable_le (T := T) prng tL t 0 false lam none {}
      (step, h₀) hh₀ t'
    dsimp only at hle
    simp only [List.length_nil] at hle
    omega
  rcases step with _ | ⟨σv, k⟩
  · simp only [support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    refine ⟨hPBA, (SMEngineInv.init _ b hB1 hBB).mono hqB, ?_⟩
    intro P ep v hv
    cases P <;> simp [abortedParties] at hv
  · simp only [support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    refine ⟨hPBA, (SMEngineInv.init _ b hB1 hBB).mono hqB, ?_⟩
    intro P ep v hv
    cases P <;> simp only [mkParties] at hv
    · split_ifs at hv with ht0
      · cases hv; exact hInitR _
    · cases hv


private abbrev pbaStage2RedEsEnc (fm : Bool)
    (st : PRNGBucketAuthEState Γ T RSt SS RS M E K I) :
    Ty.denote pbaStage2RedEsTy :=
  (pbaRedEsEnc st, fm)

open _root_.CryptoGames.SM.Engine (HooksCAgrees vSend_eq_bind vSendStep1_bounded) in
private theorem vSend_pbaModeInv [DecidableEq T] [DecidableEq I] [Inhabited E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L k B B_q Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) (fm : Bool)
    {VROkStep : ℕ → RS → Prop}
    (hHk : HooksCAgrees (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      prngBucketAuthHsEnc (PBAInv L (k + 1)) (HBoundedPost := PBAInv L k)
      (VROk := VROkStep B_q)
      (hkPbaModeC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δcka qep tL t fm)
      (hkPbaMode cka prng fs Δcka qep tL t fm))
    (ctx : Ctx Γ T (Option RSt) SS RS M E) (P : Party)
    (s : VP Γ T (Option RSt) SS RS) (m : M) (r : Option CCoins)
    (h : PRNGBucketAuthState T RSt K I) (hInv : PBAInv L (k + 1) h) :
    ∀ res ∈ support ((vSend (hkPbaMode cka prng fs Δcka qep tL t fm)
        ctx P s m none r).run h),
      PBAInv L k res.2 := by
  intro ⟨vsRes, h'⟩ hmem
  rw [vSend_eq_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨s₁?, h₁⟩, hs1, hmem⟩ := hmem
  have hInv1 := vSendStep1_bounded prngBucketAuthHsEnc (PBAInv L (k + 1))
    (hkPbaModeC L B Δcka qep tL t fm)
    (hkPbaMode cka prng fs Δcka qep tL t fm) hHk
    ctx P s r h hInv (s₁?, h₁) hs1
  rcases s₁? with _ | s₁
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hInv1
  · rcases hs1vS : s₁.vS with _ | v
    · simp only [hs1vS, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInv1
    · cases fm <;>
        (dsimp only [hkPbaMode, hooksPRNGBucketAuthMain, hooksPRNGBucketAuthForgedHdr,
           hooksPRNGBucketAuthHybrid] at hmem;
         simp only [hs1vS, StateT.run_pure, pure_bind,
           support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
         rcases hmem with ⟨_, rfl⟩; exact hInv1)

open _root_.CryptoGames.SM.Engine (transmitE abortE run_liftH_bind) in
private theorem implPRNGBucketAuthGen_tr_eq [DecidableEq T] [DecidableEq M]
    [DecidableEq E] [Inhabited E]
    (hk : Hooks (PRFPRNG.spec RSt I K) (PRNGBucketAuthState T RSt K I)
      Γ T RSt SS RS M E CCoins Γ (Option RSt) SS RS)
    (Δcka qep maxSkip : ℕ) (tL : Option ℕ) (onlyNewForged : Bool)
    (es : EState (VP Γ T (Option RSt) SS RS) M (Header T × E) (PRNGBucketAuthState T RSt K I))
    (winEp : Option ℕ) (P : Party) (m : M) (r : Option CCoins) :
    ((implPRNGBucketAuthGen hk Δcka qep maxSkip tL onlyNewForged)
      (.inr (.inl (.inl (.inl (.inl (P, m, r))))))).run (es, winEp) =
      (fun p => (p.1, (p.2, winEp))) <$>
        (transmitE hk (2 + Δcka) qep pbaNoDoomPolicy (P, m, r)).run es := by
  change (do
    let (es0, winEp0) : PRNGBucketAuthEState Γ T RSt SS RS M E K I ← get
    if es0.abort || es0.g.win then return none
    match es0.g.epMgmt (2 + Δcka) qep P r.isSome with
    | none => return none
    | some s₁ =>
      let (res, h') ← StateT.lift ((vSend hk s₁ P (s₁.st P) m none r).run es0.h)
      match res with
      | none =>
        set ({ es0 with h := h', abort := true }, winEp0)
        return none
      | some (st', ct) =>
        let recE : Record M (Header T × E) := ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, ct⟩
        set ({ es0 with g := s₁.record (2 + Δcka) P st' recE false, h := h' }, winEp0)
        return some ct).run (es, winEp) = _
  unfold transmitE abortE
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hab : (es.abort || es.g.win)
  · simp [hab, StateT.run_pure]
  · simp only [hab, Bool.false_eq_true, ↓reduceIte]
    rcases hep : es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁
    · simp [StateT.run_pure]
    · simp only [pbaNoDoomPolicy_leakDoom, Bool.false_eq_true, ↓reduceIte]
      rw [run_liftH_bind, map_bind]
      simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
      refine bind_congr fun ⟨vsRes, h'⟩ => ?_
      rcases vsRes with _ | ⟨st', ct⟩ <;>
        simp [StateT.run_set, StateT.run_modify]

open _root_.CryptoGames.SM.Engine (corrE abortE run_liftH_bind) in
private theorem implPRNGBucketAuthGen_corr_eq [DecidableEq T] [DecidableEq M]
    [DecidableEq E] [Inhabited E]
    (hk : Hooks (PRFPRNG.spec RSt I K) (PRNGBucketAuthState T RSt K I)
      Γ T RSt SS RS M E CCoins Γ (Option RSt) SS RS)
    (Δcka qep maxSkip : ℕ) (tL : Option ℕ) (onlyNewForged : Bool)
    (es : EState (VP Γ T (Option RSt) SS RS) M (Header T × E) (PRNGBucketAuthState T RSt K I))
    (winEp : Option ℕ) (P : Party) :
    ((implPRNGBucketAuthGen hk Δcka qep maxSkip tL onlyNewForged) (.inr (.inr P))).run (es, winEp) =
      (fun p => (p.1, (p.2, winEp))) <$>
        (corrE hk pbaNoDoomPolicy P).run es := by
  change (do
    let (es0, winEp0) : PRNGBucketAuthEState Γ T RSt SS RS M E K I ← get
    if es0.abort || es0.g.win || !(es0.g.corrAllowed P) then return none
    let s₁ := es0.g.afterCorr P
    let (res, h') ← StateT.lift ((hk.reveal es0.g P (es0.g.st P)).run es0.h)
    match res with
    | none =>
      set ({ es0 with h := h', abort := true }, winEp0)
      return none
    | some stOut =>
      set ({ es0 with g := s₁, h := h' }, winEp0)
      return some stOut).run (es, winEp) = _
  unfold corrE abortE
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases href : (es.abort || es.g.win || !(es.g.corrAllowed P))
  · simp [href, StateT.run_pure]
  · simp only [href, pbaNoDoomPolicy_leakDoom, pbaNoDoomPolicy_corrDoom, Bool.or_false,
      Bool.false_eq_true, ↓reduceIte]
    rw [run_liftH_bind, map_bind]
    simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
    refine bind_congr fun ⟨revRes, h'⟩ => ?_
    rcases revRes with _ | stOut <;>
      simp [StateT.run_set, StateT.run_modify]

private theorem eval_caseSum_inl {Γ' t1 t2 u} (e : Expr OO Γ' (.sum t1 t2))
    (c1 : Comp OO II (t1 :: Γ') u) (c2 : Comp OO II (t2 :: Γ') u) (ρ : Env Γ') (a : Ty.denote t1)
    (he : e.eval ρ = .inl a) :
    (Comp.caseSum e c1 c2).eval ρ = c1.eval (Env.cons a ρ) := by
  simp [Comp.eval, he]

private theorem eval_caseSum_inr {Γ' t1 t2 u} (e : Expr OO Γ' (.sum t1 t2))
    (c1 : Comp OO II (t1 :: Γ') u) (c2 : Comp OO II (t2 :: Γ') u) (ρ : Env Γ') (b : Ty.denote t2)
    (he : e.eval ρ = .inr b) :
    (Comp.caseSum e c1 c2).eval ρ = c2.eval (Env.cons b ρ) := by
  simp [Comp.eval, he]

private theorem with_comp_env {Γ' u β} {c : Comp OO II Γ' u} {ρ : Env Γ'}
    {f : Ty.denote u → β} {rhs}
    (h : ∀ ρ' : Env Γ', ρ' = ρ → (f <$> c.eval ρ') = rhs) :
    (f <$> c.eval ρ) = rhs := h ρ rfl

set_option maxHeartbeats 400000 in
open _root_.CryptoGames.CKA (CKASort ckaOps ckaSMQ ckaSMCodec ckaPsEnc ckaPsDec) in
open _root_.CryptoGames.SM (orE_eval not_eval isSomeE_eval pair_eval some_eval pGet pGet_eval partyEnc) in
open _root_.CryptoGames.SM.Engine
  (HooksCAgrees ConfigECAgrees SMStateBoundedEngine
   eval_bind_ret eval_ite eval_caseOpt eval_bind eval_ret
   esEnc cGsEnc cRecEnc
   esG esH esAbort esMk cGsWin cGsSt cGsEpoch cGsIdx
   vpTcurNat vpTblEnc vpEnc
   cEpMgmtE_eval epMgmt_lists_eq vSendC_eval cRecordE_eval
   deliverEC_eval injectEC_eval cCorrAllowedE_eval cAfterCorrE_eval
   transmitE corrE deliverE injectE abortE run_liftH_bind) in
private theorem rdec_pbaHandle_eval
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L k B B_q Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) (fm : Bool)
    {VROkStep : ℕ → RS → Prop}
    (hDefaultE : defaultE = default)
    (heqT : eqT = (· == ·))
    (heqM : eqM = (· == ·))
    (heqE : eqE = (· == ·))
    (hHk : HooksCAgrees (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      prngBucketAuthHsEnc (PBAInv L (k + 1)) (HBoundedPost := PBAInv L k)
      (VROk := VROkStep B_q)
      (hkPbaModeC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δcka qep tL t fm)
      (hkPbaMode cka prng fs Δcka qep tL t fm))
    (es : EState (VP Γ T (Option RSt) SS RS) M (Header T × E) (PRNGBucketAuthState T RSt K I))
    (winEp : Option ℕ)
    (q : (spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hInv : PBAInv L (k + 1) es.h)
    (hBound : SMStateBoundedEngine L es.g)
    (hVR : ∀ P t₀ v, (es.g.st P).vR t₀ = some v → VROkStep B_q v) :
    ((fun p => ((prngSMCodec KC Γ CCoins T I KR RSt K SS RS M E).rdec q p.1, p.2)) <$>
      ((redPRNGAuthBucketHybridProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
          (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK)
          L B Δcka qep fs.maxSkip tL t).handle.eval
        (.cons (pbaStage2RedEsEnc fm (es, winEp))
          (.cons ((prngSMCodec KC Γ CCoins T I KR RSt K SS RS M E).qenc q) .nil)))) =
      Prod.map id (pbaStage2RedEsEnc fm) <$>
        ((implPRNGBucketAuthGen (hkPbaMode cka prng fs Δcka qep tL t fm)
          Δcka qep fs.maxSkip tL fm) (.inr q)).run (es, winEp) := by
  let hkC := hkPbaModeC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) L B Δcka qep tL t fm
  let hk := hkPbaMode cka prng fs Δcka qep tL t fm
  let cfgC := bucketAuthCfgEC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) Δcka tL
  let cfg := bucketAuthCfg (M := M) Δcka tL
  have hCfg : ConfigECAgrees cfgC cfg := bucketAuthCfgEC_agrees Δcka tL
  dsimp only [redPRNGAuthBucketHybridProg]
  rw [eval_bind_ret]
  set ρ₀ := Env.cons (t := pbaStage2RedEsTy) (pbaStage2RedEsEnc fm (es, winEp))
    (Env.cons (t := ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E)
      ((prngSMCodec KC Γ CCoins T I KR RSt K SS RS M E).qenc q) .nil)
  have h0 : (Expr.pair (.fst (.fst (Expr.v0 (O := OO))))
      (.pair (.snd (.fst .v0)) (.pair (.snd .v0) .v1))).eval ρ₀ =
      (esEnc pbaVpEnc prngBucketAuthHsEnc es, winEp, fm,
       (prngSMCodec KC Γ CCoins T I KR RSt K SS RS M E).qenc q) := rfl
  rw [h0]; clear h0
  set ρ_top := Env.cons
    (t := .prod pbaEsTy (.prod (.opt .nat) (.prod .bool (ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E))))
    (esEnc pbaVpEnc prngBucketAuthHsEnc es, winEp, fm,
     (prngSMCodec KC Γ CCoins T I KR RSt K SS RS M E).qenc q) ρ₀
  change _ <$> (Comp.ite _ _ _).eval ρ_top = _
  rw [eval_ite]
  have hFm : (Expr.fst (.snd (.snd (Expr.v0 (O := OO))))).eval ρ_top = fm := rfl
  rw [hFm]; clear hFm
  cases fm
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rcases q with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
    · rw [implPRNGBucketAuthGen_tr_eq]
      rw [eval_caseSum_inl _ _ _ _ _ rfl, eval_caseSum_inl _ _ _ _ _ rfl,
          eval_caseSum_inl _ _ _ _ _ rfl, eval_caseSum_inl _ _ _ _ _ rfl]
      refine with_comp_env fun ρ₁ hρ₁ => ?_
      rw [eval_bind_ret]
      have hArg : (Expr.v0 (O := OO)).eval ρ₁ = (partyEnc P, m, r) := by
        subst hρ₁; rfl
      rw [hArg]; clear hArg
      set ρ₂ := Env.cons (t := .prod .bool (.prod (.base CKASort.msg) (.opt (.base CKASort.ccoins))))
        (partyEnc P, m, r) ρ₁
      unfold transmitE abortE
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      change _ <$> (Comp.ite _ _ _).eval ρ₂ = _
      rw [eval_ite]
      have hCond1 : (orE (esAbort (.fst (Expr.v5 (O := OO))))
          (cGsWin (esG (.fst .v5)))).eval ρ₂ = (es.abort || es.g.win) := by
        subst hρ₁
        simp [ρ₂, ρ_top, orE_eval, esAbort, cGsWin, esG, esEnc, cGsEnc,
          Expr.eval, Expr.v5, Env.get_cons_zero, Env.get_cons_succ]
      rw [hCond1]; clear hCond1
      by_cases hab : (es.abort || es.g.win)
      · simp only [hab, ↓reduceIte]
        subst hρ₁
        simp [ρ₂, ρ_top, ρ₀, Comp.eval, StateT.run_pure,
          Prod.map, pbaStage2RedEsEnc, pbaRedEsEnc,
          Expr.eval, Expr.v5, Env.get_cons_zero, Env.get_cons_succ]
      · simp only [hab, Bool.false_eq_true, ↓reduceIte]
        rw [eval_caseOpt]
        have hEp : (cEpMgmtE (2 + Δcka) qep (esG (.fst (Expr.v5 (O := OO)))) (.fst .v0)
            (isSomeE (.snd (.snd .v0)))).eval ρ₂ =
            (es.g.epMgmt (2 + Δcka) qep P r.isSome).map (cGsEnc pbaVpEnc) := by
          have := cEpMgmtE_eval pbaVpEnc (O' := OO) (2 + Δcka) qep
            (esG (.fst .v5)) (.fst .v0) (isSomeE (.snd (.snd .v0)))
            ρ₂ es.g P (by subst hρ₁; rfl) (by subst hρ₁; rfl)
          simpa [ρ₂, isSomeE_eval, Expr.eval, Env.get, Expr.v0] using this
        rw [hEp]; clear hEp
        rcases hep : es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁
        · subst hρ₁
          simp [ρ₂, ρ_top, ρ₀, Comp.eval, StateT.run_pure, Prod.map,
            pbaStage2RedEsEnc, pbaRedEsEnc,
            Expr.eval, Expr.v5, Env.get_cons_zero, Env.get_cons_succ]
        · simp only [Option.map_some, pbaNoDoomPolicy_leakDoom, Bool.false_eq_true, ↓reduceIte]
          set ρ₃ := Env.cons (t := cGsTy pbaVpTy) (cGsEnc pbaVpEnc s₁) ρ₂
          change _ <$> (Comp.bind (vSendC _ _ _ _ _ _ _ _) _).eval ρ₃ = _
          rw [eval_bind]
          have hStP : (pGet (cGsSt (Expr.v0 (O := OO))) (.fst .v1)).eval ρ₃ =
              pbaVpEnc (s₁.st P) :=
            pGet_eval (cGsSt .v0) (.fst .v1) ρ₃ (fun Q => pbaVpEnc (s₁.st Q)) P rfl rfl
          have hVSend := vSendC_eval hDefaultE prngBucketAuthHsEnc (PBAInv L (k + 1)) hkC hk hHk
            (esH (.fst .v6))
            .v0 (.fst .v1) (pGet (cGsSt .v0) (.fst .v1))
            (.fst (.snd .v1)) .none (.snd (.snd .v1))
            ρ₃ es.h s₁ P (s₁.st P) m none r hInv
            (by subst hρ₁; rfl) rfl rfl hStP rfl rfl rfl
          dsimp only [hkC, hkPbaModeC] at hVSend
          rw [hVSend, bind_map_left, run_liftH_bind, map_bind, map_bind, map_bind]
          refine bind_congr fun ⟨vsRes, h'⟩ => ?_
          rcases vsRes with _ | ⟨st', ct⟩
          · subst hρ₁
            simp [ρ₃, ρ₂, ρ_top, ρ₀, Comp.eval, StateT.run_modify, Prod.map,
              pbaStage2RedEsEnc, pbaRedEsEnc, esMk, esG, esEnc,
              Expr.eval, Expr.v0, Expr.v7, Env.get_cons_zero, Env.get_cons_succ]
          · simp only [Prod.map, Option.map_some, id_eq, eval_caseOpt,
              StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, map_pure]
            set ρ₄ := Env.cons (t := .prod pbaVpTy hdrCtTy) (pbaVpEnc st', ct)
              (Env.cons (t := .prod (.opt (.prod pbaVpTy hdrCtTy)) pbaHsTy)
                (some (pbaVpEnc st', ct), prngBucketAuthHsEnc h') ρ₃)
            change _ <$> (Comp.ret _).eval ρ₄ = _
            have hEp4 : (pGet (cGsEpoch (Expr.v2 (O := OO))) (.fst .v3)).eval ρ₄ = s₁.epoch P :=
              pGet_eval (cGsEpoch .v2) (.fst .v3) ρ₄ s₁.epoch P rfl rfl
            have hIdx4 : (pGet (cGsIdx (Expr.v2 (O := OO))) (.fst .v3)).eval ρ₄ = s₁.idx P :=
              pGet_eval (cGsIdx .v2) (.fst .v3) ρ₄ s₁.idx P rfl rfl
            have hRecE : (Expr.pair
                (.pair (.fst (Expr.v3 (O := OO)))
                  (.pair (pGet (cGsEpoch .v2) (.fst .v3))
                    (.add (pGet (cGsIdx .v2) (.fst .v3)) (.nat 1))))
                (.pair (.fst (.snd .v3)) (.snd .v0))).eval ρ₄ =
                cRecEnc ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, ct⟩ := by
              simp only [Expr.eval, hEp4, hIdx4]; rfl
            have hRecord := cRecordE_eval pbaVpEnc (O' := OO) L (2 + Δcka)
              (Expr.v2 (O := OO)) (.fst .v3) (.fst .v0)
              (.pair (.pair (.fst .v3)
                (.pair (pGet (cGsEpoch .v2) (.fst .v3))
                  (.add (pGet (cGsIdx .v2) (.fst .v3)) (.nat 1))))
                (.pair (.fst (.snd .v3)) (.snd .v0)))
              (.bool false) ρ₄ s₁ P st' ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, ct⟩
              ((epMgmt_lists_eq hep).2.2.1 ▸ hBound.comp_le)
              rfl rfl rfl hRecE
            simp only [eval_ret, esMk, pair_eval, hRecord]
            subst hρ₁
            simp [ρ₄, ρ₃, ρ₂, ρ_top, ρ₀, pbaStage2RedEsEnc, pbaRedEsEnc,
              esAbort, esEnc, Expr.eval, Expr.v0, Expr.v1,
              Env.get_cons_zero, Env.get_cons_succ]
    · change _ = Prod.map id (pbaStage2RedEsEnc false) <$> (pure none : StateT _ _ _).run (es, winEp)
      rw [eval_caseSum_inl _ _ _ _ _ rfl, eval_caseSum_inl _ _ _ _ _ rfl,
          eval_caseSum_inl _ _ _ _ _ rfl, eval_caseSum_inr _ _ _ _ _ rfl]
      refine with_comp_env fun ρ₁ hρ₁ => ?_
      subst hρ₁
      simp [ρ_top, ρ₀, pbaStage2RedEsEnc, pbaRedEsEnc,
        Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v4,
        Env.get_cons_zero, Env.get_cons_succ]
    · change _ = Prod.map id (pbaStage2RedEsEnc false) <$>
        (do
          let (es0, winEp0) : PRNGBucketAuthEState Γ T RSt SS RS M E K I ← get
          let (out, es') ← StateT.lift ((deliverE hk fs.maxSkip cfg (P, c)).run es0)
          set (es', winEp0)
          return out).run (es, winEp)
      rw [eval_caseSum_inl _ _ _ _ _ rfl, eval_caseSum_inl _ _ _ _ _ rfl,
          eval_caseSum_inr _ _ _ _ _ rfl]
      refine with_comp_env fun ρ₁ hρ₁ => ?_
      rw [eval_bind]
      have hDel := deliverEC_eval prngBucketAuthHsEnc (PBAInv L (k + 1)) hkC hk hHk
        L fs.maxSkip cfgC cfg hCfg heqT heqM heqE
        (.fst .v3) .v0 ρ₁ es P c hInv hBound (hVR P) (by subst hρ₁; rfl) (by subst hρ₁; rfl)
      dsimp only [hkC, hkPbaModeC] at hDel
      rw [hDel, bind_map_left, map_bind]
      simp only [StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set, StateT.run_pure,
        pure_bind, bind_assoc, map_bind]
      refine bind_congr fun ⟨out, es'⟩ => ?_
      subst hρ₁
      rcases out with _ | (_ | m') <;>
        simp [ρ_top, ρ₀, pbaStage2RedEsEnc, pbaRedEsEnc,
          _root_.CryptoGames.SM.smRrDec, _root_.CryptoGames.SM.smRrEnc,
          Comp.eval, Prod.map,
          Expr.eval, Expr.v0, Expr.v4, Env.get_cons_zero, Env.get_cons_succ]
    · change _ = Prod.map id (pbaStage2RedEsEnc false) <$>
        (do
          let (es0, winEp0) : PRNGBucketAuthEState Γ T RSt SS RS M E K I ← get
          let wasWin := es0.g.win
          let (out, es') ← StateT.lift ((injectE hk (2 + Δcka) qep cfg (P, c)).run es0)
          let isNewForged :=
            decide (c.1.1 = (es0.g.st P).tcur + 1) && !isHonestHdrPRNGBucket es0.h c.1
          let winEp' :=
            if !wasWin && es'.g.win && (!false || isNewForged) then some c.1.1 else winEp0
          set (es', winEp')
          return out).run (es, winEp)
      rw [eval_caseSum_inl _ _ _ _ _ rfl, eval_caseSum_inr _ _ _ _ _ rfl]
      refine with_comp_env fun ρ₁ hρ₁ => ?_
      rw [eval_bind]
      have hInj := injectEC_eval prngBucketAuthHsEnc (PBAInv L (k + 1)) hkC hk hHk
        L (2 + Δcka) qep cfgC cfg hCfg heqT heqE
        (.fst .v2) .v0 ρ₁ es P c hInv hBound (hVR P) (by subst hρ₁; rfl) (by subst hρ₁; rfl)
      dsimp only [hkC, hkPbaModeC] at hInj
      rw [hInj, bind_map_left, map_bind]
      simp only [StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set, StateT.run_pure,
        pure_bind, bind_assoc, map_bind]

      refine bind_congr fun ⟨out, es'⟩ => ?_
      subst hρ₁
      rcases out with _ | (_ | m') <;>
        simp [ρ_top, ρ₀, pbaStage2RedEsEnc, pbaRedEsEnc,
          _root_.CryptoGames.SM.smRrDec, _root_.CryptoGames.SM.smRrEnc,
          cGsWin, esG, esEnc, cGsEnc, Comp.eval, Prod.map,
          Expr.eval, Expr.v0, Expr.v1, Expr.v3, Env.get_cons_zero, Env.get_cons_succ]
    · rw [implPRNGBucketAuthGen_corr_eq]
      rw [eval_caseSum_inr _ _ _ _ _ rfl]
      refine with_comp_env fun ρ₁ hρ₁ => ?_
      unfold corrE abortE
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      change _ <$> (Comp.ite _ _ _).eval ρ₁ = _
      rw [eval_ite]
      have hCorrOk : (cCorrAllowedE L (esG (.fst (Expr.v1 (O := OO)))) .v0).eval ρ₁ =
          es.g.corrAllowed P :=
        cCorrAllowedE_eval pbaVpEnc (O' := OO) L (esG (.fst .v1)) .v0 ρ₁ es.g P
          hBound.trans_le hBound.chall_le hBound.comp_le (by subst hρ₁; rfl) (by subst hρ₁; rfl)
      have hRefuse : (orE (esAbort (.fst (Expr.v1 (O := OO))))
          (orE (cGsWin (esG (.fst .v1)))
            (.not (cCorrAllowedE L (esG (.fst .v1)) .v0)))).eval ρ₁ =
          (es.abort || es.g.win || !(es.g.corrAllowed P)) := by
        simp only [orE_eval, not_eval, hCorrOk]
        subst hρ₁
        simp [ρ_top, esAbort, cGsWin, esG, esEnc, cGsEnc, Expr.eval, Expr.v1, Bool.or_assoc]
      rw [hRefuse]; clear hRefuse
      by_cases href : (es.abort || es.g.win || !(es.g.corrAllowed P))
      · simp only [href, ↓reduceIte]
        subst hρ₁
        simp [ρ_top, ρ₀, Comp.eval, StateT.run_pure,
          Prod.map, pbaStage2RedEsEnc, pbaRedEsEnc,
          Expr.eval, Expr.v1, Env.get_cons_zero, Env.get_cons_succ]
      · simp only [href, pbaNoDoomPolicy_leakDoom, pbaNoDoomPolicy_corrDoom, Bool.or_self,
          Bool.false_eq_true, ↓reduceIte, eval_bind]
        have hStP : (pGet (cGsSt (esG (.fst (Expr.v1 (O := OO))))) .v0).eval ρ₁ =
            pbaVpEnc (es.g.st P) :=
          pGet_eval (cGsSt (esG (.fst .v1))) .v0 ρ₁
            (fun Q => pbaVpEnc (es.g.st Q)) P (by subst hρ₁; rfl) (by subst hρ₁; rfl)
        have hRev := hHk.reveal_eval (esH (.fst .v1)) (esG (.fst .v1)) .v0
          (pGet (cGsSt (esG (.fst .v1))) .v0) ρ₁ es.h es.g P (es.g.st P) hInv
          (by subst hρ₁; rfl) (by subst hρ₁; rfl) (by subst hρ₁; rfl) hStP
        dsimp only [hkC, hkPbaModeC, hooksPRNGBucketAuthMainC, hooksPRNGBucketAuthForgedHdrC,
          hooksPRNGBucketAuthC] at hRev
        rw [hRev, bind_map_left, run_liftH_bind, map_bind, map_bind, map_bind]
        refine bind_congr fun ⟨revRes, h'⟩ => ?_
        rcases revRes with _ | stOut
        · subst hρ₁
          simp [ρ_top, ρ₀, Comp.eval, StateT.run_modify, Prod.map,
            pbaStage2RedEsEnc, pbaRedEsEnc, esMk, esG, esEnc,
            Expr.eval, Expr.v0, Expr.v2, Env.get_cons_zero, Env.get_cons_succ]
        · simp only [Prod.map, Option.map_some, id_eq, eval_caseOpt,
            StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, map_pure]
          set ρ₂ := Env.cons (t := psTy) (ckaPsEnc stOut)
            (Env.cons (t := .prod (.opt psTy) pbaHsTy)
              (some (ckaPsEnc stOut), prngBucketAuthHsEnc h') ρ₁)
          change _ <$> (Comp.ret _).eval ρ₂ = _
          have hAfter2 : (cAfterCorrE L (esG (.fst (Expr.v3 (O := OO)))) .v2).eval ρ₂ =
              cGsEnc pbaVpEnc (es.g.afterCorr P) :=
            cAfterCorrE_eval pbaVpEnc (O' := OO) L (esG (.fst .v3)) .v2 ρ₂ es.g P
              hBound.trans_le hBound.comp_u (by subst hρ₁; rfl) (by subst hρ₁; rfl)
          simp only [eval_ret, esMk, pair_eval, hAfter2]
          subst hρ₁
          simp [ρ₂, ρ_top, ρ₀, pbaStage2RedEsEnc, pbaRedEsEnc, ckaPsDec, ckaPsEnc,
            esAbort, esEnc, Expr.eval, Expr.v0, Expr.v1, Expr.v3,
            Env.get_cons_zero, Env.get_cons_succ]
  · simp only [↓reduceIte]
    rcases q with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
    · rw [implPRNGBucketAuthGen_tr_eq]
      rw [eval_caseSum_inl _ _ _ _ _ rfl, eval_caseSum_inl _ _ _ _ _ rfl,
          eval_caseSum_inl _ _ _ _ _ rfl, eval_caseSum_inl _ _ _ _ _ rfl]
      refine with_comp_env fun ρ₁ hρ₁ => ?_
      rw [eval_bind_ret]
      have hArg : (Expr.v0 (O := OO)).eval ρ₁ = (partyEnc P, m, r) := by
        subst hρ₁; rfl
      rw [hArg]; clear hArg
      set ρ₂ := Env.cons (t := .prod .bool (.prod (.base CKASort.msg) (.opt (.base CKASort.ccoins))))
        (partyEnc P, m, r) ρ₁
      unfold transmitE abortE
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      change _ <$> (Comp.ite _ _ _).eval ρ₂ = _
      rw [eval_ite]
      have hCond1 : (orE (esAbort (.fst (Expr.v5 (O := OO))))
          (cGsWin (esG (.fst .v5)))).eval ρ₂ = (es.abort || es.g.win) := by
        subst hρ₁
        simp [ρ₂, ρ_top, orE_eval, esAbort, cGsWin, esG, esEnc, cGsEnc,
          Expr.eval, Expr.v5, Env.get_cons_zero, Env.get_cons_succ]
      rw [hCond1]; clear hCond1
      by_cases hab : (es.abort || es.g.win)
      · simp only [hab, ↓reduceIte]
        subst hρ₁
        simp [ρ₂, ρ_top, ρ₀, Comp.eval, StateT.run_pure,
          Prod.map, pbaStage2RedEsEnc, pbaRedEsEnc,
          Expr.eval, Expr.v5, Env.get_cons_zero, Env.get_cons_succ]
      · simp only [hab, Bool.false_eq_true, ↓reduceIte]
        rw [eval_caseOpt]
        have hEp : (cEpMgmtE (2 + Δcka) qep (esG (.fst (Expr.v5 (O := OO)))) (.fst .v0)
            (isSomeE (.snd (.snd .v0)))).eval ρ₂ =
            (es.g.epMgmt (2 + Δcka) qep P r.isSome).map (cGsEnc pbaVpEnc) := by
          have := cEpMgmtE_eval pbaVpEnc (O' := OO) (2 + Δcka) qep
            (esG (.fst .v5)) (.fst .v0) (isSomeE (.snd (.snd .v0)))
            ρ₂ es.g P (by subst hρ₁; rfl) (by subst hρ₁; rfl)
          simpa [ρ₂, isSomeE_eval, Expr.eval, Env.get, Expr.v0] using this
        rw [hEp]; clear hEp
        rcases hep : es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁
        · subst hρ₁
          simp [ρ₂, ρ_top, ρ₀, Comp.eval, StateT.run_pure, Prod.map,
            pbaStage2RedEsEnc, pbaRedEsEnc,
            Expr.eval, Expr.v5, Env.get_cons_zero, Env.get_cons_succ]
        · simp only [Option.map_some, pbaNoDoomPolicy_leakDoom, Bool.false_eq_true, ↓reduceIte]
          set ρ₃ := Env.cons (t := cGsTy pbaVpTy) (cGsEnc pbaVpEnc s₁) ρ₂
          change _ <$> (Comp.bind (vSendC _ _ _ _ _ _ _ _) _).eval ρ₃ = _
          rw [eval_bind]
          have hStP : (pGet (cGsSt (Expr.v0 (O := OO))) (.fst .v1)).eval ρ₃ =
              pbaVpEnc (s₁.st P) :=
            pGet_eval (cGsSt .v0) (.fst .v1) ρ₃ (fun Q => pbaVpEnc (s₁.st Q)) P rfl rfl
          have hVSend := vSendC_eval hDefaultE prngBucketAuthHsEnc (PBAInv L (k + 1)) hkC hk hHk
            (esH (.fst .v6))
            .v0 (.fst .v1) (pGet (cGsSt .v0) (.fst .v1))
            (.fst (.snd .v1)) .none (.snd (.snd .v1))
            ρ₃ es.h s₁ P (s₁.st P) m none r hInv
            (by subst hρ₁; rfl) rfl rfl hStP rfl rfl rfl
          dsimp only [hkC, hkPbaModeC] at hVSend
          rw [hVSend, bind_map_left, run_liftH_bind, map_bind, map_bind, map_bind]
          refine bind_congr fun ⟨vsRes, h'⟩ => ?_
          rcases vsRes with _ | ⟨st', ct⟩
          · subst hρ₁
            simp [ρ₃, ρ₂, ρ_top, ρ₀, Comp.eval, StateT.run_modify, Prod.map,
              pbaStage2RedEsEnc, pbaRedEsEnc, esMk, esG, esEnc,
              Expr.eval, Expr.v0, Expr.v7, Env.get_cons_zero, Env.get_cons_succ]
          · simp only [Prod.map, Option.map_some, id_eq, eval_caseOpt,
              StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, map_pure]
            set ρ₄ := Env.cons (t := .prod pbaVpTy hdrCtTy) (pbaVpEnc st', ct)
              (Env.cons (t := .prod (.opt (.prod pbaVpTy hdrCtTy)) pbaHsTy)
                (some (pbaVpEnc st', ct), prngBucketAuthHsEnc h') ρ₃)
            change _ <$> (Comp.ret _).eval ρ₄ = _
            have hEp4 : (pGet (cGsEpoch (Expr.v2 (O := OO))) (.fst .v3)).eval ρ₄ = s₁.epoch P :=
              pGet_eval (cGsEpoch .v2) (.fst .v3) ρ₄ s₁.epoch P rfl rfl
            have hIdx4 : (pGet (cGsIdx (Expr.v2 (O := OO))) (.fst .v3)).eval ρ₄ = s₁.idx P :=
              pGet_eval (cGsIdx .v2) (.fst .v3) ρ₄ s₁.idx P rfl rfl
            have hRecE : (Expr.pair
                (.pair (.fst (Expr.v3 (O := OO)))
                  (.pair (pGet (cGsEpoch .v2) (.fst .v3))
                    (.add (pGet (cGsIdx .v2) (.fst .v3)) (.nat 1))))
                (.pair (.fst (.snd .v3)) (.snd .v0))).eval ρ₄ =
                cRecEnc ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, ct⟩ := by
              simp only [Expr.eval, hEp4, hIdx4]; rfl
            have hRecord := cRecordE_eval pbaVpEnc (O' := OO) L (2 + Δcka)
              (Expr.v2 (O := OO)) (.fst .v3) (.fst .v0)
              (.pair (.pair (.fst .v3)
                (.pair (pGet (cGsEpoch .v2) (.fst .v3))
                  (.add (pGet (cGsIdx .v2) (.fst .v3)) (.nat 1))))
                (.pair (.fst (.snd .v3)) (.snd .v0)))
              (.bool false) ρ₄ s₁ P st' ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, ct⟩
              ((epMgmt_lists_eq hep).2.2.1 ▸ hBound.comp_le)
              rfl rfl rfl hRecE
            simp only [eval_ret, esMk, pair_eval, hRecord]
            subst hρ₁
            simp [ρ₄, ρ₃, ρ₂, ρ_top, ρ₀, pbaStage2RedEsEnc, pbaRedEsEnc,
              esAbort, esEnc, Expr.eval, Expr.v0, Expr.v1,
              Env.get_cons_zero, Env.get_cons_succ]
    · change _ = Prod.map id (pbaStage2RedEsEnc true) <$> (pure none : StateT _ _ _).run (es, winEp)
      rw [eval_caseSum_inl _ _ _ _ _ rfl, eval_caseSum_inl _ _ _ _ _ rfl,
          eval_caseSum_inl _ _ _ _ _ rfl, eval_caseSum_inr _ _ _ _ _ rfl]
      refine with_comp_env fun ρ₁ hρ₁ => ?_
      subst hρ₁
      simp [ρ_top, ρ₀, pbaStage2RedEsEnc, pbaRedEsEnc,
        Comp.eval, StateT.run_pure, Prod.map, Expr.eval, Expr.v4,
        Env.get_cons_zero, Env.get_cons_succ]
    · change _ = Prod.map id (pbaStage2RedEsEnc true) <$>
        (do
          let (es0, winEp0) : PRNGBucketAuthEState Γ T RSt SS RS M E K I ← get
          let (out, es') ← StateT.lift ((deliverE hk fs.maxSkip cfg (P, c)).run es0)
          set (es', winEp0)
          return out).run (es, winEp)
      rw [eval_caseSum_inl _ _ _ _ _ rfl, eval_caseSum_inl _ _ _ _ _ rfl,
          eval_caseSum_inr _ _ _ _ _ rfl]
      refine with_comp_env fun ρ₁ hρ₁ => ?_
      rw [eval_bind]
      have hDel := deliverEC_eval prngBucketAuthHsEnc (PBAInv L (k + 1)) hkC hk hHk
        L fs.maxSkip cfgC cfg hCfg heqT heqM heqE
        (.fst .v3) .v0 ρ₁ es P c hInv hBound (hVR P) (by subst hρ₁; rfl) (by subst hρ₁; rfl)
      dsimp only [hkC, hkPbaModeC] at hDel
      rw [hDel, bind_map_left, map_bind]
      simp only [StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set, StateT.run_pure,
        pure_bind, bind_assoc, map_bind]
      refine bind_congr fun ⟨out, es'⟩ => ?_
      subst hρ₁
      rcases out with _ | (_ | m') <;>
        simp [ρ_top, ρ₀, pbaStage2RedEsEnc, pbaRedEsEnc,
          _root_.CryptoGames.SM.smRrDec, _root_.CryptoGames.SM.smRrEnc,
          Comp.eval, Prod.map,
          Expr.eval, Expr.v0, Expr.v4, Env.get_cons_zero, Env.get_cons_succ]
    · change _ = Prod.map id (pbaStage2RedEsEnc true) <$>
        (do
          let (es0, winEp0) : PRNGBucketAuthEState Γ T RSt SS RS M E K I ← get
          let wasWin := es0.g.win
          let (out, es') ← StateT.lift ((injectE hk (2 + Δcka) qep cfg (P, c)).run es0)
          let isNewForged :=
            decide (c.1.1 = (es0.g.st P).tcur + 1) && !isHonestHdrPRNGBucket es0.h c.1
          let winEp' :=
            if !wasWin && es'.g.win && (!true || isNewForged) then some c.1.1 else winEp0
          set (es', winEp')
          return out).run (es, winEp)
      rw [eval_caseSum_inl _ _ _ _ _ rfl, eval_caseSum_inr _ _ _ _ _ rfl]
      refine with_comp_env fun ρ₁ hρ₁ => ?_
      rw [eval_bind]
      have hInj := injectEC_eval prngBucketAuthHsEnc (PBAInv L (k + 1)) hkC hk hHk
        L (2 + Δcka) qep cfgC cfg hCfg heqT heqE
        (.fst .v2) .v0 ρ₁ es P c hInv hBound (hVR P) (by subst hρ₁; rfl) (by subst hρ₁; rfl)
      dsimp only [hkC, hkPbaModeC] at hInj
      rw [hInj, bind_map_left, map_bind]
      simp only [StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set, StateT.run_pure,
        pure_bind, bind_assoc, map_bind]

      refine bind_congr fun ⟨out, es'⟩ => ?_
      refine with_comp_env fun ρ₂ hρ₂ => ?_
      have hStP : (pGet (cGsSt (esG (.fst (Expr.v3 (O := OO))))) (.fst .v1)).eval ρ₂ =
          pbaVpEnc (es.g.st P) :=
        pGet_eval (cGsSt (esG (.fst .v3))) (.fst .v1) ρ₂
          (fun Q => pbaVpEnc (es.g.st Q)) P (by subst hρ₂; subst hρ₁; rfl) (by subst hρ₂; subst hρ₁; rfl)
      have hHon : (isHonestHdrPRNGBucketE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
          (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (esH (.fst .v3)) (.fst (.snd .v1))).eval ρ₂ = isHonestHdrPRNGBucket es.h c.1 :=
        isHonestHdrPRNGBucketE_eval heqT (esH (.fst .v3)) (.fst (.snd .v1)) ρ₂ es.h c.1
          (by subst hρ₂; subst hρ₁; rfl) (by subst hρ₂; subst hρ₁; rfl)
      have hTcur : (vpTcurNat (pGet (cGsSt (esG (.fst (Expr.v3 (O := OO))))) (.fst .v1))).eval ρ₂ =
          (es.g.st P).tcur := by
        simp [vpTcurNat, hStP, pbaVpEnc, vpTblEnc, vpEnc, Expr.eval]
      generalize hHonGen : isHonestHdrPRNGBucketE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
          (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (esH (.fst .v3)) (.fst (.snd .v1)) = honExpr at hHon ⊢
      generalize hTcurGen : vpTcurNat (pGet (cGsSt (esG (.fst (Expr.v3 (O := OO))))) (.fst .v1)) =
          tcurExpr at hTcur ⊢
      simp only [eval_ret, Expr.eval, hTcur, hHon]
      clear hStP hHon hTcur hHonGen hTcurGen honExpr tcurExpr
      subst hρ₂; subst hρ₁
      rcases out with _ | (_ | m') <;>
        simp [ρ_top, ρ₀, pbaStage2RedEsEnc, pbaRedEsEnc,
          _root_.CryptoGames.SM.smRrDec, _root_.CryptoGames.SM.smRrEnc,
          cGsWin, esG, esEnc, cGsEnc, Prod.map,
          Expr.eval, Expr.v0, Expr.v1, Expr.v3, Env.get_cons_zero, Env.get_cons_succ]
    · rw [implPRNGBucketAuthGen_corr_eq]
      rw [eval_caseSum_inr _ _ _ _ _ rfl]
      refine with_comp_env fun ρ₁ hρ₁ => ?_
      unfold corrE abortE
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      change _ <$> (Comp.ite _ _ _).eval ρ₁ = _
      rw [eval_ite]
      have hCorrOk : (cCorrAllowedE L (esG (.fst (Expr.v1 (O := OO)))) .v0).eval ρ₁ =
          es.g.corrAllowed P :=
        cCorrAllowedE_eval pbaVpEnc (O' := OO) L (esG (.fst .v1)) .v0 ρ₁ es.g P
          hBound.trans_le hBound.chall_le hBound.comp_le (by subst hρ₁; rfl) (by subst hρ₁; rfl)
      have hRefuse : (orE (esAbort (.fst (Expr.v1 (O := OO))))
          (orE (cGsWin (esG (.fst .v1)))
            (.not (cCorrAllowedE L (esG (.fst .v1)) .v0)))).eval ρ₁ =
          (es.abort || es.g.win || !(es.g.corrAllowed P)) := by
        simp only [orE_eval, not_eval, hCorrOk]
        subst hρ₁
        simp [ρ_top, esAbort, cGsWin, esG, esEnc, cGsEnc, Expr.eval, Expr.v1, Bool.or_assoc]
      rw [hRefuse]; clear hRefuse
      by_cases href : (es.abort || es.g.win || !(es.g.corrAllowed P))
      · simp only [href, ↓reduceIte]
        subst hρ₁
        simp [ρ_top, ρ₀, Comp.eval, StateT.run_pure,
          Prod.map, pbaStage2RedEsEnc, pbaRedEsEnc,
          Expr.eval, Expr.v1, Env.get_cons_zero, Env.get_cons_succ]
      · simp only [href, pbaNoDoomPolicy_leakDoom, pbaNoDoomPolicy_corrDoom, Bool.or_self,
          Bool.false_eq_true, ↓reduceIte, eval_bind]
        have hStP : (pGet (cGsSt (esG (.fst (Expr.v1 (O := OO))))) .v0).eval ρ₁ =
            pbaVpEnc (es.g.st P) :=
          pGet_eval (cGsSt (esG (.fst .v1))) .v0 ρ₁
            (fun Q => pbaVpEnc (es.g.st Q)) P (by subst hρ₁; rfl) (by subst hρ₁; rfl)
        have hRev := hHk.reveal_eval (esH (.fst .v1)) (esG (.fst .v1)) .v0
          (pGet (cGsSt (esG (.fst .v1))) .v0) ρ₁ es.h es.g P (es.g.st P) hInv
          (by subst hρ₁; rfl) (by subst hρ₁; rfl) (by subst hρ₁; rfl) hStP
        dsimp only [hkC, hkPbaModeC, hooksPRNGBucketAuthMainC, hooksPRNGBucketAuthForgedHdrC,
          hooksPRNGBucketAuthC] at hRev
        rw [hRev, bind_map_left, run_liftH_bind, map_bind, map_bind, map_bind]
        refine bind_congr fun ⟨revRes, h'⟩ => ?_
        rcases revRes with _ | stOut
        · subst hρ₁
          simp [ρ_top, ρ₀, Comp.eval, StateT.run_modify, Prod.map,
            pbaStage2RedEsEnc, pbaRedEsEnc, esMk, esG, esEnc,
            Expr.eval, Expr.v0, Expr.v2, Env.get_cons_zero, Env.get_cons_succ]
        · simp only [Prod.map, Option.map_some, id_eq, eval_caseOpt,
            StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, map_pure]
          set ρ₂ := Env.cons (t := psTy) (ckaPsEnc stOut)
            (Env.cons (t := .prod (.opt psTy) pbaHsTy)
              (some (ckaPsEnc stOut), prngBucketAuthHsEnc h') ρ₁)
          change _ <$> (Comp.ret _).eval ρ₂ = _
          have hAfter2 : (cAfterCorrE L (esG (.fst (Expr.v3 (O := OO)))) .v2).eval ρ₂ =
              cGsEnc pbaVpEnc (es.g.afterCorr P) :=
            cAfterCorrE_eval pbaVpEnc (O' := OO) L (esG (.fst .v3)) .v2 ρ₂ es.g P
              hBound.trans_le hBound.comp_u (by subst hρ₁; rfl) (by subst hρ₁; rfl)
          simp only [eval_ret, esMk, pair_eval, hAfter2]
          subst hρ₁
          simp [ρ₂, ρ_top, ρ₀, pbaStage2RedEsEnc, pbaRedEsEnc, ckaPsDec, ckaPsEnc,
            esAbort, esEnc, Expr.eval, Expr.v0, Expr.v1, Expr.v3,
            Env.get_cons_zero, Env.get_cons_succ]

open _root_.CryptoGames.SM.Engine
  (HooksCAgrees SMEngineInv SMVRInv transmitE corrE deliverE injectE abortE run_liftH_bind
   transmitE_inv deliverE_inv injectE_inv corrE_inv implE implE_vrInv) in
private theorem implPRNGBucketAuthGen_step_inv
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L k B B_q Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) (fm : Bool)
    {VROkStep : ℕ → RS → Prop}
    (hHk : HooksCAgrees (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      prngBucketAuthHsEnc (PBAInv L (k + 1)) (HBoundedPost := PBAInv L k)
      (VROk := VROkStep B_q)
      (hkPbaModeC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δcka qep tL t fm)
      (hkPbaMode cka prng fs Δcka qep tL t fm))
    (hVRHk : HooksVRInv VROkStep (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL t))
    (hInitR : ∀ k0, VROkStep 0 (fs.initReceiver k0))
    (es : EState (VP Γ T (Option RSt) SS RS) M (Header T × E) (PRNGBucketAuthState T RSt K I))
    (winEp : Option ℕ)
    (q : (spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hInv : PBAInv L (k + 1) es.h)
    (hEng : SMEngineInv L B_q (k + 1) es.g)
    (hVR : SMVRInv VROkStep B_q (k + 1) es.g) :
    ∀ res ∈ support (((implPRNGBucketAuthGen (hkPbaMode cka prng fs Δcka qep tL t fm)
        Δcka qep fs.maxSkip tL fm) (.inr q)).run (es, winEp)),
      PBAInv L k res.2.1.h ∧ SMEngineInv L B_q k res.2.1.g ∧
        SMVRInv VROkStep B_q k res.2.1.g := by
  let hk := hkPbaMode cka prng fs Δcka qep tL t fm
  have hVRMode := hkPbaMode_vrInv cka prng fs Δcka qep tL t fm hVRHk hInitR
  let cfg := bucketAuthCfg (M := M) Δcka tL
  rcases q with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
  · rw [implPRNGBucketAuthGen_tr_eq]
    intro res hmem
    rw [support_map, Set.mem_image] at hmem
    obtain ⟨⟨out, es'⟩, htr, rfl⟩ := hmem
    refine ⟨?_, transmitE_inv hk pbaNoDoomPolicy es (P, m, r) hEng (out, es') htr,
      implE_vrInv hk hVRMode (maxSkip := fs.maxSkip) cfg pbaNoDoomPolicy es
        (.inl (.inl (.inl (.inl (P, m, r))))) hEng hVR (out, es') htr⟩
    unfold transmitE abortE at htr
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at htr
    by_cases hab : (es.abort || es.g.win)
    · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at htr
      rcases htr with ⟨_, rfl⟩; exact hInv.mono (Nat.le_succ k)
    · simp only [hab, Bool.false_eq_true, ↓reduceIte] at htr
      rcases hep : es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁
      · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at htr
        rcases htr with ⟨_, rfl⟩; exact hInv.mono (Nat.le_succ k)
      · simp only [hep, pbaNoDoomPolicy_leakDoom, Bool.false_eq_true, ↓reduceIte,
          run_liftH_bind, mem_support_bind_iff] at htr
        obtain ⟨⟨vsRes, h'⟩, hvs, htr⟩ := htr
        have hInv' := vSend_pbaModeInv cka prng fs L k B B_q Δcka qep tL t fm hHk
          s₁ P (s₁.st P) m r es.h hInv (vsRes, h') hvs
        rcases vsRes with _ | ⟨st', ct⟩ <;>
          (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
             support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at htr;
           rcases htr with ⟨_, rfl⟩; exact hInv')
  · intro res hmem
    change res ∈ support ((pure none : StateT _ _ _).run (es, winEp)) at hmem
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    exact ⟨hInv.mono (Nat.le_succ k), hEng.mono (Nat.le_succ k),
      SMVRInv.mono (VROkStep := VROkStep) hVRMode.mono (Nat.le_succ k) hVR⟩
  · intro res hmem
    change res ∈ support ((do
      let (es0, winEp0) ← (get : StateT (PRNGBucketAuthEState Γ T RSt SS RS M E K I) _ _)
      let (out, es') ← StateT.lift ((deliverE hk fs.maxSkip cfg (P, c)).run es0)
      set (es', winEp0)
      return out).run (es, winEp)) at hmem
    simp only [StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set, StateT.run_pure,
      pure_bind, bind_assoc, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hmem
    obtain ⟨⟨out, es'⟩, hdel, rfl⟩ := hmem
    exact ⟨deliverE_pbaModeInv cka prng fs L k B B_q Δcka qep fs.maxSkip tL t fm cfg hHk es (P, c)
        hInv (out, es') hdel,
      deliverE_inv hk cfg es (P, c) hEng (out, es') hdel,
      implE_vrInv hk hVRMode (Δ := 2 + Δcka) (qep := qep) cfg pbaNoDoomPolicy es
        (.inl (.inl (.inr (P, c)))) hEng hVR (out, es') hdel⟩
  · intro res hmem
    change res ∈ support ((do
      let (es0, winEp0) : PRNGBucketAuthEState Γ T RSt SS RS M E K I ← get
      let wasWin := es0.g.win
      let (out, es') ← StateT.lift ((injectE hk (2 + Δcka) qep cfg (P, c)).run es0)
      let isNewForged :=
        decide (c.1.1 = (es0.g.st P).tcur + 1) && !isHonestHdrPRNGBucket es0.h c.1
      let winEp' :=
        if !wasWin && es'.g.win && (!fm || isNewForged) then some c.1.1 else winEp0
      set (es', winEp')
      return out).run (es, winEp)) at hmem
    simp only [StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set, StateT.run_pure,
      pure_bind, bind_assoc, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hmem
    obtain ⟨⟨out, es'⟩, hinj, rfl⟩ := hmem
    exact ⟨injectE_pbaModeInv cka prng fs L k B B_q Δcka qep tL t fm cfg hHk es (P, c) hInv
        (out, es') hinj,
      injectE_inv hk cfg es (P, c) hEng (out, es') hinj,
      implE_vrInv hk hVRMode (Δ := 2 + Δcka) (qep := qep) (maxSkip := fs.maxSkip) cfg
        pbaNoDoomPolicy es (.inl (.inr (P, c))) hEng hVR (out, es') hinj⟩
  · rw [implPRNGBucketAuthGen_corr_eq]
    intro res hmem
    rw [support_map, Set.mem_image] at hmem
    obtain ⟨⟨out, es'⟩, hcr, rfl⟩ := hmem
    refine ⟨?_, corrE_inv hk pbaNoDoomPolicy es P hEng (out, es') hcr,
      implE_vrInv hk hVRMode (Δ := 2 + Δcka) (qep := qep) (maxSkip := fs.maxSkip) cfg
        pbaNoDoomPolicy es (.inr P) hEng hVR (out, es') hcr⟩
    unfold corrE abortE at hcr
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hcr
    by_cases href : (es.abort || es.g.win || !(es.g.corrAllowed P))
    · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hcr
      rcases hcr with ⟨_, rfl⟩; exact hInv.mono (Nat.le_succ k)
    · simp only [href, pbaNoDoomPolicy_leakDoom, pbaNoDoomPolicy_corrDoom, Bool.or_false,
        Bool.false_eq_true, ↓reduceIte, run_liftH_bind, mem_support_bind_iff] at hcr
      obtain ⟨⟨revRes, h'⟩, hrev, hcr⟩ := hcr
      have hRevTbl : ∀ res ∈ support ((hk.reveal es.g P (es.g.st P)).run es.h),
          res.2.fTable = es.h.fTable := by
        intro r0 hr0
        cases fm
        · dsimp only [hk, hkPbaMode, hooksPRNGBucketAuthMain, hooksPRNGBucketAuthHybrid,
            liftPBucketAuth] at hr0
          simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr0
          rcases hres : resolveCorrRoot es.h (es.g.st P).tcur (es.g.st P).root with _ | σ <;>
            (rw [hres] at hr0; dsimp only at hr0)
          · by_cases hc : (!postLeak tL es.g && es.h.corrRoot.isNone &&
                !decide ((es.g.st P).tcur < healEpoch tL) &&
                ((es.g.st P).tcur == max (es.g.epoch .A) (es.g.epoch .B))) = true
            · simp only [hc, ↓reduceIte, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
                mem_support_bind_iff] at hr0
              obtain ⟨σOpt, _, hr0⟩ := hr0
              rcases σOpt with _ | σOut
              · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr0
                subst hr0; rfl
              · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                  support_pure, Set.mem_singleton_iff] at hr0
                subst hr0; rfl
            · simp only [hc, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, support_pure,
                Set.mem_singleton_iff] at hr0
              subst hr0; rfl
          · by_cases hc : (!decide ((es.g.st P).tcur < healEpoch tL) && es.h.corrRoot.isNone) = true
            · simp only [hc, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
                pure_bind, support_pure, Set.mem_singleton_iff] at hr0
              subst hr0; rfl
            · simp only [hc, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, support_pure,
                Set.mem_singleton_iff] at hr0
              subst hr0; rfl
        · dsimp only [hk, hkPbaMode, hooksPRNGBucketAuthForgedHdr] at hr0
          by_cases hc : (!decide ((es.g.st P).tcur < healEpoch tL) ||
              !decide (max (es.g.epoch .A) (es.g.epoch .B) < healEpoch tL)) = true
          · simp only [hc, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr0
            subst hr0; rfl
          · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hr0
            rcases hroot : (es.g.st P).root with _ | σ <;>
              (rw [hroot] at hr0; dsimp only at hr0;
               simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr0;
               subst hr0; rfl)
      have hfEq' := hRevTbl (revRes, h') hrev
      rcases revRes with _ | stOut <;>
        (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
           support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hcr;
         rcases hcr with ⟨_, rfl⟩;
         intro t0; dsimp only; rw [hfEq']; exact (hInv.mono (Nat.le_succ k)) t0)

open _root_.ReductionDsl (isGameQuery handlerImpl) in
open _root_.CryptoGames.SM.Engine (SMEngineInv SMVRInv) in
private theorem simulateQ_pbaHandle_eq
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B B_q Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) (fm : Bool)
    {VROkStep : ℕ → RS → Prop}
    (hSend : ckaSend = cka.send)
    (hRecv : ckaReceive = cka.receive)
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send)
    (hFsRecv : fsReceive = fs.receive)
    (heqT : eqT = (· == ·))
    (heqI : eqI = (· == ·))
    (heqM : eqM = (· == ·))
    (heqE : eqE = (· == ·))
    (hDefaultE : defaultE = default)
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hSampK : sampK = ($ᵗ K : ProbComp K))
    (hVRHk : HooksVRInv VROkStep (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL t))
    (hInitR : ∀ k0, VROkStep 0 (fs.initReceiver k0))
    (hFsB : ∀ rs hdr e rs' i m, VROkStep B_q rs → fs.receive rs hdr e = some (rs', i, m) → i ≤ B) :
    ∀ {α : Type}
      {oa : OracleComp (unifSpec + spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) α}
      {qAdv : ℕ},
      oa.IsQueryBoundP
        (isGameQuery (G := spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) qAdv →
      ∀ (st : PRNGBucketAuthEState Γ T RSt SS RS M E K I),
        PBAInv L qAdv st.1.h → SMEngineInv L B_q qAdv st.1.g →
        SMVRInv VROkStep B_q qAdv st.1.g →
        (simulateQ
          (handlerImpl (C := prngSMCodec KC Γ CCoins T I KR RSt K SS RS M E)
            (redPRNGAuthBucketHybridProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
              (ckaSend := ckaSend) (ckaReceive := ckaReceive)
              (prngInit := prngInit) (prngUp := prngUp)
              (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
              (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
              (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
              (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
              (sampI := sampI) (sampK := sampK)
              L B Δcka qep fs.maxSkip tL t).handle) oa).run (pbaStage2RedEsEnc fm st) =
          (Prod.map id (pbaStage2RedEsEnc fm) <$>
            (simulateQ (implPRNGBucketAuthGen (hkPbaMode cka prng fs Δcka qep tL t fm)
              Δcka qep fs.maxSkip tL fm) oa).run st) ∧
        ∀ res ∈ support ((simulateQ (implPRNGBucketAuthGen
            (hkPbaMode cka prng fs Δcka qep tL t fm) Δcka qep fs.maxSkip tL fm) oa).run st),
          PBAInv L 0 res.2.1.h ∧ SMEngineInv L B_q 0 res.2.1.g := by
  intro α oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro qAdv _ st hHB hInv _
    refine ⟨by simp [simulateQ_pure, Prod.map]; rfl, ?_⟩
    intro res hmem
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    exact ⟨hHB.mono (Nat.zero_le qAdv), hInv.mono (Nat.zero_le qAdv)⟩
  | query_bind q mx ih =>
    intro qAdv hq st hHB hInv hVR
    rw [isQueryBoundP_query_bind_iff] at hq
    rw [simulateQ_query_bind, simulateQ_query_bind]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq]
    erw [StateT.run_bind, StateT.run_bind]
    dsimp only [liftM, monadLift, MonadLift.monadLift]
    cases q with
    | inl n =>
      have hCoinL :
          ((handlerImpl (C := prngSMCodec KC Γ CCoins T I KR RSt K SS RS M E)
            (redPRNGAuthBucketHybridProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
              (ckaSend := ckaSend) (ckaReceive := ckaReceive)
              (prngInit := prngInit) (prngUp := prngUp)
              (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
              (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
              (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
              (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
              (sampI := sampI) (sampK := sampK)
              L B Δcka qep fs.maxSkip tL t).handle) (.inl n)).run (pbaStage2RedEsEnc fm st) =
          (fun u => (u, pbaStage2RedEsEnc fm st)) <$>
            query (spec := unifSpec + PRFPRNG.spec RSt I K) (.inl n) := by
        change (StateT.lift (query (spec := unifSpec + PRFPRNG.spec RSt I K) (.inl n))).run
          (pbaStage2RedEsEnc fm st) = _
        simp only [StateT.run_lift, map_eq_bind_pure_comp, Function.comp_def]
      have hCoinR :
          ((implPRNGBucketAuthGen (hkPbaMode cka prng fs Δcka qep tL t fm)
            Δcka qep fs.maxSkip tL fm) (.inl n)).run st =
          (fun u => (u, st)) <$>
            query (spec := unifSpec + PRFPRNG.spec RSt I K) (.inl n) := by
        change (StateT.lift (query (spec := unifSpec + PRFPRNG.spec RSt I K) (.inl n))).run st = _
        simp only [StateT.run_lift, map_eq_bind_pure_comp, Function.comp_def]
      erw [hCoinL]
      rw [hCoinR, bind_map_left]
      erw [bind_map_left]
      rw [map_bind]
      refine ⟨bind_congr fun u => (ih u (hq.2 u) st hHB hInv hVR).1, ?_⟩
      intro res hmem
      rw [mem_support_bind_iff] at hmem
      obtain ⟨u, _, hmem⟩ := hmem
      exact (ih u (hq.2 u) st hHB hInv hVR).2 res hmem
    | inr q0 =>
      have hpos : 0 < qAdv := hq.1.resolve_left (by simp [isGameQuery])
      obtain ⟨m, rfl⟩ : ∃ m, qAdv = m + 1 := ⟨qAdv - 1, by omega⟩
      have hqm : ∀ u, (mx u).IsQueryBoundP
          (isGameQuery (G := spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) m := by
        intro u; simpa [isGameQuery] using hq.2 u
      have hVRMode := hkPbaMode_vrInv cka prng fs Δcka qep tL t fm hVRHk hInitR
      have hVRB : ∀ P t₀ v, (st.1.g.st P).vR t₀ = some v → VROkStep B_q v :=
        fun P t₀ v hv => hVRMode.mono (Nat.sub_le B_q (m + 1)) (hVR P t₀ v hv)
      have hHk_m := hkPbaModeC_agrees_vr
        (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (prngInit := prngInit)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampI := sampI)
        cka prng fs L m B B_q Δcka qep tL t fm
        hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend hFsRecv heqT heqI
        hSampCCoins hSampK hVRHk hInitR hFsB
      have hStep :
          ((handlerImpl (C := prngSMCodec KC Γ CCoins T I KR RSt K SS RS M E)
            (redPRNGAuthBucketHybridProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
              (ckaSend := ckaSend) (ckaReceive := ckaReceive)
              (prngInit := prngInit) (prngUp := prngUp)
              (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
              (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
              (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
              (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
              (sampI := sampI) (sampK := sampK)
              L B Δcka qep fs.maxSkip tL t).handle) (.inr q0)).run (pbaStage2RedEsEnc fm st) =
          Prod.map id (pbaStage2RedEsEnc fm) <$>
            ((implPRNGBucketAuthGen (hkPbaMode cka prng fs Δcka qep tL t fm)
              Δcka qep fs.maxSkip tL fm) (.inr q0)).run st := by
        rcases st with ⟨es, winEp⟩
        have hEval := rdec_pbaHandle_eval cka prng fs L m B B_q Δcka qep tL t fm
          hDefaultE heqT heqM heqE hHk_m es winEp q0 hHB hInv.toBoundedEngine hVRB
        simp only [map_eq_bind_pure_comp, Function.comp_def] at hEval
        simp only [handlerImpl, map_eq_bind_pure_comp, Function.comp_def]
        exact hEval
      erw [hStep, bind_map_left]
      rw [map_bind]
      refine ⟨OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, st₁⟩ hmem => ?_, ?_⟩
      · obtain ⟨hHB₁, hInv₁, hVR₁⟩ := implPRNGBucketAuthGen_step_inv
          cka prng fs L m B B_q Δcka qep tL t fm hHk_m hVRHk hInitR st.1 st.2 q0
          hHB hInv hVR (u, st₁) hmem
        exact (ih u (hqm u) st₁ hHB₁ hInv₁ hVR₁).1
      · intro res hmem
        rw [mem_support_bind_iff] at hmem
        obtain ⟨⟨u, st₁⟩, hmem₁, hmem₂⟩ := hmem
        obtain ⟨hHB₁, hInv₁, hVR₁⟩ := implPRNGBucketAuthGen_step_inv
          cka prng fs L m B B_q Δcka qep tL t fm hHk_m hVRHk hInitR st.1 st.2 q0
          hHB hInv hVR (u, st₁) hmem₁
        exact (ih u (hqm u) st₁ hHB₁ hInv₁ hVR₁).2 res hmem₂

open _root_.CryptoGames.SM.Engine (TComp) in
private theorem simulateQ_liftM_unif_pba {ι : Type} {tspec : OracleSpec.{0, 0} ι} {St α : Type}
    (impl : QueryImpl tspec (StateT St ProbComp)) (mx : ProbComp α) :
    simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl)
      (liftM mx : TComp tspec α) =
    StateT.lift mx := by
  ext st
  change (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl)
    (liftM mx : TComp tspec α)).run st = (mx >>= fun a => pure (a, st))
  rw [← liftComp_eq_liftM]
  induction mx using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t0 r ih =>
    rw [liftComp_bind, liftComp_liftM_query]
    have hq : (liftM (OracleSpec.query t0) : TComp tspec _) =
        (liftM (OracleSpec.query (spec := unifSpec + tspec) (.inl t0)) : TComp tspec _) := rfl
    have hrun :
        ((liftM ((QueryImpl.liftTarget (StateT St ProbComp)
          (QueryImpl.ofLift unifSpec ProbComp) + impl)
          (.inl t0)) : StateT St ProbComp (unifSpec.Range t0))).run st =
        ((liftM (OracleSpec.query t0) : ProbComp _) >>= fun u => pure (u, st)) := rfl
    rw [hq, simulateQ_query_bind]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, StateT.run_bind]
    rw [hrun]
    simp only [bind_assoc, pure_bind, ih]

private theorem simulateQ_sampleT_run_pba {ι : Type} {tspec : OracleSpec.{0, 0} ι} {St α : Type}
    [SampleableType α] (impl : QueryImpl tspec (StateT St ProbComp)) (st : St) :
    (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl)
      (sampleT α)).run st =
    (($ᵗ α : ProbComp α) >>= fun a => pure (a, st)) := by
  unfold sampleT
  rw [simulateQ_liftM_unif_pba]
  rfl


private theorem rootPRNGBucketAuthHybrid_zero_support_some
    [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR RSt I K) (tL : Option ℕ) (t : ℕ) (lam : I) (kr : KR) (b_prng : Bool)
    (step : Option (Option RSt × K)) (h₀ : PRNGBucketAuthState T RSt K I)
    (sp : PRFPRNG.GameState RSt I K)
    (hmem : ((step, h₀), sp) ∈ support
      ((simulateQ
        ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (PRFPRNG.GameState RSt I K) ProbComp) + PRFPRNG.oracleImpl prng)
        ((rootPRNGBucketAuthHybrid (T := T) prng tL t 0 false lam none).run {})).run
        { σ := prng.init kr, b := b_prng })) :
    ∃ σv k, step = some (σv, k) := by
  unfold rootPRNGBucketAuthHybrid liftPBucketAuth at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  have h0_lt : ¬(t < 0) := by omega
  have hCr0 : ({} : PRNGBucketAuthState T RSt K I).corrRoot = none := rfl
  simp only [h0_lt, ↓reduceIte, Option.isSome_none, Bool.or_false,
    Bool.false_eq_true] at hmem
  by_cases hts : 0 = t
  · subst hts
    have hcond' : (tL.isSome && decide (0 = healEpoch tL)) = false := by
      rcases tL with _ | l <;> simp [healEpoch]
    simp only [↓reduceIte, hcond', Bool.false_eq_true] at hmem
    cases b_prng
    · simp [PRFPRNG.challPrfQuery, PRFPRNG.oracleImpl, PRFPRNG.challPrfImpl,
        StateT.run_bind, StateT.run_pure, StateT.run_get, StateT.run_set, StateT.run_lift,
        simulateQ_bind, simulateQ_query, simulateQ_pure,
        map_eq_bind_pure_comp, bind_assoc] at hmem
      rcases hmem with ⟨⟨rfl, _⟩, _⟩
      exact ⟨_, _, rfl⟩
    · simp [PRFPRNG.challPrfQuery, PRFPRNG.oracleImpl, PRFPRNG.challPrfImpl, List.lookup,
        StateT.run_bind, StateT.run_pure, StateT.run_get, StateT.run_set, StateT.run_lift,
        StateT.run_modify, StateT.run_monadLift, monadLift_self,
        simulateQ_bind, simulateQ_query, simulateQ_pure,
        map_eq_bind_pure_comp, bind_assoc] at hmem
      rcases hmem with ⟨R', ⟨rfl, _⟩, _⟩
      exact ⟨_, _, rfl⟩
  · simp only [hts, ↓reduceIte] at hmem
    rcases tL with _ | l
    · have hHeal0 : ¬(0 < healEpoch none) := by simp [healEpoch]
      simp only [hHeal0, decide_false, Bool.not_false, Option.isSome_none, Bool.false_and,
        Bool.false_eq_true, ↓reduceIte] at hmem
      have hTbl0 : (({} : PRNGBucketAuthState T RSt K I).fTable 0) = [] := rfl
      simp [lookupPRNGBucketAuthF, List.lookup,
        PRFPRNG.processQuery, PRFPRNG.oracleImpl, PRFPRNG.processImpl, PRFPRNG.samIfNec,
        StateT.run_bind, StateT.run_pure, StateT.run_lift, StateT.run_get, StateT.run_set,
        StateT.run_modify, simulateQ_bind, simulateQ_query, simulateQ_pure,
        map_eq_bind_pure_comp, bind_assoc] at hmem
      rcases hmem with ⟨kRand, ⟨⟨rfl, _⟩, _⟩, _⟩
      exact ⟨_, _, rfl⟩
    · have hHeal1 : 0 < healEpoch (some l) := by simp [healEpoch]
      simp only [hHeal1, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hmem
      simp [PRFPRNG.processQuery, PRFPRNG.corrQuery, PRFPRNG.oracleImpl, PRFPRNG.processImpl,
        PRFPRNG.corrImpl, PRFPRNG.samIfNec, StateT.run_bind, StateT.run_pure, StateT.run_lift,
        StateT.run_get, StateT.run_set, simulateQ_bind, simulateQ_query, simulateQ_pure,
        map_eq_bind_pure_comp, bind_assoc] at hmem
      rcases hmem with ⟨⟨rfl, _⟩, _⟩
      exact ⟨_, _, rfl⟩

open _root_.ReductionDsl (isGameQuery) in
open _root_.CryptoGames.CKA (ckaSamplers) in
open _root_.CryptoGames.SM (pair_eval not_eval) in
open _root_.CryptoGames.SM.Engine
  (eval_bind eval_bind_ret eval_caseOpt eval_ret esEnc esG esAbort cGsWin cGsEnc
   cAuthOKE cAuthOKE_eval optNatLit optNatLit_eval) in
open _root_.CryptoGames.SM.Engine.RedPRNG (liftP_eq_liftM) in
private theorem redPRNGAuthBucketHybridProg_eval_eq_bind_vr
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B B_q Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    {VROkStep : ℕ → RS → Prop}
    (hInitA : ckaInitA = cka.initA)
    (hInitB : ckaInitB = cka.initB)
    (hSend : ckaSend = cka.send)
    (hRecv : ckaReceive = cka.receive)
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send)
    (hFsRecv : fsReceive = fs.receive)
    (heqT : eqT = (· == ·))
    (heqI : eqI = (· == ·))
    (heqM : eqM = (· == ·))
    (heqE : eqE = (· == ·))
    (hDefaultE : defaultE = default)
    (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hSampK : sampK = ($ᵗ K : ProbComp K))
    (hVRHk : HooksVRInv VROkStep (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL t))
    (hInitR : ∀ k, VROkStep 0 (fs.initReceiver k))
    (hFsB : ∀ rs hdr e rs' i m, VROkStep B_q rs → fs.receive rs hdr e = some (rs', i, m) → i ≤ B)
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : SchemeAdversary Γ T RSt SS RS M CCoins E) (qAdv : ℕ)
    (hA : MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q) :
    (redPRNGAuthBucketHybridProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L B Δcka qep fs.maxSkip tL t).eval (fun _ => A) () =
      (do
        let fm ← sampleT Bool
        let es₀ ← initPRNGBucketAuthRaw cka prng fs lam tL t false
        let (_, es', winEp') ←
          (simulateQ (implPRNGBucketAuthGen (hkPbaMode cka prng fs Δcka qep tL t fm)
            Δcka qep fs.maxSkip tL fm) A).run (es₀, none)
        match winEp' with
        | none => pure false
        | some tWin =>
          pure (!es'.abort && es'.g.win && authLosingConditionsAvoided (2 + Δcka) tL tWin es'.g)) := by
  have hA' : A.IsQueryBoundP
      (isGameQuery (G := spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) qAdv := by
    refine hA.of_imp (fun x hx => ?_)
    rcases x with _ | _ <;> simp_all [isGameQuery]
  dsimp only [CostedReduction.eval, CostedReduction.impl, redPRNGAuthBucketHybridProg]
  rw [eval_bind]
  have hBit : (Comp.sample (O := OO) (I := II) CKASamp.bit .unit).eval
      (Env.cons (t := (.unit : Ty S)) () .nil) = sampleT Bool := by
    simp only [Comp.eval, prngIface, prngSamplers, ckaSamplers, sampleT]
    exact liftP_eq_liftM II (fun _ => rfl) ($ᵗ Bool)
  rw [hBit, bind_assoc]
  refine bind_congr fun fm => ?_
  set ρ_fm := Env.cons (t := (.bool : Ty S)) fm (Env.cons (t := (.unit : Ty S)) () .nil)
  have hInit := initPRNGBucketAuthEStateC_eval
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (fsSend := fsSend) (fsReceive := fsReceive)
    (eqT := eqT) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampCCoins := sampCCoins) (sampI := sampI)
    cka prng fs hInitA hInitB hPrngUp hFsInitS hFsInitR heqI hSampKC hSampK
    L tL t (.bool false) ρ_fm
  rw [eval_bind, hInit]
  simp only [bind_map_left, eval_ret, ρ_fm, Expr.eval, Expr.v0, Expr.v1,
    Env.get_cons_zero, Env.get_cons_succ, bind_assoc, pure_bind]
  refine OracleComp.bind_congr_of_forall_mem_support
    (initPRNGBucketAuthRaw cka prng fs lam tL t false) fun es₀ hes₀ => ?_
  have hVRMode := hkPbaMode_vrInv cka prng fs Δcka qep tL t fm hVRHk hInitR
  obtain ⟨hPBA₀, hInv₀, hVR₀⟩ := initPRNGBucketAuthRaw_inv cka prng fs lam tL t false
    hqB hB1 hBB (fun k => hVRMode.mono (Nat.zero_le _) (hInitR k)) es₀ hes₀
  obtain ⟨hSim, hSimInv⟩ := simulateQ_pbaHandle_eq
    (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (prngInit := prngInit)
    (lam := lam) (sampKR := sampKR) (sampKC := sampKC) (sampI := sampI)
    cka prng fs L B B_q Δcka qep tL t fm
    hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend hFsRecv
    heqT heqI heqM heqE hDefaultE hSampCCoins hSampK hVRHk hInitR hFsB
    hA' (es₀, none) hPBA₀ hInv₀ hVR₀
  dsimp only [redPRNGAuthBucketHybridProg, pbaStage2RedEsEnc, pbaRedEsEnc] at hSim
  erw [hSim, bind_map_left]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨b', es', winEp'⟩ hes' => ?_
  obtain ⟨_, hInv'⟩ := hSimInv (b', es', winEp') hes'
  have hBnd' := hInv'.toBoundedEngine
  dsimp only [Prod.map, id_eq]
  rw [eval_bind_ret]
  set ρ_f := Env.cons (t := pbaStage2RedEsTy) (pbaStage2RedEsEnc fm (es', winEp'))
    (Env.cons (t := (.bool : Ty S)) b' .nil)
  have hPair : (Expr.pair (.fst (.fst (Expr.var (O := OO) .zero)))
      (.snd (.fst (.var .zero)))).eval ρ_f =
      (esEnc pbaVpEnc prngBucketAuthHsEnc es', winEp') := rfl
  rw [hPair]; clear hPair
  set ρ_f1 := Env.cons (t := pbaRedEsTy) (esEnc pbaVpEnc prngBucketAuthHsEnc es', winEp') ρ_f
  change (Comp.caseOpt _ _ _).eval ρ_f1 = _
  rw [eval_caseOpt]
  have hWinOpt : (Expr.snd (Expr.var (O := OO) .zero)).eval ρ_f1 = winEp' := rfl
  rw [hWinOpt]; clear hWinOpt
  rcases winEp' with _ | tWin
  · simp only [eval_ret, Expr.eval]
  · dsimp only
    set ρ_w := Env.cons (t := (.nat : Ty S)) tWin ρ_f1
    change (Comp.ret _).eval ρ_w = _
    rw [eval_ret]
    have hAuthOK := cAuthOKE_eval (vpEncFn := pbaVpEnc) (O' := OO) L (2 + Δcka)
      (optNatLit (O' := OO) tL) (.var .zero) (esG (.fst (.var (.succ .zero)))) ρ_w es'.g
      hBnd'.leaks_le hBnd'.corrs_le rfl
    have htWin : (Expr.var (O := OO) .zero).eval ρ_w = tWin := rfl
    rw [optNatLit_eval, htWin] at hAuthOK
    generalize hAuthGen : cAuthOKE (O' := OO) L (2 + Δcka) (optNatLit (O' := OO) tL)
      (.var .zero) (esG (.fst (.var (.succ .zero)))) = authExpr at hAuthOK ⊢
    simp only [Expr.eval, hAuthOK]
    clear hAuthOK hAuthGen authExpr htWin
    simp only [ρ_w, ρ_f1, esAbort, esG, cGsWin, esEnc, cGsEnc, Expr.eval,
      Env.get_cons_zero, Env.get_cons_succ, Bool.and_assoc]

/-- Evaluation bridge (`HooksVRInv` / `fromAEADPRG`) for `redPRNGAuthBucketHybridProg`: under
`MakesAtMostQueries A qAdv` and `qAdv ≤ B_q`, the costed program's `PRFPRNG.branch b_prng`
computation equals shallow `redPRNGAuthBucketHybrid`. -/
theorem redPRNGAuthBucketHybridProg_branch_eval_vr_impl
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B B_q Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    {VROkStep : ℕ → RS → Prop}
    (hInitA : ckaInitA = cka.initA)
    (hInitB : ckaInitB = cka.initB)
    (hSend : ckaSend = cka.send)
    (hRecv : ckaReceive = cka.receive)
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send)
    (hFsRecv : fsReceive = fs.receive)
    (heqT : eqT = (· == ·))
    (heqI : eqI = (· == ·))
    (heqM : eqM = (· == ·))
    (heqE : eqE = (· == ·))
    (hDefaultE : defaultE = default)
    (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hSampI : sampI = ($ᵗ I : ProbComp I))
    (hSampK : sampK = ($ᵗ K : ProbComp K))
    (hVRHk : HooksVRInv VROkStep (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL t))
    (hInitR : ∀ k, VROkStep 0 (fs.initReceiver k))
    (hFsB : ∀ rs hdr e rs' i m, VROkStep B_q rs → fs.receive rs hdr e = some (rs', i, m) → i ≤ B)
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : SchemeAdversary Γ T RSt SS RS M CCoins E) (qAdv : ℕ)
    (hA : MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q)
    (b_prng : Bool) :
    PRFPRNG.branch prng b_prng
      ((redPRNGAuthBucketHybridProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
          (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK)
          L B Δcka qep fs.maxSkip tL t).eval (fun _ => A) ()) =
      PRFPRNG.branch prng b_prng (redPRNGAuthBucketHybrid cka prng fs lam Δcka qep tL t A) := by
  let _ := hSampI
  rw [redPRNGAuthBucketHybridProg_eval_eq_bind_vr cka prng fs L B B_q Δcka qep tL t
    hInitA hInitB hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend hFsRecv
    heqT heqI heqM heqE hDefaultE hSampKC hSampCCoins hSampK hVRHk hInitR hFsB hB1 hBB A qAdv hA hqB]
  unfold PRFPRNG.branch redPRNGAuthBucketHybrid
  refine bind_congr fun kr => ?_
  rw [StateT.run'_eq, StateT.run'_eq]
  refine congrArg (Prod.fst <$> ·) ?_
  simp only [StateT.run_bind, simulateQ_bind, simulateQ_sampleT_run_pba, bind_assoc, pure_bind]
  refine bind_congr fun fm => ?_
  cases fm
  · simp only [Bool.false_eq_true, ↓reduceIte]
    unfold redPRNGAuthBucketHybridMain runPRNGAuthBucketHybridGen
      initPRNGBucketAuthHybrid initPRNGBucketAuthRaw hkPbaMode
    dsimp only
    simp only [StateT.run_bind, StateT.run_lift, simulateQ_bind, simulateQ_sampleT_run_pba,
      bind_assoc, pure_bind]
    refine bind_congr fun kc => ?_
    refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨step, h₀⟩, sp⟩ hmem => ?_
    obtain ⟨σv, k, rfl⟩ := rootPRNGBucketAuthHybrid_zero_support_some (T := T)
      prng tL t lam kr b_prng step h₀ sp hmem
    simp only [StateT.run_bind, simulateQ_bind, StateT.run_pure, simulateQ_pure,
      pure_bind, bind_assoc]
    refine congrArg (· >>= _) ?_
    congr
  · simp only [↓reduceIte]
    unfold redPRNGAuthBucketHybridForgedHdr runPRNGAuthBucketHybridGen
      initPRNGBucketAuthHybrid initPRNGBucketAuthRaw hkPbaMode
    dsimp only
    simp only [StateT.run_bind, StateT.run_lift, simulateQ_bind, simulateQ_sampleT_run_pba,
      bind_assoc, pure_bind]
    refine bind_congr fun kc => ?_
    refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨step, h₀⟩, sp⟩ hmem => ?_
    obtain ⟨σv, k, rfl⟩ := rootPRNGBucketAuthHybrid_zero_support_some (T := T)
      prng tL t lam kr b_prng step h₀ sp hmem
    simp only [StateT.run_bind, simulateQ_bind, StateT.run_pure, simulateQ_pure,
      pure_bind, bind_assoc]
    refine congrArg (· >>= _) ?_
    congr

end CostedBucketAuth

end

end Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthEval
