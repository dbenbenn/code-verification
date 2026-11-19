/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGDefs -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGEvalHooks
import Computational.Proofs.ReductionDsl.SM.DeliverForgeBucketSimEval
import Computational.Proofs.ReductionDsl.Bridge
import Computational.Proofs.ReductionDsl.Notation

set_option autoImplicit false
set_option linter.unusedSectionVars false
open CryptoGames (CKAScheme FSAEADScheme PRFPRNG Party)
open CryptoGames.CKA (ckaPsEnc ckaSamplers)
open CryptoGames.PRFPRNG (prngIface prngOps prngSamplers prngSig)
open CryptoGames.SM (Config leN maxN orE orE_eval pair_eval some_eval)
open CryptoGames.SM.Construction (Header PartyState abortedParties abortedPartiesE abortedPartiesE_eval healEpoch hooksPRNGBucketParPaperC_agrees_vr hooksPRNGBucketSplitPaperC initPRNGBucketHybridEStateC isHonestHdrPRNGBucketE mkParties prngBucketEsTy prngBucketHsCache prngBucketHsCorrRoot prngBucketHsEmptyE prngBucketHsEnc prngBucketHsTy prngBucketRedEsTy prngBucketRevealForgedHdrC prngBucketStartRecvMainC prngVpEnc prngVpTy resolveCorrRootE rootPRNGBucketHybridC_eval rootPRNGBucketHybrid_fTable_len sampleT validGuessBucketParPaperE validGuessBucketParPaperE_eval)
open CryptoGames.SM.Engine (Ctx EState Hooks HooksCAgrees HooksVRInv SMEngineInv SMVRInv TComp VP abortE cGsEnc cGsEpoch cGsInitE_eval cGsTy commitE deliverE esEnc esMk eval_bind eval_bind_ret eval_caseOpt eval_ite eval_ret injectE liftP_eq_liftM mkPartiesE mkPartiesE_eval realPartyE_eval run_liftH_bind vRecv_bounded vSend vSendStep1_bounded vSend_eq_bind vpRoot vpTcurNat vpVR vpVS vpΓ)
open ReductionDsl (Env Expr Ty)

namespace Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGSplitEvalHooks

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

@[expose] def initPRNGBucketRaw [DecidableEq I] [SampleableType KC] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (Δbucket : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) (b : Bool) :
    _root_.CryptoGames.PRFPRNG.AdversaryComp RSt I K
      (EState (VP Γ T (Option RSt) SS RS) M (Header T × E)
        (_root_.CryptoGames.SM.Construction.DeliverForge.PRNGBucketState T RSt K I)) := do
  let kc ← sampleT KC
  let (step, h₀) ← (_root_.CryptoGames.SM.Construction.DeliverForge.rootPRNGBucketHybrid prng Δbucket tL par t 0 false lam none).run {}
  match step with
  | none =>
    let (vA, vB) := abortedParties (T := T) (RSt := RSt) (SS := SS) (RS := RS)
      (cka.initA kc) (cka.initB kc)
    pure { g := { st := fun | .A => vA | .B => vB, b := b }, h := h₀, abort := true }
  | some (σv, k) =>
    let (vA, vB) := mkParties (T := T) (cka.initA kc) (cka.initB kc) σv
      (fs.initSender k) (fs.initReceiver k)
    pure { g := { st := fun | .A => vA | .B => vB, b := b }, h := h₀, abort := false }

theorem initPRNGBucketHybridEStateC_eval [DecidableEq I] [SampleableType KC] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (hInitA : ckaInitA = cka.initA)
    (hInitB : ckaInitB = cka.initB)
    (hPrngUp : prngUp = prng.up)
    (heqI : eqI = (· == ·))
    (hFsInitS : fsInitSender = fs.initSender)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (hSampK : sampK = ($ᵗ K : ProbComp K))
    (L Δbucket : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) {Γ'} (bE : Expr OOev Γ' .bool) (ρ : Env Γ') :
    (initPRNGBucketHybridEStateC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L Δbucket tL par t bE).eval ρ =
      esEnc prngVpEnc prngBucketHsEnc <$>
        initPRNGBucketRaw cka prng fs lam Δbucket tL par t (bE.eval ρ) := by
  unfold initPRNGBucketHybridEStateC initPRNGBucketRaw
  rw [eval_bind_ret]
  set b := bE.eval ρ
  set ρ₁ := _root_.ReductionDsl.Env.cons (t := (.bool : Ty Sev)) b ρ
  rw [eval_bind, map_bind]
  have hKC : (@_root_.ReductionDsl.Comp.sample _ _ _ OOev IIev _ _root_.CryptoGames.CKA.CKASamp.kc .unit).eval ρ₁ = sampleT KC := by
    simp only [_root_.ReductionDsl.Comp.eval, prngIface, prngSamplers, ckaSamplers, hSampKC, sampleT]
    exact liftP_eq_liftM IIev (fun _ => rfl) ($ᵗ KC)
  rw [hKC]
  refine bind_congr fun kc => ?_
  set ρ₂ := _root_.ReductionDsl.Env.cons (t := (.base .kc : Ty Sev)) kc ρ₁
  rw [eval_bind, map_bind]
  have ⟨hRoot, _⟩ := rootPRNGBucketHybridC_eval
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)
    prng hPrngUp heqI hSampK L Δbucket tL par t
    prngBucketHsEmptyE (.nat 0) (.bool false) (_root_.ReductionDsl.Expr.op (O := OOev) _root_.CryptoGames.CKA.CKAOp.lamI .unit) .none ρ₂
    ({} : _root_.CryptoGames.SM.Construction.DeliverForge.PRNGBucketState T RSt K I) rfl (Nat.zero_le L)
  simp only [_root_.ReductionDsl.Expr.eval] at hRoot
  rw [hRoot, bind_map_left]
  refine bind_congr fun ⟨step, h₀⟩ => ?_
  dsimp only [Prod.map, id_eq]
  set ρ₂p := _root_.ReductionDsl.Env.cons
    (t := (.prod (.opt (.prod (.opt (.base .sig)) (.base .k))) pbHsTyEv : Ty Sev))
    (step, prngBucketHsEnc h₀) ρ₂
  rcases step with _ | ⟨σv, k⟩
  · simp only [eval_caseOpt, _root_.ReductionDsl.Expr.eval, _root_.ReductionDsl.Expr.v0, map_pure]
    change (_root_.ReductionDsl.Comp.ret _).eval ρ₂p = _
    rw [eval_ret]
    set pAB := abortedParties (T := T) (RSt := RSt) (SS := SS) (RS := RS)
      (cka.initA kc) (cka.initB kc)
    have hAbP := abortedPartiesE_eval
      (_root_.ReductionDsl.Expr.op (O := OOev) _root_.CryptoGames.CKA.CKAOp.ckaInitA .v1) (_root_.ReductionDsl.Expr.op (O := OOev) _root_.CryptoGames.CKA.CKAOp.ckaInitB .v1) ρ₂p
    have hAbP' :
        (abortedPartiesE
          (_root_.ReductionDsl.Expr.op (O := OOev) _root_.CryptoGames.CKA.CKAOp.ckaInitA .v1)
          (_root_.ReductionDsl.Expr.op (O := OOev) _root_.CryptoGames.CKA.CKAOp.ckaInitB .v1)).eval ρ₂p =
          (prngVpEnc pAB.1, prngVpEnc pAB.2) := by
      rw [hAbP]
      simp [ρ₂p, ρ₂, ρ₁, hInitA, hInitB, pAB, Prod.map, _root_.ReductionDsl.Expr.eval, _root_.ReductionDsl.Expr.v1]
    have hGs := cGsInitE_eval prngVpEnc (O' := OOev)
      (.fst (abortedPartiesE
        (_root_.ReductionDsl.Expr.op (O := OOev) _root_.CryptoGames.CKA.CKAOp.ckaInitA .v1) (_root_.ReductionDsl.Expr.op (O := OOev) _root_.CryptoGames.CKA.CKAOp.ckaInitB .v1)))
      (.snd (abortedPartiesE
        (_root_.ReductionDsl.Expr.op (O := OOev) _root_.CryptoGames.CKA.CKAOp.ckaInitA .v1) (_root_.ReductionDsl.Expr.op (O := OOev) _root_.CryptoGames.CKA.CKAOp.ckaInitB .v1)))
      .v2 ρ₂p pAB.1 pAB.2
      (by simp [_root_.ReductionDsl.Expr.eval, hAbP']) (by simp [_root_.ReductionDsl.Expr.eval, hAbP'])
    simp only [esMk, pair_eval, hGs]
    rfl
  · simp only [eval_caseOpt, _root_.ReductionDsl.Expr.eval, _root_.ReductionDsl.Expr.v0, map_pure]
    set ρ₃ := _root_.ReductionDsl.Env.cons (t := (.prod (.opt (.base .sig)) (.base .k) : Ty Sev)) (σv, k) ρ₂p
    change (_root_.ReductionDsl.Comp.ret _).eval ρ₃ = _
    rw [eval_ret]
    set pAB := mkParties (T := T) (cka.initA kc) (cka.initB kc) σv
      (fs.initSender k) (fs.initReceiver k)
    have hMkP := mkPartiesE_eval (O' := OOev)
      (_root_.ReductionDsl.Expr.op (O := OOev) _root_.CryptoGames.CKA.CKAOp.ckaInitA .v2) (_root_.ReductionDsl.Expr.op (O := OOev) _root_.CryptoGames.CKA.CKAOp.ckaInitB .v2)
      (.fst .v0)
      (_root_.ReductionDsl.Expr.op (O := OOev) _root_.CryptoGames.CKA.CKAOp.fsInitSender (.snd .v0))
      (_root_.ReductionDsl.Expr.op (O := OOev) _root_.CryptoGames.CKA.CKAOp.fsInitReceiver (.snd .v0)) ρ₃
    have hMkP' :
        (mkPartiesE (O' := OOev)
          (_root_.ReductionDsl.Expr.op (O := OOev) _root_.CryptoGames.CKA.CKAOp.ckaInitA .v2)
          (_root_.ReductionDsl.Expr.op (O := OOev) _root_.CryptoGames.CKA.CKAOp.ckaInitB .v2)
          (.fst .v0)
          (_root_.ReductionDsl.Expr.op (O := OOev) _root_.CryptoGames.CKA.CKAOp.fsInitSender (.snd .v0))
          (_root_.ReductionDsl.Expr.op (O := OOev) _root_.CryptoGames.CKA.CKAOp.fsInitReceiver (.snd .v0))).eval ρ₃ =
          (prngVpEnc pAB.1, prngVpEnc pAB.2) := by
      rw [hMkP]
      simp [ρ₃, ρ₂p, ρ₂, ρ₁, hInitA, hInitB, hFsInitS, hFsInitR, pAB, Prod.map,
        _root_.ReductionDsl.Expr.eval, _root_.ReductionDsl.Expr.v0, _root_.ReductionDsl.Expr.v2]
    have hGs := cGsInitE_eval prngVpEnc (O' := OOev)
      (.fst (mkPartiesE
        (_root_.ReductionDsl.Expr.op (O := OOev) _root_.CryptoGames.CKA.CKAOp.ckaInitA .v2)
        (_root_.ReductionDsl.Expr.op (O := OOev) _root_.CryptoGames.CKA.CKAOp.ckaInitB .v2)
        (.fst .v0)
        (_root_.ReductionDsl.Expr.op (O := OOev) _root_.CryptoGames.CKA.CKAOp.fsInitSender (.snd .v0))
        (_root_.ReductionDsl.Expr.op (O := OOev) _root_.CryptoGames.CKA.CKAOp.fsInitReceiver (.snd .v0))))
      (.snd (mkPartiesE
        (_root_.ReductionDsl.Expr.op (O := OOev) _root_.CryptoGames.CKA.CKAOp.ckaInitA .v2)
        (_root_.ReductionDsl.Expr.op (O := OOev) _root_.CryptoGames.CKA.CKAOp.ckaInitB .v2)
        (.fst .v0)
        (_root_.ReductionDsl.Expr.op (O := OOev) _root_.CryptoGames.CKA.CKAOp.fsInitSender (.snd .v0))
        (_root_.ReductionDsl.Expr.op (O := OOev) _root_.CryptoGames.CKA.CKAOp.fsInitReceiver (.snd .v0))))
      .v3 ρ₃ pAB.1 pAB.2
      (by simp [_root_.ReductionDsl.Expr.eval, hMkP']) (by simp [_root_.ReductionDsl.Expr.eval, hMkP'])
    dsimp only [_root_.ReductionDsl.Expr.v0] at hGs
    simp only [esMk, pair_eval, hGs]
    rfl

private theorem simulateQ_liftM_unif_bucket {ι : Type} {tspec : OracleSpec.{0, 0} ι} {St α : Type}
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
  | query_bind t r ih =>
    rw [liftComp_bind, liftComp_liftM_query]
    have hq : (liftM (OracleSpec.query t) : TComp tspec _) =
        (liftM (OracleSpec.query (spec := unifSpec + tspec) (.inl t)) : TComp tspec _) := rfl
    have hrun :
        ((liftM ((QueryImpl.liftTarget (StateT St ProbComp)
          (QueryImpl.ofLift unifSpec ProbComp) + impl)
          (.inl t)) : StateT St ProbComp (unifSpec.Range t))).run st =
        ((liftM (OracleSpec.query t) : ProbComp _) >>= fun u => pure (u, st)) := rfl
    rw [hq, simulateQ_query_bind]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, StateT.run_bind]
    rw [hrun]
    simp only [bind_assoc, pure_bind, ih]

theorem simulateQ_sampleT_run_bucket {ι : Type} {tspec : OracleSpec.{0, 0} ι} {St α : Type}
    [SampleableType α] (impl : QueryImpl tspec (StateT St ProbComp)) (st : St) :
    (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl)
      (sampleT α)).run st =
    (($ᵗ α : ProbComp α) >>= fun a => pure (a, st)) := by
  unfold sampleT
  rw [simulateQ_liftM_unif_bucket]
  rfl

theorem rootPRNGBucketHybrid_zero_support_some
    [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR RSt I K) (Δbucket : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) (lam : I)
    (kr : KR) (b_prng : Bool)
    (step : Option (Option RSt × K))
    (h₀ : _root_.CryptoGames.SM.Construction.DeliverForge.PRNGBucketState T RSt K I)
    (sp : _root_.CryptoGames.PRFPRNG.GameState RSt I K)
    (hmem : ((step, h₀), sp) ∈ support
      ((simulateQ
        ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (_root_.CryptoGames.PRFPRNG.GameState RSt I K) ProbComp) + _root_.CryptoGames.PRFPRNG.oracleImpl prng)
        ((_root_.CryptoGames.SM.Construction.DeliverForge.rootPRNGBucketHybrid (T := T) prng Δbucket tL par t 0 false lam none).run {})).run
        { σ := prng.init kr, b := b_prng })) :
    ∃ σv k, step = some (σv, k) := by
  unfold _root_.CryptoGames.SM.Construction.DeliverForge.rootPRNGBucketHybrid _root_.CryptoGames.SM.Construction.DeliverForge.liftPBucket
    _root_.CryptoGames.SM.Construction.DeliverForge.lookupPRNGBucketF at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  have h0_lt : ¬(t < 0) := by omega
  have h0_pl : (false || ({} : _root_.CryptoGames.SM.Construction.DeliverForge.PRNGBucketState T RSt K I).corrRoot.isSome) = false := rfl
  simp only [h0_lt, h0_pl, Bool.false_eq_true, ↓reduceIte] at hmem
  by_cases hts : t = 0
  · subst hts
    have hnoTH : (tL.isSome && decide (0 = healEpoch tL)) = false := by
      cases tL <;> simp [healEpoch]
    simp only [↓reduceIte, hnoTH, Bool.false_eq_true] at hmem
    cases hIn : _root_.CryptoGames.SM.Construction.DeliverForge.inStage2BucketGen Δbucket tL par 0
    · simp only [hIn, Bool.false_eq_true, ↓reduceIte] at hmem
      simp [_root_.CryptoGames.PRFPRNG.processQuery, _root_.CryptoGames.PRFPRNG.corrQuery, _root_.CryptoGames.PRFPRNG.oracleImpl, _root_.CryptoGames.PRFPRNG.processImpl,
        _root_.CryptoGames.PRFPRNG.corrImpl, _root_.CryptoGames.PRFPRNG.samIfNec, StateT.run_bind, StateT.run_pure, StateT.run_lift,
        StateT.run_get, StateT.run_set, simulateQ_bind, simulateQ_query, simulateQ_pure,
        map_eq_bind_pure_comp, bind_assoc] at hmem
      rcases hmem with ⟨⟨rfl, _⟩, _⟩
      exact ⟨_, _, rfl⟩
    · simp only [hIn, ↓reduceIte] at hmem
      cases b_prng
      · simp [_root_.CryptoGames.PRFPRNG.challPrfQuery, _root_.CryptoGames.PRFPRNG.oracleImpl, _root_.CryptoGames.PRFPRNG.challPrfImpl,
          StateT.run_bind, StateT.run_pure, StateT.run_get, StateT.run_set, StateT.run_lift,
          simulateQ_bind, simulateQ_query, simulateQ_pure,
          map_eq_bind_pure_comp, bind_assoc] at hmem
        rcases hmem with ⟨⟨rfl, _⟩, _⟩
        exact ⟨_, _, rfl⟩
      · simp [_root_.CryptoGames.PRFPRNG.challPrfQuery, _root_.CryptoGames.PRFPRNG.oracleImpl, _root_.CryptoGames.PRFPRNG.challPrfImpl, List.lookup,
          StateT.run_bind, StateT.run_pure, StateT.run_get, StateT.run_set, StateT.run_lift,
          StateT.run_modify, StateT.run_monadLift, monadLift_self,
          simulateQ_bind, simulateQ_query, simulateQ_pure,
          map_eq_bind_pure_comp, bind_assoc] at hmem
        rcases hmem with ⟨R', ⟨rfl, _⟩, _⟩
        exact ⟨_, _, rfl⟩
  · have hts0 : ¬(0 = t) := Ne.symm hts
    simp only [hts0, ↓reduceIte] at hmem
    rcases tL with _ | l
    · have hnlt : ¬(0 < healEpoch none) := by simp [healEpoch]
      simp only [hnlt, Option.isSome_none, Bool.false_and,
        Bool.false_eq_true, ↓reduceIte] at hmem
      cases hIn : _root_.CryptoGames.SM.Construction.DeliverForge.inStage2BucketGen Δbucket none par 0
      · simp only [hIn, Bool.false_eq_true, ↓reduceIte] at hmem
        simp [_root_.CryptoGames.PRFPRNG.processQuery, _root_.CryptoGames.PRFPRNG.oracleImpl, _root_.CryptoGames.PRFPRNG.processImpl, _root_.CryptoGames.PRFPRNG.samIfNec,
          StateT.run_bind, StateT.run_pure, StateT.run_lift, StateT.run_get, StateT.run_set,
          simulateQ_bind, simulateQ_query, simulateQ_pure,
          map_eq_bind_pure_comp, bind_assoc] at hmem
        rcases hmem with ⟨⟨rfl, _⟩, _⟩
        exact ⟨_, _, rfl⟩
      · simp only [hIn, ↓reduceIte] at hmem
        simp [_root_.CryptoGames.PRFPRNG.processQuery, _root_.CryptoGames.PRFPRNG.oracleImpl, _root_.CryptoGames.PRFPRNG.processImpl, _root_.CryptoGames.PRFPRNG.samIfNec,
          List.lookup,
          StateT.run_bind, StateT.run_pure, StateT.run_lift, StateT.run_get, StateT.run_set,
          StateT.run_modify, simulateQ_bind, simulateQ_query, simulateQ_pure,
          map_eq_bind_pure_comp, bind_assoc] at hmem
        rcases hmem with ⟨kRand, ⟨rfl, _⟩, _⟩
        exact ⟨_, _, rfl⟩
    · have hlt : 0 < healEpoch (some l) := by simp [healEpoch]
      simp only [hlt] at hmem
      simp [_root_.CryptoGames.PRFPRNG.processQuery, _root_.CryptoGames.PRFPRNG.corrQuery, _root_.CryptoGames.PRFPRNG.oracleImpl, _root_.CryptoGames.PRFPRNG.processImpl,
        _root_.CryptoGames.PRFPRNG.corrImpl, _root_.CryptoGames.PRFPRNG.samIfNec, StateT.run_bind, StateT.run_pure, StateT.run_lift,
        StateT.run_get, StateT.run_set, simulateQ_bind, simulateQ_query, simulateQ_pure,
        map_eq_bind_pure_comp, bind_assoc] at hmem
      rcases hmem with ⟨⟨rfl, _⟩, _⟩
      exact ⟨_, _, rfl⟩

theorem initPRNGBucketRaw_inv [DecidableEq I] [SampleableType KC] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (Δbucket : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) (b : Bool)
    {L B qAdv : ℕ} (hqB : qAdv ≤ B) (hB1 : B + 1 ≤ L) (hBB : B * B ≤ L * L) :
    ∀ es₀ ∈ support (initPRNGBucketRaw cka prng fs lam Δbucket tL par t b),
      SMEngineInv L B qAdv es₀.g ∧ es₀.g.b = b ∧
        (∀ τ, (es₀.h.fTable τ).length + qAdv ≤ L) := by
  intro es₀ hmem
  unfold initPRNGBucketRaw at hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨kc, _, hmem⟩ := hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨⟨step, h₀⟩, hroot, hmem⟩ := hmem
  dsimp only at hmem
  have hLen := (rootPRNGBucketHybrid_fTable_len (T := T) prng Δbucket tL par t 0 false lam none {}
    (step, h₀) hroot).1
  rcases step with _ | ⟨σv, k⟩
  · simp only [support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    refine ⟨(_root_.CryptoGames.SM.Construction.SMEngineInv.aborted b hB1 hBB).mono hqB, rfl, fun τ => ?_⟩
    have h0 := hLen τ
    simp at h0
    dsimp only
    omega
  · simp only [support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    refine ⟨(_root_.CryptoGames.SM.Engine.SMEngineInv.init _ b hB1 hBB).mono hqB, rfl, fun τ => ?_⟩
    have h0 := hLen τ
    simp at h0
    dsimp only
    omega

theorem initPRNGBucketRaw_vrInv [DecidableEq I] [SampleableType KC] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (Δbucket : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) (b : Bool)
    {VROkStep : ℕ → RS → Prop} {B qAdv : ℕ}
    (hInitR : ∀ k, VROkStep (B - qAdv) (fs.initReceiver k)) :
    ∀ es₀ ∈ support (initPRNGBucketRaw cka prng fs lam Δbucket tL par t b),
      SMVRInv VROkStep B qAdv es₀.g := by
  intro es₀ hmem P τ v hv
  unfold initPRNGBucketRaw at hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨kc, _, hmem⟩ := hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨⟨step, h₀⟩, _, hmem⟩ := hmem
  rcases step with _ | ⟨σv, k⟩
  · simp only [support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    cases P <;> simp [abortedParties] at hv
  · simp only [support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    cases P <;> simp only [mkParties] at hv
    · split_ifs at hv with ht0
      · cases hv; exact hInitR _
    · cases hv

@[expose] def prngBucketHBoundedStep (L m : ℕ)
    (h : _root_.CryptoGames.SM.Construction.DeliverForge.PRNGBucketState T RSt K I) : Prop :=
  ∀ τ, (h.fTable τ).length + m ≤ L

theorem prngBucketHBoundedStep_mono {L m₁ m₂ : ℕ}
    {h : _root_.CryptoGames.SM.Construction.DeliverForge.PRNGBucketState T RSt K I}
    (hm : m₁ ≤ m₂) (hHB : prngBucketHBoundedStep L m₂ h) :
    prngBucketHBoundedStep L m₁ h :=
  fun τ => Nat.le_trans (Nat.add_le_add_left hm _) (hHB τ)


@[expose] def hooksPRNGBucketSplitGen [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δbucket qep : ℕ) (tL : Option ℕ) (par gMain : Bool) (t0 : ℕ) :
    Hooks (_root_.CryptoGames.PRFPRNG.spec RSt I K) (_root_.CryptoGames.SM.Construction.DeliverForge.PRNGBucketState T RSt K I)
      Γ T RSt SS RS M E CCoins Γ (Option RSt) SS RS :=
  if gMain then
    _root_.CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketMainGen cka prng fs Δbucket qep tL par t0
  else
    _root_.CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketForgedHdrGen cka prng fs Δbucket qep tL par t0

private theorem resolveCorrRootE_eval {Γ'}
    (hE : Expr OOev Γ' pbHsTyEv) (epE : Expr OOev Γ' .nat)
    (σvE : Expr OOev Γ' (.opt (.base .sig))) (ρ : Env Γ')
    (h : _root_.CryptoGames.SM.Construction.DeliverForge.PRNGBucketState T RSt K I)
    (hh : hE.eval ρ = prngBucketHsEnc h) :
    (resolveCorrRootE hE epE σvE).eval ρ =
      _root_.CryptoGames.SM.Construction.DeliverForge.resolveCorrRoot h (epE.eval ρ) (σvE.eval ρ) := by
  unfold resolveCorrRootE _root_.CryptoGames.SM.Construction.DeliverForge.resolveCorrRoot
  simp only [_root_.ReductionDsl.Expr.eval, hh, prngBucketHsEnc, prngBucketHsCorrRoot, _root_.ReductionDsl.Expr.v0]
  rcases σvE.eval ρ with _ | σ
  · rcases h.corrRoot with _ | ⟨eC, σC⟩
    · rfl
    · dsimp only [_root_.ReductionDsl.Env.get_cons_zero, _root_.ReductionDsl.Env.get_cons_succ]
      by_cases hEq : epE.eval ρ = eC <;> simp [hEq, _root_.ReductionDsl.Expr.eval, _root_.ReductionDsl.Expr.v1]
  · rfl

theorem isHonestHdrPRNGBucketE_eval [DecidableEq T]
    (heqT : eqT = (· == ·))
    {Γ'} (hE : Expr OOev Γ' pbHsTyEv) (hdrE : Expr OOev Γ' (.prod .nat (.opt (.base .t))))
    (ρ : Env Γ')
    (h : _root_.CryptoGames.SM.Construction.DeliverForge.PRNGBucketState T RSt K I) (hdr : Header T)
    (hh : hE.eval ρ = prngBucketHsEnc h) (hhdr : hdrE.eval ρ = hdr) :
    (isHonestHdrPRNGBucketE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) hE hdrE).eval ρ =
      _root_.CryptoGames.SM.Construction.DeliverForge.isHonestHdrPRNGBucket h hdr := by
  unfold isHonestHdrPRNGBucketE _root_.CryptoGames.SM.Construction.DeliverForge.isHonestHdrPRNGBucket
  simp only [_root_.ReductionDsl.Expr.eval, hh, prngBucketHsCache, prngBucketHsEnc, heqT,
    _root_.ReductionDsl.Expr.v0, _root_.ReductionDsl.Expr.v1, _root_.ReductionDsl.Env.get_cons_zero, _root_.ReductionDsl.Env.get_cons_succ, BEq.beq]
  rw [hhdr]
  rcases hdr with ⟨tHdr, _ | tn0⟩ <;> rcases h.cache tHdr with _ | ⟨Tc, σc, kVal⟩ <;> rfl

private theorem prngBucketStartRecvMainC_eval [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (hRecv : ckaReceive = cka.receive)
    (hFsInitR : fsInitReceiver = fs.initReceiver)
    (heqT : eqT = (· == ·))
    (Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    {Γ'} (hE : Expr OOev Γ' pbHsTyEv) (ctxE : Expr OOev Γ' (cGsTy pbVpTyEv))
    (pE : Expr OOev Γ' .bool) (tE : Expr OOev Γ' .nat)
    (γE : Expr OOev Γ' (.base .γ)) (σvE : Expr OOev Γ' (.opt (.base .sig)))
    (tnE : Expr OOev Γ' (.base .t)) (ρ : Env Γ')
    (h : _root_.CryptoGames.SM.Construction.DeliverForge.PRNGBucketState T RSt K I)
    (ctx : Ctx Γ T (Option RSt) SS RS M E) (P : Party)
    (hh : hE.eval ρ = prngBucketHsEnc h) :
    (prngBucketStartRecvMainC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) Δbucket qep tL par hE ctxE pE tE γE σvE tnE).eval ρ =
      Prod.map id prngBucketHsEnc <$>
        ((_root_.CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketMainGen cka prng fs Δbucket qep tL par t).startRecv ctx P
          (tE.eval ρ) (γE.eval ρ) (σvE.eval ρ) (tnE.eval ρ)).run h := by
  set t0 : ℕ := tE.eval ρ
  set γ0 : Γ := γE.eval ρ
  set tn0 : T := tnE.eval ρ
  unfold prngBucketStartRecvMainC _root_.CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketMainGen
  dsimp only
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [eval_bind_ret]
  have h0 : (_root_.ReductionDsl.Expr.pair hE (.pair tE (.pair γE tnE))).eval ρ =
      (prngBucketHsEnc h, t0, γ0, tn0) := by
    simp [_root_.ReductionDsl.Expr.eval, hh, t0, γ0, tn0]
  rw [h0]; clear h0
  set ρ₁ := _root_.ReductionDsl.Env.cons
    (t := (.prod pbHsTyEv (.prod .nat (.prod (.base .γ) (.base .t))) : Ty Sev))
    (prngBucketHsEnc h, t0, γ0, tn0) ρ
  rw [eval_caseOpt]
  have hHonest :
      (_root_.ReductionDsl.Expr.caseOpt (.tget (prngBucketHsCache (.fst (_root_.ReductionDsl.Expr.v0 (O := OOev)))) (.fst (.snd .v0))) .none
        (.ite (_root_.ReductionDsl.Expr.op (O := OOev) _root_.CryptoGames.CKA.CKAOp.eqT (.pair (.fst .v0) (.snd (.snd (.snd .v1)))))
          (.some (.snd .v0)) .none)).eval ρ₁ =
      (match h.cache t0 with
        | some (tCached, σc, kVal) => if tCached = tn0 then some (σc, kVal) else none
        | none => none) := by
    simp only [ρ₁, prngBucketHsCache, prngBucketHsEnc, heqT, _root_.ReductionDsl.Expr.eval,
      _root_.ReductionDsl.Expr.v0, _root_.ReductionDsl.Expr.v1, _root_.ReductionDsl.Env.get_cons_zero, _root_.ReductionDsl.Env.get_cons_succ, BEq.beq]
    rcases h.cache t0 with _ | ⟨tCached, σc, kVal⟩
    · rfl
    · by_cases hEq : tCached = tn0 <;> simp [hEq]
  rw [hHonest]; clear hHonest
  have hCond :
      (_root_.ReductionDsl.Expr.and
        (.and (.not (.lt (.nat (qep + 1)) (.fst (.snd (_root_.ReductionDsl.Expr.v0 (O := OOev))))))
          (validGuessBucketParPaperE Δbucket tL par (.fst (.snd .v0))))
        (.and (.bool tL.isSome) (.eqN (.fst (.snd .v0)) (.nat (healEpoch tL))))).eval ρ₁ =
      (!(decide (qep + 1 < t0)) && _root_.CryptoGames.SM.Construction.DeliverForge.inStage2BucketGen Δbucket tL par t0 &&
        (tL.isSome && decide (t0 = healEpoch tL))) := by
    simp [ρ₁, _root_.CryptoGames.SM.Construction.DeliverForge.inStage2BucketGen, validGuessBucketParPaperE_eval, _root_.ReductionDsl.Expr.eval, _root_.ReductionDsl.Expr.v0]
  set cnd : Bool := !(decide (qep + 1 < t0)) && _root_.CryptoGames.SM.Construction.DeliverForge.inStage2BucketGen Δbucket tL par t0 &&
    (tL.isSome && decide (t0 = healEpoch tL))
  rcases hCache : h.cache t0 with _ | ⟨tCached, σc, kVal⟩
  · dsimp only
    rw [eval_ite, hCond]
    cases cnd <;>
      simp [ρ₁, _root_.ReductionDsl.Expr.eval, _root_.ReductionDsl.Expr.v0, StateT.run_pure]
  · by_cases hEq : tCached = tn0
    · simp only [hEq, ↓reduceIte]
      set ρ₂ := _root_.ReductionDsl.Env.cons (t := (.prod (.opt (.base .sig)) (.base .k) : Ty Sev)) (σc, kVal) ρ₁
      have hResC :
          (resolveCorrRootE (O := OOev) (.fst .v1) (.fst (.snd .v1)) (.fst .v0)).eval ρ₂ =
          _root_.CryptoGames.SM.Construction.DeliverForge.resolveCorrRoot h t0 σc :=
        resolveCorrRootE_eval _ _ _ ρ₂ h rfl
      change (_root_.ReductionDsl.Comp.ret _).eval ρ₂ = _
      rw [eval_ret, pair_eval, some_eval, some_eval, pair_eval, pair_eval, hResC]
      simp [ρ₂, ρ₁, hRecv, hFsInitR, _root_.ReductionDsl.Expr.eval, _root_.ReductionDsl.Expr.v0, _root_.ReductionDsl.Expr.v1, StateT.run_pure]
    · simp only [hEq, ↓reduceIte]
      rw [eval_ite, hCond]
      cases cnd <;>
        simp [ρ₁, _root_.ReductionDsl.Expr.eval, _root_.ReductionDsl.Expr.v0, StateT.run_pure]

private theorem hooksPRNGBucketMainGen_startRecv_fTable_len [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (ctx : Ctx Γ T (Option RSt) SS RS M E) (P : Party)
    (t0 : ℕ) (γ0 : Γ) (σv0 : Option RSt) (tn0 : T)
    (h : _root_.CryptoGames.SM.Construction.DeliverForge.PRNGBucketState T RSt K I) :
    ∀ res ∈ support (((_root_.CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketMainGen cka prng fs Δbucket qep tL par t).startRecv
        ctx P t0 γ0 σv0 tn0).run h),
      ∀ τ, (res.2.fTable τ).length ≤ (h.fTable τ).length + 1 := by
  intro res hmem τ
  dsimp only [_root_.CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketMainGen] at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  rcases hCache : h.cache t0 with _ | ⟨tCached, σc, kVal⟩ <;> simp only [hCache] at hmem
  · split_ifs at hmem <;>
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact Nat.le_add_right _ _
  · by_cases hEq : tCached = tn0 <;> simp only [hEq, ↓reduceIte] at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact Nat.le_add_right _ _
    · split_ifs at hmem <;>
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; exact Nat.le_add_right _ _

private theorem hooksPRNGBucketMainGen_startRecv_rs [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    {VROk : RS → Prop} (hInitR : ∀ k, VROk (fs.initReceiver k))
    (ctx : Ctx Γ T (Option RSt) SS RS M E) (P : Party)
    (t0 : ℕ) (γ0 : Γ) (σv0 : Option RSt) (tn0 : T)
    (h : _root_.CryptoGames.SM.Construction.DeliverForge.PRNGBucketState T RSt K I) :
    ∀ res ∈ support (((_root_.CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketMainGen cka prng fs Δbucket qep tL par t).startRecv
        ctx P t0 γ0 σv0 tn0).run h),
      ∀ γ' σ' rs, res.1 = some (some (γ', σ', rs)) → VROk rs := by
  intro res hmem γ' σ' rs hst
  dsimp only [_root_.CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketMainGen] at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  rcases hCache : h.cache t0 with _ | ⟨tCached, σc, kVal⟩ <;> simp only [hCache] at hmem
  · split_ifs at hmem <;>
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; simp at hst
  · by_cases hEq : tCached = tn0 <;> simp only [hEq, ↓reduceIte] at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; cases hst; exact hInitR _
    · split_ifs at hmem <;>
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; simp at hst

private theorem prngBucketRevealForgedHdrC_eval [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    {Γ'} (hE : Expr OOev Γ' pbHsTyEv) (ctxE : Expr OOev Γ' (cGsTy pbVpTyEv))
    (pE : Expr OOev Γ' .bool) (vpE : Expr OOev Γ' pbVpTyEv) (ρ : Env Γ')
    (h : _root_.CryptoGames.SM.Construction.DeliverForge.PRNGBucketState T RSt K I)
    (ctx : Ctx Γ T (Option RSt) SS RS M E) (P : Party)
    (vp : VP Γ T (Option RSt) SS RS)
    (hh : hE.eval ρ = prngBucketHsEnc h)
    (hctx : ctxE.eval ρ = cGsEnc prngVpEnc ctx)
    (hvp : vpE.eval ρ = prngVpEnc vp) :
    (prngBucketRevealForgedHdrC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) tL hE ctxE pE vpE).eval ρ =
      Prod.map (Option.map ckaPsEnc) prngBucketHsEnc <$>
        ((_root_.CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketForgedHdrGen cka prng fs Δbucket qep tL par t).reveal
          ctx P vp).run h := by
  unfold prngBucketRevealForgedHdrC _root_.CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketForgedHdrGen
  dsimp only
  rw [eval_bind_ret]
  have h0 : (_root_.ReductionDsl.Expr.pair hE (.pair ctxE vpE)).eval ρ =
      (prngBucketHsEnc h, cGsEnc prngVpEnc ctx, prngVpEnc vp) := by
    simp [_root_.ReductionDsl.Expr.eval, hh, hctx, hvp]
  rw [h0]; clear h0
  set ρ₁ := _root_.ReductionDsl.Env.cons
    (t := (.prod pbHsTyEv (.prod (cGsTy pbVpTyEv) pbVpTyEv) : Ty Sev))
    (prngBucketHsEnc h, cGsEnc prngVpEnc ctx, prngVpEnc vp) ρ
  have hMax :
      (maxN (O' := OOev) (.fst (cGsEpoch (.fst (.snd .v0))))
        (.snd (cGsEpoch (.fst (.snd .v0))))).eval ρ₁ =
      max (ctx.epoch .A) (ctx.epoch .B) := by
    rw [Nat.max_def]
    simp only [ρ₁, maxN, leN, cGsEpoch, cGsEnc, _root_.ReductionDsl.Expr.eval, _root_.ReductionDsl.Expr.v0]
    by_cases hlt : ctx.epoch .B < ctx.epoch .A <;> simp [hlt]
  have hCond :
      (orE (O' := OOev) (.not (.lt (vpTcurNat (.snd (.snd .v0))) (.nat (healEpoch tL))))
        (.not (.lt (maxN (.fst (cGsEpoch (.fst (.snd .v0))))
          (.snd (cGsEpoch (.fst (.snd .v0))))) (.nat (healEpoch tL))))).eval ρ₁ =
      (!decide (vp.tcur < healEpoch tL) ||
        !decide (max (ctx.epoch .A) (ctx.epoch .B) < healEpoch tL)) := by
    have he : (vpTcurNat (O' := OOev) (.snd (.snd .v0))).eval ρ₁ = vp.tcur := rfl
    rw [orE_eval]
    simp [_root_.ReductionDsl.Expr.eval, he, hMax]
  rw [eval_ite, hCond]
  set badB : Bool := !decide (vp.tcur < healEpoch tL) ||
    !decide (max (ctx.epoch .A) (ctx.epoch .B) < healEpoch tL)
  change (if badB = true then _ else _) =
    Prod.map (Option.map ckaPsEnc) prngBucketHsEnc <$> StateT.run (if badB = true then _ else _) h
  cases badB
  · simp only [Bool.false_eq_true, ↓reduceIte, eval_caseOpt]
    have hRoot : (vpRoot (O' := OOev) (.snd (.snd .v0))).eval ρ₁ = vp.root := rfl
    rw [hRoot]
    rcases vp.root with _ | σ
    · simp [eval_ret, StateT.run_pure, ρ₁, _root_.ReductionDsl.Expr.eval, _root_.ReductionDsl.Expr.v0]
    · set ρ₂ := _root_.ReductionDsl.Env.cons (t := (.base .sig : Ty Sev)) σ ρ₁
      change (_root_.ReductionDsl.Comp.ret _).eval ρ₂ = _
      have hReal := realPartyE_eval (O' := OOev)
        (.snd (.snd .v1)) (vpΓ (.snd (.snd .v1))) .v0
        (vpVS (.snd (.snd .v1))) (vpVR (.snd (.snd .v1))) ρ₂ vp rfl
      have hΓ2 : (vpΓ (O' := OOev) (.snd (.snd .v1))).eval ρ₂ = vp.γ := rfl
      have hVS2 : (vpVS (O' := OOev) (.snd (.snd .v1))).eval ρ₂ = vp.vS := rfl
      have hVR2 : (vpVR (O' := OOev) (.snd (.snd .v1))).eval ρ₂ = vp.vR := rfl
      rw [eval_ret, pair_eval, some_eval, hReal, hΓ2, hVS2, hVR2]
      simp [StateT.run_pure, ρ₂, ρ₁, _root_.ReductionDsl.Expr.eval, _root_.ReductionDsl.Expr.v0, _root_.ReductionDsl.Expr.v1]
  · simp [eval_ret, StateT.run_pure, ρ₁, _root_.ReductionDsl.Expr.eval, _root_.ReductionDsl.Expr.v0]

theorem hooksPRNGBucketSplitPaperC_agrees_vr [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B Δbucket qep : ℕ) (tL : Option ℕ) (par gMain : Bool) (t0 : ℕ)
    {m : ℕ} {VROk : RS → Prop}
    (hSend : ckaSend = cka.send) (hRecv : ckaReceive = cka.receive)
    (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender) (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send) (hFsRecv : fsReceive = fs.receive)
    (heqT : eqT = (· == ·)) (heqI : eqI = (· == ·))
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
      (prngBucketHBoundedStep L (m + 1))
      (HBoundedPost := prngBucketHBoundedStep L m)
      (VROk := VROk)
      (hooksPRNGBucketSplitPaperC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δbucket qep tL par gMain t0)
      (hooksPRNGBucketSplitGen cka prng fs Δbucket qep tL par gMain t0) := by
  have hBase := hooksPRNGBucketParPaperC_agrees_vr
    (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (prngInit := prngInit)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampI := sampI)
    cka prng fs L B Δbucket qep tL par t0 (m := m) (VROk := VROk)
    hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend hFsRecv heqT heqI hSampCCoins hSampK
    hInitR hFsB
  cases gMain
  · refine
      { hBounded_post := hBase.hBounded_post
        startSend_eval := hBase.startSend_eval
        startSend_bounded := hBase.startSend_bounded
        startRecv_eval := hBase.startRecv_eval
        startRecv_bounded := hBase.startRecv_bounded
        startRecv_vrOk := hBase.startRecv_vrOk
        fsSend_eval := hBase.fsSend_eval
        fsRecv_eval := hBase.fsRecv_eval
        fsRecv_bounded := hBase.fsRecv_bounded
        commit_eval := hBase.commit_eval
        reveal_eval := fun hE ctxE pE vpE ρ h ctx P vp _ hh hctx _ hvp =>
          prngBucketRevealForgedHdrC_eval cka prng fs Δbucket qep tL par t0
            hE ctxE pE vpE ρ h ctx P vp hh hctx hvp }
  · refine
      { hBounded_post := hBase.hBounded_post
        startSend_eval := hBase.startSend_eval
        startSend_bounded := hBase.startSend_bounded
        startRecv_eval := fun hE ctxE pE tE γE σE tnE ρ h ctx P _ hh _ _ =>
          prngBucketStartRecvMainC_eval cka prng fs hRecv hFsInitR heqT
            Δbucket qep tL par t0 hE ctxE pE tE γE σE tnE ρ h ctx P hh
        startRecv_bounded := fun ctx P t1 γ1 σ1 tn1 h hHB res hmem τ => by
          have h1 := hooksPRNGBucketMainGen_startRecv_fTable_len cka prng fs
            Δbucket qep tL par t0 ctx P t1 γ1 σ1 tn1 h res hmem τ
          have h2 := hHB τ
          omega
        startRecv_vrOk := fun ctx P t1 γ1 σ1 tn1 h _ =>
          hooksPRNGBucketMainGen_startRecv_rs cka prng fs Δbucket qep tL par t0
            hInitR ctx P t1 γ1 σ1 tn1 h
        fsSend_eval := hBase.fsSend_eval
        fsRecv_eval := hBase.fsRecv_eval
        fsRecv_bounded := hBase.fsRecv_bounded
        commit_eval := hBase.commit_eval
        reveal_eval := hBase.reveal_eval }

theorem hooksPRNGBucketSplit_vrInv [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par gMain : Bool) (t0 : ℕ)
    {VROkStep : ℕ → RS → Prop}
    (hVRHk : HooksVRInv VROkStep (_root_.CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t0))
    (hInitR : ∀ k, VROkStep 0 (fs.initReceiver k)) :
    HooksVRInv VROkStep (hooksPRNGBucketSplitGen cka prng fs (3 + Δcka) qep tL par gMain t0) where
  mono := hVRHk.mono
  startRecv_step := by
    cases gMain
    · exact hVRHk.startRecv_step
    · intro ctx P t1 γ1 σ1 tn1 h res hmem
      exact hooksPRNGBucketMainGen_startRecv_rs cka prng fs (3 + Δcka) qep tL par t0
        hInitR ctx P t1 γ1 σ1 tn1 h res hmem
  fsRecv_step := by cases gMain <;> exact hVRHk.fsRecv_step
  commit_vR := by cases gMain <;> exact hVRHk.commit_vR

@[local simp]
private theorem run_commitE_prngBucketSplit
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δbucket qep : ℕ) (tL : Option ℕ) (par gMain : Bool) (t0 : ℕ)
    (s : Ctx Γ T (Option RSt) SS RS M E) (P : Party)
    (old new : VP Γ T (Option RSt) SS RS) (pos : _root_.CryptoGames.SM.Pos)
    (es : EState (VP Γ T (Option RSt) SS RS) M (Header T × E)
      (_root_.CryptoGames.SM.Construction.DeliverForge.PRNGBucketState T RSt K I)) :
    (commitE (hooksPRNGBucketSplitGen cka prng fs Δbucket qep tL par gMain t0)
      s P old new pos).run es =
      pure (some (s.accept P new pos), es) := by
  cases gMain <;>
    simp [hooksPRNGBucketSplitGen, commitE, _root_.CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketMainGen,
      _root_.CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketForgedHdrGen, _root_.CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketHybridGen]

private theorem vSend_prngBucketSplit_bounded [DecidableEq T] [DecidableEq I] [Inhabited E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B Δbucket qep : ℕ) (tL : Option ℕ) (par gMain : Bool) (t0 : ℕ)
    {HBounded HBoundedPost : _root_.CryptoGames.SM.Construction.DeliverForge.PRNGBucketState T RSt K I → Prop} {VROk : RS → Prop}
    (hHk : HooksCAgrees prngBucketHsEnc HBounded (HBoundedPost := HBoundedPost) (VROk := VROk)
      (hooksPRNGBucketSplitPaperC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δbucket qep tL par gMain t0)
      (hooksPRNGBucketSplitGen cka prng fs Δbucket qep tL par gMain t0))
    (ctx : Ctx Γ T (Option RSt) SS RS M E) (P : Party)
    (s : VP Γ T (Option RSt) SS RS) (msg : M) (pair : Option (M × M)) (r : Option CCoins)
    (h : _root_.CryptoGames.SM.Construction.DeliverForge.PRNGBucketState T RSt K I) (hHB : HBounded h) :
    ∀ res ∈ support
      ((vSend (hooksPRNGBucketSplitGen cka prng fs Δbucket qep tL par gMain t0)
        ctx P s msg pair r).run h),
      HBoundedPost res.2 := by
  intro res hmem
  rw [vSend_eq_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨s₁?, h₁⟩, hstep1, hmem⟩ := hmem
  have hHB₁ := vSendStep1_bounded prngBucketHsEnc HBounded _ _ hHk ctx P s r h hHB (s₁?, h₁) hstep1
  rcases s₁? with _ | s₁
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; exact hHB₁
  · cases hvs : s₁.vS with
    | none =>
      simp only [hvs, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact hHB₁
    | some v =>
      cases gMain <;>
      · simp only [hvs, hooksPRNGBucketSplitGen, _root_.CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketMainGen,
          _root_.CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketForgedHdrGen, _root_.CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketHybridGen,
          pure_bind] at hmem
        subst hmem; exact hHB₁

theorem implEDFPaperBucketRaw_split_bounded
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B Δ Δbucket qep maxSkip : ℕ) (tL : Option ℕ) (par gMain : Bool) (t0 : ℕ) (cfg : Config M)
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
    (q : (_root_.CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (es : EState (VP Γ T (Option RSt) SS RS) M (Header T × E)
      (_root_.CryptoGames.SM.Construction.DeliverForge.PRNGBucketState T RSt K I))
    (hHB : prngBucketHBoundedStep L (m + 1) es.h) :
    ∀ res ∈ support
      ((_root_.CryptoGames.SM.Construction.DeliverForge.implEDFPaperBucketRaw
          (hooksPRNGBucketSplitGen cka prng fs Δbucket qep tL par gMain t0)
          Δ qep maxSkip cfg (.inr q)).run es),
      prngBucketHBoundedStep L m res.2.h := by
  have hMono := prngBucketHBoundedStep_mono (Nat.le_succ m) hHB
  rcases q with ((((⟨P, msg, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩
  · intro res hmem
    change res ∈ support ((_root_.CryptoGames.SM.Construction.DeliverForge.transmitEBucket _ Δ qep (P, msg, r)).run es) at hmem
    unfold _root_.CryptoGames.SM.Construction.DeliverForge.transmitEBucket abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases hab : (es.abort || es.g.win)
    · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact hMono
    · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
      rcases hep : es.g.epMgmt Δ qep P r.isSome with _ | s₁
      · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; exact hMono
      · simp only [hep, run_liftH_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨vsRes, h₁⟩, hvs, hmem⟩ := hmem
        have hHB₁ := vSend_prngBucketSplit_bounded cka prng fs L B Δbucket qep tL par gMain t0 hHk
          s₁ P (s₁.st P) msg none r es.h hHB (vsRes, h₁) hvs
        rcases vsRes with _ | ⟨st', ct⟩ <;>
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff] at hmem
          subst hmem; exact hHB₁
  · intro res hmem
    change res ∈ support ((_root_.CryptoGames.SM.Construction.DeliverForge.challEBucket (P, m₀, m₁, r)).run es) at hmem
    simp only [_root_.CryptoGames.SM.Construction.DeliverForge.challEBucket, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; exact hMono
  · intro res hmem
    change res ∈ support ((deliverE _ maxSkip cfg (P, c)).run es) at hmem
    unfold deliverE abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases hab : (es.abort || es.g.win)
    · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact hMono
    · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
      rcases hin : es.g.inTransit P.other c with _ | r
      · simp only [hin, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; exact hMono
      · simp only [hin, run_liftH_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨vrRes, h₁⟩, hvr, hmem⟩ := hmem
        have hHB₁ := vRecv_bounded prngBucketHsEnc (prngBucketHBoundedStep L (m + 1)) _ _ hHk
          es.g P (es.g.st P) c (some r) es.h hHB (vrRes, h₁) hvr
        rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff] at hmem
          subst hmem; exact hHB₁
        · dsimp only at hmem
          split_ifs at hmem <;>
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff] at hmem
            subst hmem; exact hHB₁
        · dsimp only at hmem
          simp only [StateT.run_bind, run_commitE_prngBucketSplit, StateT.run_modify,
            StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hmem
          subst hmem; exact hHB₁
  · intro res hmem
    change res ∈ support ((injectE _ Δ qep cfg (P, c)).run es) at hmem
    unfold injectE abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases hab : (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj Δ))
    · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact hMono
    · simp only [hab, Bool.false_eq_true, ↓reduceIte, run_liftH_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨vrRes, h₁⟩, hvr, hmem⟩ := hmem
      have hHB₁ := vRecv_bounded prngBucketHsEnc (prngBucketHBoundedStep L (m + 1)) _ _ hHk
        es.g P (es.g.st P) c none es.h hHB (vrRes, h₁) hvr
      rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; exact hHB₁
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; exact hHB₁
      · dsimp only at hmem
        by_cases hqep : qep + 1 < t'
        · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
          subst hmem; exact hHB₁
        · simp only [hqep, ↓reduceIte] at hmem
          by_cases htriv : es.g.trivial Δ ⟨P.other, t', i'⟩ = true
          · simp only [htriv, ↓reduceIte, StateT.run_bind, run_commitE_prngBucketSplit,
              StateT.run_modify, StateT.run_pure, pure_bind, support_pure,
              Set.mem_singleton_iff] at hmem
            subst hmem; exact hHB₁
          · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem
            by_cases hfull : cfg.injectFull t' = true
            · simp only [hfull, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
                pure_bind, support_pure, Set.mem_singleton_iff] at hmem
              subst hmem; exact hHB₁
            · simp only [hfull, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
                support_pure, Set.mem_singleton_iff] at hmem
              subst hmem; exact hHB₁
  · intro res hmem
    change res ∈ support ((_root_.CryptoGames.SM.Construction.DeliverForge.corrEPaperBucket _ P).run es) at hmem
    unfold _root_.CryptoGames.SM.Construction.DeliverForge.corrEPaperBucket abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases href : (es.abort || es.g.win || !(es.g.corrAllowedPaper P))
    · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact hMono
    · simp only [href, Bool.false_eq_true, ↓reduceIte, run_liftH_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨⟨revRes, h₁⟩, hrev, hmem⟩ := hmem
      have hf₁ : h₁.fTable = es.h.fTable := by
        cases gMain
        · simp only [hooksPRNGBucketSplitGen, Bool.false_eq_true, ↓reduceIte] at hrev
          dsimp only [_root_.CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketForgedHdrGen] at hrev
          by_cases hBad : (!decide ((es.g.st P).tcur < healEpoch tL) ||
              !decide (max (es.g.epoch .A) (es.g.epoch .B) < healEpoch tL)) = true
          · simp only [hBad, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hrev
            cases hrev; rfl
          · simp only [hBad, Bool.false_eq_true, ↓reduceIte] at hrev
            rcases hrt : (es.g.st P).root with _ | σ <;>
              simp only [hrt, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hrev <;>
              cases hrev <;> rfl
        · simp only [hooksPRNGBucketSplitGen, ↓reduceIte] at hrev
          dsimp only [_root_.CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketMainGen, _root_.CryptoGames.SM.Construction.DeliverForge.hooksPRNGBucketHybridGen] at hrev
          simp only [StateT.run_bind, StateT.run_get, pure_bind] at hrev
          rcases hR : _root_.CryptoGames.SM.Construction.DeliverForge.resolveCorrRoot es.h (es.g.st P).tcur (es.g.st P).root with _ | σ <;>
            simp only [hR] at hrev
          · by_cases hcond : (!_root_.CryptoGames.SM.Construction.DeliverForge.postLeak tL es.g && es.h.corrRoot.isNone &&
                !decide ((es.g.st P).tcur < healEpoch tL) &&
                ((es.g.st P).tcur == max (es.g.epoch .A) (es.g.epoch .B))) = true
            · simp only [hcond, ↓reduceIte, StateT.run_bind, _root_.CryptoGames.SM.Construction.DeliverForge.liftPBucket, StateT.run_lift,
                bind_assoc, pure_bind, mem_support_bind_iff] at hrev
              obtain ⟨σ?, _, hrev⟩ := hrev
              rcases σ? with _ | σOut
              · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hrev
                cases hrev; rfl
              · by_cases hlc : es.h.lc.isNone = true <;>
                  simp only [hlc, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
                    StateT.run_modify, StateT.run_pure, pure_bind, support_pure,
                    Set.mem_singleton_iff] at hrev <;>
                  cases hrev <;> rfl
            · simp only [hcond, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, support_pure,
                Set.mem_singleton_iff] at hrev
              cases hrev; rfl
          · by_cases hc1 : (!decide ((es.g.st P).tcur < healEpoch tL) && es.h.corrRoot.isNone) = true <;>
              by_cases hc2 : (!_root_.CryptoGames.SM.Construction.DeliverForge.postLeak tL es.g && es.h.lc.isNone &&
                  !decide ((es.g.st P).tcur < healEpoch tL)) = true <;>
              simp only [hc1, hc2, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
                StateT.run_modify, StateT.run_pure, pure_bind, support_pure,
                Set.mem_singleton_iff] at hrev <;>
              cases hrev <;> rfl
      have hMono1 : prngBucketHBoundedStep L m h₁ := fun τ => by
        simpa only [prngBucketHBoundedStep, hf₁] using hMono τ
      rcases revRes with _ | stOut <;>
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; exact hMono1
  · intro res hmem
    change res ∈ support ((_root_.CryptoGames.SM.Construction.DeliverForge.deliverForgeE _ Δ qep cfg (P, c, c')).run es) at hmem
    unfold _root_.CryptoGames.SM.Construction.DeliverForge.deliverForgeE abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases hab : (es.abort || es.g.win)
    · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact hMono
    · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
      rcases hin : es.g.inTransit P.other c with _ | r
      · simp only [hin, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; exact hMono
      · simp only [hin] at hmem
        by_cases hskip :
            ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos || c.1 != c'.1)
        · simp only [hskip, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
          subst hmem; exact hMono
        · simp only [hskip, Bool.false_eq_true, ↓reduceIte, run_liftH_bind,
            mem_support_bind_iff] at hmem
          obtain ⟨⟨vrRes, h₁⟩, hvr, hmem⟩ := hmem
          have hHB₁ := vRecv_bounded prngBucketHsEnc (prngBucketHBoundedStep L (m + 1)) _ _ hHk
            es.g P (es.g.st P) c' none es.h hHB (vrRes, h₁) hvr
          rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff] at hmem
            subst hmem; exact hHB₁
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
            subst hmem; exact hHB₁
          · dsimp only at hmem
            by_cases hbad_ep : (decide (qep + 1 < t') || (t' != r.pos.epoch)) = true
            · simp only [hbad_ep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
              subst hmem; exact hHB₁
            · simp only [hbad_ep, Bool.false_eq_true, ↓reduceIte] at hmem
              by_cases htriv : es.g.trivial Δ ⟨P.other, t', i'⟩ = true
              · simp only [htriv, ↓reduceIte, StateT.run_bind, run_commitE_prngBucketSplit,
                  StateT.run_modify, StateT.run_pure, pure_bind, support_pure,
                  Set.mem_singleton_iff] at hmem
                subst hmem; exact hHB₁
              · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem
                by_cases hfull : cfg.injectFull t' = true
                · simp only [hfull, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
                    pure_bind, support_pure, Set.mem_singleton_iff] at hmem
                  subst hmem; exact hHB₁
                · simp only [hfull, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
                    support_pure, Set.mem_singleton_iff] at hmem
                  subst hmem; exact hHB₁

end HooksPRNGBucketEval

end

end Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGSplitEvalHooks
