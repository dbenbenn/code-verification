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
import Computational.Proofs.ReductionDsl.Notation

set_option autoImplicit false
set_option linter.unusedSectionVars false

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

private def initPRNGBucketRaw [DecidableEq I] [SampleableType KC] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (Δbucket : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) (b : Bool) :
    PRFPRNG.AdversaryComp RSt I K
      (EState (VP Γ T (Option RSt) SS RS) M (Header T × E)
        (DeliverForge.PRNGBucketState T RSt K I)) := do
  let kc ← sampleT KC
  let (step, h₀) ← (DeliverForge.rootPRNGBucketHybrid prng Δbucket tL par t 0 false lam none).run {}
  match step with
  | none =>
    let (vA, vB) := abortedParties (T := T) (RSt := RSt) (SS := SS) (RS := RS)
      (cka.initA kc) (cka.initB kc)
    pure { g := { st := fun | .A => vA | .B => vB, b := b }, h := h₀, abort := true }
  | some (σv, k) =>
    let (vA, vB) := mkParties (T := T) (cka.initA kc) (cka.initB kc) σv
      (fs.initSender k) (fs.initReceiver k)
    pure { g := { st := fun | .A => vA | .B => vB, b := b }, h := h₀, abort := false }

private theorem initPRNGBucketHybridEStateC_eval [DecidableEq I] [SampleableType KC] [SampleableType K]
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
  set ρ₁ := Env.cons (t := (.bool : Ty Sev)) b ρ
  rw [eval_bind, map_bind]
  have hKC : (@Comp.sample _ _ _ OOev IIev _ CKASamp.kc .unit).eval ρ₁ = sampleT KC := by
    simp only [Comp.eval, prngIface, prngSamplers, ckaSamplers, hSampKC, sampleT]
    exact liftP_eq_liftM IIev (fun _ => rfl) ($ᵗ KC)
  rw [hKC]
  refine bind_congr fun kc => ?_
  set ρ₂ := Env.cons (t := (.base .kc : Ty Sev)) kc ρ₁
  rw [eval_bind, map_bind]
  have ⟨hRoot, _⟩ := rootPRNGBucketHybridC_eval
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)
    prng hPrngUp heqI hSampK L Δbucket tL par t
    prngBucketHsEmptyE (.nat 0) (.bool false) (Expr.op (O := OOev) CKAOp.lamI .unit) .none ρ₂
    ({} : DeliverForge.PRNGBucketState T RSt K I) rfl (Nat.zero_le L)
  simp only [Expr.eval] at hRoot
  rw [hRoot, bind_map_left]
  refine bind_congr fun ⟨step, h₀⟩ => ?_
  dsimp only [Prod.map, id_eq]
  set ρ₂p := Env.cons
    (t := (.prod (.opt (.prod (.opt (.base .sig)) (.base .k))) pbHsTyEv : Ty Sev))
    (step, prngBucketHsEnc h₀) ρ₂
  rcases step with _ | ⟨σv, k⟩
  · simp only [eval_caseOpt, Expr.eval, Expr.v0, map_pure]
    change (Comp.ret _).eval ρ₂p = _
    rw [eval_ret]
    set pAB := abortedParties (T := T) (RSt := RSt) (SS := SS) (RS := RS)
      (cka.initA kc) (cka.initB kc)
    have hAbP := abortedPartiesE_eval
      (Expr.op (O := OOev) CKAOp.ckaInitA .v1) (Expr.op (O := OOev) CKAOp.ckaInitB .v1) ρ₂p
    have hAbP' :
        (abortedPartiesE
          (Expr.op (O := OOev) CKAOp.ckaInitA .v1)
          (Expr.op (O := OOev) CKAOp.ckaInitB .v1)).eval ρ₂p =
          (prngVpEnc pAB.1, prngVpEnc pAB.2) := by
      rw [hAbP]
      simp [ρ₂p, ρ₂, ρ₁, hInitA, hInitB, pAB, Prod.map, Expr.eval, Expr.v1]
    have hGs := cGsInitE_eval prngVpEnc (O' := OOev)
      (.fst (abortedPartiesE
        (Expr.op (O := OOev) CKAOp.ckaInitA .v1) (Expr.op (O := OOev) CKAOp.ckaInitB .v1)))
      (.snd (abortedPartiesE
        (Expr.op (O := OOev) CKAOp.ckaInitA .v1) (Expr.op (O := OOev) CKAOp.ckaInitB .v1)))
      .v2 ρ₂p pAB.1 pAB.2
      (by simp [Expr.eval, hAbP']) (by simp [Expr.eval, hAbP'])
    simp only [esMk, pair_eval, hGs]
    rfl
  · simp only [eval_caseOpt, Expr.eval, Expr.v0, map_pure]
    set ρ₃ := Env.cons (t := (.prod (.opt (.base .sig)) (.base .k) : Ty Sev)) (σv, k) ρ₂p
    change (Comp.ret _).eval ρ₃ = _
    rw [eval_ret]
    set pAB := mkParties (T := T) (cka.initA kc) (cka.initB kc) σv
      (fs.initSender k) (fs.initReceiver k)
    have hMkP := mkPartiesE_eval (O' := OOev)
      (Expr.op (O := OOev) CKAOp.ckaInitA .v2) (Expr.op (O := OOev) CKAOp.ckaInitB .v2)
      (.fst .v0)
      (Expr.op (O := OOev) CKAOp.fsInitSender (.snd .v0))
      (Expr.op (O := OOev) CKAOp.fsInitReceiver (.snd .v0)) ρ₃
    have hMkP' :
        (mkPartiesE (O' := OOev)
          (Expr.op (O := OOev) CKAOp.ckaInitA .v2)
          (Expr.op (O := OOev) CKAOp.ckaInitB .v2)
          (.fst .v0)
          (Expr.op (O := OOev) CKAOp.fsInitSender (.snd .v0))
          (Expr.op (O := OOev) CKAOp.fsInitReceiver (.snd .v0))).eval ρ₃ =
          (prngVpEnc pAB.1, prngVpEnc pAB.2) := by
      rw [hMkP]
      simp [ρ₃, ρ₂p, ρ₂, ρ₁, hInitA, hInitB, hFsInitS, hFsInitR, pAB, Prod.map,
        Expr.eval, Expr.v0, Expr.v2]
    have hGs := cGsInitE_eval prngVpEnc (O' := OOev)
      (.fst (mkPartiesE
        (Expr.op (O := OOev) CKAOp.ckaInitA .v2)
        (Expr.op (O := OOev) CKAOp.ckaInitB .v2)
        (.fst .v0)
        (Expr.op (O := OOev) CKAOp.fsInitSender (.snd .v0))
        (Expr.op (O := OOev) CKAOp.fsInitReceiver (.snd .v0))))
      (.snd (mkPartiesE
        (Expr.op (O := OOev) CKAOp.ckaInitA .v2)
        (Expr.op (O := OOev) CKAOp.ckaInitB .v2)
        (.fst .v0)
        (Expr.op (O := OOev) CKAOp.fsInitSender (.snd .v0))
        (Expr.op (O := OOev) CKAOp.fsInitReceiver (.snd .v0))))
      .v3 ρ₃ pAB.1 pAB.2
      (by simp [Expr.eval, hMkP']) (by simp [Expr.eval, hMkP'])
    dsimp only [Expr.v0] at hGs
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

private theorem simulateQ_sampleT_run_bucket {ι : Type} {tspec : OracleSpec.{0, 0} ι} {St α : Type}
    [SampleableType α] (impl : QueryImpl tspec (StateT St ProbComp)) (st : St) :
    (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl)
      (sampleT α)).run st =
    (($ᵗ α : ProbComp α) >>= fun a => pure (a, st)) := by
  unfold sampleT
  rw [simulateQ_liftM_unif_bucket]
  rfl

private theorem rootPRNGBucketHybrid_zero_support_some
    [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR RSt I K) (Δbucket : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) (lam : I)
    (kr : KR) (b_prng : Bool)
    (step : Option (Option RSt × K))
    (h₀ : DeliverForge.PRNGBucketState T RSt K I)
    (sp : PRFPRNG.GameState RSt I K)
    (hmem : ((step, h₀), sp) ∈ support
      ((simulateQ
        ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (PRFPRNG.GameState RSt I K) ProbComp) + PRFPRNG.oracleImpl prng)
        ((DeliverForge.rootPRNGBucketHybrid (T := T) prng Δbucket tL par t 0 false lam none).run {})).run
        { σ := prng.init kr, b := b_prng })) :
    ∃ σv k, step = some (σv, k) := by
  unfold DeliverForge.rootPRNGBucketHybrid DeliverForge.liftPBucket
    DeliverForge.lookupPRNGBucketF at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  have h0_lt : ¬(t < 0) := by omega
  have h0_pl : (false || ({} : DeliverForge.PRNGBucketState T RSt K I).corrRoot.isSome) = false := rfl
  simp only [h0_lt, h0_pl, Bool.false_eq_true, ↓reduceIte] at hmem
  by_cases hts : t = 0
  · subst hts
    have hnoTH : (tL.isSome && decide (0 = healEpoch tL)) = false := by
      cases tL <;> simp [healEpoch]
    simp only [↓reduceIte, hnoTH, Bool.false_eq_true] at hmem
    cases hIn : DeliverForge.inStage2BucketGen Δbucket tL par 0
    · simp only [hIn, Bool.false_eq_true, ↓reduceIte] at hmem
      simp [PRFPRNG.processQuery, PRFPRNG.corrQuery, PRFPRNG.oracleImpl, PRFPRNG.processImpl,
        PRFPRNG.corrImpl, PRFPRNG.samIfNec, StateT.run_bind, StateT.run_pure, StateT.run_lift,
        StateT.run_get, StateT.run_set, simulateQ_bind, simulateQ_query, simulateQ_pure,
        map_eq_bind_pure_comp, bind_assoc] at hmem
      rcases hmem with ⟨⟨rfl, _⟩, _⟩
      exact ⟨_, _, rfl⟩
    · simp only [hIn, ↓reduceIte] at hmem
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
  · have hts0 : ¬(0 = t) := Ne.symm hts
    simp only [hts0, ↓reduceIte] at hmem
    rcases tL with _ | l
    · have hnlt : ¬(0 < healEpoch none) := by simp [healEpoch]
      simp only [hnlt, Option.isSome_none, Bool.false_and,
        Bool.false_eq_true, ↓reduceIte] at hmem
      cases hIn : DeliverForge.inStage2BucketGen Δbucket none par 0
      · simp only [hIn, Bool.false_eq_true, ↓reduceIte] at hmem
        simp [PRFPRNG.processQuery, PRFPRNG.oracleImpl, PRFPRNG.processImpl, PRFPRNG.samIfNec,
          StateT.run_bind, StateT.run_pure, StateT.run_lift, StateT.run_get, StateT.run_set,
          simulateQ_bind, simulateQ_query, simulateQ_pure,
          map_eq_bind_pure_comp, bind_assoc] at hmem
        rcases hmem with ⟨⟨rfl, _⟩, _⟩
        exact ⟨_, _, rfl⟩
      · simp only [hIn, ↓reduceIte] at hmem
        simp [PRFPRNG.processQuery, PRFPRNG.oracleImpl, PRFPRNG.processImpl, PRFPRNG.samIfNec,
          List.lookup,
          StateT.run_bind, StateT.run_pure, StateT.run_lift, StateT.run_get, StateT.run_set,
          StateT.run_modify, simulateQ_bind, simulateQ_query, simulateQ_pure,
          map_eq_bind_pure_comp, bind_assoc] at hmem
        rcases hmem with ⟨kRand, ⟨rfl, _⟩, _⟩
        exact ⟨_, _, rfl⟩
    · have hlt : 0 < healEpoch (some l) := by simp [healEpoch]
      simp only [hlt] at hmem
      simp [PRFPRNG.processQuery, PRFPRNG.corrQuery, PRFPRNG.oracleImpl, PRFPRNG.processImpl,
        PRFPRNG.corrImpl, PRFPRNG.samIfNec, StateT.run_bind, StateT.run_pure, StateT.run_lift,
        StateT.run_get, StateT.run_set, simulateQ_bind, simulateQ_query, simulateQ_pure,
        map_eq_bind_pure_comp, bind_assoc] at hmem
      rcases hmem with ⟨⟨rfl, _⟩, _⟩
      exact ⟨_, _, rfl⟩

private theorem initPRNGBucketRaw_inv [DecidableEq I] [SampleableType KC] [SampleableType K]
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
    refine ⟨(SMEngineInv.aborted b hB1 hBB).mono hqB, rfl, fun τ => ?_⟩
    have h0 := hLen τ
    simp at h0
    dsimp only
    omega
  · simp only [support_pure, Set.mem_singleton_iff] at hmem
    subst hmem
    refine ⟨(SMEngineInv.init _ b hB1 hBB).mono hqB, rfl, fun τ => ?_⟩
    have h0 := hLen τ
    simp at h0
    dsimp only
    omega

private theorem initPRNGBucketRaw_vrInv [DecidableEq I] [SampleableType KC] [SampleableType K]
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

private def prngBucketHBoundedStep (L m : ℕ)
    (h : DeliverForge.PRNGBucketState T RSt K I) : Prop :=
  ∀ τ, (h.fTable τ).length + m ≤ L

private theorem prngBucketHBoundedStep_mono {L m₁ m₂ : ℕ}
    {h : DeliverForge.PRNGBucketState T RSt K I}
    (hm : m₁ ≤ m₂) (hHB : prngBucketHBoundedStep L m₂ h) :
    prngBucketHBoundedStep L m₁ h :=
  fun τ => Nat.le_trans (Nat.add_le_add_left hm _) (hHB τ)

private theorem vSend_prngBucket_bounded [DecidableEq T] [DecidableEq I] [Inhabited E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    {HBounded HBoundedPost : DeliverForge.PRNGBucketState T RSt K I → Prop} {VROk : RS → Prop}
    (hHk : HooksCAgrees prngBucketHsEnc HBounded (HBoundedPost := HBoundedPost) (VROk := VROk)
      (hooksPRNGBucketParPaperC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δbucket qep tL par t)
      (DeliverForge.hooksPRNGBucketHybridGen cka prng fs Δbucket qep tL par t))
    (ctx : Ctx Γ T (Option RSt) SS RS M E) (P : Party)
    (s : VP Γ T (Option RSt) SS RS) (msg : M) (pair : Option (M × M)) (r : Option CCoins)
    (h : DeliverForge.PRNGBucketState T RSt K I) (hHB : HBounded h) :
    ∀ res ∈ support
      ((vSend (DeliverForge.hooksPRNGBucketHybridGen cka prng fs Δbucket qep tL par t)
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
      simp only [hvs, DeliverForge.hooksPRNGBucketHybridGen, StateT.run_pure,
        pure_bind, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact hHB₁

@[local simp]
private theorem run_commitE_prngBucketGen
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (s : Ctx Γ T (Option RSt) SS RS M E) (P : Party)
    (old new : VP Γ T (Option RSt) SS RS) (pos : SM.Pos)
    (es : EState (VP Γ T (Option RSt) SS RS) M (Header T × E)
      (DeliverForge.PRNGBucketState T RSt K I)) :
    (commitE (DeliverForge.hooksPRNGBucketHybridGen cka prng fs Δbucket qep tL par t)
      s P old new pos).run es =
      pure (some (s.accept P new pos), es) := by
  simp [commitE, DeliverForge.hooksPRNGBucketHybridGen]

private theorem deliverE_prngBucket_bounded
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B Δbucket qep maxSkip : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) (cfg : Config M)
    {m : ℕ} {VROk : RS → Prop}
    (hHk : HooksCAgrees prngBucketHsEnc (prngBucketHBoundedStep L (m + 1))
      (HBoundedPost := prngBucketHBoundedStep L m) (VROk := VROk)
      (hooksPRNGBucketParPaperC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δbucket qep tL par t)
      (DeliverForge.hooksPRNGBucketHybridGen cka prng fs Δbucket qep tL par t))
    (es : EState (VP Γ T (Option RSt) SS RS) M (Header T × E)
      (DeliverForge.PRNGBucketState T RSt K I))
    (arg : Party × (Header T × E))
    (hHB : prngBucketHBoundedStep L (m + 1) es.h) :
    ∀ res ∈ support
      ((deliverE (DeliverForge.hooksPRNGBucketHybridGen cka prng fs Δbucket qep tL par t)
        maxSkip cfg arg).run es),
      prngBucketHBoundedStep L m res.2.h := by
  rcases arg with ⟨P, c⟩
  intro res hmem
  have hMono := prngBucketHBoundedStep_mono (Nat.le_succ m) hHB
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
        simp only [StateT.run_bind, run_commitE_prngBucketGen, StateT.run_modify,
          StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; exact hHB₁

private theorem injectE_prngBucket_bounded
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B Δ Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) (cfg : Config M)
    {m : ℕ} {VROk : RS → Prop}
    (hHk : HooksCAgrees prngBucketHsEnc (prngBucketHBoundedStep L (m + 1))
      (HBoundedPost := prngBucketHBoundedStep L m) (VROk := VROk)
      (hooksPRNGBucketParPaperC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δbucket qep tL par t)
      (DeliverForge.hooksPRNGBucketHybridGen cka prng fs Δbucket qep tL par t))
    (es : EState (VP Γ T (Option RSt) SS RS) M (Header T × E)
      (DeliverForge.PRNGBucketState T RSt K I))
    (arg : Party × (Header T × E))
    (hHB : prngBucketHBoundedStep L (m + 1) es.h) :
    ∀ res ∈ support
      ((injectE (DeliverForge.hooksPRNGBucketHybridGen cka prng fs Δbucket qep tL par t)
        Δ qep cfg arg).run es),
      prngBucketHBoundedStep L m res.2.h := by
  rcases arg with ⟨P, c⟩
  intro res hmem
  have hMono := prngBucketHBoundedStep_mono (Nat.le_succ m) hHB
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
        · simp only [htriv, ↓reduceIte, StateT.run_bind, run_commitE_prngBucketGen,
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

private theorem deliverForgeE_prngBucket_bounded
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B Δ Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) (cfg : Config M)
    {m : ℕ} {VROk : RS → Prop}
    (hHk : HooksCAgrees prngBucketHsEnc (prngBucketHBoundedStep L (m + 1))
      (HBoundedPost := prngBucketHBoundedStep L m) (VROk := VROk)
      (hooksPRNGBucketParPaperC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δbucket qep tL par t)
      (DeliverForge.hooksPRNGBucketHybridGen cka prng fs Δbucket qep tL par t))
    (es : EState (VP Γ T (Option RSt) SS RS) M (Header T × E)
      (DeliverForge.PRNGBucketState T RSt K I))
    (arg : Party × (Header T × E) × (Header T × E))
    (hHB : prngBucketHBoundedStep L (m + 1) es.h) :
    ∀ res ∈ support
      ((DeliverForge.deliverForgeE
        (DeliverForge.hooksPRNGBucketHybridGen cka prng fs Δbucket qep tL par t)
        Δ qep cfg arg).run es),
      prngBucketHBoundedStep L m res.2.h := by
  rcases arg with ⟨P, c, c'⟩
  intro res hmem
  have hMono := prngBucketHBoundedStep_mono (Nat.le_succ m) hHB
  unfold DeliverForge.deliverForgeE abortE at hmem
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
            · simp only [htriv, ↓reduceIte, StateT.run_bind, run_commitE_prngBucketGen,
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

private theorem transmitEBucket_prngBucket_bounded
    [DecidableEq T] [DecidableEq I] [Inhabited E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B Δ Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    {m : ℕ} {VROk : RS → Prop}
    (hHk : HooksCAgrees prngBucketHsEnc (prngBucketHBoundedStep L (m + 1))
      (HBoundedPost := prngBucketHBoundedStep L m) (VROk := VROk)
      (hooksPRNGBucketParPaperC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δbucket qep tL par t)
      (DeliverForge.hooksPRNGBucketHybridGen cka prng fs Δbucket qep tL par t))
    (es : EState (VP Γ T (Option RSt) SS RS) M (Header T × E)
      (DeliverForge.PRNGBucketState T RSt K I))
    (arg : Party × M × Option CCoins)
    (hHB : prngBucketHBoundedStep L (m + 1) es.h) :
    ∀ res ∈ support
      ((DeliverForge.transmitEBucket
        (DeliverForge.hooksPRNGBucketHybridGen cka prng fs Δbucket qep tL par t)
        Δ qep arg).run es),
      prngBucketHBoundedStep L m res.2.h := by
  rcases arg with ⟨P, msg, r⟩
  intro res hmem
  have hMono := prngBucketHBoundedStep_mono (Nat.le_succ m) hHB
  unfold DeliverForge.transmitEBucket abortE at hmem
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
      have hHB₁ := vSend_prngBucket_bounded cka prng fs L B Δbucket qep tL par t hHk
        s₁ P (s₁.st P) msg none r es.h hHB (vsRes, h₁) hvs
      rcases vsRes with _ | ⟨st', ct⟩ <;>
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; exact hHB₁

private theorem implEDFBucketRawChoice_prngBucket_bounded (paper : Bool)
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B Δ Δbucket qep maxSkip : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) (cfg : Config M)
    {m : ℕ} {VROk : RS → Prop}
    (hHk : HooksCAgrees prngBucketHsEnc (prngBucketHBoundedStep L (m + 1))
      (HBoundedPost := prngBucketHBoundedStep L m) (VROk := VROk)
      (hooksPRNGBucketParPaperC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δbucket qep tL par t)
      (DeliverForge.hooksPRNGBucketHybridGen cka prng fs Δbucket qep tL par t))
    (q : (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (es : EState (VP Γ T (Option RSt) SS RS) M (Header T × E)
      (DeliverForge.PRNGBucketState T RSt K I))
    (hHB : prngBucketHBoundedStep L (m + 1) es.h) :
    ∀ res ∈ support
      (((if paper then
          DeliverForge.implEDFPaperBucketRaw
            (DeliverForge.hooksPRNGBucketHybridGen cka prng fs Δbucket qep tL par t)
            Δ qep maxSkip cfg (.inr q)
        else
          DeliverForge.implEDFBucketRaw
            (DeliverForge.hooksPRNGBucketHybridGen cka prng fs Δbucket qep tL par t)
            Δ qep maxSkip cfg (.inr q))).run es),
      prngBucketHBoundedStep L m res.2.h := by
  have hMono := prngBucketHBoundedStep_mono (Nat.le_succ m) hHB
  rcases q with ((((arg | ⟨P, m₀, m₁, r⟩) | arg) | arg) | P) | arg
  · cases paper <;>
      exact transmitEBucket_prngBucket_bounded cka prng fs L B Δ Δbucket qep tL par t hHk es arg hHB
  · intro res hmem
    cases paper <;>
    · change res ∈ support ((DeliverForge.challEBucket (P, m₀, m₁, r)).run es) at hmem
      simp only [DeliverForge.challEBucket, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact hMono
  · cases paper <;>
      exact deliverE_prngBucket_bounded cka prng fs L B Δbucket qep maxSkip tL par t cfg hHk es arg hHB
  · cases paper <;>
      exact injectE_prngBucket_bounded cka prng fs L B Δ Δbucket qep tL par t cfg hHk es arg hHB
  · intro res hmem
    cases paper
    · change res ∈ support ((DeliverForge.corrEBucket _ P).run es) at hmem
      unfold DeliverForge.corrEBucket abortE at hmem
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
      by_cases href : (es.abort || es.g.win || !(es.g.corrAllowed P))
      · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; exact hMono
      · simp only [href, Bool.false_eq_true, ↓reduceIte, run_liftH_bind,
          mem_support_bind_iff] at hmem
        obtain ⟨⟨revRes, h₁⟩, hrev, hmem⟩ := hmem
        have hf₁ : h₁.fTable = es.h.fTable := by
          dsimp only [DeliverForge.hooksPRNGBucketHybridGen] at hrev
          simp only [StateT.run_bind, StateT.run_get, pure_bind] at hrev
          rcases hR : DeliverForge.resolveCorrRoot es.h (es.g.st P).tcur (es.g.st P).root with _ | σ <;>
            simp only [hR] at hrev
          · by_cases hc0 : (!DeliverForge.postLeak tL es.g && es.h.corrRoot.isNone &&
                !decide ((es.g.st P).tcur < healEpoch tL) &&
                ((es.g.st P).tcur == max (es.g.epoch .A) (es.g.epoch .B))) = true
            · simp only [hc0, ↓reduceIte, StateT.run_bind, DeliverForge.liftPBucket, StateT.run_lift,
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
            · simp only [hc0, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, support_pure,
                Set.mem_singleton_iff] at hrev
              cases hrev; rfl
          · by_cases hc1 : (!decide ((es.g.st P).tcur < healEpoch tL) && es.h.corrRoot.isNone) = true <;>
              by_cases hc2 : (!DeliverForge.postLeak tL es.g && es.h.lc.isNone &&
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
    · change res ∈ support ((DeliverForge.corrEPaperBucket _ P).run es) at hmem
      unfold DeliverForge.corrEPaperBucket abortE at hmem
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
      by_cases href : (es.abort || es.g.win || !(es.g.corrAllowedPaper P))
      · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; exact hMono
      · simp only [href, Bool.false_eq_true, ↓reduceIte, run_liftH_bind,
          mem_support_bind_iff] at hmem
        obtain ⟨⟨revRes, h₁⟩, hrev, hmem⟩ := hmem
        have hf₁ : h₁.fTable = es.h.fTable := by
          dsimp only [DeliverForge.hooksPRNGBucketHybridGen] at hrev
          simp only [StateT.run_bind, StateT.run_get, pure_bind] at hrev
          rcases hR : DeliverForge.resolveCorrRoot es.h (es.g.st P).tcur (es.g.st P).root with _ | σ <;>
            simp only [hR] at hrev
          · by_cases hc0 : (!DeliverForge.postLeak tL es.g && es.h.corrRoot.isNone &&
                !decide ((es.g.st P).tcur < healEpoch tL) &&
                ((es.g.st P).tcur == max (es.g.epoch .A) (es.g.epoch .B))) = true
            · simp only [hc0, ↓reduceIte, StateT.run_bind, DeliverForge.liftPBucket, StateT.run_lift,
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
            · simp only [hc0, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, support_pure,
                Set.mem_singleton_iff] at hrev
              cases hrev; rfl
          · by_cases hc1 : (!decide ((es.g.st P).tcur < healEpoch tL) && es.h.corrRoot.isNone) = true <;>
              by_cases hc2 : (!DeliverForge.postLeak tL es.g && es.h.lc.isNone &&
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
  · cases paper <;>
      exact deliverForgeE_prngBucket_bounded cka prng fs L B Δ Δbucket qep tL par t cfg hHk es arg hHB

private theorem redPRNGAuthDFBucketHybridProg_eval_eq_bind_initPRNGBucketRaw_vr
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KC] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B B_q Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
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
    (hVRHk : HooksVRInv VROkStep (DeliverForge.hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t))
    (hInitR : ∀ k, VROkStep 0 (fs.initReceiver k))
    (hFsB : ∀ rs hdr e rs' i m, VROkStep B_q rs → fs.receive rs hdr e = some (rs', i, m) → i ≤ B)
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) (qAdv : ℕ)
    (hA : DeliverForge.MakesAtMostQueriesDF A qAdv) (hqB : qAdv ≤ B_q) :
    ((redPRNGAuthDFBucketHybridProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L B Δcka qep fs.maxSkip tL par t).eval (fun _ => A) ()) =
      (do
        let es₀ ← initPRNGBucketRaw cka prng fs lam (3 + Δcka) tL par t false
        let (_, st) ←
          (simulateQ
            (DeliverForge.implEDFBucket
              (DeliverForge.hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t)
              (2 + Δcka) qep fs.maxSkip (DeliverForge.bucketAuthCfg Δcka tL par))
            A).run (es₀, none)
        return DeliverForge.authOutBucket (2 + Δcka) tL st) := by
  have hA' : A.IsQueryBoundP
      (isGameQuery (G := SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) qAdv := by
    refine hA.of_imp (fun x hx => ?_)
    rcases x with _ | _ <;> simp_all [isGameQuery]
  have hHk : ∀ {m : ℕ}, HooksCAgrees prngBucketHsEnc (prngBucketHBoundedStep L (m + 1))
      (HBoundedPost := prngBucketHBoundedStep L m) (VROk := VROkStep B_q)
      (hooksPRNGBucketParPaperC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B (3 + Δcka) qep tL par t)
      (DeliverForge.hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t) :=
    fun {m} => hooksPRNGBucketParPaperC_agrees_vr
      (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (prngInit := prngInit)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampI := sampI)
      cka prng fs L B (3 + Δcka) qep tL par t
      hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend hFsRecv heqT heqI hSampCCoins hSampK
      (fun k => hVRHk.mono (Nat.zero_le B_q) (hInitR k)) hFsB
  have hInit := initPRNGBucketHybridEStateC_eval
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampCCoins := sampCCoins)
    (sampI := sampI)
    cka prng fs hInitA hInitB hPrngUp heqI hFsInitS hFsInitR hSampKC hSampK
    L (3 + Δcka) tL par t (Expr.bool (O := OOev) false) (Env.cons (t := (.unit : Ty Sev)) () .nil)
  unfold CostedReduction.eval redPRNGAuthDFBucketHybridProg redPRNGAuthDFBucketHybridProgGen
    CostedReduction.impl
  dsimp only
  rw [eval_bind, hInit]
  let vpE := vpTblEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
    (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
    (γvT := .base .γ) (svT := .opt (.base .sig)) (ssvT := .base .ss) (rsvT := .base .rs)
  have hVp : prngVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (K := K) =
      vpE := rfl
  rw [hVp]
  simp only [bind_map_left, eval_ret, Expr.eval, Expr.v0, Env.get_cons_zero,
    bind_assoc, pure_bind]
  refine OracleComp.bind_congr_of_forall_mem_support
    (initPRNGBucketRaw cka prng fs lam (3 + Δcka) tL par t false) fun es₀ hes₀ => ?_
  have ⟨hInv₀, _, hHB₀'⟩ :=
    initPRNGBucketRaw_inv cka prng fs lam (3 + Δcka) tL par t false hqB hB1 hBB es₀ hes₀
  have hHB₀ : prngBucketHBoundedStep L qAdv es₀.h := hHB₀'
  have hVR₀ := initPRNGBucketRaw_vrInv (B := B_q) (qAdv := qAdv)
    cka prng fs lam (3 + Δcka) tL par t false
    (fun k => hVRHk.mono (Nat.zero_le _) (hInitR k)) es₀ hes₀
  have ⟨hSim, hSimInv⟩ := Engine.simulateQ_implEDFBucket_vr_eq hDefaultE (fun _ => rfl)
    prngBucketHsEnc (prngBucketHBoundedStep L) (fun hm hHB => prngBucketHBoundedStep_mono hm hHB)
    (hooksPRNGBucketParPaperC L B (3 + Δcka) qep tL par t)
    (DeliverForge.hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t)
    L B_q (2 + Δcka) qep fs.maxSkip hHk hVRHk
    (bucketParPaperAuthCfgEC (3 + Δcka) tL par) (DeliverForge.bucketAuthCfg Δcka tL par)
    (bucketParPaperAuthCfgEC_agrees Δcka tL par) rfl
    heqT heqM heqE
    (fun {m} q es hHB _ =>
      implEDFBucketRawChoice_prngBucket_bounded false cka prng fs L B (2 + Δcka) (3 + Δcka)
        qep fs.maxSkip tL par t (DeliverForge.bucketAuthCfg Δcka tL par) hHk q es hHB)
    hA' es₀ none hHB₀ hInv₀ hVR₀
  refine Eq.trans (congrArg (fun m => m >>= _) hSim) ?_
  rw [bind_map_left]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨b', es', winEp'⟩ hes' => ?_
  obtain ⟨_, hInv', _⟩ := hSimInv (b', es', winEp') hes'
  have hBnd' := hInv'.toBoundedEngine
  dsimp only [Prod.map, id]
  rw [eval_bind_ret, eval_caseOpt]
  rcases winEp' with _ | tWin
  · rfl
  · set ρ₂ := Env.cons (t := .nat) tWin
      (Env.cons (t := pbRedEsTyEv) (esEnc vpTblEnc prngBucketHsEnc es', some tWin)
        (Env.cons (t := pbRedEsTyEv) (esEnc vpTblEnc prngBucketHsEnc es', some tWin)
          (Env.cons (t := (.bool : Ty Sev)) b' .nil)))
    change (Comp.ret _).eval ρ₂ = _
    rw [eval_ret]
    congr 1
    have hAuth := cAuthOKE_eval (vpEncFn := vpTblEnc) (O' := OOev) L (2 + Δcka)
      (optNatLit tL) (.var Var.zero) (esG (.fst .v1)) ρ₂ es'.g hBnd'.leaks_le hBnd'.corrs_le rfl
    have htL : (optNatLit (O' := OOev) tL).eval ρ₂ = tL := by cases tL <;> rfl
    have hAb : (esAbort (O' := OOev) (.fst .v1)).eval ρ₂ = es'.abort := rfl
    have hW : (cGsWin (O' := OOev) (esG (.fst .v1))).eval ρ₂ = es'.g.win := rfl
    unfold DeliverForge.authOutBucket authOut
    simp only [Expr.eval, hAb, hW, hAuth, htL, Bool.and_assoc]
    rfl

private theorem redPRNGAuthDFPaperBucketHybridProg_eval_eq_bind_initPRNGBucketRaw_vr
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KC] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B B_q Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
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
    (hVRHk : HooksVRInv VROkStep (DeliverForge.hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t))
    (hInitR : ∀ k, VROkStep 0 (fs.initReceiver k))
    (hFsB : ∀ rs hdr e rs' i m, VROkStep B_q rs → fs.receive rs hdr e = some (rs', i, m) → i ≤ B)
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) (qAdv : ℕ)
    (hA : DeliverForge.MakesAtMostQueriesDF A qAdv) (hqB : qAdv ≤ B_q) :
    ((redPRNGAuthDFPaperBucketHybridProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK)
        L B Δcka qep fs.maxSkip tL par t).eval (fun _ => A) ()) =
      (do
        let es₀ ← initPRNGBucketRaw cka prng fs lam (3 + Δcka) tL par t false
        let (_, st) ←
          (simulateQ
            (DeliverForge.implEDFPaperBucket
              (DeliverForge.hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t)
              (2 + Δcka) qep fs.maxSkip (DeliverForge.bucketAuthCfg Δcka tL par))
            A).run (es₀, none)
        return DeliverForge.authOutBucketPaperAt (2 + Δcka) tL t st) := by
  have hA' : A.IsQueryBoundP
      (isGameQuery (G := SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) qAdv := by
    refine hA.of_imp (fun x hx => ?_)
    rcases x with _ | _ <;> simp_all [isGameQuery]
  have hHk : ∀ {m : ℕ}, HooksCAgrees prngBucketHsEnc (prngBucketHBoundedStep L (m + 1))
      (HBoundedPost := prngBucketHBoundedStep L m) (VROk := VROkStep B_q)
      (hooksPRNGBucketParPaperC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B (3 + Δcka) qep tL par t)
      (DeliverForge.hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t) :=
    fun {m} => hooksPRNGBucketParPaperC_agrees_vr
      (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (prngInit := prngInit)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampI := sampI)
      cka prng fs L B (3 + Δcka) qep tL par t
      hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend hFsRecv heqT heqI hSampCCoins hSampK
      (fun k => hVRHk.mono (Nat.zero_le B_q) (hInitR k)) hFsB
  have hInit := initPRNGBucketHybridEStateC_eval
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampCCoins := sampCCoins)
    (sampI := sampI)
    cka prng fs hInitA hInitB hPrngUp heqI hFsInitS hFsInitR hSampKC hSampK
    L (3 + Δcka) tL par t (Expr.bool (O := OOev) false) (Env.cons (t := (.unit : Ty Sev)) () .nil)
  unfold CostedReduction.eval redPRNGAuthDFPaperBucketHybridProg
    redPRNGAuthDFPaperBucketHybridProgGen CostedReduction.impl
  dsimp only
  rw [eval_bind, hInit]
  let vpE := vpTblEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
    (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
    (γvT := .base .γ) (svT := .opt (.base .sig)) (ssvT := .base .ss) (rsvT := .base .rs)
  have hVp : prngVpEnc (KC := KC) (Γ := Γ) (CCoins := CCoins) (I := I) (KR := KR) (K := K) =
      vpE := rfl
  rw [hVp]
  simp only [bind_map_left, eval_ret, Expr.eval, Expr.v0, Env.get_cons_zero,
    bind_assoc, pure_bind]
  refine OracleComp.bind_congr_of_forall_mem_support
    (initPRNGBucketRaw cka prng fs lam (3 + Δcka) tL par t false) fun es₀ hes₀ => ?_
  have ⟨hInv₀, _, hHB₀'⟩ :=
    initPRNGBucketRaw_inv cka prng fs lam (3 + Δcka) tL par t false hqB hB1 hBB es₀ hes₀
  have hHB₀ : prngBucketHBoundedStep L qAdv es₀.h := hHB₀'
  have hVR₀ := initPRNGBucketRaw_vrInv (B := B_q) (qAdv := qAdv)
    cka prng fs lam (3 + Δcka) tL par t false
    (fun k => hVRHk.mono (Nat.zero_le _) (hInitR k)) es₀ hes₀
  have ⟨hSim, hSimInv⟩ := Engine.simulateQ_implEDFPaperBucket_vr_eq hDefaultE (fun _ => rfl)
    prngBucketHsEnc (prngBucketHBoundedStep L) (fun hm hHB => prngBucketHBoundedStep_mono hm hHB)
    (hooksPRNGBucketParPaperC L B (3 + Δcka) qep tL par t)
    (DeliverForge.hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t)
    L B_q (2 + Δcka) qep fs.maxSkip hHk hVRHk
    (bucketParPaperAuthCfgEC (3 + Δcka) tL par) (DeliverForge.bucketAuthCfg Δcka tL par)
    (bucketParPaperAuthCfgEC_agrees Δcka tL par) rfl
    heqT heqM heqE
    (fun {m} q es hHB _ =>
      implEDFBucketRawChoice_prngBucket_bounded true cka prng fs L B (2 + Δcka) (3 + Δcka)
        qep fs.maxSkip tL par t (DeliverForge.bucketAuthCfg Δcka tL par) hHk q es hHB)
    hA' es₀ none hHB₀ hInv₀ hVR₀
  refine Eq.trans (congrArg (fun m => m >>= _) hSim) ?_
  rw [bind_map_left]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨b', es', winEp'⟩ hes' => ?_
  obtain ⟨_, hInv', _⟩ := hSimInv (b', es', winEp') hes'
  have hBnd' := hInv'.toBoundedEngine
  dsimp only [Prod.map, id]
  rw [eval_bind_ret, eval_caseOpt]
  rcases winEp' with _ | tWin
  · rfl
  · set ρ₂ := Env.cons (t := .nat) tWin
      (Env.cons (t := pbRedEsTyEv) (esEnc vpTblEnc prngBucketHsEnc es', some tWin)
        (Env.cons (t := pbRedEsTyEv) (esEnc vpTblEnc prngBucketHsEnc es', some tWin)
          (Env.cons (t := (.bool : Ty Sev)) b' .nil)))
    change (Comp.ret _).eval ρ₂ = _
    rw [eval_ret]
    congr 1
    have hAuth := cAuthOKE_eval (vpEncFn := vpTblEnc) (O' := OOev) L (2 + Δcka)
      (optNatLit tL) (.var Var.zero) (esG (.fst .v1)) ρ₂ es'.g hBnd'.leaks_le hBnd'.corrs_le rfl
    have htL : (optNatLit (O' := OOev) tL).eval ρ₂ = tL := by cases tL <;> rfl
    have hAb : (esAbort (O' := OOev) (.fst .v1)).eval ρ₂ = es'.abort := rfl
    have hW : (cGsWin (O' := OOev) (esG (.fst .v1))).eval ρ₂ = es'.g.win := rfl
    have hLc : (prngBucketHsLc (O := OOev) (esH (.fst .v1))).eval ρ₂ = es'.h.lc := rfl
    unfold DeliverForge.authOutBucketPaperAt DeliverForge.authOutBucketPaper
      DeliverForge.authOutBucket authOut
    simp only [Expr.eval, hAb, hW, hAuth, htL, hLc]
    rcases es'.h.lc with _ | e
    · simp only [Bool.and_assoc]
      rfl
    · have hρ₂ : ρ₂.get Var.zero = tWin := rfl
      simp only [Env.get_cons_zero, hρ₂, Bool.and_assoc]
      have hle : (!@decide (e < t) (Nat.decLt e t)) = decide (t ≤ e) := by
        by_cases h : e < t <;> simp [h, Nat.not_lt.mp]
      exact congrArg (fun b => !es'.abort && (es'.g.win && (authLosingConditionsAvoided (2 + Δcka) tL tWin es'.g && b)))
        ((congrArg (fun d => !@decide (e < t) d) (Subsingleton.elim _ (Nat.decLt e t))).trans hle)

private theorem redPRNGAuthDFBucketHybridProg_branch_eval_vr
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B B_q Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) {VROkStep : ℕ → RS → Prop}
    (hInitA : ckaInitA = cka.initA) (hInitB : ckaInitB = cka.initB)
    (hSend : ckaSend = cka.send) (hRecv : ckaReceive = cka.receive) (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender) (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send) (hFsRecv : fsReceive = fs.receive)
    (heqT : eqT = (· == ·)) (heqI : eqI = (· == ·)) (heqM : eqM = (· == ·)) (heqE : eqE = (· == ·))
    (hDefaultE : defaultE = default) (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins)) (hSampK : sampK = ($ᵗ K : ProbComp K))
    (hVRHk : HooksVRInv VROkStep (DeliverForge.hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t))
    (hInitR : ∀ k, VROkStep 0 (fs.initReceiver k))
    (hFsB : ∀ rs hdr e rs' i m, VROkStep B_q rs → fs.receive rs hdr e = some (rs', i, m) → i ≤ B)
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) (qAdv : ℕ)
    (hA : DeliverForge.MakesAtMostQueriesDF A qAdv) (hqB : qAdv ≤ B_q) (b_prng : Bool) :
    PRFPRNG.branch prng b_prng
      ((redPRNGAuthDFBucketHybridProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
          (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L B Δcka qep fs.maxSkip tL par t).eval (fun _ => A) ()) =
      PRFPRNG.branch prng b_prng
        (DeliverForge.redPRNGAuthDFBucketHybrid cka prng fs lam Δcka qep tL par t A) := by
  rw [redPRNGAuthDFBucketHybridProg_eval_eq_bind_initPRNGBucketRaw_vr cka prng fs L B B_q Δcka qep
    tL par t hInitA hInitB hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend hFsRecv heqT heqI heqM
    heqE hDefaultE hSampKC hSampCCoins hSampK hVRHk hInitR hFsB hB1 hBB A qAdv hA hqB]
  unfold PRFPRNG.branch DeliverForge.redPRNGAuthDFBucketHybrid DeliverForge.engRunDFBucket
    DeliverForge.initPRNGBucketHybrid initPRNGBucketRaw
  refine bind_congr fun kr => ?_
  rw [StateT.run'_eq, StateT.run'_eq]
  refine congrArg (Prod.fst <$> ·) ?_
  simp only [StateT.run_bind, StateT.run_lift, simulateQ_bind, simulateQ_sampleT_run_bucket,
    bind_assoc, pure_bind]
  refine bind_congr fun kc => ?_
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨step, h₀⟩, sp⟩ hmem => ?_
  obtain ⟨σv, k, rfl⟩ := rootPRNGBucketHybrid_zero_support_some (T := T)
    prng (3 + Δcka) tL par t lam kr b_prng step h₀ sp hmem
  simp [StateT.run_pure, simulateQ_pure]; rfl

private theorem redPRNGAuthDFPaperBucketHybridProg_branch_eval_vr
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B B_q Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) {VROkStep : ℕ → RS → Prop}
    (hInitA : ckaInitA = cka.initA) (hInitB : ckaInitB = cka.initB)
    (hSend : ckaSend = cka.send) (hRecv : ckaReceive = cka.receive) (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender) (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send) (hFsRecv : fsReceive = fs.receive)
    (heqT : eqT = (· == ·)) (heqI : eqI = (· == ·)) (heqM : eqM = (· == ·)) (heqE : eqE = (· == ·))
    (hDefaultE : defaultE = default) (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins)) (hSampK : sampK = ($ᵗ K : ProbComp K))
    (hVRHk : HooksVRInv VROkStep (DeliverForge.hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t))
    (hInitR : ∀ k, VROkStep 0 (fs.initReceiver k))
    (hFsB : ∀ rs hdr e rs' i m, VROkStep B_q rs → fs.receive rs hdr e = some (rs', i, m) → i ≤ B)
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) (qAdv : ℕ)
    (hA : DeliverForge.MakesAtMostQueriesDF A qAdv) (hqB : qAdv ≤ B_q) (b_prng : Bool) :
    PRFPRNG.branch prng b_prng
      ((redPRNGAuthDFPaperBucketHybridProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
          (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L B Δcka qep fs.maxSkip tL par t).eval (fun _ => A) ()) =
      PRFPRNG.branch prng b_prng
        (DeliverForge.redPRNGAuthDFPaperBucketHybrid cka prng fs lam Δcka qep tL par t A) := by
  rw [redPRNGAuthDFPaperBucketHybridProg_eval_eq_bind_initPRNGBucketRaw_vr cka prng fs L B B_q Δcka qep
    tL par t hInitA hInitB hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend hFsRecv heqT heqI heqM
    heqE hDefaultE hSampKC hSampCCoins hSampK hVRHk hInitR hFsB hB1 hBB A qAdv hA hqB]
  unfold PRFPRNG.branch DeliverForge.redPRNGAuthDFPaperBucketHybrid
    DeliverForge.redPRNGAuthDFPaperBucketHybridAt DeliverForge.engRunDFPaperBucket
    DeliverForge.initPRNGBucketHybrid initPRNGBucketRaw
  refine bind_congr fun kr => ?_
  rw [StateT.run'_eq, StateT.run'_eq]
  refine congrArg (Prod.fst <$> ·) ?_
  simp only [StateT.run_bind, StateT.run_lift, simulateQ_bind, simulateQ_sampleT_run_bucket,
    bind_assoc, pure_bind]
  refine bind_congr fun kc => ?_
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨step, h₀⟩, sp⟩ hmem => ?_
  obtain ⟨σv, k, rfl⟩ := rootPRNGBucketHybrid_zero_support_some (T := T)
    prng (3 + Δcka) tL par t lam kr b_prng step h₀ sp hmem
  simp [StateT.run_pure, simulateQ_pure]; rfl

theorem redPRNGAuthDFBucketHybridProg_advantage_vr_impl
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B B_q Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
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
    (hVRHk : HooksVRInv VROkStep (DeliverForge.hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t))
    (hInitR : ∀ k, VROkStep 0 (fs.initReceiver k))
    (hFsB : ∀ rs hdr e rs' i m, VROkStep B_q rs → fs.receive rs hdr e = some (rs', i, m) → i ≤ B)
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) (qAdv : ℕ)
    (hA : DeliverForge.MakesAtMostQueriesDF A qAdv) (hqB : qAdv ≤ B_q) :
    PRFPRNG.advantage prng
      ((redPRNGAuthDFBucketHybridProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
          (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK)
          L B Δcka qep fs.maxSkip tL par t).eval (fun _ => A) ()) =
      PRFPRNG.advantage prng
        (DeliverForge.redPRNGAuthDFBucketHybrid cka prng fs lam Δcka qep tL par t A) := by
  have hGame : PRFPRNG.game prng
      ((redPRNGAuthDFBucketHybridProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
          (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK)
          L B Δcka qep fs.maxSkip tL par t).eval (fun _ => A) ()) =
      PRFPRNG.game prng
        (DeliverForge.redPRNGAuthDFBucketHybrid cka prng fs lam Δcka qep tL par t A) := by
    unfold PRFPRNG.game
    refine bind_congr fun b_prng => ?_
    have hBr := redPRNGAuthDFBucketHybridProg_branch_eval_vr
      (prngInit := prngInit) (lam := lam) (sampKR := sampKR) (sampI := sampI)
      cka prng fs L B B_q Δcka qep tL par t
      hInitA hInitB hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend hFsRecv
      heqT heqI heqM heqE hDefaultE hSampKC hSampCCoins hSampK
      hVRHk hInitR hFsB hB1 hBB A qAdv hA hqB b_prng
    unfold PRFPRNG.branch at hBr
    simp only [← bind_assoc]
    exact congrArg (· >>= fun b' => pure (b_prng == b')) hBr
  unfold PRFPRNG.advantage
  rw [hGame]

theorem redPRNGAuthDFPaperBucketHybridProg_advantage_vr_impl
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (L B B_q Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
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
    (hVRHk : HooksVRInv VROkStep (DeliverForge.hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t))
    (hInitR : ∀ k, VROkStep 0 (fs.initReceiver k))
    (hFsB : ∀ rs hdr e rs' i m, VROkStep B_q rs → fs.receive rs hdr e = some (rs', i, m) → i ≤ B)
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) (qAdv : ℕ)
    (hA : DeliverForge.MakesAtMostQueriesDF A qAdv) (hqB : qAdv ≤ B_q) :
    PRFPRNG.advantage prng
      ((redPRNGAuthDFPaperBucketHybridProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
          (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK)
          L B Δcka qep fs.maxSkip tL par t).eval (fun _ => A) ()) =
      PRFPRNG.advantage prng
        (DeliverForge.redPRNGAuthDFPaperBucketHybrid cka prng fs lam Δcka qep tL par t A) := by
  have hGame : PRFPRNG.game prng
      ((redPRNGAuthDFPaperBucketHybridProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
          (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
          (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
          (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK)
          L B Δcka qep fs.maxSkip tL par t).eval (fun _ => A) ()) =
      PRFPRNG.game prng
        (DeliverForge.redPRNGAuthDFPaperBucketHybrid cka prng fs lam Δcka qep tL par t A) := by
    unfold PRFPRNG.game
    refine bind_congr fun b_prng => ?_
    have hBr := redPRNGAuthDFPaperBucketHybridProg_branch_eval_vr
      (prngInit := prngInit) (lam := lam) (sampKR := sampKR) (sampI := sampI)
      cka prng fs L B B_q Δcka qep tL par t
      hInitA hInitB hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend hFsRecv
      heqT heqI heqM heqE hDefaultE hSampKC hSampCCoins hSampK
      hVRHk hInitR hFsB hB1 hBB A qAdv hA hqB b_prng
    unfold PRFPRNG.branch at hBr
    simp only [← bind_assoc]
    exact congrArg (· >>= fun b' => pure (b_prng == b')) hBr
  unfold PRFPRNG.advantage
  rw [hGame]

end HooksPRNGBucketEval

end CryptoGames.SM.Construction
