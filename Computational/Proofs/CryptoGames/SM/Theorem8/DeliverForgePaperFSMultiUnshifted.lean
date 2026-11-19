/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFS -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperBucketFS -- proof-setup: allow-public-import
public import Computational.Proofs.HeadlineV1.DeliverForgePaperChallSim -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.Fig8Atomic -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SessionAuthBridge -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.Ratchet.LibsignalShortDefs
import Computational.Proofs.CryptoGames.FSAEAD.PubProofDefs
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma11Aux
import Computational.Proofs.E2E.SessionAuthPubToAD
import Computational.Proofs.E2E.SessionAuthMultiDec
import Computational.Proofs.E2E.SessionAuthMultiShort
import Computational.Proofs.E2E.SessionAuthRouter
import Computational.Proofs.E2E.SessionAuthQueries
import Computational.Proofs.E2E.SessionAuthWireQueries

/-!
# Unshifted Multi-Session `DeliverForge` `TwoModeMultiSessBounds` (`N04b`)

Proves `redFSAuthDFPaperMulti_twoModeMultiSessBounds` (`qR = 2 * q`, `M = q`, `qd = q`) for
`multiSessPubToAD protoSignalCodec` over `redFSAuthDFPaperMulti`.-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFSMulti

open OracleSpec OracleComp
open _root_.CryptoGames (Party CKAScheme PRFPRNG FSAEADScheme)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.CKA (DHFun dhScheme)
open _root_.CryptoGames.Ratchet (rootPRNG)
open _root_.CryptoGames.SM (GameState Pos Record)
open _root_.CryptoGames.SM.Engine (VP Ctx EState TComp vSend vRecv liftH abortE commitE
  transmitE challE deliverE injectE coinsE)
open _root_.CryptoGames.SM.Construction (Header PartyState Mode sampleT mkParties
  FSMultiSpec FSMultiState FSMultiBook liftFSMulti lookupMultiF regSessMulti regSessOptMulti
  rootFSMulti hooksFSMulti initFSMultiRaw runFSMultiDFPaper redFSAuthDFPaperMulti)
open _root_.CryptoGames.SM.Construction.DeliverForge (specDF AdversaryDF SchemeAdversaryDF
  MakesAtMostQueriesDF deliverForgeE corrEPaper implEDFPaper)
open _root_.CryptoGames.GuardedSafe (GuardedSafePost)
open _root_.CryptoGames.FSAEAD (corruptSenderQuery transmitQuery challengeQuery deliverQuery
  injectQuery encBadMsg queryADOutsideClass)
open _root_.CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey maxForwardJumps)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart lFS)
open _root_.CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C)
open _root_.CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open _root_.CryptoVerification.LibsignalSession.HeadlineV1 (badSendMsgDF SendMsgsOkDF
  GuardedSMDFShort)
open Computational.Proofs.ReductionDsl.Fig8Atomic (atomicShortPubB atomicShortPubB_imp_shortB)
open _root_.CryptoVerification.E2E.Signed.SessionRouter (sessOffRange onAnySess onSess)
open _root_.CryptoVerification.E2E.Signed.SessionWireQueries (fsOutsideClass onSess_imp_onAnySess)
open Computational.Proofs.E2E.SessionAuthBridge (multiSessPubToAD TwoModeMultiSessBounds)
open Computational.Proofs.E2E.SessionAuthPubToAD (multiSessPubToAD_offRange
  multiSessPubToAD_decBound multiSessPubToAD_shortAD multiSessPubToAD_oneADClass
  multiSessPubToAD_guardedShort)

/-! ## 1. `SafeZero` Bridge & Query Lifting Helpers -/

private abbrev SafeZero {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (Q : spec.Domain → Prop) (Post : α → Prop) (oa : OracleComp spec α) : Prop :=
  GuardedSafePost (fun _ _ => True) Q Post oa

private theorem safeZero_to_isQueryBoundP
    {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    {Q : spec.Domain → Prop} [DecidablePred Q] {Post : α → Prop} {oa : OracleComp spec α}
    (h : SafeZero Q Post oa) : oa.IsQueryBoundP Q 0 := by
  induction h with
  | pure _ => simp
  | query_bind hQt _ ih =>
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl hQt, fun u => by simpa [hQt] using ih u trivial⟩

private theorem query_eq_liftM {ι : Type} {spec : OracleSpec.{0, 0} ι} (t : spec.Domain) :
    (query (spec := spec) t : OracleComp spec (spec.Range t)) = liftM (spec.query t) := rfl

private theorem hq_to_isRight {Γ T RSt SS RS M CCoins E : Type} {q : ℕ}
    {A : SchemeAdversaryDF Γ T RSt SS RS M CCoins E}
    (hq : MakesAtMostQueriesDF A q) : A.IsQueryBoundP (fun x => x.isRight = true) q :=
  hq.of_imp fun x hx => by rcases x with _ | _ <;> simp_all

private theorem safeZero_sampleT {ι₀ : Type} {tspec : OracleSpec.{0, 0} ι₀}
    {Q : (unifSpec + tspec).Domain → Prop} (hInl : ∀ u, ¬ Q (.inl u))
    (X : Type) [SampleableType X] :
    SafeZero Q (fun _ => True) (sampleT (tspec := tspec) X) :=
  GuardedSafePost.liftComp_unif hInl ($ᵗ X : ProbComp X)

private theorem safeZero_lift_sampleT {ι₀ : Type} {tspec : OracleSpec.{0, 0} ι₀}
    {HS : Type} {Q : (unifSpec + tspec).Domain → Prop} (hInl : ∀ u, ¬ Q (.inl u))
    (X : Type) [SampleableType X] (h : HS) :
    SafeZero Q (fun z : X × HS => z.2 = h)
      ((StateT.lift (sampleT (tspec := tspec) X) : StateT HS (TComp tspec) X).run h) := by
  rw [StateT.run_lift]
  exact (safeZero_sampleT hInl X).bind fun _ _ => GuardedSafePost.pure rfl

private theorem hm_run_bind {ι₀ : Type} {tspec : OracleSpec.{0, 0} ι₀} {HS α β : Type}
    (x : StateT HS (TComp tspec) α) (f : α → StateT HS (TComp tspec) β) (s : HS) :
    (x >>= f).run s = (x.run s >>= fun p => (f p.1).run p.2) := rfl

private theorem liftH_run {ι₀ : Type} {tspec : OracleSpec.{0, 0} ι₀}
    {Vγ T VR VSg VRg M E HS α : Type}
    (m : StateT HS (TComp tspec) α)
    (es : EState (VP Vγ T VR VSg VRg) M (Header T × E) HS) :
    (liftH m).run es = (m.run es.h >>= fun p => pure (p.1, { es with h := p.2 })) := rfl

private theorem safeZero_liftFSMulti_query
    {SS RS T M E RSt K I : Type} {Q : (unifSpec + FSMultiSpec SS RS T M E).Domain → Prop}
    (sIdx : ℕ) (q : (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E).Domain)
    (hQ : ¬ Q (.inr ⟨sIdx, q⟩)) (h : FSMultiState T RSt K I E) :
    SafeZero Q (fun z => z.2 = h)
      ((liftFSMulti (SS := SS) (RS := RS) (T := T) (M := M) (E := E)
        (Sig := RSt) (K := K) (I := I) sIdx
        (liftM (OracleSpec.query
          (spec := unifSpec + _root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E) (.inr q)))).run h) := by
  have hq : ((liftFSMulti (SS := SS) (RS := RS) (T := T) (M := M) (E := E)
      (Sig := RSt) (K := K) (I := I) sIdx (liftM (OracleSpec.query
        (spec := unifSpec + _root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E) (.inr q)))).run h) =
      (query (spec := unifSpec + FSMultiSpec SS RS T M E)
        (Sum.inr ⟨sIdx, q⟩) >>= fun a => pure (a, h)) := by
    simp [liftFSMulti, StateT.run_lift]
  rw [hq, query_eq_liftM]
  exact GuardedSafePost.query_bind hQ fun _ _ => GuardedSafePost.pure rfl

private theorem sendsIn_of_succ_false {P : Party} {k : ℕ}
    (h : P.sendsIn (k + 1) = false) : P.sendsIn k = true := by
  cases P <;> simp only [Party.sendsIn, beq_eq_false_iff_ne, beq_iff_eq] at h ⊢ <;> omega

private theorem epMgmt_st {St Msg C : Type} (s : GameState St Msg C)
    (Δ qep : ℕ) (P : Party) (hasCoins : Bool) {s₁ : GameState St Msg C}
    (h : s.epMgmt Δ qep P hasCoins = some s₁) : s₁.st = s.st := by
  unfold GameState.epMgmt at h
  split_ifs at h <;> cases h <;> simp [GameState.leak]

/-! ## 2. Unified Bad-Query Predicate & Engine State Invariant (`PaperMultiInv`) -/

private def badEncMulti {SS RS T M E : Type} (ok : M → Bool) :
    (unifSpec + FSMultiSpec SS RS T M E).Domain → Bool
  | .inl _ => false
  | .inr ⟨_, q⟩ => encBadMsg (SS := SS) (RS := RS) (AD := Header T) (C := E) ok (.inr q)

private def outEpMulti {SS RS T M E : Type} (t : ℕ) :
    (unifSpec + FSMultiSpec SS RS T M E).Domain → Bool
  | .inl _ => false
  | .inr ⟨_, q⟩ =>
    queryADOutsideClass (SS := SS) (RS := RS) (AD := Header T) (Msg := M) (C := E)
      (fun h : Header T => h.1) t (.inr q)

private def badMultiQuery {SS RS T M E : Type} (M_cap t : ℕ) (ok : M → Bool)
    (x : (unifSpec + FSMultiSpec SS RS T M E).Domain) : Bool :=
  sessOffRange M_cap x || badEncMulti ok x || outEpMulti t x

private theorem badMultiQuery_inl_false {SS RS T M E : Type}
    (M_cap t : ℕ) (ok : M → Bool) (u : unifSpec.Domain) :
    ¬ (badMultiQuery (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_cap t ok (.inl u) = true) := by
  simp [badMultiQuery, sessOffRange, badEncMulti, outEpMulti]

private structure PaperMultiInv {Γ T RSt K I SS RS M E : Type}
    (t M_cap rem : ℕ)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E)) : Prop where
  len_le : es.h.sessions.length + rem ≤ M_cap
  id_eq : ∀ P : Party, (es.g.st P).id = P
  cache_ok : ∀ t' Tc σc k sIdx,
    es.h.cache t' = some (Tc, σc, k, some sIdx) → t' = t ∧ sIdx < es.h.sessions.length
  vs_ep : ∀ P sIdx,
    P.sendsIn (es.g.st P).tcur = true → (es.g.st P).vS = some (.inr sIdx) → (es.g.st P).tcur = t
  vs_lt : ∀ P sIdx,
    (es.g.st P).vS = some (.inr sIdx) → sIdx < es.h.sessions.length
  vr_ok : ∀ P t' sIdx,
    (es.g.st P).vR t' = some (.inr sIdx) → t' = t ∧ sIdx < es.h.sessions.length

private theorem PaperMultiInv.mono_rem {Γ T RSt K I SS RS M E : Type}
    {t M_cap rem₁ rem₂ : ℕ}
    {es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E)}
    (h : PaperMultiInv t M_cap rem₂ es) (hle : rem₁ ≤ rem₂) :
    PaperMultiInv t M_cap rem₁ es :=
  { h with len_le := Nat.le_trans (Nat.add_le_add_left hle _) h.len_le }

private theorem PaperMultiInv.with_g_same_st {Γ T RSt K I SS RS M E : Type}
    {t M_cap rem : ℕ}
    {es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E)}
    {g' : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E} {ab' : Bool}
    (h : PaperMultiInv t M_cap rem es) (hst : g'.st = es.g.st) :
    PaperMultiInv t M_cap rem { es with g := g', abort := ab' } :=
  { len_le := h.len_le
    id_eq := fun P => by dsimp; rw [hst]; exact h.id_eq P
    cache_ok := h.cache_ok
    vs_ep := fun P sIdx hs hv => by dsimp at hs hv ⊢; rw [hst] at hs hv ⊢; exact h.vs_ep P sIdx hs hv
    vs_lt := fun P sIdx hv => by dsimp at hv; rw [hst] at hv; exact h.vs_lt P sIdx hv
    vr_ok := fun P t' sIdx hv => by dsimp at hv; rw [hst] at hv; exact h.vr_ok P t' sIdx hv }

/-! ## 3. Multi-Session Hook & Initialization Safety Lemmas -/

section HookSpecs

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}
  [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
  [SampleableType I] [SampleableType K]

private theorem lookupMultiF_safe {Q : (unifSpec + FSMultiSpec SS RS T M E).Domain → Prop}
    (hInl : ∀ u, ¬ Q (.inl u)) (Ik : I) (h : FSMultiState T RSt K I E) :
    SafeZero Q (fun r => r.2.sessions = h.sessions ∧ r.2.cache = h.cache)
      ((lookupMultiF (SS := SS) (RS := RS) (T := T) (M := M) (E := E) Ik).run h) := by
  unfold lookupMultiF
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rcases h.table.lookup Ik with _ | k
  · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
    exact (safeZero_lift_sampleT hInl K h).bind fun ⟨_, h1⟩ hh1 => by
      subst hh1; exact GuardedSafePost.pure ⟨rfl, rfl⟩
  · simp only [StateT.run_pure]; exact GuardedSafePost.pure ⟨rfl, rfl⟩

private theorem regSessMulti_safe {Q : (unifSpec + FSMultiSpec SS RS T M E).Domain → Prop}
    (Ik : I) (h : FSMultiState T RSt K I E) :
    SafeZero Q
      (fun r => r.1 < r.2.sessions.length ∧ h.sessions.length ≤ r.2.sessions.length ∧
        r.2.sessions.length ≤ h.sessions.length + 1 ∧ r.2.cache = h.cache)
      ((regSessMulti (SS := SS) (RS := RS) (T := T) (M := M) (E := E) Ik).run h) := by
  unfold regSessMulti
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs with hmem
  · simp only [StateT.run_pure]
    exact GuardedSafePost.pure ⟨List.idxOf_lt_length_of_mem hmem, le_rfl, Nat.le_add_right _ _, rfl⟩
  · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
    exact GuardedSafePost.pure ⟨by simp, by simp, by simp, rfl⟩

private theorem regSessOptMulti_safe {Q : (unifSpec + FSMultiSpec SS RS T M E).Domain → Prop}
    (sid : Option I) (h : FSMultiState T RSt K I E) :
    SafeZero Q
      (fun r =>
        (∀ sIdx, r.1 = some sIdx → sid.isSome = true ∧ sIdx < r.2.sessions.length) ∧
        (sid = none → r.1 = none ∧ r.2 = h) ∧
        h.sessions.length ≤ r.2.sessions.length ∧
        r.2.sessions.length ≤ h.sessions.length + 1 ∧ r.2.cache = h.cache)
      ((regSessOptMulti (SS := SS) (RS := RS) (T := T) (M := M) (E := E) sid).run h) := by
  rcases sid with _ | Ik
  · simp only [regSessOptMulti, StateT.run_pure]
    exact GuardedSafePost.pure
      ⟨(fun _ h1 => by cases h1), fun _ => ⟨rfl, rfl⟩, le_rfl, Nat.le_add_right _ _, rfl⟩
  · rw [regSessOptMulti, map_eq_bind_pure_comp, hm_run_bind]
    refine (regSessMulti_safe Ik h).bind fun ⟨idx, h'⟩ hp => ?_
    dsimp only at hp ⊢
    simp only [Function.comp_apply, StateT.run_pure]
    exact GuardedSafePost.pure
      ⟨(fun sIdx hs => by injection hs with hs'; subst hs'; exact ⟨rfl, hp.1⟩),
       (fun hno => by cases hno), hp.2.1, hp.2.2.1, hp.2.2.2⟩

private theorem rootFSMulti_safe {Q : (unifSpec + FSMultiSpec SS RS T M E).Domain → Prop}
    (hInl : ∀ u, ¬ Q (.inl u))
    (prng : PRFPRNG KR RSt I K) (mo : Mode) (t' : ℕ) (Ik : I) (σ : RSt)
    (h : FSMultiState T RSt K I E) :
    SafeZero Q (fun r => r.2.sessions = h.sessions ∧ r.2.cache = h.cache ∧
        (r.1.2.2.isSome = true → t' = mo.tStar))
      ((rootFSMulti (SS := SS) (RS := RS) (T := T) (M := M) (E := E) prng mo t' Ik σ).run h) := by
  unfold rootFSMulti
  split_ifs with hgt heq hth1 hth2
  · simp only [StateT.run_pure]; exact GuardedSafePost.pure ⟨rfl, rfl, fun hs => by simp at hs⟩
  · simp only [StateT.run_bind, StateT.run_pure]
    refine (safeZero_lift_sampleT hInl I h).bind fun ⟨Ir, h1⟩ hh1 => ?_
    refine (safeZero_lift_sampleT hInl K h1).bind fun ⟨k, h2⟩ hh2 => ?_
    subst hh1; subst hh2; exact GuardedSafePost.pure ⟨rfl, rfl, fun _ => heq⟩
  · simp only [StateT.run_bind, StateT.run_pure]
    exact (lookupMultiF_safe hInl Ik h).bind fun ⟨k, h1⟩ hh1 =>
      GuardedSafePost.pure ⟨hh1.1, hh1.2, fun _ => heq⟩
  · simp only [StateT.run_bind, StateT.run_pure]
    exact (safeZero_lift_sampleT hInl I h).bind fun ⟨Ir, h1⟩ hh1 => by
      subst hh1; exact GuardedSafePost.pure ⟨rfl, rfl, fun hs => by simp at hs⟩
  · simp only [StateT.run_pure]; exact GuardedSafePost.pure ⟨rfl, rfl, fun hs => by simp at hs⟩

private theorem initFSMultiRaw_paperMulti_safe
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (M_cap q : ℕ) (hqM : q ≤ M_cap) (tL : Option ℕ) (t : ℕ) (ht0 : 0 < t)
    (ok : M → Bool) (b : Bool) :
    SafeZero (fun x => badMultiQuery M_cap t ok x = true)
      (PaperMultiInv t M_cap q) (initFSMultiRaw cka prng fs lam ⟨true, tL, t⟩ b) := by
  have hInl := badMultiQuery_inl_false (SS := SS) (RS := RS) (T := T) (E := E) M_cap t ok
  unfold initFSMultiRaw
  refine (safeZero_sampleT hInl KR).bind fun kr _ => ?_
  refine (safeZero_sampleT hInl KC).bind fun kc _ => ?_
  refine (rootFSMulti_safe hInl prng ⟨true, tL, t⟩ 0 lam (prng.init kr) {}).bind
    fun ⟨⟨σ, k, sid⟩, h1⟩ hh1 => ?_
  dsimp only at hh1
  have hsid : sid = none := by
    cases hsid' : sid with
    | none => rfl
    | some _ => have := hh1.2.2 (by simp [hsid']); omega
  refine (regSessOptMulti_safe sid h1).bind fun ⟨optIdx, h2⟩ hh2 => ?_
  dsimp only at hh2
  rcases hh2.2.1 hsid with ⟨hopt, hh2_eq⟩
  cases hopt
  have hlen0 : h2.sessions.length = 0 := by rw [hh2_eq, hh1.1]; rfl
  refine GuardedSafePost.pure
    { len_le := by dsimp only; omega
      id_eq := fun P => by cases P <;> rfl
      cache_ok := fun t' _ _ _ _ hc => by rw [hh2_eq, hh1.2.1] at hc; cases hc
      vs_ep := fun P _ _ hvs => by cases P <;> simp [mkParties] at hvs
      vs_lt := fun P _ hvs => by cases P <;> simp [mkParties] at hvs
      vr_ok := fun P t' _ hvr => by
        cases P
        · simp only [mkParties] at hvr; split_ifs at hvr; cases hvr
        · simp [mkParties] at hvr }

section FixedHooks

variable (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
  (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka M_cap : ℕ)
  (tL : Option ℕ) (t : ℕ) (la : Bool) (ok : M → Bool)

private theorem hooksFSMulti_startSend_safe
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party) (t' : ℕ) (γ : Γ) (σ : RSt)
    (r : Option CCoins) (h : FSMultiState T RSt K I E)
    (hCache : ∀ τ Tc σc k sIdx,
      h.cache τ = some (Tc, σc, k, some sIdx) → τ = t ∧ sIdx < h.sessions.length) :
    SafeZero (fun x => badMultiQuery M_cap t ok x = true)
      (fun res => h.sessions.length ≤ res.2.sessions.length ∧
        res.2.sessions.length ≤ h.sessions.length + 1 ∧
        (∀ τ Tc σc k sIdx, res.2.cache τ = some (Tc, σc, k, some sIdx) → τ = t ∧ sIdx < res.2.sessions.length) ∧
        (∀ γ' T' σ' ssv sIdx, res.1 = some (γ', T', σ', ssv) → ssv = .inr sIdx → t' = t ∧ sIdx < res.2.sessions.length))
      (((hooksFSMulti cka prng fs Δcka ⟨true, tL, t⟩ false la).startSend ctx P t' γ σ r).run h) := by
  have hInl := badMultiQuery_inl_false (SS := SS) (RS := RS) (T := T) (E := E) M_cap t ok
  dsimp only [hooksFSMulti]
  have hPure : ∀ (coins : CCoins) (σ' : RSt) (k : K) (sid : Option I) (h1 : FSMultiState T RSt K I E),
      (h1.sessions = h.sessions ∧ h1.cache = h.cache ∧ (sid.isSome = true → t' = t)) →
      ∀ (optIdx : Option ℕ) (h2 : FSMultiState T RSt K I E),
      ((∀ sIdx, optIdx = some sIdx → sid.isSome = true ∧ sIdx < h2.sessions.length) ∧
        (sid = none → optIdx = none ∧ h2 = h1) ∧ h1.sessions.length ≤ h2.sessions.length ∧
        h2.sessions.length ≤ h1.sessions.length + 1 ∧ h2.cache = h1.cache) →
      (let res : Option (Γ × T × RSt × (SS ⊕ ℕ)) × FSMultiState T RSt K I E :=
        (some ((cka.send γ coins).1, (cka.send γ coins).2.1, σ',
          match optIdx with | none => .inl (fs.initSender k) | some sIdx => .inr sIdx),
         { h2 with cache := Function.update h2.cache t' (some ((cka.send γ coins).2.1, σ', k, optIdx)) });
       h.sessions.length ≤ res.2.sessions.length ∧ res.2.sessions.length ≤ h.sessions.length + 1 ∧
       (∀ τ Tc σc kc sIdx, res.2.cache τ = some (Tc, σc, kc, some sIdx) → τ = t ∧ sIdx < res.2.sessions.length) ∧
       (∀ γ' T' σ' ssv sIdx, res.1 = some (γ', T', σ', ssv) → ssv = .inr sIdx → t' = t ∧ sIdx < res.2.sessions.length)) := by
    intro coins σ' k sid h1 hh1 optIdx h2 hh2; dsimp only
    have hmono : h.sessions.length ≤ h2.sessions.length := by rw [← hh1.1]; exact hh2.2.2.1
    refine ⟨hmono, by rw [← hh1.1]; exact hh2.2.2.2.1, fun τ Tc σc kc sIdx hc => ?_, fun _ _ _ ssv sIdx hres hssv => ?_⟩
    · by_cases hτ : τ = t'
      · subst hτ; simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hc
        rcases hh2.1 sIdx hc.2.2.2 with ⟨hsid_some, hlt⟩; exact ⟨hh1.2.2 hsid_some, hlt⟩
      · simp only [Function.update_of_ne hτ, hh2.2.2.2.2, hh1.2.1] at hc
        exact ⟨(hCache τ Tc σc kc sIdx hc).1, Nat.lt_of_lt_of_le (hCache τ Tc σc kc sIdx hc).2 hmono⟩
    · injection hres with htuple; subst hssv
      have hssv_eq := (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj htuple).2).2).2
      cases hopt : optIdx with
      | none => simp [hopt] at hssv_eq
      | some idx =>
        simp only [hopt, Sum.inr.injEq] at hssv_eq; subst hssv_eq
        rcases hh2.1 idx hopt with ⟨hsid_some, hidx_lt⟩; exact ⟨hh1.2.2 hsid_some, hidx_lt⟩
  rcases r with _ | c
  · dsimp only; rw [hm_run_bind]
    refine (safeZero_lift_sampleT hInl CCoins h).bind fun ⟨coins, h0⟩ hh0 => ?_
    dsimp only at hh0 ⊢; subst h0; rw [hm_run_bind]
    refine (rootFSMulti_safe hInl prng ⟨true, tL, t⟩ t' (cka.send γ coins).2.2 σ h).bind fun ⟨⟨σ', k, sid⟩, h1⟩ hh1 => ?_
    dsimp only at hh1 ⊢; rw [hm_run_bind]
    refine (regSessOptMulti_safe sid h1).bind fun ⟨optIdx, h2⟩ hh2 => ?_
    dsimp only at hh2 ⊢; simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
    exact GuardedSafePost.pure (hPure coins σ' k sid h1 hh1 optIdx h2 hh2)
  · dsimp only; simp only [pure_bind]; rw [hm_run_bind]
    refine (rootFSMulti_safe hInl prng ⟨true, tL, t⟩ t' (cka.send γ c).2.2 σ h).bind fun ⟨⟨σ', k, sid⟩, h1⟩ hh1 => ?_
    dsimp only at hh1 ⊢; rw [hm_run_bind]
    refine (regSessOptMulti_safe sid h1).bind fun ⟨optIdx, h2⟩ hh2 => ?_
    dsimp only at hh2 ⊢; simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
    exact GuardedSafePost.pure (hPure c σ' k sid h1 hh1 optIdx h2 hh2)

private theorem hooksFSMulti_startRecv_safe
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party) (t' : ℕ) (γ : Γ) (σ : RSt) (Tn : T)
    (h : FSMultiState T RSt K I E)
    (hCache : ∀ τ Tc σc k sIdx, h.cache τ = some (Tc, σc, k, some sIdx) → τ = t ∧ sIdx < h.sessions.length) :
    SafeZero (fun x => badMultiQuery M_cap t ok x = true)
      (fun res => h.sessions.length ≤ res.2.sessions.length ∧
        res.2.sessions.length ≤ h.sessions.length + 1 ∧ res.2.cache = h.cache ∧
        (∀ γ' σ' rsv sIdx, res.1 = some (some (γ', σ', rsv)) → rsv = .inr sIdx → t' = t ∧ sIdx < res.2.sessions.length))
      (((hooksFSMulti cka prng fs Δcka ⟨true, tL, t⟩ false la).startRecv ctx P t' γ σ Tn).run h) := by
  have hInl := badMultiQuery_inl_false (SS := SS) (RS := RS) (T := T) (E := E) M_cap t ok
  dsimp only [hooksFSMulti]; simp only [StateT.run_bind, StateT.run_get, pure_bind]
  have hForgedBranch :
      SafeZero (fun x => badMultiQuery (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_cap t ok x = true)
        (fun res : Option (Option (Γ × RSt × (RS ⊕ ℕ))) × FSMultiState T RSt K I E =>
          h.sessions.length ≤ res.2.sessions.length ∧ res.2.sessions.length ≤ h.sessions.length + 1 ∧
          res.2.cache = h.cache ∧
          (∀ γ' σ' rsv sIdx, res.1 = some (some (γ', σ', rsv)) → rsv = .inr sIdx → t' = t ∧ sIdx < res.2.sessions.length))
        ((if false then return some none
          else if (⟨true, tL, t⟩ : Mode).auth && t' = (⟨true, tL, t⟩ : Mode).tStar then
            if (⟨true, tL, t⟩ : Mode).tL.isSome && (⟨true, tL, t⟩ : Mode).tStar = (⟨true, tL, t⟩ : Mode).tH then
              return none
            else do
              let kk := cka.receive γ Tn
              let _ ← lookupMultiF (SS := SS) (RS := RS) (T := T) (M := M) (E := E) kk.2
              let sIdx ← regSessMulti (SS := SS) (RS := RS) (T := T) (M := M) (E := E) kk.2
              return some (some (kk.1, (prng.up σ kk.2).1, (Sum.inr sIdx : RS ⊕ ℕ)))
          else return some none).run h) := by
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.true_and, decide_eq_true_eq]
    split_ifs with ht' hth
    · simp only [StateT.run_pure]; exact GuardedSafePost.pure ⟨le_rfl, Nat.le_add_right _ _, rfl, fun _ _ _ _ h1 => by cases h1⟩
    · simp only [StateT.run_bind, StateT.run_pure]
      refine (lookupMultiF_safe hInl (cka.receive γ Tn).2 h).bind fun ⟨_, h1⟩ hh1 => ?_
      refine (regSessMulti_safe (cka.receive γ Tn).2 h1).bind fun ⟨idx, h2⟩ hh2 => ?_
      refine GuardedSafePost.pure ⟨by rw [← hh1.1]; exact hh2.2.1,
        by rw [← hh1.1]; exact hh2.2.2.1, by rw [hh2.2.2.2, hh1.2], fun _ _ rsv sIdx hres hrsv => ?_⟩
      injection hres with hsome; injection hsome with htuple; subst hrsv
      have hrsv_eq := (Prod.mk.inj (Prod.mk.inj htuple).2).2
      simp only [Sum.inr.injEq] at hrsv_eq; subst hrsv_eq; exact ⟨ht', hh2.1⟩
    · simp only [StateT.run_pure]; exact GuardedSafePost.pure ⟨le_rfl, Nat.le_add_right _ _, rfl, fun _ _ _ _ h1 => by cases h1⟩
  rcases hcache_eq : h.cache t' with _ | ⟨Tc, σc, k, optIdx⟩
  · exact hForgedBranch
  · by_cases hTc : Tc = Tn
    · simp only [hTc, ↓reduceIte, StateT.run_pure]
      refine GuardedSafePost.pure ⟨le_rfl, Nat.le_add_right _ _, rfl, fun _ _ rsv sIdx hres hrsv => ?_⟩
      injection hres with hsome; injection hsome with htuple; subst hrsv
      have hrsv_eq := (Prod.mk.inj (Prod.mk.inj htuple).2).2
      cases hopt : optIdx with
      | none => simp [hopt] at hrsv_eq
      | some idx =>
        simp only [hopt, Sum.inr.injEq] at hrsv_eq; subst hrsv_eq; rw [hopt] at hcache_eq
        exact hCache t' Tc σc k idx hcache_eq
    · simp only [hTc, ↓reduceIte]; exact hForgedBranch

local macro "close_fs_send_e" : tactic => `(tactic| (
  dsimp only; rw [hm_run_bind]
  refine (safeZero_liftFSMulti_query _ _ (by
    simp_all [badMultiQuery, sessOffRange, badEncMulti, outEpMulti, encBadMsg, queryADOutsideClass])
    _).bind fun ⟨e?, h_end⟩ hh_end => ?_
  dsimp only at hh_end ⊢; subst h_end; rcases e? with _ | e
  · simp only [StateT.run_pure]; exact GuardedSafePost.pure ⟨rfl, rfl, fun _ _ _ h1 => by cases h1⟩
  · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
    exact GuardedSafePost.pure ⟨rfl, rfl, fun v' _ _ h1 hv' => by
      injection h1 with h2; exact (Prod.mk.inj h2).1.trans hv'⟩))

private theorem hooksFSMulti_fsSend_safe
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party) (t' : ℕ) (ssv : SS ⊕ ℕ)
    (hdr : Header T) (m : M) (pair : Option (M × M)) (h : FSMultiState T RSt K I E)
    (hSsv : ∀ sIdx, ssv = .inr sIdx → hdr.1 = t ∧ sIdx < M_cap)
    (hMsgOk : match pair with | none => ok m = true | some (m₀, m₁) => ok m₀ = true ∧ ok m₁ = true) :
    SafeZero (fun x => badMultiQuery M_cap t ok x = true)
      (fun res => res.2.sessions = h.sessions ∧ res.2.cache = h.cache ∧
        (∀ v' e sIdx, res.1 = some (v', e) → v' = .inr sIdx → ssv = .inr sIdx))
      (((hooksFSMulti cka prng fs Δcka ⟨true, tL, t⟩ false la).fsSend ctx P t' ssv hdr m pair).run h) := by
  dsimp only [hooksFSMulti]; rcases ssv with ss | sIdx
  · simp only [StateT.run_pure]
    exact GuardedSafePost.pure ⟨rfl, rfl, fun v' _ _ h1 hv' => by
      injection h1 with h2; rw [← (Prod.mk.inj h2).1] at hv'; cases hv'⟩
  · rcases hSsv sIdx rfl with ⟨hhdr_t, hsIdx_lt⟩
    rw [hm_run_bind]; simp only [StateT.run_get, pure_bind]
    by_cases hneed : (!ctx.safeCh (2 + Δcka) P && !((h.book sIdx).getD {}).sCorr) = true
    · simp only [hneed, ↓reduceIte]; cases la
      · simp only [Bool.false_eq_true, ↓reduceIte]; rw [hm_run_bind]; unfold corruptSenderQuery
        refine (safeZero_liftFSMulti_query sIdx _ (by
          simp [badMultiQuery, sessOffRange, badEncMulti, outEpMulti, encBadMsg,
            queryADOutsideClass, hsIdx_lt]) h).bind fun ⟨o, h1⟩ hh1 => ?_
        dsimp only at hh1 ⊢; subst h1; rcases o with _ | _
        · simp only [Bool.not_false, ↓reduceIte, StateT.run_pure]
          exact GuardedSafePost.pure ⟨rfl, rfl, fun _ _ _ h1 => by cases h1⟩
        · simp only [StateT.run_bind, StateT.run_modify, pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          rcases pair with _ | ⟨m₀, m₁⟩
          · unfold transmitQuery; close_fs_send_e
          · unfold challengeQuery; close_fs_send_e
      · simp only [↓reduceIte, Bool.not_false, StateT.run_pure]
        exact GuardedSafePost.pure ⟨rfl, rfl, fun _ _ _ h1 => by cases h1⟩
    · simp only [hneed, Bool.false_eq_true, ↓reduceIte, Bool.not_true]
      rcases pair with _ | ⟨m₀, m₁⟩
      · unfold transmitQuery; close_fs_send_e
      · unfold challengeQuery; close_fs_send_e

local macro "close_fs_recv_q" rec_id:term : tactic => `(tactic| (
  rw [hm_run_bind]
  refine (safeZero_liftFSMulti_query _ _ (by
    simp_all [badMultiQuery, sessOffRange, badEncMulti, outEpMulti, encBadMsg, queryADOutsideClass])
    _).bind fun ⟨res, h2⟩ hh2 => ?_
  dsimp only at hh2 ⊢; subst h2; rcases res with _ | (_ | ⟨i, mo'⟩)
  · simp only [StateT.run_pure]; exact GuardedSafePost.pure ⟨rfl, rfl, fun _ _ _ _ h1 => by cases h1⟩
  · simp only [StateT.run_pure]; exact GuardedSafePost.pure ⟨rfl, rfl, fun _ _ _ _ h1 => by cases h1⟩
  · simp only [StateT.run_bind, StateT.run_get, pure_bind]; split_ifs
    · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
      exact GuardedSafePost.pure ⟨rfl, rfl, fun _ _ _ _ h1 => by cases h1⟩
    · simp only [StateT.run_bind, StateT.run_modify, pure_bind]
      rcases mo' with _ | m' <;> rcases ($rec_id : Option _) with _ | r <;> simp only [StateT.run_pure]
      · exact GuardedSafePost.pure ⟨rfl, rfl, fun _ _ _ _ h1 => by cases h1⟩
      all_goals exact GuardedSafePost.pure ⟨rfl, rfl, fun v' _ _ _ h1 hv' => by
        injection h1 with h2; injection h2 with h3; exact (Prod.mk.inj h3).1.trans hv'⟩))

private theorem hooksFSMulti_fsRecv_safe
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party) (t0 : ℕ) (rsv : RS ⊕ ℕ)
    (hdr : Header T) (e : E) (rec : Option (Record M (Header T × E))) (h : FSMultiState T RSt K I E)
    (hRsv : ∀ sIdx, rsv = .inr sIdx → hdr.1 = t ∧ sIdx < M_cap) :
    SafeZero (fun x => badMultiQuery M_cap t ok x = true)
      (fun res => res.2.sessions = h.sessions ∧ res.2.cache = h.cache ∧
        (∀ v' i m' sIdx, res.1 = some (some (v', i, m')) → v' = .inr sIdx → rsv = .inr sIdx))
      (((hooksFSMulti cka prng fs Δcka ⟨true, tL, t⟩ false la).fsRecv ctx P t0 rsv hdr e rec).run h) := by
  dsimp only [hooksFSMulti]; rcases rsv with rs | sIdx
  · simp only [StateT.run_pure]
    refine GuardedSafePost.pure ⟨rfl, rfl, fun v' _ _ _ h1 hv' => ?_⟩
    rcases hrcv : fs.receive rs hdr e with _ | o
    · simp [hrcv] at h1
    · simp only [hrcv, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1; rw [← h1.1] at hv'; cases hv'
  · rcases hRsv sIdx rfl with ⟨hhdr_t, hsIdx_lt⟩
    rw [hm_run_bind]; simp only [StateT.run_get, pure_bind]
    set matched := ((h.book sIdx).getD {}).fsTrans.find? (fun x => x.2 == (hdr, e))
    by_cases hneed : (matched.isNone && !_root_.CryptoGames.SM.healedBy ctx.tL (2 + Δcka) t0 &&
        !((h.book sIdx).getD {}).sCorr) = true
    · simp only [hneed, ↓reduceIte]; cases la
      · simp only [Bool.false_eq_true, ↓reduceIte]; rw [hm_run_bind]; unfold corruptSenderQuery
        refine (safeZero_liftFSMulti_query sIdx _ (by
          simp [badMultiQuery, sessOffRange, badEncMulti, outEpMulti, encBadMsg,
            queryADOutsideClass, hsIdx_lt]) h).bind fun ⟨o, h1⟩ hh1 => ?_
        dsimp only at hh1 ⊢; subst h1; rcases o with _ | _
        · simp only [Bool.not_false, ↓reduceIte, StateT.run_pure]
          exact GuardedSafePost.pure ⟨rfl, rfl, fun _ _ _ _ h1 => by cases h1⟩
        · simp only [StateT.run_bind, StateT.run_modify, pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          by_cases hmat : matched.isSome = true
          · simp only [hmat, ↓reduceIte]; unfold deliverQuery; close_fs_recv_q rec
          · simp only [hmat, Bool.false_eq_true, ↓reduceIte]; unfold injectQuery; close_fs_recv_q rec
      · simp only [↓reduceIte, Bool.not_false, StateT.run_pure]
        exact GuardedSafePost.pure ⟨rfl, rfl, fun _ _ _ _ h1 => by cases h1⟩
    · simp only [hneed, Bool.false_eq_true, ↓reduceIte, Bool.not_true]
      by_cases hmat : matched.isSome = true
      · simp only [hmat, ↓reduceIte]; unfold deliverQuery; close_fs_recv_q rec
      · simp only [hmat, Bool.false_eq_true, ↓reduceIte]; unfold injectQuery; close_fs_recv_q rec

private theorem hooksFSMulti_reveal_safe
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (vp : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) (h : FSMultiState T RSt K I E)
    (hVsLt : ∀ sIdx, vp.vS = some (.inr sIdx) → sIdx < M_cap) :
    SafeZero (fun x => badMultiQuery M_cap t ok x = true)
      (fun res => res.2.sessions = h.sessions ∧ res.2.cache = h.cache)
      (((hooksFSMulti cka prng fs Δcka ⟨true, tL, t⟩ false la).reveal ctx P vp).run h) := by
  dsimp only [hooksFSMulti]
  rcases hvs : vp.vS with _ | (ss | sIdx)
  · simp only [pure_bind]
    split_ifs <;> simp only [StateT.run_pure] <;> exact GuardedSafePost.pure ⟨rfl, rfl⟩
  · simp only [pure_bind]
    split_ifs <;> simp only [StateT.run_pure] <;> exact GuardedSafePost.pure ⟨rfl, rfl⟩
  · cases la
    · simp only [Bool.false_eq_true, ↓reduceIte]; rw [hm_run_bind]
      unfold corruptSenderQuery
      refine (safeZero_liftFSMulti_query sIdx _ (by
        simp [badMultiQuery, sessOffRange, badEncMulti, outEpMulti, encBadMsg, queryADOutsideClass]
        exact hVsLt sIdx hvs) h).bind
        fun ⟨o, h1⟩ hh1 => ?_
      dsimp only at hh1 ⊢; subst hh1; rcases o with _ | _
      · simp only [pure_bind, StateT.run_pure]; exact GuardedSafePost.pure ⟨rfl, rfl⟩
      · simp only [StateT.run_bind, StateT.run_modify, pure_bind]
        split_ifs <;> simp only [StateT.run_pure] <;> exact GuardedSafePost.pure ⟨rfl, rfl⟩
    · simp only [↓reduceIte, pure_bind, StateT.run_pure]
      exact GuardedSafePost.pure ⟨rfl, rfl⟩

/-! ## 4. Engine Step Lemmas (`vSend`, `vRecv`, `commitE`, and `implEDFPaper`) -/

private theorem vSend_paperMulti_safe
    (rem' : ℕ)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E))
    (hInv : PaperMultiInv t M_cap (rem' + 1) es)
    (s₁ : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (hs₁ : s₁.st = es.g.st)
    (P : Party) (m : M) (pair : Option (M × M)) (r : Option CCoins)
    (hMsgOk : match pair with | none => ok m = true | some (m₀, m₁) => ok m₀ = true ∧ ok m₁ = true) :
    SafeZero (fun x => badMultiQuery M_cap t ok x = true)
      (fun res =>
        res.2.h.sessions.length + rem' ≤ M_cap ∧
        (∀ τ Tc σc k sIdx,
          res.2.h.cache τ = some (Tc, σc, k, some sIdx) → τ = t ∧ sIdx < res.2.h.sessions.length) ∧
        es.h.sessions.length ≤ res.2.h.sessions.length ∧
        res.2.g = es.g ∧
        (∀ st' c, res.1 = some (st', c) →
          st'.id = P ∧
          (∀ sIdx, P.sendsIn st'.tcur = true → st'.vS = some (.inr sIdx) → st'.tcur = t) ∧
          (∀ sIdx, st'.vS = some (.inr sIdx) → sIdx < res.2.h.sessions.length) ∧
          st'.vR = (es.g.st P).vR))
      ((liftH (vSend (hooksFSMulti cka prng fs Δcka ⟨true, tL, t⟩ false la)
        s₁ P (s₁.st P) m pair r)).run es) := by
  rw [liftH_run]
  unfold vSend
  rw [hs₁]
  set vp := es.g.st P
  have hvp_id : vp.id = P := hInv.id_eq P
  by_cases hsends : vp.id.sendsIn (vp.tcur + 1) = true
  · simp only [hsends, ↓reduceIte]; rw [hm_run_bind, bind_assoc]
    refine (hooksFSMulti_startSend_safe cka prng fs Δcka M_cap tL t la ok s₁ P
      (vp.tcur + 1) vp.γ vp.root r es.h hInv.cache_ok).bind fun ⟨o, h1⟩ hh1 => ?_
    dsimp only at hh1 ⊢
    have h1_len_M : h1.sessions.length + rem' ≤ M_cap := by
      have := hInv.len_le; have := hh1.2.1; omega
    rcases o with _ | ⟨γ', T', σ', ss⟩
    · simp only [pure_bind, StateT.run_pure]
      exact GuardedSafePost.pure ⟨h1_len_M, hh1.2.2.1, hh1.1, rfl, fun _ _ h1 => by cases h1⟩
    · simp only [pure_bind]
      rw [hm_run_bind, bind_assoc]
      have hv_ok : ∀ sIdx, ss = .inr sIdx → (vp.tcur + 1, some T').1 = t ∧ sIdx < M_cap := by
        intro sIdx hss
        rcases hh1.2.2.2 γ' T' σ' ss sIdx rfl hss with ⟨htcur, hlt⟩
        exact ⟨htcur, by omega⟩
      refine (hooksFSMulti_fsSend_safe cka prng fs Δcka M_cap tL t la ok s₁ P (vp.tcur + 1) ss
        (vp.tcur + 1, some T') m pair h1 hv_ok hMsgOk).bind fun ⟨fe?, h2⟩ hh2 => ?_
      dsimp only at hh2 ⊢
      have h2_len_M : h2.sessions.length + rem' ≤ M_cap := by rw [hh2.1]; exact h1_len_M
      have h2_cache : ∀ τ Tc σc k sIdx,
          h2.cache τ = some (Tc, σc, k, some sIdx) → τ = t ∧ sIdx < h2.sessions.length := by
        intro τ Tc σc k sIdx hc; rw [hh2.2.1] at hc; rw [hh2.1]
        exact hh1.2.2.1 τ Tc σc k sIdx hc
      have h2_mono : es.h.sessions.length ≤ h2.sessions.length := by rw [hh2.1]; exact hh1.1
      rcases fe? with _ | ⟨v', e⟩
      · simp only [StateT.run_pure, pure_bind]
        exact GuardedSafePost.pure ⟨h2_len_M, h2_cache, h2_mono, rfl, fun _ _ h1 => by cases h1⟩
      · simp only [StateT.run_pure, pure_bind]
        refine GuardedSafePost.pure ⟨h2_len_M, h2_cache, h2_mono, rfl, fun st' _ hres => ?_⟩
        injection hres with hpair; rcases Prod.mk.inj hpair with ⟨hst', _⟩; subst hst'
        refine ⟨hvp_id, ?_, ?_, rfl⟩
        · intro sIdx _ hv'; injection hv' with hv''
          exact (hh1.2.2.2 γ' T' σ' ss sIdx rfl (hh2.2.2 v' e sIdx rfl hv'')).1
        · intro sIdx hv'; injection hv' with hv''
          rw [hh2.1]; exact (hh1.2.2.2 γ' T' σ' ss sIdx rfl (hh2.2.2 v' e sIdx rfl hv'')).2
  · simp only [hsends, Bool.false_eq_true, ↓reduceIte, pure_bind]
    have hsends_cur : P.sendsIn vp.tcur = true := by
      apply sendsIn_of_succ_false; rw [← hvp_id]
      cases hs : vp.id.sendsIn (vp.tcur + 1) <;> simp_all
    have h0_len_M : es.h.sessions.length + rem' ≤ M_cap := by have := hInv.len_le; omega
    rcases hvs_eq : vp.vS with _ | v
    · simp only [StateT.run_pure, pure_bind]
      refine GuardedSafePost.pure ⟨h0_len_M, hInv.cache_ok, le_rfl, rfl, fun st' _ hres => ?_⟩
      injection hres with hpair; rcases Prod.mk.inj hpair with ⟨hst', _⟩; subst hst'
      exact ⟨hvp_id, (by intro _ _ hv; rw [hvs_eq] at hv; cases hv),
        (by intro _ hv; rw [hvs_eq] at hv; cases hv), rfl⟩
    · rw [hm_run_bind, bind_assoc]
      have hv_ok : ∀ sIdx, v = .inr sIdx → (vp.tcur, vp.curCkaMsg).1 = t ∧ sIdx < M_cap := by
        intro sIdx hv; subst hv
        exact ⟨hInv.vs_ep P sIdx hsends_cur hvs_eq, by have := hInv.vs_lt P sIdx hvs_eq; omega⟩
      refine (hooksFSMulti_fsSend_safe cka prng fs Δcka M_cap tL t la ok s₁ P vp.tcur v
        (vp.tcur, vp.curCkaMsg) m pair es.h hv_ok hMsgOk).bind fun ⟨fe?, h2⟩ hh2 => ?_
      dsimp only at hh2 ⊢
      have h2_len_M : h2.sessions.length + rem' ≤ M_cap := by rw [hh2.1]; exact h0_len_M
      have h2_cache : ∀ τ Tc σc k sIdx,
          h2.cache τ = some (Tc, σc, k, some sIdx) → τ = t ∧ sIdx < h2.sessions.length := by
        intro τ Tc σc k sIdx hc; rw [hh2.2.1] at hc; rw [hh2.1]
        exact hInv.cache_ok τ Tc σc k sIdx hc
      have h2_mono : es.h.sessions.length ≤ h2.sessions.length := by rw [hh2.1]
      rcases fe? with _ | ⟨v', e⟩
      · simp only [StateT.run_pure, pure_bind]
        exact GuardedSafePost.pure ⟨h2_len_M, h2_cache, h2_mono, rfl, fun _ _ h1 => by cases h1⟩
      · simp only [StateT.run_pure, pure_bind]
        refine GuardedSafePost.pure ⟨h2_len_M, h2_cache, h2_mono, rfl, fun st' _ hres => ?_⟩
        injection hres with hpair; rcases Prod.mk.inj hpair with ⟨hst', _⟩; subst hst'
        refine ⟨hvp_id, ?_, ?_, rfl⟩
        · intro sIdx _ hv'; injection hv' with hv''
          rw [hh2.2.2 v' e sIdx rfl hv''] at hvs_eq; exact hInv.vs_ep P sIdx hsends_cur hvs_eq
        · intro sIdx hv'; injection hv' with hv''
          rw [hh2.2.2 v' e sIdx rfl hv''] at hvs_eq; rw [hh2.1]; exact hInv.vs_lt P sIdx hvs_eq

private theorem vRecv_paperMulti_safe
    (rem' : ℕ)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E))
    (hInv : PaperMultiInv t M_cap (rem' + 1) es)
    (P : Party) (ct : Header T × E) (rec : Option (Record M (Header T × E))) :
    SafeZero (fun x => badMultiQuery M_cap t ok x = true)
      (fun res =>
        res.2.h.sessions.length + rem' ≤ M_cap ∧
        (∀ τ Tc σc k sIdx,
          res.2.h.cache τ = some (Tc, σc, k, some sIdx) → τ = t ∧ sIdx < res.2.h.sessions.length) ∧
        es.h.sessions.length ≤ res.2.h.sessions.length ∧
        res.2.g = es.g ∧
        (∀ st' t' i' m', res.1 = some (some (st', t', i', m')) →
          st'.id = P ∧
          (∀ sIdx, P.sendsIn st'.tcur = true → st'.vS = some (.inr sIdx) → st'.tcur = t) ∧
          (∀ sIdx, st'.vS = some (.inr sIdx) → sIdx < res.2.h.sessions.length) ∧
          (∀ τ sIdx, st'.vR τ = some (.inr sIdx) → τ = t ∧ sIdx < res.2.h.sessions.length)))
      ((liftH (vRecv (hooksFSMulti cka prng fs Δcka ⟨true, tL, t⟩ false la)
        es.g P (es.g.st P) ct rec)).run es) := by
  rw [liftH_run]
  unfold vRecv
  set vp := es.g.st P
  have hvp_id : vp.id = P := hInv.id_eq P
  by_cases hguard : (vp.id.sendsIn ct.1.1 || decide (vp.tcur + 1 < ct.1.1)) = true
  · simp only [hguard, ↓reduceIte, StateT.run_pure, pure_bind]
    exact GuardedSafePost.pure ⟨by dsimp only; have := hInv.len_le; omega, hInv.cache_ok, le_rfl, rfl,
      fun _ _ _ _ h1 => by cases h1⟩
  · have hnot_sends : P.sendsIn ct.1.1 = false := by
      rw [← hvp_id]; cases hs : vp.id.sendsIn ct.1.1 <;> simp_all
    have h0_len_M : es.h.sessions.length + rem' ≤ M_cap := by have := hInv.len_le; omega
    simp only [hguard, Bool.false_eq_true, ↓reduceIte]
    by_cases ht1 : ct.1.1 = vp.tcur + 1
    · simp only [ht1, ↓reduceIte]
      rcases hc2 : ct.1.2 with _ | Tn
      · simp only [pure_bind, StateT.run_pure]
        exact GuardedSafePost.pure ⟨h0_len_M, hInv.cache_ok, le_rfl, rfl, fun _ _ _ _ h1 => by cases h1⟩
      · dsimp only; rw [hm_run_bind, bind_assoc]
        refine (hooksFSMulti_startRecv_safe cka prng fs Δcka M_cap tL t la ok es.g P
          (vp.tcur + 1) vp.γ vp.root Tn es.h hInv.cache_ok).bind fun ⟨sr?, h1⟩ hh1 => ?_
        dsimp only at hh1 ⊢
        have h1_len_M : h1.sessions.length + rem' ≤ M_cap := by
          have := hInv.len_le; have := hh1.2.1; omega
        have h1_cache : ∀ τ Tc σc k sIdx,
            h1.cache τ = some (Tc, σc, k, some sIdx) → τ = t ∧ sIdx < h1.sessions.length := by
          intro τ Tc σc k sIdx hc; rw [hh1.2.2.1] at hc
          exact ⟨(hInv.cache_ok τ Tc σc k sIdx hc).1,
            Nat.lt_of_lt_of_le (hInv.cache_ok τ Tc σc k sIdx hc).2 hh1.1⟩
        rcases sr? with _ | (_ | ⟨γ', σ', rs⟩)
        · simp only [pure_bind, StateT.run_pure]
          exact GuardedSafePost.pure ⟨h1_len_M, h1_cache, hh1.1, rfl, fun _ _ _ _ h1 => by cases h1⟩
        · simp only [pure_bind, StateT.run_pure]
          exact GuardedSafePost.pure ⟨h1_len_M, h1_cache, hh1.1, rfl, fun _ _ _ _ h1 => by cases h1⟩
        · simp only [pure_bind, Function.update_self]
          rw [hm_run_bind, bind_assoc]
          have hv_ok : ∀ sIdx, rs = .inr sIdx → ct.1.1 = t ∧ sIdx < M_cap := by
            intro sIdx hrs
            rcases hh1.2.2.2 γ' σ' rs sIdx rfl hrs with ⟨ht_eq, hlt⟩
            exact ⟨by rw [ht1, ht_eq], by omega⟩
          refine (hooksFSMulti_fsRecv_safe cka prng fs Δcka M_cap tL t la ok es.g P (vp.tcur + 1) rs
            ct.1 ct.2 rec h1 hv_ok).bind fun ⟨fr?, h2⟩ hh2 => ?_
          dsimp only at hh2 ⊢
          have h2_len_M : h2.sessions.length + rem' ≤ M_cap := by rw [hh2.1]; exact h1_len_M
          have h2_cache : ∀ τ Tc σc k sIdx,
              h2.cache τ = some (Tc, σc, k, some sIdx) → τ = t ∧ sIdx < h2.sessions.length := by
            intro τ Tc σc k sIdx hc; rw [hh2.2.1] at hc; rw [hh2.1]
            exact h1_cache τ Tc σc k sIdx hc
          have h2_mono : es.h.sessions.length ≤ h2.sessions.length := by rw [hh2.1]; exact hh1.1
          rcases fr? with _ | (_ | ⟨v', i', m'⟩)
          · simp only [StateT.run_pure, pure_bind]
            exact GuardedSafePost.pure ⟨h2_len_M, h2_cache, h2_mono, rfl, fun _ _ _ _ h1 => by cases h1⟩
          · simp only [StateT.run_pure, pure_bind]
            exact GuardedSafePost.pure ⟨h2_len_M, h2_cache, h2_mono, rfl, fun _ _ _ _ h1 => by cases h1⟩
          · simp only [StateT.run_pure, pure_bind]
            refine GuardedSafePost.pure ⟨h2_len_M, h2_cache, h2_mono, rfl, fun st' _ _ _ hres => ?_⟩
            injection hres with hres1; injection hres1 with htuple
            rcases Prod.mk.inj htuple with ⟨hst', _⟩; subst hst'
            refine ⟨hvp_id,
              (fun _ hsends_sm _ => by rw [← ht1, hnot_sends] at hsends_sm; cases hsends_sm),
              (fun sIdx hvs => by rw [hh2.1]; exact Nat.lt_of_lt_of_le (hInv.vs_lt P sIdx hvs) hh1.1),
              fun τ sIdx hvr' => ?_⟩
            by_cases hτ : τ = vp.tcur + 1
            · subst hτ; simp only [Function.update_self, Option.some.injEq] at hvr'
              rw [hh2.1]; exact hh1.2.2.2 γ' σ' rs sIdx rfl (hh2.2.2 v' i' m' sIdx rfl hvr')
            · simp only [Function.update_of_ne hτ] at hvr'
              rw [hh2.1]
              exact ⟨(hInv.vr_ok P τ sIdx hvr').1, Nat.lt_of_lt_of_le (hInv.vr_ok P τ sIdx hvr').2 hh1.1⟩
    · simp only [ht1, ↓reduceIte, pure_bind]
      rcases hvr_eq : vp.vR ct.1.1 with _ | v
      · simp only [StateT.run_pure, pure_bind]
        exact GuardedSafePost.pure ⟨h0_len_M, hInv.cache_ok, le_rfl, rfl, fun _ _ _ _ h1 => by cases h1⟩
      · rw [hm_run_bind, bind_assoc]
        have hv_ok : ∀ sIdx, v = .inr sIdx → ct.1.1 = t ∧ sIdx < M_cap := by
          intro sIdx hv; subst hv
          rcases hInv.vr_ok P ct.1.1 sIdx hvr_eq with ⟨ht_eq, hlt⟩; exact ⟨ht_eq, by omega⟩
        refine (hooksFSMulti_fsRecv_safe cka prng fs Δcka M_cap tL t la ok es.g P ct.1.1 v
          ct.1 ct.2 rec es.h hv_ok).bind fun ⟨fr?, h2⟩ hh2 => ?_
        dsimp only at hh2 ⊢
        have h2_len_M : h2.sessions.length + rem' ≤ M_cap := by rw [hh2.1]; exact h0_len_M
        have h2_cache : ∀ τ Tc σc k sIdx,
            h2.cache τ = some (Tc, σc, k, some sIdx) → τ = t ∧ sIdx < h2.sessions.length := by
          intro τ Tc σc k sIdx hc; rw [hh2.2.1] at hc; rw [hh2.1]
          exact hInv.cache_ok τ Tc σc k sIdx hc
        have h2_mono : es.h.sessions.length ≤ h2.sessions.length := by rw [hh2.1]
        rcases fr? with _ | (_ | ⟨v', i', m'⟩)
        · simp only [StateT.run_pure, pure_bind]
          exact GuardedSafePost.pure ⟨h2_len_M, h2_cache, h2_mono, rfl, fun _ _ _ _ h1 => by cases h1⟩
        · simp only [StateT.run_pure, pure_bind]
          exact GuardedSafePost.pure ⟨h2_len_M, h2_cache, h2_mono, rfl, fun _ _ _ _ h1 => by cases h1⟩
        · simp only [StateT.run_pure, pure_bind]
          refine GuardedSafePost.pure ⟨h2_len_M, h2_cache, h2_mono, rfl, fun st' _ _ _ hres => ?_⟩
          injection hres with hres1; injection hres1 with htuple
          rcases Prod.mk.inj htuple with ⟨hst', _⟩; subst hst'
          refine ⟨hvp_id, hInv.vs_ep P, fun sIdx hvs => by rw [hh2.1]; exact hInv.vs_lt P sIdx hvs, ?_⟩
          intro τ sIdx hvr'
          by_cases hτ : τ = ct.1.1
          · subst τ; simp only [Function.update_self, Option.some.injEq] at hvr'
            rw [hh2.2.2 v' i' m' sIdx rfl hvr'] at hvr_eq; rw [hh2.1]; exact hInv.vr_ok P ct.1.1 sIdx hvr_eq
          · simp only [Function.update_of_ne hτ] at hvr'; rw [hh2.1]; exact hInv.vr_ok P τ sIdx hvr'

private theorem commitE_paperMulti_safe
    (s : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (old st' : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) (pos : Pos)
    (es₁ : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E)) :
    SafeZero (fun x => badMultiQuery M_cap t ok x = true)
      (fun res => res.2 = es₁ ∧ ∀ s₁, res.1 = some s₁ → s₁.st = Function.update s.st P st')
      ((commitE (hooksFSMulti cka prng fs Δcka ⟨true, tL, t⟩ false la) s P old st' pos).run es₁) := by
  unfold commitE liftH; dsimp only [hooksFSMulti]
  simp only [StateT.run_bind, StateT.run_pure, pure_bind]
  refine GuardedSafePost.pure ⟨rfl, fun s₁ hs₁ => ?_⟩
  injection hs₁ with hs₁'; subst hs₁'
  funext Q; by_cases hQ : Q = P
  · subst hQ; simp [GameState.accept, GameState.delete]
  · simp [GameState.accept, GameState.delete, hQ]

end FixedHooks

private theorem update_party_inv
    {t M_cap rem' : ℕ}
    {es es₁ : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E)}
    (hInv : PaperMultiInv t M_cap (rem' + 1) es)
    (hlen : es₁.h.sessions.length + rem' ≤ M_cap)
    (hcache : ∀ τ Tc σc k sIdx,
      es₁.h.cache τ = some (Tc, σc, k, some sIdx) → τ = t ∧ sIdx < es₁.h.sessions.length)
    (hmono : es.h.sessions.length ≤ es₁.h.sessions.length)
    {g' : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E} (P : Party)
    {st' : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)}
    (hg' : g'.st = Function.update es.g.st P st')
    (hid : st'.id = P)
    (hvs_ep : ∀ sIdx, P.sendsIn st'.tcur = true → st'.vS = some (.inr sIdx) → st'.tcur = t)
    (hvs_lt : ∀ sIdx, st'.vS = some (.inr sIdx) → sIdx < es₁.h.sessions.length)
    (hvr : ∀ τ sIdx, st'.vR τ = some (.inr sIdx) → τ = t ∧ sIdx < es₁.h.sessions.length) :
    PaperMultiInv t M_cap rem' { es₁ with g := g' } :=
  { len_le := hlen
    id_eq := fun Q => by
      rw [hg']; by_cases hQ : Q = P
      · subst hQ; simp [Function.update_self, hid]
      · simp [Function.update_of_ne hQ, hInv.id_eq Q]
    cache_ok := hcache
    vs_ep := fun Q sIdx hs hv => by
      dsimp only at hs hv ⊢; rw [hg'] at hs hv ⊢; by_cases hQ : Q = P
      · subst hQ; simp only [Function.update_self] at hs hv ⊢; exact hvs_ep sIdx hs hv
      · simp only [Function.update_of_ne hQ] at hs hv ⊢; exact hInv.vs_ep Q sIdx hs hv
    vs_lt := fun Q sIdx hv => by
      dsimp only at hv; rw [hg'] at hv; by_cases hQ : Q = P
      · subst hQ; simp only [Function.update_self] at hv; exact hvs_lt sIdx hv
      · simp only [Function.update_of_ne hQ] at hv
        exact Nat.lt_of_lt_of_le (hInv.vs_lt Q sIdx hv) hmono
    vr_ok := fun Q τ sIdx hv => by
      dsimp only at hv; rw [hg'] at hv; by_cases hQ : Q = P
      · subst hQ; simp only [Function.update_self] at hv; exact hvr τ sIdx hv
      · simp only [Function.update_of_ne hQ] at hv
        exact ⟨(hInv.vr_ok Q τ sIdx hv).1, Nat.lt_of_lt_of_le (hInv.vr_ok Q τ sIdx hv).2 hmono⟩ }

private theorem PaperMultiInv.of_vRecv_step
    {t M_cap rem' : ℕ}
    {es es₁ : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E)}
    (hInv : PaperMultiInv t M_cap (rem' + 1) es)
    (hlen : es₁.h.sessions.length + rem' ≤ M_cap)
    (hcache : ∀ τ Tc σc k sIdx,
      es₁.h.cache τ = some (Tc, σc, k, some sIdx) → τ = t ∧ sIdx < es₁.h.sessions.length)
    (hmono : es.h.sessions.length ≤ es₁.h.sessions.length)
    (hg : es₁.g = es.g) :
    PaperMultiInv t M_cap rem' es₁ :=
  { len_le := hlen
    id_eq := fun P => by rw [hg]; exact hInv.id_eq P
    cache_ok := hcache
    vs_ep := fun P sIdx hs hv => by rw [hg] at hs hv ⊢; exact hInv.vs_ep P sIdx hs hv
    vs_lt := fun Q sIdx hv => by rw [hg] at hv; exact Nat.lt_of_lt_of_le (hInv.vs_lt Q sIdx hv) hmono
    vr_ok := fun Q τ sIdx hv => by
      rw [hg] at hv
      exact ⟨(hInv.vr_ok Q τ sIdx hv).1, Nat.lt_of_lt_of_le (hInv.vr_ok Q τ sIdx hv).2 hmono⟩ }

private theorem coinsE_paperMulti_safe
    (M_cap rem t : ℕ) (ok : M → Bool) (u : unifSpec.Domain)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E))
    (hInv : PaperMultiInv t M_cap rem es) :
    SafeZero (fun x => badMultiQuery M_cap t ok x = true)
      (fun r => PaperMultiInv t M_cap rem r.2)
      ((coinsE (tspec := FSMultiSpec SS RS T M E) u).run es) := by
  unfold coinsE; rw [StateT.run_lift]
  exact GuardedSafePost.query_bind (badMultiQuery_inl_false M_cap t ok u)
    fun _ _ => GuardedSafePost.pure hInv

private theorem implEDFPaper_inr_paperMulti_safe
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep M_cap rem' : ℕ) (tL : Option ℕ) (t : ℕ) (la : Bool)
    {ok₀ ok : M → Bool} (hok : ∀ m, ok₀ m = true → ok m = true)
    (qr : (specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (hqr_sh : badSendMsgDF (St := PartyState Γ T RSt SS RS) (Coins := CCoins)
      (C := Header T × E) ok₀ (.inr qr) = false)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E))
    (hInv : PaperMultiInv t M_cap (rem' + 1) es) :
    SafeZero (fun x => badMultiQuery M_cap t ok x = true)
      (fun r => PaperMultiInv t M_cap rem' r.2)
      ((implEDFPaper (hooksFSMulti cka prng fs Δcka ⟨true, tL, t⟩ false la)
        (2 + Δcka) qep fs.maxSkip (⟨true, tL, t⟩ : Mode).cfg (⟨true, tL, t⟩ : Mode).policy
        (.inr qr)).run es) := by
  have hInv' : PaperMultiInv t M_cap rem' es := hInv.mono_rem (Nat.le_succ rem')
  rcases qr with (((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩)
  · -- 1. `transmitE`
    have hm_ok : ok m = true := hok m (by simpa [badSendMsgDF] using hqr_sh)
    change SafeZero _ _ ((transmitE _ _ _ _ (P, m, r)).run es)
    unfold transmitE; simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · simp only [StateT.run_pure]; exact GuardedSafePost.pure hInv'
    · cases hep : es.g.epMgmt (2 + Δcka) qep P r.isSome with
      | none => simp only [StateT.run_pure]; exact GuardedSafePost.pure hInv'
      | some s₁ =>
        dsimp only; split_ifs
        · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
          exact GuardedSafePost.pure (hInv'.with_g_same_st rfl)
        · simp only [StateT.run_bind]
          have hs₁_st := epMgmt_st es.g (2 + Δcka) qep P r.isSome hep
          refine (vSend_paperMulti_safe cka prng fs Δcka M_cap tL t la ok rem' es hInv s₁ hs₁_st
            P m none r hm_ok).bind fun ⟨out, es₁⟩ h1 => ?_
          dsimp only at h1
          rcases out with _ | ⟨st', ct⟩
          · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
            exact GuardedSafePost.pure
              ((hInv.of_vRecv_step h1.1 h1.2.1 h1.2.2.1 h1.2.2.2.1).with_g_same_st rfl)
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
            rcases h1.2.2.2.2 st' ct rfl with ⟨hid, hvs_ep, hvs_lt, hvr_eq⟩
            refine GuardedSafePost.pure
              (update_party_inv hInv h1.1 h1.2.1 h1.2.2.1 P
                (by simp [GameState.record, hs₁_st]) hid hvs_ep hvs_lt fun τ sIdx hv => ?_)
            rw [hvr_eq] at hv
            exact ⟨(hInv.vr_ok P τ sIdx hv).1, Nat.lt_of_lt_of_le (hInv.vr_ok P τ sIdx hv).2 h1.2.2.1⟩
  · -- 2. `challE`
    have hm01_ok : ok m₀ = true ∧ ok m₁ = true := by
      simp only [badSendMsgDF, Bool.or_eq_false_iff, Bool.not_eq_false'] at hqr_sh
      exact ⟨hok m₀ hqr_sh.1, hok m₁ hqr_sh.2⟩
    change SafeZero _ _ ((challE _ _ _ _ _ (P, m₀, m₁, r)).run es)
    unfold challE; simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win) = true
    · simp only [hab, ↓reduceIte, StateT.run_pure]; exact GuardedSafePost.pure hInv'
    · simp only [hab, Bool.false_eq_true, ↓reduceIte]
      cases hep : es.g.epMgmt (2 + Δcka) qep P r.isSome with
      | none => simp only [StateT.run_pure]; exact GuardedSafePost.pure hInv'
      | some s₁ =>
        dsimp only
        by_cases hch1 : (!(s₁.safeCh (2 + Δcka) P) || !((Mode.cfg (M := M) ⟨true, tL, t⟩).challAllowedIn (s₁.epoch P))) = true
        · simp only [hch1, ↓reduceIte, StateT.run_pure]; exact GuardedSafePost.pure hInv'
        · simp only [hch1, Bool.false_eq_true, ↓reduceIte]
          by_cases hch2 : (⟨true, tL, t⟩ : Mode).policy.leakDoom es.g s₁ = true
          · simp only [hch2, ↓reduceIte, abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
            exact GuardedSafePost.pure (hInv'.with_g_same_st rfl)
          · simp only [hch2, Bool.false_eq_true, ↓reduceIte]; rw [hm_run_bind]
            have hs₁_st := epMgmt_st es.g (2 + Δcka) qep P r.isSome hep
            refine (vSend_paperMulti_safe cka prng fs Δcka M_cap tL t la ok rem' es hInv s₁ hs₁_st
              P _ (some (m₀, m₁)) r hm01_ok).bind fun ⟨out, es₁⟩ h1 => ?_
            dsimp only at h1
            rcases out with _ | ⟨st', ct⟩
            · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
              exact GuardedSafePost.pure
                ((hInv.of_vRecv_step h1.1 h1.2.1 h1.2.2.1 h1.2.2.2.1).with_g_same_st rfl)
            · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
              rcases h1.2.2.2.2 st' ct rfl with ⟨hid, hvs_ep, hvs_lt, hvr_eq⟩
              refine GuardedSafePost.pure
                (update_party_inv hInv h1.1 h1.2.1 h1.2.2.1 P
                  (by simp [GameState.record, hs₁_st]) hid hvs_ep hvs_lt fun τ sIdx hv => ?_)
              rw [hvr_eq] at hv
              exact ⟨(hInv.vr_ok P τ sIdx hv).1, Nat.lt_of_lt_of_le (hInv.vr_ok P τ sIdx hv).2 h1.2.2.1⟩
  · -- 3. `deliverE`
    change SafeZero _ _ ((deliverE _ _ _ (P, c)).run es)
    unfold deliverE; simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · simp only [StateT.run_pure]; exact GuardedSafePost.pure hInv'
    · cases es.g.inTransit P.other c with
      | none => simp only [StateT.run_pure]; exact GuardedSafePost.pure hInv'
      | some rec =>
        dsimp only; simp only [StateT.run_bind]
        refine (vRecv_paperMulti_safe cka prng fs Δcka M_cap tL t la ok rem' es hInv P c (some rec)).bind
          fun ⟨out, es₁⟩ h1 => ?_
        dsimp only at h1
        have hes₁_inv : PaperMultiInv t M_cap rem' es₁ := hInv.of_vRecv_step h1.1 h1.2.1 h1.2.2.1 h1.2.2.2.1
        rcases out with _ | (_ | ⟨st', t', i', m'⟩)
        · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
          exact GuardedSafePost.pure (hes₁_inv.with_g_same_st rfl)
        · dsimp only; split_ifs
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
            exact GuardedSafePost.pure (hes₁_inv.with_g_same_st rfl)
          · simp only [StateT.run_pure]
            exact GuardedSafePost.pure hes₁_inv
        · simp only [StateT.run_bind]
          rcases h1.2.2.2.2 st' t' i' m' rfl with ⟨hid, hvs_ep, hvs_lt, hvr⟩
          refine (commitE_paperMulti_safe cka prng fs Δcka M_cap tL t la ok es.g P
            (es.g.st P) st' rec.pos es₁).bind fun ⟨s₁?, es₂⟩ h2 => ?_
          dsimp only at h2
          rcases h2 with ⟨rfl, h2⟩; rcases s₁? with _ | s₁
          · simp only [StateT.run_pure]; exact GuardedSafePost.pure hes₁_inv
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
            exact GuardedSafePost.pure
              (update_party_inv hInv h1.1 h1.2.1 h1.2.2.1 P
                (by split_ifs <;> simp [h2 s₁ rfl]) hid hvs_ep hvs_lt hvr)
  · -- 4. `injectE`
    change SafeZero _ _ ((injectE _ _ _ _ (P, c)).run es)
    unfold injectE; simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · simp only [StateT.run_pure]; exact GuardedSafePost.pure hInv'
    · simp only [StateT.run_bind]
      refine (vRecv_paperMulti_safe cka prng fs Δcka M_cap tL t la ok rem' es hInv P c none).bind
        fun ⟨out, es₁⟩ h1 => ?_
      dsimp only at h1
      have hes₁_inv : PaperMultiInv t M_cap rem' es₁ := hInv.of_vRecv_step h1.1 h1.2.1 h1.2.2.1 h1.2.2.2.1
      rcases out with _ | (_ | ⟨st', t', i', m'⟩)
      · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
        exact GuardedSafePost.pure (hes₁_inv.with_g_same_st rfl)
      · simp only [StateT.run_pure]; exact GuardedSafePost.pure hes₁_inv
      · dsimp only; split_ifs
        · simp only [StateT.run_pure]; exact GuardedSafePost.pure hes₁_inv
        · simp only [StateT.run_bind]
          rcases h1.2.2.2.2 st' t' i' m' rfl with ⟨hid, hvs_ep, hvs_lt, hvr⟩
          refine (commitE_paperMulti_safe cka prng fs Δcka M_cap tL t la ok es.g P
            (es.g.st P) st' ⟨P.other, t', i'⟩ es₁).bind fun ⟨s₁?, es₂⟩ h2 => ?_
          dsimp only at h2
          rcases h2 with ⟨rfl, h2⟩; rcases s₁? with _ | s₁
          · simp only [StateT.run_pure]; exact GuardedSafePost.pure hes₁_inv
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
            exact GuardedSafePost.pure
              (update_party_inv hInv h1.1 h1.2.1 h1.2.2.1 P (h2 s₁ rfl) hid hvs_ep hvs_lt hvr)
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
          exact GuardedSafePost.pure (hes₁_inv.with_g_same_st rfl)
        · simp only [StateT.run_pure]; exact GuardedSafePost.pure hes₁_inv
  · -- 5. `corrEPaper`
    change SafeZero _ _ ((corrEPaper _ _ P).run es)
    unfold corrEPaper; simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · simp only [StateT.run_pure]; exact GuardedSafePost.pure hInv'
    · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
      exact GuardedSafePost.pure (hInv'.with_g_same_st rfl)
    · rw [hm_run_bind]
      unfold liftH; dsimp only [StateT.run]
      rw [bind_assoc]; simp only [pure_bind]
      have hvs_M : ∀ sIdx, (es.g.st P).vS = some (.inr sIdx) → sIdx < M_cap := fun sIdx hv => by
        have := hInv.vs_lt P sIdx hv; have := hInv.len_le; omega
      refine (hooksFSMulti_reveal_safe cka prng fs Δcka M_cap tL t la ok es.g P (es.g.st P)
        es.h hvs_M).bind fun ⟨o, h1⟩ hh1 => ?_
      dsimp only at hh1
      have hes₁_inv : PaperMultiInv t M_cap rem' { es with h := h1 } :=
        { len_le := by rw [hh1.1]; exact hInv'.len_le
          id_eq := hInv.id_eq
          cache_ok := fun τ Tc σc k sIdx hc => by
            rw [hh1.2] at hc; rw [hh1.1]; exact hInv.cache_ok τ Tc σc k sIdx hc
          vs_ep := hInv.vs_ep
          vs_lt := fun Q sIdx hv => by rw [hh1.1]; exact hInv.vs_lt Q sIdx hv
          vr_ok := fun Q τ sIdx hv => by rw [hh1.1]; exact hInv.vr_ok Q τ sIdx hv }
      rcases o with _ | _
      · simp only [abortE]
        exact GuardedSafePost.pure (hes₁_inv.with_g_same_st rfl)
      · exact GuardedSafePost.pure (hes₁_inv.with_g_same_st (by simp [GameState.afterCorr, GameState.leak]))
  · -- 6. `deliverForgeE`
    change SafeZero _ _ ((deliverForgeE _ _ _ _ (P, c, c')).run es)
    unfold deliverForgeE; simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · simp only [StateT.run_pure]; exact GuardedSafePost.pure hInv'
    · cases es.g.inTransit P.other c with
      | none => simp only [StateT.run_pure]; exact GuardedSafePost.pure hInv'
      | some rec =>
        dsimp only; split_ifs
        · simp only [StateT.run_pure]; exact GuardedSafePost.pure hInv'
        · simp only [StateT.run_bind]
          refine (vRecv_paperMulti_safe cka prng fs Δcka M_cap tL t la ok rem' es hInv P c' none).bind
            fun ⟨out, es₁⟩ h1 => ?_
          dsimp only at h1
          have hes₁_inv : PaperMultiInv t M_cap rem' es₁ := hInv.of_vRecv_step h1.1 h1.2.1 h1.2.2.1 h1.2.2.2.1
          rcases out with _ | (_ | ⟨st', t', i', m'⟩)
          · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
            exact GuardedSafePost.pure (hes₁_inv.with_g_same_st rfl)
          · simp only [StateT.run_pure]; exact GuardedSafePost.pure hes₁_inv
          · dsimp only; split_ifs
            · simp only [StateT.run_pure]; exact GuardedSafePost.pure hes₁_inv
            · simp only [StateT.run_bind]
              rcases h1.2.2.2.2 st' t' i' m' rfl with ⟨hid, hvs_ep, hvs_lt, hvr⟩
              refine (commitE_paperMulti_safe cka prng fs Δcka M_cap tL t la ok es.g P
                (es.g.st P) st' ⟨P.other, t', i'⟩ es₁).bind fun ⟨s₁?, es₂⟩ h2 => ?_
              dsimp only at h2
              rcases h2 with ⟨rfl, h2⟩; rcases s₁? with _ | s₁
              · simp only [StateT.run_pure]; exact GuardedSafePost.pure hes₁_inv
              · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
                exact GuardedSafePost.pure
                  (update_party_inv hInv h1.1 h1.2.1 h1.2.2.1 P (h2 s₁ rfl) hid hvs_ep hvs_lt hvr)
            · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
              exact GuardedSafePost.pure (hes₁_inv.with_g_same_st rfl)
            · simp only [StateT.run_pure]; exact GuardedSafePost.pure hes₁_inv

/-! ## 5. Whole-Reduction Zero-Bad-Query Bound on `redFSAuthDFPaperMulti` -/

private theorem simulateQ_paperMulti_safe {α : Type}
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep M_cap rem : ℕ) (tL : Option ℕ) (t : ℕ) (la : Bool)
    {ok₀ ok : M → Bool} (hok : ∀ m, ok₀ m = true → ok m = true)
    (oa : OracleComp (unifSpec + specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) α)
    (hq : oa.IsQueryBoundP (fun x => x.isRight = true) rem)
    (hsh : oa.IsQueryBoundP (fun x => badSendMsgDF (St := PartyState Γ T RSt SS RS)
      (Coins := CCoins) (C := Header T × E) ok₀ x = true) 0)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E))
    (hInv : PaperMultiInv t M_cap rem es) :
    SafeZero (fun x => badMultiQuery M_cap t ok x = true) (fun _ => True)
      ((simulateQ (implEDFPaper (hooksFSMulti cka prng fs Δcka ⟨true, tL, t⟩ false la)
        (2 + Δcka) qep fs.maxSkip (⟨true, tL, t⟩ : Mode).cfg (⟨true, tL, t⟩ : Mode).policy) oa).run es) := by
  induction oa using OracleComp.inductionOn generalizing rem es with
  | pure _ => simp only [simulateQ_pure, StateT.run_pure]; exact GuardedSafePost.pure trivial
  | query_bind qA k ih =>
    simp only [simulateQ_query_bind, StateT.run_bind]
    rw [isQueryBoundP_query_bind_iff] at hq hsh
    have hqA_sh : badSendMsgDF (St := PartyState Γ T RSt SS RS) (Coins := CCoins)
        (C := Header T × E) ok₀ qA = false := by
      cases hb : badSendMsgDF (St := PartyState Γ T RSt SS RS) (Coins := CCoins)
          (C := Header T × E) ok₀ qA
      · rfl
      · exact False.elim ((hsh.1.resolve_right (Nat.not_lt_zero 0)) hb)
    have hk_sh : ∀ y, (k y).IsQueryBoundP (fun x => badSendMsgDF (St := PartyState Γ T RSt SS RS)
        (Coins := CCoins) (C := Header T × E) ok₀ x = true) 0 :=
      fun y => by simpa [hqA_sh] using hsh.2 y
    rcases qA with u | qr
    · exact (coinsE_paperMulti_safe M_cap rem t ok u es hInv).bind fun z hz =>
        ih z.1 rem (by simpa using hq.2 z.1) (hk_sh z.1) z.2 hz
    · rcases rem with _ | rem'
      · simp at hq
      · exact (implEDFPaper_inr_paperMulti_safe cka prng fs Δcka qep M_cap rem' tL t la hok qr
          hqA_sh es hInv).bind fun z hz => ih z.1 rem' (by simpa using hq.2 z.1) (hk_sh z.1) z.2 hz

private theorem redFSAuthDFPaperMulti_badMultiQuery_zero
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (q Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) (ht0 : 0 < t) (la : Bool)
    {ok₀ ok : M → Bool} (hok : ∀ m, ok₀ m = true → ok m = true)
    (A : SchemeAdversaryDF Γ T RSt SS RS M CCoins E)
    (hq : MakesAtMostQueriesDF A q) (hsh : SendMsgsOkDF ok₀ A) :
    (redFSAuthDFPaperMulti cka prng fs lam Δcka qep la tL t A).IsQueryBoundP
      (fun x => badMultiQuery q t ok x = true) 0 := by
  unfold redFSAuthDFPaperMulti runFSMultiDFPaper
  dsimp only
  simp only [bind_assoc]
  refine safeZero_to_isQueryBoundP (Post := fun _ => True) ?_
  refine (initFSMultiRaw_paperMulti_safe cka prng fs lam q q le_rfl tL t ht0 ok false).bind
    fun es₀ hes₀ => ?_
  exact (simulateQ_paperMulti_safe cka prng fs Δcka qep q q tL t la hok A
    (hq_to_isRight hq) hsh es₀ hes₀).bind fun _ _ => GuardedSafePost.pure trivial

end HookSpecs

/-! ## 6. Target Theorem `redFSAuthDFPaperMulti_twoModeMultiSessBounds` (`N04b`, `qR = 2 * q`) -/

public section

section LibsignalBridges

variable (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (Dh : DHFun (BitVec 256) Pt)

/-- `TwoModeMultiSessBounds` (`M = q`) for `multiSessPubToAD` on `redFSAuthDFPaperMulti`. -/
theorem redFSAuthDFPaperMulti_twoModeMultiSessBounds
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (hℓ : ℓ < 10 ^ 6)
    (q Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) (ht0 : 0 < t)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq : MakesAtMostQueriesDF A q)
    (hsh : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A)
    (hg : GuardedSMDFShort A) :
    TwoModeMultiSessBounds maxForwardJumps (2 * q) q q
      (fun la (_ : Unit) =>
        multiSessPubToAD protoSignalCodec
          (redFSAuthDFPaperMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep la tL t A)) := by
  let AdvPub : Bool → _ := fun la =>
    redFSAuthDFPaperMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep la tL t A
  have hbad : ∀ la : Bool,
      (AdvPub la).IsQueryBoundP
        (fun x => badMultiQuery q t
          (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB) x = true) 0 := fun la =>
    redFSAuthDFPaperMulti_badMultiQuery_zero
      (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam q Δcka qep tL t ht0 la
      (fun _ hm => atomicShortPubB_imp_shortB hm) A hq hsh
  exact
    { offRange := fun la _ =>
        multiSessPubToAD_offRange protoSignalCodec (AdvPub la) q
          ((hbad la).of_imp fun x hx => by
            rw [badMultiQuery, Bool.or_eq_true, Bool.or_eq_true]
            exact Or.inl (Or.inl hx))
      decBound := fun la _ =>
        multiSessPubToAD_decBound protoSignalCodec (AdvPub la) q
          (Computational.Proofs.E2E.SessionAuthMultiDec.redFSAuthDFPaperMulti_dec_onAnySess
            (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam q Δcka qep tL t la A hq)
      shortAD := fun la _ =>
        multiSessPubToAD_shortAD protoSignalCodec (AdvPub la)
          ((hbad la).of_imp fun x hx => by
            rw [badMultiQuery, Bool.or_eq_true, Bool.or_eq_true]
            refine Or.inl (Or.inr ?_)
            rcases x with _ | ⟨_, (((((⟨_, _⟩ | ⟨_, _, _⟩) | _) | _) | _) | _)⟩ <;> exact hx)
      guardedShort := fun la _ =>
        multiSessPubToAD_guardedShort protoSignalCodec (AdvPub la)
          (Computational.Proofs.E2E.SessionAuthMultiShort.redFSAuthDFPaperMulti_guardedMultiInjectShort
            C Dh encPt encT idOf lam hℓ Δcka qep tL t la A hsh hg)
      oneADClass := fun la j _ =>
        ⟨t, multiSessPubToAD_oneADClass protoSignalCodec (AdvPub la) j t
          ((hbad la).of_imp fun x hx => by
            rw [badMultiQuery, Bool.or_eq_true]
            refine Or.inr ?_
            have hany := onSess_imp_onAnySess (fsOutsideClass (fun h : Header Pt => h.1) t) j x hx
            rcases x with _ | ⟨_, (((((⟨_, _⟩ | ⟨_, _, _⟩) | _) | _) | _) | _)⟩ <;> exact hany)⟩ }

end LibsignalBridges

end

end Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFSMulti
