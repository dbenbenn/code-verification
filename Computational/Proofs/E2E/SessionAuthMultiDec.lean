/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperTMinusFS -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperBucketFS -- proof-setup: allow-public-import
public import Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2 -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SessionAuthBridge -- proof-setup: allow-public-import
import Computational.Proofs.E2E.SessionAuthHooksPot

/-!
# Total Decryption-Query (`onAnySess fsInjQ ≤ q`) Bounds for Stage-2 Multi-Session Reductions

Proves `onAnySess fsInjQ ≤ q` for `redFSAuthDFShiftedPaperMultiGen`, `redFSAuthDFPaperMulti`,
and `redFSAuthDFPaperMultiBucket` via `ShallowHooksPot` (`SessionAuthHooksPot`).-/

set_option autoImplicit false

namespace Computational.Proofs.E2E.SessionAuthMultiDec

public section

open OracleSpec OracleComp
open _root_.CryptoGames (CKAScheme PRFPRNG FSAEADScheme)
open _root_.CryptoGames.FSAEAD (
  transmitQuery challengeQuery corruptSenderQuery deliverQuery injectQuery)
open _root_.CryptoGames.SM.Engine (EState VP)
open _root_.CryptoGames.SM.Construction (Header Mode sampleT
  FSMultiSpec FSMultiState FSMultiBook hooksFSMulti rootFSMulti initFSMultiRaw
  liftFSMulti lookupMultiF regSessMulti regSessOptMulti
  FSMultiDFBucketState hooksFSMultiDFBucketPaper rootFSMultiDFBucketPaper
  initFSMultiDFBucketPaper liftFSMultiDFBucket lookupMultiDFBucketF
  bucketAuthCfgGen runFSMultiDFPaper
  redFSAuthDFPaperMulti redFSAuthDFPaperMultiBucket redFSAuthDFPaperMultiBucketGen)
open _root_.CryptoGames.SM.Construction.DeliverForge (SchemeAdversaryDF
  MakesAtMostQueriesDF engRunDFPaperBucket
  implEDFPaperBucket implEDFPaperBucketRaw withWinEpDF)
open _root_.CryptoVerification.E2E.Signed.SessionRouter (onAnySess)
open _root_.CryptoVerification.E2E.Signed.SessionQueries (fsInjQ)
open Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2 (
  runFSMultiDFShiftedPaper redFSAuthDFShiftedPaperMultiGen)
open Computational.Proofs.E2E.SessionAuthHooksPot (
  PotBound potBound_simulateQ_run ShallowHooksPot coinsE_pot
  implEDFShiftedPaperGen_inr_pot implEDFPaper_inr_pot
  implEDFPaperBucketRaw_inr_pot withWinEpDF_pot)

private theorem lift_inr_query_eq {ι₁ ι₂ : Type}
    {s₁ : OracleSpec.{0, 0} ι₁} {s₂ : OracleSpec.{0, 0} ι₂} (q₀ : s₂.Domain) :
    (liftM (OracleSpec.query q₀) : OracleComp (s₁ + s₂) (s₂.Range q₀)) =
      liftM (OracleSpec.query (spec := s₁ + s₂) (Sum.inr q₀)) := rfl

private theorem query_eq_liftM {ι : Type} {spec : OracleSpec.{0, 0} ι} (t : spec.Domain) :
    (query (spec := spec) t : OracleComp spec (spec.Range t)) = liftM (spec.query t) := rfl

private theorem hq_to_isRight {Γ T RSt SS RS M CCoins E : Type} {q : ℕ}
    {A : SchemeAdversaryDF Γ T RSt SS RS M CCoins E} (hq : MakesAtMostQueriesDF A q) :
    A.IsQueryBoundP (fun x => x.isRight = true) q :=
  hq.of_imp fun x hx => by cases x <;> exact hx

/-! ## 1. Decryption-Query (`onAnySess fsInjQ ≤ q`) Bounds via `ShallowHooksPot` -/

section DecBound

private def fsInjMultiPred {SS RS T M E : Type} :
    (unifSpec + FSMultiSpec SS RS T M E).Domain → Bool
  | .inl _ => false
  | .inr ⟨_, .inr _⟩ => true
  | .inr ⟨_, .inl _⟩ => false

private theorem fsInjMultiPred_inl {SS RS T M E : Type} (u : unifSpec.Domain) :
    fsInjMultiPred (SS := SS) (RS := RS) (T := T) (M := M) (E := E) (.inl u) = false := rfl

private theorem sampleT_inj_pot {SS RS T M E : Type}
    (α : Type) [SampleableType α] (rem : ℕ) :
    PotBound (fsInjMultiPred (SS := SS) (RS := RS) (T := T) (M := M) (E := E))
      (fun _ => rem) (sampleT α) rem :=
  PotBound.of_zero_queries fsInjMultiPred_inl ($ᵗ α : ProbComp α) rem

private theorem lift_sampleT_inj_pot {SS RS T M E HS : Type}
    (α : Type) [SampleableType α] (h : HS) (rem : ℕ) :
    PotBound (fsInjMultiPred (SS := SS) (RS := RS) (T := T) (M := M) (E := E))
      (fun _ => rem) ((StateT.lift (sampleT α)).run h) rem := by
  rw [StateT.run_lift]
  exact (sampleT_inj_pot α rem).bind fun _ _ hk => PotBound.pure hk

private theorem liftFSMulti_inj_zero {SS RS T M E Sig K I : Type} (sIdx : ℕ)
    (q₀ : (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E).Domain)
    (hq₀ : fsInjMultiPred (SS := SS) (RS := RS) (T := T) (M := M) (E := E) (.inr ⟨sIdx, q₀⟩) = false)
    (h : FSMultiState T Sig K I E) (rem : ℕ) :
    PotBound fsInjMultiPred (fun _ => rem)
      ((liftFSMulti (SS := SS) (RS := RS) (T := T) (M := M) (E := E)
        sIdx (liftM (OracleSpec.query q₀))).run h) rem := by
  have hq : ((liftFSMulti (SS := SS) (RS := RS) (T := T) (M := M) (E := E)
      sIdx (liftM (OracleSpec.query q₀))).run h) =
      (query (spec := unifSpec + FSMultiSpec SS RS T M E)
        (Sum.inr ⟨sIdx, q₀⟩) >>= fun a => pure (a, h)) := by
    rw [lift_inr_query_eq]; simp [liftFSMulti, StateT.run_lift]
  rw [hq]
  exact (PotBound.query_zero rem hq₀).bind fun _ _ hk => PotBound.pure hk

private theorem liftFSMulti_inj_le_one {SS RS T M E Sig K I : Type} (sIdx : ℕ)
    (q₀ : (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E).Domain)
    (h : FSMultiState T Sig K I E) (rem : ℕ) :
    PotBound fsInjMultiPred (fun _ => rem)
      ((liftFSMulti (SS := SS) (RS := RS) (T := T) (M := M) (E := E)
        sIdx (liftM (OracleSpec.query q₀))).run h) (rem + 1) := by
  have hq : ((liftFSMulti (SS := SS) (RS := RS) (T := T) (M := M) (E := E)
      sIdx (liftM (OracleSpec.query q₀))).run h) =
      (query (spec := unifSpec + FSMultiSpec SS RS T M E)
        (Sum.inr ⟨sIdx, q₀⟩) >>= fun a => pure (a, h)) := by
    rw [lift_inr_query_eq]; simp [liftFSMulti, StateT.run_lift]
  rw [hq]
  exact (PotBound.query_le_one (m := rem) le_rfl).bind fun _ _ hk => PotBound.pure hk

private theorem liftFSMultiDFBucket_inj_zero {SS RS T M E Sig K I : Type} (sIdx : ℕ)
    (q₀ : (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E).Domain)
    (hq₀ : fsInjMultiPred (SS := SS) (RS := RS) (T := T) (M := M) (E := E) (.inr ⟨sIdx, q₀⟩) = false)
    (h : FSMultiDFBucketState T Sig K I E) (rem : ℕ) :
    PotBound fsInjMultiPred (fun _ => rem)
      ((liftFSMultiDFBucket (SS := SS) (RS := RS) (T := T) (M := M) (E := E)
        sIdx (liftM (OracleSpec.query q₀))).run h) rem := by
  have hq : ((liftFSMultiDFBucket (SS := SS) (RS := RS) (T := T) (M := M) (E := E)
      sIdx (liftM (OracleSpec.query q₀))).run h) =
      (query (spec := unifSpec + FSMultiSpec SS RS T M E)
        (Sum.inr ⟨sIdx, q₀⟩) >>= fun a => pure (a, h)) := by
    rw [lift_inr_query_eq]; simp [liftFSMultiDFBucket, StateT.run_lift]
  rw [hq]
  exact (PotBound.query_zero rem hq₀).bind fun _ _ hk => PotBound.pure hk

private theorem liftFSMultiDFBucket_inj_le_one {SS RS T M E Sig K I : Type} (sIdx : ℕ)
    (q₀ : (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E).Domain)
    (h : FSMultiDFBucketState T Sig K I E) (rem : ℕ) :
    PotBound fsInjMultiPred (fun _ => rem)
      ((liftFSMultiDFBucket (SS := SS) (RS := RS) (T := T) (M := M) (E := E)
        sIdx (liftM (OracleSpec.query q₀))).run h) (rem + 1) := by
  have hq : ((liftFSMultiDFBucket (SS := SS) (RS := RS) (T := T) (M := M) (E := E)
      sIdx (liftM (OracleSpec.query q₀))).run h) =
      (query (spec := unifSpec + FSMultiSpec SS RS T M E)
        (Sum.inr ⟨sIdx, q₀⟩) >>= fun a => pure (a, h)) := by
    rw [lift_inr_query_eq]; simp [liftFSMultiDFBucket, StateT.run_lift]
  rw [hq]
  exact (PotBound.query_le_one (m := rem) le_rfl).bind fun _ _ hk => PotBound.pure hk

private theorem lookupMultiF_inj {SS RS T M E Sig K I : Type} [DecidableEq I] [SampleableType K]
    (Ik : I) (h : FSMultiState T Sig K I E) (rem : ℕ) :
    PotBound (fsInjMultiPred (SS := SS) (RS := RS) (T := T) (M := M) (E := E))
      (fun _ => rem) ((lookupMultiF (SS := SS) (RS := RS) (M := M) Ik).run h) rem := by
  unfold lookupMultiF
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases h.table.lookup Ik with
  | some _ => exact PotBound.pure le_rfl
  | none =>
    simp only [StateT.run_bind]
    exact (lift_sampleT_inj_pot K h rem).bind fun _ _ hk => by
      simp only [StateT.run_modify, StateT.run_pure, pure_bind]; exact PotBound.pure hk

private theorem regSessMulti_inj {SS RS T M E Sig K I : Type} [DecidableEq I]
    (Ik : I) (h : FSMultiState T Sig K I E) (rem : ℕ) :
    PotBound (fsInjMultiPred (SS := SS) (RS := RS) (T := T) (M := M) (E := E))
      (fun _ => rem) ((regSessMulti (SS := SS) (RS := RS) (M := M) Ik).run h) rem := by
  unfold regSessMulti
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split <;> simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind] <;>
    exact PotBound.pure le_rfl

private theorem regSessOptMulti_inj {SS RS T M E Sig K I : Type} [DecidableEq I]
    (sid : Option I) (h : FSMultiState T Sig K I E) (rem : ℕ) :
    PotBound (fsInjMultiPred (SS := SS) (RS := RS) (T := T) (M := M) (E := E))
      (fun _ => rem) ((regSessOptMulti (SS := SS) (RS := RS) (M := M) sid).run h) rem := by
  cases sid with
  | none => simp only [regSessOptMulti, StateT.run_pure]; exact PotBound.pure le_rfl
  | some Ik =>
    simp only [regSessOptMulti, StateT.run_map]
    exact (regSessMulti_inj Ik h rem).map fun _ => le_rfl

private theorem rootFSMulti_inj {KR RSt K I T SS RS M E : Type}
    [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR RSt I K) (mo : Mode) (t : ℕ) (Ik : I) (σ : RSt)
    (h : FSMultiState T RSt K I E) (rem : ℕ) :
    PotBound (fsInjMultiPred (SS := SS) (RS := RS) (T := T) (M := M) (E := E))
      (fun _ => rem)
      ((rootFSMulti (T := T) (SS := SS) (RS := RS) (M := M) (E := E) prng mo t Ik σ).run h) rem := by
  unfold rootFSMulti
  split
  · exact PotBound.pure le_rfl
  · split
    · split
      · simp only [StateT.run_bind]
        refine (lift_sampleT_inj_pot I h rem).bind fun ⟨_, h1⟩ m hm => ?_
        exact ((lift_sampleT_inj_pot K h1 rem).mono (fun _ => le_rfl) hm).bind fun _ _ hm2 =>
          PotBound.pure hm2
      · simp only [StateT.run_bind]
        exact (lookupMultiF_inj Ik h rem).bind fun _ _ hm => PotBound.pure hm
    · split
      · simp only [StateT.run_bind]
        exact (lift_sampleT_inj_pot I h rem).bind fun _ _ hm => PotBound.pure hm
      · exact PotBound.pure le_rfl

private theorem fsSendTailMulti_inj {SS RS T M E Sig K I : Type}
    (sIdx : ℕ) (hdr : Header T) (m : M) (pair : Option (M × M))
    (h : FSMultiState T Sig K I E) (rem : ℕ) :
    PotBound (fsInjMultiPred (SS := SS) (RS := RS) (T := T) (M := M) (E := E))
      (fun _ => rem)
      ((do
        let e? ← match pair with
          | some (m₀, m₁) =>
            liftFSMulti sIdx (challengeQuery (SenderState := SS) (ReceiverState := RS) hdr m₀ m₁)
          | none =>
            liftFSMulti sIdx (transmitQuery (SenderState := SS) (ReceiverState := RS) hdr m)
        match e? with
        | none => return none
        | some e =>
          modify fun st : FSMultiState T Sig K I E =>
            let b0 := (st.book sIdx).getD {}
            let cnt' := b0.fsCount + 1
            let b' : FSMultiBook T E := { b0 with fsCount := cnt', fsTrans := (cnt', hdr, e) :: b0.fsTrans }
            { st with book := Function.update st.book sIdx (some b') }
          return some ((.inr sIdx : SS ⊕ ℕ), e)).run h) rem := by
  rcases pair with _ | ⟨m₀, m₁⟩
  · simp only [StateT.run_bind, transmitQuery, query_eq_liftM]
    refine (liftFSMulti_inj_zero sIdx _ rfl h rem).bind fun ⟨o, _⟩ _ hm => ?_
    rcases o with _ | _ <;>
      simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind] <;>
      exact PotBound.pure hm
  · simp only [StateT.run_bind, challengeQuery, query_eq_liftM]
    refine (liftFSMulti_inj_zero sIdx _ rfl h rem).bind fun ⟨o, _⟩ _ hm => ?_
    rcases o with _ | _ <;>
      simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind] <;>
      exact PotBound.pure hm

private theorem hooksFSMulti_inj_pot
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (gMain la : Bool) :
    ShallowHooksPot fsInjMultiPred (fun _ => 0) (hooksFSMulti cka prng fs Δcka mo gMain la) where
  inl_false := fsInjMultiPred_inl
  startSend_pot _ _ t γ σ r h rem := by
    dsimp only [hooksFSMulti, Nat.add_zero]
    rcases r with _ | c
    · simp only [StateT.run_bind]
      refine (lift_sampleT_inj_pot CCoins h rem).bind fun ⟨coins, h1⟩ _ hm1 => ?_
      refine ((rootFSMulti_inj prng mo t (cka.send γ coins).2.2 σ h1 rem).mono
        (fun _ => le_rfl) hm1).bind fun ⟨⟨_, _, sid⟩, h2⟩ _ hm2 => ?_
      refine ((regSessOptMulti_inj sid h2 rem).mono (fun _ => le_rfl) hm2).bind fun _ _ hm3 => ?_
      simp only [StateT.run_modify, StateT.run_pure, pure_bind]; exact PotBound.pure hm3
    · simp only [StateT.run_bind, StateT.run_pure, pure_bind]
      refine (rootFSMulti_inj prng mo t (cka.send γ c).2.2 σ h rem).bind
        fun ⟨⟨_, _, sid⟩, h2⟩ _ hm2 => ?_
      refine ((regSessOptMulti_inj sid h2 rem).mono (fun _ => le_rfl) hm2).bind fun _ _ hm3 => ?_
      simp only [StateT.run_modify, pure_bind]; exact PotBound.pure hm3
  startRecv_pot _ _ t γ σ Tn h rem := by
    dsimp only [hooksFSMulti, Nat.add_zero]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split
    · exact PotBound.pure le_rfl
    · split
      · exact PotBound.pure le_rfl
      · split
        · split
          · exact PotBound.pure le_rfl
          · simp only [StateT.run_bind]
            refine (lookupMultiF_inj (cka.receive γ Tn).2 h rem).bind fun ⟨_, h1⟩ _ hm1 => ?_
            exact ((regSessMulti_inj (cka.receive γ Tn).2 h1 rem).mono (fun _ => le_rfl) hm1).bind
              fun _ _ hm2 => PotBound.pure hm2
        · exact PotBound.pure le_rfl
  fsSend_pot _ _ _ ssv hdr m pair h rem := by
    dsimp only [hooksFSMulti, Nat.add_zero]
    rcases ssv with _ | sIdx
    · exact PotBound.pure (by omega)
    · simp only [StateT.run_bind, StateT.run_get, pure_bind]
      split
      · cases la
        · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, corruptSenderQuery, query_eq_liftM]
          refine (liftFSMulti_inj_zero sIdx _ rfl h (rem + 1)).bind fun ⟨o, h1⟩ _ hm1 => ?_
          rcases o with _ | _
          · simp only [StateT.run_pure, Bool.not_false, ↓reduceIte]; exact PotBound.pure (by omega)
          · simp only [StateT.run_bind, StateT.run_modify, pure_bind,
              Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            exact (fsSendTailMulti_inj (SS := SS) (RS := RS) sIdx hdr m pair _ rem).mono
              (fun _ => le_rfl) (by omega)
        · simp only [↓reduceIte, StateT.run_pure, Bool.not_false]
          exact PotBound.pure (by omega)
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        exact (fsSendTailMulti_inj (SS := SS) (RS := RS) sIdx hdr m pair h rem).mono
          (fun _ => le_rfl) (by omega)
  fsRecv_pot _ _ _ rsv hdr e rec h rem := by
    dsimp only [hooksFSMulti, Nat.add_zero]
    rcases rsv with _ | sIdx
    · exact PotBound.pure (by omega)
    · simp only [StateT.run_bind, StateT.run_get, pure_bind]
      let matched : Option (ℕ × Header T × E) :=
        ((h.book sIdx).getD {}).fsTrans.find? (fun x => x.2 == (hdr, e))
      have hTail : ∀ h' : FSMultiState T RSt K I E,
          PotBound fsInjMultiPred (fun _ => rem)
            ((do
              let res ← if matched.isSome then
                  liftFSMulti sIdx (deliverQuery (SenderState := SS) (ReceiverState := RS) hdr e)
                else
                  liftFSMulti sIdx (injectQuery (SenderState := SS) (ReceiverState := RS) hdr e)
              match res with
              | none => return (none : Option (Option ((RS ⊕ ℕ) × ℕ × M)))
              | some .rejected => return some none
              | some (.accepted i mo') =>
                let s1 ← get
                let bk1 := (s1.book sIdx).getD {}
                if la && matched.isNone && (!bk1.sCorr) && bk1.fsCount < i then
                  modify fun (s : FSMultiState T RSt K I E) => { s with lfWin := true }
                  return none
                else
                  let drop := (matched.map (fun (x : ℕ × Header T × E) => x.1)).getD i
                  modify fun (s : FSMultiState T RSt K I E) =>
                    let b := (s.book sIdx).getD {}
                    let b' : FSMultiBook T E := { b with fsTrans := b.fsTrans.filter (·.1 != drop) }
                    { s with book := Function.update s.book sIdx (some b') }
                  match mo', rec with
                  | some m, _ => return some (some ((.inr sIdx : RS ⊕ ℕ), i, m))
                  | none, some r => return some (some ((.inr sIdx : RS ⊕ ℕ), i, r.msg))
                  | none, none => return none).run h') (rem + 1) := by
        intro h'; split_ifs
        · simp only [StateT.run_bind, deliverQuery, query_eq_liftM]
          refine (liftFSMulti_inj_le_one sIdx _ h' rem).bind fun ⟨res, _⟩ _ hm1 => ?_
          rcases res with _ | (_ | ⟨_, mo'⟩)
          · exact PotBound.pure hm1
          · exact PotBound.pure hm1
          · simp only [StateT.run_bind, StateT.run_get, pure_bind]; split_ifs
            · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
              exact PotBound.pure hm1
            · simp only [StateT.run_bind, StateT.run_modify, pure_bind]
              rcases mo' with _ | _ <;> rcases rec with _ | _ <;> exact PotBound.pure hm1
        · simp only [StateT.run_bind, injectQuery, query_eq_liftM]
          refine (liftFSMulti_inj_le_one sIdx _ h' rem).bind fun ⟨res, _⟩ _ hm1 => ?_
          rcases res with _ | (_ | ⟨_, mo'⟩)
          · exact PotBound.pure hm1
          · exact PotBound.pure hm1
          · simp only [StateT.run_bind, StateT.run_get, pure_bind]; split_ifs
            · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
              exact PotBound.pure hm1
            · simp only [StateT.run_bind, StateT.run_modify, pure_bind]
              rcases mo' with _ | _ <;> rcases rec with _ | _ <;> exact PotBound.pure hm1
      split
      · cases la
        · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, corruptSenderQuery, query_eq_liftM]
          refine (liftFSMulti_inj_zero sIdx _ rfl h (rem + 1)).bind fun ⟨o, _⟩ _ hm1 => ?_
          rcases o with _ | _
          · simp only [StateT.run_pure, Bool.not_false, ↓reduceIte]; exact PotBound.pure (by omega)
          · simp only [StateT.run_bind, StateT.run_modify, pure_bind,
              Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            exact (hTail _).mono (fun _ => le_rfl) (by omega)
        · simp only [↓reduceIte, StateT.run_pure, Bool.not_false]
          exact PotBound.pure (by omega)
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        exact hTail h
  commit_pot _ _ _ _ _ rem := PotBound.pure le_rfl
  reveal_pot _ _ vp h rem := by
    dsimp only [hooksFSMulti, Nat.add_zero]
    rcases vp.vS with _ | (_ | sIdx)
    · simp only [pure_bind]; split_ifs <;> exact PotBound.pure (by omega)
    · simp only [pure_bind]; split_ifs <;> exact PotBound.pure (by omega)
    · cases la
      · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, corruptSenderQuery, query_eq_liftM]
        refine (liftFSMulti_inj_zero sIdx _ rfl h (rem + 1)).bind fun ⟨o, _⟩ _ hm1 => ?_
        rcases o with _ | _
        · simp only [StateT.run_pure, pure_bind]; exact PotBound.pure (by omega)
        · simp only [StateT.run_bind, StateT.run_modify, pure_bind]
          split_ifs <;> exact PotBound.pure (by omega)
      · simp only [↓reduceIte, StateT.run_pure, pure_bind]; exact PotBound.pure (by omega)

private theorem lookupMultiDFBucketF_inj {SS RS T M E Sig K I : Type}
    [DecidableEq I] [SampleableType K]
    (t0 : ℕ) (ik : I) (h : FSMultiDFBucketState T Sig K I E) (rem : ℕ) :
    PotBound (fsInjMultiPred (SS := SS) (RS := RS) (T := T) (M := M) (E := E))
      (fun _ => rem) ((lookupMultiDFBucketF (SS := SS) (RS := RS) (M := M) t0 ik).run h) rem := by
  unfold lookupMultiDFBucketF
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases (h.fTable t0).lookup ik with
  | some _ => exact PotBound.pure le_rfl
  | none =>
    simp only [StateT.run_bind]
    exact (lift_sampleT_inj_pot K h rem).bind fun _ _ hk => by
      simp only [StateT.run_modify, StateT.run_pure, pure_bind]; exact PotBound.pure hk

private theorem rootFSMultiDFBucketPaper_inj {KR RSt K I T SS RS M E : Type}
    [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR RSt I K) (Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool)
    (t0 : ℕ) (pl : Bool) (ik0 : I) (σ0 : RSt)
    (h : FSMultiDFBucketState T RSt K I E) (rem : ℕ) :
    PotBound (fsInjMultiPred (SS := SS) (RS := RS) (T := T) (M := M) (E := E))
      (fun _ => rem)
      ((rootFSMultiDFBucketPaper (T := T) (SS := SS) (RS := RS) (M := M) (E := E)
        prng Δbucket qep tL par t0 pl ik0 σ0).run h) rem := by
  unfold rootFSMultiDFBucketPaper; dsimp only
  split
  · exact PotBound.pure le_rfl
  · split
    · split
      · simp only [StateT.run_bind]
        refine (lift_sampleT_inj_pot I h rem).bind fun ⟨_, h1⟩ _ hm => ?_
        exact ((lift_sampleT_inj_pot K h1 rem).mono (fun _ => le_rfl) hm).bind fun _ _ hm2 =>
          PotBound.pure hm2
      · simp only [StateT.run_bind]
        exact (lookupMultiDFBucketF_inj t0 ik0 h rem).bind fun _ _ hm => PotBound.pure hm
    · split
      · simp only [StateT.run_bind]
        refine (lift_sampleT_inj_pot I h rem).bind fun ⟨_, h1⟩ _ hm => ?_
        exact ((lift_sampleT_inj_pot K h1 rem).mono (fun _ => le_rfl) hm).bind fun _ _ hm2 =>
          PotBound.pure hm2
      · exact PotBound.pure le_rfl

private theorem fsSendTailBucket_inj {SS RS T M E Sig K I : Type}
    (sIdx : ℕ) (hdr : Header T) (m : M) (pair : Option (M × M))
    (h : FSMultiDFBucketState T Sig K I E) (rem : ℕ) :
    PotBound (fsInjMultiPred (SS := SS) (RS := RS) (T := T) (M := M) (E := E))
      (fun _ => rem)
      ((do
        let e? ← match pair with
          | some (m₀, m₁) =>
            liftFSMultiDFBucket sIdx (challengeQuery (SenderState := SS) (ReceiverState := RS) hdr m₀ m₁)
          | none =>
            liftFSMultiDFBucket sIdx (transmitQuery (SenderState := SS) (ReceiverState := RS) hdr m)
        match e? with
        | none => return none
        | some e =>
          modify fun st : FSMultiDFBucketState T Sig K I E =>
            let b0 := (st.book sIdx).getD {}
            let cnt' := b0.fsCount + 1
            let b' : FSMultiBook T E := { b0 with fsCount := cnt', fsTrans := (cnt', hdr, e) :: b0.fsTrans }
            { st with book := Function.update st.book sIdx (some b') }
          return some ((.inr sIdx : SS ⊕ ℕ), e)).run h) rem := by
  rcases pair with _ | ⟨m₀, m₁⟩
  · simp only [StateT.run_bind, transmitQuery, query_eq_liftM]
    refine (liftFSMultiDFBucket_inj_zero sIdx _ rfl h rem).bind fun ⟨o, _⟩ _ hm => ?_
    rcases o with _ | _ <;>
      simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind] <;>
      exact PotBound.pure hm
  · simp only [StateT.run_bind, challengeQuery, query_eq_liftM]
    refine (liftFSMultiDFBucket_inj_zero sIdx _ rfl h rem).bind fun ⟨o, _⟩ _ hm => ?_
    rcases o with _ | _ <;>
      simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind] <;>
      exact PotBound.pure hm

private theorem hooksFSMultiDFBucketPaper_inj_pot
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka Δbucket qep : ℕ)
    (tL : Option ℕ) (par la : Bool) :
    ShallowHooksPot fsInjMultiPred (fun _ => 0)
      (hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la) where
  inl_false := fsInjMultiPred_inl
  startSend_pot _ _ t0 γ0 σ0 r0 h rem := by
    dsimp only [hooksFSMultiDFBucketPaper, Nat.add_zero]
    rcases r0 with _ | c
    · simp only [StateT.run_bind]
      refine (lift_sampleT_inj_pot CCoins h rem).bind fun ⟨coins, h1⟩ _ hm1 => ?_
      refine ((rootFSMultiDFBucketPaper_inj prng Δbucket qep tL par t0 _
        (cka.send γ0 coins).2.2 σ0 h1 rem).mono (fun _ => le_rfl) hm1).bind fun _ _ hm2 => ?_
      simp only [StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind]
      exact PotBound.pure hm2
    · simp only [StateT.run_bind, StateT.run_pure, pure_bind]
      refine (rootFSMultiDFBucketPaper_inj prng Δbucket qep tL par t0 _
        (cka.send γ0 c).2.2 σ0 h rem).bind fun _ _ hm2 => ?_
      simp only [StateT.run_get, StateT.run_set, pure_bind]
      exact PotBound.pure hm2
  startRecv_pot _ _ t0 γ0 σ0 tn0 h rem := by
    dsimp only [hooksFSMultiDFBucketPaper, Nat.add_zero]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split
    · exact PotBound.pure le_rfl
    · split
      · split
        · exact PotBound.pure le_rfl
        · split
          · exact PotBound.pure le_rfl
          · simp only [StateT.run_bind]
            refine (lookupMultiDFBucketF_inj t0 (cka.receive γ0 tn0).2 h rem).bind fun _ _ hm1 => ?_
            simp only [StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind]
            exact PotBound.pure hm1
      · exact PotBound.pure le_rfl
  fsSend_pot _ _ _ ssv hdr m pair h rem := by
    dsimp only [hooksFSMultiDFBucketPaper, Nat.add_zero]
    rcases ssv with _ | sIdx
    · exact PotBound.pure (by omega)
    · simp only [StateT.run_bind, StateT.run_get, pure_bind]
      split
      · simp only [StateT.run_bind, corruptSenderQuery, query_eq_liftM]
        refine (liftFSMultiDFBucket_inj_zero sIdx _ rfl h (rem + 1)).bind fun ⟨o, _⟩ _ hm1 => ?_
        rcases o with _ | _
        · simp only [StateT.run_pure, Bool.not_false, ↓reduceIte]; exact PotBound.pure (by omega)
        · simp only [StateT.run_bind, StateT.run_modify, pure_bind,
            Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          exact (fsSendTailBucket_inj (SS := SS) (RS := RS) sIdx hdr m pair _ rem).mono
            (fun _ => le_rfl) (by omega)
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        exact (fsSendTailBucket_inj (SS := SS) (RS := RS) sIdx hdr m pair h rem).mono
          (fun _ => le_rfl) (by omega)
  fsRecv_pot _ _ _ rsv hdr e rec h rem := by
    dsimp only [hooksFSMultiDFBucketPaper, Nat.add_zero]
    rcases rsv with _ | sIdx
    · exact PotBound.pure (by omega)
    · simp only [StateT.run_bind, StateT.run_get, pure_bind]
      let matched : Option (ℕ × Header T × E) :=
        ((h.book sIdx).getD {}).fsTrans.find? (fun x => x.2 == (hdr, e))
      have hTail : ∀ h' : FSMultiDFBucketState T RSt K I E,
          PotBound fsInjMultiPred (fun _ => rem)
            ((do
              let res ← if matched.isSome then
                  liftFSMultiDFBucket sIdx (deliverQuery (SenderState := SS) (ReceiverState := RS) hdr e)
                else
                  liftFSMultiDFBucket sIdx (injectQuery (SenderState := SS) (ReceiverState := RS) hdr e)
              match res with
              | none => return (none : Option (Option ((RS ⊕ ℕ) × ℕ × M)))
              | some .rejected => return some none
              | some (.accepted i mo') =>
                let s1 ← get
                let bk1 := (s1.book sIdx).getD {}
                if la && matched.isNone && (!bk1.sCorr) && bk1.fsCount < i then
                  modify fun (s : FSMultiDFBucketState T RSt K I E) => { s with lfWin := true }
                  return none
                else
                  let drop := (matched.map (fun (x : ℕ × Header T × E) => x.1)).getD i
                  modify fun (s : FSMultiDFBucketState T RSt K I E) =>
                    let b := (s.book sIdx).getD {}
                    let b' : FSMultiBook T E := { b with fsTrans := b.fsTrans.filter (·.1 != drop) }
                    { s with book := Function.update s.book sIdx (some b') }
                  match mo', rec with
                  | some m, _ => return some (some ((.inr sIdx : RS ⊕ ℕ), i, m))
                  | none, some r => return some (some ((.inr sIdx : RS ⊕ ℕ), i, r.msg))
                  | none, none => return none).run h') (rem + 1) := by
        intro h'; split_ifs
        · simp only [StateT.run_bind, deliverQuery, query_eq_liftM]
          refine (liftFSMultiDFBucket_inj_le_one sIdx _ h' rem).bind fun ⟨res, _⟩ _ hm1 => ?_
          rcases res with _ | (_ | ⟨_, mo'⟩)
          · exact PotBound.pure hm1
          · exact PotBound.pure hm1
          · simp only [StateT.run_bind, StateT.run_get, pure_bind]; split_ifs
            · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
              exact PotBound.pure hm1
            · simp only [StateT.run_bind, StateT.run_modify, pure_bind]
              rcases mo' with _ | _ <;> rcases rec with _ | _ <;> exact PotBound.pure hm1
        · simp only [StateT.run_bind, injectQuery, query_eq_liftM]
          refine (liftFSMultiDFBucket_inj_le_one sIdx _ h' rem).bind fun ⟨res, _⟩ _ hm1 => ?_
          rcases res with _ | (_ | ⟨_, mo'⟩)
          · exact PotBound.pure hm1
          · exact PotBound.pure hm1
          · simp only [StateT.run_bind, StateT.run_get, pure_bind]; split_ifs
            · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
              exact PotBound.pure hm1
            · simp only [StateT.run_bind, StateT.run_modify, pure_bind]
              rcases mo' with _ | _ <;> rcases rec with _ | _ <;> exact PotBound.pure hm1
      split
      · simp only [StateT.run_bind, corruptSenderQuery, query_eq_liftM]
        refine (liftFSMultiDFBucket_inj_zero sIdx _ rfl h (rem + 1)).bind fun ⟨o, _⟩ _ hm1 => ?_
        rcases o with _ | _
        · simp only [StateT.run_pure, Bool.not_false, ↓reduceIte]; exact PotBound.pure (by omega)
        · simp only [StateT.run_bind, StateT.run_modify, pure_bind,
            Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          exact (hTail _).mono (fun _ => le_rfl) (by omega)
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        exact hTail h
  commit_pot _ _ _ _ _ rem := PotBound.pure le_rfl
  reveal_pot _ _ vp h rem := by
    dsimp only [hooksFSMultiDFBucketPaper, Nat.add_zero]
    rcases vp.vS with _ | (_ | sIdx)
    · simp only [pure_bind]; split_ifs <;> exact PotBound.pure (by omega)
    · simp only [pure_bind]; split_ifs <;> exact PotBound.pure (by omega)
    · simp only [StateT.run_bind, corruptSenderQuery, query_eq_liftM]
      refine (liftFSMultiDFBucket_inj_zero sIdx _ rfl h (rem + 1)).bind fun ⟨o, _⟩ _ hm1 => ?_
      rcases o with _ | _
      · simp only [StateT.run_pure, pure_bind]; exact PotBound.pure (by omega)
      · simp only [StateT.run_bind, StateT.run_modify, pure_bind]
        split_ifs <;> exact PotBound.pure (by omega)

private theorem initFSMultiRaw_inj {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq I] [SampleableType KR] [SampleableType KC]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (mo : Mode) (b : Bool) (rem : ℕ) :
    PotBound fsInjMultiPred (fun _ => rem) (initFSMultiRaw cka prng fs lam mo b) rem := by
  unfold initFSMultiRaw
  refine (sampleT_inj_pot KR rem).bind fun kr _ hm1 => ?_
  refine ((sampleT_inj_pot KC rem).mono (fun _ => le_rfl) hm1).bind fun _ _ hm2 => ?_
  refine ((rootFSMulti_inj (T := T) (SS := SS) (RS := RS) (M := M) (E := E) prng mo 0 lam
    (prng.init kr) ({} : FSMultiState T RSt K I E) rem).mono (fun _ => le_rfl) hm2).bind
    fun ⟨⟨_, _, sid⟩, h1⟩ _ hm3 => ?_
  exact ((regSessOptMulti_inj (SS := SS) (RS := RS) (M := M) sid h1 rem).mono
    (fun _ => le_rfl) hm3).bind fun _ _ hm4 => PotBound.pure hm4

private theorem initFSMultiDFBucketPaper_inj {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq I] [SampleableType KR] [SampleableType KC]
    [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) (rem : ℕ) :
    PotBound fsInjMultiPred (fun _ => rem)
      ((initFSMultiDFBucketPaper L cka prng fs lam Δbucket qep tL par).run
        ({} : FSMultiDFBucketState T RSt K I E)) rem := by
  unfold initFSMultiDFBucketPaper
  simp only [StateT.run_bind]
  refine (lift_sampleT_inj_pot KR ({} : FSMultiDFBucketState T RSt K I E) rem).bind
    fun ⟨kr, h1⟩ _ hm1 => ?_
  refine ((lift_sampleT_inj_pot KC h1 rem).mono (fun _ => le_rfl) hm1).bind fun ⟨_, h2⟩ _ hm2 => ?_
  refine ((rootFSMultiDFBucketPaper_inj (T := T) (SS := SS) (RS := RS) (M := M) (E := E)
    prng Δbucket qep tL par 0 false lam (prng.init kr) h2 rem).mono (fun _ => le_rfl) hm2).bind
    fun _ _ hm3 => ?_
  simp only [StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind]
  exact PotBound.pure hm3

private theorem redFSAuthDFShiftedPaperMultiGen_dec_pub
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (q Δcka qep l t : ℕ) (authH la : Bool)
    (A : SchemeAdversaryDF Γ T RSt SS RS M CCoins E)
    (hq : MakesAtMostQueriesDF A q) :
    (redFSAuthDFShiftedPaperMultiGen cka prng fs lam Δcka qep l t authH la A).IsQueryBoundP
      (fun x => fsInjMultiPred x = true) q := by
  have hq' := hq_to_isRight hq
  unfold redFSAuthDFShiftedPaperMultiGen runFSMultiDFShiftedPaper
  rw [bind_assoc]
  have hkPot := hooksFSMulti_inj_pot cka prng fs Δcka ⟨authH, some (l - 1), t⟩ false la
  refine ((initFSMultiRaw_inj cka prng fs lam _ false q).bind (post := fun _ => 0) fun es₀ m hm =>
    ((potBound_simulateQ_run fsInjMultiPred (fun _ => 0) _
      (fun u st rem => coinsE_pot (pot := fun _ => 0) fsInjMultiPred_inl u st rem)
      (fun qr st rem => implEDFShiftedPaperGen_inr_pot hkPot (!authH) l (2 + Δcka) qep
        fs.maxSkip t _ _ qr st rem)
      q A hq' es₀).mono (fun _ => Nat.zero_le _) (by omega)).bind fun _ m2 _ =>
      PotBound.pure (Nat.zero_le m2)).to_isQueryBoundP

private theorem redFSAuthDFPaperMulti_dec_pub
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (q Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) (la : Bool)
    (A : SchemeAdversaryDF Γ T RSt SS RS M CCoins E)
    (hq : MakesAtMostQueriesDF A q) :
    (redFSAuthDFPaperMulti cka prng fs lam Δcka qep la tL t A).IsQueryBoundP
      (fun x => fsInjMultiPred x = true) q := by
  have hq' := hq_to_isRight hq
  unfold redFSAuthDFPaperMulti runFSMultiDFPaper
  rw [bind_assoc]
  have hkPot := hooksFSMulti_inj_pot cka prng fs Δcka ⟨true, tL, t⟩ false la
  refine ((initFSMultiRaw_inj cka prng fs lam _ false q).bind (post := fun _ => 0) fun es₀ m hm =>
    ((potBound_simulateQ_run fsInjMultiPred (fun _ => 0) _
      (fun u st rem => coinsE_pot (pot := fun _ => 0) fsInjMultiPred_inl u st rem)
      (fun qr st rem => implEDFPaper_inr_pot hkPot (2 + Δcka) qep fs.maxSkip _ _ qr st rem)
      q A hq' es₀).mono (fun _ => Nat.zero_le _) (by omega)).bind fun _ m2 _ =>
      PotBound.pure (Nat.zero_le m2)).to_isQueryBoundP

private theorem redFSAuthDFPaperMultiBucket_dec_pub
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (q Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par la : Bool)
    (A : SchemeAdversaryDF Γ T RSt SS RS M CCoins E)
    (hq : MakesAtMostQueriesDF A q) :
    (redFSAuthDFPaperMultiBucket L cka prng fs lam Δcka Δbucket qep la tL par A).IsQueryBoundP
      (fun x => fsInjMultiPred x = true) q := by
  have hq' := hq_to_isRight hq
  unfold redFSAuthDFPaperMultiBucket redFSAuthDFPaperMultiBucketGen engRunDFPaperBucket
    implEDFPaperBucket
  rw [bind_assoc]
  let hk := hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la
  let rawImpl := implEDFPaperBucketRaw hk (2 + Δcka) qep fs.maxSkip (bucketAuthCfgGen Δbucket tL par)
  let impl := withWinEpDF (fun c => c.1.1) (fun es => es.g.win) rawImpl
  have hkPot := hooksFSMultiDFBucketPaper_inj_pot L cka prng fs Δcka Δbucket qep tL par la
  refine ((initFSMultiDFBucketPaper_inj L cka prng fs lam Δbucket qep tL par q).bind
    (post := fun _ => 0) fun ⟨vs, h⟩ m hm => ?_).to_isQueryBoundP
  rcases vs with _ | ⟨vA, vB⟩
  · simp only [pure_bind]; exact PotBound.pure (Nat.zero_le m)
  · simp only [bind_assoc]
    let es₀ : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E)
        (FSMultiDFBucketState T RSt K I E) :=
      { g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := h }
    exact ((potBound_simulateQ_run fsInjMultiPred (fun _ => 0) impl
      (fun u st rem => withWinEpDF_pot (pot := fun _ => 0) (rem := rem) _ _
        rawImpl (.inl u) st (coinsE_pot (pot := fun _ => 0) fsInjMultiPred_inl u st.1 rem))
      (fun qr st rem => withWinEpDF_pot (pot := fun _ => 0) (rem := rem) _ _
        rawImpl (.inr qr) st (implEDFPaperBucketRaw_inr_pot hkPot (2 + Δcka) qep fs.maxSkip _ qr st.1 rem))
      q A hq' (es₀, none)).mono (fun _ => Nat.zero_le _) (by omega)).bind fun _ m2 _ =>
      PotBound.pure (Nat.zero_le m2)

/-- Total decryption-query bound (`onAnySess fsInjQ ≤ q`) on `redFSAuthDFShiftedPaperMultiGen`. -/
theorem redFSAuthDFShiftedPaperMultiGen_dec_onAnySess
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (q Δcka qep l t : ℕ) (authH la : Bool)
    (A : SchemeAdversaryDF Γ T RSt SS RS M CCoins E)
    (hq : MakesAtMostQueriesDF A q) :
    (redFSAuthDFShiftedPaperMultiGen cka prng fs lam Δcka qep l t authH la A).IsQueryBoundP
      (fun x => onAnySess fsInjQ x = true) q :=
  (redFSAuthDFShiftedPaperMultiGen_dec_pub cka prng fs lam q Δcka qep l t authH la A hq).of_imp
    fun x hx => by rcases x with _ | ⟨_, _ | _⟩ <;> exact hx

/-- Total decryption-query bound (`onAnySess fsInjQ ≤ q`) on `redFSAuthDFPaperMulti`. -/
theorem redFSAuthDFPaperMulti_dec_onAnySess
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (q Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) (la : Bool)
    (A : SchemeAdversaryDF Γ T RSt SS RS M CCoins E)
    (hq : MakesAtMostQueriesDF A q) :
    (redFSAuthDFPaperMulti cka prng fs lam Δcka qep la tL t A).IsQueryBoundP
      (fun x => onAnySess fsInjQ x = true) q :=
  (redFSAuthDFPaperMulti_dec_pub cka prng fs lam q Δcka qep tL t la A hq).of_imp
    fun x hx => by rcases x with _ | ⟨_, _ | _⟩ <;> exact hx

/-- Total decryption-query bound (`onAnySess fsInjQ ≤ q`) on `redFSAuthDFPaperMultiBucket`. -/
theorem redFSAuthDFPaperMultiBucket_dec_onAnySess
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (q Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par la : Bool)
    (A : SchemeAdversaryDF Γ T RSt SS RS M CCoins E)
    (hq : MakesAtMostQueriesDF A q) :
    (redFSAuthDFPaperMultiBucket L cka prng fs lam Δcka Δbucket qep la tL par A).IsQueryBoundP
      (fun x => onAnySess fsInjQ x = true) q :=
  (redFSAuthDFPaperMultiBucket_dec_pub L cka prng fs lam q Δcka Δbucket qep tL par la A hq).of_imp
    fun x hx => by rcases x with _ | ⟨_, _ | _⟩ <;> exact hx

end DecBound

end

end Computational.Proofs.E2E.SessionAuthMultiDec
