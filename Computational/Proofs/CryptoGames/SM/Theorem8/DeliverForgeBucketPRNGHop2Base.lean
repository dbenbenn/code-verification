/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGDefs -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperCKA
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFS
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma10Aux
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma10
import Computational.Proofs.CryptoGames.SM.Theorem1.Lemma17Aux
import VCVio.OracleComp.EvalDist.Measure
import VCVio.EvalDist.EvalDistEq
import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.OracleComp.SimSemantics.StateT.StateProjection
import VCVio.ProgramLogic.Unary.HoareTriple

/-!
# Hop-2 Base (`t = healEpoch tL`) for `(tL, par)` Bucket `DeliverForge` PRNG Hybrid

Couples `CKA.branch cka Δcka (healEpoch tL) true (redCKAAuthDF{,Paper}Bucket ...)` against
`PRFPRNG.branch prng false (redPRNGAuthDF{,Paper}BucketHybrid ... (healEpoch tL) ...)` by reusing
`AuthL10.Sync` at `moBase tL = ⟨true, tL, healEpoch tL⟩`.-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

public section

open OracleSpec OracleComp ENNReal MeasureTheory
open CryptoGames CryptoGames.CKA CryptoGames.PRFPRNG CryptoGames.FSAEAD CryptoGames.SM
open CryptoGames.SM.Engine CryptoGames.SM.Construction

namespace CryptoGames.SM.Construction.DeliverForge

section BaseCoupling

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {KC Γ CCoins T I KR Sig K SS RS M E : Type}

private def moBase (tL : Option ℕ) : Mode :=
  ⟨true, tL, healEpoch tL⟩

private def toEStateP
    (esB : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)) :
    AuthL10.EStateP Γ T Sig SS RS M E K :=
  { g := esB.g, h := { cache := esB.h.cache }, abort := esB.abort }

private theorem estateB_mk_abort_false
    {esB : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    (h : esB.abort = false) :
    ({ g := esB.g, h := esB.h, abort := false } :
      EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)) = esB := by
  cases esB
  simp_all

@[local simp]
private theorem healEpoch_none_eq : healEpoch none = 0 := rfl

@[local simp]
private theorem healEpoch_some_eq (l : ℕ) : healEpoch (some l) = l + 2 := rfl

@[local simp]
private theorem moBase_auth (tL : Option ℕ) : (moBase tL).auth = true := rfl

@[local simp]
private theorem moBase_tL (tL : Option ℕ) : (moBase tL).tL = tL := rfl

@[local simp]
private theorem moBase_tStar (tL : Option ℕ) : (moBase tL).tStar = healEpoch tL := rfl

@[local simp]
private theorem moBase_tH (tL : Option ℕ) : (moBase tL).tH = healEpoch tL := by
  cases tL <;> rfl

private theorem knownRoot_moBase (tL : Option ℕ) (e : ℕ) :
    AuthL10.knownRoot (moBase tL) e = true := by
  cases tL with
  | none =>
    simp [AuthL10.knownRoot, moBase, Mode.tH]
  | some l =>
    by_cases hlt : e < l + 2
    · simp [AuthL10.knownRoot, moBase, Mode.tH, hlt]
    · have hle : l + 2 ≤ e := Nat.le_of_not_lt hlt
      simp [AuthL10.knownRoot, moBase, Mode.tH, hle]

private theorem root_P_moBase
    {prng : PRFPRNG KR Sig I K} {Δcka : ℕ} {tL : Option ℕ}
    {esC : AuthL10.EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esB : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : AuthL10.Sync prng Δcka (moBase tL) esC sc (toEStateP esB) sp) (P : Party) :
    (esB.g.st P).root = some (esC.g.st P).root := by
  have hr := hS.root_P P
  rw [knownRoot_moBase] at hr
  exact hr

private theorem inStage2Bucket_localCKA_and_gt {Δcka : ℕ} {tL : Option ℕ} {par : Bool} {ep : ℕ}
    (hb : inStage2Bucket Δcka tL par (ep + 1) = true) :
    AuthL10.localCKA (moBase tL) Δcka ep = true ∧
      healEpoch tL < ep + 1 ∧
      (tL.isSome && decide (ep + 1 = healEpoch tL)) = false := by
  unfold inStage2Bucket at hb
  rw [Bool.and_eq_true] at hb
  cases tL with
  | none =>
    simp [moBase, AuthL10.localCKA, healEpoch]
  | some l =>
    have hadm := hb.1
    simp [lastLeakGuessAdmissible, healedBy] at hadm
    have hle1 : l + 2 + Δcka ≤ ep := by omega
    have hlt2 : l + 2 < ep + 1 := by omega
    have hne3 : ep ≠ l + 1 := by omega
    refine ⟨?_, ?_, ?_⟩
    · simp [AuthL10.localCKA, moBase, Mode.tH, hle1]
    · simpa [healEpoch] using hlt2
    · simp [healEpoch, hne3]

private def StepRelBaseRaw
    (prng : PRFPRNG KR Sig I K) (Δcka : ℕ) (tL : Option ℕ) {α : Type}
    (x : (α × AuthL10.EStateC Γ T Sig SS RS M E I) × CKA.GameState Γ T)
    (y : (α × EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)) ×
      PRFPRNG.GameState Sig I K) : Prop :=
  x.1.2.abort = true ∨
    (x.1.1 = y.1.1 ∧ AuthL10.Sync prng Δcka (moBase tL) x.1.2 x.2 (toEStateP y.1.2) y.2)

private theorem leComp_pure_sync {prng : PRFPRNG KR Sig I K} {Δcka : ℕ} {tL : Option ℕ} {α : Type}
    {lhs : ProbComp ((α × AuthL10.EStateC Γ T Sig SS RS M E I) × CKA.GameState Γ T)}
    {rhs : ProbComp
      ((α × EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)) ×
        PRFPRNG.GameState Sig I K)}
    (u : α) {esC' : AuthL10.EStateC Γ T Sig SS RS M E I} {sc' : CKA.GameState Γ T}
    {esB' : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {sp' : PRFPRNG.GameState Sig I K}
    (hS' : AuthL10.Sync prng Δcka (moBase tL) esC' sc' (toEStateP esB') sp')
    (hL : lhs = pure ((u, esC'), sc'))
    (hR : rhs = pure ((u, esB'), sp')) :
    AuthL11.LeComp (StepRelBaseRaw prng Δcka tL) lhs rhs := by
  rw [hL, hR]
  exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hS'⟩)

@[local simp]
private theorem hooksCKABucket_fsRecv
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (tL : Option ℕ) (par : Bool)
    (ctx : Ctx (Option Γ) T Sig SS RS M E) (P : Party) (m : ℕ)
    (rs : RS) (h : Header T) (e : E) (rec : Option (SM.Record M (Header T × E))) :
    (hooksCKABucket cka prng fs Δcka tL par).fsRecv ctx P m rs h e rec =
      pure (some (fs.receive rs h e)) := rfl

@[local simp]
private theorem hooksCKABucket_commit
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (tL : Option ℕ) (par : Bool)
    (ctx : Ctx (Option Γ) T Sig SS RS M E) (P : Party)
    (old new : VP (Option Γ) T Sig SS RS) :
    (hooksCKABucket cka prng fs Δcka tL par).commit ctx P old new =
      (hooksCKA cka prng fs Δcka (moBase tL)).commit ctx P old new := rfl

@[local simp]
private theorem hooksCKABucket_fsSend
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (tL : Option ℕ) (par : Bool)
    (ctx : Ctx (Option Γ) T Sig SS RS M E) (P : Party) (m : ℕ)
    (ss : SS) (h : Header T) (msg : M) (pair : Option (M × M)) :
    (hooksCKABucket cka prng fs Δcka tL par).fsSend ctx P m ss h msg pair =
      pure (some (fs.send ss h msg)) := rfl

@[local simp]
private theorem hooksCKABucket_startSend
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (tL : Option ℕ) (par : Bool) :
    (hooksCKABucket cka prng fs Δcka tL par).startSend =
      (hooksCKA cka prng fs Δcka (moBase tL)).startSend := rfl

@[local simp]
private theorem hooksPRNGBucketHybrid_fsRecv
    [DecidableEq T] [DecidableEq I] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party) (m : ℕ)
    (rs : RS) (h : Header T) (e : E) (rec : Option (SM.Record M (Header T × E))) :
    (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t).fsRecv ctx P m rs h e rec =
      pure (some (fs.receive rs h e)) := rfl

@[local simp]
private theorem hooksPRNGBucketHybrid_commit
    [DecidableEq T] [DecidableEq I] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party)
    (old new : VP Γ T (Option Sig) SS RS) :
    (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t).commit ctx P old new =
      pure (some new) := rfl

@[local simp]
private theorem hooksPRNGBucketHybrid_fsSend
    [DecidableEq T] [DecidableEq I] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party) (m : ℕ)
    (ss : SS) (h : Header T) (msg : M) (pair : Option (M × M)) :
    (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t).fsSend ctx P m ss h msg pair =
      pure (some (fs.send ss h msg)) := rfl

private theorem hooksPRNGBucketHybrid_reveal_some_run
    [DecidableEq T] [DecidableEq I] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party)
    (vp : VP Γ T (Option Sig) SS RS) (σ : Sig) (hroot : vp.root = some σ)
    (h0 : PRNGBucketState T Sig K I) :
    ((hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t).reveal ctx P vp).run h0 =
      pure (some (realParty vp vp.γ σ vp.vS vp.vR),
        let h1 := if !(vp.tcur < healEpoch tL) && h0.corrRoot.isNone then
          { h0 with corrRoot := some (vp.tcur, σ) } else h0
        if !(postLeak tL ctx) && h0.lc.isNone && !(vp.tcur < healEpoch tL) then
          { h1 with lc := some vp.tcur } else h1) := by
  dsimp only [hooksPRNGBucketHybrid, hooksPRNGBucketHybridGen]
  rw [hroot]
  dsimp only [resolveCorrRoot]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs <;>
    simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, StateT.run_map,
      pure_bind, map_pure]

private theorem hooksCKABucket_startRecv_honest
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (tL : Option ℕ) (par : Bool)
    (ctx : Ctx (Option Γ) T Sig SS RS M E) (P : Party) (m : ℕ)
    (γv : Option Γ) (σ : Sig) (Tm : T) (Im : I) (h : CKAState T I)
    (hc : h.cache m = some (Tm, Im)) :
    ((hooksCKABucket cka prng fs Δcka tL par).startRecv ctx P m γv σ Tm).run h =
      pure (some (some (γv.map fun γ => (cka.receive γ Tm).1,
        (prng.up σ Im).1, fs.initReceiver (prng.up σ Im).2)), h) := by
  simp [hooksCKABucket, hc, StateT.run_bind, StateT.run_get, StateT.run_pure]

private theorem hooksPRNGBucketHybrid_startRecv_honest
    [DecidableEq T] [DecidableEq I] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party) (m : ℕ)
    (γ0 : Γ) (σv0 : Option Sig) (Tm : T) (σc : Option Sig) (kVal : K)
    (h : PRNGBucketState T Sig K I)
    (hc : h.cache m = some (Tm, σc, kVal))
    (hσc : ∃ σ, σc = some σ) :
    ((hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t).startRecv ctx P m γ0 σv0 Tm).run h =
      pure (some (some ((cka.receive γ0 Tm).1, σc, fs.initReceiver kVal)), h) := by
  rcases hσc with ⟨σ, rfl⟩
  simp [hooksPRNGBucketHybrid, hooksPRNGBucketHybridGen, resolveCorrRoot, hc,
    StateT.run_bind, StateT.run_get, StateT.run_pure]

private theorem hooksCKABucket_startRecv_unhonest
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (tL : Option ℕ) (par : Bool)
    (ctx : Ctx (Option Γ) T Sig SS RS M E) (P : Party) (m : ℕ)
    (γv : Option Γ) (σ : Sig) (Tn : T) (h : CKAState T I)
    (hc : ∀ Im, h.cache m ≠ some (Tn, Im)) :
    ((hooksCKABucket cka prng fs Δcka tL par).startRecv ctx P m γv σ Tn).run h =
      pure (if inStage2Bucket Δcka tL par m then
        match γv with
        | some γ =>
          let k := cka.receive γ Tn
          let p := prng.up σ k.2
          some (some (some k.1, p.1, fs.initReceiver p.2))
        | none => none
      else some none, h) := by
  cases hcm : h.cache m with
  | none =>
    simp [hooksCKABucket, hcm, StateT.run_bind, StateT.run_get]
    split <;> cases γv <;> rfl
  | some pair =>
    rcases pair with ⟨Tc, Ik⟩
    have hne : Tc ≠ Tn := fun heq => hc Ik (heq ▸ hcm)
    simp [hooksCKABucket, hcm, hne, StateT.run_bind, StateT.run_get]
    split <;> cases γv <;> rfl

private theorem hooksPRNGBucketHybrid_startRecv_unhonest_base
    [DecidableEq T] [DecidableEq I] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party) (ep : ℕ)
    (γ0 : Γ) (σv0 : Option Sig) (Tn : T) (h : PRNGBucketState T Sig K I)
    (hc : ∀ σc k, h.cache (ep + 1) ≠ some (Tn, σc, k))
    (hσv0 : ∃ σ, σv0 = some σ) :
    ((hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL)).startRecv
      ctx P (ep + 1) γ0 σv0 Tn).run h =
      pure (if !(qep + 1 < ep + 1) && inStage2Bucket Δcka tL par (ep + 1) then
        match σv0 with
        | none => none
        | some σ =>
          let kk := cka.receive γ0 Tn
          let p := prng.up σ kk.2
          some (some (kk.1, some p.1, fs.initReceiver p.2))
      else some none, h) := by
  rcases hσv0 with ⟨σ, rfl⟩
  have hguard_eq :
      (lastLeakGuessAdmissible (3 + Δcka) tL (ep + 1) && (partyPar (Party.senderOf (ep + 1)) == par)) =
        inStage2Bucket Δcka tL par (ep + 1) := rfl
  cases hcm : h.cache (ep + 1) with
  | none =>
    simp only [hooksPRNGBucketHybrid, hooksPRNGBucketHybridGen, hcm, StateT.run_bind,
      StateT.run_get, pure_bind, hguard_eq]
    by_cases hb : inStage2Bucket Δcka tL par (ep + 1) = true
    · obtain ⟨_, hgt, hnot_tH⟩ := inStage2Bucket_localCKA_and_gt hb
      by_cases hqep : qep + 1 < ep + 1
      · simp [hb, hqep]
      · have hnot_eq : ¬(tL.isSome = true ∧ ep + 1 = healEpoch tL) := by
          simpa [Bool.and_eq_false_iff, decide_eq_false_iff_not] using hnot_tH
        simp [hb, hqep, hgt, hnot_eq, resolveCorrRoot]
    · simp [hb]
  | some tup =>
    rcases tup with ⟨Tc, σc, kVal⟩
    have hne : Tc ≠ Tn := fun heq => hc σc kVal (heq ▸ hcm)
    simp only [hooksPRNGBucketHybrid, hooksPRNGBucketHybridGen, hcm, hne, ↓reduceIte,
      StateT.run_bind, StateT.run_get, pure_bind, hguard_eq]
    by_cases hb : inStage2Bucket Δcka tL par (ep + 1) = true
    · obtain ⟨_, hgt, hnot_tH⟩ := inStage2Bucket_localCKA_and_gt hb
      by_cases hqep : qep + 1 < ep + 1
      · simp [hb, hqep]
      · have hnot_eq : ¬(tL.isSome = true ∧ ep + 1 = healEpoch tL) := by
          simpa [Bool.and_eq_false_iff, decide_eq_false_iff_not] using hnot_tH
        simp [hb, hqep, hgt, hnot_eq, resolveCorrRoot]
    · simp [hb]

private theorem max_epoch_other_le_succ
    {prng : PRFPRNG KR Sig I K} {Δcka : ℕ} {mo : Mode}
    {esC : AuthL10.EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esP : AuthL10.EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    (hS : AuthL10.Sync prng Δcka mo esC sc esP sp) (P : Party) :
    esC.g.epoch P.other ≤ esC.g.epoch P + 1 := by
  rcases hS.ping_pong with ⟨hR, _⟩ | ⟨_, hR, _⟩
  · have hepP := AuthL10.epoch_eq_of_synced hS.epoch_S hR P
    have hepO := AuthL10.epoch_eq_of_synced hS.epoch_S hR P.other
    omega
  · rcases AuthL10.party_cases_of_epoch (max (esC.g.epoch .A) (esC.g.epoch .B)) P with hP | hP
    · have hO : P.other = Party.receiverOf (max (esC.g.epoch .A) (esC.g.epoch .B)) := by
        rw [hP, AuthL10.senderOf_other]
      have hS_ep := hS.epoch_S
      rw [← hP] at hS_ep; rw [← hO] at hR; omega
    · have hO : Party.other P = Party.senderOf (max (esC.g.epoch .A) (esC.g.epoch .B)) := by
        rw [hP, AuthL10.receiverOf_other]
      have hS_ep := hS.epoch_S
      rw [← hO] at hS_ep; rw [← hP] at hR; omega

private theorem run_commitE_CKABucket_new
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (tL : Option ℕ) (par : Bool)
    {esC : AuthL10.EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esB : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : AuthL10.Sync prng Δcka (moBase tL) esC sc (toEStateP esB) sp)
    (P : Party) (Tm : T) (vR' : ℕ → Option RS) (pos : SM.Pos)
    (hr_ep : pos.epoch = esC.g.epoch P + 1)
    (hO_ep : esC.g.epoch P.other = esC.g.epoch P + 1)
    (hlast : AuthL10.localCKA (moBase tL) Δcka (esC.g.epoch P) = false → sc.lastMsg = some Tm) :
    ∃ sc',
      ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
        ((commitE (hooksCKABucket cka prng fs Δcka tL par) esC.g P (esC.g.st P)
          ({ esC.g.st P with
            tcur := esC.g.epoch P + 1
            γ := (esC.g.st P).γ.map fun γ => (cka.receive γ Tm).1
            root := (esC.g.st P.other).root
            vR := vR' }) pos).run esC)).run sc) =
        pure ((some (esC.g.accept P
          ({ esC.g.st P with
            tcur := esC.g.epoch P + 1
            γ := if AuthL10.localCKA (moBase tL) Δcka (esC.g.epoch P + 1)
              then some (cka.receive (esB.g.st P).γ Tm).1 else none
            root := (esC.g.st P.other).root
            vR := vR' }) pos), esC), sc') ∧
      AuthL10.Sync prng Δcka (moBase tL)
        { esC with
          g := esC.g.accept P
            ({ esC.g.st P with
              tcur := esC.g.epoch P + 1
              γ := if AuthL10.localCKA (moBase tL) Δcka (esC.g.epoch P + 1)
                then some (cka.receive (esB.g.st P).γ Tm).1 else none
              root := (esC.g.st P.other).root
              vR := vR' }) pos } sc'
        (toEStateP { esB with
          g := esB.g.accept P
            ({ esB.g.st P with
              tcur := esC.g.epoch P + 1
              γ := (cka.receive (esB.g.st P).γ Tm).1
              root := (esB.g.st P.other).root
              vR := vR' }) pos }) sp := by
  let m := esC.g.epoch P + 1
  let γP' := (cka.receive (esB.g.st P).γ Tm).1
  by_cases hloc : AuthL10.localCKA (moBase tL) Δcka (esC.g.epoch P) = true
  · have hloc_m : AuthL10.localCKA (moBase tL) Δcka m = true :=
      AuthL10.localCKA_mono (moBase tL) Δcka hloc (Nat.le_succ _)
    have hγC : (esC.g.st P).γ = some (esB.g.st P).γ := by rw [hS.γ_C P, hloc]; rfl
    refine ⟨sc, ?_, hS.accept_new P γP' vR' pos hr_ep hO_ep hS.b_C
      (fun h => by simp [m, hloc_m] at h)⟩
    simp [-Prod.mk.injEq, commitE, hooksCKA, hS.tcur_C P, hγC, hloc_m, m, γP',
      StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure]
  · simp only [Bool.not_eq_true] at hloc
    have hγC : (esC.g.st P).γ = none := by rw [hS.γ_C P, hloc]; rfl
    obtain ⟨hsc_stP, hsc_epP⟩ := hS.cka_st P (Or.inl hloc)
    obtain ⟨hsc_stO, hsc_epO⟩ := hS.cka_st P.other (Or.inr (by simpa using hloc))
    have hcanR : sc.canReceive P = true := by
      simp [CKA.GameState.canReceive, hsc_epO, hsc_epP, hO_ep]
    have hlast_eq : sc.lastMsg = some Tm := hlast hloc
    let sc' := sc.afterReceive P γP'
    have htL_none : (moBase tL).tL.isNone = false := by
      simp only [AuthL10.localCKA, Bool.or_eq_false_iff] at hloc
      exact hloc.1
    by_cases hfin : (moBase tL).tH + Δcka ≤ m
    · have hloc_m : AuthL10.localCKA (moBase tL) Δcka m = true := by
        simp only [AuthL10.localCKA, Bool.or_eq_true, decide_eq_true_eq]
        exact Or.inr hfin
      refine ⟨sc', ?_, hS.accept_new (sc' := sc') P γP' vR' pos hr_ep hO_ep hS.b_C
        (fun h => by simp [m, hloc_m] at h)⟩
      have hfin' : healEpoch tL + Δcka ≤ m := hfin
      simp [-Prod.mk.injEq, commitE, hooksCKA, liftC, CKA.receiveQuery, CKA.corrQuery,
        AuthL10.cImpl, CKA.oracleImpl, CKA.receiveImpl, CKA.corrImpl, toEStateP,
        hS.tcur_C P, hγC, hcanR, hlast_eq, hsc_stP, hfin', hloc_m, sc',
        CKA.GameState.afterReceive, CKA.GameState.finished, hsc_epP, m, γP',
        StateT.lift, simulateQ_bind, simulateQ_query, simulateQ_pure,
        map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure]
    · have hloc_m : AuthL10.localCKA (moBase tL) Δcka m = false := by
        simp only [AuthL10.localCKA, Bool.or_eq_false_iff, decide_eq_false_iff_not]
        exact ⟨htL_none, hfin⟩
      refine ⟨sc', ?_, hS.accept_new (sc' := sc') P γP' vR' pos hr_ep hO_ep hS.b_C fun _ => ?_⟩
      · have hfin' : ¬(healEpoch tL + Δcka ≤ m) := hfin
        simp [-Prod.mk.injEq, commitE, hooksCKA, liftC, CKA.receiveQuery, AuthL10.cImpl,
          CKA.oracleImpl, CKA.receiveImpl, toEStateP,
          hS.tcur_C P, hγC, hcanR, hlast_eq, hsc_stP, hfin', hloc_m, sc', m, γP',
          StateT.lift, simulateQ_bind, simulateQ_query, simulateQ_pure,
          map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure]
      · simp [sc', CKA.GameState.afterReceive, Party.other_ne, hsc_epP, hsc_stO, hsc_epO, hO_ep, m]

private theorem leComp_deliverE_base
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (arg : Party × (Header T × E))
    {esC : AuthL10.EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esB : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : AuthL10.Sync prng Δcka (moBase tL) esC sc (toEStateP esB) sp) :
    AuthL11.LeComp (StepRelBaseRaw prng Δcka tL)
      ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
        ((deliverE (hooksCKABucket cka prng fs Δcka tL par) fs.maxSkip
          (bucketAuthCfg Δcka tL par) arg).run esC)).run sc)
      ((simulateQ (AuthL10.pImpl prng)
        ((deliverE (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL)) fs.maxSkip
          (bucketAuthCfg Δcka tL par) arg).run esB)).run sp) := by
  rcases arg with ⟨P, c⟩
  have habC : esC.abort = false := hS.abort_C
  have habB : esB.abort = false := hS.abort_P
  have hwin : esB.g.win = esC.g.win := AuthL10.eraseSt_win hS.g_eq
  have htrans : esB.g.inTransit P.other c = esC.g.inTransit P.other c :=
    AuthL10.eraseSt_inTransit hS.g_eq P.other c
  have hchall : esB.g.chall = esC.g.chall := AuthL10.eraseSt_chall hS.g_eq
  have hcfg_win : (bucketAuthCfg Δcka tL par : SM.Config M).deliverWin = false := rfl
  have hesC_eq := AuthL10.estate_mk_abort_false habC
  have hesB_eq := estateB_mk_abort_false habB
  have hidB : (esB.g.st P).id = P := hS.id_P P
  have htcurB : (esB.g.st P).tcur = esC.g.epoch P := hS.tcur_P P
  by_cases hwin0 : esC.g.win = true
  · exact leComp_pure_sync none hS
      (by simp [-Prod.mk.injEq, deliverE, habC, hwin0])
      (by simp [-Prod.mk.injEq, deliverE, habB, hwin, hwin0])
  · simp only [Bool.not_eq_true] at hwin0
    cases hr : esC.g.inTransit P.other c with
    | none =>
      exact leComp_pure_sync none hS
        (by simp [-Prod.mk.injEq, deliverE, habC, hwin0, hr])
        (by simp [-Prod.mk.injEq, deliverE, habB, hwin, hwin0, htrans, hr])
    | some r =>
      obtain ⟨hmem, hsender, hct⟩ := AuthL10.inTransit_some_props hr
      obtain ⟨ht1, hsend_other, hle_other, _⟩ := hS.trans_inv r hmem
      rw [hct] at ht1; rw [hsender] at hsend_other hle_other
      have hsend0 : P.sendsIn c.1.1 = false := by
        rw [ht1]; have h1 := AuthL10.sendsIn_other P r.pos.epoch; rw [hsend_other] at h1
        simpa using h1.symm
      have hmax_bound := max_epoch_other_le_succ hS P
      have hle : ¬ (esC.g.epoch P + 1 < c.1.1) := by omega
      by_cases hnew : c.1.1 = esC.g.epoch P + 1
      · have hsend0' : P.sendsIn (esC.g.epoch P + 1) = false := hnew ▸ hsend0
        obtain ⟨hr_ep, _, _, hO_ep, _, Tm, Im, hct2, hcC, _, hSroot, hcP, hlast⟩ :=
          hS.deliver_new_info hr hnew
        let p := prng.up (esC.g.st P).root Im
        have hp1 : (prng.up (esC.g.st P).root Im).1 = (esC.g.st P.other).root := hSroot.symm
        have hcB : esB.h.cache (esC.g.epoch P + 1) = some (Tm, (esB.g.st P.other).root, p.2) := hcP
        have hstartC := fun ctx γv =>
          hooksCKABucket_startRecv_honest cka prng fs Δcka tL par ctx P (esC.g.epoch P + 1) γv
            (esC.g.st P).root Tm Im esC.h hcC
        have hstartB := fun ctx =>
          hooksPRNGBucketHybrid_startRecv_honest cka prng fs Δcka qep tL par (healEpoch tL)
            ctx P (esC.g.epoch P + 1) (esB.g.st P).γ (esB.g.st P).root Tm
            (esB.g.st P.other).root p.2 esB.h hcB ⟨_, root_P_moBase hS P.other⟩
        cases hfs : fs.receive (fs.initReceiver p.2) c.1 c.2 with
        | none =>
          exact leComp_pure_sync (some .rejected) hS
            (by simp [-Prod.mk.injEq, deliverE, vRecv, habC, hwin0, hr, hcfg_win,
              hS.id_C P, hS.tcur_C P, hsend0', hnew, hct2, hstartC, hp1, p, hfs,
              StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure, hesC_eq])
            (by simp [-Prod.mk.injEq, deliverE, vRecv, habB, hwin, hwin0, htrans, hr,
              hcfg_win, hidB, htcurB, hsend0', hnew, hct2, hstartB, hfs,
              StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure, hesB_eq])
        | some vim =>
          rcases vim with ⟨v', i', m'⟩
          let m := esC.g.epoch P + 1
          let vR' := Function.update (esC.g.st P).vR m (some v')
          have hvRB : (esB.g.st P).vR = (esC.g.st P).vR := hS.vR_eq P
          obtain ⟨sc', hcommitC, hS'⟩ :=
            run_commitE_CKABucket_new cka prng fs Δcka tL par hS P Tm vR' r.pos hr_ep hO_ep hlast
          have hcommitC' :
              ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
                ((commitE (hooksCKABucket cka prng fs Δcka tL par) esC.g P (esC.g.st P)
                  { id := P, root := (esC.g.st P.other).root, vS := (esC.g.st P).vS,
                    vR := Function.update (esC.g.st P).vR (esC.g.epoch P + 1) (some v'),
                    γ := Option.map (fun γ => (cka.receive γ Tm).1) (esC.g.st P).γ,
                    curCkaMsg := (esC.g.st P).curCkaMsg, tcur := esC.g.epoch P + 1 }
                  r.pos).run esC)).run sc) =
                pure ((some (esC.g.accept P
                  { id := P, root := (esC.g.st P.other).root, vS := (esC.g.st P).vS,
                    vR := Function.update (esC.g.st P).vR (esC.g.epoch P + 1) (some v'),
                    γ := if AuthL10.localCKA (moBase tL) Δcka (esC.g.epoch P + 1) = true
                      then some (cka.receive (esB.g.st P).γ Tm).1 else none,
                    curCkaMsg := (esC.g.st P).curCkaMsg, tcur := esC.g.epoch P + 1 } r.pos),
                  esC), sc') := by
            simpa [hS.id_C P, vR', m] using hcommitC
          exact leComp_pure_sync
            (esC' := { esC with
              g := esC.g.accept P
                ({ esC.g.st P with
                  tcur := esC.g.epoch P + 1
                  γ := if AuthL10.localCKA (moBase tL) Δcka (esC.g.epoch P + 1)
                    then some (cka.receive (esB.g.st P).γ Tm).1 else none
                  root := (esC.g.st P.other).root
                  vR := vR' }) r.pos })
            (esB' := { esB with
              g := esB.g.accept P
                ({ esB.g.st P with
                  tcur := esC.g.epoch P + 1
                  γ := (cka.receive (esB.g.st P).γ Tm).1
                  root := (esB.g.st P.other).root
                  vR := vR' }) r.pos })
            (some (.accepted m i' (if esC.g.chall.contains r.pos then none else some m'))) hS'
            (by simp [-Prod.mk.injEq, deliverE, vRecv, habC, hwin0, hr, hcfg_win,
              hS.id_C P, hS.tcur_C P, hsend0', hnew, hct2, hstartC, hp1, p, hfs, m, vR',
              StateT.run_bind, StateT.run_pure, StateT.run_modify, simulateQ_bind, simulateQ_pure,
              hcommitC', hesC_eq])
            (by simp [-Prod.mk.injEq, deliverE, commitE, vRecv, habB, hwin, hwin0, htrans,
              hr, hcfg_win, hchall, hidB, htcurB, hsend0', hnew, hct2, hvRB, hstartB, hfs, m, vR',
              StateT.run_bind, StateT.run_pure, StateT.run_modify, simulateQ_bind, simulateQ_pure])
      · have hle_ep : r.pos.epoch ≤ esC.g.epoch P := by omega
        have hvRB : (esB.g.st P).vR c.1.1 = (esC.g.st P).vR c.1.1 := congrFun (hS.vR_eq P) _
        cases hvR : (esC.g.st P).vR c.1.1 with
        | none =>
          exact leComp_pure_sync (some .rejected) hS
            (by simp [-Prod.mk.injEq, deliverE, vRecv, habC, hwin0, hr, hcfg_win,
              hS.id_C P, hS.tcur_C P, hsend0, hle, hnew, hvR, StateT.run_pure, hesC_eq])
            (by simp [-Prod.mk.injEq, deliverE, vRecv, habB, hwin, hwin0, htrans, hr,
              hcfg_win, hidB, htcurB, hsend0, hle, hnew, hvRB, hvR, StateT.run_pure, hesB_eq])
        | some v =>
          cases hfs : fs.receive v c.1 c.2 with
          | none =>
            exact leComp_pure_sync (some .rejected) hS
              (by simp [-Prod.mk.injEq, deliverE, vRecv, habC, hwin0, hr, hcfg_win,
                hS.id_C P, hS.tcur_C P, hsend0, hle, hnew, hvR, hfs, StateT.run_pure, hesC_eq])
              (by simp [-Prod.mk.injEq, deliverE, vRecv, habB, hwin, hwin0, htrans, hr,
                hcfg_win, hidB, htcurB, hsend0, hle, hnew, hvRB, hvR, hfs,
                StateT.run_pure, hesB_eq])
          | some vim =>
            rcases vim with ⟨v', i', m'⟩
            let vR' := Function.update (esC.g.st P).vR c.1.1 (some v')
            have hvRB_all : (esB.g.st P).vR = (esC.g.st P).vR := hS.vR_eq P
            exact leComp_pure_sync
              (esC' := { esC with g := esC.g.accept P { esC.g.st P with vR := vR' } r.pos })
              (esB' := { esB with g := esB.g.accept P { esB.g.st P with vR := vR' } r.pos })
              (some (.accepted c.1.1 i' (if esC.g.chall.contains r.pos then none else some m')))
              (hS.accept_old P vR' r.pos hle_ep)
              (by simp [-Prod.mk.injEq, deliverE, commitE, hooksCKA, vRecv, habC, hwin0, hr,
                hcfg_win, hS.id_C P, hS.tcur_C P, hsend0, hle, hnew, hvR, hfs, vR',
                StateT.run_pure, StateT.run_modify])
              (by simp [-Prod.mk.injEq, deliverE, commitE, vRecv, habB, hwin, hwin0, htrans,
                hr, hcfg_win, hchall, hidB, htcurB, hsend0, hle, hnew, hvRB, hvR, hfs, hvRB_all,
                vR', StateT.run_pure, StateT.run_modify])

set_option maxHeartbeats 400000 in
private theorem leComp_deliverForgeE_base
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (df : Party × (Header T × E) × (Header T × E))
    {esC : AuthL10.EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esB : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : AuthL10.Sync prng Δcka (moBase tL) esC sc (toEStateP esB) sp) :
    AuthL11.LeComp (StepRelBaseRaw prng Δcka tL)
      ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
        ((deliverForgeE (hooksCKABucket cka prng fs Δcka tL par) (2 + Δcka) qep
          (bucketAuthCfg Δcka tL par) df).run esC)).run sc)
      ((simulateQ (AuthL10.pImpl prng)
        ((deliverForgeE (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
          (2 + Δcka) qep (bucketAuthCfg Δcka tL par) df).run esB)).run sp) := by
  rcases df with ⟨P, c, c'⟩
  have habC : esC.abort = false := hS.abort_C
  have habB : esB.abort = false := hS.abort_P
  have hwin : esB.g.win = esC.g.win := AuthL10.eraseSt_win hS.g_eq
  have htrans_c : esB.g.inTransit P.other c = esC.g.inTransit P.other c :=
    AuthL10.eraseSt_inTransit hS.g_eq P.other c
  have htrans_c' : esB.g.inTransit P.other c' = esC.g.inTransit P.other c' :=
    AuthL10.eraseSt_inTransit hS.g_eq P.other c'
  have hcomp : esB.g.comp = esC.g.comp := AuthL10.eraseSt_comp hS.g_eq
  have hesC_eq := AuthL10.estate_mk_abort_false habC
  have hesB_eq := estateB_mk_abort_false habB
  by_cases hwin0 : esC.g.win = true
  · have hC :
        ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
          ((deliverForgeE (hooksCKABucket cka prng fs Δcka tL par) (2 + Δcka) qep
            (bucketAuthCfg Δcka tL par) (P, c, c')).run esC)).run sc) =
          pure ((none, esC), sc) := by
      simp [deliverForgeE, habC, hwin0]
    have hB :
        ((simulateQ (AuthL10.pImpl prng)
          ((deliverForgeE (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
            (2 + Δcka) qep (bucketAuthCfg Δcka tL par) (P, c, c')).run esB)).run sp) =
          pure ((none, esB), sp) := by
      simp [deliverForgeE, habB, hwin, hwin0]
    rw [hC, hB]
    exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hS⟩)
  · simp only [Bool.not_eq_true] at hwin0
    cases hr : esC.g.inTransit P.other c with
    | none =>
      have hC :
          ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
            ((deliverForgeE (hooksCKABucket cka prng fs Δcka tL par) (2 + Δcka) qep
              (bucketAuthCfg Δcka tL par) (P, c, c')).run esC)).run sc) =
            pure ((none, esC), sc) := by
        simp [deliverForgeE, habC, hwin0, hr]
      have hB :
          ((simulateQ (AuthL10.pImpl prng)
            ((deliverForgeE (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
              (2 + Δcka) qep (bucketAuthCfg Δcka tL par) (P, c, c')).run esB)).run sp) =
            pure ((none, esB), sp) := by
        simp [deliverForgeE, habB, hwin, hwin0, htrans_c, hr]
      rw [hC, hB]
      exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hS⟩)
    | some r =>
      by_cases hguard :
          ((esC.g.inTransit P.other c').isSome || esC.g.comp.contains r.pos || c.1 != c'.1) = true
      · simp only [Bool.or_eq_true, List.contains_iff_mem, bne_iff_ne] at hguard
        have hC :
            ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
              ((deliverForgeE (hooksCKABucket cka prng fs Δcka tL par) (2 + Δcka) qep
                (bucketAuthCfg Δcka tL par) (P, c, c')).run esC)).run sc) =
              pure ((none, esC), sc) := by
          simp [deliverForgeE, habC, hwin0, hr, hguard, StateT.run_pure]
        have hB :
            ((simulateQ (AuthL10.pImpl prng)
              ((deliverForgeE (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
                (2 + Δcka) qep (bucketAuthCfg Δcka tL par) (P, c, c')).run esB)).run sp) =
              pure ((none, esB), sp) := by
          simp [deliverForgeE, habB, hwin, hwin0, htrans_c, hr, htrans_c', hcomp, hguard,
            StateT.run_pure]
        rw [hC, hB]
        exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hS⟩)
      · simp only [Bool.not_eq_true, Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hguard
        rcases hguard with ⟨⟨htrans0, hcomp0⟩, hhdr⟩
        have hcomp0' : r.pos ∉ esC.g.comp := by simpa using hcomp0
        have hhdr' : c'.1 = c.1 := hhdr.symm
        obtain ⟨hmem, hsender, hct⟩ := AuthL10.inTransit_some_props hr
        obtain ⟨ht1, hsend_other, hle_other, _⟩ := hS.trans_inv r hmem
        rw [hct] at ht1
        rw [hsender] at hsend_other hle_other
        have hsend0 : P.sendsIn c'.1.1 = false := by
          rw [hhdr', ht1]
          have h1 := AuthL10.sendsIn_other P r.pos.epoch
          rw [hsend_other] at h1
          simpa using h1.symm
        have hmax_bound : esC.g.epoch P.other ≤ esC.g.epoch P + 1 := by
          rcases hS.ping_pong with ⟨hR, _⟩ | ⟨_, hR, _⟩
          · have hepP := AuthL10.epoch_eq_of_synced hS.epoch_S hR P
            have hepO := AuthL10.epoch_eq_of_synced hS.epoch_S hR P.other
            omega
          · rcases AuthL10.party_cases_of_epoch (max (esC.g.epoch .A) (esC.g.epoch .B)) P with hP | hP
            · have hO : P.other = Party.receiverOf (max (esC.g.epoch .A) (esC.g.epoch .B)) := by
                rw [hP, AuthL10.senderOf_other]
              have hS_ep := hS.epoch_S
              rw [← hP] at hS_ep
              rw [← hO] at hR
              omega
            · have hO : P.other = Party.senderOf (max (esC.g.epoch .A) (esC.g.epoch .B)) := by
                rw [hP, AuthL10.receiverOf_other]
              have hS_ep := hS.epoch_S
              rw [← hO] at hS_ep
              rw [← hP] at hR
              omega
        have hle : ¬ (esC.g.epoch P + 1 < c'.1.1) := by rw [hhdr', ht1]; omega
        have hidB : (esB.g.st P).id = P := hS.id_P P
        have htcurB : (esB.g.st P).tcur = esC.g.epoch P := hS.tcur_P P
        by_cases hnew : c'.1.1 = esC.g.epoch P + 1
        · have hnew_c : c.1.1 = esC.g.epoch P + 1 := by rw [hhdr, hnew]
          have hsend0' : P.sendsIn (esC.g.epoch P + 1) = false := hnew ▸ hsend0
          obtain ⟨hr_ep, _, _, hO_ep, _, Tm, Im, hct2, hcC, _, hSroot, hcP, hlast⟩ :=
            hS.deliver_new_info hr hnew_c
          have hc'2 : c'.1.2 = some Tm := by rw [hhdr', hct2]
          let p := prng.up (esC.g.st P).root Im
          have hp1 : (prng.up (esC.g.st P).root Im).1 = (esC.g.st P.other).root := hSroot.symm
          let γP' := (cka.receive (esB.g.st P).γ Tm).1
          have hstartC := fun ctx γv =>
            hooksCKABucket_startRecv_honest cka prng fs Δcka tL par ctx P (esC.g.epoch P + 1) γv
              (esC.g.st P).root Tm Im esC.h hcC
          have hstartB := fun ctx =>
            hooksPRNGBucketHybrid_startRecv_honest cka prng fs Δcka qep tL par (healEpoch tL)
              ctx P (esC.g.epoch P + 1) (esB.g.st P).γ (esB.g.st P).root Tm
              (esB.g.st P.other).root p.2 esB.h hcP ⟨_, root_P_moBase hS P.other⟩
          cases hfs : fs.receive (fs.initReceiver p.2) c'.1 c'.2 with
          | none =>
            have hC :
                ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
                  ((deliverForgeE (hooksCKABucket cka prng fs Δcka tL par) (2 + Δcka) qep
                    (bucketAuthCfg Δcka tL par) (P, c, c')).run esC)).run sc) =
                  pure ((some .rejected, esC), sc) := by
              simp [deliverForgeE, vRecv, habC, hwin0, hr, htrans0,
                hcomp0', hhdr, hS.id_C P, hS.tcur_C P, hsend0', hnew, hc'2, hstartC, hp1, p, hfs,
                StateT.run_bind, StateT.run_pure, simulateQ_pure, hesC_eq]
            have hB :
                ((simulateQ (AuthL10.pImpl prng)
                  ((deliverForgeE (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
                    (2 + Δcka) qep (bucketAuthCfg Δcka tL par) (P, c, c')).run esB)).run sp) =
                  pure ((some .rejected, esB), sp) := by
              simp [deliverForgeE, vRecv, habB,
                hwin, hwin0, htrans_c, hr, htrans_c', htrans0, hcomp, hcomp0', hhdr, hidB, htcurB,
                hsend0', hnew, hc'2, hstartB, hfs,
                StateT.run_bind, StateT.run_pure, simulateQ_pure, hesB_eq]
            rw [hC, hB]
            exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hS⟩)
          | some vim =>
            rcases vim with ⟨v', i', m'⟩
            let m := esC.g.epoch P + 1
            by_cases hqep : qep + 1 < m
            · have hC :
                  ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
                    ((deliverForgeE (hooksCKABucket cka prng fs Δcka tL par) (2 + Δcka) qep
                      (bucketAuthCfg Δcka tL par) (P, c, c')).run esC)).run sc) =
                    pure ((some .rejected, esC), sc) := by
                simp [deliverForgeE, vRecv, habC, hwin0, hr, htrans0,
                  hcomp0', hhdr, hS.id_C P, hS.tcur_C P, hsend0', hnew, hc'2, hstartC, hp1, p,
                  hfs, m, hqep, StateT.run_bind, StateT.run_pure, simulateQ_pure, hesC_eq]
              have hB :
                  ((simulateQ (AuthL10.pImpl prng)
                    ((deliverForgeE (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
                      (2 + Δcka) qep (bucketAuthCfg Δcka tL par) (P, c, c')).run esB)).run sp) =
                    pure ((some .rejected, esB), sp) := by
                simp [deliverForgeE, vRecv, habB,
                  hwin, hwin0, htrans_c, hr, htrans_c', htrans0, hcomp, hcomp0', hhdr, hidB,
                  htcurB, hsend0', hnew, hc'2, hstartB, hfs, m, hqep,
                  StateT.run_bind, StateT.run_pure, simulateQ_pure, hesB_eq]
              rw [hC, hB]
              exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hS⟩)
            · let pos : SM.Pos := ⟨P.other, m, i'⟩
              have htriv_eq : esB.g.trivial (2 + Δcka) pos = esC.g.trivial (2 + Δcka) pos :=
                AuthL10.eraseSt_trivial hS.g_eq (2 + Δcka) pos
              by_cases htriv : esC.g.trivial (2 + Δcka) pos
              · let vR' := Function.update (Function.update (esC.g.st P).vR m
                  (some (fs.initReceiver p.2))) m (some v')
                let γC_final := if AuthL10.localCKA (moBase tL) Δcka m then some γP' else none
                let stC_final : VP (Option Γ) T Sig SS RS :=
                  { esC.g.st P with
                    tcur := m, γ := γC_final, root := (esC.g.st P.other).root, vR := vR' }
                let stB_final : VP Γ T (Option Sig) SS RS :=
                  { esB.g.st P with
                    tcur := m, γ := γP', root := (esB.g.st P.other).root, vR := vR' }
                have hvRB : (esB.g.st P).vR = (esC.g.st P).vR := hS.vR_eq P
                have hB :
                    ((simulateQ (AuthL10.pImpl prng)
                      ((deliverForgeE
                        (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
                        (2 + Δcka) qep (bucketAuthCfg Δcka tL par) (P, c, c')).run esB)).run sp) =
                      pure ((some (.accepted m i' (some m')),
                        { esB with g := esB.g.accept P stB_final pos }), sp) := by
                  simp [deliverForgeE, commitE, vRecv, habB, hwin, hwin0, htrans_c, hr, htrans_c',
                    htrans0, hcomp, hcomp0', hhdr, hidB, htcurB, hsend0', hnew, hc'2, hvRB,
                    hstartB, hfs, m, hqep, hr_ep, pos, htriv_eq, htriv, vR', stB_final, γP',
                    StateT.run_bind, StateT.run_pure, StateT.run_modify, simulateQ_pure]
                by_cases hloc : AuthL10.localCKA (moBase tL) Δcka (esC.g.epoch P) = true
                · have hloc_m : AuthL10.localCKA (moBase tL) Δcka m = true :=
                    AuthL10.localCKA_mono (moBase tL) Δcka hloc (Nat.le_succ _)
                  have hγC : (esC.g.st P).γ = some (esB.g.st P).γ := by
                    rw [hS.γ_C P, hloc]; rfl
                  have hC :
                      ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
                        ((deliverForgeE (hooksCKABucket cka prng fs Δcka tL par) (2 + Δcka) qep
                          (bucketAuthCfg Δcka tL par) (P, c, c')).run esC)).run sc) =
                        pure ((some (.accepted m i' (some m')),
                          { esC with g := esC.g.accept P stC_final pos }), sc) := by
                    simp [deliverForgeE, commitE, vRecv, hooksCKA, habC, hwin0, hr,
                      htrans0, hcomp0', hhdr, hS.id_C P, hS.tcur_C P, hsend0', hnew, hc'2,
                      hstartC, hp1, p, hfs, hγC, hloc_m, m, hqep, hr_ep, pos, htriv, vR',
                      γC_final, stC_final, γP',
                      StateT.run_bind, StateT.run_pure, StateT.run_modify, simulateQ_pure]
                  rw [hC, hB]
                  exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hS.accept_new P γP' vR' pos rfl hO_ep
                    hS.b_C (fun h => by simp [m, hloc_m] at h)⟩)
                · simp only [Bool.not_eq_true] at hloc
                  have hγC : (esC.g.st P).γ = none := by
                    rw [hS.γ_C P, hloc]; rfl
                  obtain ⟨hsc_stP, hsc_epP⟩ := hS.cka_st P (Or.inl hloc)
                  obtain ⟨hsc_stO, hsc_epO⟩ := hS.cka_st P.other (Or.inr (by simpa using hloc))
                  have hcanR : sc.canReceive P = true := by
                    simp [CKA.GameState.canReceive, hsc_epO, hsc_epP, hO_ep]
                  have hlast_eq : sc.lastMsg = some Tm := hlast hloc
                  let sc' := sc.afterReceive P γP'
                  have htL_none : (moBase tL).tL.isNone = false := by
                    simp only [AuthL10.localCKA, Bool.or_eq_false_iff] at hloc
                    exact hloc.1
                  by_cases hfin : healEpoch tL + Δcka ≤ m
                  · have hloc_m : AuthL10.localCKA (moBase tL) Δcka m = true := by
                      simp [AuthL10.localCKA, moBase, Mode.tH, hfin]
                    have hC :
                        ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
                          ((deliverForgeE (hooksCKABucket cka prng fs Δcka tL par) (2 + Δcka) qep
                            (bucketAuthCfg Δcka tL par) (P, c, c')).run esC)).run sc) =
                          pure ((some (.accepted m i' (some m')),
                            { esC with g := esC.g.accept P stC_final pos }), sc') := by
                      simp [deliverForgeE, commitE, hooksCKA, liftC, StateT.lift, toEStateP,
                        CKA.receiveQuery, CKA.corrQuery, AuthL10.cImpl, CKA.oracleImpl,
                        CKA.receiveImpl, CKA.corrImpl, vRecv, habC, hwin0, hr, htrans0,
                        hcomp0', hhdr, hS.id_C P, hS.tcur_C P, hsend0', hnew, hc'2, hstartC, hp1,
                        p, hfs, hγC, hcanR, hlast_eq, hsc_stP, hfin, hloc_m, sc',
                        CKA.GameState.afterReceive, CKA.GameState.finished, hsc_epP, m, hqep,
                        hr_ep, pos, htriv, vR', γC_final, stC_final, γP',
                        simulateQ_bind, simulateQ_query, simulateQ_pure, map_eq_bind_pure_comp,
                        StateT.run_bind, StateT.run_pure, StateT.run_modify]
                    rw [hC, hB]
                    exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hS.accept_new P γP' vR' pos rfl hO_ep
                      hS.b_C (fun h => by simp [m, hloc_m] at h)⟩)
                  · have hloc_m : AuthL10.localCKA (moBase tL) Δcka m = false := by
                      simp only [AuthL10.localCKA, Bool.or_eq_false_iff, decide_eq_false_iff_not,
                        moBase_tH]
                      exact ⟨htL_none, hfin⟩
                    have hC :
                        ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
                          ((deliverForgeE (hooksCKABucket cka prng fs Δcka tL par) (2 + Δcka) qep
                            (bucketAuthCfg Δcka tL par) (P, c, c')).run esC)).run sc) =
                          pure ((some (.accepted m i' (some m')),
                            { esC with g := esC.g.accept P stC_final pos }), sc') := by
                      simp [deliverForgeE, commitE, hooksCKA, liftC, StateT.lift, toEStateP,
                        CKA.receiveQuery, AuthL10.cImpl, CKA.oracleImpl, CKA.receiveImpl, vRecv,
                        habC, hwin0, hr, htrans0, hcomp0', hhdr, hS.id_C P, hS.tcur_C P,
                        hsend0', hnew, hc'2, hstartC, hp1, p, hfs, hγC, hcanR, hlast_eq, hsc_stP,
                        hfin, hloc_m, sc', m, hqep, hr_ep, pos, htriv, vR', γC_final, stC_final,
                        γP', simulateQ_bind, simulateQ_query, simulateQ_pure,
                        map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure, StateT.run_modify]
                    rw [hC, hB]
                    refine AuthL11.LeComp.pure (Or.inr ⟨rfl,
                      hS.accept_new P γP' vR' pos rfl hO_ep hS.b_C fun _ => ?_⟩)
                    simp [sc', CKA.GameState.afterReceive, Party.other_ne, hsc_epP, hsc_stO,
                      hsc_epO, hO_ep]
              · simp only [Bool.not_eq_true] at htriv
                by_cases hinj : (bucketAuthCfg Δcka tL par : SM.Config M).injectFull m
                · have hC :
                      ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
                        ((deliverForgeE (hooksCKABucket cka prng fs Δcka tL par) (2 + Δcka) qep
                          (bucketAuthCfg Δcka tL par) (P, c, c')).run esC)).run sc) =
                        pure ((some .rejected, { esC with g := { esC.g with win := true } }), sc) := by
                    simp [deliverForgeE, vRecv, habC, hwin0, hr,
                      htrans0, hcomp0', hhdr, hS.id_C P, hS.tcur_C P, hsend0', hnew, hc'2,
                      hstartC, hp1, p, hfs, m, hqep, hr_ep, pos, htriv, hinj,
                      StateT.run_bind, StateT.run_pure, StateT.run_modify, simulateQ_pure]
                  have hB :
                      ((simulateQ (AuthL10.pImpl prng)
                        ((deliverForgeE
                          (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
                          (2 + Δcka) qep (bucketAuthCfg Δcka tL par) (P, c, c')).run esB)).run sp) =
                        pure ((some .rejected, { esB with g := { esB.g with win := true } }), sp) := by
                    simp [deliverForgeE, vRecv,
                      habB, hwin, hwin0, htrans_c, hr, htrans_c', htrans0, hcomp, hcomp0', hhdr,
                      hidB, htcurB, hsend0', hnew, hc'2, hstartB, hfs, m, hqep, hr_ep, pos,
                      htriv_eq, htriv, hinj,
                      StateT.run_bind, StateT.run_pure, StateT.run_modify, simulateQ_pure]
                  rw [hC, hB]
                  exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hS.set_win_prf true sp.prf (Or.inl rfl)⟩)
                · simp only [Bool.not_eq_true] at hinj
                  have hC :
                      ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
                        ((deliverForgeE (hooksCKABucket cka prng fs Δcka tL par) (2 + Δcka) qep
                          (bucketAuthCfg Δcka tL par) (P, c, c')).run esC)).run sc) =
                        pure ((some .rejected, esC), sc) := by
                    simp [deliverForgeE, vRecv, habC, hwin0, hr,
                      htrans0, hcomp0', hhdr, hS.id_C P, hS.tcur_C P, hsend0', hnew, hc'2,
                      hstartC, hp1, p, hfs, m, hqep, hr_ep, pos, htriv, hinj,
                      StateT.run_bind, StateT.run_pure, simulateQ_pure, hesC_eq]
                  have hB :
                      ((simulateQ (AuthL10.pImpl prng)
                        ((deliverForgeE
                          (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
                          (2 + Δcka) qep (bucketAuthCfg Δcka tL par) (P, c, c')).run esB)).run sp) =
                        pure ((some .rejected, esB), sp) := by
                    simp [deliverForgeE, vRecv,
                      habB, hwin, hwin0, htrans_c, hr, htrans_c', htrans0, hcomp, hcomp0', hhdr,
                      hidB, htcurB, hsend0', hnew, hc'2, hstartB, hfs, m, hqep, hr_ep, pos,
                      htriv_eq, htriv, hinj,
                      StateT.run_bind, StateT.run_pure, simulateQ_pure, hesB_eq]
                  rw [hC, hB]
                  exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hS⟩)
        · have hle_ep : c'.1.1 ≤ esC.g.epoch P := by omega
          have hvRB : (esB.g.st P).vR c'.1.1 = (esC.g.st P).vR c'.1.1 := congrFun (hS.vR_eq P) _
          cases hvR : (esC.g.st P).vR c'.1.1 with
          | none =>
            have hC :
                ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
                  ((deliverForgeE (hooksCKABucket cka prng fs Δcka tL par) (2 + Δcka) qep
                    (bucketAuthCfg Δcka tL par) (P, c, c')).run esC)).run sc) =
                  pure ((some .rejected, esC), sc) := by
              simp [deliverForgeE, vRecv, habC, hwin0, hr, htrans0, hcomp0', hhdr, hS.id_C P,
                hS.tcur_C P, hsend0, hle, hnew, hvR, StateT.run_bind, StateT.run_pure,
                simulateQ_pure, hesC_eq]
            have hB :
                ((simulateQ (AuthL10.pImpl prng)
                  ((deliverForgeE (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
                    (2 + Δcka) qep (bucketAuthCfg Δcka tL par) (P, c, c')).run esB)).run sp) =
                  pure ((some .rejected, esB), sp) := by
              simp [deliverForgeE, vRecv, habB, hwin, hwin0, htrans_c, hr, htrans_c', htrans0,
                hcomp, hcomp0', hhdr, hidB, htcurB, hsend0, hle, hnew, hvRB, hvR,
                StateT.run_bind, StateT.run_pure, simulateQ_pure, hesB_eq]
            rw [hC, hB]
            exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hS⟩)
          | some v =>
            cases hfs : fs.receive v c'.1 c'.2 with
            | none =>
              have hC :
                  ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
                    ((deliverForgeE (hooksCKABucket cka prng fs Δcka tL par) (2 + Δcka) qep
                      (bucketAuthCfg Δcka tL par) (P, c, c')).run esC)).run sc) =
                    pure ((some .rejected, esC), sc) := by
                simp [deliverForgeE, vRecv, habC, hwin0, hr, htrans0,
                  hcomp0', hhdr, hS.id_C P, hS.tcur_C P, hsend0, hle, hnew, hvR, hfs,
                  StateT.run_bind, StateT.run_pure, simulateQ_pure, hesC_eq]
              have hB :
                  ((simulateQ (AuthL10.pImpl prng)
                    ((deliverForgeE
                      (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
                      (2 + Δcka) qep (bucketAuthCfg Δcka tL par) (P, c, c')).run esB)).run sp) =
                    pure ((some .rejected, esB), sp) := by
                simp [deliverForgeE, vRecv, habB,
                  hwin, hwin0, htrans_c, hr, htrans_c', htrans0, hcomp, hcomp0', hhdr, hidB,
                  htcurB, hsend0, hle, hnew, hvRB, hvR, hfs,
                  StateT.run_bind, StateT.run_pure, simulateQ_pure, hesB_eq]
              rw [hC, hB]
              exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hS⟩)
            | some vim =>
              rcases vim with ⟨v', i', m'⟩
              have heq_ep : r.pos.epoch = c'.1.1 := by rw [hhdr', ht1]
              by_cases hqep : qep + 1 < c'.1.1
              · have hC :
                    ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
                      ((deliverForgeE (hooksCKABucket cka prng fs Δcka tL par) (2 + Δcka) qep
                        (bucketAuthCfg Δcka tL par) (P, c, c')).run esC)).run sc) =
                      pure ((some .rejected, esC), sc) := by
                  simp [deliverForgeE, vRecv, habC, hwin0, hr, htrans0,
                    hcomp0', hhdr, hS.id_C P, hS.tcur_C P, hsend0, hle, hnew, hvR, hfs, hqep,
                    StateT.run_bind, StateT.run_pure, simulateQ_pure, hesC_eq]
                have hB :
                    ((simulateQ (AuthL10.pImpl prng)
                      ((deliverForgeE
                        (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
                        (2 + Δcka) qep (bucketAuthCfg Δcka tL par) (P, c, c')).run esB)).run sp) =
                      pure ((some .rejected, esB), sp) := by
                  simp [deliverForgeE, vRecv, habB,
                    hwin, hwin0, htrans_c, hr, htrans_c', htrans0, hcomp, hcomp0', hhdr, hidB,
                    htcurB, hsend0, hle, hnew, hvRB, hvR, hfs, hqep,
                    StateT.run_bind, StateT.run_pure, simulateQ_pure, hesB_eq]
                rw [hC, hB]
                exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hS⟩)
              · let pos : SM.Pos := ⟨P.other, c'.1.1, i'⟩
                have htriv_eq : esB.g.trivial (2 + Δcka) pos = esC.g.trivial (2 + Δcka) pos :=
                  AuthL10.eraseSt_trivial hS.g_eq (2 + Δcka) pos
                by_cases htriv : esC.g.trivial (2 + Δcka) pos
                · let vR' := Function.update (esC.g.st P).vR c'.1.1 (some v')
                  have hvRB_all : (esB.g.st P).vR = (esC.g.st P).vR := hS.vR_eq P
                  have hvR'_eq : Function.update (esB.g.st P).vR c'.1.1 (some v') = vR' := by
                    simp [vR', hvRB_all]
                  have hC :
                      ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
                        ((deliverForgeE (hooksCKABucket cka prng fs Δcka tL par) (2 + Δcka) qep
                          (bucketAuthCfg Δcka tL par) (P, c, c')).run esC)).run sc) =
                        pure ((some (.accepted c'.1.1 i' (some m')),
                          { esC with g := esC.g.accept P { esC.g.st P with vR := vR' } pos }), sc) := by
                    simp [deliverForgeE, vRecv, commitE, hooksCKA, habC, hwin0, hr,
                      htrans0, hcomp0', hhdr, hS.id_C P, hS.tcur_C P, hsend0, hle, hnew, hvR, hfs,
                      hqep, heq_ep, htriv, pos, vR',
                      StateT.run_bind, StateT.run_pure, StateT.run_modify, simulateQ_pure]
                  have hB :
                      ((simulateQ (AuthL10.pImpl prng)
                        ((deliverForgeE
                          (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
                          (2 + Δcka) qep (bucketAuthCfg Δcka tL par) (P, c, c')).run esB)).run sp) =
                        pure ((some (.accepted c'.1.1 i' (some m')),
                          { esB with g := esB.g.accept P { esB.g.st P with vR := vR' } pos }), sp) := by
                    simp [deliverForgeE, vRecv, commitE, habB, hwin, hwin0, htrans_c, hr, htrans_c',
                      htrans0, hcomp, hcomp0', hhdr, hidB, htcurB, hsend0, hle, hnew, hvRB, hvR,
                      hfs, hqep, heq_ep, htriv_eq, htriv, pos, hvR'_eq,
                      StateT.run_bind, StateT.run_pure, StateT.run_modify, simulateQ_pure]
                  rw [hC, hB]
                  exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hS.accept_old P vR' pos hle_ep⟩)
                · simp only [Bool.not_eq_true] at htriv
                  by_cases hinj : (bucketAuthCfg Δcka tL par : SM.Config M).injectFull c'.1.1
                  · have hC :
                        ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
                          ((deliverForgeE (hooksCKABucket cka prng fs Δcka tL par) (2 + Δcka) qep
                             (bucketAuthCfg Δcka tL par) (P, c, c')).run esC)).run sc) =
                          pure ((some .rejected, { esC with g := { esC.g with win := true } }), sc) := by
                      simp [deliverForgeE, vRecv, habC, hwin0, hr,
                        htrans0, hcomp0', hhdr, hS.id_C P, hS.tcur_C P, hsend0, hle, hnew, hvR,
                        hfs, hqep, heq_ep, htriv, hinj, pos,
                        StateT.run_bind, StateT.run_pure, StateT.run_modify, simulateQ_pure]
                    have hB :
                        ((simulateQ (AuthL10.pImpl prng)
                          ((deliverForgeE
                            (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
                            (2 + Δcka) qep (bucketAuthCfg Δcka tL par) (P, c, c')).run esB)).run sp) =
                          pure ((some .rejected, { esB with g := { esB.g with win := true } }), sp) := by
                      simp [deliverForgeE, vRecv,
                        habB, hwin, hwin0, htrans_c, hr, htrans_c', htrans0, hcomp, hcomp0', hhdr,
                        hidB, htcurB, hsend0, hle, hnew, hvRB, hvR, hfs, hqep, heq_ep, htriv_eq,
                        htriv, hinj, pos,
                        StateT.run_bind, StateT.run_pure, StateT.run_modify, simulateQ_pure]
                    rw [hC, hB]
                    exact AuthL11.LeComp.pure
                      (Or.inr ⟨rfl, hS.set_win_prf true sp.prf (Or.inl rfl)⟩)
                  · simp only [Bool.not_eq_true] at hinj
                    have hC :
                        ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
                          ((deliverForgeE (hooksCKABucket cka prng fs Δcka tL par) (2 + Δcka) qep
                            (bucketAuthCfg Δcka tL par) (P, c, c')).run esC)).run sc) =
                          pure ((some .rejected, esC), sc) := by
                      simp [deliverForgeE, vRecv, habC, hwin0, hr,
                        htrans0, hcomp0', hhdr, hS.id_C P, hS.tcur_C P, hsend0, hle, hnew, hvR,
                        hfs, hqep, heq_ep, htriv, hinj, pos,
                        StateT.run_bind, StateT.run_pure, simulateQ_pure, hesC_eq]
                    have hB :
                        ((simulateQ (AuthL10.pImpl prng)
                          ((deliverForgeE
                            (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
                            (2 + Δcka) qep (bucketAuthCfg Δcka tL par) (P, c, c')).run esB)).run sp) =
                          pure ((some .rejected, esB), sp) := by
                      simp [deliverForgeE, vRecv,
                        habB, hwin, hwin0, htrans_c, hr, htrans_c', htrans0, hcomp, hcomp0', hhdr,
                        hidB, htcurB, hsend0, hle, hnew, hvRB, hvR, hfs, hqep, heq_ep, htriv_eq,
                        htriv, hinj, pos,
                        StateT.run_bind, StateT.run_pure, simulateQ_pure, hesB_eq]
                    rw [hC, hB]
                    exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hS⟩)

set_option maxHeartbeats 400000 in
private theorem leComp_injectE_base
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (arg : Party × (Header T × E))
    {esC : AuthL10.EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esB : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : AuthL10.Sync prng Δcka (moBase tL) esC sc (toEStateP esB) sp) :
    AuthL11.LeComp (StepRelBaseRaw prng Δcka tL)
      ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
        ((injectE (hooksCKABucket cka prng fs Δcka tL par) (2 + Δcka) qep
          (bucketAuthCfg Δcka tL par) arg).run esC)).run sc)
      ((simulateQ (AuthL10.pImpl prng)
        ((injectE (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
          (2 + Δcka) qep (bucketAuthCfg Δcka tL par) arg).run esB)).run sp) := by
  rcases arg with ⟨P, c⟩
  have habC : esC.abort = false := hS.abort_C
  have habB : esB.abort = false := hS.abort_P
  have hwin : esB.g.win = esC.g.win := AuthL10.eraseSt_win hS.g_eq
  have htrans : esB.g.inTransit P.other c = esC.g.inTransit P.other c :=
    AuthL10.eraseSt_inTransit hS.g_eq P.other c
  have hsafe : esB.g.safeInj (2 + Δcka) = esC.g.safeInj (2 + Δcka) :=
    AuthL10.eraseSt_safeInj hS.g_eq (2 + Δcka)
  have hesC_eq := AuthL10.estate_mk_abort_false habC
  have hesB_eq := estateB_mk_abort_false habB
  have hidB : (esB.g.st P).id = P := hS.id_P P
  have htcurB : (esB.g.st P).tcur = esC.g.epoch P := hS.tcur_P P
  by_cases hguard : esC.g.win || (esC.g.inTransit P.other c).isSome || !esC.g.safeInj (2 + Δcka)
  · simp only [Bool.or_eq_true, Bool.not_eq_true'] at hguard
    have hC :
        ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
          ((injectE (hooksCKABucket cka prng fs Δcka tL par) (2 + Δcka) qep
            (bucketAuthCfg Δcka tL par) (P, c)).run esC)).run sc) =
          pure ((none, esC), sc) := by
      simp [injectE, habC, hguard, StateT.run_pure]
    have hB :
        ((simulateQ (AuthL10.pImpl prng)
          ((injectE (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
            (2 + Δcka) qep (bucketAuthCfg Δcka tL par) (P, c)).run esB)).run sp) =
          pure ((none, esB), sp) := by
      simp [injectE, habB, hwin, htrans, hsafe, hguard, StateT.run_pure]
    rw [hC, hB]
    exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hS⟩)
  · simp only [Bool.not_eq_true, Bool.or_eq_false_iff, Bool.not_eq_false'] at hguard
    rcases hguard with ⟨⟨hwin0, htrans0⟩, hsafe0⟩
    by_cases hsend : P.sendsIn c.1.1 || decide (esC.g.epoch P + 1 < c.1.1)
    · simp only [Bool.or_eq_true, decide_eq_true_eq] at hsend
      have hC :
          ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
            ((injectE (hooksCKABucket cka prng fs Δcka tL par) (2 + Δcka) qep
              (bucketAuthCfg Δcka tL par) (P, c)).run esC)).run sc) =
            pure ((some .rejected, esC), sc) := by
        simp [injectE, vRecv, habC, hwin0, htrans0, hsafe0, hS.id_C P, hS.tcur_C P, hsend,
          StateT.run_pure, hesC_eq]
      have hB :
          ((simulateQ (AuthL10.pImpl prng)
            ((injectE (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
              (2 + Δcka) qep (bucketAuthCfg Δcka tL par) (P, c)).run esB)).run sp) =
            pure ((some .rejected, esB), sp) := by
        simp [injectE, vRecv, habB, hwin, htrans, hsafe, hwin0, htrans0, hsafe0, hidB, htcurB,
          hsend, StateT.run_pure, hesB_eq]
      rw [hC, hB]
      exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hS⟩)
    · simp only [Bool.not_eq_true, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hsend
      rcases hsend with ⟨hsend0, hle⟩
      by_cases hnew : c.1.1 = esC.g.epoch P + 1
      · have hsend0' : P.sendsIn (esC.g.epoch P + 1) = false := hnew ▸ hsend0
        have htriv_false : ∀ i', esC.g.trivial (2 + Δcka) ⟨P.other, esC.g.epoch P + 1, i'⟩ = false :=
          fun i' => AuthL10.trivial_false_of_safeInj esC.g (2 + Δcka) P i' hsafe0 hS.comp_inv
        have htrivB_false : ∀ i', esB.g.trivial (2 + Δcka) ⟨P.other, esC.g.epoch P + 1, i'⟩ = false := by
          intro i'
          exact (AuthL10.eraseSt_trivial hS.g_eq (2 + Δcka) _).trans (htriv_false i')
        cases hTn : c.1.2 with
        | none =>
          have hC :
              ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
                ((injectE (hooksCKABucket cka prng fs Δcka tL par) (2 + Δcka) qep
                  (bucketAuthCfg Δcka tL par) (P, c)).run esC)).run sc) =
                pure ((some .rejected, esC), sc) := by
            simp [injectE, vRecv, habC, hwin0, htrans0, hsafe0, hS.id_C P, hS.tcur_C P, hsend0',
              hnew, hTn, StateT.run_pure, hesC_eq]
          have hB :
              ((simulateQ (AuthL10.pImpl prng)
                ((injectE (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
                  (2 + Δcka) qep (bucketAuthCfg Δcka tL par) (P, c)).run esB)).run sp) =
                pure ((some .rejected, esB), sp) := by
            simp [injectE, vRecv, habB, hwin, htrans, hsafe, hwin0, htrans0, hsafe0, hidB, htcurB,
              hsend0', hnew, hTn, StateT.run_pure, hesB_eq]
          rw [hC, hB]
          exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hS⟩)
        | some Tn =>
          have hafter : ∀ (γC' : Option Γ) (σC' : Sig) (γB' : Γ) (σB' : Option Sig) (rs : RS)
              (hsC : ((hooksCKABucket cka prng fs Δcka tL par).startRecv esC.g P (esC.g.epoch P + 1)
                (esC.g.st P).γ (esC.g.st P).root Tn).run esC.h =
                pure (some (some (γC', σC', rs)), esC.h))
              (hsB : ((hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL)).startRecv
                esB.g P (esC.g.epoch P + 1) (esB.g.st P).γ (esB.g.st P).root Tn).run esB.h =
                pure (some (some (γB', σB', rs)), esB.h)),
              AuthL11.LeComp (StepRelBaseRaw prng Δcka tL)
                ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
                  ((injectE (hooksCKABucket cka prng fs Δcka tL par) (2 + Δcka) qep
                    (bucketAuthCfg Δcka tL par) (P, c)).run esC)).run sc)
                ((simulateQ (AuthL10.pImpl prng)
                  ((injectE (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
                    (2 + Δcka) qep (bucketAuthCfg Δcka tL par) (P, c)).run esB)).run sp) := by
            intro γC' σC' γB' σB' rs hsC hsB
            rcases hfs : fs.receive rs c.1 c.2 with _ | ⟨v', i', m'⟩
            · have hC :
                  ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
                    ((injectE (hooksCKABucket cka prng fs Δcka tL par) (2 + Δcka) qep
                      (bucketAuthCfg Δcka tL par) (P, c)).run esC)).run sc) =
                    pure ((some .rejected, esC), sc) := by
                simp [injectE, vRecv, habC, hwin0, htrans0, hsafe0,
                  hS.id_C P, hS.tcur_C P, hsend0', hnew, hTn, hsC, hfs,
                  StateT.run_bind, StateT.run_pure, simulateQ_pure, hesC_eq]
              have hB :
                  ((simulateQ (AuthL10.pImpl prng)
                    ((injectE (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
                      (2 + Δcka) qep (bucketAuthCfg Δcka tL par) (P, c)).run esB)).run sp) =
                    pure ((some .rejected, esB), sp) := by
                simp [injectE, vRecv, habB, hwin,
                  htrans, hsafe, hwin0, htrans0, hsafe0, hidB, htcurB, hsend0', hnew, hTn, hsB,
                  hfs, StateT.run_bind, StateT.run_pure, simulateQ_pure, hesB_eq]
              rw [hC, hB]
              exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hS⟩)
            · by_cases hqep : qep + 1 < esC.g.epoch P + 1
              · have hC :
                    ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
                      ((injectE (hooksCKABucket cka prng fs Δcka tL par) (2 + Δcka) qep
                        (bucketAuthCfg Δcka tL par) (P, c)).run esC)).run sc) =
                      pure ((some .rejected, esC), sc) := by
                  simp [injectE, vRecv, habC, hwin0, htrans0, hsafe0,
                    hS.id_C P, hS.tcur_C P, hsend0', hnew, hTn, hsC, hfs, hqep,
                    StateT.run_bind, StateT.run_pure, simulateQ_pure, hesC_eq]
                have hB :
                    ((simulateQ (AuthL10.pImpl prng)
                      ((injectE (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
                        (2 + Δcka) qep (bucketAuthCfg Δcka tL par) (P, c)).run esB)).run sp) =
                      pure ((some .rejected, esB), sp) := by
                  simp [injectE, vRecv, habB, hwin,
                    htrans, hsafe, hwin0, htrans0, hsafe0, hidB, htcurB, hsend0', hnew, hTn, hsB,
                    hfs, hqep, StateT.run_bind, StateT.run_pure, simulateQ_pure, hesB_eq]
                rw [hC, hB]
                exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hS⟩)
              · have htrivC := htriv_false i'
                have htrivB := htrivB_false i'
                by_cases hinj : (bucketAuthCfg Δcka tL par : SM.Config M).injectFull (esC.g.epoch P + 1)
                · have hC :
                      ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
                        ((injectE (hooksCKABucket cka prng fs Δcka tL par) (2 + Δcka) qep
                          (bucketAuthCfg Δcka tL par) (P, c)).run esC)).run sc) =
                        pure ((some .rejected, { esC with g := { esC.g with win := true } }), sc) := by
                    simp [injectE, vRecv, habC, hwin0, htrans0, hsafe0,
                      hS.id_C P, hS.tcur_C P, hsend0', hnew, hTn, hsC, hfs, hqep, htrivC, hinj,
                      StateT.run_bind, StateT.run_pure, StateT.run_modify, simulateQ_pure]
                  have hB :
                      ((simulateQ (AuthL10.pImpl prng)
                        ((injectE (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
                          (2 + Δcka) qep (bucketAuthCfg Δcka tL par) (P, c)).run esB)).run sp) =
                        pure ((some .rejected, { esB with g := { esB.g with win := true } }), sp) := by
                    simp [injectE, vRecv, habB,
                      hwin, htrans, hsafe, hwin0, htrans0, hsafe0, hidB, htcurB, hsend0', hnew,
                      hTn, hsB, hfs, hqep, htrivB, hinj,
                      StateT.run_bind, StateT.run_pure, StateT.run_modify, simulateQ_pure]
                  rw [hC, hB]
                  exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hS.set_win_prf true sp.prf (Or.inl rfl)⟩)
                · simp only [Bool.not_eq_true] at hinj
                  have hC :
                      ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
                        ((injectE (hooksCKABucket cka prng fs Δcka tL par) (2 + Δcka) qep
                          (bucketAuthCfg Δcka tL par) (P, c)).run esC)).run sc) =
                        pure ((some .rejected, esC), sc) := by
                    simp [injectE, vRecv, habC, hwin0, htrans0, hsafe0,
                      hS.id_C P, hS.tcur_C P, hsend0', hnew, hTn, hsC, hfs, hqep, htrivC, hinj,
                      StateT.run_bind, StateT.run_pure, simulateQ_pure, hesC_eq]
                  have hB :
                      ((simulateQ (AuthL10.pImpl prng)
                        ((injectE (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
                          (2 + Δcka) qep (bucketAuthCfg Δcka tL par) (P, c)).run esB)).run sp) =
                        pure ((some .rejected, esB), sp) := by
                    simp [injectE, vRecv, habB,
                      hwin, htrans, hsafe, hwin0, htrans0, hsafe0, hidB, htcurB, hsend0', hnew,
                      hTn, hsB, hfs, hqep, htrivB, hinj,
                      StateT.run_bind, StateT.run_pure, simulateQ_pure, hesB_eq]
                  rw [hC, hB]
                  exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hS⟩)
          have hnone :
              (∀ Im, esC.h.cache (esC.g.epoch P + 1) ≠ some (Tn, Im)) →
              (∀ σc k, esB.h.cache (esC.g.epoch P + 1) ≠ some (Tn, σc, k)) →
              AuthL11.LeComp (StepRelBaseRaw prng Δcka tL)
                ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
                  ((injectE (hooksCKABucket cka prng fs Δcka tL par) (2 + Δcka) qep
                    (bucketAuthCfg Δcka tL par) (P, c)).run esC)).run sc)
                ((simulateQ (AuthL10.pImpl prng)
                  ((injectE (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
                    (2 + Δcka) qep (bucketAuthCfg Δcka tL par) (P, c)).run esB)).run sp) := by
            intro hcC_none hcB_none
            have hsC_un := fun ctx => hooksCKABucket_startRecv_unhonest cka prng fs Δcka tL par ctx P
              (esC.g.epoch P + 1) (esC.g.st P).γ (esC.g.st P).root Tn esC.h hcC_none
            have hsB_un := fun ctx => hooksPRNGBucketHybrid_startRecv_unhonest_base cka prng fs Δcka qep tL par
              ctx P (esC.g.epoch P) (esB.g.st P).γ (esB.g.st P).root Tn esB.h hcB_none
              ⟨_, root_P_moBase hS P⟩
            by_cases hb : inStage2Bucket Δcka tL par (esC.g.epoch P + 1) = true
            · obtain ⟨hloc, _, _⟩ := inStage2Bucket_localCKA_and_gt hb
              have hγC : (esC.g.st P).γ = some (esB.g.st P).γ := by
                rw [hS.γ_C P, hloc]; rfl
              have hrootB : (esB.g.st P).root = some (esC.g.st P).root := by
                have hr := hS.root_P P
                rw [knownRoot_moBase] at hr
                exact hr
              by_cases hqep : qep + 1 < esC.g.epoch P + 1
              · have hsB_rej : ∀ ctx,
                    ((hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL)).startRecv
                      ctx P (esC.g.epoch P + 1) (esB.g.st P).γ (esB.g.st P).root Tn).run esB.h =
                      pure (some none, esB.h) := by
                  intro ctx; rw [hsB_un ctx]; simp [hqep]
                have hB :
                    ((simulateQ (AuthL10.pImpl prng)
                      ((injectE (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
                        (2 + Δcka) qep (bucketAuthCfg Δcka tL par) (P, c)).run esB)).run sp) =
                      pure ((some .rejected, esB), sp) := by
                  simp [injectE, vRecv, habB, hwin, htrans, hsafe, hwin0, htrans0, hsafe0, hidB,
                    htcurB, hsend0', hnew, hTn, hsB_rej,
                    StateT.run_bind, StateT.run_pure, simulateQ_pure, hesB_eq]
                let kk := cka.receive (esB.g.st P).γ Tn
                let p := prng.up (esC.g.st P).root kk.2
                have hsC_ok : ∀ ctx,
                    ((hooksCKABucket cka prng fs Δcka tL par).startRecv ctx P (esC.g.epoch P + 1)
                      (esC.g.st P).γ (esC.g.st P).root Tn).run esC.h =
                      pure (some (some (some kk.1, p.1, fs.initReceiver p.2)), esC.h) := by
                  intro ctx; rw [hsC_un ctx]; simp [hb, hγC, kk, p]
                rcases hfs : fs.receive (fs.initReceiver p.2) c.1 c.2 with _ | ⟨v', i', m'⟩
                · have hC :
                      ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
                        ((injectE (hooksCKABucket cka prng fs Δcka tL par) (2 + Δcka) qep
                          (bucketAuthCfg Δcka tL par) (P, c)).run esC)).run sc) =
                        pure ((some .rejected, esC), sc) := by
                    simp [injectE, vRecv, habC, hwin0, htrans0, hsafe0,
                      hS.id_C P, hS.tcur_C P, hsend0', hnew, hTn, hsC_ok, hfs,
                      StateT.run_bind, StateT.run_pure, simulateQ_pure, hesC_eq]
                  rw [hC, hB]
                  exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hS⟩)
                · have hC :
                      ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
                        ((injectE (hooksCKABucket cka prng fs Δcka tL par) (2 + Δcka) qep
                          (bucketAuthCfg Δcka tL par) (P, c)).run esC)).run sc) =
                        pure ((some .rejected, esC), sc) := by
                    simp [injectE, vRecv, habC, hwin0, htrans0, hsafe0,
                      hS.id_C P, hS.tcur_C P, hsend0', hnew, hTn, hsC_ok, hfs, hqep,
                      StateT.run_bind, StateT.run_pure, simulateQ_pure, hesC_eq]
                  rw [hC, hB]
                  exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hS⟩)
              · let kk := cka.receive (esB.g.st P).γ Tn
                let p := prng.up (esC.g.st P).root kk.2
                refine hafter (some kk.1) p.1 kk.1 (some p.1) (fs.initReceiver p.2) ?_ ?_
                · rw [hsC_un esC.g]
                  simp [hb, hγC, kk, p]
                · rw [hsB_un esB.g]
                  simp [hqep, hb, hrootB, kk, p]
            · have hsC_rej : ∀ ctx,
                  ((hooksCKABucket cka prng fs Δcka tL par).startRecv ctx P (esC.g.epoch P + 1)
                    (esC.g.st P).γ (esC.g.st P).root Tn).run esC.h =
                    pure (some none, esC.h) := by
                intro ctx; rw [hsC_un ctx]; simp [hb]
              have hsB_rej : ∀ ctx,
                  ((hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL)).startRecv
                    ctx P (esC.g.epoch P + 1) (esB.g.st P).γ (esB.g.st P).root Tn).run esB.h =
                    pure (some none, esB.h) := by
                intro ctx; rw [hsB_un ctx]; simp [hb]
              have hC :
                  ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
                    ((injectE (hooksCKABucket cka prng fs Δcka tL par) (2 + Δcka) qep
                      (bucketAuthCfg Δcka tL par) (P, c)).run esC)).run sc) =
                    pure ((some .rejected, esC), sc) := by
                simp [injectE, vRecv, habC, hwin0, htrans0, hsafe0, hS.id_C P, hS.tcur_C P,
                  hsend0', hnew, hTn, hsC_rej, StateT.run_bind, StateT.run_pure, simulateQ_pure,
                  hesC_eq]
              have hB :
                  ((simulateQ (AuthL10.pImpl prng)
                    ((injectE (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
                      (2 + Δcka) qep (bucketAuthCfg Δcka tL par) (P, c)).run esB)).run sp) =
                    pure ((some .rejected, esB), sp) := by
                simp [injectE, vRecv, habB, hwin, htrans, hsafe, hwin0, htrans0, hsafe0, hidB,
                  htcurB, hsend0', hnew, hTn, hsB_rej, StateT.run_bind, StateT.run_pure,
                  simulateQ_pure, hesB_eq]
              rw [hC, hB]
              exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hS⟩)
          have hcache := hS.cache_at_succ P c.1.1 hnew
          rcases hcache with ⟨hcC, hcP⟩ | ⟨Tm, Im, hcC, hcP⟩
          · rw [hnew] at hcC hcP
            exact hnone (by simp [hcC]) (by dsimp only [toEStateP] at hcP; simp [hcP])
          · rw [hnew] at hcC hcP
            by_cases hTm : Tm = Tn
            · subst hTm
              let p := prng.up (esC.g.st P).root Im
              refine hafter ((esC.g.st P).γ.map fun γ => (cka.receive γ Tm).1) p.1
                (cka.receive (esB.g.st P).γ Tm).1
                (esB.g.st (Party.senderOf (esC.g.epoch P + 1))).root
                (fs.initReceiver p.2)
                (hooksCKABucket_startRecv_honest cka prng fs Δcka tL par esC.g P
                  (esC.g.epoch P + 1) (esC.g.st P).γ (esC.g.st P).root Tm Im esC.h hcC)
                (hooksPRNGBucketHybrid_startRecv_honest cka prng fs Δcka qep tL par (healEpoch tL)
                  esB.g P (esC.g.epoch P + 1) (esB.g.st P).γ (esB.g.st P).root Tm
                  (esB.g.st (Party.senderOf (esC.g.epoch P + 1))).root p.2 esB.h hcP
                  ⟨_, root_P_moBase hS (Party.senderOf (esC.g.epoch P + 1))⟩)
            · exact hnone (by simp [hcC, hTm])
                (by dsimp only [toEStateP] at hcP; simp [hcP, hTm])
      · have hle_ep : c.1.1 ≤ esC.g.epoch P := by omega
        have hvRB : (esB.g.st P).vR c.1.1 = (esC.g.st P).vR c.1.1 := congrFun (hS.vR_eq P) _
        cases hvR : (esC.g.st P).vR c.1.1 with
        | none =>
          have hC :
              ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
                 ((injectE (hooksCKABucket cka prng fs Δcka tL par) (2 + Δcka) qep
                  (bucketAuthCfg Δcka tL par) (P, c)).run esC)).run sc) =
                pure ((some .rejected, esC), sc) := by
            simp [injectE, vRecv, habC, hwin0, htrans0, hsafe0, hS.id_C P, hS.tcur_C P, hsend0,
              hle, hnew, hvR, StateT.run_pure, hesC_eq]
          have hB :
              ((simulateQ (AuthL10.pImpl prng)
                ((injectE (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
                  (2 + Δcka) qep (bucketAuthCfg Δcka tL par) (P, c)).run esB)).run sp) =
                pure ((some .rejected, esB), sp) := by
            simp [injectE, vRecv, habB, hwin, htrans, hsafe, hwin0, htrans0, hsafe0, hidB, htcurB,
              hsend0, hle, hnew, hvRB, hvR, StateT.run_pure, hesB_eq]
          rw [hC, hB]
          exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hS⟩)
        | some v =>
          rcases hfs : fs.receive v c.1 c.2 with _ | ⟨v', i', m'⟩
          · have hC :
                ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
                  ((injectE (hooksCKABucket cka prng fs Δcka tL par) (2 + Δcka) qep
                    (bucketAuthCfg Δcka tL par) (P, c)).run esC)).run sc) =
                  pure ((some .rejected, esC), sc) := by
              simp [injectE, vRecv, habC, hwin0, htrans0, hsafe0,
                hS.id_C P, hS.tcur_C P, hsend0, hle, hnew, hvR, hfs, StateT.run_pure, hesC_eq]
            have hB :
                ((simulateQ (AuthL10.pImpl prng)
                  ((injectE (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
                    (2 + Δcka) qep (bucketAuthCfg Δcka tL par) (P, c)).run esB)).run sp) =
                  pure ((some .rejected, esB), sp) := by
              simp [injectE, vRecv, habB, hwin,
                htrans, hsafe, hwin0, htrans0, hsafe0, hidB, htcurB, hsend0, hle, hnew, hvRB, hvR,
                hfs, StateT.run_pure, hesB_eq]
            rw [hC, hB]
            exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hS⟩)
          · by_cases hqep : qep + 1 < c.1.1
            · have hC :
                  ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
                    ((injectE (hooksCKABucket cka prng fs Δcka tL par) (2 + Δcka) qep
                      (bucketAuthCfg Δcka tL par) (P, c)).run esC)).run sc) =
                    pure ((some .rejected, esC), sc) := by
                simp [injectE, vRecv, habC, hwin0, htrans0, hsafe0,
                  hS.id_C P, hS.tcur_C P, hsend0, hle, hnew, hvR, hfs, hqep, StateT.run_pure,
                  hesC_eq]
              have hB :
                  ((simulateQ (AuthL10.pImpl prng)
                    ((injectE (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
                      (2 + Δcka) qep (bucketAuthCfg Δcka tL par) (P, c)).run esB)).run sp) =
                    pure ((some .rejected, esB), sp) := by
                simp [injectE, vRecv, habB, hwin,
                  htrans, hsafe, hwin0, htrans0, hsafe0, hidB, htcurB, hsend0, hle, hnew, hvRB,
                  hvR, hfs, hqep, StateT.run_pure, hesB_eq]
              rw [hC, hB]
              exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hS⟩)
            · let pos : SM.Pos := ⟨P.other, c.1.1, i'⟩
              have htriv_eq : esB.g.trivial (2 + Δcka) pos = esC.g.trivial (2 + Δcka) pos :=
                AuthL10.eraseSt_trivial hS.g_eq (2 + Δcka) pos
              by_cases htriv : esC.g.trivial (2 + Δcka) pos
              · let vR' := Function.update (esC.g.st P).vR c.1.1 (some v')
                have hvRB_all : (esB.g.st P).vR = (esC.g.st P).vR := hS.vR_eq P
                have hvR'_eq : Function.update (esB.g.st P).vR c.1.1 (some v') = vR' := by
                  simp [vR', hvRB_all]
                have hC :
                    ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
                      ((injectE (hooksCKABucket cka prng fs Δcka tL par) (2 + Δcka) qep
                        (bucketAuthCfg Δcka tL par) (P, c)).run esC)).run sc) =
                      pure ((some (.accepted c.1.1 i' (some m')),
                        { esC with g := esC.g.accept P { esC.g.st P with vR := vR' } pos }), sc) := by
                  simp [injectE, vRecv, commitE, hooksCKA, habC, hwin0, htrans0,
                    hsafe0, hS.id_C P, hS.tcur_C P, hsend0, hle, hnew, hvR, hfs, hqep, htriv, pos,
                    vR', StateT.run_pure, StateT.run_modify]
                have hB :
                    ((simulateQ (AuthL10.pImpl prng)
                      ((injectE (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
                        (2 + Δcka) qep (bucketAuthCfg Δcka tL par) (P, c)).run esB)).run sp) =
                      pure ((some (.accepted c.1.1 i' (some m')),
                        { esB with g := esB.g.accept P { esB.g.st P with vR := vR' } pos }), sp) := by
                  simp [injectE, vRecv, commitE,
                    habB, hwin, htrans, hsafe, hwin0, htrans0, hsafe0, hidB, htcurB, hsend0, hle,
                    hnew, hvRB, hvR, hfs, hqep, htriv_eq, htriv, pos, hvR'_eq,
                    StateT.run_pure, StateT.run_modify]
                rw [hC, hB]
                exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hS.accept_old P vR' pos hle_ep⟩)
              · simp only [Bool.not_eq_true] at htriv
                by_cases hinj : (bucketAuthCfg Δcka tL par : SM.Config M).injectFull c.1.1
                · have hC :
                      ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
                        ((injectE (hooksCKABucket cka prng fs Δcka tL par) (2 + Δcka) qep
                          (bucketAuthCfg Δcka tL par) (P, c)).run esC)).run sc) =
                        pure ((some .rejected, { esC with g := { esC.g with win := true } }), sc) := by
                    simp [injectE, vRecv, habC, hwin0, htrans0, hsafe0,
                      hS.id_C P, hS.tcur_C P, hsend0, hle, hnew, hvR, hfs, hqep, pos, htriv, hinj,
                      StateT.run_pure, StateT.run_modify]
                  have hB :
                      ((simulateQ (AuthL10.pImpl prng)
                        ((injectE (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
                          (2 + Δcka) qep (bucketAuthCfg Δcka tL par) (P, c)).run esB)).run sp) =
                        pure ((some .rejected, { esB with g := { esB.g with win := true } }), sp) := by
                    simp [injectE, vRecv, habB,
                      hwin, htrans, hsafe, hwin0, htrans0, hsafe0, hidB, htcurB, hsend0, hle,
                      hnew, hvRB, hvR, hfs, hqep, pos, htriv_eq, htriv, hinj,
                      StateT.run_pure, StateT.run_modify]
                  rw [hC, hB]
                  exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hS.set_win_prf true sp.prf (Or.inl rfl)⟩)
                · simp only [Bool.not_eq_true] at hinj
                  have hC :
                      ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
                        ((injectE (hooksCKABucket cka prng fs Δcka tL par) (2 + Δcka) qep
                          (bucketAuthCfg Δcka tL par) (P, c)).run esC)).run sc) =
                        pure ((some .rejected, esC), sc) := by
                    simp [injectE, vRecv, habC, hwin0, htrans0, hsafe0,
                      hS.id_C P, hS.tcur_C P, hsend0, hle, hnew, hvR, hfs, hqep, pos, htriv, hinj,
                      StateT.run_pure, hesC_eq]
                  have hB :
                      ((simulateQ (AuthL10.pImpl prng)
                        ((injectE (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
                          (2 + Δcka) qep (bucketAuthCfg Δcka tL par) (P, c)).run esB)).run sp) =
                        pure ((some .rejected, esB), sp) := by
                    simp [injectE, vRecv, habB,
                      hwin, htrans, hsafe, hwin0, htrans0, hsafe0, hidB, htcurB, hsend0, hle,
                      hnew, hvRB, hvR, hfs, hqep, pos, htriv_eq, htriv, hinj,
                      StateT.run_pure, hesB_eq]
                  rw [hC, hB]
                  exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hS⟩)

private theorem leak_tL_eq {St Msg C : Type} (g : SM.GameState St Msg C) (e : ℕ) :
    (g.leak e).tL = some (maxOpt g.tL e) := rfl

private theorem postLeak_leak_false_of_lt_tH {St Msg C : Type}
    {tL : Option ℕ} {g : SM.GameState St Msg C} {e : ℕ}
    (hpl : postLeak tL g = false) (he : e + 1 < healEpoch tL) :
    postLeak tL (g.leak e) = false := by
  cases tL with
  | none => simp [healEpoch] at he
  | some l =>
    have he_le : e ≤ l := by simp [healEpoch] at he; omega
    rw [postLeak, leak_tL_eq]
    cases htL : g.tL with
    | none =>
      simp only [Thm1L17.maxOpt_none, Thm1L17.ltOpt_some, decide_eq_false_iff_not]
      omega
    | some cur =>
      simp only [postLeak, htL, Thm1L17.ltOpt_some, decide_eq_false_iff_not] at hpl
      simp only [Thm1L17.maxOpt_some, Thm1L17.ltOpt_some, decide_eq_false_iff_not]
      omega

private theorem postLeak_afterCorr_false_of_lt_tH {St Msg C : Type}
    {tL : Option ℕ} {g : SM.GameState St Msg C} (P : Party)
    (hpl : postLeak tL g = false) (he : max (g.epoch .A) (g.epoch .B) + 1 < healEpoch tL) :
    postLeak tL (g.afterCorr P) = false := by
  have h := postLeak_leak_false_of_lt_tH hpl he
  dsimp [postLeak, SM.GameState.afterCorr, SM.GameState.leak] at h ⊢
  exact h

@[local simp]
private theorem postLeak_record {St Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    (tL : Option ℕ) (g : SM.GameState St Msg C) (Δ : ℕ) (P : Party)
    (st' : St) (rcd : SM.Record Msg C) (ch : Bool) :
    postLeak tL (g.record Δ P st' rcd ch) = postLeak tL g := rfl

@[local simp]
private theorem postLeak_accept {St Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    (tL : Option ℕ) (g : SM.GameState St Msg C) (P : Party) (st' : St) (pos : SM.Pos) :
    postLeak tL (g.accept P st' pos) = postLeak tL g := rfl

private theorem postLeak_epMgmtNew_false {St Msg C : Type}
    {tL : Option ℕ} {g : SM.GameState St Msg C} (Δ : ℕ) (P : Party) (bad : Bool)
    (hpl : postLeak tL g = false)
    (hbad : bad = false ∨ g.epoch P + 1 + 2 ≤ healEpoch tL) :
    postLeak tL (AuthL10.epMgmtNew g Δ P bad) = false := by
  unfold AuthL10.epMgmtNew
  rcases hbad with rfl | hle
  · simpa [postLeak] using hpl
  · by_cases hcond : (bad && !(g.safeCh Δ P)) = true
    · have hlt : (g.epoch P + 1) + 1 < healEpoch tL := by omega
      have h := postLeak_leak_false_of_lt_tH hpl hlt
      simpa [hcond, postLeak] using h
    · simp only [Bool.not_eq_true] at hcond
      simpa [hcond, postLeak] using hpl

private theorem epoch_accept_le_qep {St Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    {g : SM.GameState St Msg C} {qep : ℕ} (hle : ∀ Q, g.epoch Q ≤ qep)
    (P : Party) (st' : St) (pos : SM.Pos) (hpos : pos.epoch ≤ qep) :
    ∀ Q, (g.accept P st' pos).epoch Q ≤ qep := fun Q => by
  by_cases hQP : Q = P
  · subst hQP
    simp [SM.GameState.accept, SM.GameState.delete]
    exact ⟨hle Q, hpos⟩
  · simp [SM.GameState.accept, SM.GameState.delete, hQP]
    exact hle Q

private theorem max_epoch_le_accept {St Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    (g : SM.GameState St Msg C) (P : Party) (st' : St) (pos : SM.Pos) :
    max (g.epoch .A) (g.epoch .B) ≤
      max ((g.accept P st' pos).epoch .A) ((g.accept P st' pos).epoch .B) := by
  cases P <;> simp [SM.GameState.accept, SM.GameState.delete] <;> omega

private structure SyncBaseRaw (prng : PRFPRNG KR Sig I K) (Δcka qep : ℕ) (tL : Option ℕ)
    (esC : AuthL10.EStateC Γ T Sig SS RS M E I) (sc : CKA.GameState Γ T)
    (esB : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I))
    (sp : PRFPRNG.GameState Sig I K) : Prop where
  sync : AuthL10.Sync prng Δcka (moBase tL) esC sc (toEStateP esB) sp
  epoch_le_qep : ∀ P, esC.g.epoch P ≤ qep
  pre_tH : max (esC.g.epoch .A) (esC.g.epoch .B) < healEpoch tL →
    postLeak tL esC.g = false ∧ esB.h.corrRoot = none
  lc_ge_tH : ∀ e, esB.h.lc = some e → healEpoch tL ≤ e

private def StepRelBase
    (prng : PRFPRNG KR Sig I K) (Δcka qep : ℕ) (tL : Option ℕ) {α : Type}
    (x : (α × AuthL10.EStateC Γ T Sig SS RS M E I) × CKA.GameState Γ T)
    (y : (α × EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)) ×
      PRFPRNG.GameState Sig I K) : Prop :=
  x.1.2.abort = true ∨
    (x.1.1 = y.1.1 ∧ SyncBaseRaw prng Δcka qep tL x.1.2 x.2 y.1.2 y.2)

private theorem leComp_strengthen_support {α β : Type} {R R' : α → β → Prop}
    {x : ProbComp α} {y : ProbComp β}
    (hx : AuthL11.LeComp R x y)
    {P : α → Prop} {Q : β → Prop}
    (hL : ∀ a ∈ support x, P a)
    (hR : ∀ b ∈ support y, Q b)
    (himp : ∀ a b, P a → Q b → R a b → R' a b) :
    AuthL11.LeComp R' x y := by
  classical
  intro F₁ F₂ hF
  let F₁' : α → ProbComp Bool := fun a => if P a then F₁ a else pure false
  let F₂' : β → ProbComp Bool := fun b => if Q b then F₂ b else pure true
  have h1 : 𝒟[x >>= F₁] {true} ≤ 𝒟[x >>= F₁'] {true} :=
    OracleComp.evalDist_bind_apply_mono_of_support x F₁ F₁' (MeasurableSet.singleton true)
      fun a ha => by simp [F₁', hL a ha]
  have h2 : 𝒟[x >>= F₁'] {true} ≤ 𝒟[y >>= F₂'] {true} :=
    hx F₁' F₂' fun a b hRab => by
      by_cases hPa : P a
      · by_cases hQb : Q b
        · simp only [F₁', F₂', hPa, hQb, ↓reduceIte]
          exact hF a b (himp a b hPa hQb hRab)
        · simp only [F₁', F₂', hPa, hQb, ↓reduceIte]
          have hle1 : 𝒟[F₁ a] {true} ≤ 1 := MeasureTheory.prob_le_one
          simp [hle1]
      · simp [F₁', hPa]
  have h3 : 𝒟[y >>= F₂'] {true} ≤ 𝒟[y >>= F₂] {true} :=
    OracleComp.evalDist_bind_apply_mono_of_support y F₂' F₂ (MeasurableSet.singleton true)
      fun b hb => by simp [F₂', hR b hb]
  exact h1.trans (h2.trans h3)

private theorem mem_support_pure {α : Type} {r x : α}
    (hr : r ∈ support (pure x : ProbComp α)) : r = x := by
  simpa only [support_pure, Set.mem_singleton_iff] using hr

private theorem mem_support_sim_run_bind {ι : Type} {spec : OracleSpec.{0, 0} ι}
    {S H α β : Type} (impl : QueryImpl spec (StateT S ProbComp))
    (m : StateT H (OracleComp spec) α) (f : α → StateT H (OracleComp spec) β)
    (h : H) (s : S) {r : (β × H) × S}
    (hr : r ∈ support ((simulateQ impl ((m >>= f).run h)).run s)) :
    ∃ r1 ∈ support ((simulateQ impl (m.run h)).run s),
      r ∈ support ((simulateQ impl ((f r1.1.1).run r1.1.2)).run r1.2) := by
  simpa only [StateT.run_bind, simulateQ_bind, support_bind, Set.mem_iUnion, exists_prop] using hr

private theorem lookupPRNGBucketF_corrRoot [DecidableEq I] [SampleableType KR]
    [SampleableType I] [SampleableType K] (prng : PRFPRNG KR Sig I K)
    (t0 : ℕ) (x : I) (h : PRNGBucketState T Sig K I) (sp : PRFPRNG.GameState Sig I K) :
    ∀ r ∈ support ((simulateQ (AuthL10.pImpl prng) ((lookupPRNGBucketF t0 x).run h)).run sp),
      r.1.2.corrRoot = h.corrRoot ∧ r.1.2.lc = h.lc := by
  intro r hr
  unfold lookupPRNGBucketF at hr
  rcases mem_support_sim_run_bind _ _ _ h sp hr with ⟨r0, hr0, hr1⟩
  simp only [StateT.run_get, simulateQ_pure] at hr0
  rcases mem_support_pure hr0 with rfl
  cases hc : (h.fTable t0).lookup x with
  | some y =>
    simp only [hc, StateT.run_pure, simulateQ_pure] at hr1
    rcases mem_support_pure hr1 with rfl
    exact ⟨rfl, rfl⟩
  | none =>
    simp only [hc] at hr1
    rcases mem_support_sim_run_bind _ _ _ h sp hr1 with ⟨r2, hr2, hr3⟩
    have h2 : r2.1.2 = h := by
      simp only [StateT.run_lift, simulateQ_bind, StateT.run_bind, support_bind,
        Set.mem_iUnion, exists_prop, map_eq_bind_pure_comp, StateT.run_pure, simulateQ_pure] at hr2
      rcases hr2 with ⟨_, _, hr2'⟩
      exact congrArg Prod.snd (congrArg Prod.fst (mem_support_pure hr2'))
    simp only [h2, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
      simulateQ_pure] at hr3
    rcases mem_support_pure hr3 with rfl
    exact ⟨rfl, rfl⟩

private theorem liftPBucket_corrRoot {α : Type} [DecidableEq I] [SampleableType KR]
    [SampleableType I] [SampleableType K] (prng : PRFPRNG KR Sig I K)
    (x : PRFPRNG.AdversaryComp Sig I K α)
    (h : PRNGBucketState T Sig K I) (sp : PRFPRNG.GameState Sig I K) :
    ∀ r ∈ support ((simulateQ (AuthL10.pImpl prng)
      ((liftPBucket (T := T) x).run h)).run sp),
      r.1.2.corrRoot = h.corrRoot ∧ r.1.2.lc = h.lc := by
  intro r hr
  simp only [liftPBucket, StateT.run_lift, map_eq_bind_pure_comp, simulateQ_bind,
    StateT.run_bind, support_bind, Set.mem_iUnion, exists_prop, StateT.run_pure,
    simulateQ_pure] at hr
  rcases hr with ⟨_, _, hr'⟩
  rcases mem_support_pure hr' with rfl
  exact ⟨rfl, rfl⟩

private theorem startRecv_PRNGBucket_corrRoot
    [DecidableEq T] [DecidableEq I] [SampleableType KR] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party) (t0 : ℕ)
    (γ0 : Γ) (σ0 : Option Sig) (tn0 : T)
    (h : PRNGBucketState T Sig K I) (sp : PRFPRNG.GameState Sig I K) :
    ∀ r ∈ support ((simulateQ (AuthL10.pImpl prng)
      (((hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t).startRecv
        ctx P t0 γ0 σ0 tn0).run h)).run sp),
      r.1.2.corrRoot = h.corrRoot ∧ r.1.2.lc = h.lc := by
  intro r hr
  dsimp only [hooksPRNGBucketHybrid, hooksPRNGBucketHybridGen] at hr
  rcases mem_support_sim_run_bind _ _ _ h sp hr with ⟨r0, hr0, hr1⟩
  simp only [StateT.run_get, simulateQ_pure] at hr0
  rcases mem_support_pure hr0 with rfl
  dsimp only at hr1
  split at hr1
  · simp only [StateT.run_pure, simulateQ_pure] at hr1
    rcases mem_support_pure hr1 with rfl; exact ⟨rfl, rfl⟩
  · split at hr1
    · split at hr1
      · simp only [StateT.run_pure, simulateQ_pure] at hr1
        rcases mem_support_pure hr1 with rfl; exact ⟨rfl, rfl⟩
      · split at hr1
        · split at hr1 <;>
            (simp only [StateT.run_pure, simulateQ_pure] at hr1; rcases mem_support_pure hr1 with rfl; exact ⟨rfl, rfl⟩)
        · split at hr1
          · rcases mem_support_sim_run_bind _ _ _ h sp hr1 with ⟨r2, hr2, hr3⟩
            have h2 := liftPBucket_corrRoot prng _ h sp r2 hr2
            rcases r2 with ⟨⟨ans2, h2'⟩, sp2⟩
            dsimp only at h2 hr3
            cases ans2 with
            | none =>
              simp only [StateT.run_pure, simulateQ_pure] at hr3
              rcases mem_support_pure hr3 with rfl; exact h2
            | some pair =>
              simp only [StateT.run_pure, simulateQ_pure] at hr3
              rcases mem_support_pure hr3 with rfl; exact h2
          · split at hr1
            · rcases mem_support_sim_run_bind _ _ _ h sp hr1 with ⟨r2, hr2, hr3⟩
              have h2 := lookupPRNGBucketF_corrRoot prng t0 _ h sp r2 hr2
              simp only [StateT.run_pure, simulateQ_pure] at hr3
              rcases mem_support_pure hr3 with rfl; exact h2
            · simp only [StateT.run_pure, simulateQ_pure] at hr1
              rcases mem_support_pure hr1 with rfl; exact ⟨rfl, rfl⟩
    · simp only [StateT.run_pure, simulateQ_pure] at hr1
      rcases mem_support_pure hr1 with rfl; exact ⟨rfl, rfl⟩

private theorem vRecv_PRNGBucket_corrRoot
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party)
    (vp : VP Γ T (Option Sig) SS RS) (c : Header T × E)
    (rec : Option (SM.Record M (Header T × E)))
    (h : PRNGBucketState T Sig K I) (sp : PRFPRNG.GameState Sig I K) :
    ∀ r ∈ support ((simulateQ (AuthL10.pImpl prng)
      ((vRecv (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t) ctx P vp c rec).run h)).run sp),
      r.1.2.corrRoot = h.corrRoot ∧ r.1.2.lc = h.lc := by
  intro r hr
  unfold vRecv at hr
  by_cases hg : (vp.id.sendsIn c.1.1 || decide (vp.tcur + 1 < c.1.1)) = true
  · simp only [hg, ↓reduceIte, StateT.run_pure, simulateQ_pure] at hr
    rcases mem_support_pure hr with rfl; exact ⟨rfl, rfl⟩
  · simp only [hg, Bool.false_eq_true, ↓reduceIte] at hr
    by_cases ht1 : c.1.1 = vp.tcur + 1
    · simp only [ht1, ↓reduceIte] at hr
      cases hc2 : c.1.2 with
      | none =>
        simp only [hc2, pure_bind, StateT.run_pure, simulateQ_pure] at hr
        rcases mem_support_pure hr with rfl; exact ⟨rfl, rfl⟩
      | some Tn =>
        simp only [hc2] at hr
        rcases mem_support_sim_run_bind _ _ _ h sp hr with ⟨ra, hra, hrb⟩
        have ha := startRecv_PRNGBucket_corrRoot cka prng fs Δcka qep tL par t
          ctx P (vp.tcur + 1) vp.γ vp.root Tn h sp ra hra
        rcases ra with ⟨⟨ansa, ha'⟩, spa⟩
        dsimp only at ha hrb
        cases ansa with
        | none =>
          simp only [pure_bind, StateT.run_pure, simulateQ_pure] at hrb
          rcases mem_support_pure hrb with rfl; exact ha
        | some opta =>
          cases opta with
          | none =>
            simp only [pure_bind, StateT.run_pure, simulateQ_pure] at hrb
            rcases mem_support_pure hrb with rfl; exact ha
          | some tri =>
            rcases tri with ⟨γ', σ', rs⟩
            simp only [pure_bind, Function.update_self, hooksPRNGBucketHybrid_fsRecv] at hrb
            cases hfs : fs.receive rs c.1 c.2 with
            | none =>
              simp only [hfs, StateT.run_pure, simulateQ_pure] at hrb
              rcases mem_support_pure hrb with rfl; exact ha
            | some vim =>
              rcases vim with ⟨v', i', m'⟩
              simp only [hfs, StateT.run_pure, simulateQ_pure] at hrb
              rcases mem_support_pure hrb with rfl; exact ha
    · simp only [ht1, ↓reduceIte, pure_bind] at hr
      cases hvR : vp.vR c.1.1 with
      | none =>
        simp only [hvR, StateT.run_pure, simulateQ_pure] at hr
        rcases mem_support_pure hr with rfl; exact ⟨rfl, rfl⟩
      | some v =>
        simp only [hvR, hooksPRNGBucketHybrid_fsRecv, pure_bind] at hr
        cases hfs : fs.receive v c.1 c.2 with
        | none =>
          simp only [hfs, StateT.run_pure, simulateQ_pure] at hr
          rcases mem_support_pure hr with rfl; exact ⟨rfl, rfl⟩
        | some vim =>
          rcases vim with ⟨v', i', m'⟩
          simp only [hfs, StateT.run_pure, simulateQ_pure] at hr
          rcases mem_support_pure hr with rfl; exact ⟨rfl, rfl⟩

private theorem liftH_vRecv_PRNGBucket_corrRoot
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party)
    (vp : VP Γ T (Option Sig) SS RS) (c : Header T × E)
    (rec : Option (SM.Record M (Header T × E)))
    (esB : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I))
    (sp : PRFPRNG.GameState Sig I K) :
    ∀ r ∈ support ((simulateQ (AuthL10.pImpl prng)
      ((liftH (vRecv (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t)
        ctx P vp c rec)).run esB)).run sp),
      r.1.2.h.corrRoot = esB.h.corrRoot ∧ r.1.2.h.lc = esB.h.lc := by
  intro r hr
  simp only [AuthL11.run_liftH, simulateQ_bind, StateT.run_bind, support_bind,
    Set.mem_iUnion, exists_prop, simulateQ_pure] at hr
  rcases hr with ⟨r1, hr1, hr2⟩
  have h1 := vRecv_PRNGBucket_corrRoot cka prng fs Δcka qep tL par t ctx P vp c rec esB.h sp r1 hr1
  rcases mem_support_pure hr2 with rfl
  exact h1

private theorem deliverE_PRNGBucket_corrRoot
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (arg : Party × (Header T × E))
    (esB : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I))
    (sp : PRFPRNG.GameState Sig I K) :
    ∀ r ∈ support ((simulateQ (AuthL10.pImpl prng)
      ((deliverE (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t) fs.maxSkip
        (bucketAuthCfg Δcka tL par) arg).run esB)).run sp),
      r.1.2.h.corrRoot = esB.h.corrRoot ∧ r.1.2.h.lc = esB.h.lc := by
  rcases arg with ⟨P, c⟩
  intro r hr
  unfold deliverE at hr
  rcases mem_support_sim_run_bind _ _ _ esB sp hr with ⟨r0, hr0, hr1⟩
  simp only [StateT.run_get, simulateQ_pure] at hr0
  rcases mem_support_pure hr0 with rfl
  dsimp only at hr1
  by_cases hguard : (esB.abort || esB.g.win) = true
  · simp only [hguard, ↓reduceIte, StateT.run_pure, simulateQ_pure] at hr1
    rcases mem_support_pure hr1 with rfl; exact ⟨rfl, rfl⟩
  · simp only [hguard, Bool.false_eq_true, ↓reduceIte] at hr1
    cases htr : esB.g.inTransit P.other c with
    | none =>
      simp only [htr, StateT.run_pure, simulateQ_pure] at hr1
      rcases mem_support_pure hr1 with rfl; exact ⟨rfl, rfl⟩
    | some rec =>
      simp only [htr] at hr1
      rcases mem_support_sim_run_bind _ _ _ esB sp hr1 with ⟨r1, hr1a, hr2⟩
      have h1 := liftH_vRecv_PRNGBucket_corrRoot cka prng fs Δcka qep tL par t
        esB.g P (esB.g.st P) c (some rec) esB sp r1 hr1a
      rcases r1 with ⟨⟨ans, es1⟩, sp1⟩
      dsimp only at h1 hr2
      cases ans with
      | none =>
        simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          simulateQ_pure] at hr2
        rcases mem_support_pure hr2 with rfl; exact h1
      | some opt =>
        cases opt with
        | none =>
          have hwin_f : (bucketAuthCfg Δcka tL par : SM.Config M).deliverWin = false := rfl
          simp only [hwin_f, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
            StateT.run_pure, simulateQ_pure] at hr2
          rcases mem_support_pure hr2 with rfl; exact h1
        | some quad =>
          rcases quad with ⟨vp', t', i', m'⟩
          simp only [commitE, AuthL11.run_liftH, hooksPRNGBucketHybrid_commit, StateT.run_bind,
            StateT.run_pure, pure_bind, StateT.run_modify, simulateQ_pure] at hr2
          rcases mem_support_pure hr2 with rfl; exact h1

private theorem deliverForgeE_PRNGBucket_corrRoot
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (arg : Party × (Header T × E) × (Header T × E))
    (esB : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I))
    (sp : PRFPRNG.GameState Sig I K) :
    ∀ r ∈ support ((simulateQ (AuthL10.pImpl prng)
      ((deliverForgeE (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t) (2 + Δcka) qep
        (bucketAuthCfg Δcka tL par) arg).run esB)).run sp),
      r.1.2.h.corrRoot = esB.h.corrRoot ∧ r.1.2.h.lc = esB.h.lc := by
  rcases arg with ⟨P, c, c'⟩
  intro r hr
  unfold deliverForgeE at hr
  rcases mem_support_sim_run_bind _ _ _ esB sp hr with ⟨r0, hr0, hr1⟩
  simp only [StateT.run_get, simulateQ_pure] at hr0
  rcases mem_support_pure hr0 with rfl
  dsimp only at hr1
  split at hr1
  · simp only [StateT.run_pure, simulateQ_pure] at hr1
    rcases mem_support_pure hr1 with rfl; exact ⟨rfl, rfl⟩
  · cases htr : esB.g.inTransit P.other c with
    | none =>
      simp only [htr, StateT.run_pure, simulateQ_pure] at hr1
      rcases mem_support_pure hr1 with rfl; exact ⟨rfl, rfl⟩
    | some rec =>
      simp only [htr] at hr1
      split at hr1
      · simp only [StateT.run_pure, simulateQ_pure] at hr1
        rcases mem_support_pure hr1 with rfl; exact ⟨rfl, rfl⟩
      · rcases mem_support_sim_run_bind _ _ _ esB sp hr1 with ⟨r1, hr1a, hr2⟩
        have h1 := liftH_vRecv_PRNGBucket_corrRoot cka prng fs Δcka qep tL par t
          esB.g P (esB.g.st P) c' none esB sp r1 hr1a
        rcases r1 with ⟨⟨ans, es1⟩, sp1⟩
        dsimp only at h1 hr2
        cases ans with
        | none =>
          simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            simulateQ_pure] at hr2
          rcases mem_support_pure hr2 with rfl; exact h1
        | some opt =>
          cases opt with
          | none =>
            simp only [StateT.run_pure, simulateQ_pure] at hr2
            rcases mem_support_pure hr2 with rfl; exact h1
          | some quad =>
            rcases quad with ⟨vp', t', i', m'⟩
            dsimp only at hr2
            split at hr2
            · simp only [StateT.run_pure, simulateQ_pure] at hr2
              rcases mem_support_pure hr2 with rfl; exact h1
            · split at hr2
              · simp only [commitE, AuthL11.run_liftH, hooksPRNGBucketHybrid_commit,
                  StateT.run_bind, StateT.run_pure, pure_bind, StateT.run_modify,
                  simulateQ_pure] at hr2
                rcases mem_support_pure hr2 with rfl; exact h1
              · split at hr2 <;>
                  (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                    simulateQ_pure] at hr2
                   rcases mem_support_pure hr2 with rfl; exact h1)

private theorem injectE_PRNGBucket_corrRoot
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (arg : Party × (Header T × E))
    (esB : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I))
    (sp : PRFPRNG.GameState Sig I K) :
    ∀ r ∈ support ((simulateQ (AuthL10.pImpl prng)
      ((injectE (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t) (2 + Δcka) qep
        (bucketAuthCfg Δcka tL par) arg).run esB)).run sp),
      r.1.2.h.corrRoot = esB.h.corrRoot ∧ r.1.2.h.lc = esB.h.lc := by
  rcases arg with ⟨P, c⟩
  intro r hr
  unfold injectE at hr
  rcases mem_support_sim_run_bind _ _ _ esB sp hr with ⟨r0, hr0, hr1⟩
  simp only [StateT.run_get, simulateQ_pure] at hr0
  rcases mem_support_pure hr0 with rfl
  dsimp only at hr1
  split at hr1
  · simp only [StateT.run_pure, simulateQ_pure] at hr1
    rcases mem_support_pure hr1 with rfl; exact ⟨rfl, rfl⟩
  · rcases mem_support_sim_run_bind _ _ _ esB sp hr1 with ⟨r1, hr1a, hr2⟩
    have h1 := liftH_vRecv_PRNGBucket_corrRoot cka prng fs Δcka qep tL par t
      esB.g P (esB.g.st P) c none esB sp r1 hr1a
    rcases r1 with ⟨⟨ans, es1⟩, sp1⟩
    dsimp only at h1 hr2
    cases ans with
    | none =>
      simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
        simulateQ_pure] at hr2
      rcases mem_support_pure hr2 with rfl; exact h1
    | some opt =>
      cases opt with
      | none =>
        simp only [StateT.run_pure, simulateQ_pure] at hr2
        rcases mem_support_pure hr2 with rfl; exact h1
      | some quad =>
        rcases quad with ⟨vp', t', i', m'⟩
        dsimp only at hr2
        split at hr2
        · simp only [StateT.run_pure, simulateQ_pure] at hr2
          rcases mem_support_pure hr2 with rfl; exact h1
        · split at hr2
          · simp only [commitE, AuthL11.run_liftH, hooksPRNGBucketHybrid_commit, StateT.run_bind,
              StateT.run_pure, pure_bind, StateT.run_modify, simulateQ_pure] at hr2
            rcases mem_support_pure hr2 with rfl; exact h1
          · split at hr2 <;>
              (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                simulateQ_pure] at hr2
               rcases mem_support_pure hr2 with rfl; exact h1)

private def PostRecvC (qep : ℕ) (tL : Option ℕ)
    (esC esC' : AuthL10.EStateC Γ T Sig SS RS M E I) : Prop :=
  esC'.abort = true ∨
    ((∀ Q, esC'.g.epoch Q ≤ qep) ∧
      max (esC.g.epoch .A) (esC.g.epoch .B) ≤ max (esC'.g.epoch .A) (esC'.g.epoch .B) ∧
      postLeak tL esC'.g = postLeak tL esC.g)

private theorem postRecvC_refl {qep : ℕ} {tL : Option ℕ}
    {esC : AuthL10.EStateC Γ T Sig SS RS M E I} (hle : ∀ Q, esC.g.epoch Q ≤ qep) :
    PostRecvC qep tL esC esC :=
  Or.inr ⟨hle, le_rfl, rfl⟩

private theorem postRecvC_accept [DecidableEq M] [DecidableEq T] [DecidableEq E]
    {qep : ℕ} {tL : Option ℕ}
    {esC es1 : AuthL10.EStateC Γ T Sig SS RS M E I}
    (hle : ∀ Q, esC.g.epoch Q ≤ qep)
    (P : Party) (st0 st1 : VP (Option Γ) T Sig SS RS) (pos : SM.Pos)
    (hpos : pos.epoch ≤ qep) :
    PostRecvC qep tL esC
      { es1 with g := { esC.g.accept P st0 pos with st := Function.update (esC.g.accept P st0 pos).st P st1 } } :=
  Or.inr ⟨epoch_accept_le_qep hle P st0 pos hpos,
    max_epoch_le_accept esC.g P st0 pos,
    postLeak_accept tL esC.g P st0 pos⟩

private theorem commitE_CKABucket_support
    [DecidableEq T] [DecidableEq M] [DecidableEq E]
    [SampleableType KC] [SampleableType CCoins] [SampleableType I]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (tL : Option ℕ) (par : Bool)
    (ctx : Ctx (Option Γ) T Sig SS RS M E) (P : Party)
    (old new : VP (Option Γ) T Sig SS RS) (pos : SM.Pos)
    (es1 : AuthL10.EStateC Γ T Sig SS RS M E I) (sc : CKA.GameState Γ T) :
    ∀ r ∈ support ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
      ((commitE (hooksCKABucket cka prng fs Δcka tL par) ctx P old new pos).run es1)).run sc),
      (r.1.1 = none ∧ r.1.2.abort = true) ∨
      (∃ new',
        r.1.1 = some { ctx.accept P new pos with st := Function.update (ctx.accept P new pos).st P new' } ∧
        r.1.2.g = es1.g) := by
  intro r hr
  unfold commitE at hr
  rcases mem_support_sim_run_bind _ _ _ es1 sc hr with ⟨r1, hr1, hr2⟩
  have hg1 : r1.1.2.g = es1.g := by
    simp only [AuthL11.run_liftH, simulateQ_bind, StateT.run_bind, support_bind,
      Set.mem_iUnion, exists_prop, simulateQ_pure] at hr1
    rcases hr1 with ⟨_, _, hr1'⟩
    rcases mem_support_pure hr1' with rfl
    rfl
  rcases r1 with ⟨⟨ans, es1'⟩, sc1⟩
  dsimp only at hg1 hr2
  cases ans with
  | none =>
    simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
      simulateQ_pure] at hr2
    rcases mem_support_pure hr2 with rfl
    exact Or.inl ⟨rfl, rfl⟩
  | some new' =>
    simp only [StateT.run_pure, simulateQ_pure] at hr2
    rcases mem_support_pure hr2 with rfl
    exact Or.inr ⟨new', rfl, hg1⟩

private theorem liftH_vRecv_CKABucket_g
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (tL : Option ℕ) (par : Bool)
    (ctx : Ctx (Option Γ) T Sig SS RS M E) (P : Party)
    (vp : VP (Option Γ) T Sig SS RS) (c : Header T × E)
    (rec : Option (SM.Record M (Header T × E)))
    (esC : AuthL10.EStateC Γ T Sig SS RS M E I) (sc : CKA.GameState Γ T) :
    ∀ r ∈ support ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
      ((liftH (vRecv (hooksCKABucket cka prng fs Δcka tL par) ctx P vp c rec)).run esC)).run sc),
      (∀ vp' t' i' m', r.1.1 = some (some (vp', t', i', m')) → t' = c.1.1) ∧
      r.1.2.g = esC.g := by
  intro r hr
  simp only [AuthL11.run_liftH, simulateQ_bind, StateT.run_bind, support_bind,
    Set.mem_iUnion, exists_prop, simulateQ_pure] at hr
  rcases hr with ⟨r0, hr0, hr0'⟩
  rcases mem_support_pure hr0' with rfl
  refine ⟨?_, rfl⟩
  intro vp' t' i' m' hans
  unfold vRecv at hr0
  by_cases hg : (vp.id.sendsIn c.1.1 || decide (vp.tcur + 1 < c.1.1)) = true
  · simp only [hg, ↓reduceIte, StateT.run_pure, simulateQ_pure] at hr0
    rcases mem_support_pure hr0 with rfl; simp at hans
  · simp only [hg, Bool.false_eq_true, ↓reduceIte] at hr0
    by_cases ht1 : c.1.1 = vp.tcur + 1
    · simp only [ht1, ↓reduceIte] at hr0
      cases hc2 : c.1.2 with
      | none =>
        simp only [hc2, pure_bind, StateT.run_pure, simulateQ_pure] at hr0
        rcases mem_support_pure hr0 with rfl; simp at hans
      | some Tn =>
        simp only [hc2] at hr0
        rcases mem_support_sim_run_bind _ _ _ esC.h sc hr0 with ⟨ra, _, hrb⟩
        rcases ra with ⟨⟨ansa, ha'⟩, sca⟩
        dsimp only at hrb
        cases ansa with
        | none =>
          simp only [pure_bind, StateT.run_pure, simulateQ_pure] at hrb
          rcases mem_support_pure hrb with rfl; simp at hans
        | some opta =>
          cases opta with
          | none =>
            simp only [pure_bind, StateT.run_pure, simulateQ_pure] at hrb
            rcases mem_support_pure hrb with rfl; simp at hans
          | some tri =>
            rcases tri with ⟨γ', σ', rs⟩
            simp only [pure_bind, Function.update_self, hooksCKABucket_fsRecv] at hrb
            cases hfs : fs.receive rs c.1 c.2 with
            | none =>
              simp only [hfs, StateT.run_pure, simulateQ_pure] at hrb
              rcases mem_support_pure hrb with rfl; simp at hans
            | some vim =>
              rcases vim with ⟨v2, i2, m2⟩
              simp only [hfs, StateT.run_pure, simulateQ_pure] at hrb
              rcases mem_support_pure hrb with rfl
              simp only [Option.some.injEq, Prod.mk.injEq] at hans
              exact hans.2.1.symm.trans ht1.symm
    · simp only [ht1, ↓reduceIte, pure_bind] at hr0
      cases hvR : vp.vR c.1.1 with
      | none =>
        simp only [hvR, StateT.run_pure, simulateQ_pure] at hr0
        rcases mem_support_pure hr0 with rfl; simp at hans
      | some v =>
        simp only [hvR, hooksCKABucket_fsRecv, pure_bind] at hr0
        cases hfs : fs.receive v c.1 c.2 with
        | none =>
          simp only [hfs, StateT.run_pure, simulateQ_pure] at hr0
          rcases mem_support_pure hr0 with rfl; simp at hans
        | some vim =>
          rcases vim with ⟨v2, i2, m2⟩
          simp only [hfs, StateT.run_pure, simulateQ_pure] at hr0
          rcases mem_support_pure hr0 with rfl
          simp only [Option.some.injEq, Prod.mk.injEq] at hans
          exact hans.2.1.symm

private theorem deliverE_CKABucket_post
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (arg : Party × (Header T × E))
    {esC : AuthL10.EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esB : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : SyncBaseRaw prng Δcka qep tL esC sc esB sp) :
    ∀ r ∈ support ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
      ((deliverE (hooksCKABucket cka prng fs Δcka tL par) fs.maxSkip
        (bucketAuthCfg Δcka tL par) arg).run esC)).run sc),
      PostRecvC qep tL esC r.1.2 := by
  rcases arg with ⟨P, c⟩
  intro r hr
  unfold deliverE at hr
  rcases mem_support_sim_run_bind _ _ _ esC sc hr with ⟨r0, hr0, hr1⟩
  simp only [StateT.run_get, simulateQ_pure] at hr0
  rcases mem_support_pure hr0 with rfl
  dsimp only at hr1
  split at hr1
  · simp only [StateT.run_pure, simulateQ_pure] at hr1
    rcases mem_support_pure hr1 with rfl; exact postRecvC_refl hS.epoch_le_qep
  · cases htr : esC.g.inTransit P.other c with
    | none =>
      simp only [htr, StateT.run_pure, simulateQ_pure] at hr1
      rcases mem_support_pure hr1 with rfl; exact postRecvC_refl hS.epoch_le_qep
    | some rec =>
      simp only [htr] at hr1
      obtain ⟨hmem, _, _⟩ := AuthL10.inTransit_some_props htr
      have hpos_le : rec.pos.epoch ≤ qep :=
        ((hS.sync.trans_inv rec hmem).2.2.1).trans (hS.epoch_le_qep rec.pos.sender)
      rcases mem_support_sim_run_bind _ _ _ esC sc hr1 with ⟨r1, hr1a, hr2⟩
      obtain ⟨_, hg1⟩ := liftH_vRecv_CKABucket_g cka prng fs Δcka tL par esC.g P (esC.g.st P) c
        (some rec) esC sc r1 hr1a
      rcases r1 with ⟨⟨ans, es1⟩, sc1⟩
      dsimp only at hg1 hr2
      cases ans with
      | none =>
        simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          simulateQ_pure] at hr2
        rcases mem_support_pure hr2 with rfl; exact Or.inl rfl
      | some opt =>
        cases opt with
        | none =>
          have hwin_f : (bucketAuthCfg Δcka tL par : SM.Config M).deliverWin = false := rfl
          simp only [hwin_f, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
            StateT.run_pure, simulateQ_pure] at hr2
          rcases mem_support_pure hr2 with rfl
          exact Or.inr ⟨hg1 ▸ hS.epoch_le_qep, by simp [hg1], by simp [hg1]⟩
        | some quad =>
          rcases quad with ⟨vp', t', i', m'⟩
          rcases mem_support_sim_run_bind _ _ _ es1 sc1 hr2 with ⟨r2, hr2a, hr2b⟩
          have hc2 := commitE_CKABucket_support cka prng fs Δcka tL par esC.g P (esC.g.st P)
            vp' rec.pos es1 sc1 r2 hr2a
          rcases r2 with ⟨⟨cans, es2⟩, sc2⟩
          dsimp only at hr2b
          rcases hc2 with ⟨rfl, hab2⟩ | ⟨new', rfl, _⟩
          · simp only [StateT.run_pure, simulateQ_pure] at hr2b
            rcases mem_support_pure hr2b with rfl; exact Or.inl hab2
          · have hwin_f : (bucketAuthCfg Δcka tL par : SM.Config M).deliverWin = false := rfl
            simp only [hwin_f, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
              StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              simulateQ_pure] at hr2b
            rcases mem_support_pure hr2b with rfl
            exact postRecvC_accept hS.epoch_le_qep P vp' new' rec.pos hpos_le

private theorem deliverForgeE_CKABucket_post
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (arg : Party × (Header T × E) × (Header T × E))
    {esC : AuthL10.EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esB : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : SyncBaseRaw prng Δcka qep tL esC sc esB sp) :
    ∀ r ∈ support ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
      ((deliverForgeE (hooksCKABucket cka prng fs Δcka tL par) (2 + Δcka) qep
        (bucketAuthCfg Δcka tL par) arg).run esC)).run sc),
      PostRecvC qep tL esC r.1.2 := by
  rcases arg with ⟨P, c, c'⟩
  intro r hr
  unfold deliverForgeE at hr
  rcases mem_support_sim_run_bind _ _ _ esC sc hr with ⟨r0, hr0, hr1⟩
  simp only [StateT.run_get, simulateQ_pure] at hr0
  rcases mem_support_pure hr0 with rfl
  dsimp only at hr1
  split at hr1
  · simp only [StateT.run_pure, simulateQ_pure] at hr1
    rcases mem_support_pure hr1 with rfl; exact postRecvC_refl hS.epoch_le_qep
  · cases htr : esC.g.inTransit P.other c with
    | none =>
      simp only [htr, StateT.run_pure, simulateQ_pure] at hr1
      rcases mem_support_pure hr1 with rfl; exact postRecvC_refl hS.epoch_le_qep
    | some rec =>
      simp only [htr] at hr1
      split at hr1
      · simp only [StateT.run_pure, simulateQ_pure] at hr1
        rcases mem_support_pure hr1 with rfl; exact postRecvC_refl hS.epoch_le_qep
      · obtain ⟨hmem, _, _⟩ := AuthL10.inTransit_some_props htr
        have hrec_le : rec.pos.epoch ≤ qep :=
          ((hS.sync.trans_inv rec hmem).2.2.1).trans (hS.epoch_le_qep rec.pos.sender)
        rcases mem_support_sim_run_bind _ _ _ esC sc hr1 with ⟨r1, hr1a, hr2⟩
        obtain ⟨_, hg1⟩ := liftH_vRecv_CKABucket_g cka prng fs Δcka tL par esC.g P (esC.g.st P) c'
          none esC sc r1 hr1a
        rcases r1 with ⟨⟨ans, es1⟩, sc1⟩
        dsimp only at hg1 hr2
        cases ans with
        | none =>
          simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            simulateQ_pure] at hr2
          rcases mem_support_pure hr2 with rfl; exact Or.inl rfl
        | some opt =>
          cases opt with
          | none =>
            simp only [StateT.run_pure, simulateQ_pure] at hr2
            rcases mem_support_pure hr2 with rfl
            exact Or.inr ⟨hg1 ▸ hS.epoch_le_qep, by simp [hg1], by simp [hg1]⟩
          | some quad =>
            rcases quad with ⟨vp', t', i', m'⟩
            by_cases hbad : (decide (qep + 1 < t') || (t' != rec.pos.epoch)) = true
            · simp only [hbad, ↓reduceIte, StateT.run_pure, simulateQ_pure] at hr2
              rcases mem_support_pure hr2 with rfl
              exact Or.inr ⟨hg1 ▸ hS.epoch_le_qep, by simp [hg1], by simp [hg1]⟩
            · simp only [hbad, Bool.false_eq_true, ↓reduceIte] at hr2
              have ht'_eq : t' = rec.pos.epoch := by
                simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at hbad
                exact hbad.2
              split at hr2
              · rcases mem_support_sim_run_bind _ _ _ es1 sc1 hr2 with ⟨r2, hr2a, hr2b⟩
                have hc2 := commitE_CKABucket_support cka prng fs Δcka tL par esC.g P (esC.g.st P)
                  vp' ⟨P.other, t', i'⟩ es1 sc1 r2 hr2a
                rcases r2 with ⟨⟨cans, es2⟩, sc2⟩
                dsimp only at hr2b
                rcases hc2 with ⟨rfl, hab2⟩ | ⟨new', rfl, _⟩
                · simp only [StateT.run_pure, simulateQ_pure] at hr2b
                  rcases mem_support_pure hr2b with rfl; exact Or.inl hab2
                · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                    simulateQ_pure] at hr2b
                  rcases mem_support_pure hr2b with rfl
                  exact postRecvC_accept hS.epoch_le_qep P vp' new' ⟨P.other, t', i'⟩
                    (ht'_eq ▸ hrec_le)
              · split at hr2
                · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                    simulateQ_pure] at hr2
                  rcases mem_support_pure hr2 with rfl
                  exact Or.inr ⟨hg1 ▸ hS.epoch_le_qep, by simp [hg1], by simp [hg1, postLeak]⟩
                · simp only [StateT.run_pure, simulateQ_pure] at hr2
                  rcases mem_support_pure hr2 with rfl
                  exact Or.inr ⟨hg1 ▸ hS.epoch_le_qep, by simp [hg1], by simp [hg1]⟩

private theorem injectE_CKABucket_post
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (arg : Party × (Header T × E))
    {esC : AuthL10.EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esB : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : SyncBaseRaw prng Δcka qep tL esC sc esB sp) :
    ∀ r ∈ support ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
      ((injectE (hooksCKABucket cka prng fs Δcka tL par) (2 + Δcka) qep
        (bucketAuthCfg Δcka tL par) arg).run esC)).run sc),
      PostRecvC qep tL esC r.1.2 := by
  rcases arg with ⟨P, c⟩
  intro r hr
  unfold injectE at hr
  rcases mem_support_sim_run_bind _ _ _ esC sc hr with ⟨r0, hr0, hr1⟩
  simp only [StateT.run_get, simulateQ_pure] at hr0
  rcases mem_support_pure hr0 with rfl
  dsimp only at hr1
  by_cases hguard : (esC.abort || esC.g.win || (esC.g.inTransit P.other c).isSome ||
      !esC.g.safeInj (2 + Δcka)) = true
  · simp only [hguard, ↓reduceIte, StateT.run_pure, simulateQ_pure] at hr1
    rcases mem_support_pure hr1 with rfl; exact postRecvC_refl hS.epoch_le_qep
  · simp only [hguard, Bool.false_eq_true, ↓reduceIte] at hr1
    have hsafe : esC.g.safeInj (2 + Δcka) = true := by
      revert hguard; cases esC.abort <;> cases esC.g.win <;>
        cases (esC.g.inTransit P.other c).isSome <;> cases esC.g.safeInj (2 + Δcka) <;> simp
    by_cases hvguard : (P.sendsIn c.1.1 || decide (esC.g.epoch P + 1 < c.1.1)) = true
    · have hvnone : vRecv (hooksCKABucket cka prng fs Δcka tL par) esC.g P (esC.g.st P) c none =
          pure (some none) := by
        unfold vRecv
        rw [hS.sync.id_C P, hS.sync.tcur_C P]
        rcases Bool.or_eq_true_iff.mp hvguard with hs | hlt
        · simp [hs]
        · simp [decide_eq_true_eq.mp hlt]
      rw [hvnone] at hr1
      simp only [AuthL11.run_liftH, StateT.run_pure, StateT.run_bind, pure_bind,
        simulateQ_pure] at hr1
      rcases mem_support_pure hr1 with rfl
      exact postRecvC_refl hS.epoch_le_qep
    · have hsend0 : P.sendsIn c.1.1 = false := by
        revert hvguard; cases P.sendsIn c.1.1 <;> simp
      have hle_succ : c.1.1 ≤ esC.g.epoch P + 1 := by
        revert hvguard; simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt]
        exact And.right
      rcases mem_support_sim_run_bind _ _ _ esC sc hr1 with ⟨r1, hr1a, hr2⟩
      obtain ⟨ht_eq_fn, hg1⟩ := liftH_vRecv_CKABucket_g cka prng fs Δcka tL par
        esC.g P (esC.g.st P) c none esC sc r1 hr1a
      rcases r1 with ⟨⟨ans, es1⟩, sc1⟩
      dsimp only at hg1 hr2
      cases ans with
      | none =>
        simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          simulateQ_pure] at hr2
        rcases mem_support_pure hr2 with rfl; exact Or.inl rfl
      | some opt =>
        cases opt with
        | none =>
          simp only [StateT.run_pure, simulateQ_pure] at hr2
          rcases mem_support_pure hr2 with rfl
          exact Or.inr ⟨hg1 ▸ hS.epoch_le_qep, by simp [hg1], by simp [hg1]⟩
        | some quad =>
          rcases quad with ⟨vp', t', i', m'⟩
          have ht' : t' = c.1.1 := ht_eq_fn vp' t' i' m' rfl
          subst ht'
          dsimp only at hr2
          split at hr2
          · simp only [StateT.run_pure, simulateQ_pure] at hr2
            rcases mem_support_pure hr2 with rfl
            exact Or.inr ⟨hg1 ▸ hS.epoch_le_qep, by simp [hg1], by simp [hg1]⟩
          · by_cases htriv : esC.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ = true
            · simp only [htriv, ↓reduceIte] at hr2
              have hne_new : c.1.1 ≠ esC.g.epoch P + 1 := by
                intro hnew
                have htf := AuthL10.trivial_false_of_safeInj esC.g (2 + Δcka) P i' hsafe
                  hS.sync.comp_inv
                rw [hnew, htf] at htriv
                cases htriv
              have hc_le : c.1.1 ≤ qep := by
                have hep := hS.epoch_le_qep P
                omega
              rcases mem_support_sim_run_bind _ _ _ es1 sc1 hr2 with ⟨r2, hr2a, hr2b⟩
              have hc2 := commitE_CKABucket_support cka prng fs Δcka tL par esC.g P (esC.g.st P)
                vp' ⟨P.other, c.1.1, i'⟩ es1 sc1 r2 hr2a
              rcases r2 with ⟨⟨cans, es2⟩, sc2⟩
              dsimp only at hr2b
              rcases hc2 with ⟨rfl, hab2⟩ | ⟨new', rfl, _⟩
              · simp only [StateT.run_pure, simulateQ_pure] at hr2b
                rcases mem_support_pure hr2b with rfl; exact Or.inl hab2
              · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                  simulateQ_pure] at hr2b
                rcases mem_support_pure hr2b with rfl
                exact postRecvC_accept hS.epoch_le_qep P vp' new' ⟨P.other, c.1.1, i'⟩ hc_le
            · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hr2
              split at hr2
              · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                  simulateQ_pure] at hr2
                rcases mem_support_pure hr2 with rfl
                exact Or.inr ⟨hg1 ▸ hS.epoch_le_qep, by simp [hg1], by simp [hg1, postLeak]⟩
              · simp only [StateT.run_pure, simulateQ_pure] at hr2
                rcases mem_support_pure hr2 with rfl
                exact Or.inr ⟨hg1 ▸ hS.epoch_le_qep, by simp [hg1], by simp [hg1]⟩

private theorem stepRelBase_of_postRecvC
    {prng : PRFPRNG KR Sig I K} {Δcka qep : ℕ} {tL : Option ℕ} {α : Type}
    {esC : AuthL10.EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esB : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : SyncBaseRaw prng Δcka qep tL esC sc esB sp)
    (a : (α × AuthL10.EStateC Γ T Sig SS RS M E I) × CKA.GameState Γ T)
    (b : (α × EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)) ×
      PRFPRNG.GameState Sig I K)
    (ha : PostRecvC qep tL esC a.1.2)
    (hb : b.1.2.h.corrRoot = esB.h.corrRoot ∧ b.1.2.h.lc = esB.h.lc)
    (hr : StepRelBaseRaw prng Δcka tL a b) :
    StepRelBase prng Δcka qep tL a b := by
  rcases hr with hab | ⟨hu, hsync'⟩
  · exact Or.inl hab
  · rcases ha with hab | ⟨hep', hmax_le, hpl_eq⟩
    · exact Or.inl hab
    · refine Or.inr ⟨hu, ⟨hsync', hep', fun hlt => ?_, fun e he => hS.lc_ge_tH e (hb.2 ▸ he)⟩⟩
      obtain ⟨hpl0, hcr0⟩ := hS.pre_tH (lt_of_le_of_lt hmax_le hlt)
      exact ⟨hpl_eq.trans hpl0, hb.1.trans hcr0⟩

private theorem leComp_deliverE_base_sync
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (arg : Party × (Header T × E))
    {esC : AuthL10.EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esB : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : SyncBaseRaw prng Δcka qep tL esC sc esB sp) :
    AuthL11.LeComp (StepRelBase prng Δcka qep tL)
      ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
        ((deliverE (hooksCKABucket cka prng fs Δcka tL par) fs.maxSkip
          (bucketAuthCfg Δcka tL par) arg).run esC)).run sc)
      ((simulateQ (AuthL10.pImpl prng)
        ((deliverE (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL)) fs.maxSkip
          (bucketAuthCfg Δcka tL par) arg).run esB)).run sp) :=
  leComp_strengthen_support
    (leComp_deliverE_base cka prng fs Δcka qep tL par arg hS.sync)
    (deliverE_CKABucket_post cka prng fs Δcka qep tL par arg hS)
    (deliverE_PRNGBucket_corrRoot cka prng fs Δcka qep tL par (healEpoch tL) arg esB sp)
    (stepRelBase_of_postRecvC hS)

private theorem leComp_deliverForgeE_base_sync
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (arg : Party × (Header T × E) × (Header T × E))
    {esC : AuthL10.EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esB : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : SyncBaseRaw prng Δcka qep tL esC sc esB sp) :
    AuthL11.LeComp (StepRelBase prng Δcka qep tL)
      ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
        ((deliverForgeE (hooksCKABucket cka prng fs Δcka tL par) (2 + Δcka) qep
          (bucketAuthCfg Δcka tL par) arg).run esC)).run sc)
      ((simulateQ (AuthL10.pImpl prng)
        ((deliverForgeE (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
          (2 + Δcka) qep (bucketAuthCfg Δcka tL par) arg).run esB)).run sp) :=
  leComp_strengthen_support
    (leComp_deliverForgeE_base cka prng fs Δcka qep tL par arg hS.sync)
    (deliverForgeE_CKABucket_post cka prng fs Δcka qep tL par arg hS)
    (deliverForgeE_PRNGBucket_corrRoot cka prng fs Δcka qep tL par (healEpoch tL) arg esB sp)
    (stepRelBase_of_postRecvC hS)

private theorem leComp_injectE_base_sync
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (arg : Party × (Header T × E))
    {esC : AuthL10.EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esB : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : SyncBaseRaw prng Δcka qep tL esC sc esB sp) :
    AuthL11.LeComp (StepRelBase prng Δcka qep tL)
      ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
        ((injectE (hooksCKABucket cka prng fs Δcka tL par) (2 + Δcka) qep
          (bucketAuthCfg Δcka tL par) arg).run esC)).run sc)
      ((simulateQ (AuthL10.pImpl prng)
        ((injectE (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
          (2 + Δcka) qep (bucketAuthCfg Δcka tL par) arg).run esB)).run sp) :=
  leComp_strengthen_support
    (leComp_injectE_base cka prng fs Δcka qep tL par arg hS.sync)
    (injectE_CKABucket_post cka prng fs Δcka qep tL par arg hS)
    (injectE_PRNGBucket_corrRoot cka prng fs Δcka qep tL par (healEpoch tL) arg esB sp)
    (stepRelBase_of_postRecvC hS)

private theorem leComp_corrChoice_base_sync
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par paper : Bool) (P : Party)
    {esC : AuthL10.EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esB : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {sp : PRFPRNG.GameState Sig I K}
    (hSB : SyncBaseRaw prng Δcka qep tL esC sc esB sp) :
    AuthL11.LeComp (StepRelBase prng Δcka qep tL)
      ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
        (((if paper then corrEPaperBucket (hooksCKABucket cka prng fs Δcka tL par)
           else corrEBucket (hooksCKABucket cka prng fs Δcka tL par)) P).run esC)).run sc)
      ((simulateQ (AuthL10.pImpl prng)
        (((if paper then
            corrEPaperBucket (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
           else corrEBucket (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL)))
          P).run esB)).run sp) := by
  have hS := hSB.sync
  have habC : esC.abort = false := hS.abort_C
  have habB : esB.abort = false := hS.abort_P
  have hwin : esB.g.win = esC.g.win := AuthL10.eraseSt_win hS.g_eq
  have hca_std : esB.g.corrAllowed P = esC.g.corrAllowed P :=
    AuthL10.eraseSt_corrAllowed hS.g_eq P
  have hca_pap : esB.g.corrAllowedPaper P = esC.g.corrAllowedPaper P :=
    AuthL11.eraseSt_corrAllowedPaper hS.g_eq P
  let caC := if paper then esC.g.corrAllowedPaper P else esC.g.corrAllowed P
  by_cases hguard : esC.g.win || !caC
  · simp only [Bool.or_eq_true, Bool.not_eq_true'] at hguard
    have hC : ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
        (((if paper then corrEPaperBucket (hooksCKABucket cka prng fs Δcka tL par)
           else corrEBucket (hooksCKABucket cka prng fs Δcka tL par)) P).run esC)).run sc) =
        pure ((none, esC), sc) := by
      cases paper <;> simp [caC] at hguard <;>
        simp [corrEBucket, corrEPaperBucket, habC, hguard]
    have hB : ((simulateQ (AuthL10.pImpl prng)
        (((if paper then
            corrEPaperBucket (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
           else corrEBucket (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL)))
          P).run esB)).run sp) =
        pure ((none, esB), sp) := by
      cases paper <;> simp [caC] at hguard <;>
        simp [corrEBucket, corrEPaperBucket, habB, hwin, hca_std, hca_pap, hguard]
    rw [hC, hB]
    exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hSB⟩)
  · simp only [Bool.not_eq_true, Bool.or_eq_false_iff, Bool.not_eq_false'] at hguard
    have hrootB : (esB.g.st P).root = some (esC.g.st P).root := root_P_moBase hS P
    have htcurB : (esB.g.st P).tcur = esC.g.epoch P := hS.tcur_P P
    have hrp := hS.realParty_eq P ((toEStateP esB).g.st P).γ (esC.g.st P).root
    let hB1 : PRNGBucketState T Sig K I :=
      if !(esC.g.epoch P < healEpoch tL) && esB.h.corrRoot.isNone then
        { esB.h with corrRoot := some (esC.g.epoch P, (esC.g.st P).root) }
      else esB.h
    let hB' : PRNGBucketState T Sig K I :=
      if !(postLeak tL esB.g) && esB.h.lc.isNone && !(esC.g.epoch P < healEpoch tL) then
        { hB1 with lc := some (esC.g.epoch P) }
      else hB1
    have hcacheB' : hB'.cache = esB.h.cache := by
      dsimp only [hB', hB1]; split_ifs <;> rfl
    have hlc1 : hB1.lc = esB.h.lc := by
      dsimp only [hB1]; split_ifs <;> rfl
    have hlcB' : ∀ e, hB'.lc = some e → healEpoch tL ≤ e := by
      intro e he
      dsimp only [hB'] at he
      split_ifs at he with h1
      · simp only [Option.some.injEq] at he; subst he
        simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h1
        exact Nat.le_of_not_lt h1.2
      · rw [hlc1] at he
        exact hSB.lc_ge_tH e he
    have htoP_after :
        toEStateP { esB with g := esB.g.afterCorr P, h := hB' } =
          { toEStateP esB with g := (toEStateP esB).g.afterCorr P } := by
      simp [toEStateP, hcacheB']
    have hsync_after : ∀ {sc'},
        AuthL10.Sync prng Δcka (moBase tL)
          { esC with g := esC.g.afterCorr P } sc'
          { toEStateP esB with g := (toEStateP esB).g.afterCorr P } sp →
        AuthL10.Sync prng Δcka (moBase tL)
          { esC with g := esC.g.afterCorr P } sc'
          (toEStateP { esB with g := esB.g.afterCorr P, h := hB' }) sp := by
      intro sc' hs; rw [htoP_after]; exact hs
    have hB :
        ((simulateQ (AuthL10.pImpl prng)
          (((if paper then
              corrEPaperBucket (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
             else corrEBucket (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL)))
            P).run esB)).run sp) =
          pure ((some (realParty (esC.g.st P) ((toEStateP esB).g.st P).γ (esC.g.st P).root
            (esC.g.st P).vS (esC.g.st P).vR),
            { esB with g := esB.g.afterCorr P, h := hB' }), sp) := by
      dsimp only [toEStateP] at hrp ⊢
      cases paper <;> simp [caC] at hguard <;>
        simp [-Prod.mk.injEq, corrEBucket, corrEPaperBucket, liftH,
          hooksPRNGBucketHybrid_reveal_some_run _ _ _ _ _ _ _ _ _ _ _ _ hrootB,
          habB, hwin, hca_std, hca_pap, hguard, htcurB, hB', hB1,
          StateT.run_bind, StateT.run_get, StateT.run_modify, StateT.run_pure,
          pure_bind, hrp]
    by_cases hloc : AuthL10.localCKA (moBase tL) Δcka (esC.g.epoch P)
    · have hγC : (esC.g.st P).γ = some ((toEStateP esB).g.st P).γ := by
        rw [hS.γ_C P, hloc]; rfl
      have hnot_pre : ¬ max ((esC.g.afterCorr P).epoch .A) ((esC.g.afterCorr P).epoch .B) < healEpoch tL := by
        dsimp only [SM.GameState.afterCorr, SM.GameState.leak]
        have hep_le : esC.g.epoch P ≤ max (esC.g.epoch .A) (esC.g.epoch .B) := by
          cases P <;> simp
        simp only [AuthL10.localCKA, moBase_tL, moBase_tH, Bool.or_eq_true, decide_eq_true_eq] at hloc
        rcases hloc with hnone | hge
        · cases tL <;> simp at hnone ⊢
        · omega
      have hC : ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
          (((if paper then corrEPaperBucket (hooksCKABucket cka prng fs Δcka tL par)
             else corrEBucket (hooksCKABucket cka prng fs Δcka tL par)) P).run esC)).run sc) =
          pure ((some (realParty (esC.g.st P) ((toEStateP esB).g.st P).γ (esC.g.st P).root
            (esC.g.st P).vS (esC.g.st P).vR),
            { esC with g := esC.g.afterCorr P }), sc) := by
        cases paper <;> simp [caC] at hguard <;>
          simp [corrEBucket, corrEPaperBucket, hooksCKABucket, hooksCKA, habC, hguard, hγC,
            StateT.run_modify]
      rw [hC, hB]
      exact AuthL11.LeComp.pure (Or.inr ⟨rfl, ⟨hsync_after (hS.afterCorr P),
        fun Q => by dsimp only [SM.GameState.afterCorr, SM.GameState.leak]; exact hSB.epoch_le_qep Q,
        fun hlt => (hnot_pre hlt).elim, hlcB'⟩⟩)
    · simp only [Bool.not_eq_true] at hloc
      have hγC : (esC.g.st P).γ = none := by rw [hS.γ_C P, hloc]; rfl
      obtain ⟨hcka_stP, hcka_epP⟩ := hS.cka_st P (Or.inl hloc)
      obtain ⟨_, hcka_epO⟩ := hS.cka_st P.other (Or.inr (by simpa using hloc))
      by_cases hcorr : sc.allowCorr (healEpoch tL) || sc.finished Δcka (healEpoch tL) P
      · simp only [Bool.or_eq_true] at hcorr
        have hC : ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
            (((if paper then corrEPaperBucket (hooksCKABucket cka prng fs Δcka tL par)
               else corrEBucket (hooksCKABucket cka prng fs Δcka tL par)) P).run esC)).run sc) =
            pure ((some (realParty (esC.g.st P) ((toEStateP esB).g.st P).γ (esC.g.st P).root
              (esC.g.st P).vS (esC.g.st P).vR),
              { esC with g := esC.g.afterCorr P }), sc) := by
          cases paper <;> simp [caC] at hguard <;>
            simp [corrEBucket, corrEPaperBucket, hooksCKABucket, hooksCKA, liftC, CKA.corrQuery,
              AuthL10.cImpl, CKA.oracleImpl, CKA.corrImpl, habC, hguard, hγC, hcorr, hcka_stP,
              simulateQ_bind, simulateQ_query, map_eq_bind_pure_comp, StateT.run_modify]
        rw [hC, hB]
        refine AuthL11.LeComp.pure (Or.inr ⟨rfl, ⟨hsync_after (hS.afterCorr P),
          fun Q => by dsimp only [SM.GameState.afterCorr, SM.GameState.leak]; exact hSB.epoch_le_qep Q,
          fun hlt => ?_, hlcB'⟩⟩)
        dsimp only [SM.GameState.afterCorr, SM.GameState.leak] at hlt
        obtain ⟨hpl0, hcr0⟩ := hSB.pre_tH hlt
        have hmax_sc : max (sc.epoch .A) (sc.epoch .B) = max (esC.g.epoch .A) (esC.g.epoch .B) := by
          cases P <;> simp [Party.other] at hcka_epP hcka_epO <;> simp [hcka_epP, hcka_epO]
        have hfin_f : sc.finished Δcka (healEpoch tL) P = false := by
          have hep_le : esC.g.epoch P ≤ max (esC.g.epoch .A) (esC.g.epoch .B) := by
            cases P <;> simp
          simp [CKA.GameState.finished, hcka_epP]; omega
        have hallow : sc.allowCorr (healEpoch tL) = true := by
          rcases hcorr with h1 | h2
          · exact h1
          · rw [hfin_f] at h2; cases h2
        have hmax_lt : max (esC.g.epoch .A) (esC.g.epoch .B) + 1 < healEpoch tL := by
          simp [CKA.GameState.allowCorr, hmax_sc] at hallow; omega
        refine ⟨postLeak_afterCorr_false_of_lt_tH P hpl0 hmax_lt, ?_⟩
        have hep_le : esC.g.epoch P ≤ max (esC.g.epoch .A) (esC.g.epoch .B) := by
          cases P <;> simp
        have hlt_ep : esC.g.epoch P < healEpoch tL := by omega
        simp [hB', hB1, hlt_ep, hcr0]
      · simp only [Bool.not_eq_true, Bool.or_eq_false_iff] at hcorr
        have hC : ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
            (((if paper then corrEPaperBucket (hooksCKABucket cka prng fs Δcka tL par)
               else corrEBucket (hooksCKABucket cka prng fs Δcka tL par)) P).run esC)).run sc) =
            pure ((none, { esC with abort := true }), sc) := by
          cases paper <;> simp [caC] at hguard <;>
            simp [corrEBucket, corrEPaperBucket, abortE, hooksCKABucket, hooksCKA, liftC,
              CKA.corrQuery, AuthL10.cImpl, CKA.oracleImpl, CKA.corrImpl, habC, hguard, hγC, hcorr,
              simulateQ_bind, simulateQ_query, map_eq_bind_pure_comp, StateT.run_modify]
        rw [hC]
        exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl

private theorem leComp_transmitEBucket_same_base
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (P : Party) (m_msg : M) (r : Option CCoins)
    {esC : AuthL10.EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esB : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : SyncBaseRaw prng Δcka qep tL esC sc esB sp)
    (hwin0 : esC.g.win = false)
    (hsend : P.sendsIn (esC.g.epoch P + 1) = false) :
    AuthL11.LeComp (StepRelBase prng Δcka qep tL)
      ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
        ((transmitEBucket (hooksCKABucket cka prng fs Δcka tL par)
          (2 + Δcka) qep (P, m_msg, r)).run esC)).run sc)
      ((simulateQ (AuthL10.pImpl prng)
        ((transmitEBucket (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
          (2 + Δcka) qep (P, m_msg, r)).run esB)).run sp) := by
  have hsync := hS.sync
  have hwin : esB.g.win = esC.g.win := AuthL10.eraseSt_win hsync.g_eq
  have hepP : esB.g.epoch P = esC.g.epoch P := congrFun (AuthL10.eraseSt_epoch hsync.g_eq) P
  have hidxP : esB.g.idx P = esC.g.idx P := congrFun (AuthL10.eraseSt_idx hsync.g_eq) P
  have habC : esC.abort = false := hsync.abort_C
  have habB : esB.abort = false := hsync.abort_P
  have hidC : (esC.g.st P).id = P := hsync.id_C P
  have hidB : (esB.g.st P).id = P := hsync.id_P P
  have htcurC : (esC.g.st P).tcur = esC.g.epoch P := hsync.tcur_C P
  have htcurB : (esB.g.st P).tcur = esC.g.epoch P := hsync.tcur_P P
  have hvSB : (esB.g.st P).vS = (esC.g.st P).vS := hsync.vS_eq P
  have hTcurB : (esB.g.st P).curCkaMsg = (esC.g.st P).curCkaMsg := hsync.Tcur_eq P
  have hsend0 : P.sendsIn (esC.g.epoch P) = true := AuthL10.sendsIn_of_succ_false hsend
  have hqep : ¬ (qep < esC.g.epoch P) := Nat.not_lt.mpr (hS.epoch_le_qep P)
  cases hvS : (esC.g.st P).vS with
  | none =>
    have hstC : ({ esC.g.st P with vS := none } : VP (Option Γ) T Sig SS RS) = esC.g.st P := by
      rcases h : esC.g.st P with ⟨id, root, vS, vR, γ, curCkaMsg, tcur⟩
      rw [h] at hvS; subst hvS; rfl
    have hstB : ({ esB.g.st P with vS := none } : VP Γ T (Option Sig) SS RS) = esB.g.st P := by
      have hvSB0 : (esB.g.st P).vS = none := hvSB.trans hvS
      rcases h : esB.g.st P with ⟨id, root, vS, vR, γ, curCkaMsg, tcur⟩
      rw [h] at hvSB0; subst hvSB0; rfl
    let c : Header T × E := ((esC.g.epoch P, (esC.g.st P).curCkaMsg), default)
    let rcd : SM.Record M (Header T × E) := ⟨⟨P, esC.g.epoch P, esC.g.idx P + 1⟩, m_msg, c⟩
    have hC : ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
        ((transmitEBucket (hooksCKABucket cka prng fs Δcka tL par)
          (2 + Δcka) qep (P, m_msg, r)).run esC)).run sc) =
        pure ((some c,
          { esC with g := esC.g.record (2 + Δcka) P { esC.g.st P with vS := none } rcd false }), sc) := by
      rw [hstC]; simp [-Prod.mk.injEq, transmitEBucket, vSend, SM.GameState.epMgmt, habC, hwin0,
        hsend, hqep, hidC, htcurC, hvS, c, rcd, AuthL11.run_liftH, StateT.run_bind, StateT.run_get,
        StateT.run_modify, StateT.run_pure, simulateQ_bind, simulateQ_pure, map_eq_bind_pure_comp]
    have hB : ((simulateQ (AuthL10.pImpl prng)
        ((transmitEBucket (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
          (2 + Δcka) qep (P, m_msg, r)).run esB)).run sp) =
        pure ((some c,
          { esB with g := esB.g.record (2 + Δcka) P { esB.g.st P with vS := none } rcd false }), sp) := by
      rw [hstB]; simp [-Prod.mk.injEq, transmitEBucket, vSend, SM.GameState.epMgmt, habB, hwin, hwin0,
        hepP, hidxP, hsend, hqep, hidB, htcurB, hvSB, hvS, hTcurB, c, rcd, AuthL11.run_liftH,
        StateT.run_bind, StateT.run_get, StateT.run_modify, StateT.run_pure,
        simulateQ_bind, simulateQ_pure, map_eq_bind_pure_comp]
    rw [hC, hB]
    refine AuthL11.LeComp.pure (Or.inr ⟨rfl, ⟨?_, fun Q => hS.epoch_le_qep Q, fun hlt => ?_, hS.lc_ge_tH⟩⟩)
    · simpa [toEStateP, hstC, hstB, c, rcd] using
        hsync.record_same_epoch P none m_msg default hsend0
    · obtain ⟨hpl, hcr⟩ := hS.pre_tH (by simpa [SM.GameState.record] using hlt)
      exact ⟨by rw [postLeak_record]; exact hpl, hcr⟩
  | some v =>
    let h : Header T := (esC.g.epoch P, (esC.g.st P).curCkaMsg)
    let fe := fs.send v h m_msg
    let c : Header T × E := (h, fe.2)
    let rcd : SM.Record M (Header T × E) := ⟨⟨P, esC.g.epoch P, esC.g.idx P + 1⟩, m_msg, c⟩
    have hC : ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
        ((transmitEBucket (hooksCKABucket cka prng fs Δcka tL par)
          (2 + Δcka) qep (P, m_msg, r)).run esC)).run sc) =
        pure ((some c,
          { esC with g := esC.g.record (2 + Δcka) P { esC.g.st P with vS := some fe.1 } rcd false }), sc) := by
      simp [-Prod.mk.injEq, transmitEBucket, vSend, hooksCKABucket_fsSend, FSAEADScheme.send,
        SM.GameState.epMgmt, habC, hwin0, hsend, hqep, hidC, htcurC, hvS, h, fe, c, rcd,
        AuthL11.run_liftH, StateT.run_bind, StateT.run_get, StateT.run_modify, StateT.run_pure,
        simulateQ_bind, simulateQ_pure, map_eq_bind_pure_comp]
    have hB : ((simulateQ (AuthL10.pImpl prng)
        ((transmitEBucket (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
          (2 + Δcka) qep (P, m_msg, r)).run esB)).run sp) =
        pure ((some c,
          { esB with g := esB.g.record (2 + Δcka) P { esB.g.st P with vS := some fe.1 } rcd false }), sp) := by
      simp [-Prod.mk.injEq, transmitEBucket, vSend, hooksPRNGBucketHybrid_fsSend, FSAEADScheme.send,
        SM.GameState.epMgmt, habB, hwin, hwin0, hepP, hidxP, hsend, hqep, hidB, htcurB, hvSB, hvS,
        hTcurB, h, fe, c, rcd, AuthL11.run_liftH, StateT.run_bind, StateT.run_get, StateT.run_modify,
        StateT.run_pure, simulateQ_bind, simulateQ_pure, map_eq_bind_pure_comp]
    rw [hC, hB]
    refine AuthL11.LeComp.pure (Or.inr ⟨rfl, ⟨?_, fun Q => hS.epoch_le_qep Q, fun hlt => ?_, hS.lc_ge_tH⟩⟩)
    · simpa [toEStateP] using hsync.record_same_epoch P (some fe.1) m_msg fe.2 hsend0
    · obtain ⟨hpl, hcr⟩ := hS.pre_tH (by simpa [SM.GameState.record] using hlt)
      exact ⟨by rw [postLeak_record]; exact hpl, hcr⟩

private def postSendRawC
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ)
    (P : Party) (m_msg : M) (bad : Bool)
    (esC : AuthL10.EStateC Γ T Sig SS RS M E I)
    (res : Option (Option Γ × T × Sig × SS) × CKAState T I) :
    Option (Header T × E) × AuthL10.EStateC Γ T Sig SS RS M E I :=
  match res.1 with
  | none => (none, { esC with h := res.2, abort := true })
  | some (γ', Tm, σ', ss) =>
    let m := esC.g.epoch P + 1
    let h : Header T := (m, some Tm)
    let fe := fs.send ss h m_msg
    let stC' : VP (Option Γ) T Sig SS RS :=
      { esC.g.st P with tcur := m, γ := γ', curCkaMsg := some Tm, root := σ', vS := some fe.1 }
    let gC₁ := AuthL10.epMgmtNew esC.g (2 + Δcka) P bad
    let rcd : SM.Record M (Header T × E) := ⟨⟨P, m, 1⟩, m_msg, (h, fe.2)⟩
    (some (h, fe.2), { esC with g := gC₁.record (2 + Δcka) P stC' rcd false, h := res.2 })

private def postSendRawB
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ)
    (P : Party) (m_msg : M) (bad : Bool)
    (esB : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I))
    (res : Option (Γ × T × Option Sig × SS) × PRNGBucketState T Sig K I) :
    Option (Header T × E) ×
      EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) :=
  match res.1 with
  | none => (none, { esB with h := res.2, abort := true })
  | some (γ', Tm, σ', ss) =>
    let m := esB.g.epoch P + 1
    let h : Header T := (m, some Tm)
    let fe := fs.send ss h m_msg
    let stB' : VP Γ T (Option Sig) SS RS :=
      { esB.g.st P with tcur := m, γ := γ', curCkaMsg := some Tm, root := σ', vS := some fe.1 }
    let gB₁ := AuthL10.epMgmtNew esB.g (2 + Δcka) P bad
    let rcd : SM.Record M (Header T × E) := ⟨⟨P, m, 1⟩, m_msg, (h, fe.2)⟩
    (some (h, fe.2), { esB with g := gB₁.record (2 + Δcka) P stB' rcd false, h := res.2 })

private theorem stepC_transmitEBucket_new
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (P : Party) (m_msg : M) (r : Option CCoins)
    (esC : AuthL10.EStateC Γ T Sig SS RS M E I) (sc : CKA.GameState Γ T)
    (hab : esC.abort = false) (hwin : esC.g.win = false)
    (hid : (esC.g.st P).id = P) (htcur : (esC.g.st P).tcur = esC.g.epoch P)
    (hsend : P.sendsIn (esC.g.epoch P + 1) = true)
    (hqep : ¬ qep < esC.g.epoch P + 1) :
    ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
      ((transmitEBucket (hooksCKABucket cka prng fs Δcka tL par)
        (2 + Δcka) qep (P, m_msg, r)).run esC)).run sc) =
      ((simulateQ (AuthL10.cImpl cka Δcka (moBase tL).tH)
        (((hooksCKA cka prng fs Δcka (moBase tL)).startSend
          (AuthL10.epMgmtNew esC.g (2 + Δcka) P r.isSome)
          P (esC.g.epoch P + 1) (esC.g.st P).γ (esC.g.st P).root r).run esC.h)).run sc) >>=
        fun out => pure (postSendRawC fs Δcka P m_msg r.isSome esC out.1, out.2) := by
  have hep := AuthL10.epMgmt_eq_epMgmtNew esC.g (2 + Δcka) qep P r.isSome hsend hqep
  simp only [transmitEBucket, hab, hwin, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hep,
    vSend, hooksCKABucket_startSend, hooksCKABucket_fsSend, AuthL10.epMgmtNew_st, hid, htcur, hsend,
    moBase_tH, AuthL11.run_liftH, StateT.run_bind, StateT.run_get,
    pure_bind, bind_assoc, simulateQ_bind, map_eq_bind_pure_comp]
  congr 1
  funext out
  rcases out with ⟨⟨ans, h'⟩, sc'⟩
  cases ans with
  | none =>
    simp [postSendRawC, abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure,
      pure_bind, simulateQ_pure]
  | some val =>
    rcases val with ⟨γ', Tm, σ', ss⟩
    simp [postSendRawC, FSAEADScheme.send, hid, hab, AuthL10.epMgmtNew_st, htcur,
      StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, simulateQ_pure]

private theorem stepB_transmitEBucket_new
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (P : Party) (m_msg : M) (r : Option CCoins)
    (esB : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I))
    (sp : PRFPRNG.GameState Sig I K)
    (hab : esB.abort = false) (hwin : esB.g.win = false)
    (hid : (esB.g.st P).id = P) (htcur : (esB.g.st P).tcur = esB.g.epoch P)
    (hsend : P.sendsIn (esB.g.epoch P + 1) = true)
    (hqep : ¬ qep < esB.g.epoch P + 1) :
    ((simulateQ (AuthL10.pImpl prng)
      ((transmitEBucket (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
        (2 + Δcka) qep (P, m_msg, r)).run esB)).run sp) =
      ((simulateQ (AuthL10.pImpl prng)
        (((hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL)).startSend
          (AuthL10.epMgmtNew esB.g (2 + Δcka) P r.isSome)
          P (esB.g.epoch P + 1) (esB.g.st P).γ (esB.g.st P).root r).run esB.h)).run sp) >>=
        fun out => pure (postSendRawB fs Δcka P m_msg r.isSome esB out.1, out.2) := by
  have hep := AuthL10.epMgmt_eq_epMgmtNew esB.g (2 + Δcka) qep P r.isSome hsend hqep
  simp only [transmitEBucket, hab, hwin, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hep,
    vSend, hooksPRNGBucketHybrid_fsSend, AuthL10.epMgmtNew_st, hid, htcur, hsend,
    AuthL11.run_liftH, StateT.run_bind, StateT.run_get,
    pure_bind, bind_assoc, simulateQ_bind, map_eq_bind_pure_comp]
  congr 1
  funext out
  rcases out with ⟨⟨ans, h'⟩, sp'⟩
  cases ans with
  | none =>
    simp [postSendRawB, abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure,
      pure_bind, simulateQ_pure]
  | some val =>
    rcases val with ⟨γ', Tm, σ', ss⟩
    simp [postSendRawB, FSAEADScheme.send, hid, hab, AuthL10.epMgmtNew_st, htcur,
      StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, simulateQ_pure]

private def startSendBBucket_body [DecidableEq I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δbucket : ℕ) (tL : Option ℕ) (par : Bool) (t m : ℕ) (pl : Bool)
    (γ : Γ) (σv : Option Sig) (coins : CCoins) :
    HM (PRFPRNG.spec Sig I K) (PRNGBucketState T Sig K I)
      (Option (Γ × T × Option Sig × SS)) := do
  let c := cka.send γ coins
  match ← rootPRNGBucketHybrid prng Δbucket tL par t m pl c.2.2 σv with
  | none => return none
  | some (σ', kVal) =>
    modify fun s => { s with cache := Function.update s.cache m (some (c.2.1, σ', kVal)) }
    return some (c.1, c.2.1, σ', fs.initSender kVal)

private def preLcSend (tL : Option ℕ) (m : ℕ) (pl : Bool)
    (h : PRNGBucketState T Sig K I) : PRNGBucketState T Sig K I :=
  if pl && h.lc.isNone && decide (healEpoch tL < m) then
    { h with lc := some (m - 1) }
  else h

@[local simp]
private theorem preLcSend_cache (tL : Option ℕ) (m : ℕ) (pl : Bool)
    (h : PRNGBucketState T Sig K I) :
    (preLcSend tL m pl h).cache = h.cache := by
  unfold preLcSend; split_ifs <;> rfl

@[local simp]
private theorem preLcSend_corrRoot (tL : Option ℕ) (m : ℕ) (pl : Bool)
    (h : PRNGBucketState T Sig K I) :
    (preLcSend tL m pl h).corrRoot = h.corrRoot := by
  unfold preLcSend; split_ifs <;> rfl

private theorem preLcSend_lc_ge_tH {tL : Option ℕ} {m : ℕ} {pl : Bool}
    {h : PRNGBucketState T Sig K I}
    (hlc : ∀ e, h.lc = some e → healEpoch tL ≤ e) :
    ∀ e, (preLcSend tL m pl h).lc = some e → healEpoch tL ≤ e := by
  intro e he
  unfold preLcSend at he
  split_ifs at he with hc
  · simp only [Option.some.injEq] at he
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    omega
  · exact hlc e he

private theorem startSendBBucket_some_eq [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party) (m : ℕ) (γ : Γ) (σv : Option Sig)
    (coins : CCoins) (h : PRNGBucketState T Sig K I) :
    (((hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t).startSend ctx P m γ σv (some coins)).run h) =
      (startSendBBucket_body cka prng fs (3 + Δcka) tL par t m (postLeak tL ctx) γ σv coins).run
        (preLcSend tL m (postLeak tL ctx) h) := by
  simp only [hooksPRNGBucketHybrid, hooksPRNGBucketHybridGen, startSendBBucket_body, preLcSend,
    StateT.run_bind, StateT.run_get, StateT.run_modify, StateT.run_pure, pure_bind]
  split_ifs <;> rfl

private theorem startSendBBucket_none_eq [DecidableEq T] [DecidableEq I]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party) (m : ℕ) (γ : Γ) (σv : Option Sig)
    (h : PRNGBucketState T Sig K I) (sp : PRFPRNG.GameState Sig I K) :
    (simulateQ (AuthL10.pImpl prng)
      (((hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t).startSend ctx P m γ σv none).run h)).run sp =
      ($ᵗ CCoins : ProbComp CCoins) >>= fun coins =>
        (simulateQ (AuthL10.pImpl prng)
          ((startSendBBucket_body cka prng fs (3 + Δcka) tL par t m (postLeak tL ctx) γ σv coins).run
            (preLcSend tL m (postLeak tL ctx) h))).run sp := by
  have hpre : (((hooksPRNGBucketHybrid cka prng fs Δcka qep tL par t).startSend ctx P m γ σv none).run h) =
      ((StateT.lift (sampleT CCoins) >>= fun coins =>
        startSendBBucket_body cka prng fs (3 + Δcka) tL par t m (postLeak tL ctx) γ σv coins).run
          (preLcSend tL m (postLeak tL ctx) h)) := by
    simp only [hooksPRNGBucketHybrid, hooksPRNGBucketHybridGen, startSendBBucket_body, preLcSend,
      StateT.run_bind, StateT.run_get, StateT.run_modify, StateT.run_pure, pure_bind]
    split_ifs <;> rfl
  rw [hpre]
  simp [StateT.run_lift, StateT.run_bind, simulateQ_bind, AuthL10.simulateQ_sampleT_pImpl,
    map_eq_bind_pure_comp, bind_assoc]

private theorem stepRelBase_postSendRaw_new
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (P : Party) (m_msg : M) (bad : Bool)
    {esC : AuthL10.EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esB : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : SyncBaseRaw prng Δcka qep tL esC sc esB sp)
    (hB0 : PRNGBucketState T Sig K I)
    (hB0_cache : hB0.cache = esB.h.cache)
    (hB0_cr : hB0.corrRoot = esB.h.corrRoot)
    (hB0_lc : ∀ e, hB0.lc = some e → healEpoch tL ≤ e)
    (γP' : Γ) (Tm : T) (Im : I)
    (sc' : CKA.GameState Γ T) (sp' : PRFPRNG.GameState Sig I K)
    (hsend : P.sendsIn (esC.g.epoch P + 1) = true)
    (hqep_m : esC.g.epoch P + 1 ≤ qep)
    (hb_sc' : sc'.b = true) (hb_sp' : sp'.b = false)
    (hcka' : AuthL10.localCKA (moBase tL) Δcka (esC.g.epoch P) = false →
      sc'.st P = γP' ∧ sc'.epoch P = esC.g.epoch P + 1 ∧
      sc'.st P.other = (esB.g.st P.other).γ ∧ sc'.epoch P.other = esC.g.epoch P ∧
      sc'.lastMsg = some Tm)
    (hprng_before : esC.g.epoch P + 1 < healEpoch tL →
      sp'.σ = (prng.up (esC.g.st P).root Im).1 ∧
      sp'.corr = true ∧ sp'.prng = false ∧ sp'.prf = false)
    (hpre' : esC.g.epoch P + 1 < healEpoch tL →
      postLeak tL (AuthL10.epMgmtNew esC.g (2 + Δcka) P bad) = false ∧ esB.h.corrRoot = none) :
    let m := esC.g.epoch P + 1
    let p := prng.up (esC.g.st P).root Im
    let resC : Option (Option Γ × T × Sig × SS) × CKAState T I :=
      (some (if AuthL10.localCKA (moBase tL) Δcka m then some γP' else none,
        Tm, p.1, fs.initSender p.2),
        { cache := Function.update esC.h.cache m (some (Tm, Im)) })
    let resB : Option (Γ × T × Option Sig × SS) × PRNGBucketState T Sig K I :=
      (some (γP', Tm, some p.1, fs.initSender p.2),
        { hB0 with cache := Function.update hB0.cache m (some (Tm, some p.1, p.2)) })
    StepRelBase prng Δcka qep tL
      (postSendRawC fs Δcka P m_msg bad esC resC, sc')
      (postSendRawB fs Δcka P m_msg bad esB resB, sp') := by
  intro m p resC resB
  have hsync := hS.sync
  have hepP : esB.g.epoch P = esC.g.epoch P := congrFun (AuthL10.eraseSt_epoch hsync.g_eq) P
  obtain ⟨hO_ep, _, _⟩ := hsync.ping_pong_synced P hsend
  let fe := fs.send (fs.initSender p.2) (m, some Tm) m_msg
  have hsync' := hsync.record_new_epoch P bad γP' Tm Im fe.1 m_msg fe.2 sc' sp' hsend hb_sc' hb_sp'
    hcka'
    (fun hlt _ => hprng_before (by simpa [moBase_tStar] using hlt))
    (fun hlt hfalse => by
      have hlt' : esC.g.epoch P + 1 < healEpoch tL := by simpa [moBase_tStar] using hlt
      cases tL with
      | none => simp at hlt'
      | some l => simp [moBase_tL, moBase_tH] at hlt' hfalse; omega)
    (fun heq hfalse => by
      have heq' : esC.g.epoch P + 1 = healEpoch tL := by simpa [moBase_tStar] using heq
      cases tL with
      | none => simp at heq'
      | some l => simp [moBase_tL, moBase_tStar, moBase_tH] at hfalse)
  have hkr : (if AuthL10.knownRoot (moBase tL) m then some p.1 else none) = some p.1 := by
    simp [knownRoot_moBase]
  dsimp only [resC, resB, postSendRawC, postSendRawB]
  simp only [hepP, m]
  refine Or.inr ⟨rfl, ⟨?_, fun Q => ?_, fun hlt => ?_, hB0_lc⟩⟩
  · simpa [toEStateP, hB0_cache, hkr, m, p, fe] using hsync'
  · dsimp only [SM.GameState.record]
    rw [AuthL10.epMgmtNew_epoch]
    rcases AuthL10.party_eq_or_eq_other Q P with hQ | hQ
    · rw [hQ]; simp [m, hqep_m]
    · rw [hQ]; simp [Party.other_ne, hS.epoch_le_qep P.other]
  · dsimp only [SM.GameState.record] at hlt
    rw [AuthL10.epMgmtNew_epoch, AuthL10.max_epoch_update_succ hO_ep] at hlt
    obtain ⟨hpl', hcr'⟩ := hpre' hlt
    exact ⟨by simpa [postLeak_record] using hpl', hB0_cr.trans hcr'⟩

private theorem leComp_startSendBBucket_coins
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (P : Party) (m_msg : M) (bad : Bool)
    {esC : AuthL10.EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esB : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : SyncBaseRaw prng Δcka qep tL esC sc esB sp)
    (coins : CCoins) (sc' : CKA.GameState Γ T)
    (hsend : P.sendsIn (esC.g.epoch P + 1) = true)
    (hqep_m : esC.g.epoch P + 1 ≤ qep)
    (hnot_tH : (tL.isSome && decide (esC.g.epoch P + 1 = healEpoch tL)) = false)
    (hbad : esC.g.epoch P + 1 < healEpoch tL → bad = false ∨ esC.g.epoch P + 1 + 2 ≤ healEpoch tL)
    (hb_sc' : sc'.b = true)
    (hcka' : AuthL10.localCKA (moBase tL) Δcka (esC.g.epoch P) = false →
      sc'.st P = (cka.send (esB.g.st P).γ coins).1 ∧ sc'.epoch P = esC.g.epoch P + 1 ∧
      sc'.st P.other = (esB.g.st P.other).γ ∧ sc'.epoch P.other = esC.g.epoch P ∧
      sc'.lastMsg = some (cka.send (esB.g.st P).γ coins).2.1) :
    let m := esC.g.epoch P + 1
    let c_cka := cka.send (esB.g.st P).γ coins
    let p := prng.up (esC.g.st P).root c_cka.2.2
    let resC : Option (Option Γ × T × Sig × SS) × CKAState T I :=
      (some (if AuthL10.localCKA (moBase tL) Δcka m then some c_cka.1 else none,
        c_cka.2.1, p.1, fs.initSender p.2),
        { cache := Function.update esC.h.cache m (some (c_cka.2.1, c_cka.2.2)) })
    let pl := postLeak tL (AuthL10.epMgmtNew esB.g (2 + Δcka) P bad)
    AuthL11.LeComp (StepRelBase prng Δcka qep tL)
      (pure (postSendRawC fs Δcka P m_msg bad esC resC, sc'))
      ((simulateQ (AuthL10.pImpl prng)
          ((startSendBBucket_body cka prng fs (3 + Δcka) tL par (healEpoch tL) m pl
            (esB.g.st P).γ (esB.g.st P).root coins).run (preLcSend tL m pl esB.h))).run sp >>=
        fun out => pure (postSendRawB fs Δcka P m_msg bad esB out.1, out.2)) := by
  intro m c_cka p resC pl
  let hB0 := preLcSend tL m pl esB.h
  have hB0_cache : hB0.cache = esB.h.cache := preLcSend_cache tL m pl esB.h
  have hB0_cr : hB0.corrRoot = esB.h.corrRoot := preLcSend_corrRoot tL m pl esB.h
  have hB0_lc : ∀ e, hB0.lc = some e → healEpoch tL ≤ e := preLcSend_lc_ge_tH hS.lc_ge_tH
  have hsync := hS.sync
  obtain ⟨hO_ep, hmax0, hroot0⟩ := hsync.ping_pong_synced P hsend
  have hroot_max : (esC.g.st (Party.senderOf (max (esC.g.epoch .A) (esC.g.epoch .B)))).root =
      (esC.g.st P).root := by
    rcases AuthL10.party_eq_or_eq_other
        (Party.senderOf (max (esC.g.epoch .A) (esC.g.epoch .B))) P with hEq | hEq
    · rw [hEq]
    · rw [hEq, hroot0]
  have hrootB0 : (esB.g.st P).root = some (esC.g.st P).root := root_P_moBase hsync P
  by_cases hgt : healEpoch tL < m
  · let resB : Option (Γ × T × Option Sig × SS) × PRNGBucketState T Sig K I :=
      (some (c_cka.1, c_cka.2.1, some p.1, fs.initSender p.2),
        { hB0 with cache := Function.update hB0.cache m (some (c_cka.2.1, some p.1, p.2)) })
    have hB : (simulateQ (AuthL10.pImpl prng)
        ((startSendBBucket_body cka prng fs (3 + Δcka) tL par (healEpoch tL) m pl
          (esB.g.st P).γ (esB.g.st P).root coins).run hB0)).run sp =
        pure (resB, sp) := by
      simp only [startSendBBucket_body, rootPRNGBucketHybrid, resolveCorrRoot,
        hgt, ↓reduceIte, hrootB0, c_cka, p, resB, StateT.run_bind, StateT.run_get, StateT.run_pure,
        StateT.run_modify, pure_bind, simulateQ_pure]
    change AuthL11.LeComp _ _
      ((simulateQ (AuthL10.pImpl prng)
        ((startSendBBucket_body cka prng fs (3 + Δcka) tL par (healEpoch tL) m pl
          (esB.g.st P).γ (esB.g.st P).root coins).run hB0)).run sp >>= _)
    rw [hB, pure_bind]
    exact AuthL11.LeComp.pure (stepRelBase_postSendRaw_new prng fs Δcka qep tL P m_msg bad hS
      hB0 hB0_cache hB0_cr hB0_lc
      c_cka.1 c_cka.2.1 c_cka.2.2 sc' sp hsend hqep_m hb_sc' hsync.b_P hcka'
      (fun h => by omega) (fun h => by omega))
  · have hne_tH : m ≠ healEpoch tL := by
      intro heq
      cases htL : tL with
      | none => rw [htL, healEpoch_none_eq] at heq; omega
      | some l => simp [htL, m, heq] at hnot_tH
    have hlt : m < healEpoch tL := by omega
    have hmax_lt : max (esC.g.epoch .A) (esC.g.epoch .B) < healEpoch tL := by omega
    obtain ⟨hpl0, hcr0⟩ := hS.pre_tH hmax_lt
    have hplC : postLeak tL (AuthL10.epMgmtNew esC.g (2 + Δcka) P bad) = false :=
      postLeak_epMgmtNew_false (2 + Δcka) P bad hpl0 (hbad hlt)
    have hpl_eq : pl = false := by
      dsimp only [pl]
      have htL_eq : (AuthL10.epMgmtNew esB.g (2 + Δcka) P bad).tL =
          (AuthL10.epMgmtNew esC.g (2 + Δcka) P bad).tL :=
        AuthL10.eraseSt_tL (AuthL10.eraseSt_epMgmtNew hsync.g_eq (2 + Δcka) P bad)
      simpa [postLeak, htL_eq] using hplC
    have htL_some : tL.isSome = true := by
      cases tL with
      | none => simp at hlt
      | some _ => rfl
    have hlt_tH0 : ((moBase tL).tL.isSome && decide (max (esC.g.epoch .A) (esC.g.epoch .B) < (moBase tL).tH)) = true := by
      simp [moBase_tL, moBase_tH, htL_some, hmax_lt]
    obtain ⟨hσ, hcorr, hprng, hprf⟩ := hsync.prng_before_tH (by simpa [moBase] using hmax_lt) hlt_tH0
    rw [hroot_max] at hσ
    let resB : Option (Γ × T × Option Sig × SS) × PRNGBucketState T Sig K I :=
      (some (c_cka.1, c_cka.2.1, some p.1, fs.initSender p.2),
        { hB0 with cache := Function.update hB0.cache m (some (c_cka.2.1, some p.1, p.2)) })
    let sp' : PRFPRNG.GameState Sig I K := { sp with σ := p.1, corr := true }
    have hcrB0 : hB0.corrRoot = none := hB0_cr.trans hcr0
    have hB : (simulateQ (AuthL10.pImpl prng)
        ((startSendBBucket_body cka prng fs (3 + Δcka) tL par (healEpoch tL) m pl
          (esB.g.st P).γ (esB.g.st P).root coins).run hB0)).run sp =
        pure (resB, sp') := by
      simp [startSendBBucket_body, rootPRNGBucketHybrid, resolveCorrRoot,
        hgt, hne_tH, hlt, hpl_eq, hcrB0, hrootB0,
        liftPBucket, PRFPRNG.processQuery, PRFPRNG.corrQuery, AuthL10.pImpl, PRFPRNG.oracleImpl,
        PRFPRNG.processImpl, PRFPRNG.corrImpl, PRFPRNG.samIfNec,
        hsync.b_P, hcorr, hprng, hprf, hσ, c_cka, p, resB, sp',
        StateT.lift, simulateQ_bind, simulateQ_query, simulateQ_pure,
        map_eq_bind_pure_comp, StateT.run_bind, StateT.run_get, StateT.run_pure, StateT.run_modify]
    change AuthL11.LeComp _ _
      ((simulateQ (AuthL10.pImpl prng)
        ((startSendBBucket_body cka prng fs (3 + Δcka) tL par (healEpoch tL) m pl
          (esB.g.st P).γ (esB.g.st P).root coins).run hB0)).run sp >>= _)
    rw [hB, pure_bind]
    exact AuthL11.LeComp.pure (stepRelBase_postSendRaw_new prng fs Δcka qep tL P m_msg bad hS
      hB0 hB0_cache hB0_cr hB0_lc
      c_cka.1 c_cka.2.1 c_cka.2.2 sc' sp' hsend hqep_m hb_sc' hsync.b_P hcka'
      (fun _ => ⟨rfl, rfl, hprng, hprf⟩) (fun _ => ⟨hplC, hcr0⟩))

private theorem leComp_startSendBBucket_chall
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (P : Party) (m_msg : M)
    {esC : AuthL10.EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esB : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : SyncBaseRaw prng Δcka qep tL esC sc esB sp)
    (coins : CCoins) (sc' : CKA.GameState Γ T)
    (hsend : P.sendsIn (esC.g.epoch P + 1) = true)
    (hqep_m : esC.g.epoch P + 1 ≤ qep)
    (htH : (tL.isSome && decide (esC.g.epoch P + 1 = healEpoch tL)) = true)
    (hb_sc' : sc'.b = true)
    (hcka' : AuthL10.localCKA (moBase tL) Δcka (esC.g.epoch P) = false →
      sc'.st P = (cka.send (esB.g.st P).γ coins).1 ∧ sc'.epoch P = esC.g.epoch P + 1 ∧
      sc'.st P.other = (esB.g.st P.other).γ ∧ sc'.epoch P.other = esC.g.epoch P ∧
      sc'.lastMsg = some (cka.send (esB.g.st P).γ coins).2.1) :
    let m := esC.g.epoch P + 1
    let c_cka := cka.send (esB.g.st P).γ coins
    let pl := postLeak tL (AuthL10.epMgmtNew esB.g (2 + Δcka) P false)
    AuthL11.LeComp (StepRelBase prng Δcka qep tL)
      (($ᵗ I : ProbComp I) >>= fun I₁ =>
        let p := prng.up (esC.g.st P).root I₁
        let resC : Option (Option Γ × T × Sig × SS) × CKAState T I :=
          (some (if AuthL10.localCKA (moBase tL) Δcka m then some c_cka.1 else none,
            c_cka.2.1, p.1, fs.initSender p.2),
            { cache := Function.update esC.h.cache m (some (c_cka.2.1, I₁)) })
        pure (postSendRawC fs Δcka P m_msg false esC resC, sc'))
      ((simulateQ (AuthL10.pImpl prng)
          ((startSendBBucket_body cka prng fs (3 + Δcka) tL par (healEpoch tL) m pl
            (esB.g.st P).γ (esB.g.st P).root coins).run (preLcSend tL m pl esB.h))).run sp >>=
        fun out => pure (postSendRawB fs Δcka P m_msg false esB out.1, out.2)) := by
  intro m c_cka pl
  let hB0 := preLcSend tL m pl esB.h
  have hB0_cache : hB0.cache = esB.h.cache := preLcSend_cache tL m pl esB.h
  have hB0_cr : hB0.corrRoot = esB.h.corrRoot := preLcSend_corrRoot tL m pl esB.h
  have hB0_lc : ∀ e, hB0.lc = some e → healEpoch tL ≤ e := preLcSend_lc_ge_tH hS.lc_ge_tH
  have hsync := hS.sync
  obtain ⟨hO_ep, hmax0, hroot0⟩ := hsync.ping_pong_synced P hsend
  have hroot_max : (esC.g.st (Party.senderOf (max (esC.g.epoch .A) (esC.g.epoch .B)))).root =
      (esC.g.st P).root := by
    rcases AuthL10.party_eq_or_eq_other
        (Party.senderOf (max (esC.g.epoch .A) (esC.g.epoch .B))) P with hEq | hEq
    · rw [hEq]
    · rw [hEq, hroot0]
  obtain ⟨htL_some, hm_tH⟩ : tL.isSome = true ∧ m = healEpoch tL := by
    simpa [m, Bool.and_eq_true, decide_eq_true_eq] using htH
  have hmax_lt : max (esC.g.epoch .A) (esC.g.epoch .B) < healEpoch tL := by omega
  obtain ⟨hpl0, hcr0⟩ := hS.pre_tH hmax_lt
  have hplC : postLeak tL (AuthL10.epMgmtNew esC.g (2 + Δcka) P false) = false :=
    postLeak_epMgmtNew_false (2 + Δcka) P false hpl0 (Or.inl rfl)
  have hpl_eq : pl = false := by
    dsimp only [pl]
    have htL_eq : (AuthL10.epMgmtNew esB.g (2 + Δcka) P false).tL =
        (AuthL10.epMgmtNew esC.g (2 + Δcka) P false).tL :=
      AuthL10.eraseSt_tL (AuthL10.eraseSt_epMgmtNew hsync.g_eq (2 + Δcka) P false)
    simpa [postLeak, htL_eq] using hplC
  have hlt_tH0 : ((moBase tL).tL.isSome && decide (max (esC.g.epoch .A) (esC.g.epoch .B) < (moBase tL).tH)) = true := by
    simp [moBase_tL, moBase_tH, htL_some, hmax_lt]
  obtain ⟨hσ, hcorr, hprng, hprf⟩ := hsync.prng_before_tH (by simpa [moBase] using hmax_lt) hlt_tH0
  rw [hroot_max] at hσ
  have hrootB0 : (esB.g.st P).root = some (esC.g.st P).root := root_P_moBase hsync P
  have hgt : ¬ (healEpoch tL < m) := by omega
  have hcrB0 : hB0.corrRoot = none := hB0_cr.trans hcr0
  have hB : (simulateQ (AuthL10.pImpl prng)
      ((startSendBBucket_body cka prng fs (3 + Δcka) tL par (healEpoch tL) m pl
        (esB.g.st P).γ (esB.g.st P).root coins).run hB0)).run sp =
      ($ᵗ I : ProbComp I) >>= fun I₁ =>
        let p := prng.up (esC.g.st P).root I₁
        pure ((some (c_cka.1, c_cka.2.1, some p.1, fs.initSender p.2),
          { hB0 with cache := Function.update hB0.cache m (some (c_cka.2.1, some p.1, p.2)) }),
          { sp with σ := p.1, corr := true, prng := true }) := by
    simp [startSendBBucket_body, rootPRNGBucketHybrid, resolveCorrRoot,
      hgt, hm_tH, htL_some, hpl_eq, hcrB0, hrootB0,
      liftPBucket, PRFPRNG.challPrngQuery, PRFPRNG.corrQuery, AuthL10.pImpl, PRFPRNG.oracleImpl,
      PRFPRNG.challPrngImpl, PRFPRNG.corrImpl, PRFPRNG.samIfNec, PRFPRNG.up,
      hcorr, hprng, hprf, hsync.b_P, hσ, c_cka,
      StateT.lift, simulateQ_bind, simulateQ_query, simulateQ_pure,
      map_eq_bind_pure_comp, StateT.run_bind, StateT.run_get, StateT.run_pure, StateT.run_modify,
      bind_assoc]
  change AuthL11.LeComp _ _
    ((simulateQ (AuthL10.pImpl prng)
      ((startSendBBucket_body cka prng fs (3 + Δcka) tL par (healEpoch tL) m pl
        (esB.g.st P).γ (esB.g.st P).root coins).run hB0)).run sp >>= _)
  rw [hB, bind_assoc]
  refine AuthL11.LeComp.sample_bind ($ᵗ I) fun I₁ _ => ?_
  rw [pure_bind]
  exact AuthL11.LeComp.pure (stepRelBase_postSendRaw_new prng fs Δcka qep tL P m_msg false hS
    hB0 hB0_cache hB0_cr hB0_lc
    c_cka.1 c_cka.2.1 I₁ sc'
    { sp with σ := (prng.up (esC.g.st P).root I₁).1, corr := true, prng := true }
    hsend hqep_m hb_sc' hsync.b_P hcka' (fun h => by omega) (fun h => by omega))

set_option maxHeartbeats 400000 in
private theorem leComp_transmitEBucket_new_base
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (P : Party) (m_msg : M) (r : Option CCoins)
    {esC : AuthL10.EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esB : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : SyncBaseRaw prng Δcka qep tL esC sc esB sp)
    (hwin0 : esC.g.win = false)
    (hsend : P.sendsIn (esC.g.epoch P + 1) = true) :
    AuthL11.LeComp (StepRelBase prng Δcka qep tL)
      ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
        ((transmitEBucket (hooksCKABucket cka prng fs Δcka tL par)
          (2 + Δcka) qep (P, m_msg, r)).run esC)).run sc)
      ((simulateQ (AuthL10.pImpl prng)
        ((transmitEBucket (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
          (2 + Δcka) qep (P, m_msg, r)).run esB)).run sp) := by
  have hsync := hS.sync
  have hwin : esB.g.win = esC.g.win := AuthL10.eraseSt_win hsync.g_eq
  have hepP : esB.g.epoch P = esC.g.epoch P := congrFun (AuthL10.eraseSt_epoch hsync.g_eq) P
  by_cases hqep : qep < esC.g.epoch P + 1
  · have hqep_le : qep ≤ esC.g.epoch P := by omega
    have hC : ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
        ((transmitEBucket (hooksCKABucket cka prng fs Δcka tL par)
          (2 + Δcka) qep (P, m_msg, r)).run esC)).run sc) = pure ((none, esC), sc) := by
      simp [-Prod.mk.injEq, transmitEBucket, SM.GameState.epMgmt, hsync.abort_C, hwin0,
        hsend, hqep_le, StateT.run_bind, StateT.run_get, StateT.run_pure, simulateQ_pure]
    have hB : ((simulateQ (AuthL10.pImpl prng)
        ((transmitEBucket (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
          (2 + Δcka) qep (P, m_msg, r)).run esB)).run sp) = pure ((none, esB), sp) := by
      simp [-Prod.mk.injEq, transmitEBucket, SM.GameState.epMgmt, hsync.abort_P, hwin, hwin0,
        hepP, hsend, hqep_le, StateT.run_bind, StateT.run_get, StateT.run_pure, simulateQ_pure]
    rw [hC, hB]
    exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hS⟩)
  · have hqep_m : esC.g.epoch P + 1 ≤ qep := Nat.not_lt.mp hqep
    rw [stepC_transmitEBucket_new cka prng fs Δcka qep tL par P m_msg r esC sc
        hsync.abort_C hwin0 (hsync.id_C P) (hsync.tcur_C P) hsend hqep,
      stepB_transmitEBucket_new cka prng fs Δcka qep tL par P m_msg r esB sp
        hsync.abort_P (hwin.trans hwin0) (hsync.id_P P) ((hsync.tcur_P P).trans hepP.symm)
        (by rw [hepP]; exact hsend) (by rw [hepP]; exact hqep)]
    let m := esC.g.epoch P + 1
    by_cases hloc : AuthL10.localCKA (moBase tL) Δcka (esC.g.epoch P)
    · have hloc_m : AuthL10.localCKA (moBase tL) Δcka m = true :=
        AuthL10.localCKA_mono (moBase tL) Δcka hloc (Nat.le_succ _)
      have hnot_tH : (tL.isSome && decide (esC.g.epoch P + 1 = healEpoch tL)) = false := by
        simp only [AuthL10.localCKA, moBase_tL, moBase_tH, Bool.or_eq_true, decide_eq_true_eq] at hloc
        rcases hloc with h | h
        · cases h' : tL <;> simp_all
        · simp [show esC.g.epoch P + 1 ≠ healEpoch tL by omega]
      have hnot_lt : ¬ (esC.g.epoch P + 1 < healEpoch tL) := by
        simp only [AuthL10.localCKA, moBase_tL, moBase_tH, Bool.or_eq_true, decide_eq_true_eq] at hloc
        rcases hloc with h | h
        · cases tL <;> simp at h ⊢
        · omega
      have hγC : (esC.g.st P).γ = some (esB.g.st P).γ := by
        simpa [toEStateP, hloc] using hsync.γ_C P
      cases r with
      | some coins =>
        let c_cka := cka.send (esB.g.st P).γ coins
        let p := prng.up (esC.g.st P).root c_cka.2.2
        let resC : Option (Option Γ × T × Sig × SS) × CKAState T I :=
          (some (if AuthL10.localCKA (moBase tL) Δcka m then some c_cka.1 else none,
            c_cka.2.1, p.1, fs.initSender p.2),
            { cache := Function.update esC.h.cache m (some (c_cka.2.1, c_cka.2.2)) })
        have hC : (simulateQ (AuthL10.cImpl cka Δcka (moBase tL).tH)
            (((hooksCKA cka prng fs Δcka (moBase tL)).startSend
              (AuthL10.epMgmtNew esC.g (2 + Δcka) P true)
              P (esC.g.epoch P + 1) (esC.g.st P).γ (esC.g.st P).root (some coins)).run esC.h)).run sc =
            pure (resC, sc) := by
          simp [hooksCKA, cacheC, hγC, hloc_m, m, c_cka, p, resC,
            StateT.run_bind, StateT.run_pure, StateT.run_modify, simulateQ_pure]
        simp only [Option.isSome_some]
        rw [hC, pure_bind, hepP, startSendBBucket_some_eq]
        exact leComp_startSendBBucket_coins cka prng fs Δcka qep tL par P m_msg true hS coins sc
          hsend hqep_m hnot_tH (fun h => absurd h hnot_lt) hsync.b_C (fun h => by simp [hloc] at h)
      | none =>
        have hC : (simulateQ (AuthL10.cImpl cka Δcka (moBase tL).tH)
            (((hooksCKA cka prng fs Δcka (moBase tL)).startSend
              (AuthL10.epMgmtNew esC.g (2 + Δcka) P false)
              P (esC.g.epoch P + 1) (esC.g.st P).γ (esC.g.st P).root none).run esC.h)).run sc =
            ($ᵗ CCoins : ProbComp CCoins) >>= fun coins =>
              let c_cka := cka.send (esB.g.st P).γ coins
              let p := prng.up (esC.g.st P).root c_cka.2.2
              pure ((some (if AuthL10.localCKA (moBase tL) Δcka m then some c_cka.1 else none,
                c_cka.2.1, p.1, fs.initSender p.2),
                { cache := Function.update esC.h.cache m (some (c_cka.2.1, c_cka.2.2)) }), sc) := by
          simp [hooksCKA, cacheC, hγC, hloc_m, m,
            StateT.lift, StateT.run_bind, StateT.run_pure, StateT.run_modify,
            simulateQ_bind, simulateQ_pure, map_eq_bind_pure_comp, bind_assoc]
        simp only [Option.isSome_none]
        rw [hC, hepP, startSendBBucket_none_eq, bind_assoc, bind_assoc]
        refine AuthL11.LeComp.sample_bind ($ᵗ CCoins) fun coins _ => ?_
        rw [pure_bind]
        exact leComp_startSendBBucket_coins cka prng fs Δcka qep tL par P m_msg false hS coins sc
          hsend hqep_m hnot_tH (fun _ => Or.inl rfl) hsync.b_C (fun h => by simp [hloc] at h)
    · simp only [Bool.not_eq_true] at hloc
      have hγC : (esC.g.st P).γ = none := by
        simpa [toEStateP, hloc] using hsync.γ_C P
      have htL_none : (moBase tL).tL.isNone = false := by
        simp only [AuthL10.localCKA, Bool.or_eq_false_iff] at hloc
        exact hloc.1
      have htL_some : tL.isSome = true := by
        cases h' : tL <;> simp_all [moBase]
      obtain ⟨hsc_stP, hsc_epP⟩ := hsync.cka_st P (Or.inl hloc)
      obtain ⟨hsc_stO, hsc_epO⟩ := hsync.cka_st P.other (Or.inr (by simpa using hloc))
      dsimp only [toEStateP] at hsc_stP hsc_stO
      obtain ⟨hO_ep, _, _⟩ := hsync.ping_pong_synced P hsend
      have hcanS : sc.canSend P = true := by
        simp [CKA.GameState.canSend, hsc_epP, hsc_epO, hO_ep, hsend]
      have htL_ne : tL ≠ none := Option.isSome_iff_ne_none.mp htL_some
      have htL_isNone : tL.isNone = false := by cases tL <;> simp_all
      cases r with
      | some coins =>
        by_cases hbad_ok : healEpoch tL < esC.g.epoch P + 1 + 2
        · have hC : (simulateQ (AuthL10.cImpl cka Δcka (moBase tL).tH)
              (((hooksCKA cka prng fs Δcka (moBase tL)).startSend
                (AuthL10.epMgmtNew esC.g (2 + Δcka) P true)
                P (esC.g.epoch P + 1) (esC.g.st P).γ (esC.g.st P).root (some coins)).run esC.h)).run sc =
              pure ((none, esC.h), sc) := by
            simp [hooksCKA, liftC, CKA.sendWithAdversaryCoinsQuery, AuthL10.cImpl,
              CKA.oracleImpl, CKA.sendWithAdversaryCoinsImpl, moBase_tH, hγC, hcanS, hsc_epP,
              hbad_ok, StateT.lift, simulateQ_bind, simulateQ_query, simulateQ_pure,
              map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure]
          simp only [Option.isSome_some]
          rw [hC, pure_bind]
          exact AuthL11.LeComp.pure_left _ _ fun _ _ => Or.inl rfl
        · have hnot_tH : (tL.isSome && decide (esC.g.epoch P + 1 = healEpoch tL)) = false := by
            simp [show esC.g.epoch P + 1 ≠ healEpoch tL by omega]
          have hfin : ¬ (healEpoch tL + Δcka ≤ m) := by omega
          have hloc_m : AuthL10.localCKA (moBase tL) Δcka m = false := by
            simp [AuthL10.localCKA, moBase_tH, htL_isNone]; omega
          let c_cka := cka.send (esB.g.st P).γ coins
          let p := prng.up (esC.g.st P).root c_cka.2.2
          let sc' := sc.afterSend P c_cka.1 c_cka.2.1
          let resC : Option (Option Γ × T × Sig × SS) × CKAState T I :=
            (some (if AuthL10.localCKA (moBase tL) Δcka m then some c_cka.1 else none,
              c_cka.2.1, p.1, fs.initSender p.2),
              { cache := Function.update esC.h.cache m (some (c_cka.2.1, c_cka.2.2)) })
          have hC : (simulateQ (AuthL10.cImpl cka Δcka (moBase tL).tH)
              (((hooksCKA cka prng fs Δcka (moBase tL)).startSend
                (AuthL10.epMgmtNew esC.g (2 + Δcka) P true)
                P (esC.g.epoch P + 1) (esC.g.st P).γ (esC.g.st P).root (some coins)).run esC.h)).run sc =
              pure (resC, sc') := by
            simp [hooksCKA, cacheC, liftC, CKA.sendWithAdversaryCoinsQuery, AuthL10.cImpl,
              CKA.oracleImpl, CKA.sendWithAdversaryCoinsImpl, moBase_tH, hγC, hcanS, hsc_epP,
              hsc_stP, hbad_ok, hfin, hloc_m, m, c_cka, p, sc', resC,
              StateT.lift, simulateQ_bind, simulateQ_query, simulateQ_pure,
              map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure, StateT.run_modify]
          simp only [Option.isSome_some]
          rw [hC, pure_bind, hepP, startSendBBucket_some_eq]
          refine leComp_startSendBBucket_coins cka prng fs Δcka qep tL par P m_msg true hS coins sc'
            hsend hqep_m hnot_tH (fun _ => Or.inr (by omega)) hsync.b_C fun _ => ?_
          simp [sc', c_cka, CKA.GameState.afterSend, Party.other_ne,
            hsc_epP, hsc_stO, hsc_epO, hO_ep]
      | none =>
        by_cases heq_tH : esC.g.epoch P + 1 = healEpoch tL
        · have htH : (tL.isSome && decide (esC.g.epoch P + 1 = healEpoch tL)) = true := by
            simpa [htL_some] using heq_tH
          have hC : (simulateQ (AuthL10.cImpl cka Δcka (moBase tL).tH)
              (((hooksCKA cka prng fs Δcka (moBase tL)).startSend
                (AuthL10.epMgmtNew esC.g (2 + Δcka) P false)
                P (esC.g.epoch P + 1) (esC.g.st P).γ (esC.g.st P).root none).run esC.h)).run sc =
              ($ᵗ CCoins : ProbComp CCoins) >>= fun coins => ($ᵗ I : ProbComp I) >>= fun I₁ =>
                let c_cka := cka.send (esB.g.st P).γ coins
                let p := prng.up (esC.g.st P).root I₁
                pure ((some (if AuthL10.localCKA (moBase tL) Δcka m then some c_cka.1 else none,
                  c_cka.2.1, p.1, fs.initSender p.2),
                  { cache := Function.update esC.h.cache m (some (c_cka.2.1, I₁)) }),
                  sc.afterSend P c_cka.1 c_cka.2.1) := by
            by_cases hΔ : Δcka = 0
            · simp [hooksCKA, cacheC, liftC, CKA.challQuery, CKA.corrQuery, AuthL10.cImpl,
                CKA.oracleImpl, CKA.challImpl, CKA.corrImpl, CKA.GameState.afterSend,
                CKA.GameState.finished, AuthL10.localCKA, moBase_tL, moBase_tH, htL_ne, htL_none,
                hγC, heq_tH, hcanS, hsc_epP, hsc_stP, hsync.b_C, hΔ, m,
                StateT.lift, simulateQ_bind, simulateQ_query, simulateQ_pure,
                map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure, StateT.run_modify, bind_assoc]
            · simp [hooksCKA, cacheC, liftC, CKA.challQuery, AuthL10.cImpl,
                CKA.oracleImpl, CKA.challImpl, AuthL10.localCKA, moBase_tL, moBase_tH, htL_ne,
                htL_none, hγC, heq_tH, hcanS, hsc_epP, hsc_stP, hsync.b_C, hΔ, m,
                StateT.lift, simulateQ_bind, simulateQ_query, simulateQ_pure,
                map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure, StateT.run_modify, bind_assoc]
          simp only [Option.isSome_none]
          rw [hC, hepP, startSendBBucket_none_eq, bind_assoc, bind_assoc]
          refine AuthL11.LeComp.sample_bind ($ᵗ CCoins) fun coins _ => ?_
          rw [bind_assoc]
          simpa [pure_bind] using leComp_startSendBBucket_chall cka prng fs Δcka qep tL par P m_msg hS coins
            (sc.afterSend P (cka.send (esB.g.st P).γ coins).1 (cka.send (esB.g.st P).γ coins).2.1)
            hsend hqep_m htH hsync.b_C (fun _ => by
              simp [CKA.GameState.afterSend, Party.other_ne, hsc_epP, hsc_stO, hsc_epO, hO_ep])
        · have hnot_tH : (tL.isSome && decide (esC.g.epoch P + 1 = healEpoch tL)) = false := by
            simp [heq_tH]
          have hC : (simulateQ (AuthL10.cImpl cka Δcka (moBase tL).tH)
              (((hooksCKA cka prng fs Δcka (moBase tL)).startSend
                (AuthL10.epMgmtNew esC.g (2 + Δcka) P false)
                P (esC.g.epoch P + 1) (esC.g.st P).γ (esC.g.st P).root none).run esC.h)).run sc =
              ($ᵗ CCoins : ProbComp CCoins) >>= fun coins =>
                let c_cka := cka.send (esB.g.st P).γ coins
                let p := prng.up (esC.g.st P).root c_cka.2.2
                pure ((some (if AuthL10.localCKA (moBase tL) Δcka m then some c_cka.1 else none,
                  c_cka.2.1, p.1, fs.initSender p.2),
                  { cache := Function.update esC.h.cache m (some (c_cka.2.1, c_cka.2.2)) }),
                  sc.afterSend P c_cka.1 c_cka.2.1) := by
            by_cases hfin : healEpoch tL + Δcka ≤ m
            · have hloc_m : AuthL10.localCKA (moBase tL) Δcka m = true := by
                simp [AuthL10.localCKA, moBase_tH, hfin]
              simp [hooksCKA, cacheC, liftC, CKA.sendQuery, CKA.corrQuery, AuthL10.cImpl,
                CKA.oracleImpl, CKA.sendImpl, CKA.corrImpl, CKA.GameState.afterSend,
                CKA.GameState.finished, moBase_tH, hγC, heq_tH, hcanS, hsc_epP, hsc_stP, hfin,
                hloc_m, m, StateT.lift, simulateQ_bind, simulateQ_query, simulateQ_pure,
                map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure, StateT.run_modify, bind_assoc]
            · have hloc_m : AuthL10.localCKA (moBase tL) Δcka m = false := by
                simp [AuthL10.localCKA, moBase_tH, htL_isNone]; omega
              simp [hooksCKA, cacheC, liftC, CKA.sendQuery, AuthL10.cImpl,
                CKA.oracleImpl, CKA.sendImpl, moBase_tH, hγC, heq_tH, hcanS, hsc_epP, hsc_stP,
                hfin, hloc_m, m, StateT.lift, simulateQ_bind, simulateQ_query, simulateQ_pure,
                map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure, StateT.run_modify, bind_assoc]
          simp only [Option.isSome_none]
          rw [hC, hepP, startSendBBucket_none_eq, bind_assoc, bind_assoc]
          refine AuthL11.LeComp.sample_bind ($ᵗ CCoins) fun coins _ => ?_
          rw [pure_bind]
          refine leComp_startSendBBucket_coins cka prng fs Δcka qep tL par P m_msg false hS coins
            (sc.afterSend P (cka.send (esB.g.st P).γ coins).1 (cka.send (esB.g.st P).γ coins).2.1)
            hsend hqep_m hnot_tH (fun _ => Or.inl rfl) hsync.b_C fun _ => ?_
          simp [CKA.GameState.afterSend, Party.other_ne, hsc_epP, hsc_stO, hsc_epO, hO_ep]

private theorem leComp_transmitEBucket_base
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (arg : Party × M × Option CCoins)
    {esC : AuthL10.EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esB : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : SyncBaseRaw prng Δcka qep tL esC sc esB sp) :
    AuthL11.LeComp (StepRelBase prng Δcka qep tL)
      ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
        ((transmitEBucket (hooksCKABucket cka prng fs Δcka tL par)
          (2 + Δcka) qep arg).run esC)).run sc)
      ((simulateQ (AuthL10.pImpl prng)
        ((transmitEBucket (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
          (2 + Δcka) qep arg).run esB)).run sp) := by
  rcases arg with ⟨P, m_msg, r⟩
  by_cases hwin0 : esC.g.win = true
  · have hwin : esB.g.win = esC.g.win := AuthL10.eraseSt_win hS.sync.g_eq
    have hC : ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
        ((transmitEBucket (hooksCKABucket cka prng fs Δcka tL par)
          (2 + Δcka) qep (P, m_msg, r)).run esC)).run sc) = pure ((none, esC), sc) := by
      simp [-Prod.mk.injEq, transmitEBucket, hS.sync.abort_C, hwin0,
        StateT.run_bind, StateT.run_get, StateT.run_pure, simulateQ_pure]
    have hB : ((simulateQ (AuthL10.pImpl prng)
        ((transmitEBucket (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
          (2 + Δcka) qep (P, m_msg, r)).run esB)).run sp) = pure ((none, esB), sp) := by
      simp [-Prod.mk.injEq, transmitEBucket, hS.sync.abort_P, hwin, hwin0,
        StateT.run_bind, StateT.run_get, StateT.run_pure, simulateQ_pure]
    rw [hC, hB]
    exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hS⟩)
  · simp only [Bool.not_eq_true] at hwin0
    by_cases hsend : P.sendsIn (esC.g.epoch P + 1) = true
    · exact leComp_transmitEBucket_new_base cka prng fs Δcka qep tL par P m_msg r hS hwin0 hsend
    · simp only [Bool.not_eq_true] at hsend
      exact leComp_transmitEBucket_same_base cka prng fs Δcka qep tL par P m_msg r hS hwin0 hsend

private def implEDFBucketRawChoiceBase {ι : Type} {tspec : OracleSpec.{0, 0} ι} {HS Γv Sv SSv RSv : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E] (paper : Bool)
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv) (Δ qep maxSkip : ℕ) (cfg : Config M) :
    QueryImpl (unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E))
      (EM tspec Γv T Sv SSv RSv M E HS) :=
  if paper then implEDFPaperBucketRaw hk Δ qep maxSkip cfg else implEDFBucketRaw hk Δ qep maxSkip cfg

private theorem leComp_implEDFBucketRawChoice_base (paper : Bool)
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (q : (AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    {esC : AuthL10.EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esB : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I)}
    {sp : PRFPRNG.GameState Sig I K}
    (hSB : SyncBaseRaw prng Δcka qep tL esC sc esB sp) :
    AuthL11.LeComp (StepRelBase prng Δcka qep tL)
      ((simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
        ((implEDFBucketRawChoiceBase paper (hooksCKABucket cka prng fs Δcka tL par)
          (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) q).run esC)).run sc)
      ((simulateQ (AuthL10.pImpl prng)
        ((implEDFBucketRawChoiceBase paper
          (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
          (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par) q).run esB)).run sp) := by
  rcases q with n | (((((arg | arg) | arg) | arg) | P) | df)
  · cases paper <;>
    · simp [implEDFBucketRawChoiceBase, implEDFPaperBucketRaw, implEDFBucketRaw,
        coinsE, AuthL10.cImpl, AuthL10.pImpl, StateT.run_lift, simulateQ_bind, simulateQ_query,
        map_eq_bind_pure_comp, bind_assoc]
      exact AuthL11.LeComp.sample_bind _ fun u _ => AuthL11.LeComp.pure (Or.inr ⟨rfl, hSB⟩)
  · cases paper <;>
    · simp only [implEDFBucketRawChoiceBase, ↓reduceIte, Bool.false_eq_true,
        implEDFPaperBucketRaw, implEDFBucketRaw, QueryImpl.add_apply]
      exact leComp_transmitEBucket_base cka prng fs Δcka qep tL par arg hSB
  · cases paper <;>
    · simp only [implEDFBucketRawChoiceBase, ↓reduceIte, Bool.false_eq_true,
        implEDFPaperBucketRaw, implEDFBucketRaw, QueryImpl.add_apply, challEBucket,
        StateT.run_pure, simulateQ_pure]
      exact AuthL11.LeComp.pure (Or.inr ⟨rfl, hSB⟩)
  · cases paper <;>
    · simp only [implEDFBucketRawChoiceBase, ↓reduceIte, Bool.false_eq_true,
        implEDFPaperBucketRaw, implEDFBucketRaw, QueryImpl.add_apply]
      exact leComp_deliverE_base_sync cka prng fs Δcka qep tL par arg hSB
  · cases paper <;>
    · simp only [implEDFBucketRawChoiceBase, ↓reduceIte, Bool.false_eq_true,
        implEDFPaperBucketRaw, implEDFBucketRaw, QueryImpl.add_apply]
      exact leComp_injectE_base_sync cka prng fs Δcka qep tL par arg hSB
  · have hcorr := leComp_corrChoice_base_sync cka prng fs Δcka qep tL par paper P hSB
    cases paper <;>
    · simp only [↓reduceIte, Bool.false_eq_true] at hcorr
      simpa [implEDFBucketRawChoiceBase, implEDFPaperBucketRaw, implEDFBucketRaw] using hcorr
  · cases paper <;>
    · simp only [implEDFBucketRawChoiceBase, ↓reduceIte, Bool.false_eq_true,
        implEDFPaperBucketRaw, implEDFBucketRaw, QueryImpl.add_apply]
      exact leComp_deliverForgeE_base_sync cka prng fs Δcka qep tL par df hSB

private def StepRelBucketBase (prng : PRFPRNG KR Sig I K) (Δcka qep : ℕ) (tL : Option ℕ) {α : Type}
    (x : (α × (AuthL10.EStateC Γ T Sig SS RS M E I × Option ℕ)) × CKA.GameState Γ T)
    (y : (α × (EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ)) ×
      PRFPRNG.GameState Sig I K) : Prop :=
  x.1.2.1.abort = true ∨
    (x.1.1 = y.1.1 ∧ x.1.2.2 = y.1.2.2 ∧ SyncBaseRaw prng Δcka qep tL x.1.2.1 x.2 y.1.2.1 y.2)

private def stepCBucketBase (paper : Bool)
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (q : (AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (stC : AuthL10.EStateC Γ T Sig SS RS M E I × Option ℕ) (sc : CKA.GameState Γ T) :
    ProbComp (((AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Range q ×
      (AuthL10.EStateC Γ T Sig SS RS M E I × Option ℕ)) × CKA.GameState Γ T) :=
  (simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
    ((withWinEpDF (fun c => c.1.1) (fun es => es.g.win)
      (implEDFBucketRawChoiceBase paper (hooksCKABucket cka prng fs Δcka tL par)
        (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par)) q).run stC)).run sc

private def stepBBucketBase (paper : Bool)
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (q : (AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (stB : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ)
    (sp : PRFPRNG.GameState Sig I K) :
    ProbComp (((AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Range q ×
      (EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ)) ×
      PRFPRNG.GameState Sig I K) :=
  (simulateQ (AuthL10.pImpl prng)
    ((withWinEpDF (fun c => c.1.1) (fun es => es.g.win)
      (implEDFBucketRawChoiceBase paper
        (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
        (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par)) q).run stB)).run sp

private theorem leComp_stepCBucketBase_stepBBucketBase (paper : Bool)
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (q : (AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    {stC : AuthL10.EStateC Γ T Sig SS RS M E I × Option ℕ} {sc : CKA.GameState Γ T}
    {stB : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ}
    {sp : PRFPRNG.GameState Sig I K}
    (hwinEp : stC.2 = stB.2) (hSB : SyncBaseRaw prng Δcka qep tL stC.1 sc stB.1 sp) :
    AuthL11.LeComp (StepRelBucketBase prng Δcka qep tL)
      (stepCBucketBase paper cka prng fs Δcka qep tL par q stC sc)
      (stepBBucketBase paper cka prng fs Δcka qep tL par q stB sp) := by
  rcases stC with ⟨esC, winEpC⟩; rcases stB with ⟨esB, winEpB⟩
  dsimp only at hwinEp hSB; subst hwinEp
  unfold stepCBucketBase stepBBucketBase withWinEpDF
  simp only [StateT.run_mk, simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure]
  refine (leComp_implEDFBucketRawChoice_base paper cka prng fs Δcka qep tL par q hSB).bind ?_
  rintro ⟨⟨uC, esC'⟩, sc'⟩ ⟨⟨uB, esB'⟩, sp'⟩ (hab | ⟨hu, hSB'⟩)
  · exact AuthL11.LeComp.pure (Or.inl hab)
  · dsimp only at hu hSB'; subst hu
    have hw0 : esB.g.win = esC.g.win := AuthL10.eraseSt_win hSB.sync.g_eq
    have hw1 : esB'.g.win = esC'.g.win := AuthL10.eraseSt_win hSB'.sync.g_eq
    dsimp only
    rw [hw0, hw1]
    exact AuthL11.LeComp.pure (Or.inr ⟨rfl, rfl, hSB'⟩)

private theorem stepCBucketBase_abort (paper : Bool)
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (q : (AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (stC : AuthL10.EStateC Γ T Sig SS RS M E I × Option ℕ) (sc : CKA.GameState Γ T)
    (hab : stC.1.abort = true) :
    ∀ r ∈ support (stepCBucketBase paper cka prng fs Δcka qep tL par q stC sc),
      r.1.2.1.abort = true := by
  intro r hr; rcases stC with ⟨esC, winEpC⟩; dsimp only at hab
  rcases q with n | (((((q | q) | q) | q) | P) | df)
  · cases paper <;>
    · simp [stepCBucketBase, withWinEpDF, implEDFBucketRawChoiceBase, implEDFPaperBucketRaw,
        implEDFBucketRaw, coinsE, AuthL10.cImpl, StateT.run_lift, simulateQ_bind, simulateQ_query,
        map_eq_bind_pure_comp, bind_assoc] at hr
      rcases hr with ⟨_, _, rfl⟩; exact hab
  · cases paper <;>
    · simp [stepCBucketBase, withWinEpDF, implEDFBucketRawChoiceBase, implEDFPaperBucketRaw,
        implEDFBucketRaw, transmitEBucket, hab] at hr
      rcases hr with rfl; exact hab
  · cases paper <;>
    · simp [stepCBucketBase, withWinEpDF, implEDFBucketRawChoiceBase, implEDFPaperBucketRaw,
        implEDFBucketRaw, challEBucket] at hr
      rcases hr with rfl; exact hab
  all_goals
    cases paper <;>
    · simp [stepCBucketBase, withWinEpDF, implEDFBucketRawChoiceBase, implEDFPaperBucketRaw,
        implEDFBucketRaw, deliverE, injectE, corrEPaperBucket, corrEBucket, deliverForgeE, hab] at hr
      rcases hr with rfl; exact hab

private def authOutBucketChoiceBase {VPt Msg C HS : Type} [DecidableEq Msg] [DecidableEq C]
    (paper : Bool) (Δ : ℕ) (tL : Option ℕ) (st : EState VPt Msg C HS × Option ℕ) : Bool :=
  if paper then authOutBucketPaper Δ tL st else authOutBucket Δ tL st

private def authOutBucketChoiceBaseB {VPt Msg C T' Sig' K' I' : Type}
    [DecidableEq Msg] [DecidableEq C]
    (paper : Bool) (Δ : ℕ) (tL : Option ℕ)
    (st : EState VPt Msg C (PRNGBucketState T' Sig' K' I') × Option ℕ) : Bool :=
  if paper then authOutBucketPaperAt Δ tL (healEpoch tL) st else authOutBucket Δ tL st

private def runCBucketBase (paper : Bool)
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (oa : AuthL11.SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (stC : AuthL10.EStateC Γ T Sig SS RS M E I × Option ℕ) (sc : CKA.GameState Γ T) : ProbComp Bool := do
  let r ← (simulateQ (AuthL10.cImpl cka Δcka (healEpoch tL))
    ((simulateQ (withWinEpDF (fun c => c.1.1) (fun es => es.g.win)
      (implEDFBucketRawChoiceBase paper (hooksCKABucket cka prng fs Δcka tL par)
        (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par))) oa).run stC)).run sc
  pure (authOutBucketChoiceBase paper (2 + Δcka) tL r.1.2)

private def runBBucketBase (paper : Bool)
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (oa : AuthL11.SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (stB : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ)
    (sp : PRFPRNG.GameState Sig I K) : ProbComp Bool := do
  let r ← (simulateQ (AuthL10.pImpl prng)
    ((simulateQ (withWinEpDF (fun c => c.1.1) (fun es => es.g.win)
      (implEDFBucketRawChoiceBase paper
        (hooksPRNGBucketHybrid cka prng fs Δcka qep tL par (healEpoch tL))
        (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par))) oa).run stB)).run sp
  pure (authOutBucketChoiceBaseB paper (2 + Δcka) tL r.1.2)

private theorem runCBucketBase_pure (paper : Bool)
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par b : Bool)
    (stC : AuthL10.EStateC Γ T Sig SS RS M E I × Option ℕ) (sc : CKA.GameState Γ T) :
    runCBucketBase paper cka prng fs Δcka qep tL par (pure b) stC sc =
      pure (authOutBucketChoiceBase paper (2 + Δcka) tL stC) := by simp [runCBucketBase]

private theorem runBBucketBase_pure (paper : Bool)
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par b : Bool)
    (stB : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ)
    (sp : PRFPRNG.GameState Sig I K) :
    runBBucketBase paper cka prng fs Δcka qep tL par (pure b) stB sp =
      pure (authOutBucketChoiceBaseB paper (2 + Δcka) tL stB) := by simp [runBBucketBase]

private theorem runCBucketBase_query_bind (paper : Bool)
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (q : (AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (k : (AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Range q →
      AuthL11.SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (stC : AuthL10.EStateC Γ T Sig SS RS M E I × Option ℕ) (sc : CKA.GameState Γ T) :
    runCBucketBase paper cka prng fs Δcka qep tL par (liftM (OracleSpec.query q) >>= k) stC sc =
      stepCBucketBase paper cka prng fs Δcka qep tL par q stC sc >>= fun r =>
        runCBucketBase paper cka prng fs Δcka qep tL par (k r.1.1) r.1.2 r.2 := by
  simp [runCBucketBase, stepCBucketBase, simulateQ_bind, StateT.run_bind, map_eq_bind_pure_comp, bind_assoc]

private theorem runBBucketBase_query_bind (paper : Bool)
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (q : (AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (k : (AuthL11.SMSpecDF Γ T Sig SS RS M CCoins E).Range q →
      AuthL11.SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (stB : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ)
    (sp : PRFPRNG.GameState Sig I K) :
    runBBucketBase paper cka prng fs Δcka qep tL par (liftM (OracleSpec.query q) >>= k) stB sp =
      stepBBucketBase paper cka prng fs Δcka qep tL par q stB sp >>= fun r =>
        runBBucketBase paper cka prng fs Δcka qep tL par (k r.1.1) r.1.2 r.2 := by
  simp [runBBucketBase, stepBBucketBase, simulateQ_bind, StateT.run_bind, map_eq_bind_pure_comp, bind_assoc]

private theorem runCBucketBase_abort (paper : Bool)
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (oa : AuthL11.SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {stC : AuthL10.EStateC Γ T Sig SS RS M E I × Option ℕ} {sc : CKA.GameState Γ T}
    (hab : stC.1.abort = true) :
    𝒟[runCBucketBase paper cka prng fs Δcka qep tL par oa stC sc] {true} = 0 := by
  induction oa using OracleComp.inductionOn generalizing stC sc with
  | pure b' =>
    rw [runCBucketBase_pure]; rcases stC with ⟨esC, winEpC⟩; dsimp only at hab
    cases paper <;> cases winEpC <;> simp [authOutBucketChoiceBase, authOutBucketPaper, authOutBucket, authOut, hab]
  | query_bind q k ih =>
    rw [runCBucketBase_query_bind]
    exact AuthL11.evalDist_bind_eq_zero _ _ fun r hr =>
      ih r.1.1 (stepCBucketBase_abort paper cka prng fs Δcka qep tL par q stC sc hab r hr)

private theorem runCBucketBase_le_runBBucketBase (paper : Bool)
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (oa : AuthL11.SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {stC : AuthL10.EStateC Γ T Sig SS RS M E I × Option ℕ} {sc : CKA.GameState Γ T}
    {stB : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) × Option ℕ}
    {sp : PRFPRNG.GameState Sig I K}
    (hwinEp : stC.2 = stB.2) (hSB : SyncBaseRaw prng Δcka qep tL stC.1 sc stB.1 sp) :
    𝒟[runCBucketBase paper cka prng fs Δcka qep tL par oa stC sc] {true} ≤
      𝒟[runBBucketBase paper cka prng fs Δcka qep tL par oa stB sp] {true} := by
  induction oa using OracleComp.inductionOn generalizing stC sc stB sp with
  | pure b' =>
    rw [runCBucketBase_pure, runBBucketBase_pure]
    rcases stC with ⟨esC, winEpC⟩; rcases stB with ⟨esB, winEpB⟩
    dsimp only at hwinEp hSB; subst hwinEp
    have houtBase : authOutBucket (2 + Δcka) tL (esC, winEpC) =
        authOutBucket (2 + Δcka) tL (esB, winEpC) := by
      cases winEpC with
      | none => rfl
      | some tWin =>
        have hw0 : esB.g.win = esC.g.win := AuthL10.eraseSt_win hSB.sync.g_eq
        have ha0 : authLosingConditionsAvoided (2 + Δcka) tL tWin esB.g =
            authLosingConditionsAvoided (2 + Δcka) tL tWin esC.g :=
          AuthL10.eraseSt_authOK hSB.sync.g_eq (2 + Δcka) tL tWin
        simp only [authOutBucket, authOut]
        rw [hSB.sync.abort_C, (show esB.abort = false from hSB.sync.abort_P), hw0, ha0]
    have hout : authOutBucketChoiceBase paper (2 + Δcka) tL (esC, winEpC) =
        authOutBucketChoiceBaseB paper (2 + Δcka) tL (esB, winEpC) := by
      cases paper
      · simp only [authOutBucketChoiceBase, authOutBucketChoiceBaseB, ↓reduceIte,
          Bool.false_eq_true, houtBase]
      · simp only [authOutBucketChoiceBase, authOutBucketChoiceBaseB,
          authOutBucketPaperAt, authOutBucketPaper, ↓reduceIte, houtBase]
        cases h : esB.h.lc with
        | none => simp
        | some e => simp [hSB.lc_ge_tH e h]
    rw [hout]
  | query_bind q k ih =>
    rw [runCBucketBase_query_bind, runBBucketBase_query_bind]
    refine leComp_stepCBucketBase_stepBBucketBase paper cka prng fs Δcka qep tL par q
      hwinEp hSB _ _ ?_
    rintro ⟨⟨uC, stC'⟩, sc'⟩ ⟨⟨uB, stB'⟩, sp'⟩ (hab | ⟨hu, hwinEp', hSB'⟩)
    · rw [runCBucketBase_abort paper cka prng fs Δcka qep tL par (k uC) hab]; exact zero_le
    · dsimp only at hu; subst hu; exact ih uC hwinEp' hSB'

private def initES_B
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (σv : Option Sig) (kr : KR) (kc : KC) :
    EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketState T Sig K I) :=
  let out := prng.up (prng.init kr) lam
  let vp := mkParties (T := T) (cka.initA kc) (cka.initB kc) σv
    (fs.initSender out.2) (fs.initReceiver out.2)
  { g := { st := fun P => match P with | .A => vp.1 | .B => vp.2, b := false }, h := {} }

private def initSP_none_bucket (prng : PRFPRNG KR Sig I K) (lam : I)
    (Δbucket : ℕ) (par : Bool) (kr : KR) : PRFPRNG.GameState Sig I K :=
  if inStage2BucketGen Δbucket none par 0 then
    AuthL10.initSP_zero prng kr
  else
    AuthL10.initSP prng lam (some 0) kr

private theorem syncBaseRaw_init_none [DecidableEq T]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep Δbucket : ℕ) (par : Bool)
    (kr : KR) (kc kc_ext : KC) :
    SyncBaseRaw (M := M) (E := E) prng Δcka qep none
      (AuthL10.initES_C cka prng fs lam none kr kc)
      (CKA.initState cka kc_ext true)
      (initES_B cka prng fs lam (some (prng.up (prng.init kr) lam).1) kr kc)
      (initSP_none_bucket prng lam Δbucket par kr) :=
  { sync :=
      { abort_C := rfl
        abort_P := rfl
        b_C := rfl
        b_P := by unfold initSP_none_bucket; split_ifs <;> rfl
        g_eq := rfl
        id_C := fun P => by cases P <;> rfl
        id_P := fun P => by cases P <;> rfl
        tcur_C := fun P => by cases P <;> rfl
        tcur_P := fun P => by cases P <;> rfl
        vS_eq := fun P => by cases P <;> rfl
        vR_eq := fun P => by cases P <;> rfl
        Tcur_eq := fun P => by cases P <;> rfl
        γ_C := fun P => by cases P <;> rfl
        root_P := fun P => by
          have hkr : AuthL10.knownRoot (moBase none) 0 = true := by simp [AuthL10.knownRoot]
          cases P <;> simp [toEStateP, initES_B, AuthL10.initES_C, mkParties, hkr]
        cka_st := fun P h => by simp [AuthL10.localCKA, AuthL10.initES_C] at h
        trans_inv := fun r hr => by simp [AuthL10.initES_C] at hr
        comp_inv := fun pos hpos => by simp [AuthL10.initES_C] at hpos
        epoch_S := rfl
        cache_gt := fun _ _ => ⟨rfl, rfl⟩
        ping_pong := Or.inl ⟨rfl, rfl⟩
        prng_before_tH := fun h => by simp [AuthL10.initES_C] at h
        prng_after_tH := fun h => by simp [AuthL10.initES_C] at h
        prng_at_tStar := fun _ h => by change 0 + 1 = 0 at h; omega }
    epoch_le_qep := fun _ => Nat.zero_le qep
    pre_tH := fun h => by simp [AuthL10.initES_C] at h
    lc_ge_tH := fun _ h => by simp [initES_B] at h }

private theorem syncBaseRaw_init_some [DecidableEq T]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep l : ℕ)
    (kr : KR) (kc : KC) :
    SyncBaseRaw (M := M) (E := E) prng Δcka qep (some l)
      (AuthL10.initES_C cka prng fs lam (some l) kr kc)
      (CKA.initState cka kc true)
      (initES_B cka prng fs lam (some (prng.up (prng.init kr) lam).1) kr kc)
      (AuthL10.initSP prng lam (some l) kr) := by
  have hloc0 : AuthL10.localCKA (moBase (some l)) Δcka 0 = false := by
    simp [AuthL10.localCKA]
  refine
    { sync :=
        { abort_C := rfl
          abort_P := rfl
          b_C := rfl
          b_P := rfl
          g_eq := rfl
          id_C := fun P => by cases P <;> rfl
          id_P := fun P => by cases P <;> rfl
          tcur_C := fun P => by cases P <;> rfl
          tcur_P := fun P => by cases P <;> rfl
          vS_eq := fun P => by cases P <;> rfl
          vR_eq := fun P => by cases P <;> rfl
          Tcur_eq := fun P => by cases P <;> rfl
          γ_C := fun P => by cases P <;> simp [AuthL10.initES_C, toEStateP, initES_B, mkParties, hloc0]
          root_P := fun P => by
            have hkr := knownRoot_moBase (some l) 0
            cases P <;> simp [toEStateP, initES_B, AuthL10.initES_C, mkParties, hkr]
          cka_st := fun P _ => by cases P <;> exact ⟨rfl, rfl⟩
          trans_inv := fun r hr => by simp [AuthL10.initES_C] at hr
          comp_inv := fun pos hpos => by simp [AuthL10.initES_C] at hpos
          epoch_S := rfl
          cache_gt := fun _ _ => ⟨rfl, rfl⟩
          ping_pong := Or.inl ⟨rfl, rfl⟩
          prng_before_tH := fun _ _ => ⟨rfl, rfl, rfl, rfl⟩
          prng_after_tH := fun _ h => by simp [AuthL10.initES_C] at h
          prng_at_tStar := fun h => by change 0 = l + 2 at h; omega }
      epoch_le_qep := fun _ => Nat.zero_le qep
      pre_tH := fun _ => ⟨rfl, rfl⟩
      lc_ge_tH := fun _ h => by simp [initES_B] at h }

private theorem initPRNGBucketHybrid_run_none
    [DecidableEq I] [SampleableType KC] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (Δbucket : ℕ) (par : Bool) (kr : KR) :
    (simulateQ (AuthL10.pImpl prng)
      ((initPRNGBucketHybrid (T := T) cka prng fs lam Δbucket none par 0).run {})).run
        { σ := prng.init kr, b := false } =
    (($ᵗ KC : ProbComp KC) >>= fun kc =>
      let out := prng.up (prng.init kr) lam
      pure ((some (mkParties (cka.initA kc) (cka.initB kc) (some out.1)
        (fs.initSender out.2) (fs.initReceiver out.2)), {}),
        initSP_none_bucket prng lam Δbucket par kr)) := by
  simp only [initPRNGBucketHybrid, StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp,
    bind_assoc, simulateQ_bind, simulateQ_pure, AuthL10.simulateQ_sampleT_pImpl, pure_bind]
  by_cases hb : inStage2BucketGen Δbucket none par 0 = true
  · simp [AuthL10.pImpl, rootPRNGBucketHybrid, resolveCorrRoot,
      liftPBucket, initSP_none_bucket, hb, PRFPRNG.challPrfQuery,
      PRFPRNG.oracleImpl, PRFPRNG.challPrfImpl, AuthL10.initSP_zero,
      StateT.run_bind, StateT.run_pure, StateT.run_get, StateT.run_set, StateT.run_lift,
      simulateQ_bind, simulateQ_query, simulateQ_pure, map_eq_bind_pure_comp, bind_assoc]
  · simp only [Bool.not_eq_true] at hb
    simp [AuthL10.pImpl, rootPRNGBucketHybrid, resolveCorrRoot,
      liftPBucket, initSP_none_bucket, hb, PRFPRNG.processQuery, PRFPRNG.corrQuery,
      PRFPRNG.oracleImpl, PRFPRNG.processImpl, PRFPRNG.corrImpl, PRFPRNG.samIfNec,
      AuthL10.initSP, StateT.run_bind, StateT.run_pure, StateT.run_get, StateT.run_set,
      StateT.run_lift, simulateQ_bind, simulateQ_query, simulateQ_pure,
      map_eq_bind_pure_comp, bind_assoc]

private theorem initPRNGBucketHybrid_run_some
    [DecidableEq I] [SampleableType KC] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (Δbucket : ℕ) (par : Bool) (l : ℕ) (kr : KR) :
    (simulateQ (AuthL10.pImpl prng)
      ((initPRNGBucketHybrid (T := T) cka prng fs lam Δbucket (some l) par (l + 2)).run {})).run
        { σ := prng.init kr, b := false } =
    (($ᵗ KC : ProbComp KC) >>= fun kc =>
      let out := prng.up (prng.init kr) lam
      pure ((some (mkParties (cka.initA kc) (cka.initB kc) (some out.1)
        (fs.initSender out.2) (fs.initReceiver out.2)), {}),
        AuthL10.initSP prng lam (some l) kr)) := by
  have h0_lt : ¬ (l + 2 < 0) := by omega
  have h0_eq : ¬ (0 = l + 2) := by omega
  have h0_tH : 0 < l + 2 := by omega
  simp only [initPRNGBucketHybrid, StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp,
    bind_assoc, simulateQ_bind, simulateQ_pure, AuthL10.simulateQ_sampleT_pImpl, pure_bind]
  simp [AuthL10.pImpl, rootPRNGBucketHybrid, resolveCorrRoot,
    liftPBucket, h0_lt, h0_eq, h0_tH, PRFPRNG.processQuery, PRFPRNG.corrQuery,
    PRFPRNG.oracleImpl, PRFPRNG.processImpl, PRFPRNG.corrImpl, PRFPRNG.samIfNec,
    AuthL10.initSP, StateT.run_bind, StateT.run_pure, StateT.run_get, StateT.run_set,
    StateT.run_lift, simulateQ_bind, simulateQ_query, simulateQ_pure,
    map_eq_bind_pure_comp, bind_assoc]

/-- Hop-2 base (`t = healEpoch tL`, `b = false`, paper engine): ideal CKA at `healEpoch tL` is
bounded by the real PRF-PRNG world of `redPRNGAuthDFPaperBucketHybrid` at `t = healEpoch tL`. -/
theorem cka_branch_true_redCKAAuthDFPaperBucket_le_prng_false_impl
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    𝒟[CKA.branch cka Δcka (healEpoch tL) true
        (redCKAAuthDFPaperBucket cka prng fs lam Δcka qep tL par A)] {true} ≤
      𝒟[PRFPRNG.branch prng false
        (redPRNGAuthDFPaperBucketHybrid cka prng fs lam Δcka qep tL par (healEpoch tL) A)] {true} := by
  have hcImpl : (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (CKA.GameState Γ T) ProbComp) + CKA.oracleImpl cka Δcka (healEpoch tL) =
      AuthL10.cImpl cka Δcka (healEpoch tL) := rfl
  have hpImpl : (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (PRFPRNG.GameState Sig I K) ProbComp) + PRFPRNG.oracleImpl prng =
      AuthL10.pImpl prng := rfl
  cases tL with
  | none =>
    have hL : CKA.branch cka Δcka (healEpoch none) true
        (redCKAAuthDFPaperBucket cka prng fs lam Δcka qep none par A) =
        (($ᵗ KC : ProbComp KC) >>= fun kc_ext => ($ᵗ KR : ProbComp KR) >>= fun kr =>
          ($ᵗ KC : ProbComp KC) >>= fun kc =>
            runCBucketBase true cka prng fs Δcka qep none par A
              (AuthL10.initES_C cka prng fs lam none kr kc, none)
              (CKA.initState cka kc_ext true)) := by
      unfold CKA.branch redCKAAuthDFPaperBucket engRunDFPaperBucket initCKA
        runCBucketBase AuthL10.initES_C implEDFPaperBucket implEDFBucketRawChoiceBase authOutBucketChoiceBase
      simp only [hcImpl, StateT.run'_eq, StateT.run_lift, StateT.run_bind, StateT.run_pure,
        simulateQ_bind, simulateQ_pure, AuthL10.simulateQ_sampleT_run,
        map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, ↓reduceIte, healEpoch_none_eq]
      rfl
    have hR : PRFPRNG.branch prng false
        (redPRNGAuthDFPaperBucketHybrid cka prng fs lam Δcka qep none par (healEpoch none) A) =
        (($ᵗ KR : ProbComp KR) >>= fun kr => ($ᵗ KC : ProbComp KC) >>= fun kc =>
          runBBucketBase true cka prng fs Δcka qep none par A
            (initES_B cka prng fs lam (some (prng.up (prng.init kr) lam).1) kr kc, none)
            (initSP_none_bucket prng lam (3 + Δcka) par kr)) := by
      unfold PRFPRNG.branch redPRNGAuthDFPaperBucketHybrid redPRNGAuthDFPaperBucketHybridAt engRunDFPaperBucket
        runBBucketBase initES_B implEDFPaperBucket implEDFBucketRawChoiceBase authOutBucketChoiceBaseB
      simp only [hpImpl, healEpoch_none_eq, StateT.run'_eq, StateT.run_bind, simulateQ_bind,
        initPRNGBucketHybrid_run_none cka prng fs lam (3 + Δcka) par, map_eq_bind_pure_comp,
        bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure, Function.comp_apply, ↓reduceIte]
      rfl
    have hconst :
        𝒟[($ᵗ KC : ProbComp KC) >>= fun _ : KC => ($ᵗ KR : ProbComp KR) >>= fun kr =>
          ($ᵗ KC : ProbComp KC) >>= fun kc =>
            runBBucketBase true cka prng fs Δcka qep none par A
              (initES_B cka prng fs lam (some (prng.up (prng.init kr) lam).1) kr kc, none)
              (initSP_none_bucket prng lam (3 + Δcka) par kr)] {true} =
        𝒟[($ᵗ KR : ProbComp KR) >>= fun kr => ($ᵗ KC : ProbComp KC) >>= fun kc =>
          runBBucketBase true cka prng fs Δcka qep none par A
            (initES_B cka prng fs lam (some (prng.up (prng.init kr) lam).1) kr kc, none)
            (initSP_none_bucket prng lam (3 + Δcka) par kr)] {true} := by
      rw [OracleComp.evalDist_bind_const]
    rw [hL, hR, ← hconst]
    refine AuthL11.evalDist_bind_mono ($ᵗ KC) _ _ fun kc_ext _ => ?_
    refine AuthL11.evalDist_bind_mono ($ᵗ KR) _ _ fun kr _ => ?_
    refine AuthL11.evalDist_bind_mono ($ᵗ KC) _ _ fun kc _ => ?_
    exact runCBucketBase_le_runBBucketBase true cka prng fs Δcka qep none par A rfl
      (syncBaseRaw_init_none cka prng fs lam Δcka qep (3 + Δcka) par kr kc kc_ext)
  | some l =>
    have hL : CKA.branch cka Δcka (healEpoch (some l)) true
        (redCKAAuthDFPaperBucket cka prng fs lam Δcka qep (some l) par A) =
        (($ᵗ KC : ProbComp KC) >>= fun kc => ($ᵗ KR : ProbComp KR) >>= fun kr =>
          runCBucketBase true cka prng fs Δcka qep (some l) par A
            (AuthL10.initES_C cka prng fs lam (some l) kr kc, none)
            (CKA.initState cka kc true)) := by
      unfold CKA.branch redCKAAuthDFPaperBucket engRunDFPaperBucket initCKA
        runCBucketBase AuthL10.initES_C implEDFPaperBucket implEDFBucketRawChoiceBase authOutBucketChoiceBase
      simp only [hcImpl, StateT.run'_eq, StateT.run_lift, StateT.run_bind, StateT.run_pure,
        simulateQ_bind, simulateQ_pure, AuthL10.simulateQ_sampleT_run,
        map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, ↓reduceIte, healEpoch_some_eq]
      rfl
    have hR : PRFPRNG.branch prng false
        (redPRNGAuthDFPaperBucketHybrid cka prng fs lam Δcka qep (some l) par (healEpoch (some l)) A) =
        (($ᵗ KR : ProbComp KR) >>= fun kr => ($ᵗ KC : ProbComp KC) >>= fun kc =>
          runBBucketBase true cka prng fs Δcka qep (some l) par A
            (initES_B cka prng fs lam (some (prng.up (prng.init kr) lam).1) kr kc, none)
            (AuthL10.initSP prng lam (some l) kr)) := by
      unfold PRFPRNG.branch redPRNGAuthDFPaperBucketHybrid redPRNGAuthDFPaperBucketHybridAt engRunDFPaperBucket
        runBBucketBase initES_B implEDFPaperBucket implEDFBucketRawChoiceBase authOutBucketChoiceBaseB
      simp only [hpImpl, healEpoch_some_eq, StateT.run'_eq, StateT.run_bind, simulateQ_bind,
        initPRNGBucketHybrid_run_some cka prng fs lam (3 + Δcka) par l, map_eq_bind_pure_comp,
        bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure, Function.comp_apply, ↓reduceIte]
      rfl
    rw [hL, hR, OracleComp.evalDist_bind_bind_swap ($ᵗ KR) ($ᵗ KC)]
    refine AuthL11.evalDist_bind_mono ($ᵗ KC) _ _ fun kc _ => ?_
    refine AuthL11.evalDist_bind_mono ($ᵗ KR) _ _ fun kr _ => ?_
    exact runCBucketBase_le_runBBucketBase true cka prng fs Δcka qep (some l) par A rfl
      (syncBaseRaw_init_some cka prng fs lam Δcka qep l kr kc)

end BaseCoupling

end CryptoGames.SM.Construction.DeliverForge
