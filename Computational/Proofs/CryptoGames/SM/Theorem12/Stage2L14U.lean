/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.FSAEAD.Lazy -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Reductions -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem12.Stage2Defs -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.SM.Engine
import Computational.Proofs.CryptoGames.SM.Theorem12.Lemma13
import Computational.Proofs.CryptoGames.SM.Theorem12.Lemma14

/-!
# Stage-2 Switch-Back Lemma 14 (`b = true` Coupling) (`SM/Theorem12/Stage2L14U.lean`)

**Checked by Lean.** No theorem of `Computational/Theorems/` unfolds a definition of this file, and
Lean's kernel checks every proof in it: you do not need to read it to trust those theorems.

Proves `branch_redCKAPrivU_true_dEq_redPRNGPriv_true`: for `0 < t` and admissible `tL`,
`CKA.branch cka Δcka (healEpoch tL) true (redCKAPrivU ... tL t A)` is distributionally equal (`DEq`)
to `PRFPRNG.branch prng true (redPRNGPriv ... tL t A)`.-/

set_option autoImplicit false

public section

open OracleComp OracleSpec ENNReal CryptoGames CryptoGames.Lazy

namespace CryptoGames.SM.Construction

section Stage2L14U

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

variable (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
  (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)

namespace PrivL14U

open Engine PrivL14

set_option linter.unusedSectionVars false

private def projL
    (es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAUState T I K)) :
    EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I) :=
  { g := es.g, h := es.h.1, abort := es.abort }

private def patchES (prng : PRFPRNG KR Sig I K) (tStar : ℕ)
    (esL : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAUState T I K))
    (esR : EState (PartyState Γ T (Option Sig) SS RS) M (Header T × E) (PRNGState T Sig K)) :
    EState (PartyState Γ T (Option Sig) SS RS) M (Header T × E) (PRNGState T Sig K) :=
  { g := esR.g
    abort := esR.abort
    h := { cache := fun e =>
      if e = tStar then
        match esR.h.cache e, esL.h.1.cache e with
        | some (Tc, σopt, _), some (_, Ik) =>
          some (Tc, σopt, (prng.up (esL.g.st (Party.senderOf tStar).other).root Ik).2)
        | x, _ => x
      else esR.h.cache e } }

private def SyncU (prng : PRFPRNG KR Sig I K) (Δcka : ℕ) (tL : Option ℕ) (tStar : ℕ)
    (sL : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAUState T I K) ×
      CKA.GameState Γ T)
    (sR : EState (PartyState Γ T (Option Sig) SS RS) M (Header T × E) (PRNGState T Sig K) ×
      PRFPRNG.GameState Sig I K) : Prop :=
  Sync prng Δcka tL tStar (projL sL.1, sL.2)
    (patchES prng tStar sL.1 sR.1, { sR.2 with b := false }) ∧
  sR.2.b = true ∧
  (max (sL.1.g.epoch .A) (sL.1.g.epoch .B) < tStar → sR.2.table = [] ∧ sL.1.h.2 = none) ∧
  (∀ Tc σopt k, sR.1.h.cache tStar = some (Tc, σopt, k) → sL.1.h.2 = some k)

private def SyncOrDoomU (prng : PRFPRNG KR Sig I K) (Δcka : ℕ) (tL : Option ℕ) (tStar : ℕ)
    (sL : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAUState T I K) ×
      CKA.GameState Γ T)
    (sR : EState (PartyState Γ T (Option Sig) SS RS) M (Header T × E) (PRNGState T Sig K) ×
      PRFPRNG.GameState Sig I K) : Prop :=
  SyncU prng Δcka tL tStar sL sR ∨
    (Doom tL sL.1 ∧ Doom tL sR.1)

private theorem SyncU.privOutP_eq (prng : PRFPRNG KR Sig I K) (Δcka : ℕ) (tL : Option ℕ)
    (tStar : ℕ) (b b' : Bool)
    {sL : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAUState T I K) ×
      CKA.GameState Γ T}
    {sR : EState (PartyState Γ T (Option Sig) SS RS) M (Header T × E) (PRNGState T Sig K) ×
      PRFPRNG.GameState Sig I K}
    (hs : SyncU prng Δcka tL tStar sL sR) :
    privOutP (2 + Δcka) ⟨false, tL, tStar⟩ b b' sL.1 =
      privOutP (2 + Δcka) ⟨false, tL, tStar⟩ b b' sR.1 := by
  simpa [privOutP, projL, patchES] using Sync.privOutP_eq prng Δcka tL tStar b b' hs.1

private theorem SyncU.set_win {prng : PRFPRNG KR Sig I K} {Δcka : ℕ} {tL : Option ℕ} {tStar : ℕ}
    {esL : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAUState T I K)}
    {cs : CKA.GameState Γ T}
    {esR : EState (PartyState Γ T (Option Sig) SS RS) M (Header T × E) (PRNGState T Sig K)}
    {ps : PRFPRNG.GameState Sig I K}
    (hs : SyncU prng Δcka tL tStar (esL, cs) (esR, ps)) :
    SyncU prng Δcka tL tStar
      ({ esL with g := { esL.g with win := true } }, cs)
      ({ esR with g := { esR.g with win := true } }, ps) := by
  rcases hs with ⟨hs14, hb, hpre, hcache⟩
  exact ⟨hs14.set_win, hb, hpre, hcache⟩

private theorem sync_congr_cache_tStar
    {esL : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {cs : CKA.GameState Γ T}
    {esR : EState (PartyState Γ T (Option Sig) SS RS) M (Header T × E) (PRNGState T Sig K)}
    {ps : PRFPRNG.GameState Sig I K}
    {hR' : PRNGState T Sig K} {tL : Option ℕ} {tStar : ℕ}
    (hs : Sync prng Δcka tL tStar (esL, cs) (esR, ps))
    (hne : ∀ e, e ≠ tStar → hR'.cache e = esR.h.cache e)
    (hnone : esR.h.cache tStar = none → hR'.cache tStar = none)
    (hnotsend : ∀ P t0, P.sendsIn (t0 + 1) = true →
      esL.g.epoch P = t0 + 1 → esL.g.epoch P.other = t0 → t0 + 1 ≠ tStar) :
    Sync prng Δcka tL tStar (esL, cs) ({ esR with h := hR' }, ps) := by
  rcases hs with ⟨habL, habR, he, hinv, hp, hcka, ⟨hpp1, hpp2⟩, hprng⟩
  refine ⟨habL, habR, he, hinv, hp, hcka, ⟨fun t' ht' => ?_, ?_⟩, hprng⟩
  · rcases hpp1 t' ht' with ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    by_cases het : t' = tStar
    · subst het; exact hnone h2
    · rw [hne t' het]; exact h2
  · rcases hpp2 with hleft | ⟨P, t0, Tc, Ik, hP, hepP, hepPo, hcL, ⟨hcR, hroot⟩, hcs⟩
    · exact Or.inl hleft
    · right
      refine ⟨P, t0, Tc, Ik, hP, hepP, hepPo, hcL, ⟨?_, hroot⟩, hcs⟩
      rw [hne (t0 + 1) (hnotsend P t0 hP hepP hepPo)]
      exact hcR

private theorem runHM_lift_state2 {α : Type}
    {oimpl : QueryImpl (CKA.spec Γ CCoins T I) (StateT (CKA.GameState Γ T) ProbComp)}
    (mx : CKA.AdversaryComp Γ CCoins T I α) (h : CKAUState T I K) (cs : CKA.GameState Γ T) :
    runHM oimpl
      (StateT.lift mx : Engine.HM (CKA.spec Γ CCoins T I) (CKAUState T I K) α) h cs =
    (fun r => ((r.1.1, (r.1.2, h.2)), r.2)) <$>
      runHM oimpl
        (StateT.lift mx : Engine.HM (CKA.spec Γ CCoins T I) (CKAState T I) α) h.1 cs := by
  simp [runHM, StateT.run_lift, map_eq_bind_pure_comp]

private theorem runHM_reveal_hooksCKAU
    {oimpl : QueryImpl (CKA.spec Γ CCoins T I) (StateT (CKA.GameState Γ T) ProbComp)}
    (mo : Mode) (ctx : Ctx (Option Γ) T Sig SS RS M E)
    (P : Party) (vp : PartyState (Option Γ) T Sig SS RS) (h : CKAUState T I K)
    (cs : CKA.GameState Γ T) :
    runHM oimpl
      ((hooksCKAU cka prng fs Δcka mo).reveal ctx P vp) h cs =
    (fun r => ((r.1.1, (r.1.2, h.2)), r.2)) <$>
      runHM oimpl
        ((hooksCKA cka prng fs Δcka mo).reveal ctx P vp) h.1 cs := by
  dsimp only [hooksCKAU, hooksCKA, liftC]
  cases vp.γ with
  | some γ =>
    simp [runHM_pure]
  | none =>
    rw [runHM_bind, runHM_bind, runHM_lift_state2, bind_map_left, map_bind]
    congr 1
    funext ⟨⟨γ?, h1⟩, cs1⟩
    cases γ? <;> simp [runHM_pure]

private theorem runHM_commit_hooksCKAU
    {oimpl : QueryImpl (CKA.spec Γ CCoins T I) (StateT (CKA.GameState Γ T) ProbComp)}
    (mo : Mode) (ctx : Ctx (Option Γ) T Sig SS RS M E)
    (P : Party) (old new : PartyState (Option Γ) T Sig SS RS) (h : CKAUState T I K)
    (cs : CKA.GameState Γ T) :
    runHM oimpl
      ((hooksCKAU cka prng fs Δcka mo).commit ctx P old new) h cs =
    (fun r => ((r.1.1, (r.1.2, h.2)), r.2)) <$>
      runHM oimpl
        ((hooksCKA cka prng fs Δcka mo).commit ctx P old new) h.1 cs := by
  dsimp only [hooksCKAU, hooksCKA, liftC]
  by_cases hc : (decide (old.tcur < new.tcur) && old.γ.isNone) = true
  · simp only [hc, ↓reduceIte]
    rw [runHM_bind, runHM_bind, runHM_lift_state2, bind_map_left, map_bind]
    congr 1
    funext ⟨⟨u, h1⟩, cs1⟩
    cases u with
    | none => simp [runHM_pure]
    | some _ =>
      dsimp only
      by_cases h2 : mo.tH + Δcka ≤ new.tcur
      · simp only [h2, ↓reduceIte]
        rw [runHM_bind, runHM_bind, runHM_lift_state2, bind_map_left, map_bind]
        congr 1
        funext ⟨⟨γ?, h1'⟩, cs2⟩
        cases γ? <;> simp [runHM_pure]
      · simp [h2, runHM_pure]
  · simp [hc, runHM_pure]

private theorem runEM_corrE_syncU (tL : Option ℕ) (tStar : ℕ) (P : Party)
    (sL : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAUState T I K) ×
      CKA.GameState Γ T)
    (sR : EState (PartyState Γ T (Option Sig) SS RS) M (Header T × E) (PRNGState T Sig K) ×
      PRFPRNG.GameState Sig I K)
    (hs : SyncU prng Δcka tL tStar sL sR)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) tL tStar = true) :
    ∃ ans sL' sR',
      runEM (CKA.oracleImpl cka Δcka (healEpoch tL))
        (corrE (hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩) ⟨false, tL, tStar⟩ P) sL =
        pure (ans, sL') ∧
      runEM (PRFPRNG.oracleImpl prng)
        (corrE (hooksPRNG cka prng fs ⟨false, tL, tStar⟩) ⟨false, tL, tStar⟩ P) sR =
        pure (ans, sR') ∧
      SyncOrDoomU prng Δcka tL tStar sL' sR' := by
  rcases sL with ⟨esL, cs⟩
  rcases sR with ⟨esR, ps⟩
  rcases hs with ⟨hs14, hb, hpre, hcache⟩
  dsimp only at hs14 hb hpre hcache
  have habL : esL.abort = false := hs14.1
  have habR : esR.abort = false := hs14.2.1
  have he : eraseSt esL.g = eraseSt esR.g := hs14.2.2.1
  have hwin := eraseSt_win he
  have hca := eraseSt_corrAllowed he P
  unfold corrE
  rw [runEM_bind, runEM_get, pure_bind, runEM_bind, runEM_get, pure_bind]
  dsimp only
  rw [habL, habR, ← hwin, ← hca]
  by_cases hguard : (esL.g.win || !esL.g.corrAllowed P) = true
  · simp only [Bool.false_or, hguard, ↓reduceIte, runEM_pure]
    exact ⟨none, (esL, cs), (esR, ps), rfl, rfl, Or.inl ⟨hs14, hb, hpre, hcache⟩⟩
  · simp only [Bool.false_or, hguard, Bool.false_eq_true, ↓reduceIte]
    have he_ac := eraseSt_afterCorr he P
    have hld_eq := eraseSt_leakDoom he he_ac ⟨false, tL, tStar⟩
    have hcd_eq := eraseSt_corrDoom he ⟨false, tL, tStar⟩ P
    rw [← hld_eq, ← hcd_eq]
    by_cases hdoom : (Policy.leakDoom ⟨false, tL, tStar⟩ esL.g (esL.g.afterCorr P) ||
        Policy.corrDoom ⟨false, tL, tStar⟩ esL.g P) = true
    · simp only [hdoom, ↓reduceIte, runEM_abort_pure]
      exact ⟨none, ({ esL with abort := true }, cs), ({ esR with abort := true }, ps),
        rfl, rfl, Or.inr ⟨Or.inl rfl, Or.inl rfl⟩⟩
    · simp only [hdoom, Bool.false_eq_true, ↓reduceIte]
      have hdoom' : Policy.leakDoom ⟨false, tL, tStar⟩ esL.g (esL.g.afterCorr P) = false ∧
          Policy.corrDoom ⟨false, tL, tStar⟩ esL.g P = false :=
        Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hdoom)
      rcases runHM_reveal_sync cka prng fs Δcka tL tStar P (projL esL) cs
        (patchES prng tStar esL esR) { ps with b := false } hs14 hvg hdoom'.1 hdoom'.2 with
        ⟨hrevL, hrevR⟩
      have hrevLU :
          runHM (CKA.oracleImpl cka Δcka (healEpoch tL))
            ((hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩).reveal esL.g P (esL.g.st P))
            esL.h cs =
          pure ((some (realParty (esR.g.st P) (esR.g.st P).γ (esL.g.st P).root
            (esR.g.st P).vS (esR.g.st P).vR), esL.h), cs) := by
        rcases hs14.2.2.2.2.1 P with ⟨_, _, _, _, hvS, hvR, _⟩
        dsimp only [projL, patchES] at hvS hvR
        rw [runHM_reveal_hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩ esL.g P (esL.g.st P) esL.h cs]
        simp only [projL, patchES] at hrevL
        rw [hrevL, map_pure, Prod.mk.eta, hvS, hvR]
      have hrevRU :
          runHM (PRFPRNG.oracleImpl prng)
            ((hooksPRNG cka prng fs ⟨false, tL, tStar⟩).reveal esR.g P (esR.g.st P))
            esR.h ps =
          pure ((some (realParty (esR.g.st P) (esR.g.st P).γ (esL.g.st P).root
            (esR.g.st P).vS (esR.g.st P).vR), esR.h), ps) := by
        have hrootSome : (esR.g.st P).root = some (esL.g.st P).root := by
          dsimp only [hooksPRNG, projL, patchES] at hrevR
          cases hr : (esR.g.st P).root with
          | none =>
            rw [hr, runHM_pure] at hrevR
            injection hrevR with h1
            rcases Prod.mk.inj h1 with ⟨h2, _⟩
            rcases Prod.mk.inj h2 with ⟨h3, _⟩
            contradiction
          | some σ =>
            rw [hr, runHM_pure] at hrevR
            injection hrevR with h1
            rcases Prod.mk.inj h1 with ⟨h2, _⟩
            rcases Prod.mk.inj h2 with ⟨h3, _⟩
            injection h3 with h4
            have := congrArg PartyState.root h4
            simpa [realParty] using this
        dsimp only [hooksPRNG]
        simp [hrootSome, runHM_pure]
      rw [runEM_bind, runEM_liftH, hrevLU, map_pure, pure_bind]
      dsimp only
      rw [runEM_modify_pure]
      rw [runEM_bind, runEM_liftH, hrevRU, map_pure, pure_bind]
      dsimp only
      rw [runEM_modify_pure]
      refine ⟨_, _, _, rfl, rfl, Or.inl ?_⟩
      rcases hs14 with ⟨_, _, _, hinv, hp, hcka, hpp, hprng⟩
      refine ⟨⟨habL, habR, he_ac, hinv.afterCorr, hp, hcka, hpp, hprng⟩, hb, hpre, hcache⟩

private theorem runHM_startRecv_hooksCKAU_honest (tL : Option ℕ) (tStar t : ℕ)
    (ctx : Ctx (Option Γ) T Sig SS RS M E) (P : Party) (γv : Option Γ) (σ : Sig)
    (Tn : T) (Ik : I) (kEpoch : K) (h : CKAUState T I K) (cs : CKA.GameState Γ T)
    (hcL : h.1.cache t = some (Tn, Ik))
    (hkEq : t = tStar → h.2 = some kEpoch)
    (hkNe : t ≠ tStar → kEpoch = (prng.up σ Ik).2) :
    runHM (CKA.oracleImpl cka Δcka (healEpoch tL))
      ((hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩).startRecv ctx P t γv σ Tn) h cs =
    pure ((some (some (γv.map fun γ => (cka.receive γ Tn).1,
      (prng.up σ Ik).1, fs.initReceiver kEpoch)), h), cs) := by
  dsimp only [hooksCKAU]
  rw [runHM_bind, runHM_get, pure_bind]
  simp only [hcL, ↓reduceIte]
  by_cases het : t = tStar
  · simp [het, hkEq het, runHM_pure]
  · simp [het, hkNe het, runHM_pure]

private theorem runHM_vRecv_syncU (tL : Option ℕ) (tStar : ℕ)
    (P : Party) (c : Header T × E) (rec : Option (Record M (Header T × E)))
    (esL : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAUState T I K))
    (cs : CKA.GameState Γ T)
    (esR : EState (PartyState Γ T (Option Sig) SS RS) M (Header T × E) (PRNGState T Sig K))
    (ps : PRFPRNG.GameState Sig I K)
    (hs : SyncU prng Δcka tL tStar (esL, cs) (esR, ps)) :
    (runHM (CKA.oracleImpl cka Δcka (healEpoch tL))
        (vRecv (hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩) esL.g P (esL.g.st P) c rec)
        esL.h cs = pure ((some none, esL.h), cs) ∧
      runHM (PRFPRNG.oracleImpl prng)
        (vRecv (hooksPRNG cka prng fs ⟨false, tL, tStar⟩) esR.g P (esR.g.st P) c rec)
        esR.h ps = pure ((some none, esR.h), ps)) ∨
    ∃ st'L st'R i m,
      runHM (CKA.oracleImpl cka Δcka (healEpoch tL))
        (vRecv (hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩) esL.g P (esL.g.st P) c rec)
        esL.h cs = pure ((some (some (st'L, c.1.1, i, m)), esL.h), cs) ∧
      runHM (PRFPRNG.oracleImpl prng)
        (vRecv (hooksPRNG cka prng fs ⟨false, tL, tStar⟩) esR.g P (esR.g.st P) c rec)
        esR.h ps = pure ((some (some (st'R, c.1.1, i, m)), esR.h), ps) ∧
      RecvStep cka Δcka tL tStar (projL esL) (patchES prng tStar esL esR) cs P c.1.1 st'L st'R := by
  rcases hs with ⟨hs14, _, _, hcache⟩
  dsimp only at hs14 hcache
  rcases hs14 with ⟨_, _, _, _, hp, _, hpp, _⟩
  dsimp only [projL, patchES] at hp
  rcases hp P with ⟨hidL, hidR, htcurL, htcurR, hvS, hvR, hTcur, hγ, hroot⟩
  unfold vRecv
  dsimp only
  rw [hidL, hidR, htcurL, htcurR]
  by_cases hbad : (P.sendsIn c.1.1 || decide (esL.g.epoch P + 1 < c.1.1)) = true
  · left
    simp [hbad, runHM_pure]
  · simp only [hbad, Bool.false_eq_true, ↓reduceIte]
    have hbad' : P.sendsIn c.1.1 = false ∧ c.1.1 ≤ esL.g.epoch P + 1 := by
      rcases Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hbad) with ⟨h1, h2⟩
      exact ⟨h1, by have := of_decide_eq_false h2; omega⟩
    by_cases hstep : c.1.1 = esL.g.epoch P + 1
    · simp only [hstep, ↓reduceIte]
      cases hTn : c.1.2 with
      | none =>
        left
        simp [runHM_pure]
      | some Tn =>
        have hsends : P.sendsIn (esL.g.epoch P + 1) = false := by
          rw [← hstep]; exact hbad'.1
        rcases hpp.recv_step P with ⟨hcL, hcR⟩ |
          ⟨_, hepO, Tc, Ik, hcL, ⟨hcR, hrootO⟩, hcsO⟩
        · dsimp only [projL, patchES] at hcL hcR
          have hcR' : esR.h.cache (esL.g.epoch P + 1) = none := by
            by_cases het : esL.g.epoch P + 1 = tStar
            · simp only [het, ↓reduceIte] at hcR
              cases hx : esR.h.cache tStar with
              | none => simpa [het] using hx
              | some val =>
                rcases val with ⟨Tc', σopt', k'⟩
                rw [het] at hcL
                simp [hx, hcL] at hcR
            · simpa [het] using hcR
          left
          dsimp only [hooksCKAU, hooksPRNG]
          simp [runHM_bind, runHM_get, hcL, hcR', runHM_pure]
        · dsimp only [projL, patchES] at hcL hcR hepO hrootO
          have hexR : ∃ kEpoch,
              esR.h.cache (esL.g.epoch P + 1) =
                some (Tc,
                  (if decide (tStar ≤ esL.g.epoch P + 1) ||
                      (tL.isSome && decide (esL.g.epoch P + 1 < healEpoch tL))
                   then some (prng.up (esL.g.st P).root Ik).1 else none),
                  kEpoch) ∧
              (esL.g.epoch P + 1 = tStar → esL.h.2 = some kEpoch) ∧
              (esL.g.epoch P + 1 ≠ tStar → kEpoch = (prng.up (esL.g.st P).root Ik).2) := by
            by_cases het : esL.g.epoch P + 1 = tStar
            · simp only [het, ↓reduceIte] at hcR
              rw [het] at hcL
              cases hx : esR.h.cache tStar with
              | none => simp [hx] at hcR
              | some val =>
                rcases val with ⟨Tc', σopt', k'⟩
                simp only [hx, hcL] at hcR
                injection hcR with hval
                rcases Prod.mk.inj hval with ⟨rfl, hval2⟩
                rcases Prod.mk.inj hval2 with ⟨rfl, _⟩
                exact ⟨k', by simp [het, hx], fun _ => hcache Tc' _ k' hx,
                  fun hne => absurd het hne⟩
            · simp only [het, ↓reduceIte] at hcR
              exact ⟨_, hcR, fun heq => absurd heq het, fun _ => rfl⟩
          rcases hexR with ⟨kEpoch, hcR', hkEq, hkNe⟩
          by_cases hTc : Tc = Tn
          · subst hTc
            have hsrL := runHM_startRecv_hooksCKAU_honest cka prng fs Δcka tL tStar
              (esL.g.epoch P + 1) esL.g P (esL.g.st P).γ (esL.g.st P).root Tc Ik kEpoch
              esL.h cs hcL hkEq hkNe
            rw [runHM_bind, hsrL, pure_bind]
            dsimp only [hooksCKAU, hooksPRNG]
            simp only [runHM_bind, runHM_get, pure_bind, hcR', ↓reduceIte,
              runHM_pure, Function.update_self]
            cases hfs : fs.receive (fs.initReceiver kEpoch) c.1 c.2 with
            | none =>
              left; simp [runHM_pure]
            | some res =>
              rcases res with ⟨v', i, m⟩
              right
              refine ⟨_, _, i, m, by rw [runHM_pure], by rw [runHM_pure], Or.inr ?_⟩
              refine ⟨rfl, hsends, rfl, rfl, rfl, rfl, hvS, ?_, hTcur, ?_, rfl,
                hepO, hrootO, Tc, rfl, hcsO⟩
              · rw [hvR]
              · dsimp only [projL, patchES]
                cases hγ' : (esL.g.st P).γ with
                | none => rfl
                | some γ0 =>
                  have hγeq : γ0 = (esR.g.st P).γ := by
                    rw [hγ] at hγ'
                    split at hγ'
                    · exact Option.some.inj hγ'.symm
                    · contradiction
                  simp [hγeq]
          · left
            dsimp only [hooksCKAU, hooksPRNG]
            simp [runHM_bind, runHM_get, hcL, hcR', hTc, runHM_pure]
    · have hle : c.1.1 ≤ esL.g.epoch P := by omega
      simp only [hstep, ↓reduceIte, pure_bind]
      rw [hvR]
      cases hvRt : (esR.g.st P).vR c.1.1 with
      | none =>
        left; simp [runHM_pure]
      | some v =>
        dsimp only [hooksCKAU, hooksPRNG]
        rw [runHM_bind, runHM_pure, pure_bind, runHM_bind, runHM_pure, pure_bind]
        dsimp only
        cases hfs : fs.receive v c.1 c.2 with
        | none =>
          left; simp [runHM_pure]
        | some res =>
          rcases res with ⟨v', i, m⟩
          right
          refine ⟨_, _, i, m, by rw [runHM_pure], by rw [runHM_pure], Or.inl ?_⟩
          refine ⟨hle, htcurL, rfl, rfl, hidL, hidR, htcurL, htcurR, hvS, rfl, hTcur, hγ, hroot⟩

private theorem runEM_commitE_syncU (tL : Option ℕ) (tStar : ℕ) (P : Party) (pos : Pos)
    (st'L : PartyState (Option Γ) T Sig SS RS)
    (st'R : PartyState Γ T (Option Sig) SS RS)
    (esL : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAUState T I K))
    (cs : CKA.GameState Γ T)
    (esR : EState (PartyState Γ T (Option Sig) SS RS) M (Header T × E) (PRNGState T Sig K))
    (ps : PRFPRNG.GameState Sig I K)
    (hs : SyncU prng Δcka tL tStar (esL, cs) (esR, ps))
    (hr : RecvStep cka Δcka tL tStar (projL esL) (patchES prng tStar esL esR) cs P pos.epoch st'L st'R) :
    ∃ s₁L s₁R cs',
      runEM (CKA.oracleImpl cka Δcka (healEpoch tL))
        (commitE (hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩) esL.g P (esL.g.st P) st'L pos)
        (esL, cs) = pure (some s₁L, (esL, cs')) ∧
      runEM (PRFPRNG.oracleImpl prng)
        (commitE (hooksPRNG cka prng fs ⟨false, tL, tStar⟩) esR.g P (esR.g.st P) st'R pos)
        (esR, ps) = pure (some s₁R, (esR, ps)) ∧
      SyncU prng Δcka tL tStar ({ esL with g := s₁L }, cs') ({ esR with g := s₁R }, ps) := by
  rcases hs with ⟨hs14, hb, hpre, hcache⟩
  dsimp only at hs14 hb hpre hcache
  rcases runEM_commitE_sync cka prng fs Δcka tL tStar P pos st'L st'R
    (projL esL) cs (patchES prng tStar esL esR) { ps with b := false } hs14 hr with
    ⟨s₁L, s₁R, cs', hcommL14, hcommR14, hs14'⟩
  have hdet : ∃ new',
      runHM (CKA.oracleImpl cka Δcka (healEpoch tL))
        ((hooksCKA cka prng fs Δcka ⟨false, tL, tStar⟩).commit
          (esL.g.accept P st'L pos) P (esL.g.st P) st'L)
        esL.h.1 cs = pure ((some new', esL.h.1), cs') ∧
      s₁L = { esL.g.accept P st'L pos with st := Function.update (esL.g.accept P st'L pos).st P new' } := by
    unfold commitE at hcommL14
    dsimp only [projL] at hcommL14
    rw [runEM_bind, runEM_liftH] at hcommL14
    have hdet0 : ∃ opt cs1,
        runHM (CKA.oracleImpl cka Δcka (healEpoch tL))
          ((hooksCKA cka prng fs Δcka ⟨false, tL, tStar⟩).commit
            (esL.g.accept P st'L pos) P (esL.g.st P) st'L)
          esL.h.1 cs = pure ((opt, esL.h.1), cs1) := by
      dsimp only [hooksCKA]
      by_cases hc : (decide ((esL.g.st P).tcur < st'L.tcur) && (esL.g.st P).γ.isNone) = true
      · simp only [hc, ↓reduceIte]
        rw [runHM_bind, runHM_liftC_receive]
        split
        · rw [pure_bind, runHM_pure]; exact ⟨_, _, rfl⟩
        · cases cs.lastMsg with
          | none => rw [pure_bind, runHM_pure]; exact ⟨_, _, rfl⟩
          | some Tc =>
            rw [pure_bind]
            dsimp only
            by_cases h2 : (Mode.mk false tL tStar).tH + Δcka ≤ st'L.tcur
            · simp only [h2, ↓reduceIte]
              rw [runHM_bind, runHM_liftC_corr, pure_bind]
              split <;> (rw [runHM_pure]; exact ⟨_, _, rfl⟩)
            · simp only [h2, ↓reduceIte]
              rw [runHM_pure]; exact ⟨_, _, rfl⟩
      · simp only [hc, Bool.false_eq_true, ↓reduceIte]
        rw [runHM_pure]; exact ⟨_, _, rfl⟩
    rcases hdet0 with ⟨opt, cs1, hdet0⟩
    rw [hdet0, map_pure, pure_bind] at hcommL14
    cases opt with
    | none =>
      rw [runEM_abort_pure] at hcommL14
      injection hcommL14 with hpair
      injection (Prod.mk.inj hpair).1
    | some new' =>
      simp only [runEM_pure] at hcommL14
      injection hcommL14 with hpair
      rcases Prod.mk.inj hpair with ⟨hs1, hcs1⟩
      have hcs_eq : cs1 = cs' := congrArg Prod.snd hcs1
      subst hcs_eq
      exact ⟨new', hdet0, Option.some.inj hs1.symm⟩
  rcases hdet with ⟨new', hdet, hs1L_form⟩
  have hcommLU :
      runEM (CKA.oracleImpl cka Δcka (healEpoch tL))
        (commitE (hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩) esL.g P (esL.g.st P) st'L pos)
        (esL, cs) = pure (some s₁L, (esL, cs')) := by
    unfold commitE
    rw [runEM_bind, runEM_liftH,
      runHM_commit_hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩
        (esL.g.accept P st'L pos) P (esL.g.st P) st'L esL.h cs]
    dsimp only
    rw [hdet]
    rcases esL with ⟨gL, ⟨h1, h2⟩, abL⟩
    simp [hs1L_form, runEM_pure]
  have hcommRU :
      runEM (PRFPRNG.oracleImpl prng)
        (commitE (hooksPRNG cka prng fs ⟨false, tL, tStar⟩) esR.g P (esR.g.st P) st'R pos)
        (esR, ps) = pure (some s₁R, (esR, ps)) := by
    have hs1R : s₁R = esR.g.accept P st'R pos := by
      unfold commitE hooksPRNG at hcommR14
      dsimp only [patchES] at hcommR14
      simp only [runEM_bind, runEM_liftH, runHM_pure, map_pure, pure_bind, runEM_pure,
        accept_update_st] at hcommR14
      injection hcommR14 with hpair
      exact Option.some.inj (Prod.mk.inj hpair).1.symm
    subst hs1R
    unfold commitE hooksPRNG
    simp [runEM_bind, runEM_liftH, runHM_pure, runEM_pure, accept_update_st]
  have hep_acc : s₁L.epoch = (esL.g.accept P st'L pos).epoch := by
    rw [hs1L_form]
  refine ⟨s₁L, s₁R, cs', hcommLU, hcommRU, ?_, hb, ?_, hcache⟩
  · rcases hr with ⟨hle, hst_tcur, hst_root, _, _⟩ |
      ⟨ht_step, _, _, _, _, _, _, _, _, _, _, hepO, _, _, _, _⟩
    · dsimp only [projL] at hle hst_tcur hst_root
      have hnotlt : ¬((esL.g.st P).tcur < st'L.tcur) := by
        have := (hs14.2.2.2.2.1 P).2.2.1
        dsimp only [projL] at this; omega
      have hnew_eq : new' = st'L := by
        dsimp only [hooksCKA] at hdet
        simp only [hnotlt, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
          runHM_pure] at hdet
        injection hdet with h1
        rcases Prod.mk.inj h1 with ⟨h2, _⟩
        rcases Prod.mk.inj h2 with ⟨h3, _⟩
        exact Option.some.inj h3.symm
      have hs1L_eq : s₁L = esL.g.accept P st'L pos := by
        rw [hs1L_form, hnew_eq, accept_update_st]
      have hroot_all : ∀ R, (s₁L.st R).root = (esL.g.st R).root := by
        intro R
        rw [hs1L_eq]
        simp only [SM.GameState.accept, SM.GameState.delete]
        by_cases hRP : R = P
        · rw [hRP]; simp [Function.update_self, hst_root]
        · simp [Function.update_of_ne hRP]
      have hpatch_eq :
          (patchES prng tStar { esL with g := s₁L } { esR with g := s₁R }).h =
          (patchES prng tStar esL esR).h := by
        dsimp only [patchES]
        congr 1; funext e
        by_cases het : e = tStar
        · subst het; simp [hroot_all]
        · simp [het]
      dsimp only [projL] at hs14' ⊢
      change Sync prng Δcka tL tStar ({ g := s₁L, h := esL.h.1, abort := esL.abort }, cs')
        ({ g := s₁R, h := (patchES prng tStar { esL with g := s₁L } { esR with g := s₁R }).h,
           abort := esR.abort }, { ps with b := false })
      rw [hpatch_eq]
      exact hs14'
    · have hep_both : ∀ R, s₁L.epoch R = esL.g.epoch P + 1 := by
        intro R
        rw [hep_acc]
        simp only [SM.GameState.accept, SM.GameState.delete]
        dsimp only [projL] at ht_step hepO
        by_cases hRP : R = P
        · rw [hRP]; simp [Function.update_self, ht_step]
        · have hRo : R = P.other := by cases P <;> cases R <;> simp at hRP ⊢
          rw [hRo]; simp [Function.update_of_ne (Party.other_ne P), hepO]
      exact sync_congr_cache_tStar prng Δcka
        (esL := { g := s₁L, h := esL.h.1, abort := esL.abort })
        (esR := { g := s₁R, h := (patchES prng tStar esL esR).h, abort := esR.abort })
        (hR' := (patchES prng tStar { esL with g := s₁L } { esR with g := s₁R }).h)
        hs14'
        (fun e he => by simp [patchES, he])
        (fun hnone => by
          dsimp only [patchES] at hnone ⊢
          simp only [↓reduceIte] at hnone ⊢
          cases hx : esR.h.cache tStar with
          | none => rfl
          | some val =>
            rcases val with ⟨Tc', σopt', k'⟩
            cases hy : esL.h.1.cache tStar <;> simp [hx, hy] at hnone)
        (fun Q t0 _ h1 h2 => by
          rw [hep_both Q] at h1
          rw [hep_both Q.other] at h2
          omega)
  · intro hlt
    dsimp only at hlt
    apply hpre
    have hep_le : ∀ R, esL.g.epoch R ≤ s₁L.epoch R := by
      intro R
      rw [hep_acc]
      simp only [SM.GameState.accept, SM.GameState.delete]
      by_cases hRP : R = P
      · rw [hRP]; simp [Function.update_self]
      · simp [Function.update_of_ne hRP]
    have hA := hep_le .A
    have hB := hep_le .B
    omega

private theorem runEM_deliverE_syncU (maxSkip : ℕ) (cfg : Config M)
    (tL : Option ℕ) (tStar : ℕ) (q : Party × (Header T × E))
    (esL : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAUState T I K))
    (cs : CKA.GameState Γ T)
    (esR : EState (PartyState Γ T (Option Sig) SS RS) M (Header T × E) (PRNGState T Sig K))
    (ps : PRFPRNG.GameState Sig I K)
    (hs : SyncU prng Δcka tL tStar (esL, cs) (esR, ps)) :
    ∃ out sL' sR',
      runEM (CKA.oracleImpl cka Δcka (healEpoch tL))
        (deliverE (hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩) maxSkip cfg q) (esL, cs) =
        pure (out, sL') ∧
      runEM (PRFPRNG.oracleImpl prng)
        (deliverE (hooksPRNG cka prng fs ⟨false, tL, tStar⟩) maxSkip cfg q) (esR, ps) =
        pure (out, sR') ∧
      SyncU prng Δcka tL tStar sL' sR' := by
  rcases q with ⟨P, c⟩
  have habL : esL.abort = false := hs.1.1
  have habR : esR.abort = false := hs.1.2.1
  have he : eraseSt esL.g = eraseSt esR.g := hs.1.2.2.1
  have hinv : GameInv esL.g := hs.1.2.2.2.1
  have hwin : esR.g.win = esL.g.win := (eraseSt_win he).symm
  have htr_eq : esR.g.inTransit P.other c = esL.g.inTransit P.other c :=
    (eraseSt_inTransit he P.other c).symm
  unfold deliverE
  dsimp only
  rw [runEM_bind, runEM_get, runEM_bind, runEM_get]
  simp only [pure_bind]
  rw [habL, habR, hwin]
  by_cases hw : (false || esL.g.win) = true
  · refine ⟨none, (esL, cs), (esR, ps), ?_, ?_, hs⟩ <;> simp [hw, runEM_pure]
  · simp only [hw, Bool.false_eq_true, ↓reduceIte]
    rw [htr_eq]
    cases htr : esL.g.inTransit P.other c with
    | none =>
      refine ⟨none, (esL, cs), (esR, ps), ?_, ?_, hs⟩ <;> simp [runEM_pure]
    | some r =>
      dsimp only
      have hmust_eq : esR.g.mustBeCorrect maxSkip P r = esL.g.mustBeCorrect maxSkip P r :=
        (eraseSt_mustBeCorrect he maxSkip P r).symm
      rw [runEM_bind, runEM_liftH, runEM_bind, runEM_liftH]
      rcases runHM_vRecv_syncU cka prng fs Δcka tL tStar P c (some r) esL cs esR ps hs with
        ⟨hL, hR⟩ | ⟨st'L, st'R, i, m, hL, hR, hstep⟩
      · rw [hL, hR]
        simp only [map_pure, pure_bind]
        rw [hmust_eq]
        by_cases hmust : (cfg.deliverWin && esL.g.mustBeCorrect maxSkip P r) = true
        · refine ⟨some .rejected, ({ esL with g := { esL.g with win := true } }, cs),
            ({ esR with g := { esR.g with win := true } }, ps), ?_, ?_, hs.set_win⟩ <;>
            simp [hmust, runEM_map_modify]
        · refine ⟨some .rejected, (esL, cs), (esR, ps), ?_, ?_, hs⟩ <;>
            simp [hmust, runEM_pure]
      · rw [hL, hR]
        simp only [map_pure, pure_bind]
        have hr_ep : r.pos.epoch = c.1.1 := hinv.inTransit_epoch htr
        have hstep' : RecvStep cka Δcka tL tStar (projL esL) (patchES prng tStar esL esR)
            cs P r.pos.epoch st'L st'R := hr_ep ▸ hstep
        rcases runEM_commitE_syncU cka prng fs Δcka tL tStar P r.pos st'L st'R esL cs esR ps hs hstep' with
          ⟨g'L, g'R, cs', hcommL, hcommR, hs'⟩
        rw [runEM_bind, hcommL, runEM_bind, hcommR]
        simp only [pure_bind]
        rw [hmust_eq]
        have hchall_eq : esR.g.chall = esL.g.chall := (eraseSt_chall he).symm
        rw [hchall_eq]
        set bad := (cfg.deliverWin && esL.g.mustBeCorrect maxSkip P r) &&
          !(decide ((c.1.1, i, m) = (r.pos.epoch, r.pos.idx, r.msg)))
        by_cases hbad : bad = true
        · refine ⟨some (.accepted c.1.1 i (if esL.g.chall.contains r.pos then none else some m)),
            ({ esL with g := { g'L with win := true } }, cs'),
            ({ esR with g := { g'R with win := true } }, ps), ?_, ?_, hs'.set_win⟩ <;>
            simp [bad, hbad, runEM_map_modify]
        · refine ⟨some (.accepted c.1.1 i (if esL.g.chall.contains r.pos then none else some m)),
            ({ esL with g := g'L }, cs'), ({ esR with g := g'R }, ps), ?_, ?_, hs'⟩ <;>
            simp [bad, hbad, runEM_map_modify]

private theorem runEM_injectE_syncU (cfg : Config M)
    (tL : Option ℕ) (tStar : ℕ) (q : Party × (Header T × E))
    (esL : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAUState T I K))
    (cs : CKA.GameState Γ T)
    (esR : EState (PartyState Γ T (Option Sig) SS RS) M (Header T × E) (PRNGState T Sig K))
    (ps : PRFPRNG.GameState Sig I K)
    (hs : SyncU prng Δcka tL tStar (esL, cs) (esR, ps)) :
    ∃ out sL' sR',
      runEM (CKA.oracleImpl cka Δcka (healEpoch tL))
        (injectE (hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩) (2 + Δcka) qep cfg q) (esL, cs) =
        pure (out, sL') ∧
      runEM (PRFPRNG.oracleImpl prng)
        (injectE (hooksPRNG cka prng fs ⟨false, tL, tStar⟩) (2 + Δcka) qep cfg q) (esR, ps) =
        pure (out, sR') ∧
      SyncU prng Δcka tL tStar sL' sR' := by
  rcases q with ⟨P, c⟩
  have habL : esL.abort = false := hs.1.1
  have habR : esR.abort = false := hs.1.2.1
  have he : eraseSt esL.g = eraseSt esR.g := hs.1.2.2.1
  have hwin : esR.g.win = esL.g.win := (eraseSt_win he).symm
  have htr_eq : esR.g.inTransit P.other c = esL.g.inTransit P.other c :=
    (eraseSt_inTransit he P.other c).symm
  have hsafe_eq : esR.g.safeInj (2 + Δcka) = esL.g.safeInj (2 + Δcka) :=
    (eraseSt_safeInj he (2 + Δcka)).symm
  unfold injectE
  dsimp only
  rw [runEM_bind, runEM_get, runEM_bind, runEM_get]
  simp only [pure_bind]
  rw [habL, habR, hwin, htr_eq, hsafe_eq]
  by_cases hg : ((false || esL.g.win || (esL.g.inTransit P.other c).isSome) ||
      !esL.g.safeInj (2 + Δcka)) = true
  · refine ⟨none, (esL, cs), (esR, ps), ?_, ?_, hs⟩ <;>
      (rw [ite_bool_true hg]; exact runEM_pure _ _ _)
  · simp only [hg, Bool.false_eq_true, ↓reduceIte]
    rw [runEM_bind, runEM_liftH, runEM_bind, runEM_liftH]
    rcases runHM_vRecv_syncU cka prng fs Δcka tL tStar P c none esL cs esR ps hs with
      ⟨hL, hR⟩ | ⟨st'L, st'R, i, m, hL, hR, hstep⟩
    · rw [hL, hR]
      refine ⟨some .rejected, (esL, cs), (esR, ps), ?_, ?_, hs⟩ <;>
        simp [map_pure, pure_bind, runEM_pure]
    · rw [hL, hR]
      simp only [map_pure, pure_bind]
      by_cases hqep : qep + 1 < c.1.1
      · refine ⟨some .rejected, (esL, cs), (esR, ps), ?_, ?_, hs⟩ <;>
          simp [hqep, runEM_pure]
      · simp only [hqep, ↓reduceIte]
        set pos : Pos := ⟨P.other, c.1.1, i⟩
        have htriv_eq : esR.g.trivial (2 + Δcka) pos = esL.g.trivial (2 + Δcka) pos :=
          (eraseSt_trivial he (2 + Δcka) pos).symm
        rw [htriv_eq]
        by_cases htriv : esL.g.trivial (2 + Δcka) pos = true
        · simp only [htriv, ↓reduceIte]
          rcases runEM_commitE_syncU cka prng fs Δcka tL tStar P pos st'L st'R esL cs esR ps hs hstep with
            ⟨g'L, g'R, cs', hcommL, hcommR, hs'⟩
          rw [runEM_bind, hcommL, runEM_bind, hcommR]
          refine ⟨some (.accepted c.1.1 i (some m)),
            ({ esL with g := g'L }, cs'), ({ esR with g := g'R }, ps), ?_, ?_, hs'⟩ <;>
            simp [pure_bind, runEM_map_modify]
        · simp only [htriv, Bool.false_eq_true, ↓reduceIte]
          by_cases hfull : cfg.injectFull c.1.1 = true
          · refine ⟨some .rejected, ({ esL with g := { esL.g with win := true } }, cs),
              ({ esR with g := { esR.g with win := true } }, ps), ?_, ?_, hs.set_win⟩ <;>
              simp [hfull, runEM_map_modify]
          · refine ⟨some .rejected, (esL, cs), (esR, ps), ?_, ?_, hs⟩ <;>
              simp [hfull, runEM_pure]

private theorem runHM_cacheCU
    {oimpl : QueryImpl (CKA.spec Γ CCoins T I) (StateT (CKA.GameState Γ T) ProbComp)}
    (t : ℕ) (x : T × I) (h : CKAUState T I K) (cs : CKA.GameState Γ T) :
    runHM oimpl (cacheCU t x) h cs =
      pure (((), ({ cache := Function.update h.1.cache t (some x) }, h.2)), cs) := by
  simp [cacheCU, runHM_modify]

private theorem runHM_liftP_challPrf_true (Ik : I) (h : PRNGState T Sig K)
    (ps : PRFPRNG.GameState Sig I K) (hb : ps.b = true) (htbl : ps.table = [])
    (hcorr : ps.corr = false) (hprng : ps.prng = false) :
    runHM (PRFPRNG.oracleImpl prng) (liftP (PRFPRNG.challPrfQuery Ik)) h ps =
      (($ᵗ K : ProbComp K) >>= fun kU =>
        pure ((some ((prng.up ps.σ Ik).1, kU), h),
          { ps with prf := true, table := [(Ik, kU)] })) := by
  simp [runHM, liftP, PRFPRNG.challPrfQuery, outerFull, PRFPRNG.oracleImpl,
    PRFPRNG.challPrfImpl, StateT.run_lift, simulateQ_query, hb, htbl, hcorr, hprng]

private theorem runHM_liftP_challPrng_none_true (h : PRNGState T Sig K)
    (ps : PRFPRNG.GameState Sig I K) (hb : ps.b = true) (hprf : ps.prf = false) :
    runHM (PRFPRNG.oracleImpl prng) (liftP (PRFPRNG.challPrngQuery none)) h ps =
      (($ᵗ I : ProbComp I) >>= fun Ir =>
        ($ᵗ K : ProbComp K) >>= fun kU =>
          pure ((some kU, h),
            { ps with σ := (prng.up ps.σ Ir).1, corr := false, prng := true })) := by
  simp [runHM, liftP, PRFPRNG.challPrngQuery, outerFull, PRFPRNG.oracleImpl,
    PRFPRNG.challPrngImpl, PRFPRNG.samIfNec, StateT.run_lift, simulateQ_query,
    hb, hprf]

private theorem runHM_rootPRNG_ne_tStar {tL : Option ℕ} {tStar t : ℕ} {Ik : I}
    {σ : Sig} {σv : Option Sig} (h : PRNGState T Sig K) (ps : PRFPRNG.GameState Sig I K)
    (hne : t ≠ tStar) (hb : ps.b = true)
    (hσv : tStar < t →
      σv = (if decide (tStar ≤ t - 1) || (tL.isSome && decide (t - 1 < healEpoch tL))
            then some σ else none))
    (ht0 : 0 < t → (t - 1 < tStar →
      ps.table = [] ∧ ps.prf = false ∧ ps.prng = false ∧
      ps.corr = (tL.isSome && decide (t - 1 < healEpoch tL)) ∧ ps.σ = σ))
    (hz : t = 0 →
      ps.table = [] ∧ ps.prf = false ∧ ps.prng = false ∧ ps.corr = false ∧ ps.σ = σ)
    (hnotH : ¬(tL.isSome = true ∧ t = healEpoch tL)) :
    ∃ ps',
      runHM (PRFPRNG.oracleImpl prng) (rootPRNG prng ⟨false, tL, tStar⟩ t Ik σv) h ps =
        pure ((some (if decide (tStar ≤ t) || (tL.isSome && decide (t < healEpoch tL))
                     then some (prng.up σ Ik).1 else none,
                   (prng.up σ Ik).2), h), ps') ∧
      ps'.b = true ∧
      (t < tStar →
        ps'.table = [] ∧ ps'.prf = false ∧ ps'.prng = false ∧
        ps'.corr = (tL.isSome && decide (t < healEpoch tL)) ∧
        ps'.σ = (prng.up σ Ik).1) := by
  unfold rootPRNG
  by_cases hgt : tStar < t
  · have hle1 : decide (tStar ≤ t - 1) = true := decide_eq_true (by omega)
    have hle2 : decide (tStar ≤ t) = true := decide_eq_true (by omega)
    simp only [hgt, ↓reduceIte, hσv hgt, hle1, Bool.true_or, hle2, runHM_pure]
    exact ⟨ps, rfl, hb, fun hlt => absurd hlt (by omega)⟩
  · have hlt : t < tStar := by omega
    have hcond : ((⟨false, tL, tStar⟩ : Mode).tL.isSome &&
        decide (t = (⟨false, tL, tStar⟩ : Mode).tH)) = false := by
      simp only [Bool.and_eq_false_imp]
      intro h1
      exact decide_eq_false (fun h2 => hnotH ⟨h1, h2⟩)
    simp only [hgt, hne, ↓reduceIte, hcond, Bool.false_eq_true]
    have hps : ps.table = [] ∧ ps.prf = false ∧ ps.prng = false ∧ ps.σ = σ := by
      by_cases hpos : 0 < t
      · rcases ht0 hpos (by omega) with ⟨htbl, hprf, hprng, _, hσ⟩
        exact ⟨htbl, hprf, hprng, hσ⟩
      · rcases hz (by omega) with ⟨htbl, hprf, hprng, _, hσ⟩
        exact ⟨htbl, hprf, hprng, hσ⟩
    rcases hps with ⟨htbl, hprf, hprng, hσ⟩
    have hnotle : decide (tStar ≤ t) = false := decide_eq_false (by omega)
    by_cases hltH : tL.isSome = true ∧ t < healEpoch tL
    · have hcond2 : ((⟨false, tL, tStar⟩ : Mode).tL.isSome &&
          decide (t < (⟨false, tL, tStar⟩ : Mode).tH)) = true := by
        simp [Mode.tH, hltH.1, hltH.2]
      simp only [hcond2, ↓reduceIte]
      rw [runHM_processCorr_some prng Ik h ps hprf, hσ]
      refine ⟨{ ps with σ := (prng.up σ Ik).1, corr := true }, ?_, hb, fun _ => ?_⟩
      · simp [hnotle, hltH.1, hltH.2]
      · refine ⟨htbl, hprf, hprng, ?_, rfl⟩
        simp [hltH.1, hltH.2]
    · have hcond2 : ((⟨false, tL, tStar⟩ : Mode).tL.isSome &&
          decide (t < (⟨false, tL, tStar⟩ : Mode).tH)) = false := by
        simp only [Bool.and_eq_false_imp]
        intro h1
        exact decide_eq_false (fun h2 => hltH ⟨h1, h2⟩)
      simp only [hcond2, Bool.false_eq_true, ↓reduceIte]
      rw [runHM_bind, runHM_liftP_process_some prng Ik h ps hprf, pure_bind]
      dsimp only
      rw [hσ, runHM_pure]
      have hfalse : (tL.isSome && decide (t < healEpoch tL)) = false := by
        cases htL : tL.isSome
        · rfl
        · simp only [Bool.true_and, decide_eq_false_iff_not]
          exact fun h => hltH ⟨htL, h⟩
      refine ⟨{ ps with σ := (prng.up σ Ik).1, corr := ps.corr }, ?_, hb, fun _ => ?_⟩
      · simp [hnotle, hfalse]
      · refine ⟨htbl, hprf, hprng, ?_, rfl⟩
        rw [hfalse]
        by_cases hpos : 0 < t
        · rw [(ht0 hpos (by omega)).2.2.2.1]
          cases htL : tL.isSome
          · rfl
          · simp only [Bool.true_and]
            have hneH : t ≠ healEpoch tL := fun h => hnotH ⟨htL, h⟩
            have hnotlt : ¬(t < healEpoch tL) := fun h => hltH ⟨htL, h⟩
            exact decide_eq_false (by omega)
        · exact (hz (by omega)).2.2.2.1

private theorem runHM_rootPRNG_heal_lt {tL : Option ℕ} {tStar t : ℕ} {Ik : I} {σ : Sig}
    {σv : Option Sig} (h : PRNGState T Sig K) (ps : PRFPRNG.GameState Sig I K)
    (hlt : t < tStar) (htL : tL.isSome = true) (htH : t = healEpoch tL)
    (hps : ps.b = true ∧ ps.table = [] ∧ ps.prf = false ∧ ps.prng = false ∧ ps.σ = σ) :
    ∃ ps' : I → PRFPRNG.GameState Sig I K,
      runHM (PRFPRNG.oracleImpl prng) (rootPRNG prng ⟨false, tL, tStar⟩ t Ik σv) h ps =
        (fun Ir =>
          let p := prng.up σ Ir
          ((some (if decide (tStar ≤ t) || (tL.isSome && decide (t < healEpoch tL))
                  then some p.1 else none, p.2), h), ps' Ir)) <$> ($ᵗ I : ProbComp I) ∧
      (∀ Ir, (ps' Ir).b = true ∧
        (ps' Ir).table = [] ∧ (ps' Ir).prf = false ∧ (ps' Ir).prng = false ∧
        (ps' Ir).corr = (tL.isSome && decide (t < healEpoch tL)) ∧
        (ps' Ir).σ = (prng.up σ Ir).1) := by
  rcases hps with ⟨hb, htbl, hprf, hprng, hσ⟩
  have hng : ¬(tStar < t) := by omega
  have hne : t ≠ tStar := by omega
  have hcond : ((⟨false, tL, tStar⟩ : Mode).tL.isSome &&
      decide (t = (⟨false, tL, tStar⟩ : Mode).tH)) = true := by
    simp [Mode.tH, htL, htH]
  unfold rootPRNG
  simp only [hng, hne, ↓reduceIte, hcond]
  rw [runHM_bind, runHM_liftP_process_none prng h ps hprf]
  have hnotle : decide (tStar ≤ t) = false := decide_eq_false (by omega)
  have hnotltH : decide (t < healEpoch tL) = false := decide_eq_false (by omega)
  refine ⟨fun Ir => { ps with σ := (prng.up σ Ir).1, corr := false }, ?_, fun Ir => ?_⟩
  · simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
    refine bind_congr fun Ir => ?_
    simp [runHM_pure, hσ, hnotle, hnotltH]
  · simp [hb, htbl, hprf, hprng, hnotltH]

private theorem runHM_rootPRNG_eq_tStar_notH {tL : Option ℕ} {tStar : ℕ} {Ik : I} {σ : Sig}
    {σv : Option Sig} (h : PRNGState T Sig K) (ps : PRFPRNG.GameState Sig I K)
    (hnotH : ¬(tL.isSome = true ∧ tStar = healEpoch tL))
    (hps : ps.b = true ∧ ps.table = [] ∧ ps.prf = false ∧ ps.prng = false ∧
      ps.corr = false ∧ ps.σ = σ) :
    runHM (PRFPRNG.oracleImpl prng) (rootPRNG prng ⟨false, tL, tStar⟩ tStar Ik σv) h ps =
      (($ᵗ K : ProbComp K) >>= fun kU =>
        pure ((some (if decide (tStar ≤ tStar) || (tL.isSome && decide (tStar < healEpoch tL))
                     then some (prng.up σ Ik).1 else none, kU), h),
          { ps with prf := true, table := [(Ik, kU)] })) := by
  rcases hps with ⟨hb, htbl, hprf, hprng, hcorr, hσ⟩
  have hcond : ((⟨false, tL, tStar⟩ : Mode).tL.isSome &&
      decide (tStar = (⟨false, tL, tStar⟩ : Mode).tH)) = false := by
    simp only [Bool.and_eq_false_imp]
    intro h1
    exact decide_eq_false (fun h2 => hnotH ⟨h1, h2⟩)
  unfold rootPRNG
  simp only [lt_irrefl, ↓reduceIte, hcond, Bool.false_eq_true]
  rw [runHM_bind, runHM_liftP_challPrf_true prng Ik h ps hb htbl hcorr hprng, bind_assoc]
  refine bind_congr fun kU => ?_
  rw [pure_bind]
  dsimp only
  rw [runHM_pure]
  simp [hσ]

private theorem runHM_rootPRNG_eq_tStar_heal {tL : Option ℕ} {tStar : ℕ} {Ik : I} {σ : Sig}
    {σv : Option Sig} (h : PRNGState T Sig K) (ps : PRFPRNG.GameState Sig I K)
    (htL : tL.isSome = true) (htH : tStar = healEpoch tL)
    (hps : ps.b = true ∧ ps.prf = false ∧ ps.σ = σ) :
    runHM (PRFPRNG.oracleImpl prng) (rootPRNG prng ⟨false, tL, tStar⟩ tStar Ik σv) h ps =
      (($ᵗ I : ProbComp I) >>= fun Ir =>
        ($ᵗ K : ProbComp K) >>= fun kU =>
          pure ((some (if decide (tStar ≤ tStar) || (tL.isSome && decide (tStar < healEpoch tL))
                       then some (prng.up σ Ir).1 else none, kU), h),
            { ps with σ := (prng.up σ Ir).1, corr := true, prng := true })) := by
  rcases hps with ⟨hb, hprf, hσ⟩
  have hcond : ((⟨false, tL, tStar⟩ : Mode).tL.isSome &&
      decide (tStar = (⟨false, tL, tStar⟩ : Mode).tH)) = true := by
    simp [Mode.tH, htL, htH]
  unfold rootPRNG
  simp only [lt_irrefl, ↓reduceIte, hcond]
  rw [runHM_bind, runHM_liftP_challPrng_none_true prng h ps hb hprf]
  simp only [bind_assoc]
  refine bind_congr fun Ir => bind_congr fun kU => ?_
  rw [pure_bind]
  dsimp only
  rw [runHM_bind,
    runHM_liftP_corr prng h { ps with σ := (prng.up ps.σ Ir).1, corr := false, prng := true } hprf,
    pure_bind]
  dsimp only
  rw [runHM_pure]
  simp [hσ]

private theorem syncU_after_same_send
    (tL : Option ℕ) (tStar : ℕ) (P : Party) (m : M) (isChall : Bool)
    (esL : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAUState T I K))
    (cs : CKA.GameState Γ T)
    (esR : EState (PartyState Γ T (Option Sig) SS RS) M (Header T × E) (PRNGState T Sig K))
    (ps : PRFPRNG.GameState Sig I K)
    (hs : SyncU prng Δcka tL tStar (esL, cs) (esR, ps)) :
    let h : Header T := (esL.g.epoch P, (esL.g.st P).curCkaMsg)
    let stcL : PartyState (Option Γ) T Sig SS RS × (Header T × E) := match (esL.g.st P).vS with
      | none => (esL.g.st P, (h, default))
      | some v =>
        let fsOut := fs.send v h m
        ({ esL.g.st P with vS := some fsOut.1 }, (h, fsOut.2))
    let stcR : PartyState Γ T (Option Sig) SS RS × (Header T × E) := match (esL.g.st P).vS with
      | none => (esR.g.st P, (h, default))
      | some v =>
        let fsOut := fs.send v h m
        ({ esR.g.st P with vS := some fsOut.1 }, (h, fsOut.2))
    let recL : Record M (Header T × E) := ⟨⟨P, esL.g.epoch P, esL.g.idx P + 1⟩, m, stcL.2⟩
    SyncU prng Δcka tL tStar
      ({ esL with g := esL.g.record (2 + Δcka) P stcL.1 recL isChall }, cs)
      ({ esR with g := esR.g.record (2 + Δcka) P stcR.1 recL isChall }, ps) := by
  intro h stcL stcR recL
  rcases hs with ⟨hs14, hb, hpre, hcache⟩
  have hs14' := sync_after_same_send prng fs Δcka tL tStar P m isChall
    (projL esL) cs (patchES prng tStar esL esR) { ps with b := false } hs14
  dsimp only [projL] at hs14'
  have hrootL : stcL.1.root = (esL.g.st P).root := by
    dsimp [stcL]; cases (esL.g.st P).vS <;> rfl
  have hroot_all : ∀ Q, ((esL.g.record (2 + Δcka) P stcL.1 recL isChall).st Q).root =
      (esL.g.st Q).root := by
    intro Q
    by_cases hQP : Q = P
    · rw [hQP]; simp [SM.GameState.record, hrootL]
    · simp [SM.GameState.record, hQP]
  have hpatch_eq :
      (patchES prng tStar
        { esL with g := esL.g.record (2 + Δcka) P stcL.1 recL isChall }
        { esR with g := esR.g.record (2 + Δcka) P stcR.1 recL isChall }).h =
      (patchES prng tStar esL esR).h := by
    dsimp only [patchES]
    congr 1; funext e
    by_cases het : e = tStar
    · subst het; simp [hroot_all]
    · simp [het]
  refine ⟨?_, hb, hpre, hcache⟩
  dsimp only [projL]
  change Sync prng Δcka tL tStar
    ({ g := esL.g.record (2 + Δcka) P stcL.1 recL isChall, h := esL.h.1, abort := esL.abort }, cs)
    ({ g := esR.g.record (2 + Δcka) P stcR.1 recL isChall,
       h := (patchES prng tStar
         { esL with g := esL.g.record (2 + Δcka) P stcL.1 recL isChall }
         { esR with g := esR.g.record (2 + Δcka) P stcR.1 recL isChall }).h,
       abort := esR.abort }, { ps with b := false })
  rw [hpatch_eq]
  exact hs14'

private theorem syncU_after_new_send
    (tL : Option ℕ) (tStar : ℕ) (P : Party) (m : M) (bad isChall : Bool)
    (coins : CCoins) (Ik : I) (kEpoch : K) (kOpt1 : Option K)
    (s₁L : Ctx (Option Γ) T Sig SS RS M E)
    (s₁R : Ctx Γ T (Option Sig) SS RS M E)
    (esL : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAUState T I K))
    (cs : CKA.GameState Γ T)
    (esR : EState (PartyState Γ T (Option Sig) SS RS) M (Header T × E) (PRNGState T Sig K))
    (ps ps' : PRFPRNG.GameState Sig I K)
    (hs : SyncU prng Δcka tL tStar (esL, cs) (esR, ps))
    (hsends : P.sendsIn (esL.g.epoch P + 1) = true)
    (hepL : esL.g.epMgmt (2 + Δcka) qep P bad = some s₁L)
    (hepR : esR.g.epMgmt (2 + Δcka) qep P bad = some s₁R)
    (hb' : ps'.b = true)
    (hps' : esL.g.epoch P + 1 < tStar →
      ps'.table = [] ∧ ps'.prf = false ∧ ps'.prng = false ∧
      ps'.corr = (tL.isSome && decide (esL.g.epoch P + 1 < healEpoch tL)) ∧
      ps'.σ = (prng.up (esL.g.st P).root Ik).1)
    (hkOpt_eq : esL.g.epoch P + 1 = tStar → kOpt1 = some kEpoch)
    (hkOpt_ne : esL.g.epoch P + 1 ≠ tStar → kOpt1 = esL.h.2)
    (hkEp_ne : esL.g.epoch P + 1 ≠ tStar → kEpoch = (prng.up (esL.g.st P).root Ik).2) :
    let ep := esL.g.epoch P
    let c_cka := cka.send (esR.g.st P).γ coins
    let p := prng.up (esL.g.st P).root Ik
    let γ'L : Option Γ :=
      if tL.isNone || decide (healEpoch tL + Δcka ≤ ep + 1) then some c_cka.1 else none
    let σ'R : Option Sig :=
      if decide (tStar ≤ ep + 1) || (tL.isSome && decide (ep + 1 < healEpoch tL))
      then some p.1 else none
    let h : Header T := (ep + 1, some c_cka.2.1)
    let fsOut := fs.send (fs.initSender kEpoch) h m
    let st'L : PartyState (Option Γ) T Sig SS RS :=
      { s₁L.st P with tcur := ep + 1, γ := γ'L, curCkaMsg := some c_cka.2.1,
                      root := p.1, vS := some fsOut.1 }
    let st'R : PartyState Γ T (Option Sig) SS RS :=
      { s₁R.st P with tcur := ep + 1, γ := c_cka.1, curCkaMsg := some c_cka.2.1,
                      root := σ'R, vS := some fsOut.1 }
    let c := (h, fsOut.2)
    let recL : Record M (Header T × E) := ⟨⟨P, s₁L.epoch P, s₁L.idx P + 1⟩, m, c⟩
    let recR : Record M (Header T × E) := ⟨⟨P, s₁R.epoch P, s₁R.idx P + 1⟩, m, c⟩
    let h'L : CKAUState T I K :=
      ({ cache := Function.update esL.h.1.cache (ep + 1) (some (c_cka.2.1, Ik)) }, kOpt1)
    let h'R : PRNGState T Sig K :=
      { cache := Function.update esR.h.cache (ep + 1) (some (c_cka.2.1, σ'R, kEpoch)) }
    let cs' : CKA.GameState Γ T :=
      if tL.isNone || decide (healEpoch tL + Δcka ≤ ep) then cs
      else cs.afterSend P c_cka.1 c_cka.2.1
    SyncU prng Δcka tL tStar
      ({ esL with g := s₁L.record (2 + Δcka) P st'L recL isChall, h := h'L }, cs')
      ({ esR with g := s₁R.record (2 + Δcka) P st'R recR isChall, h := h'R }, ps') := by
  intro ep c_cka p γ'L σ'R h fsOut st'L st'R c recL recR h'L h'R cs'
  rcases hs with ⟨hs14, hb, hpre, hcache⟩
  dsimp only at hs14 hb hpre hcache
  rcases hs14 with ⟨habL, habR, he, hinv, hp, hcka, hpp, hprng⟩
  dsimp only [projL, patchES] at habL habR he hinv hp hcka hprng
  rcases eraseSt_epMgmt_some he hepL with ⟨s₁R', hepR', he₁, hst₁L, hst₁R⟩
  rw [hepR] at hepR'; injection hepR' with hepR'; subst hepR'
  have hs₁L_eq := epMgmt_sendsIn_true hsends hepL
  have hep₁L : s₁L.epoch = Function.update esL.g.epoch P (ep + 1) := by rw [hs₁L_eq]
  have hrec_eq : recR = recL := by
    dsimp [recL, recR]; rw [eraseSt_epoch he₁, eraseSt_idx he₁]
  have hrec_ep : recL.ct.1.1 = recL.pos.epoch := by
    dsimp [recL, c, h]; rw [hep₁L, Function.update_self]
  rcases hpp.synced_of_sendsIn hsends with ⟨hAB, hrootAB⟩
  dsimp only [projL] at hAB hrootAB
  have hep_other : esL.g.epoch P.other = ep := by cases P <;> dsimp [ep] <;> omega
  have hroot_other : (esL.g.st P.other).root = (esL.g.st P).root := by
    cases P <;> simp [Party.other, hrootAB]
  have hmax_new :
      max ((s₁L.record (2 + Δcka) P st'L recL isChall).epoch .A)
          ((s₁L.record (2 + Δcka) P st'L recL isChall).epoch .B) = ep + 1 := by
    simp only [SM.GameState.record, hep₁L]
    cases P <;> simp [Function.update, hAB, ep]
  refine ⟨⟨habL, habR,
    hrec_eq ▸ eraseSt_record he₁ (2 + Δcka) P st'L st'R recL isChall,
    (hinv.epMgmt hepL).record hrec_ep, ?_, ?_, ?_, ?_⟩, hb', ?_, ?_⟩
  · intro Q
    dsimp [projL, patchES]
    by_cases hQP : Q = P
    · subst hQP
      simp only [SM.GameState.record, hep₁L, Function.update_self]
      rcases hp Q with ⟨hidL, hidR, _, _, _, hvR, _, _, _⟩
      dsimp [st'L, st'R]
      rw [hst₁L, hst₁R]
      exact ⟨hidL, hidR, rfl, rfl, rfl, hvR, rfl, rfl, rfl⟩
    · simp only [SM.GameState.record, hep₁L, Function.update_of_ne hQP, hst₁L, hst₁R]
      exact hp Q
  · refine ⟨?_, fun Q htL hQlt => ?_⟩
    · dsimp [cs']; split <;> exact hcka.1
    · simp only [projL, SM.GameState.record, hep₁L] at hQlt ⊢
      have hunh : ep < healEpoch tL + Δcka := by
        by_cases hQP : Q = P
        · subst hQP; simp only [Function.update_self] at hQlt; omega
        · simp only [Function.update_of_ne hQP] at hQlt
          have hQep : esL.g.epoch Q = ep := by cases P <;> cases Q <;> dsimp [ep] <;> omega
          omega
      have hcond : (tL.isNone || decide (healEpoch tL + Δcka ≤ ep)) = false := by
        cases tL with
        | none => simp at htL
        | some l => simp [decide_eq_false (by omega : ¬(healEpoch (some l) + Δcka ≤ ep))]
      have hcs' : cs' = cs.afterSend P c_cka.1 c_cka.2.1 := by dsimp [cs']; rw [hcond]; rfl
      rw [hcs']
      by_cases hQP : Q = P
      · subst hQP
        simp only [CKA.GameState.afterSend, Function.update_self, patchES]
        exact ⟨rfl, by rw [(hcka.2 Q htL hunh).2]⟩
      · simp only [CKA.GameState.afterSend, Function.update_of_ne hQP, patchES, hst₁R] at hQlt ⊢
        exact hcka.2 Q htL hQlt
  · refine ⟨fun t' ht' => ?_, Or.inr ⟨P, ep, c_cka.2.1, Ik, hsends, ?_, ?_, ?_, ?_, ?_⟩⟩
    · dsimp only [projL] at ht' ⊢
      rw [hmax_new] at ht'
      have hne : t' ≠ ep + 1 := by omega
      have hpp1 := hpp.1 t' (by dsimp [projL]; cases P <;> simp [hAB, ep] at ht' ⊢ <;> omega)
      dsimp only [projL, patchES] at hpp1
      rcases hpp1 with ⟨hcL_t', hcR_t'⟩
      have hcL_new : h'L.1.cache t' = none := by
        dsimp [h'L]; rw [Function.update_of_ne hne]; exact hcL_t'
      refine ⟨hcL_new, ?_⟩
      dsimp only [patchES, h'R]
      rw [Function.update_of_ne hne]
      by_cases het : t' = tStar
      · subst het
        simp only [↓reduceIte, hcL_t'] at hcR_t'
        simp only [↓reduceIte, hcL_new]
        rcases hx : esR.h.cache t' with _ | ⟨Tc0, σopt0, k0⟩ <;> simp [hx] at hcR_t' ⊢
      · simp only [het, ↓reduceIte] at hcR_t' ⊢
        exact hcR_t'
    · simp [projL, SM.GameState.record, hep₁L]
    · simp [projL, SM.GameState.record, hep₁L, Party.other_ne, hep_other]
    · dsimp [projL, h'L]; rw [Function.update_self]
    · dsimp [projL, patchES, h'R, h'L, st'L, p, σ'R, ep]
      refine ⟨?_, ?_⟩
      · by_cases het : esL.g.epoch P + 1 = tStar
        · simp only [het, ↓reduceIte, Function.update_self]
          rw [senderOf_eq_of_sendsIn (het ▸ hsends)]
          simp [SM.GameState.record, hst₁L, Function.update_of_ne (Party.other_ne P), hroot_other]
        · simp [het, Function.update_self, hkEp_ne het, SM.GameState.record, hst₁L,
            Function.update_of_ne (Party.other_ne P), hroot_other]
      · simp [SM.GameState.record, Function.update_self, Function.update_of_ne (Party.other_ne P),
          hst₁L, hroot_other]
    · intro htL hunh
      have hcond : (tL.isNone || decide (healEpoch tL + Δcka ≤ ep)) = false := by
        cases tL with
        | none => simp at htL
        | some l => simp [decide_eq_false (by omega : ¬(healEpoch (some l) + Δcka ≤ ep))]
      have hcs' : cs' = cs.afterSend P c_cka.1 c_cka.2.1 := by dsimp [cs']; rw [hcond]; rfl
      rw [hcs']
      simp [CKA.GameState.afterSend, (hcka.2 P htL hunh).2, ep]
  · unfold PRNGRel
    dsimp [projL, patchES]
    simp only [hmax_new]
    intro hlt
    rw [senderOf_eq_of_sendsIn hsends]
    simp only [SM.GameState.record, Function.update_self]
    rcases hps' hlt with ⟨_, hprf, hprng1, hcorr, hσ⟩
    exact ⟨trivial, hprf, hprng1, hcorr, hσ⟩
  · intro hlt
    dsimp [h'L] at hlt ⊢
    rw [hmax_new] at hlt
    refine ⟨(hps' hlt).1, ?_⟩
    rw [hkOpt_ne (by omega)]
    have hmax_old : max (esL.g.epoch .A) (esL.g.epoch .B) < tStar := by
      dsimp [ep] at hlt; cases P <;> simp [hAB] at hlt ⊢ <;> omega
    exact (hpre hmax_old).2
  · intro Tc0 σopt0 k0 hc
    dsimp [h'L, h'R] at hc ⊢
    by_cases het : tStar = ep + 1
    · rw [het, Function.update_self] at hc
      injection hc with hval
      rcases Prod.mk.inj (Prod.mk.inj hval).2 with ⟨_, rfl⟩
      exact hkOpt_eq het.symm
    · rw [Function.update_of_ne het] at hc
      rw [hkOpt_ne (Ne.symm het)]
      exact hcache Tc0 σopt0 k0 hc

private theorem runHM_hooksCKAU_some_some
    (tL : Option ℕ) (tStar : ℕ) (ctx : Ctx (Option Γ) T Sig SS RS M E)
    (P : Party) (ep : ℕ) (γ : Γ) (σ : Sig) (coins : CCoins)
    (h : CKAUState T I K) (cs : CKA.GameState Γ T) :
    runHM (CKA.oracleImpl cka Δcka (healEpoch tL))
      ((hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩).startSend ctx P (ep + 1) (some γ) σ (some coins))
      h cs =
    let c := cka.send γ coins
    let p := prng.up σ c.2.2
    if ep + 1 = tStar then
      ($ᵗ K : ProbComp K) >>= fun kU =>
        pure ((some (some c.1, c.2.1, p.1, fs.initSender kU),
          ({ cache := Function.update h.1.cache (ep + 1) (some (c.2.1, c.2.2)) }, some kU)), cs)
    else
      pure ((some (some c.1, c.2.1, p.1, fs.initSender p.2),
        ({ cache := Function.update h.1.cache (ep + 1) (some (c.2.1, c.2.2)) }, h.2)), cs) := by
  dsimp only [hooksCKAU]
  rw [runHM_bind, runHM_get, pure_bind]
  dsimp only
  rw [runHM_bind, runHM_pure, pure_bind]
  dsimp only
  rw [runHM_bind, runHM_cacheCU, pure_bind]
  dsimp only
  by_cases het : ep + 1 = tStar
  · simp only [het, ↓reduceIte]
    rw [runHM_bind, runHM_sampleT, bind_map_left]
    refine bind_congr fun kU => ?_
    dsimp only
    rw [runHM_bind, runHM_pure, pure_bind]
    dsimp only
    rw [runHM_bind, runHM_modify, pure_bind, runHM_pure]
  · simp only [het, ↓reduceIte]
    rw [runHM_bind, runHM_pure, pure_bind]
    dsimp only
    rw [runHM_bind, runHM_modify, pure_bind, runHM_pure]

private theorem runHM_hooksCKAU_some_none
    (tL : Option ℕ) (tStar : ℕ) (ctx : Ctx (Option Γ) T Sig SS RS M E)
    (P : Party) (ep : ℕ) (γ : Γ) (σ : Sig)
    (h : CKAUState T I K) (cs : CKA.GameState Γ T) :
    runHM (CKA.oracleImpl cka Δcka (healEpoch tL))
      ((hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩).startSend ctx P (ep + 1) (some γ) σ none)
      h cs =
    (($ᵗ CCoins : ProbComp CCoins) >>= fun coins =>
      let c := cka.send γ coins
      let p := prng.up σ c.2.2
      if ep + 1 = tStar then
        ($ᵗ K : ProbComp K) >>= fun kU =>
          pure ((some (some c.1, c.2.1, p.1, fs.initSender kU),
            ({ cache := Function.update h.1.cache (ep + 1) (some (c.2.1, c.2.2)) }, some kU)), cs)
      else
        pure ((some (some c.1, c.2.1, p.1, fs.initSender p.2),
          ({ cache := Function.update h.1.cache (ep + 1) (some (c.2.1, c.2.2)) }, h.2)), cs)) := by
  dsimp only [hooksCKAU]
  rw [runHM_bind, runHM_get, pure_bind]
  dsimp only
  rw [runHM_bind, runHM_sampleT, bind_map_left]
  refine bind_congr fun coins => ?_
  dsimp only
  rw [runHM_bind, runHM_cacheCU, pure_bind]
  dsimp only
  by_cases het : ep + 1 = tStar
  · simp only [het, ↓reduceIte]
    rw [runHM_bind, runHM_sampleT, bind_map_left]
    refine bind_congr fun kU => ?_
    dsimp only
    rw [runHM_bind, runHM_pure, pure_bind]
    dsimp only
    rw [runHM_bind, runHM_modify, pure_bind, runHM_pure]
  · simp only [het, ↓reduceIte]
    rw [runHM_bind, runHM_pure, pure_bind]
    dsimp only
    rw [runHM_bind, runHM_modify, pure_bind, runHM_pure]

private theorem runHM_hooksCKAU_corrStep
    (tL : Option ℕ) (tStar : ℕ) (P : Party) (ep : ℕ) (γ' : Γ) (T' : T) (σ' : Sig)
    (kEpoch : K) (h1 : CKAState T I) (kOpt1 : Option K) (cs : CKA.GameState Γ T)
    (htL : tL.isNone = false) (hcsep : cs.epoch P = ep) :
    runHM (CKA.oracleImpl cka Δcka (healEpoch tL))
      (if (⟨false, tL, tStar⟩ : Mode).tH + Δcka ≤ ep + 1 then
        StateT.lift (CKA.corrQuery P) >>= fun x =>
          match x with
          | none => pure none
          | some γ0 => pure (some (some γ0, T', σ', fs.initSender kEpoch))
       else pure (some (none, T', σ', fs.initSender kEpoch)))
      (h1, kOpt1) (cs.afterSend P γ' T') =
    pure ((some (if tL.isNone || decide (healEpoch tL + Δcka ≤ ep + 1) then some γ' else none,
      T', σ', fs.initSender kEpoch), (h1, kOpt1)), cs.afterSend P γ' T') := by
  by_cases hfin : healEpoch tL + Δcka ≤ ep + 1
  · have hfin' : (⟨false, tL, tStar⟩ : Mode).tH + Δcka ≤ ep + 1 := hfin
    simp only [hfin', ↓reduceIte]
    rw [runHM_bind, runHM_lift_state2, show (StateT.lift (CKA.corrQuery P) :
      Engine.HM (CKA.spec Γ CCoins T I) (CKAState T I) _) = liftC (CKA.corrQuery P) from rfl,
      runHM_liftC_corr, map_pure, pure_bind]
    simp [CKA.GameState.finished, CKA.GameState.afterSend, hcsep, hfin, runHM_pure]
  · have hfin' : ¬((⟨false, tL, tStar⟩ : Mode).tH + Δcka ≤ ep + 1) := hfin
    simp [hfin', htL, hfin, runHM_pure]

private theorem runHM_hooksCKAU_none_some
    (tL : Option ℕ) (tStar : ℕ) (ctx : Ctx (Option Γ) T Sig SS RS M E)
    (P : Party) (ep : ℕ) (γ : Γ) (σ : Sig) (coins : CCoins)
    (h : CKAUState T I K) (cs : CKA.GameState Γ T)
    (htL : tL.isNone = false) (hcanSend : cs.canSend P = true)
    (hallow : decide (cs.epoch P + 1 + 2 ≤ healEpoch tL) = true)
    (hcsep : cs.epoch P = ep) (hcsst : cs.st P = γ) :
    runHM (CKA.oracleImpl cka Δcka (healEpoch tL))
      ((hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩).startSend ctx P (ep + 1) none σ (some coins))
      h cs =
    let c := cka.send γ coins
    let p := prng.up σ c.2.2
    let γ'L := if tL.isNone || decide (healEpoch tL + Δcka ≤ ep + 1) then some c.1 else none
    if ep + 1 = tStar then
      ($ᵗ K : ProbComp K) >>= fun kU =>
        pure ((some (γ'L, c.2.1, p.1, fs.initSender kU),
          ({ cache := Function.update h.1.cache (ep + 1) (some (c.2.1, c.2.2)) }, some kU)),
          cs.afterSend P c.1 c.2.1)
    else
      pure ((some (γ'L, c.2.1, p.1, fs.initSender p.2),
        ({ cache := Function.update h.1.cache (ep + 1) (some (c.2.1, c.2.2)) }, h.2)),
        cs.afterSend P c.1 c.2.1) := by
  dsimp only [hooksCKAU]
  rw [runHM_bind, runHM_get, pure_bind]
  dsimp only
  rw [runHM_bind, runHM_lift_state2, show (StateT.lift (CKA.sendWithAdversaryCoinsQuery P coins) :
    Engine.HM (CKA.spec Γ CCoins T I) (CKAState T I) _) =
    liftC (CKA.sendWithAdversaryCoinsQuery P coins) from rfl, runHM_liftC_sendBad]
  simp only [hcanSend, Bool.not_true, hallow, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
    hcsst, map_pure, pure_bind]
  rw [runHM_bind, runHM_cacheCU, pure_bind]
  dsimp only
  by_cases het : ep + 1 = tStar
  · simp only [het, ↓reduceIte]
    rw [runHM_bind, runHM_sampleT, bind_map_left]
    refine bind_congr fun kU => ?_
    dsimp only
    rw [runHM_bind, runHM_modify, pure_bind]
    have hstep := runHM_hooksCKAU_corrStep cka fs Δcka tL tStar P ep
      (cka.send γ coins).1 (cka.send γ coins).2.1 (prng.up σ (cka.send γ coins).2.2).1 kU
      { cache := Function.update h.1.cache (ep + 1) (some ((cka.send γ coins).2.1, (cka.send γ coins).2.2)) }
      (some kU) cs htL hcsep
    rw [het] at hstep
    exact hstep
  · simp only [het, ↓reduceIte]
    rw [runHM_bind, runHM_modify, pure_bind]
    exact runHM_hooksCKAU_corrStep cka fs Δcka tL tStar P ep
      (cka.send γ coins).1 (cka.send γ coins).2.1 (prng.up σ (cka.send γ coins).2.2).1
      (prng.up σ (cka.send γ coins).2.2).2
      { cache := Function.update h.1.cache (ep + 1) (some ((cka.send γ coins).2.1, (cka.send γ coins).2.2)) }
      h.2 cs htL hcsep

private theorem runHM_hooksCKAU_none_heal
    (tL : Option ℕ) (tStar : ℕ) (ctx : Ctx (Option Γ) T Sig SS RS M E)
    (P : Party) (ep : ℕ) (γ : Γ) (σ : Sig)
    (h : CKAUState T I K) (cs : CKA.GameState Γ T)
    (htL : tL.isNone = false) (hcanSend : cs.canSend P = true)
    (heqH : ep + 1 = healEpoch tL) (hcsb : cs.b = true)
    (hcsep : cs.epoch P = ep) (hcsst : cs.st P = γ) :
    runHM (CKA.oracleImpl cka Δcka (healEpoch tL))
      ((hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩).startSend ctx P (ep + 1) none σ none)
      h cs =
    (($ᵗ CCoins : ProbComp CCoins) >>= fun coins =>
      ($ᵗ I : ProbComp I) >>= fun Ir =>
      let c := cka.send γ coins
      let p := prng.up σ Ir
      let γ'L := if tL.isNone || decide (healEpoch tL + Δcka ≤ ep + 1) then some c.1 else none
      if ep + 1 = tStar then
        ($ᵗ K : ProbComp K) >>= fun kU =>
          pure ((some (γ'L, c.2.1, p.1, fs.initSender kU),
            ({ cache := Function.update h.1.cache (ep + 1) (some (c.2.1, Ir)) }, some kU)),
            cs.afterSend P c.1 c.2.1)
      else
        pure ((some (γ'L, c.2.1, p.1, fs.initSender p.2),
          ({ cache := Function.update h.1.cache (ep + 1) (some (c.2.1, Ir)) }, h.2)),
          cs.afterSend P c.1 c.2.1)) := by
  have hcs_eqH : (cs.epoch P + 1 != healEpoch tL) = false := by rw [hcsep]; simp [heqH]
  have hiteH : ∀ {α : Type} (x y : α),
      (if ep + 1 = (⟨false, tL, tStar⟩ : Mode).tH then x else y) = x := by
    intro α x y; change (if ep + 1 = healEpoch tL then x else y) = x; split <;> [rfl; contradiction]
  dsimp only [hooksCKAU]
  rw [runHM_bind, runHM_get, pure_bind]
  dsimp only
  rw [hiteH, runHM_bind, runHM_lift_state2, show (StateT.lift (CKA.challQuery P) :
    Engine.HM (CKA.spec Γ CCoins T I) (CKAState T I) _) = liftC (CKA.challQuery P) from rfl,
    runHM_liftC_chall cka Δcka (healEpoch tL) P h.1 cs hcsb]
  simp only [hcanSend, Bool.not_true, hcs_eqH, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
    hcsst, map_bind, map_pure, bind_assoc, pure_bind]
  refine bind_congr fun coins => bind_congr fun Ir => ?_
  rw [runHM_bind, runHM_cacheCU, pure_bind]
  dsimp only
  by_cases het : ep + 1 = tStar
  · simp only [het, ↓reduceIte]
    rw [runHM_bind, runHM_sampleT, bind_map_left]
    refine bind_congr fun kU => ?_
    dsimp only
    rw [runHM_bind, runHM_modify, pure_bind]
    have hstep := runHM_hooksCKAU_corrStep cka fs Δcka tL tStar P ep
      (cka.send γ coins).1 (cka.send γ coins).2.1 (prng.up σ Ir).1 kU
      { cache := Function.update h.1.cache (ep + 1) (some ((cka.send γ coins).2.1, Ir)) }
      (some kU) cs htL hcsep
    rw [het] at hstep
    exact hstep
  · simp only [het, ↓reduceIte]
    rw [runHM_bind, runHM_modify, pure_bind]
    exact runHM_hooksCKAU_corrStep cka fs Δcka tL tStar P ep
      (cka.send γ coins).1 (cka.send γ coins).2.1 (prng.up σ Ir).1 (prng.up σ Ir).2
      { cache := Function.update h.1.cache (ep + 1) (some ((cka.send γ coins).2.1, Ir)) }
      h.2 cs htL hcsep

private theorem runHM_hooksCKAU_none_send
    (tL : Option ℕ) (tStar : ℕ) (ctx : Ctx (Option Γ) T Sig SS RS M E)
    (P : Party) (ep : ℕ) (γ : Γ) (σ : Sig)
    (h : CKAUState T I K) (cs : CKA.GameState Γ T)
    (htL : tL.isNone = false) (hcanSend : cs.canSend P = true)
    (hneH : ep + 1 ≠ healEpoch tL)
    (hcsep : cs.epoch P = ep) (hcsst : cs.st P = γ) :
    runHM (CKA.oracleImpl cka Δcka (healEpoch tL))
      ((hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩).startSend ctx P (ep + 1) none σ none)
      h cs =
    (($ᵗ CCoins : ProbComp CCoins) >>= fun coins =>
      let c := cka.send γ coins
      let p := prng.up σ c.2.2
      let γ'L := if tL.isNone || decide (healEpoch tL + Δcka ≤ ep + 1) then some c.1 else none
      if ep + 1 = tStar then
        ($ᵗ K : ProbComp K) >>= fun kU =>
          pure ((some (γ'L, c.2.1, p.1, fs.initSender kU),
            ({ cache := Function.update h.1.cache (ep + 1) (some (c.2.1, c.2.2)) }, some kU)),
            cs.afterSend P c.1 c.2.1)
      else
        pure ((some (γ'L, c.2.1, p.1, fs.initSender p.2),
          ({ cache := Function.update h.1.cache (ep + 1) (some (c.2.1, c.2.2)) }, h.2)),
          cs.afterSend P c.1 c.2.1)) := by
  have hcs_neH : (cs.epoch P + 1 == healEpoch tL) = false := by
    rw [hcsep]; exact beq_eq_false_iff_ne.mpr hneH
  have hiteH : ∀ {α : Type} (x y : α),
      (if ep + 1 = (⟨false, tL, tStar⟩ : Mode).tH then x else y) = y := by
    intro α x y; change (if ep + 1 = healEpoch tL then x else y) = y; split <;> [contradiction; rfl]
  dsimp only [hooksCKAU]
  rw [runHM_bind, runHM_get, pure_bind]
  dsimp only
  rw [hiteH, runHM_bind, runHM_lift_state2, show (StateT.lift (CKA.sendQuery P) :
    Engine.HM (CKA.spec Γ CCoins T I) (CKAState T I) _) = liftC (CKA.sendQuery P) from rfl,
    runHM_liftC_send cka Δcka (healEpoch tL) P h.1 cs]
  simp only [hcanSend, Bool.not_true, hcs_neH, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
    hcsst, map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
  refine bind_congr fun coins => ?_
  rw [runHM_bind, runHM_cacheCU, pure_bind]
  dsimp only
  by_cases het : ep + 1 = tStar
  · simp only [het, ↓reduceIte]
    rw [runHM_bind, runHM_sampleT, bind_map_left]
    refine bind_congr fun kU => ?_
    dsimp only
    rw [runHM_bind, runHM_modify, pure_bind]
    have hstep := runHM_hooksCKAU_corrStep cka fs Δcka tL tStar P ep
      (cka.send γ coins).1 (cka.send γ coins).2.1 (prng.up σ (cka.send γ coins).2.2).1 kU
      { cache := Function.update h.1.cache (ep + 1) (some ((cka.send γ coins).2.1, (cka.send γ coins).2.2)) }
      (some kU) cs htL hcsep
    rw [het] at hstep
    exact hstep
  · simp only [het, ↓reduceIte]
    rw [runHM_bind, runHM_modify, pure_bind]
    exact runHM_hooksCKAU_corrStep cka fs Δcka tL tStar P ep
      (cka.send γ coins).1 (cka.send γ coins).2.1 (prng.up σ (cka.send γ coins).2.2).1
      (prng.up σ (cka.send γ coins).2.2).2
      { cache := Function.update h.1.cache (ep + 1) (some ((cka.send γ coins).2.1, (cka.send γ coins).2.2)) }
      h.2 cs htL hcsep

private theorem runHM_hooksPRNG_none (mo : Mode) (ctx : Ctx Γ T (Option Sig) SS RS M E)
    (P : Party) (t : ℕ) (γ : Γ) (σv : Option Sig) (h : PRNGState T Sig K)
    (ps : PRFPRNG.GameState Sig I K) :
    runHM (PRFPRNG.oracleImpl prng)
      ((hooksPRNG cka prng fs mo).startSend ctx P t γ σv none) h ps =
    (($ᵗ CCoins : ProbComp CCoins) >>= fun coins =>
      runHM (PRFPRNG.oracleImpl prng)
        ((hooksPRNG cka prng fs mo).startSend ctx P t γ σv (some coins)) h ps) := by
  dsimp only [hooksPRNG]
  rw [runHM_bind, runHM_sampleT, bind_map_left]
  refine bind_congr fun coins => ?_
  dsimp only
  symm
  rw [runHM_bind, runHM_pure, pure_bind]

private theorem prng_pre_of_syncU_sendsIn {tL : Option ℕ} {tStar : ℕ} {P : Party}
    {esL : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAUState T I K)}
    {cs : CKA.GameState Γ T}
    {esR : EState (PartyState Γ T (Option Sig) SS RS) M (Header T × E) (PRNGState T Sig K)}
    {ps : PRFPRNG.GameState Sig I K}
    (hs : SyncU prng Δcka tL tStar (esL, cs) (esR, ps))
    (hsends : P.sendsIn (esL.g.epoch P + 1) = true) :
    ((esR.g.st P).root =
      if decide (tStar ≤ esL.g.epoch P) || (tL.isSome && decide (esL.g.epoch P < healEpoch tL))
      then some (esL.g.st P).root else none) ∧
    ps.b = true ∧
    (esL.g.epoch P < tStar →
      ps.table = [] ∧ ps.prf = false ∧ ps.prng = false ∧
      ps.corr = (tL.isSome && decide (esL.g.epoch P < healEpoch tL)) ∧
      ps.σ = (esL.g.st P).root) := by
  rcases hs with ⟨hs14, hb, hpre, _⟩
  rcases prng_pre_of_sync_sendsIn hs14 hsends with ⟨hroot_pre, hps_pre⟩
  dsimp only [projL, patchES] at hroot_pre hps_pre
  rcases hs14.2.2.2.2.2.2.1.synced_of_sendsIn hsends with ⟨hAB, _⟩
  dsimp only [projL] at hAB
  refine ⟨hroot_pre, hb, fun hlt => ?_⟩
  rcases hps_pre hlt with ⟨_, hprf, hprng1, hcorr, hσ⟩
  have hmax : max (esL.g.epoch .A) (esL.g.epoch .B) < tStar := by
    cases P <;> simp [hAB] at hlt ⊢ <;> omega
  exact ⟨(hpre hmax).1, hprf, hprng1, hcorr, hσ⟩

private def sendPost {Γv Sv HS OS : Type} (Δ : ℕ) (s₁ : Ctx Γv T Sv SS RS M E)
    (P : Party) (ep : ℕ) (m : M) (isChall : Bool)
    (es : EState (PartyState Γv T Sv SS RS) M (Header T × E) HS)
    (res : (Option (Γv × T × Sv × SS) × HS) × OS) :
    ProbComp (Option (Header T × E) ×
      (EState (PartyState Γv T Sv SS RS) M (Header T × E) HS × OS)) :=
  match res.1.1 with
  | none => pure (none, ({ es with h := res.1.2, abort := true }, res.2))
  | some (γ', T', σ', ss) =>
    let h : Header T := (ep + 1, some T')
    let fsOut := fs.send ss h m
    let st' : PartyState Γv T Sv SS RS :=
      { es.g.st P with tcur := ep + 1, γ := γ', curCkaMsg := some T',
                       root := σ', vS := some fsOut.1 }
    let ct := (h, fsOut.2)
    let rcd : Record M (Header T × E) := ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, ct⟩
    pure (some ct, ({ es with g := s₁.record Δ P st' rcd isChall, h := res.1.2 }, res.2))

private theorem runEM_sendCore_eq_sendPost {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {OS Γv Sv HS : Type} (oimpl : QueryImpl tspec (StateT OS ProbComp))
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SS RS)
    (hfs : ∀ ctx P t ss h m pair, hk.fsSend ctx P t ss h m pair = pure (some (fs.send ss h m)))
    (Δ : ℕ) (s₁ : Ctx Γv T Sv SS RS M E) (P : Party) (m : M)
    (pair : Option (M × M)) (r : Option CCoins) (isChall : Bool)
    (es : EState (PartyState Γv T Sv SS RS) M (Header T × E) HS) (os : OS)
    (hst : s₁.st = es.g.st) (htcur : (es.g.st P).tcur = es.g.epoch P)
    (hsends : (s₁.st P).id.sendsIn ((s₁.st P).tcur + 1) = true) :
    runEM oimpl (sendCore hk Δ s₁ P m pair r isChall) (es, os) =
      runHM oimpl (hk.startSend s₁ P (es.g.epoch P + 1) (es.g.st P).γ (es.g.st P).root r) es.h os >>=
        sendPost fs Δ s₁ P (es.g.epoch P) m isChall es := by
  rw [runEM_sendCore_sendsIn_true oimpl hk fs hfs Δ s₁ P m pair r isChall es os hsends]
  simp only [hst, htcur]
  refine bind_congr fun res => ?_
  rcases res with ⟨⟨_ | ⟨γ', T', σ', ss⟩, h'⟩, os'⟩ <;> simp [sendPost]

private theorem sendCore_step_knownU (tL : Option ℕ) (tStar : ℕ) (b : Bool)
    (P : Party) (m : M) (bad isChall : Bool) (coins : CCoins)
    (s₁L : Ctx (Option Γ) T Sig SS RS M E) (s₁R : Ctx Γ T (Option Sig) SS RS M E)
    (esL : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAUState T I K))
    (cs : CKA.GameState Γ T)
    (esR : EState (PartyState Γ T (Option Sig) SS RS) M (Header T × E) (PRNGState T Sig K))
    (ps : PRFPRNG.GameState Sig I K)
    (k : Option (Header T × E) →
      OracleComp (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) Bool)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) tL tStar = true)
    (hs : SyncU prng Δcka tL tStar (esL, cs) (esR, ps))
    (hsends : P.sendsIn (esL.g.epoch P + 1) = true)
    (hepL : esL.g.epMgmt (2 + Δcka) qep P bad = some s₁L)
    (hepR : esR.g.epMgmt (2 + Δcka) qep P bad = some s₁R)
    (hst₁L : s₁L.st = esL.g.st) (hst₁R : s₁R.st = esR.g.st)
    (hnotH : ¬(tL.isSome = true ∧ esL.g.epoch P + 1 = healEpoch tL))
    (ih : ∀ r sL' sR', SyncU prng Δcka tL tStar sL' sR' →
      DEq (evalEng (CKA.oracleImpl cka Δcka (healEpoch tL))
            (hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩)
            (2 + Δcka) qep fs.maxSkip (Config.priv tStar) ⟨false, tL, tStar⟩ b (k r) sL')
          (evalEng (PRFPRNG.oracleImpl prng)
            (hooksPRNG cka prng fs ⟨false, tL, tStar⟩)
            (2 + Δcka) qep fs.maxSkip (Config.priv tStar) ⟨false, tL, tStar⟩ b (k r) sR')) :
    let ep := esL.g.epoch P
    let c := cka.send (esR.g.st P).γ coins
    let p := prng.up (esL.g.st P).root c.2.2
    let γ'L : Option Γ :=
      if tL.isNone || decide (healEpoch tL + Δcka ≤ ep + 1) then some c.1 else none
    let cs' : CKA.GameState Γ T :=
      if tL.isNone || decide (healEpoch tL + Δcka ≤ ep) then cs
      else cs.afterSend P c.1 c.2.1
    DEq ((if ep + 1 = tStar then
            ($ᵗ K : ProbComp K) >>= fun kU =>
              pure ((some (γ'L, c.2.1, p.1, fs.initSender kU),
                ({ esL.h.1 with cache := Function.update esL.h.1.cache (ep + 1) (some (c.2.1, c.2.2)) }, some kU)), cs')
          else
            pure ((some (γ'L, c.2.1, p.1, fs.initSender p.2),
              ({ esL.h.1 with cache := Function.update esL.h.1.cache (ep + 1) (some (c.2.1, c.2.2)) }, esL.h.2)), cs')) >>=
          fun x => sendPost fs (2 + Δcka) s₁L P ep m isChall esL x >>=
            fun r => evalEng (CKA.oracleImpl cka Δcka (healEpoch tL))
              (hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩)
              (2 + Δcka) qep fs.maxSkip (Config.priv tStar) ⟨false, tL, tStar⟩ b (k r.1) r.2)
        (runHM (PRFPRNG.oracleImpl prng)
          ((hooksPRNG cka prng fs ⟨false, tL, tStar⟩).startSend s₁R P (ep + 1)
            (esR.g.st P).γ (esR.g.st P).root (some coins)) esR.h ps >>=
          fun x => sendPost fs (2 + Δcka) s₁R P ep m isChall esR x >>=
            fun r => evalEng (PRFPRNG.oracleImpl prng)
              (hooksPRNG cka prng fs ⟨false, tL, tStar⟩)
              (2 + Δcka) qep fs.maxSkip (Config.priv tStar) ⟨false, tL, tStar⟩ b (k r.1) r.2) := by
  intro ep c p γ'L cs'
  conv =>
    rhs; enter [1]
    dsimp only [hooksPRNG]
    rw [runHM_bind, runHM_pure, pure_bind]
    dsimp only
  rcases prng_pre_of_syncU_sendsIn prng Δcka hs hsends with ⟨hroot_pre, hb, hps_pre⟩
  by_cases het : ep + 1 = tStar
  · simp only [het, ↓reduceIte, bind_assoc, pure_bind]
    have hlt : ep < tStar := by omega
    rcases hps_pre hlt with ⟨htbl, hprf, hprng1, hcorr, hσ⟩
    have hcorrF : ps.corr = false := by
      rw [hcorr]
      rcases validGuess_healed hvg with hnone | ⟨l, rfl, _, hvh⟩
      · simp [hnone]
      · have hneH : tStar ≠ healEpoch (some l) := fun h => hnotH ⟨rfl, het.trans h⟩
        simp only [Option.isSome_some, Bool.true_and, decide_eq_false_iff_not]; omega
    rw [runHM_bind, runHM_rootPRNG_eq_tStar_notH prng esR.h ps (fun h => hnotH ⟨h.1, het.trans h.2⟩)
      ⟨hb, htbl, hprf, hprng1, hcorrF, hσ⟩]
    simp only [bind_assoc, pure_bind, runHM_bind, runHM_modify, runHM_pure, sendPost]
    refine DEq.bind_right ($ᵗ K) fun kU => ?_
    have hsync' := syncU_after_new_send cka prng fs Δcka qep tL tStar P m bad isChall
      coins c.2.2 kU (some kU) s₁L s₁R esL cs esR ps { ps with prf := true, table := [(c.2.2, kU)] }
      hs hsends hepL hepR hb (fun hlt' => absurd hlt' (by omega))
      (fun _ => rfl) (fun hne => absurd het hne) (fun hne => absurd het hne)
    dsimp only [ep, c, p, γ'L, cs'] at het ⊢
    simp only [het, hst₁L, hst₁R] at hsync' ⊢
    exact ih _ _ _ hsync'
  · simp only [het, ↓reduceIte, pure_bind]
    rcases runHM_rootPRNG_ne_tStar prng esR.h ps het hb
      (fun _ => hroot_pre) (fun _ => hps_pre)
      (by omega) hnotH (Ik := c.2.2) with ⟨ps', hroot_run, hb', hps'⟩
    rw [runHM_bind, hroot_run, pure_bind]
    dsimp only
    rw [runHM_bind, runHM_modify, pure_bind, runHM_pure]
    simp only [pure_bind, sendPost]
    have hsync' := syncU_after_new_send cka prng fs Δcka qep tL tStar P m bad isChall
      coins c.2.2 p.2 esL.h.2 s₁L s₁R esL cs esR ps ps'
      hs hsends hepL hepR hb' hps'
      (fun heq => absurd heq het) (fun _ => rfl) (fun _ => rfl)
    simp only [hst₁L, hst₁R] at hsync' ⊢
    exact ih _ _ _ hsync'

private theorem evalEng_sendCore_syncU (tL : Option ℕ) (tStar : ℕ) (b : Bool)
    (P : Party) (m : M) (pair : Option (M × M)) (rcoins : Option CCoins) (isChall : Bool)
    (s₁L : Ctx (Option Γ) T Sig SS RS M E) (s₁R : Ctx Γ T (Option Sig) SS RS M E)
    (esL : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAUState T I K))
    (cs : CKA.GameState Γ T)
    (esR : EState (PartyState Γ T (Option Sig) SS RS) M (Header T × E) (PRNGState T Sig K))
    (ps : PRFPRNG.GameState Sig I K)
    (k : Option (Header T × E) →
      OracleComp (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) Bool)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) tL tStar = true)
    (hs : SyncU prng Δcka tL tStar (esL, cs) (esR, ps))
    (hepL : esL.g.epMgmt (2 + Δcka) qep P rcoins.isSome = some s₁L)
    (hepR : esR.g.epMgmt (2 + Δcka) qep P rcoins.isSome = some s₁R)
    (hld : Policy.leakDoom ⟨false, tL, tStar⟩ esL.g s₁L = false)
    (ih : ∀ r sL' sR', SyncU prng Δcka tL tStar sL' sR' →
      DEq (evalEng (CKA.oracleImpl cka Δcka (healEpoch tL))
            (hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩)
            (2 + Δcka) qep fs.maxSkip (Config.priv tStar) ⟨false, tL, tStar⟩ b (k r) sL')
          (evalEng (PRFPRNG.oracleImpl prng)
            (hooksPRNG cka prng fs ⟨false, tL, tStar⟩)
            (2 + Δcka) qep fs.maxSkip (Config.priv tStar) ⟨false, tL, tStar⟩ b (k r) sR')) :
    DEq (runEM (CKA.oracleImpl cka Δcka (healEpoch tL))
          (sendCore (hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩)
            (2 + Δcka) s₁L P m pair rcoins isChall) (esL, cs) >>=
          fun r => evalEng (CKA.oracleImpl cka Δcka (healEpoch tL))
            (hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩)
            (2 + Δcka) qep fs.maxSkip (Config.priv tStar) ⟨false, tL, tStar⟩ b (k r.1) r.2)
        (runEM (PRFPRNG.oracleImpl prng)
          (sendCore (hooksPRNG cka prng fs ⟨false, tL, tStar⟩)
            (2 + Δcka) s₁R P m pair rcoins isChall) (esR, ps) >>=
          fun r => evalEng (PRFPRNG.oracleImpl prng)
            (hooksPRNG cka prng fs ⟨false, tL, tStar⟩)
            (2 + Δcka) qep fs.maxSkip (Config.priv tStar) ⟨false, tL, tStar⟩ b (k r.1) r.2) := by
  rcases hs with ⟨hs14, hb, hpre, hcache⟩
  have hs : SyncU prng Δcka tL tStar (esL, cs) (esR, ps) := ⟨hs14, hb, hpre, hcache⟩
  rcases hs14 with ⟨habL, habR, he, hinv, hp, hcka, hpp, hprng⟩
  dsimp [projL, patchES] at habL habR he hinv hp hcka hprng
  rcases eraseSt_epMgmt_some he hepL with ⟨s₁R', hepR', he₁, hst₁L, hst₁R⟩
  rw [hepR] at hepR'; injection hepR' with hepR'; subst hepR'
  by_cases hmL : MissedTL tL s₁L
  · have hmR : MissedTL tL s₁R := eraseSt_missedTL he₁ hmL
    exact (evalEng_sendCore_of_missedTL _ _ (2 + Δcka) qep fs.maxSkip (Config.priv tStar)
      ⟨false, tL, tStar⟩ b s₁L P m pair rcoins isChall k (esL, cs) hmL).trans
      (evalEng_sendCore_of_missedTL _ _ (2 + Δcka) qep fs.maxSkip (Config.priv tStar)
        ⟨false, tL, tStar⟩ b s₁R P m pair rcoins isChall k (esR, ps) hmR).symm
  · rcases hp P with ⟨hidL, hidR, htcurL, htcurR, hvS, hvR, hTcur, hγ, hroot⟩
    set ep := esL.g.epoch P
    have hfsL : ∀ ctx P t ss h m pair,
        (hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩).fsSend ctx P t ss h m pair =
          pure (some (fs.send ss h m)) := fun _ _ _ _ _ _ _ => rfl
    have hfsR : ∀ ctx P t ss h m pair,
        (hooksPRNG cka prng fs ⟨false, tL, tStar⟩).fsSend ctx P t ss h m pair =
          pure (some (fs.send ss h m)) := fun _ _ _ _ _ _ _ => rfl
    by_cases hsends : P.sendsIn (ep + 1) = true
    · have hsendsL : (s₁L.st P).id.sendsIn ((s₁L.st P).tcur + 1) = true := by
        rw [hst₁L, hidL, htcurL]; exact hsends
      have hsendsR : (s₁R.st P).id.sendsIn ((s₁R.st P).tcur + 1) = true := by
        rw [hst₁R, hidR, htcurR]; exact hsends
      have hepochR : esR.g.epoch P = esL.g.epoch P := (congrFun (eraseSt_epoch he) P).symm
      rw [runEM_sendCore_eq_sendPost fs _ _ hfsL _ s₁L P m pair rcoins isChall esL cs hst₁L htcurL hsendsL,
          runEM_sendCore_eq_sendPost fs _ _ hfsR _ s₁R P m pair rcoins isChall esR ps hst₁R
            (htcurR.trans hepochR.symm) hsendsR,
          hepochR]
      simp only [bind_assoc]
      rcases hpp.synced_of_sendsIn hsends with ⟨hAB, _⟩
      dsimp [projL] at hAB
      by_cases hloc : (tL.isNone || decide (healEpoch tL + Δcka ≤ ep)) = true
      · have hγ_some : (esL.g.st P).γ = some (esR.g.st P).γ := by rw [hγ, hloc]; rfl
        have hloc_next : (tL.isNone || decide (healEpoch tL + Δcka ≤ ep + 1)) = true := by
          rcases Bool.or_eq_true_iff.mp hloc with h1 | h2
          · simp [h1]
          · simp only [decide_eq_true_eq] at h2
            simp [decide_eq_true (by omega : healEpoch tL + Δcka ≤ ep + 1)]
        have hnotH : ¬(tL.isSome = true ∧ ep + 1 = healEpoch tL) := by
          rintro ⟨htL, heqH⟩
          rcases Bool.or_eq_true_iff.mp hloc with h1 | h2
          · cases tL <;> simp at h1 htL
          · simp only [decide_eq_true_eq] at h2; omega
        rw [hγ_some]
        cases rcoins with
        | some coins =>
          rw [runHM_hooksCKAU_some_some]
          have hstep := sendCore_step_knownU cka prng fs Δcka qep tL tStar b P m true isChall
            coins s₁L s₁R esL cs esR ps k hvg hs hsends hepL hepR hst₁L hst₁R hnotH ih
          dsimp only [ep] at hloc hloc_next ⊢
          simp only [hloc_next, hloc, ↓reduceIte] at hstep
          exact hstep
        | none =>
          rw [runHM_hooksCKAU_some_none, runHM_hooksPRNG_none]
          simp only [bind_assoc]
          refine DEq.bind_right ($ᵗ CCoins) fun coins => ?_
          have hstep := sendCore_step_knownU cka prng fs Δcka qep tL tStar b P m false isChall
            coins s₁L s₁R esL cs esR ps k hvg hs hsends hepL hepR hst₁L hst₁R hnotH ih
          dsimp only [ep] at hloc hloc_next ⊢
          simp only [hloc_next, hloc, ↓reduceIte] at hstep
          exact hstep
      · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_le] at hloc
        rcases hloc with ⟨htL_not_none, hunh⟩
        have htL_some : tL.isSome = true := by cases tL <;> simp at htL_not_none ⊢
        have htL_none_false : tL.isNone = false := by cases tL <;> simp at htL_not_none ⊢
        have hloc_false : (tL.isNone || decide (healEpoch tL + Δcka ≤ ep)) = false := by
          simp [htL_none_false, decide_eq_false (by omega : ¬(healEpoch tL + Δcka ≤ ep))]
        have hγ_none : (esL.g.st P).γ = none := by rw [hγ, hloc_false]; rfl
        rw [hγ_none]
        have hPO : esL.g.epoch P.other = ep := by cases P <;> dsimp [ep, Party.other] <;> omega
        have hunh_other : esL.g.epoch P.other < healEpoch tL + Δcka := by rw [hPO]; exact hunh
        rcases hcka.2 P htL_some hunh with ⟨hcs_stP, hcs_epP⟩
        rcases hcka.2 P.other htL_some hunh_other with ⟨_, hcs_epO⟩
        have hcanSend : cs.canSend P = true := by
          unfold CKA.GameState.canSend; rw [hcs_epP, hcs_epO]; simp [hPO, ep, hsends]
        cases rcoins with
        | some coins =>
          rcases Option.isSome_iff_exists.mp htL_some with ⟨l, htL_eq⟩
          by_cases hle_l : ep + 1 ≤ l
          · have hallow : decide (cs.epoch P + 1 + 2 ≤ healEpoch tL) = true := by
              rw [hcs_epP, htL_eq]; dsimp [healEpoch, ep]; exact decide_eq_true (by omega)
            have hnotH : ¬(tL.isSome = true ∧ ep + 1 = healEpoch tL) := by
              rw [htL_eq]; dsimp [healEpoch]; omega
            rw [runHM_hooksCKAU_none_some cka prng fs Δcka tL tStar s₁L P ep
              (esR.g.st P).γ (esL.g.st P).root coins esL.h cs
              htL_none_false hcanSend hallow hcs_epP hcs_stP]
            have hstep := sendCore_step_knownU cka prng fs Δcka qep tL tStar b P m true isChall
              coins s₁L s₁R esL cs esR ps k hvg hs hsends hepL hepR hst₁L hst₁R hnotH ih
            dsimp only [ep] at hloc_false ⊢
            simp only [hloc_false, Bool.false_eq_true, ↓reduceIte] at hstep
            exact hstep
          · have hlt_l : l < ep + 1 := by omega
            have hvh : healEpoch (some l) + Δcka ≤ tStar := by
              rcases validGuess_healed hvg with hnone | ⟨l', heq', _, hvh'⟩
              · rw [htL_eq] at hnone; contradiction
              · rw [htL_eq] at heq'; injection heq' with heq'; subst heq'
                rw [htL_eq] at hvh'; exact hvh'
            have hmL' : MissedTL tL s₁L := by
              subst htL_eq
              exact missedTL_of_bad_send hinv hAB hsends hepL hld hvh hunh hlt_l
            exact absurd hmL' hmL
        | none =>
          by_cases heqH : ep + 1 = healEpoch tL
          · have hep_lt_tStar : ep < tStar := by
              rcases validGuess_healed hvg with hnone | ⟨l, _, _, hvh⟩
              · rw [hnone] at htL_some; contradiction
              · omega
            rcases prng_pre_of_syncU_sendsIn prng Δcka hs hsends with ⟨_, hb0, hps_pre⟩
            rcases hps_pre hep_lt_tStar with ⟨htbl, hprf, hprng1, _, hσ⟩
            rw [runHM_hooksCKAU_none_heal cka prng fs Δcka tL tStar s₁L P ep
              (esR.g.st P).γ (esL.g.st P).root esL.h cs
              htL_none_false hcanSend heqH hcka.1 hcs_epP hcs_stP, runHM_hooksPRNG_none]
            simp only [bind_assoc]
            refine DEq.bind_right ($ᵗ CCoins) fun coins => ?_
            conv =>
              rhs; enter [1]
              dsimp only [hooksPRNG]
              rw [runHM_bind, runHM_pure, pure_bind]
              dsimp only
            dsimp only [ep] at heqH ⊢
            by_cases het : esL.g.epoch P + 1 = tStar
            · simp only [het, ↓reduceIte, bind_assoc, pure_bind]
              rw [runHM_bind, runHM_rootPRNG_eq_tStar_heal prng esR.h ps htL_some
                (het.symm.trans heqH) ⟨hb0, hprf, hσ⟩]
              simp only [pure_bind, runHM_bind, runHM_modify, runHM_pure, bind_assoc, sendPost]
              refine DEq.bind_right ($ᵗ I) fun Ir => DEq.bind_right ($ᵗ K) fun kU => ?_
              have hsync' := syncU_after_new_send cka prng fs Δcka qep tL tStar P m false isChall
                coins Ir kU (some kU) s₁L s₁R esL cs esR ps
                { ps with σ := (prng.up ps.σ Ir).1, corr := true, prng := true }
                hs hsends hepL hepR hb0 (fun hlt' => absurd hlt' (by omega))
                (fun _ => rfl) (fun hne => absurd het hne) (fun hne => absurd het hne)
              dsimp only [ep] at hloc_false ⊢
              simp only [het, hσ, hst₁L, hst₁R, hloc_false, Bool.false_eq_true, ↓reduceIte] at hsync' ⊢
              exact ih _ _ _ hsync'
            · have hlt_tStar : esL.g.epoch P + 1 < tStar := by
                rcases validGuess_healed hvg with hnone | ⟨l, _, _, hvh⟩
                · rw [hnone] at htL_some; contradiction
                · omega
              simp only [het, ↓reduceIte, pure_bind]
              rcases runHM_rootPRNG_heal_lt prng esR.h ps hlt_tStar htL_some heqH
                ⟨hb0, htbl, hprf, hprng1, hσ⟩
                (Ik := (cka.send (esR.g.st P).γ coins).2.2) (σv := (esR.g.st P).root) with
                ⟨ps', hroot_heal, hps'⟩
              rw [runHM_bind, hroot_heal, bind_map_left]
              simp only [bind_assoc, pure_bind, runHM_bind, runHM_modify, runHM_pure, sendPost]
              refine DEq.bind_right ($ᵗ I) fun Ir => ?_
              have hsync' := syncU_after_new_send cka prng fs Δcka qep tL tStar P m false isChall
                coins Ir (prng.up (esL.g.st P).root Ir).2 esL.h.2 s₁L s₁R esL cs esR ps (ps' Ir)
                hs hsends hepL hepR (hps' Ir).1 (fun _ => (hps' Ir).2)
                (fun heq => absurd heq het) (fun _ => rfl) (fun _ => rfl)
              dsimp only [ep] at hloc_false ⊢
              simp only [hst₁L, hst₁R, hloc_false, Bool.false_eq_true, ↓reduceIte] at hsync' ⊢
              exact ih _ _ _ hsync'
          · have hnotH : ¬(tL.isSome = true ∧ ep + 1 = healEpoch tL) := fun h => heqH h.2
            rw [runHM_hooksCKAU_none_send cka prng fs Δcka tL tStar s₁L P ep
              (esR.g.st P).γ (esL.g.st P).root esL.h cs
              htL_none_false hcanSend heqH hcs_epP hcs_stP, runHM_hooksPRNG_none]
            simp only [bind_assoc]
            refine DEq.bind_right ($ᵗ CCoins) fun coins => ?_
            have hstep := sendCore_step_knownU cka prng fs Δcka qep tL tStar b P m false isChall
              coins s₁L s₁R esL cs esR ps k hvg hs hsends hepL hepR hst₁L hst₁R hnotH ih
            dsimp only [ep] at hloc_false ⊢
            simp only [hloc_false, Bool.false_eq_true, ↓reduceIte] at hstep
            exact hstep
    · have hsendsF : P.sendsIn (ep + 1) = false := Bool.eq_false_iff.mpr hsends
      have hs₁L_eq := epMgmt_sendsIn_false hsendsF hepL
      have hs₁R_eq := epMgmt_sendsIn_false (eraseSt_epoch he ▸ hsendsF) hepR
      subst hs₁L_eq; subst hs₁R_eq
      have hsendsL : (esL.g.st P).id.sendsIn ((esL.g.st P).tcur + 1) = false := by
        rw [hidL, htcurL]; exact hsendsF
      have hsendsR : (esR.g.st P).id.sendsIn ((esR.g.st P).tcur + 1) = false := by
        rw [hidR, htcurR]; exact hsendsF
      rw [runEM_sendCore_sendsIn_false _ _ fs hfsL _ esL.g P m pair rcoins isChall esL cs hsendsL,
          runEM_sendCore_sendsIn_false _ _ fs hfsR _ esR.g P m pair rcoins isChall esR ps hsendsR]
      simp only [htcurL, htcurR, ← hTcur, ← hvS, pure_bind]
      have hepochR : esR.g.epoch P = esL.g.epoch P := (congrFun (eraseSt_epoch he) P).symm
      have hidxR : esR.g.idx P = esL.g.idx P := (congrFun (eraseSt_idx he) P).symm
      have hsync' := syncU_after_same_send prng fs Δcka tL tStar P m isChall esL cs esR ps hs
      dsimp only [ep] at htcurL htcurR hsync' ⊢
      rw [hepochR, hidxR]
      cases hvs : (esL.g.st P).vS <;>
        (simp only [hvs, htcurL, htcurR, ← hTcur] at hsync' ⊢; exact ih _ _ _ hsync')

private theorem evalEng_transmitE_syncU (tL : Option ℕ) (tStar : ℕ) (b : Bool)
    (P : Party) (m : M) (rcoins : Option CCoins)
    (esL : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAUState T I K))
    (cs : CKA.GameState Γ T)
    (esR : EState (PartyState Γ T (Option Sig) SS RS) M (Header T × E) (PRNGState T Sig K))
    (ps : PRFPRNG.GameState Sig I K)
    (k : Option (Header T × E) →
      OracleComp (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) Bool)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) tL tStar = true)
    (hs : SyncU prng Δcka tL tStar (esL, cs) (esR, ps))
    (ih : ∀ r sL' sR', SyncU prng Δcka tL tStar sL' sR' →
      DEq (evalEng (CKA.oracleImpl cka Δcka (healEpoch tL))
            (hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩)
            (2 + Δcka) qep fs.maxSkip (Config.priv tStar) ⟨false, tL, tStar⟩ b (k r) sL')
          (evalEng (PRFPRNG.oracleImpl prng)
            (hooksPRNG cka prng fs ⟨false, tL, tStar⟩)
            (2 + Δcka) qep fs.maxSkip (Config.priv tStar) ⟨false, tL, tStar⟩ b (k r) sR')) :
    DEq (runEM (CKA.oracleImpl cka Δcka (healEpoch tL))
          (transmitE (hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩)
            (2 + Δcka) qep ⟨false, tL, tStar⟩ ⟨P, m, rcoins⟩) (esL, cs) >>=
          fun r => evalEng (CKA.oracleImpl cka Δcka (healEpoch tL))
            (hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩)
            (2 + Δcka) qep fs.maxSkip (Config.priv tStar) ⟨false, tL, tStar⟩ b (k r.1) r.2)
        (runEM (PRFPRNG.oracleImpl prng)
          (transmitE (hooksPRNG cka prng fs ⟨false, tL, tStar⟩)
            (2 + Δcka) qep ⟨false, tL, tStar⟩ ⟨P, m, rcoins⟩) (esR, ps) >>=
          fun r => evalEng (PRFPRNG.oracleImpl prng)
            (hooksPRNG cka prng fs ⟨false, tL, tStar⟩)
            (2 + Δcka) qep fs.maxSkip (Config.priv tStar) ⟨false, tL, tStar⟩ b (k r.1) r.2) := by
  rcases hs with ⟨hs14, hb, hpre, hcache⟩
  have hs : SyncU prng Δcka tL tStar (esL, cs) (esR, ps) := ⟨hs14, hb, hpre, hcache⟩
  rcases hs14 with ⟨habL, habR, he, _⟩
  dsimp [projL, patchES] at habL habR he
  have hwin : esR.g.win = esL.g.win := (eraseSt_win he).symm
  unfold transmitE; dsimp only
  rw [runEM_bind, runEM_get, pure_bind, runEM_bind, runEM_get, pure_bind]; dsimp only
  rw [habL, habR, hwin]
  by_cases hg : (false || esL.g.win) = true
  · simp only [hg, ↓reduceIte, runEM_pure, pure_bind]
    exact ih none (esL, cs) (esR, ps) hs
  · simp only [hg, Bool.false_eq_true, ↓reduceIte]
    cases hepL : esL.g.epMgmt (2 + Δcka) qep P rcoins.isSome with
    | none =>
      rw [eraseSt_epMgmt_none he hepL, runEM_pure, runEM_pure, pure_bind, pure_bind]
      exact ih none (esL, cs) (esR, ps) hs
    | some s₁L =>
      rcases eraseSt_epMgmt_some he hepL with ⟨s₁R, hepR, he₁, _, _⟩
      rw [hepR]; dsimp only
      rw [(eraseSt_leakDoom he he₁ ⟨false, tL, tStar⟩).symm]
      cases hld : Policy.leakDoom ⟨false, tL, tStar⟩ esL.g s₁L
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact evalEng_sendCore_syncU cka prng fs Δcka qep tL tStar b P m none rcoins false
          s₁L s₁R esL cs esR ps k hvg hs hepL hepR hld ih
      · simp only [↓reduceIte, runEM_abort_pure, pure_bind]
        exact (evalEng_doom _ _ _ _ _ _ _ _ _ _ (Or.inl rfl)).trans
          (evalEng_doom _ _ _ _ _ _ _ _ _ _ (Or.inl rfl)).symm

private theorem evalEng_challE_syncU (tL : Option ℕ) (tStar : ℕ) (b : Bool)
    (P : Party) (m₀ m₁ : M) (rcoins : Option CCoins)
    (esL : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAUState T I K))
    (cs : CKA.GameState Γ T)
    (esR : EState (PartyState Γ T (Option Sig) SS RS) M (Header T × E) (PRNGState T Sig K))
    (ps : PRFPRNG.GameState Sig I K)
    (k : Option (Header T × E) →
      OracleComp (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) Bool)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) tL tStar = true)
    (hs : SyncU prng Δcka tL tStar (esL, cs) (esR, ps))
    (ih : ∀ r sL' sR', SyncU prng Δcka tL tStar sL' sR' →
      DEq (evalEng (CKA.oracleImpl cka Δcka (healEpoch tL))
            (hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩)
            (2 + Δcka) qep fs.maxSkip (Config.priv tStar) ⟨false, tL, tStar⟩ b (k r) sL')
          (evalEng (PRFPRNG.oracleImpl prng)
            (hooksPRNG cka prng fs ⟨false, tL, tStar⟩)
            (2 + Δcka) qep fs.maxSkip (Config.priv tStar) ⟨false, tL, tStar⟩ b (k r) sR')) :
    DEq (runEM (CKA.oracleImpl cka Δcka (healEpoch tL))
          (challE (hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩)
            (2 + Δcka) qep (Config.priv tStar) ⟨false, tL, tStar⟩ ⟨P, m₀, m₁, rcoins⟩) (esL, cs) >>=
          fun r => evalEng (CKA.oracleImpl cka Δcka (healEpoch tL))
            (hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩)
            (2 + Δcka) qep fs.maxSkip (Config.priv tStar) ⟨false, tL, tStar⟩ b (k r.1) r.2)
        (runEM (PRFPRNG.oracleImpl prng)
          (challE (hooksPRNG cka prng fs ⟨false, tL, tStar⟩)
            (2 + Δcka) qep (Config.priv tStar) ⟨false, tL, tStar⟩ ⟨P, m₀, m₁, rcoins⟩) (esR, ps) >>=
          fun r => evalEng (PRFPRNG.oracleImpl prng)
            (hooksPRNG cka prng fs ⟨false, tL, tStar⟩)
            (2 + Δcka) qep fs.maxSkip (Config.priv tStar) ⟨false, tL, tStar⟩ b (k r.1) r.2) := by
  rcases hs with ⟨hs14, hb, hpre, hcache⟩
  have hs : SyncU prng Δcka tL tStar (esL, cs) (esR, ps) := ⟨hs14, hb, hpre, hcache⟩
  rcases hs14 with ⟨habL, habR, he, _⟩
  dsimp [projL, patchES] at habL habR he
  have hwin : esR.g.win = esL.g.win := (eraseSt_win he).symm
  unfold challE; dsimp only
  rw [runEM_bind, runEM_get, pure_bind, runEM_bind, runEM_get, pure_bind]; dsimp only
  rw [habL, habR, hwin]
  by_cases hg : (false || esL.g.win) = true
  · simp only [hg, ↓reduceIte, runEM_pure, pure_bind]
    exact ih none (esL, cs) (esR, ps) hs
  · simp only [hg, Bool.false_eq_true, ↓reduceIte]
    cases hepL : esL.g.epMgmt (2 + Δcka) qep P rcoins.isSome with
    | none =>
      rw [eraseSt_epMgmt_none he hepL, runEM_pure, runEM_pure, pure_bind, pure_bind]
      exact ih none (esL, cs) (esR, ps) hs
    | some s₁L =>
      rcases eraseSt_epMgmt_some he hepL with ⟨s₁R, hepR, he₁, _, _⟩
      rw [hepR]; dsimp only
      have hsc_eq : s₁R.safeCh (2 + Δcka) P = s₁L.safeCh (2 + Δcka) P :=
        (eraseSt_safeCh he₁ (2 + Δcka) P).symm
      have hep₁_eq : s₁R.epoch P = s₁L.epoch P := (congrFun (eraseSt_epoch he₁) P).symm
      have hb_eq : esR.g.b = esL.g.b := (eraseSt_b he).symm
      have hchallOK_eq :
          (Config.priv (Msg := M) tStar).challAllowedIn (s₁R.epoch P) =
            (Config.priv (Msg := M) tStar).challAllowedIn (s₁L.epoch P) := by rw [hep₁_eq]
      rw [hsc_eq, hchallOK_eq]
      by_cases hsc :
          (!s₁L.safeCh (2 + Δcka) P || !(Config.priv (Msg := M) tStar).challAllowedIn (s₁L.epoch P)) = true
      · simp only [hsc, ↓reduceIte, runEM_pure, pure_bind]
        exact ih none (esL, cs) (esR, ps) hs
      · simp only [hsc, Bool.false_eq_true, ↓reduceIte]
        rw [(eraseSt_leakDoom he he₁ ⟨false, tL, tStar⟩).symm]
        cases hld : Policy.leakDoom ⟨false, tL, tStar⟩ esL.g s₁L
        · simp only [Bool.false_eq_true, ↓reduceIte]
          have hm_eq :
              ((Config.priv (Msg := M) tStar).challMsg (s₁R.epoch P)).getD
                (if esR.g.b then m₁ else m₀) =
              ((Config.priv (Msg := M) tStar).challMsg (s₁L.epoch P)).getD
                (if esL.g.b then m₁ else m₀) := by rw [hep₁_eq, hb_eq]
          rw [hm_eq]
          exact evalEng_sendCore_syncU cka prng fs Δcka qep tL tStar b P _ (some (m₀, m₁)) rcoins true
            s₁L s₁R esL cs esR ps k hvg hs hepL hepR hld ih
        · simp only [↓reduceIte, runEM_abort_pure, pure_bind]
          exact (evalEng_doom _ _ _ _ _ _ _ _ _ _ (Or.inl rfl)).trans
            (evalEng_doom _ _ _ _ _ _ _ _ _ _ (Or.inl rfl)).symm

private theorem evalEng_syncU (tL : Option ℕ) (tStar : ℕ) (b : Bool)
    (oa : OracleComp (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) Bool)
    (sL : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAUState T I K) ×
      CKA.GameState Γ T)
    (sR : EState (PartyState Γ T (Option Sig) SS RS) M (Header T × E) (PRNGState T Sig K) ×
      PRFPRNG.GameState Sig I K)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) tL tStar = true)
    (hs : SyncU prng Δcka tL tStar sL sR) :
    DEq (evalEng (CKA.oracleImpl cka Δcka (healEpoch tL))
          (hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩)
          (2 + Δcka) qep fs.maxSkip (Config.priv tStar) ⟨false, tL, tStar⟩ b oa sL)
        (evalEng (PRFPRNG.oracleImpl prng)
          (hooksPRNG cka prng fs ⟨false, tL, tStar⟩)
          (2 + Δcka) qep fs.maxSkip (Config.priv tStar) ⟨false, tL, tStar⟩ b oa sR) := by
  induction oa using OracleComp.inductionOn generalizing sL sR with
  | pure b' =>
    rw [evalEng_pure, evalEng_pure, hs.privOutP_eq]
  | query_bind q k ih =>
    rw [evalEng_query_bind, evalEng_query_bind]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq]
    rcases sL with ⟨esL, cs⟩
    rcases sR with ⟨esR, ps⟩
    rcases q with n | ⟨⟨⟨⟨⟨P, m, rcoins⟩ | ⟨P, m₀, m₁, rcoins⟩⟩ | ⟨P, c⟩⟩ | ⟨P, c⟩⟩ | P⟩
    · change DEq (runEM _ (coinsE n) (esL, cs) >>= _) (runEM _ (coinsE n) (esR, ps) >>= _)
      rw [runEM_coinsE_bind, runEM_coinsE_bind]
      exact DEq.bind_right _ fun x => ih x (esL, cs) (esR, ps) hs
    · exact evalEng_transmitE_syncU cka prng fs Δcka qep tL tStar b P m rcoins
        esL cs esR ps k hvg hs ih
    · exact evalEng_challE_syncU cka prng fs Δcka qep tL tStar b P m₀ m₁ rcoins
        esL cs esR ps k hvg hs ih
    · rcases runEM_deliverE_syncU cka prng fs Δcka fs.maxSkip (Config.priv tStar) tL tStar
        ⟨P, c⟩ esL cs esR ps hs with ⟨out, sL', sR', hL, hR, hs'⟩
      change DEq (runEM _ (deliverE _ _ _ ⟨P, c⟩) (esL, cs) >>= _)
                 (runEM _ (deliverE _ _ _ ⟨P, c⟩) (esR, ps) >>= _)
      rw [hL, hR, pure_bind, pure_bind]
      exact ih out sL' sR' hs'
    · rcases runEM_injectE_syncU cka prng fs Δcka qep (Config.priv tStar) tL tStar ⟨P, c⟩
        esL cs esR ps hs with ⟨out, sL', sR', hL, hR, hs'⟩
      change DEq (runEM _ (injectE _ _ _ _ ⟨P, c⟩) (esL, cs) >>= _)
                 (runEM _ (injectE _ _ _ _ ⟨P, c⟩) (esR, ps) >>= _)
      rw [hL, hR, pure_bind, pure_bind]
      exact ih out sL' sR' hs'
    · rcases runEM_corrE_syncU cka prng fs Δcka tL tStar P (esL, cs) (esR, ps) hs hvg with
        ⟨out, sL', sR', hL, hR, hsd⟩
      change DEq (runEM _ (corrE _ _ P) (esL, cs) >>= _)
                 (runEM _ (corrE _ _ P) (esR, ps) >>= _)
      rw [hL, hR, pure_bind, pure_bind]
      rcases hsd with hs' | ⟨hdL, hdR⟩
      · exact ih out sL' sR' hs'
      · exact (evalEng_doom _ _ _ _ _ _ _ _ _ sL' hdL).trans
          (evalEng_doom _ _ _ _ _ _ _ _ _ sR' hdR).symm

private theorem init_syncU
    (tL : Option ℕ) (tStar : ℕ) (b : Bool) (kr : KR) (kc_game kc : KC)
    (ps₁ : PRFPRNG.GameState Sig I K)
    (hkc : tL.isSome = true → kc_game = kc)
    (hb₁ : ps₁.b = true)
    (hps₁ : 0 < tStar →
      ps₁.table = [] ∧ ps₁.prf = false ∧ ps₁.prng = false ∧
      ps₁.corr = (tL.isSome && decide (0 < healEpoch tL)) ∧
      ps₁.σ = (prng.up (prng.init kr) lam).1) :
    let out := prng.up (prng.init kr) lam
    let γAL : Option Γ := if tL.isNone then some (cka.initA kc) else none
    let γBL : Option Γ := if tL.isNone then some (cka.initB kc) else none
    let σR : Option Sig :=
      if decide (tStar ≤ 0) || (tL.isSome && decide (0 < healEpoch tL))
      then some out.1 else none
    let pL := mkParties (T := T) γAL γBL out.1 (fs.initSender out.2) (fs.initReceiver out.2)
    let pR := mkParties (T := T) (cka.initA kc) (cka.initB kc) σR
      (fs.initSender out.2) (fs.initReceiver out.2)
    let gL : Ctx (Option Γ) T Sig SS RS M E :=
      { st := fun P => match P with | .A => pL.1 | .B => pL.2, b }
    let gR : Ctx Γ T (Option Sig) SS RS M E :=
      { st := fun P => match P with | .A => pR.1 | .B => pR.2, b }
    SyncU prng Δcka tL tStar
      ({ g := gL, h := ({}, none) }, CKA.initState cka kc_game true)
      ({ g := gR, h := {} }, ps₁) := by
  intro out γAL γBL σR pL pR gL gR
  have hpatch : patchES prng tStar
      ({ g := gL, h := ({}, none) } :
        EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAUState T I K))
      ({ g := gR, h := {} } :
        EState (PartyState Γ T (Option Sig) SS RS) M (Header T × E) (PRNGState T Sig K)) =
      { g := gR, h := {} } := by
    dsimp [patchES]
    congr 2; funext e
    by_cases het : e = tStar <;> simp [het]
  refine ⟨?_, hb₁, ?_, fun _ _ _ hc => by contradiction⟩
  · dsimp [projL]
    rw [hpatch]
    exact init_sync cka prng fs lam Δcka tL tStar b kr kc_game kc { ps₁ with b := false } hkc
      fun hlt =>
        let ⟨_, hprf, hprng1, hcorr, hσ⟩ := hps₁ hlt
        ⟨rfl, hprf, hprng1, hcorr, hσ⟩
  · intro hlt
    have ht0 : 0 < tStar := by
      have : max (gL.epoch .A) (gL.epoch .B) = 0 := rfl
      omega
    exact ⟨(hps₁ ht0).1, rfl⟩

private theorem runHM_initCKAU_eq (mo : Mode) (cs : CKA.GameState Γ T) :
    runHM (CKA.oracleImpl cka Δcka (healEpoch mo.tL))
      (initCKAU cka prng fs lam mo) ({}, none) cs =
    (fun r => ((r.1.1, (r.1.2, none)), r.2)) <$>
      runHM (CKA.oracleImpl cka Δcka (healEpoch mo.tL))
        (initCKA cka prng fs lam mo) {} cs := by
  unfold runHM initCKAU
  change StateT.run (simulateQ (outerFull (CKA.oracleImpl cka Δcka (healEpoch mo.tL)))
    ((initCKA cka prng fs lam mo).run {} >>= fun x => pure (x.1, (x.2, none)))) cs = _
  simp [simulateQ_bind, StateT.run_bind, map_eq_bind_pure_comp]

private theorem runHM_initCKAU_none (tStar : ℕ) (cs : CKA.GameState Γ T) :
    runHM (CKA.oracleImpl cka Δcka (healEpoch none))
      (initCKAU cka prng fs lam ⟨false, none, tStar⟩) ({}, none) cs =
      (($ᵗ KR : ProbComp KR) >>= fun kr =>
        ($ᵗ KC : ProbComp KC) >>= fun kc =>
          let out := prng.up (prng.init kr) lam
          pure ((some (mkParties (some (cka.initA kc)) (some (cka.initB kc)) out.1
                  (fs.initSender out.2) (fs.initReceiver out.2)), ({}, none)), cs)) := by
  rw [runHM_initCKAU_eq cka prng fs lam Δcka ⟨false, none, tStar⟩ cs,
      runHM_initCKA_none cka prng fs lam Δcka tStar {} cs]
  simp [map_bind]

private theorem runHM_initCKAU_some (l tStar : ℕ) (cs : CKA.GameState Γ T) :
    runHM (CKA.oracleImpl cka Δcka (healEpoch (some l)))
      (initCKAU cka prng fs lam ⟨false, some l, tStar⟩) ({}, none) cs =
      (($ᵗ KR : ProbComp KR) >>= fun kr =>
        let out := prng.up (prng.init kr) lam
        pure ((some (mkParties none none out.1
                (fs.initSender out.2) (fs.initReceiver out.2)), ({}, none)), cs)) := by
  rw [runHM_initCKAU_eq cka prng fs lam Δcka ⟨false, some l, tStar⟩ cs,
      runHM_initCKA_some cka prng fs lam Δcka l tStar {} cs]
  simp

end PrivL14U

/-- Stage-2 switch-back Lemma 14 (`b = true` coupling): for `0 < t` and admissible `tL`,
`CKA.branch ... true (redCKAPrivU ... tL t A)` is distributionally equal (`DEq`) to
`PRFPRNG.branch prng true (redPRNGPriv ... tL t A)`. -/
theorem branch_redCKAPrivU_true_dEq_redPRNGPriv_true
    (tL : Option ℕ) (t : ℕ) (ht : 0 < t)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) tL t = true)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    DEq (CKA.branch cka Δcka (healEpoch tL) true
          (redCKAPrivU cka prng fs lam Δcka qep tL t A))
        (PRFPRNG.branch prng true
          (redPRNGPriv cka prng fs lam Δcka qep tL t A)) := by
  open Engine PrivL14 PrivL14U in
  have hLHS :
      CKA.branch cka Δcka (healEpoch tL) true
          (redCKAPrivU cka prng fs lam Δcka qep tL t A) =
        (($ᵗ KC : ProbComp KC) >>= fun kc =>
          ($ᵗ Bool : ProbComp Bool) >>= fun b =>
          runHM (CKA.oracleImpl cka Δcka (healEpoch tL))
            (initCKAU cka prng fs lam ⟨false, tL, t⟩) ({}, none)
            (CKA.initState cka kc true) >>= fun x =>
          match x.1.1 with
          | none => ($ᵗ Bool : ProbComp Bool)
          | some (vA, vB) =>
            let g : Ctx (Option Γ) T Sig SS RS M E :=
              { st := fun P => match P with | .A => vA | .B => vB, b }
            evalEng (CKA.oracleImpl cka Δcka (healEpoch tL))
              (hooksCKAU cka prng fs Δcka ⟨false, tL, t⟩)
              (2 + Δcka) qep fs.maxSkip (Config.priv t) ⟨false, tL, t⟩ b A
              ({ g, h := x.1.2 }, x.2)) := by
    refine bind_congr fun kc => ?_
    unfold redCKAPrivU runCKAU
    change Prod.fst <$> (simulateQ (outerFull (CKA.oracleImpl cka Δcka (healEpoch tL))) _).run
      (CKA.initState cka kc true) = _
    simp only [engRun, simulateQ_bind, StateT.run_bind, bind_assoc,
      simulateQ_outerFull_sampleT, bind_map_left, map_bind, runHM]
    refine bind_congr fun b => bind_congr fun ⟨⟨vs, h⟩, os₁⟩ => ?_
    cases vs with
    | none => simp [simulateQ_outerFull_sampleT]
    | some vAvB =>
      rcases vAvB with ⟨vA, vB⟩
      simp only [evalEng, runEM, simulateQ_bind, StateT.run_bind, bind_assoc, simulateQ_pure,
        StateT.run_pure, pure_bind, bind_map_left, simulateQ_outerFull_privOut]
      rfl
  have hRHS :
      PRFPRNG.branch prng true
          (redPRNGPriv cka prng fs lam Δcka qep tL t A) =
        (($ᵗ KR : ProbComp KR) >>= fun kr =>
          ($ᵗ Bool : ProbComp Bool) >>= fun b =>
          runHM (PRFPRNG.oracleImpl prng)
            (initPRNG cka prng fs lam ⟨false, tL, t⟩) {}
            { σ := prng.init kr, b := true } >>= fun x =>
          match x.1.1 with
          | none => ($ᵗ Bool : ProbComp Bool)
          | some (vA, vB) =>
            let g : Ctx Γ T (Option Sig) SS RS M E :=
              { st := fun P => match P with | .A => vA | .B => vB, b }
            evalEng (PRFPRNG.oracleImpl prng)
              (hooksPRNG cka prng fs ⟨false, tL, t⟩)
              (2 + Δcka) qep fs.maxSkip (Config.priv t) ⟨false, tL, t⟩ b A
              ({ g, h := x.1.2 }, x.2)) := by
    refine bind_congr fun kr => ?_
    unfold redPRNGPriv runPRNG
    change Prod.fst <$> (simulateQ (outerFull (PRFPRNG.oracleImpl prng)) _).run
      { σ := prng.init kr, b := true } = _
    simp only [engRun, simulateQ_bind, StateT.run_bind, bind_assoc,
      simulateQ_outerFull_sampleT, bind_map_left, map_bind, runHM]
    refine bind_congr fun b => bind_congr fun ⟨⟨vs, h⟩, os₁⟩ => ?_
    cases vs with
    | none => simp [simulateQ_outerFull_sampleT]
    | some vAvB =>
      rcases vAvB with ⟨vA, vB⟩
      simp only [evalEng, runEM, simulateQ_bind, StateT.run_bind, bind_assoc, simulateQ_pure,
        StateT.run_pure, pure_bind, bind_map_left, simulateQ_outerFull_privOut]
      rfl
  rw [hLHS, hRHS]
  have hnotH0 : ¬(tL.isSome = true ∧ 0 = healEpoch tL) := by
    rintro ⟨htL, h0⟩
    cases tL with
    | none => simp at htL
    | some l => simp [healEpoch] at h0
  have hne0 : (0 : ℕ) ≠ t := by omega
  have hPRNG :
      DEq (($ᵗ KR : ProbComp KR) >>= fun kr =>
            ($ᵗ Bool : ProbComp Bool) >>= fun b =>
            runHM (PRFPRNG.oracleImpl prng)
              (initPRNG cka prng fs lam ⟨false, tL, t⟩) {}
              { σ := prng.init kr, b := true } >>= fun x =>
            match x.1.1 with
            | none => ($ᵗ Bool : ProbComp Bool)
            | some (vA, vB) =>
              let g : Ctx Γ T (Option Sig) SS RS M E :=
                { st := fun P => match P with | .A => vA | .B => vB, b }
              evalEng (PRFPRNG.oracleImpl prng)
                (hooksPRNG cka prng fs ⟨false, tL, t⟩)
                (2 + Δcka) qep fs.maxSkip (Config.priv t) ⟨false, tL, t⟩ b A
                ({ g, h := x.1.2 }, x.2))
          (($ᵗ Bool : ProbComp Bool) >>= fun b =>
            ($ᵗ KR : ProbComp KR) >>= fun kr =>
            ($ᵗ KC : ProbComp KC) >>= fun kc =>
            evalEng (CKA.oracleImpl cka Δcka (healEpoch tL))
              (hooksCKAU cka prng fs Δcka ⟨false, tL, t⟩)
              (2 + Δcka) qep fs.maxSkip (Config.priv t) ⟨false, tL, t⟩ b A
              (let out := prng.up (prng.init kr) lam
               let γAL : Option Γ := if tL.isNone then some (cka.initA kc) else none
               let γBL : Option Γ := if tL.isNone then some (cka.initB kc) else none
               let pL := mkParties (T := T) γAL γBL out.1
                 (fs.initSender out.2) (fs.initReceiver out.2)
               let gL : Ctx (Option Γ) T Sig SS RS M E :=
                 { st := fun P => match P with | .A => pL.1 | .B => pL.2, b }
               ({ g := gL, h := ({}, none) }, CKA.initState cka kc true))) := by
    refine (DEq.swap ($ᵗ KR) ($ᵗ Bool) _).trans (DEq.bind_right ($ᵗ Bool) fun b => ?_)
    refine DEq.bind_right ($ᵗ KR) fun kr => ?_
    unfold initPRNG
    rw [runHM_bind, runHM_sampleT, bind_map_left, bind_assoc]
    refine DEq.bind_right ($ᵗ KC) fun kc => ?_
    dsimp only
    rcases runHM_rootPRNG_ne_tStar prng ({} : PRNGState T Sig K)
      { σ := prng.init kr, b := true } hne0 rfl (fun h => absurd h (by omega))
      (fun h => absurd h (by omega)) (fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩) hnotH0
      (Ik := lam) (σv := none) with ⟨ps₁, hroot0, hb₁, hps₁⟩
    rw [runHM_bind, hroot0, pure_bind]; dsimp only
    rw [runHM_pure, pure_bind]; dsimp only
    exact (evalEng_syncU cka prng fs Δcka qep tL t b A _ _ hvg
      (init_syncU cka prng fs lam Δcka tL t b kr kc kc ps₁ (fun _ => rfl) hb₁ hps₁)).symm
  refine DEq.trans ?_ hPRNG.symm
  cases tL with
  | none =>
    have hCKA_none : ∀ kc_game : KC,
        DEq (($ᵗ Bool : ProbComp Bool) >>= fun b =>
              runHM (CKA.oracleImpl cka Δcka (healEpoch none))
                (initCKAU cka prng fs lam ⟨false, none, t⟩) ({}, none)
                (CKA.initState cka kc_game true) >>= fun x =>
              match x.1.1 with
              | none => ($ᵗ Bool : ProbComp Bool)
              | some (vA, vB) =>
                let g : Ctx (Option Γ) T Sig SS RS M E :=
                  { st := fun P => match P with | .A => vA | .B => vB, b }
                evalEng (CKA.oracleImpl cka Δcka (healEpoch none))
                  (hooksCKAU cka prng fs Δcka ⟨false, none, t⟩)
                  (2 + Δcka) qep fs.maxSkip (Config.priv t) ⟨false, none, t⟩ b A
                  ({ g, h := x.1.2 }, x.2))
            (($ᵗ Bool : ProbComp Bool) >>= fun b =>
              ($ᵗ KR : ProbComp KR) >>= fun kr =>
              ($ᵗ KC : ProbComp KC) >>= fun kc =>
              evalEng (CKA.oracleImpl cka Δcka (healEpoch none))
                (hooksCKAU cka prng fs Δcka ⟨false, none, t⟩)
                (2 + Δcka) qep fs.maxSkip (Config.priv t) ⟨false, none, t⟩ b A
                (let out := prng.up (prng.init kr) lam
                 let pL := mkParties (T := T) (some (cka.initA kc)) (some (cka.initB kc)) out.1
                   (fs.initSender out.2) (fs.initReceiver out.2)
                 let gL : Ctx (Option Γ) T Sig SS RS M E :=
                   { st := fun P => match P with | .A => pL.1 | .B => pL.2, b }
                 ({ g := gL, h := ({}, none) }, CKA.initState cka kc true))) := by
      intro kc_game
      refine DEq.bind_right ($ᵗ Bool) fun b => ?_
      rw [runHM_initCKAU_none, bind_assoc]
      refine DEq.bind_right ($ᵗ KR) fun kr => ?_
      rw [bind_assoc]
      refine DEq.bind_right ($ᵗ KC) fun kc => ?_
      rw [pure_bind]; dsimp only
      rcases runHM_rootPRNG_ne_tStar prng ({} : PRNGState T Sig K)
        { σ := prng.init kr, b := true } hne0 rfl (fun h => absurd h (by omega))
        (fun h => absurd h (by omega)) (fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩) hnotH0
        (Ik := lam) (σv := none) with ⟨ps₁, _, hb₁, hps₁⟩
      exact (evalEng_syncU cka prng fs Δcka qep none t b A _ _ hvg
        (init_syncU cka prng fs lam Δcka none t b kr kc_game kc ps₁
          (fun h => by contradiction) hb₁ hps₁)).trans
        (evalEng_syncU cka prng fs Δcka qep none t b A _ _ hvg
          (init_syncU cka prng fs lam Δcka none t b kr kc kc ps₁
            (fun _ => rfl) hb₁ hps₁)).symm
    exact (DEq.bind_right ($ᵗ KC) hCKA_none).trans (DEq.bind_const ($ᵗ KC) _)
  | some l =>
    have hCKA_some :
        DEq (($ᵗ KC : ProbComp KC) >>= fun kc =>
              ($ᵗ Bool : ProbComp Bool) >>= fun b =>
              runHM (CKA.oracleImpl cka Δcka (healEpoch (some l)))
                (initCKAU cka prng fs lam ⟨false, some l, t⟩) ({}, none)
                (CKA.initState cka kc true) >>= fun x =>
              match x.1.1 with
              | none => ($ᵗ Bool : ProbComp Bool)
              | some (vA, vB) =>
                let g : Ctx (Option Γ) T Sig SS RS M E :=
                  { st := fun P => match P with | .A => vA | .B => vB, b }
                evalEng (CKA.oracleImpl cka Δcka (healEpoch (some l)))
                  (hooksCKAU cka prng fs Δcka ⟨false, some l, t⟩)
                  (2 + Δcka) qep fs.maxSkip (Config.priv t) ⟨false, some l, t⟩ b A
                  ({ g, h := x.1.2 }, x.2))
            (($ᵗ KC : ProbComp KC) >>= fun kc =>
              ($ᵗ Bool : ProbComp Bool) >>= fun b =>
              ($ᵗ KR : ProbComp KR) >>= fun kr =>
              evalEng (CKA.oracleImpl cka Δcka (healEpoch (some l)))
                (hooksCKAU cka prng fs Δcka ⟨false, some l, t⟩)
                (2 + Δcka) qep fs.maxSkip (Config.priv t) ⟨false, some l, t⟩ b A
                (let out := prng.up (prng.init kr) lam
                 let pL := mkParties (T := T) none none out.1
                   (fs.initSender out.2) (fs.initReceiver out.2)
                 let gL : Ctx (Option Γ) T Sig SS RS M E :=
                   { st := fun P => match P with | .A => pL.1 | .B => pL.2, b }
                 ({ g := gL, h := ({}, none) }, CKA.initState cka kc true))) := by
      refine DEq.bind_right ($ᵗ KC) fun kc => DEq.bind_right ($ᵗ Bool) fun b => ?_
      rw [runHM_initCKAU_some, bind_assoc]
      refine DEq.bind_right ($ᵗ KR) fun kr => ?_
      rw [pure_bind]
    refine hCKA_some.trans ?_
    refine (DEq.swap ($ᵗ KC) ($ᵗ Bool) _).trans (DEq.bind_right ($ᵗ Bool) fun b => ?_)
    exact DEq.swap ($ᵗ KC) ($ᵗ KR) _

end Stage2L14U

end CryptoGames.SM.Construction
