/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Reductions -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem12.Stage2Defs -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem12.Stage2L13UDoom -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.SM.Theorem12.Lemma13
import Computational.Proofs.CryptoGames.SM.Theorem12.Lemma14
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# `Sync13U` Invariant and Receive/Corruption Step Lemmas for Lemma 13U (`SM/Theorem12.lean`)

**Checked by Lean.** No theorem of `Computational/Theorems/` unfolds a definition of this file, and
Lean's kernel checks every proof in it: you do not need to read it to trust those theorems.

Defines `Sync13U` and proves `corrE`, `vRecv`, `commitE`, `deliverE`, `injectE`, and post-send
`Sync13U` preservation for the real-world switch-back equivalence between `redCKAPrivUUniAt` and
`redCKAPrivU`.-/

set_option autoImplicit false

public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.SM.Construction.PrivL13U

open Engine PrivL14 CryptoGames.Lazy

section Sync13U

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}

@[expose] def PartyRel13U (Δcka : ℕ) (tL : Option ℕ) (P : Party) (ep : ℕ)
    (vpL vpR : PartyState (Option Γ) T Sig SS RS) : Prop :=
  vpL.id = P ∧ vpR.id = P ∧
  vpL.tcur = ep ∧ vpR.tcur = ep ∧
  vpL.root = vpR.root ∧ vpL.vS = vpR.vS ∧ vpL.vR = vpR.vR ∧ vpL.curCkaMsg = vpR.curCkaMsg ∧
  ∃ γ : Γ, vpL.γ = some γ ∧
    vpR.γ = (if tL.isNone || decide (healEpoch tL + Δcka ≤ ep) then some γ else none)

@[expose] def CKARel13U (Δcka : ℕ) (tL : Option ℕ)
    (gL : Ctx (Option Γ) T Sig SS RS M E)
    (csR : CKA.GameState Γ T) : Prop :=
  csR.b = false ∧
  ∀ P, tL.isSome = true → gL.epoch P < healEpoch tL + Δcka →
    (gL.st P).γ = some (csR.st P) ∧ csR.epoch P = gL.epoch P

@[expose] def PingPong13U (Δcka : ℕ) (tL : Option ℕ)
    (esL : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAUState T I K))
    (csR : CKA.GameState Γ T) : Prop :=
  (∀ t' > max (esL.g.epoch .A) (esL.g.epoch .B), esL.h.1.cache t' = none) ∧
  (esL.g.epoch .A = esL.g.epoch .B ∨
   ∃ P t0 Tc Ik,
     P.sendsIn (t0 + 1) = true ∧
     esL.g.epoch P = t0 + 1 ∧
     esL.g.epoch P.other = t0 ∧
     esL.h.1.cache (t0 + 1) = some (Tc, Ik) ∧
     (tL.isSome = true → t0 < healEpoch tL + Δcka →
       csR.epoch P = t0 + 1 ∧ csR.lastMsg = some Tc))

@[expose] def Sync13U (Δcka : ℕ) (tL : Option ℕ)
    (sL sR : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAUState T I K) ×
      CKA.GameState Γ T) : Prop :=
  sL.1.abort = false ∧ sR.1.abort = false ∧
  eraseSt sL.1.g = eraseSt sR.1.g ∧
  GameInv sL.1.g ∧
  sL.1.h = sR.1.h ∧
  (∀ P, PartyRel13U Δcka tL P (sL.1.g.epoch P) (sL.1.g.st P) (sR.1.g.st P)) ∧
  CKARel13U Δcka tL sL.1.g sR.2 ∧
  PingPong13U Δcka tL sL.1 sR.2

theorem PingPong13U.synced_of_sendsIn {Δcka : ℕ} {tL : Option ℕ}
    {esL : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAUState T I K)}
    {csR : CKA.GameState Γ T} {P : Party}
    (hpp : PingPong13U Δcka tL esL csR)
    (hs : P.sendsIn (esL.g.epoch P + 1) = true) :
    esL.g.epoch .A = esL.g.epoch .B := by
  rcases hpp.2 with hsync | ⟨Q, t0, Tc, Ik, hQ, hepQ, hepQo, -⟩
  · exact hsync
  · exfalso
    have hPQ : P = Q ∨ P = Q.other := by cases P <;> cases Q <;> decide
    rcases hPQ with rfl | rfl
    · rw [hepQ, sendsIn_succ, hQ] at hs; contradiction
    · rw [hepQo, sendsIn_other, hQ] at hs; contradiction

theorem PingPong13U.recv_step {Δcka : ℕ} {tL : Option ℕ}
    {esL : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAUState T I K)}
    {csR : CKA.GameState Γ T} (hpp : PingPong13U Δcka tL esL csR) (P : Party) :
    let ep := esL.g.epoch P
    esL.h.1.cache (ep + 1) = none ∨
    (P.other.sendsIn (ep + 1) = true ∧
     esL.g.epoch P.other = ep + 1 ∧
     ∃ Tc Ik,
       esL.h.1.cache (ep + 1) = some (Tc, Ik) ∧
       (tL.isSome = true → ep < healEpoch tL + Δcka →
         csR.epoch P.other = ep + 1 ∧ csR.lastMsg = some Tc)) := by
  intro ep
  rcases hpp with ⟨hcache, hAB | ⟨Q, t0, Tc, Ik, hQ, hepQ, hepQo, hcL, hcs⟩⟩
  · left
    apply hcache
    cases P <;> dsimp [ep] <;> omega
  · have hPQ : P = Q ∨ P = Q.other := by cases P <;> cases Q <;> decide
    rcases hPQ with rfl | rfl
    · left
      apply hcache
      cases P <;> dsimp [ep] at hepQ hepQo ⊢ <;> omega
    · right
      rw [Party.other_other]
      have hep : ep = t0 := hepQo
      rw [hep]
      exact ⟨hQ, hepQ, Tc, Ik, hcL, hcs⟩

theorem Sync13U.set_win {Δcka : ℕ} {tL : Option ℕ}
    {esL esR : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAUState T I K)}
    {csL csR : CKA.GameState Γ T}
    (hs : Sync13U Δcka tL (esL, csL) (esR, csR)) :
    Sync13U Δcka tL
      ({ esL with g := { esL.g with win := true } }, csL)
      ({ esR with g := { esR.g with win := true } }, csR) := by
  rcases hs with ⟨habL, habR, he, hinv, hh, hp, hcka, hpp⟩
  refine ⟨habL, habR, ?_, hinv, hh, hp, hcka, hpp⟩
  unfold eraseSt at he ⊢
  dsimp only
  exact congrArg (fun g => { g with win := true }) he

section RunHMCKAU

variable [SampleableType CCoins] [SampleableType I]
  (cka : CKAScheme KC Γ CCoins T I) (Δcka tH : ℕ)

theorem runHM_cacheCU (t : ℕ) (x : T × I) (h : CKAUState T I K) (cs : CKA.GameState Γ T) :
    runHM (CKA.oracleImpl cka Δcka tH) (cacheCU t x) h cs =
      pure (((), ({ cache := Function.update h.1.cache t (some x) }, h.2)), cs) := by
  simp [cacheCU, runHM_modify]

theorem runHM_liftCU_corr (P : Party) (h : CKAUState T I K) (cs : CKA.GameState Γ T) :
    runHM (CKA.oracleImpl cka Δcka tH) (StateT.lift (CKA.corrQuery P)) h cs =
      pure ((if cs.allowCorr tH || cs.finished Δcka tH P then some (cs.st P) else none, h), cs) := by
  simp [runHM, CKA.corrQuery, outerFull, CKA.oracleImpl, CKA.corrImpl,
    StateT.run_lift, simulateQ_query]
  split <;> simp

theorem runHM_liftCU_receive (P : Party) (h : CKAUState T I K) (cs : CKA.GameState Γ T) :
    runHM (CKA.oracleImpl cka Δcka tH) (StateT.lift (CKA.receiveQuery P)) h cs =
      if !(cs.canReceive P) then pure ((none, h), cs)
      else match cs.lastMsg with
        | none => pure ((none, h), cs)
        | some Tc =>
          pure ((some (), h), cs.afterReceive P (cka.receive (cs.st P) Tc).1) := by
  simp [runHM, CKA.receiveQuery, outerFull, CKA.oracleImpl, CKA.receiveImpl,
    StateT.run_lift, simulateQ_query]
  cases cs.canReceive P
  · simp
  · cases cs.lastMsg <;> simp

theorem runHM_liftCU_sendBad (P : Party) (c : CCoins) (h : CKAUState T I K)
    (cs : CKA.GameState Γ T) :
    runHM (CKA.oracleImpl cka Δcka tH) (StateT.lift (CKA.sendWithAdversaryCoinsQuery P c)) h cs =
      if !(cs.canSend P) || !decide (cs.epoch P + 1 + 2 ≤ tH) then pure ((none, h), cs)
      else
        let out := cka.send (cs.st P) c
        pure ((some out.2, h), cs.afterSend P out.1 out.2.1) := by
  by_cases h1 : cs.canSend P <;>
    simp [runHM, CKA.sendWithAdversaryCoinsQuery, outerFull, CKA.oracleImpl,
      CKA.sendWithAdversaryCoinsImpl, StateT.run_lift, simulateQ_query, h1]
  split <;> simp

theorem runHM_liftCU_sendOrChall_false (P : Party) (t : ℕ) (h : CKAUState T I K)
    (cs : CKA.GameState Γ T) (hb : cs.b = false) (hcan : cs.canSend P = true)
    (hep : cs.epoch P + 1 = t) :
    runHM (CKA.oracleImpl cka Δcka tH)
        (if t = tH then StateT.lift (CKA.challQuery P) else StateT.lift (CKA.sendQuery P)) h cs =
      (fun r =>
        let out := cka.send (cs.st P) r
        ((some out.2, h), cs.afterSend P out.1 out.2.1)) <$> ($ᵗ CCoins : ProbComp CCoins) := by
  by_cases ht : t = tH
  · subst ht
    simp [runHM, CKA.challQuery, outerFull, CKA.oracleImpl, CKA.challImpl,
      StateT.run_lift, simulateQ_query, hb, hcan, hep, map_eq_bind_pure_comp]
  · have hne : cs.epoch P + 1 ≠ tH := by omega
    simp [ht, runHM, CKA.sendQuery, outerFull, CKA.oracleImpl, CKA.sendImpl,
      StateT.run_lift, simulateQ_query, hcan, hne, map_eq_bind_pure_comp]

end RunHMCKAU

section StepLemmas13U

variable [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType CCoins] [SampleableType I] [SampleableType K]
  (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
  (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ)

@[expose] def SyncOrDoom13U (tL : Option ℕ) (tStar : ℕ)
    (sL sR : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAUState T I K) ×
      CKA.GameState Γ T) : Prop :=
  Sync13U Δcka tL sL sR ∨ (Doom13U tL tStar sL.1 ∧ Doom tL sR.1)

omit [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E] in
theorem runHM_reveal_13U (tL : Option ℕ) (tStar : ℕ) (P : Party)
    (esL esR : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAUState T I K))
    (csL csR : CKA.GameState Γ T)
    (hs : Sync13U Δcka tL (esL, csL) (esR, csR))
    (hvg : lastLeakGuessAdmissible (2 + Δcka) tL tStar = true)
    (hld : Policy.leakDoom ⟨false, tL, tStar⟩ esL.g (esL.g.afterCorr P) = false)
    (hcd : Policy.corrDoom ⟨false, tL, tStar⟩ esL.g P = false) :
    ∃ rp,
      runHM (CKA.oracleImpl cka Δcka 0)
        ((hooksCKAU cka prng fs Δcka ⟨false, none, tStar⟩).reveal esL.g P (esL.g.st P)) esL.h csL =
        pure ((some rp, esL.h), csL) ∧
      runHM (CKA.oracleImpl cka Δcka (healEpoch tL))
        ((hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩).reveal esR.g P (esR.g.st P)) esR.h csR =
        pure ((some rp, esR.h), csR) := by
  rcases hs with ⟨_, _, _, _, _, hp, hcka, _⟩
  dsimp only at hp hcka
  rcases hp P with ⟨hidL, hidR, htcurL, htcurR, hroot, hvS, hvR, hTcur, γ, hγL, hγR⟩
  have hreal : realParty (esL.g.st P) γ (esL.g.st P).root (esL.g.st P).vS (esL.g.st P).vR =
      realParty (esR.g.st P) γ (esR.g.st P).root (esR.g.st P).vS (esR.g.st P).vR := by
    simp [realParty, hidL, hidR, htcurL, htcurR, hroot, hvS, hvR, hTcur]
  refine ⟨realParty (esL.g.st P) γ (esL.g.st P).root (esL.g.st P).vS (esL.g.st P).vR, ?_, ?_⟩
  · dsimp only [hooksCKAU]; simp [hγL, runHM_pure]
  · dsimp only [hooksCKAU]
    by_cases hγc : (tL.isNone || decide (healEpoch tL + Δcka ≤ esL.g.epoch P)) = true
    · rw [hγR]; simp [hγc, runHM_pure, hreal]
    · rw [hγR]; simp only [hγc, Bool.false_eq_true, ↓reduceIte]
      rw [runHM_bind, runHM_liftCU_corr]
      have hep := epochs_of_not_corr_doom hld hcd
      rcases hep with hge | ⟨l, htL, hmaxl, _⟩
      · exfalso
        rcases validGuess_healed hvg with rfl | ⟨l, rfl, hH, hle⟩
        · simp at hγc
        · have : decide (healEpoch (some l) + Δcka ≤ esL.g.epoch P) = true :=
            decide_eq_true (by omega)
          simp [this] at hγc
      · have hltA : esL.g.epoch .A < healEpoch tL + Δcka := by
          rw [htL]; simp only [healEpoch]; omega
        have hltB : esL.g.epoch .B < healEpoch tL + Δcka := by
          rw [htL]; simp only [healEpoch]; omega
        have hltP : esL.g.epoch P < healEpoch tL + Δcka := by
          rw [htL]; simp only [healEpoch]; omega
        have hcsA := (hcka.2 .A (by simp [htL]) hltA).2
        have hcsB := (hcka.2 .B (by simp [htL]) hltB).2
        have hcsP := (hcka.2 P (by simp [htL]) hltP).1
        rw [hγL] at hcsP
        have hγeq : csR.st P = γ := Option.some.inj hcsP.symm
        have hallow : csR.allowCorr (healEpoch tL) = true := by
          unfold CKA.GameState.allowCorr
          rw [hcsA, hcsB, htL]; simp only [healEpoch]; exact decide_eq_true (by omega)
        simp [hallow, hγeq, runHM_pure, hreal]

omit [DecidableEq I] in
theorem evalEng2_corrE_13U (tL : Option ℕ) (tStar : ℕ) (b : Bool) (P : Party)
    (k : Option (PartyState Γ T Sig SS RS) →
      OracleComp (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) Bool)
    (sL sR : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAUState T I K) ×
      CKA.GameState Γ T)
    (hs : Sync13U Δcka tL sL sR)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) tL tStar = true)
    (ih : ∀ ans sL' sR', SyncOrDoom13U Δcka tL tStar sL' sR' →
      DEq (evalEng2 (CKA.oracleImpl cka Δcka 0) (hooksCKAU cka prng fs Δcka ⟨false, none, tStar⟩)
            (2 + Δcka) qep fs.maxSkip (Config.priv tStar) (polUni12 Δcka tStar) ⟨false, tL, tStar⟩
            b (k ans) sL')
          (evalEng2 (CKA.oracleImpl cka Δcka (healEpoch tL))
            (hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩)
            (2 + Δcka) qep fs.maxSkip (Config.priv tStar) ⟨false, tL, tStar⟩ ⟨false, tL, tStar⟩
            b (k ans) sR')) :
    DEq (runEM (CKA.oracleImpl cka Δcka 0)
          (corrE (hooksCKAU cka prng fs Δcka ⟨false, none, tStar⟩) (polUni12 Δcka tStar) P) sL >>=
          fun r => evalEng2 (CKA.oracleImpl cka Δcka 0)
            (hooksCKAU cka prng fs Δcka ⟨false, none, tStar⟩) (2 + Δcka) qep fs.maxSkip
            (Config.priv tStar) (polUni12 Δcka tStar) ⟨false, tL, tStar⟩ b (k r.1) r.2)
        (runEM (CKA.oracleImpl cka Δcka (healEpoch tL))
          (corrE (hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩) ⟨false, tL, tStar⟩ P) sR >>=
          fun r => evalEng2 (CKA.oracleImpl cka Δcka (healEpoch tL))
            (hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩) (2 + Δcka) qep fs.maxSkip
            (Config.priv tStar) ⟨false, tL, tStar⟩ ⟨false, tL, tStar⟩ b (k r.1) r.2) := by
  rcases sL with ⟨esL, csL⟩
  rcases sR with ⟨esR, csR⟩
  have habL : esL.abort = false := hs.1
  have habR : esR.abort = false := hs.2.1
  have he : eraseSt esL.g = eraseSt esR.g := hs.2.2.1
  have hwin := eraseSt_win he
  have hca := eraseSt_corrAllowed he P
  unfold corrE
  rw [runEM_bind, runEM_get, pure_bind, runEM_bind, runEM_get, pure_bind]
  dsimp only
  rw [habL, habR, ← hwin, ← hca]
  by_cases hguard : (esL.g.win || !esL.g.corrAllowed P) = true
  · simp only [Bool.false_or, hguard, ↓reduceIte, runEM_pure, pure_bind]
    exact ih none (esL, csL) (esR, csR) (Or.inl hs)
  · simp only [Bool.false_or, hguard, Bool.false_eq_true, ↓reduceIte]
    have he_ac := eraseSt_afterCorr he P
    have hldR_eq := eraseSt_leakDoom he he_ac ⟨false, tL, tStar⟩
    have hcdR_eq := eraseSt_corrDoom he ⟨false, tL, tStar⟩ P
    rw [← hldR_eq, ← hcdR_eq, corrDoom_polUni_eq Δcka tL tStar esL.g P]
    by_cases hdoomL : ((polUni12 Δcka tStar).leakDoom esL.g (esL.g.afterCorr P) ||
        Policy.corrDoom ⟨false, tL, tStar⟩ esL.g P) = true
    · have hdoomR : (Policy.leakDoom ⟨false, tL, tStar⟩ esL.g (esL.g.afterCorr P) ||
          Policy.corrDoom ⟨false, tL, tStar⟩ esL.g P) = true := by
        rcases Bool.or_eq_true_iff.mp hdoomL with h1 | h2
        · exact Bool.or_eq_true_iff.mpr (Or.inl (leakDoom_polUni_imp hvg _ _ h1))
        · exact Bool.or_eq_true_iff.mpr (Or.inr h2)
      simp only [hdoomL, hdoomR, ↓reduceIte, runEM_abort_pure, pure_bind]
      exact ih none ({ esL with abort := true }, csL) ({ esR with abort := true }, csR)
        (Or.inr ⟨Or.inl (Or.inl rfl), Or.inl rfl⟩)
    · simp only [hdoomL, Bool.false_eq_true, ↓reduceIte]
      rcases Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hdoomL) with ⟨hldL_f, hcd_f⟩
      by_cases hldR : Policy.leakDoom ⟨false, tL, tStar⟩ esL.g (esL.g.afterCorr P) = true
      · simp only [hldR, Bool.true_or, ↓reduceIte, runEM_abort_pure, pure_bind]
        have hhla : HasLeakAbove tL tStar (esL.g.afterCorr P) :=
          hasLeakAbove_of_leakDoom_diff esL.g (esL.g.afterCorr P) hldL_f hldR
        have hLHS : DEq
            (runEM (CKA.oracleImpl cka Δcka 0)
              (do
                match ← liftH ((hooksCKAU cka prng fs Δcka ⟨false, none, tStar⟩).reveal esL.g P (esL.g.st P)) with
                | none => abortE; pure none
                | some st => modify (fun es => { es with g := esL.g.afterCorr P }); pure (some st))
              (esL, csL) >>= fun r =>
              evalEng2 (CKA.oracleImpl cka Δcka 0)
                (hooksCKAU cka prng fs Δcka ⟨false, none, tStar⟩) (2 + Δcka) qep fs.maxSkip
                (Config.priv tStar) (polUni12 Δcka tStar) ⟨false, tL, tStar⟩ b (k r.1) r.2)
            ($ᵗ Bool : ProbComp Bool) := by
          refine (PrivL14.DEq.bind_right_supp _ fun r hr => ?_).trans (DEq.bind_const _ _)
          apply evalEng2_doom13U
          rw [runEM_bind, mem_support_bind_iff] at hr
          rcases hr with ⟨r₁, _, hr⟩
          cases hrev : r₁.1 with
          | none =>
            rw [hrev, runEM_abort_pure, support_pure, Set.mem_singleton_iff] at hr
            subst hr; exact Or.inl (Or.inl rfl)
          | some st =>
            rw [hrev, runEM_modify_pure, support_pure, Set.mem_singleton_iff] at hr
            subst hr; exact Or.inr hhla
        have hRHS : DEq
            (evalEng2 (CKA.oracleImpl cka Δcka (healEpoch tL))
              (hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩) (2 + Δcka) qep fs.maxSkip
              (Config.priv tStar) ⟨false, tL, tStar⟩ ⟨false, tL, tStar⟩ b (k none)
              ({ esR with abort := true }, csR))
            ($ᵗ Bool : ProbComp Bool) :=
          evalEng2_doom13U _ _ _ _ _ _ _ _ _ _ _ (Or.inl (Or.inl rfl))
        exact hLHS.trans hRHS.symm
      · have hldR_f : Policy.leakDoom ⟨false, tL, tStar⟩ esL.g (esL.g.afterCorr P) = false :=
          Bool.eq_false_iff.mpr hldR
        simp only [hldR_f, hcd_f, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
        rcases runHM_reveal_13U cka prng fs Δcka tL tStar P esL esR csL csR hs hvg hldR_f hcd_f with
          ⟨rp, hrevL, hrevR⟩
        rw [runEM_bind, runEM_liftH, hrevL, map_pure, pure_bind]
        dsimp only
        rw [runEM_modify_pure, pure_bind]
        rw [runEM_bind, runEM_liftH, hrevR, map_pure, pure_bind]
        dsimp only
        rw [runEM_modify_pure, pure_bind]
        apply ih (some rp)
        left
        rcases hs with ⟨_, _, _, hinv, hh, hp, hcka, hpp⟩
        exact ⟨habL, habR, he_ac, hinv.afterCorr, hh, hp, hcka, hpp⟩

@[expose] def RecvStep13U (tL : Option ℕ)
    (esL esR : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAUState T I K))
    (csR : CKA.GameState Γ T) (P : Party) (t : ℕ)
    (st'L st'R : PartyState (Option Γ) T Sig SS RS) : Prop :=
  let ep := esL.g.epoch P
  (t ≤ ep ∧ st'L.tcur = ep ∧ st'L.γ = (esL.g.st P).γ ∧
    PartyRel13U Δcka tL P ep st'L st'R) ∨
  (t = ep + 1 ∧ P.sendsIn (ep + 1) = false ∧
    st'L.id = P ∧ st'R.id = P ∧ st'L.tcur = ep + 1 ∧ st'R.tcur = ep + 1 ∧
    st'L.root = st'R.root ∧ st'L.vS = st'R.vS ∧ st'L.vR = st'R.vR ∧
    st'L.curCkaMsg = st'R.curCkaMsg ∧
    esL.g.epoch P.other = ep + 1 ∧
    ∃ γ Tc, (esL.g.st P).γ = some γ ∧
      st'L.γ = some (cka.receive γ Tc).1 ∧
      st'R.γ = (esR.g.st P).γ.map (fun g => (cka.receive g Tc).1) ∧
      (tL.isSome = true → ep < healEpoch tL + Δcka →
        csR.epoch P.other = ep + 1 ∧ csR.lastMsg = some Tc))

omit [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E] in
theorem runHM_vRecv_13U (tL : Option ℕ) (tStar : ℕ)
    (P : Party) (c : Header T × E) (rec : Option (Record M (Header T × E)))
    (esL esR : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAUState T I K))
    (csL csR : CKA.GameState Γ T)
    (hs : Sync13U Δcka tL (esL, csL) (esR, csR)) :
    (runHM (CKA.oracleImpl cka Δcka 0)
        (vRecv (hooksCKAU cka prng fs Δcka ⟨false, none, tStar⟩) esL.g P (esL.g.st P) c rec)
        esL.h csL = pure ((some none, esL.h), csL) ∧
      runHM (CKA.oracleImpl cka Δcka (healEpoch tL))
        (vRecv (hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩) esR.g P (esR.g.st P) c rec)
        esR.h csR = pure ((some none, esR.h), csR)) ∨
    ∃ st'L st'R i m,
      runHM (CKA.oracleImpl cka Δcka 0)
        (vRecv (hooksCKAU cka prng fs Δcka ⟨false, none, tStar⟩) esL.g P (esL.g.st P) c rec)
        esL.h csL = pure ((some (some (st'L, c.1.1, i, m)), esL.h), csL) ∧
      runHM (CKA.oracleImpl cka Δcka (healEpoch tL))
        (vRecv (hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩) esR.g P (esR.g.st P) c rec)
        esR.h csR = pure ((some (some (st'R, c.1.1, i, m)), esR.h), csR) ∧
      RecvStep13U cka Δcka tL esL esR csR P c.1.1 st'L st'R := by
  rcases hs with ⟨_, _, _, _, hh, hp, _, hpp⟩
  dsimp only at hh hp hpp
  rcases hp P with ⟨hidL, hidR, htcurL, htcurR, hroot, hvS, hvR, hTcur, γ, hγL, hγR⟩
  unfold vRecv
  dsimp only
  rw [hidL, hidR, htcurL, htcurR]
  by_cases hbad : (P.sendsIn c.1.1 || decide (esL.g.epoch P + 1 < c.1.1)) = true
  · left; simp [hbad, runHM_pure]
  · simp only [hbad, Bool.false_eq_true, ↓reduceIte]
    have hbad' : P.sendsIn c.1.1 = false ∧ c.1.1 ≤ esL.g.epoch P + 1 := by
      rcases Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hbad) with ⟨h1, h2⟩
      exact ⟨h1, by have := of_decide_eq_false h2; omega⟩
    by_cases hstep : c.1.1 = esL.g.epoch P + 1
    · simp only [hstep, ↓reduceIte]
      cases hTn : c.1.2 with
      | none => left; simp [runHM_pure]
      | some Tn =>
        have hsends : P.sendsIn (esL.g.epoch P + 1) = false := by
          rw [← hstep]; exact hbad'.1
        rcases hpp.recv_step P with hcNone | ⟨_, hepO, Tc, Ik, hcL, hcsO⟩
        · left
          dsimp only [hooksCKAU]
          simp [runHM_bind, runHM_get, ← hh, hcNone, runHM_pure]
        · by_cases hTc : Tc = Tn
          · subst hTc
            dsimp only [hooksCKAU]
            simp only [runHM_bind, runHM_get, pure_bind, ← hh, hcL, ↓reduceIte, runHM_pure,
              Function.update_self, ← hroot]
            set kEp := if esL.g.epoch P + 1 = tStar then
                match esL.h.2 with
                | none => (prng.up (esL.g.st P).root Ik).2
                | some kU => kU
              else (prng.up (esL.g.st P).root Ik).2
            cases hfs : fs.receive (fs.initReceiver kEp) c.1 c.2 with
            | none => left; simp [runHM_pure]
            | some res =>
              rcases res with ⟨v', i, m⟩
              right
              refine ⟨_, _, i, m, by rw [runHM_pure], by rw [runHM_pure], Or.inr ?_⟩
              refine ⟨rfl, hsends, rfl, rfl, rfl, rfl, rfl, hvS, ?_, hTcur, hepO,
                γ, Tc, hγL, ?_, rfl, hcsO⟩
              · rw [hvR]
              · simp [hγL]
          · left
            dsimp only [hooksCKAU]
            simp [runHM_bind, runHM_get, ← hh, hcL, hTc, runHM_pure]
    · have hle : c.1.1 ≤ esL.g.epoch P := by omega
      simp only [hstep, ↓reduceIte, pure_bind, hvR]
      cases hvRt : (esR.g.st P).vR c.1.1 with
      | none => left; simp [runHM_pure]
      | some v =>
        dsimp only [hooksCKAU]
        rw [runHM_bind, runHM_pure, pure_bind, runHM_bind, runHM_pure, pure_bind]
        dsimp only
        cases hfs : fs.receive v c.1 c.2 with
        | none => left; simp [runHM_pure]
        | some res =>
          rcases res with ⟨v', i, m⟩
          right
          refine ⟨_, _, i, m, by rw [runHM_pure], by rw [runHM_pure], Or.inl ?_⟩
          refine ⟨hle, htcurL, rfl, hidL, hidR, htcurL, htcurR, hroot, hvS, rfl, hTcur,
            γ, hγL, hγR⟩

omit [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E] in
theorem runEM_commitE_13U (tL : Option ℕ) (tStar : ℕ) (P : Party) (pos : Pos)
    (st'L st'R : PartyState (Option Γ) T Sig SS RS)
    (esL esR : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAUState T I K))
    (csL csR : CKA.GameState Γ T)
    (hs : Sync13U Δcka tL (esL, csL) (esR, csR))
    (hr : RecvStep13U cka Δcka tL esL esR csR P pos.epoch st'L st'R) :
    ∃ s₁L s₁R csR',
      runEM (CKA.oracleImpl cka Δcka 0)
        (commitE (hooksCKAU cka prng fs Δcka ⟨false, none, tStar⟩) esL.g P (esL.g.st P) st'L pos)
        (esL, csL) = pure (some s₁L, (esL, csL)) ∧
      runEM (CKA.oracleImpl cka Δcka (healEpoch tL))
        (commitE (hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩) esR.g P (esR.g.st P) st'R pos)
        (esR, csR) = pure (some s₁R, (esR, csR')) ∧
      Sync13U Δcka tL ({ esL with g := s₁L }, csL) ({ esR with g := s₁R }, csR') := by
  rcases hs with ⟨habL, habR, he, hinv, hh, hp, hcka, hpp⟩
  dsimp only at habL habR he hinv hh hp hcka hpp
  rcases hp P with ⟨hidL, hidR, htcurL, htcurR, hroot, hvS, hvR, hTcur, γ, hγL, hγR⟩
  have hcommL :
      runEM (CKA.oracleImpl cka Δcka 0)
        (commitE (hooksCKAU cka prng fs Δcka ⟨false, none, tStar⟩) esL.g P (esL.g.st P) st'L pos)
        (esL, csL) = pure (some (esL.g.accept P st'L pos), (esL, csL)) := by
    unfold commitE
    dsimp only [hooksCKAU]
    simp [runEM_bind, runEM_liftH, hγL, runHM_pure, runEM_pure, accept_update_st]
  rcases hr with ⟨hle, hst_tcur, hst_γ, hp'⟩ |
    ⟨ht_step, hsends, hidL', hidR', htcurL', htcurR', hroot', hvS', hvR', hTcur',
      hepO, γ0, Tc, hγL0, hst_γL, hst_γR, hcsO⟩
  · have hnotlt : ¬((esR.g.st P).tcur < st'R.tcur) := by
      have := hp'.2.2.2.1; omega
    have hcommR :
        runEM (CKA.oracleImpl cka Δcka (healEpoch tL))
          (commitE (hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩) esR.g P (esR.g.st P) st'R pos)
          (esR, csR) = pure (some (esR.g.accept P st'R pos), (esR, csR)) := by
      unfold commitE
      dsimp only [hooksCKAU]
      simp [runEM_bind, runEM_liftH, hnotlt, runHM_pure, runEM_pure, accept_update_st]
    refine ⟨esL.g.accept P st'L pos, esR.g.accept P st'R pos, csR, hcommL, hcommR, ?_⟩
    have hep_eq : ∀ Q, (esL.g.accept P st'L pos).epoch Q = esL.g.epoch Q := by
      intro Q; simp only [SM.GameState.accept, SM.GameState.delete]
      by_cases hQP : Q = P
      · subst hQP; simp [Function.update_self, Nat.max_eq_left hle]
      · simp [Function.update_of_ne hQP]
    have hγ_eq : ∀ Q, ((esL.g.accept P st'L pos).st Q).γ = (esL.g.st Q).γ := by
      intro Q; simp only [SM.GameState.accept, SM.GameState.delete]
      by_cases hQP : Q = P
      · subst hQP; simp [Function.update_self, hst_γ]
      · simp [Function.update_of_ne hQP]
    refine ⟨habL, habR, eraseSt_accept he P st'L st'R pos, hinv.accept, hh, ?_, ?_, ?_⟩
    · intro Q; rw [hep_eq Q]; simp only [SM.GameState.accept, SM.GameState.delete]
      by_cases hQP : Q = P
      · subst hQP; simp [Function.update_self]; exact hp'
      · simp [Function.update_of_ne hQP]; exact hp Q
    · refine ⟨hcka.1, fun Q htL hlt => ?_⟩
      rw [hep_eq Q] at hlt ⊢; rw [hγ_eq Q]; exact hcka.2 Q htL hlt
    · refine ⟨fun t' ht' => ?_, ?_⟩
      · rw [hep_eq .A, hep_eq .B] at ht'; exact hpp.1 t' ht'
      · rcases hpp.2 with h1 | ⟨Q, t0, Tc0, Ik0, h1, h2, h3, h4, h5⟩
        · left; rw [hep_eq .A, hep_eq .B]; exact h1
        · right; refine ⟨Q, t0, Tc0, Ik0, h1, ?_, ?_, h4, h5⟩
          · rw [hep_eq Q]; exact h2
          · rw [hep_eq Q.other]; exact h3
  · set ep := esL.g.epoch P
    have hγ0_eq : γ = γ0 := Option.some.inj (hγL.symm.trans hγL0)
    subst γ0
    have hlt_tcur : (esR.g.st P).tcur < st'R.tcur := by omega
    have hmax_ep : max (esL.g.epoch P) pos.epoch = ep + 1 := by omega
    have hep_acc : ∀ (stL : PartyState (Option Γ) T Sig SS RS) (Q : Party),
        (esL.g.accept P stL pos).epoch Q = if Q = P then ep + 1 else esL.g.epoch Q := by
      intro stL Q; simp only [SM.GameState.accept, SM.GameState.delete]
      by_cases hQP : Q = P
      · subst hQP; simp [Function.update_self, hmax_ep]
      · simp [hQP]
    have hAB_acc : (esL.g.accept P st'L pos).epoch .A = (esL.g.accept P st'L pos).epoch .B := by
      rw [hep_acc st'L .A, hep_acc st'L .B]
      cases P <;> simp [Party.other] at hepO ⊢ <;> omega
    have hmax_acc : max ((esL.g.accept P st'L pos).epoch .A) ((esL.g.accept P st'L pos).epoch .B) =
        max (esL.g.epoch .A) (esL.g.epoch .B) := by
      rw [hep_acc st'L .A, hep_acc st'L .B]
      cases P <;> simp [Party.other] at hepO ⊢ <;> omega
    by_cases hγc : (tL.isNone || decide (healEpoch tL + Δcka ≤ ep)) = true
    · have hγR_some : (esR.g.st P).γ = some γ := by rw [hγR]; simp [hγc]
      have hcommR :
          runEM (CKA.oracleImpl cka Δcka (healEpoch tL))
            (commitE (hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩) esR.g P (esR.g.st P) st'R pos)
            (esR, csR) = pure (some (esR.g.accept P st'R pos), (esR, csR)) := by
        unfold commitE
        dsimp only [hooksCKAU]
        simp [runEM_bind, runEM_liftH, hγR_some, runHM_pure, runEM_pure, accept_update_st]
      refine ⟨esL.g.accept P st'L pos, esR.g.accept P st'R pos, csR, hcommL, hcommR, ?_⟩
      have hγc' : (tL.isNone || decide (healEpoch tL + Δcka ≤ ep + 1)) = true := by
        rcases Bool.or_eq_true_iff.mp hγc with h1 | h2
        · simp [h1]
        · have := decide_eq_true_eq.mp h2
          exact Bool.or_eq_true_iff.mpr (Or.inr (decide_eq_true (by omega)))
      refine ⟨habL, habR, eraseSt_accept he P st'L st'R pos, hinv.accept, hh, ?_, ?_, ?_⟩
      · intro Q; rw [hep_acc st'L Q]; simp only [SM.GameState.accept, SM.GameState.delete]
        by_cases hQP : Q = P
        · subst hQP; simp only [↓reduceIte, Function.update_self]
          refine ⟨hidL', hidR', htcurL', htcurR', hroot', hvS', hvR', hTcur',
            (cka.receive γ Tc).1, hst_γL, ?_⟩
          rw [hst_γR, hγR_some, hγc']; rfl
        · simp [hQP]; exact hp Q
      · refine ⟨hcka.1, fun Q htL hlt => ?_⟩
        rw [hep_acc st'L Q] at hlt ⊢
        by_cases hQP : Q = P
        · subst Q; simp only [↓reduceIte] at hlt
          cases tL with
          | none => simp at htL
          | some l => simp [decide_eq_false (by omega : ¬(healEpoch (some l) + Δcka ≤ ep))] at hγc
        · simp only [hQP, ↓reduceIte, SM.GameState.accept, SM.GameState.delete,
            Function.update_of_ne hQP] at hlt ⊢
          exact hcka.2 Q htL hlt
      · refine ⟨fun t' ht' => by rw [hmax_acc] at ht'; exact hpp.1 t' ht', Or.inl hAB_acc⟩
    · have htL_some : tL.isSome = true ∧ ep < healEpoch tL + Δcka := by
        cases tL with
        | none => simp at hγc
        | some l =>
          simp only [Option.isSome_some, true_and]
          simp only [Option.isNone_some, Bool.false_or, decide_eq_true_eq, not_le] at hγc
          exact hγc
      have hγR_none : (esR.g.st P).γ = none := by rw [hγR]; simp [hγc]
      have hcsP := hcka.2 P htL_some.1 htL_some.2
      have hcsγ : csR.st P = γ := Option.some.inj (hcsP.1.symm.trans hγL)
      rcases hcsO htL_some.1 htL_some.2 with ⟨hcsO_ep, hcs_last⟩
      have hcanR : csR.canReceive P = true := by
        simp only [CKA.GameState.canReceive, beq_iff_eq]
        rw [hcsO_ep, hcsP.2]
      have hlt_ep : (esR.g.st P).tcur < ep + 1 := by omega
      set csR' := csR.afterReceive P (cka.receive γ Tc).1
      by_cases hfin : healEpoch tL + Δcka ≤ ep + 1
      · have hfinished : (csR.afterReceive P (cka.receive γ Tc).1).finished Δcka (healEpoch tL) P = true := by
          unfold CKA.GameState.finished
          simp [CKA.GameState.afterReceive, hcsP.2, ep, hfin]
        have hcsR'_st : (csR.afterReceive P (cka.receive γ Tc).1).st P = (cka.receive γ Tc).1 := by
          simp [CKA.GameState.afterReceive]
        set st'R_fin := { st'R with γ := some (cka.receive γ Tc).1 }
        have hcommR :
            runEM (CKA.oracleImpl cka Δcka (healEpoch tL))
              (commitE (hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩) esR.g P (esR.g.st P) st'R pos)
              (esR, csR) = pure (some (esR.g.accept P st'R_fin pos), (esR, csR')) := by
          unfold commitE
          dsimp only [hooksCKAU, Mode.tH]
          rw [runEM_bind, runEM_liftH]
          simp only [htcurR', hlt_ep, decide_true, hγR_none, Option.isNone_none, Bool.and_self,
            ↓reduceIte, hfin]
          rw [runHM_bind, runHM_liftCU_receive]
          simp only [hcanR, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hcs_last, hcsγ,
            pure_bind]
          rw [runHM_bind, runHM_liftCU_corr]
          simp [hfinished, hcsR'_st, ← htcurR', runHM_pure, runEM_pure, accept_update_st, st'R_fin, csR']
        refine ⟨esL.g.accept P st'L pos, esR.g.accept P st'R_fin pos, csR', hcommL, hcommR, ?_⟩
        refine ⟨habL, habR, eraseSt_accept he P st'L st'R_fin pos, hinv.accept, hh, ?_, ?_, ?_⟩
        · intro Q; rw [hep_acc st'L Q]; simp only [SM.GameState.accept, SM.GameState.delete]
          by_cases hQP : Q = P
          · subst hQP; simp only [↓reduceIte, Function.update_self]
            have hdec : decide (healEpoch tL + Δcka ≤ ep + 1) = true := decide_eq_true hfin
            refine ⟨hidL', hidR', htcurL', htcurR', hroot', hvS', hvR', hTcur',
              (cka.receive γ Tc).1, hst_γL, ?_⟩
            simp [st'R_fin, hdec]
          · simp [hQP]; exact hp Q
        · refine ⟨hcka.1, fun Q htL hlt => ?_⟩
          rw [hep_acc st'L Q] at hlt ⊢
          by_cases hQP : Q = P
          · subst hQP; simp only [↓reduceIte] at hlt; omega
          · simp only [hQP, ↓reduceIte, SM.GameState.accept, SM.GameState.delete,
              Function.update_of_ne hQP] at hlt ⊢
            have hQ := hcka.2 Q htL hlt
            simp [csR', CKA.GameState.afterReceive, Function.update_of_ne hQP, hQ.1, hQ.2]
        · refine ⟨fun t' ht' => by rw [hmax_acc] at ht'; exact hpp.1 t' ht', Or.inl hAB_acc⟩
      · have hcommR :
            runEM (CKA.oracleImpl cka Δcka (healEpoch tL))
              (commitE (hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩) esR.g P (esR.g.st P) st'R pos)
              (esR, csR) = pure (some (esR.g.accept P st'R pos), (esR, csR')) := by
          unfold commitE
          dsimp only [hooksCKAU, Mode.tH]
          rw [runEM_bind, runEM_liftH]
          simp only [htcurR', hlt_ep, decide_true, hγR_none, Option.isNone_none, Bool.and_self,
            ↓reduceIte, hfin]
          rw [runHM_bind, runHM_liftCU_receive]
          simp [hcanR, hcs_last, hcsγ, runHM_pure, runEM_pure, accept_update_st, csR']
        refine ⟨esL.g.accept P st'L pos, esR.g.accept P st'R pos, csR', hcommL, hcommR, ?_⟩
        refine ⟨habL, habR, eraseSt_accept he P st'L st'R pos, hinv.accept, hh, ?_, ?_, ?_⟩
        · intro Q; rw [hep_acc st'L Q]; simp only [SM.GameState.accept, SM.GameState.delete]
          by_cases hQP : Q = P
          · subst hQP; simp only [↓reduceIte, Function.update_self]
            have hnone : tL.isNone = false := by cases tL <;> simp at htL_some ⊢
            have hdec : decide (healEpoch tL + Δcka ≤ ep + 1) = false := decide_eq_false hfin
            refine ⟨hidL', hidR', htcurL', htcurR', hroot', hvS', hvR', hTcur',
              (cka.receive γ Tc).1, hst_γL, ?_⟩
            rw [hst_γR, hγR_none, hnone, hdec]; rfl
          · simp [hQP]; exact hp Q
        · refine ⟨hcka.1, fun Q htL hlt => ?_⟩
          rw [hep_acc st'L Q] at hlt ⊢
          by_cases hQP : Q = P
          · subst hQP; simp [SM.GameState.accept, SM.GameState.delete, csR',
              CKA.GameState.afterReceive, hst_γL, hcsP.2, ep]
          · simp only [hQP, ↓reduceIte, SM.GameState.accept, SM.GameState.delete,
              Function.update_of_ne hQP] at hlt ⊢
            have hQ := hcka.2 Q htL hlt
            simp [csR', CKA.GameState.afterReceive, Function.update_of_ne hQP, hQ.1, hQ.2]
        · refine ⟨fun t' ht' => by rw [hmax_acc] at ht'; exact hpp.1 t' ht', Or.inl hAB_acc⟩

omit [DecidableEq I] [Inhabited E] in
theorem runEM_deliverE_13U (tL : Option ℕ) (tStar : ℕ) (q : Party × (Header T × E))
    (esL esR : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAUState T I K))
    (csL csR : CKA.GameState Γ T)
    (hs : Sync13U Δcka tL (esL, csL) (esR, csR)) :
    ∃ out sL' sR',
      runEM (CKA.oracleImpl cka Δcka 0)
        (deliverE (hooksCKAU cka prng fs Δcka ⟨false, none, tStar⟩) fs.maxSkip (Config.priv tStar) q)
        (esL, csL) = pure (out, sL') ∧
      runEM (CKA.oracleImpl cka Δcka (healEpoch tL))
        (deliverE (hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩) fs.maxSkip (Config.priv tStar) q)
        (esR, csR) = pure (out, sR') ∧
      Sync13U Δcka tL sL' sR' := by
  rcases q with ⟨P, c⟩
  have habL : esL.abort = false := hs.1
  have habR : esR.abort = false := hs.2.1
  have he : eraseSt esL.g = eraseSt esR.g := hs.2.2.1
  have hinv : GameInv esL.g := hs.2.2.2.1
  have hwin : esR.g.win = esL.g.win := (eraseSt_win he).symm
  have htr_eq : esR.g.inTransit P.other c = esL.g.inTransit P.other c :=
    (eraseSt_inTransit he P.other c).symm
  unfold deliverE; dsimp only
  rw [runEM_bind, runEM_get, runEM_bind, runEM_get]
  simp only [pure_bind, habL, habR, Bool.false_or, hwin]
  by_cases hw : esL.g.win = true
  · refine ⟨none, (esL, csL), (esR, csR), ?_, ?_, hs⟩ <;> simp [hw, runEM_pure]
  · simp only [hw, Bool.false_eq_true, ↓reduceIte, htr_eq]
    cases htr : esL.g.inTransit P.other c with
    | none => refine ⟨none, (esL, csL), (esR, csR), ?_, ?_, hs⟩ <;> simp [runEM_pure]
    | some r =>
      dsimp only
      have hmust_eq : esR.g.mustBeCorrect fs.maxSkip P r = esL.g.mustBeCorrect fs.maxSkip P r :=
        (eraseSt_mustBeCorrect he fs.maxSkip P r).symm
      rw [runEM_bind, runEM_liftH, runEM_bind, runEM_liftH]
      rcases runHM_vRecv_13U cka prng fs Δcka tL tStar P c (some r) esL esR csL csR hs with
        ⟨hL, hR⟩ | ⟨st'L, st'R, i, m, hL, hR, hstep⟩
      · rw [hL, hR]; simp only [map_pure, pure_bind, hmust_eq]
        by_cases hmust : ((Config.priv (Msg := M) tStar).deliverWin && esL.g.mustBeCorrect fs.maxSkip P r) = true
        · refine ⟨some .rejected, ({ esL with g := { esL.g with win := true } }, csL),
            ({ esR with g := { esR.g with win := true } }, csR), ?_, ?_, hs.set_win⟩ <;>
            simp [hmust, runEM_map_modify]
        · refine ⟨some .rejected, (esL, csL), (esR, csR), ?_, ?_, hs⟩ <;> simp [hmust, runEM_pure]
      · rw [hL, hR]; simp only [map_pure, pure_bind]
        have hr_ep : r.pos.epoch = c.1.1 := hinv.inTransit_epoch htr
        have hstep' : RecvStep13U cka Δcka tL esL esR csR P r.pos.epoch st'L st'R := hr_ep ▸ hstep
        rcases runEM_commitE_13U cka prng fs Δcka tL tStar P r.pos st'L st'R esL esR csL csR hs hstep' with
          ⟨g'L, g'R, csR', hcommL, hcommR, hs'⟩
        rw [runEM_bind, hcommL, runEM_bind, hcommR]
        simp only [pure_bind, hmust_eq]
        have hchall_eq : esR.g.chall = esL.g.chall := (eraseSt_chall he).symm
        rw [hchall_eq]
        set bad := ((Config.priv (Msg := M) tStar).deliverWin && esL.g.mustBeCorrect fs.maxSkip P r) &&
          !(decide ((c.1.1, i, m) = (r.pos.epoch, r.pos.idx, r.msg)))
        by_cases hbad : bad = true
        · refine ⟨some (.accepted c.1.1 i (if esL.g.chall.contains r.pos then none else some m)),
            ({ esL with g := { g'L with win := true } }, csL),
            ({ esR with g := { g'R with win := true } }, csR'), ?_, ?_, hs'.set_win⟩ <;>
            simp [bad, hbad, runEM_map_modify]
        · refine ⟨some (.accepted c.1.1 i (if esL.g.chall.contains r.pos then none else some m)),
            ({ esL with g := g'L }, csL), ({ esR with g := g'R }, csR'), ?_, ?_, hs'⟩ <;>
            simp [bad, hbad, runEM_map_modify]

omit [DecidableEq M] [DecidableEq I] [Inhabited E] in
theorem runEM_injectE_13U (tL : Option ℕ) (tStar : ℕ) (q : Party × (Header T × E))
    (esL esR : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAUState T I K))
    (csL csR : CKA.GameState Γ T)
    (hs : Sync13U Δcka tL (esL, csL) (esR, csR)) :
    ∃ out sL' sR',
      runEM (CKA.oracleImpl cka Δcka 0)
        (injectE (hooksCKAU cka prng fs Δcka ⟨false, none, tStar⟩) (2 + Δcka) qep (Config.priv tStar) q)
        (esL, csL) = pure (out, sL') ∧
      runEM (CKA.oracleImpl cka Δcka (healEpoch tL))
        (injectE (hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩) (2 + Δcka) qep (Config.priv tStar) q)
        (esR, csR) = pure (out, sR') ∧
      Sync13U Δcka tL sL' sR' := by
  rcases q with ⟨P, c⟩
  have habL : esL.abort = false := hs.1
  have habR : esR.abort = false := hs.2.1
  have he : eraseSt esL.g = eraseSt esR.g := hs.2.2.1
  have hwin : esR.g.win = esL.g.win := (eraseSt_win he).symm
  have htr_eq : esR.g.inTransit P.other c = esL.g.inTransit P.other c :=
    (eraseSt_inTransit he P.other c).symm
  have hsafe_eq : esR.g.safeInj (2 + Δcka) = esL.g.safeInj (2 + Δcka) :=
    (eraseSt_safeInj he (2 + Δcka)).symm
  unfold injectE; dsimp only
  rw [runEM_bind, runEM_get, runEM_bind, runEM_get]
  simp only [pure_bind, habL, habR, Bool.false_or, hwin, htr_eq, hsafe_eq]
  by_cases hg : ((esL.g.win || (esL.g.inTransit P.other c).isSome) ||
      !esL.g.safeInj (2 + Δcka)) = true
  · refine ⟨none, (esL, csL), (esR, csR), ?_, ?_, hs⟩ <;>
      (rw [ite_bool_true hg]; exact runEM_pure _ _ _)
  · simp only [hg, Bool.false_eq_true, ↓reduceIte]
    rw [runEM_bind, runEM_liftH, runEM_bind, runEM_liftH]
    rcases runHM_vRecv_13U cka prng fs Δcka tL tStar P c none esL esR csL csR hs with
      ⟨hL, hR⟩ | ⟨st'L, st'R, i, m, hL, hR, hstep⟩
    · rw [hL, hR]
      refine ⟨some .rejected, (esL, csL), (esR, csR), ?_, ?_, hs⟩ <;>
        simp [map_pure, pure_bind, runEM_pure]
    · rw [hL, hR]; simp only [map_pure, pure_bind]
      by_cases hqep : qep + 1 < c.1.1
      · refine ⟨some .rejected, (esL, csL), (esR, csR), ?_, ?_, hs⟩ <;> simp [hqep, runEM_pure]
      · simp only [hqep, ↓reduceIte]
        set pos : Pos := ⟨P.other, c.1.1, i⟩
        have htriv_eq : esR.g.trivial (2 + Δcka) pos = esL.g.trivial (2 + Δcka) pos :=
          (eraseSt_trivial he (2 + Δcka) pos).symm
        rw [htriv_eq]
        by_cases htriv : esL.g.trivial (2 + Δcka) pos = true
        · simp only [htriv, ↓reduceIte]
          rcases runEM_commitE_13U cka prng fs Δcka tL tStar P pos st'L st'R esL esR csL csR hs hstep with
            ⟨g'L, g'R, csR', hcommL, hcommR, hs'⟩
          rw [runEM_bind, hcommL, runEM_bind, hcommR]
          refine ⟨some (.accepted c.1.1 i (some m)),
            ({ esL with g := g'L }, csL), ({ esR with g := g'R }, csR'), ?_, ?_, hs'⟩ <;>
            simp [pure_bind, runEM_map_modify]
        · simp only [htriv, Bool.false_eq_true, ↓reduceIte]
          by_cases hfull : (Config.priv (Msg := M) tStar).injectFull c.1.1 = true
          · refine ⟨some .rejected, ({ esL with g := { esL.g with win := true } }, csL),
              ({ esR with g := { esR.g with win := true } }, csR), ?_, ?_, hs.set_win⟩ <;>
              simp [hfull, runEM_map_modify]
          · refine ⟨some .rejected, (esL, csL), (esR, csR), ?_, ?_, hs⟩ <;> simp [hfull, runEM_pure]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType CCoins] [SampleableType I] [SampleableType K] in
theorem sync13U_after_same_send (tL : Option ℕ)
    (P : Party) (m : M) (c : Header T × E) (rcoins : Option CCoins) (isChall : Bool)
    (st'L st'R : PartyState (Option Γ) T Sig SS RS)
    (s₁L s₁R : Ctx (Option Γ) T Sig SS RS M E)
    (esL esR : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAUState T I K))
    (csL csR : CKA.GameState Γ T)
    (hs : Sync13U Δcka tL (esL, csL) (esR, csR))
    (hepL : esL.g.epMgmt (2 + Δcka) qep P rcoins.isSome = some s₁L)
    (hepR : esR.g.epMgmt (2 + Δcka) qep P rcoins.isSome = some s₁R)
    (hsends : P.sendsIn (esL.g.epoch P + 1) = false)
    (hc_ep : c.1.1 = esL.g.epoch P)
    (hp' : PartyRel13U Δcka tL P (esL.g.epoch P) st'L st'R)
    (hγ_eqP : st'L.γ = (esL.g.st P).γ) :
    let recL : Record M (Header T × E) := ⟨⟨P, s₁L.epoch P, s₁L.idx P + 1⟩, m, c⟩
    let recR : Record M (Header T × E) := ⟨⟨P, s₁R.epoch P, s₁R.idx P + 1⟩, m, c⟩
    Sync13U Δcka tL
      ({ esL with g := s₁L.record (2 + Δcka) P st'L recL isChall }, csL)
      ({ esR with g := s₁R.record (2 + Δcka) P st'R recR isChall }, csR) := by
  intro recL recR
  rcases hs with ⟨habL, habR, he, hinv, hh, hp, hcka, hpp⟩
  dsimp only at habL habR he hinv hh hp hcka hpp
  have he₁ : eraseSt s₁L = eraseSt s₁R := by
    rcases eraseSt_epMgmt_some he hepL with ⟨s₁R', hepR', he₁, -, -⟩
    rw [hepR] at hepR'; injection hepR' with hepR'; subst s₁R'; exact he₁
  have hs₁L_eq := epMgmt_sendsIn_false hsends hepL
  have hstL_s₁ := epMgmt_st hepL
  have hstR_s₁ := epMgmt_st hepR
  have hep_s₁ : ∀ Q, s₁L.epoch Q = esL.g.epoch Q := by
    intro Q; rw [hs₁L_eq]
  have hrec_eq : recR = recL := by
    simp [recL, recR, eraseSt_epoch he₁, eraseSt_idx he₁]
  have he_rec : eraseSt (s₁L.record (2 + Δcka) P st'L recL isChall) =
      eraseSt (s₁R.record (2 + Δcka) P st'R recR isChall) := by
    rw [hrec_eq]; exact eraseSt_record he₁ (2 + Δcka) P st'L st'R recL isChall
  have hep_rec : ∀ Q, (s₁L.record (2 + Δcka) P st'L recL isChall).epoch Q = esL.g.epoch Q := by
    intro Q; exact hep_s₁ Q
  have hrec_ep : recL.ct.1.1 = recL.pos.epoch := by simp [recL, hc_ep, hep_s₁ P]
  refine ⟨habL, habR, he_rec, (hinv.epMgmt hepL).record hrec_ep, hh, ?_, ?_, ?_⟩
  · intro Q; rw [hep_rec Q]; simp only [SM.GameState.record]
    by_cases hQP : Q = P
    · subst Q; simp [Function.update_self]; exact hp'
    · simp [Function.update_of_ne hQP, hstL_s₁, hstR_s₁]; exact hp Q
  · refine ⟨hcka.1, fun Q htL hlt => ?_⟩
    rw [hep_rec Q] at hlt ⊢; simp only [SM.GameState.record]
    by_cases hQP : Q = P
    · subst Q; simp [Function.update_self, hγ_eqP]; exact hcka.2 P htL hlt
    · simp [Function.update_of_ne hQP, hstL_s₁]; exact hcka.2 Q htL hlt
  · refine ⟨fun t' ht' => ?_, ?_⟩
    · rw [hep_rec .A, hep_rec .B] at ht'; exact hpp.1 t' ht'
    · rcases hpp.2 with h1 | ⟨Q, t0, Tc0, Ik0, h1, h2, h3, h4, h5⟩
      · left; rw [hep_rec .A, hep_rec .B]; exact h1
      · right; refine ⟨Q, t0, Tc0, Ik0, h1, ?_, ?_, h4, h5⟩
        · rw [hep_rec Q]; exact h2
        · rw [hep_rec Q.other]; exact h3

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType CCoins] [SampleableType I] [SampleableType K] in
theorem sync13U_after_new_send (tL : Option ℕ)
    (P : Party) (m : M) (rcoins : Option CCoins) (isChall : Bool)
    (Tc : T) (Ik : I) (kEpoch : K) (kOpt1 : Option K) (γ' : Γ) (γR' : Option Γ)
    (s₁L s₁R : Ctx (Option Γ) T Sig SS RS M E)
    (esL esR : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAUState T I K))
    (csL csR csR' : CKA.GameState Γ T)
    (hs : Sync13U Δcka tL (esL, csL) (esR, csR))
    (hepL : esL.g.epMgmt (2 + Δcka) qep P rcoins.isSome = some s₁L)
    (hepR : esR.g.epMgmt (2 + Δcka) qep P rcoins.isSome = some s₁R)
    (hsends : P.sendsIn (esL.g.epoch P + 1) = true)
    (hγR' : γR' = if tL.isNone || decide (healEpoch tL + Δcka ≤ esL.g.epoch P + 1) then some γ' else none)
    (hcs_b : csR'.b = false)
    (hcs_P : tL.isSome = true → esL.g.epoch P + 1 < healEpoch tL + Δcka →
      csR'.st P = γ' ∧ csR'.epoch P = esL.g.epoch P + 1)
    (hcs_O : tL.isSome = true → esL.g.epoch P.other < healEpoch tL + Δcka →
      csR'.st P.other = csR.st P.other ∧ csR'.epoch P.other = csR.epoch P.other)
    (hcs_last : tL.isSome = true → esL.g.epoch P < healEpoch tL + Δcka →
      csR'.epoch P = esL.g.epoch P + 1 ∧ csR'.lastMsg = some Tc) :
    let ep := esL.g.epoch P
    let σ' := (prng.up (esL.g.st P).root Ik).1
    let hdr : Header T := (ep + 1, some Tc)
    let fso := fs.send (fs.initSender kEpoch) hdr m
    let st'L : PartyState (Option Γ) T Sig SS RS :=
      { s₁L.st P with tcur := ep + 1, γ := some γ', curCkaMsg := some Tc, root := σ', vS := some fso.1 }
    let st'R : PartyState (Option Γ) T Sig SS RS :=
      { s₁R.st P with tcur := ep + 1, γ := γR', curCkaMsg := some Tc, root := σ', vS := some fso.1 }
    let recL : Record M (Header T × E) := ⟨⟨P, s₁L.epoch P, s₁L.idx P + 1⟩, m, (hdr, fso.2)⟩
    let recR : Record M (Header T × E) := ⟨⟨P, s₁R.epoch P, s₁R.idx P + 1⟩, m, (hdr, fso.2)⟩
    let h' : CKAUState T I K := ({ cache := Function.update esL.h.1.cache (ep + 1) (some (Tc, Ik)) }, kOpt1)
    Sync13U Δcka tL
      ({ esL with g := s₁L.record (2 + Δcka) P st'L recL isChall, h := h' }, csL)
      ({ esR with g := s₁R.record (2 + Δcka) P st'R recR isChall, h := h' }, csR') := by
  intro ep σ' hdr fso st'L st'R recL recR h'
  rcases hs with ⟨habL, habR, he, hinv, hh, hp, hcka, hpp⟩
  dsimp only at habL habR he hinv hh hp hcka hpp
  have hAB : esL.g.epoch .A = esL.g.epoch .B := hpp.synced_of_sendsIn hsends
  have hepO_eq : esL.g.epoch P.other = ep := by
    cases P <;> simp [Party.other, ep, hAB]
  have he₁ : eraseSt s₁L = eraseSt s₁R := by
    rcases eraseSt_epMgmt_some he hepL with ⟨s₁R', hepR', he₁, -, -⟩
    rw [hepR] at hepR'; injection hepR' with hepR'; subst s₁R'; exact he₁
  have hs₁L_eq := epMgmt_sendsIn_true hsends hepL
  have hstL_s₁ := epMgmt_st hepL
  have hstR_s₁ := epMgmt_st hepR
  have hep_s₁ : ∀ Q, s₁L.epoch Q = if Q = P then ep + 1 else esL.g.epoch Q := by
    intro Q; rw [hs₁L_eq]; dsimp only
    by_cases hQP : Q = P
    · subst Q; simp [Function.update_self, ep]
    · simp [hQP]
  have hrec_eq : recR = recL := by
    simp [recL, recR, eraseSt_epoch he₁, eraseSt_idx he₁]
  have he_rec : eraseSt (s₁L.record (2 + Δcka) P st'L recL isChall) =
      eraseSt (s₁R.record (2 + Δcka) P st'R recR isChall) := by
    rw [hrec_eq]; exact eraseSt_record he₁ (2 + Δcka) P st'L st'R recL isChall
  have hep_rec : ∀ Q, (s₁L.record (2 + Δcka) P st'L recL isChall).epoch Q =
      if Q = P then ep + 1 else esL.g.epoch Q := fun Q => hep_s₁ Q
  have hrec_ep : recL.ct.1.1 = recL.pos.epoch := by simp [recL, hdr, hep_s₁ P]
  rcases hp P with ⟨hidL, hidR, _, _, _, _, hvR, _, _⟩
  refine ⟨habL, habR, he_rec, (hinv.epMgmt hepL).record hrec_ep, rfl, ?_, ?_, ?_⟩
  · intro Q; rw [hep_rec Q]; simp only [SM.GameState.record]
    by_cases hQP : Q = P
    · subst hQP; simp only [↓reduceIte, Function.update_self]
      refine ⟨?_, ?_, rfl, rfl, rfl, rfl, ?_, rfl, γ', rfl, hγR'⟩
      · simp [st'L, hstL_s₁, hidL]
      · simp [st'R, hstR_s₁, hidR]
      · simp [st'L, st'R, hstL_s₁, hstR_s₁, hvR]
    · simp [hQP, hstL_s₁, hstR_s₁]; exact hp Q
  · refine ⟨hcs_b, fun Q htL hlt => ?_⟩
    rw [hep_rec Q] at hlt ⊢; simp only [SM.GameState.record]
    by_cases hQP : Q = P
    · subst hQP; simp only [↓reduceIte, Function.update_self] at hlt ⊢
      rcases hcs_P htL hlt with ⟨h1, h2⟩
      exact ⟨by simp [st'L, h1], h2⟩
    · have hQO : Q = P.other := by cases P <;> cases Q <;> simp [Party.other] at hQP ⊢
      subst hQO; simp only [hQP, ↓reduceIte, Function.update_of_ne hQP, hstL_s₁] at hlt ⊢
      rcases hcka.2 P.other htL hlt with ⟨h1, h2⟩
      rcases hcs_O htL hlt with ⟨h3, h4⟩
      exact ⟨by rw [h3]; exact h1, by rw [h4]; exact h2⟩
  · refine ⟨fun t' ht' => ?_, Or.inr ⟨P, ep, Tc, Ik, hsends, ?_, ?_, ?_, ?_⟩⟩
    · have hmax : max ((s₁L.record (2 + Δcka) P st'L recL isChall).epoch .A)
          ((s₁L.record (2 + Δcka) P st'L recL isChall).epoch .B) = ep + 1 := by
        rw [hep_rec .A, hep_rec .B]
        cases P <;> simp [ep, hAB]
      rw [hmax] at ht'
      have hne : t' ≠ ep + 1 := by omega
      simp only [h', Function.update_of_ne hne]
      apply hpp.1
      cases P <;> simp [ep, hAB] at ht' ⊢ <;> omega
    · rw [hep_rec P]; simp
    · rw [hep_rec P.other]
      have hOP : P.other ≠ P := by cases P <;> decide
      simp [hOP, hepO_eq]
    · simp [h']
    · exact hcs_last

end StepLemmas13U

end Sync13U

end CryptoGames.SM.Construction.PrivL13U
