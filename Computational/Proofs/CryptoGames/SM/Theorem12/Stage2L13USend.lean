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
import Computational.Proofs.CryptoGames.SM.Theorem12.Stage2L13URecv
import Computational.Proofs.CryptoGames.SM.Theorem12.Lemma13
import Computational.Proofs.CryptoGames.SM.Theorem12.Lemma14
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Send Step Lemmas and Main Theorem for Stage-2 Switch-Back Lemma 13U (`SM/Theorem12.lean`)

**Checked by Lean.** No theorem of `Computational/Theorems/` unfolds a definition of this file, and
Lean's kernel checks every proof in it: you do not need to read it to trust those theorems.

Proves `evalEng2_sendCore_13U`, `evalEng2_transmitE_13U`, `evalEng2_challE_13U`, `evalEng2_sync13U`,
and `branch_redCKAPrivUUniAt_dEq_redCKAPrivU_false`.-/

set_option autoImplicit false

public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.SM.Construction.PrivL13U

open Engine PrivL14 CryptoGames.Lazy

section SendAndTop13U

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}

section StepSend13U

set_option linter.unusedSectionVars false

variable [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType CCoins] [SampleableType I] [SampleableType K]
  (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
  (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ)

private theorem runHM_hooksCKAU_startSend_some_c (mo : Mode) (ctx : Ctx (Option Γ) T Sig SS RS M E)
    (P : Party) (t : ℕ) (γ : Γ) (σ : Sig) (c : CCoins) (h : CKAUState T I K)
    (oimpl : QueryImpl (CKA.spec Γ CCoins T I) (StateT (CKA.GameState Γ T) ProbComp))
    (cs : CKA.GameState Γ T) :
    runHM oimpl ((hooksCKAU cka prng fs Δcka mo).startSend ctx P t (some γ) σ (some c)) h cs =
      let out := cka.send γ c
      let p := prng.up σ out.2.2
      if t = mo.tStar then
        (fun kU =>
          ((some (some out.1, out.2.1, p.1, fs.initSender kU),
            ({ cache := Function.update h.1.cache t (some out.2) }, some kU)), cs)) <$>
          ($ᵗ K : ProbComp K)
      else
        pure ((some (some out.1, out.2.1, p.1, fs.initSender p.2),
          ({ cache := Function.update h.1.cache t (some out.2) }, h.2)), cs) := by
  dsimp only [hooksCKAU]
  by_cases ht : t = mo.tStar
  · simp [ht, cacheCU, runHM_bind, runHM_modify, runHM_sampleT, runHM_pure,
      map_eq_bind_pure_comp, bind_assoc]
  · simp [ht, cacheCU, runHM_bind, runHM_get, runHM_modify, runHM_pure, map_eq_bind_pure_comp]

private theorem runHM_hooksCKAU_startSend_some_none (mo : Mode) (ctx : Ctx (Option Γ) T Sig SS RS M E)
    (P : Party) (t : ℕ) (γ : Γ) (σ : Sig) (h : CKAUState T I K)
    (oimpl : QueryImpl (CKA.spec Γ CCoins T I) (StateT (CKA.GameState Γ T) ProbComp))
    (cs : CKA.GameState Γ T) :
    runHM oimpl ((hooksCKAU cka prng fs Δcka mo).startSend ctx P t (some γ) σ none) h cs =
      ($ᵗ CCoins : ProbComp CCoins) >>= fun c =>
        let out := cka.send γ c
        let p := prng.up σ out.2.2
        if t = mo.tStar then
          (fun kU =>
            ((some (some out.1, out.2.1, p.1, fs.initSender kU),
              ({ cache := Function.update h.1.cache t (some out.2) }, some kU)), cs)) <$>
            ($ᵗ K : ProbComp K)
        else
          pure ((some (some out.1, out.2.1, p.1, fs.initSender p.2),
            ({ cache := Function.update h.1.cache t (some out.2) }, h.2)), cs) := by
  dsimp only [hooksCKAU]
  rw [runHM_bind, runHM_get, pure_bind]
  dsimp only
  rw [runHM_bind, runHM_sampleT, bind_map_left]
  refine bind_congr fun c => ?_
  dsimp only
  by_cases ht : t = mo.tStar
  · simp [ht, cacheCU, runHM_bind, runHM_modify, runHM_sampleT, runHM_pure,
      map_eq_bind_pure_comp, bind_assoc]
  · simp [ht, cacheCU, runHM_bind, runHM_modify, runHM_pure, map_eq_bind_pure_comp]

private theorem runHM_hooksCKAU_none_tail (mo : Mode) (P : Party) (t : ℕ)
    (T' : T) (Ik : I) (γ' : Γ) (σ : Sig) (h : CKAUState T I K) (cs' : CKA.GameState Γ T)
    (hst : cs'.st P = γ') (hep : cs'.epoch P = t) :
    runHM (CKA.oracleImpl cka Δcka mo.tH)
      (do
        cacheCU t (T', Ik)
        let p := prng.up σ Ik
        let (kEpoch, kOpt1) ←
          if t = mo.tStar then do
            let kU ← StateT.lift (sampleT K)
            pure (kU, some kU)
          else pure (p.2, h.2)
        modify fun s => (s.1, kOpt1)
        if mo.tH + Δcka ≤ t then
          match ← StateT.lift (CKA.corrQuery P) with
          | none => return none
          | some γ => return some (some γ, T', p.1, fs.initSender kEpoch)
        else return some (none, T', p.1, fs.initSender kEpoch))
      h cs' =
      let p := prng.up σ Ik
      let γR' : Option Γ := if decide (mo.tH + Δcka ≤ t) then some γ' else none
      if t = mo.tStar then
        (fun kU =>
          ((some (γR', T', p.1, fs.initSender kU),
            ({ cache := Function.update h.1.cache t (some (T', Ik)) }, some kU)), cs')) <$>
          ($ᵗ K : ProbComp K)
      else
        pure ((some (γR', T', p.1, fs.initSender p.2),
          ({ cache := Function.update h.1.cache t (some (T', Ik)) }, h.2)), cs') := by
  by_cases hfin : mo.tH + Δcka ≤ t
  · have hfinished : cs'.finished Δcka mo.tH P = true := by
      unfold CKA.GameState.finished; rw [hep]; simp [hfin]
    by_cases ht : t = mo.tStar
    · subst ht
      simp [hfin, cacheCU, runHM_bind, runHM_modify, runHM_sampleT, runHM_liftCU_corr,
        hfinished, hst, runHM_pure, map_eq_bind_pure_comp, bind_assoc]
    · simp [ht, hfin, cacheCU, runHM_bind, runHM_modify, runHM_liftCU_corr,
        hfinished, hst, runHM_pure]
  · by_cases ht : t = mo.tStar
    · subst ht
      simp [hfin, cacheCU, runHM_bind, runHM_modify, runHM_sampleT, runHM_pure,
        map_eq_bind_pure_comp, bind_assoc]
    · simp [ht, hfin, cacheCU, runHM_bind, runHM_modify, runHM_pure, map_eq_bind_pure_comp]

private theorem runHM_hooksCKAU_startSend_none_none (l tStar : ℕ)
    (ctx : Ctx (Option Γ) T Sig SS RS M E) (P : Party) (ep : ℕ) (γ : Γ) (σ : Sig)
    (h : CKAUState T I K) (csR : CKA.GameState Γ T)
    (hb : csR.b = false) (hcanS : csR.canSend P = true)
    (hcsγ : csR.st P = γ) (hcsEp : csR.epoch P = ep) :
    runHM (CKA.oracleImpl cka Δcka (healEpoch (some l)))
      ((hooksCKAU cka prng fs Δcka ⟨false, some l, tStar⟩).startSend ctx P (ep + 1) none σ none)
      h csR =
      (($ᵗ CCoins : ProbComp CCoins) >>= fun c =>
        let out := cka.send γ c
        let csR' := csR.afterSend P out.1 out.2.1
        let p := prng.up σ out.2.2
        let γR' : Option Γ := if decide (healEpoch (some l) + Δcka ≤ ep + 1) then some out.1 else none
        if ep + 1 = tStar then
          (fun kU =>
            ((some (γR', out.2.1, p.1, fs.initSender kU),
              ({ cache := Function.update h.1.cache (ep + 1) (some out.2) }, some kU)), csR')) <$>
            ($ᵗ K : ProbComp K)
        else
          pure ((some (γR', out.2.1, p.1, fs.initSender p.2),
            ({ cache := Function.update h.1.cache (ep + 1) (some out.2) }, h.2)), csR')) := by
  have hq := runHM_liftCU_sendOrChall_false cka Δcka (healEpoch (some l)) P (ep + 1)
    h csR hb hcanS (by rw [hcsEp])
  unfold hooksCKAU
  simp only [Mode.tH]
  rw [runHM_bind, runHM_get, pure_bind]
  dsimp only
  by_cases hchall : ep + 1 = healEpoch (some l)
  · simp only [hchall, ↓reduceIte] at hq ⊢
    rw [runHM_bind, hq, bind_map_left]
    refine bind_congr fun c => ?_
    dsimp only
    rw [hcsγ]
    exact runHM_hooksCKAU_none_tail cka prng fs Δcka ⟨false, some l, tStar⟩ P (healEpoch (some l))
      (cka.send γ c).2.1 (cka.send γ c).2.2 (cka.send γ c).1 σ h
      (csR.afterSend P (cka.send γ c).1 (cka.send γ c).2.1)
      (by simp [CKA.GameState.afterSend])
      (by simp [CKA.GameState.afterSend, hcsEp, ← hchall])
  · simp only [hchall, ↓reduceIte] at hq ⊢
    rw [runHM_bind, hq, bind_map_left]
    refine bind_congr fun c => ?_
    dsimp only
    rw [hcsγ]
    exact runHM_hooksCKAU_none_tail cka prng fs Δcka ⟨false, some l, tStar⟩ P (ep + 1)
      (cka.send γ c).2.1 (cka.send γ c).2.2 (cka.send γ c).1 σ h
      (csR.afterSend P (cka.send γ c).1 (cka.send γ c).2.1)
      (by simp [CKA.GameState.afterSend])
      (by simp [CKA.GameState.afterSend, hcsEp])

private theorem evalEng2_sendCore_13U (tL : Option ℕ) (tStar : ℕ) (b : Bool)
    (s₁L s₁R : Ctx (Option Γ) T Sig SS RS M E)
    (P : Party) (m : M) (pair : Option (M × M)) (rcoins : Option CCoins) (isChall : Bool)
    (k : Option (Header T × E) →
      OracleComp (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) Bool)
    (esL esR : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAUState T I K))
    (csL csR : CKA.GameState Γ T)
    (hs : Sync13U Δcka tL (esL, csL) (esR, csR))
    (hepL : esL.g.epMgmt (2 + Δcka) qep P rcoins.isSome = some s₁L)
    (hepR : esR.g.epMgmt (2 + Δcka) qep P rcoins.isSome = some s₁R)
    (hldR : Policy.leakDoom ⟨false, tL, tStar⟩ esL.g s₁L = false)
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
          (sendCore (hooksCKAU cka prng fs Δcka ⟨false, none, tStar⟩) (2 + Δcka) s₁L P m pair rcoins isChall)
          (esL, csL) >>= fun r =>
          evalEng2 (CKA.oracleImpl cka Δcka 0) (hooksCKAU cka prng fs Δcka ⟨false, none, tStar⟩)
            (2 + Δcka) qep fs.maxSkip (Config.priv tStar) (polUni12 Δcka tStar) ⟨false, tL, tStar⟩
            b (k r.1) r.2)
        (runEM (CKA.oracleImpl cka Δcka (healEpoch tL))
          (sendCore (hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩) (2 + Δcka) s₁R P m pair rcoins isChall)
          (esR, csR) >>= fun r =>
          evalEng2 (CKA.oracleImpl cka Δcka (healEpoch tL))
            (hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩)
            (2 + Δcka) qep fs.maxSkip (Config.priv tStar) ⟨false, tL, tStar⟩ ⟨false, tL, tStar⟩
            b (k r.1) r.2) := by
  have hinv := hs.2.2.2.1
  have hh := hs.2.2.2.2.1
  have hp := hs.2.2.2.2.2.1
  have hcka := hs.2.2.2.2.2.2.1
  have hpp := hs.2.2.2.2.2.2.2
  dsimp only at hinv hh hp hcka hpp
  have hstL_s₁ := epMgmt_st hepL
  have hstR_s₁ := epMgmt_st hepR
  rcases hp P with ⟨hidL, hidR, htcurL, htcurR, hroot, hvS, hvR, hTcur, γ, hγL, hγR⟩
  by_cases hsends : P.sendsIn (esL.g.epoch P + 1) = false
  · have hL_vs := runEM_sendCore_sendsIn_false (CKA.oracleImpl cka Δcka 0)
      (hooksCKAU cka prng fs Δcka ⟨false, none, tStar⟩) fs (fun _ _ _ _ _ _ _ => rfl)
      (2 + Δcka) s₁L P m pair rcoins isChall esL csL
      (by rw [hstL_s₁, hidL, htcurL]; exact hsends)
    have hR_vs := runEM_sendCore_sendsIn_false (CKA.oracleImpl cka Δcka (healEpoch tL))
      (hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩) fs (fun _ _ _ _ _ _ _ => rfl)
      (2 + Δcka) s₁R P m pair rcoins isChall esR csR
      (by rw [hstR_s₁, hidR, htcurR]; exact hsends)
    rw [hL_vs, hR_vs, pure_bind, pure_bind]
    simp only [hstL_s₁, hstR_s₁, htcurL, htcurR, hTcur, hvS]
    cases hvSP : (esR.g.st P).vS with
    | none =>
      dsimp only
      apply ih _ _ _ (Or.inl ?_)
      exact sync13U_after_same_send Δcka qep tL P m _ rcoins isChall
        (esL.g.st P) (esR.g.st P) s₁L s₁R esL esR csL csR hs hepL hepR hsends rfl
        ⟨hidL, hidR, htcurL, htcurR, hroot, by rw [hvS], hvR, hTcur, γ, hγL, hγR⟩ rfl
    | some ss =>
      dsimp only
      apply ih _ _ _ (Or.inl ?_)
      exact sync13U_after_same_send Δcka qep tL P m _ rcoins isChall
        _ _ s₁L s₁R esL esR csL csR hs hepL hepR hsends rfl
        ⟨hidL, hidR, rfl, rfl, hroot, rfl, hvR, rfl, γ, hγL, hγR⟩ rfl
  · have hsends_t : P.sendsIn (esL.g.epoch P + 1) = true :=
      Bool.eq_true_of_not_eq_false hsends
    set ep := esL.g.epoch P with hep_def
    have hL_sc := runEM_sendCore_sendsIn_true (CKA.oracleImpl cka Δcka 0)
      (hooksCKAU cka prng fs Δcka ⟨false, none, tStar⟩) fs (fun _ _ _ _ _ _ _ => rfl)
      (2 + Δcka) s₁L P m pair rcoins isChall esL csL
      (by rw [hstL_s₁, hidL, htcurL]; exact hsends_t)
    have hR_sc := runEM_sendCore_sendsIn_true (CKA.oracleImpl cka Δcka (healEpoch tL))
      (hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩) fs (fun _ _ _ _ _ _ _ => rfl)
      (2 + Δcka) s₁R P m pair rcoins isChall esR csR
      (by rw [hstR_s₁, hidR, htcurR]; exact hsends_t)
    rw [hL_sc, hR_sc, bind_assoc, bind_assoc]
    simp only [hstL_s₁, hstR_s₁, htcurL, htcurR, hγL, ← hroot, ← hh]
    let stPL := esL.g.st P
    let stPR := esR.g.st P
    by_cases hγc : (tL.isNone || decide (healEpoch tL + Δcka ≤ ep)) = true
    · have hγR_some : (esR.g.st P).γ = some γ := by rw [hγR]; simp [hγc]
      have hγc' : (tL.isNone || decide (healEpoch tL + Δcka ≤ ep + 1)) = true := by
        rcases Bool.or_eq_true_iff.mp hγc with h1 | h2
        · simp [h1]
        · have := decide_eq_true_eq.mp h2
          exact Bool.or_eq_true_iff.mpr (Or.inr (decide_eq_true (by omega)))
      rw [hγR_some]
      have kStep : ∀ (c : CCoins) (kEp : K) (kOpt1 : Option K), _ := fun c kEp kOpt1 =>
        let out := cka.send γ c
        let fsOut := fs.send (fs.initSender kEp) (ep + 1, some out.2.1) m
        let stL' : PartyState (Option Γ) T Sig SS RS := { stPL with
          tcur := ep + 1, γ := some out.1, curCkaMsg := some out.2.1,
          root := (prng.up (esL.g.st P).root out.2.2).1, vS := some fsOut.1 }
        let stR' : PartyState (Option Γ) T Sig SS RS := { stPR with
          tcur := ep + 1, γ := some out.1, curCkaMsg := some out.2.1,
          root := (prng.up (esL.g.st P).root out.2.2).1, vS := some fsOut.1 }
        let recL : Record M (Header T × E) := ⟨⟨P, s₁L.epoch P, s₁L.idx P + 1⟩, m, ((ep + 1, some out.2.1), fsOut.2)⟩
        let recR : Record M (Header T × E) := ⟨⟨P, s₁R.epoch P, s₁R.idx P + 1⟩, m, ((ep + 1, some out.2.1), fsOut.2)⟩
        let h' : CKAUState T I K := ({ cache := Function.update esL.h.1.cache (ep + 1) (some out.2) }, kOpt1)
        ih (some ((ep + 1, some out.2.1), fsOut.2))
          ({ esL with g := s₁L.record (2 + Δcka) P stL' recL isChall, h := h' }, csL)
          ({ esR with g := s₁R.record (2 + Δcka) P stR' recR isChall, h := h' }, csR)
          (Or.inl (by
            have hsync := sync13U_after_new_send prng fs Δcka qep tL P m rcoins isChall
              out.2.1 out.2.2 kEp kOpt1 out.1 (some out.1) s₁L s₁R esL esR csL csR csR
              hs hepL hepR hsends_t (by rw [← hep_def]; simp [hγc']) hcka.1
              (fun htL hlt => by
                exfalso
                cases tL with
                | none => simp at htL
                | some l => simp [decide_eq_false (by omega : ¬(healEpoch (some l) + Δcka ≤ ep))] at hγc)
              (fun _ _ => ⟨rfl, rfl⟩)
              (fun htL hlt => by
                exfalso
                cases tL with
                | none => simp at htL
                | some l => simp [decide_eq_false (by omega : ¬(healEpoch (some l) + Δcka ≤ ep))] at hγc)
            simpa only [hstL_s₁, hstR_s₁] using hsync))
      cases rcoins with
      | some c =>
        rw [runHM_hooksCKAU_startSend_some_c, runHM_hooksCKAU_startSend_some_c]
        dsimp only
        by_cases ht : ep + 1 = tStar
        · simp only [ht, ↓reduceIte, bind_map_left, pure_bind]
          simpa only [ht] using (DEq.bind_right ($ᵗ K) fun kU => kStep c kU (some kU))
        · simp only [ht, ↓reduceIte, pure_bind]
          exact kStep c (prng.up (esL.g.st P).root (cka.send γ c).2.2).2 esL.h.2
      | none =>
        rw [runHM_hooksCKAU_startSend_some_none, runHM_hooksCKAU_startSend_some_none]
        simp only [bind_assoc]
        refine DEq.bind_right ($ᵗ CCoins) fun c => ?_
        by_cases ht : ep + 1 = tStar
        · simp only [ht, ↓reduceIte, bind_map_left, pure_bind]
          simpa only [ht] using (DEq.bind_right ($ᵗ K) fun kU => kStep c kU (some kU))
        · simp only [ht, ↓reduceIte, pure_bind]
          exact kStep c (prng.up (esL.g.st P).root (cka.send γ c).2.2).2 esL.h.2
    · have htL_some : ∃ l, tL = some l ∧ ep < healEpoch (some l) + Δcka := by
        cases tL with
        | none => simp at hγc
        | some l =>
          simp only [Option.isNone_some, Bool.false_or, decide_eq_true_eq, not_le] at hγc
          exact ⟨l, rfl, hγc⟩
      rcases htL_some with ⟨l, rfl, hunh⟩
      have hγR_none : (esR.g.st P).γ = none := by
        rw [hγR]
        simp [decide_eq_false (by omega : ¬(healEpoch (some l) + Δcka ≤ ep))]
      rw [hγR_none]
      have hAB : esL.g.epoch .A = esL.g.epoch .B := by
        exact hpp.synced_of_sendsIn (by rw [← hep_def]; exact hsends_t)
      have hepO_eq : esL.g.epoch P.other = ep := by cases P <;> simp [Party.other, hep_def, hAB]
      have hcsP := hcka.2 P rfl (by rw [← hep_def]; exact hunh)
      have hcsO := hcka.2 P.other rfl (by rw [hepO_eq]; exact hunh)
      have hcsγ : csR.st P = γ := Option.some.inj (hcsP.1.symm.trans hγL)
      have hcanS : csR.canSend P = true := by
        unfold CKA.GameState.canSend
        rw [hcsP.2, hcsO.2, hepO_eq, ← hep_def]
        simp [hsends_t]
      have kStep : ∀ (c : CCoins) (kEp : K) (kOpt1 : Option K), _ := fun c kEp kOpt1 =>
        let out := cka.send γ c
        let csR' := csR.afterSend P out.1 out.2.1
        let γR' : Option Γ := if decide (healEpoch (some l) + Δcka ≤ ep + 1) then some out.1 else none
        let fsOut := fs.send (fs.initSender kEp) (ep + 1, some out.2.1) m
        let stL' : PartyState (Option Γ) T Sig SS RS := { stPL with
          tcur := ep + 1, γ := some out.1, curCkaMsg := some out.2.1,
          root := (prng.up (esL.g.st P).root out.2.2).1, vS := some fsOut.1 }
        let stR' : PartyState (Option Γ) T Sig SS RS := { stPR with
          tcur := ep + 1, γ := γR', curCkaMsg := some out.2.1,
          root := (prng.up (esL.g.st P).root out.2.2).1, vS := some fsOut.1 }
        let recL : Record M (Header T × E) := ⟨⟨P, s₁L.epoch P, s₁L.idx P + 1⟩, m, ((ep + 1, some out.2.1), fsOut.2)⟩
        let recR : Record M (Header T × E) := ⟨⟨P, s₁R.epoch P, s₁R.idx P + 1⟩, m, ((ep + 1, some out.2.1), fsOut.2)⟩
        let h' : CKAUState T I K := ({ cache := Function.update esL.h.1.cache (ep + 1) (some out.2) }, kOpt1)
        ih (some ((ep + 1, some out.2.1), fsOut.2))
          ({ esL with g := s₁L.record (2 + Δcka) P stL' recL isChall, h := h' }, csL)
          ({ esR with g := s₁R.record (2 + Δcka) P stR' recR isChall, h := h' }, csR')
          (Or.inl (by
            have hOP : P.other ≠ P := by cases P <;> decide
            have hsync := sync13U_after_new_send prng fs Δcka qep (some l) P m rcoins isChall
              out.2.1 out.2.2 kEp kOpt1 out.1 γR' s₁L s₁R esL esR csL csR csR'
              hs hepL hepR hsends_t (by dsimp [γR']; rw [← hep_def]; simp) hcka.1
              (fun _ _ => by simp [csR', CKA.GameState.afterSend, hcsP.2])
              (fun _ _ => by simp [csR', CKA.GameState.afterSend, Function.update_of_ne hOP])
              (fun _ _ => by simp [csR', CKA.GameState.afterSend, hcsP.2])
            simpa only [hstL_s₁, hstR_s₁] using hsync))
      cases rcoins with
      | some c =>
        by_cases hbad_ok : ep + 1 + 2 ≤ healEpoch (some l)
        · rw [runHM_hooksCKAU_startSend_some_c]
          have hR_bad :
              runHM (CKA.oracleImpl cka Δcka (healEpoch (some l)))
                ((hooksCKAU cka prng fs Δcka ⟨false, some l, tStar⟩).startSend
                  s₁R P (ep + 1) none (esL.g.st P).root (some c)) esL.h csR =
              let out := cka.send γ c
              let csR' := csR.afterSend P out.1 out.2.1
              let p := prng.up (esL.g.st P).root out.2.2
              let γR' : Option Γ := if decide (healEpoch (some l) + Δcka ≤ ep + 1) then some out.1 else none
              if ep + 1 = tStar then
                (fun kU =>
                  ((some (γR', out.2.1, p.1, fs.initSender kU),
                    ({ cache := Function.update esL.h.1.cache (ep + 1) (some out.2) }, some kU)), csR')) <$>
                  ($ᵗ K : ProbComp K)
              else
                pure ((some (γR', out.2.1, p.1, fs.initSender p.2),
                  ({ cache := Function.update esL.h.1.cache (ep + 1) (some out.2) }, esL.h.2)), csR') := by
            dsimp only [hooksCKAU, Mode.tH]
            rw [runHM_bind, runHM_get, pure_bind]; dsimp only
            rw [runHM_bind, runHM_liftCU_sendBad]
            have hdec : decide (csR.epoch P + 1 + 2 ≤ healEpoch (some l)) = true := by
              rw [hcsP.2]; exact decide_eq_true hbad_ok
            simp only [hcanS, hdec, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
              hcsγ, pure_bind]
            exact runHM_hooksCKAU_none_tail cka prng fs Δcka ⟨false, some l, tStar⟩ P (ep + 1)
              (cka.send γ c).2.1 (cka.send γ c).2.2 (cka.send γ c).1 (esL.g.st P).root esL.h _
              (by simp [CKA.GameState.afterSend])
              (by simp [CKA.GameState.afterSend, hcsP.2, ← hep_def])
          rw [hR_bad]
          dsimp only
          by_cases ht : ep + 1 = tStar
          · simp only [ht, ↓reduceIte, bind_map_left, pure_bind]
            simpa only [ht] using (DEq.bind_right ($ᵗ K) fun kU => kStep c kU (some kU))
          · simp only [ht, ↓reduceIte, pure_bind]
            exact kStep c (prng.up (esL.g.st P).root (cka.send γ c).2.2).2 esL.h.2
        · have hvh : healEpoch (some l) + Δcka ≤ tStar := by
            rcases validGuess_healed hvg with h0 | ⟨l', heq, _, hle⟩
            · contradiction
            · cases heq; exact hle
          have hlt_l : l < ep + 1 := by simp only [healEpoch] at hbad_ok; omega
          have hmL : MissedTL (some l) s₁L :=
            missedTL_of_bad_send hinv hAB hsends_t hepL hldR hvh hunh hlt_l
          have hR_none :
              runHM (CKA.oracleImpl cka Δcka (healEpoch (some l)))
                ((hooksCKAU cka prng fs Δcka ⟨false, some l, tStar⟩).startSend
                  s₁R P (ep + 1) none (esL.g.st P).root (some c)) esL.h csR =
                pure ((none, esL.h), csR) := by
            dsimp only [hooksCKAU, Mode.tH]
            rw [runHM_bind, runHM_get, pure_bind]; dsimp only
            rw [runHM_bind, runHM_liftCU_sendBad]
            have hdec : decide (csR.epoch P + 1 + 2 ≤ healEpoch (some l)) = false := by
              rw [hcsP.2]; exact decide_eq_false hbad_ok
            simp [hcanS, hdec, runHM_pure]
          simp only [hstL_s₁, htcurL, hγL] at hL_sc
          rw [← bind_assoc, ← hL_sc]
          rw [hR_none, pure_bind]
          dsimp only
          rw [pure_bind]
          have hLHS' : DEq
              (runEM (CKA.oracleImpl cka Δcka 0)
                (sendCore (hooksCKAU cka prng fs Δcka ⟨false, none, tStar⟩)
                  (2 + Δcka) s₁L P m pair (some c) isChall) (esL, csL) >>= fun r =>
                evalEng2 (CKA.oracleImpl cka Δcka 0)
                  (hooksCKAU cka prng fs Δcka ⟨false, none, tStar⟩) (2 + Δcka) qep fs.maxSkip
                  (Config.priv tStar) (polUni12 Δcka tStar) ⟨false, some l, tStar⟩ b (k r.1) r.2)
              ($ᵗ Bool : ProbComp Bool) :=
            evalEng2_sendCore_of_doom13U _ _ _ _ _ _ _ _ _ s₁L P m pair (some c) isChall k
              (esL, csL) (Or.inl hmL)
          have hRHS : DEq
              (evalEng2 (CKA.oracleImpl cka Δcka (healEpoch (some l)))
                (hooksCKAU cka prng fs Δcka ⟨false, some l, tStar⟩) (2 + Δcka) qep fs.maxSkip
                (Config.priv tStar) ⟨false, some l, tStar⟩ ⟨false, some l, tStar⟩ b (k none)
                ({ esR with h := esL.h, abort := true }, csR))
              ($ᵗ Bool : ProbComp Bool) :=
            evalEng2_doom13U _ _ _ _ _ _ _ _ _ _ _ (Or.inl (Or.inl rfl))
          exact hLHS'.trans hRHS.symm
      | none =>
        rw [runHM_hooksCKAU_startSend_some_none,
          runHM_hooksCKAU_startSend_none_none cka prng fs Δcka l tStar s₁R P ep γ
            (esL.g.st P).root esL.h csR hcka.1 hcanS hcsγ (by rw [hcsP.2, ← hep_def])]
        simp only [bind_assoc]
        refine DEq.bind_right ($ᵗ CCoins) fun c => ?_
        by_cases ht : ep + 1 = tStar
        · simp only [ht, ↓reduceIte, bind_map_left, pure_bind]
          simpa only [ht] using (DEq.bind_right ($ᵗ K) fun kU => kStep c kU (some kU))
        · simp only [ht, ↓reduceIte, pure_bind]
          exact kStep c (prng.up (esL.g.st P).root (cka.send γ c).2.2).2 esL.h.2

private theorem evalEng2_transmitE_13U (tL : Option ℕ) (tStar : ℕ) (b : Bool)
    (q : Party × M × Option CCoins)
    (k : Option (Header T × E) →
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
          (transmitE (hooksCKAU cka prng fs Δcka ⟨false, none, tStar⟩) (2 + Δcka) qep
            (polUni12 Δcka tStar) q) sL >>= fun r =>
          evalEng2 (CKA.oracleImpl cka Δcka 0) (hooksCKAU cka prng fs Δcka ⟨false, none, tStar⟩)
            (2 + Δcka) qep fs.maxSkip (Config.priv tStar) (polUni12 Δcka tStar) ⟨false, tL, tStar⟩
            b (k r.1) r.2)
        (runEM (CKA.oracleImpl cka Δcka (healEpoch tL))
          (transmitE (hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩) (2 + Δcka) qep
            ⟨false, tL, tStar⟩ q) sR >>= fun r =>
          evalEng2 (CKA.oracleImpl cka Δcka (healEpoch tL))
            (hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩)
            (2 + Δcka) qep fs.maxSkip (Config.priv tStar) ⟨false, tL, tStar⟩ ⟨false, tL, tStar⟩
            b (k r.1) r.2) := by
  rcases q with ⟨P, m, rcoins⟩
  rcases sL with ⟨esL, csL⟩
  rcases sR with ⟨esR, csR⟩
  have habL : esL.abort = false := hs.1
  have habR : esR.abort = false := hs.2.1
  have he : eraseSt esL.g = eraseSt esR.g := hs.2.2.1
  have hwin : esR.g.win = esL.g.win := (eraseSt_win he).symm
  unfold transmitE; dsimp only
  rw [runEM_bind, runEM_get, pure_bind, runEM_bind, runEM_get, pure_bind]
  dsimp only
  rw [habL, habR, Bool.false_or, Bool.false_or, hwin]
  by_cases hw : esL.g.win = true
  · simp only [hw, ↓reduceIte, runEM_pure, pure_bind]
    exact ih none (esL, csL) (esR, csR) (Or.inl hs)
  · simp only [hw, Bool.false_eq_true, ↓reduceIte]
    cases hepL : esL.g.epMgmt (2 + Δcka) qep P rcoins.isSome with
    | none =>
      rw [eraseSt_epMgmt_none he hepL]
      simp only [runEM_pure, pure_bind]
      exact ih none (esL, csL) (esR, csR) (Or.inl hs)
    | some s₁L =>
      rcases eraseSt_epMgmt_some he hepL with ⟨s₁R, hepR, he₁, -, -⟩
      rw [hepR]; dsimp only
      have hldR_eq := eraseSt_leakDoom he he₁ ⟨false, tL, tStar⟩
      rw [← hldR_eq]
      by_cases hldL : (polUni12 Δcka tStar).leakDoom esL.g s₁L = true
      · have hldR : Policy.leakDoom ⟨false, tL, tStar⟩ esL.g s₁L = true :=
          leakDoom_polUni_imp hvg _ _ hldL
        simp only [hldL, hldR, ↓reduceIte, runEM_abort_pure, pure_bind]
        exact ih none ({ esL with abort := true }, csL) ({ esR with abort := true }, csR)
          (Or.inr ⟨Or.inl (Or.inl rfl), Or.inl rfl⟩)
      · have hldL_f : (polUni12 Δcka tStar).leakDoom esL.g s₁L = false := Bool.eq_false_iff.mpr hldL
        simp only [hldL_f, Bool.false_eq_true, ↓reduceIte]
        by_cases hldR : Policy.leakDoom ⟨false, tL, tStar⟩ esL.g s₁L = true
        · simp only [hldR, ↓reduceIte, runEM_abort_pure, pure_bind]
          have hhla : HasLeakAbove tL tStar s₁L :=
            hasLeakAbove_of_leakDoom_diff esL.g s₁L hldL_f hldR
          have hLHS := evalEng2_sendCore_of_doom13U (CKA.oracleImpl cka Δcka 0)
            (hooksCKAU cka prng fs Δcka ⟨false, none, tStar⟩) (2 + Δcka) qep fs.maxSkip
            (Config.priv tStar) (polUni12 Δcka tStar) ⟨false, tL, tStar⟩ b
            s₁L P m none rcoins false k (esL, csL) (Or.inr hhla)
          have hRHS : DEq
              (evalEng2 (CKA.oracleImpl cka Δcka (healEpoch tL))
                (hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩) (2 + Δcka) qep fs.maxSkip
                (Config.priv tStar) ⟨false, tL, tStar⟩ ⟨false, tL, tStar⟩ b (k none)
                ({ esR with abort := true }, csR))
              ($ᵗ Bool : ProbComp Bool) :=
            evalEng2_doom13U _ _ _ _ _ _ _ _ _ _ _ (Or.inl (Or.inl rfl))
          exact hLHS.trans hRHS.symm
        · have hldR_f : Policy.leakDoom ⟨false, tL, tStar⟩ esL.g s₁L = false :=
            Bool.eq_false_iff.mpr hldR
          simp only [hldR_f, Bool.false_eq_true, ↓reduceIte]
          exact evalEng2_sendCore_13U cka prng fs Δcka qep tL tStar b s₁L s₁R P m none rcoins false
            k esL esR csL csR hs hepL hepR hldR_f hvg ih

private theorem evalEng2_challE_13U (tL : Option ℕ) (tStar : ℕ) (b : Bool)
    (q : Party × M × M × Option CCoins)
    (k : Option (Header T × E) →
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
          (challE (hooksCKAU cka prng fs Δcka ⟨false, none, tStar⟩) (2 + Δcka) qep
            (Config.priv tStar) (polUni12 Δcka tStar) q) sL >>= fun r =>
          evalEng2 (CKA.oracleImpl cka Δcka 0) (hooksCKAU cka prng fs Δcka ⟨false, none, tStar⟩)
            (2 + Δcka) qep fs.maxSkip (Config.priv tStar) (polUni12 Δcka tStar) ⟨false, tL, tStar⟩
            b (k r.1) r.2)
        (runEM (CKA.oracleImpl cka Δcka (healEpoch tL))
          (challE (hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩) (2 + Δcka) qep
            (Config.priv tStar) ⟨false, tL, tStar⟩ q) sR >>= fun r =>
          evalEng2 (CKA.oracleImpl cka Δcka (healEpoch tL))
            (hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩)
            (2 + Δcka) qep fs.maxSkip (Config.priv tStar) ⟨false, tL, tStar⟩ ⟨false, tL, tStar⟩
            b (k r.1) r.2) := by
  rcases q with ⟨P, m₀, m₁, rcoins⟩
  rcases sL with ⟨esL, csL⟩
  rcases sR with ⟨esR, csR⟩
  have habL : esL.abort = false := hs.1
  have habR : esR.abort = false := hs.2.1
  have he : eraseSt esL.g = eraseSt esR.g := hs.2.2.1
  have hwin : esR.g.win = esL.g.win := (eraseSt_win he).symm
  have hb_eq : esR.g.b = esL.g.b := (eraseSt_b he).symm
  unfold challE; dsimp only
  rw [runEM_bind, runEM_get, pure_bind, runEM_bind, runEM_get, pure_bind]
  dsimp only
  rw [habL, habR, Bool.false_or, Bool.false_or, hwin]
  by_cases hw : esL.g.win = true
  · simp only [hw, ↓reduceIte, runEM_pure, pure_bind]
    exact ih none (esL, csL) (esR, csR) (Or.inl hs)
  · simp only [hw, Bool.false_eq_true, ↓reduceIte]
    cases hepL : esL.g.epMgmt (2 + Δcka) qep P rcoins.isSome with
    | none =>
      rw [eraseSt_epMgmt_none he hepL]
      simp only [runEM_pure, pure_bind]
      exact ih none (esL, csL) (esR, csR) (Or.inl hs)
    | some s₁L =>
      rcases eraseSt_epMgmt_some he hepL with ⟨s₁R, hepR, he₁, -, -⟩
      rw [hepR]; dsimp only
      have hsc_eq : s₁R.safeCh (2 + Δcka) P = s₁L.safeCh (2 + Δcka) P :=
        (eraseSt_safeCh he₁ (2 + Δcka) P).symm
      have hep_eq : s₁R.epoch P = s₁L.epoch P := (congrFun (eraseSt_epoch he₁) P).symm
      have hallow_eq : (Config.priv (Msg := M) tStar).challAllowedIn (s₁R.epoch P) =
          (Config.priv (Msg := M) tStar).challAllowedIn (s₁L.epoch P) := by rw [hep_eq]
      have hcmsg_eq : (Config.priv (Msg := M) tStar).challMsg (s₁R.epoch P) =
          (Config.priv (Msg := M) tStar).challMsg (s₁L.epoch P) := by rw [hep_eq]
      rw [hsc_eq, hallow_eq, hcmsg_eq]
      by_cases hguard : (!(s₁L.safeCh (2 + Δcka) P) ||
          !((Config.priv (Msg := M) tStar).challAllowedIn (s₁L.epoch P))) = true
      · simp only [hguard, ↓reduceIte, runEM_pure, pure_bind]
        exact ih none (esL, csL) (esR, csR) (Or.inl hs)
      · simp only [hguard, Bool.false_eq_true, ↓reduceIte]
        have hldR_eq := eraseSt_leakDoom he he₁ ⟨false, tL, tStar⟩
        rw [← hldR_eq, hb_eq]
        by_cases hldL : (polUni12 Δcka tStar).leakDoom esL.g s₁L = true
        · have hldR : Policy.leakDoom ⟨false, tL, tStar⟩ esL.g s₁L = true :=
            leakDoom_polUni_imp hvg _ _ hldL
          simp only [hldL, hldR, ↓reduceIte, runEM_abort_pure, pure_bind]
          exact ih none ({ esL with abort := true }, csL) ({ esR with abort := true }, csR)
            (Or.inr ⟨Or.inl (Or.inl rfl), Or.inl rfl⟩)
        · have hldL_f : (polUni12 Δcka tStar).leakDoom esL.g s₁L = false :=
            Bool.eq_false_iff.mpr hldL
          simp only [hldL_f, Bool.false_eq_true, ↓reduceIte]
          by_cases hldR : Policy.leakDoom ⟨false, tL, tStar⟩ esL.g s₁L = true
          · simp only [hldR, ↓reduceIte, runEM_abort_pure, pure_bind]
            have hhla : HasLeakAbove tL tStar s₁L :=
              hasLeakAbove_of_leakDoom_diff esL.g s₁L hldL_f hldR
            set m := ((Config.priv (Msg := M) tStar).challMsg (s₁L.epoch P)).getD (if esL.g.b then m₁ else m₀)
            have hLHS := evalEng2_sendCore_of_doom13U (CKA.oracleImpl cka Δcka 0)
              (hooksCKAU cka prng fs Δcka ⟨false, none, tStar⟩) (2 + Δcka) qep fs.maxSkip
              (Config.priv tStar) (polUni12 Δcka tStar) ⟨false, tL, tStar⟩ b
              s₁L P m (some (m₀, m₁)) rcoins true k (esL, csL) (Or.inr hhla)
            have hRHS : DEq
                (evalEng2 (CKA.oracleImpl cka Δcka (healEpoch tL))
                  (hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩) (2 + Δcka) qep fs.maxSkip
                  (Config.priv tStar) ⟨false, tL, tStar⟩ ⟨false, tL, tStar⟩ b (k none)
                  ({ esR with abort := true }, csR))
                ($ᵗ Bool : ProbComp Bool) :=
              evalEng2_doom13U _ _ _ _ _ _ _ _ _ _ _ (Or.inl (Or.inl rfl))
            exact hLHS.trans hRHS.symm
          · have hldR_f : Policy.leakDoom ⟨false, tL, tStar⟩ esL.g s₁L = false :=
              Bool.eq_false_iff.mpr hldR
            simp only [hldR_f, Bool.false_eq_true, ↓reduceIte]
            exact evalEng2_sendCore_13U cka prng fs Δcka qep tL tStar b s₁L s₁R P
              (((Config.priv (Msg := M) tStar).challMsg (s₁L.epoch P)).getD (if esL.g.b then m₁ else m₀))
              (some (m₀, m₁)) rcoins true k esL esR csL csR hs hepL hepR hldR_f hvg ih

private theorem evalEng2_sync13U (tL : Option ℕ) (tStar : ℕ) (b : Bool)
    (oa : OracleComp (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) Bool)
    (sL sR : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAUState T I K) ×
      CKA.GameState Γ T)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) tL tStar = true)
    (hsd : SyncOrDoom13U Δcka tL tStar sL sR) :
    DEq (evalEng2 (CKA.oracleImpl cka Δcka 0) (hooksCKAU cka prng fs Δcka ⟨false, none, tStar⟩)
          (2 + Δcka) qep fs.maxSkip (Config.priv tStar) (polUni12 Δcka tStar) ⟨false, tL, tStar⟩
          b oa sL)
        (evalEng2 (CKA.oracleImpl cka Δcka (healEpoch tL))
          (hooksCKAU cka prng fs Δcka ⟨false, tL, tStar⟩)
          (2 + Δcka) qep fs.maxSkip (Config.priv tStar) ⟨false, tL, tStar⟩ ⟨false, tL, tStar⟩
          b oa sR) := by
  induction oa using OracleComp.inductionOn generalizing sL sR with
  | pure b' =>
    rcases hsd with hs | ⟨hdL, hdR⟩
    · rw [evalEng2_pure, evalEng2_pure]
      rcases hs with ⟨habL, habR, he, -⟩
      simp only [privOutP, habL, habR, eraseSt_canon he tStar]
      exact DEq.refl _
    · rw [evalEng2_pure, evalEng2_pure,
        privOutP_of_doom13U (2 + Δcka) ⟨false, tL, tStar⟩ b b' sL.1 hdL,
        privOutP_of_doom (2 + Δcka) ⟨false, tL, tStar⟩ b b' sR.1 hdR]
  | query_bind q k ih =>
    rcases hsd with hs | ⟨hdL, hdR⟩
    · rw [evalEng2_query_bind, evalEng2_query_bind]
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq]
      rcases q with n | ⟨⟨⟨⟨qt | qc⟩ | qd⟩ | qi⟩ | P⟩
      · change DEq (runEM _ (coinsE n) sL >>= _) (runEM _ (coinsE n) sR >>= _)
        simp only [runEM_coinsE, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
        exact DEq.bind_right _ fun x => ih x sL sR (Or.inl hs)
      · exact evalEng2_transmitE_13U cka prng fs Δcka qep tL tStar b qt k sL sR hs hvg
          (fun ans sL' sR' h => ih ans sL' sR' h)
      · exact evalEng2_challE_13U cka prng fs Δcka qep tL tStar b qc k sL sR hs hvg
          (fun ans sL' sR' h => ih ans sL' sR' h)
      · rcases runEM_deliverE_13U cka prng fs Δcka tL tStar qd sL.1 sR.1 sL.2 sR.2 hs with
          ⟨out, sL', sR', hL, hR, hs'⟩
        change DEq (runEM _ (deliverE _ _ _ qd) sL >>= _) (runEM _ (deliverE _ _ _ qd) sR >>= _)
        rw [hL, hR, pure_bind, pure_bind]
        exact ih out sL' sR' (Or.inl hs')
      · rcases runEM_injectE_13U cka prng fs Δcka qep tL tStar qi sL.1 sR.1 sL.2 sR.2 hs with
          ⟨out, sL', sR', hL, hR, hs'⟩
        change DEq (runEM _ (injectE _ _ _ _ qi) sL >>= _) (runEM _ (injectE _ _ _ _ qi) sR >>= _)
        rw [hL, hR, pure_bind, pure_bind]
        exact ih out sL' sR' (Or.inl hs')
      · exact evalEng2_corrE_13U cka prng fs Δcka qep tL tStar b P k sL sR hs hvg
          (fun ans sL' sR' h => ih ans sL' sR' h)
    · exact (evalEng2_doom13U _ _ _ _ _ _ _ _ _ _ _ hdL).trans
        (evalEng2_doom13U _ _ _ _ _ _ _ _ _ _ _ (Or.inl hdR)).symm

end StepSend13U

section Top13U

variable [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]
  (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
  (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType K] in
private theorem runHM_initCKAU_none (tH tStar : ℕ) (cs : CKA.GameState Γ T) :
    runHM (CKA.oracleImpl cka Δcka tH)
      (initCKAU cka prng fs lam ⟨false, none, tStar⟩) (({} : CKAState T I), (none : Option K)) cs =
      ($ᵗ KR : ProbComp KR) >>= fun kr =>
        ($ᵗ KC : ProbComp KC) >>= fun kc =>
          let out := prng.up (prng.init kr) lam
          pure ((some (mkParties (some (cka.initA kc)) (some (cka.initB kc)) out.1
                  (fs.initSender out.2) (fs.initReceiver out.2)),
                (({} : CKAState T I), (none : Option K))), cs) := by
  change (simulateQ (outerFull (CKA.oracleImpl cka Δcka tH))
    ((initCKA cka prng fs lam ⟨false, none, tStar⟩).run {} >>= fun p =>
      pure (p.1, (p.2, (none : Option K))))).run cs = _
  unfold initCKA; dsimp only
  simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure,
    simulateQ_bind, simulateQ_pure, simulateQ_outerFull_sampleT,
    bind_map_left, bind_assoc, pure_bind]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType K] in
private theorem runHM_initCKAU_some (tH l tStar : ℕ) (cs : CKA.GameState Γ T) :
    runHM (CKA.oracleImpl cka Δcka tH)
      (initCKAU cka prng fs lam ⟨false, some l, tStar⟩) (({} : CKAState T I), (none : Option K)) cs =
      ($ᵗ KR : ProbComp KR) >>= fun kr =>
        let out := prng.up (prng.init kr) lam
        pure ((some (mkParties none none out.1
                (fs.initSender out.2) (fs.initReceiver out.2)),
              (({} : CKAState T I), (none : Option K))), cs) := by
  change (simulateQ (outerFull (CKA.oracleImpl cka Δcka tH))
    ((initCKA cka prng fs lam ⟨false, some l, tStar⟩).run {} >>= fun p =>
      pure (p.1, (p.2, (none : Option K))))).run cs = _
  unfold initCKA; dsimp only
  simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure,
    simulateQ_bind, simulateQ_pure, simulateQ_outerFull_sampleT,
    bind_map_left, bind_assoc, pure_bind]

omit [DecidableEq I] in
private theorem branch_engRun_eq (tH : ℕ) (mo : Mode) (π_eng π_out : Policy) (tStar : ℕ)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    CKA.branch cka Δcka tH false
      (show CKA.Adversary Γ CCoins T I from
        show CKA.AdversaryComp Γ CCoins T I Bool from do
          let b ← sampleT Bool
          match ← Engine.engRun (hooksCKAU cka prng fs Δcka mo) (2 + Δcka) qep fs.maxSkip
              (Config.priv tStar) π_eng (initCKAU cka prng fs lam mo) ({}, none) b A with
          | none => sampleT Bool
          | some (b', es) => Engine.privOut (2 + Δcka) π_out b b' es) =
      (($ᵗ KC : ProbComp KC) >>= fun kc_game =>
        ($ᵗ Bool : ProbComp Bool) >>= fun b =>
        runHM (CKA.oracleImpl cka Δcka tH)
          (initCKAU cka prng fs lam mo) ({}, none) (CKA.initState cka kc_game false) >>= fun x =>
        match x.1.1 with
        | none => ($ᵗ Bool : ProbComp Bool)
        | some (vA, vB) =>
          let g : Ctx (Option Γ) T Sig SS RS M E :=
            { st := fun P => match P with | .A => vA | .B => vB, b }
          evalEng2 (CKA.oracleImpl cka Δcka tH) (hooksCKAU cka prng fs Δcka mo)
            (2 + Δcka) qep fs.maxSkip (Config.priv tStar) π_eng π_out b A
            ({ g, h := x.1.2 }, x.2)) := by
  refine bind_congr fun kc_game => ?_
  change Prod.fst <$> (simulateQ (outerFull (CKA.oracleImpl cka Δcka tH)) _).run
    (CKA.initState cka kc_game false) = _
  simp only [engRun, simulateQ_bind, StateT.run_bind, bind_assoc,
    simulateQ_outerFull_sampleT, bind_map_left, map_bind, runHM]
  refine bind_congr fun b => bind_congr fun ⟨⟨vs, h⟩, os₁⟩ => ?_
  cases vs with
  | none => simp [simulateQ_outerFull_sampleT]
  | some p =>
    rcases p with ⟨vA, vB⟩
    simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      pure_bind, bind_assoc]
    change (do
      let r ← (simulateQ (outerFull (CKA.oracleImpl cka Δcka tH))
        ((simulateQ (implE (hooksCKAU cka prng fs Δcka mo) (2 + Δcka) qep fs.maxSkip
          (Config.priv tStar) π_eng) A).run { g := _, h })).run os₁
      Prod.fst <$> (simulateQ (outerFull (CKA.oracleImpl cka Δcka tH))
        (privOut (2 + Δcka) π_out b r.1.1 r.1.2)).run r.2) = _
    simp only [evalEng2, runEM, bind_map_left]
    refine bind_congr fun r => ?_
    exact simulateQ_outerFull_privOut (CKA.oracleImpl cka Δcka tH) (2 + Δcka) π_out b r.1.1 r.1.2 r.2

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
private theorem init_sync13U (tL : Option ℕ) (b : Bool) (kr : KR) (kcL kc : KC) :
    let out := prng.up (prng.init kr) lam
    let γAR : Option Γ := if tL.isNone then some (cka.initA kc) else none
    let γBR : Option Γ := if tL.isNone then some (cka.initB kc) else none
    let pL := mkParties (T := T) (some (cka.initA kc)) (some (cka.initB kc)) out.1
      (fs.initSender out.2) (fs.initReceiver out.2)
    let pR := mkParties (T := T) γAR γBR out.1 (fs.initSender out.2) (fs.initReceiver out.2)
    let gL : Ctx (Option Γ) T Sig SS RS M E :=
      { st := fun P => match P with | .A => pL.1 | .B => pL.2, b }
    let gR : Ctx (Option Γ) T Sig SS RS M E :=
      { st := fun P => match P with | .A => pR.1 | .B => pR.2, b }
    Sync13U Δcka tL
      ({ g := gL, h := (({} : CKAState T I), (none : Option K)) }, CKA.initState cka kcL false)
      ({ g := gR, h := (({} : CKAState T I), (none : Option K)) }, CKA.initState cka kc false) := by
  intro out γAR γBR pL pR gL gR
  refine ⟨rfl, rfl, rfl, ⟨fun _ h => by contradiction, fun _ h => by contradiction⟩, rfl,
    ?_, ?_, ?_⟩
  · intro P
    cases tL <;> cases P <;>
      refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, _, rfl, ?_⟩ <;>
      · dsimp [gL]; simp [gR, pR, mkParties, γAR, γBR, healEpoch]
  · refine ⟨rfl, fun P htL _ => ?_⟩
    cases P <;> exact ⟨rfl, rfl⟩
  · exact ⟨fun _ _ => rfl, Or.inl rfl⟩

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType CCoins] [SampleableType I] [SampleableType K] in
private theorem deq_swap_kc_b_kr (f : Bool → KR → KC → ProbComp Bool) :
    DEq (($ᵗ KC : ProbComp KC) >>= fun kc =>
          ($ᵗ Bool : ProbComp Bool) >>= fun b =>
          ($ᵗ KR : ProbComp KR) >>= fun kr => f b kr kc)
        (($ᵗ Bool : ProbComp Bool) >>= fun b =>
          ($ᵗ KR : ProbComp KR) >>= fun kr =>
          ($ᵗ KC : ProbComp KC) >>= fun kc => f b kr kc) :=
  (DEq.swap ($ᵗ KC) ($ᵗ Bool) _).trans
    (DEq.bind_right ($ᵗ Bool) fun _ => DEq.swap ($ᵗ KC) ($ᵗ KR) _)

theorem branch_redCKAPrivUUniAt_dEq_redCKAPrivU_false
    (_hc : cka.Correct) (tL : Option ℕ) (t : ℕ) (_ht : 0 < t)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) tL t = true)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    DEq (CKA.branch cka Δcka 0 false
          (redCKAPrivUUniAt cka prng fs lam Δcka qep tL t A))
        (CKA.branch cka Δcka (healEpoch tL) false
          (redCKAPrivU cka prng fs lam Δcka qep tL t A)) := by
  have hLHS : CKA.branch cka Δcka 0 false
      (redCKAPrivUUniAt cka prng fs lam Δcka qep tL t A) = _ :=
    branch_engRun_eq cka prng fs lam Δcka qep 0 ⟨false, none, t⟩
      (polUni12 Δcka t) ⟨false, tL, t⟩ t A
  have hRHS : CKA.branch cka Δcka (healEpoch tL) false
      (redCKAPrivU cka prng fs lam Δcka qep tL t A) = _ :=
    branch_engRun_eq cka prng fs lam Δcka qep (healEpoch tL) ⟨false, tL, t⟩
      ⟨false, tL, t⟩ ⟨false, tL, t⟩ t A
  rw [hLHS, hRHS]
  cases tL with
  | none =>
    refine DEq.bind_right ($ᵗ KC) fun kc_game => DEq.bind_right ($ᵗ Bool) fun b => ?_
    rw [runHM_initCKAU_none, runHM_initCKAU_none]
    simp only [bind_assoc, pure_bind]
    refine DEq.bind_right ($ᵗ KR) fun kr => DEq.bind_right ($ᵗ KC) fun kc => ?_
    have hinit := init_sync13U cka prng fs lam Δcka none b kr kc_game kc
    rcases hinit with ⟨h1, h2, h3, h4, h5, h6, -, h8⟩
    exact evalEng2_sync13U cka prng fs Δcka qep none t b A _ _ hvg
      (Or.inl ⟨h1, h2, h3, h4, h5, h6, ⟨rfl, fun _ ht => by simp at ht⟩, h8⟩)
  | some l =>
    let f : Bool → KR → KC → ProbComp Bool := fun b kr kc =>
      let out := prng.up (prng.init kr) lam
      let pR := mkParties (T := T) (none : Option Γ) none out.1
        (fs.initSender out.2) (fs.initReceiver out.2)
      evalEng2 (CKA.oracleImpl cka Δcka (healEpoch (some l)))
        (hooksCKAU cka prng fs Δcka ⟨false, some l, t⟩)
        (2 + Δcka) qep fs.maxSkip (Config.priv t) ⟨false, some l, t⟩ ⟨false, some l, t⟩ b A
        ({ g := { st := fun P => match P with | .A => pR.1 | .B => pR.2, b },
           h := (({} : CKAState T I), (none : Option K)) }, CKA.initState cka kc false)
    have hstep : ∀ kc_dummy : KC,
        DEq (($ᵗ Bool : ProbComp Bool) >>= fun b =>
              runHM (CKA.oracleImpl cka Δcka 0)
                (initCKAU cka prng fs lam ⟨false, none, t⟩) (({} : CKAState T I), (none : Option K))
                (CKA.initState cka kc_dummy false) >>= fun x =>
              match x.1.1 with
              | none => ($ᵗ Bool : ProbComp Bool)
              | some (vA, vB) =>
                evalEng2 (CKA.oracleImpl cka Δcka 0) (hooksCKAU cka prng fs Δcka ⟨false, none, t⟩)
                  (2 + Δcka) qep fs.maxSkip (Config.priv t) (polUni12 Δcka t) ⟨false, some l, t⟩ b A
                  ({ g := { st := fun P => match P with | .A => vA | .B => vB, b }, h := x.1.2 }, x.2))
            (($ᵗ Bool : ProbComp Bool) >>= fun b =>
              ($ᵗ KR : ProbComp KR) >>= fun kr =>
              ($ᵗ KC : ProbComp KC) >>= fun kc => f b kr kc) := by
      intro kc_dummy
      refine DEq.bind_right ($ᵗ Bool) fun b => ?_
      rw [runHM_initCKAU_none]
      simp only [bind_assoc, pure_bind]
      refine DEq.bind_right ($ᵗ KR) fun kr => DEq.bind_right ($ᵗ KC) fun kc => ?_
      exact evalEng2_sync13U cka prng fs Δcka qep (some l) t b A _ _ hvg
        (Or.inl (init_sync13U cka prng fs lam Δcka (some l) b kr kc_dummy kc))
    have hR : DEq (($ᵗ KC : ProbComp KC) >>= fun kc =>
          ($ᵗ Bool : ProbComp Bool) >>= fun b =>
          ($ᵗ KR : ProbComp KR) >>= fun kr => f b kr kc)
        (($ᵗ KC : ProbComp KC) >>= fun kc =>
          ($ᵗ Bool : ProbComp Bool) >>= fun b =>
          runHM (CKA.oracleImpl cka Δcka (healEpoch (some l)))
            (initCKAU cka prng fs lam ⟨false, some l, t⟩) (({} : CKAState T I), (none : Option K))
            (CKA.initState cka kc false) >>= fun x =>
          match x.1.1 with
          | none => ($ᵗ Bool : ProbComp Bool)
          | some (vA, vB) =>
            evalEng2 (CKA.oracleImpl cka Δcka (healEpoch (some l)))
              (hooksCKAU cka prng fs Δcka ⟨false, some l, t⟩)
              (2 + Δcka) qep fs.maxSkip (Config.priv t) ⟨false, some l, t⟩ ⟨false, some l, t⟩ b A
              ({ g := { st := fun P => match P with | .A => vA | .B => vB, b }, h := x.1.2 }, x.2)) := by
      refine DEq.bind_right ($ᵗ KC) fun kc => DEq.bind_right ($ᵗ Bool) fun b => ?_
      rw [runHM_initCKAU_some]
      simp only [bind_assoc, pure_bind]
      exact DEq.refl _
    exact (DEq.bind_right ($ᵗ KC) hstep).trans
      ((DEq.bind_const ($ᵗ KC) _).trans ((deq_swap_kc_b_kr f).symm.trans hR))

end Top13U

end SendAndTop13U

end CryptoGames.SM.Construction.PrivL13U
