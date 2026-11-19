/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem12.Stage2Defs
import Computational.Proofs.CryptoGames.SM.Theorem12.Lemma15
import Computational.Proofs.CryptoGames.SM.Theorem12.Stage2L15UniEager

/-!
# Unified Lemma 15 Coupling for Stage-2 Switch-Back (`SM/Theorem12`)

**Checked by Lean.** No theorem of `Computational/Theorems/` unfolds a definition of this file, and
Lean's kernel checks every proof in it: you do not need to read it to trust those theorems.

Couples `CKA.branch cka Δcka 0 false (redCKAPrivUUniAll ...)` (`0 < t`) to
`FSAEAD.game fs (redFSPrivUni ...)` up to an FS-AEAD `win` (`FSAEAD.advantage fs (redFSPrivUniCoin ...)`),
reusing `PrivL15.ActiveInv` via a ghost witness alongside the eager single-slot CKA coupling.-/

set_option autoImplicit false

public section

open OracleComp OracleSpec ENNReal MeasureTheory CryptoGames.Lazy
open CryptoGames.SM.Engine

namespace CryptoGames.SM.Construction

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

variable (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
  (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)

section Stage2SwitchBack

/-! ### Section 1: Coupled state invariant (`SyncU15`, `Inv15U`, `CloseByEngU`) -/

private abbrev StateLU (Γ T Sig SS RS M E I K : Type) :=
  Engine.EState (Engine.VP (Option Γ) T Sig SS RS) M (Header T × E) (CKAUState T I K) ×
    CKAEagerState Γ T K

private def AbortInvU (b : Bool) (sL : StateLU Γ T Sig SS RS M E I K)
    (sR : PrivL15.StateR Γ T Sig K I SS RS M E) : Prop :=
  sL.1.abort = true ∧ sR.1.abort = true ∧ sR.2.win = false ∧ sR.2.b = b

/-- Synchronises the eager unified `hooksCKAUEager` state `sL` with a ghost `PrivL15.StateL`
witness `sL_g` (at `tL = none`) and the unified `hooksFS` state `sR`. -/
private structure SyncU15 (prng : PRFPRNG KR Sig I K) (t : ℕ) (b : Bool)
    (sL : StateLU Γ T Sig SS RS M E I K)
    (sL_g : PrivL15.StateL Γ T Sig SS RS M E K I)
    (sR : PrivL15.StateR Γ T Sig K I SS RS M E) : Prop where
  abortL : sL.1.abort = false
  winL : sL.1.g.win = false
  bL : sL.1.g.b = b
  epoch_eq : sL.1.g.epoch = sR.1.g.epoch
  idx_eq : sL.1.g.idx = sR.1.g.idx
  tL_eq : sL.1.g.tL = sR.1.g.tL
  chall_eq : sL.1.g.chall = sR.1.g.chall
  comp_eq : sL.1.g.comp = sR.1.g.comp
  maxAcc_eq : sL.1.g.maxAcc = sR.1.g.maxAcc
  leaks_eq : sL.1.g.leaks = sR.1.g.leaks
  corrs_eq : sL.1.g.corrs = sR.1.g.corrs
  trans_eq : sL.1.g.trans = sL_g.1.g.trans
  idL : ∀ P, (sL.1.g.st P).id = P
  tcurL : ∀ P, (sL.1.g.st P).tcur = sR.1.g.epoch P
  γ_eq : ∀ P, (sL.1.g.st P).γ = some (sR.1.g.st P).γ
  Tcur_eq : ∀ P, (sL.1.g.st P).curCkaMsg = (sR.1.g.st P).curCkaMsg
  root_eq : ∀ P, (sL.1.g.st P).root = (sR.1.g.st P).root
  vS_eq : ∀ P, (sL.1.g.st P).vS = (sL_g.1.g.st P).vS
  vR_eq : ∀ P, (sL.1.g.st P).vR = (sL_g.1.g.st P).vR
  same_ep_root : sR.1.g.epoch .A = sR.1.g.epoch .B →
    (sR.1.g.st .A).root = (sR.1.g.st .B).root
  cacheL_none : ∀ t', sR.1.h.cache t' = none → sL.1.h.1.cache t' = none
  cache_pending : ∀ t' Tc σc kc ext,
    sR.1.g.epoch (Party.receiverOf t') < t' →
    sR.1.h.cache t' = some (Tc, σc, kc, ext) →
    (sR.1.g.st (Party.senderOf t')).root = σc ∧
      ∃ Ik, sL.1.h.1.cache t' = some (Tc, Ik) ∧
        (prng.up (sR.1.g.st (Party.receiverOf t')).root Ik).1 = σc ∧
        (t' ≠ t → (prng.up (sR.1.g.st (Party.receiverOf t')).root Ik).2 = kc)
  kOpt_eq : ∀ Tc σL k₀, sL_g.1.h.cache t = some (Tc, σL, k₀) → sL.1.h.2 = some k₀
  slot_eq : sL.2.2 = sL_g.2.2

private def Inv15U (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep t : ℕ) (b : Bool)
    (sL : StateLU Γ T Sig SS RS M E I K)
    (sR : PrivL15.StateR Γ T Sig K I SS RS M E) : Prop :=
  AbortInvU b sL sR ∨
    ∃ sL_g, PrivL15.ActiveInv fs Δcka qep none t b sL_g sR ∧ SyncU15 prng t b sL sL_g sR

private def CloseByEngU (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep t : ℕ) (b : Bool)
    (oa : OracleComp (PrivL15.AdvSpec Γ T Sig SS RS M CCoins E) Bool)
    (sL : StateLU Γ T Sig SS RS M E I K)
    (sR : PrivL15.StateR Γ T Sig K I SS RS M E) : Prop :=
  PrivL15.CloseBy
    (evalEngU (eagerCKAKeyImpl cka Δcka 0) (hooksCKAUEager cka prng fs Δcka ⟨false, none, t⟩)
      (2 + Δcka) qep fs.maxSkip t (polUni12 Δcka t) b oa sL)
    (evalEngMU fs (hooksFS cka prng fs Δcka ⟨false, none, t⟩ 0)
      (2 + Δcka) qep fs.maxSkip t (polUni12 Δcka t) b oa sR)
    (PrivL15.evalEngL fs (hooksFS cka prng fs Δcka ⟨false, none, t⟩ 0)
      (2 + Δcka) qep fs.maxSkip (Config.priv t) (polUni12 Δcka t) oa sR)

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType I] [SampleableType K] in
private theorem SyncU15.safeCh_eq {prng : PRFPRNG KR Sig I K} {t : ℕ} {b : Bool}
    {sL : StateLU Γ T Sig SS RS M E I K}
    {sL_g : PrivL15.StateL Γ T Sig SS RS M E K I}
    {sR : PrivL15.StateR Γ T Sig K I SS RS M E}
    (hs : SyncU15 prng t b sL sL_g sR) (Δ : ℕ) (P : Party) :
    sL.1.g.safeCh Δ P = sR.1.g.safeCh Δ P := by
  simp [GameState.safeCh, hs.tL_eq, hs.epoch_eq]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType I] [SampleableType K] in
private theorem SyncU15.safeInj_eq {prng : PRFPRNG KR Sig I K} {t : ℕ} {b : Bool}
    {sL : StateLU Γ T Sig SS RS M E I K}
    {sL_g : PrivL15.StateL Γ T Sig SS RS M E K I}
    {sR : PrivL15.StateR Γ T Sig K I SS RS M E}
    (hs : SyncU15 prng t b sL sL_g sR) (Δ : ℕ) :
    sL.1.g.safeInj Δ = sR.1.g.safeInj Δ := by
  simp [GameState.safeInj, hs.tL_eq, hs.epoch_eq]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType I] [SampleableType K] in
private theorem SyncU15.trivial_eq {fs : FSAEADScheme K SS RS (Header T) M E}
    {Δcka qep t : ℕ} {b : Bool} {prng : PRFPRNG KR Sig I K}
    {sL : StateLU Γ T Sig SS RS M E I K}
    {sL_g : PrivL15.StateL Γ T Sig SS RS M E K I}
    {sR : PrivL15.StateR Γ T Sig K I SS RS M E}
    (hg : PrivL15.ActiveInv fs Δcka qep none t b sL_g sR)
    (hs : SyncU15 prng t b sL sL_g sR) (Δ : ℕ) (pos : Pos) :
    sL.1.g.trivial Δ pos = sR.1.g.trivial Δ pos := by
  have h1 : sL.1.g.trivial Δ pos = sL_g.1.g.trivial Δ pos := by
    simp [GameState.trivial, hs.comp_eq, hg.comp_eq, hs.trans_eq, hs.tL_eq, hg.tL_eq]
  exact h1.trans (hg.trivial_eq Δ pos)

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType I] [SampleableType K] in
private theorem SyncU15.corrAllowed_eq {fs : FSAEADScheme K SS RS (Header T) M E}
    {Δcka qep t : ℕ} {b : Bool} {prng : PRFPRNG KR Sig I K}
    {sL : StateLU Γ T Sig SS RS M E I K}
    {sL_g : PrivL15.StateL Γ T Sig SS RS M E K I}
    {sR : PrivL15.StateR Γ T Sig K I SS RS M E}
    (hg : PrivL15.ActiveInv fs Δcka qep none t b sL_g sR)
    (hs : SyncU15 prng t b sL sL_g sR) (P : Party) :
    sL.1.g.corrAllowed P = sR.1.g.corrAllowed P := by
  have h1 : sL.1.g.corrAllowed P = sL_g.1.g.corrAllowed P := by
    simp [GameState.corrAllowed, hs.chall_eq, hg.chall_eq, hs.trans_eq, hs.comp_eq, hg.comp_eq]
  exact h1.trans (hg.corrAllowed_eq P)

omit [DecidableEq M] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType I] [SampleableType K] in
private theorem SyncU15.inTransit_eq {prng : PRFPRNG KR Sig I K} {t : ℕ} {b : Bool}
    {sL : StateLU Γ T Sig SS RS M E I K}
    {sL_g : PrivL15.StateL Γ T Sig SS RS M E K I}
    {sR : PrivL15.StateR Γ T Sig K I SS RS M E}
    (hs : SyncU15 prng t b sL sL_g sR) (P : Party) (c : Header T × E) :
    sL.1.g.inTransit P c = sL_g.1.g.inTransit P c := by
  simp [GameState.inTransit, hs.trans_eq]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E] in
private theorem leakDoom_eq_of_fields {StL StR : Type}
    {gL gL' : GameState StL M (Header T × E)}
    {gR gR' : GameState StR M (Header T × E)}
    (hep : gL.epoch = gR.epoch) (hleaks : gL'.leaks = gR'.leaks) (π : Engine.Policy) :
    π.leakDoom gL gL' = π.leakDoom gR gR' := by
  simp [Engine.Policy.leakDoom, hep, hleaks]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E] in
private theorem corrDoom_eq_of_epoch {StL StR : Type}
    {gL : GameState StL M (Header T × E)}
    {gR : GameState StR M (Header T × E)}
    (hep : gL.epoch = gR.epoch) (π : Engine.Policy) (P : Party) :
    π.corrDoom gL P = π.corrDoom gR P := by
  simp [Engine.Policy.corrDoom, hep]

omit [SampleableType KR] [SampleableType KC] in
private theorem closeBy_evalEngU_pure (t : ℕ) (b a : Bool)
    (sL : StateLU Γ T Sig SS RS M E I K)
    (sR : PrivL15.StateR Γ T Sig K I SS RS M E)
    (hInv : Inv15U prng fs Δcka qep t b sL sR) :
    CloseByEngU cka prng fs Δcka qep t b (pure a) sL sR := by
  unfold CloseByEngU
  rw [evalEngU_pure, evalEngMU_pure]
  refine PrivL15.closeBy_of_eq ?_
  rcases hInv with ⟨habL, habR, hwinFS, _⟩ | ⟨sL_g, hg, hs⟩
  · simp [fsPrivOutUni, privOutUni, privValidUni, habL, habR, hwinFS]
  · simp [fsPrivOutUni, privOutUni, privValidUni, hs.abortL, hg.abortR, hg.winFS,
      PrivL15.canon_eq_of_leaks_eq _ _ _ hs.leaks_eq]

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
  [SampleableType I] [SampleableType K] in
private theorem evalEngL_liftM_query_bind {Γv Sv SSv RSv HS : Type}
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (hk : Engine.Hooks (FSAEAD.spec SS RS (Header T) M E) HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : Config M) (π : Engine.Policy)
    (q : (PrivL15.AdvSpec Γ T Sig SS RS M CCoins E).Domain)
    (k : (PrivL15.AdvSpec Γ T Sig SS RS M CCoins E).Range q →
      OracleComp (PrivL15.AdvSpec Γ T Sig SS RS M CCoins E) Bool)
    (s : Engine.EState (Engine.VP Γv T Sv SSv RSv) M (Header T × E) HS ×
      FSAEAD.State SS RS (Header T) M E) :
    PrivL15.evalEngL fs hk Δ qep maxSkip cfg π (liftM (OracleSpec.query q) >>= k) s =
      PrivL15.runEM (FSAEAD.oracleImpl fs) (Engine.implE hk Δ qep maxSkip cfg π q) s >>=
        fun r => PrivL15.evalEngL fs hk Δ qep maxSkip cfg π (k r.1) r.2 :=
  PrivL15.evalEngL_query_bind fs hk Δ qep maxSkip cfg π q k s

omit [SampleableType KR] [SampleableType KC] in
private theorem closeBy_of_det_stepU (t : ℕ) (b : Bool)
    (q : (PrivL15.AdvSpec Γ T Sig SS RS M CCoins E).Domain)
    (k : (PrivL15.AdvSpec Γ T Sig SS RS M CCoins E).Range q →
      OracleComp (PrivL15.AdvSpec Γ T Sig SS RS M CCoins E) Bool)
    (sL sL' : StateLU Γ T Sig SS RS M E I K)
    (sR sR' : PrivL15.StateR Γ T Sig K I SS RS M E)
    (ansL ansR : (PrivL15.AdvSpec Γ T Sig SS RS M CCoins E).Range q)
    (hL : PrivL15.runEM (eagerCKAKeyImpl cka Δcka 0)
      (Engine.implE (hooksCKAUEager cka prng fs Δcka ⟨false, none, t⟩) (2 + Δcka) qep fs.maxSkip
        (Config.priv t) (polUni12 Δcka t) q) sL = pure (ansL, sL'))
    (hR : PrivL15.runEM (FSAEAD.oracleImpl fs)
      (Engine.implE (hooksFS cka prng fs Δcka ⟨false, none, t⟩ 0) (2 + Δcka) qep fs.maxSkip
        (Config.priv t) (polUni12 Δcka t) q) sR = pure (ansR, sR'))
    (ih : ∀ u sL₁ sR₁, Inv15U prng fs Δcka qep t b sL₁ sR₁ →
      CloseByEngU cka prng fs Δcka qep t b (k u) sL₁ sR₁)
    (hpost : sR'.2.win = true ∨ (ansL = ansR ∧ Inv15U prng fs Δcka qep t b sL' sR')) :
    CloseByEngU cka prng fs Δcka qep t b (liftM (OracleSpec.query q) >>= k) sL sR := by
  unfold CloseByEngU
  rw [evalEngU_query_bind, evalEngMU_query_bind, evalEngL_liftM_query_bind, hL, hR,
    pure_bind, pure_bind, pure_bind]
  rcases hpost with hwin | ⟨rfl, hInv'⟩
  · exact PrivL15.closeBy_of_evalDist_eq_one
      (PrivL15.evalEngL_eq_one_of_win fs _ _ _ _ _ _ (k ansR) sR' hwin)
  · exact ih ansL sL' sR' hInv'

omit [SampleableType KR] [SampleableType KC] in
private theorem closeBy_coinsEU (t : ℕ) (b : Bool)
    (n : unifSpec.Domain)
    (k : (PrivL15.AdvSpec Γ T Sig SS RS M CCoins E).Range (Sum.inl n) →
      OracleComp (PrivL15.AdvSpec Γ T Sig SS RS M CCoins E) Bool)
    (sL : StateLU Γ T Sig SS RS M E I K)
    (sR : PrivL15.StateR Γ T Sig K I SS RS M E)
    (hInv : Inv15U prng fs Δcka qep t b sL sR)
    (ih : ∀ u sL₁ sR₁, Inv15U prng fs Δcka qep t b sL₁ sR₁ →
      CloseByEngU cka prng fs Δcka qep t b (k u) sL₁ sR₁) :
    CloseByEngU cka prng fs Δcka qep t b (liftM (OracleSpec.query (Sum.inl n)) >>= k) sL sR := by
  unfold CloseByEngU
  rw [evalEngU_query_bind, evalEngMU_query_bind, evalEngL_liftM_query_bind]
  have hL : PrivL15.runEM (eagerCKAKeyImpl cka Δcka 0)
      (Engine.implE (hooksCKAUEager cka prng fs Δcka ⟨false, none, t⟩) (2 + Δcka) qep fs.maxSkip
        (Config.priv t) (polUni12 Δcka t) (.inl n)) sL =
      (fun u => (u, sL)) <$> (OracleSpec.query (spec := unifSpec) n : ProbComp _) := by
    simp [PrivL15.runEM, Engine.implE, Engine.coinsE, PrivL15.outerFull,
      StateT.run_lift, map_eq_bind_pure_comp]
  have hR : PrivL15.runEM (FSAEAD.oracleImpl fs)
      (Engine.implE (hooksFS cka prng fs Δcka ⟨false, none, t⟩ 0) (2 + Δcka) qep fs.maxSkip
        (Config.priv t) (polUni12 Δcka t) (.inl n)) sR =
      (fun u => (u, sR)) <$> (OracleSpec.query (spec := unifSpec) n : ProbComp _) := by
    simp [PrivL15.runEM, Engine.implE, Engine.coinsE, PrivL15.outerFull,
      StateT.run_lift, map_eq_bind_pure_comp]
  rw [hL, hR, bind_map_left, bind_map_left, bind_map_left]
  exact PrivL15.closeBy_bind _ fun u => ih u sL sR hInv

omit [SampleableType KR] [SampleableType KC] in
private theorem closeBy_sm_of_abortInvU (t : ℕ) (b : Bool)
    (q : (spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Domain)
    (k : (PrivL15.AdvSpec Γ T Sig SS RS M CCoins E).Range (Sum.inr q) →
      OracleComp (PrivL15.AdvSpec Γ T Sig SS RS M CCoins E) Bool)
    (sL : StateLU Γ T Sig SS RS M E I K)
    (sR : PrivL15.StateR Γ T Sig K I SS RS M E)
    (hab : AbortInvU b sL sR)
    (ih : ∀ u sL₁ sR₁, Inv15U prng fs Δcka qep t b sL₁ sR₁ →
      CloseByEngU cka prng fs Δcka qep t b (k u) sL₁ sR₁) :
    CloseByEngU cka prng fs Δcka qep t b (liftM (OracleSpec.query (Sum.inr q)) >>= k) sL sR := by
  have ⟨habL, habR, _, _⟩ := hab
  rcases q with ((((q | q) | q) | q) | q) <;>
    refine closeBy_of_det_stepU cka prng fs Δcka qep t b (Sum.inr _) k sL sL sR sR none none
      ?_ ?_ ih (Or.inr ⟨rfl, Or.inl hab⟩) <;>
    simp [PrivL15.runEM, Engine.implE, Engine.transmitE, Engine.challE, Engine.deliverE,
      Engine.injectE, Engine.corrE, habL, habR]

/-! ### Section 2: `corrE` -/

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType I] [SampleableType K] in
private theorem SyncU15.afterCorr {fs : FSAEADScheme K SS RS (Header T) M E}
    {Δcka qep t : ℕ} {b : Bool} {prng : PRFPRNG KR Sig I K}
    {sL : StateLU Γ T Sig SS RS M E I K}
    {sL_g : PrivL15.StateL Γ T Sig SS RS M E K I}
    {sR : PrivL15.StateR Γ T Sig K I SS RS M E}
    {hR' : FSState T Sig K I SS RS E} {osR' : FSAEAD.State SS RS (Header T) M E}
    (hg : PrivL15.ActiveInv fs Δcka qep none t b sL_g sR)
    (hs : SyncU15 prng t b sL sL_g sR) (P : Party)
    (hg' : PrivL15.ActiveInv fs Δcka qep none t b
      ({ sL_g.1 with g := sL_g.1.g.afterCorr P }, sL_g.2)
      ({ sR.1 with g := sR.1.g.afterCorr P, h := hR' }, osR'))
    (hcache : hR'.cache = sR.1.h.cache) :
    SyncU15 prng t b
      ({ sL.1 with g := sL.1.g.afterCorr P }, sL.2)
      ({ sL_g.1 with g := sL_g.1.g.afterCorr P }, sL_g.2)
      ({ sR.1 with g := sR.1.g.afterCorr P, h := hR' }, osR') := by
  have hcompL : (sL.1.g.afterCorr P).comp = (sL_g.1.g.afterCorr P).comp := by
    simp [GameState.afterCorr, GameState.leak, hs.trans_eq, hs.comp_eq, hg.comp_eq]
  refine
    { abortL := hs.abortL
      winL := hs.winL
      bL := hs.bL
      epoch_eq := hs.epoch_eq
      idx_eq := hs.idx_eq
      tL_eq := by simp [GameState.afterCorr, GameState.leak, hs.epoch_eq, hs.tL_eq]
      chall_eq := hs.chall_eq
      comp_eq := hcompL.trans hg'.comp_eq
      maxAcc_eq := hs.maxAcc_eq
      leaks_eq := by simp [GameState.afterCorr, GameState.leak, hs.epoch_eq, hs.tL_eq, hs.leaks_eq]
      corrs_eq := by simp [GameState.afterCorr, GameState.leak, hs.corrs_eq, hs.epoch_eq]
      trans_eq := hs.trans_eq
      idL := hs.idL
      tcurL := hs.tcurL
      γ_eq := hs.γ_eq
      Tcur_eq := hs.Tcur_eq
      root_eq := hs.root_eq
      vS_eq := hs.vS_eq
      vR_eq := hs.vR_eq
      same_ep_root := hs.same_ep_root
      cacheL_none := fun t' hc => hs.cacheL_none t' (hcache ▸ hc)
      cache_pending := fun t' Tc σc kc ext hlt hc =>
        hs.cache_pending t' Tc σc kc ext hlt (hcache ▸ hc)
      kOpt_eq := hs.kOpt_eq
      slot_eq := hs.slot_eq }

omit [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType I] in
private theorem reveal_ckau_eq (t : ℕ) {b : Bool}
    {sL : StateLU Γ T Sig SS RS M E I K}
    {sL_g : PrivL15.StateL Γ T Sig SS RS M E K I}
    {sR : PrivL15.StateR Γ T Sig K I SS RS M E}
    (hg : PrivL15.ActiveInv fs Δcka qep none t b sL_g sR)
    (hs : SyncU15 prng t b sL sL_g sR) (P : Party) :
    ((hooksCKAUEager cka prng fs Δcka ⟨false, none, t⟩).reveal sL.1.g P (sL.1.g.st P)).run sL.1.h =
      pure (some (PrivL15.realSt sR P), sL.1.h) := by
  have hreal : realParty (sL.1.g.st P) (sR.1.g.st P).γ (sL.1.g.st P).root
      (sL.1.g.st P).vS (sL.1.g.st P).vR = PrivL15.realSt sR P := by
    simp only [realParty, PrivL15.realSt, hs.idL P, hg.idR P, hs.root_eq P,
      hs.vS_eq P, hg.vS_eq P, hs.vR_eq P, hs.Tcur_eq P, hs.tcurL P, hg.tcurR P]
    congr 1
    funext t'
    exact hg.vR_eq P t'
  simp [hooksCKAUEager, hooksCKAU, liftCKAComp, hs.γ_eq P, hreal]

omit [Inhabited E] [SampleableType KR] [SampleableType KC] in
private theorem reveal_fs_with_cache (t : ℕ) {b : Bool}
    {sL_g : PrivL15.StateL Γ T Sig SS RS M E K I}
    {sR : PrivL15.StateR Γ T Sig K I SS RS M E}
    (hg : PrivL15.ActiveInv fs Δcka qep none t b sL_g sR) (P : Party)
    (hca : sR.1.g.corrAllowed P = true) :
    ∃ hR' osR',
      PrivL15.runHM (FSAEAD.oracleImpl fs)
        ((hooksFS cka prng fs Δcka ⟨false, none, t⟩ 0).reveal sR.1.g P (sR.1.g.st P))
        sR.1.h sR.2 = pure ((some (PrivL15.realSt sR P), hR'), osR') ∧
      PrivL15.ActiveInv fs Δcka qep none t b
        ({ sL_g.1 with g := sL_g.1.g.afterCorr P }, sL_g.2)
        ({ sR.1 with g := sR.1.g.afterCorr P, h := hR' }, osR') ∧
      hR'.cache = sR.1.h.cache := by
  cases hext : sR.1.h.ext with
  | some p =>
    rcases p with ⟨ss₀, rs₀⟩
    have hcurSS : PrivL15.curSS sR.1.h sR.2 = ss₀ := by simp [PrivL15.curSS, hext]
    have hcurRS : PrivL15.curRS sR.1.h sR.2 = rs₀ := by simp [PrivL15.curRS, hext]
    refine ⟨sR.1.h, sR.2, ?_, hg.afterCorr_unchanged P hca, rfl⟩
    rcases hvS : (sR.1.g.st P).vS with _ | _ | ss <;>
    · rcases hvR : (sR.1.g.st P).vR t with _ | _ | rs
      · simp [PrivL15.runHM, hooksFS, hext, hvS, hvR, PrivL15.realSt, hcurSS, hcurRS]
        congr 1; funext t'; exact hg.vR_map_of_ne_some_none P (by simp [hvR]) rs₀ t'
      · simp [PrivL15.runHM, hooksFS, hext, hvS, hvR, PrivL15.realSt, hcurSS, hcurRS]
        congr 1; funext t'; exact PrivL15.ActiveInv.vR_map_some ((sR.1.g.st P).vR t') rs₀
      · simp [PrivL15.runHM, hooksFS, hext, hvS, hvR, PrivL15.realSt, hcurSS, hcurRS]
        congr 1; funext t'; exact hg.vR_map_of_ne_some_none P (by simp [hvR]) rs₀ t'
  | none =>
    have hcurSS : PrivL15.curSS sR.1.h sR.2 = sR.2.senderState := by simp [PrivL15.curSS, hext]
    have hcurRS : PrivL15.curRS sR.1.h sR.2 = sR.2.receiverState := by simp [PrivL15.curRS, hext]
    rcases hvS : (sR.1.g.st P).vS with _ | _ | ss
    · rcases hvR : (sR.1.g.st P).vR t with _ | _ | rs
      · refine ⟨sR.1.h, sR.2, ?_, hg.afterCorr_unchanged P hca, rfl⟩
        simp [PrivL15.runHM, hooksFS, hvS, hvR, PrivL15.realSt, hcurSS, hcurRS]
        congr 1; funext t'
        exact hg.vR_map_of_ne_some_none P (by simp [hvR]) sR.2.receiverState t'
      · rcases hg.afterCorr_corruptReceiver P hca hext hvR with ⟨hcr, hInv'⟩
        refine ⟨_, _, ?_, hInv', rfl⟩
        simp [PrivL15.runHM, hooksFS, liftF, FSAEAD.corruptReceiverQuery, FSAEAD.oracleImpl,
          FSAEAD.corruptReceiverImpl, hext, hvS, hvR, hcr, PrivL15.realSt, hcurSS, hcurRS,
          PrivL15.outerFull]
        congr 1; funext t'
        exact PrivL15.ActiveInv.vR_map_some ((sR.1.g.st P).vR t') sR.2.receiverState
      · refine ⟨sR.1.h, sR.2, ?_, hg.afterCorr_unchanged P hca, rfl⟩
        simp [PrivL15.runHM, hooksFS, hvS, hvR, PrivL15.realSt, hcurSS, hcurRS]
        congr 1; funext t'
        exact hg.vR_map_of_ne_some_none P (by simp [hvR]) sR.2.receiverState t'
    · rcases hg.afterCorr_corruptSender P hca hext hvS with ⟨hvR, hended, hInv'⟩
      refine ⟨_, _, ?_, hInv', rfl⟩
      simp [PrivL15.runHM, hooksFS, liftF, FSAEAD.corruptSenderQuery, FSAEAD.oracleImpl,
        FSAEAD.corruptSenderImpl, FSAEAD.corruptSender, hext, hvS, hvR, hended,
        PrivL15.realSt, hcurSS, hcurRS, PrivL15.outerFull]
      congr 1; funext t'
      exact hg.vR_map_of_ne_some_none P (by simp [hvR]) sR.2.receiverState t'
    · rcases hvR : (sR.1.g.st P).vR t with _ | _ | rs
      · refine ⟨sR.1.h, sR.2, ?_, hg.afterCorr_unchanged P hca, rfl⟩
        simp [PrivL15.runHM, hooksFS, hvS, hvR, PrivL15.realSt, hcurSS, hcurRS]
        congr 1; funext t'
        exact hg.vR_map_of_ne_some_none P (by simp [hvR]) sR.2.receiverState t'
      · rcases hg.afterCorr_corruptReceiver P hca hext hvR with ⟨hcr, hInv'⟩
        refine ⟨_, _, ?_, hInv', rfl⟩
        simp [PrivL15.runHM, hooksFS, liftF, FSAEAD.corruptReceiverQuery, FSAEAD.oracleImpl,
          FSAEAD.corruptReceiverImpl, hext, hvS, hvR, hcr, PrivL15.realSt, hcurSS, hcurRS,
          PrivL15.outerFull]
        congr 1; funext t'
        exact PrivL15.ActiveInv.vR_map_some ((sR.1.g.st P).vR t') sR.2.receiverState
      · refine ⟨sR.1.h, sR.2, ?_, hg.afterCorr_unchanged P hca, rfl⟩
        simp [PrivL15.runHM, hooksFS, hvS, hvR, PrivL15.realSt, hcurSS, hcurRS]
        congr 1; funext t'
        exact hg.vR_map_of_ne_some_none P (by simp [hvR]) sR.2.receiverState t'

omit [SampleableType KR] [SampleableType KC] in
private theorem closeBy_corrEU (t : ℕ) (b : Bool)
    (P : Party)
    (k : (PrivL15.AdvSpec Γ T Sig SS RS M CCoins E).Range (Sum.inr (Sum.inr P)) →
      OracleComp (PrivL15.AdvSpec Γ T Sig SS RS M CCoins E) Bool)
    (sL : StateLU Γ T Sig SS RS M E I K)
    (sL_g : PrivL15.StateL Γ T Sig SS RS M E K I)
    (sR : PrivL15.StateR Γ T Sig K I SS RS M E)
    (hg : PrivL15.ActiveInv fs Δcka qep none t b sL_g sR)
    (hs : SyncU15 prng t b sL sL_g sR)
    (ih : ∀ u sL₁ sR₁, Inv15U prng fs Δcka qep t b sL₁ sR₁ →
      CloseByEngU cka prng fs Δcka qep t b (k u) sL₁ sR₁) :
    CloseByEngU cka prng fs Δcka qep t b (liftM (OracleSpec.query (Sum.inr (Sum.inr P))) >>= k)
      sL sR := by
  have hca_eq := hs.corrAllowed_eq hg P
  cases hca : sR.1.g.corrAllowed P
  · refine closeBy_of_det_stepU cka prng fs Δcka qep t b (Sum.inr (Sum.inr P)) k
      sL sL sR sR none none ?_ ?_ ih (Or.inr ⟨rfl, Or.inr ⟨sL_g, hg, hs⟩⟩)
    · simp [PrivL15.runEM, Engine.implE, Engine.corrE, hs.abortL, hs.winL, hca_eq, hca]
    · simp [PrivL15.runEM, Engine.implE, Engine.corrE, hg.abortR, hg.winR, hca]
  · have hleaks_ac : (sL.1.g.afterCorr P).leaks = (sR.1.g.afterCorr P).leaks := by
      simp [GameState.afterCorr, GameState.leak, hs.epoch_eq, hs.tL_eq, hs.leaks_eq]
    have hld_eq := leakDoom_eq_of_fields hs.epoch_eq hleaks_ac (polUni12 Δcka t)
    have hcd_eq := corrDoom_eq_of_epoch hs.epoch_eq (polUni12 Δcka t) P
    cases hdoom :
      ((polUni12 Δcka t).leakDoom sR.1.g (sR.1.g.afterCorr P) ||
        (polUni12 Δcka t).corrDoom sR.1.g P)
    · have hrevL := reveal_ckau_eq cka prng fs Δcka qep t hg hs P
      rcases reveal_fs_with_cache cka prng fs Δcka qep t hg P hca with
        ⟨hR', osR', hrevR, hg', hcache⟩
      have hs' := hs.afterCorr hg P hg' hcache
      simp only [PrivL15.runHM] at hrevR
      refine closeBy_of_det_stepU cka prng fs Δcka qep t b (Sum.inr (Sum.inr P)) k
        sL ({ sL.1 with g := sL.1.g.afterCorr P }, sL.2)
        sR ({ sR.1 with g := sR.1.g.afterCorr P, h := hR' }, osR')
        (some (PrivL15.realSt sR P)) (some (PrivL15.realSt sR P))
        ?_ ?_ ih (Or.inr ⟨rfl, Or.inr ⟨_, hg', hs'⟩⟩)
      · simp [PrivL15.runEM, Engine.implE, Engine.corrE, PrivL15.StateT_run_liftH,
          hs.abortL, hs.winL, hca_eq, hca, hld_eq, hcd_eq, hdoom, hrevL, -Bool.or_eq_true]
      · simp [PrivL15.runEM, Engine.implE, Engine.corrE, PrivL15.StateT_run_liftH,
          hg.abortR, hg.winR, hca, hdoom, hrevR, -Bool.or_eq_true]
    · refine closeBy_of_det_stepU cka prng fs Δcka qep t b (Sum.inr (Sum.inr P)) k
        sL ({ sL.1 with abort := true }, sL.2)
        sR ({ sR.1 with abort := true }, sR.2)
        none none ?_ ?_ ih (Or.inr ⟨rfl, Or.inl ⟨rfl, rfl, hg.winFS, hg.bFS⟩⟩)
      · simp [PrivL15.runEM, Engine.implE, Engine.corrE, Engine.abortE,
          hs.abortL, hs.winL, hca_eq, hca, hld_eq, hcd_eq, hdoom, -Bool.or_eq_true]
      · simp [PrivL15.runEM, Engine.implE, Engine.corrE, Engine.abortE,
          hg.abortR, hg.winR, hca, hdoom, -Bool.or_eq_true]

/-! ### Section 3: `deliverE` and `injectE` -/

private structure SteppedVPU
    (sL : StateLU Γ T Sig SS RS M E I K)
    (sL_g : PrivL15.StateL Γ T Sig SS RS M E K I)
    (sR : PrivL15.StateR Γ T Sig K I SS RS M E)
    (P : Party) (t' : ℕ)
    (s₁LU : Engine.VP (Option Γ) T Sig SS RS)
    (s₁L : Engine.VP Γ T (Option Sig) SS RS)
    (s₁R : Engine.VP Γ T Sig (Option SS) (Option RS)) : Prop where
  idL : s₁LU.id = P
  tcurL : s₁LU.tcur = max (sR.1.g.epoch P) t'
  γ_eq : s₁LU.γ = some s₁R.γ
  Tcur_eq : s₁LU.curCkaMsg = s₁R.curCkaMsg
  root_eq : s₁LU.root = s₁R.root
  vS_eq : s₁LU.vS = s₁L.vS
  vR_eq : s₁LU.vR = s₁L.vR
  step_cases : (t' ≤ sR.1.g.epoch P ∧ s₁R.root = (sR.1.g.st P).root) ∨
    (t' = sR.1.g.epoch P + 1 ∧ s₁R.root = (sR.1.g.st P.other).root)

omit [DecidableEq M] [Inhabited E] [SampleableType KR] [SampleableType KC] in
private theorem prepRecvU (t : ℕ) {b : Bool}
    {sL : StateLU Γ T Sig SS RS M E I K}
    {sL_g : PrivL15.StateL Γ T Sig SS RS M E K I}
    {sR : PrivL15.StateR Γ T Sig K I SS RS M E}
    (hg : PrivL15.ActiveInv fs Δcka qep none t b sL_g sR)
    (hs : SyncU15 prng t b sL sL_g sR) (P : Party) (c : Header T × E)
    (recL recR : Option (Record M (Header T × E))) :
    ((Engine.vRecv (hooksCKAUEager cka prng fs Δcka ⟨false, none, t⟩)
        sL.1.g P (sL.1.g.st P) c recL).run sL.1.h =
        pure (some none, sL.1.h) ∧
     (Engine.vRecv (hooksFS cka prng fs Δcka ⟨false, none, t⟩ 0)
        sR.1.g P (sR.1.g.st P) c recR).run sR.1.h =
        pure (some none, sR.1.h)) ∨
    ∃ s₁LU s₁L s₁R rsv,
      PrivL15.SteppedVP fs none t sL_g sR P c.1.1 s₁L s₁R ∧
      SteppedVPU sL sL_g sR P c.1.1 s₁LU s₁L s₁R ∧
      s₁R.vR c.1.1 = some rsv ∧
      (Engine.vRecv (hooksCKAUEager cka prng fs Δcka ⟨false, none, t⟩)
        sL.1.g P (sL.1.g.st P) c recL).run sL.1.h =
        pure (match fs.receive (rsv.getD (PrivL15.curRS sR.1.h sR.2)) c.1 c.2 with
          | none => some none
          | some (v', i, m) =>
            some (some ({ s₁LU with vR := Function.update s₁LU.vR c.1.1 (some v') },
              c.1.1, i, m)), sL.1.h) ∧
      (Engine.vRecv (hooksFS cka prng fs Δcka ⟨false, none, t⟩ 0)
        sR.1.g P (sR.1.g.st P) c recR).run sR.1.h =
        (((hooksFS cka prng fs Δcka ⟨false, none, t⟩ 0).fsRecv
            sR.1.g P c.1.1 rsv c.1 c.2 recR).run sR.1.h >>= fun p =>
          pure (match p.1 with
            | none => none
            | some none => some none
            | some (some (v', i, m)) =>
              some (some ({ s₁R with vR := Function.update s₁R.vR c.1.1 (some v') },
                c.1.1, i, m)), p.2)) := by
  cases hcond : (P.sendsIn c.1.1 || decide (sR.1.g.epoch P + 1 < c.1.1))
  · simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt] at hcond
    have hPr : P = Party.receiverOf c.1.1 :=
      (PrivL15.Party.sendsIn_false_iff_receiverOf P c.1.1).mp hcond.1
    rcases eq_or_ne c.1.1 (sR.1.g.epoch P + 1) with ht_succ | ht_ne
    · cases hc2 : c.1.2 with
      | none =>
        left
        refine ⟨?_, ?_⟩
        · simp [Engine.vRecv, hs.idL P, hs.tcurL P, hcond.1, ← ht_succ, hc2]
        · simp [Engine.vRecv, hg.idR P, hg.tcurR P, hcond.1, ← ht_succ, hc2]
      | some Tn =>
        cases hcache : sR.1.h.cache c.1.1 with
        | none =>
          have hcacheLU := hs.cacheL_none c.1.1 hcache
          left
          refine ⟨?_, ?_⟩
          · simp [Engine.vRecv, hooksCKAUEager, hooksCKAU, liftCKAComp,
              hs.idL P, hs.tcurL P, hcond.1, ← ht_succ, hc2, hcacheLU]
          · simp [Engine.vRecv, hooksFS, hg.idR P, hg.tcurR P, hcond.1, ← ht_succ, hc2, hcache]
        | some val =>
          rcases val with ⟨Tc, σc, kc, ext⟩
          have hlt_rec : sR.1.g.epoch (Party.receiverOf c.1.1) < c.1.1 := by
            rw [← hPr]; omega
          rcases hs.cache_pending c.1.1 Tc σc kc ext hlt_rec hcache with
            ⟨hsender_root, Ik, hcacheLU, hp1, hp2⟩
          rw [← hPr] at hp1 hp2
          rcases hg.cache_lookup hPr ht_succ hcache with
            ⟨σL, k₀, hcacheLg, hσL, hrs₀, hext_eq⟩
          rcases eq_or_ne Tc Tn with rfl | hne_T
          · have hPother_root : σc = (sR.1.g.st P.other).root := by
              rw [← hsender_root, hPr, PrivL15.Party.other_receiverOf]
            have hmax : max (sR.1.g.epoch P) c.1.1 = c.1.1 := Nat.max_eq_right (by omega)
            let s₁LU : Engine.VP (Option Γ) T Sig SS RS :=
              { sL.1.g.st P with
                  tcur := c.1.1
                  γ := some (cka.receive (sR.1.g.st P).γ Tc).1
                  root := σc
                  vR := Function.update (sL.1.g.st P).vR c.1.1 (some (fs.initReceiver k₀)) }
            right
            refine ⟨s₁LU, _, _, if ext then none else some (fs.initReceiver kc),
              hg.steppedVP_advance cka hPr ht_succ hcache hσL hrs₀ hext_eq,
              { idL := hs.idL P
                tcurL := by simp [s₁LU, hmax]
                γ_eq := rfl
                Tcur_eq := hs.Tcur_eq P
                root_eq := rfl
                vS_eq := hs.vS_eq P
                vR_eq := by simp [s₁LU, hs.vR_eq P]
                step_cases := Or.inr ⟨ht_succ, hPother_root⟩ },
              by simp, ?_, ?_⟩
            · have hstartLU :
                  ((hooksCKAUEager cka prng fs Δcka ⟨false, none, t⟩).startRecv
                    sL.1.g P c.1.1 (sL.1.g.st P).γ (sL.1.g.st P).root Tc).run sL.1.h =
                  pure (some (some (some (cka.receive (sR.1.g.st P).γ Tc).1,
                    σc, fs.initReceiver k₀)), sL.1.h) := by
                rcases eq_or_ne c.1.1 t with hct | hct
                · subst hct
                  have hkOpt := hs.kOpt_eq Tc σL k₀ hcacheLg
                  simp [hooksCKAUEager, hooksCKAU, liftCKAComp,
                    StateT.run_mk, StateT.run_bind, StateT.run_get, pure_bind,
                    hcacheLU, hs.root_eq P, hp1, hs.γ_eq P, hkOpt]
                · have hk₀_eq : k₀ = kc := by
                    have hco := hg.cache_other c.1.1 hct
                    rw [hcache, hcacheLg] at hco
                    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hco
                    exact hco.2.2
                  simp [hooksCKAUEager, hooksCKAU, liftCKAComp,
                    StateT.run_mk, StateT.run_bind, StateT.run_get, pure_bind,
                    hcacheLU, hs.root_eq P, hp1, hs.γ_eq P, hct, hp2 hct, hk₀_eq]
              cases hrecv : fs.receive (fs.initReceiver k₀) c.1 c.2 <;>
              · simp only [Engine.vRecv, hs.idL P, hs.tcurL P, hcond.1, ← ht_succ, hc2,
                  Nat.lt_irrefl, decide_false, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
                  StateT.run_bind, hstartLU, pure_bind, Function.update_self, hrs₀]
                simp [hooksCKAUEager, hooksCKAU, liftCKAComp, s₁LU, hrecv, hs.idL P]
            · have hstartR :
                  ((hooksFS cka prng fs Δcka ⟨false, none, t⟩ 0).startRecv sR.1.g P
                    c.1.1 (sR.1.g.st P).γ (sR.1.g.st P).root Tc).run sR.1.h =
                  pure (some (some ((cka.receive (sR.1.g.st P).γ Tc).1, σc,
                    if ext then none else some (fs.initReceiver kc))), sR.1.h) := by
                simp [hooksFS, hcache]
              simp only [Engine.vRecv, hg.idR P, hg.tcurR P, hcond.1, ← ht_succ, hc2,
                Nat.lt_irrefl, decide_false, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
                StateT.run_bind, hstartR, pure_bind, Function.update_self]
              congr 1; funext ⟨res, h'⟩
              rcases res with _ | _ | ⟨v', i, m⟩ <;> simp
          · left
            refine ⟨?_, ?_⟩
            · simp [Engine.vRecv, hooksCKAUEager, hooksCKAU, liftCKAComp,
                hs.idL P, hs.tcurL P, hcond.1, ← ht_succ, hc2, hcacheLU, hne_T]
            · simp [Engine.vRecv, hooksFS, hg.idR P, hg.tcurR P, hcond.1, ← ht_succ,
                hc2, hcache, hne_T]
    · have hle : c.1.1 ≤ sR.1.g.epoch P := by omega
      have hmax : max (sR.1.g.epoch P) c.1.1 = sR.1.g.epoch P := Nat.max_eq_left hle
      cases hvR : (sR.1.g.st P).vR c.1.1 with
      | none =>
        have hvRLU : (sL.1.g.st P).vR c.1.1 = none := by
          rw [hs.vR_eq P, hg.vR_eq P c.1.1, hvR]; rfl
        left
        refine ⟨?_, ?_⟩
        · simp [Engine.vRecv, hs.idL P, hs.tcurL P, hcond.1,
            not_lt.mpr hcond.2, ht_ne, hvRLU]
        · simp [Engine.vRecv, hg.idR P, hg.tcurR P, hcond.1,
            not_lt.mpr hcond.2, ht_ne, hvR]
      | some rsv =>
        have hvRLU : (sL.1.g.st P).vR c.1.1 = some (rsv.getD (PrivL15.curRS sR.1.h sR.2)) := by
          rw [hs.vR_eq P, hg.vR_eq P c.1.1, hvR]; rfl
        right
        refine ⟨sL.1.g.st P, sL_g.1.g.st P, sR.1.g.st P, rsv,
          hg.steppedVP_stay hPr hle,
          { idL := hs.idL P
            tcurL := by rw [hmax, hs.tcurL P]
            γ_eq := hs.γ_eq P
            Tcur_eq := hs.Tcur_eq P
            root_eq := hs.root_eq P
            vS_eq := hs.vS_eq P
            vR_eq := hs.vR_eq P
            step_cases := Or.inl ⟨hle, rfl⟩ },
          hvR, ?_, ?_⟩
        · cases hrecv : fs.receive (rsv.getD (PrivL15.curRS sR.1.h sR.2)) c.1 c.2 <;>
          simp [Engine.vRecv, hooksCKAUEager, hooksCKAU, liftCKAComp,
            hs.idL P, hs.tcurL P, hcond.1, not_lt.mpr hcond.2, ht_ne, hvRLU, hrecv]
        · simp only [Engine.vRecv, hg.idR P, hg.tcurR P, hcond.1, not_lt.mpr hcond.2,
            decide_false, Bool.or_false, Bool.false_eq_true, ht_ne, ↓reduceIte,
            StateT.run_bind, pure_bind, hvR]
          congr 1; funext ⟨res, h'⟩
          rcases res with _ | _ | ⟨v', i, m⟩ <;> simp
  · left
    refine ⟨?_, ?_⟩
    · simp [Engine.vRecv, hs.idL P, hs.tcurL P, hcond, -Bool.or_eq_true]
    · simp [Engine.vRecv, hg.idR P, hg.tcurR P, hcond, -Bool.or_eq_true]

omit [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType I] in
private theorem StateT_run_commitE_ckau {mo : Mode}
    {s : Engine.Ctx (Option Γ) T Sig SS RS M E} {P : Party}
    {old new : Engine.VP (Option Γ) T Sig SS RS} {pos : Pos}
    {es : Engine.EState (Engine.VP (Option Γ) T Sig SS RS) M (Header T × E) (CKAUState T I K)}
    (hγ : old.γ.isNone = false) :
    (Engine.commitE (hooksCKAUEager cka prng fs Δcka mo) s P old new pos).run es =
      pure (some (s.accept P new pos), es) := by
  have hγ_ne : old.γ ≠ none := by intro h; simp [h] at hγ
  simp [Engine.commitE, hooksCKAUEager, hooksCKAU, liftCKAComp, PrivL15.StateT_run_liftH,
    hγ_ne, PrivL15.accept_update_st_self]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType I] [SampleableType K] in
private theorem SteppedVPU.accept_sync {fs : FSAEADScheme K SS RS (Header T) M E}
    {Δcka qep t : ℕ} {b : Bool} {prng : PRFPRNG KR Sig I K}
    {sL : StateLU Γ T Sig SS RS M E I K}
    {sL_g : PrivL15.StateL Γ T Sig SS RS M E K I}
    {sR : PrivL15.StateR Γ T Sig K I SS RS M E}
    {P : Party} {t' : ℕ}
    {s₁LU : Engine.VP (Option Γ) T Sig SS RS}
    {s₁L : Engine.VP Γ T (Option Sig) SS RS}
    {s₁R : Engine.VP Γ T Sig (Option SS) (Option RS)}
    (hg : PrivL15.ActiveInv fs Δcka qep none t b sL_g sR)
    (hs : SyncU15 prng t b sL sL_g sR)
    (hs_vp : PrivL15.SteppedVP fs none t sL_g sR P t' s₁L s₁R)
    (hu_vp : SteppedVPU sL sL_g sR P t' s₁LU s₁L s₁R)
    (rs' : RS) (vR_R' : Option RS) (pos : Pos)
    (hR' : FSState T Sig K I SS RS E) (osR' : FSAEAD.State SS RS (Header T) M E)
    (hpos_ep : pos.epoch = t')
    (hcache : hR'.cache = sR.1.h.cache) :
    SyncU15 prng t b
      ({ sL.1 with g := sL.1.g.accept P { s₁LU with vR := Function.update s₁LU.vR t' (some rs') } pos },
       sL.2)
      ({ sL_g.1 with g := sL_g.1.g.accept P { s₁L with vR := Function.update s₁L.vR t' (some rs') } pos },
       sL_g.2)
      ({ sR.1 with g := sR.1.g.accept P { s₁R with vR := Function.update s₁R.vR t' (some vR_R') } pos,
                   h := hR' }, osR') := by
  have hep_eq : (sL.1.g.accept P { s₁LU with vR := Function.update s₁LU.vR t' (some rs') } pos).epoch =
      (sR.1.g.accept P { s₁R with vR := Function.update s₁R.vR t' (some vR_R') } pos).epoch := by
    simp [GameState.accept, GameState.delete, hu_vp.tcurL, hs_vp.tcurR, hs.epoch_eq]
  refine
    { abortL := hs.abortL
      winL := hs.winL
      bL := hs.bL
      epoch_eq := hep_eq
      idx_eq := hs.idx_eq
      tL_eq := hs.tL_eq
      chall_eq := by simp [GameState.accept, GameState.delete, hs.chall_eq]
      comp_eq := by simp [GameState.accept, GameState.delete, hs.comp_eq]
      maxAcc_eq := by simp [GameState.accept, GameState.delete, hs.maxAcc_eq]
      leaks_eq := hs.leaks_eq
      corrs_eq := hs.corrs_eq
      trans_eq := by simp [GameState.accept, GameState.delete, hs.trans_eq]
      idL := fun Q => by
        rcases eq_or_ne Q P with rfl | hne
        · simp [GameState.accept, GameState.delete, hu_vp.idL]
        · simp [GameState.accept, GameState.delete, hne, hs.idL]
      tcurL := fun Q => by
        rcases eq_or_ne Q P with rfl | hne
        · simp [GameState.accept, GameState.delete, hu_vp.tcurL, hpos_ep]
        · simp [GameState.accept, GameState.delete, hne, hs.tcurL]
      γ_eq := fun Q => by
        rcases eq_or_ne Q P with rfl | hne
        · simp [GameState.accept, GameState.delete, hu_vp.γ_eq]
        · simp [GameState.accept, GameState.delete, hne, hs.γ_eq]
      Tcur_eq := fun Q => by
        rcases eq_or_ne Q P with rfl | hne
        · simp [GameState.accept, GameState.delete, hu_vp.Tcur_eq]
        · simp [GameState.accept, GameState.delete, hne, hs.Tcur_eq]
      root_eq := fun Q => by
        rcases eq_or_ne Q P with rfl | hne
        · simp [GameState.accept, GameState.delete, hu_vp.root_eq]
        · simp [GameState.accept, GameState.delete, hne, hs.root_eq]
      vS_eq := fun Q => by
        rcases eq_or_ne Q P with rfl | hne
        · simp [GameState.accept, GameState.delete, hu_vp.vS_eq]
        · simp [GameState.accept, GameState.delete, hne, hs.vS_eq]
      vR_eq := fun Q => by
        rcases eq_or_ne Q P with rfl | hne
        · simp [GameState.accept, GameState.delete, hu_vp.vR_eq]
        · simp [GameState.accept, GameState.delete, hne, hs.vR_eq]
      same_ep_root := ?_
      cacheL_none := fun t'' hc => hs.cacheL_none t'' (hcache ▸ hc)
      cache_pending := ?_
      kOpt_eq := hs.kOpt_eq
      slot_eq := hs.slot_eq }
  · rcases hu_vp.step_cases with ⟨hle, hroot_stay⟩ | ⟨_, hroot_adv⟩
    · have hmax : max (sR.1.g.epoch P) t' = sR.1.g.epoch P := Nat.max_eq_left hle
      intro hepAB
      have hepAB₀ : sR.1.g.epoch .A = sR.1.g.epoch .B := by
        cases P <;> simp [GameState.accept, GameState.delete, hs_vp.tcurR, hmax, hpos_ep] at hepAB <;>
          omega
      cases P <;>
        simp [GameState.accept, GameState.delete, hroot_stay, hs.same_ep_root hepAB₀]
    · intro _
      cases P <;> simp [GameState.accept, GameState.delete, Party.other, hroot_adv]
  · rcases hu_vp.step_cases with ⟨hle, hroot_stay⟩ | ⟨ht_succ, _⟩
    · have hmax : max (sR.1.g.epoch P) t' = sR.1.g.epoch P := Nat.max_eq_left hle
      intro t'' Tc σc kc ext hlt hc
      have hep_same : ∀ Q,
          (sR.1.g.accept P { s₁R with vR := Function.update s₁R.vR t' (some vR_R') } pos).epoch Q =
            sR.1.g.epoch Q := by
        intro Q
        rcases eq_or_ne Q P with rfl | hne
        · simp [GameState.accept, GameState.delete, hpos_ep, hmax]
        · simp [GameState.accept, GameState.delete, hne]
      have hroot_same : ∀ Q,
          ((sR.1.g.accept P { s₁R with vR := Function.update s₁R.vR t' (some vR_R') } pos).st Q).root =
            (sR.1.g.st Q).root := by
        intro Q
        rcases eq_or_ne Q P with rfl | hne
        · simp [GameState.accept, GameState.delete, hroot_stay]
        · simp [GameState.accept, GameState.delete, hne]
      rw [hep_same] at hlt
      simp only [hroot_same]
      exact hs.cache_pending t'' Tc σc kc ext hlt (hcache ▸ hc)
    · intro t'' Tc σc kc ext hlt hc
      exfalso
      have hc0 : sR.1.h.cache t'' ≠ none := by rw [← hcache, hc]; simp
      have hle_max := (hg.cache_some_le_maxEp t'' hc0).2
      have hmax_t : max (sR.1.g.epoch P) t' = t' := Nat.max_eq_right (by omega)
      set epM := max (sR.1.g.epoch .A) (sR.1.g.epoch .B)
      have hepM_eq : epM = t' := by
        have hSe := hg.sender_epoch
        have hRe := hg.receiver_epoch
        have hle_vp := hs_vp.t'_le_maxEp
        change t' ≤ epM at hle_vp
        change sR.1.g.epoch (Party.senderOf epM) = epM at hSe
        change sR.1.g.epoch (Party.receiverOf epM) = epM ∨
          (1 ≤ epM ∧ sR.1.g.epoch (Party.receiverOf epM) + 1 = epM) at hRe
        rcases PrivL15.Party.eq_senderOf_or_receiverOf P epM with hPs | hPr
        · rw [hPs, hSe] at ht_succ; omega
        · rw [hPr] at ht_succ; omega
      have hPother_ep : sR.1.g.epoch P.other = t' := by
        have hchoice : epM = sR.1.g.epoch .A ∨ epM = sR.1.g.epoch .B := max_choice _ _
        cases P <;> simp only [Party.other] <;> omega
      have hep_new : ∀ Q,
          (sR.1.g.accept P { s₁R with vR := Function.update s₁R.vR t' (some vR_R') } pos).epoch Q = t' := by
        intro Q
        rcases eq_or_ne Q P with rfl | hne
        · simp [GameState.accept, GameState.delete, hmax_t, hpos_ep]
        · have hQP : Q = P.other := by cases Q <;> cases P <;> first | exact absurd rfl hne | rfl
          subst hQP
          simp [GameState.accept, GameState.delete, hne, hPother_ep]
      change (sR.1.g.accept P _ pos).epoch (Party.receiverOf t'') < t'' at hlt
      rw [hep_new] at hlt
      change t'' ≤ epM at hle_max
      omega

omit [SampleableType KR] [SampleableType KC] in
private theorem closeBy_deliverEU (t : ℕ) (b : Bool)
    (P : Party) (c : Header T × E)
    (k : (PrivL15.AdvSpec Γ T Sig SS RS M CCoins E).Range
        (Sum.inr (Sum.inl (Sum.inl (Sum.inr (P, c))))) →
      OracleComp (PrivL15.AdvSpec Γ T Sig SS RS M CCoins E) Bool)
    (sL : StateLU Γ T Sig SS RS M E I K)
    (sL_g : PrivL15.StateL Γ T Sig SS RS M E K I)
    (sR : PrivL15.StateR Γ T Sig K I SS RS M E)
    (hg : PrivL15.ActiveInv fs Δcka qep none t b sL_g sR)
    (hs : SyncU15 prng t b sL sL_g sR)
    (ih : ∀ u sL₁ sR₁, Inv15U prng fs Δcka qep t b sL₁ sR₁ →
      CloseByEngU cka prng fs Δcka qep t b (k u) sL₁ sR₁) :
    CloseByEngU cka prng fs Δcka qep t b
      (liftM (OracleSpec.query (Sum.inr (Sum.inl (Sum.inl (Sum.inr (P, c)))))) >>= k)
      sL sR := by
  have hesL := PrivL15.EState_mk_false_eq hs.abortL
  have hesR := PrivL15.EState_mk_false_eq hg.abortR
  have hγ_none : (sL.1.g.st P).γ.isNone = false := by simp [hs.γ_eq P]
  have hitr_u := hs.inTransit_eq P.other c
  have hmap := hg.inTransit_map_eq P.other c
  cases hitr : sR.1.g.inTransit P.other c with
  | none =>
    rw [hitr, Option.map_none, Option.map_eq_none_iff] at hmap
    refine closeBy_of_det_stepU cka prng fs Δcka qep t b
      (Sum.inr (Sum.inl (Sum.inl (Sum.inr (P, c))))) k
      sL sL sR sR none none ?_ ?_ ih (Or.inr ⟨rfl, Or.inr ⟨sL_g, hg, hs⟩⟩)
    · simp [PrivL15.runEM, Engine.implE, Engine.deliverE, hs.abortL, hs.winL, hitr_u, hmap]
    · simp [PrivL15.runEM, Engine.implE, Engine.deliverE, hg.abortR, hg.winR, hitr]
  | some rR =>
    rw [hitr, Option.map_some, Option.map_eq_some_iff] at hmap
    rcases hmap with ⟨rL, hitrL, hr_eq⟩
    have hrpos_eq : rL.pos = rR.pos := by injection hr_eq
    have hr_mem : rR ∈ sR.1.g.trans := List.mem_of_find?_eq_some hitr
    have hr_pred := List.find?_some hitr
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hr_pred
    have hr_wf := hg.trans_wf rR hr_mem
    have hr_ep : rR.pos.epoch = c.1.1 := by rw [hr_wf.1, hr_pred.2]
    have hr_pos : rR.pos = ⟨P.other, c.1.1, rR.pos.idx⟩ := by
      rcases rR with ⟨⟨s, e, i⟩, msg, ct⟩
      exact congrArg₂ (Pos.mk · · i) hr_pred.1 hr_ep
    rcases prepRecvU cka prng fs Δcka qep t hg hs P c (some rL) (some rR) with
      ⟨hvL, hvR⟩ | ⟨s₁LU, s₁L, s₁R, rsv, hs_vp, hu_vp, hvR_R, hvL, hvR⟩
    · refine closeBy_of_det_stepU cka prng fs Δcka qep t b
        (Sum.inr (Sum.inl (Sum.inl (Sum.inr (P, c))))) k
        sL sL sR sR (some .rejected) (some .rejected) ?_ ?_ ih
        (Or.inr ⟨rfl, Or.inr ⟨sL_g, hg, hs⟩⟩)
      · simp [PrivL15.runEM, Engine.implE, Engine.deliverE, Config.priv,
          PrivL15.StateT_run_liftH, hesL, hs.abortL, hs.winL, hitr_u, hitrL, hvL]
      · simp [PrivL15.runEM, Engine.implE, Engine.deliverE, Config.priv,
          PrivL15.StateT_run_liftH, hesR, hg.abortR, hg.winR, hitr, hvR]
    · rcases eq_or_ne t c.1.1 with rfl | hne_t
      · have hvR_t := hs_vp.vR_t_receiver hs_vp.P_eq
        simp only [Nat.le_max_right, ↓reduceIte, hvR_R] at hvR_t
        injection hvR_t with hrsv
        subst hrsv
        cases hext : sR.1.h.ext with
        | some val =>
          rcases val with ⟨ss_val, rs_val⟩
          have hcurRS : (none : Option RS).getD (PrivL15.curRS sR.1.h sR.2) = rs_val := by
            simp [PrivL15.curRS, hext]
          cases hrecv : fs.receive rs_val c.1 c.2 with
          | none =>
            refine closeBy_of_det_stepU cka prng fs Δcka qep c.1.1 b
              (Sum.inr (Sum.inl (Sum.inl (Sum.inr (P, c))))) k
              sL sL sR sR (some .rejected) (some .rejected) ?_ ?_ ih
              (Or.inr ⟨rfl, Or.inr ⟨sL_g, hg, hs⟩⟩)
            · simp [PrivL15.runEM, Engine.implE, Engine.deliverE, Config.priv,
                PrivL15.StateT_run_liftH, hesL, hs.abortL, hs.winL, hitr_u, hitrL,
                hvL, hcurRS, hrecv]
            · simp [PrivL15.runEM, Engine.implE, Engine.deliverE, Config.priv,
                PrivL15.StateT_run_liftH, hesR, hg.abortR, hg.winR, hitr, hvR,
                PrivL15.hooksFS_fsRecv_ext_some _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hext, hrecv]
          | some val =>
            rcases val with ⟨rs', i', m'⟩
            have hg' := hs_vp.accept_t_ext_some hg ss_val rs_val rs' rR.pos.idx hext
            dsimp only at hg'
            rw [← hr_pos] at hg'
            have hs' := hu_vp.accept_sync hg hs hs_vp rs' none rR.pos
              { sR.1.h with ext := some (ss_val, rs') } sR.2 hr_ep rfl
            let stLU' := { s₁LU with vR := Function.update s₁LU.vR c.1.1 (some rs') }
            let stR' := { s₁R with vR := Function.update s₁R.vR c.1.1 (some none) }
            let hR' := { sR.1.h with ext := some (ss_val, rs') }
            refine closeBy_of_det_stepU cka prng fs Δcka qep c.1.1 b
              (Sum.inr (Sum.inl (Sum.inl (Sum.inr (P, c))))) k
              sL ({ sL.1 with g := sL.1.g.accept P stLU' rR.pos }, sL.2)
              sR ({ sR.1 with g := sR.1.g.accept P stR' rR.pos, h := hR' }, sR.2)
              (some (.accepted c.1.1 i' (if sR.1.g.chall.contains rR.pos then none else some m')))
              (some (.accepted c.1.1 i' (if sR.1.g.chall.contains rR.pos then none else some m')))
              ?_ ?_ ih (Or.inr ⟨rfl, Or.inr ⟨_, hg', hs'⟩⟩)
            · simp [PrivL15.runEM, Engine.implE, Engine.deliverE, Config.priv,
                PrivL15.StateT_run_liftH, stLU', StateT_run_commitE_ckau cka prng fs Δcka hγ_none,
                hs.abortL, hs.winL, hitr_u, hitrL, hvL, hcurRS, hrecv, hs.chall_eq, hrpos_eq]
            · simp [PrivL15.runEM, Engine.implE, Engine.deliverE, Config.priv,
                PrivL15.StateT_run_liftH, stR', hR', PrivL15.StateT_run_commitE_fs,
                hg.abortR, hg.winR, hitr, hvR,
                PrivL15.hooksFS_fsRecv_ext_some _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hext, hrecv]
        | none =>
          have hcurRS : (none : Option RS).getD (PrivL15.curRS sR.1.h sR.2) = sR.2.receiverState := by
            simp [PrivL15.curRS, hext]
          have hended : sR.2.ended = false := (hg.ext_none hext).1
          rcases hg.inTransit_deliver_t hs_vp.P_eq rfl hext hitr with
            ⟨_, hfs_find, r_fs, hr_fs, hidx_eq, hchall_eq⟩
          cases hrecv : fs.receive sR.2.receiverState c.1 c.2 with
          | none =>
            let win' := sR.2.win ||
              (!sR.2.isCompromised r_fs.idx && decide (r_fs.idx ≤ sR.2.receiverIdx + fs.maxSkip + 1))
            refine closeBy_of_det_stepU cka prng fs Δcka qep c.1.1 b
              (Sum.inr (Sum.inl (Sum.inl (Sum.inr (P, c))))) k
              sL sL sR (sR.1, { sR.2 with win := win' })
              (some .rejected) (some .rejected) ?_ ?_ ih ?_
            · simp [PrivL15.runEM, Engine.implE, Engine.deliverE, Config.priv,
                PrivL15.StateT_run_liftH, hesL, hs.abortL, hs.winL, hitr_u, hitrL,
                hvL, hcurRS, hrecv]
            · simp [PrivL15.runEM, Engine.implE, Engine.deliverE, Config.priv,
                PrivL15.StateT_run_liftH, hesR, hg.abortR, hg.winR, hitr, hvR,
                PrivL15.hooksFS_fsRecv_deliver _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hext hfs_find,
                liftF, FSAEAD.deliverQuery, FSAEAD.oracleImpl, FSAEAD.deliverImpl,
                FSAEAD.deliver, PrivL15.outerFull, hended, hr_fs, hrecv, win']
            · cases hwin' : win'
              · right
                have hos : { sR.2 with win := false } = sR.2 := by
                  have hw := hg.winFS
                  revert hw
                  cases sR.2
                  rintro rfl
                  rfl
                rw [hos]
                exact ⟨rfl, Or.inr ⟨sL_g, hg, hs⟩⟩
              · exact Or.inl rfl
          | some val =>
            rcases val with ⟨rs', i', m'⟩
            let win' := sR.2.win ||
              ((!sR.2.isCompromised r_fs.idx &&
                decide (r_fs.idx ≤ sR.2.receiverIdx + fs.maxSkip + 1)) &&
                (i' != r_fs.idx || m' != r_fs.msg))
            let stLU' := { s₁LU with vR := Function.update s₁LU.vR c.1.1 (some rs') }
            let stR' := { s₁R with vR := Function.update s₁R.vR c.1.1 (some none) }
            let hR' := { sR.1.h with fsTrans := sR.1.h.fsTrans.filter (·.1 != rR.pos.idx) }
            let osR' := ({ sR.2 with receiverState := rs',
                                     receiverIdx := max sR.2.receiverIdx i',
                                     win := win' }).removeFromTransit rR.pos.idx
            refine closeBy_of_det_stepU cka prng fs Δcka qep c.1.1 b
              (Sum.inr (Sum.inl (Sum.inl (Sum.inr (P, c))))) k
              sL ({ sL.1 with g := sL.1.g.accept P stLU' rR.pos }, sL.2)
              sR ({ sR.1 with g := sR.1.g.accept P stR' rR.pos, h := hR' }, osR')
              (some (.accepted c.1.1 i' (if sR.1.g.chall.contains rR.pos then none else some m')))
              (some (.accepted c.1.1 i' (if sR.1.g.chall.contains rR.pos then none else some m')))
              ?_ ?_ ih ?_
            · simp [PrivL15.runEM, Engine.implE, Engine.deliverE, Config.priv,
                PrivL15.StateT_run_liftH, stLU', StateT_run_commitE_ckau cka prng fs Δcka hγ_none,
                hs.abortL, hs.winL, hitr_u, hitrL, hvL, hcurRS, hrecv, hs.chall_eq, hrpos_eq]
            · by_cases hch : rR.pos ∈ sR.1.g.chall <;>
              simp [PrivL15.runEM, Engine.implE, Engine.deliverE, Config.priv,
                PrivL15.StateT_run_liftH, stR', hR', osR', PrivL15.StateT_run_commitE_fs,
                hg.abortR, hg.winR, hitr, hvR,
                PrivL15.hooksFS_fsRecv_deliver _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hext hfs_find,
                liftF, FSAEAD.deliverQuery, FSAEAD.oracleImpl, FSAEAD.deliverImpl,
                FSAEAD.deliver, PrivL15.outerFull, hended, hr_fs, hrecv, hidx_eq, hchall_eq,
                hch, win']
            · cases hwin' : win'
              · right
                have hg' := hs_vp.accept_t_ext_none hg rs' i' rR.pos.idx win' hwin' hext
                dsimp only at hg'
                rw [← hr_pos] at hg'
                have hs' := hu_vp.accept_sync hg hs hs_vp rs' none rR.pos hR' osR' hr_ep rfl
                exact ⟨rfl, Or.inr ⟨_, hg', hs'⟩⟩
              · left
                simp [osR', FSAEAD.State.removeFromTransit, hwin']
      · rcases Option.isSome_iff_exists.mp (hs_vp.vR_other c.1.1 rsv hne_t.symm hvR_R).1 with ⟨rs, rfl⟩
        cases hrecv : fs.receive rs c.1 c.2 with
        | none =>
          refine closeBy_of_det_stepU cka prng fs Δcka qep t b
            (Sum.inr (Sum.inl (Sum.inl (Sum.inr (P, c))))) k
            sL sL sR sR (some .rejected) (some .rejected) ?_ ?_ ih
            (Or.inr ⟨rfl, Or.inr ⟨sL_g, hg, hs⟩⟩)
          · simp [PrivL15.runEM, Engine.implE, Engine.deliverE, Config.priv,
              PrivL15.StateT_run_liftH, hesL, hs.abortL, hs.winL, hitr_u, hitrL, hvL, hrecv]
          · simp [PrivL15.runEM, Engine.implE, Engine.deliverE, Config.priv,
              PrivL15.StateT_run_liftH, hesR, hg.abortR, hg.winR, hitr, hvR,
              PrivL15.hooksFS_fsRecv_some, hrecv]
        | some val =>
          rcases val with ⟨rs', i', m'⟩
          have hg' := hs_vp.accept_other hg hne_t.symm rs' rR.pos.idx
          dsimp only at hg'
          rw [← hr_pos] at hg'
          have hs' := hu_vp.accept_sync hg hs hs_vp rs' (some rs') rR.pos sR.1.h sR.2 hr_ep rfl
          let stLU' := { s₁LU with vR := Function.update s₁LU.vR c.1.1 (some rs') }
          let stR' := { s₁R with vR := Function.update s₁R.vR c.1.1 (some (some rs')) }
          refine closeBy_of_det_stepU cka prng fs Δcka qep t b
            (Sum.inr (Sum.inl (Sum.inl (Sum.inr (P, c))))) k
            sL ({ sL.1 with g := sL.1.g.accept P stLU' rR.pos }, sL.2)
            sR ({ sR.1 with g := sR.1.g.accept P stR' rR.pos, h := sR.1.h }, sR.2)
            (some (.accepted c.1.1 i' (if sR.1.g.chall.contains rR.pos then none else some m')))
            (some (.accepted c.1.1 i' (if sR.1.g.chall.contains rR.pos then none else some m')))
            ?_ ?_ ih (Or.inr ⟨rfl, Or.inr ⟨_, hg', hs'⟩⟩)
          · simp [PrivL15.runEM, Engine.implE, Engine.deliverE, Config.priv,
              PrivL15.StateT_run_liftH, stLU', StateT_run_commitE_ckau cka prng fs Δcka hγ_none,
              hs.abortL, hs.winL, hitr_u, hitrL, hvL, hrecv, hs.chall_eq, hrpos_eq]
          · simp [PrivL15.runEM, Engine.implE, Engine.deliverE, Config.priv,
              PrivL15.StateT_run_liftH, stR', PrivL15.StateT_run_commitE_fs,
              hg.abortR, hg.winR, hitr, hvR, PrivL15.hooksFS_fsRecv_some, hrecv]

omit [SampleableType KR] [SampleableType KC] in
private theorem closeBy_injectEU (t : ℕ) (b : Bool)
    (P : Party) (c : Header T × E)
    (k : (PrivL15.AdvSpec Γ T Sig SS RS M CCoins E).Range
        (Sum.inr (Sum.inl (Sum.inr (P, c)))) →
      OracleComp (PrivL15.AdvSpec Γ T Sig SS RS M CCoins E) Bool)
    (sL : StateLU Γ T Sig SS RS M E I K)
    (sL_g : PrivL15.StateL Γ T Sig SS RS M E K I)
    (sR : PrivL15.StateR Γ T Sig K I SS RS M E)
    (hg : PrivL15.ActiveInv fs Δcka qep none t b sL_g sR)
    (hs : SyncU15 prng t b sL sL_g sR)
    (ih : ∀ u sL₁ sR₁, Inv15U prng fs Δcka qep t b sL₁ sR₁ →
      CloseByEngU cka prng fs Δcka qep t b (k u) sL₁ sR₁) :
    CloseByEngU cka prng fs Δcka qep t b
      (liftM (OracleSpec.query (Sum.inr (Sum.inl (Sum.inr (P, c))))) >>= k)
      sL sR := by
  have hesL := PrivL15.EState_mk_false_eq hs.abortL
  have hesR := PrivL15.EState_mk_false_eq hg.abortR
  have hγ_none : (sL.1.g.st P).γ.isNone = false := by simp [hs.γ_eq P]
  have hitr_eq : (sL.1.g.inTransit P.other c).isSome = (sR.1.g.inTransit P.other c).isSome := by
    rw [hs.inTransit_eq P.other c]
    exact hg.inTransit_isSome_eq P.other c
  have hsafe_eq := hs.safeInj_eq (2 + Δcka)
  cases hguard : ((sR.1.g.inTransit P.other c).isSome || !sR.1.g.safeInj (2 + Δcka))
  · simp only [Bool.or_eq_false_iff, Bool.not_eq_false'] at hguard
    rcases hguard with ⟨hitr, hsafe⟩
    rcases prepRecvU cka prng fs Δcka qep t hg hs P c none none with
      ⟨hvL, hvR⟩ | ⟨s₁LU, s₁L, s₁R, rsv, hs_vp, hu_vp, hvR_R, hvL, hvR⟩
    · refine closeBy_of_det_stepU cka prng fs Δcka qep t b
        (Sum.inr (Sum.inl (Sum.inr (P, c)))) k
        sL sL sR sR (some .rejected) (some .rejected) ?_ ?_ ih
        (Or.inr ⟨rfl, Or.inr ⟨sL_g, hg, hs⟩⟩)
      · simp [PrivL15.runEM, Engine.implE, Engine.injectE, PrivL15.StateT_run_liftH, hesL,
          hs.abortL, hs.winL, hitr_eq, hitr, hsafe_eq, hsafe, hvL]
      · simp [PrivL15.runEM, Engine.implE, Engine.injectE, PrivL15.StateT_run_liftH, hesR,
          hg.abortR, hg.winR, hitr, hsafe, hvR]
    · have hnot_gt : ¬(qep + 1 < c.1.1) := by
        have := hs_vp.t'_le_maxEp
        have := hg.maxEp_le_qep
        omega
      rcases eq_or_ne t c.1.1 with rfl | hne_t
      · have hvR_t := hs_vp.vR_t_receiver hs_vp.P_eq
        simp only [Nat.le_max_right, ↓reduceIte, hvR_R] at hvR_t
        injection hvR_t with hrsv
        subst hrsv
        cases hext : sR.1.h.ext with
        | some val =>
          rcases val with ⟨ss_val, rs_val⟩
          have hcurRS : (none : Option RS).getD (PrivL15.curRS sR.1.h sR.2) = rs_val := by
            simp [PrivL15.curRS, hext]
          cases hrecv : fs.receive rs_val c.1 c.2 with
          | none =>
            refine closeBy_of_det_stepU cka prng fs Δcka qep c.1.1 b
              (Sum.inr (Sum.inl (Sum.inr (P, c)))) k
              sL sL sR sR (some .rejected) (some .rejected) ?_ ?_ ih
              (Or.inr ⟨rfl, Or.inr ⟨sL_g, hg, hs⟩⟩)
            · simp [PrivL15.runEM, Engine.implE, Engine.injectE, PrivL15.StateT_run_liftH, hesL,
                hs.abortL, hs.winL, hitr_eq, hitr, hsafe_eq, hsafe, hvL, hcurRS, hrecv]
            · simp [PrivL15.runEM, Engine.implE, Engine.injectE, PrivL15.StateT_run_liftH, hesR,
                hg.abortR, hg.winR, hitr, hsafe, hvR,
                PrivL15.hooksFS_fsRecv_ext_some _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hext, hrecv]
          | some val =>
            rcases val with ⟨rs', i', m'⟩
            have htriv : sR.1.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ = true :=
              hg.trivial_of_ext_some P.other i' (by simp [hext])
            have htriv_eq := hs.trivial_eq hg (2 + Δcka) ⟨P.other, c.1.1, i'⟩
            have hg' := hs_vp.accept_t_ext_some hg ss_val rs_val rs' i' hext
            have hs' := hu_vp.accept_sync hg hs hs_vp rs' none ⟨P.other, c.1.1, i'⟩
              { sR.1.h with ext := some (ss_val, rs') } sR.2 rfl rfl
            let stLU' := { s₁LU with vR := Function.update s₁LU.vR c.1.1 (some rs') }
            let stR' := { s₁R with vR := Function.update s₁R.vR c.1.1 (some none) }
            let hR' := { sR.1.h with ext := some (ss_val, rs') }
            refine closeBy_of_det_stepU cka prng fs Δcka qep c.1.1 b
              (Sum.inr (Sum.inl (Sum.inr (P, c)))) k
              sL ({ sL.1 with g := sL.1.g.accept P stLU' ⟨P.other, c.1.1, i'⟩ }, sL.2)
              sR ({ sR.1 with g := sR.1.g.accept P stR' ⟨P.other, c.1.1, i'⟩, h := hR' }, sR.2)
              (some (.accepted c.1.1 i' (some m')))
              (some (.accepted c.1.1 i' (some m')))
              ?_ ?_ ih (Or.inr ⟨rfl, Or.inr ⟨_, hg', hs'⟩⟩)
            · simp [PrivL15.runEM, Engine.implE, Engine.injectE, PrivL15.StateT_run_liftH, stLU',
                StateT_run_commitE_ckau cka prng fs Δcka hγ_none,
                hs.abortL, hs.winL, hitr_eq, hitr, hsafe_eq, hsafe, hvL, hcurRS, hrecv,
                hnot_gt, htriv_eq, htriv]
            · simp [PrivL15.runEM, Engine.implE, Engine.injectE, PrivL15.StateT_run_liftH,
                stR', hR', PrivL15.StateT_run_commitE_fs,
                hg.abortR, hg.winR, hitr, hsafe, hvR,
                PrivL15.hooksFS_fsRecv_ext_some _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hext, hrecv,
                hnot_gt, htriv]
        | none =>
          have hcurRS : (none : Option RS).getD (PrivL15.curRS sR.1.h sR.2) = sR.2.receiverState := by
            simp [PrivL15.curRS, hext]
          have hended : sR.2.ended = false := (hg.ext_none hext).1
          rcases hg.inTransit_inject_t hs_vp.P_eq hext hitr with ⟨hfs_find, hin_any⟩
          cases hrecv : fs.receive sR.2.receiverState c.1 c.2 with
          | none =>
            refine closeBy_of_det_stepU cka prng fs Δcka qep c.1.1 b
              (Sum.inr (Sum.inl (Sum.inr (P, c)))) k
              sL sL sR sR (some .rejected) (some .rejected) ?_ ?_ ih
              (Or.inr ⟨rfl, Or.inr ⟨sL_g, hg, hs⟩⟩)
            · simp [PrivL15.runEM, Engine.implE, Engine.injectE, PrivL15.StateT_run_liftH, hesL,
                hs.abortL, hs.winL, hitr_eq, hitr, hsafe_eq, hsafe, hvL, hcurRS, hrecv]
            · simp [PrivL15.runEM, Engine.implE, Engine.injectE, PrivL15.StateT_run_liftH, hesR,
                hg.abortR, hg.winR, hitr, hsafe, hvR,
                PrivL15.hooksFS_fsRecv_inject _ _ _ _ _ _ _ _ _ _ _ _ _ hext hfs_find,
                liftF, FSAEAD.injectQuery, FSAEAD.oracleImpl, FSAEAD.injectImpl,
                FSAEAD.inject, PrivL15.outerFull, hended, hin_any, hrecv]
          | some val =>
            rcases val with ⟨rs', i', m'⟩
            have htriv_eq := hs.trivial_eq hg (2 + Δcka) ⟨P.other, c.1.1, i'⟩
            let stLU' := { s₁LU with vR := Function.update s₁LU.vR c.1.1 (some rs') }
            let stR' := { s₁R with vR := Function.update s₁R.vR c.1.1 (some none) }
            let hR' := { sR.1.h with fsTrans := sR.1.h.fsTrans.filter (·.1 != i') }
            let osR_win := ({ sR.2 with receiverState := rs',
                                        receiverIdx := max sR.2.receiverIdx i',
                                        win := true }).removeFromTransit i'
            let osR_nowin := ({ sR.2 with receiverState := rs',
                                          receiverIdx := max sR.2.receiverIdx i',
                                          win := false }).removeFromTransit i'
            cases hcomp_i : sR.2.isCompromised i'
            · cases htriv : sR.1.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩
              · refine closeBy_of_det_stepU cka prng fs Δcka qep c.1.1 b
                  (Sum.inr (Sum.inl (Sum.inr (P, c)))) k
                  sL sL sR ({ sR.1 with h := hR' }, osR_win)
                  (some .rejected) (some .rejected)
                  ?_ ?_ ih (Or.inl (by simp [osR_win, FSAEAD.State.removeFromTransit]))
                · simp [PrivL15.runEM, Engine.implE, Engine.injectE, Config.priv,
                    PrivL15.StateT_run_liftH, hesL,
                    hs.abortL, hs.winL, hitr_eq, hitr, hsafe_eq, hsafe, hvL, hcurRS, hrecv,
                    hnot_gt, htriv_eq, htriv]
                · simp [PrivL15.runEM, Engine.implE, Engine.injectE, Config.priv,
                    PrivL15.StateT_run_liftH, hR', osR_win,
                    hg.abortR, hg.winR, hitr, hsafe, hvR,
                    PrivL15.hooksFS_fsRecv_inject _ _ _ _ _ _ _ _ _ _ _ _ _ hext hfs_find,
                    liftF, FSAEAD.injectQuery, FSAEAD.oracleImpl, FSAEAD.injectImpl,
                    FSAEAD.inject, PrivL15.outerFull, hended, hin_any, hrecv, hcomp_i,
                    hnot_gt, htriv]
              · refine closeBy_of_det_stepU cka prng fs Δcka qep c.1.1 b
                  (Sum.inr (Sum.inl (Sum.inr (P, c)))) k
                  sL ({ sL.1 with g := sL.1.g.accept P stLU' ⟨P.other, c.1.1, i'⟩ }, sL.2)
                  sR ({ sR.1 with g := sR.1.g.accept P stR' ⟨P.other, c.1.1, i'⟩, h := hR' }, osR_win)
                  (some (.accepted c.1.1 i' (some m')))
                  (some (.accepted c.1.1 i' (some m')))
                  ?_ ?_ ih (Or.inl (by simp [osR_win, FSAEAD.State.removeFromTransit]))
                · simp [PrivL15.runEM, Engine.implE, Engine.injectE, PrivL15.StateT_run_liftH,
                    stLU', StateT_run_commitE_ckau cka prng fs Δcka hγ_none,
                    hs.abortL, hs.winL, hitr_eq, hitr, hsafe_eq, hsafe, hvL, hcurRS, hrecv,
                    hnot_gt, htriv_eq, htriv]
                · simp [PrivL15.runEM, Engine.implE, Engine.injectE, PrivL15.StateT_run_liftH,
                    stR', hR', osR_win, PrivL15.StateT_run_commitE_fs,
                    hg.abortR, hg.winR, hitr, hsafe, hvR,
                    PrivL15.hooksFS_fsRecv_inject _ _ _ _ _ _ _ _ _ _ _ _ _ hext hfs_find,
                    liftF, FSAEAD.injectQuery, FSAEAD.oracleImpl, FSAEAD.injectImpl,
                    FSAEAD.inject, PrivL15.outerFull, hended, hin_any, hrecv, hcomp_i,
                    hnot_gt, htriv]
            · have htriv : sR.1.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ = true :=
                hg.trivial_of_isCompromised P.other i' hext hcomp_i
              have hg' := hs_vp.accept_t_ext_none hg rs' i' i' false rfl hext
              have hs' := hu_vp.accept_sync hg hs hs_vp rs' none ⟨P.other, c.1.1, i'⟩
                hR' osR_nowin rfl rfl
              refine closeBy_of_det_stepU cka prng fs Δcka qep c.1.1 b
                (Sum.inr (Sum.inl (Sum.inr (P, c)))) k
                sL ({ sL.1 with g := sL.1.g.accept P stLU' ⟨P.other, c.1.1, i'⟩ }, sL.2)
                sR ({ sR.1 with g := sR.1.g.accept P stR' ⟨P.other, c.1.1, i'⟩, h := hR' }, osR_nowin)
                (some (.accepted c.1.1 i' (some m')))
                (some (.accepted c.1.1 i' (some m')))
                ?_ ?_ ih (Or.inr ⟨rfl, Or.inr ⟨_, hg', hs'⟩⟩)
              · simp [PrivL15.runEM, Engine.implE, Engine.injectE, PrivL15.StateT_run_liftH,
                  stLU', StateT_run_commitE_ckau cka prng fs Δcka hγ_none,
                  hs.abortL, hs.winL, hitr_eq, hitr, hsafe_eq, hsafe, hvL, hcurRS, hrecv,
                  hnot_gt, htriv_eq, htriv]
              · simp [PrivL15.runEM, Engine.implE, Engine.injectE, PrivL15.StateT_run_liftH,
                  stR', hR', osR_nowin, PrivL15.StateT_run_commitE_fs,
                  hg.abortR, hg.winR, hitr, hsafe, hvR,
                  PrivL15.hooksFS_fsRecv_inject _ _ _ _ _ _ _ _ _ _ _ _ _ hext hfs_find,
                  liftF, FSAEAD.injectQuery, FSAEAD.oracleImpl, FSAEAD.injectImpl,
                  FSAEAD.inject, PrivL15.outerFull, hended, hin_any, hrecv, hcomp_i, hg.winFS,
                  hnot_gt, htriv]
      · rcases Option.isSome_iff_exists.mp (hs_vp.vR_other c.1.1 rsv hne_t.symm hvR_R).1 with ⟨rs, rfl⟩
        cases hrecv : fs.receive rs c.1 c.2 with
        | none =>
          refine closeBy_of_det_stepU cka prng fs Δcka qep t b
            (Sum.inr (Sum.inl (Sum.inr (P, c)))) k
            sL sL sR sR (some .rejected) (some .rejected) ?_ ?_ ih
            (Or.inr ⟨rfl, Or.inr ⟨sL_g, hg, hs⟩⟩)
          · simp [PrivL15.runEM, Engine.implE, Engine.injectE, PrivL15.StateT_run_liftH, hesL,
              hs.abortL, hs.winL, hitr_eq, hitr, hsafe_eq, hsafe, hvL, hrecv]
          · simp [PrivL15.runEM, Engine.implE, Engine.injectE, PrivL15.StateT_run_liftH, hesR,
              hg.abortR, hg.winR, hitr, hsafe, hvR, PrivL15.hooksFS_fsRecv_some, hrecv]
        | some val =>
          rcases val with ⟨rs', i', m'⟩
          have htriv_eq := hs.trivial_eq hg (2 + Δcka) ⟨P.other, c.1.1, i'⟩
          cases htriv : sR.1.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩
          · refine closeBy_of_det_stepU cka prng fs Δcka qep t b
              (Sum.inr (Sum.inl (Sum.inr (P, c)))) k
              sL sL sR sR (some .rejected) (some .rejected) ?_ ?_ ih
              (Or.inr ⟨rfl, Or.inr ⟨sL_g, hg, hs⟩⟩)
            · simp [PrivL15.runEM, Engine.implE, Engine.injectE, Config.priv,
                PrivL15.StateT_run_liftH, hesL,
                hs.abortL, hs.winL, hitr_eq, hitr, hsafe_eq, hsafe, hvL, hrecv,
                hnot_gt, htriv_eq, htriv]
            · simp [PrivL15.runEM, Engine.implE, Engine.injectE, Config.priv,
                PrivL15.StateT_run_liftH, hesR,
                hg.abortR, hg.winR, hitr, hsafe, hvR, PrivL15.hooksFS_fsRecv_some, hrecv,
                hnot_gt, htriv]
          · have hg' := hs_vp.accept_other hg hne_t.symm rs' i'
            have hs' := hu_vp.accept_sync hg hs hs_vp rs' (some rs') ⟨P.other, c.1.1, i'⟩
              sR.1.h sR.2 rfl rfl
            let stLU' := { s₁LU with vR := Function.update s₁LU.vR c.1.1 (some rs') }
            let stR' := { s₁R with vR := Function.update s₁R.vR c.1.1 (some (some rs')) }
            refine closeBy_of_det_stepU cka prng fs Δcka qep t b
              (Sum.inr (Sum.inl (Sum.inr (P, c)))) k
              sL ({ sL.1 with g := sL.1.g.accept P stLU' ⟨P.other, c.1.1, i'⟩ }, sL.2)
              sR ({ sR.1 with g := sR.1.g.accept P stR' ⟨P.other, c.1.1, i'⟩, h := sR.1.h }, sR.2)
              (some (.accepted c.1.1 i' (some m')))
              (some (.accepted c.1.1 i' (some m')))
              ?_ ?_ ih (Or.inr ⟨rfl, Or.inr ⟨_, hg', hs'⟩⟩)
            · simp [PrivL15.runEM, Engine.implE, Engine.injectE, PrivL15.StateT_run_liftH,
                stLU', StateT_run_commitE_ckau cka prng fs Δcka hγ_none,
                hs.abortL, hs.winL, hitr_eq, hitr, hsafe_eq, hsafe, hvL, hrecv,
                hnot_gt, htriv_eq, htriv]
            · simp [PrivL15.runEM, Engine.implE, Engine.injectE, PrivL15.StateT_run_liftH,
                stR', PrivL15.StateT_run_commitE_fs,
                hg.abortR, hg.winR, hitr, hsafe, hvR, PrivL15.hooksFS_fsRecv_some, hrecv,
                hnot_gt, htriv]
  · refine closeBy_of_det_stepU cka prng fs Δcka qep t b
      (Sum.inr (Sum.inl (Sum.inr (P, c)))) k
      sL sL sR sR none none ?_ ?_ ih (Or.inr ⟨rfl, Or.inr ⟨sL_g, hg, hs⟩⟩)
    · simp [PrivL15.runEM, Engine.implE, Engine.injectE, hs.abortL, hs.winL,
        hitr_eq, hsafe_eq, hguard, -Bool.or_eq_true]
    · simp [PrivL15.runEM, Engine.implE, Engine.injectE, hg.abortR, hg.winR,
        hguard, -Bool.or_eq_true]

/-! ### Section 4: `transmitE` and `challE` -/

omit [Inhabited E] [SampleableType KR] [SampleableType KC] in
private theorem hooksFS_fsSend_cache_eq (mo : Mode)
    (g : Engine.Ctx Γ T Sig (Option SS) (Option RS) M E) (P : Party) (t' : ℕ)
    (ssv : Option SS) (hdr : Header T) (m : M) (pair : Option (M × M))
    (h : FSState T Sig K I SS RS E) (os : FSAEAD.State SS RS (Header T) M E)
    {r : (Option (Option SS × E) × FSState T Sig K I SS RS E) × FSAEAD.State SS RS (Header T) M E}
    (hmem : r ∈ support (PrivL15.runHM (FSAEAD.oracleImpl fs)
      ((hooksFS cka prng fs Δcka mo 0).fsSend g P t' ssv hdr m pair) h os)) :
    r.1.2.cache = h.cache := by
  rcases r with ⟨⟨res, h'⟩, os'⟩
  dsimp only
  cases ssv with
  | some ss =>
    simp [PrivL15.runHM, hooksFS] at hmem
    rcases hmem with ⟨⟨_, h_eq⟩, _⟩
    subst h_eq; rfl
  | none =>
    cases hext : h.ext with
    | some val =>
      rcases val with ⟨ss₀, rs₀⟩
      simp [PrivL15.runHM, hooksFS, hext] at hmem
      rcases hmem with ⟨⟨_, h_eq⟩, _⟩
      subst h_eq; rfl
    | none =>
      by_cases hc : !(g.safeCh (2 + Δcka) P) && !h.fsSCorr
      · cases pair <;>
        · simp only [PrivL15.runHM, hooksFS, hext, hc, ↓reduceIte, liftF,
            StateT.run_bind, simulateQ_bind, StateT.run_lift, StateT.run_get,
            pure_bind, mem_support_bind_iff, Prod.exists] at hmem
          rcases hmem with ⟨a₁, h₁, os₁, hmem₁, hmem₂⟩
          have hc₁ : h = h₁ := by
            simp [PrivL15.outerFull] at hmem₁
            rcases hmem₁ with ⟨_, rfl⟩
            rfl
          subst hc₁
          cases a₁ with
          | none =>
            simp at hmem₂
            rcases hmem₂ with ⟨⟨_, h_eq⟩, _⟩
            subst h_eq; rfl
          | some _ =>
            simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
              StateT.run_bind, simulateQ_bind, StateT.run_modify, StateT.run_lift,
              StateT.run_pure, simulateQ_pure, pure_bind, mem_support_bind_iff, Prod.exists] at hmem₂
            rcases hmem₂ with ⟨a₂, h₂, os₂, hmem₂', hmem₃⟩
            have hc₂ : h₂.cache = h.cache := by
              simp [PrivL15.outerFull] at hmem₂'
              rcases hmem₂' with ⟨_, h_eq⟩
              subst h_eq; rfl
            cases a₂ <;> simp at hmem₃ <;> rcases hmem₃ with ⟨⟨_, h_eq⟩, _⟩ <;>
              subst h_eq <;> exact hc₂
      · cases pair <;>
        · simp only [PrivL15.runHM, hooksFS, hext, hc, Bool.false_eq_true, Bool.not_true,
            ↓reduceIte, liftF, StateT.run_bind, simulateQ_bind, StateT.run_lift, StateT.run_get,
            pure_bind, mem_support_bind_iff, Prod.exists] at hmem
          rcases hmem with ⟨a₂, h₂, os₂, hmem₂', hmem₃⟩
          have hc₂ : h₂ = h := by
            simp [PrivL15.outerFull] at hmem₂'
            rcases hmem₂' with ⟨_, rfl⟩
            rfl
          subst hc₂
          cases a₂ <;> simp at hmem₃ <;> rcases hmem₃ with ⟨⟨_, h_eq⟩, _⟩ <;>
            subst h_eq <;> rfl

omit [SampleableType KR] [SampleableType KC] in
private theorem vSendRecord_fs_stay_preserves (mo : Mode)
    (g gR₀ : Engine.Ctx Γ T Sig (Option SS) (Option RS) M E)
    (P : Party) (mR : M) (pair : Option (M × M)) (r : Option CCoins) (bad : Bool)
    (sR sR' : PrivL15.StateR Γ T Sig K I SS RS M E)
    {c : Header T × E}
    (hid : (g.st P).id = P)
    (htcur : (g.st P).tcur = g.epoch P)
    (hPs : P.sendsIn (g.epoch P) = true)
    (hrun : PrivL15.runEM (FSAEAD.oracleImpl fs)
      (PrivL15.vSendRecord (hooksFS cka prng fs Δcka mo 0) (2 + Δcka) g P mR pair r bad)
      ({ sR.1 with g := gR₀ }, sR.2) = pure (some c, sR')) :
    sR'.1.h.cache = sR.1.h.cache ∧ ∀ Q, (sR'.1.g.st Q).root = (g.st Q).root := by
  have hPs_next : P.sendsIn ((g.st P).tcur + 1) = false := by
    rw [htcur, PrivL15.Party.sendsIn_succ, hPs]; rfl
  cases hvS : (g.st P).vS with
  | none =>
    simp [PrivL15.vSendRecord, Engine.vSend, hid, hPs_next, hvS, PrivL15.runEM,
      PrivL15.StateT_run_liftH] at hrun
    rcases hrun with ⟨_, h_eq⟩
    subst h_eq
    refine ⟨rfl, fun Q => ?_⟩
    rcases eq_or_ne Q P with rfl | hne
    · simp [GameState.record]
    · simp [GameState.record]
  | some ssv =>
    have hmem : (some c, sR') ∈ support (PrivL15.runEM (FSAEAD.oracleImpl fs)
        (PrivL15.vSendRecord (hooksFS cka prng fs Δcka mo 0) (2 + Δcka) g P mR pair r bad)
        ({ sR.1 with g := gR₀ }, sR.2)) := by
      rw [hrun]; simp
    simp only [PrivL15.vSendRecord, Engine.vSend, hid, hPs_next, Bool.false_eq_true, ↓reduceIte,
      hvS, PrivL15.runEM_liftH_bind, pure_bind, mem_support_bind_iff] at hmem
    rcases hmem with ⟨res, hfs, hmem₂⟩
    have hcache := hooksFS_fsSend_cache_eq cka prng fs Δcka mo g P (g.st P).tcur ssv
      ((g.st P).tcur, (g.st P).curCkaMsg) mR pair sR.1.h sR.2 hfs
    rcases res with ⟨⟨_ | ⟨v', e⟩, h'⟩, os'⟩
    · simp [PrivL15.runEM, PrivL15.StateT_run_liftH, Engine.abortE] at hmem₂
    · simp [PrivL15.runEM, PrivL15.StateT_run_liftH] at hmem₂
      rcases hmem₂ with ⟨_, h_eq⟩
      subst h_eq
      refine ⟨hcache, fun Q => ?_⟩
      rcases eq_or_ne Q P with rfl | hne
      · simp [GameState.record]
      · simp [GameState.record, hne]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType I] [SampleableType K] in
private theorem SyncU15.of_record_stay {fs : FSAEADScheme K SS RS (Header T) M E}
    {Δcka qep t : ℕ} {b : Bool} {prng : PRFPRNG KR Sig I K}
    {sL : StateLU Γ T Sig SS RS M E I K}
    {sL_g : PrivL15.StateL Γ T Sig SS RS M E K I}
    {sR sR' : PrivL15.StateR Γ T Sig K I SS RS M E}
    (hg : PrivL15.ActiveInv fs Δcka qep none t b sL_g sR)
    (hs : SyncU15 prng t b sL sL_g sR)
    (P : Party) (vS' : Option SS) (mL : M) (c : Header T × E) (bad : Bool)
    (hg' : PrivL15.ActiveInv fs Δcka qep none t b
      ({ sL_g.1 with g := (sL_g.1.g.record (2 + Δcka) P
          { sL_g.1.g.st P with vS := vS' }
          ⟨⟨P, sL_g.1.g.epoch P, sL_g.1.g.idx P + 1⟩, mL, c⟩ bad) }, sL_g.2)
      sR')
    (hcache : sR'.1.h.cache = sR.1.h.cache)
    (hroot_R : ∀ Q, (sR'.1.g.st Q).root = (sR.1.g.st Q).root) :
    SyncU15 prng t b
      ({ sL.1 with g := (sL.1.g.record (2 + Δcka) P
          { sL.1.g.st P with vS := vS' }
          ⟨⟨P, sL.1.g.epoch P, sL.1.g.idx P + 1⟩, mL, c⟩ bad) }, sL.2)
      ({ sL_g.1 with g := (sL_g.1.g.record (2 + Δcka) P
          { sL_g.1.g.st P with vS := vS' }
          ⟨⟨P, sL_g.1.g.epoch P, sL_g.1.g.idx P + 1⟩, mL, c⟩ bad) }, sL_g.2)
      sR' := by
  have hep' : sR'.1.g.epoch = sR.1.g.epoch := by
    simpa [GameState.record, hg.epoch_eq] using hg'.epoch_eq.symm
  have hγg := hg.γ_eq
  have hTg := hg.Tcur_eq
  refine
    { abortL := hs.abortL
      winL := hs.winL
      bL := hs.bL
      epoch_eq := by simp [GameState.record, hs.epoch_eq, hep']
      idx_eq := by rw [← hg'.idx_eq]; simp [GameState.record, hs.idx_eq, hg.idx_eq]
      tL_eq := by rw [← hg'.tL_eq]; simp [GameState.record, hs.tL_eq, hg.tL_eq]
      chall_eq := by
        rw [← hg'.chall_eq]
        simp [GameState.record, hs.chall_eq, hg.chall_eq, hs.epoch_eq,
          hg.epoch_eq, hs.idx_eq, hg.idx_eq]
      comp_eq := by
        have hsafeL := hs.safeCh_eq (2 + Δcka) P
        have hsafeG := hg.safeCh_eq (2 + Δcka) P
        rw [← hg'.comp_eq]
        simp [GameState.record, hsafeL, hsafeG, hs.epoch_eq, hg.epoch_eq,
          hs.idx_eq, hg.idx_eq, hs.comp_eq, hg.comp_eq]
      maxAcc_eq := by rw [← hg'.maxAcc_eq]; simp [GameState.record, hs.maxAcc_eq, hg.maxAcc_eq]
      leaks_eq := by rw [← hg'.leaks_eq]; simp [GameState.record, hs.leaks_eq, hg.leaks_eq]
      corrs_eq := by rw [← hg'.corrs_eq]; simp [GameState.record, hs.corrs_eq, hg.corrs_eq]
      trans_eq := by
        simp [GameState.record, hs.trans_eq, hs.epoch_eq, hg.epoch_eq, hs.idx_eq, hg.idx_eq]
      idL := fun Q => by
        rcases eq_or_ne Q P with rfl | hne
        · simp [GameState.record, hs.idL]
        · simp [GameState.record, hne, hs.idL]
      tcurL := fun Q => by
        rw [hep']
        rcases eq_or_ne Q P with rfl | hne
        · simp [GameState.record, hs.tcurL]
        · simp [GameState.record, hne, hs.tcurL]
      γ_eq := fun Q => by
        have hγR := hg'.γ_eq Q
        rcases eq_or_ne Q P with rfl | hne
        · simp only [GameState.record, Function.update_self] at hγR ⊢
          rw [← hγR, hγg Q, hs.γ_eq Q]
        · simp only [GameState.record, Function.update_of_ne hne] at hγR ⊢
          rw [← hγR, hγg Q, hs.γ_eq Q]
      Tcur_eq := fun Q => by
        have hTR := hg'.Tcur_eq Q
        rcases eq_or_ne Q P with rfl | hne
        · simp only [GameState.record, Function.update_self] at hTR ⊢
          rw [← hTR, hTg Q, hs.Tcur_eq Q]
        · simp only [GameState.record, Function.update_of_ne hne] at hTR ⊢
          rw [← hTR, hTg Q, hs.Tcur_eq Q]
      root_eq := fun Q => by
        rw [hroot_R Q]
        rcases eq_or_ne Q P with rfl | hne
        · simp [GameState.record, hs.root_eq]
        · simp [GameState.record, hne, hs.root_eq]
      vS_eq := fun Q => by
        rcases eq_or_ne Q P with rfl | hne
        · simp [GameState.record]
        · simp [GameState.record, hne, hs.vS_eq]
      vR_eq := fun Q => by
        rcases eq_or_ne Q P with rfl | hne
        · simp [GameState.record, hs.vR_eq]
        · simp [GameState.record, hne, hs.vR_eq]
      same_ep_root := fun hepAB => by
        rw [hep'] at hepAB
        rw [hroot_R .A, hroot_R .B]
        exact hs.same_ep_root hepAB
      cacheL_none := fun t' hc => hs.cacheL_none t' (hcache ▸ hc)
      cache_pending := fun t' Tc σc kc ext hlt hc => by
        rw [hep'] at hlt
        simp only [hroot_R]
        exact hs.cache_pending t' Tc σc kc ext hlt (hcache ▸ hc)
      kOpt_eq := hs.kOpt_eq
      slot_eq := hs.slot_eq }

omit [SampleableType KR] [SampleableType KC] in
private theorem vSend_stay_coupled (t : ℕ) {b : Bool}
    {sL : StateLU Γ T Sig SS RS M E I K}
    {sL_g : PrivL15.StateL Γ T Sig SS RS M E K I}
    {sR : PrivL15.StateR Γ T Sig K I SS RS M E}
    (hg : PrivL15.ActiveInv fs Δcka qep none t b sL_g sR)
    (hs : SyncU15 prng t b sL sL_g sR)
    {P : Party} (hPs : P.sendsIn (sR.1.g.epoch P) = true)
    (mL mR : M) (pair : Option (M × M)) (r : Option CCoins) (bad : Bool)
    (gLU₀ : Engine.Ctx (Option Γ) T Sig SS RS M E)
    (gLg₀ : Engine.Ctx Γ T (Option Sig) SS RS M E)
    (gR₀ : Engine.Ctx Γ T Sig (Option SS) (Option RS) M E)
    {c : Header T × E} {sL_g' : PrivL15.StateL Γ T Sig SS RS M E K I}
    {sR' : PrivL15.StateR Γ T Sig K I SS RS M E}
    (hLg : PrivL15.runEM (PrivL15.eagerOracleImpl prng)
      (PrivL15.vSendRecord (hooksPRNG cka prng fs ⟨false, none, t⟩)
        (2 + Δcka) sL_g.1.g P mL pair r bad)
      ({ sL_g.1 with g := gLg₀ }, sL_g.2) = pure (some c, sL_g'))
    (hR : PrivL15.runEM (FSAEAD.oracleImpl fs)
      (PrivL15.vSendRecord (hooksFS cka prng fs Δcka ⟨false, none, t⟩ 0)
        (2 + Δcka) sR.1.g P mR pair r bad)
      ({ sR.1 with g := gR₀ }, sR.2) = pure (some c, sR'))
    (hg' : PrivL15.ActiveInv fs Δcka qep none t b sL_g' sR') :
    ∃ sL' : StateLU Γ T Sig SS RS M E I K,
      PrivL15.runEM (eagerCKAKeyImpl cka Δcka 0)
        (PrivL15.vSendRecord (hooksCKAUEager cka prng fs Δcka ⟨false, none, t⟩)
          (2 + Δcka) sL.1.g P mL pair r bad)
        ({ sL.1 with g := gLU₀ }, sL.2) = pure (some c, sL') ∧
      SyncU15 prng t b sL' sL_g' sR' := by
  have hPs_next_g : P.sendsIn ((sL_g.1.g.st P).tcur + 1) = false := by
    rw [hg.tcurL P, PrivL15.Party.sendsIn_succ, hPs]; rfl
  have hPs_next_u : P.sendsIn ((sL.1.g.st P).tcur + 1) = false := by
    rw [hs.tcurL P, PrivL15.Party.sendsIn_succ, hPs]; rfl
  have hhdr : ((sL.1.g.st P).tcur, (sL.1.g.st P).curCkaMsg) =
      ((sL_g.1.g.st P).tcur, (sL_g.1.g.st P).curCkaMsg) := by
    rw [hs.tcurL P, hg.tcurL P, hs.Tcur_eq P, hg.Tcur_eq P]
  rcases vSendRecord_fs_stay_preserves cka prng fs Δcka ⟨false, none, t⟩
      sR.1.g gR₀ P mR pair r bad sR sR' (hg.idR P) (hg.tcurR P) hPs hR with
    ⟨hcache, hroot_R⟩
  cases hvSg : (sL_g.1.g.st P).vS with
  | none =>
    have hvSu : (sL.1.g.st P).vS = none := (hs.vS_eq P).trans hvSg
    simp [PrivL15.vSendRecord, Engine.vSend, hg.idL P, hPs_next_g, hvSg, PrivL15.runEM,
      PrivL15.StateT_run_liftH] at hLg
    rcases hLg with ⟨rfl, rfl⟩
    have hstU : { sL.1.g.st P with vS := none } = sL.1.g.st P := by
      cases h : sL.1.g.st P; simp_all
    have hstG : { sL_g.1.g.st P with vS := none } = sL_g.1.g.st P := by
      cases h : sL_g.1.g.st P; simp_all
    refine ⟨({ sL.1 with g := (sL.1.g.record (2 + Δcka) P (sL.1.g.st P)
        ⟨⟨P, sL.1.g.epoch P, sL.1.g.idx P + 1⟩, mL,
          (((sL_g.1.g.st P).tcur, (sL_g.1.g.st P).curCkaMsg), default)⟩ bad) }, sL.2), ?_, ?_⟩
    · simp [PrivL15.vSendRecord, Engine.vSend, hs.idL P, hPs_next_u, hvSu, hhdr,
        PrivL15.runEM, PrivL15.StateT_run_liftH]
    · have hs' := hs.of_record_stay hg P none mL
        (((sL_g.1.g.st P).tcur, (sL_g.1.g.st P).curCkaMsg), default) bad
        (by simpa [hstG] using hg') hcache hroot_R
      simpa [hstU, hstG] using hs'
  | some ss₀ =>
    have hvSu : (sL.1.g.st P).vS = some ss₀ := (hs.vS_eq P).trans hvSg
    have hid_next_g : (sL_g.1.g.st P).id.sendsIn ((sL_g.1.g.st P).tcur + 1) = false := by
      rw [hg.idL P]; exact hPs_next_g
    have hid_next_u : (sL.1.g.st P).id.sendsIn ((sL.1.g.st P).tcur + 1) = false := by
      rw [hs.idL P]; exact hPs_next_u
    simp [PrivL15.vSendRecord, Engine.vSend, hooksPRNG, hid_next_g, hvSg,
      PrivL15.runEM, PrivL15.StateT_run_liftH] at hLg
    rcases hLg with ⟨rfl, rfl⟩
    let vS' : Option SS :=
      some (fs.send ss₀ ((sL_g.1.g.st P).tcur, (sL_g.1.g.st P).curCkaMsg) mL).1
    let ct' : Header T × E :=
      (((sL_g.1.g.st P).tcur, (sL_g.1.g.st P).curCkaMsg),
        (fs.send ss₀ ((sL_g.1.g.st P).tcur, (sL_g.1.g.st P).curCkaMsg) mL).2)
    refine ⟨({ sL.1 with g := (sL.1.g.record (2 + Δcka) P
        { sL.1.g.st P with vS := vS' }
        ⟨⟨P, sL.1.g.epoch P, sL.1.g.idx P + 1⟩, mL, ct'⟩ bad) }, sL.2), ?_, ?_⟩
    · simp [PrivL15.vSendRecord, Engine.vSend, hooksCKAUEager, hooksCKAU, liftCKAComp,
        hid_next_u, hvSu, hhdr, PrivL15.runEM, PrivL15.StateT_run_liftH, vS', ct']
    · exact hs.of_record_stay hg P vS' mL ct' bad hg' hcache hroot_R

omit [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] in
private theorem runHM_startSend_ckau_eq (mo : Mode)
    (s₁ : Engine.Ctx (Option Γ) T Sig SS RS M E) (P : Party) (t' : ℕ) (γ : Γ) (σ : Sig)
    (r : Option CCoins) (hL : CKAUState T I K) (osL : CKAEagerState Γ T K) :
    PrivL15.runHM (eagerCKAKeyImpl cka Δcka 0)
      ((hooksCKAUEager cka prng fs Δcka mo).startSend s₁ P t' (some γ) σ r) hL osL =
    PrivL15.optSample CCoins r >>= fun coins =>
      PrivL15.runHM (eagerCKAKeyImpl cka Δcka 0)
        ((hooksCKAUEager cka prng fs Δcka mo).startSend s₁ P t' (some γ) σ (some coins)) hL osL := by
  cases r with
  | some coins => simp [PrivL15.optSample]
  | none =>
    simp [PrivL15.optSample, hooksCKAUEager, PrivL15.runHM, StateT.run_bind, simulateQ_bind,
      PrivL15.simulateQ_outerFull_sampleT, bind_map_left]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType I] [SampleableType K] in
private theorem SyncU15.advance_sync {fs : FSAEADScheme K SS RS (Header T) M E}
    {Δcka qep t : ℕ} {b : Bool} {prng : PRFPRNG KR Sig I K}
    {sL : StateLU Γ T Sig SS RS M E I K}
    {sL_g : PrivL15.StateL Γ T Sig SS RS M E K I}
    {sR : PrivL15.StateR Γ T Sig K I SS RS M E}
    (hg : PrivL15.ActiveInv fs Δcka qep none t b sL_g sR)
    (hs : SyncU15 prng t b sL sL_g sR)
    {P : Party} (hPs_next : P.sendsIn (sR.1.g.epoch P + 1) = true)
    (bad : Bool) (γ' : Γ) (T' : T) (Ik : I)
    (σL' : Option Sig) (kL : K) (pgL' : PrivL15.EagerState Sig I K)
    (slU' : PrivL15.KeySlot K)
    (kR : K) (ext : Bool) (kOpt' : Option K)
    (hR_mid : FSState T Sig K I SS RS E)
    (hslot' : slU' = pgL'.2)
    (hkR_ne : sR.1.g.epoch P + 1 ≠ t → (prng.up (sR.1.g.st P).root Ik).2 = kR)
    (hkOpt_t : sR.1.g.epoch P + 1 = t → kOpt' = some kL)
    (hkOpt_ne : sR.1.g.epoch P + 1 ≠ t → kOpt' = sL.1.h.2) :
    let t' := sR.1.g.epoch P + 1
    let p := prng.up (sR.1.g.st P).root Ik
    let s₁LU := if bad && !sL.1.g.safeCh (2 + Δcka) P then sL.1.g.leak t' else sL.1.g
    let s₁L := if bad && !sL_g.1.g.safeCh (2 + Δcka) P then sL_g.1.g.leak t' else sL_g.1.g
    let s₁R := if bad && !sR.1.g.safeCh (2 + Δcka) P then sR.1.g.leak t' else sR.1.g
    let stLU₁ : Engine.VP (Option Γ) T Sig SS RS :=
      { sL.1.g.st P with
          root := p.1
          vS := some (fs.initSender kL)
          γ := some γ'
          curCkaMsg := some T'
          tcur := t' }
    let stL₁ : Engine.VP Γ T (Option Sig) SS RS :=
      { sL_g.1.g.st P with
          root := σL'
          vS := some (fs.initSender kL)
          γ := γ'
          curCkaMsg := some T'
          tcur := t' }
    let stR₁ : Engine.VP Γ T Sig (Option SS) (Option RS) :=
      { sR.1.g.st P with
          root := p.1
          vS := some (if ext then none else some (fs.initSender kR))
          γ := γ'
          curCkaMsg := some T'
          tcur := t' }
    let gMidLU : Engine.Ctx (Option Γ) T Sig SS RS M E :=
      { s₁LU with
          st := Function.update sL.1.g.st P stLU₁
          epoch := Function.update sL.1.g.epoch P t'
          idx := Function.update sL.1.g.idx P 0 }
    let gMidL : Engine.Ctx Γ T (Option Sig) SS RS M E :=
      { s₁L with
          st := Function.update sL_g.1.g.st P stL₁
          epoch := Function.update sL_g.1.g.epoch P t'
          idx := Function.update sL_g.1.g.idx P 0 }
    let gMidR : Engine.Ctx Γ T Sig (Option SS) (Option RS) M E :=
      { s₁R with
          st := Function.update sR.1.g.st P stR₁
          epoch := Function.update sR.1.g.epoch P t'
          idx := Function.update sR.1.g.idx P 0 }
    let hLU' : CKAUState T I K :=
      ({ sL.1.h.1 with cache := Function.update sL.1.h.1.cache t' (some (T', Ik)) }, kOpt')
    let hL' : PRNGState T Sig K :=
      { cache := Function.update sL_g.1.h.cache t' (some (T', σL', kL)) }
    let hR' : FSState T Sig K I SS RS E :=
      { hR_mid with cache := Function.update sR.1.h.cache t' (some (T', p.1, kR, ext)) }
    SyncU15 prng t b
      ({ sL.1 with g := gMidLU, h := hLU' }, (sL.2.1, slU'))
      ({ sL_g.1 with g := gMidL, h := hL' }, pgL')
      ({ sR.1 with g := gMidR, h := hR' }, sR.2) := by
  intro t' p s₁LU s₁L s₁R stLU₁ stL₁ stR₁ gMidLU gMidL gMidR hLU' hL' hR'
  rcases hg.epoch_of_sendsIn_succ hPs_next with ⟨_, _, hPs1, hepM, hall_ep⟩
  have hsafeL := hs.safeCh_eq (2 + Δcka) P
  have hsafeG := hg.safeCh_eq (2 + Δcka) P
  have hepAB₀ : sR.1.g.epoch .A = sR.1.g.epoch .B := (hall_ep .A).trans (hall_ep .B).symm
  have hroot_all : ∀ Q, (sR.1.g.st Q).root = (sR.1.g.st P).root := by
    have hAB := hs.same_ep_root hepAB₀
    intro Q; cases Q <;> cases P <;> simp [hAB]
  refine
    { abortL := hs.abortL
      winL := by simp only [gMidLU, s₁LU]; split_ifs <;> simp [GameState.leak, hs.winL]
      bL := by simp only [gMidLU, s₁LU]; split_ifs <;> simp [GameState.leak, hs.bL]
      epoch_eq := by simp [gMidLU, gMidR, hs.epoch_eq]
      idx_eq := by simp [gMidLU, gMidR, hs.idx_eq]
      tL_eq := by
        simp only [gMidLU, gMidR, s₁LU, s₁R, hsafeL]
        split_ifs <;> simp [GameState.leak, hs.tL_eq]
      chall_eq := by
        simp only [gMidLU, gMidR, s₁LU, s₁R, hsafeL]
        split_ifs <;> simp [GameState.leak, hs.chall_eq]
      comp_eq := by
        simp only [gMidLU, gMidR, s₁LU, s₁R, hsafeL]
        split_ifs <;> simp [GameState.leak, hs.comp_eq]
      maxAcc_eq := by
        simp only [gMidLU, gMidR, s₁LU, s₁R, hsafeL]
        split_ifs <;> simp [GameState.leak, hs.maxAcc_eq]
      leaks_eq := by
        simp only [gMidLU, gMidR, s₁LU, s₁R, hsafeL]
        split_ifs <;> simp [GameState.leak, hs.tL_eq, hs.leaks_eq]
      corrs_eq := by
        simp only [gMidLU, gMidR, s₁LU, s₁R, hsafeL]
        split_ifs <;> simp [GameState.leak, hs.corrs_eq]
      trans_eq := by
        simp only [gMidLU, gMidL, s₁LU, s₁L, hsafeL, hsafeG]
        split_ifs <;> simp [GameState.leak, hs.trans_eq]
      idL := fun Q => by
        rcases eq_or_ne Q P with rfl | hne
        · simp [gMidLU, stLU₁, hs.idL]
        · simp [gMidLU, hne, hs.idL]
      tcurL := fun Q => by
        rcases eq_or_ne Q P with rfl | hne
        · simp [gMidLU, gMidR, stLU₁]
        · simp [gMidLU, gMidR, hne, hs.tcurL]
      γ_eq := fun Q => by
        rcases eq_or_ne Q P with rfl | hne
        · simp [gMidLU, gMidR, stLU₁, stR₁]
        · simp [gMidLU, gMidR, hne, hs.γ_eq]
      Tcur_eq := fun Q => by
        rcases eq_or_ne Q P with rfl | hne
        · simp [gMidLU, gMidR, stLU₁, stR₁]
        · simp [gMidLU, gMidR, hne, hs.Tcur_eq]
      root_eq := fun Q => by
        rcases eq_or_ne Q P with rfl | hne
        · simp [gMidLU, gMidR, stLU₁, stR₁]
        · simp [gMidLU, gMidR, hne, hs.root_eq]
      vS_eq := fun Q => by
        rcases eq_or_ne Q P with rfl | hne
        · simp [gMidLU, gMidL, stLU₁, stL₁]
        · simp [gMidLU, gMidL, hne, hs.vS_eq]
      vR_eq := fun Q => by
        rcases eq_or_ne Q P with rfl | hne
        · simp [gMidLU, gMidL, stLU₁, stL₁, hs.vR_eq]
        · simp [gMidLU, gMidL, hne, hs.vR_eq]
      same_ep_root := fun hepAB => by
        exfalso
        cases P <;> simp [gMidR, t', hepAB₀] at hepAB
      cacheL_none := fun t'' hc => by
        rcases eq_or_ne t'' t' with rfl | hne
        · simp [hR'] at hc
        · simp only [hR', Function.update_of_ne hne] at hc
          simp [hLU', hne, hs.cacheL_none t'' hc]
      cache_pending := fun t'' Tc σc kc ext' hlt hc => by
        rcases eq_or_ne t'' t' with rfl | hne
        · simp only [hR', Function.update_self, Option.some.injEq, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl, rfl, rfl⟩
          have hPr_ne : Party.receiverOf t' ≠ P := fun heq =>
            PrivL15.Party.senderOf_ne_receiverOf t' (hPs1.symm.trans heq.symm)
          refine ⟨by simp [gMidR, stR₁, t', ← hPs1], Ik, by simp [hLU'], ?_, ?_⟩
          · simp [gMidR, hPr_ne, hroot_all (Party.receiverOf t'), p]
          · intro hne_t
            simp [gMidR, hPr_ne, hroot_all (Party.receiverOf t'), hkR_ne hne_t]
        · exfalso
          dsimp only at hlt
          simp only [hR', Function.update_of_ne hne] at hc
          have hc_ne : sR.1.h.cache t'' ≠ none := by simp [hc]
          have hle_max := (hg.cache_some_le_maxEp t'' hc_ne).2
          rw [hepM] at hle_max
          have hge : sR.1.g.epoch P ≤ gMidR.epoch (Party.receiverOf t'') := by
            rcases eq_or_ne (Party.receiverOf t'') P with heq | hneP
            · simp [gMidR, heq, t']
            · simp [gMidR, hneP, hall_ep (Party.receiverOf t'')]
          omega
      kOpt_eq := fun Tc σL k₀ hc => by
        rcases eq_or_ne t t' with rfl | hne
        · simp only [hL', Function.update_self, Option.some.injEq, Prod.mk.injEq] at hc
          rcases hc with ⟨_, _, rfl⟩
          exact hkOpt_t rfl
        · simp only [hL', Function.update_of_ne hne] at hc
          exact (hkOpt_ne (Ne.symm hne)).trans (hs.kOpt_eq Tc σL k₀ hc)
      slot_eq := hslot' }

omit [Inhabited E] [SampleableType KR] [SampleableType KC] in
private theorem closeBy_startSendU (t : ℕ) {b : Bool}
    {sL : StateLU Γ T Sig SS RS M E I K}
    {sL_g : PrivL15.StateL Γ T Sig SS RS M E K I}
    {sR : PrivL15.StateR Γ T Sig K I SS RS M E}
    (hg : PrivL15.ActiveInv fs Δcka qep none t b sL_g sR)
    (hs : SyncU15 prng t b sL sL_g sR)
    {P : Party} (hPs_next : P.sendsIn (sR.1.g.epoch P + 1) = true)
    (hqep : ¬(qep < sR.1.g.epoch P + 1))
    (bad : Bool) (r : Option CCoins)
    (s₁_epLU : Engine.Ctx (Option Γ) T Sig SS RS M E)
    (s₁_epR : Engine.Ctx Γ T Sig (Option SS) (Option RS) M E)
    (fR : (Option (Option Γ × T × Sig × SS) × CKAUState T I K) × CKAEagerState Γ T K → ProbComp Bool)
    (fM fL : (Option (Γ × T × Sig × Option SS) × FSState T Sig K I SS RS E) ×
      FSAEAD.State SS RS (Header T) M E → ProbComp Bool)
    (hcont : ∀ (γ' : Γ) (T' : T) (σL' : Option Sig) (kL : K)
        (pgL' : PrivL15.EagerState Sig I K) (slU' : PrivL15.KeySlot K)
        (σR' : Sig) (kR : K) (ext : Bool)
        (hLU' : CKAUState T I K) (hL' : PRNGState T Sig K)
        (hR' : FSState T Sig K I SS RS E),
      let t' := sR.1.g.epoch P + 1
      let s₁LU := if bad && !sL.1.g.safeCh (2 + Δcka) P then sL.1.g.leak t' else sL.1.g
      let s₁L := if bad && !sL_g.1.g.safeCh (2 + Δcka) P then sL_g.1.g.leak t' else sL_g.1.g
      let s₁R := if bad && !sR.1.g.safeCh (2 + Δcka) P then sR.1.g.leak t' else sR.1.g
      let stLU₁ : Engine.VP (Option Γ) T Sig SS RS :=
        { sL.1.g.st P with
            root := σR', vS := some (fs.initSender kL),
            γ := some γ', curCkaMsg := some T', tcur := t' }
      let stL₁ : Engine.VP Γ T (Option Sig) SS RS :=
        { sL_g.1.g.st P with
            root := σL', vS := some (fs.initSender kL),
            γ := γ', curCkaMsg := some T', tcur := t' }
      let stR₁ : Engine.VP Γ T Sig (Option SS) (Option RS) :=
        { sR.1.g.st P with
            root := σR', vS := some (if ext then none else some (fs.initSender kR)),
            γ := γ', curCkaMsg := some T', tcur := t' }
      let gMidLU : Engine.Ctx (Option Γ) T Sig SS RS M E :=
        { s₁LU with
            st := Function.update sL.1.g.st P stLU₁
            epoch := Function.update sL.1.g.epoch P t'
            idx := Function.update sL.1.g.idx P 0 }
      let gMidL : Engine.Ctx Γ T (Option Sig) SS RS M E :=
        { s₁L with
            st := Function.update sL_g.1.g.st P stL₁
            epoch := Function.update sL_g.1.g.epoch P t'
            idx := Function.update sL_g.1.g.idx P 0 }
      let gMidR : Engine.Ctx Γ T Sig (Option SS) (Option RS) M E :=
        { s₁R with
            st := Function.update sR.1.g.st P stR₁
            epoch := Function.update sR.1.g.epoch P t'
            idx := Function.update sR.1.g.idx P 0 }
      PrivL15.ActiveInv fs Δcka qep none t b
        ({ sL_g.1 with g := gMidL, h := hL' }, pgL')
        ({ sR.1 with g := gMidR, h := hR' }, sR.2) →
      SyncU15 prng t b
        ({ sL.1 with g := gMidLU, h := hLU' }, (sL.2.1, slU'))
        ({ sL_g.1 with g := gMidL, h := hL' }, pgL')
        ({ sR.1 with g := gMidR, h := hR' }, sR.2) →
      PrivL15.CloseBy
        (fR ((some (some γ', T', σR', fs.initSender kL), hLU'), (sL.2.1, slU')))
        (fM ((some (γ', T', σR', if ext then none else some (fs.initSender kR)), hR'), sR.2))
        (fL ((some (γ', T', σR', if ext then none else some (fs.initSender kR)), hR'), sR.2))) :
    PrivL15.CloseBy
      (PrivL15.runHM (eagerCKAKeyImpl cka Δcka 0)
        ((hooksCKAUEager cka prng fs Δcka ⟨false, none, t⟩).startSend s₁_epLU P
          (sR.1.g.epoch P + 1) (some (sR.1.g.st P).γ) (sR.1.g.st P).root r) sL.1.h sL.2 >>= fR)
      (PrivL15.runHM (FSAEAD.oracleImpl fs)
        ((hooksFS cka prng fs Δcka ⟨false, none, t⟩ 0).startSend s₁_epR P
          (sR.1.g.epoch P + 1) (sR.1.g.st P).γ (sR.1.g.st P).root r) sR.1.h sR.2 >>= fM)
      (PrivL15.runHM (FSAEAD.oracleImpl fs)
        ((hooksFS cka prng fs Δcka ⟨false, none, t⟩ 0).startSend s₁_epR P
          (sR.1.g.epoch P + 1) (sR.1.g.st P).γ (sR.1.g.st P).root r) sR.1.h sR.2 >>= fL) := by
  rw [runHM_startSend_ckau_eq, PrivL15.runHM_startSend_fs_eq, bind_assoc, bind_assoc, bind_assoc]
  refine PrivL15.closeBy_bind (PrivL15.optSample CCoins r) fun coins => ?_
  rcases hg.epoch_of_sendsIn_succ hPs_next with ⟨_, _, _, hepM, hall_ep⟩
  set c := cka.send (sR.1.g.st P).γ coins
  set p := prng.up (sR.1.g.st P).root c.2.2
  rcases lt_trichotomy t (sR.1.g.epoch P + 1) with hgt | rfl | hlt
  · have hne : sR.1.g.epoch P + 1 ≠ t := by omega
    have hL_eval :
        PrivL15.runHM (eagerCKAKeyImpl cka Δcka 0)
          ((hooksCKAUEager cka prng fs Δcka ⟨false, none, t⟩).startSend s₁_epLU P
            (sR.1.g.epoch P + 1) (some (sR.1.g.st P).γ) (sR.1.g.st P).root (some coins))
          sL.1.h sL.2 =
        pure ((some (some c.1, c.2.1, p.1, fs.initSender p.2),
          ({ sL.1.h.1 with cache := (Function.update sL.1.h.1.cache (sR.1.g.epoch P + 1)
              (some (c.2.1, c.2.2))) }, sL.1.h.2)), (sL.2.1, sL.2.2)) := by
      rcases sL.2 with ⟨sc, sl⟩
      simp [PrivL15.runHM, hooksCKAUEager, cacheCUEager, hne, c, p]
    have hR_eval :
        PrivL15.runHM (FSAEAD.oracleImpl fs)
          ((hooksFS cka prng fs Δcka ⟨false, none, t⟩ 0).startSend s₁_epR P
            (sR.1.g.epoch P + 1) (sR.1.g.st P).γ (sR.1.g.st P).root (some coins))
          sR.1.h sR.2 =
        pure ((some (c.1, c.2.1, p.1, if false then none else some (fs.initSender p.2)),
          { sR.1.h with cache := (Function.update sR.1.h.cache (sR.1.g.epoch P + 1)
              (some (c.2.1, p.1, p.2, false))) }), sR.2) := by
      simp [PrivL15.runHM, hooksFS, rootFS, extOf, hgt, c, p]
    rw [hL_eval, hR_eval, pure_bind, pure_bind, pure_bind]
    exact hcont c.1 c.2.1 (some p.1) p.2 sL_g.2 sL.2.2 p.1 p.2 false _ _ _
      (hg.advance_core hPs_next hqep bad c.1 c.2.1 (some p.1) p.2 sL_g.2 p.1 p.2 false sR.1.h
        (by simp; omega) (fun _ => rfl) (by simp; omega) ⟨rfl, rfl, rfl, rfl⟩
        (fun ht => absurd ht hne) (fun ht => absurd ht (by omega)))
      (hs.advance_sync hg hPs_next bad c.1 c.2.1 c.2.2 (some p.1) p.2 sL_g.2 sL.2.2 p.2 false
        sL.1.h.2 sR.1.h hs.slot_eq (fun _ => rfl) (fun ht => absurd ht hne) (fun _ => rfl))
  · have hbef := hg.before_t (by rw [hepM]; omega)
    rcases hbef with ⟨hbL, hcorrL, hprngL, hprfL, htableL, hroot_σ, _,
      htableR, hsessR, hfsTransR, hfsCountR, hfsSCorrR, hextR, k_fs, hslot_g, hosR⟩
    have hslotU : sL.2.2 = .ready k_fs := hs.slot_eq.trans hslot_g
    have hL_eval :
        PrivL15.runHM (eagerCKAKeyImpl cka Δcka 0)
          ((hooksCKAUEager cka prng fs Δcka ⟨false, none, sR.1.g.epoch P + 1⟩).startSend s₁_epLU P
            (sR.1.g.epoch P + 1) (some (sR.1.g.st P).γ) (sR.1.g.st P).root (some coins))
          sL.1.h sL.2 =
        pure ((some (some c.1, c.2.1, p.1, fs.initSender k_fs),
          ({ sL.1.h.1 with cache := (Function.update sL.1.h.1.cache (sR.1.g.epoch P + 1)
              (some (c.2.1, c.2.2))) }, some k_fs)), (sL.2.1, .done)) := by
      rcases sL with ⟨esL, sc, sl⟩
      dsimp only at hslotU ⊢
      subst hslotU
      simp [PrivL15.runHM, hooksCKAUEager, cacheCUEager, queryKey, PrivL15.outerFull,
        eagerCKAKeyImpl, eagerKeyOnlyImpl, drawKeyCKA, PrivL15.consumeKey, c, p]
    have hR_eval :
        PrivL15.runHM (FSAEAD.oracleImpl fs)
          ((hooksFS cka prng fs Δcka ⟨false, none, sR.1.g.epoch P + 1⟩ 0).startSend s₁_epR P
            (sR.1.g.epoch P + 1) (sR.1.g.st P).γ (sR.1.g.st P).root (some coins))
          sR.1.h sR.2 =
        (($ᵗ K : ProbComp K) >>= fun k =>
          pure ((some (c.1, c.2.1, p.1, if true then none else some (fs.initSender k)),
            { ({ sR.1.h with table := [(c.2.2, k)], sessions := [c.2.2] } :
                FSState T Sig K I SS RS E) with
                cache := (Function.update sR.1.h.cache (sR.1.g.epoch P + 1)
                  (some (c.2.1, p.1, k, true))) }), sR.2)) := by
      simp [PrivL15.runHM, hooksFS, rootFS, extOf, isExt, lookupF, htableR, hsessR,
        StateT.run_bind, PrivL15.simulateQ_outerFull_sampleT, bind_map_left, c, p]
    rw [hL_eval, hR_eval, pure_bind, bind_assoc, bind_assoc]
    refine PrivL15.closeBy_bind_right_const fun k => ?_
    simp only [pure_bind]
    let pgL' : PrivL15.EagerState Sig I K :=
      ({ sL_g.2.1 with prf := true, table := [(c.2.2, k_fs)] }, .done)
    exact hcont c.1 c.2.1 (some p.1) k_fs pgL' .done p.1 k true _ _ _
      (hg.advance_core hPs_next hqep bad c.1 c.2.1 (some p.1) k_fs pgL' p.1 k true
        { sR.1.h with table := [(c.2.2, k)], sessions := [c.2.2] }
        (by simp) (fun hne => absurd rfl hne) (by simp) ⟨rfl, rfl, rfl, rfl⟩
        (fun _ => by simp [hosR, FSAEAD.initState, hextR])
        (fun ht => absurd ht (by omega)))
      (hs.advance_sync hg hPs_next bad c.1 c.2.1 c.2.2 (some p.1) k_fs pgL' .done k true
        (some k_fs) { sR.1.h with table := [(c.2.2, k)], sessions := [c.2.2] }
        rfl (fun hne => absurd rfl hne) (fun _ => rfl) (fun hne => absurd rfl hne))
  · have hne : sR.1.g.epoch P + 1 ≠ t := by omega
    have hnot_gt : ¬(t < sR.1.g.epoch P + 1) := by omega
    have hbef := hg.before_t (by rw [hepM]; omega)
    rcases hbef with ⟨hbL, hcorrL, hprngL, hprfL, htableL, _, _,
      htableR, hsessR, hfsTransR, hfsCountR, hfsSCorrR, hextR, k_fs, hslot_g, hosR⟩
    have hL_eval :
        PrivL15.runHM (eagerCKAKeyImpl cka Δcka 0)
          ((hooksCKAUEager cka prng fs Δcka ⟨false, none, t⟩).startSend s₁_epLU P
            (sR.1.g.epoch P + 1) (some (sR.1.g.st P).γ) (sR.1.g.st P).root (some coins))
          sL.1.h sL.2 =
        pure ((some (some c.1, c.2.1, p.1, fs.initSender p.2),
          ({ sL.1.h.1 with cache := (Function.update sL.1.h.1.cache (sR.1.g.epoch P + 1)
              (some (c.2.1, c.2.2))) }, sL.1.h.2)), (sL.2.1, sL.2.2)) := by
      rcases sL.2 with ⟨sc, sl⟩
      simp [PrivL15.runHM, hooksCKAUEager, cacheCUEager, hne, c, p]
    have hR_eval :
        PrivL15.runHM (FSAEAD.oracleImpl fs)
          ((hooksFS cka prng fs Δcka ⟨false, none, t⟩ 0).startSend s₁_epR P
            (sR.1.g.epoch P + 1) (sR.1.g.st P).γ (sR.1.g.st P).root (some coins))
          sR.1.h sR.2 =
        pure ((some (c.1, c.2.1, p.1, if false then none else some (fs.initSender p.2)),
          { sR.1.h with cache := (Function.update sR.1.h.cache (sR.1.g.epoch P + 1)
              (some (c.2.1, p.1, p.2, false))) }), sR.2) := by
      simp [PrivL15.runHM, hooksFS, rootFS, extOf, hnot_gt, hne, c, p]
    rw [hL_eval, hR_eval, pure_bind, pure_bind, pure_bind]
    let pgL' : PrivL15.EagerState Sig I K := ({ sL_g.2.1 with σ := p.1 }, sL_g.2.2)
    exact hcont c.1 c.2.1 none p.2 pgL' sL.2.2 p.1 p.2 false _ _ _
      (hg.advance_core hPs_next hqep bad c.1 c.2.1 none p.2 pgL' p.1 p.2 false sR.1.h
        (by simp [hne]) (fun _ => rfl) (by simp [hlt]) ⟨rfl, rfl, rfl, rfl⟩
        (fun ht => absurd ht hne)
        (fun _ => ⟨hbL, by simpa using hcorrL, hprngL, hprfL, htableL, rfl,
          htableR, hsessR, hfsTransR, hfsCountR, hfsSCorrR, hextR, k_fs, hslot_g, hosR⟩))
      (hs.advance_sync hg hPs_next bad c.1 c.2.1 c.2.2 none p.2 pgL' sL.2.2 p.2 false
        sL.1.h.2 sR.1.h hs.slot_eq (fun _ => rfl) (fun ht => absurd ht hne) (fun _ => rfl))

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType I] [SampleableType K] in
private theorem SyncU15.epMgmt_stay {fs : FSAEADScheme K SS RS (Header T) M E}
    {Δcka qep t : ℕ} {b : Bool} {prng : PRFPRNG KR Sig I K}
    {sL : StateLU Γ T Sig SS RS M E I K}
    {sL_g : PrivL15.StateL Γ T Sig SS RS M E K I}
    {sR : PrivL15.StateR Γ T Sig K I SS RS M E}
    (hg : PrivL15.ActiveInv fs Δcka qep none t b sL_g sR)
    (hs : SyncU15 prng t b sL sL_g sR)
    {P : Party} (hPs_next : P.sendsIn (sR.1.g.epoch P + 1) = false) (bad : Bool) :
    P.sendsIn (sR.1.g.epoch P) = true ∧
    sL.1.g.epMgmt (2 + Δcka) qep P bad = some sL.1.g ∧
    sR.1.g.epMgmt (2 + Δcka) qep P bad = some sR.1.g ∧
    (polUni12 Δcka t).leakDoom sL.1.g sL.1.g = (polUni12 Δcka t).leakDoom sR.1.g sR.1.g := by
  rcases hg.epMgmt_stay hPs_next bad with ⟨hPs, _, hepR, _⟩
  have hqep_le : sR.1.g.epoch P ≤ qep := by
    simpa [GameState.epMgmt, hPs_next] using hepR
  refine ⟨hPs, ?_, hepR, leakDoom_eq_of_fields hs.epoch_eq hs.leaks_eq (polUni12 Δcka t)⟩
  simp [GameState.epMgmt, hs.epoch_eq, hPs_next, hqep_le]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType I] [SampleableType K] in
private theorem SyncU15.epMgmt_advance {fs : FSAEADScheme K SS RS (Header T) M E}
    {Δcka qep t : ℕ} {b : Bool} {prng : PRFPRNG KR Sig I K}
    {sL : StateLU Γ T Sig SS RS M E I K}
    {sL_g : PrivL15.StateL Γ T Sig SS RS M E K I}
    {sR : PrivL15.StateR Γ T Sig K I SS RS M E}
    (hg : PrivL15.ActiveInv fs Δcka qep none t b sL_g sR)
    (hs : SyncU15 prng t b sL sL_g sR)
    {P : Party} (hPs_next : P.sendsIn (sR.1.g.epoch P + 1) = true)
    (hqep : ¬(qep < sR.1.g.epoch P + 1)) (bad : Bool) :
    let t' := sR.1.g.epoch P + 1
    let s₁LU := if bad && !sL.1.g.safeCh (2 + Δcka) P then sL.1.g.leak t' else sL.1.g
    let s₁R := if bad && !sR.1.g.safeCh (2 + Δcka) P then sR.1.g.leak t' else sR.1.g
    let s₁_epLU :=
      { s₁LU with
          epoch := Function.update sL.1.g.epoch P t'
          idx := Function.update sL.1.g.idx P 0 }
    let s₁_epR :=
      { s₁R with
          epoch := Function.update sR.1.g.epoch P t'
          idx := Function.update sR.1.g.idx P 0 }
    sL.1.g.epMgmt (2 + Δcka) qep P bad = some s₁_epLU ∧
    sR.1.g.epMgmt (2 + Δcka) qep P bad = some s₁_epR ∧
    (polUni12 Δcka t).leakDoom sL.1.g s₁_epLU = (polUni12 Δcka t).leakDoom sR.1.g s₁_epR ∧
    s₁_epLU.safeCh (2 + Δcka) P = s₁_epR.safeCh (2 + Δcka) P ∧
    s₁_epLU.epoch P = t' ∧
    s₁_epR.epoch P = t' := by
  intro t' s₁LU s₁R s₁_epLU s₁_epR
  rcases hg.epMgmt_advance hPs_next hqep bad with ⟨_, hepR, _, _, _, hepR_t⟩
  have hsafe := hs.safeCh_eq (2 + Δcka) P
  have hleaks : s₁_epLU.leaks = s₁_epR.leaks := by
    simp only [s₁_epLU, s₁_epR, s₁LU, s₁R, hsafe]
    split_ifs <;> simp [GameState.leak, hs.tL_eq, hs.leaks_eq]
  have htL_ep : s₁_epLU.tL = s₁_epR.tL := by
    simp only [s₁_epLU, s₁_epR, s₁LU, s₁R, hsafe]
    split_ifs <;> simp [GameState.leak, hs.tL_eq]
  have hep_ep : s₁_epLU.epoch = s₁_epR.epoch := by
    simp [s₁_epLU, s₁_epR, hs.epoch_eq]
  refine ⟨?_, hepR, leakDoom_eq_of_fields hs.epoch_eq hleaks (polUni12 Δcka t),
    by simp [GameState.safeCh, htL_ep, hep_ep], by simp [s₁_epLU], hepR_t⟩
  dsimp only [GameState.epMgmt]
  simp only [hs.epoch_eq, hPs_next, ↓reduceIte, hqep, s₁_epLU, s₁LU, t']
  cases (bad && !sL.1.g.safeCh (2 + Δcka) P) <;> simp [GameState.leak, hs.epoch_eq]

omit [SampleableType KR] [SampleableType KC] in
private theorem closeBy_transmitEU (t : ℕ) (b : Bool)
    (P : Party) (m : M) (r : Option CCoins)
    (k : (PrivL15.AdvSpec Γ T Sig SS RS M CCoins E).Range
        (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl (P, m, r)))))) →
      OracleComp (PrivL15.AdvSpec Γ T Sig SS RS M CCoins E) Bool)
    (sL : StateLU Γ T Sig SS RS M E I K)
    (sL_g : PrivL15.StateL Γ T Sig SS RS M E K I)
    (sR : PrivL15.StateR Γ T Sig K I SS RS M E)
    (hg : PrivL15.ActiveInv fs Δcka qep none t b sL_g sR)
    (hs : SyncU15 prng t b sL sL_g sR)
    (ih : ∀ u sL₁ sR₁, Inv15U prng fs Δcka qep t b sL₁ sR₁ →
      CloseByEngU cka prng fs Δcka qep t b (k u) sL₁ sR₁) :
    CloseByEngU cka prng fs Δcka qep t b
      (liftM (OracleSpec.query (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl (P, m, r))))))) >>= k)
      sL sR := by
  cases hPs_next : P.sendsIn (sR.1.g.epoch P + 1)
  · rcases hs.epMgmt_stay hg hPs_next r.isSome with ⟨hPs, hepLU, hepR, hld_eq⟩
    cases hld : (polUni12 Δcka t).leakDoom sR.1.g sR.1.g
    · rcases hg.vSend_stay_transmit cka prng hPs m r sL_g.1.g sR.1.g with
        ⟨c, sL_g', sR', hLg_v, hR_v, hg'⟩
      rcases vSend_stay_coupled cka prng fs Δcka qep t hg hs hPs m m none r false
          sL.1.g sL_g.1.g sR.1.g hLg_v hR_v hg' with ⟨sL', hLU_v, hs'⟩
      have hesL : ({ sL.1 with g := sL.1.g }, sL.2) = sL := rfl
      have hesR : ({ sR.1 with g := sR.1.g }, sR.2) = sR := rfl
      rw [hesL] at hLU_v; rw [hesR] at hR_v
      refine closeBy_of_det_stepU cka prng fs Δcka qep t b _ k
        sL sL' sR sR' (some c) (some c) ?_ ?_ ih (Or.inr ⟨rfl, Or.inr ⟨sL_g', hg', hs'⟩⟩)
      · rw [PrivL15.runEM_implE_transmitE _ _ _ _ _ _ _ P m r sL hs.abortL hs.winL]
        simp [hepLU, hld_eq, hld, hLU_v]
      · rw [PrivL15.runEM_implE_transmitE _ _ _ _ _ _ _ P m r sR hg.abortR hg.winR]
        simp [hepR, hld, hR_v]
    · refine closeBy_of_det_stepU cka prng fs Δcka qep t b _ k
        sL ({ sL.1 with abort := true }, sL.2)
        sR ({ sR.1 with abort := true }, sR.2)
        none none ?_ ?_ ih (Or.inr ⟨rfl, Or.inl ⟨rfl, rfl, hg.winFS, hg.bFS⟩⟩)
      · rw [PrivL15.runEM_implE_transmitE _ _ _ _ _ _ _ P m r sL hs.abortL hs.winL]
        simp [hepLU, hld_eq, hld]
      · rw [PrivL15.runEM_implE_transmitE _ _ _ _ _ _ _ P m r sR hg.abortR hg.winR]
        simp [hepR, hld]
  · by_cases hqep : qep < sR.1.g.epoch P + 1
    · refine closeBy_of_det_stepU cka prng fs Δcka qep t b _ k
        sL sL sR sR none none ?_ ?_ ih (Or.inr ⟨rfl, Or.inr ⟨sL_g, hg, hs⟩⟩)
      · rw [PrivL15.runEM_implE_transmitE _ _ _ _ _ _ _ P m r sL hs.abortL hs.winL]
        simp [GameState.epMgmt, hs.epoch_eq, hPs_next, hqep]
      · rw [PrivL15.runEM_implE_transmitE _ _ _ _ _ _ _ P m r sR hg.abortR hg.winR]
        simp [GameState.epMgmt, hPs_next, hqep]
    · rcases hs.epMgmt_advance hg hPs_next hqep r.isSome with
        ⟨hepLU, hepR, hld_eq, _, _, _⟩
      set s₁_epLU :=
        { (if r.isSome && !sL.1.g.safeCh (2 + Δcka) P then sL.1.g.leak (sR.1.g.epoch P + 1)
           else sL.1.g) with
            epoch := Function.update sL.1.g.epoch P (sR.1.g.epoch P + 1)
            idx := Function.update sL.1.g.idx P 0 }
      set s₁_epR :=
        { (if r.isSome && !sR.1.g.safeCh (2 + Δcka) P then sR.1.g.leak (sR.1.g.epoch P + 1)
           else sR.1.g) with
            epoch := Function.update sR.1.g.epoch P (sR.1.g.epoch P + 1)
            idx := Function.update sR.1.g.idx P 0 }
      cases hld : (polUni12 Δcka t).leakDoom sR.1.g s₁_epR
      · unfold CloseByEngU
        rw [evalEngU_query_bind, evalEngMU_query_bind, evalEngL_liftM_query_bind]
        rw [PrivL15.runEM_implE_transmitE _ _ _ _ _ _ _ P m r sL hs.abortL hs.winL,
          PrivL15.runEM_implE_transmitE _ _ _ _ _ _ _ P m r sR hg.abortR hg.winR]
        simp only [hepLU, hepR, hld_eq, hld, Bool.false_eq_true, ↓reduceIte]
        have hst_u : s₁_epLU.st P = sL.1.g.st P := by
          cases hb : (r.isSome && !sL.1.g.safeCh (2 + Δcka) P) <;>
            simp [s₁_epLU, hb, GameState.leak]
        have hst_r : s₁_epR.st P = sR.1.g.st P := by
          cases hb : (r.isSome && !sR.1.g.safeCh (2 + Δcka) P) <;>
            simp [s₁_epR, hb, GameState.leak]
        have hPs_next_u : P.sendsIn ((s₁_epLU.st P).tcur + 1) = true := by
          rw [hst_u, hs.tcurL P]; exact hPs_next
        have hPs_next_r : P.sendsIn ((s₁_epR.st P).tcur + 1) = true := by
          rw [hst_r, hg.tcurR P]; exact hPs_next
        have hid_u : (s₁_epLU.st P).id = P := by
          rw [hst_u]; exact hs.idL P
        have hid_r : (s₁_epR.st P).id = P := by
          rw [hst_r]; exact hg.idR P
        rw [PrivL15.runEM_vSend_advance _ _ _ _ P m none r false sL hid_u hPs_next_u
              (fun _ => rfl),
          PrivL15.runEM_vSend_advance _ _ _ _ P m none r false sR hid_r hPs_next_r
              (fun _ => rfl)]
        simp only [hst_u, hst_r, hs.tcurL P, hg.tcurR P, hs.γ_eq P, hs.root_eq P, bind_assoc]
        refine closeBy_startSendU cka prng fs Δcka qep t hg hs hPs_next hqep r.isSome r
          s₁_epLU s₁_epR _ _ _
          fun γ' T' σL' kL pgL' slU' σR' kR ext hLU' hL' hR' hg_mid hs_mid => ?_
        dsimp only
        have hgMidU_eq : ∀ st₁ : Engine.VP (Option Γ) T Sig SS RS,
            { s₁_epLU with st := Function.update s₁_epLU.st P st₁ } =
            { (if r.isSome && !sL.1.g.safeCh (2 + Δcka) P then sL.1.g.leak (sR.1.g.epoch P + 1)
               else sL.1.g) with
                st := Function.update sL.1.g.st P st₁
                epoch := Function.update sL.1.g.epoch P (sR.1.g.epoch P + 1)
                idx := Function.update sL.1.g.idx P 0 } := by
          intro st₁
          cases hb : (r.isSome && !sL.1.g.safeCh (2 + Δcka) P) <;>
            simp [s₁_epLU, hb, GameState.leak]
        have hgMidR_eq : ∀ st₁ : Engine.VP Γ T Sig (Option SS) (Option RS),
            { s₁_epR with st := Function.update s₁_epR.st P st₁ } =
            { (if r.isSome && !sR.1.g.safeCh (2 + Δcka) P then sR.1.g.leak (sR.1.g.epoch P + 1)
               else sR.1.g) with
                st := Function.update sR.1.g.st P st₁
                epoch := Function.update sR.1.g.epoch P (sR.1.g.epoch P + 1)
                idx := Function.update sR.1.g.idx P 0 } := by
          intro st₁
          cases hb : (r.isSome && !sR.1.g.safeCh (2 + Δcka) P) <;>
            simp [s₁_epR, hb, GameState.leak]
        rw [hgMidU_eq, hgMidR_eq]
        have hPs_mid : P.sendsIn (({ sR.1 with
            g := { (if r.isSome && !sR.1.g.safeCh (2 + Δcka) P then sR.1.g.leak (sR.1.g.epoch P + 1)
                    else sR.1.g) with
                      st := Function.update sR.1.g.st P
                        { sR.1.g.st P with
                            root := σR',
                            vS := some (if ext then none else some (fs.initSender kR)),
                            γ := γ', curCkaMsg := some T', tcur := sR.1.g.epoch P + 1 }
                      epoch := Function.update sR.1.g.epoch P (sR.1.g.epoch P + 1)
                      idx := Function.update sR.1.g.idx P 0 },
            h := hR' }, sR.2).1.g.epoch P) = true := by
          simpa using hPs_next
        rcases hg_mid.vSend_stay_transmit cka prng hPs_mid m r sL_g.1.g sR.1.g with
          ⟨c, sL_g', sR', hLg_v, hR_v, hg'⟩
        rcases vSend_stay_coupled cka prng fs Δcka qep t hg_mid hs_mid hPs_mid m m none r false
            sL.1.g sL_g.1.g sR.1.g hLg_v hR_v hg' with ⟨sL', hLU_v, hs'⟩
        rw [hLU_v, hR_v, pure_bind, pure_bind, pure_bind]
        exact ih (some c) sL' sR' (Or.inr ⟨sL_g', hg', hs'⟩)
      · refine closeBy_of_det_stepU cka prng fs Δcka qep t b _ k
          sL ({ sL.1 with abort := true }, sL.2)
          sR ({ sR.1 with abort := true }, sR.2)
          none none ?_ ?_ ih (Or.inr ⟨rfl, Or.inl ⟨rfl, rfl, hg.winFS, hg.bFS⟩⟩)
        · rw [PrivL15.runEM_implE_transmitE _ _ _ _ _ _ _ P m r sL hs.abortL hs.winL]
          simp [hepLU, hld_eq, hld]
        · rw [PrivL15.runEM_implE_transmitE _ _ _ _ _ _ _ P m r sR hg.abortR hg.winR]
          simp [hepR, hld]

omit [SampleableType KR] [SampleableType KC] in
private theorem closeBy_challEU (t : ℕ) (b : Bool)
    (P : Party) (m₀ m₁ : M) (r : Option CCoins)
    (k : (PrivL15.AdvSpec Γ T Sig SS RS M CCoins E).Range
        (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inr (P, m₀, m₁, r)))))) →
      OracleComp (PrivL15.AdvSpec Γ T Sig SS RS M CCoins E) Bool)
    (sL : StateLU Γ T Sig SS RS M E I K)
    (sL_g : PrivL15.StateL Γ T Sig SS RS M E K I)
    (sR : PrivL15.StateR Γ T Sig K I SS RS M E)
    (hg : PrivL15.ActiveInv fs Δcka qep none t b sL_g sR)
    (hs : SyncU15 prng t b sL sL_g sR)
    (ih : ∀ u sL₁ sR₁, Inv15U prng fs Δcka qep t b sL₁ sR₁ →
      CloseByEngU cka prng fs Δcka qep t b (k u) sL₁ sR₁) :
    CloseByEngU cka prng fs Δcka qep t b
      (liftM (OracleSpec.query (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inr (P, m₀, m₁, r))))))) >>= k)
      sL sR := by
  cases hPs_next : P.sendsIn (sR.1.g.epoch P + 1)
  · rcases hs.epMgmt_stay hg hPs_next r.isSome with ⟨hPs, hepLU, hepR, hld_eq⟩
    have hsafe_eq := hs.safeCh_eq (2 + Δcka) P
    cases hguard : (!(sR.1.g.safeCh (2 + Δcka) P) ||
        !((Config.priv (Msg := M) t).challAllowedIn (sR.1.g.epoch P)))
    · simp only [Bool.or_eq_false_iff, Bool.not_eq_false', Config.priv,
        beq_iff_eq] at hguard
      rcases hguard with ⟨hsafe, ht_eq⟩
      cases hld : (polUni12 Δcka t).leakDoom sR.1.g sR.1.g
      · rcases hg.vSend_stay_chall cka prng hPs ht_eq hsafe m₀ m₁ r sL_g.1.g sR.1.g with
          ⟨c, sL_g', sR', hLg_v, hR_v, hg'⟩
        rcases vSend_stay_coupled cka prng fs Δcka qep t hg hs hPs
            (if b then m₁ else m₀) m₀ (some (m₀, m₁)) r true
            sL.1.g sL_g.1.g sR.1.g hLg_v hR_v hg' with ⟨sL', hLU_v, hs'⟩
        have hesL : ({ sL.1 with g := sL.1.g }, sL.2) = sL := rfl
        have hesR : ({ sR.1 with g := sR.1.g }, sR.2) = sR := rfl
        rw [hesL] at hLU_v; rw [hesR] at hR_v
        refine closeBy_of_det_stepU cka prng fs Δcka qep t b _ k
          sL sL' sR sR' (some c) (some c) ?_ ?_ ih (Or.inr ⟨rfl, Or.inr ⟨sL_g', hg', hs'⟩⟩)
        · rw [PrivL15.runEM_implE_challE _ _ _ _ _ _ _ P m₀ m₁ r sL hs.abortL hs.winL]
          simp [hepLU, hsafe_eq, hsafe, hs.epoch_eq, ht_eq, Config.priv,
            hld_eq, hld, hs.bL, hLU_v]
        · rw [PrivL15.runEM_implE_challE _ _ _ _ _ _ _ P m₀ m₁ r sR hg.abortR hg.winR]
          simp [hepR, hsafe, ht_eq, Config.priv, hld, hg.bR, hR_v]
      · refine closeBy_of_det_stepU cka prng fs Δcka qep t b _ k
          sL ({ sL.1 with abort := true }, sL.2)
          sR ({ sR.1 with abort := true }, sR.2)
          none none ?_ ?_ ih (Or.inr ⟨rfl, Or.inl ⟨rfl, rfl, hg.winFS, hg.bFS⟩⟩)
        · rw [PrivL15.runEM_implE_challE _ _ _ _ _ _ _ P m₀ m₁ r sL hs.abortL hs.winL]
          simp [hepLU, hsafe_eq, hsafe, hs.epoch_eq, ht_eq, Config.priv,
            hld_eq, hld]
        · rw [PrivL15.runEM_implE_challE _ _ _ _ _ _ _ P m₀ m₁ r sR hg.abortR hg.winR]
          simp [hepR, hsafe, ht_eq, Config.priv, hld]
    · refine closeBy_of_det_stepU cka prng fs Δcka qep t b _ k
        sL sL sR sR none none ?_ ?_ ih (Or.inr ⟨rfl, Or.inr ⟨sL_g, hg, hs⟩⟩)
      · rw [PrivL15.runEM_implE_challE _ _ _ _ _ _ _ P m₀ m₁ r sL hs.abortL hs.winL]
        simp [hepLU, hsafe_eq, hs.epoch_eq, hguard, -Bool.or_eq_true]
      · rw [PrivL15.runEM_implE_challE _ _ _ _ _ _ _ P m₀ m₁ r sR hg.abortR hg.winR]
        simp [hepR, hguard, -Bool.or_eq_true]
  · by_cases hqep : qep < sR.1.g.epoch P + 1
    · refine closeBy_of_det_stepU cka prng fs Δcka qep t b _ k
        sL sL sR sR none none ?_ ?_ ih (Or.inr ⟨rfl, Or.inr ⟨sL_g, hg, hs⟩⟩)
      · rw [PrivL15.runEM_implE_challE _ _ _ _ _ _ _ P m₀ m₁ r sL hs.abortL hs.winL]
        simp [GameState.epMgmt, hs.epoch_eq, hPs_next, hqep]
      · rw [PrivL15.runEM_implE_challE _ _ _ _ _ _ _ P m₀ m₁ r sR hg.abortR hg.winR]
        simp [GameState.epMgmt, hPs_next, hqep]
    · rcases hs.epMgmt_advance hg hPs_next hqep r.isSome with
        ⟨hepLU, hepR, hld_eq, hsafe_ep, hepLU_t, hepR_t⟩
      set s₁_epLU :=
        { (if r.isSome && !sL.1.g.safeCh (2 + Δcka) P then sL.1.g.leak (sR.1.g.epoch P + 1)
           else sL.1.g) with
            epoch := Function.update sL.1.g.epoch P (sR.1.g.epoch P + 1)
            idx := Function.update sL.1.g.idx P 0 }
      set s₁_epR :=
        { (if r.isSome && !sR.1.g.safeCh (2 + Δcka) P then sR.1.g.leak (sR.1.g.epoch P + 1)
           else sR.1.g) with
            epoch := Function.update sR.1.g.epoch P (sR.1.g.epoch P + 1)
            idx := Function.update sR.1.g.idx P 0 }
      cases hguard : (!(s₁_epR.safeCh (2 + Δcka) P) ||
          !((Config.priv (Msg := M) t).challAllowedIn (s₁_epR.epoch P)))
      · simp only [Bool.or_eq_false_iff, Bool.not_eq_false', Config.priv,
          beq_iff_eq] at hguard
        rcases hguard with ⟨hsafe, ht_eq⟩
        cases hld : (polUni12 Δcka t).leakDoom sR.1.g s₁_epR
        · unfold CloseByEngU
          rw [evalEngU_query_bind, evalEngMU_query_bind, evalEngL_liftM_query_bind]
          rw [PrivL15.runEM_implE_challE _ _ _ _ _ _ _ P m₀ m₁ r sL hs.abortL hs.winL,
            PrivL15.runEM_implE_challE _ _ _ _ _ _ _ P m₀ m₁ r sR hg.abortR hg.winR]
          have hguardL : (!(s₁_epLU.safeCh (2 + Δcka) P) ||
              !((Config.priv (Msg := M) t).challAllowedIn (s₁_epLU.epoch P))) = false := by
            simp [hsafe_ep, hsafe, hepLU_t, ← hepR_t, ht_eq, Config.priv]
          have hguardR : (!(s₁_epR.safeCh (2 + Δcka) P) ||
              !((Config.priv (Msg := M) t).challAllowedIn (s₁_epR.epoch P))) = false := by
            simp [hsafe, ht_eq, Config.priv]
          simp only [hepLU, hepR, hguardL, hguardR, hld_eq, hld, Bool.false_eq_true, ↓reduceIte,
            hs.bL, hg.bR]
          have hst_u : s₁_epLU.st P = sL.1.g.st P := by
            cases hb : (r.isSome && !sL.1.g.safeCh (2 + Δcka) P) <;>
              simp [s₁_epLU, hb, GameState.leak]
          have hst_r : s₁_epR.st P = sR.1.g.st P := by
            cases hb : (r.isSome && !sR.1.g.safeCh (2 + Δcka) P) <;>
              simp [s₁_epR, hb, GameState.leak]
          have hPs_next_u : P.sendsIn ((s₁_epLU.st P).tcur + 1) = true := by
            rw [hst_u, hs.tcurL P]; exact hPs_next
          have hPs_next_r : P.sendsIn ((s₁_epR.st P).tcur + 1) = true := by
            rw [hst_r, hg.tcurR P]; exact hPs_next
          have hid_u : (s₁_epLU.st P).id = P := by
            rw [hst_u]; exact hs.idL P
          have hid_r : (s₁_epR.st P).id = P := by
            rw [hst_r]; exact hg.idR P
          rw [PrivL15.runEM_vSend_advance _ _ _ _ P (if b then m₁ else m₀) (some (m₀, m₁)) r true
                sL hid_u hPs_next_u (fun _ => rfl),
            PrivL15.runEM_vSend_advance _ _ _ _ P m₀ (some (m₀, m₁)) r true
                sR hid_r hPs_next_r (fun _ => rfl)]
          simp only [hst_u, hst_r, hs.tcurL P, hg.tcurR P, hs.γ_eq P, hs.root_eq P, bind_assoc]
          refine closeBy_startSendU cka prng fs Δcka qep t hg hs hPs_next hqep r.isSome r
            s₁_epLU s₁_epR _ _ _
            fun γ' T' σL' kL pgL' slU' σR' kR ext hLU' hL' hR' hg_mid hs_mid => ?_
          dsimp only
          have hgMidU_eq : ∀ st₁ : Engine.VP (Option Γ) T Sig SS RS,
              { s₁_epLU with st := Function.update s₁_epLU.st P st₁ } =
              { (if r.isSome && !sL.1.g.safeCh (2 + Δcka) P then sL.1.g.leak (sR.1.g.epoch P + 1)
                 else sL.1.g) with
                  st := Function.update sL.1.g.st P st₁
                  epoch := Function.update sL.1.g.epoch P (sR.1.g.epoch P + 1)
                  idx := Function.update sL.1.g.idx P 0 } := by
            intro st₁
            cases hb : (r.isSome && !sL.1.g.safeCh (2 + Δcka) P) <;>
              simp [s₁_epLU, hb, GameState.leak]
          have hgMidR_eq : ∀ st₁ : Engine.VP Γ T Sig (Option SS) (Option RS),
              { s₁_epR with st := Function.update s₁_epR.st P st₁ } =
              { (if r.isSome && !sR.1.g.safeCh (2 + Δcka) P then sR.1.g.leak (sR.1.g.epoch P + 1)
                 else sR.1.g) with
                  st := Function.update sR.1.g.st P st₁
                  epoch := Function.update sR.1.g.epoch P (sR.1.g.epoch P + 1)
                  idx := Function.update sR.1.g.idx P 0 } := by
            intro st₁
            cases hb : (r.isSome && !sR.1.g.safeCh (2 + Δcka) P) <;>
              simp [s₁_epR, hb, GameState.leak]
          rw [hgMidU_eq, hgMidR_eq]
          set gMidR :=
            { (if r.isSome && !sR.1.g.safeCh (2 + Δcka) P then sR.1.g.leak (sR.1.g.epoch P + 1)
               else sR.1.g) with
                st := Function.update sR.1.g.st P
                  { sR.1.g.st P with
                      root := σR',
                      vS := some (if ext then none else some (fs.initSender kR)),
                      γ := γ', curCkaMsg := some T', tcur := sR.1.g.epoch P + 1 }
                epoch := Function.update sR.1.g.epoch P (sR.1.g.epoch P + 1)
                idx := Function.update sR.1.g.idx P 0 }
          have hPs_mid : P.sendsIn (gMidR.epoch P) = true := by simpa [gMidR] using hPs_next
          have ht_mid : gMidR.epoch P = t := by
            simp only [gMidR, Function.update_self]
            exact hepR_t ▸ ht_eq
          have hsafe_mid : gMidR.safeCh (2 + Δcka) P = true := by
            simpa [GameState.safeCh, gMidR, s₁_epR] using hsafe
          rcases hg_mid.vSend_stay_chall cka prng hPs_mid ht_mid hsafe_mid m₀ m₁ r
              sL_g.1.g sR.1.g with ⟨c, sL_g', sR', hLg_v, hR_v, hg'⟩
          rcases vSend_stay_coupled cka prng fs Δcka qep t hg_mid hs_mid hPs_mid
              (if b then m₁ else m₀) m₀ (some (m₀, m₁)) r true
              sL.1.g sL_g.1.g sR.1.g hLg_v hR_v hg' with ⟨sL', hLU_v, hs'⟩
          rw [hLU_v, hR_v, pure_bind, pure_bind, pure_bind]
          exact ih (some c) sL' sR' (Or.inr ⟨sL_g', hg', hs'⟩)
        · refine closeBy_of_det_stepU cka prng fs Δcka qep t b _ k
            sL ({ sL.1 with abort := true }, sL.2)
            sR ({ sR.1 with abort := true }, sR.2)
            none none ?_ ?_ ih (Or.inr ⟨rfl, Or.inl ⟨rfl, rfl, hg.winFS, hg.bFS⟩⟩)
          · rw [PrivL15.runEM_implE_challE _ _ _ _ _ _ _ P m₀ m₁ r sL hs.abortL hs.winL]
            simp [hepLU, hsafe_ep, hsafe, hepLU_t, ← hepR_t, ht_eq, Config.priv, hld_eq, hld]
          · rw [PrivL15.runEM_implE_challE _ _ _ _ _ _ _ P m₀ m₁ r sR hg.abortR hg.winR]
            simp [hepR, hsafe, ht_eq, Config.priv, hld]
      · refine closeBy_of_det_stepU cka prng fs Δcka qep t b _ k
          sL sL sR sR none none ?_ ?_ ih (Or.inr ⟨rfl, Or.inr ⟨sL_g, hg, hs⟩⟩)
        · rw [PrivL15.runEM_implE_challE _ _ _ _ _ _ _ P m₀ m₁ r sL hs.abortL hs.winL]
          simp [hepLU, hsafe_ep, hepLU_t, ← hepR_t, hguard, -Bool.or_eq_true]
        · rw [PrivL15.runEM_implE_challE _ _ _ _ _ _ _ P m₀ m₁ r sR hg.abortR hg.winR]
          simp [hepR, hguard, -Bool.or_eq_true]

/-! ### Section 5: Induction over `oa`, `init` coupling (`0 < t`), and main theorem -/

omit [SampleableType KR] [SampleableType KC] in
private theorem closeBy_evalEngU (t : ℕ) (b : Bool)
    (oa : OracleComp (PrivL15.AdvSpec Γ T Sig SS RS M CCoins E) Bool) :
    ∀ (sL : StateLU Γ T Sig SS RS M E I K)
      (sR : PrivL15.StateR Γ T Sig K I SS RS M E),
      Inv15U prng fs Δcka qep t b sL sR →
      CloseByEngU cka prng fs Δcka qep t b oa sL sR := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro sL sR hInv
    exact closeBy_evalEngU_pure cka prng fs Δcka qep t b a sL sR hInv
  | query_bind q k ih =>
    intro sL sR hInv
    rcases q with n | q
    · exact closeBy_coinsEU cka prng fs Δcka qep t b n k sL sR hInv ih
    · rcases hInv with hab | ⟨sL_g, hg, hs⟩
      · exact closeBy_sm_of_abortInvU cka prng fs Δcka qep t b q k sL sR hab ih
      · rcases q with ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
        · exact closeBy_transmitEU cka prng fs Δcka qep t b P m r k sL sL_g sR hg hs ih
        · exact closeBy_challEU cka prng fs Δcka qep t b P m₀ m₁ r k sL sL_g sR hg hs ih
        · exact closeBy_deliverEU cka prng fs Δcka qep t b P c k sL sL_g sR hg hs ih
        · exact closeBy_injectEU cka prng fs Δcka qep t b P c k sL sL_g sR hg hs ih
        · exact closeBy_corrEU cka prng fs Δcka qep t b P k sL sL_g sR hg hs ih

private theorem closeBy_bind_left_const {α : Type} [SampleableType α]
    {cR : α → ProbComp Bool} {cM cL : ProbComp Bool}
    (h : ∀ a, PrivL15.CloseBy (cR a) cM cL) :
    PrivL15.CloseBy (($ᵗ α : ProbComp α) >>= cR) cM cL := by
  have h' : PrivL15.CloseBy (($ᵗ α : ProbComp α) >>= cR)
      (($ᵗ α : ProbComp α) >>= fun _ => cM)
      (($ᵗ α : ProbComp α) >>= fun _ => cL) :=
    PrivL15.closeBy_bind ($ᵗ α) h
  unfold PrivL15.CloseBy at h' ⊢
  simpa only [OracleComp.evalDist_bind_const] using h'

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E] in
private theorem runHM_initCKAUEager_eq (t : ℕ)
    (osL : CKAEagerState Γ T K) :
    PrivL15.runHM (eagerCKAKeyImpl cka Δcka 0)
      (initCKAUEager cka prng fs lam ⟨false, none, t⟩) ({}, none) osL =
    (($ᵗ KR : ProbComp KR) >>= fun kr =>
      ($ᵗ KC : ProbComp KC) >>= fun kc =>
        let out := prng.up (prng.init kr) lam
        pure ((some (mkParties (T := T) (some (cka.initA kc)) (some (cka.initB kc))
          out.1 (fs.initSender out.2) (fs.initReceiver out.2)), ({}, none)), osL)) := by
  have hLift : ∀ {α : Type} (x : CKA.AdversaryComp Γ CCoins T I α)
      (os : CKAEagerState Γ T K),
      (simulateQ (PrivL15.outerFull (eagerCKAKeyImpl cka Δcka 0))
        (simulateQ (liftCKAImpl (Γ := Γ) (CCoins := CCoins) (T := T) (I := I) (K := K)) x)).run os =
      (fun r => (r.1, (r.2, os.2))) <$>
        (simulateQ (PrivL15.outerFull (CKA.oracleImpl cka Δcka 0)) x).run os.1 := by
    intro α x
    induction x using OracleComp.inductionOn with
    | pure a =>
      rintro ⟨g, sl⟩
      simp
    | query_bind q k ih =>
      rintro ⟨g, sl⟩
      rcases q with n | q
      · simp [liftCKAImpl, PrivL15.outerFull, bind_map_left, map_bind]
        exact bind_congr fun u => ih u (g, sl)
      · simp [liftCKAImpl, PrivL15.outerFull, eagerCKAKeyImpl, liftCKAM, bind_map_left, map_bind]
        exact bind_congr fun ⟨a, g'⟩ => ih a (g', sl)
  unfold PrivL15.runHM initCKAUEager liftCKAComp
  rw [StateT.run_mk, hLift]
  change (fun r => (r.1, r.2, osL.2)) <$>
    (simulateQ (PrivL15.outerFull (CKA.oracleImpl cka Δcka 0))
      ((initCKA cka prng fs lam ⟨false, none, t⟩).run {} >>= fun x =>
        pure (x.1, (x.2, none)))).run osL.1 = _
  simp [initCKA, StateT.run_bind, simulateQ_bind, PrivL15.simulateQ_outerFull_sampleT,
    bind_map_left, map_bind]

/-- Unified Stage-2 Lemma 15 (`0 < t`): the `boolDist` between
`CKA.branch cka Δcka 0 false (redCKAPrivUUniAll ...)` and `FSAEAD.game fs (redFSPrivUni ...)` is at
most `FSAEAD.advantage fs (redFSPrivUniCoin ...)`. -/
theorem boolDist_redCKAPrivUUniAll_redFSPrivUni_le
    (t : ℕ) (ht : 0 < t) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    𝒟[CKA.branch cka Δcka 0 false
        (redCKAPrivUUniAll cka prng fs lam Δcka qep t A)].boolDist
      𝒟[FSAEAD.game fs (redFSPrivUni cka prng fs lam Δcka qep t A)] ≤
    FSAEAD.advantage fs (redFSPrivUniCoin cka prng fs lam Δcka qep t A) := by
  rw [evalDist_branch_redCKAPrivUUniAll_eq_eager, evalDist_game_redFSPrivUni,
    advantage_redFSPrivUniCoin]
  refine PrivL15.boolDist_le_of_closeBy ?_
  refine PrivL15.closeBy_bind ($ᵗ Bool) fun b => ?_
  refine PrivL15.closeBy_bind ($ᵗ K) fun k_fs => ?_
  refine closeBy_bind_left_const fun kc₀ => ?_
  rw [runHM_initCKAUEager_eq, PrivL15.runHM_initFS_eq, bind_assoc, bind_assoc, bind_assoc]
  refine PrivL15.closeBy_bind ($ᵗ KR) fun kr => ?_
  rw [bind_assoc, bind_assoc, bind_assoc]
  refine PrivL15.closeBy_bind ($ᵗ KC) fun kc => ?_
  set out := prng.up (prng.init kr) lam
  have hnot_gt : ¬(t < 0) := by omega
  have hne0 : 0 ≠ t := by omega
  have hR_body :
      PrivL15.runHM (FSAEAD.oracleImpl fs)
        (PrivL15.initFSBody cka prng fs lam ⟨false, none, t⟩ 0 kr kc)
        ({} : FSState T Sig K I SS RS E) (FSAEAD.initState fs k_fs b) =
      pure ((some (mkParties (T := T) (cka.initA kc) (cka.initB kc) out.1
        (if false then none else some (fs.initSender out.2))
        (if false then none else some (fs.initReceiver out.2))),
        ({} : FSState T Sig K I SS RS E)), FSAEAD.initState fs k_fs b) := by
    simp [PrivL15.runHM, PrivL15.initFSBody, rootFS, extOf, hnot_gt, hne0, out]
  rw [hR_body]
  simp only [pure_bind, evalAfterInitU, evalAfterInitMU, PrivL15.evalAfterInitCoin]
  let pgL : PrivL15.EagerState Sig I K :=
    ({ σ := out.1, b := true, corr := false, prng := false, prf := false, table := [] },
      .ready k_fs)
  have hg₀ := PrivL15.ActiveInv.init_mkParties (fs := fs) (Δcka := Δcka) (qep := qep)
    (tL := none) (t := t) (b := b)
    (cka.initA kc) (cka.initB kc) none out.2 out.1 out.2 false pgL
    ({} : FSState T Sig K I SS RS E) k_fs
    (by simp; omega) (fun _ => rfl) (by simp [ht]) rfl ⟨rfl, rfl, rfl, rfl⟩
    (fun ht0 => absurd ht0.symm hne0)
    (fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
  have hs₀ : SyncU15 prng t b
      ({ g := { st := fun P => match P with
                  | .A => (mkParties (T := T) (some (cka.initA kc)) (some (cka.initB kc))
                      out.1 (fs.initSender out.2) (fs.initReceiver out.2)).1
                  | .B => (mkParties (T := T) (some (cka.initA kc)) (some (cka.initB kc))
                      out.1 (fs.initSender out.2) (fs.initReceiver out.2)).2
                b := b },
         h := ({}, none) },
       (CKA.initState cka kc₀ false, .ready k_fs))
      ({ g := { st := fun P => match P with
                  | .A => (mkParties (T := T) (cka.initA kc) (cka.initB kc)
                      (none : Option Sig) (fs.initSender out.2) (fs.initReceiver out.2)).1
                  | .B => (mkParties (T := T) (cka.initA kc) (cka.initB kc)
                      (none : Option Sig) (fs.initSender out.2) (fs.initReceiver out.2)).2
                b := b },
         h := {} }, pgL)
      ({ g := { st := fun P => match P with
                  | .A => (mkParties (T := T) (cka.initA kc) (cka.initB kc) out.1
                      (if false then none else some (fs.initSender out.2))
                      (if false then none else some (fs.initReceiver out.2))).1
                  | .B => (mkParties (T := T) (cka.initA kc) (cka.initB kc) out.1
                      (if false then none else some (fs.initSender out.2))
                      (if false then none else some (fs.initReceiver out.2))).2
                b := false },
         h := {} },
       FSAEAD.initState fs k_fs b) :=
    { abortL := rfl
      winL := rfl
      bL := rfl
      epoch_eq := rfl
      idx_eq := rfl
      tL_eq := rfl
      chall_eq := rfl
      comp_eq := rfl
      maxAcc_eq := rfl
      leaks_eq := rfl
      corrs_eq := rfl
      trans_eq := rfl
      idL := fun P => by cases P <;> rfl
      tcurL := fun P => by cases P <;> rfl
      γ_eq := fun P => by cases P <;> rfl
      Tcur_eq := fun P => by cases P <;> rfl
      root_eq := fun P => by cases P <;> rfl
      vS_eq := fun P => by cases P <;> rfl
      vR_eq := fun P => by cases P <;> rfl
      same_ep_root := fun _ => rfl
      cacheL_none := fun _ _ => rfl
      cache_pending := fun _ _ _ _ _ _ hc => nomatch hc
      kOpt_eq := fun _ _ _ hc => nomatch hc
      slot_eq := rfl }
  exact closeBy_evalEngU cka prng fs Δcka qep t b A _ _ (Or.inr ⟨_, hg₀, hs₀⟩)

end Stage2SwitchBack

end CryptoGames.SM.Construction
