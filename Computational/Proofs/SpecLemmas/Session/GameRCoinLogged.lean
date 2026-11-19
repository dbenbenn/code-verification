/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Session.StatementSession
public import ToMathlib.MeasureTheory.Measure.Bool
import Mathlib.Tactic.Ring
import VCVio.OracleComp.SimSemantics.SimulateQ
import VCVio.EvalDist.Monad.Basic
import VCVio.EvalDist.ProbabilityBounds
import VCVio.EvalDist.MeasureTVDist.Event
import VCVio.OracleComp.EvalDist.Measure

public section

set_option autoImplicit false

/-!
# Faithfulness and identical-until-bad lemmas for `gameRCoinLogged`

**Checked by Lean.**

Proves `GameRCoinLoggedFaithful` (forgetting the `WriterT` send-coin log of `gameRCoinLogged`
equals `SM.gameR`) together with prefix-closed online identical-until-bad, halted-game, and
`boolDist`/`boolBias` transfer lemmas for `smSchemeCoinLogged` and `sessionKemFailProb`.
-/

namespace Computational.Proofs.SpecLemmas.Session.GameRCoinLogged

open MeasureTheory (Measure IsProbabilityMeasure lintegral_congr lintegral_indicator)
open OracleComp OracleSpec
open scoped ENNReal
open CryptoGames (Party SMSchemeR)
open CryptoGames.CBC (Plain)
open CryptoGames.LibsignalSession (Crypto GhostState IdentityKey PublicKey)
open CryptoGames.SM (Adversary ConfigR GameState RecvResult challImpl challR corrR deliverR
  gameR initState injectR oracleImplR runR samIfNec spec transmitImpl transmitR)
open CryptoVerification.E2E (Bytes GameRCoinLoggedFaithful SMSchemeRM challRM
  configRefuseEarlyBobCorr deliverRM gameRCoinLogged injectRM liftStateT oracleImplRM
  paramsIdsWithSpqr sessionKemFailProb sessionSchemeFixedSpk smSchemeCoinLogged transmitRM)
open CryptoVerification.LibsignalSpqrV1 (MlKem coinBytes coinBytes_length
  spqrV1SessionUniformCoins)

local instance instLawfulMonadWriterTListCoin {Coins : Type} {M : Type → Type}
    [Monad M] [LawfulMonad M] : LawfulMonad (WriterT (List Coins) M) :=
  LawfulMonad.mk'
    (id_map := fun _ => by ext; simp)
    (pure_bind := fun _ _ => by ext; simp)
    (bind_assoc := fun _ _ _ => by ext; simp)
    (bind_pure_comp := fun _ _ => by ext; simp)

/-! ## Forgetful homomorphism and `GameRCoinLoggedFaithful` -/

@[expose] def forgetCoinW {Coins α : Type} (m : WriterT (List Coins) ProbComp α) : ProbComp α :=
  Prod.fst <$> m.run

@[simp] theorem forgetCoinW_pure {Coins α : Type} (a : α) :
    forgetCoinW (Coins := Coins) (pure a) = pure a := by simp [forgetCoinW]

@[simp] theorem forgetCoinW_map {Coins α β : Type} (f : α → β)
    (m : WriterT (List Coins) ProbComp α) :
    forgetCoinW (f <$> m) = f <$> forgetCoinW m := by simp [forgetCoinW, Functor.map_map]

@[simp] theorem forgetCoinW_bind {Coins α β : Type}
    (m : WriterT (List Coins) ProbComp α) (k : α → WriterT (List Coins) ProbComp β) :
    forgetCoinW (m >>= k) = forgetCoinW m >>= fun a => forgetCoinW (k a) := by
  simp [forgetCoinW, map_eq_bind_pure_comp, bind_assoc]

@[simp] theorem forgetCoinW_tell {Coins : Type} (w : List Coins) :
    forgetCoinW (MonadWriter.tell w : WriterT (List Coins) ProbComp PUnit) = pure ⟨⟩ := by
  simp [forgetCoinW, MonadWriter.tell]

@[simp] theorem forgetCoinW_liftM {Coins α : Type} (c : ProbComp α) :
    forgetCoinW (liftM c : WriterT (List Coins) ProbComp α) = c := by
  dsimp [forgetCoinW, liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, WriterT.liftTell]
  simp [Functor.map_map]

@[simp] theorem smSchemeCoinLogged_send_run {Key St Msg Coins RCoins C : Type}
    (sm : SMSchemeR Key St Msg Coins RCoins C) (st : St) (m : Msg) (r : Coins) :
    ((smSchemeCoinLogged sm).send st m r).run = pure (sm.send st m r, [r]) := by
  simp [smSchemeCoinLogged, MonadWriter.tell]

@[simp] theorem smSchemeCoinLogged_receive_run {Key St Msg Coins RCoins C : Type}
    (sm : SMSchemeR Key St Msg Coins RCoins C) (st : St) (c : C) (rc : RCoins) :
    ((smSchemeCoinLogged sm).receive st c rc).run = pure (sm.receive st c rc, []) := by
  simp [smSchemeCoinLogged]

@[simp] theorem smSchemeCoinLogged_initState {Key St Msg Coins RCoins C : Type}
    (sm : SMSchemeR Key St Msg Coins RCoins C) (k : Key) (b : Bool) :
    (smSchemeCoinLogged sm).initState k b = initState sm.sendPart k b := rfl

def pureCoinSchemeRM {Key St Msg Coins RCoins C : Type}
    (sm : SMSchemeR Key St Msg Coins RCoins C) :
    SMSchemeRM ProbComp Key St Msg Coins RCoins C where
  initA := sm.initA
  initB := sm.initB
  send st m r := pure (sm.send st m r)
  receive st c rc := pure (sm.receive st c rc)

@[expose] def forgetCoinS1 {Coins σ α : Type}
    (m : StateT σ (WriterT (List Coins) ProbComp) α) : StateT σ ProbComp α :=
  fun s => forgetCoinW (m.run s)

@[simp] theorem forgetCoinS1_run {Coins σ α : Type}
    (m : StateT σ (WriterT (List Coins) ProbComp) α) (s : σ) :
    (forgetCoinS1 m).run s = forgetCoinW (m.run s) := rfl

@[simp] theorem forgetCoinS1_pure {Coins σ α : Type} (a : α) :
    forgetCoinS1 (pure a : StateT σ (WriterT (List Coins) ProbComp) α) = pure a := by ext s; simp

@[simp] theorem forgetCoinS1_map {Coins σ α β : Type} (f : α → β)
    (m : StateT σ (WriterT (List Coins) ProbComp) α) :
    forgetCoinS1 (f <$> m) = f <$> forgetCoinS1 m := by ext s; simp

@[simp] theorem forgetCoinS1_bind {Coins σ α β : Type}
    (m : StateT σ (WriterT (List Coins) ProbComp) α)
    (k : α → StateT σ (WriterT (List Coins) ProbComp) β) :
    forgetCoinS1 (m >>= k) = forgetCoinS1 m >>= fun a => forgetCoinS1 (k a) := by ext s; simp

@[simp] theorem forgetCoinS1_get {Coins σ : Type} :
    forgetCoinS1 (get : StateT σ (WriterT (List Coins) ProbComp) σ) = get := by ext s; simp

@[simp] theorem forgetCoinS1_set {Coins σ : Type} (s' : σ) :
    forgetCoinS1 (set s' : StateT σ (WriterT (List Coins) ProbComp) PUnit) = set s' := by ext s; simp

@[simp] theorem forgetCoinS1_lift {Coins σ α : Type} (m : WriterT (List Coins) ProbComp α) :
    forgetCoinS1 (StateT.lift m : StateT σ (WriterT (List Coins) ProbComp) α) =
      StateT.lift (forgetCoinW m) := by ext s; simp [StateT.run_lift]

@[simp] theorem forgetCoinS1_liftStateT {Coins σ α : Type} (x : StateT σ ProbComp α) :
    forgetCoinS1 (liftStateT (n := WriterT (List Coins) ProbComp) x) = x := by
  ext s; exact forgetCoinW_liftM (x s)

private theorem oracleImplRM_pure_eq {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (q : (spec St Msg Coins C).Domain) :
    oracleImplRM (pureCoinSchemeRM sm) Δ qep cfg q = oracleImplR sm Δ qep cfg q := by
  rcases q with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
  · change transmitRM (pureCoinSchemeRM sm) Δ qep cfg (P, m, r) = transmitR sm Δ qep cfg (P, m, r)
    ext gs; unfold transmitRM transmitR transmitImpl SMSchemeR.sendPart pureCoinSchemeRM liftM monadLift
    dsimp only [MonadLiftT.monadLift, instMonadLiftTOfMonadLift, instMonadLiftT, MonadLift.monadLift]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases cfg.sendOK gs P
    · simp only [Bool.not_false, ↓reduceIte]
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind]
      cases gs.win
      · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift, pure_bind, bind_assoc]
        congr 1
      · simp only [↓reduceIte]
  · change challRM (pureCoinSchemeRM sm) Δ qep cfg (P, m₀, m₁, r) = challR sm Δ qep cfg (P, m₀, m₁, r)
    ext gs; unfold challRM challR challImpl SMSchemeR.sendPart pureCoinSchemeRM liftM monadLift
    dsimp only [MonadLiftT.monadLift, instMonadLiftTOfMonadLift, instMonadLiftT, MonadLift.monadLift]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases cfg.sendOK gs P
    · simp only [Bool.not_false, ↓reduceIte]
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind]
      cases gs.win
      · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift, pure_bind, bind_assoc]
        congr 1
      · simp only [↓reduceIte]
  · change deliverRM (pureCoinSchemeRM sm) cfg (P, c) = deliverR sm cfg (P, c)
    ext gs; unfold deliverRM deliverR pureCoinSchemeRM liftM monadLift
    dsimp only [MonadLiftT.monadLift, instMonadLiftTOfMonadLift, instMonadLiftT, MonadLift.monadLift]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases gs.win
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases gs.inTransit P.other c with
      | none => rfl
      | some r => simp only [StateT.run_bind, StateT.run_lift, pure_bind, bind_assoc]; congr 1
    · simp only [↓reduceIte]
  · change injectRM (pureCoinSchemeRM sm) Δ qep cfg (P, c) = injectR sm Δ qep cfg (P, c)
    ext gs; unfold injectRM injectR pureCoinSchemeRM liftM monadLift
    dsimp only [MonadLiftT.monadLift, instMonadLiftTOfMonadLift, instMonadLiftT, MonadLift.monadLift]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases (gs.win || (gs.inTransit P.other c).isSome || !(gs.safeInj Δ) || !(cfg.injOK c))
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift, pure_bind, bind_assoc]
      congr 1
    · simp only [↓reduceIte]
  · rfl

theorem forgetCoinS1_oracleImplRM_smSchemeCoinLogged {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (q : (spec St Msg Coins C).Domain) :
    forgetCoinS1 (oracleImplRM (smSchemeCoinLogged sm) Δ qep cfg q) =
      oracleImplR sm Δ qep cfg q := by
  rw [← oracleImplRM_pure_eq sm Δ qep cfg q]
  have hsend : ∀ s m r,
      forgetCoinW ((smSchemeCoinLogged sm).send s m r) = (pureCoinSchemeRM sm).send s m r := by
    intro s m r; simp [smSchemeCoinLogged, pureCoinSchemeRM]
  have hrecv : ∀ s c rc,
      forgetCoinW ((smSchemeCoinLogged sm).receive s c rc) =
        (pureCoinSchemeRM sm).receive s c rc := by
    intro s c rc; simp [smSchemeCoinLogged, pureCoinSchemeRM]
  rcases q with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
  · change forgetCoinS1 (transmitRM _ Δ qep cfg (P, m, r)) = transmitRM _ Δ qep cfg (P, m, r)
    unfold transmitRM; simp only [forgetCoinS1_bind, forgetCoinS1_get]; congr 1; funext s
    cases cfg.sendOK s P <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    · exact forgetCoinS1_pure _
    · cases s.win <;> simp only [Bool.false_eq_true, ↓reduceIte, forgetCoinS1_bind,
        forgetCoinS1_lift, forgetCoinW_liftM, forgetCoinS1_pure]
      congr 1; funext ⟨coins, bad⟩
      cases s.epMgmt Δ qep P bad with
      | none => exact forgetCoinS1_pure _
      | some s₁ => simp [hsend]
  · change forgetCoinS1 (challRM _ Δ qep cfg (P, m₀, m₁, r)) = challRM _ Δ qep cfg (P, m₀, m₁, r)
    unfold challRM; simp only [forgetCoinS1_bind, forgetCoinS1_get]; congr 1; funext s
    cases cfg.sendOK s P <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    · exact forgetCoinS1_pure _
    · cases s.win <;> simp only [Bool.false_eq_true, ↓reduceIte, forgetCoinS1_bind,
        forgetCoinS1_lift, forgetCoinW_liftM, forgetCoinS1_pure]
      congr 1; funext ⟨coins, bad⟩
      cases s.epMgmt Δ qep P bad with
      | none => exact forgetCoinS1_pure _
      | some s₁ =>
        dsimp only
        cases (!(s₁.safeCh Δ P) || !(cfg.base.challAllowedIn (s₁.epoch P))) <;> simp [hsend]
  · change forgetCoinS1 (deliverRM _ cfg (P, c)) = deliverRM _ cfg (P, c)
    unfold deliverRM; simp only [forgetCoinS1_bind, forgetCoinS1_get]; congr 1; funext s
    cases s.win <;> simp only [Bool.false_eq_true, ↓reduceIte, forgetCoinS1_pure]
    cases s.inTransit P.other c with
    | none => exact forgetCoinS1_pure _
    | some r =>
      dsimp only; simp only [forgetCoinS1_bind, forgetCoinS1_lift, forgetCoinW_liftM]
      congr 1; funext rc; rw [hrecv]; congr 1; funext out
      cases out with
      | none => split_ifs <;> simp
      | some x => rcases x with ⟨st', t', i', m'⟩; dsimp only; split_ifs <;> simp
  · change forgetCoinS1 (injectRM _ Δ qep cfg (P, c)) = injectRM _ Δ qep cfg (P, c)
    unfold injectRM; simp only [forgetCoinS1_bind, forgetCoinS1_get]; congr 1; funext s
    cases (s.win || (s.inTransit P.other c).isSome || !(s.safeInj Δ) || !(cfg.injOK c)) <;>
      simp only [Bool.false_eq_true, ↓reduceIte, forgetCoinS1_bind, forgetCoinS1_lift,
        forgetCoinW_liftM, forgetCoinS1_pure]
    congr 1; funext rc; rw [hrecv]; congr 1; funext out
    cases out with
    | none => exact forgetCoinS1_pure _
    | some x => rcases x with ⟨st', t', i', m'⟩; dsimp only; split_ifs <;> simp
  · exact forgetCoinS1_liftStateT _

theorem forgetCoinS1_simulateQ {Coins ι σ : Type} {ospec : OracleSpec ι}
    (impl₁ : QueryImpl ospec (StateT σ (WriterT (List Coins) ProbComp)))
    (impl₂ : QueryImpl ospec (StateT σ ProbComp))
    (himpl : ∀ t, forgetCoinS1 (impl₁ t) = impl₂ t) {α : Type} (oa : OracleComp ospec α) :
    forgetCoinS1 (simulateQ impl₁ oa) = simulateQ impl₂ oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query, forgetCoinS1_bind, himpl t,
      simulateQ_bind, simulateQ_spec_query]
    exact congrArg (impl₂ t >>= ·) (funext ih)

/-- Forgetting the send-coin log of `gameRCoinLogged` equals `SM.gameR`. -/
theorem fst_gameRCoinLogged {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (A : Adversary St Msg Coins C) :
    Prod.fst <$> gameRCoinLogged sm Δ qep cfg A = gameR sm Δ qep cfg A := by
  change forgetCoinW (do
    let b ← liftM ($ᵗ Bool : ProbComp Bool)
    let k ← liftM ($ᵗ Key : ProbComp Key)
    let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (GameState St Msg C) (WriterT (List Coins) ProbComp)) +
      oracleImplRM (smSchemeCoinLogged sm) Δ qep cfg
    let (b', s) ← (simulateQ impl A).run ((smSchemeCoinLogged sm).initState k b)
    return (b == b' || s.win)) = gameR sm Δ qep cfg A
  unfold gameR runR; simp only [forgetCoinW_bind, forgetCoinW_liftM, bind_assoc]
  congr 1; funext b; congr 1; funext k
  have himpl : ∀ t : (unifSpec + spec St Msg Coins C).Domain,
      forgetCoinS1
        (((QueryImpl.ofLift unifSpec ProbComp).liftTarget
            (StateT (GameState St Msg C) (WriterT (List Coins) ProbComp)) +
          oracleImplRM (smSchemeCoinLogged sm) Δ qep cfg) t) =
        (((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (GameState St Msg C) ProbComp) +
          oracleImplR sm Δ qep cfg) t) := by
    rintro (u | q)
    · ext gs
      change forgetCoinW ((StateT.lift (liftM (QueryImpl.ofLift unifSpec ProbComp u) :
        WriterT (List Coins) ProbComp _)).run gs) =
        (StateT.lift (QueryImpl.ofLift unifSpec ProbComp u)).run gs
      simp [StateT.run_lift]
    · exact forgetCoinS1_oracleImplRM_smSchemeCoinLogged sm Δ qep cfg q
  rw [← forgetCoinS1_run, forgetCoinS1_simulateQ _ _ himpl A, smSchemeCoinLogged_initState]; simp

theorem evalDist_fst_gameRCoinLogged {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (A : Adversary St Msg Coins C) :
    𝒟[Prod.fst <$> gameRCoinLogged sm Δ qep cfg A] = 𝒟[gameR sm Δ qep cfg A] :=
  congrArg evalDist (fst_gameRCoinLogged sm Δ qep cfg A)

/-- Forgetting the send-coin log of `gameRCoinLogged` preserves `evalDist` (`GameRCoinLoggedFaithful`). -/
theorem gameRCoinLogged_faithful : GameRCoinLoggedFaithful :=
  fun sm Δ qep cfg A => evalDist_fst_gameRCoinLogged sm Δ qep cfg A

/-! ## `KemFailBad` over 64-byte send tapes -/

theorem tapePairFails_coinBytes_eq (K : MlKem) (r₁ r₂ : BitVec 512) :
    K.tapePairFails (coinBytes r₁) (coinBytes r₂) =
      K.honestExchangeFails ⟨coinBytes r₁, coinBytes_length r₁⟩
        ⟨(coinBytes r₂).take 32, by simp [coinBytes_length r₂]⟩ := by
  unfold MlKem.tapePairFails; simp [coinBytes_length r₁, coinBytes_length r₂]

theorem kemFailBad_eq_true_iff (K : MlKem) (tapes : List (List (BitVec 8))) :
    K.KemFailBad tapes = true ↔ ∃ t₁ ∈ tapes, ∃ t₂ ∈ tapes, K.tapePairFails t₁ t₂ = true := by
  simp [MlKem.KemFailBad, List.any_eq_true]

theorem kemFailBad_mono_subset (K : MlKem) {l₁ l₂ : List (List (BitVec 8))}
    (hsub : l₁ ⊆ l₂) (h : K.KemFailBad l₁ = true) : K.KemFailBad l₂ = true := by
  rw [kemFailBad_eq_true_iff] at h ⊢; rcases h with ⟨t₁, ht₁, t₂, ht₂, hfail⟩
  exact ⟨t₁, hsub ht₁, t₂, hsub ht₂, hfail⟩

theorem kemFailBad_eq_false_of_subset (K : MlKem) {l₁ l₂ : List (List (BitVec 8))}
    (hsub : l₁ ⊆ l₂) (h : K.KemFailBad l₂ = false) : K.KemFailBad l₁ = false := by
  cases h₁ : K.KemFailBad l₁
  · rfl
  · rw [kemFailBad_mono_subset K hsub h₁] at h; cases h

abbrev kemFailBadLog (K : MlKem) (w : List (BitVec 512)) : Bool :=
  K.KemFailBad (w.map coinBytes)

/-- A predicate on coin logs is prefix-closed when extending a bad log never makes it good again. -/
def PrefixClosed {Coins : Type} (good : List Coins → Prop) : Prop :=
  ∀ w₁ w₂, good (w₁ ++ w₂) → good w₁

/-! ## Prefix-closed online identical-until-bad -/

@[expose] def embedCoinW {Coins α : Type} (m : WriterT (List Coins) ProbComp α) :
    StateT (List Coins) ProbComp α :=
  fun pre => (fun zw => (zw.1, pre ++ zw.2)) <$> m.run

@[simp] theorem embedCoinW_run {Coins α : Type}
    (m : WriterT (List Coins) ProbComp α) (pre : List Coins) :
    (embedCoinW m).run pre = (fun zw => (zw.1, pre ++ zw.2)) <$> m.run := rfl

@[simp] theorem embedCoinW_run_nil {Coins α : Type} (m : WriterT (List Coins) ProbComp α) :
    (embedCoinW m).run [] = m.run := by simp

@[simp] theorem embedCoinW_pure {Coins α : Type} (a : α) :
    embedCoinW (pure a : WriterT (List Coins) ProbComp α) = pure a := by ext pre; simp

@[simp] theorem embedCoinW_map {Coins α β : Type} (f : α → β)
    (m : WriterT (List Coins) ProbComp α) :
    embedCoinW (f <$> m) = f <$> embedCoinW m := by ext pre; simp [Functor.map_map]

@[simp] theorem embedCoinW_liftM {Coins α : Type} (c : ProbComp α) :
    embedCoinW (liftM c : WriterT (List Coins) ProbComp α) = liftM c := by
  ext pre
  change (fun zw => (zw.1, pre ++ zw.2)) <$> (liftM c : WriterT (List Coins) ProbComp α).run =
    (StateT.lift c).run pre
  dsimp [liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, WriterT.liftTell]
  simp [map_eq_bind_pure_comp]

@[simp] theorem embedCoinW_bind {Coins α β : Type}
    (m : WriterT (List Coins) ProbComp α) (k : α → WriterT (List Coins) ProbComp β) :
    embedCoinW (m >>= k) = embedCoinW m >>= fun a => embedCoinW (k a) := by
  ext pre
  simp only [embedCoinW_run, WriterT.run_bind, StateT.run_bind, map_eq_bind_pure_comp,
    Function.comp_apply, bind_assoc, pure_bind, List.append_assoc]; rfl

@[simp] theorem embedCoinW_smSchemeCoinLogged_send {Key St Msg Coins RCoins C : Type}
    (sm : SMSchemeR Key St Msg Coins RCoins C) (st : St) (m : Msg) (r : Coins) :
    embedCoinW ((smSchemeCoinLogged sm).send st m r) =
      (fun pre => pure (sm.send st m r, pre ++ [r])) := by
  ext pre; change _ = pure (sm.send st m r, pre ++ [r]); simp

@[simp] theorem embedCoinW_smSchemeCoinLogged_receive {Key St Msg Coins RCoins C : Type}
    (sm : SMSchemeR Key St Msg Coins RCoins C) (st : St) (c : C) (rc : RCoins) :
    embedCoinW ((smSchemeCoinLogged sm).receive st c rc) = pure (sm.receive st c rc) := by
  ext pre; simp

@[expose] def embedCoinS1 {Coins σ α : Type} (m : StateT σ (WriterT (List Coins) ProbComp) α) :
    StateT σ (StateT (List Coins) ProbComp) α :=
  fun s => embedCoinW (m.run s)

@[simp] theorem embedCoinS1_run {Coins σ α : Type}
    (m : StateT σ (WriterT (List Coins) ProbComp) α) (s : σ) :
    (embedCoinS1 m).run s = embedCoinW (m.run s) := rfl

@[simp] theorem embedCoinS1_pure {Coins σ α : Type} (a : α) :
    embedCoinS1 (pure a : StateT σ (WriterT (List Coins) ProbComp) α) = pure a := by ext s pre; simp

@[simp] theorem embedCoinS1_map {Coins σ α β : Type} (f : α → β)
    (m : StateT σ (WriterT (List Coins) ProbComp) α) :
    embedCoinS1 (f <$> m) = f <$> embedCoinS1 m := by ext s pre; simp

@[simp] theorem embedCoinS1_bind {Coins σ α β : Type}
    (m : StateT σ (WriterT (List Coins) ProbComp) α)
    (k : α → StateT σ (WriterT (List Coins) ProbComp) β) :
    embedCoinS1 (m >>= k) = embedCoinS1 m >>= fun a => embedCoinS1 (k a) := by ext s pre; simp

@[simp] theorem embedCoinS1_get {Coins σ : Type} :
    embedCoinS1 (get : StateT σ (WriterT (List Coins) ProbComp) σ) = get := by ext s pre; simp

@[simp] theorem embedCoinS1_set {Coins σ : Type} (s' : σ) :
    embedCoinS1 (set s' : StateT σ (WriterT (List Coins) ProbComp) PUnit) = set s' := by
  ext s pre; simp

@[simp] theorem embedCoinS1_lift {Coins σ α : Type} (m : WriterT (List Coins) ProbComp α) :
    embedCoinS1 (StateT.lift m : StateT σ (WriterT (List Coins) ProbComp) α) =
      StateT.lift (embedCoinW m) := by ext s pre; simp [StateT.run_lift]

@[simp] theorem embedCoinS1_liftStateT {Coins σ α : Type} (x : StateT σ ProbComp α) :
    embedCoinS1 (liftStateT (n := WriterT (List Coins) ProbComp) x) =
      liftStateT (n := StateT (List Coins) ProbComp) x := by
  ext s pre; exact congrFun (congrArg StateT.run (embedCoinW_liftM (x s))) pre

theorem embedCoinS1_simulateQ {Coins ι σ : Type} {ospec : OracleSpec ι}
    (impl₁ : QueryImpl ospec (StateT σ (WriterT (List Coins) ProbComp)))
    (impl₂ : QueryImpl ospec (StateT σ (StateT (List Coins) ProbComp)))
    (himpl : ∀ t, embedCoinS1 (impl₁ t) = impl₂ t) {α : Type} (oa : OracleComp ospec α) :
    embedCoinS1 (simulateQ impl₁ oa) = simulateQ impl₂ oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query, embedCoinS1_bind, himpl t,
      simulateQ_bind, simulateQ_spec_query]
    exact congrArg (impl₂ t >>= ·) (funext ih)

/-- Once the coin log fails `good`, every output state of `m` stays outside `good`. -/
def PreservesBad {Coins α : Type} (good : List Coins → Prop)
    (m : StateT (List Coins) ProbComp α) : Prop :=
  ∀ log, ¬ good log → ∀ z ∈ support (m.run log), ¬ good z.2

theorem PreservesBad.pure {Coins α : Type} (good : List Coins → Prop) (a : α) :
    PreservesBad good (pure a : StateT (List Coins) ProbComp α) := by
  intro log hbad z hz
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz; exact hbad

theorem PreservesBad.liftM {Coins α : Type} (good : List Coins → Prop) (c : ProbComp α) :
    PreservesBad good (liftM c : StateT (List Coins) ProbComp α) := by
  intro log hbad z hz
  change z ∈ support ((StateT.lift c).run log) at hz
  simp only [StateT.run_lift, support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
    exists_prop] at hz
  rcases hz with ⟨_, _, rfl⟩; exact hbad

theorem PreservesBad.append {Coins α : Type} {good : List Coins → Prop}
    (hpref : PrefixClosed good) (f : List Coins → α × List Coins)
    (hf : ∀ log, ∃ sfx, (f log).2 = log ++ sfx) :
    PreservesBad good (fun log => Pure.pure (f log)) := by
  intro log hbad z hz
  change z ∈ support (Pure.pure (f log)) at hz
  rw [support_pure, Set.mem_singleton_iff] at hz
  subst hz; rcases hf log with ⟨sfx, heq⟩
  exact fun hg => hbad (hpref log sfx (heq ▸ hg))

theorem PreservesBad.embedCoinW {Coins α : Type} {good : List Coins → Prop}
    (hpref : PrefixClosed good) (m : WriterT (List Coins) ProbComp α) :
    PreservesBad good (embedCoinW m) := by
  intro log hbad z hz
  rw [embedCoinW_run, support_map, Set.mem_image] at hz
  rcases hz with ⟨zw, _, rfl⟩
  exact fun hg => hbad (hpref log zw.2 hg)

theorem PreservesBad.bind {Coins α β : Type} {good : List Coins → Prop}
    {m : StateT (List Coins) ProbComp α} {k : α → StateT (List Coins) ProbComp β}
    (hm : PreservesBad good m) (hk : ∀ a, PreservesBad good (k a)) :
    PreservesBad good (m >>= k) := by
  intro log hbad z hz
  simp only [StateT.run_bind, support_bind, Set.mem_iUnion, exists_prop] at hz
  rcases hz with ⟨x, hx, hz⟩; exact hk x.1 x.2 (hm log hbad x hx) z hz

/-- Online prefix-aware identical-until-bad agreement on `StateT (List Coins) ProbComp`. -/
structure AgreeOnline {Coins α : Type} (good : List Coins → Prop)
    (m₁ m₂ : StateT (List Coins) ProbComp α) : Prop where
  pres₁ : PreservesBad good m₁
  pres₂ : PreservesBad good m₂
  agree : ∀ log, good log → ∀ p : α × List Coins → Prop,
    Pr{let z ← m₁.run log}[p z ∧ good z.2] = Pr{let z ← m₂.run log}[p z ∧ good z.2]

theorem AgreeOnline.refl {Coins α : Type} {good : List Coins → Prop}
    {m : StateT (List Coins) ProbComp α} (hm : PreservesBad good m) : AgreeOnline good m m :=
  ⟨hm, hm, fun _ _ _ => rfl⟩

theorem AgreeOnline.pure {Coins α : Type} (good : List Coins → Prop) (a : α) :
    AgreeOnline good (pure a : StateT (List Coins) ProbComp α) (pure a) :=
  AgreeOnline.refl (PreservesBad.pure good a)

theorem AgreeOnline.liftM {Coins α : Type} (good : List Coins → Prop) (c : ProbComp α) :
    AgreeOnline good (liftM c : StateT (List Coins) ProbComp α) (liftM c) :=
  AgreeOnline.refl (PreservesBad.liftM good c)

theorem AgreeOnline.bind {Coins α β : Type} {good : List Coins → Prop}
    {m₁ m₂ : StateT (List Coins) ProbComp α} {k₁ k₂ : α → StateT (List Coins) ProbComp β}
    (hm : AgreeOnline good m₁ m₂) (hk : ∀ a, AgreeOnline good (k₁ a) (k₂ a)) :
    AgreeOnline good (m₁ >>= k₁) (m₂ >>= k₂) where
  pres₁ := PreservesBad.bind hm.pres₁ fun a => (hk a).pres₁
  pres₂ := PreservesBad.bind hm.pres₂ fun a => (hk a).pres₂
  agree log hlog p := by
    simp only [StateT.run_bind]
    let : MeasurableSpace (α × List Coins) := ⊤
    let G : Set (α × List Coins) := {x | good x.2}
    let F (k : α → StateT (List Coins) ProbComp β) (x : α × List Coins) : ℝ≥0∞ :=
      Pr{let z ← (k x.1).run x.2}[p z ∧ good z.2]
    have hF_ind₁ (x : α × List Coins) : F k₁ x = G.indicator (F k₁) x := by
      by_cases hx : x ∈ G
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx]
        exact prEvent_eq_zero_of_forall_mem_support _ _ fun z hz ⟨_, hg⟩ =>
          (hk x.1).pres₁ x.2 hx z hz hg
    have hF_ind₂ (x : α × List Coins) : F k₂ x = G.indicator (F k₂) x := by
      by_cases hx : x ∈ G
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx]
        exact prEvent_eq_zero_of_forall_mem_support _ _ fun z hz ⟨_, hg⟩ =>
          (hk x.1).pres₂ x.2 hx z hz hg
    have hF_eq_G (x : α × List Coins) : G.indicator (F k₁) x = G.indicator (F k₂) x := by
      by_cases hx : x ∈ G
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]; exact (hk x.1).agree x.2 hx p
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
    have hrestrict : 𝒟[m₁.run log].restrict G = 𝒟[m₂.run log].restrict G := by
      refine Measure.ext fun A hA => ?_
      rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
      change 𝒟[m₁.run log] {z | z ∈ A ∧ good z.2} = 𝒟[m₂.run log] {z | z ∈ A ∧ good z.2}
      rw [← prEvent_eq_evalDist_of_discrete, ← prEvent_eq_evalDist_of_discrete]
      exact hm.agree log hlog (· ∈ A)
    rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete]
    change ∫⁻ x, F k₁ x ∂𝒟[m₁.run log] = ∫⁻ x, F k₂ x ∂𝒟[m₂.run log]
    calc ∫⁻ x, F k₁ x ∂𝒟[m₁.run log]
        = ∫⁻ x, G.indicator (F k₂) x ∂𝒟[m₁.run log] :=
            lintegral_congr fun x => by rw [hF_ind₁ x, hF_eq_G x]
      _ = ∫⁻ x, F k₂ x ∂(𝒟[m₁.run log].restrict G) := lintegral_indicator MeasurableSet.of_discrete _
      _ = ∫⁻ x, F k₂ x ∂(𝒟[m₂.run log].restrict G) := by rw [hrestrict]
      _ = ∫⁻ x, G.indicator (F k₂) x ∂𝒟[m₂.run log] :=
            (lintegral_indicator MeasurableSet.of_discrete _).symm
      _ = ∫⁻ x, F k₂ x ∂𝒟[m₂.run log] := lintegral_congr fun x => (hF_ind₂ x).symm

def AgreeOnlineS1 {Coins σ α : Type} (good : List Coins → Prop)
    (m₁ m₂ : StateT σ (StateT (List Coins) ProbComp) α) : Prop :=
  ∀ s, AgreeOnline good (m₁.run s) (m₂.run s)

theorem AgreeOnlineS1.pure {Coins σ α : Type} (good : List Coins → Prop) (a : α) :
    AgreeOnlineS1 good (pure a : StateT σ (StateT (List Coins) ProbComp) α) (pure a) :=
  fun s => AgreeOnline.pure good (a, s)

theorem AgreeOnlineS1.get {Coins σ : Type} (good : List Coins → Prop) :
    AgreeOnlineS1 good (get : StateT σ (StateT (List Coins) ProbComp) σ) get :=
  fun s => AgreeOnline.pure good (s, s)

theorem AgreeOnlineS1.set {Coins σ : Type} (good : List Coins → Prop) (s' : σ) :
    AgreeOnlineS1 good (set s' : StateT σ (StateT (List Coins) ProbComp) PUnit) (set s') :=
  fun _ => AgreeOnline.pure good ((), s')

theorem AgreeOnlineS1.lift {Coins σ α : Type} {good : List Coins → Prop}
    {m₁ m₂ : StateT (List Coins) ProbComp α} (hm : AgreeOnline good m₁ m₂) :
    AgreeOnlineS1 good (StateT.lift m₁ : StateT σ (StateT (List Coins) ProbComp) α)
      (StateT.lift m₂ : StateT σ (StateT (List Coins) ProbComp) α) :=
  fun s => by simp only [StateT.run_lift]; exact AgreeOnline.bind hm fun a => AgreeOnline.pure good (a, s)

theorem AgreeOnlineS1.bind {Coins σ α β : Type} {good : List Coins → Prop}
    {m₁ m₂ : StateT σ (StateT (List Coins) ProbComp) α}
    {k₁ k₂ : α → StateT σ (StateT (List Coins) ProbComp) β}
    (hm : AgreeOnlineS1 good m₁ m₂) (hk : ∀ a, AgreeOnlineS1 good (k₁ a) (k₂ a)) :
    AgreeOnlineS1 good (m₁ >>= k₁) (m₂ >>= k₂) :=
  fun s => by simp only [StateT.run_bind]; exact AgreeOnline.bind (hm s) fun x => hk x.1 x.2

theorem AgreeOnlineS1.simulateQ {Coins ι σ : Type} {ospec : OracleSpec ι} {good : List Coins → Prop}
    (impl₁ impl₂ : QueryImpl ospec (StateT σ (StateT (List Coins) ProbComp)))
    (himpl : ∀ t, AgreeOnlineS1 good (impl₁ t) (impl₂ t)) {α : Type} (oa : OracleComp ospec α) :
    AgreeOnlineS1 good (simulateQ impl₁ oa) (simulateQ impl₂ oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact AgreeOnlineS1.pure good a
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query, simulateQ_bind, simulateQ_spec_query]
    exact AgreeOnlineS1.bind (himpl t) ih

def smSchemeCoinState {Key St Msg Coins RCoins C : Type}
    (sm : SMSchemeR Key St Msg Coins RCoins C) :
    SMSchemeRM (StateT (List Coins) ProbComp) Key St Msg Coins RCoins C where
  initA := sm.initA
  initB := sm.initB
  send st m r := fun log => pure (sm.send st m r, log ++ [r])
  receive st c rc := pure (sm.receive st c rc)

/-- Online-halted `transmit` oracle returning `none` once `badLog (log ++ [coins]) = true`. -/
def transmitRHalted {Key St Msg Coins RCoins C : Type} [SampleableType Coins]
    (badLog : List Coins → Bool) (sm : SMSchemeR Key St Msg Coins RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    QueryImpl ((Party × Msg × Option Coins) →ₒ Option C)
      (StateT (GameState St Msg C) (StateT (List Coins) ProbComp)) :=
  fun ⟨P, m, r⟩ => do
    let s ← get
    if !(cfg.sendOK s P) then return none
    if s.win then return none
    let (coins, bad) ← StateT.lift (liftM (samIfNec r : ProbComp (Coins × Bool)))
    match s.epMgmt Δ qep P bad with
    | none => return none
    | some s₁ =>
      let isBad ← StateT.lift (fun log => let log' := log ++ [coins]; pure (badLog log', log'))
      if isBad then return none
      else
        let out := sm.send (s₁.st P) m coins
        set (s₁.record Δ P out.1 ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, out.2⟩ false)
        return some out.2

/-- Online-halted `chall` oracle returning `none` once `badLog (log ++ [coins]) = true`. -/
def challRHalted {Key St Msg Coins RCoins C : Type} [SampleableType Coins]
    (badLog : List Coins → Bool) (sm : SMSchemeR Key St Msg Coins RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    QueryImpl ((Party × Msg × Msg × Option Coins) →ₒ Option C)
      (StateT (GameState St Msg C) (StateT (List Coins) ProbComp)) :=
  fun ⟨P, m₀, m₁, r⟩ => do
    let s ← get
    if !(cfg.sendOK s P) then return none
    if s.win then return none
    let (coins, bad) ← StateT.lift (liftM (samIfNec r : ProbComp (Coins × Bool)))
    match s.epMgmt Δ qep P bad with
    | none => return none
    | some s₁ =>
      if !(s₁.safeCh Δ P) || !(cfg.base.challAllowedIn (s₁.epoch P)) then return none
      let isBad ← StateT.lift (fun log => let log' := log ++ [coins]; pure (badLog log', log'))
      if isBad then return none
      else
        let m := (cfg.base.challMsg (s₁.epoch P)).getD (if s.b then m₁ else m₀)
        let out := sm.send (s₁.st P) m coins
        set (s₁.record Δ P out.1 ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, out.2⟩ true)
        return some out.2

def oracleImplRHalted {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (badLog : List Coins → Bool) (sm : SMSchemeR Key St Msg Coins RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    QueryImpl (spec St Msg Coins C)
      (StateT (GameState St Msg C) (StateT (List Coins) ProbComp)) :=
  transmitRHalted badLog sm Δ qep cfg + challRHalted badLog sm Δ qep cfg +
    deliverRM (smSchemeCoinState sm) cfg + injectRM (smSchemeCoinState sm) Δ qep cfg +
    ((fun P => liftStateT (corrR cfg P)) :
      QueryImpl (Party →ₒ Option St)
        (StateT (GameState St Msg C) (StateT (List Coins) ProbComp)))

private theorem embedCoinS1_oracleImplRM_eq {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (q : (spec St Msg Coins C).Domain) :
    embedCoinS1 (oracleImplRM (smSchemeCoinLogged sm) Δ qep cfg q) =
      oracleImplRM (smSchemeCoinState sm) Δ qep cfg q := by
  rcases q with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
  · change embedCoinS1 (transmitRM (smSchemeCoinLogged sm) Δ qep cfg (P, m, r)) =
      transmitRM (smSchemeCoinState sm) Δ qep cfg (P, m, r)
    unfold transmitRM; simp only [embedCoinS1_bind, embedCoinS1_get]; congr 1; funext s
    cases cfg.sendOK s P <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    · exact embedCoinS1_pure _
    · cases s.win <;> simp only [Bool.false_eq_true, ↓reduceIte, embedCoinS1_bind,
        embedCoinS1_lift, embedCoinW_liftM, embedCoinS1_pure]
      congr 1; funext ⟨coins, bad⟩
      cases s.epMgmt Δ qep P bad with
      | none => exact embedCoinS1_pure _
      | some s₁ => simp [smSchemeCoinState]
  · change embedCoinS1 (challRM (smSchemeCoinLogged sm) Δ qep cfg (P, m₀, m₁, r)) =
      challRM (smSchemeCoinState sm) Δ qep cfg (P, m₀, m₁, r)
    unfold challRM; simp only [embedCoinS1_bind, embedCoinS1_get]; congr 1; funext s
    cases cfg.sendOK s P <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    · exact embedCoinS1_pure _
    · cases s.win <;> simp only [Bool.false_eq_true, ↓reduceIte, embedCoinS1_bind,
        embedCoinS1_lift, embedCoinW_liftM, embedCoinS1_pure]
      congr 1; funext ⟨coins, bad⟩
      cases s.epMgmt Δ qep P bad with
      | none => exact embedCoinS1_pure _
      | some s₁ =>
        dsimp only
        cases (!(s₁.safeCh Δ P) || !(cfg.base.challAllowedIn (s₁.epoch P))) <;>
          simp [smSchemeCoinState]
  · change embedCoinS1 (deliverRM (smSchemeCoinLogged sm) cfg (P, c)) =
      deliverRM (smSchemeCoinState sm) cfg (P, c)
    unfold deliverRM; simp only [embedCoinS1_bind, embedCoinS1_get]; congr 1; funext s
    cases s.win <;> simp only [Bool.false_eq_true, ↓reduceIte, embedCoinS1_pure]
    cases s.inTransit P.other c with
    | none => exact embedCoinS1_pure _
    | some r =>
      dsimp only
      simp only [embedCoinS1_bind, embedCoinS1_lift, embedCoinW_liftM,
        embedCoinW_smSchemeCoinLogged_receive, smSchemeCoinState]
      congr 1; funext rc; congr 1; funext out
      cases out with
      | none => split_ifs <;> simp
      | some x => rcases x with ⟨st', t', i', m'⟩; dsimp only; split_ifs <;> simp
  · change embedCoinS1 (injectRM (smSchemeCoinLogged sm) Δ qep cfg (P, c)) =
      injectRM (smSchemeCoinState sm) Δ qep cfg (P, c)
    unfold injectRM; simp only [embedCoinS1_bind, embedCoinS1_get]; congr 1; funext s
    cases (s.win || (s.inTransit P.other c).isSome || !(s.safeInj Δ) || !(cfg.injOK c)) <;>
      simp only [Bool.false_eq_true, ↓reduceIte, embedCoinS1_bind, embedCoinS1_lift,
        embedCoinW_liftM, embedCoinW_smSchemeCoinLogged_receive, embedCoinS1_pure, smSchemeCoinState]
    congr 1; funext rc; congr 1; funext out
    cases out with
    | none => exact embedCoinS1_pure _
    | some x => rcases x with ⟨st', t', i', m'⟩; dsimp only; split_ifs <;> simp
  · exact embedCoinS1_liftStateT _

private theorem gameRCoinLogged_eq_state {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (A : Adversary St Msg Coins C) :
    gameRCoinLogged sm Δ qep cfg A =
      (StateT.run · []) do
        let b ← liftM ($ᵗ Bool : ProbComp Bool); let k ← liftM ($ᵗ Key : ProbComp Key)
        let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
            (StateT (GameState St Msg C) (StateT (List Coins) ProbComp)) +
          oracleImplRM (smSchemeCoinState sm) Δ qep cfg
        let (b', s) ← (simulateQ impl A).run (initState sm.sendPart k b)
        return (b == b' || s.win) := by
  unfold gameRCoinLogged; rw [← embedCoinW_run_nil]; congr 1
  simp only [embedCoinW_bind, embedCoinW_liftM, smSchemeCoinLogged_initState]
  congr 1; funext b; congr 1; funext k
  have himpl : ∀ t : (unifSpec + spec St Msg Coins C).Domain,
      embedCoinS1 (((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (GameState St Msg C) (WriterT (List Coins) ProbComp)) +
        oracleImplRM (smSchemeCoinLogged sm) Δ qep cfg) t) =
      (((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (GameState St Msg C) (StateT (List Coins) ProbComp)) +
        oracleImplRM (smSchemeCoinState sm) Δ qep cfg) t) := by
    rintro (u | q)
    · change embedCoinS1 (StateT.lift (liftM (QueryImpl.ofLift unifSpec ProbComp u))) =
        StateT.lift (liftM (QueryImpl.ofLift unifSpec ProbComp u))
      rw [embedCoinS1_lift, embedCoinW_liftM]
    · exact embedCoinS1_oracleImplRM_eq sm Δ qep cfg q
  rw [← embedCoinS1_run, embedCoinS1_simulateQ _ _ himpl A]; ext pre; simp

/-! ## Boolean distance and bias transfer -/

theorem boolDist_fst_le_prEvent_of_good_le {β : Type}
    (exp : ProbComp (Bool × β)) (exp₀ : ProbComp Bool) (badEv : Bool × β → Prop)
    (hgood : ∀ b : Bool, Pr{let z ← exp}[z.1 = b ∧ ¬ badEv z] ≤ Pr{let b' ← exp₀}[b' = b]) :
    (𝒟[Prod.fst <$> exp]).boolDist (𝒟[exp₀]) ≤ Pr{let z ← exp}[badEv z] := by
  let : MeasurableSpace (Bool × β) := ⊤
  refine Measure.boolDist_le_of_apply_le _ _ fun b => ?_
  have hsing : ({b} : Set Bool) = {x | x = b} := Set.ext fun _ => Set.mem_singleton_iff
  have hfst : (𝒟[Prod.fst <$> exp]) {b} = (𝒟[exp]) {z | z.1 = b} := by
    rw [hsing, ← prEvent_eq_evalDist_of_discrete, prEvent_map, prEvent_eq_evalDist_of_discrete]
  have hrhs : (𝒟[exp₀]) {b} = Pr{let b' ← exp₀}[b' = b] := by
    rw [hsing, ← prEvent_eq_evalDist_of_discrete]
  rw [hfst, hrhs]
  have hsub : {z : Bool × β | z.1 = b} ⊆ {z | z.1 = b ∧ ¬ badEv z} ∪ {z | badEv z} :=
    fun z hz => by by_cases hb : badEv z <;> [exact Or.inr hb; exact Or.inl ⟨hz, hb⟩]
  calc (𝒟[exp]) {z | z.1 = b}
      ≤ (𝒟[exp]) ({z | z.1 = b ∧ ¬ badEv z} ∪ {z | badEv z}) := MeasureTheory.measure_mono hsub
    _ ≤ (𝒟[exp]) {z | z.1 = b ∧ ¬ badEv z} + (𝒟[exp]) {z | badEv z} :=
        MeasureTheory.measure_union_le _ _
    _ = Pr{let z ← exp}[z.1 = b ∧ ¬ badEv z] + Pr{let z ← exp}[badEv z] := by
        rw [← prEvent_eq_evalDist_of_discrete, ← prEvent_eq_evalDist_of_discrete]
    _ ≤ Pr{let b' ← exp₀}[b' = b] + Pr{let z ← exp}[badEv z] := by gcongr; exact hgood b

theorem boolDist_fst_le_prEvent_of_agree {β : Type}
    (exp exp₀ : ProbComp (Bool × β)) (badEv : Bool × β → Prop)
    (hagree : ∀ p : Bool × β → Prop,
      Pr{let z ← exp}[p z ∧ ¬ badEv z] = Pr{let z ← exp₀}[p z ∧ ¬ badEv z]) :
    (𝒟[Prod.fst <$> exp]).boolDist (𝒟[Prod.fst <$> exp₀]) ≤ Pr{let z ← exp}[badEv z] := by
  let : MeasurableSpace (Bool × β) := ⊤
  refine boolDist_fst_le_prEvent_of_good_le exp (Prod.fst <$> exp₀) badEv fun b => ?_
  rw [hagree fun z => z.1 = b, prEvent_map, prEvent_eq_evalDist_of_discrete,
    prEvent_eq_evalDist_of_discrete]
  exact MeasureTheory.measure_mono fun _ h => h.1

theorem boolBias_le_add_two_mul_of_boolDist_le (μ ν : Measure Bool) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (ε : ℝ≥0∞) (h : μ.boolDist ν ≤ ε) :
    μ.boolBias ≤ ν.boolBias + 2 * ε := by
  have hbd : μ.boolDist ν = ENNReal.absDiff (μ {true}) (ν {true}) := Measure.boolDist.eq_1 μ ν
  calc μ.boolBias = 2 * ENNReal.absDiff (μ {true}) (1 / 2) :=
        Measure.boolBias_eq_two_mul_absDiff_half_of_isProbabilityMeasure μ
    _ ≤ 2 * (ENNReal.absDiff (μ {true}) (ν {true}) + ENNReal.absDiff (ν {true}) (1 / 2)) := by
        gcongr; exact ENNReal.absDiff_triangle _ _ _
    _ = 2 * ENNReal.absDiff (ν {true}) (1 / 2) + 2 * μ.boolDist ν := by rw [← hbd]; ring
    _ = ν.boolBias + 2 * μ.boolDist ν := by
        rw [Measure.boolBias_eq_two_mul_absDiff_half_of_isProbabilityMeasure ν]
    _ ≤ ν.boolBias + 2 * ε := by gcongr

end Computational.Proofs.SpecLemmas.Session.GameRCoinLogged
