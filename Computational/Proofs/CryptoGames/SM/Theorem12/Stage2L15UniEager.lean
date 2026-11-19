/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem12.Stage2Defs
public import Computational.Proofs.CryptoGames.SM.Theorem12.Lemma15
public import Computational.Proofs.CryptoGames.FSAEAD.Lazy -- proof-setup: allow-public-import

/-!
# Eager Key-Slot Commutation and Outcome Reductions for Stage-2 Switch-Back (`SM/Theorem12`)

**Checked by Lean.** No theorem of `Computational/Theorems/` unfolds a definition of this file, and
Lean's kernel checks every proof in it: you do not need to read it to trust those theorems.

Lifts `hooksCKAU` to an eager single-slot `KeySlot K` oracle (`hooksCKAUEager`, `eagerCKAKeyImpl`)
and reduces `CKA.branch cka Δcka 0 false (redCKAPrivUUniAll ...)` and
`FSAEAD.game fs (redFSPrivUni ...)` / `FSAEAD.advantage fs (redFSPrivUniCoin ...)` to aligned
post-initialization engine evaluations (`evalAfterInitU`, `evalAfterInitMU`,
`PrivL15.evalAfterInitCoin`).-/

set_option autoImplicit false

public section

open OracleComp OracleSpec ENNReal MeasureTheory CryptoGames.Lazy

namespace CryptoGames.SM.Construction

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

variable (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
  (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)

section Stage2SwitchBack

abbrev KeySpec (K : Type) : OracleSpec Unit := Unit →ₒ K

abbrev CKAKeySpec (Γ CCoins T I K : Type) := CKA.spec Γ CCoins T I + KeySpec K

@[expose] def queryKey {Γ CCoins T I K : Type} :
    OracleComp (unifSpec + CKAKeySpec Γ CCoins T I K) K :=
  query (spec := unifSpec + CKAKeySpec Γ CCoins T I K) (Sum.inr (Sum.inr ()))

@[expose] def liftCKAImpl {Γ CCoins T I K : Type} :
    QueryImpl (unifSpec + CKA.spec Γ CCoins T I)
      (OracleComp (unifSpec + CKAKeySpec Γ CCoins T I K))
  | Sum.inl n => query (spec := unifSpec + CKAKeySpec Γ CCoins T I K) (Sum.inl n)
  | Sum.inr q => query (spec := unifSpec + CKAKeySpec Γ CCoins T I K) (Sum.inr (Sum.inl q))

@[expose] def liftCKAComp {Γ CCoins T I K α : Type}
    (x : CKA.AdversaryComp Γ CCoins T I α) :
    OracleComp (unifSpec + CKAKeySpec Γ CCoins T I K) α :=
  simulateQ liftCKAImpl x

@[expose] def cacheCUEager {T I K : Type} (t : ℕ) (x : T × I) :
    Engine.HM (CKAKeySpec Γ CCoins T I K) (CKAUState T I K) Unit :=
  modify fun s => ({ s.1 with cache := Function.update s.1.cache t (some x) }, s.2)

@[expose] def hooksCKAUEager (mo : Mode) :
    Engine.Hooks (CKAKeySpec Γ CCoins T I K) (CKAUState T I K) Γ T Sig SS RS M E CCoins
      (Option Γ) Sig SS RS where
  startSend ctx P t γv σ r := do
    let s0 ← get
    match γv with
    | some γ =>
      let coins ← match r with
        | some c => pure c
        | none => StateT.lift (sampleT CCoins)
      let c := cka.send γ coins
      cacheCUEager t (c.2.1, c.2.2)
      let p := prng.up σ c.2.2
      let (kEpoch, kOpt1) ←
        if t = mo.tStar then do
          let kU ← StateT.lift queryKey
          pure (kU, some kU)
        else pure (p.2, s0.2)
      modify fun s => (s.1, kOpt1)
      return some (some c.1, c.2.1, p.1, fs.initSender kEpoch)
    | none =>
      StateT.mk fun s =>
        liftCKAComp (((hooksCKAU cka prng fs Δcka mo).startSend ctx P t none σ r).run s)
  startRecv ctx P t γv σ Tn :=
    StateT.mk fun s => liftCKAComp (((hooksCKAU cka prng fs Δcka mo).startRecv ctx P t γv σ Tn).run s)
  fsSend ctx P t ss h m pair :=
    StateT.mk fun s => liftCKAComp (((hooksCKAU cka prng fs Δcka mo).fsSend ctx P t ss h m pair).run s)
  fsRecv ctx P t rs h e rec :=
    StateT.mk fun s => liftCKAComp (((hooksCKAU cka prng fs Δcka mo).fsRecv ctx P t rs h e rec).run s)
  commit ctx P old new :=
    StateT.mk fun s => liftCKAComp (((hooksCKAU cka prng fs Δcka mo).commit ctx P old new).run s)
  reveal ctx P vp :=
    StateT.mk fun s => liftCKAComp (((hooksCKAU cka prng fs Δcka mo).reveal ctx P vp).run s)

@[expose] def initCKAUEager (mo : Mode) :
    Engine.HM (CKAKeySpec Γ CCoins T I K) (CKAUState T I K)
      (Option (PartyState (Option Γ) T Sig SS RS × PartyState (Option Γ) T Sig SS RS)) :=
  StateT.mk fun s => liftCKAComp ((initCKAU cka prng fs lam mo).run s)

abbrev CKAEagerState (Γ T K : Type) := CKA.GameState Γ T × PrivL15.KeySlot K

private def fillKeyCKA {Γ T K : Type} [SampleableType K] (_ : CKA.GameState Γ T) :
    PrivL15.KeySlot K → ProbComp (PrivL15.KeySlot K)
  | .unknown => PrivL15.KeySlot.ready <$> ($ᵗ K)
  | sl => pure sl

@[expose] def liftCKAM {Γ T K α : Type} (x : StateT (CKA.GameState Γ T) ProbComp α) :
    StateT (CKAEagerState Γ T K) ProbComp α :=
  StateT.mk fun s => (fun r => (r.1, (r.2, s.2))) <$> x.run s.1

@[expose] def drawKeyCKA {Γ T K : Type} [SampleableType K] :
    StateT (CKAEagerState Γ T K) ProbComp K :=
  StateT.mk fun s => (fun r => (r.1, (s.1, r.2))) <$> PrivL15.consumeKey s.2

private def realKeyOnlyImpl (Γ T K : Type) [SampleableType K] :
    QueryImpl (KeySpec K) (StateT (CKA.GameState Γ T) ProbComp) :=
  fun _ => liftM ($ᵗ K : ProbComp K)

@[expose] def eagerKeyOnlyImpl (Γ T K : Type) [SampleableType K] :
    QueryImpl (KeySpec K) (StateT (CKAEagerState Γ T K) ProbComp) :=
  fun _ => drawKeyCKA

private def realCKAKeyImpl
    (cka : CKAScheme KC Γ CCoins T I) (Δcka tstar : ℕ) :
    QueryImpl (CKAKeySpec Γ CCoins T I K) (StateT (CKA.GameState Γ T) ProbComp) :=
  (CKA.oracleImpl cka Δcka tstar :
      QueryImpl (CKA.spec Γ CCoins T I) (StateT (CKA.GameState Γ T) ProbComp)) +
    realKeyOnlyImpl Γ T K

@[expose] def eagerCKAKeyImpl
    (cka : CKAScheme KC Γ CCoins T I) (Δcka tstar : ℕ) :
    QueryImpl (CKAKeySpec Γ CCoins T I K) (StateT (CKAEagerState Γ T K) ProbComp) :=
  ((fun q => liftCKAM (CKA.oracleImpl cka Δcka tstar q)) :
      QueryImpl (CKA.spec Γ CCoins T I) (StateT (CKAEagerState Γ T K) ProbComp)) +
    eagerKeyOnlyImpl Γ T K

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I] in
private theorem fillKeyCKA_idem :
    Idem (fillKeyCKA (Γ := Γ) (T := T) (K := K)) := by
  intro _ sl
  cases sl <;>
    simp only [fillKeyCKA, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind] <;>
    exact DEq.refl _

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I] in
private theorem comm_liftCKAM {α : Type} (x : StateT (CKA.GameState Γ T) ProbComp α) :
    Comm (fillKeyCKA (Γ := Γ) (T := T) (K := K)) (liftCKAM x) := by
  rintro ⟨g, sl⟩
  have hfg : ∀ g' : CKA.GameState Γ T, fillKeyCKA (K := K) g' = fillKeyCKA g := fun _ => rfl
  simp only [fillSt, fillOut, liftCKAM, StateT.run_mk, map_eq_bind_pure_comp, bind_assoc,
    Function.comp_apply, pure_bind, hfg]
  refine (DEq.swap _ _ _).trans ?_
  refine DEq.bind_right _ fun r => ?_
  have := DEq.bind_left (fillKeyCKA_idem g sl)
    (fun y => pure (r.1, r.2, y))
  simpa only [bind_assoc] using this

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I] in
private theorem comm_drawKeyCKA :
    Comm (fillKeyCKA (Γ := Γ) (T := T) (K := K)) drawKeyCKA := by
  rintro ⟨g, sl⟩
  cases sl <;>
    simp only [fillSt, fillOut, fillKeyCKA, drawKeyCKA, PrivL15.consumeKey, StateT.run_mk,
      map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind] <;>
    exact DEq.refl _

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] in
private theorem comm_eagerCKAKeyImpl (tstar : ℕ)
    (q : (unifSpec + CKAKeySpec Γ CCoins T I K).Domain) :
    Comm (fillKeyCKA (Γ := Γ) (T := T) (K := K))
      (PrivL15.outerFull (eagerCKAKeyImpl cka Δcka tstar) q) := by
  rcases q with n | (q | _)
  · exact comm_liftCKAM (query (spec := unifSpec) n)
  · exact comm_liftCKAM (CKA.oracleImpl cka Δcka tstar q)
  · exact comm_drawKeyCKA (K := K)

private def StepNRCKA {Γ T K α : Type}
    (m₁ : StateT (CKAEagerState Γ T K) ProbComp α)
    (m₂ : StateT (CKA.GameState Γ T) ProbComp α) : Prop :=
  ∀ g sl, PrivL15.NonReady sl →
    Prod.map id Prod.fst <$> m₁.run (g, sl) = m₂.run g ∧
    ∀ z ∈ support (m₁.run (g, sl)), PrivL15.NonReady z.2.2

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
private theorem stepNRCKA_liftCKAM {α : Type} (x : StateT (CKA.GameState Γ T) ProbComp α) :
    StepNRCKA (K := K) (liftCKAM x) x := by
  intro g sl hsl
  refine ⟨by simp [liftCKAM], ?_⟩
  intro z hz
  simp only [liftCKAM, StateT.run_mk, support_map, Set.mem_image] at hz
  rcases hz with ⟨_, _, rfl⟩
  exact hsl

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I] in
private theorem stepNRCKA_drawKeyCKA :
    StepNRCKA (Γ := Γ) (T := T) (K := K) drawKeyCKA (liftM ($ᵗ K : ProbComp K)) := by
  intro g sl hsl
  have hc := PrivL15.consumeKey_of_nonReady hsl
  refine ⟨by simp [drawKeyCKA, hc, StateT.run_monadLift, map_eq_bind_pure_comp], ?_⟩
  intro z hz
  simp only [drawKeyCKA, hc, StateT.run_mk, support_map, Set.mem_image] at hz
  rcases hz with ⟨_, ⟨_, _, rfl⟩, rfl⟩
  trivial

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] in
private theorem eagerCKAKeyImpl_step (tstar : ℕ)
    (q : (unifSpec + CKAKeySpec Γ CCoins T I K).Domain) :
    StepNRCKA (PrivL15.outerFull (eagerCKAKeyImpl cka Δcka tstar) q)
      (PrivL15.outerFull (realCKAKeyImpl cka Δcka tstar) q) := by
  rcases q with n | (q | _)
  · exact stepNRCKA_liftCKAM (query (spec := unifSpec) n)
  · exact stepNRCKA_liftCKAM (CKA.oracleImpl cka Δcka tstar q)
  · exact stepNRCKA_drawKeyCKA

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] in
private theorem simulateQ_eagerCKAKeyImpl_nonReady {α : Type} (tstar : ℕ)
    (oa : OracleComp (unifSpec + CKAKeySpec Γ CCoins T I K) α) :
    ∀ (s : CKAEagerState Γ T K), PrivL15.NonReady s.2 →
      Prod.map id Prod.fst <$>
        (simulateQ (PrivL15.outerFull (eagerCKAKeyImpl cka Δcka tstar)) oa).run s =
      (simulateQ (PrivL15.outerFull (realCKAKeyImpl cka Δcka tstar)) oa).run s.1 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s _
    simp
  | query_bind q k ih =>
    intro ⟨g, sl⟩ hsl
    obtain ⟨h1, h2⟩ := eagerCKAKeyImpl_step cka Δcka tstar q g sl hsl
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, map_bind]
    rw [← h1, bind_map_left]
    exact bind_congr_of_forall_mem_support _ fun z hz => ih z.1 z.2 (h2 z hz)

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] in
private theorem simulateQ_realCKAKeyImpl_liftCKAComp {α : Type} (tstar : ℕ)
    (x : CKA.AdversaryComp Γ CCoins T I α) :
    simulateQ (PrivL15.outerFull (realCKAKeyImpl cka Δcka tstar)) (liftCKAComp (K := K) x) =
      simulateQ (PrivL15.outerFull (CKA.oracleImpl cka Δcka tstar)) x := by
  induction x using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q k ih =>
    rcases q with n | q
    · simp only [liftCKAComp, simulateQ_bind, liftCKAImpl,
        simulateQ_query, PrivL15.outerFull]
      exact congrArg (_ >>= ·) (funext ih)
    · simp only [liftCKAComp, simulateQ_bind, liftCKAImpl,
        simulateQ_query, PrivL15.outerFull, realCKAKeyImpl]
      exact congrArg (_ >>= ·) (funext ih)

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] in
private theorem simulateQ_realCKAKeyImpl_queryKey (tstar : ℕ) :
    simulateQ (PrivL15.outerFull (realCKAKeyImpl cka Δcka tstar))
      (queryKey (Γ := Γ) (CCoins := CCoins) (T := T) (I := I) (K := K)) =
    simulateQ (PrivL15.outerFull (CKA.oracleImpl cka Δcka tstar)) (sampleT K) := by
  ext os
  rw [PrivL15.simulateQ_outerFull_sampleT]
  simp [queryKey, PrivL15.outerFull, realCKAKeyImpl, realKeyOnlyImpl]

/-! ### Section B: Unified engine outcomes and reduction unfoldings -/

@[expose] def privOutUni {VPt C HS : Type} (Δ t : ℕ) (b b' : Bool)
    (es : Engine.EState VPt M C HS) : ProbComp Bool :=
  if privValidUni Δ t es then pure (b == b') else ($ᵗ Bool : ProbComp Bool)

@[expose] def fsPrivOutUni {VPt C HS : Type} (Δ t : ℕ) (b b' : Bool)
    (es : Engine.EState VPt M C HS) (win : Bool) : ProbComp Bool :=
  if win then pure true else privOutUni Δ t b b' es

@[expose] def evalEngU {ι : Type} {tspec : OracleSpec.{0, 0} ι} {OS Γv Sv SSv RSv HS : Type}
    (oimpl : QueryImpl tspec (StateT OS ProbComp))
    (hk : Engine.Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip t : ℕ) (π : Engine.Policy) (b : Bool)
    (oa : OracleComp (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) Bool)
    (s : Engine.EState (Engine.VP Γv T Sv SSv RSv) M (Header T × E) HS × OS) : ProbComp Bool :=
  PrivL15.runEM oimpl (simulateQ (Engine.implE hk Δ qep maxSkip (Config.priv t) π) oa) s >>=
    fun r => privOutUni Δ t b r.1 r.2.1

@[expose] def evalEngMU {Γv Sv SSv RSv HS : Type}
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (hk : Engine.Hooks (FSAEAD.spec SS RS (Header T) M E) HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip t : ℕ) (π : Engine.Policy) (b : Bool)
    (oa : OracleComp (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) Bool)
    (s : Engine.EState (Engine.VP Γv T Sv SSv RSv) M (Header T × E) HS ×
      FSAEAD.State SS RS (Header T) M E) : ProbComp Bool :=
  PrivL15.runEM (FSAEAD.oracleImpl fs)
      (simulateQ (Engine.implE hk Δ qep maxSkip (Config.priv t) π) oa) s >>=
    fun r => fsPrivOutUni Δ t b r.1 r.2.1 r.2.2.win

@[expose] def evalAfterInitU {ι : Type} {tspec : OracleSpec.{0, 0} ι} {OS Γv Sv SSv RSv HS : Type}
    (oimpl : QueryImpl tspec (StateT OS ProbComp))
    (hk : Engine.Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip t : ℕ) (π : Engine.Policy) (b : Bool)
    (oa : OracleComp (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) Bool)
    (r : (Option (Engine.VP Γv T Sv SSv RSv × Engine.VP Γv T Sv SSv RSv) × HS) × OS) :
    ProbComp Bool :=
  match r.1.1 with
  | none => ($ᵗ Bool : ProbComp Bool)
  | some (vA, vB) =>
    evalEngU oimpl hk Δ qep maxSkip t π b oa
      ({ g := { st := fun P => match P with | .A => vA | .B => vB, b },
         h := r.1.2 }, r.2)

@[expose] def evalAfterInitMU {Γv Sv SSv RSv HS : Type}
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (hk : Engine.Hooks (FSAEAD.spec SS RS (Header T) M E) HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip t : ℕ) (π : Engine.Policy) (b b₀ : Bool)
    (oa : OracleComp (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) Bool)
    (r : (Option (Engine.VP Γv T Sv SSv RSv × Engine.VP Γv T Sv SSv RSv) × HS) ×
      FSAEAD.State SS RS (Header T) M E) : ProbComp Bool :=
  match r.1.1 with
  | none => if r.2.win then pure true else ($ᵗ Bool : ProbComp Bool)
  | some (vA, vB) =>
    evalEngMU fs hk Δ qep maxSkip t π b oa
      ({ g := { st := fun P => match P with | .A => vA | .B => vB, b := b₀ },
         h := r.1.2 }, r.2)

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
  [SampleableType I] [SampleableType K] in
theorem evalEngU_pure {ι : Type} {tspec : OracleSpec.{0, 0} ι} {OS Γv Sv SSv RSv HS : Type}
    (oimpl : QueryImpl tspec (StateT OS ProbComp))
    (hk : Engine.Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip t : ℕ) (π : Engine.Policy) (b b' : Bool)
    (s : Engine.EState (Engine.VP Γv T Sv SSv RSv) M (Header T × E) HS × OS) :
    evalEngU oimpl hk Δ qep maxSkip t π b (pure b') s = privOutUni Δ t b b' s.1 := by
  simp [evalEngU, PrivL15.runEM_pure]

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
  [SampleableType I] [SampleableType K] in
theorem evalEngMU_pure {Γv Sv SSv RSv HS : Type}
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (hk : Engine.Hooks (FSAEAD.spec SS RS (Header T) M E) HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip t : ℕ) (π : Engine.Policy) (b b' : Bool)
    (s : Engine.EState (Engine.VP Γv T Sv SSv RSv) M (Header T × E) HS ×
      FSAEAD.State SS RS (Header T) M E) :
    evalEngMU fs hk Δ qep maxSkip t π b (pure b') s = fsPrivOutUni Δ t b b' s.1 s.2.win := by
  simp [evalEngMU, PrivL15.runEM_pure]

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
  [SampleableType I] [SampleableType K] in
theorem evalEngU_query_bind {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {OS Γv Sv SSv RSv HS : Type}
    (oimpl : QueryImpl tspec (StateT OS ProbComp))
    (hk : Engine.Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip t : ℕ) (π : Engine.Policy) (b : Bool)
    (q : (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Domain)
    (k : (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Range q →
      OracleComp (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) Bool)
    (s : Engine.EState (Engine.VP Γv T Sv SSv RSv) M (Header T × E) HS × OS) :
    evalEngU oimpl hk Δ qep maxSkip t π b (liftM (OracleSpec.query q) >>= k) s =
      PrivL15.runEM oimpl (Engine.implE hk Δ qep maxSkip (Config.priv t) π q) s >>=
        fun r => evalEngU oimpl hk Δ qep maxSkip t π b (k r.1) r.2 := by
  simp [evalEngU, simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
    id_map, PrivL15.runEM_bind, bind_assoc]

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
  [SampleableType I] [SampleableType K] in
theorem evalEngMU_query_bind {Γv Sv SSv RSv HS : Type}
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (hk : Engine.Hooks (FSAEAD.spec SS RS (Header T) M E) HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip t : ℕ) (π : Engine.Policy) (b : Bool)
    (q : (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Domain)
    (k : (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Range q →
      OracleComp (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) Bool)
    (s : Engine.EState (Engine.VP Γv T Sv SSv RSv) M (Header T × E) HS ×
      FSAEAD.State SS RS (Header T) M E) :
    evalEngMU fs hk Δ qep maxSkip t π b (liftM (OracleSpec.query q) >>= k) s =
      PrivL15.runEM (FSAEAD.oracleImpl fs) (Engine.implE hk Δ qep maxSkip (Config.priv t) π q) s >>=
        fun r => evalEngMU fs hk Δ qep maxSkip t π b (k r.1) r.2 := by
  simp [evalEngMU, simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
    id_map, PrivL15.runEM_bind, bind_assoc]

omit [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
private theorem evalDist_fsPrivOutUni_step {VPt C HS : Type} (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δ t : ℕ) (b b' : Bool) (es : Engine.EState VPt M C HS)
    (st : FSAEAD.State SS RS (Header T) M E) :
    𝒟[((simulateQ (PrivL15.fsFullImpl fs)
          (if privValidUni Δ t es then pure b' else sampleT Bool)).run st : ProbComp _) >>=
        fun z => pure (b == z.1 || z.2.win)] =
      𝒟[fsPrivOutUni Δ t b b' es st.win] := by
  cases hwin : st.win
  · cases hv : privValidUni Δ t es
    · simp only [hv, Bool.false_eq_true, ↓reduceIte, fsPrivOutUni, privOutUni,
        PrivL15.evalDist_sampleT_bool_run, bind_map_left, hwin, Bool.or_false]
      simpa only [Bool.beq_comm] using PrivL15.evalDist_uniformBool_beq b
    · simp [fsPrivOutUni, privOutUni, hwin, hv]
  · cases hv : privValidUni Δ t es
    · simp only [Bool.false_eq_true, ↓reduceIte, fsPrivOutUni,
        PrivL15.evalDist_sampleT_bool_run, bind_map_left, hwin, Bool.or_true]
      exact (DEq.bind_const ($ᵗ Bool) (pure true)).evalDist_eq
    · simp [fsPrivOutUni, hwin]

theorem evalDist_game_redFSPrivUni (t : ℕ)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    𝒟[FSAEAD.game fs (redFSPrivUni cka prng fs lam Δcka qep t A)] =
    𝒟[do
      let b ← ($ᵗ Bool : ProbComp Bool)
      let k ← ($ᵗ K : ProbComp K)
      let r ← PrivL15.runHM (FSAEAD.oracleImpl fs) (initFS cka prng fs lam ⟨false, none, t⟩ 0)
        ({} : FSState T Sig K I SS RS E) (FSAEAD.initState fs k b)
      evalAfterInitMU fs (hooksFS cka prng fs Δcka ⟨false, none, t⟩ 0)
        (2 + Δcka) qep fs.maxSkip t (polUni12 Δcka t) b false A r] := by
  unfold FSAEAD.game redFSPrivUni runFSUni
  refine evalDist_bind_congr _ _ _ fun b => evalDist_bind_congr _ _ _ fun k => ?_
  change 𝒟[(simulateQ (PrivL15.fsFullImpl fs) _).run (FSAEAD.initState fs k b) >>=
    fun z => pure (b == z.1 || z.2.win)] = _
  simp only [Engine.engRun, simulateQ_bind, StateT.run_bind, bind_assoc, PrivL15.runHM]
  refine evalDist_bind_congr _ _ _ fun ⟨⟨vs, h⟩, os₁⟩ => ?_
  cases vs with
  | none =>
    cases hwin : os₁.win
    · simp only [evalAfterInitMU, hwin, Bool.false_eq_true, ↓reduceIte,
        simulateQ_pure, StateT.run_pure, pure_bind,
        PrivL15.evalDist_sampleT_bool_run, bind_map_left, Bool.or_false]
      simpa only [Bool.beq_comm] using PrivL15.evalDist_uniformBool_beq b
    · simp only [evalAfterInitMU, hwin, ↓reduceIte,
        simulateQ_pure, StateT.run_pure, pure_bind,
        PrivL15.evalDist_sampleT_bool_run, bind_map_left, Bool.or_true]
      exact (DEq.bind_const ($ᵗ Bool) (pure true)).evalDist_eq
  | some vAvB =>
    rcases vAvB with ⟨vA, vB⟩
    simp only [evalAfterInitMU, evalEngMU, PrivL15.runEM, simulateQ_bind, StateT.run_bind,
      bind_assoc, simulateQ_pure, StateT.run_pure, pure_bind, bind_map_left]
    exact evalDist_bind_congr _ _ _ fun ⟨⟨b', es⟩, st⟩ =>
      evalDist_fsPrivOutUni_step fs (2 + Δcka) t b b' es st

theorem advantage_redFSPrivUniCoin (t : ℕ)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    FSAEAD.advantage fs (redFSPrivUniCoin cka prng fs lam Δcka qep t A) =
    𝒟[do
      let b ← ($ᵗ Bool : ProbComp Bool)
      let k ← ($ᵗ K : ProbComp K)
      let r ← PrivL15.runHM (FSAEAD.oracleImpl fs) (initFS cka prng fs lam ⟨false, none, t⟩ 0)
        ({} : FSState T Sig K I SS RS E) (FSAEAD.initState fs k b)
      PrivL15.evalAfterInitCoin fs (hooksFS cka prng fs Δcka ⟨false, none, t⟩ 0)
        (2 + Δcka) qep fs.maxSkip (Config.priv t) (polUni12 Δcka t) false A r] {true} := by
  unfold FSAEAD.advantage FSAEAD.game redFSPrivUniCoin runFSUni
  have hdist :
      𝒟[do
        let b ← ($ᵗ Bool : ProbComp Bool)
        let k ← ($ᵗ K : ProbComp K)
        let (b', st) ← (simulateQ (PrivL15.fsFullImpl fs) (do
          let _ ← Engine.engRun (hooksFS cka prng fs Δcka ⟨false, none, t⟩ 0) (2 + Δcka) qep
            fs.maxSkip (Config.priv t) (polUni12 Δcka t) (initFS cka prng fs lam ⟨false, none, t⟩ 0)
            {} false A
          sampleT Bool)).run (FSAEAD.initState fs k b)
        pure (b == b' || st.win)] =
      𝒟[(do
        let b ← ($ᵗ Bool : ProbComp Bool)
        let k ← ($ᵗ K : ProbComp K)
        let r ← PrivL15.runHM (FSAEAD.oracleImpl fs) (initFS cka prng fs lam ⟨false, none, t⟩ 0)
          ({} : FSState T Sig K I SS RS E) (FSAEAD.initState fs k b)
        PrivL15.evalAfterInitCoin fs (hooksFS cka prng fs Δcka ⟨false, none, t⟩ 0)
          (2 + Δcka) qep fs.maxSkip (Config.priv t) (polUni12 Δcka t) false A r) >>= fun w =>
        if w then pure true else ($ᵗ Bool : ProbComp Bool)] := by
    conv_rhs => simp only [bind_assoc]
    refine evalDist_bind_congr _ _ _ fun b => evalDist_bind_congr _ _ _ fun k => ?_
    simp only [Engine.engRun, simulateQ_bind, StateT.run_bind, bind_assoc, PrivL15.runHM]
    refine evalDist_bind_congr _ _ _ fun ⟨⟨vs, h⟩, os₁⟩ => ?_
    cases vs with
    | none =>
      simp only [PrivL15.evalAfterInitCoin, simulateQ_pure, StateT.run_pure, pure_bind]
      exact PrivL15.evalDist_coin_or_win fs b os₁
    | some vAvB =>
      rcases vAvB with ⟨vA, vB⟩
      simp only [PrivL15.evalAfterInitCoin, PrivL15.evalEngL, PrivL15.runEM, simulateQ_bind,
        StateT.run_bind, bind_assoc, simulateQ_pure, StateT.run_pure, pure_bind, bind_map_left]
      exact evalDist_bind_congr _ _ _ fun ⟨_, st⟩ =>
        PrivL15.evalDist_coin_or_win fs b st
  exact (congrArg Measure.boolBias hdist).trans (PrivL15.boolBias_coin_or_win _)

omit [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] in
private theorem runHM_hooksCKAUEager_startSend (mo : Mode)
    (ctx : Engine.Ctx (Option Γ) T Sig SS RS M E) (P : Party) (t' : ℕ)
    (γv : Option Γ) (σ : Sig) (r : Option CCoins)
    (h : CKAUState T I K) (os : CKA.GameState Γ T) :
    PrivL15.runHM (realCKAKeyImpl cka Δcka 0)
      ((hooksCKAUEager cka prng fs Δcka mo).startSend ctx P t' γv σ r) h os =
    PrivL15.runHM (CKA.oracleImpl cka Δcka 0)
      ((hooksCKAU cka prng fs Δcka mo).startSend ctx P t' γv σ r) h os := by
  cases γv with
  | none =>
    simp [hooksCKAUEager, PrivL15.runHM, simulateQ_realCKAKeyImpl_liftCKAComp]
  | some γ =>
    cases r <;> by_cases ht : t' = mo.tStar <;>
      simp [hooksCKAUEager, hooksCKAU, cacheCUEager, cacheCU, PrivL15.runHM, ht,
        StateT.run_bind, simulateQ_bind, PrivL15.simulateQ_outerFull_sampleT,
        simulateQ_realCKAKeyImpl_queryKey]

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] in
private theorem runEM_implE_hooksCKAUEager (mo : Mode) (t : ℕ) (π : Engine.Policy)
    (q : (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Domain)
    (s : Engine.EState (Engine.VP (Option Γ) T Sig SS RS) M (Header T × E) (CKAUState T I K) ×
      CKA.GameState Γ T) :
    PrivL15.runEM (realCKAKeyImpl cka Δcka 0)
      (Engine.implE (hooksCKAUEager cka prng fs Δcka mo) (2 + Δcka) qep fs.maxSkip (Config.priv t) π q) s =
    PrivL15.runEM (CKA.oracleImpl cka Δcka 0)
      (Engine.implE (hooksCKAU cka prng fs Δcka mo) (2 + Δcka) qep fs.maxSkip (Config.priv t) π q) s := by
  have hlift : ∀ {α : Type}
      (xE : Engine.HM (CKAKeySpec Γ CCoins T I K) (CKAUState T I K) α)
      (xR : Engine.HM (CKA.spec Γ CCoins T I) (CKAUState T I K) α)
      (es : Engine.EState (Engine.VP (Option Γ) T Sig SS RS) M (Header T × E) (CKAUState T I K))
      (os : CKA.GameState Γ T),
      PrivL15.runHM (realCKAKeyImpl cka Δcka 0) xE es.h os =
        PrivL15.runHM (CKA.oracleImpl cka Δcka 0) xR es.h os →
      PrivL15.runEM (realCKAKeyImpl cka Δcka 0) (Engine.liftH xE) (es, os) =
        PrivL15.runEM (CKA.oracleImpl cka Δcka 0) (Engine.liftH xR) (es, os) := by
    intro α xE xR es os hEq
    simp only [PrivL15.runEM, PrivL15.StateT_run_liftH, simulateQ_bind, StateT.run_bind,
      simulateQ_pure, StateT.run_pure, PrivL15.runHM] at hEq ⊢
    rw [hEq]
  have hbind : ∀ {α β : Type}
      (m : Engine.HM (CKA.spec Γ CCoins T I) (CKAUState T I K) α)
      (kE : α → Engine.HM (CKAKeySpec Γ CCoins T I K) (CKAUState T I K) β)
      (kR : α → Engine.HM (CKA.spec Γ CCoins T I) (CKAUState T I K) β)
      (h : CKAUState T I K) (os : CKA.GameState Γ T),
      (∀ a h' os',
        PrivL15.runHM (realCKAKeyImpl cka Δcka 0) (kE a) h' os' =
          PrivL15.runHM (CKA.oracleImpl cka Δcka 0) (kR a) h' os') →
      PrivL15.runHM (realCKAKeyImpl cka Δcka 0)
        (StateT.mk (fun s => liftCKAComp (m.run s)) >>= kE) h os =
      PrivL15.runHM (CKA.oracleImpl cka Δcka 0) (m >>= kR) h os := by
    intro α β m kE kR h os hk
    simp only [PrivL15.runHM, StateT.run_bind, simulateQ_bind, StateT.run_mk,
      simulateQ_realCKAKeyImpl_liftCKAComp (K := K)]
    exact bind_congr fun ⟨⟨a, h'⟩, os'⟩ => hk a h' os'
  have hbindHM : ∀ {α β : Type}
      (mE : Engine.HM (CKAKeySpec Γ CCoins T I K) (CKAUState T I K) α)
      (mR : Engine.HM (CKA.spec Γ CCoins T I) (CKAUState T I K) α)
      (kE : α → Engine.HM (CKAKeySpec Γ CCoins T I K) (CKAUState T I K) β)
      (kR : α → Engine.HM (CKA.spec Γ CCoins T I) (CKAUState T I K) β)
      (h : CKAUState T I K) (os : CKA.GameState Γ T),
      PrivL15.runHM (realCKAKeyImpl cka Δcka 0) mE h os =
        PrivL15.runHM (CKA.oracleImpl cka Δcka 0) mR h os →
      (∀ a h' os',
        PrivL15.runHM (realCKAKeyImpl cka Δcka 0) (kE a) h' os' =
          PrivL15.runHM (CKA.oracleImpl cka Δcka 0) (kR a) h' os') →
      PrivL15.runHM (realCKAKeyImpl cka Δcka 0) (mE >>= kE) h os =
        PrivL15.runHM (CKA.oracleImpl cka Δcka 0) (mR >>= kR) h os := by
    intro α β mE mR kE kR h os hm hk
    simp only [PrivL15.runHM, StateT.run_bind, simulateQ_bind] at hm ⊢
    rw [hm]
    exact bind_congr fun ⟨⟨a, h'⟩, os'⟩ => hk a h' os'
  have hvSend : ∀ (s₁ : Engine.Ctx (Option Γ) T Sig SS RS M E) (P : Party) (m : M)
      (pair : Option (M × M)) (r : Option CCoins)
      (s0 : Engine.EState (Engine.VP (Option Γ) T Sig SS RS) M (Header T × E) (CKAUState T I K) ×
        CKA.GameState Γ T),
      PrivL15.runEM (realCKAKeyImpl cka Δcka 0)
        (Engine.liftH (Engine.vSend (hooksCKAUEager cka prng fs Δcka mo) s₁ P (s₁.st P) m pair r)) s0 =
      PrivL15.runEM (CKA.oracleImpl cka Δcka 0)
        (Engine.liftH (Engine.vSend (hooksCKAU cka prng fs Δcka mo) s₁ P (s₁.st P) m pair r)) s0 := by
    intro s₁ P m pair r ⟨es, os⟩
    apply hlift
    unfold Engine.vSend
    split_ifs
    · refine hbindHM _ _ _ _ es.h os
        (runHM_hooksCKAUEager_startSend cka prng fs Δcka mo s₁ P
          ((s₁.st P).tcur + 1) (s₁.st P).γ (s₁.st P).root r es.h os)
        fun ans h₁ os₁ => ?_
      rcases ans with _ | ⟨γ', T', σ', ss⟩
      · simp [PrivL15.runHM]
      · simp only [pure_bind]
        exact hbind _ _ _ h₁ os₁ fun a _ _ => by
          rcases a with _ | ⟨_, _⟩ <;> simp [PrivL15.runHM]
    · simp only [pure_bind]
      cases (s₁.st P).vS with
      | none => simp [PrivL15.runHM]
      | some ss =>
        exact hbind _ _ _ es.h os fun a _ _ => by rcases a with _ | ⟨_, _⟩ <;> simp [PrivL15.runHM]
  have hvRecv : ∀ (g : Engine.Ctx (Option Γ) T Sig SS RS M E) (P : Party) (c : Header T × E)
      (rec : Option (Record M (Header T × E)))
      (s0 : Engine.EState (Engine.VP (Option Γ) T Sig SS RS) M (Header T × E) (CKAUState T I K) ×
        CKA.GameState Γ T),
      PrivL15.runEM (realCKAKeyImpl cka Δcka 0)
        (Engine.liftH (Engine.vRecv (hooksCKAUEager cka prng fs Δcka mo) g P (g.st P) c rec)) s0 =
      PrivL15.runEM (CKA.oracleImpl cka Δcka 0)
        (Engine.liftH (Engine.vRecv (hooksCKAU cka prng fs Δcka mo) g P (g.st P) c rec)) s0 := by
    intro g P c rec ⟨es, os⟩
    apply hlift
    dsimp only [Engine.vRecv]
    split_ifs
    · simp [PrivL15.runHM]
    · cases c.1.2
      · simp [PrivL15.runHM]
      · refine hbind _ _ _ es.h os fun res h₁ os₁ => ?_
        rcases res with _ | _ | ⟨γ', σ', rs⟩
        · simp [PrivL15.runHM]
        · simp [PrivL15.runHM]
        · simp only [pure_bind, Function.update_self]
          exact hbind _ _ _ h₁ os₁ fun a _ _ => by
            rcases a with _ | _ | ⟨_, _, _⟩ <;> simp [PrivL15.runHM]
    · simp only [pure_bind]
      cases (g.st P).vR c.1.1 with
      | none => simp [PrivL15.runHM]
      | some rs =>
        exact hbind _ _ _ es.h os fun a _ _ => by
          rcases a with _ | _ | ⟨_, _, _⟩ <;> simp [PrivL15.runHM]
  have hpure : ∀ {α : Type} (a : α)
      (s0 : Engine.EState (Engine.VP (Option Γ) T Sig SS RS) M (Header T × E) (CKAUState T I K) ×
        CKA.GameState Γ T),
      PrivL15.runEM (realCKAKeyImpl (K := K) cka Δcka 0) (pure a) s0 =
      PrivL15.runEM (CKA.oracleImpl cka Δcka 0) (pure a) s0 :=
    fun _ _ => rfl
  have hget : ∀
      (s0 : Engine.EState (Engine.VP (Option Γ) T Sig SS RS) M (Header T × E) (CKAUState T I K) ×
        CKA.GameState Γ T),
      PrivL15.runEM (realCKAKeyImpl (K := K) cka Δcka 0) get s0 =
      PrivL15.runEM (CKA.oracleImpl cka Δcka 0) get s0 :=
    fun _ => rfl
  have hmod : ∀ f
      (s0 : Engine.EState (Engine.VP (Option Γ) T Sig SS RS) M (Header T × E) (CKAUState T I K) ×
        CKA.GameState Γ T),
      PrivL15.runEM (realCKAKeyImpl (K := K) cka Δcka 0) (modify f) s0 =
      PrivL15.runEM (CKA.oracleImpl cka Δcka 0) (modify f) s0 :=
    fun _ _ => rfl
  have habort : ∀ s0,
      PrivL15.runEM (realCKAKeyImpl (K := K) cka Δcka 0)
        (Engine.abortE : Engine.EM (CKAKeySpec Γ CCoins T I K) (Option Γ) T Sig SS RS M E (CKAUState T I K) Unit) s0 =
      PrivL15.runEM (CKA.oracleImpl cka Δcka 0)
        (Engine.abortE : Engine.EM (CKA.spec Γ CCoins T I) (Option Γ) T Sig SS RS M E (CKAUState T I K) Unit) s0 :=
    fun s0 => hmod _ s0
  have hebind : ∀ {α β : Type}
      (mE : Engine.EM (CKAKeySpec Γ CCoins T I K) (Option Γ) T Sig SS RS M E (CKAUState T I K) α)
      (mR : Engine.EM (CKA.spec Γ CCoins T I) (Option Γ) T Sig SS RS M E (CKAUState T I K) α)
      (kE : α → Engine.EM (CKAKeySpec Γ CCoins T I K) (Option Γ) T Sig SS RS M E (CKAUState T I K) β)
      (kR : α → Engine.EM (CKA.spec Γ CCoins T I) (Option Γ) T Sig SS RS M E (CKAUState T I K) β),
      (∀ s0, PrivL15.runEM (realCKAKeyImpl (K := K) cka Δcka 0) mE s0 =
        PrivL15.runEM (CKA.oracleImpl cka Δcka 0) mR s0) →
      (∀ a s0, PrivL15.runEM (realCKAKeyImpl (K := K) cka Δcka 0) (kE a) s0 =
        PrivL15.runEM (CKA.oracleImpl cka Δcka 0) (kR a) s0) →
      ∀ s0, PrivL15.runEM (realCKAKeyImpl (K := K) cka Δcka 0) (mE >>= kE) s0 =
        PrivL15.runEM (CKA.oracleImpl cka Δcka 0) (mR >>= kR) s0 := by
    intro α β mE mR kE kR hm hk s0
    simp only [PrivL15.runEM_bind, hm s0]
    exact bind_congr fun ⟨a, s'⟩ => hk a s'
  have hcommit : ∀ ctx P old new pos s0,
      PrivL15.runEM (realCKAKeyImpl (K := K) cka Δcka 0)
        (Engine.commitE (hooksCKAUEager cka prng fs Δcka mo) ctx P old new pos) s0 =
      PrivL15.runEM (CKA.oracleImpl cka Δcka 0)
        (Engine.commitE (hooksCKAU cka prng fs Δcka mo) ctx P old new pos) s0 := by
    intro ctx P old new pos
    dsimp only [Engine.commitE]
    refine hebind _ _ _ _ (fun ⟨es, os⟩ => hlift _ _ es os (by
      simp [hooksCKAUEager, PrivL15.runHM, simulateQ_realCKAKeyImpl_liftCKAComp (K := K)])) ?_
    rintro (_ | new')
    · exact hebind _ _ _ _ habort fun _ => hpure _
    · exact hpure _
  rcases q with n | ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
  · simp [PrivL15.runEM, Engine.implE, Engine.coinsE, PrivL15.outerFull, StateT.run_lift]
  · change PrivL15.runEM _ (Engine.transmitE _ _ _ _ (P, m, r)) s =
        PrivL15.runEM _ (Engine.transmitE _ _ _ _ (P, m, r)) s
    dsimp only [Engine.transmitE]
    refine hebind _ _ _ _ hget (fun es => ?_) s
    split_ifs
    · exact hpure _
    · rcases es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁
      · exact hpure _
      · dsimp only
        split_ifs
        · exact hebind _ _ _ _ habort (fun _ => hpure _)
        · refine hebind _ _ _ _ (hvSend s₁ P m none r) (fun x => ?_)
          rcases x with _ | ⟨st', c'⟩
          · exact hebind _ _ _ _ habort (fun _ => hpure _)
          · exact hebind _ _ _ _ (hmod _) (fun _ => hpure _)
  · change PrivL15.runEM _ (Engine.challE _ _ _ _ _ (P, m₀, m₁, r)) s =
        PrivL15.runEM _ (Engine.challE _ _ _ _ _ (P, m₀, m₁, r)) s
    dsimp only [Engine.challE]
    refine hebind _ _ _ _ hget (fun es => ?_) s
    cases es.abort || es.g.win
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rcases es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁
      · exact hpure _
      · dsimp only
        split_ifs
        · exact hpure _
        · exact hebind _ _ _ _ habort (fun _ => hpure _)
        · refine hebind _ _ _ _ (hvSend s₁ P _ (some (m₀, m₁)) r) (fun x => ?_)
          rcases x with _ | ⟨st', c'⟩
          · exact hebind _ _ _ _ habort (fun _ => hpure _)
          · exact hebind _ _ _ _ (hmod _) (fun _ => hpure _)
        · refine hebind _ _ _ _ (hvSend s₁ P _ (some (m₀, m₁)) r) (fun x => ?_)
          rcases x with _ | ⟨st', c'⟩
          · exact hebind _ _ _ _ habort (fun _ => hpure _)
          · exact hebind _ _ _ _ (hmod _) (fun _ => hpure _)
    · simp only [↓reduceIte]
      exact hpure _
  · change PrivL15.runEM _ (Engine.deliverE _ _ _ (P, c)) s =
        PrivL15.runEM _ (Engine.deliverE _ _ _ (P, c)) s
    dsimp only [Engine.deliverE]
    refine hebind _ _ _ _ hget (fun es => ?_) s
    split_ifs
    · exact hpure _
    · rcases es.g.inTransit P.other c with _ | rec
      · exact hpure _
      · dsimp only
        refine hebind _ _ _ _ (hvRecv es.g P c (some rec)) (fun x => ?_)
        rcases x with _ | _ | ⟨st', t', i', m'⟩
        · exact hebind _ _ _ _ habort (fun _ => hpure _)
        · dsimp only
          split_ifs
          · exact hebind _ _ _ _ (hmod _) (fun _ => hpure _)
          · exact hpure _
        · refine hebind _ _ _ _ (hcommit es.g P (es.g.st P) st' rec.pos) (fun y => ?_)
          rcases y with _ | s₁
          · exact hpure _
          · exact hebind _ _ _ _ (hmod _) (fun _ => hpure _)
  · change PrivL15.runEM _ (Engine.injectE _ _ _ _ (P, c)) s =
        PrivL15.runEM _ (Engine.injectE _ _ _ _ (P, c)) s
    dsimp only [Engine.injectE]
    refine hebind _ _ _ _ hget (fun es => ?_) s
    split_ifs
    · exact hpure _
    · refine hebind _ _ _ _ (hvRecv es.g P c none) (fun x => ?_)
      rcases x with _ | _ | ⟨st', t', i', m'⟩
      · exact hebind _ _ _ _ habort (fun _ => hpure _)
      · exact hpure _
      · dsimp only
        split_ifs
        · exact hpure _
        · refine hebind _ _ _ _ (hcommit es.g P (es.g.st P) st' ⟨P.other, t', i'⟩) (fun y => ?_)
          rcases y with _ | s₁
          · exact hpure _
          · exact hebind _ _ _ _ (hmod _) (fun _ => hpure _)
        · exact hebind _ _ _ _ (hmod _) (fun _ => hpure _)
        · exact hpure _
  · change PrivL15.runEM _ (Engine.corrE _ _ P) s =
        PrivL15.runEM _ (Engine.corrE _ _ P) s
    dsimp only [Engine.corrE]
    refine hebind _ _ _ _ hget (fun es => ?_) s
    split_ifs
    · exact hpure _
    · exact hebind _ _ _ _ habort (fun _ => hpure _)
    · refine hebind _ _ _ _ (fun ⟨es', os'⟩ => hlift _ _ es' os' (by
        simp [hooksCKAUEager, PrivL15.runHM, simulateQ_realCKAKeyImpl_liftCKAComp (K := K)])) (fun x => ?_)
      rcases x with _ | st
      · exact hebind _ _ _ _ habort (fun _ => hpure _)
      · exact hebind _ _ _ _ (hmod _) (fun _ => hpure _)

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] in
private theorem evalEngU_realCKAKeyImpl_eq (mo : Mode) (t : ℕ) (π : Engine.Policy) (b : Bool)
    (oa : OracleComp (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) Bool) :
    ∀ s,
      evalEngU (realCKAKeyImpl cka Δcka 0) (hooksCKAUEager cka prng fs Δcka mo)
        (2 + Δcka) qep fs.maxSkip t π b oa s =
      evalEngU (CKA.oracleImpl cka Δcka 0) (hooksCKAU cka prng fs Δcka mo)
        (2 + Δcka) qep fs.maxSkip t π b oa s := by
  induction oa using OracleComp.inductionOn with
  | pure b' =>
    intro s
    simp [evalEngU_pure]
  | query_bind q k ih =>
    intro s
    rw [evalEngU_query_bind, evalEngU_query_bind, runEM_implE_hooksCKAUEager]
    exact bind_congr fun r => ih r.1 r.2

private def redCKAPrivUUniAllEager (t : ℕ)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    OracleComp (unifSpec + CKAKeySpec Γ CCoins T I K) Bool := do
  let b ← sampleT Bool
  match ← Engine.engRun (hooksCKAUEager cka prng fs Δcka ⟨false, none, t⟩) (2 + Δcka) qep fs.maxSkip
    (Config.priv t) (polUni12 Δcka t) (initCKAUEager cka prng fs lam ⟨false, none, t⟩) ({}, none) b A with
  | none => sampleT Bool
  | some (b', es) =>
    if privValidUni (2 + Δcka) t es then pure (b == b') else sampleT Bool

omit [DecidableEq M] in
private theorem simulateQ_privOutUni {ι : Type} {tspec : OracleSpec.{0, 0} ι} {OS VPt C HS : Type}
    (oimpl : QueryImpl tspec (StateT OS ProbComp)) (Δ t : ℕ) (b b' : Bool)
    (es : Engine.EState VPt M C HS) (os : OS) :
    Prod.fst <$> (simulateQ (PrivL15.outerFull oimpl)
        (if privValidUni Δ t es then pure (b == b') else sampleT Bool)).run os =
      privOutUni Δ t b b' es := by
  cases hv : privValidUni Δ t es <;>
    simp [privOutUni, hv, PrivL15.simulateQ_outerFull_sampleT]

omit [DecidableEq I] in
theorem evalDist_branch_redCKAPrivUUniAll_eq_eager (t : ℕ)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    𝒟[CKA.branch cka Δcka 0 false (redCKAPrivUUniAll cka prng fs lam Δcka qep t A)] =
    𝒟[do
      let b ← ($ᵗ Bool : ProbComp Bool)
      let k_fs ← ($ᵗ K : ProbComp K)
      let kc₀ ← ($ᵗ KC : ProbComp KC)
      let r ← PrivL15.runHM (eagerCKAKeyImpl cka Δcka 0)
        (initCKAUEager cka prng fs lam ⟨false, none, t⟩) ({}, none)
        (CKA.initState cka kc₀ false, .ready k_fs)
      evalAfterInitU (eagerCKAKeyImpl cka Δcka 0) (hooksCKAUEager cka prng fs Δcka ⟨false, none, t⟩)
        (2 + Δcka) qep fs.maxSkip t (polUni12 Δcka t) b A r] := by
  have h1 :
      CKA.branch cka Δcka 0 false (redCKAPrivUUniAll cka prng fs lam Δcka qep t A) =
      (($ᵗ KC : ProbComp KC) >>= fun kc₀ =>
        Prod.fst <$> (simulateQ (PrivL15.outerFull (realCKAKeyImpl cka Δcka 0))
          (redCKAPrivUUniAllEager cka prng fs lam Δcka qep t A)).run
          (CKA.initState cka kc₀ false)) := by
    refine bind_congr fun kc₀ => ?_
    change Prod.fst <$> (simulateQ (PrivL15.outerFull (CKA.oracleImpl cka Δcka 0))
        (redCKAPrivUUniAll cka prng fs lam Δcka qep t A)).run (CKA.initState cka kc₀ false) = _
    unfold redCKAPrivUUniAll runCKAUUni redCKAPrivUUniAllEager
    simp only [Engine.engRun, simulateQ_bind, StateT.run_bind, bind_assoc,
      PrivL15.simulateQ_outerFull_sampleT, bind_map_left, map_bind]
    refine bind_congr fun b => ?_
    have hinit :
        (simulateQ (PrivL15.outerFull (CKA.oracleImpl cka Δcka 0))
          ((initCKAU cka prng fs lam ⟨false, none, t⟩).run ({}, none))).run
          (CKA.initState cka kc₀ false) =
        (simulateQ (PrivL15.outerFull (realCKAKeyImpl cka Δcka 0))
          ((initCKAUEager cka prng fs lam ⟨false, none, t⟩).run ({}, none))).run
          (CKA.initState cka kc₀ false) := by
      simp only [initCKAUEager, StateT.run_mk, simulateQ_realCKAKeyImpl_liftCKAComp (K := K)]
    rw [hinit]
    refine bind_congr fun ⟨⟨vs, h⟩, os₁⟩ => ?_
    cases vs with
    | none => simp [PrivL15.simulateQ_outerFull_sampleT]
    | some vAvB =>
      rcases vAvB with ⟨vA, vB⟩
      have heng := evalEngU_realCKAKeyImpl_eq cka prng fs Δcka qep ⟨false, none, t⟩ t
        (polUni12 Δcka t) b A
        ({ g := { st := fun P => match P with | .A => vA | .B => vB, b }, h }, os₁)
      simp only [evalEngU, PrivL15.runEM, simulateQ_bind, StateT.run_bind, bind_assoc,
        simulateQ_pure, StateT.run_pure, pure_bind, bind_map_left,
        simulateQ_privOutUni] at heng ⊢
      exact heng.symm
  rw [h1]
  have h2 : ∀ kc₀ : KC,
      DEq (Prod.fst <$> (simulateQ (PrivL15.outerFull (realCKAKeyImpl cka Δcka 0))
            (redCKAPrivUUniAllEager cka prng fs lam Δcka qep t A)).run
            (CKA.initState cka kc₀ false))
          (($ᵗ K : ProbComp K) >>= fun k_fs =>
            Prod.fst <$> (simulateQ (PrivL15.outerFull (eagerCKAKeyImpl cka Δcka 0))
              (redCKAPrivUUniAllEager cka prng fs lam Δcka qep t A)).run
              (CKA.initState cka kc₀ false, .ready k_fs)) := by
    intro kc₀
    rw [← simulateQ_eagerCKAKeyImpl_nonReady cka Δcka 0 _
      (CKA.initState cka kc₀ false, .unknown) trivial]
    simp only [Functor.map_map]
    change DEq (Prod.fst <$> (simulateQ (PrivL15.outerFull (eagerCKAKeyImpl cka Δcka 0))
          (redCKAPrivUUniAllEager cka prng fs lam Δcka qep t A)).run
          (CKA.initState cka kc₀ false, .unknown)) _
    have hcomm := Comm.simulateQ fillKeyCKA_idem (comm_eagerCKAKeyImpl cka Δcka 0)
      (redCKAPrivUUniAllEager cka prng fs lam Δcka qep t A)
      (CKA.initState cka kc₀ false, .unknown)
    have hmap := DEq.map hcomm.symm Prod.fst
    have hdrop : ∀ m : ProbComp (Bool × CKAEagerState Γ T K),
        DEq (Prod.fst <$> (m >>= fillOut (fillKeyCKA (Γ := Γ) (T := T) (K := K))))
            (Prod.fst <$> m) := by
      intro m
      simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, fillOut, fillSt]
      refine DEq.bind_right m fun z => ?_
      simpa only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind] using
        DEq.bind_const (fillKeyCKA z.2.1 z.2.2) (pure z.1)
    refine (hdrop _).symm.trans (hmap.trans ?_)
    simp only [fillSt, fillKeyCKA, Functor.map_map, bind_map_left, bind_assoc, map_bind]
    exact DEq.bind_right ($ᵗ K) fun k_fs => by simpa only [map_bind] using hdrop _
  have h3 :
      DEq (($ᵗ KC : ProbComp KC) >>= fun kc₀ =>
            Prod.fst <$> (simulateQ (PrivL15.outerFull (realCKAKeyImpl cka Δcka 0))
              (redCKAPrivUUniAllEager cka prng fs lam Δcka qep t A)).run
              (CKA.initState cka kc₀ false))
          (do
            let b ← ($ᵗ Bool : ProbComp Bool)
            let k_fs ← ($ᵗ K : ProbComp K)
            let kc₀ ← ($ᵗ KC : ProbComp KC)
            let r ← PrivL15.runHM (eagerCKAKeyImpl cka Δcka 0)
              (initCKAUEager cka prng fs lam ⟨false, none, t⟩) ({}, none)
              (CKA.initState cka kc₀ false, .ready k_fs)
            evalAfterInitU (eagerCKAKeyImpl cka Δcka 0)
              (hooksCKAUEager cka prng fs Δcka ⟨false, none, t⟩)
              (2 + Δcka) qep fs.maxSkip t (polUni12 Δcka t) b A r) := by
    refine (DEq.bind_right ($ᵗ KC) h2).trans ?_
    refine (DEq.swap ($ᵗ KC) ($ᵗ K) _).trans ?_
    have hunf : ∀ k_fs kc₀,
        Prod.fst <$> (simulateQ (PrivL15.outerFull (eagerCKAKeyImpl cka Δcka 0))
          (redCKAPrivUUniAllEager cka prng fs lam Δcka qep t A)).run
          (CKA.initState cka kc₀ false, .ready k_fs) =
        (($ᵗ Bool : ProbComp Bool) >>= fun b =>
          PrivL15.runHM (eagerCKAKeyImpl cka Δcka 0)
            (initCKAUEager cka prng fs lam ⟨false, none, t⟩) ({}, none)
            (CKA.initState cka kc₀ false, .ready k_fs) >>= fun r =>
          evalAfterInitU (eagerCKAKeyImpl cka Δcka 0)
            (hooksCKAUEager cka prng fs Δcka ⟨false, none, t⟩)
            (2 + Δcka) qep fs.maxSkip t (polUni12 Δcka t) b A r) := by
      intro k_fs kc₀
      unfold redCKAPrivUUniAllEager
      simp only [Engine.engRun, simulateQ_bind, StateT.run_bind, bind_assoc,
        PrivL15.simulateQ_outerFull_sampleT, bind_map_left, map_bind, PrivL15.runHM]
      refine bind_congr fun b => bind_congr fun ⟨⟨vs, h⟩, os₁⟩ => ?_
      cases vs with
      | none => simp [evalAfterInitU, PrivL15.simulateQ_outerFull_sampleT]
      | some vAvB =>
        rcases vAvB with ⟨vA, vB⟩
        simp only [evalAfterInitU, evalEngU, PrivL15.runEM, simulateQ_bind, StateT.run_bind,
          bind_assoc, simulateQ_pure, StateT.run_pure, pure_bind, bind_map_left,
          simulateQ_privOutUni]
        rfl
    simp_rw [hunf]
    refine (DEq.bind_right ($ᵗ K) fun k_fs => DEq.swap ($ᵗ KC) ($ᵗ Bool) _).trans ?_
    exact DEq.swap ($ᵗ K) ($ᵗ Bool) _
  exact h3.evalDist_eq

end Stage2SwitchBack

end CryptoGames.SM.Construction
