/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.SessionAuthBridge -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.FSAEAD.Theorem5On
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.WireHop
import Computational.Proofs.GameHop.Advantage
import Computational.Proofs.GameHop.Rnd

/-!
# Zero-Query Session Vanishing for `fsAuthCompBoundWith` & `fsAeadAuthMixtureCompBound`

Proves that inactive session slots making `0` `FSAEAD` queries contribute `0` to
`fsAuthPrgMix`, `fsAuthSWMix`, `fsAuthCompBoundMix`, `fsAuthCompBoundWith`, and
`E2E.fsAeadAuthMixtureCompBound`.-/

namespace Computational.Proofs.SessionCostedFig8.BucketFSAuthZeroQueries

public section

set_option autoImplicit false

open scoped ENNReal
open OracleSpec OracleComp
open MeasureTheory (Measure)
open _root_.CryptoGames (Party MACScheme AEADScheme WireAEAD)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.FSAEAD (MakesAtMostQueries EncMsgsOk pubRed pubRedImpl
  RatchetSenderState RatchetReceiverState)
open _root_.CryptoGames.FSAEAD.Thm5 (hp isLookaheadHop slotCount slotToHybridHopIndex hInit DG
  implWith multiImplWith otOpsWith SpecialOps)
open _root_.CryptoGames.SM.Construction (Header)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart LibsignalCiphertextWithSalt32
  lPubOf lChainPRG lAeadR lIdeal lSaltPRF32 lSaltRed slotSaltRed lWire lWireRed slotWireRed)
open _root_.CryptoGames.LibsignalSM.Proofs.WireHop (lWireRed_eq wRedImpl)
open _root_.CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey SignalMessageProtoCodec
  maxForwardJumps)
open _root_.CryptoVerification.E2E.Signed (prgAvg prfAvg)
open _root_.CryptoVerification.E2E.Signed.FSMix (wireAvg)
open _root_.CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open _root_.CryptoVerification.LibsignalSession (FsAdv pubToAD fsCostedRedsInst fsAuthCompBound
  fsAuthCompBoundMix fsAuthPrgMix fsAuthSWMix fsAuthCompBoundWith fsAuthCompBoundWith_inst_eq
  fsAeadAuthMixtureCompBound_inst_eq)
open Computational.Proofs.GameHop.Rnd (evalDist_uniformBool_ite_true)
open Computational.Proofs.GameHop.Advantage (boolBias_eq_zero_of_apply_true_eq_half)
open Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out (advBit hRunOut multiRunOut
  cumulativeChainPrgReductionOut multiSlotOtccaReductionOut)
open Computational.Proofs.ReductionDsl.FsAtomicMacros (atomicShortB)

/-- Any `OracleComp (unifSpec + H) α` making `0` `.inr` queries produces the exact same `ProbComp α`
output distribution under any two stateful implementations that forward `unifSpec` coins cleanly. -/
private theorem fst_simulateQ_run_eq_of_no_inr {κ α σ₁ σ₂ : Type} {H : OracleSpec.{0, 0} κ}
    (impl₁ : QueryImpl (unifSpec + H) (StateT σ₁ ProbComp))
    (impl₂ : QueryImpl (unifSpec + H) (StateT σ₂ ProbComp))
    (h₁ : ∀ n (s : σ₁), (impl₁ (.inl n)).run s =
      (fun u => (u, s)) <$> query (spec := unifSpec) n)
    (h₂ : ∀ n (s : σ₂), (impl₂ (.inl n)).run s =
      (fun u => (u, s)) <$> query (spec := unifSpec) n)
    {c : OracleComp (unifSpec + H) α}
    (hc : c.IsQueryBoundP (fun q => q.isRight = true) 0) :
    ∀ (s₁ : σ₁) (s₂ : σ₂),
      Prod.fst <$> (simulateQ impl₁ c).run s₁ = Prod.fst <$> (simulateQ impl₂ c).run s₂ := by
  induction c using OracleComp.inductionOn with
  | pure a => intro s₁ s₂; simp
  | query_bind q k ih =>
    rw [isQueryBoundP_query_bind_iff] at hc; intro s₁ s₂
    cases q with
    | inr x => exact False.elim (hc.1.elim (fun h => h rfl) (Nat.not_lt_zero 0))
    | inl n =>
      have hk : ∀ u, (k u).IsQueryBoundP (fun q => q.isRight = true) 0 :=
        fun u => by simpa using hc.2 u
      rw [OracleComp.run_simulateQ_query_bind, OracleComp.run_simulateQ_query_bind,
        h₁ n s₁, h₂ n s₂, bind_map_left, bind_map_left, map_bind, map_bind]
      exact bind_congr fun u => ih u (hk u) s₁ s₂

/-- Any stateful coin-forwarding simulation of a `0`-`.inr`-query computation preserves `0` `.inr`
queries in the target `unifSpec + H₂` monad. -/
private theorem isQueryBoundP_no_inr_simulateQ_run {κ₁ κ₂ α σ : Type}
    {H₁ : OracleSpec.{0, 0} κ₁} {H₂ : OracleSpec.{0, 0} κ₂}
    (impl : QueryImpl (unifSpec + H₁) (StateT σ (OracleComp (unifSpec + H₂))))
    (hcoin : ∀ n (s : σ), (impl (.inl n)).run s =
      (fun u => (u, s)) <$> query (spec := unifSpec + H₂) (.inl n))
    {c : OracleComp (unifSpec + H₁) α}
    (hc : c.IsQueryBoundP (fun q => q.isRight = true) 0) :
    ∀ (s : σ), ((simulateQ impl c).run s).IsQueryBoundP (fun q => q.isRight = true) 0 := by
  induction c using OracleComp.inductionOn with
  | pure a => intro s; simp [simulateQ_pure, StateT.run_pure]
  | query_bind q k ih =>
    rw [isQueryBoundP_query_bind_iff] at hc; intro s
    cases q with
    | inr x => exact False.elim (hc.1.elim (fun h => h rfl) (Nat.not_lt_zero 0))
    | inl n =>
      have hk : ∀ u, (k u).IsQueryBoundP (fun q => q.isRight = true) 0 :=
        fun u => by simpa using hc.2 u
      rw [OracleComp.run_simulateQ_query_bind, hcoin n s, bind_map_left]
      change (liftM (OracleSpec.query (spec := unifSpec + H₂) (.inl n)) >>= fun u =>
          (simulateQ impl (k u)).run s).IsQueryBoundP _ 0
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (by simp), fun u => by simpa using ih u (hk u) s⟩

private theorem isQueryBoundP_no_inr_map {κ α β : Type} {H : OracleSpec.{0, 0} κ}
    (f : α → β) {c : OracleComp (unifSpec + H) α}
    (hc : c.IsQueryBoundP (fun q => q.isRight = true) 0) :
    (f <$> c).IsQueryBoundP (fun q => q.isRight = true) 0 := by
  induction c using OracleComp.inductionOn with
  | pure a => simp
  | query_bind q k ih =>
    rw [isQueryBoundP_query_bind_iff] at hc
    cases q with
    | inr x => exact False.elim (hc.1.elim (fun h => h rfl) (Nat.not_lt_zero 0))
    | inl n =>
      change (liftM (OracleSpec.query (spec := unifSpec + H) (.inl n)) >>= fun u =>
          f <$> k u).IsQueryBoundP _ 0
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (by simp), fun u => by simpa using ih u (by simpa using hc.2 u)⟩

private theorem isQueryBoundP_no_inr_liftM {κ α : Type} {H : OracleSpec.{0, 0} κ}
    (p : ProbComp α) :
    (liftM p : OracleComp (unifSpec + H) α).IsQueryBoundP (fun q => q.isRight = true) 0 := by
  induction p using OracleComp.inductionOn with
  | pure a => simp
  | query_bind n k ih =>
    change (liftM (OracleSpec.query (spec := unifSpec + H) (.inl n)) >>= fun u =>
        (liftM (k u) : OracleComp (unifSpec + H) α)).IsQueryBoundP _ 0
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp), fun u => by simpa using ih u⟩

private theorem isQueryBoundP_no_inr_bind {κ α β : Type} {H : OracleSpec.{0, 0} κ}
    {c : OracleComp (unifSpec + H) α} {k : α → OracleComp (unifSpec + H) β}
    (hc : c.IsQueryBoundP (fun q => q.isRight = true) 0)
    (hk : ∀ a, (k a).IsQueryBoundP (fun q => q.isRight = true) 0) :
    (c >>= k).IsQueryBoundP (fun q => q.isRight = true) 0 := by
  induction c using OracleComp.inductionOn with
  | pure a => simpa using hk a
  | query_bind q k₀ ih =>
    rw [isQueryBoundP_query_bind_iff] at hc
    cases q with
    | inr x => exact False.elim (hc.1.elim (fun h => h rfl) (Nat.not_lt_zero 0))
    | inl n =>
      change (liftM (OracleSpec.query (spec := unifSpec + H) (.inl n)) >>= fun u =>
          k₀ u >>= k).IsQueryBoundP _ 0
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (by simp), fun u => by simpa using ih u (by simpa using hc.2 u)⟩

theorem evalDist_bind_const_probComp {α β : Type} [MeasurableSpace β]
    (p : ProbComp α) (q : ProbComp β) :
    𝒟[p >>= fun _ => q] = 𝒟[q] := by
  induction p using OracleComp.inductionOn with
  | pure a =>
    simp
  | query_bind n k ih =>
    change 𝒟[query (spec := unifSpec) n >>= fun u => (k u >>= fun _ => q)] = 𝒟[q]
    rw [evalDist_bind_congr (query (spec := unifSpec) n)
      (fun u => k u >>= fun _ => q) (fun _ => q) (fun u => ih u)]
    rw [evalDist_bind_of_discrete]
    ext s hs
    rw [Measure.bind_apply hs Measurable.of_discrete.aemeasurable]
    simp

private theorem boolBias_uniformBool_key_beq {K : Type} [SampleableType K] (c₀ : ProbComp Bool) :
    𝒟[do
      let b ← ($ᵗ Bool : ProbComp Bool)
      let _ ← ($ᵗ K : ProbComp K)
      let out ← c₀
      pure (b == out)].boolBias = 0 := by
  apply boolBias_eq_zero_of_apply_true_eq_half
  have hdrop :
      𝒟[do
        let b ← ($ᵗ Bool : ProbComp Bool)
        let _ ← ($ᵗ K : ProbComp K)
        let out ← c₀
        pure (b == out)] =
      𝒟[do
        let b ← ($ᵗ Bool : ProbComp Bool)
        if b then (c₀ >>= fun out => pure (true == out))
        else (c₀ >>= fun out => pure (false == out))] := by
    refine evalDist_bind_congr ($ᵗ Bool : ProbComp Bool) _ _ fun b => ?_
    rw [evalDist_bind_const_probComp ($ᵗ K : ProbComp K)]
    cases b <;> rfl
  rw [hdrop, evalDist_uniformBool_ite_true]
  have hT : (c₀ >>= fun out => pure (true == out)) = c₀ := by
    simp
  have hF : 𝒟[c₀ >>= fun out => pure (false == out)] {true} = 𝒟[c₀] {false} := by
    rw [evalDist_bind_of_discrete,
      Measure.bind_apply (measurableSet_singleton true) Measurable.of_discrete.aemeasurable,
      MeasureTheory.lintegral_fintype, Fintype.sum_bool]
    simp
  rw [hT, hF]
  have huniv : 𝒟[c₀] {true} + 𝒟[c₀] {false} = 1 := by
    have h1 : (1 : ℝ≥0∞) = 𝒟[c₀] Set.univ := (MeasureTheory.measure_univ (μ := 𝒟[c₀])).symm
    rw [h1]
    have hset : (Set.univ : Set Bool) = {true} ∪ {false} := by
      ext x; cases x <;> simp
    rw [hset, MeasureTheory.measure_union (by simp) (measurableSet_singleton false)]
  rw [huniv, one_div]

/-- A constant `PRGAdversary` (`∀ x y, adv x = adv y`) has `prgAdvantage = 0`. -/
private theorem prgAdvantage_const_eq_zero {Seed R : Type}
    [SampleableType Seed] [SampleableType R]
    (prg : PRGScheme Seed R) (adv : PRGScheme.PRGAdversary R)
    (hconst : ∀ r₁ r₂, adv r₁ = adv r₂) :
    prg.prgAdvantage adv = 0 := by
  have h0 : Nonempty Seed := SampleableType.nonempty Seed
  obtain ⟨s₀⟩ := h0
  let c₀ : ProbComp Bool := adv (prg.gen s₀)
  have hEq : ∀ r, adv r = c₀ := fun r => hconst r (prg.gen s₀)
  unfold PRGScheme.prgAdvantage PRGScheme.prgRealExperiment PRGScheme.prgIdealExperiment
  simp only [hEq, evalDist_bind_const_probComp]
  rw [Measure.boolDist, ENNReal.absDiff_self]

/-- Any `PRFAdversary` making `0` `.inr` queries has `prfAdvantage = 0`. -/
private theorem prfAdvantage_no_inr_eq_zero {Key Input Tag : Type} [DecidableEq Input]
    [SampleableType Key] [SampleableType Tag]
    (mac : MACScheme Key Input Tag) (adv : MACScheme.PRFAdversary Input Tag)
    (h0 : adv.IsQueryBoundP (fun q => q.isRight = true) 0) :
    mac.prfAdvantage adv = 0 := by
  obtain ⟨k₀⟩ : Nonempty Key := SampleableType.nonempty Key
  let st₀ : MACScheme.PRFState Key Input Tag := { key := k₀, b := false }
  let impl : QueryImpl (unifSpec + MACScheme.prfSpec Input Tag)
      (StateT (MACScheme.PRFState Key Input Tag) ProbComp) :=
    (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (MACScheme.PRFState Key Input Tag) ProbComp) + MACScheme.prfEval mac
  have hcoin : ∀ n (s : MACScheme.PRFState Key Input Tag),
      (impl (.inl n)).run s = (fun u => (u, s)) <$> query (spec := unifSpec) n := by
    intro n s; simp [impl, QueryImpl.liftTarget, map_eq_bind_pure_comp]
  let c₀ : ProbComp Bool := Prod.fst <$> (simulateQ impl adv).run st₀
  have hrun : ∀ (s : MACScheme.PRFState Key Input Tag),
      (simulateQ impl adv).run' s = c₀ := fun s => by
    rw [StateT.run'_eq]; exact fst_simulateQ_run_eq_of_no_inr impl impl hcoin hcoin h0 s st₀
  unfold MACScheme.prfAdvantage MACScheme.prfGame
  have hgame :
      (do let b ← $ᵗ Bool; let key ← $ᵗ Key; let b' ← (simulateQ impl adv).run' { key, b };
          pure (b == b')) =
      (do let b ← $ᵗ Bool; let _ ← $ᵗ Key; let b' ← c₀; pure (b == b')) :=
    bind_congr fun b => bind_congr fun key =>
      congrArg (· >>= fun b' => pure (b == b')) (hrun { key, b })
  rw [hgame]; exact boolBias_uniformBool_key_beq c₀

/-- Any `WireAdversary` making `0` `.inr` queries has `wireOtccaAdvantage = 0`. -/
private theorem wireOtccaAdvantage_no_inr_eq_zero {K AD H M M' C T : Type}
    [SampleableType K] [SampleableType C] [SampleableType T] [DecidableEq AD] [DecidableEq T]
    (ae : WireAEAD K AD H M M' C T) (adv : WireAEAD.WireAdversary AD H M M' T)
    (h0 : adv.IsQueryBoundP (fun q => q.isRight = true) 0) :
    ae.wireOtccaAdvantage adv = 0 := by
  obtain ⟨k₀⟩ : Nonempty K := SampleableType.nonempty K
  let st₀ : WireAEAD.WireState K AD T := { key := k₀, b := false }
  let wOracles : QueryImpl (WireAEAD.wireSpec AD H M M' T)
      (StateT (WireAEAD.WireState K AD T) ProbComp) := ae.wireEncrypt + ae.wireDecrypt
  let impl : QueryImpl (unifSpec + WireAEAD.wireSpec AD H M M' T)
      (StateT (WireAEAD.WireState K AD T) ProbComp) :=
    (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (WireAEAD.WireState K AD T) ProbComp) + wOracles
  have hcoin : ∀ n (s : WireAEAD.WireState K AD T),
      (impl (.inl n)).run s = (fun u => (u, s)) <$> query (spec := unifSpec) n := by
    intro n s; simp [impl, QueryImpl.liftTarget, map_eq_bind_pure_comp]
  let c₀ : ProbComp Bool := Prod.fst <$> (simulateQ impl adv).run st₀
  have hrun : ∀ (s : WireAEAD.WireState K AD T),
      (simulateQ impl adv).run' s = c₀ := fun s => by
    rw [StateT.run'_eq]
    exact fst_simulateQ_run_eq_of_no_inr (H := WireAEAD.wireSpec AD H M M' T)
      impl impl hcoin hcoin h0 s st₀
  unfold WireAEAD.wireOtccaAdvantage WireAEAD.wireOtccaGame
  have hgame :
      (do let b ← $ᵗ Bool; let key ← $ᵗ K; let b' ← (simulateQ impl adv).run' { key, b };
          pure (b == b')) =
      (do let b ← $ᵗ Bool; let _ ← $ᵗ K; let b' ← c₀; pure (b == b')) :=
    bind_congr fun b => bind_congr fun key =>
      congrArg (· >>= fun b' => pure (b == b')) (hrun { key, b })
  rw [hgame]; exact boolBias_uniformBool_key_beq c₀

private theorem pubToAD_no_inr_of_makesAtMostQueries_zero {Pt : Type} {ℓ : ℕ}
    (codec : SignalMessageProtoCodec) (A : FsAdv Pt ℓ) (h0 : MakesAtMostQueries A 0) :
    (pubToAD codec A).IsQueryBoundP (fun q => q.isRight = true) 0 := by
  have hA : A.IsQueryBoundP (fun q => q.isRight = true) 0 :=
    h0.of_imp fun x hx => by cases x <;> simp at hx ⊢
  let impl := pubRedImpl
    (SS := RatchetSenderState (BitVec 256))
    (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
    (AD := Header Pt) (M := Plain ℓ)
    (fun c : ℕ × LibsignalCiphertextWithSalt32 => lPubOf codec c.2)
  unfold pubToAD pubRed; rw [StateT.run'_eq]
  refine isQueryBoundP_no_inr_map Prod.fst (isQueryBoundP_no_inr_simulateQ_run impl ?_ hA false)
  intro n s; simp [impl, pubRedImpl, StateT.run_lift, map_eq_bind_pure_comp]

private theorem multiSlotOtccaReductionOut_no_inr_of_zero {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (maxSkip N : ℕ) (la : Bool) (A : FsAdv Pt ℓ) (h0 : MakesAtMostQueries A 0) :
    (multiSlotOtccaReductionOut (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf)
      (lChainPRG C.F) maxSkip N la advBit (pubToAD codec A)).IsQueryBoundP
      (fun q => q.isRight = true) 0 := by
  have hB := pubToAD_no_inr_of_makesAtMostQueries_zero codec A h0
  let impl := multiImplWith (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf)
    (lChainPRG C.F) maxSkip (hp N 0 la) N (DG (lChainPRG C.F))
    (some (otOpsWith (lIdeal C codec ℓ encT)))
  unfold multiSlotOtccaReductionOut multiRunOut
  refine isQueryBoundP_no_inr_bind
    (H := AEADScheme.otccaSpec (ℕ × (Header Pt × LibsignalMsgPublicPart))
      (Plain ℓ) LibsignalCiphertextWithSalt32)
    (isQueryBoundP_no_inr_liftM ($ᵗ Bool)) fun b => ?_
  refine isQueryBoundP_no_inr_bind
    (isQueryBoundP_no_inr_simulateQ_run impl ?_ hB (hInit b .unknown)) fun _ => by simp
  intro n s; simp [impl, multiImplWith, QueryImpl.liftTarget, map_eq_bind_pure_comp]; rfl

/-- `fsAuthPrgMix` vanishes whenever `A o` makes `0` `FSAEAD` queries for every `o`. -/
theorem fsAuthPrgMix_eq_zero_of_zero_queries {Pt : Type} [DecidableEq Pt] {α : Type}
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (oa : ProbComp α) (idOf : α → Party → IdentityKey) (maxSkip m : ℕ)
    (A : α → FsAdv Pt ℓ) (h0 : ∀ o, MakesAtMostQueries (A o) 0) :
    fsAuthPrgMix C codec ℓ encT oa idOf maxSkip A m = 0 := by
  unfold fsAuthPrgMix; apply prgAdvantage_const_eq_zero; intro mt₁ mt₂; unfold prgAvg
  refine congrArg (oa >>= ·) (funext fun o => ?_); dsimp only
  have hB := pubToAD_no_inr_of_makesAtMostQueries_zero codec (A o) (h0 o)
  let impl := implWith (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT (idOf o))
    (lChainPRG C.F) maxSkip (hp (m / 2) 0 (isLookaheadHop m)) (DG (lChainPRG C.F))
    (none : Option (SpecialOps (Header Pt × LibsignalMsgPublicPart) (Plain ℓ)
      LibsignalCiphertextWithSalt32 ProbComp))
  have hcoin : ∀ n s,
      (impl (.inl n)).run s = (fun u => (u, s)) <$> query (spec := unifSpec) n := fun n s => by
    simp [impl, implWith, QueryImpl.liftTarget, map_eq_bind_pure_comp]
  unfold cumulativeChainPrgReductionOut hRunOut
  refine congrArg ((liftM ($ᵗ Bool : ProbComp Bool) : ProbComp Bool) >>= ·) (funext fun b => ?_)
  have hfst := fst_simulateQ_run_eq_of_no_inr
    (H := CryptoGames.FSAEAD.spec _ _ _ _ _) impl impl hcoin hcoin hB
    (hInit b (.mat (m / 2) mt₁)) (hInit b (.mat (m / 2) mt₂))
  simpa only [advBit, map_eq_bind_pure_comp, Function.comp_def] using hfst

/-- `fsAuthSWMix` vanishes whenever `Afalse o` and `Atrue o` make `0` `FSAEAD` queries. -/
theorem fsAuthSWMix_eq_zero_of_zero_queries {Pt : Type} [DecidableEq Pt] {α : Type}
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (oa : ProbComp α) (idOf : α → Party → IdentityKey) (maxSkip q m : ℕ)
    (Afalse Atrue : α → FsAdv Pt ℓ)
    (h0F : ∀ o, MakesAtMostQueries (Afalse o) 0)
    (h0T : ∀ o, MakesAtMostQueries (Atrue o) 0) :
    fsAuthSWMix C codec ℓ encT oa idOf maxSkip q Afalse Atrue m = 0 := by
  unfold fsAuthSWMix; dsimp only
  let la := isLookaheadHop m; let N := if la then q + (maxSkip + 1) else q
  have hSalt : (lSaltPRF32 C.F).prfAdvantage
      (prfAvg oa fun o => lSaltRed C codec ℓ encT (idOf o)
        (slotSaltRed C codec ℓ encT (idOf o) N (m / 2)
          (multiSlotOtccaReductionOut (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT (idOf o))
            (lChainPRG C.F) maxSkip N la advBit (pubToAD codec (Afalse o))))) = 0 := by
    refine prfAdvantage_no_inr_eq_zero _ _ (isQueryBoundP_no_inr_bind (isQueryBoundP_no_inr_liftM oa)
      fun o => ?_)
    have h0o := multiSlotOtccaReductionOut_no_inr_of_zero C codec ℓ encT (idOf o) maxSkip N la
      (Afalse o) (h0F o)
    have hSlot : (slotSaltRed C codec ℓ encT (idOf o) N (m / 2)
        (multiSlotOtccaReductionOut (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT (idOf o))
          (lChainPRG C.F) maxSkip N la advBit (pubToAD codec (Afalse o)))).IsQueryBoundP
        (fun q => q.isRight = true) 0 := by
      unfold slotSaltRed
      refine isQueryBoundP_no_inr_bind (isQueryBoundP_no_inr_liftM _) fun _ =>
        isQueryBoundP_no_inr_bind (isQueryBoundP_no_inr_liftM _) fun _ =>
          isQueryBoundP_no_inr_map _ (isQueryBoundP_no_inr_simulateQ_run _ ?_ h0o _)
      intro n s
      simp [CryptoGames.FSAEAD.Thm5.slotRedImpl, StateT.run_lift, map_eq_bind_pure_comp]
    unfold lSaltRed; dsimp only
    refine isQueryBoundP_no_inr_bind (isQueryBoundP_no_inr_liftM _) fun _ => ?_
    rw [StateT.run'_eq]
    refine isQueryBoundP_no_inr_bind
        (isQueryBoundP_no_inr_map _ (isQueryBoundP_no_inr_simulateQ_run _ ?_ hSlot _))
        fun _ => by simp
    intro n s; simp [StateT.run_lift, map_eq_bind_pure_comp]
  have hWire : (lWire C codec ℓ).wireOtccaAdvantage
      (wireAvg oa fun o => lWireRed C codec ℓ encT (idOf o) 0
        (slotWireRed C codec ℓ encT (idOf o) (m / 2)
          (multiSlotOtccaReductionOut (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT (idOf o))
            (lChainPRG C.F) maxSkip N la advBit (pubToAD codec (Atrue o))))) = 0 := by
    refine wireOtccaAdvantage_no_inr_eq_zero _ _
      (isQueryBoundP_no_inr_bind (isQueryBoundP_no_inr_liftM oa) fun o => ?_)
    have h0o := multiSlotOtccaReductionOut_no_inr_of_zero C codec ℓ encT (idOf o) maxSkip N la
      (Atrue o) (h0T o)
    have hSlot : (slotWireRed C codec ℓ encT (idOf o) (m / 2)
        (multiSlotOtccaReductionOut (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT (idOf o))
          (lChainPRG C.F) maxSkip N la advBit (pubToAD codec (Atrue o)))).IsQueryBoundP
        (fun q => q.isRight = true) 0 := by
      unfold slotWireRed
      refine isQueryBoundP_no_inr_map _ (isQueryBoundP_no_inr_simulateQ_run _ ?_ h0o _)
      intro n s
      simp [CryptoGames.FSAEAD.Thm5.slotRedImpl, StateT.run_lift, map_eq_bind_pure_comp]
    rw [lWireRed_eq]
    refine isQueryBoundP_no_inr_bind (isQueryBoundP_no_inr_simulateQ_run _ ?_ hSlot _)
      fun ⟨b', st⟩ => ?_
    · intro n s; simp [wRedImpl, StateT.run_lift, map_eq_bind_pure_comp]
    · by_cases hcond : st.2.2.1 = true
      · simpa [hcond] using isQueryBoundP_no_inr_liftM
          (H := WireAEAD.wireSpec _ _ _ _ _) ($ᵗ Bool)
      · simp [hcond]
  rw [hSalt, hWire]; simp

/-- `fsAuthCompBoundMix` vanishes whenever `A stage la o` makes `0` `FSAEAD` queries. -/
theorem fsAuthCompBoundMix_eq_zero_of_zero_queries {Pt : Type} [DecidableEq Pt] {α : Type}
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (oa : ProbComp α) (idOf : α → Party → IdentityKey) (maxSkip qR : ℕ)
    (A : Bool → Bool → α → FsAdv Pt ℓ)
    (h0 : ∀ stage la o, MakesAtMostQueries (A stage la o) 0) :
    fsAuthCompBoundMix C codec ℓ encT oa idOf maxSkip qR A = 0 := by
  unfold fsAuthCompBoundMix
  have hsum : ∀ j ∈ Finset.range (slotCount maxSkip qR),
      (let m := slotToHybridHopIndex qR j
       let la := isLookaheadHop m
       fsAuthPrgMix C codec ℓ encT oa idOf maxSkip (A false la) m +
         fsAuthSWMix C codec ℓ encT oa idOf maxSkip qR (A false la) (A true la) m) = 0 := by
    intro j _
    dsimp only
    rw [fsAuthPrgMix_eq_zero_of_zero_queries C codec ℓ encT oa idOf maxSkip _ _ (h0 false _),
      fsAuthSWMix_eq_zero_of_zero_queries C codec ℓ encT oa idOf maxSkip qR _ _ _
        (h0 false _) (h0 true _), add_zero]
  rw [Finset.sum_eq_zero hsum, mul_zero]

/-- `fsAuthCompBoundWith` on `fsCostedRedsInst` vanishes whenever `A stage la` makes `0` queries. -/
theorem fsAuthCompBoundWith_inst_eq_zero_of_zero_queries
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (qR : ℕ)
    (hℓ : ℓ < 10 ^ 6) (hinj : Function.Injective encT)
    (A : Bool → Bool → FsAdv Pt ℓ)
    (h0 : ∀ stage la, MakesAtMostQueries (A stage la) 0) :
    fsAuthCompBoundWith C protoSignalCodec ℓ qR
      (fsCostedRedsInst C protoSignalCodec ℓ encT idOf qR) A = 0 := by
  have hAqR : ∀ stage la, MakesAtMostQueries (A stage la) qR :=
    fun stage la => (h0 stage la).mono (Nat.zero_le qR)
  have hshort : ∀ stage la,
      EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) (A stage la) := by
    intro stage la
    unfold EncMsgsOk
    refine (h0 stage la).of_imp fun t ht => ?_
    cases t with
    | inl _ => simp [CryptoGames.FSAEAD.encBadMsg] at ht
    | inr _ => rfl
  rw [fsAuthCompBoundWith_inst_eq C ℓ encT idOf qR 0 hℓ hinj A hAqR hshort]
  have hpure : fsAuthCompBound C protoSignalCodec ℓ encT idOf qR 0 A =
      fsAuthCompBoundMix C protoSignalCodec ℓ encT (pure ()) (fun _ => idOf) maxForwardJumps qR
        (fun stage la _ => A stage la) := by
    unfold fsAuthCompBoundMix fsAuthCompBound
    have hslot : slotCount maxForwardJumps qR =
        CryptoVerification.LibsignalSession.fsSlotCount qR := rfl
    rw [hslot]
    refine congrArg (2 * ·) (Finset.sum_congr rfl fun k _ => ?_)
    dsimp only
    unfold fsAuthPrgMix CryptoVerification.LibsignalSession.chainPRGTermAuth
      fsAuthSWMix CryptoVerification.LibsignalSession.saltPRFTermAuth
      CryptoVerification.LibsignalSession.wireOtccaTermAuth
    have hprg : prgAvg (pure ()) (fun (_ : Unit) =>
        cumulativeChainPrgReductionOut (lIdeal C protoSignalCodec ℓ encT)
          (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
          (slotToHybridHopIndex qR k) advBit
          (pubToAD protoSignalCodec (A false (isLookaheadHop (slotToHybridHopIndex qR k))))) =
        cumulativeChainPrgReductionOut (lIdeal C protoSignalCodec ℓ encT)
          (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
          (slotToHybridHopIndex qR k) advBit
          (pubToAD protoSignalCodec (A false (isLookaheadHop (slotToHybridHopIndex qR k)))) := by
      funext mt
      exact pure_bind () _
    rw [hprg]
    dsimp only [prfAvg, wireAvg, Computational.Proofs.ReductionDsl.FsAtomicSoundness.multiSlotAdvAuth]
    simp only [liftM_pure, pure_bind]
  rw [hpure]
  exact fsAuthCompBoundMix_eq_zero_of_zero_queries C protoSignalCodec ℓ encT (pure ())
    (fun _ => idOf) maxForwardJumps qR (fun stage la _ => A stage la)
    (fun stage la _ => h0 stage la)

/-- `E2E.fsAeadAuthMixtureCompBound` on `fsCostedRedsInst` vanishes whenever `A stage la o` makes
`0` `FSAEAD` queries. -/
theorem fsAeadAuthMixtureCompBound_inst_eq_zero_of_zero_queries
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {α : Type}
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (oa : ProbComp α)
    (idOf : α → Party → IdentityKey) (qR : ℕ)
    (hℓ : ℓ < 10 ^ 6) (hinj : Function.Injective encT)
    (A : Bool → Bool → α → FsAdv Pt ℓ)
    (h0 : ∀ stage la o, MakesAtMostQueries (A stage la o) 0) :
    CryptoVerification.E2E.fsAeadAuthMixtureCompBound C protoSignalCodec ℓ oa qR
      (fun o => fsCostedRedsInst C protoSignalCodec ℓ encT (idOf o) qR) A = 0 := by
  have hAqR : ∀ stage la o, MakesAtMostQueries (A stage la o) qR :=
    fun stage la o => (h0 stage la o).mono (Nat.zero_le qR)
  have hshort : ∀ stage la o,
      EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1)
        (A stage la o) := by
    intro stage la o
    unfold EncMsgsOk
    refine (h0 stage la o).of_imp fun t ht => ?_
    cases t with
    | inl _ => simp [CryptoGames.FSAEAD.encBadMsg] at ht
    | inr _ => rfl
  rw [fsAeadAuthMixtureCompBound_inst_eq C ℓ encT oa idOf qR hℓ hinj A hAqR hshort]
  exact fsAuthCompBoundMix_eq_zero_of_zero_queries C protoSignalCodec ℓ encT oa idOf 25000 qR A h0

end

end Computational.Proofs.SessionCostedFig8.BucketFSAuthZeroQueries
