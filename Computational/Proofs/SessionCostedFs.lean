/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import Computational.Proofs.SessionCostedBase
import Computational.Proofs.ReductionDsl.FSAEAD.HybridCosted
import Computational.Proofs.ReductionDsl.FSAEAD.PubCosted
import Computational.Proofs.ReductionDsl.FSAEAD.SaltWireCosted
public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalBound -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.FsAtomicOps -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.FsAtomicMacros
public import Computational.Proofs.ReductionDsl.FsAtomicBundles -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.FsAtomicSoundness -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.FsAtomicBounds
public import Computational.Specifications.Session.StatementComposed
public import Computational.Proofs.E2E.SignedFSBound -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.HiddenSaltBound -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.AtomicTablesHonest
public import Computational.Proofs.ReductionDsl.Soundness -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.FSAEAD.HybridRed
import Computational.Proofs.GameHop.StateSim
import Computational.Proofs.CryptoGames.FSAEAD.Theorem5On
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.FSAEADBound
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.PubToAD
public import Computational.Proofs.CryptoGames.FSAEAD.HybridWithProofDefs
import Computational.Proofs.ReductionDsl.FSAEAD.HybridRedBase
import Computational.Proofs.ReductionDsl.FsAtomicBoundsSaltWire
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Finset.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Order.Disjoint
import Mathlib.Order.SetNotation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import PolyFun.Control.Monad.Support
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import ToMathlib.Control.StateT
import VCVio.CryptoFoundations.SecExp
import VCVio.EvalDist.Defs.Measure.Core
import VCVio.EvalDist.MeasureTVDist.Event
import VCVio.EvalDist.Monad.Basic
import VCVio.EvalDist.Monad.Bool
import VCVio.EvalDist.ProbabilityNotation
import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.OracleComp.EvalDist.Measure
import VCVio.OracleComp.OracleSpec
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.QueryTracking.SubSpec
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.SimSemantics.StateT.Basic
import VCVio.Prelude.Core
import VCVio.ProgramLogic.Unary.HoareTriple

/-!
# Costed FS-AEAD Reduction Bundle and Advantage Bridges

Instantiates the compiled atomic `FsCostedReds` bundle `fsCostedRedsInst` with `fsCostedBounds`
and proves its single-adversary, slot-sum, `DeliverForge`, and mixture advantage equalities at
`protoSignalCodec` under `EncMsgsOk atomicShortB`.-/

public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalSession

open OracleComp OracleSpec ENNReal
open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst
  LibsignalSession HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme MACScheme
  WireAEAD FSAEAD
open CryptoVerification.LibsignalProtoCodec
open ReductionDsl
open Computational.Proofs.ReductionDsl.FsAtomicOps
open Computational.Proofs.ReductionDsl.FsAtomicMacros
open Computational.Proofs.GameHop.StateSim (isQueryBoundP_congr_pred)

/-! ## Parameterized composition bridges -/

section FsCosted

variable {Pt : Type} [DecidableEq Pt]

lemma fsMakesAtMost_iff_isGameQuery {SS RS AD M Ciphertext : Type}
    (A : FSAEAD.Adversary SS RS AD M Ciphertext) (qR : ℕ) :
    FSAEAD.MakesAtMostQueries A qR ↔
      A.IsQueryBoundP (ReductionDsl.isGameQuery (G := FSAEAD.spec SS RS AD M Ciphertext)) qR :=
  ⟨isQueryBoundP_congr_pred (fun x => by cases x <;> simp [ReductionDsl.isGameQuery]),
   isQueryBoundP_congr_pred (fun x => by cases x <;> simp [ReductionDsl.isGameQuery])⟩

lemma hopIdx_le (qR j : ℕ) (hj : j < fsSlotCount qR) :
    FSAEAD.Thm5.slotToHybridHopIndex qR j ≤ 2 * (qR + maxForwardJumps + 1) := by
  unfold FSAEAD.Thm5.slotToHybridHopIndex fsSlotCount at *
  split_ifs <;> omega

omit [DecidableEq Pt] in
def fsCostedRedsBoundedWitness (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) :
    FsCostedReds C codec ℓ encT idOf :=
  Computational.Proofs.ReductionDsl.FsAtomicBundles.fsCostedRedsBoundedWitness C codec ℓ encT idOf

omit [DecidableEq Pt] in
theorem fsCostedRedsBoundedWitness_bounds (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (qR qep : ℕ) :
    fsCostedBounds qR qep (fsCostedRedsBoundedWitness C codec ℓ encT idOf) :=
  Computational.Proofs.ReductionDsl.FsAtomicBounds.fsCostedRedsBoundedWitness_bounds
    C codec ℓ encT idOf qR qep

/-! ## Atomic instance and clamped-codec bridges -/

/-- Compiled atomic `FsCostedReds` bundle over `ReductionDsl.atomicFsOps`. -/
abbrev fsCostedRedsInst (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (qR : ℕ) :
    FsCostedReds C codec ℓ encT idOf :=
  Computational.Proofs.ReductionDsl.FsAtomicBundles.fsCostedRedsInst C codec ℓ encT idOf qR

theorem fsCostedRedsInst_bounds (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (qR qep : ℕ) :
    fsCostedBounds qR qep (fsCostedRedsInst C codec ℓ encT idOf qR) :=
  Computational.Proofs.ReductionDsl.FsAtomicBounds.fsCostedRedsInst_bounds C codec ℓ encT idOf qR qep

theorem pubToADCosted_inst_queries (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (qR : ℕ)
    (A : FsAdv Pt ℓ) (hA : FSAEAD.MakesAtMostQueries A qR) :
    (pubToADCosted (fsCostedRedsInst C codec ℓ encT idOf qR) A).IsQueryBoundP
      (isGameQuery (G := FSAEAD.spec (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256))
        (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) (ℕ × LCt))) qR := by
  have hb := fsCostedRedsInst_bounds C codec ℓ encT idOf qR 0
  unfold fsCostedBounds at hb
  obtain ⟨⟨-, -, hq, -⟩, -⟩ := hb
  exact (CostedReduction.queryBound_eval (fsCostedRedsInst C codec ℓ encT idOf qR).pubRed _
    (fun _ => 1) (fun _ => 0) (fun _ _ _ => le_rfl) (fun _ => by simp [isGameQuery])
    (fun _ => A) qR (fun _ => (fsMakesAtMost_iff_isGameQuery A qR).mp hA) ()).mono hq

alias pubToADWith_inst_queries := pubToADCosted_inst_queries

theorem multiSlotAdvCosted_inst_queries (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (qR : ℕ) (la : Bool)
    (A : FsAdv Pt ℓ) (hA : FSAEAD.MakesAtMostQueries A qR) :
    (multiSlotAdvCosted qR (fsCostedRedsInst C codec ℓ encT idOf qR) la A).IsQueryBoundP
      (isGameQuery (G := AEADScheme.otccaSpec
        (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt)) qR := by
  let _ := hA
  let Rm := (fsCostedRedsInst C codec ℓ encT idOf qR).multiRed la
  have hb := fsCostedRedsInst_bounds C codec ℓ encT idOf qR 0
  unfold fsCostedBounds at hb
  obtain ⟨-, -, hm, -⟩ := hb
  obtain ⟨-, -, hq, -⟩ := hm la
  change Rm.totalQueries (fun _ => 1) (fun _ => 0) qR ≤ qR at hq
  rcases (by
    change ((fsCostedRedsInst C codec ℓ encT idOf qR).multiRed la).chDone.queries
        (fun _ => 1) (fun _ => 0) = 0 ∧
      ((fsCostedRedsInst C codec ℓ encT idOf qR).multiRed la).handlePost.queries
        (fun _ => 1) (fun _ => 0) = 0
    generalize hR₀ : (fsCostedRedsInst C codec ℓ encT idOf qR).multiRed la = R₀
    dsimp only [fsCostedRedsInst,
      Computational.Proofs.ReductionDsl.FsAtomicBundles.fsCostedRedsInst,
      Computational.Proofs.ReductionDsl.MacroLift.guardTwoStageRed] at hR₀
    by_cases hℓ : ℓ < 10 ^ 6
    · simp only [hℓ, ↓reduceIte] at hR₀; subst hR₀; exact ⟨rfl, rfl⟩
    · simp only [hℓ, ↓reduceIte] at hR₀; subst hR₀; exact ⟨rfl, rfl⟩ :
    Rm.chDone.queries (fun _ => 1) (fun _ => 0) = 0 ∧
      Rm.handlePost.queries (fun _ => 1) (fun _ => 0) = 0) with ⟨hch0, hpost0⟩
  unfold multiSlotAdvCosted evalTwoStage1
  refine (isQueryBoundP_bind
    (Rm.eval1_queryBound _ (fun _ => 1) (fun _ => 0) (fun _ _ _ => le_rfl)
      (fun _ => by simp [isGameQuery])
      (fun _ => pubToADCosted (fsCostedRedsInst C codec ℓ encT idOf qR) A) () qR false)
    fun cm _ =>
      Rm.eval2_queryBound _ (fun _ => 1) (fun _ => 0) (fun _ _ _ => le_rfl)
        (fun _ => by simp [isGameQuery]) cm.2 () qR false).mono ?_
  dsimp only [TwoStageCostedReduction.totalQueries] at hq
  rw [hch0, hpost0] at hq ⊢
  simp only [Nat.max_zero, Nat.zero_max, Nat.mul_zero] at hq ⊢
  omega

alias multiSlotAdvWith_inst_queries := multiSlotAdvCosted_inst_queries

theorem multiSlotAdvAuthCosted_inst_queries (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (qR : ℕ) (la : Bool)
    (A : FsAdv Pt ℓ) (hA : FSAEAD.MakesAtMostQueries A qR) :
    (multiSlotAdvAuthCosted qR (fsCostedRedsInst C codec ℓ encT idOf qR) la A).IsQueryBoundP
      (isGameQuery (G := AEADScheme.otccaSpec
        (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt)) qR := by
  let _ := hA
  let Rm := (fsCostedRedsInst C codec ℓ encT idOf qR).multiRedAuth la
  have hb := fsCostedRedsInst_bounds C codec ℓ encT idOf qR 0
  unfold fsCostedBounds at hb
  obtain ⟨-, -, -, -, -, -, -, -, hm⟩ := hb
  obtain ⟨-, -, hq, -⟩ := hm la
  change Rm.totalQueries (fun _ => 1) (fun _ => 0) qR ≤ qR at hq
  rcases (by
    change ((fsCostedRedsInst C codec ℓ encT idOf qR).multiRedAuth la).chDone.queries
        (fun _ => 1) (fun _ => 0) = 0 ∧
      ((fsCostedRedsInst C codec ℓ encT idOf qR).multiRedAuth la).handlePost.queries
        (fun _ => 1) (fun _ => 0) = 0
    generalize hR₀ : (fsCostedRedsInst C codec ℓ encT idOf qR).multiRedAuth la = R₀
    dsimp only [fsCostedRedsInst,
      Computational.Proofs.ReductionDsl.FsAtomicBundles.fsCostedRedsInst,
      Computational.Proofs.ReductionDsl.MacroLift.guardTwoStageRed] at hR₀
    by_cases hℓ : ℓ < 10 ^ 6
    · simp only [hℓ, ↓reduceIte] at hR₀; subst hR₀; exact ⟨rfl, rfl⟩
    · simp only [hℓ, ↓reduceIte] at hR₀; subst hR₀; exact ⟨rfl, rfl⟩ :
    Rm.chDone.queries (fun _ => 1) (fun _ => 0) = 0 ∧
      Rm.handlePost.queries (fun _ => 1) (fun _ => 0) = 0) with ⟨hch0, hpost0⟩
  unfold multiSlotAdvAuthCosted evalTwoStage1
  refine (isQueryBoundP_bind
    (Rm.eval1_queryBound _ (fun _ => 1) (fun _ => 0) (fun _ _ _ => le_rfl)
      (fun _ => by simp [isGameQuery])
      (fun _ => pubToADCosted (fsCostedRedsInst C codec ℓ encT idOf qR) A) () qR false)
    fun cm _ =>
      Rm.eval2_queryBound _ (fun _ => 1) (fun _ => 0) (fun _ _ _ => le_rfl)
        (fun _ => by simp [isGameQuery]) cm.2 () qR false).mono ?_
  dsimp only [TwoStageCostedReduction.totalQueries] at hq
  rw [hch0, hpost0] at hq ⊢
  simp only [Nat.max_zero, Nat.zero_max, Nat.mul_zero] at hq ⊢
  omega

alias multiSlotAdvAuthWith_inst_queries := multiSlotAdvAuthCosted_inst_queries

omit [DecidableEq Pt] in
lemma pubToAD_clamped_eq (ℓ : ℕ) (A : FsAdv Pt ℓ) :
    pubToAD clampedProtoSignalCodec A = pubToAD protoSignalCodec A := rfl

theorem pubToADCosted_inst_eq (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (qR : ℕ)
    (hℓ : ℓ < 10 ^ 6) (A : FsAdv Pt ℓ) :
    pubToADCosted (fsCostedRedsInst C codec ℓ encT idOf qR) A = pubToAD protoSignalCodec A :=
  Computational.Proofs.ReductionDsl.FsAtomicSoundness.pubToADCosted_inst_eq
    C codec ℓ encT idOf qR hℓ A

alias pubToADWith_inst_eq := pubToADCosted_inst_eq

theorem saltRedComposed_inst_coinSimEquiv
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (qR j : ℕ)
    (hℓ : ℓ < 10 ^ 6) (hj : j ≤ 2 * (qR + maxForwardJumps + 1))
    (hinj : Function.Injective encT) (A : FsAdv Pt ℓ)
    (hA : FSAEAD.MakesAtMostQueries A qR) :
    CoinSimEquiv (saltPrfTargetIface ℓ Pt).fwdU
      ((fsCostedRedsInst C codec ℓ encT idOf qR).lSaltRed.eval
        (fun _ => ((fsCostedRedsInst C codec ℓ encT idOf qR).slotSaltRed j).eval
          (fun _ => multiSlotAdvCosted qR (fsCostedRedsInst C codec ℓ encT idOf qR)
            (FSAEAD.Thm5.isLookaheadHop j) A) ()) ())
      (lSaltRed C clampedProtoSignalCodec ℓ encT idOf
        (slotSaltRed C clampedProtoSignalCodec ℓ encT idOf
          (if FSAEAD.Thm5.isLookaheadHop j then qR + (maxForwardJumps + 1) else qR) (j / 2)
          (multiSlotAdv C clampedProtoSignalCodec ℓ encT idOf qR
            (FSAEAD.Thm5.isLookaheadHop j) A))) := by
  have hM := Computational.Proofs.ReductionDsl.FsAtomicSoundness.multiSlotAdvCosted_inst_coinSimEquiv
    C codec ℓ encT idOf qR (FSAEAD.Thm5.isLookaheadHop j) hℓ hinj A hA
  have hMq := Computational.Proofs.ReductionDsl.FsAtomicSoundness.multiSlotAdv_clamped_queries
    C ℓ encT idOf qR (FSAEAD.Thm5.isLookaheadHop j) A hA
  have hS := (CostedReduction.eval_coinSimEquiv_congr
    ((fsCostedRedsInst C codec ℓ encT idOf qR).slotSaltRed j) (fun _ => hM) ()).trans
    (Computational.Proofs.ReductionDsl.FsAtomicSoundness.slotSaltRed_inst_coinSimEquiv
      C codec ℓ encT idOf qR j hℓ hj hinj _ hMq)
  exact (CostedReduction.eval_coinSimEquiv_congr
    (fsCostedRedsInst C codec ℓ encT idOf qR).lSaltRed (fun _ => hS) ()).trans
    (Computational.Proofs.ReductionDsl.FsAtomicSoundness.lSaltRed_inst_coinSimEquiv
      C codec ℓ encT idOf qR hℓ hinj _)

theorem wireRedComposed_inst_coinSimEquiv
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (qR j : ℕ)
    (hℓ : ℓ < 10 ^ 6) (hj : j ≤ 2 * (qR + maxForwardJumps + 1))
    (hinj : Function.Injective encT) (A : FsAdv Pt ℓ)
    (hA : FSAEAD.MakesAtMostQueries A qR) :
    CoinSimEquiv (wireOtccaTargetIface ℓ Pt).fwdU
      ((fsCostedRedsInst C codec ℓ encT idOf qR).lWireRed.eval
        (fun _ => ((fsCostedRedsInst C codec ℓ encT idOf qR).slotWireRed j).eval
          (fun _ => multiSlotAdvCosted qR (fsCostedRedsInst C codec ℓ encT idOf qR)
            (FSAEAD.Thm5.isLookaheadHop j) A) ()) ())
      (lWireRed C clampedProtoSignalCodec ℓ encT idOf 0
        (slotWireRed C clampedProtoSignalCodec ℓ encT idOf (j / 2)
          (multiSlotAdv C clampedProtoSignalCodec ℓ encT idOf qR
            (FSAEAD.Thm5.isLookaheadHop j) A))) := by
  have hM := Computational.Proofs.ReductionDsl.FsAtomicSoundness.multiSlotAdvCosted_inst_coinSimEquiv
    C codec ℓ encT idOf qR (FSAEAD.Thm5.isLookaheadHop j) hℓ hinj A hA
  have hMq := Computational.Proofs.ReductionDsl.FsAtomicSoundness.multiSlotAdv_clamped_queries
    C ℓ encT idOf qR (FSAEAD.Thm5.isLookaheadHop j) A hA
  have hS := (CostedReduction.eval_coinSimEquiv_congr
    ((fsCostedRedsInst C codec ℓ encT idOf qR).slotWireRed j) (fun _ => hM) ()).trans
    (Computational.Proofs.ReductionDsl.FsAtomicSoundness.slotWireRed_inst_coinSimEquiv
      C codec ℓ encT idOf qR j hℓ hj hinj _ hMq)
  have hSq := Computational.Proofs.ReductionDsl.FsAtomicSoundness.slotWireRed_clamped_queries
    C ℓ encT idOf qR j _ hMq
  exact (CostedReduction.eval_coinSimEquiv_congr
    (fsCostedRedsInst C codec ℓ encT idOf qR).lWireRed (fun _ => hS) ()).trans
    (Computational.Proofs.ReductionDsl.FsAtomicSoundness.lWireRed_inst_coinSimEquiv
      C codec ℓ encT idOf qR hℓ hinj _ hSq)

theorem chainPRGTermWith_inst_eq_clamped
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (qR j : ℕ)
    (hℓ : ℓ < 10 ^ 6) (hj : j ≤ 2 * (qR + maxForwardJumps + 1))
    (hinj : Function.Injective encT) (A : FsAdv Pt ℓ)
    (hA : FSAEAD.MakesAtMostQueries A qR) :
    chainPRGTermCosted C qR (fsCostedRedsInst C codec ℓ encT idOf qR) A j =
      chainPRGTerm C clampedProtoSignalCodec ℓ encT idOf A j := by
  unfold chainPRGTermCosted chainPRGTerm
  exact prgAdvantage_congr (lChainPRG C.F (j / 2)) fun mt =>
    (Computational.Proofs.ReductionDsl.FsAtomicSoundness.prgRedZero_inst_coinSimEquiv
      C codec ℓ encT idOf qR j hℓ hj hinj A hA mt).evalDistEq_unifSpec

theorem saltPRFTermWith_inst_eq_clamped
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (qR j : ℕ)
    (hℓ : ℓ < 10 ^ 6) (hj : j ≤ 2 * (qR + maxForwardJumps + 1))
    (hinj : Function.Injective encT) (A : FsAdv Pt ℓ)
    (hA : FSAEAD.MakesAtMostQueries A qR) :
    saltPRFTermCosted C qR (fsCostedRedsInst C codec ℓ encT idOf qR) A j =
      saltPRFTerm C clampedProtoSignalCodec ℓ encT idOf qR A j := by
  unfold saltPRFTermCosted saltPRFTerm
  exact prfAdvantage_congr (lSaltPRF32 C.F)
    (saltRedComposed_inst_coinSimEquiv C codec ℓ encT idOf qR j hℓ hj hinj A hA)

theorem fsPrgMixWith_inst_eq_clamped {α : Type}
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (oa : ProbComp α) (idOf : α → Party → IdentityKey)
    (qR j : ℕ) (hℓ : ℓ < 10 ^ 6) (hj : j ≤ 2 * (qR + maxForwardJumps + 1))
    (hinj : Function.Injective encT)
    (A : α → FsAdv Pt ℓ) (hA : ∀ o, FSAEAD.MakesAtMostQueries (A o) qR) :
    CryptoVerification.E2E.fsChainPrgMixtureTerm C oa qR
        (fun o => fsCostedRedsInst C codec ℓ encT (idOf o) qR) A j =
      CryptoVerification.E2E.Signed.FSMix.fsPrgMix C clampedProtoSignalCodec ℓ encT
        oa idOf 25000 A j := by
  unfold CryptoVerification.E2E.fsChainPrgMixtureTerm
    CryptoVerification.E2E.Signed.FSMix.fsPrgMix
    CryptoVerification.E2E.prefixPrgAvg CryptoVerification.E2E.Signed.prgAvg
  exact prgAdvantage_congr (lChainPRG C.F (j / 2)) fun mt =>
    EvalDistEq.rfl.bind fun o =>
      (Computational.Proofs.ReductionDsl.FsAtomicSoundness.prgRedZero_inst_coinSimEquiv
        C codec ℓ encT (idOf o) qR j hℓ hj hinj (A o) (hA o) mt).evalDistEq_unifSpec

/-- Direct-output (`advBit`) slot-`j` PRG term matching `chainPRGTermAuthCosted`. -/
@[expose] noncomputable def chainPRGTermAuth (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (R : FsAdv Pt ℓ) (j : ℕ) : ℝ≥0∞ :=
  (lChainPRG C.F (j / 2)).prgAdvantage
    (Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out.cumulativeChainPrgReductionOut
      (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf) (lChainPRG C.F)
      maxForwardJumps j Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out.advBit
      (pubToAD codec R))

/-- Direct-output (`advBit`) slot-`j` salt-PRF term matching `saltPRFTermAuthCosted`. -/
@[expose] noncomputable def saltPRFTermAuth (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (qR : ℕ) (R : FsAdv Pt ℓ) (j : ℕ) : ℝ≥0∞ :=
  let la := FSAEAD.Thm5.isLookaheadHop j
  (lSaltPRF32 C.F).prfAdvantage
    (lSaltRed C codec ℓ encT idOf
      (slotSaltRed C codec ℓ encT idOf
        (if la then qR + (maxForwardJumps + 1) else qR) (j / 2)
        (Computational.Proofs.ReductionDsl.FsAtomicSoundness.multiSlotAdvAuth
          C codec ℓ encT idOf qR la R)))

/-- Direct-output (`advBit`) slot-`j` wire OT-CCA term matching `wireOtccaTermAuthCosted`. -/
@[expose] noncomputable def wireOtccaTermAuth (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (qR _qd : ℕ) (R : FsAdv Pt ℓ) (j : ℕ) :
    ℝ≥0∞ :=
  let la := FSAEAD.Thm5.isLookaheadHop j
  (lWire C codec ℓ).wireOtccaAdvantage
    (lWireRed C codec ℓ encT idOf 0
      (slotWireRed C codec ℓ encT idOf (j / 2)
        (Computational.Proofs.ReductionDsl.FsAtomicSoundness.multiSlotAdvAuth
          C codec ℓ encT idOf qR la R)))

/-- Uncosted direct-output multi-session FS-AEAD step bound at one session matching
`fsAuthCompBoundWith` and `E2E.fsAeadAuthSlotSumBound`. -/
@[expose] noncomputable def fsAuthCompBound (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (qR qd : ℕ)
    (A : Bool → Bool → FsAdv Pt ℓ) : ℝ≥0∞ :=
  2 * ∑ j ∈ Finset.range (fsSlotCount qR),
    let m := FSAEAD.Thm5.slotToHybridHopIndex qR j
    let la := FSAEAD.Thm5.isLookaheadHop m
    (chainPRGTermAuth C codec ℓ encT idOf (A false la) m +
      (2 * saltPRFTermAuth C codec ℓ encT idOf qR (A false la) m +
        wireOtccaTermAuth C codec ℓ encT idOf qR qd (A true la) m))

/-- Uncosted averaged direct-output chain-PRG term at hop `m`. -/
@[expose] noncomputable def fsAuthPrgMix {α : Type} (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (oa : ProbComp α) (idOf : α → Party → IdentityKey) (maxSkip : ℕ)
    (A : α → FsAdv Pt ℓ) (m : ℕ) : ℝ≥0∞ :=
  (lChainPRG C.F (m / 2)).prgAdvantage
    (CryptoVerification.E2E.Signed.prgAvg oa fun o =>
      Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out.cumulativeChainPrgReductionOut
        (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT (idOf o))
        (lChainPRG C.F) maxSkip m Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out.advBit
        (pubToAD codec (A o)))

/-- Uncosted averaged direct-output salt-PRF (`Afalse`) + wire OT-CCA (`Atrue`) term at hop `m`. -/
@[expose] noncomputable def fsAuthSWMix {α : Type} (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (oa : ProbComp α) (idOf : α → Party → IdentityKey) (maxSkip q : ℕ)
    (Afalse Atrue : α → FsAdv Pt ℓ) (m : ℕ) : ℝ≥0∞ :=
  let la := FSAEAD.Thm5.isLookaheadHop m
  2 * (lSaltPRF32 C.F).prfAdvantage
      (CryptoVerification.E2E.Signed.prfAvg oa fun o => lSaltRed C codec ℓ encT (idOf o)
        (slotSaltRed C codec ℓ encT (idOf o) (if la then q + (maxSkip + 1) else q) (m / 2)
          (Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out.multiSlotOtccaReductionOut
            (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT (idOf o)) (lChainPRG C.F) maxSkip
            (if la then q + (maxSkip + 1) else q) la
            Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out.advBit
            (pubToAD codec (Afalse o))))) +
    (lWire C codec ℓ).wireOtccaAdvantage
      (CryptoVerification.E2E.Signed.FSMix.wireAvg oa fun o => lWireRed C codec ℓ encT (idOf o) 0
        (slotWireRed C codec ℓ encT (idOf o) (m / 2)
          (Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out.multiSlotOtccaReductionOut
            (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT (idOf o)) (lChainPRG C.F) maxSkip
            (if la then q + (maxSkip + 1) else q) la
            Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out.advBit
            (pubToAD codec (Atrue o)))))

/-- Uncosted averaged direct-output multi-session FS-AEAD step bound matching
`E2E.fsAeadAuthMixtureCompBound`. -/
@[expose] noncomputable def fsAuthCompBoundMix {α : Type} (C : Crypto) (codec : SignalMessageProtoCodec)
    (ℓ : ℕ) (encT : Pt → PublicKey) (oa : ProbComp α) (idOf : α → Party → IdentityKey)
    (maxSkip qR : ℕ) (A : Bool → Bool → α → FsAdv Pt ℓ) : ℝ≥0∞ :=
  2 * ∑ j ∈ Finset.range (FSAEAD.Thm5.slotCount maxSkip qR),
    let m := FSAEAD.Thm5.slotToHybridHopIndex qR j
    let la := FSAEAD.Thm5.isLookaheadHop m
    (fsAuthPrgMix C codec ℓ encT oa idOf maxSkip (A false la) m +
      fsAuthSWMix C codec ℓ encT oa idOf maxSkip qR (A false la) (A true la) m)

theorem saltRedAuthComposed_inst_coinSimEquiv
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (qR j : ℕ)
    (hℓ : ℓ < 10 ^ 6) (hj : j ≤ 2 * (qR + maxForwardJumps + 1))
    (hinj : Function.Injective encT) (A : FsAdv Pt ℓ)
    (hA : FSAEAD.MakesAtMostQueries A qR) :
    CoinSimEquiv (saltPrfTargetIface ℓ Pt).fwdU
      ((fsCostedRedsInst C codec ℓ encT idOf qR).lSaltRed.eval
        (fun _ => ((fsCostedRedsInst C codec ℓ encT idOf qR).slotSaltRed j).eval
          (fun _ => multiSlotAdvAuthCosted qR (fsCostedRedsInst C codec ℓ encT idOf qR)
            (FSAEAD.Thm5.isLookaheadHop j) A) ()) ())
      (lSaltRed C clampedProtoSignalCodec ℓ encT idOf
        (slotSaltRed C clampedProtoSignalCodec ℓ encT idOf
          (if FSAEAD.Thm5.isLookaheadHop j then qR + (maxForwardJumps + 1) else qR) (j / 2)
          (Computational.Proofs.ReductionDsl.FsAtomicSoundness.multiSlotAdvAuth
            C clampedProtoSignalCodec ℓ encT idOf qR (FSAEAD.Thm5.isLookaheadHop j) A))) := by
  have hM :=
    Computational.Proofs.ReductionDsl.FsAtomicSoundness.multiSlotAdvAuthCosted_inst_coinSimEquiv
      C codec ℓ encT idOf qR (FSAEAD.Thm5.isLookaheadHop j) hℓ hinj A hA
  have hMq := Computational.Proofs.ReductionDsl.FsAtomicSoundness.multiSlotAdvAuth_clamped_queries
    C ℓ encT idOf qR (FSAEAD.Thm5.isLookaheadHop j) A hA
  have hS := (CostedReduction.eval_coinSimEquiv_congr
    ((fsCostedRedsInst C codec ℓ encT idOf qR).slotSaltRed j) (fun _ => hM) ()).trans
    (Computational.Proofs.ReductionDsl.FsAtomicSoundness.slotSaltRed_inst_coinSimEquiv
      C codec ℓ encT idOf qR j hℓ hj hinj _ hMq)
  exact (CostedReduction.eval_coinSimEquiv_congr
    (fsCostedRedsInst C codec ℓ encT idOf qR).lSaltRed (fun _ => hS) ()).trans
    (Computational.Proofs.ReductionDsl.FsAtomicSoundness.lSaltRed_inst_coinSimEquiv
      C codec ℓ encT idOf qR hℓ hinj _)

theorem wireRedAuthComposed_inst_coinSimEquiv
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (qR j : ℕ)
    (hℓ : ℓ < 10 ^ 6) (hj : j ≤ 2 * (qR + maxForwardJumps + 1))
    (hinj : Function.Injective encT) (A : FsAdv Pt ℓ)
    (hA : FSAEAD.MakesAtMostQueries A qR) :
    CoinSimEquiv (wireOtccaTargetIface ℓ Pt).fwdU
      ((fsCostedRedsInst C codec ℓ encT idOf qR).lWireRed.eval
        (fun _ => ((fsCostedRedsInst C codec ℓ encT idOf qR).slotWireRed j).eval
          (fun _ => multiSlotAdvAuthCosted qR (fsCostedRedsInst C codec ℓ encT idOf qR)
            (FSAEAD.Thm5.isLookaheadHop j) A) ()) ())
      (lWireRed C clampedProtoSignalCodec ℓ encT idOf 0
        (slotWireRed C clampedProtoSignalCodec ℓ encT idOf (j / 2)
          (Computational.Proofs.ReductionDsl.FsAtomicSoundness.multiSlotAdvAuth
            C clampedProtoSignalCodec ℓ encT idOf qR (FSAEAD.Thm5.isLookaheadHop j) A))) := by
  have hM :=
    Computational.Proofs.ReductionDsl.FsAtomicSoundness.multiSlotAdvAuthCosted_inst_coinSimEquiv
      C codec ℓ encT idOf qR (FSAEAD.Thm5.isLookaheadHop j) hℓ hinj A hA
  have hMq := Computational.Proofs.ReductionDsl.FsAtomicSoundness.multiSlotAdvAuth_clamped_queries
    C ℓ encT idOf qR (FSAEAD.Thm5.isLookaheadHop j) A hA
  have hS := (CostedReduction.eval_coinSimEquiv_congr
    ((fsCostedRedsInst C codec ℓ encT idOf qR).slotWireRed j) (fun _ => hM) ()).trans
    (Computational.Proofs.ReductionDsl.FsAtomicSoundness.slotWireRed_inst_coinSimEquiv
      C codec ℓ encT idOf qR j hℓ hj hinj _ hMq)
  have hSq := Computational.Proofs.ReductionDsl.FsAtomicSoundness.slotWireRed_clamped_queries
    C ℓ encT idOf qR j _ hMq
  exact (CostedReduction.eval_coinSimEquiv_congr
    (fsCostedRedsInst C codec ℓ encT idOf qR).lWireRed (fun _ => hS) ()).trans
    (Computational.Proofs.ReductionDsl.FsAtomicSoundness.lWireRed_inst_coinSimEquiv
      C codec ℓ encT idOf qR hℓ hinj _ hSq)

theorem chainPRGTermAuthWith_inst_eq_clamped
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (qR j : ℕ)
    (hℓ : ℓ < 10 ^ 6) (hj : j ≤ 2 * (qR + maxForwardJumps + 1))
    (hinj : Function.Injective encT) (A : FsAdv Pt ℓ)
    (hA : FSAEAD.MakesAtMostQueries A qR) :
    chainPRGTermAuthCosted C qR (fsCostedRedsInst C codec ℓ encT idOf qR) A j =
      chainPRGTermAuth C clampedProtoSignalCodec ℓ encT idOf A j := by
  unfold chainPRGTermAuthCosted chainPRGTermAuth
  exact prgAdvantage_congr (lChainPRG C.F (j / 2)) fun mt =>
    (Computational.Proofs.ReductionDsl.FsAtomicSoundness.prgRedAuth_inst_coinSimEquiv
      C codec ℓ encT idOf qR j hℓ hj hinj A hA mt).evalDistEq_unifSpec

theorem saltPRFTermAuthWith_inst_eq_clamped
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (qR j : ℕ)
    (hℓ : ℓ < 10 ^ 6) (hj : j ≤ 2 * (qR + maxForwardJumps + 1))
    (hinj : Function.Injective encT) (A : FsAdv Pt ℓ)
    (hA : FSAEAD.MakesAtMostQueries A qR) :
    saltPRFTermAuthCosted C qR (fsCostedRedsInst C codec ℓ encT idOf qR) A j =
      saltPRFTermAuth C clampedProtoSignalCodec ℓ encT idOf qR A j := by
  unfold saltPRFTermAuthCosted saltPRFTermAuth
  exact prfAdvantage_congr (lSaltPRF32 C.F)
    (saltRedAuthComposed_inst_coinSimEquiv C codec ℓ encT idOf qR j hℓ hj hinj A hA)

theorem fsAuthPrgMixWith_inst_eq_clamped {α : Type}
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (oa : ProbComp α) (idOf : α → Party → IdentityKey)
    (qR j : ℕ) (hℓ : ℓ < 10 ^ 6) (hj : j ≤ 2 * (qR + maxForwardJumps + 1))
    (hinj : Function.Injective encT)
    (A : α → FsAdv Pt ℓ) (hA : ∀ o, FSAEAD.MakesAtMostQueries (A o) qR) :
    (lChainPRG C.F (j / 2)).prgAdvantage
        (CryptoVerification.E2E.prefixPrgAvg oa fun o =>
          fun mt =>
            evalTwoStage1 ((fsCostedRedsInst C codec ℓ encT (idOf o) qR).prgRedAuth j) qR false
              (fun _ => pubToADCosted (fsCostedRedsInst C codec ℓ encT (idOf o) qR) (A o)) mt) =
      fsAuthPrgMix C clampedProtoSignalCodec ℓ encT oa idOf 25000 A j := by
  unfold fsAuthPrgMix CryptoVerification.E2E.prefixPrgAvg CryptoVerification.E2E.Signed.prgAvg
  exact prgAdvantage_congr (lChainPRG C.F (j / 2)) fun mt =>
    EvalDistEq.rfl.bind fun o =>
      (Computational.Proofs.ReductionDsl.FsAtomicSoundness.prgRedAuth_inst_coinSimEquiv
        C codec ℓ encT (idOf o) qR j hℓ hj hinj (A o) (hA o) mt).evalDistEq_unifSpec

/-! ### 3. Clamped-to-`protoSignalCodec` bridges under `EncMsgsOk atomicShortB` -/

omit [DecidableEq Pt] in
private lemma run_simulateQ_eq_of_dis {κ : Type} {spec : OracleSpec.{0, 0} κ}
    {m : Type → Type} [Monad m] [LawfulMonad m] {α σ : Type}
    {impl₁ impl₂ : QueryImpl spec (StateT σ m)}
    {dis : κ → Prop} [DecidablePred dis]
    (oa : OracleComp spec α) (hoa : oa.IsQueryBoundP dis 0) (s : σ)
    (hstep : ∀ t s, ¬dis t → (impl₁ t).run s = (impl₂ t).run s) :
    (simulateQ impl₁ oa).run s = (simulateQ impl₂ oa).run s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => rfl
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hoa
    obtain ⟨hdis, hk⟩ := hoa
    have hndis : ¬dis t := by simpa using hdis
    simp only [hndis, ↓reduceIte] at hk
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind]
    rw [hstep t s hndis]
    exact bind_congr fun z => ih z.1 (hk z.1) z.2

omit [DecidableEq Pt] in
private lemma multiEncIdxWith_clamped_eq {m : Type → Type}
    [Monad m] [MonadLiftT ProbComp m]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (t mSlot : ℕ)
    (ops₁ ops₂ : Option (FSAEAD.Thm5.SpecialOps (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt m))
    (his : ops₁.isSome = ops₂.isSome)
    (henc : ∀ o₁ o₂, ops₁ = some o₁ → ops₂ = some o₂ → ∀ i a msg,
      atomicShortB a.2 = true → o₁.enc (i, a) msg = o₂.enc (i, a) msg)
    (i : ℕ) (a : Header Pt × LibsignalMsgPublicPart) (msg : Plain ℓ)
    (ha : atomicShortB a.2 = true) :
    FSAEAD.Thm5.multiEncIdxWith (CK := BitVec 256) (lIdeal C clampedProtoSignalCodec ℓ encT)
        (lAeadR C clampedProtoSignalCodec ℓ encT idOf) t mSlot ops₁ i a msg =
      FSAEAD.Thm5.multiEncIdxWith (CK := BitVec 256) (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) t mSlot ops₂ i a msg := by
  unfold FSAEAD.Thm5.multiEncIdxWith
  refine congrArg (Bind.bind FSAEAD.Thm5.getH) (funext fun st => ?_)
  have hk : FSAEAD.Thm5.multiKind t mSlot ops₁ st i = FSAEAD.Thm5.multiKind t mSlot ops₂ st i := by
    unfold FSAEAD.Thm5.multiKind; rw [his]
  rw [hk]
  generalize FSAEAD.Thm5.multiKind t mSlot ops₂ st i = κ
  have hid := lIdeal_clamped_eq C ℓ encT (i, a) ha
  have hkeys : ∀ K, (lAeadR C clampedProtoSignalCodec ℓ encT idOf).enc K (i, a) msg =
      (lAeadR C protoSignalCodec ℓ encT idOf).enc K (i, a) msg :=
    fun K => lAeadR_clamped_enc_eq C ℓ encT idOf K (i, a) msg ha
  cases κ with
  | ideal => simp only [hid]
  | special =>
    cases h1 : ops₁ <;> cases h2 : ops₂
    · simp only [hid, hkeys]
    · simp [h1, h2] at his
    · simp [h1, h2] at his
    · rename_i o₁ o₂
      simp only [henc o₁ o₂ h1 h2 i a msg ha]
  | real => simp only [hid, hkeys]

omit [DecidableEq Pt] in
private lemma multiDecIdx_clamped_eq {m : Type → Type} [Monad m]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (t mSlot : ℕ)
    (ops₁ ops₂ : Option (FSAEAD.Thm5.SpecialOps (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt m))
    (his : ops₁.isSome = ops₂.isSome)
    (hdec : ∀ o₁ o₂, ops₁ = some o₁ → ops₂ = some o₂ → o₁.dec = o₂.dec)
    (hint : Option (Plain ℓ)) (i : ℕ) (a : Header Pt × LibsignalMsgPublicPart) (e : LCt) :
    FSAEAD.Thm5.multiDecIdx (CK := BitVec 256)
        (lAeadR C clampedProtoSignalCodec ℓ encT idOf) t mSlot ops₁ hint i a e =
      FSAEAD.Thm5.multiDecIdx (CK := BitVec 256)
        (lAeadR C protoSignalCodec ℓ encT idOf) t mSlot ops₂ hint i a e := by
  unfold FSAEAD.Thm5.multiDecIdx
  cases hint with
  | some msg => rfl
  | none =>
    dsimp only
    refine congrArg (Bind.bind FSAEAD.Thm5.getH) (funext fun st => ?_)
    have hk : FSAEAD.Thm5.multiKind t mSlot ops₁ st i =
        FSAEAD.Thm5.multiKind t mSlot ops₂ st i := by
      unfold FSAEAD.Thm5.multiKind; rw [his]
    rw [hk, lAeadR_clamped_dec_eq]
    generalize FSAEAD.Thm5.multiKind t mSlot ops₂ st i = κ
    cases κ with
    | ideal => rfl
    | special =>
      cases h1 : ops₁ <;> cases h2 : ops₂
      · rfl
      · simp [h1, h2] at his
      · simp [h1, h2] at his
      · rename_i o₁ o₂
        simp only [hdec o₁ o₂ h1 h2]
    | real => rfl

private lemma multiImplWith_clamped_run_eq {m : Type → Type} [Monad m] [LawfulMonad m]
    [MonadLiftT ProbComp m]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (P : FSAEAD.Thm5.Params) (mSlot : ℕ)
    (ops₁ ops₂ : Option (FSAEAD.Thm5.SpecialOps (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt
      m))
    (his : ops₁.isSome = ops₂.isSome)
    (henc : ∀ o₁ o₂, ops₁ = some o₁ → ops₂ = some o₂ → ∀ i a msg,
      atomicShortB a.2 = true → o₁.enc (i, a) msg = o₂.enc (i, a) msg)
    (hdec : ∀ o₁ o₂, ops₁ = some o₁ → ops₂ = some o₂ → o₁.dec = o₂.dec)
    (B : FSAEAD.Adversary (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256))
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) (ℕ × LCt))
    (hB : FSAEAD.EncADsOk (fun ap : Header Pt × LibsignalMsgPublicPart => atomicShortB ap.2) B)
    (s : FSAEAD.Thm5.HSt (BitVec 256) (BitVec 256) (Header Pt × LibsignalMsgPublicPart)
      (Plain ℓ) LCt) :
    (simulateQ (FSAEAD.Thm5.multiImplWith (lIdeal C clampedProtoSignalCodec ℓ encT)
      (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps P mSlot
      (FSAEAD.Thm5.DG (lChainPRG C.F)) ops₁) B).run s =
    (simulateQ (FSAEAD.Thm5.multiImplWith (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps P mSlot
      (FSAEAD.Thm5.DG (lChainPRG C.F)) ops₂) B).run s := by
  have hrec : ∀ hint a c,
      FSAEAD.Thm5.multiReceiveH (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F)
        maxForwardJumps P mSlot (FSAEAD.Thm5.DG (lChainPRG C.F)) ops₁ hint a c =
      FSAEAD.Thm5.multiReceiveH (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F)
        maxForwardJumps P mSlot (FSAEAD.Thm5.DG (lChainPRG C.F)) ops₂ hint a c := by
    intro hint a c
    unfold FSAEAD.Thm5.multiReceiveH
    simp only [multiDecIdx_clamped_eq C ℓ encT idOf _ mSlot ops₁ ops₂ his hdec]
  refine run_simulateQ_eq_of_dis B hB s fun t st ht => ?_
  rcases t with n | (((((⟨a, msg⟩ | ⟨a, m0, m1⟩) | u) | u) | ⟨a, c⟩) | ⟨a, c⟩)
  · dsimp only [FSAEAD.Thm5.multiImplWith, QueryImpl.add_apply_inl]
  · have ha : atomicShortB a.2 = true := by simpa [FSAEAD.encBadAD] using ht
    show (FSAEAD.Thm5.multiTransmitHWith (lIdeal C clampedProtoSignalCodec ℓ encT) (lAeadR C clampedProtoSignalCodec ℓ encT idOf)
        (lChainPRG C.F) P mSlot (FSAEAD.Thm5.DG (lChainPRG C.F)) ops₁ (a, msg)).run st =
      (FSAEAD.Thm5.multiTransmitHWith (lIdeal C protoSignalCodec ℓ encT) (lAeadR C protoSignalCodec ℓ encT idOf)
        (lChainPRG C.F) P mSlot (FSAEAD.Thm5.DG (lChainPRG C.F)) ops₂ (a, msg)).run st
    unfold FSAEAD.Thm5.multiTransmitHWith
    simp only [multiEncIdxWith_clamped_eq C ℓ encT idOf _ mSlot ops₁ ops₂ his henc _ a _ ha]
  · have ha : atomicShortB a.2 = true := by simpa [FSAEAD.encBadAD] using ht
    show (FSAEAD.Thm5.multiChallengeHWith (lIdeal C clampedProtoSignalCodec ℓ encT) (lAeadR C clampedProtoSignalCodec ℓ encT idOf)
        (lChainPRG C.F) P mSlot (FSAEAD.Thm5.DG (lChainPRG C.F)) ops₁ (a, m0, m1)).run st =
      (FSAEAD.Thm5.multiChallengeHWith (lIdeal C protoSignalCodec ℓ encT) (lAeadR C protoSignalCodec ℓ encT idOf)
        (lChainPRG C.F) P mSlot (FSAEAD.Thm5.DG (lChainPRG C.F)) ops₂ (a, m0, m1)).run st
    unfold FSAEAD.Thm5.multiChallengeHWith
    simp only [multiEncIdxWith_clamped_eq C ℓ encT idOf _ mSlot ops₁ ops₂ his henc _ a _ ha]
  · show (FSAEAD.Thm5.corruptSenderH (m := m) (AD := Header Pt × LibsignalMsgPublicPart)
        (M := Plain ℓ) (C := LCt) (lChainPRG C.F) P u).run st =
      (FSAEAD.Thm5.corruptSenderH (m := m) (AD := Header Pt × LibsignalMsgPublicPart)
        (M := Plain ℓ) (C := LCt) (lChainPRG C.F) P u).run st
    rfl
  · show (FSAEAD.Thm5.corruptReceiverH (m := m) (AD := Header Pt × LibsignalMsgPublicPart)
        (M := Plain ℓ) (C := LCt) (MK := BitVec 256) (lChainPRG C.F) P u).run st =
      (FSAEAD.Thm5.corruptReceiverH (m := m) (AD := Header Pt × LibsignalMsgPublicPart)
        (M := Plain ℓ) (C := LCt) (MK := BitVec 256) (lChainPRG C.F) P u).run st
    rfl
  · show (FSAEAD.Thm5.multiDeliverH (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F)
        maxForwardJumps P mSlot (FSAEAD.Thm5.DG (lChainPRG C.F)) ops₁ (a, c)).run st =
      (FSAEAD.Thm5.multiDeliverH (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F)
        maxForwardJumps P mSlot (FSAEAD.Thm5.DG (lChainPRG C.F)) ops₂ (a, c)).run st
    unfold FSAEAD.Thm5.multiDeliverH
    simp only [hrec]
  · show (FSAEAD.Thm5.multiInjectH (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F)
        maxForwardJumps P mSlot (FSAEAD.Thm5.DG (lChainPRG C.F)) ops₁ (a, c)).run st =
      (FSAEAD.Thm5.multiInjectH (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F)
        maxForwardJumps P mSlot (FSAEAD.Thm5.DG (lChainPRG C.F)) ops₂ (a, c)).run st
    unfold FSAEAD.Thm5.multiInjectH
    simp only [hrec]

omit [DecidableEq Pt] in
private lemma pubToAD_encADsOk (ℓ : ℕ) (A : FsAdv Pt ℓ)
    (hshort : FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) A) :
    FSAEAD.EncADsOk (fun ap : Header Pt × LibsignalMsgPublicPart => atomicShortB ap.2)
      (pubToAD protoSignalCodec A) :=
  CryptoGames.LibsignalSM.Proofs.ProstPubToAD.pubRed_encADsOk
    atomicShortB (fun c : ℕ × LCt => lPubOf protoSignalCodec c.2) A hshort

theorem cumulativeChainPrgReduction_clamped_eq
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (j : ℕ)
    (A : FsAdv Pt ℓ)
    (hshort : FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) A)
    (mt : BitVec 256 × BitVec 256) :
    FSAEAD.Thm5.cumulativeChainPrgReduction (lIdeal C clampedProtoSignalCodec ℓ encT)
        (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps j
        (pubToAD clampedProtoSignalCodec A) mt =
      FSAEAD.Thm5.cumulativeChainPrgReduction (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps j
        (pubToAD protoSignalCodec A) mt := by
  have hA' := pubToAD_encADsOk ℓ A hshort
  rw [pubToAD_clamped_eq ℓ A]
  unfold FSAEAD.Thm5.cumulativeChainPrgReduction FSAEAD.Thm5.hRunWith
  rw [← CryptoGames.FSAEAD.Thm5.Costed.multiImplWith_zero_none
      (lIdeal C clampedProtoSignalCodec ℓ encT)
      (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
      (FSAEAD.Thm5.hp (j / 2) 0 (FSAEAD.Thm5.isLookaheadHop j)) (FSAEAD.Thm5.DG (lChainPRG C.F)) rfl,
    ← CryptoGames.FSAEAD.Thm5.Costed.multiImplWith_zero_none
      (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
      (FSAEAD.Thm5.hp (j / 2) 0 (FSAEAD.Thm5.isLookaheadHop j)) (FSAEAD.Thm5.DG (lChainPRG C.F)) rfl]
  refine bind_congr fun b => ?_
  rw [multiImplWith_clamped_run_eq C ℓ encT idOf _ 0 none none rfl
    (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) _ hA' _]

theorem multiSlotAdv_clamped_eq
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (qR : ℕ) (la : Bool) (A : FsAdv Pt ℓ)
    (hshort : FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) A) :
    multiSlotAdv C clampedProtoSignalCodec ℓ encT idOf qR la A =
      multiSlotAdv C protoSignalCodec ℓ encT idOf qR la A := by
  have hA' := pubToAD_encADsOk ℓ A hshort
  unfold multiSlotAdv FSAEAD.Thm5.multiSlotOtccaReduction FSAEAD.Thm5.multiRunWith
  rw [pubToAD_clamped_eq ℓ A]
  refine bind_congr fun b => ?_
  rw [multiImplWith_clamped_run_eq C ℓ encT idOf _ _
    (some (FSAEAD.Thm5.otOpsWith (lIdeal C clampedProtoSignalCodec ℓ encT)))
    (some (FSAEAD.Thm5.otOpsWith (lIdeal C protoSignalCodec ℓ encT))) rfl
    (fun _ _ h1 h2 i a msg ha => by
      cases h1; cases h2
      dsimp only [FSAEAD.Thm5.otOpsWith]
      rw [lIdeal_clamped_eq C ℓ encT (i, a) ha])
    (fun _ _ h1 h2 => by cases h1; cases h2; rfl) _ hA' _]

private lemma slotRedImpl_congr_at {AD M Ct SL SR : Type}
    (implL₁ implL₂ : QueryImpl (FSAEAD.Thm5.IndexedOtccaSpec AD M Ct) (StateT SL ProbComp))
    (implR₁ implR₂ : QueryImpl (FSAEAD.Thm5.IndexedOtccaSpec AD M Ct) (StateT SR ProbComp))
    (k : ℕ) (t : (FSAEAD.Thm5.IndexedOtccaSpec AD M Ct).Domain)
    (hL : implL₁ t = implL₂ t) (hR : implR₁ t = implR₂ t) :
    FSAEAD.Thm5.slotRedImpl implL₁ implR₁ k t = FSAEAD.Thm5.slotRedImpl implL₂ implR₂ k t := by
  rcases t with n | (⟨h, m⟩ | ⟨h, e⟩)
  · rfl
  · simp only [FSAEAD.Thm5.slotRedImpl, hL, hR]
  · simp only [FSAEAD.Thm5.slotRedImpl, hL, hR]

private lemma slotSaltImpl_clamped_eq
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (b : Bool)
    (t : (FSAEAD.Thm5.IndexedOtccaSpec (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt).Domain)
    (ht : ¬(AEADScheme.otEncBad
      (fun ia : ℕ × (Header Pt × LibsignalMsgPublicPart) => atomicShortB ia.2.2) t = true)) :
    slotSaltImpl C clampedProtoSignalCodec ℓ encT idOf b t =
      slotSaltImpl C protoSignalCodec ℓ encT idOf b t ∧
    slotSaltImplNF C clampedProtoSignalCodec ℓ encT idOf b t =
      slotSaltImplNF C protoSignalCodec ℓ encT idOf b t := by
  rcases t with n | (⟨a, m⟩ | ⟨a, e⟩)
  · exact ⟨rfl, rfl⟩
  · have ha : atomicShortB a.2.2 = true := by simpa [AEADScheme.otEncBad] using ht
    have hid := lIdeal_clamped_eq C ℓ encT a ha
    have henc : ∀ mk, (lAeadK C clampedProtoSignalCodec ℓ encT idOf).enc mk ((a.1, a.2.1), a.2.2) m =
        (lAeadK C protoSignalCodec ℓ encT idOf).enc mk ((a.1, a.2.1), a.2.2) m :=
      fun mk => lAeadK_clamped_enc_eq C ℓ encT idOf mk ((a.1, a.2.1), a.2.2) m ha
    exact ⟨by simp only [slotSaltImpl, hid, henc], by simp only [slotSaltImplNF, hid, henc]⟩
  · exact ⟨by simp only [slotSaltImpl, lAeadK_clamped_dec_eq],
      by simp only [slotSaltImplNF, lAeadK_clamped_dec_eq]⟩

private lemma otImpl_clamped_eq
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (t : (FSAEAD.Thm5.IndexedOtccaSpec (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt).Domain)
    (ht : ¬(AEADScheme.otEncBad
      (fun ia : ℕ × (Header Pt × LibsignalMsgPublicPart) => atomicShortB ia.2.2) t = true)) :
    FSAEAD.Thm5.otImpl (lIdeal C clampedProtoSignalCodec ℓ encT)
        (lAeadR C clampedProtoSignalCodec ℓ encT idOf) t =
      FSAEAD.Thm5.otImpl (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) t := by
  rcases t with n | (⟨a, m⟩ | ⟨a, e⟩)
  · simp only [FSAEAD.Thm5.otImpl, QueryImpl.add_apply_inl]
  · have ha : atomicShortB a.2.2 = true := by simpa [AEADScheme.otEncBad] using ht
    have hid := lIdeal_clamped_eq C ℓ encT a ha
    have henc : ∀ K, (lAeadR C clampedProtoSignalCodec ℓ encT idOf).enc K a m =
        (lAeadR C protoSignalCodec ℓ encT idOf).enc K a m :=
      fun K => lAeadR_clamped_enc_eq C ℓ encT idOf K a m ha
    simp only [FSAEAD.Thm5.otImpl, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
      AEADScheme.otccaEncryptAdIdeal, hid, henc]
  · simp only [FSAEAD.Thm5.otImpl, QueryImpl.add_apply_inr, AEADScheme.otccaDecrypt,
      lAeadR_clamped_dec_eq]

theorem slotSaltRed_clamped_eq
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N k : ℕ)
    (B : OTCCAAdversary (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt)
    (hB : AEADScheme.OTEncADsOk
      (fun ia : ℕ × (Header Pt × LibsignalMsgPublicPart) => atomicShortB ia.2.2) B) :
    slotSaltRed C clampedProtoSignalCodec ℓ encT idOf N k B =
      slotSaltRed C protoSignalCodec ℓ encT idOf N k B := by
  unfold slotSaltRed
  refine bind_congr fun K₀ => bind_congr fun ks => ?_
  refine congrArg (Prod.fst <$> ·) ?_
  refine run_simulateQ_eq_of_dis B hB _ fun t s ht => ?_
  rw [slotRedImpl_congr_at _ _ _ _ k t (otImpl_clamped_eq C ℓ encT idOf t ht)
    (slotSaltImpl_clamped_eq C ℓ encT idOf false t ht).1]

theorem slotWireRed_clamped_eq
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (k : ℕ)
    (B : OTCCAAdversary (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt)
    (hB : AEADScheme.OTEncADsOk
      (fun ia : ℕ × (Header Pt × LibsignalMsgPublicPart) => atomicShortB ia.2.2) B) :
    slotWireRed C clampedProtoSignalCodec ℓ encT idOf k B =
      slotWireRed C protoSignalCodec ℓ encT idOf k B := by
  unfold slotWireRed
  refine congrArg (Prod.fst <$> ·) ?_
  refine run_simulateQ_eq_of_dis B hB _ fun t s ht => ?_
  rw [slotRedImpl_congr_at _ _ _ _ k t (slotSaltImpl_clamped_eq C ℓ encT idOf false t ht).2
    (slotSaltImpl_clamped_eq C ℓ encT idOf true t ht).1]

theorem lSaltRed_clamped_eq
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (B : OTCCAAdversary (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt)
    (hB : AEADScheme.OTEncADsOk
      (fun ia : ℕ × (Header Pt × LibsignalMsgPublicPart) => atomicShortB ia.2.2) B) :
    lSaltRed C clampedProtoSignalCodec ℓ encT idOf B =
      lSaltRed C protoSignalCodec ℓ encT idOf B := by
  unfold lSaltRed
  refine bind_congr fun b => ?_
  simp only [StateT.run']
  refine congrArg (fun p => (Prod.fst <$> p) >>= _) ?_
  refine run_simulateQ_eq_of_dis B hB none fun t s ht => ?_
  rcases t with n | (⟨a, m⟩ | ⟨a, e⟩)
  · rfl
  · have ha : atomicShortB a.2.2 = true := by simpa [AEADScheme.otEncBad] using ht
    have hid := lIdeal_clamped_eq C ℓ encT a ha
    have henc : ∀ mk, (lAeadK C clampedProtoSignalCodec ℓ encT idOf).enc mk ((a.1, a.2.1), a.2.2) m =
        (lAeadK C protoSignalCodec ℓ encT idOf).enc mk ((a.1, a.2.1), a.2.2) m :=
      fun mk => lAeadK_clamped_enc_eq C ℓ encT idOf mk ((a.1, a.2.1), a.2.2) m ha
    simp only [hid, henc]
  · simp only [lAeadK_clamped_dec_eq]

private lemma multiSlotAdv_otEncADsOk
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (qR : ℕ) (la : Bool) (A : FsAdv Pt ℓ)
    (hshort : FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) A) :
    AEADScheme.OTEncADsOk
      (fun ia : ℕ × (Header Pt × LibsignalMsgPublicPart) => atomicShortB ia.2.2)
      (multiSlotAdv C protoSignalCodec ℓ encT idOf qR la A) :=
  CryptoGames.LibsignalSM.Proofs.ProstFSAEADBound.multiRedWith_otEncADsOk
    (fun ap : Header Pt × LibsignalMsgPublicPart => atomicShortB ap.2)
    (lIdeal C protoSignalCodec ℓ encT) (lAeadR C protoSignalCodec ℓ encT idOf)
    (lChainPRG C.F) maxForwardJumps (if la then qR + (maxForwardJumps + 1) else qR) la
    (pubToAD protoSignalCodec A) (pubToAD_encADsOk ℓ A hshort)

private lemma slotSaltRed_otEncADsOk
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N k : ℕ)
    (B : OTCCAAdversary (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt)
    (hB : AEADScheme.OTEncADsOk
      (fun ia : ℕ × (Header Pt × LibsignalMsgPublicPart) => atomicShortB ia.2.2) B) :
    AEADScheme.OTEncADsOk
      (fun ia : ℕ × (Header Pt × LibsignalMsgPublicPart) => atomicShortB ia.2.2)
      (slotSaltRed C protoSignalCodec ℓ encT idOf N k B) := by
  unfold slotSaltRed AEADScheme.OTEncADsOk
  have hQu : ∀ u, ¬(AEADScheme.otEncBad (M := Plain ℓ) (C := LCt)
      (fun ia : ℕ × (Header Pt × LibsignalMsgPublicPart) => atomicShortB ia.2.2) (.inl u) = true) :=
    fun u => by simp [AEADScheme.otEncBad]
  rw [← Nat.zero_add 0]
  refine isQueryBoundP_bind (FSAEAD.Thm5.isQueryBoundP_liftProb hQu _) fun K₀ _ => ?_
  rw [← Nat.zero_add 0]
  refine isQueryBoundP_bind (FSAEAD.Thm5.isQueryBoundP_liftProb hQu _) fun ks _ => ?_
  exact (isQueryBoundP_map_iff _ _ _).mpr
    (FSAEAD.Thm5.slotRedImpl_isQueryBoundP _ _ k hQu B _ hB)

theorem chainPRGTermWith_inst_eq
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (qR j : ℕ)
    (hℓ : ℓ < 10 ^ 6) (hj : j ≤ 2 * (qR + maxForwardJumps + 1))
    (hinj : Function.Injective encT) (A : FsAdv Pt ℓ)
    (hA : FSAEAD.MakesAtMostQueries A qR)
    (hshort : FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) A) :
    chainPRGTermCosted C qR (fsCostedRedsInst C codec ℓ encT idOf qR) A j =
      chainPRGTerm C protoSignalCodec ℓ encT idOf A j := by
  rw [chainPRGTermWith_inst_eq_clamped C codec ℓ encT idOf qR j hℓ hj hinj A hA]
  unfold chainPRGTerm
  exact congrArg (lChainPRG C.F (j / 2)).prgAdvantage
    (funext fun mt => cumulativeChainPrgReduction_clamped_eq C ℓ encT idOf j A hshort mt)

alias chainPRGTermCosted_inst_eq := chainPRGTermWith_inst_eq

theorem saltPRFTermWith_inst_eq
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (qR j : ℕ)
    (hℓ : ℓ < 10 ^ 6) (hj : j ≤ 2 * (qR + maxForwardJumps + 1))
    (hinj : Function.Injective encT) (A : FsAdv Pt ℓ)
    (hA : FSAEAD.MakesAtMostQueries A qR)
    (hshort : FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) A) :
    saltPRFTermCosted C qR (fsCostedRedsInst C codec ℓ encT idOf qR) A j =
      saltPRFTerm C protoSignalCodec ℓ encT idOf qR A j := by
  rw [saltPRFTermWith_inst_eq_clamped C codec ℓ encT idOf qR j hℓ hj hinj A hA]
  unfold saltPRFTerm
  dsimp only
  have hM_ok := multiSlotAdv_otEncADsOk C ℓ encT idOf qR (FSAEAD.Thm5.isLookaheadHop j) A hshort
  rw [multiSlotAdv_clamped_eq C ℓ encT idOf qR (FSAEAD.Thm5.isLookaheadHop j) A hshort,
    slotSaltRed_clamped_eq C ℓ encT idOf _ (j / 2) _ hM_ok,
    lSaltRed_clamped_eq C ℓ encT idOf _ (slotSaltRed_otEncADsOk C ℓ encT idOf _ (j / 2) _ hM_ok)]

alias saltPRFTermCosted_inst_eq := saltPRFTermWith_inst_eq

theorem wireOtccaTermWith_inst_eq
    (C : Crypto) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (qR qd j : ℕ)
    (hℓ : ℓ < 10 ^ 6) (hj : j ≤ 2 * (qR + maxForwardJumps + 1))
    (hinj : Function.Injective encT) (A : FsAdv Pt ℓ)
    (hA : FSAEAD.MakesAtMostQueries A qR)
    (hshort : FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) A) :
    wireOtccaTermCosted C protoSignalCodec ℓ qR
        (fsCostedRedsInst C protoSignalCodec ℓ encT idOf qR) A j =
      wireOtccaTerm C protoSignalCodec ℓ encT idOf qR qd A j := by
  unfold wireOtccaTermCosted wireOtccaTerm
  dsimp only
  rw [wireOtccaAdvantage_congr (lWire C protoSignalCodec ℓ)
    (wireRedComposed_inst_coinSimEquiv C protoSignalCodec ℓ encT idOf qR j hℓ hj hinj A hA)]
  have hM_ok := multiSlotAdv_otEncADsOk C ℓ encT idOf qR (FSAEAD.Thm5.isLookaheadHop j) A hshort
  rw [multiSlotAdv_clamped_eq C ℓ encT idOf qR (FSAEAD.Thm5.isLookaheadHop j) A hshort,
    slotWireRed_clamped_eq C ℓ encT idOf (j / 2) _ hM_ok]
  rfl

alias wireOtccaTermCosted_inst_eq := wireOtccaTermWith_inst_eq

/-- Equates `fsAeadSlotSumBound` on `fsCostedRedsInst` with `deliverForgeFSCompBound` under `EncMsgsOk atomicShortB`. -/
theorem deliverForgeFSCompBoundWith_inst_eq
    (C : Crypto) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (qR : ℕ)
    (hℓ : ℓ < 10 ^ 6) (hinj : Function.Injective encT) (A : FsAdv Pt ℓ)
    (hA : FSAEAD.MakesAtMostQueries A qR)
    (hshort : FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) A) :
    CryptoVerification.E2E.fsAeadSlotSumBound C qR
        (fsCostedRedsInst C protoSignalCodec ℓ encT idOf qR) A =
      CryptoGames.LibsignalSM.Proofs.Refinement.deliverForgeFSCompBound C protoSignalCodec ℓ encT
        idOf qR A := by
  unfold CryptoVerification.E2E.fsAeadSlotSumBound
    CryptoGames.LibsignalSM.Proofs.Refinement.deliverForgeFSCompBound
  refine congrArg (2 * ·) (Finset.sum_congr rfl fun k hk => ?_)
  have hj := hopIdx_le qR k (Finset.mem_range.mp hk)
  rw [chainPRGTermWith_inst_eq C protoSignalCodec ℓ encT idOf qR _ hℓ hj hinj A hA hshort,
    saltPRFTermWith_inst_eq C protoSignalCodec ℓ encT idOf qR _ hℓ hj hinj A hA hshort,
    wireOtccaTermWith_inst_eq C ℓ encT idOf qR qR _ hℓ hj hinj A hA hshort]

theorem fsPrgMixWith_inst_eq {α : Type}
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (oa : ProbComp α) (idOf : α → Party → IdentityKey)
    (qR j : ℕ) (hℓ : ℓ < 10 ^ 6) (hj : j ≤ 2 * (qR + maxForwardJumps + 1))
    (hinj : Function.Injective encT)
    (A : α → FsAdv Pt ℓ) (hA : ∀ o, FSAEAD.MakesAtMostQueries (A o) qR)
    (hshort : ∀ o,
      FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) (A o)) :
    CryptoVerification.E2E.fsChainPrgMixtureTerm C oa qR
        (fun o => fsCostedRedsInst C codec ℓ encT (idOf o) qR) A j =
      CryptoVerification.E2E.Signed.FSMix.fsPrgMix C protoSignalCodec ℓ encT
        oa idOf 25000 A j := by
  rw [fsPrgMixWith_inst_eq_clamped C codec ℓ encT oa idOf qR j hℓ hj hinj A hA]
  unfold CryptoVerification.E2E.Signed.FSMix.fsPrgMix CryptoVerification.E2E.Signed.prgAvg
  exact congrArg (lChainPRG C.F (j / 2)).prgAdvantage (funext fun mt => bind_congr fun o =>
    cumulativeChainPrgReduction_clamped_eq C ℓ encT (idOf o) j (A o) (hshort o) mt)

theorem fsSWMixWith_inst_eq {α : Type}
    (C : Crypto) (ℓ : ℕ)
    (encT : Pt → PublicKey) (oa : ProbComp α) (idOf : α → Party → IdentityKey)
    (qR j : ℕ) (hℓ : ℓ < 10 ^ 6) (hj : j ≤ 2 * (qR + maxForwardJumps + 1))
    (hinj : Function.Injective encT)
    (A : α → FsAdv Pt ℓ) (hA : ∀ o, FSAEAD.MakesAtMostQueries (A o) qR)
    (hshort : ∀ o,
      FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) (A o)) :
    CryptoVerification.E2E.fsSaltWireMixtureTerm C protoSignalCodec ℓ oa qR
        (fun o => fsCostedRedsInst C protoSignalCodec ℓ encT (idOf o) qR) A j =
      CryptoVerification.E2E.Signed.FSMix.fsSWMix C protoSignalCodec ℓ encT
        oa idOf 25000 qR A j := by
  unfold CryptoVerification.E2E.fsSaltWireMixtureTerm
    CryptoVerification.E2E.Signed.FSMix.fsSWMix
    CryptoVerification.E2E.prefixPrfAvg CryptoVerification.E2E.Signed.prfAvg
    CryptoVerification.E2E.prefixWireAvg CryptoVerification.E2E.Signed.FSMix.wireAvg
  refine congrArg₂ (· + ·) (congrArg (2 * ·) ?_) ?_
  · refine prfAdvantage_congr (lSaltPRF32 C.F) ((CoinSimEquiv.refl _).bind fun o => ?_)
    refine (saltRedComposed_inst_coinSimEquiv C protoSignalCodec ℓ encT (idOf o) qR j
      hℓ hj hinj (A o) (hA o)).trans (CoinSimEquiv.of_eq ?_)
    have hM_ok := multiSlotAdv_otEncADsOk C ℓ encT (idOf o) qR
      (FSAEAD.Thm5.isLookaheadHop j) (A o) (hshort o)
    rw [multiSlotAdv_clamped_eq C ℓ encT (idOf o) qR (FSAEAD.Thm5.isLookaheadHop j) (A o)
        (hshort o),
      slotSaltRed_clamped_eq C ℓ encT (idOf o) _ (j / 2) _ hM_ok,
      lSaltRed_clamped_eq C ℓ encT (idOf o) _
        (slotSaltRed_otEncADsOk C ℓ encT (idOf o) _ (j / 2) _ hM_ok)]
    rfl
  · refine wireOtccaAdvantage_congr (lWire C protoSignalCodec ℓ)
      ((CoinSimEquiv.refl _).bind fun o => ?_)
    refine (wireRedComposed_inst_coinSimEquiv C protoSignalCodec ℓ encT (idOf o) qR j
      hℓ hj hinj (A o) (hA o)).trans (CoinSimEquiv.of_eq ?_)
    have hM_ok := multiSlotAdv_otEncADsOk C ℓ encT (idOf o) qR
      (FSAEAD.Thm5.isLookaheadHop j) (A o) (hshort o)
    rw [multiSlotAdv_clamped_eq C ℓ encT (idOf o) qR (FSAEAD.Thm5.isLookaheadHop j) (A o)
        (hshort o),
      slotWireRed_clamped_eq C ℓ encT (idOf o) (j / 2) _ hM_ok]
    rfl

theorem fsShortBoundMixWith_inst_eq {α : Type}
    (C : Crypto) (ℓ : ℕ)
    (encT : Pt → PublicKey) (oa : ProbComp α) (idOf : α → Party → IdentityKey)
    (qR qd : ℕ) (hℓ : ℓ < 10 ^ 6) (hinj : Function.Injective encT)
    (A : α → FsAdv Pt ℓ) (hA : ∀ o, FSAEAD.MakesAtMostQueries (A o) qR)
    (hshort : ∀ o,
      FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) (A o)) :
    CryptoVerification.E2E.fsAeadMixtureBound C protoSignalCodec ℓ oa
        (q := qR) (qd := qd)
        (fun o => fsCostedRedsInst C protoSignalCodec ℓ encT (idOf o) qR) A =
      CryptoVerification.E2E.Signed.FSMix.fsShortBoundMix C protoSignalCodec ℓ encT
        oa idOf 25000 qR qd A := by
  unfold CryptoVerification.E2E.fsAeadMixtureBound
    CryptoVerification.E2E.Signed.FSMix.fsShortBoundMix
  have hslot : fsSlotCount qR = FSAEAD.Thm5.slotCount 25000 qR := rfl
  rw [← hslot]
  refine congrArg (· + 4 * ((qd : ℝ≥0∞) * macForgeryProb C.F))
    (congrArg (2 * ·) (Finset.sum_congr rfl fun k hk => ?_))
  have hj := hopIdx_le qR k (Finset.mem_range.mp hk)
  rw [fsPrgMixWith_inst_eq C protoSignalCodec ℓ encT oa idOf qR _ hℓ hj hinj A hA hshort,
    fsSWMixWith_inst_eq C ℓ encT oa idOf qR _ hℓ hj hinj A hA hshort]

theorem cumulativeChainPrgReductionOut_clamped_eq
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (j : ℕ)
    (F : Bool →
      FSAEAD.Thm5.HState (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LCt → Bool)
    (A : FsAdv Pt ℓ)
    (hshort : FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) A)
    (mt : BitVec 256 × BitVec 256) :
    Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out.cumulativeChainPrgReductionOut
        (lIdeal C clampedProtoSignalCodec ℓ encT)
        (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps j F
        (pubToAD clampedProtoSignalCodec A) mt =
      Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out.cumulativeChainPrgReductionOut
        (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps j F
        (pubToAD protoSignalCodec A) mt := by
  have hA' := pubToAD_encADsOk ℓ A hshort
  rw [pubToAD_clamped_eq ℓ A]
  unfold Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out.cumulativeChainPrgReductionOut
    Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out.hRunOut
  rw [← CryptoGames.FSAEAD.Thm5.Costed.multiImplWith_zero_none
      (lIdeal C clampedProtoSignalCodec ℓ encT)
      (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
      (FSAEAD.Thm5.hp (j / 2) 0 (FSAEAD.Thm5.isLookaheadHop j)) (FSAEAD.Thm5.DG (lChainPRG C.F)) rfl,
    ← CryptoGames.FSAEAD.Thm5.Costed.multiImplWith_zero_none
      (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
      (FSAEAD.Thm5.hp (j / 2) 0 (FSAEAD.Thm5.isLookaheadHop j)) (FSAEAD.Thm5.DG (lChainPRG C.F)) rfl]
  refine bind_congr fun b => ?_
  rw [multiImplWith_clamped_run_eq C ℓ encT idOf _ 0 none none rfl
    (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) _ hA' _]

theorem multiSlotAdvAuth_clamped_eq
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (qR : ℕ) (la : Bool) (A : FsAdv Pt ℓ)
    (hshort : FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) A) :
    Computational.Proofs.ReductionDsl.FsAtomicSoundness.multiSlotAdvAuth
        C clampedProtoSignalCodec ℓ encT idOf qR la A =
      Computational.Proofs.ReductionDsl.FsAtomicSoundness.multiSlotAdvAuth
        C protoSignalCodec ℓ encT idOf qR la A := by
  have hA' := pubToAD_encADsOk ℓ A hshort
  unfold Computational.Proofs.ReductionDsl.FsAtomicSoundness.multiSlotAdvAuth
    Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out.multiSlotOtccaReductionOut
    Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out.multiRunOut
  rw [pubToAD_clamped_eq ℓ A]
  refine bind_congr fun b => ?_
  rw [multiImplWith_clamped_run_eq C ℓ encT idOf _ _
    (some (FSAEAD.Thm5.otOpsWith (lIdeal C clampedProtoSignalCodec ℓ encT)))
    (some (FSAEAD.Thm5.otOpsWith (lIdeal C protoSignalCodec ℓ encT))) rfl
    (fun _ _ h1 h2 i a msg ha => by
      cases h1; cases h2
      dsimp only [FSAEAD.Thm5.otOpsWith]
      rw [lIdeal_clamped_eq C ℓ encT (i, a) ha])
    (fun _ _ h1 h2 => by cases h1; cases h2; rfl) _ hA' _]

private lemma multiSlotAdvAuth_otEncADsOk
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (qR : ℕ) (la : Bool) (A : FsAdv Pt ℓ)
    (hshort : FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) A) :
    AEADScheme.OTEncADsOk
      (fun ia : ℕ × (Header Pt × LibsignalMsgPublicPart) => atomicShortB ia.2.2)
      (Computational.Proofs.ReductionDsl.FsAtomicSoundness.multiSlotAdvAuth
        C protoSignalCodec ℓ encT idOf qR la A) := by
  have hbase := multiSlotAdv_otEncADsOk C ℓ encT idOf qR la A hshort
  unfold AEADScheme.OTEncADsOk at hbase ⊢
  let P : OracleComp _ Bool :=
    Computational.Proofs.ReductionDsl.FsAtomicSoundness.multiSlotAdvAuth
      C protoSignalCodec ℓ encT idOf qR la A
  let Q : OracleComp _ Bool := multiSlotAdv C protoSignalCodec ℓ encT idOf qR la A
  have hmap : ((fun _ : Bool => ()) <$> P) = ((fun _ : Bool => ()) <$> Q) := by
    dsimp only [P, Q]
    unfold Computational.Proofs.ReductionDsl.FsAtomicSoundness.multiSlotAdvAuth multiSlotAdv
      Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out.multiSlotOtccaReductionOut
      FSAEAD.Thm5.multiSlotOtccaReduction
      Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out.multiRunOut
      FSAEAD.Thm5.multiRunWith
    simp only [map_bind, map_pure]
  have hm := (isQueryBoundP_map_iff Q (fun _ : Bool => ()) _).mpr hbase
  rw [← hmap] at hm
  exact (isQueryBoundP_map_iff P (fun _ : Bool => ()) _).mp hm

theorem chainPRGTermAuthWith_inst_eq
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (qR j : ℕ)
    (hℓ : ℓ < 10 ^ 6) (hj : j ≤ 2 * (qR + maxForwardJumps + 1))
    (hinj : Function.Injective encT) (A : FsAdv Pt ℓ)
    (hA : FSAEAD.MakesAtMostQueries A qR)
    (hshort : FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) A) :
    chainPRGTermAuthCosted C qR (fsCostedRedsInst C codec ℓ encT idOf qR) A j =
      chainPRGTermAuth C protoSignalCodec ℓ encT idOf A j := by
  rw [chainPRGTermAuthWith_inst_eq_clamped C codec ℓ encT idOf qR j hℓ hj hinj A hA]
  unfold chainPRGTermAuth
  exact congrArg (lChainPRG C.F (j / 2)).prgAdvantage
    (funext fun mt =>
      cumulativeChainPrgReductionOut_clamped_eq C ℓ encT idOf j _ A hshort mt)

alias chainPRGTermAuthCosted_inst_eq := chainPRGTermAuthWith_inst_eq

theorem saltPRFTermAuthWith_inst_eq
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (qR j : ℕ)
    (hℓ : ℓ < 10 ^ 6) (hj : j ≤ 2 * (qR + maxForwardJumps + 1))
    (hinj : Function.Injective encT) (A : FsAdv Pt ℓ)
    (hA : FSAEAD.MakesAtMostQueries A qR)
    (hshort : FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) A) :
    saltPRFTermAuthCosted C qR (fsCostedRedsInst C codec ℓ encT idOf qR) A j =
      saltPRFTermAuth C protoSignalCodec ℓ encT idOf qR A j := by
  rw [saltPRFTermAuthWith_inst_eq_clamped C codec ℓ encT idOf qR j hℓ hj hinj A hA]
  unfold saltPRFTermAuth
  dsimp only
  have hM_ok := multiSlotAdvAuth_otEncADsOk C ℓ encT idOf qR (FSAEAD.Thm5.isLookaheadHop j) A hshort
  rw [multiSlotAdvAuth_clamped_eq C ℓ encT idOf qR (FSAEAD.Thm5.isLookaheadHop j) A hshort,
    slotSaltRed_clamped_eq C ℓ encT idOf _ (j / 2) _ hM_ok,
    lSaltRed_clamped_eq C ℓ encT idOf _ (slotSaltRed_otEncADsOk C ℓ encT idOf _ (j / 2) _ hM_ok)]

alias saltPRFTermAuthCosted_inst_eq := saltPRFTermAuthWith_inst_eq

theorem wireOtccaTermAuthWith_inst_eq
    (C : Crypto) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (qR qd j : ℕ)
    (hℓ : ℓ < 10 ^ 6) (hj : j ≤ 2 * (qR + maxForwardJumps + 1))
    (hinj : Function.Injective encT) (A : FsAdv Pt ℓ)
    (hA : FSAEAD.MakesAtMostQueries A qR)
    (hshort : FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) A) :
    wireOtccaTermAuthCosted C protoSignalCodec ℓ qR
        (fsCostedRedsInst C protoSignalCodec ℓ encT idOf qR) A j =
      wireOtccaTermAuth C protoSignalCodec ℓ encT idOf qR qd A j := by
  unfold wireOtccaTermAuthCosted wireOtccaTermAuth
  dsimp only
  rw [wireOtccaAdvantage_congr (lWire C protoSignalCodec ℓ)
    (wireRedAuthComposed_inst_coinSimEquiv C protoSignalCodec ℓ encT idOf qR j hℓ hj hinj A hA)]
  have hM_ok := multiSlotAdvAuth_otEncADsOk C ℓ encT idOf qR (FSAEAD.Thm5.isLookaheadHop j) A hshort
  rw [multiSlotAdvAuth_clamped_eq C ℓ encT idOf qR (FSAEAD.Thm5.isLookaheadHop j) A hshort,
    slotWireRed_clamped_eq C ℓ encT idOf (j / 2) _ hM_ok]
  rfl

alias wireOtccaTermAuthCosted_inst_eq := wireOtccaTermAuthWith_inst_eq

theorem fsAuthCompBoundWith_inst_eq
    (C : Crypto) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (qR qd : ℕ)
    (hℓ : ℓ < 10 ^ 6) (hinj : Function.Injective encT) (A : Bool → Bool → FsAdv Pt ℓ)
    (hA : ∀ stage la, FSAEAD.MakesAtMostQueries (A stage la) qR)
    (hshort : ∀ stage la,
      FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1)
        (A stage la)) :
    fsAuthCompBoundWith C protoSignalCodec ℓ qR
        (fsCostedRedsInst C protoSignalCodec ℓ encT idOf qR) A =
      fsAuthCompBound C protoSignalCodec ℓ encT idOf qR qd A := by
  unfold fsAuthCompBoundWith fsAuthCompBound
  refine congrArg (2 * ·) (Finset.sum_congr rfl fun k hk => ?_)
  have hj := hopIdx_le qR k (Finset.mem_range.mp hk)
  dsimp only
  rw [chainPRGTermAuthWith_inst_eq C protoSignalCodec ℓ encT idOf qR _ hℓ hj hinj
      _ (hA false _) (hshort false _),
    saltPRFTermAuthWith_inst_eq C protoSignalCodec ℓ encT idOf qR _ hℓ hj hinj
      _ (hA false _) (hshort false _),
    wireOtccaTermAuthWith_inst_eq C ℓ encT idOf qR qd _ hℓ hj hinj
      _ (hA true _) (hshort true _)]

theorem fsAeadAuthSlotSumBound_inst_eq
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (qR qd : ℕ)
    (hℓ : ℓ < 10 ^ 6) (hinj : Function.Injective encT) (A : Bool → Bool → FsAdv Pt ℓ)
    (hA : ∀ stage la, FSAEAD.MakesAtMostQueries (A stage la) qR)
    (hshort : ∀ stage la,
      FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1)
        (A stage la)) :
    CryptoVerification.E2E.fsAeadAuthSlotSumBound C qR
        (fsCostedRedsInst C protoSignalCodec ℓ encT idOf qR) A =
      fsAuthCompBound C protoSignalCodec ℓ encT idOf qR qd A := by
  unfold CryptoVerification.E2E.fsAeadAuthSlotSumBound fsAuthCompBound
  refine congrArg (2 * ·) (Finset.sum_congr rfl fun k hk => ?_)
  have hj := hopIdx_le qR k (Finset.mem_range.mp hk)
  dsimp only
  rw [chainPRGTermAuthWith_inst_eq C protoSignalCodec ℓ encT idOf qR _ hℓ hj hinj
      _ (hA false _) (hshort false _),
    saltPRFTermAuthWith_inst_eq C protoSignalCodec ℓ encT idOf qR _ hℓ hj hinj
      _ (hA false _) (hshort false _),
    wireOtccaTermAuthWith_inst_eq C ℓ encT idOf qR qd _ hℓ hj hinj
      _ (hA true _) (hshort true _),
    add_assoc]

theorem fsAuthPrgMixWith_inst_eq {α : Type}
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (oa : ProbComp α) (idOf : α → Party → IdentityKey)
    (qR j : ℕ) (hℓ : ℓ < 10 ^ 6) (hj : j ≤ 2 * (qR + maxForwardJumps + 1))
    (hinj : Function.Injective encT)
    (A : α → FsAdv Pt ℓ) (hA : ∀ o, FSAEAD.MakesAtMostQueries (A o) qR)
    (hshort : ∀ o,
      FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) (A o)) :
    (lChainPRG C.F (j / 2)).prgAdvantage
        (CryptoVerification.E2E.prefixPrgAvg oa fun o =>
          fun mt =>
            evalTwoStage1 ((fsCostedRedsInst C codec ℓ encT (idOf o) qR).prgRedAuth j) qR false
              (fun _ => pubToADCosted (fsCostedRedsInst C codec ℓ encT (idOf o) qR) (A o)) mt) =
      fsAuthPrgMix C protoSignalCodec ℓ encT oa idOf 25000 A j := by
  rw [fsAuthPrgMixWith_inst_eq_clamped C codec ℓ encT oa idOf qR j hℓ hj hinj A hA]
  unfold fsAuthPrgMix CryptoVerification.E2E.Signed.prgAvg
  exact congrArg (lChainPRG C.F (j / 2)).prgAdvantage (funext fun mt => bind_congr fun o =>
    cumulativeChainPrgReductionOut_clamped_eq C ℓ encT (idOf o) j _ (A o) (hshort o) mt)

theorem fsAuthSWMixWith_inst_eq {α : Type}
    (C : Crypto) (ℓ : ℕ)
    (encT : Pt → PublicKey) (oa : ProbComp α) (idOf : α → Party → IdentityKey)
    (qR j : ℕ) (hℓ : ℓ < 10 ^ 6) (hj : j ≤ 2 * (qR + maxForwardJumps + 1))
    (hinj : Function.Injective encT)
    (Afalse Atrue : α → FsAdv Pt ℓ)
    (hAf : ∀ o, FSAEAD.MakesAtMostQueries (Afalse o) qR)
    (hAt : ∀ o, FSAEAD.MakesAtMostQueries (Atrue o) qR)
    (hsf : ∀ o,
      FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) (Afalse o))
    (hst : ∀ o,
      FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) (Atrue o)) :
    2 * (lSaltPRF32 C.F).prfAdvantage
        (CryptoVerification.E2E.prefixPrfAvg oa fun o =>
          (fsCostedRedsInst C protoSignalCodec ℓ encT (idOf o) qR).lSaltRed.eval
            (fun _ =>
              ((fsCostedRedsInst C protoSignalCodec ℓ encT (idOf o) qR).slotSaltRed j).eval
                (fun _ =>
                  multiSlotAdvAuthCosted qR
                    (fsCostedRedsInst C protoSignalCodec ℓ encT (idOf o) qR)
                    (FSAEAD.Thm5.isLookaheadHop j) (Afalse o)) ()) ()) +
      (lWire C protoSignalCodec ℓ).wireOtccaAdvantage
        (CryptoVerification.E2E.prefixWireAvg oa fun o =>
          (fsCostedRedsInst C protoSignalCodec ℓ encT (idOf o) qR).lWireRed.eval
            (fun _ =>
              ((fsCostedRedsInst C protoSignalCodec ℓ encT (idOf o) qR).slotWireRed j).eval
                (fun _ =>
                  multiSlotAdvAuthCosted qR
                    (fsCostedRedsInst C protoSignalCodec ℓ encT (idOf o) qR)
                    (FSAEAD.Thm5.isLookaheadHop j) (Atrue o)) ()) ()) =
      fsAuthSWMix C protoSignalCodec ℓ encT oa idOf 25000 qR Afalse Atrue j := by
  unfold fsAuthSWMix CryptoVerification.E2E.prefixPrfAvg CryptoVerification.E2E.Signed.prfAvg
    CryptoVerification.E2E.prefixWireAvg CryptoVerification.E2E.Signed.FSMix.wireAvg
  refine congrArg₂ (· + ·) (congrArg (2 * ·) ?_) ?_
  · refine prfAdvantage_congr (lSaltPRF32 C.F) ((CoinSimEquiv.refl _).bind fun o => ?_)
    refine (saltRedAuthComposed_inst_coinSimEquiv C protoSignalCodec ℓ encT (idOf o) qR j
      hℓ hj hinj (Afalse o) (hAf o)).trans (CoinSimEquiv.of_eq ?_)
    have hM_ok := multiSlotAdvAuth_otEncADsOk C ℓ encT (idOf o) qR
      (FSAEAD.Thm5.isLookaheadHop j) (Afalse o) (hsf o)
    rw [multiSlotAdvAuth_clamped_eq C ℓ encT (idOf o) qR (FSAEAD.Thm5.isLookaheadHop j) (Afalse o)
        (hsf o),
      slotSaltRed_clamped_eq C ℓ encT (idOf o) _ (j / 2) _ hM_ok,
      lSaltRed_clamped_eq C ℓ encT (idOf o) _
        (slotSaltRed_otEncADsOk C ℓ encT (idOf o) _ (j / 2) _ hM_ok)]
    rfl
  · refine wireOtccaAdvantage_congr (lWire C protoSignalCodec ℓ)
      ((CoinSimEquiv.refl _).bind fun o => ?_)
    refine (wireRedAuthComposed_inst_coinSimEquiv C protoSignalCodec ℓ encT (idOf o) qR j
      hℓ hj hinj (Atrue o) (hAt o)).trans (CoinSimEquiv.of_eq ?_)
    have hM_ok := multiSlotAdvAuth_otEncADsOk C ℓ encT (idOf o) qR
      (FSAEAD.Thm5.isLookaheadHop j) (Atrue o) (hst o)
    rw [multiSlotAdvAuth_clamped_eq C ℓ encT (idOf o) qR (FSAEAD.Thm5.isLookaheadHop j) (Atrue o)
        (hst o),
      slotWireRed_clamped_eq C ℓ encT (idOf o) (j / 2) _ hM_ok]
    rfl

theorem fsAeadAuthMixtureCompBound_inst_eq {α : Type}
    (C : Crypto) (ℓ : ℕ)
    (encT : Pt → PublicKey) (oa : ProbComp α) (idOf : α → Party → IdentityKey)
    (qR : ℕ) (hℓ : ℓ < 10 ^ 6) (hinj : Function.Injective encT)
    (A : Bool → Bool → α → FsAdv Pt ℓ)
    (hA : ∀ stage la o, FSAEAD.MakesAtMostQueries (A stage la o) qR)
    (hshort : ∀ stage la o,
      FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1)
        (A stage la o)) :
    CryptoVerification.E2E.fsAeadAuthMixtureCompBound C protoSignalCodec ℓ oa qR
        (fun o => fsCostedRedsInst C protoSignalCodec ℓ encT (idOf o) qR) A =
      fsAuthCompBoundMix C protoSignalCodec ℓ encT oa idOf 25000 qR A := by
  unfold CryptoVerification.E2E.fsAeadAuthMixtureCompBound fsAuthCompBoundMix
  have hslot : fsSlotCount qR = FSAEAD.Thm5.slotCount 25000 qR := rfl
  rw [← hslot]
  refine congrArg (2 * ·) (Finset.sum_congr rfl fun k hk => ?_)
  have hj := hopIdx_le qR k (Finset.mem_range.mp hk)
  dsimp only
  rw [add_assoc,
    fsAuthPrgMixWith_inst_eq C protoSignalCodec ℓ encT oa idOf qR _ hℓ hj hinj
      _ (hA false _) (hshort false _),
    fsAuthSWMixWith_inst_eq C ℓ encT oa idOf qR _ hℓ hj hinj
      _ _ (hA false _) (hA true _) (hshort false _) (hshort true _)]

end FsCosted

end CryptoVerification.LibsignalSession
