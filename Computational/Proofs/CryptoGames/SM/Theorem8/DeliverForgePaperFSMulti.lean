/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFS -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperShiftedFS3 -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperBucketPRNG -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperBucketFS -- proof-setup: allow-public-import
public import Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2 -- proof-setup: allow-public-import
public import Computational.Proofs.HeadlineV1.DeliverForgePaperChallSim -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.Fig8Atomic -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SessionAuthLazy -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SessionAuthFS -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SessionAuthBridge -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.TopAssembly -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFSMultiBase -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFSMultiShifted -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFSMultiUnshifted -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFSMultiBucketInactive -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFSMultiBucket -- proof-setup: allow-public-import
import Computational.Proofs.E2E.SessionAuthHooksPot
import Computational.Proofs.E2E.SessionAuthMultiPot
import Computational.Proofs.E2E.SessionAuthMultiReal
import Computational.Proofs.E2E.SessionAuthMultiEnd
import Computational.Proofs.GameHop.Rnd

/-!
# Stage-2 Multi-Session Paper `DeliverForge` Hop-3 (`FSMultiSpec`) Bridges (`[B7]` × `[B8]`)

Couples the post-PRNG local games of the Stage-2 `DeliverForgePaper` families
(`localAuthDFShiftedDir2Paper`, `localAuthDFShiftedPaper`, `AuthL11.localAuthDFPaper`,
`localAuthDFPaperBucket`, and `localAuthDFBucket`) to the two-mode (`la = false` + `la = true`)
real multi-session `FSMultiSpec` experiments (`multiSessRealWinProb`), and establishes
per-session query bounds, `TwoModeMultiSessBounds`, and ideal-cutoff zero-output
(`multiSessEndWinProb = 0`) invariants.-/

set_option autoImplicit false

namespace Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFSMulti

public section

open scoped ENNReal MeasureTheory
open OracleSpec OracleComp
open _root_.CryptoGames (Party CKAScheme PRFPRNG FSAEADScheme AEADScheme)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.CKA (DHFun dhScheme)
open _root_.CryptoGames.Ratchet (rootPRNG)
open _root_.CryptoGames.SM (authLosingConditionsAvoided)
open _root_.CryptoGames.SM.Construction (Header Mode healEpoch sampleT
  inStage2BucketGen redFSAuthDFPaperMulti redFSAuthDFPaperMultiBucket
  redFSAuthDFPaperMultiBucketMode)
open _root_.CryptoGames.SM.Construction.DeliverForge (AdversaryDF SchemeAdversaryDF
  MakesAtMostQueriesDF authOutBucket authOutBucketPaper bucketAuthCfg engRunDFPaperBucket
  hooksLocalBucket initLocalBucket
  localAuthDFPaperBucket localAuthDFPaperBucketMain localAuthDFPaperBucketForgedHdr
  localAuthDFPaperBucketMode localAuthDFShiftedDir2Paper localAuthDFShiftedPaper)
open _root_.CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey SignalMessageProtoCodec
  maxForwardJumps)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart dummyKey lFS
  lIdeal lAeadR lChainPRG LibsignalCiphertextWithSalt32)
open _root_.CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C)
open _root_.CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open _root_.CryptoVerification.LibsignalSession.HeadlineV1 (SendMsgsOkDF GuardedSMDFShort)
open Computational.Proofs.ReductionDsl.Fig8Atomic (atomicShortPubB)
open Computational.Proofs.ReductionDsl.FsAtomicMacros (atomicShortB)
open _root_.CryptoVerification.LibsignalSession (FsAdv fsAuthCompBoundWith fsCostedRedsInst macForgeryTerm)
open _root_.CryptoVerification.E2E.Signed.SessionRouter (lazyInit sessLift multiSessSpec sessOffRange
  onSess onAnySess)
open _root_.CryptoVerification.E2E.Signed.SessionFS (fsInit fsImpl fsSpec)
open _root_.CryptoVerification.E2E.Signed.SessionQueries (isQueryBoundP_bind_zero_left)
open _root_.CryptoVerification.E2E.Signed.SessionWireQueries (GuardedMultiInjectShort
  multiInjectLong fsOutsideClass)
open Computational.Proofs.E2E.SessionAuthBridge (authHopCutoff MultiSessFsAdv MultiSessPubFsAdv
  multiSessPubToAD TwoModeMultiSessBounds RouterAdvCompat
  sessionHybrid_two_modes_le_sum_fsAuthCompBoundWith)
open Computational.Proofs.SessionCostedFig8.TopAssembly (multiSessRealWinProb multiSessEndWinProb
  multiSess_two_modes_le_sum_fsAuthCompBoundWith_min sum_range_mul_mod_div)
open Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2 (
  redFSAuthDFShiftedPaperMultiGen redFSAuthDFShiftedPaperMulti redFSAuthDFShiftedDir2PaperMulti)

theorem two_mul_evalDist_unif_bool_bind (f : Bool → ProbComp Bool) :
    2 * 𝒟[($ᵗ Bool : ProbComp Bool) >>= f] {true} =
      𝒟[f true] {true} + 𝒟[f false] {true} := by
  have hfg : (($ᵗ Bool : ProbComp Bool) >>= f) =
      (do let sel ← ($ᵗ Bool : ProbComp Bool); if sel then f true else f false) := by
    congr 1; ext b; cases b <;> rfl
  rw [hfg, Computational.Proofs.GameHop.Rnd.evalDist_uniformBool_ite_true]
  exact ENNReal.mul_div_cancel (by norm_num) (by norm_num)

theorem simulateQ_lift_sampleT_run_eq {κ ι σ : Type}
    {G : OracleSpec.{0, 0} κ} {H : OracleSpec.{0, 0} ι}
    (impl : QueryImpl (unifSpec + G) (StateT σ (OracleComp (unifSpec + H))))
    (hInl : ∀ n, impl (.inl n) = StateT.lift (query (spec := unifSpec + H) (.inl n)))
    {α : Type} [SampleableType α] (s : σ) :
    (simulateQ impl (sampleT (tspec := G) α)).run s =
      (sampleT (tspec := H) α >>= fun a => pure (a, s)) := by
  unfold sampleT
  induction ($ᵗ α : ProbComp α) using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind n k ih =>
    change (simulateQ impl
        ((query (spec := unifSpec + G) (.inl n)) >>= fun u =>
          liftComp (k u) (unifSpec + G))).run s =
      (((query (spec := unifSpec + H) (.inl n)) >>= fun u =>
          liftComp (k u) (unifSpec + H)) >>= fun a => pure (a, s))
    rw [simulateQ_bind, StateT.run_bind, simulateQ_HasQuery_query, hInl n]
    simp only [StateT.run_lift, bind_assoc, pure_bind]
    exact congrArg (query (spec := unifSpec + H) (.inl n) >>= ·) (funext fun u => ih u s)

theorem simulateQ_sessLift_sampleT_run_eq {ι σ : Type}
    {G : OracleSpec.{0, 0} ι}
    (sub : QueryImpl G (StateT σ ProbComp))
    {α : Type} [SampleableType α] (st : ℕ → σ) :
    (simulateQ (sessLift sub) (sampleT (tspec := multiSessSpec G) α)).run st =
      (($ᵗ α : ProbComp α) >>= fun a => pure (a, st)) := by
  unfold sampleT
  induction ($ᵗ α : ProbComp α) using OracleComp.inductionOn generalizing st with
  | pure a => simp
  | query_bind n k ih =>
    change (simulateQ (sessLift sub)
        ((query (spec := unifSpec + multiSessSpec G) (.inl n)) >>= fun u =>
          liftComp (k u) (unifSpec + multiSessSpec G))).run st =
      ((query (spec := unifSpec) n >>= k) >>= fun a => pure (a, st))
    rw [simulateQ_bind, StateT.run_bind, simulateQ_HasQuery_query]
    simp only [sessLift, bind_assoc]
    exact congrArg (query (spec := unifSpec) n >>= ·) (funext fun u => ih u st)

private theorem stateT_run'_eq_map_run {σ : Type} {m : Type → Type} [Functor m] {α : Type}
    (x : StateT σ m α) (s : σ) : x.run' s = Prod.fst <$> x.run s := rfl

theorem multiSessPubToAD_sampleT_bind {Pt : Type} (codec : SignalMessageProtoCodec) {ℓ : ℕ}
    {α : Type} [SampleableType α]
    (RBr : α → MultiSessPubFsAdv Pt ℓ) :
    multiSessPubToAD codec (sampleT α >>= RBr) =
      (sampleT α >>= fun a => multiSessPubToAD codec (RBr a)) := by
  unfold multiSessPubToAD
  dsimp only
  rw [stateT_run'_eq_map_run, simulateQ_bind, StateT.run_bind,
    simulateQ_lift_sampleT_run_eq _ (fun _ => rfl)]
  simp only [stateT_run'_eq_map_run, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]

theorem sampleT_bind_isQueryBoundP {ι : Type} {G : OracleSpec.{0, 0} ι}
    {α β : Type} [SampleableType α]
    (Pbad : (unifSpec + G).Domain → Prop) [DecidablePred Pbad]
    (hInl : ∀ n, ¬ Pbad (.inl n))
    {k : ℕ} (f : α → OracleComp (unifSpec + G) β)
    (hf : ∀ a, (f a).IsQueryBoundP Pbad k) :
    (sampleT (tspec := G) α >>= f).IsQueryBoundP Pbad k := by
  refine isQueryBoundP_bind_zero_left ?_ hf
  unfold sampleT
  exact IsQueryBoundP.liftComp_subSpec (p := fun _ => False)
    (fun n => ⟨False.elim, fun h => hInl n h⟩)
    (Computational.Proofs.GameHop.StateSim.isQueryBoundP_false ($ᵗ α : ProbComp α) 0)

theorem sampleT_guardedMultiInjectShort_bind {Pt : Type} {ℓ : ℕ}
    {α : Type} [SampleableType α]
    (f : α → MultiSessFsAdv Pt ℓ)
    (hf : ∀ a, GuardedMultiInjectShort (f a)) :
    GuardedMultiInjectShort (sampleT α >>= f) := by
  unfold GuardedMultiInjectShort sampleT
  exact (CryptoGames.GuardedSafe.GuardedSafePost.liftComp_unif
    (tspec := multiSessSpec (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32))
    (fun _ => False.elim) ($ᵗ α : ProbComp α)).bind fun a _ => hf a

theorem twoModeMultiSessBounds_sampleT_bool
    {Pt : Type} [DecidableEq Pt] {ℓ : ℕ} {α : Type} {B qR M qd : ℕ}
    (Adv : Bool → Bool → α → MultiSessFsAdv Pt ℓ)
    (hTrue : TwoModeMultiSessBounds B qR M qd (Adv true))
    (hFalse : TwoModeMultiSessBounds B qR M qd (Adv false))
    (honeAD : ∀ la j o, ∃ k₀ : ℕ, ∀ gMain,
      (Adv gMain la o).IsQueryBoundP
        (fun t => onSess (fsOutsideClass
          (fun ap : Header Pt × LibsignalMsgPublicPart => ap.1.1) k₀) j t = true) 0) :
    TwoModeMultiSessBounds B qR M qd
      (fun la o => sampleT Bool >>= fun gMain => Adv gMain la o) where
  offRange la o := sampleT_bind_isQueryBoundP _ (fun _ => by simp [sessOffRange]) _
    fun gMain => by cases gMain; exact hFalse.offRange la o; exact hTrue.offRange la o
  decBound la o := sampleT_bind_isQueryBoundP _ (fun _ => by simp [onAnySess]) _
    fun gMain => by cases gMain; exact hFalse.decBound la o; exact hTrue.decBound la o
  shortAD la o := sampleT_bind_isQueryBoundP _ (fun _ => by simp [onAnySess]) _
    fun gMain => by cases gMain; exact hFalse.shortAD la o; exact hTrue.shortAD la o
  guardedShort la o := sampleT_guardedMultiInjectShort_bind _
    fun gMain => by cases gMain; exact hFalse.guardedShort la o; exact hTrue.guardedShort la o
  oneADClass la j o := by
    obtain ⟨k₀, hk₀⟩ := honeAD la j o
    exact ⟨k₀, sampleT_bind_isQueryBoundP _ (fun _ => by simp [onSess]) _ (hk₀ ·)⟩

theorem multiSessRealWinProb_add_eq_two_mul_sampleT_bool
    {Pt : Type} [DecidableEq Pt] (C : Crypto) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (Adv : Bool → Bool → MultiSessFsAdv Pt ℓ) (la : Bool) :
    multiSessRealWinProb C ℓ encT idOf (Adv true) la +
      multiSessRealWinProb C ℓ encT idOf (Adv false) la =
    2 * multiSessRealWinProb C ℓ encT idOf
      (fun la' => sampleT Bool >>= fun gMain => Adv gMain la') la := by
  unfold multiSessRealWinProb
  rw [simulateQ_bind, StateT.run_bind, simulateQ_sessLift_sampleT_run_eq]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  symm
  exact two_mul_evalDist_unif_bool_bind (fun gMain =>
    (simulateQ (sessLift (lazyInit fsInit (fsImpl
      (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps
      (CryptoGames.FSAEAD.Thm5.hp 0 0 la))))
      (Adv gMain la)).run (fun _ => none) >>= fun x => pure x.1)

theorem multiSessEndWinProb_sampleT_bool_eq_zero
    {Pt : Type} [DecidableEq Pt] (C : Crypto) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (qR : ℕ)
    (Adv : Bool → Bool → MultiSessFsAdv Pt ℓ) (la : Bool)
    (hTrue : multiSessEndWinProb C ℓ encT idOf qR (Adv true) la = 0)
    (hFalse : multiSessEndWinProb C ℓ encT idOf qR (Adv false) la = 0) :
    multiSessEndWinProb C ℓ encT idOf qR
      (fun la' => sampleT Bool >>= fun gMain => Adv gMain la') la = 0 := by
  have h2 : 2 * multiSessEndWinProb C ℓ encT idOf qR
      (fun la' => sampleT Bool >>= fun gMain => Adv gMain la') la = 0 := by
    unfold multiSessEndWinProb at *
    dsimp only at *
    rw [simulateQ_bind, StateT.run_bind, simulateQ_sessLift_sampleT_run_eq]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind] at *
    rw [two_mul_evalDist_unif_bool_bind, hTrue, hFalse, add_zero]
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

private theorem multiSess_two_modes_le_sum_fsAuthCompBoundWith_two_mul_q
    {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (M q : ℕ) (hq32 : 2 * q + 25002 < 2 ^ 32)
    (Adv : Bool → MultiSessFsAdv Pt ℓ)
    (A : Bool → Bool → ℕ → FsAdv Pt ℓ)
    (hℓ : ℓ < 10 ^ 6) (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (hbds : TwoModeMultiSessBounds maxForwardJumps (2 * q) M q
      (fun la (_ : Unit) => Adv la))
    (hcompat : RouterAdvCompat C protoSignalCodec ℓ encT
      (pure ()) (fun _ => idOf) maxForwardJumps (2 * q) M
      (fun la (_ : Unit) => Adv la) (fun stage la j _ => A stage la j))
    (hA : ∀ j < M, ∀ stage la, _root_.CryptoGames.FSAEAD.MakesAtMostQueries (A stage la j) (2 * q))
    (hshort : ∀ j < M, ∀ stage la,
      _root_.CryptoGames.FSAEAD.EncMsgsOk
        (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) (A stage la j))
    (hendFalse : multiSessEndWinProb C ℓ encT idOf (2 * q) Adv false = 0)
    (hendTrue : multiSessEndWinProb C ℓ encT idOf (2 * q) Adv true = 0) :
    2 * (multiSessRealWinProb C ℓ encT idOf Adv false +
          multiSessRealWinProb C ℓ encT idOf Adv true) ≤
      (∑ j ∈ Finset.range M,
        fsAuthCompBoundWith C protoSignalCodec ℓ (2 * q)
          (fsCostedRedsInst C protoSignalCodec ℓ encT idOf (2 * q))
          (fun stage la => A stage la j)) +
      4 * macForgeryTerm C q := by
  have hcut : 2 * q + (maxForwardJumps + 1) ≤ 2 ^ 32 := by
    change 2 * q + (25000 + 1) ≤ 2 ^ 32
    omega
  exact sessionHybrid_two_modes_le_sum_fsAuthCompBoundWith C ℓ encT idOf
    (2 * q) M q Adv A hℓ hinj hdum hcut hbds hcompat hA hshort hendFalse hendTrue


section LibsignalBridges

variable (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (Dh : DHFun (BitVec 256) Pt)


/-- `B1` (`localAuthDFShiftedDir2Paper`) post-PRNG local game bounded by the two-mode
(`la = false` + `la = true`) `multiSessRealWinProb` of `redFSAuthDFShiftedDir2PaperMulti`. -/
theorem localAuthDFShiftedDir2Paper_le_multiSessRealWinProb
    (hD : ∀ k x, C.D k (C.E k x) = x)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (idOf : Party → IdentityKey) (lam : Pt) (hℓ : ℓ < 10 ^ 6)
    (q qep l t : ℕ) (ht2 : 2 ≤ t) (hl : l = t - 1)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq : MakesAtMostQueriesDF A q)
    (hsh : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    let Adv := fun la =>
      multiSessPubToAD protoSignalCodec
        (redFSAuthDFShiftedDir2PaperMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam qep l t la A)
    𝒟[localAuthDFShiftedDir2Paper (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam 0 qep l (some (l - 1)) t A] {true} ≤
      multiSessRealWinProb C ℓ encT idOf Adv false +
        multiSessRealWinProb C ℓ encT idOf Adv true :=
  Computational.Proofs.E2E.SessionAuthMultiReal.localAuthDFShiftedDir2Paper_le_multiSessRealWinProb ℓ Pt C Dh hD encPt encT hinj hdum idOf lam hℓ q qep l t ht2 hl A hq hsh

/-- `B2` (`localAuthDFShiftedPaper`) post-PRNG local game bounded by the two-mode
(`la = false` + `la = true`) `multiSessRealWinProb` of `redFSAuthDFShiftedPaperMulti`. -/
theorem localAuthDFShiftedPaper_le_multiSessRealWinProb
    (hD : ∀ k x, C.D k (C.E k x) = x)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (idOf : Party → IdentityKey) (lam : Pt) (hℓ : ℓ < 10 ^ 6)
    (q Δcka qep l t : ℕ) (ht3 : 2 + Δcka ≤ t) (hl : l = t - (1 + Δcka))
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq : MakesAtMostQueriesDF A q)
    (hsh : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    let Adv := fun la =>
      multiSessPubToAD protoSignalCodec
        (redFSAuthDFShiftedPaperMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep l t la A)
    𝒟[localAuthDFShiftedPaper (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep l (some (l - 1)) t A] {true} ≤
      multiSessRealWinProb C ℓ encT idOf Adv false +
        multiSessRealWinProb C ℓ encT idOf Adv true :=
  Computational.Proofs.E2E.SessionAuthMultiReal.localAuthDFShiftedPaper_le_multiSessRealWinProb ℓ Pt C Dh hD encPt encT hinj hdum idOf lam hℓ q Δcka qep l t ht3 hl A hq hsh

/-- Unshifted single-epoch (`AuthL11.localAuthDFPaper`) post-PRNG local game bounded by the two-mode
(`la = false` + `la = true`) `multiSessRealWinProb` of `redFSAuthDFPaperMulti`. -/
theorem localAuthDFPaper_le_multiSessRealWinProb
    (hD : ∀ k x, C.D k (C.E k x) = x)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (idOf : Party → IdentityKey) (lam : Pt) (hℓ : ℓ < 10 ^ 6)
    (q Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq : MakesAtMostQueriesDF A q)
    (hsh : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    let Adv := fun la =>
      multiSessPubToAD protoSignalCodec
        (redFSAuthDFPaperMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep la tL t A)
    𝒟[_root_.CryptoGames.SM.Construction.AuthL11.localAuthDFPaper (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep tL t A] {true} ≤
      multiSessRealWinProb C ℓ encT idOf Adv false +
        multiSessRealWinProb C ℓ encT idOf Adv true :=
  Computational.Proofs.E2E.SessionAuthMultiReal.localAuthDFPaper_le_multiSessRealWinProb ℓ Pt C Dh hD encPt encT hinj hdum idOf lam hℓ q Δcka qep tL t A hq hsh

/-- Post-PRNG `(tL, par)`-bucket local game under `corrAllowedPaper` (`engRunDFPaperBucket`)
evaluated with `authOutBucket` (without `&& (s.tL == tL)`). -/
@[expose] def localAuthDFPaperBucketRaw
    {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) : ProbComp Bool := do
  let r ← simulateQ _root_.CryptoGames.SM.Construction.AuthL11.lImpl
    (engRunDFPaperBucket (hooksLocalBucket cka prng fs Δcka qep tL par)
      (2 + Δcka) qep fs.maxSkip (bucketAuthCfg Δcka tL par)
      (initLocalBucket cka prng fs lam (3 + Δcka) qep tL par) {} false A)
  return match r with
    | none => false
    | some (_, st) =>
      match st.2 with
      | none => false
      | some tWin => !st.1.abort && st.1.g.win && authLosingConditionsAvoided (2 + Δcka) tL tWin st.1.g


/-- `(tL, par)`-bucket (`localAuthDFPaperBucketRaw`, without `&& (s.tL == tL)`) post-PRNG local game
bounded by the two-mode (`la = false` + `la = true`) `multiSessRealWinProb` of
`redFSAuthDFPaperMultiBucket`. -/
theorem localAuthDFPaperBucketRaw_le_multiSessRealWinProb
    (hD : ∀ k x, C.D k (C.E k x) = x)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (idOf : Party → IdentityKey) (lam : Pt) (hℓ : ℓ < 10 ^ 6)
    (q qep : ℕ) (tL : Option ℕ) (par : Bool)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq : MakesAtMostQueriesDF A q)
    (hsh : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    let Adv := fun la =>
      multiSessPubToAD protoSignalCodec
        (redFSAuthDFPaperMultiBucket (q + 1) (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam 1 4 qep la tL par A)
    𝒟[localAuthDFPaperBucketRaw (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam 1 qep tL par A] {true} ≤
      multiSessRealWinProb C ℓ encT idOf Adv false +
        multiSessRealWinProb C ℓ encT idOf Adv true :=
  Computational.Proofs.E2E.SessionAuthMultiReal.localAuthDFPaperBucketRaw_le_multiSessRealWinProb ℓ Pt C Dh hD encPt encT hinj hdum idOf lam hℓ q qep tL par A hq hsh

/-! ## 2. Ideal-Cutoff (`multiSessEndWinProb = 0`) Zero-Output Theorems -/


/-- Ideal-cutoff (`hp cut cut la`) zero-output theorem for `redFSAuthDFShiftedPaperMultiGen`
(`B1` and `B2`). -/
theorem multiSessEndWinProb_redFSAuthDFShiftedPaperMultiGen_eq_zero
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (q qR Δcka qep l t : ℕ) (authH la : Bool)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq : MakesAtMostQueriesDF A q) (hqR : 2 * q ≤ qR) :
    multiSessEndWinProb C ℓ encT idOf qR
      (fun la' =>
        multiSessPubToAD protoSignalCodec
          (redFSAuthDFShiftedPaperMultiGen (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep l t authH la' A))
      la = 0 :=
  Computational.Proofs.E2E.SessionAuthMultiEnd.multiSessEndWinProb_redFSAuthDFShiftedPaperMultiGen_eq_zero ℓ Pt C Dh encPt encT idOf lam q qR Δcka qep l t authH la A hq hqR

/-- Ideal-cutoff (`hp cut cut la`) zero-output theorem for `redFSAuthDFPaperMulti`. -/
theorem multiSessEndWinProb_redFSAuthDFPaperMulti_eq_zero
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (q qR Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) (la : Bool)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq : MakesAtMostQueriesDF A q) (hqR : 2 * q ≤ qR) :
    multiSessEndWinProb C ℓ encT idOf qR
      (fun la' =>
        multiSessPubToAD protoSignalCodec
          (redFSAuthDFPaperMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep la' tL t A))
      la = 0 :=
  Computational.Proofs.E2E.SessionAuthMultiEnd.multiSessEndWinProb_redFSAuthDFPaperMulti_eq_zero ℓ Pt C Dh encPt encT idOf lam q qR Δcka qep tL t la A hq hqR

/-- Ideal-cutoff (`hp cut cut la`) zero-output theorem for `redFSAuthDFPaperMultiBucket`. -/
theorem multiSessEndWinProb_redFSAuthDFPaperMultiBucket_eq_zero
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (q qR Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par la : Bool) (hΔb : 2 ≤ Δbucket := by omega)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq : MakesAtMostQueriesDF A q) (hqR : 2 * q ≤ qR) :
    multiSessEndWinProb C ℓ encT idOf qR
      (fun la' =>
        multiSessPubToAD protoSignalCodec
          (redFSAuthDFPaperMultiBucket (q + 1) (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka Δbucket qep la' tL par A))
      la = 0 :=
  Computational.Proofs.E2E.SessionAuthMultiEnd.multiSessEndWinProb_redFSAuthDFPaperMultiBucket_eq_zero ℓ Pt C Dh encPt encT idOf lam q qR Δcka Δbucket qep tL par la hΔb A hq hqR

/-- Per-session `2 * q` query bound on `redFSAuthDFShiftedPaperMultiGen`. -/
theorem redFSAuthDFShiftedPaperMultiGen_sess_isQueryBoundP
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (q Δcka qep l t : ℕ) (authH la : Bool)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq : MakesAtMostQueriesDF A q) (s : ℕ) :
    (redFSAuthDFShiftedPaperMultiGen (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep l t authH la A).IsQueryBoundP
      (fun x => (match x with | .inl _ => false | .inr ⟨s', _⟩ => decide (s' = s)) = true)
      (2 * q) :=
  (Computational.Proofs.E2E.SessionAuthMultiPot.redFSAuthDFShiftedPaperMultiGen_sess_isQueryBoundP
    (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
    (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam q Δcka qep l t authH la A hq s).of_imp
    fun x hx => by rcases x with _ | ⟨_, _⟩ <;> exact hx


/-- Per-session `2 * q` query bound on `redFSAuthDFPaperMulti`. -/
theorem redFSAuthDFPaperMulti_sess_isQueryBoundP
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (q Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) (la : Bool)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq : MakesAtMostQueriesDF A q) (s : ℕ) :
    (redFSAuthDFPaperMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep la tL t A).IsQueryBoundP
      (fun x => (match x with | .inl _ => false | .inr ⟨s', _⟩ => decide (s' = s)) = true)
      (2 * q) :=
  (Computational.Proofs.E2E.SessionAuthMultiPot.redFSAuthDFPaperMulti_sess_isQueryBoundP
    (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
    (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam q Δcka qep tL t la A hq s).of_imp
    fun x hx => by rcases x with _ | ⟨_, _⟩ <;> exact hx


/-- Per-session `2 * q` query bound on `redFSAuthDFPaperMultiBucket`. -/
theorem redFSAuthDFPaperMultiBucket_sess_isQueryBoundP
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (q Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par la : Bool)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq : MakesAtMostQueriesDF A q) (s : ℕ) :
    (redFSAuthDFPaperMultiBucket (q + 1) (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka Δbucket qep la tL par A).IsQueryBoundP
      (fun x => (match x with | .inl _ => false | .inr ⟨s', _⟩ => decide (s' = s)) = true)
      (2 * q) :=
  (Computational.Proofs.E2E.SessionAuthMultiPot.redFSAuthDFPaperMultiBucket_sess_isQueryBoundP
    (q + 1) (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
    (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam q Δcka Δbucket qep tL par la A hq s).of_imp
    fun x hx => by rcases x with _ | ⟨_, _⟩ <;> exact hx


private theorem self_le_two_mul_ennreal (x : ℝ≥0∞) : x ≤ 2 * x := by
  calc
    x = 1 * x := (one_mul x).symm
    _ ≤ 2 * x := by gcongr; norm_num

/-- Packaged `B1` (`localAuthDFShiftedDir2Paper`) Hop-3 Stage-2 bound into
`(∑ j ∈ Finset.range q, fsAuthCompBoundWith ...) + 4 * macForgeryTerm C q`. -/
theorem localAuthDFShiftedDir2Paper_le_fsAuthCompBoundWith
    (hD : ∀ k x, C.D k (C.E k x) = x)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (idOf : Party → IdentityKey) (lam : Pt) (hℓ : ℓ < 10 ^ 6)
    (q qep l t : ℕ) (hq32 : 2 * q + 25002 < 2 ^ 32) (ht2 : 2 ≤ t) (hl : l = t - 1)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq : MakesAtMostQueriesDF A q)
    (hsh : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A)
    (hg : GuardedSMDFShort A)
    (F : Bool → Bool → ℕ → FsAdv Pt ℓ)
    (hcompat : RouterAdvCompat C protoSignalCodec ℓ encT (pure ()) (fun _ => idOf)
      maxForwardJumps (2 * q) q
      (fun la (_ : Unit) =>
        multiSessPubToAD protoSignalCodec
          (redFSAuthDFShiftedDir2PaperMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam qep l t la A))
      (fun stage la j _ => F stage la j))
    (hF_q : ∀ j < q, ∀ stage la, _root_.CryptoGames.FSAEAD.MakesAtMostQueries (F stage la j) (2 * q))
    (hF_sh : ∀ j < q, ∀ stage la,
      _root_.CryptoGames.FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) (F stage la j)) :
    𝒟[localAuthDFShiftedDir2Paper (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam 0 qep l (some (l - 1)) t A] {true} ≤
      (∑ j ∈ Finset.range q,
        fsAuthCompBoundWith C protoSignalCodec ℓ (2 * q)
          (fsCostedRedsInst C protoSignalCodec ℓ encT idOf (2 * q))
          (fun stage la => F stage la j)) +
      4 * macForgeryTerm C q := by
  refine (localAuthDFShiftedDir2Paper_le_multiSessRealWinProb ℓ Pt C Dh hD encPt encT hinj hdum
    idOf lam hℓ q qep l t ht2 hl A hq hsh).trans ?_
  refine (self_le_two_mul_ennreal _).trans ?_
  exact multiSess_two_modes_le_sum_fsAuthCompBoundWith_two_mul_q C ℓ encT idOf q q hq32 _ F hℓ hinj hdum
    (redFSAuthDFShiftedPaperMultiGen_twoModeMultiSessBounds ℓ Pt C Dh encPt encT idOf lam hℓ q 0
      qep l t (by omega) false A hq hsh hg)
    hcompat hF_q hF_sh
    (multiSessEndWinProb_redFSAuthDFShiftedPaperMultiGen_eq_zero ℓ Pt C Dh encPt encT idOf lam q
      (2 * q) 0 qep l t false false A hq le_rfl)
    (multiSessEndWinProb_redFSAuthDFShiftedPaperMultiGen_eq_zero ℓ Pt C Dh encPt encT idOf lam q
      (2 * q) 0 qep l t false true A hq le_rfl)

/-- Packaged `B2` (`localAuthDFShiftedPaper`) Hop-3 Stage-2 bound into
`(∑ j ∈ Finset.range q, fsAuthCompBoundWith ...) + 4 * macForgeryTerm C q`. -/
theorem localAuthDFShiftedPaper_le_fsAuthCompBoundWith
    (hD : ∀ k x, C.D k (C.E k x) = x)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (idOf : Party → IdentityKey) (lam : Pt) (hℓ : ℓ < 10 ^ 6)
    (q Δcka qep l t : ℕ) (hq32 : 2 * q + 25002 < 2 ^ 32)
    (ht3 : 2 + Δcka ≤ t) (hl : l = t - (1 + Δcka))
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq : MakesAtMostQueriesDF A q)
    (hsh : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A)
    (hg : GuardedSMDFShort A)
    (F : Bool → Bool → ℕ → FsAdv Pt ℓ)
    (hcompat : RouterAdvCompat C protoSignalCodec ℓ encT (pure ()) (fun _ => idOf)
      maxForwardJumps (2 * q) q
      (fun la (_ : Unit) =>
        multiSessPubToAD protoSignalCodec
          (redFSAuthDFShiftedPaperMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep l t la A))
      (fun stage la j _ => F stage la j))
    (hF_q : ∀ j < q, ∀ stage la, _root_.CryptoGames.FSAEAD.MakesAtMostQueries (F stage la j) (2 * q))
    (hF_sh : ∀ j < q, ∀ stage la,
      _root_.CryptoGames.FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) (F stage la j)) :
    𝒟[localAuthDFShiftedPaper (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep l (some (l - 1)) t A] {true} ≤
      (∑ j ∈ Finset.range q,
        fsAuthCompBoundWith C protoSignalCodec ℓ (2 * q)
          (fsCostedRedsInst C protoSignalCodec ℓ encT idOf (2 * q))
          (fun stage la => F stage la j)) +
      4 * macForgeryTerm C q := by
  refine (localAuthDFShiftedPaper_le_multiSessRealWinProb ℓ Pt C Dh hD encPt encT hinj hdum
    idOf lam hℓ q Δcka qep l t ht3 hl A hq hsh).trans ?_
  refine (self_le_two_mul_ennreal _).trans ?_
  exact multiSess_two_modes_le_sum_fsAuthCompBoundWith_two_mul_q C ℓ encT idOf q q hq32 _ F hℓ hinj hdum
    (redFSAuthDFShiftedPaperMultiGen_twoModeMultiSessBounds ℓ Pt C Dh encPt encT idOf lam hℓ q Δcka
      qep l t (by omega) true A hq hsh hg)
    hcompat hF_q hF_sh
    (multiSessEndWinProb_redFSAuthDFShiftedPaperMultiGen_eq_zero ℓ Pt C Dh encPt encT idOf lam q
      (2 * q) Δcka qep l t true false A hq le_rfl)
    (multiSessEndWinProb_redFSAuthDFShiftedPaperMultiGen_eq_zero ℓ Pt C Dh encPt encT idOf lam q
      (2 * q) Δcka qep l t true true A hq le_rfl)

/-- Coin-averaged (`gMain ← sampleT Bool`) Stage-2 Hop-3 `(tL, par)`-bucket `Main + ForgedHdr`
bound into `1 * (∑ t ∈ Finset.Ico (healEpoch tL) (qep + 2), ∑ j ∈ Finset.range q, fsAuthCompBoundWith ...) +
4 * macForgeryTerm C q` (`complete` glue theorem). -/
theorem localAuthDFPaperBucket_main_add_forgedHdr_le_fsAuthCompBoundWith_of_coin
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (idOf : Party → IdentityKey) (lam : Pt) (hℓ : ℓ < 10 ^ 6)
    (q qep : ℕ) (hq32 : 2 * q + 25002 < 2 ^ 32) (tL : Option ℕ) (par : Bool)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (RBr : Bool → Bool → MultiSessPubFsAdv Pt ℓ)
    (F : Bool → Bool → ℕ → ℕ → FsAdv Pt ℓ)
    (hRealMain :
      𝒟[localAuthDFPaperBucketMain (dhScheme Dh) (rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam 1 qep tL par A] {true} ≤
        multiSessRealWinProb C ℓ encT idOf
          (fun la => multiSessPubToAD protoSignalCodec (RBr true la)) false +
        multiSessRealWinProb C ℓ encT idOf
          (fun la => multiSessPubToAD protoSignalCodec (RBr true la)) true)
    (hRealForged :
      𝒟[localAuthDFPaperBucketForgedHdr (dhScheme Dh) (rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam 1 qep tL par A] {true} ≤
        multiSessRealWinProb C ℓ encT idOf
          (fun la => multiSessPubToAD protoSignalCodec (RBr false la)) false +
        multiSessRealWinProb C ℓ encT idOf
          (fun la => multiSessPubToAD protoSignalCodec (RBr false la)) true)
    (hbds : TwoModeMultiSessBounds maxForwardJumps (2 * q)
      (((qep + 2) - healEpoch tL) * q) q
      (fun la (_ : Unit) =>
        multiSessPubToAD protoSignalCodec (sampleT Bool >>= fun gMain => RBr gMain la)))
    (hcompat : RouterAdvCompat C protoSignalCodec ℓ encT (pure ()) (fun _ => idOf)
      maxForwardJumps (2 * q) (((qep + 2) - healEpoch tL) * q)
      (fun la (_ : Unit) =>
        multiSessPubToAD protoSignalCodec (sampleT Bool >>= fun gMain => RBr gMain la))
      (fun stage la idx _ => F stage la (idx % q) (healEpoch tL + idx / q)))
    (hF_q : ∀ j < q, ∀ t ∈ Finset.Ico (healEpoch tL) (qep + 2), ∀ stage la,
      _root_.CryptoGames.FSAEAD.MakesAtMostQueries (F stage la j t) (2 * q))
    (hF_sh : ∀ j < q, ∀ t ∈ Finset.Ico (healEpoch tL) (qep + 2), ∀ stage la,
      _root_.CryptoGames.FSAEAD.EncMsgsOk
        (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) (F stage la j t))
    (hend : ∀ gMain la : Bool,
      multiSessEndWinProb C ℓ encT idOf (2 * q)
        (fun la' => multiSessPubToAD protoSignalCodec (RBr gMain la')) la = 0) :
    𝒟[localAuthDFPaperBucketMain (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam 1 qep tL par A] {true} +
      𝒟[localAuthDFPaperBucketForgedHdr (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam 1 qep tL par A] {true} ≤
      (∑ t ∈ Finset.Ico (healEpoch tL) (qep + 2),
        ∑ j ∈ Finset.range q,
          fsAuthCompBoundWith C protoSignalCodec ℓ (2 * q)
            (fsCostedRedsInst C protoSignalCodec ℓ encT idOf (2 * q))
            (fun stage la => F stage la j t)) +
      4 * macForgeryTerm C q := by
  let Adv : Bool → Bool → MultiSessFsAdv Pt ℓ :=
    fun gMain la => multiSessPubToAD protoSignalCodec (RBr gMain la)
  let AdvCoin : Bool → MultiSessFsAdv Pt ℓ :=
    fun la => multiSessPubToAD protoSignalCodec (sampleT Bool >>= fun gMain => RBr gMain la)
  have hCoinEq : ∀ la, AdvCoin la = (sampleT Bool >>= fun gMain => Adv gMain la) :=
    fun la => multiSessPubToAD_sampleT_bind protoSignalCodec (fun gMain => RBr gMain la)
  have hSum :
      𝒟[localAuthDFPaperBucketMain (dhScheme Dh) (rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam 1 qep tL par A] {true} +
        𝒟[localAuthDFPaperBucketForgedHdr (dhScheme Dh) (rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam 1 qep tL par A] {true} ≤
      2 * (multiSessRealWinProb C ℓ encT idOf AdvCoin false +
            multiSessRealWinProb C ℓ encT idOf AdvCoin true) := by
    refine (add_le_add hRealMain hRealForged).trans (le_of_eq ?_)
    have h1 : (multiSessRealWinProb C ℓ encT idOf (Adv true) false +
          multiSessRealWinProb C ℓ encT idOf (Adv true) true) +
        (multiSessRealWinProb C ℓ encT idOf (Adv false) false +
          multiSessRealWinProb C ℓ encT idOf (Adv false) true) =
        (multiSessRealWinProb C ℓ encT idOf (Adv true) false +
          multiSessRealWinProb C ℓ encT idOf (Adv false) false) +
        (multiSessRealWinProb C ℓ encT idOf (Adv true) true +
          multiSessRealWinProb C ℓ encT idOf (Adv false) true) := by
      ac_rfl
    rw [h1, multiSessRealWinProb_add_eq_two_mul_sampleT_bool C ℓ encT idOf Adv false,
      multiSessRealWinProb_add_eq_two_mul_sampleT_bool C ℓ encT idOf Adv true, ← mul_add]
    have hFunEq : (fun la' => sampleT Bool >>= fun gMain => Adv gMain la') = AdvCoin := by
      funext la'; exact (hCoinEq la').symm
    rw [hFunEq]
  refine hSum.trans ?_
  have hFunEq : AdvCoin = (fun la' => sampleT Bool >>= fun gMain => Adv gMain la') := by
    funext la'; exact hCoinEq la'
  have hendFalse : multiSessEndWinProb C ℓ encT idOf (2 * q) AdvCoin false = 0 := by
    rw [hFunEq]
    exact multiSessEndWinProb_sampleT_bool_eq_zero C ℓ encT idOf (2 * q) Adv false
      (hend true false) (hend false false)
  have hendTrue : multiSessEndWinProb C ℓ encT idOf (2 * q) AdvCoin true = 0 := by
    rw [hFunEq]
    exact multiSessEndWinProb_sampleT_bool_eq_zero C ℓ encT idOf (2 * q) Adv true
      (hend true true) (hend false true)
  have h1 := multiSess_two_modes_le_sum_fsAuthCompBoundWith_two_mul_q C ℓ encT idOf
    (((qep + 2) - healEpoch tL) * q) q hq32 AdvCoin
    (fun stage la idx => F stage la (idx % q) (healEpoch tL + idx / q))
    hℓ hinj hdum hbds hcompat
    (fun idx hidx stage la => by
      have hq0 : 0 < q := Nat.pos_of_ne_zero fun h0 => by subst h0; simp at hidx
      have hdiv : idx / q < (qep + 2) - healEpoch tL :=
        Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
      have hmem : healEpoch tL + idx / q ∈ Finset.Ico (healEpoch tL) (qep + 2) := by
        rw [Finset.mem_Ico]
        generalize idx / q = d at hdiv ⊢
        omega
      exact hF_q (idx % q) (Nat.mod_lt idx hq0) (healEpoch tL + idx / q) hmem stage la)
    (fun idx hidx stage la => by
      have hq0 : 0 < q := Nat.pos_of_ne_zero fun h0 => by subst h0; simp at hidx
      have hdiv : idx / q < (qep + 2) - healEpoch tL :=
        Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
      have hmem : healEpoch tL + idx / q ∈ Finset.Ico (healEpoch tL) (qep + 2) := by
        rw [Finset.mem_Ico]
        generalize idx / q = d at hdiv ⊢
        omega
      exact hF_sh (idx % q) (Nat.mod_lt idx hq0) (healEpoch tL + idx / q) hmem stage la)
    hendFalse hendTrue
  refine h1.trans (add_le_add ?_ le_rfl)
  by_cases hle : healEpoch tL ≤ qep + 2
  · rw [sum_range_mul_mod_div ((qep + 2) - healEpoch tL) q
      (fun j d => fsAuthCompBoundWith C protoSignalCodec ℓ (2 * q)
        (fsCostedRedsInst C protoSignalCodec ℓ encT idOf (2 * q))
        (fun stage la => F stage la j (healEpoch tL + d)))]
    rw [Finset.sum_Ico_eq_sum_range]
  · have hsub : (qep + 2) - healEpoch tL = 0 := Nat.sub_eq_zero_of_le (by omega)
    have hico : Finset.Ico (healEpoch tL) (qep + 2) = ∅ := Finset.Ico_eq_empty (by omega)
    simp [hsub, hico]

/-- Per-branch (`gMain = true` + `gMain = false`) Stage-2 Hop-3 `(tL, par)`-bucket `Main + ForgedHdr`
bound into `1 * (∑ t ∈ Finset.Ico (healEpoch tL) (qep + 2), ∑ j ∈ Finset.range q, fsAuthCompBoundWith ...) +
4 * macForgeryTerm C q` (`complete`, automatically lifting per-branch `TwoModeMultiSessBounds` across
`sampleT Bool`). -/
theorem localAuthDFPaperBucket_main_add_forgedHdr_le_fsAuthCompBoundWith_of_branches
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (idOf : Party → IdentityKey) (lam : Pt) (hℓ : ℓ < 10 ^ 6)
    (q qep : ℕ) (hq32 : 2 * q + 25002 < 2 ^ 32) (tL : Option ℕ) (par : Bool)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (RBr : Bool → Bool → MultiSessPubFsAdv Pt ℓ)
    (F : Bool → Bool → ℕ → ℕ → FsAdv Pt ℓ)
    (hRealMain :
      𝒟[localAuthDFPaperBucketMain (dhScheme Dh) (rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam 1 qep tL par A] {true} ≤
        multiSessRealWinProb C ℓ encT idOf
          (fun la => multiSessPubToAD protoSignalCodec (RBr true la)) false +
        multiSessRealWinProb C ℓ encT idOf
          (fun la => multiSessPubToAD protoSignalCodec (RBr true la)) true)
    (hRealForged :
      𝒟[localAuthDFPaperBucketForgedHdr (dhScheme Dh) (rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam 1 qep tL par A] {true} ≤
        multiSessRealWinProb C ℓ encT idOf
          (fun la => multiSessPubToAD protoSignalCodec (RBr false la)) false +
        multiSessRealWinProb C ℓ encT idOf
          (fun la => multiSessPubToAD protoSignalCodec (RBr false la)) true)
    (hbdsMain : TwoModeMultiSessBounds maxForwardJumps (2 * q)
      (((qep + 2) - healEpoch tL) * q) q
      (fun la (_ : Unit) => multiSessPubToAD protoSignalCodec (RBr true la)))
    (hbdsForged : TwoModeMultiSessBounds maxForwardJumps (2 * q)
      (((qep + 2) - healEpoch tL) * q) q
      (fun la (_ : Unit) => multiSessPubToAD protoSignalCodec (RBr false la)))
    (honeAD : ∀ la j, ∃ k₀ : ℕ, ∀ gMain,
      (multiSessPubToAD protoSignalCodec (RBr gMain la)).IsQueryBoundP
        (fun t => onSess (fsOutsideClass
          (fun ap : Header Pt × LibsignalMsgPublicPart => ap.1.1) k₀) j t = true) 0)
    (hcompat : RouterAdvCompat C protoSignalCodec ℓ encT (pure ()) (fun _ => idOf)
      maxForwardJumps (2 * q) (((qep + 2) - healEpoch tL) * q)
      (fun la (_ : Unit) =>
        multiSessPubToAD protoSignalCodec (sampleT Bool >>= fun gMain => RBr gMain la))
      (fun stage la idx _ => F stage la (idx % q) (healEpoch tL + idx / q)))
    (hF_q : ∀ j < q, ∀ t ∈ Finset.Ico (healEpoch tL) (qep + 2), ∀ stage la,
      _root_.CryptoGames.FSAEAD.MakesAtMostQueries (F stage la j t) (2 * q))
    (hF_sh : ∀ j < q, ∀ t ∈ Finset.Ico (healEpoch tL) (qep + 2), ∀ stage la,
      _root_.CryptoGames.FSAEAD.EncMsgsOk
        (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) (F stage la j t))
    (hend : ∀ gMain la : Bool,
      multiSessEndWinProb C ℓ encT idOf (2 * q)
        (fun la' => multiSessPubToAD protoSignalCodec (RBr gMain la')) la = 0) :
    𝒟[localAuthDFPaperBucketMain (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam 1 qep tL par A] {true} +
      𝒟[localAuthDFPaperBucketForgedHdr (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam 1 qep tL par A] {true} ≤
      (∑ t ∈ Finset.Ico (healEpoch tL) (qep + 2),
        ∑ j ∈ Finset.range q,
          fsAuthCompBoundWith C protoSignalCodec ℓ (2 * q)
            (fsCostedRedsInst C protoSignalCodec ℓ encT idOf (2 * q))
            (fun stage la => F stage la j t)) +
      4 * macForgeryTerm C q := by
  have hbdsCoin : TwoModeMultiSessBounds maxForwardJumps (2 * q)
      (((qep + 2) - healEpoch tL) * q) q
      (fun la (_ : Unit) =>
        multiSessPubToAD protoSignalCodec (sampleT Bool >>= fun gMain => RBr gMain la)) := by
    have hEq : (fun la (_ : Unit) =>
        multiSessPubToAD protoSignalCodec (sampleT Bool >>= fun gMain => RBr gMain la)) =
      (fun la (_ : Unit) =>
        sampleT Bool >>= fun gMain => multiSessPubToAD protoSignalCodec (RBr gMain la)) := by
      funext la _
      exact multiSessPubToAD_sampleT_bind protoSignalCodec (fun gMain => RBr gMain la)
    rw [hEq]
    exact twoModeMultiSessBounds_sampleT_bool
      (fun gMain la (_ : Unit) => multiSessPubToAD protoSignalCodec (RBr gMain la))
      hbdsMain hbdsForged (fun la j _ => honeAD la j)
  exact localAuthDFPaperBucket_main_add_forgedHdr_le_fsAuthCompBoundWith_of_coin
    ℓ Pt C Dh encPt encT hinj hdum idOf lam hℓ q qep hq32 tL par A RBr F
    hRealMain hRealForged hbdsCoin hcompat hF_q hF_sh hend

/-! ## 5. `qR = min (2 * q) (q + 2)` Stage-2 Corollaries (`R116` P3a) -/

theorem multiSessEndWinProb_redFSAuthDFShiftedPaperMultiGen_eq_zero_min
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (q qR Δcka qep l t : ℕ) (authH la : Bool)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq : MakesAtMostQueriesDF A q) (hqR : min (2 * q) (q + 2) ≤ qR) :
    multiSessEndWinProb C ℓ encT idOf qR
      (fun la' => multiSessPubToAD protoSignalCodec
        (redFSAuthDFShiftedPaperMultiGen (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep l t authH la' A)) la = 0 :=
  Computational.Proofs.E2E.SessionAuthMultiEnd.multiSessEndWinProb_redFSAuthDFShiftedPaperMultiGen_eq_zero_min
    ℓ Pt C Dh encPt encT idOf lam q qR Δcka qep l t authH la A hq hqR

theorem multiSessEndWinProb_redFSAuthDFPaperMultiBucket_eq_zero_min
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (q qR Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par la : Bool) (hΔb : 2 ≤ Δbucket := by omega)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq : MakesAtMostQueriesDF A q) (hqR : min (2 * q) (q + 2) ≤ qR) :
    multiSessEndWinProb C ℓ encT idOf qR
      (fun la' => multiSessPubToAD protoSignalCodec
        (redFSAuthDFPaperMultiBucket (q + 1) (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka Δbucket qep la' tL par A)) la = 0 :=
  Computational.Proofs.E2E.SessionAuthMultiEnd.multiSessEndWinProb_redFSAuthDFPaperMultiBucket_eq_zero_min
    ℓ Pt C Dh encPt encT idOf lam q qR Δcka Δbucket qep tL par la hΔb A hq hqR

theorem redFSAuthDFShiftedPaperMultiGen_sess_isQueryBoundP_min
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (q Δcka qep l t : ℕ) (authH la : Bool)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq : MakesAtMostQueriesDF A q) (s : ℕ) :
    (redFSAuthDFShiftedPaperMultiGen (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep l t authH la A).IsQueryBoundP
      (fun x => (match x with | .inl _ => false | .inr ⟨s', _⟩ => decide (s' = s)) = true)
      (min (2 * q) (q + 2)) :=
  (Computational.Proofs.E2E.SessionAuthMultiPot.redFSAuthDFShiftedPaperMultiGen_sess_isQueryBoundP_min
    (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
    (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam q Δcka qep l t authH la A hq s).of_imp
    fun x hx => by rcases x with _ | ⟨_, _⟩ <;> exact hx

theorem redFSAuthDFPaperMultiBucket_sess_isQueryBoundP_min
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (q Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par la : Bool)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq : MakesAtMostQueriesDF A q) (s : ℕ) :
    (redFSAuthDFPaperMultiBucket (q + 1) (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka Δbucket qep la tL par A).IsQueryBoundP
      (fun x => (match x with | .inl _ => false | .inr ⟨s', _⟩ => decide (s' = s)) = true)
      (min (2 * q) (q + 2)) :=
  (Computational.Proofs.E2E.SessionAuthMultiPot.redFSAuthDFPaperMultiBucket_sess_isQueryBoundP_min
    (q + 1) (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
    (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam q Δcka Δbucket qep tL par la A hq s).of_imp
    fun x hx => by rcases x with _ | ⟨_, _⟩ <;> exact hx

theorem localAuthDFShiftedDir2Paper_le_fsAuthCompBoundWith_min
    (hD : ∀ k x, C.D k (C.E k x) = x) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (idOf : Party → IdentityKey) (lam : Pt) (hℓ : ℓ < 10 ^ 6)
    (q qep l t : ℕ) (hq32 : 2 * q + 25002 < 2 ^ 32) (ht2 : 2 ≤ t) (hl : l = t - 1)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq : MakesAtMostQueriesDF A q)
    (hsh : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A)
    (hg : GuardedSMDFShort A) (F : Bool → Bool → ℕ → FsAdv Pt ℓ)
    (hcompat : RouterAdvCompat C protoSignalCodec ℓ encT (pure ()) (fun _ => idOf)
      maxForwardJumps (min (2 * q) (q + 2)) q
      (fun la (_ : Unit) => multiSessPubToAD protoSignalCodec
        (redFSAuthDFShiftedDir2PaperMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam qep l t la A))
      (fun stage la j _ => F stage la j))
    (hF_q : ∀ j < q, ∀ stage la, _root_.CryptoGames.FSAEAD.MakesAtMostQueries (F stage la j) (min (2 * q) (q + 2)))
    (hF_sh : ∀ j < q, ∀ stage la,
      _root_.CryptoGames.FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) (F stage la j)) :
    𝒟[localAuthDFShiftedDir2Paper (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam 0 qep l (some (l - 1)) t A] {true} ≤
      (∑ j ∈ Finset.range q, fsAuthCompBoundWith C protoSignalCodec ℓ (min (2 * q) (q + 2))
        (fsCostedRedsInst C protoSignalCodec ℓ encT idOf (min (2 * q) (q + 2))) (fun stage la => F stage la j)) +
      4 * macForgeryTerm C q := by
  have hbds0 := redFSAuthDFShiftedPaperMultiGen_twoModeMultiSessBounds ℓ Pt C Dh encPt encT idOf
    lam hℓ q 0 qep l t (by omega) false A hq hsh hg
  have hbds : TwoModeMultiSessBounds maxForwardJumps (min (2 * q) (q + 2)) q q
      (fun la (_ : Unit) => multiSessPubToAD protoSignalCodec
        (redFSAuthDFShiftedDir2PaperMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam qep l t la A)) :=
    ⟨hbds0.offRange, hbds0.decBound, hbds0.shortAD, hbds0.guardedShort, hbds0.oneADClass⟩
  refine (localAuthDFShiftedDir2Paper_le_multiSessRealWinProb ℓ Pt C Dh hD encPt encT hinj hdum
    idOf lam hℓ q qep l t ht2 hl A hq hsh).trans ((self_le_two_mul_ennreal _).trans ?_)
  exact multiSess_two_modes_le_sum_fsAuthCompBoundWith_min C ℓ encT idOf q q hq32 _ F hℓ hinj hdum
    hbds hcompat hF_q hF_sh
    (multiSessEndWinProb_redFSAuthDFShiftedPaperMultiGen_eq_zero_min ℓ Pt C Dh encPt encT idOf lam q
      (min (2 * q) (q + 2)) 0 qep l t false false A hq le_rfl)
    (multiSessEndWinProb_redFSAuthDFShiftedPaperMultiGen_eq_zero_min ℓ Pt C Dh encPt encT idOf lam q
      (min (2 * q) (q + 2)) 0 qep l t false true A hq le_rfl)

theorem localAuthDFShiftedPaper_le_fsAuthCompBoundWith_min
    (hD : ∀ k x, C.D k (C.E k x) = x) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (idOf : Party → IdentityKey) (lam : Pt) (hℓ : ℓ < 10 ^ 6)
    (q Δcka qep l t : ℕ) (hq32 : 2 * q + 25002 < 2 ^ 32) (ht3 : 2 + Δcka ≤ t) (hl : l = t - (1 + Δcka))
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq : MakesAtMostQueriesDF A q)
    (hsh : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A)
    (hg : GuardedSMDFShort A) (F : Bool → Bool → ℕ → FsAdv Pt ℓ)
    (hcompat : RouterAdvCompat C protoSignalCodec ℓ encT (pure ()) (fun _ => idOf)
      maxForwardJumps (min (2 * q) (q + 2)) q
      (fun la (_ : Unit) => multiSessPubToAD protoSignalCodec
        (redFSAuthDFShiftedPaperMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep l t la A))
      (fun stage la j _ => F stage la j))
    (hF_q : ∀ j < q, ∀ stage la, _root_.CryptoGames.FSAEAD.MakesAtMostQueries (F stage la j) (min (2 * q) (q + 2)))
    (hF_sh : ∀ j < q, ∀ stage la,
      _root_.CryptoGames.FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) (F stage la j)) :
    𝒟[localAuthDFShiftedPaper (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep l (some (l - 1)) t A] {true} ≤
      (∑ j ∈ Finset.range q, fsAuthCompBoundWith C protoSignalCodec ℓ (min (2 * q) (q + 2))
        (fsCostedRedsInst C protoSignalCodec ℓ encT idOf (min (2 * q) (q + 2))) (fun stage la => F stage la j)) +
      4 * macForgeryTerm C q := by
  have hbds0 := redFSAuthDFShiftedPaperMultiGen_twoModeMultiSessBounds ℓ Pt C Dh encPt encT idOf
    lam hℓ q Δcka qep l t (by omega) true A hq hsh hg
  have hbds : TwoModeMultiSessBounds maxForwardJumps (min (2 * q) (q + 2)) q q
      (fun la (_ : Unit) => multiSessPubToAD protoSignalCodec
        (redFSAuthDFShiftedPaperMulti (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep l t la A)) :=
    ⟨hbds0.offRange, hbds0.decBound, hbds0.shortAD, hbds0.guardedShort, hbds0.oneADClass⟩
  refine (localAuthDFShiftedPaper_le_multiSessRealWinProb ℓ Pt C Dh hD encPt encT hinj hdum
    idOf lam hℓ q Δcka qep l t ht3 hl A hq hsh).trans ((self_le_two_mul_ennreal _).trans ?_)
  exact multiSess_two_modes_le_sum_fsAuthCompBoundWith_min C ℓ encT idOf q q hq32 _ F hℓ hinj hdum
    hbds hcompat hF_q hF_sh
    (multiSessEndWinProb_redFSAuthDFShiftedPaperMultiGen_eq_zero_min ℓ Pt C Dh encPt encT idOf lam q
      (min (2 * q) (q + 2)) Δcka qep l t true false A hq le_rfl)
    (multiSessEndWinProb_redFSAuthDFShiftedPaperMultiGen_eq_zero_min ℓ Pt C Dh encPt encT idOf lam q
      (min (2 * q) (q + 2)) Δcka qep l t true true A hq le_rfl)

theorem localAuthDFPaperBucket_main_add_forgedHdr_le_fsAuthCompBoundWith_of_coin_min
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (idOf : Party → IdentityKey) (lam : Pt) (hℓ : ℓ < 10 ^ 6)
    (q qep : ℕ) (hq32 : 2 * q + 25002 < 2 ^ 32) (tL : Option ℕ) (par : Bool)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (RBr : Bool → Bool → MultiSessPubFsAdv Pt ℓ) (F : Bool → Bool → ℕ → ℕ → FsAdv Pt ℓ)
    (hRealMain : 𝒟[localAuthDFPaperBucketMain (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam 1 qep tL par A] {true} ≤
      multiSessRealWinProb C ℓ encT idOf (fun la => multiSessPubToAD protoSignalCodec (RBr true la)) false +
      multiSessRealWinProb C ℓ encT idOf (fun la => multiSessPubToAD protoSignalCodec (RBr true la)) true)
    (hRealForged : 𝒟[localAuthDFPaperBucketForgedHdr (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam 1 qep tL par A] {true} ≤
      multiSessRealWinProb C ℓ encT idOf (fun la => multiSessPubToAD protoSignalCodec (RBr false la)) false +
      multiSessRealWinProb C ℓ encT idOf (fun la => multiSessPubToAD protoSignalCodec (RBr false la)) true)
    (hbds : TwoModeMultiSessBounds maxForwardJumps (min (2 * q) (q + 2)) (((qep + 2) - healEpoch tL) * q) q
      (fun la (_ : Unit) => multiSessPubToAD protoSignalCodec (sampleT Bool >>= fun gMain => RBr gMain la)))
    (hcompat : RouterAdvCompat C protoSignalCodec ℓ encT (pure ()) (fun _ => idOf)
      maxForwardJumps (min (2 * q) (q + 2)) (((qep + 2) - healEpoch tL) * q)
      (fun la (_ : Unit) => multiSessPubToAD protoSignalCodec (sampleT Bool >>= fun gMain => RBr gMain la))
      (fun stage la idx _ => F stage la (idx % q) (healEpoch tL + idx / q)))
    (hF_q : ∀ j < q, ∀ t ∈ Finset.Ico (healEpoch tL) (qep + 2), ∀ stage la,
      _root_.CryptoGames.FSAEAD.MakesAtMostQueries (F stage la j t) (min (2 * q) (q + 2)))
    (hF_sh : ∀ j < q, ∀ t ∈ Finset.Ico (healEpoch tL) (qep + 2), ∀ stage la,
      _root_.CryptoGames.FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) (F stage la j t))
    (hend : ∀ gMain la : Bool, multiSessEndWinProb C ℓ encT idOf (min (2 * q) (q + 2))
      (fun la' => multiSessPubToAD protoSignalCodec (RBr gMain la')) la = 0) :
    𝒟[localAuthDFPaperBucketMain (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam 1 qep tL par A] {true} +
      𝒟[localAuthDFPaperBucketForgedHdr (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam 1 qep tL par A] {true} ≤
      (∑ t ∈ Finset.Ico (healEpoch tL) (qep + 2), ∑ j ∈ Finset.range q,
        fsAuthCompBoundWith C protoSignalCodec ℓ (min (2 * q) (q + 2))
          (fsCostedRedsInst C protoSignalCodec ℓ encT idOf (min (2 * q) (q + 2))) (fun stage la => F stage la j t)) +
      4 * macForgeryTerm C q := by
  let Adv : Bool → Bool → MultiSessFsAdv Pt ℓ := fun gMain la => multiSessPubToAD protoSignalCodec (RBr gMain la)
  let AdvCoin : Bool → MultiSessFsAdv Pt ℓ := fun la => multiSessPubToAD protoSignalCodec (sampleT Bool >>= fun gMain => RBr gMain la)
  have hFunEq : AdvCoin = (fun la' => sampleT Bool >>= fun gMain => Adv gMain la') := by
    funext la'; exact multiSessPubToAD_sampleT_bind protoSignalCodec (fun gMain => RBr gMain la')
  have hSum : 𝒟[localAuthDFPaperBucketMain (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam 1 qep tL par A] {true} +
      𝒟[localAuthDFPaperBucketForgedHdr (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam 1 qep tL par A] {true} ≤
      2 * (multiSessRealWinProb C ℓ encT idOf AdvCoin false + multiSessRealWinProb C ℓ encT idOf AdvCoin true) := by
    refine (add_le_add hRealMain hRealForged).trans (le_of_eq ?_)
    have h1 : (multiSessRealWinProb C ℓ encT idOf (Adv true) false + multiSessRealWinProb C ℓ encT idOf (Adv true) true) +
        (multiSessRealWinProb C ℓ encT idOf (Adv false) false + multiSessRealWinProb C ℓ encT idOf (Adv false) true) =
        (multiSessRealWinProb C ℓ encT idOf (Adv true) false + multiSessRealWinProb C ℓ encT idOf (Adv false) false) +
        (multiSessRealWinProb C ℓ encT idOf (Adv true) true + multiSessRealWinProb C ℓ encT idOf (Adv false) true) := by ac_rfl
    rw [h1, multiSessRealWinProb_add_eq_two_mul_sampleT_bool C ℓ encT idOf Adv false,
      multiSessRealWinProb_add_eq_two_mul_sampleT_bool C ℓ encT idOf Adv true, ← mul_add, ← hFunEq]
  have hIdx (idx : ℕ) (hidx : idx < ((qep + 2) - healEpoch tL) * q) :
      idx % q < q ∧ healEpoch tL + idx / q ∈ Finset.Ico (healEpoch tL) (qep + 2) := by
    have hq0 : 0 < q := Nat.pos_of_ne_zero fun h0 => by subst h0; simp at hidx
    have hdiv : idx / q < (qep + 2) - healEpoch tL := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
    refine ⟨Nat.mod_lt idx hq0, ?_⟩
    rw [Finset.mem_Ico]; generalize idx / q = d at hdiv ⊢; omega
  have hendFalse : multiSessEndWinProb C ℓ encT idOf (min (2 * q) (q + 2)) AdvCoin false = 0 := by
    rw [hFunEq]; exact multiSessEndWinProb_sampleT_bool_eq_zero C ℓ encT idOf (min (2 * q) (q + 2)) Adv false (hend true false) (hend false false)
  have hendTrue : multiSessEndWinProb C ℓ encT idOf (min (2 * q) (q + 2)) AdvCoin true = 0 := by
    rw [hFunEq]; exact multiSessEndWinProb_sampleT_bool_eq_zero C ℓ encT idOf (min (2 * q) (q + 2)) Adv true (hend true true) (hend false true)
  refine hSum.trans ((multiSess_two_modes_le_sum_fsAuthCompBoundWith_min C ℓ encT idOf
    (((qep + 2) - healEpoch tL) * q) q hq32 AdvCoin
    (fun stage la idx => F stage la (idx % q) (healEpoch tL + idx / q))
    hℓ hinj hdum ⟨hbds.1, hbds.2, hbds.3, hbds.4, hbds.5⟩ hcompat
    (fun idx hidx stage la => hF_q _ (hIdx idx hidx).1 _ (hIdx idx hidx).2 stage la)
    (fun idx hidx stage la => hF_sh _ (hIdx idx hidx).1 _ (hIdx idx hidx).2 stage la)
    hendFalse hendTrue).trans (add_le_add ?_ le_rfl))
  by_cases hle : healEpoch tL ≤ qep + 2
  · rw [sum_range_mul_mod_div ((qep + 2) - healEpoch tL) q
      (fun j d => fsAuthCompBoundWith C protoSignalCodec ℓ (min (2 * q) (q + 2))
        (fsCostedRedsInst C protoSignalCodec ℓ encT idOf (min (2 * q) (q + 2)))
        (fun stage la => F stage la j (healEpoch tL + d))), Finset.sum_Ico_eq_sum_range]
  · simp [Nat.sub_eq_zero_of_le (by omega : qep + 2 ≤ healEpoch tL),
      Finset.Ico_eq_empty (by omega : ¬ healEpoch tL < qep + 2)]

theorem localAuthDFPaperBucket_main_add_forgedHdr_le_fsAuthCompBoundWith_of_branches_min
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (idOf : Party → IdentityKey) (lam : Pt) (hℓ : ℓ < 10 ^ 6)
    (q qep : ℕ) (hq32 : 2 * q + 25002 < 2 ^ 32) (tL : Option ℕ) (par : Bool)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (RBr : Bool → Bool → MultiSessPubFsAdv Pt ℓ) (F : Bool → Bool → ℕ → ℕ → FsAdv Pt ℓ)
    (hRealMain : 𝒟[localAuthDFPaperBucketMain (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam 1 qep tL par A] {true} ≤
      multiSessRealWinProb C ℓ encT idOf (fun la => multiSessPubToAD protoSignalCodec (RBr true la)) false +
      multiSessRealWinProb C ℓ encT idOf (fun la => multiSessPubToAD protoSignalCodec (RBr true la)) true)
    (hRealForged : 𝒟[localAuthDFPaperBucketForgedHdr (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam 1 qep tL par A] {true} ≤
      multiSessRealWinProb C ℓ encT idOf (fun la => multiSessPubToAD protoSignalCodec (RBr false la)) false +
      multiSessRealWinProb C ℓ encT idOf (fun la => multiSessPubToAD protoSignalCodec (RBr false la)) true)
    (hbdsMain : TwoModeMultiSessBounds maxForwardJumps (min (2 * q) (q + 2)) (((qep + 2) - healEpoch tL) * q) q
      (fun la (_ : Unit) => multiSessPubToAD protoSignalCodec (RBr true la)))
    (hbdsForged : TwoModeMultiSessBounds maxForwardJumps (min (2 * q) (q + 2)) (((qep + 2) - healEpoch tL) * q) q
      (fun la (_ : Unit) => multiSessPubToAD protoSignalCodec (RBr false la)))
    (honeAD : ∀ la j, ∃ k₀ : ℕ, ∀ gMain,
      (multiSessPubToAD protoSignalCodec (RBr gMain la)).IsQueryBoundP
        (fun t => onSess (fsOutsideClass (fun ap : Header Pt × LibsignalMsgPublicPart => ap.1.1) k₀) j t = true) 0)
    (hcompat : RouterAdvCompat C protoSignalCodec ℓ encT (pure ()) (fun _ => idOf)
      maxForwardJumps (min (2 * q) (q + 2)) (((qep + 2) - healEpoch tL) * q)
      (fun la (_ : Unit) => multiSessPubToAD protoSignalCodec (sampleT Bool >>= fun gMain => RBr gMain la))
      (fun stage la idx _ => F stage la (idx % q) (healEpoch tL + idx / q)))
    (hF_q : ∀ j < q, ∀ t ∈ Finset.Ico (healEpoch tL) (qep + 2), ∀ stage la,
      _root_.CryptoGames.FSAEAD.MakesAtMostQueries (F stage la j t) (min (2 * q) (q + 2)))
    (hF_sh : ∀ j < q, ∀ t ∈ Finset.Ico (healEpoch tL) (qep + 2), ∀ stage la,
      _root_.CryptoGames.FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) (F stage la j t))
    (hend : ∀ gMain la : Bool, multiSessEndWinProb C ℓ encT idOf (min (2 * q) (q + 2))
      (fun la' => multiSessPubToAD protoSignalCodec (RBr gMain la')) la = 0) :
    𝒟[localAuthDFPaperBucketMain (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam 1 qep tL par A] {true} +
      𝒟[localAuthDFPaperBucketForgedHdr (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam 1 qep tL par A] {true} ≤
      (∑ t ∈ Finset.Ico (healEpoch tL) (qep + 2), ∑ j ∈ Finset.range q,
        fsAuthCompBoundWith C protoSignalCodec ℓ (min (2 * q) (q + 2))
          (fsCostedRedsInst C protoSignalCodec ℓ encT idOf (min (2 * q) (q + 2))) (fun stage la => F stage la j t)) +
      4 * macForgeryTerm C q := by
  have hbdsCoin : TwoModeMultiSessBounds maxForwardJumps (min (2 * q) (q + 2))
      (((qep + 2) - healEpoch tL) * q) q
      (fun la (_ : Unit) => multiSessPubToAD protoSignalCodec (sampleT Bool >>= fun gMain => RBr gMain la)) := by
    have hEq : (fun la (_ : Unit) => multiSessPubToAD protoSignalCodec (sampleT Bool >>= fun gMain => RBr gMain la)) =
        (fun la (_ : Unit) => sampleT Bool >>= fun gMain => multiSessPubToAD protoSignalCodec (RBr gMain la)) := by
      funext la _; exact multiSessPubToAD_sampleT_bind protoSignalCodec (fun gMain => RBr gMain la)
    rw [hEq]
    exact twoModeMultiSessBounds_sampleT_bool
      (fun gMain la (_ : Unit) => multiSessPubToAD protoSignalCodec (RBr gMain la))
      hbdsMain hbdsForged (fun la j _ => honeAD la j)
  exact localAuthDFPaperBucket_main_add_forgedHdr_le_fsAuthCompBoundWith_of_coin_min
    ℓ Pt C Dh encPt encT hinj hdum idOf lam hℓ q qep hq32 tL par A RBr F
    hRealMain hRealForged hbdsCoin hcompat hF_q hF_sh hend

end LibsignalBridges

end

end Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFSMulti
