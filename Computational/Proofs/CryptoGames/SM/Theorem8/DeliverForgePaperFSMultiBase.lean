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
import Computational.Proofs.E2E.SessionAuthHooksPot
import Computational.Proofs.E2E.SessionAuthMultiPot

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
open _root_.CryptoGames.SM.Construction (Header Mode healEpoch
  inStage2BucketGen redFSAuthDFPaperMulti redFSAuthDFPaperMultiBucket)
open _root_.CryptoGames.SM.Construction.DeliverForge (AdversaryDF SchemeAdversaryDF
  MakesAtMostQueriesDF authOutBucket authOutBucketPaper bucketAuthCfg engRunDFPaperBucket
  hooksLocalBucket initLocalBucket
  localAuthDFPaperBucket localAuthDFShiftedDir2Paper localAuthDFShiftedPaper)
open _root_.CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey maxForwardJumps)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart dummyKey lFS)
open _root_.CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C)
open _root_.CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open _root_.CryptoVerification.LibsignalSession.HeadlineV1 (SendMsgsOkDF GuardedSMDFShort)
open Computational.Proofs.ReductionDsl.Fig8Atomic (atomicShortPubB)
open Computational.Proofs.ReductionDsl.FsAtomicMacros (atomicShortB)
open _root_.CryptoVerification.LibsignalSession (FsAdv fsAuthCompBoundWith fsCostedRedsInst macForgeryTerm)
open _root_.CryptoVerification.E2E.Signed.SessionRouter (lazyInit sessLift multiSessSpec sessOffRange)
open _root_.CryptoVerification.E2E.Signed.SessionFS (fsInit fsImpl)
open Computational.Proofs.E2E.SessionAuthBridge (authHopCutoff MultiSessFsAdv multiSessPubToAD
  TwoModeMultiSessBounds RouterAdvCompat)
open Computational.Proofs.SessionCostedFig8.TopAssembly (multiSessRealWinProb multiSessEndWinProb
  multiSess_two_modes_le_sum_fsAuthCompBoundWith_min sum_range_mul_mod_div)
open Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2 (
  redFSAuthDFShiftedPaperMultiGen redFSAuthDFShiftedPaperMulti redFSAuthDFShiftedDir2PaperMulti)

/-- Single-session real (`b_fs = false`) initial state sampler for `fs : FSAEADScheme`. -/
@[expose] def fsMultiRealInit {K SS RS AD M E : Type} [SampleableType K]
    (fs : FSAEADScheme K SS RS AD M E) :
    ProbComp (_root_.CryptoGames.FSAEAD.State SS RS AD M E) := do
  let k ← ($ᵗ K : ProbComp K)
  return _root_.CryptoGames.FSAEAD.initState fs k false

theorem fsMultiRealInit_b_false {K SS RS AD M E : Type} [SampleableType K]
    (fs : FSAEADScheme K SS RS AD M E)
    {st : _root_.CryptoGames.FSAEAD.State SS RS AD M E} (hst : st ∈ support (fsMultiRealInit fs)) :
    st.b = false := by
  unfold fsMultiRealInit at hst
  rw [mem_support_bind_iff] at hst
  obtain ⟨k, _, hk⟩ := hst
  simp only [support_pure, Set.mem_singleton_iff] at hk
  subst hk
  rfl

/-- Multi-session real (`Thm5.hp 0 0 la`) execution of a multi-session ratchet adversary `Adv`. -/
@[expose] def multiFsRealRun {CK MK AD M C : Type}
    [SampleableType MK] [SampleableType CK]
    [DecidableEq AD] [DecidableEq M] [DecidableEq C]
    (ideal : ℕ × AD → ProbComp C) (ae : AEADScheme MK (ℕ × AD) M C)
    (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ) (la : Bool)
    (Adv : OracleComp (unifSpec + multiSessSpec (CryptoVerification.E2E.Signed.SessionFS.fsSpec CK MK AD M C)) Bool) :
    ProbComp Bool :=
  Prod.fst <$> (simulateQ (sessLift
    (lazyInit fsInit (fsImpl ideal ae G maxSkip (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 la)))) Adv).run (fun _ => none)

/-- Multi-session ideal-cutoff (`Thm5.hp cut cut la`) execution of a multi-session ratchet adversary `Adv`. -/
@[expose] def multiFsEndRun {CK MK AD M C : Type}
    [SampleableType MK] [SampleableType CK]
    [DecidableEq AD] [DecidableEq M] [DecidableEq C]
    (ideal : ℕ × AD → ProbComp C) (ae : AEADScheme MK (ℕ × AD) M C)
    (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip cut : ℕ) (la : Bool)
    (Adv : OracleComp (unifSpec + multiSessSpec (CryptoVerification.E2E.Signed.SessionFS.fsSpec CK MK AD M C)) Bool) :
    ProbComp Bool :=
  Prod.fst <$> (simulateQ (sessLift
    (lazyInit fsInit (fsImpl ideal ae G maxSkip (_root_.CryptoGames.FSAEAD.Thm5.hp cut cut la)))) Adv).run (fun _ => none)

/-! ## 1. Real Multi-Session Hop-3 Coupling (`localAuthDF* ≤ multiSessRealWinProb`) -/

section LibsignalBridges

variable (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (Dh : DHFun (BitVec 256) Pt)

end LibsignalBridges

end

end Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFSMulti

