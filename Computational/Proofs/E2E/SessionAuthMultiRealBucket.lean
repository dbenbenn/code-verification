/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFS -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeBucketPRNGDefs -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperBucketFS -- proof-setup: allow-public-import
public import Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2 -- proof-setup: allow-public-import
public import Computational.Proofs.HeadlineV1.DeliverForgePaperChallSim -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.Fig8Atomic -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SessionAuthBridge -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.TopAssembly -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperShiftedFS3 -- proof-setup: allow-public-import
import Computational.Proofs.E2E.SessionAuthLazy
import Computational.Proofs.E2E.SessionAuthFS
import Computational.Proofs.E2E.SessionAuthPubToAD
import Computational.Proofs.E2E.SessionAuthMultiPot
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.PubToAD
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.MsgAeadCorrect
import Computational.Proofs.CryptoGames.FSAEAD.Theorem5Start
import Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFSMultiBucketInactive
import Computational.Proofs.E2E.SessionAuthMultiRealBucketSplit

public import Computational.Proofs.E2E.SessionAuthMultiRealBase -- proof-setup: allow-public-import

/-!
# Real Multi-Session Hop-3 Coupling (`localAuthDF* ≤ multiSessRealWinProb`)

Couples the post-PRNG local games of the Stage-2 `DeliverForgePaper` families
(`localAuthDFShiftedDir2Paper`, `localAuthDFShiftedPaper`, `AuthL11.localAuthDFPaper`, and
`localAuthDFPaperBucketRaw`) to the two-mode (`la = false` + `la = true`) real multi-session
`FSMultiSpec` experiments (`multiSessRealWinProb`).-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Computational.Proofs.E2E.SessionAuthMultiReal

public section

open scoped ENNReal MeasureTheory
open OracleSpec OracleComp
open _root_.CryptoGames (Party CKAScheme PRFPRNG FSAEADScheme AEADScheme)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.CKA (DHFun dhScheme)
open _root_.CryptoGames.Ratchet (rootPRNG)
open _root_.CryptoGames.SM (GameState Pos Record RecvResult Config healedBy ltOpt maxOpt
  canon lastLeakGuessAdmissible authLosingConditionsAvoided)
open _root_.CryptoGames.SM.Engine (VP EState Ctx vSend vRecv commitE
  deliverE injectE abortE coinsE)
open _root_.CryptoGames.SM.Construction (PartyState Header healEpoch realParty mkParties
  FSMultiBook FSMultiDFBucketState hooksFSMultiDFBucketPaper hooksFSMultiDFBucketPaperMode
  initFSMultiDFBucketPaper redFSAuthDFPaperMulti redFSAuthDFPaperMultiBucket
  redFSAuthDFPaperMultiBucketMode isHonestHdrFSMultiDFBucket regSessMultiDFBucket
  regSessOptMultiDFBucket lookupMultiDFBucketF rootFSMultiDFBucketPaper postLeakDFBucket
  inStage2BucketGen)
open _root_.CryptoGames.SM.Construction.DeliverForge (AdversaryDF SchemeAdversaryDF partyPar
  MakesAtMostQueriesDF bucketAuthCfg engRunDFPaperBucket engRunDFPaperBucketMode
  implEDFPaperBucket implEDFPaperBucketMode implEDFPaperBucketRaw withWinEpDF withWinEpDFMode
  transmitEBucket challEBucket corrEPaperBucket deliverForgeE authOutBucket authOutBucketPaper
  inStage2Bucket LocalBucketState hooksLocalBucket hooksLocalBucketMain hooksLocalBucketForgedHdr
  isHonestHdrLocalBucket initLocalBucket rootLocalBucket lookupLocalBucketF postLeak
  localAuthDFPaperBucketMode localAuthDFPaperBucketMain localAuthDFPaperBucketForgedHdr
  localAuthDFPaperBucketSplit localAuthDFShiftedDir2Paper localAuthDFShiftedPaper)
open _root_.CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey maxForwardJumps)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart LibsignalCiphertextWithSalt32
  dummyKey lFS lAead lAeadR lIdeal lPubOf lChainPRG)
open _root_.CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C)
open _root_.CryptoVerification.LibsignalProtoCodec (protoSignalCodec)

open _root_.CryptoVerification.LibsignalSession.HeadlineV1 (SendMsgsOkDF)
open Computational.Proofs.ReductionDsl.Fig8Atomic (atomicShortPubB atomicShortPubB_imp_shortB)
open _root_.CryptoVerification.E2E.Signed.SessionRouter (lazyInit sessLift multiSessSpec sessOffRange)
open _root_.CryptoVerification.E2E.Signed.SessionFS (fsInit fsImpl fsSpec)
open Computational.Proofs.E2E.SessionAuthBridge (multiSessPubToAD)
open Computational.Proofs.E2E.SessionAuthPubToAD (multiSessPubToAD_offRange)
open Computational.Proofs.SessionCostedFig8.TopAssembly (multiSessRealWinProb)
open Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2 (
  redFSAuthDFShiftedPaperMulti redFSAuthDFShiftedDir2PaperMulti)

section LibsignalBridges

variable (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (Dh : DHFun (BitVec 256) Pt)


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
        multiSessRealWinProb C ℓ encT idOf Adv true := by
  exact Computational.Proofs.E2E.SessionAuthMultiRealBucketSplit.localAuthDFPaperBucketRaw_le_multiSessRealWinProb_split
    ℓ Pt C Dh hD encPt encT hinj hdum idOf lam hℓ q qep tL par A hq hsh

/-- Mode-parameterized (`gMain : Bool`, `true` = `Main`, `false` = `ForgedHdr`) `(tL, par)`-bucket
post-PRNG local game bounded by the two-mode (`la = false` + `la = true`) `multiSessRealWinProb` of
`redFSAuthDFPaperMultiBucketMode`. -/
theorem localAuthDFPaperBucketMode_le_multiSessRealWinProb
    (hD : ∀ k x, C.D k (C.E k x) = x)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (idOf : Party → IdentityKey) (lam : Pt) (hℓ : ℓ < 10 ^ 6)
    (q qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par : Bool)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq : MakesAtMostQueriesDF A q)
    (hsh : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    let Adv := fun la =>
      multiSessPubToAD protoSignalCodec
        (redFSAuthDFPaperMultiBucketMode (q + 1) (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam 1 4 qep gMain la tL par A)
    𝒟[localAuthDFPaperBucketMode (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam 1 qep gMain tL par A] {true} ≤
      multiSessRealWinProb C ℓ encT idOf Adv false +
        multiSessRealWinProb C ℓ encT idOf Adv true := by
  exact Computational.Proofs.E2E.SessionAuthMultiRealBucketSplit.localAuthDFPaperBucketMode_le_multiSessRealWinProb_split
    ℓ Pt C Dh hD encPt encT hinj hdum idOf lam hℓ q qep gMain tL par A hq hsh


end LibsignalBridges

end

end Computational.Proofs.E2E.SessionAuthMultiReal
