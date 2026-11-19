/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeBase -- proof-setup: allow-public-import
import Computational.Proofs.SessionCostedFig8.ProgSizeBounds
import Computational.Proofs.SessionCostedFig8.BucketFSAuthZeroQueries
import Computational.Proofs.SessionCostedFig8.BucketFSAuthCostA
import Computational.Proofs.SessionCostedFig8.BucketFSAuthShort
import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopHalt
import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopSplit

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHop

public section

open scoped ENNReal
open OracleSpec OracleComp
open _root_.CryptoGames (Party)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.CKA (DHFun)
open _root_.CryptoGames.FSAEAD (MakesAtMostQueries RatchetSenderState RatchetReceiverState)
open _root_.CryptoGames.FSAEAD.Thm5 (hp)
open _root_.CryptoGames.SM.Construction (Header healEpoch fsaeadMultiHeaderAdIface)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart LibsignalCiphertextWithSalt32
  dummyKey lChainPRG lAeadR lIdeal GuardedFSInjectShort)
open _root_.CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C)
open _root_.CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey SignalMessageProtoCodec
  maxForwardJumps)
open _root_.CryptoVerification.E2E.Signed.SessionRouter (sessLift lazyInit)
open _root_.CryptoVerification.E2E.Signed.SessionFS (fsInit fsImpl)
open _root_.CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open _root_.CryptoVerification.LibsignalSession (FsAdv fsCostedRedsInst
  fsAuthCompBoundMix fsAuthPrgMix fsAuthSWMix fsAuthCompBoundWith
  macForgeryTerm ratchetCostBudget GRedBounded)
open Computational.Proofs.ReductionDsl.FsAtomicMacros (atomicShortB)
open Computational.Proofs.E2E.SessionAuthBridge (authHopCutoff MultiSessFsAdv
  multiSessPubToAD TwoModeMultiSessBounds RouterAdvCompat)
open _root_.ReductionDsl (CostedReduction fsaeadHeaderIface fig8SmCodec atomicFig8Ops
  bits reductionSizeBudget)
open _root_.CryptoGames.CKA (dhScheme)
open _root_.CryptoGames.PRFPRNG (prngSMCodec)
open _root_.CryptoGames.Ratchet (rootPRNG)
open _root_.CryptoGames.Ratchet.LibsignalInst (lFS)
open Computational.Proofs.ReductionDsl.PureAuxMacroLift (compCostW)
open Computational.Proofs.ReductionDsl.Fig8Atomic (dhSchemeFb atomicShortPubB
  atomicShortPubB_imp_shortB fsAtomicB)
open Computational.Proofs.ReductionDsl.Fig8ExcessCosts (ckaOpC ckaSampC)
open Computational.Proofs.ReductionDsl.Fig8WeightedParts (fig8AtomicStepBound)
open Computational.Proofs.ReductionDsl.SizeBudgetBridge (bits_mono bits_pos bits_succ_le)
open Computational.Proofs.SessionCostedFig8.BundlesCompilers (fig8CkaOpsShallow)
open Computational.Proofs.SessionCostedFig8.BundlesAuxSize (compSizeW ckaOpS ckaSampS)
open Computational.Proofs.SessionCostedFig8.BundlesMultiFs (compileFsMultiAtomic
  compileFsMultiAtomic_gRedBounded compileFsMultiAtomic_routerAdvCompat
  compileFsMultiAtomic_isQueryBoundP compileFsMultiAtomic_makesAtMostQueries
  compileFsMultiAtomic_encMsgsOk compileFsMultiAtomic_guardedFSInjectShort
  fsMultiQueryC fsMultiQueryS)
open Computational.Proofs.SessionCostedFig8.TopAssembly (multiSessRealWinProb
  multiSessEndWinProb bucket_four_branch_fs_le)
open Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth (redFSAuthMultiBucketProg
  redFSAuthMultiBucketProg_totalQueries localAuthBucketMain localAuthBucketForgedHdr
  localAuthBucketMainPar localAuthBucketForgedHdrPar localAuthBucketMain_le_par_false_add_true
  localAuthBucketForgedHdr_le_par_false_add_true)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeBase (BucketFsOk fsAeadAuthMixtureCompBound_inst_eq_zero_of_zero_queries fsAuthCompBoundMix_eq_zero_of_zero_queries fsAuthCompBoundWith_inst_eq_zero_of_zero_queries fsAuthPrgMix_eq_zero_of_zero_queries fsAuthSWMix_eq_zero_of_zero_queries healEpoch_le_of_forall_some optGetD_le_of_forall_some redFSAuthMultiBucketAtomic_decQueries redFSAuthMultiBucketAtomic_encAtomicShort_and_eqPub redFSAuthMultiBucketAtomic_fsOk_and_encAtomicShort redFSAuthMultiBucketAtomic_gRedBounded redFSAuthMultiBucketAtomic_guardedFSInjectShort redFSAuthMultiBucketAtomic_inactive_fsAeadAuthMixtureCompBound_eq_zero redFSAuthMultiBucketAtomic_inactive_fsAuthCompBoundWith_eq_zero redFSAuthMultiBucketAtomic_inactive_makesAtMostQueries_zero redFSAuthMultiBucketAtomic_makesAtMostQueries redFSAuthMultiBucketAtomic_oneADClass redFSAuthMultiBucketAtomic_routerAdvCompat redFSAuthMultiBucketProg_inactive_isQueryBoundP_zero redFSAuthMultiBucketProg_parts_le redFSAuthMultiBucketProg_sess_isQueryBoundP redFSAuthMultiBucketProg_size_le redFSAuthMultiBucketProg_twoModeMultiSessBounds redFSAuthMultiBucketShallow redFSAuthMultiBucketShallow_decQueries redFSAuthMultiBucketShallow_noCr redFSAuthMultiBucketShallow_totalQueries)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopSplit (
  localAuthBucketMainPar_le_multiSessRealWinProb_split)

theorem localAuthBucketMainPar_le_multiSessRealWinProb
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (hD : ∀ k x, C.D k (C.E k x) = x)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (hℓ : ℓ < 10 ^ 6) (q B0 qep : ℕ)
    (hB0 : B0 = (q + 1) * (maxForwardJumps + 1))
    (tL : Option ℕ) (par : Bool)
    (A : OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (hq : CryptoGames.SM.MakesAtMostQueries A q)
    (hsh : CryptoGames.LibsignalSM.Proofs.SessionShort.FSAEADRed.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    let AdvBr := fun la =>
      multiSessPubToAD protoSignalCodec
        ((redFSAuthMultiBucketShallow ℓ Pt C Dh encPt encT idOf lam (q + 1) B0 qep
            true la tL par).eval (fun _ => A) ())
    𝒟[localAuthBucketMainPar (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam 1 qep tL par A] {true} ≤
      multiSessRealWinProb C ℓ encT idOf AdvBr false +
        multiSessRealWinProb C ℓ encT idOf AdvBr true := by
  exact localAuthBucketMainPar_le_multiSessRealWinProb_split
    ℓ Pt C Dh hDh hD encPt encT hinj hdum idOf lam hℓ q B0 qep hB0 tL par A hq hsh

end

end Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHop
