/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Session.StatementComposed
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFSMulti -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.Fig8Atomic -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.DFProgFsStage2Defs

import Computational.Specifications.Session.StatementIdsModel
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFSMultiBucket
import Computational.Proofs.E2E.SessionAuthBridge
import Computational.Proofs.E2E.SessionAuthMultiEndBucket
import Computational.Proofs.E2E.SessionAuthMultiEndBucketPot
import Computational.Proofs.E2E.SessionAuthMultiRealBucket
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNERedsHop3BucketAux
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNERedsHop3BucketMode
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNERedsHop3BucketQuery
import Computational.Proofs.ReductionDsl.FsAtomicMacros
import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperBucketFS
import Computational.Proofs.SessionCostedFig8.BundlesCompilers
import Computational.Proofs.SessionCostedFig8.BundlesMultiFs
import Computational.Proofs.SessionCostedFig8.BundlesMultiFsBase
import Computational.Proofs.SessionCostedFig8.DFProgBucketBounds
import Computational.Proofs.SessionCostedFig8.TopAssembly
import Computational.Proofs.SessionCostedFs

set_option autoImplicit false

namespace Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNERedsHop3Bucket

public section

open scoped ENNReal
open OracleComp OracleSpec
open _root_.ReductionDsl (CostedReduction)
open _root_.CryptoGames (Party CKAScheme PRFPRNG FSAEADScheme)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.CKA (DHFun dhScheme)
open _root_.CryptoGames.PRFPRNG (prngOps prngSMCodecDF)
open _root_.CryptoGames.FSAEAD (EncMsgsOk MakesAtMostQueries RatchetReceiverState
  RatchetSenderState encBadMsg)
open _root_.CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey maxForwardJumps)
open _root_.CryptoVerification.LibsignalSession (FsAdv FsCostedReds fsAuthCompBoundWith
  fsCostedRedsInst macForgeryTerm)
open _root_.CryptoVerification.LibsignalSession.HeadlineV1 (GuardedSMDFShort SendMsgsOkDF
  badSendMsgDF)
open _root_.CryptoVerification.E2E (idsOf)
open _root_.CryptoGames.Ratchet (rootPRNG)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalCiphertextWithSalt32
  LibsignalMsgPublicPart dummyKey lFS)
open _root_.CryptoGames.SM (admissibleLastLeakGuesses specDF)
open _root_.CryptoGames.SM.Construction (FSMultiSpec Header PartyState fsaeadMultiHeaderAdIface
  healEpoch redFSAuthDFPaperMultiBucketMode redFSAuthDFPaperMultiBucketModeProg
  redFSAuthDFPaperMultiBucketModeProg_totalQueries sampleT)
open _root_.CryptoGames.SM.Construction.DeliverForge (AdversaryDF MakesAtMostQueriesDF
  localAuthDFPaperBucketForgedHdr localAuthDFPaperBucketMain localAuthDFPaperBucketMode)
open _root_.CryptoGames.Ratchet.LibsignalSim (Fig8C Fig8St)
open _root_.CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFSMulti
  (localAuthDFPaperBucket_main_add_forgedHdr_le_fsAuthCompBoundWith_of_branches
   localAuthDFPaperBucket_main_add_forgedHdr_le_fsAuthCompBoundWith_of_branches_min
   redFSAuthDFPaperMultiBucketMode_oneADClass_uniform
   redFSAuthDFPaperMultiBucketMode_twoModeMultiSessBounds)
open Computational.Proofs.E2E.SessionAuthBridge (RouterAdvCompat multiSessPubToAD)
open Computational.Proofs.E2E.SessionAuthMultiEnd
  (multiSessEndWinProb_redFSAuthDFPaperMultiBucketMode_eq_zero
   multiSessEndWinProb_redFSAuthDFPaperMultiBucketMode_eq_zero_min)
open Computational.Proofs.E2E.SessionAuthMultiEndBucketPot
  (redFSAuthDFPaperMultiBucketMode_sess_isQueryBoundP_min)
open Computational.Proofs.E2E.SessionAuthMultiReal
  (localAuthDFPaperBucketMode_le_multiSessRealWinProb)
open Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNERedsHop3BucketMode
  (redFSAuthDFPaperMultiBucketModeProg_eval_lFS)
open Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNERedsHop3BucketQuery
  (redFSAuthDFPaperMultiBucketModeGen_encBadMsg redFSAuthDFPaperMultiBucketModeGen_noCr)
open Computational.Proofs.ReductionDsl.Fig8Atomic (atomicShortPubB dhSchemeFb fsAtomicB)
open Computational.Proofs.ReductionDsl.FsAtomicMacros (atomicShortB)
open Computational.Proofs.SessionCostedFig8.BundlesCompilers (fig8CkaOpsShallow)
open Computational.Proofs.SessionCostedFig8.BundlesMultiFs (compileFsMultiDFAtomic
  compileFsMultiDFAtomic_encMsgsOk compileFsMultiDFAtomic_isQueryBoundP
  compileFsMultiDFAtomic_routerAdvCompat)
open Computational.Proofs.SessionCostedFig8.DFProgBucketBounds (dummyFsStage2AtomicProg)
open Computational.Proofs.SessionCostedFig8.DFProgFsStage2Defs
  (ckaCoinBranchDFRed ckaCoinBranchDFRed_eval_sampleT ckaCoinBranchDFRed_isQueryBoundP
   redFSAuthDFPaperMultiBucketAtomicProg redFSAuthDFPaperMultiBucketAtomicProg_eq_compile)

private theorem fsAuthCompBoundWith_eq_fsAeadAuthSlotSumBound
    {Pt : Type} [DecidableEq Pt] (C : Crypto) (ℓ : ℕ)
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey} (qR : ℕ)
    (R : FsCostedReds C protoSignalCodec ℓ encT idOf)
    (A : Bool → Bool → FsAdv Pt ℓ) :
    fsAuthCompBoundWith C protoSignalCodec ℓ qR R A =
      CryptoVerification.E2E.fsAeadAuthSlotSumBound C qR R A := by
  unfold fsAuthCompBoundWith CryptoVerification.E2E.fsAeadAuthSlotSumBound
  refine congrArg (2 * ·) (Finset.sum_congr rfl fun _ _ => ?_)
  dsimp only
  rw [add_assoc]

private theorem admissibleLastLeakGuesses_four_some_le {N : ℕ} {tL : Option ℕ}
    (htL : tL ∈ admissibleLastLeakGuesses 4 (N + 1)) :
    ∀ x, tL = some x → x ≤ N + 3 := by
  simp only [admissibleLastLeakGuesses, Finset.mem_insert, Finset.mem_image, Finset.mem_range] at htL
  rintro x rfl
  rcases htL with h | ⟨l, hl, h⟩
  · cases h
  · cases h
    omega

private theorem sum_Ico_min_le_B_fs_u_sum
    {R Adv : Type} (tL : Option ℕ) (q qep : ℕ)
    (evalR : R → Adv)
    (B : (Bool → Bool → Adv) → ℝ≥0∞)
    (P : Bool → Bool → ℕ → R) (D : R) :
    ∑ t ∈ Finset.Ico (healEpoch tL) (min (qep + 1) (q + 11) + 2),
      ∑ j ∈ Finset.range q,
        B (fun stage la => evalR (P stage la (q * (t - healEpoch tL) + j))) ≤
    ∑ t ∈ Finset.Ico (healEpoch tL) ((qep + 1) + 2),
      ∑ j ∈ Finset.range q,
        B (fun stage la =>
          evalR (if healEpoch tL ≤ t ∧ t ≤ min (qep + 1) (q + 11) + 3 ∧ j < q then
            P stage la (q * (t - healEpoch tL) + j)
          else
            D)) := by
  calc
    _ = ∑ t ∈ Finset.Ico (healEpoch tL) (min (qep + 1) (q + 11) + 2),
          ∑ j ∈ Finset.range q,
            B (fun stage la =>
              evalR (if healEpoch tL ≤ t ∧ t ≤ min (qep + 1) (q + 11) + 3 ∧ j < q then
                P stage la (q * (t - healEpoch tL) + j)
              else
                D)) := by
      refine Finset.sum_congr rfl fun t ht => Finset.sum_congr rfl fun j hj => ?_
      simp only [Finset.mem_Ico, Finset.mem_range] at ht hj
      have hcond : healEpoch tL ≤ t ∧ t ≤ min (qep + 1) (q + 11) + 3 ∧ j < q :=
        ⟨ht.1, by omega, hj⟩
      congr 1; funext stage; funext la
      rw [ite_eq_left_iff.mpr fun h => absurd hcond h]
    _ ≤ _ :=
      Finset.sum_le_sum_of_subset (fun t ht => by
        simp only [Finset.mem_Ico] at ht ⊢
        exact ⟨ht.1, by omega⟩)

private theorem localAuthDFPaperBucketMode_true_eq_main
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool)
    (A : AdversaryDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) :
    localAuthDFPaperBucketMode cka prng fs lam Δcka qep true tL par A =
      localAuthDFPaperBucketMain cka prng fs lam Δcka qep tL par A := by
  unfold localAuthDFPaperBucketMode localAuthDFPaperBucketMain
  rfl

private theorem localAuthDFPaperBucketMode_false_eq_forgedHdr
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool)
    (A : AdversaryDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)) :
    localAuthDFPaperBucketMode cka prng fs lam Δcka qep false tL par A =
      localAuthDFPaperBucketForgedHdr cka prng fs lam Δcka qep tL par A := by
  unfold localAuthDFPaperBucketMode localAuthDFPaperBucketForgedHdr
  rfl

private theorem redFSAuthDFPaperMultiBucketModeProg_eq_beq
    {Pt : Type} [DecidableEq Pt] [SampleableType Pt]
    (ℓ : ℕ) (Z : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (L B0 qep maxSkip : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) :
    (redFSAuthDFPaperMultiBucketModeProg
        (KR := BitVec 256) (RSt := BitVec 256) (K := BitVec 256)
        (ckaInitA := (dhSchemeFb Dh).initA) (ckaInitB := (dhSchemeFb Dh).initB)
        (ckaSend := (dhSchemeFb Dh).send) (ckaReceive := (dhSchemeFb Dh).receive)
        (prngInit := (rootPRNG Z.F encPt).init) (prngUp := (rootPRNG Z.F encPt).up)
        (fsInitSender := (fsAtomicB Z ℓ encT idOf B0).initSender)
        (fsInitReceiver := (fsAtomicB Z ℓ encT idOf B0).initReceiver)
        (fsSend := (fsAtomicB Z ℓ encT idOf B0).send)
        (fsReceive := (fsAtomicB Z ℓ encT idOf B0).receive)
        (eqT := (· == ·)) (eqI := (· == ·))
        (eqM := @BEq.beq (LibsignalMsgPublicPart × Plain ℓ) instBEqOfDecidableEq)
        (eqE := @BEq.beq (ℕ × LibsignalCiphertextWithSalt32) instBEqOfDecidableEq)
        (lam := lam) (defaultE := default)
        (sampKR := ($ᵗ (BitVec 256))) (sampKC := ($ᵗ (BitVec 256)))
        (sampCCoins := ($ᵗ (BitVec 256))) (sampI := ($ᵗ Pt)) (sampK := ($ᵗ (BitVec 256)))
        L B0 1 4 qep maxSkip gMain la tL par).eval (fun _ => A) () =
      (redFSAuthDFPaperMultiBucketModeProg
        (KR := BitVec 256) (RSt := BitVec 256) (K := BitVec 256)
        (ckaInitA := (dhSchemeFb Dh).initA) (ckaInitB := (dhSchemeFb Dh).initB)
        (ckaSend := (dhSchemeFb Dh).send) (ckaReceive := (dhSchemeFb Dh).receive)
        (prngInit := (rootPRNG Z.F encPt).init) (prngUp := (rootPRNG Z.F encPt).up)
        (fsInitSender := (fsAtomicB Z ℓ encT idOf B0).initSender)
        (fsInitReceiver := (fsAtomicB Z ℓ encT idOf B0).initReceiver)
        (fsSend := (fsAtomicB Z ℓ encT idOf B0).send)
        (fsReceive := (fsAtomicB Z ℓ encT idOf B0).receive)
        (eqT := (· == ·)) (eqI := (· == ·)) (eqM := (· == ·)) (eqE := (· == ·))
        (lam := lam) (defaultE := default)
        (sampKR := ($ᵗ (BitVec 256))) (sampKC := ($ᵗ (BitVec 256)))
        (sampCCoins := ($ᵗ (BitVec 256))) (sampI := ($ᵗ Pt)) (sampK := ($ᵗ (BitVec 256)))
        L B0 1 4 qep maxSkip gMain la tL par).eval (fun _ => A) () := by
  have heqM_beq :
      (@BEq.beq (LibsignalMsgPublicPart × Plain ℓ) instBEqOfDecidableEq) = (· == ·) := by
    funext x1 x2
    exact Bool.eq_iff_iff.mpr (decide_eq_true_iff.trans beq_iff_eq.symm)
  have heqE_beq :
      (@BEq.beq (ℕ × LibsignalCiphertextWithSalt32) instBEqOfDecidableEq) = (· == ·) := by
    funext x1 x2
    exact Bool.eq_iff_iff.mpr (decide_eq_true_iff.trans beq_iff_eq.symm)
  exact congrArg₂
    (fun eqM_fn eqE_fn =>
      (redFSAuthDFPaperMultiBucketModeProg
        (KR := BitVec 256) (RSt := BitVec 256) (K := BitVec 256)
        (ckaInitA := (dhSchemeFb Dh).initA) (ckaInitB := (dhSchemeFb Dh).initB)
        (ckaSend := (dhSchemeFb Dh).send) (ckaReceive := (dhSchemeFb Dh).receive)
        (prngInit := (rootPRNG Z.F encPt).init) (prngUp := (rootPRNG Z.F encPt).up)
        (fsInitSender := (fsAtomicB Z ℓ encT idOf B0).initSender)
        (fsInitReceiver := (fsAtomicB Z ℓ encT idOf B0).initReceiver)
        (fsSend := (fsAtomicB Z ℓ encT idOf B0).send)
        (fsReceive := (fsAtomicB Z ℓ encT idOf B0).receive)
        (eqT := (· == ·)) (eqI := (· == ·)) (eqM := eqM_fn) (eqE := eqE_fn)
        (lam := lam) (defaultE := default)
        (sampKR := ($ᵗ (BitVec 256))) (sampKC := ($ᵗ (BitVec 256)))
        (sampCCoins := ($ᵗ (BitVec 256))) (sampI := ($ᵗ Pt)) (sampK := ($ᵗ (BitVec 256)))
        L B0 1 4 qep maxSkip gMain la tL par).eval (fun _ => A) ())
    heqM_beq heqE_beq

private theorem localAuthDFPaperBucket_main_add_forgedHdr_le_qepC_sum_min
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (Z : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (hDh : Dh.Commutes)
    (hD : ∀ k x, Z.D k (Z.E k x) = x)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (idA idB : IdentityKey) (lam : Pt)
    (hℓ : ℓ < 10 ^ 6) (q qep : ℕ)
    (hq32 : 2 * q + 25002 < 2 ^ 32)
    (tL : Option ℕ) (htL_clamp : ∀ x, tL = some x → x ≤ min (qep + 1) (q + 11) + 3) (par : Bool)
    (challAdvDF : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq_ch : MakesAtMostQueriesDF challAdvDF q)
    (hsh_ch : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) challAdvDF)
    (hg_ch : GuardedSMDFShort challAdvDF) :
    𝒟[localAuthDFPaperBucketMode (dhScheme Dh) (rootPRNG Z.F encPt)
        (lFS Z protoSignalCodec ℓ encT (idsOf idA idB) 25000) lam 1 (qep + 1) true tL par challAdvDF] {true} +
      𝒟[localAuthDFPaperBucketMode (dhScheme Dh) (rootPRNG Z.F encPt)
        (lFS Z protoSignalCodec ℓ encT (idsOf idA idB) 25000) lam 1 (qep + 1) false tL par challAdvDF] {true} ≤
      (∑ t ∈ Finset.Ico (healEpoch tL) (min (qep + 1) (q + 11) + 2),
        ∑ j ∈ Finset.range q,
          CryptoVerification.E2E.fsAeadAuthSlotSumBound Z (min (2 * q) (q + 2))
            (fsCostedRedsInst Z protoSignalCodec ℓ encT (idsOf idA idB) (min (2 * q) (q + 2)))
            (fun stage la =>
              (redFSAuthDFPaperMultiBucketAtomicProg ℓ Pt Z Dh encPt encT (idsOf idA idB) lam
                stage la (q * (t - healEpoch tL) + j) (min (2 * q) (q + 2)) q (qep + 1) tL par).eval
                (fun _ => challAdvDF) ())) +
      4 * macForgeryTerm Z q := by
  let _ := hDh
  let idOf := idsOf idA idB
  let B0 := (q + 1) * (maxForwardJumps + 1)
  let qepC := min (qep + 1) (q + 11)
  let qR := min (2 * q) (q + 2)
  have hms25000 : (25000 : ℕ) = maxForwardJumps := rfl
  rw [hms25000,
    Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNERedsHop3BucketAux.localAuthDFPaperBucketMode_eq_min_qep
      (dhScheme Dh) (rootPRNG Z.F encPt) (lFS Z protoSignalCodec ℓ encT idOf maxForwardJumps)
      lam 1 q qep true tL par challAdvDF hq_ch,
    Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNERedsHop3BucketAux.localAuthDFPaperBucketMode_eq_min_qep
      (dhScheme Dh) (rootPRNG Z.F encPt) (lFS Z protoSignalCodec ℓ encT idOf maxForwardJumps)
      lam 1 q qep false tL par challAdvDF hq_ch]
  obtain ⟨R_mode, hR_mode⟩ :
      ∃ R_mode : Bool → Bool → CostedReduction (fig8CkaOpsShallow ℓ Pt Z Dh encPt encT idOf lam B0)
        (fsaeadMultiHeaderAdIface (BitVec 256) (_root_.CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
        (specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
        (prngSMCodecDF (BitVec 256) (_root_.CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
        .unit .unit .bool .bool,
      ∀ gMain la, R_mode gMain la =
        redFSAuthDFPaperMultiBucketModeProg (q + 1) B0 1 4 qepC maxForwardJumps gMain la tL par :=
    ⟨_, fun _ _ => rfl⟩
  let R_coin := fun la : Bool =>
    ckaCoinBranchDFRed ℓ Pt Z Dh encPt encT idOf lam B0 (R_mode true la) (R_mode false la)
  let RBr := fun gMain la : Bool =>
    redFSAuthDFPaperMultiBucketMode (q + 1) (dhScheme Dh) (rootPRNG Z.F encPt)
      (lFS Z protoSignalCodec ℓ encT idOf maxForwardJumps) lam 1 4 qepC gMain la tL par challAdvDF
  let F : Bool → Bool → ℕ → ℕ → FsAdv Pt ℓ := fun stage la j t =>
    (redFSAuthDFPaperMultiBucketAtomicProg ℓ Pt Z Dh encPt encT idOf lam
      stage la (q * (t - healEpoch tL) + j) qR q (qep + 1) tL par).eval
      (fun _ => challAdvDF) ()
  have hActive : ∀ stage la idx,
      redFSAuthDFPaperMultiBucketAtomicProg ℓ Pt Z Dh encPt encT idOf lam
        stage la idx qR q (qep + 1) tL par =
      compileFsMultiDFAtomic ℓ Pt Z Dh encPt encT idOf lam stage la idx qepC qR B0 (R_coin la) := by
    intro stage la idx
    dsimp only [R_coin, qR]
    rw [hR_mode true la, hR_mode false la]
    exact redFSAuthDFPaperMultiBucketAtomicProg_eq_compile ℓ Pt Z Dh encPt encT idOf lam
      stage la idx (min (2 * q) (q + 2)) q (qep + 1) tL par htL_clamp (by omega)
  have hEvalMode : ∀ gMain la, (R_mode gMain la).eval (fun _ => challAdvDF) () = RBr gMain la := by
    intro gMain la
    have hEqEval :
        (R_mode gMain la).eval (fun _ => challAdvDF) () =
        (redFSAuthDFPaperMultiBucketModeProg
          (ckaInitA := (dhSchemeFb Dh).initA) (ckaInitB := (dhSchemeFb Dh).initB)
          (ckaSend := (dhSchemeFb Dh).send) (ckaReceive := (dhSchemeFb Dh).receive)
          (prngInit := (rootPRNG Z.F encPt).init) (prngUp := (rootPRNG Z.F encPt).up)
          (fsInitSender := (fsAtomicB Z ℓ encT idOf B0).initSender)
          (fsInitReceiver := (fsAtomicB Z ℓ encT idOf B0).initReceiver)
          (fsSend := (fsAtomicB Z ℓ encT idOf B0).send)
          (fsReceive := (fsAtomicB Z ℓ encT idOf B0).receive)
          (eqT := (· == ·)) (eqI := (· == ·)) (eqM := (· == ·)) (eqE := (· == ·))
          (lam := lam) (defaultE := default)
          (sampKR := ($ᵗ (BitVec 256))) (sampKC := ($ᵗ (BitVec 256)))
          (sampCCoins := ($ᵗ (BitVec 256))) (sampI := ($ᵗ Pt)) (sampK := ($ᵗ (BitVec 256)))
          (q + 1) B0 1 4 qepC maxForwardJumps gMain la tL par).eval (fun _ => challAdvDF) () := by
      rw [hR_mode gMain la]
      exact redFSAuthDFPaperMultiBucketModeProg_eq_beq ℓ Z Dh encPt encT idOf lam
        (q + 1) B0 qepC maxForwardJumps gMain la tL par challAdvDF
    exact hEqEval.trans (redFSAuthDFPaperMultiBucketModeProg_eval_lFS ℓ Z Dh encPt encT idOf lam
      q B0 qepC gMain la tL par rfl challAdvDF hq_ch hsh_ch)
  have hEvalCoin : ∀ la, (R_coin la).eval (fun _ => challAdvDF) () =
      (sampleT Bool >>= fun gMain => RBr gMain la) := by
    intro la
    rw [ckaCoinBranchDFRed_eval_sampleT ℓ Pt Z Dh encPt encT idOf lam B0
      (R_mode true la) (R_mode false la) (fun _ => challAdvDF) ()]
    congr 1; funext gMain; cases gMain <;> simp [hEvalMode]
  have hSessQ_mode : ∀ gMain la s,
      ((R_mode gMain la).eval (fun _ => challAdvDF) ()).IsQueryBoundP
        (fun x => (match x with | .inl _ => false | .inr ⟨s', _⟩ => decide (s' = s)) = true) qR := by
    intro gMain la s
    rw [hEvalMode gMain la]
    dsimp only [RBr, qR]
    exact (redFSAuthDFPaperMultiBucketMode_sess_isQueryBoundP_min (q + 1) (dhScheme Dh)
      (rootPRNG Z.F encPt) (lFS Z protoSignalCodec ℓ encT idOf maxForwardJumps) lam q 1 4 qepC
      gMain tL par la challAdvDF hq_ch s).of_imp
      (fun x hx => by rcases x with _ | ⟨_, _⟩ <;> exact hx)
  have hSessQ_coin : ∀ la s,
      ((R_coin la).eval (fun _ => challAdvDF) ()).IsQueryBoundP
        (fun x => (match x with | .inl _ => false | .inr ⟨s', _⟩ => decide (s' = s)) = true) qR :=
    fun la s =>
      ckaCoinBranchDFRed_isQueryBoundP ℓ Pt Z Dh encPt encT idOf lam B0
        (R_mode true la) (R_mode false la) (fun _ => challAdvDF) () _ qR
        (fun _ => by simp) (hSessQ_mode true la s) (hSessQ_mode false la s)
  have hNoCr_mode : ∀ gMain la,
      ((R_mode gMain la).eval (fun _ => challAdvDF) ()).IsQueryBoundP
        (fun x => (match x with | .inr ⟨_, .inl (.inl (.inr _))⟩ => true | _ => false) = true) 0 := by
    intro gMain la
    rw [hEvalMode gMain la]
    dsimp only [RBr, redFSAuthDFPaperMultiBucketMode]
    exact (redFSAuthDFPaperMultiBucketModeGen_noCr (q + 1) (dhScheme Dh) (rootPRNG Z.F encPt)
      (lFS Z protoSignalCodec ℓ encT idOf maxForwardJumps) lam 1 4 qepC gMain la tL par challAdvDF).of_imp
      (fun x hx => by rcases x with _ | ⟨_, ((_ | _) | _) | _⟩ <;> exact hx)
  have hNoCr_coin : ∀ la,
      ((R_coin la).eval (fun _ => challAdvDF) ()).IsQueryBoundP
        (fun x => (match x with | .inr ⟨_, .inl (.inl (.inr _))⟩ => true | _ => false) = true) 0 :=
    fun la =>
      ckaCoinBranchDFRed_isQueryBoundP ℓ Pt Z Dh encPt encT idOf lam B0
        (R_mode true la) (R_mode false la) (fun _ => challAdvDF) () _ 0
        (fun _ => by simp) (hNoCr_mode true la) (hNoCr_mode false la)
  have hShort_mode : ∀ gMain la s,
      ((R_mode gMain la).eval (fun _ => challAdvDF) ()).IsQueryBoundP
        (fun x => (match x with
          | .inl _ => false
          | .inr ⟨s', qv⟩ => decide (s' = s) &&
              encBadMsg (SS := RatchetSenderState (BitVec 256))
                (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
                (AD := Header Pt) (C := ℕ × LibsignalCiphertextWithSalt32)
                (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) (.inr qv)) = true) 0 := by
    intro gMain la s
    rw [hEvalMode gMain la]
    exact redFSAuthDFPaperMultiBucketModeGen_encBadMsg Z Dh encPt encT idOf lam
      (q + 1) ℓ 1 4 qepC gMain la tL par s challAdvDF hsh_ch
  have hShort_coin : ∀ la s,
      ((R_coin la).eval (fun _ => challAdvDF) ()).IsQueryBoundP
        (fun x => (match x with
          | .inl _ => false
          | .inr ⟨s', qv⟩ => decide (s' = s) &&
              encBadMsg (SS := RatchetSenderState (BitVec 256))
                (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
                (AD := Header Pt) (C := ℕ × LibsignalCiphertextWithSalt32)
                (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) (.inr qv)) = true) 0 :=
    fun la s =>
      ckaCoinBranchDFRed_isQueryBoundP ℓ Pt Z Dh encPt encT idOf lam B0
        (R_mode true la) (R_mode false la) (fun _ => challAdvDF) () _ 0
        (fun _ => by simp) (hShort_mode true la s) (hShort_mode false la s)
  have hMB0 : ((qepC + 2) - healEpoch tL) * q ≤ (qepC + 2) * B0 + B0 * B0 + 1 := by
    have hqB0 : q ≤ B0 := by dsimp only [B0]; unfold maxForwardJumps; omega
    have hmul : ((qepC + 2) - healEpoch tL) * q ≤ (qepC + 2) * B0 :=
      Nat.mul_le_mul (Nat.sub_le _ _) hqB0
    omega
  have hqR_B0 : qR ≤ B0 := by dsimp only [qR, B0]; unfold maxForwardJumps; omega
  have hCompat0 := compileFsMultiDFAtomic_routerAdvCompat ℓ Pt Z Dh encPt encT
    (pure ()) (fun _ => idOf) (fun _ => lam) hℓ hinj qepC qR (((qepC + 2) - healEpoch tL) * q) B0
    hMB0 hqR_B0
    (fun la _ _ => R_coin la) (fun _ => challAdvDF)
    (fun la _ _ s => ((hSessQ_coin la s).mono (by dsimp only [qR]; omega)).of_imp
      (fun x hx => by rcases x with _ | ⟨_, _⟩ <;> exact hx))
    (fun la _ _ => (hNoCr_coin la).of_imp
      (fun x hx => by rcases x with _ | ⟨_, ((_ | _) | _) | _⟩ <;> exact hx))
    (fun la _ _ s => (hShort_coin la s).of_imp
      (fun x hx => by rcases x with _ | ⟨_, _⟩ <;> exact hx))
  have hAdvEq :
      (fun la (_ : Unit) => multiSessPubToAD protoSignalCodec ((R_coin la).eval (fun _ => challAdvDF) ())) =
      (fun la (_ : Unit) => multiSessPubToAD protoSignalCodec (sampleT Bool >>= fun gMain => RBr gMain la)) := by
    funext la _; rw [hEvalCoin la]
  have hSlotEq :
      (fun stage la idx (_ : Unit) =>
        (compileFsMultiDFAtomic ℓ Pt Z Dh encPt encT idOf lam stage la idx qepC qR B0
          (R_coin la)).eval (fun _ => challAdvDF) ()) =
      (fun stage la idx (_ : Unit) => F stage la (idx % q) (healEpoch tL + idx / q)) := by
    funext stage la idx _
    dsimp only [F]
    rw [Nat.add_sub_cancel_left, Nat.div_add_mod, hActive stage la idx]
  have hCompat : RouterAdvCompat Z protoSignalCodec ℓ encT (pure ()) (fun _ => idOf)
      maxForwardJumps qR (((qepC + 2) - healEpoch tL) * q)
      (fun la (_ : Unit) => multiSessPubToAD protoSignalCodec (sampleT Bool >>= fun gMain => RBr gMain la))
      (fun stage la idx _ => F stage la (idx % q) (healEpoch tL + idx / q)) := by
    simpa only [hAdvEq, hSlotEq] using hCompat0
  have hF_q : ∀ j < q, ∀ t ∈ Finset.Ico (healEpoch tL) (qepC + 2), ∀ stage la,
      MakesAtMostQueries (F stage la j t) qR := by
    intro j _ t _ stage la
    dsimp only [F]
    rw [hActive stage la (q * (t - healEpoch tL) + j)]
    have hQ := compileFsMultiDFAtomic_isQueryBoundP ℓ Pt Z Dh encPt encT idOf lam
      stage la (q * (t - healEpoch tL) + j) qepC qR B0 (R_coin la) challAdvDF
      (fun _ => true) qR
      ((hSessQ_coin la (q * (t - healEpoch tL) + j)).of_imp
        (fun x hx => by rcases x with _ | ⟨_, _⟩ <;> simp only [Bool.and_true] at hx <;> exact hx))
    exact hQ.of_imp fun x hx => by cases x <;> exact hx
  have hF_sh : ∀ j < q, ∀ t ∈ Finset.Ico (healEpoch tL) (qepC + 2), ∀ stage la,
      EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) (F stage la j t) := by
    intro j _ t _ stage la
    dsimp only [F]
    rw [hActive stage la (q * (t - healEpoch tL) + j)]
    exact compileFsMultiDFAtomic_encMsgsOk ℓ Pt Z Dh encPt encT idOf lam
      stage la (q * (t - healEpoch tL) + j) qepC qR B0 (R_coin la) challAdvDF
      (fun m => atomicShortB m.1)
      ((hShort_coin la (q * (t - healEpoch tL) + j)).of_imp
        (fun x hx => by rcases x with _ | ⟨_, _⟩ <;> exact hx))
  have hbdsT := redFSAuthDFPaperMultiBucketMode_twoModeMultiSessBounds ℓ Pt Z Dh encPt encT idOf lam hℓ
    q 1 4 qepC (by omega) true tL par challAdvDF hq_ch hsh_ch hg_ch
  have hbdsF := redFSAuthDFPaperMultiBucketMode_twoModeMultiSessBounds ℓ Pt Z Dh encPt encT idOf lam hℓ
    q 1 4 qepC (by omega) false tL par challAdvDF hq_ch hsh_ch hg_ch
  have hMain :=
    localAuthDFPaperBucket_main_add_forgedHdr_le_fsAuthCompBoundWith_of_branches_min
      ℓ Pt Z Dh encPt encT hinj hdum idOf lam hℓ q qepC hq32 tL par challAdvDF RBr F
      (localAuthDFPaperBucketMode_le_multiSessRealWinProb ℓ Pt Z Dh hD encPt encT hinj hdum
        idOf lam hℓ q qepC true tL par challAdvDF hq_ch hsh_ch)
      (localAuthDFPaperBucketMode_le_multiSessRealWinProb ℓ Pt Z Dh hD encPt encT hinj hdum
        idOf lam hℓ q qepC false tL par challAdvDF hq_ch hsh_ch)
      ⟨hbdsT.1, hbdsT.2, hbdsT.3, hbdsT.4, hbdsT.5⟩
      ⟨hbdsF.1, hbdsF.2, hbdsF.3, hbdsF.4, hbdsF.5⟩
      (redFSAuthDFPaperMultiBucketMode_oneADClass_uniform ℓ Pt Z Dh encPt encT idOf lam
        q 1 4 qepC (by omega) tL par challAdvDF hq_ch hsh_ch)
      hCompat hF_q hF_sh
      (fun gMain la => multiSessEndWinProb_redFSAuthDFPaperMultiBucketMode_eq_zero_min
        ℓ Pt Z Dh encPt encT idOf lam q qR 1 4 qepC gMain tL par la (by omega)
        challAdvDF hq_ch le_rfl)
  rw [localAuthDFPaperBucketMode_true_eq_main, localAuthDFPaperBucketMode_false_eq_forgedHdr]
  simpa only [fsAuthCompBoundWith_eq_fsAeadAuthSlotSumBound] using hMain

/-- Direct `v1SessionRedsPaper.B_fs_u` corollary at `qR = min (2 * q) (q + 2)` (zero `hqep`). -/
theorem localAuthDFPaperBucket_main_add_forgedHdr_le_B_fs_u_sum_min
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (Z : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (hDh : Dh.Commutes)
    (hD : ∀ k x, Z.D k (Z.E k x) = x)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (idA idB : IdentityKey) (lam : Pt)
    (hℓ : ℓ < 10 ^ 6) (q qep : ℕ)
    (hq32 : 2 * q + 25002 < 2 ^ 32)
    (tL : Option ℕ) (htL : tL ∈ admissibleLastLeakGuesses 4 ((qep + 1) + 1)) (par : Bool)
    (challAdvDF : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq_ch : MakesAtMostQueriesDF challAdvDF q)
    (hsh_ch : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) challAdvDF)
    (hg_ch : GuardedSMDFShort challAdvDF) :
    𝒟[localAuthDFPaperBucketMode (dhScheme Dh) (rootPRNG Z.F encPt)
        (lFS Z protoSignalCodec ℓ encT (idsOf idA idB) 25000) lam 1 (qep + 1) true tL par challAdvDF] {true} +
      𝒟[localAuthDFPaperBucketMode (dhScheme Dh) (rootPRNG Z.F encPt)
        (lFS Z protoSignalCodec ℓ encT (idsOf idA idB) 25000) lam 1 (qep + 1) false tL par challAdvDF] {true} ≤
      (∑ t ∈ Finset.Ico (healEpoch tL) ((qep + 1) + 2),
        ∑ j ∈ Finset.range q,
          CryptoVerification.E2E.fsAeadAuthSlotSumBound Z (min (2 * q) (q + 2))
            (fsCostedRedsInst Z protoSignalCodec ℓ encT (idsOf idA idB) (min (2 * q) (q + 2)))
            (fun stage la =>
              (if healEpoch tL ≤ t ∧ t ≤ min (qep + 1) (q + 11) + 3 ∧ j < q then
                redFSAuthDFPaperMultiBucketAtomicProg ℓ Pt Z Dh encPt encT (idsOf idA idB) lam
                  stage la (q * (t - healEpoch tL) + j) (min (2 * q) (q + 2)) q (qep + 1) tL par
              else
                dummyFsStage2AtomicProg Dh encPt Z ℓ encT (idsOf idA idB) lam).eval
                (fun _ => challAdvDF) ())) +
      4 * macForgeryTerm Z q := by
  by_cases htL_clamp : ∀ x, tL = some x → x ≤ min (qep + 1) (q + 11) + 3
  · refine (localAuthDFPaperBucket_main_add_forgedHdr_le_qepC_sum_min
      ℓ Z Dh hDh hD encPt encT hinj hdum idA idB lam hℓ q qep hq32 tL htL_clamp par
      challAdvDF hq_ch hsh_ch hg_ch).trans
      (add_le_add ?_ le_rfl)
    exact sum_Ico_min_le_B_fs_u_sum tL q qep
      (fun R => R.eval (fun _ => challAdvDF) ())
      (fun A => CryptoVerification.E2E.fsAeadAuthSlotSumBound Z (min (2 * q) (q + 2))
        (fsCostedRedsInst Z protoSignalCodec ℓ encT (idsOf idA idB) (min (2 * q) (q + 2))) A)
      (fun stage la idx => redFSAuthDFPaperMultiBucketAtomicProg ℓ Pt Z Dh encPt encT (idsOf idA idB) lam
        stage la idx (min (2 * q) (q + 2)) q (qep + 1) tL par)
      (dummyFsStage2AtomicProg Dh encPt Z ℓ encT (idsOf idA idB) lam)
  · push Not at htL_clamp
    obtain ⟨x, hx, hgt⟩ := htL_clamp
    have hx_le := admissibleLastLeakGuesses_four_some_le htL x hx
    have hlt : q < healEpoch tL := by
      rw [hx]
      change q < x + 2
      omega
    rw [Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNERedsHop3BucketAux.localAuthDFPaperBucketMode_evalDist_true_eq_zero_of_lt_healEpoch
          (dhScheme Dh) (rootPRNG Z.F encPt) (lFS Z protoSignalCodec ℓ encT (idsOf idA idB) 25000)
          lam q (qep + 1) true tL par hlt challAdvDF hq_ch,
        Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNERedsHop3BucketAux.localAuthDFPaperBucketMode_evalDist_true_eq_zero_of_lt_healEpoch
          (dhScheme Dh) (rootPRNG Z.F encPt) (lFS Z protoSignalCodec ℓ encT (idsOf idA idB) 25000)
          lam q (qep + 1) false tL par hlt challAdvDF hq_ch]
    simp only [zero_add]
    exact zero_le

end

end Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNERedsHop3Bucket
