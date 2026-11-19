/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Session.StatementComposed
public import Computational.Proofs.SessionCostedFs -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.Bundles -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem12.Stage2Defs -- proof-setup: allow-public-import
import Computational.Proofs.Fig8SchemeBridge
import Computational.Proofs.ReductionDsl.PureAuxMacroLift
import Computational.Proofs.SessionCostedFig8.BundlesEval
import Computational.Proofs.SessionCostedFig8.FsAtomicBSwap
import Computational.Proofs.SessionCostedFig8.QuerySubsumes
import Computational.Proofs.SessionCostedFig8.RedCKAPrivUBridge
import Computational.Proofs.SessionCostedFig8.RedCKAPrivUDhSwap
import Computational.Proofs.SessionCostedFig8.RedFSUniEval
import Computational.Proofs.SessionCostedFig8.Stage2Swap
import Computational.Proofs.ReductionDsl.SM.RedFSPotOK
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.PrivRedQueries
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.SessionShort
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement
import Computational.Proofs.CryptoGames.CKA.DHProof
import Computational.Proofs.CryptoGames.SM.Theorem12
import Computational.Proofs.E2E.SignedCoin
import Computational.Proofs.SignalWireRoundTrip

/-!
# Drop-In Stage-2 Mixture Privacy Bridges for `SessionCostedDF` & `SessionCostedFig8`

Provides:
1. `fig8RedsInst_priv_fsOk_min_of_fsOk2q`: upgrades `FsOk ℓ (2 * q) q` to
   `FsOk ℓ (min (2 * q) (q + 2)) q` on `(fig8RedsInst ...).redFSPriv` and `.redFSPrivCoin` via
   `BundlesEval.fig8RedsInst_redFSPriv{,Coin}_querySubsumes` +
   `RedFSPotOK.redFSPrivUni{,Coin}Prog_makesAtMostQueries` (also closes `SessionCostedFig8`'s
   `fig8RedsInst_fsOk_min_and_encAtomicShort`).
2. `fig8RedsInst_redCKAPrivU_semantic_advAvg_advantage` (and point-mass
   `fig8RedsInst_redCKAPrivU_semantic_advantage`): chains `BundlesEval`, `RedCKAPrivUBridge`, and
   `RedCKAPrivUDhSwap` from `fig8RedsInst.redCKAPrivU` to `SM.Construction.redCKAPrivU (dhScheme Dh)`.
3. `fig8RedsInst_redFSPriv{,Coin}_semantic_mix_evalDistEq` (and point-mass versions): chains
   `BundlesEval`, `RedFSUniEval`, and `Stage2Swap` from `fig8RedsInst.redFSPriv{,Coin}` to
   `SM.Construction.redFSPrivUni{,Coin} (dhScheme Dh) ... (lFS ...)`.
4. `fig8MixPriv_simFig8_le_fig8MixShortPrivV1_of_fsOk2q`: complete drop-in proof of
   `SessionCostedDF.fig8MixPriv_simFig8_le_fig8MixShortPrivV1` (`SessionCostedDF.lean:399–413`).-/

set_option autoImplicit false

open OracleSpec OracleComp

public section

open scoped ENNReal
open Computational.Proofs.ReductionDsl.Fig8Atomic (atomicShortPubB dhSchemeFb fsAtomicB)
open Computational.Proofs.ReductionDsl.FsAtomicMacros (atomicShortB)
open CryptoGames (CKAScheme PRFPRNG)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun dhScheme dhScheme_correct)
open CryptoGames.FSAEAD (RatchetReceiverState RatchetSenderState)
open CryptoGames.LibsignalSM (Fig8Adv lBlank)
open CryptoGames.LibsignalSession (Crypto GhostState IdentityKey PublicKey SignalMessageProtoCodec maxForwardJumps)
open CryptoGames.Ratchet (rootPRNG)
open CryptoGames.Ratchet.LibsignalInst (GuardedFSInjectShort LibsignalCiphertextWithSalt32 LibsignalMsgPublicPart dummyKey lFS lFig8)
open CryptoGames.SM.Construction (Header healEpoch)
open CryptoVerification.E2E (Bytes SessionCostedReductions fig8MixShortPrivV1 fsAeadMixtureBound idsOf prefixAdvAvg)
open CryptoVerification.E2E.Signed (advAvg ckaBranch_avg prngBranch_avg)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSession (FsAdv FsCostedReds fsCostedRedsInst signalEncodeFits32_proto signalRoundTripShort_proto)

namespace Computational.Proofs.SessionCostedDFStage2Priv

section Stage2Priv

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
local instance : Inhabited Pt := ⟨0⟩

/-- Exact copy of `CryptoVerification.LibsignalSession.FsOk` (`SessionCostedFig8.lean:88–99`,
definitionally equal by `rfl`). -/
@[expose] def FsOk2 (ℓ qR qd : ℕ)
    (R : CryptoGames.FSAEAD.RatchetAdversary (BitVec 256) (BitVec 256) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) LibsignalCiphertextWithSalt32) : Prop :=
  CryptoGames.FSAEAD.MakesAtMostQueries R qR ∧ CryptoGames.FSAEAD.MakesAtMostDecQueries R qd ∧
    CryptoGames.FSAEAD.EqualPubChallenges R ∧
    CryptoGames.FSAEAD.AllQueriesInOneADClass (fun h : Header Pt => h.1) R ∧
    CryptoGames.FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB) R ∧
    GuardedFSInjectShort R

/-- Tightens `FsOk2 ℓ (2 * q) q` on `fig8RedsInst.redFSPriv` and `fig8RedsInst.redFSPrivCoin` to
`FsOk2 ℓ (min (2 * q) (q + 2)) q` using `RedFSPotOK.redFSPrivUni{,Coin}Prog_makesAtMostQueries`. -/
theorem fig8RedsInst_priv_fsOk_min_of_fsOk2q
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : CryptoGames.Party → IdentityKey) (lam : Pt) (qep q i : ℕ)
    (B_adv : Fig8Adv Pt ℓ) (hqB : CryptoGames.SM.MakesAtMostQueries B_adv q)
    (h2q :
      let R := Computational.Proofs.SessionCostedFig8.Bundles.fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q
      let privAdv := (R.privRedB i).eval (fun _ => B_adv) ()
      (FsOk2 ℓ (2 * q) q ((R.redFSPriv i).eval (fun _ => privAdv) ()) ∧
        CryptoGames.FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
          ((R.redFSPriv i).eval (fun _ => privAdv) ())) ∧
      (FsOk2 ℓ (2 * q) q ((R.redFSPrivCoin i).eval (fun _ => privAdv) ()) ∧
        CryptoGames.FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
          ((R.redFSPrivCoin i).eval (fun _ => privAdv) ()))) :
    let R := Computational.Proofs.SessionCostedFig8.Bundles.fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q
    let privAdv := (R.privRedB i).eval (fun _ => B_adv) ()
    (FsOk2 ℓ (min (2 * q) (q + 2)) q ((R.redFSPriv i).eval (fun _ => privAdv) ()) ∧
      CryptoGames.FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
        ((R.redFSPriv i).eval (fun _ => privAdv) ())) ∧
    (FsOk2 ℓ (min (2 * q) (q + 2)) q ((R.redFSPrivCoin i).eval (fun _ => privAdv) ()) ∧
      CryptoGames.FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
        ((R.redFSPrivCoin i).eval (fun _ => privAdv) ())) := by
  intro R privAdv
  have hPrivEq : privAdv = CryptoGames.SM.ThmB.privRedB (2 + 1) qep i (lBlank ℓ) B_adv :=
    Computational.Proofs.SessionCostedFig8.BundlesEval.fig8RedsInst_privRedB_eval Dh encPt C codec ℓ hℓ encT idOf lam qep q i B_adv hqB
  have hqPriv : CryptoGames.SM.MakesAtMostQueries privAdv q := by
    rw [hPrivEq]
    exact CryptoGames.LibsignalSM.Proofs.PrivRedQueries.privRedB_queries (2 + 1) qep i (lBlank ℓ) B_adv q hqB
  have hSubPriv := Computational.Proofs.SessionCostedFig8.BundlesEval.fig8RedsInst_redFSPriv_querySubsumes
    Dh encPt C codec ℓ hℓ encT idOf lam qep q i privAdv
  have hSubCoin := Computational.Proofs.SessionCostedFig8.BundlesEval.fig8RedsInst_redFSPrivCoin_querySubsumes
    Dh encPt C codec ℓ hℓ encT idOf lam qep q i privAdv
  have hMinPriv : CryptoGames.FSAEAD.MakesAtMostQueries ((R.redFSPriv i).eval (fun _ => privAdv) ())
      (min (2 * q) (q + 2)) :=
    hSubPriv.fsaeadMakesAtMostQueries_of_querySubsumes
      (Computational.Proofs.ReductionDsl.SM.RedFSPotOK.redFSPrivUniProg_makesAtMostQueries
        (q + 1) ((q + 1) * (maxForwardJumps + 1)) 1 qep maxForwardJumps i q privAdv hqPriv)
  have hMinCoin : CryptoGames.FSAEAD.MakesAtMostQueries ((R.redFSPrivCoin i).eval (fun _ => privAdv) ())
      (min (2 * q) (q + 2)) :=
    hSubCoin.fsaeadMakesAtMostQueries_of_querySubsumes
      (Computational.Proofs.ReductionDsl.SM.RedFSPotOK.redFSPrivUniCoinProg_makesAtMostQueries
        (q + 1) ((q + 1) * (maxForwardJumps + 1)) 1 qep maxForwardJumps i q privAdv hqPriv)
  exact ⟨⟨⟨hMinPriv, h2q.1.1.2⟩, h2q.1.2⟩, ⟨⟨hMinCoin, h2q.2.1.2⟩, h2q.2.2⟩⟩

theorem cka_boolDist_mix_eq_advantage {KC Γ CCoins T I α : Type}
    [SampleableType KC] [SampleableType CCoins] [SampleableType I]
    (cka : CKAScheme KC Γ CCoins T I) (Δcka tStar : ℕ) (oa : ProbComp α)
    (D : α → CryptoGames.CKA.Adversary Γ CCoins T I) :
    (𝒟[oa >>= fun o => CryptoGames.CKA.branch cka Δcka tStar true (D o)].boolDist
      𝒟[oa >>= fun o => CryptoGames.CKA.branch cka Δcka tStar false (D o)]) =
    CryptoGames.CKA.advantage cka Δcka tStar (prefixAdvAvg oa D) := by
  rw [CryptoGames.CKA.advantage_eq_boolDist]
  change _ = (𝒟[CryptoGames.CKA.branch cka Δcka tStar true (advAvg oa D)].boolDist
    𝒟[CryptoGames.CKA.branch cka Δcka tStar false (advAvg oa D)])
  rw [ckaBranch_avg, ckaBranch_avg]

theorem prng_boolDist_mix_eq_advantage {KR Sig I K α : Type}
    [SampleableType KR] [SampleableType I] [SampleableType K] [DecidableEq I]
    (prng : PRFPRNG KR Sig I K) (oa : ProbComp α)
    (D : α → CryptoGames.PRFPRNG.Adversary Sig I K) :
    (𝒟[oa >>= fun o => CryptoGames.PRFPRNG.branch prng true (D o)].boolDist
      𝒟[oa >>= fun o => CryptoGames.PRFPRNG.branch prng false (D o)]) =
    CryptoGames.PRFPRNG.advantage prng (prefixAdvAvg oa D) := by
  rw [CryptoGames.PRFPRNG.advantage_eq_boolDist]
  change _ = (𝒟[CryptoGames.PRFPRNG.branch prng true (advAvg oa D)].boolDist
    𝒟[CryptoGames.PRFPRNG.branch prng false (advAvg oa D)])
  rw [prngBranch_avg, prngBranch_avg]

/-- Mixture (`prefixAdvAvg`) semantic advantage bridge for `fig8RedsInst.redCKAPrivU`. -/
theorem fig8RedsInst_redCKAPrivU_semantic_advAvg_advantage {α : Type}
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (codec : SignalMessageProtoCodec) (hc : codec = protoSignalCodec)
    (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) (encT : Pt → PublicKey) (oa : ProbComp α)
    (idOf : α → CryptoGames.Party → IdentityKey)
    (lam : Pt) (qep q tStar : ℕ) (tL : Option ℕ) (i : ℕ) (A : α → Fig8Adv Pt ℓ)
    (hqA : ∀ o, CryptoGames.SM.MakesAtMostQueries (A o) q)
    (hshA : ∀ o, CryptoGames.LibsignalSM.Proofs.SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) (A o)) :
    CryptoGames.CKA.advantage (dhScheme Dh) 1 tStar
      (prefixAdvAvg oa fun o =>
        ((Computational.Proofs.SessionCostedFig8.Bundles.fig8RedsInst Dh encPt C codec ℓ encT (idOf o) lam qep q).redCKAPrivU tL i).eval
          (fun _ => A o) ()) =
    CryptoGames.CKA.advantage (dhScheme Dh) 1 tStar
      (prefixAdvAvg oa fun o =>
        CryptoGames.SM.Construction.redCKAPrivU (dhScheme Dh) (rootPRNG C.F encPt)
          (lFS C codec ℓ encT (idOf o) maxForwardJumps) lam 1 qep tL i (A o)) := by
  subst hc
  change CryptoGames.CKA.advantage (dhScheme Dh) 1 tStar (advAvg oa _) =
    CryptoGames.CKA.advantage (dhScheme Dh) 1 tStar (advAvg oa _)
  rw [Computational.Proofs.SessionCostedFig8.QuerySubsumes.ckaAdvantage_advAvg_congr (dhScheme Dh) 1 tStar oa fun o =>
      Computational.Proofs.SessionCostedFig8.BundlesEval.fig8RedsInst_redCKAPrivU_coinSimEquiv Dh encPt C protoSignalCodec ℓ hℓ encT
        (idOf o) lam qep q tL i (A o),
    CryptoGames.CKA.advantage_eq_boolDist, CryptoGames.CKA.advantage_eq_boolDist,
    ckaBranch_avg, ckaBranch_avg, ckaBranch_avg, ckaBranch_avg]
  have hBr : ∀ b,
      (oa >>= fun o => CryptoGames.CKA.branch (dhScheme Dh) 1 tStar b
        ((CryptoGames.SM.Construction.redCKAPrivUProg (q + 1) ((q + 1) * (maxForwardJumps + 1))
          1 qep maxForwardJumps tL i :
          ReductionDsl.CostedReduction
            (Computational.Proofs.SessionCostedFig8.Bundles.fig8CkaOpsShallow ℓ Pt C Dh encPt encT (idOf o) lam
              ((q + 1) * (maxForwardJumps + 1)))
            (CryptoGames.CKA.ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
              (BitVec 256) (BitVec 256) (BitVec 256)
              (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
              (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
              ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
            _ _ .unit .unit .bool .bool).eval (fun _ => A o) ())) =
      (oa >>= fun o => CryptoGames.CKA.branch (dhScheme Dh) 1 tStar b
        (CryptoGames.SM.Construction.redCKAPrivU (dhScheme Dh) (rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT (idOf o) maxForwardJumps) lam 1 qep tL i (A o))) :=
    fun b => bind_congr fun o => by
      rw [Computational.Proofs.SessionCostedFig8.RedCKAPrivUBridge.redCKAPrivUProg_eval_atomic Dh encPt C ℓ encT (idOf o) lam qep q tL i
        (A o) (hqA o)]
      have hFsSwap :
          CryptoGames.SM.Construction.redCKAPrivU (dhSchemeFb Dh) (rootPRNG C.F encPt)
            (fsAtomicB C ℓ encT (idOf o) ((q + 1) * (maxForwardJumps + 1))) lam 1 qep tL i (A o) =
          CryptoGames.SM.Construction.redCKAPrivU (dhSchemeFb Dh) (rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT (idOf o) maxForwardJumps) lam 1 qep tL i (A o) := by
        unfold CryptoGames.SM.Construction.redCKAPrivU
        refine bind_congr fun bSM => ?_
        rw [Computational.Proofs.SessionCostedFig8.RedCKAPrivUBridge.runCKAU_fsAtomicB_eq_lFS (dhSchemeFb Dh) (rootPRNG C.F encPt) C ℓ encT
          (idOf o) lam ((q + 1) * (maxForwardJumps + 1)) q 1 qep ⟨false, tL, i⟩ bSM (Nat.le_refl _)
          (A o) q (hqA o) (Nat.le_refl q) (hshA o)]
      rw [hFsSwap, ← CryptoVerification.LibsignalSession.Fig8SchemeBridge.ckaBranch_dhSchemeFb_eq,
        Computational.Proofs.SessionCostedFig8.RedCKAPrivUDhSwap.ckaBranch_redCKAPrivU_dhSchemeFb_eq]
  rw [hBr true, hBr false]

/-- Point-mass semantic `=ᵈ` game bridge for `fig8RedsInst.redFSPriv` (`redFSPrivUni`). -/
theorem fig8RedsInst_redFSPriv_semantic_game_evalDistEq
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (codec : SignalMessageProtoCodec) (hc : codec = protoSignalCodec)
    (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) (encT : Pt → PublicKey) (idOf : CryptoGames.Party → IdentityKey)
    (lam : Pt) (qep q i : ℕ) (A : Fig8Adv Pt ℓ)
    (hqA : CryptoGames.SM.MakesAtMostQueries A q)
    (hshA : CryptoGames.LibsignalSM.Proofs.SessionShort.SendMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    CryptoGames.FSAEAD.game (lFS C codec ℓ encT idOf maxForwardJumps)
      (((Computational.Proofs.SessionCostedFig8.Bundles.fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redFSPriv i).eval
        (fun _ => A) ()) =ᵈ
    CryptoGames.FSAEAD.game (lFS C codec ℓ encT idOf maxForwardJumps)
      (CryptoGames.SM.Construction.redFSPrivUni (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C codec ℓ encT idOf maxForwardJumps) lam 1 qep i A) := by
  subst hc
  let B0 := (q + 1) * (maxForwardJumps + 1)
  have hCoin := Computational.Proofs.ReductionDsl.PureAuxMacroLift.fsaeadGame_evalDistEq_of_coinSimEquiv
    (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
    (Computational.Proofs.SessionCostedFig8.BundlesEval.fig8RedsInst_redFSPriv_coinSimEquiv Dh encPt C protoSignalCodec ℓ hℓ encT idOf
      lam qep q i A)
  have hClamp :
      ((CryptoGames.SM.Construction.redFSPrivUniProg (q + 1) B0 1 qep maxForwardJumps i :
        ReductionDsl.CostedReduction (Computational.Proofs.SessionCostedFig8.Bundles.fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
          (CryptoGames.PRFPRNG.fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
            (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
            (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
            (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
            ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
          _ _ .unit .unit .bool .bool).eval (fun _ => A) ()) =
      CryptoGames.SM.Construction.redFSPrivUni (dhSchemeFb Dh) (rootPRNG C.F encPt)
        (CryptoGames.SM.Construction.fsClamp B0 (fsAtomicB C ℓ encT idOf B0)) lam 1 qep i A :=
    Computational.Proofs.SessionCostedFig8.RedFSUniEval.redFSPrivUniProg_eval_clamp_eq (dhSchemeFb Dh) (rootPRNG C.F encPt)
      (fsAtomicB C ℓ encT idOf B0) (q + 1) B0 q 1 qep i
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (Nat.le_refl _) (Nat.mul_le_mul (Nat.le_succ q) (Nat.le_succ q))
      A q hqA (Nat.le_refl q)
  refine hCoin.trans ?_
  rw [hClamp, Computational.Proofs.SessionCostedFig8.Stage2Swap.fsaeadGame_redFSPrivUni_atomic_eq Dh (rootPRNG C.F encPt) C ℓ encT idOf
    lam B0 B0 q 1 qep i (Nat.le_refl _) (Nat.le_refl _) A q hqA (Nat.le_refl q) hshA]

/-- Point-mass semantic `=ᵈ` game bridge for `fig8RedsInst.redFSPrivCoin` (`redFSPrivUniCoin`). -/
theorem fig8RedsInst_redFSPrivCoin_semantic_game_evalDistEq
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (codec : SignalMessageProtoCodec) (hc : codec = protoSignalCodec)
    (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) (encT : Pt → PublicKey) (idOf : CryptoGames.Party → IdentityKey)
    (lam : Pt) (qep q i : ℕ) (A : Fig8Adv Pt ℓ)
    (hqA : CryptoGames.SM.MakesAtMostQueries A q)
    (hshA : CryptoGames.LibsignalSM.Proofs.SessionShort.SendMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    CryptoGames.FSAEAD.game (lFS C codec ℓ encT idOf maxForwardJumps)
      (((Computational.Proofs.SessionCostedFig8.Bundles.fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redFSPrivCoin i).eval
        (fun _ => A) ()) =ᵈ
    CryptoGames.FSAEAD.game (lFS C codec ℓ encT idOf maxForwardJumps)
      (CryptoGames.SM.Construction.redFSPrivUniCoin (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C codec ℓ encT idOf maxForwardJumps) lam 1 qep i A) := by
  subst hc
  let B0 := (q + 1) * (maxForwardJumps + 1)
  have hCoin := Computational.Proofs.ReductionDsl.PureAuxMacroLift.fsaeadGame_evalDistEq_of_coinSimEquiv
    (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
    (Computational.Proofs.SessionCostedFig8.BundlesEval.fig8RedsInst_redFSPrivCoin_coinSimEquiv Dh encPt C protoSignalCodec ℓ hℓ encT idOf
      lam qep q i A)
  have hClamp :
      ((CryptoGames.SM.Construction.redFSPrivUniCoinProg (q + 1) B0 1 qep maxForwardJumps i :
        ReductionDsl.CostedReduction (Computational.Proofs.SessionCostedFig8.Bundles.fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
          (CryptoGames.PRFPRNG.fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
            (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
            (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
            (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
            ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
          _ _ .unit .unit .bool .bool).eval (fun _ => A) ()) =
      CryptoGames.SM.Construction.redFSPrivUniCoin (dhSchemeFb Dh) (rootPRNG C.F encPt)
        (CryptoGames.SM.Construction.fsClamp B0 (fsAtomicB C ℓ encT idOf B0)) lam 1 qep i A :=
    Computational.Proofs.SessionCostedFig8.RedFSUniEval.redFSPrivUniCoinProg_eval_clamp_eq (dhSchemeFb Dh) (rootPRNG C.F encPt)
      (fsAtomicB C ℓ encT idOf B0) (q + 1) B0 q 1 qep i
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (Nat.le_refl _) (Nat.mul_le_mul (Nat.le_succ q) (Nat.le_succ q))
      A q hqA (Nat.le_refl q)
  refine hCoin.trans ?_
  rw [hClamp, Computational.Proofs.SessionCostedFig8.Stage2Swap.fsaeadGame_redFSPrivUniCoin_atomic_eq Dh (rootPRNG C.F encPt) C ℓ encT idOf
    lam B0 B0 q 1 qep i (Nat.le_refl _) (Nat.le_refl _) A q hqA (Nat.le_refl q) hshA]

private theorem fig8RedsInst_redCKAPriv_semantic_advAvg_advantage {α : Type}
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (C : Crypto)
    (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) (encT : Pt → PublicKey) (oa : ProbComp α)
    (idOf : α → CryptoGames.Party → IdentityKey) (lam : Pt) (qep q tStar : ℕ)
    (tL : Option ℕ) (i : ℕ) (A : α → Fig8Adv Pt ℓ)
    (hqA : ∀ o, CryptoGames.SM.MakesAtMostQueries (A o) q)
    (hshA : ∀ o, CryptoGames.LibsignalSM.Proofs.SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) (A o)) :
    CryptoGames.CKA.advantage (dhScheme Dh) 1 tStar
      (prefixAdvAvg oa fun o =>
        ((Computational.Proofs.SessionCostedFig8.Bundles.fig8RedsInst Dh encPt C protoSignalCodec ℓ encT (idOf o) lam qep q).redCKAPriv tL i).eval
          (fun _ => A o) ()) =
    CryptoGames.CKA.advantage (dhScheme Dh) 1 tStar
      (prefixAdvAvg oa fun o =>
        CryptoGames.SM.Construction.redCKAPriv (dhScheme Dh) (rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT (idOf o) maxForwardJumps) lam 1 qep tL i (A o)) := by
  change CryptoGames.CKA.advantage (dhScheme Dh) 1 tStar (advAvg oa _) =
    CryptoGames.CKA.advantage (dhScheme Dh) 1 tStar (advAvg oa _)
  rw [Computational.Proofs.SessionCostedFig8.QuerySubsumes.ckaAdvantage_advAvg_congr (dhScheme Dh) 1 tStar oa fun o =>
      Computational.Proofs.SessionCostedFig8.BundlesEval.fig8RedsInst_redCKAPriv_coinSimEquiv Dh encPt C protoSignalCodec
        ℓ hℓ encT (idOf o) lam qep q tL i (A o) (hqA o)]
  rw [CryptoGames.CKA.advantage_eq_boolDist, CryptoGames.CKA.advantage_eq_boolDist,
    ckaBranch_avg, ckaBranch_avg, ckaBranch_avg, ckaBranch_avg]
  have hBr : ∀ b,
      (oa >>= fun o => CryptoGames.CKA.branch (dhScheme Dh) 1 tStar b
        (CryptoGames.SM.Construction.redCKAPriv (dhSchemeFb Dh) (rootPRNG C.F encPt)
          (fsAtomicB C ℓ encT (idOf o) ((q + 1) * (maxForwardJumps + 1)))
          lam 1 qep tL i (A o))) =
      (oa >>= fun o => CryptoGames.CKA.branch (dhScheme Dh) 1 tStar b
        (CryptoGames.SM.Construction.redCKAPriv (dhScheme Dh) (rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT (idOf o) maxForwardJumps) lam 1 qep tL i (A o))) :=
    fun b => bind_congr fun o => by
      rw [← CryptoVerification.LibsignalSession.Fig8SchemeBridge.ckaBranch_dhSchemeFb_eq]
      exact Computational.Proofs.SessionCostedFig8.FsAtomicBSwap.ckaBranch_redCKAPriv_atomic_eq Dh (rootPRNG C.F encPt) C ℓ encT (idOf o)
        lam ((q + 1) * (maxForwardJumps + 1)) q 1 tStar qep tL i b (Nat.le_refl _)
        (A o) q (hqA o) (Nat.le_refl q) (hshA o)
  rw [hBr true, hBr false]

private theorem fig8RedsInst_redPRNGPriv_semantic_advAvg_advantage {α : Type}
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (C : Crypto)
    (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) (encT : Pt → PublicKey) (oa : ProbComp α)
    (idOf : α → CryptoGames.Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (tL : Option ℕ) (i : ℕ) (A : α → Fig8Adv Pt ℓ)
    (hqA : ∀ o, CryptoGames.SM.MakesAtMostQueries (A o) q)
    (hshA : ∀ o, CryptoGames.LibsignalSM.Proofs.SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) (A o)) :
    CryptoGames.PRFPRNG.advantage (rootPRNG C.F encPt)
      (prefixAdvAvg oa fun o =>
        ((Computational.Proofs.SessionCostedFig8.Bundles.fig8RedsInst Dh encPt C protoSignalCodec ℓ encT (idOf o) lam qep q).redPRNGPriv tL i).eval
          (fun _ => A o) ()) =
    CryptoGames.PRFPRNG.advantage (rootPRNG C.F encPt)
      (prefixAdvAvg oa fun o =>
        CryptoGames.SM.Construction.redPRNGPriv (dhScheme Dh) (rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT (idOf o) maxForwardJumps) lam 1 qep tL i (A o)) := by
  change CryptoGames.PRFPRNG.advantage (rootPRNG C.F encPt) (advAvg oa _) =
    CryptoGames.PRFPRNG.advantage (rootPRNG C.F encPt) (advAvg oa _)
  rw [Computational.Proofs.SessionCostedFig8.QuerySubsumes.prngAdvantage_advAvg_congr (rootPRNG C.F encPt) oa fun o =>
      Computational.Proofs.SessionCostedFig8.BundlesEval.fig8RedsInst_redPRNGPriv_prog_coinSimEquiv Dh encPt C protoSignalCodec
        ℓ hℓ encT (idOf o) lam qep q tL i (A o)]
  rw [CryptoGames.PRFPRNG.advantage_eq_boolDist, CryptoGames.PRFPRNG.advantage_eq_boolDist,
    prngBranch_avg, prngBranch_avg, prngBranch_avg, prngBranch_avg]
  have hBr : ∀ b,
      (oa >>= fun o => CryptoGames.PRFPRNG.branch (rootPRNG C.F encPt) b
        ((CryptoGames.SM.Construction.redPRNGPrivProg (q + 1) ((q + 1) * (maxForwardJumps + 1))
          1 qep maxForwardJumps tL i :
          ReductionDsl.CostedReduction
            (Computational.Proofs.SessionCostedFig8.Bundles.fig8CkaOpsShallow ℓ Pt C Dh encPt encT (idOf o) lam
              ((q + 1) * (maxForwardJumps + 1)))
            (CryptoGames.PRFPRNG.prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
              (BitVec 256) (BitVec 256) (BitVec 256)
              (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
              (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
              ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
            _ _ .unit .unit .bool .bool).eval (fun _ => A o) ())) =
      (oa >>= fun o => CryptoGames.PRFPRNG.branch (rootPRNG C.F encPt) b
        (CryptoGames.SM.Construction.redPRNGPriv (dhScheme Dh) (rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT (idOf o) maxForwardJumps) lam 1 qep tL i (A o))) :=
    fun b => bind_congr fun o => by
      rw [Computational.Proofs.SessionCostedFig8.BundlesEval.redPRNGPrivProg_branch_eval_atomic Dh encPt C ℓ encT (idOf o)
        lam qep q tL i (A o) (hqA o) b,
        Computational.Proofs.SessionCostedFig8.FsAtomicBSwap.redPRNGPriv_atomic_eq Dh (rootPRNG C.F encPt) C ℓ encT (idOf o) lam
          ((q + 1) * (maxForwardJumps + 1)) q 1 qep tL i (Nat.le_refl _) (A o) q (hqA o)
          (Nat.le_refl q) (hshA o)]
  rw [hBr true, hBr false]

omit [Zero Pt] [SampleableType Pt] in
private theorem fsMixBias_le_fsAeadMixtureBound_of_fsOk {α : Type}
    (Z : Crypto) (hD : ∀ k x, Z.D k (Z.E k x) = x) {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (oa : ProbComp α) (idOf : α → CryptoGames.Party → IdentityKey) (qR qd : ℕ)
    (hqR32 : qR + 25002 < 2 ^ 32)
    (Rfs : ∀ o, FsCostedReds Z protoSignalCodec ℓ encT (idOf o))
    (hRfs : ∀ o, Rfs o = fsCostedRedsInst Z protoSignalCodec ℓ encT (idOf o) qR)
    (B_cost B_sem : α → FsAdv Pt ℓ)
    (hEq : (oa >>= fun o => CryptoGames.FSAEAD.game (lFS Z protoSignalCodec ℓ encT (idOf o) 25000) (B_cost o)) =ᵈ
      (oa >>= fun o => CryptoGames.FSAEAD.game (lFS Z protoSignalCodec ℓ encT (idOf o) 25000) (B_sem o)))
    (hOk : ∀ o, FsOk2 ℓ qR qd (B_cost o) ∧
      CryptoGames.FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) (B_cost o)) :
    𝒟[oa >>= fun o => CryptoGames.FSAEAD.game (lFS Z protoSignalCodec ℓ encT (idOf o) 25000) (B_sem o)].boolBias ≤
      fsAeadMixtureBound Z protoSignalCodec ℓ oa qR qd Rfs B_cost := by
  rw [← hEq.evalDist_eq,
    show Rfs = (fun o => fsCostedRedsInst Z protoSignalCodec ℓ encT (idOf o) qR) from funext hRfs,
    CryptoVerification.LibsignalSession.fsShortBoundMixWith_inst_eq Z ℓ encT oa idOf qR qd hℓ hinj B_cost
      (fun o => (hOk o).1.1) (fun o => (hOk o).2)]
  exact CryptoVerification.E2E.Signed.FSMix.lFS_bound_mix Z hD protoSignalCodec signalRoundTripShort_proto
    signalEncodeFits32_proto ℓ (by omega) encT hinj hdum oa idOf 25000 le_rfl
    B_cost qR qd (fun o => (hOk o).1.1) (fun o => (hOk o).1.2.1) hqR32
    (fun o => (hOk o).1.2.2.1) (fun o => (hOk o).1.2.2.2.1)
    (fun o => (hOk o).1.2.2.2.2.1) (fun o => (hOk o).1.2.2.2.2.2)

/-- Complete drop-in proof of `SessionCostedDF.fig8MixPriv_simFig8_le_fig8MixShortPrivV1`
(`SessionCostedDF.lean:399–413`), parameterized over `R` matching `v1SessionReds`'s `.fig8`, `.fs`,
and `.simFig8` projections plus `(fig8RedsInst_fsOk_and_encAtomicShort ...).2` (`hPrivFsOk2q`). -/
theorem fig8MixPriv_simFig8_le_fig8MixShortPrivV1_of_fsOk2q {α : Type}
    (Z : Crypto) (K : CryptoVerification.LibsignalSpqrV1.MlKem)
    (hD : ∀ k x, Z.D k (Z.E k x) = x) {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (lam : Pt)
    (qep q : ℕ) (hq32 : 2 * q + 25002 < 2 ^ 32)
    (oa : ProbComp α) (ida idb : α → IdentityKey)
    (R : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (A : α → CryptoGames.SM.Adversary (GhostState Bytes) (CryptoGames.CBC.Plain ℓ) (BitVec 512) Bytes)
    (hq : ∀ o, CryptoGames.SM.MakesAtMostQueries (A o) q)
    (hFig8 : ∀ o, (R o).fig8 =
      Computational.Proofs.SessionCostedFig8.Bundles.fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) lam (qep + 1) q)
    (hFs : ∀ o, (R o).fs =
      fsCostedRedsInst Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) (min (2 * q) (q + 2)))
    (hSim : ∀ o, (R o).simFig8 =
      Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog.simFig8RedProg
        ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q)
    (h18 : ∀ (simAdv : α → Fig8Adv Pt ℓ),
      (∀ o ∈ support oa, CryptoGames.SM.EqualPubChalls (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1) (simAdv o)) →
      𝒟[oa >>= fun o => CryptoGames.SM.game (lFig8 Dh encPt Z protoSignalCodec ℓ encT
          (idsOf (ida o) (idb o)) 25000 lam) (2 + 1) (qep + 1) CryptoGames.SM.Config.h2 (simAdv o)].boolBias ≤
        2 * ∑ i ∈ Finset.range ((qep + 1) + 1),
          𝒟[oa >>= fun o => CryptoGames.SM.privAllGame (lFig8 Dh encPt Z protoSignalCodec ℓ encT
            (idsOf (ida o) (idb o)) 25000 lam) (2 + 1) (qep + 1) i
            (CryptoGames.SM.ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) (simAdv o))].boolBias)
    (hPrivFsOk2q : ∀ o i,
      let simAdv := ((R o).simFig8).eval (fun _ => A o) ()
      let Rf := Computational.Proofs.SessionCostedFig8.Bundles.fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) lam (qep + 1) q
      let privAdv := (Rf.privRedB i).eval (fun _ => simAdv) ()
      (FsOk2 ℓ (2 * q) q ((Rf.redFSPriv i).eval (fun _ => privAdv) ()) ∧
        CryptoGames.FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
          ((Rf.redFSPriv i).eval (fun _ => privAdv) ())) ∧
      (FsOk2 ℓ (2 * q) q ((Rf.redFSPrivCoin i).eval (fun _ => privAdv) ()) ∧
        CryptoGames.FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
          ((Rf.redFSPrivCoin i).eval (fun _ => privAdv) ()))) :
    let simAdv : α → Fig8Adv Pt ℓ := fun o =>
      (Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog.simFig8RedProg
        ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).eval (fun _ => A o) ()
    𝒟[oa >>= fun o => CryptoGames.SM.game (lFig8 Dh encPt Z protoSignalCodec ℓ encT
        (idsOf (ida o) (idb o)) 25000 lam) (2 + 1) (qep + 1) CryptoGames.SM.Config.h2 (simAdv o)].boolBias ≤
      fig8MixShortPrivV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb R A := by
  intro simAdv
  have hSimEq : ∀ o, ((R o).simFig8).eval (fun _ => A o) () = simAdv o := fun o => by rw [hSim o]
  have hqSim : ∀ o, CryptoGames.SM.MakesAtMostQueries (simAdv o) q := fun o =>
    Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog.simFig8RedProg_queries
      hℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q (A o) (hq o)
  have heqSim : ∀ o, CryptoGames.SM.EqualPubChalls (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1) (simAdv o) :=
    fun o =>
      Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog.simFig8RedProg_equalPub
        hℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q (A o) (hq o)
  have hshSim : ∀ o, CryptoGames.LibsignalSM.Proofs.SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) (simAdv o) :=
    fun o =>
      Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog.simFig8RedProg_sendAtomicShort
        hℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q (A o) (hq o)
  have hqR32 : min (2 * q) (q + 2) + 25002 < 2 ^ 32 := by omega
  refine (h18 simAdv (fun o _ => heqSim o)).trans ?_
  unfold fig8MixShortPrivV1
  dsimp only
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) zero_le
  have hPrivEq : ∀ o,
      (((R o).fig8.privRedB i).eval (fun _ => ((R o).simFig8).eval (fun _ => A o) ()) ()) =
      CryptoGames.SM.ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) (simAdv o) := fun o => by
    rw [hFig8 o, hSimEq o]
    exact Computational.Proofs.SessionCostedFig8.BundlesEval.fig8RedsInst_privRedB_eval Dh encPt Z protoSignalCodec ℓ hℓ encT
      (idsOf (ida o) (idb o)) lam (qep + 1) q i (simAdv o) (hqSim o)
  have hqPriv : ∀ o,
      CryptoGames.SM.MakesAtMostQueries (CryptoGames.SM.ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) (simAdv o)) q :=
    fun o => CryptoGames.LibsignalSM.Proofs.PrivRedQueries.privRedB_queries (2 + 1) (qep + 1) i (lBlank ℓ) (simAdv o) q (hqSim o)
  have hshPriv : ∀ o, CryptoGames.LibsignalSM.Proofs.SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
      (CryptoGames.SM.ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) (simAdv o)) :=
    fun o => CryptoGames.LibsignalSM.Proofs.SessionShort.privRedB_sendOk (2 + 1) (qep + 1) i
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
      (lBlank ℓ) (fun _ => rfl) (simAdv o) (hshSim o)
  have h12 := CryptoGames.SM.Construction.theorem12_stage2_mix
    (dhScheme Dh) (rootPRNG Z.F encPt) lam 1 (qep + 1) (dhScheme_correct Dh hDh) oa
    (fun o => lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) i
    (fun o => CryptoGames.SM.ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) (simAdv o))
  refine h12.trans ?_
  refine add_le_add (add_le_add ?_ ?_) ?_
  · refine le_of_eq (Finset.sum_congr rfl fun tL _ => ?_)
    rw [cka_boolDist_mix_eq_advantage, cka_boolDist_mix_eq_advantage,
      prng_boolDist_mix_eq_advantage]
    have h1 : (fun o => (((R o).fig8.redCKAPriv tL i).eval
        (fun _ => ((R o).fig8.privRedB i).eval (fun _ => ((R o).simFig8).eval (fun _ => A o) ()) ()) ())) =
        (fun o => ((Computational.Proofs.SessionCostedFig8.Bundles.fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
          lam (qep + 1) q).redCKAPriv tL i).eval
          (fun _ => CryptoGames.SM.ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) (simAdv o)) ()) := by
      funext o; rw [hPrivEq o, hFig8 o]
    have h2 : (fun o => (((R o).fig8.redCKAPrivU tL i).eval
        (fun _ => ((R o).fig8.privRedB i).eval (fun _ => ((R o).simFig8).eval (fun _ => A o) ()) ()) ())) =
        (fun o => ((Computational.Proofs.SessionCostedFig8.Bundles.fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
          lam (qep + 1) q).redCKAPrivU tL i).eval
          (fun _ => CryptoGames.SM.ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) (simAdv o)) ()) := by
      funext o; rw [hPrivEq o, hFig8 o]
    have h3 : (fun o => (((R o).fig8.redPRNGPriv tL i).eval
        (fun _ => ((R o).fig8.privRedB i).eval (fun _ => ((R o).simFig8).eval (fun _ => A o) ()) ()) ())) =
        (fun o => ((Computational.Proofs.SessionCostedFig8.Bundles.fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o))
          lam (qep + 1) q).redPRNGPriv tL i).eval
          (fun _ => CryptoGames.SM.ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) (simAdv o)) ()) := by
      funext o; rw [hPrivEq o, hFig8 o]
    rw [h1, h2, h3,
      fig8RedsInst_redCKAPriv_semantic_advAvg_advantage Dh encPt Z ℓ hℓ encT oa
        (fun o => idsOf (ida o) (idb o)) lam (qep + 1) q (healEpoch tL) tL i _ hqPriv hshPriv,
      fig8RedsInst_redCKAPrivU_semantic_advAvg_advantage Dh encPt Z protoSignalCodec rfl ℓ hℓ encT oa
        (fun o => idsOf (ida o) (idb o)) lam (qep + 1) q (healEpoch tL) tL i _ hqPriv hshPriv,
      fig8RedsInst_redPRNGPriv_semantic_advAvg_advantage Dh encPt Z ℓ hℓ encT oa
        (fun o => idsOf (ida o) (idb o)) lam (qep + 1) q tL i _ hqPriv hshPriv]
    rfl
  · refine fsMixBias_le_fsAeadMixtureBound_of_fsOk Z hD hℓ encT hinj hdum oa
      (fun o => idsOf (ida o) (idb o)) (min (2 * q) (q + 2)) q hqR32
      (fun o => (R o).fs) hFs _ _ ?_ ?_
    · refine EvalDistEq.rfl.bind fun o => ?_
      rw [hPrivEq o, hFig8 o]
      exact fig8RedsInst_redFSPriv_semantic_game_evalDistEq Dh encPt Z protoSignalCodec rfl ℓ hℓ
        encT (idsOf (ida o) (idb o)) lam (qep + 1) q i _ (hqPriv o) (hshPriv o)
    · intro o
      have hMin := fig8RedsInst_priv_fsOk_min_of_fsOk2q Dh encPt Z protoSignalCodec ℓ hℓ encT
        (idsOf (ida o) (idb o)) lam (qep + 1) q i (simAdv o) (hqSim o)
        (by simpa only [hSimEq o] using hPrivFsOk2q o i)
      simpa only [hFig8 o, hSimEq o] using hMin.1
  · refine mul_le_mul_of_nonneg_left
      (fsMixBias_le_fsAeadMixtureBound_of_fsOk Z hD hℓ encT hinj hdum oa
        (fun o => idsOf (ida o) (idb o)) (min (2 * q) (q + 2)) q hqR32
        (fun o => (R o).fs) hFs _ _ ?_ ?_) zero_le
    · refine EvalDistEq.rfl.bind fun o => ?_
      rw [hPrivEq o, hFig8 o]
      exact fig8RedsInst_redFSPrivCoin_semantic_game_evalDistEq Dh encPt Z protoSignalCodec rfl ℓ hℓ
        encT (idsOf (ida o) (idb o)) lam (qep + 1) q i _ (hqPriv o) (hshPriv o)
    · intro o
      have hMin := fig8RedsInst_priv_fsOk_min_of_fsOk2q Dh encPt Z protoSignalCodec ℓ hℓ encT
        (idsOf (ida o) (idb o)) lam (qep + 1) q i (simAdv o) (hqSim o)
        (by simpa only [hSimEq o] using hPrivFsOk2q o i)
      simpa only [hFig8 o, hSimEq o] using hMin.2

end Stage2Priv


end Computational.Proofs.SessionCostedDFStage2Priv
