/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Session.StatementComposed
public import Computational.Proofs.CryptoGames.SM.BucketAuthBridge -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SessionAuthBridge -- proof-setup: allow-public-import
import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSMInstance
import Computational.Proofs.CryptoGames.Ratchet.LibsignalSessionStatementsShort
import Computational.Proofs.CryptoGames.CKA.DHProof
import Computational.Proofs.SignalWireRoundTrip
import Computational.Proofs.E2E.SignedFig8
import Computational.Proofs.CryptoGames.SM.Theorem6Libsignal
public import Computational.Proofs.CryptoGames.SM.Theorem12 -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement
import Computational.Proofs.SessionCostedFs
public import Computational.Proofs.CryptoGames.SM.BlankedPrivRed -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma10
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma10Aux
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma11
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma9
import Computational.Proofs.E2E.SignedPrims
import Computational.Proofs.ReductionDsl.AtomicTablesHonest
import Computational.Proofs.ReductionDsl.FSAEAD.SaltWire
import Computational.Proofs.ReductionDsl.FsAtomicBoundsBase
import Computational.Proofs.ReductionDsl.LibsignalBoundDDHChain
import Computational.Proofs.ReductionDsl.PubRed

public section

set_option autoImplicit false

open Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth (cka_branch_true_redCKAAuthBucket_mix_le_sum_two_mul_prng_add_par localAuthBucketForgedHdrPar localAuthBucketMainPar redPRNGAuthBucketHybrid)
open Computational.Proofs.ReductionDsl.FsAtomicMacros (atomicShortB)
open CryptoGames (CKAScheme PRFPRNG Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun dhScheme dhScheme_correct)
open CryptoGames.LibsignalSM (Fig8Adv lBlank)
open CryptoGames.LibsignalSession (Crypto GhostState IdentityKey PublicKey)
open CryptoGames.Ratchet (rootPRNG)
open CryptoGames.Ratchet.LibsignalInst (GuardedFSInjectShort LibsignalCiphertextWithSalt32 LibsignalMsgPublicPart dummyKey lFS lFig8)
open CryptoGames.SM (admissibleLastLeakGuesses)
open CryptoGames.SM.Construction (Header healEpoch)
open CryptoVerification.E2E (Bytes SessionCostedReductions fig8MixShortAuthV1 fig8MixShortPrivV1 fsAeadAuthMixtureCompBound fsAeadMixtureBound idsOf prefixAdvAvg)
open CryptoVerification.E2E.Signed (advAvg ckaBranch_avg evalDist_bind_apply_le_sum_sum prngBranch_avg)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSession (FsAdv FsCostedReds fsCostedRedsInst signalEncodeFits32_proto signalRoundTripShort_proto)

namespace Computational.Proofs.E2E.Fig8Stage2MixHelpers

open OracleSpec OracleComp
open scoped ENNReal

section Helpers

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
local instance : Inhabited Pt := ⟨0⟩

theorem evalDist_bind_apply_le_sum {α κ : Type} (oa : ProbComp α) (f : α → ProbComp Bool)
    (u : Finset κ) (g : κ → α → ProbComp Bool)
    (H : ∀ a, 𝒟[f a] {true} ≤ ∑ k ∈ u, 𝒟[g k a] {true}) :
    𝒟[oa >>= f] {true} ≤ ∑ k ∈ u, 𝒟[oa >>= g k] {true} := by
  simpa using evalDist_bind_apply_le_sum_sum oa f ({()} : Finset Unit) (fun _ => u) (fun _ => g)
    (fun a => by simpa using H a)

/-- `FsOk` + `atomicShortB` predicate on a costed FS-AEAD reduction. -/
@[expose] def FsOkAtomic (ℓ qR qd : ℕ)
    (R : CryptoGames.FSAEAD.RatchetAdversary (BitVec 256) (BitVec 256) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) LibsignalCiphertextWithSalt32) : Prop :=
  (CryptoGames.FSAEAD.MakesAtMostQueries R qR ∧ CryptoGames.FSAEAD.MakesAtMostDecQueries R qd ∧
    CryptoGames.FSAEAD.EqualPubChallenges R ∧
    CryptoGames.FSAEAD.AllQueriesInOneADClass (fun h : Header Pt => h.1) R ∧
    CryptoGames.FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB) R ∧
    GuardedFSInjectShort R) ∧
    CryptoGames.FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) R

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

omit [Zero Pt] [SampleableType Pt] in
theorem fsMixBias_le_fsAeadMixtureBound_of_fsOk {α : Type}
    (Z : Crypto) (hD : ∀ k x, Z.D k (Z.E k x) = x) {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (oa : ProbComp α) (idOf : α → Party → IdentityKey) (qR qd : ℕ)
    (hqR32 : qR + 25002 < 2 ^ 32)
    (Rfs : ∀ o, FsCostedReds Z protoSignalCodec ℓ encT (idOf o))
    (hRfs : ∀ o, Rfs o = fsCostedRedsInst Z protoSignalCodec ℓ encT (idOf o) qR)
    (B_cost B_sem : α → FsAdv Pt ℓ)
    (hEq : (oa >>= fun o => CryptoGames.FSAEAD.game (lFS Z protoSignalCodec ℓ encT (idOf o) 25000) (B_cost o)) =ᵈ
      (oa >>= fun o => CryptoGames.FSAEAD.game (lFS Z protoSignalCodec ℓ encT (idOf o) 25000) (B_sem o)))
    (hOk : ∀ o, FsOkAtomic ℓ qR qd (B_cost o)) :
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

/-- Stage-2 mixture `SM.Config.h2` privacy bound into `fig8MixShortPrivV1` from per-reduction
evaluation agreement. -/
theorem fig8MixPriv_le_fig8MixShortPrivV1_of_fig8Eval {α : Type}
    (Z : Crypto) (K : CryptoVerification.LibsignalSpqrV1.MlKem)
    (hD : ∀ k x, Z.D k (Z.E k x) = x) {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (lam : Pt)
    (qep q : ℕ) (hq32 : 2 * q + 25002 < 2 ^ 32)
    (oa : ProbComp α) (ida idb : α → IdentityKey)
    (R : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (A : α → CryptoGames.SM.Adversary (GhostState Bytes) (CryptoGames.CBC.Plain ℓ) (BitVec 512) Bytes)
    (hFs : ∀ o, (R o).fs =
      fsCostedRedsInst Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) (min (2 * q) (q + 2)))
    (heqSim : ∀ o ∈ support oa,
      CryptoGames.SM.EqualPubChalls (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1)
        ((R o).simFig8.eval (fun _ => A o) ()))
    (hCKAPriv : ∀ i < (qep + 1) + 1, ∀ tL ∈ admissibleLastLeakGuesses (2 + 1) i,
      CryptoGames.CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
        (prefixAdvAvg oa fun o =>
          ((R o).fig8.redCKAPriv tL i).eval
            (fun _ => ((R o).fig8.privRedB i).eval (fun _ => (R o).simFig8.eval (fun _ => A o) ()) ()) ()) =
      CryptoGames.CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
        (prefixAdvAvg oa fun o =>
          CryptoGames.SM.Construction.redCKAPriv (dhScheme Dh) (rootPRNG Z.F encPt)
            (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL i
            (CryptoGames.SM.ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) ((R o).simFig8.eval (fun _ => A o) ()))))
    (hCKAPrivU : ∀ i < (qep + 1) + 1, ∀ tL ∈ admissibleLastLeakGuesses (2 + 1) i,
      CryptoGames.CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
        (prefixAdvAvg oa fun o =>
          ((R o).fig8.redCKAPrivU tL i).eval
            (fun _ => ((R o).fig8.privRedB i).eval (fun _ => (R o).simFig8.eval (fun _ => A o) ()) ()) ()) =
      CryptoGames.CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
        (prefixAdvAvg oa fun o =>
          CryptoGames.SM.Construction.redCKAPrivU (dhScheme Dh) (rootPRNG Z.F encPt)
            (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL i
            (CryptoGames.SM.ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) ((R o).simFig8.eval (fun _ => A o) ()))))
    (hPRNGPriv : ∀ i < (qep + 1) + 1, ∀ tL ∈ admissibleLastLeakGuesses (2 + 1) i,
      CryptoGames.PRFPRNG.advantage (rootPRNG Z.F encPt)
        (prefixAdvAvg oa fun o =>
          ((R o).fig8.redPRNGPriv tL i).eval
            (fun _ => ((R o).fig8.privRedB i).eval (fun _ => (R o).simFig8.eval (fun _ => A o) ()) ()) ()) =
      CryptoGames.PRFPRNG.advantage (rootPRNG Z.F encPt)
        (prefixAdvAvg oa fun o =>
          CryptoGames.SM.Construction.redPRNGPriv (dhScheme Dh) (rootPRNG Z.F encPt)
            (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL i
            (CryptoGames.SM.ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) ((R o).simFig8.eval (fun _ => A o) ()))))
    (hFSPrivEq : ∀ i < (qep + 1) + 1,
      (oa >>= fun o => CryptoGames.FSAEAD.game (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000)
        (((R o).fig8.redFSPriv i).eval
          (fun _ => ((R o).fig8.privRedB i).eval (fun _ => (R o).simFig8.eval (fun _ => A o) ()) ()) ())) =ᵈ
      (oa >>= fun o => CryptoGames.FSAEAD.game (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000)
        (CryptoGames.SM.Construction.redFSPrivUni (dhScheme Dh) (rootPRNG Z.F encPt)
          (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) i
          (CryptoGames.SM.ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) ((R o).simFig8.eval (fun _ => A o) ())))))
    (hFSPrivOk : ∀ i < (qep + 1) + 1, ∀ o,
      FsOkAtomic ℓ (min (2 * q) (q + 2)) q
        (((R o).fig8.redFSPriv i).eval
          (fun _ => ((R o).fig8.privRedB i).eval (fun _ => (R o).simFig8.eval (fun _ => A o) ()) ()) ()))
    (hFSPrivCoinEq : ∀ i < (qep + 1) + 1,
      (oa >>= fun o => CryptoGames.FSAEAD.game (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000)
        (((R o).fig8.redFSPrivCoin i).eval
          (fun _ => ((R o).fig8.privRedB i).eval (fun _ => (R o).simFig8.eval (fun _ => A o) ()) ()) ())) =ᵈ
      (oa >>= fun o => CryptoGames.FSAEAD.game (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000)
        (CryptoGames.SM.Construction.redFSPrivUniCoin (dhScheme Dh) (rootPRNG Z.F encPt)
          (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) i
          (CryptoGames.SM.ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) ((R o).simFig8.eval (fun _ => A o) ())))))
    (hFSPrivCoinOk : ∀ i < (qep + 1) + 1, ∀ o,
      FsOkAtomic ℓ (min (2 * q) (q + 2)) q
        (((R o).fig8.redFSPrivCoin i).eval
          (fun _ => ((R o).fig8.privRedB i).eval (fun _ => (R o).simFig8.eval (fun _ => A o) ()) ()) ())) :
    𝒟[oa >>= fun o => CryptoGames.SM.game (lFig8 Dh encPt Z protoSignalCodec ℓ encT
        (idsOf (ida o) (idb o)) 25000 lam) (2 + 1) (qep + 1) CryptoGames.SM.Config.h2
        ((R o).simFig8.eval (fun _ => A o) ())].boolBias ≤
      fig8MixShortPrivV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb R A := by
  have hqR32 : min (2 * q) (q + 2) + 25002 < 2 ^ 32 := by omega
  have h18 := _root_.CryptoGames.SM.lemma18_h2_blank_mix_stage2
    (fun o => lFig8 Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000 lam)
    (2 + 1) (qep + 1) (by omega) oa (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1) (lBlank ℓ)
    (fun _ _ h => congrArg (·, default) h)
    (fun o => (R o).simFig8.eval (fun _ => A o) ()) heqSim
  refine h18.trans ?_
  unfold fig8MixShortPrivV1
  dsimp only
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => ?_) zero_le
  have hi' : i < (qep + 1) + 1 := Finset.mem_range.mp hi
  have h12 := CryptoGames.SM.Construction.theorem12_stage2_mix
    (dhScheme Dh) (rootPRNG Z.F encPt) lam 1 (qep + 1) (dhScheme_correct Dh hDh) oa
    (fun o => lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) i
    (fun o => CryptoGames.SM.ThmB.privRedB (2 + 1) (qep + 1) i (lBlank ℓ) ((R o).simFig8.eval (fun _ => A o) ()))
  refine h12.trans ?_
  refine add_le_add (add_le_add ?_ ?_) ?_
  · refine le_of_eq (Finset.sum_congr rfl fun tL htL => ?_)
    rw [cka_boolDist_mix_eq_advantage, cka_boolDist_mix_eq_advantage,
      prng_boolDist_mix_eq_advantage,
      ← hCKAPriv i hi' tL htL, ← hCKAPrivU i hi' tL htL, ← hPRNGPriv i hi' tL htL]
  · exact fsMixBias_le_fsAeadMixtureBound_of_fsOk Z hD hℓ encT hinj hdum oa
      (fun o => idsOf (ida o) (idb o)) (min (2 * q) (q + 2)) q hqR32
      (fun o => (R o).fs) hFs _ _ (hFSPrivEq i hi') (hFSPrivOk i hi')
  · exact mul_le_mul_of_nonneg_left
      (fsMixBias_le_fsAeadMixtureBound_of_fsOk Z hD hℓ encT hinj hdum oa
        (fun o => idsOf (ida o) (idb o)) (min (2 * q) (q + 2)) q hqR32
        (fun o => (R o).fs) hFs _ _ (hFSPrivCoinEq i hi') (hFSPrivCoinOk i hi'))
      zero_le

private theorem sum_range_mul_mod_div (K m : ℕ) (g : ℕ → ℕ → ℝ≥0∞) :
    ∑ idx ∈ Finset.range (K * m), g (idx % m) (idx / m) =
      ∑ s ∈ Finset.range K, ∑ r ∈ Finset.range m, g r s := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr' : r < m := Finset.mem_range.mp hr
    have hm : 0 < m := by omega
    have hmod : (K * m + r) % m = r := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr']
    have hdiv : (K * m + r) / m = K := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt hr', Nat.zero_add]
    rw [hmod, hdiv]

theorem sum_two_modes_mod_div_eq_ico_range (a b q : ℕ) (f : ℕ → ℕ → ℝ≥0∞) :
    (∑ s ∈ Finset.range (b - a), f 0 (a + s)) +
        (∑ idx ∈ Finset.range ((b - a) * q), f (idx % q + 1) (a + idx / q)) =
      ∑ t ∈ Finset.Ico a b, ∑ j ∈ Finset.range (q + 1), f j t := by
  rw [sum_range_mul_mod_div (b - a) q (fun r s => f (r + 1) (a + s)),
      ← Finset.sum_add_distrib, Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_range_succ' (fun j => f j (a + s)) q, add_comm]

theorem sum_single_mode_mod_div_eq_ico_range (a b q : ℕ) (f : ℕ → ℕ → ℝ≥0∞) :
    ∑ idx ∈ Finset.range ((b - a) * (q + 1)), f (idx % (q + 1)) (a + idx / (q + 1)) =
      ∑ t ∈ Finset.Ico a b, ∑ j ∈ Finset.range (q + 1), f j t := by
  rw [sum_range_mul_mod_div (b - a) (q + 1) (fun j s => f j (a + s)),
      Finset.sum_Ico_eq_sum_range]

/-- Stage-2 mixture `bucketAuthGame` bound into `fig8MixShortAuthV1` from Hop 1 (`h9`), Hop 2
(`cka_branch_true_redCKAAuthBucket_mix_le_sum_two_mul_prng_add_par` + `hCKAAuth` + `hPRNGAuth`),
and Hop 3 (`hFSAuth`). -/
theorem fig8MixAuth_le_fig8MixShortAuthV1_of_fig8Eval {α : Type}
    (Z : Crypto) (K : CryptoVerification.LibsignalSpqrV1.MlKem)
    {ℓ : ℕ} (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) (oa : ProbComp α) (ida idb : α → IdentityKey)
    (R : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (A : α → CryptoGames.SM.Adversary (GhostState Bytes) (CryptoGames.CBC.Plain ℓ) (BitVec 512) Bytes)
    (h9 : ∀ tL ∈ admissibleLastLeakGuesses (2 + 1) ((qep + 1) + 1), ∀ o,
      _root_.CryptoGames.SM.BucketAuthBridge.bucketAuthAdvantage
        (lFig8 Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000 lam)
        (2 + 1) (qep + 1) tL
        (CryptoGames.SM.Thm1.challSim (2 + 1) (qep + 1) ((R o).simFig8.eval (fun _ => A o) ())) ≤
      𝒟[CryptoGames.CKA.branch (dhScheme Dh) 1 (healEpoch tL) false
        (_root_.Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.redCKAAuthBucket (dhScheme Dh) (rootPRNG Z.F encPt)
          (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL
          (CryptoGames.SM.Thm1.challSim (2 + 1) (qep + 1) ((R o).simFig8.eval (fun _ => A o) ())))] {true})
    (hCKAAuth : ∀ tL ∈ admissibleLastLeakGuesses (2 + 1) ((qep + 1) + 1),
      CryptoGames.CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
        (prefixAdvAvg oa fun o =>
          ((R o).fig8.redCKAAuth tL).eval
            (fun _ => (R o).fig8.challSim.eval (fun _ => (R o).simFig8.eval (fun _ => A o) ()) ()) ()) =
      CryptoGames.CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
        (prefixAdvAvg oa fun o =>
          _root_.Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.redCKAAuthBucket (dhScheme Dh) (rootPRNG Z.F encPt)
            (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL
            (CryptoGames.SM.Thm1.challSim (2 + 1) (qep + 1) ((R o).simFig8.eval (fun _ => A o) ()))))
    (hPRNGAuth : ∀ tL ∈ admissibleLastLeakGuesses (2 + 1) ((qep + 1) + 1),
      ∀ t ∈ Finset.Ico (healEpoch tL) ((qep + 1) + 2),
      CryptoGames.PRFPRNG.advantage (rootPRNG Z.F encPt)
        (prefixAdvAvg oa fun o =>
          redPRNGAuthBucketHybrid (dhScheme Dh) (rootPRNG Z.F encPt)
            (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL t
            (CryptoGames.SM.Thm1.challSim (2 + 1) (qep + 1) ((R o).simFig8.eval (fun _ => A o) ()))) ≤
      CryptoGames.PRFPRNG.advantage (rootPRNG Z.F encPt)
        (prefixAdvAvg oa fun o =>
          ((R o).fig8.redPRNGAuth tL t).eval
            (fun _ => (R o).fig8.challSim.eval (fun _ => (R o).simFig8.eval (fun _ => A o) ()) ()) ()))
    (hFSAuth : ∀ tL ∈ admissibleLastLeakGuesses (2 + 1) ((qep + 1) + 1),
      𝒟[oa >>= fun o =>
          localAuthBucketMainPar (dhScheme Dh) (rootPRNG Z.F encPt)
            (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL false
            (CryptoGames.SM.Thm1.challSim (2 + 1) (qep + 1) ((R o).simFig8.eval (fun _ => A o) ()))] {true} +
        𝒟[oa >>= fun o =>
          localAuthBucketMainPar (dhScheme Dh) (rootPRNG Z.F encPt)
            (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL true
            (CryptoGames.SM.Thm1.challSim (2 + 1) (qep + 1) ((R o).simFig8.eval (fun _ => A o) ()))] {true} +
        𝒟[oa >>= fun o =>
          localAuthBucketForgedHdrPar (dhScheme Dh) (rootPRNG Z.F encPt)
            (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL false
            (CryptoGames.SM.Thm1.challSim (2 + 1) (qep + 1) ((R o).simFig8.eval (fun _ => A o) ()))] {true} +
        𝒟[oa >>= fun o =>
          localAuthBucketForgedHdrPar (dhScheme Dh) (rootPRNG Z.F encPt)
            (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL true
            (CryptoGames.SM.Thm1.challSim (2 + 1) (qep + 1) ((R o).simFig8.eval (fun _ => A o) ()))] {true} ≤
      (∑ t ∈ Finset.Ico (healEpoch tL) ((qep + 1) + 2),
        ∑ j ∈ Finset.range (q + 1),
          fsAeadAuthMixtureCompBound Z protoSignalCodec ℓ oa (min (2 * q) (q + 2))
            (fun o => (R o).fs)
            (fun stage la o =>
              ((R o).fig8.redFSAuth stage la j tL t).eval
                (fun _ => (R o).fig8.challSim.eval (fun _ => (R o).simFig8.eval (fun _ => A o) ()) ()) ())) +
        8 * CryptoVerification.LibsignalSession.macForgeryTerm Z q) :
    2 * ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) ((qep + 1) + 1),
      𝒟[oa >>= fun o =>
        _root_.CryptoGames.SM.BucketAuthBridge.bucketAuthGame
          (lFig8 Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000 lam)
          (2 + 1) (qep + 1) tL
          (CryptoGames.SM.Thm1.challSim (2 + 1) (qep + 1) ((R o).simFig8.eval (fun _ => A o) ()))] {true} ≤
      fig8MixShortAuthV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb R A := by
  unfold fig8MixShortAuthV1
  dsimp only
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun tL htL => ?_) zero_le
  set B : α → Fig8Adv Pt ℓ := fun o =>
    CryptoGames.SM.Thm1.challSim (2 + 1) (qep + 1) ((R o).simFig8.eval (fun _ => A o) ())
  have hHop1 :
      𝒟[oa >>= fun o =>
          _root_.CryptoGames.SM.BucketAuthBridge.bucketAuthGame
            (lFig8 Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000 lam)
            (2 + 1) (qep + 1) tL (B o)] {true} ≤
        𝒟[oa >>= fun o =>
          CryptoGames.CKA.branch (dhScheme Dh) 1 (healEpoch tL) false
            (_root_.Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.redCKAAuthBucket (dhScheme Dh) (rootPRNG Z.F encPt)
              (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL (B o))] {true} :=
    _root_.CryptoGames.SM.Construction.AuthL11.evalDist_bind_mono oa _ _ fun o _ => h9 tL htL o
  set pT := 𝒟[oa >>= fun o =>
    CryptoGames.CKA.branch (dhScheme Dh) 1 (healEpoch tL) true
      (_root_.Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.redCKAAuthBucket (dhScheme Dh) (rootPRNG Z.F encPt)
        (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL (B o))]
  set pF := 𝒟[oa >>= fun o =>
    CryptoGames.CKA.branch (dhScheme Dh) 1 (healEpoch tL) false
      (_root_.Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.redCKAAuthBucket (dhScheme Dh) (rootPRNG Z.F encPt)
        (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL (B o))]
  have hSplitCKA : pF {true} ≤ pT.boolDist pF + pT {true} := by
    rw [MeasureTheory.Measure.boolDist_comm, add_comm]
    exact MeasureTheory.Measure.apply_true_le_add_boolDist pF pT
  have hCKAEq :
      pT.boolDist pF =
        CryptoGames.CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
          (prefixAdvAvg oa fun o =>
            ((R o).fig8.redCKAAuth tL).eval
              (fun _ => (R o).fig8.challSim.eval (fun _ => (R o).simFig8.eval (fun _ => A o) ()) ()) ()) := by
    rw [cka_boolDist_mix_eq_advantage, ← hCKAAuth tL htL]
  have hHop2 := cka_branch_true_redCKAAuthBucket_mix_le_sum_two_mul_prng_add_par
    (dhScheme Dh) (rootPRNG Z.F encPt) lam 1 (qep + 1) (dhScheme_correct Dh hDh) oa
    (fun o => lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) tL htL B
  have hPRNGSum :
      (∑ t ∈ Finset.Ico (healEpoch tL) ((qep + 1) + 2),
        2 * (𝒟[oa >>= fun o => CryptoGames.PRFPRNG.branch (rootPRNG Z.F encPt) true
              (redPRNGAuthBucketHybrid (dhScheme Dh) (rootPRNG Z.F encPt)
                (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL t (B o))].boolDist
          𝒟[oa >>= fun o => CryptoGames.PRFPRNG.branch (rootPRNG Z.F encPt) false
              (redPRNGAuthBucketHybrid (dhScheme Dh) (rootPRNG Z.F encPt)
                (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL t (B o))])) ≤
      ∑ t ∈ Finset.Ico (healEpoch tL) ((qep + 1) + 2),
        2 * CryptoGames.PRFPRNG.advantage (rootPRNG Z.F encPt)
          (prefixAdvAvg oa fun o =>
            ((R o).fig8.redPRNGAuth tL t).eval
              (fun _ => (R o).fig8.challSim.eval (fun _ => (R o).simFig8.eval (fun _ => A o) ()) ()) ()) := by
    refine Finset.sum_le_sum fun t ht => mul_le_mul_of_nonneg_left ?_ zero_le
    rw [prng_boolDist_mix_eq_advantage]
    exact hPRNGAuth tL htL t ht
  have hHop23 :
      pT {true} ≤
        (∑ t ∈ Finset.Ico (healEpoch tL) ((qep + 1) + 2),
            (2 * CryptoGames.PRFPRNG.advantage (rootPRNG Z.F encPt)
                (prefixAdvAvg oa fun o =>
                  ((R o).fig8.redPRNGAuth tL t).eval
                    (fun _ => (R o).fig8.challSim.eval (fun _ => (R o).simFig8.eval (fun _ => A o) ()) ()) ())
              + ∑ j ∈ Finset.range (q + 1),
                  fsAeadAuthMixtureCompBound Z protoSignalCodec ℓ oa (min (2 * q) (q + 2))
                    (fun o => (R o).fs)
                    (fun stage la o =>
                      ((R o).fig8.redFSAuth stage la j tL t).eval
                        (fun _ => (R o).fig8.challSim.eval (fun _ => (R o).simFig8.eval (fun _ => A o) ()) ()) ()))) +
          8 * CryptoVerification.LibsignalSession.macForgeryTerm Z q := by
    have hReassoc : ∀ s a b c d : ℝ≥0∞, s + a + b + c + d = s + (a + b + c + d) :=
      fun _ _ _ _ _ => by ac_rfl
    rw [hReassoc] at hHop2
    refine hHop2.trans ?_
    refine (add_le_add hPRNGSum (hFSAuth tL htL)).trans_eq ?_
    rw [← add_assoc, ← Finset.sum_add_distrib]
  refine (hHop1.trans hSplitCKA).trans ?_
  rw [hCKAEq, add_assoc]
  exact add_le_add le_rfl hHop23

end Helpers

end Computational.Proofs.E2E.Fig8Stage2MixHelpers
