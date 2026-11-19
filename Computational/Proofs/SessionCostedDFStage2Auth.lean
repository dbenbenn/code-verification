/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Session.StatementComposed
public import Computational.Proofs.SessionCostedFs -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.BucketAuthBridge -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SessionAuthBridge -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Defs -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridge -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.CKA.DHProof
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.SessionShort
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RestrictedReds
import Computational.Proofs.CryptoGames.SM.Theorem1
import Computational.Proofs.CryptoGames.SM.Theorem8.Stage2Bucket
import Computational.Proofs.E2E.Fig8Stage2MixHelpers
import Computational.Proofs.E2E.SignedFig8
import Computational.Proofs.E2E.SignedSession
import Computational.Proofs.E2E.SignedThm8
import Computational.Proofs.SessionCostedFig8.BundlesEval
public import Computational.Proofs.SessionCostedFig8.Bundles -- proof-setup: allow-public-import

/-!
# Drop-In Stage-2 Mixture Bucket Authenticity Bridges for `SessionCostedDF`

Provides:
1. Mixture (`oa : ProbComp α`) counterparts of `SessionCostedFig8.TopAssembly`'s multi-session
   FS-AEAD wrappers (`multiSessMix_two_modes_le_sum_fsAeadAuthMixtureCompBound_min`,
   `bucketMix_two_branch_fs_le`, `bucketMix_single_branch_fs_le`,
   `bucketMix_parity_two_branch_fs_le`, `bucketMix_four_branch_fs_le`) backed by
   `SessionAuthBridge.sessionHybrid_two_modes_le_sum_fsAeadAuthMixtureCompBound`.
2. Per-bucket Stage-2 mixture assembly (`bucketMixAuth_le_fig8MixAuthBucketTerm_of_hops` and
   `fig8MixBucketAuth_le_fig8MixShortAuthV1_of_bucket`) into `fig8MixShortAuthV1`.
3. Unchanged-signature drop-in proofs of `SessionCostedDF.boolBias_mixFig8_le_fig8MixShortV1`
   (`SessionCostedDF.lean:418–460`, via `BucketAuthBridge.lemma17_bucket_mix`) and
   `SessionCostedDF.evalDist_mixSimCNoneWin_le_fig8MixShortAuthV1` (`SessionCostedDF.lean:465–494`,
   via `BucketAuthBridge.run_win_prob_le_bucketAuth`).-/

set_option autoImplicit false

open OracleComp
open _root_.CryptoVerification.E2E.Signed.SessionRouter (sessLift lazyInit)
open _root_.CryptoVerification.E2E.Signed.SessionFS (fsInit fsImpl)
open _root_.CryptoGames.LibsignalSM.Proofs.Refinement (simCNoneWinEvent)

public section

open scoped ENNReal
open Computational.Proofs.E2E.SessionAuthBridge (MultiSessFsAdv RouterAdvCompat TwoModeMultiSessBounds authHopCutoff sessionHybrid_two_modes_le_sum_fsAeadAuthMixtureCompBound)
open Computational.Proofs.ReductionDsl.FsAtomicMacros (atomicShortB)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun dhScheme)
open CryptoGames.FSAEAD.Thm5 (hp)
open CryptoGames.LibsignalSM (Fig8Adv)
open CryptoGames.LibsignalSM.Proofs.Refinement (simCNoneWinEvent)
open CryptoGames.LibsignalSession (Crypto GhostState IdentityKey PublicKey)
open CryptoGames.Ratchet (rootPRNG)
open CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart dummyKey lAeadR lChainPRG lFig8 lIdeal)
open CryptoGames.SM (admissibleLastLeakGuesses)
open CryptoGames.SM.BucketAuthBridge (bucketAuthGame lemma17_bucket_mix run_win_prob_le_bucketAuth)
open CryptoGames.SM.Construction (healEpoch)
open CryptoVerification.E2E (Bytes SessionCostedReductions fig8MixShortAuthV1 fig8MixShortPrivV1 fsAeadAuthMixtureCompBound idsOf paramsV1 prefixAdvAvg)
open CryptoVerification.E2E.Signed (evalDist_bind_apply_le_sum_sum)
open CryptoVerification.E2E.Signed.SessionFS (fsImpl fsInit)
open CryptoVerification.E2E.Signed.SessionRouter (lazyInit sessLift)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSession (FsAdv FsCostedReds fsCostedRedsInst macForgeryTerm)

namespace Computational.Proofs.SessionCostedDFStage2Auth

/-! ### 1. Exact `Finset` `(t, j)` Reindexing Identities -/

theorem sum_range_mul_mod_div (K m : ℕ) (g : ℕ → ℕ → ℝ≥0∞) :
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

private theorem le_add_two_mul_of_two_mul_le_add_four_mul {X S M : ℝ≥0∞}
    (h : 2 * X ≤ S + 4 * M) :
    X ≤ S + 2 * M := by
  have h2ne0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2neTop : (2 : ℝ≥0∞) ≠ ⊤ := ENNReal.ofNat_ne_top
  rw [← ENNReal.mul_le_mul_iff_right h2ne0 h2neTop]
  calc
    2 * X ≤ S + 4 * M := h
    _ = 1 * S + 4 * M := by rw [one_mul]
    _ ≤ 2 * S + 4 * M := add_le_add (by gcongr; norm_num) le_rfl
    _ = 2 * (S + 2 * M) := by ring

/-! ### 2. Mixture Multi-Session FS-AEAD Step Wrappers (`SessionAuthBridge`) -/

/-- Real (`hp 0 0 la`) mixture win probability of a multi-session AD-level FS-AEAD adversary
`Adv la o` under prefix `oa : ProbComp α`. -/
@[expose] noncomputable def multiSessMixRealWinProb {Pt : Type} [DecidableEq Pt] {α : Type}
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (oa : ProbComp α) (idOf : α → CryptoGames.Party → IdentityKey)
    (Adv : Bool → α → MultiSessFsAdv Pt ℓ) (la : Bool) : ℝ≥0∞ :=
  𝒟[oa >>= fun o => Prod.fst <$> (simulateQ (sessLift
    (lazyInit fsInit (fsImpl
      (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT (idOf o))
      (lChainPRG C.F) 25000 (hp 0 0 la)))) (Adv la o)).run
    (fun _ => none)] {true}

/-- Ideal-cutoff (`hp N N la` where `N = authHopCutoff 25000 qR la`) mixture win probability of
`Adv la o` under prefix `oa : ProbComp α`. -/
@[expose] noncomputable def multiSessMixEndWinProb {Pt : Type} [DecidableEq Pt] {α : Type}
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (oa : ProbComp α) (idOf : α → CryptoGames.Party → IdentityKey)
    (qR : ℕ) (Adv : Bool → α → MultiSessFsAdv Pt ℓ) (la : Bool) : ℝ≥0∞ :=
  let N := authHopCutoff 25000 qR la
  𝒟[oa >>= fun o => Prod.fst <$> (simulateQ (sessLift
    (lazyInit fsInit (fsImpl
      (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT (idOf o))
      (lChainPRG C.F) 25000 (hp N N la)))) (Adv la o)).run
    (fun _ => none)] {true}

/-- Mixture multi-session family wrapper around
`SessionAuthBridge.sessionHybrid_two_modes_le_sum_fsAeadAuthMixtureCompBound` at
`qR = min (2 * q) (q + 2)` and `qd = q`, rewriting `4 * (q * macForgeryProb C.F)` to
`4 * macForgeryTerm C q`. -/
theorem multiSessMix_two_modes_le_sum_fsAeadAuthMixtureCompBound_min
    {Pt : Type} [DecidableEq Pt] {α : Type}
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (oa : ProbComp α) (idOf : α → CryptoGames.Party → IdentityKey)
    (M q : ℕ) (hq32 : 2 * q + 25002 < 2 ^ 32)
    (Rfs : ∀ o, FsCostedReds C protoSignalCodec ℓ encT (idOf o))
    (hRfs : ∀ o, Rfs o = fsCostedRedsInst C protoSignalCodec ℓ encT (idOf o) (min (2 * q) (q + 2)))
    (Adv : Bool → α → MultiSessFsAdv Pt ℓ)
    (A : Bool → Bool → ℕ → α → FsAdv Pt ℓ)
    (hℓ : ℓ < 10 ^ 6) (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (hbds : TwoModeMultiSessBounds 25000 (min (2 * q) (q + 2)) M q Adv)
    (hcompat : RouterAdvCompat C protoSignalCodec ℓ encT
      oa idOf 25000 (min (2 * q) (q + 2)) M Adv A)
    (hA : ∀ j < M, ∀ stage la o, CryptoGames.FSAEAD.MakesAtMostQueries (A stage la j o) (min (2 * q) (q + 2)))
    (hshort : ∀ j < M, ∀ stage la o,
      CryptoGames.FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1)
        (A stage la j o))
    (hendFalse : multiSessMixEndWinProb C ℓ encT oa idOf (min (2 * q) (q + 2)) Adv false = 0)
    (hendTrue : multiSessMixEndWinProb C ℓ encT oa idOf (min (2 * q) (q + 2)) Adv true = 0) :
    2 * (multiSessMixRealWinProb C ℓ encT oa idOf Adv false +
          multiSessMixRealWinProb C ℓ encT oa idOf Adv true) ≤
      (∑ j ∈ Finset.range M,
        fsAeadAuthMixtureCompBound C protoSignalCodec ℓ oa (min (2 * q) (q + 2)) Rfs
          (fun stage la o => A stage la j o)) +
      4 * macForgeryTerm C q := by
  have hcut : min (2 * q) (q + 2) + (25000 + 1) ≤ 2 ^ 32 := by omega
  rw [show Rfs = (fun o => fsCostedRedsInst C protoSignalCodec ℓ encT (idOf o) (min (2 * q) (q + 2)))
    from funext hRfs]
  exact sessionHybrid_two_modes_le_sum_fsAeadAuthMixtureCompBound C ℓ encT oa idOf
    (min (2 * q) (q + 2)) M q Adv A hℓ hinj hdum hcut hbds hcompat hA hshort hendFalse hendTrue

/-- Four-branch (`gMain ∈ {true, false}`, `par ∈ {false, true}`) mixture multi-session FS-AEAD
bound for a fixed bucket `tL` (`M = ((qepSm + 2) - healEpoch tL) * (q + 1)`): exact mixture
counterpart of `TopAssembly.bucket_four_branch_fs_le`. -/
theorem bucketMix_four_branch_fs_le
    {Pt : Type} [DecidableEq Pt] {α : Type}
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (oa : ProbComp α) (idOf : α → CryptoGames.Party → IdentityKey)
    (qepSm q : ℕ) (tL : Option ℕ) (hq32 : 2 * q + 25002 < 2 ^ 32)
    (Rfs : ∀ o, FsCostedReds C protoSignalCodec ℓ encT (idOf o))
    (hRfs : ∀ o, Rfs o = fsCostedRedsInst C protoSignalCodec ℓ encT (idOf o) (min (2 * q) (q + 2)))
    (AdvBr : Bool → Bool → Bool → α → MultiSessFsAdv Pt ℓ)
    (ABr : Bool → Bool → Bool → Bool → ℕ → α → FsAdv Pt ℓ)
    (A : Bool → Bool → ℕ → ℕ → α → FsAdv Pt ℓ)
    (hℓ : ℓ < 10 ^ 6) (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (hbds : ∀ gMain par, TwoModeMultiSessBounds 25000 (min (2 * q) (q + 2))
      (((qepSm + 2) - healEpoch tL) * (q + 1)) q (AdvBr gMain par))
    (hcompat : ∀ gMain par, RouterAdvCompat C protoSignalCodec ℓ encT
      oa idOf 25000 (min (2 * q) (q + 2)) (((qepSm + 2) - healEpoch tL) * (q + 1))
      (AdvBr gMain par) (ABr gMain par))
    (hendF : ∀ gMain par,
      multiSessMixEndWinProb C ℓ encT oa idOf (min (2 * q) (q + 2)) (AdvBr gMain par) false = 0)
    (hendT : ∀ gMain par,
      multiSessMixEndWinProb C ℓ encT oa idOf (min (2 * q) (q + 2)) (AdvBr gMain par) true = 0)
    (hABr : ∀ gMain par idx, idx < ((qepSm + 2) - healEpoch tL) * (q + 1) →
      ∀ stage la o, CryptoGames.FSAEAD.MakesAtMostQueries (ABr gMain par stage la idx o) (min (2 * q) (q + 2)))
    (hshort : ∀ gMain par idx, idx < ((qepSm + 2) - healEpoch tL) * (q + 1) →
      ∀ stage la o,
        CryptoGames.FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1)
          (ABr gMain par stage la idx o))
    (hActive : ∀ idx, idx < ((qepSm + 2) - healEpoch tL) * (q + 1) →
      ∀ stage la o,
        ABr (decide (idx % (q + 1) = 0))
          (decide (CryptoGames.Party.senderOf (healEpoch tL + idx / (q + 1)) == .A)) stage la idx o =
          A stage la (idx % (q + 1)) (healEpoch tL + idx / (q + 1)) o)
    (hZero : ∀ gMain par idx, idx < ((qepSm + 2) - healEpoch tL) * (q + 1) →
      ¬(decide (idx % (q + 1) = 0) = gMain ∧
        decide (CryptoGames.Party.senderOf (healEpoch tL + idx / (q + 1)) == .A) = par) →
      fsAeadAuthMixtureCompBound C protoSignalCodec ℓ oa (min (2 * q) (q + 2)) Rfs
        (fun stage la o => ABr gMain par stage la idx o) = 0) :
    (multiSessMixRealWinProb C ℓ encT oa idOf (AdvBr true false) false +
      multiSessMixRealWinProb C ℓ encT oa idOf (AdvBr true false) true) +
    (multiSessMixRealWinProb C ℓ encT oa idOf (AdvBr true true) false +
      multiSessMixRealWinProb C ℓ encT oa idOf (AdvBr true true) true) +
    (multiSessMixRealWinProb C ℓ encT oa idOf (AdvBr false false) false +
      multiSessMixRealWinProb C ℓ encT oa idOf (AdvBr false false) true) +
    (multiSessMixRealWinProb C ℓ encT oa idOf (AdvBr false true) false +
      multiSessMixRealWinProb C ℓ encT oa idOf (AdvBr false true) true) ≤
      (∑ t ∈ Finset.Ico (healEpoch tL) (qepSm + 2),
        ∑ j ∈ Finset.range (q + 1),
          fsAeadAuthMixtureCompBound C protoSignalCodec ℓ oa (min (2 * q) (q + 2)) Rfs
            (fun stage la o => A stage la j t o)) +
      8 * macForgeryTerm C q := by
  set M := ((qepSm + 2) - healEpoch tL) * (q + 1)
  have hTF := multiSessMix_two_modes_le_sum_fsAeadAuthMixtureCompBound_min C ℓ encT oa idOf M q hq32
    Rfs hRfs (AdvBr true false) (ABr true false) hℓ hinj hdum (hbds true false) (hcompat true false)
    (hABr true false) (hshort true false) (hendF true false) (hendT true false)
  have hTT := multiSessMix_two_modes_le_sum_fsAeadAuthMixtureCompBound_min C ℓ encT oa idOf M q hq32
    Rfs hRfs (AdvBr true true) (ABr true true) hℓ hinj hdum (hbds true true) (hcompat true true)
    (hABr true true) (hshort true true) (hendF true true) (hendT true true)
  have hFF := multiSessMix_two_modes_le_sum_fsAeadAuthMixtureCompBound_min C ℓ encT oa idOf M q hq32
    Rfs hRfs (AdvBr false false) (ABr false false) hℓ hinj hdum (hbds false false) (hcompat false false)
    (hABr false false) (hshort false false) (hendF false false) (hendT false false)
  have hFT := multiSessMix_two_modes_le_sum_fsAeadAuthMixtureCompBound_min C ℓ encT oa idOf M q hq32
    Rfs hRfs (AdvBr false true) (ABr false true) hℓ hinj hdum (hbds false true) (hcompat false true)
    (hABr false true) (hshort false true) (hendF false true) (hendT false true)
  have hSumIdx :
      ((∑ idx ∈ Finset.range M,
          fsAeadAuthMixtureCompBound C protoSignalCodec ℓ oa (min (2 * q) (q + 2)) Rfs
            (fun stage la o => ABr true false stage la idx o)) +
        (∑ idx ∈ Finset.range M,
          fsAeadAuthMixtureCompBound C protoSignalCodec ℓ oa (min (2 * q) (q + 2)) Rfs
            (fun stage la o => ABr true true stage la idx o))) +
      ((∑ idx ∈ Finset.range M,
          fsAeadAuthMixtureCompBound C protoSignalCodec ℓ oa (min (2 * q) (q + 2)) Rfs
            (fun stage la o => ABr false false stage la idx o)) +
        (∑ idx ∈ Finset.range M,
          fsAeadAuthMixtureCompBound C protoSignalCodec ℓ oa (min (2 * q) (q + 2)) Rfs
            (fun stage la o => ABr false true stage la idx o))) =
      ∑ idx ∈ Finset.range M,
        fsAeadAuthMixtureCompBound C protoSignalCodec ℓ oa (min (2 * q) (q + 2)) Rfs
          (fun stage la o => A stage la (idx % (q + 1)) (healEpoch tL + idx / (q + 1)) o) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun idx hidx => ?_
    have hidx' : idx < M := Finset.mem_range.mp hidx
    cases hg : decide (idx % (q + 1) = 0) <;>
      cases hp : decide (CryptoGames.Party.senderOf (healEpoch tL + idx / (q + 1)) == .A)
    · rw [hZero true false idx hidx' (by rw [hg, hp]; decide),
          hZero true true idx hidx' (by rw [hg, hp]; decide),
          hZero false true idx hidx' (by rw [hg, hp]; decide),
          add_zero, zero_add, add_zero]
      have hAct : (fun stage la o => ABr false false stage la idx o) =
          (fun stage la o => A stage la (idx % (q + 1)) (healEpoch tL + idx / (q + 1)) o) := by
        funext stage la o
        have h1 := hActive idx hidx' stage la o
        rwa [hg, hp] at h1
      rw [hAct]
    · rw [hZero true false idx hidx' (by rw [hg, hp]; decide),
          hZero true true idx hidx' (by rw [hg, hp]; decide),
          hZero false false idx hidx' (by rw [hg, hp]; decide),
          add_zero, zero_add, zero_add]
      have hAct : (fun stage la o => ABr false true stage la idx o) =
          (fun stage la o => A stage la (idx % (q + 1)) (healEpoch tL + idx / (q + 1)) o) := by
        funext stage la o
        have h1 := hActive idx hidx' stage la o
        rwa [hg, hp] at h1
      rw [hAct]
    · rw [hZero true true idx hidx' (by rw [hg, hp]; decide),
          hZero false false idx hidx' (by rw [hg, hp]; decide),
          hZero false true idx hidx' (by rw [hg, hp]; decide),
          add_zero, add_zero, add_zero]
      have hAct : (fun stage la o => ABr true false stage la idx o) =
          (fun stage la o => A stage la (idx % (q + 1)) (healEpoch tL + idx / (q + 1)) o) := by
        funext stage la o
        have h1 := hActive idx hidx' stage la o
        rwa [hg, hp] at h1
      rw [hAct]
    · rw [hZero true false idx hidx' (by rw [hg, hp]; decide),
          hZero false false idx hidx' (by rw [hg, hp]; decide),
          hZero false true idx hidx' (by rw [hg, hp]; decide),
          zero_add, add_zero, add_zero]
      have hAct : (fun stage la o => ABr true true stage la idx o) =
          (fun stage la o => A stage la (idx % (q + 1)) (healEpoch tL + idx / (q + 1)) o) := by
        funext stage la o
        have h1 := hActive idx hidx' stage la o
        rwa [hg, hp] at h1
      rw [hAct]
  have h2 :
      2 * ((multiSessMixRealWinProb C ℓ encT oa idOf (AdvBr true false) false +
            multiSessMixRealWinProb C ℓ encT oa idOf (AdvBr true false) true) +
          (multiSessMixRealWinProb C ℓ encT oa idOf (AdvBr true true) false +
            multiSessMixRealWinProb C ℓ encT oa idOf (AdvBr true true) true) +
          (multiSessMixRealWinProb C ℓ encT oa idOf (AdvBr false false) false +
            multiSessMixRealWinProb C ℓ encT oa idOf (AdvBr false false) true) +
          (multiSessMixRealWinProb C ℓ encT oa idOf (AdvBr false true) false +
            multiSessMixRealWinProb C ℓ encT oa idOf (AdvBr false true) true)) ≤
        (∑ t ∈ Finset.Ico (healEpoch tL) (qepSm + 2),
          ∑ j ∈ Finset.range (q + 1),
            fsAeadAuthMixtureCompBound C protoSignalCodec ℓ oa (min (2 * q) (q + 2)) Rfs
              (fun stage la o => A stage la j t o)) +
        4 * (4 * macForgeryTerm C q) := by
    have hMul4 : ∀ w x y z : ℝ≥0∞, 2 * (w + x + y + z) = 2 * w + 2 * x + 2 * y + 2 * z := by
      intro w x y z; ring
    rw [hMul4]
    calc
      2 * (multiSessMixRealWinProb C ℓ encT oa idOf (AdvBr true false) false +
            multiSessMixRealWinProb C ℓ encT oa idOf (AdvBr true false) true) +
        2 * (multiSessMixRealWinProb C ℓ encT oa idOf (AdvBr true true) false +
            multiSessMixRealWinProb C ℓ encT oa idOf (AdvBr true true) true) +
        2 * (multiSessMixRealWinProb C ℓ encT oa idOf (AdvBr false false) false +
            multiSessMixRealWinProb C ℓ encT oa idOf (AdvBr false false) true) +
        2 * (multiSessMixRealWinProb C ℓ encT oa idOf (AdvBr false true) false +
            multiSessMixRealWinProb C ℓ encT oa idOf (AdvBr false true) true)
        ≤ ((∑ idx ∈ Finset.range M,
              fsAeadAuthMixtureCompBound C protoSignalCodec ℓ oa (min (2 * q) (q + 2)) Rfs
                (fun stage la o => ABr true false stage la idx o)) + 4 * macForgeryTerm C q) +
          ((∑ idx ∈ Finset.range M,
              fsAeadAuthMixtureCompBound C protoSignalCodec ℓ oa (min (2 * q) (q + 2)) Rfs
                (fun stage la o => ABr true true stage la idx o)) + 4 * macForgeryTerm C q) +
          ((∑ idx ∈ Finset.range M,
              fsAeadAuthMixtureCompBound C protoSignalCodec ℓ oa (min (2 * q) (q + 2)) Rfs
                (fun stage la o => ABr false false stage la idx o)) + 4 * macForgeryTerm C q) +
          ((∑ idx ∈ Finset.range M,
              fsAeadAuthMixtureCompBound C protoSignalCodec ℓ oa (min (2 * q) (q + 2)) Rfs
                (fun stage la o => ABr false true stage la idx o)) + 4 * macForgeryTerm C q) :=
          add_le_add (add_le_add (add_le_add hTF hTT) hFF) hFT
      _ = (((∑ idx ∈ Finset.range M,
              fsAeadAuthMixtureCompBound C protoSignalCodec ℓ oa (min (2 * q) (q + 2)) Rfs
                (fun stage la o => ABr true false stage la idx o)) +
            (∑ idx ∈ Finset.range M,
              fsAeadAuthMixtureCompBound C protoSignalCodec ℓ oa (min (2 * q) (q + 2)) Rfs
                (fun stage la o => ABr true true stage la idx o))) +
          ((∑ idx ∈ Finset.range M,
              fsAeadAuthMixtureCompBound C protoSignalCodec ℓ oa (min (2 * q) (q + 2)) Rfs
                (fun stage la o => ABr false false stage la idx o)) +
            (∑ idx ∈ Finset.range M,
              fsAeadAuthMixtureCompBound C protoSignalCodec ℓ oa (min (2 * q) (q + 2)) Rfs
                (fun stage la o => ABr false true stage la idx o)))) +
            4 * (4 * macForgeryTerm C q) := by ring
      _ = _ := by
          rw [hSumIdx, sum_single_mode_mod_div_eq_ico_range (healEpoch tL) (qepSm + 2) q
            (fun j t => fsAeadAuthMixtureCompBound C protoSignalCodec ℓ oa (min (2 * q) (q + 2)) Rfs
              (fun stage la o => A stage la j t o))]
  have hCancel := le_add_two_mul_of_two_mul_le_add_four_mul h2
  refine hCancel.trans (add_le_add le_rfl ?_)
  exact le_of_eq (by ring)

/-! ### 3. `fig8MixShortAuthV1` Per-Bucket Decomposition & Top-Level `SessionCostedDF` Corollaries -/

section TopMixAuth

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

/-- Per-`tL` summand of `fig8MixShortAuthV1` (`StatementComposed.lean:641–660`). -/
@[expose] noncomputable def fig8MixAuthBucketTerm {α : Type}
    (Z : Crypto) (K : CryptoVerification.LibsignalSpqrV1.MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep q : ℕ) (oa : ProbComp α) (ida idb : α → IdentityKey)
    (R : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (A : α → CryptoGames.SM.Adversary (GhostState Bytes) (CryptoGames.CBC.Plain ℓ) (BitVec 512) Bytes)
    (tL : Option ℕ) : ℝ≥0∞ :=
  let qR := min (2 * q) (q + 2)
  let cka := dhScheme Dh
  let prng := rootPRNG Z.F encPt
  let simA := fun o => (R o).simFig8.eval (fun _ => A o) ()
  let authB := fun o => (R o).fig8.challSim.eval (fun _ => simA o) ()
  CryptoGames.CKA.advantage cka 1 (healEpoch tL)
      (prefixAdvAvg oa fun o => ((R o).fig8.redCKAAuth tL).eval (fun _ => authB o) ())
    + (∑ t ∈ Finset.Ico (healEpoch tL) ((qep + 1) + 2),
        (2 * CryptoGames.PRFPRNG.advantage prng
            (prefixAdvAvg oa fun o => ((R o).fig8.redPRNGAuth tL t).eval (fun _ => authB o) ())
          + ∑ j ∈ Finset.range (q + 1),
              fsAeadAuthMixtureCompBound Z protoSignalCodec ℓ oa qR (fun o => (R o).fs)
                (fun stage la o => ((R o).fig8.redFSAuth stage la j tL t).eval (fun _ => authB o) ())))
    + 8 * macForgeryTerm Z q

theorem fig8MixShortAuthV1_eq_two_mul_sum_bucketTerm {α : Type}
    (Z : Crypto) (K : CryptoVerification.LibsignalSpqrV1.MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep q : ℕ) (oa : ProbComp α) (ida idb : α → IdentityKey)
    (R : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (A : α → CryptoGames.SM.Adversary (GhostState Bytes) (CryptoGames.CBC.Plain ℓ) (BitVec 512) Bytes) :
    fig8MixShortAuthV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb R A =
      2 * ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) ((qep + 1) + 1),
        fig8MixAuthBucketTerm Z K ℓ Dh encPt encT decT lam qep q oa ida idb R A tL := by
  unfold fig8MixShortAuthV1 fig8MixAuthBucketTerm
  rfl

private theorem evalDist_bind_apply_le_sum {α κ : Type} (oa : ProbComp α)
    (f : α → ProbComp Bool) (u : Finset κ) (g : κ → α → ProbComp Bool)
    (H : ∀ a, 𝒟[f a] {true} ≤ ∑ k ∈ u, 𝒟[g k a] {true}) :
    𝒟[oa >>= f] {true} ≤ ∑ k ∈ u, 𝒟[oa >>= g k] {true} := by
  simpa only [Finset.sum_singleton] using
    evalDist_bind_apply_le_sum_sum oa f ({()} : Finset Unit) (fun _ => u) (fun _ => g)
      (fun a => by simpa only [Finset.sum_singleton] using H a)

/-- Drop-in unchanged-signature proof of `SessionCostedDF.boolBias_mixFig8_le_fig8MixShortV1`
(`SessionCostedDF.lean:418–460`) via `BucketAuthBridge.lemma17_bucket_mix`. -/
theorem boolBias_mixFig8_le_fig8MixShortV1_of_bucketAndPriv {α : Type}
    (Z : Crypto) (K : CryptoVerification.LibsignalSpqrV1.MlKem)
    {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep q : ℕ) (oa : ProbComp α) (ida idb : α → IdentityKey)
    (R : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (A : α → CryptoGames.SM.Adversary (GhostState Bytes) (CryptoGames.CBC.Plain ℓ) (BitVec 512) Bytes)
    (hq : ∀ o, CryptoGames.SM.MakesAtMostQueries (A o) q)
    (hBucketAuth :
      let simAdv : α → Fig8Adv Pt ℓ := fun o =>
        (Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog.simFig8RedProg
          ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).eval (fun _ => A o) ()
      2 * ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) ((qep + 1) + 1),
          𝒟[oa >>= fun o => bucketAuthGame
            (lFig8 Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000 lam)
            (2 + 1) (qep + 1) tL (CryptoGames.SM.Thm1.challSim (2 + 1) (qep + 1) (simAdv o))] {true} ≤
        fig8MixShortAuthV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb R A)
    (hPriv :
      let simAdv : α → Fig8Adv Pt ℓ := fun o =>
        (Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog.simFig8RedProg
          ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).eval (fun _ => A o) ()
      𝒟[oa >>= fun o => CryptoGames.SM.game (lFig8 Dh encPt Z protoSignalCodec ℓ encT
          (idsOf (ida o) (idb o)) 25000 lam) (2 + 1) (qep + 1) CryptoGames.SM.Config.h2 (simAdv o)].boolBias ≤
        fig8MixShortPrivV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb R A) :
    𝒟[oa >>= fun o => CryptoGames.SM.game (lFig8 Dh encPt Z protoSignalCodec ℓ encT
        (idsOf (ida o) (idb o)) 25000 lam) 3 (qep + 1) CryptoGames.SM.Config.h1
        (CryptoGames.LibsignalSM.Refine.libsignalToModularSchemeSim (paramsV1 Z K (ida o) (idb o)) ℓ Dh encPt encT decT
          (idsOf (ida o) (idb o)) lam qep (A o))].boolBias ≤
      fig8MixShortAuthV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb R A +
      fig8MixShortPrivV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb R A := by
  let simAdv : α → Fig8Adv Pt ℓ := fun o =>
    (Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog.simFig8RedProg
      ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).eval (fun _ => A o) ()
  have hGame :
      (oa >>= fun o => CryptoGames.SM.game (lFig8 Dh encPt Z protoSignalCodec ℓ encT
        (idsOf (ida o) (idb o)) 25000 lam) 3 (qep + 1) CryptoGames.SM.Config.h1
        (CryptoGames.LibsignalSM.Refine.libsignalToModularSchemeSim (paramsV1 Z K (ida o) (idb o)) ℓ Dh encPt encT decT
          (idsOf (ida o) (idb o)) lam qep (A o))) =
      (oa >>= fun o => CryptoGames.SM.game (lFig8 Dh encPt Z protoSignalCodec ℓ encT
        (idsOf (ida o) (idb o)) 25000 lam) (2 + 1) (qep + 1) CryptoGames.SM.Config.h1 (simAdv o)) :=
    bind_congr fun o =>
      (Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog.simFig8RedProg_sm_game_eq
        hℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q CryptoGames.SM.Config.h1 (A o) (hq o)).symm
  rw [hGame]
  have h17 := lemma17_bucket_mix
    (fun o => lFig8 Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000 lam)
    (2 + 1) (qep + 1) (by omega) oa simAdv
  calc _ ≤ _ := h17
    _ ≤ fig8MixShortPrivV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb R A +
        fig8MixShortAuthV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb R A :=
      add_le_add hPriv hBucketAuth
    _ = _ := add_comm _ _

/-- Drop-in unchanged-signature proof of
`SessionCostedDF.evalDist_mixSimCNoneWin_le_fig8MixShortAuthV1` (`SessionCostedDF.lean:465–494`)
via `BucketAuthBridge.run_win_prob_le_bucketAuth`. -/
theorem evalDist_mixSimCNoneWin_le_fig8MixShortAuthV1_of_bucket {α : Type}
    (Z : Crypto) (K : CryptoVerification.LibsignalSpqrV1.MlKem)
    {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep q : ℕ) (oa : ProbComp α) (ida idb : α → IdentityKey)
    (R : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (A : α → CryptoGames.SM.Adversary (GhostState Bytes) (CryptoGames.CBC.Plain ℓ) (BitVec 512) Bytes)
    (hq : ∀ o, CryptoGames.SM.MakesAtMostQueries (A o) q)
    (hBucketAuth :
      let simAdv : α → Fig8Adv Pt ℓ := fun o =>
        (Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog.simFig8RedProg
          ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).eval (fun _ => A o) ()
      2 * ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) ((qep + 1) + 1),
          𝒟[oa >>= fun o => bucketAuthGame
            (lFig8 Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000 lam)
            (2 + 1) (qep + 1) tL (CryptoGames.SM.Thm1.challSim (2 + 1) (qep + 1) (simAdv o))] {true} ≤
        fig8MixShortAuthV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb R A) :
    2 * 𝒟[oa >>= fun o => simCNoneWinEvent (paramsV1 Z K (ida o) (idb o)) ℓ Dh encPt encT decT
        (idsOf (ida o) (idb o)) lam qep (A o)] {true} ≤
      fig8MixShortAuthV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb R A := by
  let simAdv : α → Fig8Adv Pt ℓ := fun o =>
    (Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog.simFig8RedProg
      ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).eval (fun _ => A o) ()
  have hWin :
      𝒟[oa >>= fun o => simCNoneWinEvent (paramsV1 Z K (ida o) (idb o)) ℓ Dh encPt encT decT
          (idsOf (ida o) (idb o)) lam qep (A o)] {true} ≤
        ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) ((qep + 1) + 1),
          𝒟[oa >>= fun o => bucketAuthGame (lFig8 Dh encPt Z protoSignalCodec ℓ encT
            (idsOf (ida o) (idb o)) 25000 lam) (2 + 1) (qep + 1) tL
            (CryptoGames.SM.Thm1.challSim (2 + 1) (qep + 1) (simAdv o))] {true} :=
    evalDist_bind_apply_le_sum oa _ _ _ fun o => by
      rw [Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog.simFig8RedProg_simCNoneWinEvent_eq
        hℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q (A o) (hq o)]
      exact run_win_prob_le_bucketAuth
        (lFig8 Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000 lam)
        (2 + 1) (qep + 1) (by omega) (simAdv o)
  exact (mul_le_mul_right hWin 2).trans hBucketAuth

section Stage2InstBridge

open Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth
  (localAuthBucketForgedHdrPar localAuthBucketMainPar redCKAAuthBucket redPRNGAuthBucketHybrid)
open Computational.Proofs.E2E.SessionAuthBridge (multiSessPubToAD)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog
  (simFig8RedProg simFig8RedProg_guardedSMShort simFig8RedProg_queries simFig8RedProg_sendAtomicShort)
open Computational.Proofs.ReductionDsl.Fig8Atomic (atomicShortPubB)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeBase
  (redFSAuthMultiBucketAtomic redFSAuthMultiBucketAtomic_fsOk_and_encAtomicShort
   redFSAuthMultiBucketAtomic_inactive_fsAeadAuthMixtureCompBound_eq_zero
   redFSAuthMultiBucketAtomic_makesAtMostQueries redFSAuthMultiBucketAtomic_routerAdvCompat
   redFSAuthMultiBucketProg_twoModeMultiSessBounds redFSAuthMultiBucketShallow)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHop
  (localAuthBucketMainPar_le_multiSessRealWinProb)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeForgedHop
  (localAuthBucketForgedHdrPar_le_multiSessRealWinProb)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeEndMix
  (multiSessEndWinProbMix_redFSAuthMultiBucket_eq_zero)
open _root_.CryptoGames.LibsignalSession (maxForwardJumps)
open _root_.CryptoGames.Ratchet.LibsignalInst (lFS)
open _root_.CryptoGames.SM.Thm1 (challSim challSim_queries)

local instance : Inhabited Pt := ⟨0⟩

private theorem evalDist_bind_le_add_mix {α : Type} (p : ProbComp α)
    (F G₁ G₂ : α → ProbComp Bool)
    (h : ∀ a, 𝒟[F a] {true} ≤ 𝒟[G₁ a] {true} + 𝒟[G₂ a] {true}) :
    𝒟[p >>= F] {true} ≤ 𝒟[p >>= G₁] {true} + 𝒟[p >>= G₂] {true} := by
  simpa only [Finset.sum_pair Bool.false_ne_true] using
    (evalDist_bind_apply_le_sum p F ({false, true} : Finset Bool)
      (fun b : Bool => Bool.rec (motive := fun _ => α → ProbComp Bool) G₁ G₂ b) fun a => by
        simpa only [Finset.sum_pair Bool.false_ne_true] using h a)

omit [Zero Pt] [SampleableType Pt] in
private theorem multiSessRealWinProb_eq_realComp {α : Type}
    (Z : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : α → CryptoGames.Party → IdentityKey)
    (X : Bool → α → MultiSessFsAdv Pt ℓ) (la : Bool) (o : α) :
    SessionCostedFig8.TopAssembly.multiSessRealWinProb Z ℓ encT (idOf o) (fun la' => X la' o) la =
      𝒟[Prod.fst <$> (simulateQ (sessLift
        (lazyInit fsInit (fsImpl (lIdeal Z protoSignalCodec ℓ encT)
          (lAeadR Z protoSignalCodec ℓ encT (idOf o)) (lChainPRG Z.F) 25000 (hp 0 0 la))))
        (X la o)).run (fun _ => none)] {true} := rfl

omit [Zero Pt] [SampleableType Pt] in
private theorem evalDist_bind_le_multiSessMixRealWinProb {α : Type}
    (Z : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (oa : ProbComp α) (idOf : α → CryptoGames.Party → IdentityKey)
    (P : α → ProbComp Bool) (X : Bool → α → MultiSessFsAdv Pt ℓ)
    (h : ∀ o, 𝒟[P o] {true} ≤
      SessionCostedFig8.TopAssembly.multiSessRealWinProb Z ℓ encT (idOf o) (fun la => X la o) false +
        SessionCostedFig8.TopAssembly.multiSessRealWinProb Z ℓ encT (idOf o) (fun la => X la o) true) :
    𝒟[oa >>= P] {true} ≤
      multiSessMixRealWinProb Z ℓ encT oa idOf X false +
        multiSessMixRealWinProb Z ℓ encT oa idOf X true :=
  evalDist_bind_le_add_mix oa P
    (fun o => Prod.fst <$> (simulateQ (sessLift
      (lazyInit fsInit (fsImpl (lIdeal Z protoSignalCodec ℓ encT)
        (lAeadR Z protoSignalCodec ℓ encT (idOf o)) (lChainPRG Z.F) 25000 (hp 0 0 false))))
      (X false o)).run (fun _ => none))
    (fun o => Prod.fst <$> (simulateQ (sessLift
      (lazyInit fsInit (fsImpl (lIdeal Z protoSignalCodec ℓ encT)
        (lAeadR Z protoSignalCodec ℓ encT (idOf o)) (lChainPRG Z.F) 25000 (hp 0 0 true))))
      (X true o)).run (fun _ => none))
    fun o => by simpa only [multiSessRealWinProb_eq_realComp] using h o

omit [Zero Pt] [SampleableType Pt] in
private theorem multiSessMixEndWinProb_eq_zero_of_mfj {α : Type}
    (Z : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (oa : ProbComp α) (idOf : α → CryptoGames.Party → IdentityKey)
    (qR : ℕ) (X : Bool → α → MultiSessFsAdv Pt ℓ) (la : Bool)
    (h : 𝒟[oa >>= fun o => Prod.fst <$> (simulateQ (sessLift
        (lazyInit fsInit (fsImpl (lIdeal Z protoSignalCodec ℓ encT)
          (lAeadR Z protoSignalCodec ℓ encT (idOf o)) (lChainPRG Z.F) maxForwardJumps
          (hp (authHopCutoff maxForwardJumps qR la) (authHopCutoff maxForwardJumps qR la) la))))
        (X la o)).run (fun _ => none)] {true} = 0) :
    multiSessMixEndWinProb Z ℓ encT oa idOf qR X la = 0 := h

omit [Zero Pt] [SampleableType Pt] in
private theorem twoModeMultiSessBounds_of_mfj {α : Type} {ℓ : ℕ}
    (qR M q : ℕ) (X : Bool → α → MultiSessFsAdv Pt ℓ)
    (h : TwoModeMultiSessBounds maxForwardJumps qR M q X) :
    TwoModeMultiSessBounds 25000 qR M q X := h

omit [Zero Pt] [SampleableType Pt] in
private theorem routerAdvCompat_of_mfj {α : Type}
    (Z : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (oa : ProbComp α) (idOf : α → CryptoGames.Party → IdentityKey)
    (qR M : ℕ) (X : Bool → α → MultiSessFsAdv Pt ℓ) (Y : Bool → Bool → ℕ → α → FsAdv Pt ℓ)
    (h : RouterAdvCompat Z protoSignalCodec ℓ encT oa idOf maxForwardJumps qR M X Y) :
    RouterAdvCompat Z protoSignalCodec ℓ encT oa idOf 25000 qR M X Y := h

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem encMsgsOk_atomicShortB_of_pubB {ℓ : ℕ} (Y : FsAdv Pt ℓ)
    (h : CryptoGames.FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) Y) :
    CryptoGames.FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) Y := h

/-- Complete packaged Stage-2 Mixture Hop-3 `(tL)`-bucket FS-AEAD + MAC bound combining
`BucketFSAuthBridge.localAuthBucket{Main,ForgedHdr}Par_le_multiSessRealWinProb` and
`bucketMix_four_branch_fs_le`, directly discharging `hFSAuth` of
`Fig8Stage2MixHelpers.fig8MixAuth_le_fig8MixShortAuthV1_of_fig8Eval` over any prefix `oa`. -/
theorem localAuthBucketMix_par_le_sum_fsAeadAuthMixtureCompBound {α : Type}
    (Z : Crypto) (hD : ∀ k x, Z.D k (Z.E k x) = x)
    {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (oa : ProbComp α) (idOf : α → CryptoGames.Party → IdentityKey) (lam : Pt)
    (qepSm q : ℕ) (hq32 : 2 * q + 25002 < 2 ^ 32)
    (Rfs : ∀ o, FsCostedReds Z protoSignalCodec ℓ encT (idOf o))
    (hRfs : ∀ o, Rfs o = fsCostedRedsInst Z protoSignalCodec ℓ encT (idOf o) (min (2 * q) (q + 2)))
    (tL : Option ℕ) (B : α → Fig8Adv Pt ℓ)
    (hq : ∀ o, CryptoGames.SM.MakesAtMostQueries (B o) q)
    (heq : ∀ o, CryptoGames.SM.EqualPubChalls (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1) (B o))
    (hsh : ∀ o, CryptoGames.LibsignalSM.Proofs.SessionShort.FSAEADRed.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) (B o))
    (hg : ∀ o, CryptoGames.LibsignalSM.Proofs.SessionShort.GuardedSMShort (B o))
    (F : Bool → Bool → ℕ → ℕ → α → FsAdv Pt ℓ)
    (hActive : ∀ j t, j < q + 1 → healEpoch tL ≤ t → t < qepSm + 2 →
      ∀ stage la o,
        (redFSAuthMultiBucketAtomic ℓ Pt Z Dh encPt encT (idOf o) lam stage la
          ((q + 1) * (t - healEpoch tL) + j) qepSm (min (2 * q) (q + 2))
          ((q + 1) * (maxForwardJumps + 1)) (q + 1) (decide (j = 0)) tL
          (decide (CryptoGames.Party.senderOf t == .A))).eval (fun _ => B o) () =
        F stage la j t o) :
    𝒟[oa >>= fun o => localAuthBucketMainPar (dhScheme Dh) (rootPRNG Z.F encPt)
        (lFS Z protoSignalCodec ℓ encT (idOf o) 25000) lam 1 qepSm tL false (B o)] {true} +
      𝒟[oa >>= fun o => localAuthBucketMainPar (dhScheme Dh) (rootPRNG Z.F encPt)
        (lFS Z protoSignalCodec ℓ encT (idOf o) 25000) lam 1 qepSm tL true (B o)] {true} +
      𝒟[oa >>= fun o => localAuthBucketForgedHdrPar (dhScheme Dh) (rootPRNG Z.F encPt)
        (lFS Z protoSignalCodec ℓ encT (idOf o) 25000) lam 1 qepSm tL false (B o)] {true} +
      𝒟[oa >>= fun o => localAuthBucketForgedHdrPar (dhScheme Dh) (rootPRNG Z.F encPt)
        (lFS Z protoSignalCodec ℓ encT (idOf o) 25000) lam 1 qepSm tL true (B o)] {true} ≤
      (∑ t ∈ Finset.Ico (healEpoch tL) (qepSm + 2), ∑ j ∈ Finset.range (q + 1),
        fsAeadAuthMixtureCompBound Z protoSignalCodec ℓ oa (min (2 * q) (q + 2)) Rfs
          (fun stage la o => F stage la j t o)) + 8 * macForgeryTerm Z q := by
  have hmfj : (25000 : ℕ) = maxForwardJumps := rfl
  conv_lhs => simp only [hmfj]
  let B0 := (q + 1) * (maxForwardJumps + 1)
  let qR := min (2 * q) (q + 2)
  let AdvBr : Bool → Bool → Bool → α → MultiSessFsAdv Pt ℓ := fun gMain par la o =>
    multiSessPubToAD protoSignalCodec
      ((redFSAuthMultiBucketShallow ℓ Pt Z Dh encPt encT (idOf o) lam (q + 1) B0 qepSm gMain la tL par).eval
        (fun _ => B o) ())
  let ABr : Bool → Bool → Bool → Bool → ℕ → α → FsAdv Pt ℓ := fun gMain par stage la idx o =>
    (redFSAuthMultiBucketAtomic ℓ Pt Z Dh encPt encT (idOf o) lam stage la idx qepSm qR B0 (q + 1) gMain tL par).eval
      (fun _ => B o) ()
  have hMF := evalDist_bind_le_multiSessMixRealWinProb Z ℓ encT oa idOf
    (fun o => localAuthBucketMainPar (dhScheme Dh) (rootPRNG Z.F encPt)
      (lFS Z protoSignalCodec ℓ encT (idOf o) maxForwardJumps) lam 1 qepSm tL false (B o))
    (AdvBr true false) fun o =>
      localAuthBucketMainPar_le_multiSessRealWinProb ℓ Pt Z Dh hDh hD encPt encT hinj hdum
        (idOf o) lam hℓ q B0 qepSm rfl tL false (B o) (hq o) (hsh o)
  have hMT := evalDist_bind_le_multiSessMixRealWinProb Z ℓ encT oa idOf
    (fun o => localAuthBucketMainPar (dhScheme Dh) (rootPRNG Z.F encPt)
      (lFS Z protoSignalCodec ℓ encT (idOf o) maxForwardJumps) lam 1 qepSm tL true (B o))
    (AdvBr true true) fun o =>
      localAuthBucketMainPar_le_multiSessRealWinProb ℓ Pt Z Dh hDh hD encPt encT hinj hdum
        (idOf o) lam hℓ q B0 qepSm rfl tL true (B o) (hq o) (hsh o)
  have hFF := evalDist_bind_le_multiSessMixRealWinProb Z ℓ encT oa idOf
    (fun o => localAuthBucketForgedHdrPar (dhScheme Dh) (rootPRNG Z.F encPt)
      (lFS Z protoSignalCodec ℓ encT (idOf o) maxForwardJumps) lam 1 qepSm tL false (B o))
    (AdvBr false false) fun o =>
      localAuthBucketForgedHdrPar_le_multiSessRealWinProb ℓ Pt Z Dh hDh hD encPt encT hinj hdum
        (idOf o) lam hℓ q B0 qepSm rfl tL false (B o) (hq o) (hsh o)
  have hFT := evalDist_bind_le_multiSessMixRealWinProb Z ℓ encT oa idOf
    (fun o => localAuthBucketForgedHdrPar (dhScheme Dh) (rootPRNG Z.F encPt)
      (lFS Z protoSignalCodec ℓ encT (idOf o) maxForwardJumps) lam 1 qepSm tL true (B o))
    (AdvBr false true) fun o =>
      localAuthBucketForgedHdrPar_le_multiSessRealWinProb ℓ Pt Z Dh hDh hD encPt encT hinj hdum
        (idOf o) lam hℓ q B0 qepSm rfl tL true (B o) (hq o) (hsh o)
  refine (add_le_add (add_le_add (add_le_add hMF hMT) hFF) hFT).trans ?_
  refine bucketMix_four_branch_fs_le Z ℓ encT oa idOf qepSm q tL hq32 Rfs hRfs AdvBr ABr F hℓ hinj hdum
    (fun gMain par => twoModeMultiSessBounds_of_mfj qR (((qepSm + 2) - healEpoch tL) * (q + 1)) q
      (AdvBr gMain par) (redFSAuthMultiBucketProg_twoModeMultiSessBounds oa ℓ Pt Z Dh encPt encT idOf
        (fun _ => lam) hℓ q B0 qepSm gMain tL par B hq heq hsh hg))
    (fun gMain par => routerAdvCompat_of_mfj Z ℓ encT oa idOf qR (((qepSm + 2) - healEpoch tL) * (q + 1))
      (AdvBr gMain par) (ABr gMain par) (redFSAuthMultiBucketAtomic_routerAdvCompat oa ℓ Pt Z Dh encPt encT
        idOf (fun _ => lam) hℓ hinj q B0 qepSm rfl gMain tL par B (fun o _ => hq o) (fun o _ => hsh o)))
    (fun gMain par => multiSessMixEndWinProb_eq_zero_of_mfj Z ℓ encT oa idOf qR (AdvBr gMain par) false
      (multiSessEndWinProbMix_redFSAuthMultiBucket_eq_zero oa ℓ Pt Z Dh encPt encT idOf
        (fun _ => lam) q qR B0 qepSm gMain tL par false B (fun o _ => hq o) le_rfl))
    (fun gMain par => multiSessMixEndWinProb_eq_zero_of_mfj Z ℓ encT oa idOf qR (AdvBr gMain par) true
      (multiSessEndWinProbMix_redFSAuthMultiBucket_eq_zero oa ℓ Pt Z Dh encPt encT idOf
        (fun _ => lam) q qR B0 qepSm gMain tL par true B (fun o _ => hq o) le_rfl))
    (fun gMain par idx _ stage la o => redFSAuthMultiBucketAtomic_makesAtMostQueries ℓ Pt Z Dh encPt encT
      (idOf o) lam stage la idx q qepSm qR B0 gMain tL par (B o) (hq o))
    (fun gMain par idx _ stage la o => encMsgsOk_atomicShortB_of_pubB (ABr gMain par stage la idx o)
      (redFSAuthMultiBucketAtomic_fsOk_and_encAtomicShort ℓ Pt Z Dh encPt encT
        (idOf o) lam hℓ stage la idx q qepSm qR B0 gMain tL par (B o) (hq o) (heq o) (hsh o) (hg o)).2)
    (fun idx hidx stage la o => ?_) (fun gMain par idx _ hne => ?_)
  · have hdiv : idx / (q + 1) < (qepSm + 2) - healEpoch tL :=
      Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
    have hmod : idx % (q + 1) < q + 1 := Nat.mod_lt idx (Nat.succ_pos q)
    have hle : healEpoch tL ≤ healEpoch tL + idx / (q + 1) := Nat.le_add_right _ _
    have hlt : healEpoch tL + idx / (q + 1) < qepSm + 2 := by
      generalize idx / (q + 1) = d at hdiv ⊢
      omega
    have hidxEq : (q + 1) * (healEpoch tL + idx / (q + 1) - healEpoch tL) + idx % (q + 1) = idx := by
      rw [Nat.add_sub_cancel_left, Nat.div_add_mod]
    have hAct := hActive (idx % (q + 1)) (healEpoch tL + idx / (q + 1)) hmod hle hlt stage la o
    rw [hidxEq] at hAct
    exact hAct
  · rw [funext hRfs]
    exact redFSAuthMultiBucketAtomic_inactive_fsAeadAuthMixtureCompBound_eq_zero oa ℓ Pt Z Dh encPt encT
      idOf (fun _ => lam) hℓ hinj idx q qepSm qR B0 gMain tL par B hq (Or.inr hne)

/-- Complete Stage-2 drop-in proof of `SessionCostedDF.fig8MixAuth_simFig8_le_fig8MixShortAuthV1`,
automatically discharging Hop 1 (`Stage2Bucket.lemma9_bucket_at`), `simFig8RedProg` + `challSim`
query/equalPub/shortness/guardedness invariants, and Hop 3
(`localAuthBucketMix_par_le_sum_fsAeadAuthMixtureCompBound`), leaving only the `redCKAAuth`,
`redPRNGAuth`, and active-slot `redFSAuth` `fig8RedsInst` bridges. -/
theorem fig8MixAuth_simFig8_le_fig8MixShortAuthV1_of_stage2Inst {α : Type}
    (Z : Crypto) (K : CryptoVerification.LibsignalSpqrV1.MlKem)
    (hD : ∀ k x, Z.D k (Z.E k x) = x) {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (lam : Pt)
    (qep q : ℕ) (hq32 : 2 * q + 25002 < 2 ^ 32)
    (oa : ProbComp α) (ida idb : α → IdentityKey)
    (R : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (A : α → CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : ∀ o, CryptoGames.SM.MakesAtMostQueries (A o) q)
    (hChall : ∀ o, (R o).fig8.challSim =
      (Computational.Proofs.SessionCostedFig8.Bundles.fig8RedsInst Dh encPt Z protoSignalCodec ℓ encT
        (idsOf (ida o) (idb o)) lam (qep + 1) q).challSim)
    (hFs : ∀ o, (R o).fs =
      fsCostedRedsInst Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) (min (2 * q) (q + 2)))
    (hSim : ∀ o, (R o).simFig8 =
      simFig8RedProg ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q)
    (hCKAAuth :
      let simAdv : α → Fig8Adv Pt ℓ := fun o =>
        (simFig8RedProg ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).eval (fun _ => A o) ()
      ∀ tL ∈ admissibleLastLeakGuesses (2 + 1) ((qep + 1) + 1),
        CryptoGames.CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
          (prefixAdvAvg oa fun o =>
            ((R o).fig8.redCKAAuth tL).eval (fun _ => challSim (2 + 1) (qep + 1) (simAdv o)) ()) =
        CryptoGames.CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
          (prefixAdvAvg oa fun o => redCKAAuthBucket (dhScheme Dh) (rootPRNG Z.F encPt)
            (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL
            (challSim (2 + 1) (qep + 1) (simAdv o))))
    (hPRNGAuth :
      let simAdv : α → Fig8Adv Pt ℓ := fun o =>
        (simFig8RedProg ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).eval (fun _ => A o) ()
      ∀ tL ∈ admissibleLastLeakGuesses (2 + 1) ((qep + 1) + 1),
      ∀ t ∈ Finset.Ico (healEpoch tL) ((qep + 1) + 2),
        CryptoGames.PRFPRNG.advantage (rootPRNG Z.F encPt)
          (prefixAdvAvg oa fun o => redPRNGAuthBucketHybrid (dhScheme Dh) (rootPRNG Z.F encPt)
            (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1) tL t
            (challSim (2 + 1) (qep + 1) (simAdv o))) ≤
        CryptoGames.PRFPRNG.advantage (rootPRNG Z.F encPt)
          (prefixAdvAvg oa fun o =>
            ((R o).fig8.redPRNGAuth tL t).eval (fun _ => challSim (2 + 1) (qep + 1) (simAdv o)) ()))
    (hFSActive :
      let simAdv : α → Fig8Adv Pt ℓ := fun o =>
        (simFig8RedProg ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).eval (fun _ => A o) ()
      ∀ tL ∈ admissibleLastLeakGuesses (2 + 1) ((qep + 1) + 1),
      ∀ j t, j < q + 1 → healEpoch tL ≤ t → t < (qep + 1) + 2 → ∀ stage la o,
        (redFSAuthMultiBucketAtomic ℓ Pt Z Dh encPt encT (idsOf (ida o) (idb o)) lam stage la
          ((q + 1) * (t - healEpoch tL) + j) (qep + 1) (min (2 * q) (q + 2))
          ((q + 1) * (maxForwardJumps + 1)) (q + 1) (decide (j = 0)) tL
          (decide (CryptoGames.Party.senderOf t == .A))).eval
            (fun _ => challSim (2 + 1) (qep + 1) (simAdv o)) () =
        ((R o).fig8.redFSAuth stage la j tL t).eval
          (fun _ => challSim (2 + 1) (qep + 1) (simAdv o)) ()) :
    let simAdv : α → Fig8Adv Pt ℓ := fun o =>
      (simFig8RedProg ℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q).eval (fun _ => A o) ()
    2 * ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) ((qep + 1) + 1),
      𝒟[oa >>= fun o => bucketAuthGame
        (lFig8 Dh encPt Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000 lam)
        (2 + 1) (qep + 1) tL (challSim (2 + 1) (qep + 1) (simAdv o))] {true} ≤
      fig8MixShortAuthV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb R A := by
  intro simAdv
  have hSimEq : ∀ o, ((R o).simFig8).eval (fun _ => A o) () = simAdv o := fun o => by rw [hSim o]
  have hqSim : ∀ o, CryptoGames.SM.MakesAtMostQueries (simAdv o) q := fun o =>
    simFig8RedProg_queries hℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q (A o) (hq o)
  have hshSim : ∀ o, CryptoGames.LibsignalSM.Proofs.SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) (simAdv o) := fun o =>
    simFig8RedProg_sendAtomicShort hℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q (A o) (hq o)
  have hgSim : ∀ o, CryptoGames.LibsignalSM.Proofs.SessionShort.GuardedSMShort (simAdv o) := fun o =>
    simFig8RedProg_guardedSMShort hℓ Z K (ida o) (idb o) Dh encPt encT decT lam qep q (A o) (hq o)
  have hChallEq : ∀ o,
      ((R o).fig8.challSim).eval (fun _ => ((R o).simFig8).eval (fun _ => A o) ()) () =
      challSim (2 + 1) (qep + 1) (simAdv o) := fun o => by
    rw [hChall o, hSimEq o]
    exact Computational.Proofs.SessionCostedFig8.BundlesEval.fig8RedsInst_challSim_eval
      Dh encPt Z protoSignalCodec ℓ hℓ encT (idsOf (ida o) (idb o)) lam (qep + 1) q
      (simAdv o) (hqSim o)
  let B : α → Fig8Adv Pt ℓ := fun o => challSim (2 + 1) (qep + 1) (simAdv o)
  have hqB : ∀ o, CryptoGames.SM.MakesAtMostQueries (B o) q := fun o =>
    challSim_queries (2 + 1) (qep + 1) (simAdv o) q (hqSim o)
  have heqB : ∀ o, CryptoGames.SM.EqualPubChalls (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1) (B o) :=
    fun o => CryptoGames.LibsignalSM.Proofs.RestrictedReds.challSim_equalPub (2 + 1) (qep + 1)
      (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1) (simAdv o)
  have hshB : ∀ o, CryptoGames.LibsignalSM.Proofs.SessionShort.FSAEADRed.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) (B o) :=
    fun o => CryptoGames.LibsignalSM.Proofs.QueryBounds.isQueryBoundP_congr
      (by rintro (_ | ((((_ | _) | _) | _) | _)) <;> rfl)
      (CryptoGames.LibsignalSM.Proofs.SessionShort.challSim_sendOk (2 + 1) (qep + 1)
        (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) (simAdv o) (hshSim o))
  have hgB : ∀ o, CryptoGames.LibsignalSM.Proofs.SessionShort.GuardedSMShort (B o) := fun o =>
    CryptoGames.LibsignalSM.Proofs.SessionShort.challSim_guardedSMShort (2 + 1) (qep + 1)
      (simAdv o) (hgSim o)
  conv_lhs => simp only [← hSimEq]
  refine Computational.Proofs.E2E.Fig8Stage2MixHelpers.fig8MixAuth_le_fig8MixShortAuthV1_of_fig8Eval
    Z K Dh hDh encPt encT decT lam qep q oa ida idb R A
    (fun tL _ o => by
      rw [hSimEq o]
      exact CryptoGames.SM.Construction.lemma9_bucket_at (dhScheme Dh) (rootPRNG Z.F encPt)
        (lFS Z protoSignalCodec ℓ encT (idsOf (ida o) (idb o)) 25000) lam 1 (qep + 1)
        (CryptoGames.CKA.dhScheme_correct Dh hDh) tL (B o))
    (fun tL htL => by simp only [hChallEq]; simp only [hSimEq]; exact hCKAAuth tL htL)
    (fun tL htL t ht => by simp only [hChallEq]; simp only [hSimEq]; exact hPRNGAuth tL htL t ht)
    (fun tL htL => ?_)
  conv_lhs => simp only [hSimEq]
  exact localAuthBucketMix_par_le_sum_fsAeadAuthMixtureCompBound
    Z hD hℓ Dh hDh encPt encT hinj hdum oa (fun o => idsOf (ida o) (idb o)) lam (qep + 1) q hq32
    (fun o => (R o).fs) hFs tL B hqB heqB hshB hgB
    (fun stage la j t o =>
      ((R o).fig8.redFSAuth stage la j tL t).eval
        (fun _ => (R o).fig8.challSim.eval (fun _ => (R o).simFig8.eval (fun _ => A o) ()) ()) ())
    (fun j t hj hle hlt stage la o => by
      rw [hChallEq o]
      exact hFSActive tL htL j t hj hle hlt stage la o)

end Stage2InstBridge

end TopMixAuth

end Computational.Proofs.SessionCostedDFStage2Auth
