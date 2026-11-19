/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalBound -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.BucketAuthBridge -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SessionAuthBridge -- proof-setup: allow-public-import

/-!
# Stage-2 Top-Level Figure 8 Assembly Helpers (`TopAssembly`)

Provides layout- and `DeliverForge`-independent Stage-2 assembly lemmas for `SessionCostedFig8`:
1. Exact `Finset` `(t, j)` reindexing identities for both two-mode (`j = 0` main + `1 ≤ j ≤ q`
   forged-header) and single-mode (`0 ≤ j ≤ q`) multi-session FS-AEAD routers.
2. Point-mass multi-session `SessionAuthBridge` step wrappers into
   `∑ t ∈ Finset.Ico (healEpoch tL) (qep + 2), ∑ j ∈ Finset.range (q + 1), fsAuthCompBoundWith ... + 8 * macForgeryTerm C q`.
3. Decomposition of `fig8ShortBoundWith` into `fig8AuthPart + fig8PrivPart` and assembly of
   `fig8BucketAuth_le_fig8ShortBoundWith` and `fig8Hybrid_le_fig8ShortBoundWith` via
   `BucketAuthBridge.lemma17_bucket`.-/

public section

set_option autoImplicit false

open scoped MeasureTheory
open Computational.Proofs.E2E.SessionAuthBridge (MultiSessFsAdv RouterAdvCompat TwoModeMultiSessBounds authHopCutoff sessionHybrid_two_modes_le_sum_fsAuthCompBoundWith)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun dhScheme)
open CryptoGames.LibsignalSM (Fig8Adv)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey SignalMessageProtoCodec maxForwardJumps)
open CryptoGames.Ratchet (rootPRNG)
open CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart dummyKey lAeadR lChainPRG lFig8 lIdeal)
open CryptoGames.SM (admissibleLastLeakGuesses)
open CryptoGames.SM.BucketAuthBridge (bucketAuthAdvantage lemma17_bucket)
open CryptoGames.SM.Construction (healEpoch)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSession (Fig8CostedReds FsAdv FsCostedReds fig8ShortBoundWith fsAuthCompBoundWith fsCostedRedsInst fsShortBoundWith macForgeryTerm)

namespace Computational.Proofs.SessionCostedFig8.TopAssembly

open scoped ENNReal
open OracleComp OracleSpec
open _root_.CryptoVerification.E2E.Signed.SessionRouter (sessLift lazyInit)
open _root_.CryptoVerification.E2E.Signed.SessionFS (fsInit fsImpl)
open Computational.Proofs.ReductionDsl.FsAtomicMacros (atomicShortB)

/-! ### 1. Exact `Finset` `(t, j)` Reindexing Identities -/

/-- Product reindexing `idx = s * m + r` (`idx % m = r`, `idx / m = s`) over `Finset.range (K * m)`. -/
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

/-- Transposed product reindexing `idx = r * K + s` (`idx / K = r`, `idx % K = s`) over
`Finset.range (m * K)`. -/
theorem sum_range_mul_div_mod (K m : ℕ) (g : ℕ → ℕ → ℝ≥0∞) :
    ∑ idx ∈ Finset.range (m * K), g (idx / K) (idx % K) =
      ∑ s ∈ Finset.range K, ∑ r ∈ Finset.range m, g r s := by
  rw [sum_range_mul_mod_div m K (fun s r => g r s), Finset.sum_comm]

/-- Two-mode (`j = 0` on `range (b - a)` plus `1 ≤ j ≤ q` via `idx % q + 1`, `a + idx / q` on
`range ((b - a) * q)`) reindexing onto `∑ t ∈ Finset.Ico a b, ∑ j ∈ Finset.range (q + 1), f j t`. -/
theorem sum_two_modes_mod_div_eq_ico_range (a b q : ℕ) (f : ℕ → ℕ → ℝ≥0∞) :
    (∑ s ∈ Finset.range (b - a), f 0 (a + s)) +
        (∑ idx ∈ Finset.range ((b - a) * q), f (idx % q + 1) (a + idx / q)) =
      ∑ t ∈ Finset.Ico a b, ∑ j ∈ Finset.range (q + 1), f j t := by
  rw [sum_range_mul_mod_div (b - a) q (fun r s => f (r + 1) (a + s)),
      ← Finset.sum_add_distrib, Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_range_succ' (fun j => f j (a + s)) q, add_comm]

/-- Single-mode (`0 ≤ j ≤ q` via `idx % (q + 1)`, `a + idx / (q + 1)` on
`range ((b - a) * (q + 1))`) reindexing onto
`∑ t ∈ Finset.Ico a b, ∑ j ∈ Finset.range (q + 1), f j t`. -/
theorem sum_single_mode_mod_div_eq_ico_range (a b q : ℕ) (f : ℕ → ℕ → ℝ≥0∞) :
    ∑ idx ∈ Finset.range ((b - a) * (q + 1)), f (idx % (q + 1)) (a + idx / (q + 1)) =
      ∑ t ∈ Finset.Ico a b, ∑ j ∈ Finset.range (q + 1), f j t := by
  rw [sum_range_mul_mod_div (b - a) (q + 1) (fun j s => f j (a + s)),
      Finset.sum_Ico_eq_sum_range]

/-! ### 2. Multi-Session FS-AEAD Step Wrappers (`SessionAuthBridge`) -/

/-- Real (`hp 0 0 la`) win probability of a multi-session AD-level FS-AEAD adversary `Adv la`. -/
@[expose] noncomputable def multiSessRealWinProb {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (Adv : Bool → MultiSessFsAdv Pt ℓ) (la : Bool) : ℝ≥0∞ :=
  𝒟[Prod.fst <$> (simulateQ (sessLift
    (lazyInit fsInit (fsImpl
      (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps (CryptoGames.FSAEAD.Thm5.hp 0 0 la)))) (Adv la)).run
    (fun _ => none)] {true}

/-- Ideal-cutoff (`hp N N la` where `N = authHopCutoff maxForwardJumps qR la`) win probability of
a multi-session AD-level FS-AEAD adversary `Adv la`. -/
@[expose] noncomputable def multiSessEndWinProb {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (qR : ℕ) (Adv : Bool → MultiSessFsAdv Pt ℓ) (la : Bool) : ℝ≥0∞ :=
  let N := authHopCutoff maxForwardJumps qR la
  𝒟[Prod.fst <$> (simulateQ (sessLift
    (lazyInit fsInit (fsImpl
      (lIdeal C protoSignalCodec ℓ encT)
      (lAeadR C protoSignalCodec ℓ encT idOf)
      (lChainPRG C.F) maxForwardJumps (CryptoGames.FSAEAD.Thm5.hp N N la)))) (Adv la)).run
    (fun _ => none)] {true}

/-- Single multi-session family wrapper around `sessionHybrid_two_modes_le_sum_fsAuthCompBoundWith`
at `qR = min (2 * q) (q + 2)` and `qd = q`, rewriting `4 * (q * macForgeryProb C.F)` to
`4 * macForgeryTerm C q`. -/
theorem multiSess_two_modes_le_sum_fsAuthCompBoundWith_min
    {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (M q : ℕ) (hq32 : 2 * q + 25002 < 2 ^ 32)
    (Adv : Bool → MultiSessFsAdv Pt ℓ)
    (A : Bool → Bool → ℕ → FsAdv Pt ℓ)
    (hℓ : ℓ < 10 ^ 6) (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (hbds : TwoModeMultiSessBounds maxForwardJumps (min (2 * q) (q + 2)) M q
      (fun la (_ : Unit) => Adv la))
    (hcompat : RouterAdvCompat C protoSignalCodec ℓ encT
      (pure ()) (fun _ => idOf) maxForwardJumps (min (2 * q) (q + 2)) M
      (fun la (_ : Unit) => Adv la) (fun stage la j _ => A stage la j))
    (hA : ∀ j < M, ∀ stage la, CryptoGames.FSAEAD.MakesAtMostQueries (A stage la j) (min (2 * q) (q + 2)))
    (hshort : ∀ j < M, ∀ stage la,
      CryptoGames.FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1)
        (A stage la j))
    (hendFalse : multiSessEndWinProb C ℓ encT idOf (min (2 * q) (q + 2)) Adv false = 0)
    (hendTrue : multiSessEndWinProb C ℓ encT idOf (min (2 * q) (q + 2)) Adv true = 0) :
    2 * (multiSessRealWinProb C ℓ encT idOf Adv false +
          multiSessRealWinProb C ℓ encT idOf Adv true) ≤
      (∑ j ∈ Finset.range M,
        fsAuthCompBoundWith C protoSignalCodec ℓ (min (2 * q) (q + 2))
          (fsCostedRedsInst C protoSignalCodec ℓ encT idOf (min (2 * q) (q + 2)))
          (fun stage la => A stage la j)) +
      4 * macForgeryTerm C q := by
  have hcut : min (2 * q) (q + 2) + (maxForwardJumps + 1) ≤ 2 ^ 32 := by
    change min (2 * q) (q + 2) + (25000 + 1) ≤ 2 ^ 32
    omega
  exact sessionHybrid_two_modes_le_sum_fsAuthCompBoundWith C ℓ encT idOf
    (min (2 * q) (q + 2)) M q Adv A hℓ hinj hdum hcut hbds hcompat hA hshort hendFalse hendTrue

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

/-- Four-branch (`gMain ∈ {true, false}`, `par ∈ {false, true}`) multi-session FS-AEAD bound for a
fixed bucket `tL` (`M = ((qep + 2) - healEpoch tL) * (q + 1)`): active `(gMain, par)` sessions match
`A` while the other 3 branches vanish (`hZero`), and `16 * mac` halves to `8 * mac` via `2 * X`. -/
theorem bucket_four_branch_fs_le
    {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (qep q : ℕ) (tL : Option ℕ) (hq32 : 2 * q + 25002 < 2 ^ 32)
    (AdvBr : Bool → Bool → Bool → MultiSessFsAdv Pt ℓ)
    (ABr : Bool → Bool → Bool → Bool → ℕ → FsAdv Pt ℓ)
    (A : Bool → Bool → ℕ → ℕ → FsAdv Pt ℓ)
    (hℓ : ℓ < 10 ^ 6) (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (hbds : ∀ gMain par, TwoModeMultiSessBounds maxForwardJumps (min (2 * q) (q + 2))
      (((qep + 2) - healEpoch tL) * (q + 1)) q (fun la (_ : Unit) => AdvBr gMain par la))
    (hcompat : ∀ gMain par, RouterAdvCompat C protoSignalCodec ℓ encT
      (pure ()) (fun _ => idOf) maxForwardJumps (min (2 * q) (q + 2))
      (((qep + 2) - healEpoch tL) * (q + 1))
      (fun la (_ : Unit) => AdvBr gMain par la)
      (fun stage la idx _ => ABr gMain par stage la idx))
    (hendF : ∀ gMain par,
      multiSessEndWinProb C ℓ encT idOf (min (2 * q) (q + 2)) (AdvBr gMain par) false = 0)
    (hendT : ∀ gMain par,
      multiSessEndWinProb C ℓ encT idOf (min (2 * q) (q + 2)) (AdvBr gMain par) true = 0)
    (hABr : ∀ gMain par idx, idx < ((qep + 2) - healEpoch tL) * (q + 1) →
      ∀ stage la, CryptoGames.FSAEAD.MakesAtMostQueries (ABr gMain par stage la idx) (min (2 * q) (q + 2)))
    (hshort : ∀ gMain par idx, idx < ((qep + 2) - healEpoch tL) * (q + 1) →
      ∀ stage la,
        CryptoGames.FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1)
          (ABr gMain par stage la idx))
    (hActive : ∀ idx, idx < ((qep + 2) - healEpoch tL) * (q + 1) →
      ∀ stage la,
        ABr (decide (idx % (q + 1) = 0))
          (decide (CryptoGames.Party.senderOf (healEpoch tL + idx / (q + 1)) == .A)) stage la idx =
          A stage la (idx % (q + 1)) (healEpoch tL + idx / (q + 1)))
    (hZero : ∀ gMain par idx, idx < ((qep + 2) - healEpoch tL) * (q + 1) →
      ¬(decide (idx % (q + 1) = 0) = gMain ∧
        decide (CryptoGames.Party.senderOf (healEpoch tL + idx / (q + 1)) == .A) = par) →
      fsAuthCompBoundWith C protoSignalCodec ℓ (min (2 * q) (q + 2))
        (fsCostedRedsInst C protoSignalCodec ℓ encT idOf (min (2 * q) (q + 2)))
        (fun stage la => ABr gMain par stage la idx) = 0) :
    (multiSessRealWinProb C ℓ encT idOf (AdvBr true false) false +
      multiSessRealWinProb C ℓ encT idOf (AdvBr true false) true) +
    (multiSessRealWinProb C ℓ encT idOf (AdvBr true true) false +
      multiSessRealWinProb C ℓ encT idOf (AdvBr true true) true) +
    (multiSessRealWinProb C ℓ encT idOf (AdvBr false false) false +
      multiSessRealWinProb C ℓ encT idOf (AdvBr false false) true) +
    (multiSessRealWinProb C ℓ encT idOf (AdvBr false true) false +
      multiSessRealWinProb C ℓ encT idOf (AdvBr false true) true) ≤
      (∑ t ∈ Finset.Ico (healEpoch tL) (qep + 2),
        ∑ j ∈ Finset.range (q + 1),
          fsAuthCompBoundWith C protoSignalCodec ℓ (min (2 * q) (q + 2))
            (fsCostedRedsInst C protoSignalCodec ℓ encT idOf (min (2 * q) (q + 2)))
            (fun stage la => A stage la j t)) +
      8 * macForgeryTerm C q := by
  set M := ((qep + 2) - healEpoch tL) * (q + 1)
  have hTF := multiSess_two_modes_le_sum_fsAuthCompBoundWith_min C ℓ encT idOf M q hq32
    (AdvBr true false) (ABr true false) hℓ hinj hdum (hbds true false) (hcompat true false)
    (hABr true false) (hshort true false) (hendF true false) (hendT true false)
  have hTT := multiSess_two_modes_le_sum_fsAuthCompBoundWith_min C ℓ encT idOf M q hq32
    (AdvBr true true) (ABr true true) hℓ hinj hdum (hbds true true) (hcompat true true)
    (hABr true true) (hshort true true) (hendF true true) (hendT true true)
  have hFF := multiSess_two_modes_le_sum_fsAuthCompBoundWith_min C ℓ encT idOf M q hq32
    (AdvBr false false) (ABr false false) hℓ hinj hdum (hbds false false) (hcompat false false)
    (hABr false false) (hshort false false) (hendF false false) (hendT false false)
  have hFT := multiSess_two_modes_le_sum_fsAuthCompBoundWith_min C ℓ encT idOf M q hq32
    (AdvBr false true) (ABr false true) hℓ hinj hdum (hbds false true) (hcompat false true)
    (hABr false true) (hshort false true) (hendF false true) (hendT false true)
  have hSumIdx :
      ((∑ idx ∈ Finset.range M,
          fsAuthCompBoundWith C protoSignalCodec ℓ (min (2 * q) (q + 2))
            (fsCostedRedsInst C protoSignalCodec ℓ encT idOf (min (2 * q) (q + 2)))
            (fun stage la => ABr true false stage la idx)) +
        (∑ idx ∈ Finset.range M,
          fsAuthCompBoundWith C protoSignalCodec ℓ (min (2 * q) (q + 2))
            (fsCostedRedsInst C protoSignalCodec ℓ encT idOf (min (2 * q) (q + 2)))
            (fun stage la => ABr true true stage la idx))) +
      ((∑ idx ∈ Finset.range M,
          fsAuthCompBoundWith C protoSignalCodec ℓ (min (2 * q) (q + 2))
            (fsCostedRedsInst C protoSignalCodec ℓ encT idOf (min (2 * q) (q + 2)))
            (fun stage la => ABr false false stage la idx)) +
        (∑ idx ∈ Finset.range M,
          fsAuthCompBoundWith C protoSignalCodec ℓ (min (2 * q) (q + 2))
            (fsCostedRedsInst C protoSignalCodec ℓ encT idOf (min (2 * q) (q + 2)))
            (fun stage la => ABr false true stage la idx))) =
      ∑ idx ∈ Finset.range M,
        fsAuthCompBoundWith C protoSignalCodec ℓ (min (2 * q) (q + 2))
          (fsCostedRedsInst C protoSignalCodec ℓ encT idOf (min (2 * q) (q + 2)))
          (fun stage la => A stage la (idx % (q + 1)) (healEpoch tL + idx / (q + 1))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun idx hidx => ?_
    have hidx' : idx < M := Finset.mem_range.mp hidx
    cases hg : decide (idx % (q + 1) = 0) <;>
      cases hp : decide (CryptoGames.Party.senderOf (healEpoch tL + idx / (q + 1)) == .A)
    · rw [hZero true false idx hidx' (by rw [hg, hp]; decide),
          hZero true true idx hidx' (by rw [hg, hp]; decide),
          hZero false true idx hidx' (by rw [hg, hp]; decide),
          add_zero, zero_add, add_zero]
      have hAct : (fun stage la => ABr false false stage la idx) =
          (fun stage la => A stage la (idx % (q + 1)) (healEpoch tL + idx / (q + 1))) := by
        funext stage la
        have h1 := hActive idx hidx' stage la
        rwa [hg, hp] at h1
      rw [hAct]
    · rw [hZero true false idx hidx' (by rw [hg, hp]; decide),
          hZero true true idx hidx' (by rw [hg, hp]; decide),
          hZero false false idx hidx' (by rw [hg, hp]; decide),
          add_zero, zero_add, zero_add]
      have hAct : (fun stage la => ABr false true stage la idx) =
          (fun stage la => A stage la (idx % (q + 1)) (healEpoch tL + idx / (q + 1))) := by
        funext stage la
        have h1 := hActive idx hidx' stage la
        rwa [hg, hp] at h1
      rw [hAct]
    · rw [hZero true true idx hidx' (by rw [hg, hp]; decide),
          hZero false false idx hidx' (by rw [hg, hp]; decide),
          hZero false true idx hidx' (by rw [hg, hp]; decide),
          add_zero, add_zero, add_zero]
      have hAct : (fun stage la => ABr true false stage la idx) =
          (fun stage la => A stage la (idx % (q + 1)) (healEpoch tL + idx / (q + 1))) := by
        funext stage la
        have h1 := hActive idx hidx' stage la
        rwa [hg, hp] at h1
      rw [hAct]
    · rw [hZero true false idx hidx' (by rw [hg, hp]; decide),
          hZero false false idx hidx' (by rw [hg, hp]; decide),
          hZero false true idx hidx' (by rw [hg, hp]; decide),
          zero_add, add_zero, add_zero]
      have hAct : (fun stage la => ABr true true stage la idx) =
          (fun stage la => A stage la (idx % (q + 1)) (healEpoch tL + idx / (q + 1))) := by
        funext stage la
        have h1 := hActive idx hidx' stage la
        rwa [hg, hp] at h1
      rw [hAct]
  have h2 :
      2 * ((multiSessRealWinProb C ℓ encT idOf (AdvBr true false) false +
            multiSessRealWinProb C ℓ encT idOf (AdvBr true false) true) +
          (multiSessRealWinProb C ℓ encT idOf (AdvBr true true) false +
            multiSessRealWinProb C ℓ encT idOf (AdvBr true true) true) +
          (multiSessRealWinProb C ℓ encT idOf (AdvBr false false) false +
            multiSessRealWinProb C ℓ encT idOf (AdvBr false false) true) +
          (multiSessRealWinProb C ℓ encT idOf (AdvBr false true) false +
            multiSessRealWinProb C ℓ encT idOf (AdvBr false true) true)) ≤
        (∑ t ∈ Finset.Ico (healEpoch tL) (qep + 2),
          ∑ j ∈ Finset.range (q + 1),
            fsAuthCompBoundWith C protoSignalCodec ℓ (min (2 * q) (q + 2))
              (fsCostedRedsInst C protoSignalCodec ℓ encT idOf (min (2 * q) (q + 2)))
              (fun stage la => A stage la j t)) +
        4 * (4 * macForgeryTerm C q) := by
    have hL :
        2 * ((multiSessRealWinProb C ℓ encT idOf (AdvBr true false) false +
              multiSessRealWinProb C ℓ encT idOf (AdvBr true false) true) +
            (multiSessRealWinProb C ℓ encT idOf (AdvBr true true) false +
              multiSessRealWinProb C ℓ encT idOf (AdvBr true true) true) +
            (multiSessRealWinProb C ℓ encT idOf (AdvBr false false) false +
              multiSessRealWinProb C ℓ encT idOf (AdvBr false false) true) +
            (multiSessRealWinProb C ℓ encT idOf (AdvBr false true) false +
              multiSessRealWinProb C ℓ encT idOf (AdvBr false true) true)) =
        (2 * (multiSessRealWinProb C ℓ encT idOf (AdvBr true false) false +
              multiSessRealWinProb C ℓ encT idOf (AdvBr true false) true) +
          2 * (multiSessRealWinProb C ℓ encT idOf (AdvBr true true) false +
              multiSessRealWinProb C ℓ encT idOf (AdvBr true true) true)) +
        (2 * (multiSessRealWinProb C ℓ encT idOf (AdvBr false false) false +
              multiSessRealWinProb C ℓ encT idOf (AdvBr false false) true) +
          2 * (multiSessRealWinProb C ℓ encT idOf (AdvBr false true) false +
              multiSessRealWinProb C ℓ encT idOf (AdvBr false true) true)) := by ring
    rw [hL]
    calc
      (2 * (multiSessRealWinProb C ℓ encT idOf (AdvBr true false) false +
            multiSessRealWinProb C ℓ encT idOf (AdvBr true false) true) +
        2 * (multiSessRealWinProb C ℓ encT idOf (AdvBr true true) false +
            multiSessRealWinProb C ℓ encT idOf (AdvBr true true) true)) +
      (2 * (multiSessRealWinProb C ℓ encT idOf (AdvBr false false) false +
            multiSessRealWinProb C ℓ encT idOf (AdvBr false false) true) +
        2 * (multiSessRealWinProb C ℓ encT idOf (AdvBr false true) false +
            multiSessRealWinProb C ℓ encT idOf (AdvBr false true) true))
        ≤ (((∑ idx ∈ Finset.range M,
              fsAuthCompBoundWith C protoSignalCodec ℓ (min (2 * q) (q + 2))
                (fsCostedRedsInst C protoSignalCodec ℓ encT idOf (min (2 * q) (q + 2)))
                (fun stage la => ABr true false stage la idx)) + 4 * macForgeryTerm C q) +
            ((∑ idx ∈ Finset.range M,
              fsAuthCompBoundWith C protoSignalCodec ℓ (min (2 * q) (q + 2))
                (fsCostedRedsInst C protoSignalCodec ℓ encT idOf (min (2 * q) (q + 2)))
                (fun stage la => ABr true true stage la idx)) + 4 * macForgeryTerm C q)) +
          (((∑ idx ∈ Finset.range M,
              fsAuthCompBoundWith C protoSignalCodec ℓ (min (2 * q) (q + 2))
                (fsCostedRedsInst C protoSignalCodec ℓ encT idOf (min (2 * q) (q + 2)))
                (fun stage la => ABr false false stage la idx)) + 4 * macForgeryTerm C q) +
            ((∑ idx ∈ Finset.range M,
              fsAuthCompBoundWith C protoSignalCodec ℓ (min (2 * q) (q + 2))
                (fsCostedRedsInst C protoSignalCodec ℓ encT idOf (min (2 * q) (q + 2)))
                (fun stage la => ABr false true stage la idx)) + 4 * macForgeryTerm C q)) :=
          add_le_add (add_le_add hTF hTT) (add_le_add hFF hFT)
      _ = (((∑ idx ∈ Finset.range M,
              fsAuthCompBoundWith C protoSignalCodec ℓ (min (2 * q) (q + 2))
                (fsCostedRedsInst C protoSignalCodec ℓ encT idOf (min (2 * q) (q + 2)))
                (fun stage la => ABr true false stage la idx)) +
            (∑ idx ∈ Finset.range M,
              fsAuthCompBoundWith C protoSignalCodec ℓ (min (2 * q) (q + 2))
                (fsCostedRedsInst C protoSignalCodec ℓ encT idOf (min (2 * q) (q + 2)))
                (fun stage la => ABr true true stage la idx))) +
          ((∑ idx ∈ Finset.range M,
              fsAuthCompBoundWith C protoSignalCodec ℓ (min (2 * q) (q + 2))
                (fsCostedRedsInst C protoSignalCodec ℓ encT idOf (min (2 * q) (q + 2)))
                (fun stage la => ABr false false stage la idx)) +
            (∑ idx ∈ Finset.range M,
              fsAuthCompBoundWith C protoSignalCodec ℓ (min (2 * q) (q + 2))
                (fsCostedRedsInst C protoSignalCodec ℓ encT idOf (min (2 * q) (q + 2)))
                (fun stage la => ABr false true stage la idx)))) +
          4 * (4 * macForgeryTerm C q) := by ring
      _ = _ := by
          rw [hSumIdx, sum_single_mode_mod_div_eq_ico_range (healEpoch tL) (qep + 2) q
            (fun j t => fsAuthCompBoundWith C protoSignalCodec ℓ (min (2 * q) (q + 2))
              (fsCostedRedsInst C protoSignalCodec ℓ encT idOf (min (2 * q) (q + 2)))
              (fun stage la => A stage la j t))]
  have hCancel := le_add_two_mul_of_two_mul_le_add_four_mul h2
  have h24 : 2 * (4 * macForgeryTerm C q) = 8 * macForgeryTerm C q := by ring
  rwa [h24] at hCancel

/-! ### 3. `fig8ShortBoundWith` Decomposition and Top-Level Stage-2 Assembly -/

section TopBound

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

/-- Per-`tL` authenticity summand inside `fig8ShortBoundWith`. -/
@[expose] noncomputable def fig8AuthBucketTerm (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (R : Fig8CostedReds Dh encPt C codec ℓ encT idOf lam)
    (Rfs : FsCostedReds C codec ℓ encT idOf) (B : Fig8Adv Pt ℓ) (tL : Option ℕ) : ℝ≥0∞ :=
  let qR := min (2 * q) (q + 2)
  let cka := dhScheme Dh
  let prng := rootPRNG C.F encPt
  let authB := R.challSim.eval (fun _ => B) ()
  CryptoGames.CKA.advantage cka 1 (healEpoch tL) ((R.redCKAAuth tL).eval (fun _ => authB) ())
    + (∑ t ∈ Finset.Ico (healEpoch tL) (qep + 2),
        (2 * CryptoGames.PRFPRNG.advantage prng ((R.redPRNGAuth tL t).eval (fun _ => authB) ())
          + ∑ j ∈ Finset.range (q + 1),
              fsAuthCompBoundWith C codec ℓ qR Rfs
                (fun stage la => (R.redFSAuth stage la j tL t).eval (fun _ => authB) ())))
    + 8 * macForgeryTerm C q

/-- Stage-2 authenticity half of `fig8ShortBoundWith`. -/
@[expose] noncomputable def fig8AuthPart (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (R : Fig8CostedReds Dh encPt C codec ℓ encT idOf lam)
    (Rfs : FsCostedReds C codec ℓ encT idOf) (B : Fig8Adv Pt ℓ) : ℝ≥0∞ :=
  2 * ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) (qep + 1),
    fig8AuthBucketTerm Dh encPt C codec ℓ encT idOf lam qep q R Rfs B tL

/-- Stage-2 privacy half of `fig8ShortBoundWith`. -/
@[expose] noncomputable def fig8PrivPart (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (R : Fig8CostedReds Dh encPt C codec ℓ encT idOf lam)
    (Rfs : FsCostedReds C codec ℓ encT idOf) (B : Fig8Adv Pt ℓ) : ℝ≥0∞ :=
  let qR := min (2 * q) (q + 2)
  let cka := dhScheme Dh
  let prng := rootPRNG C.F encPt
  let privB := fun i => (R.privRedB i).eval (fun _ => B) ()
  2 * ∑ i ∈ Finset.range (qep + 1),
    ((∑ tL ∈ admissibleLastLeakGuesses (2 + 1) i,
        (2 * CryptoGames.CKA.advantage cka 1 (healEpoch tL) ((R.redCKAPriv tL i).eval (fun _ => privB i) ())
          + 2 * CryptoGames.CKA.advantage cka 1 (healEpoch tL) ((R.redCKAPrivU tL i).eval (fun _ => privB i) ())
          + 2 * CryptoGames.PRFPRNG.advantage prng ((R.redPRNGPriv tL i).eval (fun _ => privB i) ())))
      + fsShortBoundWith C codec ℓ qR q Rfs
          ((R.redFSPriv i).eval (fun _ => privB i) ())
      + 2 * fsShortBoundWith C codec ℓ qR q Rfs
          ((R.redFSPrivCoin i).eval (fun _ => privB i) ()))

/-- Definitional split `fig8ShortBoundWith = fig8AuthPart + fig8PrivPart`. -/
theorem fig8ShortBoundWith_eq_authPart_add_privPart
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (C : Crypto)
    (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (R : Fig8CostedReds Dh encPt C codec ℓ encT idOf lam)
    (Rfs : FsCostedReds C codec ℓ encT idOf) (B : Fig8Adv Pt ℓ) :
    fig8ShortBoundWith Dh encPt C codec ℓ encT idOf lam qep q R Rfs B =
      fig8AuthPart Dh encPt C codec ℓ encT idOf lam qep q R Rfs B +
        fig8PrivPart Dh encPt C codec ℓ encT idOf lam qep q R Rfs B := by
  unfold fig8ShortBoundWith fig8AuthPart fig8AuthBucketTerm fig8PrivPart
  rfl

end TopBound

end Computational.Proofs.SessionCostedFig8.TopAssembly
