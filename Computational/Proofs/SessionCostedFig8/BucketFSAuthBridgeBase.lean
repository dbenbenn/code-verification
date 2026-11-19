/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.BundlesCompilers -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.BundlesAuxSize -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.BundlesMultiFs -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.TopAssembly -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SessionAuthBridge -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.Fig8Atomic -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.SessionShort -- proof-setup: allow-public-import
import Computational.Proofs.SessionCostedFig8.Bundles
import Computational.Proofs.SessionCostedFig8.ProgSizeBounds
import Computational.Proofs.SessionCostedFig8.BucketFSAuthZeroQueries
import Computational.Proofs.SessionCostedFig8.BucketFSAuthCostA
import Computational.Proofs.SessionCostedFig8.BucketFSAuthShort
import Computational.Proofs.SessionCostedFig8.BucketFSAuthCostB
import Computational.Proofs.SessionCostedFig8.BucketFSAuthPotOK
import Computational.Proofs.SessionCostedFig8.BucketFSAuthCompat
import Computational.Proofs.SessionCostedFig8.BucketFSAuthTwoMode
import Computational.Proofs.SessionCostedFig8.BucketFSAuthOneClassSend
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.SessionShort.FSAEADRed -- proof-setup: allow-public-import

/-!
# Base definitions and costed bundle wiring for `BucketFSAuthBridge`
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeBase

public section

set_option autoImplicit false

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

/-! ## 1. Zero-Query Session Vanishing for `fsAuthCompBoundWith` & `fsAeadAuthMixtureCompBound` -/

/-- `fsAuthPrgMix` vanishes whenever `A o` makes `0` `FSAEAD` queries for every `o`. -/
theorem fsAuthPrgMix_eq_zero_of_zero_queries {Pt : Type} [DecidableEq Pt] {α : Type}
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (oa : ProbComp α) (idOf : α → Party → IdentityKey) (maxSkip m : ℕ)
    (A : α → FsAdv Pt ℓ) (h0 : ∀ o, MakesAtMostQueries (A o) 0) :
    fsAuthPrgMix C codec ℓ encT oa idOf maxSkip A m = 0 :=
  BucketFSAuthZeroQueries.fsAuthPrgMix_eq_zero_of_zero_queries C codec ℓ encT oa idOf maxSkip m A h0

/-- `fsAuthSWMix` vanishes whenever `Afalse o` and `Atrue o` make `0` `FSAEAD` queries. -/
theorem fsAuthSWMix_eq_zero_of_zero_queries {Pt : Type} [DecidableEq Pt] {α : Type}
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (oa : ProbComp α) (idOf : α → Party → IdentityKey) (maxSkip q m : ℕ)
    (Afalse Atrue : α → FsAdv Pt ℓ)
    (h0F : ∀ o, MakesAtMostQueries (Afalse o) 0)
    (h0T : ∀ o, MakesAtMostQueries (Atrue o) 0) :
    fsAuthSWMix C codec ℓ encT oa idOf maxSkip q Afalse Atrue m = 0 :=
  BucketFSAuthZeroQueries.fsAuthSWMix_eq_zero_of_zero_queries C codec ℓ encT oa idOf maxSkip q m
    Afalse Atrue h0F h0T

/-- `fsAuthCompBoundMix` vanishes whenever `A stage la o` makes `0` `FSAEAD` queries. -/
theorem fsAuthCompBoundMix_eq_zero_of_zero_queries {Pt : Type} [DecidableEq Pt] {α : Type}
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (oa : ProbComp α) (idOf : α → Party → IdentityKey) (maxSkip qR : ℕ)
    (A : Bool → Bool → α → FsAdv Pt ℓ)
    (h0 : ∀ stage la o, MakesAtMostQueries (A stage la o) 0) :
    fsAuthCompBoundMix C codec ℓ encT oa idOf maxSkip qR A = 0 :=
  BucketFSAuthZeroQueries.fsAuthCompBoundMix_eq_zero_of_zero_queries C codec ℓ encT oa idOf maxSkip
    qR A h0

/-- `fsAuthCompBoundWith` on `fsCostedRedsInst` vanishes whenever `A stage la` makes `0` queries. -/
theorem fsAuthCompBoundWith_inst_eq_zero_of_zero_queries
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (qR : ℕ)
    (hℓ : ℓ < 10 ^ 6) (hinj : Function.Injective encT)
    (A : Bool → Bool → FsAdv Pt ℓ)
    (h0 : ∀ stage la, MakesAtMostQueries (A stage la) 0) :
    fsAuthCompBoundWith C protoSignalCodec ℓ qR
      (fsCostedRedsInst C protoSignalCodec ℓ encT idOf qR) A = 0 :=
  BucketFSAuthZeroQueries.fsAuthCompBoundWith_inst_eq_zero_of_zero_queries C ℓ encT idOf qR hℓ hinj
    A h0

/-- `E2E.fsAeadAuthMixtureCompBound` on `fsCostedRedsInst` vanishes whenever `A stage la o` makes
`0` `FSAEAD` queries. -/
theorem fsAeadAuthMixtureCompBound_inst_eq_zero_of_zero_queries
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {α : Type}
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (oa : ProbComp α)
    (idOf : α → Party → IdentityKey) (qR : ℕ)
    (hℓ : ℓ < 10 ^ 6) (hinj : Function.Injective encT)
    (A : Bool → Bool → α → FsAdv Pt ℓ)
    (h0 : ∀ stage la o, MakesAtMostQueries (A stage la o) 0) :
    CryptoVerification.E2E.fsAeadAuthMixtureCompBound C protoSignalCodec ℓ oa qR
      (fun o => fsCostedRedsInst C protoSignalCodec ℓ encT (idOf o) qR) A = 0 :=
  BucketFSAuthZeroQueries.fsAeadAuthMixtureCompBound_inst_eq_zero_of_zero_queries C ℓ encT oa idOf
    qR hℓ hinj A h0

/-! ## 2. Shallow & Atomic Multi-Session `(tL, par)`-Bucket Reductions, Cost, Size, & `GRedBounded` -/

section BucketMultiFs

open _root_.ReductionDsl (Sig Ty Ops Iface Expr Comp CostedReduction fsaeadHeaderIface
  fig8SmCodec atomicFig8Ops bits reductionSizeBudget)
open _root_.CryptoGames.CKA (dhScheme)
open _root_.CryptoGames.PRFPRNG (prngSMCodec)
open _root_.CryptoGames.Ratchet (rootPRNG)
open _root_.CryptoGames.Ratchet.LibsignalInst (lFS)
open Computational.Proofs.ReductionDsl.PureAuxMacroLift (compCostW)
open Computational.Proofs.ReductionDsl.Fig8Atomic (dhSchemeFb atomicShortPubB
  atomicShortPubB_imp_shortB fsAtomicB)
open Computational.Proofs.ReductionDsl.Fig8ExcessCosts (ckaOpC ckaSampC)
open Computational.Proofs.ReductionDsl.Fig8WeightedParts (fig8AtomicStepBound)
open Computational.Proofs.ReductionDsl.SizeBudgetBridge (bits_mono bits_pos bits_succ_le bits_mul_le)
open Computational.Proofs.SessionCostedFig8.BundlesCompilers (fig8CkaOpsShallow)
open Computational.Proofs.SessionCostedFig8.BundlesAuxSize (exprSizeW compSizeW ckaOpS ckaSampS)
open Computational.Proofs.SessionCostedFig8.BundlesMultiFsBase (
  fsMultiQueryC fsMultiQueryS compListMNodes compQueryCount)
open Computational.Proofs.SessionCostedFig8.BundlesMultiFs (compileFsMultiAtomic
  compileFsMultiAtomic_gRedBounded compileFsMultiAtomic_routerAdvCompat
  compileFsMultiAtomic_isQueryBoundP compileFsMultiAtomic_makesAtMostQueries
  compileFsMultiAtomic_encMsgsOk compileFsMultiAtomic_guardedFSInjectShort)
open Computational.Proofs.SessionCostedFig8.TopAssembly (multiSessRealWinProb
  multiSessEndWinProb bucket_four_branch_fs_le)
open Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth (redFSAuthMultiBucketProg
  redFSAuthMultiBucketProg_totalQueries localAuthBucketMain localAuthBucketForgedHdr
  localAuthBucketMainPar localAuthBucketForgedHdrPar localAuthBucketMain_le_par_false_add_true
  localAuthBucketForgedHdr_le_par_false_add_true)

/-- Definitional 6-conjunct `FsOk` predicate matching `CryptoVerification.LibsignalSession.FsOk`. -/
@[expose] def BucketFsOk {Pt : Type} [DecidableEq Pt] (ℓ qR qd : ℕ)
    (R : CryptoGames.FSAEAD.RatchetAdversary (BitVec 256) (BitVec 256) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) LibsignalCiphertextWithSalt32) : Prop :=
  CryptoGames.FSAEAD.MakesAtMostQueries R qR ∧
    CryptoGames.FSAEAD.MakesAtMostDecQueries R qd ∧
    CryptoGames.FSAEAD.EqualPubChallenges R ∧
    CryptoGames.FSAEAD.AllQueriesInOneADClass (fun h : Header Pt => h.1) R ∧
    CryptoGames.FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB) R ∧
    GuardedFSInjectShort R

/-- Shallow-ops instantiation of `BucketPRNGAuth.redFSAuthMultiBucketProg` over
`Bundles.fig8CkaOpsShallow` and `fsaeadMultiHeaderAdIface`. -/
@[expose] def redFSAuthMultiBucketShallow
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (L B0 qep : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool) :
    CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (fsaeadMultiHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (prngSMCodec (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      .unit .unit .bool .bool :=
  let _ : Inhabited Pt := ⟨0⟩
  redFSAuthMultiBucketProg L B0 1 qep maxForwardJumps gMain la tL par

/-- Atomic single-session `fsaeadHeaderIface ℓ Pt` compilation of `redFSAuthMultiBucketShallow`
at router `(stage, la, idx)`. -/
@[expose] def redFSAuthMultiBucketAtomic
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (stage la : Bool) (idx qep qR B0 L : ℕ) (gMain : Bool) (tL : Option ℕ) (par : Bool) :
    CostedReduction (atomicFig8Ops ℓ Pt C Dh encPt encT lam) (fsaeadHeaderIface ℓ Pt)
      (CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (fig8SmCodec ℓ Pt) .unit .unit .bool .bool :=
  compileFsMultiAtomic ℓ Pt C Dh encPt encT idOf lam stage la idx qep qR B0
    (redFSAuthMultiBucketShallow ℓ Pt C Dh encPt encT idOf lam L B0 qep gMain la tL par)

theorem healEpoch_le_of_forall_some {tL : Option ℕ} {qep : ℕ}
    (htL : ∀ x, tL = some x → x ≤ qep + 3) : healEpoch tL ≤ qep + 6 := by
  cases tL with
  | none => simp [healEpoch]
  | some x => have := htL x rfl; simp [healEpoch]; omega

theorem optGetD_le_of_forall_some {tL : Option ℕ} {qep : ℕ}
    (htL : ∀ x, tL = some x → x ≤ qep + 3) : tL.getD 0 ≤ qep + 3 := by
  cases tL with
  | none => simp
  | some x => simpa using htL x rfl

/-- Weighted step-cost bound for `redFSAuthMultiBucketShallow` discharging `hparts` of
`BundlesMultiFs.compileFsMultiAtomic_gRedBounded`. -/
theorem redFSAuthMultiBucketProg_parts_le
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (q qep qR B0 : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool)
    (hB0 : B0 = (q + 1) * (maxForwardJumps + 1))
    (hqR : qR ≤ 2 * q + 2)
    (htL : ∀ x, tL = some x → x ≤ qep + 3) :
    let R := redFSAuthMultiBucketShallow ℓ Pt C Dh encPt encT idOf lam (q + 1) B0 qep gMain la tL par
    compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qep qR B0) R.init +
        compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qep qR B0) R.finish + 100000 ≤
          fig8AtomicStepBound q qep ∧
      compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qep qR B0) R.handle + 200000 ≤
        fig8AtomicStepBound q qep := by
  let _ : Inhabited Pt := ⟨0⟩
  have htH : healEpoch tL ≤ qep + 6 := healEpoch_le_of_forall_some htL
  have htL0 : tL.getD 0 ≤ qep + 3 := optGetD_le_of_forall_some htL
  have hbH : bits (healEpoch tL) ≤ bits qep + 6 := by
    have h1 : bits (healEpoch tL) ≤ bits (((((qep + 1) + 1) + 1) + 1) + 1 + 1) := bits_mono (by omega)
    have h2 := bits_succ_le ((((qep + 1) + 1) + 1) + 1 + 1)
    have h3 := bits_succ_le ((((qep + 1) + 1) + 1) + 1)
    have h4 := bits_succ_le (((qep + 1) + 1) + 1)
    have h5 := bits_succ_le ((qep + 1) + 1)
    have h6 := bits_succ_le (qep + 1)
    have h7 := bits_succ_le qep
    omega
  have hbL0 : bits (tL.getD 0) ≤ bits qep + 3 := by
    have h1 : bits (tL.getD 0) ≤ bits (((qep + 1) + 1) + 1) := bits_mono (by omega)
    have h3 := bits_succ_le ((qep + 1) + 1)
    have h4 := bits_succ_le (qep + 1)
    have h5 := bits_succ_le qep
    omega
  have hbB0 : bits B0 ≤ B0 + 1 := ProgSizeBounds.bits_le_succ_nat B0
  have hbSkip : bits maxForwardJumps ≤ maxForwardJumps + 1 :=
    ProgSizeBounds.bits_le_succ_nat maxForwardJumps
  dsimp only [redFSAuthMultiBucketShallow]
  set R0 := redFSAuthMultiBucketProg (q + 1) B0 1 qep maxForwardJumps gMain la tL par
  obtain ⟨hIF, hH⟩ :
      compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qep qR B0) R0.init +
          compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qep qR B0) R0.finish ≤
            2800 * (q + 1) + bits qep + 6 * bits (tL.getD 0) + 12 * bits (healEpoch tL) + 30000 ∧
        compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qep qR B0) R0.handle ≤
          20 * B0 + 3 * bits B0 + 16000 * (q + 1) + 16 * bits qep + 10 * bits (tL.getD 0) +
            15 * bits (healEpoch tL) + bits maxForwardJumps + 4000 * qR + 3800000 :=
    BucketFSAuthCostA.redFSAuthMultiBucketProg_generic_costW_le
      B0 (q + 1) qep qR maxForwardJumps gMain la tL par
  unfold fig8AtomicStepBound maxForwardJumps at *
  dsimp only at hIF hH ⊢
  generalize bits qep = bq at *
  generalize bits B0 = bB0 at *
  generalize bits 25000 = bSk at *
  have hqbq : 0 ≤ (q + 1) * (3 * bq + 60) := Nat.zero_le _
  generalize (q + 1) * (3 * bq + 60) = qbq at *
  constructor <;> omega

/-- Bit-length helper showing `2 * bits (q + 1) ≤ bits (ratchetCostBudget q qep)`. -/
private theorem two_mul_bits_succ_le_bits_ratchetCostBudget (q qep : ℕ) :
    2 * bits (q + 1) ≤ bits (ratchetCostBudget q qep) := by
  set k := Nat.log 2 (q + 1)
  have hpow : 2 ^ k ≤ q + 1 := Nat.pow_log_le_self 2 (by omega)
  have hsq : 2 ^ (k + k + 1) ≤ ratchetCostBudget q qep := by
    have hbp : 1 ≤ bits qep := bits_pos qep
    have hkk : 2 ^ k * 2 ^ k ≤ (q + 1) * (q + 1) := Nat.mul_le_mul hpow hpow
    have h212 : (2 ^ 12 : ℕ) = 4096 := rfl
    rw [Nat.pow_add, Nat.pow_add, Nat.pow_one]
    unfold ratchetCostBudget
    rw [h212, Nat.pow_two]
    nlinarith
  have hlog : k + k + 1 ≤ Nat.log 2 (ratchetCostBudget q qep) :=
    Nat.le_log_of_pow_le (by decide) hsq
  unfold bits
  omega

private theorem ckaOpS_eq_bundles (B0 : ℕ) :
    ckaOpS B0 = Computational.Proofs.SessionCostedFig8.Bundles.ckaOpS B0 := by
  funext o; cases o <;> rfl

private theorem ckaSampS_eq_bundles :
    ckaSampS = Computational.Proofs.SessionCostedFig8.Bundles.ckaSampS := rfl

private theorem exprSizeW_eq_bundles {S : Sig} {O : Ops S} (opS : O.Op → ℕ)
    {Γ : List (Ty S)} {t : Ty S} (e : Expr O Γ t) :
    exprSizeW opS e = Computational.Proofs.SessionCostedFig8.Bundles.exprSizeW opS e := by
  induction e <;> simp only [exprSizeW, Computational.Proofs.SessionCostedFig8.Bundles.exprSizeW, *]

private theorem compSizeW_eq_bundles {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} (opS : O.Op → ℕ) (sS : I.smp.Samp → ℕ) (qS : I.Tag → ℕ)
    {Γ : List (Ty S)} {t : Ty S} (c : Comp O I Γ t) :
    compSizeW opS sS qS c =
      Computational.Proofs.SessionCostedFig8.Bundles.compSizeW opS sS qS c := by
  induction c <;>
    simp only [compSizeW, Computational.Proofs.SessionCostedFig8.Bundles.compSizeW,
      exprSizeW_eq_bundles, *]

theorem redFSAuthMultiBucketProg_size_le
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (q qep qR B0 : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool)
    (hB0 : B0 = (q + 1) * (maxForwardJumps + 1))
    (hqR : qR ≤ 2 * q + 2)
    (htL : ∀ x, tL = some x → x ≤ qep + 3)
    (hqep : qep ≤ 4096 * q + 100000000 := by omega) :
    let R := redFSAuthMultiBucketShallow ℓ Pt C Dh encPt encT idOf lam (q + 1) B0 qep gMain la tL par
    compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qep qR B0) R.init +
      compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qep qR B0) R.handle +
      compSizeW (ckaOpS B0) ckaSampS (fsMultiQueryS qep qR B0) R.finish + 400 ≤
        1400000 + 585 * bits (ratchetCostBudget q qep) := by
  let _ : Inhabited Pt := ⟨0⟩
  have htH : healEpoch tL ≤ qep + 6 := healEpoch_le_of_forall_some htL
  have htL0 : tL.getD 0 ≤ qep + 3 := optGetD_le_of_forall_some htL
  have hb27 : bits (2 ^ 27) = 28 := by decide
  have hb15 : bits (2 ^ 15) = 16 := by decide
  have hbSk : bits maxForwardJumps = 15 := by decide
  have h1 : bits (qep + qR + B0 + 1) ≤ 28 + bits (q + 1) := by
    have hm : qep + qR + B0 + 1 ≤ 2 ^ 27 * (q + 1) := by
      rw [hB0]; unfold maxForwardJumps; omega
    exact (bits_mono hm).trans ((bits_mul_le _ _).trans (by rw [hb27]))
  have h2 : bits B0 ≤ 16 + bits (q + 1) := by
    have hm : B0 ≤ 2 ^ 15 * (q + 1) := by
      rw [hB0]; unfold maxForwardJumps; omega
    exact (bits_mono hm).trans ((bits_mul_le _ _).trans (by rw [hb15]))
  have h3 : bits qep ≤ 28 + bits (q + 1) := by
    have hm : qep ≤ 2 ^ 27 * (q + 1) := by omega
    exact (bits_mono hm).trans ((bits_mul_le _ _).trans (by rw [hb27]))
  have h4 : bits (tL.getD 0) ≤ 28 + bits (q + 1) := by
    have hm : tL.getD 0 ≤ 2 ^ 27 * (q + 1) := by omega
    exact (bits_mono hm).trans ((bits_mul_le _ _).trans (by rw [hb27]))
  have h5 : bits (healEpoch tL) ≤ 28 + bits (q + 1) := by
    have hm : healEpoch tL ≤ 2 ^ 27 * (q + 1) := by omega
    exact (bits_mono hm).trans ((bits_mul_le _ _).trans (by rw [hb27]))
  have hbud := two_mul_bits_succ_le_bits_ratchetCostBudget q qep
  intro R
  rw [compSizeW_eq_bundles, compSizeW_eq_bundles, compSizeW_eq_bundles,
    ckaOpS_eq_bundles, ckaSampS_eq_bundles]
  have hgen :
      Computational.Proofs.SessionCostedFig8.Bundles.compSizeW
          (Computational.Proofs.SessionCostedFig8.Bundles.ckaOpS B0)
          Computational.Proofs.SessionCostedFig8.Bundles.ckaSampS
          (fsMultiQueryS qep qR B0) R.init +
        Computational.Proofs.SessionCostedFig8.Bundles.compSizeW
          (Computational.Proofs.SessionCostedFig8.Bundles.ckaOpS B0)
          Computational.Proofs.SessionCostedFig8.Bundles.ckaSampS
          (fsMultiQueryS qep qR B0) R.handle +
        Computational.Proofs.SessionCostedFig8.Bundles.compSizeW
          (Computational.Proofs.SessionCostedFig8.Bundles.ckaOpS B0)
          Computational.Proofs.SessionCostedFig8.Bundles.ckaSampS
          (fsMultiQueryS qep qR B0) R.finish ≤
        280 * bits (qep + qR + B0 + 1) + 12 * bits B0 + 290 * bits (q + 1) + 45 * bits qep +
          130 * bits (tL.getD 0) + 140 * bits (healEpoch tL) + 10 * bits maxForwardJumps + 410000 :=
    BucketFSAuthCostB.redFSAuthMultiBucketProg_generic_sizeW_le
      B0 (q + 1) qep qR maxForwardJumps gMain la tL par
  omega

theorem redFSAuthMultiBucketShallow_totalQueries
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (q B0 qep : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool) :
    (redFSAuthMultiBucketShallow ℓ Pt C Dh encPt encT idOf lam (q + 1) B0 qep gMain la tL par).totalQueries
      (fun _ => 1) (fun _ => 0) q ≤ 2 * q := by
  let _ : Inhabited Pt := ⟨0⟩
  dsimp only [redFSAuthMultiBucketShallow]
  exact redFSAuthMultiBucketProg_totalQueries (q + 1) B0 1 qep maxForwardJumps gMain la tL par q

private theorem redFSAuthMultiBucketProg_listM_and_qCount
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    {ckaInitA ckaInitB : KC → Γ} {ckaSend : Γ → CCoins → Γ × T × I} {ckaReceive : Γ → T → Γ × I}
    {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
    {fsInitSender : K → SS} {fsInitReceiver : K → RS}
    {fsSend : SS → Header T → M → SS × E} {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
    {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
    {lam : I} {defaultE : E}
    {sampKR : ProbComp KR} {sampKC : ProbComp KC} {sampCCoins : ProbComp CCoins}
    {sampI : ProbComp I} {sampK : ProbComp K}
    (L B0 Δcka qep maxSkip : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool) :
    let R := redFSAuthMultiBucketProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B0 Δcka qep maxSkip gMain la tL par
    compListMNodes R.init + compListMNodes R.handle + compListMNodes R.finish ≤ 50 ∧
      compQueryCount R.init + compQueryCount R.handle + compQueryCount R.finish ≤ 60 := by
  intro R
  refine ⟨?_, ?_⟩
  · simp only [R, redFSAuthMultiBucketProg,
      Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.initFSMultiBucketAuthEStateC,
      Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.hooksFSMultiBucketAuthC,
      Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.lookupMultiBucketFC,
      Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.rootFSMultiBucketAuthC,
      Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketAuthStartSendC,
      Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketAuthStartRecvC,
      Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketAuthFsSendC,
      Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketAuthFsRecvC,
      Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketAuthCommitC,
      Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketAuthRevealC,
      Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.rangeListBucketC,
      _root_.CryptoGames.SM.Engine.deliverEC, _root_.CryptoGames.SM.Engine.injectEC,
      _root_.CryptoGames.SM.Engine.vSendC, _root_.CryptoGames.SM.Engine.vSendStep1C,
      _root_.CryptoGames.SM.Engine.vRecvC, _root_.CryptoGames.SM.Engine.vRecvStep1C,
      _root_.CryptoGames.SM.Engine.commitEC,
      compListMNodes, Nat.add_zero]
    omega
  · simp only [R, redFSAuthMultiBucketProg,
      Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.initFSMultiBucketAuthEStateC,
      Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.hooksFSMultiBucketAuthC,
      Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.lookupMultiBucketFC,
      Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.rootFSMultiBucketAuthC,
      Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketAuthStartSendC,
      Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketAuthStartRecvC,
      Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketAuthFsSendC,
      Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketAuthFsRecvC,
      Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketAuthCommitC,
      Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketAuthRevealC,
      Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.rangeListBucketC,
      _root_.CryptoGames.SM.Engine.deliverEC, _root_.CryptoGames.SM.Engine.injectEC,
      _root_.CryptoGames.SM.Engine.vSendC, _root_.CryptoGames.SM.Engine.vSendStep1C,
      _root_.CryptoGames.SM.Engine.vRecvC, _root_.CryptoGames.SM.Engine.vRecvStep1C,
      _root_.CryptoGames.SM.Engine.commitEC,
      compQueryCount, Nat.add_zero, Nat.zero_add]
    omega

/-- Packaged `GRedBounded` within `ratchetCostBudget q qep` for `redFSAuthMultiBucketAtomic`. -/
theorem redFSAuthMultiBucketAtomic_gRedBounded
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (stage la : Bool) (idx q qep qR B0 : ℕ) (gMain : Bool) (tL : Option ℕ) (par : Bool)
    (hB0 : B0 = (q + 1) * (maxForwardJumps + 1))
    (hqR : qR ≤ 2 * q + 2)
    (htL : ∀ x, tL = some x → x ≤ qep + 3)
    (hqep : qep ≤ 4096 * q + 100000000 := by omega) :
    GRedBounded
      (redFSAuthMultiBucketAtomic ℓ Pt C Dh encPt encT idOf lam stage la idx qep qR B0 (q + 1)
        gMain tL par)
      (fun _ => 1) (fun _ => 0) q (2 * q) (ratchetCostBudget q qep) := by
  let _ : Inhabited Pt := ⟨0⟩
  have hB0_le : B0 ≤ (2 * q + 2) * (maxForwardJumps + 1) := by
    rw [hB0]
    exact Nat.mul_le_mul_right _ (by omega)
  obtain ⟨hLM, hQC⟩ :
      let R := redFSAuthMultiBucketShallow ℓ Pt C Dh encPt encT idOf lam (q + 1) B0 qep gMain la tL par
      compListMNodes R.init + compListMNodes R.handle + compListMNodes R.finish ≤ 50 ∧
        compQueryCount R.init + compQueryCount R.handle + compQueryCount R.finish ≤ 60 := by
    dsimp only [redFSAuthMultiBucketShallow]
    exact redFSAuthMultiBucketProg_listM_and_qCount (q + 1) B0 1 qep maxForwardJumps gMain la tL par
  dsimp only [redFSAuthMultiBucketAtomic]
  exact compileFsMultiAtomic_gRedBounded ℓ Pt C Dh encPt encT idOf lam stage la idx qep qR B0
    (redFSAuthMultiBucketShallow ℓ Pt C Dh encPt encT idOf lam (q + 1) B0 qep gMain la tL par)
    q (2 * q) hB0_le
    (redFSAuthMultiBucketProg_parts_le ℓ Pt C Dh encPt encT idOf lam q qep qR B0 gMain la tL par
      hB0 hqR htL)
    (redFSAuthMultiBucketProg_size_le ℓ Pt C Dh encPt encT idOf lam q qep qR B0 gMain la tL par
      hB0 hqR htL hqep)
    (redFSAuthMultiBucketShallow_totalQueries ℓ Pt C Dh encPt encT idOf lam q B0 qep gMain la
      tL par)
    le_rfl hLM hQC

/-! ## 3. Per-Session Query Bounds, Inactive-Slot Vanishing, `TwoModeMultiSessBounds`, & `FsOk` -/

attribute [local irreducible] redFSAuthMultiBucketProg in
/-- Per-session query bound `min (2 * q) (q + 2)` on `redFSAuthMultiBucketShallow.eval` for every
session index `s`. -/
theorem redFSAuthMultiBucketProg_sess_isQueryBoundP
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (q B0 qep : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool)
    (A : OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) (s : ℕ) :
    ((redFSAuthMultiBucketShallow ℓ Pt C Dh encPt encT idOf lam (q + 1) B0 qep gMain la tL par).eval
      (fun _ => A) ()).IsQueryBoundP
      (fun t => (match t with
        | .inl _ => false
        | .inr ⟨s', _⟩ => decide (s' = s)) = true) (min (2 * q) (q + 2)) := by
  let _ : Inhabited Pt := ⟨0⟩
  dsimp only [redFSAuthMultiBucketShallow]
  exact (BucketFSAuthPotOK.redFSAuthMultiBucketProg_sess_isQueryBoundP_gen
    (q + 1) B0 1 qep maxForwardJumps gMain la tL par s q A hq).of_imp fun x hx => by
      rcases x with _ | ⟨_, _⟩ <;> exact hx

attribute [local irreducible] redFSAuthMultiBucketProg in
/-- Inactive-slot `0`-query bound: if `idx` does not match both `(gMain = decide (idx % (q + 1) = 0))`
and `(par = decide (Party.senderOf (healEpoch tL + idx / (q + 1)) == .A))` (or if
`idx ≥ ((qep + 2) - healEpoch tL) * (q + 1)`), session `idx` receives `0` queries. -/
theorem redFSAuthMultiBucketProg_inactive_isQueryBoundP_zero
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (q B0 qep : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool)
    (A : OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) (idx : ℕ)
    (hinact : idx ≥ ((qep + 2) - healEpoch tL) * (q + 1) ∨
      ¬(decide (idx % (q + 1) = 0) = gMain ∧
        decide (Party.senderOf (healEpoch tL + idx / (q + 1)) == .A) = par)) :
    ((redFSAuthMultiBucketShallow ℓ Pt C Dh encPt encT idOf lam (q + 1) B0 qep gMain la tL par).eval
      (fun _ => A) ()).IsQueryBoundP
      (fun t => (match t with
        | .inl _ => false
        | .inr ⟨s', _⟩ => decide (s' = idx)) = true) 0 := by
  let _ : Inhabited Pt := ⟨0⟩
  dsimp only [redFSAuthMultiBucketShallow]
  exact (BucketFSAuthCompat.redFSAuthMultiBucketProg_inactive_isQueryBoundP_zero_gen
    q B0 1 qep maxForwardJumps gMain la tL par idx A hq hinact).of_imp fun x hx => by
      rcases x with _ | ⟨_, _⟩ <;> exact hx

attribute [local irreducible] redFSAuthMultiBucketProg in
private theorem redFSAuthMultiBucketShallow_oneADClass_aux
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (q B0 qep : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool) (j : ℕ)
    (A : OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    ((redFSAuthMultiBucketShallow ℓ Pt C Dh encPt encT idOf lam (q + 1) B0 qep gMain la tL par).eval
      (fun _ => A) ()).IsQueryBoundP
      (fun t => (match t with
        | .inl _ => false
        | .inr ⟨s', o'⟩ =>
          decide (s' = j) &&
            CryptoGames.FSAEAD.queryADOutsideClass
              (SS := RatchetSenderState (BitVec 256))
              (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
              (fun h : Header Pt => h.1) (healEpoch tL + j / (q + 1)) (.inr o')) = true) 0 := by
  let _ : Inhabited Pt := ⟨0⟩
  dsimp only [redFSAuthMultiBucketShallow]
  exact (BucketFSAuthOneClassSend.redFSAuthMultiBucketProg_oneADClass_gen
    q B0 1 qep maxForwardJumps gMain la tL par j A hq).of_imp fun x hx => by
      rcases x with _ | ⟨_, _⟩ <;> exact hx

attribute [local irreducible] redFSAuthMultiBucketProg in
private theorem redFSAuthMultiBucketShallow_guardedShort_aux
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (hℓ : ℓ < 10 ^ 6) (q B0 qep : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool)
    (A : OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (hg : CryptoGames.LibsignalSM.Proofs.SessionShort.GuardedSMShort A) :
    CryptoVerification.E2E.Signed.SessionWireQueries.GuardedMultiInjectShort
      ((redFSAuthMultiBucketShallow ℓ Pt C Dh encPt encT idOf lam (q + 1) B0 qep gMain la tL par).eval
        (fun _ => A) ()) := by
  let _ : Inhabited Pt := ⟨0⟩
  dsimp only [redFSAuthMultiBucketShallow, fig8CkaOpsShallow]
  exact BucketFSAuthShort.redFSAuthMultiBucketProg_guardedMultiInjectShort
    (BucketFSAuthShort.fsAtomicB_send_short C ℓ encT idOf B0 hℓ)
    (by decide) (q + 1) B0 1 qep maxForwardJumps gMain la tL par A hg

attribute [local irreducible] redFSAuthMultiBucketProg in
private theorem redFSAuthMultiBucketShallow_badTrOrCh_aux
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (q B0 qep : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool)
    (A : OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (hsh : CryptoGames.LibsignalSM.Proofs.SessionShort.FSAEADRed.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    ((redFSAuthMultiBucketShallow ℓ Pt C Dh encPt encT idOf lam (q + 1) B0 qep gMain la tL par).eval
      (fun _ => A) ()).IsQueryBoundP
      (fun t => BucketFSAuthShort.badTrOrCh
        (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) t = true) 0 := by
  let _ : Inhabited Pt := ⟨0⟩
  dsimp only [redFSAuthMultiBucketShallow, fig8CkaOpsShallow]
  exact BucketFSAuthShort.redFSAuthMultiBucketProg_badTrOrCh
    (ok := fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
    (q + 1) B0 1 qep maxForwardJumps gMain la tL par A hsh

private theorem redFSAuthMultiBucketShallow_eq_twoMode :
    @redFSAuthMultiBucketShallow = @BucketFSAuthTwoMode.redFSAuthMultiBucketShallow' :=
  rfl

/-- `TwoModeMultiSessBounds` for `multiSessPubToAD` over `redFSAuthMultiBucketShallow` across any
prefix distribution `oa : ProbComp α`. -/
theorem redFSAuthMultiBucketProg_twoModeMultiSessBounds
    {α : Type} (oa : ProbComp α)
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : α → Party → IdentityKey) (lam : α → Pt)
    (hℓ : ℓ < 10 ^ 6) (q B0 qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par : Bool)
    (A : α → OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (hq : ∀ o, CryptoGames.SM.MakesAtMostQueries (A o) q)
    (heq : ∀ o,
      CryptoGames.SM.EqualPubChalls (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1) (A o))
    (hsh : ∀ o,
      CryptoGames.LibsignalSM.Proofs.SessionShort.FSAEADRed.SendMsgsOk
        (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) (A o))
    (hg : ∀ o,
      CryptoGames.LibsignalSM.Proofs.SessionShort.GuardedSMShort (A o)) :
    TwoModeMultiSessBounds maxForwardJumps (min (2 * q) (q + 2))
      (((qep + 2) - healEpoch tL) * (q + 1)) q
      (fun la o =>
        multiSessPubToAD protoSignalCodec
          ((redFSAuthMultiBucketShallow ℓ Pt C Dh encPt encT (idOf o) (lam o) (q + 1) B0 qep
              gMain la tL par).eval (fun _ => A o) ())) := by
  let _ := oa
  let _ := heq
  rw [redFSAuthMultiBucketShallow_eq_twoMode]
  exact BucketFSAuthTwoMode.redFSAuthMultiBucketProg_twoModeMultiSessBounds_of_parts
    ℓ Pt C Dh encPt encT idOf lam q B0 qep gMain tL par A hq hsh
    (fun la o idx hidx => by
      rw [← redFSAuthMultiBucketShallow_eq_twoMode]
      exact redFSAuthMultiBucketProg_inactive_isQueryBoundP_zero ℓ Pt C Dh encPt encT (idOf o)
        (lam o) q B0 qep gMain la tL par (A o) (hq o) idx (Or.inl hidx))
    (fun la o => by
      rw [← redFSAuthMultiBucketShallow_eq_twoMode]
      exact redFSAuthMultiBucketShallow_guardedShort_aux ℓ Pt C Dh encPt encT (idOf o) (lam o)
        hℓ q B0 qep gMain la tL par (A o) (hg o))
    (fun la j o => ⟨healEpoch tL + j / (q + 1), by
      rw [← redFSAuthMultiBucketShallow_eq_twoMode]
      exact redFSAuthMultiBucketShallow_oneADClass_aux ℓ Pt C Dh encPt encT (idOf o) (lam o)
        q B0 qep gMain la tL par j (A o) (hq o)⟩)

theorem redFSAuthMultiBucketShallow_noCr
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (L B0 qep : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool) (q : ℕ)
    (A : OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    ((redFSAuthMultiBucketShallow ℓ Pt C Dh encPt encT idOf lam L B0 qep gMain la tL par).eval
      (fun _ => A) ()).IsQueryBoundP
      (fun t => (match t with | .inr ⟨_, .inl (.inl (.inr _))⟩ => true | _ => false) = true) 0 := by
  rw [redFSAuthMultiBucketShallow_eq_twoMode]
  exact BucketFSAuthTwoMode.redFSAuthMultiBucketShallow_noCr
    ℓ Pt C Dh encPt encT idOf lam L B0 qep gMain la tL par q A hq

/-- `RouterAdvCompat` for `redFSAuthMultiBucketAtomic` across any prefix distribution
`oa : ProbComp α`. -/
theorem redFSAuthMultiBucketAtomic_routerAdvCompat
    {α : Type} (oa : ProbComp α)
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : α → Party → IdentityKey) (lam : α → Pt)
    (hℓ : ℓ < 10 ^ 6) (hinj : Function.Injective encT)
    (q B0 qep : ℕ) (hB0 : B0 = (q + 1) * (maxForwardJumps + 1))
    (gMain : Bool) (tL : Option ℕ) (par : Bool)
    (A : α → OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (hq : ∀ o ∈ support oa, CryptoGames.SM.MakesAtMostQueries (A o) q)
    (hsh : ∀ o ∈ support oa,
      CryptoGames.LibsignalSM.Proofs.SessionShort.FSAEADRed.SendMsgsOk
        (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) (A o)) :
    RouterAdvCompat C protoSignalCodec ℓ encT oa idOf maxForwardJumps (min (2 * q) (q + 2))
      (((qep + 2) - healEpoch tL) * (q + 1))
      (fun la o =>
        multiSessPubToAD protoSignalCodec
          ((redFSAuthMultiBucketShallow ℓ Pt C Dh encPt encT (idOf o) (lam o) (q + 1) B0 qep
              gMain la tL par).eval (fun _ => A o) ()))
      (fun stage la idx o =>
        (redFSAuthMultiBucketAtomic ℓ Pt C Dh encPt encT (idOf o) (lam o) stage la idx qep
            (min (2 * q) (q + 2)) B0 (q + 1) gMain tL par).eval (fun _ => A o) ()) := by
  have hMB0 : ((qep + 2) - healEpoch tL) * (q + 1) ≤ (qep + 2) * B0 + B0 * B0 + 1 := by
    have hB0_ge : q + 1 ≤ B0 := by
      rw [hB0]; exact Nat.le_mul_of_pos_right _ (by unfold maxForwardJumps; omega)
    have h1 : ((qep + 2) - healEpoch tL) * (q + 1) ≤ (qep + 2) * B0 :=
      Nat.mul_le_mul (Nat.sub_le _ _) hB0_ge
    omega
  have hqR : min (2 * q) (q + 2) ≤ B0 := by rw [hB0]; unfold maxForwardJumps; omega
  refine compileFsMultiAtomic_routerAdvCompat ℓ Pt C Dh encPt encT oa idOf lam hℓ hinj
    qep (min (2 * q) (q + 2)) (((qep + 2) - healEpoch tL) * (q + 1)) B0 hMB0 hqR
    (fun la _ o => redFSAuthMultiBucketShallow ℓ Pt C Dh encPt encT (idOf o) (lam o) (q + 1) B0
      qep gMain la tL par) A ?_ ?_ ?_
  · intro la o ho s
    exact ((redFSAuthMultiBucketProg_sess_isQueryBoundP ℓ Pt C Dh encPt encT (idOf o) (lam o)
      q B0 qep gMain la tL par (A o) (hq o ho) s).mono (by omega)).of_imp fun x hx => by
        rcases x with _ | ⟨_, _⟩ <;> exact hx
  · intro la o ho
    exact (redFSAuthMultiBucketShallow_noCr ℓ Pt C Dh encPt encT (idOf o) (lam o) (q + 1) B0 qep
      gMain la tL par q (A o) (hq o ho)).of_imp fun x hx => by
        rcases x with _ | ⟨_, ((_ | _) | _) | _⟩ <;> exact hx
  · intro la o ho s
    have hBad := redFSAuthMultiBucketShallow_badTrOrCh_aux ℓ Pt C Dh encPt encT (idOf o) (lam o)
      q B0 qep gMain la tL par (A o) (hsh o ho)
    refine BucketFSAuthShort.isQueryBoundP_of_imp (fun t ht => ?_) hBad
    rcases t with _ | ⟨s', qv⟩
    · simp at ht
    · rw [show @atomicShortB = @atomicShortPubB from rfl] at ht
      rcases qv with ((((⟨_, m⟩ | ⟨_, m₀, m₁⟩) | _) | _) | _) | _
      · simp only [BucketFSAuthShort.badTrOrCh, CryptoGames.FSAEAD.encBadMsg, Bool.and_eq_true] at ht ⊢
        exact ht.2
      · rfl
      · simp only [CryptoGames.FSAEAD.encBadMsg, Bool.and_false, reduceCtorEq] at ht
      · simp only [CryptoGames.FSAEAD.encBadMsg, Bool.and_false, reduceCtorEq] at ht
      · simp only [CryptoGames.FSAEAD.encBadMsg, Bool.and_false, reduceCtorEq] at ht
      · simp only [CryptoGames.FSAEAD.encBadMsg, Bool.and_false, reduceCtorEq] at ht

/-- Per-session `FSAEAD.MakesAtMostQueries ... (min (2 * q) (q + 2))` for
`redFSAuthMultiBucketAtomic`. -/
theorem redFSAuthMultiBucketAtomic_makesAtMostQueries
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (stage la : Bool) (idx q qep qR B0 : ℕ) (gMain : Bool) (tL : Option ℕ) (par : Bool)
    (A : OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    CryptoGames.FSAEAD.MakesAtMostQueries
      ((redFSAuthMultiBucketAtomic ℓ Pt C Dh encPt encT idOf lam stage la idx qep qR B0 (q + 1)
          gMain tL par).eval (fun _ => A) ())
      (min (2 * q) (q + 2)) :=
  compileFsMultiAtomic_makesAtMostQueries ℓ Pt C Dh encPt encT idOf lam stage la idx qep qR B0
    (min (2 * q) (q + 2))
    (redFSAuthMultiBucketShallow ℓ Pt C Dh encPt encT idOf lam (q + 1) B0 qep gMain la tL par) A
    ((redFSAuthMultiBucketProg_sess_isQueryBoundP ℓ Pt C Dh encPt encT idOf lam q B0 qep gMain la
      tL par A hq idx).of_imp fun x hx => by
        rcases x with _ | ⟨_, _⟩ <;> exact hx)

/-- Inactive-slot `FSAEAD.MakesAtMostQueries ... 0` for `redFSAuthMultiBucketAtomic`. -/
theorem redFSAuthMultiBucketAtomic_inactive_makesAtMostQueries_zero
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (stage la : Bool) (idx q qep qR B0 : ℕ) (gMain : Bool) (tL : Option ℕ) (par : Bool)
    (A : OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (hq : CryptoGames.SM.MakesAtMostQueries A q)
    (hinact : idx ≥ ((qep + 2) - healEpoch tL) * (q + 1) ∨
      ¬(decide (idx % (q + 1) = 0) = gMain ∧
        decide (Party.senderOf (healEpoch tL + idx / (q + 1)) == .A) = par)) :
    CryptoGames.FSAEAD.MakesAtMostQueries
      ((redFSAuthMultiBucketAtomic ℓ Pt C Dh encPt encT idOf lam stage la idx qep qR B0 (q + 1)
          gMain tL par).eval (fun _ => A) ()) 0 :=
  compileFsMultiAtomic_makesAtMostQueries ℓ Pt C Dh encPt encT idOf lam stage la idx qep qR B0 0
    (redFSAuthMultiBucketShallow ℓ Pt C Dh encPt encT idOf lam (q + 1) B0 qep gMain la tL par) A
    ((redFSAuthMultiBucketProg_inactive_isQueryBoundP_zero ℓ Pt C Dh encPt encT idOf lam q B0 qep
      gMain la tL par A hq idx hinact).of_imp fun x hx => by
        rcases x with _ | ⟨_, _⟩ <;> exact hx)

/-- Inactive-slot `fsAuthCompBoundWith = 0` for `redFSAuthMultiBucketAtomic` (directly discharging
`hZero` of `TopAssembly.bucket_four_branch_fs_le`). -/
theorem redFSAuthMultiBucketAtomic_inactive_fsAuthCompBoundWith_eq_zero
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (hℓ : ℓ < 10 ^ 6) (hinj : Function.Injective encT)
    (idx q qep qR B0 : ℕ) (gMain : Bool) (tL : Option ℕ) (par : Bool)
    (A : OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (hq : CryptoGames.SM.MakesAtMostQueries A q)
    (hinact : idx ≥ ((qep + 2) - healEpoch tL) * (q + 1) ∨
      ¬(decide (idx % (q + 1) = 0) = gMain ∧
        decide (Party.senderOf (healEpoch tL + idx / (q + 1)) == .A) = par)) :
    fsAuthCompBoundWith C protoSignalCodec ℓ qR
      (fsCostedRedsInst C protoSignalCodec ℓ encT idOf qR)
      (fun stage la =>
        (redFSAuthMultiBucketAtomic ℓ Pt C Dh encPt encT idOf lam stage la idx qep qR B0 (q + 1)
          gMain tL par).eval (fun _ => A) ()) = 0 :=
  fsAuthCompBoundWith_inst_eq_zero_of_zero_queries C ℓ encT idOf qR hℓ hinj _ fun stage la =>
    redFSAuthMultiBucketAtomic_inactive_makesAtMostQueries_zero ℓ Pt C Dh encPt encT idOf lam
      stage la idx q qep qR B0 gMain tL par A hq hinact

/-- Inactive-slot `fsAeadAuthMixtureCompBound = 0` for `redFSAuthMultiBucketAtomic` (directly
discharging `hZero` of `TopAssembly.bucket_four_branch_fs_mix_le` over any `oa : ProbComp α`). -/
theorem redFSAuthMultiBucketAtomic_inactive_fsAeadAuthMixtureCompBound_eq_zero
    {α : Type} (oa : ProbComp α)
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : α → Party → IdentityKey) (lam : α → Pt)
    (hℓ : ℓ < 10 ^ 6) (hinj : Function.Injective encT)
    (idx q qep qR B0 : ℕ) (gMain : Bool) (tL : Option ℕ) (par : Bool)
    (A : α → OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (hq : ∀ o, CryptoGames.SM.MakesAtMostQueries (A o) q)
    (hinact : idx ≥ ((qep + 2) - healEpoch tL) * (q + 1) ∨
      ¬(decide (idx % (q + 1) = 0) = gMain ∧
        decide (Party.senderOf (healEpoch tL + idx / (q + 1)) == .A) = par)) :
    CryptoVerification.E2E.fsAeadAuthMixtureCompBound C protoSignalCodec ℓ oa qR
      (fun o => fsCostedRedsInst C protoSignalCodec ℓ encT (idOf o) qR)
      (fun stage la o =>
        (redFSAuthMultiBucketAtomic ℓ Pt C Dh encPt encT (idOf o) (lam o) stage la idx qep qR B0
          (q + 1) gMain tL par).eval (fun _ => A o) ()) = 0 :=
  fsAeadAuthMixtureCompBound_inst_eq_zero_of_zero_queries C ℓ encT oa idOf qR hℓ hinj _
    fun stage la o =>
      redFSAuthMultiBucketAtomic_inactive_makesAtMostQueries_zero ℓ Pt C Dh encPt encT (idOf o)
        (lam o) stage la idx q qep qR B0 gMain tL par (A o) (hq o) hinact

theorem redFSAuthMultiBucketShallow_decQueries
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (L B0 qep : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool) (idx q : ℕ)
    (A : OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    ((redFSAuthMultiBucketShallow ℓ Pt C Dh encPt encT idOf lam L B0 qep gMain la tL par).eval
      (fun _ => A) ()).IsQueryBoundP
      (fun t => (match t with
        | .inl _ => false
        | .inr ⟨s, qv⟩ => decide (s = idx) &&
            CryptoGames.FSAEAD.isDecQuery (SS := RatchetSenderState (BitVec 256))
              (RS := RatchetReceiverState (BitVec 256) (BitVec 256)) (.inr qv)) = true) q := by
  rw [redFSAuthMultiBucketShallow_eq_twoMode]
  exact BucketFSAuthTwoMode.redFSAuthMultiBucketShallow_decQueries
    ℓ Pt C Dh encPt encT idOf lam L B0 qep gMain la tL par idx q A hq

theorem redFSAuthMultiBucketAtomic_encAtomicShort_and_eqPub
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (stage la : Bool) (idx q qep qR B0 : ℕ) (gMain : Bool) (tL : Option ℕ) (par : Bool)
    (A : OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (hsh : CryptoGames.LibsignalSM.Proofs.SessionShort.FSAEADRed.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    CryptoGames.FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
      ((redFSAuthMultiBucketAtomic ℓ Pt C Dh encPt encT idOf lam stage la idx qep qR B0 (q + 1)
          gMain tL par).eval (fun _ => A) ()) ∧
    CryptoGames.FSAEAD.EqualPubChallenges
      ((redFSAuthMultiBucketAtomic ℓ Pt C Dh encPt encT idOf lam stage la idx qep qR B0 (q + 1)
          gMain tL par).eval (fun _ => A) ()) := by
  let R_sh := redFSAuthMultiBucketShallow ℓ Pt C Dh encPt encT idOf lam (q + 1) B0 qep gMain la tL par
  have hBad := redFSAuthMultiBucketShallow_badTrOrCh_aux ℓ Pt C Dh encPt encT idOf lam
    q B0 qep gMain la tL par A hsh
  refine ⟨?_, ?_⟩
  · refine compileFsMultiAtomic_encMsgsOk ℓ Pt C Dh encPt encT idOf lam stage la idx qep qR B0 R_sh A
      (fun m => atomicShortPubB m.1) ?_
    refine BucketFSAuthShort.isQueryBoundP_of_imp (fun t ht => ?_) hBad
    rcases t with _ | ⟨s', qv⟩
    · simp at ht
    · rcases qv with ((((⟨_, m⟩ | ⟨_, m₀, m₁⟩) | _) | _) | _) | _ <;>
        · simp [BucketFSAuthShort.badTrOrCh, CryptoGames.FSAEAD.encBadMsg] at ht ⊢
          try exact ht
          try exact ht.2
  · have hE0 := compileFsMultiAtomic_isQueryBoundP ℓ Pt C Dh encPt encT idOf lam stage la idx qep qR B0
      R_sh A
      (fun qv => CryptoGames.FSAEAD.unequalPubChall
        (SS := RatchetSenderState (BitVec 256))
        (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
        (AD := Header Pt) (Pub := LibsignalMsgPublicPart) (M := Plain ℓ)
        (C := ℕ × LibsignalCiphertextWithSalt32) (.inr qv))
      0
      (BucketFSAuthShort.isQueryBoundP_of_imp (fun t ht => by
        rcases t with _ | ⟨s', qv⟩
        · simp at ht
        · rcases qv with ((((⟨_, m⟩ | ⟨_, m₀, m₁⟩) | _) | _) | _) | _ <;>
            simp [BucketFSAuthShort.badTrOrCh, CryptoGames.FSAEAD.unequalPubChall] at ht ⊢)
        hBad)
    refine BucketFSAuthShort.isQueryBoundP_of_imp (fun t ht => ?_) hE0
    rcases t with _ | qv
    · simp [CryptoGames.FSAEAD.unequalPubChall] at ht
    · exact ht

theorem redFSAuthMultiBucketAtomic_decQueries
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (stage la : Bool) (idx q qep qR B0 : ℕ) (gMain : Bool) (tL : Option ℕ) (par : Bool)
    (A : OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    CryptoGames.FSAEAD.MakesAtMostDecQueries
      ((redFSAuthMultiBucketAtomic ℓ Pt C Dh encPt encT idOf lam stage la idx qep qR B0 (q + 1)
          gMain tL par).eval (fun _ => A) ()) q := by
  have hD0 := compileFsMultiAtomic_isQueryBoundP ℓ Pt C Dh encPt encT idOf lam stage la idx qep qR B0
    (redFSAuthMultiBucketShallow ℓ Pt C Dh encPt encT idOf lam (q + 1) B0 qep gMain la tL par) A
    (fun qv => CryptoGames.FSAEAD.isDecQuery
      (SS := RatchetSenderState (BitVec 256))
      (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
      (AD := Header Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
      (C := ℕ × LibsignalCiphertextWithSalt32) (.inr qv))
    q
    (BucketFSAuthShort.isQueryBoundP_of_imp (fun t ht => by
      rcases t with _ | ⟨s', qv⟩
      · simp at ht
      · rcases qv with ((((_ | _) | _) | _) | _) | _ <;>
          · simp [CryptoGames.FSAEAD.isDecQuery] at ht ⊢
            try exact ht)
      (redFSAuthMultiBucketShallow_decQueries ℓ Pt C Dh encPt encT idOf lam (q + 1) B0 qep
        gMain la tL par idx q A hq))
  refine BucketFSAuthShort.isQueryBoundP_of_imp (fun t ht => ?_) hD0
  rcases t with _ | qv
  · simp [CryptoGames.FSAEAD.isDecQuery] at ht
  · exact ht

theorem redFSAuthMultiBucketAtomic_oneADClass
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (stage la : Bool) (idx q qep qR B0 : ℕ) (gMain : Bool) (tL : Option ℕ) (par : Bool)
    (A : OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    CryptoGames.FSAEAD.AllQueriesInOneADClass (fun h : Header Pt => h.1)
      ((redFSAuthMultiBucketAtomic ℓ Pt C Dh encPt encT idOf lam stage la idx qep qR B0 (q + 1)
          gMain tL par).eval (fun _ => A) ()) := by
  let k₀ := healEpoch tL + idx / (q + 1)
  have hAt := compileFsMultiAtomic_isQueryBoundP ℓ Pt C Dh encPt encT idOf lam stage la idx qep qR B0
    (redFSAuthMultiBucketShallow ℓ Pt C Dh encPt encT idOf lam (q + 1) B0 qep gMain la tL par) A
    (fun qv => CryptoGames.FSAEAD.queryADOutsideClass
      (SS := RatchetSenderState (BitVec 256))
      (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
      (Msg := LibsignalMsgPublicPart × Plain ℓ)
      (C := ℕ × LibsignalCiphertextWithSalt32)
      (fun h : Header Pt => h.1) k₀ (.inr qv))
    0
    ((redFSAuthMultiBucketShallow_oneADClass_aux ℓ Pt C Dh encPt encT idOf lam q B0 qep
      gMain la tL par idx A hq).of_imp fun x hx => by
        rcases x with _ | ⟨_, _⟩ <;> exact hx)
  refine ⟨k₀, BucketFSAuthShort.isQueryBoundP_of_imp (fun t ht => ?_) hAt⟩
  rcases t with _ | qv
  · simp [CryptoGames.FSAEAD.queryADOutsideClass] at ht
  · exact ht

theorem redFSAuthMultiBucketAtomic_guardedFSInjectShort
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (hℓ : ℓ < 10 ^ 6)
    (stage la : Bool) (idx q qep qR B0 : ℕ) (gMain : Bool) (tL : Option ℕ) (par : Bool)
    (A : OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (hg : CryptoGames.LibsignalSM.Proofs.SessionShort.GuardedSMShort A) :
    GuardedFSInjectShort
      ((redFSAuthMultiBucketAtomic ℓ Pt C Dh encPt encT idOf lam stage la idx qep qR B0 (q + 1)
          gMain tL par).eval (fun _ => A) ()) := by
  let R_sh := redFSAuthMultiBucketShallow ℓ Pt C Dh encPt encT idOf lam (q + 1) B0 qep gMain la tL par
  have hG_sh := redFSAuthMultiBucketShallow_guardedShort_aux ℓ Pt C Dh encPt encT idOf lam
    hℓ q B0 qep gMain la tL par A hg
  exact compileFsMultiAtomic_guardedFSInjectShort ℓ Pt C Dh encPt encT idOf lam stage la idx qep qR B0
    R_sh A hG_sh

/-- Single-session `FsOk ℓ (2 * q) q` and `EncMsgsOk atomicShortPubB` for
`redFSAuthMultiBucketAtomic` (discharging `SessionCostedFig8.fig8RedsInst_fsOk_and_encAtomicShort`). -/
theorem redFSAuthMultiBucketAtomic_fsOk_and_encAtomicShort
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (hℓ : ℓ < 10 ^ 6)
    (stage la : Bool) (idx q qep qR B0 : ℕ) (gMain : Bool) (tL : Option ℕ) (par : Bool)
    (A : OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (hq : CryptoGames.SM.MakesAtMostQueries A q)
    (heq : CryptoGames.SM.EqualPubChalls (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1) A)
    (hsh : CryptoGames.LibsignalSM.Proofs.SessionShort.FSAEADRed.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A)
    (hg : CryptoGames.LibsignalSM.Proofs.SessionShort.GuardedSMShort A) :
    BucketFsOk ℓ (2 * q) q
      ((redFSAuthMultiBucketAtomic ℓ Pt C Dh encPt encT idOf lam stage la idx qep qR B0 (q + 1)
          gMain tL par).eval (fun _ => A) ()) ∧
    CryptoGames.FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
      ((redFSAuthMultiBucketAtomic ℓ Pt C Dh encPt encT idOf lam stage la idx qep qR B0 (q + 1)
          gMain tL par).eval (fun _ => A) ()) := by
  let _ := heq
  have ⟨hEncAt, hEqPub⟩ := redFSAuthMultiBucketAtomic_encAtomicShort_and_eqPub
    ℓ Pt C Dh encPt encT idOf lam stage la idx q qep qR B0 gMain tL par A hsh
  have hMakes := (redFSAuthMultiBucketAtomic_makesAtMostQueries ℓ Pt C Dh encPt encT idOf lam
    stage la idx q qep qR B0 gMain tL par A hq).mono (Nat.min_le_left _ _)
  have hDec := redFSAuthMultiBucketAtomic_decQueries
    ℓ Pt C Dh encPt encT idOf lam stage la idx q qep qR B0 gMain tL par A hq
  have hOneAD := redFSAuthMultiBucketAtomic_oneADClass
    ℓ Pt C Dh encPt encT idOf lam stage la idx q qep qR B0 gMain tL par A hq
  have hGuard := redFSAuthMultiBucketAtomic_guardedFSInjectShort
    ℓ Pt C Dh encPt encT idOf lam hℓ stage la idx q qep qR B0 gMain tL par A hg
  exact ⟨⟨hMakes, hDec, hEqPub, hOneAD,
    BucketFSAuthShort.encMsgsOk_shortB_of_atomicShortPubB hEncAt, hGuard⟩, hEncAt⟩

end BucketMultiFs

end

end Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeBase
