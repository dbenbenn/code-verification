/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.SM.DeliverForge -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperCKA -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperBucketPRNG -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.DFProgBoundsBase -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.Fig8SourceCosts
import Computational.Proofs.ReductionDsl.Fig8ExcessCosts
public import Computational.Proofs.SessionCostedFig8.ProgSizeBounds -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.Fig8WeightedParts
import Computational.Proofs.GameHop.ReductionDsl.CostUB
import Computational.Proofs.ReductionDsl.Notation
import ProofLib.BV.WidthNorm
import Computational.Proofs.ReductionDsl.AtomicTablesHonest
import Computational.Proofs.ReductionDsl.FSAEAD.SaltWire
import Computational.Proofs.ReductionDsl.FsAtomicBoundsBase
import Computational.Proofs.ReductionDsl.LibsignalBoundDDHChain
import Computational.Proofs.ReductionDsl.PubRed

/-!
# Weighted Program Bounds and `GRedBounded` Wrappers for `(tL, par)`-Bucket `DeliverForge` Reductions

Establishes weighted step-cost, excess-cost, and description-size bounds together with compiled
atomic `CostedReduction` programs and `GRedBounded` certificates (plus `0`-query out-of-range
fallbacks) for the Stage-2 `(tL, par)`-bucket CKA and ascending `t`-hybrid PRF-PRNG reductions
`redCKAAuthDF{,Paper}BucketProg` and `redPRNGAuthDF{,Paper}BucketHybridProg`.-/

namespace Computational.Proofs.SessionCostedFig8.DFProgBucketBounds

public section

set_option autoImplicit false

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Ops Iface Expr Comp CostedReduction bits reductionSizeBudget
  bits_le_succ atomicFig8Ops fig8SmCodecDF ckaTargetIface prngTargetIface)
open Computational.Proofs.GameHop.ReductionDsl.CostUB (exprCostUB exprCost_le_costUB compCostUB compCost_le_costUB)
open scoped Computational.Proofs.ReductionDsl.Notation
open _root_.CryptoGames (Party)
open _root_.CryptoGames.LibsignalSession (maxForwardJumps)
open _root_.CryptoGames.SM.Construction (Header healEpoch)
open _root_.CryptoVerification.LibsignalSession (ratchetCostBudget GRedBounded)
open Computational.Proofs.ReductionDsl.PureAuxMacroLift (exprCostW compCostW)
open Computational.Proofs.ReductionDsl.Fig8SourceCosts (HooksCostBounded bits_succ_le
  bits_le_bits_qep_add cInTransitE_cost_le cCompContainsE_cost_le vRecvC_cost_le
  commitEC_cost_le esG_cost esH_cost esSetH_cost esSetG_cost esAbort_cost pGet_cost cGsSt_cost
  cGsEpoch_cost cGsSetWin_cost cRecPos_cost otherE_cost isSomeE_cost
  v0_cost v1_cost v2_cost v3_cost v4_cost v5_cost v6_cost hooksCKAC_costBounded initCKAEStateC_cost_le)
open Computational.Proofs.ReductionDsl.Fig8ExcessCosts (ckaOpC ckaSampC ckaQueryC prngQueryC fsQueryC
  exprExcessUB compExcessUB compCostW_le_cost_add_excessUB HooksExcessBounded
  cInTransitE_excessUB vSendC_excessUB_le vRecvC_excessUB_le commitEC_excessUB_le
  hooksCKAC_excessBounded initCKAEStateC_excessUB_le optNatLit_excessUB
  exprExcessUB_v0 exprExcessUB_v1 exprExcessUB_v2 exprExcessUB_v3 exprExcessUB_v4
  exprExcessUB_v5 exprExcessUB_v6 exprExcessUB_v7 exprExcessUB_var
  exprExcessUB_unit exprExcessUB_bool exprExcessUB_nat exprExcessUB_none exprExcessUB_nil
  exprExcessUB_add exprExcessUB_sub exprExcessUB_modK exprExcessUB_lt exprExcessUB_eqN
  exprExcessUB_not exprExcessUB_and exprExcessUB_ite exprExcessUB_pair exprExcessUB_fst
  exprExcessUB_snd exprExcessUB_inl exprExcessUB_inr exprExcessUB_some exprExcessUB_cons
  exprExcessUB_caseOpt exprExcessUB_caseSum exprExcessUB_letE exprExcessUB_op
  exprExcessUB_anyB exprExcessUB_foldrB exprExcessUB_tconst exprExcessUB_tget exprExcessUB_tset
  compExcessUB_ret compExcessUB_bind compExcessUB_ite compExcessUB_caseOpt compExcessUB_caseSum
  compExcessUB_sample compExcessUB_query)
open Computational.Proofs.ReductionDsl.Fig8WeightedParts (fig8AtomicStepBound compCostW_le_of_parts
  bits_le_add_one)
open Computational.Proofs.SessionCostedFig8.ProgSizeBounds (HooksSizeBounded
  bits_B0_le_ratchetCostBudget bits_four bits_le_ratchetCostBudget_of_le_linear bits_one
  bits_qep_le_ratchetCostBudget bits_three bits_two bits_zero cInTransitE_sizeW_le
  vSendC_sizeW_le vRecvC_sizeW_le commitEC_sizeW_le compSizeW_bind compSizeW_caseOpt
  compSizeW_caseSum compSizeW_ite compSizeW_query compSizeW_ret compSizeW_sample exprSizeW_add
  exprSizeW_and exprSizeW_anyB
  exprSizeW_bool exprSizeW_caseOpt exprSizeW_caseSum exprSizeW_cons exprSizeW_eqN
  exprSizeW_findB exprSizeW_foldrB exprSizeW_fst exprSizeW_inl exprSizeW_inr exprSizeW_ite
  exprSizeW_letE exprSizeW_lt exprSizeW_modK exprSizeW_nat exprSizeW_nil exprSizeW_none
  exprSizeW_not exprSizeW_op exprSizeW_pair exprSizeW_snd exprSizeW_some exprSizeW_sub
  exprSizeW_tconst exprSizeW_tget exprSizeW_tset exprSizeW_unit exprSizeW_v0 exprSizeW_v1
  exprSizeW_v2 exprSizeW_v3 exprSizeW_v4 exprSizeW_v5 exprSizeW_v6 exprSizeW_v7 exprSizeW_var
  hooksCKAC_sizeBounded initCKAEStateC_sizeW_le optNatLit_sizeW size_le_ratchetSizeBudget)

/-! ## 1. Dummy `0`-Query `SM.specDF` → `fsaeadHeaderIface` Fallback (`[B4]` / `[B7]`) -/

section DummyFsStage2

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

@[expose] def dummyFsDFShallowProg (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt) :
    CostedReduction (Bundles.fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam 0)
      (CryptoGames.PRFPRNG.fsaeadHeaderAdIface (BitVec 256)
        (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt (BitVec 256)
        (BitVec 256) (BitVec 256) (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (CryptoGames.SM.specDF (CryptoGames.Ratchet.LibsignalSim.Fig8St Pt)
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (BitVec 256) (CryptoGames.Ratchet.LibsignalSim.Fig8C Pt))
      (CryptoGames.PRFPRNG.prngSMCodecDF (BitVec 256)
        (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt (BitVec 256)
        (BitVec 256) (BitVec 256) (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32))
      .unit .unit .bool .bool where
  σ := .unit
  init := .ret (.pair .unit .unit)
  handle :=
    .caseSum .v1
      (.caseSum .v0
        (.caseSum .v0
          (.caseSum .v0
            (.caseSum .v0
              (.ret (.pair (.inl (.inl (.inl (.inl (.inl .none))))) .unit))
              (.ret (.pair (.inl (.inl (.inl (.inl (.inr .none))))) .unit)))
            (.ret (.pair (.inl (.inl (.inl (.inr .none)))) .unit)))
          (.ret (.pair (.inl (.inl (.inr .none))) .unit)))
        (.ret (.pair (.inl (.inr .none)) .unit)))
      (.ret (.pair (.inr .none) .unit))
  finish := .ret (.bool false)

@[expose] def dummyFsStage2AtomicProg (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt) :=
  Bundles.compileFsDFAtomic ℓ Pt C Dh encPt encT idOf lam 0
    (dummyFsDFShallowProg Dh encPt C ℓ encT idOf lam)

theorem dummyFsStage2AtomicProg_gRedBounded (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt)
    (qep q qOut : ℕ) :
    GRedBounded (dummyFsStage2AtomicProg Dh encPt C ℓ encT idOf lam)
      (fun _ => 1) (fun _ => 0) q qOut (ratchetCostBudget q qep) := by
  dsimp only [dummyFsStage2AtomicProg]
  refine DFProgBoundsBase.compileFsDFAtomic_gRedBounded ℓ Pt C Dh encPt encT idOf lam 0
    (dummyFsDFShallowProg Dh encPt C ℓ encT idOf lam) q qep qOut ⟨?_, ?_⟩ ?_ ?_
  · simp only [dummyFsDFShallowProg, fig8AtomicStepBound, compCostW, exprCostW, Expr.v0, Expr.v1]
    omega
  · simp only [dummyFsDFShallowProg, fig8AtomicStepBound, compCostW, exprCostW, Expr.v0, Expr.v1]
    omega
  · simp only [dummyFsDFShallowProg, compSizeW_ret, compSizeW_caseSum, exprSizeW_pair,
      exprSizeW_unit, exprSizeW_bool, exprSizeW_inl, exprSizeW_inr, exprSizeW_none,
      exprSizeW_v0, exprSizeW_v1, reductionSizeBudget]
    omega
  · simp [CostedReduction.totalQueries, dummyFsDFShallowProg, Comp.queries]

@[expose] def dummyCkaDFShallowProg (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt) :
    CostedReduction (Bundles.fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam 0)
      (CryptoGames.CKA.ckaIface (BitVec 256)
        (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt (BitVec 256)
        (BitVec 256) (BitVec 256) (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (CryptoGames.SM.specDF (CryptoGames.Ratchet.LibsignalSim.Fig8St Pt)
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (BitVec 256) (CryptoGames.Ratchet.LibsignalSim.Fig8C Pt))
      (CryptoGames.CKA.ckaSMCodecDF (BitVec 256)
        (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt (BitVec 256)
        (BitVec 256) (BitVec 256) (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32))
      .unit .unit .bool .bool where
  σ := .unit
  init := .ret (.pair .unit .unit)
  handle :=
    .caseSum .v1
      (.caseSum .v0
        (.caseSum .v0
          (.caseSum .v0
            (.caseSum .v0
              (.ret (.pair (.inl (.inl (.inl (.inl (.inl .none))))) .unit))
              (.ret (.pair (.inl (.inl (.inl (.inl (.inr .none))))) .unit)))
            (.ret (.pair (.inl (.inl (.inl (.inr .none)))) .unit)))
          (.ret (.pair (.inl (.inl (.inr .none))) .unit)))
        (.ret (.pair (.inl (.inr .none)) .unit)))
      (.ret (.pair (.inr .none) .unit))
  finish := .ret (.bool false)

@[expose] def dummyCkaStage2AtomicProg (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt) :=
  Bundles.compileCkaDFAtomic ℓ Pt C Dh encPt encT idOf lam 0
    (dummyCkaDFShallowProg Dh encPt C ℓ encT idOf lam)

theorem dummyCkaStage2AtomicProg_gRedBounded (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt)
    (qep q qOut : ℕ) :
    GRedBounded (dummyCkaStage2AtomicProg Dh encPt C ℓ encT idOf lam)
      (fun _ => 1) (fun _ => 0) q qOut (ratchetCostBudget q qep) := by
  dsimp only [dummyCkaStage2AtomicProg]
  refine DFProgBoundsBase.compileCkaDFAtomic_gRedBounded ℓ Pt C Dh encPt encT idOf lam 0
    (dummyCkaDFShallowProg Dh encPt C ℓ encT idOf lam) q qep qOut ⟨?_, ?_⟩ ?_ ?_
  · simp only [dummyCkaDFShallowProg, fig8AtomicStepBound, compCostW, exprCostW, Expr.v0, Expr.v1]; omega
  · simp only [dummyCkaDFShallowProg, fig8AtomicStepBound, compCostW, exprCostW, Expr.v0, Expr.v1]; omega
  · simp only [dummyCkaDFShallowProg, compSizeW_ret, compSizeW_caseSum, exprSizeW_pair,
      exprSizeW_unit, exprSizeW_bool, exprSizeW_inl, exprSizeW_inr, exprSizeW_none,
      exprSizeW_v0, exprSizeW_v1, reductionSizeBudget]; omega
  · simp [CostedReduction.totalQueries, dummyCkaDFShallowProg, Comp.queries]

@[expose] def dummyPrngDFShallowProg (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt) :
    CostedReduction (Bundles.fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam 0)
      (CryptoGames.PRFPRNG.prngIface (BitVec 256)
        (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt (BitVec 256)
        (BitVec 256) (BitVec 256) (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (CryptoGames.SM.specDF (CryptoGames.Ratchet.LibsignalSim.Fig8St Pt)
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (BitVec 256) (CryptoGames.Ratchet.LibsignalSim.Fig8C Pt))
      (CryptoGames.PRFPRNG.prngSMCodecDF (BitVec 256)
        (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt (BitVec 256)
        (BitVec 256) (BitVec 256) (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32))
      .unit .unit .bool .bool where
  σ := .unit
  init := .ret (.pair .unit .unit)
  handle :=
    .caseSum .v1
      (.caseSum .v0
        (.caseSum .v0
          (.caseSum .v0
            (.caseSum .v0
              (.ret (.pair (.inl (.inl (.inl (.inl (.inl .none))))) .unit))
              (.ret (.pair (.inl (.inl (.inl (.inl (.inr .none))))) .unit)))
            (.ret (.pair (.inl (.inl (.inl (.inr .none)))) .unit)))
          (.ret (.pair (.inl (.inl (.inr .none))) .unit)))
        (.ret (.pair (.inl (.inr .none)) .unit)))
      (.ret (.pair (.inr .none) .unit))
  finish := .ret (.bool false)

@[expose] def dummyPrngStage2AtomicProg (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt) :=
  Bundles.compilePrngDFAtomic ℓ Pt C Dh encPt encT idOf lam 0
    (dummyPrngDFShallowProg Dh encPt C ℓ encT idOf lam)

theorem dummyPrngStage2AtomicProg_gRedBounded (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt)
    (qep q qOut : ℕ) :
    GRedBounded (dummyPrngStage2AtomicProg Dh encPt C ℓ encT idOf lam)
      (fun _ => 1) (fun _ => 0) q qOut (ratchetCostBudget q qep) := by
  dsimp only [dummyPrngStage2AtomicProg]
  refine DFProgBoundsBase.compilePrngDFAtomic_gRedBounded ℓ Pt C Dh encPt encT idOf lam 0
    (dummyPrngDFShallowProg Dh encPt C ℓ encT idOf lam) q qep qOut ⟨?_, ?_⟩ ?_ ?_
  · simp only [dummyPrngDFShallowProg, fig8AtomicStepBound, compCostW, exprCostW, Expr.v0, Expr.v1]; omega
  · simp only [dummyPrngDFShallowProg, fig8AtomicStepBound, compCostW, exprCostW, Expr.v0, Expr.v1]; omega
  · simp only [dummyPrngDFShallowProg, compSizeW_ret, compSizeW_caseSum, exprSizeW_pair,
      exprSizeW_unit, exprSizeW_bool, exprSizeW_inl, exprSizeW_inr, exprSizeW_none,
      exprSizeW_v0, exprSizeW_v1, reductionSizeBudget]; omega
  · simp [CostedReduction.totalQueries, dummyPrngDFShallowProg, Comp.queries]

end DummyFsStage2

/-! ## 2. Generic `ConfigEC` & Arbitrary-`Δ ≤ 4` Engine Helpers -/

section GenericEngineBounds

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}
  {ckaInitA : KC → Γ} {ckaInitB : KC → Γ}
  {ckaSend : Γ → CCoins → Γ × T × I} {ckaReceive : Γ → T → Γ × I}
  {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS} {fsInitReceiver : K → RS}
  {fsSend : SS → Header T → M → SS × E} {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
  {lam : I} {defaultE : E}
  {sampKR : ProbComp KR} {sampKC : ProbComp KC} {sampCCoins : ProbComp CCoins}
  {sampI : ProbComp I} {sampK : ProbComp K}

local notation "S_cka" => CryptoGames.CKA.ckaSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "OO_cka" =>
  CryptoGames.CKA.ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE
local notation "ckaHdrCtT" => CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E

private theorem letE_cost_le_costUB {S : Sig} {O : Ops S} {Γ : List (Ty S)} {a b : Ty S}
    (x : Expr O Γ a) (body : Expr O (a :: Γ) b) :
    (Expr.letE x body).cost ≤ x.cost + exprCostUB body + 1 := by
  have h := exprCost_le_costUB body
  simp only [Expr.cost]; omega

private theorem cost_bind_ret_le_costUB {S : Sig} {O : Ops S} {ι : Type} {TSpec : OracleSpec ι}
    {I' : Iface S TSpec} {Γ' : List (Ty S)} {t u : Ty S}
    (e : Expr O Γ' t) (k : Comp O I' (t :: Γ') u) :
    (Comp.bind (.ret e) k).cost ≤ e.cost + compCostUB k + 2 := by
  have hk := compCost_le_costUB k; simp only [Comp.cost]; omega

private theorem ret_pair_letE_cost_le_costUB {S : Sig} {O : Ops S} {ι : Type} {TSpec : OracleSpec ι}
    {I' : Iface S TSpec} {Γ' : List (Ty S)} {t u v : Ty S}
    (e : Expr O Γ' t) (k : Expr O (t :: Γ') u) (r : Expr O Γ' v) :
    (Comp.ret (I := I') (.pair (.letE e k) r)).cost ≤ e.cost + r.cost + exprCostUB k + 3 := by
  have hk := exprCost_le_costUB k; simp only [Comp.cost, Expr.cost]; omega

private theorem hdrEqE_cost_le {Γ'} (c₁ c₂ : Expr OO_cka Γ' ckaHdrCtT) :
    (CryptoGames.SM.Engine.hdrEqE c₁ c₂).cost ≤ c₁.cost + c₂.cost + 40 := by
  have hmax11 : max 1 1 = 1 := rfl; have hmax14 : max 1 4 = 4 := rfl
  simp only [CryptoGames.SM.Engine.hdrEqE, CryptoGames.SM.Engine.optTEqE, CryptoGames.CKA.ckaOps,
    Expr.cost, v0_cost, v1_cost, hmax11, hmax14, Nat.reduceAdd]; omega

private theorem hdrEqE_excessUB (B0 : ℕ) {Γ'} (c₁ c₂ : Expr OO_cka Γ' ckaHdrCtT) :
    exprExcessUB (ckaOpC B0) (CryptoGames.SM.Engine.hdrEqE c₁ c₂) ≤
      exprExcessUB (ckaOpC B0) c₁ + exprExcessUB (ckaOpC B0) c₂ + 20 := by
  simp only [CryptoGames.SM.Engine.hdrEqE, CryptoGames.SM.Engine.optTEqE, ckaOpC,
    exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_bool, exprExcessUB_eqN, exprExcessUB_and,
    exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_caseOpt, exprExcessUB_letE,
    exprExcessUB_op, Nat.add_zero, Nat.zero_add]; omega

set_option linter.unusedSimpArgs false in
private theorem hdrEqE_sizeW_le (B0 : ℕ) {Γ'} (c₁ c₂ : Expr OO_cka Γ' ckaHdrCtT) :
    Bundles.exprSizeW (Bundles.ckaOpS B0) (CryptoGames.SM.Engine.hdrEqE c₁ c₂) ≤
      Bundles.exprSizeW (Bundles.ckaOpS B0) c₁ + Bundles.exprSizeW (Bundles.ckaOpS B0) c₂ + 400 := by
  simp only [CryptoGames.SM.Engine.hdrEqE, CryptoGames.SM.Engine.optTEqE, CryptoGames.CKA.ckaOps,
    Bundles.ckaOpS, exprSizeW_v0, exprSizeW_v1, exprSizeW_var, exprSizeW_bool, exprSizeW_eqN,
    exprSizeW_and, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_caseOpt, exprSizeW_letE,
    exprSizeW_op, Nat.reduceAdd]; omega

set_option linter.unusedSimpArgs false in
theorem cSafeInjE_any_cost_le {O' : Ops S_cka} {vpT : Ty S_cka} (Δ : ℕ) (hΔ : Δ ≤ 4) {Γ'}
    (s : Expr O' Γ' (CryptoGames.SM.Engine.cGsTy vpT)) :
    (CryptoGames.SM.Engine.cSafeInjE Δ s).cost ≤ s.cost + 80 := by
  have hc : Δ = 0 ∨ Δ = 1 ∨ Δ = 2 ∨ Δ = 3 ∨ Δ = 4 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl <;>
  · refine (letE_cost_le_costUB _ _).trans ?_
    simp only [CryptoGames.SM.healedByE, CryptoGames.SM.leN, CryptoGames.SM.minN,
      CryptoGames.SM.Engine.cGsTL, CryptoGames.SM.Engine.cGsEpoch,
      Expr.cost, Expr.v0, Expr.v1, dsl_cost, exprCostUB,
      bits_zero, bits_one, bits_two, bits_three, bits_four, Nat.reduceAdd]
    omega

set_option linter.unusedSimpArgs false in
theorem cEpMgmtE_any_cost_le {O' : Ops S_cka} {vpT : Ty S_cka} (Δ qep : ℕ) (hΔ : Δ ≤ 4) {Γ'}
    (s : Expr O' Γ' (CryptoGames.SM.Engine.cGsTy vpT)) (p bad : Expr O' Γ' .bool) :
    (CryptoGames.SM.Engine.cEpMgmtE Δ qep s p bad).cost ≤
      s.cost + p.cost + bad.cost + 5 * bits qep + 750 := by
  have hc : Δ = 0 ∨ Δ = 1 ∨ Δ = 2 ∨ Δ = 3 ∨ Δ = 4 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl <;>
  · refine (letE_cost_le_costUB _ _).trans ?_
    simp only [CryptoGames.SM.Engine.cSafeChE, CryptoGames.SM.Engine.cLeakE,
      CryptoGames.SM.Engine.cGsMk, CryptoGames.SM.sendsInE, CryptoGames.SM.healedByE,
      CryptoGames.SM.maxOptE, CryptoGames.SM.maxN, CryptoGames.SM.leN, CryptoGames.SM.pSet,
      CryptoGames.SM.pGet, CryptoGames.SM.Engine.cGsSt, CryptoGames.SM.Engine.cGsB,
      CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.cGsEpoch, CryptoGames.SM.Engine.cGsIdx,
      CryptoGames.SM.Engine.cGsTL, CryptoGames.SM.Engine.cGsTrans, CryptoGames.SM.Engine.cGsChall,
      CryptoGames.SM.Engine.cGsComp, CryptoGames.SM.Engine.cGsMaxAcc,
      CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs,
      Expr.cost, Expr.v0, Expr.v1, Expr.v2, dsl_cost, exprCostUB,
      bits_zero, bits_one, bits_two, bits_three, bits_four, Nat.reduceAdd]
    omega

set_option linter.unusedSimpArgs false in
theorem cRecordE_any_cost_le {O' : Ops S_cka} {vpT : Ty S_cka} (L Δ : ℕ) (hΔ : Δ ≤ 4) {Γ'}
    (s : Expr O' Γ' (CryptoGames.SM.Engine.cGsTy vpT)) (p : Expr O' Γ' .bool)
    (st' : Expr O' Γ' vpT) (r : Expr O' Γ' CryptoGames.SM.Engine.cRecTy)
    (isChall : Expr O' Γ' .bool) :
    (CryptoGames.SM.Engine.cRecordE L Δ s p st' r isChall).cost ≤
      s.cost + p.cost + st'.cost + r.cost + isChall.cost + 750 := by
  have hc : Δ = 0 ∨ Δ = 1 ∨ Δ = 2 ∨ Δ = 3 ∨ Δ = 4 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl <;>
  · refine (letE_cost_le_costUB _ _).trans ?_
    simp only [CryptoGames.SM.Engine.cSafeChE, CryptoGames.SM.Engine.cCompInsertE,
      CryptoGames.SM.Engine.cCompSetE, CryptoGames.SM.Engine.cGsMk, CryptoGames.SM.healedByE,
      CryptoGames.SM.leN, CryptoGames.SM.pSet, CryptoGames.SM.pGet,
      CryptoGames.SM.Engine.cRecPos, CryptoGames.SM.posSender, CryptoGames.SM.posEpoch,
      CryptoGames.SM.posIdx, CryptoGames.SM.Engine.cGsSt, CryptoGames.SM.Engine.cGsB,
      CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.cGsEpoch, CryptoGames.SM.Engine.cGsIdx,
      CryptoGames.SM.Engine.cGsTL, CryptoGames.SM.Engine.cGsTrans, CryptoGames.SM.Engine.cGsChall,
      CryptoGames.SM.Engine.cGsComp, CryptoGames.SM.Engine.cGsMaxAcc,
      CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs,
      Expr.cost, Expr.v0, Expr.v1, Expr.v2, dsl_cost, exprCostUB,
      bits_zero, bits_one, bits_two, bits_three, bits_four, Nat.reduceAdd]
    omega

set_option linter.unusedSimpArgs false in
theorem cTrivialE_any_cost_le {O' : Ops S_cka} {vpT : Ty S_cka} (L Δ : ℕ) (hΔ : Δ ≤ 4) {Γ'}
    (s : Expr O' Γ' (CryptoGames.SM.Engine.cGsTy vpT))
    (pos : Expr O' Γ' CryptoGames.SM.posTy) :
    (CryptoGames.SM.Engine.cTrivialE L Δ s pos).cost ≤ s.cost + pos.cost + 150 * L + 360 := by
  have hc : Δ = 0 ∨ Δ = 1 ∨ Δ = 2 ∨ Δ = 3 ∨ Δ = 4 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl <;>
  · refine (letE_cost_le_costUB _ _).trans ?_
    simp only [CryptoGames.SM.Engine.cCompContainsE, CryptoGames.SM.orE, CryptoGames.SM.healedByE,
      CryptoGames.SM.leN, CryptoGames.SM.Engine.cGsTrans, CryptoGames.SM.Engine.cGsTL,
      CryptoGames.SM.Engine.cGsComp, CryptoGames.SM.Engine.cRecPos, CryptoGames.SM.pGet,
      CryptoGames.SM.posEq, CryptoGames.SM.boolEq, CryptoGames.SM.posSender,
      CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx,
      Expr.cost, Expr.v0, Expr.v1, Expr.v2, dsl_cost, exprCostUB,
      bits_zero, bits_one, bits_two, bits_three, bits_four, Nat.reduceAdd]
    omega

set_option linter.unusedSimpArgs false in
theorem cCorrAllowedPaperE_cost_le {O' : Ops S_cka} {vpT : Ty S_cka} (L : ℕ) {Γ'}
    (s : Expr O' Γ' (CryptoGames.SM.Engine.cGsTy vpT)) (p : Expr O' Γ' .bool) :
    (CryptoGames.SM.Engine.cCorrAllowedPaperE L s p).cost ≤ s.cost + p.cost + 300 * L + 150 := by
  refine (letE_cost_le_costUB _ _).trans ?_
  simp only [CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.boolEq,
    CryptoGames.SM.posSender, CryptoGames.SM.otherE,
    Expr.cost, Expr.v0, Expr.v1, dsl_cost, exprCostUB, Nat.reduceAdd]
  omega

set_option linter.unusedSimpArgs false in
theorem cCorrAllowedE_cost_le {O' : Ops S_cka} {vpT : Ty S_cka} (L : ℕ) {Γ'}
    (s : Expr O' Γ' (CryptoGames.SM.Engine.cGsTy vpT)) (p : Expr O' Γ' .bool) :
    (CryptoGames.SM.Engine.cCorrAllowedE L s p).cost ≤ s.cost + p.cost + 300 * L + 150 := by
  refine (letE_cost_le_costUB _ _).trans ?_
  simp only [CryptoGames.SM.Engine.cCompContainsE, CryptoGames.SM.Engine.cGsChall,
    CryptoGames.SM.Engine.cGsTrans, CryptoGames.SM.Engine.cGsComp, CryptoGames.SM.Engine.cRecPos,
    CryptoGames.SM.pGet, CryptoGames.SM.posSender, CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx,
    CryptoGames.SM.boolEq, CryptoGames.SM.otherE,
    Expr.cost, Expr.v0, Expr.v1, Expr.v2, dsl_cost, exprCostUB, Nat.reduceAdd]
  omega

set_option linter.unusedSimpArgs false in
theorem cAfterCorrE_cost_le {O' : Ops S_cka} {vpT : Ty S_cka} (L : ℕ) {Γ'}
    (s : Expr O' Γ' (CryptoGames.SM.Engine.cGsTy vpT)) (p : Expr O' Γ' .bool) :
    (CryptoGames.SM.Engine.cAfterCorrE L s p).cost ≤ s.cost + p.cost + 5500 * L + 4000 := by
  refine (letE_cost_le_costUB _ _).trans ?_
  simp only [CryptoGames.SM.Engine.cGsMk, CryptoGames.SM.Engine.cLeakE,
    CryptoGames.SM.Engine.cCompInsertE, CryptoGames.SM.Engine.cCompSetE,
    CryptoGames.SM.pSet, CryptoGames.SM.pGet, CryptoGames.SM.maxOptE, CryptoGames.SM.maxN,
    CryptoGames.SM.leN, CryptoGames.SM.boolEq, CryptoGames.SM.otherE,
    CryptoGames.SM.Engine.cRecPos, CryptoGames.SM.posSender, CryptoGames.SM.posEpoch,
    CryptoGames.SM.posIdx, CryptoGames.SM.Engine.cGsSt, CryptoGames.SM.Engine.cGsB,
    CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.cGsEpoch, CryptoGames.SM.Engine.cGsIdx,
    CryptoGames.SM.Engine.cGsTL, CryptoGames.SM.Engine.cGsTrans, CryptoGames.SM.Engine.cGsChall,
    CryptoGames.SM.Engine.cGsComp, CryptoGames.SM.Engine.cGsMaxAcc,
    CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs,
    Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, dsl_cost, exprCostUB, Nat.reduceAdd]
  omega

set_option linter.unusedSimpArgs false in
theorem cAuthOKE_any_cost_le {O' : Ops S_cka} {vpT : Ty S_cka} (L Δ : ℕ) (hΔ : Δ ≤ 4) {Γ'}
    (tLStar : Expr O' Γ' (.opt .nat)) (tStar : Expr O' Γ' .nat)
    (s : Expr O' Γ' (CryptoGames.SM.Engine.cGsTy vpT)) :
    (CryptoGames.SM.Engine.cAuthOKE L Δ tLStar tStar s).cost ≤
      tLStar.cost + tStar.cost + s.cost + 100 * L + 250 := by
  have hc : Δ = 0 ∨ Δ = 1 ∨ Δ = 2 ∨ Δ = 3 ∨ Δ = 4 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl <;>
  · refine (letE_cost_le_costUB _ _).trans ?_
    simp only [CryptoGames.SM.Engine.cCanonE, CryptoGames.SM.validGuessE, CryptoGames.SM.healedByE,
      CryptoGames.SM.optNatEqE, CryptoGames.SM.ltOptE, CryptoGames.SM.leN, CryptoGames.SM.maxN,
      CryptoGames.SM.boolEq, CryptoGames.SM.receiverOfE,
      CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs,
      Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, dsl_cost, exprCostUB,
      bits_zero, bits_one, bits_two, bits_three, bits_four, Nat.reduceAdd]
    omega

set_option linter.unusedSimpArgs false in
theorem vSendC_any_cost_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (H : ℕ)
    (hhk : HooksCostBounded hk H)
    {Γ'} (h : Expr OO_cka Γ' hsT)
    (ctx : Expr OO_cka Γ'
      (CryptoGames.SM.Engine.cGsTy (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
    (p : Expr OO_cka Γ' .bool)
    (s : Expr OO_cka Γ' (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))
    (m : Expr OO_cka Γ' (.base .msg))
    (pair : Expr OO_cka Γ' (.opt (.prod (.base .msg) (.base .msg))))
    (r : Expr OO_cka Γ' (.opt (.base .ccoins))) :
    (CryptoGames.SM.Engine.vSendC hk h ctx p s m pair r).cost ≤
      2 * (h.cost + ctx.cost + p.cost + s.cost + m.cost + pair.cost + r.cost) + 2 * H + 900 := by
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let Γ0 : List (Ty S_cka) :=
    .prod hsT (.prod (CryptoGames.SM.Engine.cGsTy vpT) (.prod .bool (.prod vpT (.opt (.base .ccoins))))) ::
      .prod hsT (.prod (CryptoGames.SM.Engine.cGsTy vpT) (.prod .bool (.prod vpT (.prod (.base .msg)
        (.prod (.opt (.prod (.base .msg) (.base .msg))) (.opt (.base .ccoins))))))) :: Γ'
  let Γ1 : List (Ty S_cka) :=
    ssvT :: vpT :: .prod (.opt vpT) hsT ::
      .prod hsT (.prod (CryptoGames.SM.Engine.cGsTy vpT) (.prod .bool (.prod vpT (.prod (.base .msg)
        (.prod (.opt (.prod (.base .msg) (.base .msg))) (.opt (.base .ccoins))))))) :: Γ'
  have hss := hhk.startSend_le (Γ' := Γ0)
    (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))
    (.add (CryptoGames.SM.Engine.vpTcurNat (.fst (.snd (.snd (.snd .v0))))) (.nat 1))
    (CryptoGames.SM.Engine.vpΓ (.fst (.snd (.snd (.snd .v0)))))
    (CryptoGames.SM.Engine.vpRoot (.fst (.snd (.snd (.snd .v0)))))
    (.snd (.snd (.snd (.snd .v0))))
  have hfs := hhk.fsSend_le (Γ' := Γ1)
    (.snd .v2) (.fst (.snd .v3)) (.fst (.snd (.snd .v3)))
    (CryptoGames.SM.Engine.vpTcurNat .v1) .v0
    (.pair (CryptoGames.SM.Engine.vpTcurNat .v1) (CryptoGames.SM.Engine.vpTcur .v1))
    (.fst (.snd (.snd (.snd (.snd .v3)))))
    (.fst (.snd (.snd (.snd (.snd (.snd .v3))))))
  simp only [CryptoGames.SM.Engine.vpTcurNat, CryptoGames.SM.Engine.vpTcur,
    CryptoGames.SM.Engine.vpΓ, CryptoGames.SM.Engine.vpRoot,
    Expr.cost, dsl_cost, v0_cost, v1_cost, v2_cost, v3_cost, bits_one, Nat.reduceAdd] at hss hfs
  simp only [CryptoGames.SM.Engine.vSendC, CryptoGames.SM.Engine.vSendStep1C,
    CryptoGames.SM.sendsInE, CryptoGames.SM.Engine.vpMk, CryptoGames.SM.Engine.vpId,
    CryptoGames.SM.Engine.vpVS, CryptoGames.SM.Engine.vpVR, CryptoGames.SM.Engine.vpTcur,
    CryptoGames.SM.Engine.vpTcurNat, CryptoGames.SM.Engine.vpSetVS, CryptoGames.SM.Engine.vpΓ,
    CryptoGames.SM.Engine.vpRoot, CryptoGames.CKA.ckaOps, Comp.cost, Expr.cost, dsl_cost,
    v0_cost, v1_cost, v2_cost, v3_cost, v4_cost, bits_zero, bits_one, bits_two, Nat.reduceAdd]
  omega

set_option linter.unusedSimpArgs false in
theorem deliverEC_any_cost_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (H L maxSkip : ℕ)
    (cfg : CryptoGames.SM.Engine.ConfigEC OO_cka) (hhk : HooksCostBounded hk H)
    {Γ'} (es : Expr OO_cka Γ'
      (CryptoGames.SM.Engine.esTy (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ' (.prod .bool ckaHdrCtT)) :
    (CryptoGames.SM.Engine.deliverEC hk L maxSkip cfg es arg).cost ≤
      2 * (es.cost + arg.cost) + 3 * H + 800 * L + 2 * (maxSkip + 1) + 5500 := by
  have hms := bits_le_succ maxSkip
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let decT : Ty S_cka := .prod vpT (.prod .nat (.prod .nat (.base .msg)))
  let Γ0 : List (Ty S_cka) := .prod (CryptoGames.SM.Engine.esTy vpT hsT) (.prod .bool ckaHdrCtT) :: Γ'
  let Γ1 : List (Ty S_cka) := CryptoGames.SM.Engine.cRecTy :: Γ0
  let Γ2 : List (Ty S_cka) := .opt decT :: .prod (.opt (.opt decT)) hsT :: Γ1
  let Γ3 : List (Ty S_cka) := decT :: Γ2
  let Γ4 : List (Ty S_cka) :=
    CryptoGames.SM.Engine.cGsTy vpT :: .prod (.opt (CryptoGames.SM.Engine.cGsTy vpT)) (CryptoGames.SM.Engine.esTy vpT hsT) :: Γ3
  have hit := cInTransitE_cost_le (vpT := vpT) L (Γ' := Γ0)
    (CryptoGames.SM.Engine.esG (O' := OO_cka) (.fst .v0)) (CryptoGames.SM.otherE (.fst (.snd .v0))) (.snd (.snd .v0))
  have hvr := vRecvC_cost_le hk H hhk (Γ' := Γ1)
    (CryptoGames.SM.Engine.esH (.fst .v1)) (CryptoGames.SM.Engine.esG (.fst .v1)) (.fst (.snd .v1))
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v1))) (.fst (.snd .v1)))
    (.snd (.snd .v1)) (.some .v0)
  have hcm := commitEC_cost_le hk H L hhk (Γ' := Γ3)
    (CryptoGames.SM.Engine.esSetH (.fst .v4) (.snd .v2)) (CryptoGames.SM.Engine.esG (.fst .v4)) (.fst (.snd .v4))
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v4))) (.fst (.snd .v4)))
    (.fst .v0) (CryptoGames.SM.Engine.cRecPos .v3)
  have hmb3 : (CryptoGames.SM.Engine.cMustBeCorrectE (O' := OO_cka) (vpT := vpT) L maxSkip (Γ' := Γ2)
      (CryptoGames.SM.Engine.esG (.fst .v3)) (.fst (.snd .v3)) .v2).cost ≤ bits maxSkip + 300 := by
    refine (exprCost_le_costUB _).trans ?_
    simp only [CryptoGames.SM.Engine.cMustBeCorrectE, CryptoGames.SM.Engine.cCompContainsE,
      CryptoGames.SM.Engine.cGsMaxAcc, CryptoGames.SM.Engine.cGsComp, CryptoGames.SM.Engine.cRecPos,
      CryptoGames.SM.Engine.esG, CryptoGames.SM.leN, CryptoGames.SM.maxAccGet, CryptoGames.SM.pGet,
      CryptoGames.SM.posSender, CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx,
      Expr.v0, Expr.v1, Expr.v2, Expr.v3, dsl_cost, exprCostUB, bits_one, Nat.reduceAdd]
    omega
  have hmb6 : (CryptoGames.SM.Engine.cMustBeCorrectE (O' := OO_cka) (vpT := vpT) L maxSkip (Γ' := Γ4)
      (CryptoGames.SM.Engine.esG (.fst .v6)) (.fst (.snd .v6)) .v5).cost ≤ bits maxSkip + 300 := by
    refine (exprCost_le_costUB _).trans ?_
    simp only [CryptoGames.SM.Engine.cMustBeCorrectE, CryptoGames.SM.Engine.cCompContainsE,
      CryptoGames.SM.Engine.cGsMaxAcc, CryptoGames.SM.Engine.cGsComp, CryptoGames.SM.Engine.cRecPos,
      CryptoGames.SM.Engine.esG, CryptoGames.SM.leN, CryptoGames.SM.maxAccGet, CryptoGames.SM.pGet,
      CryptoGames.SM.posSender, CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx,
      Expr.v0, Expr.v1, Expr.v5, Expr.v6, dsl_cost, exprCostUB, bits_one, Nat.reduceAdd]
    omega
  have hcc6 : (CryptoGames.SM.Engine.cChallContainsE (O' := OO_cka) (vpT := vpT) L (Γ' := Γ4)
      (CryptoGames.SM.Engine.esG (.fst .v6)) (CryptoGames.SM.Engine.cRecPos .v5)).cost ≤ 40 * L + 50 := by
    refine (exprCost_le_costUB _).trans ?_
    simp only [CryptoGames.SM.Engine.cChallContainsE, CryptoGames.SM.Engine.cGsChall,
      CryptoGames.SM.Engine.cRecPos, CryptoGames.SM.Engine.esG,
      CryptoGames.SM.posEq, CryptoGames.SM.boolEq, CryptoGames.SM.posSender,
      CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx,
      Expr.v0, Expr.v1, Expr.v5, Expr.v6, dsl_cost, exprCostUB, bits_one, Nat.reduceAdd]
    omega
  simp only [esG_cost, esH_cost, esSetH_cost, pGet_cost, cGsSt_cost, cRecPos_cost, otherE_cost,
    Expr.cost, dsl_cost, v0_cost, v1_cost, v2_cost, v3_cost, v4_cost, v5_cost, v6_cost,
    Nat.reduceAdd] at hit hvr hcm
  simp only [CryptoGames.SM.Engine.deliverEC, CryptoGames.SM.orE, CryptoGames.SM.Engine.cGsWin,
    CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.cRecMsg, CryptoGames.SM.posEpoch,
    CryptoGames.SM.posIdx, cRecPos_cost, esG_cost, esH_cost, esAbort_cost, esSetG_cost,
    cGsSetWin_cost, CryptoGames.CKA.ckaOps, Comp.cost, Expr.cost, dsl_cost,
    v0_cost, v1_cost, v2_cost, v3_cost, v5_cost, Nat.reduceAdd]
  omega

set_option linter.unusedSimpArgs false in
theorem deliverEC_any_excessUB_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sC : I'.smp.Samp → ℕ} {qC : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (Ho Hs Hr L maxSkip : ℕ)
    (cfg : CryptoGames.SM.Engine.ConfigEC OO_cka)
    (hhk : HooksExcessBounded B0 sC qC hk Ho Hs Hr)
    {Γ'} (es : Expr OO_cka Γ'
      (CryptoGames.SM.Engine.esTy (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ' (.prod .bool ckaHdrCtT)) :
    compExcessUB (ckaOpC B0) sC qC (CryptoGames.SM.Engine.deliverEC hk L maxSkip cfg es arg) ≤
      6 * (exprExcessUB (ckaOpC B0) es + exprExcessUB (ckaOpC B0) arg) + 2 * Ho + Hr + 150 * L + 32000 := by
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let decT : Ty S_cka := .prod vpT (.prod .nat (.prod .nat (.base .msg)))
  let Γ_dl0 : List (Ty S_cka) := .prod (CryptoGames.SM.Engine.esTy vpT hsT) (.prod .bool ckaHdrCtT) :: Γ'
  have hit := cInTransitE_excessUB (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (vpT := vpT) B0 L (Γ' := Γ_dl0) (CryptoGames.SM.Engine.esG (.fst .v0)) (CryptoGames.SM.otherE (.fst (.snd .v0))) (.snd (.snd .v0))
  have hvr := vRecvC_excessUB_le hk Ho Hs Hr hhk (Γ' := CryptoGames.SM.Engine.cRecTy :: Γ_dl0) (CryptoGames.SM.Engine.esH (.fst .v1)) (CryptoGames.SM.Engine.esG (.fst .v1)) (.fst (.snd .v1)) (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v1))) (.fst (.snd .v1))) (.snd (.snd .v1)) (.some .v0)
  have hcm := commitEC_excessUB_le hk Ho Hs Hr L hhk (Γ' := decT :: .opt decT :: .prod (.opt (.opt decT)) hsT :: CryptoGames.SM.Engine.cRecTy :: Γ_dl0) (CryptoGames.SM.Engine.esSetH (.fst .v4) (.snd .v2)) (CryptoGames.SM.Engine.esG (.fst .v4)) (.fst (.snd .v4)) (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v4))) (.fst (.snd .v4))) (.fst .v0) (CryptoGames.SM.Engine.cRecPos .v3)
  simp only [CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.esSetH, CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.cGsSt, CryptoGames.SM.Engine.cRecPos, CryptoGames.SM.pGet, CryptoGames.SM.otherE, exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4, exprExcessUB_not, exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_some, exprExcessUB_letE, Nat.add_zero, Nat.zero_add, Nat.mul_zero] at hit hvr hcm
  simp only [CryptoGames.SM.Engine.deliverEC, CryptoGames.SM.Engine.cCompContainsE, CryptoGames.SM.Engine.cChallContainsE, CryptoGames.SM.Engine.cMustBeCorrectE, CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.esSetG, CryptoGames.SM.Engine.esSetH, CryptoGames.SM.Engine.cGsMk, CryptoGames.SM.Engine.cGsSetWin, CryptoGames.SM.Engine.cGsSt, CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.cGsEpoch, CryptoGames.SM.Engine.cGsIdx, CryptoGames.SM.Engine.cGsTL, CryptoGames.SM.Engine.cGsTrans, CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.Engine.cGsComp, CryptoGames.SM.Engine.cGsMaxAcc, CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs, CryptoGames.SM.Engine.cRecPos, CryptoGames.SM.Engine.cRecMsg, CryptoGames.SM.pGet, CryptoGames.SM.orE, CryptoGames.SM.otherE, CryptoGames.SM.leN, CryptoGames.SM.maxAccGet, CryptoGames.SM.posEq, CryptoGames.SM.boolEq, CryptoGames.SM.posSender, CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx, ckaOpC, exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4, exprExcessUB_v5, exprExcessUB_v6, exprExcessUB_v7, exprExcessUB_var, exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none, exprExcessUB_add, exprExcessUB_lt, exprExcessUB_eqN, exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_inl, exprExcessUB_inr, exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_letE, exprExcessUB_op, exprExcessUB_anyB, exprExcessUB_tget, compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt, Nat.add_zero, Nat.zero_add, Nat.mul_zero]; omega

set_option linter.unusedSimpArgs false in
theorem deliverEC_any_sizeW_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sS : I'.smp.Samp → ℕ} {qS : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (Ho Hs Hr L maxSkip : ℕ) (cfg : CryptoGames.SM.Engine.ConfigEC OO_cka)
    (hhk : HooksSizeBounded B0 sS qS hk Ho Hs Hr)
    {Γ'} (es : Expr OO_cka Γ'
      (CryptoGames.SM.Engine.esTy (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ' (.prod .bool ckaHdrCtT)) :
    Bundles.compSizeW (Bundles.ckaOpS B0) sS qS (CryptoGames.SM.Engine.deliverEC hk L maxSkip cfg es arg) ≤
      6 * (Bundles.exprSizeW (Bundles.ckaOpS B0) es + Bundles.exprSizeW (Bundles.ckaOpS B0) arg) + 2 * Ho + Hr + 9 * bits L + 5 * bits maxSkip + 6000 := by
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let decT : Ty S_cka := .prod vpT (.prod .nat (.prod .nat (.base .msg)))
  let Γ_dl0 : List (Ty S_cka) := .prod (CryptoGames.SM.Engine.esTy vpT hsT) (.prod .bool ckaHdrCtT) :: Γ'
  have hit := cInTransitE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (vpT := vpT) B0 L (Γ' := Γ_dl0) (CryptoGames.SM.Engine.esG (.fst .v0)) (CryptoGames.SM.otherE (.fst (.snd .v0))) (.snd (.snd .v0))
  have hvr := vRecvC_sizeW_le hk Ho Hs Hr hhk (Γ' := CryptoGames.SM.Engine.cRecTy :: Γ_dl0) (CryptoGames.SM.Engine.esH (.fst .v1)) (CryptoGames.SM.Engine.esG (.fst .v1)) (.fst (.snd .v1)) (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v1))) (.fst (.snd .v1))) (.snd (.snd .v1)) (.some .v0)
  have hcm := commitEC_sizeW_le hk Ho Hs Hr L hhk (Γ' := decT :: .opt decT :: .prod (.opt (.opt decT)) hsT :: CryptoGames.SM.Engine.cRecTy :: Γ_dl0) (CryptoGames.SM.Engine.esSetH (.fst .v4) (.snd .v2)) (CryptoGames.SM.Engine.esG (.fst .v4)) (.fst (.snd .v4)) (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v4))) (.fst (.snd .v4))) (.fst .v0) (CryptoGames.SM.Engine.cRecPos .v3)
  simp only [CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.esSetH, CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.cGsSt, CryptoGames.SM.Engine.cRecPos, CryptoGames.SM.pGet, CryptoGames.SM.otherE, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4, exprSizeW_var, exprSizeW_not, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_some, exprSizeW_letE, Nat.reduceAdd] at hit hvr hcm
  simp only [CryptoGames.SM.Engine.deliverEC, CryptoGames.SM.Engine.cCompContainsE, CryptoGames.SM.Engine.cChallContainsE, CryptoGames.SM.Engine.cMustBeCorrectE, CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.esSetG, CryptoGames.SM.Engine.esSetH, CryptoGames.SM.Engine.cGsMk, CryptoGames.SM.Engine.cGsSetWin, CryptoGames.SM.Engine.cGsSt, CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.cGsEpoch, CryptoGames.SM.Engine.cGsIdx, CryptoGames.SM.Engine.cGsTL, CryptoGames.SM.Engine.cGsTrans, CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.Engine.cGsComp, CryptoGames.SM.Engine.cGsMaxAcc, CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs, CryptoGames.SM.Engine.cRecPos, CryptoGames.SM.Engine.cRecMsg, CryptoGames.SM.pGet, CryptoGames.SM.orE, CryptoGames.SM.otherE, CryptoGames.SM.leN, CryptoGames.SM.maxAccGet, CryptoGames.SM.posEq, CryptoGames.SM.boolEq, CryptoGames.SM.posSender, CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx, Bundles.ckaOpS, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4, exprSizeW_v5, exprSizeW_v6, exprSizeW_v7, exprSizeW_var, exprSizeW_unit, exprSizeW_bool, exprSizeW_nat, exprSizeW_none, exprSizeW_nil, exprSizeW_add, exprSizeW_sub, exprSizeW_modK, exprSizeW_lt, exprSizeW_eqN, exprSizeW_not, exprSizeW_and, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_inl, exprSizeW_inr, exprSizeW_some, exprSizeW_caseOpt, exprSizeW_caseSum, exprSizeW_letE, exprSizeW_op, exprSizeW_cons, exprSizeW_findB, exprSizeW_anyB, exprSizeW_foldrB, exprSizeW_tconst, exprSizeW_tget, exprSizeW_tset, compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt, compSizeW_caseSum, bits_zero, bits_one, bits_two, bits_three, bits_four, Nat.reduceAdd]; omega

set_option linter.unusedSimpArgs false in
theorem injectEC_anyCfg_cost_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (H L Δ qep C_inj : ℕ)
    (hΔ : Δ ≤ 4) (cfg : CryptoGames.SM.Engine.ConfigEC OO_cka)
    (hcfg : ∀ {Γ'} (e : Expr OO_cka Γ' .nat), (cfg.injectFullE e).cost ≤ 3 * e.cost + C_inj)
    (hhk : HooksCostBounded hk H)
    {Γ'} (es : Expr OO_cka Γ'
      (CryptoGames.SM.Engine.esTy (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ' (.prod .bool ckaHdrCtT)) :
    (CryptoGames.SM.Engine.injectEC hk L Δ qep cfg es arg).cost ≤
      2 * (es.cost + arg.cost) + 3 * H + 800 * L + bits qep + C_inj + 4700 := by
  have hqep1 := bits_succ_le qep
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let decT : Ty S_cka := .prod vpT (.prod .nat (.prod .nat (.base .msg)))
  let Γ0 : List (Ty S_cka) := .prod (CryptoGames.SM.Engine.esTy vpT hsT) (.prod .bool ckaHdrCtT) :: Γ'
  let Γ1 : List (Ty S_cka) := decT :: .opt decT :: .prod (.opt (.opt decT)) hsT :: Γ0
  have hit := cInTransitE_cost_le (vpT := vpT) L (Γ' := Γ0) (CryptoGames.SM.Engine.esG (O' := OO_cka) (.fst .v0)) (CryptoGames.SM.otherE (.fst (.snd .v0))) (.snd (.snd .v0))
  have hsi := cSafeInjE_any_cost_le (O' := OO_cka) (vpT := vpT) Δ hΔ (Γ' := Γ0) (CryptoGames.SM.Engine.esG (.fst .v0))
  have hvr := vRecvC_cost_le hk H hhk (Γ' := Γ0) (CryptoGames.SM.Engine.esH (.fst .v0)) (CryptoGames.SM.Engine.esG (.fst .v0)) (.fst (.snd .v0)) (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v0))) (.fst (.snd .v0))) (.snd (.snd .v0)) .none
  have htr := cTrivialE_any_cost_le (O' := OO_cka) (vpT := vpT) L Δ hΔ (Γ' := Γ1) (CryptoGames.SM.Engine.esG (.fst .v3)) (.pair (CryptoGames.SM.otherE (.fst (.snd .v3))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hcm := commitEC_cost_le hk H L hhk (Γ' := Γ1) (CryptoGames.SM.Engine.esSetH (.fst .v3) (.snd .v2)) (CryptoGames.SM.Engine.esG (.fst .v3)) (.fst (.snd .v3)) (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v3))) (.fst (.snd .v3))) (.fst .v0) (.pair (CryptoGames.SM.otherE (.fst (.snd .v3))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hij := hcfg (Γ' := Γ1) (.fst (.snd .v0))
  simp only [esG_cost, esH_cost, esSetH_cost, pGet_cost, cGsSt_cost, otherE_cost, Expr.cost, dsl_cost, v0_cost, v2_cost, v3_cost, Nat.reduceAdd] at hit hsi hvr htr hcm hij
  simp only [CryptoGames.SM.Engine.injectEC, CryptoGames.SM.orE, isSomeE_cost, CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.esMk, esG_cost, esH_cost, esAbort_cost, esSetH_cost, esSetG_cost, cGsSetWin_cost, Comp.cost, Expr.cost, dsl_cost, v0_cost, v1_cost, v2_cost, v3_cost, Nat.reduceAdd]; omega

set_option linter.unusedSimpArgs false in
theorem injectEC_anyCfg_excessUB_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sC : I'.smp.Samp → ℕ} {qC : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (Ho Hs Hr L Δ qep : ℕ)
    (cfg : CryptoGames.SM.Engine.ConfigEC OO_cka)
    (hcfg : ∀ {Γ'} (e : Expr OO_cka Γ' .nat), exprExcessUB (ckaOpC B0) (cfg.injectFullE e) ≤ 4 * exprExcessUB (ckaOpC B0) e)
    (hhk : HooksExcessBounded B0 sC qC hk Ho Hs Hr)
    {Γ'} (es : Expr OO_cka Γ'
      (CryptoGames.SM.Engine.esTy (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ' (.prod .bool ckaHdrCtT)) :
    compExcessUB (ckaOpC B0) sC qC (CryptoGames.SM.Engine.injectEC hk L Δ qep cfg es arg) ≤
      6 * (exprExcessUB (ckaOpC B0) es + exprExcessUB (ckaOpC B0) arg) + 2 * Ho + Hr + 150 * L + 500 := by
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let decT : Ty S_cka := .prod vpT (.prod .nat (.prod .nat (.base .msg)))
  let Γ_ij0 : List (Ty S_cka) := .prod (CryptoGames.SM.Engine.esTy vpT hsT) (.prod .bool ckaHdrCtT) :: Γ'
  have hit := cInTransitE_excessUB (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (vpT := vpT) B0 L (Γ' := Γ_ij0) (CryptoGames.SM.Engine.esG (.fst .v0)) (CryptoGames.SM.otherE (.fst (.snd .v0))) (.snd (.snd .v0))
  have hvr := vRecvC_excessUB_le hk Ho Hs Hr hhk (Γ' := Γ_ij0) (CryptoGames.SM.Engine.esH (.fst .v0)) (CryptoGames.SM.Engine.esG (.fst .v0)) (.fst (.snd .v0)) (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v0))) (.fst (.snd .v0))) (.snd (.snd .v0)) .none
  have hcm := commitEC_excessUB_le hk Ho Hs Hr L hhk (Γ' := decT :: .opt decT :: .prod (.opt (.opt decT)) hsT :: Γ_ij0) (CryptoGames.SM.Engine.esSetH (.fst .v3) (.snd .v2)) (CryptoGames.SM.Engine.esG (.fst .v3)) (.fst (.snd .v3)) (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v3))) (.fst (.snd .v3))) (.fst .v0) (.pair (CryptoGames.SM.otherE (.fst (.snd .v3))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hij := hcfg (Γ' := decT :: .opt decT :: .prod (.opt (.opt decT)) hsT :: Γ_ij0) (.fst (.snd .v0))
  simp only [CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.esSetH, CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.cGsSt, CryptoGames.SM.pGet, CryptoGames.SM.otherE, exprExcessUB_v0, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_var, exprExcessUB_not, exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_none, exprExcessUB_letE, Nat.add_zero, Nat.zero_add, Nat.mul_zero] at hit hvr hcm hij
  simp only [CryptoGames.SM.Engine.injectEC, CryptoGames.SM.Engine.cSafeInjE, CryptoGames.SM.Engine.cCompContainsE, CryptoGames.SM.Engine.cTrivialE, CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.esSetG, CryptoGames.SM.Engine.esSetH, CryptoGames.SM.Engine.cGsMk, CryptoGames.SM.Engine.cGsSetWin, CryptoGames.SM.Engine.cGsSt, CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.cGsEpoch, CryptoGames.SM.Engine.cGsIdx, CryptoGames.SM.Engine.cGsTL, CryptoGames.SM.Engine.cGsTrans, CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.Engine.cGsComp, CryptoGames.SM.Engine.cGsMaxAcc, CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs, CryptoGames.SM.Engine.cRecPos, CryptoGames.SM.healedByE, CryptoGames.SM.pGet, CryptoGames.SM.orE, CryptoGames.SM.isSomeE, CryptoGames.SM.otherE, CryptoGames.SM.leN, CryptoGames.SM.minN, CryptoGames.SM.ltOptE, CryptoGames.SM.posEq, CryptoGames.SM.boolEq, CryptoGames.SM.posSender, CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx, ckaOpC, exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_var, exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none, exprExcessUB_add, exprExcessUB_lt, exprExcessUB_eqN, exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_inl, exprExcessUB_inr, exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_letE, exprExcessUB_anyB, exprExcessUB_tget, compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt, Nat.add_zero, Nat.zero_add, Nat.mul_zero]; omega

set_option linter.unusedSimpArgs false in
theorem injectEC_anyCfg_sizeW_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sS : I'.smp.Samp → ℕ} {qS : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (Ho Hs Hr L Δ qep S_inj : ℕ) (hΔ : Δ ≤ 4) (cfg : CryptoGames.SM.Engine.ConfigEC OO_cka)
    (hcfg : ∀ {Γ'} (e : Expr OO_cka Γ' .nat), Bundles.exprSizeW (Bundles.ckaOpS B0) (cfg.injectFullE e) ≤ 4 * Bundles.exprSizeW (Bundles.ckaOpS B0) e + S_inj)
    (hhk : HooksSizeBounded B0 sS qS hk Ho Hs Hr)
    {Γ'} (es : Expr OO_cka Γ'
      (CryptoGames.SM.Engine.esTy (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ' (.prod .bool ckaHdrCtT)) :
    Bundles.compSizeW (Bundles.ckaOpS B0) sS qS (CryptoGames.SM.Engine.injectEC hk L Δ qep cfg es arg) ≤
      6 * (Bundles.exprSizeW (Bundles.ckaOpS B0) es + Bundles.exprSizeW (Bundles.ckaOpS B0) arg) + 2 * Ho + Hr + 8 * bits L + 4 * bits qep + 3 * S_inj + 6200 := by
  have hqep1 := bits_succ_le qep; have hc : Δ = 0 ∨ Δ = 1 ∨ Δ = 2 ∨ Δ = 3 ∨ Δ = 4 := by omega
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let decT : Ty S_cka := .prod vpT (.prod .nat (.prod .nat (.base .msg)))
  let Γ_ij0 : List (Ty S_cka) := .prod (CryptoGames.SM.Engine.esTy vpT hsT) (.prod .bool ckaHdrCtT) :: Γ'
  have hit := cInTransitE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (vpT := vpT) B0 L (Γ' := Γ_ij0) (CryptoGames.SM.Engine.esG (.fst .v0)) (CryptoGames.SM.otherE (.fst (.snd .v0))) (.snd (.snd .v0))
  have hvr := vRecvC_sizeW_le hk Ho Hs Hr hhk (Γ' := Γ_ij0) (CryptoGames.SM.Engine.esH (.fst .v0)) (CryptoGames.SM.Engine.esG (.fst .v0)) (.fst (.snd .v0)) (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v0))) (.fst (.snd .v0))) (.snd (.snd .v0)) .none
  have hcm := commitEC_sizeW_le hk Ho Hs Hr L hhk (Γ' := decT :: .opt decT :: .prod (.opt (.opt decT)) hsT :: Γ_ij0) (CryptoGames.SM.Engine.esSetH (.fst .v3) (.snd .v2)) (CryptoGames.SM.Engine.esG (.fst .v3)) (.fst (.snd .v3)) (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v3))) (.fst (.snd .v3))) (.fst .v0) (.pair (CryptoGames.SM.otherE (.fst (.snd .v3))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hij := hcfg (Γ' := decT :: .opt decT :: .prod (.opt (.opt decT)) hsT :: Γ_ij0) (.fst (.snd .v0))
  simp only [CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.esSetH, CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.cGsSt, CryptoGames.SM.pGet, CryptoGames.SM.otherE, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_var, exprSizeW_not, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_none, exprSizeW_letE, Nat.reduceAdd] at hit hvr hcm hij
  rcases hc with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [CryptoGames.SM.Engine.injectEC, CryptoGames.SM.Engine.cSafeInjE, CryptoGames.SM.Engine.cCompContainsE, CryptoGames.SM.Engine.cTrivialE, CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.esSetG, CryptoGames.SM.Engine.esSetH, CryptoGames.SM.Engine.cGsMk, CryptoGames.SM.Engine.cGsSetWin, CryptoGames.SM.Engine.cGsSt, CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.cGsEpoch, CryptoGames.SM.Engine.cGsIdx, CryptoGames.SM.Engine.cGsTL, CryptoGames.SM.Engine.cGsTrans, CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.Engine.cGsComp, CryptoGames.SM.Engine.cGsMaxAcc, CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs, CryptoGames.SM.Engine.cRecPos, CryptoGames.SM.healedByE, CryptoGames.SM.pGet, CryptoGames.SM.orE, CryptoGames.SM.isSomeE, CryptoGames.SM.otherE, CryptoGames.SM.leN, CryptoGames.SM.minN, CryptoGames.SM.ltOptE, CryptoGames.SM.posEq, CryptoGames.SM.boolEq, CryptoGames.SM.posSender, CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx, Bundles.ckaOpS, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4, exprSizeW_v5, exprSizeW_v6, exprSizeW_v7, exprSizeW_var, exprSizeW_unit, exprSizeW_bool, exprSizeW_nat, exprSizeW_none, exprSizeW_nil, exprSizeW_add, exprSizeW_sub, exprSizeW_modK, exprSizeW_lt, exprSizeW_eqN, exprSizeW_not, exprSizeW_and, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_inl, exprSizeW_inr, exprSizeW_some, exprSizeW_caseOpt, exprSizeW_caseSum, exprSizeW_letE, exprSizeW_op, exprSizeW_cons, exprSizeW_findB, exprSizeW_anyB, exprSizeW_foldrB, exprSizeW_tconst, exprSizeW_tget, exprSizeW_tset, compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt, compSizeW_caseSum, bits_zero, bits_one, bits_two, bits_three, bits_four, Nat.reduceAdd]
    omega

theorem deliverForgeEC_anyCfg_cost_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (H L Δ qep C_inj : ℕ)
    (hΔ : Δ ≤ 4) (cfg : CryptoGames.SM.Engine.ConfigEC OO_cka)
    (hcfg : ∀ {Γ'} (e : Expr OO_cka Γ' .nat), (cfg.injectFullE e).cost ≤ 3 * e.cost + C_inj)
    (hhk : HooksCostBounded hk H)
    {Γ'} (es : Expr OO_cka Γ' (CryptoGames.SM.Engine.esTy
      (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ' (.prod .bool (.prod ckaHdrCtT ckaHdrCtT))) :
    (CryptoGames.SM.Engine.deliverForgeEC hk L Δ qep cfg es arg).cost ≤
      es.cost + arg.cost + 3 * H + 650 * L + bits qep + C_inj + 5100 := by
  have hqep1 := bits_succ_le qep
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let decT : Ty S_cka := .prod vpT (.prod .nat (.prod .nat (.base .msg)))
  let Γ0 : List (Ty S_cka) := .prod (CryptoGames.SM.Engine.esTy vpT hsT) (.prod .bool (.prod ckaHdrCtT ckaHdrCtT)) :: Γ'
  let Γ1 : List (Ty S_cka) := CryptoGames.SM.Engine.cRecTy :: Γ0
  let Γ2 : List (Ty S_cka) := decT :: .opt decT :: .prod (.opt (.opt decT)) hsT :: Γ1
  have hit0 := cInTransitE_cost_le (vpT := vpT) L (Γ' := Γ0) (CryptoGames.SM.Engine.esG (O' := OO_cka) (.fst .v0)) (CryptoGames.SM.otherE (.fst (.snd .v0))) (.fst (.snd (.snd .v0)))
  have hit1 := cInTransitE_cost_le (vpT := vpT) L (Γ' := Γ1) (CryptoGames.SM.Engine.esG (O' := OO_cka) (.fst .v1)) (CryptoGames.SM.otherE (.fst (.snd .v1))) (.snd (.snd (.snd .v1)))
  have hcc1 := cCompContainsE_cost_le (O' := OO_cka) (vpT := vpT) L (Γ' := Γ1) (CryptoGames.SM.Engine.esG (.fst .v1)) (CryptoGames.SM.Engine.cRecPos .v0)
  have hhe1 := hdrEqE_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (Γ' := Γ1) (.fst (.snd (.snd .v1))) (.snd (.snd (.snd .v1)))
  have hvr := vRecvC_cost_le hk H hhk (Γ' := Γ1) (CryptoGames.SM.Engine.esH (.fst .v1)) (CryptoGames.SM.Engine.esG (.fst .v1)) (.fst (.snd .v1)) (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v1))) (.fst (.snd .v1))) (.snd (.snd (.snd .v1))) .none
  have htr := cTrivialE_any_cost_le (O' := OO_cka) (vpT := vpT) L Δ hΔ (Γ' := Γ2) (CryptoGames.SM.Engine.esG (.fst .v4)) (.pair (CryptoGames.SM.otherE (.fst (.snd .v4))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hcm := commitEC_cost_le hk H L hhk (Γ' := Γ2) (CryptoGames.SM.Engine.esSetH (.fst .v4) (.snd .v2)) (CryptoGames.SM.Engine.esG (.fst .v4)) (.fst (.snd .v4)) (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v4))) (.fst (.snd .v4))) (.fst .v0) (.pair (CryptoGames.SM.otherE (.fst (.snd .v4))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hij := hcfg (Γ' := Γ2) (.fst (.snd .v0))
  simp only [esG_cost, esH_cost, esSetH_cost, pGet_cost, cGsSt_cost, cRecPos_cost, otherE_cost, Expr.cost, v0_cost, v1_cost, v2_cost, v4_cost, Nat.reduceAdd] at hit0 hit1 hcc1 hhe1 hvr htr hcm hij
  simp only [CryptoGames.SM.Engine.deliverForgeEC, CryptoGames.SM.orE, CryptoGames.SM.isSomeE, CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.esMk, CryptoGames.SM.posEpoch, cRecPos_cost, esG_cost, esAbort_cost, esSetH_cost, esSetG_cost, cGsSetWin_cost, Comp.cost, Expr.cost, v0_cost, v1_cost, v2_cost, v3_cost, v4_cost, Nat.reduceAdd]; omega

theorem deliverForgeEC_anyCfg_excessUB_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sC : I'.smp.Samp → ℕ} {qC : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (Ho Hs Hr L Δ qep : ℕ)
    (cfg : CryptoGames.SM.Engine.ConfigEC OO_cka)
    (hcfg : ∀ {Γ'} (e : Expr OO_cka Γ' .nat), exprExcessUB (ckaOpC B0) (cfg.injectFullE e) ≤ 4 * exprExcessUB (ckaOpC B0) e)
    (hhk : HooksExcessBounded B0 sC qC hk Ho Hs Hr)
    {Γ'} (es : Expr OO_cka Γ' (CryptoGames.SM.Engine.esTy
      (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ' (.prod .bool (.prod ckaHdrCtT ckaHdrCtT))) :
    compExcessUB (ckaOpC B0) sC qC (CryptoGames.SM.Engine.deliverForgeEC hk L Δ qep cfg es arg) ≤
      60 * (exprExcessUB (ckaOpC B0) es + exprExcessUB (ckaOpC B0) arg) + 2 * Ho + Hr + 300 * L + 1000 := by
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let decT : Ty S_cka := .prod vpT (.prod .nat (.prod .nat (.base .msg)))
  let Γ0 : List (Ty S_cka) := .prod (CryptoGames.SM.Engine.esTy vpT hsT) (.prod .bool (.prod ckaHdrCtT ckaHdrCtT)) :: Γ'
  let Γ1 : List (Ty S_cka) := CryptoGames.SM.Engine.cRecTy :: Γ0
  let Γ2 : List (Ty S_cka) := decT :: .opt decT :: .prod (.opt (.opt decT)) hsT :: Γ1
  have hit0 := cInTransitE_excessUB (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (vpT := vpT) B0 L (Γ' := Γ0) (CryptoGames.SM.Engine.esG (.fst .v0)) (CryptoGames.SM.otherE (.fst (.snd .v0))) (.fst (.snd (.snd .v0)))
  have hit1 := cInTransitE_excessUB (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (vpT := vpT) B0 L (Γ' := Γ1) (CryptoGames.SM.Engine.esG (.fst .v1)) (CryptoGames.SM.otherE (.fst (.snd .v1))) (.snd (.snd (.snd .v1)))
  have hhe1 := hdrEqE_excessUB (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) B0 (Γ' := Γ1) (.fst (.snd (.snd .v1))) (.snd (.snd (.snd .v1)))
  have hvr := vRecvC_excessUB_le hk Ho Hs Hr hhk (Γ' := Γ1) (CryptoGames.SM.Engine.esH (.fst .v1)) (CryptoGames.SM.Engine.esG (.fst .v1)) (.fst (.snd .v1)) (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v1))) (.fst (.snd .v1))) (.snd (.snd (.snd .v1))) .none
  have hcm := commitEC_excessUB_le hk Ho Hs Hr L hhk (Γ' := Γ2) (CryptoGames.SM.Engine.esSetH (.fst .v4) (.snd .v2)) (CryptoGames.SM.Engine.esG (.fst .v4)) (.fst (.snd .v4)) (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v4))) (.fst (.snd .v4))) (.fst .v0) (.pair (CryptoGames.SM.otherE (.fst (.snd .v4))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hij := hcfg (Γ' := Γ2) (.fst (.snd .v0))
  simp only [CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.esSetH, CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.cGsSt, CryptoGames.SM.pGet, CryptoGames.SM.otherE, exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v4, exprExcessUB_not, exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_none, exprExcessUB_letE, Nat.add_zero, Nat.zero_add, Nat.mul_zero] at hit0 hit1 hhe1 hvr hcm hij
  simp only [CryptoGames.SM.Engine.deliverForgeEC, CryptoGames.SM.Engine.cCompContainsE, CryptoGames.SM.Engine.cTrivialE, CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.esSetG, CryptoGames.SM.Engine.esSetH, CryptoGames.SM.Engine.cGsMk, CryptoGames.SM.Engine.cGsSetWin, CryptoGames.SM.Engine.cGsSt, CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.cGsEpoch, CryptoGames.SM.Engine.cGsIdx, CryptoGames.SM.Engine.cGsTL, CryptoGames.SM.Engine.cGsTrans, CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.Engine.cGsComp, CryptoGames.SM.Engine.cGsMaxAcc, CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs, CryptoGames.SM.Engine.cRecPos, CryptoGames.SM.healedByE, CryptoGames.SM.pGet, CryptoGames.SM.orE, CryptoGames.SM.isSomeE, CryptoGames.SM.otherE, CryptoGames.SM.leN, CryptoGames.SM.posEq, CryptoGames.SM.boolEq, CryptoGames.SM.posSender, CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx, exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4, exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none, exprExcessUB_add, exprExcessUB_lt, exprExcessUB_eqN, exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_inl, exprExcessUB_inr, exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_letE, exprExcessUB_anyB, exprExcessUB_tget, compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt, Nat.add_zero, Nat.zero_add, Nat.mul_zero]; omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
theorem deliverForgeEC_anyCfg_sizeW_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sS : I'.smp.Samp → ℕ} {qS : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (Ho Hs Hr L Δ qep S_inj : ℕ)
    (hΔ : Δ ≤ 4) (cfg : CryptoGames.SM.Engine.ConfigEC OO_cka)
    (hcfg : ∀ {Γ'} (e : Expr OO_cka Γ' .nat), Bundles.exprSizeW (Bundles.ckaOpS B0) (cfg.injectFullE e) ≤ 4 * Bundles.exprSizeW (Bundles.ckaOpS B0) e + S_inj)
    (hhk : HooksSizeBounded B0 sS qS hk Ho Hs Hr)
    {Γ'} (es : Expr OO_cka Γ' (CryptoGames.SM.Engine.esTy
      (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ' (.prod .bool (.prod ckaHdrCtT ckaHdrCtT))) :
    Bundles.compSizeW (Bundles.ckaOpS B0) sS qS (CryptoGames.SM.Engine.deliverForgeEC hk L Δ qep cfg es arg) ≤
      10 * (Bundles.exprSizeW (Bundles.ckaOpS B0) es + Bundles.exprSizeW (Bundles.ckaOpS B0) arg) + 2 * Ho + Hr + 20 * bits L + 5 * bits qep + 5 * S_inj + 10500 := by
  have hqep1 := bits_succ_le qep; have hc : Δ = 0 ∨ Δ = 1 ∨ Δ = 2 ∨ Δ = 3 ∨ Δ = 4 := by omega
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let decT : Ty S_cka := .prod vpT (.prod .nat (.prod .nat (.base .msg)))
  let Γ0 : List (Ty S_cka) := .prod (CryptoGames.SM.Engine.esTy vpT hsT) (.prod .bool (.prod ckaHdrCtT ckaHdrCtT)) :: Γ'
  let Γ1 : List (Ty S_cka) := CryptoGames.SM.Engine.cRecTy :: Γ0
  let Γ2 : List (Ty S_cka) := decT :: .opt decT :: .prod (.opt (.opt decT)) hsT :: Γ1
  have hit0 := cInTransitE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (vpT := vpT) B0 L (Γ' := Γ0) (CryptoGames.SM.Engine.esG (.fst .v0)) (CryptoGames.SM.otherE (.fst (.snd .v0))) (.fst (.snd (.snd .v0)))
  have hit1 := cInTransitE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) (vpT := vpT) B0 L (Γ' := Γ1) (CryptoGames.SM.Engine.esG (.fst .v1)) (CryptoGames.SM.otherE (.fst (.snd .v1))) (.snd (.snd (.snd .v1)))
  have hhe1 := hdrEqE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) B0 (Γ' := Γ1) (.fst (.snd (.snd .v1))) (.snd (.snd (.snd .v1)))
  have hvr := vRecvC_sizeW_le hk Ho Hs Hr hhk (Γ' := Γ1) (CryptoGames.SM.Engine.esH (.fst .v1)) (CryptoGames.SM.Engine.esG (.fst .v1)) (.fst (.snd .v1)) (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v1))) (.fst (.snd .v1))) (.snd (.snd (.snd .v1))) .none
  have hcm := commitEC_sizeW_le hk Ho Hs Hr L hhk (Γ' := Γ2) (CryptoGames.SM.Engine.esSetH (.fst .v4) (.snd .v2)) (CryptoGames.SM.Engine.esG (.fst .v4)) (.fst (.snd .v4)) (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v4))) (.fst (.snd .v4))) (.fst .v0) (.pair (CryptoGames.SM.otherE (.fst (.snd .v4))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hij := hcfg (Γ' := Γ2) (.fst (.snd .v0))
  simp only [CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.esSetH, CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.cGsSt, CryptoGames.SM.pGet, CryptoGames.SM.otherE, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v4, exprSizeW_var, exprSizeW_not, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_none, exprSizeW_letE, Nat.reduceAdd] at hit0 hit1 hhe1 hvr hcm hij
  rcases hc with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [CryptoGames.SM.Engine.deliverForgeEC, CryptoGames.SM.Engine.cCompContainsE, CryptoGames.SM.Engine.cChallContainsE, CryptoGames.SM.Engine.cTrivialE, CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.esSetG, CryptoGames.SM.Engine.esSetH, CryptoGames.SM.Engine.cGsMk, CryptoGames.SM.Engine.cGsSetWin, CryptoGames.SM.Engine.cGsSt, CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.cGsEpoch, CryptoGames.SM.Engine.cGsIdx, CryptoGames.SM.Engine.cGsTL, CryptoGames.SM.Engine.cGsTrans, CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.Engine.cGsComp, CryptoGames.SM.Engine.cGsMaxAcc, CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs, CryptoGames.SM.Engine.cRecPos, CryptoGames.SM.healedByE, CryptoGames.SM.pGet, CryptoGames.SM.orE, CryptoGames.SM.isSomeE, CryptoGames.SM.otherE, CryptoGames.SM.leN, CryptoGames.SM.posEq, CryptoGames.SM.boolEq, CryptoGames.SM.posSender, CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx, Bundles.ckaOpS, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4, exprSizeW_v5, exprSizeW_var, exprSizeW_unit, exprSizeW_bool, exprSizeW_nat, exprSizeW_none, exprSizeW_nil, exprSizeW_add, exprSizeW_sub, exprSizeW_modK, exprSizeW_lt, exprSizeW_eqN, exprSizeW_not, exprSizeW_and, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_inl, exprSizeW_inr, exprSizeW_some, exprSizeW_caseOpt, exprSizeW_caseSum, exprSizeW_letE, exprSizeW_op, exprSizeW_cons, exprSizeW_findB, exprSizeW_anyB, exprSizeW_foldrB, exprSizeW_tconst, exprSizeW_tget, exprSizeW_tset, compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt, compSizeW_caseSum, bits_zero, bits_one, bits_two, bits_three, bits_four, Nat.reduceAdd]
    omega

/-! ## 3. Shared `(tL, par)`-Bucket `bucketHandleC`, `ckaBucketFinishC`, and Paper Bucket CKA Bounds -/

@[expose, reducible] def corrAllowedChoiceE {vpT : Ty S_cka}
    (paper : Bool) (L : ℕ) {Γ'} (s0 : Expr OO_cka Γ' (CryptoGames.SM.Engine.cGsTy vpT))
    (p0 : Expr OO_cka Γ' .bool) : Expr OO_cka Γ' .bool :=
  match paper with
  | true => CryptoGames.SM.Engine.cCorrAllowedPaperE (O' := OO_cka) L s0 p0
  | false => CryptoGames.SM.Engine.cCorrAllowedE (O' := OO_cka) L s0 p0

@[expose] def bucketHandleC {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S_cka}
    (paper : Bool)
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (L Δ qep maxSkip : ℕ) (cfg : CryptoGames.SM.Engine.ConfigEC OO_cka) :
    Comp OO_cka I'
      [.prod (CryptoGames.SM.Engine.esTy
        (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT)
        (.opt .nat),
       (CryptoGames.CKA.ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).Q]
      (.prod (CryptoGames.CKA.ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).R
        (.prod (CryptoGames.SM.Engine.esTy
          (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT)
          (.opt .nat))) :=
  rdsl [st, q] do
    (es0, winEp0, q0) ← return (st.1, st.2, q)
    match q0 with
    | .inl qBase =>
      match qBase with
      | .inl (.inl (.inl (.inl x))) =>
        (p0, m0, r0) ← return x
        if CryptoGames.SM.orE (CryptoGames.SM.Engine.esAbort es0)
            (CryptoGames.SM.Engine.cGsWin (CryptoGames.SM.Engine.esG es0)) then
          return (.inl (inl (inl (inl (inl none)))), (es0, winEp0))
        else
          match CryptoGames.SM.Engine.cEpMgmtE (raw Δ) (raw qep) (CryptoGames.SM.Engine.esG es0) p0
              (CryptoGames.SM.isSomeE r0) with
          | none => return (.inl (inl (inl (inl (inl none)))), (es0, winEp0))
          | some s1 =>
            (res, h') ← CryptoGames.SM.Engine.vSendC (raw hk)
              (CryptoGames.SM.Engine.esH es0) s1 p0
              (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt s1) p0) m0 none r0
            match res with
            | none =>
              return (.inl (inl (inl (inl (inl none)))),
                (CryptoGames.SM.Engine.esMk (CryptoGames.SM.Engine.esG es0) h' true, winEp0))
            | some (st', ct) =>
              let recE :=
                ((p0, CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsEpoch s1) p0,
                  CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsIdx s1) p0 + 1), m0, ct)
              let g' := CryptoGames.SM.Engine.cRecordE (raw L) (raw Δ) s1 p0 st' recE false
              return (.inl (inl (inl (inl (inl (some ct))))),
                (CryptoGames.SM.Engine.esMk g' h' (CryptoGames.SM.Engine.esAbort es0), winEp0))
      | .inl (.inl (.inl (.inr _))) =>
        return (.inl (inl (inl (inl (inr none)))), (es0, winEp0))
      | .inl (.inl (.inr x)) =>
        (out, es') ← CryptoGames.SM.Engine.deliverEC (raw hk) L maxSkip (raw cfg) es0 x
        return (.inl (inl (inl (inr out))), (es', winEp0))
      | .inl (.inr x) =>
        let wasWin := CryptoGames.SM.Engine.cGsWin (CryptoGames.SM.Engine.esG es0)
        (out, es') ← CryptoGames.SM.Engine.injectEC (raw hk) L (raw Δ) qep (raw cfg) es0 x
        let winEp' :=
          if !wasWin && CryptoGames.SM.Engine.cGsWin (CryptoGames.SM.Engine.esG es') then
            some x.2.1.1
          else winEp0
        return (.inl (inl (inr out)), (es', winEp'))
      | .inr p0 =>
        let s0 := CryptoGames.SM.Engine.esG es0
        if CryptoGames.SM.orE (CryptoGames.SM.Engine.esAbort es0)
            (CryptoGames.SM.orE (CryptoGames.SM.Engine.cGsWin s0)
              (!(corrAllowedChoiceE (raw paper) (raw L) s0 p0))) then
          return (.inl (inr none), (es0, winEp0))
        else
          let s1 := CryptoGames.SM.Engine.cAfterCorrE (raw L) s0 p0
          (res, h') ← CryptoGames.SM.Engine.HooksC.reveal (raw hk)
            (CryptoGames.SM.Engine.esH es0) s0 p0
            (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt s0) p0)
          match res with
          | none =>
            return (.inl (inr none), (CryptoGames.SM.Engine.esMk s0 h' true, winEp0))
          | some stOut =>
            return (.inl (inr (some stOut)),
              (CryptoGames.SM.Engine.esMk s1 h' (CryptoGames.SM.Engine.esAbort es0), winEp0))
    | .inr x =>
      let wasWin := CryptoGames.SM.Engine.cGsWin (CryptoGames.SM.Engine.esG es0)
      (out, es') ← CryptoGames.SM.Engine.deliverForgeEC (raw hk) L (raw Δ) qep (raw cfg) es0 x
      let winEp' :=
        if !wasWin && CryptoGames.SM.Engine.cGsWin (CryptoGames.SM.Engine.esG es') then
          some x.2.2.1.1
        else winEp0
      return (.inr out, (es', winEp'))

@[expose] def ckaBucketFinishC {ι : Type} {Spec' : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka Spec'} {vpT hsT : Ty S_cka}
    (L Δ : ℕ) (tL : Option ℕ) :
    Comp OO_cka I' [.prod (CryptoGames.SM.Engine.esTy vpT hsT) (.opt .nat), .unit] .bool :=
  rdsl [st, _] do
    (es0, winEp0) ← return (st.1, st.2)
    match winEp0 with
    | none => return false
    | some tWin =>
      return ((!(CryptoGames.SM.Engine.esAbort es0) &&
        CryptoGames.SM.Engine.cGsWin (CryptoGames.SM.Engine.esG es0)) &&
        CryptoGames.SM.Engine.cAuthOKE (raw L) (raw Δ)
          (CryptoGames.SM.Engine.optNatLit (raw tL)) tWin (CryptoGames.SM.Engine.esG es0))

private def bucketFinishModeC {ι : Type} {Spec' : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka Spec'} {vpT hsT : Ty S_cka}
    (mode : Fin 3) (L Δ : ℕ) (tL : Option ℕ) :
    Comp OO_cka I' [.prod (CryptoGames.SM.Engine.esTy vpT hsT) (.opt .nat), .bool] .bool :=
  match mode with
  | ⟨0, _⟩ =>
    rdsl [st, _] do
      (es0, winEp0) ← return (st.1, st.2)
      match winEp0 with
      | none => return false
      | some tWin =>
        return ((!(CryptoGames.SM.Engine.esAbort es0) &&
          CryptoGames.SM.Engine.cGsWin (CryptoGames.SM.Engine.esG es0)) &&
          CryptoGames.SM.Engine.cAuthOKE (raw L) (raw Δ)
            (CryptoGames.SM.Engine.optNatLit (raw tL)) tWin (CryptoGames.SM.Engine.esG es0))
  | ⟨1, _⟩ =>
    rdsl [st, _] do
      (es0, winEp0) ← return (st.1, st.2)
      match winEp0 with
      | none => return false
      | some tWin =>
        return (((!(CryptoGames.SM.Engine.esAbort es0) &&
          CryptoGames.SM.Engine.cGsWin (CryptoGames.SM.Engine.esG es0)) &&
          CryptoGames.SM.Engine.cAuthOKE (raw L) (raw Δ)
            (CryptoGames.SM.Engine.optNatLit (raw tL)) tWin (CryptoGames.SM.Engine.esG es0)) &&
          CryptoGames.SM.optNatEqE (CryptoGames.SM.Engine.cGsTL (CryptoGames.SM.Engine.esG es0))
            (CryptoGames.SM.Engine.optNatLit (raw tL)))
  | ⟨_ + 2, _⟩ =>
    rdsl [st, _] do
      (es0, winEp0) ← return (st.1, st.2)
      match winEp0 with
      | none => return false
      | some tWin =>
        return ((!(CryptoGames.SM.Engine.esAbort es0) &&
          CryptoGames.SM.Engine.cGsWin (CryptoGames.SM.Engine.esG es0)) &&
          CryptoGames.SM.Engine.cAuthOKE (raw L) (raw Δ)
            (CryptoGames.SM.Engine.optNatLit (raw tL)) tWin (CryptoGames.SM.Engine.esG es0) &&
          CryptoGames.SM.optNatEqE (CryptoGames.SM.Engine.cGsTL (CryptoGames.SM.Engine.esG es0))
            (CryptoGames.SM.Engine.optNatLit (raw tL)))

theorem redCKAAuthDFPaperBucketProgGen_handle_eq (L B Δcka Δbucket qep maxSkip : ℕ)
    (tL : Option ℕ) (par : Bool) :
    (CryptoGames.SM.Construction.redCKAAuthDFPaperBucketProgGen
      (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B Δcka Δbucket qep maxSkip tL par).handle =
    bucketHandleC true
      (CryptoGames.SM.Construction.hooksCKABucketParPaperC (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B Δcka Δbucket tL par)
      L (2 + Δcka) qep maxSkip
      (CryptoGames.SM.Construction.bucketParPaperAuthCfgEC Δbucket tL par) := rfl

private theorem corrAllowedChoiceE_cost_le {vpT : Ty S_cka} (paper : Bool) (L : ℕ) {Γ'}
    (s0 : Expr OO_cka Γ' (CryptoGames.SM.Engine.cGsTy vpT)) (p0 : Expr OO_cka Γ' .bool) :
    (corrAllowedChoiceE paper L s0 p0).cost ≤ s0.cost + p0.cost + 300 * L + 150 := by
  cases paper
  · exact cCorrAllowedE_cost_le L s0 p0
  · exact cCorrAllowedPaperE_cost_le L s0 p0

set_option linter.unusedSimpArgs false in
private theorem corrAllowedChoiceE_excessUB {vpT : Ty S_cka} (B0 : ℕ) (paper : Bool) (L : ℕ) {Γ'}
    (s0 : Expr OO_cka Γ' (CryptoGames.SM.Engine.cGsTy vpT)) (p0 : Expr OO_cka Γ' .bool) :
    exprExcessUB (ckaOpC B0) (corrAllowedChoiceE paper L s0 p0) ≤
      2 * (exprExcessUB (ckaOpC B0) s0 + exprExcessUB (ckaOpC B0) p0) := by
  cases paper <;> ·
    simp only [corrAllowedChoiceE, CryptoGames.SM.Engine.cCorrAllowedPaperE,
      CryptoGames.SM.Engine.cCorrAllowedE, CryptoGames.SM.Engine.cCompContainsE,
      CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.Engine.cGsTrans, CryptoGames.SM.Engine.cGsComp,
      CryptoGames.SM.Engine.cRecPos, CryptoGames.SM.pGet, CryptoGames.SM.posSender,
      CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx, CryptoGames.SM.boolEq, CryptoGames.SM.otherE,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_var, exprExcessUB_bool,
      exprExcessUB_nat, exprExcessUB_eqN, exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite,
      exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_letE, exprExcessUB_anyB,
      exprExcessUB_tget, Nat.add_zero, Nat.zero_add, Nat.mul_zero]; omega

set_option linter.unusedSimpArgs false in
private theorem corrAllowedChoiceE_sizeW_le {vpT : Ty S_cka} (B0 : ℕ) (paper : Bool) (L : ℕ) {Γ'}
    (s0 : Expr OO_cka Γ' (CryptoGames.SM.Engine.cGsTy vpT)) (p0 : Expr OO_cka Γ' .bool) :
    Bundles.exprSizeW (Bundles.ckaOpS B0) (corrAllowedChoiceE paper L s0 p0) ≤
      2 * (Bundles.exprSizeW (Bundles.ckaOpS B0) s0 + Bundles.exprSizeW (Bundles.ckaOpS B0) p0) +
        4 * bits L + 200 := by
  cases paper <;> ·
    simp only [corrAllowedChoiceE, CryptoGames.SM.Engine.cCorrAllowedPaperE,
      CryptoGames.SM.Engine.cCorrAllowedE, CryptoGames.SM.Engine.cCompContainsE,
      CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.Engine.cGsTrans, CryptoGames.SM.Engine.cGsComp,
      CryptoGames.SM.Engine.cRecPos, CryptoGames.SM.pGet, CryptoGames.SM.posSender,
      CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx, CryptoGames.SM.boolEq, CryptoGames.SM.otherE,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_var, exprSizeW_bool, exprSizeW_nat,
      exprSizeW_eqN, exprSizeW_not, exprSizeW_and, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst,
      exprSizeW_snd, exprSizeW_letE, exprSizeW_anyB, exprSizeW_tget, bits_zero, bits_one, Nat.reduceAdd]; omega

set_option linter.unusedSimpArgs false in
theorem ckaBucketFinishC_cost_le {ι : Type} {Spec' : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka Spec'} {vpT hsT : Ty S_cka} (L Δ : ℕ) (hΔ : Δ ≤ 4) (tL : Option ℕ) :
    (ckaBucketFinishC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (I' := I') (vpT := vpT) (hsT := hsT) L Δ tL).cost ≤
      240 * L + 2 * bits (tL.getD 0) + 350 := by
  let Γf : List (Ty S_cka) := .nat :: .prod (CryptoGames.SM.Engine.esTy vpT hsT) (.opt .nat) ::
    [.prod (CryptoGames.SM.Engine.esTy vpT hsT) (.opt .nat), .unit]
  have hAuth := cAuthOKE_any_cost_le (O' := OO_cka) (vpT := vpT) L Δ hΔ (Γ' := Γf)
    (CryptoGames.SM.Engine.optNatLit tL) .v0 (CryptoGames.SM.Engine.esG (hsT := hsT) (.fst .v1))
  have hOpt : (CryptoGames.SM.Engine.optNatLit (O' := OO_cka) (Γ' := Γf) tL).cost ≤
      bits (tL.getD 0) + 2 := by
    cases tL <;> simp only [CryptoGames.SM.Engine.optNatLit, Option.getD, Expr.cost, bits_zero] <;> omega
  dsimp only [ckaBucketFinishC]
  simp only [esG_cost, esAbort_cost, CryptoGames.SM.Engine.cGsWin, Comp.cost, Expr.cost, dsl_cost,
    v0_cost, v1_cost, Nat.reduceAdd] at hAuth ⊢; omega

set_option linter.unusedSimpArgs false in
theorem ckaBucketFinishC_excessUB_le {ι : Type} {Spec' : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka Spec'} {vpT hsT : Ty S_cka}
    (B0 : ℕ) (sC : I'.smp.Samp → ℕ) (qC : I'.Tag → ℕ) (L Δ : ℕ) (tL : Option ℕ) :
    compExcessUB (ckaOpC B0) sC qC
      (ckaBucketFinishC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) (I' := I') (vpT := vpT) (hsT := hsT) L Δ tL) ≤ 20 := by
  simp only [ckaBucketFinishC, CryptoGames.SM.Engine.cAuthOKE, CryptoGames.SM.Engine.cCanonE,
    CryptoGames.SM.validGuessE, CryptoGames.SM.healedByE, CryptoGames.SM.optNatEqE,
    CryptoGames.SM.ltOptE, CryptoGames.SM.leN, CryptoGames.SM.maxN, CryptoGames.SM.boolEq,
    CryptoGames.SM.receiverOfE,
    CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.esG,
    CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs, optNatLit_excessUB,
    exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_var,
    exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none, exprExcessUB_add, exprExcessUB_modK,
    exprExcessUB_lt, exprExcessUB_eqN, exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite,
    exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_some, exprExcessUB_caseOpt,
    exprExcessUB_letE, exprExcessUB_anyB, exprExcessUB_foldrB, compExcessUB_ret, compExcessUB_bind,
    compExcessUB_caseOpt, Nat.add_zero, Nat.zero_add, Nat.mul_zero]; omega

set_option linter.unusedSimpArgs false in
theorem ckaBucketFinishC_sizeW_le {ι : Type} {Spec' : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka Spec'} {vpT hsT : Ty S_cka}
    (B0 : ℕ) (sS : I'.smp.Samp → ℕ) (qS : I'.Tag → ℕ) (L Δ : ℕ) (hΔ : Δ ≤ 4) (tL : Option ℕ) :
    Bundles.compSizeW (Bundles.ckaOpS B0) sS qS
      (ckaBucketFinishC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) (I' := I') (vpT := vpT) (hsT := hsT) L Δ tL) ≤
      10 * bits L + 4 * bits (tL.getD 0) + 600 := by
  have hc : Δ = 0 ∨ Δ = 1 ∨ Δ = 2 ∨ Δ = 3 ∨ Δ = 4 := by omega
  cases tL <;> rcases hc with rfl | rfl | rfl | rfl | rfl <;> ·
    simp only [ckaBucketFinishC, CryptoGames.SM.Engine.cAuthOKE, CryptoGames.SM.Engine.cCanonE,
      CryptoGames.SM.validGuessE, CryptoGames.SM.healedByE, CryptoGames.SM.optNatEqE,
      CryptoGames.SM.ltOptE, CryptoGames.SM.leN, CryptoGames.SM.maxN, CryptoGames.SM.boolEq,
      CryptoGames.SM.receiverOfE, Option.getD, CryptoGames.SM.Engine.optNatLit,
      CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.esG,
      CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_var, exprSizeW_bool,
      exprSizeW_nat, exprSizeW_none, exprSizeW_add, exprSizeW_modK, exprSizeW_lt, exprSizeW_eqN,
      exprSizeW_not, exprSizeW_and, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
      exprSizeW_some, exprSizeW_caseOpt, exprSizeW_letE, exprSizeW_anyB, exprSizeW_foldrB,
      compSizeW_ret, compSizeW_bind, compSizeW_caseOpt,
      bits_zero, bits_one, bits_two, bits_three, bits_four, Nat.reduceAdd]; omega

set_option linter.unusedSimpArgs false in
private theorem bucketFinishModeC_cost_le {ι : Type} {Spec' : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka Spec'} {vpT hsT : Ty S_cka}
    (mode : Fin 3) (L Δ : ℕ) (hΔ : Δ ≤ 4) (tL : Option ℕ) :
    (bucketFinishModeC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (I' := I') (vpT := vpT) (hsT := hsT) mode L Δ tL).cost ≤
      240 * L + 4 * bits (tL.getD 0) + 400 := by
  rcases mode with ⟨_ | _ | _, _⟩ <;> ·
    let Γf : List (Ty S_cka) := .nat :: .prod (CryptoGames.SM.Engine.esTy vpT hsT) (.opt .nat) ::
      [.prod (CryptoGames.SM.Engine.esTy vpT hsT) (.opt .nat), .bool]
    have hAuth := cAuthOKE_any_cost_le (O' := OO_cka) (vpT := vpT) L Δ hΔ (Γ' := Γf)
      (CryptoGames.SM.Engine.optNatLit tL) .v0 (CryptoGames.SM.Engine.esG (hsT := hsT) (.fst .v1))
    have hOpt : (CryptoGames.SM.Engine.optNatLit (O' := OO_cka) (Γ' := Γf) tL).cost ≤
        bits (tL.getD 0) + 2 := by
      cases tL <;> simp only [CryptoGames.SM.Engine.optNatLit, Option.getD, Expr.cost, bits_zero] <;> omega
    have hEq : (CryptoGames.SM.optNatEqE (Γ := Γf)
        (CryptoGames.SM.Engine.cGsTL
          (CryptoGames.SM.Engine.esG (O' := OO_cka) (vpT := vpT) (hsT := hsT) (.fst .v1)))
        (CryptoGames.SM.Engine.optNatLit tL)).cost ≤ 2 * bits (tL.getD 0) + 30 := by
      cases tL <;> simp only [CryptoGames.SM.optNatEqE, CryptoGames.SM.Engine.cGsTL,
        CryptoGames.SM.Engine.optNatLit, Option.getD, esG_cost, Expr.cost, dsl_cost,
        v0_cost, v1_cost, v2_cost, bits_zero, Nat.reduceAdd] <;> omega
    dsimp only [bucketFinishModeC]
    simp only [esG_cost, esAbort_cost, CryptoGames.SM.Engine.cGsWin, Comp.cost, Expr.cost, dsl_cost,
      v0_cost, v1_cost, Nat.reduceAdd] at hAuth hEq ⊢; omega

set_option linter.unusedSimpArgs false in
private theorem bucketFinishModeC_excessUB_le {ι : Type} {Spec' : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka Spec'} {vpT hsT : Ty S_cka}
    (B0 : ℕ) (sC : I'.smp.Samp → ℕ) (qC : I'.Tag → ℕ) (mode : Fin 3) (L Δ : ℕ) (tL : Option ℕ) :
    compExcessUB (ckaOpC B0) sC qC
      (bucketFinishModeC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) (I' := I') (vpT := vpT) (hsT := hsT) mode L Δ tL) ≤ 30 := by
  rcases mode with ⟨_ | _ | _, _⟩ <;> ·
    simp only [bucketFinishModeC, ckaBucketFinishC, CryptoGames.SM.Engine.cAuthOKE,
      CryptoGames.SM.Engine.cCanonE, CryptoGames.SM.Engine.cGsTL,
      CryptoGames.SM.validGuessE, CryptoGames.SM.healedByE, CryptoGames.SM.optNatEqE,
      CryptoGames.SM.ltOptE, CryptoGames.SM.leN, CryptoGames.SM.maxN, CryptoGames.SM.boolEq,
      CryptoGames.SM.receiverOfE,
      CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.esG,
      CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs, optNatLit_excessUB,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_var,
      exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none, exprExcessUB_add, exprExcessUB_modK,
      exprExcessUB_lt, exprExcessUB_eqN, exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite,
      exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_some, exprExcessUB_caseOpt,
      exprExcessUB_letE, exprExcessUB_anyB, exprExcessUB_foldrB, compExcessUB_ret, compExcessUB_bind,
      compExcessUB_caseOpt, Nat.add_zero, Nat.zero_add, Nat.mul_zero]; omega

set_option linter.unusedSimpArgs false in
private theorem bucketFinishModeC_sizeW_le {ι : Type} {Spec' : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka Spec'} {vpT hsT : Ty S_cka}
    (B0 : ℕ) (sS : I'.smp.Samp → ℕ) (qS : I'.Tag → ℕ) (mode : Fin 3) (L Δ : ℕ) (hΔ : Δ ≤ 4)
    (tL : Option ℕ) :
    Bundles.compSizeW (Bundles.ckaOpS B0) sS qS
      (bucketFinishModeC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) (I' := I') (vpT := vpT) (hsT := hsT) mode L Δ tL) ≤
      10 * bits L + 8 * bits (tL.getD 0) + 700 := by
  have hbΔ : bits Δ ≤ 3 := by rcases (by omega : Δ = 0 ∨ Δ = 1 ∨ Δ = 2 ∨ Δ = 3 ∨ Δ = 4) with rfl | rfl | rfl | rfl | rfl <;> decide
  rcases mode with ⟨_ | _ | _, _⟩ <;> cases tL <;> ·
    simp only [bucketFinishModeC, ckaBucketFinishC, CryptoGames.SM.Engine.cAuthOKE,
      CryptoGames.SM.Engine.cCanonE, CryptoGames.SM.Engine.cGsTL,
      CryptoGames.SM.validGuessE, CryptoGames.SM.healedByE, CryptoGames.SM.optNatEqE,
      CryptoGames.SM.ltOptE, CryptoGames.SM.leN, CryptoGames.SM.maxN, CryptoGames.SM.boolEq,
      CryptoGames.SM.receiverOfE, Option.getD, CryptoGames.SM.Engine.optNatLit,
      CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.esG,
      CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_var, exprSizeW_bool,
      exprSizeW_nat, exprSizeW_none, exprSizeW_add, exprSizeW_modK, exprSizeW_lt, exprSizeW_eqN,
      exprSizeW_not, exprSizeW_and, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
      exprSizeW_some, exprSizeW_caseOpt, exprSizeW_letE, exprSizeW_anyB, exprSizeW_foldrB,
      compSizeW_ret, compSizeW_bind, compSizeW_caseOpt,
      bits_zero, bits_one, bits_two, Nat.reduceAdd]; omega

set_option linter.unusedSimpArgs false in
theorem bucketHandleC_cost_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S_cka}
    (paper : Bool) (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (H L Δ qep maxSkip C_inj : ℕ) (hΔ : Δ ≤ 4) (cfg : CryptoGames.SM.Engine.ConfigEC OO_cka)
    (hcfg : ∀ {Γ'} (e : Expr OO_cka Γ' .nat), (cfg.injectFullE e).cost ≤ 3 * e.cost + C_inj)
    (hhk : HooksCostBounded hk H) :
    (bucketHandleC paper hk L Δ qep maxSkip cfg).cost ≤
      3 * H + 6000 * L + 5 * bits qep + 2 * (maxSkip + 1) + C_inj + 8000 := by
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let psT := CryptoGames.CKA.ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E
  let esT := CryptoGames.SM.Engine.esTy vpT hsT; let qT := (CryptoGames.CKA.ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).Q
  let txQ : Ty S_cka := .prod .bool (.prod (.base .msg) (.opt (.base .ccoins)))
  let chQ : Ty S_cka := .prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .ccoins))))
  let dlQ : Ty S_cka := .prod .bool ckaHdrCtT; let dfQ : Ty S_cka := .prod .bool (.prod ckaHdrCtT ckaHdrCtT)
  let smqT : Ty S_cka := .sum (.sum (.sum (.sum txQ chQ) dlQ) dlQ) .bool
  let Γ0 : List (Ty S_cka) := .prod esT (.prod (.opt .nat) qT) :: [.prod esT (.opt .nat), qT]
  let Γ_df : List (Ty S_cka) := dfQ :: Γ0; let Γ_cr : List (Ty S_cka) := .bool :: smqT :: Γ0
  let Γ_cr2 : List (Ty S_cka) := psT :: .prod (.opt psT) hsT :: Γ_cr
  let Γ_ij : List (Ty S_cka) := dlQ :: .sum (.sum (.sum txQ chQ) dlQ) dlQ :: smqT :: Γ0
  let Γ_dl : List (Ty S_cka) := dlQ :: .sum (.sum txQ chQ) dlQ :: .sum (.sum (.sum txQ chQ) dlQ) dlQ :: smqT :: Γ0
  let Γ_tx0 : List (Ty S_cka) := txQ :: txQ :: .sum txQ chQ :: .sum (.sum txQ chQ) dlQ :: .sum (.sum (.sum txQ chQ) dlQ) dlQ :: smqT :: Γ0
  let Γ_tx1 : List (Ty S_cka) := CryptoGames.SM.Engine.cGsTy vpT :: Γ_tx0
  let Γ_tx2 : List (Ty S_cka) := .prod vpT ckaHdrCtT :: .prod (.opt (.prod vpT ckaHdrCtT)) hsT :: Γ_tx1
  have hep := cEpMgmtE_any_cost_le (O' := OO_cka) (vpT := vpT) Δ qep hΔ (Γ' := Γ_tx0)
    (CryptoGames.SM.Engine.esG (.fst .v6)) (.fst .v0) (CryptoGames.SM.isSomeE (.snd (.snd .v0)))
  have hvs := vSendC_any_cost_le hk H hhk (Γ' := Γ_tx1) (CryptoGames.SM.Engine.esH (.fst .v7)) .v0
    (.fst .v1) (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt .v0) (.fst .v1)) (.fst (.snd .v1)) .none (.snd (.snd .v1))
  have hrec := cRecordE_any_cost_le (O' := OO_cka) (vpT := vpT) L Δ hΔ (Γ' := Γ_tx2) .v2 (.fst .v3) (.fst .v0)
    (.pair (.pair (.fst .v3) (.pair (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsEpoch .v2) (.fst .v3))
      (.add (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsIdx .v2) (.fst .v3)) (.nat 1))))
      (.pair (.fst (.snd .v3)) (.snd .v0))) (.bool false)
  have hdl := deliverEC_any_cost_le hk H L maxSkip cfg hhk (Γ' := Γ_dl) (.fst .v4) .v0
  have hij := injectEC_anyCfg_cost_le hk H L Δ qep C_inj hΔ cfg hcfg hhk (Γ' := Γ_ij) (.fst .v3) .v0
  have hca := corrAllowedChoiceE_cost_le (vpT := vpT) paper L (Γ' := Γ_cr)
    (CryptoGames.SM.Engine.esG (O' := OO_cka) (.fst .v2)) .v0
  have hac := cAfterCorrE_cost_le (O' := OO_cka) (vpT := vpT) L (Γ' := Γ_cr2)
    (CryptoGames.SM.Engine.esG (hsT := hsT) (.fst .v4)) .v2
  have hrv := hhk.reveal_le (Γ' := Γ_cr) (CryptoGames.SM.Engine.esH (.fst .v2))
    (CryptoGames.SM.Engine.esG (.fst .v2)) .v0
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v2))) .v0)
  have hdf := deliverForgeEC_anyCfg_cost_le hk H L Δ qep C_inj hΔ cfg hcfg hhk (Γ' := Γ_df) (.fst .v1) .v0
  simp only [esG_cost, esH_cost, pGet_cost, cGsSt_cost, cGsEpoch_cost, CryptoGames.SM.Engine.cGsIdx,
    isSomeE_cost, Expr.cost, dsl_cost, v0_cost, v1_cost, v2_cost, v3_cost, v4_cost, v6_cost,
    Expr.v7, bits_one, Nat.reduceAdd] at hep hvs hrec hdl hij hca hac hrv hdf
  dsimp only [bucketHandleC]
  simp only [CryptoGames.SM.orE, CryptoGames.SM.Engine.cGsIdx,
    CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.esMk, esG_cost, esH_cost, esAbort_cost,
    Comp.cost, Expr.cost, dsl_cost, v0_cost, v1_cost, v2_cost, v3_cost, v4_cost, v5_cost, v6_cost,
    Expr.v7, bits_zero, bits_one, Nat.reduceAdd]; omega

set_option linter.unusedSimpArgs false in
theorem bucketHandleC_excessUB_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sC : I'.smp.Samp → ℕ} {qC : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (paper : Bool) (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (Ho Hs Hr L Δ qep maxSkip : ℕ) (cfg : CryptoGames.SM.Engine.ConfigEC OO_cka)
    (hcfg : ∀ {Γ'} (e : Expr OO_cka Γ' .nat),
      exprExcessUB (ckaOpC B0) (cfg.injectFullE e) ≤ 4 * exprExcessUB (ckaOpC B0) e)
    (hhk : HooksExcessBounded B0 sC qC hk Ho Hs Hr) :
    compExcessUB (ckaOpC B0) sC qC (bucketHandleC paper hk L Δ qep maxSkip cfg) ≤
      8 * Ho + Hs + 3 * Hr + 600 * L + 35000 := by
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let esT := CryptoGames.SM.Engine.esTy vpT hsT; let qT := (CryptoGames.CKA.ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).Q
  let txQ : Ty S_cka := .prod .bool (.prod (.base .msg) (.opt (.base .ccoins)))
  let chQ : Ty S_cka := .prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .ccoins))))
  let dlQ : Ty S_cka := .prod .bool ckaHdrCtT; let dfQ : Ty S_cka := .prod .bool (.prod ckaHdrCtT ckaHdrCtT)
  let smqT : Ty S_cka := .sum (.sum (.sum (.sum txQ chQ) dlQ) dlQ) .bool
  let Γ0 : List (Ty S_cka) := .prod esT (.prod (.opt .nat) qT) :: [.prod esT (.opt .nat), qT]
  let Γ_df : List (Ty S_cka) := dfQ :: Γ0; let Γ_cr : List (Ty S_cka) := .bool :: smqT :: Γ0
  let Γ_ij : List (Ty S_cka) := dlQ :: .sum (.sum (.sum txQ chQ) dlQ) dlQ :: smqT :: Γ0
  let Γ_dl : List (Ty S_cka) := dlQ :: .sum (.sum txQ chQ) dlQ :: .sum (.sum (.sum txQ chQ) dlQ) dlQ :: smqT :: Γ0
  let Γ_tx0 : List (Ty S_cka) := txQ :: txQ :: .sum txQ chQ :: .sum (.sum txQ chQ) dlQ :: .sum (.sum (.sum txQ chQ) dlQ) dlQ :: smqT :: Γ0
  let Γ_tx1 : List (Ty S_cka) := CryptoGames.SM.Engine.cGsTy vpT :: Γ_tx0
  have hvs := vSendC_excessUB_le hk Ho Hs Hr hhk (Γ' := Γ_tx1) (CryptoGames.SM.Engine.esH (.fst .v7)) .v0
    (.fst .v1) (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt .v0) (.fst .v1)) (.fst (.snd .v1)) .none (.snd (.snd .v1))
  have hdl := deliverEC_any_excessUB_le hk Ho Hs Hr L maxSkip cfg hhk (Γ' := Γ_dl) (.fst .v4) .v0
  have hij := injectEC_anyCfg_excessUB_le hk Ho Hs Hr L Δ qep cfg hcfg hhk (Γ' := Γ_ij) (.fst .v3) .v0
  have hca := corrAllowedChoiceE_excessUB (vpT := vpT) B0 paper L (Γ' := Γ_cr)
    (CryptoGames.SM.Engine.esG (O' := OO_cka) (.fst .v2)) .v0
  have hrv := hhk.reveal_le (Γ' := Γ_cr) (CryptoGames.SM.Engine.esH (.fst .v2))
    (CryptoGames.SM.Engine.esG (.fst .v2)) .v0
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v2))) .v0)
  have hdf := deliverForgeEC_anyCfg_excessUB_le hk Ho Hs Hr L Δ qep cfg hcfg hhk (Γ' := Γ_df) (.fst .v1) .v0
  simp only [CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.cGsSt,
    CryptoGames.SM.pGet, exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3,
    exprExcessUB_v4, exprExcessUB_v7, exprExcessUB_var, exprExcessUB_none, exprExcessUB_ite,
    exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_letE,
    Nat.add_zero, Nat.zero_add, Nat.mul_zero] at hvs hdl hij hca hrv hdf
  dsimp only [bucketHandleC]
  simp only [CryptoGames.SM.Engine.cEpMgmtE, CryptoGames.SM.Engine.cRecordE,
    CryptoGames.SM.Engine.cAfterCorrE, CryptoGames.SM.Engine.cSafeChE, CryptoGames.SM.Engine.cLeakE,
    CryptoGames.SM.Engine.cCompInsertE, CryptoGames.SM.Engine.cCompSetE,
    CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH,
    CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.cGsMk, CryptoGames.SM.Engine.cGsSt,
    CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.cGsEpoch,
    CryptoGames.SM.Engine.cGsIdx, CryptoGames.SM.Engine.cGsTL, CryptoGames.SM.Engine.cGsTrans,
    CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.Engine.cGsComp, CryptoGames.SM.Engine.cGsMaxAcc,
    CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs, CryptoGames.SM.Engine.cRecPos,
    CryptoGames.SM.sendsInE, CryptoGames.SM.healedByE, CryptoGames.SM.maxOptE, CryptoGames.SM.maxN,
    CryptoGames.SM.leN, CryptoGames.SM.pSet, CryptoGames.SM.pGet, CryptoGames.SM.orE,
    CryptoGames.SM.isSomeE, CryptoGames.SM.boolEq,
    CryptoGames.SM.otherE, CryptoGames.SM.posSender, CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx,
    exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
    exprExcessUB_v5, exprExcessUB_v6, exprExcessUB_v7, exprExcessUB_var, exprExcessUB_unit,
    exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none, exprExcessUB_nil, exprExcessUB_add,
    exprExcessUB_modK, exprExcessUB_lt, exprExcessUB_eqN, exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite,
    exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_inl, exprExcessUB_inr,
    exprExcessUB_some, exprExcessUB_cons, exprExcessUB_caseOpt, exprExcessUB_letE,
    exprExcessUB_foldrB, exprExcessUB_tget, exprExcessUB_tset,
    compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt, compExcessUB_caseSum,
    Nat.add_zero, Nat.zero_add, Nat.mul_zero]; omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
theorem bucketHandleC_sizeW_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sS : I'.smp.Samp → ℕ} {qS : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (paper : Bool) (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (Ho Hs Hr L Δ qep maxSkip S_inj : ℕ) (hΔ : Δ ≤ 4) (cfg : CryptoGames.SM.Engine.ConfigEC OO_cka)
    (hcfg : ∀ {Γ'} (e : Expr OO_cka Γ' .nat),
      Bundles.exprSizeW (Bundles.ckaOpS B0) (cfg.injectFullE e) ≤
        4 * Bundles.exprSizeW (Bundles.ckaOpS B0) e + S_inj)
    (hhk : HooksSizeBounded B0 sS qS hk Ho Hs Hr) :
    Bundles.compSizeW (Bundles.ckaOpS B0) sS qS (bucketHandleC paper hk L Δ qep maxSkip cfg) ≤
      10 * Ho + 2 * Hs + 4 * Hr + 60 * bits L + 20 * bits qep + 10 * bits maxSkip + 8 * S_inj + 40000 := by
  have hc : Δ = 0 ∨ Δ = 1 ∨ Δ = 2 ∨ Δ = 3 ∨ Δ = 4 := by omega
  have hbΔ : bits Δ ≤ 4 := by rcases hc with rfl | rfl | rfl | rfl | rfl <;> decide
  have hb1Δ : bits (Δ + 1) ≤ 4 := by rcases hc with rfl | rfl | rfl | rfl | rfl <;> decide
  have hb2Δ : bits (2 + Δ) ≤ 4 := by rcases hc with rfl | rfl | rfl | rfl | rfl <;> decide
  have hqep1 := bits_succ_le qep
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let esT := CryptoGames.SM.Engine.esTy vpT hsT; let qT := (CryptoGames.CKA.ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).Q
  let txQ : Ty S_cka := .prod .bool (.prod (.base .msg) (.opt (.base .ccoins)))
  let chQ : Ty S_cka := .prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .ccoins))))
  let dlQ : Ty S_cka := .prod .bool ckaHdrCtT; let dfQ : Ty S_cka := .prod .bool (.prod ckaHdrCtT ckaHdrCtT)
  let smqT : Ty S_cka := .sum (.sum (.sum (.sum txQ chQ) dlQ) dlQ) .bool
  let Γ0 : List (Ty S_cka) := .prod esT (.prod (.opt .nat) qT) :: [.prod esT (.opt .nat), qT]
  let Γ_df : List (Ty S_cka) := dfQ :: Γ0; let Γ_cr : List (Ty S_cka) := .bool :: smqT :: Γ0
  let Γ_ij : List (Ty S_cka) := dlQ :: .sum (.sum (.sum txQ chQ) dlQ) dlQ :: smqT :: Γ0
  let Γ_dl : List (Ty S_cka) := dlQ :: .sum (.sum txQ chQ) dlQ :: .sum (.sum (.sum txQ chQ) dlQ) dlQ :: smqT :: Γ0
  let Γ_tx0 : List (Ty S_cka) := txQ :: txQ :: .sum txQ chQ :: .sum (.sum txQ chQ) dlQ :: .sum (.sum (.sum txQ chQ) dlQ) dlQ :: smqT :: Γ0
  let Γ_tx1 : List (Ty S_cka) := CryptoGames.SM.Engine.cGsTy vpT :: Γ_tx0
  have hvs := vSendC_sizeW_le hk Ho Hs Hr hhk (Γ' := Γ_tx1) (CryptoGames.SM.Engine.esH (.fst .v7)) .v0
    (.fst .v1) (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt .v0) (.fst .v1)) (.fst (.snd .v1)) .none (.snd (.snd .v1))
  have hdl := deliverEC_any_sizeW_le hk Ho Hs Hr L maxSkip cfg hhk (Γ' := Γ_dl) (.fst .v4) .v0
  have hij := injectEC_anyCfg_sizeW_le hk Ho Hs Hr L Δ qep S_inj hΔ cfg hcfg hhk (Γ' := Γ_ij) (.fst .v3) .v0
  have hca := corrAllowedChoiceE_sizeW_le (vpT := vpT) B0 paper L (Γ' := Γ_cr)
    (CryptoGames.SM.Engine.esG (O' := OO_cka) (.fst .v2)) .v0
  have hrv := hhk.reveal_le (Γ' := Γ_cr) (CryptoGames.SM.Engine.esH (.fst .v2))
    (CryptoGames.SM.Engine.esG (.fst .v2)) .v0
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v2))) .v0)
  have hdf := deliverForgeEC_anyCfg_sizeW_le hk Ho Hs Hr L Δ qep S_inj hΔ cfg hcfg hhk (Γ' := Γ_df) (.fst .v1) .v0
  simp only [CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.cGsSt,
    CryptoGames.SM.pGet, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4,
    exprSizeW_v7, exprSizeW_var, exprSizeW_none, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst,
    exprSizeW_snd, exprSizeW_letE, Nat.reduceAdd] at hvs hdl hij hca hrv hdf
  dsimp only [bucketHandleC]
  simp only [CryptoGames.SM.Engine.cEpMgmtE, CryptoGames.SM.Engine.cRecordE,
    CryptoGames.SM.Engine.cAfterCorrE, CryptoGames.SM.Engine.cSafeChE, CryptoGames.SM.Engine.cLeakE,
    CryptoGames.SM.Engine.cCompInsertE, CryptoGames.SM.Engine.cCompSetE,
    CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH,
    CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.cGsMk, CryptoGames.SM.Engine.cGsSt,
    CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.cGsEpoch,
    CryptoGames.SM.Engine.cGsIdx, CryptoGames.SM.Engine.cGsTL, CryptoGames.SM.Engine.cGsTrans,
    CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.Engine.cGsComp, CryptoGames.SM.Engine.cGsMaxAcc,
    CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs, CryptoGames.SM.Engine.cRecPos,
    CryptoGames.SM.sendsInE, CryptoGames.SM.healedByE, CryptoGames.SM.maxOptE, CryptoGames.SM.maxN,
    CryptoGames.SM.leN, CryptoGames.SM.pSet, CryptoGames.SM.pGet, CryptoGames.SM.orE,
    CryptoGames.SM.isSomeE, CryptoGames.SM.boolEq,
    CryptoGames.SM.otherE, CryptoGames.SM.posSender, CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4, exprSizeW_v5,
    exprSizeW_v6, exprSizeW_v7, exprSizeW_var, exprSizeW_unit, exprSizeW_bool, exprSizeW_nat,
    exprSizeW_none, exprSizeW_nil, exprSizeW_add, exprSizeW_sub, exprSizeW_modK, exprSizeW_lt,
    exprSizeW_eqN, exprSizeW_not, exprSizeW_and, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst,
    exprSizeW_snd, exprSizeW_inl, exprSizeW_inr, exprSizeW_some, exprSizeW_cons, exprSizeW_caseOpt,
    exprSizeW_caseSum, exprSizeW_letE, exprSizeW_foldrB, exprSizeW_tconst, exprSizeW_tget,
    exprSizeW_tset, compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt,
    compSizeW_caseSum, bits_zero, bits_one, bits_two, bits_three, bits_four, Nat.reduceAdd]; omega

private theorem bits_healEpoch_le (tL : Option ℕ) :
    bits (healEpoch tL) ≤ bits (tL.getD 0) + 2 := by
  cases tL with
  | none => simp [healEpoch]
  | some n =>
    dsimp only [healEpoch, Option.getD]
    rw [show n + 2 = (n + 1) + 1 from rfl]
    have h1 := bits_succ_le n; have h2 := bits_succ_le (n + 1); omega

private theorem bind_ret_bucketInit_cost_le {S' : Sig} {O' : Ops S'} {ι : Type}
    {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S' TSpec} {σ : Ty S'}
    (c : Comp O' I' [.unit] σ) :
    (Comp.bind c (Comp.ret (.pair .unit (.pair .v0 (.none (t := .nat)))))).cost ≤ c.cost + 8 := by
  simp only [Comp.cost, Expr.cost, v0_cost]; omega

private theorem bind_ret_bucketInit_excessUB_le {S' : Sig} {O' : Ops S'} {ι : Type}
    {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S' TSpec} {opC : O'.Op → ℕ}
    {sC : I'.smp.Samp → ℕ} {qC : I'.Tag → ℕ} {σ : Ty S'}
    (c : Comp O' I' [.unit] σ) :
    compExcessUB opC sC qC (Comp.bind c (Comp.ret (.pair .unit (.pair .v0 (.none (t := .nat)))))) ≤
      compExcessUB opC sC qC c := by
  simp only [compExcessUB_bind, compExcessUB_ret, exprExcessUB_pair, exprExcessUB_unit,
    exprExcessUB_v0, exprExcessUB_none, Nat.add_zero]; omega

private theorem bind_ret_bucketInit_sizeW_le {S' : Sig} {O' : Ops S'} {ι : Type}
    {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S' TSpec} {opS : O'.Op → ℕ}
    {sS : I'.smp.Samp → ℕ} {qS : I'.Tag → ℕ} {σ : Ty S'}
    (c : Comp O' I' [.unit] σ) :
    Bundles.compSizeW opS sS qS
      (Comp.bind c (Comp.ret (.pair .unit (.pair .v0 (.none (t := .nat)))))) ≤
      Bundles.compSizeW opS sS qS c + 10 := by
  simp only [compSizeW_bind, compSizeW_ret, exprSizeW_pair, exprSizeW_unit, exprSizeW_v0,
    exprSizeW_none]; omega

set_option linter.unusedSimpArgs false in
private theorem validGuessBucketParPaperE_cost_le {O' : Ops S_cka} (tL : Option ℕ) (par : Bool)
    {Γ'} (e : Expr O' Γ' .nat) :
    (CryptoGames.SM.Construction.validGuessBucketParPaperE 4 tL par e).cost ≤
      3 * e.cost + (2 * bits (tL.getD 0) + 80) := by
  have hb5 : bits 5 = 3 := rfl
  cases tL <;> cases par <;> ·
    simp only [CryptoGames.SM.Construction.validGuessBucketParPaperE, CryptoGames.SM.validGuessE,
      CryptoGames.SM.healedByE, CryptoGames.SM.optNatEqE, CryptoGames.SM.ltOptE,
      CryptoGames.SM.leN, CryptoGames.SM.maxN, CryptoGames.SM.boolEq,
      CryptoGames.SM.receiverOfE, CryptoGames.SM.senderOfE, CryptoGames.SM.Engine.optNatLit,
      Option.getD, Expr.cost, dsl_cost, v0_cost, v1_cost, bits_zero, bits_one, bits_two,
      bits_three, bits_four, hb5, Nat.reduceAdd]; omega

set_option linter.unusedSimpArgs false in
private theorem validGuessBucketParPaperE_excessUB (B0 : ℕ) (tL : Option ℕ) (par : Bool)
    {Γ'} (e : Expr OO_cka Γ' .nat) :
    exprExcessUB (ckaOpC B0) (CryptoGames.SM.Construction.validGuessBucketParPaperE 4 tL par e) ≤
      4 * exprExcessUB (ckaOpC B0) e := by
  cases tL <;> cases par <;> ·
    simp only [CryptoGames.SM.Construction.validGuessBucketParPaperE, CryptoGames.SM.validGuessE,
      CryptoGames.SM.healedByE, CryptoGames.SM.optNatEqE, CryptoGames.SM.ltOptE,
      CryptoGames.SM.leN, CryptoGames.SM.maxN, CryptoGames.SM.boolEq,
      CryptoGames.SM.receiverOfE, CryptoGames.SM.senderOfE, optNatLit_excessUB,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_var, exprExcessUB_bool, exprExcessUB_nat,
      exprExcessUB_add, exprExcessUB_modK, exprExcessUB_lt, exprExcessUB_eqN, exprExcessUB_not,
      exprExcessUB_and, exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd,
      exprExcessUB_caseOpt, exprExcessUB_letE, Nat.add_zero, Nat.zero_add, Nat.mul_zero]; omega

set_option linter.unusedSimpArgs false in
private theorem validGuessBucketParPaperE_sizeW_le (B0 : ℕ) (tL : Option ℕ) (par : Bool)
    {Γ'} (e : Expr OO_cka Γ' .nat) :
    Bundles.exprSizeW (Bundles.ckaOpS B0)
      (CryptoGames.SM.Construction.validGuessBucketParPaperE 4 tL par e) ≤
      4 * Bundles.exprSizeW (Bundles.ckaOpS B0) e + (4 * bits (tL.getD 0) + 150) := by
  have hb5 : bits 5 = 3 := rfl
  cases tL <;> cases par <;> ·
    simp only [CryptoGames.SM.Construction.validGuessBucketParPaperE, CryptoGames.SM.validGuessE,
      CryptoGames.SM.healedByE, CryptoGames.SM.optNatEqE, CryptoGames.SM.ltOptE,
      CryptoGames.SM.leN, CryptoGames.SM.maxN, CryptoGames.SM.boolEq,
      CryptoGames.SM.receiverOfE, CryptoGames.SM.senderOfE, CryptoGames.SM.Engine.optNatLit,
      Option.getD, exprSizeW_v0, exprSizeW_v1, exprSizeW_var, exprSizeW_bool, exprSizeW_nat,
      exprSizeW_none, exprSizeW_add, exprSizeW_modK, exprSizeW_lt, exprSizeW_eqN, exprSizeW_not,
      exprSizeW_and, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_some,
      exprSizeW_caseOpt, exprSizeW_letE, bits_zero, bits_one, bits_two, bits_three, bits_four,
      hb5, Nat.reduceAdd]; omega

set_option maxRecDepth 100000 in
private theorem bucketHandleC_compCostW_le_fig8AtomicStepBound {ι : Type}
    {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S_cka (unifSpec + TSpec)} {qC : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (paper : Bool) (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (q qep : ℕ) (tL : Option ℕ) (par : Bool) (htL : tL.getD 0 ≤ qep + 2)
    (hhkC : HooksCostBounded hk
      (30 * (q + 1) + 15 * bits qep + (q + 1) * (maxForwardJumps + 1) + 5000))
    (hhkE : HooksExcessBounded ((q + 1) * (maxForwardJumps + 1)) ckaSampC qC hk
      (30 * (q + 1) + 10000) 400000
      (20 * ((q + 1) * (maxForwardJumps + 1)) +
        3 * bits ((q + 1) * (maxForwardJumps + 1)) + 2710000)) :
    compCostW (ckaOpC ((q + 1) * (maxForwardJumps + 1))) ckaSampC qC
      (bucketHandleC paper hk (q + 1) (2 + 1) qep maxForwardJumps
        (CryptoGames.SM.Construction.bucketParPaperAuthCfgEC (3 + 1) tL par)) + 200000 ≤
      fig8AtomicStepBound q qep := by
  rw [show (2 : ℕ) + 1 = 3 from rfl, show (3 : ℕ) + 1 = 4 from rfl]
  let L := q + 1; let B := (q + 1) * (maxForwardJumps + 1)
  let H := 30 * L + 15 * bits qep + B + 5000
  let Ho := 30 * L + 10000; let Hs := 400000; let Hr := 20 * B + 3 * bits B + 2710000
  have hmfj : maxForwardJumps = 25000 := rfl
  have htL_bits := bits_le_bits_qep_add (x := tL.getD 0) (qep := qep) (by omega)
  have hbB := bits_le_add_one B
  have hC := bucketHandleC_cost_le paper hk H L 3 qep maxForwardJumps (2 * bits (tL.getD 0) + 80)
    (by omega) (CryptoGames.SM.Construction.bucketParPaperAuthCfgEC 4 tL par)
    (fun e => validGuessBucketParPaperE_cost_le tL par e) hhkC
  have hE := bucketHandleC_excessUB_le (B0 := B) (sC := ckaSampC) (qC := qC) paper hk Ho Hs Hr L 3
    qep maxForwardJumps (CryptoGames.SM.Construction.bucketParPaperAuthCfgEC 4 tL par)
    (fun e => validGuessBucketParPaperE_excessUB B tL par e) hhkE
  have hW := compCostW_le_cost_add_excessUB (ckaOpC B) ckaSampC qC
    (bucketHandleC paper hk L 3 qep maxForwardJumps
      (CryptoGames.SM.Construction.bucketParPaperAuthCfgEC 4 tL par))
  unfold fig8AtomicStepBound
  dsimp only [L, B, H, Ho, Hs, Hr] at hC hE hW hbB ⊢
  generalize bits ((q + 1) * (maxForwardJumps + 1)) = bB at hE hbB
  generalize (q + 1) * (maxForwardJumps + 1) = Bv at hC hE hW hbB ⊢
  generalize (q + 1) * (3 * bits qep + 60) = Lbq at ⊢
  omega

private theorem bucketHandleC_sizeW_le_ratchet {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {sS : I'.smp.Samp → ℕ} {qS : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (paper : Bool) (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (q qep : ℕ) (tL : Option ℕ) (par : Bool) (htL : tL.getD 0 ≤ qep + 2)
    (hqep : qep ≤ 4096 * q + 100000000)
    (hhk : HooksSizeBounded ((q + 1) * (maxForwardJumps + 1)) sS qS hk
      (30 * bits (ratchetCostBudget q qep) + 18000) 2000
      (5 * bits (ratchetCostBudget q qep) + 2000)) :
    Bundles.compSizeW (Bundles.ckaOpS ((q + 1) * (maxForwardJumps + 1))) sS qS
      (bucketHandleC paper hk (q + 1) (2 + 1) qep maxForwardJumps
        (CryptoGames.SM.Construction.bucketParPaperAuthCfgEC (3 + 1) tL par)) ≤
      500 * bits (ratchetCostBudget q qep) + 240000 := by
  rw [show (2 : ℕ) + 1 = 3 from rfl, show (3 : ℕ) + 1 = 4 from rfl]
  have hbL : bits (q + 1) ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbqep : bits qep ≤ bits (ratchetCostBudget q qep) := bits_qep_le_ratchetCostBudget hqep
  have hbm : bits maxForwardJumps ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (by unfold maxForwardJumps; omega)
  have hbtL : bits (tL.getD 0) ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hS := bucketHandleC_sizeW_le (B0 := (q + 1) * (maxForwardJumps + 1)) (sS := sS) (qS := qS)
    paper hk (30 * bits (ratchetCostBudget q qep) + 18000) 2000
    (5 * bits (ratchetCostBudget q qep) + 2000) (q + 1) 3 qep maxForwardJumps
    (4 * bits (tL.getD 0) + 150) (by omega)
    (CryptoGames.SM.Construction.bucketParPaperAuthCfgEC 4 tL par)
    (fun e => validGuessBucketParPaperE_sizeW_le _ tL par e) hhk
  generalize Bundles.compSizeW (Bundles.ckaOpS ((q + 1) * (maxForwardJumps + 1))) sS qS
    (bucketHandleC paper hk (q + 1) 3 qep maxForwardJumps
      (CryptoGames.SM.Construction.bucketParPaperAuthCfgEC 4 tL par)) = lhs at hS ⊢
  generalize bits (ratchetCostBudget q qep) = bR at hbL hbqep hbm hbtL hS ⊢
  generalize bits (q + 1) = bL at hbL hS
  generalize bits qep = bq at hbqep hS
  generalize bits maxForwardJumps = bm at hbm hS
  generalize bits (tL.getD 0) = btL at hbtL hS
  exact hS.trans (by omega)

set_option linter.unusedSimpArgs false in
private theorem hooksCKABucketParPaperC_costBounded (B : ℕ) (tL : Option ℕ) (par : Bool) :
    HooksCostBounded
      (CryptoGames.SM.Construction.hooksCKABucketParPaperC (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B 1 (3 + 1) tL par)
      (3 * bits (healEpoch tL) + 2 * bits (tL.getD 0) + (B + 1) + 1200) := by
  let base := hooksCKAC_costBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) B ⟨true, tL, 0⟩
  have hmH : (⟨true, tL, 0⟩ : CryptoGames.SM.Construction.Mode).tH = healEpoch tL := rfl
  have hmS : bits (⟨true, tL, 0⟩ : CryptoGames.SM.Construction.Mode).tStar = 1 := rfl
  refine ⟨fun h ctx p t γv σ r => ?_, fun h ctx p t γv σ tn => ?_,
    fun h ctx p t ss hdr m pair => ?_, fun h ctx p t rs hdr e rec_ => ?_,
    fun h ctx p old new => ?_, fun h ctx p vp => ?_⟩
  · exact (base.startSend_le h ctx p t γv σ r).trans (by rw [hmH, hmS]; omega)
  · have hb5 : bits 5 = 3 := rfl
    cases tL <;> cases par <;> ·
      dsimp only [CryptoGames.SM.Construction.hooksCKABucketParPaperC,
        CryptoGames.SM.Construction.ckaStartRecvBucketParPaperAnsE]
      refine (ret_pair_letE_cost_le_costUB _ _ _).trans ?_
      simp only [CryptoGames.SM.Construction.validGuessBucketParPaperE, CryptoGames.SM.validGuessE,
        CryptoGames.SM.healedByE, CryptoGames.SM.optNatEqE, CryptoGames.SM.ltOptE,
        CryptoGames.SM.leN, CryptoGames.SM.maxN, CryptoGames.SM.boolEq,
        CryptoGames.SM.receiverOfE, CryptoGames.SM.senderOfE, CryptoGames.SM.Engine.optNatLit,
        Option.getD, CryptoGames.CKA.ckaOps, Expr.cost, Expr.v0, Expr.v1, Expr.v2,
        dsl_cost, exprCostUB, bits_zero, bits_one, bits_two, bits_three, bits_four, hb5,
        Nat.reduceAdd]; omega
  · exact (base.fsSend_le h ctx p t ss hdr m pair).trans (by rw [hmH, hmS]; omega)
  · exact (base.fsRecv_le h ctx p t rs hdr e rec_).trans (by rw [hmH, hmS]; omega)
  · exact (base.commit_le h ctx p old new).trans (by rw [hmH, hmS]; omega)
  · exact (base.reveal_le h ctx p vp).trans (by rw [hmH, hmS]; omega)

set_option linter.unusedSimpArgs false in
private theorem hooksCKABucketParPaperC_excessBounded (B0 B : ℕ) (tL : Option ℕ) (par : Bool) :
    HooksExcessBounded B0 ckaSampC ckaQueryC
      (CryptoGames.SM.Construction.hooksCKABucketParPaperC (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B 1 (3 + 1) tL par)
      5000 380000 (20 * B0 + 3 * bits B + 2710000) := by
  let base := hooksCKAC_excessBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) B0 B ⟨true, tL, 0⟩
  refine ⟨fun h ctx p t γv σ r => (base.startSend_le h ctx p t γv σ r).trans (by omega),
    fun h ctx p t γv σ tn => ?_,
    fun h ctx p t ss hdr m pair => base.fsSend_le h ctx p t ss hdr m pair,
    fun h ctx p t rs hdr e rec_ => base.fsRecv_le h ctx p t rs hdr e rec_,
    fun h ctx p old new => (base.commit_le h ctx p old new).trans (by omega),
    fun h ctx p vp => (base.reveal_le h ctx p vp).trans (by omega)⟩
  cases tL <;> cases par <;> ·
    simp only [CryptoGames.SM.Construction.hooksCKABucketParPaperC,
      CryptoGames.SM.Construction.ckaStartRecvBucketParPaperAnsE,
      CryptoGames.SM.Construction.validGuessBucketParPaperE, CryptoGames.SM.validGuessE,
      CryptoGames.SM.healedByE, CryptoGames.SM.optNatEqE, CryptoGames.SM.ltOptE,
      CryptoGames.SM.leN, CryptoGames.SM.maxN, CryptoGames.SM.boolEq,
      CryptoGames.SM.receiverOfE, CryptoGames.SM.senderOfE, optNatLit_excessUB, ckaOpC,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_var,
      exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_add, exprExcessUB_modK, exprExcessUB_lt,
      exprExcessUB_eqN, exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite, exprExcessUB_pair,
      exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_none, exprExcessUB_some,
      exprExcessUB_caseOpt, exprExcessUB_letE, exprExcessUB_op, exprExcessUB_tget,
      compExcessUB_ret, Nat.reduceAdd, Nat.add_zero, Nat.zero_add, Nat.mul_zero]; omega

set_option linter.unusedSimpArgs false in
private theorem hooksCKABucketParPaperC_sizeBounded (B0 B : ℕ) (tL : Option ℕ) (par : Bool) :
    HooksSizeBounded B0 Bundles.ckaSampS Bundles.ckaQueryS
      (CryptoGames.SM.Construction.hooksCKABucketParPaperC (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B 1 (3 + 1) tL par)
      (5 * bits (healEpoch tL) + 5 * bits (tL.getD 0) + 6000) 2000
      (3 * bits B0 + 2 * bits B + 2000) := by
  let base := hooksCKAC_sizeBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) B0 B ⟨true, tL, 0⟩
  have hmH : (⟨true, tL, 0⟩ : CryptoGames.SM.Construction.Mode).tH = healEpoch tL := rfl
  have hmS : bits (⟨true, tL, 0⟩ : CryptoGames.SM.Construction.Mode).tStar = 1 := rfl
  refine ⟨fun h ctx p t γv σ r => (base.startSend_le h ctx p t γv σ r).trans (by rw [hmH, hmS]; omega),
    fun h ctx p t γv σ tn => ?_,
    fun h ctx p t ss hdr m pair => base.fsSend_le h ctx p t ss hdr m pair,
    fun h ctx p t rs hdr e rec_ => base.fsRecv_le h ctx p t rs hdr e rec_,
    fun h ctx p old new => (base.commit_le h ctx p old new).trans (by rw [hmH, hmS]; omega),
    fun h ctx p vp => (base.reveal_le h ctx p vp).trans (by rw [hmH, hmS]; omega)⟩
  have hb5 : bits 5 = 3 := rfl
  cases tL <;> cases par <;> ·
    simp only [CryptoGames.SM.Construction.hooksCKABucketParPaperC,
      CryptoGames.SM.Construction.ckaStartRecvBucketParPaperAnsE,
      CryptoGames.SM.Construction.validGuessBucketParPaperE, CryptoGames.SM.validGuessE,
      CryptoGames.SM.healedByE, CryptoGames.SM.optNatEqE, CryptoGames.SM.ltOptE,
      CryptoGames.SM.leN, CryptoGames.SM.maxN, CryptoGames.SM.boolEq,
      CryptoGames.SM.receiverOfE, CryptoGames.SM.senderOfE, CryptoGames.SM.Engine.optNatLit,
      Option.getD, Bundles.ckaOpS, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3,
      exprSizeW_var, exprSizeW_bool, exprSizeW_nat, exprSizeW_none, exprSizeW_add,
      exprSizeW_modK, exprSizeW_lt, exprSizeW_eqN, exprSizeW_not, exprSizeW_and, exprSizeW_ite,
      exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_some, exprSizeW_caseOpt,
      exprSizeW_letE, exprSizeW_op, exprSizeW_tget, compSizeW_ret,
      bits_zero, bits_one, bits_two, bits_three, bits_four, hb5, Nat.reduceAdd]; omega

private theorem redCKAAuthDFBucketCommon_parts_le (paper : Bool) (finMode : Fin 3) (B0 q qep : ℕ)
    (tL : Option ℕ) (par : Bool) (hB0 : B0 = (q + 1) * (maxForwardJumps + 1))
    (htL : tL.getD 0 ≤ qep + 2) :
    let initC := Comp.bind (Γ := [.unit])
      (CryptoGames.SM.Construction.initCKAEStateC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) ⟨true, tL, 0⟩ (.bool false))
      (Comp.ret (.pair .unit (.pair .v0 (.none (t := .nat)))))
    let hk := CryptoGames.SM.Construction.hooksCKABucketParPaperC (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) B0 1 (3 + 1) tL par
    let finC := bucketFinishModeC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE)
      (I' := CryptoGames.CKA.ckaIface KC Γ CCoins T I KR RSt K SS RS M E
        sampKR sampKC sampCCoins sampI sampK)
      (vpT := @CryptoGames.SM.Construction.ckaVpTy KC Γ CCoins T I KR RSt K SS RS M E)
      (hsT := @CryptoGames.SM.Construction.ckaHsTy KC Γ CCoins T I KR RSt K SS RS M E)
      finMode (q + 1) (2 + 1) tL
    compCostW (ckaOpC B0) ckaSampC ckaQueryC initC +
      compCostW (ckaOpC B0) ckaSampC ckaQueryC finC + 100000 ≤ fig8AtomicStepBound q qep ∧
    compCostW (ckaOpC B0) ckaSampC ckaQueryC
      (bucketHandleC paper hk (q + 1) (2 + 1) qep maxForwardJumps
        (CryptoGames.SM.Construction.bucketParPaperAuthCfgEC (3 + 1) tL par)) + 200000 ≤
      fig8AtomicStepBound q qep := by
  subst hB0
  intro initC hk finC
  have htL_bits := bits_le_bits_qep_add (x := tL.getD 0) (qep := qep) (by omega)
  have htH_bits := bits_healEpoch_le tL
  constructor
  · let e0 := CryptoGames.SM.Construction.initCKAEStateC (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) (Γ' := [.unit]) ⟨true, tL, 0⟩ (.bool false)
    have hiC := (bind_ret_bucketInit_cost_le e0).trans
      (Nat.add_le_add_right (initCKAEStateC_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
        (Γ' := [.unit]) ⟨true, tL, 0⟩ (.bool false)) 8)
    have hiE := (bind_ret_bucketInit_excessUB_le
      (opC := ckaOpC ((q + 1) * (maxForwardJumps + 1))) (sC := ckaSampC)
      (qC := ckaQueryC) e0).trans (initCKAEStateC_excessUB_le (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) ((q + 1) * (maxForwardJumps + 1))
        ⟨true, tL, 0⟩ (.bool (Γ := [.unit]) false))
    have hiW := compCostW_le_cost_add_excessUB (ckaOpC ((q + 1) * (maxForwardJumps + 1)))
      ckaSampC ckaQueryC initC
    have hfC := bucketFinishModeC_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE)
      (I' := CryptoGames.CKA.ckaIface KC Γ CCoins T I KR RSt K SS
        RS M E sampKR sampKC sampCCoins sampI sampK)
      (vpT := @CryptoGames.SM.Construction.ckaVpTy KC Γ CCoins T I KR RSt K SS RS M E)
      (hsT := @CryptoGames.SM.Construction.ckaHsTy KC Γ CCoins T I KR RSt K SS RS M E)
      finMode (q + 1) (2 + 1) (by omega) tL
    have hfE := bucketFinishModeC_excessUB_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE)
      (I' := CryptoGames.CKA.ckaIface KC Γ CCoins T I KR RSt K SS
        RS M E sampKR sampKC sampCCoins sampI sampK)
      ((q + 1) * (maxForwardJumps + 1)) ckaSampC ckaQueryC
      (vpT := @CryptoGames.SM.Construction.ckaVpTy KC Γ CCoins T I KR RSt K SS RS M E)
      (hsT := @CryptoGames.SM.Construction.ckaHsTy KC Γ CCoins T I KR RSt K SS RS M E)
      finMode (q + 1) (2 + 1) tL
    have hfW := compCostW_le_cost_add_excessUB (ckaOpC ((q + 1) * (maxForwardJumps + 1)))
      ckaSampC ckaQueryC finC
    simp only [Expr.cost, exprExcessUB_bool, Nat.reduceAdd] at hiC hiE
    unfold fig8AtomicStepBound
    dsimp only [initC, finC, e0] at hiC hiE hiW hfC hfE hfW ⊢
    omega
  · refine bucketHandleC_compCostW_le_fig8AtomicStepBound paper hk q qep tL par htL ?_ ?_
    · exact (hooksCKABucketParPaperC_costBounded _ tL par).mono (by omega)
    · exact (hooksCKABucketParPaperC_excessBounded _ _ tL par).mono (by omega) (by omega) (by omega)

private theorem redCKAAuthDFBucketCommon_size_le (paper : Bool) (finMode : Fin 3) (B0 q qep : ℕ)
    (tL : Option ℕ) (par : Bool) (hB0 : B0 = (q + 1) * (maxForwardJumps + 1))
    (htL : tL.getD 0 ≤ qep + 2) (hqep : qep ≤ 4096 * q + 100000000) :
    let initC := Comp.bind (Γ := [.unit])
      (CryptoGames.SM.Construction.initCKAEStateC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) ⟨true, tL, 0⟩ (.bool false))
      (Comp.ret (.pair .unit (.pair .v0 (.none (t := .nat)))))
    let hk := CryptoGames.SM.Construction.hooksCKABucketParPaperC (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) B0 1 (3 + 1) tL par
    let finC := bucketFinishModeC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE)
      (I' := CryptoGames.CKA.ckaIface KC Γ CCoins T I KR RSt K SS RS M E
        sampKR sampKC sampCCoins sampI sampK)
      (vpT := @CryptoGames.SM.Construction.ckaVpTy KC Γ CCoins T I KR RSt K SS RS M E)
      (hsT := @CryptoGames.SM.Construction.ckaHsTy KC Γ CCoins T I KR RSt K SS RS M E)
      finMode (q + 1) (2 + 1) tL
    Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS initC +
      Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS
        (bucketHandleC paper hk (q + 1) (2 + 1) qep maxForwardJumps
          (CryptoGames.SM.Construction.bucketParPaperAuthCfgEC (3 + 1) tL par)) +
      Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS finC + 520 ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep) := by
  subst hB0
  intro initC hk finC
  have hbL : bits (q + 1) ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbtL : bits (tL.getD 0) ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbtH : bits (healEpoch tL) ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (by cases tL <;> (simp [healEpoch] at htL ⊢; try omega))
  have hbB : bits ((q + 1) * (maxForwardJumps + 1)) ≤ bits (ratchetCostBudget q qep) :=
    bits_B0_le_ratchetCostBudget q qep
  have hi : Bundles.compSizeW (Bundles.ckaOpS ((q + 1) * (maxForwardJumps + 1)))
      Bundles.ckaSampS Bundles.ckaQueryS initC ≤ 9000 := by
    refine (bind_ret_bucketInit_sizeW_le _).trans ?_
    have h0 := initCKAEStateC_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) (Γ' := [.unit])
      ((q + 1) * (maxForwardJumps + 1)) ⟨true, tL, 0⟩ (.bool false)
    simp only [exprSizeW_bool] at h0; omega
  have hh : Bundles.compSizeW (Bundles.ckaOpS ((q + 1) * (maxForwardJumps + 1)))
      Bundles.ckaSampS Bundles.ckaQueryS
      (bucketHandleC paper hk (q + 1) (2 + 1) qep maxForwardJumps
        (CryptoGames.SM.Construction.bucketParPaperAuthCfgEC (3 + 1) tL par)) ≤
      500 * bits (ratchetCostBudget q qep) + 240000 :=
    bucketHandleC_sizeW_le_ratchet paper hk q qep tL par htL hqep
      ((hooksCKABucketParPaperC_sizeBounded _ _ tL par).mono
        (by generalize bits (ratchetCostBudget q qep) = bR at hbtH hbtL ⊢; omega) le_rfl
        (by generalize bits (ratchetCostBudget q qep) = bR at hbB ⊢
            generalize (q + 1) * (maxForwardJumps + 1) = B at hbB ⊢; omega))
  have hf : Bundles.compSizeW (Bundles.ckaOpS ((q + 1) * (maxForwardJumps + 1)))
      Bundles.ckaSampS Bundles.ckaQueryS finC ≤
      18 * bits (ratchetCostBudget q qep) + 700 := by
    have h0 := bucketFinishModeC_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE)
      (I' := CryptoGames.CKA.ckaIface KC Γ CCoins T I KR RSt K SS
        RS M E sampKR sampKC sampCCoins sampI sampK)
      ((q + 1) * (maxForwardJumps + 1)) Bundles.ckaSampS Bundles.ckaQueryS
      (vpT := @CryptoGames.SM.Construction.ckaVpTy KC Γ CCoins T I KR RSt K SS RS M E)
      (hsT := @CryptoGames.SM.Construction.ckaHsTy KC Γ CCoins T I KR RSt K SS RS M E)
      finMode (q + 1) (2 + 1) (by omega) tL
    dsimp only [finC] at h0 ⊢
    generalize bits (ratchetCostBudget q qep) = bR at hbL hbtL ⊢; omega
  refine size_le_ratchetSizeBudget (C₀ := 300000) (C₁ := 1100) (by decide) (by decide) ?_
  generalize bits (ratchetCostBudget q qep) = bR at hi hh hf ⊢; omega

private theorem redCKAAuthDFBucketProg_parts_le (B0 q qep : ℕ) (tL : Option ℕ) (par : Bool)
    (hB0 : B0 = (q + 1) * (maxForwardJumps + 1)) (htL : tL.getD 0 ≤ qep + 2) :
    let P := CryptoGames.SM.Construction.redCKAAuthDFBucketProg
      (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) (q + 1) B0 1 qep maxForwardJumps tL par
    compCostW (ckaOpC B0) ckaSampC ckaQueryC P.init +
      compCostW (ckaOpC B0) ckaSampC ckaQueryC P.finish + 100000 ≤ fig8AtomicStepBound q qep ∧
    compCostW (ckaOpC B0) ckaSampC ckaQueryC P.handle + 200000 ≤ fig8AtomicStepBound q qep :=
  redCKAAuthDFBucketCommon_parts_le false ⟨0, by decide⟩ B0 q qep tL par hB0 htL

private theorem redCKAAuthDFBucketProg_size_le (B0 q qep : ℕ) (tL : Option ℕ) (par : Bool)
    (hB0 : B0 = (q + 1) * (maxForwardJumps + 1)) (htL : tL.getD 0 ≤ qep + 2)
    (hqep : qep ≤ 4096 * q + 100000000) :
    let P := CryptoGames.SM.Construction.redCKAAuthDFBucketProg
      (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) (q + 1) B0 1 qep maxForwardJumps tL par
    Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS P.init +
      Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS P.handle +
      Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS P.finish + 520 ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep) :=
  redCKAAuthDFBucketCommon_size_le false ⟨0, by decide⟩ B0 q qep tL par hB0 htL hqep

theorem redCKAAuthDFPaperBucketProg_parts_le (B0 q qep : ℕ) (tL : Option ℕ) (par : Bool)
    (hB0 : B0 = (q + 1) * (maxForwardJumps + 1)) (htL : tL.getD 0 ≤ qep + 2) :
    let P := CryptoGames.SM.Construction.redCKAAuthDFPaperBucketProg
      (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) (q + 1) B0 1 qep maxForwardJumps tL par
    compCostW (ckaOpC B0) ckaSampC ckaQueryC P.init +
      compCostW (ckaOpC B0) ckaSampC ckaQueryC P.finish + 100000 ≤ fig8AtomicStepBound q qep ∧
    compCostW (ckaOpC B0) ckaSampC ckaQueryC P.handle + 200000 ≤ fig8AtomicStepBound q qep :=
  redCKAAuthDFBucketCommon_parts_le true ⟨0, by decide⟩ B0 q qep tL par hB0 htL

theorem redCKAAuthDFPaperBucketProg_size_le (B0 q qep : ℕ) (tL : Option ℕ) (par : Bool)
    (hB0 : B0 = (q + 1) * (maxForwardJumps + 1)) (htL : tL.getD 0 ≤ qep + 2)
    (hqep : qep ≤ 4096 * q + 100000000) :
    let P := CryptoGames.SM.Construction.redCKAAuthDFPaperBucketProg
      (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) (q + 1) B0 1 qep maxForwardJumps tL par
    Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS P.init +
      Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS P.handle +
      Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS P.finish + 520 ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep) :=
  redCKAAuthDFBucketCommon_size_le true ⟨0, by decide⟩ B0 q qep tL par hB0 htL hqep

set_option linter.unusedSimpArgs false in
private theorem hooksPRNGBucketParPaperC_costBounded (L B qep : ℕ) (tL : Option ℕ)
    (par : Bool) (t : ℕ) :
    HooksCostBounded
      (CryptoGames.SM.Construction.hooksPRNGBucketParPaperC (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B (3 + 1) qep tL par t)
      (20 * L + 2 * bits (qep + 1) + 6 * bits (healEpoch tL) + 4 * bits (tL.getD 0) +
        2 * bits t + (B + 1) + 3500) where
  startSend_le h ctx p tE γv σ r := by
    have hb5 : bits 5 = 3 := rfl
    cases tL <;> cases par <;> ·
      dsimp only [CryptoGames.SM.Construction.hooksPRNGBucketParPaperC,
        CryptoGames.SM.Construction.prngBucketStartSendC]
      refine (cost_bind_ret_le_costUB _ _).trans ?_
      simp only [CryptoGames.SM.Construction.rootPRNGBucketHybridC,
        CryptoGames.SM.Construction.postLeakBucketE, CryptoGames.SM.Construction.resolveCorrRootE,
        CryptoGames.SM.Construction.lookupPRNGBucketFC, CryptoGames.SM.Construction.tableLookupE,
        CryptoGames.SM.Construction.prngProcessCorrC, CryptoGames.SM.Construction.prngBucketHsCache,
        CryptoGames.SM.Construction.prngBucketHsFTbl, CryptoGames.SM.Construction.prngBucketHsCorrRoot,
        CryptoGames.SM.Construction.prngBucketHsLc, CryptoGames.SM.Construction.prngBucketHsSetLc,
        CryptoGames.SM.Construction.prngBucketHsSetCache, CryptoGames.SM.Construction.prngBucketHsSetFTblAt,
        CryptoGames.SM.Construction.prngBucketHsSetCorrRoot, CryptoGames.SM.orE, CryptoGames.SM.isSomeE,
        CryptoGames.SM.Construction.validGuessBucketParPaperE, CryptoGames.SM.validGuessE,
        CryptoGames.SM.healedByE, CryptoGames.SM.optNatEqE, CryptoGames.SM.leN, CryptoGames.SM.maxN,
        CryptoGames.SM.boolEq, CryptoGames.SM.receiverOfE, CryptoGames.SM.senderOfE,
        healEpoch, bits_two, bits_three, bits_four, hb5,
        CryptoGames.SM.ltOptE, CryptoGames.SM.Engine.cGsTL, CryptoGames.SM.Engine.optNatLit, Option.getD,
        CryptoGames.PRFPRNG.prngIface, CryptoGames.PRFPRNG.prngSamplers, CryptoGames.PRFPRNG.prngOps,
        CryptoGames.CKA.ckaSamplers, CryptoGames.CKA.ckaOps,
        Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5,
        bits_zero, bits_one, dsl_cost, compCostUB, exprCostUB, Nat.reduceAdd]; omega
  startRecv_le h ctx p tE γv σ tn := by
    have hb5 : bits 5 = 3 := rfl
    cases tL <;> cases par <;> ·
      dsimp only [CryptoGames.SM.Construction.hooksPRNGBucketParPaperC,
        CryptoGames.SM.Construction.prngBucketStartRecvC]
      refine (cost_bind_ret_le_costUB _ _).trans ?_
      simp only [CryptoGames.SM.Construction.lookupPRNGBucketFC,
        CryptoGames.SM.Construction.postLeakBucketE, CryptoGames.SM.Construction.resolveCorrRootE,
        CryptoGames.SM.Construction.tableLookupE, CryptoGames.SM.Construction.prngBucketHsCache,
        CryptoGames.SM.Construction.prngBucketHsFTbl, CryptoGames.SM.Construction.prngBucketHsCorrRoot,
        CryptoGames.SM.Construction.prngBucketHsLc,
        CryptoGames.SM.Construction.prngBucketHsSetFTblAt, CryptoGames.SM.orE, CryptoGames.SM.isSomeE,
        CryptoGames.SM.Engine.cGsTL,
        CryptoGames.SM.Construction.validGuessBucketParPaperE, CryptoGames.SM.validGuessE,
        CryptoGames.SM.healedByE, CryptoGames.SM.optNatEqE, CryptoGames.SM.ltOptE,
        CryptoGames.SM.leN, CryptoGames.SM.maxN, CryptoGames.SM.boolEq,
        CryptoGames.SM.receiverOfE, CryptoGames.SM.senderOfE, CryptoGames.SM.Engine.optNatLit,
        healEpoch, Option.getD, CryptoGames.PRFPRNG.prngIface, CryptoGames.PRFPRNG.prngSamplers,
        CryptoGames.PRFPRNG.prngOps, CryptoGames.CKA.ckaSamplers, CryptoGames.CKA.ckaOps,
        Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, dsl_cost, compCostUB, exprCostUB,
        bits_zero, bits_one, bits_two, bits_three, bits_four, hb5, Nat.reduceAdd]; omega
  fsSend_le h ctx p tE ss hdr m pair := by
    simp only [CryptoGames.SM.Construction.hooksPRNGBucketParPaperC,
      CryptoGames.SM.Construction.prngBucketFsSendC, CryptoGames.PRFPRNG.prngOps,
      CryptoGames.CKA.ckaOps, Comp.cost, Expr.cost]; omega
  fsRecv_le h ctx p tE rs hdr e rec_ := by
    have hB := bits_le_succ B
    simp only [CryptoGames.SM.Construction.hooksPRNGBucketParPaperC,
      CryptoGames.SM.Construction.prngBucketFsRecvC, CryptoGames.PRFPRNG.prngOps,
      CryptoGames.CKA.ckaOps, Comp.cost, Expr.cost]; omega
  commit_le h ctx p old new := by
    simp only [CryptoGames.SM.Construction.hooksPRNGBucketParPaperC,
      CryptoGames.SM.Construction.prngBucketCommitC, Comp.cost, Expr.cost]; omega
  reveal_le h ctx p vp := by
    cases tL <;> ·
      dsimp only [CryptoGames.SM.Construction.hooksPRNGBucketParPaperC,
        CryptoGames.SM.Construction.prngBucketRevealC]
      refine (cost_bind_ret_le_costUB _ _).trans ?_
      simp only [CryptoGames.SM.Construction.postLeakBucketE,
        CryptoGames.SM.Construction.resolveCorrRootE,
        CryptoGames.SM.Construction.prngBucketHsCorrRoot,
        CryptoGames.SM.Construction.prngBucketHsSetCorrRoot,
        CryptoGames.SM.Construction.prngBucketHsLc, CryptoGames.SM.Construction.prngBucketHsSetLc,
        CryptoGames.SM.Construction.prngBucketHsCache,
        CryptoGames.SM.Construction.prngBucketHsFTbl,
        CryptoGames.SM.isSomeE, CryptoGames.SM.maxN, CryptoGames.SM.leN, CryptoGames.SM.ltOptE,
        CryptoGames.SM.Engine.cGsEpoch, CryptoGames.SM.Engine.cGsTL,
        CryptoGames.SM.Engine.optNatLit, healEpoch, Option.getD,
        CryptoGames.PRFPRNG.prngIface, CryptoGames.PRFPRNG.prngSamplers,
        CryptoGames.PRFPRNG.prngOps, CryptoGames.CKA.ckaSamplers, CryptoGames.CKA.ckaOps,
        CryptoGames.SM.Engine.realPartyE, CryptoGames.SM.Engine.vpMk,
        CryptoGames.SM.Engine.vpId, CryptoGames.SM.Engine.vpRoot, CryptoGames.SM.Engine.vpVS,
        CryptoGames.SM.Engine.vpVR, CryptoGames.SM.Engine.vpΓ, CryptoGames.SM.Engine.vpTcur,
        CryptoGames.SM.Engine.vpTcurNat, Expr.cost, Expr.v0, Expr.v1, Expr.v2,
        bits_zero, bits_one, dsl_cost, compCostUB, exprCostUB, Nat.reduceAdd]; omega

set_option linter.unusedSimpArgs false in
private theorem hooksPRNGBucketParPaperC_excessBounded (B0 L B qep : ℕ) (tL : Option ℕ)
    (par : Bool) (t : ℕ) :
    HooksExcessBounded B0 ckaSampC prngQueryC
      (CryptoGames.SM.Construction.hooksPRNGBucketParPaperC (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B (3 + 1) qep tL par t)
      (15 * L + 8000) 380000 (20 * B0 + 3 * bits B + 2710000) where
  startSend_le h ctx p tE γv σ r := by
    cases tL <;> cases par <;> ·
      simp only [CryptoGames.SM.Construction.hooksPRNGBucketParPaperC,
        CryptoGames.SM.Construction.prngBucketStartSendC,
        CryptoGames.SM.Construction.rootPRNGBucketHybridC,
        CryptoGames.SM.Construction.postLeakBucketE, CryptoGames.SM.Construction.resolveCorrRootE,
        CryptoGames.SM.Construction.lookupPRNGBucketFC, CryptoGames.SM.Construction.tableLookupE,
        CryptoGames.SM.Construction.prngProcessCorrC, CryptoGames.SM.Construction.prngBucketHsCache,
        CryptoGames.SM.Construction.prngBucketHsFTbl, CryptoGames.SM.Construction.prngBucketHsCorrRoot,
        CryptoGames.SM.Construction.prngBucketHsLc, CryptoGames.SM.Construction.prngBucketHsSetLc,
        CryptoGames.SM.Construction.prngBucketHsSetCache, CryptoGames.SM.Construction.prngBucketHsSetFTblAt,
        CryptoGames.SM.Construction.prngBucketHsSetCorrRoot, CryptoGames.SM.orE, CryptoGames.SM.isSomeE,
        CryptoGames.SM.Construction.validGuessBucketParPaperE, CryptoGames.SM.validGuessE,
        CryptoGames.SM.healedByE, CryptoGames.SM.optNatEqE, CryptoGames.SM.leN, CryptoGames.SM.maxN,
        CryptoGames.SM.boolEq, CryptoGames.SM.receiverOfE, CryptoGames.SM.senderOfE,
        CryptoGames.SM.ltOptE, CryptoGames.SM.Engine.cGsTL, optNatLit_excessUB,
        ckaOpC, ckaSampC, prngQueryC,
        exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
        exprExcessUB_v5, exprExcessUB_var, exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat,
        exprExcessUB_none, exprExcessUB_add, exprExcessUB_sub, exprExcessUB_modK, exprExcessUB_lt, exprExcessUB_eqN, exprExcessUB_not,
      exprExcessUB_and, exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd,
      exprExcessUB_some, exprExcessUB_cons, exprExcessUB_caseOpt, exprExcessUB_letE, exprExcessUB_op,
      exprExcessUB_foldrB, exprExcessUB_tget, exprExcessUB_tset, compExcessUB_ret, compExcessUB_bind,
      compExcessUB_ite, compExcessUB_caseOpt, compExcessUB_sample, compExcessUB_query,
      Nat.reduceAdd, Nat.add_zero, Nat.zero_add, Nat.mul_zero]; omega
  startRecv_le h ctx p tE γv σ tn := by
    cases tL <;> cases par <;> ·
      simp only [CryptoGames.SM.Construction.hooksPRNGBucketParPaperC,
        CryptoGames.SM.Construction.prngBucketStartRecvC,
        CryptoGames.SM.Construction.postLeakBucketE, CryptoGames.SM.Construction.resolveCorrRootE,
        CryptoGames.SM.Construction.lookupPRNGBucketFC, CryptoGames.SM.Construction.tableLookupE,
        CryptoGames.SM.Construction.prngBucketHsCache, CryptoGames.SM.Construction.prngBucketHsFTbl,
        CryptoGames.SM.Construction.prngBucketHsCorrRoot, CryptoGames.SM.Construction.prngBucketHsLc,
        CryptoGames.SM.Construction.prngBucketHsSetFTblAt, CryptoGames.SM.orE, CryptoGames.SM.isSomeE,
        CryptoGames.SM.Engine.cGsTL,
        CryptoGames.SM.Construction.validGuessBucketParPaperE, CryptoGames.SM.validGuessE,
        CryptoGames.SM.healedByE, CryptoGames.SM.optNatEqE, CryptoGames.SM.ltOptE,
        CryptoGames.SM.leN, CryptoGames.SM.maxN, CryptoGames.SM.boolEq,
        CryptoGames.SM.receiverOfE, CryptoGames.SM.senderOfE, optNatLit_excessUB,
        ckaOpC, ckaSampC, prngQueryC,
        exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
        exprExcessUB_var, exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none,
        exprExcessUB_add, exprExcessUB_sub, exprExcessUB_modK, exprExcessUB_lt, exprExcessUB_eqN,
        exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst,
        exprExcessUB_snd, exprExcessUB_some, exprExcessUB_cons, exprExcessUB_caseOpt,
        exprExcessUB_letE, exprExcessUB_op, exprExcessUB_foldrB, exprExcessUB_tget, exprExcessUB_tset,
        compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt,
        compExcessUB_sample, compExcessUB_query, Nat.reduceAdd, Nat.add_zero, Nat.zero_add,
        Nat.mul_zero]; omega
  fsSend_le h ctx p tE ss hdr m pair := by
    simp only [CryptoGames.SM.Construction.hooksPRNGBucketParPaperC,
      CryptoGames.SM.Construction.prngBucketFsSendC, ckaOpC,
      exprExcessUB_pair, exprExcessUB_some, exprExcessUB_op, compExcessUB_ret]; omega
  fsRecv_le h ctx p tE rs hdr e rec_ := by
    simp only [CryptoGames.SM.Construction.hooksPRNGBucketParPaperC,
      CryptoGames.SM.Construction.prngBucketFsRecvC, ckaOpC,
      exprExcessUB_pair, exprExcessUB_some, exprExcessUB_op, compExcessUB_ret]; omega
  commit_le h ctx p old new := by
    simp only [CryptoGames.SM.Construction.hooksPRNGBucketParPaperC,
      CryptoGames.SM.Construction.prngBucketCommitC,
      exprExcessUB_pair, exprExcessUB_some, compExcessUB_ret]; omega
  reveal_le h ctx p vp := by
    simp only [CryptoGames.SM.Construction.hooksPRNGBucketParPaperC,
      CryptoGames.SM.Construction.prngBucketRevealC,
      CryptoGames.SM.Construction.postLeakBucketE, CryptoGames.SM.Construction.resolveCorrRootE,
      CryptoGames.SM.Construction.prngBucketHsCorrRoot,
      CryptoGames.SM.Construction.prngBucketHsSetCorrRoot,
      CryptoGames.SM.Construction.prngBucketHsLc, CryptoGames.SM.Construction.prngBucketHsSetLc,
      CryptoGames.SM.Construction.prngBucketHsCache, CryptoGames.SM.Construction.prngBucketHsFTbl,
      CryptoGames.SM.isSomeE, CryptoGames.SM.maxN, CryptoGames.SM.leN, CryptoGames.SM.ltOptE,
      CryptoGames.SM.Engine.cGsEpoch, CryptoGames.SM.Engine.cGsTL, optNatLit_excessUB,
      ckaOpC, ckaSampC, prngQueryC,
      CryptoGames.SM.Engine.realPartyE, CryptoGames.SM.Engine.vpMk, CryptoGames.SM.Engine.vpId,
      CryptoGames.SM.Engine.vpRoot, CryptoGames.SM.Engine.vpVS, CryptoGames.SM.Engine.vpVR,
      CryptoGames.SM.Engine.vpΓ, CryptoGames.SM.Engine.vpTcur, CryptoGames.SM.Engine.vpTcurNat,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_var, exprExcessUB_unit,
      exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_lt, exprExcessUB_eqN, exprExcessUB_not,
      exprExcessUB_and, exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd,
      exprExcessUB_none, exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_letE,
      compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt,
      compExcessUB_query, Nat.reduceAdd, Nat.add_zero, Nat.zero_add, Nat.mul_zero]; omega

set_option linter.unusedSimpArgs false in
private theorem hooksPRNGBucketParPaperC_sizeBounded (B0 L B qep : ℕ) (tL : Option ℕ)
    (par : Bool) (t : ℕ) :
    HooksSizeBounded B0 Bundles.ckaSampS Bundles.ckaQueryS
      (CryptoGames.SM.Construction.hooksPRNGBucketParPaperC (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B (3 + 1) qep tL par t)
      (bits L + 8 * bits (healEpoch tL) + 5 * bits t + 5 * bits (tL.getD 0) +
        2 * bits (qep + 1) + 17900) 2000 (3 * bits B0 + 2 * bits B + 2000) where
  startSend_le h ctx p tE γv σ r := by
    have hb5 : bits 5 = 3 := rfl
    cases tL <;> cases par <;> ·
      simp only [CryptoGames.SM.Construction.hooksPRNGBucketParPaperC,
        CryptoGames.SM.Construction.prngBucketStartSendC,
        CryptoGames.SM.Construction.rootPRNGBucketHybridC,
        CryptoGames.SM.Construction.postLeakBucketE, CryptoGames.SM.Construction.resolveCorrRootE,
        CryptoGames.SM.Construction.lookupPRNGBucketFC, CryptoGames.SM.Construction.tableLookupE,
        CryptoGames.SM.Construction.prngProcessCorrC, CryptoGames.SM.Construction.prngBucketHsCache,
        CryptoGames.SM.Construction.prngBucketHsFTbl, CryptoGames.SM.Construction.prngBucketHsCorrRoot,
        CryptoGames.SM.Construction.prngBucketHsLc, CryptoGames.SM.Construction.prngBucketHsSetLc,
        CryptoGames.SM.Construction.prngBucketHsSetCache, CryptoGames.SM.Construction.prngBucketHsSetFTblAt,
        CryptoGames.SM.Construction.prngBucketHsSetCorrRoot, CryptoGames.SM.orE, CryptoGames.SM.isSomeE,
        CryptoGames.SM.Construction.validGuessBucketParPaperE, CryptoGames.SM.validGuessE,
        CryptoGames.SM.healedByE, CryptoGames.SM.optNatEqE, CryptoGames.SM.leN, CryptoGames.SM.maxN,
        CryptoGames.SM.boolEq, CryptoGames.SM.receiverOfE, CryptoGames.SM.senderOfE,
        CryptoGames.SM.ltOptE, CryptoGames.SM.Engine.cGsTL, CryptoGames.SM.Engine.optNatLit,
        healEpoch, Option.getD, Bundles.ckaOpS, Bundles.ckaSampS, Bundles.ckaQueryS,
        exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4, exprSizeW_v5,
        exprSizeW_var, exprSizeW_unit, exprSizeW_bool, exprSizeW_nat, exprSizeW_none, exprSizeW_add, exprSizeW_sub,
        exprSizeW_modK, exprSizeW_lt, exprSizeW_eqN, exprSizeW_not, exprSizeW_and, exprSizeW_ite, exprSizeW_pair,
        exprSizeW_fst, exprSizeW_snd, exprSizeW_some, exprSizeW_cons, exprSizeW_caseOpt,
        exprSizeW_letE, exprSizeW_op, exprSizeW_foldrB, exprSizeW_tget, exprSizeW_tset,
        compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt, compSizeW_sample,
        compSizeW_query, bits_zero, bits_one, bits_two, bits_three, bits_four, hb5, Nat.reduceAdd]; omega
  startRecv_le h ctx p tE γv σ tn := by
    have hb5 : bits 5 = 3 := rfl
    cases tL <;> cases par <;> ·
      simp only [CryptoGames.SM.Construction.hooksPRNGBucketParPaperC,
        CryptoGames.SM.Construction.prngBucketStartRecvC,
        CryptoGames.SM.Construction.postLeakBucketE, CryptoGames.SM.Construction.resolveCorrRootE,
        CryptoGames.SM.Construction.lookupPRNGBucketFC, CryptoGames.SM.Construction.tableLookupE,
        CryptoGames.SM.Construction.prngBucketHsCache, CryptoGames.SM.Construction.prngBucketHsFTbl,
        CryptoGames.SM.Construction.prngBucketHsCorrRoot, CryptoGames.SM.Construction.prngBucketHsLc,
        CryptoGames.SM.Construction.prngBucketHsSetFTblAt, CryptoGames.SM.orE, CryptoGames.SM.isSomeE,
        CryptoGames.SM.Engine.cGsTL,
        CryptoGames.SM.Construction.validGuessBucketParPaperE, CryptoGames.SM.validGuessE,
        CryptoGames.SM.healedByE, CryptoGames.SM.optNatEqE, CryptoGames.SM.ltOptE,
        CryptoGames.SM.leN, CryptoGames.SM.maxN, CryptoGames.SM.boolEq,
        CryptoGames.SM.receiverOfE, CryptoGames.SM.senderOfE, CryptoGames.SM.Engine.optNatLit,
        healEpoch, Option.getD, Bundles.ckaOpS, Bundles.ckaSampS, Bundles.ckaQueryS,
        exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4, exprSizeW_var,
        exprSizeW_unit, exprSizeW_bool, exprSizeW_nat, exprSizeW_none, exprSizeW_add, exprSizeW_sub,
        exprSizeW_modK, exprSizeW_lt, exprSizeW_eqN, exprSizeW_not, exprSizeW_and, exprSizeW_ite,
        exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_some, exprSizeW_cons,
        exprSizeW_caseOpt, exprSizeW_letE, exprSizeW_op, exprSizeW_foldrB, exprSizeW_tget,
        exprSizeW_tset, compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt,
        compSizeW_sample, compSizeW_query,
        bits_zero, bits_one, bits_two, bits_three, bits_four, hb5, Nat.reduceAdd]; omega
  fsSend_le h ctx p tE ss hdr m pair := by
    simp only [CryptoGames.SM.Construction.hooksPRNGBucketParPaperC,
      CryptoGames.SM.Construction.prngBucketFsSendC, Bundles.ckaOpS,
      exprSizeW_pair, exprSizeW_some, exprSizeW_op, compSizeW_ret, Nat.reduceAdd]; omega
  fsRecv_le h ctx p tE rs hdr e rec_ := by
    simp only [CryptoGames.SM.Construction.hooksPRNGBucketParPaperC,
      CryptoGames.SM.Construction.prngBucketFsRecvC, Bundles.ckaOpS,
      exprSizeW_pair, exprSizeW_some, exprSizeW_op, compSizeW_ret, Nat.reduceAdd]; omega
  commit_le h ctx p old new := by
    simp only [CryptoGames.SM.Construction.hooksPRNGBucketParPaperC,
      CryptoGames.SM.Construction.prngBucketCommitC,
      exprSizeW_pair, exprSizeW_some, compSizeW_ret, Nat.reduceAdd]; omega
  reveal_le h ctx p vp := by
    cases tL <;> ·
      simp only [CryptoGames.SM.Construction.hooksPRNGBucketParPaperC,
        CryptoGames.SM.Construction.prngBucketRevealC,
        CryptoGames.SM.Construction.postLeakBucketE, CryptoGames.SM.Construction.resolveCorrRootE,
        CryptoGames.SM.Construction.prngBucketHsCorrRoot,
        CryptoGames.SM.Construction.prngBucketHsSetCorrRoot,
        CryptoGames.SM.Construction.prngBucketHsLc, CryptoGames.SM.Construction.prngBucketHsSetLc,
        CryptoGames.SM.Construction.prngBucketHsCache, CryptoGames.SM.Construction.prngBucketHsFTbl,
        CryptoGames.SM.isSomeE, CryptoGames.SM.maxN, CryptoGames.SM.leN, CryptoGames.SM.ltOptE,
        CryptoGames.SM.Engine.cGsEpoch, CryptoGames.SM.Engine.cGsTL,
        CryptoGames.SM.Engine.optNatLit, healEpoch, Option.getD,
        Bundles.ckaOpS, Bundles.ckaSampS, Bundles.ckaQueryS,
        CryptoGames.SM.Engine.realPartyE, CryptoGames.SM.Engine.vpMk, CryptoGames.SM.Engine.vpId,
        CryptoGames.SM.Engine.vpRoot, CryptoGames.SM.Engine.vpVS, CryptoGames.SM.Engine.vpVR,
        CryptoGames.SM.Engine.vpΓ, CryptoGames.SM.Engine.vpTcur, CryptoGames.SM.Engine.vpTcurNat,
        exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_var, exprSizeW_unit, exprSizeW_bool,
        exprSizeW_nat, exprSizeW_lt, exprSizeW_eqN, exprSizeW_not, exprSizeW_and, exprSizeW_ite,
        exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_none, exprSizeW_some,
        exprSizeW_caseOpt, exprSizeW_letE, compSizeW_ret, compSizeW_bind, compSizeW_ite,
        compSizeW_caseOpt, compSizeW_query, bits_zero, bits_one, Nat.reduceAdd]; omega

set_option linter.unusedSimpArgs false in
private theorem initPRNGBucketHybridEStateC_cost_le (L Δbucket : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) {Γ'}
    (bE : Expr OO_cka Γ' .bool) :
    (CryptoGames.SM.Construction.initPRNGBucketHybridEStateC (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L Δbucket tL par t bE).cost ≤
      bE.cost + 20 * L + 2 * bits t + 3 * bits Δbucket + 3 * bits (healEpoch tL) + 3 * bits (tL.getD 0) + 1500 := by
  cases tL <;> cases par <;> ·
    dsimp only [CryptoGames.SM.Construction.initPRNGBucketHybridEStateC]
    refine (cost_bind_ret_le_costUB _ _).trans ?_
    simp only [CryptoGames.SM.Construction.rootPRNGBucketHybridC,
      CryptoGames.SM.Construction.prngBucketHsLc, CryptoGames.SM.Construction.prngBucketHsSetLc,
      CryptoGames.SM.Construction.validGuessBucketParPaperE, CryptoGames.SM.validGuessE,
      CryptoGames.SM.healedByE, CryptoGames.SM.optNatEqE, CryptoGames.SM.ltOptE,
      CryptoGames.SM.leN, CryptoGames.SM.maxN, CryptoGames.SM.boolEq,
      CryptoGames.SM.receiverOfE, CryptoGames.SM.senderOfE, CryptoGames.SM.Engine.optNatLit, Option.getD,
      bits_two,
    CryptoGames.SM.Construction.resolveCorrRootE,
    CryptoGames.SM.Construction.lookupPRNGBucketFC, CryptoGames.SM.Construction.tableLookupE,
    CryptoGames.SM.Construction.prngProcessCorrC, CryptoGames.SM.Construction.prngBucketHsEmptyE,
    CryptoGames.SM.Construction.prngBucketHsCache, CryptoGames.SM.Construction.prngBucketHsFTbl,
    CryptoGames.SM.Construction.prngBucketHsCorrRoot,
    CryptoGames.SM.Construction.prngBucketHsSetFTblAt,
    CryptoGames.SM.Construction.prngBucketHsSetCorrRoot,
    CryptoGames.SM.orE, CryptoGames.SM.isSomeE,
    CryptoGames.SM.Construction.abortedPartiesE, CryptoGames.SM.Engine.mkPartiesE,
    CryptoGames.SM.Engine.cGsInitE, CryptoGames.SM.Engine.cGsMk, CryptoGames.SM.Engine.esMk,
    CryptoGames.SM.Engine.vpMk, CryptoGames.PRFPRNG.prngIface, CryptoGames.PRFPRNG.prngSamplers,
    CryptoGames.PRFPRNG.prngOps, CryptoGames.CKA.ckaSamplers, CryptoGames.CKA.ckaOps,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, bits_zero, bits_one,
    dsl_cost, compCostUB, exprCostUB, Nat.reduceAdd]; omega

set_option linter.unusedSimpArgs false in
private theorem initPRNGBucketHybridEStateC_excessUB_le (B0 L Δbucket : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) {Γ'}
    (bE : Expr OO_cka Γ' .bool) :
    compExcessUB (ckaOpC B0) ckaSampC prngQueryC
      (CryptoGames.SM.Construction.initPRNGBucketHybridEStateC (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L Δbucket tL par t bE) ≤
      exprExcessUB (ckaOpC B0) bE + 15 * L + 5000 := by
  cases tL <;> cases par <;> ·
    simp only [CryptoGames.SM.Construction.initPRNGBucketHybridEStateC,
      CryptoGames.SM.Construction.rootPRNGBucketHybridC,
      CryptoGames.SM.Construction.prngBucketHsLc, CryptoGames.SM.Construction.prngBucketHsSetLc,
      CryptoGames.SM.Construction.validGuessBucketParPaperE, CryptoGames.SM.validGuessE,
      CryptoGames.SM.healedByE, CryptoGames.SM.optNatEqE, CryptoGames.SM.ltOptE,
      CryptoGames.SM.leN, CryptoGames.SM.maxN, CryptoGames.SM.boolEq,
      CryptoGames.SM.receiverOfE, CryptoGames.SM.senderOfE, optNatLit_excessUB,
      exprExcessUB_add, exprExcessUB_modK,
    CryptoGames.SM.Construction.resolveCorrRootE,
    CryptoGames.SM.Construction.lookupPRNGBucketFC, CryptoGames.SM.Construction.tableLookupE,
    CryptoGames.SM.Construction.prngProcessCorrC, CryptoGames.SM.Construction.prngBucketHsEmptyE,
    CryptoGames.SM.Construction.prngBucketHsCache, CryptoGames.SM.Construction.prngBucketHsFTbl,
    CryptoGames.SM.Construction.prngBucketHsCorrRoot,
    CryptoGames.SM.Construction.prngBucketHsSetFTblAt,
    CryptoGames.SM.Construction.prngBucketHsSetCorrRoot,
    CryptoGames.SM.orE, CryptoGames.SM.isSomeE,
    CryptoGames.SM.Construction.abortedPartiesE, CryptoGames.SM.Engine.mkPartiesE,
    CryptoGames.SM.Engine.cGsInitE, CryptoGames.SM.Engine.cGsMk, CryptoGames.SM.Engine.esMk,
    CryptoGames.SM.Engine.vpMk, ckaOpC, ckaSampC, prngQueryC,
    exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
    exprExcessUB_v5, exprExcessUB_var, exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat,
    exprExcessUB_none, exprExcessUB_nil, exprExcessUB_sub, exprExcessUB_lt, exprExcessUB_eqN,
    exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst,
    exprExcessUB_snd, exprExcessUB_some, exprExcessUB_cons, exprExcessUB_caseOpt, exprExcessUB_letE,
    exprExcessUB_op, exprExcessUB_foldrB, exprExcessUB_tconst, exprExcessUB_tget, exprExcessUB_tset,
    compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt,
    compExcessUB_sample, compExcessUB_query, Nat.reduceAdd, Nat.add_zero, Nat.zero_add,
    Nat.mul_zero]; omega

set_option linter.unusedSimpArgs false in
private theorem initPRNGBucketHybridEStateC_sizeW_le (B0 L Δbucket : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) {Γ'}
    (bE : Expr OO_cka Γ' .bool) :
    Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS
      (CryptoGames.SM.Construction.initPRNGBucketHybridEStateC (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L Δbucket tL par t bE) ≤
      Bundles.exprSizeW (Bundles.ckaOpS B0) bE + bits L + 5 * bits Δbucket + 5 * bits (healEpoch tL) +
        5 * bits (tL.getD 0) + 5 * bits t + 8000 := by
  cases tL <;> cases par <;> ·
    simp only [CryptoGames.SM.Construction.initPRNGBucketHybridEStateC,
      CryptoGames.SM.Construction.rootPRNGBucketHybridC,
      CryptoGames.SM.Construction.prngBucketHsLc, CryptoGames.SM.Construction.prngBucketHsSetLc,
      CryptoGames.SM.Construction.validGuessBucketParPaperE, CryptoGames.SM.validGuessE,
      CryptoGames.SM.healedByE, CryptoGames.SM.optNatEqE, CryptoGames.SM.ltOptE,
      CryptoGames.SM.leN, CryptoGames.SM.maxN, CryptoGames.SM.boolEq,
      CryptoGames.SM.receiverOfE, CryptoGames.SM.senderOfE, CryptoGames.SM.Engine.optNatLit, Option.getD,
      exprSizeW_add, exprSizeW_modK, bits_two,
    CryptoGames.SM.Construction.resolveCorrRootE,
    CryptoGames.SM.Construction.lookupPRNGBucketFC, CryptoGames.SM.Construction.tableLookupE,
    CryptoGames.SM.Construction.prngProcessCorrC, CryptoGames.SM.Construction.prngBucketHsEmptyE,
    CryptoGames.SM.Construction.prngBucketHsCache, CryptoGames.SM.Construction.prngBucketHsFTbl,
    CryptoGames.SM.Construction.prngBucketHsCorrRoot,
    CryptoGames.SM.Construction.prngBucketHsSetFTblAt,
    CryptoGames.SM.Construction.prngBucketHsSetCorrRoot,
    CryptoGames.SM.orE, CryptoGames.SM.isSomeE,
    CryptoGames.SM.Construction.abortedPartiesE, CryptoGames.SM.Engine.mkPartiesE,
    CryptoGames.SM.Engine.cGsInitE, CryptoGames.SM.Engine.cGsMk, CryptoGames.SM.Engine.esMk,
    CryptoGames.SM.Engine.vpMk, Bundles.ckaOpS, Bundles.ckaSampS, Bundles.ckaQueryS,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4, exprSizeW_v5,
    exprSizeW_var, exprSizeW_unit, exprSizeW_bool, exprSizeW_nat, exprSizeW_none, exprSizeW_nil,
    exprSizeW_sub, exprSizeW_lt, exprSizeW_eqN, exprSizeW_not, exprSizeW_and, exprSizeW_ite,
    exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_some, exprSizeW_cons, exprSizeW_caseOpt,
    exprSizeW_letE, exprSizeW_op, exprSizeW_foldrB, exprSizeW_tconst, exprSizeW_tget, exprSizeW_tset,
    compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt, compSizeW_sample,
    compSizeW_query, bits_zero, bits_one, Nat.reduceAdd]; omega

private theorem redPRNGAuthDFBucketCommon_parts_le (paper : Bool) (finMode : Fin 3) (B0 q qep : ℕ)
    (tL : Option ℕ) (par : Bool) (t : ℕ) (hB0 : B0 = (q + 1) * (maxForwardJumps + 1))
    (ht : t < qep + 2) (htL : tL.getD 0 ≤ qep + 2) :
    let initC := Comp.bind (Γ := [.unit])
      (CryptoGames.SM.Construction.initPRNGBucketHybridEStateC (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) (q + 1) (3 + 1) tL par t (.bool false))
      (Comp.ret (.pair .unit (.pair .v0 (.none (t := .nat)))))
    let hk := CryptoGames.SM.Construction.hooksPRNGBucketParPaperC (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) (q + 1) B0 (3 + 1) qep tL par t
    let finC := bucketFinishModeC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE)
      (I' := CryptoGames.PRFPRNG.prngIface KC Γ CCoins T I KR RSt K SS RS M E
        sampKR sampKC sampCCoins sampI sampK)
      (vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E
        (.base .γ) (.opt (.base .sig)) (.base .ss) (.base .rs))
      (hsT := @CryptoGames.SM.Construction.prngBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E)
      finMode (q + 1) (2 + 1) tL
    compCostW (ckaOpC B0) ckaSampC prngQueryC initC +
      compCostW (ckaOpC B0) ckaSampC prngQueryC finC + 100000 ≤ fig8AtomicStepBound q qep ∧
    compCostW (ckaOpC B0) ckaSampC prngQueryC
      (bucketHandleC paper hk (q + 1) (2 + 1) qep maxForwardJumps
        (CryptoGames.SM.Construction.bucketParPaperAuthCfgEC (3 + 1) tL par)) + 200000 ≤
      fig8AtomicStepBound q qep := by
  subst hB0
  intro initC hk finC
  have hqep1 := bits_succ_le qep
  have ht_bits := bits_le_bits_qep_add (x := t) (qep := qep) (by omega)
  have htL_bits := bits_le_bits_qep_add (x := tL.getD 0) (qep := qep) (by omega)
  have htH_bits := bits_healEpoch_le tL
  constructor
  · let e0 := CryptoGames.SM.Construction.initPRNGBucketHybridEStateC (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) (Γ' := [.unit]) (q + 1) (3 + 1) tL par t (.bool false)
    have hiC := (bind_ret_bucketInit_cost_le e0).trans
      (Nat.add_le_add_right (initPRNGBucketHybridEStateC_cost_le (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) (Γ' := [.unit]) (q + 1) (3 + 1) tL par t (.bool false)) 8)
    have hiE := (bind_ret_bucketInit_excessUB_le
      (opC := ckaOpC ((q + 1) * (maxForwardJumps + 1))) (sC := ckaSampC)
      (qC := prngQueryC) e0).trans (initPRNGBucketHybridEStateC_excessUB_le
        (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
        ((q + 1) * (maxForwardJumps + 1)) (q + 1) (3 + 1) tL par t (.bool (Γ := [.unit]) false))
    have hiW := compCostW_le_cost_add_excessUB (ckaOpC ((q + 1) * (maxForwardJumps + 1)))
      ckaSampC prngQueryC initC
    have hfC := bucketFinishModeC_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE)
      (I' := CryptoGames.PRFPRNG.prngIface KC Γ CCoins T I KR RSt K
        SS RS M E sampKR sampKC sampCCoins sampI sampK)
      (vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E
        (.base .γ) (.opt (.base .sig)) (.base .ss) (.base .rs))
      (hsT := @CryptoGames.SM.Construction.prngBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E)
      finMode (q + 1) (2 + 1) (by omega) tL
    have hfE := bucketFinishModeC_excessUB_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE)
      (I' := CryptoGames.PRFPRNG.prngIface KC Γ CCoins T I KR RSt K
        SS RS M E sampKR sampKC sampCCoins sampI sampK)
      ((q + 1) * (maxForwardJumps + 1)) ckaSampC prngQueryC
      (vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E
        (.base .γ) (.opt (.base .sig)) (.base .ss) (.base .rs))
      (hsT := @CryptoGames.SM.Construction.prngBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E)
      finMode (q + 1) (2 + 1) tL
    have hfW := compCostW_le_cost_add_excessUB (ckaOpC ((q + 1) * (maxForwardJumps + 1)))
      ckaSampC prngQueryC finC
    simp only [Expr.cost, exprExcessUB_bool, Nat.reduceAdd, bits_four] at hiC hiE
    unfold fig8AtomicStepBound
    dsimp only [initC, finC, e0] at hiC hiE hiW hfC hfE hfW ⊢
    omega
  · refine bucketHandleC_compCostW_le_fig8AtomicStepBound paper hk q qep tL par htL ?_ ?_
    · exact (hooksPRNGBucketParPaperC_costBounded (q + 1) _ qep tL par t).mono (by omega)
    · exact (hooksPRNGBucketParPaperC_excessBounded _ (q + 1) _ qep tL par t).mono
        (by omega) (by omega) (by omega)

private theorem redPRNGAuthDFBucketCommon_size_le (paper : Bool) (finMode : Fin 3) (B0 q qep : ℕ)
    (tL : Option ℕ) (par : Bool) (t : ℕ) (hB0 : B0 = (q + 1) * (maxForwardJumps + 1))
    (ht : t < qep + 2) (htL : tL.getD 0 ≤ qep + 2) (hqep : qep ≤ 4096 * q + 100000000) :
    let initC := Comp.bind (Γ := [.unit])
      (CryptoGames.SM.Construction.initPRNGBucketHybridEStateC (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) (q + 1) (3 + 1) tL par t (.bool false))
      (Comp.ret (.pair .unit (.pair .v0 (.none (t := .nat)))))
    let hk := CryptoGames.SM.Construction.hooksPRNGBucketParPaperC (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) (q + 1) B0 (3 + 1) qep tL par t
    let finC := bucketFinishModeC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE)
      (I' := CryptoGames.PRFPRNG.prngIface KC Γ CCoins T I KR RSt K SS RS M E
        sampKR sampKC sampCCoins sampI sampK)
      (vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E
        (.base .γ) (.opt (.base .sig)) (.base .ss) (.base .rs))
      (hsT := @CryptoGames.SM.Construction.prngBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E)
      finMode (q + 1) (2 + 1) tL
    Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS initC +
      Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS
        (bucketHandleC paper hk (q + 1) (2 + 1) qep maxForwardJumps
          (CryptoGames.SM.Construction.bucketParPaperAuthCfgEC (3 + 1) tL par)) +
      Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS finC + 520 ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep) := by
  subst hB0
  intro initC hk finC
  have hqep1 := bits_succ_le qep
  have hbL : bits (q + 1) ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbqep : bits qep ≤ bits (ratchetCostBudget q qep) := bits_qep_le_ratchetCostBudget hqep
  have hbt : bits t ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbtL : bits (tL.getD 0) ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbtH : bits (healEpoch tL) ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (by cases tL <;> (simp [healEpoch] at htL ⊢; try omega))
  have hbB : bits ((q + 1) * (maxForwardJumps + 1)) ≤ bits (ratchetCostBudget q qep) :=
    bits_B0_le_ratchetCostBudget q qep
  have hi : Bundles.compSizeW (Bundles.ckaOpS ((q + 1) * (maxForwardJumps + 1)))
      Bundles.ckaSampS Bundles.ckaQueryS initC ≤
      20 * bits (ratchetCostBudget q qep) + 9000 := by
    refine (bind_ret_bucketInit_sizeW_le _).trans ?_
    have h0 := initPRNGBucketHybridEStateC_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      (Γ' := [.unit]) ((q + 1) * (maxForwardJumps + 1)) (q + 1) (3 + 1) tL par t (.bool false)
    dsimp only [initC]
    simp only [exprSizeW_bool, Nat.reduceAdd, bits_four] at h0 ⊢
    generalize bits (ratchetCostBudget q qep) = bR at hbL hbt hbtH hbtL ⊢; omega
  have hh : Bundles.compSizeW (Bundles.ckaOpS ((q + 1) * (maxForwardJumps + 1)))
      Bundles.ckaSampS Bundles.ckaQueryS
      (bucketHandleC paper hk (q + 1) (2 + 1) qep maxForwardJumps
        (CryptoGames.SM.Construction.bucketParPaperAuthCfgEC (3 + 1) tL par)) ≤
      500 * bits (ratchetCostBudget q qep) + 240000 :=
    bucketHandleC_sizeW_le_ratchet paper hk q qep tL par htL hqep
      ((hooksPRNGBucketParPaperC_sizeBounded _ (q + 1) _ qep tL par t).mono
        (by generalize bits (ratchetCostBudget q qep) = bR at hbL hbtH hbt hbtL hbqep hqep1 ⊢; omega)
        le_rfl
        (by generalize bits (ratchetCostBudget q qep) = bR at hbB ⊢
            generalize (q + 1) * (maxForwardJumps + 1) = B at hbB ⊢; omega))
  have hf : Bundles.compSizeW (Bundles.ckaOpS ((q + 1) * (maxForwardJumps + 1)))
      Bundles.ckaSampS Bundles.ckaQueryS finC ≤
      18 * bits (ratchetCostBudget q qep) + 700 := by
    have h0 := bucketFinishModeC_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE)
      (I' := CryptoGames.PRFPRNG.prngIface KC Γ CCoins T I KR RSt K
        SS RS M E sampKR sampKC sampCCoins sampI sampK)
      ((q + 1) * (maxForwardJumps + 1)) Bundles.ckaSampS Bundles.ckaQueryS
      (vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E
        (.base .γ) (.opt (.base .sig)) (.base .ss) (.base .rs))
      (hsT := @CryptoGames.SM.Construction.prngBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E)
      finMode (q + 1) (2 + 1) (by omega) tL
    dsimp only [finC] at h0 ⊢
    generalize bits (ratchetCostBudget q qep) = bR at hbL hbtL ⊢; omega
  refine size_le_ratchetSizeBudget (C₀ := 300000) (C₁ := 1100) (by decide) (by decide) ?_
  generalize bits (ratchetCostBudget q qep) = bR at hi hh hf ⊢; omega

private theorem redPRNGAuthDFBucketHybridProg_parts_le (B0 q qep : ℕ) (tL : Option ℕ) (par : Bool)
    (t : ℕ) (hB0 : B0 = (q + 1) * (maxForwardJumps + 1))
    (ht : t < qep + 2) (htL : tL.getD 0 ≤ qep + 2) :
    let P := CryptoGames.SM.Construction.redPRNGAuthDFBucketHybridProg
      (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) (q + 1) B0 1 qep maxForwardJumps tL par t
    compCostW (ckaOpC B0) ckaSampC prngQueryC P.init +
      compCostW (ckaOpC B0) ckaSampC prngQueryC P.finish + 100000 ≤ fig8AtomicStepBound q qep ∧
    compCostW (ckaOpC B0) ckaSampC prngQueryC P.handle + 200000 ≤ fig8AtomicStepBound q qep :=
  redPRNGAuthDFBucketCommon_parts_le false ⟨0, by decide⟩ B0 q qep tL par t hB0 ht htL

private theorem redPRNGAuthDFBucketHybridProg_size_le (B0 q qep : ℕ) (tL : Option ℕ) (par : Bool)
    (t : ℕ) (hB0 : B0 = (q + 1) * (maxForwardJumps + 1))
    (ht : t < qep + 2) (htL : tL.getD 0 ≤ qep + 2) (hqep : qep ≤ 4096 * q + 100000000) :
    let P := CryptoGames.SM.Construction.redPRNGAuthDFBucketHybridProg
      (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) (q + 1) B0 1 qep maxForwardJumps tL par t
    Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS P.init +
      Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS P.handle +
      Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS P.finish + 520 ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep) :=
  redPRNGAuthDFBucketCommon_size_le false ⟨0, by decide⟩ B0 q qep tL par t hB0 ht htL hqep

section SplitBucketBounds
set_option linter.unusedVariables false

private def prngBucketLcFinishC {ι : Type} {Spec' : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka Spec'}
    (checkGMain : Option Bool) (L Δ : ℕ) (tL : Option ℕ) (t0 : ℕ) :
    Comp OO_cka I'
      [.prod (CryptoGames.SM.Engine.esTy
        (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E
          (.base .γ) (.opt (.base .sig)) (.base .ss) (.base .rs))
        (@CryptoGames.SM.Construction.prngBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E))
        (.opt .nat), .bool] .bool :=
  match checkGMain with
  | none =>
    rdsl [st, _] do
      (es0, winEp0) ← return (st.1, st.2)
      match winEp0 with
      | none => return false
      | some tWin =>
        let lcOK :=
          match CryptoGames.SM.Construction.prngBucketHsLc (CryptoGames.SM.Engine.esH es0) with
          | none => true
          | some e => !(e < nat t0)
        return (((!(CryptoGames.SM.Engine.esAbort es0) &&
          CryptoGames.SM.Engine.cGsWin (CryptoGames.SM.Engine.esG es0)) &&
          CryptoGames.SM.Engine.cAuthOKE (raw L) (raw Δ)
            (CryptoGames.SM.Engine.optNatLit (raw tL)) tWin (CryptoGames.SM.Engine.esG es0)) && lcOK)
  | some gMain =>
    rdsl [st, _] do
      (es0, winEp0) ← return (st.1, st.2)
      match winEp0 with
      | none => return false
      | some tWin =>
        let lcOK :=
          if bool gMain then
            match CryptoGames.SM.Construction.prngBucketHsLc (CryptoGames.SM.Engine.esH es0) with
            | none => true
            | some e => !(e < nat t0)
          else
            true
        return (((!(CryptoGames.SM.Engine.esAbort es0) &&
          CryptoGames.SM.Engine.cGsWin (CryptoGames.SM.Engine.esG es0)) &&
          CryptoGames.SM.Engine.cAuthOKE (raw L) (raw Δ)
            (CryptoGames.SM.Engine.optNatLit (raw tL)) tWin (CryptoGames.SM.Engine.esG es0)) && lcOK)

set_option linter.unusedSimpArgs false in
private theorem prngBucketLcFinishC_cost_le {ι : Type} {Spec' : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka Spec'}
    (checkGMain : Option Bool) (L Δ : ℕ) (hΔ : Δ ≤ 4) (tL : Option ℕ) (t0 : ℕ) :
    (prngBucketLcFinishC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (I' := I') checkGMain L Δ tL t0).cost ≤
      240 * L + 2 * bits (tL.getD 0) + bits t0 + 420 := by
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E
    (.base .γ) (.opt (.base .sig)) (.base .ss) (.base .rs)
  let hsT := @CryptoGames.SM.Construction.prngBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E
  let Γf : List (Ty S_cka) := .nat :: .prod (CryptoGames.SM.Engine.esTy vpT hsT) (.opt .nat) ::
    [.prod (CryptoGames.SM.Engine.esTy vpT hsT) (.opt .nat), .bool]
  have hAuth := cAuthOKE_any_cost_le (O' := OO_cka) (vpT := vpT) L Δ hΔ (Γ' := Γf)
    (CryptoGames.SM.Engine.optNatLit tL) .v0 (CryptoGames.SM.Engine.esG (hsT := hsT) (.fst .v1))
  have hOpt : (CryptoGames.SM.Engine.optNatLit (O' := OO_cka) (Γ' := Γf) tL).cost ≤
      bits (tL.getD 0) + 2 := by
    cases tL <;> simp only [CryptoGames.SM.Engine.optNatLit, Option.getD, Expr.cost, bits_zero] <;> omega
  cases checkGMain <;> ·
    dsimp only [prngBucketLcFinishC]
    simp only [CryptoGames.SM.Construction.prngBucketHsLc, esG_cost, esH_cost, esAbort_cost,
      CryptoGames.SM.Engine.cGsWin, Comp.cost, Expr.cost, dsl_cost,
      v0_cost, v1_cost, Nat.reduceAdd] at hAuth ⊢; omega

set_option linter.unusedSimpArgs false in
private theorem prngBucketLcFinishC_excessUB_le {ι : Type} {Spec' : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka Spec'}
    (B0 : ℕ) (sC : I'.smp.Samp → ℕ) (qC : I'.Tag → ℕ)
    (checkGMain : Option Bool) (L Δ : ℕ) (tL : Option ℕ) (t0 : ℕ) :
    compExcessUB (ckaOpC B0) sC qC
      (prngBucketLcFinishC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) (I' := I') checkGMain L Δ tL t0) ≤ 30 := by
  cases checkGMain <;> ·
    simp only [prngBucketLcFinishC, CryptoGames.SM.Construction.prngBucketHsLc,
      CryptoGames.SM.Engine.cAuthOKE, CryptoGames.SM.Engine.cCanonE,
      CryptoGames.SM.validGuessE, CryptoGames.SM.healedByE, CryptoGames.SM.optNatEqE,
      CryptoGames.SM.ltOptE, CryptoGames.SM.leN, CryptoGames.SM.maxN, CryptoGames.SM.boolEq,
      CryptoGames.SM.receiverOfE, CryptoGames.SM.Engine.esH,
      CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.esG,
      CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs, optNatLit_excessUB,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_var,
      exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none, exprExcessUB_add, exprExcessUB_modK,
      exprExcessUB_lt, exprExcessUB_eqN, exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite,
      exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_some, exprExcessUB_caseOpt,
      exprExcessUB_letE, exprExcessUB_anyB, exprExcessUB_foldrB, compExcessUB_ret, compExcessUB_bind,
      compExcessUB_caseOpt, Nat.add_zero, Nat.zero_add, Nat.mul_zero]; omega

set_option linter.unusedSimpArgs false in
private theorem prngBucketLcFinishC_sizeW_le {ι : Type} {Spec' : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka Spec'}
    (B0 : ℕ) (sS : I'.smp.Samp → ℕ) (qS : I'.Tag → ℕ)
    (checkGMain : Option Bool) (L Δ : ℕ) (hΔ : Δ ≤ 4) (tL : Option ℕ) (t0 : ℕ) :
    Bundles.compSizeW (Bundles.ckaOpS B0) sS qS
      (prngBucketLcFinishC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) (I' := I') checkGMain L Δ tL t0) ≤
      10 * bits L + 4 * bits (tL.getD 0) + 2 * bits t0 + 650 := by
  have hc : Δ = 0 ∨ Δ = 1 ∨ Δ = 2 ∨ Δ = 3 ∨ Δ = 4 := by omega
  cases checkGMain <;> cases tL <;> rcases hc with rfl | rfl | rfl | rfl | rfl <;> ·
    simp only [prngBucketLcFinishC, CryptoGames.SM.Construction.prngBucketHsLc,
      CryptoGames.SM.Engine.cAuthOKE, CryptoGames.SM.Engine.cCanonE,
      CryptoGames.SM.validGuessE, CryptoGames.SM.healedByE, CryptoGames.SM.optNatEqE,
      CryptoGames.SM.ltOptE, CryptoGames.SM.leN, CryptoGames.SM.maxN, CryptoGames.SM.boolEq,
      CryptoGames.SM.receiverOfE, Option.getD, CryptoGames.SM.Engine.optNatLit,
      CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.cGsWin,
      CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_var, exprSizeW_bool,
      exprSizeW_nat, exprSizeW_none, exprSizeW_add, exprSizeW_modK, exprSizeW_lt, exprSizeW_eqN,
      exprSizeW_not, exprSizeW_and, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
      exprSizeW_some, exprSizeW_caseOpt, exprSizeW_letE, exprSizeW_anyB, exprSizeW_foldrB,
      compSizeW_ret, compSizeW_bind, compSizeW_caseOpt,
      bits_zero, bits_one, bits_two, bits_three, bits_four, Nat.reduceAdd]; omega

set_option linter.unusedSimpArgs false in
private theorem hooksPRNGBucketSplitPaperC_costBounded (L B qep : ℕ) (tL : Option ℕ)
    (par gMain : Bool) (t0 : ℕ) :
    HooksCostBounded
      (CryptoGames.SM.Construction.hooksPRNGBucketSplitPaperC (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B (3 + 1) qep tL par gMain t0)
      (20 * L + 2 * bits (qep + 1) + 6 * bits (healEpoch tL) + 4 * bits (tL.getD 0) +
        2 * bits t0 + (B + 1) + 3500) where
  startSend_le := (hooksPRNGBucketParPaperC_costBounded L B qep tL par t0).startSend_le
  startRecv_le h ctx p tE γv σ tn := by
    have hb5 : bits 5 = 3 := rfl
    cases gMain
    · exact (hooksPRNGBucketParPaperC_costBounded L B qep tL par t0).startRecv_le h ctx p tE γv σ tn
    · cases tL <;> cases par <;> ·
        dsimp only [CryptoGames.SM.Construction.hooksPRNGBucketSplitPaperC,
          CryptoGames.SM.Construction.prngBucketStartRecvSplitC,
          CryptoGames.SM.Construction.prngBucketStartRecvMainC]
        refine (cost_bind_ret_le_costUB _ _).trans ?_
        simp only [CryptoGames.SM.Construction.resolveCorrRootE,
          CryptoGames.SM.Construction.prngBucketHsCache,
          CryptoGames.SM.Construction.prngBucketHsCorrRoot,
          CryptoGames.SM.orE, CryptoGames.SM.isSomeE,
          CryptoGames.SM.Construction.validGuessBucketParPaperE, CryptoGames.SM.validGuessE,
          CryptoGames.SM.healedByE, CryptoGames.SM.optNatEqE, CryptoGames.SM.ltOptE,
          CryptoGames.SM.leN, CryptoGames.SM.maxN, CryptoGames.SM.boolEq,
          CryptoGames.SM.receiverOfE, CryptoGames.SM.senderOfE, CryptoGames.SM.Engine.optNatLit,
          healEpoch, Option.getD, Option.isSome, ite_true, ite_false,
          Bool.false_eq_true, Bool.true_eq_false,
          CryptoGames.PRFPRNG.prngIface, CryptoGames.PRFPRNG.prngSamplers,
          CryptoGames.PRFPRNG.prngOps, CryptoGames.CKA.ckaSamplers, CryptoGames.CKA.ckaOps,
          Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, dsl_cost, compCostUB, exprCostUB,
          bits_zero, bits_one, bits_two, bits_three, bits_four, hb5, Nat.reduceAdd]; omega
  fsSend_le := (hooksPRNGBucketParPaperC_costBounded L B qep tL par t0).fsSend_le
  fsRecv_le := (hooksPRNGBucketParPaperC_costBounded L B qep tL par t0).fsRecv_le
  commit_le := (hooksPRNGBucketParPaperC_costBounded L B qep tL par t0).commit_le
  reveal_le h ctx p vp := by
    cases gMain
    · cases tL <;> ·
        dsimp only [CryptoGames.SM.Construction.hooksPRNGBucketSplitPaperC,
          CryptoGames.SM.Construction.prngBucketRevealSplitC,
          CryptoGames.SM.Construction.prngBucketRevealForgedHdrC]
        simp only [ite_false, Bool.false_eq_true]
        refine (cost_bind_ret_le_costUB _ _).trans ?_
        simp only [CryptoGames.SM.orE, CryptoGames.SM.maxN, CryptoGames.SM.leN,
          CryptoGames.SM.Engine.cGsEpoch, CryptoGames.SM.Engine.realPartyE,
          CryptoGames.SM.Engine.vpMk, CryptoGames.SM.Engine.vpId, CryptoGames.SM.Engine.vpRoot,
          CryptoGames.SM.Engine.vpVS, CryptoGames.SM.Engine.vpVR, CryptoGames.SM.Engine.vpΓ,
          CryptoGames.SM.Engine.vpTcur, CryptoGames.SM.Engine.vpTcurNat,
          healEpoch, Option.getD, Option.isSome, ite_true, ite_false,
          Bool.false_eq_true, Bool.true_eq_false,
          CryptoGames.PRFPRNG.prngIface, CryptoGames.PRFPRNG.prngSamplers,
          CryptoGames.PRFPRNG.prngOps, CryptoGames.CKA.ckaSamplers, CryptoGames.CKA.ckaOps,
          Expr.cost, Expr.v0, Expr.v1, Expr.v2,
          bits_zero, bits_one, dsl_cost, compCostUB, exprCostUB, Nat.reduceAdd]; omega
    · dsimp only [CryptoGames.SM.Construction.hooksPRNGBucketSplitPaperC,
        CryptoGames.SM.Construction.prngBucketRevealSplitC]
      simp only [ite_true]
      exact (hooksPRNGBucketParPaperC_costBounded L B qep tL par t0).reveal_le h ctx p vp

set_option linter.unusedSimpArgs false in
private theorem hooksPRNGBucketSplitPaperC_excessBounded (B0 L B qep : ℕ) (tL : Option ℕ)
    (par gMain : Bool) (t0 : ℕ) :
    HooksExcessBounded B0 ckaSampC prngQueryC
      (CryptoGames.SM.Construction.hooksPRNGBucketSplitPaperC (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B (3 + 1) qep tL par gMain t0)
      (15 * L + 8000) 380000 (20 * B0 + 3 * bits B + 2710000) where
  startSend_le := (hooksPRNGBucketParPaperC_excessBounded B0 L B qep tL par t0).startSend_le
  startRecv_le h ctx p tE γv σ tn := by
    cases gMain
    · exact (hooksPRNGBucketParPaperC_excessBounded B0 L B qep tL par t0).startRecv_le h ctx p tE γv σ tn
    · cases tL <;> cases par <;> ·
        simp only [CryptoGames.SM.Construction.hooksPRNGBucketSplitPaperC,
          CryptoGames.SM.Construction.prngBucketStartRecvSplitC,
          CryptoGames.SM.Construction.prngBucketStartRecvMainC,
          CryptoGames.SM.Construction.resolveCorrRootE,
          CryptoGames.SM.Construction.prngBucketHsCache,
          CryptoGames.SM.Construction.prngBucketHsCorrRoot,
          CryptoGames.SM.orE, CryptoGames.SM.isSomeE,
          CryptoGames.SM.Construction.validGuessBucketParPaperE, CryptoGames.SM.validGuessE,
          CryptoGames.SM.healedByE, CryptoGames.SM.optNatEqE, CryptoGames.SM.ltOptE,
          CryptoGames.SM.leN, CryptoGames.SM.maxN, CryptoGames.SM.boolEq,
          CryptoGames.SM.receiverOfE, CryptoGames.SM.senderOfE, optNatLit_excessUB,
          healEpoch, Option.getD, Option.isSome, ite_true, ite_false,
          Bool.false_eq_true, Bool.true_eq_false,
          ckaOpC, ckaSampC, prngQueryC,
          exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
          exprExcessUB_var, exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none,
          exprExcessUB_add, exprExcessUB_sub, exprExcessUB_modK, exprExcessUB_lt, exprExcessUB_eqN,
          exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst,
          exprExcessUB_snd, exprExcessUB_some, exprExcessUB_cons, exprExcessUB_caseOpt,
          exprExcessUB_letE, exprExcessUB_op, exprExcessUB_foldrB, exprExcessUB_tget, exprExcessUB_tset,
          compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt,
          compExcessUB_sample, compExcessUB_query, Nat.reduceAdd, Nat.add_zero, Nat.zero_add,
          Nat.mul_zero]; omega
  fsSend_le := (hooksPRNGBucketParPaperC_excessBounded B0 L B qep tL par t0).fsSend_le
  fsRecv_le := (hooksPRNGBucketParPaperC_excessBounded B0 L B qep tL par t0).fsRecv_le
  commit_le := (hooksPRNGBucketParPaperC_excessBounded B0 L B qep tL par t0).commit_le
  reveal_le h ctx p vp := by
    cases gMain
    · simp only [CryptoGames.SM.Construction.hooksPRNGBucketSplitPaperC,
        CryptoGames.SM.Construction.prngBucketRevealSplitC,
        CryptoGames.SM.Construction.prngBucketRevealForgedHdrC,
        CryptoGames.SM.orE, CryptoGames.SM.maxN, CryptoGames.SM.leN,
        CryptoGames.SM.Engine.cGsEpoch, optNatLit_excessUB, ckaOpC, ckaSampC, prngQueryC,
        healEpoch, Option.getD, Option.isSome, ite_true, ite_false,
        Bool.false_eq_true, Bool.true_eq_false,
        CryptoGames.SM.Engine.realPartyE, CryptoGames.SM.Engine.vpMk, CryptoGames.SM.Engine.vpId,
        CryptoGames.SM.Engine.vpRoot, CryptoGames.SM.Engine.vpVS, CryptoGames.SM.Engine.vpVR,
        CryptoGames.SM.Engine.vpΓ, CryptoGames.SM.Engine.vpTcur, CryptoGames.SM.Engine.vpTcurNat,
        exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_var, exprExcessUB_unit,
        exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_lt, exprExcessUB_eqN, exprExcessUB_not,
        exprExcessUB_and, exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd,
        exprExcessUB_none, exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_letE,
        compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt,
        compExcessUB_query, Nat.reduceAdd, Nat.add_zero, Nat.zero_add, Nat.mul_zero]; omega
    · dsimp only [CryptoGames.SM.Construction.hooksPRNGBucketSplitPaperC,
        CryptoGames.SM.Construction.prngBucketRevealSplitC]
      simp only [ite_true]
      exact (hooksPRNGBucketParPaperC_excessBounded B0 L B qep tL par t0).reveal_le h ctx p vp

set_option linter.unusedSimpArgs false in
private theorem hooksPRNGBucketSplitPaperC_sizeBounded (B0 L B qep : ℕ) (tL : Option ℕ)
    (par gMain : Bool) (t0 : ℕ) :
    HooksSizeBounded B0 Bundles.ckaSampS Bundles.ckaQueryS
      (CryptoGames.SM.Construction.hooksPRNGBucketSplitPaperC (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B (3 + 1) qep tL par gMain t0)
      (bits L + 8 * bits (healEpoch tL) + 5 * bits t0 + 5 * bits (tL.getD 0) +
        2 * bits (qep + 1) + 17900) 2000 (3 * bits B0 + 2 * bits B + 2000) where
  startSend_le := (hooksPRNGBucketParPaperC_sizeBounded B0 L B qep tL par t0).startSend_le
  startRecv_le h ctx p tE γv σ tn := by
    have hb5 : bits 5 = 3 := rfl
    cases gMain
    · exact (hooksPRNGBucketParPaperC_sizeBounded B0 L B qep tL par t0).startRecv_le h ctx p tE γv σ tn
    · cases tL <;> cases par <;> ·
        dsimp only [CryptoGames.SM.Construction.hooksPRNGBucketSplitPaperC,
          CryptoGames.SM.Construction.prngBucketStartRecvSplitC,
          CryptoGames.SM.Construction.prngBucketStartRecvMainC]
        simp only [CryptoGames.SM.Construction.resolveCorrRootE,
          CryptoGames.SM.Construction.prngBucketHsCache,
          CryptoGames.SM.Construction.prngBucketHsCorrRoot,
          CryptoGames.SM.orE, CryptoGames.SM.isSomeE,
          CryptoGames.SM.Construction.validGuessBucketParPaperE, CryptoGames.SM.validGuessE,
          CryptoGames.SM.healedByE, CryptoGames.SM.optNatEqE, CryptoGames.SM.ltOptE,
          CryptoGames.SM.leN, CryptoGames.SM.maxN, CryptoGames.SM.boolEq,
          CryptoGames.SM.receiverOfE, CryptoGames.SM.senderOfE, CryptoGames.SM.Engine.optNatLit,
          healEpoch, Option.getD, Option.isSome, ite_true, ite_false,
          Bool.false_eq_true, Bool.true_eq_false,
          Bundles.ckaOpS, Bundles.ckaSampS, Bundles.ckaQueryS,
          exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4, exprSizeW_var,
          exprSizeW_unit, exprSizeW_bool, exprSizeW_nat, exprSizeW_none, exprSizeW_add, exprSizeW_sub,
          exprSizeW_modK, exprSizeW_lt, exprSizeW_eqN, exprSizeW_not, exprSizeW_and, exprSizeW_ite,
          exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_some, exprSizeW_cons,
          exprSizeW_caseOpt, exprSizeW_letE, exprSizeW_op, exprSizeW_foldrB, exprSizeW_tget,
          exprSizeW_tset, compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt,
          compSizeW_sample, compSizeW_query,
          bits_zero, bits_one, bits_two, bits_three, bits_four, hb5, Nat.reduceAdd]; omega
  fsSend_le := (hooksPRNGBucketParPaperC_sizeBounded B0 L B qep tL par t0).fsSend_le
  fsRecv_le := (hooksPRNGBucketParPaperC_sizeBounded B0 L B qep tL par t0).fsRecv_le
  commit_le := (hooksPRNGBucketParPaperC_sizeBounded B0 L B qep tL par t0).commit_le
  reveal_le h ctx p vp := by
    cases gMain
    · cases tL <;> ·
        dsimp only [CryptoGames.SM.Construction.hooksPRNGBucketSplitPaperC,
          CryptoGames.SM.Construction.prngBucketRevealSplitC,
          CryptoGames.SM.Construction.prngBucketRevealForgedHdrC]
        simp only [CryptoGames.SM.orE, CryptoGames.SM.maxN, CryptoGames.SM.leN,
          CryptoGames.SM.Engine.cGsEpoch,
          healEpoch, Option.getD, Option.isSome, ite_true, ite_false,
          Bool.false_eq_true, Bool.true_eq_false,
          Bundles.ckaOpS, Bundles.ckaSampS, Bundles.ckaQueryS,
          CryptoGames.SM.Engine.realPartyE, CryptoGames.SM.Engine.vpMk, CryptoGames.SM.Engine.vpId,
          CryptoGames.SM.Engine.vpRoot, CryptoGames.SM.Engine.vpVS, CryptoGames.SM.Engine.vpVR,
          CryptoGames.SM.Engine.vpΓ, CryptoGames.SM.Engine.vpTcur, CryptoGames.SM.Engine.vpTcurNat,
          exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_var, exprSizeW_unit, exprSizeW_bool,
          exprSizeW_nat, exprSizeW_lt, exprSizeW_eqN, exprSizeW_not, exprSizeW_and, exprSizeW_ite,
          exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_none, exprSizeW_some,
          exprSizeW_caseOpt, exprSizeW_letE, compSizeW_ret, compSizeW_bind, compSizeW_ite,
          compSizeW_caseOpt, compSizeW_query, bits_zero, bits_one, Nat.reduceAdd]; omega
    · dsimp only [CryptoGames.SM.Construction.hooksPRNGBucketSplitPaperC,
        CryptoGames.SM.Construction.prngBucketRevealSplitC]
      simp only [ite_true]
      exact (hooksPRNGBucketParPaperC_sizeBounded B0 L B qep tL par t0).reveal_le h ctx p vp

private def splitHandleC {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' (.base .γ) (.opt (.base .sig)) (.base .ss) (.base .rs)
      (@CryptoGames.SM.Construction.prngBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E))
    (L Δ qep maxSkip : ℕ) (gMain : Bool) (cfg : CryptoGames.SM.Engine.ConfigEC OO_cka) :
    Comp OO_cka I'
      [.prod (CryptoGames.SM.Engine.esTy
        (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E
          (.base .γ) (.opt (.base .sig)) (.base .ss) (.base .rs))
        (@CryptoGames.SM.Construction.prngBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E))
        (.opt .nat),
       (CryptoGames.CKA.ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).Q]
      (.prod (CryptoGames.CKA.ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).R
        (.prod (CryptoGames.SM.Engine.esTy
          (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E
            (.base .γ) (.opt (.base .sig)) (.base .ss) (.base .rs))
          (@CryptoGames.SM.Construction.prngBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E))
          (.opt .nat))) :=
  rdsl [st, q] do
    (es0, winEp0, q0) ← return (st.1, st.2, q)
    match q0 with
    | .inl qBase =>
      match qBase with
      | .inl (.inl (.inl (.inl x))) =>
        (p0, m0, r0) ← return x
        if CryptoGames.SM.orE (CryptoGames.SM.Engine.esAbort es0)
            (CryptoGames.SM.Engine.cGsWin (CryptoGames.SM.Engine.esG es0)) then
          return (.inl (inl (inl (inl (inl none)))), (es0, winEp0))
        else
          match CryptoGames.SM.Engine.cEpMgmtE (raw Δ) (raw qep) (CryptoGames.SM.Engine.esG es0) p0
              (CryptoGames.SM.isSomeE r0) with
          | none => return (.inl (inl (inl (inl (inl none)))), (es0, winEp0))
          | some s1 =>
            (res, h') ← CryptoGames.SM.Engine.vSendC (raw hk)
              (CryptoGames.SM.Engine.esH es0) s1 p0
              (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt s1) p0) m0 none r0
            match res with
            | none =>
              return (.inl (inl (inl (inl (inl none)))),
                (CryptoGames.SM.Engine.esMk (CryptoGames.SM.Engine.esG es0) h' true, winEp0))
            | some (st', ct) =>
              let recE :=
                ((p0, CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsEpoch s1) p0,
                  CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsIdx s1) p0 + 1), m0, ct)
              let g' := CryptoGames.SM.Engine.cRecordE (raw L) (raw Δ) s1 p0 st' recE false
              return (.inl (inl (inl (inl (inl (some ct))))),
                (CryptoGames.SM.Engine.esMk g' h' (CryptoGames.SM.Engine.esAbort es0), winEp0))
      | .inl (.inl (.inl (.inr _))) =>
        return (.inl (inl (inl (inl (inr none)))), (es0, winEp0))
      | .inl (.inl (.inr x)) =>
        (out, es') ← CryptoGames.SM.Engine.deliverEC (raw hk) L maxSkip (raw cfg) es0 x
        return (.inl (inl (inl (inr out))), (es', winEp0))
      | .inl (.inr x) =>
        let wasWin := CryptoGames.SM.Engine.cGsWin (CryptoGames.SM.Engine.esG es0)
        let isNewForged :=
          (x.2.1.1 == CryptoGames.SM.Engine.vpTcurNat
            (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG es0)) x.1) + 1) &&
            !(CryptoGames.SM.Construction.isHonestHdrPRNGBucketE (ckaInitA := ckaInitA)
              (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
              (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
              (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
              (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
              (defaultE := defaultE) (CryptoGames.SM.Engine.esH es0) x.2.1)
        (out, es') ← CryptoGames.SM.Engine.injectEC (raw hk) L (raw Δ) qep (raw cfg) es0 x
        let winEp' :=
          if !wasWin && CryptoGames.SM.Engine.cGsWin (CryptoGames.SM.Engine.esG es') &&
              CryptoGames.SM.orE (bool gMain) isNewForged then
            some x.2.1.1
          else winEp0
        return (.inl (inl (inr out)), (es', winEp'))
      | .inr p0 =>
        let s0 := CryptoGames.SM.Engine.esG es0
        if CryptoGames.SM.orE (CryptoGames.SM.Engine.esAbort es0)
            (CryptoGames.SM.orE (CryptoGames.SM.Engine.cGsWin s0)
              (!(CryptoGames.SM.Engine.cCorrAllowedPaperE (raw L) s0 p0))) then
          return (.inl (inr none), (es0, winEp0))
        else
          let s1 := CryptoGames.SM.Engine.cAfterCorrE (raw L) s0 p0
          (res, h') ← CryptoGames.SM.Engine.HooksC.reveal (raw hk)
            (CryptoGames.SM.Engine.esH es0) s0 p0
            (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt s0) p0)
          match res with
          | none =>
            return (.inl (inr none), (CryptoGames.SM.Engine.esMk s0 h' true, winEp0))
          | some stOut =>
            return (.inl (inr (some stOut)),
              (CryptoGames.SM.Engine.esMk s1 h' (CryptoGames.SM.Engine.esAbort es0), winEp0))
    | .inr x =>
      let wasWin := CryptoGames.SM.Engine.cGsWin (CryptoGames.SM.Engine.esG es0)
      (out, es') ← CryptoGames.SM.Engine.deliverForgeEC (raw hk) L (raw Δ) qep (raw cfg) es0 x
      let winEp' :=
        if !wasWin && CryptoGames.SM.Engine.cGsWin (CryptoGames.SM.Engine.esG es') && bool gMain then
          some x.2.2.1.1
        else winEp0
      return (.inr out, (es', winEp'))

set_option linter.unusedSimpArgs false in
private theorem splitHandleC_cost_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' (.base .γ) (.opt (.base .sig)) (.base .ss) (.base .rs)
      (@CryptoGames.SM.Construction.prngBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E))
    (H L Δ qep maxSkip C_inj : ℕ) (hΔ : Δ ≤ 4) (gMain : Bool)
    (cfg : CryptoGames.SM.Engine.ConfigEC OO_cka)
    (hcfg : ∀ {Γ'} (e : Expr OO_cka Γ' .nat), (cfg.injectFullE e).cost ≤ 3 * e.cost + C_inj)
    (hhk : HooksCostBounded hk H) :
    (splitHandleC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      hk L Δ qep maxSkip gMain cfg).cost ≤
      3 * H + 6000 * L + 5 * bits qep + 2 * (maxSkip + 1) + C_inj + 8000 := by
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E
    (.base .γ) (.opt (.base .sig)) (.base .ss) (.base .rs)
  let hsT := @CryptoGames.SM.Construction.prngBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E
  let psT := CryptoGames.CKA.ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E
  let esT := CryptoGames.SM.Engine.esTy vpT hsT
  let qT := (CryptoGames.CKA.ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).Q
  let txQ : Ty S_cka := .prod .bool (.prod (.base .msg) (.opt (.base .ccoins)))
  let chQ : Ty S_cka := .prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .ccoins))))
  let dlQ : Ty S_cka := .prod .bool ckaHdrCtT
  let dfQ : Ty S_cka := .prod .bool (.prod ckaHdrCtT ckaHdrCtT)
  let smqT : Ty S_cka := .sum (.sum (.sum (.sum txQ chQ) dlQ) dlQ) .bool
  let Γ0 : List (Ty S_cka) := .prod esT (.prod (.opt .nat) qT) :: [.prod esT (.opt .nat), qT]
  let Γ_df : List (Ty S_cka) := dfQ :: Γ0; let Γ_cr : List (Ty S_cka) := .bool :: smqT :: Γ0
  let Γ_cr2 : List (Ty S_cka) := psT :: .prod (.opt psT) hsT :: Γ_cr
  let Γ_ij : List (Ty S_cka) := dlQ :: .sum (.sum (.sum txQ chQ) dlQ) dlQ :: smqT :: Γ0
  let Γ_dl : List (Ty S_cka) := dlQ :: .sum (.sum txQ chQ) dlQ :: .sum (.sum (.sum txQ chQ) dlQ) dlQ :: smqT :: Γ0
  let Γ_tx0 : List (Ty S_cka) := txQ :: txQ :: .sum txQ chQ :: .sum (.sum txQ chQ) dlQ :: .sum (.sum (.sum txQ chQ) dlQ) dlQ :: smqT :: Γ0
  let Γ_tx1 : List (Ty S_cka) := CryptoGames.SM.Engine.cGsTy vpT :: Γ_tx0
  let Γ_tx2 : List (Ty S_cka) := .prod vpT ckaHdrCtT :: .prod (.opt (.prod vpT ckaHdrCtT)) hsT :: Γ_tx1
  have hep := cEpMgmtE_any_cost_le (O' := OO_cka) (vpT := vpT) Δ qep hΔ (Γ' := Γ_tx0)
    (CryptoGames.SM.Engine.esG (.fst .v6)) (.fst .v0) (CryptoGames.SM.isSomeE (.snd (.snd .v0)))
  have hvs := vSendC_any_cost_le hk H hhk (Γ' := Γ_tx1) (CryptoGames.SM.Engine.esH (.fst .v7)) .v0
    (.fst .v1) (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt .v0) (.fst .v1)) (.fst (.snd .v1)) .none (.snd (.snd .v1))
  have hrec := cRecordE_any_cost_le (O' := OO_cka) (vpT := vpT) L Δ hΔ (Γ' := Γ_tx2) .v2 (.fst .v3) (.fst .v0)
    (.pair (.pair (.fst .v3) (.pair (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsEpoch .v2) (.fst .v3))
      (.add (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsIdx .v2) (.fst .v3)) (.nat 1))))
      (.pair (.fst (.snd .v3)) (.snd .v0))) (.bool false)
  have hdl := deliverEC_any_cost_le hk H L maxSkip cfg hhk (Γ' := Γ_dl) (.fst .v4) .v0
  have hij := injectEC_anyCfg_cost_le hk H L Δ qep C_inj hΔ cfg hcfg hhk (Γ' := Γ_ij) (.fst .v3) .v0
  have hca := corrAllowedChoiceE_cost_le (vpT := vpT) true L (Γ' := Γ_cr)
    (CryptoGames.SM.Engine.esG (O' := OO_cka) (.fst .v2)) .v0
  have hac := cAfterCorrE_cost_le (O' := OO_cka) (vpT := vpT) L (Γ' := Γ_cr2)
    (CryptoGames.SM.Engine.esG (hsT := hsT) (.fst .v4)) .v2
  have hrv := hhk.reveal_le (Γ' := Γ_cr) (CryptoGames.SM.Engine.esH (.fst .v2))
    (CryptoGames.SM.Engine.esG (.fst .v2)) .v0
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v2))) .v0)
  have hdf := deliverForgeEC_anyCfg_cost_le hk H L Δ qep C_inj hΔ cfg hcfg hhk (Γ' := Γ_df) (.fst .v1) .v0
  dsimp only [corrAllowedChoiceE] at hca
  simp only [esG_cost, esH_cost, pGet_cost, cGsSt_cost, cGsEpoch_cost, CryptoGames.SM.Engine.cGsIdx,
    isSomeE_cost, Expr.cost, dsl_cost, v0_cost, v1_cost, v2_cost, v3_cost, v4_cost, v6_cost,
    Expr.v7, bits_one, Nat.reduceAdd] at hep hvs hrec hdl hij hca hac hrv hdf
  dsimp only [splitHandleC]
  simp only [CryptoGames.SM.Construction.isHonestHdrPRNGBucketE,
    CryptoGames.SM.Construction.prngBucketHsCache, CryptoGames.SM.Engine.vpTcurNat,
    CryptoGames.SM.Engine.vpTcur, pGet_cost, cGsSt_cost,
    CryptoGames.SM.orE, CryptoGames.SM.Engine.cGsIdx,
    CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.esMk, esG_cost, esH_cost, esAbort_cost,
    Comp.cost, Expr.cost, dsl_cost, v0_cost, v1_cost, v2_cost, v3_cost, v4_cost, v5_cost, v6_cost,
    Expr.v7, bits_zero, bits_one, Nat.reduceAdd]; omega

private theorem prngBucketSplitHandle_cost_le
    (H L B Δcka Δbucket qep maxSkip C_inj : ℕ) (hΔ : 2 + Δcka ≤ 4)
    (tL : Option ℕ) (par gMain : Bool) (t0 : ℕ)
    (hcfg : ∀ {Γ'} (e : Expr OO_cka Γ' .nat),
      ((CryptoGames.SM.Construction.bucketParPaperAuthCfgEC Δbucket tL par).injectFullE e).cost ≤
        3 * e.cost + C_inj)
    (hhk : HooksCostBounded
      (CryptoGames.SM.Construction.hooksPRNGBucketSplitPaperC (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δbucket qep tL par gMain t0) H) :
    (CryptoGames.SM.Construction.redPRNGAuthDFPaperBucketSplitProgGen (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B Δcka Δbucket qep maxSkip tL par gMain t0).handle.cost ≤
      3 * H + 6000 * L + 5 * bits qep + 2 * (maxSkip + 1) + C_inj + 8000 :=
  splitHandleC_cost_le _ H L (2 + Δcka) qep maxSkip C_inj hΔ gMain _ hcfg hhk

set_option linter.unusedSimpArgs false in
private theorem splitHandleC_excessUB_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sC : I'.smp.Samp → ℕ} {qC : I'.Tag → ℕ}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' (.base .γ) (.opt (.base .sig)) (.base .ss) (.base .rs)
      (@CryptoGames.SM.Construction.prngBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E))
    (Ho Hs Hr L Δ qep maxSkip : ℕ) (gMain : Bool) (cfg : CryptoGames.SM.Engine.ConfigEC OO_cka)
    (hcfg : ∀ {Γ'} (e : Expr OO_cka Γ' .nat),
      exprExcessUB (ckaOpC B0) (cfg.injectFullE e) ≤ 4 * exprExcessUB (ckaOpC B0) e)
    (hhk : HooksExcessBounded B0 sC qC hk Ho Hs Hr) :
    compExcessUB (ckaOpC B0) sC qC
      (splitHandleC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        hk L Δ qep maxSkip gMain cfg) ≤
      8 * Ho + Hs + 3 * Hr + 600 * L + 35000 := by
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E
    (.base .γ) (.opt (.base .sig)) (.base .ss) (.base .rs)
  let hsT := @CryptoGames.SM.Construction.prngBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E
  let esT := CryptoGames.SM.Engine.esTy vpT hsT
  let qT := (CryptoGames.CKA.ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).Q
  let txQ : Ty S_cka := .prod .bool (.prod (.base .msg) (.opt (.base .ccoins)))
  let chQ : Ty S_cka := .prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .ccoins))))
  let dlQ : Ty S_cka := .prod .bool ckaHdrCtT
  let dfQ : Ty S_cka := .prod .bool (.prod ckaHdrCtT ckaHdrCtT)
  let smqT : Ty S_cka := .sum (.sum (.sum (.sum txQ chQ) dlQ) dlQ) .bool
  let Γ0 : List (Ty S_cka) := .prod esT (.prod (.opt .nat) qT) :: [.prod esT (.opt .nat), qT]
  let Γ_df : List (Ty S_cka) := dfQ :: Γ0; let Γ_cr : List (Ty S_cka) := .bool :: smqT :: Γ0
  let Γ_ij : List (Ty S_cka) := dlQ :: .sum (.sum (.sum txQ chQ) dlQ) dlQ :: smqT :: Γ0
  let Γ_dl : List (Ty S_cka) := dlQ :: .sum (.sum txQ chQ) dlQ :: .sum (.sum (.sum txQ chQ) dlQ) dlQ :: smqT :: Γ0
  let Γ_tx0 : List (Ty S_cka) := txQ :: txQ :: .sum txQ chQ :: .sum (.sum txQ chQ) dlQ :: .sum (.sum (.sum txQ chQ) dlQ) dlQ :: smqT :: Γ0
  let Γ_tx1 : List (Ty S_cka) := CryptoGames.SM.Engine.cGsTy vpT :: Γ_tx0
  have hvs := vSendC_excessUB_le hk Ho Hs Hr hhk (Γ' := Γ_tx1) (CryptoGames.SM.Engine.esH (.fst .v7)) .v0
    (.fst .v1) (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt .v0) (.fst .v1)) (.fst (.snd .v1)) .none (.snd (.snd .v1))
  have hdl := deliverEC_any_excessUB_le hk Ho Hs Hr L maxSkip cfg hhk (Γ' := Γ_dl) (.fst .v4) .v0
  have hij := injectEC_anyCfg_excessUB_le hk Ho Hs Hr L Δ qep cfg hcfg hhk (Γ' := Γ_ij) (.fst .v3) .v0
  have hca := corrAllowedChoiceE_excessUB (vpT := vpT) B0 true L (Γ' := Γ_cr)
    (CryptoGames.SM.Engine.esG (O' := OO_cka) (.fst .v2)) .v0
  have hrv := hhk.reveal_le (Γ' := Γ_cr) (CryptoGames.SM.Engine.esH (.fst .v2))
    (CryptoGames.SM.Engine.esG (.fst .v2)) .v0
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v2))) .v0)
  have hdf := deliverForgeEC_anyCfg_excessUB_le hk Ho Hs Hr L Δ qep cfg hcfg hhk (Γ' := Γ_df) (.fst .v1) .v0
  dsimp only [corrAllowedChoiceE] at hca
  simp only [CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.cGsSt,
    CryptoGames.SM.pGet, exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3,
    exprExcessUB_v4, exprExcessUB_v7, exprExcessUB_var, exprExcessUB_none, exprExcessUB_ite,
    exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_letE,
    Nat.add_zero, Nat.zero_add, Nat.mul_zero] at hvs hdl hij hca hrv hdf
  dsimp only [splitHandleC]
  simp only [CryptoGames.SM.Construction.isHonestHdrPRNGBucketE,
    CryptoGames.SM.Construction.prngBucketHsCache, CryptoGames.SM.Engine.vpTcurNat,
    CryptoGames.SM.Engine.vpTcur, ckaOpC,
    CryptoGames.SM.Engine.cEpMgmtE, CryptoGames.SM.Engine.cRecordE,
    CryptoGames.SM.Engine.cAfterCorrE, CryptoGames.SM.Engine.cSafeChE, CryptoGames.SM.Engine.cLeakE,
    CryptoGames.SM.Engine.cCompInsertE, CryptoGames.SM.Engine.cCompSetE,
    CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH,
    CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.cGsMk, CryptoGames.SM.Engine.cGsSt,
    CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.cGsEpoch,
    CryptoGames.SM.Engine.cGsIdx, CryptoGames.SM.Engine.cGsTL, CryptoGames.SM.Engine.cGsTrans,
    CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.Engine.cGsComp, CryptoGames.SM.Engine.cGsMaxAcc,
    CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs, CryptoGames.SM.Engine.cRecPos,
    CryptoGames.SM.sendsInE, CryptoGames.SM.healedByE, CryptoGames.SM.maxOptE, CryptoGames.SM.maxN,
    CryptoGames.SM.leN, CryptoGames.SM.pSet, CryptoGames.SM.pGet, CryptoGames.SM.orE,
    CryptoGames.SM.isSomeE, CryptoGames.SM.boolEq,
    CryptoGames.SM.otherE, CryptoGames.SM.posSender, CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx,
    exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
    exprExcessUB_v5, exprExcessUB_v6, exprExcessUB_v7, exprExcessUB_var, exprExcessUB_unit,
    exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none, exprExcessUB_nil, exprExcessUB_add,
    exprExcessUB_modK, exprExcessUB_lt, exprExcessUB_eqN, exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite,
    exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_inl, exprExcessUB_inr,
    exprExcessUB_some, exprExcessUB_cons, exprExcessUB_caseOpt, exprExcessUB_letE, exprExcessUB_op,
    exprExcessUB_foldrB, exprExcessUB_tget, exprExcessUB_tset,
    compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt, compExcessUB_caseSum,
    Nat.reduceAdd, Nat.add_zero, Nat.zero_add, Nat.mul_zero]; omega

private theorem prngBucketSplitHandle_excessUB_le
    (B0 Ho Hs Hr L B Δcka Δbucket qep maxSkip : ℕ)
    (tL : Option ℕ) (par gMain : Bool) (t0 : ℕ)
    (hcfg : ∀ {Γ'} (e : Expr OO_cka Γ' .nat),
      exprExcessUB (ckaOpC B0)
        ((CryptoGames.SM.Construction.bucketParPaperAuthCfgEC Δbucket tL par).injectFullE e) ≤
        4 * exprExcessUB (ckaOpC B0) e)
    (hhk : HooksExcessBounded B0 ckaSampC prngQueryC
      (CryptoGames.SM.Construction.hooksPRNGBucketSplitPaperC (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δbucket qep tL par gMain t0) Ho Hs Hr) :
    compExcessUB (ckaOpC B0) ckaSampC prngQueryC
      (CryptoGames.SM.Construction.redPRNGAuthDFPaperBucketSplitProgGen (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δcka Δbucket qep maxSkip tL par gMain t0).handle ≤
      8 * Ho + Hs + 3 * Hr + 600 * L + 35000 :=
  splitHandleC_excessUB_le _ Ho Hs Hr L (2 + Δcka) qep maxSkip gMain _ hcfg hhk

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
private theorem splitHandleC_sizeW_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sS : I'.smp.Samp → ℕ} {qS : I'.Tag → ℕ}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' (.base .γ) (.opt (.base .sig)) (.base .ss) (.base .rs)
      (@CryptoGames.SM.Construction.prngBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E))
    (Ho Hs Hr L Δ qep maxSkip S_inj : ℕ) (hΔ : Δ ≤ 4) (gMain : Bool)
    (cfg : CryptoGames.SM.Engine.ConfigEC OO_cka)
    (hcfg : ∀ {Γ'} (e : Expr OO_cka Γ' .nat),
      Bundles.exprSizeW (Bundles.ckaOpS B0) (cfg.injectFullE e) ≤
        4 * Bundles.exprSizeW (Bundles.ckaOpS B0) e + S_inj)
    (hhk : HooksSizeBounded B0 sS qS hk Ho Hs Hr) :
    Bundles.compSizeW (Bundles.ckaOpS B0) sS qS
      (splitHandleC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        hk L Δ qep maxSkip gMain cfg) ≤
      10 * Ho + 2 * Hs + 4 * Hr + 60 * bits L + 20 * bits qep + 10 * bits maxSkip + 8 * S_inj + 40000 := by
  have hc : Δ = 0 ∨ Δ = 1 ∨ Δ = 2 ∨ Δ = 3 ∨ Δ = 4 := by omega
  have hbΔ : bits Δ ≤ 4 := by rcases hc with rfl | rfl | rfl | rfl | rfl <;> decide
  have hb1Δ : bits (Δ + 1) ≤ 4 := by rcases hc with rfl | rfl | rfl | rfl | rfl <;> decide
  have hb2Δ : bits (2 + Δ) ≤ 4 := by rcases hc with rfl | rfl | rfl | rfl | rfl <;> decide
  have hqep1 := bits_succ_le qep
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E
    (.base .γ) (.opt (.base .sig)) (.base .ss) (.base .rs)
  let hsT := @CryptoGames.SM.Construction.prngBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E
  let esT := CryptoGames.SM.Engine.esTy vpT hsT
  let qT := (CryptoGames.CKA.ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E).Q
  let txQ : Ty S_cka := .prod .bool (.prod (.base .msg) (.opt (.base .ccoins)))
  let chQ : Ty S_cka := .prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .ccoins))))
  let dlQ : Ty S_cka := .prod .bool ckaHdrCtT
  let dfQ : Ty S_cka := .prod .bool (.prod ckaHdrCtT ckaHdrCtT)
  let smqT : Ty S_cka := .sum (.sum (.sum (.sum txQ chQ) dlQ) dlQ) .bool
  let Γ0 : List (Ty S_cka) := .prod esT (.prod (.opt .nat) qT) :: [.prod esT (.opt .nat), qT]
  let Γ_df : List (Ty S_cka) := dfQ :: Γ0; let Γ_cr : List (Ty S_cka) := .bool :: smqT :: Γ0
  let Γ_ij : List (Ty S_cka) := dlQ :: .sum (.sum (.sum txQ chQ) dlQ) dlQ :: smqT :: Γ0
  let Γ_dl : List (Ty S_cka) := dlQ :: .sum (.sum txQ chQ) dlQ :: .sum (.sum (.sum txQ chQ) dlQ) dlQ :: smqT :: Γ0
  let Γ_tx0 : List (Ty S_cka) := txQ :: txQ :: .sum txQ chQ :: .sum (.sum txQ chQ) dlQ :: .sum (.sum (.sum txQ chQ) dlQ) dlQ :: smqT :: Γ0
  let Γ_tx1 : List (Ty S_cka) := CryptoGames.SM.Engine.cGsTy vpT :: Γ_tx0
  have hvs := vSendC_sizeW_le hk Ho Hs Hr hhk (Γ' := Γ_tx1) (CryptoGames.SM.Engine.esH (.fst .v7)) .v0
    (.fst .v1) (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt .v0) (.fst .v1)) (.fst (.snd .v1)) .none (.snd (.snd .v1))
  have hdl := deliverEC_any_sizeW_le hk Ho Hs Hr L maxSkip cfg hhk (Γ' := Γ_dl) (.fst .v4) .v0
  have hij := injectEC_anyCfg_sizeW_le hk Ho Hs Hr L Δ qep S_inj hΔ cfg hcfg hhk (Γ' := Γ_ij) (.fst .v3) .v0
  have hca := corrAllowedChoiceE_sizeW_le (vpT := vpT) B0 true L (Γ' := Γ_cr)
    (CryptoGames.SM.Engine.esG (O' := OO_cka) (.fst .v2)) .v0
  have hrv := hhk.reveal_le (Γ' := Γ_cr) (CryptoGames.SM.Engine.esH (.fst .v2))
    (CryptoGames.SM.Engine.esG (.fst .v2)) .v0
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v2))) .v0)
  have hdf := deliverForgeEC_anyCfg_sizeW_le hk Ho Hs Hr L Δ qep S_inj hΔ cfg hcfg hhk (Γ' := Γ_df) (.fst .v1) .v0
  dsimp only [corrAllowedChoiceE] at hca
  simp only [CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.cGsSt,
    CryptoGames.SM.pGet, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4,
    exprSizeW_v7, exprSizeW_var, exprSizeW_none, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst,
    exprSizeW_snd, exprSizeW_letE, Nat.reduceAdd] at hvs hdl hij hca hrv hdf
  dsimp only [splitHandleC]
  simp only [CryptoGames.SM.Construction.isHonestHdrPRNGBucketE,
    CryptoGames.SM.Construction.prngBucketHsCache, CryptoGames.SM.Engine.vpTcurNat,
    CryptoGames.SM.Engine.vpTcur, Bundles.ckaOpS,
    CryptoGames.SM.Engine.cEpMgmtE, CryptoGames.SM.Engine.cRecordE,
    CryptoGames.SM.Engine.cAfterCorrE, CryptoGames.SM.Engine.cSafeChE, CryptoGames.SM.Engine.cLeakE,
    CryptoGames.SM.Engine.cCompInsertE, CryptoGames.SM.Engine.cCompSetE,
    CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH,
    CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.cGsMk, CryptoGames.SM.Engine.cGsSt,
    CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.cGsEpoch,
    CryptoGames.SM.Engine.cGsIdx, CryptoGames.SM.Engine.cGsTL, CryptoGames.SM.Engine.cGsTrans,
    CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.Engine.cGsComp, CryptoGames.SM.Engine.cGsMaxAcc,
    CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs, CryptoGames.SM.Engine.cRecPos,
    CryptoGames.SM.sendsInE, CryptoGames.SM.healedByE, CryptoGames.SM.maxOptE, CryptoGames.SM.maxN,
    CryptoGames.SM.leN, CryptoGames.SM.pSet, CryptoGames.SM.pGet, CryptoGames.SM.orE,
    CryptoGames.SM.isSomeE, CryptoGames.SM.boolEq,
    CryptoGames.SM.otherE, CryptoGames.SM.posSender, CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4, exprSizeW_v5,
    exprSizeW_v6, exprSizeW_v7, exprSizeW_var, exprSizeW_unit, exprSizeW_bool, exprSizeW_nat,
    exprSizeW_none, exprSizeW_nil, exprSizeW_add, exprSizeW_sub, exprSizeW_modK, exprSizeW_lt,
    exprSizeW_eqN, exprSizeW_not, exprSizeW_and, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst,
    exprSizeW_snd, exprSizeW_inl, exprSizeW_inr, exprSizeW_some, exprSizeW_cons, exprSizeW_caseOpt,
    exprSizeW_caseSum, exprSizeW_letE, exprSizeW_op, exprSizeW_foldrB, exprSizeW_tconst, exprSizeW_tget,
    exprSizeW_tset, compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt,
    compSizeW_caseSum, bits_zero, bits_one, bits_two, bits_three, bits_four, Nat.reduceAdd]; omega

private theorem prngBucketSplitHandle_sizeW_le
    (B0 Ho Hs Hr L B Δcka Δbucket qep maxSkip S_inj : ℕ) (hΔ : 2 + Δcka ≤ 4)
    (tL : Option ℕ) (par gMain : Bool) (t0 : ℕ)
    (hcfg : ∀ {Γ'} (e : Expr OO_cka Γ' .nat),
      Bundles.exprSizeW (Bundles.ckaOpS B0)
        ((CryptoGames.SM.Construction.bucketParPaperAuthCfgEC Δbucket tL par).injectFullE e) ≤
        4 * Bundles.exprSizeW (Bundles.ckaOpS B0) e + S_inj)
    (hhk : HooksSizeBounded B0 Bundles.ckaSampS Bundles.ckaQueryS
      (CryptoGames.SM.Construction.hooksPRNGBucketSplitPaperC (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δbucket qep tL par gMain t0) Ho Hs Hr) :
    Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS
      (CryptoGames.SM.Construction.redPRNGAuthDFPaperBucketSplitProgGen (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B Δcka Δbucket qep maxSkip tL par gMain t0).handle ≤
      10 * Ho + 2 * Hs + 4 * Hr + 60 * bits L + 20 * bits qep + 10 * bits maxSkip + 8 * S_inj + 40000 :=
  splitHandleC_sizeW_le _ Ho Hs Hr L (2 + Δcka) qep maxSkip S_inj hΔ gMain _ hcfg hhk

private theorem redPRNGAuthDFPaperBucketHybridProg_parts_le (B0 q qep : ℕ) (tL : Option ℕ)
    (par : Bool) (t : ℕ) (hB0 : B0 = (q + 1) * (maxForwardJumps + 1))
    (ht : t < qep + 2) (htL : tL.getD 0 ≤ qep + 2) :
    let P := CryptoGames.SM.Construction.redPRNGAuthDFPaperBucketHybridProg
      (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) (q + 1) B0 1 qep maxForwardJumps tL par t
    compCostW (ckaOpC B0) ckaSampC prngQueryC P.init +
      compCostW (ckaOpC B0) ckaSampC prngQueryC P.finish + 100000 ≤ fig8AtomicStepBound q qep ∧
    compCostW (ckaOpC B0) ckaSampC prngQueryC P.handle + 200000 ≤ fig8AtomicStepBound q qep := by
  subst hB0
  intro P
  have ht_bits := bits_le_bits_qep_add (x := t) (qep := qep) (by omega)
  have htL_bits := bits_le_bits_qep_add (x := tL.getD 0) (qep := qep) (by omega)
  have htH_bits := bits_healEpoch_le tL
  have hCommon := redPRNGAuthDFBucketCommon_parts_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
    (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
    true ⟨0, by decide⟩ _ q qep tL par t rfl ht htL
  refine ⟨?_, hCommon.2⟩
  let e0 := CryptoGames.SM.Construction.initPRNGBucketHybridEStateC (ckaInitA := ckaInitA)
    (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
    (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
    (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) (Γ' := [.unit]) (q + 1) (3 + 1) tL par t (.bool false)
  have hiC := (bind_ret_bucketInit_cost_le e0).trans
    (Nat.add_le_add_right (initPRNGBucketHybridEStateC_cost_le (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) (Γ' := [.unit]) (q + 1) (3 + 1) tL par t (.bool false)) 8)
  have hiE := (bind_ret_bucketInit_excessUB_le
    (opC := ckaOpC ((q + 1) * (maxForwardJumps + 1))) (sC := ckaSampC)
    (qC := prngQueryC) e0).trans (initPRNGBucketHybridEStateC_excessUB_le
      (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      ((q + 1) * (maxForwardJumps + 1)) (q + 1) (3 + 1) tL par t (.bool (Γ := [.unit]) false))
  have hiW := compCostW_le_cost_add_excessUB (ckaOpC ((q + 1) * (maxForwardJumps + 1)))
    ckaSampC prngQueryC P.init
  have hfC := prngBucketLcFinishC_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE)
    (I' := CryptoGames.PRFPRNG.prngIface KC Γ CCoins T I KR RSt K
      SS RS M E sampKR sampKC sampCCoins sampI sampK) none (q + 1) (2 + 1) (by omega) tL t
  have hfE := prngBucketLcFinishC_excessUB_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE)
    (I' := CryptoGames.PRFPRNG.prngIface KC Γ CCoins T I KR RSt K
      SS RS M E sampKR sampKC sampCCoins sampI sampK)
    ((q + 1) * (maxForwardJumps + 1)) ckaSampC prngQueryC none (q + 1) (2 + 1) tL t
  have hfW := compCostW_le_cost_add_excessUB (ckaOpC ((q + 1) * (maxForwardJumps + 1)))
    ckaSampC prngQueryC P.finish
  simp only [Expr.cost, exprExcessUB_bool, Nat.reduceAdd, bits_four] at hiC hiE
  dsimp only [P, CryptoGames.SM.Construction.redPRNGAuthDFPaperBucketHybridProg,
    CryptoGames.SM.Construction.redPRNGAuthDFPaperBucketHybridProgGen,
    prngBucketLcFinishC, e0] at hiC hiE hiW hfC hfE hfW ⊢
  generalize (q + 1) * (maxForwardJumps + 1) = B0 at hiE hfE hiW hfW ⊢
  simp only [fig8AtomicStepBound, maxForwardJumps, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  clear hCommon
  omega

private theorem redPRNGAuthDFPaperBucketHybridProg_size_le (B0 q qep : ℕ) (tL : Option ℕ)
    (par : Bool) (t : ℕ) (hB0 : B0 = (q + 1) * (maxForwardJumps + 1))
    (ht : t < qep + 2) (htL : tL.getD 0 ≤ qep + 2) (hqep : qep ≤ 4096 * q + 100000000) :
    let P := CryptoGames.SM.Construction.redPRNGAuthDFPaperBucketHybridProg
      (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) (q + 1) B0 1 qep maxForwardJumps tL par t
    Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS P.init +
      Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS P.handle +
      Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS P.finish + 520 ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep) := by
  subst hB0
  intro P
  have hqep1 := bits_succ_le qep
  have hbL : bits (q + 1) ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbqep : bits qep ≤ bits (ratchetCostBudget q qep) := bits_qep_le_ratchetCostBudget hqep
  have hbt : bits t ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbtL : bits (tL.getD 0) ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbtH : bits (healEpoch tL) ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (by cases tL <;> (simp [healEpoch] at htL ⊢; try omega))
  have hbB : bits ((q + 1) * (maxForwardJumps + 1)) ≤ bits (ratchetCostBudget q qep) :=
    bits_B0_le_ratchetCostBudget q qep
  have hi : Bundles.compSizeW (Bundles.ckaOpS ((q + 1) * (maxForwardJumps + 1)))
      Bundles.ckaSampS Bundles.ckaQueryS P.init ≤
      20 * bits (ratchetCostBudget q qep) + 9000 := by
    refine (bind_ret_bucketInit_sizeW_le _).trans ?_
    have h0 := initPRNGBucketHybridEStateC_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      (Γ' := [.unit]) ((q + 1) * (maxForwardJumps + 1)) (q + 1) (3 + 1) tL par t (.bool false)
    dsimp only [P, CryptoGames.SM.Construction.redPRNGAuthDFPaperBucketHybridProg,
      CryptoGames.SM.Construction.redPRNGAuthDFPaperBucketHybridProgGen]
    simp only [exprSizeW_bool, Nat.reduceAdd, bits_four] at h0 ⊢
    generalize bits (ratchetCostBudget q qep) = bR at hbL hbt hbtH hbtL ⊢; omega
  have hh : Bundles.compSizeW (Bundles.ckaOpS ((q + 1) * (maxForwardJumps + 1)))
      Bundles.ckaSampS Bundles.ckaQueryS P.handle ≤
      500 * bits (ratchetCostBudget q qep) + 240000 :=
    bucketHandleC_sizeW_le_ratchet true _ q qep tL par htL hqep
      ((hooksPRNGBucketParPaperC_sizeBounded _ (q + 1) _ qep tL par t).mono
        (by generalize bits (ratchetCostBudget q qep) = bR at hbL hbtH hbt hbtL hbqep hqep1 ⊢; omega)
        le_rfl
        (by generalize bits (ratchetCostBudget q qep) = bR at hbB ⊢
            generalize (q + 1) * (maxForwardJumps + 1) = B at hbB ⊢; omega))
  have hf : Bundles.compSizeW (Bundles.ckaOpS ((q + 1) * (maxForwardJumps + 1)))
      Bundles.ckaSampS Bundles.ckaQueryS P.finish ≤
      18 * bits (ratchetCostBudget q qep) + 700 := by
    have h0 := prngBucketLcFinishC_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE)
      (I' := CryptoGames.PRFPRNG.prngIface KC Γ CCoins T I KR RSt K
        SS RS M E sampKR sampKC sampCCoins sampI sampK)
      ((q + 1) * (maxForwardJumps + 1)) Bundles.ckaSampS Bundles.ckaQueryS
      none (q + 1) (2 + 1) (by omega) tL t
    dsimp only [P, CryptoGames.SM.Construction.redPRNGAuthDFPaperBucketHybridProg,
      CryptoGames.SM.Construction.redPRNGAuthDFPaperBucketHybridProgGen,
      prngBucketLcFinishC] at h0 ⊢
    generalize bits (ratchetCostBudget q qep) = bR at hbL hbtL hbt ⊢; omega
  refine size_le_ratchetSizeBudget (C₀ := 300000) (C₁ := 1100) (by decide) (by decide) ?_
  generalize bits (ratchetCostBudget q qep) = bR at hi hh hf ⊢; omega

set_option maxRecDepth 100000 in
private theorem redPRNGAuthDFPaperBucketSplitProg_parts_le (B0 q qep : ℕ) (tL : Option ℕ)
    (par gMain : Bool) (t0 : ℕ) (hB0 : B0 = (q + 1) * (maxForwardJumps + 1))
    (ht0 : t0 < qep + 2) (htL : tL.getD 0 ≤ qep + 2) :
    let P := CryptoGames.SM.Construction.redPRNGAuthDFPaperBucketSplitProg
      (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) (q + 1) B0 1 qep maxForwardJumps tL par gMain t0
    compCostW (ckaOpC B0) ckaSampC prngQueryC P.init +
      compCostW (ckaOpC B0) ckaSampC prngQueryC P.finish + 100000 ≤ fig8AtomicStepBound q qep ∧
    compCostW (ckaOpC B0) ckaSampC prngQueryC P.handle + 200000 ≤ fig8AtomicStepBound q qep := by
  subst hB0
  intro P
  have hqep1 := bits_succ_le qep
  have ht0_bits := bits_le_bits_qep_add (x := t0) (qep := qep) (by omega)
  have htL_bits := bits_le_bits_qep_add (x := tL.getD 0) (qep := qep) (by omega)
  have htH_bits := bits_healEpoch_le tL
  constructor
  · let e0 := CryptoGames.SM.Construction.initPRNGBucketHybridEStateC (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) (Γ' := [.unit]) (q + 1) (3 + 1) tL par t0 (.bool false)
    have hiC := (bind_ret_bucketInit_cost_le e0).trans
      (Nat.add_le_add_right (initPRNGBucketHybridEStateC_cost_le (ckaInitA := ckaInitA)
        (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
        (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
        (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
        (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) (Γ' := [.unit]) (q + 1) (3 + 1) tL par t0 (.bool false)) 8)
    have hiE := (bind_ret_bucketInit_excessUB_le
      (opC := ckaOpC ((q + 1) * (maxForwardJumps + 1))) (sC := ckaSampC)
      (qC := prngQueryC) e0).trans (initPRNGBucketHybridEStateC_excessUB_le
        (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
        (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
        ((q + 1) * (maxForwardJumps + 1)) (q + 1) (3 + 1) tL par t0 (.bool (Γ := [.unit]) false))
    have hiW := compCostW_le_cost_add_excessUB (ckaOpC ((q + 1) * (maxForwardJumps + 1)))
      ckaSampC prngQueryC P.init
    have hfC := prngBucketLcFinishC_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE)
      (I' := CryptoGames.PRFPRNG.prngIface KC Γ CCoins T I KR RSt K
        SS RS M E sampKR sampKC sampCCoins sampI sampK) (some gMain) (q + 1) (2 + 1) (by omega) tL t0
    have hfE := prngBucketLcFinishC_excessUB_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE)
      (I' := CryptoGames.PRFPRNG.prngIface KC Γ CCoins T I KR RSt K
        SS RS M E sampKR sampKC sampCCoins sampI sampK)
      ((q + 1) * (maxForwardJumps + 1)) ckaSampC prngQueryC (some gMain) (q + 1) (2 + 1) tL t0
    have hfW := compCostW_le_cost_add_excessUB (ckaOpC ((q + 1) * (maxForwardJumps + 1)))
      ckaSampC prngQueryC P.finish
    simp only [Expr.cost, exprExcessUB_bool, Nat.reduceAdd, bits_four] at hiC hiE
    dsimp only [P, CryptoGames.SM.Construction.redPRNGAuthDFPaperBucketSplitProg,
      CryptoGames.SM.Construction.redPRNGAuthDFPaperBucketSplitProgGen,
      prngBucketLcFinishC, e0] at hiC hiE hiW hfC hfE hfW ⊢
    generalize (q + 1) * (maxForwardJumps + 1) = B0 at hiE hfE hiW hfW ⊢
    simp only [fig8AtomicStepBound, maxForwardJumps, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    omega
  · let L := q + 1; let B := (q + 1) * (maxForwardJumps + 1)
    let H := 30 * L + 15 * bits qep + B + 5000
    let Ho := 30 * L + 10000; let Hs := 400000; let Hr := 20 * B + 3 * bits B + 2710000
    have hmfj : maxForwardJumps = 25000 := rfl
    have hbB := bits_le_add_one B
    have hhkC : HooksCostBounded
        (CryptoGames.SM.Construction.hooksPRNGBucketSplitPaperC (ckaInitA := ckaInitA)
          (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
          (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
          (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
          (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L B (3 + 1) qep tL par gMain t0) H :=
      (hooksPRNGBucketSplitPaperC_costBounded L B qep tL par gMain t0).mono
        (by dsimp only [L, B, H]; generalize (q + 1) * (maxForwardJumps + 1) = Bv at ⊢; omega)
    have hhkE : HooksExcessBounded B ckaSampC prngQueryC
        (CryptoGames.SM.Construction.hooksPRNGBucketSplitPaperC (ckaInitA := ckaInitA)
          (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
          (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
          (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
          (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
          (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
          (sampI := sampI) (sampK := sampK) L B (3 + 1) qep tL par gMain t0) Ho Hs Hr :=
      (hooksPRNGBucketSplitPaperC_excessBounded B L B qep tL par gMain t0).mono
        (by dsimp only [L, Ho]; omega) (by decide) le_rfl
    have hC := prngBucketSplitHandle_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      H L B 1 (3 + 1) qep maxForwardJumps (2 * bits (tL.getD 0) + 80) (by omega) tL par gMain t0
      (fun e => validGuessBucketParPaperE_cost_le tL par e) hhkC
    have hE := prngBucketSplitHandle_excessUB_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      B Ho Hs Hr L B 1 (3 + 1) qep maxForwardJumps tL par gMain t0
      (fun e => validGuessBucketParPaperE_excessUB B tL par e) hhkE
    have hW := compCostW_le_cost_add_excessUB (ckaOpC B) ckaSampC prngQueryC P.handle
    unfold fig8AtomicStepBound
    dsimp only [P, CryptoGames.SM.Construction.redPRNGAuthDFPaperBucketSplitProg,
      L, B, H, Ho, Hs, Hr] at hC hE hW hbB ⊢
    generalize bits ((q + 1) * (maxForwardJumps + 1)) = bB at hE hbB
    generalize (q + 1) * (maxForwardJumps + 1) = Bv at hC hE hW hbB ⊢
    generalize (q + 1) * (3 * bits qep + 60) = Lbq at ⊢
    omega

private theorem redPRNGAuthDFPaperBucketSplitProg_size_le (B0 q qep : ℕ) (tL : Option ℕ)
    (par gMain : Bool) (t0 : ℕ) (hB0 : B0 = (q + 1) * (maxForwardJumps + 1))
    (ht0 : t0 < qep + 2) (htL : tL.getD 0 ≤ qep + 2) (hqep : qep ≤ 4096 * q + 100000000) :
    let P := CryptoGames.SM.Construction.redPRNGAuthDFPaperBucketSplitProg
      (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) (q + 1) B0 1 qep maxForwardJumps tL par gMain t0
    Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS P.init +
      Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS P.handle +
      Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS P.finish + 520 ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep) := by
  subst hB0
  intro P
  have hqep1 := bits_succ_le qep
  have hbL : bits (q + 1) ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbqep : bits qep ≤ bits (ratchetCostBudget q qep) := bits_qep_le_ratchetCostBudget hqep
  have hbt0 : bits t0 ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbtL : bits (tL.getD 0) ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbtH : bits (healEpoch tL) ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (by cases tL <;> (simp [healEpoch] at htL ⊢; try omega))
  have hbB : bits ((q + 1) * (maxForwardJumps + 1)) ≤ bits (ratchetCostBudget q qep) :=
    bits_B0_le_ratchetCostBudget q qep
  have hbm : bits maxForwardJumps ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (by unfold maxForwardJumps; omega)
  have hi : Bundles.compSizeW (Bundles.ckaOpS ((q + 1) * (maxForwardJumps + 1)))
      Bundles.ckaSampS Bundles.ckaQueryS P.init ≤
      20 * bits (ratchetCostBudget q qep) + 9000 := by
    refine (bind_ret_bucketInit_sizeW_le _).trans ?_
    have h0 := initPRNGBucketHybridEStateC_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      (Γ' := [.unit]) ((q + 1) * (maxForwardJumps + 1)) (q + 1) (3 + 1) tL par t0 (.bool false)
    dsimp only [P, CryptoGames.SM.Construction.redPRNGAuthDFPaperBucketSplitProg,
      CryptoGames.SM.Construction.redPRNGAuthDFPaperBucketSplitProgGen]
    simp only [exprSizeW_bool, Nat.reduceAdd, bits_four] at h0 ⊢
    generalize bits (ratchetCostBudget q qep) = bR at hbL hbt0 hbtH hbtL ⊢; omega
  have hh : Bundles.compSizeW (Bundles.ckaOpS ((q + 1) * (maxForwardJumps + 1)))
      Bundles.ckaSampS Bundles.ckaQueryS P.handle ≤
      500 * bits (ratchetCostBudget q qep) + 240000 := by
    have hS := prngBucketSplitHandle_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
      (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
      ((q + 1) * (maxForwardJumps + 1)) (30 * bits (ratchetCostBudget q qep) + 18000) 2000
      (5 * bits (ratchetCostBudget q qep) + 2000) (q + 1) ((q + 1) * (maxForwardJumps + 1))
      1 (3 + 1) qep maxForwardJumps (4 * bits (tL.getD 0) + 150) (by omega) tL par gMain t0
      (fun e => validGuessBucketParPaperE_sizeW_le _ tL par e)
      ((hooksPRNGBucketSplitPaperC_sizeBounded _ (q + 1) _ qep tL par gMain t0).mono
        (by generalize bits (ratchetCostBudget q qep) = bR at hbL hbtH hbt0 hbtL hbqep hqep1 ⊢; omega)
        le_rfl
        (by generalize bits (ratchetCostBudget q qep) = bR at hbB ⊢
            generalize (q + 1) * (maxForwardJumps + 1) = B at hbB ⊢; omega))
    dsimp only [P, CryptoGames.SM.Construction.redPRNGAuthDFPaperBucketSplitProg] at hS ⊢
    exact hS.trans (by
      generalize bits (ratchetCostBudget q qep) = bR at hbL hbqep hbm hbtL ⊢
      generalize bits (q + 1) = bL at hbL ⊢
      generalize bits qep = bq at hbqep ⊢
      generalize bits maxForwardJumps = bm at hbm ⊢
      generalize bits (tL.getD 0) = btL at hbtL ⊢
      omega)
  have hf : Bundles.compSizeW (Bundles.ckaOpS ((q + 1) * (maxForwardJumps + 1)))
      Bundles.ckaSampS Bundles.ckaQueryS P.finish ≤
      18 * bits (ratchetCostBudget q qep) + 700 := by
    have h0 := prngBucketLcFinishC_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE)
      (I' := CryptoGames.PRFPRNG.prngIface KC Γ CCoins T I KR RSt K
        SS RS M E sampKR sampKC sampCCoins sampI sampK)
      ((q + 1) * (maxForwardJumps + 1)) Bundles.ckaSampS Bundles.ckaQueryS
      (some gMain) (q + 1) (2 + 1) (by omega) tL t0
    dsimp only [P, CryptoGames.SM.Construction.redPRNGAuthDFPaperBucketSplitProg,
      CryptoGames.SM.Construction.redPRNGAuthDFPaperBucketSplitProgGen,
      prngBucketLcFinishC] at h0 ⊢
    generalize bits (ratchetCostBudget q qep) = bR at hbL hbtL hbt0 ⊢; omega
  refine size_le_ratchetSizeBudget (C₀ := 300000) (C₁ := 1100) (by decide) (by decide) ?_
  generalize bits (ratchetCostBudget q qep) = bR at hi hh hf ⊢; omega

private theorem bucketSlotEpoch_lt_of_lt (Δbucket : ℕ) (tL : Option ℕ) (par : Bool) {t bound : ℕ}
    (ht : t < bound) :
    CryptoGames.SM.Construction.DeliverForge.bucketSlotEpoch Δbucket tL par t < bound := by
  unfold CryptoGames.SM.Construction.DeliverForge.bucketSlotEpoch
  split_ifs <;> omega

private theorem redPRNGAuthDFPaperBucketPackedProg_parts_le (B0 q qep : ℕ) (tL : Option ℕ)
    (par : Bool) (t : ℕ) (hB0 : B0 = (q + 1) * (maxForwardJumps + 1))
    (ht : t < qep + 2) (htL : tL.getD 0 ≤ qep + 2) :
    let P := CryptoGames.SM.Construction.redPRNGAuthDFPaperBucketPackedProg
      (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) (q + 1) B0 1 qep maxForwardJumps tL par t
    compCostW (ckaOpC B0) ckaSampC prngQueryC P.init +
      compCostW (ckaOpC B0) ckaSampC prngQueryC P.finish + 100000 ≤ fig8AtomicStepBound q qep ∧
    compCostW (ckaOpC B0) ckaSampC prngQueryC P.handle + 200000 ≤ fig8AtomicStepBound q qep :=
  redPRNGAuthDFPaperBucketSplitProg_parts_le B0 q qep tL par
    (CryptoGames.SM.Construction.DeliverForge.bucketSlotIsMain (3 + 1) tL par t)
    (CryptoGames.SM.Construction.DeliverForge.bucketSlotEpoch (3 + 1) tL par t)
    hB0 (bucketSlotEpoch_lt_of_lt (3 + 1) tL par ht) htL

private theorem redPRNGAuthDFPaperBucketPackedProg_size_le (B0 q qep : ℕ) (tL : Option ℕ)
    (par : Bool) (t : ℕ) (hB0 : B0 = (q + 1) * (maxForwardJumps + 1))
    (ht : t < qep + 2) (htL : tL.getD 0 ≤ qep + 2) (hqep : qep ≤ 4096 * q + 100000000) :
    let P := CryptoGames.SM.Construction.redPRNGAuthDFPaperBucketPackedProg
      (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) (q + 1) B0 1 qep maxForwardJumps tL par t
    Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS P.init +
      Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS P.handle +
      Bundles.compSizeW (Bundles.ckaOpS B0) Bundles.ckaSampS Bundles.ckaQueryS P.finish + 520 ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep) :=
  redPRNGAuthDFPaperBucketSplitProg_size_le B0 q qep tL par
    (CryptoGames.SM.Construction.DeliverForge.bucketSlotIsMain (3 + 1) tL par t)
    (CryptoGames.SM.Construction.DeliverForge.bucketSlotEpoch (3 + 1) tL par t)
    hB0 (bucketSlotEpoch_lt_of_lt (3 + 1) tL par ht) htL hqep

end SplitBucketBounds

end GenericEngineBounds

/-! ## 4. Concrete `[B8]` `(tL, par)`-Bucket Atomic Programs & `GRedBounded` Certificates -/

section BucketConcreteAtomicProgs

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

local instance : Inhabited Pt := ⟨0⟩

@[expose] def redCKAAuthDFBucketAtomicProg (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt)
    (qep q : ℕ) (tL : Option ℕ) (par : Bool) :
    CostedReduction (atomicFig8Ops ℓ Pt C Dh encPt encT lam) (ckaTargetIface ℓ Pt)
      (CryptoGames.SM.specDF (CryptoGames.Ratchet.LibsignalSim.Fig8St Pt)
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (BitVec 256) (CryptoGames.Ratchet.LibsignalSim.Fig8C Pt))
      (fig8SmCodecDF ℓ Pt) .unit .unit .bool .bool :=
  let B0 := (q + 1) * (maxForwardJumps + 1)
  Bundles.compileCkaDFAtomic ℓ Pt C Dh encPt encT idOf lam B0
    (CryptoGames.SM.Construction.redCKAAuthDFBucketProg (q + 1) B0 1 qep maxForwardJumps tL par)

@[expose] def redCKAAuthDFPaperBucketAtomicProg (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt)
    (qep q : ℕ) (tL : Option ℕ) (par : Bool) :
    CostedReduction (atomicFig8Ops ℓ Pt C Dh encPt encT lam) (ckaTargetIface ℓ Pt)
      (CryptoGames.SM.specDF (CryptoGames.Ratchet.LibsignalSim.Fig8St Pt)
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (BitVec 256) (CryptoGames.Ratchet.LibsignalSim.Fig8C Pt))
      (fig8SmCodecDF ℓ Pt) .unit .unit .bool .bool :=
  let B0 := (q + 1) * (maxForwardJumps + 1)
  Bundles.compileCkaDFAtomic ℓ Pt C Dh encPt encT idOf lam B0
    (CryptoGames.SM.Construction.redCKAAuthDFPaperBucketProg (q + 1) B0 1 qep maxForwardJumps tL par)

@[expose] def redPRNGAuthDFBucketHybridAtomicProg (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt)
    (qep q : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) :
    CostedReduction (atomicFig8Ops ℓ Pt C Dh encPt encT lam) (prngTargetIface ℓ Pt)
      (CryptoGames.SM.specDF (CryptoGames.Ratchet.LibsignalSim.Fig8St Pt)
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (BitVec 256) (CryptoGames.Ratchet.LibsignalSim.Fig8C Pt))
      (fig8SmCodecDF ℓ Pt) .unit .unit .bool .bool :=
  let B0 := (q + 1) * (maxForwardJumps + 1)
  Bundles.compilePrngDFAtomic ℓ Pt C Dh encPt encT idOf lam B0
    (CryptoGames.SM.Construction.redPRNGAuthDFBucketHybridProg (q + 1) B0 1 qep maxForwardJumps tL par t)

theorem isActiveBucketEpoch_succ_disjoint (Δbucket : ℕ) (hΔb : 4 ≤ Δbucket := by omega)
    (tL : Option ℕ) (par : Bool) (t0 : ℕ) :
    CryptoGames.SM.Construction.DeliverForge.isActiveBucketEpoch Δbucket tL par t0 = true →
      CryptoGames.SM.Construction.DeliverForge.isActiveBucketEpoch Δbucket tL par (t0 + 1) = false :=
  CryptoGames.SM.Construction.DeliverForge.isActiveBucketEpoch_succ_eq_false hΔb

@[expose] def redPRNGAuthDFPaperBucketSplitAtomicProg (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt)
    (qep q : ℕ) (tL : Option ℕ) (par gMain : Bool) (t0 : ℕ) :
    CostedReduction (atomicFig8Ops ℓ Pt C Dh encPt encT lam) (prngTargetIface ℓ Pt)
      (CryptoGames.SM.specDF (CryptoGames.Ratchet.LibsignalSim.Fig8St Pt)
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (BitVec 256) (CryptoGames.Ratchet.LibsignalSim.Fig8C Pt))
      (fig8SmCodecDF ℓ Pt) .unit .unit .bool .bool :=
  let B0 := (q + 1) * (maxForwardJumps + 1)
  Bundles.compilePrngDFAtomic ℓ Pt C Dh encPt encT idOf lam B0
    (CryptoGames.SM.Construction.redPRNGAuthDFPaperBucketSplitProg (q + 1) B0 1 qep maxForwardJumps tL par gMain t0)

@[expose] def redPRNGAuthDFPaperBucketPackedAtomicProg (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt)
    (qep q : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) :
    CostedReduction (atomicFig8Ops ℓ Pt C Dh encPt encT lam) (prngTargetIface ℓ Pt)
      (CryptoGames.SM.specDF (CryptoGames.Ratchet.LibsignalSim.Fig8St Pt)
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (BitVec 256) (CryptoGames.Ratchet.LibsignalSim.Fig8C Pt))
      (fig8SmCodecDF ℓ Pt) .unit .unit .bool .bool :=
  let B0 := (q + 1) * (maxForwardJumps + 1)
  Bundles.compilePrngDFAtomic ℓ Pt C Dh encPt encT idOf lam B0
    (CryptoGames.SM.Construction.redPRNGAuthDFPaperBucketPackedProg (q + 1) B0 1 qep maxForwardJumps tL par t)

@[expose] def redPRNGAuthDFPaperBucketHybridAtomicProg (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt)
    (qep q : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ) :
    CostedReduction (atomicFig8Ops ℓ Pt C Dh encPt encT lam) (prngTargetIface ℓ Pt)
      (CryptoGames.SM.specDF (CryptoGames.Ratchet.LibsignalSim.Fig8St Pt)
        (CryptoGames.Ratchet.LibsignalInst.LibsignalMsgPublicPart × CryptoGames.CBC.Plain ℓ)
        (BitVec 256) (CryptoGames.Ratchet.LibsignalSim.Fig8C Pt))
      (fig8SmCodecDF ℓ Pt) .unit .unit .bool .bool :=
  let B0 := (q + 1) * (maxForwardJumps + 1)
  let tH : ℕ := healEpoch tL
  if CryptoGames.SM.Construction.DeliverForge.isActiveBucketEpoch (3 + 1) tL par t then
    Bundles.compilePrngDFAtomic ℓ Pt C Dh encPt encT idOf lam B0
      (CryptoGames.SM.Construction.redPRNGAuthDFPaperBucketSplitProg (q + 1) B0 1 qep maxForwardJumps tL par false t)
  else if decide (tH < t) && CryptoGames.SM.Construction.DeliverForge.isActiveBucketEpoch (3 + 1) tL par (t - 1) then
    Bundles.compilePrngDFAtomic ℓ Pt C Dh encPt encT idOf lam B0
      (CryptoGames.SM.Construction.redPRNGAuthDFPaperBucketSplitProg (q + 1) B0 1 qep maxForwardJumps tL par true (t - 1))
  else
    dummyPrngStage2AtomicProg Dh encPt C ℓ encT idOf lam

theorem redCKAAuthDFBucketAtomicProg_gRedBounded (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt)
    (qep q : ℕ) (tL : Option ℕ) (par : Bool) (htL : tL.getD 0 ≤ qep + 2 := by omega)
    (hqep : qep ≤ 4096 * q + 100000000 := by omega) :
    GRedBounded (redCKAAuthDFBucketAtomicProg Dh encPt C ℓ encT idOf lam qep q tL par)
      (fun _ => 1) (fun _ => 0) q (2 + 2 * q) (ratchetCostBudget q qep) := by
  dsimp only [redCKAAuthDFBucketAtomicProg]
  exact DFProgBoundsBase.compileCkaDFAtomic_gRedBounded ℓ Pt C Dh encPt encT idOf lam _ _ q qep (2 + 2 * q)
    (redCKAAuthDFBucketProg_parts_le _ q qep tL par rfl htL)
    (redCKAAuthDFBucketProg_size_le _ q qep tL par rfl htL hqep)
    (by rw [CryptoGames.SM.Construction.redCKAAuthDFBucketProg_totalQueries]; omega)

theorem redCKAAuthDFPaperBucketAtomicProg_gRedBounded (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt)
    (qep q : ℕ) (tL : Option ℕ) (par : Bool) (htL : tL.getD 0 ≤ qep + 2 := by omega)
    (hqep : qep ≤ 4096 * q + 100000000 := by omega) :
    GRedBounded (redCKAAuthDFPaperBucketAtomicProg Dh encPt C ℓ encT idOf lam qep q tL par)
      (fun _ => 1) (fun _ => 0) q (2 + 2 * q) (ratchetCostBudget q qep) := by
  dsimp only [redCKAAuthDFPaperBucketAtomicProg]
  exact DFProgBoundsBase.compileCkaDFAtomic_gRedBounded ℓ Pt C Dh encPt encT idOf lam _ _ q qep (2 + 2 * q)
    (redCKAAuthDFPaperBucketProg_parts_le _ q qep tL par rfl htL)
    (redCKAAuthDFPaperBucketProg_size_le _ q qep tL par rfl htL hqep)
    (by rw [CryptoGames.SM.Construction.redCKAAuthDFPaperBucketProg_totalQueries]; omega)

theorem redPRNGAuthDFBucketHybridAtomicProg_gRedBounded (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt)
    (qep q : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (ht : t < qep + 2 := by omega) (htL : tL.getD 0 ≤ qep + 2 := by omega)
    (hqep : qep ≤ 4096 * q + 100000000 := by omega) :
    GRedBounded (redPRNGAuthDFBucketHybridAtomicProg Dh encPt C ℓ encT idOf lam qep q tL par t)
      (fun _ => 1) (fun _ => 0) q (2 + 2 * q) (ratchetCostBudget q qep) := by
  dsimp only [redPRNGAuthDFBucketHybridAtomicProg]
  exact DFProgBoundsBase.compilePrngDFAtomic_gRedBounded ℓ Pt C Dh encPt encT idOf lam _ _ q qep (2 + 2 * q)
    (redPRNGAuthDFBucketHybridProg_parts_le _ q qep tL par t rfl ht htL)
    (redPRNGAuthDFBucketHybridProg_size_le _ q qep tL par t rfl ht htL hqep)
    (by rw [CryptoGames.SM.Construction.redPRNGAuthDFBucketHybridProg_totalQueries]; omega)

theorem redPRNGAuthDFPaperBucketSplitAtomicProg_gRedBounded (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt)
    (qep q : ℕ) (tL : Option ℕ) (par gMain : Bool) (t0 : ℕ)
    (ht0 : t0 < qep + 2 := by omega) (htL : tL.getD 0 ≤ qep + 2 := by omega)
    (hqep : qep ≤ 4096 * q + 100000000 := by omega) :
    GRedBounded (redPRNGAuthDFPaperBucketSplitAtomicProg Dh encPt C ℓ encT idOf lam qep q tL par gMain t0)
      (fun _ => 1) (fun _ => 0) q (2 + 2 * q) (ratchetCostBudget q qep) := by
  dsimp only [redPRNGAuthDFPaperBucketSplitAtomicProg]
  exact DFProgBoundsBase.compilePrngDFAtomic_gRedBounded ℓ Pt C Dh encPt encT idOf lam _ _ q qep (2 + 2 * q)
    (redPRNGAuthDFPaperBucketSplitProg_parts_le _ q qep tL par gMain t0 rfl ht0 htL)
    (redPRNGAuthDFPaperBucketSplitProg_size_le _ q qep tL par gMain t0 rfl ht0 htL hqep)
    (by rw [CryptoGames.SM.Construction.redPRNGAuthDFPaperBucketSplitProg,
            CryptoGames.SM.Construction.redPRNGAuthDFPaperBucketSplitProgGen_totalQueries]; omega)

theorem redPRNGAuthDFPaperBucketPackedAtomicProg_gRedBounded (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt)
    (qep q : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (ht : t < qep + 2 := by omega) (htL : tL.getD 0 ≤ qep + 2 := by omega)
    (hqep : qep ≤ 4096 * q + 100000000 := by omega) :
    GRedBounded (redPRNGAuthDFPaperBucketPackedAtomicProg Dh encPt C ℓ encT idOf lam qep q tL par t)
      (fun _ => 1) (fun _ => 0) q (2 + 2 * q) (ratchetCostBudget q qep) := by
  dsimp only [redPRNGAuthDFPaperBucketPackedAtomicProg]
  exact DFProgBoundsBase.compilePrngDFAtomic_gRedBounded ℓ Pt C Dh encPt encT idOf lam _ _ q qep (2 + 2 * q)
    (redPRNGAuthDFPaperBucketPackedProg_parts_le _ q qep tL par t rfl ht htL)
    (redPRNGAuthDFPaperBucketPackedProg_size_le _ q qep tL par t rfl ht htL hqep)
    (by rw [CryptoGames.SM.Construction.redPRNGAuthDFPaperBucketPackedProg_totalQueries]; omega)

theorem redPRNGAuthDFPaperBucketHybridAtomicProg_gRedBounded (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : CryptoGames.LibsignalSession.Crypto) (ℓ : ℕ)
    (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
    (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt)
    (qep q : ℕ) (tL : Option ℕ) (par : Bool) (t : ℕ)
    (ht : t < qep + 2 := by omega) (htL : tL.getD 0 ≤ qep + 2 := by omega)
    (hqep : qep ≤ 4096 * q + 100000000 := by omega) :
    GRedBounded (redPRNGAuthDFPaperBucketHybridAtomicProg Dh encPt C ℓ encT idOf lam qep q tL par t)
      (fun _ => 1) (fun _ => 0) q (2 + 2 * q) (ratchetCostBudget q qep) := by
  unfold redPRNGAuthDFPaperBucketHybridAtomicProg
  dsimp only
  split_ifs
  · exact redPRNGAuthDFPaperBucketSplitAtomicProg_gRedBounded Dh encPt C ℓ encT idOf lam qep q tL par false t ht htL hqep
  · exact redPRNGAuthDFPaperBucketSplitAtomicProg_gRedBounded Dh encPt C ℓ encT idOf lam qep q tL par true (t - 1) (by omega) htL hqep
  · exact dummyPrngStage2AtomicProg_gRedBounded Dh encPt C ℓ encT idOf lam qep q (2 + 2 * q)

end BucketConcreteAtomicProgs

end -- public section

end Computational.Proofs.SessionCostedFig8.DFProgBucketBounds
