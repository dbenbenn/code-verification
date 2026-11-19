/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.LibsignalCli.StatementPqElf
public import Computational.Specifications.Game.ModelIface
public import Computational.Proofs.LibsignalCli.MainHaltedPrefixCore -- proof-setup: allow-public-import
import Computational.Proofs.E2E.BinaryHarnessCostedRedsV1
public import Computational.Proofs.E2E.Dsl.CompositionHaltedWitness -- proof-setup: allow-public-import
import Computational.Proofs.E2E.Dsl.CompositionHaltedWitnessInst
public import Computational.Proofs.E2E.Dsl.CompositionHaltedSimSpecInst -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.CompositionHaltedPrefixInv -- proof-setup: allow-public-import
import Computational.Proofs.E2E.Dsl.PrefixRedHalted
import Computational.Proofs.E2E.Dsl.PrefixRedHaltedEval
public import Computational.Proofs.E2E.Dsl.PrefixRedHaltedInst -- proof-setup: allow-public-import
import Computational.Proofs.E2E.Dsl.M3Interfaces
import Computational.Proofs.E2E.Dsl.KindRedHaltedEval
import Computational.Proofs.ReductionDsl.Soundness
import Computational.Proofs.E2E.ComposedKeyIndHop
import Computational.Proofs.E2E.ComposedPrefixHelpers
import Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping
import Computational.Proofs.E2E.Dsl.E2EStateRepr
import Computational.Proofs.E2E.Dsl.FreshnessSim
import Computational.Proofs.E2E.Dsl.HaltedStartSessionSim
import Computational.Proofs.E2E.Dsl.LocalSessionStep
import Computational.Proofs.E2E.Dsl.LocalSessionStepAux
import Computational.Proofs.E2E.Dsl.M3Subprograms
import Computational.Proofs.E2E.Dsl.PqxdhSim
import Computational.Proofs.E2E.Dsl.PqxdhSimBranches
import Computational.Proofs.E2E.Dsl.SpqrSimChain
import Computational.Proofs.E2E.Dsl.SpqrSimHist
import Computational.Proofs.E2E.Dsl.StartAndExtSm
import Computational.Proofs.E2E.Dsl.StartAndExtSmAux
import Computational.Proofs.E2E.TagSync1KeyReal
import Computational.Proofs.Game.PromotedCostedReds.AtomicOpsHonest
import Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge
import Computational.Proofs.GameHop.Advantage
import Computational.Proofs.GameHop.GlobalHybrid
import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds
import Computational.Proofs.ReductionDsl.MacroLift
import Computational.Proofs.ReductionDsl.SM.GameCosted
import Computational.Proofs.SignalPqxdh.Security.CollisionsA
import Computational.Proofs.SignalPqxdh.Security.CollisionsB
import Computational.Proofs.SignalPqxdh.Security.FgGapDhA
import Computational.Proofs.SignalPqxdh.Security.FgGapDhB
import Computational.Proofs.SignalPqxdh.Security.FgGapDhC
import Computational.Proofs.SignalPqxdh.Security.FgGapDhCouplingA
import Computational.Proofs.SignalPqxdh.Security.FgGapDhCouplingB
import Computational.Proofs.SignalPqxdh.Security.FgGapDhCouplingC
import Computational.Proofs.SignalPqxdh.Security.FgGapDhCouplingD
import Computational.Proofs.SignalPqxdh.Security.FgGapDhD
import Computational.Proofs.SignalPqxdh.Security.FgGapDhE
import Computational.Proofs.SignalPqxdh.Security.FgGapDhIk
import Computational.Proofs.SignalPqxdh.Security.FgGapDhIkInv
import Computational.Proofs.SignalPqxdh.Security.FgGapDhOpk
import Computational.Proofs.SignalPqxdh.Security.FgGapDhOpkInv
import Computational.Proofs.SignalPqxdh.Security.RoKemHop
import Computational.Proofs.SignalPqxdh.Security.RoKemHopA
import Computational.Proofs.SignalPqxdh.Security.RoKemHopB
import Computational.Proofs.SignalPqxdh.Security.SigHop
import Computational.Proofs.SignalPqxdh.Security.SigHopA
import Computational.Proofs.SignalPqxdh.Security.SigHopB
import Computational.Proofs.SignalPqxdh.Security.SigHopC
import Mathlib.Data.List.Dedup
import VCVio.EvalDist.EvalDistEq
import VCVio.EvalDist.MeasureTVDist.Event
import VCVio.EvalDist.Monad.Bool
import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.OracleComp.SimSemantics.StateT.StateProjection
import VCVio.ProgramLogic.Unary.HoareTriple

/-!
# Clamped Two-Stage Prefix Reduction Equivalence

Establishes two-stage `ProbComp` equivalence between `prefixRedHalted` (including clamped slot
`min k (min qStart (min b.q_total S.N_send_tot))`) and
`MainHaltedPrefixCore.bhPrefixRedWithSessionTracked` for all `k : ℕ`.
-/

public section

set_option autoImplicit false

open scoped BigOperators

namespace Computational.Proofs.E2E.Dsl.CompositionHaltedPrefixEval

open OracleComp OracleSpec
open _root_.ReductionDsl (Env Expr Comp Ty atomicSig atomicE2EOps
  e2eSessionTargetIface keyIndQT keyIndQenc sidT sidV smQT smQenc)
open CryptoGames.CBC (Plain)
open CryptoGames.LibsignalSession (Crypto GhostState IdentityKey PublicKey)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.E2E (BHE2EDrvState BHE2ESmResp BHModelInst BHTargetResp Bytes
  ModelDriverInstanceMeta SampledSessionKey bhBaseMirror bhClassifyTarget bhClassifyTargetOnly
  bhE2EDrvInstClean bhE2EFinishStartSpk bhE2EGuard bhE2EInstIkACorr bhE2EMirror
  bhIsBobRecvSMQuery bhLiftP bhPackSmResp bhShallowCheckExtSm bhShallowCommitExtSm
  bhShallowStepPostLocal bhShallowStepPreNonCtl bhTargetGameSpec bhTargetQenc
  e2eTargetGameCodec stageOneAsProbComp)
open Computational.Proofs.LibsignalCli.MainHaltedPrefixCore (SessionHaltTracker
  bhE2ELocalStartSessionTracked bhE2EStepLocalSmSessionTracked
  bhE2EStepLocalSmSessionTracked_eq_filter bhPrefixHandlePreWithSessionTracked
  bhPrefixRedWithSessionTracked bhShallowStepPreCtlSessionTracked
  bhShallowStepPreNonCtlSessionTracked)
open Computational.Proofs.E2E.Dsl.M3Interfaces (DrvMetaAligned DrvQueryBounded
  bhExtSmStep bhFilterSmQuery bhPromoteSlotK)
open Computational.Proofs.E2E.Dsl.PrefixRedHalted (HaltedPrefixSubprograms bhPrefixHandlePostWithHalted
  bhPrefixHandlePreWithHalted bhPrefixRedWithHalted bhShallowStepPostLocalHalted
  bhShallowStepPreCtlHalted bhShallowStepPreNonCtlHalted drvHaltedEnc drvHaltedTy
  prefixHandlePostHalted_eval_ctl prefixHandlePostHalted_eval_ki prefixHandlePostHalted_eval_sm
  prefixHandlePreHalted_eval_ctl prefixHandlePreHalted_eval_ki prefixHandlePreHalted_eval_sm
  prefixKiStepHaltedC prefixRedHalted prefixRedHalted_stage1Queries)
open Computational.Proofs.E2E.Dsl.PrefixRedHaltedEval (atomicGameRespEnc atomicPrefixCtxEnc
  mapPreEnc packAtomicSmRespEnc)
open Computational.Proofs.E2E.Dsl.PrefixRedHaltedInst (ValidHaltedPrefixSubprogramsInst)
open Computational.Proofs.E2E.Dsl.CompositionHaltedWitness (HaltedPausedInv
  HaltedTargetAdvPerInstanceBounded bhPrefixRedWithHalted_eq_bhPrefixRedWithSessionTracked)
open Computational.Proofs.E2E.Dsl.CompositionHaltedWitnessInst (isQueryBoundP_min nextSendDone)
open Computational.Proofs.E2E.Dsl.CompositionHaltedSimSpecInst (TwoStageAtomicSimSpecInst
  twoStage_stage12_comp_eq_inst)
open Computational.Proofs.E2E.Dsl.CompositionHaltedPrefixInv (HaltedPrefixSimInvInst)

private theorem atomicLiftP_map {ℓ : ℕ} {Pt α β : Type} (f : α → β) (p : ProbComp α) :
    (e2eSessionTargetIface ℓ Pt).liftP (f <$> p) =
      f <$> (e2eSessionTargetIface ℓ Pt).liftP p := by
  simp [PrefixRedHaltedEval.atomicSessionTargetIface_liftP_eq_bhLiftP, bhLiftP]

private theorem drvQueryBounded_of_prefixInv
    {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {TrackInv : ℕ → τ → Prop} {C : Crypto} {K : MlKem}
    {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ}
    {σH : BHE2EDrvState S ℓ × List τ}
    (h : HaltedPrefixSimInvInst TrackInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone σH) :
    DrvQueryBounded b.q_total (min qStart (min b.q_total S.N_send_tot)) σH.1 :=
  let hm := h.drvMirrorBounded_clamped
  ⟨hm.prins_le, le_trans hm.bundles_le (Nat.min_le_left _ _), hm.opks_le, hm.sends_le,
    hm.corrPrins_le, hm.insts_le, hm.instMeta_le, hm.revSpks_le⟩

private theorem prefixKiStepHaltedC_eval_eq_inst
    {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {SessH : Type}
    {subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH}
    {T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey SessH}
    {TrackInv : ℕ → SessH → Prop}
    {b : SignalPqxdh.QueryBudget} {qStart qInst qep : ℕ} {qs : ℕ → ℕ}
    (hValid : ValidHaltedPrefixSubprogramsInst subs T TrackInv b qStart qInst qep)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ}
    {σH : BHE2EDrvState S ℓ × List SessH}
    (hInv : HaltedPrefixSimInvInst TrackInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone σH)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvHaltedTy subs))
    (kqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S))
    (ρ : Env Γ) (kq : SignalPqxdh.KeyIndQuery S)
    (hσH : σHE.eval ρ = drvHaltedEnc subs σH)
    (hkq : kqE.eval ρ = keyIndQenc kq) :
    (prefixKiStepHaltedC subs b σHE kqE).eval ρ =
      (e2eSessionTargetIface ℓ Pt).liftP
        ((fun out => (atomicGameRespEnc out.1, drvHaltedEnc subs (out.2, σH.2))) <$>
          bhShallowStepPreNonCtl P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P)
            C K qep decT encT σH.1 (.inl (.inl kq))) := by
  dsimp only [prefixKiStepHaltedC, Comp.eval]
  rw [pure_bind]
  let ρ1 : Env (Ty.prod (drvHaltedTy subs) (keyIndQT (ℓ := ℓ) (Pt := Pt) S) :: Γ) :=
    .cons ((Expr.pair σHE kqE).eval ρ) ρ
  have h1 : (subs.kiStepC b (.fst (.fst .v0)) (.snd .v0)).eval ρ1 = _ :=
    hValid.kiStepC_eval hP hInv.drvMirrorBounded_clamped.prins_le
      hInv.base.instMeta_length_le hInv.stListBounded_qTotal
      (.fst (.fst .v0)) (.snd .v0) ρ1 kq
      (by simp [ρ1, Expr.eval, Expr.v0, hσH, drvHaltedEnc])
      (by simp [ρ1, Expr.eval, Expr.v0, hkq])
  change ((subs.kiStepC b (.fst (.fst .v0)) (.snd .v0)).eval ρ1 >>= _) = _
  rw [h1, atomicLiftP_map, bind_map_left, atomicLiftP_map]
  simp only [map_eq_bind_pure_comp, Function.comp_def]
  exact bind_congr fun ⟨_, _⟩ => by simp [Expr.eval, Expr.v0, Expr.v1, hσH, drvHaltedEnc]

private theorem bhFilterSmQuery_isBobRecv {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {d : BHModelInst S ℓ} {im : ModelDriverInstanceMeta S}
    {sq sq' : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain}
    (hf : bhFilterSmQuery d im sq = some sq') :
    bhIsBobRecvSMQuery sq' = bhIsBobRecvSMQuery sq := by
  unfold bhFilterSmQuery at hf
  rcases sq with (((qTr | qCh) | ⟨pDl, cDl⟩) | ⟨pIj, cIj⟩) | qCr
  · simp only [Option.some.injEq] at hf; subst hf; rfl
  · simp only [Option.some.injEq] at hf; subst hf; rfl
  · cases pDl
    · dsimp only at hf; split_ifs at hf; simp only [Option.some.injEq] at hf; subst hf; rfl
    · dsimp only at hf; split_ifs at hf
      · cases hdec : CryptoVerification.E2E.bhDecodePreKeyMsgE cDl <;> rw [hdec] at hf
        · cases hf
        · dsimp only at hf; split_ifs at hf; simp only [Option.some.injEq] at hf; subst hf; rfl
      · cases hdec : CryptoVerification.E2E.bhDecodePreKeyMsgE cDl <;> rw [hdec] at hf
        · simp only [Option.some.injEq] at hf; subst hf; rfl
        · dsimp only at hf; split_ifs at hf; simp only [Option.some.injEq] at hf; subst hf; rfl
  · cases pIj
    · dsimp only at hf; split_ifs at hf; simp only [Option.some.injEq] at hf; subst hf; rfl
    · dsimp only at hf; split_ifs at hf
      · cases hdec : CryptoVerification.E2E.bhDecodePreKeyMsgE cIj <;> rw [hdec] at hf
        · simp only [Option.some.injEq] at hf; subst hf; rfl
        · dsimp only at hf; split_ifs at hf; simp only [Option.some.injEq] at hf; subst hf; rfl
  · simp only [Option.some.injEq] at hf; subst hf; rfl

private theorem checkExtSm_eq_of_filter {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {k : ℕ} {σ : BHE2EDrvState S ℓ}
    {d : BHModelInst S ℓ} {im : ModelDriverInstanceMeta S}
    (hcl : (!bhE2EDrvInstClean σ k) = false)
    (hd : σ.insts[k]? = some d)
    (him : σ.instMeta[k]? = some im)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (hcorr : (!im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σ d) = false) :
    bhShallowCheckExtSm k σ k sq =
      match bhFilterSmQuery d im sq with
      | none => .inl (.inr (none, none, none))
      | some sq' => .inr sq' := by
  dsimp only [bhShallowCheckExtSm]
  have hneq : (k != k) = false := by simp
  rw [hneq, Bool.false_or, hcl]
  simp only [Bool.false_eq_true, ↓reduceIte, hd, him, hcorr]
  unfold bhFilterSmQuery
  rcases sq with (((qTr | qCh) | ⟨pDl, cDl⟩) | ⟨pIj, cIj⟩) | qCr
  · rfl
  · rfl
  · cases pDl
    · dsimp only; split_ifs <;> rfl
    · cases im.bobAccepted
      · dsimp only [Bool.not_false, ↓reduceIte]
        rcases CryptoVerification.E2E.bhDecodePreKeyMsgE cDl with _ | _
        · rfl
        · dsimp only; split_ifs <;> rfl
      · dsimp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        rcases CryptoVerification.E2E.bhDecodePreKeyMsgE cDl with _ | _
        · rfl
        · dsimp only; split_ifs <;> rfl
  · cases pIj
    · dsimp only; split_ifs <;> rfl
    · cases im.bobAccepted
      · rfl
      · dsimp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        rcases CryptoVerification.E2E.bhDecodePreKeyMsgE cIj with _ | _
        · rfl
        · dsimp only; split_ifs <;> rfl
  · rfl

/-! ## Two-stage simulation equivalence -/

@[expose] def prefixRedHalted_twoStageSimSpecInst
    {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {SessH : Type}
    {subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH}
    {T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey SessH}
    {TrackInv : ℕ → SessH → Prop}
    {b : SignalPqxdh.QueryBudget} {qStart qInst qep k : ℕ} {qs : ℕ → ℕ}
    (hValid : ValidHaltedPrefixSubprogramsInst subs T TrackInv b qStart qInst qep)
    (hqInst : Finset.sup (Finset.range qStart) qs ≤ qInst)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    (hPromoteK : ∀ {σH : BHE2EDrvState S ℓ × List SessH},
      σH.1.insts.length ≤ min qStart (min b.q_total S.N_send_tot) →
      ∀ {Γ} (kE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat)
        (idxOptE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.opt .nat))
        (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ subs.drvTy) (ρ : Env Γ) (idx? : Option ℕ),
        kE.eval ρ = k → idxOptE.eval ρ = idx? → σE.eval ρ = subs.drvEnc σH.1 →
        (subs.promoteSlotKC qStart kE idxOptE σE).eval ρ =
          match bhPromoteSlotK k idx? σH.1 with
          | .inl ans => pure (.inl (ans.1, subs.drvEnc ans.2))
          | .inr (ctx, p, σ_p) => pure (.inr (atomicPrefixCtxEnc ctx, (p, subs.drvEnc σ_p)))) :
    TwoStageAtomicSimSpecInst S Pt ℓ (atomicE2EOps ℓ P C K decT encT) b qStart qs
      (BHE2EDrvState S ℓ × List SessH) (Option ℕ) where
  R := prefixRedHalted subs b qStart qInst qep k
  R_ref := bhPrefixRedWithHalted S ℓ P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P)
    C K qep decT encT
    (fun bm σH sid =>
      bhE2ELocalStartSessionTracked T.init (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P)
        C K (some bm) σH sid)
    (bhE2EStepLocalSmSessionTracked T C K qep decT encT) k
  drvEnc := drvHaltedEnc subs
  πEnc := id
  σ0 := ({}, [])
  Inv := HaltedPrefixSimInvInst TrackInv C K b qStart qs
  PausedInv := HaltedPausedInv k
  qenc_eq _ := rfl
  rdec_eq _ _ := rfl
  stage1_queries_zero := prefixRedHalted_stage1Queries subs b qStart qInst qep k
  init_inv := HaltedPrefixSimInvInst.empty TrackInv C K b qStart qs false
  init_costed := by
    dsimp only [prefixRedHalted, Comp.eval, Expr.eval, drvHaltedEnc]
    rw [subs.emptyDrvStateE_eval]
    rfl
  init_ref := rfl
  chDone_eq _ _ := by
    dsimp only [prefixRedHalted, bhPrefixRedWithHalted, Comp.eval]
    rw [subs.defaultPrefixCtxE_eval]
    rfl
  resume_eq {_ _ _ _ σ_p} _ _ p flip := by
    dsimp only [prefixRedHalted, bhPrefixRedWithHalted, Comp.eval, Expr.eval]
    rw [subs.drvSetBitE_eval (.fst .v0) .v2 _ σ_p.1 (by simp [Expr.eval, Expr.v0, drvHaltedEnc])]
    rfl
  resume_inv {_ _ _ _ σ_p} hInv hPaused p flip rs hrs := by
    dsimp only [bhPrefixRedWithHalted] at hrs
    simp only [support_pure, Set.mem_singleton_iff] at hrs
    subst hrs
    exact ⟨hInv.setBit flip, hPaused⟩
  stepPre_eq {qKiDone qSendDone qStartDone qSessDone σH} hInv t hBud := by
    rcases t with (kq | cq) | ⟨i, sq⟩
    · dsimp only [prefixRedHalted, bhPrefixRedWithHalted, e2eTargetGameCodec]
      rw [prefixHandlePreHalted_eval_ki]
      dsimp only [bhPrefixHandlePreWithHalted, bhShallowStepPreNonCtlHalted, bhTargetQenc]
      let ρ_ki : Env [keyIndQT (ℓ := ℓ) (Pt := Pt) S,
          Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
          drvHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q] :=
        .cons (keyIndQenc kq) (.cons (.inl (keyIndQenc kq))
          (.cons (drvHaltedEnc subs σH) (.cons (.inl (.inl (keyIndQenc kq))) .nil)))
      rw [prefixKiStepHaltedC_eval_eq_inst hValid hP hInv .v2 .v0 ρ_ki kq rfl rfl]
      rw [atomicLiftP_map, bind_map_left]
      simp only [PrefixRedHaltedEval.atomicSessionTargetIface_liftP_eq_bhLiftP,
        bhLiftP, simulateQ_bind, simulateQ_pure, map_bind, map_pure, bind_assoc, pure_bind,
        mapPreEnc]
    · rcases cq with ⟨sid⟩
      dsimp only [prefixRedHalted, bhPrefixRedWithHalted, e2eTargetGameCodec]
      rw [prefixHandlePreHalted_eval_ctl]
      dsimp only [bhPrefixHandlePreWithHalted, bhShallowStepPreCtlHalted, bhTargetQenc]
      let ρ_ctl : Env [sidT (ℓ := ℓ) (Pt := Pt) S,
          Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
          drvHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q] :=
        .cons (sidV sid) (.cons (.inr (sidV sid))
          (.cons (drvHaltedEnc subs σH) (.cons (.inl (.inr (sidV sid))) .nil)))
      rw [hValid.localStartHaltedC_eval true hInv.drvMirrorBounded_clamped
        hInv.stListBounded_qTotal hInv.base.tracks_length_le .v2 .v0 ρ_ctl sid rfl rfl]
      rw [atomicLiftP_map, bind_map_left]
      simp only [PrefixRedHaltedEval.atomicSessionTargetIface_liftP_eq_bhLiftP,
        bhLiftP, simulateQ_bind, map_bind, bind_assoc]
      refine bind_congr_of_forall_mem_support _ fun ⟨idx?, σH'⟩ hmem => ?_
      have hOut := PrefixRedHaltedEval.mem_support_of_atomicSessionLiftP (Pt := Pt) _ hmem
      obtain ⟨hInv', -⟩ :=
        hInv.localStartSessionTracked_preserves hValid.track_valid P C K (some true) hBud sid hOut
      let ρ_pr : Env [Ty.prod (.opt .nat) (drvHaltedTy subs),
          sidT (ℓ := ℓ) (Pt := Pt) S,
          Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
          drvHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q] :=
        .cons (idx?, drvHaltedEnc subs σH') ρ_ctl
      rw [hPromoteK hInv'.base.insts_length_le (.nat k) (.fst .v0) (.fst (.snd .v0))
        ρ_pr idx? rfl rfl (by simp [ρ_pr, Expr.eval, Expr.v0, drvHaltedEnc])]
      rcases σH' with ⟨σ', logs'⟩
      dsimp only [bhPromoteSlotK]
      split_ifs with hlt
      · simp [mapPreEnc, drvHaltedEnc, simulateQ_pure]
        cases σ'.insts[k]? <;> rfl
      · simp [mapPreEnc, atomicGameRespEnc, drvHaltedEnc, simulateQ_pure]
    · dsimp only [prefixRedHalted, bhPrefixRedWithHalted, e2eTargetGameCodec]
      rw [prefixHandlePreHalted_eval_sm]
      dsimp only [bhPrefixHandlePreWithHalted, bhShallowStepPreNonCtlHalted, bhTargetQenc]
      let ρ_sm : Env [Ty.prod .nat (smQT (ℓ := ℓ) (Pt := Pt)),
          drvHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q] :=
        .cons (i, smQenc sq) (.cons (drvHaltedEnc subs σH) (.cons (.inr (i, smQenc sq)) .nil))
      have hSim0 := hInv.base.toHaltedSimInv hValid.track_valid
      rw [hValid.haltedStepLocalSmC_eval
        hInv.base.insts_length_le hInv.base.metaAligned
        hInv.drvMirrorBounded_clamped.corrPrins_le hInv.drvMirrorBounded_clamped.revSpks_le
        hInv.drvMirrorBounded_clamped.prins_le
        (fun d hd gs hgs => (hSim0.sessions d hd gs hgs).mono hqInst)
        (fun d hd gs hgs => (hInv.base.epoch_bounded d hd gs hgs).mono hqInst)
        hInv.base.tracks_length_le
        (fun st hst => hValid.track_valid.mono hqInst (hSim0.tracks_inv st hst))
        .v1 (.fst .v0) (.snd .v0) ρ_sm i sq rfl rfl rfl]
      rw [atomicLiftP_map, bind_map_left]
      simp only [PrefixRedHaltedEval.atomicSessionTargetIface_liftP_eq_bhLiftP,
        bhLiftP, simulateQ_bind, simulateQ_pure, map_bind, map_pure, bind_assoc, pure_bind,
        mapPreEnc, atomicGameRespEnc]
  stepPre_inv {qKiDone qSendDone qStartDone qSessDone σH} hInv t hBud res hres := by
    dsimp only [bhPrefixRedWithHalted] at hres
    rcases t with (kq | cq) | ⟨i, sq⟩
    · dsimp only [bhPrefixHandlePreWithHalted, bhShallowStepPreNonCtlHalted, bhTargetQenc] at hres
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hres
      rcases hres with ⟨⟨r, σH1⟩, h1, rfl⟩
      have h1p := KindRedHaltedEval.mem_support_of_bhLiftP _ h1
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h1p
      rcases h1p with ⟨⟨r', σ'⟩, hki, hpair⟩
      cases hpair
      have hSendNext : nextSendDone qSendDone kq ≤ S.N_send_tot := by
        dsimp only [nextSendDone]
        split_ifs with hs
        · exact hBud.2 hs
        · exact hInv.base.send_le
      exact (hInv.kiStep_preserves P C K qep decT encT kq hBud.1 hSendNext hki).1
    · rcases cq with ⟨sid⟩
      dsimp only [bhPrefixHandlePreWithHalted, bhShallowStepPreCtlHalted, bhTargetQenc] at hres
      simp only [mem_support_bind_iff] at hres
      rcases hres with ⟨ctlOut, hctl, hres⟩
      have hctlP := KindRedHaltedEval.mem_support_of_bhLiftP _ hctl
      simp only [mem_support_bind_iff] at hctlP
      rcases hctlP with ⟨⟨idx?, ⟨σ', logs'⟩⟩, hst, hif⟩
      obtain ⟨hInv', -⟩ :=
        hInv.localStartSessionTracked_preserves hValid.track_valid P C K (some true) hBud sid hst
      split_ifs at hif with hlt
      · simp only [support_pure, Set.mem_singleton_iff] at hif
        subst hif
        simp only [support_pure, Set.mem_singleton_iff] at hres
        subst hres
        obtain ⟨hInvP, hPausedP⟩ := hInv'.promoteSlotK_paused_preserves hlt
        exact ⟨⟨.startDR sid, rfl⟩, hInvP, hPausedP⟩
      · simp only [support_pure, Set.mem_singleton_iff] at hif
        subst hif
        simp only [support_pure, Set.mem_singleton_iff] at hres
        subst hres
        exact hInv'
    · dsimp only [bhPrefixHandlePreWithHalted, bhShallowStepPreNonCtlHalted, bhTargetQenc] at hres
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hres
      rcases hres with ⟨⟨r, σH1⟩, h1, rfl⟩
      have h1p := KindRedHaltedEval.mem_support_of_bhLiftP _ h1
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h1p
      rcases h1p with ⟨⟨sr, σH'⟩, hsm, hpair⟩
      cases hpair
      exact (hInv.stepLocalSmSessionTracked_preserves hValid.track_valid C K qep decT encT
        i hBud sq hsm).1
  stepPost_eq {qKiDone qSendDone qStartDone qSessDone σH} hInv hPaused t _hBud := by
    rcases t with (kq | cq) | ⟨i, sq⟩
    · dsimp only [prefixRedHalted, bhPrefixRedWithHalted, e2eTargetGameCodec]
      rw [prefixHandlePostHalted_eval_ki]
      dsimp only [bhPrefixHandlePostWithHalted, bhShallowStepPostLocalHalted, bhTargetQenc]
      let ρ_ki : Env [keyIndQT (ℓ := ℓ) (Pt := Pt) S,
          Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
          drvHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q] :=
        .cons (keyIndQenc kq) (.cons (.inl (keyIndQenc kq))
          (.cons (drvHaltedEnc subs σH) (.cons (.inl (.inl (keyIndQenc kq))) .nil)))
      rw [prefixKiStepHaltedC_eval_eq_inst hValid hP hInv .v2 .v0 ρ_ki kq rfl rfl]
      rw [atomicLiftP_map]
      simp only [PrefixRedHaltedEval.atomicSessionTargetIface_liftP_eq_bhLiftP,
        bhLiftP, simulateQ_bind, simulateQ_pure, map_eq_bind_pure_comp, Function.comp_def,
        bind_assoc, pure_bind, bhShallowStepPostLocal, bhShallowStepPreNonCtl, Prod.map]
    · rcases cq with ⟨sid⟩
      dsimp only [prefixRedHalted, bhPrefixRedWithHalted, e2eTargetGameCodec]
      rw [prefixHandlePostHalted_eval_ctl]
      dsimp only [bhPrefixHandlePostWithHalted, bhShallowStepPostLocalHalted, bhTargetQenc]
      let ρ_ctl : Env [sidT (ℓ := ℓ) (Pt := Pt) S,
          Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
          drvHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q] :=
        .cons (sidV sid) (.cons (.inr (sidV sid))
          (.cons (drvHaltedEnc subs σH) (.cons (.inl (.inr (sidV sid))) .nil)))
      rw [hValid.localStartHaltedC_eval false hInv.drvMirrorBounded_clamped
        hInv.stListBounded_qTotal hInv.base.tracks_length_le .v2 .v0 ρ_ctl sid rfl rfl]
      rw [atomicLiftP_map, bind_map_left]
      simp only [PrefixRedHaltedEval.atomicSessionTargetIface_liftP_eq_bhLiftP,
        bhLiftP, simulateQ_bind, simulateQ_pure, map_bind, map_pure,
        Prod.map, atomicGameRespEnc]
    · dsimp only [prefixRedHalted, bhPrefixRedWithHalted, e2eTargetGameCodec]
      rw [prefixHandlePostHalted_eval_sm]
      dsimp only [bhPrefixHandlePostWithHalted, bhTargetQenc]
      let ρ_sm : Env [Ty.prod .nat (smQT (ℓ := ℓ) (Pt := Pt)),
          drvHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q] :=
        .cons (i, smQenc sq) (.cons (drvHaltedEnc subs σH) (.cons (.inr (i, smQenc sq)) .nil))
      rcases σH with ⟨σ, tracks⟩
      by_cases hik : i = k
      · subst hik
        rw [decide_eq_true rfl]; simp only [↓reduceIte]
        have hi_nInst : i < min qStart (min b.q_total S.N_send_tot) :=
          lt_of_lt_of_le hPaused.1 hInv.base.insts_length_le
        rw [hValid.extSmStepC_eval (drvQueryBounded_of_prefixInv hInv) hInv.base.metaAligned
          hPaused (.nat i) (.fst .v1) (.snd .v0) ρ_sm sq hi_nInst rfl
          (by simp [ρ_sm, Expr.eval, Expr.v1, drvHaltedEnc]) rfl]
        simp only [bind_map_left]
        set d := σ.insts[i]'hPaused.1
        have hd : σ.insts[i]? = some d := List.getElem?_eq_getElem hPaused.1
        have hmeta_lt : i < σ.instMeta.length := by
          have hlen : σ.instMeta.length = σ.insts.length := hInv.base.metaAligned
          have hi_lt : i < σ.insts.length := hPaused.1
          omega
        set im := σ.instMeta[i]'hmeta_lt
        have him : σ.instMeta[i]? = some im := List.getElem?_eq_getElem hmeta_lt
        have hd_gs : d.gs = none := hPaused.2 d hd
        by_cases hcl : (!bhE2EDrvInstClean σ i) = true
        · have hchk : bhShallowCheckExtSm i σ i sq = .inl (.inr (none, none, none)) := by
            dsimp only [bhShallowCheckExtSm]; rw [hcl]; simp
          rw [hchk]
          dsimp only [bhShallowStepPostLocalHalted, bhE2EStepLocalSmSessionTracked, bhExtSmStep]
          rw [hcl]
          simp [bhLiftP, simulateQ_pure, Prod.map, atomicGameRespEnc, drvHaltedEnc]
        · have hclF : (!bhE2EDrvInstClean σ i) = false := Bool.eq_false_iff.mpr hcl
          by_cases hcorr : (!im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σ d) = true
          · have hchk : bhShallowCheckExtSm i σ i sq = .inl (.inr (none, none, none)) := by
              dsimp only [bhShallowCheckExtSm]
              have hneq : (i != i) = false := by simp
              rw [hneq, Bool.false_or, hclF]; simp [hd, him, hcorr]
            rw [hchk]
            dsimp only [bhShallowStepPostLocalHalted, bhE2EStepLocalSmSessionTracked, bhExtSmStep]
            rw [hclF]
            simp [hd, him, hcorr, bhLiftP, simulateQ_pure, Prod.map, atomicGameRespEnc, drvHaltedEnc]
          · have hcorrF : (!im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σ d) = false :=
              Bool.eq_false_iff.mpr hcorr
            cases hf : bhFilterSmQuery d im sq with
            | none =>
              have hchk : bhShallowCheckExtSm i σ i sq = .inl (.inr (none, none, none)) := by
                rw [checkExtSm_eq_of_filter hclF hd him sq hcorrF, hf]
              rw [hchk]
              dsimp only [bhShallowStepPostLocalHalted, bhE2EStepLocalSmSessionTracked, bhExtSmStep]
              rw [hclF]
              simp [hd, him, hcorrF, hf, hd_gs, bhLiftP, simulateQ_pure, Prod.map,
                atomicGameRespEnc, drvHaltedEnc]
            | some sq' =>
              have hchk : bhShallowCheckExtSm i σ i sq = .inr sq' := by
                rw [checkExtSm_eq_of_filter hclF hd him sq hcorrF, hf]
              rw [hchk]
              have hcorrF' :
                  (!im.bobAccepted && bhIsBobRecvSMQuery sq' && bhE2EInstIkACorr σ d) = false := by
                rwa [bhFilterSmQuery_isBobRecv hf]
              dsimp only [bhExtSmStep, bhShallowCommitExtSm]
              rw [hclF]
              simp only [Bool.false_eq_true, ↓reduceIte, hd, him, hcorrF, hf,
                map_bind, map_pure, bind_assoc, pure_bind]
              refine bind_congr fun r => ?_
              have hunp : CryptoVerification.E2E.bhUnpackSmResp sq' (bhPackSmResp sq' r) = r := by
                rcases sq' with (((_ | _) | _) | _) | _ <;> rfl
              simp [hcorrF', hunp, Prod.map, atomicGameRespEnc, drvHaltedEnc]
      · rw [decide_eq_false hik]; simp only [Bool.false_eq_true, ↓reduceIte]
        have hchk : bhShallowCheckExtSm k σ i sq = .inl (.inr (none, none, none)) := by
          dsimp only [bhShallowCheckExtSm]
          have hneB : (i != k) = true := bne_iff_ne.mpr hik
          rw [hneB]; simp
        rw [hchk]
        have hSim0 := hInv.base.toHaltedSimInv hValid.track_valid
        rw [hValid.haltedStepLocalSmC_eval
          hInv.base.insts_length_le hInv.base.metaAligned
          hInv.drvMirrorBounded_clamped.corrPrins_le hInv.drvMirrorBounded_clamped.revSpks_le
          hInv.drvMirrorBounded_clamped.prins_le
          (fun d hd gs hgs => (hSim0.sessions d hd gs hgs).mono hqInst)
          (fun d hd gs hgs => (hInv.base.epoch_bounded d hd gs hgs).mono hqInst)
          hInv.base.tracks_length_le
          (fun st hst => hValid.track_valid.mono hqInst (hSim0.tracks_inv st hst))
          .v1 (.fst .v0) (.snd .v0) ρ_sm i sq rfl rfl rfl]
        rw [atomicLiftP_map, bind_map_left]
        dsimp only [bhShallowStepPostLocalHalted]
        simp only [PrefixRedHaltedEval.atomicSessionTargetIface_liftP_eq_bhLiftP,
          bhLiftP, simulateQ_bind, simulateQ_pure, map_bind, map_pure,
          Prod.map, atomicGameRespEnc]
  stepPost_inv {qKiDone qSendDone qStartDone qSessDone σH} hInv hPaused t hBud p hp := by
    dsimp only [bhPrefixRedWithHalted] at hp
    rcases t with (kq | cq) | ⟨i, sq⟩
    · dsimp only [bhPrefixHandlePostWithHalted, bhShallowStepPostLocalHalted, bhTargetQenc] at hp
      have hp' := KindRedHaltedEval.mem_support_of_bhLiftP _ hp
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hp'
      rcases hp' with ⟨⟨r', σ'⟩, hki, rfl⟩
      have hSendNext : nextSendDone qSendDone kq ≤ S.N_send_tot := by
        dsimp only [nextSendDone]
        split_ifs with hs
        · exact hBud.2 hs
        · exact hInv.base.send_le
      obtain ⟨hInv', hPau'⟩ :=
        hInv.kiStep_preserves P C K qep decT encT kq hBud.1 hSendNext hki
      exact ⟨hPau' k hPaused, hInv'⟩
    · rcases cq with ⟨sid⟩
      dsimp only [bhPrefixHandlePostWithHalted, bhShallowStepPostLocalHalted, bhTargetQenc] at hp
      have hp' := KindRedHaltedEval.mem_support_of_bhLiftP _ hp
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hp'
      rcases hp' with ⟨⟨idx?, σH1⟩, hst, rfl⟩
      obtain ⟨hInv', hPau'⟩ :=
        hInv.localStartSessionTracked_preserves hValid.track_valid P C K (some false) hBud sid hst
      exact ⟨hPau' k hPaused, hInv'⟩
    · dsimp only [bhPrefixHandlePostWithHalted, bhTargetQenc] at hp
      cases hchk : bhShallowCheckExtSm k σH.1 i sq with
      | inl _ =>
        rw [hchk] at hp
        have hp' := KindRedHaltedEval.mem_support_of_bhLiftP _ hp
        dsimp only [bhShallowStepPostLocalHalted] at hp'
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hp'
        rcases hp' with ⟨⟨sr, σH'⟩, hsm, rfl⟩
        obtain ⟨hInv', hPau'⟩ := hInv.stepLocalSmSessionTracked_preserves hValid.track_valid
          C K qep decT encT i hBud sq hsm
        exact ⟨hPau' k hPaused, hInv'⟩
      | inr sq' =>
        have hik : i = k := by
          dsimp only [bhShallowCheckExtSm] at hchk
          by_contra hne
          rw [bne_iff_ne.mpr hne, Bool.true_or] at hchk
          simp at hchk
        subst hik
        rw [hchk] at hp
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hp
        rcases hp with ⟨r, -, rfl⟩
        obtain ⟨hInv', hPau'⟩ := hInv.commitExtSm_preserves hValid.track_valid hPaused hBud
          sq' (bhPackSmResp sq' r)
        exact ⟨hPau', hInv'⟩
  finish_eq {_ _ _ _ σ_out} hInv b_out flip := by
    dsimp only [prefixRedHalted, bhPrefixRedWithHalted]
    let ρ_f : Env [drvHaltedTy subs, .bool, .bool] :=
      .cons (drvHaltedEnc subs σ_out) (.cons b_out (.cons flip .nil))
    rw [hValid.finishPrefixC_eval hP hInv.base.insts_length_le hInv.tested_length_le
      hInv.respSessions_untested hInv.stListBounded_qTotal (.fst .v0) .v1 .v2 ρ_f b_out flip
      (by simp [ρ_f, Expr.eval, Expr.v0, drvHaltedEnc]) rfl rfl]
    rfl

theorem prefixEval_eq_of_valid_inst_any_k
    {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {SessH : Type}
    {subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH}
    {T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey SessH}
    {TrackInv : ℕ → SessH → Prop}
    {b : SignalPqxdh.QueryBudget} {qStart qInst qep k : ℕ} {qs : ℕ → ℕ}
    (hValid : ValidHaltedPrefixSubprogramsInst subs T TrackInv b qStart qInst qep)
    (hqInst : Finset.sup (Finset.range qStart) qs ≤ qInst)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    (hPromoteK : ∀ {σH : BHE2EDrvState S ℓ × List SessH},
      σH.1.insts.length ≤ min qStart (min b.q_total S.N_send_tot) →
      ∀ {Γ} (kE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat)
        (idxOptE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.opt .nat))
        (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ subs.drvTy) (ρ : Env Γ) (idx? : Option ℕ),
        kE.eval ρ = k → idxOptE.eval ρ = idx? → σE.eval ρ = subs.drvEnc σH.1 →
        (subs.promoteSlotKC qStart kE idxOptE σE).eval ρ =
          match bhPromoteSlotK k idx? σH.1 with
          | .inl ans => pure (.inl (ans.1, subs.drvEnc ans.2))
          | .inr (ctx, p, σ_p) => pure (.inr (atomicPrefixCtxEnc ctx, (p, subs.drvEnc σ_p))))
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hB : HaltedTargetAdvPerInstanceBounded B_A b qStart qs)
    {β : Type}
    (game2 : IdentityKey → IdentityKey → BitVec 256 →
      OracleComp
        (unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) Bool →
      ProbComp β)
    (qTot : ℕ) (flip : Bool) :
    let R := prefixRedHalted subs b qStart qInst qep k
    let R_sh := bhPrefixRedWithSessionTracked T P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P)
      C K qep decT encT k
    (stageOneAsProbComp (R.eval1 (fun _ => B_A) () qTot false) >>= fun o =>
      game2 o.1.1 o.1.2.1 o.1.2.2 (R.eval2 o.2 flip qTot false)) =
    (stageOneAsProbComp (R_sh.eval1 (fun _ => B_A) () qTot false) >>= fun o =>
      game2 o.1.idA o.1.idB o.1.spkCoins (R_sh.eval2 o.2 flip qTot false)) := by
  dsimp only
  have hSim := twoStage_stage12_comp_eq_inst
    (prefixRedHalted_twoStageSimSpecInst hValid hqInst hP hPromoteK)
    B_A hB game2 qTot qTot false flip
  dsimp only [prefixRedHalted_twoStageSimSpecInst] at hSim
  rwa [bhPrefixRedWithHalted_eq_bhPrefixRedWithSessionTracked] at hSim

/-! ## Clamped-slot equivalence -/

private theorem map_set_eq_self_local {α β : Type} (f : α → β) :
    ∀ (l : List α) (i : ℕ) (x d : α), l[i]? = some d → f x = f d → (l.set i x).map f = l.map f
  | [], _, _, _, h, _ => nomatch h
  | _ :: _, 0, _, _, h, hf => by cases h; simp [hf]
  | a :: as, i + 1, x, d, h, hf => by
    simp only [List.getElem?_cons_succ, List.set_cons_succ, List.map_cons] at h ⊢
    exact congrArg (f a :: ·) (map_set_eq_self_local f as i x d h hf)

private theorem mem_support_of_stageOneAsProbComp_local {ℓ : ℕ} {α : Type}
    (oa : OracleComp
      (unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) α)
    {x : α} (hx : x ∈ support (stageOneAsProbComp oa)) : x ∈ support oa := by
  induction oa using OracleComp.inductionOn with
  | pure _ => simpa [stageOneAsProbComp] using hx
  | query_bind q mx ih =>
    unfold stageOneAsProbComp at hx
    rw [simulateQ_query_bind, mem_support_bind_iff] at hx
    rcases hx with ⟨u, -, hxu⟩
    rw [mem_support_bind_iff]
    exact ⟨u, mem_support_query q u, ih u hxu⟩

private def shallowInstsBoundInv {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (qKiDone qStartDone : ℕ) (σ : BHE2EDrvState S ℓ) : Prop :=
  σ.sends.length ≤ qKiDone ∧ σ.insts.length ≤ qStartDone ∧ (σ.insts.map (·.sid)).Nodup ∧
    (∀ s ∈ σ.insts.map (·.sid), s ∈ σ.sends.map Prod.fst)

private theorem shallowInstsBoundInv_insts_le {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {qKiDone qStartDone : ℕ} {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {σ : BHE2EDrvState S ℓ}
    (hInv : shallowInstsBoundInv qKiDone qStartDone σ)
    (hKi : qKiDone ≤ b.q_total) (hSt : qStartDone ≤ min qStart S.N_send_tot) :
    σ.insts.length ≤ min qStart (min b.q_total S.N_send_tot) := by
  have hSub : σ.insts.length ≤ σ.sends.length := by
    simpa only [List.length_map] using hInv.2.2.1.length_le_of_subset hInv.2.2.2
  have := le_trans hSub (le_trans hInv.1 hKi)
  have := le_trans hInv.2.1 hSt
  omega

private theorem shallowInstsBoundInv_mirror {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {qKiDone qStartDone : ℕ} {σ : BHE2EDrvState S ℓ}
    (hInv : shallowInstsBoundInv qKiDone qStartDone σ) (st' : SignalPqxdh.KeyIndState S)
    (kq : SignalPqxdh.KeyIndQuery S) (kr : SignalPqxdh.KeyIndResponse) :
    shallowInstsBoundInv (qKiDone + 1) qStartDone (bhE2EMirror { σ with st := st' } kq kr) := by
  rcases hInv with ⟨hsends, hinsts, hnodup, hsub⟩
  refine ⟨?_, hinsts, hnodup, fun s hs => ?_⟩
  · cases kq <;> cases kr <;> simp only [bhE2EMirror, bhBaseMirror, List.length_cons] <;> omega
  · cases kq <;> cases kr <;>
      simp only [bhE2EMirror, bhBaseMirror, List.map_cons, List.mem_cons] at hs ⊢
    all_goals first | exact hsub s hs | exact Or.inr (hsub s hs)

private theorem shallowInstsBoundInv_finishStartSpk {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (C : Crypto) (K : MlKem) (bm? : Option Bool) {qKiDone qStartDone : ℕ} {σ : BHE2EDrvState S ℓ}
    (hInv : shallowInstsBoundInv qKiDone qStartDone σ) (st2 : SignalPqxdh.KeyIndState S)
    (sid : SignalPqxdh.SessionId S) (rTest rSpk : SignalPqxdh.KeyIndResponse)
    (spkCoins : BitVec 256) :
    shallowInstsBoundInv qKiDone (qStartDone + 1)
      (bhE2EFinishStartSpk C K bm? { σ with st := st2 } sid rTest rSpk spkCoins).2 := by
  rcases hInv with ⟨hsends, hinsts, hnodup, hsub⟩
  have hmono : shallowInstsBoundInv qKiDone (qStartDone + 1) { σ with st := st2 } :=
    ⟨hsends, Nat.le_succ_of_le hinsts, hnodup, hsub⟩
  unfold bhE2EFinishStartSpk
  cases hg : bhE2EGuard { σ with st := st2 } sid with
  | none => exact hmono
  | some val =>
    rcases val with ⟨_, _, _⟩; dsimp only
    cases rTest <;> cases rSpk <;> dsimp only
    all_goals try exact hmono
    split_ifs with hmatch
    · dsimp only; unfold bhE2EGuard at hg
      by_cases hany : σ.insts.any (fun d => d.sid == sid) = true
      · simp [hany] at hg
      · simp only [hany, Bool.false_eq_true, ↓reduceIte] at hg
        cases hfind : σ.sends.find? (fun (s, _, _) => s == sid) with
        | none => simp [hfind] at hg
        | some sendEntry =>
          have hnotmem : sid ∉ σ.insts.map (·.sid) := fun hmem => by
            rcases List.mem_map.mp hmem with ⟨d, hd, rfl⟩
            exact hany (List.any_eq_true.mpr ⟨d, hd, beq_self_eq_true _⟩)
          have hinSends : sid ∈ σ.sends.map Prod.fst := by
            have hf := List.mem_of_find?_eq_some hfind
            have hbeq : (sendEntry.1 == sid) = true := by simpa using List.find?_some hfind
            have heq : sendEntry.1 = sid := beq_iff_eq.mp hbeq
            rw [← heq]
            exact List.mem_map_of_mem (f := Prod.fst) hf
          refine ⟨hsends, by simp only [List.length_append, List.length_singleton]; omega, ?_,
            fun s hs => ?_⟩
          · rw [List.map_append, List.map_singleton, List.nodup_append]
            exact ⟨hnodup, List.nodup_singleton _, fun x hx y hy hxy => by
              rw [List.mem_singleton] at hy; subst hy; subst hxy; exact hnotmem hx⟩
          · rw [List.map_append, List.map_singleton, List.mem_append, List.mem_singleton] at hs
            rcases hs with hs | rfl
            · exact hsub s hs
            · exact hinSends
    · exact hmono

private theorem shallowInstsBoundInv_stepLocalSm {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (C : Crypto) (K : MlKem) (qep : ℕ) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {qKiDone qStartDone : ℕ} {σH : BHE2EDrvState S ℓ × List τ}
    (hInv : shallowInstsBoundInv qKiDone qStartDone σH.1)
    (i : ℕ) (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    {out : BHE2ESmResp ℓ × (BHE2EDrvState S ℓ × List τ)}
    (hout : out ∈ support (bhE2EStepLocalSmSessionTracked T C K qep decT encT σH i sq)) :
    shallowInstsBoundInv qKiDone qStartDone out.2.1 := by
  rw [bhE2EStepLocalSmSessionTracked_eq_filter] at hout
  by_cases hclean : (!bhE2EDrvInstClean σH.1 i) = true
  · simp only [hclean, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hout
    subst hout; exact hInv
  · simp only [hclean, Bool.false_eq_true, ↓reduceIte] at hout
    cases hm1 : σH.1.insts[i]? with
    | none =>
      simp only [hm1, support_pure, Set.mem_singleton_iff] at hout
      subst hout; exact hInv
    | some d =>
      cases hm2 : σH.1.instMeta[i]? with
      | none =>
        simp only [hm1, hm2, support_pure, Set.mem_singleton_iff] at hout
        subst hout; exact hInv
      | some im =>
        simp only [hm1, hm2] at hout
        by_cases hcorr : (!im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σH.1 d) = true
        · simp only [hcorr, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hout
          subst hout
          exact ⟨hInv.1, hInv.2.1, hInv.2.2.1, hInv.2.2.2⟩
        · simp only [hcorr, Bool.false_eq_true, ↓reduceIte] at hout
          cases hgs : d.gs with
          | none =>
            simp only [hgs, support_pure, Set.mem_singleton_iff] at hout
            subst hout; exact hInv
          | some _ =>
            cases hflt :
                Computational.Proofs.LibsignalCli.MainHaltedPrefixCore.bhFilterSmQuery d im sq with
            | none =>
              simp only [hgs, hflt, support_pure, Set.mem_singleton_iff] at hout
              subst hout; exact hInv
            | some _ =>
              simp only [hgs, hflt, mem_support_bind_iff] at hout
              rcases hout with ⟨⟨⟨_, gs'⟩, _⟩, -, hret⟩
              simp only [support_pure, Set.mem_singleton_iff] at hret
              subst hret
              have hmap :=
                map_set_eq_self_local (·.sid) σH.1.insts i { d with gs := some gs' } d hm1 rfl
              rcases hInv with ⟨hsends, hinsts, hnodup, hsub⟩
              exact ⟨hsends, by simpa only [List.length_set] using hinsts,
                by rwa [hmap], by rwa [hmap]⟩

end Computational.Proofs.E2E.Dsl.CompositionHaltedPrefixEval
