/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.LibsignalCli.MainHaltedKeyInd -- proof-setup: allow-public-import
public import Computational.Proofs.LibsignalCli.MainHaltedPrefixCore -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.CompositionHaltedWitness -- proof-setup: allow-public-import
import Computational.Proofs.E2E.Dsl.KindRedHalted
public import Computational.Proofs.E2E.Dsl.KindRedHaltedInst -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.PrefixRedHaltedInst -- proof-setup: allow-public-import
import Computational.Proofs.E2E.Dsl.CompositionHaltedWitnessInst
import Computational.Proofs.E2E.Dsl.CompositionHaltedSimSpecInst
import Computational.Proofs.E2E.Dsl.HaltedStartSessionSim
import Computational.Proofs.E2E.Dsl.KindRedHaltedEval
import Computational.Proofs.E2E.Dsl.PqxdhSim
import Computational.Proofs.E2E.ComposedKeyIndHop
import Computational.Proofs.E2E.ComposedPrefixHelpers
import Computational.Proofs.E2E.Dsl.LocalSessionStep
import Computational.Proofs.E2E.Dsl.LocalSessionStepAux
import Computational.Proofs.E2E.Dsl.M3Subprograms
import Computational.Proofs.E2E.Dsl.StartAndExtSm
import Computational.Proofs.E2E.TagSync1KeyReal
import Computational.Proofs.Game.PromotedCostedReds.AtomicOpsHonest
import Computational.Proofs.GameHop.Advantage
import Computational.Proofs.GameHop.GlobalHybrid
import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds
import Computational.Proofs.ReductionDsl.SM.GameCosted
import Computational.Proofs.ReductionDsl.Soundness
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
# Clamped handshake reduction `1KeyReal` equivalence

Proves `kindRedHalted_clamped_1KeyRealExp_eq` by coupling `HaltedKindSimInvInst` with
`pqxdhKeyIndImpl1KeyReal` state-list bounds.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Computational.Proofs.E2E.CompositionHaltedKindReal

open scoped BigOperators
open OracleComp OracleSpec
open _root_.ReductionDsl (Sig Ops Iface Ty Env Expr Comp GameCodec CostedReduction
  atomicSig atomicE2EOps bits e2eKeyIndTargetIface e2eSessionTargetIface smQT smQenc
  sidT sidV keyIndQT keyIndRT keyIndQenc keyIndRenc BV256 E2EKeyIndTag)
open CryptoGames.CBC (Plain)
open CryptoGames.LibsignalSession (Crypto GhostState PublicKey)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.E2E (BHE2EDrvState BHModelInst BHTargetResp Bytes BhShallowRed
  CompositionCostedReductionFamily bhDrvKiQueryOk
  bhE2EDrvWon bhE2EFinishStartSpk bhE2EGuard bhE2EMirror bhBaseMirror bhFwdU bhLiftP
  bhNoOpkRespPromoted bhPackSmResp bhShallowImplOfHandle bhTargetGameSpec
  bhTargetQenc bhTargetRdec configRefuseEarlyBobCorr e2eTargetGameCodec
  paramsIdsWithSpqr sessionSchemeFixedSpk)
open Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge (KemFailSessionTrack)
open Computational.Proofs.LibsignalCli.MainHaltedKeyInd (bhKindRedWithTracked)
open Computational.Proofs.LibsignalCli.MainHaltedPrefixCore (bhClassifyTarget bhClassifyTargetOnly
  bhE2EStepLocalSmSessionTracked bhFilterSmQuery oracleImplRSessionTracked)
open Computational.Proofs.E2E.Dsl.KindRedHalted (HaltedKindSubprograms bhKindHandleWithHalted
  bhKindRedWithHalted drvKindHaltedEnc drvKindHaltedTy kindHandleHalted_eval_ctl
  kindHandleHalted_eval_ki kindHandleHalted_eval_sm kindRedHalted kindStartStepHaltedC
  mkAtomicRevealSpkSkE mkAtomicTestSessionE)
open Computational.Proofs.E2E.Dsl.KindRedHaltedEval (atomicKeyIndTargetIface_liftP_eq_bhLiftP
  atomicKindRespEnc e2eTargetGameCodec_rdec_atomicKindRespEnc mem_support_of_bhLiftP
  packAtomicSmRespEnc)
open Computational.Proofs.E2E.Dsl.CompositionHaltedWitness (HaltedTargetAdvPerInstanceBounded
  bhKindRedWithHalted_eq_bhKindRedWithTracked kemFailSessionTracker)
open Computational.Proofs.E2E.Dsl.CompositionHaltedWitnessInst (HaltedKindSimInvInst
  isQueryBoundP_min isSendKiQuery nextSendDone nextSessDone)
open Computational.Proofs.E2E.Dsl.CompositionHaltedSimSpecInst (StepBudgetOkInst StepNextInvInst
  isKiQ isSendQ isSendQ_inl_inl isSessQ isStartQ stepBudgetOkInst_of_bounds)
open Computational.Proofs.E2E.Dsl.M3Interfaces (DrvMirrorBounded)

private theorem st_run_get_bind {σ : Type} {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type}
    (k : σ → StateT σ m α) (s : σ) : (MonadState.get >>= k).run s = (k s).run s :=
  pure_bind (s, s) _

private theorem st_run_getOf_bind {σ : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    {α : Type} (k : σ → StateT σ m α) (s : σ) : (MonadStateOf.get >>= k).run s = (k s).run s :=
  pure_bind (s, s) _

private def StMono {S : SignalPqxdh.Setup} (st₀ st : SignalPqxdh.KeyIndState S) : Prop :=
  st₀.spkBundles.length ≤ st.spkBundles.length ∧ st₀.opkEntries.length ≤ st.opkEntries.length

private theorem stMono_refl {S : SignalPqxdh.Setup} (st : SignalPqxdh.KeyIndState S) :
    StMono st st := ⟨le_rfl, le_rfl⟩

private theorem stateT_mono_pure {S : SignalPqxdh.Setup} {α : Type} (a : α)
    {st₀ st : SignalPqxdh.KeyIndState S} (h : StMono st₀ st) :
    ∀ out ∈ support ((pure a : StateT (SignalPqxdh.KeyIndState S) ProbComp α).run st),
      StMono st₀ out.2 := by
  intro out hout
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
  subst hout; exact h

private theorem stateT_mono_bind {S : SignalPqxdh.Setup} {α β : Type}
    (m : StateT (SignalPqxdh.KeyIndState S) ProbComp α)
    (f : α → StateT (SignalPqxdh.KeyIndState S) ProbComp β)
    {st₀ st : SignalPqxdh.KeyIndState S}
    (hm : ∀ p ∈ support (m.run st), StMono st₀ p.2)
    (hf : ∀ a st1, StMono st₀ st1 → ∀ out ∈ support ((f a).run st1), StMono st₀ out.2) :
    ∀ out ∈ support ((m >>= f).run st), StMono st₀ out.2 := by
  intro out hout
  simp only [StateT.run_bind, mem_support_bind_iff] at hout
  rcases hout with ⟨p, hp, hout⟩
  exact hf p.1 p.2 (hm p hp) out hout

private theorem stateT_mono_getOf {S : SignalPqxdh.Setup} {α : Type}
    (f : SignalPqxdh.KeyIndState S → StateT (SignalPqxdh.KeyIndState S) ProbComp α)
    {st₀ st : SignalPqxdh.KeyIndState S}
    (hf : ∀ out ∈ support ((f st).run st), StMono st₀ out.2) :
    ∀ out ∈ support ((MonadStateOf.get >>= f).run st), StMono st₀ out.2 := by
  simpa only [st_run_getOf_bind] using hf

private theorem stateT_mono_lift {S : SignalPqxdh.Setup} {α : Type} (x : ProbComp α)
    {st₀ st : SignalPqxdh.KeyIndState S} (h : StMono st₀ st) :
    ∀ out ∈ support ((liftM x : StateT (SignalPqxdh.KeyIndState S) ProbComp α).run st),
      StMono st₀ out.2 := by
  intro out hout
  change out ∈ support (x >>= fun a => pure (a, st)) at hout
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
  rcases hout with ⟨_, -, rfl⟩
  exact h

private theorem stateT_mono_set {S : SignalPqxdh.Setup}
    {st₀ st st' : SignalPqxdh.KeyIndState S} (h : StMono st₀ st') :
    ∀ out ∈ support ((MonadStateOf.set st' : StateT (SignalPqxdh.KeyIndState S) ProbComp PUnit).run st),
      StMono st₀ out.2 := by
  intro out hout
  change out ∈ support (pure (PUnit.unit, st')) at hout
  simp only [support_pure, Set.mem_singleton_iff] at hout
  subst hout; exact h

private theorem st_run_lift_bind {σ : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β : Type} (x : m α) (k : α → StateT σ m β) (s : σ) :
    ((liftM x : StateT σ m α) >>= k).run s = (x >>= fun a => (k a).run s) := by
  change ((x >>= fun a => pure (a, s)) >>= fun p => (k p.1).run p.2) = _
  simp only [LawfulMonad.bind_assoc, pure_bind]

set_option linter.unusedSimpArgs false in
private theorem recordKeyIndResp_stMono {S : SignalPqxdh.Setup} (P : SignalPqxdh.Primitives)
    (r : SignalPqxdh.KeyIndRespEntry S) {st₀ st : SignalPqxdh.KeyIndState S} (h : StMono st₀ st) :
    ∀ out ∈ support ((SignalPqxdh.recordKeyIndResp S P r).run st), StMono st₀ out.2 := by
  intro out hmem
  unfold SignalPqxdh.recordKeyIndResp at hmem
  simp only [st_run_get_bind, st_run_getOf_bind, LawfulMonad.bind_assoc] at hmem
  rcases hpart : st.sessions.find? (fun s => SignalPqxdh.keyIndPartner P s r) with _ | s
  · rw [hpart] at hmem; dsimp only at hmem
    simp only [st_run_lift_bind, StateT.run_set, support_pure, mem_support_bind_iff,
      Set.mem_singleton_iff] at hmem
    rcases hmem with ⟨_, -, rfl⟩; exact h
  · rw [hpart] at hmem; dsimp only at hmem
    simp only [pure_bind, StateT.run_set, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; exact h

private theorem runKeyIndInitiate_stMono {S : SignalPqxdh.Setup} (P : SignalPqxdh.Primitives)
    (sid : SignalPqxdh.SessionId S) (u : Fin S.N_id) (bundle : SignalPqxdh.PreKeyBundleInput)
    {st₀ st : SignalPqxdh.KeyIndState S} (h : StMono st₀ st) :
    ∀ out ∈ support ((SignalPqxdh.runKeyIndInitiate false S P sid u bundle).run st),
      StMono st₀ out.2 := by
  dsimp only [SignalPqxdh.runKeyIndInitiate]
  refine stateT_mono_getOf _ ?_
  by_cases hc1 : (st.sessions.any (fun e => e.sid == sid)) = true
  · simp only [hc1, ↓reduceIte]; exact stateT_mono_pure _ h
  · simp only [hc1, Bool.false_eq_true, ↓reduceIte]
    split
    · next uEntry =>
      by_cases hc2 : (!SignalPqxdh.koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bundle) = true
      · simp only [hc2, ↓reduceIte]; exact stateT_mono_pure _ h
      · simp only [hc2, Bool.false_eq_true, ↓reduceIte]
        refine stateT_mono_bind _ _ (stateT_mono_lift _ h) fun ekASk _ h1 => ?_
        refine stateT_mono_bind _ _ (stateT_mono_lift _ h1) fun kemCoins _ h2 => ?_
        by_cases hc3 : (!(P.sigVerify (SignalPqxdh.resolveSigPk P st.principals bundle.ikB)
            (SignalPqxdh.encodeEC bundle.spkB) bundle.spkSig &&
          P.sigVerify (SignalPqxdh.resolveSigPk P st.principals bundle.ikB)
            (SignalPqxdh.encodeKEM bundle.pqspkB) bundle.pqspkSig)) = true
        · simp only [hc3, ↓reduceIte]; exact stateT_mono_pure _ h2
        · simp only [hc3, Bool.false_eq_true, ↓reduceIte]
          split
          · refine stateT_mono_bind _ _ (stateT_mono_lift _ h2) fun ⟨drKeyReal, roCache'⟩ _ h3 => ?_
            split
            · refine stateT_mono_bind _ _ (stateT_mono_pure _ h3) fun _ _ _ => ?_
              refine stateT_mono_bind _ _ (stateT_mono_set ⟨h.1, h.2⟩) fun _ _ h4 => ?_
              split <;> exact stateT_mono_pure _ h4
            · refine stateT_mono_bind _ _ (stateT_mono_lift _ h3) fun _ _ _ => ?_
              refine stateT_mono_bind _ _ (stateT_mono_set ⟨h.1, h.2⟩) fun _ _ h4 => ?_
              split <;> exact stateT_mono_pure _ h4
          · exact stateT_mono_pure _ h2
    · exact stateT_mono_pure _ h

set_option linter.unusedSimpArgs false in
private theorem pqxdh1KeyReal_stMono {S : SignalPqxdh.Setup} (P : SignalPqxdh.Primitives)
    (kq : SignalPqxdh.KeyIndQuery S) (st : SignalPqxdh.KeyIndState S) :
    ∀ out ∈ support ((SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P kq).run st), StMono st out.2 := by
  have h0 := stMono_refl st
  cases kq with
  | initPrin u =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal; dsimp only
    refine stateT_mono_getOf _ ?_
    by_cases hc : (st.principals.any (fun (idx, _) => idx == u.val)) = true
    · simp only [hc, ↓reduceIte]; exact stateT_mono_pure _ h0
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      refine stateT_mono_bind _ _ (stateT_mono_lift _ h0) fun _ _ _ => ?_
      exact stateT_mono_bind _ _ (stateT_mono_set h0) fun _ _ h2 => stateT_mono_pure _ h2
  | roQuery secrets =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal; dsimp only
    refine stateT_mono_getOf _ ?_
    refine stateT_mono_bind _ _ (stateT_mono_lift _ h0) fun ⟨_, _⟩ _ _ => ?_
    exact stateT_mono_bind _ _ (stateT_mono_set h0) fun _ _ h2 => stateT_mono_pure _ h2
  | revealDhSecrets =>
    exact stateT_mono_pure _ h0
  | corruptIK u =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl; dsimp only
    refine stateT_mono_getOf _ ?_
    split
    · exact stateT_mono_pure _ h0
    · exact stateT_mono_bind _ _ (stateT_mono_set h0) fun _ _ h2 => stateT_mono_pure _ h2
  | genSPK u j =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl; dsimp only
    refine stateT_mono_getOf _ ?_
    by_cases hc : (st.spkBundles.any (fun (k, _) => k == (u.val, j.val))) = true
    · simp only [hc, ↓reduceIte]; exact stateT_mono_pure _ h0
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      split
      · refine stateT_mono_bind _ _ (stateT_mono_lift _ h0) fun _ _ h0 => ?_
        refine stateT_mono_bind _ _ (stateT_mono_lift _ h0) fun _ _ h0 => ?_
        refine stateT_mono_bind _ _ (stateT_mono_lift _ h0) fun ⟨_, _⟩ _ h0 => ?_
        refine stateT_mono_bind _ _ (stateT_mono_lift _ h0) fun _ _ _ => ?_
        refine stateT_mono_bind _ _ (stateT_mono_set ⟨Nat.le_succ _, le_rfl⟩) fun _ _ h5 =>
          stateT_mono_pure _ h5
      · exact stateT_mono_pure _ h0
  | genOPK u j o =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl; dsimp only
    refine stateT_mono_getOf _ ?_
    by_cases hc : (st.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val))) = true
    · simp only [hc, ↓reduceIte]; exact stateT_mono_pure _ h0
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      refine stateT_mono_bind _ _ (stateT_mono_lift _ h0) fun _ _ _ => ?_
      refine stateT_mono_bind _ _ (stateT_mono_set ⟨le_rfl, Nat.le_succ _⟩) fun _ _ h2 =>
        stateT_mono_pure _ h2
  | initiateOPK u i bundle =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl; dsimp only
    refine stateT_mono_getOf _ ?_
    by_cases hc : bundle.opkB?.isNone = true
    · simp only [hc, ↓reduceIte]; exact stateT_mono_pure _ h0
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact runKeyIndInitiate_stMono P (.sendOPK u i) u bundle h0
  | initiateNoOPK u i bundle =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl; dsimp only
    refine stateT_mono_getOf _ ?_
    by_cases hc : bundle.opkB?.isSome = true
    · simp only [hc, ↓reduceIte]; exact stateT_mono_pure _ h0
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact runKeyIndInitiate_stMono P (.sendNoOPK u i) u bundle h0
  | acceptOPK k j o hdr =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl; dsimp only
    refine stateT_mono_getOf _ ?_
    by_cases hc1 : (!(hdr.spkId == UInt32.ofNat j.val &&
         hdr.pqspkId == UInt32.ofNat j.val &&
         hdr.opkId? == some (UInt32.ofNat o.val) &&
         hdr.ikAPk.length == 32 &&
         hdr.ekAPk.length == 32)) = true
    · simp only [hc1, ↓reduceIte]; exact stateT_mono_pure _ h0
    · simp only [hc1, Bool.false_eq_true, ↓reduceIte]
      by_cases hc2 : (st.usedRecvOPK.contains (k.val, j.val, o.val)) = true
      · simp only [hc2, ↓reduceIte]; exact stateT_mono_pure _ h0
      · simp only [hc2, Bool.false_eq_true, ↓reduceIte]
        by_cases hc3 : (!SignalPqxdh.koskSenderOk P st.principals st.advKeys hdr.ikAPk) = true
        · simp only [hc3, ↓reduceIte]; exact stateT_mono_pure _ h0
        · simp only [hc3, Bool.false_eq_true, ↓reduceIte]
          split
          · split
            · split
              · split_ifs
                · exact stateT_mono_pure _ h0
                · split
                  · split
                    · refine stateT_mono_bind _ _ (stateT_mono_lift _ h0) fun ⟨_, _⟩ _ _ => ?_
                      refine stateT_mono_bind _ _ (stateT_mono_set ⟨le_rfl, by simp⟩) fun _ _ h2 => ?_
                      refine stateT_mono_bind _ _ (recordKeyIndResp_stMono P _ h2) fun _ _ h3 => ?_
                      split <;> exact stateT_mono_pure _ h3
                    · exact stateT_mono_pure _ h0
                  · exact stateT_mono_pure _ h0
              · exact stateT_mono_pure _ h0
            · exact stateT_mono_pure _ h0
          · exact stateT_mono_pure _ h0
  | acceptNoOPK k j l hdr =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl; dsimp only
    refine stateT_mono_getOf _ ?_
    by_cases hc1 : (!(hdr.spkId == UInt32.ofNat j.val &&
         hdr.pqspkId == UInt32.ofNat j.val &&
         hdr.opkId? == none &&
         hdr.ikAPk.length == 32 &&
         hdr.ekAPk.length == 32)) = true
    · simp only [hc1, ↓reduceIte]; exact stateT_mono_pure _ h0
    · simp only [hc1, Bool.false_eq_true, ↓reduceIte]
      by_cases hc2 : (st.usedRecvNoOPK.contains (k.val, j.val, l.val)) = true
      · simp only [hc2, ↓reduceIte]; exact stateT_mono_pure _ h0
      · simp only [hc2, Bool.false_eq_true, ↓reduceIte]
        by_cases hc3 : (!SignalPqxdh.koskSenderOk P st.principals st.advKeys hdr.ikAPk) = true
        · simp only [hc3, ↓reduceIte]; exact stateT_mono_pure _ h0
        · simp only [hc3, Bool.false_eq_true, ↓reduceIte]
          split
          · split
            · split
              · split
                · refine stateT_mono_bind _ _ (stateT_mono_lift _ h0) fun ⟨_, _⟩ _ _ => ?_
                  refine stateT_mono_bind _ _ (stateT_mono_set h0) fun _ _ h2 => ?_
                  refine stateT_mono_bind _ _ (recordKeyIndResp_stMono P _ h2) fun _ _ h3 => ?_
                  split <;> exact stateT_mono_pure _ h3
                · exact stateT_mono_pure _ h0
              · exact stateT_mono_pure _ h0
            · exact stateT_mono_pure _ h0
          · exact stateT_mono_pure _ h0
  | testSession sid =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl; dsimp only
    refine stateT_mono_getOf _ ?_
    by_cases hc : (!SignalPqxdh.isKeyIndSessionTestable st sid) = true
    · simp only [hc, ↓reduceIte]; exact stateT_mono_pure _ h0
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      split
      · exact stateT_mono_bind _ _ (stateT_mono_set h0) fun _ _ h2 => stateT_mono_pure _ h2
      · split
        · exact stateT_mono_pure _ h0
        · exact stateT_mono_bind _ _ (stateT_mono_set h0) fun _ _ h2 => stateT_mono_pure _ h2
  | revealSessionKey sid =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl; dsimp only
    refine stateT_mono_getOf _ ?_
    split
    · split_ifs
      · exact stateT_mono_pure _ h0
      · exact stateT_mono_bind _ _ (stateT_mono_set h0) fun _ _ h2 => stateT_mono_pure _ h2
    · split
      · exact stateT_mono_pure _ h0
      · split_ifs
        · exact stateT_mono_pure _ h0
        · exact stateT_mono_bind _ _ (stateT_mono_set h0) fun _ _ h2 => stateT_mono_pure _ h2
  | revealSpkSk u j =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl; dsimp only
    refine stateT_mono_getOf _ ?_
    split
    · exact stateT_mono_pure _ h0
    · refine stateT_mono_bind _ _ (stateT_mono_set ⟨by simp, le_rfl⟩) fun _ _ h2 =>
        stateT_mono_pure _ h2
  | registerKey sk =>
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl; dsimp only
    refine stateT_mono_getOf _ ?_
    split
    · exact stateT_mono_pure _ h0
    · exact stateT_mono_bind _ _ (stateT_mono_set h0) fun _ _ h2 => stateT_mono_pure _ h2

set_option linter.unusedSimpArgs false in
private theorem pqxdh1KeyReal_genSPK_succ {S : SignalPqxdh.Setup} (P : SignalPqxdh.Primitives)
    (u : Fin S.N_id) (j : Fin S.N_recv) (st : SignalPqxdh.KeyIndState S)
    {out : SignalPqxdh.KeyIndResponse × SignalPqxdh.KeyIndState S}
    (hmem : out ∈ support ((SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P (.genSPK u j)).run st))
    (hresp : out.1 matches .bundleResp ..) :
    out.2.spkBundles.length = st.spkBundles.length + 1 := by
  unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl at hmem
  simp only [st_run_get_bind, st_run_getOf_bind, LawfulMonad.bind_assoc] at hmem
  by_cases hc : (st.spkBundles.any (fun (k, _) => k == (u.val, j.val))) = true
  · simp only [hc, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; nomatch hresp
  · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hmem
    rcases hp : st.principals.find? (fun (idx, _) => idx == u.val) with _ | ⟨_, uEntry⟩
    · rw [hp] at hmem; dsimp only at hmem
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; nomatch hresp
    · rw [hp] at hmem; dsimp only at hmem
      simp only [st_run_lift_bind, StateT.run_set, StateT.run_pure, pure_bind,
        LawfulMonad.bind_assoc, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hmem
      rcases hmem with ⟨_, -, _, -, ⟨_, _⟩, -, _, -, rfl⟩
      simp

set_option linter.unusedSimpArgs false in
private theorem pqxdh1KeyReal_genOPK_succ {S : SignalPqxdh.Setup} (P : SignalPqxdh.Primitives)
    (u : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (st : SignalPqxdh.KeyIndState S)
    {out : SignalPqxdh.KeyIndResponse × SignalPqxdh.KeyIndState S}
    (hmem : out ∈ support ((SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P (.genOPK u j o)).run st))
    (hresp : out.1 matches .pkResp ..) :
    out.2.opkEntries.length = st.opkEntries.length + 1 := by
  unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal SignalPqxdh.pqxdhKeyIndImpl at hmem
  simp only [st_run_get_bind, st_run_getOf_bind, LawfulMonad.bind_assoc] at hmem
  by_cases hc : (st.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val))) = true
  · simp only [hc, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; nomatch hresp
  · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hmem
    simp only [st_run_lift_bind, StateT.run_set, StateT.run_pure, pure_bind,
      LawfulMonad.bind_assoc, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hmem
    rcases hmem with ⟨_, -, rfl⟩
    simp

private structure KindRealInv {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (C : Crypto) (K : MlKem) (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (qKiDone qSendDone qStartDone : ℕ) (qSessDone : ℕ → ℕ)
    (σst : (BHE2EDrvState S ℓ × List (KemFailSessionTrack C.F Bytes)) × SignalPqxdh.KeyIndState S) :
    Prop where
  base : HaltedKindSimInvInst (Dsl.PrefixRedHaltedInst.KemBridgeTrackInvLocal C.F K)
    C K b qStart qs qKiDone qSendDone qStartDone qSessDone σst.1
  st_list : Dsl.PqxdhSimTypes.stListBounded S qKiDone σst.2
  bundles_le_st : σst.1.1.bundles.length ≤ σst.2.spkBundles.length
  opks_le_st : σst.1.1.opks.length ≤ σst.2.opkEntries.length

private theorem KindRealInv.drvMirrorBounded_clamped {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {C : Crypto} {K : MlKem} {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    {qKiDone qSendDone qStartDone : ℕ} {qSessDone : ℕ → ℕ}
    {σst : (BHE2EDrvState S ℓ × List (KemFailSessionTrack C.F Bytes)) × SignalPqxdh.KeyIndState S}
    (h : KindRealInv C K b qStart qs qKiDone qSendDone qStartDone qSessDone σst) :
    DrvMirrorBounded b.q_total (min b.q_total S.N_spk_tot) (min b.q_total S.N_opk_tot)
      (min b.q_total S.N_send_tot) b.q_total (min qStart (min b.q_total S.N_send_tot)) σst.1.1 where
  prins_le := Nat.le_trans h.base.mirror.prins_le h.base.ki_le
  bundles_le := Nat.le_trans h.bundles_le_st ((h.st_list.mono h.base.ki_le).spkBundles_le)
  opks_le := Nat.le_trans h.opks_le_st ((h.st_list.mono h.base.ki_le).opkEntries_le)
  sends_le := h.base.sends_length_le
  corrPrins_le := Nat.le_trans h.base.mirror.corrPrins_le h.base.ki_le
  insts_le := h.base.insts_length_le
  instMeta_le := h.base.instMeta_length_le
  revSpks_le := Nat.le_trans h.base.mirror.revSpks_le h.base.ki_le

private def kiNoOpkPromoted {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (σ : BHE2EDrvState S ℓ) : SignalPqxdh.KeyIndQuery S → Bool
  | .corruptIK u => bhNoOpkRespPromoted σ.instMeta u
  | _ => false

private theorem atomicKeyIndLiftP_map {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt α β : Type}
    (f : α → β) (p : ProbComp α) :
    (e2eKeyIndTargetIface S ℓ Pt).liftP (f <$> p) =
      f <$> (e2eKeyIndTargetIface S ℓ Pt).liftP p := by
  simp [atomicKeyIndTargetIface_liftP_eq_bhLiftP, bhLiftP]

private theorem eval_query_keyInd {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (qE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S))
    (ρ : Env Γ) (kq : SignalPqxdh.KeyIndQuery S)
    (hq : qE.eval ρ = keyIndQenc kq) :
    (Comp.query (O := atomicE2EOps ℓ P C K decT encT)
      (I := e2eKeyIndTargetIface S ℓ Pt) E2EKeyIndTag.keyInd qE).eval ρ =
      keyIndRenc <$>
        (liftM ((unifSpec + SignalPqxdh.keyIndSpec S).query (.inr kq)) :
          OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) _) := by
  dsimp only [Comp.eval, e2eKeyIndTargetIface]
  rw [hq, Dsl.KindRedHalted.keyIndQdec_keyIndQenc]

private theorem comp_eval_bind_sample_bv256 {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt}
    {encT : Pt → PublicKey} {Γ : List (Ty (atomicSig ℓ Pt))} {b : Ty (atomicSig ℓ Pt)}
    (c2 : Comp (atomicE2EOps ℓ P C K decT encT) (e2eKeyIndTargetIface S ℓ Pt)
      (BV256 (ℓ := ℓ) (Pt := Pt) :: Γ) b) (ρ : Env Γ) :
    (Comp.bind (.sample (I := e2eKeyIndTargetIface S ℓ Pt)
      (_root_.ReductionDsl.UniformSamplerTag.base _root_.ReductionDsl.AtomicBaseUnif.bv256) .unit) c2).eval ρ =
      (bhLiftP (G := SignalPqxdh.keyIndSpec S) ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>=
        fun bv => c2.eval (.cons bv ρ)) := by
  dsimp only [Comp.eval, e2eKeyIndTargetIface, _root_.ReductionDsl.atomicBaseSamplers,
    _root_.ReductionDsl.unifSamplers]
  rw [atomicKeyIndTargetIface_liftP_eq_bhLiftP]; rfl

private theorem comp_eval_bind {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (atomicSig ℓ Pt))} {a b : Ty (atomicSig ℓ Pt)}
    (c1 : Comp (atomicE2EOps ℓ P C K decT encT) (e2eKeyIndTargetIface S ℓ Pt) Γ a)
    (c2 : Comp (atomicE2EOps ℓ P C K decT encT) (e2eKeyIndTargetIface S ℓ Pt) (a :: Γ) b) (ρ : Env Γ) :
    (Comp.bind c1 c2).eval ρ = (c1.eval ρ >>= fun x => c2.eval (.cons x ρ)) := rfl

private theorem comp_eval_ret {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (atomicSig ℓ Pt))} {a : Ty (atomicSig ℓ Pt)}
    (e : Expr (atomicE2EOps ℓ P C K decT encT) Γ a) (ρ : Env Γ) :
    (Comp.ret (I := e2eKeyIndTargetIface S ℓ Pt) e).eval ρ = pure (e.eval ρ) := rfl

private theorem comp_eval_caseOpt {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (atomicSig ℓ Pt))} {a b : Ty (atomicSig ℓ Pt)}
    (e : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.opt a))
    (cN : Comp (atomicE2EOps ℓ P C K decT encT) (e2eKeyIndTargetIface S ℓ Pt) Γ b)
    (cS : Comp (atomicE2EOps ℓ P C K decT encT) (e2eKeyIndTargetIface S ℓ Pt) (a :: Γ) b) (ρ : Env Γ) :
    (Comp.caseOpt e cN cS).eval ρ = match e.eval ρ with | none => cN.eval ρ | some x => cS.eval (.cons x ρ) := by
  dsimp only [Comp.eval]; cases e.eval ρ <;> rfl

private theorem unpack_qb {ι : Type} {spec : OracleSpec ι} {α : Type}
    {Pred : ι → Prop} [DecidablePred Pred] {q : ι} {mx : spec.Range q → OracleComp spec α} {n : ℕ}
    (h : (liftM (OracleSpec.query (spec := spec) q) >>= mx).IsQueryBoundP Pred n) :
    (Pred q → 0 < n ∧ ∀ v, (mx v).IsQueryBoundP Pred (n - 1)) ∧
    (¬Pred q → ∀ v, (mx v).IsQueryBoundP Pred n) := by
  rw [isQueryBoundP_query_bind_iff] at h
  refine ⟨fun hp => ⟨h.1.resolve_left (fun hnp => hnp hp), fun v => ?_⟩, fun hnp v => ?_⟩
  · simpa [hp] using h.2 v
  · simpa [hnp] using h.2 v

end Computational.Proofs.E2E.CompositionHaltedKindReal
