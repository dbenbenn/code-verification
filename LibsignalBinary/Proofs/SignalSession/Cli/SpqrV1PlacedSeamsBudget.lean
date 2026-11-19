/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.V1.BobTailV1PlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.SpqrV1.M4.VerifyMacTrapPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.TripleRatchet.Encrypt.RootPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.StepSpqrPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.TrapBridgePlaced -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeams
public import LibsignalBinary.Proofs.SpecLemmas.LibsignalE2E.PqxdhCorrectModelProofDefs
import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.ErrorDisplayTag -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1PlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Statements
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SendCodeSym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.TripleRatchet.CliRatchetCodeSymA -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.TripleRatchet.SpqrSendEmpty.CorePlacedBudget -- proof-setup: allow-public-import
public import ProofLib.Disproof.Basic
public import ProofLib.Placed.OpcodeExclusion
public import ProofLib.RegChain
import LibsignalBinary.Proofs.SpecLemmas.RoLiterals
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.TripleRatchet.SpqrSendEmpty.CoreBudget

/-!
# Budget-Threaded SPQR-V1 Placed Entry-Point Seam Bundle

Packages the three relocatable `[LibsignalPlacement]` SPQR-V1 entry-block budget contracts
(Blocks 327, 329, 427) in envelope-parametric (`SpqrV1PlacedSeamsOfEnv`) and default
bounded-envelope (`SpqrV1PlacedSeams`) forms, together with cross-block caller transfer lemmas.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget

export CryptoVerification.SignalSession.Cli
  (blockLib_327_externs blockLib_329_externs
   instIsLsBlockProg_blockProgram_327 instIsLsBlockProg_blockProgram_329)

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (IsLsBlockProg LibsignalPlacement libsignalSessionLib lsProg_75 lsmpl)
open CryptoVerification.CliHandshake.InitiatePlaced (instIsLsBlockProg_521 lsProg_521)
open CryptoVerification.CliRatchet.Placed (blkPC_428 blkPl_428)
open CryptoVerification.CliRatchet.SendPlaced (blkPC_427 blkPl_427 instIsLsBlockProg_427)
open CryptoVerification.E2E (pqxdhSpqrModel)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (ls_subroutine_ok_rocl_of_block subroutine_ok_withLsCodeRoLoaded_of_rocl)
open CryptoVerification.LibsignalSpqrV1
  (MlKem Params SpqrRecvModel recvResultAtX_entails_recvResultAt recvResultExactKeyAt
   spqrV1 spqrV1Recv spqrV1Recv_eq spqrV1_eq)
open CryptoVerification.LibsignalTripleRatchet
  (SendCall SpqrModel VecArg spqrRecvResultAt spqrRecvStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive (spqrRecvRawSpec)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.Slots
  (subroutine_ok_cliPlaced_of_trTrap trTrapExternsPlaced)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.Cli.E2E.V1.BobTailV1PlacedBudget
  (InitialStateMemInvPlacedOk InitialStateMemInvPlacedOkOfEnv
   spqrInitialStatePlacedInnerSpec spqrInitialStatePlacedInnerSpecOfEnv)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.VerifyMacTrapPlacedBudget (lsLogOff_eq_logOff_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget (SpqrSendCoinsEnv)
open LibsignalBinary.Proofs.Cli.TripleRatchet.SpqrSendEmpty.CorePlacedBudget
  (spqrSendCoinsDispPlacedSpec spqrSendCoinsPlacedSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.StepSpqrPlacedBudget
  (spqrInitialStateInnerSpec)
open LibsignalBinary.Proofs.SpqrV1.ErrorDisplayTag
  (recvResultExactKeyDispAt recvResultExactKeyDispAt_entails_exactKeyAt
   recvResultExactKeyDispAt_entails_spqrRecvResultDispAt spqrRecvResultDispAt_entails_spqrRecvResultAt
   spqrSendResultDispAt_entails_spqrSendResultAt)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (SpqrBoundedEvs)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget (InitialStateEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1PlacedBudget (SpqrRecvEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs
  (spqrRecvRawDispSpec spqrRecvRawDispSpecPlaced spqrRecvRawSpecPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs.Simp
  (spqrRecvResultAt_atState spqrRecvResultDispAt_atState vecArg_at_atState)

/-!
## 1. Byte-Indexed Default Envelopes Matching `InitialStateEnv`, `SpqrRecvEnv`, `SpqrSendCoinsEnv`
-/

/-- `Params`-indexed form of `InitialStateEnv F` (`(fun x => InitialStateParamsEnv F x.p) = InitialStateEnv F`
    definitionally), matching `StepSpqrPlacedBudget.spqrInitialStateInnerSpec`. -/
@[expose] def InitialStateParamsEnv (_F : ShaCompress) (p : Params) (evs : List AllocEvent) : Prop :=
  match p.version with
  | .v0 => evs = []
  | .v1 => SpqrBoundedEvs 128 (4 * p.authKey.length + 4096) evs

theorem initialStateParamsEnv_nonempty (F : ShaCompress) (p : Params) :
    ∃ evs, InitialStateParamsEnv F p evs := by
  cases h : p.version <;> simp only [InitialStateParamsEnv, h]
  · exact ⟨[], rfl⟩
  · exact ⟨[], SpqrBoundedEvs.nil _ _⟩

/-- Byte-slice-indexed form of `SpqrRecvEnv`
    (`(fun st msg : VecArg => SpqrRecvBytesEnv st.bytes msg.bytes) = SpqrRecvEnv` definitionally),
    matching `DecryptPlacedBudget.spqrRecvPlacedSpecXT`. -/
@[expose] def SpqrRecvBytesEnv (st msg : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  SpqrBoundedEvs 512 (4 * st.length + 4 * msg.length + 16384) evs

theorem spqrRecvBytesEnv_nonempty (st msg : List (BitVec 8)) :
    ∃ evs, SpqrRecvBytesEnv st msg evs :=
  ⟨[], SpqrBoundedEvs.nil 512 (4 * st.length + 4 * msg.length + 16384)⟩

/-- Byte-slice-indexed form of `SpqrSendCoinsEnv`
    (`(fun sc : SendCall => SpqrSendCoinsBytesEnv sc.st.bytes sc.rest) = SpqrSendCoinsEnv`
    definitionally), matching `RootPlacedBudget.otrEncryptV1_coins_placed_ok`. -/
@[expose] def SpqrSendCoinsBytesEnv (st _rest : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  SpqrBoundedEvs 512 (4 * st.length + 16384) evs

theorem spqrSendCoinsBytesEnv_nonempty (st rest : List (BitVec 8)) :
    ∃ evs, SpqrSendCoinsBytesEnv st rest evs :=
  ⟨[], SpqrBoundedEvs.nil 512 (4 * st.length + 16384)⟩

/-! ## 2. Budget-Threaded Inner Entry Specifications (`Blocks 329, 427`) -/

/-- Envelope-parametric image-free `[LibsignalPlacement]` inner `Spec` of `spqrRecvSpecExactKey`
    (Block `329`, `spqr::recv`), dropping `allocFailedIn` from `onPanic` while retaining genuine
    protocol panics `R.recvPanics`. -/
@[expose] def spqrRecvPlacedInnerSpecXOfEnv [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (R : SpqrRecvModel)
    (RecvEnv : VecArg → VecArg → List AllocEvent → Prop) :
    Spec ((VecArg × VecArg × BitVec 64) × M.σ) where
  pre := fun ((st, msg, ret), stB) s =>
    ⌜FitsEnv M lim stB (RecvEnv st msg)⌝ ∗
      ⌜s.readReg64 .x0 = st.v ∧ s.readReg64 .x1 = msg.v ∧ s.readReg64 .x8 = ret⌝ ∗
      st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
      lsLogOff ∗ A.pool lim stB s ∗ stackAt s.sp spqrRecvStack
  post := fun ((st, msg, ret), stB) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜RecvEnv st msg evs⌝ ∗
      ⌜sf.trace = s0.trace ∧ ¬ R.recvPanics st.bytes msg.bytes⌝ ∗
      st.at A.repAlloc ∗ msg.at A.repAlloc ∗
      recvResultExactKeyAt A.repAlloc ret (R.recv st.bytes msg.bytes) ∗
      lsLogOff ∗ A.pool lim (M.stepEvents evs stB) sf ∗
      stackAt s0.sp spqrRecvStack
  onPanic := fun ((st, msg, _), _) s0 sf =>
    ⌜R.recvPanics st.bytes msg.bytes ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Default budget-threaded `[LibsignalPlacement]` `spqrRecvPlacedInnerSpecX` at `SpqrRecvEnv`. -/
abbrev spqrRecvPlacedInnerSpecX [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (R : SpqrRecvModel) :
    Spec ((VecArg × VecArg × BitVec 64) × M.σ) :=
  spqrRecvPlacedInnerSpecXOfEnv M A lim R SpqrRecvEnv

/-- Envelope-parametric image-free `[LibsignalPlacement]` inner `Spec` of
    `spqrRecvSpecExactKeyBounded` (Block `329`, `spqr::recv`) with `tokenInitPlacedAt` framed and
    `st.bytes.length < 2 ^ 32`, `msg.bytes.length < 2 ^ 40`, and `spqrRecvStack ≤ s.sp.toNat`. -/
@[expose] def spqrRecvPlacedInnerSpecXTOfEnv [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (R : SpqrRecvModel)
    (RecvEnv : VecArg → VecArg → List AllocEvent → Prop) :
    Spec ((VecArg × VecArg × BitVec 64) × M.σ) :=
  { spqrRecvPlacedInnerSpecXOfEnv M A lim R RecvEnv with
    pre := fun (x, stB) s =>
      ⌜x.1.bytes.length < 2 ^ 32 ∧ x.2.1.bytes.length < 2 ^ 40 ∧ spqrRecvStack ≤ s.sp.toNat⌝ ∗
        tokenInitPlacedAt ∗
        (spqrRecvPlacedInnerSpecXOfEnv M A lim R RecvEnv).pre (x, stB) s
    post := fun (x, stB) s0 sf =>
      tokenInitPlacedAt ∗
        (spqrRecvPlacedInnerSpecXOfEnv M A lim R RecvEnv).post (x, stB) s0 sf }

/-- Default budget-threaded `[LibsignalPlacement]` `spqrRecvPlacedInnerSpecXT` at `SpqrRecvEnv`. -/
abbrev spqrRecvPlacedInnerSpecXT [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (R : SpqrRecvModel) :
    Spec ((VecArg × VecArg × BitVec 64) × M.σ) :=
  spqrRecvPlacedInnerSpecXTOfEnv M A lim R SpqrRecvEnv

/-- Display-tag-strengthened (`recvResultExactKeyDispAt`, carrying `SpqrErrorValidTag d` on
    `.error sd`) envelope-parametric image-free `[LibsignalPlacement]` inner `Spec` of
    `spqrRecvSpecExactKey` (Block `329`, `spqr::recv`). -/
@[expose] def spqrRecvPlacedInnerDispSpecXOfEnv [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (R : SpqrRecvModel)
    (RecvEnv : VecArg → VecArg → List AllocEvent → Prop) :
    Spec ((VecArg × VecArg × BitVec 64) × M.σ) where
  pre := (spqrRecvPlacedInnerSpecXOfEnv M A lim R RecvEnv).pre
  post := fun ((st, msg, ret), stB) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜RecvEnv st msg evs⌝ ∗
      ⌜sf.trace = s0.trace ∧ ¬ R.recvPanics st.bytes msg.bytes⌝ ∗
      st.at A.repAlloc ∗ msg.at A.repAlloc ∗
      recvResultExactKeyDispAt A.repAlloc ret (R.recv st.bytes msg.bytes) ∗
      lsLogOff ∗ A.pool lim (M.stepEvents evs stB) sf ∗
      stackAt s0.sp spqrRecvStack
  onPanic := (spqrRecvPlacedInnerSpecXOfEnv M A lim R RecvEnv).onPanic

/-- Default display-tag-strengthened `[LibsignalPlacement]` `spqrRecvPlacedInnerDispSpecX` at
    `SpqrRecvEnv`. -/
abbrev spqrRecvPlacedInnerDispSpecX [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (R : SpqrRecvModel) :
    Spec ((VecArg × VecArg × BitVec 64) × M.σ) :=
  spqrRecvPlacedInnerDispSpecXOfEnv M A lim R SpqrRecvEnv

/-- Display-tag-strengthened (`recvResultExactKeyDispAt`) envelope-parametric image-free
    `[LibsignalPlacement]` inner `Spec` of `spqrRecvSpecExactKeyBounded` (Block `329`, `spqr::recv`)
    with `tokenInitPlacedAt` framed and `st.bytes.length < 2 ^ 32`, `msg.bytes.length < 2 ^ 40`,
    `spqrRecvStack ≤ s.sp.toNat`. -/
@[expose] def spqrRecvPlacedInnerDispSpecXTOfEnv [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (R : SpqrRecvModel)
    (RecvEnv : VecArg → VecArg → List AllocEvent → Prop) :
    Spec ((VecArg × VecArg × BitVec 64) × M.σ) :=
  { spqrRecvPlacedInnerDispSpecXOfEnv M A lim R RecvEnv with
    pre := fun (x, stB) s =>
      ⌜x.1.bytes.length < 2 ^ 32 ∧ x.2.1.bytes.length < 2 ^ 40 ∧ spqrRecvStack ≤ s.sp.toNat⌝ ∗
        tokenInitPlacedAt ∗
        (spqrRecvPlacedInnerDispSpecXOfEnv M A lim R RecvEnv).pre (x, stB) s
    post := fun (x, stB) s0 sf =>
      tokenInitPlacedAt ∗
        (spqrRecvPlacedInnerDispSpecXOfEnv M A lim R RecvEnv).post (x, stB) s0 sf }

/-- Default display-tag-strengthened `[LibsignalPlacement]` `spqrRecvPlacedInnerDispSpecXT` at
    `SpqrRecvEnv`. -/
abbrev spqrRecvPlacedInnerDispSpecXT [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (R : SpqrRecvModel) :
    Spec ((VecArg × VecArg × BitVec 64) × M.σ) :=
  spqrRecvPlacedInnerDispSpecXTOfEnv M A lim R SpqrRecvEnv

/-- Monotonicity downgrade from `spqrRecvPlacedInnerDispSpecXTOfEnv` to
    `spqrRecvPlacedInnerSpecXTOfEnv` under `StoreKit.withLsCodeRoLoaded`. -/
theorem spqrRecvPlacedInnerDispSpecXT_imp_innerSpecXT [LibsignalPlacement]
    {M : AllocCostModel} {prog : Program} {entry : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {R : SpqrRecvModel}
    {RecvEnv : VecArg → VecArg → List AllocEvent → Prop}
    (h : subroutine_ok prog entry
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrRecvPlacedInnerDispSpecXTOfEnv M A lim R RecvEnv))) :
    subroutine_ok prog entry
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrRecvPlacedInnerSpecXTOfEnv M A lim R RecvEnv)) := by
  refine subroutine_ok_mono h
    (fun _ _ _ hpre => hpre)
    (fun ((st, msg, ret), stB) _ _ _ hpost => by
      dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
        spqrRecvPlacedInnerDispSpecXTOfEnv, spqrRecvPlacedInnerDispSpecXOfEnv,
        spqrRecvPlacedInnerSpecXTOfEnv, spqrRecvPlacedInnerSpecXOfEnv] at hpost ⊢
      refine Satisfies.mono (sepConj_mono_left (sepConj_mono_right
        (Entails.sepExists_mono fun evs => sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
            (recvResultExactKeyDispAt_entails_exactKeyAt A.repAlloc ret
              (R.recv st.bytes msg.bytes))))))))) hpost)
    (fun _ _ _ _ hpan => hpan)
    (fun _ _ _ _ _ he => he)

/-- Envelope-parametric image-free `[LibsignalPlacement]` inner `Spec` of `spqrSendSpecT` for
    `<Coins>` (Block `427`) strengthened with `spqrSendResultDispAt` (`SpqrErrorValidTag d` on
    `none`), with `tokenInitPlacedAt` framed and `st.bytes.length < 2 ^ 32`, `64 ≤ rest.length`,
    definitionally matching the `hSend` hypothesis of `RootPlacedBudget.otrEncryptV1_coins_placed_ok`
    at `F := tokenInitPlacedAt`. -/
@[expose] def spqrSendCoinsPlacedSpecTOfEnv [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    (SendEnv : SendCall → List AllocEvent → Prop) :
    Spec (SendCall × M.σ) :=
  { spqrSendCoinsDispPlacedSpec M A lim ctl S SendEnv with
    pre := fun (x, stB) s =>
      ⌜x.st.bytes.length < 2 ^ 32 ∧ 64 ≤ x.rest.length⌝ ∗
        tokenInitPlacedAt ∗
        (spqrSendCoinsDispPlacedSpec M A lim ctl S SendEnv).pre (x, stB) s
    post := fun (x, stB) s0 sf =>
      tokenInitPlacedAt ∗
        (spqrSendCoinsDispPlacedSpec M A lim ctl S SendEnv).post (x, stB) s0 sf }

/-- Default budget-threaded `[LibsignalPlacement]` `spqrSendCoinsPlacedSpecT` at `SpqrSendCoinsEnv`. -/
abbrev spqrSendCoinsPlacedSpecT [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel) :
    Spec (SendCall × M.σ) :=
  spqrSendCoinsPlacedSpecTOfEnv M A lim ctl S SpqrSendCoinsEnv

/-- Explicit `*Disp*` alias for `spqrSendCoinsPlacedSpecTOfEnv` (definitionally equal). -/
abbrev spqrSendCoinsDispPlacedSpecTOfEnv [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    (SendEnv : SendCall → List AllocEvent → Prop) :
    Spec (SendCall × M.σ) :=
  spqrSendCoinsPlacedSpecTOfEnv M A lim ctl S SendEnv

/-- Explicit `*Disp*` alias for `spqrSendCoinsPlacedSpecT` (definitionally equal). -/
abbrev spqrSendCoinsDispPlacedSpecT [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel) :
    Spec (SendCall × M.σ) :=
  spqrSendCoinsPlacedSpecT M A lim ctl S

/-- Non-display-tag counterpart of `spqrSendCoinsPlacedSpecTOfEnv` wrapping
    `CorePlacedBudget.spqrSendCoinsPlacedSpec`. -/
@[expose] def spqrSendCoinsPlainPlacedSpecTOfEnv [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    (SendEnv : SendCall → List AllocEvent → Prop) :
    Spec (SendCall × M.σ) :=
  { spqrSendCoinsPlacedSpec M A lim ctl S SendEnv with
    pre := fun (x, stB) s =>
      ⌜x.st.bytes.length < 2 ^ 32 ∧ 64 ≤ x.rest.length⌝ ∗
        tokenInitPlacedAt ∗
        (spqrSendCoinsPlacedSpec M A lim ctl S SendEnv).pre (x, stB) s
    post := fun (x, stB) s0 sf =>
      tokenInitPlacedAt ∗
        (spqrSendCoinsPlacedSpec M A lim ctl S SendEnv).post (x, stB) s0 sf }

/-- Monotonicity downgrade from `spqrSendCoinsPlacedSpecTOfEnv` to
    `spqrSendCoinsPlainPlacedSpecTOfEnv` under `StoreKit.withLsCodeRoLoaded`. -/
theorem spqrSendCoinsPlacedSpecT_imp_plain [LibsignalPlacement]
    {M : AllocCostModel} {prog : Program} {entry : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64} {S : SpqrModel}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (h : subroutine_ok prog entry
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecTOfEnv M A lim ctl S SendEnv))) :
    subroutine_ok prog entry
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlainPlacedSpecTOfEnv M A lim ctl S SendEnv)) := by
  refine subroutine_ok_mono h
    (fun _ _ _ hpre => hpre)
    (fun (x, stB) _ _ _ hpost => by
      dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
        spqrSendCoinsPlacedSpecTOfEnv, spqrSendCoinsDispPlacedSpec,
        spqrSendCoinsPlainPlacedSpecTOfEnv, spqrSendCoinsPlacedSpec] at hpost ⊢
      refine Satisfies.mono (sepConj_mono_left (sepConj_mono_right
        (Entails.sepExists_mono fun evs => sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (spqrSendResultDispAt_entails_spqrSendResultAt A.repAlloc x.ret
            (S.send x.st.bytes x.rest))))))) hpost)
    (fun _ _ _ _ hpan => hpan)
    (fun _ _ _ _ _ he => he)

/-! ## 3. Three-Seam Hypothesis Bundle (`SpqrV1PlacedSeamsOfEnv` / `SpqrV1PlacedSeams`) -/

/-- Envelope-parametric three-seam hypothesis bundle for the SPQR-V1 entry blocks
    (`327`, `329`, `427`) on the placed CLI hook map
    `cliGhostExterns gh (cliExternsPlaced mmpl W)` (carrying `SpqrErrorValidTag` on `spqrRecv`
    and `spqrSendCoins` error exits). -/
structure SpqrV1PlacedSeamsOfEnv [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (InitEnv : InitialStateGhost → List AllocEvent → Prop)
    (RecvEnv : VecArg → VecArg → List AllocEvent → Prop)
    (SendEnv : SendCall → List AllocEvent → Prop) : Prop where
  /-- Block `327`: `spqr::initial_state` at `lsmpl.base 327`. -/
  spqrInitialState :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 327 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 327)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrInitialStatePlacedInnerSpecOfEnv M A lim W.C.F InitEnv))
  /-- Block `329`: `spqr::recv` at `lsmpl.base 329` on
  `Slots.trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))`, strengthened with
  `recvResultExactKeyDispAt`. -/
  spqrRecv :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 329
        (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 329)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrRecvPlacedInnerDispSpecXTOfEnv M A lim (spqrV1Recv W.C.F W.Q.K) RecvEnv))
  /-- Block `427`: `spqr::send::<signal_session_ratchet::Coins>` at `lsmpl.base 427`, strengthened
  with `spqrSendResultDispAt`. -/
  spqrSendCoins :
    subroutine_ok
      ((blkPC_427).rebase (blkPl_427).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecTOfEnv M A lim 0#64 (pqxdhSpqrModel ⟨W.C, W.Q⟩) SendEnv))

/-- Default budget-threaded three-seam hypothesis bundle for SPQR-V1 (`Blocks 327, 329, 427`). -/
abbrev SpqrV1PlacedSeams [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) : Prop :=
  SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W (InitialStateEnv W.C.F) SpqrRecvEnv SpqrSendCoinsEnv

/-! ## 4. Cross-Block Transfer & Downstream Consumer Bridges -/

/-- Non-display-tag Block-`329` projection of `SpqrV1PlacedSeamsOfEnv.spqrRecv`. -/
theorem SpqrV1PlacedSeamsOfEnv.spqrRecv_plain [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {RecvEnv : VecArg → VecArg → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (hS : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitEnv RecvEnv SendEnv) :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 329
        (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 329)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrRecvPlacedInnerSpecXTOfEnv M A lim (spqrV1Recv W.C.F W.Q.K) RecvEnv)) :=
  spqrRecvPlacedInnerDispSpecXT_imp_innerSpecXT hS.spqrRecv

/-- Non-display-tag Block-`427` projection of `SpqrV1PlacedSeamsOfEnv.spqrSendCoins`. -/
theorem SpqrV1PlacedSeamsOfEnv.spqrSendCoins_plain [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {RecvEnv : VecArg → VecArg → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (hS : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitEnv RecvEnv SendEnv) :
    subroutine_ok
      ((blkPC_427).rebase (blkPl_427).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlainPlacedSpecTOfEnv M A lim 0#64 (pqxdhSpqrModel ⟨W.C, W.Q⟩) SendEnv)) :=
  spqrSendCoinsPlacedSpecT_imp_plain hS.spqrSendCoins

/-- Transfer `SpqrV1PlacedSeamsOfEnv.spqrInitialState` to any caller block `i < 619`. -/
theorem SpqrV1PlacedSeamsOfEnv.spqrInitialState_at_block [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {RecvEnv : VecArg → VecArg → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (hS : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitEnv RecvEnv SendEnv)
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 327)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrInitialStatePlacedInnerSpecOfEnv M A lim W.C.F InitEnv)) :=
  subroutine_ok_withLsCodeRoLoaded_of_rocl
    (ls_subroutine_ok_rocl_of_block (callerProg := callerProg)
      hS.spqrInitialState hi (by decide) (by decide))

/-- Instantiate `BobTailV1PlacedBudget.InitialStateMemInvPlacedOkOfEnv` on Block `75` (`lsProg_75`). -/
theorem SpqrV1PlacedSeamsOfEnv.initialStateMemInv_lsProg75 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {RecvEnv : VecArg → VecArg → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (hS : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitEnv RecvEnv SendEnv) :
    InitialStateMemInvPlacedOkOfEnv M
      (CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
      A lim W.C.F InitEnv (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  hS.spqrInitialState_at_block
    (callerProg := lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 75) (by decide)

/-- Instantiate `StepSpqrPlacedBudget.spqrInitialStateInnerSpec` on Block `521` (`lsProg_521`)
    for any `Params`-indexed envelope `InitStateEnv`. -/
theorem SpqrV1PlacedSeamsOfEnv.spqrInitialState_initProg_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {RecvEnv : VecArg → VecArg → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (hS : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W (fun x => InitStateEnv x.p) RecvEnv SendEnv) :
    subroutine_ok (lsProg_521 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 327)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrInitialStateInnerSpec A lim InitStateEnv W.C.F)) :=
  hS.spqrInitialState_at_block
    (callerProg := lsProg_521 (cliGhostExterns gh (cliExternsPlaced mmpl W)))

/-- Default `InitialStateParamsEnv W.C.F` instantiation of `spqrInitialStateInnerSpec` on
    Block `521` (`lsProg_521`). -/
theorem SpqrV1PlacedSeams.spqrInitialState_initProg [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hS : SpqrV1PlacedSeams M A lim mmpl gh W) :
    subroutine_ok (lsProg_521 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 327)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrInitialStateInnerSpec A lim (InitialStateParamsEnv W.C.F) W.C.F)) :=
  SpqrV1PlacedSeamsOfEnv.spqrInitialState_initProg_ofEnv hS

/-- Transfer display-tag-strengthened `SpqrV1PlacedSeamsOfEnv.spqrRecv` to any caller block
    `i < 619` on `Slots.trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))`. -/
theorem SpqrV1PlacedSeamsOfEnv.spqrRecvDisp_trTrap_at_block [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {RecvEnv : VecArg → VecArg → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (hS : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitEnv RecvEnv SendEnv)
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i
      (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 329)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrRecvPlacedInnerDispSpecXTOfEnv M A lim (spqrV1Recv W.C.F W.Q.K) RecvEnv)) :=
  subroutine_ok_withLsCodeRoLoaded_of_rocl
    (ls_subroutine_ok_rocl_of_block (callerProg := callerProg)
      hS.spqrRecv hi (by decide) (by decide))

/-- Transfer display-tag-strengthened `SpqrV1PlacedSeamsOfEnv.spqrRecv` to any caller block
    `i < 619` on `cliGhostExterns gh (cliExternsPlaced mmpl W)`. -/
theorem SpqrV1PlacedSeamsOfEnv.spqrRecvDisp_at_block [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {RecvEnv : VecArg → VecArg → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (hS : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitEnv RecvEnv SendEnv)
    {callerProg : Program} {i : Nat}
    [hcaller : IsLsBlockProg callerProg i (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 329)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrRecvPlacedInnerDispSpecXTOfEnv M A lim (spqrV1Recv W.C.F W.Q.K) RecvEnv)) := by
  have : IsLsBlockProg
      (libsignalSessionLib.blockProgram lsmpl i
        (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      i (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) :=
    ⟨rfl, hcaller.externs_eq⟩
  have htr := hS.spqrRecvDisp_trTrap_at_block
    (callerProg := libsignalSessionLib.blockProgram lsmpl i
      (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))) hi
  rw [hcaller.eq_blockProgram]
  exact subroutine_ok_cliPlaced_of_trTrap
    (pc := (libsignalSessionLib.blockLib i).program (libsignalSessionLib.blockPlacement lsmpl i))
    (b := (libsignalSessionLib.blockPlacement lsmpl i).base) htr

/-- Transfer non-display-tag `SpqrV1PlacedSeamsOfEnv.spqrRecv_plain` to any caller block `i < 619`
    on `Slots.trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))`. -/
theorem SpqrV1PlacedSeamsOfEnv.spqrRecv_trTrap_at_block [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {RecvEnv : VecArg → VecArg → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (hS : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitEnv RecvEnv SendEnv)
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i
      (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 329)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrRecvPlacedInnerSpecXTOfEnv M A lim (spqrV1Recv W.C.F W.Q.K) RecvEnv)) :=
  spqrRecvPlacedInnerDispSpecXT_imp_innerSpecXT (hS.spqrRecvDisp_trTrap_at_block hi)

/-- Transfer non-display-tag `SpqrV1PlacedSeamsOfEnv.spqrRecv_plain` to any caller block `i < 619`
    on `cliGhostExterns gh (cliExternsPlaced mmpl W)`. -/
theorem SpqrV1PlacedSeamsOfEnv.spqrRecv_at_block [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {RecvEnv : VecArg → VecArg → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (hS : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitEnv RecvEnv SendEnv)
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 329)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrRecvPlacedInnerSpecXTOfEnv M A lim (spqrV1Recv W.C.F W.Q.K) RecvEnv)) :=
  spqrRecvPlacedInnerDispSpecXT_imp_innerSpecXT (hS.spqrRecvDisp_at_block hi)

/-- Budget-threaded relocatable `spqrRecvRawSpecPlaced` (`PqRecvBudgetDefs`) with
    `tokenInitPlacedAt` framed and DEV-SPQR3 / DEV-SPQR4 preconditions
    (`st.bytes.length < 2 ^ 32`, `msg.bytes.length < 2 ^ 40`, `spqrRecvStack ≤ s.sp.toNat`),
    mirroring `SpqrRecvTrapV1Placed.spqrRecvRawSpecT`. -/
@[expose] def spqrRecvRawSpecPlacedT [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (S : SpqrModel)
    (RecvEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop) :
    Spec ((VecArg × VecArg × BitVec 64) × M.σ) :=
  { spqrRecvRawSpecPlaced A lim S RecvEnv with
    pre := fun (x, stB) s =>
      ⌜x.1.bytes.length < 2 ^ 32 ∧ x.2.1.bytes.length < 2 ^ 40 ∧ spqrRecvStack ≤ s.sp.toNat⌝ ∗
        tokenInitPlacedAt ∗ (spqrRecvRawSpecPlaced A lim S RecvEnv).pre (x, stB) s
    post := fun (x, stB) s0 sf =>
      tokenInitPlacedAt ∗ (spqrRecvRawSpecPlaced A lim S RecvEnv).post (x, stB) s0 sf }

/-- Display-tag-strengthened (`spqrRecvResultDispAt`) counterpart of `spqrRecvRawSpecPlacedT`
    (`PqRecvBudgetDefs.spqrRecvRawDispSpecPlaced` with `tokenInitPlacedAt` and input/stack bounds
    framed). -/
@[expose] def spqrRecvRawDispSpecPlacedT [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (S : SpqrModel)
    (RecvEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop) :
    Spec ((VecArg × VecArg × BitVec 64) × M.σ) :=
  { spqrRecvRawDispSpecPlaced A lim S RecvEnv with
    pre := fun (x, stB) s =>
      ⌜x.1.bytes.length < 2 ^ 32 ∧ x.2.1.bytes.length < 2 ^ 40 ∧ spqrRecvStack ≤ s.sp.toNat⌝ ∗
        tokenInitPlacedAt ∗ (spqrRecvRawDispSpecPlaced A lim S RecvEnv).pre (x, stB) s
    post := fun (x, stB) s0 sf =>
      tokenInitPlacedAt ∗ (spqrRecvRawDispSpecPlaced A lim S RecvEnv).post (x, stB) s0 sf }

/-- Bridge `StoreKit.withLsCodeRoLoaded lsmpl (spqrRecvPlacedInnerSpecXTOfEnv ...)` to
    `LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (spqrRecvRawSpecPlacedT ...)`,
    mirroring `SpqrRecvTrapV1Placed.spqrRecvPlacedInnerSpecXT_imp_spqrRecvRawSpecT`. -/
theorem spqrRecvPlacedInnerSpecXT_imp_spqrRecvRawSpecPlacedT [LibsignalPlacement]
    {M : AllocCostModel} {prog : Program} {entry : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress} {K : MlKem}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    (h : subroutine_ok prog entry
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrRecvPlacedInnerSpecXTOfEnv M A lim (spqrV1Recv F K)
          (fun st msg => RecvBytesEnv st.bytes msg.bytes)))) :
    subroutine_ok prog entry
      (CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (spqrRecvRawSpecPlacedT A lim (spqrV1 F K) RecvBytesEnv)) := by
  have heq_pan :
      (spqrV1Recv F K).recvPanics = fun st msg => (spqrV1 F K).recvPanics st msg = true := by
    rw [spqrV1Recv_eq, spqrV1_eq]; rfl
  refine subroutine_ok_mono h
    (fun ((st, msg, ret), stB) Fr s0 hpre => by
      dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
        CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded,
        spqrRecvPlacedInnerSpecXTOfEnv, spqrRecvPlacedInnerSpecXOfEnv,
        spqrRecvRawSpecPlacedT, spqrRecvRawSpecPlaced, spqrRecvRawSpec,
        RustCliAllocBudget.atState_pool, vecArg_at_atState] at hpre ⊢
      rwa [lsLogOff_eq_logOff_placed])
    (fun ((st, msg, ret), stB) Fr s0 sf hpost => by
      dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
        CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded,
        spqrRecvPlacedInnerSpecXTOfEnv, spqrRecvPlacedInnerSpecXOfEnv,
        spqrRecvRawSpecPlacedT, spqrRecvRawSpecPlaced, spqrRecvRawSpec,
        RustCliAllocBudget.atState_pool, vecArg_at_atState,
        spqrRecvResultAt_atState] at hpost ⊢
      rw [heq_pan, lsLogOff_eq_logOff_placed] at hpost
      refine Satisfies.mono (sepConj_mono_left (sepConj_mono_right
        (Entails.sepExists_mono fun evs => sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
            (recvResultAtX_entails_recvResultAt A.repAlloc ret F K
              st.bytes msg.bytes)))))))) hpost)
    (fun ((st, msg, ret), stB) Fr s0 sf hpan => by
      dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
        CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded,
        spqrRecvPlacedInnerSpecXTOfEnv, spqrRecvPlacedInnerSpecXOfEnv,
        spqrRecvRawSpecPlacedT, spqrRecvRawSpecPlaced] at hpan ⊢
      rwa [heq_pan] at hpan)
    (fun _ _ _ _ _ he => he)

/-- Bridge `StoreKit.withLsCodeRoLoaded lsmpl (spqrRecvPlacedInnerDispSpecXTOfEnv ...)` to
    `LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (spqrRecvRawDispSpecPlacedT ...)` via
    `ErrorDisplayTag.recvResultExactKeyDispAt_entails_spqrRecvResultDispAt`. -/
theorem spqrRecvPlacedInnerDispSpecXT_imp_spqrRecvRawDispSpecPlacedT [LibsignalPlacement]
    {M : AllocCostModel} {prog : Program} {entry : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress} {K : MlKem}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    (h : subroutine_ok prog entry
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrRecvPlacedInnerDispSpecXTOfEnv M A lim (spqrV1Recv F K)
          (fun st msg => RecvBytesEnv st.bytes msg.bytes)))) :
    subroutine_ok prog entry
      (CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (spqrRecvRawDispSpecPlacedT A lim (spqrV1 F K) RecvBytesEnv)) := by
  have heq_pan :
      (spqrV1Recv F K).recvPanics = fun st msg => (spqrV1 F K).recvPanics st msg = true := by
    rw [spqrV1Recv_eq, spqrV1_eq]; rfl
  refine subroutine_ok_mono h
    (fun ((st, msg, ret), stB) Fr s0 hpre => by
      dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
        CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded,
        spqrRecvPlacedInnerDispSpecXTOfEnv, spqrRecvPlacedInnerDispSpecXOfEnv,
        spqrRecvPlacedInnerSpecXOfEnv, spqrRecvRawDispSpecPlacedT, spqrRecvRawDispSpecPlaced,
        spqrRecvRawDispSpec, spqrRecvRawSpec,
        RustCliAllocBudget.atState_pool, vecArg_at_atState] at hpre ⊢
      rwa [lsLogOff_eq_logOff_placed])
    (fun ((st, msg, ret), stB) Fr s0 sf hpost => by
      dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
        CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded,
        spqrRecvPlacedInnerDispSpecXTOfEnv, spqrRecvPlacedInnerDispSpecXOfEnv,
        spqrRecvRawDispSpecPlacedT, spqrRecvRawDispSpecPlaced, spqrRecvRawDispSpec,
        RustCliAllocBudget.atState_pool, vecArg_at_atState,
        spqrRecvResultDispAt_atState] at hpost ⊢
      rw [heq_pan, lsLogOff_eq_logOff_placed] at hpost
      refine Satisfies.mono (sepConj_mono_left (sepConj_mono_right
        (Entails.sepExists_mono fun evs => sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
            (recvResultExactKeyDispAt_entails_spqrRecvResultDispAt A.repAlloc ret F K
              st.bytes msg.bytes)))))))) hpost)
    (fun ((st, msg, ret), stB) Fr s0 sf hpan => by
      dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
        CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded,
        spqrRecvPlacedInnerDispSpecXTOfEnv, spqrRecvPlacedInnerDispSpecXOfEnv,
        spqrRecvPlacedInnerSpecXOfEnv, spqrRecvRawDispSpecPlacedT, spqrRecvRawDispSpecPlaced] at hpan ⊢
      rwa [heq_pan] at hpan)
    (fun _ _ _ _ _ he => he)

/-- Monotonicity downgrade from `spqrRecvRawDispSpecPlacedT` to `spqrRecvRawSpecPlacedT` under
    `LibsignalTripleRatchet.withLsCodeRoLoaded`. -/
theorem spqrRecvRawDispSpecPlacedT_imp_rawSpecPlacedT [LibsignalPlacement]
    {M : AllocCostModel} {prog : Program} {entry : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {S : SpqrModel}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    (h : subroutine_ok prog entry
      (CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (spqrRecvRawDispSpecPlacedT A lim S RecvBytesEnv))) :
    subroutine_ok prog entry
      (CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (spqrRecvRawSpecPlacedT A lim S RecvBytesEnv)) := by
  refine subroutine_ok_mono h
    (fun _ _ _ hpre => hpre)
    (fun ((st, msg, ret), stB) _ _ _ hpost => by
      dsimp only [CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded,
        spqrRecvRawDispSpecPlacedT, spqrRecvRawDispSpecPlaced, spqrRecvRawDispSpec,
        spqrRecvRawSpecPlacedT, spqrRecvRawSpecPlaced, spqrRecvRawSpec,
        spqrRecvResultDispAt_atState, spqrRecvResultAt_atState] at hpost ⊢
      refine Satisfies.mono (sepConj_mono_left (sepConj_mono_right
        (Entails.sepExists_mono fun evs => sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
            (spqrRecvResultDispAt_entails_spqrRecvResultAt A.repAlloc ret
              (S.recv st.bytes msg.bytes))))))))) hpost)
    (fun _ _ _ _ hpan => hpan)
    (fun _ _ _ _ _ he => he)

/-- Bridge `SpqrV1PlacedSeamsOfEnv.spqrRecv` at any `cliGhostExterns gh (cliExternsPlaced mmpl W)`
    caller block `i < 619` directly to `spqrRecvRawDispSpecPlacedT`. -/
theorem SpqrV1PlacedSeamsOfEnv.spqrRecv_rawDispSpecPlacedT_at_block [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (hS : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitEnv
      (fun st msg => RecvBytesEnv st.bytes msg.bytes) SendEnv)
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 329)
      (CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (spqrRecvRawDispSpecPlacedT A lim (spqrV1 W.C.F W.Q.K) RecvBytesEnv)) :=
  spqrRecvPlacedInnerDispSpecXT_imp_spqrRecvRawDispSpecPlacedT (hS.spqrRecvDisp_at_block hi)

/-- Bridge `SpqrV1PlacedSeamsOfEnv.spqrRecv` at any `cliGhostExterns gh (cliExternsPlaced mmpl W)`
    caller block `i < 619` directly to `spqrRecvRawSpecPlacedT`. -/
theorem SpqrV1PlacedSeamsOfEnv.spqrRecv_rawSpecPlacedT_at_block [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (hS : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitEnv
      (fun st msg => RecvBytesEnv st.bytes msg.bytes) SendEnv)
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 329)
      (CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (spqrRecvRawSpecPlacedT A lim (spqrV1 W.C.F W.Q.K) RecvBytesEnv)) :=
  spqrRecvPlacedInnerSpecXT_imp_spqrRecvRawSpecPlacedT (hS.spqrRecv_at_block hi)

/-- Transfer `SpqrV1PlacedSeamsOfEnv.spqrSendCoins` to Block `428` (`otrEncryptV1_coins_placed_ok`). -/
theorem SpqrV1PlacedSeamsOfEnv.spqrSendCoins_at_428 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {RecvEnv : VecArg → VecArg → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (hS : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitEnv RecvEnv SendEnv) :
    subroutine_ok
      ((blkPC_428).rebase (blkPl_428).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecTOfEnv M A lim 0#64 (pqxdhSpqrModel ⟨W.C, W.Q⟩) SendEnv)) := by
  have : IsLsBlockProg
      ((blkPC_427).rebase (blkPl_427).base (cliGhostExterns gh (cliExternsPlaced mmpl W))) 427
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    instIsLsBlockProg_427 (cliGhostExterns gh (cliExternsPlaced mmpl W))
  exact subroutine_ok_withLsCodeRoLoaded_of_rocl
    (ls_subroutine_ok_rocl_of_block
      (callerProg := (blkPC_428).rebase (blkPl_428).base
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      hS.spqrSendCoins (by decide) (by decide) (by decide))

/-- Explicit `*Disp*` alias for `SpqrV1PlacedSeamsOfEnv.spqrSendCoins_at_428`. -/
abbrev SpqrV1PlacedSeamsOfEnv.spqrSendCoinsDisp_at_428 :=
  @SpqrV1PlacedSeamsOfEnv.spqrSendCoins_at_428

/-- Transfer non-display-tag `SpqrV1PlacedSeamsOfEnv.spqrSendCoins_plain` to Block `428`. -/
theorem SpqrV1PlacedSeamsOfEnv.spqrSendCoinsPlain_at_428 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {RecvEnv : VecArg → VecArg → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (hS : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitEnv RecvEnv SendEnv) :
    subroutine_ok
      ((blkPC_428).rebase (blkPl_428).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlainPlacedSpecTOfEnv M A lim 0#64 (pqxdhSpqrModel ⟨W.C, W.Q⟩) SendEnv)) := by
  have : IsLsBlockProg
      ((blkPC_427).rebase (blkPl_427).base (cliGhostExterns gh (cliExternsPlaced mmpl W))) 427
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    instIsLsBlockProg_427 (cliGhostExterns gh (cliExternsPlaced mmpl W))
  exact subroutine_ok_withLsCodeRoLoaded_of_rocl
    (ls_subroutine_ok_rocl_of_block
      (callerProg := (blkPC_428).rebase (blkPl_428).base
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      hS.spqrSendCoins_plain (by decide) (by decide) (by decide))

end LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget
