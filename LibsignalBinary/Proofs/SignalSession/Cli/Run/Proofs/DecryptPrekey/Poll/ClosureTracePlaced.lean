/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePanicPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
public import LibsignalBinary.Proofs.E2E.HooksE.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Placed.Bridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Kits -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Layout -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Sem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Spec
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.SpecState -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlot -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlaced -- proof-setup: allow-public-import
public import Arm64.Trusted.Object.Labels
public import ProofLib.BV
public import ProofLib.Disproof.Basic
public import ProofLib.MallocngBridge
public import ProofLib.Placed
public import ProofLib.Placed.LabelsCheck
public import ProofLib.Placed.LabelsCoverage
public import ProofLib.Placed.LabelsInterned
public import ProofLib.Placed.SharedCode
public import ProofLib.Process.FsLemmas
public import ProofLib.SepLogic.LoopTactics
public import ProofLib.SepLogic.WP.SyscallsMmap
public import ProofLib.StdStartup.MuslStage1Init
public import ProofLib.StdStartup.OutlineAtomics
public import ProofLib.StdStartup.Strlen
public import VerifiedLibraries.Musl.Spec
public import VerifiedLibraries.Musl.Spec.Top
public import VerifiedLibraries.RustStd.Spec
public import VerifiedLibraries.RustStd.Spec.AllocFormatInner
public import VerifiedLibraries.RustStd.Spec.AllocFormatInnerBudget
public import VerifiedLibraries.RustStd.Spec.AllocStringClone
public import VerifiedLibraries.RustStd.Spec.CoreFmtDisplay
public import VerifiedLibraries.RustStd.Spec.CoreFmtWrite
public import VerifiedLibraries.RustStd.Spec.CoreFromUtf8
public import VerifiedLibraries.RustStd.Spec.CoreMemrchr
public import VerifiedLibraries.RustStd.Spec.FsRead
public import VerifiedLibraries.RustStd.Spec.FsWrite
public import VerifiedLibraries.RustStd.Spec.Stdio
public import VerifiedLibraries.RustStd.Spec.TimeAdd
public import VerifiedLibraries.RustStd.Spec.TimeDurationSince
import LibsignalBinary.Proofs.SignalSession.Cli.CliSessionCodeSymA
import LibsignalBinary.Proofs.SignalSession.Cli.CliSessionCodeSymB
import LibsignalBinary.Proofs.SignalSession.Cli.CliSessionCodeSymC
import LibsignalBinary.Proofs.SignalSession.Cli.CliSessionCodeSymD
import LibsignalBinary.Proofs.SignalSession.Cli.CliSessionCodeSymE
public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocMetaFullProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocMetaFullStage2
public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocSlotProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocSlotStage2
public import VerifiedLibraries.Mallocng.Proofs.PlacedCallocProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedLibcFreeStage1
public import VerifiedLibraries.Mallocng.Proofs.PlacedMallocEntryProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedPosixMemalignProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedReallocProof
public import VerifiedLibraries.Mallocng.Proofs.RdlAllocProof
public import VerifiedLibraries.Mallocng.Proofs.SyscallWrappersProof
public import VerifiedLibraries.Musl.Proofs.CryptoHooks
public import VerifiedLibraries.Musl.Proofs.MemmoveProof
public import VerifiedLibraries.Musl.Proofs.MemsetProof
public import VerifiedLibraries.RustStd.Proofs.MallocngBridgeCommon

/-!
# Relocatable `[LibsignalPlacement]` Generalized Trace and Exit Postcondition Packagers

Proves `dpPollPost_of_slotTraceFT_placed` packaging closure exit states from `slotTraceFT` and
`slotOutTr` under `[LibsignalPlacement]`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.E2E
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs

private theorem pure_sepConj_intro_placed {φ : Prop} {P Q : SepProp} (hφ : φ) (h : P ⊢ Q) :
    P ⊢ ⌜φ⌝ ∗ Q := by
  have hEq : φ = True := propext ⟨fun _ => trivial, fun _ => hφ⟩
  rw [hEq, pure_true, emp_sepConj]
  exact h

/-- Packages `decResAt`, `storesAt`, preserved caller borrows, `dpFutDoneAt`, `memRegion cx 32`,
`stackAt s0.sp stk'`, and any leftover heap `Leftover` into `dpPollSpecState.post` at
`dpSlotPollKStatePlaced E2E.HooksE.A0 B S` from `slotTraceFT` and `slotOutTr`. -/
theorem dpPollPost_of_slotTraceFT_placed [LibsignalPlacement] (B : RunBudgets) (S : RunSem)
    (stk' : Nat)
    (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S))
    (s0 sf : State)
    (g' : StoresGhost) (e : Except (ApiError AddrVal Unit) E2E.Bytes)
    (Leftover : SepProp)
    (hft : slotTraceFT s0.fs s0.trace sf.fs sf.trace)
    (hout : slotOutTr (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
      g' e s0.trace sf.trace) :
    decResAt E2E.HooksE.A0 y.out e ∗
      storesAt E2E.HooksE.A0 y.g.stores g' ∗
      protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
      protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
      preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
      FromRecordCallees.lsLogOff ∗
      E2E.HooksE.A0.pool ∗
      Leftover ∗
      dpFutDoneAt y.fut ∗
      memRegion y.cx 32 ∗
      stackAt s0.sp stk' ⊢
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (dpPollSpecState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S) stk')).post y s0 sf := by
  have hdec := decResAt_entails_dpWords_resHeap E2E.HooksE.A0 y.out e
  have hany : Leftover ⊢ anyHeap := entails_anyHeap Leftover
  refine Entails.trans (sepConj_mono hdec
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hany)))))))) ?_
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun ws => ?_
  let K := dpSlotPollKStatePlaced E2E.HooksE.A0 B S
  change (⌜ws.length = 6 ∧ ws.head? ≠ some pendingTag⌝ ∗
      dpWordsAt y.out ws ∗ dpResHeap E2E.HooksE.A0 ws e) ∗
      storesAt E2E.HooksE.A0 y.g.stores g' ∗
      protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
      protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
      preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
      FromRecordCallees.lsLogOff ∗ E2E.HooksE.A0.pool ∗ anyHeap ∗
      dpFutDoneAt y.fut ∗ memRegion y.cx 32 ∗ stackAt s0.sp stk' ⊢
    (∃∗ ws', ⌜ws'.length = 6 ∧ ws'.head? ≠ some pendingTag⌝ ∗
      dpWordsAt y.out ws' ∗ K.res y.g s0.fs s0.trace sf.fs sf.trace ws') ∗
      dpFutDoneAt y.fut ∗ memRegion y.cx 32 ∗ stackAt s0.sp stk'
  have hreord :
      (⌜ws.length = 6 ∧ ws.head? ≠ some pendingTag⌝ ∗
        dpWordsAt y.out ws ∗ dpResHeap E2E.HooksE.A0 ws e) ∗
      storesAt E2E.HooksE.A0 y.g.stores g' ∗
      protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
      protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
      preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
      FromRecordCallees.lsLogOff ∗ E2E.HooksE.A0.pool ∗ anyHeap ∗
      dpFutDoneAt y.fut ∗ memRegion y.cx 32 ∗ stackAt s0.sp stk' =
      (⌜ws.length = 6 ∧ ws.head? ≠ some pendingTag⌝ ∗
        dpWordsAt y.out ws ∗
        (storesAt E2E.HooksE.A0 y.g.stores g' ∗ dpResHeap E2E.HooksE.A0 ws e ∗
          protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
          protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
          preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
          FromRecordCallees.lsLogOff ∗ E2E.HooksE.A0.pool ∗ anyHeap)) ∗
      (dpFutDoneAt y.fut ∗ memRegion y.cx 32 ∗ stackAt s0.sp stk') := by
    ac_rfl
  rw [hreord]
  refine sepConj_mono_left (Entails.sepExists_right ws ?_)
  refine sepConj_mono_right (sepConj_mono_right ?_)
  dsimp only [K, dpSlotPollKStatePlaced]
  exact Entails.sepExists_right g'
    (Entails.sepExists_right e (pure_sepConj_intro_placed ⟨hft, hout⟩ (Entails.refl _)))

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
