/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePanic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureDefsPlaced
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4Defs
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3Stmt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.SpecState -- proof-setup: allow-public-import
public import Arm64.Trusted.Object.Labels
public import ProofLib.BV
public import ProofLib.Disproof.Basic
public import ProofLib.Hoare.MultiCodeROHook
public import ProofLib.MallocngBridge
public import ProofLib.Placed
public import ProofLib.Placed.LabelsCheck
public import ProofLib.Placed.LabelsCoverage
public import ProofLib.Placed.LabelsInterned
public import ProofLib.Placed.SharedCode
public import ProofLib.Process.FsLemmas
public import ProofLib.SepLogic.LoopTactics
public import ProofLib.SepLogic.WP.Apply
public import ProofLib.SepLogic.WP.SyscallsMmap
public import ProofLib.StdStartup.MuslStage1Init
public import ProofLib.StdStartup.OutlineAtomics
public import ProofLib.StdStartup.Strlen
public import VerifiedLibraries.Mallocng.Spec
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
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyP3a2
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
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# Relocatable `[LibsignalPlacement]` Poll Panic Postcondition Bridges

Lifts `P3P4.PanicOomProp`, `ResponderClosure.PanicOomProp`, and `GenP3.genP3S5PanicProp` across an
outer spatial frame into `(withLsCodeRoLoaded lsmpl (dpPollSpecState K stk')).onPanic`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 ProofLib
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.E2E
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession
open CryptoVerification.SignalSession.Cli.RunProofs

private theorem anyHeap_sepConj_left_placed (Fr : SepProp) : anyHeap ∗ Fr ⊢ anyHeap :=
  entails_anyHeap (anyHeap ∗ Fr)

/-- Lifts `genP3S5ModelPanicProp` across an outer spatial frame `Fr` into
`(LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecState K stk')).onPanic y s0 sf ∗ R` whenever the pure model
panic implies `K.panics y.g`. -/
theorem dpPollOnPanic_of_modelPanic_placed [LibsignalPlacement] {K : DpPollKState} (stk' : Nat)
    (y : DpPollGhostState K)
    {C : Crypto} {Q : LibsignalSpqrV1.MlKem}
    {rem loc : AddrGhost} {st : SessionState (List (BitVec 8))}
    {msg : SignalMessage} {msgVer : BitVec 32} {rest : List (BitVec 8)}
    {s0 sf : State} {Pf Fr R : SepProp}
    (hmod : genP3S5ModelPanicProp C Q rem loc st msg msgVer rest s0 sf Pf)
    (hpan : st.version = msgVer →
      (genP3S5Model C Q rem loc msg rest st).1 = .error .panic → K.panics y.g)
    (hm : sf.mem ⊨ (Pf ∗ Fr) ∗ R) :
    sf.mem ⊨ (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecState K stk')).onPanic y s0 sf ∗ R := by
  rw [sepConj_assoc] at hm
  have h1 := hmod (Fr ∗ R) hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at h1
  obtain ⟨⟨hver, herr, htr⟩, hrest⟩ := h1
  have hkpan : K.panics y.g := hpan hver herr
  dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, dpPollSpecState]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨htr, Or.inr hkpan⟩, ?_⟩
  rw [← sepConj_assoc] at hrest
  exact Satisfies.mono (sepConj_mono_left (anyHeap_sepConj_left_placed Fr)) hrest

/-- Lifts `P3P4.PanicOomProp s0` across an outer spatial frame `Fr` into
`(LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecState K stk')).onPanic y s0 sf ∗ R`. -/
theorem dpPollOnPanic_of_p3p4Oom_placed [LibsignalPlacement] {K : DpPollKState} (stk' : Nat)
    (y : DpPollGhostState K)
    {s0 sf : State} {Pf Fr R : SepProp}
    (hoom : CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4.PanicOomProp s0 sf Pf)
    (hm : sf.mem ⊨ (Pf ∗ Fr) ∗ R) :
    sf.mem ⊨ (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecState K stk')).onPanic y s0 sf ∗ R := by
  rw [sepConj_assoc] at hm
  have h1 := hoom (Fr ∗ R) hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at h1
  obtain ⟨⟨ha, htr⟩, hrest⟩ := h1
  dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, dpPollSpecState]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨htr, Or.inl ha⟩, ?_⟩
  rw [← sepConj_assoc] at hrest
  exact Satisfies.mono (sepConj_mono_left (anyHeap_sepConj_left_placed Fr)) hrest

/-- Lifts `ResponderClosure.PanicOomProp s0` across an outer spatial frame `Fr` into
`(LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecState K stk')).onPanic y s0 sf ∗ R`. -/
theorem dpPollOnPanic_of_closOom_placed [LibsignalPlacement] {K : DpPollKState} (stk' : Nat)
    (y : DpPollGhostState K)
    {s0 sf : State} {Pf Fr R : SepProp}
    (hoom : CryptoVerification.E2E.Pqxdh.ResponderClosure.PanicOomProp s0 sf Pf)
    (hm : sf.mem ⊨ (Pf ∗ Fr) ∗ R) :
    sf.mem ⊨ (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecState K stk')).onPanic y s0 sf ∗ R :=
  dpPollOnPanic_of_p3p4Oom_placed stk' y hoom hm

/-- Lifts `genP3S5PanicProp` (either `P3P4.PanicOomProp` or `genP3S5ModelPanicProp`) into
`(LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecState K stk')).onPanic y s0 sf ∗ R`. -/
theorem dpPollOnPanic_of_genP3_placed [LibsignalPlacement] {K : DpPollKState} (stk' : Nat)
    (y : DpPollGhostState K)
    {C : Crypto} {Q : LibsignalSpqrV1.MlKem}
    {rem loc : AddrGhost} {st : SessionState (List (BitVec 8))}
    {msg : SignalMessage} {msgVer : BitVec 32} {rest : List (BitVec 8)}
    {s0 sf : State} {Pf Fr R : SepProp}
    (hgen : genP3S5PanicProp C Q rem loc st msg msgVer rest s0 sf Pf)
    (hpan : st.version = msgVer →
      (genP3S5Model C Q rem loc msg rest st).1 = .error .panic → K.panics y.g)
    (hm : sf.mem ⊨ (Pf ∗ Fr) ∗ R) :
    sf.mem ⊨ (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecState K stk')).onPanic y s0 sf ∗ R := by
  rcases hgen with hoom | hmod
  · exact dpPollOnPanic_of_p3p4Oom_placed stk' y hoom hm
  · exact dpPollOnPanic_of_modelPanic_placed stk' y hmod hpan hm

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
