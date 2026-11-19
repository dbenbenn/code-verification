/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.DepsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.KemDeserializePlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KemDeserializeSlotPlacedBudget
import Arm64.Trusted.Spec.Hoare
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.GenLsBlockUltra
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.Placed.GenLsBlockFast

/-!
# File-Descriptor-Threaded `kem::Key<Public>::deserialize` Slot Adapter (Placed)

Lifts `cliKemDeserialize_placed_at_block` across `AllocWithFds.withFds` when `lim.enforced = true`,
discharging `withFdsGe3Closed` for Block `590` (`kem::Key<Public>::deserialize`) on `lsProg_579 H`
both for `slotsOfPlaced` and `slotsOfSigPkFrozenPlaced`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KemDeserializeSlotPlacedBudgetFd

open Arm64 ProofLib SepProp
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement ls_hook_ok_ultra_of_mem lsmpl)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (extract_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_plain withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet (extHookStack memcpyName)
open CryptoVerification.SignalSession.Cli.Main.Placed (instIsLsBlockProg_617)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_590)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose (RunNeeds RunSem)
open CryptoVerification.SpqrV1.Alloc (sessionMemcpyRegionROSpec)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget (CodecHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed extract_withFdsGe3Closed withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
  (hookOk_allocBudget_withFds hookOk_deallocBudget_withFds hookOk_reallocBudget_withFds
   withFds withFds_pool_enforced withFds_repAlloc)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget
  (hookOk_rustAllocWithStack hookOk_rustDeallocExternWithStack hookOk_rustReallocExternWithStack)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs slotsOfPlaced slotsOfSigPkFrozenPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.KemDeserialize.SpecBudget
  (cliKemDeserializeSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.KemDeserializePlacedBudget
  (cliKemDeserializeSpecPlaced cliKemDeserialize_placed_at_block)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd (slotWithFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsXCliPlaced)

theorem subroutine_ok_of_pre_post {α : Type} {P : Program} {entry : BitVec 64}
    {spec1 spec2 : Spec α} {Q : α → State → Prop}
    (hok : subroutine_ok P entry spec1)
    (hpan : spec2.onPanic = spec1.onPanic)
    (hexc : spec2.onExit = spec1.onExit)
    (hoom : spec2.onOom = spec1.onOom)
    (hpre : ∀ x R s0, (s0.mem ⊨ spec2.pre x s0 ∗ R) → Q x s0 ∧ (s0.mem ⊨ spec1.pre x s0 ∗ R))
    (hpost : ∀ x R s0 sf, Q x s0 → (sf.mem ⊨ spec1.post x s0 sf ∗ R) →
      (sf.mem ⊨ spec2.post x s0 sf ∗ R)) :
    subroutine_ok P entry spec2 := by
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre2 hsp _
  obtain ⟨hq, hpre1⟩ := hpre x R s0 hpre2
  refine subroutine_ok.mono_outcome hok x R s0 hpc hrun hpre1 hsp ?_
  rintro sf (⟨hret, hcc, hp1⟩ | ⟨hp, hpan1⟩ | ⟨c, hc, hexc1⟩ | ⟨ho, hoom1⟩)
  · exact Or.inl ⟨hret, hcc, hpost x R s0 sf hq hp1⟩
  · exact Or.inr (Or.inl ⟨hp, hpan ▸ hpan1⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hexc ▸ hexc1⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom ▸ hoom1⟩))

theorem codecHooksPlaced_withFds [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h : CodecHooksPlaced M A lim H) :
    CodecHooksPlaced M (withFds A) lim H where
  shim := h.shim
  alloc := let ⟨f, hf, hok⟩ := h.alloc; ⟨f, hf, hookOk_allocBudget_withFds hok⟩
  realloc := let ⟨f, hf, hok⟩ := h.realloc; ⟨f, hf, hookOk_reallocBudget_withFds hok⟩
  dealloc := let ⟨f, hf, hok⟩ := h.dealloc; ⟨f, hf, hookOk_deallocBudget_withFds hok⟩
  memcpy := h.memcpy
  panic_alloc := h.panic_alloc
  panic_raw := h.panic_raw

/-- Lifts `AllocContractsXCliPlaced` from `A` to `withFds A` via `RunHooksPlaced A lim H`. -/
theorem allocContractsXCliPlaced_withFds_of_runHooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hh : RunHooksPlaced A lim H) :
    AllocContractsXCliPlaced (withFds A) lim H := by
  have hc := codecHooksPlaced_withFds hh.codecHooks
  rcases hc.alloc with ⟨fa, hfa, hoka⟩
  rcases hc.dealloc with ⟨fd, hfd, hokd⟩
  rcases hc.realloc with ⟨fr, hfr, hokr⟩
  exact
    { hh.alloc with
      alloc := subroutine_ok_withLsCodeRoLoaded_of_plain
        (ls_hook_ok_ultra_of_mem
          ⟨fa, hfa, hookOk_rustAllocWithStack hoka (by decide) (by decide)⟩ (by decide))
      dealloc := subroutine_ok_withLsCodeRoLoaded_of_plain
        (ls_hook_ok_ultra_of_mem
          ⟨fd, hfd, hookOk_rustDeallocExternWithStack hokd (by decide) (by decide)⟩ (by decide))
      realloc := subroutine_ok_withLsCodeRoLoaded_of_plain
        (ls_hook_ok_ultra_of_mem
          ⟨fr, hfr, hookOk_rustReallocExternWithStack hokr (by decide) (by decide)⟩ (by decide)) }

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KemDeserializeSlotPlacedBudgetFd
