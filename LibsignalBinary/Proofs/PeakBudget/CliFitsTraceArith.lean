/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
public import LibsignalBinary.Proofs.PeakBudget.GroupCreditKit -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
public import LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux -- proof-setup: allow-public-import
public import ProofLib.ProgramReflection.SortedFresh
public import ProofLib.ProgramReflection.Variant.TrapTransfer
public import ProofLib.SepLogic.WP.Apply
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.PeakBudget.SpqrDomainCaps

/-!
# Whole-`main` `FitsTrace` / `FitsEnv` Arithmetic

Closed-form physical RAM and 48-bit virtual-address budget expressions for `fineCostModel`
(both `cumB`-coupled and `GroupCreditKit` decoupled-group formulations), sequential 6-phase
`main` composition (`M1 → M2 → M3 → (FreeOnlyEvs ∨ M4Run → M5 → M6)`), and concrete `1 GiB`
(`2 ^ 30`) RAM and `2 ^ 48` VA bounds under reachable CLI, PQXDH, and SPQR domain caps.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith

open _root_.Arm64 ProofLib
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsTrace FreeOnlyEvs SeqEnv
  rustAllocEvents rustDeallocEvents
)
open LibsignalBinary.Heap.Fine (FineScale FineStepBound fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds (
  FineStepBound_mono fineCostModel_baseFine_eq fineCostModel_largeCost_eq
  fineCostModel_largeMetaCost_eq fineCostModel_smallMaxReq_eq
  fineDynIvsOfCum fineMaxGroupsOfCum fineMaxMetaAreasOfCum fineStepReserveOfCum
)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit (
  HasFineGroupCredit PhaseGroupSpec
  fineDynIvsOfGroups fineDynIvsOfGroups_mono
  fineMaxGroupsOfGroups fineMaxMetaAreasOfGroups
  fineStepReserveOfGroups fineStepReserveOfGroups_mono
  fitsEnv_fineCostModel_of_phaseCredit_groups
  fitsTrace_fineCostModel_of_phaseCredit_groups
)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (
  ConcatEnv ModelHyps PhaseCreditSpec
)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (
  fineCostModel_modelHyps fitsEnv_fineCostModel_of_phaseCredit
  fitsTrace_fineCostModel_of_phaseCredit
)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (
  msgCapBytes sessionCapBytes spqrStateTightCapBytes
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (
  HasFineReallocCredit
)

/-! ## Concrete CLI `BudgetLimits` and Domain Caps -/

/-- `1 GiB` (`1,073,741,824` B) physical RAM cap for the placed CLI binary. -/
@[expose] def cliOneGiB : Nat := 2 ^ 30

/-- Conservative upper bound on ELF static `LOAD` + initial stack/auxv interval count (`64`). -/
@[expose] def cliDefaultStaticCount : Nat := 64

/-- Conservative upper bound on ELF static `LOAD` + initial stack/auxv bytes (`16 MiB`). -/
@[expose] def cliDefaultStaticBytes : Nat := 16 * 1024 * 1024

/-- Default enforced `1 GiB` `BudgetLimits` for placed CLI whole-`main` budget discharge. -/
@[expose] def cliBudgetLimits : BudgetLimits where
  staticCount := cliDefaultStaticCount
  staticBytes := cliDefaultStaticBytes
  physCap := cliOneGiB
  enforced := true

/-- Constant `fineCostModel` root/base credit (`18,686,152` B). -/
@[expose] def cliBaseFine : Nat := 18686152

/-- Constant `fineCostModel` small-allocation threshold (`135,167` B). -/
def cliSmallMaxReq : Nat := 135167

/-- Reachable formatted `ProtocolAddress` / key-id filename cap (`64` B). -/
@[expose] def cliMaxAddrTextBytes : Nat := 64

/-- Reachable CLI store directory path length cap (`64` B; `StoresGhost.opened` uses `≤ 26` B). -/
@[expose] def cliMaxDirPathBytes : Nat := 64

/-- Reachable dirty store entry count per CLI command (`≤ 4` in `init` / `recv_prekey`). -/
@[expose] def cliMaxDirtyEntries : Nat := 4

theorem cliBaseFine_eq : HasFineReallocCredit.baseFine fineCostModel = cliBaseFine :=
  fineCostModel_baseFine_eq

/-! ## Closed-Form RAM and VA Budget Functions -/

/-- Closed-form upper bound on `fineCostModel.footprint b` given `(cumB, peakB)`. -/
@[expose] def cliFootprintBound (cumB peakB : Nat) : Nat :=
  cliBaseFine + cumB + peakB

/-- Physical RAM bound required by `fitsTrace_fineCostModel_of_phaseCredit`. -/
def cliRamNeed (staticBytes cumB peakB maxReq : Nat) : Nat :=
  staticBytes + cliFootprintBound cumB peakB + 2 * fineStepReserveOfCum maxReq 16 cumB

theorem cliFootprintBound_mono {c₁ c₂ p₁ p₂ : Nat} (hc : c₁ ≤ c₂) (hp : p₁ ≤ p₂) :
    cliFootprintBound c₁ p₁ ≤ cliFootprintBound c₂ p₂ := by
  unfold cliFootprintBound
  omega

/-- Physical RAM bound required by `fitsTrace_fineCostModel_of_phaseCredit_groups` when
group creation `(fineGroupsScaled + FineScale - 1) / FineScale` is bounded by `grpB`. -/
@[expose] def cliDecoupledRamNeed (staticBytes cumB peakB maxReq grpB : Nat) : Nat :=
  staticBytes + cliFootprintBound cumB peakB + 2 * fineStepReserveOfGroups maxReq 16 grpB

/-- 48-bit virtual-address bound required by `fitsTrace_fineCostModel_of_phaseCredit_groups`
under decoupled group bound `grpB`. -/
@[expose] def cliDecoupledVaNeed (staticBytes staticCount cumB peakB maxReq grpB : Nat) : Nat :=
  MMAP_MIN_ADDR + staticBytes + cliFootprintBound cumB peakB +
    fineStepReserveOfGroups maxReq 16 grpB +
    (staticCount + fineDynIvsOfGroups grpB + 16) *
      (fineStepReserveOfGroups maxReq 16 grpB + PAGE_SIZE) +
    fineStepReserveOfGroups maxReq 16 grpB

theorem cliDecoupledRamNeed_mono {sb₁ sb₂ c₁ c₂ p₁ p₂ r₁ r₂ g₁ g₂ : Nat}
    (hsb : sb₁ ≤ sb₂) (hc : c₁ ≤ c₂) (hp : p₁ ≤ p₂) (hr : r₁ ≤ r₂) (hg : g₁ ≤ g₂) :
    cliDecoupledRamNeed sb₁ c₁ p₁ r₁ g₁ ≤ cliDecoupledRamNeed sb₂ c₂ p₂ r₂ g₂ := by
  have hfp := cliFootprintBound_mono hc hp
  have hst : fineStepReserveOfGroups r₁ 16 g₁ ≤ fineStepReserveOfGroups r₂ 16 g₂ :=
    fineStepReserveOfGroups_mono hr (Nat.le_refl _) hg
  unfold cliDecoupledRamNeed
  omega

theorem cliDecoupledVaNeed_mono {sb₁ sb₂ sc₁ sc₂ c₁ c₂ p₁ p₂ r₁ r₂ g₁ g₂ : Nat}
    (hsb : sb₁ ≤ sb₂) (hsc : sc₁ ≤ sc₂) (hc : c₁ ≤ c₂) (hp : p₁ ≤ p₂)
    (hr : r₁ ≤ r₂) (hg : g₁ ≤ g₂) :
    cliDecoupledVaNeed sb₁ sc₁ c₁ p₁ r₁ g₁ ≤ cliDecoupledVaNeed sb₂ sc₂ c₂ p₂ r₂ g₂ := by
  have hfp := cliFootprintBound_mono hc hp
  have hst : fineStepReserveOfGroups r₁ 16 g₁ ≤ fineStepReserveOfGroups r₂ 16 g₂ :=
    fineStepReserveOfGroups_mono hr (Nat.le_refl _) hg
  have hdyn := fineDynIvsOfGroups_mono hg
  have hmul :
      (sc₁ + fineDynIvsOfGroups g₁ + 16) * (fineStepReserveOfGroups r₁ 16 g₁ + PAGE_SIZE) ≤
        (sc₂ + fineDynIvsOfGroups g₂ + 16) * (fineStepReserveOfGroups r₂ 16 g₂ + PAGE_SIZE) :=
    Nat.mul_le_mul (by omega) (by omega)
  unfold cliDecoupledVaNeed
  omega

/-- Weakens `(PhaseCreditSpec, PhaseGroupSpec)` bounds to literal caps
`(cumCap, peakCap, reqCap, grpCap)` and discharges `FitsTrace fineCostModel`. -/
theorem fitsTrace_fineCostModel_of_group_literal_bounds
    {lim : BudgetLimits} {Env : List AllocEvent → Prop}
    {cumB liveB peakB maxReq grpS cumCap peakCap reqCap grpCap : Nat}
    (hSpec : PhaseCreditSpec fineCostModel Env cumB liveB peakB maxReq)
    (hGrp : PhaseGroupSpec fineCostModel Env grpS)
    (hcum : cumB ≤ cumCap)
    (hlive : liveB ≤ peakCap)
    (hpeak : peakB ≤ peakCap)
    (hreq : maxReq ≤ reqCap)
    (hgrp : (grpS + FineScale - 1) / FineScale ≤ grpCap)
    (henf : lim.enforced = true)
    (hram : cliDecoupledRamNeed lim.staticBytes cumCap peakCap reqCap grpCap ≤ lim.physCap)
    (hva : cliDecoupledVaNeed lim.staticBytes lim.staticCount cumCap peakCap reqCap grpCap ≤ 2 ^ 48)
    {fullLog : List AllocEvent} (hEnv : Env fullLog) :
    FitsTrace fineCostModel lim (fineStepReserveOfGroups reqCap 16 grpCap) fullLog := by
  have hCapSpec : PhaseCreditSpec fineCostModel Env cumCap peakCap peakCap reqCap :=
    hSpec.mono hcum hlive hpeak hreq
  exact fitsTrace_fineCostModel_of_phaseCredit_groups
    hCapSpec hGrp (Nat.le_refl peakCap) hgrp henf
    (by simpa only [cliDecoupledRamNeed, cliFootprintBound, cliBaseFine] using hram)
    (by simpa only [cliDecoupledVaNeed, cliFootprintBound, cliBaseFine] using hva)
    hEnv

/-- Discharges `FitsEnv fineCostModel` at `fineCostModel.init` from literal credit and group caps. -/
theorem fitsEnv_fineCostModel_of_group_literal_bounds
    {lim : BudgetLimits} {Env : List AllocEvent → Prop}
    {cumB liveB peakB maxReq grpS cumCap peakCap reqCap grpCap : Nat}
    (hSpec : PhaseCreditSpec fineCostModel Env cumB liveB peakB maxReq)
    (hGrp : PhaseGroupSpec fineCostModel Env grpS)
    (hcum : cumB ≤ cumCap)
    (hlive : liveB ≤ peakCap)
    (hpeak : peakB ≤ peakCap)
    (hreq : maxReq ≤ reqCap)
    (hgrp : (grpS + FineScale - 1) / FineScale ≤ grpCap)
    (henf : lim.enforced = true)
    (hram : cliDecoupledRamNeed lim.staticBytes cumCap peakCap reqCap grpCap ≤ lim.physCap)
    (hva : cliDecoupledVaNeed lim.staticBytes lim.staticCount cumCap peakCap reqCap grpCap ≤ 2 ^ 48) :
    FitsEnv fineCostModel lim fineCostModel.init Env := by
  have hCapSpec : PhaseCreditSpec fineCostModel Env cumCap peakCap peakCap reqCap :=
    hSpec.mono hcum hlive hpeak hreq
  exact fitsEnv_fineCostModel_of_phaseCredit_groups
    hCapSpec hGrp (Nat.le_refl peakCap) hgrp henf
    (by simpa only [cliDecoupledRamNeed, cliFootprintBound, cliBaseFine] using hram)
    (by simpa only [cliDecoupledVaNeed, cliFootprintBound, cliBaseFine] using hva)

/-! ## Sequential 6-Phase `main` Composition -/

/-- Whole-`main` 6-phase envelope: setup phases `M1 → M2 → M3` followed either by early-exit
`FreeOnlyEvs` or by `M4Run → M5 → M6`. -/
@[expose] def CliMainSixPhaseEnv
    (M1 M2 M3 M4Run M5 M6 : List AllocEvent → Prop)
    (evs : List AllocEvent) : Prop :=
  SeqEnv (SeqEnv M1 (SeqEnv M2 M3))
    (fun evs' => FreeOnlyEvs evs' ∨ SeqEnv M4Run (SeqEnv M5 M6) evs')
    evs

/-- Per-phase `(Δcum, Δlive, Δpeak, maxReq)` tuple bundle for the 6 sequential phases of `main`. -/
structure CliMainPhaseBounds where
  c1 : Nat
  l1 : Nat
  p1 : Nat
  r1 : Nat
  c2 : Nat
  l2 : Nat
  p2 : Nat
  r2 : Nat
  c3 : Nat
  l3 : Nat
  p3 : Nat
  r3 : Nat
  c4 : Nat
  l4 : Nat
  p4 : Nat
  r4 : Nat
  c5 : Nat
  l5 : Nat
  p5 : Nat
  r5 : Nat
  c6 : Nat
  l6 : Nat
  p6 : Nat
  r6 : Nat

namespace CliMainPhaseBounds

end CliMainPhaseBounds

/-- Per-phase `FineScale`-scaled group delta bundle (`g1..g6`) for the 6 sequential phases of `main`. -/
structure CliMainGroupBounds where
  g1 : Nat
  g2 : Nat
  g3 : Nat
  g4 : Nat
  g5 : Nat
  g6 : Nat

namespace CliMainGroupBounds

end CliMainGroupBounds

/-! ## Concrete `1 GiB` RAM and `2 ^ 48` VA Closure Bounds -/

/-- Physical RAM bound `≤ 1 GiB` under decoupled-group caps
`(760,000,000, 60,000,000, 4,200,000, 50,000)` (`1,036,375,496 ≤ 2 ^ 30`). -/
theorem cliDecoupledRamNeed_le_oneGiB_of_S4 :
    cliDecoupledRamNeed cliDefaultStaticBytes 760000000 60000000 4200000 50000 ≤ cliOneGiB := by
  decide

/-- Virtual-address bound `≤ 2 ^ 48` under decoupled-group caps `(760,000,000, 60,000,000, 4,200,000, 50,000)`. -/
theorem cliDecoupledVaNeed_le_2_48_of_S4 :
    cliDecoupledVaNeed cliDefaultStaticBytes cliDefaultStaticCount
      760000000 60000000 4200000 50000 ≤ 2 ^ 48 := by
  decide

/-- `1 GiB` decoupled-group `FitsEnv fineCostModel` bound at `fineCostModel.init`. -/
theorem fitsEnv_oneGiB_of_group_bounds_S4
    {lim : BudgetLimits} {Env : List AllocEvent → Prop}
    {cumB liveB peakB maxReq grpS : Nat}
    (hSpec : PhaseCreditSpec fineCostModel Env cumB liveB peakB maxReq)
    (hGrp : PhaseGroupSpec fineCostModel Env grpS)
    (hcum : cumB ≤ 760000000)
    (hlive : liveB ≤ 60000000)
    (hpeak : peakB ≤ 60000000)
    (hreq : maxReq ≤ 4200000)
    (hgrp : (grpS + FineScale - 1) / FineScale ≤ 50000)
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap : cliOneGiB ≤ lim.physCap) :
    FitsEnv fineCostModel lim fineCostModel.init Env := by
  have hram : cliDecoupledRamNeed lim.staticBytes 760000000 60000000 4200000 50000 ≤ lim.physCap :=
    Nat.le_trans
      (cliDecoupledRamNeed_mono hsb (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
      (Nat.le_trans cliDecoupledRamNeed_le_oneGiB_of_S4 hcap)
  have hva : cliDecoupledVaNeed lim.staticBytes lim.staticCount
      760000000 60000000 4200000 50000 ≤ 2 ^ 48 :=
    Nat.le_trans
      (cliDecoupledVaNeed_mono hsb hsc (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
      cliDecoupledVaNeed_le_2_48_of_S4
  exact fitsEnv_fineCostModel_of_group_literal_bounds
    hSpec hGrp hcum hlive hpeak hreq hgrp henf hram hva

/-- Non-vacuity 6-phase trace witness for `CliMainSixPhaseEnv` under `cliBudgetLimits` (`1 GiB`),
exercising `stdin` + session load, temporary `sc = 63` encryption/writeback buffers, and `LineWriter`. -/
@[expose] def CliMainWitnessEnv : List AllocEvent → Prop :=
  CliMainSixPhaseEnv
    (· = rustAllocEvents 48 8)
    (· = rustAllocEvents 64 8)
    (ConcatEnv (· = rustAllocEvents msgCapBytes 1) (· = rustAllocEvents sessionCapBytes 1))
    (ConcatEnv (· = rustAllocEvents sessionCapBytes 1) (· = rustDeallocEvents sessionCapBytes 1))
    (ConcatEnv (· = rustAllocEvents 512 1) (· = rustDeallocEvents 512 1))
    (· = rustAllocEvents 1024 1)

theorem cliMainWitnessEnv_inhabited :
    ∃ evs : List AllocEvent, CliMainWitnessEnv evs ∧ evs.length = 9 := by
  refine ⟨rustAllocEvents 48 8 ++
      (rustAllocEvents 64 8 ++
        (rustAllocEvents msgCapBytes 1 ++ rustAllocEvents sessionCapBytes 1)) ++
      (rustAllocEvents sessionCapBytes 1 ++ rustDeallocEvents sessionCapBytes 1 ++
        ((rustAllocEvents 512 1 ++ rustDeallocEvents 512 1) ++ rustAllocEvents 1024 1)),
    ?_, ?_⟩
  · unfold CliMainWitnessEnv CliMainSixPhaseEnv
    exact SeqEnv.append
      (SeqEnv.append rfl (SeqEnv.append rfl (ConcatEnv.append rfl rfl)))
      (Or.inr (SeqEnv.append (ConcatEnv.append rfl rfl)
        (SeqEnv.append (ConcatEnv.append rfl rfl) rfl)))
  · decide

end LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
