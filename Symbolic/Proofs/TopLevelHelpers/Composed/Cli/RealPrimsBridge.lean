/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.ElfBinding
import Symbolic.Proofs.SpecLemmas.ElfBindingSha256

/-!
# Parametric Bridge to `CompRefinesCliBinaryReal` (`RP-REF`)

Proves `cliElfProgressReal_of_progress` and `compRefinesCliBinaryReal_of_binary`, transferring
hook-parametric `CliElfProgress` and `CompRefinesCliBinary bytes` plus `RealPrimsAdmissible` to
`CompRefinesCliBinaryReal bytes` without importing `CliElf` or `RefinementElf` (blueprint node
`RP-REF`).

- **Proof idea**: Specialize `CliElfProgress` and `CompRefinesCli HooksMatchPlaced (elfRel elf addrs)`
  at `W := realCliHooks`. By `ElfBindingSha256.realHooksAgreeOnInput_iff_true_of_eq` and
  `ElfBindingSha256.elfRel_eq_runFnToRelation_of_eq`, `RealHooksAgreeOnInput realCliHooks i` holds
  unconditionally and `elfRel elf addrs interp realCliHooks = elfRelReal elf addrs interp u`, so
  rewriting `CliReachable` and `CliTraces` yields `CliElfProgressReal` and unfiltered
  `CompRefinesCli`.
- **Status**: `done` (Falsification: hypothesis-drop mutations `¬ CompRefinesCliBinaryReal []` when
  dropping `href`, universal-vs-existential gap when dropping `hadm`, and specialization at
  `W = realCliHooks`; no counterexample).
- **Handoff**: Complete with `0 sorry` and no binary (`CliElf` / `RefinementElf`) imports; wired into
  `RealPrims.lean`.
-/

public section

set_option autoImplicit false

namespace Symbolic.Proofs.TopLevelHelpers.Composed.Cli.RealPrimsBridge

open Arm64.Process (ElfImage)
open CryptoProofLib.Refinement (ExternInterpretation)
open CryptoVerification.SignalSession (CliElfAddrs)
open DY.Libsignal.Composed.Refinement.Cli
  (CliElfProgress CliElfProgressReal CompRefinesCli CompRefinesCliBinary CompRefinesCliBinaryReal
   HooksMatchPlaced RealPrimsAdmissible RealPrimsMatch elfRel elfRelReal
   elfRel_eq_runFnToRelation_of_eq realCliHooks realHooksAgreeOnInput_iff_true_of_eq)

private theorem elfRel_realCliHooks_eq_elfRelReal
    (elf : ElfImage) (addrs : CliElfAddrs) (interp : ExternInterpretation) (u : Unit) :
    elfRel elf addrs interp realCliHooks = elfRelReal elf addrs interp u :=
  elfRel_eq_runFnToRelation_of_eq elf addrs interp rfl

private theorem compRefinesCli_elfRelReal_of_elfRel {elf : ElfImage} {addrs : CliElfAddrs}
    (href : CompRefinesCli HooksMatchPlaced (elfRel elf addrs)) :
    CompRefinesCli (fun interp (_ : Unit) => RealPrimsMatch interp) (elfRelReal elf addrs) := by
  intro interp hcontracts u hmatch r hr
  obtain ⟨S, hS⟩ := href interp hcontracts realCliHooks hmatch r hr
  refine ⟨S, fun evs htr hinv => ?_⟩
  rw [← elfRel_realCliHooks_eq_elfRelReal elf addrs interp u] at htr
  exact hS evs htr hinv

/-- Specializes `CliElfProgress` at `W := realCliHooks` to obtain unfiltered `CliElfProgressReal`. -/
theorem cliElfProgressReal_of_progress {elf : ElfImage} {addrs : CliElfAddrs}
    (hprog : CliElfProgress elf addrs) : CliElfProgressReal elf addrs := by
  intro interp hcontracts hmatch r hr t hreach c i hvc hin
  rw [← elfRel_realCliHooks_eq_elfRelReal elf addrs interp ()] at hreach
  exact hprog interp hcontracts realCliHooks hmatch r hr t hreach c i hvc hin
    ((realHooksAgreeOnInput_iff_true_of_eq rfl i).mpr trivial)

/-- Parametric bridge from `RealPrimsAdmissible` and `CompRefinesCliBinary bytes` to
`CompRefinesCliBinaryReal bytes`. -/
theorem compRefinesCliBinaryReal_of_binary {bytes : List (BitVec 8)}
    (hadm : RealPrimsAdmissible) (href : CompRefinesCliBinary bytes) :
    CompRefinesCliBinaryReal bytes := by
  obtain ⟨elf, addrs, hparse, haddrs, hprog, hcli⟩ := href
  exact ⟨hadm, elf, addrs, hparse, haddrs,
    cliElfProgressReal_of_progress hprog,
    compRefinesCli_elfRelReal_of_elfRel hcli⟩

end Symbolic.Proofs.TopLevelHelpers.Composed.Cli.RealPrimsBridge
