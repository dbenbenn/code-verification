/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.ElfBinding
public import Symbolic.Specifications.Security.Binary
import Symbolic.Proofs.SpecLemmas.ElfBindingSha256

/-!
# Parametric Bridge to `SignalSessionSecureReal` (`RP-SEC`)

Proves `signalSessionSecureReal_of_binary`, transferring `RealPrimsAdmissible` and
hook-parametric `SignalSessionSecure bytes` to `SignalSessionSecureReal bytes` without importing
`CliElf` or `AsmLevelSecurityElf` (blueprint node `RP-SEC`).

- **Proof idea**: Unpack `hsec : SignalSessionSecure bytes` and specialize both `CliElfProgress` and
  `SignalSessionSecureFor HooksMatchPlaced (elfRel elf addrs)` at `W := realCliHooks`. By
  `ElfBindingSha256.realHooksAgreeOnInput_iff_true_of_eq` and
  `ElfBindingSha256.elfRel_eq_runFnToRelation_of_eq`, the per-call guard holds trivially and
  `elfRel elf addrs interp realCliHooks = elfRelReal elf addrs interp u`, transferring both
  `CliReachable` and `CliTraces` directly.
- **Status**: `done` (Falsification: hypothesis-drop mutations `¬ SignalSessionSecureReal []` when
  dropping `hsec`, universal-vs-existential gap when dropping `hadm`, and specialization at
  `W = realCliHooks`; no counterexample).
- **Handoff**: Complete with `0 sorry` and no binary (`CliElf` / `AsmLevelSecurityElf`) imports;
  wired into `RealPrims.lean`.
-/

public section

set_option autoImplicit false

namespace Symbolic.Proofs.TopLevelHelpers.Composed.Cli.RealPrimsSecBridge

open Arm64.Process (ElfImage)
open CryptoProofLib.Refinement (ExternInterpretation)
open CryptoVerification.SignalSession (CliElfAddrs)
open DY.Libsignal.Composed.Refinement.Cli
  (CliElfProgress CliElfProgressReal HooksMatchPlaced RealPrimsAdmissible RealPrimsMatch elfRel
   elfRelReal elfRel_eq_runFnToRelation_of_eq realCliHooks realHooksAgreeOnInput_iff_true_of_eq)
open DY.Libsignal.Composed.Security (SignalSessionSecure SignalSessionSecureFor SignalSessionSecureReal)

private theorem elfRel_realCliHooks_eq_elfRelReal
    (elf : ElfImage) (addrs : CliElfAddrs) (interp : ExternInterpretation) (u : Unit) :
    elfRel elf addrs interp realCliHooks = elfRelReal elf addrs interp u :=
  elfRel_eq_runFnToRelation_of_eq elf addrs interp rfl

private theorem cliElfProgressReal_of_progress_sec {elf : ElfImage} {addrs : CliElfAddrs}
    (hprog : CliElfProgress elf addrs) : CliElfProgressReal elf addrs := by
  intro interp hcontracts hmatch r hr t hreach c i hvc hin
  rw [← elfRel_realCliHooks_eq_elfRelReal elf addrs interp ()] at hreach
  exact hprog interp hcontracts realCliHooks hmatch r hr t hreach c i hvc hin
    ((realHooksAgreeOnInput_iff_true_of_eq rfl i).mpr trivial)

private theorem signalSessionSecureFor_elfRelReal_of_elfRel {elf : ElfImage} {addrs : CliElfAddrs}
    (hfor : SignalSessionSecureFor HooksMatchPlaced (elfRel elf addrs)) :
    SignalSessionSecureFor (fun interp (_ : Unit) => RealPrimsMatch interp)
      (elfRelReal elf addrs) := by
  intro interp hcontracts u hmatch r hr
  obtain ⟨S, hS⟩ := hfor interp hcontracts realCliHooks hmatch r hr
  refine ⟨S, fun evs htr hinv hcf => ?_⟩
  rw [← elfRel_realCliHooks_eq_elfRelReal elf addrs interp u] at htr
  exact hS evs htr hinv hcf

/-- Parametric bridge from `RealPrimsAdmissible` and `SignalSessionSecure bytes` to
`SignalSessionSecureReal bytes`. -/
theorem signalSessionSecureReal_of_binary {bytes : List (BitVec 8)}
    (hadm : RealPrimsAdmissible) (hsec : SignalSessionSecure bytes) :
    SignalSessionSecureReal bytes := by
  obtain ⟨elf, addrs, hparse, haddrs, hprog, hfor⟩ := hsec
  exact ⟨hadm, elf, addrs, hparse, haddrs,
    cliElfProgressReal_of_progress_sec hprog,
    signalSessionSecureFor_elfRelReal_of_elfRel hfor⟩

end Symbolic.Proofs.TopLevelHelpers.Composed.Cli.RealPrimsSecBridge
