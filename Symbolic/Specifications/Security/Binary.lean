/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.ElfBinding
public import Symbolic.Specifications.Security.AsmSecure

/-!
# Binary Security Statement for `libsignal-cli`

**Trusted: the statement.**

States the top-level security theorem `SignalSessionSecure bytes` for the ARM64 ELF binary
implementing PQXDH, SPQR, and the Triple Ratchet, via the run-parametric property
`SignalSessionSecureFor Agree R`.
-/

@[expose] public section

set_option autoImplicit false

namespace DY.Libsignal.Composed.Security

open Arm64.Process (ElfImage)
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (CliEvent RunEvent)
open DY.Libsignal.Composed.Refinement
  (AllSecurityQueriesHoldOnHwTrace Explains OpaqueSymbolSemantics
   ProtocolSetup ProtocolSetupWF)
open DY.Libsignal.Composed.Refinement.Cli
  (CliElfProgress CliElfProgressReal CliTraces CliTurn CoinsFresh ExternContractsHoldCli
   HooksMatchPlaced InvertsGuarded NextEventCollides RealPrimsAdmissible RealPrimsMatch elfRel
   elfRelReal initDirs)
open CryptoVerification.SignalSession (CliElfAddrs Inputs Outcome resolveCliElfAddrs)

/-- Protocol security over run relation `R` and primitive-agreement predicate `Agree` from
`initDirs`: for every valid `interp`, agreeing `W`, and well-formed `r`, there exist opaque
semantics `S` such that every guarded, coin-fresh trace `evs` is either explained (`Explains`) and
satisfies `AllSecurityQueriesHoldOnHwTrace`, or has an explained prefix `evs₁` satisfying
`AllSecurityQueriesHoldOnHwTrace` whose next run event hits `NextEventCollides`. -/
def SignalSessionSecureFor {ω : Type} (Agree : ExternInterpretation → ω → Prop)
    (R : ExternInterpretation → ω → Inputs → Option Outcome → Prop) : Prop :=
  ∀ interp : ExternInterpretation, ExternContractsHoldCli interp →
  ∀ W : ω, Agree interp W →
  ∀ r : ProtocolSetup, ProtocolSetupWF r →
  ∃ S : OpaqueSymbolSemantics,
  ∀ evs : List CliEvent,
    CliTraces (R interp W) interp r (CliTurn.init (initDirs interp r)) evs →
    InvertsGuarded interp r evs →
    CoinsFresh r evs →
    (
      (∃ g ss vis, Explains interp r S g ss vis evs) ∧
      AllSecurityQueriesHoldOnHwTrace interp r S evs)
    ∨ (∃ (evs₁ : List CliEvent) (ev : RunEvent) (evs₂ : List CliEvent),
        evs = evs₁ ++ .run ev :: evs₂ ∧
        (∃ g ss vis,
          Explains interp r S g ss vis evs₁ ∧
          NextEventCollides interp r S g ss vis evs₁ ev) ∧
        AllSecurityQueriesHoldOnHwTrace interp r S evs₁)

/-- Binary security and no-fault progress of ELF image `bytes`: parses `bytes`, resolves the 18
panic and 5 `SampleNTT` addresses from `.symtab` (`resolveCliElfAddrs`), and asserts
`CliElfProgress elf addrs` and `SignalSessionSecureFor HooksMatchPlaced (elfRel elf addrs)`. -/
def SignalSessionSecure (bytes : List (BitVec 8)) : Prop :=
  ∃ (elf : ElfImage) (addrs : CliElfAddrs),
    ElfImage.parse bytes = .ok elf ∧
    resolveCliElfAddrs bytes elf = .ok addrs ∧
    CliElfProgress elf addrs ∧
    SignalSessionSecureFor HooksMatchPlaced (elfRel elf addrs)

/-- Binary security and no-fault progress of ELF image `bytes` at the real primitives: the real
primitives obey the symbolic laws (`RealPrimsAdmissible`); `bytes` parses and its 18 panic and 5
`SampleNTT` addresses resolve from `.symtab` (`resolveCliElfAddrs`); progress holds
(`CliElfProgressReal`); and `SignalSessionSecureFor` holds on guarded, coin-fresh traces
(`CliTraces` with `ValidCall` / `InputsFor` / `LeaksFrom`, `InvertsGuarded`, and `CoinsFresh`) over
`elfRelReal elf addrs` (no `RealHooksAgreeOnInput` filter) for every extern interpretation agreeing
with `realCliHooks` (`RealPrimsMatch`). -/
def SignalSessionSecureReal (bytes : List (BitVec 8)) : Prop :=
  RealPrimsAdmissible ∧
  ∃ (elf : ElfImage) (addrs : CliElfAddrs),
    ElfImage.parse bytes = .ok elf ∧
    resolveCliElfAddrs bytes elf = .ok addrs ∧
    CliElfProgressReal elf addrs ∧
    SignalSessionSecureFor (fun interp (_ : Unit) => RealPrimsMatch interp) (elfRelReal elf addrs)

end DY.Libsignal.Composed.Security
