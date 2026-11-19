/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.CliBinaryProof -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.ProcessBridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.SmDirProofDefs
import LibsignalBinary.Proofs.E2E.Bin.Tpidr
import LibsignalBinary.Proofs.SignalSession.Cli.Main.GamePaths
import LibsignalBinary.Proofs.SignalSession.Cli.Main.MuslHarnessOk
import LibsignalBinary.Proofs.SignalSession.Cli.RunBridge
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliSymtabGhost
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Process
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs

public section

set_option autoImplicit false
set_option maxRecDepth 200000

/-!
# Whole-Process Out-of-Memory Predicate and Signal-Status Bridges

Defines `PanickedAllocFails` and preserves `SIGABRT` signal status across `toSigState`.
-/

namespace CryptoVerification.SignalSession

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalProtoCodec
open CryptoVerification.SignalSession.MuslElf

/-! ## Tight `main` OOM Predicate -/

/-- Strengthened `Cli.RunAllocFails` witnessing a reachable `.Panicked` state whose trace contains `allocFailedEvent`. -/
@[expose] def PanickedAllocFails (elf : ElfImage) (P : Program) (i : Inputs) : Prop :=
  ∃ s0 sf, elf.loadState (Cli.cliInputs i) = .ok s0 ∧
    Steps P s0 sf ∧ sf.status = .Panicked ∧ RustHeap.allocFailedEvent ∈ sf.trace

theorem status_toSigState_of_panicked {s : State} (h : s.status = .Panicked) :
    (toSigState s).status = .Signaled 6 := by
  unfold toSigState sigAbrt
  simp [h, State.status_setStatus]

end CryptoVerification.SignalSession
