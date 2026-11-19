/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Security.Binary
public import Symbolic.Proofs.SpecLemmas.SecurityBinaryPlaced -- proof-setup: allow-public-import
import Symbolic.Proofs.Swarm.CREF.Cli.TopEvents

/-!
# Assembly-Level CLI Security from Whole-Protocol Refinement

Transfers relocatable whole-protocol CLI refinement (`CompRefinesCliBinaryPlaced`) to
assembly-level security (`SignalSessionSecurePlaced`).
-/

public section

set_option autoImplicit false

namespace Symbolic.Proofs.TopLevelHelpers.Composed.Cli.AsmSecurity

open Arm64.Obj (MultiPlacement)
open Arm64.Process (ElfImage)
open CryptoProofLib.Refinement (ExternInterpretation)
open CryptoVerification.SignalSession (CliHooks)
open DY.Libsignal.Composed.Refinement.Cli (signalSessionSecureFor_of_refines)

abbrev elfRelPlaced (mpl : MultiPlacement) (elf : ElfImage)
    (interp : ExternInterpretation) (W : CliHooks) :
    CryptoVerification.SignalSession.Inputs →
    Option CryptoVerification.SignalSession.Outcome → Prop :=
  DY.Libsignal.Composed.Refinement.Cli.elfRelPlaced mpl elf interp W

abbrev CompRefinesCliBinaryPlacedAt (mpl : MultiPlacement) (bytes : List (BitVec 8)) : Prop :=
  DY.Libsignal.Composed.Refinement.Cli.CompRefinesCliBinaryPlacedAt mpl bytes

abbrev CompRefinesCliBinaryPlaced (bytes : List (BitVec 8)) : Prop :=
  DY.Libsignal.Composed.Refinement.Cli.CompRefinesCliBinaryPlaced bytes

abbrev SignalSessionSecurePlacedAt (mpl : MultiPlacement) (bytes : List (BitVec 8)) : Prop :=
  DY.Libsignal.Composed.Security.SignalSessionSecurePlacedAt mpl bytes

abbrev SignalSessionSecurePlaced (bytes : List (BitVec 8)) : Prop :=
  DY.Libsignal.Composed.Security.SignalSessionSecurePlaced bytes

/-- Transfers `CompRefinesCliBinaryPlaced bytes` to `SignalSessionSecurePlaced bytes`. -/
theorem signal_session_secure_placed_of_binary_refines {bytes : List (BitVec 8)}
    (hBin : CompRefinesCliBinaryPlaced bytes) : SignalSessionSecurePlaced bytes := by
  intro mpl hLs
  rcases hBin mpl hLs with ⟨elf, hparse, hcode, hprog, hRef⟩
  exact ⟨elf, hparse, hcode, hprog, signalSessionSecureFor_of_refines hRef⟩

/-- Transfers `CompRefinesCliBinary bytes` to `SignalSessionSecure bytes`. -/
theorem signal_session_secure_of_binary_refines {bytes : List (BitVec 8)}
    (hBin : DY.Libsignal.Composed.Refinement.Cli.CompRefinesCliBinary bytes) :
    DY.Libsignal.Composed.Security.SignalSessionSecure bytes := by
  rcases hBin with ⟨elf, addrs, hparse, haddrs, hprog, hRef⟩
  exact ⟨elf, addrs, hparse, haddrs, hprog, signalSessionSecureFor_of_refines hRef⟩

end Symbolic.Proofs.TopLevelHelpers.Composed.Cli.AsmSecurity

namespace Symbolic.Proofs.TopLevelHelpers.Composed.Cli

open AsmSecurity (CompRefinesCliBinaryPlaced CompRefinesCliBinaryPlacedAt
  SignalSessionSecurePlaced SignalSessionSecurePlacedAt elfRelPlaced)

/-- Transfers `CompRefinesCliBinaryPlaced bytes` to `SignalSessionSecurePlaced bytes`. -/
theorem signal_session_secure_placed_of_binary_refines {bytes : List (BitVec 8)}
    (hBin : CompRefinesCliBinaryPlaced bytes) : SignalSessionSecurePlaced bytes :=
  AsmSecurity.signal_session_secure_placed_of_binary_refines hBin

/-- Transfers `CompRefinesCliBinary bytes` to `SignalSessionSecure bytes`. -/
theorem signal_session_secure_of_binary_refines {bytes : List (BitVec 8)}
    (hBin : DY.Libsignal.Composed.Refinement.Cli.CompRefinesCliBinary bytes) :
    DY.Libsignal.Composed.Security.SignalSessionSecure bytes :=
  AsmSecurity.signal_session_secure_of_binary_refines hBin

/--
info: 'Symbolic.Proofs.TopLevelHelpers.Composed.Cli.signal_session_secure_placed_of_binary_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms signal_session_secure_placed_of_binary_refines

/--
info: 'Symbolic.Proofs.TopLevelHelpers.Composed.Cli.signal_session_secure_of_binary_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms signal_session_secure_of_binary_refines

end Symbolic.Proofs.TopLevelHelpers.Composed.Cli
