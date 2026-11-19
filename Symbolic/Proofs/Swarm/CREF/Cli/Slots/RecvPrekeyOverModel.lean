/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import Symbolic.Proofs.Swarm.CREF.TR.PureSessionBounds
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma
import Symbolic.Proofs.Hooks2.BridgeXPure
import Symbolic.Proofs.SR.SendSpecWPure
public import Symbolic.Proofs.Swarm.TRREF.SpqrSemOf -- proof-setup: allow-public-import
import Symbolic.Proofs.Swarm.CREF.Cli.RetiredStatementDefs
import Symbolic.Proofs.Swarm.CREF.Sem
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Refinement.LemmasPure -- shake: keep
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSession
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionSM
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhInputs
public import LibsignalBinary.Specifications.LibsignalE2E.StateXModel
public import LibsignalBinary.Specifications.SignalSession.PqDir
public import Symbolic.Specifications.Concrete.ExternInterpretation
public import Symbolic.Specifications.Concrete.MachineEvents

/-!
# Session-Clearing Domain Preservation and Pure SPQR Adapter

Proves that clearing `session := none` preserves `PqxdhPartyInSpecDomain` (`wfPq_clear_session`)
and defines the pure `Spqr` record `pureSpqrOf` induced by `spqrModelOf`.
-/

public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.Cli.Slots
open Symbolic.Swarm.CREF.CliPure

cref_open
open Symbolic.Swarm.CREF.CliPure
open CryptoProofLib.Refinement (ExternInterpretation)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.E2E
open CryptoVerification.SignalSession
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent StateAndMessage)
open DY.Libsignal.Refinement (sha256CompressFunction aesCbcDecryptSymbol)
open DY.Libsignal.PQXDH.Refinement (X25519TorsionFree)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure
open Symbolic.Swarm.TRREF.SpqrSemOf (spqrModelOf)

theorem wfPq_clear_session (P : PEParams) {st : PqParty} (hwf : PqxdhPartyInSpecDomain P st) :
    PqxdhPartyInSpecDomain P { st with session := none } := by
  obtain ⟨_, hfiles, hnd⟩ := hwf
  unfold PqxdhPartyInSpecDomain
  refine And.intro (fun _ _ h => nomatch h) (And.intro (fun f hf => hfiles f ?_) hnd)
  unfold encodeDir at hf ⊢
  simp only [List.mem_append, List.not_mem_nil, or_false] at hf ⊢
  tauto

/-- Pure `Spqr` record induced by `spqrModelOf`. -/
@[expose] def pureSpqrOf (interpretation : ExternInterpretation) : Spqr HwBytes HwBytes :=
  let M := spqrModelOf interpretation
  ⟨fun _ _ => [], M.send, M.recv, M.sendPanics, M.recvPanics⟩

end Symbolic.Swarm.CREF.Cli.Slots
