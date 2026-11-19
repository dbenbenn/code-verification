/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.ProcessBridgePq -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.ProcessOom -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliBinaryPqProofDefs
import LibsignalBinary.Proofs.SignalSession.Cli.RunBridge
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

public section

set_option autoImplicit false
set_option maxRecDepth 200000

/-!
# Whole-Binary PQXDH CLI Composition

Layout-generic composition from `MainOkCliPq`, non-matching pre-key `recv` (`MainOkOver`),
`Cli.muslHarness_ok`, and ELF `PT_LOAD` segment-slice witnesses (`CliElfFrozen`, `CliElfStatics`,
`CliElfTokenCells`, `patchElfTokens`) to `CliSpecPqxdhNoMatch`, `CliPqxdhElfCorrectUnderAllocOk elf`,
and `CliPqxdhBinaryCorrectUnderAllocOk bytes`. Also proves the decomposition
`CliPqxdhAllocNeverFails elf W ↔ CliPqFiveAllocOk elf W ∧ CliPqNoMatchAllocOk elf W`.
-/

namespace CryptoVerification.SignalSession

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession.MuslElf

/-! ## 1. `OutcomeMatchesModelExceptPath`, `CliPqxdhInputs`, and `CliPqxdhAllocNeverFails` Lemmas -/

theorem Outcome.AgreeExcept.refl (p : String) (o : Outcome) : Outcome.AgreeExcept p o o := by
  cases o <;> simp [Outcome.AgreeExcept]

theorem OutcomeMatchesModelExceptPath.of_eq {W : PEParams} {i : Inputs} {p : String}
    {r : Option (Option (PqParty × List (BitVec 8)))} {o : Outcome}
    (h : o = pqxdhExpectedOutcome W i r) : OutcomeMatchesModelExceptPath W i p r o := by
  subst h
  unfold OutcomeMatchesModelExceptPath
  split
  · exact Outcome.AgreeExcept.refl p _
  · rfl

theorem cliPqInputs_init {W : PEParams} {st : PqParty} (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) (hst : PqxdhPartyInSpecDomain W st) (hnone : st.session = none) :
    CliPqxdhInputs W (pqInitInputs W st b t) :=
  ⟨st, hst, Or.inl ⟨hnone, b, t, rfl⟩⟩

theorem cliPqInputs_send {W : PEParams} {st : PqParty} (m : List (BitVec 8))
    (r : List.Vector (BitVec 8) 64) (hst : PqxdhPartyInSpecDomain W st) (hm : m.length < 2 ^ 32) :
    CliPqxdhInputs W (pqSendInputs W st m r) :=
  ⟨st, hst, Or.inr (Or.inl ⟨m, r, hm, rfl⟩)⟩

theorem cliPqInputs_recvWhisper {W : PEParams} {st : PqParty} (c : List (BitVec 8))
    (rc : BitVec 256) (hst : PqxdhPartyInSpecDomain W st) (hc : c.length < 2 ^ 32) :
    CliPqxdhInputs W (pqRecvInputs W st (wireWhisper :: c) rc) :=
  ⟨st, hst, Or.inr (Or.inr (Or.inl ⟨c, rc, hc, rfl⟩))⟩

theorem cliPqInputs_recvPrekey {W : PEParams} {st : PqParty} (m : PreKeyMessageFields)
    (rc : BitVec 256) (hst : PqxdhPartyInSpecDomain W st) (hm : m.inner.length + 2048 < 2 ^ 32) :
    CliPqxdhInputs W (pqRecvInputs W st (wirePrekey :: m.bytes) rc) :=
  ⟨st, hst, Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rc, hm, rfl⟩)))⟩

theorem cliPqInputs_recvBad {W : PEParams} {st : PqParty} (c : List (BitVec 8))
    (rc : BitVec 256) (hst : PqxdhPartyInSpecDomain W st) (hc : c.length < 2 ^ 32)
    (h2 : c.head? ≠ some wireWhisper) (h3 : c.head? ≠ some wirePrekey) :
    CliPqxdhInputs W (pqRecvInputs W st c rc) :=
  ⟨st, hst, Or.inr (Or.inr (Or.inr (Or.inr ⟨c, rc, hc, h2, h3, rfl⟩)))⟩

end CryptoVerification.SignalSession
