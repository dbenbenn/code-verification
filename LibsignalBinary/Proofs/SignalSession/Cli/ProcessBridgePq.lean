/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.PqBundleInst -- proof-setup: allow-public-import
import all Init.Data.String.Defs
import all Init.Data.String.Basic
import all Init.Data.Repr
import all Init.Data.ToString.Basic
public import LibsignalBinary.Proofs.SignalSession.Cli.ProcessBridge -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Main.GamePaths -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.RunBridge -- shake: keep
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Run -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

public section

set_option autoImplicit false
set_option maxRecDepth 200000

/-!
# Whole-Process Symbolic PQXDH Bridge

Composes `MainOkCliPq` and `ProcessBridge.cliRunsTo_of_main_call` into per-input (`CliSpecPqPerInput`)
and global-allocation (`CliSpecPqxdh`) 5-clause whole-process specifications on
`cliRunAbortOnPanic elf W`, together with unconditional OOM-disjunction counterparts.
-/

namespace CryptoVerification.SignalSession

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession.MuslElf CryptoVerification.SignalSession.ElfFrozen

/-! ## PQXDH Input Side Conditions -/

theorem inputsLoadable_pqInitInputs (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) (hst : PqxdhPartyInSpecDomain W st) :
    Cli.InputsLoadable (pqInitInputs W st b t) := by
  refine ⟨(loadable_pqInitInputs W st b t).1, fun f hf =>
    ⟨(loadable_pqInitInputs W st b t).2 f hf, ?_⟩⟩
  simp only [pqInitInputs, pqInputs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    or_assoc] at hf
  rcases hf with h | h | rfl
  · have hlt := hst.2.1 f h; unfold MAX_LFS_FILESIZE; omega
  · unfold publicBundleOf PublicBundle.files at h
    cases ho : b.opk with
    | none =>
      simp only [ho, Option.map_none, List.append_nil, List.mem_cons, List.not_mem_nil,
        or_false] at h
      rcases h with rfl | rfl | rfl | rfl <;>
        simp [djbKey, kyberKey, le32, MAX_LFS_FILESIZE]
    | some ok =>
      obtain ⟨id, key⟩ := ok
      simp only [ho, Option.map_some, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl <;>
        simp [djbKey, kyberKey, le32, MAX_LFS_FILESIZE]
  · simp [initiateTapeLen, MAX_LFS_FILESIZE]

theorem inputsLoadable_pqSendInputs (W : PEParams) (st : PqParty) (m : List (BitVec 8))
    (r : List.Vector (BitVec 8) 64) (hst : PqxdhPartyInSpecDomain W st) :
    Cli.InputsLoadable (pqSendInputs W st m r) := by
  refine ⟨(loadable_pqSendInputs W st m r).1, fun f hf =>
    ⟨(loadable_pqSendInputs W st m r).2 f hf, ?_⟩⟩
  simp only [pqSendInputs, pqInputs, List.append_nil, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hf
  rcases hf with h | rfl
  · have hlt := hst.2.1 f h; unfold MAX_LFS_FILESIZE; omega
  · simp [MAX_LFS_FILESIZE]

theorem inputsLoadable_pqRecvInputs (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) (hst : PqxdhPartyInSpecDomain W st) :
    Cli.InputsLoadable (pqRecvInputs W st c rc) := by
  refine ⟨(loadable_pqRecvInputs W st c rc).1, fun f hf =>
    ⟨(loadable_pqRecvInputs W st c rc).2 f hf, ?_⟩⟩
  simp only [pqRecvInputs, pqInputs, List.append_nil, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hf
  rcases hf with h | rfl
  · have hlt := hst.2.1 f h; unfold MAX_LFS_FILESIZE; omega
  · simp [HMAC.keyToBytes32, MAX_LFS_FILESIZE]

theorem coinsReadable_pqInitInputs (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    Cli.CoinsReadable (pqInitInputs W st b t) :=
  Cli.coinsReadable_pqInputs W st _ _ _ _ (Or.inr ⟨b, rfl⟩)

theorem coinsReadable_pqSendInputs (W : PEParams) (st : PqParty) (m : List (BitVec 8))
    (r : List.Vector (BitVec 8) 64) :
    Cli.CoinsReadable (pqSendInputs W st m r) :=
  Cli.coinsReadable_pqInputs W st _ _ _ _ (Or.inl rfl)

theorem coinsReadable_pqRecvInputs (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) :
    Cli.CoinsReadable (pqRecvInputs W st c rc) :=
  Cli.coinsReadable_pqInputs W st _ _ _ _ (Or.inl rfl)

theorem cliInputsOk_pqInitInputs (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    Cli.CliInputsOk (pqInitInputs W st b t) := by
  unfold Cli.CliInputsOk PrintableAsciiArg ArgvFitsInitialStack pqInitInputs pqInputs
  dsimp only
  cases st.party <;> decide

theorem cliInputsOk_pqSendInputs (W : PEParams) (st : PqParty) (m : List (BitVec 8))
    (r : List.Vector (BitVec 8) 64) :
    Cli.CliInputsOk (pqSendInputs W st m r) := by
  unfold Cli.CliInputsOk PrintableAsciiArg ArgvFitsInitialStack pqSendInputs pqInputs
  dsimp only
  cases st.party <;> decide

theorem cliInputsOk_pqRecvInputs (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) :
    Cli.CliInputsOk (pqRecvInputs W st c rc) := by
  unfold Cli.CliInputsOk PrintableAsciiArg ArgvFitsInitialStack pqRecvInputs pqInputs
  dsimp only
  cases st.party <;> decide

end CryptoVerification.SignalSession
