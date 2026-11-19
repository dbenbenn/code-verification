/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.RealMainBinaryEnvAdapterD3 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyDom0Record -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlotDom0 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.GrowOne104Budget
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.HookLift
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetSubHops

/-!
# Parametric & Closed `archivedTrials = []` Producers

Producers discharging `archivedTrials = []` (`Dom0`) from session-file and `loadRec` ties:
1. Polymorphic `{α : Type} {xs : List α}` eliminators (`list_eq_nil_of_loadRec_ok_tie`,
   `list_eq_nil_of_loadRec_decode_tie`, `list_eq_nil_of_deserialize_tie`) and `W4RecvPrekeyRealDom0`
   lifts (`w4RecvPrekeyRealDom0_of_recordTie`, `w4RecvPrekeyRealDom0_of_loadRec_tie`).
2. Closed `CliPqOrD3RecvDom` producers (`exists_loadRec_scopeKit_ok_of_cliPqOrD3RecvDom`,
   `sessions_get_deserialize_prev0_of_cliPqOrD3RecvDom`, and the induced `list_eq_nil_*` and
   `w4RecvPrekeyRealDom0Of_of_cliPqOrD3RecvDom_*` lemmas).
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyDom0Tie

open Arm64.Process (bytesOfString)
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification.E2E (PEParams)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession (Inputs)
open CryptoVerification.SignalSession.Cli (StoresGhost addressText)
open CryptoVerification.SignalSession.Cli.MainHops (AddrV cliIo parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose (addrValOf runFiles)
open CryptoVerification.SignalSession.Cli.Slots (EncodeInjOn loadRec scopeIn scopeKit)
open LibsignalBinary.Proofs.PeakBudget.RealMainBinaryEnvAdapterD3 (CliPqOrD3RecvDom)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyDom0Record
  (RecordStructure cliPqOrD3RecvDom_eq_pqRecvInputs
   deserialize_encodeRecordUnderExtras_of_record_le encodeRecordUnderExtras_length_le_2pow64_of_wf
   loadRec_cliPqOrD3RecvDom_scopeKit_some_decode loadRec_pqRecv_of_scope
   loadRec_pqRecv_scopeKit_eq sessions_get_pqRecv_eq)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot
  (W4RecvPrekeyRealDom W4RecvPrekeyRealParams)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot1MiB (W4RecvPrekeyRealDomOf)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlotDom0
  (W4RecvPrekeyRealDom0 W4RecvPrekeyRealDom0Of)

/-! ## Parametric `list_eq_nil_*` & `w4RecvPrekeyRealDom0_of_recordTie` Producers -/

/-- Polymorphic prost `RecordStructure.decode` tie consumer over `loadRec Scope F peer = .ok recOpt`:
covers both `recOpt = none` (`hNone`) and `recOpt = some r` (`hTie` + `hPrev0`). -/
theorem list_eq_nil_of_loadRec_decode_tie {α : Type}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer : AddrVal} {recOpt : Option (SessionRecord (List (BitVec 8)))} {xs : List α}
    (hlr : loadRec Scope F peer = .ok recOpt)
    (hNone : loadRec Scope F peer = .ok none → xs = [])
    (hTie : ∀ r rec, loadRec Scope F peer = .ok (some r) →
      RecordStructure.decode (encodeRecord r) = some rec →
      xs.length ≤ rec.previousSessions.length)
    (hPrev0 : ∀ r, loadRec Scope F peer = .ok (some r) →
      ∃ rec, RecordStructure.decode (encodeRecord r) = some rec ∧ rec.previousSessions = []) :
    xs = [] := by
  cases recOpt with
  | none => exact hNone hlr
  | some r =>
    obtain ⟨rec, hdec, hnil⟩ := hPrev0 r hlr
    have hle := hTie r rec hlr hdec
    rw [hnil, List.length_nil, Nat.le_zero] at hle
    exact List.eq_nil_of_length_eq_zero hle

/-- Polymorphic prost `RecordStructure.deserialize` tie consumer over raw
`StoresGhost.opened.sessions.get`: handles both empty (`[]` → `orec = none`) and non-empty
(`b :: bs` → `orec = some rec`) session files with a single `hTie` hypothesis. -/
theorem list_eq_nil_of_deserialize_tie {α : Type}
    {F : FsFiles} {peer : AddrVal} {bs : List (BitVec 8)} {orec : Option RecordStructure}
    {xs : List α}
    (hget : StoresGhost.opened.sessions.get cliIo.rd F (addressText peer) = .ok bs)
    (hdes : RecordStructure.deserialize bs = .ok orec)
    (hprev0 : (orec.map (·.previousSessions.length)).getD 0 = 0)
    (hTie : ∀ bs' orec',
      StoresGhost.opened.sessions.get cliIo.rd F (addressText peer) = .ok bs' →
      RecordStructure.deserialize bs' = .ok orec' →
      xs.length ≤ (orec'.map (·.previousSessions.length)).getD 0) :
    xs = [] := by
  have hle := hTie bs orec hget hdes
  rw [hprev0, Nat.le_zero] at hle
  exact List.eq_nil_of_length_eq_zero hle

/-! ## Closed `archivedTrials = []` Producers on `CliPqOrD3RecvDom` -/

/-- `scopeKit` specialization of `exists_loadRec_ok_of_cliPqOrD3RecvDom` (`0` extra hypotheses). -/
theorem exists_loadRec_scopeKit_ok_of_cliPqOrD3RecvDom {W : PEParams}
    {i : Inputs} {peer : AddrV}
    (hi : CliPqOrD3RecvDom W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peer)) :
    ∃ recOpt, loadRec scopeKit (runFiles i) (addrValOf peer) = .ok recOpt := by
  obtain ⟨st, ct, rc, hwf, rfl⟩ := cliPqOrD3RecvDom_eq_pqRecvInputs hi hparse
  exact ⟨_, loadRec_pqRecv_scopeKit_eq hwf hparse⟩

/-- On any `.recv peer` input in `CliPqOrD3RecvDom W i`, raw `StoresGhost.opened.sessions.get`
succeeds and prost `RecordStructure.deserialize` yields `0` previous sessions across both
`st.session = none` (`bs = []`, `orec = none`) and `st.session = some (x, g)` (`orec = some ⟨…, []⟩`). -/
theorem sessions_get_deserialize_prev0_of_cliPqOrD3RecvDom {W : PEParams}
    {i : Inputs} {peer : AddrV}
    (hi : CliPqOrD3RecvDom W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peer)) :
    ∃ bs orec,
      StoresGhost.opened.sessions.get cliIo.rd (runFiles i) (addressText (addrValOf peer)) =
        .ok bs ∧
      RecordStructure.deserialize bs = .ok orec ∧
      (orec.map (·.previousSessions.length)).getD 0 = 0 := by
  obtain ⟨st, ct, rc, hwf, rfl⟩ := cliPqOrD3RecvDom_eq_pqRecvInputs hi hparse
  have hget := sessions_get_pqRecv_eq hwf hparse
  cases hs : st.session with
  | none =>
    rw [hs] at hget
    exact ⟨[], none, hget, RecordStructure.deserialize_nil, rfl⟩
  | some xg =>
    rcases xg with ⟨x, g⟩
    rw [hs] at hget
    have hlen := encodeRecordUnderExtras_length_le_2pow64_of_wf hwf hs
    exact ⟨_, _, hget, deserialize_encodeRecordUnderExtras_of_record_le hlen, rfl⟩

/-- Polymorphic `xs = []` producer on `CliPqOrD3RecvDom W i` from a `loadRec` +
`RecordStructure.decode` tie across both `st.session = none` and `st.session = some (x, g)`. -/
theorem list_eq_nil_of_cliPqOrD3RecvDom_loadRec_decodeTie {α : Type} {W : PEParams}
    {i : Inputs} {peer : AddrV} {xs : List α}
    (hi : CliPqOrD3RecvDom W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peer))
    (hNone : loadRec scopeKit (runFiles i) (addrValOf peer) = .ok none → xs = [])
    (hTie : ∀ r rec, loadRec scopeKit (runFiles i) (addrValOf peer) = .ok (some r) →
      RecordStructure.decode (encodeRecord r) = some rec →
      xs.length ≤ rec.previousSessions.length) :
    xs = [] := by
  obtain ⟨recOpt, hlr⟩ := exists_loadRec_scopeKit_ok_of_cliPqOrD3RecvDom hi hparse
  refine list_eq_nil_of_loadRec_decode_tie hlr hNone hTie fun r hsome => ?_
  obtain ⟨_, _, _, _, _, _, _, _, hdec, _⟩ :=
    loadRec_cliPqOrD3RecvDom_scopeKit_some_decode hi hparse hsome
  exact ⟨_, hdec, rfl⟩

/-- Polymorphic `xs = []` producer on `CliPqOrD3RecvDom W i` from a `sessions.get` +
`RecordStructure.deserialize` tie handling both `st.session = none` and `st.session = some (x, g)`. -/
theorem list_eq_nil_of_cliPqOrD3RecvDom_deserializeTie {α : Type} {W : PEParams}
    {i : Inputs} {peer : AddrV} {xs : List α}
    (hi : CliPqOrD3RecvDom W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peer))
    (hTie : ∀ bs orec,
      StoresGhost.opened.sessions.get cliIo.rd (runFiles i) (addressText (addrValOf peer)) =
        .ok bs →
      RecordStructure.deserialize bs = .ok orec →
      xs.length ≤ (orec.map (·.previousSessions.length)).getD 0) :
    xs = [] := by
  obtain ⟨bs, orec, hget, hdes, hprev0⟩ :=
    sessions_get_deserialize_prev0_of_cliPqOrD3RecvDom hi hparse
  exact list_eq_nil_of_deserialize_tie hget hdes hprev0 hTie

end LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyDom0Tie
