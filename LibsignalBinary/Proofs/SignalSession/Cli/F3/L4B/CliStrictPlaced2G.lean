/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3ExternNoAllocFail
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.PlacedOomRecovery2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2EntryGuard -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemFirstStopTransfer -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Domains
import LibsignalBinary.Proofs.SpecLemmas.FsFold
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Process
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Run
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.RunProofDefs
import ProofLib.ProgramReflection
import LibsignalBinary.Proofs.SpecLemmas.RoLiterals
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced -- proof-setup: allow-public-import

/-!
# Entry-Guarded Two-Placement `extB2NeedLocks` Strict Composer

Entry-guarded counterparts of `CliStrictPlaced2` threading `F3C2EntryGuard mpl mmpl` from
`ElfSlicesPqOomC2EntryGuardLr.cliElf_f3MuslHarness_c2EntryGuard_of_linkedAt` and
`Block617TransferFixedHypG` into
`CliStrictPlaced2.outcome_of_main_strict_b2_needLocks_guarded_perInput_at`. Eliminating the entry
guard internally at the process harness boundary leaves the whole-process conclusions
(`cliRunExtOnInputsSigAt = some …`, `CliSpecPqxdh`, `CliPqxdhElfCorrectStrictPlaced2`,
`CliPqxdhElfCorrectPlaced`) guard-free.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2G

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoGames (Party)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (GhostState)
open CryptoVerification.E2E
  (Bytes PEParams PreKeyBundleFields PreKeyMessageFields RecordExtras UnreachedPqxdhPrimitives
   djbKey initiateTapeLen kyberKey partyAddressName wirePrekey wireWhisper)
open CryptoVerification.LibsignalSpqrV1 (sha256Compress)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.RustHeap (allocFailedEvent)
open CryptoVerification.SignalSession
  (Address ArgvFitsInitialStack CliHooks CliPqxdhInputs
   CliRun CliSpecPqxdh CliSpecPqxdhNoMatch
   CliSpecPqxdhNoMatchOrExcusedAbort CliSpecPqxdhOrExcusedAbort Cmd Inputs Outcome
   OutcomeMatchesModelExceptPath OutcomeOrExcusedAbort PqParty PqSessionMatches
   PqxdhPartyInSpecDomain PrintableAsciiArg PublicBundle bundleDir cliExternsPlaced
   cliProcessInputs coinsFile dirsFold encodeDir fileCapBytes filesFold filesOf files_eq_entries
   initFsState_entries le32 loadState_status_running loadable_pqInitInputs loadable_pqRecvInputs
   loadable_pqSendInputs maxPlaintextBytes observe outcomeOf outcomeOf_eq_aborted
   outcomeOf_eq_exited partyAddress pqInitInputs pqInitModel pqInputs pqRecvInputs
   pqRecvPrekeyModel pqRecvWhisperModel pqSendInputs pqSendModel pqxdhExpectedOutcome
   publicBundleOf realCrypto realPqxdhPrims sessionFile stdinCapBytes stdioPaths)
open CryptoVerification.SignalSession.Placed (cliTokenPatchPlaced)
open LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced
  (CliPqxdhElfCorrectPlaced CliReachesOOMPlaced CliReachesSampleNttStuckPlaced)
open LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced.Placed
  (CliElfCodeMatchesPlaced cliProgPlacedSig cliRunPlacedSig)
open CryptoVerification.SignalSession.Cli
  (CliInputsOk CoinsReadable CommitOk ElfStaticOk InputsLoadable IsSendOverCap IsStdinOverCap
   MainCaseB2 MainResult RunAnswer cliInputs fsView_congr fsView_writeAll_initFsState
   loadState_fs_trace signExtend_ofNat_small)
open CryptoVerification.SignalSession.Cli.MainHops (CallV cmdTag parseArgs parseArgs_cmd)
open LibsignalBinary.Heap (BudgetLimits)
open LibsignalBinary.Heap.Fine
  (FineBudget fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
  (CliElfExtB2NeedLocksAssumptions2
   MainOkCliExtOverB2NeedLocksPlacedAt MainOkCliExtPqB2NeedLocksPlacedAt
   MuslHarnessFineNeedLocksGuardedPerInput b2MainEntryPreFine b2MainSpecTightNeedLocksFineAt
   cliBudgetLimits cliRunPlacedSig_eq_on_input_of_progEq2 exit_frame_needLocks_n
   outcome_of_main_strict_b2_needLocks_guarded_perInput_at)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3ExternNoAllocFail
  (ExternPreservesNoAllocFailed externPreservesNoAllocFailed_cliExternsPlaced
   externPreservesNoAllocFailed_none steps_preserves_no_allocFailed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
  (CliElfTokenCellsPlacedAt cliProgExtPlacedAt cliProgExtPlacedSigAt
   cliProgExtPlacedSigAt_cliExternsPlaced_eq cliRunExtOnInputsSigAt cliRunExtOnInputsSigAt_eq_some
   cliRunsToExtOnInputsAt_of_outcomeOf_observed cliRunsToExtOnInputsAt_of_outcomeOf_usage
   cliStaticsPlacedAt elfStaticOk_patchElfTokensPlacedAt loadState_patchElfTokensPlacedAt
   patchElfTokensPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.PlacedOomRecovery2
  (CliPqxdhElfCorrectStrictPlaced2Aes cliPqxdhElfCorrectPlaced_of_strict2Aes
   outcomeOrExcusedAbort_of_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG
  (Block617TransferFixedHypG withEntryGuard)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2EntryGuard (F3C2EntryGuard)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost (keepMemcpyBlk20)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost (keepMemsetBlk21)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemFirstStopTransfer
  (RealNeverViolatesSampleNtt realNeverViolatesSampleNtt_of_not_cliReachesSampleNttStuckPlaced
   steps_cliProgPlacedSig_of_running)

/-- Combined Block-`617` entry guard pairing `F3C2EntryGuard` with `SampleNTT` non-violation
(`RealNeverViolatesSampleNtt mpl (cliExternsPlaced mmpl)`). -/
abbrev F3SampleNttEntryGuard (mpl mmpl : Obj.MultiPlacement) (s0 : State) : Prop :=
  F3C2EntryGuard mpl mmpl s0 ∧ RealNeverViolatesSampleNtt mpl (cliExternsPlaced mmpl) s0

/-- Combined `W`-independent Block-`617` entry-`lr`-false predicate covering both `memset` (`blk21`)
and `memcpy` (`blk20`), `rfl`-definitionally equal to
`ElfMemsetEntryGuard.F3MemsetMemcpyEntryLrFalse` while staying `CliElf`-free. -/
abbrev F3MemsetMemcpyEntryLrFalse (mmpl : Obj.MultiPlacement) (s0 : State) : Prop :=
  keepMemsetBlk21 mmpl (s0.readReg64 .lr) = false ∧
  keepMemcpyBlk20 mmpl (s0.readReg64 .lr) = false

/-! ## 0. Import-Light PQXDH Input Side-Condition Helpers -/

private theorem coinsReadable_of_last (i : Inputs) (prefixFiles : List (String × List (BitVec 8)))
    (coins : List (BitVec 8)) (hfiles : i.files = prefixFiles ++ [(coinsFile, coins)])
    (hcap : coins.length ≤ fileCapBytes) :
    CoinsReadable i := by
  unfold CoinsReadable
  rw [files_eq_entries]
  have hne : (normalizePath "coins").isEmpty = false := by rfl_kernel
  have hnsB : (stdioPaths.map normalizePath).contains (normalizePath "coins") = false := by
    rfl_kernel
  have hns : normalizePath "coins" ∉ stdioPaths.map normalizePath := fun hm => by
    rw [← List.contains_iff_mem] at hm
    exact Bool.noConfusion (hnsB.symm.trans hm)
  rw [hne, initFsState_entries (cliInputs i) (normalizePath "coins") hns]
  change (filesFold i.files (dirsFold i.dirs {})).entries (normalizePath "coins") ≠ some .dir ∧
    ∀ bs, (filesFold i.files (dirsFold i.dirs {})).entries (normalizePath "coins") = some (.file bs) →
      bs.length ≤ fileCapBytes
  rw [hfiles]
  unfold filesFold
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, FsState.setFile, FsState.setEntry, coinsFile]
  refine ⟨by simp, fun bs h => ?_⟩
  simp at h
  subst h
  exact hcap

private theorem coinsReadable_pqInitInputs (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    CoinsReadable (pqInitInputs W st b t) :=
  coinsReadable_of_last _ (encodeDir W st ++ (publicBundleOf b).files bundleDir) t.toList
    (by simp [pqInitInputs, pqInputs, List.append_assoc])
    (by simp [List.Vector.toList_length, initiateTapeLen, fileCapBytes])

private theorem coinsReadable_pqSendInputs (W : PEParams) (st : PqParty) (m : List (BitVec 8))
    (r : List.Vector (BitVec 8) 64) :
    CoinsReadable (pqSendInputs W st m r) :=
  coinsReadable_of_last _ (encodeDir W st) r.toList
    (by simp [pqSendInputs, pqInputs])
    (by simp [List.Vector.toList_length, fileCapBytes])

private theorem coinsReadable_pqRecvInputs (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) :
    CoinsReadable (pqRecvInputs W st c rc) :=
  coinsReadable_of_last _ (encodeDir W st) (keyToBytes32 rc)
    (by simp [pqRecvInputs, pqInputs])
    (by simp [keyToBytes32, fileCapBytes])

private theorem inputsLoadable_pqInitInputs (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) (hst : PqxdhPartyInSpecDomain W st) :
    InputsLoadable (pqInitInputs W st b t) := by
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

private theorem inputsLoadable_pqSendInputs (W : PEParams) (st : PqParty) (m : List (BitVec 8))
    (r : List.Vector (BitVec 8) 64) (hst : PqxdhPartyInSpecDomain W st) :
    InputsLoadable (pqSendInputs W st m r) := by
  refine ⟨(loadable_pqSendInputs W st m r).1, fun f hf =>
    ⟨(loadable_pqSendInputs W st m r).2 f hf, ?_⟩⟩
  simp only [pqSendInputs, pqInputs, List.append_nil, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hf
  rcases hf with h | rfl
  · have hlt := hst.2.1 f h; unfold MAX_LFS_FILESIZE; omega
  · simp [MAX_LFS_FILESIZE]

private theorem inputsLoadable_pqRecvInputs (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) (hst : PqxdhPartyInSpecDomain W st) :
    InputsLoadable (pqRecvInputs W st c rc) := by
  refine ⟨(loadable_pqRecvInputs W st c rc).1, fun f hf =>
    ⟨(loadable_pqRecvInputs W st c rc).2 f hf, ?_⟩⟩
  simp only [pqRecvInputs, pqInputs, List.append_nil, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hf
  rcases hf with h | rfl
  · have hlt := hst.2.1 f h; unfold MAX_LFS_FILESIZE; omega
  · simp [keyToBytes32, MAX_LFS_FILESIZE]

private theorem partyAddress_text_toList (P : Party) :
    (partyAddress P).text.toList = (partyAddressName P).toList ++ ".".toList ++ ['1'] := by
  have ht1 : toString (1 : Nat) = String.singleton (Nat.digitChar 1) := Nat.repr_of_lt (by omega)
  have hd1 : Nat.digitChar 1 = '1' := Nat.digitChar_eq_one.mpr rfl
  simp [partyAddress, Address.text, ht1, hd1, String.toList_append]

private theorem partyAddress_text_printable (P : Party) :
    PrintableAsciiArg (partyAddress P).text := by
  have ht1 : toString (1 : Nat) = String.singleton (Nat.digitChar 1) := Nat.repr_of_lt (by omega)
  refine ⟨?_, ?_⟩
  · intro h
    have hl := congrArg String.utf8ByteSize h
    simp [partyAddress, Address.text, ht1, String.utf8ByteSize_append] at hl
  · intro c hc
    rw [partyAddress_text_toList] at hc
    cases P <;> revert c hc <;> decide

private theorem partyAddress_text_length (P : Party) :
    (partyAddress P).text.length = 38 := by
  rw [← String.length_toList, partyAddress_text_toList]
  cases P <;> decide

private theorem cliInputsOk_pqInitInputs (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    CliInputsOk (pqInitInputs W st b t) := by
  refine ⟨?_, ?_⟩
  · intro a ha
    simp only [pqInitInputs, pqInputs, Cmd.argv, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · unfold PrintableAsciiArg; decide
    · exact partyAddress_text_printable st.party.other
    · unfold PrintableAsciiArg bundleDir; decide
  · unfold ArgvFitsInitialStack pqInitInputs pqInputs Cmd.argv
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      partyAddress_text_length]
    unfold bundleDir
    decide

private theorem cliInputsOk_pqSendInputs (W : PEParams) (st : PqParty) (m : List (BitVec 8))
    (r : List.Vector (BitVec 8) 64) :
    CliInputsOk (pqSendInputs W st m r) := by
  refine ⟨?_, ?_⟩
  · intro a ha
    simp only [pqSendInputs, pqInputs, Cmd.argv, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · unfold PrintableAsciiArg; decide
    · exact partyAddress_text_printable st.party.other
  · unfold ArgvFitsInitialStack pqSendInputs pqInputs Cmd.argv
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      partyAddress_text_length]
    decide

private theorem cliInputsOk_pqRecvInputs (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) :
    CliInputsOk (pqRecvInputs W st c rc) := by
  refine ⟨?_, ?_⟩
  · intro a ha
    simp only [pqRecvInputs, pqInputs, Cmd.argv, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · unfold PrintableAsciiArg; decide
    · exact partyAddress_text_printable st.party.other
  · unfold ArgvFitsInitialStack pqRecvInputs pqInputs Cmd.argv
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      partyAddress_text_length]
    decide

private theorem not_isSendOverCap_of_stdin_le {i : Inputs} (h : i.stdin.length ≤ 1_000_000) :
    ¬ IsSendOverCap i :=
  fun ⟨_, hgt⟩ => Nat.not_lt.mpr h hgt

private theorem not_isStdinOverCap_of_stdin_le {i : Inputs} (h : i.stdin.length ≤ stdinCapBytes) :
    ¬ IsStdinOverCap i :=
  fun ⟨_, hgt⟩ => Nat.not_lt.mpr h hgt

private theorem isSendOverCap_pqSendInputs (W : PEParams) (st : PqParty) (m : List (BitVec 8))
    (r : List.Vector (BitVec 8) 64) (h : 1_000_000 < m.length) :
    IsSendOverCap (pqSendInputs W st m r) := by
  refine ⟨?_, h⟩
  obtain ⟨c, hc, htag⟩ := parseArgs_cmd (.send (partyAddress st.party.other)) rfl
  cases c <;> simp [CallV.tag, cmdTag] at htag
  rename_i peer
  exact ⟨peer, hc⟩

private theorem not_isSendOverCap_pqInitInputs (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    ¬ IsSendOverCap (pqInitInputs W st b t) := by
  rintro ⟨_, hgt⟩
  simp [pqInitInputs, pqInputs] at hgt

private theorem not_isSendOverCap_pqRecvInputs (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) :
    ¬ IsSendOverCap (pqRecvInputs W st c rc) := by
  rintro ⟨⟨peer, hp⟩, -⟩
  obtain ⟨v, hv, htag⟩ := parseArgs_cmd (.recv (partyAddress st.party.other)) rfl
  change parseArgs uuidTryParse
    ((Cmd.recv (partyAddress st.party.other)).argv.map bytesOfString) = some (.send peer) at hp
  rw [hp] at hv
  injection hv with heq
  subst heq
  simp [CallV.tag, cmdTag] at htag

private theorem isStdinOverCap_pqSendInputs (W : PEParams) (st : PqParty) (m : List (BitVec 8))
    (r : List.Vector (BitVec 8) 64) (h : stdinCapBytes < m.length) :
    IsStdinOverCap (pqSendInputs W st m r) := by
  refine ⟨?_, h⟩
  obtain ⟨c, hc, htag⟩ := parseArgs_cmd (.send (partyAddress st.party.other)) rfl
  exact ⟨c, hc, by rw [htag]; simp [cmdTag]⟩

private theorem isStdinOverCap_pqRecvInputs (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) (h : stdinCapBytes < c.length) :
    IsStdinOverCap (pqRecvInputs W st c rc) := by
  refine ⟨?_, h⟩
  obtain ⟨v, hv, htag⟩ := parseArgs_cmd (.recv (partyAddress st.party.other)) rfl
  exact ⟨v, hv, by rw [htag]; simp [cmdTag]⟩

private theorem not_isStdinOverCap_pqInitInputs (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    ¬ IsStdinOverCap (pqInitInputs W st b t) :=
  not_isStdinOverCap_of_stdin_le (by simp [pqInitInputs, pqInputs])

/-! ## 1. Guarded Single-Input `NeedLocks` Call Bridges -/

/-- Guarded single-input `NeedLocks` strict `stdinOverCap` bridge to
`cliRunExtOnInputsSigAt`, consuming `MuslHarnessFineNeedLocksGuardedPerInput` via
`CliStrictPlaced2.outcome_of_main_strict_b2_needLocks_guarded_perInput_at`. -/
theorem cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_stdinOverCap
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {idx : Nat}
    {inputsOf : Inputs → ProcessInputs} {exitStk : Nat} {libcAddr : BitVec 64}
    {elf : ElfImage} {W : CliHooks}
    {CodeOk : Memory → Prop} {lim : BudgetLimits} {st : FineBudget} {stk : Nat}
    {Statics : SepProp} {EntryGuard : State → Prop} {Run : Inputs → RunAnswer → Prop}
    (hext : ExternPreservesNoAllocFailed (ext W))
    (hE : ElfStaticOk elf)
    (htok : CliElfTokenCellsPlacedAt mpl elf)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hCode : ∀ m, CodeOk m → (cliProgExtPlacedAt mpl ext idx W).CodeLoaded m)
    (hH : MuslHarnessFineNeedLocksGuardedPerInput exitStk libcAddr (patchElfTokensPlacedAt mpl elf)
      (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx) inputsOf
      mmpl lim st stk CodeOk Statics EntryGuard)
    (hmain : ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx)
        (withEntryGuard EntryGuard
          (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart)
            lim st stk Statics Run inputsOf)))
    (hstk : exitStk ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    {i : Inputs}
    (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hstin : IsStdinOverCap i) :
    cliRunExtOnInputsSigAt mpl ext idx inputsOf elf W i =
      some (.exited 2 [] (filesOf i.files)) := by
  have hbrk : (patchElfTokensPlacedAt mpl elf).brkStart = elf.brkStart := rfl
  obtain ⟨res, hout, hresObs⟩ :=
    outcome_of_main_strict_b2_needLocks_guarded_perInput_at rfl externPreservesNoAllocFailed_none
      hext (elfStaticOk_patchElfTokensPlacedAt hE) hfs_eq hCode hH
      (fun γ tp => by simpa only [withEntryGuard, hbrk] using hmain γ tp)
      hstk hstk' hi hl (MainCaseB2.stdinOverCap hstin)
  have hruns := cliRunsToExtOnInputsAt_of_outcomeOf_usage
    (loadState_patchElfTokensPlacedAt hE htok (inputsOf i)) hout hresObs
  exact cliRunExtOnInputsSigAt_eq_some hruns

/-- Guarded single-input `NeedLocks` strict `sendOverCap` bridge to
`cliRunExtOnInputsSigAt`. -/
theorem cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_sendOverCap
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {idx : Nat}
    {inputsOf : Inputs → ProcessInputs} {exitStk : Nat} {libcAddr : BitVec 64}
    {elf : ElfImage} {W : CliHooks}
    {CodeOk : Memory → Prop} {lim : BudgetLimits} {st : FineBudget} {stk : Nat}
    {Statics : SepProp} {EntryGuard : State → Prop} {Run : Inputs → RunAnswer → Prop}
    (hext : ExternPreservesNoAllocFailed (ext W))
    (hE : ElfStaticOk elf)
    (htok : CliElfTokenCellsPlacedAt mpl elf)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hCode : ∀ m, CodeOk m → (cliProgExtPlacedAt mpl ext idx W).CodeLoaded m)
    (hH : MuslHarnessFineNeedLocksGuardedPerInput exitStk libcAddr (patchElfTokensPlacedAt mpl elf)
      (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx) inputsOf
      mmpl lim st stk CodeOk Statics EntryGuard)
    (hmain : ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx)
        (withEntryGuard EntryGuard
          (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart)
            lim st stk Statics Run inputsOf)))
    (hstk : exitStk ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    {i : Inputs}
    (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hover : IsSendOverCap i) (hnstin : ¬ IsStdinOverCap i)
    (hcoins : CoinsReadable i) :
    cliRunExtOnInputsSigAt mpl ext idx inputsOf elf W i =
      some (.exited 1 [] (filesOf i.files)) := by
  have hbrk : (patchElfTokensPlacedAt mpl elf).brkStart = elf.brkStart := rfl
  obtain ⟨res, hout, hresObs⟩ :=
    outcome_of_main_strict_b2_needLocks_guarded_perInput_at rfl externPreservesNoAllocFailed_none
      hext (elfStaticOk_patchElfTokensPlacedAt hE) hfs_eq hCode hH
      (fun γ tp => by simpa only [withEntryGuard, hbrk] using hmain γ tp)
      hstk hstk' hi hl (MainCaseB2.sendOverCap hover hnstin hcoins)
  have hruns := cliRunsToExtOnInputsAt_of_outcomeOf_observed (a := some none)
    (loadState_patchElfTokensPlacedAt hE htok (inputsOf i)) hout hresObs
  exact cliRunExtOnInputsSigAt_eq_some hruns

/-- Guarded single-input `NeedLocks` strict call bridge to `cliRunExtOnInputsSigAt`. -/
theorem cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_call_obs
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {idx : Nat}
    {inputsOf : Inputs → ProcessInputs} {exitStk : Nat} {libcAddr : BitVec 64}
    {elf : ElfImage} {W : CliHooks}
    {CodeOk : Memory → Prop} {lim : BudgetLimits} {st : FineBudget} {stk : Nat}
    {Statics : SepProp} {EntryGuard : State → Prop} {Run : Inputs → RunAnswer → Prop}
    (hext : ExternPreservesNoAllocFailed (ext W))
    (hE : ElfStaticOk elf)
    (htok : CliElfTokenCellsPlacedAt mpl elf)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hCode : ∀ m, CodeOk m → (cliProgExtPlacedAt mpl ext idx W).CodeLoaded m)
    (hH : MuslHarnessFineNeedLocksGuardedPerInput exitStk libcAddr (patchElfTokensPlacedAt mpl elf)
      (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx) inputsOf
      mmpl lim st stk CodeOk Statics EntryGuard)
    (hmain : ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx)
        (withEntryGuard EntryGuard
          (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart)
            lim st stk Statics Run inputsOf)))
    (hstk : exitStk ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    {i : Inputs} {a : RunAnswer} {o : Outcome}
    (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hrun : Run i a) (hnover : ¬ IsSendOverCap i) (hnstin : ¬ IsStdinOverCap i)
    (hobs : observe i.files a = o)
    (hcoins : CoinsReadable i) (hcommit : CommitOk i (MainResult.ofAnswer a)) :
    cliRunExtOnInputsSigAt mpl ext idx inputsOf elf W i = some o := by
  have hbrk : (patchElfTokensPlacedAt mpl elf).brkStart = elf.brkStart := rfl
  obtain ⟨res, hout, hresObs⟩ :=
    outcome_of_main_strict_b2_needLocks_guarded_perInput_at rfl externPreservesNoAllocFailed_none
      hext (elfStaticOk_patchElfTokensPlacedAt hE) hfs_eq hCode hH
      (fun γ tp => by simpa only [withEntryGuard, hbrk] using hmain γ tp)
      hstk hstk' hi hl (MainCaseB2.call hrun hnover hnstin hcoins hcommit)
  have hruns := cliRunsToExtOnInputsAt_of_outcomeOf_observed
    (loadState_patchElfTokensPlacedAt hE htok (inputsOf i)) hout hresObs
  rw [hobs] at hruns
  exact cliRunExtOnInputsSigAt_eq_some hruns

/-- Predicate-valued companion of `cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_call_obs`. -/
theorem cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_call_pred
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {idx : Nat}
    {inputsOf : Inputs → ProcessInputs} {exitStk : Nat} {libcAddr : BitVec 64}
    {elf : ElfImage} {W : CliHooks}
    {CodeOk : Memory → Prop} {lim : BudgetLimits} {st : FineBudget} {stk : Nat}
    {Statics : SepProp} {EntryGuard : State → Prop} {Run : Inputs → RunAnswer → Prop}
    {P : Outcome → Prop}
    (hext : ExternPreservesNoAllocFailed (ext W))
    (hE : ElfStaticOk elf)
    (htok : CliElfTokenCellsPlacedAt mpl elf)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hCode : ∀ m, CodeOk m → (cliProgExtPlacedAt mpl ext idx W).CodeLoaded m)
    (hH : MuslHarnessFineNeedLocksGuardedPerInput exitStk libcAddr (patchElfTokensPlacedAt mpl elf)
      (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx) inputsOf
      mmpl lim st stk CodeOk Statics EntryGuard)
    (hmain : ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx)
        (withEntryGuard EntryGuard
          (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart)
            lim st stk Statics Run inputsOf)))
    (hstk : exitStk ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    {i : Inputs} {a : RunAnswer}
    (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hrun : Run i a) (hnover : ¬ IsSendOverCap i) (hnstin : ¬ IsStdinOverCap i)
    (hp : P (observe i.files a))
    (hcoins : CoinsReadable i) (hcommit : CommitOk i (MainResult.ofAnswer a)) :
    ∃ o, cliRunExtOnInputsSigAt mpl ext idx inputsOf elf W i = some o ∧ P o :=
  ⟨observe i.files a,
    cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_call_obs hext hE htok hfs_eq hCode hH
      hmain hstk hstk' hi hl hrun hnover hnstin rfl hcoins hcommit, hp⟩

/-! ## 2. Guarded `MainOkCliExt*B2NeedLocksPlacedAtG` Predicates and Transfer Bridges -/

/-- Guard-parametric `NeedLocks` + `argvAtRO` 5-clause PQXDH `main` specification
(real-AES guarded). -/
@[expose] def MainOkCliExtPqB2NeedLocksPlacedAtG
    (mpl mmpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State))
    (mainIdx : Nat) (inputsOf : Inputs → ProcessInputs)
    (EntryGuard : State → Prop) (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) (lim : BudgetLimits) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    W.C.E = CryptoGames.AES256.aes256Enc →
    W.C.D = CryptoGames.AES256.aes256Dec →
    W.C.X = CryptoGames.RFC7748.x25519Ref →
    W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
    W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
    W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
    W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
    W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → RunAnswer → Prop,
      (∀ (γ : GhostName) (tp : BitVec 64),
        subroutine_ok (cliProgExtPlacedAt mpl ext mainIdx W) (mpl.base mainIdx)
          (withEntryGuard EntryGuard
            (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
              (fineHookRustCliAllocBudget γ mmpl tp brkStart)
              lim fineCostModel.init stk (cliStaticsPlacedAt mpl) Run inputsOf))) ∧
      ∀ p : PqParty, PqxdhPartyInSpecDomain WP p →
        (∀ (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen),
          p.session = none →
          ∃ a, Run (pqInitInputs WP p b t) a ∧
            observe (pqInitInputs WP p b t).files a =
              pqxdhExpectedOutcome WP (pqInitInputs WP p b t) (pqInitModel X WP p b t) ∧
            CommitOk (pqInitInputs WP p b t) (MainResult.ofAnswer a)) ∧
        (∀ (m : List (BitVec 8)) (r : List.Vector (BitVec 8) 64), m.length < 2 ^ 32 →
          ∃ a, Run (pqSendInputs WP p m r) a ∧
            observe (pqSendInputs WP p m r).files a =
              pqxdhExpectedOutcome WP (pqSendInputs WP p m r) (pqSendModel WP p m r.toList) ∧
            CommitOk (pqSendInputs WP p m r) (MainResult.ofAnswer a)) ∧
        (∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
          ∃ a, Run (pqRecvInputs WP p (wireWhisper :: c) rc) a ∧
            observe (pqRecvInputs WP p (wireWhisper :: c) rc).files a =
              pqxdhExpectedOutcome WP (pqRecvInputs WP p (wireWhisper :: c) rc)
                (pqRecvWhisperModel WP p c rc) ∧
            CommitOk (pqRecvInputs WP p (wireWhisper :: c) rc) (MainResult.ofAnswer a)) ∧
        (∀ (m : PreKeyMessageFields) (rc : BitVec 256), m.inner.length + 2048 < 2 ^ 32 →
          (∀ x g, p.session = some (x, g) → PqSessionMatches x g m) →
          ∃ a, Run (pqRecvInputs WP p (wirePrekey :: m.bytes) rc) a ∧
            observe (pqRecvInputs WP p (wirePrekey :: m.bytes) rc).files a =
              pqxdhExpectedOutcome WP (pqRecvInputs WP p (wirePrekey :: m.bytes) rc)
                (pqRecvPrekeyModel X WP p m rc) ∧
            CommitOk (pqRecvInputs WP p (wirePrekey :: m.bytes) rc) (MainResult.ofAnswer a)) ∧
        (∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
          c.head? ≠ some wireWhisper → c.head? ≠ some wirePrekey →
          ∃ a, Run (pqRecvInputs WP p c rc) a ∧
            observe (pqRecvInputs WP p c rc).files a =
              .exited 1 [] (filesOf (pqRecvInputs WP p c rc).files) ∧
            CommitOk (pqRecvInputs WP p c rc) (MainResult.ofAnswer a))

/-- Guard-parametric `NeedLocks` + `argvAtRO` `NoMatch` `main` specification
(real-AES guarded). -/
@[expose] def MainOkCliExtOverB2NeedLocksPlacedAtG
    (mpl mmpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State))
    (mainIdx : Nat) (inputsOf : Inputs → ProcessInputs)
    (EntryGuard : State → Prop) (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) (lim : BudgetLimits) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    W.C.E = CryptoGames.AES256.aes256Enc →
    W.C.D = CryptoGames.AES256.aes256Dec →
    W.C.X = CryptoGames.RFC7748.x25519Ref →
    W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
    W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
    W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
    W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
    W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → RunAnswer → Prop,
      (∀ (γ : GhostName) (tp : BitVec 64),
        subroutine_ok (cliProgExtPlacedAt mpl ext mainIdx W) (mpl.base mainIdx)
          (withEntryGuard EntryGuard
            (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
              (fineHookRustCliAllocBudget γ mmpl tp brkStart)
              lim fineCostModel.init stk (cliStaticsPlacedAt mpl) Run inputsOf))) ∧
      ∀ st : PqParty, PqxdhPartyInSpecDomain WP st →
        ∀ (x : RecordExtras) (g : GhostState Bytes), st.session = some (x, g) →
        ∀ (m : PreKeyMessageFields) (rc : BitVec 256), m.inner.length + 2048 < 2 ^ 32 →
          ¬ PqSessionMatches x g m →
          ∃ a, Run (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) a ∧
            OutcomeMatchesModelExceptPath WP (pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
              (sessionFile (partyAddress st.party.other))
              (pqRecvPrekeyModel X WP { st with session := none } m rc)
              (observe (pqRecvInputs WP st (wirePrekey :: m.bytes) rc).files a) ∧
            CommitOk (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) (MainResult.ofAnswer a)

/-- Entry-guard-free ghost counterpart of `MainOkCliExtPqB2NeedLocksPlacedAtG` carrying
`W.C.E = CryptoGames.AES256.aes256Enc` and `W.C.D = CryptoGames.AES256.aes256Dec`. -/
@[expose] def MainOkCliExtPqB2NeedLocksPlacedAtAes
    (mpl mmpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State))
    (mainIdx : Nat) (inputsOf : Inputs → ProcessInputs)
    (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) (lim : BudgetLimits) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    W.C.E = CryptoGames.AES256.aes256Enc →
    W.C.D = CryptoGames.AES256.aes256Dec →
    W.C.X = CryptoGames.RFC7748.x25519Ref →
    W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
    W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
    W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
    W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
    W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → RunAnswer → Prop,
      (∀ (γ : GhostName) (tp : BitVec 64),
        subroutine_ok (cliProgExtPlacedAt mpl ext mainIdx W) (mpl.base mainIdx)
          (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart)
            lim fineCostModel.init stk (cliStaticsPlacedAt mpl) Run inputsOf)) ∧
      ∀ p : PqParty, PqxdhPartyInSpecDomain WP p →
        (∀ (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen),
          p.session = none →
          ∃ a, Run (pqInitInputs WP p b t) a ∧
            observe (pqInitInputs WP p b t).files a =
              pqxdhExpectedOutcome WP (pqInitInputs WP p b t) (pqInitModel X WP p b t) ∧
            CommitOk (pqInitInputs WP p b t) (MainResult.ofAnswer a)) ∧
        (∀ (m : List (BitVec 8)) (r : List.Vector (BitVec 8) 64), m.length < 2 ^ 32 →
          ∃ a, Run (pqSendInputs WP p m r) a ∧
            observe (pqSendInputs WP p m r).files a =
              pqxdhExpectedOutcome WP (pqSendInputs WP p m r) (pqSendModel WP p m r.toList) ∧
            CommitOk (pqSendInputs WP p m r) (MainResult.ofAnswer a)) ∧
        (∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
          ∃ a, Run (pqRecvInputs WP p (wireWhisper :: c) rc) a ∧
            observe (pqRecvInputs WP p (wireWhisper :: c) rc).files a =
              pqxdhExpectedOutcome WP (pqRecvInputs WP p (wireWhisper :: c) rc)
                (pqRecvWhisperModel WP p c rc) ∧
            CommitOk (pqRecvInputs WP p (wireWhisper :: c) rc) (MainResult.ofAnswer a)) ∧
        (∀ (m : PreKeyMessageFields) (rc : BitVec 256), m.inner.length + 2048 < 2 ^ 32 →
          (∀ x g, p.session = some (x, g) → PqSessionMatches x g m) →
          ∃ a, Run (pqRecvInputs WP p (wirePrekey :: m.bytes) rc) a ∧
            observe (pqRecvInputs WP p (wirePrekey :: m.bytes) rc).files a =
              pqxdhExpectedOutcome WP (pqRecvInputs WP p (wirePrekey :: m.bytes) rc)
                (pqRecvPrekeyModel X WP p m rc) ∧
            CommitOk (pqRecvInputs WP p (wirePrekey :: m.bytes) rc) (MainResult.ofAnswer a)) ∧
        (∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
          c.head? ≠ some wireWhisper → c.head? ≠ some wirePrekey →
          ∃ a, Run (pqRecvInputs WP p c rc) a ∧
            observe (pqRecvInputs WP p c rc).files a =
              .exited 1 [] (filesOf (pqRecvInputs WP p c rc).files) ∧
            CommitOk (pqRecvInputs WP p c rc) (MainResult.ofAnswer a))

/-- Entry-guard-free ghost counterpart of `MainOkCliExtOverB2NeedLocksPlacedAtG` carrying
`W.C.E = CryptoGames.AES256.aes256Enc` and `W.C.D = CryptoGames.AES256.aes256Dec`. -/
@[expose] def MainOkCliExtOverB2NeedLocksPlacedAtAes
    (mpl mmpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State))
    (mainIdx : Nat) (inputsOf : Inputs → ProcessInputs)
    (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) (lim : BudgetLimits) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    W.C.E = CryptoGames.AES256.aes256Enc →
    W.C.D = CryptoGames.AES256.aes256Dec →
    W.C.X = CryptoGames.RFC7748.x25519Ref →
    W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
    W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
    W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
    W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
    W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → RunAnswer → Prop,
      (∀ (γ : GhostName) (tp : BitVec 64),
        subroutine_ok (cliProgExtPlacedAt mpl ext mainIdx W) (mpl.base mainIdx)
          (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart)
            lim fineCostModel.init stk (cliStaticsPlacedAt mpl) Run inputsOf)) ∧
      ∀ st : PqParty, PqxdhPartyInSpecDomain WP st →
        ∀ (x : RecordExtras) (g : GhostState Bytes), st.session = some (x, g) →
        ∀ (m : PreKeyMessageFields) (rc : BitVec 256), m.inner.length + 2048 < 2 ^ 32 →
          ¬ PqSessionMatches x g m →
          ∃ a, Run (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) a ∧
            OutcomeMatchesModelExceptPath WP (pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
              (sessionFile (partyAddress st.party.other))
              (pqRecvPrekeyModel X WP { st with session := none } m rc)
              (observe (pqRecvInputs WP st (wirePrekey :: m.bytes) rc).files a) ∧
            CommitOk (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) (MainResult.ofAnswer a)

/-- Specialization of `MainOkCliExtPqB2NeedLocksPlacedAtG` at `ext := cliExternsPlaced mmpl`,
`mainIdx := 617`, `inputsOf := cliProcessInputs`, `EntryGuard := F3SampleNttEntryGuard mpl mmpl`,
and `lim := cliBudgetLimits`. -/
abbrev MainOkCliF3PqB2NeedLocksPlacedAtG
    (mpl mmpl : Obj.MultiPlacement) (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) : Prop :=
  MainOkCliExtPqB2NeedLocksPlacedAtG mpl mmpl (cliExternsPlaced mmpl) 617 cliProcessInputs
    (F3SampleNttEntryGuard mpl mmpl) CodeOk libcAddr brkStart stk cliBudgetLimits

/-- Specialization of `MainOkCliExtOverB2NeedLocksPlacedAtG` at `ext := cliExternsPlaced mmpl`,
`mainIdx := 617`, `inputsOf := cliProcessInputs`, `EntryGuard := F3SampleNttEntryGuard mpl mmpl`,
and `lim := cliBudgetLimits`. -/
abbrev MainOkCliF3OverB2NeedLocksPlacedAtG
    (mpl mmpl : Obj.MultiPlacement) (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) : Prop :=
  MainOkCliExtOverB2NeedLocksPlacedAtG mpl mmpl (cliExternsPlaced mmpl) 617 cliProcessInputs
    (F3SampleNttEntryGuard mpl mmpl) CodeOk libcAddr brkStart stk cliBudgetLimits

/-- Lift an unguarded ghost `MainOkCliExtPqB2NeedLocksPlacedAt` witness across
`Block617TransferFixedHypG` at `F3SampleNttEntryGuard mpl mmpl`. -/
theorem mainOkCliF3PqG_of_block617TransferFixedG
    {mpl mmpl : Obj.MultiPlacement}
    {EG : CliHooks → String → Option (State → State)}
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (hTr : Block617TransferFixedHypG mpl mmpl EG (cliExternsPlaced mmpl)
      (F3SampleNttEntryGuard mpl mmpl) CodeOk_ghost CodeOk_real libcAddr brkStart stk)
    (hGhost : MainOkCliExtPqB2NeedLocksPlacedAt mpl mmpl EG 617 cliProcessInputs
      CodeOk_ghost libcAddr brkStart stk cliBudgetLimits) :
    MainOkCliF3PqB2NeedLocksPlacedAtG mpl mmpl CodeOk_real libcAddr brkStart stk := by
  intro hDropNz X W _ _ _ _ _ _ _ _
  obtain ⟨Run, hmainW, hclauses⟩ := hGhost hDropNz X W
  exact ⟨Run, hTr W Run hmainW, hclauses⟩

/-- Lift a real-AES ghost `MainOkCliExtPqB2NeedLocksPlacedAtAes` witness across pointwise
`Block617TransferFixedHypG` at `F3SampleNttEntryGuard mpl mmpl`. -/
theorem mainOkCliF3PqG_of_block617TransferFixedGAes
    {mpl mmpl : Obj.MultiPlacement}
    {EG : CliHooks → String → Option (State → State)}
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (hTr : ∀ W : CliHooks,
      W.C.E = CryptoGames.AES256.aes256Enc →
      W.C.D = CryptoGames.AES256.aes256Dec →
      W.C.X = CryptoGames.RFC7748.x25519Ref →
      W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
      W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
      W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
      W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
      W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
      ∀ (Run : Inputs → RunAnswer → Prop),
        (∀ (γ : GhostName) (tp : BitVec 64),
          subroutine_ok (cliProgExtPlacedAt mpl EG 617 W) (mpl.base 617)
            (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk_ghost
              (fineHookRustCliAllocBudget γ mmpl tp brkStart)
              cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl)
              Run cliProcessInputs)) →
        (∀ (γ : GhostName) (tp : BitVec 64),
          subroutine_ok (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (mpl.base 617)
            (withEntryGuard (F3SampleNttEntryGuard mpl mmpl)
              (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk_real
                (fineHookRustCliAllocBudget γ mmpl tp brkStart)
                cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl)
                Run cliProcessInputs))))
    (hGhost : MainOkCliExtPqB2NeedLocksPlacedAtAes mpl mmpl EG 617 cliProcessInputs
      CodeOk_ghost libcAddr brkStart stk cliBudgetLimits) :
    MainOkCliF3PqB2NeedLocksPlacedAtG mpl mmpl CodeOk_real libcAddr brkStart stk := by
  intro hDropNz X W hE hD hX hPub hF512 hEnc hDec hK
  obtain ⟨Run, hmainW, hclauses⟩ := hGhost hDropNz X W hE hD hX hPub hF512 hEnc hDec hK
  exact ⟨Run, hTr W hE hD hX hPub hF512 hEnc hDec hK Run hmainW, hclauses⟩

/-- Lift an unguarded ghost `MainOkCliExtOverB2NeedLocksPlacedAt` witness across
`Block617TransferFixedHypG` at `F3SampleNttEntryGuard mpl mmpl`. -/
theorem mainOkCliF3OverG_of_block617TransferFixedG
    {mpl mmpl : Obj.MultiPlacement}
    {EG : CliHooks → String → Option (State → State)}
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (hTr : Block617TransferFixedHypG mpl mmpl EG (cliExternsPlaced mmpl)
      (F3SampleNttEntryGuard mpl mmpl) CodeOk_ghost CodeOk_real libcAddr brkStart stk)
    (hGhost : MainOkCliExtOverB2NeedLocksPlacedAt mpl mmpl EG 617 cliProcessInputs
      CodeOk_ghost libcAddr brkStart stk cliBudgetLimits) :
    MainOkCliF3OverB2NeedLocksPlacedAtG mpl mmpl CodeOk_real libcAddr brkStart stk := by
  intro hDropNz X W _ _ _ _ _ _ _ _
  obtain ⟨Run, hmainW, hclauses⟩ := hGhost hDropNz X W
  exact ⟨Run, hTr W Run hmainW, hclauses⟩

/-- Lift a real-AES ghost `MainOkCliExtOverB2NeedLocksPlacedAtAes` witness across pointwise
`Block617TransferFixedHypG` at `F3SampleNttEntryGuard mpl mmpl`. -/
theorem mainOkCliF3OverG_of_block617TransferFixedGAes
    {mpl mmpl : Obj.MultiPlacement}
    {EG : CliHooks → String → Option (State → State)}
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (hTr : ∀ W : CliHooks,
      W.C.E = CryptoGames.AES256.aes256Enc →
      W.C.D = CryptoGames.AES256.aes256Dec →
      W.C.X = CryptoGames.RFC7748.x25519Ref →
      W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
      W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
      W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
      W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
      W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
      ∀ (Run : Inputs → RunAnswer → Prop),
        (∀ (γ : GhostName) (tp : BitVec 64),
          subroutine_ok (cliProgExtPlacedAt mpl EG 617 W) (mpl.base 617)
            (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk_ghost
              (fineHookRustCliAllocBudget γ mmpl tp brkStart)
              cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl)
              Run cliProcessInputs)) →
        (∀ (γ : GhostName) (tp : BitVec 64),
          subroutine_ok (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (mpl.base 617)
            (withEntryGuard (F3SampleNttEntryGuard mpl mmpl)
              (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk_real
                (fineHookRustCliAllocBudget γ mmpl tp brkStart)
                cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl)
                Run cliProcessInputs))))
    (hGhost : MainOkCliExtOverB2NeedLocksPlacedAtAes mpl mmpl EG 617 cliProcessInputs
      CodeOk_ghost libcAddr brkStart stk cliBudgetLimits) :
    MainOkCliF3OverB2NeedLocksPlacedAtG mpl mmpl CodeOk_real libcAddr brkStart stk := by
  intro hDropNz X W hE hD hX hPub hF512 hEnc hDec hK
  obtain ⟨Run, hmainW, hclauses⟩ := hGhost hDropNz X W hE hD hX hPub hF512 hEnc hDec hK
  exact ⟨Run, hTr W hE hD hX hPub hF512 hEnc hDec hK Run hmainW, hclauses⟩

/-! ## 3. Guarded Strict `CliSpecPqxdh` ∧ `CliSpecPqxdhNoMatch` Composers -/

/-- Entry-guarded counterpart of `CliStrictPlaced2.cliSpecPqxdh_ext_strict_of_b2_needLocks`,
eliminating `EntryGuard` internally via the single-input bridges in Section 1. -/
theorem cliSpecPqxdh_ext_strict_of_b2_needLocks_guarded
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {mainIdx : Nat}
    {inputsOf : Inputs → ProcessInputs} {EntryGuard : State → Prop}
    {exitStk : Nat} {libcAddr : BitVec 64}
    {CodeOk : Memory → Prop} {stk : Nat} {lim : BudgetLimits}
    {elf : ElfImage} {W : CliHooks}
    (hext : ExternPreservesNoAllocFailed (ext W))
    (hE : ElfStaticOk elf)
    (htok : CliElfTokenCellsPlacedAt mpl elf)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hCode : ∀ m, CodeOk m → (cliProgExtPlacedAt mpl ext mainIdx W).CodeLoaded m)
    (hH : MuslHarnessFineNeedLocksGuardedPerInput exitStk libcAddr (patchElfTokensPlacedAt mpl elf)
      (cliProgExtPlacedAt mpl ext mainIdx W) (mpl.base mainIdx) inputsOf
      mmpl lim fineCostModel.init stk CodeOk (cliStaticsPlacedAt mpl) EntryGuard)
    (hstk : exitStk ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    (hDropNz : mpl.base 547 ≠ 0#64)
    (hmain : MainOkCliExtPqB2NeedLocksPlacedAtG mpl mmpl ext mainIdx inputsOf EntryGuard CodeOk
      libcAddr elf.brkStart stk lim)
    (hAesE : W.C.E = CryptoGames.AES256.aes256Enc)
    (hAesD : W.C.D = CryptoGames.AES256.aes256Dec)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (hF512 : W.Q.F512 = CryptoGames.SHA512.sha512CompressState)
    (hEnc : W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec)
    (hDec : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental) :
    ∀ X : UnreachedPqxdhPrimitives,
      CliSpecPqxdh (cliRunExtOnInputsSigAt mpl ext mainIdx inputsOf elf W) X ⟨W.C, W.Q⟩ := by
  intro X p hp
  let WP : PEParams := ⟨W.C, W.Q⟩
  obtain ⟨Run, hmainW, hclauses⟩ := hmain hDropNz X W hAesE hAesD hX hPub hF512 hEnc hDec hK
  obtain ⟨hInit, hSend, hWhisper, hPrekey, hBad⟩ := hclauses p hp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro b t hnone
    obtain ⟨a, hrun, hobs, hcommit⟩ := hInit b t hnone
    exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_call_obs hext hE htok hfs_eq
      hCode hH hmainW hstk hstk'
      (cliInputsOk_pqInitInputs WP p b t) (inputsLoadable_pqInitInputs WP p b t hp)
      hrun (not_isSendOverCap_pqInitInputs WP p b t)
      (not_isStdinOverCap_pqInitInputs WP p b t) hobs
      (coinsReadable_pqInitInputs WP p b t) hcommit
  · intro m r hm
    by_cases hstin : m.length > stdinCapBytes
    · simp only [hstin, ↓reduceIte]
      exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_stdinOverCap hext hE htok hfs_eq
        hCode hH hmainW hstk hstk'
        (cliInputsOk_pqSendInputs WP p m r) (inputsLoadable_pqSendInputs WP p m r hp)
        (isStdinOverCap_pqSendInputs WP p m r hstin)
    · simp only [hstin, ↓reduceIte]
      have hnstin : ¬ IsStdinOverCap (pqSendInputs WP p m r) :=
        not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)
      by_cases hover : m.length > maxPlaintextBytes
      · simp only [hover, ↓reduceIte]
        exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_sendOverCap hext hE htok hfs_eq
          hCode hH hmainW hstk hstk'
          (cliInputsOk_pqSendInputs WP p m r) (inputsLoadable_pqSendInputs WP p m r hp)
          (isSendOverCap_pqSendInputs WP p m r (by unfold maxPlaintextBytes at hover; exact hover))
          hnstin (coinsReadable_pqSendInputs WP p m r)
      · simp only [hover, ↓reduceIte]
        obtain ⟨a, hrun, hobs, hcommit⟩ := hSend m r hm
        exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_call_obs hext hE htok hfs_eq
          hCode hH hmainW hstk hstk'
          (cliInputsOk_pqSendInputs WP p m r) (inputsLoadable_pqSendInputs WP p m r hp)
          hrun
          (not_isSendOverCap_of_stdin_le
            (by simp only [pqSendInputs, pqInputs]; unfold maxPlaintextBytes at hover; omega))
          hnstin hobs (coinsReadable_pqSendInputs WP p m r) hcommit
  · intro c rc hc
    by_cases hstin : (wireWhisper :: c).length > stdinCapBytes
    · simp only [hstin, ↓reduceIte]
      exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_stdinOverCap hext hE htok hfs_eq
        hCode hH hmainW hstk hstk'
        (cliInputsOk_pqRecvInputs WP p (wireWhisper :: c) rc)
        (inputsLoadable_pqRecvInputs WP p (wireWhisper :: c) rc hp)
        (isStdinOverCap_pqRecvInputs WP p (wireWhisper :: c) rc hstin)
    · simp only [hstin, ↓reduceIte]
      obtain ⟨a, hrun, hobs, hcommit⟩ := hWhisper c rc hc
      exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_call_obs hext hE htok hfs_eq
        hCode hH hmainW hstk hstk'
        (cliInputsOk_pqRecvInputs WP p (wireWhisper :: c) rc)
        (inputsLoadable_pqRecvInputs WP p (wireWhisper :: c) rc hp)
        hrun (not_isSendOverCap_pqRecvInputs WP p (wireWhisper :: c) rc)
        (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)) hobs
        (coinsReadable_pqRecvInputs WP p (wireWhisper :: c) rc) hcommit
  · intro m rc hm hmatch
    by_cases hstin : (wirePrekey :: m.bytes).length > stdinCapBytes
    · simp only [hstin, ↓reduceIte]
      exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_stdinOverCap hext hE htok hfs_eq
        hCode hH hmainW hstk hstk'
        (cliInputsOk_pqRecvInputs WP p (wirePrekey :: m.bytes) rc)
        (inputsLoadable_pqRecvInputs WP p (wirePrekey :: m.bytes) rc hp)
        (isStdinOverCap_pqRecvInputs WP p (wirePrekey :: m.bytes) rc hstin)
    · simp only [hstin, ↓reduceIte]
      obtain ⟨a, hrun, hobs, hcommit⟩ := hPrekey m rc hm hmatch
      exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_call_obs hext hE htok hfs_eq
        hCode hH hmainW hstk hstk'
        (cliInputsOk_pqRecvInputs WP p (wirePrekey :: m.bytes) rc)
        (inputsLoadable_pqRecvInputs WP p (wirePrekey :: m.bytes) rc hp)
        hrun (not_isSendOverCap_pqRecvInputs WP p (wirePrekey :: m.bytes) rc)
        (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)) hobs
        (coinsReadable_pqRecvInputs WP p (wirePrekey :: m.bytes) rc) hcommit
  · intro c rc hc h2 h3
    by_cases hstin : c.length > stdinCapBytes
    · simp only [hstin, ↓reduceIte]
      exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_stdinOverCap hext hE htok hfs_eq
        hCode hH hmainW hstk hstk'
        (cliInputsOk_pqRecvInputs WP p c rc) (inputsLoadable_pqRecvInputs WP p c rc hp)
        (isStdinOverCap_pqRecvInputs WP p c rc hstin)
    · simp only [hstin, ↓reduceIte]
      obtain ⟨a, hrun, hobs, hcommit⟩ := hBad c rc hc h2 h3
      exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_call_obs hext hE htok hfs_eq
        hCode hH hmainW hstk hstk'
        (cliInputsOk_pqRecvInputs WP p c rc) (inputsLoadable_pqRecvInputs WP p c rc hp)
        hrun (not_isSendOverCap_pqRecvInputs WP p c rc)
        (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)) hobs
        (coinsReadable_pqRecvInputs WP p c rc) hcommit

/-- Entry-guarded counterpart of `CliStrictPlaced2.cliSpecPqxdhNoMatch_ext_strict_of_b2_needLocks`,
eliminating `EntryGuard` internally via the single-input bridges in Section 1. -/
theorem cliSpecPqxdhNoMatch_ext_strict_of_b2_needLocks_guarded
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {mainIdx : Nat}
    {inputsOf : Inputs → ProcessInputs} {EntryGuard : State → Prop}
    {exitStk : Nat} {libcAddr : BitVec 64}
    {CodeOk : Memory → Prop} {stk : Nat} {lim : BudgetLimits}
    {elf : ElfImage} {W : CliHooks}
    (hext : ExternPreservesNoAllocFailed (ext W))
    (hE : ElfStaticOk elf)
    (htok : CliElfTokenCellsPlacedAt mpl elf)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hCode : ∀ m, CodeOk m → (cliProgExtPlacedAt mpl ext mainIdx W).CodeLoaded m)
    (hH : MuslHarnessFineNeedLocksGuardedPerInput exitStk libcAddr (patchElfTokensPlacedAt mpl elf)
      (cliProgExtPlacedAt mpl ext mainIdx W) (mpl.base mainIdx) inputsOf
      mmpl lim fineCostModel.init stk CodeOk (cliStaticsPlacedAt mpl) EntryGuard)
    (hstk : exitStk ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    (hDropNz : mpl.base 547 ≠ 0#64)
    (hover : MainOkCliExtOverB2NeedLocksPlacedAtG mpl mmpl ext mainIdx inputsOf EntryGuard CodeOk
      libcAddr elf.brkStart stk lim)
    (hAesE : W.C.E = CryptoGames.AES256.aes256Enc)
    (hAesD : W.C.D = CryptoGames.AES256.aes256Dec)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (hF512 : W.Q.F512 = CryptoGames.SHA512.sha512CompressState)
    (hEnc : W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec)
    (hDec : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental) :
    ∀ X : UnreachedPqxdhPrimitives,
      CliSpecPqxdhNoMatch (cliRunExtOnInputsSigAt mpl ext mainIdx inputsOf elf W) X ⟨W.C, W.Q⟩ := by
  intro X st hst x g hsess m rc hm hnomatch
  let WP : PEParams := ⟨W.C, W.Q⟩
  obtain ⟨Run, hmainW, hclause⟩ := hover hDropNz X W hAesE hAesD hX hPub hF512 hEnc hDec hK
  by_cases hstin : (wirePrekey :: m.bytes).length > stdinCapBytes
  · simp only [hstin, ↓reduceIte]
    exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_stdinOverCap hext hE htok hfs_eq
      hCode hH hmainW hstk hstk'
      (cliInputsOk_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
      (inputsLoadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hst)
      (isStdinOverCap_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hstin)
  · simp only [hstin, ↓reduceIte]
    obtain ⟨a, hrun, hobsEx, hcommit⟩ := hclause st hst x g hsess m rc hm hnomatch
    exact
      cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_call_pred hext hE htok hfs_eq hCode hH
        hmainW hstk hstk'
        (cliInputsOk_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
        (inputsLoadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hst)
        hrun (not_isSendOverCap_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
        (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin))
        hobsEx (coinsReadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc) hcommit

/-! ## 4. Guarded Assumptions Bundle, Startup Discharger, and ELF Composers -/

/-- Guarded extension of `CliElfExtB2NeedLocksAssumptions2` carrying `harnessG` at `EntryGuard`. -/
structure CliElfExtB2NeedLocksAssumptions2G
    (mpl mmpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State))
    (mainIdx : Nat) (inputsOf : Inputs → ProcessInputs)
    (EntryGuard : State → Prop)
    (exitStk : Nat) (libcAddr : BitVec 64) (stk : Nat) (CodeOk : Memory → Prop)
    (lim : BudgetLimits) (elf : ElfImage) : Prop extends
    CliElfExtB2NeedLocksAssumptions2 mpl mmpl ext mainIdx inputsOf
      exitStk libcAddr stk CodeOk lim elf where
  harnessG : ∀ W : CliHooks,
    MuslHarnessFineNeedLocksGuardedPerInput exitStk libcAddr (patchElfTokensPlacedAt mpl elf)
      (cliProgExtPlacedAt mpl ext mainIdx W) (mpl.base mainIdx) inputsOf
      mmpl lim fineCostModel.init stk CodeOk (cliStaticsPlacedAt mpl) EntryGuard

/-- Forgetful projection from `CliElfExtB2NeedLocksAssumptions2G` to the unguarded
`CliElfExtB2NeedLocksAssumptions2`. -/
theorem CliElfExtB2NeedLocksAssumptions2G.toUnguarded
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)}
    {mainIdx : Nat} {inputsOf : Inputs → ProcessInputs}
    {EntryGuard : State → Prop}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {lim : BudgetLimits} {elf : ElfImage}
    (H : CliElfExtB2NeedLocksAssumptions2G mpl mmpl ext mainIdx inputsOf EntryGuard
      exitStk libcAddr stk CodeOk lim elf) :
    CliElfExtB2NeedLocksAssumptions2 mpl mmpl ext mainIdx inputsOf
      exitStk libcAddr stk CodeOk lim elf :=
  H.toCliElfExtB2NeedLocksAssumptions2

/-- Concrete `cliBudgetLimits` + `F3C2EntryGuard mpl mmpl` specialization of
`CliElfExtB2NeedLocksAssumptions2G`. -/
abbrev CliElfF3B2NeedLocksAssumptionsG
    (mpl mmpl : Obj.MultiPlacement)
    (exitStk : Nat) (libcAddr : BitVec 64) (stk : Nat) (CodeOk : Memory → Prop)
    (elf : ElfImage) : Prop :=
  CliElfExtB2NeedLocksAssumptions2G mpl mmpl (cliExternsPlaced mmpl) 617 cliProcessInputs
    (F3C2EntryGuard mpl mmpl) exitStk libcAddr stk CodeOk cliBudgetLimits elf

/-- Real-AES-guarded `inputsOf`-parameterized strict 2-placement ELF correctness predicate. -/
@[expose] def CliPqxdhExtOnInputsElfCorrectStrictPlacedAt2Aes
    (mpl mmpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State))
    (mainIdx : Nat) (inputsOf : Inputs → ProcessInputs) (elf : ElfImage) : Prop :=
  CliElfCodeMatchesPlaced mpl mmpl elf ∧
  ∀ W : CliHooks,
    W.C.E = CryptoGames.AES256.aes256Enc →
    W.C.D = CryptoGames.AES256.aes256Dec →
    W.C.X = CryptoGames.RFC7748.x25519Ref →
    W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
    W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
    W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
    W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
    W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
    ∀ X : UnreachedPqxdhPrimitives,
      CliSpecPqxdh (cliRunExtOnInputsSigAt mpl ext mainIdx inputsOf elf W) X ⟨W.C, W.Q⟩ ∧
      CliSpecPqxdhNoMatch (cliRunExtOnInputsSigAt mpl ext mainIdx inputsOf elf W) X ⟨W.C, W.Q⟩

/-- Real-AES-guarded strict 2-placement ELF correctness at `inputsOf := cliProcessInputs`. -/
abbrev CliPqxdhExtElfCorrectStrictPlacedAt2Aes
    (mpl mmpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State))
    (mainIdx : Nat) (elf : ElfImage) : Prop :=
  CliPqxdhExtOnInputsElfCorrectStrictPlacedAt2Aes mpl mmpl ext mainIdx cliProcessInputs elf

private theorem cliSpecPqxdh_congr_on_inputs
    {run₁ run₂ : CliRun} {X : UnreachedPqxdhPrimitives} {WP : PEParams}
    (heq : ∀ i : Inputs, CliPqxdhInputs WP i → run₁ i = run₂ i)
    (h : CliSpecPqxdh run₂ X WP) :
    CliSpecPqxdh run₁ X WP := by
  intro st hdom
  obtain ⟨h1, h2, h3, h4, h5⟩ := h st hdom
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro b t hnone
    rw [heq _ ⟨st, hdom, Or.inl ⟨hnone, b, t, rfl⟩⟩]
    exact h1 b t hnone
  · intro m r hm
    have hi : CliPqxdhInputs WP (pqSendInputs WP st m r) :=
      ⟨st, hdom, Or.inr (Or.inl ⟨m, r, hm, rfl⟩)⟩
    have h2' := h2 m r hm
    split_ifs at h2' ⊢ <;> (rw [heq _ hi]; exact h2')
  · intro c rc hc
    have hi : CliPqxdhInputs WP (pqRecvInputs WP st (wireWhisper :: c) rc) :=
      ⟨st, hdom, Or.inr (Or.inr (Or.inl ⟨c, rc, hc, rfl⟩))⟩
    have h3' := h3 c rc hc
    split_ifs at h3' ⊢ <;> (rw [heq _ hi]; exact h3')
  · intro m rc hm hmatch
    have hi : CliPqxdhInputs WP (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) :=
      ⟨st, hdom, Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rc, hm, rfl⟩)))⟩
    have h4' := h4 m rc hm hmatch
    split_ifs at h4' ⊢ <;> (rw [heq _ hi]; exact h4')
  · intro c rc hc h2ne h3ne
    have hi : CliPqxdhInputs WP (pqRecvInputs WP st c rc) :=
      ⟨st, hdom, Or.inr (Or.inr (Or.inr (Or.inr ⟨c, rc, hc, h2ne, h3ne, rfl⟩)))⟩
    have h5' := h5 c rc hc h2ne h3ne
    split_ifs at h5' ⊢ <;> (rw [heq _ hi]; exact h5')

private theorem cliSpecPqxdhNoMatch_congr_on_inputs
    {run₁ run₂ : CliRun} {X : UnreachedPqxdhPrimitives} {WP : PEParams}
    (heq : ∀ i : Inputs, CliPqxdhInputs WP i → run₁ i = run₂ i)
    (h : CliSpecPqxdhNoMatch run₂ X WP) :
    CliSpecPqxdhNoMatch run₁ X WP := by
  intro st hdom x g hsess m rc hm hnm
  have hi : CliPqxdhInputs WP (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) :=
    ⟨st, hdom, Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rc, hm, rfl⟩)))⟩
  have h' := h st hdom x g hsess m rc hm hnm
  rw [heq _ hi]
  exact h'

theorem cliPqxdhElfCorrectStrictPlaced2Aes_of_extOnInputsProgEq
    {mpl mmpl : Obj.MultiPlacement} {ext : CliHooks → String → Option (State → State)}
    {mainIdx : Nat} {inputsOf : Inputs → ProcessInputs} {elf : ElfImage}
    (hprog : ∀ W : CliHooks,
      cliProgPlacedSig mpl mmpl W = cliProgExtPlacedSigAt mpl ext mainIdx W)
    (hload : ∀ (W : CliHooks) (i : Inputs),
      CliPqxdhInputs ⟨W.C, W.Q⟩ i →
      elf.loadState (cliProcessInputs i) = elf.loadState (inputsOf i))
    (hStrict : CliPqxdhExtOnInputsElfCorrectStrictPlacedAt2Aes mpl mmpl ext mainIdx inputsOf elf) :
    CliPqxdhElfCorrectStrictPlaced2Aes mpl mmpl elf := by
  refine ⟨hStrict.1, fun W hE hD hX hPub hF512 hEnc hDec hK X => ?_⟩
  have heq : ∀ i : Inputs, CliPqxdhInputs ⟨W.C, W.Q⟩ i →
      cliRunPlacedSig mpl mmpl elf W i =
        cliRunExtOnInputsSigAt mpl ext mainIdx inputsOf elf W i :=
    fun i hi => cliRunPlacedSig_eq_on_input_of_progEq2 (hprog W) (hload W i hi)
  exact ⟨cliSpecPqxdh_congr_on_inputs heq
      (hStrict.2 W hE hD hX hPub hF512 hEnc hDec hK X).1,
    cliSpecPqxdhNoMatch_congr_on_inputs heq
      (hStrict.2 W hE hD hX hPub hF512 hEnc hDec hK X).2⟩

theorem cliPqxdhElfCorrectStrictPlaced2Aes_of_extProgEq
    {mpl mmpl : Obj.MultiPlacement} {ext : CliHooks → String → Option (State → State)}
    {mainIdx : Nat} {elf : ElfImage}
    (hprog : ∀ W : CliHooks,
      cliProgPlacedSig mpl mmpl W = cliProgExtPlacedSigAt mpl ext mainIdx W)
    (hStrict : CliPqxdhExtElfCorrectStrictPlacedAt2Aes mpl mmpl ext mainIdx elf) :
    CliPqxdhElfCorrectStrictPlaced2Aes mpl mmpl elf :=
  cliPqxdhElfCorrectStrictPlaced2Aes_of_extOnInputsProgEq hprog (fun _ _ _ => rfl) hStrict

/-- Guarded top strict 2-placement ELF theorem eliminating `EntryGuard` via `H.harnessG`. -/
theorem cliPqxdhExtOnInputsElfCorrectStrictPlacedAt2_of_b2NeedLocksAssumptionsG
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)}
    {mainIdx : Nat} {inputsOf : Inputs → ProcessInputs}
    {EntryGuard : State → Prop}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {lim : BudgetLimits} {elf : ElfImage}
    (hext : ∀ W : CliHooks, ExternPreservesNoAllocFailed (ext W))
    (H : CliElfExtB2NeedLocksAssumptions2G mpl mmpl ext mainIdx inputsOf EntryGuard
      exitStk libcAddr stk CodeOk lim elf)
    (hmain : MainOkCliExtPqB2NeedLocksPlacedAtG mpl mmpl ext mainIdx inputsOf EntryGuard CodeOk
      libcAddr elf.brkStart stk lim)
    (hover : MainOkCliExtOverB2NeedLocksPlacedAtG mpl mmpl ext mainIdx inputsOf EntryGuard CodeOk
      libcAddr elf.brkStart stk lim) :
    CliPqxdhExtOnInputsElfCorrectStrictPlacedAt2Aes mpl mmpl ext mainIdx inputsOf elf :=
  ⟨H.codeMatches, fun W hE hD hX hPub hF512 hEnc hDec hK X =>
    ⟨cliSpecPqxdh_ext_strict_of_b2_needLocks_guarded (hext W) H.elfStaticOk H.tokenCells
      H.fsEq (H.codeLoaded W) (H.harnessG W) H.stkLo H.stkHi H.base547NeZero hmain
      hE hD hX hPub hF512 hEnc hDec hK X,
     cliSpecPqxdhNoMatch_ext_strict_of_b2_needLocks_guarded (hext W) H.elfStaticOk H.tokenCells
      H.fsEq (H.codeLoaded W) (H.harnessG W) H.stkLo H.stkHi H.base547NeZero hover
      hE hD hX hPub hF512 hEnc hDec hK X⟩⟩

/-- Guarded strict 2-placement single-input whole-process outcome bridge upgrading `H.harnessG`'s
`F3C2EntryGuard` to `F3SampleNttEntryGuard` on input `i` via
`realNeverViolatesSampleNtt_of_not_cliReachesSampleNttStuckPlaced`. -/
theorem outcome_of_main_strict_f3_sampleNtt_at
    {mpl mmpl : Obj.MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage} {W : CliHooks} {Run : Inputs → RunAnswer → Prop}
    (hext : ExternPreservesNoAllocFailed (cliExternsPlaced mmpl W))
    (H : CliElfF3B2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmain : ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (mpl.base 617)
        (withEntryGuard (F3SampleNttEntryGuard mpl mmpl)
          (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart)
            cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl) Run cliProcessInputs)))
    {i : Inputs} {r : MainResult}
    (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hc : MainCaseB2 Run IsSendOverCap IsStdinOverCap i r)
    (hNoStuck : ¬ CliReachesSampleNttStuckPlaced mpl mmpl elf W i) :
    ∃ res,
      outcomeOf (patchElfTokensPlacedAt mpl elf)
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (cliProcessInputs i) = some res ∧
      MainResult.Observed i.files r res := by
  let P := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W
  obtain ⟨s0, sm, Fr, γ, hload, hsteps0, hpc, hrun, hal, hfs, htr, hG, hx0, hmem, hexit⟩ :=
    H.harnessG W (elfStaticOk_patchElfTokensPlacedAt H.elfStaticOk) i ⟨hi, hl⟩
  have hpatch := loadState_patchElfTokensPlacedAt H.elfStaticOk H.tokenCells (cliProcessInputs i)
  have hmap : (elf.loadState (cliProcessInputs i)).map (cliTokenPatchPlaced mpl) = .ok s0 :=
    hpatch.symm.trans hload
  have hSntt : RealNeverViolatesSampleNtt mpl (cliExternsPlaced mmpl) sm := by
    cases hLoadElf : elf.loadState (cliProcessInputs i) with
    | error _ => simp [hLoadElf, Except.map] at hmap
    | ok s_elf =>
      simp only [hLoadElf, Except.map, Except.ok.injEq] at hmap
      have hStart : Steps (cliProgPlacedSig mpl mmpl W) (cliTokenPatchPlaced mpl s_elf) sm :=
        hmap ▸ steps_cliProgPlacedSig_of_running W W (loadState_status_running hload) hrun hsteps0
      exact realNeverViolatesSampleNtt_of_not_cliReachesSampleNttStuckPlaced W hLoadElf hStart hrun
        hNoStuck (fun _ => rfl)
  have hbrk : (patchElfTokensPlacedAt mpl elf).brkStart = elf.brkStart := rfl
  let A := fineHookRustCliAllocBudget γ mmpl sm.tpidrEl0 elf.brkStart
  obtain ⟨hfs0, htr0⟩ := loadState_fs_trace hload
  change sm.mem ⊨
    b2MainEntryPreFine CodeOk A cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl) i
      sm ∗ Fr at hmem
  simp only [b2MainEntryPreFine, sepConj_assoc, satisfies_pure_sepConj] at hmem
  obtain ⟨⟨hCO, hsp⟩, hmem⟩ := hmem
  let baseSpec :=
    b2MainSpecTightNeedLocksFineAt libcAddr CodeOk A cliBudgetLimits fineCostModel.init stk
      (cliStaticsPlacedAt mpl) Run cliProcessInputs
  have hpre : sm.mem ⊨ (withEntryGuard (F3SampleNttEntryGuard mpl mmpl) baseSpec).pre ⟨i, r⟩ sm ∗ Fr := by
    simp only [withEntryGuard, baseSpec, b2MainSpecTightNeedLocksFineAt, sepConj_assoc,
      satisfies_pure_sepConj]
    exact ⟨⟨hG, hSntt⟩, ⟨hCO, hc, hi, ⟨hx0, hfs.trans hfs0, htr.trans htr0⟩, hsp⟩, hmem⟩
  obtain ⟨sf, hsteps1, hout, _⟩ :=
    (hmain γ sm.tpidrEl0).no_fault_before_outcome ⟨i, r⟩ Fr sm hpc hrun hpre hal
      (H.codeLoaded W sm.mem hCO)
  have hsteps01 := hsteps0.trans hsteps1
  rcases hout with ⟨hret, _, hpost⟩ | ⟨hpan, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · simp only [withEntryGuard, b2MainSpecTightNeedLocksFineAt, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    obtain ⟨⟨code, w, out, rfl, hw0, hfiles, hout⟩, hpost⟩ := hpost
    have hpost' : sf.mem ⊨ (((libcAddr + 3#64) ↦₈ 0#8) ∗ stackAt sm.sp stk ∗ anyHeap) ∗ Fr := by
      simpa only [sepConj_assoc] using hpost
    obtain ⟨sx, hsteps2, hst, hfsx, htrx⟩ :=
      hexit sf hsteps1 hret (exit_frame_needLocks_n H.stkLo H.stkHi hpost')
    have hle := hc.code_le rfl
    refine ⟨_, outcomeOf_eq_exited hload (hsteps01.trans hsteps2) hst, ?_⟩
    dsimp only [MainResult.Observed]
    refine ⟨?_, ?_, ?_⟩
    · rw [hw0, signExtend_ofNat_small hle]
    · rw [htrx, hout]
    · rw [hfsx, fsView_congr hfiles, hfs, hfs0, H.fsEq i]
      exact fsView_writeAll_initFsState i w hc.commitOk
  · simp only [withEntryGuard, b2MainSpecTightNeedLocksFineAt, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    rcases hpost.1 with rfl | hA
    · exact ⟨_, outcomeOf_eq_aborted hload hsteps01 hpan, trivial⟩
    · have hs0 : allocFailedEvent ∉ s0.trace := by rw [htr0]; simp
      exact absurd (List.mem_of_mem_drop hA)
        (steps_preserves_no_allocFailed (prog := P) rfl hext externPreservesNoAllocFailed_none
          hsteps01 hs0)
  · simp only [withEntryGuard, b2MainSpecTightNeedLocksFineAt] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · simp only [withEntryGuard, b2MainSpecTightNeedLocksFineAt] at hpost
    exact (not_satisfies_false_sepConj hpost).elim

/-- Single-input `SampleNTT`-guarded `stdinOverCap` bridge directly to `cliRunPlacedSig`. -/
theorem cliRunPlacedSig_of_strict_f3_sampleNtt_stdinOverCap
    {mpl mmpl : Obj.MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage} {W : CliHooks} {Run : Inputs → RunAnswer → Prop}
    (hext : ExternPreservesNoAllocFailed (cliExternsPlaced mmpl W))
    (H : CliElfF3B2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmain : ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (mpl.base 617)
        (withEntryGuard (F3SampleNttEntryGuard mpl mmpl)
          (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart)
            cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl) Run cliProcessInputs)))
    {i : Inputs}
    (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hstin : IsStdinOverCap i)
    (hNoStuck : ¬ CliReachesSampleNttStuckPlaced mpl mmpl elf W i) :
    cliRunPlacedSig mpl mmpl elf W i = some (.exited 2 [] (filesOf i.files)) := by
  obtain ⟨res, hout, hresObs⟩ :=
    outcome_of_main_strict_f3_sampleNtt_at hext H hmain hi hl (MainCaseB2.stdinOverCap hstin)
      hNoStuck
  have hruns := cliRunsToExtOnInputsAt_of_outcomeOf_usage
    (loadState_patchElfTokensPlacedAt H.elfStaticOk H.tokenCells (cliProcessInputs i)) hout hresObs
  exact (cliRunPlacedSig_eq_on_input_of_progEq2
    (cliProgExtPlacedSigAt_cliExternsPlaced_eq mpl mmpl W).symm rfl).trans
    (cliRunExtOnInputsSigAt_eq_some hruns)

/-- Single-input `SampleNTT`-guarded `sendOverCap` bridge directly to `cliRunPlacedSig`. -/
theorem cliRunPlacedSig_of_strict_f3_sampleNtt_sendOverCap
    {mpl mmpl : Obj.MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage} {W : CliHooks} {Run : Inputs → RunAnswer → Prop}
    (hext : ExternPreservesNoAllocFailed (cliExternsPlaced mmpl W))
    (H : CliElfF3B2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmain : ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (mpl.base 617)
        (withEntryGuard (F3SampleNttEntryGuard mpl mmpl)
          (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart)
            cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl) Run cliProcessInputs)))
    {i : Inputs}
    (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hover : IsSendOverCap i) (hnstin : ¬ IsStdinOverCap i)
    (hcoins : CoinsReadable i)
    (hNoStuck : ¬ CliReachesSampleNttStuckPlaced mpl mmpl elf W i) :
    cliRunPlacedSig mpl mmpl elf W i = some (.exited 1 [] (filesOf i.files)) := by
  obtain ⟨res, hout, hresObs⟩ :=
    outcome_of_main_strict_f3_sampleNtt_at hext H hmain hi hl
      (MainCaseB2.sendOverCap hover hnstin hcoins) hNoStuck
  have hruns := cliRunsToExtOnInputsAt_of_outcomeOf_observed (a := some none)
    (loadState_patchElfTokensPlacedAt H.elfStaticOk H.tokenCells (cliProcessInputs i)) hout hresObs
  exact (cliRunPlacedSig_eq_on_input_of_progEq2
    (cliProgExtPlacedSigAt_cliExternsPlaced_eq mpl mmpl W).symm rfl).trans
    (cliRunExtOnInputsSigAt_eq_some hruns)

/-- Single-input `SampleNTT`-guarded `call` equality bridge directly to `cliRunPlacedSig`. -/
theorem cliRunPlacedSig_of_strict_f3_sampleNtt_call_obs
    {mpl mmpl : Obj.MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage} {W : CliHooks} {Run : Inputs → RunAnswer → Prop}
    (hext : ExternPreservesNoAllocFailed (cliExternsPlaced mmpl W))
    (H : CliElfF3B2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmain : ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (mpl.base 617)
        (withEntryGuard (F3SampleNttEntryGuard mpl mmpl)
          (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart)
            cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl) Run cliProcessInputs)))
    {i : Inputs} {a : RunAnswer} {o : Outcome}
    (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hrun : Run i a) (hnover : ¬ IsSendOverCap i) (hnstin : ¬ IsStdinOverCap i)
    (hobs : observe i.files a = o)
    (hcoins : CoinsReadable i) (hcommit : CommitOk i (MainResult.ofAnswer a))
    (hNoStuck : ¬ CliReachesSampleNttStuckPlaced mpl mmpl elf W i) :
    cliRunPlacedSig mpl mmpl elf W i = some o := by
  obtain ⟨res, hout, hresObs⟩ :=
    outcome_of_main_strict_f3_sampleNtt_at hext H hmain hi hl
      (MainCaseB2.call hrun hnover hnstin hcoins hcommit) hNoStuck
  have hruns := cliRunsToExtOnInputsAt_of_outcomeOf_observed
    (loadState_patchElfTokensPlacedAt H.elfStaticOk H.tokenCells (cliProcessInputs i)) hout hresObs
  rw [hobs] at hruns
  exact (cliRunPlacedSig_eq_on_input_of_progEq2
    (cliProgExtPlacedSigAt_cliExternsPlaced_eq mpl mmpl W).symm rfl).trans
    (cliRunExtOnInputsSigAt_eq_some hruns)

/-- Predicate-valued companion of `cliRunPlacedSig_of_strict_f3_sampleNtt_call_obs`. -/
theorem cliRunPlacedSig_of_strict_f3_sampleNtt_call_pred
    {mpl mmpl : Obj.MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage} {W : CliHooks} {Run : Inputs → RunAnswer → Prop}
    {P : Outcome → Prop}
    (hext : ExternPreservesNoAllocFailed (cliExternsPlaced mmpl W))
    (H : CliElfF3B2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmain : ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (mpl.base 617)
        (withEntryGuard (F3SampleNttEntryGuard mpl mmpl)
          (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart)
            cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl) Run cliProcessInputs)))
    {i : Inputs} {a : RunAnswer}
    (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hrun : Run i a) (hnover : ¬ IsSendOverCap i) (hnstin : ¬ IsStdinOverCap i)
    (hp : P (observe i.files a))
    (hcoins : CoinsReadable i) (hcommit : CommitOk i (MainResult.ofAnswer a))
    (hNoStuck : ¬ CliReachesSampleNttStuckPlaced mpl mmpl elf W i) :
    ∃ o, cliRunPlacedSig mpl mmpl elf W i = some o ∧ P o :=
  ⟨observe i.files a,
    cliRunPlacedSig_of_strict_f3_sampleNtt_call_obs hext H hmain hi hl hrun hnover hnstin rfl
      hcoins hcommit hNoStuck, hp⟩

/-- Guarded strict 2-placement ELF composer concluding
`CliPqxdhElfCorrectStrictPlaced2Aes mpl mmpl elf` under `¬ CliReachesSampleNttStuckPlaced`. -/
theorem cliPqxdhElfCorrectStrictPlaced2_of_f3B2NeedLocksG
    {mpl mmpl : Obj.MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (hext : ∀ W : CliHooks, ExternPreservesNoAllocFailed (cliExternsPlaced mmpl W))
    (H : CliElfF3B2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmain : MainOkCliF3PqB2NeedLocksPlacedAtG mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hover : MainOkCliF3OverB2NeedLocksPlacedAtG mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hNoStuck : ∀ W : CliHooks,
      W.C.E = CryptoGames.AES256.aes256Enc →
      W.C.D = CryptoGames.AES256.aes256Dec →
      W.C.X = CryptoGames.RFC7748.x25519Ref →
      W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
      W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
      W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
      W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
      W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
      ∀ i : Inputs, CliPqxdhInputs ⟨W.C, W.Q⟩ i →
        ¬ CliReachesSampleNttStuckPlaced mpl mmpl elf W i) :
    CliPqxdhElfCorrectStrictPlaced2Aes mpl mmpl elf := by
  refine ⟨H.codeMatches, fun W hAesE hAesD hX hPub hF512 hEnc hDec hK X => ?_⟩
  let WP : PEParams := ⟨W.C, W.Q⟩
  have hNS := hNoStuck W hAesE hAesD hX hPub hF512 hEnc hDec hK
  refine ⟨?_, ?_⟩
  · intro p hp
    obtain ⟨Run, hmainW, hclauses⟩ :=
      hmain H.base547NeZero X W hAesE hAesD hX hPub hF512 hEnc hDec hK
    obtain ⟨hInit, hSend, hWhisper, hPrekey, hBad⟩ := hclauses p hp
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro b t hnone
      obtain ⟨a, hrun, hobs, hcommit⟩ := hInit b t hnone
      exact cliRunPlacedSig_of_strict_f3_sampleNtt_call_obs (hext W) H hmainW
        (cliInputsOk_pqInitInputs WP p b t) (inputsLoadable_pqInitInputs WP p b t hp)
        hrun (not_isSendOverCap_pqInitInputs WP p b t)
        (not_isStdinOverCap_pqInitInputs WP p b t) hobs
        (coinsReadable_pqInitInputs WP p b t) hcommit
        (hNS _ ⟨p, hp, Or.inl ⟨hnone, b, t, rfl⟩⟩)
    · intro m r hm
      have hiDom : CliPqxdhInputs WP (pqSendInputs WP p m r) :=
        ⟨p, hp, Or.inr (Or.inl ⟨m, r, hm, rfl⟩)⟩
      by_cases hstin : m.length > stdinCapBytes
      · simp only [hstin, ↓reduceIte]
        exact cliRunPlacedSig_of_strict_f3_sampleNtt_stdinOverCap (hext W) H hmainW
          (cliInputsOk_pqSendInputs WP p m r) (inputsLoadable_pqSendInputs WP p m r hp)
          (isStdinOverCap_pqSendInputs WP p m r hstin) (hNS _ hiDom)
      · simp only [hstin, ↓reduceIte]
        have hnstin : ¬ IsStdinOverCap (pqSendInputs WP p m r) :=
          not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)
        by_cases hovc : m.length > maxPlaintextBytes
        · simp only [hovc, ↓reduceIte]
          exact cliRunPlacedSig_of_strict_f3_sampleNtt_sendOverCap (hext W) H hmainW
            (cliInputsOk_pqSendInputs WP p m r) (inputsLoadable_pqSendInputs WP p m r hp)
            (isSendOverCap_pqSendInputs WP p m r (by unfold maxPlaintextBytes at hovc; exact hovc))
            hnstin (coinsReadable_pqSendInputs WP p m r) (hNS _ hiDom)
        · simp only [hovc, ↓reduceIte]
          obtain ⟨a, hrun, hobs, hcommit⟩ := hSend m r hm
          exact cliRunPlacedSig_of_strict_f3_sampleNtt_call_obs (hext W) H hmainW
            (cliInputsOk_pqSendInputs WP p m r) (inputsLoadable_pqSendInputs WP p m r hp)
            hrun
            (not_isSendOverCap_of_stdin_le
              (by simp only [pqSendInputs, pqInputs]; unfold maxPlaintextBytes at hovc; omega))
            hnstin hobs (coinsReadable_pqSendInputs WP p m r) hcommit (hNS _ hiDom)
    · intro c rc hc
      have hiDom : CliPqxdhInputs WP (pqRecvInputs WP p (wireWhisper :: c) rc) :=
        ⟨p, hp, Or.inr (Or.inr (Or.inl ⟨c, rc, hc, rfl⟩))⟩
      by_cases hstin : (wireWhisper :: c).length > stdinCapBytes
      · simp only [hstin, ↓reduceIte]
        exact cliRunPlacedSig_of_strict_f3_sampleNtt_stdinOverCap (hext W) H hmainW
          (cliInputsOk_pqRecvInputs WP p (wireWhisper :: c) rc)
          (inputsLoadable_pqRecvInputs WP p (wireWhisper :: c) rc hp)
          (isStdinOverCap_pqRecvInputs WP p (wireWhisper :: c) rc hstin) (hNS _ hiDom)
      · simp only [hstin, ↓reduceIte]
        obtain ⟨a, hrun, hobs, hcommit⟩ := hWhisper c rc hc
        exact cliRunPlacedSig_of_strict_f3_sampleNtt_call_obs (hext W) H hmainW
          (cliInputsOk_pqRecvInputs WP p (wireWhisper :: c) rc)
          (inputsLoadable_pqRecvInputs WP p (wireWhisper :: c) rc hp)
          hrun (not_isSendOverCap_pqRecvInputs WP p (wireWhisper :: c) rc)
          (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)) hobs
          (coinsReadable_pqRecvInputs WP p (wireWhisper :: c) rc) hcommit (hNS _ hiDom)
    · intro m rc hm hmatch
      have hiDom : CliPqxdhInputs WP (pqRecvInputs WP p (wirePrekey :: m.bytes) rc) :=
        ⟨p, hp, Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rc, hm, rfl⟩)))⟩
      by_cases hstin : (wirePrekey :: m.bytes).length > stdinCapBytes
      · simp only [hstin, ↓reduceIte]
        exact cliRunPlacedSig_of_strict_f3_sampleNtt_stdinOverCap (hext W) H hmainW
          (cliInputsOk_pqRecvInputs WP p (wirePrekey :: m.bytes) rc)
          (inputsLoadable_pqRecvInputs WP p (wirePrekey :: m.bytes) rc hp)
          (isStdinOverCap_pqRecvInputs WP p (wirePrekey :: m.bytes) rc hstin) (hNS _ hiDom)
      · simp only [hstin, ↓reduceIte]
        obtain ⟨a, hrun, hobs, hcommit⟩ := hPrekey m rc hm hmatch
        exact cliRunPlacedSig_of_strict_f3_sampleNtt_call_obs (hext W) H hmainW
          (cliInputsOk_pqRecvInputs WP p (wirePrekey :: m.bytes) rc)
          (inputsLoadable_pqRecvInputs WP p (wirePrekey :: m.bytes) rc hp)
          hrun (not_isSendOverCap_pqRecvInputs WP p (wirePrekey :: m.bytes) rc)
          (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)) hobs
          (coinsReadable_pqRecvInputs WP p (wirePrekey :: m.bytes) rc) hcommit (hNS _ hiDom)
    · intro c rc hc h2 h3
      have hiDom : CliPqxdhInputs WP (pqRecvInputs WP p c rc) :=
        ⟨p, hp, Or.inr (Or.inr (Or.inr (Or.inr ⟨c, rc, hc, h2, h3, rfl⟩)))⟩
      by_cases hstin : c.length > stdinCapBytes
      · simp only [hstin, ↓reduceIte]
        exact cliRunPlacedSig_of_strict_f3_sampleNtt_stdinOverCap (hext W) H hmainW
          (cliInputsOk_pqRecvInputs WP p c rc) (inputsLoadable_pqRecvInputs WP p c rc hp)
          (isStdinOverCap_pqRecvInputs WP p c rc hstin) (hNS _ hiDom)
      · simp only [hstin, ↓reduceIte]
        obtain ⟨a, hrun, hobs, hcommit⟩ := hBad c rc hc h2 h3
        exact cliRunPlacedSig_of_strict_f3_sampleNtt_call_obs (hext W) H hmainW
          (cliInputsOk_pqRecvInputs WP p c rc) (inputsLoadable_pqRecvInputs WP p c rc hp)
          hrun (not_isSendOverCap_pqRecvInputs WP p c rc)
          (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)) hobs
          (coinsReadable_pqRecvInputs WP p c rc) hcommit (hNS _ hiDom)
  · intro st hst x g hsess m rc hm hnomatch
    obtain ⟨Run, hmainW, hclause⟩ :=
      hover H.base547NeZero X W hAesE hAesD hX hPub hF512 hEnc hDec hK
    have hiDom : CliPqxdhInputs WP (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) :=
      ⟨st, hst, Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rc, hm, rfl⟩)))⟩
    by_cases hstin : (wirePrekey :: m.bytes).length > stdinCapBytes
    · simp only [hstin, ↓reduceIte]
      exact cliRunPlacedSig_of_strict_f3_sampleNtt_stdinOverCap (hext W) H hmainW
        (cliInputsOk_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
        (inputsLoadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hst)
        (isStdinOverCap_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hstin) (hNS _ hiDom)
    · simp only [hstin, ↓reduceIte]
      obtain ⟨a, hrun, hobsEx, hcommit⟩ := hclause st hst x g hsess m rc hm hnomatch
      exact cliRunPlacedSig_of_strict_f3_sampleNtt_call_pred (hext W) H hmainW
        (cliInputsOk_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
        (inputsLoadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hst)
        hrun (not_isSendOverCap_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
        (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin))
        hobsEx (coinsReadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc) hcommit (hNS _ hiDom)

/-- Guarded 2-placement `CliPqxdhElfCorrectPlaced` ELF composer,
discharging excused `SampleNTT` divergence via `hStuckDiv`. -/
theorem cliPqxdhElfCorrectPlaced_of_f3B2NeedLocksG
    {mpl mmpl : Obj.MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (hext : ∀ W : CliHooks, ExternPreservesNoAllocFailed (cliExternsPlaced mmpl W))
    (H : CliElfF3B2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmain : MainOkCliF3PqB2NeedLocksPlacedAtG mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hover : MainOkCliF3OverB2NeedLocksPlacedAtG mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hStuckDiv : ∀ (W : CliHooks),
      W.C.F = sha256Compress →
      W.C.E = CryptoGames.AES256.aes256Enc →
      W.C.D = CryptoGames.AES256.aes256Dec →
      W.C.X = CryptoGames.RFC7748.x25519Ref →
      W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
      W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
      W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
      W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
      W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
      ∀ (i : Inputs), CliPqxdhInputs ⟨W.C, W.Q⟩ i →
        CliReachesSampleNttStuckPlaced mpl mmpl elf W i →
        cliRunPlacedSig mpl mmpl elf W i = none) :
    CliPqxdhElfCorrectPlaced mpl mmpl elf := by
  refine ⟨H.codeMatches, fun X => ?_⟩
  let W : CliHooks := ⟨realCrypto, realPqxdhPrims⟩
  have hF : W.C.F = sha256Compress := rfl
  have hAesE : W.C.E = CryptoGames.AES256.aes256Enc := rfl
  have hAesD : W.C.D = CryptoGames.AES256.aes256Dec := rfl
  have hX : W.C.X = CryptoGames.RFC7748.x25519Ref := rfl
  have hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef := rfl
  have hF512 : W.Q.F512 = CryptoGames.SHA512.sha512CompressState := rfl
  have hEnc : W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec := rfl
  have hDec : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec := rfl
  have hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental := rfl
  let WP : PEParams := ⟨W.C, W.Q⟩
  have hSD := hStuckDiv W hF hAesE hAesD hX hPub hF512 hEnc hDec hK
  refine ⟨?_, ?_⟩
  · intro p hp
    obtain ⟨Run, hmainW, hclauses⟩ :=
      hmain H.base547NeZero X W hAesE hAesD hX hPub hF512 hEnc hDec hK
    obtain ⟨hInit, hSend, hWhisper, hPrekey, hBad⟩ := hclauses p hp
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro b t hnone
      have hiDom : CliPqxdhInputs WP (pqInitInputs WP p b t) :=
        ⟨p, hp, Or.inl ⟨hnone, b, t, rfl⟩⟩
      by_cases hStuck : CliReachesSampleNttStuckPlaced mpl mmpl elf W (pqInitInputs WP p b t)
      · exact Or.inr ⟨hSD _ hiDom hStuck, Or.inr hStuck⟩
      · obtain ⟨a, hrun, hobs, hcommit⟩ := hInit b t hnone
        exact outcomeOrExcusedAbort_of_eq
          (cliRunPlacedSig_of_strict_f3_sampleNtt_call_obs (hext W) H hmainW
            (cliInputsOk_pqInitInputs WP p b t) (inputsLoadable_pqInitInputs WP p b t hp)
            hrun (not_isSendOverCap_pqInitInputs WP p b t)
            (not_isStdinOverCap_pqInitInputs WP p b t) hobs
            (coinsReadable_pqInitInputs WP p b t) hcommit hStuck)
    · intro m r hm
      have hiDom : CliPqxdhInputs WP (pqSendInputs WP p m r) :=
        ⟨p, hp, Or.inr (Or.inl ⟨m, r, hm, rfl⟩)⟩
      by_cases hStuck : CliReachesSampleNttStuckPlaced mpl mmpl elf W (pqSendInputs WP p m r)
      · exact Or.inr ⟨hSD _ hiDom hStuck, Or.inr hStuck⟩
      · refine outcomeOrExcusedAbort_of_eq ?_
        by_cases hstin : m.length > stdinCapBytes
        · simp only [hstin, ↓reduceIte]
          exact cliRunPlacedSig_of_strict_f3_sampleNtt_stdinOverCap (hext W) H hmainW
            (cliInputsOk_pqSendInputs WP p m r) (inputsLoadable_pqSendInputs WP p m r hp)
            (isStdinOverCap_pqSendInputs WP p m r hstin) hStuck
        · simp only [hstin, ↓reduceIte]
          have hnstin : ¬ IsStdinOverCap (pqSendInputs WP p m r) :=
            not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)
          by_cases hovc : m.length > maxPlaintextBytes
          · simp only [hovc, ↓reduceIte]
            exact cliRunPlacedSig_of_strict_f3_sampleNtt_sendOverCap (hext W) H hmainW
              (cliInputsOk_pqSendInputs WP p m r) (inputsLoadable_pqSendInputs WP p m r hp)
              (isSendOverCap_pqSendInputs WP p m r (by unfold maxPlaintextBytes at hovc; exact hovc))
              hnstin (coinsReadable_pqSendInputs WP p m r) hStuck
          · simp only [hovc, ↓reduceIte]
            obtain ⟨a, hrun, hobs, hcommit⟩ := hSend m r hm
            exact cliRunPlacedSig_of_strict_f3_sampleNtt_call_obs (hext W) H hmainW
              (cliInputsOk_pqSendInputs WP p m r) (inputsLoadable_pqSendInputs WP p m r hp)
              hrun
              (not_isSendOverCap_of_stdin_le
                (by simp only [pqSendInputs, pqInputs]; unfold maxPlaintextBytes at hovc; omega))
              hnstin hobs (coinsReadable_pqSendInputs WP p m r) hcommit hStuck
    · intro c rc hc
      have hiDom : CliPqxdhInputs WP (pqRecvInputs WP p (wireWhisper :: c) rc) :=
        ⟨p, hp, Or.inr (Or.inr (Or.inl ⟨c, rc, hc, rfl⟩))⟩
      by_cases hStuck :
          CliReachesSampleNttStuckPlaced mpl mmpl elf W (pqRecvInputs WP p (wireWhisper :: c) rc)
      · exact Or.inr ⟨hSD _ hiDom hStuck, Or.inr hStuck⟩
      · refine outcomeOrExcusedAbort_of_eq ?_
        by_cases hstin : (wireWhisper :: c).length > stdinCapBytes
        · simp only [hstin, ↓reduceIte]
          exact cliRunPlacedSig_of_strict_f3_sampleNtt_stdinOverCap (hext W) H hmainW
            (cliInputsOk_pqRecvInputs WP p (wireWhisper :: c) rc)
            (inputsLoadable_pqRecvInputs WP p (wireWhisper :: c) rc hp)
            (isStdinOverCap_pqRecvInputs WP p (wireWhisper :: c) rc hstin) hStuck
        · simp only [hstin, ↓reduceIte]
          obtain ⟨a, hrun, hobs, hcommit⟩ := hWhisper c rc hc
          exact cliRunPlacedSig_of_strict_f3_sampleNtt_call_obs (hext W) H hmainW
            (cliInputsOk_pqRecvInputs WP p (wireWhisper :: c) rc)
            (inputsLoadable_pqRecvInputs WP p (wireWhisper :: c) rc hp)
            hrun (not_isSendOverCap_pqRecvInputs WP p (wireWhisper :: c) rc)
            (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)) hobs
            (coinsReadable_pqRecvInputs WP p (wireWhisper :: c) rc) hcommit hStuck
    · intro m rc hm hmatch
      have hiDom : CliPqxdhInputs WP (pqRecvInputs WP p (wirePrekey :: m.bytes) rc) :=
        ⟨p, hp, Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rc, hm, rfl⟩)))⟩
      by_cases hStuck :
          CliReachesSampleNttStuckPlaced mpl mmpl elf W (pqRecvInputs WP p (wirePrekey :: m.bytes) rc)
      · exact Or.inr ⟨hSD _ hiDom hStuck, Or.inr hStuck⟩
      · refine outcomeOrExcusedAbort_of_eq ?_
        by_cases hstin : (wirePrekey :: m.bytes).length > stdinCapBytes
        · simp only [hstin, ↓reduceIte]
          exact cliRunPlacedSig_of_strict_f3_sampleNtt_stdinOverCap (hext W) H hmainW
            (cliInputsOk_pqRecvInputs WP p (wirePrekey :: m.bytes) rc)
            (inputsLoadable_pqRecvInputs WP p (wirePrekey :: m.bytes) rc hp)
            (isStdinOverCap_pqRecvInputs WP p (wirePrekey :: m.bytes) rc hstin) hStuck
        · simp only [hstin, ↓reduceIte]
          obtain ⟨a, hrun, hobs, hcommit⟩ := hPrekey m rc hm hmatch
          exact cliRunPlacedSig_of_strict_f3_sampleNtt_call_obs (hext W) H hmainW
            (cliInputsOk_pqRecvInputs WP p (wirePrekey :: m.bytes) rc)
            (inputsLoadable_pqRecvInputs WP p (wirePrekey :: m.bytes) rc hp)
            hrun (not_isSendOverCap_pqRecvInputs WP p (wirePrekey :: m.bytes) rc)
            (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)) hobs
            (coinsReadable_pqRecvInputs WP p (wirePrekey :: m.bytes) rc) hcommit hStuck
    · intro c rc hc h2 h3
      have hiDom : CliPqxdhInputs WP (pqRecvInputs WP p c rc) :=
        ⟨p, hp, Or.inr (Or.inr (Or.inr (Or.inr ⟨c, rc, hc, h2, h3, rfl⟩)))⟩
      by_cases hStuck : CliReachesSampleNttStuckPlaced mpl mmpl elf W (pqRecvInputs WP p c rc)
      · exact Or.inr ⟨hSD _ hiDom hStuck, Or.inr hStuck⟩
      · refine outcomeOrExcusedAbort_of_eq ?_
        by_cases hstin : c.length > stdinCapBytes
        · simp only [hstin, ↓reduceIte]
          exact cliRunPlacedSig_of_strict_f3_sampleNtt_stdinOverCap (hext W) H hmainW
            (cliInputsOk_pqRecvInputs WP p c rc) (inputsLoadable_pqRecvInputs WP p c rc hp)
            (isStdinOverCap_pqRecvInputs WP p c rc hstin) hStuck
        · simp only [hstin, ↓reduceIte]
          obtain ⟨a, hrun, hobs, hcommit⟩ := hBad c rc hc h2 h3
          exact cliRunPlacedSig_of_strict_f3_sampleNtt_call_obs (hext W) H hmainW
            (cliInputsOk_pqRecvInputs WP p c rc) (inputsLoadable_pqRecvInputs WP p c rc hp)
            hrun (not_isSendOverCap_pqRecvInputs WP p c rc)
            (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)) hobs
            (coinsReadable_pqRecvInputs WP p c rc) hcommit hStuck
  · intro st hst x g hsess m rc hm hnomatch
    obtain ⟨Run, hmainW, hclause⟩ :=
      hover H.base547NeZero X W hAesE hAesD hX hPub hF512 hEnc hDec hK
    have hiDom : CliPqxdhInputs WP (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) :=
      ⟨st, hst, Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rc, hm, rfl⟩)))⟩
    by_cases hStuck :
        CliReachesSampleNttStuckPlaced mpl mmpl elf W (pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
    · exact Or.inr ⟨hSD _ hiDom hStuck, Or.inr hStuck⟩
    · refine Or.inl ?_
      by_cases hstin : (wirePrekey :: m.bytes).length > stdinCapBytes
      · refine ⟨.exited 2 [] (filesOf (pqRecvInputs WP st (wirePrekey :: m.bytes) rc).files), ?_,
          by simp only [hstin, ↓reduceIte]; rfl⟩
        exact cliRunPlacedSig_of_strict_f3_sampleNtt_stdinOverCap (hext W) H hmainW
          (cliInputsOk_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
          (inputsLoadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hst)
          (isStdinOverCap_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hstin) hStuck
      · obtain ⟨a, hrun, hobsEx, hcommit⟩ := hclause st hst x g hsess m rc hm hnomatch
        obtain ⟨o, ho, hpo⟩ :=
          cliRunPlacedSig_of_strict_f3_sampleNtt_call_pred (hext W) H hmainW
            (cliInputsOk_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
            (inputsLoadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hst)
            hrun (not_isSendOverCap_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
            (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin))
            hobsEx (coinsReadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc) hcommit hStuck
        exact ⟨o, ho, by simp only [hstin, ↓reduceIte]; exact hpo⟩

/-- `hext`-discharged convenience form of `cliPqxdhElfCorrectStrictPlaced2_of_f3B2NeedLocksG`. -/
theorem cliPqxdhElfCorrectStrictPlaced2_of_f3B2NeedLocksG'
    {mpl mmpl : Obj.MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3B2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmain : MainOkCliF3PqB2NeedLocksPlacedAtG mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hover : MainOkCliF3OverB2NeedLocksPlacedAtG mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hNoStuck : ∀ W : CliHooks,
      W.C.E = CryptoGames.AES256.aes256Enc →
      W.C.D = CryptoGames.AES256.aes256Dec →
      W.C.X = CryptoGames.RFC7748.x25519Ref →
      W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
      W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
      W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
      W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
      W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
      ∀ i : Inputs, CliPqxdhInputs ⟨W.C, W.Q⟩ i →
        ¬ CliReachesSampleNttStuckPlaced mpl mmpl elf W i) :
    CliPqxdhElfCorrectStrictPlaced2Aes mpl mmpl elf :=
  cliPqxdhElfCorrectStrictPlaced2_of_f3B2NeedLocksG
    (externPreservesNoAllocFailed_cliExternsPlaced mmpl) H hmain hover hNoStuck

/-- `hext`-discharged convenience form of `cliPqxdhElfCorrectPlaced_of_f3B2NeedLocksG`. -/
theorem cliPqxdhElfCorrectPlaced_of_f3B2NeedLocksG'
    {mpl mmpl : Obj.MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3B2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmain : MainOkCliF3PqB2NeedLocksPlacedAtG mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hover : MainOkCliF3OverB2NeedLocksPlacedAtG mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hStuckDiv : ∀ (W : CliHooks),
      W.C.F = sha256Compress →
      W.C.E = CryptoGames.AES256.aes256Enc →
      W.C.D = CryptoGames.AES256.aes256Dec →
      W.C.X = CryptoGames.RFC7748.x25519Ref →
      W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
      W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
      W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
      W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
      W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
      ∀ (i : Inputs), CliPqxdhInputs ⟨W.C, W.Q⟩ i →
        CliReachesSampleNttStuckPlaced mpl mmpl elf W i →
        cliRunPlacedSig mpl mmpl elf W i = none) :
    CliPqxdhElfCorrectPlaced mpl mmpl elf :=
  cliPqxdhElfCorrectPlaced_of_f3B2NeedLocksG
    (externPreservesNoAllocFailed_cliExternsPlaced mmpl) H hmain hover hStuckDiv

end LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2G
