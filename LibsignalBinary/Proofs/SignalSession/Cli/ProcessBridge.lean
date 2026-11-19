/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.SignalSession.SmDir
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.StackBudget -- proof-setup: allow-public-import
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Repr
import all Init.Data.String.Defs
import LibsignalBinary.Proofs.E2E.Reach.BundleCommon
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Domains
import LibsignalBinary.Proofs.SignalSession.Cli.Main.GamePaths
import LibsignalBinary.Proofs.SignalSession.Cli.ProcessBridgeExec
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliRun
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Process
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Run
import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs
import LibsignalBinary.Proofs.CodeLayout

public section

set_option autoImplicit false
set_option maxRecDepth 200000

/-!
# Whole-Process Symbolic Bridge to `CliRunsTo` and `CliBinaryCorrect`

**Checked by Lean.**

Bridges `Cli.outcome_of_main_cliExterns` (over `Cli.cliProg img (cliExterns W)`, `.Panicked`, and
`Cli.RunAllocFails`) to `CliRunsTo elf W i o` (over `cliProgAbortOnPanic W`, where `.Panicked` maps
to `SIGABRT` via `abortOnPanic`) and `CliBinaryCorrect elf`, together with parametric extern-table
(`cliProgWith`) counterparts.

Note that `steps_cliProg_to_cliProgSig` requires `s0.status = .Running` (satisfied on loaded states
by `loadState_status_running`) so that initial states are preserved by `toSigState`.
-/

namespace CryptoVerification.SignalSession

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalTripleRatchet

/-! ## Program Alignment at `cliBase` -/

/-- Maps `.Panicked` to `.Signaled sigAbrt` (`SIGABRT`, signal `6`), leaving all other statuses unchanged. -/
@[expose] def toSigState (s : State) : State :=
  match s.status with
  | .Panicked => s.setStatus (.Signaled sigAbrt)
  | _ => s

@[simp] theorem abortOnPanic_eq_toSigState (h : State → State) (s : State) :
    abortOnPanic h s = toSigState (h s) := rfl

theorem toSigState_of_ne_panicked {s : State} (h : s.status ≠ .Panicked) :
    toSigState s = s := by
  unfold toSigState
  split
  · rename_i hp; exact absurd hp h
  · rfl

@[simp] theorem toSigState_mem (s : State) : (toSigState s).mem = s.mem := by
  unfold toSigState; split <;> rfl

@[simp] theorem toSigState_symtab (s : State) : (toSigState s).symtab = s.symtab := by
  unfold toSigState; split <;> rfl

@[simp] theorem toSigState_trace (s : State) : (toSigState s).trace = s.trace := by
  unfold toSigState; split <;> rfl

@[simp] theorem toSigState_fs (s : State) : (toSigState s).fs = s.fs := by
  unfold toSigState; split <;> rfl

@[simp] theorem cliInputs_eq_cliProcessInputs (i : Inputs) :
    Cli.cliInputs i = cliProcessInputs i := rfl

/-- Transports `ElfImageRunsTo` across `elf'.loadState inputs = (elf.loadState inputs).map patch`. -/
theorem elfImageRunsTo_of_load_map {elf elf' : ElfImage} {inputs : ProcessInputs}
    {post : ProcessOutcome → Prop} {prog : Program} {patch : State → State}
    (hpatch : elf'.loadState inputs = (elf.loadState inputs).map patch)
    (hraw : ElfImageRunsTo elf' inputs post (oom := fun _ => False) (prog := prog)) :
    ∃ s0, elf.loadState inputs = .ok s0 ∧
      _root_.Arm64.Process.ProcessRunsTo prog (patch s0) post := by
  rcases hraw with ⟨s0', hload', hRuns⟩
  rw [hpatch] at hload'
  cases hload : elf.loadState inputs with
  | error _ =>
    rw [hload] at hload'
    cases hload'
  | ok s0 =>
    rw [hload] at hload'
    simp only [Except.map, Except.ok.injEq] at hload'
    subst hload'
    exact ⟨s0, rfl, hRuns⟩

theorem inputsLoadable_smInputs {C : Crypto} (g : GhostState Bytes) (cmd : Cmd)
    (coins stdin : List (BitVec 8))
    (hg : Reach (spqrOffSessionParams C) g) (hcoins : coins.length ≤ MAX_LFS_FILESIZE) :
    Cli.InputsLoadable (smInputs g cmd coins stdin) := by
  refine ⟨(loadable_smInputs g cmd coins stdin).1, fun f hf =>
    ⟨(loadable_smInputs g cmd coins stdin).2 f hf, ?_⟩⟩
  simp only [smInputs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with h | rfl
  · simp only [dirOfE, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · cases g.party <;> decide +kernel
    · simp [IdentityKey.serialize, PublicKey.serialize, MAX_LFS_FILESIZE]
    · have hlt := Reach.reach_encodeRecord_length_lt_20 C hg
      dsimp [MAX_LFS_FILESIZE]; omega
  · exact hcoins

theorem coinsReadable_smInputs (g : GhostState Bytes) (cmd : Cmd)
    (coins stdin : List (BitVec 8))
    (hcap : coins.length ≤ fileCapBytes := by
      first | decide | simp [HMAC.keyToBytes32, List.Vector.toList_length, initiateTapeLen, fileCapBytes]) :
    Cli.CoinsReadable (smInputs g cmd coins stdin) :=
  Cli.coinsReadable_smInputs g cmd coins stdin hcap

theorem commitOk_smSendModel (C : Crypto) (g : GhostState Bytes) (m : List (BitVec 8)) :
    Cli.CommitOk (smSendInputs g m) (Cli.MainResult.ofAnswer (smSendModel C g m)) := by
  unfold smSendModel
  cases sendModelSpqrOff C g m with
  | none => trivial
  | some r =>
    cases r with
    | none => intro _ h; cases h
    | some p =>
      rcases p with ⟨rec, _⟩
      exact Cli.writeOk_smInputs g _ _ _ rec

theorem commitOk_smRecvModel (C : Crypto) (g : GhostState Bytes) (c : List (BitVec 8))
    (rc : BitVec 256) :
    Cli.CommitOk (smRecvInputs g c rc) (Cli.MainResult.ofAnswer (smRecvModel C g c rc)) := by
  unfold smRecvModel
  cases recvModelSpqrOff C g c rc with
  | none => trivial
  | some r =>
    cases r with
    | none => intro _ h; cases h
    | some p =>
      rcases p with ⟨rec, _⟩
      exact Cli.writeOk_smInputs g _ _ _ rec

theorem cliInputsOk_smSendInputs (g : GhostState Bytes) (m : List (BitVec 8)) :
    Cli.CliInputsOk (smSendInputs g m) := by
  unfold Cli.CliInputsOk PrintableAsciiArg ArgvFitsInitialStack smSendInputs smInputs
  dsimp only
  cases g.party <;> decide

theorem cliInputsOk_smRecvInputs (g : GhostState Bytes) (c : List (BitVec 8)) (rc : BitVec 256) :
    Cli.CliInputsOk (smRecvInputs g c rc) := by
  unfold Cli.CliInputsOk PrintableAsciiArg ArgvFitsInitialStack smRecvInputs smInputs
  dsimp only
  cases g.party <;> decide

/-! ### Cap-Violation Helpers -/

theorem not_isSendOverCap_of_stdin_le {i : Inputs} (h : i.stdin.length ≤ 1_000_000) :
    ¬ Cli.IsSendOverCap i :=
  fun ⟨_, hgt⟩ => Nat.not_lt.mpr h hgt

theorem not_isStdinOverCap_of_stdin_le {i : Inputs} (h : i.stdin.length ≤ stdinCapBytes) :
    ¬ Cli.IsStdinOverCap i :=
  fun ⟨_, hgt⟩ => Nat.not_lt.mpr h hgt

theorem isSendOverCap_smSendInputs (g : GhostState Bytes) (m : List (BitVec 8))
    (h : 1_000_000 < m.length) :
    Cli.IsSendOverCap (smSendInputs g m) := by
  refine ⟨?_, h⟩
  obtain ⟨c, hc, htag⟩ :=
    Cli.MainHops.parseArgs_cmd (.send (partyAddress g.party.other)) rfl
  cases c <;> simp [Cli.MainHops.CallV.tag, Cli.MainHops.cmdTag] at htag
  rename_i peer
  exact ⟨peer, hc⟩

theorem isStdinOverCap_smSendInputs (g : GhostState Bytes) (m : List (BitVec 8))
    (h : stdinCapBytes < m.length) :
    Cli.IsStdinOverCap (smSendInputs g m) := by
  refine ⟨?_, h⟩
  obtain ⟨c, hc, htag⟩ :=
    Cli.MainHops.parseArgs_cmd (.send (partyAddress g.party.other)) rfl
  exact ⟨c, hc, by rw [htag]; simp [Cli.MainHops.cmdTag]⟩

theorem isStdinOverCap_smRecvInputs (g : GhostState Bytes) (c : List (BitVec 8))
    (rc : BitVec 256) (h : stdinCapBytes < (msgTypeWhisper :: c).length) :
    Cli.IsStdinOverCap (smRecvInputs g c rc) := by
  refine ⟨?_, h⟩
  obtain ⟨v, hv, htag⟩ :=
    Cli.MainHops.parseArgs_cmd (.recv (partyAddress g.party.other)) rfl
  exact ⟨v, hv, by rw [htag]; simp [Cli.MainHops.cmdTag]⟩

theorem not_isSendOverCap_smRecvInputs (g : GhostState Bytes) (c : List (BitVec 8))
    (rc : BitVec 256) :
    ¬ Cli.IsSendOverCap (smRecvInputs g c rc) := by
  rintro ⟨⟨peer, hp⟩, -⟩
  obtain ⟨v, hv, htag⟩ :=
    Cli.MainHops.parseArgs_cmd (.recv (partyAddress g.party.other)) rfl
  change Cli.MainHops.parseArgs CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse
    ((Cmd.recv (partyAddress g.party.other)).argv.map bytesOfString) = some (.send peer) at hp
  rw [hp] at hv
  injection hv with heq
  subst heq
  simp [Cli.MainHops.CallV.tag, Cli.MainHops.cmdTag] at htag

theorem isSendOverCap_pqSendInputs (W : PEParams) (st : PqParty) (m : List (BitVec 8))
    (r : List.Vector (BitVec 8) 64) (h : 1_000_000 < m.length) :
    Cli.IsSendOverCap (pqSendInputs W st m r) := by
  refine ⟨?_, h⟩
  obtain ⟨c, hc, htag⟩ :=
    Cli.MainHops.parseArgs_cmd (.send (partyAddress st.party.other)) rfl
  cases c <;> simp [Cli.MainHops.CallV.tag, Cli.MainHops.cmdTag] at htag
  rename_i peer
  exact ⟨peer, hc⟩

theorem not_isSendOverCap_pqInitInputs (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    ¬ Cli.IsSendOverCap (pqInitInputs W st b t) := by
  rintro ⟨_, hgt⟩
  simp [pqInitInputs, pqInputs] at hgt

theorem not_isSendOverCap_pqRecvInputs (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) :
    ¬ Cli.IsSendOverCap (pqRecvInputs W st c rc) := by
  rintro ⟨⟨peer, hp⟩, -⟩
  obtain ⟨v, hv, htag⟩ :=
    Cli.MainHops.parseArgs_cmd (.recv (partyAddress st.party.other)) rfl
  change Cli.MainHops.parseArgs CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse
    ((Cmd.recv (partyAddress st.party.other)).argv.map bytesOfString) = some (.send peer) at hp
  rw [hp] at hv
  injection hv with heq
  subst heq
  simp [Cli.MainHops.CallV.tag, Cli.MainHops.cmdTag] at htag

theorem isStdinOverCap_pqSendInputs (W : PEParams) (st : PqParty) (m : List (BitVec 8))
    (r : List.Vector (BitVec 8) 64) (h : stdinCapBytes < m.length) :
    Cli.IsStdinOverCap (pqSendInputs W st m r) := by
  refine ⟨?_, h⟩
  obtain ⟨c, hc, htag⟩ :=
    Cli.MainHops.parseArgs_cmd (.send (partyAddress st.party.other)) rfl
  exact ⟨c, hc, by rw [htag]; simp [Cli.MainHops.cmdTag]⟩

theorem isStdinOverCap_pqRecvInputs (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) (h : stdinCapBytes < c.length) :
    Cli.IsStdinOverCap (pqRecvInputs W st c rc) := by
  refine ⟨?_, h⟩
  obtain ⟨v, hv, htag⟩ :=
    Cli.MainHops.parseArgs_cmd (.recv (partyAddress st.party.other)) rfl
  exact ⟨v, hv, by rw [htag]; simp [Cli.MainHops.cmdTag]⟩

theorem not_isStdinOverCap_pqInitInputs (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    ¬ Cli.IsStdinOverCap (pqInitInputs W st b t) :=
  not_isStdinOverCap_of_stdin_le (by simp [pqInitInputs, pqInputs])

end CryptoVerification.SignalSession
