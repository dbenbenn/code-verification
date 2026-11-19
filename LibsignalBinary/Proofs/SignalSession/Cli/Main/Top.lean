/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.CliRun
public import LibsignalBinary.Proofs.SpecLemmas.SymtabGhost -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliRunProofDefs
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliRun
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ProcessProofDefs
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.RunProofDefs
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Model -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Process
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Run

/-!
# CLI `main` Result Model, Entry Frame, and Musl Harness Contract

Defines `MainResult`, `MainCase`, `MainCaseB2`, `mainFrame`, `MainEntryFacts`, `MainPost`,
`MuslHarness`, `RunAllocFails`, and `MainResult.Observed` for `extern "C" fn main(argc, argv) -> c_int`
and its composition with musl's `_start`/`exit_group` harness.
-/

public section

set_option warningAsError false

/-! ## `main` -/

namespace CryptoVerification.SignalSession.Cli

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

/-! ### Inputs -/

/-- Process inputs for one CLI invocation on `i`, with `argv[0] = "signal-session"` followed by `i.argv`. -/
@[expose] def cliInputs (i : Inputs) : ProcessInputs :=
  processInputs ("libsignal-cli" :: i.argv) i.stdin i.files i.dirs

/-- Input precondition for musl startup: printable ASCII arguments fitting the initial stack (`ArgvFitsInitialStack`). -/
@[expose] def CliInputsOk (i : Inputs) : Prop := (∀ a ∈ i.argv, PrintableAsciiArg a) ∧ ArgvFitsInitialStack i.argv

/-- Loader admissibility predicate: every directory and file path satisfies `LoadablePath`, and every initial regular file has size at most `MAX_LFS_FILESIZE` (`2 ^ 63 - 1`). -/
@[expose] def InputsLoadable (i : Inputs) : Prop :=
  (∀ d ∈ i.dirs, LoadablePath d) ∧
  (∀ f ∈ i.files, LoadablePath f.1 ∧ f.2.length ≤ MAX_LFS_FILESIZE)

/-- Static ELF well-formedness and `brk` bound below the base of the 8 MiB stack (`DEV-CLI7`). -/
@[expose] def ElfStaticOk (elf : ElfImage) : Prop :=
  elf.WellFormed = true ∧ elf.brkStart.toNat ≤ defaultStackTop.toNat - 8388608

/-! ### `main`'s result -/

/-- Outcome of `main` on a single call: panic (`abort`), or return code `code` after committing `writes` in order and writing `out` to stdout. -/
inductive MainResult where
  | abort
  | ret (code : Nat) (writes : List (String × List (BitVec 8))) (out : List (BitVec 8))

/-- Result of `run`: `none` on panic, `some none` on reject, or `some (some (writes, out))` on accept. -/
abbrev RunAnswer := Option (Option (List (String × List (BitVec 8)) × List (BitVec 8)))

/-- Maps `run`'s `RunAnswer` to `MainResult` (`abort` on `none`, exit `1` on reject, exit `0` committing `writes` and printing `out` on accept). -/
@[expose] def MainResult.ofAnswer : RunAnswer → MainResult
  | none => .abort
  | some none => .ret 1 [] []
  | some (some (w, out)) => .ret 0 w out

/-- `"coins"` is not a directory in the initial file system and any regular file there has size at most `fileCapBytes`, so `read_file("coins")` returns `Ok`. -/
@[expose] def CoinsReadable (i : Inputs) : Prop :=
  (initFsState (cliInputs i)).files "coins" ≠ some .dir ∧
    ∀ bs, (initFsState (cliInputs i)).files "coins" = some (.file bs) → bs.length ≤ fileCapBytes

/-- `p` is a valid non-directory path whose proper ancestors are all directories in the initial file system, so `write_file(p, _)` returns `Ok`. -/
@[expose] def WriteOk (i : Inputs) (p : String) : Prop :=
  PathOk p = true ∧ (initFsState (cliInputs i)).files p ≠ some .dir ∧
    (∀ q ∈ ancestors p, (initFsState (cliInputs i)).files q = some .dir) ∧
    ∀ pref ∈ (FsPath.nonEmptyPrefixes (normalizePath p)).dropLast,
      (initFsState (cliInputs i)).entries pref = some .dir

/-- Every committed write in `r` satisfies `WriteOk i`. -/
@[expose] def CommitOk (i : Inputs) : MainResult → Prop
  | .ret _ w _ => ∀ pw ∈ w, WriteOk i pw.1
  | .abort => True

/-- Expected `MainResult` for input `i`: `usage` (exit `2` with no I/O when `i.argv` fails CLI grammar parsing) or `call` (`run` yields `r` with `CoinsReadable` and `CommitOk`). -/
inductive MainCase (Run : Inputs → RunAnswer → Prop) : Inputs → MainResult → Prop
  | usage {i : Inputs} : (∀ a ∈ i.argv, PrintableAsciiArg a) → ArgvShapeOk i.argv = false →
      MainCase Run i (.ret 2 [] [])
  | call {i : Inputs} {r : RunAnswer} : Run i r → CoinsReadable i →
      CommitOk i (MainResult.ofAnswer r) → MainCase Run i (MainResult.ofAnswer r)

theorem MainCase.commitOk {Run : Inputs → RunAnswer → Prop} {i : Inputs} {r : MainResult}
    (h : MainCase Run i r) : CommitOk i r := by
  cases h with
  | usage _ _ => intro _ hp; cases hp
  | call _ _ hc => exact hc

theorem MainResult.ofAnswer_code_le {a : RunAnswer} {code : Nat}
    {w : List (String × List (BitVec 8))} {out : List (BitVec 8)}
    (h : MainResult.ofAnswer a = .ret code w out) : code ≤ 2 := by
  match a, h with
  | none, h => cases h
  | some none, h => cases h; decide
  | some (some _), h => cases h; decide

/-- Every `MainCase` return code is at most `2`. -/
theorem MainCase.code_le {Run : Inputs → RunAnswer → Prop} {i : Inputs} {r : MainResult}
    (hc : MainCase Run i r) {code : Nat} {w : List (String × List (BitVec 8))}
    {out : List (BitVec 8)} (hr : r = .ret code w out) : code ≤ 2 := by
  cases hc with
  | usage _ _ => cases hr; decide
  | call _ _ _ => exact MainResult.ofAnswer_code_le hr

/-- Expected `MainResult` with bounded `read_stdin` (`StdinOverCap`, exit `2`) and early send-plaintext length check (`SendOverCap`, exit `1`). -/
inductive MainCaseB2 (Run : Inputs → RunAnswer → Prop)
    (SendOverCap StdinOverCap : Inputs → Prop) : Inputs → MainResult → Prop
  | usage {i : Inputs} : (∀ a ∈ i.argv, PrintableAsciiArg a) → ArgvShapeOk i.argv = false →
      MainCaseB2 Run SendOverCap StdinOverCap i (.ret 2 [] [])
  | stdinOverCap {i : Inputs} : StdinOverCap i →
      MainCaseB2 Run SendOverCap StdinOverCap i (.ret 2 [] [])
  | sendOverCap {i : Inputs} : SendOverCap i → ¬ StdinOverCap i → CoinsReadable i →
      MainCaseB2 Run SendOverCap StdinOverCap i (.ret 1 [] [])
  | call {i : Inputs} {r : RunAnswer} : Run i r → ¬ SendOverCap i → ¬ StdinOverCap i →
      CoinsReadable i → CommitOk i (MainResult.ofAnswer r) →
      MainCaseB2 Run SendOverCap StdinOverCap i (MainResult.ofAnswer r)

theorem MainCaseB2.commitOk {Run : Inputs → RunAnswer → Prop}
    {SendOverCap StdinOverCap : Inputs → Prop}
    {i : Inputs} {r : MainResult} (h : MainCaseB2 Run SendOverCap StdinOverCap i r) :
    CommitOk i r := by
  cases h with
  | usage _ _ => intro _ hp; cases hp
  | stdinOverCap _ => intro _ hp; cases hp
  | sendOverCap _ _ _ => intro _ hp; cases hp
  | call _ _ _ _ hc => exact hc

/-- Every `MainCaseB2` return code is at most `2`. -/
theorem MainCaseB2.code_le {Run : Inputs → RunAnswer → Prop}
    {SendOverCap StdinOverCap : Inputs → Prop}
    {i : Inputs} {r : MainResult} (hc : MainCaseB2 Run SendOverCap StdinOverCap i r)
    {code : Nat} {w : List (String × List (BitVec 8))}
    {out : List (BitVec 8)} (hr : r = .ret code w out) : code ≤ 2 := by
  cases hc with
  | usage _ _ => cases hr; decide
  | stdinOverCap _ => cases hr; decide
  | sendOverCap _ _ _ => cases hr; decide
  | call _ _ _ _ _ => exact MainResult.ofAnswer_code_le hr

/-- Send-plaintext cap violation: `argv` parses as `send <peer>` and `1_000_000 < i.stdin.length`. -/
@[expose] def IsSendOverCap (i : Inputs) : Prop :=
  (∃ peer, MainHops.parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.send peer)) ∧
    1_000_000 < i.stdin.length

/-- Standard-input cap violation: `argv` parses as `send` or `recv` and `stdinCapBytes < i.stdin.length`. -/
@[expose] def IsStdinOverCap (i : Inputs) : Prop :=
  (∃ c, MainHops.parseArgs uuidTryParse (i.argv.map bytesOfString) = some c ∧ 1 < c.tag) ∧
    stdinCapBytes < i.stdin.length

/-! ### `mainSpec` -/

/-- NUL-terminated byte string `s` at `p`. -/
@[expose] def cStrAt (p : BitVec 64) (s : List (BitVec 8)) : SepProp := p ↦ₛ (s ++ [0#8])

/-- NULL-terminated C `argv` pointer array at `a`, each entry pointing to its NUL-terminated string. -/
@[expose] def argvAt : BitVec 64 → List (List (BitVec 8)) → SepProp
  | a, [] => a ↦₆₄ 0#64
  | a, s :: ss => ∃∗ p, (a ↦₆₄ p) ∗ cStrAt p s ∗ argvAt (a + 8#64) ss

/-- Entry separation-logic frame for `main`: `argv` at `x1`, `stk` stack bytes below `sp`, the allocator pool, and writable statics `Statics`. -/
@[expose] def mainFrame (A : RustAlloc) (stk : Nat) (Statics : SepProp) (i : Inputs) (s : State) :
    SepProp :=
  argvAt (s.readReg64 .x1) (("libsignal-cli" :: i.argv).map bytesOfString) ∗
    stackAt s.sp stk ∗ A.pool ∗ Statics

/-- Image-base offset of `signal_session::coins::NEXT.0` (`.img.data`, 8 bytes). -/
abbrev coinsNextOff : BitVec 64 := 0x9a050#64

/-- Image-base offset of `signal_session::coins::LEFT.0` (`.img.bss`, 8 bytes). -/
abbrev coinsLeftOff : BitVec 64 := 0x9a058#64

/-- Register and state invariants at `main` entry: `w0 = argc`, initial file system, and empty trace. -/
@[expose] def MainEntryFacts (i : Inputs) (s : State) : Prop :=
  (s.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 (i.argv.length + 1) ∧
    s.fs = initFsState (cliInputs i) ∧ s.trace = []

/-- Postcondition of a normal return from `main`: `w0 = code`, committed writes applied in order, and stdout `out`. -/
@[expose] def MainPost (r : MainResult) (s0 sf : State) : Prop :=
  ∃ code w out, r = .ret code w out ∧
    (sf.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 code ∧
    sf.fs.files = (writeAll s0.fs w).files ∧
    ProcessOutcome.traceStreamBytes .stdout sf.trace = out
where
  /-- Applies each `(path, bytes)` write in `ws` to `fs` in order. -/
  writeAll (fs : FsState) (ws : List (String × List (BitVec 8))) : FsState :=
    ws.foldl (fun fs w => fs.setFile w.1 (some (.file w.2))) fs

structure MainGhost where
  i : Inputs
  r : MainResult

abbrev mainName : String := "main"

/-! ### Musl Startup and Exit -/

/-- Contract for musl's `_start` startup to `mainPc` and `exit_group` shutdown from `main`'s return, preserving the file system and trace and converting `w0` to `.Exited (signExtend 64 w0)`. -/
@[expose] def MuslHarness (elf : ElfImage) (P : Program) (mainPc : BitVec 64) (Fr : SepProp)
    (Ok : Inputs → Prop) (MainPre : Inputs → State → SepProp) : Prop :=
  ElfStaticOk elf → ∀ i, Ok i → ∃ s0 sm,
    elf.loadState (cliInputs i) = .ok s0 ∧ Steps P s0 sm ∧
    sm.pc = mainPc ∧ sm.status = .Running ∧ sm.spAligned = true ∧
    sm.fs = s0.fs ∧ sm.trace = s0.trace ∧
    (sm.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 (i.argv.length + 1) ∧
    (sm.mem ⊨ MainPre i sm ∗ Fr) ∧
    ∀ sr, Steps P sm sr → Returned sm sr → (sr.mem ⊨ stackAt sm.sp 48 ∗ Fr ∗ anyHeap) →
      ∃ sx, Steps P sr sx ∧
        sx.status = .Exited (((sr.readReg64 .x0).setWidth 32).signExtend 64) ∧
        sx.fs = sr.fs ∧ sx.trace = sr.trace

/-- Every PC in `[lo, hi)` has `P.externAt? pc = none`. -/
@[expose] def MuslHookFree (P : Program) (lo hi : BitVec 64) : Prop :=
  ∀ pc, lo ≤ pc → pc < hi → (P.externAt? pc).isNone = true

/-! ### Process Composition -/

/-- Some execution of `P` from the loaded state on `i` records an allocation failure. -/
@[expose] def RunAllocFails (elf : ElfImage) (P : Program) (i : Inputs) : Prop :=
  ∃ s0 s, elf.loadState (cliInputs i) = .ok s0 ∧ Steps P s0 s ∧ allocFailedEvent ∈ s.trace

/-- Relates a `MainResult` to the process-level `ProcessResult` (`abort` maps to `.aborted`; `ret code writes out` maps to exit `code`, stdout `out`, and `filesOf (files ++ writes)`). -/
@[expose] def MainResult.Observed (files : List (String × List (BitVec 8))) :
    MainResult → ProcessResult → Prop
  | .abort, .aborted => True
  | .ret code w out, .exited c o fs =>
      c = BitVec.ofNat 64 code ∧ o = out ∧ fsView fs = filesOf (files ++ w)
  | _, _ => False

theorem loadState_fs_trace {elf : ElfImage} {inputs : ProcessInputs} {s0 : State}
    (h : elf.loadState inputs = .ok s0) : s0.fs = initFsState inputs ∧ s0.trace = [] := by
  dsimp only [ElfImage.loadState, Bind.bind, Pure.pure, Except.bind, Except.pure] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · cases h
          exact ⟨rfl, rfl⟩

theorem mem_stdioPaths (q : String) :
    q ∈ stdioPaths ↔ q = "<stdin>" ∨ q = "<stdout>" ∨ q = "<stderr>" := by
  simp [stdioPaths]

theorem fsView_congr {fs fs' : FsState} (h : fs.files = fs'.files) :
    fsView fs = fsView fs' := by
  funext q
  simp only [fsView, h]

private theorem writeAll_entries_congr {a b : FsState}
    (ws : List (String × List (BitVec 8))) {k : FsPath} (h : a.entries k = b.entries k) :
    (MainPost.writeAll a ws).entries k = (MainPost.writeAll b ws).entries k := by
  induction ws generalizing a b with
  | nil => exact h
  | cons w ws ih =>
    apply ih
    simp only [FsState.setFile, FsState.setEntry]
    split
    · rfl
    · exact h

private theorem writeOk_disjoint_prefix {i : Inputs} {p p' : String}
    (hp : WriteOk i p) (hp' : WriteOk i p')
    {pref : FsPath} (hpref : pref ∈ (FsPath.nonEmptyPrefixes (normalizePath p')).dropLast) :
    pref ≠ normalizePath p := by
  intro heq
  have he : (initFsState (cliInputs i)).entries (normalizePath p) = some .dir :=
    heq ▸ hp'.2.2.2 pref hpref
  have hf : (initFsState (cliInputs i)).files p = some .dir := by
    rw [files_eq_entries]
    split
    · rfl
    · exact he
  exact hp.2.1 hf

private theorem sameFiles_setEntry_dir_right {a b : FsState} (h : SameFiles a b)
    {pref : FsPath} (hdir : a.entries pref = some .dir) :
    SameFiles a (b.setEntry pref (some .dir)) := by
  intro k
  simp only [FsState.setEntry]
  split
  · rename_i hk
    rw [beq_iff_eq.mp hk, hdir]
  · exact h k

private theorem sameFiles_foldl_dir_right {a b : FsState} (h : SameFiles a b)
    {l : List FsPath} (hl : ∀ pref ∈ l, a.entries pref = some .dir) :
    SameFiles a (l.foldl (fun acc pref => acc.setEntry pref (some .dir)) b) := by
  induction l generalizing b with
  | nil => exact h
  | cons pref ls ih =>
    exact ih (sameFiles_setEntry_dir_right h (hl pref (.head _)))
      (fun p hp => hl p (.tail _ hp))

private theorem sameFiles_writeAll_filesFold {a b : FsState}
    (ws : List (String × List (BitVec 8))) (h : SameFiles a b)
    (hdir : ∀ w ∈ ws, ∀ pref ∈ (FsPath.nonEmptyPrefixes (normalizePath w.1)).dropLast,
      a.entries pref = some .dir)
    (hne : ∀ w ∈ ws, ∀ w' ∈ ws,
      ∀ pref ∈ (FsPath.nonEmptyPrefixes (normalizePath w'.1)).dropLast,
      pref ≠ normalizePath w.1) :
    SameFiles (MainPost.writeAll a ws) (filesFold ws b) := by
  induction ws generalizing a b with
  | nil => exact h
  | cons w ws ih =>
    obtain ⟨p, bs⟩ := w
    apply ih
    · exact (sameFiles_foldl_dir_right h (hdir (p, bs) (.head _))).setEntry
        (normalizePath p) (some (.file bs))
    · intro w' hw' pref hpref
      have hne' : pref ≠ normalizePath p := hne (p, bs) (.head _) w' (.tail _ hw') pref hpref
      simp only [FsState.setFile, FsState.setEntry]
      split
      · rename_i heq
        exact absurd (beq_iff_eq.mp heq) hne'
      · exact hdir w' (.tail _ hw') pref hpref
    · intro w1 hw1 w2 hw2 pref hpref
      exact hne w1 (.tail _ hw1) w2 (.tail _ hw2) pref hpref

private theorem filesFold_append (xs ys : List (String × List (BitVec 8))) (a : FsState) :
    filesFold (xs ++ ys) a = filesFold ys (filesFold xs a) := by
  unfold filesFold
  rw [List.foldl_append]

/-- `fsView` after applying valid writes `ws` to `initFsState (cliInputs i)` equals `filesOf (i.files ++ ws)`. -/
theorem fsView_writeAll_initFsState (i : Inputs) (ws : List (String × List (BitVec 8)))
    (hw : ∀ pw ∈ ws, WriteOk i pw.1) :
    fsView (MainPost.writeAll (initFsState (cliInputs i)) ws) = filesOf (i.files ++ ws) := by
  funext q
  unfold filesOf fsView
  split
  · rfl
  · rename_i hq
    show fileOfEntry ((MainPost.writeAll (initFsState (cliInputs i)) ws).files q) =
      fileOfEntry ((initFsState { files := i.files ++ ws }).files q)
    simp only [FsState.files, FsState.getEntry]
    split
    · rfl
    · rw [writeAll_entries_congr ws (initFsState_entries (cliInputs i) (normalizePath q) hq),
        initFsState_entries { files := i.files ++ ws } (normalizePath q) hq,
        filesFold_append]
      exact sameFiles_writeAll_filesFold ws
        (SameFiles.filesFold_same
          (NoFiles.sameFiles (NoFiles.dirsFold_none i.dirs) (NoFiles.dirsFold_none [])) i.files)
        (fun w hw_mem pref hpref => (hw w hw_mem).2.2.2 pref hpref)
        (fun w hw1 w' hw2 _ hpref => writeOk_disjoint_prefix (hw w hw1) (hw w' hw2) hpref)
        (normalizePath q)

theorem signExtend_ofNat_small {code : Nat} (h : code ≤ 2) :
    (BitVec.ofNat 32 code).signExtend 64 = BitVec.ofNat 64 code := by
  rcases (by omega : code = 0 ∨ code = 1 ∨ code = 2) with rfl | rfl | rfl <;> decide

theorem exit_frame {m : Memory} {sp : BitVec 64} {stk : Nat} {Fr : SepProp}
    (hstk : 48 ≤ stk) (hstk' : stk ≤ 2 ^ 64) (h : m ⊨ (stackAt sp stk ∗ anyHeap) ∗ Fr) :
    m ⊨ stackAt sp 48 ∗ Fr ∗ anyHeap := by
  have hsplit := stackAt_split_bottom sp 48 (stk - 48) (by omega)
  rw [show 48 + (stk - 48) = stk by omega] at hsplit
  rw [hsplit] at h
  refine Satisfies.mono ?_ h
  have e : ((memRegion (sp - BitVec.ofNat 64 stk) (stk - 48) ∗ stackAt sp 48) ∗ anyHeap) ∗ Fr =
      stackAt sp 48 ∗ Fr ∗ (memRegion (sp - BitVec.ofNat 64 stk) (stk - 48) ∗ anyHeap) := by
    ac_rfl
  rw [e]
  exact sepConj_mono_right (sepConj_mono_right (entails_anyHeap _))

/-- Under `MainResult.Observed`, `toOutcome` of `MainResult.ofAnswer a` equals `observe files a`. -/
theorem MainResult.observed_ofAnswer (files : List (String × List (BitVec 8))) (a : RunAnswer)
    (res : ProcessResult) (h : MainResult.Observed files (MainResult.ofAnswer a) res) :
    toOutcome res = observe files a := by
  cases a with
  | none =>
    cases res with
    | exited _ _ _ => cases h
    | aborted => rfl
  | some a' =>
    cases a' with
    | none =>
      cases res with
      | exited c o fs =>
        obtain ⟨rfl, rfl, hfs⟩ := h
        simp only [toOutcome, observe, List.append_nil] at hfs ⊢
        rw [hfs]
        rfl
      | aborted => cases h
    | some p =>
      obtain ⟨w, out⟩ := p
      cases res with
      | exited c o fs =>
        obtain ⟨rfl, rfl, hfs⟩ := h
        simp only [toOutcome, observe]
        rw [hfs]
        rfl
      | aborted => cases h

theorem MainResult.observed_usage (files : List (String × List (BitVec 8))) (res : ProcessResult)
    (h : MainResult.Observed files (.ret 2 [] []) res) :
    toOutcome res = .exited 2 [] (filesOf files) := by
  cases res with
  | exited c o fs =>
    obtain ⟨rfl, rfl, hfs⟩ := h
    simp only [toOutcome, List.append_nil] at hfs ⊢
    rw [hfs]
    rfl
  | aborted => cases h

theorem MainResult.observed_sendOverCap (files : List (String × List (BitVec 8)))
    (res : ProcessResult) (h : MainResult.Observed files (.ret 1 [] []) res) :
    toOutcome res = .exited 1 [] (filesOf files) :=
  MainResult.observed_ofAnswer files (some none) res h

end CryptoVerification.SignalSession.Cli
