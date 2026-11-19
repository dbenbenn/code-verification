/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Placed.CliPlainPanPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2G -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2GWithF -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3ExternNoAllocFail
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.PlacedOomRecovery2
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2EntryGuard
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemFirstStopTransfer
import LibsignalBinary.Proofs.SignalSession.Cli.ProcessBridgePq
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Process
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Run
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.RunProofDefs
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Kdf
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq

/-!
# Plain-Memory Guarded Two-Placement ELF Composers

Plain-memory (`elf.loadState` without `cliTokenPatchPlaced` or `patchElfTokensPlacedAt`)
counterparts of `PlacedOomRecovery2`, `T2NoOomBridge`, `CliStrictPlaced2G`, and
`CliStrictPlaced2GWithF` over `cliRunPlainPanPlacedSig`, `CliReachesOOMPlainPanPlaced`, and
`CliReachesSampleNttStuckPlainPanPlaced`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.PlainPlacedComposer

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames.HMAC (ShaState)
open CryptoGames.LibsignalSession (GhostState)
open CryptoVerification.E2E
  (Bytes PEParams PreKeyBundleFields PreKeyMessageFields RecordExtras UnreachedPqxdhPrimitives
   initiateTapeLen wirePrekey wireWhisper)
open CryptoVerification.LibsignalSpqrV1 (sha256Compress)
open CryptoVerification.RustHeap (allocFailedEvent)
open CryptoVerification.SignalSession
  (CliHooks CliPqxdhInputs CliSpecPqxdh CliSpecPqxdhNoMatch CliSpecPqxdhNoMatchOrExcusedAbort
   CliSpecPqxdhOrExcusedAbort Inputs Outcome OutcomeMatchesModelExceptPath OutcomeOrExcusedAbort
   PqParty PqSessionMatches PqxdhPartyInSpecDomain cliExternsPlaced cliInputsOk_pqInitInputs
   cliInputsOk_pqRecvInputs cliInputsOk_pqSendInputs cliProcessInputs coinsReadable_pqInitInputs
   coinsReadable_pqRecvInputs coinsReadable_pqSendInputs filesOf inputsLoadable_pqInitInputs
   inputsLoadable_pqRecvInputs inputsLoadable_pqSendInputs isSendOverCap_pqSendInputs
   isStdinOverCap_pqRecvInputs isStdinOverCap_pqSendInputs loadState_status_running
   maxPlaintextBytes not_isSendOverCap_of_stdin_le not_isSendOverCap_pqInitInputs
   not_isSendOverCap_pqRecvInputs not_isStdinOverCap_of_stdin_le not_isStdinOverCap_pqInitInputs
   observe outcomeOf outcomeOf_eq_aborted outcomeOf_eq_exited partyAddress pqInitInputs pqInitModel
   pqInputs pqRecvInputs pqRecvPrekeyModel pqRecvWhisperModel pqSendInputs pqSendModel
   pqxdhExpectedOutcome realCrypto realPEParams realPqxdhPrims sessionFile stdinCapBytes)
open CryptoVerification.SignalSession.Cli
  (CliInputsOk CoinsReadable CommitOk InputsLoadable IsSendOverCap IsStdinOverCap
   MainCaseB2 MainResult RunAnswer fsView_congr fsView_writeAll_initFsState
   loadState_fs_trace signExtend_ofNat_small)
open LibsignalBinary.Heap (BudgetLimits)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced
  (CliElfCodeMatchesPlaced cliHookTablePlaced)
open LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced.Placed (cliProgPlacedSig)
open LibsignalBinary.Proofs.Placed.CliPlainPanPlaced
  (CliPqxdhElfCorrectPlainPanPlaced CliReachesOOMPlainPanPlaced
   CliReachesSampleNttStuckPlainPanPlaced CliRunsToPlainPanPlaced cliRunPlainPanPlacedSig
   cliRunsToPlainPanPlaced_of_eq_some)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
  (CliElfExtPlainB2NeedLocksAssumptions2 MuslHarnessFineNeedLocksGuardedPerInput
   b2MainEntryPreFine b2MainSpecTightNeedLocksFineAt cliBudgetLimits exit_frame_needLocks_n)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2G (F3SampleNttEntryGuard)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2GWithF
  (MainOkCliF3OverB2NeedLocksPlacedAtGWithF MainOkCliF3PqB2NeedLocksPlacedAtGWithF)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3ExternNoAllocFail
  (ExternPreservesNoAllocFailed externPreservesNoAllocFailed_cliExternsPlaced
   externPreservesNoAllocFailed_none steps_preserves_no_allocFailed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
  (cliProgExtPlacedAt cliRunPlainExtOnInputsSigAt_eq_some
   cliRunPlainExtPlacedSigAt_cliExternsPlaced_eq
   cliRunsToPlainExtOnInputsAt_of_outcomeOf_observed
   cliRunsToPlainExtOnInputsAt_of_outcomeOf_usage cliStaticsPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.PlacedOomRecovery2
  (cliSpecPqxdhNoMatchOrExcusedAbort_of_strict cliSpecPqxdhNoMatch_of_orExcusedAbort_noOOM
   cliSpecPqxdhOrExcusedAbort_of_strict outcomeOrExcusedAbort_eq_of_not_exc
   outcomeOrExcusedAbort_of_eq outcomeOrExcusedAbort_of_not_exc)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG (withEntryGuard)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2EntryGuard (F3C2EntryGuard)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemFirstStopTransfer
  (RealNeverViolatesSampleNtt mlKemSampleNttStuckAt_iff realNeverViolatesFamily_of_startup
   steps_cliProgPlacedSig_of_running)

/-! ## 1. Plain-Memory ELF-Correctness Predicates and OOM Refutation -/

/-- `F`-parameterized plain-memory ELF correctness abbreviation (`rfl`-equal to
`CliPqxdhElfCorrectPlainPanPlaced` at `F = sha256Compress` once instantiated at `realCrypto`). -/
abbrev CliPqxdhElfCorrectPlainPanPlacedWith
    (F : ShaState → List (BitVec 8) → ShaState)
    (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage) : Prop :=
  CliElfCodeMatchesPlaced mpl mmpl elf ∧
  ∀ W : CliHooks,
    W.C.F = F →
    W.C.E = CryptoGames.AES256.aes256Enc →
    W.C.D = CryptoGames.AES256.aes256Dec →
    W.C.X = CryptoGames.RFC7748.x25519Ref →
    W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
    W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
    W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
    W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
    W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
    ∀ X : UnreachedPqxdhPrimitives,
      CliSpecPqxdhOrExcusedAbort
        (fun i => CliReachesOOMPlainPanPlaced mpl mmpl elf W i ∨
          CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W i)
        (cliRunPlainPanPlacedSig mpl mmpl elf W) X ⟨W.C, W.Q⟩ ∧
      CliSpecPqxdhNoMatchOrExcusedAbort
        (fun i => CliReachesOOMPlainPanPlaced mpl mmpl elf W i ∨
          CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W i)
        (cliRunPlainPanPlacedSig mpl mmpl elf W) X ⟨W.C, W.Q⟩

/-- Strict relocatable plain-memory `CliPqxdhElfCorrect` at SHA-256 compression function `F`. -/
@[expose] def CliPqxdhElfCorrectStrictPlainPlaced2With
    (F : ShaState → List (BitVec 8) → ShaState)
    (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage) : Prop :=
  CliElfCodeMatchesPlaced mpl mmpl elf ∧
  ∀ W : CliHooks,
    W.C.F = F →
    W.C.E = CryptoGames.AES256.aes256Enc →
    W.C.D = CryptoGames.AES256.aes256Dec →
    W.C.X = CryptoGames.RFC7748.x25519Ref →
    W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
    W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
    W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
    W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
    W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
    ∀ X : UnreachedPqxdhPrimitives,
      CliSpecPqxdh (cliRunPlainPanPlacedSig mpl mmpl elf W) X ⟨W.C, W.Q⟩ ∧
      CliSpecPqxdhNoMatch (cliRunPlainPanPlacedSig mpl mmpl elf W) X ⟨W.C, W.Q⟩

theorem cliPqxdhElfCorrectPlainPanPlacedWith_of_strict2With
    {F : ShaState → List (BitVec 8) → ShaState}
    {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage}
    (h : CliPqxdhElfCorrectStrictPlainPlaced2With F mpl mmpl elf) :
    CliPqxdhElfCorrectPlainPanPlacedWith F mpl mmpl elf :=
  ⟨h.1, fun W hF hE hD hX hPub hF512 hEnc hDec hK X =>
    ⟨cliSpecPqxdhOrExcusedAbort_of_strict (h.2 W hF hE hD hX hPub hF512 hEnc hDec hK X).1,
     cliSpecPqxdhNoMatchOrExcusedAbort_of_strict (h.2 W hF hE hD hX hPub hF512 hEnc hDec hK X).2⟩⟩

theorem cliPqxdhElfCorrectPlainPanPlaced_of_placedWith
    {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage}
    (h : CliPqxdhElfCorrectPlainPanPlacedWith sha256Compress mpl mmpl elf) :
    CliPqxdhElfCorrectPlainPanPlaced mpl mmpl elf :=
  ⟨h.1, fun X => h.2 ⟨realCrypto, realPqxdhPrims⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl X⟩

/-- Step-safety refutation on plain-memory runs: `CliRunsToPlainPanPlaced` refutes `.OutOfMemory`. -/
theorem not_cliReachesOOMPlainPanPlaced_of_cliRunsToPlainPanPlaced
    {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage} {W : CliHooks} {i : Inputs} {o : Outcome}
    (hr : CliRunsToPlainPanPlaced mpl mmpl elf W i o) :
    ¬ CliReachesOOMPlainPanPlaced mpl mmpl elf W i := by
  rcases hr with ⟨s0, hload, _, hsafe⟩
  rintro ⟨s0', s, hload', hsteps, hs⟩
  rw [hload] at hload'
  injection hload' with hs0
  subst hs0
  rcases hsafe s hsteps with ⟨_, hterm, _⟩ | ⟨_, hfalse⟩ | ⟨hrun, _⟩
  · rcases hterm with ⟨_, hex, _⟩ | ⟨_, hsig, _⟩
    · rw [hs] at hex; cases hex
    · rw [hs] at hsig; cases hsig
  · exact hfalse
  · rw [hs] at hrun; cases hrun

private def dummyUnreachedPlain : UnreachedPqxdhPrimitives where
  sigPkGen := fun _ => []
  sigSign := fun _ _ _ => []
  scalarMul := fun _ _ => []
  scalarAdd := fun _ _ => []
  kemKeyGen := fun _ => ([], [])
  pow8 := fun _ => []
  isValidDhTriple := fun _ _ _ => false

theorem not_cliReachesOOMPlainPanPlaced_of_strict
    {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage} {W : CliHooks}
    (hStrictW : ∀ X : UnreachedPqxdhPrimitives,
      CliSpecPqxdh (cliRunPlainPanPlacedSig mpl mmpl elf W) X ⟨W.C, W.Q⟩ ∧
      CliSpecPqxdhNoMatch (cliRunPlainPanPlacedSig mpl mmpl elf W) X ⟨W.C, W.Q⟩)
    (i : Inputs) (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ i) :
    ¬ CliReachesOOMPlainPanPlaced mpl mmpl elf W i := by
  suffices hEx : ∃ o : Outcome, cliRunPlainPanPlacedSig mpl mmpl elf W i = some o by
    obtain ⟨o, ho⟩ := hEx
    exact not_cliReachesOOMPlainPanPlaced_of_cliRunsToPlainPanPlaced
      (cliRunsToPlainPanPlaced_of_eq_some ho)
  obtain ⟨hSpec, hNoMatch⟩ := hStrictW dummyUnreachedPlain
  rcases hi with ⟨st, hdom, hclause⟩
  obtain ⟨hInit, hSend, hWhisper, hPrekeyMatch, hOther⟩ := hSpec st hdom
  rcases hclause with
      ⟨hnone, b, t, rfl⟩ |
      ⟨m, r, hlen, rfl⟩ |
      ⟨c, rc, hlen, rfl⟩ |
      ⟨m, rc, hlen, rfl⟩ |
      ⟨c, rc, hlen, hhw, hhp, rfl⟩
  · exact ⟨_, hInit b t hnone⟩
  · have h := hSend m r hlen
    by_cases h1 : m.length > stdinCapBytes
    · simp only [h1, ↓reduceIte] at h; exact ⟨_, h⟩
    · by_cases h2 : m.length > maxPlaintextBytes <;>
        simp only [h1, h2, ↓reduceIte] at h <;> exact ⟨_, h⟩
  · have h := hWhisper c rc hlen
    by_cases h1 : (wireWhisper :: c).length > stdinCapBytes <;>
      simp only [h1, ↓reduceIte] at h <;> exact ⟨_, h⟩
  · cases hsess : st.session with
    | none =>
      have h := hPrekeyMatch m rc hlen (by intro _ _ h'; rw [hsess] at h'; cases h')
      by_cases h1 : (wirePrekey :: m.bytes).length > stdinCapBytes <;>
        simp only [h1, ↓reduceIte] at h <;> exact ⟨_, h⟩
    | some xg =>
      rcases xg with ⟨x, g⟩
      by_cases hm : PqSessionMatches x g m
      · have h := hPrekeyMatch m rc hlen (by
          intro x' g' h'
          rw [hsess] at h'
          injection h' with hpair
          cases hpair
          exact hm)
        by_cases h1 : (wirePrekey :: m.bytes).length > stdinCapBytes <;>
          simp only [h1, ↓reduceIte] at h <;> exact ⟨_, h⟩
      · have h := hNoMatch st hdom x g hsess m rc hlen hm
        by_cases h1 : (wirePrekey :: m.bytes).length > stdinCapBytes
        · simp only [h1, ↓reduceIte] at h; exact ⟨_, h⟩
        · simp only [h1, ↓reduceIte] at h
          obtain ⟨o, ho, _⟩ := h
          exact ⟨o, ho⟩
  · have h := hOther c rc hlen hhw hhp
    by_cases h1 : c.length > stdinCapBytes <;>
      simp only [h1, ↓reduceIte] at h <;> exact ⟨_, h⟩

/-! ## 2. Guarded Plain-Memory Assumptions Bundle & `SampleNTT` Startup Bridge -/

/-- Guarded extension of `CliElfExtPlainB2NeedLocksAssumptions2` carrying `harnessG` directly on
plain `elf` (no `patchElfTokensPlacedAt`, no `tokenCells`). -/
structure CliElfExtPlainB2NeedLocksAssumptions2G
    (mpl mmpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State))
    (mainIdx : Nat) (inputsOf : Inputs → ProcessInputs)
    (EntryGuard : State → Prop)
    (exitStk : Nat) (libcAddr : BitVec 64) (stk : Nat) (CodeOk : Memory → Prop)
    (lim : BudgetLimits) (elf : ElfImage) : Prop extends
    CliElfExtPlainB2NeedLocksAssumptions2 mpl mmpl ext mainIdx inputsOf
      exitStk libcAddr stk CodeOk lim elf where
  harnessG : ∀ W : CliHooks,
    MuslHarnessFineNeedLocksGuardedPerInput exitStk libcAddr elf
      (cliProgExtPlacedAt mpl ext mainIdx W) (mpl.base mainIdx) inputsOf
      mmpl lim fineCostModel.init stk CodeOk (cliStaticsPlacedAt mpl) EntryGuard

/-- Concrete `cliBudgetLimits` + `F3C2EntryGuard mpl mmpl` specialization of
`CliElfExtPlainB2NeedLocksAssumptions2G` on plain `elf`. -/
abbrev CliElfF3PlainB2NeedLocksAssumptionsG
    (mpl mmpl : Obj.MultiPlacement)
    (exitStk : Nat) (libcAddr : BitVec 64) (stk : Nat) (CodeOk : Memory → Prop)
    (elf : ElfImage) : Prop :=
  CliElfExtPlainB2NeedLocksAssumptions2G mpl mmpl (cliExternsPlaced mmpl) 617 cliProcessInputs
    (F3C2EntryGuard mpl mmpl) exitStk libcAddr stk CodeOk cliBudgetLimits elf

/-- Plain-memory `¬ CliReachesSampleNttStuckPlainPanPlaced → RealNeverViolatesSampleNtt` bridge
at `main` entry `sm` reached from `elf.loadState (cliProcessInputs i) = .ok s0`. -/
theorem realNeverViolatesSampleNtt_of_not_cliReachesSampleNttStuckPlainPanPlaced
    {mpl mmpl : Obj.MultiPlacement} (W₀ : CliHooks) {elf : ElfImage} {i : Inputs}
    {s0 sm : State}
    (hLoad : elf.loadState (cliProcessInputs i) = .ok s0)
    (hStart : Steps (cliProgPlacedSig mpl mmpl W₀) s0 sm)
    (hrun_sm : sm.status = .Running)
    (hNoStuck : ¬ CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W₀ i)
    (hTbl : ∀ W : CliHooks, cliHookTablePlaced mmpl W = cliHookTablePlaced mmpl W₀ := by
      intro _; rfl) :
    RealNeverViolatesSampleNtt mpl (cliExternsPlaced mmpl) sm := by
  refine realNeverViolatesFamily_of_startup W₀ hStart hrun_sm
    (fun sym u hmem hsteps hpc hrun => ?_) hTbl
  exact Classical.byContradiction fun hnot =>
    hNoStuck ⟨s0, u, hLoad, hsteps, hrun,
      (mlKemSampleNttStuckAt_iff mpl u).mpr ⟨sym, hmem, hpc, hnot⟩⟩

/-- Guarded strict 2-placement single-input whole-process outcome bridge on plain `elf`,
upgrading `H.harnessG`'s `F3C2EntryGuard` to `F3SampleNttEntryGuard` on input `i` via
`realNeverViolatesSampleNtt_of_not_cliReachesSampleNttStuckPlainPanPlaced`. -/
theorem outcome_of_main_strict_plain_f3_sampleNtt_at
    {mpl mmpl : Obj.MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage} {W : CliHooks} {Run : Inputs → RunAnswer → Prop}
    (hext : ExternPreservesNoAllocFailed (cliExternsPlaced mmpl W))
    (H : CliElfF3PlainB2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmain : ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (mpl.base 617)
        (withEntryGuard (F3SampleNttEntryGuard mpl mmpl)
          (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart)
            cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl) Run cliProcessInputs)))
    {i : Inputs} {r : MainResult}
    (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hc : MainCaseB2 Run IsSendOverCap IsStdinOverCap i r)
    (hNoStuck : ¬ CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W i) :
    ∃ res,
      outcomeOf elf
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (cliProcessInputs i) = some res ∧
      MainResult.Observed i.files r res := by
  let P := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W
  obtain ⟨s0, sm, Fr, γ, hload, hsteps0, hpc, hrun, hal, hfs, htr, hG, hx0, hmem, hexit⟩ :=
    H.harnessG W H.elfStaticOk i ⟨hi, hl⟩
  have hStart : Steps (cliProgPlacedSig mpl mmpl W) s0 sm :=
    steps_cliProgPlacedSig_of_running W W (loadState_status_running hload) hrun hsteps0
  have hSntt : RealNeverViolatesSampleNtt mpl (cliExternsPlaced mmpl) sm :=
    realNeverViolatesSampleNtt_of_not_cliReachesSampleNttStuckPlainPanPlaced W hload hStart hrun
      hNoStuck (fun _ => rfl)
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

/-! ## 3. Single-Input & Per-Clause Bridges to `cliRunPlainPanPlacedSig` -/

theorem cliRunPlainPanPlacedSig_of_strict_f3_sampleNtt_stdinOverCap
    {mpl mmpl : Obj.MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage} {W : CliHooks} {Run : Inputs → RunAnswer → Prop}
    (hext : ExternPreservesNoAllocFailed (cliExternsPlaced mmpl W))
    (H : CliElfF3PlainB2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmain : ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (mpl.base 617)
        (withEntryGuard (F3SampleNttEntryGuard mpl mmpl)
          (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart)
            cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl) Run cliProcessInputs)))
    {i : Inputs}
    (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hstin : IsStdinOverCap i)
    (hNoStuck : ¬ CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W i) :
    cliRunPlainPanPlacedSig mpl mmpl elf W i = some (.exited 2 [] (filesOf i.files)) := by
  obtain ⟨res, hout, hresObs⟩ :=
    outcome_of_main_strict_plain_f3_sampleNtt_at hext H hmain hi hl
      (MainCaseB2.stdinOverCap hstin) hNoStuck
  have hruns := cliRunsToPlainExtOnInputsAt_of_outcomeOf_usage hout hresObs
  exact (congrFun (cliRunPlainExtPlacedSigAt_cliExternsPlaced_eq mpl mmpl elf W).symm i).trans
    (cliRunPlainExtOnInputsSigAt_eq_some hruns)

theorem cliRunPlainPanPlacedSig_of_strict_f3_sampleNtt_sendOverCap
    {mpl mmpl : Obj.MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage} {W : CliHooks} {Run : Inputs → RunAnswer → Prop}
    (hext : ExternPreservesNoAllocFailed (cliExternsPlaced mmpl W))
    (H : CliElfF3PlainB2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
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
    (hNoStuck : ¬ CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W i) :
    cliRunPlainPanPlacedSig mpl mmpl elf W i = some (.exited 1 [] (filesOf i.files)) := by
  obtain ⟨res, hout, hresObs⟩ :=
    outcome_of_main_strict_plain_f3_sampleNtt_at hext H hmain hi hl
      (MainCaseB2.sendOverCap hover hnstin hcoins) hNoStuck
  have hruns := cliRunsToPlainExtOnInputsAt_of_outcomeOf_observed (a := some none) hout hresObs
  exact (congrFun (cliRunPlainExtPlacedSigAt_cliExternsPlaced_eq mpl mmpl elf W).symm i).trans
    (cliRunPlainExtOnInputsSigAt_eq_some hruns)

theorem cliRunPlainPanPlacedSig_of_strict_f3_sampleNtt_call_obs
    {mpl mmpl : Obj.MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage} {W : CliHooks} {Run : Inputs → RunAnswer → Prop}
    (hext : ExternPreservesNoAllocFailed (cliExternsPlaced mmpl W))
    (H : CliElfF3PlainB2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
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
    (hNoStuck : ¬ CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W i) :
    cliRunPlainPanPlacedSig mpl mmpl elf W i = some o := by
  obtain ⟨res, hout, hresObs⟩ :=
    outcome_of_main_strict_plain_f3_sampleNtt_at hext H hmain hi hl
      (MainCaseB2.call hrun hnover hnstin hcoins hcommit) hNoStuck
  have hruns := cliRunsToPlainExtOnInputsAt_of_outcomeOf_observed hout hresObs
  rw [hobs] at hruns
  exact (congrFun (cliRunPlainExtPlacedSigAt_cliExternsPlaced_eq mpl mmpl elf W).symm i).trans
    (cliRunPlainExtOnInputsSigAt_eq_some hruns)

theorem cliRunPlainPanPlacedSig_of_strict_f3_sampleNtt_call_pred
    {mpl mmpl : Obj.MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage} {W : CliHooks} {Run : Inputs → RunAnswer → Prop}
    {P : Outcome → Prop}
    (hext : ExternPreservesNoAllocFailed (cliExternsPlaced mmpl W))
    (H : CliElfF3PlainB2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
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
    (hNoStuck : ¬ CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W i) :
    ∃ o, cliRunPlainPanPlacedSig mpl mmpl elf W i = some o ∧ P o :=
  ⟨observe i.files a,
    cliRunPlainPanPlacedSig_of_strict_f3_sampleNtt_call_obs hext H hmain hi hl hrun hnover hnstin
      rfl hcoins hcommit hNoStuck, hp⟩

theorem cliRunPlainPanPlacedSig_pqInit_strict_of_f3B2NeedLocksG'
    {F : ShaState → List (BitVec 8) → ShaState}
    {mpl mmpl : Obj.MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3PlainB2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmain : MainOkCliF3PqB2NeedLocksPlacedAtGWithF F mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (W : CliHooks)
    (hF : W.C.F = F)
    (hAesE : W.C.E = CryptoGames.AES256.aes256Enc)
    (hAesD : W.C.D = CryptoGames.AES256.aes256Dec)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (hF512 : W.Q.F512 = CryptoGames.SHA512.sha512CompressState)
    (hEnc : W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec)
    (hDec : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    (X : UnreachedPqxdhPrimitives)
    (p : PqParty) (hp : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ p)
    (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen)
    (hnone : p.session = none)
    (hNoStuck :
      ¬ CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W (pqInitInputs ⟨W.C, W.Q⟩ p b t)) :
    cliRunPlainPanPlacedSig mpl mmpl elf W (pqInitInputs ⟨W.C, W.Q⟩ p b t) =
      some (pqxdhExpectedOutcome ⟨W.C, W.Q⟩ (pqInitInputs ⟨W.C, W.Q⟩ p b t)
        (pqInitModel X ⟨W.C, W.Q⟩ p b t)) := by
  let WP : PEParams := ⟨W.C, W.Q⟩
  obtain ⟨Run, hmainW, hclauses⟩ :=
    hmain H.base547NeZero X W hF hAesE hAesD hX hPub hF512 hEnc hDec hK
  obtain ⟨a, hrun, hobs, hcommit⟩ := (hclauses p hp).1 b t hnone
  exact cliRunPlainPanPlacedSig_of_strict_f3_sampleNtt_call_obs
    (externPreservesNoAllocFailed_cliExternsPlaced mmpl W) H hmainW
    (cliInputsOk_pqInitInputs WP p b t) (inputsLoadable_pqInitInputs WP p b t hp)
    hrun (not_isSendOverCap_pqInitInputs WP p b t)
    (not_isStdinOverCap_pqInitInputs WP p b t) hobs
    (coinsReadable_pqInitInputs WP p b t) hcommit hNoStuck

theorem cliRunPlainPanPlacedSig_pqSend_strict_of_f3B2NeedLocksG'
    {F : ShaState → List (BitVec 8) → ShaState}
    {mpl mmpl : Obj.MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3PlainB2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmain : MainOkCliF3PqB2NeedLocksPlacedAtGWithF F mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (W : CliHooks)
    (hF : W.C.F = F)
    (hAesE : W.C.E = CryptoGames.AES256.aes256Enc)
    (hAesD : W.C.D = CryptoGames.AES256.aes256Dec)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (hF512 : W.Q.F512 = CryptoGames.SHA512.sha512CompressState)
    (hEnc : W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec)
    (hDec : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    (p : PqParty) (hp : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ p)
    (m : List (BitVec 8)) (r : List.Vector (BitVec 8) 64)
    (hm : m.length < 2 ^ 32)
    (hNoStuck :
      ¬ CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W (pqSendInputs ⟨W.C, W.Q⟩ p m r)) :
    cliRunPlainPanPlacedSig mpl mmpl elf W (pqSendInputs ⟨W.C, W.Q⟩ p m r) =
      if m.length > stdinCapBytes then
        some (.exited 2 [] (filesOf (pqSendInputs ⟨W.C, W.Q⟩ p m r).files))
      else if m.length > maxPlaintextBytes then
        some (.exited 1 [] (filesOf (pqSendInputs ⟨W.C, W.Q⟩ p m r).files))
      else
        some (pqxdhExpectedOutcome ⟨W.C, W.Q⟩ (pqSendInputs ⟨W.C, W.Q⟩ p m r)
          (pqSendModel ⟨W.C, W.Q⟩ p m r.toList)) := by
  let WP : PEParams := ⟨W.C, W.Q⟩
  have hextW := externPreservesNoAllocFailed_cliExternsPlaced mmpl W
  obtain ⟨Run, hmainW, hclauses⟩ :=
    hmain H.base547NeZero dummyUnreachedPlain W hF hAesE hAesD hX hPub hF512 hEnc hDec hK
  by_cases hstin : m.length > stdinCapBytes
  · simp only [hstin, ↓reduceIte]
    exact cliRunPlainPanPlacedSig_of_strict_f3_sampleNtt_stdinOverCap hextW H hmainW
      (cliInputsOk_pqSendInputs WP p m r) (inputsLoadable_pqSendInputs WP p m r hp)
      (isStdinOverCap_pqSendInputs WP p m r hstin) hNoStuck
  · simp only [hstin, ↓reduceIte]
    have hnstin : ¬ IsStdinOverCap (pqSendInputs WP p m r) :=
      not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)
    by_cases hovc : m.length > maxPlaintextBytes
    · simp only [hovc, ↓reduceIte]
      exact cliRunPlainPanPlacedSig_of_strict_f3_sampleNtt_sendOverCap hextW H hmainW
        (cliInputsOk_pqSendInputs WP p m r) (inputsLoadable_pqSendInputs WP p m r hp)
        (isSendOverCap_pqSendInputs WP p m r (by unfold maxPlaintextBytes at hovc; exact hovc))
        hnstin (coinsReadable_pqSendInputs WP p m r) hNoStuck
    · simp only [hovc, ↓reduceIte]
      obtain ⟨a, hrun, hobs, hcommit⟩ := (hclauses p hp).2.1 m r hm
      exact cliRunPlainPanPlacedSig_of_strict_f3_sampleNtt_call_obs hextW H hmainW
        (cliInputsOk_pqSendInputs WP p m r) (inputsLoadable_pqSendInputs WP p m r hp)
        hrun
        (not_isSendOverCap_of_stdin_le
          (by simp only [pqSendInputs, pqInputs]; unfold maxPlaintextBytes at hovc; omega))
        hnstin hobs (coinsReadable_pqSendInputs WP p m r) hcommit hNoStuck

theorem cliRunPlainPanPlacedSig_pqRecvWhisper_strict_of_f3B2NeedLocksG'
    {F : ShaState → List (BitVec 8) → ShaState}
    {mpl mmpl : Obj.MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3PlainB2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmain : MainOkCliF3PqB2NeedLocksPlacedAtGWithF F mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (W : CliHooks)
    (hF : W.C.F = F)
    (hAesE : W.C.E = CryptoGames.AES256.aes256Enc)
    (hAesD : W.C.D = CryptoGames.AES256.aes256Dec)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (hF512 : W.Q.F512 = CryptoGames.SHA512.sha512CompressState)
    (hEnc : W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec)
    (hDec : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    (p : PqParty) (hp : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ p)
    (c : List (BitVec 8)) (rc : BitVec 256)
    (hc : c.length < 2 ^ 32)
    (hNoStuck :
      ¬ CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W
          (pqRecvInputs ⟨W.C, W.Q⟩ p (wireWhisper :: c) rc)) :
    cliRunPlainPanPlacedSig mpl mmpl elf W (pqRecvInputs ⟨W.C, W.Q⟩ p (wireWhisper :: c) rc) =
      if (wireWhisper :: c).length > stdinCapBytes then
        some (.exited 2 [] (filesOf (pqRecvInputs ⟨W.C, W.Q⟩ p (wireWhisper :: c) rc).files))
      else
        some (pqxdhExpectedOutcome ⟨W.C, W.Q⟩
          (pqRecvInputs ⟨W.C, W.Q⟩ p (wireWhisper :: c) rc)
          (pqRecvWhisperModel ⟨W.C, W.Q⟩ p c rc)) := by
  let WP : PEParams := ⟨W.C, W.Q⟩
  have hextW := externPreservesNoAllocFailed_cliExternsPlaced mmpl W
  obtain ⟨Run, hmainW, hclauses⟩ :=
    hmain H.base547NeZero dummyUnreachedPlain W hF hAesE hAesD hX hPub hF512 hEnc hDec hK
  by_cases hstin : (wireWhisper :: c).length > stdinCapBytes
  · simp only [hstin, ↓reduceIte]
    exact cliRunPlainPanPlacedSig_of_strict_f3_sampleNtt_stdinOverCap hextW H hmainW
      (cliInputsOk_pqRecvInputs WP p (wireWhisper :: c) rc)
      (inputsLoadable_pqRecvInputs WP p (wireWhisper :: c) rc hp)
      (isStdinOverCap_pqRecvInputs WP p (wireWhisper :: c) rc hstin) hNoStuck
  · simp only [hstin, ↓reduceIte]
    obtain ⟨a, hrun, hobs, hcommit⟩ := (hclauses p hp).2.2.1 c rc hc
    exact cliRunPlainPanPlacedSig_of_strict_f3_sampleNtt_call_obs hextW H hmainW
      (cliInputsOk_pqRecvInputs WP p (wireWhisper :: c) rc)
      (inputsLoadable_pqRecvInputs WP p (wireWhisper :: c) rc hp)
      hrun (not_isSendOverCap_pqRecvInputs WP p (wireWhisper :: c) rc)
      (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)) hobs
      (coinsReadable_pqRecvInputs WP p (wireWhisper :: c) rc) hcommit hNoStuck

theorem cliRunPlainPanPlacedSig_pqRecvPrekeyMatch_strict_of_f3B2NeedLocksG'
    {F : ShaState → List (BitVec 8) → ShaState}
    {mpl mmpl : Obj.MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3PlainB2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmain : MainOkCliF3PqB2NeedLocksPlacedAtGWithF F mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (W : CliHooks)
    (hF : W.C.F = F)
    (hAesE : W.C.E = CryptoGames.AES256.aes256Enc)
    (hAesD : W.C.D = CryptoGames.AES256.aes256Dec)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (hF512 : W.Q.F512 = CryptoGames.SHA512.sha512CompressState)
    (hEnc : W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec)
    (hDec : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    (X : UnreachedPqxdhPrimitives)
    (p : PqParty) (hp : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ p)
    (m : PreKeyMessageFields) (rc : BitVec 256)
    (hm : m.inner.length + 2048 < 2 ^ 32)
    (hmatch : ∀ x g, p.session = some (x, g) → PqSessionMatches x g m)
    (hNoStuck :
      ¬ CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W
          (pqRecvInputs ⟨W.C, W.Q⟩ p (wirePrekey :: m.bytes) rc)) :
    cliRunPlainPanPlacedSig mpl mmpl elf W (pqRecvInputs ⟨W.C, W.Q⟩ p (wirePrekey :: m.bytes) rc) =
      if (wirePrekey :: m.bytes).length > stdinCapBytes then
        some (.exited 2 [] (filesOf (pqRecvInputs ⟨W.C, W.Q⟩ p (wirePrekey :: m.bytes) rc).files))
      else
        some (pqxdhExpectedOutcome ⟨W.C, W.Q⟩
          (pqRecvInputs ⟨W.C, W.Q⟩ p (wirePrekey :: m.bytes) rc)
          (pqRecvPrekeyModel X ⟨W.C, W.Q⟩ p m rc)) := by
  let WP : PEParams := ⟨W.C, W.Q⟩
  have hextW := externPreservesNoAllocFailed_cliExternsPlaced mmpl W
  obtain ⟨Run, hmainW, hclauses⟩ :=
    hmain H.base547NeZero X W hF hAesE hAesD hX hPub hF512 hEnc hDec hK
  by_cases hstin : (wirePrekey :: m.bytes).length > stdinCapBytes
  · simp only [hstin, ↓reduceIte]
    exact cliRunPlainPanPlacedSig_of_strict_f3_sampleNtt_stdinOverCap hextW H hmainW
      (cliInputsOk_pqRecvInputs WP p (wirePrekey :: m.bytes) rc)
      (inputsLoadable_pqRecvInputs WP p (wirePrekey :: m.bytes) rc hp)
      (isStdinOverCap_pqRecvInputs WP p (wirePrekey :: m.bytes) rc hstin) hNoStuck
  · simp only [hstin, ↓reduceIte]
    obtain ⟨a, hrun, hobs, hcommit⟩ := (hclauses p hp).2.2.2.1 m rc hm hmatch
    exact cliRunPlainPanPlacedSig_of_strict_f3_sampleNtt_call_obs hextW H hmainW
      (cliInputsOk_pqRecvInputs WP p (wirePrekey :: m.bytes) rc)
      (inputsLoadable_pqRecvInputs WP p (wirePrekey :: m.bytes) rc hp)
      hrun (not_isSendOverCap_pqRecvInputs WP p (wirePrekey :: m.bytes) rc)
      (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)) hobs
      (coinsReadable_pqRecvInputs WP p (wirePrekey :: m.bytes) rc) hcommit hNoStuck

theorem cliRunPlainPanPlacedSig_pqRecvBad_strict_of_f3B2NeedLocksG'
    {F : ShaState → List (BitVec 8) → ShaState}
    {mpl mmpl : Obj.MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3PlainB2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmain : MainOkCliF3PqB2NeedLocksPlacedAtGWithF F mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (W : CliHooks)
    (hF : W.C.F = F)
    (hAesE : W.C.E = CryptoGames.AES256.aes256Enc)
    (hAesD : W.C.D = CryptoGames.AES256.aes256Dec)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (hF512 : W.Q.F512 = CryptoGames.SHA512.sha512CompressState)
    (hEnc : W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec)
    (hDec : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    (p : PqParty) (hp : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ p)
    (c : List (BitVec 8)) (rc : BitVec 256)
    (hc : c.length < 2 ^ 32)
    (h2 : c.head? ≠ some wireWhisper) (h3 : c.head? ≠ some wirePrekey)
    (hNoStuck :
      ¬ CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W (pqRecvInputs ⟨W.C, W.Q⟩ p c rc)) :
    cliRunPlainPanPlacedSig mpl mmpl elf W (pqRecvInputs ⟨W.C, W.Q⟩ p c rc) =
      if c.length > stdinCapBytes then
        some (.exited 2 [] (filesOf (pqRecvInputs ⟨W.C, W.Q⟩ p c rc).files))
      else
        some (.exited 1 [] (filesOf (pqRecvInputs ⟨W.C, W.Q⟩ p c rc).files)) := by
  let WP : PEParams := ⟨W.C, W.Q⟩
  have hextW := externPreservesNoAllocFailed_cliExternsPlaced mmpl W
  obtain ⟨Run, hmainW, hclauses⟩ :=
    hmain H.base547NeZero dummyUnreachedPlain W hF hAesE hAesD hX hPub hF512 hEnc hDec hK
  by_cases hstin : c.length > stdinCapBytes
  · simp only [hstin, ↓reduceIte]
    exact cliRunPlainPanPlacedSig_of_strict_f3_sampleNtt_stdinOverCap hextW H hmainW
      (cliInputsOk_pqRecvInputs WP p c rc) (inputsLoadable_pqRecvInputs WP p c rc hp)
      (isStdinOverCap_pqRecvInputs WP p c rc hstin) hNoStuck
  · simp only [hstin, ↓reduceIte]
    obtain ⟨a, hrun, hobs, hcommit⟩ := (hclauses p hp).2.2.2.2 c rc hc h2 h3
    exact cliRunPlainPanPlacedSig_of_strict_f3_sampleNtt_call_obs hextW H hmainW
      (cliInputsOk_pqRecvInputs WP p c rc) (inputsLoadable_pqRecvInputs WP p c rc hp)
      hrun (not_isSendOverCap_pqRecvInputs WP p c rc)
      (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)) hobs
      (coinsReadable_pqRecvInputs WP p c rc) hcommit hNoStuck

theorem cliRunPlainPanPlacedSig_pqRecvNoMatch_strict_of_f3B2NeedLocksG'
    {F : ShaState → List (BitVec 8) → ShaState}
    {mpl mmpl : Obj.MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3PlainB2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hover : MainOkCliF3OverB2NeedLocksPlacedAtGWithF F mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (W : CliHooks)
    (hF : W.C.F = F)
    (hAesE : W.C.E = CryptoGames.AES256.aes256Enc)
    (hAesD : W.C.D = CryptoGames.AES256.aes256Dec)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (hF512 : W.Q.F512 = CryptoGames.SHA512.sha512CompressState)
    (hEnc : W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec)
    (hDec : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    (X : UnreachedPqxdhPrimitives)
    (st : PqParty) (hst : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st)
    (x : RecordExtras) (g : GhostState Bytes) (hsess : st.session = some (x, g))
    (m : PreKeyMessageFields) (rc : BitVec 256)
    (hm : m.inner.length + 2048 < 2 ^ 32)
    (hnomatch : ¬ PqSessionMatches x g m)
    (hNoStuck :
      ¬ CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W
          (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: m.bytes) rc)) :
    if (wirePrekey :: m.bytes).length > stdinCapBytes then
      cliRunPlainPanPlacedSig mpl mmpl elf W (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: m.bytes) rc) =
        some (.exited 2 [] (filesOf (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: m.bytes) rc).files))
    else
      ∃ o : Outcome,
        cliRunPlainPanPlacedSig mpl mmpl elf W (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: m.bytes) rc) =
          some o ∧
        OutcomeMatchesModelExceptPath ⟨W.C, W.Q⟩
          (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: m.bytes) rc)
          (sessionFile (partyAddress st.party.other))
          (pqRecvPrekeyModel X ⟨W.C, W.Q⟩ { st with session := none } m rc) o := by
  let WP : PEParams := ⟨W.C, W.Q⟩
  have hextW := externPreservesNoAllocFailed_cliExternsPlaced mmpl W
  obtain ⟨Run, hmainW, hclause⟩ :=
    hover H.base547NeZero X W hF hAesE hAesD hX hPub hF512 hEnc hDec hK
  by_cases hstin : (wirePrekey :: m.bytes).length > stdinCapBytes
  · simp only [hstin, ↓reduceIte]
    exact cliRunPlainPanPlacedSig_of_strict_f3_sampleNtt_stdinOverCap hextW H hmainW
      (cliInputsOk_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
      (inputsLoadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hst)
      (isStdinOverCap_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hstin) hNoStuck
  · simp only [hstin, ↓reduceIte]
    obtain ⟨a, hrun, hobsEx, hcommit⟩ := hclause st hst x g hsess m rc hm hnomatch
    exact cliRunPlainPanPlacedSig_of_strict_f3_sampleNtt_call_pred hextW H hmainW
      (cliInputsOk_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
      (inputsLoadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hst)
      hrun (not_isSendOverCap_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
      (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin))
      hobsEx (coinsReadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc) hcommit hNoStuck

/-! ## 4. Plain-Memory ELF Composers and `¬ CliReachesOOMPlainPanPlaced` -/

theorem cliPqxdhElfCorrectStrictPlainPlaced2With_of_f3B2NeedLocksG'
    {F : ShaState → List (BitVec 8) → ShaState}
    {mpl mmpl : Obj.MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3PlainB2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmain : MainOkCliF3PqB2NeedLocksPlacedAtGWithF F mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hover : MainOkCliF3OverB2NeedLocksPlacedAtGWithF F mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hNoStuck : ∀ (W : CliHooks),
      W.C.F = F →
      W.C.E = CryptoGames.AES256.aes256Enc →
      W.C.D = CryptoGames.AES256.aes256Dec →
      W.C.X = CryptoGames.RFC7748.x25519Ref →
      W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
      W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
      W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
      W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
      W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
      ∀ (i : Inputs), CliPqxdhInputs ⟨W.C, W.Q⟩ i →
        ¬ CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W i) :
    CliPqxdhElfCorrectStrictPlainPlaced2With F mpl mmpl elf := by
  refine ⟨H.codeMatches, fun W hF hAesE hAesD hX hPub hF512 hEnc hDec hK X => ?_⟩
  let WP : PEParams := ⟨W.C, W.Q⟩
  have hNS := hNoStuck W hF hAesE hAesD hX hPub hF512 hEnc hDec hK
  refine ⟨?_, ?_⟩
  · intro p hp
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro b t hnone
      exact cliRunPlainPanPlacedSig_pqInit_strict_of_f3B2NeedLocksG' H hmain W hF hAesE hAesD hX
        hPub hF512 hEnc hDec hK X p hp b t hnone (hNS _ ⟨p, hp, Or.inl ⟨hnone, b, t, rfl⟩⟩)
    · intro m r hm
      exact cliRunPlainPanPlacedSig_pqSend_strict_of_f3B2NeedLocksG' H hmain W hF hAesE hAesD hX
        hPub hF512 hEnc hDec hK p hp m r hm (hNS _ ⟨p, hp, Or.inr (Or.inl ⟨m, r, hm, rfl⟩)⟩)
    · intro c rc hc
      exact cliRunPlainPanPlacedSig_pqRecvWhisper_strict_of_f3B2NeedLocksG' H hmain W hF hAesE
        hAesD hX hPub hF512 hEnc hDec hK p hp c rc hc
        (hNS _ ⟨p, hp, Or.inr (Or.inr (Or.inl ⟨c, rc, hc, rfl⟩))⟩)
    · intro m rc hm hmatch
      exact cliRunPlainPanPlacedSig_pqRecvPrekeyMatch_strict_of_f3B2NeedLocksG' H hmain W hF hAesE
        hAesD hX hPub hF512 hEnc hDec hK X p hp m rc hm hmatch
        (hNS _ ⟨p, hp, Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rc, hm, rfl⟩)))⟩)
    · intro c rc hc h2 h3
      exact cliRunPlainPanPlacedSig_pqRecvBad_strict_of_f3B2NeedLocksG' H hmain W hF hAesE hAesD
        hX hPub hF512 hEnc hDec hK p hp c rc hc h2 h3
        (hNS _ ⟨p, hp, Or.inr (Or.inr (Or.inr (Or.inr ⟨c, rc, hc, h2, h3, rfl⟩)))⟩)
  · intro st hst x g hsess m rc hm hnomatch
    exact cliRunPlainPanPlacedSig_pqRecvNoMatch_strict_of_f3B2NeedLocksG' H hover W hF hAesE hAesD
      hX hPub hF512 hEnc hDec hK X st hst x g hsess m rc hm hnomatch
      (hNS _ ⟨st, hst, Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rc, hm, rfl⟩)))⟩)

theorem cliPqxdhElfCorrectPlainPanPlacedWith_of_f3B2NeedLocksG'
    {F : ShaState → List (BitVec 8) → ShaState}
    {mpl mmpl : Obj.MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3PlainB2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmain : MainOkCliF3PqB2NeedLocksPlacedAtGWithF F mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hover : MainOkCliF3OverB2NeedLocksPlacedAtGWithF F mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hStuckDiv : ∀ (W : CliHooks),
      W.C.F = F →
      W.C.E = CryptoGames.AES256.aes256Enc →
      W.C.D = CryptoGames.AES256.aes256Dec →
      W.C.X = CryptoGames.RFC7748.x25519Ref →
      W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
      W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
      W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
      W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
      W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
      ∀ (i : Inputs), CliPqxdhInputs ⟨W.C, W.Q⟩ i →
        CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W i →
        cliRunPlainPanPlacedSig mpl mmpl elf W i = none) :
    CliPqxdhElfCorrectPlainPanPlacedWith F mpl mmpl elf := by
  refine ⟨H.codeMatches, fun W hF hAesE hAesD hX hPub hF512 hEnc hDec hK X => ?_⟩
  let WP : PEParams := ⟨W.C, W.Q⟩
  have hSD := hStuckDiv W hF hAesE hAesD hX hPub hF512 hEnc hDec hK
  refine ⟨?_, ?_⟩
  · intro p hp
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro b t hnone
      have hiDom : CliPqxdhInputs WP (pqInitInputs WP p b t) :=
        ⟨p, hp, Or.inl ⟨hnone, b, t, rfl⟩⟩
      by_cases hStuck : CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W (pqInitInputs WP p b t)
      · exact Or.inr ⟨hSD _ hiDom hStuck, Or.inr hStuck⟩
      · exact outcomeOrExcusedAbort_of_eq
          (cliRunPlainPanPlacedSig_pqInit_strict_of_f3B2NeedLocksG' H hmain W hF hAesE hAesD hX
            hPub hF512 hEnc hDec hK X p hp b t hnone hStuck)
    · intro m r hm
      have hiDom : CliPqxdhInputs WP (pqSendInputs WP p m r) :=
        ⟨p, hp, Or.inr (Or.inl ⟨m, r, hm, rfl⟩)⟩
      by_cases hStuck : CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W (pqSendInputs WP p m r)
      · exact Or.inr ⟨hSD _ hiDom hStuck, Or.inr hStuck⟩
      · have hEq :=
          cliRunPlainPanPlacedSig_pqSend_strict_of_f3B2NeedLocksG' H hmain W hF hAesE hAesD hX hPub
            hF512 hEnc hDec hK p hp m r hm hStuck
        refine outcomeOrExcusedAbort_of_eq ?_
        split_ifs at hEq ⊢ <;> exact hEq
    · intro c rc hc
      have hiDom : CliPqxdhInputs WP (pqRecvInputs WP p (wireWhisper :: c) rc) :=
        ⟨p, hp, Or.inr (Or.inr (Or.inl ⟨c, rc, hc, rfl⟩))⟩
      by_cases hStuck :
          CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W
            (pqRecvInputs WP p (wireWhisper :: c) rc)
      · exact Or.inr ⟨hSD _ hiDom hStuck, Or.inr hStuck⟩
      · have hEq :=
          cliRunPlainPanPlacedSig_pqRecvWhisper_strict_of_f3B2NeedLocksG' H hmain W hF hAesE hAesD
            hX hPub hF512 hEnc hDec hK p hp c rc hc hStuck
        refine outcomeOrExcusedAbort_of_eq ?_
        split_ifs at hEq ⊢ <;> exact hEq
    · intro m rc hm hmatch
      have hiDom : CliPqxdhInputs WP (pqRecvInputs WP p (wirePrekey :: m.bytes) rc) :=
        ⟨p, hp, Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rc, hm, rfl⟩)))⟩
      by_cases hStuck :
          CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W
            (pqRecvInputs WP p (wirePrekey :: m.bytes) rc)
      · exact Or.inr ⟨hSD _ hiDom hStuck, Or.inr hStuck⟩
      · have hEq :=
          cliRunPlainPanPlacedSig_pqRecvPrekeyMatch_strict_of_f3B2NeedLocksG' H hmain W hF hAesE
            hAesD hX hPub hF512 hEnc hDec hK X p hp m rc hm hmatch hStuck
        refine outcomeOrExcusedAbort_of_eq ?_
        split_ifs at hEq ⊢ <;> exact hEq
    · intro c rc hc h2 h3
      have hiDom : CliPqxdhInputs WP (pqRecvInputs WP p c rc) :=
        ⟨p, hp, Or.inr (Or.inr (Or.inr (Or.inr ⟨c, rc, hc, h2, h3, rfl⟩)))⟩
      by_cases hStuck : CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W (pqRecvInputs WP p c rc)
      · exact Or.inr ⟨hSD _ hiDom hStuck, Or.inr hStuck⟩
      · have hEq :=
          cliRunPlainPanPlacedSig_pqRecvBad_strict_of_f3B2NeedLocksG' H hmain W hF hAesE hAesD hX
            hPub hF512 hEnc hDec hK p hp c rc hc h2 h3 hStuck
        refine outcomeOrExcusedAbort_of_eq ?_
        split_ifs at hEq ⊢ <;> exact hEq
  · intro st hst x g hsess m rc hm hnomatch
    have hiDom : CliPqxdhInputs WP (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) :=
      ⟨st, hst, Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rc, hm, rfl⟩)))⟩
    by_cases hStuck :
        CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W
          (pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
    · exact Or.inr ⟨hSD _ hiDom hStuck, Or.inr hStuck⟩
    · have hNM :=
        cliRunPlainPanPlacedSig_pqRecvNoMatch_strict_of_f3B2NeedLocksG' H hover W hF hAesE hAesD
          hX hPub hF512 hEnc hDec hK X st hst x g hsess m rc hm hnomatch hStuck
      refine Or.inl ?_
      by_cases hstin : (wirePrekey :: m.bytes).length > stdinCapBytes
      · simp only [hstin, ↓reduceIte] at hNM
        exact ⟨_, hNM, by simp only [hstin, ↓reduceIte]⟩
      · simp only [hstin, ↓reduceIte] at hNM
        obtain ⟨o, ho, hpo⟩ := hNM
        exact ⟨o, ho, by simp only [hstin, ↓reduceIte]; exact hpo⟩

theorem cliPqxdhElfCorrectPlainPanPlaced_of_f3B2NeedLocksG'
    {mpl mmpl : Obj.MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3PlainB2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmain : MainOkCliF3PqB2NeedLocksPlacedAtGWithF sha256Compress mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hover : MainOkCliF3OverB2NeedLocksPlacedAtGWithF sha256Compress mpl mmpl CodeOk libcAddr elf.brkStart stk)
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
        CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W i →
        cliRunPlainPanPlacedSig mpl mmpl elf W i = none) :
    CliPqxdhElfCorrectPlainPanPlaced mpl mmpl elf :=
  cliPqxdhElfCorrectPlainPanPlaced_of_placedWith
    (cliPqxdhElfCorrectPlainPanPlacedWith_of_f3B2NeedLocksG' H hmain hover hStuckDiv)

theorem not_cliReachesOOMPlainPanPlaced_of_f3B2NeedLocksG_notStuck
    {F : ShaState → List (BitVec 8) → ShaState}
    {mpl mmpl : Obj.MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3PlainB2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmain : MainOkCliF3PqB2NeedLocksPlacedAtGWithF F mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hover : MainOkCliF3OverB2NeedLocksPlacedAtGWithF F mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (W : CliHooks)
    (hF : W.C.F = F)
    (hE : W.C.E = CryptoGames.AES256.aes256Enc)
    (hD : W.C.D = CryptoGames.AES256.aes256Dec)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (hF512 : W.Q.F512 = CryptoGames.SHA512.sha512CompressState)
    (hEnc : W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec)
    (hDec : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    {i : Inputs}
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ i)
    (hNoStuck : ¬ CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W i) :
    ¬ CliReachesOOMPlainPanPlaced mpl mmpl elf W i := by
  suffices hEx : ∃ o : Outcome, cliRunPlainPanPlacedSig mpl mmpl elf W i = some o by
    obtain ⟨o, ho⟩ := hEx
    exact not_cliReachesOOMPlainPanPlaced_of_cliRunsToPlainPanPlaced
      (cliRunsToPlainPanPlaced_of_eq_some ho)
  rcases hi with ⟨st, hdom, hclause⟩
  rcases hclause with
      ⟨hnone, b, t, rfl⟩ |
      ⟨m, r, hlen, rfl⟩ |
      ⟨c, rc, hlen, rfl⟩ |
      ⟨m, rc, hlen, rfl⟩ |
      ⟨c, rc, hlen, hhw, hhp, rfl⟩
  · exact ⟨_, cliRunPlainPanPlacedSig_pqInit_strict_of_f3B2NeedLocksG' H hmain W hF hE hD hX hPub
      hF512 hEnc hDec hK dummyUnreachedPlain st hdom b t hnone hNoStuck⟩
  · have h := cliRunPlainPanPlacedSig_pqSend_strict_of_f3B2NeedLocksG' H hmain W hF hE hD hX hPub
      hF512 hEnc hDec hK st hdom m r hlen hNoStuck
    by_cases h1 : m.length > stdinCapBytes
    · simp only [h1, ↓reduceIte] at h; exact ⟨_, h⟩
    · by_cases h2 : m.length > maxPlaintextBytes <;>
        simp only [h1, h2, ↓reduceIte] at h <;> exact ⟨_, h⟩
  · have h := cliRunPlainPanPlacedSig_pqRecvWhisper_strict_of_f3B2NeedLocksG' H hmain W hF hE hD
      hX hPub hF512 hEnc hDec hK st hdom c rc hlen hNoStuck
    by_cases h1 : (wireWhisper :: c).length > stdinCapBytes <;>
      simp only [h1, ↓reduceIte] at h <;> exact ⟨_, h⟩
  · cases hsess : st.session with
    | none =>
      have h := cliRunPlainPanPlacedSig_pqRecvPrekeyMatch_strict_of_f3B2NeedLocksG' H hmain W hF
        hE hD hX hPub hF512 hEnc hDec hK dummyUnreachedPlain st hdom m rc hlen
        (fun _ _ h' => by rw [hsess] at h'; cases h') hNoStuck
      by_cases h1 : (wirePrekey :: m.bytes).length > stdinCapBytes <;>
        simp only [h1, ↓reduceIte] at h <;> exact ⟨_, h⟩
    | some xg =>
      rcases xg with ⟨x, g⟩
      by_cases hm : PqSessionMatches x g m
      · have h := cliRunPlainPanPlacedSig_pqRecvPrekeyMatch_strict_of_f3B2NeedLocksG' H hmain W hF
          hE hD hX hPub hF512 hEnc hDec hK dummyUnreachedPlain st hdom m rc hlen
          (fun x' g' h' => by
            rw [hsess] at h'
            injection h' with hpair
            cases hpair
            exact hm) hNoStuck
        by_cases h1 : (wirePrekey :: m.bytes).length > stdinCapBytes <;>
          simp only [h1, ↓reduceIte] at h <;> exact ⟨_, h⟩
      · have h := cliRunPlainPanPlacedSig_pqRecvNoMatch_strict_of_f3B2NeedLocksG' H hover W hF hE
          hD hX hPub hF512 hEnc hDec hK dummyUnreachedPlain st hdom x g hsess m rc hlen hm hNoStuck
        by_cases h1 : (wirePrekey :: m.bytes).length > stdinCapBytes
        · simp only [h1, ↓reduceIte] at h; exact ⟨_, h⟩
        · simp only [h1, ↓reduceIte] at h
          obtain ⟨o, ho, _⟩ := h
          exact ⟨o, ho⟩
  · have h := cliRunPlainPanPlacedSig_pqRecvBad_strict_of_f3B2NeedLocksG' H hmain W hF hE hD hX
      hPub hF512 hEnc hDec hK st hdom c rc hlen hhw hhp hNoStuck
    by_cases h1 : c.length > stdinCapBytes <;>
      simp only [h1, ↓reduceIte] at h <;> exact ⟨_, h⟩

end LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.PlainPlacedComposer
