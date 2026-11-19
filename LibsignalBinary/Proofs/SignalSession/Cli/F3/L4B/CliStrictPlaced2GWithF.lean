/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4A.T2NoOomBridge
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2G -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3ExternNoAllocFail
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.PlacedOomRecovery2
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2EntryGuard
import Arm64.Trusted.Spec.Hoare
import LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Process
import LibsignalBinary.Proofs.SignalSession.Cli.ProcessBridgePq
import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced -- proof-setup: allow-public-import
import LibsignalBinary.Specifications.SignalSession.CliProcess
import LibsignalBinary.Specifications.SignalSession.CliRun
import LibsignalBinary.Specifications.SignalSession.PqDir
import LibsignalBinary.Specifications.SignalSession.PqDirNoMatch
import LibsignalBinary.Specifications.SignalSession.Run

/-!
# `F`-Pinned (`W.C.F = F`) Strict Two-Placement Composers

`W.C.F = F`-guarded counterparts of `CliStrictPlaced2` and `CliStrictPlaced2G` producing
`CliPqxdhElfCorrectStrictPlaced2With F mpl mmpl elf`,
`CliPqxdhElfCorrectPlacedWith F mpl mmpl elf`, and
`¬ CliReachesOOMPlaced mpl mmpl elf W i`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2GWithF

open Arm64 Arm64.Obj Arm64.Process
open CryptoGames.HMAC (ShaState)
open CryptoGames.LibsignalSession (GhostState)
open CryptoVerification.E2E
  (Bytes PEParams PreKeyBundleFields PreKeyMessageFields RecordExtras UnreachedPqxdhPrimitives
   initiateTapeLen wirePrekey wireWhisper)
open CryptoVerification.SignalSession
  (CliHooks CliPqxdhInputs CliSpecPqxdh CliSpecPqxdhNoMatch CliSpecPqxdhNoMatchOrExcusedAbort
   CliSpecPqxdhOrExcusedAbort Inputs Outcome OutcomeMatchesModelExceptPath OutcomeOrExcusedAbort
   PqParty PqSessionMatches PqxdhPartyInSpecDomain cliExternsPlaced cliInputsOk_pqInitInputs
   cliInputsOk_pqRecvInputs cliInputsOk_pqSendInputs cliProcessInputs coinsReadable_pqInitInputs
   coinsReadable_pqRecvInputs coinsReadable_pqSendInputs filesOf inputsLoadable_pqInitInputs
   inputsLoadable_pqRecvInputs inputsLoadable_pqSendInputs isSendOverCap_pqSendInputs
   isStdinOverCap_pqRecvInputs isStdinOverCap_pqSendInputs maxPlaintextBytes
   not_isSendOverCap_of_stdin_le not_isSendOverCap_pqInitInputs not_isSendOverCap_pqRecvInputs
   not_isStdinOverCap_of_stdin_le not_isStdinOverCap_pqInitInputs observe partyAddress pqInitInputs
   pqInitModel pqInputs pqRecvInputs pqRecvPrekeyModel pqRecvWhisperModel pqSendInputs pqSendModel
   pqxdhExpectedOutcome sessionFile stdinCapBytes)
open LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced
  (CliReachesOOMPlaced CliReachesSampleNttStuckPlaced cliRunPlacedSig)
open CryptoVerification.SignalSession.Cli
  (CommitOk ElfStaticOk IsStdinOverCap MainResult RunAnswer cliInputs)
open LibsignalBinary.Heap (BudgetLimits)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4A.T2NoOomBridge
  (cliRunsToPlaced_of_cliRunPlacedSig_eq_some not_cliReachesOOMPlaced_of_cliRunsToPlaced
   not_cliReachesOOMPlaced_of_strict)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
  (CliElfExtB2NeedLocksAssumptions2 CliElfF3B2NeedLocksAssumptions
   MuslHarnessFineNeedLocksGuardedPerInput MuslHarnessFineNeedLocksPerInput
   b2MainSpecTightNeedLocksFineAt cliBudgetLimits cliRunExtOnInputsSigAt_of_strict_b2_needLocks_call_obs
   cliRunExtOnInputsSigAt_of_strict_b2_needLocks_call_pred
   cliRunExtOnInputsSigAt_of_strict_b2_needLocks_sendOverCap
   cliRunExtOnInputsSigAt_of_strict_b2_needLocks_stdinOverCap
   cliRunPlacedSig_eq_cliRunExtPlacedSigAt_of_progEq2)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2G
  (CliElfExtB2NeedLocksAssumptions2G CliElfF3B2NeedLocksAssumptionsG F3SampleNttEntryGuard
   cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_call_obs
   cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_call_pred
   cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_sendOverCap
   cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_stdinOverCap
   cliRunPlacedSig_of_strict_f3_sampleNtt_call_obs
   cliRunPlacedSig_of_strict_f3_sampleNtt_call_pred
   cliRunPlacedSig_of_strict_f3_sampleNtt_sendOverCap
   cliRunPlacedSig_of_strict_f3_sampleNtt_stdinOverCap)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3ExternNoAllocFail
  (ExternPreservesNoAllocFailed externPreservesNoAllocFailed_cliExternsPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
  (CliElfTokenCellsPlacedAt cliProgExtPlacedAt cliProgExtPlacedSigAt_cliExternsPlaced_eq
   cliRunExtOnInputsSigAt cliRunExtPlacedSigAt cliStaticsPlacedAt patchElfTokensPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.PlacedOomRecovery2
  (CliPqxdhElfCorrectPlacedWith CliPqxdhElfCorrectStrictPlaced2With
   cliPqxdhElfCorrectPlacedWith_of_strict2With outcomeOrExcusedAbort_of_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG
  (Block617TransferFixedHypG withEntryGuard)

/-! ## 1. Unguarded `F`-Pinned `MainOk*WithF` Predicates and Strict Composers -/

/-- `W.C.F = F`- and real-AES-pinned `NeedLocks` + SWAR-padded `argvAtRO` 5-clause PQXDH `main` spec. -/
@[expose] def MainOkCliExtPqB2NeedLocksPlacedAtWithF
    (F : ShaState → List (BitVec 8) → ShaState)
    (mpl mmpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State))
    (mainIdx : Nat) (inputsOf : Inputs → ProcessInputs) (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) (lim : BudgetLimits) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    W.C.F = F →
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

/-- `W.C.F = F`- and real-AES-pinned `NeedLocks` + SWAR-padded `argvAtRO` `NoMatch` `main` spec. -/
@[expose] def MainOkCliExtOverB2NeedLocksPlacedAtWithF
    (F : ShaState → List (BitVec 8) → ShaState)
    (mpl mmpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State))
    (mainIdx : Nat) (inputsOf : Inputs → ProcessInputs) (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) (lim : BudgetLimits) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    W.C.F = F →
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

abbrev MainOkCliF3PqB2NeedLocksPlacedAtWithF
    (F : ShaState → List (BitVec 8) → ShaState)
    (mpl mmpl : Obj.MultiPlacement) (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) : Prop :=
  MainOkCliExtPqB2NeedLocksPlacedAtWithF F mpl mmpl (cliExternsPlaced mmpl) 617 cliProcessInputs
    CodeOk libcAddr brkStart stk cliBudgetLimits

abbrev MainOkCliF3OverB2NeedLocksPlacedAtWithF
    (F : ShaState → List (BitVec 8) → ShaState)
    (mpl mmpl : Obj.MultiPlacement) (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) : Prop :=
  MainOkCliExtOverB2NeedLocksPlacedAtWithF F mpl mmpl (cliExternsPlaced mmpl) 617 cliProcessInputs
    CodeOk libcAddr brkStart stk cliBudgetLimits

theorem cliSpecPqxdh_ext_strict_of_b2_needLocks_withF
    {F : ShaState → List (BitVec 8) → ShaState}
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {mainIdx : Nat}
    {inputsOf : Inputs → ProcessInputs} {exitStk : Nat} {libcAddr : BitVec 64}
    {CodeOk : Memory → Prop} {stk : Nat} {lim : BudgetLimits}
    {elf : ElfImage} {W : CliHooks}
    (hF : W.C.F = F)
    (hAesE : W.C.E = CryptoGames.AES256.aes256Enc)
    (hAesD : W.C.D = CryptoGames.AES256.aes256Dec)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (hF512 : W.Q.F512 = CryptoGames.SHA512.sha512CompressState)
    (hEnc : W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec)
    (hDec : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    (hext : ExternPreservesNoAllocFailed (ext W))
    (hE : ElfStaticOk elf)
    (htok : CliElfTokenCellsPlacedAt mpl elf)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hCode : ∀ m, CodeOk m → (cliProgExtPlacedAt mpl ext mainIdx W).CodeLoaded m)
    (hH : MuslHarnessFineNeedLocksPerInput exitStk libcAddr (patchElfTokensPlacedAt mpl elf)
      (cliProgExtPlacedAt mpl ext mainIdx W) (mpl.base mainIdx) inputsOf
      mmpl lim fineCostModel.init stk CodeOk (cliStaticsPlacedAt mpl))
    (hstk : exitStk ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    (hDropNz : mpl.base 547 ≠ 0#64)
    (hmain : MainOkCliExtPqB2NeedLocksPlacedAtWithF F mpl mmpl ext mainIdx inputsOf CodeOk
      libcAddr elf.brkStart stk lim) :
    ∀ X : UnreachedPqxdhPrimitives,
      CliSpecPqxdh (cliRunExtOnInputsSigAt mpl ext mainIdx inputsOf elf W) X ⟨W.C, W.Q⟩ := by
  intro X p hp
  let WP : PEParams := ⟨W.C, W.Q⟩
  obtain ⟨Run, hmainW, hclauses⟩ := hmain hDropNz X W hF hAesE hAesD hX hPub hF512 hEnc hDec hK
  obtain ⟨hInit, hSend, hWhisper, hPrekey, hBad⟩ := hclauses p hp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro b t hnone
    obtain ⟨a, hrun, hobs, hcommit⟩ := hInit b t hnone
    exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_call_obs hext hE htok hfs_eq
      hCode hH hmainW hstk hstk'
      (cliInputsOk_pqInitInputs WP p b t) (inputsLoadable_pqInitInputs WP p b t hp)
      hrun (not_isSendOverCap_pqInitInputs WP p b t)
      (not_isStdinOverCap_pqInitInputs WP p b t) hobs
      (coinsReadable_pqInitInputs WP p b t) hcommit
  · intro m r hm
    by_cases hstin : m.length > stdinCapBytes
    · simp only [hstin, ↓reduceIte]
      exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_stdinOverCap hext hE htok hfs_eq
        hCode hH hmainW hstk hstk'
        (cliInputsOk_pqSendInputs WP p m r) (inputsLoadable_pqSendInputs WP p m r hp)
        (isStdinOverCap_pqSendInputs WP p m r hstin)
    · simp only [hstin, ↓reduceIte]
      have hnstin : ¬ IsStdinOverCap (pqSendInputs WP p m r) :=
        not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)
      by_cases hover : m.length > maxPlaintextBytes
      · simp only [hover, ↓reduceIte]
        exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_sendOverCap hext hE htok hfs_eq
          hCode hH hmainW hstk hstk'
          (cliInputsOk_pqSendInputs WP p m r) (inputsLoadable_pqSendInputs WP p m r hp)
          (isSendOverCap_pqSendInputs WP p m r (by unfold maxPlaintextBytes at hover; exact hover))
          hnstin (coinsReadable_pqSendInputs WP p m r)
      · simp only [hover, ↓reduceIte]
        obtain ⟨a, hrun, hobs, hcommit⟩ := hSend m r hm
        exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_call_obs hext hE htok hfs_eq
          hCode hH hmainW hstk hstk'
          (cliInputsOk_pqSendInputs WP p m r) (inputsLoadable_pqSendInputs WP p m r hp)
          hrun
          (not_isSendOverCap_of_stdin_le
            (by simp only [pqSendInputs, pqInputs]; unfold maxPlaintextBytes at hover; omega))
          hnstin hobs (coinsReadable_pqSendInputs WP p m r) hcommit
  · intro c rc hc
    by_cases hstin : (wireWhisper :: c).length > stdinCapBytes
    · simp only [hstin, ↓reduceIte]
      exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_stdinOverCap hext hE htok hfs_eq
        hCode hH hmainW hstk hstk'
        (cliInputsOk_pqRecvInputs WP p (wireWhisper :: c) rc)
        (inputsLoadable_pqRecvInputs WP p (wireWhisper :: c) rc hp)
        (isStdinOverCap_pqRecvInputs WP p (wireWhisper :: c) rc hstin)
    · simp only [hstin, ↓reduceIte]
      obtain ⟨a, hrun, hobs, hcommit⟩ := hWhisper c rc hc
      exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_call_obs hext hE htok hfs_eq
        hCode hH hmainW hstk hstk'
        (cliInputsOk_pqRecvInputs WP p (wireWhisper :: c) rc)
        (inputsLoadable_pqRecvInputs WP p (wireWhisper :: c) rc hp)
        hrun (not_isSendOverCap_pqRecvInputs WP p (wireWhisper :: c) rc)
        (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)) hobs
        (coinsReadable_pqRecvInputs WP p (wireWhisper :: c) rc) hcommit
  · intro m rc hm hmatch
    by_cases hstin : (wirePrekey :: m.bytes).length > stdinCapBytes
    · simp only [hstin, ↓reduceIte]
      exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_stdinOverCap hext hE htok hfs_eq
        hCode hH hmainW hstk hstk'
        (cliInputsOk_pqRecvInputs WP p (wirePrekey :: m.bytes) rc)
        (inputsLoadable_pqRecvInputs WP p (wirePrekey :: m.bytes) rc hp)
        (isStdinOverCap_pqRecvInputs WP p (wirePrekey :: m.bytes) rc hstin)
    · simp only [hstin, ↓reduceIte]
      obtain ⟨a, hrun, hobs, hcommit⟩ := hPrekey m rc hm hmatch
      exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_call_obs hext hE htok hfs_eq
        hCode hH hmainW hstk hstk'
        (cliInputsOk_pqRecvInputs WP p (wirePrekey :: m.bytes) rc)
        (inputsLoadable_pqRecvInputs WP p (wirePrekey :: m.bytes) rc hp)
        hrun (not_isSendOverCap_pqRecvInputs WP p (wirePrekey :: m.bytes) rc)
        (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)) hobs
        (coinsReadable_pqRecvInputs WP p (wirePrekey :: m.bytes) rc) hcommit
  · intro c rc hc h2 h3
    by_cases hstin : c.length > stdinCapBytes
    · simp only [hstin, ↓reduceIte]
      exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_stdinOverCap hext hE htok hfs_eq
        hCode hH hmainW hstk hstk'
        (cliInputsOk_pqRecvInputs WP p c rc) (inputsLoadable_pqRecvInputs WP p c rc hp)
        (isStdinOverCap_pqRecvInputs WP p c rc hstin)
    · simp only [hstin, ↓reduceIte]
      obtain ⟨a, hrun, hobs, hcommit⟩ := hBad c rc hc h2 h3
      exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_call_obs hext hE htok hfs_eq
        hCode hH hmainW hstk hstk'
        (cliInputsOk_pqRecvInputs WP p c rc) (inputsLoadable_pqRecvInputs WP p c rc hp)
        hrun (not_isSendOverCap_pqRecvInputs WP p c rc)
        (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)) hobs
        (coinsReadable_pqRecvInputs WP p c rc) hcommit

theorem cliSpecPqxdhNoMatch_ext_strict_of_b2_needLocks_withF
    {F : ShaState → List (BitVec 8) → ShaState}
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {mainIdx : Nat}
    {inputsOf : Inputs → ProcessInputs} {exitStk : Nat} {libcAddr : BitVec 64}
    {CodeOk : Memory → Prop} {stk : Nat} {lim : BudgetLimits}
    {elf : ElfImage} {W : CliHooks}
    (hF : W.C.F = F)
    (hAesE : W.C.E = CryptoGames.AES256.aes256Enc)
    (hAesD : W.C.D = CryptoGames.AES256.aes256Dec)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (hF512 : W.Q.F512 = CryptoGames.SHA512.sha512CompressState)
    (hEnc : W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec)
    (hDec : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    (hext : ExternPreservesNoAllocFailed (ext W))
    (hE : ElfStaticOk elf)
    (htok : CliElfTokenCellsPlacedAt mpl elf)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hCode : ∀ m, CodeOk m → (cliProgExtPlacedAt mpl ext mainIdx W).CodeLoaded m)
    (hH : MuslHarnessFineNeedLocksPerInput exitStk libcAddr (patchElfTokensPlacedAt mpl elf)
      (cliProgExtPlacedAt mpl ext mainIdx W) (mpl.base mainIdx) inputsOf
      mmpl lim fineCostModel.init stk CodeOk (cliStaticsPlacedAt mpl))
    (hstk : exitStk ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    (hDropNz : mpl.base 547 ≠ 0#64)
    (hover : MainOkCliExtOverB2NeedLocksPlacedAtWithF F mpl mmpl ext mainIdx inputsOf CodeOk
      libcAddr elf.brkStart stk lim) :
    ∀ X : UnreachedPqxdhPrimitives,
      CliSpecPqxdhNoMatch (cliRunExtOnInputsSigAt mpl ext mainIdx inputsOf elf W) X ⟨W.C, W.Q⟩ := by
  intro X st hst x g hsess m rc hm hnomatch
  let WP : PEParams := ⟨W.C, W.Q⟩
  obtain ⟨Run, hmainW, hclause⟩ := hover hDropNz X W hF hAesE hAesD hX hPub hF512 hEnc hDec hK
  by_cases hstin : (wirePrekey :: m.bytes).length > stdinCapBytes
  · simp only [hstin, ↓reduceIte]
    exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_stdinOverCap hext hE htok hfs_eq
      hCode hH hmainW hstk hstk'
      (cliInputsOk_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
      (inputsLoadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hst)
      (isStdinOverCap_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hstin)
  · simp only [hstin, ↓reduceIte]
    obtain ⟨a, hrun, hobsEx, hcommit⟩ := hclause st hst x g hsess m rc hm hnomatch
    exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_call_pred hext hE htok hfs_eq hCode hH
      hmainW hstk hstk'
      (cliInputsOk_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
      (inputsLoadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hst)
      hrun (not_isSendOverCap_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
      (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin))
      hobsEx (coinsReadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc) hcommit

theorem cliPqxdhElfCorrectStrictPlaced2With_of_f3B2NeedLocks
    {F : ShaState → List (BitVec 8) → ShaState}
    {mpl mmpl : Obj.MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (hext : ∀ W : CliHooks, ExternPreservesNoAllocFailed (cliExternsPlaced mmpl W))
    (H : CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmain : MainOkCliF3PqB2NeedLocksPlacedAtWithF F mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hover : MainOkCliF3OverB2NeedLocksPlacedAtWithF F mpl mmpl CodeOk libcAddr elf.brkStart stk) :
    CliPqxdhElfCorrectStrictPlaced2With F mpl mmpl elf := by
  refine ⟨H.codeMatches, fun W hF hAesE hAesD hX hPub hF512 hEnc hDec hK X => ?_⟩
  dsimp only [LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced.cliRunPlacedSig]
  rw [cliRunPlacedSig_eq_cliRunExtPlacedSigAt_of_progEq2
    (cliProgExtPlacedSigAt_cliExternsPlaced_eq mpl mmpl W).symm]
  change CliSpecPqxdh
      (cliRunExtOnInputsSigAt mpl (cliExternsPlaced mmpl) 617 cliProcessInputs elf W) X ⟨W.C, W.Q⟩ ∧
    CliSpecPqxdhNoMatch
      (cliRunExtOnInputsSigAt mpl (cliExternsPlaced mmpl) 617 cliProcessInputs elf W) X ⟨W.C, W.Q⟩
  exact
    ⟨cliSpecPqxdh_ext_strict_of_b2_needLocks_withF
      hF hAesE hAesD hX hPub hF512 hEnc hDec hK (hext W) H.elfStaticOk H.tokenCells
      H.fsEq (H.codeLoaded W) (H.harness W) H.stkLo H.stkHi H.base547NeZero hmain X,
     cliSpecPqxdhNoMatch_ext_strict_of_b2_needLocks_withF
      hF hAesE hAesD hX hPub hF512 hEnc hDec hK (hext W) H.elfStaticOk H.tokenCells
      H.fsEq (H.codeLoaded W) (H.harness W) H.stkLo H.stkHi H.base547NeZero hover X⟩

theorem cliPqxdhElfCorrectStrictPlaced2With_of_f3B2NeedLocks'
    {F : ShaState → List (BitVec 8) → ShaState}
    {mpl mmpl : Obj.MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmain : MainOkCliF3PqB2NeedLocksPlacedAtWithF F mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hover : MainOkCliF3OverB2NeedLocksPlacedAtWithF F mpl mmpl CodeOk libcAddr elf.brkStart stk) :
    CliPqxdhElfCorrectStrictPlaced2With F mpl mmpl elf :=
  cliPqxdhElfCorrectStrictPlaced2With_of_f3B2NeedLocks
    (externPreservesNoAllocFailed_cliExternsPlaced mmpl) H hmain hover

theorem cliPqxdhElfCorrectPlacedWith_of_f3B2NeedLocks'
    {F : ShaState → List (BitVec 8) → ShaState}
    {mpl mmpl : Obj.MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmain : MainOkCliF3PqB2NeedLocksPlacedAtWithF F mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hover : MainOkCliF3OverB2NeedLocksPlacedAtWithF F mpl mmpl CodeOk libcAddr elf.brkStart stk) :
    CliPqxdhElfCorrectPlacedWith F mpl mmpl elf :=
  cliPqxdhElfCorrectPlacedWith_of_strict2With
    (cliPqxdhElfCorrectStrictPlaced2With_of_f3B2NeedLocks' H hmain hover)

/-! ## 2. Guarded `F`-Pinned `MainOk*GWithF` Predicates and Strict Composers -/

/-- Guarded `W.C.F = F` + real-AES `NeedLocks` + `argvAtRO` 5-clause PQXDH `main` specification. -/
@[expose] def MainOkCliExtPqB2NeedLocksPlacedAtGWithF
    (F : ShaState → List (BitVec 8) → ShaState)
    (mpl mmpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State))
    (mainIdx : Nat) (inputsOf : Inputs → ProcessInputs)
    (EntryGuard : State → Prop) (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) (lim : BudgetLimits) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    W.C.F = F →
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

/-- Guarded `W.C.F = F` + real-AES `NeedLocks` + `argvAtRO` `NoMatch` `main` specification. -/
@[expose] def MainOkCliExtOverB2NeedLocksPlacedAtGWithF
    (F : ShaState → List (BitVec 8) → ShaState)
    (mpl mmpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State))
    (mainIdx : Nat) (inputsOf : Inputs → ProcessInputs)
    (EntryGuard : State → Prop) (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) (lim : BudgetLimits) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    W.C.F = F →
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

abbrev MainOkCliF3PqB2NeedLocksPlacedAtGWithF
    (F : ShaState → List (BitVec 8) → ShaState)
    (mpl mmpl : Obj.MultiPlacement) (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) : Prop :=
  MainOkCliExtPqB2NeedLocksPlacedAtGWithF F mpl mmpl (cliExternsPlaced mmpl) 617 cliProcessInputs
    (F3SampleNttEntryGuard mpl mmpl) CodeOk libcAddr brkStart stk cliBudgetLimits

abbrev MainOkCliF3OverB2NeedLocksPlacedAtGWithF
    (F : ShaState → List (BitVec 8) → ShaState)
    (mpl mmpl : Obj.MultiPlacement) (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) : Prop :=
  MainOkCliExtOverB2NeedLocksPlacedAtGWithF F mpl mmpl (cliExternsPlaced mmpl) 617 cliProcessInputs
    (F3SampleNttEntryGuard mpl mmpl) CodeOk libcAddr brkStart stk cliBudgetLimits

theorem mainOkCliF3PqGWithF_of_block617TransferFixedG
    {F : ShaState → List (BitVec 8) → ShaState}
    {mpl mmpl : Obj.MultiPlacement}
    {EG : CliHooks → String → Option (State → State)}
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (hTr : Block617TransferFixedHypG mpl mmpl EG (cliExternsPlaced mmpl)
      (F3SampleNttEntryGuard mpl mmpl) CodeOk_ghost CodeOk_real libcAddr brkStart stk)
    (hGhost : MainOkCliExtPqB2NeedLocksPlacedAtWithF F mpl mmpl EG 617 cliProcessInputs
      CodeOk_ghost libcAddr brkStart stk cliBudgetLimits) :
    MainOkCliF3PqB2NeedLocksPlacedAtGWithF F mpl mmpl CodeOk_real libcAddr brkStart stk := by
  intro hDropNz X W hF hE hD hX hPub hF512 hEnc hDec hK
  obtain ⟨Run, hmainW, hclauses⟩ := hGhost hDropNz X W hF hE hD hX hPub hF512 hEnc hDec hK
  exact ⟨Run, hTr W Run hmainW, hclauses⟩

theorem mainOkCliF3PqGWithF_of_block617TransferFixedGAes
    {F : ShaState → List (BitVec 8) → ShaState}
    {mpl mmpl : Obj.MultiPlacement}
    {EG : CliHooks → String → Option (State → State)}
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (hTr : ∀ W : CliHooks,
      W.C.F = F →
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
    (hGhost : MainOkCliExtPqB2NeedLocksPlacedAtWithF F mpl mmpl EG 617 cliProcessInputs
      CodeOk_ghost libcAddr brkStart stk cliBudgetLimits) :
    MainOkCliF3PqB2NeedLocksPlacedAtGWithF F mpl mmpl CodeOk_real libcAddr brkStart stk := by
  intro hDropNz X W hF hE hD hX hPub hF512 hEnc hDec hK
  obtain ⟨Run, hmainW, hclauses⟩ := hGhost hDropNz X W hF hE hD hX hPub hF512 hEnc hDec hK
  exact ⟨Run, hTr W hF hE hD hX hPub hF512 hEnc hDec hK Run hmainW, hclauses⟩

theorem mainOkCliF3OverGWithF_of_block617TransferFixedG
    {F : ShaState → List (BitVec 8) → ShaState}
    {mpl mmpl : Obj.MultiPlacement}
    {EG : CliHooks → String → Option (State → State)}
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (hTr : Block617TransferFixedHypG mpl mmpl EG (cliExternsPlaced mmpl)
      (F3SampleNttEntryGuard mpl mmpl) CodeOk_ghost CodeOk_real libcAddr brkStart stk)
    (hGhost : MainOkCliExtOverB2NeedLocksPlacedAtWithF F mpl mmpl EG 617 cliProcessInputs
      CodeOk_ghost libcAddr brkStart stk cliBudgetLimits) :
    MainOkCliF3OverB2NeedLocksPlacedAtGWithF F mpl mmpl CodeOk_real libcAddr brkStart stk := by
  intro hDropNz X W hF hE hD hX hPub hF512 hEnc hDec hK
  obtain ⟨Run, hmainW, hclauses⟩ := hGhost hDropNz X W hF hE hD hX hPub hF512 hEnc hDec hK
  exact ⟨Run, hTr W Run hmainW, hclauses⟩

theorem mainOkCliF3OverGWithF_of_block617TransferFixedGAes
    {F : ShaState → List (BitVec 8) → ShaState}
    {mpl mmpl : Obj.MultiPlacement}
    {EG : CliHooks → String → Option (State → State)}
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (hTr : ∀ W : CliHooks,
      W.C.F = F →
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
    (hGhost : MainOkCliExtOverB2NeedLocksPlacedAtWithF F mpl mmpl EG 617 cliProcessInputs
      CodeOk_ghost libcAddr brkStart stk cliBudgetLimits) :
    MainOkCliF3OverB2NeedLocksPlacedAtGWithF F mpl mmpl CodeOk_real libcAddr brkStart stk := by
  intro hDropNz X W hF hE hD hX hPub hF512 hEnc hDec hK
  obtain ⟨Run, hmainW, hclauses⟩ := hGhost hDropNz X W hF hE hD hX hPub hF512 hEnc hDec hK
  exact ⟨Run, hTr W hF hE hD hX hPub hF512 hEnc hDec hK Run hmainW, hclauses⟩

theorem cliSpecPqxdh_ext_strict_of_b2_needLocks_guarded_withF
    {F : ShaState → List (BitVec 8) → ShaState}
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {mainIdx : Nat}
    {inputsOf : Inputs → ProcessInputs} {EntryGuard : State → Prop}
    {exitStk : Nat} {libcAddr : BitVec 64}
    {CodeOk : Memory → Prop} {stk : Nat} {lim : BudgetLimits}
    {elf : ElfImage} {W : CliHooks}
    (hF : W.C.F = F)
    (hAesE : W.C.E = CryptoGames.AES256.aes256Enc)
    (hAesD : W.C.D = CryptoGames.AES256.aes256Dec)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (hF512 : W.Q.F512 = CryptoGames.SHA512.sha512CompressState)
    (hEnc : W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec)
    (hDec : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
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
    (hmain : MainOkCliExtPqB2NeedLocksPlacedAtGWithF F mpl mmpl ext mainIdx inputsOf EntryGuard
      CodeOk libcAddr elf.brkStart stk lim) :
    ∀ X : UnreachedPqxdhPrimitives,
      CliSpecPqxdh (cliRunExtOnInputsSigAt mpl ext mainIdx inputsOf elf W) X ⟨W.C, W.Q⟩ := by
  intro X p hp
  let WP : PEParams := ⟨W.C, W.Q⟩
  obtain ⟨Run, hmainW, hclauses⟩ := hmain hDropNz X W hF hAesE hAesD hX hPub hF512 hEnc hDec hK
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

theorem cliSpecPqxdhNoMatch_ext_strict_of_b2_needLocks_guarded_withF
    {F : ShaState → List (BitVec 8) → ShaState}
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {mainIdx : Nat}
    {inputsOf : Inputs → ProcessInputs} {EntryGuard : State → Prop}
    {exitStk : Nat} {libcAddr : BitVec 64}
    {CodeOk : Memory → Prop} {stk : Nat} {lim : BudgetLimits}
    {elf : ElfImage} {W : CliHooks}
    (hF : W.C.F = F)
    (hAesE : W.C.E = CryptoGames.AES256.aes256Enc)
    (hAesD : W.C.D = CryptoGames.AES256.aes256Dec)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (hF512 : W.Q.F512 = CryptoGames.SHA512.sha512CompressState)
    (hEnc : W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec)
    (hDec : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
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
    (hover : MainOkCliExtOverB2NeedLocksPlacedAtGWithF F mpl mmpl ext mainIdx inputsOf EntryGuard
      CodeOk libcAddr elf.brkStart stk lim) :
    ∀ X : UnreachedPqxdhPrimitives,
      CliSpecPqxdhNoMatch (cliRunExtOnInputsSigAt mpl ext mainIdx inputsOf elf W) X ⟨W.C, W.Q⟩ := by
  intro X st hst x g hsess m rc hm hnomatch
  let WP : PEParams := ⟨W.C, W.Q⟩
  obtain ⟨Run, hmainW, hclause⟩ := hover hDropNz X W hF hAesE hAesD hX hPub hF512 hEnc hDec hK
  by_cases hstin : (wirePrekey :: m.bytes).length > stdinCapBytes
  · simp only [hstin, ↓reduceIte]
    exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_stdinOverCap hext hE htok hfs_eq
      hCode hH hmainW hstk hstk'
      (cliInputsOk_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
      (inputsLoadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hst)
      (isStdinOverCap_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hstin)
  · simp only [hstin, ↓reduceIte]
    obtain ⟨a, hrun, hobsEx, hcommit⟩ := hclause st hst x g hsess m rc hm hnomatch
    exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_call_pred hext hE htok hfs_eq hCode hH
      hmainW hstk hstk'
      (cliInputsOk_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
      (inputsLoadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hst)
      hrun (not_isSendOverCap_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
      (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin))
      hobsEx (coinsReadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc) hcommit

private def dummyUnreachedWithF : UnreachedPqxdhPrimitives where
  sigPkGen := fun _ => []
  sigSign := fun _ _ _ => []
  scalarMul := fun _ _ => []
  scalarAdd := fun _ _ => []
  kemKeyGen := fun _ => ([], [])
  pow8 := fun _ => []
  isValidDhTriple := fun _ _ _ => false

/-- Per-input `pqInitInputs` strict outcome under `¬ CliReachesSampleNttStuckPlaced`. -/
theorem cliRunPlacedSig_pqInit_strict_of_f3B2NeedLocksG'
    {F : ShaState → List (BitVec 8) → ShaState}
    {mpl mmpl : Obj.MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3B2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
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
      ¬ CliReachesSampleNttStuckPlaced mpl mmpl elf W (pqInitInputs ⟨W.C, W.Q⟩ p b t)) :
    cliRunPlacedSig mpl mmpl elf W (pqInitInputs ⟨W.C, W.Q⟩ p b t) =
      some (pqxdhExpectedOutcome ⟨W.C, W.Q⟩ (pqInitInputs ⟨W.C, W.Q⟩ p b t)
        (pqInitModel X ⟨W.C, W.Q⟩ p b t)) := by
  let WP : PEParams := ⟨W.C, W.Q⟩
  obtain ⟨Run, hmainW, hclauses⟩ :=
    hmain H.base547NeZero X W hF hAesE hAesD hX hPub hF512 hEnc hDec hK
  obtain ⟨a, hrun, hobs, hcommit⟩ := (hclauses p hp).1 b t hnone
  exact cliRunPlacedSig_of_strict_f3_sampleNtt_call_obs
    (externPreservesNoAllocFailed_cliExternsPlaced mmpl W) H hmainW
    (cliInputsOk_pqInitInputs WP p b t) (inputsLoadable_pqInitInputs WP p b t hp)
    hrun (not_isSendOverCap_pqInitInputs WP p b t)
    (not_isStdinOverCap_pqInitInputs WP p b t) hobs
    (coinsReadable_pqInitInputs WP p b t) hcommit hNoStuck

/-- Per-input `pqSendInputs` strict outcome under `¬ CliReachesSampleNttStuckPlaced`. -/
theorem cliRunPlacedSig_pqSend_strict_of_f3B2NeedLocksG'
    {F : ShaState → List (BitVec 8) → ShaState}
    {mpl mmpl : Obj.MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3B2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
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
      ¬ CliReachesSampleNttStuckPlaced mpl mmpl elf W (pqSendInputs ⟨W.C, W.Q⟩ p m r)) :
    cliRunPlacedSig mpl mmpl elf W (pqSendInputs ⟨W.C, W.Q⟩ p m r) =
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
    hmain H.base547NeZero dummyUnreachedWithF W hF hAesE hAesD hX hPub hF512 hEnc hDec hK
  by_cases hstin : m.length > stdinCapBytes
  · simp only [hstin, ↓reduceIte]
    exact cliRunPlacedSig_of_strict_f3_sampleNtt_stdinOverCap hextW H hmainW
      (cliInputsOk_pqSendInputs WP p m r) (inputsLoadable_pqSendInputs WP p m r hp)
      (isStdinOverCap_pqSendInputs WP p m r hstin) hNoStuck
  · simp only [hstin, ↓reduceIte]
    have hnstin : ¬ IsStdinOverCap (pqSendInputs WP p m r) :=
      not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)
    by_cases hovc : m.length > maxPlaintextBytes
    · simp only [hovc, ↓reduceIte]
      exact cliRunPlacedSig_of_strict_f3_sampleNtt_sendOverCap hextW H hmainW
        (cliInputsOk_pqSendInputs WP p m r) (inputsLoadable_pqSendInputs WP p m r hp)
        (isSendOverCap_pqSendInputs WP p m r (by unfold maxPlaintextBytes at hovc; exact hovc))
        hnstin (coinsReadable_pqSendInputs WP p m r) hNoStuck
    · simp only [hovc, ↓reduceIte]
      obtain ⟨a, hrun, hobs, hcommit⟩ := (hclauses p hp).2.1 m r hm
      exact cliRunPlacedSig_of_strict_f3_sampleNtt_call_obs hextW H hmainW
        (cliInputsOk_pqSendInputs WP p m r) (inputsLoadable_pqSendInputs WP p m r hp)
        hrun
        (not_isSendOverCap_of_stdin_le
          (by simp only [pqSendInputs, pqInputs]; unfold maxPlaintextBytes at hovc; omega))
        hnstin hobs (coinsReadable_pqSendInputs WP p m r) hcommit hNoStuck

/-- Per-input `pqRecvInputs ... (wireWhisper :: c)` strict outcome under
`¬ CliReachesSampleNttStuckPlaced`. -/
theorem cliRunPlacedSig_pqRecvWhisper_strict_of_f3B2NeedLocksG'
    {F : ShaState → List (BitVec 8) → ShaState}
    {mpl mmpl : Obj.MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3B2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
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
      ¬ CliReachesSampleNttStuckPlaced mpl mmpl elf W
          (pqRecvInputs ⟨W.C, W.Q⟩ p (wireWhisper :: c) rc)) :
    cliRunPlacedSig mpl mmpl elf W (pqRecvInputs ⟨W.C, W.Q⟩ p (wireWhisper :: c) rc) =
      if (wireWhisper :: c).length > stdinCapBytes then
        some (.exited 2 [] (filesOf (pqRecvInputs ⟨W.C, W.Q⟩ p (wireWhisper :: c) rc).files))
      else
        some (pqxdhExpectedOutcome ⟨W.C, W.Q⟩
          (pqRecvInputs ⟨W.C, W.Q⟩ p (wireWhisper :: c) rc)
          (pqRecvWhisperModel ⟨W.C, W.Q⟩ p c rc)) := by
  let WP : PEParams := ⟨W.C, W.Q⟩
  have hextW := externPreservesNoAllocFailed_cliExternsPlaced mmpl W
  obtain ⟨Run, hmainW, hclauses⟩ :=
    hmain H.base547NeZero dummyUnreachedWithF W hF hAesE hAesD hX hPub hF512 hEnc hDec hK
  by_cases hstin : (wireWhisper :: c).length > stdinCapBytes
  · simp only [hstin, ↓reduceIte]
    exact cliRunPlacedSig_of_strict_f3_sampleNtt_stdinOverCap hextW H hmainW
      (cliInputsOk_pqRecvInputs WP p (wireWhisper :: c) rc)
      (inputsLoadable_pqRecvInputs WP p (wireWhisper :: c) rc hp)
      (isStdinOverCap_pqRecvInputs WP p (wireWhisper :: c) rc hstin) hNoStuck
  · simp only [hstin, ↓reduceIte]
    obtain ⟨a, hrun, hobs, hcommit⟩ := (hclauses p hp).2.2.1 c rc hc
    exact cliRunPlacedSig_of_strict_f3_sampleNtt_call_obs hextW H hmainW
      (cliInputsOk_pqRecvInputs WP p (wireWhisper :: c) rc)
      (inputsLoadable_pqRecvInputs WP p (wireWhisper :: c) rc hp)
      hrun (not_isSendOverCap_pqRecvInputs WP p (wireWhisper :: c) rc)
      (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)) hobs
      (coinsReadable_pqRecvInputs WP p (wireWhisper :: c) rc) hcommit hNoStuck

/-- Per-input `pqRecvInputs ... (wirePrekey :: m.bytes)` empty/matching-session strict outcome
under `¬ CliReachesSampleNttStuckPlaced`. -/
theorem cliRunPlacedSig_pqRecvPrekeyMatch_strict_of_f3B2NeedLocksG'
    {F : ShaState → List (BitVec 8) → ShaState}
    {mpl mmpl : Obj.MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3B2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
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
      ¬ CliReachesSampleNttStuckPlaced mpl mmpl elf W
          (pqRecvInputs ⟨W.C, W.Q⟩ p (wirePrekey :: m.bytes) rc)) :
    cliRunPlacedSig mpl mmpl elf W (pqRecvInputs ⟨W.C, W.Q⟩ p (wirePrekey :: m.bytes) rc) =
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
    exact cliRunPlacedSig_of_strict_f3_sampleNtt_stdinOverCap hextW H hmainW
      (cliInputsOk_pqRecvInputs WP p (wirePrekey :: m.bytes) rc)
      (inputsLoadable_pqRecvInputs WP p (wirePrekey :: m.bytes) rc hp)
      (isStdinOverCap_pqRecvInputs WP p (wirePrekey :: m.bytes) rc hstin) hNoStuck
  · simp only [hstin, ↓reduceIte]
    obtain ⟨a, hrun, hobs, hcommit⟩ := (hclauses p hp).2.2.2.1 m rc hm hmatch
    exact cliRunPlacedSig_of_strict_f3_sampleNtt_call_obs hextW H hmainW
      (cliInputsOk_pqRecvInputs WP p (wirePrekey :: m.bytes) rc)
      (inputsLoadable_pqRecvInputs WP p (wirePrekey :: m.bytes) rc hp)
      hrun (not_isSendOverCap_pqRecvInputs WP p (wirePrekey :: m.bytes) rc)
      (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)) hobs
      (coinsReadable_pqRecvInputs WP p (wirePrekey :: m.bytes) rc) hcommit hNoStuck

/-- Per-input untagged `pqRecvInputs` strict outcome under `¬ CliReachesSampleNttStuckPlaced`. -/
theorem cliRunPlacedSig_pqRecvBad_strict_of_f3B2NeedLocksG'
    {F : ShaState → List (BitVec 8) → ShaState}
    {mpl mmpl : Obj.MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3B2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
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
      ¬ CliReachesSampleNttStuckPlaced mpl mmpl elf W (pqRecvInputs ⟨W.C, W.Q⟩ p c rc)) :
    cliRunPlacedSig mpl mmpl elf W (pqRecvInputs ⟨W.C, W.Q⟩ p c rc) =
      if c.length > stdinCapBytes then
        some (.exited 2 [] (filesOf (pqRecvInputs ⟨W.C, W.Q⟩ p c rc).files))
      else
        some (.exited 1 [] (filesOf (pqRecvInputs ⟨W.C, W.Q⟩ p c rc).files)) := by
  let WP : PEParams := ⟨W.C, W.Q⟩
  have hextW := externPreservesNoAllocFailed_cliExternsPlaced mmpl W
  obtain ⟨Run, hmainW, hclauses⟩ :=
    hmain H.base547NeZero dummyUnreachedWithF W hF hAesE hAesD hX hPub hF512 hEnc hDec hK
  by_cases hstin : c.length > stdinCapBytes
  · simp only [hstin, ↓reduceIte]
    exact cliRunPlacedSig_of_strict_f3_sampleNtt_stdinOverCap hextW H hmainW
      (cliInputsOk_pqRecvInputs WP p c rc) (inputsLoadable_pqRecvInputs WP p c rc hp)
      (isStdinOverCap_pqRecvInputs WP p c rc hstin) hNoStuck
  · simp only [hstin, ↓reduceIte]
    obtain ⟨a, hrun, hobs, hcommit⟩ := (hclauses p hp).2.2.2.2 c rc hc h2 h3
    exact cliRunPlacedSig_of_strict_f3_sampleNtt_call_obs hextW H hmainW
      (cliInputsOk_pqRecvInputs WP p c rc) (inputsLoadable_pqRecvInputs WP p c rc hp)
      hrun (not_isSendOverCap_pqRecvInputs WP p c rc)
      (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)) hobs
      (coinsReadable_pqRecvInputs WP p c rc) hcommit hNoStuck

/-- Per-input `pqRecvInputs ... (wirePrekey :: m.bytes)` non-matching-session strict outcome under
`¬ CliReachesSampleNttStuckPlaced`. -/
theorem cliRunPlacedSig_pqRecvNoMatch_strict_of_f3B2NeedLocksG'
    {F : ShaState → List (BitVec 8) → ShaState}
    {mpl mmpl : Obj.MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3B2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
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
      ¬ CliReachesSampleNttStuckPlaced mpl mmpl elf W
          (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: m.bytes) rc)) :
    if (wirePrekey :: m.bytes).length > stdinCapBytes then
      cliRunPlacedSig mpl mmpl elf W (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: m.bytes) rc) =
        some (.exited 2 [] (filesOf (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: m.bytes) rc).files))
    else
      ∃ o : Outcome,
        cliRunPlacedSig mpl mmpl elf W (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: m.bytes) rc) =
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
    exact cliRunPlacedSig_of_strict_f3_sampleNtt_stdinOverCap hextW H hmainW
      (cliInputsOk_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
      (inputsLoadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hst)
      (isStdinOverCap_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hstin) hNoStuck
  · simp only [hstin, ↓reduceIte]
    obtain ⟨a, hrun, hobsEx, hcommit⟩ := hclause st hst x g hsess m rc hm hnomatch
    exact cliRunPlacedSig_of_strict_f3_sampleNtt_call_pred hextW H hmainW
      (cliInputsOk_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
      (inputsLoadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hst)
      hrun (not_isSendOverCap_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
      (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin))
      hobsEx (coinsReadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc) hcommit hNoStuck

theorem cliPqxdhElfCorrectStrictPlaced2With_of_f3B2NeedLocksG
    {F : ShaState → List (BitVec 8) → ShaState}
    {mpl mmpl : Obj.MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (hext : ∀ W : CliHooks, ExternPreservesNoAllocFailed (cliExternsPlaced mmpl W))
    (H : CliElfF3B2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
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
        ¬ CliReachesSampleNttStuckPlaced mpl mmpl elf W i) :
    CliPqxdhElfCorrectStrictPlaced2With F mpl mmpl elf := by
  refine ⟨H.codeMatches, fun W hF hAesE hAesD hX hPub hF512 hEnc hDec hK X => ?_⟩
  let WP : PEParams := ⟨W.C, W.Q⟩
  have hNS := hNoStuck W hF hAesE hAesD hX hPub hF512 hEnc hDec hK
  refine ⟨?_, ?_⟩
  · intro p hp
    obtain ⟨Run, hmainW, hclauses⟩ :=
      hmain H.base547NeZero X W hF hAesE hAesD hX hPub hF512 hEnc hDec hK
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
      hover H.base547NeZero X W hF hAesE hAesD hX hPub hF512 hEnc hDec hK
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

theorem cliPqxdhElfCorrectStrictPlaced2With_of_f3B2NeedLocksG'
    {F : ShaState → List (BitVec 8) → ShaState}
    {mpl mmpl : Obj.MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3B2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
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
        ¬ CliReachesSampleNttStuckPlaced mpl mmpl elf W i) :
    CliPqxdhElfCorrectStrictPlaced2With F mpl mmpl elf :=
  cliPqxdhElfCorrectStrictPlaced2With_of_f3B2NeedLocksG
    (externPreservesNoAllocFailed_cliExternsPlaced mmpl) H hmain hover hNoStuck

theorem cliPqxdhElfCorrectPlacedWith_of_f3B2NeedLocksG'
    {F : ShaState → List (BitVec 8) → ShaState}
    {mpl mmpl : Obj.MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3B2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
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
        CliReachesSampleNttStuckPlaced mpl mmpl elf W i →
        cliRunPlacedSig mpl mmpl elf W i = none) :
    CliPqxdhElfCorrectPlacedWith F mpl mmpl elf := by
  refine ⟨H.codeMatches, fun W hF hAesE hAesD hX hPub hF512 hEnc hDec hK X => ?_⟩
  let WP : PEParams := ⟨W.C, W.Q⟩
  have hSD := hStuckDiv W hF hAesE hAesD hX hPub hF512 hEnc hDec hK
  refine ⟨?_, ?_⟩
  · intro p hp
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro b t hnone
      have hiDom : CliPqxdhInputs WP (pqInitInputs WP p b t) :=
        ⟨p, hp, Or.inl ⟨hnone, b, t, rfl⟩⟩
      by_cases hStuck : CliReachesSampleNttStuckPlaced mpl mmpl elf W (pqInitInputs WP p b t)
      · exact Or.inr ⟨hSD _ hiDom hStuck, Or.inr hStuck⟩
      · exact outcomeOrExcusedAbort_of_eq
          (cliRunPlacedSig_pqInit_strict_of_f3B2NeedLocksG' H hmain W hF hAesE hAesD hX hPub hF512
            hEnc hDec hK X p hp b t hnone hStuck)
    · intro m r hm
      have hiDom : CliPqxdhInputs WP (pqSendInputs WP p m r) :=
        ⟨p, hp, Or.inr (Or.inl ⟨m, r, hm, rfl⟩)⟩
      by_cases hStuck : CliReachesSampleNttStuckPlaced mpl mmpl elf W (pqSendInputs WP p m r)
      · exact Or.inr ⟨hSD _ hiDom hStuck, Or.inr hStuck⟩
      · have hEq :=
          cliRunPlacedSig_pqSend_strict_of_f3B2NeedLocksG' H hmain W hF hAesE hAesD hX hPub hF512
            hEnc hDec hK p hp m r hm hStuck
        refine outcomeOrExcusedAbort_of_eq ?_
        split_ifs at hEq ⊢ <;> exact hEq
    · intro c rc hc
      have hiDom : CliPqxdhInputs WP (pqRecvInputs WP p (wireWhisper :: c) rc) :=
        ⟨p, hp, Or.inr (Or.inr (Or.inl ⟨c, rc, hc, rfl⟩))⟩
      by_cases hStuck :
          CliReachesSampleNttStuckPlaced mpl mmpl elf W (pqRecvInputs WP p (wireWhisper :: c) rc)
      · exact Or.inr ⟨hSD _ hiDom hStuck, Or.inr hStuck⟩
      · have hEq :=
          cliRunPlacedSig_pqRecvWhisper_strict_of_f3B2NeedLocksG' H hmain W hF hAesE hAesD hX hPub
            hF512 hEnc hDec hK p hp c rc hc hStuck
        refine outcomeOrExcusedAbort_of_eq ?_
        split_ifs at hEq ⊢ <;> exact hEq
    · intro m rc hm hmatch
      have hiDom : CliPqxdhInputs WP (pqRecvInputs WP p (wirePrekey :: m.bytes) rc) :=
        ⟨p, hp, Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rc, hm, rfl⟩)))⟩
      by_cases hStuck :
          CliReachesSampleNttStuckPlaced mpl mmpl elf W (pqRecvInputs WP p (wirePrekey :: m.bytes) rc)
      · exact Or.inr ⟨hSD _ hiDom hStuck, Or.inr hStuck⟩
      · have hEq :=
          cliRunPlacedSig_pqRecvPrekeyMatch_strict_of_f3B2NeedLocksG' H hmain W hF hAesE hAesD hX
            hPub hF512 hEnc hDec hK X p hp m rc hm hmatch hStuck
        refine outcomeOrExcusedAbort_of_eq ?_
        split_ifs at hEq ⊢ <;> exact hEq
    · intro c rc hc h2 h3
      have hiDom : CliPqxdhInputs WP (pqRecvInputs WP p c rc) :=
        ⟨p, hp, Or.inr (Or.inr (Or.inr (Or.inr ⟨c, rc, hc, h2, h3, rfl⟩)))⟩
      by_cases hStuck : CliReachesSampleNttStuckPlaced mpl mmpl elf W (pqRecvInputs WP p c rc)
      · exact Or.inr ⟨hSD _ hiDom hStuck, Or.inr hStuck⟩
      · have hEq :=
          cliRunPlacedSig_pqRecvBad_strict_of_f3B2NeedLocksG' H hmain W hF hAesE hAesD hX hPub hF512
            hEnc hDec hK p hp c rc hc h2 h3 hStuck
        refine outcomeOrExcusedAbort_of_eq ?_
        split_ifs at hEq ⊢ <;> exact hEq
  · intro st hst x g hsess m rc hm hnomatch
    have hiDom : CliPqxdhInputs WP (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) :=
      ⟨st, hst, Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rc, hm, rfl⟩)))⟩
    by_cases hStuck :
        CliReachesSampleNttStuckPlaced mpl mmpl elf W (pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
    · exact Or.inr ⟨hSD _ hiDom hStuck, Or.inr hStuck⟩
    · have hNM :=
        cliRunPlacedSig_pqRecvNoMatch_strict_of_f3B2NeedLocksG' H hover W hF hAesE hAesD hX hPub
          hF512 hEnc hDec hK X st hst x g hsess m rc hm hnomatch hStuck
      refine Or.inl ?_
      by_cases hstin : (wirePrekey :: m.bytes).length > stdinCapBytes
      · simp only [hstin, ↓reduceIte] at hNM
        exact ⟨_, hNM, by simp only [hstin, ↓reduceIte]⟩
      · simp only [hstin, ↓reduceIte] at hNM
        obtain ⟨o, ho, hpo⟩ := hNM
        exact ⟨o, ho, by simp only [hstin, ↓reduceIte]; exact hpo⟩

/-- Per-input `¬ CliReachesOOMPlaced` bridge under `¬ CliReachesSampleNttStuckPlaced` across all
6 clauses of `CliPqxdhInputs ⟨W.C, W.Q⟩`. -/
theorem not_cliReachesOOMPlaced_of_f3B2NeedLocksG_notStuck
    {F : ShaState → List (BitVec 8) → ShaState}
    {mpl mmpl : Obj.MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3B2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
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
    (hNoStuck : ¬ CliReachesSampleNttStuckPlaced mpl mmpl elf W i) :
    ¬ CliReachesOOMPlaced mpl mmpl elf W i := by
  suffices hEx : ∃ o : Outcome, cliRunPlacedSig mpl mmpl elf W i = some o by
    obtain ⟨o, ho⟩ := hEx
    exact not_cliReachesOOMPlaced_of_cliRunsToPlaced (cliRunsToPlaced_of_cliRunPlacedSig_eq_some ho)
  rcases hi with ⟨st, hdom, hclause⟩
  rcases hclause with
      ⟨hnone, b, t, rfl⟩ |
      ⟨m, r, hlen, rfl⟩ |
      ⟨c, rc, hlen, rfl⟩ |
      ⟨m, rc, hlen, rfl⟩ |
      ⟨c, rc, hlen, hhw, hhp, rfl⟩
  · exact ⟨_, cliRunPlacedSig_pqInit_strict_of_f3B2NeedLocksG' H hmain W hF hE hD hX hPub hF512
      hEnc hDec hK dummyUnreachedWithF st hdom b t hnone hNoStuck⟩
  · have h := cliRunPlacedSig_pqSend_strict_of_f3B2NeedLocksG' H hmain W hF hE hD hX hPub hF512
      hEnc hDec hK st hdom m r hlen hNoStuck
    by_cases h1 : m.length > stdinCapBytes
    · simp only [h1, ↓reduceIte] at h; exact ⟨_, h⟩
    · by_cases h2 : m.length > maxPlaintextBytes <;>
        simp only [h1, h2, ↓reduceIte] at h <;> exact ⟨_, h⟩
  · have h := cliRunPlacedSig_pqRecvWhisper_strict_of_f3B2NeedLocksG' H hmain W hF hE hD hX hPub
      hF512 hEnc hDec hK st hdom c rc hlen hNoStuck
    by_cases h1 : (wireWhisper :: c).length > stdinCapBytes <;>
      simp only [h1, ↓reduceIte] at h <;> exact ⟨_, h⟩
  · cases hsess : st.session with
    | none =>
      have h := cliRunPlacedSig_pqRecvPrekeyMatch_strict_of_f3B2NeedLocksG' H hmain W hF hE hD hX
        hPub hF512 hEnc hDec hK dummyUnreachedWithF st hdom m rc hlen
        (fun _ _ h' => by rw [hsess] at h'; cases h') hNoStuck
      by_cases h1 : (wirePrekey :: m.bytes).length > stdinCapBytes <;>
        simp only [h1, ↓reduceIte] at h <;> exact ⟨_, h⟩
    | some xg =>
      rcases xg with ⟨x, g⟩
      by_cases hm : PqSessionMatches x g m
      · have h := cliRunPlacedSig_pqRecvPrekeyMatch_strict_of_f3B2NeedLocksG' H hmain W hF hE hD hX
          hPub hF512 hEnc hDec hK dummyUnreachedWithF st hdom m rc hlen
          (fun x' g' h' => by
            rw [hsess] at h'
            injection h' with hpair
            cases hpair
            exact hm) hNoStuck
        by_cases h1 : (wirePrekey :: m.bytes).length > stdinCapBytes <;>
          simp only [h1, ↓reduceIte] at h <;> exact ⟨_, h⟩
      · have h := cliRunPlacedSig_pqRecvNoMatch_strict_of_f3B2NeedLocksG' H hover W hF hE hD hX
          hPub hF512 hEnc hDec hK dummyUnreachedWithF st hdom x g hsess m rc hlen hm hNoStuck
        by_cases h1 : (wirePrekey :: m.bytes).length > stdinCapBytes
        · simp only [h1, ↓reduceIte] at h; exact ⟨_, h⟩
        · simp only [h1, ↓reduceIte] at h
          obtain ⟨o, ho, _⟩ := h
          exact ⟨o, ho⟩
  · have h := cliRunPlacedSig_pqRecvBad_strict_of_f3B2NeedLocksG' H hmain W hF hE hD hX hPub hF512
      hEnc hDec hK st hdom c rc hlen hhw hhp hNoStuck
    by_cases h1 : c.length > stdinCapBytes <;>
      simp only [h1, ↓reduceIte] at h <;> exact ⟨_, h⟩

/-! ## 3. `¬ CliReachesOOMPlaced` Bridge for `CliPqxdhElfCorrectStrictPlaced2With` -/

theorem hAlloc_of_cliPqxdhElfCorrectStrictPlaced2With
    {F : ShaState → List (BitVec 8) → ShaState}
    {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage}
    (hStrict : CliPqxdhElfCorrectStrictPlaced2With F mpl mmpl elf)
    (W : CliHooks)
    (hF : W.C.F = F)
    (hE : W.C.E = CryptoGames.AES256.aes256Enc)
    (hD : W.C.D = CryptoGames.AES256.aes256Dec)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (hF512 : W.Q.F512 = CryptoGames.SHA512.sha512CompressState)
    (hEnc : W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec)
    (hDec : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental) :
    ∀ i : Inputs, CliPqxdhInputs ⟨W.C, W.Q⟩ i → ¬ CliReachesOOMPlaced mpl mmpl elf W i :=
  fun i hi => not_cliReachesOOMPlaced_of_strict
    (hStrict.2 W hF hE hD hX hPub hF512 hEnc hDec hK) i hi

end LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2GWithF
