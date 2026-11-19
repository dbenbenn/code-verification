/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Placed.CliPlainPanPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomProofF3G -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomSpecF3 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MatchingPathBF3
import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3NonCanonF3
import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3
import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3UntypedElfF3
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2G
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2GWithF -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3ExternNoAllocFail
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.PlacedOomRecovery2
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.PlainPlacedComposer -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG
import LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.BundleInitElfF3
public import LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.ElfInputsExtF3 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Parity.FilesExtParity
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Process
import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Kdf
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq

/-!
# Plain-Memory Two-Placement Whole-Process ELF Interface & Assembly (`D3BinaryOomPlainF3`)

Plain-memory (`elf.loadState` without `cliTokenPatchPlaced`) siblings of `D3BinaryOomSpecF3`,
`ElfInputsExtF3`, and `D3BinaryOomProofF3G` over `cliRunPlainPanPlacedSig`,
`CliReachesOOMPlainPanPlaced`, and `CliReachesSampleNttStuckPlainPanPlaced`, reusing the unchanged
`MainOk*G` `main` specifications from `D3BinaryOomProofF3G` so zero upstream `.olean`s are
invalidated.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomPlainF3

open Arm64 (FsEntry GhostName MAX_LFS_FILESIZE Memory hasDotDot hasLeadingSlash normalizePath
  subroutine_ok)
open Arm64.Obj (MultiPlacement)
open Arm64.Process (ElfImage ProcessInputs initFsState)
open CryptoGames.LibsignalSession (GhostState)
open CryptoGames.LibsignalSessionApi (PreKeySignalMessage)
open CryptoVerification (libsignalSessionLib)
open CryptoVerification.E2E
  (PEParams PreKeyBundleFields PreKeyMessageFields RecordExtras UnreachedPqxdhPrimitives
   initiateTapeLen wirePrekey)
open CryptoVerification.LibsignalSpqrV1 (sha256Compress)
open CryptoVerification.SignalSession
  (CliHooks Inputs Outcome OutcomeMatchesModelExceptPath OutcomeOrExcusedAbort PqParty
   PqSessionMatches PqxdhPartyInSpecDomain bundleDir cliExternsPlaced cliProcessInputs coinsFile
   dirsFold encodeDir fileCapBytes filesFold filesOf files_eq_entries fsView initFsState_entries
   observe partyAddress pqInitModel pqInputs pqRecvInputs pqRecvPrekeyModel pqxdhExpectedOutcome
   publicBundleOf sessionFile stdinCapBytes stdioPaths)
open CryptoVerification.SignalSession.Cli
  (CliInputsOk CoinsReadable CommitOk InputsLoadable IsSendOverCap IsStdinOverCap MainResult
   RunAnswer cliInputs)
open CryptoVerification.SignalSession.Cli.RunCompose (RunSem runAns runRel)
open CryptoVerification.SignalSession.Cli.RunProofs (SessMatchesPm pkToE?)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.Placed.CliPlainPanPlaced
  (CliReachesOOMPlainPanPlaced CliReachesSampleNttStuckPlainPanPlaced CliRunsToPlainPanPlaced
   cliRunPlainPanPlacedSig)
open LibsignalBinary.Proofs.SignalSession.Cli.D3
  (D3NoMatchSessionFile d3PqRecvMatchingModel d3PqSessionOf)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomProofF3G
  (MainInitRunSemOkF3G MainOkOverD3F3G MainOkParseNoneD3F3G MainOkPathBD3F3G MainOkUntypedD3F3G
   MainOkValidMatchD3F3G V2F3StuckDomain mainOkCliF3OverG_of_mainOkOverD3F3G
   mainOkParseNoneD3F3G_of_untypedG)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomSpecF3
  (BundleFilesFlatRaw pqInitInputsFRaw)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MatchingPathBF3
  (cliRunSemPathB runRel_pqRecv_matchingPathB)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3NonCanonF3
  (cliInputsOk_pqRecvInputs coinsReadable_pqRecvInputs inputsLoadable_pqRecvInputs
   isStdinOverCap_pqRecvInputs not_isSendOverCap_pqRecvInputs not_isStdinOverCap_of_stdin_le)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3 (defaultExtrasF3)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3UntypedElfF3 (runRel_pqRecv_untypedReject)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
  (b2MainSpecTightNeedLocksFineAt cliBudgetLimits)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2G (F3SampleNttEntryGuard)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2GWithF
  (MainOkCliF3PqB2NeedLocksPlacedAtGWithF)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3ExternNoAllocFail
  (externPreservesNoAllocFailed_cliExternsPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
  (cliProgExtPlacedAt cliStaticsPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.PlacedOomRecovery2 (outcomeOrExcusedAbort_of_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.PlainPlacedComposer
  (CliElfF3PlainB2NeedLocksAssumptionsG CliPqxdhElfCorrectPlainPanPlacedWith
   cliPqxdhElfCorrectPlainPanPlacedWith_of_f3B2NeedLocksG'
   cliRunPlainPanPlacedSig_of_strict_f3_sampleNtt_call_obs
   cliRunPlainPanPlacedSig_of_strict_f3_sampleNtt_call_pred
   cliRunPlainPanPlacedSig_of_strict_f3_sampleNtt_stdinOverCap)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG (withEntryGuard)
open LibsignalBinary.Proofs.SignalSession.Cli.Parity
  (BundleReadWithinCap FilesExtVisibleRaw FilesVisibleRaw InputsEquivRaw LoadableFile
   fileStep_entries filesFold_entries_eq_or filesFold_eq_foldl_fileStep
   loadState_eq_of_inputsEquiv_of_visible_of_loadable loadState_error_of_not_loadable_files
   parseBundleDir)
open LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.BundleInitElfF3
  (CliInitD3Inputs InitRunSemOk cliInputsOk_of_inputsEquivRaw cliInputsOk_pqInitInputsFRaw
   observe_accept_pqInitInputsFRaw_eq observe_overCap_pqInitInputsFRaw_eq
   observe_reject_pqInitInputsFRaw_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.ElfInputsExtF3 (ExcLoadOk)

/-! ## 1. Plain-Memory Whole-Process ELF Interface Bundle (`CliPqBinaryV2OomF3PlainPanPlaced`) -/

/-- Complete two-placement `(mpl, mmpl)` plain-memory whole-process `OutcomeOrExcusedAbort`
bundle across baseline PQXDH, `recvOverStdinCap`, `canonicalNoMatch`, extended pre-key `recv`, and
flat-bundle `init` clauses. -/
structure CliPqBinaryV2OomF3PlainPanPlaced (mpl mmpl : MultiPlacement) (elf : ElfImage) : Prop where
  base : CliPqxdhElfCorrectPlainPanPlacedWith sha256Compress mpl mmpl elf
  recvOverStdinCap :
    ∀ (W : CliHooks), W.C.F = sha256Compress →
      W.C.E = CryptoGames.AES256.aes256Enc →
      W.C.D = CryptoGames.AES256.aes256Dec →
      W.C.X = CryptoGames.RFC7748.x25519Ref →
      W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
      W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
      W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
      W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
      W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
      ∀ (st : PqParty), PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st →
        ∀ (body : List (BitVec 8)) (rc : BitVec 256),
          (wirePrekey :: body).length > stdinCapBytes →
          let inp := pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc
          OutcomeOrExcusedAbort
            (fun k => CliReachesOOMPlainPanPlaced mpl mmpl elf W k ∨
              CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W k)
            (cliRunPlainPanPlacedSig mpl mmpl elf W) inp
            (· = .exited 2 [] (filesOf inp.files))
  canonicalNoMatch :
    ∀ (W : CliHooks), W.C.F = sha256Compress →
      W.C.E = CryptoGames.AES256.aes256Enc →
      W.C.D = CryptoGames.AES256.aes256Dec →
      W.C.X = CryptoGames.RFC7748.x25519Ref →
      W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
      W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
      W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
      W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
      W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
      ∀ (X : UnreachedPqxdhPrimitives) (st : PqParty),
        PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st →
        ∀ (x : RecordExtras) (g : GhostState (List (BitVec 8))), st.session = some (x, g) →
        ∀ (m : PreKeyMessageFields) (rc : BitVec 256),
          m.inner.length + 2048 < 2 ^ 32 → ¬ PqSessionMatches x g m →
          let WP : PEParams := ⟨W.C, W.Q⟩
          let inp := pqRecvInputs WP st (wirePrekey :: m.bytes) rc
          OutcomeOrExcusedAbort
            (fun k => CliReachesOOMPlainPanPlaced mpl mmpl elf W k ∨
              CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W k)
            (cliRunPlainPanPlacedSig mpl mmpl elf W) inp
            (fun o => if (wirePrekey :: m.bytes).length > stdinCapBytes then
                o = .exited 2 [] (filesOf inp.files)
              else
                OutcomeMatchesModelExceptPath WP inp (sessionFile (partyAddress st.party.other))
                  (pqRecvPrekeyModel X WP { st with session := none } m rc) o ∧
                D3NoMatchSessionFile X WP st x g m rc o)
  pksmParseNone :
    ∀ (W : CliHooks), W.C.F = sha256Compress →
      W.C.E = CryptoGames.AES256.aes256Enc →
      W.C.D = CryptoGames.AES256.aes256Dec →
      W.C.X = CryptoGames.RFC7748.x25519Ref →
      W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
      W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
      W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
      W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
      W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
      ∀ (st : PqParty), PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st →
        ∀ (body : List (BitVec 8)) (rc : BitVec 256),
          body.length < 2 ^ 32 → pksmParse body = none →
          let inp := pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc
          OutcomeOrExcusedAbort
            (fun k => CliReachesOOMPlainPanPlaced mpl mmpl elf W k ∨
              CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W k)
            (cliRunPlainPanPlacedSig mpl mmpl elf W) inp
            (· = if (wirePrekey :: body).length > stdinCapBytes then
              .exited 2 [] (filesOf inp.files)
            else
              .exited 1 [] (filesOf inp.files))
  untypedReject :
    ∀ (W : CliHooks), W.C.F = sha256Compress →
      W.C.E = CryptoGames.AES256.aes256Enc →
      W.C.D = CryptoGames.AES256.aes256Dec →
      W.C.X = CryptoGames.RFC7748.x25519Ref →
      W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
      W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
      W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
      W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
      W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
      ∀ (st : PqParty), PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st →
        ∀ (body : List (BitVec 8)) (pm : PreKeySignalMessage) (rc : BitVec 256),
          body.length < 2 ^ 32 → pksmParse body = some pm → pkToE? pm = none →
          (∀ x g, st.session = some (x, g) → ¬ SessMatchesPm (d3PqSessionOf x g) pm) →
          let inp := pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc
          OutcomeOrExcusedAbort
            (fun k => CliReachesOOMPlainPanPlaced mpl mmpl elf W k ∨
              CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W k)
            (cliRunPlainPanPlacedSig mpl mmpl elf W) inp
            (· = if (wirePrekey :: body).length > stdinCapBytes then
              .exited 2 [] (filesOf inp.files)
            else
              .exited 1 [] (filesOf inp.files))
  matchingPathB :
    ∀ (W : CliHooks), W.C.F = sha256Compress →
      W.C.E = CryptoGames.AES256.aes256Enc →
      W.C.D = CryptoGames.AES256.aes256Dec →
      W.C.X = CryptoGames.RFC7748.x25519Ref →
      W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
      W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
      W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
      W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
      W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
      ∀ (st : PqParty) (x : RecordExtras)
        (g : GhostState (List (BitVec 8))) (body : List (BitVec 8))
        (pm : PreKeySignalMessage) (rc : BitVec 256),
        PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st → st.session = some (x, g) →
        (wirePrekey :: body).length ≤ 2 ^ 32 →
        pksmParse body = some pm → SessMatchesPm (d3PqSessionOf x g) pm →
        let WP : PEParams := ⟨W.C, W.Q⟩
        let inp := pqRecvInputs WP st (wirePrekey :: body) rc
        OutcomeOrExcusedAbort
          (fun k => CliReachesOOMPlainPanPlaced mpl mmpl elf W k ∨
            CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W k)
          (cliRunPlainPanPlacedSig mpl mmpl elf W) inp
          (· = if (wirePrekey :: body).length > stdinCapBytes then
            .exited 2 [] (filesOf inp.files)
          else
            pqxdhExpectedOutcome WP inp (d3PqRecvMatchingModel WP st x g pm rc))
  validMatch :
    ∀ (W : CliHooks), W.C.F = sha256Compress →
      W.C.E = CryptoGames.AES256.aes256Enc →
      W.C.D = CryptoGames.AES256.aes256Dec →
      W.C.X = CryptoGames.RFC7748.x25519Ref →
      W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
      W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
      W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
      W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
      W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
      ∀ (X : UnreachedPqxdhPrimitives) (st : PqParty),
        PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st →
        ∀ (body : List (BitVec 8)) (pm : PreKeySignalMessage) (m : PreKeyMessageFields)
          (rc : BitVec 256),
          body.length < 2 ^ 32 → pksmParse body = some pm → pkToE? pm = some m →
          m.inner.length + 2048 < 2 ^ 32 →
          (∀ x g, st.session = some (x, g) → PqSessionMatches x g m) →
          let inp := pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc
          OutcomeOrExcusedAbort
            (fun k => CliReachesOOMPlainPanPlaced mpl mmpl elf W k ∨
              CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W k)
            (cliRunPlainPanPlacedSig mpl mmpl elf W) inp
            (· = if (wirePrekey :: body).length > stdinCapBytes then
              .exited 2 [] (filesOf inp.files)
            else
              pqxdhExpectedOutcome ⟨W.C, W.Q⟩ inp (pqRecvPrekeyModel X ⟨W.C, W.Q⟩ st m rc))
  validOver :
    ∀ (W : CliHooks), W.C.F = sha256Compress →
      W.C.E = CryptoGames.AES256.aes256Enc →
      W.C.D = CryptoGames.AES256.aes256Dec →
      W.C.X = CryptoGames.RFC7748.x25519Ref →
      W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
      W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
      W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
      W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
      W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
      ∀ (X : UnreachedPqxdhPrimitives) (st : PqParty),
        PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st →
        ∀ (x : RecordExtras) (g : GhostState (List (BitVec 8))), st.session = some (x, g) →
        ∀ (body : List (BitVec 8)) (pm : PreKeySignalMessage) (m : PreKeyMessageFields)
          (rc : BitVec 256),
          body.length < 2 ^ 32 → pksmParse body = some pm → pkToE? pm = some m →
          m.inner.length + 2048 < 2 ^ 32 → ¬ PqSessionMatches x g m →
          let WP : PEParams := ⟨W.C, W.Q⟩
          let inp := pqRecvInputs WP st (wirePrekey :: body) rc
          OutcomeOrExcusedAbort
            (fun k => CliReachesOOMPlainPanPlaced mpl mmpl elf W k ∨
              CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W k)
            (cliRunPlainPanPlacedSig mpl mmpl elf W) inp
            (fun o => if (wirePrekey :: body).length > stdinCapBytes then
                o = .exited 2 [] (filesOf inp.files)
              else
                OutcomeMatchesModelExceptPath WP inp (sessionFile (partyAddress st.party.other))
                  (pqRecvPrekeyModel X WP { st with session := none } m rc) o ∧
                D3NoMatchSessionFile X WP st x g m rc o)
  initFiles :
    ∀ (W : CliHooks), W.C.F = sha256Compress →
      W.C.E = CryptoGames.AES256.aes256Enc →
      W.C.D = CryptoGames.AES256.aes256Dec →
      W.C.X = CryptoGames.RFC7748.x25519Ref →
      W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
      W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
      W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
      W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
      W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
      ∀ (X : UnreachedPqxdhPrimitives) (st : PqParty)
        (files : List (String × List (BitVec 8))) (b : PreKeyBundleFields)
        (t : List.Vector (BitVec 8) initiateTapeLen) (i : Inputs),
        InputsEquivRaw i (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t) →
        PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st → st.session = none →
        BundleFilesFlatRaw files →
        BundleReadWithinCap (filesOf files) bundleDir →
        parseBundleDir (filesOf files) bundleDir = some (publicBundleOf b) →
        cliRunPlainPanPlacedSig mpl mmpl elf W i = none ∨
          OutcomeOrExcusedAbort
            (fun k => CliReachesOOMPlainPanPlaced mpl mmpl elf W k ∨
              CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W k)
            (cliRunPlainPanPlacedSig mpl mmpl elf W) i
            (· = pqxdhExpectedOutcome ⟨W.C, W.Q⟩ (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t)
              (pqInitModel X ⟨W.C, W.Q⟩ st b t))
  initReject :
    ∀ (W : CliHooks), W.C.F = sha256Compress →
      W.C.E = CryptoGames.AES256.aes256Enc →
      W.C.D = CryptoGames.AES256.aes256Dec →
      W.C.X = CryptoGames.RFC7748.x25519Ref →
      W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
      W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
      W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
      W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
      W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
      ∀ (st : PqParty) (files : List (String × List (BitVec 8)))
        (t : List.Vector (BitVec 8) initiateTapeLen) (i : Inputs),
        InputsEquivRaw i (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t) →
        PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st → st.session = none →
        BundleFilesFlatRaw files →
        parseBundleDir (filesOf files) bundleDir = none →
        cliRunPlainPanPlacedSig mpl mmpl elf W i = none ∨
          OutcomeOrExcusedAbort
            (fun k => CliReachesOOMPlainPanPlaced mpl mmpl elf W k ∨
              CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W k)
            (cliRunPlainPanPlacedSig mpl mmpl elf W) i
            (· = .exited 1 [] (filesOf (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t).files))
  initOverFileCap :
    ∀ (W : CliHooks), W.C.F = sha256Compress →
      W.C.E = CryptoGames.AES256.aes256Enc →
      W.C.D = CryptoGames.AES256.aes256Dec →
      W.C.X = CryptoGames.RFC7748.x25519Ref →
      W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
      W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
      W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
      W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
      W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
      ∀ (st : PqParty) (files : List (String × List (BitVec 8)))
        (t : List.Vector (BitVec 8) initiateTapeLen) (i : Inputs),
        InputsEquivRaw i (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t) →
        PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st → st.session = none →
        BundleFilesFlatRaw files →
        ¬ BundleReadWithinCap (filesOf files) bundleDir →
        cliRunPlainPanPlacedSig mpl mmpl elf W i = none ∨
          OutcomeOrExcusedAbort
            (fun k => CliReachesOOMPlainPanPlaced mpl mmpl elf W k ∨
              CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W k)
            (cliRunPlainPanPlacedSig mpl mmpl elf W) i
            (· = .exited 1 [] (filesOf (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t).files))

@[expose] def LibsignalCliPqBinaryV2OomF3PlainPanPlacedAt (mpl mmpl : MultiPlacement)
    (bytes : List (BitVec 8)) : Prop :=
  ∃ elf, ElfImage.parse bytes = .ok elf ∧ CliPqBinaryV2OomF3PlainPanPlaced mpl mmpl elf

@[expose] def LibsignalCliPqBinaryV2OomF3PlainPanPlaced (bytes : List (BitVec 8)) : Prop :=
  ∀ mpl mmpl : MultiPlacement,
    libsignalSessionLib.LinkedAt bytes mpl →
    VerifiedLibraries.mallocngLib.LinkedAt bytes mmpl →
    LibsignalCliPqBinaryV2OomF3PlainPanPlacedAt mpl mmpl bytes

/-! ## 2. Plain-Memory Input Extensionality (`InputsEquivRaw`) -/

theorem cliRunPlainPanPlacedSig_eq_none_of_loadState_error {mpl mmpl : MultiPlacement}
    {elf : ElfImage} {W : CliHooks} {i : Inputs} {msg : String}
    (herr : elf.loadState (cliProcessInputs i) = .error msg) :
    cliRunPlainPanPlacedSig mpl mmpl elf W i = none := by
  unfold cliRunPlainPanPlacedSig
  split
  · rename_i hex
    rcases hex with ⟨_, s0, hload, _⟩
    rw [herr] at hload
    cases hload
  · rfl

theorem cliRunPlainPanPlacedSig_eq_none_of_not_inputsLoadable {mpl mmpl : MultiPlacement}
    (elf : ElfImage) (W : CliHooks) {i : Inputs}
    (hnot : ¬ InputsLoadable i) : cliRunPlainPanPlacedSig mpl mmpl elf W i = none := by
  have herr : ∃ msg, elf.loadState (cliProcessInputs i) = .error msg := by
    unfold ElfImage.loadState
    by_cases hwf : (!elf.WellFormed) = true
    · simp [hwf, Bind.bind, Except.bind]
    · simp only [hwf, Bool.false_eq_true, ↓reduceIte, Bind.bind, pure, Except.pure, Except.bind]
      by_cases hd : ((cliProcessInputs i).dirs.any fun d => hasLeadingSlash d || hasDotDot d) = true
      · simp [hd]
      · simp only [hd, Bool.false_eq_true, ↓reduceIte]
        by_cases hf : ((cliProcessInputs i).files.any
            fun (p, bs) => hasLeadingSlash p || hasDotDot p ||
              !decide (bs.length ≤ MAX_LFS_FILESIZE)) = true
        · simp [hf]
        · exfalso
          apply hnot
          simp only [Bool.not_eq_true, List.any_eq_false, Bool.or_eq_false_iff,
            Bool.not_eq_false', decide_eq_true_eq] at hd hf
          exact ⟨fun d hm => hd d hm, fun f hm => ⟨⟨(hf f hm).1.1, (hf f hm).1.2⟩, (hf f hm).2⟩⟩
  obtain ⟨_, hmsg⟩ := herr
  exact cliRunPlainPanPlacedSig_eq_none_of_loadState_error hmsg

theorem filesExtVisible_cliRunPlainPanPlacedSig (mpl mmpl : MultiPlacement) (elf : ElfImage)
    (W : CliHooks) : FilesExtVisibleRaw (cliRunPlainPanPlacedSig mpl mmpl elf W) :=
  fun i i' heq hvis hvis' hload' => by
    by_cases hload : ∀ f ∈ i.files, LoadableFile f
    · right
      have hls := loadState_eq_of_inputsEquiv_of_visible_of_loadable elf heq hvis hvis' hload hload'
      unfold cliRunPlainPanPlacedSig CliRunsToPlainPanPlaced
      rw [hls]
    · obtain ⟨_, herr⟩ := loadState_error_of_not_loadable_files (elf := elf) hload
      exact Or.inl (cliRunPlainPanPlacedSig_eq_none_of_loadState_error herr)

theorem cliRunPlainPanPlacedSig_some_of_inputsEquiv {mpl mmpl : MultiPlacement} {elf : ElfImage}
    {W : CliHooks} {i i' : Inputs} {o : Outcome}
    (heq : InputsEquivRaw i i') (hvis : FilesVisibleRaw i.files) (hvis' : FilesVisibleRaw i'.files)
    (hload' : ∀ f ∈ i'.files, LoadableFile f)
    (hr : cliRunPlainPanPlacedSig mpl mmpl elf W i = some o) :
    cliRunPlainPanPlacedSig mpl mmpl elf W i' = some o := by
  rcases filesExtVisible_cliRunPlainPanPlacedSig mpl mmpl elf W i i' heq hvis hvis' hload' with
    hnone | hsame
  · rw [hr] at hnone
    cases hnone
  · exact hsame.symm.trans hr

instance instExcLoadOkOOMPlain (mpl mmpl : MultiPlacement) (elf : ElfImage) (W : CliHooks) :
    ExcLoadOk elf (CliReachesOOMPlainPanPlaced mpl mmpl elf W) where
  load_ok | ⟨s0, _, hok, _⟩ => ⟨s0, hok⟩

instance instExcLoadOkSampleNttStuckPlain (mpl mmpl : MultiPlacement) (elf : ElfImage)
    (W : CliHooks) :
    ExcLoadOk elf (CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W) where
  load_ok | ⟨s0, _, hok, _⟩ => ⟨s0, hok⟩

theorem exited_of_outcomeUpTo_raw_plain {mpl mmpl : MultiPlacement} {elf : ElfImage}
    {W : CliHooks} {exc : Inputs → Prop} [hExc : ExcLoadOk elf exc]
    {i i₀ : Inputs} {Pred : Outcome → Prop}
    {code : Nat} {out : List (BitVec 8)} {files : String → Option (List (BitVec 8))}
    (hr : cliRunPlainPanPlacedSig mpl mmpl elf W i = some (.exited code out files))
    (hup : OutcomeOrExcusedAbort exc (cliRunPlainPanPlacedSig mpl mmpl elf W) i₀ Pred)
    (heq : InputsEquivRaw i i₀) (hvis : FilesVisibleRaw i.files) (hvis₀ : FilesVisibleRaw i₀.files)
    (hload₀ : ∀ f ∈ i₀.files, hasLeadingSlash f.1 = false ∧ hasDotDot f.1 = false) :
    Pred (.exited code out files) := by
  have hnoErr₀ : ∀ msg, elf.loadState (cliProcessInputs i₀) ≠ .error msg := by
    intro msg herr
    rcases hup with ⟨_, ho₀, _⟩ | ⟨_, hexc⟩
    · have hn :=
        cliRunPlainPanPlacedSig_eq_none_of_loadState_error (mpl := mpl) (mmpl := mmpl) (W := W) herr
      rw [ho₀] at hn
      cases hn
    · obtain ⟨_, hok⟩ := hExc.load_ok hexc
      rw [herr] at hok
      cases hok
  have hloadFile₀ : ∀ f ∈ i₀.files, LoadableFile f := fun f hf =>
    ⟨hload₀ f hf, Classical.byContradiction fun hlen => by
      obtain ⟨msg, herr⟩ := loadState_error_of_not_loadable_files (elf := elf) (i := i₀)
        (fun hall => hlen (hall f hf).2)
      exact hnoErr₀ msg herr⟩
  have hr₀ := cliRunPlainPanPlacedSig_some_of_inputsEquiv heq hvis hvis₀ hloadFile₀ hr
  rcases hup with ⟨o₀, ho₀, hP⟩ | ⟨hab, _⟩
  · rw [hr₀] at ho₀
    injection ho₀ with ho'
    exact ho' ▸ hP
  · rw [hr₀] at hab
    cases hab

theorem exited_of_or_none_outcomeUpTo_eq_raw_plain {mpl mmpl : MultiPlacement}
    {elf : ElfImage} {W : CliHooks}
    {exc : Inputs → Prop} {i : Inputs} {expected : Outcome}
    {code : Nat} {out : List (BitVec 8)} {files : String → Option (List (BitVec 8))}
    (hr : cliRunPlainPanPlacedSig mpl mmpl elf W i = some (.exited code out files))
    (hor : cliRunPlainPanPlacedSig mpl mmpl elf W i = none ∨
      OutcomeOrExcusedAbort exc (cliRunPlainPanPlacedSig mpl mmpl elf W) i (· = expected)) :
    Outcome.exited code out files = expected := by
  rcases hor with hnone | (⟨o₀, ho₀, hP⟩ | ⟨hab, _⟩)
  · rw [hr] at hnone
    cases hnone
  · rw [hr] at ho₀
    injection ho₀ with ho'
    exact ho'.trans hP
  · rw [hr] at hab
    cases hab

/-! ## 3. Guarded Plain-Memory Whole-Process `recv` & Flat-Bundle `init` Lifts -/

private theorem pqRecv_strict_obs_of_plain_f3G
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage} {W : CliHooks} {Run : Inputs → RunAnswer → Prop}
    (H : CliElfF3PlainB2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmainW : ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (mpl.base 617)
        (withEntryGuard (F3SampleNttEntryGuard mpl mmpl)
          (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart)
            cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl) Run cliProcessInputs)))
    {st : PqParty} {c : List (BitVec 8)} {rc : BitVec 256} {o : Outcome}
    (hst : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st)
    (hclause : c.length ≤ stdinCapBytes →
      ∃ a, Run (pqRecvInputs ⟨W.C, W.Q⟩ st c rc) a ∧
        observe (pqRecvInputs ⟨W.C, W.Q⟩ st c rc).files a = o ∧
        CommitOk (pqRecvInputs ⟨W.C, W.Q⟩ st c rc) (MainResult.ofAnswer a))
    (hNoStuck :
      ¬ CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W (pqRecvInputs ⟨W.C, W.Q⟩ st c rc)) :
    let inp := pqRecvInputs ⟨W.C, W.Q⟩ st c rc
    cliRunPlainPanPlacedSig mpl mmpl elf W inp =
      some (if c.length > stdinCapBytes then .exited 2 [] (filesOf inp.files) else o) := by
  dsimp only
  let WP : PEParams := ⟨W.C, W.Q⟩
  by_cases hstin : c.length > stdinCapBytes
  · simp only [hstin, ↓reduceIte]
    exact cliRunPlainPanPlacedSig_of_strict_f3_sampleNtt_stdinOverCap
      (externPreservesNoAllocFailed_cliExternsPlaced mmpl W) H hmainW
      (cliInputsOk_pqRecvInputs WP st c rc) (inputsLoadable_pqRecvInputs WP st c rc hst)
      (isStdinOverCap_pqRecvInputs WP st c rc hstin) hNoStuck
  · simp only [hstin, ↓reduceIte]
    obtain ⟨a, hrun, hobs, hcommit⟩ := hclause (Nat.le_of_not_gt hstin)
    exact cliRunPlainPanPlacedSig_of_strict_f3_sampleNtt_call_obs
      (externPreservesNoAllocFailed_cliExternsPlaced mmpl W) H hmainW
      (cliInputsOk_pqRecvInputs WP st c rc) (inputsLoadable_pqRecvInputs WP st c rc hst)
      hrun (not_isSendOverCap_pqRecvInputs WP st c rc)
      (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin))
      hobs (coinsReadable_pqRecvInputs WP st c rc) hcommit hNoStuck

private theorem d3_recvOverStdinCap_strict_of_plain_f3G
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop} {elf : ElfImage}
    (H : CliElfF3PlainB2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmain : MainOkCliF3PqB2NeedLocksPlacedAtGWithF sha256Compress mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (W : CliHooks)
    (hF : W.C.F = sha256Compress)
    (hE : W.C.E = CryptoGames.AES256.aes256Enc)
    (hD : W.C.D = CryptoGames.AES256.aes256Dec)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (hF512 : W.Q.F512 = CryptoGames.SHA512.sha512CompressState)
    (hEnc : W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec)
    (hDec : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    (st : PqParty) (hst : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st)
    (body : List (BitVec 8)) (rc : BitVec 256)
    (hover : (wirePrekey :: body).length > stdinCapBytes)
    (hNoStuck :
      ¬ CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W
          (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc)) :
    let inp := pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc
    cliRunPlainPanPlacedSig mpl mmpl elf W inp = some (.exited 2 [] (filesOf inp.files)) := by
  obtain ⟨Run, hmainW, _⟩ := hmain H.base547NeZero defaultExtrasF3 W hF hE hD hX hPub hF512 hEnc hDec hK
  have h := pqRecv_strict_obs_of_plain_f3G (rc := rc) (o := .exited 2 []
      (filesOf (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc).files)) H hmainW hst
    (fun hle => False.elim (Nat.not_lt_of_ge hle hover)) hNoStuck
  dsimp only at h ⊢; simpa only [hover, ↓reduceIte] using h

theorem d3_recvOverStdinCap_of_plain_f3G
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop} {elf : ElfImage}
    (H : CliElfF3PlainB2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmain : MainOkCliF3PqB2NeedLocksPlacedAtGWithF sha256Compress mpl mmpl CodeOk libcAddr elf.brkStart stk)
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
      ∀ (i : Inputs), V2F3StuckDomain ⟨W.C, W.Q⟩ i →
        CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W i →
        cliRunPlainPanPlacedSig mpl mmpl elf W i = none) :
    ∀ (W : CliHooks),
      W.C.F = sha256Compress →
      W.C.E = CryptoGames.AES256.aes256Enc →
      W.C.D = CryptoGames.AES256.aes256Dec →
      W.C.X = CryptoGames.RFC7748.x25519Ref →
      W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
      W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
      W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
      W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
      W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
      ∀ (st : PqParty), PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st →
        ∀ (body : List (BitVec 8)) (rc : BitVec 256),
          (wirePrekey :: body).length > stdinCapBytes →
          let inp := pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc
          OutcomeOrExcusedAbort
            (fun k => CliReachesOOMPlainPanPlaced mpl mmpl elf W k ∨
              CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W k)
            (cliRunPlainPanPlacedSig mpl mmpl elf W) inp (· = .exited 2 [] (filesOf inp.files)) := by
  intro W hF hE hD hX hPub hF512 hEnc hDec hK st hst body rc hover
  dsimp only
  let inp := pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc
  by_cases hStuck : CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W inp
  · exact Or.inr ⟨hStuckDiv W hF hE hD hX hPub hF512 hEnc hDec hK inp
      (Or.inr (Or.inl ⟨st, body, rc, hst, rfl⟩)) hStuck, Or.inr hStuck⟩
  · exact outcomeOrExcusedAbort_of_eq
      (d3_recvOverStdinCap_strict_of_plain_f3G H hmain W hF hE hD hX hPub hF512 hEnc hDec hK st hst
        body rc hover hStuck)

theorem d3_pksmParseNone_strict_of_plain_f3G
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop} {elf : ElfImage}
    (H : CliElfF3PlainB2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hparseNone : MainOkParseNoneD3F3G mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (W : CliHooks)
    (hF : W.C.F = sha256Compress)
    (hE : W.C.E = CryptoGames.AES256.aes256Enc)
    (hD : W.C.D = CryptoGames.AES256.aes256Dec)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (hF512 : W.Q.F512 = CryptoGames.SHA512.sha512CompressState)
    (hEnc : W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec)
    (hDec : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    (st : PqParty) (hst : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st)
    (body : List (BitVec 8)) (rc : BitVec 256)
    (hbody : body.length < 2 ^ 32) (hnone : pksmParse body = none)
    (hNoStuck :
      ¬ CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W
          (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc)) :
    let inp := pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc
    cliRunPlainPanPlacedSig mpl mmpl elf W inp =
      some (if (wirePrekey :: body).length > stdinCapBytes then .exited 2 [] (filesOf inp.files)
        else .exited 1 [] (filesOf inp.files)) := by
  obtain ⟨Run, hmainW, hcl⟩ := hparseNone H.base547NeZero W hF hE hD hX hPub hF512 hEnc hDec hK
  exact pqRecv_strict_obs_of_plain_f3G H hmainW hst
    (fun _ => hcl st hst body rc hbody hnone) hNoStuck

theorem d3_pksmParseNone_of_plain_f3G
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop} {elf : ElfImage}
    (H : CliElfF3PlainB2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hparseNone : MainOkParseNoneD3F3G mpl mmpl CodeOk libcAddr elf.brkStart stk)
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
      ∀ (i : Inputs), V2F3StuckDomain ⟨W.C, W.Q⟩ i →
        CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W i →
        cliRunPlainPanPlacedSig mpl mmpl elf W i = none) :
    ∀ (W : CliHooks),
      W.C.F = sha256Compress →
      W.C.E = CryptoGames.AES256.aes256Enc →
      W.C.D = CryptoGames.AES256.aes256Dec →
      W.C.X = CryptoGames.RFC7748.x25519Ref →
      W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
      W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
      W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
      W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
      W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
      ∀ (st : PqParty), PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st →
        ∀ (body : List (BitVec 8)) (rc : BitVec 256),
          body.length < 2 ^ 32 → pksmParse body = none →
          let inp := pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc
          OutcomeOrExcusedAbort
            (fun k => CliReachesOOMPlainPanPlaced mpl mmpl elf W k ∨
              CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W k)
            (cliRunPlainPanPlacedSig mpl mmpl elf W) inp
            (· = if (wirePrekey :: body).length > stdinCapBytes then .exited 2 [] (filesOf inp.files)
              else .exited 1 [] (filesOf inp.files)) := by
  intro W hF hE hD hX hPub hF512 hEnc hDec hK st hst body rc hbody hnone
  dsimp only
  let inp := pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc
  by_cases hStuck : CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W inp
  · exact Or.inr ⟨hStuckDiv W hF hE hD hX hPub hF512 hEnc hDec hK inp
      (Or.inr (Or.inl ⟨st, body, rc, hst, rfl⟩)) hStuck, Or.inr hStuck⟩
  · exact outcomeOrExcusedAbort_of_eq
      (d3_pksmParseNone_strict_of_plain_f3G H hparseNone W hF hE hD hX hPub hF512 hEnc hDec hK st
        hst body rc hbody hnone hStuck)

theorem d3_untypedReject_strict_of_plain_f3G
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop} {elf : ElfImage}
    (H : CliElfF3PlainB2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (huntyped : MainOkUntypedD3F3G mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (W : CliHooks)
    (hF : W.C.F = sha256Compress)
    (hE : W.C.E = CryptoGames.AES256.aes256Enc)
    (hD : W.C.D = CryptoGames.AES256.aes256Dec)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (hF512 : W.Q.F512 = CryptoGames.SHA512.sha512CompressState)
    (hEnc : W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec)
    (hDec : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    (st : PqParty) (hst : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st)
    (body : List (BitVec 8)) (pm : PreKeySignalMessage) (rc : BitVec 256)
    (hbody : body.length < 2 ^ 32)
    (hparse : pksmParse body = some pm)
    (hpk : pkToE? pm = none)
    (hnomatch : ∀ x g, st.session = some (x, g) → ¬ SessMatchesPm (d3PqSessionOf x g) pm)
    (hNoStuck :
      ¬ CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W
          (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc)) :
    let inp := pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc
    cliRunPlainPanPlacedSig mpl mmpl elf W inp =
      some (if (wirePrekey :: body).length > stdinCapBytes then .exited 2 [] (filesOf inp.files)
        else .exited 1 [] (filesOf inp.files)) :=
  pqRecv_strict_obs_of_plain_f3G H
    (huntyped H.base547NeZero W hF hE hD hX hPub hF512 hEnc hDec hK) hst (fun _ => by
      obtain ⟨hrun, hobs, hcommit⟩ :=
        runRel_pqRecv_untypedReject W st body pm rc hst hbody hparse hpk hnomatch
      exact ⟨some none, ⟨Or.inr ⟨st, wirePrekey :: body, rc, hst, rfl⟩, hrun⟩, hobs, hcommit⟩)
    hNoStuck

theorem d3_untypedReject_of_plain_f3G
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop} {elf : ElfImage}
    (H : CliElfF3PlainB2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (huntyped : MainOkUntypedD3F3G mpl mmpl CodeOk libcAddr elf.brkStart stk)
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
      ∀ (i : Inputs), V2F3StuckDomain ⟨W.C, W.Q⟩ i →
        CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W i →
        cliRunPlainPanPlacedSig mpl mmpl elf W i = none) :
    ∀ (W : CliHooks),
      W.C.F = sha256Compress →
      W.C.E = CryptoGames.AES256.aes256Enc →
      W.C.D = CryptoGames.AES256.aes256Dec →
      W.C.X = CryptoGames.RFC7748.x25519Ref →
      W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
      W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
      W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
      W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
      W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
      ∀ (st : PqParty), PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st →
        ∀ (body : List (BitVec 8)) (pm : PreKeySignalMessage) (rc : BitVec 256),
          body.length < 2 ^ 32 → pksmParse body = some pm → pkToE? pm = none →
          (∀ x g, st.session = some (x, g) → ¬ SessMatchesPm (d3PqSessionOf x g) pm) →
          let inp := pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc
          OutcomeOrExcusedAbort
            (fun k => CliReachesOOMPlainPanPlaced mpl mmpl elf W k ∨
              CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W k)
            (cliRunPlainPanPlacedSig mpl mmpl elf W) inp
            (· = if (wirePrekey :: body).length > stdinCapBytes then .exited 2 [] (filesOf inp.files)
              else .exited 1 [] (filesOf inp.files)) := by
  intro W hF hE hD hX hPub hF512 hEnc hDec hK st hst body pm rc hbody hparse hpk hnomatch
  dsimp only
  let inp := pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc
  by_cases hStuck : CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W inp
  · exact Or.inr ⟨hStuckDiv W hF hE hD hX hPub hF512 hEnc hDec hK inp
      (Or.inr (Or.inl ⟨st, body, rc, hst, rfl⟩)) hStuck, Or.inr hStuck⟩
  · exact outcomeOrExcusedAbort_of_eq
      (d3_untypedReject_strict_of_plain_f3G H huntyped W hF hE hD hX hPub hF512 hEnc hDec hK st hst
        body pm rc hbody hparse hpk hnomatch hStuck)

theorem d3_matchingPathB_strict_of_plain_f3G
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop} {elf : ElfImage}
    (H : CliElfF3PlainB2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hpathB : MainOkPathBD3F3G mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (W : CliHooks)
    (hF : W.C.F = sha256Compress)
    (hE : W.C.E = CryptoGames.AES256.aes256Enc)
    (hD : W.C.D = CryptoGames.AES256.aes256Dec)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (hF512 : W.Q.F512 = CryptoGames.SHA512.sha512CompressState)
    (hEnc : W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec)
    (hDec : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    (st : PqParty) (x : RecordExtras) (g : GhostState (List (BitVec 8)))
    (body : List (BitVec 8)) (pm : PreKeySignalMessage) (rc : BitVec 256)
    (hwf : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st) (hsess : st.session = some (x, g))
    (hlen : (wirePrekey :: body).length ≤ 2 ^ 32)
    (hparse : pksmParse body = some pm)
    (hmatch : SessMatchesPm (d3PqSessionOf x g) pm)
    (hNoStuck :
      ¬ CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W
          (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc)) :
    let WP : PEParams := ⟨W.C, W.Q⟩
    let inp := pqRecvInputs WP st (wirePrekey :: body) rc
    cliRunPlainPanPlacedSig mpl mmpl elf W inp =
      some (if (wirePrekey :: body).length > stdinCapBytes then .exited 2 [] (filesOf inp.files)
        else pqxdhExpectedOutcome WP inp (d3PqRecvMatchingModel WP st x g pm rc)) :=
  pqRecv_strict_obs_of_plain_f3G H
    (hpathB H.base547NeZero defaultExtrasF3 W hF hE hD hX hPub hF512 hEnc hDec hK) hwf (fun _ => by
      obtain ⟨hrun, hobs, hcommit⟩ :=
        runRel_pqRecv_matchingPathB defaultExtrasF3 W st x g body pm rc hwf hsess hlen hparse hmatch
      exact ⟨runAns (cliRunSemPathB defaultExtrasF3 W)
          (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc),
        ⟨Or.inr ⟨st, wirePrekey :: body, rc, hwf, rfl⟩, hrun⟩, hobs, hcommit⟩) hNoStuck

theorem d3_matchingPathB_of_plain_f3G
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop} {elf : ElfImage}
    (H : CliElfF3PlainB2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hpathB : MainOkPathBD3F3G mpl mmpl CodeOk libcAddr elf.brkStart stk)
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
      ∀ (i : Inputs), V2F3StuckDomain ⟨W.C, W.Q⟩ i →
        CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W i →
        cliRunPlainPanPlacedSig mpl mmpl elf W i = none) :
    ∀ (W : CliHooks),
      W.C.F = sha256Compress →
      W.C.E = CryptoGames.AES256.aes256Enc →
      W.C.D = CryptoGames.AES256.aes256Dec →
      W.C.X = CryptoGames.RFC7748.x25519Ref →
      W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
      W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
      W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
      W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
      W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
      ∀ (st : PqParty) (x : RecordExtras)
        (g : GhostState (List (BitVec 8))) (body : List (BitVec 8))
        (pm : PreKeySignalMessage) (rc : BitVec 256),
        PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st → st.session = some (x, g) →
        (wirePrekey :: body).length ≤ 2 ^ 32 →
        pksmParse body = some pm → SessMatchesPm (d3PqSessionOf x g) pm →
        let WP : PEParams := ⟨W.C, W.Q⟩
        let inp := pqRecvInputs WP st (wirePrekey :: body) rc
        OutcomeOrExcusedAbort
          (fun k => CliReachesOOMPlainPanPlaced mpl mmpl elf W k ∨
            CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W k)
          (cliRunPlainPanPlacedSig mpl mmpl elf W) inp
          (· = if (wirePrekey :: body).length > stdinCapBytes then .exited 2 [] (filesOf inp.files)
            else pqxdhExpectedOutcome WP inp (d3PqRecvMatchingModel WP st x g pm rc)) := by
  intro W hF hE hD hX hPub hF512 hEnc hDec hK st x g body pm rc hwf hsess hlen hparse hmatch
  dsimp only
  let WP : PEParams := ⟨W.C, W.Q⟩
  let inp := pqRecvInputs WP st (wirePrekey :: body) rc
  by_cases hStuck : CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W inp
  · exact Or.inr ⟨hStuckDiv W hF hE hD hX hPub hF512 hEnc hDec hK inp
      (Or.inr (Or.inl ⟨st, body, rc, hwf, rfl⟩)) hStuck, Or.inr hStuck⟩
  · exact outcomeOrExcusedAbort_of_eq
      (d3_matchingPathB_strict_of_plain_f3G H hpathB W hF hE hD hX hPub hF512 hEnc hDec hK st x g
        body pm rc hwf hsess hlen hparse hmatch hStuck)

theorem d3_valid_match_strict_of_plain_f3G
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3PlainB2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hvalidMatch : MainOkValidMatchD3F3G mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (W : CliHooks)
    (hF : W.C.F = sha256Compress)
    (hE : W.C.E = CryptoGames.AES256.aes256Enc)
    (hD : W.C.D = CryptoGames.AES256.aes256Dec)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (hF512 : W.Q.F512 = CryptoGames.SHA512.sha512CompressState)
    (hEnc : W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec)
    (hDec : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    (X : UnreachedPqxdhPrimitives) (st : PqParty)
    (hst : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st)
    (body : List (BitVec 8)) (pm : PreKeySignalMessage) (m : PreKeyMessageFields)
    (rc : BitVec 256)
    (hbody : body.length < 2 ^ 32)
    (hpm : pksmParse body = some pm)
    (hm : pkToE? pm = some m)
    (hinner : m.inner.length + 2048 < 2 ^ 32)
    (hmatch : ∀ x g, st.session = some (x, g) → PqSessionMatches x g m)
    (hNoStuck :
      ¬ CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W
          (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc)) :
    let inp := pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc
    cliRunPlainPanPlacedSig mpl mmpl elf W inp =
      some (if (wirePrekey :: body).length > stdinCapBytes then
        .exited 2 [] (filesOf inp.files)
      else
        pqxdhExpectedOutcome ⟨W.C, W.Q⟩ inp (pqRecvPrekeyModel X ⟨W.C, W.Q⟩ st m rc)) := by
  dsimp only
  let WP : PEParams := ⟨W.C, W.Q⟩
  obtain ⟨Run, hmainW, hcl⟩ := hvalidMatch H.base547NeZero X W hF hE hD hX hPub hF512 hEnc hDec hK
  by_cases hstin : (wirePrekey :: body).length > stdinCapBytes
  · simp only [hstin, ↓reduceIte]
    exact cliRunPlainPanPlacedSig_of_strict_f3_sampleNtt_stdinOverCap
      (externPreservesNoAllocFailed_cliExternsPlaced mmpl W) H hmainW
      (cliInputsOk_pqRecvInputs WP st (wirePrekey :: body) rc)
      (inputsLoadable_pqRecvInputs WP st (wirePrekey :: body) rc hst)
      (isStdinOverCap_pqRecvInputs WP st (wirePrekey :: body) rc hstin) hNoStuck
  · simp only [hstin, ↓reduceIte]
    obtain ⟨a, hrun, hobs, hcommit⟩ := hcl st hst body pm m rc hbody hpm hm hinner hmatch
    exact cliRunPlainPanPlacedSig_of_strict_f3_sampleNtt_call_obs
      (externPreservesNoAllocFailed_cliExternsPlaced mmpl W) H hmainW
      (cliInputsOk_pqRecvInputs WP st (wirePrekey :: body) rc)
      (inputsLoadable_pqRecvInputs WP st (wirePrekey :: body) rc hst)
      hrun (not_isSendOverCap_pqRecvInputs WP st (wirePrekey :: body) rc)
      (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin))
      hobs (coinsReadable_pqRecvInputs WP st (wirePrekey :: body) rc) hcommit hNoStuck

theorem d3_valid_match_outcomeUpTo_of_plain_f3G
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3PlainB2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hvalidMatch : MainOkValidMatchD3F3G mpl mmpl CodeOk libcAddr elf.brkStart stk)
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
      ∀ (i : Inputs), V2F3StuckDomain ⟨W.C, W.Q⟩ i →
        CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W i →
        cliRunPlainPanPlacedSig mpl mmpl elf W i = none) :
    ∀ (W : CliHooks),
      W.C.F = sha256Compress →
      W.C.E = CryptoGames.AES256.aes256Enc →
      W.C.D = CryptoGames.AES256.aes256Dec →
      W.C.X = CryptoGames.RFC7748.x25519Ref →
      W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
      W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
      W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
      W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
      W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
      ∀ (X : UnreachedPqxdhPrimitives) (st : PqParty),
        PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st →
        ∀ (body : List (BitVec 8)) (pm : PreKeySignalMessage) (m : PreKeyMessageFields)
          (rc : BitVec 256),
          body.length < 2 ^ 32 → pksmParse body = some pm → pkToE? pm = some m →
          m.inner.length + 2048 < 2 ^ 32 →
          (∀ x g, st.session = some (x, g) → PqSessionMatches x g m) →
          let inp := pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc
          OutcomeOrExcusedAbort
            (fun k => CliReachesOOMPlainPanPlaced mpl mmpl elf W k ∨
              CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W k)
            (cliRunPlainPanPlacedSig mpl mmpl elf W) inp
            (· = if (wirePrekey :: body).length > stdinCapBytes then
              .exited 2 [] (filesOf inp.files)
            else
              pqxdhExpectedOutcome ⟨W.C, W.Q⟩ inp (pqRecvPrekeyModel X ⟨W.C, W.Q⟩ st m rc)) := by
  intro W hF hE hD hX hPub hF512 hEnc hDec hK X st hst body pm m rc hbody hpm hm hinner hmatch
  dsimp only
  let inp := pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc
  by_cases hStuck : CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W inp
  · exact Or.inr ⟨hStuckDiv W hF hE hD hX hPub hF512 hEnc hDec hK inp
      (Or.inr (Or.inl ⟨st, body, rc, hst, rfl⟩)) hStuck, Or.inr hStuck⟩
  · exact outcomeOrExcusedAbort_of_eq
      (d3_valid_match_strict_of_plain_f3G H hvalidMatch W hF hE hD hX hPub hF512 hEnc hDec hK X st
        hst body pm m rc hbody hpm hm hinner hmatch hStuck)

theorem d3_valid_over_strict_of_plain_f3G
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3PlainB2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hoverD3 : MainOkOverD3F3G mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (W : CliHooks)
    (hF : W.C.F = sha256Compress)
    (hE : W.C.E = CryptoGames.AES256.aes256Enc)
    (hD : W.C.D = CryptoGames.AES256.aes256Dec)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (hF512 : W.Q.F512 = CryptoGames.SHA512.sha512CompressState)
    (hEnc : W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec)
    (hDec : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    (X : UnreachedPqxdhPrimitives) (st : PqParty)
    (hst : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st)
    (x : RecordExtras) (g : GhostState (List (BitVec 8))) (hsess : st.session = some (x, g))
    (body : List (BitVec 8)) (pm : PreKeySignalMessage) (m : PreKeyMessageFields)
    (rc : BitVec 256)
    (hbody : body.length < 2 ^ 32)
    (hpm : pksmParse body = some pm)
    (hm : pkToE? pm = some m)
    (hinner : m.inner.length + 2048 < 2 ^ 32)
    (hnomatch : ¬ PqSessionMatches x g m)
    (hNoStuck :
      ¬ CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W
          (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc)) :
    let WP : PEParams := ⟨W.C, W.Q⟩
    let inp := pqRecvInputs WP st (wirePrekey :: body) rc
    ∃ o : Outcome,
      cliRunPlainPanPlacedSig mpl mmpl elf W inp = some o ∧
      (if (wirePrekey :: body).length > stdinCapBytes then
        o = .exited 2 [] (filesOf inp.files)
      else
        OutcomeMatchesModelExceptPath WP inp (sessionFile (partyAddress st.party.other))
          (pqRecvPrekeyModel X WP { st with session := none } m rc) o ∧
        D3NoMatchSessionFile X WP st x g m rc o) := by
  dsimp only
  let WP : PEParams := ⟨W.C, W.Q⟩
  let inp := pqRecvInputs WP st (wirePrekey :: body) rc
  obtain ⟨Run, hmainW, hbodyCl, _⟩ := hoverD3 H.base547NeZero X W hF hE hD hX hPub hF512 hEnc hDec hK
  by_cases hstin : (wirePrekey :: body).length > stdinCapBytes
  · refine ⟨.exited 2 [] (filesOf inp.files), ?_, by simp only [hstin, ↓reduceIte]; rfl⟩
    exact cliRunPlainPanPlacedSig_of_strict_f3_sampleNtt_stdinOverCap
      (externPreservesNoAllocFailed_cliExternsPlaced mmpl W) H hmainW
      (cliInputsOk_pqRecvInputs WP st (wirePrekey :: body) rc)
      (inputsLoadable_pqRecvInputs WP st (wirePrekey :: body) rc hst)
      (isStdinOverCap_pqRecvInputs WP st (wirePrekey :: body) rc hstin) hNoStuck
  · obtain ⟨a, hrun, hp, hcommit⟩ :=
      hbodyCl st hst x g hsess body pm m rc hbody hpm hm hinner hnomatch
    obtain ⟨o, ho, hpo⟩ :=
      cliRunPlainPanPlacedSig_of_strict_f3_sampleNtt_call_pred
        (P := fun o =>
          OutcomeMatchesModelExceptPath WP inp (sessionFile (partyAddress st.party.other))
            (pqRecvPrekeyModel X WP { st with session := none } m rc) o ∧
          D3NoMatchSessionFile X WP st x g m rc o)
        (externPreservesNoAllocFailed_cliExternsPlaced mmpl W) H hmainW
        (cliInputsOk_pqRecvInputs WP st (wirePrekey :: body) rc)
        (inputsLoadable_pqRecvInputs WP st (wirePrekey :: body) rc hst)
        hrun (not_isSendOverCap_pqRecvInputs WP st (wirePrekey :: body) rc)
        (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin))
        hp (coinsReadable_pqRecvInputs WP st (wirePrekey :: body) rc) hcommit hNoStuck
    refine ⟨o, ho, ?_⟩
    simp only [hstin, ↓reduceIte]
    exact hpo

theorem d3_valid_over_outcomeUpTo_of_plain_f3G
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3PlainB2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hoverD3 : MainOkOverD3F3G mpl mmpl CodeOk libcAddr elf.brkStart stk)
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
      ∀ (i : Inputs), V2F3StuckDomain ⟨W.C, W.Q⟩ i →
        CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W i →
        cliRunPlainPanPlacedSig mpl mmpl elf W i = none) :
    ∀ (W : CliHooks),
      W.C.F = sha256Compress →
      W.C.E = CryptoGames.AES256.aes256Enc →
      W.C.D = CryptoGames.AES256.aes256Dec →
      W.C.X = CryptoGames.RFC7748.x25519Ref →
      W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
      W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
      W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
      W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
      W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
      ∀ (X : UnreachedPqxdhPrimitives) (st : PqParty),
        PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st →
        ∀ (x : RecordExtras) (g : GhostState (List (BitVec 8))), st.session = some (x, g) →
        ∀ (body : List (BitVec 8)) (pm : PreKeySignalMessage) (m : PreKeyMessageFields)
          (rc : BitVec 256),
          body.length < 2 ^ 32 → pksmParse body = some pm → pkToE? pm = some m →
          m.inner.length + 2048 < 2 ^ 32 → ¬ PqSessionMatches x g m →
          let WP : PEParams := ⟨W.C, W.Q⟩
          let inp := pqRecvInputs WP st (wirePrekey :: body) rc
          OutcomeOrExcusedAbort
            (fun k => CliReachesOOMPlainPanPlaced mpl mmpl elf W k ∨
              CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W k)
            (cliRunPlainPanPlacedSig mpl mmpl elf W) inp
            (fun o => if (wirePrekey :: body).length > stdinCapBytes then
                o = .exited 2 [] (filesOf inp.files)
              else
                OutcomeMatchesModelExceptPath WP inp (sessionFile (partyAddress st.party.other))
                  (pqRecvPrekeyModel X WP { st with session := none } m rc) o ∧
                D3NoMatchSessionFile X WP st x g m rc o) := by
  intro W hF hE hD hX hPub hF512 hEnc hDec hK X st hst x g hsess body pm m rc hbody hpm hm hinner hnomatch
  dsimp only
  let WP : PEParams := ⟨W.C, W.Q⟩
  let inp := pqRecvInputs WP st (wirePrekey :: body) rc
  by_cases hStuck : CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W inp
  · exact Or.inr ⟨hStuckDiv W hF hE hD hX hPub hF512 hEnc hDec hK inp
      (Or.inr (Or.inl ⟨st, body, rc, hst, rfl⟩)) hStuck, Or.inr hStuck⟩
  · exact Or.inl (d3_valid_over_strict_of_plain_f3G H hoverD3 W hF hE hD hX hPub hF512 hEnc hDec hK
      X st hst x g hsess body pm m rc hbody hpm hm hinner hnomatch hStuck)

private theorem d3_canonical_noMatch_strict_of_plain_f3G
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3PlainB2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hoverD3 : MainOkOverD3F3G mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (W : CliHooks)
    (hF : W.C.F = sha256Compress)
    (hE : W.C.E = CryptoGames.AES256.aes256Enc)
    (hD : W.C.D = CryptoGames.AES256.aes256Dec)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (hF512 : W.Q.F512 = CryptoGames.SHA512.sha512CompressState)
    (hEnc : W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec)
    (hDec : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    (X : UnreachedPqxdhPrimitives) (st : PqParty)
    (hst : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st)
    (x : RecordExtras) (g : GhostState (List (BitVec 8))) (hsess : st.session = some (x, g))
    (m : PreKeyMessageFields) (rc : BitVec 256)
    (hinner : m.inner.length + 2048 < 2 ^ 32)
    (hnomatch : ¬ PqSessionMatches x g m)
    (hNoStuck :
      ¬ CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W
          (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: m.bytes) rc)) :
    let WP : PEParams := ⟨W.C, W.Q⟩
    let inp := pqRecvInputs WP st (wirePrekey :: m.bytes) rc
    ∃ o : Outcome,
      cliRunPlainPanPlacedSig mpl mmpl elf W inp = some o ∧
      (if (wirePrekey :: m.bytes).length > stdinCapBytes then
        o = .exited 2 [] (filesOf inp.files)
      else
        OutcomeMatchesModelExceptPath WP inp (sessionFile (partyAddress st.party.other))
          (pqRecvPrekeyModel X WP { st with session := none } m rc) o ∧
        D3NoMatchSessionFile X WP st x g m rc o) := by
  dsimp only
  let WP : PEParams := ⟨W.C, W.Q⟩
  let inp := pqRecvInputs WP st (wirePrekey :: m.bytes) rc
  obtain ⟨Run, hmainW, _, hcanonCl⟩ := hoverD3 H.base547NeZero X W hF hE hD hX hPub hF512 hEnc hDec hK
  by_cases hstin : (wirePrekey :: m.bytes).length > stdinCapBytes
  · refine ⟨.exited 2 [] (filesOf inp.files), ?_, by simp only [hstin, ↓reduceIte]; rfl⟩
    exact cliRunPlainPanPlacedSig_of_strict_f3_sampleNtt_stdinOverCap
      (externPreservesNoAllocFailed_cliExternsPlaced mmpl W) H hmainW
      (cliInputsOk_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
      (inputsLoadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hst)
      (isStdinOverCap_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hstin) hNoStuck
  · obtain ⟨a, hrun, hp, hcommit⟩ := hcanonCl st hst x g hsess m rc hinner hnomatch
    obtain ⟨o, ho, hpo⟩ :=
      cliRunPlainPanPlacedSig_of_strict_f3_sampleNtt_call_pred
        (P := fun o =>
          OutcomeMatchesModelExceptPath WP inp (sessionFile (partyAddress st.party.other))
            (pqRecvPrekeyModel X WP { st with session := none } m rc) o ∧
          D3NoMatchSessionFile X WP st x g m rc o)
        (externPreservesNoAllocFailed_cliExternsPlaced mmpl W) H hmainW
        (cliInputsOk_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
        (inputsLoadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hst)
        hrun (not_isSendOverCap_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
        (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin))
        hp (coinsReadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc) hcommit hNoStuck
    refine ⟨o, ho, ?_⟩
    simp only [hstin, ↓reduceIte]
    exact hpo

theorem d3_canonical_noMatch_outcomeUpTo_of_plain_f3G
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3PlainB2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hoverD3 : MainOkOverD3F3G mpl mmpl CodeOk libcAddr elf.brkStart stk)
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
      ∀ (i : Inputs), V2F3StuckDomain ⟨W.C, W.Q⟩ i →
        CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W i →
        cliRunPlainPanPlacedSig mpl mmpl elf W i = none) :
    ∀ (W : CliHooks),
      W.C.F = sha256Compress →
      W.C.E = CryptoGames.AES256.aes256Enc →
      W.C.D = CryptoGames.AES256.aes256Dec →
      W.C.X = CryptoGames.RFC7748.x25519Ref →
      W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
      W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
      W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
      W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
      W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
      ∀ (X : UnreachedPqxdhPrimitives) (st : PqParty),
        PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st →
        ∀ (x : RecordExtras) (g : GhostState (List (BitVec 8))), st.session = some (x, g) →
        ∀ (m : PreKeyMessageFields) (rc : BitVec 256),
          m.inner.length + 2048 < 2 ^ 32 → ¬ PqSessionMatches x g m →
          let WP : PEParams := ⟨W.C, W.Q⟩
          let inp := pqRecvInputs WP st (wirePrekey :: m.bytes) rc
          OutcomeOrExcusedAbort
            (fun k => CliReachesOOMPlainPanPlaced mpl mmpl elf W k ∨
              CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W k)
            (cliRunPlainPanPlacedSig mpl mmpl elf W) inp
            (fun o => if (wirePrekey :: m.bytes).length > stdinCapBytes then
                o = .exited 2 [] (filesOf inp.files)
              else
                OutcomeMatchesModelExceptPath WP inp (sessionFile (partyAddress st.party.other))
                  (pqRecvPrekeyModel X WP { st with session := none } m rc) o ∧
                D3NoMatchSessionFile X WP st x g m rc o) := by
  intro W hF hE hD hX hPub hF512 hEnc hDec hK X st hst x g hsess m rc hinner hnomatch
  dsimp only
  let WP : PEParams := ⟨W.C, W.Q⟩
  let inp := pqRecvInputs WP st (wirePrekey :: m.bytes) rc
  by_cases hStuck : CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W inp
  · exact Or.inr ⟨hStuckDiv W hF hE hD hX hPub hF512 hEnc hDec hK inp
      (Or.inr (Or.inl ⟨st, m.bytes, rc, hst, rfl⟩)) hStuck, Or.inr hStuck⟩
  · exact Or.inl (d3_canonical_noMatch_strict_of_plain_f3G H hoverD3 W hF hE hD hX hPub hF512 hEnc
      hDec hK X st hst x g hsess m rc hinner hnomatch hStuck)

private theorem ite_pos_plain {α : Type} {c : Prop} [inst : Decidable c] (hc : c) {a b : α} :
    (if c then a else b) = a := match inst with | isTrue _ => rfl | isFalse h => absurd hc h

private theorem ite_neg_plain {α : Type} {c : Prop} [inst : Decidable c] (hc : ¬ c) {a b : α} :
    (if c then a else b) = b := match inst with | isTrue h => absurd h hc | isFalse _ => rfl

private theorem filesOf_eq_match_filesFold_plain (f : List (String × List (BitVec 8))) {p : String}
    (hne : normalizePath p ≠ [])
    (hns : normalizePath p ∉ stdioPaths.map normalizePath) :
    filesOf f p = match (filesFold f {}).entries (normalizePath p) with
      | some (.file bs) => some bs | _ => none := by
  unfold filesOf fsView
  rw [ite_neg_plain hns, files_eq_entries,
    ite_neg_plain (by rw [List.isEmpty_eq_false_iff.mpr hne]; decide),
    initFsState_entries ({ files := f } : ProcessInputs) (normalizePath p) hns]
  rfl

private theorem filesOf_pqInitInputsF_coins_plain {P : PEParams} {st : PqParty}
    {files : List (String × List (BitVec 8))} {t : List.Vector (BitVec 8) initiateTapeLen}
    {i : Inputs} (heq : InputsEquivRaw i (pqInitInputsFRaw P st files t)) :
    filesOf i.files coinsFile = some t.toList := by
  rw [heq.2.2.2 coinsFile]
  have hne : normalizePath coinsFile ≠ [] := by decide
  have hns : normalizePath coinsFile ∉ stdioPaths.map normalizePath := by decide
  rw [filesOf_eq_match_filesFold_plain _ hne hns,
    show (pqInitInputsFRaw P st files t).files =
      (encodeDir P st ++ files) ++ [(coinsFile, t.toList)] by
        simp [pqInitInputsFRaw, pqInputs, List.append_assoc],
    filesFold_eq_foldl_fileStep, List.foldl_append, List.foldl_cons, List.foldl_nil,
    fileStep_entries, ite_pos_plain rfl]

private theorem coinsReadable_of_inputsEquiv_pqInitInputsF_plain {P : PEParams} {st : PqParty}
    {files : List (String × List (BitVec 8))} {t : List.Vector (BitVec 8) initiateTapeLen}
    {i : Inputs} (heq : InputsEquivRaw i (pqInitInputsFRaw P st files t)) :
    CoinsReadable i := by
  have hc := filesOf_pqInitInputsF_coins_plain heq
  have hne : normalizePath coinsFile ≠ [] := by decide
  have hns : normalizePath coinsFile ∉ stdioPaths.map normalizePath := by decide
  rw [filesOf_eq_match_filesFold_plain _ hne hns] at hc
  have hfold : (filesFold i.files {}).entries (normalizePath coinsFile) =
      some (.file t.toList) := by
    rcases hf : (filesFold i.files {}).entries (normalizePath coinsFile) with _ | bs | _ <;>
      rw [hf] at hc <;>
      [cases hc;
       (dsimp only at hc
        exact congrArg (fun x => some (FsEntry.file x)) (Option.some.inj hc));
       cases hc]
  unfold CoinsReadable
  rw [show "coins" = coinsFile from rfl, files_eq_entries,
    ite_neg_plain (by rw [List.isEmpty_eq_false_iff.mpr hne]; decide),
    initFsState_entries (cliInputs i) (normalizePath coinsFile) hns]
  change (filesFold i.files (dirsFold i.dirs {})).entries (normalizePath coinsFile) ≠
      some .dir ∧
    ∀ bs, (filesFold i.files (dirsFold i.dirs {})).entries (normalizePath coinsFile) =
      some (.file bs) → bs.length ≤ fileCapBytes
  rw [filesFold_entries_eq_or i.files _ hne, hfold, Option.some_or]
  refine ⟨fun h => FsEntry.noConfusion (Option.some.inj h), fun bs h => ?_⟩
  injection h with h
  injection h with h
  subst h
  simp [List.Vector.toList_length, initiateTapeLen, fileCapBytes]

private theorem not_isSendOverCap_of_inputsEquiv_pqInitInputsF_plain {P : PEParams} {st : PqParty}
    {files : List (String × List (BitVec 8))} {t : List.Vector (BitVec 8) initiateTapeLen}
    {i : Inputs} (heq : InputsEquivRaw i (pqInitInputsFRaw P st files t)) :
    ¬ IsSendOverCap i := by
  rintro ⟨-, hgt⟩
  rw [heq.2.2.1] at hgt
  simp [pqInitInputsFRaw, pqInputs] at hgt

private theorem not_isStdinOverCap_of_inputsEquiv_pqInitInputsF_plain {P : PEParams} {st : PqParty}
    {files : List (String × List (BitVec 8))} {t : List.Vector (BitVec 8) initiateTapeLen}
    {i : Inputs} (heq : InputsEquivRaw i (pqInitInputsFRaw P st files t)) :
    ¬ IsStdinOverCap i := by
  rintro ⟨-, hgt⟩
  rw [heq.2.2.1] at hgt
  simp [pqInitInputsFRaw, pqInputs, stdinCapBytes] at hgt

private def dummyUnreachedD3Plain : UnreachedPqxdhPrimitives where
  sigPkGen := fun _ => []
  sigSign := fun _ _ _ => []
  scalarMul := fun _ _ => []
  scalarAdd := fun _ _ => []
  kemKeyGen := fun _ => ([], [])
  pow8 := fun _ => []
  isValidDhTriple := fun _ _ _ => false

section OfPlainF3G

variable {mpl mmpl : MultiPlacement}
  {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
  {elf : ElfImage}
  (H : CliElfF3PlainB2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
  (hinitSem : MainInitRunSemOkF3G mpl mmpl CodeOk libcAddr elf.brkStart stk)
include H hinitSem

private theorem cliRunPlainPanPlacedSig_of_f3_semG (W : CliHooks)
    (hF : W.C.F = sha256Compress)
    (hE : W.C.E = CryptoGames.AES256.aes256Enc)
    (hD : W.C.D = CryptoGames.AES256.aes256Dec)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (hF512 : W.Q.F512 = CryptoGames.SHA512.sha512CompressState)
    (hEnc : W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec)
    (hDec : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    (X : UnreachedPqxdhPrimitives)
    {i : Inputs} {o : Outcome}
    (hdom : CliInitD3Inputs ⟨W.C, W.Q⟩ i)
    (hi : CliInputsOk i) (hload : InputsLoadable i)
    (hnoc : ¬ IsSendOverCap i) (hnstin : ¬ IsStdinOverCap i)
    (hcoins : CoinsReadable i)
    (hstep : ∀ S : RunSem, InitRunSemOk S X ⟨W.C, W.Q⟩ →
      runRel S i (runAns S i) ∧
      CommitOk i (MainResult.ofAnswer (runAns S i)) ∧
      observe i.files (runAns S i) = o)
    (hNoStuck : ¬ CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W i) :
    cliRunPlainPanPlacedSig mpl mmpl elf W i = some o := by
  obtain ⟨S, hS, hmainW⟩ := hinitSem H.base547NeZero X W hF hE hD hX hPub hF512 hEnc hDec hK
  obtain ⟨hrel, hcommit, hobs⟩ := hstep S hS
  exact cliRunPlainPanPlacedSig_of_strict_f3_sampleNtt_call_obs
    (externPreservesNoAllocFailed_cliExternsPlaced mmpl W) H hmainW
    hi hload ⟨hdom, hrel⟩ hnoc hnstin hobs hcoins hcommit hNoStuck

private theorem cliRunPlainPanPlacedSig_pqInitFiles_exact_eq_some_of_f3G
    (W : CliHooks)
    (hF : W.C.F = sha256Compress)
    (hE : W.C.E = CryptoGames.AES256.aes256Enc)
    (hD : W.C.D = CryptoGames.AES256.aes256Dec)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (hF512 : W.Q.F512 = CryptoGames.SHA512.sha512CompressState)
    (hEnc : W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec)
    (hDec : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    (X : UnreachedPqxdhPrimitives)
    {st : PqParty} {files : List (String × List (BitVec 8))} {b : PreKeyBundleFields}
    {t : List.Vector (BitVec 8) initiateTapeLen} {i : Inputs}
    (heq : InputsEquivRaw i (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t))
    (hload : InputsLoadable i)
    (hwf : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st) (hs : st.session = none)
    (hb : BundleFilesFlatRaw files)
    (hcap : BundleReadWithinCap (filesOf files) bundleDir)
    (hparse : parseBundleDir (filesOf files) bundleDir = some (publicBundleOf b))
    (hNoStuck : ¬ CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W i) :
    cliRunPlainPanPlacedSig mpl mmpl elf W i =
      some (pqxdhExpectedOutcome ⟨W.C, W.Q⟩ (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t)
        (pqInitModel X ⟨W.C, W.Q⟩ st b t)) :=
  cliRunPlainPanPlacedSig_of_f3_semG H hinitSem W hF hE hD hX hPub hF512 hEnc hDec hK X
    ⟨st, files, t, hwf, hs, hb, heq⟩
    (cliInputsOk_of_inputsEquivRaw heq (cliInputsOk_pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t))
    hload (not_isSendOverCap_of_inputsEquiv_pqInitInputsF_plain heq)
    (not_isStdinOverCap_of_inputsEquiv_pqInitInputsF_plain heq)
    (coinsReadable_of_inputsEquiv_pqInitInputsF_plain heq)
    (fun _ hS => observe_accept_pqInitInputsFRaw_eq X ⟨W.C, W.Q⟩ heq hwf hs hb hcap hparse hS)
    hNoStuck

theorem cliRunPlainPanPlacedSig_pqInitFiles_exact_ne_none_of_f3G
    (W : CliHooks)
    (hF : W.C.F = sha256Compress)
    (hE : W.C.E = CryptoGames.AES256.aes256Enc)
    (hD : W.C.D = CryptoGames.AES256.aes256Dec)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (hF512 : W.Q.F512 = CryptoGames.SHA512.sha512CompressState)
    (hEnc : W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec)
    (hDec : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    (X : UnreachedPqxdhPrimitives)
    {st : PqParty} {files : List (String × List (BitVec 8))} {b : PreKeyBundleFields}
    {t : List.Vector (BitVec 8) initiateTapeLen} {i : Inputs}
    (heq : InputsEquivRaw i (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t))
    (hload : InputsLoadable i)
    (hwf : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st) (hs : st.session = none)
    (hb : BundleFilesFlatRaw files)
    (hcap : BundleReadWithinCap (filesOf files) bundleDir)
    (hparse : parseBundleDir (filesOf files) bundleDir = some (publicBundleOf b))
    (hNoStuck : ¬ CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W i) :
    cliRunPlainPanPlacedSig mpl mmpl elf W i ≠ none := by
  rw [cliRunPlainPanPlacedSig_pqInitFiles_exact_eq_some_of_f3G H hinitSem W hF hE hD hX hPub hF512
    hEnc hDec hK X heq hload hwf hs hb hcap hparse hNoStuck]
  intro hnone; cases hnone

private theorem outcomeUpTo_pqInitFiles_exact_of_plain_f3G
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
      ∀ (i : Inputs), V2F3StuckDomain ⟨W.C, W.Q⟩ i →
        CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W i →
        cliRunPlainPanPlacedSig mpl mmpl elf W i = none)
    (W : CliHooks)
    (hF : W.C.F = sha256Compress)
    (hE : W.C.E = CryptoGames.AES256.aes256Enc)
    (hD : W.C.D = CryptoGames.AES256.aes256Dec)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (hF512 : W.Q.F512 = CryptoGames.SHA512.sha512CompressState)
    (hEnc : W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec)
    (hDec : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    (X : UnreachedPqxdhPrimitives)
    {st : PqParty} {files : List (String × List (BitVec 8))} {b : PreKeyBundleFields}
    {t : List.Vector (BitVec 8) initiateTapeLen} {i : Inputs}
    (heq : InputsEquivRaw i (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t))
    (hload : InputsLoadable i)
    (hwf : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st) (hs : st.session = none)
    (hb : BundleFilesFlatRaw files)
    (hcap : BundleReadWithinCap (filesOf files) bundleDir)
    (hparse : parseBundleDir (filesOf files) bundleDir = some (publicBundleOf b)) :
    OutcomeOrExcusedAbort
      (fun k => CliReachesOOMPlainPanPlaced mpl mmpl elf W k ∨
        CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W k)
      (cliRunPlainPanPlacedSig mpl mmpl elf W) i
      (· = pqxdhExpectedOutcome ⟨W.C, W.Q⟩ (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t)
        (pqInitModel X ⟨W.C, W.Q⟩ st b t)) := by
  by_cases hStuck : CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W i
  · exact Or.inr ⟨hStuckDiv W hF hE hD hX hPub hF512 hEnc hDec hK i
      (Or.inr (Or.inr ⟨⟨st, files, t, hwf, hs, hb, heq⟩, hload⟩)) hStuck, Or.inr hStuck⟩
  · exact outcomeOrExcusedAbort_of_eq
      (cliRunPlainPanPlacedSig_pqInitFiles_exact_eq_some_of_f3G H hinitSem W hF hE hD hX hPub hF512
        hEnc hDec hK X heq hload hwf hs hb hcap hparse hStuck)

theorem outcomeUpTo_pqInitFiles_exact_or_none_of_plain_f3G
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
      ∀ (i : Inputs), V2F3StuckDomain ⟨W.C, W.Q⟩ i →
        CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W i →
        cliRunPlainPanPlacedSig mpl mmpl elf W i = none)
    (W : CliHooks)
    (hF : W.C.F = sha256Compress)
    (hE : W.C.E = CryptoGames.AES256.aes256Enc)
    (hD : W.C.D = CryptoGames.AES256.aes256Dec)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (hF512 : W.Q.F512 = CryptoGames.SHA512.sha512CompressState)
    (hEnc : W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec)
    (hDec : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    (X : UnreachedPqxdhPrimitives)
    {st : PqParty} {files : List (String × List (BitVec 8))} {b : PreKeyBundleFields}
    {t : List.Vector (BitVec 8) initiateTapeLen} {i : Inputs}
    (heq : InputsEquivRaw i (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t))
    (hwf : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st) (hs : st.session = none)
    (hb : BundleFilesFlatRaw files)
    (hcap : BundleReadWithinCap (filesOf files) bundleDir)
    (hparse : parseBundleDir (filesOf files) bundleDir = some (publicBundleOf b)) :
    cliRunPlainPanPlacedSig mpl mmpl elf W i = none ∨
      OutcomeOrExcusedAbort
        (fun k => CliReachesOOMPlainPanPlaced mpl mmpl elf W k ∨
          CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W k)
        (cliRunPlainPanPlacedSig mpl mmpl elf W) i
        (· = pqxdhExpectedOutcome ⟨W.C, W.Q⟩ (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t)
          (pqInitModel X ⟨W.C, W.Q⟩ st b t)) := by
  by_cases hload : InputsLoadable i
  · exact .inr (outcomeUpTo_pqInitFiles_exact_of_plain_f3G H hinitSem hStuckDiv W hF hE hD hX hPub
      hF512 hEnc hDec hK X heq hload hwf hs hb hcap hparse)
  · exact .inl (cliRunPlainPanPlacedSig_eq_none_of_not_inputsLoadable elf W hload)

private theorem cliRunPlainPanPlacedSig_pqInitReject_eq_some_of_f3G (W : CliHooks)
    (hF : W.C.F = sha256Compress)
    (hE : W.C.E = CryptoGames.AES256.aes256Enc)
    (hD : W.C.D = CryptoGames.AES256.aes256Dec)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (hF512 : W.Q.F512 = CryptoGames.SHA512.sha512CompressState)
    (hEnc : W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec)
    (hDec : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    {st : PqParty} {files : List (String × List (BitVec 8))}
    {t : List.Vector (BitVec 8) initiateTapeLen} {i : Inputs}
    (heq : InputsEquivRaw i (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t))
    (hload : InputsLoadable i)
    (hwf : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st) (hs : st.session = none)
    (hb : BundleFilesFlatRaw files)
    (hparse : parseBundleDir (filesOf files) bundleDir = none)
    (hNoStuck : ¬ CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W i) :
    cliRunPlainPanPlacedSig mpl mmpl elf W i =
      some (.exited 1 [] (filesOf (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t).files)) :=
  cliRunPlainPanPlacedSig_of_f3_semG H hinitSem W hF hE hD hX hPub hF512 hEnc hDec hK
    dummyUnreachedD3Plain ⟨st, files, t, hwf, hs, hb, heq⟩
    (cliInputsOk_of_inputsEquivRaw heq (cliInputsOk_pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t))
    hload (not_isSendOverCap_of_inputsEquiv_pqInitInputsF_plain heq)
    (not_isStdinOverCap_of_inputsEquiv_pqInitInputsF_plain heq)
    (coinsReadable_of_inputsEquiv_pqInitInputsF_plain heq)
    (fun _ hS => observe_reject_pqInitInputsFRaw_eq dummyUnreachedD3Plain ⟨W.C, W.Q⟩ heq hwf hs hb
      hparse hS)
    hNoStuck

theorem cliRunPlainPanPlacedSig_pqInitReject_ne_none_of_f3G (W : CliHooks)
    (hF : W.C.F = sha256Compress)
    (hE : W.C.E = CryptoGames.AES256.aes256Enc)
    (hD : W.C.D = CryptoGames.AES256.aes256Dec)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (hF512 : W.Q.F512 = CryptoGames.SHA512.sha512CompressState)
    (hEnc : W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec)
    (hDec : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    {st : PqParty} {files : List (String × List (BitVec 8))}
    {t : List.Vector (BitVec 8) initiateTapeLen} {i : Inputs}
    (heq : InputsEquivRaw i (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t))
    (hload : InputsLoadable i)
    (hwf : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st) (hs : st.session = none)
    (hb : BundleFilesFlatRaw files)
    (hparse : parseBundleDir (filesOf files) bundleDir = none)
    (hNoStuck : ¬ CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W i) :
    cliRunPlainPanPlacedSig mpl mmpl elf W i ≠ none := by
  rw [cliRunPlainPanPlacedSig_pqInitReject_eq_some_of_f3G H hinitSem W hF hE hD hX hPub hF512 hEnc
    hDec hK heq hload hwf hs hb hparse hNoStuck]
  intro hnone; cases hnone

private theorem outcomeUpTo_pqInitReject_of_plain_f3G
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
      ∀ (i : Inputs), V2F3StuckDomain ⟨W.C, W.Q⟩ i →
        CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W i →
        cliRunPlainPanPlacedSig mpl mmpl elf W i = none)
    (W : CliHooks)
    (hF : W.C.F = sha256Compress)
    (hE : W.C.E = CryptoGames.AES256.aes256Enc)
    (hD : W.C.D = CryptoGames.AES256.aes256Dec)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (hF512 : W.Q.F512 = CryptoGames.SHA512.sha512CompressState)
    (hEnc : W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec)
    (hDec : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    {st : PqParty} {files : List (String × List (BitVec 8))}
    {t : List.Vector (BitVec 8) initiateTapeLen} {i : Inputs}
    (heq : InputsEquivRaw i (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t))
    (hload : InputsLoadable i)
    (hwf : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st) (hs : st.session = none)
    (hb : BundleFilesFlatRaw files)
    (hparse : parseBundleDir (filesOf files) bundleDir = none) :
    OutcomeOrExcusedAbort
      (fun k => CliReachesOOMPlainPanPlaced mpl mmpl elf W k ∨
        CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W k)
      (cliRunPlainPanPlacedSig mpl mmpl elf W) i
      (· = .exited 1 [] (filesOf (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t).files)) := by
  by_cases hStuck : CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W i
  · exact Or.inr ⟨hStuckDiv W hF hE hD hX hPub hF512 hEnc hDec hK i
      (Or.inr (Or.inr ⟨⟨st, files, t, hwf, hs, hb, heq⟩, hload⟩)) hStuck, Or.inr hStuck⟩
  · exact outcomeOrExcusedAbort_of_eq
      (cliRunPlainPanPlacedSig_pqInitReject_eq_some_of_f3G H hinitSem W hF hE hD hX hPub hF512 hEnc
        hDec hK heq hload hwf hs hb hparse hStuck)

theorem outcomeUpTo_pqInitReject_or_none_of_plain_f3G
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
      ∀ (i : Inputs), V2F3StuckDomain ⟨W.C, W.Q⟩ i →
        CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W i →
        cliRunPlainPanPlacedSig mpl mmpl elf W i = none)
    (W : CliHooks)
    (hF : W.C.F = sha256Compress)
    (hE : W.C.E = CryptoGames.AES256.aes256Enc)
    (hD : W.C.D = CryptoGames.AES256.aes256Dec)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (hF512 : W.Q.F512 = CryptoGames.SHA512.sha512CompressState)
    (hEnc : W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec)
    (hDec : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    {st : PqParty} {files : List (String × List (BitVec 8))}
    {t : List.Vector (BitVec 8) initiateTapeLen} {i : Inputs}
    (heq : InputsEquivRaw i (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t))
    (hwf : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st) (hs : st.session = none)
    (hb : BundleFilesFlatRaw files)
    (hparse : parseBundleDir (filesOf files) bundleDir = none) :
    cliRunPlainPanPlacedSig mpl mmpl elf W i = none ∨
      OutcomeOrExcusedAbort
        (fun k => CliReachesOOMPlainPanPlaced mpl mmpl elf W k ∨
          CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W k)
        (cliRunPlainPanPlacedSig mpl mmpl elf W) i
        (· = .exited 1 [] (filesOf (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t).files)) := by
  by_cases hload : InputsLoadable i
  · exact .inr (outcomeUpTo_pqInitReject_of_plain_f3G H hinitSem hStuckDiv W hF hE hD hX hPub hF512
      hEnc hDec hK heq hload hwf hs hb hparse)
  · exact .inl (cliRunPlainPanPlacedSig_eq_none_of_not_inputsLoadable elf W hload)

private theorem cliRunPlainPanPlacedSig_pqInitOverCap_eq_some_of_f3G (W : CliHooks)
    (hF : W.C.F = sha256Compress)
    (hE : W.C.E = CryptoGames.AES256.aes256Enc)
    (hD : W.C.D = CryptoGames.AES256.aes256Dec)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (hF512 : W.Q.F512 = CryptoGames.SHA512.sha512CompressState)
    (hEnc : W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec)
    (hDec : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    {st : PqParty} {files : List (String × List (BitVec 8))}
    {t : List.Vector (BitVec 8) initiateTapeLen} {i : Inputs}
    (heq : InputsEquivRaw i (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t))
    (hload : InputsLoadable i)
    (hwf : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st) (hs : st.session = none)
    (hb : BundleFilesFlatRaw files)
    (hover : ¬ BundleReadWithinCap (filesOf files) bundleDir)
    (hNoStuck : ¬ CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W i) :
    cliRunPlainPanPlacedSig mpl mmpl elf W i =
      some (.exited 1 [] (filesOf (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t).files)) :=
  cliRunPlainPanPlacedSig_of_f3_semG H hinitSem W hF hE hD hX hPub hF512 hEnc hDec hK
    dummyUnreachedD3Plain ⟨st, files, t, hwf, hs, hb, heq⟩
    (cliInputsOk_of_inputsEquivRaw heq (cliInputsOk_pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t))
    hload (not_isSendOverCap_of_inputsEquiv_pqInitInputsF_plain heq)
    (not_isStdinOverCap_of_inputsEquiv_pqInitInputsF_plain heq)
    (coinsReadable_of_inputsEquiv_pqInitInputsF_plain heq)
    (fun _ hS => observe_overCap_pqInitInputsFRaw_eq dummyUnreachedD3Plain ⟨W.C, W.Q⟩ heq hwf hs hb
      hover hS)
    hNoStuck

theorem cliRunPlainPanPlacedSig_pqInitOverCap_ne_none_of_f3G (W : CliHooks)
    (hF : W.C.F = sha256Compress)
    (hE : W.C.E = CryptoGames.AES256.aes256Enc)
    (hD : W.C.D = CryptoGames.AES256.aes256Dec)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (hF512 : W.Q.F512 = CryptoGames.SHA512.sha512CompressState)
    (hEnc : W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec)
    (hDec : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    {st : PqParty} {files : List (String × List (BitVec 8))}
    {t : List.Vector (BitVec 8) initiateTapeLen} {i : Inputs}
    (heq : InputsEquivRaw i (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t))
    (hload : InputsLoadable i)
    (hwf : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st) (hs : st.session = none)
    (hb : BundleFilesFlatRaw files)
    (hover : ¬ BundleReadWithinCap (filesOf files) bundleDir)
    (hNoStuck : ¬ CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W i) :
    cliRunPlainPanPlacedSig mpl mmpl elf W i ≠ none := by
  rw [cliRunPlainPanPlacedSig_pqInitOverCap_eq_some_of_f3G H hinitSem W hF hE hD hX hPub hF512 hEnc
    hDec hK heq hload hwf hs hb hover hNoStuck]
  intro hnone; cases hnone

private theorem outcomeUpTo_pqInitOverCap_of_plain_f3G
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
      ∀ (i : Inputs), V2F3StuckDomain ⟨W.C, W.Q⟩ i →
        CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W i →
        cliRunPlainPanPlacedSig mpl mmpl elf W i = none)
    (W : CliHooks)
    (hF : W.C.F = sha256Compress)
    (hE : W.C.E = CryptoGames.AES256.aes256Enc)
    (hD : W.C.D = CryptoGames.AES256.aes256Dec)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (hF512 : W.Q.F512 = CryptoGames.SHA512.sha512CompressState)
    (hEnc : W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec)
    (hDec : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    {st : PqParty} {files : List (String × List (BitVec 8))}
    {t : List.Vector (BitVec 8) initiateTapeLen} {i : Inputs}
    (heq : InputsEquivRaw i (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t))
    (hload : InputsLoadable i)
    (hwf : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st) (hs : st.session = none)
    (hb : BundleFilesFlatRaw files)
    (hover : ¬ BundleReadWithinCap (filesOf files) bundleDir) :
    OutcomeOrExcusedAbort
      (fun k => CliReachesOOMPlainPanPlaced mpl mmpl elf W k ∨
        CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W k)
      (cliRunPlainPanPlacedSig mpl mmpl elf W) i
      (· = .exited 1 [] (filesOf (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t).files)) := by
  by_cases hStuck : CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W i
  · exact Or.inr ⟨hStuckDiv W hF hE hD hX hPub hF512 hEnc hDec hK i
      (Or.inr (Or.inr ⟨⟨st, files, t, hwf, hs, hb, heq⟩, hload⟩)) hStuck, Or.inr hStuck⟩
  · exact outcomeOrExcusedAbort_of_eq
      (cliRunPlainPanPlacedSig_pqInitOverCap_eq_some_of_f3G H hinitSem W hF hE hD hX hPub hF512 hEnc
        hDec hK heq hload hwf hs hb hover hStuck)

theorem outcomeUpTo_pqInitOverCap_or_none_of_plain_f3G
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
      ∀ (i : Inputs), V2F3StuckDomain ⟨W.C, W.Q⟩ i →
        CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W i →
        cliRunPlainPanPlacedSig mpl mmpl elf W i = none)
    (W : CliHooks)
    (hF : W.C.F = sha256Compress)
    (hE : W.C.E = CryptoGames.AES256.aes256Enc)
    (hD : W.C.D = CryptoGames.AES256.aes256Dec)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (hF512 : W.Q.F512 = CryptoGames.SHA512.sha512CompressState)
    (hEnc : W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec)
    (hDec : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    {st : PqParty} {files : List (String × List (BitVec 8))}
    {t : List.Vector (BitVec 8) initiateTapeLen} {i : Inputs}
    (heq : InputsEquivRaw i (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t))
    (hwf : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st) (hs : st.session = none)
    (hb : BundleFilesFlatRaw files)
    (hover : ¬ BundleReadWithinCap (filesOf files) bundleDir) :
    cliRunPlainPanPlacedSig mpl mmpl elf W i = none ∨
      OutcomeOrExcusedAbort
        (fun k => CliReachesOOMPlainPanPlaced mpl mmpl elf W k ∨
          CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W k)
        (cliRunPlainPanPlacedSig mpl mmpl elf W) i
        (· = .exited 1 [] (filesOf (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t).files)) := by
  by_cases hload : InputsLoadable i
  · exact .inr (outcomeUpTo_pqInitOverCap_of_plain_f3G H hinitSem hStuckDiv W hF hE hD hX hPub
      hF512 hEnc hDec hK heq hload hwf hs hb hover)
  · exact .inl (cliRunPlainPanPlacedSig_eq_none_of_not_inputsLoadable elf W hload)

end OfPlainF3G

/-! ## 4. Whole-Process `CliPqBinaryV2OomF3PlainPanPlaced` Assembly -/

theorem cliPqBinaryV2OomF3PlainPanPlaced_of_f3B2NeedLocksG
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3PlainB2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmain : MainOkCliF3PqB2NeedLocksPlacedAtGWithF sha256Compress mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hoverD3 : MainOkOverD3F3G mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (huntyped : MainOkUntypedD3F3G mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hpathB : MainOkPathBD3F3G mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hvalidMatch : MainOkValidMatchD3F3G mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hinitSem : MainInitRunSemOkF3G mpl mmpl CodeOk libcAddr elf.brkStart stk)
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
      ∀ (i : Inputs), V2F3StuckDomain ⟨W.C, W.Q⟩ i →
        CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W i →
        cliRunPlainPanPlacedSig mpl mmpl elf W i = none) :
    CliPqBinaryV2OomF3PlainPanPlaced mpl mmpl elf where
  base := cliPqxdhElfCorrectPlainPanPlacedWith_of_f3B2NeedLocksG' H hmain
    (mainOkCliF3OverG_of_mainOkOverD3F3G hoverD3)
    (fun W hF hE hD hX hPub hF512 hEnc hDec hK i hi hStuck =>
      hStuckDiv W hF hE hD hX hPub hF512 hEnc hDec hK i (Or.inl hi) hStuck)
  recvOverStdinCap := fun W hF hE hD hX hPub hF512 hEnc hDec hK =>
    d3_recvOverStdinCap_of_plain_f3G H hmain hStuckDiv W hF hE hD hX hPub hF512 hEnc hDec hK
  canonicalNoMatch := fun W hF hE hD hX hPub hF512 hEnc hDec hK =>
    d3_canonical_noMatch_outcomeUpTo_of_plain_f3G H hoverD3 hStuckDiv W hF hE hD hX hPub hF512 hEnc
      hDec hK
  pksmParseNone := fun W hF hE hD hX hPub hF512 hEnc hDec hK =>
    d3_pksmParseNone_of_plain_f3G H (mainOkParseNoneD3F3G_of_untypedG huntyped) hStuckDiv W hF hE
      hD hX hPub hF512 hEnc hDec hK
  untypedReject := fun W hF hE hD hX hPub hF512 hEnc hDec hK =>
    d3_untypedReject_of_plain_f3G H huntyped hStuckDiv W hF hE hD hX hPub hF512 hEnc hDec hK
  matchingPathB := fun W hF hE hD hX hPub hF512 hEnc hDec hK =>
    d3_matchingPathB_of_plain_f3G H hpathB hStuckDiv W hF hE hD hX hPub hF512 hEnc hDec hK
  validMatch := fun W hF hE hD hX hPub hF512 hEnc hDec hK =>
    d3_valid_match_outcomeUpTo_of_plain_f3G H hvalidMatch hStuckDiv W hF hE hD hX hPub hF512 hEnc
      hDec hK
  validOver := fun W hF hE hD hX hPub hF512 hEnc hDec hK =>
    d3_valid_over_outcomeUpTo_of_plain_f3G H hoverD3 hStuckDiv W hF hE hD hX hPub hF512 hEnc hDec hK
  initFiles := fun W hF hE hD hX hPub hF512 hEnc hDec hK X _st _files _b _t _i heq hwf hs hb hcap hparse =>
    outcomeUpTo_pqInitFiles_exact_or_none_of_plain_f3G H hinitSem hStuckDiv W hF hE hD hX hPub
      hF512 hEnc hDec hK X heq hwf hs hb hcap hparse
  initReject := fun W hF hE hD hX hPub hF512 hEnc hDec hK _st _files _t _i heq hwf hs hb hparse =>
    outcomeUpTo_pqInitReject_or_none_of_plain_f3G H hinitSem hStuckDiv W hF hE hD hX hPub hF512 hEnc
      hDec hK heq hwf hs hb hparse
  initOverFileCap := fun W hF hE hD hX hPub hF512 hEnc hDec hK _st _files _t _i heq hwf hs hb hover =>
    outcomeUpTo_pqInitOverCap_or_none_of_plain_f3G H hinitSem hStuckDiv W hF hE hD hX hPub hF512
      hEnc hDec hK heq hwf hs hb hover

theorem libsignalCliPqBinaryV2OomF3PlainPanPlacedAt_of_f3B2NeedLocksG
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {bytes : List (BitVec 8)} {elf : ElfImage}
    (hparse : ElfImage.parse bytes = .ok elf)
    (H : CliElfF3PlainB2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmain : MainOkCliF3PqB2NeedLocksPlacedAtGWithF sha256Compress mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hoverD3 : MainOkOverD3F3G mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (huntyped : MainOkUntypedD3F3G mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hpathB : MainOkPathBD3F3G mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hvalidMatch : MainOkValidMatchD3F3G mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hinitSem : MainInitRunSemOkF3G mpl mmpl CodeOk libcAddr elf.brkStart stk)
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
      ∀ (i : Inputs), V2F3StuckDomain ⟨W.C, W.Q⟩ i →
        CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W i →
        cliRunPlainPanPlacedSig mpl mmpl elf W i = none) :
    LibsignalCliPqBinaryV2OomF3PlainPanPlacedAt mpl mmpl bytes :=
  ⟨elf, hparse, cliPqBinaryV2OomF3PlainPanPlaced_of_f3B2NeedLocksG H hmain hoverD3 huntyped hpathB
    hvalidMatch hinitSem hStuckDiv⟩

end LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomPlainF3
