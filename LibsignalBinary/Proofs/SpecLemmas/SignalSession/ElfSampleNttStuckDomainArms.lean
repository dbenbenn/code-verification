/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.Bridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.CliElfProof -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomProofF3G -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Hops -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Top -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.SignalSession.CliElf
public import VerifiedLibraries.Mallocng.Spec
import LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
import LibsignalBinary.Proofs.SignalSession.Cli.Parity.BundleGeneralParse
import LibsignalBinary.Proofs.SignalSession.Cli.ProcessBridge
import LibsignalBinary.Proofs.SignalSession.Cli.ProcessBridgePq
import LibsignalBinary.Proofs.SignalSession.Cli.PublicSpecs
import LibsignalBinary.Specifications.LibsignalE2E.PqxdhInputs

/-!
# `V2F3StuckDomain` Ghost `MainCaseB2` Dispatcher (`ElfSampleNttStuckDomainArms`)

Defines the `EG`-parametric 6-arm ghost block-617 `MainOk` bundle `GhostMainArmsFor`
(`GhostMainOkOverFor`, `GhostMainOkUntypedFor`, `GhostMainOkPathBFor`,
`GhostMainOkValidMatchFor`, `GhostMainInitSemFor`) and proves
`v2F3StuckDomain_ghostMainCase_of_arms`, dispatching every input `i` in `V2F3StuckDomain`
to `CliInputsOk i ∧ InputsLoadable i` together with a ghost `subroutine_ok` witness `Run`
and `MainCaseB2 Run IsSendOverCap IsStdinOverCap i r`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDomainArms

open Arm64 (FsEntry FsPath FsState GhostName State normalizePath subroutine_ok)
open Arm64.Obj (MultiPlacement)
open Arm64.Process (ProcessInputs)
open CryptoGames.LibsignalSession (GhostState)
open CryptoGames.LibsignalSessionApi (PreKeySignalMessage)
open CryptoVerification (LibsignalFrozen LibsignalPlacement)
open CryptoVerification.E2E
  (PEParams PreKeyBundleFields PreKeyMessageFields RecordExtras UnreachedPqxdhPrimitives djbKey
   initiateTapeLen kyberKey wirePrekey wireWhisper)
open CryptoVerification.LibsignalSpqrV1 (sha256Compress)
open CryptoVerification.SignalSession
  (CliHooks CliPqxdhInputs Inputs OutcomeMatchesModelExceptPath PqParty PqSessionMatches
   PqxdhPartyInSpecDomain PublicBundle bundleDir cliElfImage cliInputsOk_pqInitInputs
   cliInputsOk_pqRecvInputs cliInputsOk_pqSendInputs cliProcessInputs coinsFile
   coinsReadable_pqInitInputs coinsReadable_pqRecvInputs coinsReadable_pqSendInputs dirsFold
   encodeDir fileCapBytes filesFold filesOf files_eq_entries fsView initFsState_entries
   inputsLoadable_pqInitInputs inputsLoadable_pqRecvInputs inputsLoadable_pqSendInputs
   isSendOverCap_pqSendInputs isStdinOverCap_pqRecvInputs isStdinOverCap_pqSendInputs
   maxPlaintextBytes not_isSendOverCap_of_stdin_le not_isSendOverCap_pqInitInputs
   not_isSendOverCap_pqRecvInputs not_isStdinOverCap_of_stdin_le not_isStdinOverCap_pqInitInputs
   observe partyAddress pqInitInputs pqInputs pqRecvInputs pqRecvPrekeyModel pqSendInputs
   pqxdhExpectedOutcome publicBundleOf sessionFile stdinCapBytes stdioPaths)
open CryptoVerification.SignalSession.Cli
  (CliInputsOk CoinsReadable CommitOk InputsLoadable IsSendOverCap IsStdinOverCap MainCaseB2
   MainResult RunAnswer cliInputs splitId splitSigned)
open CryptoVerification.SignalSession.Cli.MainHops (cliMainStk)
open CryptoVerification.SignalSession.Cli.RunCompose (RunSem readU32LE runAns runRel)
open CryptoVerification.SignalSession.Cli.RunProofs (SessMatchesPm pkToE?)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit
  (pksmDecodedInnerBytes_length_le pksmParse_inner_eq_decoded)
open LibsignalBinary.Proofs.SignalSession.Cli.D3 (D3NoMatchSessionFile d3PqSessionOf)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomProofF3G (V2F3StuckDomain)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomSpecF3
  (BundleFilesFlatRaw pqInitInputsFRaw)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MatchingPathBF3
  (cliRunSemPathB runRel_pqRecv_matchingPathB)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3
  (defaultExtrasF3 pqD3ScopedRun runRel_pqRecv_parseNone_of_runSem)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3UntypedElfF3
  (cliRunSemD3 runRel_pqRecv_untypedReject)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
  (b2MainSpecTightNeedLocksFineAt cliBudgetLimits)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2GWithF
  (MainOkCliExtPqB2NeedLocksPlacedAtWithF)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
  (cliProgExtPlacedAt cliStaticsPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.Parity
  (BundleReadWithinCap InputsEquivRaw fileStep_entries filesFold_entries_eq_or
   filesFold_eq_foldl_fileStep normDjbKey normKyberKey parseBundleDir)
open LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.BundleInitElfF3
  (InitRunSemOk cliInputsOk_of_inputsEquivRaw cliInputsOk_pqInitInputsFRaw initD3ScopedRun
   observe_accept_pqInitInputsFRaw_eq observe_overCap_pqInitInputsFRaw_eq
   observe_reject_pqInitInputsFRaw_eq)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement)

/-! ## 1. `EG`-Parametric 6-Arm Ghost Block-`617` `MainOk` Specifications -/

/-- Ghost Block-`617` counterpart of `MainOkOverD3F3` parameterized over extern table `EG`. -/
@[expose] def GhostMainOkOverFor [LibsignalPlacement] (mpl mmpl : MultiPlacement)
    (EG : CliHooks → String → Option (State → State)) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    W.C.F = sha256Compress →
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
        subroutine_ok
          (cliProgExtPlacedAt mpl EG 617 W)
          (mpl.base 617)
          (b2MainSpecTightNeedLocksFineAt (mallocngAddrsOfPlacement mmpl).libc (LibsignalFrozen mpl)
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
            cliBudgetLimits fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl)
            Run cliProcessInputs)) ∧
      (∀ (st : PqParty), PqxdhPartyInSpecDomain WP st →
        ∀ (x : RecordExtras) (g : GhostState (List (BitVec 8))), st.session = some (x, g) →
        ∀ (body : List (BitVec 8)) (pm : PreKeySignalMessage) (m : PreKeyMessageFields)
          (rc : BitVec 256),
          body.length < 2 ^ 32 →
          pksmParse body = some pm →
          pkToE? pm = some m →
          m.inner.length + 2048 < 2 ^ 32 →
          ¬ PqSessionMatches x g m →
          let inp := pqRecvInputs WP st (wirePrekey :: body) rc
          ∃ a, Run inp a ∧
            (OutcomeMatchesModelExceptPath WP inp (sessionFile (partyAddress st.party.other))
               (pqRecvPrekeyModel X WP { st with session := none } m rc)
               (observe inp.files a) ∧
             D3NoMatchSessionFile X WP st x g m rc (observe inp.files a)) ∧
            CommitOk inp (MainResult.ofAnswer a)) ∧
      (∀ (st : PqParty), PqxdhPartyInSpecDomain WP st →
        ∀ (x : RecordExtras) (g : GhostState (List (BitVec 8))), st.session = some (x, g) →
        ∀ (m : PreKeyMessageFields) (rc : BitVec 256),
          m.inner.length + 2048 < 2 ^ 32 →
          ¬ PqSessionMatches x g m →
          let inp := pqRecvInputs WP st (wirePrekey :: m.bytes) rc
          ∃ a, Run inp a ∧
            (OutcomeMatchesModelExceptPath WP inp (sessionFile (partyAddress st.party.other))
               (pqRecvPrekeyModel X WP { st with session := none } m rc)
               (observe inp.files a) ∧
             D3NoMatchSessionFile X WP st x g m rc (observe inp.files a)) ∧
            CommitOk inp (MainResult.ofAnswer a))

/-- Ghost Block-`617` counterpart of `MainOkUntypedD3F3` parameterized over extern table `EG`. -/
@[expose] def GhostMainOkUntypedFor [LibsignalPlacement] (mpl mmpl : MultiPlacement)
    (EG : CliHooks → String → Option (State → State)) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ W : CliHooks,
    W.C.F = sha256Compress →
    W.C.E = CryptoGames.AES256.aes256Enc →
    W.C.D = CryptoGames.AES256.aes256Dec →
    W.C.X = CryptoGames.RFC7748.x25519Ref →
    W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
    W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
    W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
    W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
    W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
    ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok
        (cliProgExtPlacedAt mpl EG 617 W)
        (mpl.base 617)
        (b2MainSpecTightNeedLocksFineAt (mallocngAddrsOfPlacement mmpl).libc (LibsignalFrozen mpl)
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
          cliBudgetLimits fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl)
          (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD3 W))) cliProcessInputs)

/-- Ghost Block-`617` counterpart of `MainOkPathBD3F3` parameterized over extern table `EG`. -/
@[expose] def GhostMainOkPathBFor [LibsignalPlacement] (mpl mmpl : MultiPlacement)
    (EG : CliHooks → String → Option (State → State)) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    W.C.F = sha256Compress →
    W.C.E = CryptoGames.AES256.aes256Enc →
    W.C.D = CryptoGames.AES256.aes256Dec →
    W.C.X = CryptoGames.RFC7748.x25519Ref →
    W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
    W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
    W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
    W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
    W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
    ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok
        (cliProgExtPlacedAt mpl EG 617 W)
        (mpl.base 617)
        (b2MainSpecTightNeedLocksFineAt (mallocngAddrsOfPlacement mmpl).libc (LibsignalFrozen mpl)
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
          cliBudgetLimits fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl)
          (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemPathB X W))) cliProcessInputs)

/-- Ghost Block-`617` counterpart of `MainOkValidMatchD3F3` parameterized over extern table `EG`. -/
@[expose] def GhostMainOkValidMatchFor [LibsignalPlacement] (mpl mmpl : MultiPlacement)
    (EG : CliHooks → String → Option (State → State)) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    W.C.F = sha256Compress →
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
        subroutine_ok
          (cliProgExtPlacedAt mpl EG 617 W)
          (mpl.base 617)
          (b2MainSpecTightNeedLocksFineAt (mallocngAddrsOfPlacement mmpl).libc (LibsignalFrozen mpl)
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
            cliBudgetLimits fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl)
            Run cliProcessInputs)) ∧
      ∀ (st : PqParty), PqxdhPartyInSpecDomain WP st →
        ∀ (body : List (BitVec 8)) (pm : PreKeySignalMessage) (m : PreKeyMessageFields)
          (rc : BitVec 256),
          body.length < 2 ^ 32 →
          pksmParse body = some pm →
          pkToE? pm = some m →
          m.inner.length + 2048 < 2 ^ 32 →
          (∀ x g, st.session = some (x, g) → PqSessionMatches x g m) →
          let inp := pqRecvInputs WP st (wirePrekey :: body) rc
          ∃ a, Run inp a ∧
            observe inp.files a = pqxdhExpectedOutcome WP inp (pqRecvPrekeyModel X WP st m rc) ∧
            CommitOk inp (MainResult.ofAnswer a)

/-- Ghost Block-`617` counterpart of `MainInitSemF3` parameterized over extern table `EG`. -/
@[expose] def GhostMainInitSemFor [LibsignalPlacement] (mpl mmpl : MultiPlacement)
    (EG : CliHooks → String → Option (State → State)) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    W.C.F = sha256Compress →
    W.C.E = CryptoGames.AES256.aes256Enc →
    W.C.D = CryptoGames.AES256.aes256Dec →
    W.C.X = CryptoGames.RFC7748.x25519Ref →
    W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
    W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
    W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
    W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
    W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
    ∃ S : RunSem,
      InitRunSemOk S X ⟨W.C, W.Q⟩ ∧
      ∀ (γ : GhostName) (tp : BitVec 64),
        subroutine_ok
          (cliProgExtPlacedAt mpl EG 617 W)
          (mpl.base 617)
          (b2MainSpecTightNeedLocksFineAt (mallocngAddrsOfPlacement mmpl).libc (LibsignalFrozen mpl)
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
            cliBudgetLimits fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl)
            (initD3ScopedRun ⟨W.C, W.Q⟩ (runRel S)) cliProcessInputs)

/-- Bundle of the 6 ghost Block-`617` `MainOk` obligations parameterized over `EG`. -/
structure GhostMainArmsFor [LibsignalPlacement] (mpl mmpl : MultiPlacement)
    (EG : CliHooks → String → Option (State → State)) : Prop where
  hmain : MainOkCliExtPqB2NeedLocksPlacedAtWithF sha256Compress mpl mmpl EG
    617 cliProcessInputs (LibsignalFrozen mpl)
    (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk cliBudgetLimits
  hoverD3 : GhostMainOkOverFor mpl mmpl EG
  huntyped : GhostMainOkUntypedFor mpl mmpl EG
  hpathB : GhostMainOkPathBFor mpl mmpl EG
  hvalidMatch : GhostMainOkValidMatchFor mpl mmpl EG
  hinitSem : GhostMainInitSemFor mpl mmpl EG

/-! ## 2. Pure Side-Condition Helpers for `V2F3StuckDomain` -/

private theorem ite_pos_local {α : Type} {c : Prop} [inst : Decidable c] (hc : c) {a b : α} :
    (if c then a else b) = a :=
  match inst with | isTrue _ => rfl | isFalse h => absurd hc h

private theorem ite_neg_local {α : Type} {c : Prop} [inst : Decidable c] (hc : ¬ c) {a b : α} :
    (if c then a else b) = b :=
  match inst with | isTrue h => absurd h hc | isFalse _ => rfl

private theorem filesOf_eq_match_filesFold_local (f : List (String × List (BitVec 8))) {p : String}
    (hne : normalizePath p ≠ [])
    (hns : normalizePath p ∉ stdioPaths.map normalizePath) :
    filesOf f p = match (filesFold f {}).entries (normalizePath p) with
      | some (.file bs) => some bs | _ => none := by
  unfold filesOf fsView
  rw [ite_neg_local hns, files_eq_entries,
    ite_neg_local (by rw [List.isEmpty_eq_false_iff.mpr hne]; decide),
    initFsState_entries ({ files := f } : ProcessInputs) (normalizePath p) hns]
  rfl

private theorem filesOf_pqInitInputsF_coins_local {P : PEParams} {st : PqParty}
    {files : List (String × List (BitVec 8))} {t : List.Vector (BitVec 8) initiateTapeLen}
    {i : Inputs} (heq : InputsEquivRaw i (pqInitInputsFRaw P st files t)) :
    filesOf i.files coinsFile = some t.toList := by
  rw [heq.2.2.2 coinsFile]
  have hne : normalizePath coinsFile ≠ [] := by decide
  have hns : normalizePath coinsFile ∉ stdioPaths.map normalizePath := by decide
  rw [filesOf_eq_match_filesFold_local _ hne hns,
    show (pqInitInputsFRaw P st files t).files =
      (encodeDir P st ++ files) ++ [(coinsFile, t.toList)] by
        simp [pqInitInputsFRaw, pqInputs, List.append_assoc],
    filesFold_eq_foldl_fileStep, List.foldl_append, List.foldl_cons, List.foldl_nil,
    fileStep_entries, ite_pos_local rfl]

private theorem coinsReadable_of_inputsEquiv_pqInitInputsF {P : PEParams} {st : PqParty}
    {files : List (String × List (BitVec 8))} {t : List.Vector (BitVec 8) initiateTapeLen}
    {i : Inputs} (heq : InputsEquivRaw i (pqInitInputsFRaw P st files t)) :
    CoinsReadable i := by
  have hc := filesOf_pqInitInputsF_coins_local heq
  have hne : normalizePath coinsFile ≠ [] := by decide
  have hns : normalizePath coinsFile ∉ stdioPaths.map normalizePath := by decide
  rw [filesOf_eq_match_filesFold_local _ hne hns] at hc
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
    ite_neg_local (by rw [List.isEmpty_eq_false_iff.mpr hne]; decide),
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

private theorem not_isSendOverCap_of_inputsEquiv_pqInitInputsF {P : PEParams} {st : PqParty}
    {files : List (String × List (BitVec 8))} {t : List.Vector (BitVec 8) initiateTapeLen}
    {i : Inputs} (heq : InputsEquivRaw i (pqInitInputsFRaw P st files t)) :
    ¬ IsSendOverCap i := by
  rintro ⟨-, hgt⟩
  rw [heq.2.2.1] at hgt
  simp [pqInitInputsFRaw, pqInputs] at hgt

private theorem not_isStdinOverCap_of_inputsEquiv_pqInitInputsF {P : PEParams} {st : PqParty}
    {files : List (String × List (BitVec 8))} {t : List.Vector (BitVec 8) initiateTapeLen}
    {i : Inputs} (heq : InputsEquivRaw i (pqInitInputsFRaw P st files t)) :
    ¬ IsStdinOverCap i := by
  rintro ⟨-, hgt⟩
  rw [heq.2.2.1] at hgt
  simp [pqInitInputsFRaw, pqInputs, stdinCapBytes] at hgt

private theorem inner_length_le_of_pksmParse_pkToE {body : List (BitVec 8)}
    {pm : PreKeySignalMessage} {m : PreKeyMessageFields}
    (hparse : pksmParse body = some pm) (hpk : pkToE? pm = some m) :
    m.inner.length ≤ body.length := by
  have hm_inner : m.inner = pm.message.serialized := by
    unfold pkToE? at hpk
    split at hpk
    · cases hpk
    · split at hpk
      · cases hpk
      · split at hpk
        · cases hpk
        · injection hpk with hm
          exact (congrArg PreKeyMessageFields.inner hm).symm
  rw [hm_inner, pksmParse_inner_eq_decoded hparse]
  exact pksmDecodedInnerBytes_length_le body

private theorem normDjbKey_eq_djbKey {bs k : List (BitVec 8)} (h : normDjbKey bs = some k) :
    ∃ v : List.Vector (BitVec 8) 32, k = djbKey v := by
  cases bs with
  | nil => cases h
  | cons b rest =>
    dsimp only [normDjbKey] at h
    by_cases hc : b = 5#8 ∧ 32 ≤ rest.length
    · rw [ite_pos_local hc] at h
      injection h with hk
      exact ⟨⟨rest.take 32, by simp [hc.2]⟩, hk.symm⟩
    · rw [ite_neg_local hc] at h
      cases h

private theorem normKyberKey_eq_kyberKey {bs k : List (BitVec 8)} (h : normKyberKey bs = some k) :
    ∃ v : List.Vector (BitVec 8) 1568, k = kyberKey v := by
  cases bs with
  | nil => cases h
  | cons b rest =>
    dsimp only [normKyberKey] at h
    by_cases hc : b = 8#8 ∧ rest.length = 1568
    · rw [ite_pos_local hc] at h
      injection h with hk
      exact ⟨⟨rest, hc.2⟩, hk.symm⟩
    · rw [ite_neg_local hc] at h
      cases h

private theorem splitSigned_sig_len_local {bs : List (BitVec 8)} {id : BitVec 32}
    {key sig : List (BitVec 8)} (h : splitSigned bs = some (id, key, sig)) : sig.length = 64 := by
  unfold splitSigned at h
  cases hs : splitId bs with
  | none => rw [hs] at h; cases h
  | some p =>
    rcases p with ⟨_, rest⟩
    rw [hs] at h
    change (if 64 ≤ rest.length then some _ else none) = some _ at h
    by_cases hge : 64 ≤ rest.length
    · rw [ite_pos_local hge] at h
      injection h with hEq
      rcases Prod.mk.inj (Prod.mk.inj hEq).2 with ⟨_, rfl⟩
      simp only [List.length_drop]
      omega
    · rw [ite_neg_local hge] at h
      cases h

private theorem exists_publicBundleOf_of_parseBundleDir
    {d : String → Option (List (BitVec 8))} {dirName : String} {pb : PublicBundle}
    (hp : parseBundleDir d dirName = some pb) :
    ∃ b : PreKeyBundleFields, pb = publicBundleOf b := by
  unfold parseBundleDir at hp
  dsimp only [bind, Option.bind] at hp
  rcases hik : normDjbKey ((d (dirName ++ "/" ++ "identity-key")).getD []) with _ | idKey
  · rw [hik] at hp; cases hp
  rw [hik] at hp; dsimp only at hp
  obtain ⟨vId, rfl⟩ := normDjbKey_eq_djbKey hik
  rcases hreg : readU32LE ((d (dirName ++ "/" ++ "registration-id")).getD []) with _ | regId
  · rw [hreg] at hp; cases hp
  rw [hreg] at hp; dsimp only at hp
  rcases hspkS : splitSigned ((d (dirName ++ "/" ++ "signed-pre-key")).getD []) with _ | pSpk
  · rw [hspkS] at hp; cases hp
  rcases pSpk with ⟨spkId, spkKeyRaw, spkSig⟩
  rw [hspkS] at hp; dsimp only at hp
  rcases hspkN : normDjbKey spkKeyRaw with _ | spkKey
  · rw [hspkN] at hp; cases hp
  rw [hspkN] at hp; dsimp only at hp
  obtain ⟨vSpk, rfl⟩ := normDjbKey_eq_djbKey hspkN
  rcases hkpkS : splitSigned ((d (dirName ++ "/" ++ "kyber-pre-key")).getD []) with _ | pKpk
  · rw [hkpkS] at hp; cases hp
  rcases pKpk with ⟨kpkId, kpkKeyRaw, kpkSig⟩
  rw [hkpkS] at hp; dsimp only at hp
  rcases hkpkN : normKyberKey kpkKeyRaw with _ | kpkKey
  · rw [hkpkN] at hp; cases hp
  rw [hkpkN] at hp; dsimp only at hp
  obtain ⟨vKpk, rfl⟩ := normKyberKey_eq_kyberKey hkpkN
  by_cases hemp : ((d (dirName ++ "/" ++ "one-time-pre-key")).getD []).isEmpty = true
  · rw [ite_pos_local hemp] at hp
    dsimp only at hp
    injection hp with hpb
    exact ⟨{ regId := regId, opk := none, spkId := spkId, spkPub := vSpk,
             spkSig := ⟨spkSig, splitSigned_sig_len_local hspkS⟩,
             kpkId := kpkId, kpkPub := vKpk,
             kpkSig := ⟨kpkSig, splitSigned_sig_len_local hkpkS⟩,
             idPub := vId }, hpb.symm⟩
  · rw [ite_neg_local hemp] at hp
    rcases hopkS : splitId ((d (dirName ++ "/" ++ "one-time-pre-key")).getD []) with _ | pOpk
    · rw [hopkS] at hp; cases hp
    rcases pOpk with ⟨opkId, opkKeyRaw⟩
    rw [hopkS] at hp; dsimp only at hp
    rcases hopkN : normDjbKey opkKeyRaw with _ | opkKey
    · rw [hopkN] at hp; cases hp
    rw [hopkN] at hp; dsimp only at hp
    obtain ⟨vOpk, rfl⟩ := normDjbKey_eq_djbKey hopkN
    injection hp with hpb
    exact ⟨{ regId := regId, opk := some (opkId, vOpk), spkId := spkId, spkPub := vSpk,
             spkSig := ⟨spkSig, splitSigned_sig_len_local hspkS⟩,
             kpkId := kpkId, kpkPub := vKpk,
             kpkSig := ⟨kpkSig, splitSigned_sig_len_local hkpkS⟩,
             idPub := vId }, hpb.symm⟩

/-! ## 3. Main `V2F3StuckDomain` Ghost `MainCaseB2` Dispatcher -/

/-- Every input `i` in `V2F3StuckDomain ⟨W.C, W.Q⟩` satisfies `CliInputsOk i ∧ InputsLoadable i`
and admits a ghost Block-`617` `subroutine_ok` witness `Run` together with
`MainCaseB2 Run IsSendOverCap IsStdinOverCap i r`. -/
theorem v2F3StuckDomain_ghostMainCase_of_arms [LibsignalPlacement]
    {mpl mmpl : MultiPlacement}
    {EG : CliHooks → String → Option (State → State)}
    (h547 : mpl.base 547 ≠ 0#64)
    (hArms : GhostMainArmsFor mpl mmpl EG)
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
    {i : Inputs}
    (hDom : V2F3StuckDomain ⟨W.C, W.Q⟩ i) :
    CliInputsOk i ∧ InputsLoadable i ∧
    ∃ (Run : Inputs → RunAnswer → Prop) (r : MainResult),
      (∀ (γ : GhostName) (tp : BitVec 64),
        subroutine_ok
          (cliProgExtPlacedAt mpl EG 617 W)
          (mpl.base 617)
          (b2MainSpecTightNeedLocksFineAt (mallocngAddrsOfPlacement mmpl).libc
            (LibsignalFrozen mpl)
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
            cliBudgetLimits fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl)
            Run cliProcessInputs)) ∧
      MainCaseB2 Run IsSendOverCap IsStdinOverCap i r := by
  let WP : PEParams := ⟨W.C, W.Q⟩
  rcases hDom with hPq | hD3 | ⟨hInitDom, hload⟩
  · -- Arm 1: `CliPqxdhInputs WP i`
    obtain ⟨st, hst, hcases⟩ := hPq
    obtain ⟨RunMain, hSubMain, hClauses⟩ :=
      hArms.hmain h547 defaultExtrasF3 W hF hE hD hX hPub hF512 hEnc hDec hK
    obtain ⟨hInit, hSend, hWhisper, hPrekey, hBad⟩ := hClauses st hst
    rcases hcases with ⟨hnone, b, t, rfl⟩ | ⟨m, r, hm, rfl⟩ | ⟨c, rc, hc, rfl⟩ |
      ⟨m, rc, hm, rfl⟩ | ⟨c, rc, hc, h1, h2, rfl⟩
    · refine ⟨cliInputsOk_pqInitInputs WP st b t, inputsLoadable_pqInitInputs WP st b t hst, ?_⟩
      obtain ⟨a, hrun, _, hcommit⟩ := hInit b t hnone
      exact ⟨RunMain, MainResult.ofAnswer a, hSubMain,
        MainCaseB2.call hrun (not_isSendOverCap_pqInitInputs WP st b t)
          (not_isStdinOverCap_pqInitInputs WP st b t)
          (coinsReadable_pqInitInputs WP st b t) hcommit⟩
    · refine ⟨cliInputsOk_pqSendInputs WP st m r, inputsLoadable_pqSendInputs WP st m r hst, ?_⟩
      by_cases hstin : m.length > stdinCapBytes
      · exact ⟨RunMain, .ret 2 [] [], hSubMain,
          MainCaseB2.stdinOverCap (isStdinOverCap_pqSendInputs WP st m r hstin)⟩
      · have hnstin : ¬ IsStdinOverCap (pqSendInputs WP st m r) :=
          not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)
        by_cases hovc : m.length > maxPlaintextBytes
        · exact ⟨RunMain, .ret 1 [] [], hSubMain,
            MainCaseB2.sendOverCap
              (isSendOverCap_pqSendInputs WP st m r (by unfold maxPlaintextBytes at hovc; exact hovc))
              hnstin (coinsReadable_pqSendInputs WP st m r)⟩
        · obtain ⟨a, hrun, _, hcommit⟩ := hSend m r hm
          exact ⟨RunMain, MainResult.ofAnswer a, hSubMain,
            MainCaseB2.call hrun
              (not_isSendOverCap_of_stdin_le
                (by simp only [pqSendInputs, pqInputs]; unfold maxPlaintextBytes at hovc; omega))
              hnstin (coinsReadable_pqSendInputs WP st m r) hcommit⟩
    · refine ⟨cliInputsOk_pqRecvInputs WP st (wireWhisper :: c) rc,
        inputsLoadable_pqRecvInputs WP st (wireWhisper :: c) rc hst, ?_⟩
      by_cases hstin : (wireWhisper :: c).length > stdinCapBytes
      · exact ⟨RunMain, .ret 2 [] [], hSubMain,
          MainCaseB2.stdinOverCap (isStdinOverCap_pqRecvInputs WP st (wireWhisper :: c) rc hstin)⟩
      · obtain ⟨a, hrun, _, hcommit⟩ := hWhisper c rc hc
        exact ⟨RunMain, MainResult.ofAnswer a, hSubMain,
          MainCaseB2.call hrun (not_isSendOverCap_pqRecvInputs WP st (wireWhisper :: c) rc)
            (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin))
            (coinsReadable_pqRecvInputs WP st (wireWhisper :: c) rc) hcommit⟩
    · refine ⟨cliInputsOk_pqRecvInputs WP st (wirePrekey :: m.bytes) rc,
        inputsLoadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hst, ?_⟩
      by_cases hstin : (wirePrekey :: m.bytes).length > stdinCapBytes
      · exact ⟨RunMain, .ret 2 [] [], hSubMain,
          MainCaseB2.stdinOverCap (isStdinOverCap_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hstin)⟩
      · have hnstin : ¬ IsStdinOverCap (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) :=
          not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)
        have hnsend : ¬ IsSendOverCap (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) :=
          not_isSendOverCap_pqRecvInputs WP st (wirePrekey :: m.bytes) rc
        have hcoins : CoinsReadable (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) :=
          coinsReadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc
        rcases hsess : st.session with _ | ⟨x, g⟩
        · obtain ⟨a, hrun, _, hcommit⟩ :=
            hPrekey m rc hm (fun _ _ hs => nomatch hsess.symm.trans hs)
          exact ⟨RunMain, MainResult.ofAnswer a, hSubMain,
            MainCaseB2.call hrun hnsend hnstin hcoins hcommit⟩
        · by_cases hmEq : PqSessionMatches x g m
          · obtain ⟨a, hrun, _, hcommit⟩ := hPrekey m rc hm (fun x' g' hs => by
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hsess.symm.trans hs))
              exact hmEq)
            exact ⟨RunMain, MainResult.ofAnswer a, hSubMain,
              MainCaseB2.call hrun hnsend hnstin hcoins hcommit⟩
          · obtain ⟨RunOver, hSubOver, _, hOverCanon⟩ :=
              hArms.hoverD3 h547 defaultExtrasF3 W hF hE hD hX hPub hF512 hEnc hDec hK
            obtain ⟨a, hrun, _, hcommit⟩ := hOverCanon st hst x g hsess m rc hm hmEq
            exact ⟨RunOver, MainResult.ofAnswer a, hSubOver,
              MainCaseB2.call hrun hnsend hnstin hcoins hcommit⟩
    · refine ⟨cliInputsOk_pqRecvInputs WP st c rc,
        inputsLoadable_pqRecvInputs WP st c rc hst, ?_⟩
      by_cases hstin : c.length > stdinCapBytes
      · exact ⟨RunMain, .ret 2 [] [], hSubMain,
          MainCaseB2.stdinOverCap (isStdinOverCap_pqRecvInputs WP st c rc hstin)⟩
      · obtain ⟨a, hrun, _, hcommit⟩ := hBad c rc hc h1 h2
        exact ⟨RunMain, MainResult.ofAnswer a, hSubMain,
          MainCaseB2.call hrun (not_isSendOverCap_pqRecvInputs WP st c rc)
            (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin))
            (coinsReadable_pqRecvInputs WP st c rc) hcommit⟩
  · -- Arm 2: arbitrary pre-key `recv` payload `wirePrekey :: body`
    obtain ⟨st, body, rc, hst, rfl⟩ := hD3
    refine ⟨cliInputsOk_pqRecvInputs WP st (wirePrekey :: body) rc,
      inputsLoadable_pqRecvInputs WP st (wirePrekey :: body) rc hst, ?_⟩
    by_cases hstin : (wirePrekey :: body).length > stdinCapBytes
    · obtain ⟨RunMain, hSubMain, _⟩ :=
        hArms.hmain h547 defaultExtrasF3 W hF hE hD hX hPub hF512 hEnc hDec hK
      exact ⟨RunMain, .ret 2 [] [], hSubMain,
        MainCaseB2.stdinOverCap (isStdinOverCap_pqRecvInputs WP st (wirePrekey :: body) rc hstin)⟩
    · have hlen_cons : (wirePrekey :: body).length ≤ stdinCapBytes := Nat.le_of_not_gt hstin
      have hnstin : ¬ IsStdinOverCap (pqRecvInputs WP st (wirePrekey :: body) rc) :=
        not_isStdinOverCap_of_stdin_le hlen_cons
      have hnsend : ¬ IsSendOverCap (pqRecvInputs WP st (wirePrekey :: body) rc) :=
        not_isSendOverCap_pqRecvInputs WP st (wirePrekey :: body) rc
      have hcoins : CoinsReadable (pqRecvInputs WP st (wirePrekey :: body) rc) :=
        coinsReadable_pqRecvInputs WP st (wirePrekey :: body) rc
      have hbody_lt : body.length < 2 ^ 32 := by
        unfold stdinCapBytes at hlen_cons
        simp only [List.length_cons] at hlen_cons
        omega
      have hcons_le : (wirePrekey :: body).length ≤ 2 ^ 32 := by
        unfold stdinCapBytes at hlen_cons
        omega
      rcases hparse : pksmParse body with _ | pm
      · have hSub := hArms.huntyped h547 W hF hE hD hX hPub hF512 hEnc hDec hK
        obtain ⟨_, hrun, _, hcommit⟩ :=
          runRel_pqRecv_parseNone_of_runSem (S := cliRunSemD3 W) rfl rfl WP st hst body rc
            hbody_lt hparse
        exact ⟨pqD3ScopedRun WP (runRel (cliRunSemD3 W)), MainResult.ofAnswer (some none), hSub,
          MainCaseB2.call ⟨Or.inr ⟨st, wirePrekey :: body, rc, hst, rfl⟩, hrun⟩
            hnsend hnstin hcoins hcommit⟩
      · by_cases hpmMatch : ∃ x g, st.session = some (x, g) ∧ SessMatchesPm (d3PqSessionOf x g) pm
        · obtain ⟨x, g, hsess, hmPm⟩ := hpmMatch
          have hSub := hArms.hpathB h547 defaultExtrasF3 W hF hE hD hX hPub hF512 hEnc hDec hK
          obtain ⟨hrun, _, hcommit⟩ :=
            runRel_pqRecv_matchingPathB defaultExtrasF3 W st x g body pm rc hst hsess hcons_le
              hparse hmPm
          exact ⟨pqD3ScopedRun WP (runRel (cliRunSemPathB defaultExtrasF3 W)),
            MainResult.ofAnswer
              (runAns (cliRunSemPathB defaultExtrasF3 W) (pqRecvInputs WP st (wirePrekey :: body) rc)),
            hSub,
            MainCaseB2.call ⟨Or.inr ⟨st, wirePrekey :: body, rc, hst, rfl⟩, hrun⟩
              hnsend hnstin hcoins hcommit⟩
        · have hnoPm : ∀ x g, st.session = some (x, g) → ¬ SessMatchesPm (d3PqSessionOf x g) pm :=
            fun x g hs hm => hpmMatch ⟨x, g, hs, hm⟩
          rcases hpk : pkToE? pm with _ | m
          · have hSub := hArms.huntyped h547 W hF hE hD hX hPub hF512 hEnc hDec hK
            obtain ⟨hrun, _, hcommit⟩ :=
              runRel_pqRecv_untypedReject W st body pm rc hst hbody_lt hparse hpk hnoPm
            exact ⟨pqD3ScopedRun WP (runRel (cliRunSemD3 W)), MainResult.ofAnswer (some none), hSub,
              MainCaseB2.call ⟨Or.inr ⟨st, wirePrekey :: body, rc, hst, rfl⟩, hrun⟩
                hnsend hnstin hcoins hcommit⟩
          · have hinner_le : m.inner.length ≤ body.length :=
              inner_length_le_of_pksmParse_pkToE hparse hpk
            have hm_lt : m.inner.length + 2048 < 2 ^ 32 := by
              unfold stdinCapBytes at hlen_cons
              simp only [List.length_cons] at hlen_cons
              omega
            rcases hsess : st.session with _ | ⟨x, g⟩
            · obtain ⟨RunVm, hSubVm, hVm⟩ :=
                hArms.hvalidMatch h547 defaultExtrasF3 W hF hE hD hX hPub hF512 hEnc hDec hK
              obtain ⟨a, hrun, _, hcommit⟩ :=
                hVm st hst body pm m rc hbody_lt hparse hpk hm_lt
                  (fun _ _ hs => nomatch hsess.symm.trans hs)
              exact ⟨RunVm, MainResult.ofAnswer a, hSubVm,
                MainCaseB2.call hrun hnsend hnstin hcoins hcommit⟩
            · by_cases hmEq : PqSessionMatches x g m
              · obtain ⟨RunVm, hSubVm, hVm⟩ :=
                  hArms.hvalidMatch h547 defaultExtrasF3 W hF hE hD hX hPub hF512 hEnc hDec hK
                obtain ⟨a, hrun, _, hcommit⟩ :=
                  hVm st hst body pm m rc hbody_lt hparse hpk hm_lt (fun x' g' hs => by
                    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hsess.symm.trans hs))
                    exact hmEq)
                exact ⟨RunVm, MainResult.ofAnswer a, hSubVm,
                  MainCaseB2.call hrun hnsend hnstin hcoins hcommit⟩
              · obtain ⟨RunOver, hSubOver, hOverBody, _⟩ :=
                  hArms.hoverD3 h547 defaultExtrasF3 W hF hE hD hX hPub hF512 hEnc hDec hK
                obtain ⟨a, hrun, _, hcommit⟩ :=
                  hOverBody st hst x g hsess body pm m rc hbody_lt hparse hpk hm_lt hmEq
                exact ⟨RunOver, MainResult.ofAnswer a, hSubOver,
                  MainCaseB2.call hrun hnsend hnstin hcoins hcommit⟩
  · -- Arm 3: flat-bundle `init` (`CliInitD3Inputs WP i ∧ InputsLoadable i`)
    obtain ⟨st, files, t, hwf, hs, hb, heq⟩ := hInitDom
    refine ⟨cliInputsOk_of_inputsEquivRaw heq (cliInputsOk_pqInitInputsFRaw WP st files t),
      hload, ?_⟩
    obtain ⟨S, hS, hSubInit⟩ :=
      hArms.hinitSem h547 defaultExtrasF3 W hF hE hD hX hPub hF512 hEnc hDec hK
    have hnsend : ¬ IsSendOverCap i := not_isSendOverCap_of_inputsEquiv_pqInitInputsF heq
    have hnstin : ¬ IsStdinOverCap i := not_isStdinOverCap_of_inputsEquiv_pqInitInputsF heq
    have hcoins : CoinsReadable i := coinsReadable_of_inputsEquiv_pqInitInputsF heq
    by_cases hcap : BundleReadWithinCap (filesOf files) bundleDir
    · rcases hparse : parseBundleDir (filesOf files) bundleDir with _ | pb
      · obtain ⟨hrel, hcommit, _⟩ :=
          observe_reject_pqInitInputsFRaw_eq defaultExtrasF3 WP heq hwf hs hb hparse hS
        exact ⟨initD3ScopedRun WP (runRel S), MainResult.ofAnswer (runAns S i), hSubInit,
          MainCaseB2.call ⟨⟨st, files, t, hwf, hs, hb, heq⟩, hrel⟩ hnsend hnstin hcoins hcommit⟩
      · obtain ⟨b, rfl⟩ := exists_publicBundleOf_of_parseBundleDir hparse
        obtain ⟨hrel, hcommit, _⟩ :=
          observe_accept_pqInitInputsFRaw_eq defaultExtrasF3 WP heq hwf hs hb hcap hparse hS
        exact ⟨initD3ScopedRun WP (runRel S), MainResult.ofAnswer (runAns S i), hSubInit,
          MainCaseB2.call ⟨⟨st, files, t, hwf, hs, hb, heq⟩, hrel⟩ hnsend hnstin hcoins hcommit⟩
    · obtain ⟨hrel, hcommit, _⟩ :=
        observe_overCap_pqInitInputsFRaw_eq defaultExtrasF3 WP heq hwf hs hb hcap hS
      exact ⟨initD3ScopedRun WP (runRel S), MainResult.ofAnswer (runAns S i), hSubInit,
        MainCaseB2.call ⟨⟨st, files, t, hwf, hs, hb, heq⟩, hrel⟩ hnsend hnstin hcoins hcommit⟩

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDomainArms
