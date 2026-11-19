/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Refinement.Composed.Cli.ElfShaGuardBridgeBase
public import Symbolic.Proofs.Refinement.Composed.Cli.ModelB2 -- proof-setup: allow-public-import
import Symbolic.Proofs.Refinement.Composed.Cli.SDet.Defs
public import Symbolic.Proofs.Refinement.Composed.Cli.Transfer -- proof-setup: allow-public-import
import Symbolic.Proofs.Refinement.Composed.Cli.ParD3ModelV2SlotsBase
public import Symbolic.Proofs.Refinement.Composed.Cli.ParD3RpkSlot -- proof-setup: allow-public-import
import Symbolic.Proofs.Refinement.Composed.Cli.SDet.CodecInj
import Symbolic.Proofs.Refinement.Composed.Cli.SDet.FilesOfAlg
import Symbolic.Proofs.Refinement.Composed.Cli.SDet.InputsInj
import Symbolic.Proofs.Refinement.Composed.Cli.SDet.ModelCongr
public import Symbolic.Proofs.Swarm.CREF.Cli.DirInvBridge -- proof-setup: allow-public-import
import Symbolic.Proofs.Swarm.CREF.Cli.DirStepAux
import Symbolic.Proofs.Swarm.CREF.Cli.DirStepBridge
import Symbolic.Proofs.Swarm.CREF.Cli.ModelRel
import Symbolic.Proofs.Swarm.UA.Assembly
import Symbolic.Proofs.Swarm.UA.SlotInit
import Symbolic.Proofs.Swarm.UA.SlotRecvW
import Symbolic.Proofs.Swarm.UA.SlotRpkNO
import Symbolic.Proofs.Swarm.UA.SlotRpkProm
import Symbolic.Proofs.Swarm.UA.SlotSend
import Symbolic.Proofs.Swarm.UA.Top
import Symbolic.Proofs.Swarm.UA.XlateInv

/-!
# SHA-256 Domain-Guard Transfer for `PqModelPostB2`

Machine-free transfer of `PqModelPostB2` and `TraceInv` from `(withShaFInterp F₀ interp, withShaF F₀ P)`
back to `(interp, P)` along `PqTurnSim1A` and the per-call SHA-256 agreement guard `ShaAgreesOnInput`.
-/

public section

set_option autoImplicit false

namespace Symbolic.Proofs.Refinement.Composed.Cli.ElfShaGuardBridge

open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Composed.Refinement (
  ProtocolSetup ProtocolSetupWF parsePreKey
)
open DY.Libsignal.Composed.Refinement.Cli (
  BobCallAllowed BundleFilesFlat BundleReadWithinCapB2 CliCall CliTurn DirectorySnapshot
  ExternContractsHoldCli FilesVisible InputsEquiv InputsFor ModelAgree PqFieldsMatch
  PqModelPost PqModelPostB2 PqModelRel PqModelRelB2 ScrubAgree StdinBounded
  TraceInv ValidCall bundleReadNamesB2 coinsLen initDirs parseBundleFiles peerOf pqInitInputsF
  pqRecvMatchingFieldsModel preKeyOfBody? scrub
)
open DY.Libsignal.Composed.Refinement.Cli.ParD3 (
  PqTurnSim1A isScrubbedPath_of_bundleFilesFlat pqTurnSim1A_clearSession pqTurnSim1A_init
  regularFileList_of_bundleFilesFlat
)
open DY.Libsignal.Composed.Refinement.Cli.SDet (
  PqPartyEquiv inputsEquiv_pqSendInputs_extract
  pqInitModel_congr pqRecvPrekeyModel_congr pqRecvWhisperModel_congr pqSendModel_congr
  regularFileList_pqRecvInputs regularFileList_pqSendInputs
)
open CryptoGames.HMAC (ShaState keyToBytes32)
open CryptoGames.LibsignalSession (GhostState)
open CryptoVerification.E2E (
  PEParams PreKeyBundleFields PreKeyMessageFields RecordExtras UnreachedPqxdhPrimitives
  initiateTapeLen wirePrekey wireWhisper
)
open CryptoVerification.SignalSession (
  Inputs Outcome OutcomeMatchesModelExceptPath PqParty PqSessionMatches PqxdhPartyInSpecDomain
  bundleDir coinsFile encodeDir filesOf maxPlaintextBytes partyAddress pqInitInputs pqInitModel
  pqInputs pqRecvInputs pqRecvPrekeyModel pqRecvWhisperModel pqSendInputs pqSendModel
  pqxdhExpectedOutcome publicBundleOf sessionFile stdinCapBytes stdioPaths
)
open Symbolic.Swarm.CREF.Cli (
  IsScrubbedPath PqPartyInv RegularFileList bytesToVec_toList_of_len caller_pqPartyInv_of_allowed
  filesOf_append_of_regular filesOf_eq_none_of_forall_ne initDirs_interpOfParams
  inputsEquiv_pqInputs inputsEquiv_pqRecvInputs inputsEquiv_pqSendInputs interpOfParams
  isScrubbedPath_congr isScrubbedPath_encodeDir keyToBytes32_bytesToKey32
  peerOf_eq_addrE_other records_of_pqPartyInv regularFileList_encodeDir regularFile_root
  scrub_filesOf_pqInputs_reject wfPq_of_pqPartyInv
)
open Symbolic.Swarm.TRREF.SpqrSemOf (bytesToVec)
open Symbolic.Proofs.Refinement.Composed.Cli.ElfShaGuardBridgeBase (
  ShaAgreesOnInput encodeDir_withShaF externContractsHoldCli_withShaFInterp hwf_of_session_none
  initDirs_withShaFInterp modelAgree_withShaF noMatchSessionFile_transfer
  outcomeMatchesModelExceptPath_congr pqFieldsMatch_iff pqObserve_congr_local
  pqPartyEquiv_clearSession pqPartyEquiv_of_specDomain_pair pqPartyEquiv_symm
  pqRecvMatchingFieldsModel_congr_local pqSessionEquiv_symm validCall_withShaFInterp withShaF
  withShaFInterp
)

export Symbolic.Proofs.Refinement.Composed.Cli.ElfShaGuardBridgeBase (
  withShaF ShaAgreesOnInput withShaFInterp pqPartyEquiv_of_specDomain_pair pqPartyEquiv_of_weakWF
)

/-! ## Extracting `st₀` equivalence from `ValidCall` + `InputsFor` -/

private theorem cmd_is_send_of_argv {c : CliCall} {a : CryptoVerification.SignalSession.Address}
    (h : c.cmd.argv = ["send", a.text]) : ∃ peer, c.cmd = .send peer := by
  cases hm : c.cmd <;> rw [hm] at h <;> simp [CryptoVerification.SignalSession.Cmd.argv] at h
  exact ⟨_, rfl⟩

private theorem cmd_is_recv_of_argv {c : CliCall} {a : CryptoVerification.SignalSession.Address}
    (h : c.cmd.argv = ["recv", a.text]) : ∃ peer, c.cmd = .recv peer := by
  cases hm : c.cmd <;> rw [hm] at h <;> simp [CryptoVerification.SignalSession.Cmd.argv] at h
  exact ⟨_, rfl⟩

private theorem cmd_is_init_of_argv {c : CliCall} {a : CryptoVerification.SignalSession.Address}
    {dir : String} (h : c.cmd.argv = ["init", a.text, dir]) : ∃ peer d, c.cmd = .init peer d := by
  cases hm : c.cmd <;> rw [hm] at h <;> simp [CryptoVerification.SignalSession.Cmd.argv] at h
  exact ⟨_, _, rfl⟩

private theorem extract_send_of_validCall {F₀ : ShaState → HwBytes → ShaState}
    {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup} {t : CliTurn}
    {c : CliCall} {i : Inputs} {st st₀ : PqParty} {m : HwBytes}
    {coins : List.Vector (BitVec 8) 64}
    (hval : ValidCall interp r t c)
    (hin_enc : InputsFor c (filesOf (encodeDir (withShaF F₀ P) st₀)) i)
    (hpeer : peerOf r c.party = partyAddress st₀.party.other)
    (hwf : PqxdhPartyInSpecDomain P st)
    (hwf₀ : PqxdhPartyInSpecDomain (withShaF F₀ P) st₀)
    (heq : InputsEquiv i (pqSendInputs P st m coins)) :
    InputsEquiv i (pqSendInputs (withShaF F₀ P) st₀ m coins) ∧ PqPartyEquiv st st₀ := by
  let P₀ := withShaF F₀ P
  obtain ⟨peer, hcmd⟩ := cmd_is_send_of_argv (hin_enc.1.symm.trans heq.1)
  obtain ⟨hcoins, _, _, _, hguard⟩ := hval
  rw [hcmd] at hcoins hguard
  obtain ⟨_, rfl, hbun, _, _⟩ := hguard
  have hc64 : c.coins.length = 64 := by simpa [coinsLen] using hcoins
  let coinsVec : List.Vector (BitVec 8) 64 := bytesToVec 64 c.coins
  have heq₀_raw : InputsEquiv i (pqSendInputs P₀ st₀ c.stdin coinsVec) :=
    inputsEquiv_pqSendInputs hin_enc (by rw [hcmd, hpeer]) hbun
      (bytesToVec_toList_of_len hc64).symm
  have heq_P0 : InputsEquiv i (pqSendInputs P₀ st m coins) := heq
  obtain ⟨rfl, rfl, hfiles₀⟩ := inputsEquiv_pqSendInputs_extract (heq₀_raw.symm.trans heq_P0)
  exact ⟨heq₀_raw, pqPartyEquiv_of_specDomain_pair hwf hwf₀ (fun p => (hfiles₀ p).symm)⟩

private theorem extract_recv_of_validCall {F₀ : ShaState → HwBytes → ShaState}
    {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup} {t : CliTurn}
    {c : CliCall} {i : Inputs} {st st₀ : PqParty} {c_in : HwBytes} {rc : BitVec 256}
    (hval : ValidCall interp r t c)
    (hin_enc : InputsFor c (filesOf (encodeDir (withShaF F₀ P) st₀)) i)
    (hpeer : peerOf r c.party = partyAddress st₀.party.other)
    (hwf : PqxdhPartyInSpecDomain P st)
    (hwf₀ : PqxdhPartyInSpecDomain (withShaF F₀ P) st₀)
    (heq : InputsEquiv i (pqRecvInputs P st c_in rc)) :
    InputsEquiv i (pqRecvInputs (withShaF F₀ P) st₀ c_in rc) ∧ PqPartyEquiv st st₀ := by
  let P₀ := withShaF F₀ P
  obtain ⟨peer, hcmd⟩ := cmd_is_recv_of_argv (hin_enc.1.symm.trans heq.1)
  obtain ⟨hcoins, _, _, _, hguard⟩ := hval
  rw [hcmd] at hcoins hguard
  obtain ⟨_, rfl, hbun, _⟩ := hguard
  have hc32 : c.coins.length = 32 := by simpa [coinsLen] using hcoins
  let rc₀ : BitVec 256 := CryptoGames.HKDF.bytesToKey32 c.coins
  have heq₀_raw : InputsEquiv i (pqRecvInputs P₀ st₀ c.stdin rc₀) :=
    inputsEquiv_pqRecvInputs hin_enc (by rw [hcmd, hpeer]) hbun
      (keyToBytes32_bytesToKey32 hc32).symm
  have heq_P0 : InputsEquiv i (pqRecvInputs P₀ st c_in rc) := heq
  have htrans := heq₀_raw.symm.trans heq_P0
  have hstdin : c.stdin = c_in := htrans.2.2.1
  obtain ⟨hrc_bytes, hfiles₀⟩ := InputsInjAux.strip_coins_filesOf P₀ st₀ st
    (keyToBytes32 rc₀) (keyToBytes32 rc) htrans.2.2.2
  have hrc : rc₀ = rc := CodecInjAux.keyToBytes32_inj hrc_bytes
  subst hstdin; subst hrc
  exact ⟨heq₀_raw, pqPartyEquiv_of_specDomain_pair hwf hwf₀ (fun p => (hfiles₀ p).symm)⟩

/-! ## Transferring `PqModelPostB2` from `withShaF F₀ P` to `P` -/

private theorem pqInitInputs_withShaF (F₀ : ShaState → HwBytes → ShaState)
    (P : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    pqInitInputs (withShaF F₀ P) st b t = pqInitInputs P st b t :=
  rfl

private theorem pqInitInputsF_withShaF (F₀ : ShaState → HwBytes → ShaState)
    (P : PEParams) (st : PqParty) (files : List (String × HwBytes))
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    pqInitInputsF (withShaF F₀ P) st files t = pqInitInputsF P st files t :=
  rfl

private theorem pqSendInputs_withShaF (F₀ : ShaState → HwBytes → ShaState)
    (P : PEParams) (st : PqParty) (m : HwBytes) (coins : List.Vector (BitVec 8) 64) :
    pqSendInputs (withShaF F₀ P) st m coins = pqSendInputs P st m coins :=
  rfl

private theorem pqRecvInputs_withShaF (F₀ : ShaState → HwBytes → ShaState)
    (P : PEParams) (st : PqParty) (c_in : HwBytes) (rc : BitVec 256) :
    pqRecvInputs (withShaF F₀ P) st c_in rc = pqRecvInputs P st c_in rc :=
  rfl

private theorem pqxdhExpectedOutcome_withShaF (F₀ : ShaState → HwBytes → ShaState)
    (P : PEParams) (i : Inputs) (res : Option (Option (PqParty × HwBytes))) :
    pqxdhExpectedOutcome (withShaF F₀ P) i res = pqxdhExpectedOutcome P i res := by
  cases res with
  | none => rfl
  | some opt =>
    cases opt with
    | none => rfl
    | some p => rfl

private theorem outcomeMatchesModelExceptPath_withShaF (F₀ : ShaState → HwBytes → ShaState)
    (P : PEParams) (i : Inputs) (path : String)
    (res : Option (Option (PqParty × HwBytes))) (o : Outcome) :
    OutcomeMatchesModelExceptPath (withShaF F₀ P) i path res o =
      OutcomeMatchesModelExceptPath P i path res o := by
  cases res with
  | none => rfl
  | some opt =>
    cases opt with
    | none => rfl
    | some p => rfl

/-- Transfers `PqModelPostB2` from `(withShaFInterp F₀ interp, withShaF F₀ P)` back to
`(interp, P)` using `ValidCall`, `InputsFor`, and `ShaAgreesOnInput F₀ P i`. -/
theorem pqModelPostB2_of_shaF_and_guard {F₀ : ShaState → HwBytes → ShaState}
    {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup} {t : CliTurn}
    {c : CliCall} {i : Inputs} {o : Outcome} {st₀ : PqParty}
    (hval : ValidCall interp r t c)
    (hin_enc : InputsFor c (filesOf (encodeDir (withShaF F₀ P) st₀)) i)
    (hpeer : peerOf r c.party = partyAddress st₀.party.other)
    (hwf₀ : PqxdhPartyInSpecDomain (withShaF F₀ P) st₀)
    (hsha : ShaAgreesOnInput F₀ P i)
    (hpost₀ : PqModelPostB2 (withShaFInterp F₀ interp) (withShaF F₀ P) i o) :
    PqModelPostB2 interp P i o := by
  let P₀ := withShaF F₀ P
  refine
    { init := fun X st b tVec hwf hsess heq => by
        have hwf_P0 : PqxdhPartyInSpecDomain P₀ st :=
          hwf_of_session_none (encodeDir_withShaF F₀ P) hwf hsess
        have heq_P0 : InputsEquiv i (pqInitInputs P₀ st b tVec) :=
          (pqInitInputs_withShaF F₀ P st b tVec).symm ▸ heq
        have ho := hpost₀.init X st b tVec hwf_P0 hsess heq_P0
        have hmod := hsha.1 X st ((publicBundleOf b).files bundleDir) b tVec hwf hsess
          (Or.inl rfl) heq
        rw [pqxdhExpectedOutcome_withShaF, pqInitInputs_withShaF, ← hmod] at ho
        exact ho
      send := fun st m coins hwf hlen heq => by
        obtain ⟨heq₀, hst⟩ := extract_send_of_validCall hval hin_enc hpeer hwf hwf₀ heq
        have ho := hpost₀.send st₀ m coins hwf₀ hlen heq₀
        have hfiles_eq : filesOf (pqSendInputs P₀ st₀ m coins).files =
            filesOf (pqSendInputs P st m coins).files :=
          funext (heq₀.symm.trans heq).2.2.2
        have hob := pqObserve_congr_local P₀
          (regularFileList_pqSendInputs P₀ st₀ m coins)
          (regularFileList_pqSendInputs P₀ st m coins)
          (heq₀.symm.trans ((pqSendInputs_withShaF F₀ P st m coins).symm ▸ heq))
          (pqSendModel_congr P₀ (pqPartyEquiv_symm hst) m coins.toList)
        have hmod := hsha.2.1 st m coins hwf hlen heq
        rw [ho, hfiles_eq, hob, pqxdhExpectedOutcome_withShaF, pqSendInputs_withShaF, ← hmod]
      recvWhisper := fun st body rc hwf hlen heq => by
        obtain ⟨heq₀, hst⟩ := extract_recv_of_validCall hval hin_enc hpeer hwf hwf₀ heq
        have ho := hpost₀.recvWhisper st₀ body rc hwf₀ hlen heq₀
        have hfiles_eq : filesOf (pqRecvInputs P₀ st₀ (wireWhisper :: body) rc).files =
            filesOf (pqRecvInputs P st (wireWhisper :: body) rc).files :=
          funext (heq₀.symm.trans heq).2.2.2
        have hob := pqObserve_congr_local P₀
          (regularFileList_pqRecvInputs P₀ st₀ (wireWhisper :: body) rc)
          (regularFileList_pqRecvInputs P₀ st (wireWhisper :: body) rc)
          (heq₀.symm.trans ((pqRecvInputs_withShaF F₀ P st (wireWhisper :: body) rc).symm ▸ heq))
          (pqRecvWhisperModel_congr P₀ (pqPartyEquiv_symm hst) body rc)
        have hmod := hsha.2.2.1 st body rc hwf hlen heq
        rw [ho, hfiles_eq, hob, pqxdhExpectedOutcome_withShaF, pqRecvInputs_withShaF, ← hmod]
      recvPrekey := fun X st m rc hwf hlen hmatch heq => by
        obtain ⟨heq₀, hst⟩ := extract_recv_of_validCall hval hin_enc hpeer hwf hwf₀ heq
        have hmatch₀ : ∀ x₀ g₀, st₀.session = some (x₀, g₀) → PqSessionMatches x₀ g₀ m := by
          intro x₀ g₀ hs₀
          have hrel := hst.session_rel
          rw [hs₀] at hrel
          cases hs : st.session with
          | none => rw [hs] at hrel; cases hrel
          | some xg =>
            rcases xg with ⟨x, g⟩
            rw [hs] at hrel
            cases hrel with
            | some hse => exact (hse.matches_iff m).mp (hmatch x g hs)
        have ho := hpost₀.recvPrekey X st₀ m rc hwf₀ hlen hmatch₀ heq₀
        have hfiles_eq : filesOf (pqRecvInputs P₀ st₀ (wirePrekey :: m.bytes) rc).files =
            filesOf (pqRecvInputs P st (wirePrekey :: m.bytes) rc).files :=
          funext (heq₀.symm.trans heq).2.2.2
        have hob := pqObserve_congr_local P₀
          (regularFileList_pqRecvInputs P₀ st₀ (wirePrekey :: m.bytes) rc)
          (regularFileList_pqRecvInputs P₀ st (wirePrekey :: m.bytes) rc)
          (heq₀.symm.trans ((pqRecvInputs_withShaF F₀ P st (wirePrekey :: m.bytes) rc).symm ▸ heq))
          (pqRecvPrekeyModel_congr X P₀ (pqPartyEquiv_symm hst) m rc)
        have hmod := (hsha.2.2.2.1 X st m.bytes m rc hwf hlen (Or.inl rfl) heq).1 hmatch
        rw [ho, hfiles_eq, hob, pqxdhExpectedOutcome_withShaF, pqRecvInputs_withShaF, ← hmod]
      recvPrekeyNoMatch := fun X st x g m rc hwf hsess hlen hnm heq => by
        obtain ⟨heq₀, hst⟩ := extract_recv_of_validCall hval hin_enc hpeer hwf hwf₀ heq
        have hrel := hst.session_rel
        rw [hsess] at hrel
        cases hs₀ : st₀.session with
        | none => rw [hs₀] at hrel; cases hrel
        | some xg₀ =>
          rcases xg₀ with ⟨x₀, g₀⟩
          rw [hs₀] at hrel
          cases hrel with
          | some hse =>
            have hnm₀ : ¬ PqSessionMatches x₀ g₀ m :=
              fun h0 => hnm ((hse.matches_iff m).mpr h0)
            have ho := hpost₀.recvPrekeyNoMatch X st₀ x₀ g₀ m rc hwf₀ hs₀ hlen hnm₀ heq₀
            by_cases hgt : (wirePrekey :: m.bytes).length > stdinCapBytes
            · simp only [hgt, ↓reduceIte] at ho ⊢
              rw [ho]
              exact congrArg (Outcome.exited 2 []) (funext (heq₀.symm.trans heq).2.2.2)
            · simp only [hgt, ↓reduceIte] at ho ⊢
              have ho1 := outcomeMatchesModelExceptPath_congr P₀
                (regularFileList_pqRecvInputs P₀ st₀ (wirePrekey :: m.bytes) rc)
                (regularFileList_pqRecvInputs P₀ st (wirePrekey :: m.bytes) rc)
                (heq₀.symm.trans ((pqRecvInputs_withShaF F₀ P st (wirePrekey :: m.bytes) rc).symm ▸ heq))
                (pqRecvPrekeyModel_congr X P₀ (pqPartyEquiv_clearSession (pqPartyEquiv_symm hst)) m rc)
                ho
              have hmod := (hsha.2.2.2.1 X st m.bytes m rc hwf hlen (Or.inl rfl) heq).2 x g hsess hnm
              have hpath : sessionFile (partyAddress st₀.party.other) =
                  sessionFile (partyAddress st.party.other) := by rw [hst.party_eq]
              have ho2 : OutcomeMatchesModelExceptPath P
                  (pqRecvInputs P st (wirePrekey :: m.bytes) rc)
                  (sessionFile (partyAddress st₀.party.other))
                  (pqRecvPrekeyModel X P { st with session := none } m rc) o := by
                dsimp only [P₀] at ho1
                rwa [outcomeMatchesModelExceptPath_withShaF F₀ P,
                     pqRecvInputs_withShaF F₀ P, ← hmod] at ho1
              exact hpath ▸ ho2
      recvOther := fun st c_in rc hwf hlen hw hp heq => by
        obtain ⟨heq₀, _⟩ := extract_recv_of_validCall hval hin_enc hpeer hwf hwf₀ heq
        have ho := hpost₀.recvOther st₀ c_in rc hwf₀ hlen hw hp heq₀
        have hfiles_eq : filesOf (pqRecvInputs P₀ st₀ c_in rc).files =
            filesOf (pqRecvInputs P st c_in rc).files :=
          funext (heq₀.symm.trans heq).2.2.2
        rw [ho, hfiles_eq]
      recvPrekeyNoMatchSession := fun X st x g m rc hwf hsess hlen hcap hnm heq => by
        obtain ⟨heq₀, hst⟩ := extract_recv_of_validCall hval hin_enc hpeer hwf hwf₀ heq
        have hrel := hst.session_rel
        rw [hsess] at hrel
        cases hs₀ : st₀.session with
        | none => rw [hs₀] at hrel; cases hrel
        | some xg₀ =>
          rcases xg₀ with ⟨x₀, g₀⟩
          rw [hs₀] at hrel
          cases hrel with
          | some hse =>
            have hnm₀ : ¬ PqSessionMatches x₀ g₀ m :=
              fun h0 => hnm ((hse.matches_iff m).mpr h0)
            have ho := hpost₀.recvPrekeyNoMatchSession X st₀ x₀ g₀ m rc hwf₀ hs₀ hlen hcap hnm₀ heq₀
            have hmod := (hsha.2.2.2.1 X st m.bytes m rc hwf hlen (Or.inl rfl) heq).2 x g hsess hnm
            exact noMatchSessionFile_transfer X hst hse hmod ho
      recvOverStdinCap := fun st body rc hwf hlen hgt heq => by
        obtain ⟨heq₀, _⟩ := extract_recv_of_validCall hval hin_enc hpeer hwf hwf₀ heq
        have ho := hpost₀.recvOverStdinCap st₀ body rc hwf₀ hlen hgt heq₀
        rw [ho]
        exact congrArg (Outcome.exited 2 []) (funext (heq₀.symm.trans heq).2.2.2)
      recvPrekeyReject := fun st body rc hwf hlen hcap hnone heq => by
        obtain ⟨heq₀, _⟩ := extract_recv_of_validCall hval hin_enc hpeer hwf hwf₀ heq
        have ho := hpost₀.recvPrekeyReject st₀ body rc hwf₀ hlen hcap hnone heq₀
        rw [ho]
        exact congrArg (Outcome.exited 1 []) (funext (heq₀.symm.trans heq).2.2.2)
      recvPrekeyUntyped := fun st body q rc hwf hlen hcap hq hnone hnm heq => by
        obtain ⟨heq₀, hst⟩ := extract_recv_of_validCall hval hin_enc hpeer hwf hwf₀ heq
        have hnm₀ : ∀ x₀ g₀, st₀.session = some (x₀, g₀) → ¬ PqFieldsMatch x₀ g₀ q := by
          intro x₀ g₀ hs₀ hfm₀
          have hrel := hst.session_rel
          rw [hs₀] at hrel
          cases hs : st.session with
          | none => rw [hs] at hrel; cases hrel
          | some xg =>
            rcases xg with ⟨x, g⟩
            rw [hs] at hrel
            cases hrel with
            | some hse => exact hnm x g hs ((pqFieldsMatch_iff hse q).mpr hfm₀)
        have ho := hpost₀.recvPrekeyUntyped st₀ body q rc hwf₀ hlen hcap hq hnone hnm₀ heq₀
        rw [ho]
        exact congrArg (Outcome.exited 1 []) (funext (heq₀.symm.trans heq).2.2.2)
      recvPrekeyMatching := fun st x g body q rc hwf hsess hlen hcap hq hfm heq => by
        obtain ⟨heq₀, hst⟩ := extract_recv_of_validCall hval hin_enc hpeer hwf hwf₀ heq
        have hrel := hst.session_rel
        rw [hsess] at hrel
        cases hs₀ : st₀.session with
        | none => rw [hs₀] at hrel; cases hrel
        | some xg₀ =>
          rcases xg₀ with ⟨x₀, g₀⟩
          rw [hs₀] at hrel
          cases hrel with
          | some hse =>
            have hfm₀ : PqFieldsMatch x₀ g₀ q := (pqFieldsMatch_iff hse q).mp hfm
            have ho := hpost₀.recvPrekeyMatching st₀ x₀ g₀ body q rc hwf₀ hs₀ hlen hcap hq hfm₀ heq₀
            have hob := pqObserve_congr_local P₀
              (regularFileList_pqRecvInputs P₀ st₀ (wirePrekey :: body) rc)
              (regularFileList_pqRecvInputs P₀ st (wirePrekey :: body) rc)
              (heq₀.symm.trans ((pqRecvInputs_withShaF F₀ P st (wirePrekey :: body) rc).symm ▸ heq))
              (pqRecvMatchingFieldsModel_congr_local P₀ (pqPartyEquiv_symm hst)
                (pqSessionEquiv_symm hse) q rc)
            have hmod := hsha.2.2.2.2 st x g body q rc hwf hsess hlen hq hfm heq
            rw [ho, hob, pqxdhExpectedOutcome_withShaF, pqRecvInputs_withShaF, ← hmod]
      recvPrekeyParsed := fun X st body m rc hwf hlen hcap hm hinner hmatch heq => by
        obtain ⟨heq₀, hst⟩ := extract_recv_of_validCall hval hin_enc hpeer hwf hwf₀ heq
        have hmatch₀ : ∀ x₀ g₀, st₀.session = some (x₀, g₀) → PqSessionMatches x₀ g₀ m := by
          intro x₀ g₀ hs₀
          have hrel := hst.session_rel
          rw [hs₀] at hrel
          cases hs : st.session with
          | none => rw [hs] at hrel; cases hrel
          | some xg =>
            rcases xg with ⟨x, g⟩
            rw [hs] at hrel
            cases hrel with
            | some hse => exact (hse.matches_iff m).mp (hmatch x g hs)
        have ho := hpost₀.recvPrekeyParsed X st₀ body m rc hwf₀ hlen hcap hm hinner hmatch₀ heq₀
        have hob := pqObserve_congr_local P₀
          (regularFileList_pqRecvInputs P₀ st₀ (wirePrekey :: body) rc)
          (regularFileList_pqRecvInputs P₀ st (wirePrekey :: body) rc)
          (heq₀.symm.trans ((pqRecvInputs_withShaF F₀ P st (wirePrekey :: body) rc).symm ▸ heq))
          (pqRecvPrekeyModel_congr X P₀ (pqPartyEquiv_symm hst) m rc)
        have hmod := (hsha.2.2.2.1 X st body m rc hwf hinner (Or.inr ⟨hlen, hm⟩) heq).1 hmatch
        rw [ho, hob, pqxdhExpectedOutcome_withShaF, pqRecvInputs_withShaF, ← hmod]
      recvPrekeyParsedNoMatch := fun X st x g body m rc hwf hsess hlen hcap hm hinner hnm heq => by
        obtain ⟨heq₀, hst⟩ := extract_recv_of_validCall hval hin_enc hpeer hwf hwf₀ heq
        have hrel := hst.session_rel
        rw [hsess] at hrel
        cases hs₀ : st₀.session with
        | none => rw [hs₀] at hrel; cases hrel
        | some xg₀ =>
          rcases xg₀ with ⟨x₀, g₀⟩
          rw [hs₀] at hrel
          cases hrel with
          | some hse =>
            have hnm₀ : ¬ PqSessionMatches x₀ g₀ m :=
              fun h0 => hnm ((hse.matches_iff m).mpr h0)
            obtain ⟨ho_om, ho_nm⟩ :=
              hpost₀.recvPrekeyParsedNoMatch X st₀ x₀ g₀ body m rc hwf₀ hs₀ hlen hcap hm hinner hnm₀ heq₀
            have hmod := (hsha.2.2.2.1 X st body m rc hwf hinner (Or.inr ⟨hlen, hm⟩) heq).2 x g hsess hnm
            refine ⟨?_, noMatchSessionFile_transfer X hst hse hmod ho_nm⟩
            have ho1 := outcomeMatchesModelExceptPath_congr P₀
              (regularFileList_pqRecvInputs P₀ st₀ (wirePrekey :: body) rc)
              (regularFileList_pqRecvInputs P₀ st (wirePrekey :: body) rc)
              (heq₀.symm.trans ((pqRecvInputs_withShaF F₀ P st (wirePrekey :: body) rc).symm ▸ heq))
              (pqRecvPrekeyModel_congr X P₀ (pqPartyEquiv_clearSession (pqPartyEquiv_symm hst)) m rc)
              ho_om
            have hpath : sessionFile (partyAddress st₀.party.other) =
                sessionFile (partyAddress st.party.other) := by rw [hst.party_eq]
            have ho2 : OutcomeMatchesModelExceptPath P
                (pqRecvInputs P st (wirePrekey :: body) rc)
                (sessionFile (partyAddress st₀.party.other))
                (pqRecvPrekeyModel X P { st with session := none } m rc) o := by
              dsimp only [P₀] at ho1
              rwa [outcomeMatchesModelExceptPath_withShaF F₀ P,
                   pqRecvInputs_withShaF F₀ P, ← hmod] at ho1
            exact hpath ▸ ho2
      initFiles := fun X st files b tVec hwf hsess hflat hcap hparse heq => by
        have hwf_P0 : PqxdhPartyInSpecDomain P₀ st :=
          hwf_of_session_none (encodeDir_withShaF F₀ P) hwf hsess
        have heq_P0 : InputsEquiv i (pqInitInputsF P₀ st files tVec) :=
          (pqInitInputsF_withShaF F₀ P st files tVec).symm ▸ heq
        have ho := hpost₀.initFiles X st files b tVec hwf_P0 hsess hflat hcap hparse heq_P0
        have hmod := hsha.1 X st files b tVec hwf hsess (Or.inr ⟨hflat, hparse⟩) heq
        rwa [pqxdhExpectedOutcome_withShaF F₀ P, pqInitInputsF_withShaF F₀ P, ← hmod] at ho
      initOverFileCap := fun st files tVec hwf hsess hflat hover heq => by
        have hwf_P0 : PqxdhPartyInSpecDomain P₀ st :=
          hwf_of_session_none (encodeDir_withShaF F₀ P) hwf hsess
        have heq_P0 : InputsEquiv i (pqInitInputsF P₀ st files tVec) :=
          (pqInitInputsF_withShaF F₀ P st files tVec).symm ▸ heq
        have ho := hpost₀.initOverFileCap st files tVec hwf_P0 hsess hflat hover heq_P0
        rwa [pqInitInputsF_withShaF F₀ P] at ho
      initReject := fun st files tVec hwf hsess hflat hparse heq => by
        have hwf_P0 : PqxdhPartyInSpecDomain P₀ st :=
          hwf_of_session_none (encodeDir_withShaF F₀ P) hwf hsess
        have heq_P0 : InputsEquiv i (pqInitInputsF P₀ st files tVec) :=
          (pqInitInputsF_withShaF F₀ P st files tVec).symm ▸ heq
        have ho := hpost₀.initReject st files tVec hwf_P0 hsess hflat hparse heq_P0
        rwa [pqInitInputsF_withShaF F₀ P] at ho }

/-! ## Within-cap / above-cap stepping of `PqTurnSim1A` and `TraceInv` -/

@[expose] def CallWithinCap (c : CliCall) : Prop :=
  match c.cmd with
  | .init _ _ => BundleReadWithinCapB2 (filesOf c.bundle) bundleDir
  | .send _ => c.stdin.length ≤ maxPlaintextBytes
  | .recv _ => c.stdin.length ≤ stdinCapBytes

instance (c : CliCall) : Decidable (CallWithinCap c) := by
  unfold CallWithinCap; cases c.cmd <;> infer_instance

private theorem maxPlaintextBytes_le_stdinCapBytes : maxPlaintextBytes ≤ stdinCapBytes := by
  decide

private theorem bundleReadName_props {name : String} (hm : name ∈ bundleReadNamesB2) :
    (bundleDir ++ "/" ++ name) ∉ stdioPaths ∧
    IsScrubbedPath (bundleDir ++ "/" ++ name) = true ∧
    Arm64.normalizePath (bundleDir ++ "/" ++ name) ≠ Arm64.normalizePath coinsFile := by
  simp only [bundleReadNamesB2, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide, by decide⟩

private theorem filesOf_encodeDir_bundle_none (P : PEParams) (st : PqParty) {p : String}
    (hscr : IsScrubbedPath p = true) :
    filesOf (encodeDir P st) p = none :=
  filesOf_eq_none_of_forall_ne (regularFileList_encodeDir P st) fun f hf heq => by
    have := (isScrubbedPath_congr heq).symm.trans hscr
    rw [isScrubbedPath_encodeDir P st f hf] at this; cases this

private theorem filesOf_extra_bundle_eq {bundle : List (String × HwBytes)}
    (hflat : BundleFilesFlat bundle) (coins : HwBytes) {p : String}
    (hne : Arm64.normalizePath p ≠ Arm64.normalizePath coinsFile) :
    filesOf (bundle ++ [(coinsFile, coins)]) p = filesOf bundle p := by
  have hreg_b : RegularFileList bundle := regularFileList_of_bundleFilesFlat hflat
  have hreg_c : RegularFileList [(coinsFile, coins)] :=
    regularFile_root (by decide) (by decide) (by decide) (by decide)
  rw [filesOf_append_of_regular hreg_b hreg_c p]
  have hc_none : filesOf [(coinsFile, coins)] p = none :=
    filesOf_eq_none_of_forall_ne hreg_c fun f hf heq => by
      rcases List.mem_singleton.mp hf with rfl
      exact hne heq
  simp [hc_none]

private theorem filesOf_pqInitInputsF_bundle_eq (P : PEParams) (st : PqParty)
    {files : List (String × HwBytes)} (hflat : BundleFilesFlat files)
    (t : List.Vector (BitVec 8) initiateTapeLen) {name : String} (hm : name ∈ bundleReadNamesB2) :
    filesOf (pqInitInputsF P st files t).files (bundleDir ++ "/" ++ name) =
      filesOf files (bundleDir ++ "/" ++ name) := by
  obtain ⟨_, hscr, hne⟩ := bundleReadName_props hm
  have hreg_f : RegularFileList files := regularFileList_of_bundleFilesFlat hflat
  have hreg_c : RegularFileList [(coinsFile, t.toList)] :=
    regularFile_root (by decide) (by decide) (by decide) (by decide)
  change filesOf (encodeDir P st ++ files ++ [(coinsFile, t.toList)]) _ = _
  rw [List.append_assoc,
      filesOf_append_of_regular (regularFileList_encodeDir P st) (hreg_f.append hreg_c),
      filesOf_extra_bundle_eq hflat t.toList hne,
      filesOf_encodeDir_bundle_none P st hscr, Option.or_none]

theorem pqModelPost_of_b2_withinCap {interp : ExternInterpretation} {P : PEParams}
    {r : ProtocolSetup} {t : CliTurn} {c : CliCall} {i : Inputs} {o : Outcome}
    {st₀ : PqParty}
    (hnext : ValidCall interp r t c)
    (hin : InputsFor c (t.dirs c.party) i)
    (hdir₀ : t.dirs c.party = filesOf (encodeDir P st₀))
    (hcap : CallWithinCap c)
    (hpost : PqModelPostB2 interp P i o) :
    PqModelPost interp P i o where
  init := hpost.init
  send := fun st m coins hwf hlen heq => by
    obtain ⟨peer, hcmd⟩ := cmd_is_send_of_argv (hin.1.symm.trans heq.1)
    have hm_eq : m = c.stdin := heq.2.2.1.symm.trans hin.2.2.1
    have hle_pt : m.length ≤ maxPlaintextBytes := by
      rw [hm_eq]; simpa [CallWithinCap, hcmd] using hcap
    have hle_sc : m.length ≤ stdinCapBytes := Nat.le_trans hle_pt maxPlaintextBytes_le_stdinCapBytes
    have hs := hpost.send st m coins hwf hlen heq
    simp only [Nat.not_lt.mpr hle_sc, Nat.not_lt.mpr hle_pt, ↓reduceIte] at hs
    exact hs
  recvWhisper := fun st body rc hwf hlen heq => by
    obtain ⟨peer, hcmd⟩ := cmd_is_recv_of_argv (hin.1.symm.trans heq.1)
    have hst_eq : (wireWhisper :: body) = c.stdin := heq.2.2.1.symm.trans hin.2.2.1
    have hle : (wireWhisper :: body).length ≤ stdinCapBytes := by
      rw [hst_eq]; simpa [CallWithinCap, hcmd] using hcap
    have hs := hpost.recvWhisper st body rc hwf hlen heq
    simp only [Nat.not_lt.mpr hle, ↓reduceIte] at hs
    exact hs
  recvPrekey := fun X st m rc hwf hlen hmatch heq => by
    obtain ⟨peer, hcmd⟩ := cmd_is_recv_of_argv (hin.1.symm.trans heq.1)
    have hst_eq : (wirePrekey :: m.bytes) = c.stdin := heq.2.2.1.symm.trans hin.2.2.1
    have hle : (wirePrekey :: m.bytes).length ≤ stdinCapBytes := by
      rw [hst_eq]; simpa [CallWithinCap, hcmd] using hcap
    have hs := hpost.recvPrekey X st m rc hwf hlen hmatch heq
    simp only [Nat.not_lt.mpr hle, ↓reduceIte] at hs
    exact hs
  recvPrekeyNoMatch := fun X st x g m rc hwf hsess hlen hnm heq => by
    obtain ⟨peer, hcmd⟩ := cmd_is_recv_of_argv (hin.1.symm.trans heq.1)
    have hst_eq : (wirePrekey :: m.bytes) = c.stdin := heq.2.2.1.symm.trans hin.2.2.1
    have hle : (wirePrekey :: m.bytes).length ≤ stdinCapBytes := by
      rw [hst_eq]; simpa [CallWithinCap, hcmd] using hcap
    have hs := hpost.recvPrekeyNoMatch X st x g m rc hwf hsess hlen hnm heq
    simp only [Nat.not_lt.mpr hle, ↓reduceIte] at hs
    exact hs
  recvOther := fun st c_in rc hwf hlen hw hp heq => by
    obtain ⟨peer, hcmd⟩ := cmd_is_recv_of_argv (hin.1.symm.trans heq.1)
    have hst_eq : c_in = c.stdin := heq.2.2.1.symm.trans hin.2.2.1
    have hle : c_in.length ≤ stdinCapBytes := by
      rw [hst_eq]; simpa [CallWithinCap, hcmd] using hcap
    have hs := hpost.recvOther st c_in rc hwf hlen hw hp heq
    simp only [Nat.not_lt.mpr hle, ↓reduceIte] at hs
    exact hs
  recvPrekeyNoMatchSession := fun X st x g m rc hwf hsess hlen hnm heq => by
    obtain ⟨peer, hcmd⟩ := cmd_is_recv_of_argv (hin.1.symm.trans heq.1)
    have hst_eq : (wirePrekey :: m.bytes) = c.stdin := heq.2.2.1.symm.trans hin.2.2.1
    have hle : (wirePrekey :: m.bytes).length ≤ stdinCapBytes := by
      rw [hst_eq]; simpa [CallWithinCap, hcmd] using hcap
    exact hpost.recvPrekeyNoMatchSession X st x g m rc hwf hsess hlen hle hnm heq
  recvPrekeyReject := fun st body rc hwf hlen hnone heq => by
    obtain ⟨peer, hcmd⟩ := cmd_is_recv_of_argv (hin.1.symm.trans heq.1)
    have hst_eq : (wirePrekey :: body) = c.stdin := heq.2.2.1.symm.trans hin.2.2.1
    have hle : (wirePrekey :: body).length ≤ stdinCapBytes := by
      rw [hst_eq]; simpa [CallWithinCap, hcmd] using hcap
    exact hpost.recvPrekeyReject st body rc hwf hlen hle hnone heq
  recvPrekeyUntyped := fun st body q rc hwf hlen hq hnone hnm heq => by
    obtain ⟨peer, hcmd⟩ := cmd_is_recv_of_argv (hin.1.symm.trans heq.1)
    have hst_eq : (wirePrekey :: body) = c.stdin := heq.2.2.1.symm.trans hin.2.2.1
    have hle : (wirePrekey :: body).length ≤ stdinCapBytes := by
      rw [hst_eq]; simpa [CallWithinCap, hcmd] using hcap
    exact hpost.recvPrekeyUntyped st body q rc hwf hlen hle hq hnone hnm heq
  recvPrekeyMatching := fun st x g body q rc hwf hsess hlen hq hfm heq => by
    obtain ⟨peer, hcmd⟩ := cmd_is_recv_of_argv (hin.1.symm.trans heq.1)
    have hst_eq : (wirePrekey :: body) = c.stdin := heq.2.2.1.symm.trans hin.2.2.1
    have hle : (wirePrekey :: body).length ≤ stdinCapBytes := by
      rw [hst_eq]; simpa [CallWithinCap, hcmd] using hcap
    exact hpost.recvPrekeyMatching st x g body q rc hwf hsess hlen hle hq hfm heq
  recvPrekeyParsed := fun X st body m rc hwf hlen hm hinner hmatch heq => by
    obtain ⟨peer, hcmd⟩ := cmd_is_recv_of_argv (hin.1.symm.trans heq.1)
    have hst_eq : (wirePrekey :: body) = c.stdin := heq.2.2.1.symm.trans hin.2.2.1
    have hle : (wirePrekey :: body).length ≤ stdinCapBytes := by
      rw [hst_eq]; simpa [CallWithinCap, hcmd] using hcap
    exact hpost.recvPrekeyParsed X st body m rc hwf hlen hle hm hinner hmatch heq
  recvPrekeyParsedNoMatch := fun X st x g body m rc hwf hsess hlen hm hinner hnm heq => by
    obtain ⟨peer, hcmd⟩ := cmd_is_recv_of_argv (hin.1.symm.trans heq.1)
    have hst_eq : (wirePrekey :: body) = c.stdin := heq.2.2.1.symm.trans hin.2.2.1
    have hle : (wirePrekey :: body).length ≤ stdinCapBytes := by
      rw [hst_eq]; simpa [CallWithinCap, hcmd] using hcap
    exact hpost.recvPrekeyParsedNoMatch X st x g body m rc hwf hsess hlen hle hm hinner hnm heq
  initFiles := fun X st files b tVec hwf hsess hflat hparse heq => by
    obtain ⟨peer, d, hcmd⟩ := cmd_is_init_of_argv (hin.1.symm.trans heq.1)
    have hguard := hnext.2.2.2.2
    rw [hcmd] at hguard
    have hflat_c : BundleFilesFlat c.bundle := hguard.2.2.2.2.2.1
    have hcap_c : BundleReadWithinCapB2 (filesOf c.bundle) bundleDir := by
      simpa [CallWithinCap, hcmd] using hcap
    have hcap_f : BundleReadWithinCapB2 (filesOf files) bundleDir := by
      intro name hm
      obtain ⟨hns, hscr, hne_coins⟩ := bundleReadName_props hm
      have hi_eq := hin.2.2.2.1 (bundleDir ++ "/" ++ name) hns
      rw [hdir₀, filesOf_encodeDir_bundle_none P st₀ hscr, Option.or_none,
          CliCall.extra, filesOf_extra_bundle_eq hflat_c c.coins hne_coins] at hi_eq
      have hf_eq := (heq.2.2.2 (bundleDir ++ "/" ++ name)).symm.trans hi_eq
      rw [filesOf_pqInitInputsF_bundle_eq P st hflat tVec hm] at hf_eq
      rw [hf_eq]
      exact hcap_c name hm
    exact hpost.initFiles X st files b tVec hwf hsess hflat hcap_f hparse heq
  initReject := hpost.initReject

private theorem after_eq_self_of_ne_zero {r : ProtocolSetup} {t : CliTurn} {c : CliCall}
    {code : Nat} {out : HwBytes} {files : DirectorySnapshot}
    (hne : code ≠ 0) (hscr : scrub files = t.dirs c.party) :
    t.after r c code out files = t := by
  rcases t with ⟨dirs, sent, bobOff⟩
  cases code with
  | zero => exact absurd rfl hne
  | succ _ =>
    cases c.cmd <;>
      (dsimp only [CliTurn.after]; congr 1
       · funext q; split_ifs with hq <;> [exact hq ▸ hscr; rfl]
       · exact List.append_nil sent
       · simp)

theorem caller_st_of_validCall {interp : ExternInterpretation} {P : PEParams}
    {r : ProtocolSetup} {t t_clean : CliTurn} {accepted : List HwBytes} {c : CliCall}
    (hr : ProtocolSetupWF r)
    (hsim : PqTurnSim1A (interpOfParams interp P) P r t t_clean accepted)
    (hnext : ValidCall interp r t c) :
    (c.party = r.alice ∨ c.party = r.bob) ∧
    ∃ st₀, PqPartyInv (interpOfParams interp P) P r accepted c.party st₀ (t.dirs c.party) ∧
      PqxdhPartyInSpecDomain P st₀ := by
  obtain ⟨_, _, hfb, hbca, hguard⟩ := hnext
  have hp : c.party = r.alice ∨ c.party = r.bob := by
    cases hm : c.cmd <;> rw [hm] at hguard
    · exact Or.inl hguard.1
    · exact hguard.1
    · exact hguard.1
  have hd_eq : t_clean.dirs c.party = t.dirs c.party := by
    rcases hp with ha | hb
    · exact ha ▸ hsim.dirs_other r.alice hr.1
    · have hoff : t.bobOff = false := by
        cases hbo : t.bobOff with
        | false => rfl
        | true => exact absurd hb (hbca hbo)
      rw [hsim.bobOff_false_eq hoff]
  have hbca_clean : BobCallAllowed r t_clean c := fun hbo =>
    absurd (hsim.clean_bobOff.symm.trans hbo) Bool.false_ne_true
  obtain ⟨_, st₀, hst_clean⟩ := caller_pqPartyInv_of_allowed hsim.dirInv hbca_clean hp
  have hst₀ : PqPartyInv (interpOfParams interp P) P r accepted c.party st₀ (t.dirs c.party) :=
    hd_eq ▸ hst_clean
  exact ⟨hp, st₀, hst₀, wfPq_of_pqPartyInv hst₀ hfb⟩

theorem aboveCap_after_eq_self {interp : ExternInterpretation} {P : PEParams}
    {r : ProtocolSetup} {t t_clean : CliTurn} {accepted : List HwBytes}
    {c : CliCall} {i : Inputs} {code : Nat} {out : HwBytes} {files : DirectorySnapshot}
    (hr : ProtocolSetupWF r)
    (hsim : PqTurnSim1A (interpOfParams interp P) P r t t_clean accepted)
    (hnext : ValidCall interp r t c)
    (hin : InputsFor c (t.dirs c.party) i)
    (hnot_cap : ¬ CallWithinCap c)
    (hpost : PqModelPostB2 interp P i (.exited code out files)) :
    t.after r c code out files = t := by
  obtain ⟨_, st₀, hst₀, hwf₀⟩ := caller_st_of_validCall hr hsim hnext
  obtain ⟨hcoins, hsb, _, _, hguard⟩ := hnext
  have hpeer : peerOf r c.party = partyAddress st₀.party.other := by
    rw [peerOf_eq_addrE_other, ← hst₀.party_eq]
  have hin_enc : InputsFor c (filesOf (encodeDir P st₀)) i := hst₀.dir_eq ▸ hin
  have hex_rej : (code = 1 ∨ code = 2) ∧ out = [] ∧ scrub files = t.dirs c.party := by
    cases hm : c.cmd with
    | init peer dir =>
      rw [hm] at hcoins hguard
      obtain ⟨hal, rfl, rfl, hstdin, hrec_none, hflat, _⟩ := hguard
      have hcap' : ¬ BundleReadWithinCapB2 (filesOf c.bundle) bundleDir := by
        simpa [CallWithinCap, hm] using hnot_cap
      have hsess : st₀.session = none := by
        have hrec := records_of_pqPartyInv hst₀
        rw [hal, hrec_none] at hrec
        cases hs : st₀.session <;> simp [hs] at hrec
        rfl
      have hc192 : c.coins.length = initiateTapeLen := by simpa [coinsLen, initiateTapeLen] using hcoins
      let tVec : List.Vector (BitVec 8) initiateTapeLen := bytesToVec initiateTapeLen c.coins
      have htVec : tVec.toList = c.coins := bytesToVec_toList_of_len hc192
      have hcmd_st : c.cmd = .init (partyAddress st₀.party.other) bundleDir := by
        rw [hm, ← hal, hpeer]
      have heq : InputsEquiv i (pqInitInputsF P st₀ c.bundle tVec) := by
        unfold pqInitInputsF; rw [← hcmd_st, htVec, ← hstdin]
        exact inputsEquiv_pqInputs hin_enc (regularFileList_of_bundleFilesFlat hflat) rfl
      have ho := hpost.initOverFileCap st₀ c.bundle tVec hwf₀ hsess hflat hcap' heq
      injection ho with hc hout hfs
      refine ⟨Or.inl hc, hout, ?_⟩
      rw [hfs, hst₀.dir_eq]
      exact scrub_filesOf_pqInputs_reject P st₀ _ c.bundle tVec.toList []
        (regularFileList_of_bundleFilesFlat hflat) (isScrubbedPath_of_bundleFilesFlat hflat)
    | send peer =>
      rw [hm] at hcoins hguard
      obtain ⟨_, rfl, hbun, _, _⟩ := hguard
      have hsb' : c.stdin.length < 2 ^ 32 := by simpa [StdinBounded, hm] using hsb
      have hgt_pt : c.stdin.length > maxPlaintextBytes :=
        Nat.lt_of_not_ge (by simpa [CallWithinCap, hm] using hnot_cap)
      have hc64 : c.coins.length = 64 := by simpa [coinsLen] using hcoins
      let coinsVec : List.Vector (BitVec 8) 64 := bytesToVec 64 c.coins
      have heq : InputsEquiv i (pqSendInputs P st₀ c.stdin coinsVec) :=
        inputsEquiv_pqSendInputs hin_enc (by rw [hm, hpeer]) hbun (bytesToVec_toList_of_len hc64).symm
      have ho := hpost.send st₀ c.stdin coinsVec hwf₀ hsb' heq
      have hscr0 : scrub (filesOf (pqSendInputs P st₀ c.stdin coinsVec).files) = t.dirs c.party := by
        rw [hst₀.dir_eq]
        exact scrub_filesOf_pqInputs_reject P st₀ _ [] coinsVec.toList c.stdin
          (fun _ h => by cases h) (fun _ h => by cases h)
      by_cases hgt_sc : c.stdin.length > stdinCapBytes
      · simp only [hgt_sc, ↓reduceIte] at ho
        injection ho with hc hout hfs
        exact ⟨Or.inr hc, hout, hfs ▸ hscr0⟩
      · simp only [hgt_sc, hgt_pt, ↓reduceIte] at ho
        injection ho with hc hout hfs
        exact ⟨Or.inl hc, hout, hfs ▸ hscr0⟩
    | recv peer =>
      rw [hm] at hcoins hguard
      obtain ⟨_, rfl, hbun, _⟩ := hguard
      have hgt_sc : c.stdin.length > stdinCapBytes :=
        Nat.lt_of_not_ge (by simpa [CallWithinCap, hm] using hnot_cap)
      have hc32 : c.coins.length = 32 := by simpa [coinsLen] using hcoins
      let rc : BitVec 256 := CryptoGames.HKDF.bytesToKey32 c.coins
      have heq : InputsEquiv i (pqRecvInputs P st₀ c.stdin rc) :=
        inputsEquiv_pqRecvInputs hin_enc (by rw [hm, hpeer]) hbun (keyToBytes32_bytesToKey32 hc32).symm
      have hscr0 : scrub (filesOf (pqRecvInputs P st₀ c.stdin rc).files) = t.dirs c.party := by
        rw [hst₀.dir_eq]
        exact scrub_filesOf_pqInputs_reject P st₀ _ [] (keyToBytes32 rc) c.stdin
          (fun _ h => by cases h) (fun _ h => by cases h)
      cases hst_in : c.stdin with
      | nil =>
        rw [hst_in] at hgt_sc
        exact absurd hgt_sc (by decide)
      | cons b0 body =>
        by_cases hbw : b0 = wireWhisper
        · subst hbw
          have htag : wireWhisper = wireWhisperTag := rfl
          have hbody_lt : body.length < 2 ^ 32 := by
            unfold StdinBounded at hsb; rw [hm] at hsb
            exact hsb.1 body (hst_in.trans (by rw [htag]))
          rw [hst_in] at heq hgt_sc hscr0
          have ho := hpost.recvWhisper st₀ body rc hwf₀ hbody_lt heq
          simp only [hgt_sc, ↓reduceIte] at ho
          injection ho with hc hout hfs
          exact ⟨Or.inr hc, hout, hfs ▸ hscr0⟩
        · by_cases hbp : b0 = wirePrekey
          · subst hbp
            have hnot_w : (wirePrekey :: body).head? ≠ some wireWhisperTag := by
              intro h; injection h with h; revert h; decide
            have hlen_lt : (wirePrekey :: body).length < 2 ^ 32 := by
              unfold StdinBounded at hsb; rw [hm, hst_in] at hsb
              exact hsb.2.1 hnot_w
            rw [hst_in] at heq hgt_sc hscr0
            have ho := hpost.recvOverStdinCap st₀ body rc hwf₀ hlen_lt hgt_sc heq
            injection ho with hc hout hfs
            exact ⟨Or.inr hc, hout, hfs ▸ hscr0⟩
          · have hnot_w : (b0 :: body).head? ≠ some wireWhisperTag := fun h =>
              hbw (Option.some.inj h)
            have hlen_lt : (b0 :: body).length < 2 ^ 32 := by
              unfold StdinBounded at hsb; rw [hm, hst_in] at hsb
              exact hsb.2.1 hnot_w
            rw [hst_in] at heq hgt_sc hscr0
            have ho := hpost.recvOther st₀ (b0 :: body) rc hwf₀ hlen_lt
              (fun h => hbw (Option.some.inj h)) (fun h => hbp (Option.some.inj h)) heq
            simp only [hgt_sc, ↓reduceIte] at ho
            injection ho with hc hout hfs
            exact ⟨Or.inr hc, hout, hfs ▸ hscr0⟩
  obtain ⟨hc12, _, hscr⟩ := hex_rej
  have hne : code ≠ 0 := by rcases hc12 with rfl | rfl <;> decide
  exact after_eq_self_of_ne_zero hne hscr

/-- Constructs a `TraceInv` from any SHA-guarded run relation `(fun i o => Rel₀ i o ∧ ShaAgreesOnInput F₀ P i)`
to `PqModelRelB2 interp P`, maintaining `PqTurnSim1A` at `(withShaFInterp F₀ interp, withShaF F₀ P)`. -/
theorem traceInv_of_shaF_postB2 (F₀ : ShaState → HwBytes → ShaState)
    {Rel₀ : Inputs → Option Outcome → Prop}
    {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup}
    (hext : ExternContractsHoldCli interp)
    (hagree : ModelAgree interp P)
    (hr : ProtocolSetupWF r)
    (hpost_real : ∀ {i code out files},
      FilesVisible i.files →
      Rel₀ i (some (.exited code out files)) →
      PqModelPostB2 (withShaFInterp F₀ interp) (withShaF F₀ P) i (.exited code out files)) :
    ∃ I : CliTurn → Prop,
      I (CliTurn.init (initDirs interp r)) ∧
      TraceInv (fun i o => Rel₀ i o ∧ ShaAgreesOnInput F₀ P i) (PqModelRelB2 interp P) interp r I := by
  let interp₀ := withShaFInterp F₀ interp
  let P₀ := withShaF F₀ P
  have hext₀ : ExternContractsHoldCli interp₀ := externContractsHoldCli_withShaFInterp F₀ hext
  have hagree₀ : ModelAgree interp₀ P₀ := modelAgree_withShaF F₀ hagree
  let I : CliTurn → Prop := fun t =>
    ∃ t_clean₀ accepted₀, PqTurnSim1A (interpOfParams interp₀ P₀) P₀ r t t_clean₀ accepted₀
  have hinit : I (CliTurn.init (initDirs interp r)) := by
    refine ⟨CliTurn.init (initDirs (interpOfParams interp₀ P₀) r), [], ?_⟩
    have hd1 : initDirs interp r = initDirs interp₀ r := (initDirs_withShaFInterp F₀ interp r).symm
    have hd2 : initDirs interp₀ r = initDirs (interpOfParams interp₀ P₀) r :=
      congrFun (initDirs_interpOfParams interp₀ P₀).symm r
    rw [hd1, hd2]
    exact pqTurnSim1A_init hr hagree₀
  refine ⟨I, hinit, ?_⟩
  exact
    { clear := fun t p ⟨t_clean₀, accepted₀, hsim₀⟩ =>
        ⟨t_clean₀.clearSession r p, accepted₀, pqTurnSim1A_clearSession p hr hsim₀⟩
      step := fun t c i code out files ⟨t_clean₀, accepted₀, hsim₀⟩ hval hin ⟨hRel₀, hsha⟩ => by
        have hval₀ : ValidCall interp₀ r t c := (validCall_withShaFInterp F₀ interp r t c).mpr hval
        have hpost₀ : PqModelPostB2 interp₀ P₀ i (.exited code out files) :=
          hpost_real hin.2.2.2.2 hRel₀
        obtain ⟨_, st₀, hst₀, hwf₀⟩ := caller_st_of_validCall hr hsim₀ hval₀
        have hpeer : peerOf r c.party = partyAddress st₀.party.other := by
          rw [peerOf_eq_addrE_other, ← hst₀.party_eq]
        have hin_enc : InputsFor c (filesOf (encodeDir P₀ st₀)) i := hst₀.dir_eq ▸ hin
        have hpostP : PqModelPostB2 interp P i (.exited code out files) :=
          pqModelPostB2_of_shaF_and_guard hval hin_enc hpeer hwf₀ hsha hpost₀
        refine ⟨Or.inr ⟨.exited code out files, rfl, hpostP⟩, ?_⟩
        by_cases hcap : CallWithinCap c
        · have hpost1 : PqModelPost interp₀ P₀ i (.exited code out files) :=
            pqModelPost_of_b2_withinCap hval₀ hin hst₀.dir_eq hcap hpost₀
          have hRel1 : PqModelRel interp₀ P₀ i (some (.exited code out files)) :=
            PqModelRel.of_post hpost1
          obtain ⟨t_clean', accepted', hsim', _⟩ :=
            Symbolic.Proofs.Swarm.UA.Assembly.uaSlot_dispatch
              Symbolic.Proofs.Swarm.UA.SlotInit.slot_init_ua
              Symbolic.Proofs.Swarm.UA.SlotSend.slot_send_ua
              (Symbolic.Proofs.Swarm.UA.SlotRecvW.slot_recvw_ua_of
                Symbolic.Proofs.Swarm.UA.XlateInv.xlate_inv
                Symbolic.Proofs.Swarm.UA.Top.xlate_exc_w)
              Symbolic.Proofs.Swarm.UA.SlotRpkNO.slot_rpk_no_ua
              (Symbolic.Proofs.Swarm.UA.SlotRpkProm.slot_rpk_prom_ua_of_exc_w
                Symbolic.Proofs.Swarm.UA.Top.xlate_exc_w)
              interp₀ P₀ r hext₀ hagree₀ hr (evs_pre := []) hsim₀ hval₀ hin hRel1
          exact ⟨t_clean', accepted', hsim'⟩
        · have hafter := aboveCap_after_eq_self hr hsim₀ hval₀ hin hcap hpost₀
          exact ⟨t_clean₀, accepted₀, hafter.symm ▸ hsim₀⟩
      stop := fun _ _ _ o _ _ _ _ habort =>
        ⟨o, Or.inl (Or.inl habort), habort⟩ }

end Symbolic.Proofs.Refinement.Composed.Cli.ElfShaGuardBridge
