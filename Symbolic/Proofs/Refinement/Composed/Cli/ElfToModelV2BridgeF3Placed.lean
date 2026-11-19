/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.E2E.Record.Support.Phi
public import LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomSpecF3 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.ElfInputsExtF3
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Run
import Symbolic.Proofs.Refinement.Composed.Cli.BundleInitElfF3Placed
public import Symbolic.Proofs.Refinement.Composed.Cli.Model -- proof-setup: allow-public-import
public import Symbolic.Proofs.Refinement.Composed.Cli.ModelB2 -- proof-setup: allow-public-import
import Symbolic.Proofs.Refinement.Composed.Cli.PksmParseEquiv
public import Symbolic.Proofs.Refinement.Composed.Cli.Transfer -- proof-setup: allow-public-import
public import Symbolic.Specifications.Refinement.ElfBinding
public import Symbolic.Proofs.SpecLemmas.ElfBindingPlaced -- proof-setup: allow-public-import
public import Symbolic.Specifications.Refinement.Statement
import LibsignalBinary.Proofs.SignalSession.Cli.D3.PreKeyGeneralAux
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Model
import Symbolic.Proofs.Refinement.Composed.Cli.ElfRealGuardBridge

/-!
# Whole-Process ELF to Guarded Model Refinement Bridge

Discharges all 16 clauses of `PqModelPostB2` on exited runs of a two-placement
`CliPqBinaryV2OomF3Placed` ELF image and transfers `CompRefinesCliModelB2` to
`CompRefinesCliBinaryPlacedAt` and `CompRefinesCliBinaryPlaced`.
-/

public section

set_option autoImplicit false

namespace Symbolic.Proofs.Refinement.Composed.Cli.ElfToModelV2BridgeF3Placed

open Arm64.Obj (MultiPlacement)
open Arm64.Process (ElfImage)
open CryptoProofLib.Refinement (ExternInterpretation)
open DY (Participant)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement (
  PreKeyFields ProtocolSetup decodePreKey parsePreKey vec32
)
open DY.Libsignal.Composed.Refinement.Cli (
  CompRefinesCliBinaryPlaced CompRefinesCliBinaryPlacedAt CompRefinesCliModelB2 CompRefinesCliR
  DirectorySnapshot FilesVisible HooksMatchInterpretation HooksMatchPlaced InputsEquiv ModelAgree
  PqFieldsMatch PqModelPostB2 PqModelRelB2 ScrubAgree TraceInv compRefinesCliR_of_inv elfRelPlaced
  pqRecvMatchingFieldsModel preKeyOfBody?
)
open Symbolic.Proofs.Refinement.Composed.Cli (
  decodePreKey_eq_map_decodeProto pksmParse_parsePreKey_cases protoToPreKeyMsg
)
open CryptoGames.LibsignalSession (
  GhostState IdentityKey PublicKey SessionState SignalMessage currentVersion preKyberVersion
)
open CryptoGames.LibsignalSessionApi (PreKeySignalMessage)
open CryptoVerification.E2E (
  PEParams PreKeyBundleFields UnreachedPqxdhPrimitives initiateTapeLen wirePrekey wireWhisper
)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.SignalSession (
  CliHooks Inputs LoadablePath Outcome
  OutcomeOrExcusedAbort PqParty cliProcessInputs filesOf libsignalSessionLib loadable_pqInitInputs
  loadable_pqRecvInputs loadable_pqSendInputs pqInitInputs pqRecvInputs pqSendInputs
)
open LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced (CliReachesOOMPlaced)
open LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced.Placed (cliRunPlacedSig)
open CryptoVerification.SignalSession.Cli.RunProofs (SessMatchesPm pkToE? pkVecTag?)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (decodeProto kyberOk pksmParse)
open LibsignalBinary.Proofs.SignalSession.Cli.D3 (
  d3PqRecvMatchingModel d3PqSessionOf kyberPayload_isSome_of_pksmParse_v4
  version_three_or_four_of_pksmParse_some
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomSpecF3 (
  CliPqBinaryV2OomF3Placed LibsignalCliPqBinaryV2OomF3Placed LibsignalCliPqBinaryV2OomF3PlacedAt
)
open LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.ElfInputsExtF3 (
  ExcLoadOk exited_of_or_none_outcomeUpTo_eq_raw_placed exited_of_outcomeUpTo_raw_placed
  filesVisibleRaw_pqInitInputs filesVisibleRaw_pqRecvInputs filesVisibleRaw_pqSendInputs
)
open Symbolic.Proofs.Refinement.Composed.Cli.BundleInitElfF3Placed (
  outcomeUpTo_pqInitFiles_exact_or_none_of_f3_inputsEquiv
  outcomeUpTo_pqInitOverCap_or_none_of_f3_inputsEquiv
  outcomeUpTo_pqInitReject_or_none_of_f3_inputsEquiv
  scrubAgree_of_eq
)
open VerifiedLibraries (mallocngLib)

/-! ## Pre-key parser equivalence -/

private theorem hooksAgree_iff_modelAgree_f3 (interp : ExternInterpretation) (W : CliHooks) :
    HooksMatchInterpretation interp W ↔ ModelAgree interp ⟨W.C, W.Q⟩ :=
  Iff.rfl

private theorem filesVisible_pqInitInputs_f3 (P : PEParams) (st : PqParty)
    (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen) :
    LibsignalBinary.Proofs.SignalSession.Cli.Parity.FilesVisibleRaw
      (pqInitInputs P st b t).files :=
  filesVisibleRaw_pqInitInputs P st b t

private theorem filesVisible_pqSendInputs_f3 (P : PEParams) (st : PqParty) (m : HwBytes)
    (r : List.Vector (BitVec 8) 64) :
    LibsignalBinary.Proofs.SignalSession.Cli.Parity.FilesVisibleRaw
      (pqSendInputs P st m r).files :=
  filesVisibleRaw_pqSendInputs P st m r

private theorem filesVisible_pqRecvInputs_f3 (P : PEParams) (st : PqParty) (c : HwBytes)
    (rc : BitVec 256) :
    LibsignalBinary.Proofs.SignalSession.Cli.Parity.FilesVisibleRaw
      (pqRecvInputs P st c rc).files :=
  filesVisibleRaw_pqRecvInputs P st c rc

private theorem vec32_drop1_of_take33_eq_f3 {b : HwBytes} {v : List.Vector (BitVec 8) 32}
    (h : b.take 33 = 5#8 :: v.toList) :
    vec32 (b.drop 1) = v := by
  rcases v with ⟨l, hl_v⟩
  cases b with
  | nil => cases h
  | cons _ rest =>
    dsimp only [List.Vector.toList] at h
    have hrest : rest.take 32 = l := (List.cons.inj h).2
    have hlen : 32 ≤ rest.length := by
      have hl := congrArg List.length hrest
      rw [List.length_take, hl_v] at hl
      omega
    have heq : (rest ++ List.replicate 32 0#8).take 32 = l := by
      rw [List.take_append_of_le_length hlen, hrest]
    dsimp only [List.drop_succ_cons, List.drop_zero, vec32]
    exact Subtype.ext heq

private theorem decodeProto_drop1_of_pksmParse_some_f3 {body : HwBytes}
    {pm : PreKeySignalMessage} (h : pksmParse body = some pm) :
    ∃ m,
      decodeProto (body.drop 1) = some m ∧
        pm.registrationId = m.registrationId.getD 0#32 := by
  cases body with
  | nil => simp [pksmParse] at h
  | cons vb rest =>
    unfold pksmParse at h
    dsimp only [List.drop_succ_cons, List.drop_zero] at h ⊢
    by_cases hver : (vb >>> 4) < preKyberVersion ∨ currentVersion < (vb >>> 4)
    · simp [hver] at h
    · simp only [hver, ↓reduceIte] at h
      rcases hdec : decodeProto rest with _ | m
      · simp [hdec] at h
      rw [hdec] at h
      rcases hbk : m.baseKey with _ | bk
      · simp [hbk] at h
      rcases hik : m.identityKey with _ | ik
      · simp [hbk, hik] at h
      rcases hmsg : m.message with _ | msg
      · simp [hbk, hik, hmsg] at h
      rcases hsid : m.signedPreKeyId with _ | sid
      · simp [hbk, hik, hmsg, hsid] at h
      simp only [hbk, hik, hmsg, hsid] at h
      cases hkyb : kyberOk (vb >>> 4) m
      · simp [hkyb] at h
      simp only [hkyb, ↓reduceIte] at h
      rcases h1 : PublicKey.deserialize bk with _ | baseKey
      · simp [h1] at h
      rcases h2 : PublicKey.deserialize ik with _ | idKey
      · simp [h1, h2] at h
      rcases h3 : SignalMessage.tryFrom protoSignalCodec msg with _ | inner
      · simp [h1, h2, h3] at h
      simp only [h1, h2, h3, Option.some.injEq] at h
      subst h
      exact ⟨m, hdec, rfl⟩

private theorem bv8_toNat_eq_four_iff_f3 (v : BitVec 8) :
    v.toNat = 4 ↔ v = 4#8 := by
  constructor
  · intro h
    exact BitVec.eq_of_toNat_eq (by simpa using h)
  · rintro rfl
    rfl

private theorem preKeyOfBody?_eq_pksmParse_bind_pkToE?_f3 (body : HwBytes) :
    preKeyOfBody? body = (pksmParse body).bind pkToE? := by
  rcases pksmParse_parsePreKey_cases body with ⟨hpm, hq⟩ | ⟨pm, q, hpm, hq, ha⟩
  · simp [preKeyOfBody?, hpm, hq]
  · obtain ⟨m, hdec, hreg⟩ := decodeProto_drop1_of_pksmParse_some_f3 hpm
    have hraw : decodePreKey (body.drop 1) = some (protoToPreKeyMsg m) := by
      rw [decodePreKey_eq_map_decodeProto, hdec]
      rfl
    unfold preKeyOfBody?
    rw [hq, hraw, hpm]
    dsimp only [Option.bind]
    by_cases hv4 : pm.messageVersion = 4#8
    · have hqv4 : q.version = 4 := ha.version_eq.trans (by rw [hv4]; rfl)
      obtain ⟨kp, hkp⟩ := kyberPayload_isSome_of_pksmParse_v4 hpm hv4
      have hkid : q.kyberPreKeyId = some kp.preKeyId := by
        rw [ha.kyberPreKeyId_eq, hkp]
        rfl
      have hkct : q.kyberCiphertext = some kp.ciphertext := by
        rw [ha.kyberCiphertext_eq, hkp]
        rfl
      have hbk : vec32 (q.baseKey.drop 1) = pm.baseKey.bytes :=
        vec32_drop1_of_take33_eq_f3 ha.baseKey_take33_eq
      have hik : vec32 (q.identityKey.drop 1) = pm.identityKey.publicKey.bytes :=
        vec32_drop1_of_take33_eq_f3 ha.identityKey_take33_eq
      have hrhs : pkToE? pm =
          match pkVecTag? 8#8 1568 kp.ciphertext with
          | none => none
          | some ct =>
            some { regId := pm.registrationId, opkId := pm.preKeyId, spkId := pm.signedPreKeyId,
                   kpkId := kp.preKeyId, kyberCt := ct, baseKey := pm.baseKey.bytes,
                   idPub := pm.identityKey.publicKey.bytes, inner := pm.message.serialized } := by
        unfold pkToE?
        rw [hv4, hkp]
        rfl
      rw [hqv4, hkid, hkct, hrhs]
      simp only [↓reduceIte]
      cases kp.ciphertext with
      | nil => rfl
      | cons t ct =>
        dsimp only [pkVecTag?]
        have hreg' : (protoToPreKeyMsg m).registrationId.getD 0 = pm.registrationId :=
          hreg.symm
        rw [hreg', ha.preKeyId_eq, ha.signedPreKeyId_eq, hbk, hik, ha.message_serialized_eq]
        split <;> rfl
    · have hqv4 : q.version ≠ 4 := by
        rw [ha.version_eq]
        exact fun h => hv4 ((bv8_toNat_eq_four_iff_f3 pm.messageVersion).mp h)
      unfold pkToE?
      simp [hqv4, hv4]

private theorem pqFieldsMatch_iff_sessMatchesPm_f3 (x : CryptoVerification.E2E.RecordExtras)
    (g : GhostState HwBytes) {body : HwBytes} {q : PreKeyFields} {pm : PreKeySignalMessage}
    (hq : parsePreKey body = some q) (hpm : pksmParse body = some pm) :
    PqFieldsMatch x g q ↔ SessMatchesPm (d3PqSessionOf x g) pm := by
  rcases pksmParse_parsePreKey_cases body with ⟨hnone, _⟩ | ⟨pm', q', hpm', hq', ha⟩
  · rw [hpm] at hnone
    cases hnone
  · cases hpm.symm.trans hpm'
    cases hq.symm.trans hq'
    unfold PqFieldsMatch SessMatchesPm d3PqSessionOf
    dsimp only
    rw [ha.baseKey_take33_eq, ha.version_eq, and_comm]
    refine and_congr_left' ?_
    rcases version_three_or_four_of_pksmParse_some hpm with hv | hv <;>
      rw [hv] <;>
      unfold SessionState.version
    · split
      · next h0 => rw [h0]; decide
      · exact ⟨fun h => BitVec.eq_of_toNat_eq (by simpa using h), fun h => by rw [h]; rfl⟩
    · split
      · next h0 => rw [h0]; decide
      · exact ⟨fun h => BitVec.eq_of_toNat_eq (by simpa using h), fun h => by rw [h]; rfl⟩

private theorem pqRecvMatchingFieldsModel_eq_pqRecvMatchingModel_f3 (P : PEParams)
    (st : PqParty) (x : CryptoVerification.E2E.RecordExtras) (g : GhostState HwBytes)
    {body : HwBytes} {q : PreKeyFields} {pm : PreKeySignalMessage} (rc : BitVec 256)
    (hq : parsePreKey body = some q) (hpm : pksmParse body = some pm) :
    pqRecvMatchingFieldsModel P st x g q rc = d3PqRecvMatchingModel P st x g pm rc := by
  rcases pksmParse_parsePreKey_cases body with ⟨hnone, _⟩ | ⟨pm', q', hpm', hq', ha⟩
  · rw [hpm] at hnone
    cases hnone
  · cases hpm.symm.trans hpm'
    cases hq.symm.trans hq'
    have hik : (⟨⟨vec32 (q.identityKey.drop 1)⟩⟩ : IdentityKey) = pm.identityKey := by
      rcases pm with ⟨_, _, _, _, _, _, ⟨⟨ikBytes⟩⟩, _, _⟩
      exact congrArg (fun v => (⟨⟨v⟩⟩ : IdentityKey))
        (vec32_drop1_of_take33_eq_f3 ha.identityKey_take33_eq)
    unfold pqRecvMatchingFieldsModel d3PqRecvMatchingModel
    rw [hik, ha.inner_eq]
    rfl

/-! ## Input extensionality for `cliRunPlacedSig` -/

theorem exited_of_outcomeUpTo_f3 {mpl mmpl : MultiPlacement} {elf : ElfImage} {W : CliHooks}
    {exc : Inputs → Prop} {i i₀ : Inputs} {Pred : Outcome → Prop}
    {code : Nat} {out : HwBytes} {files : DirectorySnapshot}
    (hr : cliRunPlacedSig mpl mmpl elf W i = some (.exited code out files))
    (hup : OutcomeOrExcusedAbort exc (cliRunPlacedSig mpl mmpl elf W) i₀ Pred)
    (heq : InputsEquiv i i₀) (hvis : FilesVisible i.files) (hvis₀ : FilesVisible i₀.files)
    (hload₀ : ∀ f ∈ i₀.files, LoadablePath f.1)
    (hexcLoad : ∀ {j : Inputs}, exc j → ∃ s0, elf.loadState (cliProcessInputs j) = .ok s0) :
    Pred (.exited code out files) :=
  @exited_of_outcomeUpTo_raw_placed mpl mmpl elf W exc ⟨hexcLoad⟩ i i₀ Pred code out files hr hup
    heq (fun f hf => ⟨(hvis f hf).1, (hvis f hf).2.1⟩)
    (fun f hf => ⟨(hvis₀ f hf).1, (hvis₀ f hf).2.1⟩) hload₀

private theorem exited_of_outcomeUpTo_f3_visRaw {mpl mmpl : MultiPlacement} {elf : ElfImage}
    {W : CliHooks} {exc : Inputs → Prop} [ExcLoadOk elf exc] {i i₀ : Inputs} {Pred : Outcome → Prop}
    {code : Nat} {out : HwBytes} {files : DirectorySnapshot}
    (hr : cliRunPlacedSig mpl mmpl elf W i = some (.exited code out files))
    (hup : OutcomeOrExcusedAbort exc (cliRunPlacedSig mpl mmpl elf W) i₀ Pred)
    (heq : InputsEquiv i i₀) (hvis : FilesVisible i.files)
    (hvis₀ : LibsignalBinary.Proofs.SignalSession.Cli.Parity.FilesVisibleRaw i₀.files)
    (hload₀ : ∀ f ∈ i₀.files, LoadablePath f.1) :
    Pred (.exited code out files) :=
  exited_of_outcomeUpTo_raw_placed hr hup heq (fun f hf => ⟨(hvis f hf).1, (hvis f hf).2.1⟩)
    hvis₀ hload₀

private theorem exited_of_or_none_outcomeUpTo_eq_f3 {mpl mmpl : MultiPlacement} {elf : ElfImage}
    {W : CliHooks} {exc : Inputs → Prop} {i : Inputs} {expected : Outcome}
    {code : Nat} {out : HwBytes} {files : DirectorySnapshot}
    (hr : cliRunPlacedSig mpl mmpl elf W i = some (.exited code out files))
    (hor : cliRunPlacedSig mpl mmpl elf W i = none ∨
      OutcomeOrExcusedAbort exc (cliRunPlacedSig mpl mmpl elf W) i (· = expected)) :
    Outcome.exited code out files = expected :=
  exited_of_or_none_outcomeUpTo_eq_raw_placed hr hor

/-! ## `PqModelPostB2` on exited runs -/

private def defaultExtrasV2F3 : UnreachedPqxdhPrimitives :=
  { sigPkGen := fun _ => [], sigSign := fun _ _ _ => [], scalarMul := fun _ _ => [],
    scalarAdd := fun _ _ => [], kemKeyGen := fun _ => ([], []), pow8 := fun _ => [],
    isValidDhTriple := fun _ _ _ => false }

/-- Establishes `PqModelPostB2` for any exited run of a `CliPqBinaryV2OomF3Placed` ELF image under
the 9 closed primitive equations of `realCliHooks` and `FilesVisible i.files`. -/
theorem pqModelPostB2_of_cliElf_exited_f3 {mpl mmpl : MultiPlacement} {elf : ElfImage}
    (hv2 : CliPqBinaryV2OomF3Placed mpl mmpl elf)
    (interp : ExternInterpretation) {W : CliHooks}
    (hF : W.C.F = CryptoVerification.LibsignalSpqrV1.sha256Compress)
    (hE : W.C.E = CryptoGames.AES256.aes256Enc)
    (hD : W.C.D = CryptoGames.AES256.aes256Dec)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (hF512 : W.Q.F512 = CryptoGames.SHA512.sha512CompressState)
    (hEnc : W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec)
    (hDec : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    {i : Inputs} {code : Nat} {out : HwBytes} {files : DirectorySnapshot}
    (hvis : FilesVisible i.files)
    (hr : cliRunPlacedSig mpl mmpl elf W i = some (.exited code out files)) :
    PqModelPostB2 interp ⟨W.C, W.Q⟩ i (.exited code out files) := by
  have hbase := hv2.base
  refine
    { init := fun X st b t hwf hsess heq =>
        exited_of_outcomeUpTo_f3_visRaw hr
          (((hbase.2 W hF hE hD hX hPub hF512 hEnc hDec hK X).1 st hwf).1 b t hsess) heq hvis
          (filesVisible_pqInitInputs_f3 _ st b t) (loadable_pqInitInputs _ st b t).2
      send := fun st m coins hwf hlen heq =>
        exited_of_outcomeUpTo_f3_visRaw hr
          (((hbase.2 W hF hE hD hX hPub hF512 hEnc hDec hK defaultExtrasV2F3).1 st hwf).2.1 m coins hlen)
          heq hvis
          (filesVisible_pqSendInputs_f3 _ st m coins) (loadable_pqSendInputs _ st m coins).2
      recvWhisper := fun st body rc hwf hlen heq =>
        exited_of_outcomeUpTo_f3_visRaw hr
          (((hbase.2 W hF hE hD hX hPub hF512 hEnc hDec hK defaultExtrasV2F3).1 st hwf).2.2.1 body rc hlen)
          heq hvis
          (filesVisible_pqRecvInputs_f3 _ st (wireWhisper :: body) rc)
          (loadable_pqRecvInputs _ st (wireWhisper :: body) rc).2
      recvPrekey := fun X st m rc hwf hlen hmatch heq =>
        exited_of_outcomeUpTo_f3_visRaw hr
          (((hbase.2 W hF hE hD hX hPub hF512 hEnc hDec hK X).1 st hwf).2.2.2.1 m rc hlen hmatch)
          heq hvis (filesVisible_pqRecvInputs_f3 _ st (wirePrekey :: m.bytes) rc)
          (loadable_pqRecvInputs _ st (wirePrekey :: m.bytes) rc).2
      recvPrekeyNoMatch := fun X st x g m rc hwf hsess hlen hnomatch heq =>
        exited_of_outcomeUpTo_f3_visRaw hr
          ((hbase.2 W hF hE hD hX hPub hF512 hEnc hDec hK X).2 st hwf x g hsess m rc hlen hnomatch)
          heq hvis (filesVisible_pqRecvInputs_f3 _ st (wirePrekey :: m.bytes) rc)
          (loadable_pqRecvInputs _ st (wirePrekey :: m.bytes) rc).2
      recvOther := fun st c rc hwf hlen hw hp heq =>
        exited_of_outcomeUpTo_f3_visRaw hr
          (((hbase.2 W hF hE hD hX hPub hF512 hEnc hDec hK defaultExtrasV2F3).1 st hwf).2.2.2.2 c rc hlen hw hp)
          heq hvis
          (filesVisible_pqRecvInputs_f3 _ st c rc) (loadable_pqRecvInputs _ st c rc).2
      recvPrekeyNoMatchSession := fun X st x g m rc hwf hsess hlen hcap hnomatch heq => by
        have hout := exited_of_outcomeUpTo_f3_visRaw hr
          (hv2.canonicalNoMatch W hF hE hD hX hPub hF512 hEnc hDec hK X st hwf x g hsess m rc hlen hnomatch)
          heq hvis (filesVisible_pqRecvInputs_f3 _ st (wirePrekey :: m.bytes) rc)
          (loadable_pqRecvInputs _ st (wirePrekey :: m.bytes) rc).2
        simp only [Nat.not_lt.mpr hcap, ↓reduceIte] at hout
        exact hout.2
      recvOverStdinCap := fun st body rc hwf _ hover heq =>
        exited_of_outcomeUpTo_f3_visRaw
          (Pred := (· = .exited 2 []
            (filesOf (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc).files)))
          hr (hv2.recvOverStdinCap W hF hE hD hX hPub hF512 hEnc hDec hK st hwf body rc hover)
          heq hvis (filesVisible_pqRecvInputs_f3 _ st (wirePrekey :: body) rc)
          (loadable_pqRecvInputs _ st (wirePrekey :: body) rc).2
      recvPrekeyReject := fun st body rc hwf hlen hcap hnone heq => by
        have hpnone : pksmParse body = none := by
          rcases pksmParse_parsePreKey_cases body with ⟨hp, _⟩ | ⟨_, _, _, hq, _⟩
          · exact hp
          · rw [hnone] at hq
            cases hq
        have hout := exited_of_outcomeUpTo_f3_visRaw
          hr (hv2.pksmParseNone W hF hE hD hX hPub hF512 hEnc hDec hK st hwf body rc hlen hpnone)
          heq hvis (filesVisible_pqRecvInputs_f3 _ st (wirePrekey :: body) rc)
          (loadable_pqRecvInputs _ st (wirePrekey :: body) rc).2
        simpa only [Nat.not_lt.mpr hcap, ↓reduceIte] using hout
      recvPrekeyUntyped := fun st body _ rc hwf hlen hcap hq hnone hnomatch heq => by
        rcases pksmParse_parsePreKey_cases body with ⟨_, hq_none⟩ | ⟨pm, _, hpm, hq', _⟩
        · rw [hq] at hq_none
          cases hq_none
        · cases hq.symm.trans hq'
          have huntyped : pkToE? pm = none := by
            have hb := (preKeyOfBody?_eq_pksmParse_bind_pkToE?_f3 body).symm.trans hnone
            simpa [hpm] using hb
          have hnsm : ∀ x g, st.session = some (x, g) → ¬ SessMatchesPm (d3PqSessionOf x g) pm :=
            fun x g hs hsm =>
              hnomatch x g hs ((pqFieldsMatch_iff_sessMatchesPm_f3 x g hq hpm).mpr hsm)
          have hout := exited_of_outcomeUpTo_f3_visRaw
            hr (hv2.untypedReject W hF hE hD hX hPub hF512 hEnc hDec hK st hwf body pm rc hlen hpm huntyped hnsm)
            heq hvis (filesVisible_pqRecvInputs_f3 _ st (wirePrekey :: body) rc)
            (loadable_pqRecvInputs _ st (wirePrekey :: body) rc).2
          simpa only [Nat.not_lt.mpr hcap, ↓reduceIte] using hout
      recvPrekeyMatching := fun st x g body _ rc hwf hsess hlen hcap hq hfm heq => by
        rcases pksmParse_parsePreKey_cases body with ⟨_, hq_none⟩ | ⟨pm, _, hpm, hq', _⟩
        · rw [hq] at hq_none
          cases hq_none
        · cases hq.symm.trans hq'
          have hsm : SessMatchesPm (d3PqSessionOf x g) pm :=
            (pqFieldsMatch_iff_sessMatchesPm_f3 x g hq hpm).mp hfm
          rw [pqRecvMatchingFieldsModel_eq_pqRecvMatchingModel_f3 ⟨W.C, W.Q⟩ st x g rc hq hpm]
          have hout := exited_of_outcomeUpTo_f3_visRaw
            hr (hv2.matchingPathB W hF hE hD hX hPub hF512 hEnc hDec hK st x g body pm rc hwf hsess (Nat.succ_le_of_lt hlen) hpm hsm)
            heq hvis (filesVisible_pqRecvInputs_f3 _ st (wirePrekey :: body) rc)
            (loadable_pqRecvInputs _ st (wirePrekey :: body) rc).2
          simpa only [Nat.not_lt.mpr hcap, ↓reduceIte] using hout
      recvPrekeyParsed := fun X st body m rc hwf hlen hcap hm hinner hmatch heq => by
        have hbind := (preKeyOfBody?_eq_pksmParse_bind_pkToE?_f3 body).symm.trans hm
        cases hpm : pksmParse body with
        | none =>
          rw [hpm] at hbind
          cases hbind
        | some pm =>
          rw [hpm] at hbind
          have hout := exited_of_outcomeUpTo_f3_visRaw
            hr (hv2.validMatch W hF hE hD hX hPub hF512 hEnc hDec hK X st hwf body pm m rc hlen hpm hbind hinner hmatch)
            heq hvis (filesVisible_pqRecvInputs_f3 _ st (wirePrekey :: body) rc)
            (loadable_pqRecvInputs _ st (wirePrekey :: body) rc).2
          simpa only [Nat.not_lt.mpr hcap, ↓reduceIte] using hout
      recvPrekeyParsedNoMatch := fun X st x g body m rc hwf hsess hlen hcap hm hinner hnomatch heq => by
        have hbind := (preKeyOfBody?_eq_pksmParse_bind_pkToE?_f3 body).symm.trans hm
        cases hpm : pksmParse body with
        | none =>
          rw [hpm] at hbind
          cases hbind
        | some pm =>
          rw [hpm] at hbind
          have hout := exited_of_outcomeUpTo_f3_visRaw hr
            (hv2.validOver W hF hE hD hX hPub hF512 hEnc hDec hK X st hwf x g hsess body pm m rc hlen hpm hbind hinner hnomatch)
            heq hvis (filesVisible_pqRecvInputs_f3 _ st (wirePrekey :: body) rc)
            (loadable_pqRecvInputs _ st (wirePrekey :: body) rc).2
          simp only [Nat.not_lt.mpr hcap, ↓reduceIte] at hout
          exact hout
      initFiles := fun X _ _ _ _ hwf hsess hb hcap hparse heq =>
        scrubAgree_of_eq (exited_of_or_none_outcomeUpTo_eq_f3 (exc := fun _ => False) hr
          (outcomeUpTo_pqInitFiles_exact_or_none_of_f3_inputsEquiv
            hv2 W hF hE hD hX hPub hF512 hEnc hDec hK X heq hwf hsess hb hcap hparse))
      initOverFileCap := fun _ _ _ hwf hsess hb hover heq =>
        exited_of_or_none_outcomeUpTo_eq_f3 (exc := fun _ => False) hr
          (outcomeUpTo_pqInitOverCap_or_none_of_f3_inputsEquiv
            hv2 W hF hE hD hX hPub hF512 hEnc hDec hK heq hwf hsess hb hover)
      initReject := fun _ _ _ hwf hsess hb hparse heq =>
        exited_of_or_none_outcomeUpTo_eq_f3 (exc := fun _ => False) hr
          (outcomeUpTo_pqInitReject_or_none_of_f3_inputsEquiv
            hv2 W hF hE hD hX hPub hF512 hEnc hDec hK heq hwf hsess hb hparse) }

/-! ## Whole-protocol refinement transfers -/

theorem traceInv_elfRelPlaced_pqModelRelB2_f3 {mpl mmpl : MultiPlacement} {elf : ElfImage}
    (hv2 : CliPqBinaryV2OomF3Placed mpl mmpl elf)
    {interp : ExternInterpretation} {W : CliHooks} {r : ProtocolSetup}
    (hext : DY.Libsignal.Composed.Refinement.Cli.ExternContractsHoldCli interp)
    (hAgree : HooksMatchInterpretation interp W)
    (_hE : W.C.E = CryptoGames.AES256.aes256Enc)
    (_hD : W.C.D = CryptoGames.AES256.aes256Dec)
    (hr : DY.Libsignal.Composed.Refinement.ProtocolSetupWF r) :
    ∃ I : DY.Libsignal.Composed.Refinement.Cli.CliTurn → Prop,
      I (DY.Libsignal.Composed.Refinement.Cli.CliTurn.init
        (DY.Libsignal.Composed.Refinement.Cli.initDirs interp r)) ∧
      TraceInv (elfRelPlaced mpl elf interp W) (PqModelRelB2 interp ⟨W.C, W.Q⟩) interp r I :=
  Symbolic.Proofs.Refinement.Composed.Cli.ElfRealGuardBridge.traceInv_of_real_postB2
    hext ((hooksAgree_iff_modelAgree_f3 interp W).mp hAgree) hr
    (fun hfb hRel =>
      pqModelPostB2_of_cliElf_exited_f3 hv2 interp
        (W := DY.Libsignal.Composed.Refinement.Cli.realCliHooks)
        rfl rfl rfl rfl rfl rfl rfl rfl rfl hfb
        ((congrFun (LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced.cliRunPlacedSig_eq mpl mmpl elf
          DY.Libsignal.Composed.Refinement.Cli.realCliHooks) _).trans hRel))

theorem compRefinesCliR_elfPlaced_of_modelB2_f3 {mpl mmpl : MultiPlacement} {elf : ElfImage}
    (hv2 : CliPqBinaryV2OomF3Placed mpl mmpl elf)
    (hM : CompRefinesCliModelB2) :
    DY.Libsignal.Composed.Refinement.Cli.CompRefinesCli
      DY.Libsignal.Composed.Refinement.Cli.HooksMatchPlaced
      (elfRelPlaced mpl elf) :=
  compRefinesCliR_of_inv
    (fun interp W hext ⟨hAgree, hE, hD⟩ =>
      ⟨⟨W.C, W.Q⟩, (hooksAgree_iff_modelAgree_f3 interp W).mp hAgree,
        fun _r hr => traceInv_elfRelPlaced_pqModelRelB2_f3 hv2 hext hAgree hE hD hr⟩)
    hM

theorem compRefinesCliBinaryPlacedAt_of_modelB2_f3 {mpl mmpl : MultiPlacement}
    {bytes : List (BitVec 8)} {elf : ElfImage}
    (hparse : ElfImage.parse bytes = .ok elf)
    (hcm : CryptoVerification.SignalSession.Placed.CliElfCodeMatchesPlaced mpl elf)
    (hv2 : CliPqBinaryV2OomF3Placed mpl mmpl elf)
    (hprog : DY.Libsignal.Composed.Refinement.Cli.CliElfProgressPlaced mpl elf)
    (hM : CompRefinesCliModelB2) :
    CompRefinesCliBinaryPlacedAt mpl bytes :=
  ⟨elf, hparse, hcm, hprog, compRefinesCliR_elfPlaced_of_modelB2_f3 hv2 hM⟩

theorem compRefinesCliBinaryPlaced_of_modelB2_f3 {bytes : List (BitVec 8)}
    (hAt : ∀ mpl : MultiPlacement,
      libsignalSessionLib.LinkedAt bytes mpl →
      CompRefinesCliBinaryPlacedAt mpl bytes) :
    CompRefinesCliBinaryPlaced bytes :=
  hAt

theorem compRefinesCliBinaryPlacedAt_of_v2OomF3Bytes {mpl mmpl : MultiPlacement}
    {bytes : List (BitVec 8)}
    (hcm : ∀ elf : ElfImage, ElfImage.parse bytes = .ok elf →
      CryptoVerification.SignalSession.Placed.CliElfCodeMatchesPlaced mpl elf)
    (hv2 : LibsignalCliPqBinaryV2OomF3PlacedAt mpl mmpl bytes)
    (hprog : ∀ elf : ElfImage, ElfImage.parse bytes = .ok elf →
      DY.Libsignal.Composed.Refinement.Cli.CliElfProgressPlaced mpl elf)
    (hM : CompRefinesCliModelB2) :
    CompRefinesCliBinaryPlacedAt mpl bytes := by
  obtain ⟨elf, hparse, hv2Elf⟩ := hv2
  exact compRefinesCliBinaryPlacedAt_of_modelB2_f3 hparse (hcm elf hparse) hv2Elf (hprog elf hparse) hM

theorem compRefinesCliBinaryPlaced_of_v2OomF3Bytes {bytes : List (BitVec 8)}
    (hmng : mallocngLib.LinkedIn bytes)
    (hcm : ∀ mpl : MultiPlacement, libsignalSessionLib.LinkedAt bytes mpl →
      ∀ elf : ElfImage, ElfImage.parse bytes = .ok elf →
        CryptoVerification.SignalSession.Placed.CliElfCodeMatchesPlaced mpl elf)
    (hv2 : LibsignalCliPqBinaryV2OomF3Placed bytes)
    (hprog : ∀ mpl mmpl : MultiPlacement,
      libsignalSessionLib.LinkedAt bytes mpl → mallocngLib.LinkedAt bytes mmpl →
      ∀ elf : ElfImage, ElfImage.parse bytes = .ok elf →
        DY.Libsignal.Composed.Refinement.Cli.CliElfProgressPlaced mpl elf)
    (hM : CompRefinesCliModelB2) :
    CompRefinesCliBinaryPlaced bytes := by
  intro mpl hLs
  obtain ⟨mmpl, hMm⟩ := hmng
  exact compRefinesCliBinaryPlacedAt_of_v2OomF3Bytes (hcm mpl hLs) (hv2 mpl mmpl hLs hMm)
    (hprog mpl mmpl hLs hMm) hM

end Symbolic.Proofs.Refinement.Composed.Cli.ElfToModelV2BridgeF3Placed
