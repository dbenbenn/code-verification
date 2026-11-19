/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Refinement.Composed.Cli.ElfShaGuardBridge -- proof-setup: allow-public-import
public import Symbolic.Specifications.Refinement.ElfBinding
import Symbolic.Proofs.Refinement.Composed.Cli.ParD7PureGates
import Symbolic.Proofs.Swarm.UA.Assembly
import Symbolic.Proofs.Swarm.UA.SlotInit
import Symbolic.Proofs.Swarm.UA.SlotRecvW
import Symbolic.Proofs.Swarm.UA.SlotRpkNO
import Symbolic.Proofs.Swarm.UA.SlotRpkProm
import Symbolic.Proofs.Swarm.UA.SlotSend
import Symbolic.Proofs.Swarm.UA.Top
import Symbolic.Proofs.Swarm.UA.XlateInv

/-!
# Real-Hooks Domain-Guard Transfer for `PqModelPostB2`

Machine-free transfer of `PqModelPostB2` and `TraceInv` from `realCliHooks` (`P₀`) back to
arbitrary `(interp, P)` along `PqTurnSim1A` and the per-call domain guard
`ElfGuard.DirsAgreeOnInput P P₀ i ∧ ElfGuard.ModelAgreesOnInput P P₀ i` (`RealHooksAgreeOnInput`).
-/

public section

set_option autoImplicit false

namespace Symbolic.Proofs.Refinement.Composed.Cli.ElfRealGuardBridge

open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement (
  PreKeyFields ProtocolSetup ProtocolSetupWF
)
open DY.Libsignal.Composed.Refinement.Cli (
  CliTurn ExternContractsHoldCli FilesVisible InputsEquiv ModelAgree
  NoMatchSessionFile PqFieldsMatch PqModelPost PqModelPostB2 PqModelRel PqModelRelB2
  TraceInv ValidCall bundleFilesFlat_publicBundleOf initDirs pqInitInputsF pqRecvMatchingFieldsModel
)
open DY.Libsignal.Composed.Refinement.Cli.ElfGuard (
  DirsAgreeOnInput ModelAgreesOnInput
)
open DY.Libsignal.Composed.Refinement.Cli.ParD3 (
  PqTurnSim1A pqTurnSim1A_clearSession pqTurnSim1A_init
)
open CryptoGames.LibsignalSession (Crypto GhostState)
open CryptoVerification.E2E (
  PEParams PreKeyBundleFields PreKeyMessageFields RecordExtras UnreachedPqxdhPrimitives
  djbKey encodeRecordUnderExtras initiateTapeLen keyPairOf partyAddressName wirePrekey wireWhisper
)
open CryptoVerification.SignalSession (
  Cmd Inputs Outcome OutcomeMatchesModelExceptPath PqParty PqxdhPartyInSpecDomain
  addressFile baseKeysBytes baseKeysFile bundleDir coinsFile encodeDir filesOf
  identityFile identityKeyPairFile kyberRecordBytes lastResortKyberPreKeyFile le32 markKyberUsed
  oneTimeKyberPreKeyFile oneTimePreKeyFile oneTimeRecordBytes partyAddress pqInitInputs pqInitModel
  pqInputs pqRecvInputs pqRecvPrekeyModel pqRecvWhisperModel pqSendInputs pqSendModel
  pqxdhExpectedOutcome publicBundleOf registrationIdFile removeOpk sessionFile signedPreKeyFile
  signedRecordBytes stdinCapBytes textBytes
)
open CryptoVerification.RecordCodecs (
  IdentityKeyPairStructure
)
open Symbolic.Proofs.Refinement.Composed.Cli.ElfShaGuardBridge (
  CallWithinCap aboveCap_after_eq_self caller_st_of_validCall pqModelPost_of_b2_withinCap
)
open Symbolic.Swarm.CREF.Cli (
  initDirs_interpOfParams interpOfParams modelAgree_interpOfParams
)

/-! ## Long-term secret-key preservation and `encodeDir` agreement across model transitions -/

/-- States `st'` reachable in one step from `st` keep `st.me` and `st.signed`, and either keep
`st.oneTime` or erase one consumed one-time pre-key slot to `none` (`removeOpk`). -/
def PreservesLongTermKeys (st st' : PqParty) : Prop :=
  st'.me = st.me ∧
  st'.signed = st.signed ∧
  (st'.oneTime = st.oneTime ∨
    ∃ j, st'.oneTime = st.oneTime.map (fun (i, k) => if i = j then (i, none) else (i, k)))

private def idPairEntry (C : Crypto) (st : PqParty) : String × HwBytes :=
  (identityKeyPairFile, IdentityKeyPairStructure.encode
    ⟨djbKey (keyPairOf C st.me.idPriv).publicKey.bytes, st.me.idPriv.toList⟩)

private def oneTimeEntry (C : Crypto) :
    BitVec 32 × Option (List.Vector (BitVec 8) 32) → String × HwBytes :=
  fun (i, k) =>
    (oneTimePreKeyFile i, match k with | some sk => oneTimeRecordBytes C i sk | none => [])

private theorem map_oneTimeEntry_erase_congr {C C₀ : Crypto}
    {l : List (BitVec 32 × Option (List.Vector (BitVec 8) 32))}
    (j : BitVec 32)
    (h : l.map (oneTimeEntry C) = l.map (oneTimeEntry C₀)) :
    (l.map (fun (i, k) => if i = j then (i, none) else (i, k))).map (oneTimeEntry C) =
      (l.map (fun (i, k) => if i = j then (i, none) else (i, k))).map (oneTimeEntry C₀) := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨i, k⟩
    simp only [List.map_cons, List.cons.injEq] at h ⊢
    refine ⟨?_, ih h.2⟩
    by_cases hij : i = j
    · simp [hij, oneTimeEntry]
    · simp [hij, h.1]

/-- Key-subset persistence: if `encodeDir P st = encodeDir P₀ st`
and `st'` preserves `st`'s long-term private keys (possibly erasing one consumed OPK), then
`encodeDir P st' = encodeDir P₀ st'`. -/
theorem encodeDir_eq_of_preservesLongTermKeys {P P₀ : PEParams} {st st' : PqParty}
    (henc : encodeDir P st = encodeDir P₀ st)
    (hpres : PreservesLongTermKeys st st') :
    encodeDir P st' = encodeDir P₀ st' := by
  let hdr (C : Crypto) (s : PqParty) : List (String × HwBytes) :=
    [(addressFile, textBytes (partyAddress s.party).text),
     idPairEntry C s,
     (registrationIdFile, le32 s.me.regId)]
  let peerL (s : PqParty) : List (String × HwBytes) :=
    match s.peerId with
    | some k => [(identityFile (partyAddressName s.party.other), k.serialize)]
    | none => []
  let sessL (s : PqParty) : List (String × HwBytes) :=
    match s.session with
    | some (x, g) => [(sessionFile (partyAddress s.party.other), encodeRecordUnderExtras (fun _ => x) g)]
    | none => []
  let sigL (C : Crypto) (s : PqParty) : List (String × HwBytes) :=
    s.signed.map (fun (i, k) => (signedPreKeyFile i, signedRecordBytes C i k))
  let otL (C : Crypto) (s : PqParty) : List (String × HwBytes) :=
    s.oneTime.map (oneTimeEntry C)
  let tailL (s : PqParty) : List (String × HwBytes) :=
    s.kyberOneTime.map (fun (i, k) =>
      (oneTimeKyberPreKeyFile i, match k with | some k => kyberRecordBytes i k | none => [])) ++
    (s.kyberLastResort.map fun (i, k, seen) =>
      [(lastResortKyberPreKeyFile i, kyberRecordBytes i k), (baseKeysFile i, baseKeysBytes seen)]).flatten
  have henc_fold : ∀ (Q : PEParams) (s : PqParty),
      encodeDir Q s = hdr Q.C s ++ (peerL s ++ (sessL s ++ (sigL Q.C s ++ (otL Q.C s ++ tailL s)))) := by
    intro Q s
    simp only [encodeDir, hdr, idPairEntry, peerL, sessL, sigL, otL, tailL, List.append_assoc]
    rfl
  rw [henc_fold P st, henc_fold P₀ st] at henc
  obtain ⟨hhdr, h1⟩ := List.append_inj henc rfl
  have hid : idPairEntry P.C st = idPairEntry P₀.C st := (List.cons.inj (List.cons.inj hhdr).2).1
  have h2 := List.append_cancel_left (List.append_cancel_left h1)
  obtain ⟨hsig, h3⟩ := List.append_inj h2 (by simp [sigL])
  obtain ⟨hot, _⟩ := List.append_inj h3 (by simp [otL])
  obtain ⟨hme, hsigned, honetime⟩ := hpres
  have hid' : idPairEntry P.C st' = idPairEntry P₀.C st' := by
    simp only [idPairEntry, hme] at hid ⊢
    exact hid
  have hsig' : sigL P.C st' = sigL P₀.C st' := by
    simp only [sigL, hsigned] at hsig ⊢
    exact hsig
  have hot' : otL P.C st' = otL P₀.C st' := by
    rcases honetime with hot_eq | ⟨j, hot_map⟩
    · simp only [otL, hot_eq] at hot ⊢
      exact hot
    · simp only [otL, hot_map]
      exact map_oneTimeEntry_erase_congr j hot
  rw [henc_fold P st', henc_fold P₀ st']
  simp only [hdr, hid', hsig', hot']

private theorem pqInputs_congr_of_encodeDir_eq {P P₀ : PEParams} {st : PqParty}
    (henc : encodeDir P st = encodeDir P₀ st)
    (cmd : Cmd) (extra : List (String × HwBytes)) (coins stdin : HwBytes) :
    pqInputs P st cmd extra coins stdin = pqInputs P₀ st cmd extra coins stdin := by
  unfold pqInputs
  rw [henc]

private theorem pqxdhExpectedOutcome_congr_of_res {P P₀ : PEParams} (i : Inputs)
    {res : Option (Option (PqParty × HwBytes))}
    (hres : ∀ st' out, res = some (some (st', out)) → encodeDir P st' = encodeDir P₀ st') :
    pqxdhExpectedOutcome P₀ i res = pqxdhExpectedOutcome P i res := by
  cases res with
  | none => rfl
  | some opt =>
    cases opt with
    | none => rfl
    | some pair =>
      rcases pair with ⟨st', out⟩
      simp only [pqxdhExpectedOutcome, Option.map, hres st' out rfl]

private theorem outcomeMatchesModelExceptPath_congr_of_res {P P₀ : PEParams} (i : Inputs)
    (p : String) {res : Option (Option (PqParty × HwBytes))} {o : Outcome}
    (hres : ∀ st' out, res = some (some (st', out)) → encodeDir P st' = encodeDir P₀ st')
    (h₀ : OutcomeMatchesModelExceptPath P₀ i p res o) :
    OutcomeMatchesModelExceptPath P i p res o := by
  unfold OutcomeMatchesModelExceptPath at h₀ ⊢
  rwa [pqxdhExpectedOutcome_congr_of_res i hres] at h₀

private theorem preserves_pqInitModel {X : UnreachedPqxdhPrimitives} {P : PEParams}
    {st st' : PqParty} {b : PreKeyBundleFields} {t : List.Vector (BitVec 8) initiateTapeLen}
    {out : HwBytes} (h : pqInitModel X P st b t = some (some (st', out))) :
    PreservesLongTermKeys st st' := by
  unfold pqInitModel at h
  split_ifs at h
  · simp at h
  · cases hi : CryptoVerification.E2E.initiateState X P st.party st.me b t with
    | none => simp [hi] at h
    | some xg =>
      rcases xg with ⟨x, g⟩
      simp only [hi, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, _⟩
      exact ⟨rfl, rfl, Or.inl rfl⟩

private theorem preserves_pqSendModel {P : PEParams} {st st' : PqParty} {m r : HwBytes}
    {out : HwBytes} (h : pqSendModel P st m r = some (some (st', out))) :
    PreservesLongTermKeys st st' := by
  unfold pqSendModel at h
  cases hs : st.session with
  | none => simp [hs] at h
  | some xg =>
    rcases xg with ⟨x, g⟩
    simp only [hs] at h
    split at h
    · cases hr : g.session.remoteIdentity with
      | none => simp [hr] at h
      | some k =>
        simp only [hr] at h
        by_cases ht : (!st.trusts k) = true
        · simp [ht] at h
        · simp only [ht] at h
          rcases h with ⟨rfl, _⟩
          exact ⟨rfl, rfl, Or.inl rfl⟩
    · simp at h
    · simp at h

private theorem preserves_pqxdhSessionDecryptModel {P : PEParams} {st st' : PqParty}
    {x : RecordExtras} {g : GhostState HwBytes}
    {msg : CryptoGames.LibsignalSession.SignalMessage}
    {ty : CryptoGames.LibsignalSession.MessageType}
    {rc : BitVec 256} {out : HwBytes}
    (h : CryptoVerification.SignalSession.pqxdhSessionDecryptModel P st x g msg ty rc =
      some (some (st', out))) :
    PreservesLongTermKeys st st' := by
  unfold CryptoVerification.SignalSession.pqxdhSessionDecryptModel at h
  split at h
  · next pt s _ =>
    cases hr : s.remoteIdentity with
    | none => simp [hr] at h
    | some k =>
      simp only [hr] at h
      split_ifs at h
      · simp at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, _⟩
        exact ⟨rfl, rfl, Or.inl rfl⟩
  · simp at h
  · simp at h

private theorem preserves_pqRecvWhisperModel {P : PEParams} {st st' : PqParty}
    {body : HwBytes} {rc : BitVec 256} {out : HwBytes}
    (h : pqRecvWhisperModel P st body rc = some (some (st', out))) :
    PreservesLongTermKeys st st' := by
  unfold pqRecvWhisperModel at h
  cases hs : st.session with
  | none => simp [hs] at h
  | some xg =>
    rcases xg with ⟨x, g⟩
    simp only [hs] at h
    split at h
    · simp at h
    · exact preserves_pqxdhSessionDecryptModel h

private theorem markKyberUsed_preserves {st st1 : PqParty} {m : PreKeyMessageFields}
    (h : markKyberUsed st m = some st1) :
    st1.me = st.me ∧ st1.signed = st.signed ∧ st1.oneTime = st.oneTime := by
  unfold markKyberUsed at h
  cases hk : List.lookup m.kpkId st.kyberOneTime with
  | none =>
    simp only [hk] at h
    cases hl : List.lookup m.kpkId st.kyberLastResort with
    | none => simp [hl] at h
    | some ks =>
      simp only [hl] at h
      split_ifs at h
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl, rfl⟩
  | some opt =>
    cases opt with
    | none =>
      simp only [hk] at h
      cases hl : List.lookup m.kpkId st.kyberLastResort with
      | none => simp [hl] at h
      | some ks =>
        simp only [hl] at h
        split_ifs at h
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨rfl, rfl, rfl⟩
    | some _ =>
      simp only [hk, Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl, rfl⟩

private theorem preserves_pqRecvPrekeyModel {X : UnreachedPqxdhPrimitives} {P : PEParams}
    {st st' : PqParty} {m : PreKeyMessageFields} {rc : BitVec 256} {out : HwBytes}
    (h : pqRecvPrekeyModel X P st m rc = some (some (st', out))) :
    PreservesLongTermKeys st st' := by
  unfold pqRecvPrekeyModel at h
  split at h
  · simp at h
  · simp only [] at h
    split_ifs at h
    · simp at h
    · cases hs : st.session with
      | some xg =>
        rcases xg with ⟨x, g⟩
        simp only [hs] at h
        split_ifs at h
        · simp at h
        · split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, _⟩
            exact ⟨rfl, rfl, Or.inl rfl⟩
          · simp at h
          · simp at h
        · simp at h
      | none =>
        simp only [hs] at h
        cases hp : CryptoVerification.SignalSession.preKeysNamedBy st m with
        | none => simp [hp] at h
        | some k =>
          simp only [hp] at h
          cases hr : CryptoVerification.E2E.recvPrekeyState X P st.party st.me k m rc with
          | none => simp [hr] at h
          | some opt =>
            cases opt with
            | none => simp [hr] at h
            | some xgp =>
              rcases xgp with ⟨x, g, pt⟩
              simp only [hr] at h
              cases hm : markKyberUsed st m with
              | none => simp [hm] at h
              | some st1 =>
                simp only [hm, Option.some.injEq, Prod.mk.injEq] at h
                rcases h with ⟨rfl, _⟩
                obtain ⟨hme, hsig, hot⟩ := markKyberUsed_preserves hm
                unfold removeOpk
                cases hopk : m.opkId with
                | none => exact ⟨hme, hsig, Or.inl hot⟩
                | some j => exact ⟨hme, hsig, Or.inr ⟨j, by rw [hot]⟩⟩

private theorem preserves_pqRecvMatchingFieldsModel {P : PEParams} {st st' : PqParty}
    {x : RecordExtras} {g : GhostState HwBytes} {q : PreKeyFields} {rc : BitVec 256}
    {out : HwBytes} (h : pqRecvMatchingFieldsModel P st x g q rc = some (some (st', out))) :
    PreservesLongTermKeys st st' := by
  unfold pqRecvMatchingFieldsModel at h
  dsimp only at h
  split_ifs at h
  · simp at h
  · simp at h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, _⟩
      exact ⟨rfl, rfl, Or.inl rfl⟩
    · simp at h
    · simp at h

/-! ## Transferring `PqModelPostB2` and `TraceInv` across `DirsAgreeOnInput ∧ ModelAgreesOnInput` -/

/-- Transfers `PqModelPostB2` from `P₀` (`realCliHooks`) back to `P` using
`ElfGuard.DirsAgreeOnInput P P₀ i` and `ElfGuard.ModelAgreesOnInput P P₀ i`. -/
theorem pqModelPostB2_of_dirs_and_model_guard {interp : ExternInterpretation}
    {P P₀ : PEParams} {i : Inputs} {o : Outcome}
    (hdirs : DirsAgreeOnInput P P₀ i)
    (hmod : ModelAgreesOnInput P P₀ i)
    (hpost₀ : PqModelPostB2 interp P₀ i o) :
    PqModelPostB2 interp P i o where
  init := fun X st b tVec hwf hsess heq => by
    obtain ⟨henc, hwf₀⟩ :=
      hdirs st (.init _ bundleDir) _ _ _ hwf ⟨rfl, bundleFilesFlat_publicBundleOf b⟩ heq
    have hinp : pqInitInputs P st b tVec = pqInitInputs P₀ st b tVec :=
      pqInputs_congr_of_encodeDir_eq henc _ _ _ _
    have ho := hpost₀.init X st b tVec hwf₀ hsess (hinp ▸ heq)
    have hm := hmod.1 X st ((publicBundleOf b).files bundleDir) b tVec hwf hsess (Or.inl rfl) heq
    rw [ho, ← hinp, ← hm, pqxdhExpectedOutcome_congr_of_res _
      (fun _ _ h => encodeDir_eq_of_preservesLongTermKeys henc (preserves_pqInitModel h))]
  send := fun st m coins hwf hlen heq => by
    obtain ⟨henc, hwf₀⟩ := hdirs st _ _ _ _ hwf rfl heq
    have hinp : pqSendInputs P st m coins = pqSendInputs P₀ st m coins :=
      pqInputs_congr_of_encodeDir_eq henc _ _ _ _
    have ho := hpost₀.send st m coins hwf₀ hlen (hinp ▸ heq)
    have hm := hmod.2.1 st m coins hwf hlen heq
    rw [ho, ← hinp, ← hm, pqxdhExpectedOutcome_congr_of_res _
      (fun _ _ h => encodeDir_eq_of_preservesLongTermKeys henc (preserves_pqSendModel h))]
  recvWhisper := fun st body rc hwf hlen heq => by
    obtain ⟨henc, hwf₀⟩ := hdirs st _ _ _ _ hwf rfl heq
    have hinp : pqRecvInputs P st (wireWhisper :: body) rc =
        pqRecvInputs P₀ st (wireWhisper :: body) rc :=
      pqInputs_congr_of_encodeDir_eq henc _ _ _ _
    have ho := hpost₀.recvWhisper st body rc hwf₀ hlen (hinp ▸ heq)
    have hm := hmod.2.2.1 st body rc hwf hlen heq
    rw [ho, ← hinp, ← hm, pqxdhExpectedOutcome_congr_of_res _
      (fun _ _ h => encodeDir_eq_of_preservesLongTermKeys henc (preserves_pqRecvWhisperModel h))]
  recvPrekey := fun X st m rc hwf hlen hmatch heq => by
    obtain ⟨henc, hwf₀⟩ := hdirs st _ _ _ _ hwf rfl heq
    have hinp : pqRecvInputs P st (wirePrekey :: m.bytes) rc =
        pqRecvInputs P₀ st (wirePrekey :: m.bytes) rc :=
      pqInputs_congr_of_encodeDir_eq henc _ _ _ _
    have ho := hpost₀.recvPrekey X st m rc hwf₀ hlen hmatch (hinp ▸ heq)
    have hm := (hmod.2.2.2.1 X st m.bytes m rc hwf hlen (Or.inl rfl) heq).1 hmatch
    rw [ho, ← hinp, ← hm, pqxdhExpectedOutcome_congr_of_res _
      (fun _ _ h => encodeDir_eq_of_preservesLongTermKeys henc (preserves_pqRecvPrekeyModel h))]
  recvPrekeyNoMatch := fun X st x g m rc hwf hsess hlen hnm heq => by
    obtain ⟨henc, hwf₀⟩ := hdirs st _ _ _ _ hwf rfl heq
    have hinp : pqRecvInputs P st (wirePrekey :: m.bytes) rc =
        pqRecvInputs P₀ st (wirePrekey :: m.bytes) rc :=
      pqInputs_congr_of_encodeDir_eq henc _ _ _ _
    have ho := hpost₀.recvPrekeyNoMatch X st x g m rc hwf₀ hsess hlen hnm (hinp ▸ heq)
    have hm := (hmod.2.2.2.1 X st m.bytes m rc hwf hlen (Or.inl rfl) heq).2 x g hsess hnm
    have hencN : encodeDir P { st with session := none } =
        encodeDir P₀ { st with session := none } :=
      encodeDir_eq_of_preservesLongTermKeys henc ⟨rfl, rfl, Or.inl rfl⟩
    by_cases hgt : (wirePrekey :: m.bytes).length > stdinCapBytes
    · simp only [hgt, ↓reduceIte] at ho ⊢
      rwa [hinp]
    · simp only [hgt, ↓reduceIte] at ho ⊢
      rw [← hinp, ← hm] at ho
      exact outcomeMatchesModelExceptPath_congr_of_res _ _
        (fun _ _ h => encodeDir_eq_of_preservesLongTermKeys hencN (preserves_pqRecvPrekeyModel h))
        ho
  recvOther := fun st c_in rc hwf hlen hw hp heq => by
    obtain ⟨henc, hwf₀⟩ := hdirs st _ _ _ _ hwf rfl heq
    have hinp : pqRecvInputs P st c_in rc = pqRecvInputs P₀ st c_in rc :=
      pqInputs_congr_of_encodeDir_eq henc _ _ _ _
    have ho := hpost₀.recvOther st c_in rc hwf₀ hlen hw hp (hinp ▸ heq)
    rwa [← hinp] at ho
  recvPrekeyNoMatchSession := fun X st x g m rc hwf hsess hlen hcap hnm heq => by
    obtain ⟨henc, hwf₀⟩ := hdirs st _ _ _ _ hwf rfl heq
    have hinp : pqRecvInputs P st (wirePrekey :: m.bytes) rc =
        pqRecvInputs P₀ st (wirePrekey :: m.bytes) rc :=
      pqInputs_congr_of_encodeDir_eq henc _ _ _ _
    have ho := hpost₀.recvPrekeyNoMatchSession X st x g m rc hwf₀ hsess hlen hcap hnm (hinp ▸ heq)
    have hm := (hmod.2.2.2.1 X st m.bytes m rc hwf hlen (Or.inl rfl) heq).2 x g hsess hnm
    intro st' out x' g' hok
    exact ho st' out x' g' (hm ▸ hok)
  recvOverStdinCap := fun st body rc hwf hlen hgt heq => by
    obtain ⟨henc, hwf₀⟩ := hdirs st _ _ _ _ hwf rfl heq
    have hinp : pqRecvInputs P st (wirePrekey :: body) rc =
        pqRecvInputs P₀ st (wirePrekey :: body) rc :=
      pqInputs_congr_of_encodeDir_eq henc _ _ _ _
    have ho := hpost₀.recvOverStdinCap st body rc hwf₀ hlen hgt (hinp ▸ heq)
    rwa [← hinp] at ho
  recvPrekeyReject := fun st body rc hwf hlen hcap hnone heq => by
    obtain ⟨henc, hwf₀⟩ := hdirs st _ _ _ _ hwf rfl heq
    have hinp : pqRecvInputs P st (wirePrekey :: body) rc =
        pqRecvInputs P₀ st (wirePrekey :: body) rc :=
      pqInputs_congr_of_encodeDir_eq henc _ _ _ _
    have ho := hpost₀.recvPrekeyReject st body rc hwf₀ hlen hcap hnone (hinp ▸ heq)
    rwa [← hinp] at ho
  recvPrekeyUntyped := fun st body q rc hwf hlen hcap hq hnone hnm heq => by
    obtain ⟨henc, hwf₀⟩ := hdirs st _ _ _ _ hwf rfl heq
    have hinp : pqRecvInputs P st (wirePrekey :: body) rc =
        pqRecvInputs P₀ st (wirePrekey :: body) rc :=
      pqInputs_congr_of_encodeDir_eq henc _ _ _ _
    have ho := hpost₀.recvPrekeyUntyped st body q rc hwf₀ hlen hcap hq hnone hnm (hinp ▸ heq)
    rwa [← hinp] at ho
  recvPrekeyMatching := fun st x g body q rc hwf hsess hlen hcap hq hfm heq => by
    obtain ⟨henc, hwf₀⟩ := hdirs st _ _ _ _ hwf rfl heq
    have hinp : pqRecvInputs P st (wirePrekey :: body) rc =
        pqRecvInputs P₀ st (wirePrekey :: body) rc :=
      pqInputs_congr_of_encodeDir_eq henc _ _ _ _
    have ho := hpost₀.recvPrekeyMatching st x g body q rc hwf₀ hsess hlen hcap hq hfm (hinp ▸ heq)
    have hm : pqRecvMatchingFieldsModel P st x g q rc = pqRecvMatchingFieldsModel P₀ st x g q rc :=
      hmod.2.2.2.2 st x g body q rc hwf hsess hlen hq hfm heq
    rw [ho, ← hinp, ← hm, pqxdhExpectedOutcome_congr_of_res _
      (fun _ _ h => encodeDir_eq_of_preservesLongTermKeys henc
        (preserves_pqRecvMatchingFieldsModel h))]
  recvPrekeyParsed := fun X st body m rc hwf hlen hcap hm_parse hinner hmatch heq => by
    obtain ⟨henc, hwf₀⟩ := hdirs st _ _ _ _ hwf rfl heq
    have hinp : pqRecvInputs P st (wirePrekey :: body) rc =
        pqRecvInputs P₀ st (wirePrekey :: body) rc :=
      pqInputs_congr_of_encodeDir_eq henc _ _ _ _
    have ho := hpost₀.recvPrekeyParsed X st body m rc hwf₀ hlen hcap hm_parse hinner hmatch
      (hinp ▸ heq)
    have hm := (hmod.2.2.2.1 X st body m rc hwf hinner (Or.inr ⟨hlen, hm_parse⟩) heq).1 hmatch
    rw [ho, ← hinp, ← hm, pqxdhExpectedOutcome_congr_of_res _
      (fun _ _ h => encodeDir_eq_of_preservesLongTermKeys henc (preserves_pqRecvPrekeyModel h))]
  recvPrekeyParsedNoMatch := fun X st x g body m rc hwf hsess hlen hcap hm_parse hinner hnm heq => by
    obtain ⟨henc, hwf₀⟩ := hdirs st _ _ _ _ hwf rfl heq
    have hinp : pqRecvInputs P st (wirePrekey :: body) rc =
        pqRecvInputs P₀ st (wirePrekey :: body) rc :=
      pqInputs_congr_of_encodeDir_eq henc _ _ _ _
    obtain ⟨ho_om, ho_nm⟩ :=
      hpost₀.recvPrekeyParsedNoMatch X st x g body m rc hwf₀ hsess hlen hcap hm_parse hinner hnm
        (hinp ▸ heq)
    have hm := (hmod.2.2.2.1 X st body m rc hwf hinner (Or.inr ⟨hlen, hm_parse⟩) heq).2 x g hsess hnm
    have hencN : encodeDir P { st with session := none } =
        encodeDir P₀ { st with session := none } :=
      encodeDir_eq_of_preservesLongTermKeys henc ⟨rfl, rfl, Or.inl rfl⟩
    rw [← hinp, ← hm] at ho_om
    exact
      ⟨outcomeMatchesModelExceptPath_congr_of_res _ _
        (fun _ _ h => encodeDir_eq_of_preservesLongTermKeys hencN (preserves_pqRecvPrekeyModel h))
        ho_om,
       fun st' out x' g' hok => ho_nm st' out x' g' (hm ▸ hok)⟩
  initFiles := fun X st files b tVec hwf hsess hflat hcap hparse heq => by
    obtain ⟨henc, hwf₀⟩ := hdirs st (.init _ bundleDir) _ _ _ hwf ⟨rfl, hflat⟩ heq
    have hinp : pqInitInputsF P st files tVec = pqInitInputsF P₀ st files tVec :=
      pqInputs_congr_of_encodeDir_eq henc _ _ _ _
    have ho := hpost₀.initFiles X st files b tVec hwf₀ hsess hflat hcap hparse (hinp ▸ heq)
    have hm := hmod.1 X st files b tVec hwf hsess (Or.inr ⟨hflat, hparse⟩) heq
    rw [← hinp, ← hm, pqxdhExpectedOutcome_congr_of_res _
      (fun _ _ h => encodeDir_eq_of_preservesLongTermKeys henc (preserves_pqInitModel h))] at ho
    exact ho
  initOverFileCap := fun st files tVec hwf hsess hflat hover heq => by
    obtain ⟨henc, hwf₀⟩ := hdirs st (.init _ bundleDir) _ _ _ hwf ⟨rfl, hflat⟩ heq
    have hinp : pqInitInputsF P st files tVec = pqInitInputsF P₀ st files tVec :=
      pqInputs_congr_of_encodeDir_eq henc _ _ _ _
    have ho := hpost₀.initOverFileCap st files tVec hwf₀ hsess hflat hover (hinp ▸ heq)
    rwa [← hinp] at ho
  initReject := fun st files tVec hwf hsess hflat hparse heq => by
    obtain ⟨henc, hwf₀⟩ := hdirs st (.init _ bundleDir) _ _ _ hwf ⟨rfl, hflat⟩ heq
    have hinp : pqInitInputsF P st files tVec = pqInitInputsF P₀ st files tVec :=
      pqInputs_congr_of_encodeDir_eq henc _ _ _ _
    have ho := hpost₀.initReject st files tVec hwf₀ hsess hflat hparse (hinp ▸ heq)
    rwa [← hinp] at ho

/-- Constructs a `TraceInv` from any guarded run relation
`(fun i o => Rel₀ i o ∧ (ElfGuard.DirsAgreeOnInput P P₀ i ∧ ElfGuard.ModelAgreesOnInput P P₀ i))`
to `PqModelRelB2 interp P`, maintaining `PqTurnSim1A` directly at `(interpOfParams interp P, P)`. -/
theorem traceInv_of_real_postB2
    {Rel₀ : Inputs → Option Outcome → Prop}
    {interp : ExternInterpretation} {P P₀ : PEParams} {r : ProtocolSetup}
    (hext : ExternContractsHoldCli interp)
    (hagree : ModelAgree interp P)
    (hr : ProtocolSetupWF r)
    (hpost_real : ∀ {i code out files},
      FilesVisible i.files →
      Rel₀ i (some (.exited code out files)) →
      PqModelPostB2 interp P₀ i (.exited code out files)) :
    ∃ I : CliTurn → Prop,
      I (CliTurn.init (initDirs interp r)) ∧
      TraceInv
        (fun i o => Rel₀ i o ∧
          (DirsAgreeOnInput P P₀ i ∧ ModelAgreesOnInput P P₀ i))
        (PqModelRelB2 interp P) interp r I := by
  let I : CliTurn → Prop := fun t =>
    ∃ t_clean accepted, PqTurnSim1A (interpOfParams interp P) P r t t_clean accepted
  have hinit : I (CliTurn.init (initDirs interp r)) := by
    refine ⟨CliTurn.init (initDirs (interpOfParams interp P) r), [], ?_⟩
    have hd : initDirs interp r = initDirs (interpOfParams interp P) r :=
      congrFun (initDirs_interpOfParams interp P).symm r
    rw [hd]
    exact pqTurnSim1A_init hr ((modelAgree_interpOfParams interp P).mpr hagree)
  refine ⟨I, hinit, ?_⟩
  exact
    { clear := fun _ p ⟨t_clean, accepted, hsim⟩ =>
        ⟨t_clean.clearSession r p, accepted, pqTurnSim1A_clearSession p hr hsim⟩
      step := fun t c i code out files ⟨t_clean, accepted, hsim⟩ hval hin ⟨hRel₀, hdirs, hmod⟩ => by
        have hpost₀ : PqModelPostB2 interp P₀ i (.exited code out files) :=
          hpost_real hin.2.2.2.2 hRel₀
        have hpostP : PqModelPostB2 interp P i (.exited code out files) :=
          pqModelPostB2_of_dirs_and_model_guard hdirs hmod hpost₀
        refine ⟨Or.inr ⟨.exited code out files, rfl, hpostP⟩, ?_⟩
        by_cases hcap : CallWithinCap c
        · obtain ⟨_, st₀, hst₀, _⟩ := caller_st_of_validCall hr hsim hval
          have hpost1 : PqModelPost interp P i (.exited code out files) :=
            pqModelPost_of_b2_withinCap hval hin hst₀.dir_eq hcap hpostP
          have hRel1 : PqModelRel interp P i (some (.exited code out files)) :=
            Or.inr ⟨.exited code out files, rfl, hpost1⟩
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
              interp P r hext hagree hr (evs_pre := []) hsim hval hin hRel1
          exact ⟨t_clean', accepted', hsim'⟩
        · have hafter := aboveCap_after_eq_self hr hsim hval hin hcap hpostP
          exact ⟨t_clean, accepted, hafter.symm ▸ hsim⟩
      stop := fun _ _ _ o _ _ _ _ habort =>
        ⟨o, Or.inl (Or.inl habort), habort⟩ }

end Symbolic.Proofs.Refinement.Composed.Cli.ElfRealGuardBridge
