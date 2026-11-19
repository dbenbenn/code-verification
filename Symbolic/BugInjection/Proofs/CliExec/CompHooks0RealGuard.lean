/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.ElfBinding
public import Symbolic.BugInjection.Proofs.CliExec.CompHooks0Placed
public import Symbolic.BugInjection.Proofs.CliExec.CompHooks0Guard -- proof-setup: allow-public-import
public import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealX25519 -- proof-setup: allow-public-import
public import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealSha512 -- proof-setup: allow-public-import
public import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyber -- proof-setup: allow-public-import
public import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealMlkem -- proof-setup: allow-public-import
import LibsignalBinary.Specifications.LibsignalSpqrV1.Proto
import Symbolic.Proofs.Refinement.Composed.Cli.SDet.FilesOfAlg
import Symbolic.Proofs.Refinement.Composed.Cli.SDet.InputsInj
import Symbolic.Proofs.Refinement.Composed.Cli.SDet.ModelCongr
import Symbolic.Proofs.Swarm.CREF.Cli.RecordBridgeAux
import Symbolic.Proofs.Swarm.SHARED.SpqrX.Prost.MessageMerge.AppendX
import Symbolic.Proofs.Swarm.TRREF.GrowthOoo.Chain
import Symbolic.Proofs.Swarm.TRREF.GrowthOoo.Prims
import Symbolic.Proofs.Swarm.TRREF.GrowthOoo.State

/-!
# `RealHooksAgreeOnInput compHooks0` Witness Guard Lemmas

Proves `RealHooksAgreeOnInput compHooks0 i` (`ElfGuard.DirsAgreeOnInput ∧ ElfGuard.ModelAgreesOnInput`
against `realCliHooks`) across **all** matching `PqParty` states in `PqxdhPartyInSpecDomain` for
concrete witness `Inputs`:
* `realP0_eq_hybrid` equates `⟨realCliHooks.C, realCliHooks.Q⟩` to `realP0Hybrid` using the certified
  table-accelerated primitives in `CompHooks0Guard` and `CompHooks0Real{X25519,Sha512,Kyber,Mlkem}`;
* `DirsAgreeOnInput` extracts `PqPartyEquiv st st₀` for any matching `pqInputs` call, proves
  `encodeDir compP0 st = encodeDir realP0 st` from `checkPartyKeysInTable st₀ = true` (obligation (iv)),
  and transports `PqxdhPartyInSpecDomain compP0 st` to `PqxdhPartyInSpecDomain realP0 st` (including
  responder-session direction separation via `RawDir0` on `ReachablePqxdhSession`).
-/

namespace Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealGuard

open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (
  GhostState IdentityKey Mut OutgoingTripleRatchet PublicKey SessionState SignalMessage SpqrDirection
  TripleRatchet initializeInitiatorSession initializeRecipientSession rootCreateChain
)
open CryptoVerification.E2E (
  LocalIdentity PEParams PreKeyBundleFields PreKeyMessageFields RecordExtras ResponderPreKeySecrets
  UnreachedPqxdhPrimitives ReachablePqxdhSession acceptInput djbKey encodeRecordUnderExtras
  initiateInput initiateState initiateTapeLen initiatorRecordExtras keyPairOf modelPrims ofU8
  partyAddressName partyDeviceId partyIdentityKey pqxdhSessionParams pqxdhSpqrSession
  recvPrekeyState responderRecordExtras u8Vec wirePrekey
)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SignalSession (
  Cmd Inputs PqParty PqSessionMatches PqSignedKey PqxdhPartyInSpecDomain baseKeysFile bundleDir
  coinsFile encodeDir filesOf lastResortKyberPreKeyFile oneTimeKyberPreKeyFile oneTimePreKeyFile
  oneTimeRecordBytes partyAddress pqInitInputs pqInputs pqRecvInputs pqSendInputs preKeysNamedBy
  publicBundleOf signedPreKeyFile signedRecordBytes stdioPaths
)
open CryptoVerification.SpqrV1.Prost.MessageMerge.SymP3 (
  decodeKey_append_of_ok mergeFieldsLoop_step_of_ok protoPrefixStep_chainPB_mergeField
  protoPrefixStep_pqRatchetState_mergeField takeExact_eq_take_drop
)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement (PreKeyFields parsePreKey)
open DY.Libsignal.Composed.Refinement.Cli (
  BundleFilesFlat InputsEquiv PqFieldsMatch RealHooksAgreeOnInput realCliHooks
)
open DY.Libsignal.Composed.Refinement.Cli.ElfGuard (DirsAgreeOnInput ModelAgreesOnInput preKeyOfBody?)
open DY.Libsignal.Composed.Refinement.Cli.SDet (
  PqPartyEquiv PqSessionEquiv RegularFileList encodeRecordX_eq_of_pqSessionEquiv
  filesOf_append_of_regular filesOf_eq_optFold mem_of_filesOf_eq_some normalizePath_dir_nat_suf
  normalizePath_two regularFileList_bundle_files regularFileList_coins regularFileList_encodeDir
  topFileDirs
)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0Guard (
  checkInitEqAt checkPartyWF checkRecvPrekeyEqAt checkSendEqAt compP0 dummyX initiateCoreFast
  initiateState_eq_of_checkInitEqAt inputsEquiv_symm inputsEquiv_trans modelAgreesOnInput_of_pqInitInputsAt
  modelAgreesOnInput_of_pqRecvPrekey_noMatchAt modelAgreesOnInput_of_pqRecvPrekey_noneAt
  modelAgreesOnInput_of_pqSendInputsAt modelPrimsFast optEqBool pqPartyEquiv_of_checkPartyWF
  pqxdhSessionParamsFast prodEqBool recvMap_eq_of_checkRecvPrekeyEqAt recvPrekeyCoreFast
  sendMap_eq_of_checkSendEqAt serializedPartyAddressesFast serviceIdParseFast sessionStateEqBool
  sha256CompressTabled sha256CompressTabled_eq_spqr textBytesFast u8StrFast
)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0Placed (compHooks0)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0Placed.Interp0 (compSecretIdx)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyber (
  kyberDecapsHybrid kyberDecapsHybrid_eq kyberEncapsHybrid kyberEncapsHybrid_eq
)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealMlkem (mlkem768Hybrid mlkem768Hybrid_eq)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealSha512 (
  sha512CompressTabled sha512CompressTabled_eq_ref
)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealX25519 (
  compLookupPub_eq_x25519Pubkey_of_secretIdx x25519DhFast x25519DhFast_eq_ref x25519PubFast
  x25519PubFast_eq_ref
)
open Symbolic.Swarm.CREF.Cli (
  mut_exec_bind mut_exec_get mut_exec_liftE mut_exec_modify mut_exec_modifyGet mut_exec_pure
  pqSession recordScopeP_of_encodeRecordX_length
)
open Symbolic.Swarm.TRREF.GrowthOoo (
  chainParamsPB_mergeFieldsLoop_encodeRaw decodeVarint_encodeVarint_append
  mergeFieldsLoop_encodeMessage mergeFieldsLoop_nil mergeUint64_encodeVarint_append
  pqRatchetState_step_tag1
)

public section
set_option autoImplicit false

/-! ## Certified Hybrid `PEParams` for `realCliHooks` -/

/-- `PEParams` view of `realCliHooks`. -/
@[expose] noncomputable def realP0 : PEParams := ⟨realCliHooks.C, realCliHooks.Q⟩

/-- Certified table-accelerated `PEParams` equal to `realP0`. -/
@[expose] noncomputable def realP0Hybrid : PEParams :=
  ⟨{ F := sha256CompressTabled
     E := CryptoGames.AES256.aes256Enc
     D := CryptoGames.AES256.aes256Dec
     X := x25519DhFast
     pubKey := x25519PubFast },
   { F512 := sha512CompressTabled
     encaps := kyberEncapsHybrid
     decaps := kyberDecapsHybrid
     K := mlkem768Hybrid }⟩

theorem realP0_eq_hybrid : realP0 = realP0Hybrid := by
  unfold realP0 realP0Hybrid realCliHooks
  dsimp only
  rw [sha256CompressTabled_eq_spqr, x25519DhFast_eq_ref, x25519PubFast_eq_ref,
      sha512CompressTabled_eq_ref, kyberEncapsHybrid_eq, kyberDecapsHybrid_eq, mlkem768Hybrid_eq]
  rfl

@[expose] noncomputable def checkInitEqReal := checkInitEqAt compP0 realP0Hybrid
@[expose] noncomputable def checkSendEqReal := checkSendEqAt compP0 realP0Hybrid
@[expose] noncomputable def checkRecvPrekeyEqReal := checkRecvPrekeyEqAt compP0 realP0Hybrid

/-! ## Fast String/Model Bridges for Concrete Reachability Checks -/

private theorem byteArray_loop_eq' (arr : Array UInt8) (i : Nat) (r : List UInt8) :
    ByteArray.toList.loop ⟨arr⟩ i r = r.reverse ++ arr.toList.drop i := by
  unfold ByteArray.toList.loop; split
  · next h =>
    have hi : i < arr.size := h; have his : i < arr.toList.length := by simpa using hi
    have hget : (ByteArray.mk arr).get! i = arr.toList[i]'his := by simp [ByteArray.get!, getElem!_pos arr i hi]
    rw [byteArray_loop_eq' arr (i + 1) ((ByteArray.mk arr).get! i :: r), hget,
      List.reverse_cons, List.append_assoc, List.singleton_append, List.drop_eq_getElem_cons his]
  · next h =>
    have hi : arr.toList.length ≤ i := by have : ¬ i < arr.size := h; simp at *; omega
    rw [List.drop_eq_nil_of_le hi, List.append_nil]
termination_by arr.size - i
decreasing_by have : i < arr.size := ‹_›; omega

private theorem toUTF8_eq_flatMap (s : String) :
    s.toUTF8.toList = s.toList.flatMap String.utf8EncodeChar := by
  conv_lhs => rw [← String.ofList_toList (s := s)]
  rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList, List.utf8Encode]
  have h1 : (s.toList.flatMap String.utf8EncodeChar).toByteArray =
      ⟨(s.toList.flatMap String.utf8EncodeChar).toArray⟩ := by
    ext1; exact List.data_toByteArray
  rw [ByteArray.toList.eq_1, h1, byteArray_loop_eq']; simp

private theorem info_pqxdh_eq_fast :
    SignalPqxdh.INFO_PQXDH = u8StrFast "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024" := by
  unfold SignalPqxdh.INFO_PQXDH
  rw [toUTF8_eq_flatMap]
  rfl

private theorem modelPrims_eq_fast' (X : UnreachedPqxdhPrimitives) (W : PEParams) :
    modelPrims X W = modelPrimsFast X W := by
  have hkdf_eq : ∀ P : SignalPqxdh.Primitives, SignalPqxdh.hkdfDerive96Ref P = fun sec =>
      SignalPqxdh.hkdfExpand96Ref P (SignalPqxdh.hkdfExtractRef P none sec)
        (u8StrFast "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024") := by
    intro P; funext sec
    simp only [SignalPqxdh.hkdfDerive96Ref, info_pqxdh_eq_fast]
  unfold modelPrims modelPrimsFast; dsimp only; rw [hkdf_eq]

private theorem pqxdhSessionParams_eq_fast' (W : PEParams) :
    pqxdhSessionParams W = pqxdhSessionParamsFast W := by
  have hs : ∀ input, CryptoVerification.LibsignalTripleRatchetRepr.serviceIdParse
      CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse input = serviceIdParseFast input := by
    intro input
    simp only [CryptoVerification.LibsignalTripleRatchetRepr.serviceIdParse, serviceIdParseFast,
      CryptoVerification.LibsignalTripleRatchetRepr.pniPrefix_word]
  have hut : ∀ P : CryptoGames.Party,
      CryptoVerification.LibsignalTripleRatchetRepr.utf8 (partyAddressName P) =
        textBytesFast (partyAddressName P) := by
    intro P
    unfold CryptoVerification.LibsignalTripleRatchetRepr.utf8
    rw [toUTF8_eq_flatMap]
    cases P <;> rfl
  have ha : ∀ p q, CryptoVerification.E2E.serializedPartyAddresses
      CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse p q =
        serializedPartyAddressesFast p q := by
    intro p q
    simp only [CryptoVerification.E2E.serializedPartyAddresses, serializedPartyAddressesFast, hut, hs]
  simp only [pqxdhSessionParams, pqxdhSessionParamsFast, ha]

@[expose] def initiateStateFast (W : PEParams) (P : CryptoGames.Party) (me : LocalIdentity)
    (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen) :
    Option (RecordExtras × GhostState HwBytes) :=
  (initiateCoreFast dummyX W me b t).map fun ((ekAPk, kemCt), st) =>
    (initiatorRecordExtras me b ⟨u8Vec 32 ekAPk⟩ (u8Vec 1568 kemCt),
     ⟨P, st.setUnacknowledgedPreKeyMessage, 0, [0]⟩)

theorem initiateState_eq_fast (W : PEParams) (P : CryptoGames.Party) (me : LocalIdentity)
    (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen) :
    initiateState dummyX W P me b t = initiateStateFast W P me b t := by
  unfold initiateState initiateStateFast initiateCoreFast
  dsimp only
  rw [modelPrims_eq_fast']
  cases SignalPqxdh.Model.initiateKeys (modelPrimsFast dummyX W) (initiateInput W me b t) with
  | none => rfl
  | some p =>
    rcases p with ⟨dk, hdr⟩
    dsimp only
    cases initializeInitiatorSession W.C (pqxdhSpqrSession W) _ _ _ _ _ _ _ <;> rfl

@[expose] def recvPrekeyStateFast (W : PEParams) (P : CryptoGames.Party) (me : LocalIdentity)
    (k : ResponderPreKeySecrets) (m : PreKeyMessageFields) (rc : BitVec 256) :
    Option (Option (RecordExtras × GhostState HwBytes × HwBytes)) :=
  (recvPrekeyCoreFast dummyX W P me k m rc).map
    (Option.map fun (pt, st) => (responderRecordExtras me m, ⟨P, st, 1, [1]⟩, pt))

theorem recvPrekeyState_eq_fast (W : PEParams) (P : CryptoGames.Party) (me : LocalIdentity)
    (k : ResponderPreKeySecrets) (m : PreKeyMessageFields) (rc : BitVec 256) :
    recvPrekeyState dummyX W P me k m rc = recvPrekeyStateFast W P me k m rc := by
  unfold recvPrekeyState recvPrekeyStateFast recvPrekeyCoreFast
  dsimp only
  rw [modelPrims_eq_fast', pqxdhSessionParams_eq_fast']
  cases SignalMessage.tryFrom protoSignalCodec m.inner with
  | error _ => rfl
  | ok inner =>
    dsimp only
    by_cases hc : m.spkId ≠ k.spkId ∨ m.kpkId ≠ k.kpkId
    · have hcb : ((m.spkId != k.spkId) || (m.kpkId != k.kpkId)) = true := by
        simpa [Bool.or_eq_true, bne_iff_ne] using hc
      simp only [hc, hcb, ↓reduceIte]; rfl
    · have hcb : ((m.spkId != k.spkId) || (m.kpkId != k.kpkId)) = false := by
        cases hb : (m.spkId != k.spkId) || (m.kpkId != k.kpkId)
        · rfl
        · exact False.elim (hc (by simpa [Bool.or_eq_true, bne_iff_ne] using hb))
      simp only [hc, hcb, ↓reduceIte, Bool.false_eq_true]
      cases SignalPqxdh.Model.acceptKeys (modelPrimsFast dummyX W) (acceptInput W me k m) with
      | none => rfl
      | some dk =>
        dsimp only
        rcases SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
            ((pqxdhSessionParamsFast W).expectedAddrs P) inner .preKey rc _ with ⟨res, st⟩
        cases res with | ok pt => rfl | error e => cases e <;> rfl

/-! ## Decidable Equality Reflection for `RecordExtras × GhostState` -/

private theorem eq_of_sessionStateEqBool' {s₁ s₂ : SessionState HwBytes}
    (h : sessionStateEqBool s₁ s₂ = true) : s₁ = s₂ := by
  rcases s₁ with ⟨sv1, li1, ri1, rk1, pc1, sc1, rc1, ppk1, pq1⟩
  rcases s₂ with ⟨sv2, li2, ri2, rk2, pc2, sc2, rc2, ppk2, pq2⟩
  dsimp only [sessionStateEqBool] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨hsv, hli⟩, hri⟩, hrk⟩, hpc⟩, hsc⟩, hrc⟩, hppk⟩, hpq⟩
  have hli' : li1 = li2 := by
    rcases li1 with ⟨⟨v1⟩⟩; rcases li2 with ⟨⟨v2⟩⟩
    dsimp only [CompHooks0Guard.idKeyEqBool, CompHooks0Guard.pubKeyEqBool] at hli
    exact congrArg (IdentityKey.mk ∘ PublicKey.mk) (List.Vector.eq _ _ (beq_iff_eq.mp hli))
  have hri' : ri1 = ri2 := by
    cases ri1 <;> cases ri2 <;> try cases hri
    · rfl
    · rename_i a b; rcases a with ⟨⟨v1⟩⟩; rcases b with ⟨⟨v2⟩⟩
      dsimp only [optEqBool, CompHooks0Guard.idKeyEqBool, CompHooks0Guard.pubKeyEqBool] at hri
      exact congrArg (some ∘ IdentityKey.mk ∘ PublicKey.mk) (List.Vector.eq _ _ (beq_iff_eq.mp hri))
  have hsc' : sc1 = sc2 := by
    cases sc1 <;> cases sc2 <;> try cases hsc
    · rfl
    · rename_i a b
      rcases a with ⟨⟨⟨vp1⟩, ⟨vs1⟩⟩, ⟨ck1, ci1⟩⟩
      rcases b with ⟨⟨⟨vp2⟩, ⟨vs2⟩⟩, ⟨ck2, ci2⟩⟩
      dsimp only [optEqBool, CompHooks0Guard.senderChainEqBool, CompHooks0Guard.keyPairEqBool,
        CompHooks0Guard.pubKeyEqBool, CompHooks0Guard.privKeyEqBool, CompHooks0Guard.chainKeyEqBool] at hsc
      simp only [Bool.and_eq_true, beq_iff_eq] at hsc
      rcases hsc with ⟨⟨hp, hs⟩, hck, hci⟩
      rw [List.Vector.eq _ _ hp, List.Vector.eq _ _ hs, hck, hci]
  have hrc' : rc1 = rc2 := by
    have hrec : ∀ l1 l2, CompHooks0Guard.listEqBool CompHooks0Guard.recvChainEqBool l1 l2 = true → l1 = l2 := by
      intro l1
      induction l1 with
      | nil => intro l2 hl; cases l2 <;> first | rfl | cases hl
      | cons c1 tl1 ih =>
        intro l2 hl; cases l2 with
        | nil => cases hl
        | cons c2 tl2 =>
          dsimp only [CompHooks0Guard.listEqBool] at hl
          obtain ⟨hc, htl⟩ := (Bool.and_eq_true _ _).mp hl
          rcases c1 with ⟨⟨sr1⟩, ck1, mk1⟩
          rcases c2 with ⟨⟨sr2⟩, ck2, mk2⟩
          dsimp only [CompHooks0Guard.recvChainEqBool, CompHooks0Guard.pubKeyEqBool] at hc
          obtain ⟨⟨hsr, hck⟩, hmk⟩ := (Bool.and_eq_true _ _).mp hc |>.imp_left (Bool.and_eq_true _ _).mp
          have hsr' : sr1 = sr2 := List.Vector.eq _ _ (beq_iff_eq.mp hsr)
          have hck' : ck1 = ck2 := by
            cases ck1 <;> cases ck2 <;> try cases hck
            · rfl
            · rename_i k1 k2; rcases k1 with ⟨v1, i1⟩; rcases k2 with ⟨v2, i2⟩
              dsimp only [optEqBool, CompHooks0Guard.chainKeyEqBool] at hck
              obtain ⟨hv, hi⟩ := (Bool.and_eq_true _ _).mp hck
              rw [beq_iff_eq.mp hv, beq_iff_eq.mp hi]
          have hmk' : mk1 = mk2 := by
            have hmkRec : ∀ m1 m2,
                CompHooks0Guard.listEqBool CompHooks0Guard.msgKeyGenEqBool m1 m2 = true → m1 = m2 := by
              intro m1
              induction m1 with
              | nil => intro m2 hm; cases m2 <;> first | rfl | cases hm
              | cons g1 r1 ihm =>
                intro m2 hm; cases m2 with
                | nil => cases hm
                | cons g2 r2 =>
                  dsimp only [CompHooks0Guard.listEqBool, CompHooks0Guard.msgKeyGenEqBool] at hm
                  obtain ⟨h12, hr⟩ := (Bool.and_eq_true _ _).mp hm
                  rcases g1 with ⟨sd1, ct1⟩; rcases g2 with ⟨sd2, ct2⟩
                  obtain ⟨hsd, hct⟩ := (Bool.and_eq_true _ _).mp h12
                  dsimp only at hsd hct
                  rw [beq_iff_eq.mp hsd, beq_iff_eq.mp hct, ihm r2 hr]
            exact hmkRec mk1 mk2 hmk
          rw [hsr', hck', hmk', ih tl2 htl]
    exact hrec rc1 rc2 hrc
  subst hsv hli' hri' hrk hpc hsc' hrc' hppk hpq
  rfl

@[expose] def recordExtrasEqBool (a b : RecordExtras) : Bool :=
  (a.pending.preKeyId == b.pending.preKeyId) &&
  (a.pending.signedPreKeyId == b.pending.signedPreKeyId) &&
  (a.pending.baseKey.bytes.toList == b.pending.baseKey.bytes.toList) &&
  (a.pending.timestamp == b.pending.timestamp) &&
  optEqBool (fun k1 k2 => (k1.preKeyId == k2.preKeyId) && (k1.ciphertext == k2.ciphertext)) a.kyber b.kyber &&
  (a.remoteRegistrationId == b.remoteRegistrationId) &&
  (a.localRegistrationId == b.localRegistrationId) &&
  (a.aliceBaseKey == b.aliceBaseKey)

private theorem eq_of_recordExtrasEqBool {a b : RecordExtras}
    (h : recordExtrasEqBool a b = true) : a = b := by
  rcases a with ⟨⟨pk1, sp1, ⟨bk1⟩, ts1⟩, ky1, rr1, lr1, ab1⟩
  rcases b with ⟨⟨pk2, sp2, ⟨bk2⟩, ts2⟩, ky2, rr2, lr2, ab2⟩
  dsimp only [recordExtrasEqBool] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨hpk, hsp⟩, hbk⟩, hts⟩, hky⟩, hrr⟩, hlr⟩, hab⟩
  have hky' : ky1 = ky2 := by
    cases ky1 <;> cases ky2 <;> try cases hky
    · rfl
    · rename_i k1 k2; rcases k1 with ⟨i1, c1⟩; rcases k2 with ⟨i2, c2⟩
      dsimp only [optEqBool] at hky
      rcases (Bool.and_eq_true _ _).mp hky with ⟨hi, hc⟩
      rw [beq_iff_eq.mp hi, beq_iff_eq.mp hc]
  rw [hpk, hsp, List.Vector.eq _ _ hbk, hts, hky', hrr, hlr, hab]

@[expose] def ghostStateEqBool (a b : GhostState HwBytes) : Bool :=
  (a.party == b.party) && sessionStateEqBool a.session b.session &&
  (a.epoch == b.epoch) && (a.chainEpochs == b.chainEpochs)

private theorem eq_of_ghostStateEqBool {a b : GhostState HwBytes}
    (h : ghostStateEqBool a b = true) : a = b := by
  rcases a with ⟨p1, s1, e1, ce1⟩
  rcases b with ⟨p2, s2, e2, ce2⟩
  dsimp only [ghostStateEqBool] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rw [h.1.1.1, eq_of_sessionStateEqBool' h.1.1.2, h.1.2, h.2]

@[expose] def sessionPairOptEqBool :
    Option (RecordExtras × GhostState HwBytes) → Option (RecordExtras × GhostState HwBytes) → Bool :=
  optEqBool (prodEqBool recordExtrasEqBool ghostStateEqBool)

theorem eq_of_sessionPairOptEqBool {a b : Option (RecordExtras × GhostState HwBytes)}
    (h : sessionPairOptEqBool a b = true) : a = b := by
  cases a <;> cases b <;> try cases h
  · rfl
  · rename_i p1 p2; rcases p1 with ⟨x1, g1⟩; rcases p2 with ⟨x2, g2⟩
    dsimp only [sessionPairOptEqBool, optEqBool, prodEqBool] at h
    rcases (Bool.and_eq_true _ _).mp h with ⟨hx, hg⟩
    rw [eq_of_recordExtrasEqBool hx, eq_of_ghostStateEqBool hg]

/-! ## Concrete `ReachablePqxdhSession realP0` Builders -/

theorem reachReal_of_init {stInit st₀ : PqParty} {b₀ : PreKeyBundleFields}
    {t₀ : List.Vector (BitVec 8) initiateTapeLen} {x₀ : RecordExtras} {g₀ : GhostState HwBytes}
    (hInitEq : checkInitEqReal stInit b₀ t₀ = true)
    (hsess : st₀.session = some (x₀, g₀))
    (hMe : st₀.me = stInit.me)
    (hStep : sessionPairOptEqBool (initiateStateFast compP0 stInit.party stInit.me b₀ t₀) st₀.session = true) :
    ∃ gR, ReachablePqxdhSession realP0 st₀.me x₀ gR ∧ gR.party = g₀.party ∧ gR.session = g₀.session := by
  have hComp : initiateState dummyX compP0 stInit.party stInit.me b₀ t₀ = some (x₀, g₀) := by
    rw [initiateState_eq_fast]
    exact (eq_of_sessionPairOptEqBool hStep).trans hsess
  have hReal : initiateState dummyX realP0 stInit.party stInit.me b₀ t₀ = some (x₀, g₀) :=
    (initiateState_eq_of_checkInitEqAt realP0_eq_hybrid hInitEq).symm.trans hComp
  exact ⟨g₀, hMe ▸ ReachablePqxdhSession.initiate dummyX stInit.party stInit.me b₀ t₀ x₀ g₀ hReal, rfl, rfl⟩

theorem reachReal_of_send {stPrev st₀ : PqParty} {mPrev : HwBytes} {rPrev : List.Vector (BitVec 8) 64}
    {xPrev x₀ : RecordExtras} {gPrev g₀ : GhostState HwBytes}
    (hPrevSess : stPrev.session = some (xPrev, gPrev))
    (hPrevWF : checkPartyWF compP0 stPrev = true)
    (hReachPrev : ∃ gR, ReachablePqxdhSession realP0 stPrev.me xPrev gR ∧
      gR.party = gPrev.party ∧ gR.session = gPrev.session)
    (hSendEq : checkSendEqReal stPrev mPrev rPrev = true)
    (_hsess₀ : st₀.session = some (x₀, g₀))
    (hMe : st₀.me = stPrev.me)
    (hx : recordExtrasEqBool x₀ xPrev = true)
    (hStep : optEqBool sessionStateEqBool
      (match SessionState.messageEncrypt compP0.C protoSignalCodec (pqxdhSpqrSession compP0)
          ((pqxdhSessionParamsFast compP0).sendAddrs gPrev.party) mPrev rPrev.toList gPrev.session with
       | (.ok _, s) => some s | (.error _, _) => none)
      (some g₀.session) = true)
    (hParty : g₀.party = gPrev.party) :
    ∃ gR, ReachablePqxdhSession realP0 st₀.me x₀ gR ∧ gR.party = g₀.party ∧ gR.session = g₀.session := by
  obtain ⟨gR₀, hR₀, hpR₀, hsR₀⟩ := hReachPrev
  have hxEq : x₀ = xPrev := eq_of_recordExtrasEqBool hx
  have hlenR₀ : (encodeRecordUnderExtras (fun _ => xPrev) gR₀).length < 2 ^ 31 := by
    have heqEnc : encodeRecordUnderExtras (fun _ => xPrev) gR₀ =
        encodeRecordUnderExtras (fun _ => xPrev) gPrev :=
      DY.Libsignal.Composed.Refinement.Cli.SDet.encodeRecordX_eq_of_pqSessionEquiv
        ⟨hpR₀, hsR₀, rfl, rfl, rfl, fun _ => rfl⟩
    rw [heqEnc]
    unfold checkPartyWF at hPrevWF
    simp only [Bool.and_eq_true, hPrevSess, decide_eq_true_eq] at hPrevWF
    exact hPrevWF.1.1.1.1.1.2
  have hSendStep := ReachablePqxdhSession.send (W := realP0) mPrev rPrev.toList hR₀ hlenR₀
  have hMapEq := sendMap_eq_of_checkSendEqAt realP0_eq_hybrid hSendEq
  rw [hPrevSess] at hMapEq
  simp only [Option.map_some, Option.some.injEq] at hMapEq
  rw [← pqxdhSessionParams_eq_fast' compP0, hpR₀.symm, hsR₀.symm] at hStep
  refine ⟨((pqxdhSessionParams realP0).send gR₀ mPrev rPrev.toList).1, ?_, ?_, ?_⟩
  · rw [hMe, hxEq]; exact hSendStep
  · rw [CryptoVerification.E2E.Record.send_eq_afterSend]
    rcases SessionState.messageEncrypt (pqxdhSessionParams realP0).C (pqxdhSessionParams realP0).codec
        (pqxdhSessionParams realP0).spqr ((pqxdhSessionParams realP0).sendAddrs gR₀.party)
        mPrev rPrev.toList gR₀.session with ⟨_ | _, _⟩ <;> exact hpR₀.trans hParty.symm
  · rw [CryptoVerification.E2E.Record.send_eq_afterSend]
    have hRealEq : SessionState.messageEncrypt (pqxdhSessionParams realP0).C (pqxdhSessionParams realP0).codec
        (pqxdhSessionParams realP0).spqr ((pqxdhSessionParams realP0).sendAddrs gR₀.party)
        mPrev rPrev.toList gR₀.session =
      SessionState.messageEncrypt compP0.C protoSignalCodec (pqxdhSpqrSession compP0)
        ((pqxdhSessionParams compP0).sendAddrs gPrev.party) mPrev rPrev.toList gPrev.session := by
      change SessionState.messageEncrypt realP0.C protoSignalCodec (pqxdhSpqrSession realP0)
          ((pqxdhSessionParams realP0).sendAddrs gR₀.party) mPrev rPrev.toList gR₀.session = _
      rw [hpR₀, hsR₀, ← hMapEq]
    rw [hRealEq]
    rcases hm : SessionState.messageEncrypt compP0.C protoSignalCodec (pqxdhSpqrSession compP0)
        ((pqxdhSessionParams compP0).sendAddrs gPrev.party) mPrev rPrev.toList gPrev.session with ⟨e | msg, s⟩
    · rw [hpR₀, hsR₀, hm] at hStep; cases hStep
    · rw [hpR₀, hsR₀, hm] at hStep
      exact eq_of_sessionStateEqBool' hStep

theorem reachReal_of_recvPrekey {stInit st₀ : PqParty} {m₀ : PreKeyMessageFields} {rc₀ : BitVec 256}
    {x₀ : RecordExtras} {g₀ : GhostState HwBytes}
    (hRecvEq : checkRecvPrekeyEqReal stInit m₀ rc₀ = true)
    (hsess₀ : st₀.session = some (x₀, g₀))
    (hMe : st₀.me = stInit.me)
    (hStep : optEqBool (optEqBool (optEqBool (prodEqBool recordExtrasEqBool ghostStateEqBool)))
      ((preKeysNamedBy stInit m₀).map fun k =>
        (recvPrekeyStateFast compP0 stInit.party stInit.me k m₀ rc₀).map
          (Option.map fun (x, g, _) => (x, g)))
      (some (some (some (x₀, g₀)))) = true) :
    ∃ gR, ReachablePqxdhSession realP0 st₀.me x₀ gR ∧ gR.party = g₀.party ∧ gR.session = g₀.session := by
  cases hk : preKeysNamedBy stInit m₀ with
  | none => rw [hk] at hStep; cases hStep
  | some k =>
    rw [hk] at hStep
    dsimp only [Option.map, optEqBool] at hStep
    cases hr : recvPrekeyStateFast compP0 stInit.party stInit.me k m₀ rc₀ with
    | none => rw [hr] at hStep; cases hStep
    | some o =>
      cases o with
      | none => rw [hr] at hStep; cases hStep
      | some tri =>
        rcases tri with ⟨x1, g1, pt1⟩
        rw [hr] at hStep
        dsimp only [Option.map, optEqBool, prodEqBool] at hStep
        rcases (Bool.and_eq_true _ _).mp hStep with ⟨hx1, hg1⟩
        have hxEq : x1 = x₀ := eq_of_recordExtrasEqBool hx1
        have hgEq : g1 = g₀ := eq_of_ghostStateEqBool hg1
        subst hxEq hgEq
        have hMap := recvMap_eq_of_checkRecvPrekeyEqAt realP0_eq_hybrid stInit.party stInit.me rfl rfl hRecvEq
        rw [hk] at hMap
        simp only [Option.map_some, Option.some.injEq] at hMap
        have hComp : recvPrekeyState dummyX compP0 stInit.party stInit.me k m₀ rc₀ =
            some (some (x1, g1, pt1)) := by
          rw [recvPrekeyState_eq_fast]; exact hr
        have hReal : recvPrekeyState dummyX realP0 stInit.party stInit.me k m₀ rc₀ =
            some (some (x1, g1, pt1)) := hMap.symm.trans hComp
        exact ⟨g1, hMe ▸ ReachablePqxdhSession.recvPrekey dummyX stInit.party stInit.me k m₀ rc₀ x1 g1 pt1 hReal,
          rfl, rfl⟩

/-! ## Setup-Key Membership Transfer and `encodeDir compP0 st = encodeDir realP0 st` -/

@[expose] def checkSecretInTable (sk : List.Vector (BitVec 8) 32) : Bool :=
  (compSecretIdx (CryptoGames.Ratchet.clampScalar sk).toList).isSome

@[expose] def checkPartyKeysInTable (st₀ : PqParty) : Bool :=
  checkSecretInTable st₀.me.idPriv &&
  st₀.signed.all (fun (_, k) => checkSecretInTable k.priv) &&
  st₀.oneTime.all (fun (_, opt) => match opt with | some sk => checkSecretInTable sk | none => true)

private theorem lookup_eq_some_of_mem_nodup {α β : Type} [DecidableEq α] :
    ∀ {l : List (α × β)} {k : α} {v : β},
      (l.map (·.1)).Nodup → (k, v) ∈ l → l.lookup k = some v
  | [], _, _, _, hmem => nomatch hmem
  | (k', v') :: tl, k, v, hnd, hmem => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hmem with ⟨rfl, rfl⟩ | htl
    · simp [List.lookup]
    · have hne : (k == k') = false := by
        apply beq_eq_false_iff_ne.mpr
        intro heq; subst heq
        exact hnd.1 (List.mem_map.mpr ⟨(k, v), htl, rfl⟩)
      simp [List.lookup, hne, lookup_eq_some_of_mem_nodup hnd.2 htl]

private theorem mem_of_lookup_eq_some {α β : Type} [DecidableEq α] :
    ∀ {l : List (α × β)} {k : α} {v : β}, l.lookup k = some v → (k, v) ∈ l
  | [], _, _, h => nomatch h
  | (k', v') :: tl, k, v, h => by
    simp only [List.lookup] at h
    cases hk : (k == k')
    · rw [hk] at h; exact List.mem_cons_of_mem _ (mem_of_lookup_eq_some h)
    · rw [hk] at h; injection h with hv; rw [beq_iff_eq.mp hk, hv]; exact List.mem_cons_self ..

private theorem keyPairOf_eq_of_checkSecretInTable {sk : List.Vector (BitVec 8) 32}
    (h : checkSecretInTable sk = true) :
    keyPairOf compP0.C sk = keyPairOf realP0.C sk := by
  unfold checkSecretInTable at h
  cases hidx : compSecretIdx (CryptoGames.Ratchet.clampScalar sk).toList with
  | none => rw [hidx] at h; cases h
  | some i =>
    unfold keyPairOf
    dsimp only [compP0, realP0, compHooks0, realCliHooks, CryptoGames.RFC7748.x25519PubFromSecretRef]
    congr 2
    apply List.Vector.eq
    exact compLookupPub_eq_x25519Pubkey_of_secretIdx hidx

private theorem encodeDir_eq_real_of_pqPartyEquiv {st st₀ : PqParty}
    (hst : PqPartyEquiv st st₀) (hKeys : checkPartyKeysInTable st₀ = true) :
    encodeDir compP0 st = encodeDir realP0 st := by
  unfold checkPartyKeysInTable at hKeys
  simp only [Bool.and_eq_true, List.all_eq_true] at hKeys
  rcases hKeys with ⟨⟨hMeKey, hSigKeys⟩, hOtKeys⟩
  unfold encodeDir
  have hMeEq : keyPairOf compP0.C st.me.idPriv = keyPairOf realP0.C st.me.idPriv := by
    rw [hst.me_eq]; exact keyPairOf_eq_of_checkSecretInTable hMeKey
  have hSigEq : st.signed.map (fun (i, k) => (signedPreKeyFile i, signedRecordBytes compP0.C i k)) =
      st.signed.map (fun (i, k) => (signedPreKeyFile i, signedRecordBytes realP0.C i k)) := by
    apply List.map_congr_left
    rintro ⟨id, k⟩ hmem
    have hlk : st₀.signed.lookup id = some k :=
      (hst.signed_lookup id).symm.trans (lookup_eq_some_of_mem_nodup hst.signed_nodup.1 hmem)
    have hkp := keyPairOf_eq_of_checkSecretInTable (hSigKeys (id, k) (mem_of_lookup_eq_some hlk))
    simp only [signedRecordBytes, hkp]
  have hOtEq : st.oneTime.map (fun x =>
        (oneTimePreKeyFile x.1, match x.2 with | some sk => oneTimeRecordBytes compP0.C x.1 sk | none => [])) =
      st.oneTime.map (fun x =>
        (oneTimePreKeyFile x.1, match x.2 with | some sk => oneTimeRecordBytes realP0.C x.1 sk | none => [])) := by
    apply List.map_congr_left
    rintro ⟨id, opt⟩ hmem
    cases opt with
    | none => rfl
    | some sk =>
      have hlk : st₀.oneTime.lookup id = some (some sk) :=
        (hst.oneTime_lookup id).symm.trans (lookup_eq_some_of_mem_nodup hst.oneTime_nodup.1 hmem)
      have hkp := keyPairOf_eq_of_checkSecretInTable (hOtKeys (id, some sk) (mem_of_lookup_eq_some hlk))
      simp only [oneTimeRecordBytes, hkp]
  rw [hMeEq]
  exact congrArg₂ List.append
    (congrArg₂ List.append
      (congrArg₂ List.append (congrArg₂ List.append rfl hSigEq) hOtEq)
      rfl)
    rfl

/-! ## `RawDir0` Invariant Separating Initiator vs Responder `ReachablePqxdhSession` -/

private theorem mergeBytes_encodeVarint_append' (v rest : HwBytes) (hlen : v.length < 2 ^ 64) :
    Proto.mergeBytes .lengthDelimited
      (Proto.encodeVarint (BitVec.ofNat 64 v.length) ++ (v ++ rest)) = .ok (v, rest) := by
  have hl : (BitVec.ofNat 64 v.length).toNat = v.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen]
  simp [Proto.mergeBytes, Proto.checkWireType, decodeVarint_encodeVarint_append,
    takeExact_eq_take_drop, hl, Bind.bind, Except.bind]

private theorem decodeKey_encodeKey_append' (tag : BitVec 32) (wt : Proto.WireType) (rest : HwBytes)
    (h : Proto.decodeKey (Proto.encodeKey tag wt) = .ok ((tag, wt), [])) :
    Proto.decodeKey (Proto.encodeKey tag wt ++ rest) = .ok ((tag, wt), rest) := by
  simpa using decodeKey_append_of_ok rest h

private theorem chainPB_dir_tag2 (m : ChainPB) (v : BitVec 64) (rest : HwBytes) (depth' : Nat) :
    ∃ m' : ChainPB, m'.direction = m.direction ∧
      Proto.mergeFieldsLoop ChainPB.mergeField
        (Proto.encodeUint64Field 2#32 v ++ rest).length m
        (Proto.encodeUint64Field 2#32 v ++ rest) depth' =
      Proto.mergeFieldsLoop ChainPB.mergeField rest.length m' rest depth' := by
  unfold Proto.encodeUint64Field
  by_cases hv : v == 0#64
  · exact ⟨m, rfl, by simp [hv]⟩
  · refine ⟨{ m with currentEpoch := v }, rfl, ?_⟩
    simp only [hv, Bool.false_eq_true, ↓reduceIte, List.append_assoc]
    have hdk := decodeKey_encodeKey_append' 2#32 .varint (Proto.encodeVarint v ++ rest) rfl
    have hmf : ChainPB.mergeField m 2#32 .varint (Proto.encodeVarint v ++ rest) depth' =
        .ok ({ m with currentEpoch := v }, rest) := by
      simp [ChainPB.mergeField, mergeUint64_encodeVarint_append, Bind.bind, Except.bind]
    exact (mergeFieldsLoop_step_of_ok protoPrefixStep_chainPB_mergeField
      m { m with currentEpoch := v } depth' hdk hmf).2

private theorem chainPB_dir_tag5 (m : ChainPB) (v : BitVec 64) (rest : HwBytes) (depth' : Nat) :
    ∃ m' : ChainPB, m'.direction = m.direction ∧
      Proto.mergeFieldsLoop ChainPB.mergeField
        (Proto.encodeUint64Field 5#32 v ++ rest).length m
        (Proto.encodeUint64Field 5#32 v ++ rest) depth' =
      Proto.mergeFieldsLoop ChainPB.mergeField rest.length m' rest depth' := by
  unfold Proto.encodeUint64Field
  by_cases hv : v == 0#64
  · exact ⟨m, rfl, by simp [hv]⟩
  · refine ⟨{ m with sendEpoch := v }, rfl, ?_⟩
    simp only [hv, Bool.false_eq_true, ↓reduceIte, List.append_assoc]
    have hdk := decodeKey_encodeKey_append' 5#32 .varint (Proto.encodeVarint v ++ rest) rfl
    have hmf : ChainPB.mergeField m 5#32 .varint (Proto.encodeVarint v ++ rest) depth' =
        .ok ({ m with sendEpoch := v }, rest) := by
      simp [ChainPB.mergeField, mergeUint64_encodeVarint_append, Bind.bind, Except.bind]
    exact (mergeFieldsLoop_step_of_ok protoPrefixStep_chainPB_mergeField
      m { m with sendEpoch := v } depth' hdk hmf).2

private theorem chainPB_dir_tag4 (m : ChainPB) (v rest : HwBytes) (depth' : Nat)
    (hlen : (Proto.encodeBytesField 4#32 v ++ rest).length < 2 ^ 64) :
    ∃ m' : ChainPB, m'.direction = m.direction ∧
      Proto.mergeFieldsLoop ChainPB.mergeField
        (Proto.encodeBytesField 4#32 v ++ rest).length m
        (Proto.encodeBytesField 4#32 v ++ rest) depth' =
      Proto.mergeFieldsLoop ChainPB.mergeField rest.length m' rest depth' := by
  unfold Proto.encodeBytesField at hlen ⊢
  by_cases hv : v.isEmpty
  · exact ⟨m, rfl, by simp [hv]⟩
  · refine ⟨{ m with nextRoot := v }, rfl, ?_⟩
    simp only [hv, Bool.false_eq_true, ↓reduceIte, Proto.encodeBytesUncond, List.append_assoc] at hlen ⊢
    have hv_len : v.length < 2 ^ 64 := by simp only [List.length_append] at hlen; omega
    have hdk := decodeKey_encodeKey_append' 4#32 .lengthDelimited
      (Proto.encodeVarint (BitVec.ofNat 64 v.length) ++ (v ++ rest)) rfl
    have hmf : ChainPB.mergeField m 4#32 .lengthDelimited
        (Proto.encodeVarint (BitVec.ofNat 64 v.length) ++ (v ++ rest)) depth' =
        .ok ({ m with nextRoot := v }, rest) := by
      simp [ChainPB.mergeField, mergeBytes_encodeVarint_append' v rest hv_len, Bind.bind, Except.bind]
    exact (mergeFieldsLoop_step_of_ok protoPrefixStep_chainPB_mergeField
      m { m with nextRoot := v } depth' hdk hmf).2

private theorem chainPB_dir_tag3_list :
    ∀ (links : List ChainEpochPB) (m ch' : ChainPB) (rest : HwBytes) (depth' : Nat),
      (Proto.encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 links ++ rest).length < 2 ^ 64 →
      1 ≤ depth' →
      Proto.mergeFieldsLoop ChainPB.mergeField
        (Proto.encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 links ++ rest).length m
        (Proto.encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 links ++ rest) depth' = .ok ch' →
      ∃ m' : ChainPB, m'.direction = m.direction ∧
        Proto.mergeFieldsLoop ChainPB.mergeField rest.length m' rest depth' = .ok ch'
  | [], m, ch', rest, _, _, _, hloop => ⟨m, rfl, hloop⟩
  | ep :: eps, m, ch', rest, depth', hlen, hdepth, hloop => by
    obtain ⟨d, rfl⟩ : ∃ d, depth' = d + 1 := ⟨depth' - 1, by omega⟩
    have hcons : Proto.encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 (ep :: eps) ++ rest =
        Proto.encodeMessage ChainEpochPB.encodeRaw 3#32 ep ++
          (Proto.encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 eps ++ rest) := by
      simp [Proto.encodeRepeatedMessage, List.append_assoc]
    rw [hcons] at hlen hloop
    let rest1 := Proto.encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 eps ++ rest
    have hraw_len : (ChainEpochPB.encodeRaw ep).length < 2 ^ 64 := by
      simp only [Proto.encodeMessage, List.length_append] at hlen; omega
    have hl : (BitVec.ofNat 64 (ChainEpochPB.encodeRaw ep).length).toNat =
        (ChainEpochPB.encodeRaw ep).length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hraw_len]
    have hdk : Proto.decodeKey (Proto.encodeMessage ChainEpochPB.encodeRaw 3#32 ep ++ rest1) =
        .ok ((3#32, .lengthDelimited),
          Proto.encodeVarint (BitVec.ofNat 64 (ChainEpochPB.encodeRaw ep).length) ++
            (ChainEpochPB.encodeRaw ep ++ rest1)) := by
      simp only [Proto.encodeMessage, List.append_assoc]
      exact decodeKey_encodeKey_append' 3#32 .lengthDelimited _ rfl
    rcases hsub : Proto.mergeFieldsLoop ChainEpochPB.mergeField
        (ChainEpochPB.encodeRaw ep).length default (ChainEpochPB.encodeRaw ep) d with e | ep'
    · have hmf_err : ChainPB.mergeField m 3#32 .lengthDelimited
          (Proto.encodeVarint (BitVec.ofNat 64 (ChainEpochPB.encodeRaw ep).length) ++
            (ChainEpochPB.encodeRaw ep ++ rest1)) (d + 1) = .error e := by
        simp [ChainPB.mergeField, Proto.mergeRepeatedMessage, Proto.mergeMessage, Proto.checkWireType,
          decodeVarint_encodeVarint_append, takeExact_eq_take_drop, hl, hsub, Bind.bind, Except.bind]
      cases hs : Proto.encodeMessage ChainEpochPB.encodeRaw 3#32 ep ++ rest1 with
      | nil => rw [hs] at hdk; nomatch hdk
      | cons b tl =>
        rw [hs] at hloop hdk
        simp only [Proto.mergeFieldsLoop, List.length_cons, hdk, hmf_err, Bind.bind, Except.bind] at hloop
        nomatch hloop
    · have hmf_ok : ChainPB.mergeField m 3#32 .lengthDelimited
          (Proto.encodeVarint (BitVec.ofNat 64 (ChainEpochPB.encodeRaw ep).length) ++
            (ChainEpochPB.encodeRaw ep ++ rest1)) (d + 1) =
          .ok ({ m with links := m.links ++ [ep'] }, rest1) := by
        simp [ChainPB.mergeField, Proto.mergeRepeatedMessage, Proto.mergeMessage, Proto.checkWireType,
          decodeVarint_encodeVarint_append, takeExact_eq_take_drop, hl, hsub, Bind.bind, Except.bind]
      have hstep := (mergeFieldsLoop_step_of_ok protoPrefixStep_chainPB_mergeField
        m { m with links := m.links ++ [ep'] } (d + 1) hdk hmf_ok).2
      rw [hstep] at hloop
      have hlen' : rest1.length < 2 ^ 64 := by
        dsimp only [rest1]
        simp only [List.length_append] at hlen ⊢
        omega
      obtain ⟨m2, hm2, hloop2⟩ :=
        chainPB_dir_tag3_list eps { m with links := m.links ++ [ep'] } ch' rest (d + 1) hlen' hdepth hloop
      exact ⟨m2, hm2, hloop2⟩

private theorem chainPB_dir_tag6 (m ch' : ChainPB) (opt : Option ChainParamsPB) (depth' : Nat)
    (hlen : (Proto.encodeOptMessage ChainParamsPB.encodeRaw 6#32 opt).length < 2 ^ 64)
    (hdepth : 1 ≤ depth')
    (hloop : Proto.mergeFieldsLoop ChainPB.mergeField
      (Proto.encodeOptMessage ChainParamsPB.encodeRaw 6#32 opt).length m
      (Proto.encodeOptMessage ChainParamsPB.encodeRaw 6#32 opt) depth' = .ok ch') :
    ch'.direction = m.direction := by
  cases opt with
  | none =>
    simp only [Proto.encodeOptMessage, Proto.mergeFieldsLoop] at hloop
    injection hloop with h; subst h; rfl
  | some p =>
    obtain ⟨d, rfl⟩ : ∃ d, depth' = d + 1 := ⟨depth' - 1, by omega⟩
    have hraw_len : (ChainParamsPB.encodeRaw p).length < 2 ^ 64 := by
      simp only [Proto.encodeOptMessage, Proto.encodeMessage, List.length_append] at hlen; omega
    have hl : (BitVec.ofNat 64 (ChainParamsPB.encodeRaw p).length).toNat =
        (ChainParamsPB.encodeRaw p).length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hraw_len]
    have hdk : Proto.decodeKey (Proto.encodeOptMessage ChainParamsPB.encodeRaw 6#32 (some p)) =
        .ok ((6#32, .lengthDelimited),
          Proto.encodeVarint (BitVec.ofNat 64 (ChainParamsPB.encodeRaw p).length) ++
            ChainParamsPB.encodeRaw p) := by
      simp only [Proto.encodeOptMessage, Proto.encodeMessage, List.append_assoc]
      exact decodeKey_encodeKey_append' 6#32 .lengthDelimited _ rfl
    rcases hsub : Proto.mergeFieldsLoop ChainParamsPB.mergeField
        (ChainParamsPB.encodeRaw p).length (m.params.getD default) (ChainParamsPB.encodeRaw p) d with e | p'
    · have hmf_err : ChainPB.mergeField m 6#32 .lengthDelimited
          (Proto.encodeVarint (BitVec.ofNat 64 (ChainParamsPB.encodeRaw p).length) ++
            ChainParamsPB.encodeRaw p) (d + 1) = .error e := by
        have happ : Proto.encodeVarint (BitVec.ofNat 64 (ChainParamsPB.encodeRaw p).length) ++
            ChainParamsPB.encodeRaw p =
          Proto.encodeVarint (BitVec.ofNat 64 (ChainParamsPB.encodeRaw p).length) ++
            (ChainParamsPB.encodeRaw p ++ []) := by simp
        rw [happ]
        simp [ChainPB.mergeField, Proto.mergeOptMessage, Proto.mergeMessage, Proto.checkWireType,
          decodeVarint_encodeVarint_append, takeExact_eq_take_drop, hl, hsub, Bind.bind, Except.bind]
      cases hs : Proto.encodeOptMessage ChainParamsPB.encodeRaw 6#32 (some p) with
      | nil => rw [hs] at hdk; nomatch hdk
      | cons b tl =>
        rw [hs] at hloop hdk
        simp only [Proto.mergeFieldsLoop, List.length_cons, hdk, hmf_err, Bind.bind, Except.bind] at hloop
        nomatch hloop
    · have hmf_ok : ChainPB.mergeField m 6#32 .lengthDelimited
          (Proto.encodeVarint (BitVec.ofNat 64 (ChainParamsPB.encodeRaw p).length) ++
            ChainParamsPB.encodeRaw p) (d + 1) = .ok ({ m with params := some p' }, []) := by
        have happ : Proto.encodeVarint (BitVec.ofNat 64 (ChainParamsPB.encodeRaw p).length) ++
            ChainParamsPB.encodeRaw p =
          Proto.encodeVarint (BitVec.ofNat 64 (ChainParamsPB.encodeRaw p).length) ++
            (ChainParamsPB.encodeRaw p ++ []) := by simp
        rw [happ]
        simp [ChainPB.mergeField, Proto.mergeOptMessage, Proto.mergeMessage, Proto.checkWireType,
          decodeVarint_encodeVarint_append, takeExact_eq_take_drop, hl, hsub, Bind.bind, Except.bind]
      have hstep := (mergeFieldsLoop_step_of_ok protoPrefixStep_chainPB_mergeField
        m { m with params := some p' } (d + 1) hdk hmf_ok).2
      rw [hstep, mergeFieldsLoop_nil] at hloop
      injection hloop with h; subst h; rfl

private theorem chainPB_mergeFieldsLoop_encodeRaw_dir0 {ch ch' : ChainPB} {depth' : Nat}
    (hdir0 : ch.direction = 0#32)
    (hlen : (ChainPB.encodeRaw ch).length < 2 ^ 64)
    (hdepth : 1 ≤ depth')
    (hloop : Proto.mergeFieldsLoop ChainPB.mergeField
      (ChainPB.encodeRaw ch).length default (ChainPB.encodeRaw ch) depth' = .ok ch') :
    ch'.direction = 0#32 := by
  have h1 : Proto.encodeInt32Field 1#32 ch.direction = [] := by simp [Proto.encodeInt32Field, hdir0]
  have hraw : ChainPB.encodeRaw ch =
      Proto.encodeUint64Field 2#32 ch.currentEpoch ++
      (Proto.encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 ch.links ++
      (Proto.encodeBytesField 4#32 ch.nextRoot ++
      (Proto.encodeUint64Field 5#32 ch.sendEpoch ++
       Proto.encodeOptMessage ChainParamsPB.encodeRaw 6#32 ch.params))) := by
    unfold ChainPB.encodeRaw; rw [h1]; simp [List.append_assoc]
  rw [hraw] at hlen hloop
  obtain ⟨m2, hm2, hs2⟩ := chainPB_dir_tag2 default ch.currentEpoch _ depth'
  rw [hs2] at hloop
  have hl3 : (Proto.encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 ch.links ++
      (Proto.encodeBytesField 4#32 ch.nextRoot ++
      (Proto.encodeUint64Field 5#32 ch.sendEpoch ++
       Proto.encodeOptMessage ChainParamsPB.encodeRaw 6#32 ch.params))).length < 2 ^ 64 := by
    simp only [List.length_append] at hlen ⊢; omega
  obtain ⟨m3, hm3, hloop3⟩ := chainPB_dir_tag3_list ch.links m2 ch' _ depth' hl3 hdepth hloop
  have hl4 : (Proto.encodeBytesField 4#32 ch.nextRoot ++
      (Proto.encodeUint64Field 5#32 ch.sendEpoch ++
       Proto.encodeOptMessage ChainParamsPB.encodeRaw 6#32 ch.params)).length < 2 ^ 64 := by
    simp only [List.length_append] at hl3 ⊢; omega
  obtain ⟨m4, hm4, hs4⟩ := chainPB_dir_tag4 m3 ch.nextRoot _ depth' hl4
  rw [hs4] at hloop3
  obtain ⟨m5, hm5, hs5⟩ := chainPB_dir_tag5 m4 ch.sendEpoch _ depth'
  rw [hs5] at hloop3
  have hl6 : (Proto.encodeOptMessage ChainParamsPB.encodeRaw 6#32 ch.params).length < 2 ^ 64 := by
    simp only [List.length_append] at hl4 ⊢; omega
  have hm6 := chainPB_dir_tag6 m5 ch' ch.params depth' hl6 hdepth hloop3
  exact hm6.trans (hm5.trans (hm4.trans (hm3.trans hm2)))

private def encodeOptInnerLocal : Option PqRatchetState.Inner → HwBytes
  | none => []
  | some i => PqRatchetState.Inner.encode i

private theorem pqRatchetState_step_tag3_local
    (m1 st : PqRatchetState) (optInner : Option PqRatchetState.Inner) (d : Nat)
    (hlen : (encodeOptInnerLocal optInner).length < 2 ^ 64)
    (hloop : Proto.mergeFieldsLoop PqRatchetState.mergeField
      (encodeOptInnerLocal optInner).length m1 (encodeOptInnerLocal optInner) (d + 1) = .ok st) :
    st.versionNegotiation = m1.versionNegotiation ∧ st.chain = m1.chain := by
  cases optInner with
  | none =>
    dsimp only [encodeOptInnerLocal] at hloop
    rw [mergeFieldsLoop_nil] at hloop
    injection hloop with hst
    subst hst
    exact ⟨rfl, rfl⟩
  | some inner =>
    cases inner with
    | v1 v =>
      dsimp only [encodeOptInnerLocal, PqRatchetState.Inner.encode] at hlen hloop
      have hv_len : (V1State.encodeRaw v).length < 2 ^ 64 := by
        unfold Proto.encodeMessage at hlen
        simp only [List.length_append] at hlen
        omega
      rw [← List.append_nil (Proto.encodeMessage V1State.encodeRaw 3#32 v)] at hloop
      have hstep := mergeFieldsLoop_encodeMessage protoPrefixStep_pqRatchetState_mergeField
        V1State.mergeField V1State.encodeRaw
        (fun m v' => { m with inner := some (.v1 v') })
        m1 (match m1.inner with | some (.v1 v0) => v0 | none => default) v 3#32 [] d
        (by decide) (by decide) hv_len
        (by intro bs
            simp only [PqRatchetState.mergeField, PqRatchetState.Inner.merge]
            rcases m1.inner with _ | ⟨v0⟩ <;>
              cases Proto.mergeMessage V1State.mergeField .lengthDelimited _ bs (d + 1) <;> rfl)
      rw [hstep] at hloop
      rcases hv_loop : Proto.mergeFieldsLoop V1State.mergeField
          (V1State.encodeRaw v).length (match m1.inner with | some (.v1 v0) => v0 | none => default)
          (V1State.encodeRaw v) d with e | v'
      · rw [hv_loop] at hloop
        nomatch hloop
      · rw [hv_loop] at hloop
        dsimp only [Bind.bind, Except.bind] at hloop
        rw [mergeFieldsLoop_nil] at hloop
        injection hloop with hst
        subst hst
        exact ⟨rfl, rfl⟩

private theorem pqRatchetState_decode_encodeRaw_dir0 {m st : PqRatchetState}
    (hlen : (PqRatchetState.encodeRaw m).length < 2 ^ 64)
    (hch0 : ∀ c ∈ m.chain, c.direction = 0#32)
    (hdec : PqRatchetState.decode (PqRatchetState.encodeRaw m) = .ok st) :
    (∀ c ∈ st.chain, c.direction = 0#32) ∧ st.versionNegotiation = m.versionNegotiation := by
  change Proto.mergeFieldsLoop PqRatchetState.mergeField
    (PqRatchetState.encodeRaw m).length default (PqRatchetState.encodeRaw m) (99 + 1) = .ok st at hdec
  have hraw : PqRatchetState.encodeRaw m =
      Proto.encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 m.versionNegotiation ++
      (Proto.encodeOptMessage ChainPB.encodeRaw 2#32 m.chain ++ encodeOptInnerLocal m.inner) := by
    unfold PqRatchetState.encodeRaw encodeOptInnerLocal
    cases m.inner <;> simp [List.append_assoc]
  rw [hraw] at hlen hdec
  rw [pqRatchetState_step_tag1 default m.versionNegotiation _ 99 rfl hlen (by decide)] at hdec
  have hlen2 : (Proto.encodeOptMessage ChainPB.encodeRaw 2#32 m.chain ++
      encodeOptInnerLocal m.inner).length < 2 ^ 64 := by
    simp only [List.length_append] at hlen ⊢; omega
  let m0 : PqRatchetState := { (default : PqRatchetState) with versionNegotiation := m.versionNegotiation }
  cases hopt : m.chain with
  | none =>
    rw [hopt] at hlen2 hdec
    dsimp only [Proto.encodeOptMessage, List.nil_append] at hlen2 hdec
    obtain ⟨hvn, hch⟩ := pqRatchetState_step_tag3_local m0 st m.inner 99 hlen2 hdec
    exact ⟨(fun c hc => by rw [hch] at hc; nomatch hc), hvn⟩
  | some ch =>
    rw [hopt] at hlen2 hdec
    have hsub : (ChainPB.encodeRaw ch).length < 2 ^ 64 := by
      unfold Proto.encodeOptMessage Proto.encodeMessage at hlen2
      simp only [List.length_append] at hlen2; omega
    dsimp only [Proto.encodeOptMessage] at hdec
    rw [mergeFieldsLoop_encodeMessage protoPrefixStep_pqRatchetState_mergeField
          ChainPB.mergeField ChainPB.encodeRaw
          (fun x v => { x with chain := some v })
          m0 (m0.chain.getD default) ch 2#32 (encodeOptInnerLocal m.inner) 99
          (by decide) (by decide) hsub
          (by intro bs
              simp only [PqRatchetState.mergeField, Proto.mergeOptMessage]
              cases Proto.mergeMessage ChainPB.mergeField .lengthDelimited
                (m0.chain.getD default) bs 100 <;> rfl)] at hdec
    have hm0c : m0.chain = none := rfl
    rw [hm0c] at hdec
    dsimp only [Option.getD] at hdec
    rcases hch_loop : Proto.mergeFieldsLoop ChainPB.mergeField
        (ChainPB.encodeRaw ch).length default (ChainPB.encodeRaw ch) 99 with e | ch'
    · rw [hch_loop] at hdec; nomatch hdec
    · rw [hch_loop] at hdec
      dsimp only [Bind.bind, Except.bind] at hdec
      have hlen3 : (encodeOptInnerLocal m.inner).length < 2 ^ 64 := by
        unfold Proto.encodeOptMessage Proto.encodeMessage at hlen2
        simp only [List.length_append] at hlen2; omega
      obtain ⟨hvn, hch⟩ := pqRatchetState_step_tag3_local { m0 with chain := some ch' } st m.inner 99 hlen3 hdec
      have hd0 := chainPB_mergeFieldsLoop_encodeRaw_dir0 (hch0 ch (by simp [hopt])) hsub (by decide) hch_loop
      refine ⟨fun c hc => ?_, hvn⟩
      rw [hch] at hc; simp only [Option.mem_def, Option.some.injEq] at hc; subst hc; exact hd0

private def RawDir0 (bs : HwBytes) : Prop :=
  bs = [] ∨
  ∃ m : PqRatchetState, bs = PqRatchetState.encodeRaw m ∧
    (∀ c ∈ m.chain, c.direction = 0#32) ∧
    (∀ vn ∈ m.versionNegotiation, vn.direction = 0#32)

private theorem rawDir0_spqrV1Init_a2b (W : PEParams) (k : BitVec 256) :
    RawDir0 ((pqxdhSpqrSession W).init .a2b k) := by
  change RawDir0 (spqrV1InitialStateFor (spqrDeps W.C.F W.Q.K) .a2b k)
  unfold spqrV1InitialStateFor initialState libsignalSpqrParams Direction.ofSpqrDirection
  dsimp only [SpqrApiResult.ofPanic, Bind.bind, Except.bind]
  cases CryptoVerification.LibsignalSpqrV1.initInner (spqrDeps W.C.F W.Q.K) .v1 .a2b (keyToBytes32 k) with
  | error _ => exact Or.inl rfl
  | ok inner =>
    right
    refine ⟨pbToPqRatchetState
      { inner := inner
        chain := none
        versionNegotiation := some
          { authKey := keyToBytes32 k
            direction := Direction.a2b.toI32
            minVersion := CryptoVerification.LibsignalSpqrV1.Version.v1.toI32
            chainParams := some (libsignalChainParams false).intoPb } },
      rfl, (fun _ hc => by nomatch hc), fun vn hvn => ?_⟩
    simp only [pbToPqRatchetState, Option.mem_def, Option.some.injEq] at hvn
    subst hvn; rfl

private theorem chain_dir_fromPb {pb : ChainPB} {c : Chain}
    (h0 : pb.direction = 0#32) (h : Chain.fromPb pb = .ok c) : c.dir = .a2b := by
  unfold Chain.fromPb at h
  rw [h0] at h
  have hd : Direction.fromI32? 0#32 = some .a2b := rfl
  rw [hd] at h
  dsimp only [Bind.bind, Except.bind] at h
  rcases hlinks : Chain.linksFromPb pb.links with _ | links
  · rw [hlinks] at h; nomatch h
  · rw [hlinks] at h; dsimp only at h
    cases hpar : pb.params with
    | none => rw [hpar] at h; nomatch h
    | some p => rw [hpar] at h; injection h with hc; subst hc; rfl

private theorem chain_dir_fromVN (hkdf : CryptoVerification.LibsignalSpqrV1.HkdfFn)
    {vn : VersionNegotiationPB} {c : Chain}
    (h0 : vn.direction = 0#32) (h : chainFromVersionNegotiation hkdf vn = .ok c) : c.dir = .a2b := by
  unfold chainFromVersionNegotiation at h
  rw [h0] at h
  have hd : Direction.fromI32? 0#32 = some .a2b := rfl
  rw [hd] at h
  dsimp only [Bind.bind, Except.bind] at h
  cases hcp : vn.chainParams with
  | none => rw [hcp] at h; nomatch h
  | some p =>
    rw [hcp] at h; dsimp only at h
    unfold Chain.new at h; injection h with hc; subst hc; rfl

private theorem chain_dir_chainFrom (hkdf : CryptoVerification.LibsignalSpqrV1.HkdfFn)
    {pb : Option ChainPB} {vn : Option VersionNegotiationPB} {c : Chain}
    (hch : ∀ x ∈ pb, x.direction = 0#32)
    (hvn : ∀ x ∈ vn, x.direction = 0#32)
    (h : chainFrom hkdf pb vn = .ok c) : c.dir = .a2b := by
  cases pb with
  | some p => exact chain_dir_fromPb (hch p rfl) h
  | none =>
    cases vn with
    | none => nomatch h
    | some v => exact chain_dir_fromVN hkdf (hvn v rfl) h

private theorem chain_dir_addEpoch (hkdf : CryptoVerification.LibsignalSpqrV1.HkdfFn)
    {c c' : Chain} {ep : CryptoVerification.LibsignalSpqrV1.EpochSecret}
    (h : c.addEpoch hkdf ep = .ok c') : c'.dir = c.dir := by
  unfold Chain.addEpoch at h
  split_ifs at h
  injection h with hc; subst hc; rfl

private theorem chain_dir_sendKey (hkdf : CryptoVerification.LibsignalSpqrV1.HkdfFn)
    {c c' : Chain} {ep : CryptoVerification.LibsignalSpqrV1.Epoch} {out : BitVec 32 × HwBytes}
    (h : c.sendKey hkdf ep = .ok (c', out)) : c'.dir = c.dir := by
  unfold Chain.sendKey at h
  by_cases hlt : ep < c.sendEpoch
  · simp [hlt] at h
  · simp only [hlt, ↓reduceIte] at h
    rcases hc0 : ChainResult.ofError (c.epochIdx ep) with _ | idx0
    · simp [hc0, Bind.bind, Except.bind] at h
    · simp only [hc0, Bind.bind, Except.bind] at h
      by_cases hne : (c.sendEpoch != ep) = true
      · simp only [hne, ↓reduceIte] at h
        split at h
        · nomatch h
        · next link _ =>
          rcases hnk : CryptoVerification.LibsignalSpqrV1.ChainResult.ofPanic (link.send.nextKey hkdf) with _ | r
          · simp [hnk] at h
          · rcases r with ⟨send', out'⟩
            simp [hnk, pure, Except.pure] at h
            rcases h with ⟨rfl, _⟩; rfl
      · simp only [hne, Bool.false_eq_true, ↓reduceIte] at h
        split at h
        · nomatch h
        · next link _ =>
          rcases hnk : CryptoVerification.LibsignalSpqrV1.ChainResult.ofPanic (link.send.nextKey hkdf) with _ | r
          · simp [hnk] at h
          · rcases r with ⟨send', out'⟩
            simp [hnk, pure, Except.pure] at h
            rcases h with ⟨rfl, _⟩; rfl

private theorem chain_dir_recvKey (hkdf : CryptoVerification.LibsignalSpqrV1.HkdfFn)
    {c c' : Chain} {ep : CryptoVerification.LibsignalSpqrV1.Epoch} {idx : BitVec 32} {out : HwBytes}
    (h : c.recvKey hkdf ep idx = .ok (c', out)) : c'.dir = c.dir := by
  unfold Chain.recvKey at h
  split_ifs at h
  · injection h with hp; injection hp with hc _; subst hc; rfl
  · rcases hc0 : ChainResult.ofError (c.epochIdx ep) with _ | idx0
    · simp [hc0, Bind.bind, Except.bind] at h
    · simp only [hc0, Bind.bind, Except.bind] at h
      split at h
      · nomatch h
      · next link _ =>
        rcases hk : link.recv.key hkdf idx c.params with _ | r
        · simp [hk] at h
        · simp [hk, pure, Except.pure] at h; rcases h with ⟨rfl, _⟩; rfl

private theorem decodeState_spqrDeps_dir0 (F : CryptoGames.LibsignalSession.ShaCompress)
    (K : CryptoVerification.LibsignalSpqrV1.MlKem) {bs : HwBytes}
    {stPb : CryptoVerification.LibsignalSpqrV1.PqRatchetStatePB CryptoVerification.LibsignalSpqrV1.V1State}
    (hraw : RawDir0 bs) (hlen : bs.length < 2 ^ 64)
    (hdec : decodeState (spqrDeps F K) bs = .ok stPb) :
    (∀ c ∈ stPb.chain, c.direction = 0#32) ∧
    (∀ vn ∈ stPb.versionNegotiation, vn.direction = 0#32) := by
  unfold decodeState at hdec
  by_cases hemp : bs.isEmpty
  · simp only [hemp, ↓reduceIte] at hdec
    injection hdec with h; subst h
    exact ⟨(fun _ hc => by nomatch hc), (fun _ hv => by nomatch hv)⟩
  · simp only [hemp, Bool.false_eq_true, ↓reduceIte, spqrDeps] at hdec
    rcases hraw with rfl | ⟨m, rfl, hch0, hvn0⟩
    · simp at hemp
    · rcases hd : Proto.decodeState (PqRatchetState.encodeRaw m) with _ | st
      · rw [hd] at hdec; nomatch hdec
      · rw [hd] at hdec; injection hdec with h; subst h
        obtain ⟨hch', hvn'⟩ := pqRatchetState_decode_encodeRaw_dir0 hlen hch0 hd
        exact ⟨hch', fun vn hv => hvn0 vn (hvn' ▸ hv)⟩

private theorem rawDir0_spqrSend (W : PEParams) {bs newBs msg : HwBytes} { tape : HwBytes }
    {key : CryptoGames.HKDF.Salt}
    (hraw : RawDir0 bs) (hlen : bs.length < 2 ^ 64)
    (hsend : (pqxdhSpqrSession W).send bs tape = some (newBs, key, msg)) :
    RawDir0 newBs := by
  change (toSpqrModel (spqrDeps W.C.F W.Q.K) (spqrHkdfWith W.C.F)).send bs tape =
    some (newBs, key, msg) at hsend
  unfold toSpqrModel at hsend
  dsimp only at hsend
  rcases hs : (CryptoVerification.LibsignalSpqrV1.send (spqrDeps W.C.F W.Q.K) (spqrHkdfWith W.C.F) bs tape).1 with e | sOut
  · rw [hs] at hsend; cases hsend
  · rw [hs] at hsend; dsimp only at hsend
    cases hm : CryptoVerification.LibsignalSpqrV1.messageKeyToSalt? sOut.key with
    | none => rw [hm] at hsend; cases hsend
    | some sk =>
      rw [hm] at hsend; simp only [Option.some.injEq, Prod.mk.injEq] at hsend
      rcases hsend with ⟨rfl, _, _⟩
      unfold CryptoVerification.LibsignalSpqrV1.send at hs
      rcases hd : decodeState (spqrDeps W.C.F W.Q.K) bs with _ | statePb
      · simp [hd] at hs
      · obtain ⟨hch0, hvn0⟩ := decodeState_spqrDeps_dir0 W.C.F W.Q.K hraw hlen hd
        simp only [hd] at hs
        cases hinner : statePb.inner with
        | none => simp [hinner] at hs; subst hs; exact Or.inl rfl
        | some pb =>
          simp only [hinner] at hs
          rcases hst0 : (spqrDeps W.C.F W.Q.K).statesFromPb pb with _ | st0
          · simp [hst0] at hs
          · simp only [hst0] at hs
            rcases hss : (spqrDeps W.C.F W.Q.K).statesSend st0 tape with ⟨_ | ⟨mV1, kOpt, st1⟩, tape'⟩
            · simp [hss] at hs
            · simp only [hss] at hs
              unfold sendAfterStates at hs
              cases hcpb : statePb.chain with
              | some cpb =>
                rw [hcpb] at hs
                rcases hfp : Chain.fromPb cpb with _ | c
                · simp only [hfp, CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofError,
                    Bind.bind, Except.bind] at hs
                  nomatch hs
                · have hd0 : c.dir = .a2b := chain_dir_fromPb (hch0 cpb (by simp [hcpb])) hfp
                  simp only [hfp, CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofError,
                    Bind.bind, Except.bind, pure, Except.pure] at hs
                  cases kOpt with
                  | none =>
                    dsimp only at hs
                    by_cases hep0 : ((spqrDeps W.C.F W.Q.K).msgEpoch mV1 == 0#64) = true
                    · simp only [hep0, ↓reduceIte] at hs; nomatch hs
                    · simp only [hep0, Bool.false_eq_true, ↓reduceIte] at hs
                      rcases hsk : c.sendKey (spqrHkdfWith W.C.F)
                          ((spqrDeps W.C.F W.Q.K).msgEpoch mV1 - 1#64) with _ | ⟨chain2, idx, mk⟩
                      · simp only [hsk, CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainResult] at hs
                        nomatch hs
                      · have hd2 : chain2.dir = .a2b := (chain_dir_sendKey _ hsk).trans hd0
                        simp only [hsk, CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainResult] at hs
                        cases hms : (spqrDeps W.C.F W.Q.K).msgSerialize mV1 idx with
                        | nil => rw [hms] at hs; nomatch hs
                        | cons b0 tl =>
                          rw [hms] at hs; dsimp only at hs
                          by_cases hbv : (b0 != CryptoVerification.LibsignalSpqrV1.Version.v1.toU8) = true
                          · simp only [hbv, ↓reduceIte] at hs; nomatch hs
                          · simp only [hbv, Bool.false_eq_true, ↓reduceIte] at hs
                            injection hs with hsOut; subst hsOut
                            refine Or.inr ⟨pbToPqRatchetState
                              { inner := some ((spqrDeps W.C.F W.Q.K).statesIntoPb st1)
                                versionNegotiation := statePb.versionNegotiation
                                chain := some chain2.intoPb }, rfl, fun c' hc' => ?_, hvn0⟩
                            simp only [pbToPqRatchetState, Option.mem_def, Option.some.injEq] at hc'
                            subst hc'; simp [Chain.intoPb, hd2]; rfl
                  | some es =>
                    dsimp only at hs
                    rcases hae : c.addEpoch (spqrHkdfWith W.C.F) es with _ | chain1
                    · simp only [hae, CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainPanic] at hs
                      nomatch hs
                    · have hd1 : chain1.dir = .a2b := (chain_dir_addEpoch _ hae).trans hd0
                      simp only [hae, CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainPanic] at hs
                      by_cases hep0 : ((spqrDeps W.C.F W.Q.K).msgEpoch mV1 == 0#64) = true
                      · simp only [hep0, ↓reduceIte] at hs; nomatch hs
                      · simp only [hep0, Bool.false_eq_true, ↓reduceIte] at hs
                        rcases hsk : chain1.sendKey (spqrHkdfWith W.C.F)
                            ((spqrDeps W.C.F W.Q.K).msgEpoch mV1 - 1#64) with _ | ⟨chain2, idx, mk⟩
                        · simp only [hsk, CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainResult] at hs
                          nomatch hs
                        · have hd2 : chain2.dir = .a2b := (chain_dir_sendKey _ hsk).trans hd1
                          simp only [hsk, CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainResult] at hs
                          cases hms : (spqrDeps W.C.F W.Q.K).msgSerialize mV1 idx with
                          | nil => rw [hms] at hs; nomatch hs
                          | cons b0 tl =>
                            rw [hms] at hs; dsimp only at hs
                            by_cases hbv : (b0 != CryptoVerification.LibsignalSpqrV1.Version.v1.toU8) = true
                            · simp only [hbv, ↓reduceIte] at hs; nomatch hs
                            · simp only [hbv, Bool.false_eq_true, ↓reduceIte] at hs
                              injection hs with hsOut; subst hsOut
                              refine Or.inr ⟨pbToPqRatchetState
                                { inner := some ((spqrDeps W.C.F W.Q.K).statesIntoPb st1)
                                  versionNegotiation := statePb.versionNegotiation
                                  chain := some chain2.intoPb }, rfl, fun c' hc' => ?_, hvn0⟩
                              simp only [pbToPqRatchetState, Option.mem_def, Option.some.injEq] at hc'
                              subst hc'; simp [Chain.intoPb, hd2]; rfl
              | none =>
                rw [hcpb] at hs
                cases hvnpb : statePb.versionNegotiation with
                | none =>
                  simp only [hvnpb, Bind.bind, Except.bind] at hs
                  nomatch hs
                | some vn =>
                  have hvnDir : ∀ vn' ∈ (some vn : Option VersionNegotiationPB), vn'.direction = 0#32 := by
                    intro vn' hvn'
                    simp only [Option.mem_def, Option.some.injEq] at hvn'
                    subst hvn'
                    exact hvn0 vn (by simp [hvnpb])
                  rw [hvnpb] at hs
                  by_cases hslt : BitVec.slt CryptoVerification.LibsignalSpqrV1.Version.v0.toI32 vn.minVersion = true
                  · simp only [hslt, ↓reduceIte] at hs
                    rcases hcf : chainFromVersionNegotiation (spqrHkdfWith W.C.F) vn with _ | c
                    · simp only [hcf, CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofError,
                        Bind.bind, Except.bind] at hs
                      nomatch hs
                    · have hd0 : c.dir = .a2b := chain_dir_fromVN _ (hvn0 vn (by simp [hvnpb])) hcf
                      simp only [hcf, CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofError,
                        Bind.bind, Except.bind, pure, Except.pure] at hs
                      cases kOpt with
                      | none =>
                        dsimp only at hs
                        by_cases hep0 : ((spqrDeps W.C.F W.Q.K).msgEpoch mV1 == 0#64) = true
                        · simp only [hep0, ↓reduceIte] at hs; nomatch hs
                        · simp only [hep0, Bool.false_eq_true, ↓reduceIte] at hs
                          rcases hsk : c.sendKey (spqrHkdfWith W.C.F)
                              ((spqrDeps W.C.F W.Q.K).msgEpoch mV1 - 1#64) with _ | ⟨chain2, idx, mk⟩
                          · simp only [hsk, CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainResult] at hs
                            nomatch hs
                          · have hd2 : chain2.dir = .a2b := (chain_dir_sendKey _ hsk).trans hd0
                            simp only [hsk, CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainResult] at hs
                            cases hms : (spqrDeps W.C.F W.Q.K).msgSerialize mV1 idx with
                            | nil => rw [hms] at hs; nomatch hs
                            | cons b0 tl =>
                              rw [hms] at hs; dsimp only at hs
                              by_cases hbv : (b0 != CryptoVerification.LibsignalSpqrV1.Version.v1.toU8) = true
                              · simp only [hbv, ↓reduceIte] at hs; nomatch hs
                              · simp only [hbv, Bool.false_eq_true, ↓reduceIte] at hs
                                injection hs with hsOut; subst hsOut
                                refine Or.inr ⟨pbToPqRatchetState
                                  { inner := some ((spqrDeps W.C.F W.Q.K).statesIntoPb st1)
                                    versionNegotiation := some vn
                                    chain := some chain2.intoPb }, rfl, fun c' hc' => ?_, hvnDir⟩
                                simp only [pbToPqRatchetState, Option.mem_def, Option.some.injEq] at hc'
                                subst hc'; simp [Chain.intoPb, hd2]; rfl
                      | some es =>
                        dsimp only at hs
                        rcases hae : c.addEpoch (spqrHkdfWith W.C.F) es with _ | chain1
                        · simp only [hae, CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainPanic] at hs
                          nomatch hs
                        · have hd1 : chain1.dir = .a2b := (chain_dir_addEpoch _ hae).trans hd0
                          simp only [hae, CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainPanic] at hs
                          by_cases hep0 : ((spqrDeps W.C.F W.Q.K).msgEpoch mV1 == 0#64) = true
                          · simp only [hep0, ↓reduceIte] at hs; nomatch hs
                          · simp only [hep0, Bool.false_eq_true, ↓reduceIte] at hs
                            rcases hsk : chain1.sendKey (spqrHkdfWith W.C.F)
                                ((spqrDeps W.C.F W.Q.K).msgEpoch mV1 - 1#64) with _ | ⟨chain2, idx, mk⟩
                            · simp only [hsk, CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainResult] at hs
                              nomatch hs
                            · have hd2 : chain2.dir = .a2b := (chain_dir_sendKey _ hsk).trans hd1
                              simp only [hsk, CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainResult] at hs
                              cases hms : (spqrDeps W.C.F W.Q.K).msgSerialize mV1 idx with
                              | nil => rw [hms] at hs; nomatch hs
                              | cons b0 tl =>
                                rw [hms] at hs; dsimp only at hs
                                by_cases hbv : (b0 != CryptoVerification.LibsignalSpqrV1.Version.v1.toU8) = true
                                · simp only [hbv, ↓reduceIte] at hs; nomatch hs
                                · simp only [hbv, Bool.false_eq_true, ↓reduceIte] at hs
                                  injection hs with hsOut; subst hsOut
                                  refine Or.inr ⟨pbToPqRatchetState
                                    { inner := some ((spqrDeps W.C.F W.Q.K).statesIntoPb st1)
                                      versionNegotiation := some vn
                                      chain := some chain2.intoPb }, rfl, fun c' hc' => ?_, hvnDir⟩
                                  simp only [pbToPqRatchetState, Option.mem_def, Option.some.injEq] at hc'
                                  subst hc'; simp [Chain.intoPb, hd2]; rfl
                  · simp only [hslt, Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind,
                      pure, Except.pure] at hs
                    by_cases hkNone : kOpt.isNone = true
                    · simp only [hkNone, ↓reduceIte] at hs
                      cases hms : (spqrDeps W.C.F W.Q.K).msgSerialize mV1 0#32 with
                      | nil => rw [hms] at hs; nomatch hs
                      | cons b0 tl =>
                        rw [hms] at hs; dsimp only at hs
                        by_cases hbv : (b0 != CryptoVerification.LibsignalSpqrV1.Version.v1.toU8) = true
                        · simp only [hbv, ↓reduceIte] at hs; nomatch hs
                        · simp only [hbv, Bool.false_eq_true, ↓reduceIte] at hs
                          injection hs with hsOut; subst hsOut
                          exact Or.inr ⟨pbToPqRatchetState
                            { inner := some ((spqrDeps W.C.F W.Q.K).statesIntoPb st1)
                              versionNegotiation := some vn
                              chain := none }, rfl, (fun _ hc' => by nomatch hc'), hvnDir⟩
                    · simp only [hkNone, Bool.false_eq_true, ↓reduceIte] at hs
                      nomatch hs

private theorem of_ite_error_eq_ok {P : Prop} [Decidable P] {ε α : Type} {e : ε}
    {b : Except ε α} {v : α}
    (h : (if P then Except.error e else b) = Except.ok v) : b = Except.ok v := by
  by_cases hp : P
  · simp [hp] at h
  · simp [hp] at h; exact h

private theorem rawDir0_spqrRecv (W : PEParams) {bs msg newBs : HwBytes}
    {key : CryptoGames.HKDF.Salt}
    (hraw : RawDir0 bs) (hlen : bs.length < 2 ^ 64)
    (hrecv : (pqxdhSpqrSession W).recv bs msg = .ok (newBs, key)) :
    RawDir0 newBs := by
  change (toSpqrModel (spqrDeps W.C.F W.Q.K) (spqrHkdfWith W.C.F)).recv bs msg = .ok (newBs, key) at hrecv
  unfold toSpqrModel at hrecv
  dsimp only at hrecv
  rcases hr : CryptoVerification.LibsignalSpqrV1.recv (spqrDeps W.C.F W.Q.K) (spqrHkdfWith W.C.F) bs msg with e | rOut
  · rw [hr] at hrecv; cases e <;> nomatch hrecv
  · rw [hr] at hrecv; dsimp only at hrecv
    cases hks : CryptoVerification.LibsignalSpqrV1.recvKeyToSalt? rOut.key with
    | none => rw [hks] at hrecv; nomatch hrecv
    | some sk =>
      rw [hks] at hrecv; injection hrecv with hp; injection hp with hnb _; subst hnb
      unfold CryptoVerification.LibsignalSpqrV1.recv at hr
      rcases hmp : CryptoVerification.LibsignalSpqrV1.msgPreamble msg with _ | pre
      · simp [hmp, CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofError, Bind.bind, Except.bind] at hr
      · simp only [hmp, CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofError, Bind.bind, Except.bind] at hr
        rcases hd : decodeState (spqrDeps W.C.F W.Q.K) bs with _ | prePb
        · simp [hd] at hr
        · obtain ⟨hch0, hvn0⟩ := decodeState_spqrDeps_dir0 W.C.F W.Q.K hraw hlen hd
          simp only [hd] at hr
          replace hr := of_ite_error_eq_ok hr
          replace hr := of_ite_error_eq_ok hr
          by_cases hv0 : ((CryptoVerification.LibsignalSpqrV1.stateVersion prePb).toU8 == 0#8) = true
          · simp only [hv0, ↓reduceIte] at hr
            injection hr with hr'; subst hr'; exact Or.inl rfl
          · simp only [hv0, Bool.false_eq_true, ↓reduceIte] at hr
            by_cases hgt : pre.version > (CryptoVerification.LibsignalSpqrV1.stateVersion prePb).toU8
            · simp only [hgt, ↓reduceIte] at hr
              rcases hcf : chainFrom (spqrHkdfWith W.C.F) prePb.chain prePb.versionNegotiation with _ | c0
              · simp only [hcf] at hr; nomatch hr
              · have hd0 : c0.dir = .a2b := chain_dir_chainFrom _ hch0 hvn0 hcf
                simp only [hcf] at hr
                rcases hrk : c0.recvKey (spqrHkdfWith W.C.F) 0#64 pre.index with _ | ⟨c1, rk⟩
                · simp only [hrk, CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainResult] at hr
                  nomatch hr
                · have hd1 : c1.dir = .a2b := (chain_dir_recvKey _ hrk).trans hd0
                  simp only [hrk, CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainResult] at hr
                  injection hr with hr'; subst hr'
                  refine Or.inr ⟨pbToPqRatchetState
                    { chain := some c1.intoPb, versionNegotiation := prePb.versionNegotiation, inner := prePb.inner },
                    rfl, fun c hc => ?_, hvn0⟩
                  simp only [pbToPqRatchetState, Option.mem_def, Option.some.injEq] at hc
                  subst hc; simp [Chain.intoPb, hd1]; rfl
            · simp only [hgt, ↓reduceIte] at hr
              by_cases heqv : (pre.version == (CryptoVerification.LibsignalSpqrV1.stateVersion prePb).toU8) = true
              · simp only [heqv, ↓reduceIte, pure, Except.pure] at hr
                cases hinner : prePb.inner with
                | none =>
                  rw [hinner] at hr
                  injection hr with hr'; subst hr'; exact Or.inl rfl
                | some pb =>
                  rw [hinner] at hr; dsimp only at hr
                  rcases hmd : (spqrDeps W.C.F W.Q.K).msgDeserialize pre.epoch pre.remaining with _ | sckaMsg
                  · simp only [hmd] at hr; nomatch hr
                  · simp only [hmd] at hr
                    rcases hfpb : (spqrDeps W.C.F W.Q.K).statesFromPb pb with _ | st0
                    · simp only [hfpb] at hr; nomatch hr
                    · simp only [hfpb] at hr
                      rcases hsr : (spqrDeps W.C.F W.Q.K).statesRecv st0 sckaMsg with _ | ⟨kOpt, st1⟩
                      · simp only [hsr] at hr; nomatch hr
                      · simp only [hsr] at hr
                        replace hr := of_ite_error_eq_ok hr
                        rcases hcf0 : chainFrom (spqrHkdfWith W.C.F) prePb.chain prePb.versionNegotiation with _ | c0
                        · simp only [hcf0] at hr; nomatch hr
                        · have hdc0 : c0.dir = .a2b := chain_dir_chainFrom _ hch0 hvn0 hcf0
                          simp only [hcf0] at hr
                          cases kOpt with
                          | none =>
                            dsimp only at hr
                            rcases hrk : c0.recvKey (spqrHkdfWith W.C.F) (pre.epoch - 1#64) pre.index with _ | ⟨c2, mk⟩
                            · simp only [hrk, CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainResult] at hr
                              nomatch hr
                            · have hdc2 : c2.dir = .a2b := (chain_dir_recvKey _ hrk).trans hdc0
                              simp only [hrk, CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainResult] at hr
                              injection hr with hr'; subst hr'
                              refine Or.inr ⟨pbToPqRatchetState
                                { inner := some ((spqrDeps W.C.F W.Q.K).statesIntoPb st1)
                                  versionNegotiation := none
                                  chain := some c2.intoPb }, rfl, (fun c hc => ?_), (fun _ hv => by nomatch hv)⟩
                              simp only [pbToPqRatchetState, Option.mem_def, Option.some.injEq] at hc
                              subst hc; simp [Chain.intoPb, hdc2]; rfl
                          | some es =>
                            dsimp only at hr
                            rcases hae : c0.addEpoch (spqrHkdfWith W.C.F) es with _ | c1
                            · simp only [hae, CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainPanic] at hr
                              nomatch hr
                            · have hdc1 : c1.dir = .a2b := (chain_dir_addEpoch _ hae).trans hdc0
                              simp only [hae, CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainPanic] at hr
                              rcases hrk : c1.recvKey (spqrHkdfWith W.C.F) (pre.epoch - 1#64) pre.index with _ | ⟨c2, mk⟩
                              · simp only [hrk, CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainResult] at hr
                                nomatch hr
                              · have hdc2 : c2.dir = .a2b := (chain_dir_recvKey _ hrk).trans hdc1
                                simp only [hrk, CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainResult] at hr
                                injection hr with hr'; subst hr'
                                refine Or.inr ⟨pbToPqRatchetState
                                  { inner := some ((spqrDeps W.C.F W.Q.K).statesIntoPb st1)
                                    versionNegotiation := none
                                    chain := some c2.intoPb }, rfl, (fun c hc => ?_), (fun _ hv => by nomatch hv)⟩
                                simp only [pbToPqRatchetState, Option.mem_def, Option.some.injEq] at hc
                                subst hc; simp [Chain.intoPb, hdc2]; rfl
              · simp only [heqv, Bool.false_eq_true, ↓reduceIte] at hr
                replace hr := of_ite_error_eq_ok hr
                cases hvnp : prePb.versionNegotiation with
                | none =>
                  simp only [hvnp] at hr; nomatch hr
                | some vn =>
                  have hvnDir : vn.direction = 0#32 := hvn0 vn (by simp [hvnp])
                  simp only [hvnp, pure, Except.pure] at hr
                  cases hvu : CryptoVerification.LibsignalSpqrV1.Version.fromU8? pre.version with
                  | none =>
                    simp only [hvu] at hr; nomatch hr
                  | some v =>
                    simp only [hvu, hvnDir] at hr
                    have hdI32 : Direction.fromI32? 0#32 = some .a2b := rfl
                    rw [hdI32] at hr
                    dsimp only at hr
                    rcases hii : CryptoVerification.LibsignalSpqrV1.initInner (spqrDeps W.C.F W.Q.K) v .a2b vn.authKey with
                      _ | inner'
                    · simp only [hii, CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofPanic] at hr
                      nomatch hr
                    · simp only [hii, CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofPanic] at hr
                      rcases hcf' : chainFrom (spqrHkdfWith W.C.F) prePb.chain (some vn) with _ | chain'
                      · simp only [hcf'] at hr; nomatch hr
                      · have hdc : chain'.dir = .a2b :=
                          chain_dir_chainFrom _ hch0 (fun x hx => by simp at hx; subst hx; exact hvnDir) hcf'
                        simp only [hcf'] at hr
                        cases inner' with
                        | none =>
                          dsimp only at hr
                          injection hr with hr'; subst hr'; exact Or.inl rfl
                        | some pb =>
                          dsimp only at hr
                          rcases hmd : (spqrDeps W.C.F W.Q.K).msgDeserialize pre.epoch pre.remaining with _ | sckaMsg
                          · simp only [hmd] at hr; nomatch hr
                          · simp only [hmd] at hr
                            rcases hfpb : (spqrDeps W.C.F W.Q.K).statesFromPb pb with _ | st0
                            · simp only [hfpb] at hr; nomatch hr
                            · simp only [hfpb] at hr
                              rcases hsr : (spqrDeps W.C.F W.Q.K).statesRecv st0 sckaMsg with _ | ⟨kOpt, st1⟩
                              · simp only [hsr] at hr; nomatch hr
                              · simp only [hsr] at hr
                                replace hr := of_ite_error_eq_ok hr
                                rcases hcf0 : chainFrom (spqrHkdfWith W.C.F) (some chain'.intoPb) none with _ | c0
                                · simp only [hcf0] at hr; nomatch hr
                                · have hdc0 : c0.dir = .a2b :=
                                    chain_dir_chainFrom _
                                      (fun c hc => by
                                        simp only [Option.mem_def, Option.some.injEq] at hc
                                        subst hc; simp [Chain.intoPb, hdc]; rfl)
                                      (fun _ hv => by nomatch hv) hcf0
                                  simp only [hcf0] at hr
                                  cases kOpt with
                                  | none =>
                                    dsimp only at hr
                                    rcases hrk : c0.recvKey (spqrHkdfWith W.C.F) (pre.epoch - 1#64) pre.index with _ | ⟨c2, mk⟩
                                    · simp only [hrk, CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainResult] at hr
                                      nomatch hr
                                    · have hdc2 : c2.dir = .a2b := (chain_dir_recvKey _ hrk).trans hdc0
                                      simp only [hrk, CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainResult] at hr
                                      injection hr with hr'; subst hr'
                                      refine Or.inr ⟨pbToPqRatchetState
                                        { inner := some ((spqrDeps W.C.F W.Q.K).statesIntoPb st1)
                                          versionNegotiation := none
                                          chain := some c2.intoPb }, rfl, (fun c hc => ?_), (fun _ hv => by nomatch hv)⟩
                                      simp only [pbToPqRatchetState, Option.mem_def, Option.some.injEq] at hc
                                      subst hc; simp [Chain.intoPb, hdc2]; rfl
                                  | some es =>
                                    dsimp only at hr
                                    rcases hae : c0.addEpoch (spqrHkdfWith W.C.F) es with _ | c1
                                    · simp only [hae, CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainPanic] at hr
                                      nomatch hr
                                    · have hdc1 : c1.dir = .a2b := (chain_dir_addEpoch _ hae).trans hdc0
                                      simp only [hae, CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainPanic] at hr
                                      rcases hrk : c1.recvKey (spqrHkdfWith W.C.F) (pre.epoch - 1#64) pre.index with _ | ⟨c2, mk⟩
                                      · simp only [hrk, CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainResult] at hr
                                        nomatch hr
                                      · have hdc2 : c2.dir = .a2b := (chain_dir_recvKey _ hrk).trans hdc1
                                        simp only [hrk, CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainResult] at hr
                                        injection hr with hr'; subst hr'
                                        refine Or.inr ⟨pbToPqRatchetState
                                          { inner := some ((spqrDeps W.C.F W.Q.K).statesIntoPb st1)
                                            versionNegotiation := none
                                            chain := some c2.intoPb }, rfl, (fun c hc => ?_), (fun _ hv => by nomatch hv)⟩
                                        simp only [pbToPqRatchetState, Option.mem_def, Option.some.injEq] at hc
                                        subst hc; simp [Chain.intoPb, hdc2]; rfl

private theorem reachable_rawDir0_or_responder {W : PEParams} {me : LocalIdentity}
    {x : RecordExtras} {g : GhostState HwBytes}
    (hr : ReachablePqxdhSession W me x g) :
    RawDir0 g.session.pqRatchetState ∨ ∃ m : PreKeyMessageFields, x = responderRecordExtras me m := by
  induction hr with
  | initiate X P me b t x g h =>
    left
    unfold initiateState at h
    rcases hinit : SignalPqxdh.Model.initiateKeys (modelPrims X W) (initiateInput W me b t) with
      _ | ⟨dk, hdr⟩
    · simp [hinit] at h
    · rw [hinit] at h; dsimp only at h
      rcases his : initializeInitiatorSession W.C (pqxdhSpqrSession W)
          ⟨(keyPairOf W.C me.idPriv).publicKey⟩ ⟨⟨b.idPub⟩⟩ ⟨b.spkPub⟩
          (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.rootKey))
          (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.chainKey))
          (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.pqrKey))
          (CryptoGames.HKDF.bytesToKey32 ((t.toList.drop 160).take 32)) with _ | s
      · rw [his] at h; nomatch h
      · rw [his] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨_, rfl⟩
        unfold initializeInitiatorSession at his
        dsimp only [Bind.bind, Except.bind, pure, Except.pure] at his
        split at his
        · nomatch his
        · injection his with hsEq
          subst hsEq
          dsimp only [CryptoGames.LibsignalSession.SessionState.setUnacknowledgedPreKeyMessage,
            CryptoGames.LibsignalSession.SessionState.setSenderChain,
            CryptoGames.LibsignalSession.SessionState.addReceiverChain,
            CryptoGames.LibsignalSession.SessionState.new]
          exact rawDir0_spqrV1Init_a2b W _
  | recvPrekey X P me k m rc x g pt h =>
    right
    unfold recvPrekeyState at h
    rcases htf : SignalMessage.tryFrom protoSignalCodec m.inner with _ | inner
    · simp [htf] at h
    · rw [htf] at h; dsimp only at h
      split_ifs at h
      · simp at h
      · rcases hacc : SignalPqxdh.Model.acceptKeys (modelPrims X W) (acceptInput W me k m) with _ | dk
        · simp [hacc] at h
        · rw [hacc] at h; dsimp only at h
          split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            exact ⟨m, h.1.symm⟩
          · simp at h
          · simp at h
  | @send me_s x_s g_s m r _ hlen ih =>
    rcases ih with hraw | ⟨m0, hx⟩
    · left
      have hlen64 : g_s.session.pqRatchetState.length < 2 ^ 64 := by
        have h32 : g_s.session.pqRatchetState.length < 2 ^ 32 :=
          recordScopeP_of_encodeRecordX_length x_s g_s (Nat.lt_trans hlen (by decide)) _ rfl
        exact Nat.lt_trans h32 (by decide)
      rw [CryptoVerification.E2E.Record.send_eq_afterSend]
      have hEncEq : SessionState.messageEncrypt (pqxdhSessionParams W).C (pqxdhSessionParams W).codec
          (pqxdhSessionParams W).spqr ((pqxdhSessionParams W).sendAddrs g_s.party) m r g_s.session =
        SessionState.messageEncrypt W.C protoSignalCodec (pqxdhSpqrSession W)
          ((pqxdhSessionParams W).sendAddrs g_s.party) m r g_s.session := rfl
      rw [hEncEq]
      rcases hm : SessionState.messageEncrypt W.C protoSignalCodec (pqxdhSpqrSession W)
          ((pqxdhSessionParams W).sendAddrs g_s.party) m r g_s.session with ⟨_ | msg, s'⟩
      · exact hraw
      · change RawDir0 s'.pqRatchetState
        unfold SessionState.messageEncrypt at hm
        rcases hfrom : Mut.exec OutgoingTripleRatchet.fromSessionState g_s.session with ⟨_ | o, taken⟩
        · simp [hfrom] at hm
        · have hoPq : o.pqrState = g_s.session.pqRatchetState := by
            unfold OutgoingTripleRatchet.fromSessionState SessionState.takePqRatchetState at hfrom
            rcases hsc : g_s.session.senderChain with _ | sc
            · simp [hsc] at hfrom
            · simp only [hsc, mut_exec_bind, mut_exec_get, mut_exec_modifyGet] at hfrom
              split_ifs at hfrom
              · simp at hfrom
              · rcases hrem : g_s.session.remoteIdentity with _ | rem
                · simp [hrem] at hfrom
                · simp only [hrem, mut_exec_pure, Prod.mk.injEq, Except.ok.injEq] at hfrom
                  exact hfrom.1.symm ▸ rfl
          rw [hfrom] at hm; dsimp only at hm
          rcases henc : Mut.exec (OutgoingTripleRatchet.encrypt W.C protoSignalCodec (pqxdhSpqrSession W)
              m (g_s.session.encryptAddresses ((pqxdhSessionParams W).sendAddrs g_s.party)) r) o with
            ⟨_ | msg', o'⟩
          · simp [henc] at hm
          · rw [henc] at hm; injection hm with _ hs'; subst hs'
            unfold OutgoingTripleRatchet.encrypt at henc
            simp only [mut_exec_bind, mut_exec_get] at henc
            split_ifs at henc
            · simp at henc
            · rcases hsp : (pqxdhSpqrSession W).send o.pqrState r with _ | ⟨newPq, pqKey, pqMsg⟩
              · simp [hsp] at henc
              · simp only [hsp, mut_exec_bind, mut_exec_liftE] at henc
                rcases hnext : o.senderChainKey.nextChainKey W.C.F with _ | nextCk
                · simp [hnext] at henc
                · simp only [hnext, Mut.exec, ExceptT.run, StateT.run,
                    pure, set, MonadStateOf.set] at henc
                  rcases henc with ⟨_, rfl⟩
                  rw [hoPq] at hsp
                  exact rawDir0_spqrSend W hraw hlen64 hsp
    · exact Or.inr ⟨m0, hx⟩
  | @recv me_r x_r g_r g_r' c rc res _ hlen hrec ih =>
    rcases ih with hraw | ⟨m0, hx⟩
    · left
      have hlen64 : g_r.session.pqRatchetState.length < 2 ^ 64 := by
        have h32 : g_r.session.pqRatchetState.length < 2 ^ 32 :=
          recordScopeP_of_encodeRecordX_length x_r g_r (Nat.lt_trans hlen (by decide)) _ rfl
        exact Nat.lt_trans h32 (by decide)
      rcases res with ⟨_, _, _⟩
      rw [CryptoVerification.E2E.Record.receive_eq_afterRecv] at hrec
      have hCodec : (pqxdhSessionParams W).codec = protoSignalCodec := rfl
      have hC : (pqxdhSessionParams W).C = W.C := rfl
      have hSpqr : (pqxdhSessionParams W).spqr = pqxdhSpqrSession W := rfl
      rw [hCodec, hC, hSpqr] at hrec
      rcases htf : SignalMessage.tryFrom protoSignalCodec c with _ | msg
      · rw [htf] at hrec; nomatch hrec
      · rw [htf] at hrec; dsimp only at hrec
        rcases hd : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
            ((pqxdhSessionParams W).expectedAddrs g_r.party) msg .whisper rc g_r.session with ⟨_ | pt', s'⟩
        · simp [hd] at hrec
        · rw [hd] at hrec; simp only [Option.some.injEq] at hrec
          rcases hrec with ⟨rfl, _, _, _⟩
          unfold SessionState.tryDecryptFromRecord at hd
          split_ifs at hd
          · nomatch hd
          · rcases hws : Mut.exec (SessionState.tryDecryptWithState W.C (pqxdhSpqrSession W)
                ((pqxdhSessionParams W).expectedAddrs g_r.party) msg .whisper rc) g_r.session with
              ⟨_ | ptext, updated⟩
            · simp [hws] at hd
            · rw [hws] at hd; injection hd with _ hs'; subst hs'
              unfold SessionState.tryDecryptWithState TripleRatchet.fromSessionState
                SessionState.takeRatchetState SessionState.takePqRatchetState at hws
              rcases hrem : g_r.session.remoteIdentity with _ | rem
              · simp [hrem] at hws
              · simp only [hrem, mut_exec_bind, mut_exec_modifyGet, mut_exec_get, mut_exec_pure] at hws
                rcases htr : Mut.exec (TripleRatchet.decrypt W.C (pqxdhSpqrSession W)
                    ((pqxdhSessionParams W).expectedAddrs g_r.party) msg .whisper rc)
                    ⟨⟨g_r.session.rootKey, g_r.session.senderChain, g_r.session.receiverChains,
                      g_r.session.previousCounter, CryptoGames.LibsignalSession.maxForwardJumps⟩,
                      g_r.session.pqRatchetState, g_r.session.localIdentity, rem⟩ with ⟨_ | _, tr'⟩
                · simp [htr] at hws
                · rw [htr] at hws
                  simp only [mut_exec_liftE, mut_exec_modify, Prod.mk.injEq, Except.ok.injEq] at hws
                  rcases hws with ⟨_, rfl⟩
                  unfold TripleRatchet.decrypt at htr
                  simp only [Symbolic.Swarm.CREF.Cli.mut_exec_onRatchet, mut_exec_bind, mut_exec_get] at htr
                  let r0 : CryptoGames.LibsignalSession.RatchetState :=
                    ⟨g_r.session.rootKey, g_r.session.senderChain, g_r.session.receiverChains,
                      g_r.session.previousCounter, CryptoGames.LibsignalSession.maxForwardJumps⟩
                  rcases hens : Mut.exec (CryptoGames.LibsignalSession.RatchetState.ensureReceiverChain
                      W.C msg.senderRatchetKey rc) r0 with ⟨_ | ck, rs1⟩
                  · simp [r0, hens] at htr
                  · simp only [r0, hens] at htr
                    rcases hcmk : Mut.exec (CryptoGames.LibsignalSession.RatchetState.consumeMessageKey
                        W.C.F msg.senderRatchetKey ck msg.counter .whisper) rs1 with ⟨_ | mkg, rs2⟩
                    · simp [hcmk] at htr
                    · simp only [hcmk] at htr
                      split_ifs at htr
                      · simp at htr
                      · rcases hsp : (pqxdhSpqrSession W).recv g_r.session.pqRatchetState msg.pqRatchet with
                          b | ⟨newPq, pqKey⟩
                        · cases b <;> simp [hsp] at htr
                        · simp only [hsp, mut_exec_pure, mut_exec_bind] at htr
                          split_ifs at htr
                          · simp at htr
                          · split at htr
                            · simp only [mut_exec_bind, mut_exec_modify, mut_exec_pure,
                                Prod.mk.injEq, Except.ok.injEq] at htr
                              rcases htr with ⟨_, rfl⟩
                              exact rawDir0_spqrRecv W hraw hlen64 hsp
                            · simp at htr
    · exact Or.inr ⟨m0, hx⟩

@[expose] def checkNotRawDir0 (bs : HwBytes) : Bool :=
  !bs.isEmpty &&
  match PqRatchetState.decode bs with
  | .ok st =>
    match st.chain with
    | some c => c.direction != 0#32
    | none => false
  | .error _ => false

private theorem not_rawDir0_of_checkNotRawDir0 {bs : HwBytes}
    (hchk : checkNotRawDir0 bs = true) (hlen : bs.length < 2 ^ 64) : ¬ RawDir0 bs := by
  unfold checkNotRawDir0 at hchk
  rcases (Bool.and_eq_true _ _).mp hchk with ⟨hne, hdecChk⟩
  rintro (rfl | ⟨m, rfl, hch0, _⟩)
  · simp at hne
  · rcases hdec : PqRatchetState.decode (PqRatchetState.encodeRaw m) with _ | st
    · rw [hdec] at hdecChk; cases hdecChk
    · rw [hdec] at hdecChk; dsimp only at hdecChk
      obtain ⟨hch', _⟩ := pqRatchetState_decode_encodeRaw_dir0 hlen hch0 hdec
      cases hsc : st.chain with
      | none => rw [hsc] at hdecChk; cases hdecChk
      | some c =>
        rw [hsc] at hdecChk
        exact bne_iff_ne.mp hdecChk (hch' c (by simp [hsc]))

/-! ## Directory-Snapshot Extraction for Arbitrary `pqInputs` Calls -/

private theorem filesOf_eq_none_of_forall_ne'' {files : List (String × HwBytes)} {p : String}
    (hreg : RegularFileList files)
    (hne : ∀ f ∈ files, Arm64.normalizePath f.1 ≠ Arm64.normalizePath p) :
    filesOf files p = none := by
  cases hf : filesOf files p with
  | none => rfl
  | some b =>
    obtain ⟨f, hmem, hp, _⟩ := mem_of_filesOf_eq_some hreg hf
    exact False.elim (hne f hmem hp)

private theorem toString_one_local : toString (1 : Nat) = "1" := by
  change Nat.repr 1 = "1"
  rw [Nat.repr_of_lt (by omega), Nat.digitChar_eq_one.mpr rfl]
  rfl

private theorem regularFileList_of_bundleFilesFlat' {files : List (String × HwBytes)}
    (hflat : BundleFilesFlat files) : RegularFileList files := by
  intro f hf
  obtain ⟨⟨name, hnorm⟩, _⟩ := hflat f hf
  refine ⟨by rw [hnorm]; simp, ?_, ?_, ?_⟩
  · have hstdio : stdioPaths.map Arm64.normalizePath = [["<stdin>"], ["<stdout>"], ["<stderr>"]] := by
      decide
    rw [hstdio, hnorm]; simp
  · intro d _ h; rw [hnorm] at h; nomatch (List.cons.inj h).2
  · intro pref hp
    rw [hnorm] at hp
    simp only [Arm64.FsPath.nonEmptyPrefixes, List.map, List.dropLast, List.mem_singleton] at hp
    exact ⟨"bundle", by decide, hp⟩

private theorem encodeDir_norm_ne_coins_and_bundle'' (P : PEParams) (st : PqParty)
    {f : String × HwBytes} (hf : f ∈ encodeDir P st) :
    Arm64.normalizePath f.1 ≠ ["coins"] ∧ (Arm64.normalizePath f.1).head? ≠ some "bundle" := by
  unfold encodeDir at hf
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_flatten, or_assoc] at hf
  rcases hf with rfl | rfl | rfl | h | h | h | h | h | h
  · dsimp only; decide
  · dsimp only; decide
  · dsimp only; decide
  · cases hp : st.peerId with
    | none => simp [hp] at h
    | some k => simp only [hp, List.mem_singleton] at h; subst h; dsimp only; cases st.party <;> decide
  · cases hs : st.session with
    | none => simp [hs] at h
    | some xg =>
      simp only [hs, List.mem_singleton] at h; subst h; dsimp only
      cases st.party <;>
        simp only [CryptoVerification.SignalSession.sessionFile, partyAddress,
          CryptoVerification.SignalSession.Address.text, partyAddressName, toString_one_local] <;>
        decide
  · rcases h with ⟨⟨i, _⟩, _, rfl⟩
    have hn : Arm64.normalizePath (signedPreKeyFile i) = ["signed-pre-keys", toString i.toNat] := by
      simpa [signedPreKeyFile] using normalizePath_dir_nat_suf (d := "signed-pre-keys") (suf := "") i.toNat
        (by decide) (by decide) (by decide) (by decide)
    dsimp only; rw [hn]
    exact ⟨fun he => absurd (List.cons.inj he).1 (by decide),
      fun he => absurd (Option.some.inj he) (by decide)⟩
  · rcases h with ⟨⟨i, _⟩, _, rfl⟩
    have hn : Arm64.normalizePath (oneTimePreKeyFile i) = ["one-time-pre-keys", toString i.toNat] := by
      simpa [oneTimePreKeyFile] using normalizePath_dir_nat_suf (d := "one-time-pre-keys") (suf := "") i.toNat
        (by decide) (by decide) (by decide) (by decide)
    dsimp only; rw [hn]
    exact ⟨fun he => absurd (List.cons.inj he).1 (by decide),
      fun he => absurd (Option.some.inj he) (by decide)⟩
  · rcases h with ⟨⟨i, _⟩, _, rfl⟩
    have hn : Arm64.normalizePath (oneTimeKyberPreKeyFile i) =
        ["one-time-kyber-pre-keys", toString i.toNat] := by
      simpa [oneTimeKyberPreKeyFile] using
        normalizePath_dir_nat_suf (d := "one-time-kyber-pre-keys") (suf := "") i.toNat
          (by decide) (by decide) (by decide) (by decide)
    dsimp only; rw [hn]
    exact ⟨fun he => absurd (List.cons.inj he).1 (by decide),
      fun he => absurd (Option.some.inj he) (by decide)⟩
  · rcases h with ⟨l, ⟨⟨i, _, _⟩, _, rfl⟩, hl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · have hn : Arm64.normalizePath (lastResortKyberPreKeyFile i) =
          ["last-resort-kyber-pre-keys", toString i.toNat] := by
        simpa [lastResortKyberPreKeyFile] using
          normalizePath_dir_nat_suf (d := "last-resort-kyber-pre-keys") (suf := "") i.toNat
            (by decide) (by decide) (by decide) (by decide)
      dsimp only; rw [hn]
      exact ⟨fun he => absurd (List.cons.inj he).1 (by decide),
        fun he => absurd (Option.some.inj he) (by decide)⟩
    · have hn : Arm64.normalizePath (baseKeysFile i) =
          ["last-resort-kyber-pre-keys", toString i.toNat ++ ".base-keys"] := by
        simpa [baseKeysFile] using
          normalizePath_dir_nat_suf (d := "last-resort-kyber-pre-keys") (suf := ".base-keys") i.toNat
            (by decide) (by decide) (by decide) (by decide)
      dsimp only; rw [hn]
      exact ⟨fun he => absurd (List.cons.inj he).1 (by decide),
        fun he => absurd (Option.some.inj he) (by decide)⟩

private theorem strip_init_filesOf {P : PEParams} {st₀ st : PqParty}
    {b₀ : PreKeyBundleFields} {t₀ : List.Vector (BitVec 8) initiateTapeLen}
    {peer : CryptoVerification.SignalSession.Address}
    {extra : List (String × HwBytes)} {coins stdin : HwBytes}
    (hflat : BundleFilesFlat extra)
    (h : InputsEquiv (pqInitInputs P st₀ b₀ t₀) (pqInputs P st (.init peer bundleDir) extra coins stdin)) :
    ∀ p, filesOf (encodeDir P st₀) p = filesOf (encodeDir P st) p := by
  intro p
  have hregB₀ := regularFileList_bundle_files (publicBundleOf b₀)
  have hreg₀ := (regularFileList_encodeDir P st₀).append hregB₀
  have hreg₁ := (regularFileList_encodeDir P st).append (regularFileList_of_bundleFilesFlat' hflat)
  by_cases hpc : Arm64.normalizePath p = ["coins"]
  · rw [filesOf_eq_none_of_forall_ne'' (regularFileList_encodeDir P st₀)
          (fun _ hf => by rw [hpc]; exact (encodeDir_norm_ne_coins_and_bundle'' P st₀ hf).1),
        filesOf_eq_none_of_forall_ne'' (regularFileList_encodeDir P st)
          (fun _ hf => by rw [hpc]; exact (encodeDir_norm_ne_coins_and_bundle'' P st hf).1)]
  · by_cases hpb : (Arm64.normalizePath p).head? = some "bundle"
    · rw [filesOf_eq_none_of_forall_ne'' (regularFileList_encodeDir P st₀)
            (fun _ hf he => (encodeDir_norm_ne_coins_and_bundle'' P st₀ hf).2 (he ▸ hpb)),
          filesOf_eq_none_of_forall_ne'' (regularFileList_encodeDir P st)
            (fun _ hf he => (encodeDir_norm_ne_coins_and_bundle'' P st hf).2 (he ▸ hpb))]
    · have hp := h.2.2.2 p
      change filesOf (encodeDir P st₀ ++ (publicBundleOf b₀).files bundleDir ++ [(coinsFile, t₀.toList)]) p =
             filesOf (encodeDir P st ++ extra ++ [(coinsFile, coins)]) p at hp
      have hcNone : ∀ c : HwBytes, filesOf [(coinsFile, c)] p = none := fun c =>
        filesOf_eq_none_of_forall_ne'' (regularFileList_coins c) fun f hf he => by
          rw [List.mem_singleton] at hf; subst hf
          exact hpc (he.symm.trans (by decide : Arm64.normalizePath coinsFile = ["coins"]))
      have hb₀None : filesOf ((publicBundleOf b₀).files bundleDir) p = none :=
        filesOf_eq_none_of_forall_ne'' hregB₀ fun f hf he => by
          unfold CryptoVerification.SignalSession.PublicBundle.files at hf
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hf
          rcases hf with (rfl | rfl | rfl | rfl) | ho
          · exact hpb (he ▸ by dsimp only; decide)
          · exact hpb (he ▸ by dsimp only; decide)
          · exact hpb (he ▸ by dsimp only; decide)
          · exact hpb (he ▸ by dsimp only; decide)
          · cases hot : (publicBundleOf b₀).oneTime with
            | none => simp [hot] at ho
            | some ik =>
              rcases ik with ⟨_, _⟩; simp only [hot, List.mem_singleton] at ho; subst ho
              exact hpb (he ▸ by dsimp only; decide)
      have hb₁None : filesOf extra p = none :=
        filesOf_eq_none_of_forall_ne'' (regularFileList_of_bundleFilesFlat' hflat) fun f hf he => by
          obtain ⟨⟨name, hnorm⟩, _⟩ := hflat f hf
          exact hpb (he ▸ by rw [hnorm]; rfl)
      rw [filesOf_append_of_regular hreg₀ (regularFileList_coins t₀.toList),
          filesOf_append_of_regular hreg₁ (regularFileList_coins coins),
          hcNone t₀.toList, hcNone coins, Option.none_or, Option.none_or,
          filesOf_append_of_regular (regularFileList_encodeDir P st₀) hregB₀,
          filesOf_append_of_regular (regularFileList_encodeDir P st) (regularFileList_of_bundleFilesFlat' hflat),
          hb₀None, hb₁None, Option.none_or, Option.none_or] at hp
      exact hp

private theorem specDomain_real_of_none {st st₀ : PqParty}
    (hwf : PqxdhPartyInSpecDomain compP0 st)
    (hst : PqPartyEquiv st st₀) (hsess₀ : st₀.session = none)
    (hKeys : checkPartyKeysInTable st₀ = true) :
    encodeDir compP0 st = encodeDir realP0 st ∧ PqxdhPartyInSpecDomain realP0 st := by
  have henc := encodeDir_eq_real_of_pqPartyEquiv hst hKeys
  have hsNone : st.session = none := by
    have hrel := hst.session_rel; rw [hsess₀] at hrel
    cases hs : st.session with | none => rfl | some _ => rw [hs] at hrel; cases hrel
  refine ⟨henc, ⟨(fun _ _ hs => by nomatch (hsNone.symm.trans hs)), fun f hf => ?_, hwf.2.2⟩⟩
  rw [← henc] at hf
  exact hwf.2.1 f hf

/-! ## Top-Level `RealHooksAgreeOnInput compHooks0` Theorems -/

theorem dirsAgreeOnInput_of_pqInitInputs {i : Inputs} {st₀ : PqParty}
    {b₀ : PreKeyBundleFields} {t₀ : List.Vector (BitVec 8) initiateTapeLen}
    (hwf₀ : checkPartyWF compP0 st₀ = true) (hsess₀ : st₀.session = none)
    (hKeys : checkPartyKeysInTable st₀ = true)
    (heq₀ : InputsEquiv i (pqInitInputs compP0 st₀ b₀ t₀)) :
    DirsAgreeOnInput compP0 realP0 i := by
  intro st cmd extra coins stdin hwf hcmd heq
  have h := inputsEquiv_trans (inputsEquiv_symm heq₀) heq
  cases cmd with
  | send _ => have h0 : (some "init" : Option String) = some "send" := congrArg List.head? h.1; nomatch h0
  | recv _ => have h0 : (some "init" : Option String) = some "recv" := congrArg List.head? h.1; nomatch h0
  | init peer d =>
    rcases hcmd with ⟨rfl, hflat⟩
    have hdir := strip_init_filesOf hflat h
    have hst := pqPartyEquiv_of_checkPartyWF hwf hwf₀ (fun p => (hdir p).symm)
    exact specDomain_real_of_none hwf hst hsess₀ hKeys

theorem realHooksAgreeOnInput_of_pqInitInputs {i : Inputs} {st₀ : PqParty}
    {b₀ : PreKeyBundleFields} {t₀ : List.Vector (BitVec 8) initiateTapeLen}
    (hwf₀ : checkPartyWF compP0 st₀ = true) (hsess₀ : st₀.session = none)
    (hKeys : checkPartyKeysInTable st₀ = true)
    (heq₀ : InputsEquiv i (pqInitInputs compP0 st₀ b₀ t₀))
    (hEvalBool : checkInitEqReal st₀ b₀ t₀ = true) :
    RealHooksAgreeOnInput compHooks0 i :=
  ⟨dirsAgreeOnInput_of_pqInitInputs hwf₀ hsess₀ hKeys heq₀,
   modelAgreesOnInput_of_pqInitInputsAt hwf₀ heq₀ (initiateState_eq_of_checkInitEqAt realP0_eq_hybrid hEvalBool)⟩

theorem dirsAgreeOnInput_of_pqSendInputs_pending {i : Inputs} {st₀ : PqParty}
    {x₀ : RecordExtras} {g₀ : GhostState HwBytes}
    {m₀ : HwBytes} {r₀ : List.Vector (BitVec 8) 64}
    (hwf₀ : checkPartyWF compP0 st₀ = true)
    (hsess₀ : st₀.session = some (x₀, g₀))
    (hppk₀ : g₀.session.pendingPreKey = true)
    (hKeys : checkPartyKeysInTable st₀ = true)
    (hReach₀ : ∃ gR, ReachablePqxdhSession realP0 st₀.me x₀ gR ∧
      gR.party = g₀.party ∧ gR.session = g₀.session)
    (heq₀ : InputsEquiv i (pqSendInputs compP0 st₀ m₀ r₀)) :
    DirsAgreeOnInput compP0 realP0 i := by
  intro st cmd extra coins stdin hwf hcmd heq
  have h := inputsEquiv_trans (inputsEquiv_symm heq₀) heq
  cases cmd with
  | init _ _ => have h0 : (some "send" : Option String) = some "init" := congrArg List.head? h.1; nomatch h0
  | recv _ => have h0 : (some "send" : Option String) = some "recv" := congrArg List.head? h.1; nomatch h0
  | send peer =>
    subst hcmd
    have hdir := (InputsInjAux.strip_coins_filesOf compP0 st₀ st r₀.toList coins h.2.2.2).2
    have hst := pqPartyEquiv_of_checkPartyWF hwf hwf₀ (fun p => (hdir p).symm)
    have henc := encodeDir_eq_real_of_pqPartyEquiv hst hKeys
    refine ⟨henc, ⟨?_, fun f hf => by rw [← henc] at hf; exact hwf.2.1 f hf, hwf.2.2⟩⟩
    intro x g hs
    have hrel := hst.session_rel; rw [hs, hsess₀] at hrel
    cases hrel with
    | some hse =>
      dsimp only at hse
      have hxEq : x = x₀ := hse.pending_eq ((congrArg SessionState.pendingPreKey hse.session_eq).trans hppk₀)
      obtain ⟨gR, hR, hpR, hsR⟩ := hReach₀
      exact ⟨⟨gR, (by rw [hst.me_eq, hxEq]; exact hR), hpR.trans hse.party_eq.symm, hsR.trans hse.session_eq.symm⟩,
        (hwf.1 x g hs).2⟩

theorem realHooksAgreeOnInput_of_pqSendInputs_pending {i : Inputs} {st₀ : PqParty}
    {x₀ : RecordExtras} {g₀ : GhostState HwBytes}
    {m₀ : HwBytes} {r₀ : List.Vector (BitVec 8) 64}
    (hwf₀ : checkPartyWF compP0 st₀ = true)
    (hsess₀ : st₀.session = some (x₀, g₀))
    (hppk₀ : g₀.session.pendingPreKey = true)
    (hKeys : checkPartyKeysInTable st₀ = true)
    (hReach₀ : ∃ gR, ReachablePqxdhSession realP0 st₀.me x₀ gR ∧
      gR.party = g₀.party ∧ gR.session = g₀.session)
    (heq₀ : InputsEquiv i (pqSendInputs compP0 st₀ m₀ r₀))
    (hEvalBool : checkSendEqReal st₀ m₀ r₀ = true) :
    RealHooksAgreeOnInput compHooks0 i :=
  ⟨dirsAgreeOnInput_of_pqSendInputs_pending hwf₀ hsess₀ hppk₀ hKeys hReach₀ heq₀,
   modelAgreesOnInput_of_pqSendInputsAt hwf₀ (by simp [hsess₀]) heq₀
     (sendMap_eq_of_checkSendEqAt realP0_eq_hybrid hEvalBool)⟩

theorem dirsAgreeOnInput_of_pqRecvPrekey_none {i : Inputs} {st₀ : PqParty}
    {body₀ : HwBytes} {rc₀ : BitVec 256}
    (hwf₀ : checkPartyWF compP0 st₀ = true) (hsess₀ : st₀.session = none)
    (hKeys : checkPartyKeysInTable st₀ = true)
    (heq₀ : InputsEquiv i (pqRecvInputs compP0 st₀ (wirePrekey :: body₀) rc₀)) :
    DirsAgreeOnInput compP0 realP0 i := by
  intro st cmd extra coins stdin hwf hcmd heq
  have h := inputsEquiv_trans (inputsEquiv_symm heq₀) heq
  cases cmd with
  | init _ _ => have h0 : (some "recv" : Option String) = some "init" := congrArg List.head? h.1; nomatch h0
  | send _ => have h0 : (some "recv" : Option String) = some "send" := congrArg List.head? h.1; nomatch h0
  | recv peer =>
    subst hcmd
    have hdir := (InputsInjAux.strip_coins_filesOf compP0 st₀ st (keyToBytes32 rc₀) coins h.2.2.2).2
    have hst := pqPartyEquiv_of_checkPartyWF hwf hwf₀ (fun p => (hdir p).symm)
    exact specDomain_real_of_none hwf hst hsess₀ hKeys

theorem realHooksAgreeOnInput_of_pqRecvPrekey_none {i : Inputs} {st₀ : PqParty}
    {body₀ : HwBytes} {m₀ : PreKeyMessageFields} {rc₀ : BitVec 256}
    (hwf₀ : checkPartyWF compP0 st₀ = true) (hsess₀ : st₀.session = none)
    (hKeys : checkPartyKeysInTable st₀ = true)
    (heq₀ : InputsEquiv i (pqRecvInputs compP0 st₀ (wirePrekey :: body₀) rc₀))
    (hm₀ : preKeyOfBody? body₀ = some m₀)
    (hEvalBool : checkRecvPrekeyEqReal st₀ m₀ rc₀ = true) :
    RealHooksAgreeOnInput compHooks0 i :=
  ⟨dirsAgreeOnInput_of_pqRecvPrekey_none hwf₀ hsess₀ hKeys heq₀,
   modelAgreesOnInput_of_pqRecvPrekey_noneAt hwf₀ hsess₀ heq₀ hm₀
     (recvMap_eq_of_checkRecvPrekeyEqAt realP0_eq_hybrid st₀.party st₀.me rfl rfl hEvalBool)⟩

theorem dirsAgreeOnInput_of_pqRecvPrekey_responder {i : Inputs} {st₀ : PqParty}
    {x₀ : RecordExtras} {g₀ : GhostState HwBytes} {mInit : PreKeyMessageFields}
    {body₀ : HwBytes} {rc₀ : BitVec 256}
    (hwf₀ : checkPartyWF compP0 st₀ = true)
    (hsess₀ : st₀.session = some (x₀, g₀))
    (hx₀ : recordExtrasEqBool x₀ (responderRecordExtras st₀.me mInit) = true)
    (hNotDir0 : checkNotRawDir0 g₀.session.pqRatchetState = true)
    (hKeys : checkPartyKeysInTable st₀ = true)
    (hReach₀ : ∃ gR, ReachablePqxdhSession realP0 st₀.me x₀ gR ∧
      gR.party = g₀.party ∧ gR.session = g₀.session)
    (heq₀ : InputsEquiv i (pqRecvInputs compP0 st₀ (wirePrekey :: body₀) rc₀)) :
    DirsAgreeOnInput compP0 realP0 i := by
  intro st cmd extra coins stdin hwf hcmd heq
  have h := inputsEquiv_trans (inputsEquiv_symm heq₀) heq
  cases cmd with
  | init _ _ => have h0 : (some "recv" : Option String) = some "init" := congrArg List.head? h.1; nomatch h0
  | send _ => have h0 : (some "recv" : Option String) = some "send" := congrArg List.head? h.1; nomatch h0
  | recv peer =>
    subst hcmd
    have hdir := (InputsInjAux.strip_coins_filesOf compP0 st₀ st (keyToBytes32 rc₀) coins h.2.2.2).2
    have hst := pqPartyEquiv_of_checkPartyWF hwf hwf₀ (fun p => (hdir p).symm)
    have henc := encodeDir_eq_real_of_pqPartyEquiv hst hKeys
    refine ⟨henc, ⟨?_, fun f hf => by rw [← henc] at hf; exact hwf.2.1 f hf, hwf.2.2⟩⟩
    intro x g hs
    have hrel := hst.session_rel; rw [hs, hsess₀] at hrel
    cases hrel with
    | some hse =>
      dsimp only at hse
      obtain ⟨⟨g₁, hReach₁, _, hg₁s⟩, hgp, hlen31⟩ := hwf.1 x g hs
      have hlen64 : g₀.session.pqRatchetState.length < 2 ^ 64 := by
        have h32 : g.session.pqRatchetState.length < 2 ^ 32 :=
          recordScopeP_of_encodeRecordX_length x g (Nat.lt_trans hlen31 (by decide)) _ rfl
        rw [hse.session_eq] at h32
        exact Nat.lt_trans h32 (by decide)
      have hxResp : ∃ m, x = responderRecordExtras st.me m := by
        rcases reachable_rawDir0_or_responder hReach₁ with hraw | hm
        · rw [hg₁s, hse.session_eq] at hraw
          exact False.elim (not_rawDir0_of_checkNotRawDir0 hNotDir0 hlen64 hraw)
        · exact hm
      obtain ⟨m, rfl⟩ := hxResp
      have hx₀Eq : x₀ = responderRecordExtras st₀.me mInit := eq_of_recordExtrasEqBool hx₀
      have hreg : m.regId = mInit.regId := by
        have hr := hse.remoteReg_eq
        rw [hx₀Eq] at hr
        exact hr
      have hbk : m.baseKey = mInit.baseKey := by
        have hb := hse.aliceBase_eq
        rw [hx₀Eq] at hb
        dsimp only [responderRecordExtras, djbKey] at hb
        exact List.Vector.eq _ _ (List.cons.inj hb).2
      have hxEq : responderRecordExtras st.me m = x₀ := by
        rw [hx₀Eq]
        unfold responderRecordExtras
        rw [hst.me_eq, hreg, hbk]
      obtain ⟨gR, hR, hpR, hsR⟩ := hReach₀
      exact ⟨⟨gR, (by rw [hxEq, hst.me_eq]; exact hR), hpR.trans hse.party_eq.symm, hsR.trans hse.session_eq.symm⟩,
        hgp, hlen31⟩

theorem realHooksAgreeOnInput_of_pqRecvPrekey_noMatch_resp {i : Inputs} {st₀ : PqParty}
    {x₀ : RecordExtras} {g₀ : GhostState HwBytes} {mInit : PreKeyMessageFields}
    {body₀ : HwBytes} {m₀ : PreKeyMessageFields} {q₀ : PreKeyFields} {rc₀ : BitVec 256}
    (hwf₀ : checkPartyWF compP0 st₀ = true)
    (hsess₀ : st₀.session = some (x₀, g₀))
    (hx₀ : recordExtrasEqBool x₀ (responderRecordExtras st₀.me mInit) = true)
    (hNotDir0 : checkNotRawDir0 g₀.session.pqRatchetState = true)
    (hKeys : checkPartyKeysInTable st₀ = true)
    (hReach₀ : ∃ gR, ReachablePqxdhSession realP0 st₀.me x₀ gR ∧
      gR.party = g₀.party ∧ gR.session = g₀.session)
    (heq₀ : InputsEquiv i (pqRecvInputs compP0 st₀ (wirePrekey :: body₀) rc₀))
    (hm₀ : preKeyOfBody? body₀ = some m₀)
    (hq₀ : parsePreKey body₀ = some q₀)
    (hNoMatch : ∀ x g, PqSessionEquiv x g x₀ g₀ → ¬ PqSessionMatches x g m₀)
    (hNoFields : ∀ x g, PqSessionEquiv x g x₀ g₀ → ¬ PqFieldsMatch x g q₀)
    (hEvalNewBool : checkRecvPrekeyEqReal { st₀ with session := none } m₀ rc₀ = true) :
    RealHooksAgreeOnInput compHooks0 i :=
  ⟨dirsAgreeOnInput_of_pqRecvPrekey_responder hwf₀ hsess₀ hx₀ hNotDir0 hKeys hReach₀ heq₀,
   modelAgreesOnInput_of_pqRecvPrekey_noMatchAt hwf₀ hsess₀ heq₀ hm₀ hq₀ hNoMatch hNoFields
     (recvMap_eq_of_checkRecvPrekeyEqAt realP0_eq_hybrid st₀.party st₀.me rfl rfl hEvalNewBool)⟩

end

end Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealGuard
