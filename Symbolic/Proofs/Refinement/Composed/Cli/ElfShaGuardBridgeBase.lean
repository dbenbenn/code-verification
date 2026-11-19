/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Refinement.Composed.Cli.Model -- proof-setup: allow-public-import
public import Symbolic.Proofs.Refinement.Composed.Cli.SDet.Defs -- proof-setup: allow-public-import
public import Symbolic.Proofs.Refinement.Composed.Cli.SDet.FilesOfAlg -- proof-setup: allow-public-import
public import Symbolic.Proofs.Refinement.Composed.Cli.SDet.ModelCongr -- proof-setup: allow-public-import
import Symbolic.Proofs.Refinement.Composed.Cli.SDet.CodecInj
import Symbolic.Proofs.Refinement.Composed.Cli.SDet.EncodeDirInj
import Symbolic.Proofs.SpecLemmas.ElfBindingSha256

/-!
# Base Definitions and Congruence Helpers for SHA-256 Domain-Guard Transfer

Defines `withShaF`, `ShaAgreesOnInput`, `withShaFInterp`, cross-`PEParams` `PqPartyEquiv`
extraction (`pqPartyEquiv_of_specDomain_pair`, `pqPartyEquiv_of_weakWF`), and model-outcome
congruence helpers used by `ElfShaGuardBridge` and `CompHooks0Guard`.
-/

public section

set_option autoImplicit false

namespace Symbolic.Proofs.Refinement.Composed.Cli.ElfShaGuardBridgeBase

open CryptoProofLib.Refinement (ByteString ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Refinement (
  aesCbcDecryptSymbol aesCbcEncryptSymbol sha256CompressFunction sha256CompressSymbol
  shaStateBytes shaStateOfBytes x25519AgreementSymbol x25519PublicKeySymbol
)
open DY.Libsignal.PQXDH.Refinement (
  kyberDecapsSymbol kyberEncapsSymbol
)
open DY.Libsignal.Composed.Refinement (
  HonestBundle PreKeyFields ProtocolSetup parsePreKey pubBytes vec32
)
open DY.Libsignal.Composed.Refinement.Cli (
  BundleFilesFlat CliCall CliTurn ExternContractsHoldCli HonestBundleFiles InputsEquiv ModelAgree
  NoMatchSessionFile PqFieldsMatch ValidCall bobPreKeyFiles commonFiles initDirs
  noMatchRecordBytes parseBundleFiles pqInitInputsF pqRecvMatchingFieldsModel preKeyOfBody?
  shaStateOfBytes_shaStateBytes
)
open DY.Libsignal.Composed.Refinement.Cli.SDet (
  PqModelResultEquiv PqPartyEquiv PqSessionEquiv RegularFileList encodeRecordX_eq_of_pqSessionEquiv
  filesOf_append_of_regular filesOf_encodeDir_eq_of_pqPartyEquiv filesOf_eq_optFold
  normalizePath_dir_nat_suf normalizePath_two pqPartyEquiv_of_filesOf_encodeDir
  pqRecvPrekeyModel_congr regularFileList_encodeDir toString_nat_seg
)
open CryptoGames.HMAC (ShaState)
open CryptoGames.LibsignalSession (
  GhostState IdentityKey MessageType SessionState TripleRatchet
)
open CryptoVerification.E2E (
  PEParams PreKeyBundleFields PreKeyMessageFields RecordExtras UnreachedPqxdhPrimitives
  djbKey encStateUnderExtras encodeRecordUnderExtras initiateTapeLen keyPairOf
  partyAddressName pqxdhSessionParams pqxdhSpqrSession wirePrekey wireWhisper
)
open CryptoVerification.SignalSession (
  Inputs Outcome OutcomeMatchesModelExceptPath PqParty PqSessionMatches PqxdhPartyInSpecDomain
  addressFile baseKeysBytes baseKeysFile bundleDir encodeDir filesOf identityFile
  identityKeyPairFile kyberRecordBytes lastResortKyberPreKeyFile le32 oneTimeKyberPreKeyFile
  oneTimePreKeyFile oneTimeRecordBytes partyAddress pqInitModel pqRecvInputs pqRecvPrekeyModel
  pqRecvWhisperModel pqSendInputs pqSendModel pqxdhExpectedOutcome publicBundleOf
  registrationIdFile sessionFile signedPreKeyFile signedRecordBytes textBytes
)

/-! ## Parameterized SHA-256 replacement on `PEParams` and `ExternInterpretation` -/

/-- Replaces `P.C.F` with `F₀`, leaving all other cryptographic primitives unchanged. -/
@[expose] def withShaF (F₀ : ShaState → HwBytes → ShaState) (P : PEParams) : PEParams :=
  { P with C := { P.C with F := F₀ } }

/-- Per-call SHA-256 agreement guard between `P` and `withShaF F₀ P`. -/
@[expose] def ShaAgreesOnInput (F₀ : ShaState → HwBytes → ShaState)
    (P : PEParams) (i : Inputs) : Prop :=
  let P₀ : PEParams := withShaF F₀ P
  (∀ (X : UnreachedPqxdhPrimitives) (st : PqParty) (files : List (String × HwBytes))
      (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen),
    PqxdhPartyInSpecDomain P st → st.session = none →
    (files = (publicBundleOf b).files bundleDir ∨
      (BundleFilesFlat files ∧ parseBundleFiles (filesOf files) = some (publicBundleOf b))) →
    InputsEquiv i (pqInitInputsF P st files t) →
    pqInitModel X P st b t = pqInitModel X P₀ st b t) ∧
  (∀ (st : PqParty) (m : HwBytes) (coins : List.Vector (BitVec 8) 64),
    PqxdhPartyInSpecDomain P st → m.length < 2 ^ 32 →
    InputsEquiv i (pqSendInputs P st m coins) →
    pqSendModel P st m coins.toList = pqSendModel P₀ st m coins.toList) ∧
  (∀ (st : PqParty) (body : HwBytes) (rc : BitVec 256),
    PqxdhPartyInSpecDomain P st → body.length < 2 ^ 32 →
    InputsEquiv i (pqRecvInputs P st (wireWhisper :: body) rc) →
    pqRecvWhisperModel P st body rc = pqRecvWhisperModel P₀ st body rc) ∧
  (∀ (X : UnreachedPqxdhPrimitives) (st : PqParty) (body : HwBytes) (m : PreKeyMessageFields)
      (rc : BitVec 256),
    PqxdhPartyInSpecDomain P st → m.inner.length + 2048 < 2 ^ 32 →
    (body = m.bytes ∨ (body.length < 2 ^ 32 ∧ preKeyOfBody? body = some m)) →
    InputsEquiv i (pqRecvInputs P st (wirePrekey :: body) rc) →
    ((∀ x g, st.session = some (x, g) → PqSessionMatches x g m) →
      pqRecvPrekeyModel X P st m rc = pqRecvPrekeyModel X P₀ st m rc) ∧
    (∀ x g, st.session = some (x, g) → ¬ PqSessionMatches x g m →
      pqRecvPrekeyModel X P { st with session := none } m rc =
        pqRecvPrekeyModel X P₀ { st with session := none } m rc)) ∧
  (∀ (st : PqParty) (x : RecordExtras) (g : GhostState HwBytes) (body : HwBytes)
      (q : PreKeyFields) (rc : BitVec 256),
    PqxdhPartyInSpecDomain P st → st.session = some (x, g) → body.length < 2 ^ 32 →
    parsePreKey body = some q → PqFieldsMatch x g q →
    InputsEquiv i (pqRecvInputs P st (wirePrekey :: body) rc) →
    pqRecvMatchingFieldsModel P st x g q rc =
      pqRecvMatchingFieldsModel P₀ st x g q rc)

/-- Overrides `sha256CompressSymbol` on 2-argument calls in `interp` with `F₀`. -/
def withShaFInterp (F₀ : ShaState → HwBytes → ShaState)
    (interp : ExternInterpretation) : ExternInterpretation :=
  fun sym args =>
    if sym = sha256CompressSymbol then
      match args with
      | [st_b, blk] => some (shaStateBytes (F₀ (shaStateOfBytes st_b) blk))
      | _ => interp sym args
    else interp sym args

private theorem withShaFInterp_ne (F₀ : ShaState → HwBytes → ShaState)
    (interp : ExternInterpretation) {sym : String} (hne : sym ≠ sha256CompressSymbol)
    (args : List ByteString) :
    withShaFInterp F₀ interp sym args = interp sym args := by
  simp [withShaFInterp, hne]

theorem sha256CompressFunction_withShaFInterp
    (F₀ : ShaState → HwBytes → ShaState) (interp : ExternInterpretation) :
    sha256CompressFunction (withShaFInterp F₀ interp) = F₀ := by
  funext st blk
  simp [sha256CompressFunction, withShaFInterp, shaStateOfBytes_shaStateBytes]

theorem modelAgree_withShaF (F₀ : ShaState → HwBytes → ShaState)
    {interp : ExternInterpretation} {P : PEParams} (h : ModelAgree interp P) :
    ModelAgree (withShaFInterp F₀ interp) (withShaF F₀ P) := by
  refine ⟨(sha256CompressFunction_withShaFInterp F₀ interp).symm, ?_⟩
  rcases h with ⟨_, hE, hD, hX, hPub, hEnc, hDec⟩
  refine ⟨fun p k iv hk hiv => ?_, fun c k iv hk hiv => ?_, fun a b => ?_, fun a => ?_,
    fun pk rand => ?_, fun sk ct => ?_⟩
  · rw [withShaFInterp_ne F₀ interp (by decide)]; exact hE p k iv hk hiv
  · rw [withShaFInterp_ne F₀ interp (by decide)]; exact hD c k iv hk hiv
  · rw [withShaFInterp_ne F₀ interp (by decide)]; exact hX a b
  · rw [withShaFInterp_ne F₀ interp (by decide)]; exact hPub a
  · rw [withShaFInterp_ne F₀ interp (by decide)]; exact hEnc pk rand
  · rw [withShaFInterp_ne F₀ interp (by decide)]; exact hDec sk ct

theorem externContractsHoldCli_withShaFInterp
    (F₀ : ShaState → HwBytes → ShaState)
    {interp : ExternInterpretation} (h : ExternContractsHoldCli interp) :
    ExternContractsHoldCli (withShaFInterp F₀ interp) := by
  rcases h with ⟨hlaws, hcanon, htor⟩
  have hne_ag : x25519AgreementSymbol ≠ sha256CompressSymbol := by decide
  have hne_pk : x25519PublicKeySymbol ≠ sha256CompressSymbol := by decide
  have hne_ts : DY.Libsignal.Refinement.x25519TorsionSymbol ≠ sha256CompressSymbol := by decide
  have hne_enc : aesCbcEncryptSymbol ≠ sha256CompressSymbol := by decide
  have hne_dec : aesCbcDecryptSymbol ≠ sha256CompressSymbol := by decide
  have hne_hm : DY.Libsignal.PQXDH.Refinement.libcruxHmacSymbol ≠ sha256CompressSymbol := by decide
  have hts : DY.Libsignal.Refinement.torsionShift (withShaFInterp F₀ interp) =
      DY.Libsignal.Refinement.torsionShift interp := by
    funext point t
    simp only [DY.Libsignal.Refinement.torsionShift, withShaFInterp_ne F₀ interp hne_ts]
  refine ⟨?_, ?_, ?_⟩
  · refine
      { x25519_agreement_commutes := fun a b => by
          simp only [withShaFInterp_ne F₀ interp hne_ag, withShaFInterp_ne F₀ interp hne_pk]
          exact hlaws.x25519_agreement_commutes a b
        x25519_agreement_length := fun s p => by
          simp only [withShaFInterp_ne F₀ interp hne_ag]
          exact hlaws.x25519_agreement_length s p
        x25519_public_key_length := fun s => by
          simp only [withShaFInterp_ne F₀ interp hne_pk]
          exact hlaws.x25519_public_key_length s
        x25519_agreement_reads_u_coordinate := fun s p p' hp hp' hu => by
          simp only [withShaFInterp_ne F₀ interp hne_ag]
          exact hlaws.x25519_agreement_reads_u_coordinate s p p' hp hp' hu
        x25519_agreement_torsion_invariant := fun s p t => by
          simp only [hts, withShaFInterp_ne F₀ interp hne_ag]
          exact hlaws.x25519_agreement_torsion_invariant s p t
        x25519_agreement_zero_iff_low_order := fun s p hs hp => by
          simp only [withShaFInterp_ne F₀ interp hne_ag]
          exact hlaws.x25519_agreement_zero_iff_low_order s p hs hp
        x25519_public_key_not_low_order := fun s hs => by
          simp only [withShaFInterp_ne F₀ interp hne_pk]
          exact hlaws.x25519_public_key_not_low_order s hs
        aes_cbc_decrypt_inverts_encrypt := fun pt k iv => by
          simp only [withShaFInterp_ne F₀ interp hne_dec, withShaFInterp_ne F₀ interp hne_enc]
          exact hlaws.aes_cbc_decrypt_inverts_encrypt pt k iv
        aes_cbc_encrypt_of_decrypt := fun c k iv p hk hiv hd => by
          simp only [withShaFInterp_ne F₀ interp hne_dec] at hd
          simp only [withShaFInterp_ne F₀ interp hne_enc]
          exact hlaws.aes_cbc_encrypt_of_decrypt c k iv p hk hiv hd
        hmac_tag_length := fun k d t ht => by
          simp only [withShaFInterp_ne F₀ interp hne_hm] at ht
          exact hlaws.hmac_tag_length k d t ht }
  · intro s
    simp only [withShaFInterp_ne F₀ interp hne_pk]
    exact hcanon s
  · intro s t k hk hu1 hu2
    simp only [hts, withShaFInterp_ne F₀ interp hne_pk] at hu1 hu2
    exact htor s t k hk hu1 hu2

theorem initDirs_withShaFInterp (F₀ : ShaState → HwBytes → ShaState)
    (interp : ExternInterpretation) (r : ProtocolSetup) :
    initDirs (withShaFInterp F₀ interp) r = initDirs interp r := by
  have hne_pk : x25519PublicKeySymbol ≠ sha256CompressSymbol := by decide
  have hpub : pubBytes (withShaFInterp F₀ interp) = pubBytes interp := by
    funext b
    simp only [pubBytes, withShaFInterp_ne F₀ interp hne_pk]
  funext p
  simp only [initDirs, commonFiles, bobPreKeyFiles, hpub]

theorem validCall_withShaFInterp (F₀ : ShaState → HwBytes → ShaState)
    (interp : ExternInterpretation) (r : ProtocolSetup) (t : CliTurn) (c : CliCall) :
    ValidCall (withShaFInterp F₀ interp) r t c ↔ ValidCall interp r t c := by
  have hne_pk : x25519PublicKeySymbol ≠ sha256CompressSymbol := by decide
  have hpub : pubBytes (withShaFInterp F₀ interp) = pubBytes interp := by
    funext b
    simp only [pubBytes, withShaFInterp_ne F₀ interp hne_pk]
  unfold ValidCall HonestBundleFiles HonestBundle
  cases c.cmd <;> simp only [hpub]

/-! ## Cross-`PEParams` `PqPartyEquiv` from `filesOf (encodeDir ...)` -/

theorem encodeDir_withShaF (F₀ : ShaState → HwBytes → ShaState)
    (P : PEParams) (st : PqParty) :
    encodeDir (withShaF F₀ P) st = encodeDir P st :=
  rfl

theorem hwf_clearSession {P P' : PEParams} {st : PqParty}
    (henc : ∀ s, encodeDir P' s = encodeDir P s)
    (hwf : PqxdhPartyInSpecDomain P st) :
    PqxdhPartyInSpecDomain P' { st with session := none } := by
  unfold PqxdhPartyInSpecDomain
  refine And.intro (fun _ _ h => nomatch h) (And.intro (fun f hf => ?_) hwf.2.2)
  rw [henc] at hf
  apply hwf.2.1 f
  unfold encodeDir at hf ⊢
  simp only [List.mem_append] at hf ⊢
  rcases hf with ((((h1 | h2) | h3) | h4) | h5) | h6
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h1))))
  · cases h2
  · exact Or.inl (Or.inl (Or.inl (Or.inr h3)))
  · exact Or.inl (Or.inl (Or.inr h4))
  · exact Or.inl (Or.inr h5)
  · exact Or.inr h6

theorem hwf_of_session_none {P P' : PEParams} {st : PqParty}
    (henc : ∀ s, encodeDir P' s = encodeDir P s)
    (hwf : PqxdhPartyInSpecDomain P st) (hsess : st.session = none) :
    PqxdhPartyInSpecDomain P' st := by
  have h0 := hwf_clearSession henc hwf
  cases st
  dsimp only at hsess h0
  subst hsess
  exact h0

private def optStep (q : Arm64.FsPath) (acc : Option HwBytes) (f : String × HwBytes) :
    Option HwBytes :=
  if q == Arm64.normalizePath f.1 then some f.2 else acc

private theorem foldl_optStep_eq_acc {q : Arm64.FsPath} {l : List (String × HwBytes)}
    (acc : Option HwBytes) (hne : ∀ f ∈ l, q ≠ Arm64.normalizePath f.1) :
    l.foldl (optStep q) acc = acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons f fs ih =>
    have hb : (q == Arm64.normalizePath f.1) = false :=
      beq_false_of_ne (hne f (List.mem_cons_self ..))
    simp only [List.foldl_cons, optStep, hb, Bool.false_eq_true, ↓reduceIte]
    exact ih acc (fun g hg => hne g (List.mem_cons_of_mem _ hg))

private def encPre (P : PEParams) (st : PqParty) : List (String × HwBytes) :=
  [(addressFile, textBytes (partyAddress st.party).text),
   (identityKeyPairFile, CryptoVerification.RecordCodecs.IdentityKeyPairStructure.encode
      ⟨djbKey (keyPairOf P.C st.me.idPriv).publicKey.bytes, st.me.idPriv.toList⟩),
   (registrationIdFile, le32 st.me.regId)] ++
  (match st.peerId with
   | some k => [(identityFile (partyAddressName st.party.other), k.serialize)]
   | none => [])

private def encSess (st : PqParty) : List (String × HwBytes) :=
  match st.session with
  | some (x, g) => [(sessionFile (partyAddress st.party.other), encodeRecordUnderExtras (fun _ => x) g)]
  | none => []

private def encPost (P : PEParams) (st : PqParty) : List (String × HwBytes) :=
  st.signed.map (fun (i, k) => (signedPreKeyFile i, signedRecordBytes P.C i k)) ++
  st.oneTime.map (fun (i, k) =>
    (oneTimePreKeyFile i, match k with | some sk => oneTimeRecordBytes P.C i sk | none => [])) ++
  st.kyberOneTime.map (fun (i, k) =>
    (oneTimeKyberPreKeyFile i, match k with | some k => kyberRecordBytes i k | none => [])) ++
  (st.kyberLastResort.map fun (i, k, seen) =>
    [(lastResortKyberPreKeyFile i, kyberRecordBytes i k), (baseKeysFile i, baseKeysBytes seen)]).flatten

private theorem encodeDir_split_sess (P : PEParams) (st : PqParty) :
    encodeDir P st = encPre P st ++ encSess st ++ encPost P st := by
  simp only [encodeDir, encPre, encSess, encPost, List.append_assoc]; rfl

private theorem head_ne_sessions_encPre {P : PEParams} {st : PqParty} {f : String × HwBytes}
    (hf : f ∈ encPre P st) : (Arm64.normalizePath f.1).head? ≠ some "sessions" := by
  simp only [encPre, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with (rfl | rfl | rfl) | hp
  · dsimp only; decide
  · dsimp only; decide
  · dsimp only; decide
  · cases hpeer : st.peerId <;> simp only [hpeer, List.not_mem_nil, List.mem_singleton] at hp
    rcases hp with rfl
    cases st.party <;> (dsimp only; decide)

private theorem head_ne_sessions_encPost {P : PEParams} {st : PqParty} {f : String × HwBytes}
    (hf : f ∈ encPost P st) : (Arm64.normalizePath f.1).head? ≠ some "sessions" := by
  simp only [encPost, List.mem_append, List.mem_map, List.mem_flatten] at hf
  rcases hf with (((⟨⟨i, _⟩, _, rfl⟩ | ⟨⟨i, _⟩, _, rfl⟩) | ⟨⟨i, _⟩, _, rfl⟩) | ⟨l, ⟨⟨i, _, _⟩, _, rfl⟩, hfl⟩)
  · obtain ⟨hsl, _, hemp, hdot⟩ := toString_nat_seg i.toNat
    rw [show signedPreKeyFile i = "signed-pre-keys" ++ "/" ++ toString i.toNat from rfl,
        normalizePath_two (by decide) (by decide) (by decide) hsl hemp hdot]
    simp only [List.head?_cons, ne_eq, Option.some.injEq]; decide
  · obtain ⟨hsl, _, hemp, hdot⟩ := toString_nat_seg i.toNat
    rw [show oneTimePreKeyFile i = "one-time-pre-keys" ++ "/" ++ toString i.toNat from rfl,
        normalizePath_two (by decide) (by decide) (by decide) hsl hemp hdot]
    simp only [List.head?_cons, ne_eq, Option.some.injEq]; decide
  · obtain ⟨hsl, _, hemp, hdot⟩ := toString_nat_seg i.toNat
    rw [show oneTimeKyberPreKeyFile i = "one-time-kyber-pre-keys" ++ "/" ++ toString i.toNat from rfl,
        normalizePath_two (by decide) (by decide) (by decide) hsl hemp hdot]
    simp only [List.head?_cons, ne_eq, Option.some.injEq]; decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hfl
    rcases hfl with rfl | rfl
    · obtain ⟨hsl, _, hemp, hdot⟩ := toString_nat_seg i.toNat
      rw [show lastResortKyberPreKeyFile i = "last-resort-kyber-pre-keys" ++ "/" ++ toString i.toNat from rfl,
          normalizePath_two (by decide) (by decide) (by decide) hsl hemp hdot]
      simp only [List.head?_cons, ne_eq, Option.some.injEq]; decide
    · rw [show baseKeysFile i = "last-resort-kyber-pre-keys" ++ "/" ++ toString i.toNat ++ ".base-keys" from rfl,
          normalizePath_dir_nat_suf i.toNat (by decide) (by decide) (by decide) (by decide)]
      simp only [List.head?_cons, ne_eq, Option.some.injEq]; decide

private theorem toString_one_local : toString (1 : Nat) = "1" := by
  change Nat.repr 1 = "1"
  rw [Nat.repr_of_lt (by omega), Nat.digitChar_eq_one.mpr rfl]
  rfl

private theorem head_eq_sessions_sessionFile (party : CryptoGames.Party) :
    (Arm64.normalizePath (sessionFile (partyAddress party))).head? = some "sessions" := by
  cases party <;>
    simp only [sessionFile, partyAddress, CryptoVerification.SignalSession.Address.text,
      partyAddressName, toString_one_local] <;>
    decide

private theorem filesOf_encodeDir_clearSession_eq (P : PEParams) (st : PqParty) (p : String) :
    filesOf (encodeDir P { st with session := none }) p =
      if (Arm64.normalizePath p).head? = some "sessions" then none
      else filesOf (encodeDir P st) p := by
  rw [filesOf_eq_optFold (regularFileList_encodeDir P { st with session := none }) p,
      filesOf_eq_optFold (regularFileList_encodeDir P st) p]
  change (encodeDir P { st with session := none }).foldl (optStep (Arm64.normalizePath p)) none =
    if (Arm64.normalizePath p).head? = some "sessions" then none
    else (encodeDir P st).foldl (optStep (Arm64.normalizePath p)) none
  rw [encodeDir_split_sess P { st with session := none }, encodeDir_split_sess P st]
  have hpre_eq : encPre P { st with session := none } = encPre P st := rfl
  have hpost_eq : encPost P { st with session := none } = encPost P st := rfl
  have hsess_nil : encSess { st with session := none } = [] := rfl
  rw [hpre_eq, hpost_eq, hsess_nil]
  simp only [List.append_nil, List.foldl_append]
  by_cases hhd : (Arm64.normalizePath p).head? = some "sessions"
  · simp only [hhd, ↓reduceIte]
    rw [foldl_optStep_eq_acc none (fun f hf h => head_ne_sessions_encPre hf (h ▸ hhd)),
        foldl_optStep_eq_acc none (fun f hf h => head_ne_sessions_encPost hf (h ▸ hhd))]
  · simp only [hhd, ↓reduceIte]
    congr 1
    symm
    refine foldl_optStep_eq_acc _ (fun f hf h => ?_)
    cases hs : st.session <;> simp only [encSess, hs, List.not_mem_nil, List.mem_singleton] at hf
    rcases hf with rfl
    exact hhd (h ▸ head_eq_sessions_sessionFile st.party.other)

private theorem filesOf_encodeDir_sessionFile (P : PEParams) (st : PqParty) :
    filesOf (encodeDir P st) (sessionFile (partyAddress st.party.other)) =
      st.session.map (fun p => encodeRecordUnderExtras (fun _ => p.1) p.2) := by
  let p₀ := sessionFile (partyAddress st.party.other)
  have hhd₀ : (Arm64.normalizePath p₀).head? = some "sessions" :=
    head_eq_sessions_sessionFile st.party.other
  rw [filesOf_eq_optFold (regularFileList_encodeDir P st) p₀]
  change (encodeDir P st).foldl (optStep (Arm64.normalizePath p₀)) none = _
  rw [encodeDir_split_sess P st]
  simp only [List.foldl_append]
  rw [foldl_optStep_eq_acc none (fun f hf h => head_ne_sessions_encPre hf (h ▸ hhd₀)),
      foldl_optStep_eq_acc _ (fun f hf h => head_ne_sessions_encPost hf (h ▸ hhd₀))]
  unfold encSess
  cases hs : st.session with
  | none => rfl
  | some xg =>
    rcases xg with ⟨x, g⟩
    simp only [List.foldl_cons, List.foldl_nil, optStep, p₀, beq_self_eq_true,
      ↓reduceIte, Option.map_some]

/-- Extracts `PqPartyEquiv st st₀` from `PqxdhPartyInSpecDomain P st` and weak decidable bounds
on `st₀` (no `ReachablePqxdhSession` required on `st₀`). -/
theorem pqPartyEquiv_of_weakWF {P : PEParams} {st st₀ : PqParty}
    (hwf : PqxdhPartyInSpecDomain P st)
    (hwf₀N : PqxdhPartyInSpecDomain P { st₀ with session := none })
    (hsess₀ : ∀ x₀ g₀, st₀.session = some (x₀, g₀) →
      g₀.party = st₀.party ∧ (encodeRecordUnderExtras (fun _ => x₀) g₀).length < 2 ^ 31)
    (hfiles : ∀ p, filesOf (encodeDir P st) p = filesOf (encodeDir P st₀) p) :
    PqPartyEquiv st st₀ := by
  have hwfN : PqxdhPartyInSpecDomain P { st with session := none } :=
    hwf_clearSession (fun _ => rfl) hwf
  have hfilesN : ∀ p, filesOf (encodeDir P { st with session := none }) p =
      filesOf (encodeDir P { st₀ with session := none }) p := fun p => by
    rw [filesOf_encodeDir_clearSession_eq, filesOf_encodeDir_clearSession_eq, hfiles p]
  have heqN : PqPartyEquiv { st with session := none } { st₀ with session := none } :=
    pqPartyEquiv_of_filesOf_encodeDir hwfN hwf₀N hfilesN
  have hparty : st.party = st₀.party := heqN.party_eq
  have hsess : Option.Rel (fun p p' => PqSessionEquiv p.1 p.2 p'.1 p'.2)
      st.session st₀.session := by
    have hsp := hfiles (sessionFile (partyAddress st.party.other))
    rw [filesOf_encodeDir_sessionFile P st, hparty, filesOf_encodeDir_sessionFile P st₀] at hsp
    cases hs : st.session <;> cases hs₀ : st₀.session
    · exact Option.Rel.none
    · simp [hs, hs₀] at hsp
    · simp [hs, hs₀] at hsp
    · rename_i xg xg₀
      rcases xg with ⟨x, g⟩
      rcases xg₀ with ⟨x₀, g₀⟩
      simp only [hs, hs₀, Option.map_some, Option.some.injEq] at hsp
      obtain ⟨_, hg_pty, hlen⟩ := hwf.1 x g hs
      obtain ⟨hg₀_pty, hlen₀⟩ := hsess₀ x₀ g₀ hs₀
      exact Option.Rel.some
        (CodecInjAux.pqSessionEquiv_of_encodeRecordX_eq
          (hg_pty.trans (hparty.trans hg₀_pty.symm)) hlen hlen₀ hsp)
  exact
    { party_eq := hparty
      me_eq := heqN.me_eq
      peerId_eq := heqN.peerId_eq
      session_rel := hsess
      signed_lookup := heqN.signed_lookup
      oneTime_lookup := heqN.oneTime_lookup
      kyberOneTime_lookup := heqN.kyberOneTime_lookup
      kyberLastResort_lookup := heqN.kyberLastResort_lookup
      signed_nodup := heqN.signed_nodup
      oneTime_nodup := heqN.oneTime_nodup
      kyberOneTime_nodup := heqN.kyberOneTime_nodup
      kyberLastResort_nodup := heqN.kyberLastResort_nodup }

/-- Cross-`PEParams` `PqPartyEquiv` when `st` is in `P`'s spec domain, `st₀` is in
`(withShaF F₀ P)`'s spec domain, and their encoded directories agree under `filesOf`. -/
theorem pqPartyEquiv_of_specDomain_pair {F₀ : ShaState → HwBytes → ShaState}
    {P : PEParams} {st st₀ : PqParty}
    (hwf : PqxdhPartyInSpecDomain P st)
    (hwf₀ : PqxdhPartyInSpecDomain (withShaF F₀ P) st₀)
    (hfiles : ∀ p, filesOf (encodeDir (withShaF F₀ P) st) p =
      filesOf (encodeDir (withShaF F₀ P) st₀) p) :
    PqPartyEquiv st st₀ :=
  pqPartyEquiv_of_weakWF hwf
    (hwf_clearSession (P := withShaF F₀ P) (P' := P) (fun _ => rfl) hwf₀)
    (fun x₀ g₀ hs₀ => ⟨(hwf₀.1 x₀ g₀ hs₀).2.1, (hwf₀.1 x₀ g₀ hs₀).2.2⟩) hfiles

/-! ## Symmetry and model-outcome congruence helpers -/

theorem pqSessionEquiv_symm {x x' : RecordExtras} {g g' : GhostState HwBytes}
    (h : PqSessionEquiv x g x' g') : PqSessionEquiv x' g' x g :=
  { party_eq := h.party_eq.symm
    session_eq := h.session_eq.symm
    remoteReg_eq := h.remoteReg_eq.symm
    localReg_eq := h.localReg_eq.symm
    aliceBase_eq := h.aliceBase_eq.symm
    pending_eq := fun hp' => (h.pending_eq (by rwa [h.session_eq])).symm }

theorem pqPartyEquiv_symm {st st' : PqParty} (h : PqPartyEquiv st st') :
    PqPartyEquiv st' st :=
  { party_eq := h.party_eq.symm
    me_eq := h.me_eq.symm
    peerId_eq := h.peerId_eq.symm
    session_rel := by
      have hrel := h.session_rel
      cases hs : st.session <;> cases hs' : st'.session <;> rw [hs, hs'] at hrel
      · exact .none
      · cases hrel
      · cases hrel
      · cases hrel with
        | some hse => exact .some (pqSessionEquiv_symm hse)
    signed_lookup := fun id => (h.signed_lookup id).symm
    oneTime_lookup := fun id => (h.oneTime_lookup id).symm
    kyberOneTime_lookup := fun id => (h.kyberOneTime_lookup id).symm
    kyberLastResort_lookup := fun id => (h.kyberLastResort_lookup id).symm
    signed_nodup := ⟨h.signed_nodup.2, h.signed_nodup.1⟩
    oneTime_nodup := ⟨h.oneTime_nodup.2, h.oneTime_nodup.1⟩
    kyberOneTime_nodup := ⟨h.kyberOneTime_nodup.2, h.kyberOneTime_nodup.1⟩
    kyberLastResort_nodup := ⟨h.kyberLastResort_nodup.2, h.kyberLastResort_nodup.1⟩ }

theorem pqPartyEquiv_clearSession {st st' : PqParty} (h : PqPartyEquiv st st') :
    PqPartyEquiv { st with session := none } { st' with session := none } :=
  { h with session_rel := .none }

theorem pqObserve_congr_local (P : PEParams) {i₀ i₁ : Inputs}
    {r₀ r₁ : Option (Option (PqParty × HwBytes))}
    (hreg₀ : RegularFileList i₀.files) (hreg₁ : RegularFileList i₁.files)
    (heq : InputsEquiv i₀ i₁) (hr : PqModelResultEquiv r₀ r₁) :
    pqxdhExpectedOutcome P i₀ r₀ = pqxdhExpectedOutcome P i₁ r₁ := by
  cases hr with
  | panic => rfl
  | reject =>
    simp only [pqxdhExpectedOutcome, Option.map, CryptoVerification.SignalSession.observe,
      Outcome.exited.injEq, true_and]
    funext p
    exact heq.2.2.2 p
  | accept hst =>
    simp only [pqxdhExpectedOutcome, Option.map, CryptoVerification.SignalSession.observe,
      Outcome.exited.injEq, true_and]
    funext p
    rw [filesOf_append_of_regular hreg₀ (regularFileList_encodeDir P _),
        filesOf_append_of_regular hreg₁ (regularFileList_encodeDir P _),
        filesOf_encodeDir_eq_of_pqPartyEquiv P hst p, heq.2.2.2 p]

theorem outcomeMatchesModelExceptPath_congr (P : PEParams) {i₀ i₁ : Inputs}
    {path : String} {r₀ r₁ : Option (Option (PqParty × HwBytes))} {o : Outcome}
    (hreg₀ : RegularFileList i₀.files) (hreg₁ : RegularFileList i₁.files)
    (heq : InputsEquiv i₀ i₁) (hr : PqModelResultEquiv r₀ r₁)
    (h₀ : OutcomeMatchesModelExceptPath P i₀ path r₀ o) :
    OutcomeMatchesModelExceptPath P i₁ path r₁ o := by
  have hob := pqObserve_congr_local P hreg₀ hreg₁ heq hr
  cases hr with
  | panic => simpa only [OutcomeMatchesModelExceptPath, ← hob] using h₀
  | reject => simpa only [OutcomeMatchesModelExceptPath, ← hob] using h₀
  | accept _ => simpa only [OutcomeMatchesModelExceptPath, ← hob] using h₀

theorem pqFieldsMatch_iff {x x' : RecordExtras} {g g' : GhostState HwBytes}
    (h : PqSessionEquiv x g x' g') (q : PreKeyFields) :
    PqFieldsMatch x g q ↔ PqFieldsMatch x' g' q := by
  unfold PqFieldsMatch
  rw [h.aliceBase_eq, h.session_eq]

private theorem tryDecryptFromRecord_pendingPreKey_local {PQ PQC : Type} [Inhabited PQ]
    (C : CryptoGames.LibsignalSession.Crypto) (spqr : CryptoGames.LibsignalSession.Spqr PQ PQC)
    (expected : Option (List (BitVec 8))) (ciphertext : CryptoGames.LibsignalSession.SignalMessage)
    (msgType : MessageType) (coins : BitVec 256) (record s : SessionState PQ)
    (pt : List (BitVec 8))
    (h : SessionState.tryDecryptFromRecord C spqr expected ciphertext msgType coins record =
      (.ok pt, s)) :
    s.pendingPreKey = false := by
  unfold SessionState.tryDecryptFromRecord at h
  split at h
  · cases h
  · cases hd : CryptoGames.LibsignalSession.Mut.exec
        (SessionState.tryDecryptWithState C spqr expected ciphertext msgType coins) record with
    | mk r updated =>
      rw [hd] at h
      cases r with
      | error _ => cases h
      | ok _ =>
        cases h
        unfold SessionState.tryDecryptWithState CryptoGames.LibsignalSession.Mut.exec at hd
        dsimp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.run, StateT.run, StateT.bind] at hd
        cases hf : TripleRatchet.fromSessionState record with
        | mk rf st1 =>
          rw [hf] at hd
          cases rf with
          | error _ => cases hd
          | ok tr0 =>
            dsimp only [ExceptT.bindCont] at hd
            cases hdec : TripleRatchet.decrypt C spqr expected ciphertext msgType coins tr0 with
            | mk rdec tr1 =>
              rw [hdec] at hd
              cases rdec with
              | error _ =>
                dsimp only [CryptoGames.LibsignalSession.liftE] at hd
                cases hd
              | ok _ =>
                dsimp only [CryptoGames.LibsignalSession.liftE, pure, ExceptT.pure, StateT.pure,
                  ExceptT.bindCont, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
                  StateT.bind] at hd
                cases hd
                rfl

private theorem pqPartyEquiv_with_peer_session_local {st₀ st₁ : PqParty}
    (hst : PqPartyEquiv st₀ st₁) (k : IdentityKey)
    {x₀ x₁ : RecordExtras} {g₀ g₁ : GhostState HwBytes}
    (hse : PqSessionEquiv x₀ g₀ x₁ g₁) :
    PqPartyEquiv { st₀ with peerId := some k, session := some (x₀, g₀) }
                 { st₁ with peerId := some k, session := some (x₁, g₁) } where
  party_eq := hst.party_eq
  me_eq := hst.me_eq
  peerId_eq := rfl
  session_rel := Option.Rel.some hse
  signed_lookup := hst.signed_lookup
  oneTime_lookup := hst.oneTime_lookup
  kyberOneTime_lookup := hst.kyberOneTime_lookup
  kyberLastResort_lookup := hst.kyberLastResort_lookup
  signed_nodup := hst.signed_nodup
  oneTime_nodup := hst.oneTime_nodup
  kyberOneTime_nodup := hst.kyberOneTime_nodup
  kyberLastResort_nodup := hst.kyberLastResort_nodup

theorem pqRecvMatchingFieldsModel_congr_local (P : PEParams) {st₀ st₁ : PqParty}
    (hst : PqPartyEquiv st₀ st₁) {x₀ x₁ : RecordExtras} {g₀ g₁ : GhostState HwBytes}
    (hse : PqSessionEquiv x₀ g₀ x₁ g₁) (q : PreKeyFields) (rc : BitVec 256) :
    PqModelResultEquiv (pqRecvMatchingFieldsModel P st₀ x₀ g₀ q rc)
      (pqRecvMatchingFieldsModel P st₁ x₁ g₁ q rc) := by
  unfold pqRecvMatchingFieldsModel
  dsimp only
  have htr := hst.trusts_eq ⟨⟨vec32 (q.identityKey.drop 1)⟩⟩
  have hrem : g₀.session.remoteIdentity = g₁.session.remoteIdentity := by rw [hse.session_eq]
  rw [htr, hrem]
  split_ifs
  · exact .reject
  · exact .reject
  · have hdec_eq : SessionState.tryDecryptFromRecord P.C (pqxdhSpqrSession P)
        ((pqxdhSessionParams P).expectedAddrs g₀.party) q.inner .preKey rc g₀.session =
        SessionState.tryDecryptFromRecord P.C (pqxdhSpqrSession P)
        ((pqxdhSessionParams P).expectedAddrs g₁.party) q.inner .preKey rc g₁.session := by
      rw [hse.party_eq, hse.session_eq]
    rw [hdec_eq]
    cases hd : SessionState.tryDecryptFromRecord P.C (pqxdhSpqrSession P)
        ((pqxdhSessionParams P).expectedAddrs g₁.party) q.inner .preKey rc g₁.session with
    | mk res s =>
      cases res with
      | error err =>
        cases err <;> first | exact .panic | exact .reject
      | ok pt =>
        dsimp only
        have hppk_false := tryDecryptFromRecord_pendingPreKey_local P.C (pqxdhSpqrSession P)
          ((pqxdhSessionParams P).expectedAddrs g₁.party) q.inner .preKey rc g₁.session s pt hd
        have hse' : PqSessionEquiv x₀ { g₀ with session := s } x₁ { g₁ with session := s } :=
          { party_eq := hse.party_eq
            session_eq := rfl
            remoteReg_eq := hse.remoteReg_eq
            localReg_eq := hse.localReg_eq
            aliceBase_eq := hse.aliceBase_eq
            pending_eq := fun hp => by rw [hppk_false] at hp; cases hp }
        exact .accept (pqPartyEquiv_with_peer_session_local hst _ hse')

theorem noMatchRecordBytes_congr {x x₀ x' x₀' : RecordExtras}
    {g g₀ g' g₀' : GhostState HwBytes}
    (hse : PqSessionEquiv x g x₀ g₀) (hse' : PqSessionEquiv x' g' x₀' g₀') :
    noMatchRecordBytes x g x' g' = noMatchRecordBytes x₀ g₀ x₀' g₀' := by
  unfold noMatchRecordBytes
  rw [encodeRecordX_eq_of_pqSessionEquiv hse']
  congr 2
  unfold encStateUnderExtras
  simp [hse.session_eq, hse.remoteReg_eq, hse.localReg_eq, hse.aliceBase_eq]

theorem noMatchSessionFile_transfer (X : UnreachedPqxdhPrimitives)
    {P P₀ : PEParams} {st st₀ : PqParty} {x x₀ : RecordExtras} {g g₀ : GhostState HwBytes}
    {m : PreKeyMessageFields} {rc : BitVec 256} {o : Outcome}
    (hst : PqPartyEquiv st st₀) (hse : PqSessionEquiv x g x₀ g₀)
    (hsha_nm : pqRecvPrekeyModel X P { st with session := none } m rc =
      pqRecvPrekeyModel X P₀ { st with session := none } m rc)
    (h₀ : NoMatchSessionFile X P₀ st₀ x₀ g₀ m rc o) :
    NoMatchSessionFile X P st x g m rc o := by
  intro st' out x' g' hok hs' code out' fs ho
  have hok₀ : pqRecvPrekeyModel X P₀ { st with session := none } m rc = some (some (st', out)) :=
    hsha_nm ▸ hok
  have hcongr := pqRecvPrekeyModel_congr X P₀ (pqPartyEquiv_clearSession hst) m rc
  rw [hok₀] at hcongr
  cases h_r0 : pqRecvPrekeyModel X P₀ { st₀ with session := none } m rc with
  | none => rw [h_r0] at hcongr; cases hcongr
  | some opt0 =>
    cases opt0 with
    | none => rw [h_r0] at hcongr; cases hcongr
    | some pair0 =>
      rcases pair0 with ⟨st₀', out₀⟩
      rw [h_r0] at hcongr
      cases hcongr with
      | accept hst' =>
        have hrel' := hst'.session_rel
        rw [hs'] at hrel'
        cases hs₀' : st₀'.session with
        | none => rw [hs₀'] at hrel'; cases hrel'
        | some xg₀' =>
          rcases xg₀' with ⟨x₀', g₀'⟩
          rw [hs₀'] at hrel'
          cases hrel' with
          | some hse' =>
            have hfs := h₀ st₀' out x₀' g₀' h_r0 hs₀' code out' fs ho
            rw [hst.party_eq, hfs, noMatchRecordBytes_congr hse hse']

end Symbolic.Proofs.Refinement.Composed.Cli.ElfShaGuardBridgeBase
