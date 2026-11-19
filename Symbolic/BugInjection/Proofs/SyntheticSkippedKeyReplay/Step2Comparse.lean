/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay.Dag

/-!
# MAC Forgery/Seed-Collision Refuters, Comparse Roundtrips, and Setup Equivalence
-/

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay

open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent CliEvent RunEvent)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.Composed.Refinement.Cli
open DY.Libsignal.PQXDH.Refinement (PreKeyFields)
open Symbolic.Swarm.CREF
open Symbolic.BugInjection
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compI0 compTag4 compSha256Rows)
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
  (cliSetupMatchesPinned_satisfiable_of_plausible compHooks0 compRecordsI0)
open Symbolic.BugInjection.Proofs.Common443.CompI0Laws (compI0_kyberCorrectOn)
open ByteSpecs
open Symbolic.BugInjection.Proofs.Common443.CompRTag
open Symbolic.BugInjection.Proofs.Common443.CompRI0ShaInj
open Symbolic.BugInjection.Proofs.Common443.CompRNbsc38MacKey
open Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire
open Symbolic.Swarm.COMPOSED

@[expose] public section

attribute [local irreducible] Symbolic.BugInjection.hexBytes

section Step2CleanAndCollisions

open DY.Libsignal.Refinement (sha256CompressFunction)
open DY.Libsignal.TripleRatchet
  (TRSignalMsg hmac hkdfBlock1 hkdfBlock2 hkdfBlock3 trMsgKeys computeMac)
open DY.Libsignal.Composed.Refinement
  (TrialCtx UnknownSeedMacGuess TruncatedMacSeedCollision MacTagForgeryOrCollision)
open ByteSpecs (hmacWith sha256With)
open _root_.Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compTag4)
open _root_.Symbolic.BugInjection.Proofs.Common443.CompRTag (sha256With_length)
open _root_.Symbolic.BugInjection.Proofs.Common443.CompRI0ShaInj (sha256With_inj_of_untagged)
open _root_.Symbolic.BugInjection.Proofs.Common443.CompRBobInit
  (F0 Tagged hmacWith_F0_of_inner hmacKey_length_le padKey_length gamma_concat0 gamma_hmac0)
open _root_.Symbolic.BugInjection.Proofs.Common443.CompRNbsc38MacKey
  (msgPrk gamma_hmac_compI0 gamma_macKey_length keyOfTake8_computeMac keyOfTake8_macKey)

theorem hmacWith_msg_inj_of_untagged {k₁ m₁ k₂ m₂ : HwBytes}
    (htag : (hmacWith F0 k₁ m₁).take 4 ≠ compTag4)
    (heq : hmacWith F0 k₁ m₁ = hmacWith F0 k₂ m₂) :
    m₁ = m₂ := by
  set k₁' := if 64 < k₁.length then sha256With F0 k₁ else k₁
  set k₂' := if 64 < k₂.length then sha256With F0 k₂ else k₂
  have hk₁ : k₁'.length ≤ 64 := hmacKey_length_le k₁
  have hk₂ : k₂'.length ≤ 64 := hmacKey_length_le k₂
  set p5c₁ := (k₁' ++ List.replicate (64 - k₁'.length) 0).map (· ^^^ (0x5c : BitVec 8))
  set p5c₂ := (k₂' ++ List.replicate (64 - k₂'.length) 0).map (· ^^^ (0x5c : BitVec 8))
  set p36₁ := (k₁' ++ List.replicate (64 - k₁'.length) 0).map (· ^^^ (0x36 : BitVec 8))
  set p36₂ := (k₂' ++ List.replicate (64 - k₂'.length) 0).map (· ^^^ (0x36 : BitVec 8))
  have h5c₁ : p5c₁.length = 64 := by simpa [p5c₁] using padKey_length k₁' hk₁
  have h5c₂ : p5c₂.length = 64 := by simpa [p5c₂] using padKey_length k₂' hk₂
  have h36₁ : p36₁.length = 64 := by simpa [p36₁] using padKey_length k₁' hk₁
  have h36₂ : p36₂.length = 64 := by simpa [p36₂] using padKey_length k₂' hk₂
  have hm₁ : hmacWith F0 k₁ m₁ = sha256With F0 (p5c₁ ++ sha256With F0 (p36₁ ++ m₁)) := rfl
  have hm₂ : hmacWith F0 k₂ m₂ = sha256With F0 (p5c₂ ++ sha256With F0 (p36₂ ++ m₂)) := rfl
  rw [hm₁] at htag
  rw [hm₁, hm₂] at heq
  have houter := sha256With_inj_of_untagged htag heq
  have hinner : sha256With F0 (p36₁ ++ m₁) = sha256With F0 (p36₂ ++ m₂) :=
    (List.append_inj houter (h5c₁.trans h5c₂.symm)).2
  have hinner_untagged : (sha256With F0 (p36₁ ++ m₁)).take 4 ≠ compTag4 := by
    intro hit
    have hhit : Tagged (sha256With F0 (p36₁ ++ m₁)) := ⟨sha256With_length F0 _, hit⟩
    have hout := hmacWith_F0_of_inner k₁ m₁ hhit
    exact htag (by simpa [hm₁] using hout.2)
  have hin_arg := sha256With_inj_of_untagged hinner_untagged hinner
  exact (List.append_inj hin_arg (h36₁.trans h36₂.symm)).2

theorem gamma_hmac_eq_of_gamma_eq {S : OpaqueSymbolSemantics} {g : Ghost}
    {k₁ m₁ k₂ m₂ : DY.Bytes}
    (hk : gamma compI0 S g k₁ = gamma compI0 S g k₂)
    (hm : gamma compI0 S g m₁ = gamma compI0 S g m₂) :
    gamma compI0 S g (hmac k₁ m₁) = gamma compI0 S g (hmac k₂ m₂) := by
  rw [gamma_hmac_compI0, gamma_hmac_compI0, hk, hm]

theorem gamma_concat_eq0 (S : OpaqueSymbolSemantics) (g : Ghost) (a b : DY.Bytes) :
    gamma compI0 S g (DY.Concat.concat a b) =
      gamma compI0 S g a ++ gamma compI0 S g b := by
  unfold gamma
  rw [concat_gamma' compI0 S g a b]
  rfl

theorem gamma_trMsgKeys_eq_of_msgPrk_eq {S : OpaqueSymbolSemantics} {g : Ghost}
    {s₁ d₁ s₂ d₂ : DY.Bytes}
    (hprk : gamma compI0 S g (msgPrk s₁ d₁) = gamma compI0 S g (msgPrk s₂ d₂)) :
    (gamma compI0 S g (trMsgKeys s₁ d₁).cipherKey,
     gamma compI0 S g (trMsgKeys s₁ d₁).macKey,
     gamma compI0 S g (trMsgKeys s₁ d₁).iv) =
    (gamma compI0 S g (trMsgKeys s₂ d₂).cipherKey,
     gamma compI0 S g (trMsgKeys s₂ d₂).macKey,
     gamma compI0 S g (trMsgKeys s₂ d₂).iv) := by
  have hprk' : gamma compI0 S g (hmac s₁ d₁) = gamma compI0 S g (hmac s₂ d₂) := hprk
  simp only [trMsgKeys, hkdfBlock3, hkdfBlock2, hkdfBlock1]
  have hb1 : gamma compI0 S g (hmac (hmac s₁ d₁) (DY.Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys") (DY.Libsignal.TripleRatchet.litByte 1))) =
      gamma compI0 S g (hmac (hmac s₂ d₂) (DY.Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys") (DY.Libsignal.TripleRatchet.litByte 1))) :=
    gamma_hmac_eq_of_gamma_eq hprk' rfl
  have hb2 : gamma compI0 S g (hmac (hmac s₁ d₁)
        (DY.Concat.concat (hmac (hmac s₁ d₁) (DY.Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys") (DY.Libsignal.TripleRatchet.litByte 1)))
          (DY.Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys") (DY.Libsignal.TripleRatchet.litByte 2)))) =
      gamma compI0 S g (hmac (hmac s₂ d₂)
        (DY.Concat.concat (hmac (hmac s₂ d₂) (DY.Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys") (DY.Libsignal.TripleRatchet.litByte 1)))
          (DY.Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys") (DY.Libsignal.TripleRatchet.litByte 2)))) := by
    apply gamma_hmac_eq_of_gamma_eq hprk'
    simp only [gamma_concat_eq0, hb1]
  have hb3 : gamma compI0 S g (hmac (hmac s₁ d₁)
        (DY.Concat.concat (hmac (hmac s₁ d₁)
          (DY.Concat.concat (hmac (hmac s₁ d₁) (DY.Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys") (DY.Libsignal.TripleRatchet.litByte 1)))
            (DY.Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys") (DY.Libsignal.TripleRatchet.litByte 2))))
          (DY.Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys") (DY.Libsignal.TripleRatchet.litByte 3)))) =
      gamma compI0 S g (hmac (hmac s₂ d₂)
        (DY.Concat.concat (hmac (hmac s₂ d₂)
          (DY.Concat.concat (hmac (hmac s₂ d₂) (DY.Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys") (DY.Libsignal.TripleRatchet.litByte 1)))
            (DY.Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys") (DY.Libsignal.TripleRatchet.litByte 2))))
          (DY.Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys") (DY.Libsignal.TripleRatchet.litByte 3)))) := by
    apply gamma_hmac_eq_of_gamma_eq hprk'
    simp only [gamma_concat_eq0, hb2]
  rw [hb1, hb2, hb3]

theorem seed_eq_of_honest_mac {S : OpaqueSymbolSemantics} {g : Ghost}
    {salt_h seed_h a_h b_h w_h salt seed a b w mac_t : DY.Bytes}
    (hmac_h : gamma compI0 S g (computeMac (trMsgKeys salt_h seed_h).macKey a_h b_h w_h) =
      gamma compI0 S g mac_t)
    (htag_mac : (gamma compI0 S g mac_t).take 4 ≠ compTag4)
    (htag_mk : (gamma compI0 S g (trMsgKeys salt_h seed_h).macKey).take 4 ≠ compTag4)
    (htag_prk : (gamma compI0 S g (msgPrk salt_h seed_h)).take 4 ≠ compTag4)
    (hmac : gamma compI0 S g (computeMac (trMsgKeys salt seed).macKey a b w) =
      gamma compI0 S g mac_t) :
    gamma compI0 S g seed = gamma compI0 S g seed_h ∧
    gamma compI0 S g (msgPrk salt seed) = gamma compI0 S g (msgPrk salt_h seed_h) := by
  have htag_c_h : (gamma compI0 S g (computeMac (trMsgKeys salt_h seed_h).macKey a_h b_h w_h)).take 4 ≠ compTag4 := by
    rw [hmac_h]; exact htag_mac
  have htag_c : (gamma compI0 S g (computeMac (trMsgKeys salt seed).macKey a b w)).take 4 ≠ compTag4 := by
    rw [hmac]; exact htag_mac
  have hmk_h := keyOfTake8_computeMac S g _ a_h b_h w_h (gamma_macKey_length S g salt_h seed_h) htag_c_h
  have hmk := keyOfTake8_computeMac S g _ a b w (gamma_macKey_length S g salt seed) htag_c
  rw [hmac_h] at hmk_h
  rw [hmac, hmk_h] at hmk
  have hmk_eq : gamma compI0 S g (trMsgKeys salt seed).macKey =
      gamma compI0 S g (trMsgKeys salt_h seed_h).macKey := (Option.some.inj hmk).symm
  have htag_mk' : (gamma compI0 S g (trMsgKeys salt seed).macKey).take 4 ≠ compTag4 := by
    rw [hmk_eq]; exact htag_mk
  have hprk_h := keyOfTake8_macKey S g salt_h seed_h htag_mk
  have hprk := keyOfTake8_macKey S g salt seed htag_mk'
  rw [hmk_eq, hprk_h] at hprk
  have hprk_eq : gamma compI0 S g (msgPrk salt seed) =
      gamma compI0 S g (msgPrk salt_h seed_h) := (Option.some.inj hprk).symm
  have hprk_unfold : hmacWith F0 (gamma compI0 S g salt_h) (gamma compI0 S g seed_h) =
      hmacWith F0 (gamma compI0 S g salt) (gamma compI0 S g seed) := by
    simpa only [msgPrk, gamma_hmac_compI0, F0] using hprk_eq.symm
  have htag_prk' : (hmacWith F0 (gamma compI0 S g salt_h) (gamma compI0 S g seed_h)).take 4 ≠ compTag4 := by
    simpa only [msgPrk, gamma_hmac_compI0, F0] using htag_prk
  exact ⟨(hmacWith_msg_inj_of_untagged htag_prk' hprk_unfold).symm, hprk_eq⟩

-- Universal MAC forgery & seed collision refuter when msg.mac is an honest untagged MAC
theorem not_unknownSeedMacGuess_of_honest_mac {S : OpaqueSymbolSemantics} {g : Ghost}
    {known : DY.Bytes → Prop} {honest : List DY.Bytes} {msg : TRSignalMsg} {ctxs : List TrialCtx}
    {salt_h seed_h a_h b_h w_h : DY.Bytes}
    (hsalt_mem : salt_h ∈ honest)
    (hmac_h : gamma compI0 S g (computeMac (trMsgKeys salt_h seed_h).macKey a_h b_h w_h) =
      gamma compI0 S g msg.mac)
    (htag_mac : (gamma compI0 S g msg.mac).take 4 ≠ compTag4)
    (htag_mk : (gamma compI0 S g (trMsgKeys salt_h seed_h).macKey).take 4 ≠ compTag4)
    (htag_prk : (gamma compI0 S g (msgPrk salt_h seed_h)).take 4 ≠ compTag4) :
    ¬ UnknownSeedMacGuess compI0 S g known honest msg ctxs := by
  rintro ⟨ctx, _, seed, _, k, _, hmac, _, hne⟩
  obtain ⟨hseed_eq, hprk_eq⟩ := seed_eq_of_honest_mac hmac_h htag_mac htag_mk htag_prk hmac
  have hprk_salt : gamma compI0 S g (msgPrk salt_h seed) = gamma compI0 S g (msgPrk k seed) := by
    have h1 : gamma compI0 S g (msgPrk salt_h seed) = gamma compI0 S g (msgPrk salt_h seed_h) :=
      gamma_hmac_eq_of_gamma_eq rfl hseed_eq
    exact h1.trans hprk_eq.symm
  exact hne salt_h hsalt_mem (gamma_trMsgKeys_eq_of_msgPrk_eq hprk_salt)

theorem not_truncatedMacSeedCollision_of_honest_mac {S : OpaqueSymbolSemantics} {g : Ghost}
    {honest : List DY.Bytes} {msg : TRSignalMsg} {ctxs : List TrialCtx}
    {salt_h seed_h a_h b_h w_h : DY.Bytes}
    (hmac_h : gamma compI0 S g (computeMac (trMsgKeys salt_h seed_h).macKey a_h b_h w_h) =
      gamma compI0 S g msg.mac)
    (htag_mac : (gamma compI0 S g msg.mac).take 4 ≠ compTag4)
    (htag_mk : (gamma compI0 S g (trMsgKeys salt_h seed_h).macKey).take 4 ≠ compTag4)
    (htag_prk : (gamma compI0 S g (msgPrk salt_h seed_h)).take 4 ≠ compTag4) :
    ¬ TruncatedMacSeedCollision compI0 S g honest msg ctxs := by
  rintro ⟨ctx, _, seed, _, k, _, hmac, ctx₀, _, seed₀, _, hne_seed, hdisj⟩
  have h1 := (seed_eq_of_honest_mac hmac_h htag_mac htag_mk htag_prk hmac).1
  have h2 : gamma compI0 S g seed₀ = gamma compI0 S g seed_h := by
    rcases hdisj with ⟨salt₀, _, hmac₀⟩ | ⟨peerIk₀, myIk₀, salt₀, w, hmsg_eq, _⟩
    · exact (seed_eq_of_honest_mac hmac_h htag_mac htag_mk htag_prk hmac₀).1
    · have hmac₀ : gamma compI0 S g (computeMac (trMsgKeys salt₀ seed₀).macKey peerIk₀ myIk₀ w) =
          gamma compI0 S g msg.mac := (congrArg (gamma compI0 S g) hmsg_eq).symm
      exact (seed_eq_of_honest_mac hmac_h htag_mac htag_mk htag_prk hmac₀).1
  exact hne_seed (h1.trans h2.symm)

theorem not_macTagForgeryOrCollision_of_honest_mac {S : OpaqueSymbolSemantics} {g : Ghost}
    {known : DY.Bytes → Prop} {honest : List DY.Bytes} {msg : TRSignalMsg} {ctxs : List TrialCtx}
    {salt_h seed_h a_h b_h w_h : DY.Bytes}
    (hsalt_mem : salt_h ∈ honest)
    (hmac_h : gamma compI0 S g (computeMac (trMsgKeys salt_h seed_h).macKey a_h b_h w_h) =
      gamma compI0 S g msg.mac)
    (htag_mac : (gamma compI0 S g msg.mac).take 4 ≠ compTag4)
    (htag_mk : (gamma compI0 S g (trMsgKeys salt_h seed_h).macKey).take 4 ≠ compTag4)
    (htag_prk : (gamma compI0 S g (msgPrk salt_h seed_h)).take 4 ≠ compTag4) :
    ¬ MacTagForgeryOrCollision compI0 S g known honest msg ctxs := by
  rintro (hug | htsc)
  · exact not_unknownSeedMacGuess_of_honest_mac hsalt_mem hmac_h htag_mac htag_mk htag_prk hug
  · exact not_truncatedMacSeedCollision_of_honest_mac hmac_h htag_mac htag_mk htag_prk htsc

end Step2CleanAndCollisions

section Step2ComparseAndStateSafe

theorem bool_serialize_singleton (b : Bool) :
    ∃ ba : ByteArray, ba.size = 1 ∧
      (_root_.Comparse.NonExtensibleMessageFormat.bool (Bytes := DY.Bytes)).serialize b =
        [DY.Literal.literalToBytes ba] :=
  Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.bool_serialize_singleton b

theorem bool_serialize_singleton_head (b : Bool) :
    ∃ ba : ByteArray, ba.size = 1 ∧
      ba = (if b then ⟨#[1]⟩ else ⟨#[0]⟩) ∧
      (_root_.Comparse.NonExtensibleMessageFormat.bool (Bytes := DY.Bytes)).serialize b =
        [DY.Literal.literalToBytes ba] :=
  Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue.bool_serialize_singleton_head b

theorem slowNat_serialize_zero :
    (_root_.Comparse.NonExtensibleMessageFormat.slowNat (Bytes := DY.Bytes)).serialize 0 =
      (_root_.Comparse.NonExtensibleMessageFormat.bool (Bytes := DY.Bytes)).serialize false :=
  Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.slowNat_serialize_zero

theorem slowNat_serialize_succ (n : Nat) :
    (_root_.Comparse.NonExtensibleMessageFormat.slowNat (Bytes := DY.Bytes)).serialize (n + 1) =
      (_root_.Comparse.NonExtensibleMessageFormat.bool (Bytes := DY.Bytes)).serialize true ++
        (_root_.Comparse.NonExtensibleMessageFormat.slowNat (Bytes := DY.Bytes)).serialize n :=
  Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.slowNat_serialize_succ n

theorem slowString_serialize_eq (s : String) :
    (_root_.Comparse.NonExtensibleMessageFormat.slowString (Bytes := DY.Bytes)).serialize s =
      (_root_.Comparse.NonExtensibleMessageFormat.slowNat (Bytes := DY.Bytes)).serialize s.utf8ByteSize ++
        [DY.Literal.literalToBytes s.toUTF8] :=
  Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.slowString_serialize_eq s

theorem uint32_serialize_singleton (x : UInt32) :
    ∃ b : ByteArray, b.size = 4 ∧
      (_root_.Comparse.NonExtensibleMessageFormat.uint32 (Bytes := DY.Bytes)).serialize x =
        [DY.Literal.literalToBytes b] :=
  Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.uint32_serialize_singleton x

theorem toUTF8_eq_utf8Encode (s : String) : s.toUTF8 = s.toList.utf8Encode := by
  conv_lhs => rw [← String.ofList_toList (s := s)]
  rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList]

theorem alice_utf8_size : "alice".toUTF8.size = 5 := by
  rw [toUTF8_eq_utf8Encode]; decide +kernel
theorem bob_utf8_size : "bob".toUTF8.size = 3 := by
  rw [toUTF8_eq_utf8Encode]; decide +kernel

theorem concatPrefixes_nil (s : DY.Bytes) :
    _root_.Comparse.concatPrefixes [] s = s := by
  rw [Symbolic.DYBridge.Comparse.concatPrefixes_eq_1]; rfl

theorem concatPrefixes_cons (p : DY.Bytes) (ps : List DY.Bytes) (s : DY.Bytes) :
    _root_.Comparse.concatPrefixes (p :: ps) s =
      DY.Concat.concat p (_root_.Comparse.concatPrefixes ps s) := by
  rw [Symbolic.DYBridge.Comparse.concatPrefixes_eq_1, Symbolic.DYBridge.Comparse.concatPrefixes_eq_1]
  rfl

theorem concatPrefixes_append_eq :
    ∀ (xs ys : List DY.Bytes) (s : DY.Bytes),
      _root_.Comparse.concatPrefixes (xs ++ ys) s =
        _root_.Comparse.concatPrefixes xs (_root_.Comparse.concatPrefixes ys s)
  | [], ys, s => by rw [List.nil_append, concatPrefixes_nil]
  | x :: xs, ys, s => by
    rw [List.cons_append, concatPrefixes_cons, concatPrefixes_cons, concatPrefixes_append_eq xs ys s]

theorem ai_concat_eq (a b : DY.Bytes) :
    DY.Libsignal.Composed.Refinement.assumedInjective (DY.Concat.concat a b) = false := by
  let x : DY.Concat.Concat.SubF DY.Bytes := { lhs := a, rhs := b }
  change DY.Libsignal.Composed.Refinement.assumedInjective x.pack = false
  unfold DY.Libsignal.Composed.Refinement.assumedInjective DY.Concat.Concat.SubF.pack
  rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Random.Random x,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.DiffieHellman.DhPk.SubF x,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.DiffieHellman.Dh.SubF x,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.KdfExtract.KdfExtract.SubF x,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.SymEnc.Enc.SubF x,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Trunc.Trunc8.SubF x,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.PQKem.Encap.SubF x,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.PQKem.SharedSecret.SubF x]
  rfl

theorem bool_ser_false :
    (_root_.Comparse.NonExtensibleMessageFormat.bool (Bytes := DY.Bytes)).serialize false =
      [DY.Libsignal.TripleRatchet.litByte 0] := by
  obtain ⟨ba, _, rfl, heq⟩ := bool_serialize_singleton_head false
  exact heq

theorem bool_ser_true :
    (_root_.Comparse.NonExtensibleMessageFormat.bool (Bytes := DY.Bytes)).serialize true =
      [DY.Libsignal.TripleRatchet.litByte 1] := by
  obtain ⟨ba, _, rfl, heq⟩ := bool_serialize_singleton_head true
  exact heq

theorem slowNat_pos_split :
    ∀ (r : Nat),
      ∃ mid : List DY.Bytes,
        (_root_.Comparse.NonExtensibleMessageFormat.slowNat (Bytes := DY.Bytes)).serialize (r + 1) =
          mid ++ [DY.Libsignal.TripleRatchet.litByte 1, DY.Libsignal.TripleRatchet.litByte 0]
  | 0 =>
    ⟨[], by rw [slowNat_serialize_succ, slowNat_serialize_zero, bool_ser_true, bool_ser_false]; rfl⟩
  | r + 1 => by
    obtain ⟨mid, ih⟩ := slowNat_pos_split r
    exact ⟨(_root_.Comparse.NonExtensibleMessageFormat.bool (Bytes := DY.Bytes)).serialize true ++ mid,
      by rw [slowNat_serialize_succ, ih, List.append_assoc]⟩

theorem safeMemo_bool_serialize {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    (b : Bool) :
    ∀ u ∈ (_root_.Comparse.NonExtensibleMessageFormat.bool (Bytes := DY.Bytes)).serialize b,
      DagSafeMemo S g pts u := by
  obtain ⟨ba, hsz, heq⟩ := bool_serialize_singleton b
  rw [heq]
  intro u hu
  rw [List.mem_singleton] at hu; subst hu
  exact safeMemo_lit_short (by omega)

theorem safeMemo_slowNat_serialize {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} :
    ∀ (n : Nat) (u : DY.Bytes),
      u ∈ (_root_.Comparse.NonExtensibleMessageFormat.slowNat (Bytes := DY.Bytes)).serialize n →
      DagSafeMemo S g pts u
  | 0, u, hu => by
    rw [slowNat_serialize_zero] at hu
    exact safeMemo_bool_serialize false u hu
  | n + 1, u, hu => by
    rw [slowNat_serialize_succ, List.mem_append] at hu
    rcases hu with hu | hu
    · exact safeMemo_bool_serialize true u hu
    · exact safeMemo_slowNat_serialize n u hu

theorem safeMemo_slowString_party {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {p : String} (hp : p = "alice" ∨ p = "bob") :
    ∀ u ∈ (_root_.Comparse.NonExtensibleMessageFormat.slowString (Bytes := DY.Bytes)).serialize p,
      DagSafeMemo S g pts u := by
  rw [slowString_serialize_eq]
  intro u hu
  rw [List.mem_append] at hu
  rcases hu with hu | hu
  · exact safeMemo_slowNat_serialize p.utf8ByteSize u hu
  · rw [List.mem_singleton] at hu; subst hu
    rcases hp with rfl | rfl
    · exact safeMemo_lit_short (by rw [alice_utf8_size]; omega)
    · exact safeMemo_lit_short (by rw [bob_utf8_size]; omega)

theorem safeMemo_uint32_serialize {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    (x : UInt32) :
    ∀ u ∈ (_root_.Comparse.NonExtensibleMessageFormat.uint32 (Bytes := DY.Bytes)).serialize x,
      DagSafeMemo S g pts u := by
  obtain ⟨ba, hsz, heq⟩ := uint32_serialize_singleton x
  rw [heq]
  intro u hu
  rw [List.mem_singleton] at hu; subst hu
  exact safeMemo_lit_short (by omega)

theorem gamma_concat_eq (S : OpaqueSymbolSemantics) (g : Ghost) (a b : DY.Bytes) :
    gamma compI0 S g (DY.Concat.concat a b) =
      gamma compI0 S g a ++ gamma compI0 S g b := by
  unfold gamma
  rw [concat_gamma' compI0 S g a b]
  rfl

theorem memo_concat_cases {S : OpaqueSymbolSemantics} {g : Ghost} {a b : DY.Bytes}
    {x : DY.Bytes × DY.Bytes × HwBytes}
    (hx : x ∈ (gamma' compI0 S g (DY.Concat.concat a b)).memo) :
    (x.1 = DY.Concat.concat a b ∧ x.2.2 = gamma compI0 S g a ++ gamma compI0 S g b) ∨
    x ∈ (gamma' compI0 S g a).memo ∨
    x ∈ (gamma' compI0 S g b).memo := by
  rw [concat_gamma' compI0 S g a b] at hx
  dsimp only [DY.Libsignal.Composed.Refinement.concretizeConcat,
    DY.Libsignal.Composed.Refinement.node] at hx
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.mem_cons, List.mem_append] at hx
  rcases hx with rfl | hxa | hxb
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inl hxa)
  · exact Or.inr (Or.inr hxb)

theorem safeMemo2_concatPrefixes_suffix {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} :
    ∀ (ps : List DY.Bytes) {s : DY.Bytes},
      (∀ p ∈ ps, SafeMemo2 S g pts p) →
      SafeMemo2 S g pts s →
      [0x01#8, 0x00#8] <:+ gamma compI0 S g s →
      SafeMemo2 S g pts (_root_.Comparse.concatPrefixes ps s) ∧
        [0x01#8, 0x00#8] <:+ gamma compI0 S g (_root_.Comparse.concatPrefixes ps s)
  | [], s, _, hs, hsfx => by
    rw [concatPrefixes_nil]
    exact ⟨hs, hsfx⟩
  | p :: ps, s, hps, hs, hsfx => by
    rw [concatPrefixes_cons]
    obtain ⟨ih_sm, pfx, hpfx⟩ := safeMemo2_concatPrefixes_suffix ps
      (fun q hq => hps q (List.mem_cons_of_mem p hq)) hs hsfx
    have hsfx_new :
        [0x01#8, 0x00#8] <:+ gamma compI0 S g (DY.Concat.concat p (_root_.Comparse.concatPrefixes ps s)) := by
      rw [gamma_concat_eq]
      exact ⟨gamma compI0 S g p ++ pfx, by rw [List.append_assoc, hpfx]⟩
    refine ⟨?_, hsfx_new⟩
    intro x hx
    rcases memo_concat_cases hx with ⟨hx1, hx2⟩ | hxp | hxr
    · refine Or.inr (Or.inl ⟨by rw [hx1]; exact ai_concat_eq _ _, Or.inr ?_⟩)
      rw [hx2, ← gamma_concat_eq]
      exact hsfx_new
    · exact hps p List.mem_cons_self x hxp
    · exact ih_sm x hxr

theorem safeMemo2_recvTail {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {c : DY.Libsignal.TripleRatchet.RecvChain} (hr : 1 ≤ c.rIdx) :
    SafeMemo2 S g pts (Symbolic.Proofs.Tests.CliNonvacuity.SessionDag.recvTailTerm c) ∧
      [0x01#8, 0x00#8] <:+ gamma compI0 S g (Symbolic.Proofs.Tests.CliNonvacuity.SessionDag.recvTailTerm c) := by
  have hr_eq : c.rIdx = (c.rIdx - 1) + 1 := by omega
  obtain ⟨mid, hmid⟩ := slowNat_pos_split (c.rIdx - 1)
  have temp : DagTermAt S g pts (_root_.Comparse.BytesLike.empty : DY.Bytes) id_empty := by
    change DagTermAt S g pts (DY.Literal.literalToBytes ByteArray.empty) id_empty
    exact termAt_lit dag_nodes_ok (by decide) rfl
  have tb0 : DagTermAt S g pts (DY.Libsignal.TripleRatchet.litByte 0) id_b0 :=
    termAt_lit dag_nodes_ok (by decide) rfl
  have tb1 : DagTermAt S g pts (DY.Libsignal.TripleRatchet.litByte 1) id_b1 :=
    termAt_lit dag_nodes_ok (by decide) rfl
  set s0 := DY.Concat.concat (DY.Libsignal.TripleRatchet.litByte 0) _root_.Comparse.BytesLike.empty
  set s1 := DY.Concat.concat (DY.Libsignal.TripleRatchet.litByte 1) s0
  have hs0_g : gamma compI0 S g s0 = [0x00#8] := by
    dsimp only [s0]; rw [gamma_concat_eq, tb0.gamma_eq, temp.gamma_eq]; decide +kernel
  have hs0_sm : SafeMemo2 S g pts s0 := by
    intro x hx
    rcases memo_concat_cases hx with ⟨hx1, hx2⟩ | hxa | hxb
    · refine Or.inr (Or.inl ⟨by rw [hx1]; exact ai_concat_eq _ _, Or.inl ?_⟩)
      rw [hx2, ← gamma_concat_eq, hs0_g]; decide
    · exact safeMemo_toSafeMemo2 tb0.safeMemo x hxa
    · exact safeMemo_toSafeMemo2 temp.safeMemo x hxb
  have hs1_g : gamma compI0 S g s1 = [0x01#8, 0x00#8] := by
    dsimp only [s1]; rw [gamma_concat_eq, tb1.gamma_eq, hs0_g]; decide +kernel
  have hs1_sfx : [0x01#8, 0x00#8] <:+ gamma compI0 S g s1 :=
    ⟨[], by rw [List.nil_append, hs1_g]⟩
  have hs1_sm : SafeMemo2 S g pts s1 := by
    intro x hx
    rcases memo_concat_cases hx with ⟨hx1, hx2⟩ | hxa | hxb
    · refine Or.inr (Or.inl ⟨by rw [hx1]; exact ai_concat_eq _ _, Or.inr ?_⟩)
      rw [hx2, ← gamma_concat_eq]; exact hs1_sfx
    · exact safeMemo_toSafeMemo2 tb1.safeMemo x hxa
    · exact hs0_sm x hxb
  have htail_eq : Symbolic.Proofs.Tests.CliNonvacuity.SessionDag.recvTailTerm c =
      _root_.Comparse.concatPrefixes
        ((_root_.Comparse.NonExtensibleMessageFormat.uint32 (Bytes := DY.Bytes)).serialize c.index ++ mid) s1 := by
    unfold Symbolic.Proofs.Tests.CliNonvacuity.SessionDag.recvTailTerm
    rw [hr_eq, hmid, ← List.append_assoc, concatPrefixes_append_eq]
    simp only [concatPrefixes_cons, concatPrefixes_nil, s1, s0]
  rw [htail_eq]
  refine safeMemo2_concatPrefixes_suffix _ (fun u hu => ?_) hs1_sm hs1_sfx
  rcases List.mem_append.mp hu with hu32 | hmid_u
  · exact safeMemo_toSafeMemo2 (safeMemo_uint32_serialize c.index u hu32)
  · have hsn : u ∈ (_root_.Comparse.NonExtensibleMessageFormat.slowNat (Bytes := DY.Bytes)).serialize c.rIdx := by
      rw [hr_eq, hmid]
      exact List.mem_append_left _ hmid_u
    exact safeMemo_toSafeMemo2 (safeMemo_slowNat_serialize c.rIdx u hsn)

theorem mem_of_getLast? {α : Type} : ∀ {l : List α} {a : α}, l.getLast? = some a → a ∈ l
  | [], _, h => by simp at h
  | [_], a, h => by simp at h; subst h; exact List.mem_cons_self
  | x :: _ :: _, a, h => List.mem_cons_of_mem x (mem_of_getLast? h)

theorem safeMemo2_trState_of_dr {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {ls ls₀ : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState}
    {cLast : DY.Libsignal.TripleRatchet.RecvChain}
    (hpart : ls.participant = ls₀.participant)
    (hdr : ls.state.toDRState = ls₀.state.toDRState)
    (hp_party : ls₀.participant = "alice" ∨ ls₀.participant = "bob")
    (hp_peer : ls₀.state.peer = "alice" ∨ ls₀.state.peer = "bob")
    (hspqr : DagSafeMemo S g pts ls.state.spqr)
    (hcore : ∀ u ∈ [ls₀.state.myIk, ls₀.state.peerIk, ls₀.state.rk,
                     ls₀.state.dhs, ls₀.state.cks, ls₀.state.sid],
      DagSafeMemo S g pts u)
    (hrecv : ∀ c ∈ ls₀.state.recv,
      DagSafeMemo S g pts c.ratchetKey ∧
      DagSafeMemo S g pts c.chainKey)
    (hlast : ls₀.state.recv.getLast? = some cLast)
    (hrIdx : 1 ≤ cLast.rIdx) :
    SafeMemo2 S g pts (DY.Comparse.serialize ls) := by
  have hrecv_eq : ls.state.recv = ls₀.state.recv := congrArg (·.recv) hdr
  have hanchor : Symbolic.Proofs.Tests.CliNonvacuity.SessionDag.stateAnchorPair ls =
      (cLast.chainKey, Symbolic.Proofs.Tests.CliNonvacuity.SessionDag.recvTailTerm cLast) := by
    unfold Symbolic.Proofs.Tests.CliNonvacuity.SessionDag.stateAnchorPair
    rw [hrecv_eq, hlast]
  obtain ⟨htail_sm2, pfx_tail, htail_sfx⟩ := safeMemo2_recvTail (S := S) (g := g) (pts := pts) hrIdx
  have hck_sm : DagSafeMemo S g pts cLast.chainKey :=
    (hrecv cLast (mem_of_getLast? hlast)).2
  intro x hx
  rcases Symbolic.Proofs.Tests.CliNonvacuity.SessionDag.serialize_localTR_memo compI0 S g ls hx with
    ⟨u, hu, hmx⟩ | ⟨hnai, pfx_sp, hsp⟩
  · have hu_sm2 : SafeMemo2 S g pts u := by
      unfold Symbolic.Proofs.Tests.CliNonvacuity.SessionDag.trStateProxyRoots at hu
      rw [hanchor, hpart] at hu
      dsimp only at hu
      have hpeer : ls.state.peer = ls₀.state.peer := congrArg (·.peer) hdr
      have hmyIk : ls.state.myIk = ls₀.state.myIk := congrArg (·.myIk) hdr
      have hpeerIk : ls.state.peerIk = ls₀.state.peerIk := congrArg (·.peerIk) hdr
      have hrk : ls.state.rk = ls₀.state.rk := congrArg (·.rk) hdr
      have hdhs : ls.state.dhs = ls₀.state.dhs := congrArg (·.dhs) hdr
      have hcks : ls.state.cks = ls₀.state.cks := congrArg (·.cks) hdr
      have hsid : ls.state.sid = ls₀.state.sid := congrArg (·.sid) hdr
      rw [hpeer, hmyIk, hpeerIk, hrk, hdhs, hcks, hsid, hrecv_eq] at hu
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        List.mem_flatMap] at hu
      rcases hu with (((((((((h1 | h2) | h3) | h4) | h5) | h6) | h7) | h8) | h9) | h10) | h11
      · exact safeMemo_toSafeMemo2 (safeMemo_bool_serialize true u h1)
      · exact safeMemo_toSafeMemo2 (safeMemo_bool_serialize false u h2)
      · exact safeMemo_toSafeMemo2 (safeMemo_slowString_party hp_party u h3)
      · exact safeMemo_toSafeMemo2 (safeMemo_slowString_party hp_peer u h4)
      · rcases h5 with rfl | rfl | rfl | rfl | rfl <;>
          exact safeMemo_toSafeMemo2 (hcore _ (by simp))
      · exact safeMemo_toSafeMemo2 (safeMemo_uint32_serialize ls.state.ns u h6)
      · exact safeMemo_toSafeMemo2 (safeMemo_uint32_serialize ls.state.pn u h7)
      · subst h8; exact safeMemo_toSafeMemo2 (hcore _ (by simp))
      · exact safeMemo_toSafeMemo2 (safeMemo_slowNat_serialize ls.state.rIdx u h9)
      · rcases h10 with rfl | rfl | rfl | rfl
        · exact safeMemo_toSafeMemo2 hspqr
        · exact safeMemo_toSafeMemo2 (safeMemo_lit_short (ba := ByteArray.empty) (by decide))
        · exact safeMemo_toSafeMemo2 hck_sm
        · exact htail_sm2
      · obtain ⟨c, hc_mem, hc_u⟩ := h11
        rcases hc_u with ((rfl | rfl) | hidx) | hridx
        · exact safeMemo_toSafeMemo2 (hrecv c hc_mem).1
        · exact safeMemo_toSafeMemo2 (hrecv c hc_mem).2
        · exact safeMemo_toSafeMemo2 (safeMemo_uint32_serialize c.index u hidx)
        · exact safeMemo_toSafeMemo2 (safeMemo_slowNat_serialize c.rIdx u hridx)
    exact hu_sm2 x hmx
  · rw [hanchor] at hsp
    dsimp only at hsp
    refine Or.inr (Or.inl ⟨hnai, Or.inr ⟨pfx_sp ++ gamma compI0 S g cLast.chainKey ++ pfx_tail, ?_⟩⟩)
    rw [List.append_assoc, List.append_assoc, htail_sfx, hsp]

-- r0 := compRecordsI0 setup normalization
noncomputable abbrev r0 : ProtocolSetup := compRecordsI0 setup

theorem setupTrace_eq_of_parties {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false) :
    setupTrace r = setupTrace r0 := by
  unfold setupTrace r0 compRecordsI0
  dsimp only
  rw [ha, hb, hopk]

theorem runTrace_eq_of_parties {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false)
    (ss : List Step) :
    runTrace r ss = runTrace r0 ss := by
  unfold runTrace
  rw [setupTrace_eq_of_parties ha hb hopk]

theorem storedStates_eq_of_parties {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false)
    (tr : ExecTrace) :
    storedStates r tr = storedStates r0 tr := by
  unfold storedStates
  rw [setupTrace_eq_of_parties ha hb hopk]

theorem availableStates_eq_of_parties {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false)
    (tr : ExecTrace) :
    availableStates r tr = availableStates r0 tr := by
  unfold availableStates
  rw [storedStates_eq_of_parties ha hb hopk]

theorem honestSaltsOf_eq_of_parties {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false)
    (ss : List Step) :
    honestSaltsOf r ss = honestSaltsOf r0 ss := by
  unfold honestSaltsOf
  rw [setupTrace_eq_of_parties ha hb hopk]

theorem prefixTerms_eq_of_parties {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false)
    (tr : ExecTrace) (vis : List VisEntry) :
    prefixTerms r tr vis = prefixTerms r0 tr vis := by
  unfold prefixTerms principalTerms
  rw [storedStates_eq_of_parties ha hb hopk]

theorem ownKeys_eq_of_parties {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false)
    (tr : ExecTrace) (st : DY.Libsignal.TripleRatchet.TRState)
    (msg : DY.Libsignal.TripleRatchet.TRSignalMsg) :
    ownKeys r tr st msg = ownKeys r0 tr st msg := by
  unfold ownKeys
  rw [availableStates_eq_of_parties ha hb hopk]

theorem whisperTrials_eq_of_parties {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false)
    (S : OpaqueSymbolSemantics) (g : Ghost) (tr : ExecTrace)
    (msg : DY.Libsignal.TripleRatchet.TRSignalMsg) :
    whisperTrials compI0 r S g tr msg = whisperTrials compI0 r0 S g tr msg := by
  unfold whisperTrials
  rw [availableStates_eq_of_parties ha hb hopk]
  split
  · dsimp only; congr 1; funext st; rw [ownKeys_eq_of_parties ha hb hopk]
  · rfl

theorem storedRatchetKeys_eq_of_parties {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false)
    (tr : ExecTrace) (msg : DY.Libsignal.TripleRatchet.TRSignalMsg) :
    storedRatchetKeys r tr msg = storedRatchetKeys r0 tr msg := by
  unfold storedRatchetKeys
  rw [availableStates_eq_of_parties ha hb hopk]

theorem bobTrials_eq_of_parties {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false)
    (tr : ExecTrace) (p : PreKeyFields) (x : PreKeyRep) (msg : DY.Libsignal.TripleRatchet.TRSignalMsg)
    (hp_opk : p.preKeyId = none) :
    bobTrials r tr p x msg = bobTrials r0 tr p x msg := by
  unfold bobTrials ProtocolSetup.ikAPubTerm ProtocolSetup.ikBPubTerm ProtocolSetup.ikBSecTerm
    ProtocolSetup.spkSecTerm ProtocolSetup.pqskSecTerm setupPublic setupSecret setupSent setupRandoms
  rw [hp_opk]
  dsimp only
  rw [hb, setupTrace_eq_of_parties ha hb hopk]
  rfl

end Step2ComparseAndStateSafe

end
end Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay
