/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticRecvCommon.PrefixPins7003B

/-!
# Algebraic MAC-Tag Non-Forgery and Clean-Prefix Dischargers for Seed 7003 (`MacLaws7003.lean`)

Provides:
1. `not_readCollisionCli_of_no_decrypt`: discharges `¬ ReadCollisionCli` on any clean prefix
   whose steps contain no `.messageDecrypt` or `.messageDecryptSkipped`.
2. `not_signalMsgAcceptedOnlyViaCollision_of_no_explains`: discharges
   `¬ SignalMsgAcceptedOnlyViaCollision` when the extended trace has no `Explains` witness.
3. Algebraic `¬ MacTagForgeryOrCollision` lemmas under `compI7003` via
   `hmacWith_take8_inj_of_untagged` and `hmacWith_msg_inj_of_untagged` (no `ownSalts` evaluation
   required, universally valid for all `S : OpaqueSymbolSemantics`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticRecvCommon.MacLaws7003

open ByteSpecs (hmacWith)
open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open scoped DY.Libsignal.Composed
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (RunEvent CliEvent)
open DY.Libsignal.TripleRatchet
  (TRSignalMsg hmac hkdfBlock1 hkdfBlock2 hkdfBlock3 trMsgKeys computeMac)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry TrialCtx
   gamma runTrace honestSaltsOf recvRepresentationsOn
   UnknownSeedMacGuess TruncatedMacSeedCollision MacTagForgeryOrCollision
   RecvCollisionOn ReselectCollisionOn Explains)
open DY.Libsignal.Composed.Refinement.Cli
  (ReadCollisionCli SignalMsgAcceptedOnlyViaCollision)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompI7003 (compI7003 compTag4)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompI7003Laws
  (F7 hmacWith_take8_inj_of_untagged)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Gamma7003
  (gamma_concat gamma_kdfExtract gamma_trunc8)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.PrefixPins7003
  (hmacWith_F7_length hmacWith_inj_of_untagged)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.PrefixPins7003B
  (hmacWith_msg_inj_of_untagged)

attribute [local irreducible] ByteSpecs.hmacWith

theorem not_readCollisionCli_of_no_decrypt {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step} {evs : List CliEvent}
    (hno : ∀ m ∈ ss, m.decryptMsgIdx? = none) :
    ¬ ReadCollisionCli interp r S g ss evs := by
  rintro ⟨_, _, _, ss₁, ss₂, m, _, msgIdx, _, _, _, _, rfl, _, _, _, _, hdec, _⟩
  have hm : m ∈ ss₁ ++ m :: ss₂ := by simp
  rw [hno m hm] at hdec
  cases hdec

theorem not_signalMsgAcceptedOnlyViaCollision_of_no_explains {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {evs₁ : List CliEvent} {ev : RunEvent} {b : HwBytes}
    {g' : Ghost} {ss' : List Step} {vis' : List VisEntry} {t : DY.Bytes}
    (hExp : Explains interp r S g' ss' vis' evs₁)
    (hNoRead : ¬ ReadCollisionCli interp r S g' ss' evs₁)
    (ht : t ∈ recvRepresentationsOn interp S g' (runTrace r ss') b)
    (hNoExp : ∀ g₁ ss₁ vis₁, ¬ Explains interp r S g₁ ss₁ vis₁ (evs₁ ++ [.run ev]))
    (hNoRecv : ¬ RecvCollisionOn interp r S g' (runTrace r ss') vis' (honestSaltsOf r ss') t)
    (hNoResel : ¬ ReselectCollisionOn interp r S g' (runTrace r ss') vis' (honestSaltsOf r ss') t) :
    ¬ SignalMsgAcceptedOnlyViaCollision interp r S g ss evs₁ ev b := by
  rintro ⟨_, hall⟩
  rcases hall g' ss' vis' hExp hNoRead with hallColl | ⟨⟨_, _, _, _, _, g₁, vis₁, _, _, _, _, _, hex₁⟩, _⟩
  · rcases hallColl t ht with hrc | hrs
    · exact hNoRecv hrc
    · exact hNoResel hrs
  · exact hNoExp g₁ _ vis₁ hex₁

@[local simp] private theorem gamma_hmac (S : OpaqueSymbolSemantics) (g : Ghost)
    (a b : DY.Bytes) :
    gamma compI7003 S g (hmac a b) =
      hmacWith F7 (gamma compI7003 S g a) (gamma compI7003 S g b) :=
  gamma_kdfExtract S g a b

theorem gamma_computeMac_eq (S : OpaqueSymbolSemantics) (g : Ghost)
    (mk pIk mIk w : DY.Bytes) :
    gamma compI7003 S g (computeMac mk pIk mIk w) =
      (hmacWith F7 (gamma compI7003 S g mk)
        (gamma compI7003 S g pIk ++ (gamma compI7003 S g mIk ++ gamma compI7003 S g w))).take 8 := by
  unfold computeMac
  rw [gamma_trunc8, gamma_hmac, gamma_concat, gamma_concat]

theorem gamma_trMsgKeys_congr_prk {S : OpaqueSymbolSemantics} {g : Ghost}
    {salt₁ seed₁ salt₂ seed₂ : DY.Bytes}
    (hprk : gamma compI7003 S g (hmac salt₁ seed₁) = gamma compI7003 S g (hmac salt₂ seed₂)) :
    (gamma compI7003 S g (trMsgKeys salt₁ seed₁).cipherKey,
     gamma compI7003 S g (trMsgKeys salt₁ seed₁).macKey,
     gamma compI7003 S g (trMsgKeys salt₁ seed₁).iv) =
    (gamma compI7003 S g (trMsgKeys salt₂ seed₂).cipherKey,
     gamma compI7003 S g (trMsgKeys salt₂ seed₂).macKey,
     gamma compI7003 S g (trMsgKeys salt₂ seed₂).iv) := by
  dsimp only [trMsgKeys]
  have hb1 : gamma compI7003 S g (hkdfBlock1 (hmac salt₁ seed₁) (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys")) =
             gamma compI7003 S g (hkdfBlock1 (hmac salt₂ seed₂) (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys")) := by
    unfold hkdfBlock1
    simp only [gamma_hmac S g (hmac salt₁ seed₁), gamma_hmac S g (hmac salt₂ seed₂), gamma_concat, hprk]
  have hb2 : gamma compI7003 S g (hkdfBlock2 (hmac salt₁ seed₁) (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys")) =
             gamma compI7003 S g (hkdfBlock2 (hmac salt₂ seed₂) (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys")) := by
    unfold hkdfBlock2
    simp only [gamma_hmac S g (hmac salt₁ seed₁), gamma_hmac S g (hmac salt₂ seed₂), gamma_concat, hb1, hprk]
  have hb3 : gamma compI7003 S g (hkdfBlock3 (hmac salt₁ seed₁) (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys")) =
             gamma compI7003 S g (hkdfBlock3 (hmac salt₂ seed₂) (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys")) := by
    unfold hkdfBlock3
    simp only [gamma_hmac S g (hmac salt₁ seed₁), gamma_hmac S g (hmac salt₂ seed₂), gamma_concat, hb2, hprk]
  exact Prod.ext hb1 (Prod.ext hb2 hb3)

theorem not_macTagForgery_singleton_honest {S : OpaqueSymbolSemantics} {g : Ghost}
    {known : DY.Bytes → Prop} {honest : List DY.Bytes} {msg : TRSignalMsg} {ctx₁ : TrialCtx}
    {salt_h seed_h : DY.Bytes} {mk_ref msg_ref : HwBytes}
    (hmem : salt_h ∈ honest)
    (hsalt_len : (gamma compI7003 S g salt_h).length ≤ 64)
    (hmac_eq : gamma compI7003 S g msg.mac = (hmacWith F7 mk_ref msg_ref).take 8)
    (hmk_eq : gamma compI7003 S g (trMsgKeys salt_h seed_h).macKey = mk_ref)
    (hmk_len : mk_ref.length = 32)
    (hmac_untag : (hmacWith F7 mk_ref msg_ref).take 4 ≠ compTag4)
    (hmk_untag : mk_ref.take 4 ≠ compTag4)
    (hprk_untag : (gamma compI7003 S g (hmac salt_h seed_h)).take 4 ≠ compTag4) :
    ¬ MacTagForgeryOrCollision compI7003 S g known honest msg [ctx₁] := by
  rintro (⟨ctx, hctx, seed, _, k_own, _, hmac1, _, hne⟩ |
          ⟨ctx, hctx, seed, hseed, _, _, _, ctx₀, hctx₀, seed₀, hseed₀, hseedNe, _⟩)
  · rw [gamma_computeMac_eq, hmac_eq] at hmac1
    have hmk1_len : (gamma compI7003 S g (trMsgKeys k_own seed).macKey).length = 32 := by
      dsimp only [trMsgKeys, hkdfBlock2]; rw [gamma_hmac]; exact hmacWith_F7_length _ _
    obtain ⟨hmk_pin, _⟩ := hmacWith_take8_inj_of_untagged hmk1_len hmk_len hmac_untag hmac1
    rw [← hmk_eq] at hmk_pin hmk_untag
    have hprk1_len : (gamma compI7003 S g (hmac k_own seed)).length = 32 := by
      rw [gamma_hmac]; exact hmacWith_F7_length _ _
    have hprk2_len : (gamma compI7003 S g (hmac salt_h seed_h)).length = 32 := by
      rw [gamma_hmac]; exact hmacWith_F7_length _ _
    dsimp only [trMsgKeys, hkdfBlock2] at hmk_pin hmk_untag
    rw [gamma_hmac S g (hmac salt_h seed_h)] at hmk_untag
    rw [gamma_hmac S g (hmac k_own seed), gamma_hmac S g (hmac salt_h seed_h)] at hmk_pin
    obtain ⟨hprk_pin, _⟩ := hmacWith_inj_of_untagged hprk1_len hprk2_len hmk_untag hmk_pin
    have hprk_untag' : (hmacWith F7 (gamma compI7003 S g salt_h) (gamma compI7003 S g seed_h)).take 4 ≠ compTag4 := by
      rwa [gamma_hmac] at hprk_untag
    rw [gamma_hmac, gamma_hmac] at hprk_pin
    have hseed_pin := hmacWith_msg_inj_of_untagged hsalt_len hprk_untag' hprk_pin
    rw [← hseed_pin] at hprk_pin
    have hprk_match : gamma compI7003 S g (hmac salt_h seed) = gamma compI7003 S g (hmac k_own seed) := by
      rw [gamma_hmac, gamma_hmac]; exact hprk_pin.symm
    exact hne salt_h hmem (gamma_trMsgKeys_congr_prk hprk_match)
  · rcases List.mem_singleton.mp hctx with rfl
    rcases List.mem_singleton.mp hctx₀ with rfl
    cases hseed.symm.trans hseed₀
    exact hseedNe rfl

theorem not_macTagForgery_of_msg_mismatch {S : OpaqueSymbolSemantics} {g : Ghost}
    {known : DY.Bytes → Prop} {honest : List DY.Bytes} {msg : TRSignalMsg} {ctxs : List TrialCtx}
    {mk_ref msg_ref : HwBytes}
    (hmac_eq : gamma compI7003 S g msg.mac = (hmacWith F7 mk_ref msg_ref).take 8)
    (hmk_len : mk_ref.length = 32)
    (hmac_untag : (hmacWith F7 mk_ref msg_ref).take 4 ≠ compTag4)
    (hmis : ∀ ctx ∈ ctxs, ∀ seed, ctx.seed? = some seed →
      gamma compI7003 S g ctx.peerIk ++
        (gamma compI7003 S g ctx.myIk ++ gamma compI7003 S g msg.wire) ≠ msg_ref) :
    ¬ MacTagForgeryOrCollision compI7003 S g known honest msg ctxs := by
  have hno : ∀ ctx ∈ ctxs, ∀ seed, ctx.seed? = some seed → ∀ k : DY.Bytes,
      gamma compI7003 S g (computeMac (trMsgKeys k seed).macKey ctx.peerIk ctx.myIk msg.wire) ≠
        gamma compI7003 S g msg.mac := by
    intro ctx hctx seed hseed k heq
    rw [gamma_computeMac_eq, hmac_eq] at heq
    have hmk1_len : (gamma compI7003 S g (trMsgKeys k seed).macKey).length = 32 := by
      dsimp only [trMsgKeys, hkdfBlock2, hmac]; rw [gamma_kdfExtract]; exact hmacWith_F7_length _ _
    obtain ⟨_, hmsg_eq⟩ := hmacWith_take8_inj_of_untagged hmk1_len hmk_len hmac_untag heq
    exact hmis ctx hctx seed hseed hmsg_eq
  rintro (⟨ctx, hctx, seed, hseed, k, _, hmac1, _⟩ |
          ⟨ctx, hctx, seed, hseed, k, _, hmac1, _⟩)
  · exact hno ctx hctx seed hseed k hmac1
  · exact hno ctx hctx seed hseed k hmac1

end Symbolic.BugInjection.Proofs.SyntheticRecvCommon.MacLaws7003
