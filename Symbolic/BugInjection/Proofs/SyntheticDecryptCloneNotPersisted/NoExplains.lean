/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticRecvCommon.TraceState7003
import DY.Bytes.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.Trace.Basic

/-!
# Whole-Trace `Explains` Refutation for `DecryptCloneNotPersisted` (`m1Events`)

Establishes:
1. `knownBaseKeyOn_and_semPinned2_of_explains_m1_3`: explaining `[ev0, ev1_m1, ev2_m1]` pins
   `SemPinned2 S cl₁` and places Alice's base key `ek` in `bobDoneBaseKeys (runTrace r ss)`
   (`KnownBaseKeyOn`).
2. `not_explains_m1`: no `(g, ss, vis)` explains `m1Events = [ev0, ev1_m1, ev2_m1, ev3_m1]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace Symbolic.BugInjection.Proofs.SyntheticDecryptCloneNotPersisted

open ByteSpecs (hmacWith)
open DY
open scoped DY.Libsignal.Composed
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (CliEvent)
open DY.Libsignal.PQXDH (agree)
open DY.Libsignal.TripleRatchet
  (TRState TRSignalMsg RecvChain computeMac trMsgKeys kdfCk createChain
   findRecvChain consumeMessageKey)
open DY.Libsignal.Composed.Refinement
open Symbolic.Proofs.Tests.Shared.Composed.Runs (rnd StT ratchetState)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompI7003 hiding
  rk0Bytes seedA0Bytes cksA1Bytes seedB0Bytes cksA0Bytes cksB1Bytes cksB0Bytes
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompI7003Laws
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompFits7003
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.TraceEvents7003
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Gamma7003
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.PrefixPins7003
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.PrefixPins7003B
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.TraceState7003

attribute [local irreducible] Symbolic.BugInjection.hexBytes
attribute [local irreducible] ByteSpecs.hmacWith

private theorem unpack_m1_3
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry} {restEvs : List CliEvent}
    (hf : compFitsPinned7003 setup7003 compI7003 r)
    (hex : Explains compI7003 r S g ss vis (.run ev0 :: .run ev1_m1 :: .run ev2_m1 :: restEvs)) :
    ∃ tr₂ trB cl₁ ek₂ ct₂ keys₂ msg₂ seed₂ pq₂ m₂ key₂ st'₂ stB₁ c₂ c'₂ ss₃ vs₃,
      ThreeStepsOut r S g ss restEvs tr₂ trB cl₁ ek₂ ct₂ keys₂ msg₂ seed₂ pq₂ m₂ key₂
        st'₂ stB₁ c₂ c'₂ ss₃ vs₃ := by
  have hsplit : msg1M1Bytes = wire1M1Bytes ++ mac1M1Bytes := by decide +kernel
  have hwrap : runWrapped ev1_m1 = true := by
    dsimp only [runWrapped, ev1_m1]; rw [out1M1Raw_eq]; decide +kernel
  exact unpack_3_steps hf rfl rfl pt1M1Raw_eq coins1Raw_eq
    (congrArg (some ∘ Prod.mk 0) out1M1Raw_eq) hwrap out1M1_preKeyWire_eq (by decide) hsplit
    (by decide)
    (pqxdh_and_mac_facts_7003.2.2.2.2.1 ▸ pqxdh_and_mac_facts_7003.2.2.2.2.2.1)
    (pqxdh_and_mac_facts_7003.2.2.2.2.1 ▸ pqxdh_and_mac_facts_7003.2.2.2.2.2.2.1)
    ratchet_b_and_aes_facts_7003.2.2.2.2.2.2.2.2.2.2.2.1 trWireBytes_m1_eq
    rfl rfl out1M1Raw_eq coins2Raw_eq (congrArg (some ∘ Prod.mk 0) pt1M1Raw_eq) checkPreKey7003_m1 hex

private theorem out1M1_parse_inv :
    ∃ p, parsePreKeyWire out1M1Bytes = some p ∧
      p.baseKey.take 33 = ecKey (compPubOfIdx 3) ∧
      p.message = msg1M1Bytes ∧
      msg1M1Bytes.take (msg1M1Bytes.length - 8) = wire1M1Bytes ∧
      msg1M1Bytes.drop (msg1M1Bytes.length - 8) = mac1M1Bytes := by
  have h := checkPreKey7003_m1
  unfold checkPreKey7003 at h
  cases hp : parsePreKeyWire out1M1Bytes <;> rw [hp] at h
  · cases h
  · next p =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨p, rfl, h.1.1.1.1.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.1.1.2,
      h.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.2⟩

private theorem msg1M1_tryFrom_cnt0 :
    ∃ m : CryptoGames.LibsignalSession.SignalMessage,
      CryptoGames.LibsignalSession.SignalMessage.tryFrom
        CryptoVerification.LibsignalProtoCodec.protoSignalCodec msg1M1Bytes = .ok m ∧
      m.counter = 0 := by
  have h : (match CryptoGames.LibsignalSession.SignalMessage.tryFrom
      CryptoVerification.LibsignalProtoCodec.protoSignalCodec msg1M1Bytes with
    | .ok m => decide (m.counter = 0)
    | .error _ => false) = true := by decide +kernel
  cases htry : CryptoGames.LibsignalSession.SignalMessage.tryFrom
      CryptoVerification.LibsignalProtoCodec.protoSignalCodec msg1M1Bytes <;> rw [htry] at h
  · cases h
  · exact ⟨_, rfl, of_decide_eq_true h⟩

theorem knownBaseKeyOn_and_semPinned2_of_explains_m1_3
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry}
    (hf : compFitsPinned7003 setup7003 compI7003 r)
    (hex : Explains compI7003 r S g ss vis [.run ev0, .run ev1_m1, .run ev2_m1]) :
    (∃ cl₁, SemPinned2 S cl₁) ∧
    ∀ p, parsePreKeyWire out1M1Raw = some p → KnownBaseKeyOn compI7003 S g (runTrace r ss) p := by
  obtain ⟨tr₂, trB, cl₁, ek₂, ct₂, keys₂, msg₂, seed₂, pq₂, m₂, key₂, st'₂, stB₁, c₂, c'₂,
    ss₃, vs₃, hout⟩ := unpack_m1_3 hf hex
  refine ⟨⟨cl₁, hout.sem₂⟩, fun p hp => ?_⟩
  cases hout.hm₃ with
  | nil hinv₃ =>
    rw [out1M1Raw_eq] at hp
    obtain ⟨p₀, hp₀, hbk, _, _, _⟩ := out1M1_parse_inv
    cases hp.symm.trans hp₀
    refine ⟨ek₂, ?_, ?_⟩
    · rw [hout.run_eq, runSteps_invisible_bobDoneBaseKeys hinv₃]; exact hout.ek_mem
    · rw [hbk, hout.pinB.ek_eq]

theorem not_explains_m1
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry}
    (hf : compFitsPinned7003 setup7003 compI7003 r) :
    ¬ Explains compI7003 r S g ss vis m1Events := by
  intro hex
  obtain ⟨tr₂, trB, cl₁, ek₂, ct₂, keys₂, msg₂, seed₂, pq₂, m₂, key₂, st'₂, stB₁, c₂, c'₂,
    ss₃, vs₃, hout⟩ := unpack_m1_3 hf hex
  obtain ⟨pre₃, s₃, ss₄, v₃, vs₄, rfl, rfl, hinv₃, hrm₃, _⟩ :=
    matchesEventsAt_run_exit0_inv (rfl : ev3_m1.exit = some (0, pt1M1Raw)) hout.hm₃
  set tr₃ := runSteps pre₃ trB
  obtain ⟨p, hp_parse, hp_bk, hp_msg, hw_take, hm_drop⟩ := out1M1_parse_inv
  have hp_raw : parsePreKeyWire ev3_m1.input = some p := by
    dsimp only [ev3_m1]; rw [out1M1Raw_eq]; exact hp_parse
  have hek_mem₃ : ek₂ ∈ bobDoneBaseKeys tr₃ := by
    rw [runSteps_invisible_bobDoneBaseKeys hinv₃]; exact hout.ek_mem
  have hknown : ∃ ek ∈ bobDoneBaseKeys tr₃, ecKey (gamma compI7003 S g ek) = p.baseKey.take 33 :=
    ⟨ek₂, hek_mem₃, by rw [hout.pinB.ek_eq, hp_bk]⟩
  have hno₃ : NoSkippedKeys tr₃ := noSkippedKeys_runSteps_invisible hinv₃ hout.noSk
  cases s₃ with
  | bobStart _ _ _ _ _ _ _ =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hpf₃_all⟩ := hrm₃
    exact hpf₃_all p hp_raw hknown
  | messageDecryptSkipped _ _ _ _ _ _ =>
    exact not_messageDecryptSkipped_of_noSkippedKeys hno₃ hrm₃.2.2.2.2.1
  | messageDecrypt me stH msgH pqH idx =>
    obtain ⟨st, raw, msg, hme, hat_st, _, hparse, hrf, hcases⟩ := messageDecrypt_inv hrm₃
    subst me
    rw [runSteps_invisible_at?_trState hinv₃] at hat_st
    obtain ⟨_, hst_eq⟩ := hout.bob_st stH st hat_st
    subst st
    have hwrap₃ : runWrapped ev3_m1 = true := by
      dsimp only [runWrapped, ev3_m1]; rw [out1M1Raw_eq]; decide +kernel
    rw [hwrap₃] at hrf
    dsimp only [ReadsFaithfully] at hrf
    have hrep := hrf p hp_raw
    obtain ⟨_, _, _, hmsg_f⟩ := hrep
    obtain ⟨hg_wire, hg_mac, _, hm_inner⟩ := hmsg_f msg hparse
    rw [hp_msg, hw_take] at hg_wire
    rw [hp_msg, hm_drop] at hg_mac
    obtain ⟨m_in, hm_try, hm_cnt⟩ := msg1M1_tryFrom_cnt0
    obtain ⟨_, _, _, hcnt_eq, _⟩ := hm_inner m_in (hp_msg ▸ hm_try)
    have hcnt₀ : msg.counter = 0 := by
      rw [hm_cnt] at hcnt_eq
      exact UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hcnt_eq)
    rcases hcases with ⟨c, seed, c', pq, hfind, hcons, _⟩ | ⟨st', c, seed, c', pq, _, hrs, hcons, hmac⟩
    · rw [hout.pinB.recv_eq] at hfind
      dsimp only [findRecvChain, List.find?] at hfind
      split at hfind <;> cases hfind
      unfold consumeMessageKey at hcons
      rw [hcnt₀, hout.pinB.c'_idx] at hcons
      simp [show (0 : UInt32) < 1 by decide] at hcons
    · have hst'_eq : st' = (ratchetState stB₁ msg.ratchetKey (rnd tr₃.length 32)).1 :=
        (Prod.mk.inj hrs.symm).1
      have hc_eq : c = (ratchetState stB₁ msg.ratchetKey (rnd tr₃.length 32)).2 :=
        (Prod.mk.inj hrs.symm).2
      have hc_idx : c.index = 0 := by rw [hc_eq]; rfl
      have hc_ck : c.chainKey = (createChain stB₁.rk msg.ratchetKey stB₁.dhs).2 := by rw [hc_eq]; rfl
      have hseed_eq : seed = (kdfCk c.chainKey).2 := by
        unfold consumeMessageKey at hcons
        rw [hcnt₀, hc_idx] at hcons
        have h1 : ¬ ((0 : UInt32) < 0) := by decide
        have h2 : ¬ ((0 : UInt32).toNat - (0 : UInt32).toNat > DY.Libsignal.TripleRatchet.maxForwardJumps) := by decide
        have h3 : ¬ ((0 : UInt32) = DY.Libsignal.TripleRatchet.u32Max) := by decide
        rw [if_neg' h1, if_neg' h2, if_neg' h3] at hcons
        injection hcons with hp_s
        exact (Prod.mk.inj hp_s).1.symm
      have hg_hmac := congrArg (gamma compI7003 S g) hmac
      rw [hg_mac] at hg_hmac
      dsimp only [computeMac, DY.Libsignal.TripleRatchet.hmac] at hg_hmac
      have hpeer_ik : st'.peerIk = stB₁.peerIk := by rw [hst'_eq]; rfl
      have hmy_ik : st'.myIk = stB₁.myIk := by rw [hst'_eq]; rfl
      rw [gamma_trunc8, gamma_kdfExtract, gamma_concat, gamma_concat,
          hpeer_ik, hmy_ik, hout.pinB.peerIk_eq, hout.pinB.myIk_eq, hg_wire, ← List.append_assoc] at hg_hmac
      have hmk_len : (gamma compI7003 S g (trMsgKeys pq seed).macKey).length = 32 := by
        dsimp only [trMsgKeys, DY.Libsignal.TripleRatchet.hkdfBlock2, DY.Libsignal.TripleRatchet.hmac]
        rw [gamma_kdfExtract]; exact hmacWith_F7_length _ _
      have hg_mk : gamma compI7003 S g (trMsgKeys pq seed).macKey = macKey1Bytes :=
        (hmacWith_take8_inj_of_untagged hmk_len (by decide)
          (pqxdh_and_mac_facts_7003.2.2.2.2.1 ▸ pqxdh_and_mac_facts_7003.2.2.2.2.2.2.1)
          (hg_hmac.symm.trans (pqxdh_and_mac_facts_7003.2.2.2.2.1 ▸ pqxdh_and_mac_facts_7003.2.2.2.2.2.1).symm)).1
      dsimp only [trMsgKeys, DY.Libsignal.TripleRatchet.hkdfBlock2, DY.Libsignal.TripleRatchet.hmac] at hg_mk
      rw [gamma_kdfExtract] at hg_mk
      have hprk_len : (gamma compI7003 S g (DY.KdfExtract.kdfExtract pq seed)).length = 32 := by
        rw [gamma_kdfExtract]; exact hmacWith_F7_length _ _
      have hg_prk : gamma compI7003 S g (DY.KdfExtract.kdfExtract pq seed) = prkMsg1Bytes :=
        (hmacWith_inj_of_untagged hprk_len (by decide) ratchet_a_facts_7003.2.2.1
          (hg_mk.trans ratchet_a_facts_7003.2.1.symm)).1
      rw [gamma_kdfExtract] at hg_prk
      have hg_seed : gamma compI7003 S g seed = seedA0Bytes :=
        hmacWith_msg_inj_of_untagged (by decide : salt1Bytes.length ≤ 64)
          ratchet_a_facts_7003.2.2.2.2.2.2.1 (hg_prk.trans ratchet_a_facts_7003.2.2.2.2.2.1.symm)
      rw [hseed_eq] at hg_seed
      unfold kdfCk DY.Libsignal.TripleRatchet.hmac at hg_seed
      rw [gamma_kdfExtract] at hg_seed
      have hck_len : (gamma compI7003 S g c.chainKey).length = 32 := by
        rw [hc_ck]; dsimp only [createChain, DY.Libsignal.TripleRatchet.kdfRk,
          DY.Libsignal.TripleRatchet.hkdfBlock2, DY.Libsignal.TripleRatchet.hmac]
        rw [gamma_kdfExtract]; exact hmacWith_F7_length _ _
      have hg_ck : gamma compI7003 S g c.chainKey = cksA0Bytes :=
        (hmacWith_inj_of_untagged hck_len (by decide) ratchet_a_facts_7003.2.2.2.2.2.2.2.2.1
          (hg_seed.trans ratchet_a_facts_7003.2.2.2.2.2.2.2.1.symm)).1
      rw [hc_ck] at hg_ck
      dsimp only [createChain, DY.Libsignal.TripleRatchet.kdfRk,
        DY.Libsignal.TripleRatchet.hkdfBlock2, DY.Libsignal.TripleRatchet.hmac] at hg_ck
      rw [gamma_kdfExtract] at hg_ck
      set dh3 := DY.DiffieHellman.dh (DY.X25519.normalizeX25519Key msg.ratchetKey) stB₁.dhs
      have hprkRk_len : (gamma compI7003 S g (DY.KdfExtract.kdfExtract stB₁.rk dh3)).length = 32 := by
        rw [gamma_kdfExtract]; exact hmacWith_F7_length _ _
      have hg_prkRk : gamma compI7003 S g (DY.KdfExtract.kdfExtract stB₁.rk dh3) = prkA1Bytes :=
        (hmacWith_inj_of_untagged hprkRk_len (by decide) ratchet_a_facts_7003.2.2.2.2.2.2.2.2.2.2.2.2.1
          (hg_ck.trans ratchet_a_facts_7003.2.2.2.2.2.2.2.2.2.2.2.1.symm)).1
      rw [gamma_kdfExtract, hout.pinB.rk_eq] at hg_prkRk
      have hrk_eq : rk2Bytes = rk0Bytes :=
        (hmacWith_inj_of_untagged (by decide) (by decide) ratchet_a_facts_7003.2.2.2.2.2.2.2.2.2.2.2.2.2.2
          (hg_prkRk.trans ratchet_a_facts_7003.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm)).1
      exact absurd hrk_eq (by decide +kernel)
  | _ => exact absurd hrm₃.2.2.1 (by simp [Step.FitsCmd, ev3_m1])

end Symbolic.BugInjection.Proofs.SyntheticDecryptCloneNotPersisted
