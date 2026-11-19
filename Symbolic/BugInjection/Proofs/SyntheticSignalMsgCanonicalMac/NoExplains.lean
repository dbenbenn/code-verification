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
# Step 3 Pinning and Whole-Trace `Explains` Refutation for `SignalMsgCanonicalMac` (`m2Events`)

Establishes:
1. `semPinned4_of_explains_m2_4`: explaining `[ev0, ev1_m2, ev2_m2, ev3_m2]` pins
   `SemPinned4_M2 S cl₁ cl₃`.
2. `not_explains_m2`: no `(g, ss, vis)` explains `m2Events = [ev0, ev1_m2, ev2_m2, ev3_m2, ev4_m2]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace Symbolic.BugInjection.Proofs.SyntheticSignalMsgCanonicalMac

open ByteSpecs (hmacWith)
open DY
open scoped DY.Libsignal.Composed
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (CliEvent)
open DY.Libsignal.Refinement (WireFields)
open DY.Libsignal.TripleRatchet
  (TRState computeMac trMsgKeys kdfCk)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Composed.Refinement
open Symbolic.Proofs.Tests.Shared.Composed.Runs
  (StT encMsg encSig parse_encMsg ratchetState notInit_recv)
open Symbolic.BugInjection.Proofs.Common443.CliEventBridge (runMatches_filter_send_send)
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

private theorem unpack_m2_3
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry} {restEvs : List CliEvent}
    (hf : compFitsPinned7003 setup7003 compI7003 r)
    (hex : Explains compI7003 r S g ss vis (.run ev0 :: .run ev1_m2 :: .run ev2_m2 :: restEvs)) :
    ∃ tr₂ trB cl₁ ek₂ ct₂ keys₂ msg₂ seed₂ pq₂ m₂ key₂ st'₂ stB₁ c₂ c'₂ ss₃ vs₃,
      ThreeStepsOut r S g ss restEvs tr₂ trB cl₁ ek₂ ct₂ keys₂ msg₂ seed₂ pq₂ m₂ key₂
        st'₂ stB₁ c₂ c'₂ ss₃ vs₃ := by
  have hsplit : msg1M2Bytes = wire1M2Bytes ++ mac1M2Bytes := by decide +kernel
  have hwrap : runWrapped ev1_m2 = true := by
    dsimp only [runWrapped, ev1_m2]; rw [out1M2Raw_eq]; decide +kernel
  exact unpack_3_steps (ev1 := ev1_m2) (ev2 := ev2_m2) hf rfl rfl pt1M2Raw_eq coins1Raw_eq
    (congrArg (some ∘ Prod.mk 0) out1M2Raw_eq) hwrap out1M2_preKeyWire_eq (by decide) hsplit
    (by decide)
    (pqxdh_and_mac_facts_7003.2.2.2.2.2.2.2.1 ▸ pqxdh_and_mac_facts_7003.2.2.2.2.2.2.2.2.1)
    (pqxdh_and_mac_facts_7003.2.2.2.2.2.2.2.1 ▸ pqxdh_and_mac_facts_7003.2.2.2.2.2.2.2.2.2.1)
    ratchet_b_and_aes_facts_7003.2.2.2.2.2.2.2.2.2.2.2.2.1 trWireBytes_m2_1_eq
    rfl rfl out1M2Raw_eq coins2Raw_eq (congrArg (some ∘ Prod.mk 0) pt1M2Raw_eq) checkPreKey7003_m2 hex

private structure FourStepsM2Out (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (restEvs : List CliEvent) (trE₃ : ExecTrace) (cl₁ cl₃ : Nat)
    (ss₄ : List Step) (vs₄ : List VisEntry) : Prop where
  hm₄ : MatchesEventsAt compI7003 r S g (some (bundlePreKeyIds bun0Raw)) trE₃ ss₄ restEvs vs₄
  sem₄ : SemPinned4_M2 S cl₁ cl₃
  noSk : NoSkippedKeys trE₃
  alice_st : ∀ i st, trE₃.at? i = some (StT "alice" st) →
    gamma compI7003 S g st.myIk = ecKey (compPubOfIdx 0) ∧
    gamma compI7003 S g st.peerIk = ecKey (compPubOfIdx 1)

private theorem unpack_m2_4
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry} {restEvs : List CliEvent}
    (hf : compFitsPinned7003 setup7003 compI7003 r)
    (hex : Explains compI7003 r S g ss vis
      (.run ev0 :: .run ev1_m2 :: .run ev2_m2 :: .run ev3_m2 :: restEvs)) :
    ∃ trE₃ cl₁ cl₃ ss₄ vs₄, FourStepsM2Out r S g restEvs trE₃ cl₁ cl₃ ss₄ vs₄ := by
  obtain ⟨tr₂, trB, cl₁, ek₂, ct₂, keys₂, msg₂, seed₂, pq₂, m₂, key₂, st'₂, stB₁, c₂, c'₂,
    ss₃, vs₃, hout⟩ := unpack_m2_3 hf hex
  obtain ⟨pre₃, s₃, ss₄, v₃, vs₄, rfl, rfl, hinv₃, hrm₃, hm₄⟩ :=
    matchesEventsAt_run_exit0_inv (rfl : ev3_m2.exit = some (0, out3M2Raw)) hout.hm₃
  obtain ⟨hgwf₃, _⟩ := ghostWF_append hout.gwf₃
  obtain ⟨_, _, hlok₃, _⟩ := (stepsWF_append pre₃ (s₃ :: ss₄) trB).mp hout.swf₃
  obtain ⟨stH₃, cl₃, pqH₃, w₃, hs₃_eq, hls₃, _, _⟩ :=
    runMatches_filter_send_send (rfl : ev3_m2.cmd = .send peerAddrAlice) hrm₃
  dsimp only [ev3_m2] at hs₃_eq; subst hs₃_eq
  obtain ⟨st₃, hat_st₃, rfl, hnext₃, hls₃', hexp₃, hedr₃⟩ :=
    messageEncrypt_pin_aux hlok₃ hrm₃.2.2.2.2.1
  set tr₃ := runSteps pre₃ trB
  have hat_st₃' : trB.at? stH₃ = some (StT "bob" st₃) := by
    rwa [← runSteps_invisible_at?_trState hinv₃]
  obtain ⟨hstH_eq, hst_eq⟩ := hout.bob_st stH₃ st₃ hat_st₃'
  subst stH₃; subst st₃
  have hnb₃ : nextBundleIds (some (bundlePreKeyIds bun0Raw)) ev3_m2 =
      some (bundlePreKeyIds bun0Raw) := rfl
  rw [hnb₃, hnext₃] at hm₄
  set trE₃ := encTrCl tr₃ "bob" (tr₂.length + 8) stB₁ cl₃
  have hwrap₃ : runWrapped ev3_m2 = false := by
    dsimp only [runWrapped, ev3_m2]; rw [out3M2Raw_eq]; decide +kernel
  have hppk₃ : pendingPreKey tr₃ (tr₂.length + 8) = none := hout.ppk_bob pre₃ hinv₃
  obtain ⟨_, _, _, _, hok₃, _, hv₃_eq, inp₃, drs₃, outs₃, hv₃_split,
    hinp₃, hdrs₃, houts₃, _, _⟩ := hrm₃
  have hw₃_eq : w₃ = encMsg stB₁ (randTerm (tr₃.length + 1) cl₃)
      (DY.Spqr.spqrSend stB₁.spqr (randTerm (tr₃.length + 1) cl₃)).2.1
      (randTerm tr₃.length 32) := Option.some.inj (hls₃.symm.trans hls₃')
  subst hw₃_eq
  have hese₃ : encSendEntry tr₃ ((Step.messageEncrypt "bob" (tr₂.length + 8) cl₃ (tr₃.length + 2)).next tr₃)
      (tr₂.length + 8) false =
      [⟨.send, [encMsg stB₁ (randTerm (tr₃.length + 1) cl₃)
        (DY.Spqr.spqrSend stB₁.spqr (randTerm (tr₃.length + 1) cl₃)).2.1
        (randTerm tr₃.length 32)], .whisper, none⟩] := by
    unfold encSendEntry
    rw [hls₃', hppk₃]
  dsimp only [tr₃] at hexp₃ hls₃' hedr₃ hese₃ hv₃_eq
  dsimp only [stepView] at hv₃_eq
  rw [ite_eq_left_iff.mpr (fun h => absurd hok₃ h), hexp₃, List.append_nil,
      hwrap₃, hedr₃, hese₃, List.cons_append] at hv₃_eq
  have hinp₃_eq : inp₃ = ⟨.pt, [randTerm tr₃.length 32], .single, none⟩ :=
    (List.cons.inj (hv₃_split.symm.trans hv₃_eq)).1
  subst hinp₃_eq
  have houts₃_k : ∃ v, outs₃ = [v] ∧ v.kind = .send := by
    unfold OutputsMatch at houts₃
    obtain ⟨vo, rfl, hvo⟩ := houts₃
    exact ⟨vo, rfl, hvo.1.symm⟩
  obtain ⟨hdrs₃_eq, houts₃_eq⟩ :=
    drs_outs_of_stepView_send houts₃_k (hv₃_split.symm.trans hv₃_eq)
  dsimp only [ev3_m2, inputKind] at hinp₃
  rw [pt3M2Raw_eq] at hinp₃
  have hg_m₃ : gamma compI7003 S g (randTerm tr₃.length 32) = pt3M2Bytes :=
    List.singleton_injective hinp₃.2
  dsimp only [ev3_m2] at hdrs₃
  rw [hdrs₃_eq, coins3M2Raw_eq] at hdrs₃
  have hcl₃_pin := drawsMatch_nil_or_single (r := r) (S := S) (g := g)
    (ts := tr₃.length + 1) (cl := cl₃) (coins := coins3M2Bytes)
    (fun v hv hne => by
      subst hv
      refine hgwf₃.1 (rngEntry (randTerm (tr₃.length + 1) cl₃)) ?_ rfl (tr₃.length + 1) cl₃ hne
        (by simp [rngEntry])
      dsimp only [tr₃]
      rw [hv₃_eq]; simp [if_neg' hne])
    hdrs₃
  have hcl₃_le : cl₃ ≤ 64 := by
    have h64 : coins3M2Bytes.length = 64 := by decide
    omega
  have hg_coins₃ : gamma compI7003 S g (randTerm (tr₃.length + 1) cl₃) = coins3M2Bytes.take cl₃ :=
    hcl₃_pin.2
  set m₃ := randTerm tr₃.length 32
  set c₃ := randTerm (tr₃.length + 1) cl₃
  set pq₃ := (DY.Spqr.spqrSend stB₁.spqr c₃).2.1
  set w₃ := encMsg stB₁ c₃ pq₃ m₃
  unfold OutputsMatch at houts₃
  dsimp only [ev3_m2] at houts₃
  rw [out3M2Raw_eq, houts₃_eq] at houts₃
  obtain ⟨vo, hvo_eq, hbm_out⟩ := houts₃
  have hvo_inj := List.singleton_injective hvo_eq.symm
  subst hvo_inj
  dsimp only [BytesMatchEntry] at hbm_out
  obtain ⟨tw, htw_eq, hout3_eq⟩ := hbm_out.2
  have htw_inj := List.singleton_injective htw_eq.symm
  subst htw_inj
  have hg_w₃ : gamma compI7003 S g w₃ = body3M2Bytes :=
    (List.cons.inj (hout3_eq.symm.trans out3M2_split_eq.1)).2
  set keys₃ := trMsgKeys pq₃ (kdfCk stB₁.cks).2
  set wire₃ := DY.Libsignal.TripleRatchet.trHonestWireMsg
    (DY.DiffieHellman.dhPk stB₁.dhs) stB₁.ns stB₁.pn
    (DY.SymEnc.symEnc keys₃.cipherKey keys₃.iv m₃)
    (DY.Spqr.spqrSend stB₁.spqr c₃).2.2
  set mac_t₃ := computeMac keys₃.macKey stB₁.myIk stB₁.peerIk wire₃
  have hg_mac_len : (gamma compI7003 S g mac_t₃).length = 8 := by
    dsimp only [mac_t₃, computeMac, DY.Libsignal.TripleRatchet.hmac]
    rw [gamma_trunc8, gamma_kdfExtract, List.length_take, hmacWith_F7_length]; decide
  have hsplit_w₃ : gamma compI7003 S g wire₃ ++ gamma compI7003 S g mac_t₃ =
      wire3M2Bytes ++ mac3M2Bytes := by
    simpa [w₃, encMsg, gamma_concat] using hg_w₃.trans out3M2_split_eq.2.1
  obtain ⟨hg_wire₃, hg_mac₃⟩ :=
    append_inj_of_right_len hg_mac_len out3M2_split_eq.2.2.2.2.2 hsplit_w₃
  have hg_seedB : gamma compI7003 S g (kdfCk stB₁.cks).2 = seedB0Bytes := by
    unfold kdfCk DY.Libsignal.TripleRatchet.hmac DY.Libsignal.TripleRatchet.litByte
    rw [gamma_kdfExtract, hout.pinB.cks_eq, gamma_literalToBytes]
    have hb1 : ofByteArray (ByteArray.mk #[1]) = [0x01#8] := by decide
    rw [hb1]; exact ratchet_b_and_aes_facts_7003.2.2.2.1
  have hni : stB₁.spqr.view? DY.Spqr.InitState.SubF = none := by
    rw [hout.pinB.spqr_eq]; exact notInit_recv _ _
  have hpq₃_eq : pq₃ = ({ st := stB₁.spqr, coins := c₃ } : DY.Spqr.SendKey.SubF DY.Bytes).pack := by
    dsimp only [pq₃, DY.Spqr.spqrSend]; rw [hni]
  have hg_pq₃_bytes : gamma compI7003 S g pq₃ =
      spqrKeyBytes (S.sendKey (S.recvState (S.init pqrBytes [1#8]) pqMsg1Bytes)
        (coins3M2Bytes.take cl₃)) := by
    rw [hpq₃_eq, gamma_spqrSendKey, hout.pinB.spqr_bytes, hg_coins₃]
  have hg_mk₃_len : (gamma compI7003 S g keys₃.macKey).length = 32 := by
    dsimp only [keys₃, trMsgKeys, DY.Libsignal.TripleRatchet.hkdfBlock2,
      DY.Libsignal.TripleRatchet.hmac]
    rw [gamma_kdfExtract]; exact hmacWith_F7_length _ _
  have hg_mk₃ : gamma compI7003 S g keys₃.macKey = macKey3Bytes := by
    dsimp only [mac_t₃, computeMac, DY.Libsignal.TripleRatchet.hmac] at hg_mac₃
    rw [gamma_trunc8, gamma_kdfExtract, gamma_concat, gamma_concat,
        hout.pinB.myIk_eq, hout.pinB.peerIk_eq, hg_wire₃, ← List.append_assoc] at hg_mac₃
    exact (hmacWith_take8_inj_of_untagged hg_mk₃_len (by decide)
      (pqxdh_and_mac_facts_7003.2.2.2.2.2.2.2.2.2.2.1 ▸ pqxdh_and_mac_facts_7003.2.2.2.2.2.2.2.2.2.2.2.2.2)
      (hg_mac₃.trans (pqxdh_and_mac_facts_7003.2.2.2.2.2.2.2.2.2.2.1 ▸
        pqxdh_and_mac_facts_7003.2.2.2.2.2.2.2.2.2.2.2.2.1).symm)).1
  have hg_prkMsg₃_len : (gamma compI7003 S g (DY.Libsignal.TripleRatchet.hmac pq₃ (kdfCk stB₁.cks).2)).length = 32 := by
    unfold DY.Libsignal.TripleRatchet.hmac; rw [gamma_kdfExtract]; exact hmacWith_F7_length _ _
  have hg_prkMsg₃ : gamma compI7003 S g (DY.Libsignal.TripleRatchet.hmac pq₃ (kdfCk stB₁.cks).2) =
      prkMsg3Bytes := by
    dsimp only [keys₃, trMsgKeys, DY.Libsignal.TripleRatchet.hkdfBlock2,
      DY.Libsignal.TripleRatchet.hmac] at hg_mk₃
    rw [gamma_kdfExtract] at hg_mk₃
    exact (hmacWith_inj_of_untagged hg_prkMsg₃_len (by decide) ratchet_b_untagged.1
      (hg_mk₃.trans ratchet_b_and_aes_facts_7003.2.2.2.2.2.2.2.1.symm)).1
  have hg_pq₃_len : (gamma compI7003 S g pq₃).length = 32 := by
    rw [hg_pq₃_bytes]; exact spqrKeyBytes_length _
  have hsalt₃_pin : spqrKeyBytes (S.sendKey (S.recvState (S.init pqrBytes [1#8]) pqMsg1Bytes)
      (coins3M2Bytes.take cl₃)) = salt3Bytes := by
    rw [← hg_pq₃_bytes]
    unfold DY.Libsignal.TripleRatchet.hmac at hg_prkMsg₃
    rw [gamma_kdfExtract, hg_seedB] at hg_prkMsg₃
    exact (hmacWith_inj_of_untagged hg_pq₃_len (by decide) ratchet_b_untagged.2
      (hg_prkMsg₃.trans ratchet_b_and_aes_facts_7003.2.2.2.2.2.1.symm)).1
  have hg_encKey₃ : gamma compI7003 S g keys₃.cipherKey = encKey3Bytes := by
    dsimp only [keys₃, trMsgKeys, DY.Libsignal.TripleRatchet.hkdfBlock1]
    unfold DY.Libsignal.TripleRatchet.hmac DY.Libsignal.TripleRatchet.lit
      DY.Libsignal.TripleRatchet.litByte
    rw [gamma_kdfExtract, show gamma compI7003 S g (DY.KdfExtract.kdfExtract pq₃ (kdfCk stB₁.cks).2) =
        prkMsg3Bytes from hg_prkMsg₃, gamma_concat, gamma_literalToBytes, gamma_literalToBytes,
        ofByteArray_info_labels.2.2]
    have hb1 : ofByteArray (ByteArray.mk #[1]) = [0x01#8] := by decide
    rw [hb1]; exact ratchet_b_and_aes_facts_7003.2.2.2.2.2.2.1
  have hg_iv₃ : (gamma compI7003 S g keys₃.iv).take 16 = iv3Bytes := by
    change (gamma compI7003 S g
      (DY.KdfExtract.kdfExtract (DY.KdfExtract.kdfExtract pq₃ (kdfCk stB₁.cks).2)
        (DY.Concat.concat keys₃.macKey
          (DY.Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys")
            (DY.Libsignal.TripleRatchet.litByte 3))))).take 16 = iv3Bytes
    rw [gamma_kdfExtract, show gamma compI7003 S g (DY.KdfExtract.kdfExtract pq₃ (kdfCk stB₁.cks).2) =
        prkMsg3Bytes from hg_prkMsg₃, gamma_concat, hg_mk₃, gamma_concat]
    unfold DY.Libsignal.TripleRatchet.lit DY.Libsignal.TripleRatchet.litByte
    rw [gamma_literalToBytes, gamma_literalToBytes, ofByteArray_info_labels.2.2]
    have hb3 : ofByteArray (ByteArray.mk #[3]) = [0x03#8] := by decide
    rw [hb3, ← List.append_assoc, ratchet_b_and_aes_facts_7003.2.2.2.2.2.2.2.2.1]
    exact ratchet_b_and_aes_facts_7003.2.2.2.2.2.2.2.2.2.1
  have hg_ct₃ : gamma compI7003 S g (DY.SymEnc.symEnc keys₃.cipherKey keys₃.iv m₃) = ct3M2Bytes := by
    rw [gamma_symEnc, hg_encKey₃, hg_iv₃, hg_m₃, ratchet_b_and_aes_facts_7003.2.2.2.2.2.2.2.2.2.2.2.2.2]
  have hvo_mem : (⟨.send, [w₃], .whisper, none⟩ : VisEntry) ∈ v₃ := by
    rw [hv₃_eq]; simp
  have haddr_w₃ : g.addr wire₃ = [] :=
    (hgwf₃.2.2 _ hvo_mem rfl).2 rfl w₃ (encSig stB₁ c₃ pq₃ m₃) rfl (parse_encMsg stB₁ c₃ pq₃ m₃)
  have hpq_msg₃ : (DY.Spqr.spqrSend stB₁.spqr c₃).2.2 =
      ({ st := stB₁.spqr, coins := c₃ } : DY.Spqr.SendMsg.SubF DY.Bytes).pack := rfl
  have hg_wire₃' :
      trWireBytes [] DY.TrWire.canonicalVariation
        (WireFields.ofBytes [4#8] (compPubOfIdx 5) [0, 0, 0, 0] [0, 0, 0, 0] ct3M2Bytes)
        (gamma compI7003 S g (DY.Spqr.spqrSend stB₁.spqr c₃).2.2) = wire3M2Bytes := by
    have hw_unfold : wire₃ = DY.TrWire.trWireMsg DY.Libsignal.TripleRatchet.messageVersion
        (DY.DiffieHellman.dhPk stB₁.dhs) 0 0
        (DY.SymEnc.symEnc keys₃.cipherKey keys₃.iv m₃)
        (DY.Spqr.spqrSend stB₁.spqr c₃).2.2 DY.TrWire.canonicalVariation := by
      dsimp only [wire₃, DY.Libsignal.TripleRatchet.trHonestWireMsg]
      rw [hout.pinB.ns_eq, hout.pinB.pn_eq]
    rw [hw_unfold] at hg_wire₃ haddr_w₃
    rw [gamma_trWireMsg, haddr_w₃, hout.pinB.dhs_pk_eq, hg_ct₃] at hg_wire₃
    exact hg_wire₃
  have hpq_bytes_eq : gamma compI7003 S g (DY.Spqr.spqrSend stB₁.spqr c₃).2.2 = pqMsg3Bytes :=
    trWireBytes_pq_inj_7003 (by decide : 0 < pqMsg3Bytes.length)
      (by decide : pqMsg3Bytes.length < 64) (hg_wire₃'.trans trWireBytes_m2_3_eq.symm)
  rw [hpq_msg₃, gamma_spqrSendMsg, hout.pinB.spqr_bytes, hg_coins₃] at hpq_bytes_eq
  refine ⟨trE₃, cl₁, cl₃, ss₄, vs₄,
    ⟨hm₄, ⟨hout.sem₂, hlok₃.1, hsalt₃_pin, hpq_bytes_eq⟩,
     noSkippedKeys_encTrCl (noSkippedKeys_runSteps_invisible hinv₃ hout.noSk), ?_⟩⟩
  intro i st hat
  rw [encTrCl_trState_eq] at hat
  split at hat
  · simp [StT] at hat
  · rw [runSteps_invisible_at?_trState hinv₃] at hat
    exact hout.alice_st i st hat

theorem semPinned4_of_explains_m2_4
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry}
    (hf : compFitsPinned7003 setup7003 compI7003 r)
    (hex : Explains compI7003 r S g ss vis [.run ev0, .run ev1_m2, .run ev2_m2, .run ev3_m2]) :
    ∃ cl₁ cl₃, SemPinned4_M2 S cl₁ cl₃ := by
  obtain ⟨_, cl₁, cl₃, _, _, hout⟩ := unpack_m2_4 hf hex
  exact ⟨cl₁, cl₃, hout.sem₄⟩

private theorem ev4_mac_contradiction
    {S : OpaqueSymbolSemantics} {g : Ghost}
    {pq seed peerIk myIk wire mac : DY.Bytes}
    (hpeer : gamma compI7003 S g peerIk = ecKey (compPubOfIdx 1))
    (hmy : gamma compI7003 S g myIk = ecKey (compPubOfIdx 0))
    (hw : gamma compI7003 S g wire = wire4M2Bytes)
    (hm : gamma compI7003 S g mac = mac3M2Bytes)
    (hmac : mac = computeMac (trMsgKeys pq seed).macKey peerIk myIk wire) : False := by
  have hg := congrArg (gamma compI7003 S g) hmac
  rw [hm] at hg
  dsimp only [computeMac, DY.Libsignal.TripleRatchet.hmac] at hg
  rw [gamma_trunc8, gamma_kdfExtract, gamma_concat, gamma_concat,
      hpeer, hmy, hw, ← List.append_assoc] at hg
  have hmk_len : (gamma compI7003 S g (trMsgKeys pq seed).macKey).length = 32 := by
    dsimp only [trMsgKeys, DY.Libsignal.TripleRatchet.hkdfBlock2, DY.Libsignal.TripleRatchet.hmac]
    rw [gamma_kdfExtract]; exact hmacWith_F7_length _ _
  have hmsg_eq : ecKey (compPubOfIdx 1) ++ ecKey (compPubOfIdx 0) ++ wire4M2Bytes = macIn3M2Bytes :=
    (hmacWith_take8_inj_of_untagged hmk_len (by decide)
      pqxdh_and_mac_facts_7003.2.2.2.2.2.2.2.2.2.2.2.2.2
      (hg.symm.trans pqxdh_and_mac_facts_7003.2.2.2.2.2.2.2.2.2.2.2.2.1.symm)).2
  have hlen := congrArg List.length hmsg_eq
  have hl1 : (ecKey (compPubOfIdx 1)).length = 33 := by decide
  have hl0 : (ecKey (compPubOfIdx 0)).length = 33 := by decide
  simp only [List.length_append, hl1, hl0, in4M2_split_eq.2.2.2.2.1,
    pqxdh_and_mac_facts_7003.2.2.2.2.2.2.2.2.2.2.2.1] at hlen
  omega

theorem not_explains_m2
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry}
    (hf : compFitsPinned7003 setup7003 compI7003 r) :
    ¬ Explains compI7003 r S g ss vis m2Events := by
  intro hex
  obtain ⟨trE₃, _, _, ss₄, vs₄, hout⟩ := unpack_m2_4 hf hex
  obtain ⟨pre₄, s₄, _, _, _, rfl, rfl, hinv₄, hrm₄, _⟩ :=
    matchesEventsAt_run_exit0_inv (rfl : ev4_m2.exit = some (0, pt3M2Raw)) hout.hm₄
  set tr₄ := runSteps pre₄ trE₃
  have hno₄ : NoSkippedKeys tr₄ := noSkippedKeys_runSteps_invisible hinv₄ hout.noSk
  cases s₄ with
  | bobStart b a kh regA mh pqH spqrIdx =>
    obtain ⟨_, _, _, _, hok₄, _, hv₄_eq, inp₄, drs₄, outs₄, hv₄_split,
      hinp₄, _, _, _, _⟩ := hrm₄
    dsimp only [stepView, bobVis] at hv₄_eq
    rw [ite_eq_left_iff.mpr (fun h => absurd hok₄ h), List.cons_append] at hv₄_eq
    have hinp₄_eq := (List.cons.inj (hv₄_split.symm.trans hv₄_eq)).1
    subst hinp₄_eq
    dsimp only [BytesMatchEntry, ev4_m2] at hinp₄
    rw [in4M2Raw_eq] at hinp₄
    rcases _ : received tr₄ [mh.ek, mh.ct, mh.msg] ++ (bobOpkPk b kh tr₄).toList with
      _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | _⟩⟩⟩⟩ <;>
      simp_all [PreKeyRecvOpkMatches, OpkNamed, in4M2_split_eq.2.2.2.2.2]
  | messageDecryptSkipped _ _ _ _ _ _ =>
    exact not_messageDecryptSkipped_of_noSkippedKeys hno₄ hrm₄.2.2.2.2.1
  | messageDecrypt me stH msgH pqH idx =>
    obtain ⟨st, raw, msg, hme, hat_st, _, hparse, hrf, hcases⟩ := messageDecrypt_inv hrm₄
    dsimp only [ev4_m2] at hme; subst hme
    rw [runSteps_invisible_at?_trState hinv₄] at hat_st
    obtain ⟨hmy, hpeer⟩ := hout.alice_st stH st hat_st
    have hwrap₄ : runWrapped ev4_m2 = false := by
      dsimp only [runWrapped, ev4_m2]; rw [in4M2Raw_eq]; decide +kernel
    rw [hwrap₄] at hrf
    dsimp only [ReadsFaithfully, ev4_m2] at hrf
    rw [in4M2Raw_eq, in4M2_split_eq.1] at hrf
    obtain ⟨_, _, _, hmsg_f⟩ := hrf
    obtain ⟨hg_wire, hg_mac, _, _⟩ := hmsg_f msg hparse
    rw [in4M2_split_eq.2.2.1] at hg_wire
    rw [in4M2_split_eq.2.2.2.1] at hg_mac
    rcases hcases with ⟨_, seed, _, pq, _, _, hmac⟩ | ⟨st', _, seed, _, pq, _, hrs, _, hmac⟩
    · exact ev4_mac_contradiction hpeer hmy hg_wire hg_mac hmac
    · have hst'_eq : st' = (ratchetState st msg.ratchetKey
          (Symbolic.Proofs.Tests.Shared.Composed.Runs.rnd tr₄.length 32)).1 :=
        (Prod.mk.inj hrs.symm).1
      have hpeer' : gamma compI7003 S g st'.peerIk = ecKey (compPubOfIdx 1) := by
        rw [hst'_eq]; exact hpeer
      have hmy' : gamma compI7003 S g st'.myIk = ecKey (compPubOfIdx 0) := by
        rw [hst'_eq]; exact hmy
      exact ev4_mac_contradiction hpeer' hmy' hg_wire hg_mac hmac
  | _ => exact absurd hrm₄.2.2.1 (by simp [Step.FitsCmd, ev4_m2])

end Symbolic.BugInjection.Proofs.SyntheticSignalMsgCanonicalMac
