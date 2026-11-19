/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticRecvCommon.PrefixPins7003
public import Symbolic.BugInjection.Proofs.Common443.CompRTag
import DY.Bytes.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import Symbolic.Proofs.Swarm.UA.XlateSteps
import Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAux
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Step 2 (`bobStart`), Step 3 (`messageEncrypt`), and Whole-Trace `Explains` Refutations for Seed 7003

Establishes:
1. `bobDone_nil_of_explains_m1_2`, `bobDone_nil_of_explains_m2_2`, `semPinned2_of_explains_m1_2`,
   `semPinned2_of_explains_m2_2`.
2. `pin_step2_bobStart`: characterizes `s₂ = .bobStart` at `ev2_m1` and `ev2_m2`.
3. `knownBaseKeyOn_and_semPinned2_of_explains_m1_3` and `not_explains_m1`.
4. `semPinned4_of_explains_m2_4` and `not_explains_m2`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace Symbolic.BugInjection.Proofs.SyntheticRecvCommon.PrefixPins7003B

open ByteSpecs (hmacWith sha256With)
open DY
open scoped DY.Libsignal.Composed
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (RunEvent CliEvent)
open DY.Libsignal.Refinement (WireFields canonicalVariation)
open DY.Libsignal.PQXDH
  (PQXDHState PQXDHEvent HandshakeKeys AliceHandshakeOut BobKeyHandles PreKeyMsgHandles
   agree serializedIk bobAgreement isCanonicalKey errToOption)
open DY.Libsignal.PQXDH.Refinement (wirePrekeyTag kyberEncapsSymbol)
open DY.Libsignal.TripleRatchet
  (TRState TREvent TRSignalMsg RecvChain SessionInfo parseTrSignalMsg computeMac trMsgKeys
   kdfCk createChain findRecvChain setRecvChain consumeMessageKey recvChainFor spqrA2B spqrB2A u32Max)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Composed (ComposedEvent)
open DY.Libsignal.Composed.Refinement
open Symbolic.Swarm.CREF (b1_setupTr4)
open Symbolic.Proofs.Swarm.UA.XlateSteps (stepIn_next stepIn_ok)
open Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAux (pack_of_view_eq_some)
open Symbolic.Proofs.Tests.Shared.Composed.Runs
  (Runs rnd RndE NetE EvP EvT EvC StP StT aliceOut aliceSt aliceTr aliceTrOpt
   bobOut bobSt0 encMsg encSig encSt parse_encMsg ratchetState skipTr recvSt)
open Symbolic.BugInjection.Proofs.Common443.CliEventBridge (runMatches_filter_send_send)
open Symbolic.BugInjection.Proofs.Common443.CompRTag (sha256With_length)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompI7003 hiding
  rk0Bytes seedA0Bytes cksA1Bytes seedB0Bytes cksA0Bytes cksB1Bytes cksB0Bytes
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompI7003Laws
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompFits7003
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.TraceEvents7003
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Gamma7003
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.PrefixPins7003

attribute [local irreducible] Symbolic.BugInjection.hexBytes

/-! ## 1. Arbitrary-Salt HMAC Message Injectivity -/

theorem hmacWith_msg_inj_of_untagged {k₁ k₂ m₁ m₂ : HwBytes}
    (hk₂ : k₂.length ≤ 64)
    (h₂ : (hmacWith F7 k₂ m₂).take 4 ≠ compTag4)
    (heq : hmacWith F7 k₁ m₁ = hmacWith F7 k₂ m₂) :
    m₁ = m₂ := by
  let k₁' := if 64 < k₁.length then sha256With F7 k₁ else k₁
  have hk₁'64 : k₁'.length ≤ 64 := by
    dsimp only [k₁']; split
    · have hl := sha256With_length F7 k₁; omega
    · omega
  have heq₁ : hmacWith F7 k₁ m₁ = hmacWith F7 k₁' m₁ := by
    unfold hmacWith
    have hn : ¬ 64 < k₁'.length := by omega
    simp only [k₁', hn, ↓reduceIte]
  rw [heq₁, hmacWith_eq k₁' m₁ hk₁'64, hmacWith_eq k₂ m₂ hk₂] at heq
  have hin₂ : (sha256With F7 (kblk k₂ 0x36 ++ m₂)).take 4 ≠ compTag4 :=
    hmac_inner_untagged k₂ m₂ hk₂ h₂
  rw [hmacWith_eq k₂ m₂ hk₂] at h₂
  have hout_eq := sha256With_take8_inj_of_untagged h₂ (congrArg (List.take 8) heq)
  have hx₁ := kblk_length k₁' 0x5c hk₁'64
  have hx₂ := kblk_length k₂ 0x5c hk₂
  have hin_eq : sha256With F7 (kblk k₁' 0x36 ++ m₁) =
      sha256With F7 (kblk k₂ 0x36 ++ m₂) := by
    have := congrArg (List.drop 64) hout_eq
    rwa [List.drop_left' hx₁, List.drop_left' hx₂] at this
  have hm_full := sha256With_take8_inj_of_untagged hin₂ (congrArg (List.take 8) hin_eq)
  have hy₁ := kblk_length k₁' 0x36 hk₁'64
  have hy₂ := kblk_length k₂ 0x36 hk₂
  have := congrArg (List.drop 64) hm_full
  rwa [List.drop_left' hy₁, List.drop_left' hy₂] at this

attribute [local irreducible] ByteSpecs.hmacWith

/-! ## 2. Trace Preservation Helpers Across `aliceTr` and `encTrCl` -/

private theorem range_split_le {a b : Nat} (h : a ≤ b) :
    List.range b = List.range a ++ List.range' a (b - a) := by
  induction h with
  | refl => simp
  | @step m hm ih =>
    have hle : a ≤ m := hm
    have hsub : m + 1 - a = (m - a) + 1 := by omega
    rw [List.range_succ, ih, hsub, List.range'_concat, List.append_assoc, Nat.one_mul,
      Nat.add_sub_cancel' hle]

theorem aliceTr_bobDone_eq (tr : ExecTrace) (a b : Participant) (ikA ikB spk pqpk : DY.Bytes) :
    bobDoneBaseKeys (aliceTr tr a b ikA ikB spk pqpk) = bobDoneBaseKeys tr := by
  unfold bobDoneBaseKeys
  set tr' := aliceTr tr a b ikA ikB spk pqpk
  have hlen : tr'.length = tr.length + 9 := by
    simp only [tr', aliceTr, aliceTrOpt, length_append_eq, Nat.add_assoc]
  let f : Nat → Option DY.Bytes := fun i =>
    match tr'.getEventAt PQXDHEvent i with
    | some (.BobDone _ _ _ _ _ _ _ ek _ _) => some ek
    | _ => none
  change (List.range tr'.length).filterMap f = _
  rw [range_split_le (by omega : tr.length ≤ tr'.length), List.filterMap_append]
  have htail : (List.range' tr.length (tr'.length - tr.length)).filterMap f = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro i hi; rw [List.mem_range'_1] at hi
    dsimp only [f, tr', aliceTr, aliceTrOpt]
    rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
    repeat first
      | rw [at?_append_other_eq (E₂ := DY.ProtocolEvent.ExecEntryT PQXDHEvent) rfl]
      | rw [at?_append_same_eq (fun _ => rfl)]
    simp only [length_append_eq, Nat.add_assoc]
    by_cases h5 : i = tr.length + 5
    · subst h5; simp
    · rw [if_neg' h5, at?_ge_length_eq tr (by omega)]
  rw [htail, List.append_nil]
  refine List.filterMap_congr fun i hi => ?_
  rw [List.mem_range] at hi
  dsimp only [f, tr', aliceTr, aliceTrOpt]
  rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
  repeat first
    | rw [at?_append_other_eq (E₂ := DY.ProtocolEvent.ExecEntryT PQXDHEvent) rfl]
    | rw [at?_append_same_eq (fun _ => rfl), if_neg' (by simp [length_append_eq, Nat.add_assoc]; omega)]
  rfl

theorem encTrCl_bobDone_eq (tr : ExecTrace) (me : Participant) (stH : Nat) (st : TRState) (cl : Nat) :
    bobDoneBaseKeys (encTrCl tr me stH st cl) = bobDoneBaseKeys tr := by
  unfold bobDoneBaseKeys
  set tr' := encTrCl tr me stH st cl
  have hlen : tr'.length = tr.length + 7 := by
    simp only [tr', encTrCl, length_append_eq, Nat.add_assoc]
  let f : Nat → Option DY.Bytes := fun i =>
    match tr'.getEventAt PQXDHEvent i with
    | some (.BobDone _ _ _ _ _ _ _ ek _ _) => some ek
    | _ => none
  change (List.range tr'.length).filterMap f = _
  rw [range_split_le (by omega : tr.length ≤ tr'.length), List.filterMap_append]
  have htail : (List.range' tr.length (tr'.length - tr.length)).filterMap f = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro i hi; rw [List.mem_range'_1] at hi
    dsimp only [f, tr', encTrCl]
    rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
    repeat rw [at?_append_other_eq (E₂ := DY.ProtocolEvent.ExecEntryT PQXDHEvent) rfl]
    rw [at?_ge_length_eq tr (by omega)]
  rw [htail, List.append_nil]
  refine List.filterMap_congr fun i hi => ?_
  dsimp only [f, tr', encTrCl]
  rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
  repeat rw [at?_append_other_eq (E₂ := DY.ProtocolEvent.ExecEntryT PQXDHEvent) rfl]
  rfl

theorem aliceTr_pqxdhState_eq (tr : ExecTrace) (a b : Participant) (ikA ikB spk pqpk : DY.Bytes) (i : Nat) :
    ((aliceTr tr a b ikA ikB spk pqpk).at? i :
      Option (DY.PersistentGlobalState.State.ExecEntryT
        (DY.PersistentLocalState.LocalState PQXDHState))) = tr.at? i := by
  unfold aliceTr aliceTrOpt
  repeat rw [at?_append_other_eq (E₂ := DY.PersistentGlobalState.State.ExecEntryT
    (DY.PersistentLocalState.LocalState PQXDHState)) rfl]

theorem encTrCl_pqxdhState_eq (tr : ExecTrace) (me : Participant) (stH : Nat) (st : TRState) (cl i : Nat) :
    ((encTrCl tr me stH st cl).at? i :
      Option (DY.PersistentGlobalState.State.ExecEntryT
        (DY.PersistentLocalState.LocalState PQXDHState))) = tr.at? i := by
  unfold encTrCl
  repeat rw [at?_append_other_eq (E₂ := DY.PersistentGlobalState.State.ExecEntryT
    (DY.PersistentLocalState.LocalState PQXDHState)) rfl]

theorem encTrCl_pqxdhEvent_eq (tr : ExecTrace) (me : Participant) (stH : Nat) (st : TRState) (cl i : Nat) :
    ((encTrCl tr me stH st cl).at? i : Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) = tr.at? i := by
  unfold encTrCl
  repeat rw [at?_append_other_eq (E₂ := DY.ProtocolEvent.ExecEntryT PQXDHEvent) rfl]

theorem encTrCl_compEvent_eq (tr : ExecTrace) (me : Participant) (stH : Nat) (st : TRState) (cl i : Nat) :
    ((encTrCl tr me stH st cl).at? i : Option (DY.ProtocolEvent.ExecEntryT ComposedEvent)) = tr.at? i := by
  unfold encTrCl
  repeat rw [at?_append_other_eq (E₂ := DY.ProtocolEvent.ExecEntryT ComposedEvent) rfl]

/-! ## 3. 2-Call Prefix (`[ev0, ev1]`) Unpacking -/

theorem unpack_explains_2
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry}
    {ev1 : RunEvent} {ptBytes outBytes ctBytes wireBytes macBytes msgBytes : HwBytes}
    (hf : compFitsPinned7003 setup7003 compI7003 r)
    (hev_party : ev1.party = "alice")
    (hev_cmd : ev1.cmd = .send peerAddrBob)
    (hev_inp : ev1.input = ptBytes)
    (hev_coins : ev1.coins = coins1Bytes)
    (hev_exit : ev1.exit = some (0, outBytes))
    (hwrap : runWrapped ev1 = true)
    (hout_wire : outBytes = preKeyWire none 7 9 1111 (ecKey (compPubOfIdx 0))
      (compPubOfIdx 3) kyberCt0Bytes msgBytes)
    (hmsg_len : msgBytes.length = 159)
    (hmsg_split : msgBytes = wireBytes ++ macBytes)
    (hmac_len : macBytes.length = 8)
    (hmac_eq : (hmacWith F7 macKey1Bytes
      (ecKey (compPubOfIdx 0) ++ ecKey (compPubOfIdx 1) ++ wireBytes)).take 8 = macBytes)
    (hmac_untag : (hmacWith F7 macKey1Bytes
      (ecKey (compPubOfIdx 0) ++ ecKey (compPubOfIdx 1) ++ wireBytes)).take 4 ≠ compTag4)
    (haes_eq : compAesPerm encKey1Bytes iv1Bytes ptBytes = ctBytes)
    (htr_wire : trWireBytes addr1Bytes canonicalVariation
      (WireFields.ofBytes [4#8] (compPubOfIdx 4) [0, 0, 0, 0] [0, 0, 0, 0] ctBytes)
      pqMsg1Bytes = wireBytes)
    (hex : Explains compI7003 r S g ss vis [.run ev0, .run ev1]) :
    bobDoneBaseKeys (runTrace r ss) = [] ∧ ∃ cl₁, SemPinned2 S cl₁ := by
  obtain ⟨hgs, hgwf, ⟨_, _, hswf, _⟩, hm⟩ := hex
  obtain ⟨pre₀, s₀, ss₁, v₀, vs₁, rfl, rfl, hinv₀, hrm₀, hm₁⟩ :=
    matchesEventsAt_run_exit0_inv (rfl : ev0.exit = some (0, out0Raw)) hm
  obtain ⟨hgwf₀, hgwf_rest₁⟩ := ghostWF_append hgwf
  obtain ⟨_, _hs₀_pre, _hs₀_lok, hswf₁⟩ := (stepsWF_append pre₀ (s₀ :: ss₁) (setupTrace r)).mp hswf
  obtain ⟨spkPk, pqPk, hnext₀, hpin₀⟩ := pin_step0_init hf hgs hgwf₀ hinv₀ hrm₀
  obtain ⟨pre₁, s₁, ss₂, v₁, vs₂, rfl, rfl, hinv₁, hrm₁, hm₂⟩ :=
    matchesEventsAt_run_exit0_inv hev_exit hm₁
  obtain ⟨hgwf₁, _⟩ := ghostWF_append hgwf_rest₁
  rw [hnext₀] at hswf₁ hrm₁ hm₂
  obtain ⟨_, _hs₁_pre, hs₁_lok, _⟩ := (stepsWF_append pre₁ (s₁ :: ss₂) _).mp hswf₁
  have htr₀_trNone : ∀ i, ((runSteps pre₀ (setupTrace r)).at? i :
      Option (DY.PersistentGlobalState.State.ExecEntryT
        (DY.PersistentLocalState.LocalState TRState))) = none := by
    intro i; rw [runSteps_invisible_at?_trState hinv₀, setupTrace_eq_7003 hf, setupTr4_trState_none]
  obtain ⟨cl₁, hsem₂, hnext₁⟩ := pin_step1_encrypt hf hpin₀ htr₀_trNone
    (fun i => by rw [runSteps_invisible_at?_nonNet (fun _ => rfl) hinv₀, setupTrace_eq_7003 hf, setupTr4_compEvent_none])
    hgwf₁ hinv₁ hs₁_lok hev_party hev_cmd hev_inp hev_coins hev_exit hwrap hout_wire
    hmsg_len hmsg_split hmac_len hmac_eq hmac_untag haes_eq htr_wire hrm₁
  cases hm₂ with
  | nil hinv₂ =>
    refine ⟨?_, cl₁, hsem₂⟩
    unfold runTrace
    have hrun_split : ∀ (a b : List Step) (t : ExecTrace), runSteps (a ++ b) t = runSteps b (runSteps a t) := by
      intro a b t; induction a generalizing t with
      | nil => rfl
      | cons x xs ih => exact ih (x.next t)
    rw [hrun_split pre₀, runSteps, hnext₀, hrun_split pre₁, runSteps, hnext₁,
        runSteps_invisible_bobDoneBaseKeys hinv₂, encTrCl_bobDone_eq,
        runSteps_invisible_bobDoneBaseKeys hinv₁, aliceTr_bobDone_eq,
        runSteps_invisible_bobDoneBaseKeys hinv₀, setupTrace_eq_7003 hf, setupTr4_bobDone_nil]

theorem bobDone_nil_of_explains_m1_2
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry}
    (hf : compFitsPinned7003 setup7003 compI7003 r)
    (hex : Explains compI7003 r S g ss vis [.run ev0, .run ev1_m1]) :
    bobDoneBaseKeys (runTrace r ss) = [] := by
  have hsplit : msg1M1Bytes = wire1M1Bytes ++ mac1M1Bytes := by decide +kernel
  have hwrap : runWrapped ev1_m1 = true := by
    dsimp only [runWrapped, ev1_m1]; rw [out1M1Raw_eq]; decide +kernel
  exact (unpack_explains_2 hf rfl rfl pt1M1Raw_eq coins1Raw_eq (congrArg (some ∘ Prod.mk 0) out1M1Raw_eq)
    hwrap out1M1_preKeyWire_eq (by decide) hsplit (by decide)
    (pqxdh_and_mac_facts_7003.2.2.2.2.1 ▸ pqxdh_and_mac_facts_7003.2.2.2.2.2.1)
    (pqxdh_and_mac_facts_7003.2.2.2.2.1 ▸ pqxdh_and_mac_facts_7003.2.2.2.2.2.2.1)
    ratchet_b_and_aes_facts_7003.2.2.2.2.2.2.2.2.2.2.2.1
    trWireBytes_m1_eq hex).1

theorem semPinned2_of_explains_m1_2
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry}
    (hf : compFitsPinned7003 setup7003 compI7003 r)
    (hex : Explains compI7003 r S g ss vis [.run ev0, .run ev1_m1]) :
    ∃ cl₁, SemPinned2 S cl₁ := by
  have hsplit : msg1M1Bytes = wire1M1Bytes ++ mac1M1Bytes := by decide +kernel
  have hwrap : runWrapped ev1_m1 = true := by
    dsimp only [runWrapped, ev1_m1]; rw [out1M1Raw_eq]; decide +kernel
  exact (unpack_explains_2 hf rfl rfl pt1M1Raw_eq coins1Raw_eq (congrArg (some ∘ Prod.mk 0) out1M1Raw_eq)
    hwrap out1M1_preKeyWire_eq (by decide) hsplit (by decide)
    (pqxdh_and_mac_facts_7003.2.2.2.2.1 ▸ pqxdh_and_mac_facts_7003.2.2.2.2.2.1)
    (pqxdh_and_mac_facts_7003.2.2.2.2.1 ▸ pqxdh_and_mac_facts_7003.2.2.2.2.2.2.1)
    ratchet_b_and_aes_facts_7003.2.2.2.2.2.2.2.2.2.2.2.1
    trWireBytes_m1_eq hex).2

theorem bobDone_nil_of_explains_m2_2
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry}
    (hf : compFitsPinned7003 setup7003 compI7003 r)
    (hex : Explains compI7003 r S g ss vis [.run ev0, .run ev1_m2]) :
    bobDoneBaseKeys (runTrace r ss) = [] := by
  have hsplit : msg1M2Bytes = wire1M2Bytes ++ mac1M2Bytes := by decide +kernel
  have hwrap : runWrapped ev1_m2 = true := by
    dsimp only [runWrapped, ev1_m2]; rw [out1M2Raw_eq]; decide +kernel
  exact (unpack_explains_2 hf rfl rfl pt1M2Raw_eq coins1Raw_eq (congrArg (some ∘ Prod.mk 0) out1M2Raw_eq)
    hwrap out1M2_preKeyWire_eq (by decide) hsplit (by decide)
    (pqxdh_and_mac_facts_7003.2.2.2.2.2.2.2.1 ▸ pqxdh_and_mac_facts_7003.2.2.2.2.2.2.2.2.1)
    (pqxdh_and_mac_facts_7003.2.2.2.2.2.2.2.1 ▸ pqxdh_and_mac_facts_7003.2.2.2.2.2.2.2.2.2.1)
    ratchet_b_and_aes_facts_7003.2.2.2.2.2.2.2.2.2.2.2.2.1
    trWireBytes_m2_1_eq hex).1

theorem semPinned2_of_explains_m2_2
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry}
    (hf : compFitsPinned7003 setup7003 compI7003 r)
    (hex : Explains compI7003 r S g ss vis [.run ev0, .run ev1_m2]) :
    ∃ cl₁, SemPinned2 S cl₁ := by
  have hsplit : msg1M2Bytes = wire1M2Bytes ++ mac1M2Bytes := by decide +kernel
  have hwrap : runWrapped ev1_m2 = true := by
    dsimp only [runWrapped, ev1_m2]; rw [out1M2Raw_eq]; decide +kernel
  exact (unpack_explains_2 hf rfl rfl pt1M2Raw_eq coins1Raw_eq (congrArg (some ∘ Prod.mk 0) out1M2Raw_eq)
    hwrap out1M2_preKeyWire_eq (by decide) hsplit (by decide)
    (pqxdh_and_mac_facts_7003.2.2.2.2.2.2.2.1 ▸ pqxdh_and_mac_facts_7003.2.2.2.2.2.2.2.2.1)
    (pqxdh_and_mac_facts_7003.2.2.2.2.2.2.2.1 ▸ pqxdh_and_mac_facts_7003.2.2.2.2.2.2.2.2.2.1)
    ratchet_b_and_aes_facts_7003.2.2.2.2.2.2.2.2.2.2.2.2.1
    trWireBytes_m2_1_eq hex).2

/-! ## 4. Step 2 (`ev2_m1` / `ev2_m2`, `bob recv` `bobStart`) Pinning -/

def bobTr0 (tr : ExecTrace) (ek ct : DY.Bytes) (keys : HandshakeKeys)
    (msg : TRSignalMsg) (seed pq m key : DY.Bytes) (st' stOut : TRState) (c : RecvChain) : ExecTrace :=
  let o := bobOut (randTerm 5 32) (randTerm 10 32) (randTerm 16 64)
    (DY.DiffieHellman.dhPk (randTerm 0 32)) ek ct keys
  let tr1 := (tr.append (RndE 32)).append (NetE key)
  let tr5 := (((tr1.append
      (EvP (.BobDone "bob" "alice" o.ikB o.ikA o.spk o.pqpk o.opk o.ek o.ct o.keys))).append
      (EvT (.DHRatchet "bob" st'.peer msg.ratchetKey (DY.DiffieHellman.dhPk st'.dhs)))).append
      (EvT (.HonestDH (st'.sessionInfo "bob") st'.dhs (st'.rIdx - 2)))).append
      (EvC (.HandshakeSession (st'.sessionInfo "bob") tr1.length))
  (((tr5.append (EvT (.Received "bob" st'.peer msg.ratchetKey 0 m))).append
    (EvT (.MessageKey (st'.sessionInfo "bob") .receiver seed pq 0 c.rIdx (tr5.length + 2)))).append
    (StT "bob" stOut))

structure BobPin2 (S : OpaqueSymbolSemantics) (g : Ghost) (tr₂ : ExecTrace)
    (ek₂ ct₂ : DY.Bytes) (keys₂ : HandshakeKeys) (msg₂ : TRSignalMsg)
    (seed₂ pq₂ m₂ key₂ : DY.Bytes) (st'₂ stB₁ : TRState) (c₂ c'₂ : RecvChain) : Prop where
  ek_eq : gamma compI7003 S g ek₂ = compPubOfIdx 3
  pqr_eq : gamma compI7003 S g keys₂.pqr = pqrBytes
  rk_eq : gamma compI7003 S g stB₁.rk = rk2Bytes
  cks_eq : gamma compI7003 S g stB₁.cks = cksB0Bytes
  dhs_pk_eq : gamma compI7003 S g (DY.DiffieHellman.dhPk stB₁.dhs) = compPubOfIdx 5
  myIk_eq : gamma compI7003 S g stB₁.myIk = ecKey (compPubOfIdx 1)
  peerIk_eq : gamma compI7003 S g stB₁.peerIk = ecKey (compPubOfIdx 0)
  peer_eq : stB₁.peer = "alice"
  ns_eq : stB₁.ns = 0
  pn_eq : stB₁.pn = 0
  recv_eq : stB₁.recv = [c'₂]
  c'_rk : c'₂.ratchetKey = msg₂.ratchetKey
  c'_rk_bytes : gamma compI7003 S g c'₂.ratchetKey = compPubOfIdx 4
  c'_idx : c'₂.index = 1
  spqr_eq : stB₁.spqr = recvSt (DY.Spqr.spqrInit keys₂.pqr spqrB2A) msg₂.pqRatchet
  spqr_bytes : gamma compI7003 S g stB₁.spqr = S.recvState (S.init pqrBytes [1#8]) pqMsg1Bytes
  sid_eq : stB₁.sessionInfo "bob" = st'₂.sessionInfo "bob"

private theorem checkPreKey7003_inv {w msg wire mac ct pq : HwBytes}
    (h : checkPreKey7003 w msg wire mac ct pq = true) :
    ∃ p, parsePreKeyWire w = some p ∧
      p.baseKey.take 33 = ecKey (compPubOfIdx 3) ∧
      p.kyberCiphertext = some (kyberKey kyberCt0Bytes) ∧
      msg.take (msg.length - 8) = wire ∧
      msg.drop (msg.length - 8) = mac ∧
      p.inner.senderRatchetKey.bytes.toList = compPubOfIdx 4 ∧
      p.inner.counter = 0 ∧
      p.inner.pqRatchet = pq := by
  unfold checkPreKey7003 at h
  cases hp : parsePreKeyWire w <;> rw [hp] at h
  · cases h
  · next p =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨p, rfl, h.1.1.1.1.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2,
      h.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.2,
      h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.2⟩

section KyberBobAux
unseal DY.Bytes

private theorem kyberSs_of_bobAgreement
    (S : OpaqueSymbolSemantics) (g : Ghost) {ct ss : DY.Bytes}
    (hdec : errToOption (DY.PQKem.kemDecap (randTerm 16 64) ct) = some ss)
    (hct : gamma compI7003 S g ct = kyberCt0Bytes) :
    gamma compI7003 S g ss = kyberSs0Bytes := by
  dsimp only [errToOption, DY.PQKem.kemDecap, DY.PQKem.CanPQKem.kemDecap] at hdec
  rcases hv1 : ct.view? DY.PQKem.Encap.SubF with _ | ⟨pk, ent⟩ <;> rw [hv1] at hdec
  · cases hdec
  · dsimp only at hdec
    rcases hv2 : pk.view? DY.PQKem.Pk.SubF with _ | ⟨sk'⟩ <;> rw [hv2] at hdec
    · cases hdec
    · dsimp only at hdec
      split at hdec
      · injection hdec with hss
        subst hss
        rcases pack_of_view_eq_some hv1 with rfl
        have hent_len : (gamma compI7003 S g ent).length = 32 := by
          by_contra hne
          have hct_nil : gamma compI7003 S g (({ pk, entropy := ent } : DY.PQKem.Encap.SubF DY.Bytes).pack) = [] := by
            unfold gamma gamma'
            rw [rec_eq_concretizeAll (concretizeKemEncap compI7003)]
            dsimp only [concretizeKemEncap]
            have hne' : ((ent.rec (concretizeAll compI7003 S g)).bytes).length ≠ 32 := hne
            simp [hne', opaqueNode]
          rw [hct_nil] at hct
          have h1568 : kyberCt0Bytes.length = 1568 := by decide
          rw [← hct] at h1568; cases h1568
        have h1 : gamma compI7003 S g (DY.PQKem.kemEncap pk ent).1 = kyberCt0Bytes := hct
        rw [gamma_kemEncap_fst_32 S g pk ent hent_len] at h1
        have he0 : (gamma compI7003 S g ent == compKyberE0) = true := by
          unfold compKyberEncaps at h1
          cases hbeq : (gamma compI7003 S g ent == compKyberE0)
          · rw [hbeq, if_neg' Bool.false_ne_true] at h1
            have hdef : (compDefaultKyberCt ++ compDefaultKyberSs).take 1568 ≠ kyberCt0Bytes := by
              decide +kernel
            exact absurd h1 hdef
          · rfl
        change gamma compI7003 S g (DY.PQKem.kemEncap pk ent).2 = kyberSs0Bytes
        rw [gamma_kemEncap_snd_32 S g pk ent hent_len]
        unfold compKyberEncaps
        simp only [he0, ↓reduceIte]
        decide +kernel
      · cases hdec

private theorem gamma_kemRejKey (S : OpaqueSymbolSemantics) (g : Ghost) (sk ct : DY.Bytes) :
    gamma compI7003 S g (DY.PQKem.kemRejKey sk ct) =
      S.kemDecap (gamma compI7003 S g (DY.PQKem.kemPk sk)) (gamma compI7003 S g ct) := by
  unfold gamma gamma'
  show ((({ sk, cipher := ct } : DY.PQKem.RejKey.SubF DY.Bytes).pack).rec
    (concretizeAll compI7003 S g)).bytes = _
  rw [rec_eq_concretizeAll (DY.Libsignal.Composed.Refinement.concretizeKemRej S)]
  dsimp only [DY.Libsignal.Composed.Refinement.concretizeKemRej, node]
  have hpk : S.kemPk (((sk.rec (concretizeAll compI7003 S g)).bytes)) =
      gamma compI7003 S g (DY.PQKem.kemPk sk) := by
    unfold gamma gamma'
    show _ = ((({ sk } : DY.PQKem.Pk.SubF DY.Bytes).pack).rec
      (concretizeAll compI7003 S g)).bytes
    rw [rec_eq_concretizeAll (concretizeKemPk S)]
    rfl
  rw [hpk]; rfl

end KyberBobAux

theorem pin_step2_bobStart
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {tr₂ : ExecTrace} {s₂ : Step} {v₂ : List VisEntry}
    {ev2 : RunEvent} {outBytes ptBytes msgBytes wireBytes macBytes ctBytes : HwBytes}
    (hf : compFitsPinned7003 setup7003 compI7003 r)
    (hgs : GhostAndSemMatchSetup compI7003 r S g)
    (hgwf : GhostWF g v₂)
    (htr₂_bobDone : bobDoneBaseKeys tr₂ = [])
    (htr₂_pqState : ∀ i, (tr₂.at? i :
      Option (DY.PersistentGlobalState.State.ExecEntryT
        (DY.PersistentLocalState.LocalState PQXDHState))) =
      (b1_setupTr4 "alice" "bob").at? i)
    (htr₂_regA : ∀ i ik vk hon,
      (tr₂.at? i : Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) =
        some (EvP (.IdentityRegistered "alice" ik vk hon)) →
      ik = DY.DiffieHellman.dhPk (randTerm 0 32))
    (hev_party : ev2.party = "bob")
    (hev_cmd : ev2.cmd = .recv peerAddrAlice)
    (hev_inp : ev2.input = outBytes)
    (hev_coins : ev2.coins = coins2Bytes)
    (hev_exit : ev2.exit = some (0, ptBytes))
    (hchk : checkPreKey7003 outBytes msgBytes wireBytes macBytes ctBytes pqMsg1Bytes = true)
    (hrm₂ : RunMatches compI7003 r S g tr₂ s₂ ev2 v₂ (some (bundlePreKeyIds bun0Raw))) :
    ∃ ek₂ ct₂ keys₂ msg₂ seed₂ pq₂ m₂ key₂ st'₂ stB₁ c₂ c'₂,
      s₂.next tr₂ = bobTr0 tr₂ ek₂ ct₂ keys₂ msg₂ seed₂ pq₂ m₂ key₂ st'₂ stB₁ c₂ ∧
      BobPin2 S g tr₂ ek₂ ct₂ keys₂ msg₂ seed₂ pq₂ m₂ key₂ st'₂ stB₁ c₂ c'₂ := by
  obtain ⟨ha_id, _, _, _⟩ := setup_ids_7003 hf
  obtain ⟨p, hp_parse, hp_ek, hp_ct, hmsg_w, hmsg_m, hp_rk, hp_cnt, hp_pq⟩ := checkPreKey7003_inv hchk
  obtain ⟨hcls, hparty, hfits, hpeer, hok, _, hv_eq, inp, drs, outs, hv_split,
    hinp, hdrs, houts, hrf, hpf⟩ := hrm₂
  have hpf_p := hpf p (hev_inp ▸ hp_parse)
  rw [htr₂_bobDone] at hpf_p
  cases s₂ <;> try (simp [Step.FitsCmd, hev_cmd] at hfits)
  case messageDecrypt => simp at hpf_p
  case messageDecryptSkipped => simp at hpf_p
  case bobStart b a kh regA mh pqH spqrIdx =>
    have hb : b = "bob" := by rw [hev_party] at hparty; exact Option.some.inj hparty
    subst hb
    dsimp only [Step.MatchesSetupPeer] at hpeer
    rw [ha_id] at hpeer; subst hpeer
    have hok' : ((DY.Libsignal.Composed.bobStart "bob" "alice" kh regA mh pqH spqrIdx).run tr₂).1.isSome = true := by
      dsimp only [Step.ok, Step.toInput] at hok
      erw [stepIn_ok] at hok; exact hok
    obtain ⟨_, hrun⟩ := isSome_iff_exists.mp hok'
    simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline] at hrun
    obtain ⟨o_hs, tr_hs, hhs, htr_hs, hr1, _⟩ := bind_some_inv hrun
    have hhs_orig := hhs
    -- Invert bobHandshake
    unfold DY.Libsignal.PQXDH.bobHandshake at hhs
    obtain ⟨ikB, _, hik, htr_ik, hh1, _⟩ := bind_some_inv hhs
    obtain ⟨hat_ik, htr_ik'⟩ := getKey_some_inv hik; rw [htr_ik'] at htr_ik; subst htr_ik
    obtain ⟨spkSk, _, hspk, htr_spk, hh2, _⟩ := bind_some_inv hh1
    obtain ⟨hat_spk, htr_spk'⟩ := getKey_some_inv hspk; rw [htr_spk'] at htr_spk; subst htr_spk
    obtain ⟨pqsk, _, hpqk, htr_pqk, hh3, _⟩ := bind_some_inv hh2
    obtain ⟨hat_pqk, htr_pqk'⟩ := getKey_some_inv hpqk; rw [htr_pqk'] at htr_pqk; subst htr_pqk
    have hopk_none : kh.opk = none := by
      cases hopk : kh.opk with
      | none => rfl
      | some oi =>
        rw [hopk] at hh3; dsimp only at hh3
        obtain ⟨_, _, hopk_g, _, _, _⟩ := bind_some_inv hh3
        obtain ⟨hat_opk, _⟩ := getKey_some_inv hopk_g
        rw [htr₂_pqState, setupTr4_pqxdhState_eq] at hat_opk
        split at hat_opk <;> try (split at hat_opk <;> try (split at hat_opk <;> try (split at hat_opk)))
        all_goals simp [StP] at hat_opk
    rw [hopk_none] at hh3; dsimp only at hh3
    obtain ⟨opkSk, tr_opk, hopk_p, htr_opk, hh4, _⟩ := bind_some_inv hh3
    rw [Traceful.run_pure] at hopk_p htr_opk; injection hopk_p with hopk_p; subst opkSk; subst tr_opk
    obtain ⟨⟨ikAPk, vkA⟩, tr_reg, hreg, htr_reg, hh5, _⟩ := bind_some_inv hh4
    obtain ⟨honA, hat_reg, htr_reg'⟩ := lookupIdentity_some_inv hreg; rw [htr_reg'] at htr_reg; subst tr_reg
    obtain ⟨ek₂, tr_ek, hek, htr_ek, hh6, _⟩ := bind_some_inv hh5
    obtain ⟨hat_ek, htr_ek'⟩ := receiveMessage_some_inv hek; rw [htr_ek'] at htr_ek; subst tr_ek
    obtain ⟨ct₂, tr_ct, hct, htr_ct, hh7, _⟩ := bind_some_inv hh6
    obtain ⟨hat_ct, htr_ct'⟩ := receiveMessage_some_inv hct; rw [htr_ct'] at htr_ct; subst tr_ct
    obtain ⟨_, tr_can, hgd_can, htr_can, hh8, _⟩ := bind_some_inv hh7
    have hcan : isCanonicalKey ek₂ = true := guard_some_inv hgd_can
    rw [_root_.guard, if_pos' hcan, Traceful.run_pure] at htr_can; subst tr_can
    dsimp only at hh8
    rcases hagree : bobAgreement ikB spkSk pqsk none ikAPk ek₂ ct₂ with _ | keys₂ <;> rw [hagree] at hh8
    · simp [Traceful.run_failure] at hh8
    · dsimp only at hh8
      have hikB_eq : ikB = randTerm 5 32 := by
        have h := hat_ik; rw [htr₂_pqState, setupTr4_pqxdhState_eq] at h
        split at h <;> try (split at h <;> try (split at h <;> try (split at h)))
        all_goals simp [StP] at h
        exact h.symm
      subst hikB_eq
      have hspk_eq : spkSk = randTerm 10 32 := by
        have h := hat_spk; rw [htr₂_pqState, setupTr4_pqxdhState_eq] at h
        split at h <;> try (split at h <;> try (split at h <;> try (split at h)))
        all_goals simp [StP] at h
        exact h.symm
      subst hspk_eq
      have hpqsk_eq : pqsk = randTerm 16 64 := by
        have h := hat_pqk; rw [htr₂_pqState, setupTr4_pqxdhState_eq] at h
        split at h <;> try (split at h <;> try (split at h <;> try (split at h)))
        all_goals simp [StP] at h
        exact h.symm
      subst hpqsk_eq
      have hikA_eq : ikAPk = DY.DiffieHellman.dhPk (randTerm 0 32) := htr₂_regA _ _ _ _ hat_reg
      subst hikA_eq
      have hh_runs := Runs.bobHandshake hat_ik hat_spk hat_pqk hopk_none hat_reg hat_ek hat_ct hcan hagree
      have ho_eq : o_hs = bobOut (randTerm 5 32) (randTerm 10 32) (randTerm 16 64)
          (DY.DiffieHellman.dhPk (randTerm 0 32)) ek₂ ct₂ keys₂ :=
        Option.some.inj (hhs_orig.symm.trans hh_runs.1)
      have htr_hs_eq : tr_hs = tr₂ := htr_hs.symm.trans hh_runs.2
      rw [ho_eq, htr_hs_eq] at hr1
      -- Invert the ratchet & decrypt body of bobStart
      obtain ⟨msg₂, tr_m, hmsg_r, htr_m, hr2, _⟩ := bind_some_inv hr1
      obtain ⟨t₂, hat_msg, hparse₂, hver₂, htr_m'⟩ := receiveSignalMsg_some_inv hmsg_r
      rw [htr_m'] at htr_m; subst tr_m
      set st0 := bobSt0 "alice" (randTerm 5 32) (randTerm 10 32)
        (DY.DiffieHellman.dhPk (randTerm 0 32)) keys₂ msg₂
      obtain ⟨⟨st'₂, c₂, rat₂⟩, tr_erc, herc, htr_erc, hr3, _⟩ := bind_some_inv hr2
      have hlow₂ : DY.Libsignal.TripleRatchet.x25519LowOrder msg₂.ratchetKey = false := by
        cases hlo : DY.Libsignal.TripleRatchet.x25519LowOrder msg₂.ratchetKey
        · rfl
        · rw [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor] at herc
          unfold recvChainFor findRecvChain at herc
          dsimp only [List.find?] at herc
          rw [hlo] at herc
          simp [Traceful.run_failure] at herc
      have herc_runs := Runs.ensureReceiverChain_ratchet (tr := tr₂) (st := st0) (pk := msg₂.ratchetKey) rfl hlow₂
      have herc_pair := Option.some.inj (herc.symm.trans herc_runs.1)
      have hrs₂ : ratchetState st0 msg₂.ratchetKey (rnd tr₂.length 32) = (st'₂, c₂) := by
        rcases hpair : ratchetState st0 msg₂.ratchetKey (rnd tr₂.length 32) with ⟨s_a, c_a⟩
        rw [hpair] at herc_pair
        injection herc_pair with h1 h2
        injection h2 with h2' _
        subst h1; subst h2'; rfl
      have htr_erc' : tr_erc = tr₂.append (RndE 32) := htr_erc.symm.trans herc_runs.2
      subst htr_erc'
      dsimp only at hr3
      rcases hcons₂ : consumeMessageKey c₂ msg₂.counter with _ | ⟨seed₂, c'₂⟩ <;> rw [hcons₂] at hr3
      · simp [Traceful.run_failure] at hr3
      · dsimp only at hr3
        rcases hrecv₂ : DY.Spqr.spqrRecv st'₂.spqr msg₂.pqRatchet spqrIdx with _ | ⟨spqr'₂, key₂⟩ <;>
          rw [hrecv₂] at hr3
        · simp [Traceful.run_failure] at hr3
        · dsimp only at hr3
          obtain ⟨_, tr_k2, _, htr_k2, hr4, _⟩ := bind_some_inv hr3
          rw [(Runs.sendMessage _ _).2] at htr_k2; subst htr_k2
          obtain ⟨pq₂, _, hrpq₂, htr_pq2, hr5, _⟩ := bind_some_inv hr4
          obtain ⟨hat_pq₂, htr_pq2'⟩ := receiveMessage_some_inv hrpq₂
          rw [htr_pq2'] at htr_pq2; subst htr_pq2
          obtain ⟨m₂, _, hvmd, _, _, _⟩ := bind_some_inv hr5
          unfold DY.Libsignal.TripleRatchet.verifyMacAndDecrypt at hvmd
          obtain ⟨_, _, hgd_mac, htr_mac, hdec_r, _⟩ := bind_some_inv hvmd
          have hmac₂ : msg₂.mac = computeMac (trMsgKeys pq₂ seed₂).macKey st'₂.peerIk st'₂.myIk msg₂.wire :=
            guard_some_inv hgd_mac
          rw [_root_.guard, if_pos' hmac₂, Traceful.run_pure] at htr_mac; subst htr_mac
          have hdec₂ : DY.SymEnc.symDec (trMsgKeys pq₂ seed₂).cipherKey (trMsgKeys pq₂ seed₂).iv msg₂.ciphertext =
              some m₂ := by
            rcases hd : DY.SymEnc.symDec (trMsgKeys pq₂ seed₂).cipherKey (trMsgKeys pq₂ seed₂).iv msg₂.ciphertext with _ | x <;>
              rw [hd] at hdec_r
            · simp [MonadLift.monadLift, MonadLiftT.monadLift, errToOption] at hdec_r
            · simp [MonadLift.monadLift, MonadLiftT.monadLift, errToOption] at hdec_r
              exact congrArg some hdec_r
          set stB₁ : TRState := { st'₂ with recv := setRecvChain st'₂.recv c'₂, spqr := spqr'₂ }
          have hruns₂ := Runs.bobStart hat_ik hat_spk hat_pqk hopk_none hat_reg hat_ek hat_ct hcan hagree
            hat_msg hparse₂ hver₂ hlow₂ hrs₂ hcons₂ hrecv₂ hat_pq₂ hmac₂ hdec₂ (stOut := stB₁) rfl
          -- Unpack stepView of s₂ to get ReadsFaithfully and DrawsMatch
          have hbobOpk : bobOpkPk "bob" kh tr₂ = none := by simp [bobOpkPk, hopk_none]
          have hrec_terms : received tr₂ [mh.ek, mh.ct, mh.msg] = [ek₂, ct₂, t₂] := by
            simp only [received, List.filterMap,
              getMessageSentAt_of_at?_net hat_ek,
              getMessageSentAt_of_at?_net hat_ct,
              getMessageSentAt_of_at?_net hat_msg]
          dsimp only [stepView] at hv_eq
          rw [ite_eq_left_iff.mpr (fun h => absurd hok h), hbobOpk] at hv_eq
          dsimp only [bobVis, Option.toList] at hv_eq
          rw [List.append_nil, hrec_terms, List.cons_append, List.cons_append] at hv_eq
          have hinp_eq : inp = ⟨.recv, [ek₂, ct₂, t₂], .preKeyRecv, none⟩ :=
            (List.cons.inj (hv_split.symm.trans hv_eq)).1
          subst hinp_eq
          rw [hev_inp] at hrf
          dsimp only [ReadsFaithfully] at hrf
          obtain ⟨_, _, _, hp_rm, p', hp'_parse, hfi⟩ := hrf
          have hp_eq : p' = p := Option.some.inj (hp'_parse.symm.trans hp_parse)
          subst p'
          dsimp only [PreKeyRecvMatches] at hp_rm
          obtain ⟨p'', hp''_parse, hp_ek', hp_ct', hp_msg', _⟩ := hp_rm
          have hp''_eq : p'' = p := Option.some.inj (hp''_parse.symm.trans hp_parse)
          subst p''
          have hg_ek₂ : gamma compI7003 S g ek₂ = compPubOfIdx 3 :=
            ecKey_inj (hp_ek'.symm.trans hp_ek)
          have hg_ct₂ : gamma compI7003 S g ct₂ = kyberCt0Bytes := by
            have h1 := Option.some.inj (hp_ct'.symm.trans hp_ct)
            exact kyberKey_inj h1
          obtain ⟨msg₂', hparse₂', hfi_w, hfi_m, _, hfi_ct, hfi_rk, hfi_pq, hfi_cnt, _⟩ := hfi
          have hmsg₂_eq : msg₂' = msg₂ := Option.some.inj (hparse₂'.symm.trans hparse₂)
          subst msg₂'
          have hcnt₀ : msg₂.counter = 0 := by
            rw [hp_cnt] at hfi_cnt
            exact UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hfi_cnt)
          have hc₂_def : c₂ =
              { ratchetKey := msg₂.ratchetKey
                chainKey := (createChain keys₂.rk msg₂.ratchetKey (randTerm 10 32)).2
                index := 0
                rIdx := 2 } := by
            have h2 := Prod.mk.inj hrs₂.symm
            exact h2.2
          have hc₂_idx : c₂.index = 0 := by rw [hc₂_def]
          have hskip_eq : ∀ t s pk child, skipTr t s pk c₂ child msg₂.counter = t := by
            intro t s pk child
            unfold skipTr
            rw [hcnt₀, hc₂_idx]
            simp [DY.Libsignal.TripleRatchet.logSkippedKeys, Traceful.run_pure]
          have hnext₂ : (Step.bobStart "bob" "alice" kh regA mh pqH spqrIdx).next tr₂ =
              bobTr0 tr₂ ek₂ ct₂ keys₂ msg₂ seed₂ pq₂ m₂ key₂ st'₂ stB₁ c₂ := by
            dsimp only [Step.next, Step.toInput]
            erw [stepIn_next, hruns₂.2]
            dsimp only [bobTr0]
            rw [hskip_eq, hcnt₀, hc₂_idx]
            rfl
          -- Compute exposures, newRandoms, receivedPlaintext on bobTr0
          set tr₃_b := bobTr0 tr₂ ek₂ ct₂ keys₂ msg₂ seed₂ pq₂ m₂ key₂ st'₂ stB₁ c₂
          have hlen_b : tr₃_b.length = tr₂.length + 9 := by
            simp only [tr₃_b, bobTr0, length_append_eq, Nat.add_assoc]
          have hexp₂ : exposures tr₂ tr₃_b = [] := by
            unfold exposures newIndices
            rw [hlen_b, Nat.add_sub_cancel_left]
            have hpq_nil : (List.range' tr₂.length 9).filterMap (pqExposureAt tr₃_b) = [] := by
              rw [List.filterMap_eq_nil_iff]; intro j hj; rw [List.mem_range'_1] at hj
              unfold pqExposureAt; rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
              dsimp only [tr₃_b, bobTr0]
              repeat first
                | rw [at?_append_other_eq rfl]
                | rw [at?_append_same_eq (fun _ => rfl)]
              simp only [length_append_eq, Nat.add_assoc]
              by_cases hj2 : j = tr₂.length + 2
              · subst hj2; simp
              · rw [if_neg' hj2, at?_ge_length_eq tr₂ (by omega)]
            have htr_nil : (List.range' tr₂.length 9).filterMap (trExposureAt tr₃_b) = [] := by
              rw [List.filterMap_eq_nil_iff]; intro j hj; rw [List.mem_range'_1] at hj
              unfold trExposureAt; rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
              dsimp only [tr₃_b, bobTr0]
              repeat first
                | rw [at?_append_other_eq rfl]
                | rw [at?_append_same_eq (fun _ => rfl)]
              simp only [length_append_eq, Nat.add_assoc]
              by_cases hj7 : j = tr₂.length + 7
              · subst hj7; simp
              · by_cases hj6 : j = tr₂.length + 6
                · subst hj6; simp
                · by_cases hj4 : j = tr₂.length + 4
                  · subst hj4; simp
                  · by_cases hj3 : j = tr₂.length + 3
                    · subst hj3; simp
                    · rw [if_neg' hj7, if_neg' hj6, if_neg' hj4, if_neg' hj3, at?_ge_length_eq tr₂ (by omega)]
            rw [hpq_nil, htr_nil]; rfl
          have hnr₂ : newRandoms tr₂ tr₃_b = [(randTerm tr₂.length 32, 32)] := by
            unfold newRandoms newIndices
            rw [hlen_b, Nat.add_sub_cancel_left]
            have hat_r : ∀ k : Nat, k < 9 →
                (tr₃_b.at? (tr₂.length + k) : Option DY.Random.ExecEntryT) =
                if k = 0 then some (RndE 32) else none := by
              intro k hk
              dsimp only [tr₃_b, bobTr0]
              repeat first
                | rw [at?_append_other_eq rfl]
                | rw [at?_append_same_eq (fun _ => rfl)]
              by_cases hk0 : k = 0
              · subst hk0; simp [Nat.add_zero]
              · have hne0 : tr₂.length + k ≠ tr₂.length := by omega
                rw [if_neg' hk0, if_neg' hne0, at?_ge_length_eq tr₂ (by omega)]
            have hrange : List.range' tr₂.length 9 =
                [tr₂.length + 0, tr₂.length + 1, tr₂.length + 2, tr₂.length + 3, tr₂.length + 4,
                 tr₂.length + 5, tr₂.length + 6, tr₂.length + 7, tr₂.length + 8] := by
              simp [List.range', Nat.add_assoc]
            rw [hrange]; dsimp only [List.filterMap]
            rw [hat_r 0 (by decide), hat_r 1 (by decide), hat_r 2 (by decide),
                hat_r 3 (by decide), hat_r 4 (by decide), hat_r 5 (by decide),
                hat_r 6 (by decide), hat_r 7 (by decide), hat_r 8 (by decide)]
            simp [Option.map, RndE, Nat.add_zero]
          have hrpt₂ : receivedPlaintext tr₂ tr₃_b = some m₂ := by
            unfold receivedPlaintext newIndices
            rw [hlen_b, Nat.add_sub_cancel_left]
            have hat_ev : ∀ k : Nat, k < 7 →
                (tr₃_b.getEventAt TREvent (tr₂.length + k)) =
                if k = 3 then some (.DHRatchet "bob" st'₂.peer msg₂.ratchetKey (DY.DiffieHellman.dhPk st'₂.dhs))
                else if k = 4 then some (.HonestDH (st'₂.sessionInfo "bob") st'₂.dhs (st'₂.rIdx - 2))
                else if k = 6 then some (.Received "bob" st'₂.peer msg₂.ratchetKey 0 m₂)
                else none := by
              intro k hk
              rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
              dsimp only [tr₃_b, bobTr0]
              repeat first
                | rw [at?_append_other_eq (E₂ := DY.ProtocolEvent.ExecEntryT TREvent) rfl]
                | rw [at?_append_same_eq (fun _ => rfl)]
              simp only [length_append_eq, Nat.add_assoc]
              have hne7 : tr₂.length + k ≠ tr₂.length + 7 := by omega
              rw [if_neg' hne7]
              by_cases hk6 : k = 6
              · subst hk6; simp
              · have hne6 : tr₂.length + k ≠ tr₂.length + 6 := by omega
                rw [if_neg' hk6, if_neg' hne6]
                by_cases hk4 : k = 4
                · subst hk4; simp [show tr₂.length + 4 ≠ tr₂.length + 3 by omega]
                · have hne4 : tr₂.length + k ≠ tr₂.length + 4 := by omega
                  rw [if_neg' hk4, if_neg' hne4]
                  by_cases hk3 : k = 3
                  · subst hk3; simp
                  · have hne3 : tr₂.length + k ≠ tr₂.length + 3 := by omega
                    rw [if_neg' hk3, if_neg' hne3, at?_ge_length_eq tr₂ (by omega)]
            have hrange : List.range' tr₂.length 9 =
                [tr₂.length + 0, tr₂.length + 1, tr₂.length + 2, tr₂.length + 3, tr₂.length + 4,
                 tr₂.length + 5, tr₂.length + 6, tr₂.length + 7, tr₂.length + 8] := by
              simp [List.range', Nat.add_assoc]
            rw [hrange]; dsimp only [List.findSome?]
            rw [hat_ev 0 (by decide), hat_ev 1 (by decide), hat_ev 2 (by decide),
                hat_ev 3 (by decide), hat_ev 4 (by decide), hat_ev 5 (by decide), hat_ev 6 (by decide)]
            rfl
          rw [hnext₂, hexp₂, List.append_nil, hnr₂, hrpt₂] at hv_eq
          dsimp only [List.map, Option.map, Option.toList] at hv_eq
          have houts_one : ∃ vo, outs = [vo] := by
            unfold OutputsMatch at houts
            rw [hev_exit, hev_cmd] at houts
            obtain ⟨vo, rfl, _⟩ := houts
            exact ⟨vo, rfl⟩
          obtain ⟨vo, rfl⟩ := houts_one
          have h1 := (List.cons.inj (hv_split.symm.trans hv_eq)).2
          have hdrs_eq : drs = [rngEntry (randTerm tr₂.length 32)] := by
            rcases drs with _ | ⟨d0, _ | ⟨d1, drs⟩⟩ <;> simp at h1
            exact congrArg (· :: []) h1.1
          rw [hdrs_eq, hev_coins] at hdrs
          have hdm_c2 := drawsMatch_nil_or_single (r := r) (S := S) (g := g)
            (ts := tr₂.length) (cl := 32) (coins := coins2Bytes)
            (fun v hv _ => by
              subst hv
              refine hgwf.1 (rngEntry (randTerm tr₂.length 32)) ?_ rfl tr₂.length 32 (by decide)
                (by simp [rngEntry])
              rw [hv_eq]; simp)
            (by simpa using hdrs)
          have hg_dhsB : gamma compI7003 S g (randTerm tr₂.length 32) = coins2Bytes := by
            rw [hdm_c2.2]; decide +kernel
          -- Evaluate Bob's handshake keys & ratchet state under γ
          obtain ⟨hg_s0, hg_s5, hg_s10, _, hg_pk0, hg_pk5, hg_pk10, hg_kpk, hkd⟩ :=
            gamma_setup_keys_7003 hf hgs
          unfold bobAgreement at hagree
          dsimp only [Bind.bind, Option.bind, Pure.pure] at hagree
          injection hagree with hkeys₂_eq
          let ss₂ := (errToOption (DY.PQKem.kemDecap (randTerm 16 64) ct₂)).getD
            (DY.PQKem.kemRejKey (randTerm 16 64) ct₂)
          have hg_ss₂ : gamma compI7003 S g ss₂ = kyberSs0Bytes := by
            dsimp only [ss₂]
            rcases hdec_k : errToOption (DY.PQKem.kemDecap (randTerm 16 64) ct₂) with _ | ss_ok
            · dsimp only [Option.getD]
              rw [gamma_kemRejKey, hg_kpk, hg_ct₂, hkd]
            · exact kyberSs_of_bobAgreement S g hdec_k hg_ct₂
          have hdh1 : gamma compI7003 S g (agree (DY.DiffieHellman.dhPk (randTerm 0 32)) (randTerm 10 32)) =
              compDhByIdx 2 0 := by
            rw [gamma_agree, hg_s10, hg_pk0, compLookupDh_secret_pub coins_secret_indices.2.2.2.2.2.2.1]
          have hdh2 : gamma compI7003 S g (agree ek₂ (randTerm 5 32)) = compDhByIdx 1 3 := by
            rw [gamma_agree, hg_s5, hg_ek₂, compLookupDh_secret_pub coins_secret_indices.2.2.2.2.2.1]
          have hdh3 : gamma compI7003 S g (agree ek₂ (randTerm 10 32)) = compDhByIdx 2 3 := by
            rw [gamma_agree, hg_s10, hg_ek₂, compLookupDh_secret_pub coins_secret_indices.2.2.2.2.2.2.1]
          have hg_ikm₂ : gamma compI7003 S g
              (DY.Libsignal.PQXDH.pqxdhIkm
                (agree (DY.DiffieHellman.dhPk (randTerm 0 32)) (randTerm 10 32))
                (agree ek₂ (randTerm 5 32))
                (agree ek₂ (randTerm 10 32)) none ss₂) =
              List.replicate 32 0xff#8 ++ compDhByIdx 2 0 ++ compDhByIdx 1 3 ++ compDhByIdx 2 3 ++
                kyberSs0Bytes := by
            unfold DY.Libsignal.PQXDH.pqxdhIkm DY.Libsignal.PQXDH.discontinuity
            simp only [gamma_concat, gamma_literalToBytes, hdh1, hdh2, hdh3, hg_ss₂, List.append_assoc]
            have hdisc : ofByteArray (ByteArray.mk (Array.replicate 32 0xFF)) = List.replicate 32 0xff#8 := by decide
            rw [hdisc]
          obtain ⟨hg_rk0, _, hg_pqr⟩ :
              gamma compI7003 S g keys₂.rk = rk0Bytes ∧
              gamma compI7003 S g keys₂.ck = ck0Bytes ∧
              gamma compI7003 S g keys₂.pqr = pqrBytes := by
            rw [← hkeys₂_eq]
            exact gamma_pqxdhKdf_eq S g _ hg_ikm₂
              pqxdh_and_mac_facts_7003.1
              pqxdh_and_mac_facts_7003.2.1
              pqxdh_and_mac_facts_7003.2.2.1
              pqxdh_and_mac_facts_7003.2.2.2.1
          -- Evaluate ratchetState st0 msg₂.ratchetKey (rnd tr₂.length 32)
          have hg_rk_msg : gamma compI7003 S g msg₂.ratchetKey = compPubOfIdx 4 :=
            hfi_rk.trans hp_rk
          have hg_dhB1 : gamma compI7003 S g (agree msg₂.ratchetKey (randTerm 10 32)) = compDhByIdx 2 4 := by
            rw [gamma_agree, hg_s10, hg_rk_msg, compLookupDh_secret_pub coins_secret_indices.2.2.2.2.2.2.1]
          have hg_prkA1 : gamma compI7003 S g
              (DY.Libsignal.TripleRatchet.hmac keys₂.rk (agree msg₂.ratchetKey (randTerm 10 32))) =
              prkA1Bytes := by
            unfold DY.Libsignal.TripleRatchet.hmac
            rw [gamma_kdfExtract, hg_rk0, hg_dhB1]
            exact ratchet_a_facts_7003.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          have hg_rk1B : gamma compI7003 S g (createChain keys₂.rk msg₂.ratchetKey (randTerm 10 32)).1 =
              rk1Bytes := by
            show gamma compI7003 S g (DY.KdfExtract.kdfExtract
              (DY.Libsignal.TripleRatchet.hmac keys₂.rk (agree msg₂.ratchetKey (randTerm 10 32)))
              (DY.Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperRatchet")
                (DY.Literal.literalToBytes (ByteArray.mk #[1])))) = rk1Bytes
            unfold DY.Libsignal.TripleRatchet.lit
            rw [gamma_kdfExtract, hg_prkA1, gamma_concat, gamma_literalToBytes, gamma_literalToBytes,
                ofByteArray_info_labels.2.1]
            have hb1 : ofByteArray (ByteArray.mk #[1]) = [0x01#8] := by decide
            rw [hb1]; exact ratchet_a_facts_7003.2.2.2.2.2.2.2.2.2.2.1
          have h_rnd_eq : rnd tr₂.length 32 = randTerm tr₂.length 32 := rfl
          have hg_dhB2 : gamma compI7003 S g (agree msg₂.ratchetKey (rnd tr₂.length 32)) =
              compDhByIdx 4 5 := by
            rw [h_rnd_eq, gamma_agree, hg_dhsB, hg_rk_msg,
                compLookupDh_secret_pub coins_secret_indices.2.2.2.2.2.2.2.2.2.1, compDhByIdx_comm]
          have hg_prkB1 : gamma compI7003 S g
              (DY.Libsignal.TripleRatchet.hmac
                (createChain keys₂.rk msg₂.ratchetKey (randTerm 10 32)).1
                (agree msg₂.ratchetKey (rnd tr₂.length 32))) = prkB1Bytes := by
            unfold DY.Libsignal.TripleRatchet.hmac
            rw [gamma_kdfExtract, hg_rk1B, hg_dhB2]
            exact ratchet_b_and_aes_facts_7003.1
          have hst'₂_eq : st'₂ = (ratchetState st0 msg₂.ratchetKey (rnd tr₂.length 32)).1 :=
            (Prod.mk.inj hrs₂.symm).1
          have hg_rk2 : gamma compI7003 S g stB₁.rk = rk2Bytes := by
            dsimp only [stB₁]; rw [hst'₂_eq]
            dsimp only [ratchetState, st0, bobSt0]
            show gamma compI7003 S g (DY.KdfExtract.kdfExtract
              (DY.Libsignal.TripleRatchet.hmac
                (createChain keys₂.rk msg₂.ratchetKey (randTerm 10 32)).1
                (agree msg₂.ratchetKey (rnd tr₂.length 32)))
              (DY.Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperRatchet")
                (DY.Literal.literalToBytes (ByteArray.mk #[1])))) = rk2Bytes
            unfold DY.Libsignal.TripleRatchet.lit
            rw [gamma_kdfExtract, hg_prkB1, gamma_concat, gamma_literalToBytes, gamma_literalToBytes,
                ofByteArray_info_labels.2.1]
            have hb1 : ofByteArray (ByteArray.mk #[1]) = [0x01#8] := by decide
            rw [hb1]; exact ratchet_b_and_aes_facts_7003.2.1
          have hg_cksB0 : gamma compI7003 S g stB₁.cks = cksB0Bytes := by
            have hrk2_inner : gamma compI7003 S g
                (createChain (createChain keys₂.rk msg₂.ratchetKey (randTerm 10 32)).1
                  msg₂.ratchetKey (rnd tr₂.length 32)).1 = rk2Bytes := by
              simpa [stB₁, hst'₂_eq, ratchetState, st0, bobSt0] using hg_rk2
            dsimp only [stB₁]; rw [hst'₂_eq]
            dsimp only [ratchetState, st0, bobSt0]
            show gamma compI7003 S g (DY.KdfExtract.kdfExtract
              (DY.Libsignal.TripleRatchet.hmac
                (createChain keys₂.rk msg₂.ratchetKey (randTerm 10 32)).1
                (agree msg₂.ratchetKey (rnd tr₂.length 32)))
              (DY.Concat.concat
                (createChain (createChain keys₂.rk msg₂.ratchetKey (randTerm 10 32)).1
                  msg₂.ratchetKey (rnd tr₂.length 32)).1
                (DY.Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperRatchet")
                  (DY.Literal.literalToBytes (ByteArray.mk #[2]))))) = cksB0Bytes
            unfold DY.Libsignal.TripleRatchet.lit
            rw [gamma_kdfExtract, hg_prkB1, gamma_concat, hrk2_inner, gamma_concat,
                gamma_literalToBytes, gamma_literalToBytes, ofByteArray_info_labels.2.1]
            have hb2 : ofByteArray (ByteArray.mk #[2]) = [0x02#8] := by decide
            rw [hb2, ← List.append_assoc]; exact ratchet_b_and_aes_facts_7003.2.2.1
          have hg_dhsB_pk : gamma compI7003 S g (DY.DiffieHellman.dhPk stB₁.dhs) = compPubOfIdx 5 := by
            dsimp only [stB₁]; rw [hst'₂_eq]
            dsimp only [ratchetState]
            rw [h_rnd_eq, gamma_dhPk, hg_dhsB]
            unfold compLookupPub
            rw [coins_secret_indices.2.2.2.2.2.2.2.2.2.1]; rfl
          have hg_myIkB : gamma compI7003 S g stB₁.myIk = ecKey (compPubOfIdx 1) := by
            dsimp only [stB₁]; rw [hst'₂_eq]
            dsimp only [ratchetState, st0, bobSt0]
            unfold serializedIk DY.Libsignal.PQXDH.encodeEC DY.Libsignal.TripleRatchet.litByte
            rw [gamma_concat, gamma_literalToBytes, hg_pk5]; rfl
          have hg_peerIkB : gamma compI7003 S g stB₁.peerIk = ecKey (compPubOfIdx 0) := by
            dsimp only [stB₁]; rw [hst'₂_eq]
            dsimp only [ratchetState, st0, bobSt0]
            unfold serializedIk DY.Libsignal.PQXDH.encodeEC DY.Libsignal.TripleRatchet.litByte
            rw [gamma_concat, gamma_literalToBytes, hg_pk0]; rfl
          -- Evaluate c'₂ and stB₁.recv and stB₁.spqr
          have hc'₂_props : c'₂.ratchetKey = msg₂.ratchetKey ∧ c'₂.index = 1 := by
            unfold consumeMessageKey at hcons₂
            rw [hcnt₀, hc₂_def] at hcons₂
            dsimp only at hcons₂
            have h1 : ¬ ((0 : UInt32) < 0) := by decide
            have h2 : ¬ ((0 : UInt32).toNat - (0 : UInt32).toNat > DY.Libsignal.TripleRatchet.maxForwardJumps) := by decide
            have h3 : ¬ ((0 : UInt32) = u32Max) := by decide
            rw [if_neg' h1, if_neg' h2, if_neg' h3] at hcons₂
            injection hcons₂ with hp_c
            have hc'_eq := (Prod.mk.inj hp_c).2.symm
            rw [hc'_eq]
            exact ⟨rfl, rfl⟩
          have hstB_recv : stB₁.recv = [c'₂] := by
            simp [stB₁, hst'₂_eq, ratchetState, st0, bobSt0,
              DY.Libsignal.TripleRatchet.maxReceiverChains, setRecvChain, hc'₂_props.1]
          have hspqr'₂_eq : spqr'₂ = recvSt (DY.Spqr.spqrInit keys₂.pqr spqrB2A) msg₂.pqRatchet := by
            have hsp_st : st'₂.spqr = DY.Spqr.spqrInit keys₂.pqr spqrB2A := by
              rw [hst'₂_eq]; rfl
            rw [hsp_st] at hrecv₂
            unfold DY.Spqr.spqrRecv DY.Spqr.spqrInit at hrecv₂
            split at hrecv₂
            · cases hrecv₂
            · rw [DY.BytesView.view_pack] at hrecv₂
              dsimp only at hrecv₂
              split at hrecv₂
              · injection hrecv₂ with hp_s
                exact (Prod.mk.inj hp_s).1.symm
              · cases hrecv₂
          have hspqr_bytes : gamma compI7003 S g stB₁.spqr =
              S.recvState (S.init pqrBytes [1#8]) pqMsg1Bytes := by
            dsimp only [stB₁]
            rw [hspqr'₂_eq, gamma_spqrRecvState, gamma_spqrInit, hg_pqr, hfi_pq, hp_pq]
            have hb2a : gamma compI7003 S g spqrB2A = [1#8] := by
              unfold spqrB2A DY.Spqr.encodeSpqrDirectionParams
              rw [gamma_literalToBytes]; decide
            rw [hb2a]
          refine ⟨ek₂, ct₂, keys₂, msg₂, seed₂, pq₂, m₂, key₂, st'₂, stB₁, c₂, c'₂, hnext₂,
            ⟨hg_ek₂, hg_pqr, hg_rk2, hg_cksB0, hg_dhsB_pk, hg_myIkB, hg_peerIkB,
             by dsimp only [stB₁]; rw [hst'₂_eq]; rfl,
             by dsimp only [stB₁]; rw [hst'₂_eq]; rfl,
             by dsimp only [stB₁]; rw [hst'₂_eq]; rfl,
             hstB_recv, hc'₂_props.1, hc'₂_props.1 ▸ hg_rk_msg, hc'₂_props.2,
             hspqr'₂_eq, hspqr_bytes, rfl⟩⟩

end Symbolic.BugInjection.Proofs.SyntheticRecvCommon.PrefixPins7003B

