/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Clean3BobStart7003
public import Symbolic.BugInjection.Proofs.SyntheticRecvCommon.MacLaws7003
public import Symbolic.BugInjection.Proofs.SyntheticDecryptCloneNotPersisted.NoExplains
public import Symbolic.Proofs.Tests.CliNonvacuity.RecvNoCollision
import DY.Bytes.Basic
import DY.Trace.Basic
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.Trace.Basic

/-!
# Step 3 Non-Collision for `DecryptCloneNotPersisted` (`Clean3NoCol.lean`)

Discharges `¬ NextEventCollides` at `ev3_m1` after the explained 3-step prefix
`[.run ev0, .run ev1_m1, .run ev2_m1]` using the clean 3-step explanation
`(gClean7003 false cl₁ 0, ssClean3 cl₁, visClean3 cl₁)` and `encMsg1Pure cl₁`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace Symbolic.BugInjection.Proofs.SyntheticDecryptCloneNotPersisted

unseal DY.Bytes

open ByteSpecs (hmacWith)
open scoped DY.Libsignal.Composed
open DY (ExecTrace)
open DY.DiffieHellman (dhPk)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (CliEvent RunEvent)
open DY.Libsignal.PQXDH.Refinement (wirePrekeyTag)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.TripleRatchet
  (TRState TREvent TRSignalMsg RecvChain messageVersion parseTrSignalMsg
   recvChainFor findRecvChain consumeMessageKey skippedSeeds createChain kdfCk
   trMsgKeys computeMac x25519LowOrder)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry TrialCtx
   gamma runTrace honestSaltsOf availableStates ownKeys storedStates storedSecrets
   plaintextTerms recvRepresentationsOn parsePreKeyWire
   whisperTrials trialTerms storedRatchetKeys getMessageSentAt_attackerKnows
   RecvCollisionOn ReselectCollisionOn Explains lastSent)
open DY.Libsignal.Composed.Refinement.Cli (NextEventCollides)
open Symbolic.Proofs.Tests.Shared.Composed.Runs (aliceSt encSig parse_encMsg)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeSteps (m0Of)
open Symbolic.Proofs.Tests.CliNonvacuity.Table.MkTerm (tRnd)
open Symbolic.Proofs.Tests.CliNonvacuity.RecvNoCollision (not_nextEventCollides_accepted_recv)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompI7003 (compI7003 compPubOfIdx)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompFits7003 (compFitsPinned7003)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.TraceEvents7003
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Gamma7003 (setup_ids_7003)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.PrefixPins7003 (SemPinned2 if_pos' if_neg')
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.TraceState7003 (NoSkippedKeys)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Dag7003Data
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Memo7003Combinators
  (SafeMemo safeMemo_of_termAt gamma_of_termAt not_memoCollisionOn_of_safeMemo)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Memo7003TermAt (safeMemo_plaintext)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.MacLaws7003
  (not_readCollisionCli_of_no_decrypt not_signalMsgAcceptedOnlyViaCollision_of_no_explains
   not_macTagForgery_of_msg_mismatch)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Dag7003Nodes
  (gClean7003 o1Pure stA0Pure key0Pure pqMsg1Pure stA1Pure encMsg1Pure encSig1Pure
   cB'Pure stB1Pure cB'Pure_chainKey_eq CommonNodes mkCommonNodes M1Nodes mkM1Nodes)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Dag7003States
  (symDec_symEnc_mem_eq ghostAndSemMatchSetup_gClean7003 pqSecrets7003
   safeMemo_pqSecrets7003 safeMemo_stA0 safeMemo_stA1 safeMemo_stB1)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Clean2BobStart7003
  (m1Clean t6Clean p1Of parse_out1Of eq_cons_tail_of_head?
   getMessageSentAt_le spqrHeaded_computeMac lastSent_t5_t6Clean)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Clean3BobStart7003

attribute [local irreducible] Symbolic.BugInjection.hexBytes
attribute [local irreducible] ByteSpecs.hmacWith

private theorem p1_false_message_eq : (p1Of false).message = msg1M1Bytes := by
  decide +kernel

attribute [local irreducible] p1Of

private def checkMsg1M1Whisper : Bool :=
  match CryptoGames.LibsignalSession.SignalMessage.tryFrom
      CryptoVerification.LibsignalProtoCodec.protoSignalCodec msg1M1Bytes with
  | .ok m =>
    decide (m.ciphertext = ct1M1Bytes) &&
    decide (m.senderRatchetKey.bytes.toList = compPubOfIdx 4) &&
    decide (m.pqRatchet = pqMsg1Bytes) &&
    decide (m.counter = 0) &&
    decide (m.messageVersion = 4)
  | .error _ => false

private theorem checkMsg1M1Whisper_eq : checkMsg1M1Whisper = true := by
  decide +kernel

theorem encMsg1_mem_recvReps_clean3 {S : OpaqueSymbolSemantics} {cl₁ : Nat}
    (hkpk : S.kemPk (bytesOf pqskBId) = bytesOf pqpkId) (hsem2 : SemPinned2 S cl₁) :
    encMsg1Pure cl₁ ∈ recvRepresentationsOn compI7003 S (gClean7003 false cl₁ 0)
      (t7Clean cl₁) msg1M1Bytes := by
  let g := gClean7003 false cl₁ 0
  have cn := mkCommonNodes (mode := false) (S := S) (pts := [tRnd 31 32])
    (cl₁ := cl₁) (cl₃ := 0) hkpk hsem2
  have mn := mkM1Nodes cn List.mem_cons_self
  have h37 : (t6Clean cl₁).getMessageSentAt 37 = some (encMsg1Pure cl₁) := by
    have hls := lastSent_t5_t6Clean cl₁
    unfold lastSent at hls
    rw [t6Clean_length, if_pos' (by rw [Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t5_length]; omega)] at hls
    exact hls
  have hknow : (encMsg1Pure cl₁).AttackerKnows (t7Clean cl₁) :=
    getMessageSentAt_attackerKnows (getMessageSentAt_le (t6Clean_le_t7Clean cl₁) h37)
  have hparse_pure : parseTrSignalMsg (encMsg1Pure cl₁) = some (encSig1Pure cl₁).2 :=
    parse_encMsg stA0Pure (tRnd 32 cl₁) key0Pure (tRnd 31 32)
  refine ⟨hknow, by rw [gamma_of_termAt mn.out1]; decide +kernel,
    by rw [hparse_pure]; rfl, ?_⟩
  intro msg hparse
  rw [hparse_pure] at hparse
  injection hparse with hparse; subst hparse
  refine ⟨by rw [gamma_of_termAt mn.wire1]; decide +kernel,
    by rw [gamma_of_termAt mn.mac1]; decide +kernel,
    spqrHeaded_computeMac _ _ _ _, ?_⟩
  intro m hm
  have hc := checkMsg1M1Whisper_eq
  unfold checkMsg1M1Whisper at hc
  rw [hm] at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨hct, hrk⟩, hpq⟩, hcnt⟩, hver⟩ := hc
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [gamma_of_termAt mn.ct1, hct]; decide +kernel
  · dsimp only [encSig1Pure, encSig, stA0Pure, aliceSt]
    rw [gamma_of_termAt cn.pk4, hrk]; decide
  · dsimp only [encSig1Pure, encSig]; change gamma compI7003 S g (pqMsg1Pure cl₁) = _
    rw [gamma_of_termAt cn.pqMsg1, hpq]; decide
  · rw [hcnt]; rfl
  · rw [hver]; rfl

theorem storedRatchetKeys_of_noSkippedKeys {r : ProtocolSetup} {tr : ExecTrace}
    (hno : NoSkippedKeys tr) (msg : TRSignalMsg) :
    storedRatchetKeys r tr msg =
      (availableStates r tr).flatMap fun st => st.toDRState.recv.map (·.ratchetKey) := by
  unfold storedRatchetKeys
  refine List.append_right_eq_self.mpr (List.filterMap_eq_nil_iff.mpr fun i _ => ?_)
  rcases he : tr.getEventAt TREvent i with _ | e
  · rfl
  · cases e with
    | SkippedKeyStored s pk n seed rIdx child => exact absurd he (hno i s pk n seed rIdx child)
    | _ => rfl

theorem not_reselectCollisionOn_clean3_m1 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false) (cl₁ : Nat)
    (hkpk : S.kemPk (bytesOf pqskBId) = bytesOf pqpkId) (hsem2 : SemPinned2 S cl₁) :
    ¬ ReselectCollisionOn compI7003 r S (gClean7003 false cl₁ 0)
      (t7Clean cl₁) (visClean3 cl₁) [DY.Spqr.zeroKey, key0Pure] (encMsg1Pure cl₁) := by
  have cn := mkCommonNodes (mode := false) (S := S) (pts := [tRnd 31 32])
    (cl₁ := cl₁) (cl₃ := 0) hkpk hsem2
  have hparse_pure : parseTrSignalMsg (encMsg1Pure cl₁) = some (encSig1Pure cl₁).2 :=
    parse_encMsg stA0Pure (tRnd 32 cl₁) key0Pure (tRnd 31 32)
  rintro ⟨msg, hparse, rk, hrk, hgamEq, hrkNe, _⟩
  rw [hparse_pure] at hparse; injection hparse with hparse; subst hparse
  rw [storedRatchetKeys_of_noSkippedKeys (noSkippedKeys_t7Clean cl₁)] at hrk
  have hav : availableStates r (t7Clean cl₁) = [stA0Pure, stA1Pure cl₁, stB1Pure cl₁] := by
    unfold availableStates; rw [storedStates_t7Clean ha hb hopk]; rfl
  rw [hav] at hrk
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_eq, List.cons_append,
    List.nil_append, List.append_nil, List.map,
    stA0Pure, stA1Pure, stB1Pure, cB'Pure, Symbolic.Proofs.Tests.Shared.Composed.Runs.encSt,
    Symbolic.Proofs.Tests.Shared.Composed.Runs.ratchetState,
    Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Dag7003Nodes.cBPure, aliceSt, o1Pure,
    TRState.toDRState, List.mem_cons, List.not_mem_nil, or_false] at hrk
  have hmrk : (encSig1Pure cl₁).2.ratchetKey = dhPk (tRnd 24 32) := rfl
  rw [hmrk] at hgamEq hrkNe
  rcases hrk with rfl | rfl | rfl
  · rw [gamma_of_termAt cn.pk2, gamma_of_termAt cn.pk4] at hgamEq
    exact absurd hgamEq (by decide)
  · rw [gamma_of_termAt cn.pk2, gamma_of_termAt cn.pk4] at hgamEq
    exact absurd hgamEq (by decide)
  · exact hrkNe rfl

theorem x25519LowOrder_dhPk (sk : DY.Bytes) : x25519LowOrder (dhPk sk) = false := by
  have hv1 : ((dhPk sk).view? DY.X25519.Variant.SubF) = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.X25519.Variant.SubF
      ({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes)
  have hv2 : ((dhPk sk).view? DY.Literal.Literal.SubF) = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Literal.Literal.SubF
      ({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes)
  simp only [x25519LowOrder, DY.X25519.normalizeX25519Key, hv1,
    DY.Literal.bytesToLiteral, DY.Literal.CanMkLiteral.bytesToLiteral, hv2]

theorem whisperTrials_of_noSkippedKeys {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {tr : ExecTrace} {msg : TRSignalMsg}
    (hno : NoSkippedKeys tr) (hver : msg.version = messageVersion) :
    whisperTrials compI7003 r S g tr msg =
      (availableStates r tr).flatMap fun st =>
        let own := ownKeys r tr st msg
        let chains :=
          (st.toDRState.recv.filter fun c =>
            decide (gamma compI7003 S g c.ratchetKey = gamma compI7003 S g msg.ratchetKey)) ++
          match recvChainFor st.toDRState msg.ratchetKey with
          | some (c, true) => [c]
          | _ => []
        chains.map fun c =>
          match consumeMessageKey c msg.counter with
          | none =>
            { peerIk := st.peerIk, myIk := st.myIk, extra := [c.chainKey],
              ownSalts := [], seed? := none }
          | some (seed, c') =>
            { peerIk := st.peerIk, myIk := st.myIk,
              extra := [c.chainKey, c'.chainKey] ++ skippedSeeds c msg.counter,
              ownSalts := own, seed? := some seed } := by
  unfold whisperTrials
  rw [if_pos' hver]
  dsimp only
  congr 1; funext st
  refine (List.append_right_eq_self.mpr (List.filterMap_eq_nil_iff.mpr fun i _ => ?_)).trans ?_
  · rcases he : tr.getEventAt TREvent i with _ | e
    · rfl
    · cases e with
      | SkippedKeyStored s pk n seed rIdx child => exact absurd he (hno i s pk n seed rIdx child)
      | _ => rfl
  · congr 2
    unfold recvChainFor DY.Libsignal.TripleRatchet.recvHalfStep
    cases findRecvChain st.recv msg.ratchetKey <;> cases x25519LowOrder msg.ratchetKey <;> rfl

theorem consumeMessageKey_0_0 (rk ck : DY.Bytes) (rIdx : Nat) :
    consumeMessageKey { ratchetKey := rk, chainKey := ck, index := 0, rIdx := rIdx } 0 =
      some ((kdfCk ck).2, { ratchetKey := rk, chainKey := (kdfCk ck).1, index := 1, rIdx := rIdx }) := rfl

theorem consumeMessageKey_1_0 (rk ck : DY.Bytes) (rIdx : Nat) :
    consumeMessageKey { ratchetKey := rk, chainKey := ck, index := 1, rIdx := rIdx } 0 = none := rfl

theorem skippedSeeds_0_0 (rk ck : DY.Bytes) (rIdx : Nat) :
    skippedSeeds { ratchetKey := rk, chainKey := ck, index := 0, rIdx := rIdx } 0 = [] := rfl

private theorem whisperTrials_clean3_m1 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false) (cl₁ : Nat)
    (hkpk : S.kemPk (bytesOf pqskBId) = bytesOf pqpkId) (hsem2 : SemPinned2 S cl₁) :
    let ckAA0 := (createChain stA0Pure.rk (dhPk (tRnd 24 32)) (tRnd 24 32)).2
    ∃ ownA0 ownA1 : List DY.Bytes,
      whisperTrials compI7003 r S (gClean7003 false cl₁ 0) (t7Clean cl₁) (encSig1Pure cl₁).2 =
        [ { peerIk := stA0Pure.peerIk, myIk := stA0Pure.myIk,
            extra := [ckAA0, (kdfCk ckAA0).1], ownSalts := ownA0, seed? := some (kdfCk ckAA0).2 },
          { peerIk := stA0Pure.peerIk, myIk := stA0Pure.myIk,
            extra := [ckAA0, (kdfCk ckAA0).1], ownSalts := ownA1, seed? := some (kdfCk ckAA0).2 },
          { peerIk := (stB1Pure cl₁).peerIk, myIk := (stB1Pure cl₁).myIk,
            extra := [(cB'Pure cl₁).chainKey], ownSalts := [], seed? := none } ] := by
  let g := gClean7003 false cl₁ 0
  have cn := mkCommonNodes (mode := false) (S := S) (pts := [tRnd 31 32])
    (cl₁ := cl₁) (cl₃ := 0) hkpk hsem2
  refine ⟨ownKeys r (t7Clean cl₁) stA0Pure (encSig1Pure cl₁).2,
    ownKeys r (t7Clean cl₁) (stA1Pure cl₁) (encSig1Pure cl₁).2, ?_⟩
  rw [whisperTrials_of_noSkippedKeys (noSkippedKeys_t7Clean cl₁) rfl]
  have hav : availableStates r (t7Clean cl₁) = [stA0Pure, stA1Pure cl₁, stB1Pure cl₁] := by
    unfold availableStates; rw [storedStates_t7Clean ha hb hopk]; rfl
  rw [hav]
  have hmrk : (encSig1Pure cl₁).2.ratchetKey = dhPk (tRnd 24 32) := rfl
  have hmcnt : (encSig1Pure cl₁).2.counter = 0 := rfl
  have hgam_ne : gamma compI7003 S g (dhPk (tRnd 10 32)) ≠ gamma compI7003 S g (dhPk (tRnd 24 32)) := by
    rw [gamma_of_termAt cn.pk2, gamma_of_termAt cn.pk4]; decide
  have hpk_ne : dhPk (tRnd 10 32) ≠ dhPk (tRnd 24 32) := fun h => hgam_ne (congrArg _ h)
  have hdec_ne : decide (gamma compI7003 S g (dhPk (tRnd 10 32)) =
      gamma compI7003 S g (dhPk (tRnd 24 32))) = false := decide_eq_false hgam_ne
  have hbeq_ne : (dhPk (tRnd 10 32) == dhPk (tRnd 24 32)) = false := beq_eq_false_iff_ne.mpr hpk_ne
  have hdec_eq : decide (gamma compI7003 S g (dhPk (tRnd 24 32)) =
      gamma compI7003 S g (dhPk (tRnd 24 32))) = true := decide_eq_true rfl
  have hbeq_eq : (dhPk (tRnd 24 32) == dhPk (tRnd 24 32)) = true := beq_self_eq_true _
  rw [hmrk, hmcnt]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  dsimp only [recvChainFor, findRecvChain, List.find?, List.filter,
    stA0Pure, stA1Pure, stB1Pure, cB'Pure, Symbolic.Proofs.Tests.Shared.Composed.Runs.encSt,
    Symbolic.Proofs.Tests.Shared.Composed.Runs.ratchetState,
    Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Dag7003Nodes.cBPure, aliceSt, o1Pure]
  rw [hdec_ne, hbeq_ne, hdec_eq, hbeq_eq, x25519LowOrder_dhPk]
  simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, List.append_nil, List.cons_append,
    List.map, consumeMessageKey_0_0, consumeMessageKey_1_0, skippedSeeds_0_0]

private theorem safeMemo_trialAA {S : OpaqueSymbolSemantics} {cl₁ : Nat}
    (mn : M1Nodes S [tRnd 31 32] cl₁) (own : List DY.Bytes) :
    let ckAA0 := (createChain stA0Pure.rk (dhPk (tRnd 24 32)) (tRnd 24 32)).2
    ∀ t ∈ trialTerms [DY.Spqr.zeroKey, key0Pure] (encSig1Pure cl₁).2
      { peerIk := stA0Pure.peerIk, myIk := stA0Pure.myIk,
        extra := [ckAA0, (kdfCk ckAA0).1], ownSalts := own, seed? := some (kdfCk ckAA0).2 },
      SafeMemo false S (gClean7003 false cl₁ 0) [tRnd 31 32] t := by
  intro ckAA0 t ht
  have hpt : SafeMemo false S (gClean7003 false cl₁ 0) [tRnd 31 32] (tRnd 31 32) :=
    safeMemo_plaintext List.mem_cons_self (Or.inl rfl) rfl
  simp only [trialTerms, List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | hdec0 | rfl | rfl | rfl | rfl | hdec1
  · exact safeMemo_of_termAt mn.ckAA0
  · exact safeMemo_of_termAt mn.ckAA1
  · exact safeMemo_of_termAt mn.zAACkey
  · exact safeMemo_of_termAt mn.zAAMkey
  · exact safeMemo_of_termAt mn.zAAIv
  · exact safeMemo_of_termAt mn.zAAMac
  · rw [symDec_symEnc_mem_eq hdec0]; exact hpt
  · exact safeMemo_of_termAt mn.p1AACkey
  · exact safeMemo_of_termAt mn.p1AAMkey
  · exact safeMemo_of_termAt mn.p1AAIv
  · exact safeMemo_of_termAt mn.p1AAMac
  · rw [symDec_symEnc_mem_eq hdec1]; exact hpt

theorem not_recvCollisionOn_clean3_m1 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false) (cl₁ : Nat)
    (hkpk : S.kemPk (bytesOf pqskBId) = bytesOf pqpkId) (hsem2 : SemPinned2 S cl₁) :
    ¬ RecvCollisionOn compI7003 r S (gClean7003 false cl₁ 0)
      (t7Clean cl₁) (visClean3 cl₁) [DY.Spqr.zeroKey, key0Pure] (encMsg1Pure cl₁) := by
  let g := gClean7003 false cl₁ 0
  let pts := [tRnd 31 32]
  have cn := mkCommonNodes (mode := false) (S := S) (pts := pts) (cl₁ := cl₁) (cl₃ := 0) hkpk hsem2
  have mn := mkM1Nodes cn List.mem_cons_self
  unfold RecvCollisionOn; dsimp only
  have hparse : parseTrSignalMsg (encMsg1Pure cl₁) = some (encSig1Pure cl₁).2 :=
    parse_encMsg _ _ _ _
  rw [hparse]; dsimp only
  obtain ⟨ownA0, ownA1, htrials⟩ := whisperTrials_clean3_m1 ha hb hopk cl₁ hkpk hsem2
  rw [htrials]
  rintro (hmemo | hmac)
  · refine not_memoCollisionOn_of_safeMemo (mode := false) (pts := pts)
      (plaintextTerms_visClean3 cl₁) ?_ ?_ ?_ ?_ ?_ hmemo
    · intro t ht; rw [sendTerms_visClean3] at ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl
      · exact safeMemo_of_termAt cn.ek
      · exact safeMemo_of_termAt cn.ctKem
      · exact safeMemo_of_termAt mn.out1
    · rw [storedStates_t7Clean ha hb hopk]
      intro ls hls; simp only [List.mem_cons, List.not_mem_nil, or_false] at hls
      rcases hls with rfl | rfl | rfl
      · exact safeMemo_stA0 cn
      · exact safeMemo_stA1 cn
      · exact safeMemo_stB1 cn
    · rw [storedSecrets_t7Clean]; exact safeMemo_pqSecrets7003 cn
    · intro t ht; rcases List.mem_singleton.mp ht with rfl
      exact safeMemo_plaintext List.mem_cons_self (Or.inl rfl) rfl
    · intro t ht
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.mem_cons, List.mem_append] at ht
      rcases ht with rfl | ht0 | ht1 | htB
      · exact safeMemo_of_termAt mn.out1
      · exact safeMemo_trialAA mn ownA0 t ht0
      · exact safeMemo_trialAA mn ownA1 t ht1
      · simp only [trialTerms, List.append_nil, List.mem_singleton] at htB
        rw [htB, cB'Pure_chainKey_eq]; exact safeMemo_of_termAt cn.stA1Cks
  · refine not_macTagForgery_of_msg_mismatch (mk_ref := macKey1Bytes) (msg_ref := macIn1M1Bytes)
      (by rw [gamma_of_termAt mn.mac1, pqxdh_and_mac_facts_7003.2.2.2.2.2.1]; decide +kernel)
      (by decide) pqxdh_and_mac_facts_7003.2.2.2.2.2.2.1 (fun ctx hctx seed hseed => ?_) hmac
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hctx
    rcases hctx with rfl | rfl | rfl
    · change gamma compI7003 S g (DY.Libsignal.PQXDH.serializedIk (dhPk (tRnd 5 32))) ++
        (gamma compI7003 S g (DY.Libsignal.PQXDH.serializedIk (dhPk (tRnd 0 32))) ++
          gamma compI7003 S g (encSig1Pure cl₁).2.wire) ≠ macIn1M1Bytes
      rw [gamma_of_termAt cn.ik1s, gamma_of_termAt cn.ik0s, gamma_of_termAt mn.wire1]
      decide +kernel
    · change gamma compI7003 S g (DY.Libsignal.PQXDH.serializedIk (dhPk (tRnd 5 32))) ++
        (gamma compI7003 S g (DY.Libsignal.PQXDH.serializedIk (dhPk (tRnd 0 32))) ++
          gamma compI7003 S g (encSig1Pure cl₁).2.wire) ≠ macIn1M1Bytes
      rw [gamma_of_termAt cn.ik1s, gamma_of_termAt cn.ik0s, gamma_of_termAt mn.wire1]
      decide +kernel
    · cases hseed

theorem not_nextEventCollides_ev3_m1 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {vis : List VisEntry}
    (hf : compFitsPinned7003 setup7003 compI7003 r)
    (hex : Explains compI7003 r S g ss vis [.run ev0, .run ev1_m1, .run ev2_m1]) :
    ¬ NextEventCollides compI7003 r S g ss vis [.run ev0, .run ev1_m1, .run ev2_m1] ev3_m1 := by
  obtain ⟨ha, hb, hopk, _⟩ := setup_ids_7003 hf
  obtain ⟨_, hkpk⟩ := ghostAndSemMatchSetup_gClean7003 false 0 0 hf hex.1
  obtain ⟨⟨cl₁, hsem2⟩, hkb⟩ := knownBaseKeyOn_and_semPinned2_of_explains_m1_3 hf hex
  have hhd : out1M1Bytes.head? = some wirePrekeyTag := by decide +kernel
  obtain ⟨body, hcons⟩ : ∃ body, out1M1Bytes = wirePrekeyTag :: body :=
    ⟨_, eq_cons_tail_of_head? hhd⟩
  have hin : ev3_m1.input = wirePrekeyTag :: body := out1M1Raw_eq.trans hcons
  refine not_nextEventCollides_accepted_recv rfl hin
    (fun htag => absurd htag (by decide)) (fun p hp => ⟨fun _ => ?_, fun hnkb => ?_⟩)
  · have hp0 : parsePreKeyWire (wirePrekeyTag :: body) = some (p1Of false) := by
      rw [← hcons]; exact parse_out1Of false
    cases hp.symm.trans hp0
    rw [p1_false_message_eq]
    exact not_signalMsgAcceptedOnlyViaCollision_of_no_explains
      (explains_clean3 false cl₁ 0 hf hex hsem2)
      (not_readCollisionCli_of_no_decrypt fun m hm => by
        simp [ssClean3, m0Of, m1Clean, m2Clean] at hm
        rcases hm with rfl | rfl | rfl <;> rfl)
      (by rw [runTrace_ssClean3 ha hb hopk]; exact encMsg1_mem_recvReps_clean3 hkpk hsem2)
      (fun _ _ _ => not_explains_m1 hf)
      (by rw [runTrace_ssClean3 ha hb hopk, honestSaltsOf_ssClean3 ha hb hopk]
          exact not_recvCollisionOn_clean3_m1 ha hb hopk cl₁ hkpk hsem2)
      (by rw [runTrace_ssClean3 ha hb hopk, honestSaltsOf_ssClean3 ha hb hopk]
          exact not_reselectCollisionOn_clean3_m1 ha hb hopk cl₁ hkpk hsem2)
  · exact absurd (hkb p (by rwa [out1M1Raw_eq, hcons])) hnkb

end Symbolic.BugInjection.Proofs.SyntheticDecryptCloneNotPersisted
