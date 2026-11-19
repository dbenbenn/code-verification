/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticSignalMsgCanonicalMac.Clean4Explain
public import Symbolic.BugInjection.Proofs.SyntheticRecvCommon.MacLaws7003
public import Symbolic.Proofs.Tests.CliNonvacuity.RecvNoCollision
public import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.TrWireMsg
import DY.Bytes.Basic
import DY.Trace.Basic
import DY.EquationalTheory.Concat
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.Trace.Basic

/-!
# Step 4 Non-Collision for `SignalMsgCanonicalMac` (`Clean4NoCol.lean`)

Discharges `¬ NextEventCollides` at `ev4_m2` after the explained 4-step prefix
`[.run ev0, .run ev1_m2, .run ev2_m2, .run ev3_m2]` using the clean 4-step explanation
`(gClean7003 true cl₁ cl₃, ssClean4 cl₁ cl₃, visClean4 cl₁ cl₃)` and `tMut4M2Pure cl₁ cl₃`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace Symbolic.BugInjection.Proofs.SyntheticSignalMsgCanonicalMac

unseal DY.Bytes

open ByteSpecs (hmacWith)
open scoped DY.Libsignal.Composed
open DY (ExecTrace)
open DY.DiffieHellman (dhPk)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (CliEvent RunEvent)
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
open Symbolic.Proofs.Tests.Shared.Composed.Runs
  (aliceSt encMsg encSig parse_encMsg length_hmac createChain_comm)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeSteps (m0Of)
open Symbolic.Proofs.Tests.CliNonvacuity.Table.MkTerm (tRnd tCat tTrW)
open Symbolic.Proofs.Tests.CliNonvacuity.RecvNoCollision (not_nextEventCollides_accepted_recv)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompI7003 (compI7003 compPubOfIdx)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompFits7003 (compFitsPinned7003)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.TraceEvents7003
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Gamma7003 (setup_ids_7003)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.PrefixPins7003 (SemPinned4_M2 if_pos' if_neg')
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
   cB'Pure stB1Pure dhsBPure key3Pure pqMsg3Pure stB2Pure encMsg3Pure encSig3Pure
   wire4MutPure tMut4M2Pure stB1Pure_cks_eq cB'Pure_chainKey_eq
   CommonNodes mkCommonNodes M2Nodes mkM2Nodes)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Dag7003States
  (symDec_symEnc_mem_eq ghostAndSemMatchSetup_gClean7003 pqSecrets7003
   safeMemo_pqSecrets7003 safeMemo_stA0 safeMemo_stA1 safeMemo_stB1 safeMemo_stB2)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Clean2BobStart7003
  (m1Clean spqrHeaded_computeMac)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Clean3BobStart7003 (m2Clean t7Clean_length)

attribute [local irreducible] Symbolic.BugInjection.hexBytes
attribute [local irreducible] ByteSpecs.hmacWith

def msgMut4Pure (cl₁ cl₃ : Nat) : TRSignalMsg :=
  { wire := wire4MutPure cl₁ cl₃
    mac := (encSig3Pure cl₁ cl₃).mac
    version := 4
    ratchetKey := dhPk dhsBPure
    counter := 0
    ciphertext := (encSig3Pure cl₁ cl₃).ciphertext
    pqRatchet := pqMsg3Pure cl₁ cl₃ }

theorem parseTrSignalMsg_tMut4M2Pure (cl₁ cl₃ : Nat) :
    parseTrSignalMsg (tMut4M2Pure cl₁ cl₃) = some (msgMut4Pure cl₁ cl₃) := by
  have hl : (DY.Concat.concat (wire4MutPure cl₁ cl₃) (encSig3Pure cl₁ cl₃).mac).length -
      DY.Trunc.trunc8Length = (wire4MutPure cl₁ cl₃).length := by
    simp [encSig3Pure, encSig, computeMac, DY.Trunc.length_trunc8, length_hmac, DY.Trunc.trunc8Length]
  have ht : tMut4M2Pure cl₁ cl₃ = DY.Concat.concat (wire4MutPure cl₁ cl₃) (encSig3Pure cl₁ cl₃).mac := rfl
  have hw : wire4MutPure cl₁ cl₃ = DY.TrWire.trWireMsg 4 (dhPk dhsBPure) 0 0
      (encSig3Pure cl₁ cl₃).ciphertext (pqMsg3Pure cl₁ cl₃) ev4Variation := rfl
  rw [ht]
  simp only [parseTrSignalMsg, hl, DY.Concat.split_concat]
  rw [hw]
  simp only [bind, Option.bind, DY.TrWire.trWireMsgFields?_trWireMsg]
  rfl

theorem tMut4M2Pure_mem_recvReps_clean4 {S : OpaqueSymbolSemantics} {cl₁ cl₃ : Nat}
    (hkpk : S.kemPk (bytesOf pqskBId) = bytesOf pqpkId) (hsem4 : SemPinned4_M2 S cl₁ cl₃) :
    tMut4M2Pure cl₁ cl₃ ∈ recvRepresentationsOn compI7003 S (gClean7003 true cl₁ cl₃)
      (t8Clean cl₁ cl₃) body4M2Bytes := by
  let g := gClean7003 true cl₁ cl₃
  let pts := [tRnd 31 32, tRnd 47 32]
  have cn := mkCommonNodes (mode := true) (S := S) (pts := pts)
    (cl₁ := cl₁) (cl₃ := cl₃) hkpk hsem4.1
  have mn := mkM2Nodes cn hsem4 List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self)
  have h53 : (t8Clean cl₁ cl₃).getMessageSentAt 53 = some (encMsg3Pure cl₁ cl₃) := by
    have hls := lastSent_t7Clean_t8Clean cl₁ cl₃
    unfold lastSent at hls
    rw [t8Clean_length, if_pos' (by rw [t7Clean_length]; omega)] at hls
    exact hls
  have hk3 : (encMsg3Pure cl₁ cl₃).AttackerKnows (t8Clean cl₁ cl₃) :=
    getMessageSentAt_attackerKnows h53
  have hsp := DY.Concat.attacker_knows_split (encMsg3Pure cl₁ cl₃)
    (encSig3Pure cl₁ cl₃).wire.length (t8Clean cl₁ cl₃) hk3
  rw [show encMsg3Pure cl₁ cl₃ = DY.Concat.concat (encSig3Pure cl₁ cl₃).wire
      (encSig3Pure cl₁ cl₃).mac from rfl, DY.Concat.split_concat] at hsp
  have hargs := DY.TrWire.attacker_knows_trWireMsg_args 4 (dhPk dhsBPure) 0 0
    (encSig3Pure cl₁ cl₃).ciphertext (pqMsg3Pure cl₁ cl₃) DY.TrWire.canonicalVariation
    (t8Clean cl₁ cl₃) hsp.1
  have hkw4 : (wire4MutPure cl₁ cl₃).AttackerKnows (t8Clean cl₁ cl₃) :=
    DY.TrWire.attacker_knows_trWireMsg 4 (dhPk dhsBPure) 0 0
      (encSig3Pure cl₁ cl₃).ciphertext (pqMsg3Pure cl₁ cl₃) ev4Variation
      (t8Clean cl₁ cl₃) hargs.1 hargs.2.1 hargs.2.2
  have hknow : (tMut4M2Pure cl₁ cl₃).AttackerKnows (t8Clean cl₁ cl₃) :=
    DY.Concat.attacker_knows_concat _ _ _ hkw4 hsp.2
  have hparse_pure := parseTrSignalMsg_tMut4M2Pure cl₁ cl₃
  refine ⟨hknow, by rw [gamma_of_termAt mn.out4Mut]; decide +kernel,
    by rw [hparse_pure]; rfl, ?_⟩
  intro msg hparse
  rw [hparse_pure] at hparse
  injection hparse with hparse; subst hparse
  refine ⟨by dsimp only [msgMut4Pure]; rw [gamma_of_termAt mn.wire4Mut, in4M2_split_eq.2.2.1]; decide +kernel,
    by dsimp only [msgMut4Pure]; rw [gamma_of_termAt mn.mac3, in4M2_split_eq.2.2.2.1]; decide +kernel,
    spqrHeaded_computeMac _ _ _ _, ?_⟩
  intro m hm
  have hc := checkWhisper4M2_eq
  unfold checkWhisper4M2 at hc
  rw [hm] at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨hct, hrk⟩, hpq⟩, hcnt⟩, _⟩, hver⟩ := hc
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [msgMut4Pure]; rw [gamma_of_termAt mn.ct3, hct]; decide +kernel
  · dsimp only [msgMut4Pure]; rw [gamma_of_termAt cn.pk5, hrk]; decide
  · dsimp only [msgMut4Pure]; rw [gamma_of_termAt mn.pqMsg3, hpq]; decide
  · rw [hcnt]; rfl
  · rw [hver]; rfl

private theorem storedRatchetKeys_of_noSkippedKeys_m2 {r : ProtocolSetup} {tr : ExecTrace}
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

theorem not_reselectCollisionOn_clean4_m2 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false) (cl₁ cl₃ : Nat)
    (hkpk : S.kemPk (bytesOf pqskBId) = bytesOf pqpkId) (hsem4 : SemPinned4_M2 S cl₁ cl₃) :
    ¬ ReselectCollisionOn compI7003 r S (gClean7003 true cl₁ cl₃)
      (t8Clean cl₁ cl₃) (visClean4 cl₁ cl₃)
      [DY.Spqr.zeroKey, key0Pure, key3Pure cl₁ cl₃] (tMut4M2Pure cl₁ cl₃) := by
  have cn := mkCommonNodes (mode := true) (S := S) (pts := [tRnd 31 32, tRnd 47 32])
    (cl₁ := cl₁) (cl₃ := cl₃) hkpk hsem4.1
  rintro ⟨msg, hparse, rk, hrk, hgamEq, hrkNe, _⟩
  rw [parseTrSignalMsg_tMut4M2Pure] at hparse; injection hparse with hparse; subst hparse
  rw [storedRatchetKeys_of_noSkippedKeys_m2 (noSkippedKeys_t8Clean cl₁ cl₃)] at hrk
  have hav : availableStates r (t8Clean cl₁ cl₃) =
      [stA0Pure, stA1Pure cl₁, stB1Pure cl₁, stB2Pure cl₁ cl₃] := by
    unfold availableStates; rw [storedStates_t8Clean ha hb hopk]; rfl
  rw [hav] at hrk
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_eq, List.cons_append,
    List.nil_append, List.append_nil, List.map,
    stA0Pure, stA1Pure, stB1Pure, stB2Pure, cB'Pure, Symbolic.Proofs.Tests.Shared.Composed.Runs.encSt,
    Symbolic.Proofs.Tests.Shared.Composed.Runs.ratchetState,
    Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Dag7003Nodes.cBPure, aliceSt, o1Pure,
    TRState.toDRState, List.mem_cons, List.not_mem_nil, or_false] at hrk
  have hmrk : (msgMut4Pure cl₁ cl₃).ratchetKey = dhPk dhsBPure := rfl
  rw [hmrk] at hgamEq hrkNe
  rcases hrk with rfl | rfl | rfl | rfl
  · rw [gamma_of_termAt cn.pk2, gamma_of_termAt cn.pk5] at hgamEq; exact absurd hgamEq (by decide)
  · rw [gamma_of_termAt cn.pk2, gamma_of_termAt cn.pk5] at hgamEq; exact absurd hgamEq (by decide)
  · rw [gamma_of_termAt cn.pk4, gamma_of_termAt cn.pk5] at hgamEq; exact absurd hgamEq (by decide)
  · rw [gamma_of_termAt cn.pk4, gamma_of_termAt cn.pk5] at hgamEq; exact absurd hgamEq (by decide)

private theorem x25519LowOrder_dhPk_m2 (sk : DY.Bytes) : x25519LowOrder (dhPk sk) = false := by
  have hv1 : ((dhPk sk).view? DY.X25519.Variant.SubF) = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.X25519.Variant.SubF
      ({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes)
  have hv2 : ((dhPk sk).view? DY.Literal.Literal.SubF) = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Literal.Literal.SubF
      ({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes)
  simp only [x25519LowOrder, DY.X25519.normalizeX25519Key, hv1,
    DY.Literal.bytesToLiteral, DY.Literal.CanMkLiteral.bytesToLiteral, hv2]

private theorem whisperTrials_of_noSkippedKeys_m2 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
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

private theorem consumeMessageKey_0_0_m2 (rk ck : DY.Bytes) (rIdx : Nat) :
    consumeMessageKey { ratchetKey := rk, chainKey := ck, index := 0, rIdx := rIdx } 0 =
      some ((kdfCk ck).2, { ratchetKey := rk, chainKey := (kdfCk ck).1, index := 1, rIdx := rIdx }) := rfl

private theorem skippedSeeds_0_0_m2 (rk ck : DY.Bytes) (rIdx : Nat) :
    skippedSeeds { ratchetKey := rk, chainKey := ck, index := 0, rIdx := rIdx } 0 = [] := rfl

private theorem trialOfState_ratchet {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {tr : ExecTrace} {msg : TRSignalMsg} (st : TRState) (c : RecvChain) (sk : DY.Bytes)
    (hmrk : msg.ratchetKey = dhPk dhsBPure) (hmcnt : msg.counter = 0)
    (hrecv : st.toDRState.recv = [c]) (hcrk : c.ratchetKey = dhPk sk)
    (hgam_ne : gamma compI7003 S g (dhPk sk) ≠ gamma compI7003 S g (dhPk dhsBPure)) :
    let ck := (createChain st.rk (dhPk dhsBPure) st.dhs).2
    (((st.toDRState.recv.filter fun c =>
        decide (gamma compI7003 S g c.ratchetKey = gamma compI7003 S g msg.ratchetKey)) ++
      match recvChainFor st.toDRState msg.ratchetKey with
      | some (c, true) => [c]
      | _ => []).map fun c =>
        (match consumeMessageKey c msg.counter with
        | none =>
          { peerIk := st.peerIk, myIk := st.myIk, extra := [c.chainKey],
            ownSalts := [], seed? := none }
        | some (seed, c') =>
          { peerIk := st.peerIk, myIk := st.myIk,
            extra := [c.chainKey, c'.chainKey] ++ skippedSeeds c msg.counter,
            ownSalts := ownKeys r tr st msg, seed? := some seed } : TrialCtx)) =
    [({ peerIk := st.peerIk, myIk := st.myIk,
        extra := [ck, (kdfCk ck).1],
        ownSalts := ownKeys r tr st msg, seed? := some (kdfCk ck).2 } : TrialCtx)] := by
  intro ck
  have hpk_ne : dhPk sk ≠ dhPk dhsBPure := fun h => hgam_ne (congrArg _ h)
  have hdec_ne : decide (gamma compI7003 S g (dhPk sk) = gamma compI7003 S g (dhPk dhsBPure)) = false :=
    decide_eq_false hgam_ne
  have hbeq_ne : (dhPk sk == dhPk dhsBPure) = false := beq_eq_false_iff_ne.mpr hpk_ne
  rw [hmrk, hmcnt]
  dsimp only [TRState.toDRState, recvChainFor, findRecvChain] at hrecv ⊢
  rw [hrecv]
  dsimp only [List.find?, List.filter]
  rw [hcrk, hdec_ne, hbeq_ne, x25519LowOrder_dhPk_m2]
  simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, List.map,
    consumeMessageKey_0_0_m2, skippedSeeds_0_0_m2, List.append_nil]
  rfl

private theorem whisperTrials_clean4_m2 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false) (cl₁ cl₃ : Nat)
    (hkpk : S.kemPk (bytesOf pqskBId) = bytesOf pqpkId) (hsem4 : SemPinned4_M2 S cl₁ cl₃) :
    let ckBB0 := (createChain (stB1Pure cl₁).rk (dhPk dhsBPure) dhsBPure).2
    ∃ ownA0 ownA1 ownB1 ownB2 : List DY.Bytes,
      whisperTrials compI7003 r S (gClean7003 true cl₁ cl₃) (t8Clean cl₁ cl₃) (msgMut4Pure cl₁ cl₃) =
        [ { peerIk := stA0Pure.peerIk, myIk := stA0Pure.myIk,
            extra := [(stB1Pure cl₁).cks, (kdfCk (stB1Pure cl₁).cks).1],
            ownSalts := ownA0, seed? := some (kdfCk (stB1Pure cl₁).cks).2 },
          { peerIk := stA0Pure.peerIk, myIk := stA0Pure.myIk,
            extra := [(stB1Pure cl₁).cks, (kdfCk (stB1Pure cl₁).cks).1],
            ownSalts := ownA1, seed? := some (kdfCk (stB1Pure cl₁).cks).2 },
          { peerIk := stA0Pure.myIk, myIk := stA0Pure.peerIk,
            extra := [ckBB0, (kdfCk ckBB0).1],
            ownSalts := ownB1, seed? := some (kdfCk ckBB0).2 },
          { peerIk := stA0Pure.myIk, myIk := stA0Pure.peerIk,
            extra := [ckBB0, (kdfCk ckBB0).1],
            ownSalts := ownB2, seed? := some (kdfCk ckBB0).2 } ] := by
  let g := gClean7003 true cl₁ cl₃
  have cn := mkCommonNodes (mode := true) (S := S) (pts := [tRnd 31 32, tRnd 47 32])
    (cl₁ := cl₁) (cl₃ := cl₃) hkpk hsem4.1
  refine ⟨ownKeys r (t8Clean cl₁ cl₃) stA0Pure (msgMut4Pure cl₁ cl₃),
    ownKeys r (t8Clean cl₁ cl₃) (stA1Pure cl₁) (msgMut4Pure cl₁ cl₃),
    ownKeys r (t8Clean cl₁ cl₃) (stB1Pure cl₁) (msgMut4Pure cl₁ cl₃),
    ownKeys r (t8Clean cl₁ cl₃) (stB2Pure cl₁ cl₃) (msgMut4Pure cl₁ cl₃), ?_⟩
  rw [whisperTrials_of_noSkippedKeys_m2 (noSkippedKeys_t8Clean cl₁ cl₃) rfl]
  have hav : availableStates r (t8Clean cl₁ cl₃) =
      [stA0Pure, stA1Pure cl₁, stB1Pure cl₁, stB2Pure cl₁ cl₃] := by
    unfold availableStates; rw [storedStates_t8Clean ha hb hopk]; rfl
  have hne25 : gamma compI7003 S g (dhPk (tRnd 10 32)) ≠ gamma compI7003 S g (dhPk dhsBPure) := by
    rw [gamma_of_termAt cn.pk2, gamma_of_termAt cn.pk5]; decide
  have hne45 : gamma compI7003 S g (dhPk (tRnd 24 32)) ≠ gamma compI7003 S g (dhPk dhsBPure) := by
    rw [gamma_of_termAt cn.pk4, gamma_of_termAt cn.pk5]; decide
  have htA0 := trialOfState_ratchet (r := r) (tr := t8Clean cl₁ cl₃) (msg := msgMut4Pure cl₁ cl₃)
    stA0Pure _ (tRnd 10 32) rfl rfl rfl rfl hne25
  have htA1 := trialOfState_ratchet (r := r) (tr := t8Clean cl₁ cl₃) (msg := msgMut4Pure cl₁ cl₃)
    (stA1Pure cl₁) _ (tRnd 10 32) rfl rfl rfl rfl hne25
  have htB1 := trialOfState_ratchet (r := r) (tr := t8Clean cl₁ cl₃) (msg := msgMut4Pure cl₁ cl₃)
    (stB1Pure cl₁) (cB'Pure cl₁) (tRnd 24 32) rfl rfl rfl rfl hne45
  have htB2 := trialOfState_ratchet (r := r) (tr := t8Clean cl₁ cl₃) (msg := msgMut4Pure cl₁ cl₃)
    (stB2Pure cl₁ cl₃) (cB'Pure cl₁) (tRnd 24 32) rfl rfl rfl rfl hne45
  have hck_ab : (createChain stA0Pure.rk (dhPk dhsBPure) (tRnd 24 32)).2 = (stB1Pure cl₁).cks := by
    rw [stB1Pure_cks_eq, createChain_comm stA0Pure.rk dhsBPure (tRnd 24 32)]
  rw [hav]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [htA0, htA1, htB1, htB2]
  simp only [List.cons_append, List.nil_append]
  have hdhs0 : stA0Pure.dhs = tRnd 24 32 := rfl
  have hdhs1 : (stA1Pure cl₁).dhs = tRnd 24 32 := rfl
  have hrk1 : (stA1Pure cl₁).rk = stA0Pure.rk := rfl
  rw [hdhs0, hdhs1, hrk1, hck_ab]
  rfl

private theorem safeMemo_trialAB {S : OpaqueSymbolSemantics} {cl₁ cl₃ : Nat}
    (cn : CommonNodes true S [tRnd 31 32, tRnd 47 32] cl₁ cl₃)
    (mn : M2Nodes S [tRnd 31 32, tRnd 47 32] cl₁ cl₃) (own : List DY.Bytes) :
    ∀ t ∈ trialTerms [DY.Spqr.zeroKey, key0Pure, key3Pure cl₁ cl₃] (msgMut4Pure cl₁ cl₃)
      { peerIk := stA0Pure.peerIk, myIk := stA0Pure.myIk,
        extra := [(stB1Pure cl₁).cks, (kdfCk (stB1Pure cl₁).cks).1],
        ownSalts := own, seed? := some (kdfCk (stB1Pure cl₁).cks).2 },
      SafeMemo true S (gClean7003 true cl₁ cl₃) [tRnd 31 32, tRnd 47 32] t := by
  intro t ht
  have hpt3 : SafeMemo true S (gClean7003 true cl₁ cl₃) [tRnd 31 32, tRnd 47 32] (tRnd 47 32) :=
    safeMemo_plaintext (List.mem_cons_of_mem _ List.mem_cons_self) (Or.inr (Or.inr rfl)) rfl
  simp only [trialTerms, List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at ht
  rcases ht with rfl | rfl |
    rfl | rfl | rfl | rfl | hdec0 |
    rfl | rfl | rfl | rfl | hdec1 |
    rfl | rfl | rfl | rfl | hdec2
  · exact safeMemo_of_termAt cn.stB1Cks
  · exact safeMemo_of_termAt mn.stB2Cks
  · exact safeMemo_of_termAt mn.zB0Ckey
  · exact safeMemo_of_termAt mn.zB0Mkey
  · exact safeMemo_of_termAt mn.zB0Iv
  · exact safeMemo_of_termAt mn.zB0Mac4
  · rw [symDec_symEnc_mem_eq hdec0]; exact hpt3
  · exact safeMemo_of_termAt mn.p1B0Ckey
  · exact safeMemo_of_termAt mn.p1B0Mkey
  · exact safeMemo_of_termAt mn.p1B0Iv
  · exact safeMemo_of_termAt mn.p1B0Mac4
  · rw [symDec_symEnc_mem_eq hdec1]; exact hpt3
  · exact safeMemo_of_termAt mn.b0Ckey
  · exact safeMemo_of_termAt mn.b0Mkey
  · exact safeMemo_of_termAt mn.b0Iv
  · exact safeMemo_of_termAt mn.p3B0Mac4
  · rw [symDec_symEnc_mem_eq hdec2]; exact hpt3

private theorem safeMemo_trialBB {S : OpaqueSymbolSemantics} {cl₁ cl₃ : Nat}
    (mn : M2Nodes S [tRnd 31 32, tRnd 47 32] cl₁ cl₃) (own : List DY.Bytes) :
    let ckBB0 := (createChain (stB1Pure cl₁).rk (dhPk dhsBPure) dhsBPure).2
    ∀ t ∈ trialTerms [DY.Spqr.zeroKey, key0Pure, key3Pure cl₁ cl₃] (msgMut4Pure cl₁ cl₃)
      { peerIk := stA0Pure.myIk, myIk := stA0Pure.peerIk,
        extra := [ckBB0, (kdfCk ckBB0).1], ownSalts := own, seed? := some (kdfCk ckBB0).2 },
      SafeMemo true S (gClean7003 true cl₁ cl₃) [tRnd 31 32, tRnd 47 32] t := by
  intro ckBB0 t ht
  have hpt3 : SafeMemo true S (gClean7003 true cl₁ cl₃) [tRnd 31 32, tRnd 47 32] (tRnd 47 32) :=
    safeMemo_plaintext (List.mem_cons_of_mem _ List.mem_cons_self) (Or.inr (Or.inr rfl)) rfl
  simp only [trialTerms, List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at ht
  rcases ht with rfl | rfl |
    rfl | rfl | rfl | rfl | hdec0 |
    rfl | rfl | rfl | rfl | hdec1 |
    rfl | rfl | rfl | rfl | hdec2
  · exact safeMemo_of_termAt mn.ckBB0
  · exact safeMemo_of_termAt mn.ckBB1
  · exact safeMemo_of_termAt mn.zBBCkey
  · exact safeMemo_of_termAt mn.zBBMkey
  · exact safeMemo_of_termAt mn.zBBIv
  · exact safeMemo_of_termAt mn.zBBMac4
  · rw [symDec_symEnc_mem_eq hdec0]; exact hpt3
  · exact safeMemo_of_termAt mn.p1BBCkey
  · exact safeMemo_of_termAt mn.p1BBMkey
  · exact safeMemo_of_termAt mn.p1BBIv
  · exact safeMemo_of_termAt mn.p1BBMac4
  · rw [symDec_symEnc_mem_eq hdec1]; exact hpt3
  · exact safeMemo_of_termAt mn.p3BBCkey
  · exact safeMemo_of_termAt mn.p3BBMkey
  · exact safeMemo_of_termAt mn.p3BBIv
  · exact safeMemo_of_termAt mn.p3BBMac4
  · rw [symDec_symEnc_mem_eq hdec2]; exact hpt3

theorem not_recvCollisionOn_clean4_m2 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false) (cl₁ cl₃ : Nat)
    (hkpk : S.kemPk (bytesOf pqskBId) = bytesOf pqpkId) (hsem4 : SemPinned4_M2 S cl₁ cl₃) :
    ¬ RecvCollisionOn compI7003 r S (gClean7003 true cl₁ cl₃)
      (t8Clean cl₁ cl₃) (visClean4 cl₁ cl₃)
      [DY.Spqr.zeroKey, key0Pure, key3Pure cl₁ cl₃] (tMut4M2Pure cl₁ cl₃) := by
  let g := gClean7003 true cl₁ cl₃
  let pts := [tRnd 31 32, tRnd 47 32]
  have cn := mkCommonNodes (mode := true) (S := S) (pts := pts) (cl₁ := cl₁) (cl₃ := cl₃) hkpk hsem4.1
  have mn := mkM2Nodes cn hsem4 List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self)
  unfold RecvCollisionOn; dsimp only
  rw [parseTrSignalMsg_tMut4M2Pure]; dsimp only
  obtain ⟨ownA0, ownA1, ownB1, ownB2, htrials⟩ := whisperTrials_clean4_m2 ha hb hopk cl₁ cl₃ hkpk hsem4
  rw [htrials]
  rintro (hmemo | hmac)
  · refine not_memoCollisionOn_of_safeMemo (mode := true) (pts := pts)
      (plaintextTerms_visClean4 cl₁ cl₃) ?_ ?_ ?_ ?_ ?_ hmemo
    · intro t ht; rw [sendTerms_visClean4] at ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · exact safeMemo_of_termAt cn.ek
      · exact safeMemo_of_termAt cn.ctKem
      · exact safeMemo_of_termAt mn.out1
      · exact safeMemo_of_termAt mn.out3
    · rw [storedStates_t8Clean ha hb hopk]
      intro ls hls; simp only [List.mem_cons, List.not_mem_nil, or_false] at hls
      rcases hls with rfl | rfl | rfl | rfl
      · exact safeMemo_stA0 cn
      · exact safeMemo_stA1 cn
      · exact safeMemo_stB1 cn
      · exact safeMemo_stB2 cn mn
    · rw [storedSecrets_t8Clean]; exact safeMemo_pqSecrets7003 cn
    · intro t ht; simp only [pts, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact safeMemo_plaintext List.mem_cons_self (Or.inr (Or.inl rfl)) rfl
      · exact safeMemo_plaintext (List.mem_cons_of_mem _ List.mem_cons_self) (Or.inr (Or.inr rfl)) rfl
    · intro t ht
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.mem_cons, List.mem_append] at ht
      rcases ht with rfl | htA0 | htA1 | htB1 | htB2
      · exact safeMemo_of_termAt mn.out4Mut
      · exact safeMemo_trialAB cn mn ownA0 t htA0
      · exact safeMemo_trialAB cn mn ownA1 t htA1
      · exact safeMemo_trialBB mn ownB1 t htB1
      · exact safeMemo_trialBB mn ownB2 t htB2
  · refine not_macTagForgery_of_msg_mismatch (mk_ref := macKey3Bytes) (msg_ref := macIn3M2Bytes)
      (by dsimp only [msgMut4Pure]; rw [gamma_of_termAt mn.mac3, pqxdh_and_mac_facts_7003.2.2.2.2.2.2.2.2.2.2.2.2.1]; decide +kernel)
      (by decide) pqxdh_and_mac_facts_7003.2.2.2.2.2.2.2.2.2.2.2.2.2 (fun ctx hctx seed _ => ?_) hmac
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hctx
    rcases hctx with rfl | rfl | rfl | rfl
    · change gamma compI7003 S g (DY.Libsignal.PQXDH.serializedIk (dhPk (tRnd 5 32))) ++
        (gamma compI7003 S g (DY.Libsignal.PQXDH.serializedIk (dhPk (tRnd 0 32))) ++
          gamma compI7003 S g (wire4MutPure cl₁ cl₃)) ≠ macIn3M2Bytes
      rw [gamma_of_termAt cn.ik1s, gamma_of_termAt cn.ik0s, gamma_of_termAt mn.wire4Mut]
      decide +kernel
    · change gamma compI7003 S g (DY.Libsignal.PQXDH.serializedIk (dhPk (tRnd 5 32))) ++
        (gamma compI7003 S g (DY.Libsignal.PQXDH.serializedIk (dhPk (tRnd 0 32))) ++
          gamma compI7003 S g (wire4MutPure cl₁ cl₃)) ≠ macIn3M2Bytes
      rw [gamma_of_termAt cn.ik1s, gamma_of_termAt cn.ik0s, gamma_of_termAt mn.wire4Mut]
      decide +kernel
    · change gamma compI7003 S g (DY.Libsignal.PQXDH.serializedIk (dhPk (tRnd 0 32))) ++
        (gamma compI7003 S g (DY.Libsignal.PQXDH.serializedIk (dhPk (tRnd 5 32))) ++
          gamma compI7003 S g (wire4MutPure cl₁ cl₃)) ≠ macIn3M2Bytes
      rw [gamma_of_termAt cn.ik0s, gamma_of_termAt cn.ik1s, gamma_of_termAt mn.wire4Mut]
      decide +kernel
    · change gamma compI7003 S g (DY.Libsignal.PQXDH.serializedIk (dhPk (tRnd 0 32))) ++
        (gamma compI7003 S g (DY.Libsignal.PQXDH.serializedIk (dhPk (tRnd 5 32))) ++
          gamma compI7003 S g (wire4MutPure cl₁ cl₃)) ≠ macIn3M2Bytes
      rw [gamma_of_termAt cn.ik0s, gamma_of_termAt cn.ik1s, gamma_of_termAt mn.wire4Mut]
      decide +kernel

theorem not_nextEventCollides_ev4_m2 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {vis : List VisEntry}
    (hf : compFitsPinned7003 setup7003 compI7003 r)
    (hex : Explains compI7003 r S g ss vis [.run ev0, .run ev1_m2, .run ev2_m2, .run ev3_m2]) :
    ¬ NextEventCollides compI7003 r S g ss vis
        [.run ev0, .run ev1_m2, .run ev2_m2, .run ev3_m2] ev4_m2 := by
  obtain ⟨ha, hb, hopk, _⟩ := setup_ids_7003 hf
  obtain ⟨_, hkpk⟩ := ghostAndSemMatchSetup_gClean7003 true 0 0 hf hex.1
  obtain ⟨cl₁, cl₃, hsem4⟩ := semPinned4_of_explains_m2_4 hf hex
  have hin : ev4_m2.input = wireWhisperTag :: body4M2Bytes := in4M2Raw_eq.trans in4M2_split_eq.1
  refine not_nextEventCollides_accepted_recv rfl hin (fun _ => ?_) (fun p hp => ?_)
  · exact not_signalMsgAcceptedOnlyViaCollision_of_no_explains
      (explains_clean4 cl₁ cl₃ hf hex hsem4)
      (not_readCollisionCli_of_no_decrypt fun m hm => by
        simp [ssClean4, m0Of, m1Clean, m2Clean, m3Clean] at hm
        rcases hm with rfl | rfl | rfl | rfl <;> rfl)
      (by rw [runTrace_ssClean4 ha hb hopk]; exact tMut4M2Pure_mem_recvReps_clean4 hkpk hsem4)
      (fun _ _ _ => not_explains_m2 hf)
      (by rw [runTrace_ssClean4 ha hb hopk, honestSaltsOf_ssClean4 ha hb hopk]
          exact not_recvCollisionOn_clean4_m2 ha hb hopk cl₁ cl₃ hkpk hsem4)
      (by rw [runTrace_ssClean4 ha hb hopk, honestSaltsOf_ssClean4 ha hb hopk]
          exact not_reselectCollisionOn_clean4_m2 ha hb hopk cl₁ cl₃ hkpk hsem4)
  · rw [← in4M2_split_eq.1, in4M2_split_eq.2.2.2.2.2] at hp
    cases hp

end Symbolic.BugInjection.Proofs.SyntheticSignalMsgCanonicalMac
