/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.RecvDagDefs
public import Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.RecvCleanExplain
public import Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.ShaMacLaws
public import Symbolic.Proofs.Tests.CliNonvacuity.RecvNoCollision
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Tests.CliNonvacuity.Defs
import Symbolic.Proofs.Tests.Shared.Composed.PrunedSpecLemmas
import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc
import Symbolic.Proofs.Swarm.CREF.Initiate.InitOk35Pure
import DY.Bytes.Basic
import DY.Trace.Basic
import DY.Actions.Network
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.EquationalTheory.Concat
import Symbolic.DYBridge.DY.EquationalTheory.DiffieHellman
import Symbolic.DYBridge.DY.EquationalTheory.Literal
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Actions.Network

/-!
# Receiver Collision Discharger for `DhRatchetNoSendStepCli` Call 2 (`RecvMemoBobStart.lean`)

1. Rewrites `HonestSession.o1`, `HonestSession.stA0`, `HonestSession.key0`, and `encWire`/`encMac`/`encOut`
   to pure trace-free `DY.Bytes` terms and certifies `TermAt S (gClean cl) [HonestSession.m0]` on all
   181 DAG nodes in `RecvDagData`, universally quantified over `S : OpaqueSymbolSemantics` under the
   three prefix-pinned equations (`S.kemPk`, `S.chainKey`, `S.sendMsg`).
2. Instantiates `computeMac_pins_salt_and_seed` against a reference semantics `S₀` to deduce the
   `S.chainKey` pin from any outer `Explains` witness of `[.run dhEv0, .run dhEv1]`.
3. Discharges `¬ BobSessionStartCollidesOrImplicitRejectsOn`, `xClean n ∈ preKeyRepresentationsOn`,
   `Explains dhRatchetI0 r S (gClean n) (ssClean2 n) (visClean2 n) [.run dhEv0, .run dhEv1]`, and
   `not_nextEventCollides_ev2`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.RecvMemoBobStart

unseal DY.Bytes

open scoped DY.Libsignal.Composed
open DY (ExecTrace)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (CliEvent)
open DY.Libsignal.PQXDH.Refinement (wirePrekeyTag preKeyBundleByteLength)
open DY.Libsignal.TripleRatchet
  (TRState kdfCk trMsgKeys computeMac trHonestWireMsg parseTrSignalMsg spqrA2B)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup ProtocolSetupWF OpaqueSymbolSemantics Ghost Step VisEntry BundlePreKeyIds
   gamma gamma' spqrKeyBytes ofByteArray ecKey kyberKey pubBytes secretBytes slice preKeyWire
   randTerm setupTrace setupPublic received rngEntry kyberCoinEntries aliceDraws aliceVis
   newRandoms encDraws nextBundleIds inputKind runWrapped stepView runTrace lastSent
   GhostAndSemMatchSetup BytesMatchEntry DrawsMatch OutputsMatch ReadsFaithfully PathFaithfulAt
   RunMatches MatchesEventsAt Explains
   getMessageSentAt_attackerKnows preKeyRepresentationsOn honestSaltsOf
   BobSessionStartCollidesOrImplicitRejectsOn)
open DY.Libsignal.Composed.Refinement.Cli (NextEventCollides)
open Symbolic.BugInjection (cliCompShape)
open Symbolic.BugInjection.Proofs.Common443.Census443Defs
  (encPreSaltTr encSalt encWire encMac encOut encSt encNextTr)
open Symbolic.BugInjection.Proofs.Common443.CompRFaithfulInner
  (encParsedMsg parseTrSignalMsg_encOut faithfulInner_of_gamma_encOut_generic)
open Symbolic.Swarm.CREF
  (setupPublic_4 setupTrace_at?_14 setupTrace_at?_15 setupTrace_at?_20 setupTrace_at?_21)
open Symbolic.Proofs.Tests.Shared.Composed
open Symbolic.Proofs.Tests.CliNonvacuity.Defs (matchesEvents_run1)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeSteps
  (m0Of setupTrace_false_eq m0_ok_false m0_next_false vis_m0_false visStep visEncStep)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
  (length_append_entry_eq getMessageSentAt_eq_at?)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionDag
  (recvTailTerm stateAnchorPair trStateProxyRoots)
open Symbolic.Proofs.Tests.CliNonvacuity.Table.MkTerm (tCat tSSendM)
open Symbolic.Proofs.Tests.CliNonvacuity.RecvNoCollisionAux
  (not_knownBaseKeyOn_of_no_recv)
open Symbolic.Proofs.Tests.CliNonvacuity.RecvNoCollision
  (not_preKeyStartCollidesOrRejects_of_clean not_nextEventCollides_accepted_prekey)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compTag4)
open Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.DefsI0
  (dhRatchetI0 dhAesPt0 cliCompFitsPinned)
open Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.NoPrefixExplains
  (dhEv0 dhEv1 dhEv2)
open Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.ShaMacLaws
  (computeMac_pins_salt_and_seed not_macTagForgeryOrCollision_of_honest_mac)
open Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.RecvDagData
open Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.RecvMemoCombinators
open Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.RecvMemoTermAt
open Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.RecvPeelPins
open Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.RecvCleanExplain

/-! ## 0. Trace-Free Forms of `HonestSession` Handshake & Encrypt Terms -/

def o1Pure : DY.Libsignal.PQXDH.AliceHandshakeOut :=
  let ek := randTerm 22 32
  let e := randTerm 23 32
  let ikBPk := DY.DiffieHellman.dhPk HonestSession.ikB
  let spkPk := DY.DiffieHellman.dhPk HonestSession.spkB
  let pqPk := DY.PQKem.kemPk HonestSession.pqskB
  { ikA := DY.DiffieHellman.dhPk HonestSession.ikA, ikB := ikBPk,
    spk := spkPk, pqpk := pqPk, opk := none, ek := DY.DiffieHellman.dhPk ek,
    ct := (DY.Libsignal.PQXDH.aliceAgreement HonestSession.ikA ek ikBPk spkPk pqPk none e).1,
    keys := (DY.Libsignal.PQXDH.aliceAgreement HonestSession.ikA ek ikBPk spkPk pqPk none e).2 }

theorem o1_eq : HonestSession.o1 = o1Pure := by
  unfold HonestSession.o1 o1Pure
    Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOut
    Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOut
    Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt
    Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.rnd
    randTerm
  rw [HonestSession.t4_length]

theorem keys1_eq : HonestSession.keys1 = o1Pure.keys := by
  unfold HonestSession.keys1; rw [o1_eq]

def stA0Pure : TRState :=
  Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceSt "bob" o1Pure HonestSession.dhsA

theorem stA0_eq : HonestSession.stA0 = stA0Pure := by
  unfold HonestSession.stA0 stA0Pure; rw [o1_eq]

def key0Pure : DY.Bytes :=
  DY.Spqr.spqrChainKey o1Pure.keys.pqr spqrA2B (DY.Literal.literalToBytes ⟨#[1, 0, 0, 0]⟩)

theorem key0_eq : HonestSession.key0 = key0Pure := by
  unfold HonestSession.key0 key0Pure
  rw [stA0_eq]
  exact Symbolic.Proofs.Tests.Shared.Composed.PrunedSpecLemmas.spqrSend_key_init
    o1Pure.keys.pqr spqrA2B HonestSession.coins0

theorem encSalt_clean_eq (cl : Nat) :
    encSalt HonestSession.t5 HonestSession.stA0 cl 33 = key0Pure := by
  have hs : encSalt HonestSession.t5 HonestSession.stA0 cl (HonestSession.t5.length + 2) =
      (DY.Spqr.spqrSend HonestSession.stA0.spqr (randTerm (HonestSession.t5.length + 1) cl)).2.1 :=
    Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc.encSalt_self
      HonestSession.t5 HonestSession.stA0 cl
  rw [HonestSession.t5_length] at hs
  rw [hs, stA0_eq]
  exact Symbolic.Proofs.Tests.Shared.Composed.PrunedSpecLemmas.spqrSend_key_init
    o1Pure.keys.pqr spqrA2B (randTerm 32 cl)

def pqMsgPure (cl : Nat) : DY.Bytes :=
  (DY.Spqr.spqrSend stA0Pure.spqr (randTerm 32 cl)).2.2

def encWirePure (cl : Nat) : DY.Bytes :=
  let seed := (kdfCk stA0Pure.cks).2
  let keys := trMsgKeys key0Pure seed
  trHonestWireMsg (DY.DiffieHellman.dhPk stA0Pure.dhs) 0 0
    (DY.SymEnc.symEnc keys.cipherKey keys.iv HonestSession.m0) (pqMsgPure cl)

def encMacPure (cl : Nat) : DY.Bytes :=
  let seed := (kdfCk stA0Pure.cks).2
  let keys := trMsgKeys key0Pure seed
  computeMac keys.macKey stA0Pure.myIk stA0Pure.peerIk (encWirePure cl)

def encOutPure (cl : Nat) : DY.Bytes :=
  DY.Concat.concat (encWirePure cl) (encMacPure cl)

theorem encWire_clean_eq (cl : Nat) :
    encWire HonestSession.t5 HonestSession.stA0 cl 33 = encWirePure cl := by
  unfold encWire encWirePure pqMsgPure HonestSession.m0 Symbolic.Proofs.Tests.Shared.Composed.Runs.rnd
  rw [encSalt_clean_eq, HonestSession.t5_length, stA0_eq]
  rfl

theorem encMac_clean_eq (cl : Nat) :
    encMac HonestSession.t5 HonestSession.stA0 cl 33 = encMacPure cl := by
  unfold encMac encMacPure
  rw [encSalt_clean_eq, encWire_clean_eq, stA0_eq]

theorem encOut_clean_eq (cl : Nat) :
    encOut HonestSession.t5 HonestSession.stA0 cl 33 = encOutPure cl := by
  unfold encOut encOutPure
  rw [encWire_clean_eq, encMac_clean_eq]

/-! ## 1. Compositional `TermAt` & `SafeMemo` Proofs Over `RecvDagData` -/

abbrev pts0 : List DY.Bytes := [HonestSession.m0]

private theorem ofByteArray_zero32_pub :
    ofByteArray { data := Array.replicate 32 0 } = bytesOf zero32Id := by decide +kernel

private theorem ofByteArray_ff32_pub :
    ofByteArray { data := Array.replicate 32 255 } = bytesOf ff32Id := by decide +kernel

private theorem ta_b00 (S : OpaqueSymbolSemantics) (cl : Nat) :
    TermAt S (gClean cl) pts0 spqrA2B b00Id := termAt_litByteArray (bs := [0#8]) rfl
private theorem ta_b01 (S : OpaqueSymbolSemantics) (cl : Nat) :
    TermAt S (gClean cl) pts0 (DY.Libsignal.TripleRatchet.litByte 1) b01Id :=
  termAt_litByteArray (bs := [1#8]) rfl
private theorem ta_b02 (S : OpaqueSymbolSemantics) (cl : Nat) :
    TermAt S (gClean cl) pts0 (DY.Libsignal.TripleRatchet.litByte 2) b02Id :=
  termAt_litByteArray (bs := [2#8]) rfl
private theorem ta_b03 (S : OpaqueSymbolSemantics) (cl : Nat) :
    TermAt S (gClean cl) pts0 (DY.Libsignal.TripleRatchet.litByte 3) b03Id :=
  termAt_litByteArray (bs := [3#8]) rfl
private theorem ta_b05 (S : OpaqueSymbolSemantics) (cl : Nat) :
    TermAt S (gClean cl) pts0 (DY.Literal.literalToBytes ⟨#[5]⟩) b05Id :=
  termAt_litByteArray (bs := [5#8]) rfl
private theorem ta_u32_1 (S : OpaqueSymbolSemantics) (cl : Nat) :
    TermAt S (gClean cl) pts0 (DY.Literal.literalToBytes ⟨#[1, 0, 0, 0]⟩) u32_1Id :=
  termAt_litByteArray (bs := [1#8, 0#8, 0#8, 0#8]) rfl
private theorem ta_ff32 (S : OpaqueSymbolSemantics) (cl : Nat) :
    TermAt S (gClean cl) pts0 DY.Libsignal.PQXDH.discontinuity ff32Id :=
  termAt_litByteArray ofByteArray_ff32_pub
private theorem ta_zeroSalt (S : OpaqueSymbolSemantics) (cl : Nat) :
    TermAt S (gClean cl) pts0 DY.Libsignal.TripleRatchet.zeroSalt zero32Id :=
  termAt_litByteArray ofByteArray_zero32_pub
private theorem ta_zeroKey (S : OpaqueSymbolSemantics) (cl : Nat) :
    TermAt S (gClean cl) pts0 DY.Spqr.zeroKey zero32Id :=
  termAt_litByteArray ofByteArray_zero32_pub
private theorem ta_wrLbl (S : OpaqueSymbolSemantics) (cl : Nat) :
    TermAt S (gClean cl) pts0 (DY.Libsignal.TripleRatchet.lit "WhisperRatchet") wrLblId :=
  termAt_litByteArray ofByteArray_whisperRatchet
private theorem ta_wmkLbl (S : OpaqueSymbolSemantics) (cl : Nat) :
    TermAt S (gClean cl) pts0 (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys") wmkLblId :=
  termAt_litByteArray ofByteArray_whisperMsgKeys
private theorem ta_pqxdhLbl (S : OpaqueSymbolSemantics) (cl : Nat) :
    TermAt S (gClean cl) pts0 DY.Libsignal.PQXDH.pqxdhLabel pqxdhLblId :=
  termAt_litByteArray ofByteArray_pqxdhLabel

private theorem ta_wmkInfo1 (S : OpaqueSymbolSemantics) (cl : Nat) :
    TermAt S (gClean cl) pts0
      (tCat (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys")
        (DY.Libsignal.TripleRatchet.litByte 1)) wmkInfo1Id :=
  termAt_concat (by decide) (by decide) (ta_wmkLbl S cl) (ta_b01 S cl)

private theorem ta_wmkInfo2 (S : OpaqueSymbolSemantics) (cl : Nat) :
    TermAt S (gClean cl) pts0
      (tCat (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys")
        (DY.Libsignal.TripleRatchet.litByte 2)) wmkInfo2Id :=
  termAt_concat (by decide) (by decide) (ta_wmkLbl S cl) (ta_b02 S cl)

private theorem ta_wmkInfo3 (S : OpaqueSymbolSemantics) (cl : Nat) :
    TermAt S (gClean cl) pts0
      (tCat (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys")
        (DY.Libsignal.TripleRatchet.litByte 3)) wmkInfo3Id :=
  termAt_concat (by decide) (by decide) (ta_wmkLbl S cl) (ta_b03 S cl)

private theorem ta_wrInfo1 (S : OpaqueSymbolSemantics) (cl : Nat) :
    TermAt S (gClean cl) pts0
      (tCat (DY.Libsignal.TripleRatchet.lit "WhisperRatchet")
        (DY.Libsignal.TripleRatchet.litByte 1)) wrInfo1Id :=
  termAt_concat (by decide) (by decide) (ta_wrLbl S cl) (ta_b01 S cl)

private theorem ta_wrInfo2 (S : OpaqueSymbolSemantics) (cl : Nat) :
    TermAt S (gClean cl) pts0
      (tCat (DY.Libsignal.TripleRatchet.lit "WhisperRatchet")
        (DY.Libsignal.TripleRatchet.litByte 2)) wrInfo2Id :=
  termAt_concat (by decide) (by decide) (ta_wrLbl S cl) (ta_b02 S cl)

private theorem ta_pqxdhInfo1 (S : OpaqueSymbolSemantics) (cl : Nat) :
    TermAt S (gClean cl) pts0
      (tCat DY.Libsignal.PQXDH.pqxdhLabel (DY.Libsignal.TripleRatchet.litByte 1)) pqxdhInfo1Id :=
  termAt_concat (by decide) (by decide) (ta_pqxdhLbl S cl) (ta_b01 S cl)

private theorem ta_pqxdhInfo2 (S : OpaqueSymbolSemantics) (cl : Nat) :
    TermAt S (gClean cl) pts0
      (tCat DY.Libsignal.PQXDH.pqxdhLabel (DY.Libsignal.TripleRatchet.litByte 2)) pqxdhInfo2Id :=
  termAt_concat (by decide) (by decide) (ta_pqxdhLbl S cl) (ta_b02 S cl)

private theorem ta_pqxdhInfo3 (S : OpaqueSymbolSemantics) (cl : Nat) :
    TermAt S (gClean cl) pts0
      (tCat DY.Libsignal.PQXDH.pqxdhLabel (DY.Libsignal.TripleRatchet.litByte 3)) pqxdhInfo3Id :=
  termAt_concat (by decide) (by decide) (ta_pqxdhLbl S cl) (ta_b03 S cl)

private theorem ta_ikA (S : OpaqueSymbolSemantics) (cl : Nat) :
    TermAt S (gClean cl) pts0 HonestSession.ikA ikAId :=
  termAt_rand (by decide) (by decide) rfl

private theorem ta_ikB (S : OpaqueSymbolSemantics) (cl : Nat) :
    TermAt S (gClean cl) pts0 HonestSession.ikB ikBId :=
  termAt_rand (by decide) (by decide) rfl

private theorem ta_spkB (S : OpaqueSymbolSemantics) (cl : Nat) :
    TermAt S (gClean cl) pts0 HonestSession.spkB spkBId :=
  termAt_rand (by decide) (by decide) rfl

private theorem ta_pqskB (S : OpaqueSymbolSemantics) (cl : Nat) :
    TermAt S (gClean cl) pts0 HonestSession.pqskB pqskBId :=
  termAt_rand (by decide) (by decide) rfl

private theorem ta_pk0 (S : OpaqueSymbolSemantics) (cl : Nat) :
    TermAt S (gClean cl) pts0 (DY.DiffieHellman.dhPk HonestSession.ikA) pk0Id :=
  termAt_dhPk (by decide) (by decide) (ta_ikA S cl)

private theorem ta_pk1 (S : OpaqueSymbolSemantics) (cl : Nat) :
    TermAt S (gClean cl) pts0 (DY.DiffieHellman.dhPk HonestSession.ikB) pk1Id :=
  termAt_dhPk (by decide) (by decide) (ta_ikB S cl)

private theorem ta_pk2 (S : OpaqueSymbolSemantics) (cl : Nat) :
    TermAt S (gClean cl) pts0 (DY.DiffieHellman.dhPk HonestSession.spkB) pk2Id :=
  termAt_dhPk (by decide) (by decide) (ta_spkB S cl)

private theorem ta_ik0s (S : OpaqueSymbolSemantics) (cl : Nat) :
    TermAt S (gClean cl) pts0
      (DY.Libsignal.PQXDH.serializedIk (DY.DiffieHellman.dhPk HonestSession.ikA)) ik0sId :=
  termAt_concat (by decide) (by decide) (ta_b05 S cl) (ta_pk0 S cl)

private theorem ta_ik1s (S : OpaqueSymbolSemantics) (cl : Nat) :
    TermAt S (gClean cl) pts0
      (DY.Libsignal.PQXDH.serializedIk (DY.DiffieHellman.dhPk HonestSession.ikB)) ik1sId :=
  termAt_concat (by decide) (by decide) (ta_b05 S cl) (ta_pk1 S cl)

private theorem ta_r22 (S : OpaqueSymbolSemantics) (cl : Nat) :
    TermAt S (gClean cl) pts0 (randTerm 22 32) r22Id :=
  termAt_rand (by decide) (by decide) rfl

private theorem ta_r23 (S : OpaqueSymbolSemantics) (cl : Nat) :
    TermAt S (gClean cl) pts0 (randTerm 23 32) r23Id :=
  termAt_rand (by decide) (by decide) rfl

private theorem ta_dhsA (S : OpaqueSymbolSemantics) (cl : Nat) :
    TermAt S (gClean cl) pts0 HonestSession.dhsA dhsAId :=
  termAt_rand (by decide) (by decide) rfl

private theorem ta_ek (S : OpaqueSymbolSemantics) (cl : Nat) :
    TermAt S (gClean cl) pts0 o1Pure.ek ekId :=
  termAt_dhPk (by decide) (by decide) (ta_r22 S cl)

private theorem ta_pk4 (S : OpaqueSymbolSemantics) (cl : Nat) :
    TermAt S (gClean cl) pts0 (DY.DiffieHellman.dhPk HonestSession.dhsA) pk4Id :=
  termAt_dhPk (by decide) (by decide) (ta_dhsA S cl)

private theorem ta_pqpk {S : OpaqueSymbolSemantics} (cl : Nat)
    (hpqpk : S.kemPk (bytesOf pqskBId) = bytesOf pqpkId) :
    TermAt S (gClean cl) pts0 (DY.PQKem.kemPk HonestSession.pqskB) pqpkId := by
  have hsk := ta_pqskB S cl
  obtain ⟨hsh, hsm⟩ := opaque_kemPk hsk.2.2.2
  have hgam : gamma dhRatchetI0 S (gClean cl) (DY.PQKem.kemPk HonestSession.pqskB) =
      bytesOf pqpkId := by
    unfold gamma DY.PQKem.kemPk
    show ((({ sk := HonestSession.pqskB } : DY.PQKem.Pk.SubF DY.Bytes).pack).rec
      (DY.Libsignal.Composed.Refinement.concretizeAll dhRatchetI0 S (gClean cl))).bytes = _
    rw [DY.Bytes.rec_eq (DY.Libsignal.Composed.Refinement.concretizeKemPk S)
      (DY.Libsignal.Composed.Refinement.concretizeAll dhRatchetI0 S (gClean cl))]
    dsimp only [DY.Libsignal.Composed.Refinement.concretizeKemPk,
      DY.Libsignal.Composed.Refinement.opaqueNode]
    change S.kemPk (gamma' dhRatchetI0 S (gClean cl) HonestSession.pqskB).bytes = bytesOf pqpkId
    rw [hsk.2.1, hpqpk]
  exact termAt_of_opaque_pinned (bs := bytesOf pqpkId) (by decide +kernel) (by decide) hsh hgam hsm

private theorem ta_ctKem {S : OpaqueSymbolSemantics} (cl : Nat)
    (hpqpk : S.kemPk (bytesOf pqskBId) = bytesOf pqpkId) :
    TermAt S (gClean cl) pts0 o1Pure.ct ctKemId :=
  termAt_kemEncap (by decide) (by decide) (ta_pqpk cl hpqpk) (ta_r23 S cl)

private theorem ta_ssKem {S : OpaqueSymbolSemantics} (cl : Nat)
    (hpqpk : S.kemPk (bytesOf pqskBId) = bytesOf pqpkId) :
    TermAt S (gClean cl) pts0
      (DY.PQKem.kemEncap (DY.PQKem.kemPk HonestSession.pqskB) (randTerm 23 32)).2 ssKemId :=
  termAt_kemSS (by decide) (by decide) (ta_pqpk cl hpqpk) (ta_r23 S cl)

private theorem normalizeX25519Key_dhPk (a : DY.Bytes) :
    DY.X25519.normalizeX25519Key (DY.DiffieHellman.dhPk a) = DY.DiffieHellman.dhPk a := by
  dsimp only [DY.X25519.normalizeX25519Key, DY.DiffieHellman.dhPk, DY.DiffieHellman.CanDH.dhPk]
  rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.X25519.Variant.SubF]

private theorem agree_dhPk (a b : DY.Bytes) :
    DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk a) b =
      DY.DiffieHellman.dh (DY.DiffieHellman.dhPk a) b := by
  unfold DY.Libsignal.PQXDH.agree; rw [normalizeX25519Key_dhPk]

private theorem ta_dh02 (S : OpaqueSymbolSemantics) (cl : Nat) :
    TermAt S (gClean cl) pts0
      (DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk HonestSession.spkB) HonestSession.ikA)
      dh02Id :=
  termAt_congr (agree_dhPk _ _)
    (termAt_dh_dhPk (by decide) (by decide) (by decide +kernel) shapeOf_rand shapeOf_rand
      (ta_spkB S cl) (ta_pk2 S cl) (ta_ikA S cl) (ta_pk0 S cl))

private theorem ta_dh13 (S : OpaqueSymbolSemantics) (cl : Nat) :
    TermAt S (gClean cl) pts0
      (DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk HonestSession.ikB) (randTerm 22 32))
      dh13Id :=
  termAt_congr ((agree_dhPk _ _).trans (DY.DiffieHellman.dh_commutes _ _))
    (termAt_dh_dhPk (by decide) (by decide) (by decide +kernel) shapeOf_rand shapeOf_rand
      (ta_r22 S cl) (ta_ek S cl) (ta_ikB S cl) (ta_pk1 S cl))

private theorem ta_dh23 (S : OpaqueSymbolSemantics) (cl : Nat) :
    TermAt S (gClean cl) pts0
      (DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk HonestSession.spkB) (randTerm 22 32))
      dh23Id :=
  termAt_congr ((agree_dhPk _ _).trans (DY.DiffieHellman.dh_commutes _ _))
    (termAt_dh_dhPk (by decide) (by decide) (by decide +kernel) shapeOf_rand shapeOf_rand
      (ta_r22 S cl) (ta_ek S cl) (ta_spkB S cl) (ta_pk2 S cl))

private theorem ta_prkPq {S : OpaqueSymbolSemantics} (cl : Nat)
    (hpqpk : S.kemPk (bytesOf pqskBId) = bytesOf pqpkId) :
    TermAt S (gClean cl) pts0
      (DY.Libsignal.TripleRatchet.hmac DY.Libsignal.TripleRatchet.zeroSalt
        (DY.Libsignal.PQXDH.pqxdhIkm
          (DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk HonestSession.spkB) HonestSession.ikA)
          (DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk HonestSession.ikB) (randTerm 22 32))
          (DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk HonestSession.spkB) (randTerm 22 32))
          none
          (DY.PQKem.kemEncap (DY.PQKem.kemPk HonestSession.pqskB) (randTerm 23 32)).2)) prkPqId := by
  have hc3 := termAt_concat (id := c3Id) (by decide) (by decide) (ta_dh23 S cl) (ta_ssKem cl hpqpk)
  have hc2 := termAt_concat (id := c2Id) (by decide) (by decide) (ta_dh13 S cl) hc3
  have hc1 := termAt_concat (id := c1Id) (by decide) (by decide) (ta_dh02 S cl) hc2
  have hikm := termAt_concat (id := ikmId) (by decide) (by decide) (ta_ff32 S cl) hc1
  exact termAt_kdf (by decide) (by decide) (ta_zeroSalt S cl) hikm

private theorem ta_keys_rk {S : OpaqueSymbolSemantics} (cl : Nat)
    (hpqpk : S.kemPk (bytesOf pqskBId) = bytesOf pqpkId) :
    TermAt S (gClean cl) pts0 o1Pure.keys.rk rkInitId :=
  termAt_kdf (by decide) (by decide) (ta_prkPq cl hpqpk) (ta_pqxdhInfo1 S cl)

private theorem ta_keys_ck {S : OpaqueSymbolSemantics} (cl : Nat)
    (hpqpk : S.kemPk (bytesOf pqskBId) = bytesOf pqpkId) :
    TermAt S (gClean cl) pts0 o1Pure.keys.ck ckInitId :=
  termAt_kdf (by decide) (by decide) (ta_prkPq cl hpqpk)
    (termAt_concat (id := pqi2CId) (by decide) (by decide)
      (ta_keys_rk cl hpqpk) (ta_pqxdhInfo2 S cl))

private theorem ta_keys_pqr {S : OpaqueSymbolSemantics} (cl : Nat)
    (hpqpk : S.kemPk (bytesOf pqskBId) = bytesOf pqpkId) :
    TermAt S (gClean cl) pts0 o1Pure.keys.pqr pqrInitId :=
  termAt_kdf (by decide) (by decide) (ta_prkPq cl hpqpk)
    (termAt_concat (id := pqi3CId) (by decide) (by decide)
      (ta_keys_ck cl hpqpk) (ta_pqxdhInfo3 S cl))

private theorem ta_sid {S : OpaqueSymbolSemantics} (cl : Nat)
    (hpqpk : S.kemPk (bytesOf pqskBId) = bytesOf pqpkId) :
    TermAt S (gClean cl) pts0 stA0Pure.sid sidId :=
  termAt_concat (by decide) (by decide) (ta_pk4 S cl) (ta_keys_rk cl hpqpk)

private theorem ta_dh24 (S : OpaqueSymbolSemantics) (cl : Nat) :
    TermAt S (gClean cl) pts0
      (DY.DiffieHellman.dh (DY.DiffieHellman.dhPk HonestSession.spkB) HonestSession.dhsA) dh24Id :=
  termAt_congr (DY.DiffieHellman.dh_commutes _ _)
    (termAt_dh_dhPk (by decide) (by decide) (by decide +kernel) shapeOf_rand shapeOf_rand
      (ta_dhsA S cl) (ta_pk4 S cl) (ta_spkB S cl) (ta_pk2 S cl))

private theorem ta_prkA {S : OpaqueSymbolSemantics} (cl : Nat)
    (hpqpk : S.kemPk (bytesOf pqskBId) = bytesOf pqpkId) :
    TermAt S (gClean cl) pts0
      (DY.Libsignal.TripleRatchet.hmac o1Pure.keys.rk
        (DY.DiffieHellman.dh (DY.DiffieHellman.dhPk HonestSession.spkB) HonestSession.dhsA)) prkAId :=
  termAt_kdf (by decide) (by decide) (ta_keys_rk cl hpqpk) (ta_dh24 S cl)

private theorem ta_stA0_rk {S : OpaqueSymbolSemantics} (cl : Nat)
    (hpqpk : S.kemPk (bytesOf pqskBId) = bytesOf pqpkId) :
    TermAt S (gClean cl) pts0 stA0Pure.rk stA0RkId := by
  unfold stA0Pure Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceSt
    DY.Libsignal.TripleRatchet.createChain DY.Libsignal.TripleRatchet.kdfRk DY.X25519.agree
  dsimp only [o1Pure]
  rw [normalizeX25519Key_dhPk]
  exact termAt_kdf (by decide) (by decide) (ta_prkA cl hpqpk) (ta_wrInfo1 S cl)

private theorem ta_stA0_cks {S : OpaqueSymbolSemantics} (cl : Nat)
    (hpqpk : S.kemPk (bytesOf pqskBId) = bytesOf pqpkId) :
    TermAt S (gClean cl) pts0 stA0Pure.cks stA0CksId := by
  have hrk := ta_stA0_rk cl hpqpk
  unfold stA0Pure Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceSt
    DY.Libsignal.TripleRatchet.createChain DY.Libsignal.TripleRatchet.kdfRk DY.X25519.agree at hrk ⊢
  dsimp only [o1Pure] at hrk ⊢
  rw [normalizeX25519Key_dhPk] at hrk ⊢
  exact termAt_kdf (by decide) (by decide) (ta_prkA cl hpqpk)
    (termAt_concat (id := wri2CId) (by decide) (by decide) hrk (ta_wrInfo2 S cl))

private theorem ta_seed0 {S : OpaqueSymbolSemantics} (cl : Nat)
    (hpqpk : S.kemPk (bytesOf pqskBId) = bytesOf pqpkId) :
    TermAt S (gClean cl) pts0 (kdfCk stA0Pure.cks).2 seed0Id :=
  termAt_kdf (by decide) (by decide) (ta_stA0_cks cl hpqpk) (ta_b01 S cl)

private theorem ta_nck0 {S : OpaqueSymbolSemantics} (cl : Nat)
    (hpqpk : S.kemPk (bytesOf pqskBId) = bytesOf pqpkId) :
    TermAt S (gClean cl) pts0 (kdfCk stA0Pure.cks).1 nck0Id :=
  termAt_kdf (by decide) (by decide) (ta_stA0_cks cl hpqpk) (ta_b02 S cl)

private theorem coin_dag_spec :
    ((List.range 65).all fun cl =>
      decide (cl = 0) ||
        ((opOf (91 + cl) == .rand 32 cl) &&
         decide (91 + cl < dagSize) &&
         (bytesOf (91 + cl) == dhEv1CoinsFast.take cl))) = true := by
  decide +kernel

private theorem coins32_safe_and_gamma (S : OpaqueSymbolSemantics) {cl : Nat} (hcl : cl ≤ 64) :
    SafeMemo S (gClean cl) pts0 (randTerm 32 cl) ∧
    gamma dhRatchetI0 S (gClean cl) (randTerm 32 cl) = dhEv1CoinsFast.take cl := by
  by_cases h0 : cl = 0
  · subst h0
    have hg' : gamma' dhRatchetI0 S (gClean 0) (randTerm 32 0) =
        { bytes := [], shape := DY.Libsignal.Composed.Refinement.litOf [], memo := [] } := by
      unfold gamma'
      change (({ timestamp := 32, size := 0 } : DY.Random.Random DY.Bytes).pack).rec
        (DY.Libsignal.Composed.Refinement.concretizeAll dhRatchetI0 S (gClean 0)) = _
      rw [DY.Bytes.rec_eq (DY.Libsignal.Composed.Refinement.concretizeRandom (gClean 0))
        (DY.Libsignal.Composed.Refinement.concretizeAll dhRatchetI0 S (gClean 0))]
      simp [DY.Libsignal.Composed.Refinement.concretizeRandom]
    refine ⟨(fun x hx => by rw [hg'] at hx; cases hx), ?_⟩
    unfold gamma; rw [hg']; simp
  · have hmem := List.all_eq_true.mp coin_dag_spec cl (List.mem_range.mpr (by omega))
    simp only [h0, decide_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at hmem
    obtain ⟨⟨hop, hid⟩, hb⟩ := hmem
    have hg : (gClean cl).σ 32 cl = bytesOf (91 + cl) := by
      unfold gClean
      have hbne : (cl != 0) = true := bne_iff_ne.mpr h0
      have hble : decide (cl ≤ 64) = true := decide_eq_true hcl
      simp [hbne, hble, hb]
    have hta := termAt_rand (S := S) (g := gClean cl) (pts := pts0) hop hid hg
    exact ⟨hta.2.2.2, hta.2.1.trans hb⟩

private theorem ta_key0 {S : OpaqueSymbolSemantics} (cl : Nat)
    (hpqpk : S.kemPk (bytesOf pqskBId) = bytesOf pqpkId)
    (hck : spqrKeyBytes (S.chainKey (bytesOf pqrInitId) [0#8] [1#8, 0#8, 0#8, 0#8]) =
      bytesOf pqKey0Id) :
    TermAt S (gClean cl) pts0 key0Pure pqKey0Id := by
  have hpqr := ta_keys_pqr cl hpqpk
  have hp := ta_b00 S cl
  have hidx := ta_u32_1 S cl
  obtain ⟨hsh, hsm, _⟩ := opaque_spqrChainKey hpqr.2.2.2 hp.2.2.2 hidx.2.2.2
  have hgam : gamma dhRatchetI0 S (gClean cl) key0Pure = bytesOf pqKey0Id := by
    unfold gamma key0Pure DY.Spqr.spqrChainKey
    show ((({ authKey := o1Pure.keys.pqr, params := spqrA2B,
              idx := DY.Literal.literalToBytes ⟨#[1, 0, 0, 0]⟩ } :
        DY.Spqr.ChainKey.SubF DY.Bytes).pack).rec
      (DY.Libsignal.Composed.Refinement.concretizeAll dhRatchetI0 S (gClean cl))).bytes = _
    rw [DY.Bytes.rec_eq (DY.Libsignal.Composed.Refinement.concretizeSpqrChainKey S)
      (DY.Libsignal.Composed.Refinement.concretizeAll dhRatchetI0 S (gClean cl))]
    dsimp only [DY.Libsignal.Composed.Refinement.concretizeSpqrChainKey,
      DY.Libsignal.Composed.Refinement.spqrKeyNode,
      DY.Libsignal.Composed.Refinement.opaqueNode]
    change spqrKeyBytes (S.chainKey
      (gamma' dhRatchetI0 S (gClean cl) o1Pure.keys.pqr).bytes
      (gamma' dhRatchetI0 S (gClean cl) spqrA2B).bytes
      (gamma' dhRatchetI0 S (gClean cl) (DY.Literal.literalToBytes ⟨#[1, 0, 0, 0]⟩)).bytes) =
      bytesOf pqKey0Id
    rw [hpqr.2.1, hp.2.1, hidx.2.1]
    have hb0 : bytesOf b00Id = [0#8] := by decide +kernel
    have hu1 : bytesOf u32_1Id = [1#8, 0#8, 0#8, 0#8] := by decide +kernel
    rw [hb0, hu1, hck]
  exact termAt_of_opaque_pinned (bs := bytesOf pqKey0Id) (by decide +kernel) (by decide) hsh hgam hsm

private theorem ta_pqMsg0 {S : OpaqueSymbolSemantics} {cl : Nat} (hcl : cl ≤ 64)
    (hpqpk : S.kemPk (bytesOf pqskBId) = bytesOf pqpkId)
    (hpqm : S.sendMsg (S.init (bytesOf pqrInitId) [0#8]) (dhEv1CoinsFast.take cl) =
      bytesOf pqMsg0Id) :
    TermAt S (gClean cl) pts0 (pqMsgPure cl) pqMsg0Id := by
  have hpqr := ta_keys_pqr cl hpqpk
  have hp := ta_b00 S cl
  have hst := safeMemo_spqrInit hpqr.2.2.2 hp.2.2.2
  obtain ⟨hc_safe, hc_gam⟩ := coins32_safe_and_gamma S hcl
  obtain ⟨hsh, hsm⟩ := opaque_spqrSendMsg hst hc_safe
  have hgam : gamma dhRatchetI0 S (gClean cl) (pqMsgPure cl) = bytesOf pqMsg0Id := by
    unfold pqMsgPure stA0Pure Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceSt
    dsimp only
    rw [show (DY.Spqr.spqrSend (DY.Spqr.spqrInit o1Pure.keys.pqr spqrA2B) (randTerm 32 cl)).2.2 =
        tSSendM (DY.Spqr.spqrInit o1Pure.keys.pqr spqrA2B) (randTerm 32 cl) from rfl]
    unfold gamma gamma' tSSendM
    rw [DY.Bytes.rec_eq (DY.Libsignal.Composed.Refinement.concretizeSpqrSendMsg S)
      (DY.Libsignal.Composed.Refinement.concretizeAll dhRatchetI0 S (gClean cl))]
    dsimp only [DY.Libsignal.Composed.Refinement.concretizeSpqrSendMsg,
      DY.Libsignal.Composed.Refinement.opaqueNode, DY.Spqr.spqrInit]
    rw [show (((({ authKey := o1Pure.keys.pqr, params := spqrA2B } :
        DY.Spqr.InitState.SubF DY.Bytes).pack).rec
        (DY.Libsignal.Composed.Refinement.concretizeAll dhRatchetI0 S (gClean cl))).bytes) =
        S.init (bytesOf pqrInitId) (bytesOf b00Id) from by
      rw [DY.Bytes.rec_eq (DY.Libsignal.Composed.Refinement.concretizeSpqrInit S)
        (DY.Libsignal.Composed.Refinement.concretizeAll dhRatchetI0 S (gClean cl))]
      dsimp only [DY.Libsignal.Composed.Refinement.concretizeSpqrInit,
        DY.Libsignal.Composed.Refinement.opaqueNode]
      change S.init
        (gamma' dhRatchetI0 S (gClean cl) o1Pure.keys.pqr).bytes
        (gamma' dhRatchetI0 S (gClean cl) spqrA2B).bytes = _
      rw [hpqr.2.1, hp.2.1]]
    have hb0 : bytesOf b00Id = [0#8] := by decide +kernel
    change S.sendMsg (S.init (bytesOf pqrInitId) (bytesOf b00Id))
      (gamma' dhRatchetI0 S (gClean cl) (randTerm 32 cl)).bytes = bytesOf pqMsg0Id
    have hc_gam' : (gamma' dhRatchetI0 S (gClean cl) (randTerm 32 cl)).bytes =
        dhEv1CoinsFast.take cl := hc_gam
    rw [hb0, hc_gam', hpqm]
  exact termAt_of_opaque_pinned (bs := bytesOf pqMsg0Id) (by decide +kernel) (by decide) hsh hgam hsm

private theorem ta_mk1 {S : OpaqueSymbolSemantics} (cl : Nat)
    (hpqpk : S.kemPk (bytesOf pqskBId) = bytesOf pqpkId)
    (hck : spqrKeyBytes (S.chainKey (bytesOf pqrInitId) [0#8] [1#8, 0#8, 0#8, 0#8]) =
      bytesOf pqKey0Id) :
    let mk1 := trMsgKeys key0Pure (kdfCk stA0Pure.cks).2
    TermAt S (gClean cl) pts0 mk1.cipherKey ckey0Id ∧
    TermAt S (gClean cl) pts0 mk1.macKey mkey0Id ∧
    TermAt S (gClean cl) pts0 mk1.iv iv0Id := by
  have hprk := termAt_kdf (id := prk0Id) (by decide) (by decide)
    (ta_key0 cl hpqpk hck) (ta_seed0 cl hpqpk)
  have hckey := termAt_kdf (id := ckey0Id) (by decide) (by decide) hprk (ta_wmkInfo1 S cl)
  have hmkey := termAt_kdf (id := mkey0Id) (by decide) (by decide) hprk
    (termAt_concat (id := wmki2_0Id) (by decide) (by decide) hckey (ta_wmkInfo2 S cl))
  have hiv := termAt_kdf (id := iv0Id) (by decide) (by decide) hprk
    (termAt_concat (id := wmki3_0Id) (by decide) (by decide) hmkey (ta_wmkInfo3 S cl))
  exact ⟨hckey, hmkey, hiv⟩

private theorem ta_wire_mac_out {S : OpaqueSymbolSemantics} {cl : Nat} (hcl : cl ≤ 64)
    (hpqpk : S.kemPk (bytesOf pqskBId) = bytesOf pqpkId)
    (hck : spqrKeyBytes (S.chainKey (bytesOf pqrInitId) [0#8] [1#8, 0#8, 0#8, 0#8]) =
      bytesOf pqKey0Id)
    (hpqm : S.sendMsg (S.init (bytesOf pqrInitId) [0#8]) (dhEv1CoinsFast.take cl) =
      bytesOf pqMsg0Id) :
    TermAt S (gClean cl) pts0 (encWirePure cl) wire0Id ∧
    TermAt S (gClean cl) pts0 (encMacPure cl) mac0Id ∧
    TermAt S (gClean cl) pts0 (encOutPure cl) wmac0Id ∧
    TermAt S (gClean cl) pts0
      (computeMac (trMsgKeys DY.Spqr.zeroKey (kdfCk stA0Pure.cks).2).macKey
        (DY.Libsignal.PQXDH.serializedIk (DY.DiffieHellman.dhPk HonestSession.ikA))
        (DY.Libsignal.PQXDH.serializedIk (DY.DiffieHellman.dhPk HonestSession.ikB))
        (encWirePure cl)) zMacId ∧
    TermAt S (gClean cl) pts0 (trMsgKeys DY.Spqr.zeroKey (kdfCk stA0Pure.cks).2).cipherKey zCkeyId ∧
    TermAt S (gClean cl) pts0 (trMsgKeys DY.Spqr.zeroKey (kdfCk stA0Pure.cks).2).macKey zMkeyId ∧
    TermAt S (gClean cl) pts0 (trMsgKeys DY.Spqr.zeroKey (kdfCk stA0Pure.cks).2).iv zIvId := by
  obtain ⟨hckey, hmkey, hiv⟩ := ta_mk1 cl hpqpk hck
  have hct := termAt_symEncPt (id := ct0Id) (ts := 31) (by decide +kernel) (by decide)
    hckey hiv List.mem_cons_self rfl
  have hwire := termAt_trWire (id := wire0Id) (ver := 4) (cnt := 0) (prev := 0) (addr := pqAddrBytes)
    (by decide +kernel) (by decide)
    (ta_pk4 S cl) hct (ta_pqMsg0 hcl hpqpk hpqm) pqAddrBytes_eq_serialize
  have hmi := termAt_concat (id := mi0Id) (by decide) (by decide) (ta_ik0s S cl)
    (termAt_concat (id := miR0Id) (by decide) (by decide) (ta_ik1s S cl) hwire)
  have hfmac := termAt_kdf (id := fmac0Id) (by decide) (by decide) hmkey hmi
  have hmac := termAt_trunc8 (id := mac0Id) (by decide) (by decide) hfmac
  have hout := termAt_concat (id := wmac0Id) (by decide) (by decide) hwire hmac
  have hzprk := termAt_kdf (id := zPrkId) (by decide) (by decide)
    (ta_zeroKey S cl) (ta_seed0 cl hpqpk)
  have hzckey := termAt_kdf (id := zCkeyId) (by decide) (by decide) hzprk (ta_wmkInfo1 S cl)
  have hzmkey := termAt_kdf (id := zMkeyId) (by decide) (by decide) hzprk
    (termAt_concat (id := zWmki2Id) (by decide) (by decide) hzckey (ta_wmkInfo2 S cl))
  have hziv := termAt_kdf (id := zIvId) (by decide) (by decide) hzprk
    (termAt_concat (id := zWmki3Id) (by decide) (by decide) hzmkey (ta_wmkInfo3 S cl))
  have hzfmac := termAt_kdf (id := zFmacId) (by decide) (by decide) hzmkey hmi
  have hzmac := termAt_trunc8 (id := zMacId) (by decide) (by decide) hzfmac
  exact ⟨hwire, hmac, hout, hzmac, hzckey, hzmkey, hziv⟩

/-! ## 2. Reference Semantics `S₀` & Pinning `S.chainKey` from Outer `Explains` -/

private def S₀ : OpaqueSymbolSemantics where
  init _ _ := []
  chainKey _ _ _ := bytesOf pqKey0Id
  sendState _ _ := []
  sendKey _ _ := []
  sendMsg _ _ := bytesOf pqMsg0Id
  recvState _ _ := []
  recvKey _ _ := []
  kemPk _ := bytesOf pqpkId
  kemDecap _ _ := []
  vk _ := []
  sign _ _ _ := []

private theorem S₀_ck :
    spqrKeyBytes (S₀.chainKey (bytesOf pqrInitId) [0#8] [1#8, 0#8, 0#8, 0#8]) =
      bytesOf pqKey0Id := by
  decide +kernel

theorem pins_of_outer_explains {iw : cliCompShape.Interp} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step} {vis : List VisEntry}
    (hfit : cliCompFitsPinned iw r)
    (hex : Explains dhRatchetI0 r S g ss vis [.run dhEv0, .run dhEv1]) :
    S.kemPk (bytesOf pqskBId) = bytesOf pqpkId ∧
    spqrKeyBytes (S.chainKey (bytesOf pqrInitId) [0#8] [1#8, 0#8, 0#8, 0#8]) =
      bytesOf pqKey0Id ∧
    ∃ n, (n = 0 ∨ n = 32 ∨ n = 64) ∧
      S.sendMsg (S.init (bytesOf pqrInitId) [0#8]) (dhEv1CoinsFast.take n) = bytesOf pqMsg0Id := by
  obtain ⟨hpqpk, ⟨salt₁, seed₁, a₁, b₁, w₁, hs₁_len, hs₁_gam, hmac₁_eq⟩, ⟨n, hn_valid, hpqm⟩⟩ :=
    peel_prefix2_pins hfit hex
  have hmac₀_ta := (ta_wire_mac_out (S := S₀) (cl := 0) (Nat.zero_le _) rfl S₀_ck rfl).2.1
  have hkey₀_ta := ta_key0 (S := S₀) 0 rfl S₀_ck
  have hs₀_len : (gamma dhRatchetI0 S₀ (gClean 0) key0Pure).length = 32 := by
    rw [gamma_of_termAt hkey₀_ta]; decide +kernel
  have huntag₁ : (gamma dhRatchetI0 S g (computeMac (trMsgKeys salt₁ seed₁).macKey a₁ b₁ w₁)).take 4 ≠
      compTag4 := by
    rw [hmac₁_eq]; exact dhP0_mac_untagged
  have hmac_eq_0 :
      gamma dhRatchetI0 S g (computeMac (trMsgKeys salt₁ seed₁).macKey a₁ b₁ w₁) =
      gamma dhRatchetI0 S₀ (gClean 0) (encMacPure 0) :=
    hmac₁_eq.trans (gamma_of_termAt hmac₀_ta).symm
  obtain ⟨hsalt_pin, _⟩ := computeMac_pins_salt_and_seed hs₁_len hs₀_len huntag₁ hmac_eq_0
  rw [hs₁_gam, gamma_of_termAt hkey₀_ta] at hsalt_pin
  exact ⟨hpqpk, hsalt_pin, n, hn_valid, hpqm⟩

/-! ## 3. `SafeMemo` on Prefix & Trial Terms for `(gClean n, ssClean2 n, visClean2 n)` -/

private theorem safeMemo_storedSecrets (S : OpaqueSymbolSemantics) (cl : Nat) :
    ∀ t ∈ storedSecretsClean, SafeMemo S (gClean cl) pts0 t := by
  intro t ht
  dsimp only [storedSecretsClean,
    Symbolic.Proofs.Tests.CliNonvacuity.SessionCollisionsAux.pqSecretsList] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  have halice_no : notAnyAiNodeBytes (ofByteArray "alice".toUTF8) = true := by
    rw [ofByteArray_alice]; decide +kernel
  have halice_pos : 0 < (ofByteArray "alice".toUTF8).length := by
    rw [ofByteArray_alice]; decide +kernel
  have hbob_no : notAnyAiNodeBytes (ofByteArray "bob".toUTF8) = true := by
    rw [ofByteArray_bob]; decide +kernel
  have hbob_pos : 0 < (ofByteArray "bob".toUTF8).length := by
    rw [ofByteArray_bob]; decide +kernel
  rcases ht with rfl | rfl | rfl | rfl
  · refine safeMemo_serialize_local_pqxdh _ halice_no halice_pos (ta_ikA S cl).2.2.2 ?_
    dsimp only; rw [gamma_of_termAt (ta_ikA S cl)]; decide +kernel
  · refine safeMemo_serialize_local_pqxdh _ hbob_no hbob_pos (ta_ikB S cl).2.2.2 ?_
    dsimp only; rw [gamma_of_termAt (ta_ikB S cl)]; decide +kernel
  · refine safeMemo_serialize_local_pqxdh _ hbob_no hbob_pos (ta_spkB S cl).2.2.2 ?_
    dsimp only; rw [gamma_of_termAt (ta_spkB S cl)]; decide +kernel
  · refine safeMemo_serialize_local_pqxdh _ hbob_no hbob_pos (ta_pqskB S cl).2.2.2 ?_
    dsimp only; rw [gamma_of_termAt (ta_pqskB S cl)]; decide +kernel

private theorem safeMemo_trState_clean {S : OpaqueSymbolSemantics} {cl : Nat} (_hcl : cl ≤ 64)
    (hpqpk : S.kemPk (bytesOf pqskBId) = bytesOf pqpkId)
    {st : TRState}
    (hpeer : st.peer = "bob")
    (hmIk : st.myIk = stA0Pure.myIk)
    (hpIk : st.peerIk = stA0Pure.peerIk)
    (hrk : st.rk = stA0Pure.rk)
    (hdhs : st.dhs = HonestSession.dhsA)
    (hcks : SafeMemo S (gClean cl) pts0 st.cks)
    (hns : st.ns = 0 ∨ st.ns = 1 ∨ st.ns = 2)
    (hpn : st.pn = 0)
    (hsid : st.sid = stA0Pure.sid)
    (hspqr : SafeMemo S (gClean cl) pts0 st.spqr)
    (hrecv : st.recv = [{ ratchetKey := DY.DiffieHellman.dhPk HonestSession.spkB,
                          chainKey := o1Pure.keys.ck, index := 0, rIdx := 1 }]) :
    SafeMemo S (gClean cl) pts0
      (DY.Comparse.serialize ({ participant := "alice", state := st } :
        DY.PersistentLocalState.LocalState TRState)) := by
  let ls : DY.PersistentLocalState.LocalState TRState := { participant := "alice", state := st }
  have hanc_eq : stateAnchorPair ls =
      (o1Pure.keys.ck, recvTailTerm { ratchetKey := DY.DiffieHellman.dhPk HonestSession.spkB,
                                      chainKey := o1Pure.keys.ck, index := 0, rIdx := 1 }) := by
    unfold stateAnchorPair; dsimp only [ls]; rw [hrecv]; rfl
  obtain ⟨hrt_safe, u, hu, hrt_gam⟩ := safeMemo_recvTailTerm_0_1
    (S := S) (g := gClean cl) (pts := pts0) (DY.DiffieHellman.dhPk HonestSession.spkB) o1Pure.keys.ck
  have hck_ta := ta_keys_ck cl hpqpk
  apply safeMemo_trState_of_noAiSuffix (ls := ls)
  · rw [hanc_eq]
    dsimp only
    rw [gamma_of_termAt hck_ta, hrt_gam]
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · intro p hp
    unfold trStateProxyRoots at hp
    rw [hanc_eq] at hp
    dsimp only [ls] at hp
    rw [hpeer, hmIk, hpIk, hrk, hdhs, hpn, hsid, hrecv] at hp
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.append_assoc, List.mem_append] at hp
    have halice_no : notAnyAiNodeBytes (ofByteArray "alice".toUTF8) = true := by
      rw [ofByteArray_alice]; decide +kernel
    have halice_pos : 0 < (ofByteArray "alice".toUTF8).length := by
      rw [ofByteArray_alice]; decide +kernel
    have hbob_no : notAnyAiNodeBytes (ofByteArray "bob".toUTF8) = true := by
      rw [ofByteArray_bob]; decide +kernel
    have hbob_pos : 0 < (ofByteArray "bob".toUTF8).length := by
      rw [ofByteArray_bob]; decide +kernel
    rcases hp with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13
    · exact (safeMemo_mem_bool true h1).1
    · exact (safeMemo_mem_bool false h2).1
    · exact (safeMemo_mem_slowString halice_no halice_pos h3).1
    · exact (safeMemo_mem_slowString hbob_no hbob_pos h4).1
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h5
      rcases h5 with rfl | rfl | rfl | rfl | rfl
      · exact (ta_ik0s S cl).2.2.2
      · exact (ta_ik1s S cl).2.2.2
      · exact (ta_stA0_rk cl hpqpk).2.2.2
      · exact (ta_dhsA S cl).2.2.2
      · exact hcks
    · exact (safeMemo_mem_uint32_small hns h6).1
    · exact (safeMemo_mem_uint32_small (Or.inl rfl) h7).1
    · rcases List.mem_singleton.mp h8 with rfl; exact (ta_sid cl hpqpk).2.2.2
    · exact (safeMemo_mem_slowNat _ h9).1
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h10
      rcases h10 with rfl | rfl | rfl | rfl
      · exact hspqr
      · exact safeMemo_bytesLike_empty.1
      · exact hck_ta.2.2.2
      · exact hrt_safe
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h11
      rcases h11 with rfl | rfl
      · exact (ta_pk2 S cl).2.2.2
      · exact hck_ta.2.2.2
    · exact (safeMemo_mem_uint32_small (Or.inl rfl) h12).1
    · exact (safeMemo_mem_slowNat _ h13).1

private theorem safeMemo_storedStates {S : OpaqueSymbolSemantics} {cl : Nat} (hcl : cl ≤ 64)
    (hpqpk : S.kemPk (bytesOf pqskBId) = bytesOf pqpkId) :
    ∀ ls ∈ storedStatesClean cl, SafeMemo S (gClean cl) pts0 (DY.Comparse.serialize ls) := by
  intro ls hls
  dsimp only [storedStatesClean] at hls
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hls
  have hspqr0 : SafeMemo S (gClean cl) pts0 stA0Pure.spqr :=
    safeMemo_spqrInit (ta_keys_pqr cl hpqpk).2.2.2 (ta_b00 S cl).2.2.2
  rcases hls with rfl | rfl
  · rw [stA0_eq]
    exact safeMemo_trState_clean hcl hpqpk rfl rfl rfl rfl rfl
      (ta_stA0_cks cl hpqpk).2.2.2 (Or.inl rfl) rfl rfl hspqr0 rfl
  · unfold encSt
    rw [HonestSession.t5_length, stA0_eq]
    refine safeMemo_trState_clean hcl hpqpk rfl rfl rfl rfl rfl
      (ta_nck0 cl hpqpk).2.2.2 (Or.inr (Or.inl rfl)) rfl rfl ?_ rfl
    exact safeMemo_spqrSendState hspqr0 (coins32_safe_and_gamma S hcl).1

/-! ## 4. Discharging `¬ BobSessionStartCollidesOrImplicitRejectsOn`, `xClean_mem`, and `Explains` -/

theorem not_bobStartCollides_clean2 {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {n : Nat}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false)
    (hn : n ≤ 64)
    (hpqpk : S.kemPk (bytesOf pqskBId) = bytesOf pqpkId)
    (hck : spqrKeyBytes (S.chainKey (bytesOf pqrInitId) [0#8] [1#8, 0#8, 0#8, 0#8]) =
      bytesOf pqKey0Id)
    (hpqm : S.sendMsg (S.init (bytesOf pqrInitId) [0#8]) (dhEv1CoinsFast.take n) =
      bytesOf pqMsg0Id) :
    ¬ BobSessionStartCollidesOrImplicitRejectsOn dhRatchetI0 r S (gClean n)
      (runTrace r (ssClean2 n)) (visClean2 n) (honestSaltsOf r (ssClean2 n)) dhP0 (xClean n) := by
  unfold BobSessionStartCollidesOrImplicitRejectsOn
  dsimp only
  have hparse : parseTrSignalMsg (xClean n).msg =
      some (encParsedMsg HonestSession.t5 HonestSession.stA0 n 33) :=
    parseTrSignalMsg_encOut HonestSession.t5 HonestSession.stA0 n 33
  rw [hparse]
  dsimp only
  rw [runTrace_ssClean2 ha hb hopk, bobTrials_clean2 ha hb hopk (t6Clean n),
      honestSaltsOf_ssClean2 ha hb hopk, bobTrialTerms_clean2]
  obtain ⟨_, hmac_ta, hout_ta, hzmac_ta, hzckey_ta, hzmkey_ta, hziv_ta⟩ :=
    ta_wire_mac_out hn hpqpk hck hpqm
  obtain ⟨hckey_ta, hmkey_ta, hiv_ta⟩ := ta_mk1 n hpqpk hck
  rintro (hmemo | hmac)
  · refine not_memoCollisionOn_of_safeMemo (pts := pts0)
      (plaintextTerms_visClean2 n) ?_ ?_ ?_ ?_ ?_ hmemo
    · intro t ht
      rw [sendTerms_visClean2, o1_eq] at ht
      simp only [xClean, encOut_clean_eq, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl
      · exact (ta_ek S n).2.2.2
      · exact (ta_ctKem n hpqpk).2.2.2
      · exact hout_ta.2.2.2
    · rw [storedStates_t6Clean ha hb hopk]
      exact safeMemo_storedStates hn hpqpk
    · rw [storedSecrets_t6Clean]
      exact safeMemo_storedSecrets S n
    · intro t ht
      rcases List.mem_singleton.mp ht with rfl
      exact safeMemo_plaintext List.mem_cons_self rfl
    · intro t ht
      dsimp only [bobTrialTermsClean, xClean, encParsedMsg] at ht
      rw [encWire_clean_eq, encOut_clean_eq, o1_eq, keys1_eq, stA0_eq, key0_eq] at ht
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl
      · exact (ta_ek S n).2.2.2
      · exact (ta_ctKem n hpqpk).2.2.2
      · exact hout_ta.2.2.2
      · exact (ta_keys_rk n hpqpk).2.2.2
      · exact (ta_keys_ck n hpqpk).2.2.2
      · exact (ta_keys_pqr n hpqpk).2.2.2
      · exact (ta_stA0_cks n hpqpk).2.2.2
      · exact (ta_nck0 n hpqpk).2.2.2
      · exact hzckey_ta.2.2.2
      · exact hzmkey_ta.2.2.2
      · exact hziv_ta.2.2.2
      · exact hzmac_ta.2.2.2
      · exact hckey_ta.2.2.2
      · exact hmkey_ta.2.2.2
      · exact hiv_ta.2.2.2
      · exact hmac_ta.2.2.2
      · exact safeMemo_plaintext List.mem_cons_self rfl
  · have hmem_salt : HonestSession.key0 ∈ [DY.Spqr.zeroKey, HonestSession.key0] :=
      List.mem_cons_of_mem _ List.mem_cons_self
    have hmac_msg : (encParsedMsg HonestSession.t5 HonestSession.stA0 n 33).mac =
        encMacPure n := by
      dsimp only [encParsedMsg]; exact encMac_clean_eq n
    have hmac_hon :
        computeMac (trMsgKeys HonestSession.key0 (kdfCk HonestSession.stA0.cks).2).macKey
          HonestSession.stA0.myIk HonestSession.stA0.peerIk
          (encParsedMsg HonestSession.t5 HonestSession.stA0 n 33).wire = encMacPure n := by
      dsimp only [encParsedMsg, encMacPure]
      rw [encWire_clean_eq, key0_eq, stA0_eq]
    refine not_macTagForgeryOrCollision_of_honest_mac hmem_salt
      (by rw [hmac_msg, hmac_hon]) ?_ hmac
    rw [hmac_msg, gamma_of_termAt hmac_ta]
    exact dhP0_mac_untagged

private theorem t6Clean_le_t5 (cl : Nat) : HonestSession.t5 ≤ t6Clean cl := by
  unfold t6Clean encNextTr encPreSaltTr
  exact DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _)
    (DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _)
      (DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _)
        (DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _)
          (DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _)
            (DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) (DY.Trace.append_le _ _))))))

private theorem getMessageSentAt_le {tr₁ tr₂ : ExecTrace} {i : Nat} {m : DY.Bytes}
    (hle : tr₁ ≤ tr₂) (h : tr₁.getMessageSentAt i = some m) :
    tr₂.getMessageSentAt i = some m := by
  rw [getMessageSentAt_eq_at?] at h ⊢
  rcases hat : (tr₁.at? i : Option DY.Network.ExecEntryT) with _ | ⟨x⟩ <;> rw [hat] at h
  · cases h
  · injection h with hx
    rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some hle hat]
    exact congrArg some hx

private theorem at?_append_eq {E : Type} [DY.ExecTraceTypes.Has E]
    (tr : ExecTrace) (e : E) {i : Nat} (hi : tr.length = i) :
    ((tr.append e).at? i : Option E) = some e := by
  subst hi
  exact Symbolic.Swarm.COMPOSED.CompTrace.at?_append_here tr e

private theorem t5_sent_25_26 :
    HonestSession.t5.getMessageSentAt 25 = some HonestSession.o1.ek ∧
    HonestSession.t5.getMessageSentAt 26 = some HonestSession.o1.ct := by
  have hat25 : (HonestSession.t5.at? 25 : Option DY.Network.ExecEntryT) =
      some (Symbolic.Swarm.COMPOSED.CompTrace.NetE HonestSession.o1.ek) := by
    unfold HonestSession.t5 Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTr
      Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTrOpt
    dsimp only
    iterate 5 rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _
      (by simp only [length_append_entry_eq, HonestSession.t4_length]; omega)]
    exact at?_append_eq _ _ (by simp only [length_append_entry_eq, HonestSession.t4_length])
  have hat26 : (HonestSession.t5.at? 26 : Option DY.Network.ExecEntryT) =
      some (Symbolic.Swarm.COMPOSED.CompTrace.NetE HonestSession.o1.ct) := by
    unfold HonestSession.t5 Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTr
      Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTrOpt
    dsimp only
    iterate 4 rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _
      (by simp only [length_append_entry_eq, HonestSession.t4_length]; omega)]
    exact at?_append_eq _ _ (by simp only [length_append_entry_eq, HonestSession.t4_length])
  exact ⟨by rw [getMessageSentAt_eq_at?, hat25], by rw [getMessageSentAt_eq_at?, hat26]⟩

theorem xClean_mem {iw : cliCompShape.Interp} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {n : Nat}
    (hfit : cliCompFitsPinned iw r) (hn : n ≤ 64)
    (hpqpk : S.kemPk (bytesOf pqskBId) = bytesOf pqpkId)
    (hck : spqrKeyBytes (S.chainKey (bytesOf pqrInitId) [0#8] [1#8, 0#8, 0#8, 0#8]) =
      bytesOf pqKey0Id)
    (hpqm : S.sendMsg (S.init (bytesOf pqrInitId) [0#8]) (dhEv1CoinsFast.take n) =
      bytesOf pqMsg0Id) :
    xClean n ∈ preKeyRepresentationsOn dhRatchetI0 r S (gClean n)
      (runTrace r (ssClean2 n)) (wirePrekeyTag :: dhEv1OutFast.tail) := by
  obtain ⟨⟨⟨_, hopk, _, _, hspkId, hkpkId, hs0, _, _, _, _, _, _, _, _, _⟩,
    _, _, ⟨ha, hb⟩, _, _⟩, _, _⟩ := hfit
  rw [runTrace_ssClean2 ha hb hopk]
  obtain ⟨hs25, hs26⟩ := t5_sent_25_26
  have hkek : (xClean n).ek.AttackerKnows (t6Clean n) :=
    getMessageSentAt_attackerKnows (getMessageSentAt_le (t6Clean_le_t5 n) hs25)
  have hkct : (xClean n).ct.AttackerKnows (t6Clean n) :=
    getMessageSentAt_attackerKnows (getMessageSentAt_le (t6Clean_le_t5 n) hs26)
  have hkmsg : (xClean n).msg.AttackerKnows (t6Clean n) := by
    have hls := lastSent_t5_t6Clean n
    unfold lastSent at hls
    split at hls
    · exact getMessageSentAt_attackerKnows hls
    · cases hls
  obtain ⟨_, _, hout_ta, _, _, _, _⟩ := ta_wire_mac_out hn hpqpk hck hpqm
  have hek_gam : gamma dhRatchetI0 S (gClean n) (xClean n).ek = bytesOf ekId := by
    dsimp only [xClean]; rw [o1_eq]; exact gamma_of_termAt (ta_ek S n)
  have hct_gam : gamma dhRatchetI0 S (gClean n) (xClean n).ct = bytesOf ctKemId := by
    dsimp only [xClean]; rw [o1_eq]; exact gamma_of_termAt (ta_ctKem n hpqpk)
  have hmsg_gam : gamma dhRatchetI0 S (gClean n) (xClean n).msg = bytesOf wmac0Id := by
    dsimp only [xClean]; rw [encOut_clean_eq]; exact gamma_of_termAt hout_ta
  have hfi := faithfulInner_of_gamma_encOut_generic dhRatchetI0 S (gClean n)
    HonestSession.t5 HonestSession.stA0 n 33 dhP0 rfl rfl
    (hmsg_gam.trans dhP0_msg_eq.symm) dhP0_innerCanonical
  refine ⟨hkek, hkct, hkmsg, ⟨dhP0, parse_dhEv2_cons, ?_, ?_, ?_, dhP0_version, ?_, ?_, ?_, ?_⟩,
    ⟨dhP0, parse_dhEv2_cons, hfi⟩⟩
  · rw [hek_gam, dhP0_baseKey]; decide +kernel
  · rw [hct_gam, dhP0_kyberCt]; rfl
  · rw [hmsg_gam, dhP0_msg_eq]
  · rw [dhP0_spkId, hspkId]; rfl
  · rw [dhP0_kpkId, hkpkId]; rfl
  · unfold DY.Libsignal.Composed.Refinement.ProtocolSetup.ikASecBytes
    rw [hs0, dhP0_identityKey]; decide +kernel
  · exact ⟨false, dhP0, parse_dhEv2_cons, dhP0_preKeyId⟩

private def initCoinsPieces : List HwBytes :=
  [bytesOf r22Id] ++
    ((List.range 32).map fun j => (dhEv0CoinsFast.drop (32 + 4 * j)).take 4) ++
    [bytesOf dhsAId]

private theorem initCoinsPieces_spec :
    initCoinsPieces.all (· != []) = true ∧
    initCoinsPieces.flatten = dhEv0CoinsFast ∧
    ((List.range 32).all fun j =>
      let p := (dhEv0CoinsFast.drop (32 + 4 * j)).take 4
      (p.length == 4) && (p.head? == (bytesOf r23Id)[j]?)) = true := by
  decide +kernel

private theorem kyberCoins_forall₂ {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {n : Nat} :
    List.Forall₂
      (fun p v => BytesMatchEntry dhRatchetI0 r S (gClean n) .rng p v)
      ((List.range 32).map fun j => (dhEv0CoinsFast.drop (32 + 4 * j)).take 4)
      (kyberCoinEntries (randTerm 23 32)) := by
  have hr23_gam : gamma dhRatchetI0 S (gClean n) (randTerm 23 32) = bytesOf r23Id :=
    gamma_of_termAt (ta_r23 S n)
  have hr23_len : (bytesOf r23Id).length = 32 := by decide +kernel
  have hspec := initCoinsPieces_spec.2.2
  unfold kyberCoinEntries
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
  intro j hj
  have hok := List.all_eq_true.mp hspec j hj
  simp only [Bool.and_eq_true, beq_iff_eq] at hok
  exact ⟨rfl, hok.1, randTerm 23 32, rfl, by rw [hr23_gam, hr23_len], by rw [hr23_gam]; exact hok.2⟩

private theorem forall₂_append {α β : Type} {R : α → β → Prop} {l₁ l₂ : List α} {m₁ m₂ : List β}
    (h₁ : List.Forall₂ R l₁ m₁) (h₂ : List.Forall₂ R l₂ m₂) :
    List.Forall₂ R (l₁ ++ l₂) (m₁ ++ m₂) := by
  induction h₁ with
  | nil => exact h₂
  | cons h _ ih => exact .cons h ih

private theorem dhEv0_nextBundleIds :
    nextBundleIds none dhEv0 = some ((none, 7#32, 9#32) : BundlePreKeyIds) := by
  rw [nextBundleIds, dhEv0_cmd, dhEv0_inp_eq]; decide +kernel

private theorem runMatches_clean0 {iw : cliCompShape.Interp} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {n : Nat}
    (hfit : cliCompFitsPinned iw r)
    (hgc : GhostAndSemMatchSetup dhRatchetI0 r S (gClean n)) :
    RunMatches dhRatchetI0 r S (gClean n) (setupTrace r) (m0Of false) dhEv0
      (stepView (m0Of false) HonestSession.t4 false) none := by
  obtain ⟨⟨⟨hwf, hopk, _, _, _, _, _, _, _, ho5, ho6, ho7, _, _, _, _⟩,
    _, _, ⟨ha, hb⟩, _, _⟩, _, _⟩ := hfit
  have hst_eq := setupTrace_eq_t4 ha hb hopk
  have hrec_eq : received HonestSession.t4 [14, 15, 20, 21] =
      [setupPublic r 4, setupPublic r 5, setupPublic r 6, setupPublic r 7] := by
    rw [← hst_eq]
    have hm14 : (setupTrace r).getMessageSentAt 14 = some (setupPublic r 4) := by
      rw [getMessageSentAt_eq_at?, setupTrace_at?_14 r hwf.1]
    have hm15 : (setupTrace r).getMessageSentAt 15 = some (setupPublic r 5) := by
      rw [getMessageSentAt_eq_at?, setupTrace_at?_15 r hwf.1]
    have hm20 : (setupTrace r).getMessageSentAt 20 = some (setupPublic r 6) := by
      rw [getMessageSentAt_eq_at?, setupTrace_at?_20 r hwf.1]
    have hm21 : (setupTrace r).getMessageSentAt 21 = some (setupPublic r 7) := by
      rw [getMessageSentAt_eq_at?, setupTrace_at?_21 r hwf.1]
    simp [received, hm14, hm15, hm20, hm21]
  let inp0 : VisEntry :=
    ⟨.recv, [setupPublic r 4, setupPublic r 5, setupPublic r 6, setupPublic r 7], .bundle, none⟩
  let done0 := DY.Libsignal.Composed.Refinement.eventIdx
    DY.Libsignal.Composed.Refinement.isAliceDone HonestSession.t4 HonestSession.t5
  let drs0 : List VisEntry :=
    [rngEntry (randTerm 22 32)] ++ kyberCoinEntries (randTerm 23 32) ++
      [{ rngEntry HonestSession.dhsA with anchor := done0 }]
  have hvis0 : stepView (m0Of false) HonestSession.t4 false = inp0 :: (drs0 ++ []) := by
    rw [vis_m0_false, List.append_nil]
    unfold visStep
    rw [exposures_t4_t5, List.append_nil]
    simp only [m0Of, Bool.false_eq_true, ↓reduceIte, aliceVis, HonestSession.bh1,
      Option.toList, List.append_nil]
    have hnr0 : (newRandoms HonestSession.t4 HonestSession.t5).map (·.1) =
        [randTerm 22 32, randTerm 23 32, HonestSession.dhsA] := by
      rw [newRandoms_t4_t5]; rfl
    rw [hrec_eq, hnr0]; rfl
  refine ⟨rfl, rfl, trivial, hb.symm, by rw [hst_eq]; exact m0_ok_false, ⟨[], rfl⟩,
    by rw [hst_eq, vis_m0_false (runWrapped dhEv0), vis_m0_false false],
    inp0, drs0, [], hvis0, ?_, ?_, rfl, trivial, fun _ _ => trivial⟩
  · refine ⟨by rw [inputKind, dhEv0_cmd], ?_, ?_⟩
    · rw [dhEv0_inp_eq]
      have hg4 : gamma dhRatchetI0 S (gClean n) (setupPublic r 4) = bytesOf pk2Id := by
        rw [setupPublic_4 r hwf.1]; exact gamma_of_termAt (ta_pk2 S n)
      have hg5 : gamma dhRatchetI0 S (gClean n) (setupPublic r 5) =
          Symbolic.BugInjection.Synthetic.Witnesses.DhRatchetNoSendStepCli.setup.spkSig :=
        (hgc.2.1 r.spkSigTerm (by simp)).trans ho5
      have hg6 : gamma dhRatchetI0 S (gClean n) (setupPublic r 6) =
          Symbolic.BugInjection.Synthetic.Witnesses.DhRatchetNoSendStepCli.setup.kyberPk :=
        (hgc.2.1 r.pqpkPubTerm (by simp)).trans ho6
      have hg7 : gamma dhRatchetI0 S (gClean n) (setupPublic r 7) =
          Symbolic.BugInjection.Synthetic.Witnesses.DhRatchetNoSendStepCli.setup.kyberPkSig :=
        (hgc.2.1 r.pqpkSigTerm (by simp)).trans ho7
      refine ⟨by decide +kernel, ?_, ?_, ?_, ?_⟩
      · rw [hg4]; decide +kernel
      · rw [hg5]; decide +kernel
      · rw [hg6]; decide +kernel
      · rw [hg7]; decide +kernel
    · rw [dhEv0_inp_eq]; decide +kernel
  · refine ⟨initCoinsPieces, ?_, ?_, ?_⟩
    · intro p hp
      exact bne_iff_ne.mp (List.all_eq_true.mp initCoinsPieces_spec.1 p hp)
    · rw [dhEv0_coins_eq, initCoinsPieces_spec.2.1]
    · dsimp only [initCoinsPieces, drs0]
      refine forall₂_append (forall₂_append ?_ kyberCoins_forall₂) ?_
      · exact List.Forall₂.cons ⟨rfl, by simp [rngEntry, gamma_of_termAt (ta_r22 S n)]⟩ .nil
      · exact List.Forall₂.cons ⟨rfl, by simp [rngEntry, gamma_of_termAt (ta_dhsA S n)]⟩ .nil

private theorem runMatches_clean1 {iw : cliCompShape.Interp} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {n : Nat}
    (hfit : cliCompFitsPinned iw r) (hn : n ≤ 64)
    (hpqpk : S.kemPk (bytesOf pqskBId) = bytesOf pqpkId)
    (hck : spqrKeyBytes (S.chainKey (bytesOf pqrInitId) [0#8] [1#8, 0#8, 0#8, 0#8]) =
      bytesOf pqKey0Id)
    (hpqm : S.sendMsg (S.init (bytesOf pqrInitId) [0#8]) (dhEv1CoinsFast.take n) =
      bytesOf pqMsg0Id) :
    RunMatches dhRatchetI0 r S (gClean n)
      ((m0Of false).next (setupTrace r)) (m1Clean n) dhEv1
      (stepView (m1Clean n) HonestSession.t5 true) (some (none, 7#32, 9#32)) := by
  obtain ⟨⟨⟨_, hopk, hregA, _, _, _, hs0, _, _, _, _, _, _, _, _, _⟩,
    _, _, ⟨ha, hb⟩, _, _⟩, _, _⟩ := hfit
  have htr1 : (m0Of false).next (setupTrace r) = HonestSession.t5 := by
    rw [setupTrace_eq_t4 ha hb hopk, m0_next_false]
  have hw1 : runWrapped dhEv1 = true := by
    unfold runWrapped; rw [dhEv1_cmd, dhEv1_exit_eq]; decide +kernel
  let inp1 : VisEntry := ⟨.pt, [HonestSession.m0], .single, none⟩
  let drs1 : List VisEntry := if n = 0 then [] else [rngEntry (randTerm 32 n)]
  let out1 : VisEntry := ⟨.send, [HonestSession.o1.ek, HonestSession.o1.ct, (xClean n).msg],
                          .preKeySend, none⟩
  have hvis1 : stepView (m1Clean n) HonestSession.t5 true = inp1 :: (drs1 ++ [out1]) := by
    rw [vis_m1Clean, visEncStep, newRandoms_t5_t6Clean, lastSent_t5_t6Clean,
        exposures_t5_t6Clean, List.append_nil]
    unfold encDraws
    by_cases hn0 : n = 0 <;> simp [hn0, inp1, drs1, out1, HonestSession.m0,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.rnd, randTerm]
  obtain ⟨_, _, hout_ta, _, _, _, _⟩ := ta_wire_mac_out hn hpqpk hck hpqm
  refine ⟨rfl, rfl, trivial, trivial, by rw [htr1]; exact m1Clean_ok n,
    ⟨dhEv1OutFast, dhEv1_exit_eq⟩, by rw [htr1, hw1],
    inp1, drs1, [out1], hvis1, ?_, ?_, ?_, trivial, fun _ _ => trivial⟩
  · refine ⟨by rw [inputKind, dhEv1_cmd], ?_⟩
    rw [dhEv1_inp_eq, dhEv1InpFast_eq_pt0]
    have hm0_gam : gamma dhRatchetI0 S (gClean n) HonestSession.m0 = dhAesPt0 :=
      congrArg (·.bytes) (gamma'_plaintext_eq (ts := 31) (g := gClean n) (S := S) rfl)
    simp [inp1, hm0_gam]
  · by_cases hn0 : n = 0
    · simp only [drs1, hn0, ↓reduceIte]
      exact ⟨[], (fun _ h => nomatch h), List.nil_prefix, .nil⟩
    · simp only [drs1, hn0, ↓reduceIte]
      refine ⟨[dhEv1CoinsFast.take n], ?_, ?_, ?_⟩
      · intro p hp
        rcases List.mem_singleton.mp hp with rfl
        intro hempty
        have hlen := congrArg List.length hempty
        rw [List.length_take, dhEv1CoinsFast_len, Nat.min_eq_left hn] at hlen
        exact hn0 hlen
      · rw [dhEv1_coins_eq, List.flatten_singleton]
        exact List.take_prefix n dhEv1CoinsFast
      · exact List.Forall₂.cons
          ⟨rfl, by simp [rngEntry, (coins32_safe_and_gamma S hn).2]⟩ .nil
  · dsimp only [OutputsMatch]
    rw [dhEv1_exit_eq, dhEv1_cmd]
    refine ⟨out1, rfl, rfl, none, 7#32, 9#32, rfl, ?_⟩
    have hek_gam : gamma dhRatchetI0 S (gClean n) HonestSession.o1.ek = bytesOf ekId := by
      rw [o1_eq]; exact gamma_of_termAt (ta_ek S n)
    have hct_gam : gamma dhRatchetI0 S (gClean n) HonestSession.o1.ct = bytesOf ctKemId := by
      rw [o1_eq]; exact gamma_of_termAt (ta_ctKem n hpqpk)
    have hmsg_gam : gamma dhRatchetI0 S (gClean n) (xClean n).msg = bytesOf wmac0Id := by
      dsimp only [xClean]; rw [encOut_clean_eq]; exact gamma_of_termAt hout_ta
    unfold DY.Libsignal.Composed.Refinement.ProtocolSetup.ikASecBytes
    rw [hek_gam, hct_gam, hmsg_gam, hregA, hs0]
    decide +kernel

theorem explains_clean2 {iw : cliCompShape.Interp} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step} {vis : List VisEntry} {n : Nat}
    (hfit : cliCompFitsPinned iw r)
    (hex : Explains dhRatchetI0 r S g ss vis [.run dhEv0, .run dhEv1])
    (hn_valid : n = 0 ∨ n = 32 ∨ n = 64)
    (hpqpk : S.kemPk (bytesOf pqskBId) = bytesOf pqpkId)
    (hck : spqrKeyBytes (S.chainKey (bytesOf pqrInitId) [0#8] [1#8, 0#8, 0#8, 0#8]) =
      bytesOf pqKey0Id)
    (hpqm : S.sendMsg (S.init (bytesOf pqrInitId) [0#8]) (dhEv1CoinsFast.take n) =
      bytesOf pqMsg0Id) :
    Explains dhRatchetI0 r S (gClean n) (ssClean2 n) (visClean2 n) [.run dhEv0, .run dhEv1] := by
  have hn : n ≤ 64 := by rcases hn_valid with rfl | rfl | rfl <;> decide
  have hgc := gClean_compat n hfit hex.1
  have ⟨⟨⟨_, hopk, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩,
    _, _, ⟨ha, hb⟩, _, _⟩, _, _⟩ := hfit
  refine ⟨hgc, ghostWF_clean2 hn, modelRunWF_clean2 ha hb hopk n hn_valid, ?_⟩
  have hnil : MatchesEventsAt dhRatchetI0 r S (gClean n)
      (nextBundleIds (some (none, 7#32, 9#32)) dhEv1)
      ((m1Clean n).next ((m0Of false).next (setupTrace r))) [] [] [] :=
    MatchesEventsAt.nil (fun _ h => nomatch h)
  have h1 := matchesEvents_run1 (runMatches_clean1 hfit hn hpqpk hck hpqm) hnil
  rw [List.append_nil, ← dhEv0_nextBundleIds] at h1
  exact matchesEvents_run1 (runMatches_clean0 hfit hgc) h1

theorem not_nextEventCollides_ev2 {iw : cliCompShape.Interp} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step} {vis : List VisEntry}
    (hfit : cliCompFitsPinned iw r)
    (hex : Explains dhRatchetI0 r S g ss vis [.run dhEv0, .run dhEv1]) :
    ¬ NextEventCollides dhRatchetI0 r S g ss vis [.run dhEv0, .run dhEv1] dhEv2 := by
  have ⟨⟨⟨hwf, hopk, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩,
    _, _, ⟨ha, hb⟩, _, _⟩, _, _⟩ := hfit
  obtain ⟨hpqpk, hck, n, hn_valid, hpqm⟩ := pins_of_outer_explains hfit hex
  have hn_le : n ≤ 64 := by rcases hn_valid with rfl | rfl | rfl <;> decide
  exact not_nextEventCollides_accepted_prekey
    rfl dhEv2_inp_cons parse_dhEv2_cons
    (not_knownBaseKeyOn_of_no_recv hwf hex (by decide))
    (not_preKeyStartCollidesOrRejects_of_clean
      (not_kyberMismatch_dhP0 r)
      (explains_clean2 hfit hex hn_valid hpqpk hck hpqm)
      (not_readCollisionCli_prefix2 r S (gClean n) (ssClean2 n))
      (xClean_mem hfit hn_le hpqpk hck hpqm)
      (not_bobStartCollides_clean2 ha hb hopk hn_le hpqpk hck hpqm))

end Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.RecvMemoBobStart
