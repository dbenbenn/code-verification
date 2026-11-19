/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.DefsI0
public import Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.I0Laws
public import Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.ShaMacLaws
public import Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.NoPrefixExplains
public import Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.RecvDagData
public import Symbolic.BugInjection.Proofs.Common443.Census443Defs
public import Symbolic.BugInjection.Proofs.Common443.CompRFaithfulInner
public import Symbolic.Proofs.Tests.Shared.Composed.HonestSession
public import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeSteps
public import Symbolic.Proofs.Tests.CliNonvacuity.Witness
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import Symbolic.BugInjection.Proofs.Common443.CliEventBridge
import Symbolic.BugInjection.Proofs.Common443.CliCoinSplit
import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvBundle
import Symbolic.BugInjection.Proofs.Common443.CompRX0Bytes
import Symbolic.BugInjection.Proofs.Common443.CompRX0Gamma
import Symbolic.BugInjection.Proofs.Common443.CompRX0Mem
import Symbolic.BugInjection.Proofs.Common443.CompRGamma
import Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy
import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct
import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice
import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc
import Symbolic.Proofs.Tests.Shared.Composed.PrunedSpecLemmas
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.BobStartRun
import Symbolic.Proofs.Swarm.CREF.TR.RecvDec
import Symbolic.Proofs.Swarm.UA.BI.Step
import Symbolic.Proofs.Swarm.UA.XlateSteps
import Symbolic.Proofs.Swarm.UA.ClassicalBridge
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Random
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
public import Symbolic.Proofs.Swarm.UA.Defs

/-!
# Prefix Pinning for `DhRatchetNoSendStepCli` Call 2 (`RecvPeelPins.lean`)

1. Fast byte conversions for `dhEv0..dhEv2` and parsed `dhP0 : PreKeyFields`, with
   `not_kyberMismatch_dhP0` and `not_readCollisionCli_prefix2`.
2. Setup normalization (`r` vs `r0 := mkRecords false`).
3. `peel_prefix2_pins`: extracts `∃ n ≤ 64` and the concrete `S`-pins
   (`S.kemPk`, `S.sendMsg`, and the MAC-pinned `S.chainKey` equation) from any explanation of
   `[.run dhEv0, .run dhEv1]` under `cliCompFitsPinned`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.RecvPeelPins

open scoped DY.Libsignal.Composed
open DY (ExecTrace)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent CliEvent)
open DY.Libsignal.PQXDH.Refinement (wirePrekeyTag kyberEncapsSymbol)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.TripleRatchet (TRSignalMsg kdfCk trMsgKeys computeMac spqrA2B)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry Move
   PreKeyFields PreKeyRep eventKind
   gamma gamma' clamp randTerm ofByteArray spqrKeyBytes
   setupTrace setupRandoms setupRandomsAt setupSecret setupPublic secretBytes
   runTrace storedStates honestSaltsOf bobTrials
   GhostAndSemMatchSetup ModelRunWF Explains
   KyberMismatch parsePreKeyWire preKeySpqrIndex)
open DY.Libsignal.Composed.Refinement.Cli (ReadCollisionCli ReadCollisionCliClassical)
open Symbolic.Proofs.Swarm.UA.Defs (callsOf SchedFits flatEvents)
open Symbolic.Proofs.Swarm.UA.ClassicalBridge (BreakFree breakFree_nil explainsClassical_of)
open Symbolic.BugInjection (cliCompShape fillFresh)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compTag4 compLookupPub)
open Symbolic.BugInjection.Proofs.Common443.Census443Defs
  (iniAliceOut iniAliceStartState encSalt encWire encMac)
open Symbolic.BugInjection.Proofs.Common443.CliCoinSplit (initiateDrawsOfCoins)
open Symbolic.BugInjection.Proofs.Common443.CompRFaithfulInner
  (InnerWireCanonical encParsedMsg parseTrSignalMsg_encOut faithfulInner_of_gamma_encOut_generic)
open Symbolic.Swarm.COMPOSED.CompTrace (TRStEntry TRStE)
open Symbolic.Proofs.Tests.Shared.Composed
open Symbolic.Proofs.Tests.CliNonvacuity.Witness (mkRecords)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeSteps (setupTrace_false_eq)
open Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.DefsI0
  (dhRatchetI0 dhAesPt0 cliCompFitsPinned)
open Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.I0Laws
  (dhRatchetI0_cryptoEquationsHold dhRatchetI0_kyberCorrectOn
   dhRatchetI0_publicKey dhRatchetI0_agreement dhRatchetI0_kyberEncaps)
open Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.NoPrefixExplains
  (dhEv0 dhEv1 dhEv2)
open Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.RecvDagData

/-! ## 1. Fast Byte Literals for `dhEv0..dhEv2` & Parsed `dhP0` -/

def dhEv0Inp : HwBytes := dhEv0.input
def dhEv0Coins : HwBytes := dhEv0.coins
def dhEv0Out : HwBytes :=
  match dhEv0.exit with
  | some (_, out) => out
  | none => []
def dhEv1Inp : HwBytes := dhEv1.input
def dhEv1Coins : HwBytes := dhEv1.coins
def dhEv1Out : HwBytes :=
  match dhEv1.exit with
  | some (_, out) => out
  | none => []
def dhEv2Coins : HwBytes := dhEv2.coins
def dhEv2Out : HwBytes :=
  match dhEv2.exit with
  | some (_, out) => out
  | none => []

def hexDigit (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10

private theorem hexBytes_ofList (cs : List Char) :
    Symbolic.BugInjection.hexBytes (String.ofList cs) =
      Symbolic.BugInjection.hexBytes.go hexDigit cs := by
  unfold Symbolic.BugInjection.hexBytes hexDigit; rw [String.toList_ofList]

attribute [local irreducible] Symbolic.BugInjection.hexBytes

local elab "chars_of_hex_out" id:ident : term => do
  let e := Lean.mkConst (← Lean.resolveGlobalConstNoOverload id)
  let eWhnf ← Lean.Meta.whnf e
  let args := eWhnf.getAppArgs
  let sLit ← Lean.Meta.whnf args[0]!
  match sLit with
  | .lit (.strVal s) => return Lean.toExpr s.toList
  | _ => throwError "not strVal: {sLit}"

local elab "str_of_hex_out" id:ident : term => do
  let e := Lean.mkConst (← Lean.resolveGlobalConstNoOverload id)
  let eWhnf ← Lean.Meta.whnf e
  let args := eWhnf.getAppArgs
  let sLit ← Lean.Meta.whnf args[0]!
  return sLit

def dhEv0InpChars : List Char := chars_of_hex_out dhEv0Inp
private theorem dhEv0Inp_eq_hex : dhEv0Inp = Symbolic.BugInjection.hexBytes (str_of_hex_out dhEv0Inp) := rfl
private theorem dhEv0InpStr_eq : (str_of_hex_out dhEv0Inp) = String.ofList dhEv0InpChars := rfl
def dhEv0InpFast : HwBytes := Symbolic.BugInjection.hexBytes.go hexDigit dhEv0InpChars
theorem dhEv0_inp_eq : dhEv0.input = dhEv0InpFast := by
  change dhEv0Inp = Symbolic.BugInjection.hexBytes.go hexDigit dhEv0InpChars
  rw [dhEv0Inp_eq_hex, dhEv0InpStr_eq, hexBytes_ofList]

def dhEv0CoinsChars : List Char := chars_of_hex_out dhEv0Coins
private theorem dhEv0Coins_eq_hex : dhEv0Coins = Symbolic.BugInjection.hexBytes (str_of_hex_out dhEv0Coins) := rfl
private theorem dhEv0CoinsStr_eq : (str_of_hex_out dhEv0Coins) = String.ofList dhEv0CoinsChars := rfl
def dhEv0CoinsFast : HwBytes := Symbolic.BugInjection.hexBytes.go hexDigit dhEv0CoinsChars
theorem dhEv0_coins_eq : dhEv0.coins = dhEv0CoinsFast := by
  change dhEv0Coins = Symbolic.BugInjection.hexBytes.go hexDigit dhEv0CoinsChars
  rw [dhEv0Coins_eq_hex, dhEv0CoinsStr_eq, hexBytes_ofList]

def dhEv1InpChars : List Char := chars_of_hex_out dhEv1Inp
private theorem dhEv1Inp_eq_hex : dhEv1Inp = Symbolic.BugInjection.hexBytes (str_of_hex_out dhEv1Inp) := rfl
private theorem dhEv1InpStr_eq : (str_of_hex_out dhEv1Inp) = String.ofList dhEv1InpChars := rfl
def dhEv1InpFast : HwBytes := Symbolic.BugInjection.hexBytes.go hexDigit dhEv1InpChars
theorem dhEv1_inp_eq : dhEv1.input = dhEv1InpFast := by
  change dhEv1Inp = Symbolic.BugInjection.hexBytes.go hexDigit dhEv1InpChars
  rw [dhEv1Inp_eq_hex, dhEv1InpStr_eq, hexBytes_ofList]

def dhEv1CoinsChars : List Char := chars_of_hex_out dhEv1Coins
private theorem dhEv1Coins_eq_hex : dhEv1Coins = Symbolic.BugInjection.hexBytes (str_of_hex_out dhEv1Coins) := rfl
private theorem dhEv1CoinsStr_eq : (str_of_hex_out dhEv1Coins) = String.ofList dhEv1CoinsChars := rfl
def dhEv1CoinsFast : HwBytes := Symbolic.BugInjection.hexBytes.go hexDigit dhEv1CoinsChars
theorem dhEv1_coins_eq : dhEv1.coins = dhEv1CoinsFast := by
  change dhEv1Coins = Symbolic.BugInjection.hexBytes.go hexDigit dhEv1CoinsChars
  rw [dhEv1Coins_eq_hex, dhEv1CoinsStr_eq, hexBytes_ofList]

def dhEv1OutChars : List Char := chars_of_hex_out dhEv1Out
private theorem dhEv1Out_eq_hex : dhEv1Out = Symbolic.BugInjection.hexBytes (str_of_hex_out dhEv1Out) := rfl
private theorem dhEv1OutStr_eq : (str_of_hex_out dhEv1Out) = String.ofList dhEv1OutChars := rfl
def dhEv1OutFast : HwBytes := Symbolic.BugInjection.hexBytes.go hexDigit dhEv1OutChars
theorem dhEv1Out_eq_fast : dhEv1Out = dhEv1OutFast := by
  change dhEv1Out = Symbolic.BugInjection.hexBytes.go hexDigit dhEv1OutChars
  rw [dhEv1Out_eq_hex, dhEv1OutStr_eq, hexBytes_ofList]

theorem dhEv1_exit_eq : dhEv1.exit = some (0, dhEv1OutFast) := by
  rw [← dhEv1Out_eq_fast]; rfl

theorem dhEv2_inp_eq : dhEv2.input = dhEv1OutFast := by
  change dhEv1Out = dhEv1OutFast; exact dhEv1Out_eq_fast

theorem dhEv2_inp_cons : dhEv2.input = wirePrekeyTag :: dhEv1OutFast.tail := by
  rw [dhEv2_inp_eq]; decide +kernel

theorem dhEv1OutFast_parses : (parsePreKeyWire dhEv1OutFast).isSome = true := by
  decide +kernel

def dhP0 : PreKeyFields := (parsePreKeyWire dhEv1OutFast).get dhEv1OutFast_parses

theorem parse_dhEv1OutFast : parsePreKeyWire dhEv1OutFast = some dhP0 :=
  (Option.some_get dhEv1OutFast_parses).symm

theorem parse_dhEv2_input : parsePreKeyWire dhEv2.input = some dhP0 := by
  rw [dhEv2_inp_eq]; exact parse_dhEv1OutFast

theorem parse_dhEv2_cons : parsePreKeyWire (wirePrekeyTag :: dhEv1OutFast.tail) = some dhP0 := by
  rw [← dhEv2_inp_cons]; exact parse_dhEv2_input

theorem dhEv1OutFast_lt : dhEv1OutFast.length < 2 ^ 63 := by decide +kernel
theorem dhEv1InpFast_eq_pt0 : dhEv1InpFast = dhAesPt0 := by decide +kernel
theorem dhEv1CoinsFast_len : dhEv1CoinsFast.length = 64 := by decide +kernel
theorem dhP0_version : dhP0.version = 4 := by decide +kernel
theorem dhP0_preKeyId : dhP0.preKeyId = none := by decide +kernel
theorem dhP0_spkId : dhP0.signedPreKeyId = 7 := by decide +kernel
theorem dhP0_kpkId : dhP0.kyberPreKeyId = some 9 := by decide +kernel
theorem dhP0_baseKey : dhP0.baseKey = 0x05#8 :: bytesOf ekId := by decide +kernel
theorem dhP0_identityKey : dhP0.identityKey = 0x05#8 :: bytesOf pk0Id := by decide +kernel
theorem dhP0_kyberCt : dhP0.kyberCiphertext = some (0x08#8 :: bytesOf ctKemId) := by decide +kernel
theorem dhP0_pqRatchet : dhP0.inner.pqRatchet = bytesOf pqMsg0Id := by decide +kernel
theorem dhP0_ciphertext : dhP0.inner.ciphertext = bytesOf ct0Id := by decide +kernel
theorem dhP0_counter : dhP0.inner.counter = 0 := by decide +kernel
theorem dhP0_prevCounter : dhP0.inner.previousCounter = 0 := by decide +kernel
theorem dhP0_msg_eq : dhP0.message = bytesOf wmac0Id := by decide +kernel
theorem dhP0_mac_drop : dhP0.message.drop (dhP0.message.length - 8) = bytesOf mac0Id := by
  decide +kernel
theorem dhP0_mac_untagged : (bytesOf mac0Id).take 4 ≠ compTag4 := by decide +kernel
theorem dhP0_spqrIdx : preKeySpqrIndex dhP0 = 1 := by decide +kernel
theorem dhP0_innerCanonical : InnerWireCanonical dhP0 := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  decide +kernel

theorem dhEv0_cmd : dhEv0.cmd = .init ⟨DY.Libsignal.Composed.Refinement.Cli.bobUuid, 1⟩ "bundle" := rfl
theorem dhEv1_cmd : dhEv1.cmd = .send ⟨DY.Libsignal.Composed.Refinement.Cli.bobUuid, 1⟩ := rfl
theorem callsOf_prefix2 : callsOf [.run dhEv0, .run dhEv1] = [("alice", true), ("alice", true)] := rfl

theorem not_kyberMismatch_dhP0 (r : ProtocolSetup) :
    ¬ KyberMismatch dhRatchetI0 r dhP0 := by
  rintro ⟨e, ctBytes, ss, he32, hkc, henc, hnot⟩
  rw [dhP0_kyberCt] at hkc
  unfold DY.Libsignal.Composed.Refinement.kyberKey at hkc
  have hct : ctBytes = bytesOf ctKemId := (List.cons.inj (Option.some.inj hkc)).2.symm
  subst hct
  have hmem : bytesOf ctKemId ∈
      Symbolic.BugInjection.Synthetic.Witnesses.DhRatchetNoSendStepCli.setup.kyberCts := by
    decide +kernel
  exact hnot (dhRatchetI0_kyberCorrectOn r
    Symbolic.BugInjection.Synthetic.Witnesses.DhRatchetNoSendStepCli.setup.kyberCts
    _ hmem e ss he32 henc)

theorem not_readCollisionCli_prefix2 (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (g : Ghost) (ss : List Step) :
    ¬ ReadCollisionCli dhRatchetI0 r S g ss [.run dhEv0, .run dhEv1] := by
  rintro ⟨evs₁, ev, evs₂, _, _, _, _, _, out, _, _, heq, _, ⟨peer, hcmd⟩, _, _⟩
  have hmem : CliEvent.run ev ∈ ([.run dhEv0, .run dhEv1] : List CliEvent) := by
    rw [heq]; simp
  rcases List.mem_cons.mp hmem with h0 | h1
  · injection h0 with hev; subst hev; rw [dhEv0_cmd] at hcmd; cases hcmd
  · rcases List.mem_singleton.mp h1 with h1'
    injection h1' with hev; subst hev; rw [dhEv1_cmd] at hcmd; cases hcmd

/-! ## 2. Setup Normalization (`r` vs `r0 := mkRecords false`) -/

abbrev r0 : ProtocolSetup := mkRecords false

theorem setupTrace_eq_r0 {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false) :
    setupTrace r = setupTrace r0 := by
  unfold setupTrace r0 mkRecords; rw [ha, hb, hopk]

theorem setupTrace_eq_t4 {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false) :
    setupTrace r = HonestSession.t4 := by
  rw [setupTrace_eq_r0 ha hb hopk, setupTrace_false_eq]

theorem setupRandoms_eq_r0 {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false) :
    setupRandoms r = setupRandoms r0 := by
  unfold setupRandoms; rw [setupTrace_eq_r0 ha hb hopk]

theorem setupRandomsAt_eq_r0 {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false) :
    setupRandomsAt r = setupRandomsAt r0 := by
  unfold setupRandomsAt; rw [setupTrace_eq_r0 ha hb hopk]

theorem setupSecret_eq_r0 {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false) (k : Nat) :
    setupSecret r k = setupSecret r0 k := by
  unfold setupSecret; rw [setupRandoms_eq_r0 ha hb hopk]

theorem setupPublic_eq_r0 {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false) (k : Nat) :
    setupPublic r k = setupPublic r0 k := by
  unfold setupPublic DY.Libsignal.Composed.Refinement.setupSent
  rw [setupTrace_eq_r0 ha hb hopk]

theorem runTrace_eq_r0 {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false) (ss : List Step) :
    runTrace r ss = runTrace r0 ss := by
  unfold runTrace; rw [setupTrace_eq_r0 ha hb hopk]

theorem storedStates_eq_r0 {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false) (tr : ExecTrace) :
    storedStates r tr = storedStates r0 tr := by
  unfold storedStates; rw [setupTrace_eq_r0 ha hb hopk]

theorem honestSaltsOf_eq_r0 {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false) (ss : List Step) :
    honestSaltsOf r ss = honestSaltsOf r0 ss := by
  unfold honestSaltsOf; rw [setupTrace_eq_r0 ha hb hopk]

theorem stepsStateFaithful_iff_r0 {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false) (ss : List Step) :
    DY.Libsignal.Composed.Refinement.StepsStateFaithful r ss ↔
      DY.Libsignal.Composed.Refinement.StepsStateFaithful r0 ss := by
  unfold DY.Libsignal.Composed.Refinement.StepsStateFaithful
  simp only [runTrace_eq_r0 ha hb hopk]

theorem modelRunWF_iff_r0 {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false) (ss : List Step) :
    ModelRunWF r ss ↔ ModelRunWF r0 ss := by
  have hr0 : r0.withOpk = false := rfl
  unfold ModelRunWF
  rw [setupRandoms_eq_r0 ha hb hopk, setupTrace_eq_r0 ha hb hopk, hopk, hr0,
      stepsStateFaithful_iff_r0 ha hb hopk]

theorem bobTrials_dhP0_eq_r0 {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false)
    (tr tr' : ExecTrace) (x : PreKeyRep) (msg : TRSignalMsg) :
    bobTrials r tr dhP0 x msg = bobTrials r0 tr' dhP0 x msg := by
  unfold bobTrials DY.Libsignal.Composed.Refinement.ProtocolSetup.ikAPubTerm
    DY.Libsignal.Composed.Refinement.ProtocolSetup.ikBPubTerm
    DY.Libsignal.Composed.Refinement.ProtocolSetup.ikBSecTerm
    DY.Libsignal.Composed.Refinement.ProtocolSetup.spkSecTerm
    DY.Libsignal.Composed.Refinement.ProtocolSetup.pqskSecTerm
  rw [dhP0_preKeyId]
  dsimp only [Option.all]
  rw [setupSecret_eq_r0 ha hb hopk 1,
      setupSecret_eq_r0 ha hb hopk 2,
      setupSecret_eq_r0 ha hb hopk 4,
      setupPublic_eq_r0 ha hb hopk 0,
      setupPublic_eq_r0 ha hb hopk 2]

/-! ## 3. Peeling `[.run dhEv0, .run dhEv1]` to Pin `S` and `n ≤ 64` -/

section UnsealedSetup
unseal DY.Bytes

private theorem gamma_lit_dh (S : OpaqueSymbolSemantics) (g : Ghost) (b : ByteArray) :
    gamma dhRatchetI0 S g (DY.Literal.literalToBytes b) = ofByteArray b := by
  unfold gamma gamma' DY.Literal.literalToBytes
  show ((({ lit := b } : DY.Literal.Literal.SubF DY.Bytes).pack).rec
    (DY.Libsignal.Composed.Refinement.concretizeAll dhRatchetI0 S g)).bytes = _
  rw [DY.Bytes.rec_eq DY.Libsignal.Composed.Refinement.concretizeLit
    (DY.Libsignal.Composed.Refinement.concretizeAll dhRatchetI0 S g)]; rfl

private theorem gamma_kemPk_dh (S : OpaqueSymbolSemantics) (g : Ghost) (seed : DY.Bytes) :
    gamma dhRatchetI0 S g (DY.PQKem.kemPk seed) = S.kemPk (gamma dhRatchetI0 S g seed) := by
  unfold gamma gamma' DY.PQKem.kemPk
  show ((({ sk := seed } : DY.PQKem.Pk.SubF DY.Bytes).pack).rec
    (DY.Libsignal.Composed.Refinement.concretizeAll dhRatchetI0 S g)).bytes = _
  rw [DY.Bytes.rec_eq (DY.Libsignal.Composed.Refinement.concretizeKemPk S)
    (DY.Libsignal.Composed.Refinement.concretizeAll dhRatchetI0 S g)]; rfl

private theorem gamma_kemSS_dh (S : OpaqueSymbolSemantics) (g : Ghost) (pk e : DY.Bytes)
    (he : (gamma dhRatchetI0 S g e).length = 32) :
    gamma dhRatchetI0 S g (DY.PQKem.kemEncap pk e).2 =
      ((dhRatchetI0 kyberEncapsSymbol [gamma dhRatchetI0 S g pk, gamma dhRatchetI0 S g e]).getD []).drop 1568 := by
  unfold gamma gamma' at he ⊢
  show ((({ pk := pk, entropy := e } : DY.PQKem.SharedSecret.SubF DY.Bytes).pack).rec
    (DY.Libsignal.Composed.Refinement.concretizeAll dhRatchetI0 S g)).bytes = _
  rw [DY.Bytes.rec_eq (DY.Libsignal.Composed.Refinement.concretizeKemSS dhRatchetI0 S)
    (DY.Libsignal.Composed.Refinement.concretizeAll dhRatchetI0 S g)]
  simp only [DY.Libsignal.Composed.Refinement.concretizeKemSS, he, ↓reduceIte,
    DY.Libsignal.Composed.Refinement.node]

private theorem gamma_spqrSendMsg_init_dh (S : OpaqueSymbolSemantics) (g : Ghost)
    (a p c : DY.Bytes) :
    gamma dhRatchetI0 S g (DY.Spqr.spqrSend (DY.Spqr.spqrInit a p) c).2.2 =
      S.sendMsg (S.init (gamma dhRatchetI0 S g a) (gamma dhRatchetI0 S g p))
        (gamma dhRatchetI0 S g c) := by
  unfold gamma gamma'
  show ((({ st := DY.Spqr.spqrInit a p, coins := c } : DY.Spqr.SendMsg.SubF DY.Bytes).pack).rec
    (DY.Libsignal.Composed.Refinement.concretizeAll dhRatchetI0 S g)).bytes = _
  rw [DY.Bytes.rec_eq (DY.Libsignal.Composed.Refinement.concretizeSpqrSendMsg S)
    (DY.Libsignal.Composed.Refinement.concretizeAll dhRatchetI0 S g)]
  dsimp only [DY.Libsignal.Composed.Refinement.concretizeSpqrSendMsg,
    DY.Libsignal.Composed.Refinement.opaqueNode, DY.Spqr.spqrInit]
  congr 1
  show ((({ authKey := a, params := p } : DY.Spqr.InitState.SubF DY.Bytes).pack).rec
    (DY.Libsignal.Composed.Refinement.concretizeAll dhRatchetI0 S g)).bytes = _
  rw [DY.Bytes.rec_eq (DY.Libsignal.Composed.Refinement.concretizeSpqrInit S)
    (DY.Libsignal.Composed.Refinement.concretizeAll dhRatchetI0 S g)]; rfl

private theorem spqrKeyBytes_len (bs : HwBytes) : (spqrKeyBytes bs).length = 32 := by
  unfold spqrKeyBytes; simp

private theorem gamma_spqrSendKey_init_dh (S : OpaqueSymbolSemantics) (g : Ghost)
    (a p c : DY.Bytes) :
    gamma dhRatchetI0 S g (DY.Spqr.spqrSend (DY.Spqr.spqrInit a p) c).2.1 =
      spqrKeyBytes (S.chainKey (gamma dhRatchetI0 S g a) (gamma dhRatchetI0 S g p)
        [1#8, 0#8, 0#8, 0#8]) ∧
    (gamma dhRatchetI0 S g (DY.Spqr.spqrSend (DY.Spqr.spqrInit a p) c).2.1).length = 32 := by
  have hred : (DY.Spqr.spqrSend (DY.Spqr.spqrInit a p) c).2.1 =
      DY.Spqr.spqrChainKey a p (DY.Literal.literalToBytes ⟨#[1, 0, 0, 0]⟩) :=
    Symbolic.Proofs.Tests.Shared.Composed.PrunedSpecLemmas.spqrSend_key_init a p c
  rw [hred]
  have hgam : gamma dhRatchetI0 S g (DY.Spqr.spqrChainKey a p (DY.Literal.literalToBytes ⟨#[1, 0, 0, 0]⟩)) =
      spqrKeyBytes (S.chainKey (gamma dhRatchetI0 S g a) (gamma dhRatchetI0 S g p)
        [1#8, 0#8, 0#8, 0#8]) := by
    unfold gamma gamma' DY.Spqr.spqrChainKey
    show ((({ authKey := a, params := p, idx := (DY.Literal.literalToBytes ⟨#[1, 0, 0, 0]⟩ : DY.Bytes) } :
        DY.Spqr.ChainKey.SubF DY.Bytes).pack).rec
      (DY.Libsignal.Composed.Refinement.concretizeAll dhRatchetI0 S g)).bytes = _
    rw [DY.Bytes.rec_eq (DY.Libsignal.Composed.Refinement.concretizeSpqrChainKey S)
      (DY.Libsignal.Composed.Refinement.concretizeAll dhRatchetI0 S g)]
    have hidx : (((DY.Literal.literalToBytes ⟨#[1, 0, 0, 0]⟩ : DY.Bytes).rec
        (DY.Libsignal.Composed.Refinement.concretizeAll dhRatchetI0 S g)).bytes) =
        [1#8, 0#8, 0#8, 0#8] := by
      have h := gamma_lit_dh S g ⟨#[1, 0, 0, 0]⟩
      simpa [gamma, gamma', ofByteArray] using h
    dsimp only [DY.Libsignal.Composed.Refinement.concretizeSpqrChainKey,
      DY.Libsignal.Composed.Refinement.spqrKeyNode, DY.Libsignal.Composed.Refinement.opaqueNode]
    rw [hidx]
  exact ⟨hgam, by rw [hgam]; exact spqrKeyBytes_len _⟩

private theorem gamma_spqrA2B_dh (S : OpaqueSymbolSemantics) (g : Ghost) :
    gamma dhRatchetI0 S g spqrA2B = [0#8] := by
  have heq : spqrA2B = DY.Literal.literalToBytes ⟨#[0]⟩ := rfl
  rw [heq, gamma_lit_dh]; rfl
end UnsealedSetup

private theorem gamma_setupPublic_dh_2 {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    (hNe : r.alice ≠ r.bob) (hc : GhostAndSemMatchSetup dhRatchetI0 r S g) :
    gamma dhRatchetI0 S g (setupPublic r 2) = compLookupPub (clamp (secretBytes r 1)) := by
  rw [Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy.setupPublic_2 hNe,
      Symbolic.BugInjection.Proofs.Common443.CompRGamma.gamma_dhPk,
      ← Symbolic.BugInjection.Proofs.Common443.CompRX0Bytes.setupSecret_1 hNe,
      Symbolic.BugInjection.Proofs.Common443.CompRX0Bytes.gamma_setupSecret_1 hNe hc,
      dhRatchetI0_publicKey, Option.getD_some]

private theorem gamma_setupPublic_dh_4 {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    (hNe : r.alice ≠ r.bob) (hc : GhostAndSemMatchSetup dhRatchetI0 r S g) :
    gamma dhRatchetI0 S g (setupPublic r 4) = compLookupPub (clamp (secretBytes r 2)) := by
  rw [Symbolic.BugInjection.Proofs.Common443.CompRX0Bytes.setupPublic_4 hNe,
      Symbolic.BugInjection.Proofs.Common443.CompRGamma.gamma_dhPk,
      ← Symbolic.BugInjection.Proofs.Common443.CompRX0Bytes.setupSecret_2 hNe,
      Symbolic.BugInjection.Proofs.Common443.CompRX0Bytes.gamma_setupSecret_2 hNe hc,
      dhRatchetI0_publicKey, Option.getD_some]

private theorem pin_kemPk_of_setup {iw : cliCompShape.Interp} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost}
    (hfit : cliCompFitsPinned iw r) (hc : GhostAndSemMatchSetup dhRatchetI0 r S g) :
    S.kemPk (bytesOf pqskBId) = bytesOf pqpkId := by
  obtain ⟨⟨⟨hwf, hopk, _, _, _, _, _, _, _, _, ho6, _, _, _, _, _⟩,
    _, ⟨_, hs4, _⟩, ⟨ha, hb⟩, _, _⟩, _, _⟩ := hfit
  have h6 := hc.2.1 r.pqpkPubTerm (by simp)
  unfold DY.Libsignal.Composed.Refinement.ProtocolSetup.pqpkPubTerm at h6
  rw [ho6] at h6
  have hpub6 := Symbolic.Swarm.CREF.b1_setupPublic_6 r hwf.1
  rw [hpub6, gamma_kemPk_dh] at h6
  have hrat0 : setupRandomsAt r0 = [(0, 32), (5, 32), (10, 32), (11, 64), (16, 64), (17, 64)] := by
    rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r0 (by show "alice" ≠ "bob"; decide)]
    rfl
  have hm16 : ((16, 64) : Nat × Nat) ∈ setupRandomsAt r := by
    rw [setupRandomsAt_eq_r0 ha hb hopk, hrat0]; decide
  have hr16 : gamma dhRatchetI0 S g (randTerm 16 64) = secretBytes r 4 := by
    rw [Symbolic.BugInjection.Proofs.Common443.CompRX0Bytes.gamma_randTerm']
    simp only [show (64 : Nat) ≠ 0 by decide, ↓reduceIte, hc.1 _ hm16]
    unfold secretBytes
    rw [setupRandomsAt_eq_r0 ha hb hopk, hrat0]
    rfl
  rw [hr16, hs4] at h6
  have hsk : fillFresh 16 64 = bytesOf pqskBId := by decide +kernel
  have hpk : Symbolic.BugInjection.Synthetic.Witnesses.DhRatchetNoSendStepCli.setup.kyberPk =
      bytesOf pqpkId := by decide +kernel
  rw [hsk, hpk] at h6
  exact h6

theorem ofByteArray_pqxdhLabel :
    ofByteArray "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024".toUTF8 = bytesOf pqxdhLblId := by
  unfold ofByteArray
  rw [String.toUTF8_eq_toByteArray,
      ← String.ofList_toList (s := "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024"),
      String.toByteArray_ofList]
  decide +kernel

theorem ofByteArray_whisperRatchet :
    ofByteArray "WhisperRatchet".toUTF8 = bytesOf wrLblId := by
  unfold ofByteArray
  rw [String.toUTF8_eq_toByteArray,
      ← String.ofList_toList (s := "WhisperRatchet"),
      String.toByteArray_ofList]
  decide +kernel

theorem ofByteArray_whisperMsgKeys :
    ofByteArray "WhisperMessageKeys".toUTF8 = bytesOf wmkLblId := by
  unfold ofByteArray
  rw [String.toUTF8_eq_toByteArray,
      ← String.ofList_toList (s := "WhisperMessageKeys"),
      String.toByteArray_ofList]
  decide +kernel

theorem ofByteArray_alice :
    ofByteArray "alice".toUTF8 = bytesOf aliceLitId := by
  unfold ofByteArray
  rw [String.toUTF8_eq_toByteArray,
      ← String.ofList_toList (s := "alice"),
      String.toByteArray_ofList]
  decide +kernel

theorem ofByteArray_bob :
    ofByteArray "bob".toUTF8 = bytesOf bobLitId := by
  unfold ofByteArray
  rw [String.toUTF8_eq_toByteArray,
      ← String.ofList_toList (s := "bob"),
      String.toByteArray_ofList]
  decide +kernel

private theorem ofByteArray_zero32 :
    ofByteArray { data := Array.replicate 32 0 } = bytesOf zero32Id := by decide +kernel

private theorem ofByteArray_ff32 :
    ofByteArray { data := Array.replicate 32 255 } = bytesOf ff32Id := by decide +kernel

private theorem gamma_iniAliceOut_pqr {S : OpaqueSymbolSemantics} {g : Ghost}
    {tr₁ : ExecTrace} {ikA ikBPk spkPk pqPk : DY.Bytes}
    (hikA : gamma dhRatchetI0 S g ikA = bytesOf ikAId)
    (hikB : gamma dhRatchetI0 S g ikBPk = bytesOf pk1Id)
    (hspk : gamma dhRatchetI0 S g spkPk = bytesOf pk2Id)
    (hpq : gamma dhRatchetI0 S g pqPk = bytesOf pqpkId)
    (hek : gamma dhRatchetI0 S g (randTerm tr₁.length 32) = bytesOf r22Id)
    (hent : gamma dhRatchetI0 S g (randTerm (tr₁.length + 1) 32) = bytesOf r23Id) :
    gamma dhRatchetI0 S g (iniAliceOut tr₁ ikA ikBPk spkPk pqPk none).keys.pqr =
      bytesOf pqrInitId := by
  have he_len : (gamma dhRatchetI0 S g (randTerm (tr₁.length + 1) 32)).length = 32 := by
    rw [hent]; decide +kernel
  have hpqr_def : (iniAliceOut tr₁ ikA ikBPk spkPk pqPk none).keys.pqr =
      (DY.Libsignal.PQXDH.pqxdhKdf (DY.Libsignal.PQXDH.pqxdhIkm
        (DY.Libsignal.PQXDH.agree spkPk ikA)
        (DY.Libsignal.PQXDH.agree ikBPk (randTerm tr₁.length 32))
        (DY.Libsignal.PQXDH.agree spkPk (randTerm tr₁.length 32))
        none
        (DY.PQKem.kemEncap pqPk (randTerm (tr₁.length + 1) 32)).2)).pqr := rfl
  rw [hpqr_def]
  have hss_eq : gamma dhRatchetI0 S g (DY.PQKem.kemEncap pqPk (randTerm (tr₁.length + 1) 32)).2 =
      ((dhRatchetI0 kyberEncapsSymbol [bytesOf pqpkId, bytesOf r23Id]).getD []).drop 1568 := by
    rw [gamma_kemSS_dh S g pqPk _ he_len, hpq, hent]
  dsimp only [DY.Libsignal.PQXDH.pqxdhIkm, DY.Libsignal.PQXDH.pqxdhKdf,
    DY.Libsignal.TripleRatchet.hkdfBlock3, DY.Libsignal.TripleRatchet.hkdfBlock2,
    DY.Libsignal.TripleRatchet.hkdfBlock1,
    DY.Libsignal.PQXDH.discontinuity, DY.Libsignal.PQXDH.pqxdhLabel,
    DY.Libsignal.TripleRatchet.zeroSalt, DY.Libsignal.TripleRatchet.lit,
    DY.Libsignal.TripleRatchet.litByte]
  simp only [Symbolic.BugInjection.Proofs.Common443.CompRFaithfulInner.gamma_hmac_eq,
    Symbolic.BugInjection.Proofs.Common443.CompRFaithfulInner.gamma_concat,
    Symbolic.BugInjection.Proofs.Common443.CompRGamma.gamma_agree _ dhRatchetI0_cryptoEquationsHold,
    hss_eq, gamma_lit_dh, hikA, hikB, hspk, hek,
    ofByteArray_pqxdhLabel, ofByteArray_zero32, ofByteArray_ff32,
    dhRatchetI0_agreement, dhRatchetI0_kyberEncaps, Option.getD_some]
  decide +kernel

private theorem initDraws_dhEv0_split :
    (initiateDrawsOfCoins dhEv0CoinsFast).map MachineEvent.rng =
      .rng (bytesOf r22Id) ::
        ((initiateDrawsOfCoins dhEv0CoinsFast).tail.map MachineEvent.rng) := by
  have h0 : dhEv0CoinsFast.take 32 = bytesOf r22Id := by decide +kernel
  unfold initiateDrawsOfCoins
  simp only [List.cons_append, List.map_cons, List.tail_cons, h0]

private theorem initDraws_dhEv0_coinHeads :
    Symbolic.BugInjection.Proofs.Common443.CompRX0Gamma.coinHeads
      (((initiateDrawsOfCoins dhEv0CoinsFast).tail.map MachineEvent.rng).take 32) =
      bytesOf r23Id := by
  decide +kernel

private def MaxRandAt (tr : ExecTrace) (i k : Nat) : Prop :=
  (tr.at? i : Option DY.Random.ExecEntryT) = some ⟨k⟩ ∧
  ∀ j, i < j → (tr.at? j : Option DY.Random.ExecEntryT) = none

private theorem maxRandAt_unique {tr : ExecTrace} {i₁ k₁ i₂ k₂ : Nat}
    (h₁ : MaxRandAt tr i₁ k₁) (h₂ : MaxRandAt tr i₂ k₂) : i₁ = i₂ ∧ k₁ = k₂ := by
  by_cases hlt : i₁ < i₂
  · have h := h₁.2 i₂ hlt; rw [h₂.1] at h; cases h
  · by_cases hgt : i₂ < i₁
    · have h := h₂.2 i₁ hgt; rw [h₁.1] at h; cases h
    · have heq : i₁ = i₂ := by omega
      subst heq
      have h := Option.some.inj (h₁.1.symm.trans h₂.1)
      cases h
      exact ⟨rfl, rfl⟩

private theorem maxRandAt_rnd (tr : ExecTrace) (k : Nat) :
    MaxRandAt (tr.append (⟨k⟩ : DY.Random.ExecEntryT)) tr.length k := by
  refine ⟨Symbolic.Swarm.COMPOSED.CompTrace.at?_append_here tr (⟨k⟩ : DY.Random.ExecEntryT),
    fun j hj => ?_⟩
  have hge : (tr.append (⟨k⟩ : DY.Random.ExecEntryT)).length ≤ j := by
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.length_append_entry_eq]
    omega
  exact Symbolic.Swarm.CREF.at?_ge_length _ hge

private theorem maxRandAt_append_other {E : Type} [DY.ExecTraceTypes.Has E]
    {tr : ExecTrace} {i k : Nat} {e : E}
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option DY.Random.ExecEntryT) = none)
    (h : MaxRandAt tr i k) : MaxRandAt (tr.append e) i k :=
  ⟨(Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice.at?_append_other_eq tr e hnone i).trans h.1,
   fun j hj =>
     (Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice.at?_append_other_eq tr e hnone j).trans
       (h.2 j hj)⟩

private theorem maxRandAt_encNextTr (tr₂ : ExecTrace) (me : DY.Participant) (sIdx : Nat)
    (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) :
    MaxRandAt (Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc.encNextTr tr₂ me sIdx stA cl pq)
      (tr₂.length + 1) cl := by
  unfold Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc.encNextTr
    Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc.encPreSaltTr
  dsimp only
  iterate 5 refine maxRandAt_append_other rfl ?_
  have hlen : (tr₂.append (Symbolic.Swarm.COMPOSED.CompTrace.RndE 32)).length = tr₂.length + 1 :=
    Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.length_append_entry_eq _ _
  rw [← hlen]
  exact maxRandAt_rnd _ cl

private theorem maxRandAt_runMoves_invisible :
    ∀ (δ : List Move) (tr : ExecTrace) {i k : Nat},
      (∀ m ∈ δ, m.isSetup = false) →
      DY.Libsignal.Composed.Refinement.MovesAnchored δ tr →
      Symbolic.Swarm.CREF.MovesFrom Symbolic.Swarm.CREF.InvisibleNoEffect tr δ →
      MaxRandAt tr i k →
      MaxRandAt (DY.Libsignal.Composed.Refinement.runMoves δ tr).1 i k
  | [], _, _, _, _, _, _, h => h
  | m :: δ, tr, _, _, hs, ha, hδ, h => by
    simp only [DY.Libsignal.Composed.Refinement.runMoves]
    refine maxRandAt_runMoves_invisible δ (m.next tr)
      (fun m' hm' => hs m' (List.mem_cons_of_mem _ hm')) ha.2 hδ.2 ?_
    rcases Symbolic.BugInjection.Proofs.Common443.CompPrefixInvBundle.next_of_isSetup_false_vis_nil
      (hs m List.mem_cons_self) ha.1 hδ.1.1 with hnx | ⟨t, hnx⟩ | ⟨ev, hnx⟩
    · rwa [hnx]
    · rw [hnx]; exact maxRandAt_append_other rfl h
    · rw [hnx]; exact maxRandAt_append_other rfl h

private theorem maxRandAt_runSteps_invisible :
    ∀ (ss : List Step) (tr : ExecTrace) {i k : Nat},
      (∀ s ∈ ss, s.cls = .invisible) →
      MaxRandAt tr i k →
      MaxRandAt (DY.Libsignal.Composed.Refinement.runSteps ss tr) i k
  | [], _, _, _, _, h => h
  | s :: ss, tr, _, _, hinv, h => by
    have hs := hinv s List.mem_cons_self
    cases s <;> simp [Step.cls] at hs
    rename_i msg
    dsimp only [DY.Libsignal.Composed.Refinement.runSteps]
    rw [Symbolic.Proofs.Swarm.UA.BI.Step.next_network msg tr]
    exact maxRandAt_runSteps_invisible ss _ (fun x hx => hinv x (List.mem_cons_of_mem _ hx))
      (maxRandAt_append_other rfl h)

private theorem stepsWF_drop :
    ∀ (pre : List Step) {ss : List Step} {tr : ExecTrace},
      DY.Libsignal.Composed.Refinement.StepsWF (pre ++ ss) tr →
      DY.Libsignal.Composed.Refinement.StepsWF ss (DY.Libsignal.Composed.Refinement.runSteps pre tr)
  | [], _, _, hwf => hwf
  | _ :: pre, _, _, ⟨_, _, hwf⟩ => stepsWF_drop pre hwf

private theorem runSteps_append_eq :
    ∀ (a b : List Step) (tr : ExecTrace),
      DY.Libsignal.Composed.Refinement.runSteps (a ++ b) tr =
        DY.Libsignal.Composed.Refinement.runSteps b (DY.Libsignal.Composed.Refinement.runSteps a tr)
  | [], _, _ => rfl
  | s :: a, b, tr => runSteps_append_eq a b (s.next tr)

private theorem messageEncrypt_maxRandAt_and_rng {me : DY.Participant} {stateIdx cl pq : Nat}
    {tr₁ : ExecTrace} {w : Bool}
    (hok : (Step.messageEncrypt me stateIdx cl pq).ok tr₁ = true) :
    MaxRandAt ((Step.messageEncrypt me stateIdx cl pq).next tr₁) (tr₁.length + 1) cl ∧
    (cl ≠ 0 → DY.Libsignal.Composed.Refinement.rngEntry (randTerm (tr₁.length + 1) cl) ∈
      DY.Libsignal.Composed.Refinement.stepView (Step.messageEncrypt me stateIdx cl pq) tr₁ w) := by
  have hok0 := hok
  unfold Step.ok Step.toInput at hok
  rw [Symbolic.Proofs.Swarm.UA.BI.Step.stepIn_ok
        DY.Libsignal.TripleRatchet.messageEncrypt.reachability (me, stateIdx, cl, pq) tr₁] at hok
  have hnext : (Step.messageEncrypt me stateIdx cl pq).next tr₁ = _ :=
    Symbolic.Proofs.Swarm.UA.XlateSteps.stepIn_next
      DY.Libsignal.TripleRatchet.messageEncrypt.reachability (me, stateIdx, cl, pq) tr₁
  dsimp only [DY.Libsignal.TripleRatchet.messageEncrypt.reachability] at hok hnext
  unfold DY.Libsignal.TripleRatchet.messageEncrypt at hok hnext
  rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_fst] at hok
  rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd] at hnext
  rcases hst : ((DY.PersistentLocalState.getLocalState me stateIdx :
      DY.Traceful DY.Libsignal.TripleRatchet.TRState).run tr₁).1 with _ | st
  · rw [hst] at hok; cases hok
  · rw [hst, Symbolic.Swarm.CREF.TR.RecvDec.getLocalState_snd] at hok hnext
    dsimp only at hok hnext
    have hguard : (_root_.guard (st.ns ≠ DY.Libsignal.TripleRatchet.u32Max) : DY.Traceful Unit) = pure () := by
      unfold _root_.guard; split
      · rfl
      · next hneg =>
        exfalso; unfold _root_.guard at hok; split at hok
        · next hpos => exact hneg hpos
        · rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_fst, DY.Traceful.run_failure] at hok
          cases hok
    rw [hguard] at hok hnext
    rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_fst, DY.Traceful.run_pure] at hok; dsimp only at hok
    rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd, DY.Traceful.run_pure] at hnext; dsimp only at hnext
    rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_fst,
        (Symbolic.Swarm.CREF.TR.Runs.genRand tr₁ 32).1,
        (Symbolic.Swarm.CREF.TR.Runs.genRand tr₁ 32).2] at hok
    rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd,
        (Symbolic.Swarm.CREF.TR.Runs.genRand tr₁ 32).1,
        (Symbolic.Swarm.CREF.TR.Runs.genRand tr₁ 32).2] at hnext
    dsimp only at hok hnext
    let tr_r1 := tr₁.append (Symbolic.Swarm.COMPOSED.CompTrace.RndE 32)
    rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_fst,
        (Symbolic.Swarm.CREF.TR.Runs.genRand tr_r1 cl).1,
        (Symbolic.Swarm.CREF.TR.Runs.genRand tr_r1 cl).2] at hok
    rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd,
        (Symbolic.Swarm.CREF.TR.Runs.genRand tr_r1 cl).1,
        (Symbolic.Swarm.CREF.TR.Runs.genRand tr_r1 cl).2] at hnext
    dsimp only at hok hnext
    let tr_r2 := tr_r1.append (Symbolic.Swarm.COMPOSED.CompTrace.RndE cl)
    let spqrOut := DY.Spqr.spqrSend st.spqr (randTerm tr_r1.length cl)
    rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_fst,
        (Symbolic.Swarm.CREF.TR.Runs.sendMessage tr_r2 spqrOut.2.1).1,
        (Symbolic.Swarm.CREF.TR.Runs.sendMessage tr_r2 spqrOut.2.1).2] at hok
    rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd,
        (Symbolic.Swarm.CREF.TR.Runs.sendMessage tr_r2 spqrOut.2.1).1,
        (Symbolic.Swarm.CREF.TR.Runs.sendMessage tr_r2 spqrOut.2.1).2] at hnext
    dsimp only at hok hnext
    let tr_k := tr_r2.append (Symbolic.Swarm.COMPOSED.CompTrace.NetE spqrOut.2.1)
    rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_fst,
        Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.receiveMessage_fst_eq pq tr_k,
        Symbolic.Swarm.COMPOSED.CompTrace.receiveMessage_snd] at hok
    rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd,
        Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.receiveMessage_fst_eq pq tr_k,
        Symbolic.Swarm.COMPOSED.CompTrace.receiveMessage_snd] at hnext
    rcases hpq : tr_k.getMessageSentAt pq with _ | pqSalt
    · rw [hpq] at hok; cases hok
    · rw [hpq] at hnext; dsimp only at hnext
      let m := randTerm tr₁.length 32
      let seed := (kdfCk st.cks).2
      let keys := trMsgKeys pqSalt seed
      let ctTerm := DY.SymEnc.symEnc keys.cipherKey keys.iv m
      let wire := DY.Libsignal.TripleRatchet.trHonestWireMsg (DY.DiffieHellman.dhPk st.dhs)
        st.ns st.pn ctTerm spqrOut.2.2
      let mac := computeMac keys.macKey st.myIk st.peerIk wire
      let evSent := DY.Libsignal.TripleRatchet.TREvent.Sent me st.peer
        (DY.DiffieHellman.dhPk st.dhs) st.ns m
      have hl1 : ((DY.ProtocolEvent.logEvent evSent).run tr_k).1 = some () := by
        simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
          Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind,
          DY.Traceful.run_mk, DY.Traceful.run_pure]
      rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd, hl1,
          Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.logEvent_snd_eq evSent tr_k] at hnext
      dsimp only at hnext
      let tr_s := tr_k.append (Symbolic.Swarm.COMPOSED.CompTrace.TREvE evSent)
      rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd] at hnext
      unfold DY.Libsignal.TripleRatchet.logMessageKeyAndStore at hnext
      let evMk := DY.Libsignal.TripleRatchet.TREvent.MessageKey (st.sessionInfo me) .sender
        seed pqSalt st.ns st.rIdx stateIdx
      have hmk1 : ((DY.ProtocolEvent.logEvent evMk).run tr_s).1 = some () := by
        simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
          Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind,
          DY.Traceful.run_mk, DY.Traceful.run_pure]
      rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd,
          Symbolic.Swarm.COMPOSED.CompTrace.run_bind_fst, hmk1,
          Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.logEvent_snd_eq evMk tr_s] at hnext
      dsimp only at hnext
      let tr_mk := tr_s.append (Symbolic.Swarm.COMPOSED.CompTrace.TREvE evMk)
      let st' : DY.Libsignal.TripleRatchet.TRState :=
        { st with cks := (kdfCk st.cks).1, ns := st.ns + 1, spqr := spqrOut.1 }
      have hst1 : ((DY.PersistentLocalState.storeLocalState me st').run tr_mk).1 =
          some tr_mk.length := by
        simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
          Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
          Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
      rw [hst1, Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.storeLocalState_tr_snd_eq
        me st' tr_mk] at hnext
      dsimp only at hnext
      let tr_bef := tr_mk.append (TRStE me st')
      let msgTerm := DY.Concat.concat wire mac
      rw [(Symbolic.Swarm.CREF.TR.Runs.sendMessage tr_bef msgTerm).2] at hnext
      have hmax : MaxRandAt (tr_bef.append (Symbolic.Swarm.COMPOSED.CompTrace.NetE msgTerm))
          (tr₁.length + 1) cl := by
        dsimp only [tr_bef, tr_mk, tr_s, tr_k, tr_r2]
        iterate 5 refine maxRandAt_append_other rfl ?_
        have hlen1 : tr_r1.length = tr₁.length + 1 :=
          Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.length_append_entry_eq _ _
        rw [← hlen1]
        exact maxRandAt_rnd tr_r1 cl
      refine ⟨by rwa [hnext], fun hcl_ne => ?_⟩
      unfold DY.Libsignal.Composed.Refinement.stepView
      rw [hok0, hnext]
      simp only [↓reduceIte]
      refine List.mem_append_left _ (List.mem_append_left _ ?_)
      have hlen_tot : (tr_bef.append (Symbolic.Swarm.COMPOSED.CompTrace.NetE msgTerm)).length - tr₁.length = 7 := by
        dsimp only [tr_bef, tr_mk, tr_s, tr_k, tr_r2, tr_r1]
        simp only [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.length_append_entry_eq]
        omega
      let tr_fin := tr_bef.append (Symbolic.Swarm.COMPOSED.CompTrace.NetE msgTerm)
      have hat0 : (tr_fin.at? tr₁.length : Option DY.Random.ExecEntryT) = some ⟨32⟩ := by
        dsimp only [tr_fin, tr_bef, tr_mk, tr_s, tr_k, tr_r2, tr_r1]
        iterate 5 rw [Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice.at?_append_other_eq _ _ rfl]
        rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _
          (by rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.length_append_entry_eq]; omega)]
        exact Symbolic.Swarm.COMPOSED.CompTrace.at?_append_here tr₁ (Symbolic.Swarm.COMPOSED.CompTrace.RndE 32)
      have hat1 : (tr_fin.at? (tr₁.length + 1) : Option DY.Random.ExecEntryT) = some ⟨cl⟩ := hmax.1
      unfold DY.Libsignal.Composed.Refinement.newRandoms DY.Libsignal.Composed.Refinement.newIndices
      rw [hlen_tot]
      have hrng7 : List.range' tr₁.length 7 =
          tr₁.length :: (tr₁.length + 1) :: List.range' (tr₁.length + 2) 5 := rfl
      rw [hrng7, List.filterMap_cons, hat0, List.filterMap_cons, hat1]
      dsimp only [Option.map, DY.Libsignal.Composed.Refinement.encDraws]
      refine List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(randTerm (tr₁.length + 1) cl, cl), ?_, rfl⟩)
      exact List.mem_filter.mpr ⟨List.mem_cons_self .., bne_iff_ne.mpr hcl_ne⟩

theorem peel_prefix2_pins {iw : cliCompShape.Interp} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step} {vis : List VisEntry}
    (hfit : cliCompFitsPinned iw r)
    (hex : Explains dhRatchetI0 r S g ss vis [.run dhEv0, .run dhEv1]) :
    S.kemPk (bytesOf pqskBId) = bytesOf pqpkId ∧
    (∃ salt₁ seed₁ a₁ b₁ w₁,
      (gamma dhRatchetI0 S g salt₁).length = 32 ∧
      gamma dhRatchetI0 S g salt₁ =
        spqrKeyBytes (S.chainKey (bytesOf pqrInitId) [0#8] [1#8, 0#8, 0#8, 0#8]) ∧
      gamma dhRatchetI0 S g (computeMac (trMsgKeys salt₁ seed₁).macKey a₁ b₁ w₁) =
        bytesOf mac0Id) ∧
    ∃ n, (n = 0 ∨ n = 32 ∨ n = 64) ∧
      S.sendMsg (S.init (bytesOf pqrInitId) [0#8]) (dhEv1CoinsFast.take n) = bytesOf pqMsg0Id := by
  have hkem := pin_kemPk_of_setup hfit hex.1
  obtain ⟨⟨⟨hwf, _, _, _, _, _, hs0, hs1, hs2, _, ho6, _, _, _, _, _⟩,
    _, _, ⟨ha, hb⟩, _, _⟩, _, _⟩ := hfit
  have hbf : BreakFree [.run dhEv0, .run dhEv1] :=
    Symbolic.BugInjection.Proofs.Common443.CliEventBridge.breakFree_cons_run _
      (Symbolic.BugInjection.Proofs.Common443.CliEventBridge.breakFree_cons_run _ breakFree_nil)
  have hex_cl := explainsClassical_of hex hbf
  have hnrc : ¬ ReadCollisionCliClassical dhRatchetI0 r S g ss [.run dhEv0, .run dhEv1] := by
    refine Symbolic.BugInjection.Proofs.Common443.CliEventBridge.not_readCollisionCliClassical_of_no_recv ?_
    intro ev out hev ⟨p, hcmd⟩ _
    rcases List.mem_cons.mp hev with h0 | h1
    · injection h0 with hev0; subst hev0; rw [dhEv0_cmd] at hcmd; cases hcmd
    · rcases List.mem_singleton.mp h1 with h1'
      injection h1' with hev1; subst hev1; rw [dhEv1_cmd] at hcmd; cases hcmd
  have hsched : SchedFits (callsOf [.run dhEv0, .run dhEv1]) ["alice", "alice"] (fun _ => true) := by
    rw [callsOf_prefix2]
    refine ⟨by simp, fun k p b hget => ?_⟩
    rcases k with _ | _ | k <;> simp at hget <;> obtain ⟨rfl, rfl⟩ := hget <;> rfl
  obtain ⟨τ, ms, hex_cli, _, hnb, htr, _, _, _⟩ :=
    Symbolic.BugInjection.Proofs.Common443.CliEventBridge.xlate_inv_with_noBrk hwf hsched hex_cl hnrc
  have hflat : flatEvents [.run dhEv0, .run dhEv1] =
      [.recv dhEv0.input, .rng dhEv0.coins, .pt dhEv1.input, .rng dhEv1.coins, .send dhEv1Out] := rfl
  rw [hflat] at hex_cli
  have hc0_len : dhEv0.coins.length = 192 := by rw [dhEv0_coins_eq]; decide +kernel
  obtain ⟨blk₁, hτ, hcs₁, hex_moves⟩ :=
    Symbolic.BugInjection.Proofs.Common443.CliCoinSplit.explainsCli_init_send_decomp
      rfl hc0_len hex_cli
  have hmp_comp := hex_moves.1
  rw [hτ] at hmp_comp
  have hmp_cref := Symbolic.Swarm.CREF.MatchedPrefix.of_composed hmp_comp
  have hrs_len : ((initiateDrawsOfCoins dhEv0.coins).map MachineEvent.rng).length = 34 := by
    rw [dhEv0_coins_eq]; decide +kernel
  have hrs_kind : ∀ e ∈ (initiateDrawsOfCoins dhEv0.coins).map MachineEvent.rng,
      eventKind e = .rng := by
    intro e he; obtain ⟨_, _, rfl⟩ := List.mem_map.mp he; rfl
  have hbun4 : dhEv0.input[4]? ≠ some 1#8 := by rw [dhEv0_inp_eq]; decide +kernel
  have hw_tag : dhEv1Out.head? ≠ some wireWhisperTag := by rw [dhEv1Out_eq_fast]; decide +kernel
  obtain ⟨pre, a, idS, hb_h, shown, mid, me, sIdx, cl, pq, ⟨e, c'⟩, post, ikA, spkSig, pqpkSig,
    hms, hrest⟩ :=
    Symbolic.BugInjection.Proofs.Common443.CliCoinSplit.matchedPrefix_ini_send_bundle_legacy_split
      hwf.1 hnb hcs₁ hmp_cref hrs_len hrs_kind hbun4 hw_tag
  dsimp only at hrest
  obtain ⟨hpre, hmid, hpost, _, _, _, hdisj, _, _, _, _, _, hm₀, hls, hvis₀, hvis₁⟩ := hrest
  have ha_eq : a = r.alice ∧ ikA = setupSecret r 0 := by
    rcases hdisj with ⟨_, hal, hik⟩ | ⟨_, hbob, _⟩
    · exact ⟨hal, hik⟩
    · exfalso
      have hrf : ["alice", "alice"][DY.Libsignal.Composed.Refinement.callCount
          (DY.Libsignal.Composed.Refinement.runVis r (ms.take pre.length))]? = some a :=
        hmp_comp.2.2.1 pre.length (Move.aliceStart a r.bob idS 6 hb_h shown) a
          (by rw [hms, List.append_assoc, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl)
          rfl
      rcases hcc : DY.Libsignal.Composed.Refinement.callCount (DY.Libsignal.Composed.Refinement.runVis r (ms.take pre.length))
        with _ | _ | k <;> rw [hcc] at hrf
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at hrf
        rw [hbob, hb] at hrf; exact absurd hrf (by decide)
      · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hrf
        rw [hbob, hb] at hrf; exact absurd hrf (by decide)
      · simp only [List.getElem?_cons_succ, List.getElem?_nil, reduceCtorEq] at hrf
  obtain ⟨rfl, rfl⟩ := ha_eq
  let tr₁ := (DY.Libsignal.Composed.Refinement.runMoves pre (setupTrace r)).1
  let o := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
  let m₀ := Move.aliceStart r.alice r.bob idS 6 hb_h shown
  let tr₂ := (DY.Libsignal.Composed.Refinement.runMoves mid (m₀.next tr₁)).1
  let stA := iniAliceStartState tr₁ r.bob o
  have hown := hmp_cref.2.1.2.2.2.2.1
  have hntr := Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct.noTRState_of_movesFrom_invisibleNoEffect
    (Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct.noTRState_setupTrace r) hpre
  have hek₁ : Symbolic.Swarm.COMPOSED.CompTrace.NetMsgAt o.ek (tr₁.length + 3) (m₀.next tr₁) := by
    rw [hm₀]; exact Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice.netMsgAt_ek_iniAliceStartTr _ _ _ _
  have hct₁ : Symbolic.Swarm.COMPOSED.CompTrace.NetMsgAt o.ct (tr₁.length + 4) (m₀.next tr₁) := by
    rw [hm₀]; exact Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice.netMsgAt_ct_iniAliceStartTr _ _ _ _
  have hst₁ : ∀ j : Nat, ((m₀.next tr₁).at? j : Option TRStEntry) =
      if j = tr₁.length + 8 then some (TRStE r.alice stA) else none := by
    rw [hm₀]; exact Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice.at?_trSt_iniAliceStartTr_of_noTRState hntr _ _ _
  obtain ⟨_, hme, hsIdx, hpq, _, hnext, hlastSent, _, _, _, _, _, _, _, _, _⟩ :=
    Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc.pia_enc_inv (stA := stA)
      hms hpre hmid hpost hown hek₁ hct₁ hst₁ hls
  subst hme hsIdx hpq
  have hsm := Symbolic.BugInjection.Proofs.Common443.CliCoinSplit.sendMatches_of_encVis_split
    hcs₁ hlastSent hvis₁
  rw [dhEv1Out_eq_fast] at hsm
  obtain ⟨_, _, _, _, _, hmsg_eq⟩ :=
    Symbolic.BugInjection.Proofs.Common443.CompRX0Mem.sendMatches_append_inv
      hsm dhEv1OutFast_lt parse_dhEv1OutFast
  have hfi := faithfulInner_of_gamma_encOut_generic dhRatchetI0 S g tr₂ stA cl (tr₂.length + 2) dhP0
    rfl rfl hmsg_eq.symm dhP0_innerCanonical
  obtain ⟨msg_in, hparse_in, _, hmac_eq, _, _, _, hpq_eq, _, _⟩ := hfi
  have hmsg_in : msg_in = encParsedMsg tr₂ stA cl (tr₂.length + 2) :=
    Option.some.inj (hparse_in.symm.trans (parseTrSignalMsg_encOut tr₂ stA cl (tr₂.length + 2)))
  subst hmsg_in
  dsimp only [encParsedMsg] at hmac_eq hpq_eq
  rw [dhEv0_coins_eq, initDraws_dhEv0_split, hm₀] at hvis₀
  obtain ⟨hek_singleton, hent_eq⟩ :=
    Symbolic.BugInjection.Proofs.Common443.CompRX0Gamma.aliceVis_rng_coins hvis₀
  rw [initDraws_dhEv0_coinHeads] at hent_eq
  have hek_eq : gamma dhRatchetI0 S g (randTerm tr₁.length 32) = bytesOf r22Id :=
    List.singleton_inj.mp hek_singleton
  have hikA_eq : gamma dhRatchetI0 S g (setupSecret r 0) = bytesOf ikAId := by
    rw [Symbolic.BugInjection.Proofs.Common443.CompRX0Bytes.gamma_setupSecret_0 hwf.1 hex.1, hs0]
    decide +kernel
  have hikB_eq : gamma dhRatchetI0 S g (setupPublic r 2) = bytesOf pk1Id := by
    rw [gamma_setupPublic_dh_2 hwf.1 hex.1, hs1]; decide +kernel
  have hspk_eq : gamma dhRatchetI0 S g (setupPublic r 4) = bytesOf pk2Id := by
    rw [gamma_setupPublic_dh_4 hwf.1 hex.1, hs2]; decide +kernel
  have hpqpk_eq : gamma dhRatchetI0 S g (setupPublic r 6) = bytesOf pqpkId := by
    rw [show setupPublic r 6 = r.pqpkPubTerm from rfl, hex.1.2.1 r.pqpkPubTerm (by simp)]
    unfold DY.Libsignal.Composed.Refinement.ProtocolSetup.pqpkPubTerm
    rw [ho6]
    decide +kernel
  have hpqr_eq : gamma dhRatchetI0 S g o.keys.pqr = bytesOf pqrInitId :=
    gamma_iniAliceOut_pqr hikA_eq hikB_eq hspk_eq hpqpk_eq hek_eq hent_eq
  have hp_a2b : gamma dhRatchetI0 S g spqrA2B = [0#8] :=
    gamma_spqrA2B_dh S g
  rw [hnext] at hvis₁
  obtain ⟨_, ⟨n, hn_le, hcl_iff, hcoins_eq, _⟩, _⟩ :=
    Symbolic.BugInjection.Proofs.Common443.CliCoinSplit.encVis_of_coinSplit_send hcs₁ hvis₁
  rw [dhEv1_coins_eq] at hn_le hcoins_eq
  rw [dhEv1CoinsFast_len] at hn_le
  have hpeel_exit0 : ∀ {initIds tr_p ss_p ev_p evs_p vis_p out_p},
      ev_p.exit = some (0, out_p) →
      DY.Libsignal.Composed.Refinement.MatchesEventsAt dhRatchetI0 r S g initIds tr_p ss_p
        (.run ev_p :: evs_p) vis_p →
      ∃ pre_p s_p ss'_p v_p vs_p,
        ss_p = pre_p ++ s_p :: ss'_p ∧ vis_p = v_p ++ vs_p ∧
        DY.Libsignal.Composed.Refinement.RunMatches dhRatchetI0 r S g
          (DY.Libsignal.Composed.Refinement.runSteps pre_p tr_p) s_p ev_p v_p initIds ∧
        DY.Libsignal.Composed.Refinement.MatchesEventsAt dhRatchetI0 r S g
          (DY.Libsignal.Composed.Refinement.nextBundleIds initIds ev_p)
          (s_p.next (DY.Libsignal.Composed.Refinement.runSteps pre_p tr_p)) ss'_p evs_p vs_p := by
    intro _ _ _ _ _ _ out_p hexit hm_p
    cases hm_p with
    | run0 _ hrej _ => exact False.elim (hrej out_p hexit)
    | run1 _ hrm_p hrest_p => exact ⟨_, _, _, _, _, rfl, rfl, hrm_p, hrest_p⟩
  have hn_valid : n = 0 ∨ n = 32 ∨ n = 64 := by
    obtain ⟨_, hgwf, ⟨_, _, hswf, _⟩, hm⟩ := hex
    obtain ⟨pre₀, s₀, ss₁, v₀, vs₁, rfl, rfl, hrm₀, hm₁⟩ :=
      hpeel_exit0 (show dhEv0.exit = some (0, dhEv0Out) by rfl) hm
    obtain ⟨_, _, hswf₁⟩ := stepsWF_drop pre₀ hswf
    obtain ⟨pre₁, s₁, ss₂, v₁, vs₂, rfl, rfl, hrm₁, hm₂⟩ :=
      hpeel_exit0 (show dhEv1.exit = some (0, dhEv1Out) by rfl) hm₁
    obtain ⟨_, hs₁_lok, _⟩ := stepsWF_drop pre₁ hswf₁
    cases hm₂ with
    | nil hinv₂ =>
      obtain ⟨stH_s, cl_s, pqH_s, _, hs₁_eq, _, _, _⟩ :=
        Symbolic.BugInjection.Proofs.Common443.CliEventBridge.runMatches_filter_send_send
          dhEv1_cmd hrm₁
      obtain ⟨me_s, rfl⟩ : ∃ me_s, s₁ = .messageEncrypt me_s stH_s cl_s pqH_s := ⟨_, hs₁_eq⟩
      obtain ⟨_, _, _, _, hok₁, _, hv₁_eq, _⟩ := hrm₁
      obtain ⟨hmax_s₁, hrng_s₁⟩ :=
        messageEncrypt_maxRandAt_and_rng (w := DY.Libsignal.Composed.Refinement.runWrapped dhEv1)
          hok₁
      let tr_s₁ := DY.Libsignal.Composed.Refinement.runSteps pre₁
        (s₀.next (DY.Libsignal.Composed.Refinement.runSteps pre₀ (setupTrace r)))
      have hrun_ss : runTrace r (pre₀ ++ s₀ :: (pre₁ ++ .messageEncrypt me_s stH_s cl_s pqH_s :: ss₂)) =
          DY.Libsignal.Composed.Refinement.runSteps ss₂
            ((Step.messageEncrypt me_s stH_s cl_s pqH_s).next tr_s₁) := by
        unfold runTrace
        rw [runSteps_append_eq, DY.Libsignal.Composed.Refinement.runSteps,
            runSteps_append_eq, DY.Libsignal.Composed.Refinement.runSteps]
      have hmax_ss : MaxRandAt
          (runTrace r (pre₀ ++ s₀ :: (pre₁ ++ .messageEncrypt me_s stH_s cl_s pqH_s :: ss₂)))
          (tr_s₁.length + 1) cl_s := by
        rw [hrun_ss]
        exact maxRandAt_runSteps_invisible ss₂ _ hinv₂ hmax_s₁
      let m₁ := Move.encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c'))
      have hms_pre : ms = (pre ++ m₀ :: mid ++ [m₁]) ++ post := by
        dsimp only [tr₁, tr₂, m₀, m₁] at hms ⊢
        simp [hms, List.append_assoc]
      have htr_m₁ : (DY.Libsignal.Composed.Refinement.runMoves
          (pre ++ m₀ :: mid ++ [m₁]) (setupTrace r)).1 = m₁.next tr₂ := by
        dsimp only [tr₁, tr₂, m₀, m₁]
        simp only [Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct.runMoves_append_fst,
          DY.Libsignal.Composed.Refinement.runMoves]
      have hrun_ms : DY.Libsignal.Composed.Refinement.runTraceMoves r ms =
          (DY.Libsignal.Composed.Refinement.runMoves post (m₁.next tr₂)).1 := by
        rw [hms_pre, Symbolic.Swarm.CREF.xpl_runTrace_eq,
            Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct.runMoves_append_fst, htr_m₁]
      have hs_post : ∀ m ∈ post, m.isSetup = false :=
        fun m hm_p => hmp_cref.2.1.2.1 m (by rw [hms_pre]; exact List.mem_append_right _ hm_p)
      have ha_post : DY.Libsignal.Composed.Refinement.MovesAnchored post (m₁.next tr₂) := by
        have ha_all := hmp_cref.2.1.2.2.1.2.1
        rw [hms_pre] at ha_all
        rw [← htr_m₁]
        exact Symbolic.Swarm.CREF.xpl_movesAnchored_append_right _ post (setupTrace r) ha_all
      have hmax_ms : MaxRandAt (DY.Libsignal.Composed.Refinement.runTraceMoves r ms)
          (tr₂.length + 1) cl := by
        rw [hrun_ms]
        refine maxRandAt_runMoves_invisible post (m₁.next tr₂) hs_post ha_post hpost ?_
        rw [hnext]
        exact maxRandAt_encNextTr tr₂ r.alice (tr₁.length + 8) stA cl (tr₂.length + 2)
      rw [htr] at hmax_ms
      obtain ⟨htlen_eq, hcl_eq⟩ := maxRandAt_unique hmax_ms hmax_ss
      subst hcl_eq
      by_cases hcl0 : cl = 0
      · left; exact hcl_iff.mp hcl0
      · have hrng_v₁ : DY.Libsignal.Composed.Refinement.rngEntry
            (randTerm (tr_s₁.length + 1) cl) ∈ v₁ := by
          rw [hv₁_eq]; exact hrng_s₁ hcl0
        have hrng_vis : DY.Libsignal.Composed.Refinement.rngEntry
            (randTerm (tr_s₁.length + 1) cl) ∈ v₀ ++ (v₁ ++ []) :=
          List.mem_append_right _ (List.mem_append_left _ hrng_v₁)
        have hsig_len : (g.σ (tr_s₁.length + 1) cl).length = cl :=
          hgwf.1 _ hrng_vis rfl (tr_s₁.length + 1) cl hcl0
            (by simp [DY.Libsignal.Composed.Refinement.rngEntry])
        have hgam_len : (gamma dhRatchetI0 S g (randTerm (tr₂.length + 1) cl)).length = cl := by
          rw [htlen_eq, Symbolic.Proofs.Swarm.UA.XlateSteps.gamma_randTerm_eq _ _ _ _ _ hcl0]
          exact hsig_len
        have htake_len : (dhEv1CoinsFast.take n).length = n := by
          rw [List.length_take, dhEv1CoinsFast_len, Nat.min_eq_left hn_le]
        have hn_eq : n = cl := by
          have hcoins_eq' : gamma dhRatchetI0 S g (randTerm (tr₂.length + 1) cl) =
              dhEv1CoinsFast.take n := hcoins_eq
          have h := congrArg List.length hcoins_eq'
          omega
        rw [hn_eq]
        exact hs₁_lok.1
  have hpqMsg_pin : S.sendMsg (S.init (bytesOf pqrInitId) [0#8]) (dhEv1CoinsFast.take n) =
      bytesOf pqMsg0Id := by
    have h1 := hpq_eq.symm
    rw [dhP0_pqRatchet] at h1
    dsimp only [stA, iniAliceStartState] at h1
    rw [gamma_spqrSendMsg_init_dh, hpqr_eq, hp_a2b, hcoins_eq] at h1
    exact h1.symm
  have hsalt_self : encSalt tr₂ stA cl (tr₂.length + 2) =
      (DY.Spqr.spqrSend stA.spqr (randTerm (tr₂.length + 1) cl)).2.1 :=
    Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc.encSalt_self tr₂ stA cl
  obtain ⟨hsalt_gam, hsalt_len⟩ :=
    gamma_spqrSendKey_init_dh S g o.keys.pqr spqrA2B (randTerm (tr₂.length + 1) cl)
  rw [hpqr_eq, hp_a2b] at hsalt_gam
  refine ⟨hkem, ⟨encSalt tr₂ stA cl (tr₂.length + 2), (kdfCk stA.cks).2,
    stA.myIk, stA.peerIk, encWire tr₂ stA cl (tr₂.length + 2), ?_, ?_, ?_⟩, ⟨n, hn_valid, hpqMsg_pin⟩⟩
  · rw [hsalt_self]; exact hsalt_len
  · rw [hsalt_self]; exact hsalt_gam
  · unfold encMac at hmac_eq; rw [hmac_eq, dhP0_mac_drop]

end Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.RecvPeelPins
