/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Synthetic.Witnesses.SkippedKeyReplayCli
public import Symbolic.BugInjection.Proofs.Common.CoinsFresh
public import Symbolic.BugInjection.Witnesses.CliShape
public import Symbolic.Specifications.Security.Binary
public import Symbolic.Specifications.Model.PQXDH
public import Symbolic.Specifications.Model.TripleRatchet
public import Symbolic.Specifications.Model.Composed
public import Symbolic.Specifications.Refinement.WireFormat
public import Symbolic.Specifications.Refinement.TraceExplanation
public import Symbolic.Specifications.Refinement.Statement
public import Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
public import Symbolic.BugInjection.Proofs.Common443.Census443Defs
public import Symbolic.BugInjection.Proofs.Common443.CompRBobInit
public import Symbolic.BugInjection.Proofs.Common443.CompRNbscTable
public import Symbolic.BugInjection.Proofs.Common443.CompRI0ShaInj
public import Symbolic.BugInjection.Proofs.Common443.CompRNbsc38MacKey
public import Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire
public import Symbolic.BugInjection.Proofs.Common443.CompI0Laws
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagTree
public import Symbolic.Proofs.Tests.CliNonvacuity.SessionDag
public import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
public import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue
public import Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber
public import Symbolic.Proofs.Tests.Shared.Composed.Runs
public import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
public import Symbolic.Proofs.Swarm.COMPOSED.CompInvDefs
public import Symbolic.Proofs.Swarm.COMPOSED.CompInv
public import Symbolic.Proofs.Swarm.UA.BI.Step
public import Symbolic.DYBridge.Comparse.Basic
public import Symbolic.DYBridge.DY.Comparse
public import Symbolic.DYBridge.DY.Bytes.Basic
public import Symbolic.DYBridge.DY.Trace.Basic
public import Symbolic.DYBridge.DY.Trace.Monad
public import Symbolic.DYBridge.DY.Trace.Manipulation
public import Symbolic.DYBridge.DY.Actions.Network
public import Symbolic.DYBridge.DY.Actions.PersistentLocalState
public import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
public import Symbolic.DYBridge.DY.Actions.ProtocolEvent
public import Symbolic.DYBridge.DY.Actions.Random
public import Symbolic.DYBridge.DY.ALaCarte.Basic
public import Symbolic.DYBridge.DY.Bytes.AttackerKnowledge
public import Symbolic.DYBridge.DY.EquationalTheory.Concat
public import Symbolic.DYBridge.DY.EquationalTheory.DiffieHellman
public import Symbolic.DYBridge.DY.EquationalTheory.KdfExtract
public import Symbolic.DYBridge.DY.EquationalTheory.Sign
public import Symbolic.DYBridge.DY.Misc.Fixpoint
public import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
public import Symbolic.DYBridge.DY.EquationalTheory.Literal

public import Comparse.Basic
public import Comparse.Formats.Basic
public import Comparse.Formats.Derived
public import DY.Comparse
public import DY.Bytes.Basic
public import DY.Bytes.AttackerKnowledge
public import DY.ALaCarte.Basic
public import DY.Misc.Fixpoint
public import DY.Misc.Instances
public import DY.Trace.Basic
public import DY.Trace.Monad
public import DY.Trace.Manipulation
public import DY.Trace.BaseAttackerKnowledge
public import DY.Actions.Network
public import DY.Actions.PersistentLocalState
public import DY.Actions.PersistentGlobalState
public import DY.Actions.ProtocolEvent
public import DY.Actions.Random
public import DY.EquationalTheory.Literal
public import DY.EquationalTheory.Concat
public import DY.EquationalTheory.DiffieHellman
public import DY.EquationalTheory.KdfExtract
public import DY.EquationalTheory.Sign

/-!
# Definitions and Wire Parsing for `synthetic-skipped-key-replay`
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
open Symbolic.BugInjection.Proofs.Common443.CompRNbscTable
open Symbolic.BugInjection.Proofs.Common443.CompRI0ShaInj
open Symbolic.BugInjection.Proofs.Common443.CompRNbsc38MacKey
open Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire
open Symbolic.Swarm.COMPOSED

@[expose] public section

attribute [local irreducible] Symbolic.BugInjection.hexBytes

/-- Witness setup from `Symbolic.BugInjection.Synthetic.Witnesses.SkippedKeyReplayCli`. -/
abbrev setup : PQXDHSpqrSetup :=
  Symbolic.BugInjection.Synthetic.Witnesses.SkippedKeyReplayCli.setup

/-- Witness interpretations and records (`cliCompFits setup`). -/
abbrev fits :=
  Symbolic.BugInjection.Synthetic.Witnesses.SkippedKeyReplayCli.fits

/-- Pinned witness predicate (`compI0`, `compHooks0`). -/
abbrev cliCompFitsPinned :=
  Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable.CliSetupMatchesPinned setup

/-- `cliCompFitsPinned` refines `fits`. -/
theorem cliCompFitsPinned_sub_fits :
    ∀ iw r, cliCompFitsPinned iw r → fits iw r :=
  fun _ _ h => ⟨h.1.1, h.2.1, h.2.2⟩

/-- Satisfiability of `cliCompFitsPinned`. -/
theorem cliCompFitsPinned_satisfiable :
    ∃ iw r, cliCompFitsPinned iw r :=
  cliSetupMatchesPinned_satisfiable_of_plausible setup (by decide +kernel) (fun _ h => nomatch h)

/-- **Non-vacuity** (kernel-checked via `cliCompFitsPinned_satisfiable`). -/
theorem nonvacuous : ∃ i r, fits i r :=
  let ⟨iw, r, h⟩ := cliCompFitsPinned_satisfiable
  ⟨iw, r, cliCompFitsPinned_sub_fits iw r h⟩

/-- Recorded 6-call CLI witness trace. -/
abbrev trace : List DY.Libsignal.HwEvents.CliEvent :=
  Symbolic.BugInjection.Synthetic.Witnesses.SkippedKeyReplayCli.trace

/-- **`CoinsFresh`** holds for `(setup, trace)` under `cliCompFitsPinned`. -/
theorem coinsFresh_trace : ∀ iw r, cliCompFitsPinned iw r → CoinsFresh r trace :=
  Symbolic.BugInjection.Proofs.Common.CoinsFresh.coinsFresh_skippedKeyReplayCli

def dummyRunEvent : RunEvent :=
  { party := "", cmd := .recv ⟨"", 0⟩, input := [], coins := [], exit := none }

def ev0 : RunEvent := match Symbolic.BugInjection.Synthetic.Witnesses.SkippedKeyReplayCli.trace with | .run e :: _ => e | _ => dummyRunEvent
def ev1 : RunEvent := match Symbolic.BugInjection.Synthetic.Witnesses.SkippedKeyReplayCli.trace with | _ :: .run e :: _ => e | _ => dummyRunEvent
def ev2 : RunEvent := match Symbolic.BugInjection.Synthetic.Witnesses.SkippedKeyReplayCli.trace with | _ :: _ :: .run e :: _ => e | _ => dummyRunEvent
def ev3 : RunEvent := match Symbolic.BugInjection.Synthetic.Witnesses.SkippedKeyReplayCli.trace with | _ :: _ :: _ :: .run e :: _ => e | _ => dummyRunEvent
def ev4 : RunEvent := match Symbolic.BugInjection.Synthetic.Witnesses.SkippedKeyReplayCli.trace with | _ :: _ :: _ :: _ :: .run e :: _ => e | _ => dummyRunEvent
def ev5 : RunEvent := match Symbolic.BugInjection.Synthetic.Witnesses.SkippedKeyReplayCli.trace with | _ :: _ :: _ :: _ :: _ :: .run e :: _ => e | _ => dummyRunEvent

theorem trace_eq :
    trace = [.run ev0, .run ev1, .run ev2, .run ev3, .run ev4, .run ev5] := rfl

theorem ev4_input_eq_ev5_input : ev4.input = ev5.input := rfl

def c1HexStr : String := "03441221058f077b99cf18821ee2ae965c81e489c17be92f1ee6982468852daa25f2d076381a21055af779b498d5843151f439cb89efff3ebd63f34cb8fd9ed756699f652d43013c228f01440a210527165deb729563ad8d9111749def188cef2c168ff56fbe8a4acd3e13f020e04a100018002210f6d1587ca74787803f3db7a7acff53d12a25010101010071d6b872735413d1bcb9aa636938b24b4812a7e80062872644bb494a914638b03224008a6f1c2e3b4d4e5f9a0b1c2d3e4f5a6b01005d3e2f107a8b4c9d8e0fa1b2c3d4e5f60119bd0c2d2712bcb728d7083007380942a10c080ba7d6fd3f62f6a80c1a195beec298e88f40c26ca538dbed93d1830b9eaec0571d5922e6f60e5e1d7010ef61cecf39106a693dcb46d49111b7e59bf1044882d30bff77d2168716247565c42d7e1630febf9ecbedca70b61f295d6168431aebe2daae25af729942c40d209a1af850ac355fd2d3306e37ba1d3cc6f7a537db53c754d0b86b1336e2a8e301dbdfb8f4e7901cb050c4a5dc7988511a0fb173046e2ebe09968a11c8140c83632a4fd0e522dd4cd9af5200cb90b3bb0e8613b1dd5b88e45c3c1948c0e315068c0bb0302e2c98b00be8632db7bbba7d4ecefb430db4e2110a9c4c5d74e29885fbbee77d9666b2476cc4ae5a0db9315ae503b391178267d0a7250840fb5225ade383afc517a656141068514c1174bee65ae062c9a9b34c0a338a0d57cd718779c8b1263b319d7802de87cf5c54829c71e9931207448683fb291deeb555a56477346d625e88c6cb5a1ea8ddf96a05ad11fa0b97222277efbcb6b5cdc5eb7de32e36d34a68e2c9761ff0fb1117378f92188bd7e56b4dcc0099edd41ddd6706d11571f706bc8c9d69753f5e6684a4cf63c937cc4e90f0a6edea6f0867f8dfa3db0fe9f8d1b4b85dafb0911ce568a76f17c166b0c9c1c30ed0923227ae2bee62ae39e5094b6ecc69157ada3335f27533853663e338d1a8d43cd0b0987f9e336a17bb0ae9bc5c6c67002686fad3623b27bb9cbe970416c048278e4036949737f0a734d0ffae6ec152261b654fcb7ad3881bc426a4ec4f3021906ec452641bd0d1de6b77b3176d68f1a763f559218dcca1af53ec2b336148b079e3d238465b00d78a9873f2db3c131a834f303760c371100459c276eb0049d2f00d691b8faaec0e8f973a5201d166ebb88f4134d9ae0457962bf94435e47a92caf1ad05f7f75c431c8b487225c3437e91b2553068c85592f655a26b1bf8083efe7d404485cf6f34d09b9d36d00c1bb0efa48f9c59633105de574625ab87089eb9b25b2a528f6f352ceabf0bc4c1029c499997eb33139d1365964d2eb5e5116e799a9ee51bb2846ae0dd1da7f6c74d4135925d31790636ec3b3cd715c6656adf9e1ba4b6a3cc83533a088ad85a5420930ac391365772931ec9cef55e588856f3bd5a677f364e034e426e73b420ad86117f68fe13825b34d3e2b7a2f09d7a10a3ac28752b44aed49bc294e2b64583449d28701e9d2004acbd09780def8e6f24e61ace09439f8811134f43bd48d009a993437296d96b94561ce718e0b47273ba19292c5e8ac3cd013d8b8a8df98d6fcff61a996593af684aeec792292f7751c8087c5c5cbcb3531cc3ecec89068db7e454f8014678a0c7eeaae541a436ed5b27929360716a31e99a5d5da2d8c499e1ac7962ab6d7bcab7e723a298ffa568fc1f55a52b4eea4d763e190ac1cf59d622ea97123bbb5f08d96cfa32bbe4ab88d15a0502e1993b6ce84aa9b99debabeee58e2ffd2008873ff3a8c9ad0dbb1117a922d9bd4ff8334261f37c4d2288ddd8eda7f6beb35b674cd0bc9934fbb7813f4992ffad01bb61dd1db4219133f0b77703c30bdb110d392daa3703c24e66cb0c99841b384f80c335aaf371137e3a5316ce3067f9f8a68e3a5cf5115c9c3753bdcd015b93da513c116e051eeb0417c6daaa499130a2009a473da36bd87e0aa384a8061edc500bbc32721ca18228780ba8e8cbc1ed873b99ba0698006fc8aca98c7374e9ac16f0a40d2744ae5f2372b7b020ae553aea72132e14d6ac6c3e597f1aaa8615218c66068565c0011e5d1c661997698cdd3bfda3c02e10a56107cced7731ef6d4b77745d5680bcdf322ede616661d114edac92b2696dbd77b94b9ba282545a7b39dd899f8db6f667d83ca1af5cb48ac7d3cb5db6e8c47cba6c0baacdf138ed09ad6e228ded241c67d2e423c42c66c52b323545f13eb77db040d486cb19f201636dd78f0c192d26e9c57e5e70e3c9ae1516e19a82b21fa606afe90911db0c70fd96731d40c72b0a37319cb02a273d9423a68ca8049ff59b5de1ddcbeff367c4309627dba2d195b804c5048a89d72003109bc5edcbc8d5fe7c61f5416c618a5a90d8ae7aa0d59844c22589ba566c8258ea39aa9c4ee9ab470bea26275b643217bdba58075e94d2058b8da3377e822eb5f3fa9693a40b465dc2f43466575a5cdd5b2d36c9c8f3383705166f867cee25f6a17f44743fa68ac622bf9aa3e82219542ec4"

def c2HexStr : String := "03441221058f077b99cf18821ee2ae965c81e489c17be92f1ee6982468852daa25f2d076381a21055af779b498d5843151f439cb89efff3ebd63f34cb8fd9ed756699f652d43013c228f01440a210527165deb729563ad8d9111749def188cef2c168ff56fbe8a4acd3e13f020e04a100118002210a05c5b48492d286787e147d0bd404f882a2501010201018602e5c4b408554b07c7d358fb0d0622578dfb95d6afc2a9df5aac0837a5dfc53224008a6f1c2e3b4d4e5f9a0b1c2d3e4f5a6b01005d3e2f107a8b4c9d8e0fa1b2c3d4e5f6011ba3bf4619b3015928d7083007380942a10c080ba7d6fd3f62f6a80c1a195beec298e88f40c26ca538dbed93d1830b9eaec0571d5922e6f60e5e1d7010ef61cecf39106a693dcb46d49111b7e59bf1044882d30bff77d2168716247565c42d7e1630febf9ecbedca70b61f295d6168431aebe2daae25af729942c40d209a1af850ac355fd2d3306e37ba1d3cc6f7a537db53c754d0b86b1336e2a8e301dbdfb8f4e7901cb050c4a5dc7988511a0fb173046e2ebe09968a11c8140c83632a4fd0e522dd4cd9af5200cb90b3bb0e8613b1dd5b88e45c3c1948c0e315068c0bb0302e2c98b00be8632db7bbba7d4ecefb430db4e2110a9c4c5d74e29885fbbee77d9666b2476cc4ae5a0db9315ae503b391178267d0a7250840fb5225ade383afc517a656141068514c1174bee65ae062c9a9b34c0a338a0d57cd718779c8b1263b319d7802de87cf5c54829c71e9931207448683fb291deeb555a56477346d625e88c6cb5a1ea8ddf96a05ad11fa0b97222277efbcb6b5cdc5eb7de32e36d34a68e2c9761ff0fb1117378f92188bd7e56b4dcc0099edd41ddd6706d11571f706bc8c9d69753f5e6684a4cf63c937cc4e90f0a6edea6f0867f8dfa3db0fe9f8d1b4b85dafb0911ce568a76f17c166b0c9c1c30ed0923227ae2bee62ae39e5094b6ecc69157ada3335f27533853663e338d1a8d43cd0b0987f9e336a17bb0ae9bc5c6c67002686fad3623b27bb9cbe970416c048278e4036949737f0a734d0ffae6ec152261b654fcb7ad3881bc426a4ec4f3021906ec452641bd0d1de6b77b3176d68f1a763f559218dcca1af53ec2b336148b079e3d238465b00d78a9873f2db3c131a834f303760c371100459c276eb0049d2f00d691b8faaec0e8f973a5201d166ebb88f4134d9ae0457962bf94435e47a92caf1ad05f7f75c431c8b487225c3437e91b2553068c85592f655a26b1bf8083efe7d404485cf6f34d09b9d36d00c1bb0efa48f9c59633105de574625ab87089eb9b25b2a528f6f352ceabf0bc4c1029c499997eb33139d1365964d2eb5e5116e799a9ee51bb2846ae0dd1da7f6c74d4135925d31790636ec3b3cd715c6656adf9e1ba4b6a3cc83533a088ad85a5420930ac391365772931ec9cef55e588856f3bd5a677f364e034e426e73b420ad86117f68fe13825b34d3e2b7a2f09d7a10a3ac28752b44aed49bc294e2b64583449d28701e9d2004acbd09780def8e6f24e61ace09439f8811134f43bd48d009a993437296d96b94561ce718e0b47273ba19292c5e8ac3cd013d8b8a8df98d6fcff61a996593af684aeec792292f7751c8087c5c5cbcb3531cc3ecec89068db7e454f8014678a0c7eeaae541a436ed5b27929360716a31e99a5d5da2d8c499e1ac7962ab6d7bcab7e723a298ffa568fc1f55a52b4eea4d763e190ac1cf59d622ea97123bbb5f08d96cfa32bbe4ab88d15a0502e1993b6ce84aa9b99debabeee58e2ffd2008873ff3a8c9ad0dbb1117a922d9bd4ff8334261f37c4d2288ddd8eda7f6beb35b674cd0bc9934fbb7813f4992ffad01bb61dd1db4219133f0b77703c30bdb110d392daa3703c24e66cb0c99841b384f80c335aaf371137e3a5316ce3067f9f8a68e3a5cf5115c9c3753bdcd015b93da513c116e051eeb0417c6daaa499130a2009a473da36bd87e0aa384a8061edc500bbc32721ca18228780ba8e8cbc1ed873b99ba0698006fc8aca98c7374e9ac16f0a40d2744ae5f2372b7b020ae553aea72132e14d6ac6c3e597f1aaa8615218c66068565c0011e5d1c661997698cdd3bfda3c02e10a56107cced7731ef6d4b77745d5680bcdf322ede616661d114edac92b2696dbd77b94b9ba282545a7b39dd899f8db6f667d83ca1af5cb48ac7d3cb5db6e8c47cba6c0baacdf138ed09ad6e228ded241c67d2e423c42c66c52b323545f13eb77db040d486cb19f201636dd78f0c192d26e9c57e5e70e3c9ae1516e19a82b21fa606afe90911db0c70fd96731d40c72b0a37319cb02a273d9423a68ca8049ff59b5de1ddcbeff367c4309627dba2d195b804c5048a89d72003109bc5edcbc8d5fe7c61f5416c618a5a90d8ae7aa0d59844c22589ba566c8258ea39aa9c4ee9ab470bea26275b643217bdba58075e94d2058b8da3377e822eb5f3fa9693a40b465dc2f43466575a5cdd5b2d36c9c8f3383705166f867cee25f6a17f44743fa68ac622bf9aa3e82219542ec4"

theorem ev3_exit_eq_ev2_input : ev3.exit = some (0, ev2.input) := rfl
theorem ev4_exit_eq_ev1_input : ev4.exit = some (0, ev1.input) := rfl
theorem ev5_exit_eq_ev1_input : ev5.exit = some (0, ev1.input) := rfl

theorem ev4_input_eq_c1Hex : ev4.input = hexBytes c1HexStr := rfl
theorem ev3_input_eq_c2Hex : ev3.input = hexBytes c2HexStr := rfl

def c1Wrap : HwBytes := hexBytes c1HexStr
def c1Chars : List Char := chars_of_hex_def c1Wrap
theorem c1HexStr_eq : c1HexStr = String.ofList c1Chars := rfl

def c2Wrap : HwBytes := hexBytes c2HexStr
def c2Chars : List Char := chars_of_hex_def c2Wrap
theorem c2HexStr_eq : c2HexStr = String.ofList c2Chars := rfl

def c1Fast : HwBytes := hexBytes.go hexDigit c1Chars
def c2Fast : HwBytes := hexBytes.go hexDigit c2Chars

theorem ev4_input_eq_fast : ev4.input = c1Fast := by
  rw [ev4_input_eq_c1Hex, c1HexStr_eq, hexBytes_ofList]; rfl

theorem ev1_exit_eq_fast : ev1.exit = some (0, c1Fast) := by
  change some (0, hexBytes c1HexStr) = _
  rw [c1HexStr_eq, hexBytes_ofList]; rfl

theorem runWrapped_ev1_fast : runWrapped ev1 = true := by
  unfold runWrapped
  have hcmd : ev1.cmd = .send ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ := rfl
  rw [hcmd, ev1_exit_eq_fast]
  decide +kernel

theorem ev2_exit_eq_fast : ev2.exit = some (0, c2Fast) := by
  change some (0, hexBytes c2HexStr) = _
  rw [c2HexStr_eq, hexBytes_ofList]; rfl

theorem runWrapped_ev2_fast : runWrapped ev2 = true := by
  unfold runWrapped
  have hcmd : ev2.cmd = .send ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ := rfl
  rw [hcmd, ev2_exit_eq_fast]
  decide +kernel

theorem ev3_input_eq_fast : ev3.input = c2Fast := by
  rw [ev3_input_eq_c2Hex, c2HexStr_eq, hexBytes_ofList]; rfl

theorem parsePreKeyWire_c1Fast_isSome : (parsePreKeyWire c1Fast).isSome = true := by
  decide +kernel

theorem parsePreKeyWire_c2Fast_isSome : (parsePreKeyWire c2Fast).isSome = true := by
  decide +kernel

def p_c1 : PreKeyFields := (parsePreKeyWire c1Fast).get parsePreKeyWire_c1Fast_isSome
def p_c2 : PreKeyFields := (parsePreKeyWire c2Fast).get parsePreKeyWire_c2Fast_isSome

theorem parsePreKeyWire_ev4 : parsePreKeyWire ev4.input = some p_c1 := by
  rw [ev4_input_eq_fast]; exact (Option.some_get parsePreKeyWire_c1Fast_isSome).symm

theorem parsePreKeyWire_ev5 : parsePreKeyWire ev5.input = some p_c1 := by
  rw [← ev4_input_eq_ev5_input]; exact parsePreKeyWire_ev4

theorem parsePreKeyWire_ev3 : parsePreKeyWire ev3.input = some p_c2 := by
  rw [ev3_input_eq_fast]; exact (Option.some_get parsePreKeyWire_c2Fast_isSome).symm

theorem p_c1_baseKey_eq_p_c2_baseKey : p_c1.baseKey = p_c2.baseKey := by
  decide +kernel

theorem p_c1_counter_eq : p_c1.inner.counter = 0 := by
  decide +kernel

theorem p_c2_counter_eq : p_c2.inner.counter = 1 := by
  decide +kernel

theorem p_c1_ratchetKey_eq_p_c2_ratchetKey :
    p_c1.inner.senderRatchetKey = p_c2.inner.senderRatchetKey := by
  decide +kernel

def msgMac8' (p : PreKeyFields) : HwBytes :=
  p.message.drop (p.message.length - 8)

def macChainOk' (k P : HwBytes) (p : PreKeyFields) : Bool :=
  ((msgMac8' p).take 4 != compTag4) && (keyOfTake8 (msgMac8' p) == some k) &&
    (k.take 4 != compTag4) && (keyOfTake8 (k.take 8) == some P)

def wireMacChainOk' (k P w : HwBytes) : Bool :=
  match parsePreKeyWire w with
  | some p => macChainOk' k P p
  | none => false

theorem macChainOk'_spec {k P : HwBytes} {p : PreKeyFields} (h : macChainOk' k P p = true) :
    (msgMac8' p).take 4 ≠ compTag4 ∧ keyOfTake8 (msgMac8' p) = some k ∧
      k.take 4 ≠ compTag4 ∧ keyOfTake8 (k.take 8) = some P := by
  simp only [macChainOk', Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem macChainOk'_of_wire {k P w : HwBytes} (h : wireMacChainOk' k P w = true)
    {p : PreKeyFields} (hp : parsePreKeyWire w = some p) : macChainOk' k P p = true := by
  unfold wireMacChainOk' at h; rw [hp] at h; exact h

theorem wireMacChainOk_ev4_fast : wireMacChainOk' wsMacKey wsPrk c1Fast = true := by
  decide +kernel

theorem wireMacChainOk_ev4 : wireMacChainOk' wsMacKey wsPrk ev4.input = true := by
  rw [ev4_input_eq_fast]; exact wireMacChainOk_ev4_fast

/-! ## Table-Backed SHA-256 / HMAC Back-Chaining for `c1` (`ev4` / `ev5`) -/

theorem padTail64_take32 (h : List (BitVec 8)) (hh : h.length = 32) :
    (padTail64 h).take 32 = h := by
  unfold padTail64; rw [List.append_assoc, List.append_assoc, List.take_left' hh]

theorem padTail64_length_32 (h : List (BitVec 8)) (hh : h.length = 32) :
    (padTail64 h).length = 64 := by
  simp only [padTail64, List.length_append, List.length_cons, List.length_nil,
    List.length_replicate, toBEBytes_length, hh]

def msg32OfTake8 (v : HwBytes) : Option HwBytes :=
  match rowOfTake8 v with
  | none => none
  | some r2 =>
    match rowOfTake8 (((leBytes 64 r2.2.1).take 32).take 8) with
    | none => none
    | some r_in2 => some ((leBytes 64 r_in2.2.1).take 32)

theorem msg32OfTake8_hmacWith_le64 (k m : HwBytes) (hk64 : k.length ≤ 64) (hm : m.length = 32)
    (h : (hmacWith F0 k m).take 4 ≠ compTag4) :
    msg32OfTake8 ((hmacWith F0 k m).take 8) = some m := by
  have hx5c := kblk_length k 0x5c hk64
  have hx36 := kblk_length k 0x36 hk64
  have h_in_untagged := hmac_inner_untagged k m hk64 h
  set inner := sha256With F0 (kblk k 0x36 ++ m) with hinner_def
  have hil : inner.length = 32 := sha256With_length F0 _
  have h_out := h
  rw [hmacWith_eq k m hk64, ← hinner_def] at h_out
  have hch_out : chunks64 (sha256Pad (kblk k 0x5c ++ inner)) = [kblk k 0x5c] ++ padTail64 inner :: [] := by
    rw [sha256Pad_append64 _ _ hx5c, chunks64_append64 _ _ hx5c, chunks64_padTail64_32 inner hil]; rfl
  have h2_out : OnTab ([kblk k 0x5c].foldl F0 sha256IV) (padTail64 inner) :=
    onTab_of_sha256With_untagged _ h_out [kblk k 0x5c] (padTail64 inner) [] hch_out
  rw [List.foldl_cons, List.foldl_nil] at h2_out
  obtain ⟨r2, hr2, _, hr2b, hF2_out⟩ := row_step h2_out
  have hsha_out : hmacWith F0 k m = digestOfOut r2.2.2 := by
    rw [hmacWith_eq k m hk64, ← hinner_def]
    unfold sha256With digestOfOut
    rw [hch_out, List.singleton_append, List.foldl_cons, List.foldl_cons, List.foldl_nil, hF2_out]
  have hblk_out : (leBytes 64 r2.2.1).take 32 = inner := by
    have hrt := leBytes_bytesToNat (padTail64 inner)
    rw [padTail64_length_32 inner hil] at hrt
    rw [hr2b, hrt, padTail64_take32 inner hil]
  have hch_in : chunks64 (sha256Pad (kblk k 0x36 ++ m)) = [kblk k 0x36] ++ padTail64 m :: [] := by
    rw [sha256Pad_append64 _ _ hx36, chunks64_append64 _ _ hx36, chunks64_padTail64_32 m hm]; rfl
  have h2_in : OnTab ([kblk k 0x36].foldl F0 sha256IV) (padTail64 m) :=
    onTab_of_sha256With_untagged _ h_in_untagged [kblk k 0x36] (padTail64 m) [] hch_in
  rw [List.foldl_cons, List.foldl_nil] at h2_in
  obtain ⟨r_in2, hr_in2, _, hr_in2b, hF2_in⟩ := row_step h2_in
  have hsha_in : inner = digestOfOut r_in2.2.2 := by
    rw [hinner_def]; unfold sha256With digestOfOut
    rw [hch_in, List.singleton_append, List.foldl_cons, List.foldl_cons, List.foldl_nil, hF2_in]
  have hblk_in : (leBytes 64 r_in2.2.1).take 32 = m := by
    have hrt := leBytes_bytesToNat (padTail64 m)
    rw [padTail64_length_32 m hm] at hrt
    rw [hr_in2b, hrt, padTail64_take32 m hm]
  have hfind_out : rowOfTake8 ((digestOfOut r2.2.2).take 8) = some r2 :=
    find?_eq_some_of_nodup compSha256Rows (fun r => (digestOfOut r.2.2).take 8)
      ((digestOfOut r2.2.2).take 8) rows_take8_nodup r2 hr2 rfl
  have hfind_in : rowOfTake8 (inner.take 8) = some r_in2 := by
    rw [hsha_in]
    exact find?_eq_some_of_nodup compSha256Rows (fun r => (digestOfOut r.2.2).take 8)
      ((digestOfOut r_in2.2.2).take 8) rows_take8_nodup r_in2 hr_in2 rfl
  rw [hsha_out]; unfold msg32OfTake8; simp only [hfind_out, hblk_out, hfind_in, hblk_in]

theorem msg32OfTake8_hmacWith_any (k m : HwBytes) (hm : m.length = 32)
    (h : (hmacWith F0 k m).take 4 ≠ compTag4) :
    msg32OfTake8 ((hmacWith F0 k m).take 8) = some m := by
  by_cases hk : 64 < k.length
  · have hlen : (sha256With F0 k).length = 32 := sha256With_length F0 k
    have hk' : ¬ 64 < (sha256With F0 k).length := by omega
    have heq : hmacWith F0 k m = hmacWith F0 (sha256With F0 k) m := by
      simp only [hmacWith, hk, hk', ↓reduceIte]
    rw [heq] at h ⊢
    exact msg32OfTake8_hmacWith_le64 (sha256With F0 k) m (by omega) hm h
  · exact msg32OfTake8_hmacWith_le64 k m (by omega) hm h

def wsSeed1Bytes : HwBytes := [0x04#8, 0xcb#8, 0xfe#8, 0x36#8, 0x49#8, 0xd9#8, 0x9f#8, 0xc1#8, 0x92#8, 0x91#8, 0xfc#8, 0x93#8, 0x9c#8, 0x35#8, 0x5b#8, 0x4f#8, 0x11#8, 0xc6#8, 0x19#8, 0x4e#8, 0x92#8, 0x6e#8, 0x3a#8, 0xde#8, 0x58#8, 0x5f#8, 0x32#8, 0xd7#8, 0x38#8, 0x46#8, 0x66#8, 0x1b#8]
def ckr0Bytes : HwBytes := [0xff#8, 0xd1#8, 0xd6#8, 0xb7#8, 0x4c#8, 0x1b#8, 0xf8#8, 0x4b#8, 0xd8#8, 0xc4#8, 0x97#8, 0x88#8, 0xb8#8, 0x07#8, 0x6a#8, 0xe9#8, 0x8c#8, 0x60#8, 0x61#8, 0x98#8, 0xb4#8, 0x0a#8, 0x8e#8, 0x05#8, 0x6a#8, 0x49#8, 0x70#8, 0x74#8, 0xee#8, 0x83#8, 0xbd#8, 0x55#8]
def whisperPrk0Bytes : HwBytes := [0xb2#8, 0x50#8, 0x7c#8, 0x15#8, 0x11#8, 0xd4#8, 0x0a#8, 0x5a#8, 0xa4#8, 0xbb#8, 0x98#8, 0xad#8, 0x3f#8, 0x64#8, 0x6d#8, 0x63#8, 0x37#8, 0x43#8, 0xd2#8, 0x74#8, 0x0f#8, 0x12#8, 0xc6#8, 0x68#8, 0x29#8, 0x08#8, 0x36#8, 0x05#8, 0xc0#8, 0x8d#8, 0x9c#8, 0x6a#8]
def rk0Bytes : HwBytes := [0x74#8, 0xe9#8, 0xaf#8, 0x1a#8, 0x58#8, 0x09#8, 0x70#8, 0x05#8, 0xb5#8, 0x77#8, 0x94#8, 0xbe#8, 0x51#8, 0x78#8, 0x72#8, 0x34#8, 0x6e#8, 0x3d#8, 0xb4#8, 0x1d#8, 0xba#8, 0x57#8, 0x2b#8, 0x69#8, 0x6c#8, 0xd6#8, 0x5a#8, 0x66#8, 0x32#8, 0x30#8, 0x99#8, 0xff#8]
def kRk0Bytes : HwBytes := [0xaa#8, 0x6c#8, 0x42#8, 0xbf#8, 0x23#8, 0x45#8, 0x25#8, 0xe1#8, 0xa8#8, 0x7d#8, 0xfa#8, 0xfd#8, 0xe6#8, 0x85#8, 0x3f#8, 0xcd#8, 0xfe#8, 0xc3#8, 0x72#8, 0xcd#8, 0x94#8, 0xac#8, 0x11#8, 0x7a#8, 0x05#8, 0x7e#8, 0x7c#8, 0x35#8, 0x52#8, 0xd9#8, 0x69#8, 0x37#8]

theorem c1_kdf_pins :
    wsPrk.take 4 ≠ compTag4 ∧
    msg32OfTake8 (wsPrk.take 8) = some wsSeed1Bytes ∧
    wsSeed1Bytes.take 4 ≠ compTag4 ∧
    keyOfTake8 (wsSeed1Bytes.take 8) = some ckr0Bytes ∧
    ckr0Bytes.take 4 ≠ compTag4 ∧
    keyOfTake8 (ckr0Bytes.take 8) = some whisperPrk0Bytes ∧
    whisperPrk0Bytes.take 4 ≠ compTag4 ∧
    keyOfTake8 (whisperPrk0Bytes.take 8) = some rk0Bytes ∧
    rk0Bytes.take 4 ≠ compTag4 ∧
    keyOfTake8 (rk0Bytes.take 8) = some kRk0Bytes := by
  decide +kernel

def whisperRatchetBlock1Bytes : HwBytes :=
  [0x57#8, 0x68#8, 0x69#8, 0x73#8, 0x70#8, 0x65#8, 0x72#8, 0x52#8,
   0x61#8, 0x74#8, 0x63#8, 0x68#8, 0x65#8, 0x74#8, 0x01#8]

theorem rk0Bytes_ne_whisperRatchetBlock1 :
    hmacWith F0 kRk0Bytes whisperRatchetBlock1Bytes ≠ rk0Bytes := by
  decide +kernel

theorem gamma_whisperRatchet_block1 {S : OpaqueSymbolSemantics} {g : Ghost} :
    gamma compI0 S g
      (Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperRatchet")
        (DY.Libsignal.TripleRatchet.litByte 0x01)) = whisperRatchetBlock1Bytes := by
  have hs : "WhisperRatchet".toUTF8 = "WhisperRatchet".toList.utf8Encode := by
    conv_lhs => rw [← String.ofList_toList (s := "WhisperRatchet")]
    rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList]
  rw [Symbolic.BugInjection.Proofs.Common443.CompRBobInit.gamma_concat0]
  unfold DY.Libsignal.TripleRatchet.lit DY.Libsignal.TripleRatchet.litByte
  rw [Symbolic.BugInjection.Proofs.Common443.CompRBobInit.gamma_lit0,
      Symbolic.BugInjection.Proofs.Common443.CompRBobInit.gamma_lit0, hs]
  decide +kernel

theorem not_hkdfBlock1_whisperRatchet_eq_rk0Bytes
    {S : OpaqueSymbolSemantics} {g : Ghost} (u v : DY.Bytes) :
    gamma compI0 S g
      (DY.Libsignal.TripleRatchet.hkdfBlock1 (DY.Libsignal.TripleRatchet.hmac u v)
        (DY.Libsignal.TripleRatchet.lit "WhisperRatchet")) ≠ rk0Bytes := by
  intro heq
  unfold DY.Libsignal.TripleRatchet.hkdfBlock1 at heq
  have hprkLen : (gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac u v)).length = 32 :=
    gamma_hmac_length S g u v
  have htag : (gamma compI0 S g
      (DY.Libsignal.TripleRatchet.hmac (DY.Libsignal.TripleRatchet.hmac u v)
        (Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperRatchet")
          (DY.Libsignal.TripleRatchet.litByte 0x01)))).take 4 ≠ compTag4 := by
    rw [heq]; exact c1_kdf_pins.2.2.2.2.2.2.2.2.1
  have hk := gamma_hmac_key_of_take8 S g (DY.Libsignal.TripleRatchet.hmac u v) _ hprkLen htag
  rw [heq, c1_kdf_pins.2.2.2.2.2.2.2.2.2] at hk
  have hprk : gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac u v) = kRk0Bytes :=
    (Option.some.inj hk).symm
  rw [gamma_hmac_compI0, hprk, gamma_whisperRatchet_block1] at heq
  exact rk0Bytes_ne_whisperRatchetBlock1 heq

theorem c1_ratchet_mac_forces_rk0Bytes
    {S : OpaqueSymbolSemantics} {g : Ghost}
    {rk dh pqSalt peerIk myIk wire : DY.Bytes}
    (hmac : gamma compI0 S g
      (DY.Libsignal.TripleRatchet.computeMac
        (DY.Libsignal.TripleRatchet.trMsgKeys pqSalt
          (DY.Libsignal.TripleRatchet.kdfCk
            (DY.Libsignal.TripleRatchet.hkdfBlock2 (DY.Libsignal.TripleRatchet.hmac rk dh)
              (DY.Libsignal.TripleRatchet.lit "WhisperRatchet"))).2).macKey
        peerIk myIk wire) = msgMac8' p_c1)
    (hrkLen : (gamma compI0 S g rk).length = 32) :
    gamma compI0 S g rk = rk0Bytes := by
  set wPrk := DY.Libsignal.TripleRatchet.hmac rk dh
  set ckr := DY.Libsignal.TripleRatchet.hkdfBlock2 wPrk (DY.Libsignal.TripleRatchet.lit "WhisperRatchet")
  set seed := (DY.Libsignal.TripleRatchet.kdfCk ckr).2
  set mKeys := DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed
  obtain ⟨hMacTag, hMacKey, hKeyTag, hKeyPrk⟩ :=
    macChainOk'_spec (macChainOk'_of_wire wireMacChainOk_ev4 parsePreKeyWire_ev4)
  have htag1 : (gamma compI0 S g (DY.Libsignal.TripleRatchet.computeMac mKeys.macKey peerIk myIk wire)).take 4 ≠ compTag4 := by
    rw [hmac]; exact hMacTag
  have hk1 := keyOfTake8_computeMac S g mKeys.macKey peerIk myIk wire (gamma_macKey_length S g pqSalt seed) htag1
  rw [hmac, hMacKey] at hk1
  have hmKeyEq : gamma compI0 S g mKeys.macKey = wsMacKey := (Option.some.inj hk1).symm
  have htag2 : (gamma compI0 S g mKeys.macKey).take 4 ≠ compTag4 := by
    rw [hmKeyEq]; exact hKeyTag
  have hk2 := keyOfTake8_macKey S g pqSalt seed htag2
  rw [hmKeyEq, hKeyPrk] at hk2
  have hPrkEq : gamma compI0 S g (msgPrk pqSalt seed) = wsPrk := (Option.some.inj hk2).symm
  have hSeedLen : (gamma compI0 S g seed).length = 32 :=
    gamma_hmac_length S g ckr (DY.Libsignal.TripleRatchet.litByte 0x01)
  have hPrkTag : (hmacWith F0 (gamma compI0 S g pqSalt) (gamma compI0 S g seed)).take 4 ≠ compTag4 := by
    rw [← gamma_hmac_compI0]; change (gamma compI0 S g (msgPrk pqSalt seed)).take 4 ≠ compTag4
    rw [hPrkEq]; exact c1_kdf_pins.1
  have hmSeed := msg32OfTake8_hmacWith_any (gamma compI0 S g pqSalt) (gamma compI0 S g seed) hSeedLen hPrkTag
  rw [← gamma_hmac_compI0] at hmSeed
  change msg32OfTake8 ((gamma compI0 S g (msgPrk pqSalt seed)).take 8) = _ at hmSeed
  rw [hPrkEq, c1_kdf_pins.2.1] at hmSeed
  have hSeedEq : gamma compI0 S g seed = wsSeed1Bytes := (Option.some.inj hmSeed).symm
  have hCkrLen : (gamma compI0 S g ckr).length = 32 :=
    gamma_hmac_length S g wPrk _
  have hSeedTag : (gamma compI0 S g seed).take 4 ≠ compTag4 := by
    rw [hSeedEq]; exact c1_kdf_pins.2.2.1
  have hkCkr := gamma_hmac_key_of_take8 S g ckr (DY.Libsignal.TripleRatchet.litByte 0x01) hCkrLen hSeedTag
  change keyOfTake8 ((gamma compI0 S g seed).take 8) = _ at hkCkr
  rw [hSeedEq, c1_kdf_pins.2.2.2.1] at hkCkr
  have hCkrEq : gamma compI0 S g ckr = ckr0Bytes := (Option.some.inj hkCkr).symm
  have hWPrkLen : (gamma compI0 S g wPrk).length = 32 := gamma_hmac_length S g rk dh
  have hCkrTag : (gamma compI0 S g ckr).take 4 ≠ compTag4 := by
    rw [hCkrEq]; exact c1_kdf_pins.2.2.2.2.1
  have hkWPrk := gamma_hmac_key_of_take8 S g wPrk _ hWPrkLen hCkrTag
  change keyOfTake8 ((gamma compI0 S g ckr).take 8) = _ at hkWPrk
  rw [hCkrEq, c1_kdf_pins.2.2.2.2.2.1] at hkWPrk
  have hWPrkEq : gamma compI0 S g wPrk = whisperPrk0Bytes := (Option.some.inj hkWPrk).symm
  have hWPrkTag : (gamma compI0 S g wPrk).take 4 ≠ compTag4 := by
    rw [hWPrkEq]; exact c1_kdf_pins.2.2.2.2.2.2.1
  have hkRk := gamma_hmac_key_of_take8 S g rk dh hrkLen hWPrkTag
  change keyOfTake8 ((gamma compI0 S g wPrk).take 8) = _ at hkRk
  rw [hWPrkEq, c1_kdf_pins.2.2.2.2.2.2.2.1] at hkRk
  exact (Option.some.inj hkRk).symm

theorem no_runRejected_ev0 : ¬ RunRejected ev0 := fun h => h _ rfl
theorem no_runRejected_ev1 : ¬ RunRejected ev1 := fun h => h _ rfl
theorem no_runRejected_ev2 : ¬ RunRejected ev2 := fun h => h _ rfl
theorem no_runRejected_ev3 : ¬ RunRejected ev3 := fun h => h _ rfl
theorem no_runRejected_ev4 : ¬ RunRejected ev4 := fun h => h _ rfl
theorem no_runRejected_ev5 : ¬ RunRejected ev5 := fun h => h _ rfl

theorem invisible_step_eq_network {s : Step} (h : s.cls = .invisible) :
    ∃ t, s = .network t := by
  cases s <;> simp [Step.cls] at h
  exact ⟨_, rfl⟩

theorem matchesEventsAt_run_of_not_rejected
    {i : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {ss : List Step}
    {ev : RunEvent} {evs : List CliEvent} {vis : List VisEntry}
    (hNotRej : ¬ RunRejected ev)
    (hM : MatchesEventsAt i r S g initIds tr ss (.run ev :: evs) vis) :
    ∃ pre s ss' v vs,
      ss = pre ++ s :: ss' ∧
      vis = v ++ vs ∧
      (∀ x ∈ pre, x.cls = .invisible) ∧
      RunMatches i r S g (runSteps pre tr) s ev v initIds ∧
      MatchesEventsAt i r S g (nextBundleIds initIds ev) (s.next (runSteps pre tr)) ss' evs vs := by
  cases hM with
  | run1 hInv hRun hRest => exact ⟨_, _, _, _, _, rfl, rfl, hInv, hRun, hRest⟩
  | run0 _ hRej _ => exact False.elim (hNotRej hRej)

theorem step_of_init_alice {r : ProtocolSetup} {s : Step}
    (hb : r.bob = "bob")
    (hp : s.party? = some "alice")
    (hc : ∀ addr bdl, ev0.cmd = .init addr bdl → s.FitsCmd (.init addr bdl))
    (hm : s.MatchesSetupPeer r) :
    ∃ idStateIdx regIdxB h, s = .aliceStart "alice" "bob" idStateIdx regIdxB h := by
  have hc' := hc ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ "bundle" rfl
  cases s <;> simp [Step.FitsCmd, Step.party?, Step.MatchesSetupPeer] at hc' hp hm
  subst hp; rw [hb] at hm; subst hm
  exact ⟨_, _, _, rfl⟩

theorem step_of_send_alice {s : Step}
    (hp : s.party? = some "alice")
    (hc : s.FitsCmd ev1.cmd) :
    (∃ stateIdx coinsLen pqIdx, s = .messageEncrypt "alice" stateIdx coinsLen pqIdx) ∨
    (∃ stateIdx, s = .messageEncryptAbort "alice" stateIdx) := by
  have hc' : ev1.cmd = .send ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ := rfl
  rw [hc'] at hc
  cases s <;> simp [Step.FitsCmd, Step.party?] at hc hp
  · subst hp; exact Or.inl ⟨_, _, _, rfl⟩
  · subst hp; exact Or.inr ⟨_, rfl⟩

theorem step_of_recv_bob {r : ProtocolSetup} {s : Step}
    (ha : r.alice = "alice")
    (hp : s.party? = some "bob")
    (hc : s.FitsCmd ev3.cmd)
    (hm : s.MatchesSetupPeer r) :
    (∃ kh regIdxA mh pqIdx spqrMsgIdx, s = .bobStart "bob" "alice" kh regIdxA mh pqIdx spqrMsgIdx) ∨
    (∃ stateIdx msgIdx pqIdx spqrMsgIdx, s = .messageDecrypt "bob" stateIdx msgIdx pqIdx spqrMsgIdx) ∨
    (∃ stateIdx msgIdx skIdx pqIdx spqrMsgIdx,
      s = .messageDecryptSkipped "bob" stateIdx msgIdx skIdx pqIdx spqrMsgIdx) := by
  have hc' : ev3.cmd = .recv ⟨"8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b", 1⟩ := rfl
  rw [hc'] at hc
  cases s <;> simp [Step.FitsCmd, Step.party?, Step.MatchesSetupPeer] at hc hp hm
  · subst hp; rw [ha] at hm; subst hm; exact Or.inl ⟨_, _, _, _, _, rfl⟩
  · subst hp; exact Or.inr (Or.inl ⟨_, _, _, _, rfl⟩)
  · subst hp; exact Or.inr (Or.inr ⟨_, _, _, _, _, rfl⟩)

/-! ## Core Disproof Obligations -/

theorem stepIn_next (c : _root_.DY.ReachabilityConfig)
    [i : _root_.DY.ReachabilityConfig.HasStep c reachability]
    (x : c.Input) (tr : ExecTrace) :
    ((reachability.step (stepIn c x)).2.run tr).2.val = ((c.step x).2.run tr).2.val :=
  congrArg (fun s => (s.2.run tr).2.val) (i.pf_step x).symm

theorem stepIn_ok (c : _root_.DY.ReachabilityConfig)
    [i : _root_.DY.ReachabilityConfig.HasStep c reachability]
    (x : c.Input) (tr : ExecTrace) :
    ((reachability.step (stepIn c x)).2.run tr).1.isSome = ((c.step x).2.run tr).1.isSome :=
  congrArg (fun s => (s.2.run tr).1.isSome) (i.pf_step x).symm


end
end Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay
