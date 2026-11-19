/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Synthetic.Witnesses.UnackPrekeyOmittedCli
public import Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.CliBridge
public import Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable

/-!
# Shared Definitions for `synthetic-unack-prekey-omitted-cli` Spec-Half Disproof

Defines `uoSetup`, `uoSendOut` (recorded witness Call-1 stdout), `uoCarrierSendOut` and
`uoCarrierTrace` (carrier Call-1 stdout/trace under `(compI0, compHooks0)`, definitionally equal
to `ImplTrace.uoCarrierTrace`), `evInit`, parameterized `evSend (out1 : HwBytes)` and
`uoEvents (out1 : HwBytes)`, trace/schedule bridge lemmas, and `cliCompFitsPinned_satisfiable_uo`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticUnackPrekeyOmitted.Defs

open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (CliEvent RunEvent)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.PQXDH.Refinement (wirePrekeyTag)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open Symbolic.Proofs.Swarm.UA.Defs (callsOf SchedFits)
open Symbolic.Proofs.Swarm.UA.ClassicalBridge (BreakFree breakFree_nil)
open Symbolic.BugInjection
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
  (CliSetupMatchesPinned cliSetupMatchesPinned_satisfiable_of_plausible)
open Symbolic.BugInjection.Proofs.Common443
open Symbolic.BugInjection.Proofs.Common443.CompI0Laws (compI0_kyberCorrectOn)
open Symbolic.BugInjection.Proofs.Common443.CliCoinSplitClose (cliCoins0)
open Symbolic.BugInjection.Proofs.Common443.CliEventBridge (breakFree_cons_run)
open Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443 (compI0)
open Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.CliBridge (nil_eq_hexBytes)

abbrev uoSetup : PQXDHSpqrSetup :=
  Symbolic.BugInjection.Synthetic.Witnesses.UnackPrekeyOmittedCli.setup

theorem uoSetup_eq :
    uoSetup = Symbolic.BugInjection.Synthetic.Witnesses.UnackPrekeyOmittedCli.setup := rfl

/-- Alice's recorded Call 1 (`send`) stdout on the witness: a 106-byte `0x02` (`wireWhisperTag`)
frame omitting the unacknowledged `0x03` (`PreKeySignalMessage`) wrapper. -/
def uoSendOut : HwBytes := [
  0x02#8, 0x44#8, 0x0a#8, 0x21#8, 0x05#8, 0x5b#8, 0xfc#8, 0x85#8, 0xa3#8, 0xb0#8, 0x8f#8, 0x59#8,
  0x13#8, 0x72#8, 0x40#8, 0xd4#8, 0x2f#8, 0xa1#8, 0x30#8, 0x80#8, 0x96#8, 0xa3#8, 0x73#8, 0x10#8,
  0xc8#8, 0x6b#8, 0x3a#8, 0xe2#8, 0xbc#8, 0x82#8, 0x0d#8, 0x6f#8, 0x0a#8, 0x37#8, 0xbf#8, 0xd3#8,
  0x3f#8, 0x10#8, 0x00#8, 0x18#8, 0x00#8, 0x22#8, 0x10#8, 0xfc#8, 0xa4#8, 0xe8#8, 0x7c#8, 0x39#8,
  0xd3#8, 0x9d#8, 0x1f#8, 0x29#8, 0xf4#8, 0x10#8, 0x85#8, 0xec#8, 0x2a#8, 0x6c#8, 0x7c#8, 0x2a#8,
  0x25#8, 0x01#8, 0x01#8, 0x01#8, 0x01#8, 0x00#8, 0xa5#8, 0x18#8, 0x12#8, 0x8c#8, 0xbc#8, 0x63#8,
  0xe0#8, 0x38#8, 0x16#8, 0x4b#8, 0x14#8, 0x44#8, 0xfc#8, 0x00#8, 0xf0#8, 0x20#8, 0x30#8, 0xc1#8,
  0xec#8, 0xf9#8, 0x8b#8, 0x52#8, 0x80#8, 0xe7#8, 0x4c#8, 0x17#8, 0x97#8, 0xe9#8, 0x0f#8, 0xdd#8,
  0x8c#8, 0x0b#8, 0x00#8, 0x52#8, 0x4f#8, 0x80#8, 0xf9#8, 0xa9#8, 0x82#8, 0x21#8
]

/-- Carrier Call 1 (`send`) stdout produced by the mutant ELF under `(compI0, compHooks0)`:
identical to `uoSendOut` on bytes `0..98`, with the 8-byte off-table MAC `d7d7d7d736084858`
on bytes `98..106`. Definitionally `rfl`-equal to `ImplTrace.c1Out`. -/
def uoCarrierSendOut : HwBytes := [
  0x02#8, 0x44#8, 0x0a#8, 0x21#8, 0x05#8, 0x5b#8, 0xfc#8, 0x85#8, 0xa3#8, 0xb0#8, 0x8f#8, 0x59#8,
  0x13#8, 0x72#8, 0x40#8, 0xd4#8, 0x2f#8, 0xa1#8, 0x30#8, 0x80#8, 0x96#8, 0xa3#8, 0x73#8, 0x10#8,
  0xc8#8, 0x6b#8, 0x3a#8, 0xe2#8, 0xbc#8, 0x82#8, 0x0d#8, 0x6f#8, 0x0a#8, 0x37#8, 0xbf#8, 0xd3#8,
  0x3f#8, 0x10#8, 0x00#8, 0x18#8, 0x00#8, 0x22#8, 0x10#8, 0xfc#8, 0xa4#8, 0xe8#8, 0x7c#8, 0x39#8,
  0xd3#8, 0x9d#8, 0x1f#8, 0x29#8, 0xf4#8, 0x10#8, 0x85#8, 0xec#8, 0x2a#8, 0x6c#8, 0x7c#8, 0x2a#8,
  0x25#8, 0x01#8, 0x01#8, 0x01#8, 0x01#8, 0x00#8, 0xa5#8, 0x18#8, 0x12#8, 0x8c#8, 0xbc#8, 0x63#8,
  0xe0#8, 0x38#8, 0x16#8, 0x4b#8, 0x14#8, 0x44#8, 0xfc#8, 0x00#8, 0xf0#8, 0x20#8, 0x30#8, 0xc1#8,
  0xec#8, 0xf9#8, 0x8b#8, 0x52#8, 0x80#8, 0xe7#8, 0x4c#8, 0x17#8, 0x97#8, 0xe9#8, 0x0f#8, 0xdd#8,
  0x8c#8, 0x0b#8, 0xd7#8, 0xd7#8, 0xd7#8, 0xd7#8, 0x36#8, 0x08#8, 0x48#8, 0x58#8
]

section FastUoSendOut

attribute [local irreducible] Symbolic.BugInjection.hexBytes

private def uoSendOutHexStr : String :=
  "02440a21055bfc85a3b08f59137240d42fa1308096a37310c86b3ae2bc820d6f0a37bfd33f100018002210fca4e87c39d39d1f29f41085ec2a6c7c2a250101010100a518128cbc63e038164b1444fc00f02030c1ecf98b5280e74c1797e90fdd8c0b00524f80f9a98221"

private def uoSendOutChars : List Char := [
  '0', '2', '4', '4', '0', 'a', '2', '1', '0', '5', '5', 'b', 'f', 'c', '8', '5',
  'a', '3', 'b', '0', '8', 'f', '5', '9', '1', '3', '7', '2', '4', '0', 'd', '4',
  '2', 'f', 'a', '1', '3', '0', '8', '0', '9', '6', 'a', '3', '7', '3', '1', '0',
  'c', '8', '6', 'b', '3', 'a', 'e', '2', 'b', 'c', '8', '2', '0', 'd', '6', 'f',
  '0', 'a', '3', '7', 'b', 'f', 'd', '3', '3', 'f', '1', '0', '0', '0', '1', '8',
  '0', '0', '2', '2', '1', '0', 'f', 'c', 'a', '4', 'e', '8', '7', 'c', '3', '9',
  'd', '3', '9', 'd', '1', 'f', '2', '9', 'f', '4', '1', '0', '8', '5', 'e', 'c',
  '2', 'a', '6', 'c', '7', 'c', '2', 'a', '2', '5', '0', '1', '0', '1', '0', '1',
  '0', '1', '0', '0', 'a', '5', '1', '8', '1', '2', '8', 'c', 'b', 'c', '6', '3',
  'e', '0', '3', '8', '1', '6', '4', 'b', '1', '4', '4', '4', 'f', 'c', '0', '0',
  'f', '0', '2', '0', '3', '0', 'c', '1', 'e', 'c', 'f', '9', '8', 'b', '5', '2',
  '8', '0', 'e', '7', '4', 'c', '1', '7', '9', '7', 'e', '9', '0', 'f', 'd', 'd',
  '8', 'c', '0', 'b', '0', '0', '5', '2', '4', 'f', '8', '0', 'f', '9', 'a', '9',
  '8', '2', '2', '1'
]

private theorem uoSendOutHexStr_eq : uoSendOutHexStr = String.ofList uoSendOutChars := rfl

private theorem uoSendOut_eq_go :
    uoSendOut = hexBytes.go CompRPlantWire.hexDigit uoSendOutChars := rfl

theorem uoSendOut_eq_hex :
    uoSendOut =
      hexBytes "02440a21055bfc85a3b08f59137240d42fa1308096a37310c86b3ae2bc820d6f0a37bfd33f100018002210fca4e87c39d39d1f29f41085ec2a6c7c2a250101010100a518128cbc63e038164b1444fc00f02030c1ecf98b5280e74c1797e90fdd8c0b00524f80f9a98221" := by
  change uoSendOut = hexBytes uoSendOutHexStr
  rw [uoSendOutHexStr_eq, CompRPlantWire.hexBytes_ofList, uoSendOut_eq_go]

private def uoCarrierSendOutHexStr : String :=
  "02440a21055bfc85a3b08f59137240d42fa1308096a37310c86b3ae2bc820d6f0a37bfd33f100018002210fca4e87c39d39d1f29f41085ec2a6c7c2a250101010100a518128cbc63e038164b1444fc00f02030c1ecf98b5280e74c1797e90fdd8c0bd7d7d7d736084858"

private def uoCarrierSendOutChars : List Char := [
  '0', '2', '4', '4', '0', 'a', '2', '1', '0', '5', '5', 'b', 'f', 'c', '8', '5',
  'a', '3', 'b', '0', '8', 'f', '5', '9', '1', '3', '7', '2', '4', '0', 'd', '4',
  '2', 'f', 'a', '1', '3', '0', '8', '0', '9', '6', 'a', '3', '7', '3', '1', '0',
  'c', '8', '6', 'b', '3', 'a', 'e', '2', 'b', 'c', '8', '2', '0', 'd', '6', 'f',
  '0', 'a', '3', '7', 'b', 'f', 'd', '3', '3', 'f', '1', '0', '0', '0', '1', '8',
  '0', '0', '2', '2', '1', '0', 'f', 'c', 'a', '4', 'e', '8', '7', 'c', '3', '9',
  'd', '3', '9', 'd', '1', 'f', '2', '9', 'f', '4', '1', '0', '8', '5', 'e', 'c',
  '2', 'a', '6', 'c', '7', 'c', '2', 'a', '2', '5', '0', '1', '0', '1', '0', '1',
  '0', '1', '0', '0', 'a', '5', '1', '8', '1', '2', '8', 'c', 'b', 'c', '6', '3',
  'e', '0', '3', '8', '1', '6', '4', 'b', '1', '4', '4', '4', 'f', 'c', '0', '0',
  'f', '0', '2', '0', '3', '0', 'c', '1', 'e', 'c', 'f', '9', '8', 'b', '5', '2',
  '8', '0', 'e', '7', '4', 'c', '1', '7', '9', '7', 'e', '9', '0', 'f', 'd', 'd',
  '8', 'c', '0', 'b', 'd', '7', 'd', '7', 'd', '7', 'd', '7', '3', '6', '0', '8',
  '4', '8', '5', '8'
]

private theorem uoCarrierSendOutHexStr_eq :
    uoCarrierSendOutHexStr = String.ofList uoCarrierSendOutChars := rfl

private theorem uoCarrierSendOut_eq_go :
    uoCarrierSendOut = hexBytes.go CompRPlantWire.hexDigit uoCarrierSendOutChars := rfl

theorem uoCarrierSendOut_eq_hex :
    uoCarrierSendOut =
      hexBytes "02440a21055bfc85a3b08f59137240d42fa1308096a37310c86b3ae2bc820d6f0a37bfd33f100018002210fca4e87c39d39d1f29f41085ec2a6c7c2a250101010100a518128cbc63e038164b1444fc00f02030c1ecf98b5280e74c1797e90fdd8c0bd7d7d7d736084858" := by
  change uoCarrierSendOut = hexBytes uoCarrierSendOutHexStr
  rw [uoCarrierSendOutHexStr_eq, CompRPlantWire.hexBytes_ofList, uoCarrierSendOut_eq_go]

end FastUoSendOut

attribute [local irreducible] Symbolic.BugInjection.hexBytes

theorem uoSendOut_head? : uoSendOut.head? = some 0x02#8 := rfl

theorem uoSendOut_head_eq_whisper : uoSendOut.head? = some wireWhisperTag := rfl

theorem uoSendOut_head_ne_prekey : uoSendOut.head? ≠ some wirePrekeyTag := by decide

theorem uoCarrierSendOut_head? : uoCarrierSendOut.head? = some 0x02#8 := rfl

theorem uoCarrierSendOut_head_eq_whisper : uoCarrierSendOut.head? = some wireWhisperTag := rfl

theorem uoCarrierSendOut_head_ne_prekey : uoCarrierSendOut.head? ≠ some wirePrekeyTag := by decide

/-- Helper indexing `UnackPrekeyOmittedCli.trace` identically to `ImplTrace.rawRunAt`. -/
def rawRunAt (k : Nat) : RunEvent :=
  match Symbolic.BugInjection.Synthetic.Witnesses.UnackPrekeyOmittedCli.trace[k]? with
  | some (.run ev) => ev
  | _ => { party := "", cmd := .send ⟨"", 0⟩, input := [], coins := [], exit := none }

/-- Carrier 2-call CLI trace produced by the mutant binary under `(compI0, compHooks0)`:
definitionally `rfl`-equal to `ImplTrace.uoCarrierTrace`. -/
def uoCarrierTrace : List CliEvent :=
  [ .run { (rawRunAt 0) with exit := some (0, []) },
    .run { (rawRunAt 1) with exit := some (0, uoCarrierSendOut) } ]

def evInit : RunEvent :=
  { party := "alice"
    cmd := .init ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ "bundle"
    input := CompRX0SS38.bunBytes
    coins := cliCoins0
    exit := some (0, []) }

theorem evInit_eq_cliBridge :
    evInit = Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.CliBridge.evInit :=
  rfl

/-- Parameterized Call 1 (`send` Alice `"hello bob"`) with exit stdout `out1`. -/
def evSend (out1 : HwBytes) : RunEvent :=
  { party := "alice"
    cmd := .send ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩
    input := CompRX0SS38.ptB
    coins := CompRX0SS38.cB
    exit := some (0, out1) }

theorem runWrapped_evSend {out1 : HwBytes} (h : out1.head? = some 0x02#8) :
    runWrapped (evSend out1) = false := by
  unfold runWrapped evSend
  dsimp only
  rw [h]
  decide

theorem runWrapped_evSend_uoSendOut : runWrapped (evSend uoSendOut) = false := rfl

theorem runWrapped_evSend_uoCarrierSendOut : runWrapped (evSend uoCarrierSendOut) = false := rfl

/-- Parameterized 2-call CLI trace `[.run evInit, .run (evSend out1)]`. -/
def uoEvents (out1 : HwBytes) : List CliEvent :=
  [.run evInit, .run (evSend out1)]

theorem uoEvents_eq :
    uoEvents uoSendOut = Symbolic.BugInjection.Synthetic.Witnesses.UnackPrekeyOmittedCli.trace := by
  unfold uoEvents evInit evSend cliCoins0
    Symbolic.BugInjection.Synthetic.Witnesses.UnackPrekeyOmittedCli.trace
  rw [CompRX0SS38.bunBytes_eq_hex, CompRX0SS38.ptB_eq_hex, CompRX0SS38.cB_eq_hex,
    uoSendOut_eq_hex, nil_eq_hexBytes]

theorem uoEvents_carrier_eq :
    uoEvents uoCarrierSendOut = uoCarrierTrace := by
  unfold uoEvents evInit evSend cliCoins0 uoCarrierTrace rawRunAt
    Symbolic.BugInjection.Synthetic.Witnesses.UnackPrekeyOmittedCli.trace
  dsimp only [List.getElem?_cons_zero, List.getElem?_cons_succ]
  rw [CompRX0SS38.bunBytes_eq_hex, CompRX0SS38.ptB_eq_hex, CompRX0SS38.cB_eq_hex]

theorem breakFree_evInit : BreakFree [.run evInit] :=
  breakFree_cons_run _ breakFree_nil

theorem breakFree_uoEvents (out1 : HwBytes) : BreakFree (uoEvents out1) :=
  breakFree_cons_run _ (breakFree_cons_run _ breakFree_nil)

theorem callsOf_evInit :
    callsOf [.run evInit] = [("alice", true)] := rfl

theorem callsOf_uoEvents (out1 : HwBytes) :
    callsOf (uoEvents out1) = [("alice", true), ("alice", true)] := rfl

set_option linter.unnecessarySeqFocus false in
theorem schedFits_evInit :
    SchedFits (callsOf [.run evInit])
      Witnesses.Cheval26SmallSubgroupHighBitComp.who
      Witnesses.Cheval26SmallSubgroupHighBitComp.ok := by
  rw [callsOf_evInit]
  refine ⟨by decide, fun k p b hget => ?_⟩
  rcases k with _ | k <;> simp at hget <;> obtain ⟨rfl, rfl⟩ := hget <;> rfl

set_option linter.unnecessarySeqFocus false in
theorem schedFits_uoEvents (out1 : HwBytes) :
    SchedFits (callsOf (uoEvents out1))
      Witnesses.Cheval26SmallSubgroupHighBitComp.who
      Witnesses.Cheval26SmallSubgroupHighBitComp.ok := by
  rw [callsOf_uoEvents]
  refine ⟨by decide, fun k p b hget => ?_⟩
  rcases k with _ | _ | k <;> simp at hget <;> obtain ⟨rfl, rfl⟩ := hget <;> rfl

theorem list_eq_two_splits {α : Type} {a b x : α} {xs ys : List α}
    (h : [a, b] = xs ++ x :: ys) :
    (xs = [] ∧ x = a ∧ ys = [b]) ∨
    (xs = [a] ∧ x = b ∧ ys = []) := by
  rcases xs with _ | ⟨x₀, _ | ⟨x₁, xs⟩⟩
  · simp at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inl ⟨rfl, rfl, rfl⟩
  · simp at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact Or.inr ⟨rfl, rfl, rfl⟩
  · simp at h

theorem compFitsPinned_hb_of_uo {r : ProtocolSetup}
    (h : compFitsPinned uoSetup compI0 r) :
    compFitsPinned Witnesses.Cheval26SmallSubgroupHighBitComp.setup compI0 r := by
  obtain ⟨⟨hwf, hopk, hra, hrb, hspk, hkpk, hs0, hs1, hs2, ho5, ho6, ho7, hsec, hcryp, hcan, _⟩,
    hi, hsec35, hpart, htorRej, _⟩ := h
  exact ⟨⟨hwf, hopk, hra, hrb, hspk, hkpk, hs0, hs1, hs2, ho5, ho6, ho7, hsec, hcryp, hcan,
    compI0_kyberCorrectOn r _⟩, hi, hsec35, hpart, htorRej, fun _ hm => nomatch hm⟩

theorem cliCompFitsPinned_satisfiable_uo :
    ∃ iw r, CliSetupMatchesPinned uoSetup iw r :=
  cliSetupMatchesPinned_satisfiable_of_plausible
    uoSetup
    (by decide +kernel)
    (fun _ h => nomatch h)

end Symbolic.BugInjection.Proofs.SyntheticUnackPrekeyOmitted.Defs
