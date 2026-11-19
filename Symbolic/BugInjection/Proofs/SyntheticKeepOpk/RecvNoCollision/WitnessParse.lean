/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import Lean
public import Symbolic.BugInjection.Synthetic.Witnesses.KeepOpkCli
public import Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
public import Symbolic.Proofs.Tests.CliNonvacuity.RecvNoCollisionAux

/-!
# Concrete Trace and Wire Parsing Facts for `KeepOpkCli` (`WitnessParse.lean`)

Extracts the 6 `RunEvent`s `ev 0 .. ev 5` of `KeepOpkCli.trace` without unfolding `hexBytes`
globally, and proves fast kernel-checked parsing, coin, bundle, and byte-level facts for Alice's
`.init`/`.send` calls (`ev 0, 1, 3, 4`) and Bob's `.recv` calls (`ev 2, 5`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.WitnessParse

open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (RunEvent CliEvent)
open DY.Libsignal.PQXDH.Refinement (wirePrekeyTag preKeyBundleByteLength)
open DY.Libsignal.Composed.Refinement
  (PreKeyFields BundlePreKeyIds parsePreKey parsePreKeyWire decodePreKey bundlePreKeyIds
   nextBundleIds preKeySpqrIndex kyberKey slice RunRejected runWrapped)
open Symbolic.BugInjection (PQXDHSpqrSetup hexBytes)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compTag4 compKyberEncaps)
open Symbolic.Proofs.Tests.CliNonvacuity.RecvNoCollisionAux (noRecvEvent)

/-- Witness setup of `KeepOpkCli`. -/
abbrev w0 : PQXDHSpqrSetup := Symbolic.BugInjection.Synthetic.Witnesses.KeepOpkCli.setup

/-- Witness CLI trace of `KeepOpkCli` (6 `.run` events, indices `0..5`). -/
abbrev trace0 : List CliEvent := Symbolic.BugInjection.Synthetic.Witnesses.KeepOpkCli.trace

def hexDigit (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10

theorem hexBytes_ofList (cs : List Char) :
    hexBytes (String.ofList cs) = hexBytes.go hexDigit cs := by
  unfold hexBytes hexDigit
  rw [String.toList_ofList]

theorem hexBytes_go_length :
    ∀ cs : List Char, (hexBytes.go hexDigit cs).length = cs.length / 2
  | [] => by simp [hexBytes.go]
  | [_] => by simp [hexBytes.go]
  | _ :: _ :: rest => by
    simp only [hexBytes.go, List.length_cons, hexBytes_go_length rest]
    omega

attribute [local irreducible] Symbolic.BugInjection.hexBytes

local elab "ko_chars_of_hex" t:term : term => do
  let e ← Lean.Elab.Term.elabTerm t none
  let sLit ← Lean.Meta.whnf (← Lean.Meta.whnf e).getAppArgs[0]!
  match sLit with
  | .lit (.strVal s) => return Lean.toExpr s.toList
  | _ => throwError "not strVal: {sLit}"

local elab "ko_str_of_hex" t:term : term => do
  let e ← Lean.Elab.Term.elabTerm t none
  Lean.Meta.whnf (← Lean.Meta.whnf e).getAppArgs[0]!

def dummyRunEvent : RunEvent :=
  { party := "", cmd := .init ⟨"", 0⟩ "", input := [], coins := [], exit := none }

def ev (k : Nat) : RunEvent :=
  match trace0[k]? with
  | some (.run e) => e
  | _ => dummyRunEvent

local elab "ko_exit_str" k:term : term => do
  let e ← Lean.Elab.Term.elabTerm (← `(RunEvent.exit (ev $k))) none
  let someVal ← Lean.Meta.whnf e
  let prodVal ← Lean.Meta.whnf someVal.getAppArgs[1]!
  let sndVal ← Lean.Meta.whnf prodVal.getAppArgs[3]!
  Lean.Meta.whnf sndVal.getAppArgs[0]!

local elab "ko_exit_chars" k:term : term => do
  let e ← Lean.Elab.Term.elabTerm (← `(RunEvent.exit (ev $k))) none
  let someVal ← Lean.Meta.whnf e
  let prodVal ← Lean.Meta.whnf someVal.getAppArgs[1]!
  let sndVal ← Lean.Meta.whnf prodVal.getAppArgs[3]!
  let sLit ← Lean.Meta.whnf sndVal.getAppArgs[0]!
  match sLit with
  | .lit (.strVal s) => return Lean.toExpr s.toList
  | _ => throwError "not strVal: {sLit}"

theorem trace_eq_evs :
    trace0 = [
      .run (ev 0), .run (ev 1), .run (ev 2),
      .run (ev 3), .run (ev 4), .run (ev 5)
    ] := rfl

theorem trace0_length : trace0.length = 6 := rfl

theorem trace0_getElem?_eq_ev {k : Nat} (hk : k < 6) :
    trace0[k]? = some (.run (ev k)) := by
  rw [trace_eq_evs]
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 => rfl
  | n + 6 => omega

theorem trace0_take_succ {k : Nat} (hk : k < 6) :
    trace0.take (k + 1) = trace0.take k ++ [.run (ev k)] := by
  have hlen : k < trace0.length := by rw [trace0_length]; exact hk
  rw [List.take_add_one, trace0_getElem?_eq_ev hk]
  rfl

theorem ev_exit_ok (k : Nat) (hk : k < 6) : ∃ out, (ev k).exit = some (0, out) := by
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 => exact ⟨_, rfl⟩
  | n + 6 => omega

theorem ev_not_rejected (k : Nat) (hk : k < 6) : ¬ RunRejected (ev k) := by
  obtain ⟨out, hout⟩ := ev_exit_ok k hk
  intro hrej
  exact hrej out hout

theorem noRecvEvent_take2 : (trace0.take 2).all noRecvEvent = true := by decide
theorem noRecvEvent_ev3 : noRecvEvent (.run (ev 3)) = true := rfl
theorem noRecvEvent_ev4 : noRecvEvent (.run (ev 4)) = true := rfl

theorem recv_split_cases {evs₁ evs₂ : List CliEvent} {e : RunEvent}
    (hsplit : trace0 = evs₁ ++ .run e :: evs₂)
    (hrecv : ∃ peer, e.cmd = .recv peer) :
    (evs₁ = trace0.take 2 ∧ e = ev 2) ∨ (evs₁ = trace0.take 5 ∧ e = ev 5) := by
  have hlen : evs₁.length < 6 := by
    have h := congrArg List.length hsplit
    rw [trace0_length, List.length_append, List.length_cons] at h
    omega
  have hget : trace0[evs₁.length]? = some (.run e) := by
    rw [hsplit, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  have hpre : evs₁ = trace0.take evs₁.length := by
    rw [hsplit, List.take_left]
  obtain ⟨peer, hcmd⟩ := hrecv
  match hm : evs₁.length with
  | 0 | 1 | 3 | 4 =>
    rw [hm] at hget
    injection hget with hrun
    injection hrun with he
    subst he
    cases hcmd
  | 2 =>
    rw [hm] at hget hpre
    injection hget with hrun
    injection hrun with he
    exact Or.inl ⟨hpre, he.symm⟩
  | 5 =>
    rw [hm] at hget hpre
    injection hget with hrun
    injection hrun with he
    exact Or.inr ⟨hpre, he.symm⟩
  | n + 6 => omega

/-! ## Exact wire/plaintext handoffs (`rfl` over irreducible `hexBytes`) -/

theorem ev3_in_eq_ev0 : (ev 3).input = (ev 0).input := rfl
theorem ev1_to_ev2 : (ev 1).exit = some (0, (ev 2).input) := rfl
theorem ev2_pt_eq_ev1 : (ev 2).exit = some (0, (ev 1).input) := rfl
theorem ev4_to_ev5 : (ev 4).exit = some (0, (ev 5).input) := rfl
theorem ev5_pt_eq_ev4 : (ev 5).exit = some (0, (ev 4).input) := rfl

/-! ## Fast byte lists for `ev 0 .. ev 5` -/

def ev0InC : List Char := ko_chars_of_hex (ev 0).input
def ev0InF : HwBytes := hexBytes.go hexDigit ev0InC
theorem ev0In_eq : (ev 0).input = ev0InF := by
  have h1 : (ev 0).input = hexBytes (ko_str_of_hex (ev 0).input) := rfl
  have h2 : (ko_str_of_hex (ev 0).input) = String.ofList ev0InC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl

def ev0CoinsC : List Char := ko_chars_of_hex (ev 0).coins
def ev0CoinsF : HwBytes := hexBytes.go hexDigit ev0CoinsC
theorem ev0Coins_eq : (ev 0).coins = ev0CoinsF := by
  have h1 : (ev 0).coins = hexBytes (ko_str_of_hex (ev 0).coins) := rfl
  have h2 : (ko_str_of_hex (ev 0).coins) = String.ofList ev0CoinsC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl

def ev0OutC : List Char := ko_exit_chars 0
def ev0OutF : HwBytes := hexBytes.go hexDigit ev0OutC
theorem ev0Out_exit_eq : (ev 0).exit = some (0, ev0OutF) := by
  have h1 : (ev 0).exit = some (0, hexBytes (ko_exit_str 0)) := rfl
  have h2 : (ko_exit_str 0) = String.ofList ev0OutC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl

def ev1InC : List Char := ko_chars_of_hex (ev 1).input
def ev1InF : HwBytes := hexBytes.go hexDigit ev1InC
theorem ev1In_eq : (ev 1).input = ev1InF := by
  have h1 : (ev 1).input = hexBytes (ko_str_of_hex (ev 1).input) := rfl
  have h2 : (ko_str_of_hex (ev 1).input) = String.ofList ev1InC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl

def ev1CoinsC : List Char := ko_chars_of_hex (ev 1).coins
def ev1CoinsF : HwBytes := hexBytes.go hexDigit ev1CoinsC
theorem ev1Coins_eq : (ev 1).coins = ev1CoinsF := by
  have h1 : (ev 1).coins = hexBytes (ko_str_of_hex (ev 1).coins) := rfl
  have h2 : (ko_str_of_hex (ev 1).coins) = String.ofList ev1CoinsC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl

def ev1OutC : List Char := ko_exit_chars 1
def ev1OutF : HwBytes := hexBytes.go hexDigit ev1OutC
theorem ev1Out_exit_eq : (ev 1).exit = some (0, ev1OutF) := by
  have h1 : (ev 1).exit = some (0, hexBytes (ko_exit_str 1)) := rfl
  have h2 : (ko_exit_str 1) = String.ofList ev1OutC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl

def ev2InC : List Char := ko_chars_of_hex (ev 2).input
def ev2InF : HwBytes := hexBytes.go hexDigit ev2InC
theorem ev2In_eq : (ev 2).input = ev2InF := by
  have h1 : (ev 2).input = hexBytes (ko_str_of_hex (ev 2).input) := rfl
  have h2 : (ko_str_of_hex (ev 2).input) = String.ofList ev2InC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl

def ev2CoinsC : List Char := ko_chars_of_hex (ev 2).coins
def ev2CoinsF : HwBytes := hexBytes.go hexDigit ev2CoinsC
theorem ev2Coins_eq : (ev 2).coins = ev2CoinsF := by
  have h1 : (ev 2).coins = hexBytes (ko_str_of_hex (ev 2).coins) := rfl
  have h2 : (ko_str_of_hex (ev 2).coins) = String.ofList ev2CoinsC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl

def ev2OutC : List Char := ko_exit_chars 2
def ev2OutF : HwBytes := hexBytes.go hexDigit ev2OutC
theorem ev2Out_exit_eq : (ev 2).exit = some (0, ev2OutF) := by
  have h1 : (ev 2).exit = some (0, hexBytes (ko_exit_str 2)) := rfl
  have h2 : (ko_exit_str 2) = String.ofList ev2OutC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl

def ev3InC : List Char := ko_chars_of_hex (ev 3).input
def ev3InF : HwBytes := hexBytes.go hexDigit ev3InC
theorem ev3In_eq : (ev 3).input = ev3InF := by
  have h1 : (ev 3).input = hexBytes (ko_str_of_hex (ev 3).input) := rfl
  have h2 : (ko_str_of_hex (ev 3).input) = String.ofList ev3InC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl

def ev3CoinsC : List Char := ko_chars_of_hex (ev 3).coins
def ev3CoinsF : HwBytes := hexBytes.go hexDigit ev3CoinsC
theorem ev3Coins_eq : (ev 3).coins = ev3CoinsF := by
  have h1 : (ev 3).coins = hexBytes (ko_str_of_hex (ev 3).coins) := rfl
  have h2 : (ko_str_of_hex (ev 3).coins) = String.ofList ev3CoinsC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl

def ev3OutC : List Char := ko_exit_chars 3
def ev3OutF : HwBytes := hexBytes.go hexDigit ev3OutC
theorem ev3Out_exit_eq : (ev 3).exit = some (0, ev3OutF) := by
  have h1 : (ev 3).exit = some (0, hexBytes (ko_exit_str 3)) := rfl
  have h2 : (ko_exit_str 3) = String.ofList ev3OutC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl

def ev4InC : List Char := ko_chars_of_hex (ev 4).input
def ev4InF : HwBytes := hexBytes.go hexDigit ev4InC
theorem ev4In_eq : (ev 4).input = ev4InF := by
  have h1 : (ev 4).input = hexBytes (ko_str_of_hex (ev 4).input) := rfl
  have h2 : (ko_str_of_hex (ev 4).input) = String.ofList ev4InC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl

def ev4CoinsC : List Char := ko_chars_of_hex (ev 4).coins
def ev4CoinsF : HwBytes := hexBytes.go hexDigit ev4CoinsC
theorem ev4Coins_eq : (ev 4).coins = ev4CoinsF := by
  have h1 : (ev 4).coins = hexBytes (ko_str_of_hex (ev 4).coins) := rfl
  have h2 : (ko_str_of_hex (ev 4).coins) = String.ofList ev4CoinsC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl

def ev4OutC : List Char := ko_exit_chars 4
def ev4OutF : HwBytes := hexBytes.go hexDigit ev4OutC
theorem ev4Out_exit_eq : (ev 4).exit = some (0, ev4OutF) := by
  have h1 : (ev 4).exit = some (0, hexBytes (ko_exit_str 4)) := rfl
  have h2 : (ko_exit_str 4) = String.ofList ev4OutC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl

def ev5InC : List Char := ko_chars_of_hex (ev 5).input
def ev5InF : HwBytes := hexBytes.go hexDigit ev5InC
theorem ev5In_eq : (ev 5).input = ev5InF := by
  have h1 : (ev 5).input = hexBytes (ko_str_of_hex (ev 5).input) := rfl
  have h2 : (ko_str_of_hex (ev 5).input) = String.ofList ev5InC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl

def ev5CoinsC : List Char := ko_chars_of_hex (ev 5).coins
def ev5CoinsF : HwBytes := hexBytes.go hexDigit ev5CoinsC
theorem ev5Coins_eq : (ev 5).coins = ev5CoinsF := by
  have h1 : (ev 5).coins = hexBytes (ko_str_of_hex (ev 5).coins) := rfl
  have h2 : (ko_str_of_hex (ev 5).coins) = String.ofList ev5CoinsC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl

def ev5OutC : List Char := ko_exit_chars 5
def ev5OutF : HwBytes := hexBytes.go hexDigit ev5OutC
theorem ev5Out_exit_eq : (ev 5).exit = some (0, ev5OutF) := by
  have h1 : (ev 5).exit = some (0, hexBytes (ko_exit_str 5)) := rfl
  have h2 : (ko_exit_str 5) = String.ofList ev5OutC := rfl
  rw [h1, h2, hexBytes_ofList]; rfl

/-! ## Command, coin, and bundle facts for `ev 0 .. ev 5` -/

/-- The 32 Kyber randomness bytes drawn in 4-byte chunks at offsets `32 + 4 * j` of `(ev 0).coins`. -/
def ev0KyberEnt : HwBytes :=
  (List.range 32).map fun j => ((ev 0).coins.drop (32 + 4 * j)).headD 0#8

def ev0KyberEntF : HwBytes :=
  (List.range 32).map fun j => (ev0CoinsF.drop (32 + 4 * j)).headD 0#8

theorem ev0KyberEnt_eq : ev0KyberEnt = ev0KyberEntF := by
  unfold ev0KyberEnt ev0KyberEntF; rw [ev0Coins_eq]

/-- The 32 Kyber randomness bytes drawn in 4-byte chunks at offsets `32 + 4 * j` of `(ev 3).coins`. -/
def ev3KyberEnt : HwBytes :=
  (List.range 32).map fun j => ((ev 3).coins.drop (32 + 4 * j)).headD 0#8

def ev3KyberEntF : HwBytes :=
  (List.range 32).map fun j => (ev3CoinsF.drop (32 + 4 * j)).headD 0#8

theorem ev3KyberEnt_eq : ev3KyberEnt = ev3KyberEntF := by
  unfold ev3KyberEnt ev3KyberEntF; rw [ev3Coins_eq]

theorem ev0_cmd_and_exit :
    (ev 0).party = "alice" ∧
    (ev 0).cmd = .init ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ "bundle" ∧
    (ev 0).exit = some (0, []) ∧
    runWrapped (ev 0) = true := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · rw [ev0Out_exit_eq]; rfl
  · unfold runWrapped
    have hcmd : (ev 0).cmd = .init ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ "bundle" := rfl
    rw [hcmd, ev0In_eq]; decide +kernel

theorem ev3_cmd_and_exit :
    (ev 3).party = "alice" ∧
    (ev 3).cmd = .init ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ "bundle" ∧
    (ev 3).exit = some (0, []) ∧
    runWrapped (ev 3) = true := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · rw [ev3Out_exit_eq]; rfl
  · unfold runWrapped
    have hcmd : (ev 3).cmd = .init ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ "bundle" := rfl
    rw [hcmd, ev3In_eq]; decide +kernel

theorem ev0_bundle_base :
    (ev 0).input.length = preKeyBundleByteLength ∧
    ((ev 0).input)[4]? = some 1#8 ∧
    nextBundleIds none (ev 0) = some (some 3#32, 7#32, 9#32) ∧
    nextBundleIds (some (some 3#32, 7#32, 9#32)) (ev 3) = some (some 3#32, 7#32, 9#32) ∧
    slice (ev 0).input 79 64 = w0.spkSig ∧
    slice (ev 0).input 147 1569 = kyberKey w0.kyberPk ∧
    slice (ev 0).input 1716 64 = w0.kyberPkSig := by
  have hcmd0 : (ev 0).cmd = .init ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ "bundle" := rfl
  have hcmd3 : (ev 3).cmd = .init ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ "bundle" := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ev0In_eq]; decide +kernel
  · rw [ev0In_eq]; decide +kernel
  · unfold nextBundleIds; rw [hcmd0, ev0In_eq]; decide +kernel
  · unfold nextBundleIds; rw [hcmd3, ev3In_eq]; decide +kernel
  · rw [ev0In_eq]; decide +kernel
  · rw [ev0In_eq]; decide +kernel
  · rw [ev0In_eq]; decide +kernel

theorem nextBundleIds_ev1 (cur : Option BundlePreKeyIds) : nextBundleIds cur (ev 1) = cur := rfl
theorem nextBundleIds_ev2 (cur : Option BundlePreKeyIds) : nextBundleIds cur (ev 2) = cur := rfl
theorem nextBundleIds_ev4 (cur : Option BundlePreKeyIds) : nextBundleIds cur (ev 4) = cur := rfl

theorem ev0_coins_base :
    (ev 0).coins.length = 192 ∧
    ev0KyberEnt.length = 32 ∧
    (compKyberEncaps ev0KyberEnt).take 1568 = w0.kyberCts.getD 0 [] ∧
    (∀ j < 32, ev0KyberEnt[j]? = ((ev 0).coins.drop (32 + 4 * j)).head?) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ev0Coins_eq]; decide +kernel
  · rw [ev0KyberEnt_eq]; decide +kernel
  · rw [ev0KyberEnt_eq]; decide +kernel
  · intro j hj
    rw [ev0KyberEnt_eq, ev0Coins_eq]
    revert hj
    match j with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31 =>
      intro _; decide +kernel
    | n + 32 => intro h; omega

theorem ev3_coins_base :
    (ev 3).coins.length = 192 ∧
    ev3KyberEnt.length = 32 ∧
    (∀ j < 32, ev3KyberEnt[j]? = ((ev 3).coins.drop (32 + 4 * j)).head?) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ev3Coins_eq]; decide +kernel
  · rw [ev3KyberEnt_eq]; decide +kernel
  · intro j hj
    rw [ev3KyberEnt_eq, ev3Coins_eq]
    revert hj
    match j with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31 =>
      intro _; decide +kernel
    | n + 32 => intro h; omega

theorem ev1_facts :
    (ev 1).party = "alice" ∧
    (ev 1).cmd = .send ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ ∧
    (ev 1).input.length < 8 ∧
    (ev 1).coins.length = 64 ∧
    runWrapped (ev 1) = true := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · rw [ev1In_eq]; decide +kernel
  · rw [ev1Coins_eq]; decide +kernel
  · unfold runWrapped
    have hcmd : (ev 1).cmd = .send ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ := rfl
    rw [hcmd, ev1Out_exit_eq]; decide +kernel

theorem ev4_facts :
    (ev 4).party = "alice" ∧
    (ev 4).cmd = .send ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ ∧
    (ev 4).input.length < 8 ∧
    (ev 4).coins.length = 64 ∧
    runWrapped (ev 4) = true := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · rw [ev4In_eq]; decide +kernel
  · rw [ev4Coins_eq]; decide +kernel
  · unfold runWrapped
    have hcmd : (ev 4).cmd = .send ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ := rfl
    rw [hcmd, ev4Out_exit_eq]; decide +kernel

theorem ev2_facts :
    (ev 2).party = "bob" ∧
    (ev 2).cmd = .recv ⟨"8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b", 1⟩ ∧
    (ev 2).coins.length = 32 ∧
    runWrapped (ev 2) = true := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · rw [ev2Coins_eq]; decide +kernel
  · unfold runWrapped
    have hcmd : (ev 2).cmd = .recv ⟨"8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b", 1⟩ := rfl
    rw [hcmd, ev2In_eq]; decide +kernel

theorem ev5_facts :
    (ev 5).party = "bob" ∧
    (ev 5).cmd = .recv ⟨"8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b", 1⟩ ∧
    (ev 5).coins.length = 32 ∧
    runWrapped (ev 5) = true := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · rw [ev5Coins_eq]; decide +kernel
  · unfold runWrapped
    have hcmd : (ev 5).cmd = .recv ⟨"8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b", 1⟩ := rfl
    rw [hcmd, ev5In_eq]; decide +kernel

/-! ## Parsed `PreKeyFields` for Bob's `.recv` calls (`ev 2` and `ev 5`) -/

theorem parse_ev2_isSome : (parsePreKeyWire ev2InF).isSome = true := by decide +kernel
def p2 : PreKeyFields := (parsePreKeyWire ev2InF).get parse_ev2_isSome

theorem parse_ev2 : parsePreKeyWire (ev 2).input = some p2 := by
  rw [ev2In_eq]
  exact (Option.some_get parse_ev2_isSome).symm

theorem parse_ev5_isSome : (parsePreKeyWire ev5InF).isSome = true := by decide +kernel
def p5 : PreKeyFields := (parsePreKeyWire ev5InF).get parse_ev5_isSome

theorem parse_ev5 : parsePreKeyWire (ev 5).input = some p5 := by
  rw [ev5In_eq]
  exact (Option.some_get parse_ev5_isSome).symm

theorem p2_ne_p5_baseKey : p2.baseKey.take 33 ≠ p5.baseKey.take 33 := by decide +kernel

theorem p2_fields_base :
    p2.version = 4#8 ∧
    p2.preKeyId = some 3#32 ∧
    p2.signedPreKeyId = 7#32 ∧
    p2.kyberPreKeyId = some 9#32 ∧
    p2.kyberCiphertext = some (kyberKey (w0.kyberCts.getD 0 [])) ∧
    p2.inner.counter.toNat = 0 ∧
    p2.inner.previousCounter.toNat = 0 ∧
    preKeySpqrIndex p2 = 1 ∧
    (p2.message.drop (p2.message.length - 8)).take 4 ≠ compTag4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem p5_fields_base :
    p5.version = 4#8 ∧
    p5.preKeyId = some 3#32 ∧
    p5.signedPreKeyId = 7#32 ∧
    p5.kyberPreKeyId = some 9#32 ∧
    p5.kyberCiphertext = some (kyberKey (w0.kyberCts.getD 1 [])) ∧
    p5.inner.counter.toNat = 0 ∧
    p5.inner.previousCounter.toNat = 0 ∧
    preKeySpqrIndex p5 = 1 ∧
    (p5.message.drop (p5.message.length - 8)).take 4 ≠ compTag4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem ev3In_eq_ev0In : ev3InF = ev0InF := by decide +kernel
theorem ev2In_eq_ev1Out : ev2InF = ev1OutF := by decide +kernel
theorem ev5In_eq_ev4Out : ev5InF = ev4OutF := by decide +kernel

def aliceBobAddrBytes : HwBytes :=
  [0x00#8, 0x8a#8, 0x6f#8, 0x1c#8, 0x2e#8, 0x3b#8, 0x4d#8, 0x4e#8, 0x5f#8, 0x9a#8, 0x0b#8,
   0x1c#8, 0x2d#8, 0x3e#8, 0x4f#8, 0x5a#8, 0x6b#8, 0x01#8, 0x00#8, 0x5d#8, 0x3e#8, 0x2f#8,
   0x10#8, 0x7a#8, 0x8b#8, 0x4c#8, 0x9d#8, 0x8e#8, 0x0f#8, 0xa1#8, 0xb2#8, 0xc3#8, 0xd4#8,
   0xe5#8, 0xf6#8, 0x01#8]

theorem serializeAddresses_alice_bob_eq :
    DY.Libsignal.Composed.Refinement.Cli.serializeAddresses
      ⟨DY.Libsignal.Composed.Refinement.Cli.aliceUuid, 1⟩
      ⟨DY.Libsignal.Composed.Refinement.Cli.bobUuid, 1⟩ = aliceBobAddrBytes := by
  decide +kernel

end Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.WitnessParse
