/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import Lean
public import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.DefsI0
public import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.I0Laws

/-!
# Concrete Trace Extraction & Fast Hex Parsing (`Calls0to4Prefix/Parse.lean`)

Provides fast kernel-checked wire/coin parsing (`ev 0 .. ev 4`, `ev0_cmd_and_exit`,
`ev0_bundle_slices`, `ev0_coins_facts`, `ev2_full_fields`, `not_kyberMismatch_ev2`,
`ev4_whisper`, `nextBundleIds_non_init`) for the 5 honest `.run` events of `rcprTrace`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained

open scoped DY.Libsignal.Composed
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (RunEvent CliEvent)
open DY.Libsignal.PQXDH.Refinement (wirePrekeyTag preKeyBundleByteLength)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup BundlePreKeyIds PreKeyFields
   clamp slice ecKey kyberKey parsePreKeyWire
   RunRejected KyberMismatch runWrapped nextBundleIds)
open Symbolic.BugInjection (hexBytes)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compTag4)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.DefsI0
  (rcprSetup rcprTrace rcprI0 rcprHooks0 rcprCompFitsPinned rcprKyberEncaps
   rcprPubOfIdx rcprPubOfOpt rcprSecretIdx rcprPointIdx)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.I0Laws
  (rcprPointIdx_rcprPubOfOpt)

def hexDigit (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10

theorem hexBytes_ofList (cs : List Char) :
    hexBytes (String.ofList cs) = hexBytes.go hexDigit cs := by
  unfold hexBytes hexDigit
  rw [String.toList_ofList]

attribute [local irreducible] Symbolic.BugInjection.hexBytes

elab "nfe_chars_of_hex" t:term : term => do
  let e ← Lean.Elab.Term.elabTerm t none
  let sLit ← Lean.Meta.whnf (← Lean.Meta.whnf e).getAppArgs[0]!
  match sLit with
  | .lit (.strVal s) => return Lean.toExpr s.toList
  | _ => throwError "not strVal: {sLit}"

elab "nfe_str_of_hex" t:term : term => do
  let e ← Lean.Elab.Term.elabTerm t none
  Lean.Meta.whnf (← Lean.Meta.whnf e).getAppArgs[0]!

abbrev cliTrace : List CliEvent :=
  Symbolic.BugInjection.Synthetic.Witnesses.RecvChainPrivRetainedCli.trace

def dummyRunEvent : RunEvent :=
  { party := "", cmd := .init ⟨"", 0⟩ "", input := [], coins := [], exit := none }

def ev (k : Nat) : RunEvent :=
  match cliTrace[k]? with
  | some (.run e) => e
  | _ => dummyRunEvent

theorem rcprTrace_take5 :
    rcprTrace.take 5 = [.run (ev 0), .run (ev 1), .run (ev 2), .run (ev 3), .run (ev 4)] := rfl

theorem rcprTrace_getElem?_eq_ev {k : Nat} (hk : k < 5) :
    rcprTrace[k]? = some (.run (ev k)) := by
  match k with
  | 0 | 1 | 2 | 3 | 4 => rfl
  | n + 5 => omega

theorem rcprTrace_take_succ {k : Nat} (hk : k < 5) :
    rcprTrace.take (k + 1) = rcprTrace.take k ++ [.run (ev k)] := by
  match k with
  | 0 | 1 | 2 | 3 | 4 => rfl
  | n + 5 => omega

theorem ev_exit_ok (k : Nat) (hk : k < 5) : ∃ out, (ev k).exit = some (0, out) := by
  match k with
  | 0 | 1 | 2 | 3 | 4 => exact ⟨_, rfl⟩
  | n + 5 => omega

theorem ev_not_rejected (k : Nat) (hk : k < 5) : ¬ RunRejected (ev k) := by
  obtain ⟨out, hout⟩ := ev_exit_ok k hk
  exact fun hrej => hrej out hout

theorem rcprPubOfIdx_inj {i j : Fin 7} (h : rcprPubOfIdx i = rcprPubOfIdx j) : i = j := by
  have hpt := congrArg rcprPointIdx h
  change rcprPointIdx (rcprPubOfOpt (some i)) = rcprPointIdx (rcprPubOfOpt (some j)) at hpt
  rw [rcprPointIdx_rcprPubOfOpt, rcprPointIdx_rcprPubOfOpt] at hpt
  exact Option.some.inj hpt

private theorem hexBytes_go_length :
    ∀ cs : List Char, (hexBytes.go hexDigit cs).length = cs.length / 2
  | [] => by simp [hexBytes.go]
  | [_] => by simp [hexBytes.go]
  | _ :: _ :: rest => by simp only [hexBytes.go, List.length_cons, hexBytes_go_length rest]; omega

/-! ### Call 0 (`aliceStart`) bundle & 192-byte coins -/

private def ev0InChars : List Char := nfe_chars_of_hex (ev 0).input
private def ev0InFast : HwBytes := hexBytes.go hexDigit ev0InChars
private theorem ev0In_eq : (ev 0).input = ev0InFast := by
  rw [show (ev 0).input = hexBytes (nfe_str_of_hex (ev 0).input) from rfl,
      show (nfe_str_of_hex (ev 0).input) = String.ofList ev0InChars from rfl,
      hexBytes_ofList]
  rfl

def ev0CoinsFast : HwBytes := hexBytes.go hexDigit (nfe_chars_of_hex (ev 0).coins)
theorem ev0Coins_eq : (ev 0).coins = ev0CoinsFast := by
  rw [show (ev 0).coins = hexBytes (nfe_str_of_hex (ev 0).coins) from rfl,
      show (nfe_str_of_hex (ev 0).coins) = String.ofList (nfe_chars_of_hex (ev 0).coins) from rfl,
      hexBytes_ofList]
  rfl

def ev0KyberEnt : HwBytes :=
  (List.range 32).map fun j => ((ev 0).coins.drop (32 + 4 * j)).headD 0#8

def ev0KyberEntFast : HwBytes :=
  (List.range 32).map fun j => (ev0CoinsFast.drop (32 + 4 * j)).headD 0#8

theorem ev0KyberEnt_eq : ev0KyberEnt = ev0KyberEntFast := by
  unfold ev0KyberEnt ev0KyberEntFast; rw [ev0Coins_eq]

theorem ev0_cmd_and_exit :
    (ev 0).party = "alice" ∧
    (ev 0).cmd = .init ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ "bundle" ∧
    (ev 0).exit = some (0, []) ∧
    runWrapped (ev 0) = true := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · change some (0, hexBytes "") = some (0, [])
    rw [show ("" : String) = String.ofList [] from rfl, hexBytes_ofList]; rfl
  · unfold runWrapped
    have hcmd : (ev 0).cmd = .init ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ "bundle" := rfl
    rw [hcmd, ev0In_eq]; decide +kernel

theorem ev0_bundle_slices :
    (ev 0).input.length = preKeyBundleByteLength ∧
    ((ev 0).input)[4]? = some 0#8 ∧
    nextBundleIds none (ev 0) = some (none, 7#32, 9#32) ∧
    slice (ev 0).input 46 33 = ecKey (rcprPubOfIdx ⟨2, by decide⟩) ∧
    slice (ev 0).input 79 64 = rcprSetup.spkSig ∧
    slice (ev 0).input 147 1569 = kyberKey rcprSetup.kyberPk ∧
    slice (ev 0).input 1716 64 = rcprSetup.kyberPkSig ∧
    slice (ev 0).input 1780 33 = ecKey (rcprPubOfIdx ⟨1, by decide⟩) := by
  have hcmd : (ev 0).cmd = .init ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ "bundle" := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ev0In_eq]; decide +kernel
  · rw [ev0In_eq]; decide +kernel
  · unfold nextBundleIds; rw [hcmd, ev0In_eq]; decide +kernel
  · rw [ev0In_eq]; decide +kernel
  · rw [ev0In_eq]; decide +kernel
  · rw [ev0In_eq]; decide +kernel
  · rw [ev0In_eq]; decide +kernel
  · rw [ev0In_eq]; decide +kernel

theorem ev0_coins_facts :
    (ev 0).coins.length = 192 ∧
    rcprSecretIdx (clamp (slice (ev 0).coins 0 32)) = some ⟨3, by decide⟩ ∧
    rcprSecretIdx (clamp (slice (ev 0).coins 160 32)) = some ⟨4, by decide⟩ ∧
    ev0KyberEnt.length = 32 ∧
    (rcprKyberEncaps ev0KyberEnt).take 1568 = rcprSetup.kyberCts.headD [] ∧
    (∀ j < 32, ev0KyberEnt[j]? = ((ev 0).coins.drop (32 + 4 * j)).head?) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ev0Coins_eq]; decide +kernel
  · rw [ev0Coins_eq]; decide +kernel
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

/-! ### Calls 1 & 3 (`.send`) and Calls 2 & 4 (`.recv`) -/

/-- Maps send index `s ∈ {0, 1}` to its call index in `rcprTrace` (`1` for Alice, `3` for Bob). -/
def sendCallOf (s : Nat) : Nat :=
  if s = 0 then 1 else 3

theorem ev1_to_ev2 : (ev 1).exit = some (0, (ev 2).input) := rfl
theorem ev2_pt_eq_ev1 : (ev 2).exit = some (0, (ev 1).input) := rfl
theorem ev3_to_ev4 : (ev 3).exit = some (0, (ev 4).input) := rfl
theorem ev4_pt_eq_ev3 : (ev 4).exit = some (0, (ev 3).input) := rfl

theorem ev1_party_cmd :
    (ev 1).party = "alice" ∧ (ev 1).cmd = .send ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ :=
  ⟨rfl, rfl⟩

theorem ev2_party_cmd :
    (ev 2).party = "bob" ∧ (ev 2).cmd = .recv ⟨"8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b", 1⟩ :=
  ⟨rfl, rfl⟩

theorem ev3_party_cmd :
    (ev 3).party = "bob" ∧ (ev 3).cmd = .send ⟨"8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b", 1⟩ :=
  ⟨rfl, rfl⟩

theorem ev4_party_cmd :
    (ev 4).party = "alice" ∧ (ev 4).cmd = .recv ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ :=
  ⟨rfl, rfl⟩

theorem send_coins_ge_64 {s : Nat} (hs : s < 2) :
    64 ≤ (ev (sendCallOf s)).coins.length := by
  match s with
  | 0 =>
    change 64 ≤ (ev 1).coins.length
    rw [show (ev 1).coins = hexBytes (nfe_str_of_hex (ev 1).coins) from rfl,
        show (nfe_str_of_hex (ev 1).coins) = String.ofList (nfe_chars_of_hex (ev 1).coins) from rfl,
        hexBytes_ofList, hexBytes_go_length]; decide
  | 1 =>
    change 64 ≤ (ev 3).coins.length
    rw [show (ev 3).coins = hexBytes (nfe_str_of_hex (ev 3).coins) from rfl,
        show (nfe_str_of_hex (ev 3).coins) = String.ofList (nfe_chars_of_hex (ev 3).coins) from rfl,
        hexBytes_ofList, hexBytes_go_length]; decide
  | n + 2 => omega

theorem send_input_len_lt_16 {s : Nat} (hs : s < 2) :
    (ev (sendCallOf s)).input.length < 16 := by
  match s with
  | 0 =>
    change (ev 1).input.length < 16
    rw [show (ev 1).input = hexBytes (nfe_str_of_hex (ev 1).input) from rfl,
        show (nfe_str_of_hex (ev 1).input) = String.ofList (nfe_chars_of_hex (ev 1).input) from rfl,
        hexBytes_ofList, hexBytes_go_length]; decide
  | 1 =>
    change (ev 3).input.length < 16
    rw [show (ev 3).input = hexBytes (nfe_str_of_hex (ev 3).input) from rfl,
        show (nfe_str_of_hex (ev 3).input) = String.ofList (nfe_chars_of_hex (ev 3).input) from rfl,
        hexBytes_ofList, hexBytes_go_length]; decide
  | n + 2 => omega

private def ev2InFast : HwBytes := hexBytes.go hexDigit (nfe_chars_of_hex (ev 2).input)
private theorem ev2In_eq : (ev 2).input = ev2InFast := by
  rw [show (ev 2).input = hexBytes (nfe_str_of_hex (ev 2).input) from rfl,
      show (nfe_str_of_hex (ev 2).input) = String.ofList (nfe_chars_of_hex (ev 2).input) from rfl,
      hexBytes_ofList]
  rfl

private def ev4InFast : HwBytes := hexBytes.go hexDigit (nfe_chars_of_hex (ev 4).input)
private theorem ev4In_eq : (ev 4).input = ev4InFast := by
  rw [show (ev 4).input = hexBytes (nfe_str_of_hex (ev 4).input) from rfl,
      show (nfe_str_of_hex (ev 4).input) = String.ofList (nfe_chars_of_hex (ev 4).input) from rfl,
      hexBytes_ofList]
  rfl

def ev2CoinsFast : HwBytes := hexBytes.go hexDigit (nfe_chars_of_hex (ev 2).coins)
theorem ev2Coins_eq : (ev 2).coins = ev2CoinsFast := by
  rw [show (ev 2).coins = hexBytes (nfe_str_of_hex (ev 2).coins) from rfl,
      show (nfe_str_of_hex (ev 2).coins) = String.ofList (nfe_chars_of_hex (ev 2).coins) from rfl,
      hexBytes_ofList]
  rfl

def ev4CoinsFast : HwBytes := hexBytes.go hexDigit (nfe_chars_of_hex (ev 4).coins)
theorem ev4Coins_eq : (ev 4).coins = ev4CoinsFast := by
  rw [show (ev 4).coins = hexBytes (nfe_str_of_hex (ev 4).coins) from rfl,
      show (nfe_str_of_hex (ev 4).coins) = String.ofList (nfe_chars_of_hex (ev 4).coins) from rfl,
      hexBytes_ofList]
  rfl

theorem ev1_runWrapped : runWrapped (ev 1) = true := by
  unfold runWrapped
  rw [ev1_party_cmd.2, ev1_to_ev2, ev2In_eq]
  decide +kernel

theorem ev3_runWrapped : runWrapped (ev 3) = false := by
  unfold runWrapped
  rw [ev3_party_cmd.2, ev3_to_ev4, ev4In_eq]
  decide +kernel

theorem ev2_runWrapped : runWrapped (ev 2) = true := by
  unfold runWrapped
  rw [ev2_party_cmd.2, ev2In_eq]
  decide +kernel

theorem ev2_input_len_lt : (ev 2).input.length < 4096 := by
  rw [ev2In_eq]; decide +kernel

theorem ev2_input_len_lt_2pow63 : (ev 2).input.length < 2 ^ 63 := by
  have h := ev2_input_len_lt; omega

theorem ev2_coins_ge_32 : 32 ≤ (ev 2).coins.length := by
  rw [ev2Coins_eq]; decide +kernel

theorem ev4_coins_ge_32 : 32 ≤ (ev 4).coins.length := by
  rw [ev4Coins_eq]; decide +kernel

theorem ev2_coins_idx :
    rcprSecretIdx (clamp (((ev 2).coins).take 32)) = some ⟨5, by decide⟩ := by
  rw [ev2Coins_eq]; decide +kernel

theorem ev4_coins_idx :
    rcprSecretIdx (clamp (((ev 4).coins).take 32)) = some ⟨6, by decide⟩ := by
  rw [ev4Coins_eq]; decide +kernel

private theorem ev2_some_preKey : (parsePreKeyWire ev2InFast).isSome = true := by
  decide +kernel

theorem ev2_has_preKey : ∃ p : PreKeyFields, parsePreKeyWire (ev 2).input = some p := by
  have hs := ev2_some_preKey
  rw [← ev2In_eq] at hs
  cases hp : parsePreKeyWire (ev 2).input with
  | none => rw [hp] at hs; cases hs
  | some p => exact ⟨p, rfl⟩

private theorem ev2_full_check :
    ((parsePreKeyWire ev2InFast).map fun p =>
      (p.version == 4#8 &&
       p.signedPreKeyId == 7 &&
       p.preKeyId == none &&
       p.kyberPreKeyId == some 9 &&
       p.kyberCiphertext == some (kyberKey (rcprSetup.kyberCts.headD [])) &&
       p.baseKey == ecKey (rcprPubOfIdx ⟨3, by decide⟩) &&
       p.identityKey == ecKey (rcprPubOfIdx ⟨0, by decide⟩) &&
       p.inner.senderRatchetKey.bytes.toList == rcprPubOfIdx ⟨4, by decide⟩ &&
       p.inner.counter.toNat == 0 &&
       p.inner.previousCounter.toNat == 0 &&
       (p.message.drop (p.message.length - 8)).take 4 != compTag4)) = some true := by
  decide +kernel

theorem ev2_full_fields {p : PreKeyFields} (hp : parsePreKeyWire (ev 2).input = some p) :
    p.version = 4#8 ∧
    p.signedPreKeyId = 7 ∧
    p.preKeyId = none ∧
    p.kyberPreKeyId = some 9 ∧
    p.kyberCiphertext = some (kyberKey (rcprSetup.kyberCts.headD [])) ∧
    p.baseKey = ecKey (rcprPubOfIdx ⟨3, by decide⟩) ∧
    p.identityKey = ecKey (rcprPubOfIdx ⟨0, by decide⟩) ∧
    p.inner.senderRatchetKey.bytes.toList = rcprPubOfIdx ⟨4, by decide⟩ ∧
    p.inner.counter.toNat = 0 ∧
    p.inner.previousCounter.toNat = 0 ∧
    (p.message.drop (p.message.length - 8)).take 4 ≠ compTag4 := by
  have hc := ev2_full_check
  rw [← ev2In_eq, hp, Option.map_some, Option.some.injEq] at hc
  simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hc
  exact ⟨hc.1.1.1.1.1.1.1.1.1.1, hc.1.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.1.2,
    hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2, hc.1.1.1.1.1.2, hc.1.1.1.1.2,
    hc.1.1.1.2, hc.1.1.2, hc.1.2, hc.2⟩

theorem not_kyberMismatch_ev2 {r : ProtocolSetup} {p : PreKeyFields}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (hp : parsePreKeyWire (ev 2).input = some p) :
    ¬ KyberMismatch rcprI0 r p := by
  have hct := (ev2_full_fields hp).2.2.2.2.1
  have hkyber := hfit.1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rintro ⟨e, ct, ss, helen, hpct, henc, hndec⟩
  rw [hct] at hpct
  injection hpct with hkk
  have hct_eq : ct = rcprSetup.kyberCts.headD [] := by
    unfold kyberKey at hkk
    exact (List.cons.inj hkk).2.symm
  subst hct_eq
  have hmem : rcprSetup.kyberCts.headD [] ∈ rcprSetup.kyberCts :=
    List.mem_of_getElem? (rfl : rcprSetup.kyberCts[0]? = _)
  exact hndec (hkyber _ hmem e ss helen henc)

/-- Parsed specification of a Whisper `.recv` input `e.input` carrying `rcprPubOfIdx pkIdx`. -/
def WhisperInputSpec (e : RunEvent) (pkIdx : Fin 7) : Prop :=
  runWrapped e = false ∧
  parsePreKeyWire e.input = none ∧
  ∃ body m,
    e.input = wireWhisperTag :: body ∧
    CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec body = .ok m ∧
    m.senderRatchetKey.bytes.toList = rcprPubOfIdx pkIdx ∧
    m.counter.toNat = 0

private def checkWhisperFast (b : HwBytes) (pkIdx : Fin 7) : Bool :=
  match b with
  | tag :: body =>
    tag == wireWhisperTag &&
    match CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec body with
    | .ok m => m.senderRatchetKey.bytes.toList == rcprPubOfIdx pkIdx && m.counter.toNat == 0
    | .error _ => false
  | [] => false

private theorem whisperInputSpec_of_check {e : RunEvent} {fast : HwBytes} {pkIdx : Fin 7}
    (hcmd : ∃ peer, e.cmd = .recv peer) (heq : e.input = fast)
    (hc : checkWhisperFast fast pkIdx = true) :
    WhisperInputSpec e pkIdx := by
  unfold checkWhisperFast at hc
  cases fast with
  | nil => cases hc
  | cons tag body =>
    dsimp only at hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    rcases hc with ⟨htag, hrest⟩
    subst htag
    cases htr : CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec body with
    | error _ => rw [htr] at hrest; cases hrest
    | ok m =>
      rw [htr] at hrest
      simp only [Bool.and_eq_true, beq_iff_eq] at hrest
      obtain ⟨peer, hp⟩ := hcmd
      refine ⟨?_, ?_, body, m, heq, htr, hrest.1, hrest.2⟩
      · unfold runWrapped; rw [hp, heq]; simp
      · rw [heq]; unfold parsePreKeyWire; simp [wireWhisperTag, wirePrekeyTag]

theorem ev4_whisper : WhisperInputSpec (ev 4) ⟨5, by decide⟩ :=
  whisperInputSpec_of_check ⟨_, ev4_party_cmd.2⟩ ev4In_eq (by decide +kernel)

theorem nextBundleIds_non_init {k : Nat} (hk0 : k ≠ 0) (hk5 : k < 5)
    (cur : Option BundlePreKeyIds) :
    nextBundleIds cur (ev k) = cur := by
  unfold nextBundleIds
  match k with
  | 0 => exact absurd rfl hk0
  | 1 | 2 | 3 | 4 => rfl
  | n + 5 => omega

end Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained
