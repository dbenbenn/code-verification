/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.PureCRel -- proof-setup: allow-public-import
public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredStatementDefs
public import Symbolic.Proofs.Swarm.CREF.TR.RecordBytesInj -- proof-setup: allow-public-import
public import Symbolic.Proofs.SpecLemmas.LeakableSecretProofDefs
import Symbolic.Proofs.Swarm.CREF.Prelude
import LibsignalBinary.Specifications.CryptoGames.AEAD.HMACDefs
import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSession
import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApi
import Symbolic.Proofs.Swarm.CREF.TR.GhostsPure
import Symbolic.Proofs.Swarm.CREF.TR.PureCanon

/-!
# Stripping Previous Sessions from Held Records

Defines `pureStripBytes` and `pureStripPrev` to drop archived sessions from serialized session
records, and proves that stripping preserves `LeakableSecret` and turns `PureCRecRelH` records into
`TR.PureTRRecordStateInv`.
-/

public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)

/-- Record bytes with previous sessions dropped (`recordBytes { rr with previous := [] }`),
returning `b` unchanged outside the image of `recordBytes`. -/
@[expose] def pureStripBytes (b : HwBytes) : HwBytes :=
  match DY.Libsignal.Rust.decodeRecordBytes? b with
  | some rr => recordBytes { rr with previous := [] }
  | none => b

/-- Record table with every record's previous sessions dropped. -/
@[expose] def pureStripPrev (records : Participant → Option HwBytes) :
    Participant → Option HwBytes :=
  fun p => (records p).map pureStripBytes

theorem pureStripBytes_recordBytes (rr : RecordRec) :
    pureStripBytes (recordBytes rr) = recordBytes { rr with previous := [] } := by
  rw [pureStripBytes, DY.Libsignal.Rust.decodeRecordBytes?_recordBytes]
  obtain ⟨⟨_, _, _, _, _, _, _, pp, pk, _, _, _, _⟩, _⟩ := rr
  cases pp <;> cases pk <;> simp [recordBytes, DY.Libsignal.Rust.DecodeRecord.normPending]

/-- Outside the image of `recordBytes`, `pureStripBytes` returns `b` unchanged (proved without `Classical.choose`). -/
theorem pureStripBytes_of_not_mem {b : HwBytes} (h : ¬ ∃ rr : RecordRec, b = recordBytes rr) :
    pureStripBytes b = b := by
  rw [pureStripBytes, (TR.decodeRecordBytes?_eq_none_iff b).mpr h]

open Classical in
/-- `pureStripBytes` agrees pointwise with the `Classical.choose` definition. -/
theorem pureStripBytes_eq_classical (b : HwBytes) :
    pureStripBytes b =
      if h : ∃ rr : RecordRec, b = recordBytes rr then
        recordBytes { Classical.choose h with previous := [] }
      else b := by
  split
  · next h =>
    calc pureStripBytes b
        = pureStripBytes (recordBytes (Classical.choose h)) := congrArg _ (Classical.choose_spec h)
      _ = _ := pureStripBytes_recordBytes _
  · next h => exact pureStripBytes_of_not_mem h

theorem pureStripBytes_of_prev_nil {rr : RecordRec} (h : rr.previous = []) :
    pureStripBytes (recordBytes rr) = recordBytes rr := by
  rw [pureStripBytes_recordBytes]
  obtain ⟨cur, prev⟩ := rr
  change prev = [] at h
  subst h
  rfl

theorem pureStripBytes_of_singleSession {b : HwBytes} (h : SingleSession b) :
    pureStripBytes b = b := by
  obtain ⟨rr, rfl, hp⟩ := h
  exact pureStripBytes_of_prev_nil hp

theorem keyInRecord_pureStripPrev (rr : RecordRec) (k : HwBytes) :
    KeyInRecord { rr with previous := [] } k ↔ KeyInRecord rr k := Iff.rfl

private theorem recKey_pureStripPrev_iff (records : Participant → Option HwBytes) (k : HwBytes) :
    (∃ p rec, pureStripPrev records p = some (recordBytes rec) ∧ KeyInRecord rec k) ↔
      ∃ p rec, records p = some (recordBytes rec) ∧ KeyInRecord rec k := by
  constructor
  · rintro ⟨p, rec, hp, hk⟩
    unfold pureStripPrev at hp
    rcases hrp : records p with _ | b
    · rw [hrp] at hp; cases hp
    · rw [hrp, Option.map_some] at hp
      have hb := Option.some.inj hp
      cases hdec : DY.Libsignal.Rust.decodeRecordBytes? b with
      | some rr =>
        rw [pureStripBytes, hdec] at hb
        exact ⟨p, rr, hrp.trans (congrArg some (DY.Libsignal.Rust.decodeRecordBytes?_sound hdec)),
          (keyInRecord_pureStripPrev rr k).1 (TR.keyInRecord_of_recordBytes_eq hb.symm hk)⟩
      | none =>
        rw [pureStripBytes, hdec] at hb
        exact ⟨p, rec, hrp.trans (congrArg some hb), hk⟩
  · rintro ⟨p, rec, hp, hk⟩
    refine ⟨p, { rec with previous := [] }, ?_, (keyInRecord_pureStripPrev rec k).2 hk⟩
    unfold pureStripPrev
    rw [hp, Option.map_some, pureStripBytes_recordBytes]

theorem leakableSecret_pureStripPrev_iff (r : ProtocolSetup) (records : Participant → Option HwBytes)
    (used : Bool) (k : HwBytes) :
    LeakableSecret r records used k ↔ LeakableSecret r (pureStripPrev records) used k := by
  unfold LeakableSecret
  rw [recKey_pureStripPrev_iff]

theorem leakEvs_pureStripPrev {r : ProtocolSetup} {records : Participant → Option HwBytes} {used : Bool}
    {evs : List MachineEvent}
    (hevs : ∀ e ∈ evs, ∃ k, LeakableSecret r records used k ∧ e = .leak k) :
    ∀ e ∈ evs, ∃ k, LeakableSecret r (pureStripPrev records) used k ∧ e = .leak k := by
  intro e he
  obtain ⟨k, hk, rfl⟩ := hevs e he
  exact ⟨k, (leakableSecret_pureStripPrev_iff r records used k).1 hk, rfl⟩

theorem singleSession_of_pureCRecRel {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move} {p : Participant} {b : HwBytes}
    (h : PureCRecRel interp r S g ms p b) : SingleSession b := by
  rcases h with hinv | ⟨-, hpnd⟩
  · obtain ⟨_, rec, _, _, hb, _, _, hsr, _⟩ := hinv p b (by simp)
    exact ⟨rec, hb, hsr.1⟩
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      recR, hb, hsr, _⟩ := hpnd
    exact ⟨recR, hb, hsr.1⟩

theorem pureCRecRel_stripBytes_of_pureCRecRelH {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move} {p : Participant} {b : HwBytes}
    (h : PureCRecRelH interp r S g ms p b) :
    PureCRecRel interp r S g ms p (pureStripBytes b) := by
  rcases h with h | ⟨rr, rfl, -, hc⟩
  · rw [pureStripBytes_of_singleSession (singleSession_of_pureCRecRel h)]
    exact h
  · rw [pureStripBytes_recordBytes]
    exact hc

private theorem trInv_one_of_pureCRecRel {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {Z : TR.PureTRSlots} (hZ : ∀ q c, Z.canon q c) {g : Ghost}
    {ms : List Move} {p : Participant} {b : HwBytes} (hp : p = r.alice ∨ p = r.bob)
    (hrec : PureCRecRel interp r S g ms p b) :
    TR.PureTRRecordStateInv interp r S Z g ms (fun q => if q = p then some b else none) := by
  intro q c hqc
  by_cases hqp : q = p
  · subst hqp
    simp only [↓reduceIte, Option.some.injEq] at hqc
    subst hqc
    rcases hrec with hinv | ⟨rfl, hpnd⟩
    · obtain ⟨_, rec, st, stateIdx, hb, hget, hcur, hsr, hsk, _, hks, hnd⟩ :=
        hinv q b (by simp)
      exact ⟨hp, rec, st, stateIdx, hb, hget, hcur, hsr, hsk, fun _ => hZ _ _, hks, hnd⟩
    · obtain ⟨_, _, _, _, _, st, stateIdx, _, _, _, _,
        _, _, _, hget, hcur, _, _, _, _,
        _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        recR, hb, hsr, hks, hmk, hnd⟩ := hpnd
      refine ⟨hp, recR, st, stateIdx, hb, hget, hcur, hsr, ?_, fun _ => hZ _ _, hks, hnd, ?_, ?_⟩
      · intro c hc k hk; rw [hmk c hc] at hk; cases hk
      · intro c hc; rw [hmk c hc]; exact List.nodup_nil
      · intro c hc k hk; rw [hmk c hc] at hk; cases hk
  · simp only [hqp, ↓reduceIte, reduceCtorEq] at hqc

/-- `TR.PureTRRecordStateInv` of `pureStripPrev records` at any slot set whose `canon` always holds. -/
theorem trRecordStateInv_pureStripPrev {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {Z : TR.PureTRSlots} (hZ : ∀ q c, Z.canon q c) {g : Ghost}
    {ms : List Move} {records : Participant → Option HwBytes}
    (hrecs : ∀ p b, records p = some b →
      (p = r.alice ∨ p = r.bob) ∧ b ≠ [] ∧ PureCRecRelH interp r S g ms p b) :
    TR.PureTRRecordStateInv interp r S Z g ms (pureStripPrev records) := by
  intro p c hpc
  unfold pureStripPrev at hpc
  rcases hrp : records p with _ | b
  · rw [hrp] at hpc; cases hpc
  · rw [hrp, Option.map_some] at hpc
    obtain ⟨hp, -, hrec⟩ := hrecs p b hrp
    exact trInv_one_of_pureCRecRel hZ hp (pureCRecRel_stripBytes_of_pureCRecRelH hrec) p c
      (by simp only [↓reduceIte]; exact hpc)

section ConstructiveEvalSanityCheck

private def sampleSessionRec : SessionRec :=
  { sessionVersion := 4#32
    localIdentityPublic := [1#8, 2#8]
    remoteIdentityPublic := [3#8, 4#8]
    rootKey := [5#8]
    previousCounter := 0#32
    senderChain := none
    receiverChains := []
    pendingPreKey := some ([1#8], [2#8])
    pendingKyberPreKey := none
    remoteRegistrationId := 7#32
    localRegistrationId := 8#32
    aliceBaseKey := [9#8]
    pqRatchetState := [42#8, 99#8] }

-- `with_unfolding_all` unseals `WireFormat.paddedVarint` (`termination_by`) so `rfl` reduces to `@Eq.refl`.
example : Symbolic.Swarm.CREF.pqStateOf
    (recordBytes { current := sampleSessionRec, previous := [[10#8, 11#8]] }) =
    [42#8, 99#8] := by with_unfolding_all rfl

example : pureStripBytes
    (recordBytes { current := sampleSessionRec, previous := [[10#8, 11#8]] }) =
    recordBytes { current := sampleSessionRec, previous := [] } := by with_unfolding_all rfl

end ConstructiveEvalSanityCheck

end Symbolic.Swarm.CREF.CliPure
