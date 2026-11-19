/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementWeak.Defs

/-!
# Honest entries and `SimInvW` helpers for the weak refinement

Proves uniqueness, raw-key agreement, and in-transit synchronization for `HonestEntryInvW`
and `SimInvW` under `SpqrWLocal`.
-/

public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.LibsignalSM.Proofs.Refinement

open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst CryptoGames.Ratchet.LibsignalSim
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

variable {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ]
  [SampleableType PQC] {ℓ : ℕ}

theorem HonestEntryInvW.congr_epExp {P : Params PQ PQC} (Inv : PQ → Prop) {Dh : DHFun (BitVec 256) Pt}
    {encT : Pt → PublicKey} {epExp epExp' : ℕ → BitVec 256}
    {wc : List (BitVec 8) × Fig8C Pt}
    (h : HonestEntryInvW P Inv Dh encT epExp wc)
    (heq : epExp' wc.2.1.1 = epExp wc.2.1.1) :
    HonestEntryInvW P Inv Dh encT epExp' wc := by
  unfold HonestEntryInvW at h ⊢
  dsimp only at h ⊢
  rw [heq]
  exact h

namespace WP2A.H3

theorem find_fig8_eq_of_map {ℓ : ℕ}
    {L_mir : List (SM.Record (Plain ℓ) (List (BitVec 8)))}
    {L_fig8 : List (SM.Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))}
    (hmap : L_mir.map (fun r => (r.pos, r.ct)) =
      L_fig8.map (fun r => (r.pos, LibsignalSim.toWire r.ct)))
    (Q : Party) (w : List (BitVec 8)) (c : Fig8C Pt)
    (hiff : ∀ r ∈ L_fig8, decide (r.ct = c) = decide (LibsignalSim.toWire r.ct = w)) :
    (L_mir.find? fun r => r.pos.sender == Q && decide (r.ct = w)).map (fun r => (r.pos, r.ct)) =
      (L_fig8.find? fun r => r.pos.sender == Q && decide (r.ct = c)).map
        (fun r => (r.pos, LibsignalSim.toWire r.ct)) := by
  induction L_mir generalizing L_fig8 with
  | nil =>
    cases L_fig8 with
    | nil => rfl
    | cons _ _ => cases hmap
  | cons r₁ L₁ ih =>
    cases L_fig8 with
    | nil => cases hmap
    | cons r₂ L₂ =>
      simp only [List.map_cons, List.cons.injEq] at hmap
      rcases hmap with ⟨hhead, htail⟩
      have hpos : r₁.pos = r₂.pos := congrArg Prod.fst hhead
      have hct : r₁.ct = LibsignalSim.toWire r₂.ct := congrArg Prod.snd hhead
      have hr₂ := hiff r₂ List.mem_cons_self
      simp only [List.find?_cons, hpos, hr₂, ← hct]
      split
      · simp [hpos, hct]
      · exact ih htail (fun r hr => hiff r (List.mem_cons_of_mem r₂ hr))

end WP2A.H3

theorem deliver_inTransit_mem {ℓ : ℕ}
    {s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
    {s : SimState PQ Pt ℓ}
    {s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (hmeta : SameMeta s_R s s_fig8)
    (htrans_hon : ∀ r ∈ s_fig8.trans,
      (LibsignalSim.toWire r.ct, r.ct) ∈ s.honest ∧ r.pos.sender = Party.senderOf r.ct.1.1)
    (Q : Party) (w : List (BitVec 8))
    {r_mir : SM.Record (Plain ℓ) (List (BitVec 8))}
    (htr_mir : s.mir.inTransit Q.other w = some r_mir) :
    ∃ c, (w, c) ∈ s.honest ∧ Party.senderOf c.1.1 = Q.other := by
  have hmir_mem : r_mir ∈ s.mir.trans := List.mem_of_find?_eq_some htr_mir
  have hmir_pred := List.find?_some htr_mir
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hmir_pred
  have hmap_mem : (r_mir.pos, w) ∈ s_fig8.trans.map (fun r => (r.pos, LibsignalSim.toWire r.ct)) := by
    rw [← hmeta.htrans_fig8, ← hmir_pred.2]
    exact List.mem_map_of_mem hmir_mem
  rw [List.mem_map] at hmap_mem
  rcases hmap_mem with ⟨r₀, hr₀, hpair₀⟩
  have hpos₀ : r₀.pos = r_mir.pos := congrArg Prod.fst hpair₀
  have hw₀ : LibsignalSim.toWire r₀.ct = w := congrArg Prod.snd hpair₀
  refine ⟨r₀.ct, ?_, ?_⟩
  · rw [← hw₀]
    exact (htrans_hon r₀ hr₀).1
  · rw [← (htrans_hon r₀ hr₀).2, hpos₀, hmir_pred.1]

theorem SimInvW.mono_r {P : Params PQ PQC} (Inv : PQ → Prop) {ℓ : ℕ} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey} {qep q r r' : ℕ}
    {x₀ : BitVec 256}
    {s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
    {s : SimState PQ Pt ℓ}
    {s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {ec : Party → BitVec 256}
    {winBefore : ℕ → Bool}
    {epExp : ℕ → BitVec 256}
    (hinv : SimInvW P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (hle : r' ≤ r) :
    SimInvW P Inv ℓ Dh encPt encT qep q r' x₀ s_R s s_fig8 ec winBefore epExp :=
  { hinv with
    hamb := by have := hinv.hamb; omega
    hamb_strict := fun h => by have := hinv.hamb_strict h; omega
    hidx_le := fun Q => by have := hinv.hidx_le Q; omega
    hhon_len := by have := hinv.hhon_len; omega }

end CryptoGames.LibsignalSM.Proofs.Refinement
