/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefs
import LibsignalBinary.Proofs.E2E.RecordX.Length
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.Fields
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- shake: keep
import LibsignalBinary.Proofs.CodeLayout

/-!
# Composition of Inlined `SessionStructure::decode` Loop

Composes the per-step contracts of `PrevDec/LoopDefs.lean` (entry, loop head, key dispatch, four
field-arm groups, and exit entailment) into `OverPrevDecodeStmt` (`+0x1ee8 → +0x2620`) for
`message_decrypt_prekey::<Coins>::{closure#0}`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

open Std Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (PanicOomProp)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure (decryptPrekeyClosureName)
open CryptoVerification.E2E.Record.DeserializeGeneral (GenField)
open Symbolic.Swarm.TRREF.B3DeserQ (SSGQ GenFieldQ prostSSGQAt ssgqOf genFieldsQ)

/-! ## Generic `SepWPp` Sequencing and Consequence -/

/-- Sequence two `SepWPp` blocks through the intermediate pc `mid`, sharing the panic post. -/
theorem overDec_sepWPp_seq {prog : Program} {mid target : BitVec 64} {s : State}
    {P : SepProp} {Qm Q Qp : State → SepProp → Prop}
    (h1 : SepWPp prog mid s P Qm Qp)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running → Qm sm Pm →
      SepWPp prog target sm Pm Q Qp) :
    SepWPp prog target s P Q Qp := by
  intro R hm hL
  rcases h1 R hm hL with ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hmm, hQ⟩ | hpan⟩
  · rcases h2 sm Pm hpcm hrunm hQ R hmm (hsteps.codeLoaded hL) with ⟨sf, hsteps', hout⟩
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr hpan⟩

theorem overDec_sepWPp_weaken_pre {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop}
    (hent : P ⊢ P') (h : SepWPp prog ret s P' Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  exact h R (Arm64.Satisfies.mono (sepConj_mono_left hent) hm) hL

theorem overDec_sepWPp_mono_post {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Q' Qp : State → SepProp → Prop}
    (hQ : ∀ sf P_f, sf.pc = ret → sf.status = .Running → Q sf P_f → Q' sf P_f)
    (h : SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s P Q' Qp := by
  intro R hm hL
  rcases h R hm hL with ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hQf⟩ | hpan⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, P_f, hmf, hQ sf P_f hpc hrun hQf⟩⟩
  · exact ⟨sf, hsteps, Or.inr hpan⟩

/-! ## Key and Arm Composition -/

/-- Every field's encoding is non-empty (it starts with the key varint). -/
theorem overDec_enc_ne_nil (fl : GenFieldQ) : fl.enc ≠ [] := by
  unfold GenFieldQ.enc CryptoVerification.LibsignalProtoCodec.encodeKey
  intro h
  exact CryptoVerification.LibsignalProtoCodec.encodeVarint_ne_nil _ (List.append_eq_nil_iff.mp h).1

/-- A field list's encodings: the suffix after dropping the head is a suffix of the whole. -/
theorem overDec_flatMap_cons (fl : GenFieldQ) (fs : List GenFieldQ) :
    (fl :: fs).flatMap GenFieldQ.enc = fl.enc ++ fs.flatMap GenFieldQ.enc := by
  rw [List.flatMap_cons]

/-- With no pending pre-key, no field of `genFields` is `pending`. -/
theorem overDec_genFields_noPending (s : Session (List (BitVec 8)))
    (hp : s.pendingPreKey = none) (f : GenField)
    (hf : f ∈ CryptoVerification.E2E.Record.DeserializeGeneral.genFields s) :
    ∀ k, f ≠ .pending k := by
  intro k hk
  subst hk
  unfold CryptoVerification.E2E.Record.DeserializeGeneral.genFields at hf
  rw [hp] at hf
  simp only [List.mem_append, List.mem_map] at hf
  rcases hf with ((((((h | h) | h) | h) | h) | h) | ⟨c, _, hc⟩) | h
  all_goals first
    | (split at h <;> simp at h)
    | (cases hc)
    | (simp at h)

/-- Every field of a session without pending pre-keys belongs to one of the four arm groups. -/
theorem overDec_anyField_of_mem (s : Session (List (BitVec 8)))
    (hp : s.pendingPreKey = none) (hk : s.pendingKyberPreKey = none)
    (fl : GenFieldQ) (hfl : fl ∈ genFieldsQ s) : OverDecAnyField fl := by
  unfold genFieldsQ at hfl
  simp only [List.mem_append, List.mem_map] at hfl
  rcases hfl with ⟨fx, hfx, rfl⟩ | h15
  · unfold CryptoVerification.E2E.Record.L1GX.genFieldsX at hfx
    simp only [hp, hk, List.mem_append, List.mem_map,
      CryptoVerification.E2E.Record.L1GX.pendingFieldX, List.not_mem_nil, or_false] at hfx
    rcases hfx with ((((⟨f, hf, rfl⟩ | h10) | h11) | h13) | h15)
    · have hnp := overDec_genFields_noPending _ rfl f hf
      cases f with
      | pending k => exact absurd rfl (hnp k)
      | version _ => exact Or.inl trivial
      | prevCounter _ => exact Or.inl trivial
      | lik _ => exact Or.inr (Or.inl trivial)
      | rik _ => exact Or.inr (Or.inl trivial)
      | root _ => exact Or.inr (Or.inl trivial)
      | sender _ => exact Or.inr (Or.inr (Or.inl trivial))
      | recv _ => exact Or.inr (Or.inr (Or.inr trivial))
    · split at h10 <;> simp only [List.mem_singleton, List.not_mem_nil] at h10
      subst h10; exact Or.inl trivial
    · split at h11 <;> simp only [List.mem_singleton, List.not_mem_nil] at h11
      subst h11; exact Or.inl trivial
    · split at h13 <;> simp only [List.mem_singleton, List.not_mem_nil] at h13
      subst h13; exact Or.inr (Or.inl trivial)
    · simp at h15
  · split at h15 <;> simp only [List.mem_singleton, List.not_mem_nil] at h15
    subst h15; exact Or.inr (Or.inl trivial)

/-- A version-4 session has a non-empty field list (tag 1 first). -/
theorem overDec_genFieldsQ_ne_nil (s : Session (List (BitVec 8)))
    (hv : s.state.sessionVersion = 4#32) : genFieldsQ s ≠ [] := by
  unfold genFieldsQ CryptoVerification.E2E.Record.L1GX.genFieldsX
    CryptoVerification.E2E.Record.DeserializeGeneral.genFields
  simp [hv]

/-- Inductive freshness chain for a field list starting from decoded value `v`: each field is fresh against the accumulator after prior fields. -/
inductive OverDecFreshChain : List GenFieldQ → SSGQ → Prop
  | nil (v : SSGQ) : OverDecFreshChain [] v
  | cons (fl : GenFieldQ) (fs : List GenFieldQ) (v : SSGQ) :
      fl.Fresh v → OverDecFreshChain fs (v.apply fl) → OverDecFreshChain (fl :: fs) v

theorem overDecFreshChain_cons_inv {fl : GenFieldQ} {fs : List GenFieldQ} {v : SSGQ}
    (h : OverDecFreshChain (fl :: fs) v) : fl.Fresh v ∧ OverDecFreshChain fs (v.apply fl) := by
  cases h with
  | cons _ _ _ h1 h2 => exact ⟨h1, h2⟩

/-- The indexed freshness of `ssgqAfter`-style folds gives the fresh chain. -/
theorem overDecFreshChain_of_getElem (fs : List GenFieldQ) (v : SSGQ)
    (h : ∀ k (hk : k < fs.length), (fs[k]'hk).Fresh ((fs.take k).foldl SSGQ.apply v)) :
    OverDecFreshChain fs v := by
  induction fs generalizing v with
  | nil => exact .nil v
  | cons fl fs ih =>
    refine .cons fl fs v (h 0 (Nat.zero_lt_succ _)) (ih (v.apply fl) ?_)
    intro k hk
    exact h (k + 1) (Nat.succ_lt_succ hk)

/-! ## Loop Exit Entailment -/

/-- The cursor and slice cells at the exit collapse to the scratch regions: the cursor word
`q + 0xbe8` and the cursor run `q + 0xbf0` to `memRegion (q + 0xbe8) 136`, the slice header
`{ptr, len}` at `q + 0x920` to `memRegion (q + 0x920) 16`. -/
theorem overDec_exit_cells (q c p l : BitVec 64) :
    ((q + 0xbe8#64) ↦₆₄ c) ∗ ((q + 0x920#64) ↦₆₄ p) ∗ ((q + 0x920#64 + 8#64) ↦₆₄ l) ∗
        memRegion (q + 0xbf0#64) 128 ⊢
      memRegion (q + 0xbe8#64) 136 ∗ memRegion (q + 0x920#64) 16 := by
  have h136 : memRegion (q + 0xbe8#64) 136 =
      memRegion (q + 0xbe8#64) 8 ∗ memRegion (q + 0xbf0#64) 128 :=
    memRegion_split' (n := 8) (k := 128) (by decide) (by bv_omega) (by decide)
  have h16 : memRegion (q + 0x920#64) 16 =
      memRegion (q + 0x920#64) 8 ∗ memRegion (q + 0x920#64 + 8#64) 8 :=
    memRegion_split' (n := 8) (k := 8) (by decide) rfl (by decide)
  rw [h136, h16]
  refine Entails.trans ?_ (Entails.of_eq (P := (memRegion (q + 0xbe8#64) 8 ∗
      memRegion (q + 0x920#64) 8 ∗ memRegion (q + 0x920#64 + 8#64) 8 ∗
      memRegion (q + 0xbf0#64) 128)) (by ac_rfl))
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono_left (pointsTo64_entails_memRegion _ _)))

theorem overDec_entails_anyHeap_right {P T : SepProp} (h : P ⊢ T) : P ⊢ T ∗ anyHeap := by
  refine Entails.trans h ?_
  refine Entails.trans (Entails.of_eq (sepConj_emp T).symm) ?_
  exact sepConj_mono_right (entails_anyHeap _)

theorem overDec_assoc_anyHeap (A B C D : SepProp) :
    (A ∗ B ∗ C ∗ D) ∗ anyHeap ⊢ A ∗ B ∗ C ∗ D ∗ anyHeap :=
  Entails.of_eq (by simp only [sepConj_assoc])

/-- At loop exit (`rest = []`), `overDecHeapExt` entails `overPrevElemAtExt A`, `overDecScratchPostExt A`, stack, and `A.pool` (using `g.enc ≠ []` to rule out `encCap = 0`). -/
theorem overDec_exit_ext {A : RustAlloc} (g : OverDecG) (v : SSGQ) (hne : g.enc ≠ []) :
    overDecHeapExt A g [] v ⊢
      overPrevElemAtExt A g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗ overDecScratchPostExt A g.q v ∗
        stackAt g.q overDecStackX ∗ A.pool ∗ anyHeap := by
  refine Entails.trans ?_ (overDec_assoc_anyHeap _ _ _ _)
  refine overDec_entails_anyHeap_right ?_
  unfold overDecHeapExt CryptoVerification.LibsignalTripleRatchet.Prost.sliceCursorAfter
  have hcells := overDec_exit_cells g.q (g.q + 0x920#64)
    (g.encPtr + BitVec.ofNat 64 (g.enc.length - ([] : List (BitVec 8)).length))
    (BitVec.ofNat 64 ([] : List (BitVec 8)).length)
  refine Entails.trans (Entails.of_eq (Q :=
    (((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗ ((g.q + 0x920#64) ↦₆₄
        (g.encPtr + BitVec.ofNat 64 (g.enc.length - ([] : List (BitVec 8)).length))) ∗
      ((g.q + 0x920#64 + 8#64) ↦₆₄ BitVec.ofNat 64 ([] : List (BitVec 8)).length) ∗
      memRegion (g.q + 0xbf0#64) 128) ∗
    (overPrevElemRestExt A g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗ (g.encPtr ↦ₛ g.enc) ∗
      prostSSGQAt A (g.q + 0x930#64) v ∗
      memRegion (g.q + 0xa88#64) 8 ∗ memRegion (g.q + 0xa90#64) 344 ∗
      stackAt g.q overDecStackX ∗ A.pool)) (by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left hcells) ?_
  unfold overPrevElemAtExt overDecScratchPostExt overPrevElemRestExt vecU8At
  split_ifs with hcap
  · refine Entails.trans (Entails.of_eq (Q := ⌜g.enc.length ≤ g.encCap.toNat ∧
        g.encCap.toNat < 2 ^ 63 ∧ g.encPtr ≠ 0⌝ ∗ _) (by sep_focus)) ?_
    refine Entails.pure_left ?_
    rintro ⟨hl, -, -⟩
    exfalso
    apply hne
    rw [hcap] at hl
    simpa using hl
  · sep_entail

theorem overDec_exit (g : OverDecG) (v : SSGQ) (hne : g.enc ≠ []) :
    overDecHeap g [] v ⊢
      overPrevElemAt g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗ overDecScratchPost g.q v ∗
        stackAt g.q overDecStackX ∗ CryptoVerification.E2E.Record.A0.pool ∗ anyHeap :=
  overDec_exit_ext g v hne

/-! ## Field Loop Induction -/

theorem overDec_flatMap_ne_nil (fs : List GenFieldQ) (hfs : fs ≠ []) :
    fs.flatMap GenFieldQ.enc ≠ [] := by
  rcases fs with _ | ⟨fl, fs⟩
  · exact absurd rfl hfs
  · rw [overDec_flatMap_cons]
    intro h
    exact overDec_enc_ne_nil fl (List.append_eq_nil_iff.mp h).1

/-- The archived session's encoding is shorter than `2 ^ 62`. -/
theorem overDec_encSession_length_lt (sess : Session (List (BitVec 8)))
    (hscope : Symbolic.Swarm.TRREF.B3Defs.DeserializeScopeP_Q
      Symbolic.Swarm.TRREF.B3Defs.NonEmptyV1Q ⟨some sess⟩) :
    (CryptoVerification.E2E.Record.encSession sess).length < 2 ^ 62 := by
  have h1 := Symbolic.Swarm.TRREF.B3DeserQ.encodeRecord_length_lt62_of_Q hscope
  have h3 : (CryptoVerification.E2E.Record.encSession sess).length ≤
      (CryptoVerification.E2E.Record.encodeRecord ⟨some sess⟩).length := by
    unfold CryptoVerification.E2E.Record.encodeRecord CryptoVerification.E2E.Record.msgField
    dsimp only [Option.map_some]
    exact CryptoVerification.E2E.RecordX.lenField_length_ge' 1
      (CryptoVerification.E2E.Record.encSession sess)
  omega

/-- `recFieldsQ_fresh` restated on the field list `recFieldsQ r`, without `ssgqAfter`. -/
theorem overDec_freshChain_recFieldsQ (r : SessionRecord (List (BitVec 8)))
    (hscope : Symbolic.Swarm.TRREF.B3Defs.DeserializeScopeP_Q
      Symbolic.Swarm.TRREF.B3Defs.NonEmptyV1Q r) :
    OverDecFreshChain (Symbolic.Swarm.TRREF.B3DeserQ.recFieldsQ r) SSGQ.empty := by
  refine overDecFreshChain_of_getElem _ _ ?_
  intro k hk
  exact Symbolic.Swarm.TRREF.B3DeserQ.recFieldsQ_fresh r hscope k hk

/-- The fields of the archived session are fresh along the decode. -/
theorem overDec_freshChain_genFieldsQ (sess : Session (List (BitVec 8)))
    (hscope : Symbolic.Swarm.TRREF.B3Defs.DeserializeScopeP_Q
      Symbolic.Swarm.TRREF.B3Defs.NonEmptyV1Q ⟨some sess⟩) :
    OverDecFreshChain (genFieldsQ sess) SSGQ.empty := by
  have h := overDec_freshChain_recFieldsQ _ hscope
  rwa [Symbolic.Swarm.TRREF.B3DeserQ.recFieldsQ_of_some (s := sess) rfl] at h

/-- Decoding all the fields of the archived session gives `ssgqOf sess`. -/
theorem overDec_fold_genFieldsQ (sess : Session (List (BitVec 8)))
    (hscope : Symbolic.Swarm.TRREF.B3Defs.DeserializeScopeP_Q
      Symbolic.Swarm.TRREF.B3Defs.NonEmptyV1Q ⟨some sess⟩) :
    (genFieldsQ sess).foldl SSGQ.apply SSGQ.empty = ssgqOf sess := by
  have hrec : Symbolic.Swarm.TRREF.B3DeserQ.recFieldsQ ⟨some sess⟩ = genFieldsQ sess :=
    Symbolic.Swarm.TRREF.B3DeserQ.recFieldsQ_of_some (r := ⟨some sess⟩) (s := sess) rfl
  have h := Symbolic.Swarm.TRREF.B3DeserQ.ssgqAfter_recFieldsQ ⟨some sess⟩ hscope sess rfl
  unfold Symbolic.Swarm.TRREF.B3DeserQ.ssgqAfter at h
  rw [List.take_length, hrec] at h
  exact h

/-- The fields of the archived session are in the four groups and well-formed. -/
theorem overDec_mem_genFieldsQ (sess : Session (List (BitVec 8)))
    (hscope : Symbolic.Swarm.TRREF.B3Defs.DeserializeScopeP_Q
      Symbolic.Swarm.TRREF.B3Defs.NonEmptyV1Q ⟨some sess⟩)
    (hpp : sess.pendingPreKey = none) (hpk : sess.pendingKyberPreKey = none) :
    ∀ fl ∈ genFieldsQ sess, OverDecAnyField fl ∧ fl.Ok := by
  have hrec : Symbolic.Swarm.TRREF.B3DeserQ.recFieldsQ ⟨some sess⟩ = genFieldsQ sess :=
    Symbolic.Swarm.TRREF.B3DeserQ.recFieldsQ_of_some (r := ⟨some sess⟩) (s := sess) rfl
  have hok := Symbolic.Swarm.TRREF.B3DeserQ.recFieldsQ_ok ⟨some sess⟩ hscope
  rw [hrec] at hok
  exact fun fl hfl => ⟨overDec_anyField_of_mem sess hpp hpk fl hfl, hok fl hfl⟩

theorem overDec_encSession_eq (sess : Session (List (BitVec 8)))
    (hscope : Symbolic.Swarm.TRREF.B3Defs.DeserializeScopeP_Q
      Symbolic.Swarm.TRREF.B3Defs.NonEmptyV1Q ⟨some sess⟩) :
    CryptoVerification.E2E.Record.encSession sess = (genFieldsQ sess).flatMap GenFieldQ.enc :=
  Symbolic.Swarm.TRREF.B3DeserQ.encSession_eq_genFieldsQ ⟨some sess⟩ hscope sess rfl

/-! ## Top-Level Loop Composition -/

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
