/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserDefsX -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.ChainDefs

public section

set_option autoImplicit false

/-!
# Leaf-Parameterized `SessionRecord::deserialize` Assembly

Assembles `chainMergeGenW_ok`, `mergeFieldGenW_ok`, `deserializeExactW_ok`, and
`deserializeBodyGW_ok` from abstract leaf bundles (`ChainLeavesW`, `MergeFieldLeavesW`,
`DeserLeavesW`) across fixed-allocator, arbitrary-allocator (`A : RustAlloc`), and relocatable
`[LibsignalPlacement]` formulations.
-/

namespace Proofs.libsignal.Hooks2

open Arm64 ProofLib SepProp CryptoVerification
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed
open CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.Serialization

theorem L1_DeserAssemblyW : True := trivial

/-! ## 1. `ChainMerge` Assembly (`ChainLeavesW` → `ChainMergeGenOkAtW`) -/

section Placed

open Arm64.Obj CryptoVerification.E2E.Record.Placed

theorem L1_DeserAssemblyW_Placed : True := trivial

/-- Return state of relocatable `chainMerge` (block `11`) with `chainMergeGenPlacedSpecW.post`. -/
@[expose] def ChainRetGPlacedW [LibsignalPlacement] (x : ChainMergeGenGhost) (R : SepProp) (s0 sf : State) : Prop :=
  Returned s0 sf ∧ CallingConventionPreserved s0 sf ∧
    (sf.mem ⊨ chainMergeGenPlacedSpecW.post x s0 sf ∗ R)

/-- Bundle of the 5 relocatable `ChainMerge` leaf theorems on `lsProg_11 H`. -/
structure ChainLeavesPlacedW [LibsignalPlacement] (H : LibsignalHooks) : Prop where
  entry : ∀ (x : ChainMergeGenGhost) (R : SepProp) (s0 : State),
    s0.pc = (blkPl_11).base →
    s0.status = .Running →
    (s0.mem ⊨ chainMergeGenPlacedSpecW.pre x s0 ∗ R) →
    s0.spAligned = true →
    ChainStepGPlacedW H x R s0 s0 (ChainLoopGPlacedW x R s0 0)
  srk : ∀ (x : ChainMergeGenGhost) (R : SepProp) (s0 : State) (k : Nat) (s : State)
    (hk : k < x.c.fields.length),
    ((x.c.fields[k]'hk).tag = 1 ∨ (x.c.fields[k]'hk).tag = 2) →
    ChainLoopGPlacedW x R s0 k s →
    ChainStepGPlacedW H x R s0 s (ChainLoopGPlacedW x R s0 (k + 1))
  ck : ∀ (x : ChainMergeGenGhost) (R : SepProp) (s0 : State) (k : Nat) (s : State)
    (hk : k < x.c.fields.length),
    (x.c.fields[k]'hk).tag = 3 →
    ChainLoopGPlacedW x R s0 k s →
    ChainStepGPlacedW H x R s0 s (ChainLoopGPlacedW x R s0 (k + 1))
  keys : ∀ (x : ChainMergeGenGhost) (R : SepProp) (s0 : State) (k : Nat) (s : State)
    (hk : k < x.c.fields.length),
    (x.c.fields[k]'hk).tag = 4 →
    ChainLoopGPlacedW x R s0 k s →
    ChainStepGPlacedW H x R s0 s (ChainLoopGPlacedW x R s0 (k + 1))
  exit : ∀ (x : ChainMergeGenGhost) (R : SepProp) (s0 s : State),
    ChainLoopGPlacedW x R s0 x.c.fields.length s →
    ChainStepGPlacedW H x R s0 s (ChainRetGPlacedW x R s0)

/-- Induction over the remaining `m` fields of `x.c.fields` on `lsProg_11 H`. -/
theorem chainLoopGPlacedW_run [LibsignalPlacement] (H : LibsignalHooks)
    (hL : ChainLeavesPlacedW H) {x : ChainMergeGenGhost} {R : SepProp} {s0 : State} :
    ∀ (m k : Nat) (s : State), k + m = x.c.fields.length →
      ChainLoopGPlacedW x R s0 k s →
      reaches_outcome (lsProg_11 H) chainMergeGenPlacedSpecW x R s0 s := by
  intro m
  induction m with
  | zero =>
    intro k s hk hs
    simp only [Nat.add_zero] at hk
    subst hk
    refine segStepG_then (hL.exit x R s0 s hs) ?_
    intro sf ⟨hret, hcc, hmem⟩
    exact reaches_outcome.of_outcome (Or.inl ⟨hret, hcc, hmem⟩)
  | succ m ih =>
    intro k s hk hs
    have hlt : k < x.c.fields.length := by omega
    have next : ∀ s', ChainLoopGPlacedW x R s0 (k + 1) s' →
        reaches_outcome (lsProg_11 H) chainMergeGenPlacedSpecW x R s0 s' :=
      fun s' hs' => ih (k + 1) s' (by omega) hs'
    rcases chainField_tag_cases (x.c.fields[k]'hlt) with h12 | h3 | h4
    · exact segStepG_then (hL.srk x R s0 k s hlt h12 hs) next
    · exact segStepG_then (hL.ck x R s0 k s hlt h3 hs) next
    · exact segStepG_then (hL.keys x R s0 k s hlt h4 hs) next

/-- Relocatable `Chain::merge` (block `11`) on an arbitrary well-formed `ChainG`. -/
theorem chainMergeGenPlacedW_ok [LibsignalPlacement] (H : LibsignalHooks)
    (hL : ChainLeavesPlacedW H) :
    ChainMergeGenPlacedOkW H := by
  unfold ChainMergeGenPlacedOkW
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hal
  exact segStepG_then (hL.entry x R s0 hpc hrun hpre hal) fun s hs =>
    chainLoopGPlacedW_run H hL x.c.fields.length 0 s (Nat.zero_add _) hs

/-- Bundle of the 6 relocatable `MergeField` tag-leaf theorems on `lsProg_15 H`. -/
structure MergeFieldLeavesPlacedW [LibsignalPlacement] (H : LibsignalHooks) : Prop where
  tag1 : MergeFieldGenPlacedOkW H (fun fl => fl.tag = 1)
  tag234 : MergeFieldGenPlacedOkW H (fun fl => fl.tag = 2 ∨ fl.tag = 3 ∨ fl.tag = 4)
  tag5 : MergeFieldGenPlacedOkW H (fun fl => fl.tag = 5)
  tag6 : ChainMergeGenPlacedOkW H → MergeFieldGenPlacedOkW H (fun fl => fl.tag = 6)
  tag7 : ChainMergeGenPlacedOkW H → MergeFieldGenPlacedOkW H (fun fl => fl.tag = 7)
  tag9 : MergeFieldGenPlacedOkW H (fun fl => fl.tag = 9)

theorem mergeFieldGenPlacedSpecW_pre_iff [LibsignalPlacement] {P : GenField → Prop}
    {x : MergeFieldGenGhost} {s0 : State} {R : SepProp} :
    (s0.mem ⊨ (mergeFieldGenPlacedSpecW P).pre x s0 ∗ R) ↔
      P x.fld ∧ (s0.mem ⊨ (mergeFieldGenPlacedSpecW (fun _ => True)).pre x s0 ∗ R) := by
  have hraw (Q : GenField → Prop) :
      (s0.mem ⊨ (mergeFieldGenPlacedSpecW Q).pre x s0 ∗ R) ↔
        LibsignalCodeRoLoaded lsmpl s0.mem ∧ (s0.mem ⊨ (mergeFieldGenRawSpecW Q).pre x s0 ∗ R) := by
    dsimp only [mergeFieldGenPlacedSpecW, LibsignalTripleRatchet.withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  rw [hraw P, hraw (fun _ => True)]
  simp only [mergeFieldGenRawSpecW, sepConj_assoc, satisfies_pure_sepConj]
  tauto

theorem mergeFieldGenPlacedOkW_of_imp [LibsignalPlacement] (H : LibsignalHooks)
    {P Q : GenField → Prop} (h : ∀ fl, P fl → Q fl)
    (hQ : MergeFieldGenPlacedOkW H Q) :
    MergeFieldGenPlacedOkW H P := by
  unfold MergeFieldGenPlacedOkW at hQ ⊢
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hal
  rw [mergeFieldGenPlacedSpecW_pre_iff] at hpre
  exact hQ.mono_outcome x R s0 hpc hrun (mergeFieldGenPlacedSpecW_pre_iff.mpr ⟨h x.fld hpre.1, hpre.2⟩) hal (fun _ hout => hout)

theorem mergeFieldGenPlacedOkW_or [LibsignalPlacement] (H : LibsignalHooks)
    {P Q : GenField → Prop}
    (hP : MergeFieldGenPlacedOkW H P) (hQ : MergeFieldGenPlacedOkW H Q) :
    MergeFieldGenPlacedOkW H (fun fl => P fl ∨ Q fl) := by
  unfold MergeFieldGenPlacedOkW at hP hQ ⊢
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hal
  rw [mergeFieldGenPlacedSpecW_pre_iff] at hpre
  rcases hpre.1 with hp | hq
  · exact hP.mono_outcome x R s0 hpc hrun (mergeFieldGenPlacedSpecW_pre_iff.mpr ⟨hp, hpre.2⟩) hal (fun _ hout => hout)
  · exact hQ.mono_outcome x R s0 hpc hrun (mergeFieldGenPlacedSpecW_pre_iff.mpr ⟨hq, hpre.2⟩) hal (fun _ hout => hout)

/-- Relocatable `SessionStructure::merge_field` (block `15`) on all in-scope `GenField` tags. -/
theorem mergeFieldGenPlacedW_ok [LibsignalPlacement] (H : LibsignalHooks)
    (hL : MergeFieldLeavesPlacedW H) (hCh : ChainMergeGenPlacedOkW H) :
    MergeFieldGenPlacedOkW H (fun _ => True) := by
  have hAll :=
    mergeFieldGenPlacedOkW_or H hL.tag1
      (mergeFieldGenPlacedOkW_or H hL.tag234
        (mergeFieldGenPlacedOkW_or H hL.tag5
          (mergeFieldGenPlacedOkW_or H (hL.tag6 hCh)
            (mergeFieldGenPlacedOkW_or H (hL.tag7 hCh) hL.tag9))))
  refine mergeFieldGenPlacedOkW_of_imp H (fun fl _ => ?_) hAll
  cases fl <;> simp [GenField.tag]

/-- Image-free exact-postcondition `SessionRecord::deserialize` contract (`deserOutRecordG` niche form). -/
@[expose] def deserializeExactRawSpecW : Spec DeserializeGenGhost where
  pre := deserializeGenRawSpec.pre
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.p ↦ₛ CryptoVerification.E2E.Record.encodeRecord x.r) ∗
      deserOutRecordG x.out x.r ∗
      stackAt s0.sp recDeserializeStack
  onPanic := deserializeGenRawSpec.onPanic

/-- Relocatable exact-postcondition `SessionRecord::deserialize` contract on block `46`, carrying
`LibsignalCodeRoLoaded lsmpl`. -/
abbrev deserializeExactPlacedSpecW [LibsignalPlacement] : Spec DeserializeGenGhost :=
  LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl deserializeExactRawSpecW

/-- Return state of relocatable `SessionRecord::deserialize` (block `46`) with `deserOutRawG`. -/
@[expose] def DeserRetGPlaced (x : DeserializeGenGhost) (R : SepProp) (s0 sf : State) : Prop :=
  Returned s0 sf ∧ CallingConventionPreserved s0 sf ∧ (sf.mem ⊨ deserOutRawG x s0 sf ∗ R)

/-- Bundle of the 3 relocatable `SessionRecord::deserialize` leaf theorems on `lsProg_46 H`. -/
structure DeserLeavesPlacedW [LibsignalPlacement] (H : LibsignalHooks) : Prop where
  entry : ∀ (x : DeserializeGenGhost) (R : SepProp) (s0 : State),
    s0.pc = (blkPl_46).base →
    s0.status = .Running →
    (s0.mem ⊨ deserializeGenPlacedSpec.pre x s0 ∗ R) →
    s0.spAligned = true →
    DeserStepGPlacedW H x R s0 s0 (DeserLoopGPlacedW x R s0 0)
  iter : MergeFieldGenPlacedOkW H (fun _ => True) →
    ∀ (x : DeserializeGenGhost) (R : SepProp) (s0 : State) (k : Nat) (s : State),
      DeserializeScope x.r →
      k < (recFields x.r).length →
      DeserLoopGPlacedW x R s0 k s →
      DeserStepGPlacedW H x R s0 s (DeserLoopGPlacedW x R s0 (k + 1))
  exit : ∀ (x : DeserializeGenGhost) (R : SepProp) (s0 s : State),
    DeserializeScope x.r →
    DeserLoopGPlacedW x R s0 (recFields x.r).length s →
    DeserStepGPlacedW H x R s0 s (DeserRetGPlaced x R s0)

/-- Induction over the remaining `m` fields of `recFields x.r` for `deserializeExactPlacedSpecW`. -/
theorem deserLoopGPlacedW_run_exact [LibsignalPlacement] (H : LibsignalHooks)
    (hD : DeserLeavesPlacedW H) (hMF : MergeFieldGenPlacedOkW H (fun _ => True))
    {x : DeserializeGenGhost} {R : SepProp} {s0 : State} (hr : DeserializeScope x.r) :
    ∀ (m k : Nat) (s : State), k + m = (recFields x.r).length →
      DeserLoopGPlacedW x R s0 k s →
      reaches_outcome (lsProg_46 H) deserializeExactPlacedSpecW x R s0 s := by
  intro m
  induction m with
  | zero =>
    intro k s hk hs
    simp only [Nat.add_zero] at hk
    subst hk
    refine segStepG_then (hD.exit x R s0 s hr hs) ?_
    rintro sf ⟨hret, hcc, hmem⟩
    exact reaches_outcome.of_outcome (Or.inl ⟨hret, hcc, hmem⟩)
  | succ m ih =>
    intro k s hk hs
    have hlt : k < (recFields x.r).length := by omega
    exact segStepG_then (hD.iter hMF x R s0 k s hr hlt hs) fun s' hs' =>
      ih (k + 1) s' (by omega) hs'

/-- Relocatable exact `SessionRecord::deserialize` contract on `lsProg_46 H`. -/
theorem deserializeExactPlacedW_ok [LibsignalPlacement] (H : LibsignalHooks)
    (hD : DeserLeavesPlacedW H) (hMF : MergeFieldGenPlacedOkW H (fun _ => True)) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base deserializeExactPlacedSpecW := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hal
  have ⟨_, hpre0⟩ := LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
  have hr : DeserializeScope x.r := by
    simp only [deserializeExactRawSpecW, deserializeGenRawSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre0
    exact hpre0.1.2.2.2
  exact segStepG_then (hD.entry x R s0 hpc hrun hpre hal) fun s hs =>
    deserLoopGPlacedW_run_exact H hD hMF hr _ 0 s (Nat.zero_add _) hs

/-- Combined relocatable assembly from `ChainLeavesPlacedW`, `MergeFieldLeavesPlacedW`, and `DeserLeavesPlacedW`. -/
theorem deserializeExactPlacedW_ok_of_leaves [LibsignalPlacement] (H : LibsignalHooks)
    (hChain : ChainLeavesPlacedW H) (hMF : MergeFieldLeavesPlacedW H) (hD : DeserLeavesPlacedW H) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base deserializeExactPlacedSpecW :=
  deserializeExactPlacedW_ok H hD (mergeFieldGenPlacedW_ok H hMF (chainMergeGenPlacedW_ok H hChain))

/-- Representation bridge from `deserOutRawG` to `deserializeGenRawSpec.post`. -/
theorem deserOutGPlacedW_post
    (hRepr : ∀ (r : SessionRecord (List (BitVec 8))), DeserializeScope r → ∀ (out : BitVec 64),
      deserOutRecordG out r ⊢ ∃∗ g : RecordGhost, ⌜CanonRecord g r⌝ ∗ sessionRecordAt A0 out g r)
    (x : DeserializeGenGhost) (hr : DeserializeScope x.r) (s0 sf : State) :
    deserOutRawG x s0 sf ⊢ deserializeGenRawSpec.post x s0 sf := by
  dsimp only [deserOutRawG, deserializeGenRawSpec]
  refine sepConj_mono_right (sepConj_mono_right ?_)
  refine Entails.trans (sepConj_mono_left (hRepr x.r hr x.out)) ?_
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun g => Entails.sepExists_right g ?_
  rw [sepConj_assoc]
  exact Entails.refl _

/-- Induction over `recFields x.r` for `deserializeGenPlacedSpec` on `lsProg_46 H`. -/
theorem deserLoopGPlacedW_run [LibsignalPlacement] (H : LibsignalHooks)
    (hD : DeserLeavesPlacedW H) (hMF : MergeFieldGenPlacedOkW H (fun _ => True))
    (hRepr : ∀ (r : SessionRecord (List (BitVec 8))), DeserializeScope r → ∀ (out : BitVec 64),
      deserOutRecordG out r ⊢ ∃∗ g : RecordGhost, ⌜CanonRecord g r⌝ ∗ sessionRecordAt A0 out g r)
    {x : DeserializeGenGhost} {R : SepProp} {s0 : State} (hr : DeserializeScope x.r) :
    ∀ (m k : Nat) (s : State), k + m = (recFields x.r).length →
      DeserLoopGPlacedW x R s0 k s →
      reaches_outcome (lsProg_46 H) deserializeGenPlacedSpec x R s0 s := by
  intro m
  induction m with
  | zero =>
    intro k s hk hs
    simp only [Nat.add_zero] at hk
    subst hk
    refine segStepG_then (hD.exit x R s0 s hr hs) ?_
    rintro sf ⟨hret, hcc, hmem⟩
    exact reaches_outcome.of_outcome (Or.inl ⟨hret, hcc,
      Satisfies.mono (sepConj_mono_left (deserOutGPlacedW_post hRepr x hr s0 sf)) hmem⟩)
  | succ m ih =>
    intro k s hk hs
    have hlt : k < (recFields x.r).length := by omega
    exact segStepG_then (hD.iter hMF x R s0 k s hr hlt hs) fun s' hs' =>
      ih (k + 1) s' (by omega) hs'

/-- Relocatable general `SessionRecord::deserialize` contract on `lsProg_46 H`. -/
theorem deserializeBodyGPlacedW_ok [LibsignalPlacement] (H : LibsignalHooks)
    (hD : DeserLeavesPlacedW H) (hMF : MergeFieldGenPlacedOkW H (fun _ => True))
    (hRepr : ∀ (r : SessionRecord (List (BitVec 8))), DeserializeScope r → ∀ (out : BitVec 64),
      deserOutRecordG out r ⊢ ∃∗ g : RecordGhost, ⌜CanonRecord g r⌝ ∗ sessionRecordAt A0 out g r) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base deserializeGenPlacedSpec := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hal
  have ⟨_, hpre0⟩ := LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
  have hr : DeserializeScope x.r := by
    simp only [deserializeGenRawSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre0
    exact hpre0.1.2.2.2
  exact segStepG_then (hD.entry x R s0 hpc hrun hpre hal) fun s hs =>
    deserLoopGPlacedW_run H hD hMF hRepr hr (recFields x.r).length 0 s (Nat.zero_add _) hs

end Placed

end Proofs.libsignal.Hooks2
