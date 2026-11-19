/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Dag7003Data

/-!
# Symbolic-SPQR Safe-Memo Combinators for Seed 7003 (`Memo7003Combinators.lean`)

Defines `SafeEntry`, `SafeMemo`, and `TermAt` over the 323-node concrete DAG in `Dag7003Data`
(parametric in `mode : Bool`, skipping `dh55Id` in M1 mode `false` and `dh44Id` in M2 mode `true`),
parametric over all `S : OpaqueSymbolSemantics`, and proves `not_memoCollisionOn_of_safeMemo`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Memo7003Combinators

open scoped DY.Libsignal.Composed
open DY (ExecTrace)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost VisEntry
   gamma' gamma assumedInjective storedStates storedSecrets
   principalTerms plaintextTerms prefixTerms MemoCollisionOn)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompI7003 (compI7003)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.TraceEvents7003
  (pt1M1Bytes pt1M2Bytes pt3M2Bytes)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Dag7003Defs
  (DagOp ai_not_pts dagPairwiseOkExcept_eq_of_ai)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Dag7003Data
  (dagSize opOf bytesOf shapeOf skipIdOf dagAllNodesOk dagPairwiseNoCollide)

def notAnyAiNodeBytes (bs : HwBytes) : Bool :=
  (List.range dagSize).all fun id => !(opOf id).isAI || !(bs == bytesOf id)

def noAiSuffix (sfx : HwBytes) : Bool :=
  (List.range dagSize).all fun id =>
    !(opOf id).isAI ||
      !(decide (sfx.length ≤ (bytesOf id).length) &&
        ((bytesOf id).drop ((bytesOf id).length - sfx.length) == sfx))

def noStrictAiSuffix (sfx : HwBytes) : Bool :=
  (List.range dagSize).all fun id =>
    !(opOf id).isAI ||
      !(decide (sfx.length < (bytesOf id).length) &&
        ((bytesOf id).drop ((bytesOf id).length - sfx.length) == sfx))

theorem notAnyAiNodeBytes_ne {bs : HwBytes} (h : notAnyAiNodeBytes bs = true)
    {id : Nat} (hid : id < dagSize) (hai : (opOf id).isAI = true) :
    bs ≠ bytesOf id := by
  have hall := List.all_eq_true.mp h id (List.mem_range.mpr hid)
  simp only [hai, Bool.not_true, Bool.false_or, Bool.not_eq_true', beq_eq_false_iff_ne] at hall
  exact hall

theorem notAnyAiNodeBytes_of_noAiSuffix {sfx bs : HwBytes}
    (h : noAiSuffix sfx = true) (hsfx : sfx <:+ bs) :
    notAnyAiNodeBytes bs = true := by
  rw [notAnyAiNodeBytes, List.all_eq_true]
  intro id hid
  have hall := List.all_eq_true.mp h id hid
  cases hai : (opOf id).isAI
  · simp
  · simp only [hai, Bool.not_true, Bool.false_or, Bool.not_eq_true'] at hall ⊢
    rw [beq_eq_false_iff_ne]
    rintro rfl
    obtain ⟨l, heq⟩ := hsfx
    have hle : sfx.length ≤ (bytesOf id).length := by rw [← heq]; simp
    have hdrop : (bytesOf id).drop ((bytesOf id).length - sfx.length) = sfx := by
      rw [← heq, show (l ++ sfx).length - sfx.length = l.length by simp, List.drop_left]
    simp [hle, hdrop] at hall

theorem notAnyAiNodeBytes_of_noStrictAiSuffix {sfx bs : HwBytes}
    (h : noStrictAiSuffix sfx = true) (hlt : sfx.length < bs.length) (hsfx : sfx <:+ bs) :
    notAnyAiNodeBytes bs = true := by
  rw [notAnyAiNodeBytes, List.all_eq_true]
  intro id hid
  have hall := List.all_eq_true.mp h id hid
  cases hai : (opOf id).isAI
  · simp
  · simp only [hai, Bool.not_true, Bool.false_or, Bool.not_eq_true'] at hall ⊢
    rw [beq_eq_false_iff_ne]
    rintro rfl
    obtain ⟨l, heq⟩ := hsfx
    have hdrop : (bytesOf id).drop ((bytesOf id).length - sfx.length) = sfx := by
      rw [← heq, show (l ++ sfx).length - sfx.length = l.length by simp, List.drop_left]
    simp [hlt, hdrop] at hall

def IsPt7003Bytes (bs : HwBytes) : Prop :=
  bs = pt1M1Bytes ∨ bs = pt1M2Bytes ∨ bs = pt3M2Bytes

def SafeEntry (mode : Bool) (pts : List DY.Bytes) (x : DY.Bytes × DY.Bytes × HwBytes) : Prop :=
  (x.1 ∈ pts ∧ IsPt7003Bytes x.2.2) ∨
  (assumedInjective x.1 = false ∧ notAnyAiNodeBytes x.2.2 = true) ∨
  (∃ id < dagSize, id ≠ skipIdOf mode ∧ x.2.1 = shapeOf id ∧ x.2.2 = bytesOf id ∧
    (assumedInjective x.1 = true → (opOf id).isAI = true))

def SafeMemo (mode : Bool) (S : OpaqueSymbolSemantics) (g : Ghost) (pts : List DY.Bytes)
    (t : DY.Bytes) : Prop :=
  ∀ x ∈ (gamma' compI7003 S g t).memo, SafeEntry mode pts x

def TermAt (mode : Bool) (S : OpaqueSymbolSemantics) (g : Ghost) (pts : List DY.Bytes)
    (t : DY.Bytes) (id : Nat) : Prop :=
  id < dagSize ∧ id ≠ skipIdOf mode ∧
  (gamma' compI7003 S g t).bytes = bytesOf id ∧
  (gamma' compI7003 S g t).shape = shapeOf id ∧
  SafeMemo mode S g pts t

theorem safeMemo_of_termAt {mode : Bool} {S : OpaqueSymbolSemantics} {g : Ghost}
    {pts : List DY.Bytes} {t : DY.Bytes} {id : Nat}
    (h : TermAt mode S g pts t id) : SafeMemo mode S g pts t :=
  h.2.2.2.2

theorem gamma_of_termAt {mode : Bool} {S : OpaqueSymbolSemantics} {g : Ghost}
    {pts : List DY.Bytes} {t : DY.Bytes} {id : Nat}
    (h : TermAt mode S g pts t id) :
    gamma compI7003 S g t = bytesOf id :=
  h.2.2.1

theorem termAt_congr {mode : Bool} {S : OpaqueSymbolSemantics} {g : Ghost}
    {pts : List DY.Bytes} {t₁ t₂ : DY.Bytes} {id : Nat}
    (heq : t₁ = t₂) (h : TermAt mode S g pts t₂ id) :
    TermAt mode S g pts t₁ id :=
  heq ▸ h

private theorem ai_ne_of_isPt7003 {id : Nat} (hid : id < dagSize) (hai : (opOf id).isAI = true)
    {bs : HwBytes} (hpt : IsPt7003Bytes bs) : bytesOf id ≠ bs := by
  have ⟨h1, h2, h3⟩ := ai_not_pts dagAllNodesOk hid hai
  rcases hpt with rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3

private theorem safeEntry_pair_no_collision {mode : Bool} {pts : List DY.Bytes}
    {known : DY.Bytes → Prop} {x₁ x₂ : DY.Bytes × DY.Bytes × HwBytes}
    (hs₁ : SafeEntry mode pts x₁) (hs₂ : SafeEntry mode pts x₂)
    (hsh : x₁.2.1 ≠ x₂.2.1)
    (hinj : assumedInjective x₁.1 = true ∨ assumedInjective x₂.1 = true)
    (hpt₁ : x₁.1 ∈ pts → x₂.1 ∉ pts ∧ assumedInjective x₂.1 = true ∧ ¬ known x₂.1)
    (hpt₂ : x₂.1 ∈ pts → x₁.1 ∉ pts ∧ assumedInjective x₁.1 = true ∧ ¬ known x₁.1)
    (hbytes : x₁.2.2 = x₂.2.2) : False := by
  rcases hs₁ with ⟨hm₁, hb₁⟩ | ⟨hn₁, hsfx₁⟩ | ⟨id₁, hid₁, hsk₁, hsh₁, hb₁, hai₁⟩
  · rcases hs₂ with ⟨hm₂, _⟩ | ⟨hn₂, _⟩ | ⟨id₂, hid₂, _, _, hb₂, hai₂⟩
    · exact (hpt₁ hm₁).1 hm₂
    · have ha₂ := (hpt₁ hm₁).2.1; rw [hn₂] at ha₂; cases ha₂
    · exact ai_ne_of_isPt7003 hid₂ (hai₂ (hpt₁ hm₁).2.1) hb₁ (hb₂.symm.trans hbytes.symm)
  · have ha₂ : assumedInjective x₂.1 = true := by
      rcases hinj with h1 | h2
      · rw [hn₁] at h1; cases h1
      · exact h2
    rcases hs₂ with ⟨hm₂, _⟩ | ⟨hn₂, _⟩ | ⟨id₂, hid₂, _, _, hb₂, hai₂⟩
    · have ha₁ := (hpt₂ hm₂).2.1; rw [hn₁] at ha₁; cases ha₁
    · rw [hn₂] at ha₂; cases ha₂
    · exact notAnyAiNodeBytes_ne hsfx₁ hid₂ (hai₂ ha₂) (hbytes.trans hb₂)
  · rcases hs₂ with ⟨hm₂, hb₂⟩ | ⟨hn₂, hsfx₂⟩ | ⟨id₂, hid₂, hsk₂, hsh₂, hb₂, hai₂⟩
    · exact ai_ne_of_isPt7003 hid₁ (hai₁ (hpt₂ hm₂).2.1) hb₂ (hb₁.symm.trans hbytes)
    · have ha₁ : assumedInjective x₁.1 = true := by
        rcases hinj with h1 | h2
        · exact h1
        · rw [hn₂] at h2; cases h2
      exact notAnyAiNodeBytes_ne hsfx₂ hid₁ (hai₁ ha₁) (hbytes.symm.trans hb₁)
    · have hai_or : (opOf id₁).isAI = true ∨ (opOf id₂).isAI = true := by
        rcases hinj with h1 | h2
        · exact Or.inl (hai₁ h1)
        · exact Or.inr (hai₂ h2)
      have hid_eq := dagPairwiseOkExcept_eq_of_ai (dagPairwiseNoCollide mode)
        hid₁ hsk₁ hid₂ hsk₂ hai_or (hb₁.symm.trans (hbytes.trans hb₂))
      exact hsh (hsh₁.trans (hid_eq ▸ hsh₂.symm))

theorem not_memoCollisionOn_of_safeMemo
    {mode : Bool} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {known : DY.Bytes → Prop} {tr : ExecTrace} {vis : List VisEntry}
    {pts newTerms : List DY.Bytes}
    (hpts : plaintextTerms vis = pts)
    (hsend : ∀ t ∈ (vis.filter (·.kind == .send)).flatMap (·.terms), SafeMemo mode S g pts t)
    (hsts : ∀ ls ∈ storedStates r tr, SafeMemo mode S g pts (DY.Comparse.serialize ls))
    (hsec : ∀ t ∈ storedSecrets tr, SafeMemo mode S g pts t)
    (hpt_safe : ∀ t ∈ pts, SafeMemo mode S g pts t)
    (hnew : ∀ t ∈ newTerms, SafeMemo mode S g pts t) :
    ¬ MemoCollisionOn compI7003 r S g known tr vis newTerms [] := by
  rintro ⟨x₁, hx₁_raw, x₂, hx₂_raw, hsh, hinj, hpt₁, hpt₂, hbytes⟩
  rw [hpts, List.append_nil] at hpt₁ hpt₂
  obtain ⟨t₁, ht₁, hmx₁⟩ := List.mem_flatMap.mp hx₁_raw
  have hs₁ : SafeEntry mode pts x₁ := hnew t₁ ht₁ x₁ hmx₁
  have hs₂ : SafeEntry mode pts x₂ := by
    rcases List.mem_append.mp hx₂_raw with hx₂_pref | hx₂_new
    · obtain ⟨t₂, ht₂, hmx₂⟩ := List.mem_flatMap.mp hx₂_pref
      dsimp only [prefixTerms, principalTerms] at ht₂
      rw [hpts] at ht₂
      simp only [List.mem_append, List.mem_map] at ht₂
      rcases ht₂ with ((hsnd | ⟨ls, hls, rfl⟩) | hsc) | hpt
      · exact hsend t₂ hsnd x₂ hmx₂
      · exact hsts ls hls x₂ hmx₂
      · exact hsec t₂ hsc x₂ hmx₂
      · exact hpt_safe t₂ hpt x₂ hmx₂
    · obtain ⟨t₂, ht₂, hmx₂⟩ := List.mem_flatMap.mp hx₂_new
      exact hnew t₂ ht₂ x₂ hmx₂
  exact safeEntry_pair_no_collision hs₁ hs₂ hsh hinj hpt₁ hpt₂ hbytes

end Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Memo7003Combinators
