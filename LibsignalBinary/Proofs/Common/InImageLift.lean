/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.Stack

/-!
# Hook-Free `subroutine_ok` Framing and Stack-Split Combinators

Provides general combinators for framing `subroutine_ok` contracts across larger stack budgets
without re-stepping instructions:
- `subroutine_ok_frame_entails`: frame an arbitrary assertion `Frame x s0` across normal return,
  panic, exit, and OOM outcomes.
- `subroutine_ok_of_stack_split`: lift hook-free contracts from `stackAt s0.sp s1` to
  `stackAt s0.sp s2` (`s1 ≤ s2 ≤ 2 ^ 64`) via `stackAt_eq_top_sep_bottom`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.InImageLift

open Arm64 ProofLib SepProp

/-- Frame an extra assertion `Frame x s0` across `subroutine_ok P addr specSmall` to establish
`subroutine_ok P addr specBig` (handling normal return, panic, exit, and OOM uniformly). -/
theorem subroutine_ok_frame_entails {α : Type} {P : Program} {addr : BitVec 64}
    {specSmall specBig : Spec α} (Frame : α → State → SepProp)
    (h : subroutine_ok P addr specSmall)
    (hpre : ∀ x s0, specBig.pre x s0 ⊢ specSmall.pre x s0 ∗ Frame x s0)
    (hpost : ∀ x s0 sf, specSmall.post x s0 sf ∗ Frame x s0 ⊢ specBig.post x s0 sf)
    (hpan : ∀ x s0 sf, specSmall.onPanic x s0 sf ∗ Frame x s0 ⊢ specBig.onPanic x s0 sf := by
      intro _ _ _; exact Entails.trans (Entails.of_eq (by simp [sepConj])) (by exact fun _ hm => False.elim (not_satisfies_false_sepConj hm)))
    (hex : ∀ x code s0 sf, specSmall.onExit x code s0 sf ∗ Frame x s0 ⊢ specBig.onExit x code s0 sf := by
      intro _ _ _ _; exact fun _ hm => False.elim (not_satisfies_false_sepConj hm))
    (hoom : ∀ x s0 sf, specSmall.onOom x s0 sf ∗ Frame x s0 ⊢ specBig.onOom x s0 sf := by
      intro _ _ _; exact fun _ hm => False.elim (not_satisfies_false_sepConj hm)) :
    subroutine_ok P addr specBig := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hm hal => ?_
  have hm' : s0.mem ⊨ specSmall.pre x s0 ∗ (Frame x s0 ∗ R) := by
    rw [← sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left (hpre x s0)) hm
  refine h.mono_outcome x (Frame x s0 ∗ R) s0 hpc hrun hm' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hp⟩ | ⟨hp_st, hp⟩ | ⟨code, hex_st, hp⟩ | ⟨ho_st, hp⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    rw [← sepConj_assoc] at hp
    exact Satisfies.mono (sepConj_mono_left (hpost x s0 sf)) hp
  · refine Or.inr (Or.inl ⟨hp_st, ?_⟩)
    rw [← sepConj_assoc] at hp
    exact Satisfies.mono (sepConj_mono_left (hpan x s0 sf)) hp
  · refine Or.inr (Or.inr (Or.inl ⟨code, hex_st, ?_⟩))
    rw [← sepConj_assoc] at hp
    exact Satisfies.mono (sepConj_mono_left (hex x code s0 sf)) hp
  · refine Or.inr (Or.inr (Or.inr ⟨ho_st, ?_⟩))
    rw [← sepConj_assoc] at hp
    exact Satisfies.mono (sepConj_mono_left (hoom x s0 sf)) hp

/-- Split `stackAt sp s2` (`s1 ≤ s2 ≤ 2 ^ 64`) into `stackAt sp s1 ∗ memRegion (sp - s2) (s2 - s1)`
for convenient framing of hook-free `subroutine_ok` proofs from `4096 + frame` to `16384 + frame`. -/
theorem stackAt_eq_top_sep_bottom (sp : BitVec 64) {s1 s2 : Nat}
    (hle : s1 ≤ s2 := by decide) (hbound : s2 ≤ 2 ^ 64 := by decide) :
    stackAt sp s2 = stackAt sp s1 ∗ memRegion (sp - BitVec.ofNat 64 s2) (s2 - s1) := by
  have hsplit : s2 = s1 + (s2 - s1) := by omega
  have h0 := ProofLib.stackAt_split_bottom sp s1 (s2 - s1) (by omega)
  rw [← hsplit] at h0
  exact h0.trans (by ac_rfl)

/-- Lift a hook-free `subroutine_ok` contract from stack footprint `s1` to `s2` (`s1 ≤ s2 ≤ 2 ^ 64`)
by framing the bottom `s2 - s1` stack bytes. -/
theorem subroutine_ok_of_stack_split {α : Type} {P : Program} {addr : BitVec 64}
    {specSmall specBig : Spec α} (s1 s2 : Nat)
    (h : subroutine_ok P addr specSmall)
    (hpre : ∀ x s0, specBig.pre x s0 ⊢
      specSmall.pre x s0 ∗ memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1))
    (hpost : ∀ x s0 sf,
      specSmall.post x s0 sf ∗ memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ⊢
        specBig.post x s0 sf)
    (hpan : ∀ x s0 sf,
      specSmall.onPanic x s0 sf ∗ memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ⊢
        specBig.onPanic x s0 sf := by
      intro _ _ _; exact fun _ hm => False.elim (not_satisfies_false_sepConj hm))
    (hex : ∀ x code s0 sf,
      specSmall.onExit x code s0 sf ∗ memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ⊢
        specBig.onExit x code s0 sf := by
      intro _ _ _ _; exact fun _ hm => False.elim (not_satisfies_false_sepConj hm))
    (hoom : ∀ x s0 sf,
      specSmall.onOom x s0 sf ∗ memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ⊢
        specBig.onOom x s0 sf := by
      intro _ _ _; exact fun _ hm => False.elim (not_satisfies_false_sepConj hm)) :
    subroutine_ok P addr specBig :=
  subroutine_ok_frame_entails
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1))
    h hpre hpost hpan hex hoom

end CryptoVerification.InImageLift
