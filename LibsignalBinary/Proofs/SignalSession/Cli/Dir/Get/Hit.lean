/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.Pure -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# Shared Epilogues, Panic Exit, and Cache-Hit Exit for `<signal_session::stores::Dir>::get`
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Get.Helpers

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SpqrV1.Alloc
open DoReserveNorm

/-- Callee-saved state not saved on `Dir::get`'s frame (`x25..x28` and `v8..v15`). -/
@[expose] def HighCalleeSaved (s0 s : State) : Prop :=
  s.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5) ∧
  s.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) ∧
  s.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) ∧
  s.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5) ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

theorem HighCalleeSaved.refl (s0 : State) : HighCalleeSaved s0 s0 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem HighCalleeSaved.of_calleeSaved {s0 s sf : State}
    (h0 : HighCalleeSaved s0 s) (hcs : CalleeSavedPreserved s sf) :
    HighCalleeSaved s0 sf := by
  obtain ⟨_, _, _, _, _, _, c25, c26, c27, c28, _, cv⟩ := hcs
  exact ⟨c25.trans h0.1, c26.trans h0.2.1, c27.trans h0.2.2.1,
         c28.trans h0.2.2.2.1, cv.trans h0.2.2.2.2⟩

theorem HighCalleeSaved.of_steps {s0 s s' : State}
    (h0 : HighCalleeSaved s0 s)
    (h25 : s'.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5))
    (h26 : s'.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5))
    (h27 : s'.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5))
    (h28 : s'.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5))
    (hv : calleeSavedVRegs s' = calleeSavedVRegs s) :
    HighCalleeSaved s0 s' :=
  ⟨h25.trans h0.1, h26.trans h0.2.1, h27.trans h0.2.2.1,
   h28.trans h0.2.2.2.1, hv.trans h0.2.2.2.2⟩

theorem HighCalleeSaved.of_step_call {s0 s s_pre sf : State}
    (h0 : HighCalleeSaved s0 s)
    (hcs : CalleeSavedPreserved s_pre sf)
    (h25 : s_pre.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5))
    (h26 : s_pre.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5))
    (h27 : s_pre.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5))
    (h28 : s_pre.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5))
    (hv : calleeSavedVRegs s_pre = calleeSavedVRegs s) :
    HighCalleeSaved s0 sf :=
  (h0.of_steps h25 h26 h27 h28 hv).of_calleeSaved hcs

theorem spAligned_of_sp_eq {s sf : State} (h : s.spAligned = true) (hsp : sf.sp = s.sp) :
    sf.spAligned = true := by
  simpa only [State.spAligned, hsp] using h

structure FrozenEq {α : Type _} (a b : α) : Prop where
  eq : a = b

theorem sepWPp_weaken_pre {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : P ⊢ P') (hwp : SepWPp prog ret s P' Q Qp oom) :
    SepWPp prog ret s P Q Qp oom :=
  fun R hm hL => hwp R (Satisfies.mono (sepConj_mono_left h) hm) hL

theorem sepWPp_exists_left {α : Type _} {prog : Program} {ret : BitVec 64} {s : State}
    {P : α → SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ a, SepWPp prog ret s (P a) Q Qp oom) :
    SepWPp prog ret s (∃∗ a, P a) Q Qp oom := by
  intro R hm hL
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨a, hm⟩
  exact h a R hm hL

theorem pure_true_sepConj (P : SepProp) : ⌜True⌝ ∗ P = P :=
  Entails.antisymm (Entails.pure_left fun _ => Entails.refl P)
    (Entails.pure_right trivial (Entails.refl P))

theorem pure_sepConj_pure_assoc (P Q : Prop) (R : SepProp) :
    ⌜P⌝ ∗ (⌜Q⌝ ∗ R) = ⌜P ∧ Q⌝ ∗ R := by
  rw [← sepConj_assoc, pure_sepConj_pure]

theorem ite_true_eq {α : Sort _} {p : Prop} [Decidable p] (h : p) (a b : α) :
    (if p then a else b) = a := by
  split <;> [rfl; exact absurd h ‹_›]

theorem ite_false_eq {α : Sort _} {p : Prop} [Decidable p] (h : ¬ p) (a b : α) :
    (if p then a else b) = b := by
  split <;> [exact absurd ‹_› h; rfl]

theorem vecBuf_dirEntry_expose (A : RustAlloc) (cap ptr : BitVec 64)
    (xs : List (List (BitVec 8) × List (BitVec 8))) :
    RustHeap.vecBuf A 48 8 (dirEntryAt A) cap ptr xs =
      ⌜xs.length ≤ cap.toNat ∧ cap.toNat * 48 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        RustHeap.arrayAt (dirEntryAt A) 48 ptr xs ∗
        (if cap = 0 then emp
         else A.live ptr (cap.toNat * 48) 8 ∗
           memRegion (ptr + BitVec.ofNat 64 (xs.length * 48)) ((cap.toNat - xs.length) * 48)) := by
  unfold RustHeap.vecBuf
  by_cases hcap : cap = 0
  · subst hcap
    by_cases hnil : xs = []
    · subst hnil
      simp only [↓reduceIte, RustHeap.arrayAt, sepConj_emp]
    · have hfalse : ¬ (xs.length ≤ (0 : BitVec 64).toNat ∧
          (0 : BitVec 64).toNat * 48 < 2 ^ 63 ∧ ptr ≠ 0) := by
        rcases List.exists_cons_of_ne_nil hnil with ⟨_, _, rfl⟩
        simp
      apply Entails.antisymm
      · exact Entails.pure_left fun h => False.elim (hfalse h)
      · exact Entails.pure_left fun h => False.elim (hfalse h)
  · simp only [hcap, ↓reduceIte]
    ac_rfl

theorem vecU8_eq_exists (A : RustAlloc) (v : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A v bs = ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, vecU8At A v cap ptr bs := rfl

theorem sepWPp_unfold_vecU8 {prog : Program} {ret : BitVec 64} {s : State}
    {A : RustAlloc} {v : BitVec 64} {bs : List (BitVec 8)} {F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ cap ptr : BitVec 64,
      bs.length ≤ cap.toNat → cap.toNat < 2 ^ 63 → ptr ≠ 0 →
      SepWPp prog ret s
        (((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (ptr ↦ₛ bs) ∗
          (if cap = 0 then emp
           else A.live ptr cap.toNat 1 ∗
             memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s (vecU8 A v bs ∗ F) Q Qp oom := by
  rw [vecU8_eq_exists]
  simp only [sepExists_sepConj_left]
  refine sepWPp_exists_left fun cap => sepWPp_exists_left fun ptr => ?_
  rw [vecU8At_expose, sepConj_assoc]
  exact SepWPp.pure_left fun ⟨h1, h2, h3⟩ => h cap ptr h1 h2 h3

theorem sepWPp_pure_mid2 {prog : Program} {ret : BitVec 64} {s : State}
    {P1 P2 P3 : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : φ → SepWPp prog ret s (P1 ∗ P2 ∗ P3) Q Qp oom) :
    SepWPp prog ret s (P1 ∗ P2 ∗ ⌜φ⌝ ∗ P3) Q Qp oom := by
  have heq : P1 ∗ P2 ∗ ⌜φ⌝ ∗ P3 = ⌜φ⌝ ∗ P1 ∗ P2 ∗ P3 := by ac_rfl
  rw [heq]
  exact SepWPp.pure_left h

theorem arrayAt_dirEntry_cons (A : RustAlloc) (ptr : BitVec 64)
    (nm bs : List (BitVec 8)) (rest : List (List (BitVec 8) × List (BitVec 8))) :
    RustHeap.arrayAt (dirEntryAt A) 48 ptr ((nm, bs) :: rest) =
      vecU8 A ptr nm ∗ vecU8 A (ptr + 24#64) bs ∗
        RustHeap.arrayAt (dirEntryAt A) 48 (ptr + 48#64) rest := by
  dsimp only [RustHeap.arrayAt, dirEntryAt]
  ac_rfl

theorem allocFailed_after_append {s0 s_pre sf : State}
    (hpfx : s0.trace <+: s_pre.trace)
    (htr : sf.trace = s_pre.trace ++ [allocFailedEvent]) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  rcases hpfx with ⟨evs0, hevs0⟩
  refine ⟨?_, ⟨evs0 ++ [allocFailedEvent], by rw [htr, ← hevs0, List.append_assoc]⟩⟩
  unfold allocFailedIn
  rw [htr, ← hevs0, List.append_assoc]
  simp

end CryptoVerification.SignalSession.Cli.Get.Helpers
