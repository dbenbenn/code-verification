/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.GrowOneCodeSym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Placed.GenLsBlock -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.Defs
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.HooksX

/-!
# Hook-Stack Framing and `[LibsignalPlacement]` Stacked Allocator Bundles

Defines `Spec.withExternStackFromAlloc'`, `withLsCodeLoaded` / `withLsCl` stack-slack framing
helpers, and `AllocContractsXPlaced`.
-/

public section

set_option autoImplicit false

namespace Proofs.libsignal.Hooks2

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet

theorem L1 : True := trivial

/-- Enrich a `Spec α` that owns `stackAt s.sp allocHookStack` (`4096`) with the remaining `12288`
bytes of `externStack` (`16384`). -/
@[expose] def _root_.Arm64.Spec.withExternStackFromAlloc' {α : Type} (spec : Spec α) : Spec α where
  pre := fun x s => spec.pre x s ∗ memRegion (s.sp - 16384#64) 12288
  post := fun x s0 sf => spec.post x s0 sf ∗ memRegion (s0.sp - 16384#64) 12288
  onPanic := spec.onPanic
  onExit := spec.onExit

/-! ## Relocatable `[LibsignalPlacement]` Proofs -/

section Placed
set_option maxRecDepth 2000000

/-- Lift `subroutine_ok_map` across `withLsCodeLoaded pl`. -/
theorem subroutine_ok_withLsCodeLoaded_map' {α β : Type} {prog : Program} {entry : BitVec 64}
    {pl : Obj.MultiPlacement} {spec : Spec α} {spec' : Spec β}
    (h : subroutine_ok prog entry (withLsCodeLoaded pl spec))
    (hmap : ∀ (y : β) (R : SepProp) (s0 : State), (s0.mem ⊨ spec'.pre y s0 ∗ R) →
      ∃ (x : α) (R' : SepProp), (s0.mem ⊨ spec.pre x s0 ∗ R') ∧
        ∀ sf : State, (sf.mem ⊨ spec.post x s0 sf ∗ R') → (sf.mem ⊨ spec'.post y s0 sf ∗ R))
    (h_no_panic : ∀ x R' s0 sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s0 sf ∗ R') := by
      intro _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_no_exit : ∀ x code R' s0 sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s0 sf ∗ R') := by
      intro _ _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_no_oom : ∀ x R' s0 sf, sf.status = .OutOfMemory → ¬(sf.mem ⊨ spec.onOom x s0 sf ∗ R') := by
      intro _ _ _ _ _ ho; exact not_satisfies_false_sepConj ho) :
    subroutine_ok prog entry (withLsCodeLoaded pl spec') := by
  refine subroutine_ok_map h (fun y R s0 hpre => ?_) h_no_panic h_no_exit
    (fun x _ _ R' s0 sf hoom ho => False.elim (h_no_oom x R' s0 sf hoom ho))
  have ⟨hcl, hpre'⟩ := extract_withLsCodeLoaded hpre
  obtain ⟨x, R', hm, hpost⟩ := hmap y R s0 hpre'
  refine ⟨x, R', ?_, hpost⟩
  dsimp only [withLsCodeLoaded]
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  exact ⟨hcl, hm⟩

/-- Lift `subroutine_ok_map_panic` across `withLsCodeLoaded pl`. -/
theorem subroutine_ok_withLsCodeLoaded_map_panic' {α β : Type} {prog : Program} {entry : BitVec 64}
    {pl : Obj.MultiPlacement} {spec : Spec α} {spec' : Spec β}
    (h : subroutine_ok prog entry (withLsCodeLoaded pl spec))
    (hmap : ∀ (y : β) (R : SepProp) (s0 : State), (s0.mem ⊨ spec'.pre y s0 ∗ R) →
      ∃ (x : α) (R' : SepProp), (s0.mem ⊨ spec.pre x s0 ∗ R') ∧
        (∀ sf : State, (sf.mem ⊨ spec.post x s0 sf ∗ R') → (sf.mem ⊨ spec'.post y s0 sf ∗ R)) ∧
        (∀ sf : State, (sf.mem ⊨ spec.onPanic x s0 sf ∗ R') → (sf.mem ⊨ spec'.onPanic y s0 sf ∗ R)))
    (h_no_exit : ∀ x code R' s0 sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s0 sf ∗ R') := by
      intro _ _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_no_oom : ∀ x R' s0 sf, sf.status = .OutOfMemory → ¬(sf.mem ⊨ spec.onOom x s0 sf ∗ R') := by
      intro _ _ _ _ _ ho; exact not_satisfies_false_sepConj ho) :
    subroutine_ok prog entry (withLsCodeLoaded pl spec') := by
  refine subroutine_ok_map_panic h (fun y R s0 hpre => ?_) h_no_exit
    (fun x _ _ R' s0 sf hoom ho => False.elim (h_no_oom x R' s0 sf hoom ho))
  have ⟨hcl, hpre'⟩ := extract_withLsCodeLoaded hpre
  obtain ⟨x, R', hm, hpost, hpan⟩ := hmap y R s0 hpre'
  refine ⟨x, R', ?_, hpost, hpan⟩
  dsimp only [withLsCodeLoaded]
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  exact ⟨hcl, hm⟩

/-- Lift `subroutine_ok_map` across `withLsCl pl`. -/
theorem subroutine_ok_withLsCl_map' {α β : Type} {prog : Program} {entry : BitVec 64}
    {pl : Obj.MultiPlacement} {spec : Spec α} {spec' : Spec β}
    (h : subroutine_ok prog entry (withLsCl pl spec))
    (hmap : ∀ (y : β) (R : SepProp) (s0 : State), (s0.mem ⊨ spec'.pre y s0 ∗ R) →
      ∃ (x : α) (R' : SepProp), (s0.mem ⊨ spec.pre x s0 ∗ R') ∧
        ∀ sf : State, (sf.mem ⊨ spec.post x s0 sf ∗ R') → (sf.mem ⊨ spec'.post y s0 sf ∗ R))
    (h_no_panic : ∀ x R' s0 sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s0 sf ∗ R') := by
      intro _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_no_exit : ∀ x code R' s0 sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s0 sf ∗ R') := by
      intro _ _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_no_oom : ∀ x R' s0 sf, sf.status = .OutOfMemory → ¬(sf.mem ⊨ spec.onOom x s0 sf ∗ R') := by
      intro _ _ _ _ _ ho; exact not_satisfies_false_sepConj ho) :
    subroutine_ok prog entry (withLsCl pl spec') := by
  apply ls_subroutine_ok_cl_of_withLsCodeLoaded
  have h0 : subroutine_ok prog entry (withLsCodeLoaded pl spec) :=
    subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => by
      dsimp only [withLsCl, withLsCodeLoaded] at hq ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      exact hq.2)
  exact subroutine_ok_withLsCodeLoaded_map' h0 hmap h_no_panic h_no_exit h_no_oom

/-- Lift `subroutine_ok_map_panic` across `withLsCl pl`. -/
theorem subroutine_ok_withLsCl_map_panic' {α β : Type} {prog : Program} {entry : BitVec 64}
    {pl : Obj.MultiPlacement} {spec : Spec α} {spec' : Spec β}
    (h : subroutine_ok prog entry (withLsCl pl spec))
    (hmap : ∀ (y : β) (R : SepProp) (s0 : State), (s0.mem ⊨ spec'.pre y s0 ∗ R) →
      ∃ (x : α) (R' : SepProp), (s0.mem ⊨ spec.pre x s0 ∗ R') ∧
        (∀ sf : State, (sf.mem ⊨ spec.post x s0 sf ∗ R') → (sf.mem ⊨ spec'.post y s0 sf ∗ R)) ∧
        (∀ sf : State, (sf.mem ⊨ spec.onPanic x s0 sf ∗ R') → (sf.mem ⊨ spec'.onPanic y s0 sf ∗ R)))
    (h_no_exit : ∀ x code R' s0 sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s0 sf ∗ R') := by
      intro _ _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_no_oom : ∀ x R' s0 sf, sf.status = .OutOfMemory → ¬(sf.mem ⊨ spec.onOom x s0 sf ∗ R') := by
      intro _ _ _ _ _ ho; exact not_satisfies_false_sepConj ho) :
    subroutine_ok prog entry (withLsCl pl spec') := by
  apply ls_subroutine_ok_cl_of_withLsCodeLoaded
  have h0 : subroutine_ok prog entry (withLsCodeLoaded pl spec) :=
    subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => by
      dsimp only [withLsCl, withLsCodeLoaded] at hq ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      exact hq.2)
  exact subroutine_ok_withLsCodeLoaded_map_panic' h0 hmap h_no_exit h_no_oom

/-- Stack-slack framing for `Spec.withHookStack` under `withLsCodeLoaded pl`. -/
theorem subroutine_ok_withLsCodeLoaded_withHookStack_mono {α : Type} {prog : Program}
    {entry : BitVec 64} {pl : Obj.MultiPlacement} {spec : Spec α} {s1 s2 : Nat}
    (hle : s1 ≤ s2) (hbound : s2 ≤ 2 ^ 64)
    (h : subroutine_ok prog entry (withLsCodeLoaded pl (spec.withHookStack s1)))
    (h_no_panic : ∀ x R' s0 sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s0 sf ∗ R') := by
      intro _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_no_exit : ∀ x code R' s0 sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s0 sf ∗ R') := by
      intro _ _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_no_oom : ∀ x R' s0 sf, sf.status = .OutOfMemory → ¬(sf.mem ⊨ spec.onOom x s0 sf ∗ R') := by
      intro _ _ _ _ _ ho; exact not_satisfies_false_sepConj ho) :
    subroutine_ok prog entry (withLsCodeLoaded pl (spec.withHookStack s2)) := by
  refine subroutine_ok_withLsCodeLoaded_map' h (fun x R s0 hpre => ?_) h_no_panic h_no_exit h_no_oom
  have hsplit : s2 = s1 + (s2 - s1) := by omega
  have hstack_pre : stackAt s0.sp s2 =
      memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ stackAt s0.sp s1 := by
    have h0 := ProofLib.stackAt_split_bottom s0.sp s1 (s2 - s1) (by omega)
    rwa [← hsplit] at h0
  refine ⟨x, memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R, ?_, ?_⟩
  · change s0.mem ⊨ (spec.pre x s0 ∗ stackAt s0.sp s2) ∗ R at hpre
    rw [hstack_pre] at hpre
    change s0.mem ⊨ (spec.pre x s0 ∗ stackAt s0.sp s1) ∗ (memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R)
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
  · intro sf hpost
    change sf.mem ⊨ (spec.post x s0 sf ∗ stackAt s0.sp s1) ∗ (memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R) at hpost
    change sf.mem ⊨ (spec.post x s0 sf ∗ stackAt s0.sp s2) ∗ R
    rw [hstack_pre]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost

/-- Stack-slack framing for `Spec.withHookStack` under `withLsCl pl`. -/
theorem subroutine_ok_withLsCl_withHookStack_mono {α : Type} {prog : Program}
    {entry : BitVec 64} {pl : Obj.MultiPlacement} {spec : Spec α} {s1 s2 : Nat}
    (hle : s1 ≤ s2) (hbound : s2 ≤ 2 ^ 64)
    (h : subroutine_ok prog entry (withLsCl pl (spec.withHookStack s1)))
    (h_no_panic : ∀ x R' s0 sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s0 sf ∗ R') := by
      intro _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_no_exit : ∀ x code R' s0 sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s0 sf ∗ R') := by
      intro _ _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_no_oom : ∀ x R' s0 sf, sf.status = .OutOfMemory → ¬(sf.mem ⊨ spec.onOom x s0 sf ∗ R') := by
      intro _ _ _ _ _ ho; exact not_satisfies_false_sepConj ho) :
    subroutine_ok prog entry (withLsCl pl (spec.withHookStack s2)) := by
  refine subroutine_ok_withLsCl_map' h (fun x R s0 hpre => ?_) h_no_panic h_no_exit h_no_oom
  have hsplit : s2 = s1 + (s2 - s1) := by omega
  have hstack_pre : stackAt s0.sp s2 =
      memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ stackAt s0.sp s1 := by
    have h0 := ProofLib.stackAt_split_bottom s0.sp s1 (s2 - s1) (by omega)
    rwa [← hsplit] at h0
  refine ⟨x, memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R, ?_, ?_⟩
  · change s0.mem ⊨ (spec.pre x s0 ∗ stackAt s0.sp s2) ∗ R at hpre
    rw [hstack_pre] at hpre
    change s0.mem ⊨ (spec.pre x s0 ∗ stackAt s0.sp s1) ∗ (memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R)
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
  · intro sf hpost
    change sf.mem ⊨ (spec.post x s0 sf ∗ stackAt s0.sp s1) ∗ (memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R) at hpost
    change sf.mem ⊨ (spec.post x s0 sf ∗ stackAt s0.sp s2) ∗ R
    rw [hstack_pre]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost

/-- Frame `memRegion (s.sp - 16384#64) 12288` onto any non-panicking `subroutine_ok` (`withExternStackFromAlloc'`). -/
theorem subroutine_ok_withExternStackFromAlloc' {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} (h : subroutine_ok prog entry spec)
    (h_no_panic : ∀ x R' s0 sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s0 sf ∗ R') := by
      intro _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_no_exit : ∀ x code R' s0 sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s0 sf ∗ R') := by
      intro _ _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_no_oom : ∀ x R' s0 sf, sf.status = .OutOfMemory → ¬(sf.mem ⊨ spec.onOom x s0 sf ∗ R') := by
      intro _ _ _ _ _ ho; exact not_satisfies_false_sepConj ho) :
    subroutine_ok prog entry spec.withExternStackFromAlloc' := by
  refine subroutine_ok_map h (fun x R s0 hpre => ?_) h_no_panic h_no_exit
    (fun x _ _ R' s0 sf hoom ho => False.elim (h_no_oom x R' s0 sf hoom ho))
  refine ⟨x, memRegion (s0.sp - 16384#64) 12288 ∗ R, ?_, ?_⟩
  · dsimp only [Spec.withExternStackFromAlloc'] at hpre
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
  · intro sf hpost
    dsimp only [Spec.withExternStackFromAlloc']
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost

/-- Relocatable `[LibsignalPlacement]` stacked allocator bundle (`withExternStackFromAlloc'`). -/
structure AllocContractsXPlaced [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop where
  alloc : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ lsRustAllocSym)
      (withLsCl lsmpl (rustAllocSpec A).withExternStackFromAlloc')
  dealloc : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ lsRustDeallocSym)
      (withLsCl lsmpl (rustDeallocSpec A).withExternStackFromAlloc')
  realloc : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ lsRustReallocSym)
      (withLsCl lsmpl (rustReallocSpec A).withExternStackFromAlloc')

theorem AllocContractsXPlaced.of_block0 [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {blk0Prog : Program} [IsLsBlockProg blk0Prog 0 H]
    (halloc : subroutine_ok blk0Prog (lsρ lsRustAllocSym)
      (withLsCodeLoaded lsmpl (rustAllocSpec A).withExternStackFromAlloc'))
    (hdealloc : subroutine_ok blk0Prog (lsρ lsRustDeallocSym)
      (withLsCodeLoaded lsmpl (rustDeallocSpec A).withExternStackFromAlloc'))
    (hrealloc : subroutine_ok blk0Prog (lsρ lsRustReallocSym)
      (withLsCodeLoaded lsmpl (rustReallocSpec A).withExternStackFromAlloc')) :
    AllocContractsXPlaced A H where
  alloc := ls_subroutine_ok_cl_of_callee (j := 0) halloc
  dealloc := ls_subroutine_ok_cl_of_callee (j := 0) hdealloc
  realloc := ls_subroutine_ok_cl_of_callee (j := 0) hrealloc

theorem AllocContractsXPlaced.of_hooks [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A)) :
    AllocContractsXPlaced A H where
  alloc := ls_subroutine_ok_cl_of_plain_prog
    (subroutine_ok_withExternStackFromAlloc' (ls_hook_ok_of_caller halloc))
  dealloc := ls_subroutine_ok_cl_of_plain_prog
    (subroutine_ok_withExternStackFromAlloc' (ls_hook_ok_of_caller hdealloc))
  realloc := ls_subroutine_ok_cl_of_plain_prog
    (subroutine_ok_withExternStackFromAlloc' (ls_hook_ok_of_caller hrealloc))

end Placed

end Proofs.libsignal.Hooks2
