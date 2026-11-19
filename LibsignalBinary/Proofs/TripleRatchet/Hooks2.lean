/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.Defs
public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import ProofLib
public import LibsignalBinary.Proofs.TripleRatchet.TrapRng -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.Defs
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import ProofLib.SepLogic.WP.Structural

set_option warningAsError false

/-!
# Generic Extern-Hook Program and Contract Bundles

Defines the generic rebased program `tripleRatchetProgAtExt b ext` and the subroutine contract
bundles `AllocContracts`, `Stage2Contracts`, `AllocContractsX`, and `Stage2ContractsX`, together
with stack-lifting helpers and concrete instantiations from `AllocHooks` and `TripleRatchetHooks`.
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

/-! ## Generic rebased program and entry helpers -/

/-- Rebased placeholder program at `b` with arbitrary extern hooks `ext` (wrapped in `Rust.withPanics`). -/
abbrev tripleRatchetProgAtExt (b : BitVec 64) (ext : String → Option (State → State)) : Program :=
  (default : Program).rebase b (Rust.withPanics ext)

theorem tripleRatchetProgAt_eq_tripleRatchetProgAtExt_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) :
    trTrapProgAt b C abs = tripleRatchetProgAtExt b (trTrapExterns C abs) :=
  rfl

theorem tripleRatchetProgAt_eq_tripleRatchetProgAtExt (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    tripleRatchetProgAt b C ctl abs = tripleRatchetProgAtExt b (tripleRatchetExterns C ctl abs) :=
  rfl

/-! ## `AllocContracts` bundle -/

/-- `subroutine_ok` contracts on `tripleRatchetProgAtExt b ext` for the Rust allocator (`alloc`, `dealloc`, `realloc`),
the no-alloc shim (`shim`), and `memcpy` / `memmove` / `memset`. -/
structure AllocContracts (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop where
  alloc : subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr allocName) (rustAllocSpec A)
  dealloc : subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr deallocName) (rustDeallocSpec A)
  realloc : subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr reallocName) (rustReallocSpec A)
  shim : subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr shimName) sessionShimSpec
  memcpy : ∀ (hookStack : Nat),
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) (libcMemcpySpec hookStack)
  session_memcpy : ∀ (hookStack : Nat),
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) (sessionMemcpySpec hookStack)
  memcpy_region :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) memcpyRegionSpec
  session_memcpy_region :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec
  memmove : ∀ (hookStack : Nat),
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr memmoveName) (libcMemmoveSpec hookStack)
  session_memmove : ∀ (hookStack : Nat),
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr memmoveName) (sessionMemmoveSpec hookStack)
  memset : ∀ (hookStack : Nat), 0 < hookStack →
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr memsetName) (libcMemsetSpec hookStack)
  session_memset : ∀ (hookStack : Nat), 0 < hookStack →
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr memsetName) (sessionMemsetSpec hookStack)
  memset_region :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr memsetName) memsetRegionSpec
  session_memset_region :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr memsetName) sessionMemsetRegionSpec


/-! ## Configurable-stack contract bundles -/

/-- Augment a `Spec α` with `stackAt s.sp hookStack` in `pre` and `stackAt s0.sp hookStack` in `post`. -/
@[expose] def withStack {α : Type} (spec : Spec α) (hookStack : Nat := extHookStack) : Spec α :=
  { spec with
    pre := fun x s => spec.pre x s ∗ stackAt s.sp hookStack
    post := fun x s0 sf => spec.post x s0 sf ∗ stackAt s0.sp hookStack }

theorem subroutine_ok_withStack_of_subroutine_ok {α : Type} {P : Program} {addr : BitVec 64}
    {spec : Spec α} (h : subroutine_ok P addr spec) (hookStack : Nat)
    (hpan : ∀ x s0 sf, spec.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hex : ∀ x code s0 sf, spec.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    subroutine_ok P addr (withStack spec hookStack) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  dsimp only [withStack] at hpre
  rw [sepConj_assoc] at hpre
  refine h.mono_outcome x (stackAt s0.sp hookStack ∗ R) s0 hpc hrun hpre hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan_sat⟩ | ⟨code, _, hex_sat⟩ | ⟨_, hoom_sat⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStack]
    rwa [sepConj_assoc]
  · rw [hpan x s0 sf, satisfies_pure_sepConj] at hpan_sat
    exact False.elim hpan_sat.1
  · rw [hex x code s0 sf, satisfies_pure_sepConj] at hex_sat
    exact False.elim hex_sat.1
  · rw [hoom x s0 sf, satisfies_pure_sepConj] at hoom_sat
    exact False.elim hoom_sat.1

/-- `rustAllocSpec A` with configurable stack budget `hookStack` (`= rustAllocSpec A` at `allocHookStack`). -/
@[expose] def rustAllocSpecWithStack (A : RustAlloc) (hookStack : Nat := extHookStack) : Spec (Nat × Nat) where
  pre := fun (size, align) s =>
    ⌜(s.readReg64 .x0).toNat = size ∧ (s.readReg64 .x1).toNat = align ∧ LayoutOk size align⌝ ∗
      A.pool ∗ stackAt s.sp hookStack
  post := fun (size, align) s0 sf =>
    A.pool ∗ stackAt s0.sp hookStack ∗
      (if sf.readReg64 .x0 = 0 then ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝
       else ⌜(sf.readReg64 .x0).toNat % align = 0 ∧ sf.trace = s0.trace⌝ ∗
         A.live (sf.readReg64 .x0) size align ∗ memRegion (sf.readReg64 .x0) size)

/-- `rustDeallocSpec A` with configurable stack budget `hookStack` (`= rustDeallocSpec A` at `allocHookStack`). -/
@[expose] def rustDeallocSpecWithStack (A : RustAlloc)
    (hookStack : Nat := extHookStack) : Spec (BitVec 64 × Nat × Nat) where
  pre := fun (p, size, align) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = size ∧ (s.readReg64 .x2).toNat = align⌝ ∗
      A.pool ∗ A.live p size align ∗ memRegion p size ∗ stackAt s.sp hookStack
  post := fun _ s0 sf => ⌜sf.trace = s0.trace⌝ ∗ A.pool ∗ stackAt s0.sp hookStack

/-- `rustDeallocSpec A` with `LayoutOk size align` in `pre` and configurable stack budget `hookStack`,
matching `Externs.deallocSpec` at both `A_layout` and `A₀`. -/
@[expose] def rustDeallocExternSpecWithStack (A : RustAlloc)
    (hookStack : Nat := extHookStack) : Spec (BitVec 64 × Nat × Nat) where
  pre := fun (p, size, align) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = size ∧ (s.readReg64 .x2).toNat = align ∧
      LayoutOk size align⌝ ∗
      A.pool ∗ A.live p size align ∗ memRegion p size ∗ stackAt s.sp hookStack
  post := fun _ s0 sf => ⌜sf.trace = s0.trace⌝ ∗ A.pool ∗ stackAt s0.sp hookStack

/-- `rustReallocSpec A` with configurable stack budget `hookStack` (`= rustReallocSpec A` at `allocHookStack`). -/
@[expose] def rustReallocSpecWithStack (A : RustAlloc)
    (hookStack : Nat := extHookStack) :
    Spec (BitVec 64 × Nat × Nat × Nat × List (BitVec 8)) where
  pre := fun (p, old, align, new, bs) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = old ∧ (s.readReg64 .x2).toNat = align ∧
      (s.readReg64 .x3).toNat = new ∧ LayoutOk new align ∧ bs.length ≤ old ∧ bs.length ≤ new⌝ ∗
      A.pool ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
      memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗ stackAt s.sp hookStack
  post := fun (p, old, align, new, bs) s0 sf =>
    A.pool ∗ stackAt s0.sp hookStack ∗
      (if sf.readReg64 .x0 = 0 then
        ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
          A.live p old align ∗ (p ↦ₛ bs) ∗
          memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length)
       else
        ⌜(sf.readReg64 .x0).toNat % align = 0 ∧ sf.trace = s0.trace⌝ ∗
          A.live (sf.readReg64 .x0) new align ∗ (sf.readReg64 .x0 ↦ₛ bs) ∗
          memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 bs.length) (new - bs.length))

/-- `rustReallocSpec A` with `LayoutOk old align` in `pre` and configurable stack budget `hookStack`,
matching `Externs.reallocSpec` at both `A_layout` and `A₀`. -/
@[expose] def rustReallocExternSpecWithStack (A : RustAlloc)
    (hookStack : Nat := extHookStack) :
    Spec (BitVec 64 × Nat × Nat × Nat × List (BitVec 8)) where
  pre := fun (p, old, align, new, bs) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = old ∧ (s.readReg64 .x2).toNat = align ∧
      (s.readReg64 .x3).toNat = new ∧ LayoutOk old align ∧ LayoutOk new align ∧
      bs.length ≤ old ∧ bs.length ≤ new⌝ ∗
      A.pool ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
      memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗ stackAt s.sp hookStack
  post := (rustReallocSpecWithStack A hookStack).post

theorem rustAllocSpecWithStack_eq_rustAllocSpec (A : RustAlloc) :
    rustAllocSpecWithStack A allocHookStack = rustAllocSpec A := rfl

theorem rustDeallocSpecWithStack_eq_rustDeallocSpec (A : RustAlloc) :
    rustDeallocSpecWithStack A allocHookStack = rustDeallocSpec A := rfl

theorem rustReallocSpecWithStack_eq_rustReallocSpec (A : RustAlloc) :
    rustReallocSpecWithStack A allocHookStack = rustReallocSpec A := rfl

theorem rustAllocWithStack_of_rustAlloc {P : Program} {addr : BitVec 64} {A : RustAlloc}
    {hookStack : Nat} (h : subroutine_ok P addr (rustAllocSpec A))
    (hle : allocHookStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addr (rustAllocSpecWithStack A hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨size, align⟩ R s0 hpc hrun hpre hal => ?_
  have hsplit : stackAt s0.sp hookStack =
      memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - allocHookStack) ∗
        stackAt s0.sp allocHookStack := by
    have h1 := stackAt_split_bottom s0.sp allocHookStack (hookStack - allocHookStack) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - allocHookStack) ∗ R
  have hpre' : s0.mem ⊨ (rustAllocSpec A).pre (size, align) s0 ∗ R' := by
    dsimp only [rustAllocSpecWithStack, rustAllocSpec, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  refine h.mono_outcome (size, align) R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [rustAllocSpecWithStack, rustAllocSpec, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · dsimp only [rustAllocSpec] at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact False.elim hpan.1
  · dsimp only [rustAllocSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [rustAllocSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

theorem rustDeallocExternWithStack_of_rustDealloc {P : Program} {addr : BitVec 64} {A : RustAlloc}
    {hookStack : Nat} (h : subroutine_ok P addr (rustDeallocSpec A))
    (hle : allocHookStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addr (rustDeallocExternSpecWithStack A hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨p, size, align⟩ R s0 hpc hrun hpre hal => ?_
  have hsplit : stackAt s0.sp hookStack =
      memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - allocHookStack) ∗
        stackAt s0.sp allocHookStack := by
    have h1 := stackAt_split_bottom s0.sp allocHookStack (hookStack - allocHookStack) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - allocHookStack) ∗ R
  have hpre' : s0.mem ⊨ (rustDeallocSpec A).pre (p, size, align) s0 ∗ R' := by
    dsimp only [rustDeallocExternSpecWithStack, rustDeallocSpec, R'] at hpre ⊢
    rw [hsplit] at hpre
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨hpure, hmem⟩
    refine ⟨⟨hpure.1, hpure.2.1, hpure.2.2.1⟩, ?_⟩
    ac_nf at hmem ⊢
  refine h.mono_outcome (p, size, align) R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [rustDeallocExternSpecWithStack, rustDeallocSpec, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · dsimp only [rustDeallocSpec] at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact False.elim hpan.1
  · dsimp only [rustDeallocSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [rustDeallocSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

theorem rustReallocExternWithStack_of_rustRealloc {P : Program} {addr : BitVec 64} {A : RustAlloc}
    {hookStack : Nat} (h : subroutine_ok P addr (rustReallocSpec A))
    (hle : allocHookStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addr (rustReallocExternSpecWithStack A hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨p, old, align, new, bs⟩ R s0 hpc hrun hpre hal => ?_
  have hsplit : stackAt s0.sp hookStack =
      memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - allocHookStack) ∗
        stackAt s0.sp allocHookStack := by
    have h1 := stackAt_split_bottom s0.sp allocHookStack (hookStack - allocHookStack) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - allocHookStack) ∗ R
  have hpre' : s0.mem ⊨ (rustReallocSpec A).pre (p, old, align, new, bs) s0 ∗ R' := by
    dsimp only [rustReallocExternSpecWithStack, rustReallocSpec, R'] at hpre ⊢
    rw [hsplit] at hpre
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨hpure, hmem⟩
    refine ⟨⟨hpure.1, hpure.2.1, hpure.2.2.1, hpure.2.2.2.1,
      hpure.2.2.2.2.2.1, hpure.2.2.2.2.2.2⟩, ?_⟩
    ac_nf at hmem ⊢
  refine h.mono_outcome (p, old, align, new, bs) R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [rustReallocExternSpecWithStack, rustReallocSpecWithStack, rustReallocSpec, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · dsimp only [rustReallocSpec] at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact False.elim hpan.1
  · dsimp only [rustReallocSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [rustReallocSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

/-- `decodeErrorFromSpec A` with configurable stack budget `hookStack` (`= decodeErrorFromSpec A` at `decodeErrorHookStack`). -/
@[expose] def decodeErrorFromSpecWithStack (A : RustAlloc)
    (hookStack : Nat := extHookStack) : Spec (BitVec 64 × BitVec 64) where
  pre := fun (k, w) s =>
    ⌜s.readReg64 .x0 = k ∧ KindNoHeap w⌝ ∗ (k ↦₆₄ w) ∗ memRegion (k + 8#64) 40 ∗
      A.pool ∗ stackAt s.sp hookStack
  post := fun (k, _) s0 sf =>
    ⌜sf.readReg64 .x0 ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
      decodeErrorAtStackLen A (sf.readReg64 .x0) 0 ∗
      memRegion k 48 ∗ A.pool ∗ stackAt s0.sp hookStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- `decodeErrorPushSpec A` with configurable stack budget `hookStack` (`= decodeErrorPushSpec A` at `decodeErrorHookStack`). -/
@[expose] def decodeErrorPushSpecWithStack (A : RustAlloc)
    (hookStack : Nat := extHookStack) : Spec (BitVec 64 × BitVec 64 × Nat) where
  pre := fun (d, e, n) s =>
    ⌜s.readReg64 .x0 = d ∧ n < 2 ^ 32⌝ ∗ (d ↦₆₄ e) ∗
      decodeErrorAtStackLen A e n ∗
      A.pool ∗ stackAt s.sp hookStack
  post := fun (d, e, n) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (d ↦₆₄ e) ∗
      decodeErrorAtStackLen A e (n + 1) ∗
      A.pool ∗ stackAt s0.sp hookStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- `decodeErrorPushSpecWithStack` existentializing the updated box pointer `e'` at slot `d` in `post`. -/
@[expose] def decodeErrorPushExternSpecWithStack (A : RustAlloc)
    (hookStack : Nat := extHookStack) : Spec (BitVec 64 × BitVec 64 × Nat) where
  pre := fun (d, e, n) s =>
    ⌜s.readReg64 .x0 = d ∧ e ≠ 0#64 ∧ n < 2 ^ 32⌝ ∗ (d ↦₆₄ e) ∗
      decodeErrorAtStackLen A e n ∗
      A.pool ∗ stackAt s.sp hookStack
  post := fun (d, _, n) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ e' : BitVec 64, ⌜e' ≠ 0#64⌝ ∗ (d ↦₆₄ e') ∗
        decodeErrorAtStackLen A e' (n + 1)) ∗
      A.pool ∗ stackAt s0.sp hookStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem decodeErrorPushExtern_of_decodeErrorPush
    {P : Program} {addr : BitVec 64} {A : RustAlloc} {hookStack : Nat}
    (h : subroutine_ok P addr (decodeErrorPushSpecWithStack A hookStack)) :
    subroutine_ok P addr (decodeErrorPushExternSpecWithStack A hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨d, e, n⟩ R s0 hpc hrun hpre hal => ?_
  simp only [decodeErrorPushExternSpecWithStack, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, he_ne, hn⟩, hmem⟩
  have hpre' : s0.mem ⊨ (decodeErrorPushSpecWithStack A hookStack).pre (d, e, n) s0 ∗ R := by
    simp only [decodeErrorPushSpecWithStack, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hn⟩, hmem⟩
  refine h.mono_outcome (d, e, n) R s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [decodeErrorPushSpecWithStack, decodeErrorPushExternSpecWithStack,
      sepConj_assoc, sepExists_sepConj_left, satisfies_pure_sepConj, satisfies_sepExists] at hpost ⊢
    exact ⟨hpost.1, e, he_ne, hpost.2⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

/-- `decodeVarintSlowSpec A` with configurable stack budget `hookStack` (`= decodeVarintSlowSpec A` at `varintSlowStack`). -/
@[expose] def decodeVarintSlowSpecWithStack (A : RustAlloc)
    (hookStack : Nat := extHookStack) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (slotA, slot, ptr, bs) s =>
    ⌜s.readReg64 .x0 = slotA ∧ bs.length < 2 ^ 64⌝ ∗
      (slotA ↦₆₄ slot) ∗ (slot ↦₆₄ ptr) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt s.sp hookStack
  post := fun (slotA, slot, ptr, bs) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (slotA ↦₆₄ slot) ∗ (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt s0.sp hookStack ∗
      match varintSlow bs with
      | some (v, k) =>
        ⌜sf.readReg64 .x0 = 0#64 ∧ sf.readReg64 .x1 = v⌝ ∗
          (slot ↦₆₄ (ptr + BitVec.ofNat 64 k)) ∗
          ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k))
      | none =>
        ⌜sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x1 ≠ 0#64⌝ ∗
          decodeErrorAtStackLen A (sf.readReg64 .x1) 0 ∗
          (slot ↦₆₄ (ptr + BitVec.ofNat 64 (min 10 bs.length))) ∗
          ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - min 10 bs.length))
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

private theorem satisfies_anyHeap_frame {m : Memory} {P F R : SepProp}
    (h : m ⊨ (P ∗ anyHeap) ∗ F ∗ R) :
    m ⊨ (P ∗ anyHeap) ∗ R := by
  have h1 : (P ∗ anyHeap) ∗ F ∗ R ⊢ (P ∗ anyHeap) ∗ R := by
    rw [sepConj_assoc P anyHeap (F ∗ R), ← sepConj_assoc anyHeap F R, sepConj_assoc P anyHeap R]
    exact sepConj_mono_right (sepConj_mono_left (entails_anyHeap (anyHeap ∗ F)))
  exact Satisfies.mono h1 h

theorem decodeErrorFromWithStack_of_decodeErrorFrom {P : Program} {addr : BitVec 64} {A : RustAlloc}
    {hookStack : Nat} (h : subroutine_ok P addr (decodeErrorFromSpec A))
    (hle : decodeErrorHookStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addr (decodeErrorFromSpecWithStack A hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨k, w⟩ R s0 hpc hrun hpre hal => ?_
  have hsplit : stackAt s0.sp hookStack =
      memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - decodeErrorHookStack) ∗
        stackAt s0.sp decodeErrorHookStack := by
    have h1 := stackAt_split_bottom s0.sp decodeErrorHookStack (hookStack - decodeErrorHookStack) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - decodeErrorHookStack) ∗ R
  have hpre' : s0.mem ⊨ (decodeErrorFromSpec A).pre (k, w) s0 ∗ R' := by
    dsimp only [decodeErrorFromSpecWithStack, decodeErrorFromSpec, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  refine h.mono_outcome (k, w) R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [decodeErrorFromSpecWithStack, decodeErrorFromSpec, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · exact Or.inr (Or.inl ⟨hpan, satisfies_anyHeap_frame hpost⟩)
  · dsimp only [decodeErrorFromSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [decodeErrorFromSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

theorem decodeErrorPushWithStack_of_decodeErrorPush {P : Program} {addr : BitVec 64} {A : RustAlloc}
    {hookStack : Nat} (h : subroutine_ok P addr (decodeErrorPushSpec A))
    (hle : decodeErrorHookStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addr (decodeErrorPushSpecWithStack A hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨d, e, n⟩ R s0 hpc hrun hpre hal => ?_
  have hsplit : stackAt s0.sp hookStack =
      memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - decodeErrorHookStack) ∗
        stackAt s0.sp decodeErrorHookStack := by
    have h1 := stackAt_split_bottom s0.sp decodeErrorHookStack (hookStack - decodeErrorHookStack) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - decodeErrorHookStack) ∗ R
  have hpre' : s0.mem ⊨ (decodeErrorPushSpec A).pre (d, e, n) s0 ∗ R' := by
    dsimp only [decodeErrorPushSpecWithStack, decodeErrorPushSpec, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  refine h.mono_outcome (d, e, n) R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [decodeErrorPushSpecWithStack, decodeErrorPushSpec, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · exact Or.inr (Or.inl ⟨hpan, satisfies_anyHeap_frame hpost⟩)
  · dsimp only [decodeErrorPushSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [decodeErrorPushSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

theorem decodeVarintSlowWithStack_of_decodeVarintSlow {P : Program} {addr : BitVec 64} {A : RustAlloc}
    {hookStack : Nat} (h : subroutine_ok P addr (decodeVarintSlowSpec A))
    (hle : varintSlowStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addr (decodeVarintSlowSpecWithStack A hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨slotA, slot, ptr, bs⟩ R s0 hpc hrun hpre hal => ?_
  have hsplit : stackAt s0.sp hookStack =
      memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - varintSlowStack) ∗
        stackAt s0.sp varintSlowStack := by
    have h1 := stackAt_split_bottom s0.sp varintSlowStack (hookStack - varintSlowStack) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - varintSlowStack) ∗ R
  have hpre' : s0.mem ⊨ (decodeVarintSlowSpec A).pre (slotA, slot, ptr, bs) s0 ∗ R' := by
    dsimp only [decodeVarintSlowSpecWithStack, decodeVarintSlowSpec, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  refine h.mono_outcome (slotA, slot, ptr, bs) R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [decodeVarintSlowSpecWithStack, decodeVarintSlowSpec, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · exact Or.inr (Or.inl ⟨hpan, satisfies_anyHeap_frame hpost⟩)
  · dsimp only [decodeVarintSlowSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [decodeVarintSlowSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

/-- `subtle::black_box::<u8>(v: u8) -> u8`: preserves the low byte `(sf.readReg64 .x0).setWidth 8 = v.setWidth 8`
and trace. -/
@[expose] def blackBoxU8Spec : Spec (BitVec 64) where
  pre := fun v s => ⌜s.readReg64 .x0 = v⌝
  post := fun v s0 sf =>
    ⌜(sf.readReg64 .x0).setWidth 8 = v.setWidth 8 ∧ sf.trace = s0.trace⌝

theorem blackBoxU8_of_blackBox {P : Program} {addr : BitVec 64}
    (h : subroutine_ok P addr blackBoxSpec) :
    subroutine_ok P addr blackBoxU8Spec := by
  refine subroutine_ok_outcome_intro fun v R s0 hpc hrun hpre hal =>
    h.mono_outcome v R s0 hpc hrun hpre hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [blackBoxSpec, blackBoxU8Spec, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨hx0, htr⟩, hR⟩
    have h8 : (sf.readReg64 .x0).setWidth 8 = v.setWidth 8 := by
      rw [hx0]
      change ((v.setWidth 8).setWidth 64).setWidth 8 = v.setWidth 8
      rw [BitVec.setWidth_setWidth_of_le (v.setWidth 8) (by decide : 8 ≤ 64), BitVec.setWidth_eq]
    exact ⟨⟨h8, htr⟩, hR⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

/-- Result layout of `<uuid::Uuid>::try_parse` at `out` (32 bytes) allowing any non-`Ok` tag
`tag ≠ uuidOkTag` on `.none`, matching both `uuidResultAt out (parse bs)` and `Externs.uuidTryParseSpec`. -/
@[expose] def uuidTryParseAnyResultAt (out : BitVec 64) : SepProp :=
  ∃∗ res : Option (List.Vector (BitVec 8) 16),
    match res with
    | some u => (out ↦₃₂ uuidOkTag) ∗ ((out + 4#64) ↦ₛ u.toList) ∗ memRegion (out + 20#64) 12
    | none => ∃∗ tag : BitVec 32, ⌜tag ≠ uuidOkTag⌝ ∗ (out ↦₃₂ tag) ∗ memRegion (out + 4#64) 28

/-- Nondeterministic `<uuid::Uuid>::try_parse(x0 = ptr, x1 = len)` contract (sret `x8`, 32 bytes):
writes `uuidTryParseAnyResultAt out` and preserves `(p ↦ₛ bs)` and trace. -/
@[expose] def uuidTryParseAnySpec : Spec (BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (p, bs, out) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧ s.readReg64 .x8 = out⌝ ∗
      (p ↦ₛ bs) ∗ memRegion out 32
  post := fun (p, bs, out) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (p ↦ₛ bs) ∗ uuidTryParseAnyResultAt out

theorem uuidResultAt_entails_any (out : BitVec 64) (r : Option (List.Vector (BitVec 8) 16)) :
    uuidResultAt out r ⊢ uuidTryParseAnyResultAt out := by
  unfold uuidTryParseAnyResultAt
  refine Entails.sepExists_right r ?_
  cases r with
  | some u => exact Entails.refl _
  | none =>
    unfold uuidResultAt
    refine Entails.sepExists_right uuidErrParseOther ?_
    rw [show (⌜uuidErrParseOther ≠ uuidOkTag⌝ : SepProp) = emp by simp [uuidErrParseOther, uuidOkTag],
      emp_sepConj]
    exact Entails.refl _

theorem uuidTryParseAny_of_spec {P : Program} {addr : BitVec 64}
    (h : subroutine_ok P addr (uuidTryParseSpec uuidTryParse)) :
    subroutine_ok P addr uuidTryParseAnySpec := by
  refine subroutine_ok_outcome_intro fun ⟨p, bs, out⟩ R s0 hpc hrun hpre hal =>
    h.mono_outcome (p, bs, out) R s0 hpc hrun hpre hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [uuidTryParseSpec, uuidTryParseAnySpec, sepConj_assoc,
      satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hmem⟩
    refine ⟨htr, ?_⟩
    exact Satisfies.mono
      (sepConj_mono_right (sepConj_mono_left (uuidResultAt_entails_any out (uuidTryParse bs)))) hmem
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

theorem uuidTryParseAnyWithStack_of_code {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (h : subroutine_ok P addr (uuidTryParseCodeSpec uuidTryParse))
    (hle : uuidTryParseStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addr (withStack uuidTryParseAnySpec hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨p, bs, out⟩ R s0 hpc hrun hpre hal => ?_
  have hsplit : stackAt s0.sp hookStack =
      memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - uuidTryParseStack) ∗
        stackAt s0.sp uuidTryParseStack := by
    have h1 := stackAt_split_bottom s0.sp uuidTryParseStack (hookStack - uuidTryParseStack) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - uuidTryParseStack) ∗ R
  have hpre' : s0.mem ⊨ (uuidTryParseCodeSpec uuidTryParse).pre (p, bs, out) s0 ∗ R' := by
    dsimp only [withStack, uuidTryParseAnySpec, uuidTryParseCodeSpec, uuidTryParseSpec, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  refine h.mono_outcome (p, bs, out) R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [uuidTryParseCodeSpec, uuidTryParseSpec, R'] at hpost
    have hpost' : sf.mem ⊨ ((⌜sf.trace = s0.trace⌝ ∗ (p ↦ₛ bs) ∗ uuidTryParseAnyResultAt out) ∗
        stackAt s0.sp uuidTryParseStack) ∗
        (memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - uuidTryParseStack) ∗ R) :=
      Satisfies.mono (sepConj_mono_left (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
        (uuidResultAt_entails_any out (uuidTryParse bs)))))) hpost
    dsimp only [withStack, uuidTryParseAnySpec]
    rw [hsplit]
    ac_nf at hpost' ⊢
  · rcases hpan with ⟨_, hpan_sat⟩
    have h0 : (uuidTryParseCodeSpec uuidTryParse).onPanic (p, bs, out) s0 sf = ⌜False⌝ := rfl
    rw [h0, satisfies_pure_sepConj] at hpan_sat
    exact False.elim hpan_sat.1
  · rcases hex with ⟨code, _, hex_sat⟩ | ⟨_, hoom_sat⟩
    · have h0 : (uuidTryParseCodeSpec uuidTryParse).onExit (p, bs, out) code s0 sf = ⌜False⌝ := rfl
      rw [h0, satisfies_pure_sepConj] at hex_sat
      exact False.elim hex_sat.1
    · have h0 : (uuidTryParseCodeSpec uuidTryParse).onOom (p, bs, out) s0 sf = ⌜False⌝ := rfl
      rw [h0, satisfies_pure_sepConj] at hoom_sat
      exact False.elim hoom_sat.1

/-- Nondeterministic `libsignal_session_rng_fill(dst = x0, len = x1)` contract:
overwrites `memRegion dst len` with some `bs` of length `len` and preserves trace. -/
@[expose] def rngFillAnySpec : Spec (BitVec 64 × Nat) where
  pre := fun (dst, len) s =>
    ⌜s.readReg64 .x0 = dst ∧ (s.readReg64 .x1).toNat = len⌝ ∗
      memRegion dst len
  post := fun (dst, len) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ bs : List (BitVec 8), ⌜bs.length = len⌝ ∗ (dst ↦ₛ bs))

/-- Separate RNG contract structure (`Stage2RngContract b ctl ext`), split out from
`Stage2ContractsX` so RNG-free code and `faultOnRngExt` instantiations do not depend on `rng_fill`. -/
structure Stage2RngContract (b : BitVec 64) (ctl : BitVec 64)
    (ext : String → Option (State → State)) : Prop where
  rng_fill :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr rngFillName) (rngFillSpec ctl)


/-- Whole-function AES-256-CBC encrypt contract parameterized by `encFn : Bytes → Bytes → Bytes → Bytes`
(`aesEncSpec E A = aesEncFnSpec (fun pt k iv => aesCbcEncrypt E (HKDF.bytesToKey32 k) (CBC.bytesToBlock iv) pt) A`). -/
@[expose] def aesEncFnSpec
    (encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8))
    (A : RustAlloc) : Spec AesCall where
  pre := fun x s => x.pre A s
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ x.frame ∗
      vecU8 A x.ret (encFn x.input x.key x.iv) ∗
      A.pool ∗ stackAt s0.sp extHookStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

@[simp]
theorem aesEncFnSpec_block_eq (E : CBC.AesKey → CBC.Block → CBC.Block) (A : RustAlloc) :
    aesEncFnSpec (fun pt k iv => aesCbcEncrypt E (HKDF.bytesToKey32 k) (CBC.bytesToBlock iv) pt) A =
      aesEncSpec E A :=
  rfl

/-- Ciphertext length bound `(encFn pt k iv).length ≤ pt.length + 16` for PKCS#7-padded
AES-256-CBC encryption. -/
@[expose] def AesEncLenBound
    (encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8)) : Prop :=
  ∀ pt k iv, (encFn pt k iv).length ≤ pt.length + 16

theorem aesEncLenBound_aesCbcEncrypt (E : CBC.AesKey → CBC.Block → CBC.Block) :
    AesEncLenBound (fun pt k iv => aesCbcEncrypt E (HKDF.bytesToKey32 k) (CBC.bytesToBlock iv) pt) := by
  intro pt k iv
  have hblk : ∀ l : List CBC.Block,
      (l.flatMap CBC.blockToBytesLE).length = 16 * l.length := by
    intro l
    induction l with
    | nil => rfl
    | cons h t ih =>
      simp only [List.flatMap_cons, List.length_append, ih, List.length_cons, CBC.blockToBytesLE,
        List.length_ofFn]
      omega
  unfold aesCbcEncrypt
  rw [hblk, List.Vector.toList_length]
  change 16 * (pt.length / 16 + 1) ≤ pt.length + 16
  omega

/-- Whole-function AES-256-CBC decrypt contract parameterized by
`decFn : Bytes → Bytes → Bytes → Option Bytes`, with `Externs.aesDecSpec`'s `.none` layout
(`(x.ret ↦₆₄ errTag) ∗ memRegion (x.ret + 8#64) 16`, without requiring `p ≠ 0` at `+8`). -/
@[expose] def aesDecFnSpec
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) : Spec AesCall where
  pre := fun x s => x.pre A s
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ x.frame ∗
      (match decFn x.input x.key x.iv with
       | some pt => vecU8 A x.ret pt
       | none => (x.ret ↦₆₄ errTag) ∗ memRegion (x.ret + 8#64) 16) ∗
      A.pool ∗ stackAt s0.sp extHookStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Block-cipher specialization of `aesDecFnSpec` (dropping `p ≠ 0` on `.none`). -/
abbrev aesDecWeakSpec (D : CBC.AesKey → CBC.Block → CBC.Block) (A : RustAlloc) : Spec AesCall :=
  aesDecFnSpec (fun ct k iv => aesCbcDecrypt D (HKDF.bytesToKey32 k) (CBC.bytesToBlock iv) ct) A

theorem aesDecWeak_of_aesDec {P : Program} {addr : BitVec 64}
    {D : CBC.AesKey → CBC.Block → CBC.Block} {A : RustAlloc}
    (h : subroutine_ok P addr (aesDecSpec D A)) :
    subroutine_ok P addr (aesDecWeakSpec D A) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal =>
    h.mono_outcome x R s0 hpc hrun hpre hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [aesDecSpec, aesDecWeakSpec, aesDecFnSpec,
      sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hmem_post⟩
    refine ⟨htr, ?_⟩
    cases hdec : aesCbcDecrypt D (HKDF.bytesToKey32 x.key) (CBC.bytesToBlock x.iv) x.input with
    | some pt =>
      simpa only [hdec, sepConj_assoc] using hmem_post
    | none =>
      simp only [hdec, sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right,
        satisfies_sepExists] at hmem_post ⊢
      rcases hmem_post with ⟨p, hmem_p⟩
      have h1 : sf.mem ⊨ ⌜p ≠ 0⌝ ∗ (x.frame ∗ (x.ret ↦₆₄ errTag) ∗
          (((x.ret + 8#64) ↦₆₄ p) ∗ memRegion (x.ret + 16#64) 8) ∗
          A.pool ∗ stackAt s0.sp extHookStack ∗ R) := by
        ac_nf at hmem_p ⊢
      rw [satisfies_pure_sepConj] at h1
      rcases h1 with ⟨_, hrest⟩
      rw [memRegion_split' (b := x.ret + 8#64) (b' := x.ret + 16#64) (n := 8) (k := 8)
        (by decide) (by bv_omega) (by decide), memRegion_eight]
      simp only [sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
      exact ⟨p, by ac_nf at hrest ⊢⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

/-- Relational empty-state `spqr::recv` contract (`st.bytes = []` at `spqrRecvStack`): writes
`spqrRecvResultAt A ret res` with `res = .ok ([], none)` or `msg.bytes ≠ [] ∧ ∃ sd, res = .error sd`. -/
@[expose] def spqrRecvEmptyAnySpec (A : RustAlloc) : Spec (VecArg × VecArg × BitVec 64) where
  pre := fun (st, msg, ret) s =>
    ⌜s.readReg64 .x0 = st.v ∧ s.readReg64 .x1 = msg.v ∧ s.readReg64 .x8 = ret ∧ st.bytes = []⌝ ∗
      st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ A.pool ∗ stackAt s.sp spqrRecvStack
  post := fun (st, msg, ret) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ st.at A ∗ msg.at A ∗
      (∃∗ res : Except Bool (List (BitVec 8) × Salt),
        ⌜res = .ok ([], none) ∨ (msg.bytes ≠ [] ∧ ∃ sd, res = .error sd)⌝ ∗
          spqrRecvResultAt A ret res) ∗
      A.pool ∗ stackAt s0.sp spqrRecvStack
  onPanic := fun _ s0 sf =>
    ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap


end CryptoVerification.LibsignalTripleRatchet
