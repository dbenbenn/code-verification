/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hooks.Defs
public import LibsignalBinary.Proofs.TripleRatchet.TrapRng -- proof-setup: allow-public-import
public import ProofLib.SepLogic.WP
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpecLemmas.LibsignalTripleRatchetProofDefs
public section

namespace CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Instruction decode lemmas -/

abbrev finishGrow7Name : String :=
  "<alloc::raw_vec::RawVecInner>::finish_grow [local#6]"

abbrev growAmortizedName : String :=
  "<alloc::raw_vec::RawVecInner>::grow_amortized"

abbrev growOneStrPairName : String :=
  "<alloc::raw_vec::RawVec<(&str, &str)>>::grow_one"

/-! ## State normalization helpers -/

namespace BS31

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

end BS31

open BS31

/-! ## Extern hook lemmas on `tripleRatchetProgAt` -/

theorem sessionShim_hookOk : HookOk hookNoop sessionShimSpec := by
  refine hookNoop_ok fun _ R s0 hpre => ?_
  simp only [sessionShimSpec, hookNoop, retHook, id_eq, State.trace_setPC,
    satisfies_pure_sepConj, true_and, emp_sepConj] at hpre ⊢
  exact hpre

theorem allocHooks_tripleRatchetExterns_trap (C : Crypto)
    (A : RustAlloc) (abs : String → Option (State → State)) (hA : AllocHooks A abs) :
    AllocHooks A (Rust.withPanics (trTrapExterns C abs)) := by
  have habs := tripleRatchetExterns_abs C 0#64 abs
  have h4 : Rust.withPanics (trTrapExterns C abs) "__rustc::__rust_alloc" =
      abs "__rustc::__rust_alloc" :=
    (withPanics_trTrap_ne C abs (n := "__rustc::__rust_alloc") (by decide)).trans
      (Option.some.inj (congrArg (·[4]?) habs))
  have h5 : Rust.withPanics (trTrapExterns C abs) "__rustc::__rust_dealloc" =
      abs "__rustc::__rust_dealloc" :=
    (withPanics_trTrap_ne C abs (n := "__rustc::__rust_dealloc") (by decide)).trans
      (Option.some.inj (congrArg (·[5]?) habs))
  have h6 : Rust.withPanics (trTrapExterns C abs) "__rustc::__rust_realloc" =
      abs "__rustc::__rust_realloc" :=
    (withPanics_trTrap_ne C abs (n := "__rustc::__rust_realloc") (by decide)).trans
      (Option.some.inj (congrArg (·[6]?) habs))
  exact ⟨by simpa [HookSat, h4] using hA.alloc,
    by simpa [HookSat, h5] using hA.dealloc,
    by simpa [HookSat, h6] using hA.realloc⟩

theorem allocHooks_tripleRatchetExterns (C : Crypto) (ctl : BitVec 64)
    (A : RustAlloc) (abs : String → Option (State → State)) (hA : AllocHooks A abs) :
    AllocHooks A (Rust.withPanics (tripleRatchetExterns C ctl abs)) := by
  have ⟨ha, hd, hr⟩ := allocHooks_tripleRatchetExterns_trap C A abs hA
  have e4 : Rust.withPanics (trTrapExterns C abs) "__rustc::__rust_alloc" =
      Rust.withPanics (tripleRatchetExterns C ctl abs) "__rustc::__rust_alloc" := by
    rw [withPanics_trTrap_ne C abs (n := "__rustc::__rust_alloc") (by decide)]
    unfold Rust.withPanics
    rw [tripleRatchetExterns_ctl C 0#64 ctl abs (n := "__rustc::__rust_alloc") (by decide)]
  have e5 : Rust.withPanics (trTrapExterns C abs) "__rustc::__rust_dealloc" =
      Rust.withPanics (tripleRatchetExterns C ctl abs) "__rustc::__rust_dealloc" := by
    rw [withPanics_trTrap_ne C abs (n := "__rustc::__rust_dealloc") (by decide)]
    unfold Rust.withPanics
    rw [tripleRatchetExterns_ctl C 0#64 ctl abs (n := "__rustc::__rust_dealloc") (by decide)]
  have e6 : Rust.withPanics (trTrapExterns C abs) "__rustc::__rust_realloc" =
      Rust.withPanics (tripleRatchetExterns C ctl abs) "__rustc::__rust_realloc" := by
    rw [withPanics_trTrap_ne C abs (n := "__rustc::__rust_realloc") (by decide)]
    unfold Rust.withPanics
    rw [tripleRatchetExterns_ctl C 0#64 ctl abs (n := "__rustc::__rust_realloc") (by decide)]
  exact ⟨by unfold HookSat at ha ⊢; rwa [← e4],
    by unfold HookSat at hd ⊢; rwa [← e5],
    by unfold HookSat at hr ⊢; rwa [← e6]⟩

/-- Uninitialized-buffer specialization of `rustReallocSpec` (`bs = []`). -/
@[expose] def rustReallocUninitSpec (A : RustAlloc) : Spec (BitVec 64 × Nat × Nat × Nat) where
  pre := fun (p, old, align, new) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = old ∧ (s.readReg64 .x2).toNat = align ∧
      (s.readReg64 .x3).toNat = new ∧ LayoutOk new align⌝ ∗
      A.pool ∗ A.live p old align ∗ memRegion p old ∗ stackAt s.sp allocHookStack
  post := fun (p, old, align, new) s0 sf =>
    A.pool ∗ stackAt s0.sp allocHookStack ∗
      (if sf.readReg64 .x0 = 0 then
        ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
          A.live p old align ∗ memRegion p old
       else
        ⌜(sf.readReg64 .x0).toNat % align = 0 ∧ sf.trace = s0.trace⌝ ∗
          A.live (sf.readReg64 .x0) new align ∗ memRegion (sf.readReg64 .x0) new)

theorem SepWP.instantiate_post_exists {α : Type _} {prog : Program} {target_pc : BitVec 64}
    {s : State} {P R : SepProp} {Q : State → α → SepProp} {rest : State → Prop} (w : α)
    (h : SepWP prog target_pc s P (fun sf P_f => (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ Q sf w ∗ R) ∧ rest sf)) :
    SepWP prog target_pc s P (fun sf P_f => (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ (∃∗ a, Q sf a) ∗ R) ∧ rest sf) :=
  SepWP.mono h fun _ _ _ _ ⟨h1, h2⟩ =>
    ⟨fun hm => Satisfies.mono (sepConj_mono_left (Entails.sepExists_intro w)) (h1 hm), h2⟩

/-! ## Arithmetic helpers for `finish_grow [local#7]` (stride 32, align 8) -/

theorem lsr59_eq_zero {new : BitVec 64} (h : new.toNat * 32 + 8 ≤ 2 ^ 63) :
    new >>> 59 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  exact Nat.div_eq_of_lt (by omega)

theorem lsl5_toNat {x : BitVec 64} (h : x.toNat * 32 < 2 ^ 64) :
    (x <<< 5).toNat = x.toNat * 32 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  change (x.toNat * 32) % 2 ^ 64 = x.toNat * 32
  exact Nat.mod_eq_of_lt h

theorem lsl5_ne_zero {new : BitVec 64} (h0 : 0 < new.toNat) (h : new.toNat * 32 < 2 ^ 64) :
    new <<< 5 ≠ 0#64 := by
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [lsl5_toNat h] at ht
  change new.toNat * 32 = 0 at ht
  omega

theorem hi_32_eq_false {new : BitVec 64} (h : new.toNat * 32 + 8 ≤ 2 ^ 63) :
    (9223372036854775800#64).ult (new <<< 5) = false := by
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, lsl5_toNat (by omega)]
  change ¬ (9223372036854775800 < new.toNat * 32)
  omega

theorem beq_lsl5_zero_eq_false {new : BitVec 64} (h0 : 0 < new.toNat)
    (h : new.toNat * 32 + 8 ≤ 2 ^ 63) :
    ((new <<< 5) == 0#64) = false :=
  beq_eq_false_iff_ne.mpr (lsl5_ne_zero h0 (by omega))

/-! ## `finish_grow` specification and verification -/

abbrev FinishGrow7Ghost :=
  BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

@[expose] def finishGrow7ZeroSpec (A : RustAlloc) : Spec FinishGrow7Ghost where
  pre := fun (out, cap, ptr, new, o0, o1, o2, fsp) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.sp = fsp ∧ cap = 0#64 ∧
      0 < new.toNat ∧ new.toNat * 32 + 8 ≤ 2 ^ 63⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.pool ∗ cells (fsp - 32#64) 4 ∗ stackAt (fsp - 32#64) allocHookStack
  post := fun (out, _cap, _ptr, new, _o0, _o1, _o2, fsp) s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      (if tag = 1#64 then
        ⌜p' = 8#64 ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝
       else
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
        A.live p' (new.toNat * 32) 8 ∗ memRegion p' (new.toNat * 32)) ∗
      A.pool ∗ cells (fsp - 32#64) 4 ∗ stackAt (fsp - 32#64) allocHookStack ∗
      (out ↦₆₄ tag) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

@[expose] def finishGrow7NeSpec (A : RustAlloc) : Spec FinishGrow7Ghost where
  pre := fun (out, cap, ptr, new, o0, o1, o2, fsp) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.sp = fsp ∧ cap ≠ 0#64 ∧
      cap.toNat * 32 < 2 ^ 63 ∧ 0 < new.toNat ∧ new.toNat * 32 + 8 ≤ 2 ^ 63⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.pool ∗ A.live ptr (cap.toNat * 32) 8 ∗ memRegion ptr (cap.toNat * 32) ∗
    cells (fsp - 32#64) 4 ∗ stackAt (fsp - 32#64) allocHookStack
  post := fun (out, cap, ptr, new, _o0, _o1, _o2, fsp) s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      (if tag = 1#64 then
        ⌜p' = 8#64 ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
        A.live ptr (cap.toNat * 32) 8 ∗ memRegion ptr (cap.toNat * 32)
       else
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
        A.live p' (new.toNat * 32) 8 ∗ memRegion p' (new.toNat * 32)) ∗
      A.pool ∗ cells (fsp - 32#64) 4 ∗ stackAt (fsp - 32#64) allocHookStack ∗
      (out ↦₆₄ tag) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

theorem memRegion_split (a : BitVec 64) (n k : Nat) (h : n + k ≤ 2 ^ 64) :
    memRegion a (n + k) = memRegion a n ∗ memRegion (a + BitVec.ofNat 64 n) k :=
  IsBlock.eq (IsBlock.memRegion a (n + k))
    ((IsBlock.memRegion a n).sepConj (IsBlock.memRegion _ k) rfl h)
    fun _ => ⟨fun _ => ⟨trivial, trivial⟩, fun _ => trivial⟩

theorem memRegion_eight (a : BitVec 64) : memRegion a 8 = ∃∗ v, a ↦₆₄ v :=
  IsBlock.eq (IsBlock.memRegion a 8)
    (IsBlock.sepExists fun v => IsBlock.pointsTo64 a v)
    fun _ => ⟨fun _ => ⟨_, rfl⟩, fun _ => trivial⟩

theorem memRegion_cells (a : BitVec 64) (k : Nat) (h : 8 * k ≤ 2 ^ 64) :
    memRegion a (8 * k) = cells a k := by
  induction k generalizing a with
  | zero => exact memRegion_zero a
  | succ k ih =>
    rw [show 8 * (k + 1) = 8 + 8 * k by omega, memRegion_split a 8 (8 * k) (by omega),
      memRegion_eight, ih _ (by omega), cells_succ, sepExists_sepConj_left]

theorem stackAt_split_cells (sp : BitVec 64) (n k : Nat) (h : n + 8 * k ≤ 2 ^ 64) :
    stackAt sp (n + 8 * k) =
      stackAt (sp - BitVec.ofNat 64 (8 * k)) n ∗ cells (sp - BitVec.ofNat 64 (8 * k)) k := by
  simp only [stackAt]
  rw [memRegion_split _ n (8 * k) h, memRegion_cells _ k (by omega)]
  generalize hj : 8 * k = j at *
  have e1 : sp - BitVec.ofNat 64 (n + j) = sp - BitVec.ofNat 64 j - BitVec.ofNat 64 n := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add, Nat.add_comm]
  have e2 : sp - BitVec.ofNat 64 (n + j) + BitVec.ofNat 64 n = sp - BitVec.ofNat 64 j := by
    rw [e1, BitVec.sub_add_cancel]
  rw [e2, e1]

theorem stackAt_split_bottom (sp : BitVec 64) (n d : Nat) (h : n + d ≤ 2 ^ 64) :
    stackAt sp (n + d) = memRegion (sp - BitVec.ofNat 64 (n + d)) d ∗ stackAt sp n := by
  simp only [stackAt]
  rw [show n + d = d + n by omega, memRegion_split _ d n (by omega)]
  congr 2
  rw [BitVec.ofNat_add, BitVec.add_comm (BitVec.ofNat 64 d), ← BitVec.sub_sub,
    BitVec.sub_add_cancel]

theorem allocFailedIn_of_eq {s0 sf : State} (h : sf.trace = s0.trace ++ [allocFailedEvent]) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  refine ⟨?_, ⟨[allocFailedEvent], h.symm⟩⟩
  simp [allocFailedIn, h]

end CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush
