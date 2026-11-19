/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.TrapRng -- proof-setup: allow-public-import
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.Defs
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
public section

namespace CryptoVerification.LibsignalTripleRatchet.InImage.VarintSlow

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

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

private theorem sessionShim_hookOk : HookOk hookNoop sessionShimSpec := by
  refine hookNoop_ok fun _ R s0 hpre => ?_
  simp only [sessionShimSpec, hookNoop, retHook, id_eq, State.trace_setPC,
    satisfies_pure_sepConj, true_and, emp_sepConj] at hpre ⊢
  exact hpre

private theorem hookSat_tripleRatchetExterns_trap (C : Crypto)
    (abs : String → Option (State → State)) {sym : String} {spec : Spec α}
    (heq : trTrapExterns C abs sym = abs sym)
    (h : HookSat abs sym spec) :
    HookSat (trTrapExterns C abs) sym spec := by
  unfold HookSat at *; rwa [heq]

private theorem hookSat_tripleRatchetExterns (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) {sym : String} {spec : Spec α}
    (heq : tripleRatchetExterns C ctl abs sym = abs sym)
    (h : HookSat abs sym spec) :
    HookSat (tripleRatchetExterns C ctl abs) sym spec := by
  unfold HookSat at *; rwa [heq]

theorem memRegion_split (a : BitVec 64) (n k : Nat) (h : n + k ≤ 2 ^ 64) :
    memRegion a (n + k) = memRegion a n ∗ memRegion (a + BitVec.ofNat 64 n) k :=
  IsBlock.eq (IsBlock.memRegion a (n + k))
    ((IsBlock.memRegion a n).sepConj (IsBlock.memRegion _ k) rfl h)
    fun _ => ⟨fun _ => ⟨trivial, trivial⟩, fun _ => trivial⟩

theorem memRegion_eight (a : BitVec 64) : memRegion a 8 = ∃∗ v, a ↦₆₄ v :=
  IsBlock.eq (IsBlock.memRegion a 8)
    (IsBlock.sepExists fun v => IsBlock.pointsTo64 a v)
    fun _ => ⟨fun _ => ⟨_, rfl⟩, fun _ => trivial⟩

theorem pointsTo64_entails_memRegion8 (a v : BitVec 64) : (a ↦₆₄ v) ⊢ memRegion a 8 := by
  rw [memRegion_eight]
  exact Entails.sepExists_intro v

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

theorem allocFailedIn_of_eq {s0 sf : State} (h : sf.trace = s0.trace ++ [allocFailedEvent]) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  refine ⟨?_, ⟨[allocFailedEvent], h.symm⟩⟩
  simp [allocFailedIn, h]

theorem stackAt_decodeErrorFrom (sp : BitVec 64) :
    stackAt sp decodeErrorHookStack =
      stackAt (sp - 4128#64) 4064 ∗
      stackAt (sp - 32#64) allocHookStack ∗ cells (sp - 32#64) 4 := by
  have h1 : stackAt sp decodeErrorHookStack =
      stackAt (sp - 32#64) (4064 + allocHookStack) ∗ cells (sp - 32#64) 4 :=
    stackAt_split_cells sp (4064 + allocHookStack) 4 (by decide)
  have h2 : stackAt (sp - 32#64) (4064 + allocHookStack) =
      stackAt (sp - 4128#64) 4064 ∗ stackAt (sp - 32#64) allocHookStack := by
    simp only [stackAt, allocHookStack]
    rw [memRegion_split _ 4064 4096 (by decide)]
    have e1 : sp - 32#64 - BitVec.ofNat 64 (4064 + 4096) = sp - 4128#64 - 4064#64 := by
      bv_lin
    have e2 : sp - 32#64 - BitVec.ofNat 64 (4064 + 4096) + 4064#64 = sp - 32#64 - 4096#64 := by
      bv_lin
    rw [e2, e1]
  rw [h1, h2, sepConj_assoc]

theorem memRegion_40_cells (a : BitVec 64) :
    memRegion a 40 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64,
       ∃∗ u3 : BitVec 64, ∃∗ u4 : BitVec 64,
        (a ↦₆₄ u4) ∗ ((a + 8#64) ↦₆₄ u3) ∗ ((a + 16#64) ↦₆₄ u2) ∗
        ((a + 24#64) ↦₆₄ u1) ∗ ((a + 32#64) ↦₆₄ u0)) := by
  rw [memRegion_split a 8 32 (by decide),
    memRegion_split (a + 8#64) 8 24 (by decide),
    memRegion_split (a + 8#64 + 8#64) 8 16 (by decide),
    memRegion_split (a + 8#64 + 8#64 + 8#64) 8 8 (by decide),
    memRegion_eight, memRegion_eight, memRegion_eight, memRegion_eight, memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion_48_cells (a : BitVec 64) :
    memRegion a 48 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64,
       ∃∗ u3 : BitVec 64, ∃∗ u4 : BitVec 64, ∃∗ w : BitVec 64,
        (a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ u4) ∗ ((a + 16#64) ↦₆₄ u3) ∗
        ((a + 24#64) ↦₆₄ u2) ∗ ((a + 32#64) ↦₆₄ u1) ∗ ((a + 40#64) ↦₆₄ u0)) := by
  rw [show (48 : Nat) = 8 + 40 from rfl, memRegion_split a 8 40 (by decide),
    memRegion_eight a, memRegion_40_cells (a + 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion_72_cells (a : BitVec 64) :
    memRegion a 72 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64,
       ∃∗ u3 : BitVec 64, ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64,
       ∃∗ u6 : BitVec 64, ∃∗ u7 : BitVec 64, ∃∗ u8 : BitVec 64,
        (a ↦₆₄ u8) ∗ ((a + 8#64) ↦₆₄ u7) ∗ ((a + 16#64) ↦₆₄ u6) ∗
        ((a + 24#64) ↦₆₄ u5) ∗ ((a + 32#64) ↦₆₄ u4) ∗ ((a + 40#64) ↦₆₄ u3) ∗
        ((a + 48#64) ↦₆₄ u2) ∗ ((a + 56#64) ↦₆₄ u1) ∗ ((a + 64#64) ↦₆₄ u0)) := by
  rw [memRegion_split a 8 64 (by decide),
    memRegion_split (a + 8#64) 8 56 (by decide),
    memRegion_split (a + 8#64 + 8#64) 8 48 (by decide),
    memRegion_split (a + 8#64 + 8#64 + 8#64) 8 40 (by decide),
    memRegion_40_cells (a + 8#64 + 8#64 + 8#64 + 8#64),
    memRegion_eight, memRegion_eight, memRegion_eight, memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd]

theorem sepWPp_pure_mid {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B ∗ C) Q Qp) :
    SepWPp prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) Q Qp := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWPp.pure_elim h

private def decodeErrorFromSpec0 (A : RustAlloc) : Spec (BitVec 64 × BitVec 64) where
  pre := (decodeErrorFromSpec A).pre
  post := fun (k, w) s0 sf =>
    ⌜sf.readReg64 .x0 ≠ 0#64 ∧ sf.trace = s0.trace ∧ KindNoHeap w⌝ ∗
      A.live (sf.readReg64 .x0) 72 8 ∗
      ((sf.readReg64 .x0) ↦₆₄ 0#64) ∗
      ((sf.readReg64 .x0 + 8#64) ↦₆₄ 8#64) ∗
      ((sf.readReg64 .x0 + 16#64) ↦₆₄ 0#64) ∗
      ((sf.readReg64 .x0 + 24#64) ↦₆₄ w) ∗
      memRegion (sf.readReg64 .x0 + 32#64) 40 ∗
      memRegion k 48 ∗
      A.pool ∗ stackAt s0.sp decodeErrorHookStack
  onPanic := (decodeErrorFromSpec A).onPanic

private theorem decodeErrorFromSpec0_post_satisfies (A : RustAlloc)
    (x : BitVec 64 × BitVec 64) (R : SepProp) (s0 sf : State)
    (hm : sf.mem ⊨ (decodeErrorFromSpec0 A).post x s0 sf ∗ R) :
    sf.mem ⊨ (decodeErrorFromSpec A).post x s0 sf ∗ R := by
  rcases x with ⟨k, w⟩
  simp only [decodeErrorFromSpec0, sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hne, htr, hkind⟩, hm⟩
  simp only [decodeErrorFromSpec, decodeErrorAtStackLen, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨hne, htr⟩, ?_⟩
  have hm' : sf.mem ⊨
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        vecAt A 32 8 stackEntryAt (sf.readReg64 .x0) cap ptr (List.replicate 0 ())) ∗
      (∃∗ w' : BitVec 64, ⌜KindNoHeap w'⌝ ∗ ((sf.readReg64 .x0 + 24#64) ↦₆₄ w')) ∗
      (A.live (sf.readReg64 .x0) 72 8 ∗ memRegion (sf.readReg64 .x0 + 32#64) 40 ∗
        memRegion k 48 ∗ A.pool ∗ stackAt s0.sp decodeErrorHookStack ∗ R) := by
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    refine ⟨w, 0#64, 8#64, ?_⟩
    simp only [vecAt, vecHeader, vecBuf, List.replicate, List.length_nil, BitVec.ofNat_eq_ofNat,
      ite_true, (by decide : (0#64 : BitVec 64).toNat = 0),
      (by decide : 0 ≤ 0 ∧ 0 * 32 < 2 ^ 63 ∧ (8#64 : BitVec 64) ≠ 0),
      sepConj_emp, sepConj_assoc, true_and]
    have hm_pure : sf.mem ⊨ ⌜(8#64 : BitVec 64) ≠ 0#64⌝ ∗ ⌜KindNoHeap w⌝ ∗
        (((sf.readReg64 .x0) ↦₆₄ 0#64) ∗ ((sf.readReg64 .x0 + 8#64) ↦₆₄ 8#64) ∗
          ((sf.readReg64 .x0 + 16#64) ↦₆₄ 0#64) ∗ ((sf.readReg64 .x0 + 24#64) ↦₆₄ w) ∗
          A.live (sf.readReg64 .x0) 72 8 ∗ memRegion (sf.readReg64 .x0 + 32#64) 40 ∗
          memRegion k 48 ∗ A.pool ∗ stackAt s0.sp decodeErrorHookStack ∗ R) :=
      (satisfies_pure_sepConj _ _ _).mpr
        ⟨by decide, (satisfies_pure_sepConj _ _ _).mpr ⟨hkind, Satisfies.of_eq hm⟩⟩
    exact Satisfies.of_eq hm_pure
  exact Satisfies.of_eq hm' (by unfold vecOf; ac_rfl)

attribute [local irreducible] Program.fnOff

end CryptoVerification.LibsignalTripleRatchet.InImage.VarintSlow
