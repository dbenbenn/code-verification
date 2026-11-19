/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecDefs
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SepWPpIn -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsX -- proof-setup: allow-public-import
import ProofLib
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
public meta import ProofLib.SepLogic.CodeLookup
public meta import ProofLib.VCGen
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Defs
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

/-!
# `<Vec<Vec<u8>> as Clone>::clone` on 1 Element

Proves `VecVecClone1OkStmt img A ext` (`vecVecClone1_okX_of_ser`) from `SerContractsX img A ext` for
`<[Vec<u8>]>::to_vec` (`x2 = 1`), allocating the 24-byte outer buffer and cloning the single inner
`Vec<u8>` (`{0, 1, 0}` when empty, or `__rust_alloc(L, 1)` + `memcpy` when `L > 0`).
-/

public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Record.Serialization
open Proofs.libsignal Proofs.libsignal.Hooks2

namespace VvcStateSimp

theorem sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

theorem sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

theorem readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

theorem readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

end VvcStateSimp

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓] VvcStateSimp.sp_setPC_pre
  VvcStateSimp.sp_setMem_setPC_pre VvcStateSimp.readReg64_setPC_pre
  VvcStateSimp.readReg64_setMem_setPC_pre VvcStateSimp.readReg32_setPC_pre
  VvcStateSimp.readReg32_setMem_setPC_pre
attribute [local wp_norm] calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32 calleeSavedVRegs_writeReg
  calleeSavedVRegs_writeVReg128_ite calleeSavedVRegs_writeVReg64_ite calleeSavedVRegs_writeVReg32_ite
  isCalleeSavedVReg updateCalleeSavedVRegs

/-! ## Instruction Fetches and Stub Contracts -/

/-- Existential 12-cell (`0x60`-byte) callee-saved frame below `sp`. -/
@[expose] def vvc1Cells (sp : BitVec 64) : SepProp :=
  ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
  ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
  ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
    ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗
    ((sp - 80#64) ↦₆₄ v2) ∗ ((sp - 72#64) ↦₆₄ v3) ∗
    ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) ∗
    ((sp - 48#64) ↦₆₄ v6) ∗ ((sp - 40#64) ↦₆₄ v7) ∗
    ((sp - 32#64) ↦₆₄ v8) ∗ ((sp - 24#64) ↦₆₄ v9) ∗
    ((sp - 16#64) ↦₆₄ v10) ∗ ((sp - 8#64) ↦₆₄ v11)

/-- Saved `x19..x30` frame cells below `s0.sp` after the prologue. -/
@[expose] def vvc1Saved (s0 : State) : SepProp :=
  ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
  ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))

set_option maxRecDepth 500000 in
theorem vvc1_stack_split (sp : BitVec 64) :
    stackAt sp vecVecClone1StackX = stackAt (sp - 96#64) Stage1X.extHookStack ∗ vvc1Cells sp := by
  have h1 := ProofLib.stackAt_split_cells sp Stage1X.extHookStack 12 (by decide)
  have hadd : Stage1X.extHookStack + 8 * 12 = vecVecClone1StackX := by decide
  rw [hadd] at h1
  change stackAt sp vecVecClone1StackX =
    stackAt (sp - 96#64) Stage1X.extHookStack ∗ cells (sp - 96#64) 12 at h1
  have hc12 : cells (sp - 96#64) 12 = vvc1Cells sp := by
    unfold vvc1Cells
    cells_unfold
  rw [h1, hc12]

theorem vvc1_saved_cells (s0 : State) : vvc1Saved s0 ⊢ vvc1Cells s0.sp := by
  unfold vvc1Saved vvc1Cells
  exact Entails.sepExists_right (s0.readReg64 (Reg.gpr 29#5)) <| Entails.sepExists_right (s0.readReg64 (Reg.gpr 30#5)) <|
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 28#5)) <| Entails.sepExists_right (s0.readReg64 (Reg.gpr 27#5)) <|
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 26#5)) <| Entails.sepExists_right (s0.readReg64 (Reg.gpr 25#5)) <|
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 24#5)) <| Entails.sepExists_right (s0.readReg64 (Reg.gpr 23#5)) <|
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 22#5)) <| Entails.sepExists_right (s0.readReg64 (Reg.gpr 21#5)) <|
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 20#5)) <| Entails.sepExists_right (s0.readReg64 (Reg.gpr 19#5)) <|
    Entails.refl _

theorem vvc1_mem24_cells (dst : BitVec 64) :
    memRegion dst 24 =
      (∃∗ d0 : BitVec 64, dst ↦₆₄ d0) ∗
      (∃∗ d1 : BitVec 64, (dst + 8#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (dst + 16#64) ↦₆₄ d2) := by
  have h1 := memRegion_split dst 8 16 (by decide)
  have h2 := memRegion_split (dst + 8#64) 8 8 (by decide)
  have hadd : dst + 8#64 + 8#64 = dst + 16#64 := by rw [BitVec.add_assoc]; rfl
  change memRegion dst 24 = memRegion dst 8 ∗ memRegion (dst + 8#64) 16 at h1
  change memRegion (dst + 8#64) 16 = memRegion (dst + 8#64) 8 ∗ memRegion (dst + 8#64 + 8#64) 8 at h2
  rw [h1, h2, hadd, ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]

theorem vvc1_allocFailedIn_of_eq {s0 sf : State} (h : sf.trace = s0.trace ++ [allocFailedEvent]) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  refine ⟨?_, ⟨[allocFailedEvent], h.symm⟩⟩
  simp [allocFailedIn, h]

@[expose] def vvc1Q (A : RustAlloc) (x : VecVecClone1Ghost) (s0 : State) (R : SepProp) :
    State → SepProp → Prop :=
  fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (vecVecClone1SpecX A).post x s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

@[expose] def vvc1Qp (A : RustAlloc) (x : VecVecClone1Ghost) (s0 : State) (R : SepProp) :
    State → SepProp → Prop :=
  fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (vecVecClone1SpecX A).onPanic x s0 sf ∗ R)

/-! ## Allocation-Error Panic Tails (`+0xec`, `+0xf8`) -/

theorem vvc1_src_eq (A : RustAlloc) (src : BitVec 64) (enc : List (BitVec 8)) :
    arrayAt (prevElem A) 24 src [enc] =
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜enc.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
          vecHeader src cap ptr (BitVec.ofNat 64 enc.length) ∗
          (if cap = 0 then emp
           else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ enc) ∗
             memRegion (ptr + BitVec.ofNat 64 enc.length) (cap.toNat - enc.length)) := by
  simp only [arrayAt, prevElem, vecU8, vecU8At, sepConj_emp]
  congr 1; funext cap; congr 1; funext ptr
  exact sepConj_left_comm _ _ _

theorem vvc1_src_fold (A : RustAlloc) (src cap ptr : BitVec 64) (enc : List (BitVec 8))
    (h : enc.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0) :
    vecHeader src cap ptr (BitVec.ofNat 64 enc.length) ∗
      (if cap = 0 then emp
       else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ enc) ∗
         memRegion (ptr + BitVec.ofNat 64 enc.length) (cap.toNat - enc.length)) ⊢
      arrayAt (prevElem A) 24 src [enc] := by
  rw [vvc1_src_eq]
  exact Entails.sepExists_right cap <| Entails.sepExists_right ptr <| Entails.pure_right h (Entails.refl _)

theorem vvc1_post_fold (A : RustAlloc) (src dst q : BitVec 64) (enc : List (BitVec 8)) (hq : q ≠ 0#64) :
    vecHeader dst 1#64 q 1#64 ∗ (arrayAt (prevElem A) 24 src [enc] ∗ A.pool ∗ A.live q 24 8 ∗ vecU8 A q enc) ⊢
      arrayAt (prevElem A) 24 src [enc] ∗ (∃∗ q' : BitVec 64, prevVecAt A dst 1#64 q' [enc]) ∗ A.pool := by
  have hpv : vecHeader dst 1#64 q 1#64 ∗ A.live q 24 8 ∗ vecU8 A q enc ⊢
      ∃∗ q' : BitVec 64, prevVecAt A dst 1#64 q' [enc] := by
    refine Entails.sepExists_right q ?_
    rw [prevVecAt_one_eq A dst 1#64 q enc (by decide)]
    have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
    rw [h1, show (1 : Nat) * 24 = 24 from rfl, show ((1 : Nat) - 1) * 24 = 0 from rfl, memRegion_zero, sepConj_emp]
    exact sepConj_mono_right (Entails.pure_right ⟨Nat.le_refl 1, by decide, hq⟩ (Entails.refl _))
  refine Entails.trans (Entails.of_eq (show _ = arrayAt (prevElem A) 24 src [enc] ∗
    (vecHeader dst 1#64 q 1#64 ∗ A.live q 24 8 ∗ vecU8 A q enc) ∗ A.pool by ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono_left hpv)

theorem vvc1_elem_nil (A : RustAlloc) (q : BitVec 64) :
    (q ↦₆₄ 0#64) ∗ ((q + 8#64) ↦₆₄ 1#64) ∗ ((q + 16#64) ↦₆₄ 0#64) ⊢ vecU8 A q [] := by
  unfold vecU8
  refine Entails.sepExists_right 0#64 (Entails.sepExists_right 1#64 ?_)
  unfold vecU8At vecHeader
  have h0 : (0#64 : BitVec 64) = 0 := rfl
  simp only [List.length_nil, h0, ↓reduceIte, sepConj_emp]
  exact Entails.trans (Entails.pure_right ⟨Nat.zero_le _, by decide, by decide⟩ (Entails.refl _))
    (Entails.of_eq (sepConj_comm _ _))

theorem vvc1_elem_cons (A : RustAlloc) (q p : BitVec 64) (enc : List (BitVec 8)) (hp : p ≠ 0#64)
    (hpos : 0 < enc.length) (hlt : enc.length < 2 ^ 63) :
    (q ↦₆₄ BitVec.ofNat 64 enc.length) ∗ ((q + 8#64) ↦₆₄ p) ∗ ((q + 16#64) ↦₆₄ BitVec.ofNat 64 enc.length) ∗
      A.live p enc.length 1 ∗ (p ↦ₛ enc) ⊢ vecU8 A q enc := by
  unfold vecU8
  refine Entails.sepExists_right (BitVec.ofNat 64 enc.length) (Entails.sepExists_right p ?_)
  have hL : (BitVec.ofNat 64 enc.length).toNat = enc.length := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hne : ¬ (BitVec.ofNat 64 enc.length = 0) := by
    intro h
    have h2 := congrArg BitVec.toNat h
    have h0 : (0 : BitVec 64).toNat = 0 := rfl
    rw [hL, h0] at h2; omega
  unfold vecU8At vecHeader
  simp only [hne, ↓reduceIte, hL, Nat.sub_self, memRegion_zero, sepConj_emp]
  exact Entails.trans (Entails.of_eq (by simp only [sepConj_assoc]))
    (sepConj_mono_right (Entails.pure_right ⟨Nat.le_refl _, hlt, hp⟩ (Entails.refl _)))

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
