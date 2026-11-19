/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerDefs
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyNoneX -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Fetch
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodySomeX
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

/-!
# `SessionRecord::serialize` with One Previous Session: Epilogue Tail and Framing Helpers

Proves `serPrev1Tail_ok : SerPrev1TailStmt img A ext` (`+692 .. ret`), dropping the cloned
`SessionStructure` and temporary `Vec<Vec<u8>>`, together with local heap-folding and branch
helpers consumed by `CloseSerBody`.
-/

public section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 2000000

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.Serialization
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX
open Proofs.libsignal.Hooks2

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local wp_norm] calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite calleeSavedVRegs_writeVReg64_ite
  calleeSavedVRegs_writeVReg32_ite isCalleeSavedVReg updateCalleeSavedVRegs

/-! ## Instruction decodes for the inline `Vec<Vec<u8>>` drop -/

theorem k5t_false_left {m : Memory} {R : SepProp} (h : m ⊨ ⌜False⌝ ∗ R) : False :=
  not_satisfies_false_sepConj h

/-! ## Shared epilogue (`+812 .. ret`) and tail (`+692 .. ret`) -/

theorem prevVecAt_one_fold_ser (A : RustAlloc) (r cap q : BitVec 64) (enc : List (BitVec 8))
    (h : cap ≠ 0#64 ∧ cap.toNat * 24 < 2 ^ 63 ∧ q ≠ 0#64) :
    ((r ↦₆₄ cap) ∗ ((r + 8#64) ↦₆₄ q) ∗ ((r + 16#64) ↦₆₄ 1#64) ∗
        A.live q (cap.toNat * 24) 8 ∗ arrayAt (prevElem A) 24 q [enc] ∗
        memRegion (q + 24#64) ((cap.toNat - 1) * 24)) ⊢
      prevVecAt A r cap q [enc] := by
  rw [prevVecAt_one_cells_ser]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (Entails.pure_right h (Entails.refl _))))

theorem prevVecAt_one_pure_first (A : RustAlloc) (r cap q : BitVec 64) (enc : List (BitVec 8)) :
    prevVecAt A r cap q [enc] =
      ⌜cap ≠ 0#64 ∧ cap.toNat * 24 < 2 ^ 63 ∧ q ≠ 0#64⌝ ∗
        ((r ↦₆₄ cap) ∗ ((r + 8#64) ↦₆₄ q) ∗ ((r + 16#64) ↦₆₄ 1#64) ∗
          A.live q (cap.toNat * 24) 8 ∗ arrayAt (prevElem A) 24 q [enc] ∗
          memRegion (q + 24#64) ((cap.toNat - 1) * 24)) := by
  rw [prevVecAt_one_cells_ser]
  ac_rfl

/-- `vecVecClone1`'s result at `sp - 800`, opened down to the element header cells at `q`. -/
theorem prevVecAt_800_open (A : RustAlloc) (sp q : BitVec 64) (enc : List (BitVec 8)) :
    prevVecAt A (sp - 800#64) 1#64 q [enc] =
      (∃∗ capE : BitVec 64, ∃∗ ptrE : BitVec 64,
        ⌜q ≠ 0#64⌝ ∗
          (((sp - 800#64) ↦₆₄ 1#64) ∗ ((sp - 792#64) ↦₆₄ q) ∗ ((sp - 784#64) ↦₆₄ 1#64) ∗
            A.live q 24 8 ∗
            (q ↦₆₄ capE) ∗ ((q + 8#64) ↦₆₄ ptrE) ∗
            ((q + 16#64) ↦₆₄ BitVec.ofNat 64 enc.length) ∗
            RustHeap.vecU8Buf A capE ptrE enc)) := by
  have e8 : sp - 800#64 + 8#64 = sp - 792#64 := bv_sub_add_lit sp 800 8
  have e16 : sp - 800#64 + 16#64 = sp - 784#64 := bv_sub_add_lit sp 800 16
  rw [prevVecAt_cap1_cells, e8, e16]
  unfold vecU8
  simp only [vecU8At_cells, sepExists_sepConj_right]
  refine ProofLib.sepExists_congr fun capE => ProofLib.sepExists_congr fun ptrE => ?_
  ac_rfl

/-- No unsigned carry out of `ofNat a + ofNat b` (the `adds` / `b.hs` branch). -/
theorem ult_ofNat_add_false {a b : Nat} (h : a + b < 2 ^ 63) :
    (BitVec.ofNat 64 a + BitVec.ofNat 64 b).ult (BitVec.ofNat 64 a) = false := by
  rw [← BitVec.ofNat_add]
  simp only [BitVec.ult, BitVec.toNat_ofNat]
  have h1 : (a + b) % 2 ^ 64 = a + b := Nat.mod_eq_of_lt (by omega)
  have h2 : a % 2 ^ 64 = a := Nat.mod_eq_of_lt (by omega)
  rw [h1, h2]
  exact decide_eq_false (by omega)

/-- Bit 63 clear and nonzero for `ofNat a + ofNat b` (the `tbz` / `cbz` branches). -/
theorem ofNat_add_bits {a b : Nat} (h : a + b < 2 ^ 63) (h1 : 1 ≤ a + b) :
    (BitVec.ofNat 64 a + BitVec.ofNat 64 b).getLsbD 63 = false ∧
      (BitVec.ofNat 64 a + BitVec.ofNat 64 b == 0#64) = false := by
  rw [← BitVec.ofNat_add]
  refine ⟨?_, ?_⟩
  · rw [BitVec.getLsbD_ofNat]
    simp only [Nat.reduceLT, decide_true, Bool.true_and]
    exact Nat.testBit_lt_two_pow (by omega)
  · apply beq_false_of_ne
    intro heq
    have h1' : (BitVec.ofNat 64 (a + b)).toNat = 0 := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1'
    omega

theorem memRegion_out32_pool_stack_swap (A : RustAlloc) (out sp : BitVec 64) :
    (memRegion out 32 ∗ A.pool ∗ stackAt sp serializeStackX) =
      (A.pool ∗ (memRegion out 32 ∗ stackAt sp serializeStackX)) := by
  ac_rfl

theorem vecU8At_init_byte_432_cap (A : RustAlloc) (sp ptr c : BitVec 64) (n : Nat)
    (b0 : BitVec 8) (hc : c.toNat = n) (hpos : 1 ≤ n) (hlt : n < 2 ^ 32) (hptr : ptr ≠ 0) :
    (((sp - 432#64) ↦₆₄ c) ∗ ((sp - 424#64) ↦₆₄ ptr) ∗ ((sp - 416#64) ↦₆₄ 1#64) ∗
      A.live ptr n 1 ∗ (ptr ↦₈ b0) ∗ memRegion (ptr + 1#64) (n - 1)) ⊢
      vecU8At A (sp - 432#64) (BitVec.ofNat 64 n) ptr [b0] := by
  have e : c = BitVec.ofNat 64 n := by
    apply BitVec.eq_of_toNat_eq
    rw [hc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  subst e
  exact vecU8At_init_byte_432X A sp ptr n b0 hpos hlt hptr

/-- Side goals of the `hF2` / `hTail` applications (pc, sp, trace, registers). -/
macro "k5_side" : tactic =>
  `(tactic| first
    | (wp_norm_lhs; done)
    | (wp_norm_goal; done)
    | (simp only [wp_norm, arm64_norm, *]; done))

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
