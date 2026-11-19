/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.Defs
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# Basic-Block Step Lemmas for `spqr::init_inner` (`0x532dc..0x5349c`, 112 instructions)

**Checked by Lean.**

Proves stack-frame layout helpers, the `.v0` path, `.v1` prologue/epilogue, post-`Authenticator::new`
state construction, and `auth_key` slice-clone basic blocks for `spqr::init_inner`.
-/

public section

namespace CryptoVerification.SpqrV1.Top.InitInner

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb
open CryptoVerification.SpqrV1.Poly.DecoderPb
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  bv_sub_sub_lit' bv_add_add_lit'

/-! ## 1. Stack Frame and Representation Helpers -/

/-- Callee-saved register save area at `[s0.sp - 48 .. s0.sp)` (`48` bytes = 6 words). -/
@[expose] def initInnerSavedCells (s0 : State) : SepProp :=
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x29) ∗
  ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x28) ∗
  ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)

theorem initInnerSavedCells_entails_memRegion (s0 : State) :
    initInnerSavedCells s0 ⊢ memRegion (s0.sp - 48#64) 48 := by
  unfold initInnerSavedCells
  rw [ProofLib.memRegion_cells (s0.sp - 48#64) 6 (by decide)]
  cells_unfold
  refine Entails.sepExists_right (s0.readReg64 .x29)
    (Entails.sepExists_right (s0.readReg64 .x30)
      (Entails.sepExists_right (s0.readReg64 .x28)
        (Entails.sepExists_right (s0.readReg64 .x21)
          (Entails.sepExists_right (s0.readReg64 .x20)
            (Entails.sepExists_right (s0.readReg64 .x19) ?_)))))
  exact Entails.of_eq (by simp only [arm64_norm])

theorem stackAt_initInner_split (sp : BitVec 64) :
    stackAt sp initInnerStack =
      stackAt (sp - 1040#64) authNewStackX ∗
      memRegion (sp - 1040#64) 992 ∗
      cells (sp - 48#64) 6 := by
  change memRegion (sp - 17680#64) 17680 =
    memRegion ((sp - 1040#64) - 16640#64) 16640 ∗
    memRegion (sp - 1040#64) 992 ∗
    cells (sp - 48#64) 6
  have hsub : (sp - 1040#64) - 16640#64 = sp - 17680#64 := by bv_omega
  rw [hsub,
      ProofLib.memRegion_split' (b := sp - 17680#64) (n := 16640) (k := 1040)
        (b' := sp - 1040#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 1040#64) (n := 992) (k := 48)
        (b' := sp - 48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_cells (sp - 48#64) 6 (by decide)]

theorem stack_restore_initInner (s0 : State) :
    stackAt (s0.sp - 1040#64) authNewStackX ∗
    memRegion (s0.sp - 1040#64) 992 ∗
    initInnerSavedCells s0 ⊢
    stackAt s0.sp initInnerStack := by
  rw [stackAt_initInner_split s0.sp, ← ProofLib.memRegion_cells (s0.sp - 48#64) 6 (by decide)]
  exact sepConj_mono_right (sepConj_mono_right (initInnerSavedCells_entails_memRegion s0))

theorem memRegion_out_224_split_8 (out : BitVec 64) :
    memRegion out optProtoInnerStateSize =
      (∃∗ w0 : BitVec 64, out ↦₆₄ w0) ∗ memRegion (out + 8#64) 216 := by
  change memRegion out 224 = (∃∗ w0 : BitVec 64, out ↦₆₄ w0) ∗ memRegion (out + 8#64) 216
  rw [ProofLib.memRegion_split' (b := out) (n := 8) (k := 216)
        (b' := out + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_cells out 1 (by decide)]
  simp only [cells, sepConj_emp]

theorem vecU8_nil_of_cells (A : RustAlloc) (v : BitVec 64) :
    (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ⊢
      vecU8 A v [] := by
  refine Entails.trans ?_ (vecU8_of_header_payload A v 0#64 1#64 [])
  unfold vecU8Payload
  have hite :
      (if (0#64 : BitVec 64) = 0#64 then (emp : SepProp)
       else A.live 1#64 (0#64 : BitVec 64).toNat 1 ∗ (1#64 ↦ₛ ([] : Bytes)) ∗
         memRegion (1#64 + BitVec.ofNat 64 ([] : Bytes).length) ((0#64 : BitVec 64).toNat - ([] : Bytes).length)) =
      emp := rfl
  rw [hite, sepConj_emp]
  dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat]
  refine Entails.trans ?_ (Entails.of_eq (show
    ⌜0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ 1#64 ≠ 0#64⌝ ∗
    ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64)) = _ by ac_rfl))
  exact Entails.pure_right
    (φ := 0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ 1#64 ≠ 0#64)
    (by decide) (Entails.refl _)

theorem vecU8_nonempty_of_cells (A : RustAlloc) (v ptr : BitVec 64) (bs : Bytes)
    (hpos : 0 < bs.length) (hlt : bs.length < 2 ^ 63) (hptr : ptr ≠ 0#64) :
    (v ↦₆₄ BitVec.ofNat 64 bs.length) ∗
    ((v + 8#64) ↦₆₄ ptr) ∗
    ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
    A.live ptr bs.length 1 ∗
    (ptr ↦ₛ bs) ⊢
      vecU8 A v bs := by
  have htoNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hne : BitVec.ofNat 64 bs.length ≠ 0#64 := by
    intro h
    have h1 := congrArg BitVec.toNat h
    rw [htoNat] at h1
    change bs.length = 0 at h1
    omega
  refine Entails.trans ?_ (vecU8_of_header_payload A v (BitVec.ofNat 64 bs.length) ptr bs)
  unfold vecU8Payload
  have hite :
      (if BitVec.ofNat 64 bs.length = 0#64 then (emp : SepProp)
       else A.live ptr (BitVec.ofNat 64 bs.length).toNat 1 ∗ (ptr ↦ₛ bs) ∗
         memRegion (ptr + BitVec.ofNat 64 bs.length) ((BitVec.ofNat 64 bs.length).toNat - bs.length)) =
      (A.live ptr bs.length 1 ∗ (ptr ↦ₛ bs)) := by
    rw [ite_eq_right_iff.mpr (fun h => False.elim (hne h)), htoNat, Nat.sub_self,
        ProofLib.memRegion_zero, sepConj_emp]
  rw [hite, htoNat]
  refine Entails.trans ?_ (Entails.of_eq (show
    ⌜bs.length ≤ bs.length ∧ bs.length < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
    ((v ↦₆₄ BitVec.ofNat 64 bs.length) ∗
     ((v + 8#64) ↦₆₄ ptr) ∗
     ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
     A.live ptr bs.length 1 ∗
     (ptr ↦ₛ bs)) = _ by ac_rfl))
  exact Entails.pure_right
    (φ := bs.length ≤ bs.length ∧ bs.length < 2 ^ 63 ∧ ptr ≠ 0#64)
    ⟨Nat.le_refl _, hlt, hptr⟩ (Entails.refl _)

theorem sortedSetPtOf_withCapacity_zero (A : RustAlloc) (v : BitVec 64) :
    ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 2#64) ∗ ((v + 16#64) ↦₆₄ 0#64)) ⊢
      sortedSetPtOf A v (SortedSetPt.withCapacity 0) := by
  unfold sortedSetPtOf vecOf vecAt vecHeader vecBuf
  refine Entails.sepExists_right 0#64 (Entails.sepExists_right 2#64 ?_)
  have hite :
      (if (0#64 : BitVec 64) = 0#64 then (emp : SepProp)
       else
         A.live (2#64) ((0#64 : BitVec 64).toNat * ptStride) ptAlign ∗
           arrayAt ptAt ptStride 2#64 [] ∗
             memRegion (2#64 + BitVec.ofNat 64 (0 * ptStride)) (((0#64 : BitVec 64).toNat - 0) * ptStride)) =
      emp := rfl
  dsimp only [SortedSetPt.withCapacity, List.length_nil, BitVec.ofNat_eq_ofNat]
  rw [hite, sepConj_comm _ (_ ∗ emp), sepConj_emp]
  exact Entails.pure_right
    (φ := 0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * ptStride < 2 ^ 63 ∧ 2#64 ≠ 0#64)
    (by decide) (Entails.refl _)

/-- `n` consecutive 24-byte `(0, 2, 0)` `SortedSet<Pt>` headers starting at `base`. -/
@[expose] def emptySortedSetPtCells : Nat → BitVec 64 → SepProp
  | 0, _ => emp
  | n + 1, base =>
    ((base ↦₆₄ 0#64) ∗ ((base + 8#64) ↦₆₄ 2#64) ∗ ((base + 16#64) ↦₆₄ 0#64)) ∗
      emptySortedSetPtCells n (base + 24#64)

theorem emptySortedSetPtCells_entails (A : RustAlloc) :
    ∀ (n : Nat) (base : BitVec 64),
      emptySortedSetPtCells n base ⊢
        sortedSetPtListOf A base (List.replicate n (SortedSetPt.withCapacity 0))
  | 0, _ => Entails.refl emp
  | n + 1, base =>
    sepConj_mono (sortedSetPtOf_withCapacity_zero A base)
      (emptySortedSetPtCells_entails A n (base + 24#64))

theorem polyDecoderAt_initHdrDecoder (A : RustAlloc) (a : BitVec 64) :
    emptySortedSetPtCells 16 a ∗
      ((a + 384#64) ↦₆₄ 48#64) ∗
      ((a + 392#64) ↦₈ 0#8) ∗
      memRegion (a + 393#64) 7 ⊢
      polyDecoderAt A a initHdrDecoder := by
  unfold polyDecoderAt polyDecoderPtsNeededOff polyDecoderIsCompleteOff
    polyDecoderPadOff polyDecoderPadSize boolByte
  dsimp only [initHdrDecoder, BitVec.ofNat_eq_ofNat]
  refine Entails.pure_right
    (φ := (List.replicate 16 (SortedSetPt.withCapacity 0)).length = NUM_POLYS ∧ 48 < 2 ^ 64)
    (by decide) ?_
  refine Entails.trans
    (sepConj_mono_left (emptySortedSetPtCells_entails A 16 a)) ?_
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.Top.InitInner
