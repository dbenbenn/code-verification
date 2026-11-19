/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Loop -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeHeap
import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Interpolate
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Proof -- shake: keep
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message`: Drop Glue and Epilogue

**Checked by Lean.**

Proves the `polys: [Option<Poly>; 16]` drop glue (`0x6c0fc..0x6c2f0`), `points_vecs` deallocation,
and register-restoration epilogue (`0x6bca0..0x6bcdc` and `0x6c2f0..0x6c2f8`) of `decoded_message`.
-/

public section

namespace CryptoVerification.SpqrV1.Poly.DecodedMessage

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Alloc CryptoVerification.CodeLayout
open CryptoVerification.LibsignalTripleRatchet.Getters CryptoVerification.LibsignalTripleRatchet.Getters.DropGlueFacts
open CryptoVerification.SpqrV1.Poly.AddChunk CryptoVerification.SpqrV1.Poly.AddChunk.AddChunkNorm
open CryptoVerification.SpqrV1.Poly.ComputeAt
open CryptoVerification.SpqrV1.Poly.LagrangeComplete

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

/-! ## Memory Region and `optPolyCacheSlotAt` Helpers -/

theorem pointsTo64_entails_memRegion8 (a w : BitVec 64) :
    (a ↦₆₄ w) ⊢ memRegion a 8 := by
  rw [ProofLib.memRegion_eight a]
  exact Entails.sepExists_intro w

theorem optPolyCacheSlot_none_entails_memRegion24 (slot : BitVec 64) :
    (slot ↦₆₄ noneCap) ∗ memRegion (slot + 8#64) 16 ⊢ memRegion slot 24 := by
  rw [show (24 : Nat) = 8 + 16 from rfl, memRegion_split slot 8 16 (by decide)]
  exact sepConj_mono_left (pointsTo64_entails_memRegion8 slot noneCap)

theorem pointsTo64_three_entails_memRegion24 (slot w0 w1 w2 : BitVec 64) :
    (slot ↦₆₄ w0) ∗ ((slot + 8#64) ↦₆₄ w1) ∗ ((slot + 16#64) ↦₆₄ w2) ⊢ memRegion slot 24 := by
  have h16 : slot + 8#64 + 8#64 = slot + 16#64 := by bv_omega
  rw [show (24 : Nat) = 8 + (8 + 8) from rfl,
    memRegion_split slot 8 (8 + 8) (by decide),
    memRegion_split (slot + 8#64) 8 8 (by decide), h16]
  exact sepConj_mono (pointsTo64_entails_memRegion8 slot w0)
    (sepConj_mono (pointsTo64_entails_memRegion8 (slot + 8#64) w1)
      (pointsTo64_entails_memRegion8 (slot + 16#64) w2))

@[local wp_norm, local arm64_norm]
theorem noneCap_slt_one : noneCap.slt 1#64 = true := rfl

attribute [local irreducible] noneCap

theorem bv64_slt_one_of_ge1_le65536 {n : Nat} (hge : 1 ≤ n) (hle : n ≤ 65536) :
    (BitVec.ofNat 64 n).slt 1#64 = false := by
  rw [Bool.eq_false_iff, ne_eq,
    slt_one_iff_eq_zero (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)]
  exact ofNat_ne_zero_of_pos (by omega) (by omega)

theorem pull_none_slot (M Pool Stk : SepProp) (slot : BitVec 64) (P : SepProp) :
    M ∗ Pool ∗ Stk ∗ ((slot ↦₆₄ noneCap) ∗ memRegion (slot + 8#64) 16) ∗ P =
      (slot ↦₆₄ noneCap) ∗ memRegion (slot + 8#64) 16 ∗ M ∗ Pool ∗ Stk ∗ P := by
  ac_rfl

theorem pull_some_slot (A : RustAlloc) (M Pool Stk : SepProp) (slot : BitVec 64) (p : Poly) (P : SepProp) :
    M ∗ Pool ∗ Stk ∗ optPolyCacheSlotAt A slot (some p) ∗ P =
      ∃∗ ptr : BitVec 64,
        ⌜1 ≤ p.coefficients.length ∧ p.coefficients.length ≤ 65536 ∧ ptr ≠ 0#64⌝ ∗
          (slot ↦₆₄ BitVec.ofNat 64 p.coefficients.length) ∗
          ((slot + 8#64) ↦₆₄ ptr) ∗
          ((slot + 16#64) ↦₆₄ BitVec.ofNat 64 p.coefficients.length) ∗
          A.live ptr (2 * p.coefficients.length) 2 ∗
          gf16SliceAt ptr p.coefficients ∗
          M ∗ Pool ∗ Stk ∗ P := by
  unfold optPolyCacheSlotAt
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
  congr 1
  funext ptr
  ac_rfl

theorem merge_prev_slot_none (sp0 slot : BitVec 64) (prev next : Nat)
    (hsum : prev + 24 = next) (hbound : next ≤ 384)
    (haddr : sp0 - 600#64 + BitVec.ofNat 64 prev = slot) (Rest : SepProp) :
    (slot ↦₆₄ noneCap) ∗ memRegion (slot + 8#64) 16 ∗
      memRegion (sp0 - 600#64) prev ∗ Rest ⊢
      memRegion (sp0 - 600#64) next ∗ Rest := by
  have heq :
      (slot ↦₆₄ noneCap) ∗ memRegion (slot + 8#64) 16 ∗
        memRegion (sp0 - 600#64) prev ∗ Rest =
      (memRegion (sp0 - 600#64) prev ∗
        ((slot ↦₆₄ noneCap) ∗ memRegion (slot + 8#64) 16)) ∗ Rest := by ac_rfl
  rw [heq]
  refine sepConj_mono_left ?_
  rw [← hsum, memRegion_split (sp0 - 600#64) prev 24 (by omega), haddr]
  exact sepConj_mono_right (optPolyCacheSlot_none_entails_memRegion24 slot)

theorem merge_prev_slot_some (sp0 slot : BitVec 64) (prev next : Nat)
    (hsum : prev + 24 = next) (hbound : next ≤ 384)
    (haddr : sp0 - 600#64 + BitVec.ofNat 64 prev = slot)
    (w0 w1 w2 : BitVec 64) (Rest : SepProp) :
    ((slot ↦₆₄ w0) ∗ ((slot + 8#64) ↦₆₄ w1) ∗ ((slot + 16#64) ↦₆₄ w2)) ∗
      (memRegion (sp0 - 600#64) prev ∗ Rest) ⊢
      memRegion (sp0 - 600#64) next ∗ Rest := by
  have heq :
      ((slot ↦₆₄ w0) ∗ ((slot + 8#64) ↦₆₄ w1) ∗ ((slot + 16#64) ↦₆₄ w2)) ∗
        (memRegion (sp0 - 600#64) prev ∗ Rest) =
      (memRegion (sp0 - 600#64) prev ∗
        ((slot ↦₆₄ w0) ∗ ((slot + 8#64) ↦₆₄ w1) ∗ ((slot + 16#64) ↦₆₄ w2))) ∗ Rest := by ac_rfl
  rw [heq]
  refine sepConj_mono_left ?_
  rw [← hsum, memRegion_split (sp0 - 600#64) prev 24 (by omega), haddr]
  exact sepConj_mono_right (pointsTo64_three_entails_memRegion24 slot w0 w1 w2)

theorem dropPolySlot_some_to_dealloc (A : RustAlloc) (slot ptr : BitVec 64) (p : Poly) (Rest : SepProp) :
    (slot ↦₆₄ BitVec.ofNat 64 p.coefficients.length) ∗
      ((slot + 8#64) ↦₆₄ ptr) ∗
      ((slot + 16#64) ↦₆₄ BitVec.ofNat 64 p.coefficients.length) ∗
      A.live ptr (2 * p.coefficients.length) 2 ∗
      gf16SliceAt ptr p.coefficients ∗ Rest ⊢
      (slot ↦₆₄ BitVec.ofNat 64 p.coefficients.length) ∗
        ((slot + 8#64) ↦₆₄ ptr) ∗
        ((slot + 16#64) ↦₆₄ BitVec.ofNat 64 p.coefficients.length) ∗
        A.live ptr (2 * p.coefficients.length) 2 ∗
        memRegion ptr (2 * p.coefficients.length) ∗ Rest := by
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))
  exact sepConj_mono_left (gf16SliceAt_to_memRegion ptr p.coefficients)

theorem bv64_lsl1_toNat_of_le65536 {n : Nat} (hle : n ≤ 65536) :
    ((BitVec.ofNat 64 n) <<< 1).toNat = 2 * n := by
  rw [bv64_lsl1_norm n, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem bv64_ofNat_ne0_of_ge1 {n : Nat} (hge : 1 ≤ n) (hle : n ≤ 65536) :
    ((BitVec.ofNat 64 n) <<< 1 == 0#64) = false := by
  rw [bv64_lsl1_norm n, beq_eq_false_iff_ne]
  intro h
  have h1 := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
  change 2 * n = 0 at h1
  omega

theorem optPolyCacheListAt_15_eq (A : RustAlloc) (sp0 : BitVec 64)
    (p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 : Option Poly) (P : SepProp) :
    optPolyCacheListAt A (sp0 - 576#64)
      [p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15] ∗ P =
      optPolyCacheSlotAt A (sp0 - 576#64) p1 ∗
      optPolyCacheSlotAt A (sp0 - 552#64) p2 ∗
      optPolyCacheSlotAt A (sp0 - 528#64) p3 ∗
      optPolyCacheSlotAt A (sp0 - 504#64) p4 ∗
      optPolyCacheSlotAt A (sp0 - 480#64) p5 ∗
      optPolyCacheSlotAt A (sp0 - 456#64) p6 ∗
      optPolyCacheSlotAt A (sp0 - 432#64) p7 ∗
      optPolyCacheSlotAt A (sp0 - 408#64) p8 ∗
      optPolyCacheSlotAt A (sp0 - 384#64) p9 ∗
      optPolyCacheSlotAt A (sp0 - 360#64) p10 ∗
      optPolyCacheSlotAt A (sp0 - 336#64) p11 ∗
      optPolyCacheSlotAt A (sp0 - 312#64) p12 ∗
      optPolyCacheSlotAt A (sp0 - 288#64) p13 ∗
      optPolyCacheSlotAt A (sp0 - 264#64) p14 ∗
      optPolyCacheSlotAt A (sp0 - 240#64) p15 ∗ P := by
  simp only [optPolyCacheListAt, vecHeaderBytes, arrayAt, arm64_norm, sepConj_emp, sepConj_assoc]

theorem list_length_16_eq {α : Type _} (xs : List α) (h : xs.length = 16) :
    ∃ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15,
      xs = [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15] :=
  match xs, h with
  | [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15], _ =>
    ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, rfl⟩

@[local wp_norm ↓, local arm64_norm ↓]
theorem sp216_add_8 (sp0 : BitVec 64) : sp0 - 216#64 + 8#64 = sp0 - 208#64 := by bv_omega
@[local wp_norm ↓, local arm64_norm ↓]
theorem sp216_add_16 (sp0 : BitVec 64) : sp0 - 216#64 + 16#64 = sp0 - 200#64 := by bv_omega

theorem memRegion24_eq_exists_three (a : BitVec 64) :
    memRegion a vecHeaderBytes =
      (∃∗ w0 : BitVec 64, a ↦₆₄ w0) ∗
      (∃∗ w1 : BitVec 64, (a + 8#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (a + 16#64) ↦₆₄ w2) := by
  have h16 : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
  rw [show vecHeaderBytes = 8 + (8 + 8) from rfl,
    memRegion_split a 8 (8 + 8) (by decide),
    memRegion_split (a + 8#64) 8 8 (by decide), h16,
    ProofLib.memRegion_eight a,
    ProofLib.memRegion_eight (a + 8#64),
    ProofLib.memRegion_eight (a + 16#64)]

theorem fold_optVecU8Of_some_nil (A : RustAlloc) (out_sret : BitVec 64) :
    (out_sret ↦₆₄ 0#64) ∗ ((out_sret + 8#64) ↦₆₄ 1#64) ∗ ((out_sret + 16#64) ↦₆₄ 0#64) ⊢
      optVecU8Of A out_sret (some []) := by
  unfold optVecU8Of vecU8 vecU8At vecHeader
  dsimp only
  apply Entails.sepExists_right 0#64
  apply Entails.sepExists_right 1#64
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_emp]
  have hpure : 0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0 :=
    ⟨by decide, by decide, by decide⟩
  rw [sepConj_comm _ ⌜_⌝]
  exact Entails.pure_right hpure (Entails.refl _)

theorem fold_optVecU8Of_some (A : RustAlloc) (out_sret out_ptr : BitVec 64)
    (outFinal : List (BitVec 8)) (n : Nat)
    (hn_ge : 1 ≤ n) (hn_le : n ≤ 2 * (16 * 65536))
    (hlen : outFinal.length = n) (hptr : out_ptr ≠ 0#64) :
    (out_sret ↦₆₄ BitVec.ofNat 64 n) ∗
      ((out_sret + 8#64) ↦₆₄ out_ptr) ∗
      ((out_sret + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗
      A.live out_ptr n 1 ∗
      (out_ptr ↦ₛ outFinal) ⊢
      optVecU8Of A out_sret (some outFinal) := by
  have hcap_ne : BitVec.ofNat 64 n ≠ 0 :=
    ofNat_ne_zero_of_pos (by omega) (by omega)
  have hcap_toNat : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold optVecU8Of vecU8 vecU8At vecHeader
  dsimp only
  apply Entails.sepExists_right (BitVec.ofNat 64 n)
  apply Entails.sepExists_right out_ptr
  simp only [hcap_ne, ↓reduceIte, hcap_toNat, hlen, Nat.sub_self, memRegion_zero, sepConj_emp]
  have hpure : n ≤ n ∧ n < 2 ^ 63 ∧ out_ptr ≠ 0 := ⟨Nat.le_refl n, by omega, hptr⟩
  rw [sepConj_comm _ (⌜_⌝ ∗ _), sepConj_assoc]
  refine Entails.pure_right hpure ?_
  exact Entails.of_eq (by ac_rfl)

/-! ## Stack Layout and Epilogue (`0x6bca0..0x6bcdc` and `0x6c2f0..0x6c2f8`) -/

/-- Saved callee-saved registers `x19..x30` at `[sp0 - 96#64 .. sp0)` (96 bytes). -/
@[expose] def savedRegsAt (sp0 : BitVec 64) (s0 : State) : SepProp :=
  ((sp0 - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
  ((sp0 - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((sp0 - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
  ((sp0 - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((sp0 - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
  ((sp0 - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((sp0 - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
  ((sp0 - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((sp0 - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
  ((sp0 - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp0 - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((sp0 - 8#64) ↦₆₄ s0.readReg64 .x19)

theorem memRegion96_eq_exists_twelve (sp0 : BitVec 64) :
    memRegion (sp0 - 96#64) 96 =
      (∃∗ v0 : BitVec 64, (sp0 - 96#64) ↦₆₄ v0) ∗
      (∃∗ v1 : BitVec 64, (sp0 - 88#64) ↦₆₄ v1) ∗
      (∃∗ v2 : BitVec 64, (sp0 - 80#64) ↦₆₄ v2) ∗
      (∃∗ v3 : BitVec 64, (sp0 - 72#64) ↦₆₄ v3) ∗
      (∃∗ v4 : BitVec 64, (sp0 - 64#64) ↦₆₄ v4) ∗
      (∃∗ v5 : BitVec 64, (sp0 - 56#64) ↦₆₄ v5) ∗
      (∃∗ v6 : BitVec 64, (sp0 - 48#64) ↦₆₄ v6) ∗
      (∃∗ v7 : BitVec 64, (sp0 - 40#64) ↦₆₄ v7) ∗
      (∃∗ v8 : BitVec 64, (sp0 - 32#64) ↦₆₄ v8) ∗
      (∃∗ v9 : BitVec 64, (sp0 - 24#64) ↦₆₄ v9) ∗
      (∃∗ v10 : BitVec 64, (sp0 - 16#64) ↦₆₄ v10) ∗
      (∃∗ v11 : BitVec 64, (sp0 - 8#64) ↦₆₄ v11) := by
  have ha1 : sp0 - 96#64 + 8#64 = sp0 - 88#64 := by bv_omega
  have ha2 : sp0 - 88#64 + 8#64 = sp0 - 80#64 := by bv_omega
  have ha3 : sp0 - 80#64 + 8#64 = sp0 - 72#64 := by bv_omega
  have ha4 : sp0 - 72#64 + 8#64 = sp0 - 64#64 := by bv_omega
  have ha5 : sp0 - 64#64 + 8#64 = sp0 - 56#64 := by bv_omega
  have ha6 : sp0 - 56#64 + 8#64 = sp0 - 48#64 := by bv_omega
  have ha7 : sp0 - 48#64 + 8#64 = sp0 - 40#64 := by bv_omega
  have ha8 : sp0 - 40#64 + 8#64 = sp0 - 32#64 := by bv_omega
  have ha9 : sp0 - 32#64 + 8#64 = sp0 - 24#64 := by bv_omega
  have ha10 : sp0 - 24#64 + 8#64 = sp0 - 16#64 := by bv_omega
  have ha11 : sp0 - 16#64 + 8#64 = sp0 - 8#64 := by bv_omega
  rw [show (96 : Nat) = 8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + 8)))))))))) from rfl,
    memRegion_split (sp0 - 96#64) 8 88 (by decide), ha1,
    memRegion_split (sp0 - 88#64) 8 80 (by decide), ha2,
    memRegion_split (sp0 - 80#64) 8 72 (by decide), ha3,
    memRegion_split (sp0 - 72#64) 8 64 (by decide), ha4,
    memRegion_split (sp0 - 64#64) 8 56 (by decide), ha5,
    memRegion_split (sp0 - 56#64) 8 48 (by decide), ha6,
    memRegion_split (sp0 - 48#64) 8 40 (by decide), ha7,
    memRegion_split (sp0 - 40#64) 8 32 (by decide), ha8,
    memRegion_split (sp0 - 32#64) 8 24 (by decide), ha9,
    memRegion_split (sp0 - 24#64) 8 16 (by decide), ha10,
    memRegion_split (sp0 - 16#64) 8 8 (by decide), ha11,
    ProofLib.memRegion_eight (sp0 - 96#64),
    ProofLib.memRegion_eight (sp0 - 88#64),
    ProofLib.memRegion_eight (sp0 - 80#64),
    ProofLib.memRegion_eight (sp0 - 72#64),
    ProofLib.memRegion_eight (sp0 - 64#64),
    ProofLib.memRegion_eight (sp0 - 56#64),
    ProofLib.memRegion_eight (sp0 - 48#64),
    ProofLib.memRegion_eight (sp0 - 40#64),
    ProofLib.memRegion_eight (sp0 - 32#64),
    ProofLib.memRegion_eight (sp0 - 24#64),
    ProofLib.memRegion_eight (sp0 - 16#64),
    ProofLib.memRegion_eight (sp0 - 8#64)]

theorem savedRegsAt_entails_memRegion96 (sp0 : BitVec 64) (s0 : State) :
    savedRegsAt sp0 s0 ⊢ memRegion (sp0 - 96#64) 96 := by
  unfold savedRegsAt
  rw [memRegion96_eq_exists_twelve sp0]
  exact sepConj_mono (Entails.sepExists_intro _)
    (sepConj_mono (Entails.sepExists_intro _)
    (sepConj_mono (Entails.sepExists_intro _)
    (sepConj_mono (Entails.sepExists_intro _)
    (sepConj_mono (Entails.sepExists_intro _)
    (sepConj_mono (Entails.sepExists_intro _)
    (sepConj_mono (Entails.sepExists_intro _)
    (sepConj_mono (Entails.sepExists_intro _)
    (sepConj_mono (Entails.sepExists_intro _)
    (sepConj_mono (Entails.sepExists_intro _)
    (sepConj_mono (Entails.sepExists_intro _)
      (Entails.sepExists_intro _)))))))))))

theorem stackAt_decodedMessage_eq (sp0 : BitVec 64) :
    stackAt sp0 decodedMessageStack =
      stackAt (sp0 - 672#64) extHookStack ∗
        memRegion (sp0 - 672#64) 576 ∗
        memRegion (sp0 - 96#64) 96 := by
  unfold stackAt decodedMessageStack extHookStack
  have h1 : sp0 - BitVec.ofNat 64 (16384 + (576 + 96)) = (sp0 - 672#64) - 16384#64 := by bv_omega
  have h2 : (sp0 - 672#64) - 16384#64 + 16384#64 = sp0 - 672#64 := by bv_omega
  have h3 : sp0 - 672#64 + 576#64 = sp0 - 96#64 := by bv_omega
  have h4 : (sp0 - 672#64) - BitVec.ofNat 64 (2 ^ 14) = (sp0 - 672#64) - 16384#64 := rfl
  rw [show (672 + 2 ^ 14 : Nat) = 16384 + (576 + 96) from rfl, h1,
    memRegion_split ((sp0 - 672#64) - 16384#64) 16384 (576 + 96) (by decide), h2,
    memRegion_split (sp0 - 672#64) 576 96 (by decide), h3, h4]
  rfl

theorem stackAt_extHook_eq_allocHook (sp : BitVec 64) :
    stackAt sp extHookStack =
      stackAt sp allocHookStack ∗ memRegion (sp - 16384#64) 12288 := by
  unfold stackAt extHookStack allocHookStack
  have h0 : sp - BitVec.ofNat 64 (12288 + 4096) = sp - 16384#64 := rfl
  have h1 : sp - 16384#64 + 12288#64 = sp - 4096#64 := by bv_omega
  rw [show (2 ^ 14 : Nat) = 12288 + 4096 from rfl, h0,
    memRegion_split (sp - 16384#64) 12288 4096 (by decide), h1, sepConj_comm]

theorem stackAt_extHook_eq_computeAt (sp : BitVec 64) :
    stackAt sp extHookStack =
      stackAt sp computeAtStack ∗ memRegion (sp - 16384#64) 12032 := by
  unfold stackAt extHookStack computeAtStack growOneStack finishGrowStack allocHookStack
  have h0 : sp - BitVec.ofNat 64 (12032 + (144 + ((4128 + 16) + 64))) = sp - 16384#64 := rfl
  have h1 : sp - 16384#64 + 12032#64 = sp - 4352#64 := by bv_omega
  rw [show (2 ^ 14 : Nat) = 12032 + (144 + ((4128 + 16) + 64)) from rfl, h0,
    memRegion_split (sp - 16384#64) 12032 (144 + ((4128 + 16) + 64)) (by decide), h1, sepConj_comm]

theorem stackAt_computeAt_eq_allocHook (sp : BitVec 64) :
    stackAt sp computeAtStack =
      stackAt sp allocHookStack ∗ memRegion (sp - 4352#64) 256 := by
  unfold stackAt computeAtStack growOneStack finishGrowStack allocHookStack
  have h1 : sp - 4352#64 + 256#64 = sp - 4096#64 := by bv_omega
  rw [show (144 + ((4128 + 16) + 64) : Nat) = 256 + 4096 from rfl,
    memRegion_split (sp - 4352#64) 256 4096 (by decide), h1, sepConj_comm]

theorem memRegion_56_8_512_entails_576 (sp0 pv_ptr : BitVec 64) :
    memRegion (sp0 - 672#64) 56 ∗ ((sp0 - 616#64) ↦₆₄ pv_ptr) ∗ memRegion (sp0 - 608#64) 512 ⊢
      memRegion (sp0 - 672#64) 576 := by
  have h1 : sp0 - 672#64 + 56#64 = sp0 - 616#64 := by bv_omega
  have h2 : sp0 - 616#64 + 8#64 = sp0 - 608#64 := by bv_omega
  rw [show (576 : Nat) = 56 + (8 + 512) from rfl,
    memRegion_split (sp0 - 672#64) 56 (8 + 512) (by decide), h1,
    memRegion_split (sp0 - 616#64) 8 512 (by decide), h2]
  exact sepConj_mono_right (sepConj_mono_left (pointsTo64_entails_memRegion8 (sp0 - 616#64) pv_ptr))

@[expose] def CalleeSavedGprsPreserved (s₀ sf : State) : Prop :=
  sf.readReg64 .x19 = s₀.readReg64 .x19 ∧
  sf.readReg64 .x20 = s₀.readReg64 .x20 ∧
  sf.readReg64 .x21 = s₀.readReg64 .x21 ∧
  sf.readReg64 .x22 = s₀.readReg64 .x22 ∧
  sf.readReg64 .x23 = s₀.readReg64 .x23 ∧
  sf.readReg64 .x24 = s₀.readReg64 .x24 ∧
  sf.readReg64 .x25 = s₀.readReg64 .x25 ∧
  sf.readReg64 .x26 = s₀.readReg64 .x26 ∧
  sf.readReg64 .x27 = s₀.readReg64 .x27 ∧
  sf.readReg64 .x28 = s₀.readReg64 .x28 ∧
  sf.readReg64 .x29 = s₀.readReg64 .x29

theorem calleeSavedPreserved_of_gprs_traceVRegs {s₀ sf : State}
    (hgprs : CalleeSavedGprsPreserved s₀ sf) (htr : traceVRegs sf = traceVRegs s₀) :
    CalleeSavedPreserved s₀ sf ∧ sf.trace = s₀.trace := by
  rcases hgprs with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29⟩
  rcases Prod.mk.inj htr with ⟨htr_tr, htr_vr⟩
  exact ⟨⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, htr_vr⟩, htr_tr⟩

theorem memRegion_48_8_entails_56 (sp0 w : BitVec 64) :
    memRegion (sp0 - 672#64) 48 ∗ ((sp0 - 624#64) ↦₆₄ w) ⊢ memRegion (sp0 - 672#64) 56 := by
  have h1 : sp0 - 672#64 + 48#64 = sp0 - 624#64 := by bv_omega
  rw [show (56 : Nat) = 48 + 8 from rfl, memRegion_split (sp0 - 672#64) 48 8 (by decide), h1]
  exact sepConj_mono_right (pointsTo64_entails_memRegion8 (sp0 - 624#64) w)

theorem memRegion_24_8_8_8_8_entails_56 (sp0 w648 w632 w624 : BitVec 64) :
    memRegion (sp0 - 672#64) 24 ∗
      ((sp0 - 648#64) ↦₆₄ w648) ∗
      memRegion (sp0 - 640#64) 8 ∗
      ((sp0 - 632#64) ↦₆₄ w632) ∗
      ((sp0 - 624#64) ↦₆₄ w624) ⊢
      memRegion (sp0 - 672#64) 56 := by
  have h1 : sp0 - 672#64 + 24#64 = sp0 - 648#64 := by bv_omega
  have h2 : sp0 - 648#64 + 8#64 = sp0 - 640#64 := by bv_omega
  have h3 : sp0 - 640#64 + 8#64 = sp0 - 632#64 := by bv_omega
  have h4 : sp0 - 632#64 + 8#64 = sp0 - 624#64 := by bv_omega
  rw [show (56 : Nat) = 24 + (8 + (8 + (8 + 8))) from rfl,
    memRegion_split (sp0 - 672#64) 24 32 (by decide), h1,
    memRegion_split (sp0 - 648#64) 8 24 (by decide), h2,
    memRegion_split (sp0 - 640#64) 8 16 (by decide), h3,
    memRegion_split (sp0 - 632#64) 8 8 (by decide), h4]
  exact sepConj_mono_right
    (sepConj_mono (pointsTo64_entails_memRegion8 (sp0 - 648#64) w648)
      (sepConj_mono_right
        (sepConj_mono (pointsTo64_entails_memRegion8 (sp0 - 632#64) w632)
          (pointsTo64_entails_memRegion8 (sp0 - 624#64) w624))))

theorem memRegion_8_504_entails_512 (sp0 w608 : BitVec 64) :
    ((sp0 - 608#64) ↦₆₄ w608) ∗ memRegion (sp0 - 600#64) 504 ⊢
      memRegion (sp0 - 608#64) 512 := by
  have h1 : sp0 - 608#64 + 8#64 = sp0 - 600#64 := by bv_omega
  rw [show (512 : Nat) = 8 + 504 from rfl, memRegion_split (sp0 - 608#64) 8 504 (by decide), h1]
  exact sepConj_mono_left (pointsTo64_entails_memRegion8 (sp0 - 608#64) w608)

end CryptoVerification.SpqrV1.Poly.DecodedMessage
