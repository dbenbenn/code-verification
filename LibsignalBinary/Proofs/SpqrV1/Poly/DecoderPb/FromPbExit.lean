/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbOuter -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbOuter -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
public import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common -- proof-setup: allow-public-import
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::encoding::polynomial::PolyDecoder>::from_pb`: Outer Loop Induction and Error Exits

Proves outer-loop induction (`+204 → +876 / +740`), shared epilogue tails (`+1244`, `+828`, `+820`,
`+1236`), the `Vec<u8>` drop loop (`+776 → +820`), and error exits A (`+712`) and B (`+740`).
-/

public section

namespace CryptoVerification.SpqrV1.Poly.DecoderPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Getters.DropGlueFacts
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem align_pre_wpp {prog : Program} {t : BitVec 64} {s : State} {P1 P2 : SepProp}
    {Q R : State → SepProp → Prop} (hwp : SepWPp prog t s P2 Q R) (h : P1 = P2) :
    SepWPp prog t s P1 Q R := h ▸ hwp

theorem align_pre_wp {prog : Program} {t : BitVec 64} {s : State} {P1 P2 : SepProp}
    {post : State → SepProp → Prop} (hwp : SepWP prog t s P2 post) (h : P1 = P2) :
    SepWP prog t s P1 post := h ▸ hwp

theorem replace_sub_entails {A B P Q : SepProp} (h : A ⊢ B) (C : SepProp)
    (hP : P = A ∗ C) (hQ : B ∗ C = Q) : P ⊢ Q := by
  rw [hP, ← hQ]; exact sepConj_mono_left h

/-! ## Outer Loop Induction (`+204 -> +876` or `+740`) -/

/-- Core stack budget of `from_pb` (`544 + dropGluePoly16Stack = 4672` bytes). -/
abbrev fromPbCoreStack : Nat := 544 + dropGluePoly16Stack

/-- Saved callee-saved registers at `[fsp + 448 .. fsp + 544)` (`= [s0.sp - 96 .. s0.sp)`). -/
@[expose] def savedRegsAt (fsp : BitVec 64) (s0 : State) : SepProp :=
  ((fsp + 448#64) ↦₆₄ s0.readReg64 .x29) ∗
  ((fsp + 456#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((fsp + 464#64) ↦₆₄ s0.readReg64 .x28) ∗
  ((fsp + 472#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((fsp + 480#64) ↦₆₄ s0.readReg64 .x26) ∗
  ((fsp + 488#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((fsp + 496#64) ↦₆₄ s0.readReg64 .x24) ∗
  ((fsp + 504#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((fsp + 512#64) ↦₆₄ s0.readReg64 .x22) ∗
  ((fsp + 520#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((fsp + 528#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((fsp + 536#64) ↦₆₄ s0.readReg64 .x19)

@[local arm64_norm, local wp_norm] theorem fsp_448_add_8 (fsp : BitVec 64) : (fsp + 448#64) + 8#64 = fsp + 456#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem fsp_448_add_16 (fsp : BitVec 64) : (fsp + 448#64) + 16#64 = fsp + 464#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem fsp_448_add_24 (fsp : BitVec 64) : (fsp + 448#64) + 24#64 = fsp + 472#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem fsp_448_add_32 (fsp : BitVec 64) : (fsp + 448#64) + 32#64 = fsp + 480#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem fsp_448_add_40 (fsp : BitVec 64) : (fsp + 448#64) + 40#64 = fsp + 488#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem fsp_448_add_48 (fsp : BitVec 64) : (fsp + 448#64) + 48#64 = fsp + 496#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem fsp_448_add_56 (fsp : BitVec 64) : (fsp + 448#64) + 56#64 = fsp + 504#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem fsp_448_add_64 (fsp : BitVec 64) : (fsp + 448#64) + 64#64 = fsp + 512#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem fsp_448_add_72 (fsp : BitVec 64) : (fsp + 448#64) + 72#64 = fsp + 520#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem fsp_448_add_80 (fsp : BitVec 64) : (fsp + 448#64) + 80#64 = fsp + 528#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem fsp_448_add_88 (fsp : BitVec 64) : (fsp + 448#64) + 88#64 = fsp + 536#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem fsp_448_add_96 (fsp : BitVec 64) : (fsp + 448#64) + 96#64 = fsp + 544#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem fsp_456_add_8 (fsp : BitVec 64) : (fsp + 456#64) + 8#64 = fsp + 464#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem fsp_464_add_8 (fsp : BitVec 64) : (fsp + 464#64) + 8#64 = fsp + 472#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem fsp_472_add_8 (fsp : BitVec 64) : (fsp + 472#64) + 8#64 = fsp + 480#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem fsp_480_add_8 (fsp : BitVec 64) : (fsp + 480#64) + 8#64 = fsp + 488#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem fsp_488_add_8 (fsp : BitVec 64) : (fsp + 488#64) + 8#64 = fsp + 496#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem fsp_496_add_8 (fsp : BitVec 64) : (fsp + 496#64) + 8#64 = fsp + 504#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem fsp_504_add_8 (fsp : BitVec 64) : (fsp + 504#64) + 8#64 = fsp + 512#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem fsp_512_add_8 (fsp : BitVec 64) : (fsp + 512#64) + 8#64 = fsp + 520#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem fsp_520_add_8 (fsp : BitVec 64) : (fsp + 520#64) + 8#64 = fsp + 528#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem fsp_528_add_8 (fsp : BitVec 64) : (fsp + 528#64) + 8#64 = fsp + 536#64 := by bv_omega

theorem savedRegsAt_entails_memRegion_96 (fsp : BitVec 64) (s0 : State) :
    savedRegsAt fsp s0 ⊢ memRegion (fsp + 448#64) 96 := by
  rw [show (96 : Nat) = 8 * 12 by rfl, ProofLib.memRegion_cells (fsp + 448#64) 12 (by decide)]
  simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
    fsp_448_add_8, fsp_456_add_8, fsp_464_add_8, fsp_472_add_8, fsp_480_add_8,
    fsp_488_add_8, fsp_496_add_8, fsp_504_add_8, fsp_512_add_8, fsp_520_add_8,
    fsp_528_add_8, ← sepExists_sepConj_left]
  unfold savedRegsAt
  exact sepConj_mono (Entails.sepExists_right _ (Entails.refl _)) (sepConj_mono (Entails.sepExists_right _ (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right _ (Entails.refl _)) (sepConj_mono (Entails.sepExists_right _ (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right _ (Entails.refl _)) (sepConj_mono (Entails.sepExists_right _ (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right _ (Entails.refl _)) (sepConj_mono (Entails.sepExists_right _ (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right _ (Entails.refl _)) (sepConj_mono (Entails.sepExists_right _ (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right _ (Entails.refl _)) (Entails.sepExists_right _ (Entails.refl _))))))))))))

theorem stackAt_fromPbCoreStack_split (sp : BitVec 64) :
    stackAt sp fromPbCoreStack =
      stackAt (sp - 544#64) dropGluePoly16Stack ∗
        memRegion (sp - 544#64) 448 ∗
        memRegion ((sp - 544#64) + 448#64) 96 := by
  have h1 : fromPbCoreStack = dropGluePoly16Stack + 544 := by decide
  rw [h1]
  simp only [stackAt]
  rw [ProofLib.memRegion_split _ dropGluePoly16Stack 544 (by decide)]
  have e1 : sp - BitVec.ofNat 64 (dropGluePoly16Stack + 544) =
      sp - 544#64 - BitVec.ofNat 64 dropGluePoly16Stack := by
    dsimp only [dropGluePoly16Stack, dropStack32, allocHookStack]
    bv_omega
  have e2 : sp - BitVec.ofNat 64 (dropGluePoly16Stack + 544) + BitVec.ofNat 64 dropGluePoly16Stack =
      sp - 544#64 := by
    dsimp only [dropGluePoly16Stack, dropStack32, allocHookStack]
    bv_omega
  rw [e2, e1, show (544 : Nat) = 448 + 96 by rfl,
      ProofLib.memRegion_split (sp - 544#64) 448 96 (by decide)]

theorem savedRegsAt_restore_fromPbCoreStack (sp fsp : BitVec 64) (hfsp : fsp = sp - 544#64) (s0 : State) :
    savedRegsAt fsp s0 ∗ memRegion fsp 448 ∗ stackAt fsp dropGluePoly16Stack ⊢
      stackAt sp fromPbCoreStack := by
  rw [hfsp, stackAt_fromPbCoreStack_split sp]
  refine Entails.trans (sepConj_mono_left (savedRegsAt_entails_memRegion_96 (sp - 544#64) s0)) ?_
  exact Entails.of_eq (by ac_rfl)

theorem stackAt_fromPbCoreStack_split_bottom_allocHook (sp : BitVec 64) :
    stackAt sp fromPbCoreStack =
      memRegion (sp - 4672#64) 576 ∗ stackAt sp allocHookStack := by
  have h : fromPbCoreStack = allocHookStack + 576 := by decide
  rw [h]
  exact stackAt_split_bottom sp allocHookStack 576 (by decide)

theorem fromPb_stackAt_dropGluePoly16_split_bottom (sp : BitVec 64) :
    stackAt sp dropGluePoly16Stack =
      memRegion (sp - 4128#64) 32 ∗ stackAt sp allocHookStack :=
  stackAt_split_bottom sp allocHookStack 32 (by decide)

/-- Conditional deallocation resource for the outer `Vec<Vec<u8>>` buffer (`sz = 24`, `align = 8`). -/
@[expose] def vecVecU8BufDealloc (A : RustAlloc) (cap ptr : BitVec 64) : SepProp :=
  if (cap == 0#64) = true then emp
  else A.live ptr (cap.toNat * 24) 8 ∗ memRegion ptr (cap.toNat * 24)

theorem vecVecU8At_expose (A : RustAlloc) (pbA : BitVec 64) (bss : List (List (BitVec 8))) :
    vecVecU8At A pbA bss ⊢
      ∃∗ cap_pts : BitVec 64, ∃∗ ptsPtr : BitVec 64,
        ⌜bss.length ≤ cap_pts.toNat ∧ cap_pts.toNat * 24 < 2 ^ 63 ∧
          bss.length * 24 < 2 ^ 63 ∧ ptsPtr ≠ 0⌝ ∗
        (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
        ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 bss.length) ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr bss ∗
        (if cap_pts = 0 then emp
          else A.live ptsPtr (cap_pts.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (bss.length * 24)) ((cap_pts.toNat - bss.length) * 24)) := by
  unfold vecVecU8At vecOf
  apply Entails.sepExists_elim; intro cap_pts
  apply Entails.sepExists_elim; intro ptsPtr
  refine Entails.sepExists_right cap_pts (Entails.sepExists_right ptsPtr ?_)
  refine Entails.trans (DropGlueFacts.vecAt_expose_loop A 24 8 (fun bs addr => vecU8 A addr bs) pbA cap_pts ptsPtr bss) ?_
  apply Entails.pure_left; rintro ⟨hle, hcap_lt, hlen_lt, hptr⟩
  refine Entails.pure_right ⟨hle, hcap_lt, hlen_lt, hptr⟩ ?_
  exact Entails.of_eq (by ac_rfl)

theorem pbA_rejoin_40 (pbA cap_pts ptsPtr len_pts : BitVec 64) :
    (pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ ((pbA + 16#64) ↦₆₄ len_pts) ∗
      memRegion (pbA + 24#64) 16 ⊢
    memRegion pbA 40 := by
  have h1 := DropGlueFacts.header_cells_entails_memRegion_24 pbA cap_pts ptsPtr
  have h2 : ((pbA + 16#64) ↦₆₄ len_pts) ⊢ memRegion (pbA + 16#64) 8 :=
    ProofLib.pointsTo64_entails_memRegion (pbA + 16#64) len_pts
  rw [show (40 : Nat) = 24 + 16 by rfl, ProofLib.memRegion_split pbA 24 16 (by decide)]
  refine Entails.trans (Q :=
    ((pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ memRegion (pbA + 16#64) 8) ∗
      memRegion (pbA + 24#64) 16) ?_ (sepConj_mono_left h1)
  exact replace_sub_entails h2
    ((pbA ↦₆₄ cap_pts) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗ memRegion (pbA + 24#64) 16)
    (by ac_rfl) (by ac_rfl)

theorem pbA_tail_entails_memRegion_16 (pbA : BitVec 64) (ptsNeeded polys : BitVec 32) (isComplete : BitVec 8) :
    ((pbA + 24#64) ↦₃₂ ptsNeeded) ∗ ((pbA + 28#64) ↦₃₂ polys) ∗
      ((pbA + 32#64) ↦₈ isComplete) ∗ memRegion (pbA + 33#64) 7 ⊢
    memRegion (pbA + 24#64) 16 := by
  have h28 : (pbA + 24#64) + 4#64 = pbA + 28#64 := by bv_omega
  have h32 : (pbA + 28#64) + 4#64 = pbA + 32#64 := by bv_omega
  have h33 : (pbA + 32#64) + 1#64 = pbA + 33#64 := by bv_omega
  rw [show (16 : Nat) = 4 + (4 + (1 + 7)) by rfl,
      ProofLib.memRegion_split (pbA + 24#64) 4 12 (by decide), h28,
      ProofLib.memRegion_split (pbA + 28#64) 4 8 (by decide), h32,
      ProofLib.memRegion_split (pbA + 32#64) 1 7 (by decide), h33]
  exact sepConj_mono (ProofLib.pointsTo32_entails_memRegion (pbA + 24#64) ptsNeeded)
    (sepConj_mono (ProofLib.pointsTo32_entails_memRegion (pbA + 28#64) polys)
      (sepConj_mono_left (ProofLib.pointsTo8_entails_memRegion (pbA + 32#64) isComplete)))

theorem memRegion_400_split_err (out : BitVec 64) :
    memRegion out 400 =
      (∃∗ d0 : BitVec 64, out ↦₆₄ d0) ∗
      (∃∗ b8 : BitVec 8, (out + 8#64) ↦₈ b8) ∗
      memRegion (out + 9#64) 391 := by
  have h9 : (out + 8#64) + 1#64 = out + 9#64 := by bv_omega
  rw [show (400 : Nat) = 8 + (1 + 391) by rfl,
      ProofLib.memRegion_split out 8 392 (by decide),
      ProofLib.memRegion_split (out + 8#64) 1 391 (by decide), h9,
      ProofLib.memRegion_eight, ProofLib.memRegion_one]

/-! ## Shared Epilogue Tails (`+1244 -> s0.lr`, `+828 -> s0.lr`, `+820 -> s0.lr`, `+1236 -> s0.lr`) -/

@[local arm64_norm, local wp_norm]
theorem cap_add_lsl1_lsl3_toNat {cap : BitVec 64} (h : cap.toNat * 24 < 2 ^ 63) :
    ((cap + (cap <<< 1#64)) <<< 3#64).toNat = cap.toNat * 24 := by
  have h1 : cap <<< 1#64 = cap + cap := by bv_bits
  have h2 (x : BitVec 64) : x <<< 3#64 = (x + x) + (x + x) + ((x + x) + (x + x)) := by bv_bits
  rw [h2, h1]
  bv_omega

@[local arm64_norm, local wp_norm]
theorem cap_add_lsl1_ubfm_toNat {cap : BitVec 64} (h : cap.toNat * 24 < 2 ^ 63) :
    (BitVec.setWidth 64 (BitVec.extractLsb' 0 61 (cap + (cap <<< 1#64))) <<< 3#64).toNat =
      cap.toNat * 24 := by
  have hex : BitVec.setWidth 64 (BitVec.extractLsb' 0 61 (cap + (cap <<< 1#64))) <<< 3#64 =
      (cap + (cap <<< 1#64)) <<< 3#64 := by bv_bits
  rw [hex]
  exact cap_add_lsl1_lsl3_toNat h

@[local arm64_norm, local wp_norm]
theorem cur_add8_sub8 (cur : BitVec 64) :
    (cur + 8#64) + 18446744073709551608#64 = cur := by bv_omega

@[local arm64_norm, local wp_norm]
theorem cur_add8_add24 (cur : BitVec 64) :
    (cur + 8#64) + 24#64 = (cur + 24#64) + 8#64 := by bv_omega

theorem ofNat_succ_sub_one_eq (n : Nat) :
    BitVec.ofNat 64 (n + 1) - 1#64 = BitVec.ofNat 64 n := by
  rw [BitVec.ofNat_add, BitVec.add_sub_cancel]

theorem fsp_rejoin_448 (fsp out pbA ptsPtr w416 w424 w432 : BitVec 64) :
    memRegion fsp 8 ∗
      ((fsp + 8#64) ↦₆₄ out) ∗ ((fsp + 16#64) ↦₆₄ pbA) ∗ ((fsp + 24#64) ↦₆₄ ptsPtr) ∗
      memRegion (fsp + 32#64) 384 ∗
      ((fsp + 416#64) ↦₆₄ w416) ∗ ((fsp + 424#64) ↦₆₄ w424) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
      memRegion (fsp + 440#64) 8 ⊢
    memRegion fsp 448 := by
  have h1 := ProofLib.pointsTo64_entails_memRegion (fsp + 8#64) out
  have h2 := ProofLib.pointsTo64_entails_memRegion (fsp + 16#64) pbA
  have h3 := ProofLib.pointsTo64_entails_memRegion (fsp + 24#64) ptsPtr
  have h4 := ProofLib.pointsTo64_entails_memRegion (fsp + 416#64) w416
  have h5 := ProofLib.pointsTo64_entails_memRegion (fsp + 424#64) w424
  have h6 := ProofLib.pointsTo64_entails_memRegion (fsp + 432#64) w432
  have ha16 : (fsp + 8#64) + 8#64 = fsp + 16#64 := by bv_omega
  have ha24 : (fsp + 16#64) + 8#64 = fsp + 24#64 := by bv_omega
  have ha32 : (fsp + 24#64) + 8#64 = fsp + 32#64 := by bv_omega
  have ha416 : (fsp + 32#64) + 384#64 = fsp + 416#64 := by bv_omega
  have ha424 : (fsp + 416#64) + 8#64 = fsp + 424#64 := by bv_omega
  have ha432 : (fsp + 424#64) + 8#64 = fsp + 432#64 := by bv_omega
  have ha440 : (fsp + 432#64) + 8#64 = fsp + 440#64 := by bv_omega
  rw [show (448 : Nat) = 8 + (8 + (8 + (8 + (384 + (8 + (8 + (8 + 8))))))) by rfl,
      ProofLib.memRegion_split fsp 8 440 (by decide),
      ProofLib.memRegion_split (fsp + 8#64) 8 432 (by decide), ha16,
      ProofLib.memRegion_split (fsp + 16#64) 8 424 (by decide), ha24,
      ProofLib.memRegion_split (fsp + 24#64) 8 416 (by decide), ha32,
      ProofLib.memRegion_split (fsp + 32#64) 384 32 (by decide), ha416,
      ProofLib.memRegion_split (fsp + 416#64) 8 24 (by decide), ha424,
      ProofLib.memRegion_split (fsp + 424#64) 8 16 (by decide), ha432,
      ProofLib.memRegion_split (fsp + 432#64) 8 8 (by decide), ha440]
  exact sepConj_mono_right (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3
    (sepConj_mono_right (sepConj_mono h4 (sepConj_mono h5 (sepConj_mono_left h6)))))))

end CryptoVerification.SpqrV1.Poly.DecoderPb
