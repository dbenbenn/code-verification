/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Loop -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Interpolate
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Proof
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message`: Full Inlined `lagrange_interpolate`

Completes the cache-miss allocation, `lagrange_interpolate_prepare` call, and `i = 0` steps to
assemble `lagrangeInterpolate_inlined_wpp` (`0x6be14..0x6c084`).
-/

public section

namespace CryptoVerification.SpqrV1.Poly.DecodedMessage

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.LagrangePrepare (lagrangePrepareName LagrangePrepareArgs lagrangePreparePure lagrangePreparePure_length lagrangePrepareStack polyOf_eq)
open CryptoVerification.SpqrV1.Poly.LagrangeComplete
open CryptoVerification.SpqrV1.Poly.ComputeAt

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

@[local wp_norm, local arm64_norm]
theorem bv64_lsl1_norm' (n : Nat) :
    (BitVec.ofNat 64 n) <<< 1 = BitVec.ofNat 64 (2 * n) :=
  bv64_lsl1_norm n

@[local wp_norm, local arm64_norm]
theorem bv64_lsl4_norm' (n : Nat) :
    (BitVec.ofNat 64 n) <<< 4 = BitVec.ofNat 64 (16 * n) :=
  bv64_lsl4_norm n

@[local wp_norm, local arm64_norm]
theorem bv64_add1_norm' (n : Nat) :
    BitVec.ofNat 64 n + 1#64 = BitVec.ofNat 64 (n + 1) :=
  bv64_add1_norm n

@[local arm64_norm, local wp_norm]
theorem umaddl_24_ofNat' (base : BitVec 64) (i : Nat) :
    base + ((BitVec.ofNat 64 i).setWidth 32).zeroExtend 64 * 24#64 =
      base + BitVec.ofNat 64 (24 * (i % 4294967296)) :=
  umaddl_24_ofNat base i

theorem gf16SliceAt_split_first' (ptr : BitVec 64) (cs : List GF16) (h : 1 ≤ cs.length) :
    gf16SliceAt ptr cs =
      gf16At (cs[0]'(by omega)) ptr ∗ gf16SliceAt (ptr + 2#64) (cs.drop 1) := by
  cases cs with
  | nil => simp at h
  | cons c rest => rfl

theorem lagrangeInterpolateTotal_coeffs_eq (pts_slice : List Pt) (hpos : 1 ≤ pts_slice.length) :
    (lagrangeInterpolateTotal pts_slice).coefficients =
      lagrangeInterpolateLoopTotal (lagrangePreparePure pts_slice) pts_slice 1 (pts_slice.length - 1)
        ((lagrangeCompletePure (lagrangePreparePure pts_slice) pts_slice 0).coefficients.drop 1) := by
  rw [lagrangeInterpolateTotal_of_pos hpos]

theorem stackAt_prepare_eq_alloc (sp : BitVec 64) :
    stackAt sp lagrangePrepareStack =
      memRegion (sp - 4304#64) 208 ∗
        stackAt sp allocHookStack := by
  show stackAt sp (208 + allocHookStack) = _
  rw [Nat.add_comm 208 allocHookStack]
  exact ProofLib.stackAt_split_bottom sp allocHookStack 208 (by decide)

theorem stackAt_alloc_eq_complete (sp : BitVec 64) :
    stackAt sp allocHookStack =
      memRegion (sp - 4096#64) 3664 ∗
        stackAt sp lagrangeCompleteStack := by
  show stackAt sp (lagrangeCompleteStack + 3664) = _
  exact ProofLib.stackAt_split_bottom sp lagrangeCompleteStack 3664 (by decide)

theorem allocFailedIn_of_trace_eq' {s0 sf : State}
    (ht : sf.trace = s0.trace ++ [allocFailedEvent]) :
    allocFailedIn s0 sf := by
  unfold allocFailedIn
  rw [ht, List.drop_left]
  exact List.Mem.head []

theorem pull_pure_after_two' (P1 P2 : SepProp) (φ : Prop) (Rest : SepProp) :
    P1 ∗ P2 ∗ ⌜φ⌝ ∗ Rest = ⌜φ⌝ ∗ P1 ∗ P2 ∗ Rest := by
  ac_rfl

theorem alloc_post_pos' {P1 P2 Rest : SepProp} {x0 : BitVec 64} {φ : Prop} {Q : SepProp}
    (h0 : x0 = 0#64) :
    P1 ∗ P2 ∗ (if x0 = 0 then ⌜φ⌝ else Q) ∗ Rest = ⌜φ⌝ ∗ P1 ∗ P2 ∗ Rest := by
  have h0' : x0 = 0 := h0
  simp only [h0', ↓reduceIte]
  exact pull_pure_after_two' P1 P2 φ Rest

theorem alloc_post_neg' {P1 P2 Rest : SepProp} {x0 : BitVec 64} {φ ψ : Prop} {Q : SepProp}
    (h0 : x0 ≠ 0#64) :
    P1 ∗ P2 ∗ (if x0 = 0 then ⌜φ⌝ else ⌜ψ⌝ ∗ Q) ∗ Rest = ⌜ψ⌝ ∗ P1 ∗ P2 ∗ Q ∗ Rest := by
  have h0' : x0 ≠ 0 := h0
  simp only [h0', ↓reduceIte]
  rw [sepConj_assoc ⌜ψ⌝ Q Rest]
  exact pull_pure_after_two' P1 P2 ψ (Q ∗ Rest)

theorem SepWPp.pure_elim_focus {prog : Program} {ret : BitVec 64} {s : State}
    (φ : Prop) {P P' : SepProp} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s P' Q Qp)
    (hf : P = ⌜φ⌝ ∗ P' := by sep_focus) :
    SepWPp prog ret s P Q Qp := by
  rw [hf]
  exact SepWPp.pure_left h

/-- Scratch stack slots used by inlined `lagrange_interpolate` (`0x6be14..0x6c084`):
    `[sp + 8]`, `[sp + 0x10]`, `[sp + 0x20]`, and `[x29 - 96 .. x29 - 24]`. -/
@[expose] def interpolateScratchAt (sp0 : BitVec 64) : SepProp :=
  ∃∗ v664 : BitVec 64, ∃∗ v656 : BitVec 64, ∃∗ v640 : BitVec 64,
  ∃∗ v192 : BitVec 64, ∃∗ v184 : BitVec 64, ∃∗ v176 : BitVec 64,
  ∃∗ v168 : BitVec 64, ∃∗ v160 : BitVec 64, ∃∗ v152 : BitVec 64,
    ((sp0 - 664#64) ↦₆₄ v664) ∗ ((sp0 - 656#64) ↦₆₄ v656) ∗ ((sp0 - 640#64) ↦₆₄ v640) ∗
    ((sp0 - 192#64) ↦₆₄ v192) ∗ ((sp0 - 184#64) ↦₆₄ v184) ∗ ((sp0 - 176#64) ↦₆₄ v176) ∗
    ((sp0 - 168#64) ↦₆₄ v168) ∗ ((sp0 - 160#64) ↦₆₄ v160) ∗ ((sp0 - 152#64) ↦₆₄ v152) ∗
    memRegion (sp0 - 144#64) 24

theorem pointsTo64_three_entails_memRegion_24 (sp0 v0 v1 v2 : BitVec 64) (Rest : SepProp) :
    ((sp0 - 144#64) ↦₆₄ v0) ∗ ((sp0 - 136#64) ↦₆₄ v1) ∗ ((sp0 - 128#64) ↦₆₄ v2) ∗ Rest ⊢
      memRegion (sp0 - 144#64) 24 ∗ Rest := by
  have h1 : sp0 - 136#64 = (sp0 - 144#64) + 8#64 := by bv_omega
  have h2 : sp0 - 128#64 = (sp0 - 144#64) + 16#64 := by bv_omega
  rw [h1, h2, show (24 : Nat) = 8 + (8 + 8) from rfl,
    memRegion_split (sp0 - 144#64) 8 16 (by omega),
    memRegion_split ((sp0 - 144#64) + 8#64) 8 8 (by omega),
    ProofLib.memRegion_eight (sp0 - 144#64),
    ProofLib.memRegion_eight ((sp0 - 144#64) + 8#64),
    ProofLib.memRegion_eight (((sp0 - 144#64) + 8#64) + 8#64),
    BitVec.add_assoc, show (8#64 : BitVec 64) + 8#64 = 16#64 from rfl, sepConj_assoc, sepConj_assoc]
  refine sepConj_mono (Entails.sepExists_intro v0) (sepConj_mono (Entails.sepExists_intro v1) ?_)
  exact sepConj_mono_left (Entails.sepExists_intro v2)

theorem fold_interpolateScratchAt (sp0 v664 v656 v640 v192 v184 v176 v168 v160 v152 : BitVec 64)
    (Rest : SepProp) :
    ((sp0 - 664#64) ↦₆₄ v664) ∗ ((sp0 - 656#64) ↦₆₄ v656) ∗ ((sp0 - 640#64) ↦₆₄ v640) ∗
      ((sp0 - 192#64) ↦₆₄ v192) ∗ ((sp0 - 184#64) ↦₆₄ v184) ∗ ((sp0 - 176#64) ↦₆₄ v176) ∗
      ((sp0 - 168#64) ↦₆₄ v168) ∗ ((sp0 - 160#64) ↦₆₄ v160) ∗ ((sp0 - 152#64) ↦₆₄ v152) ∗
      memRegion (sp0 - 144#64) 24 ∗ Rest ⊢
      interpolateScratchAt sp0 ∗ Rest := by
  rw [show ((sp0 - 664#64) ↦₆₄ v664) ∗ ((sp0 - 656#64) ↦₆₄ v656) ∗ ((sp0 - 640#64) ↦₆₄ v640) ∗
        ((sp0 - 192#64) ↦₆₄ v192) ∗ ((sp0 - 184#64) ↦₆₄ v184) ∗ ((sp0 - 176#64) ↦₆₄ v176) ∗
        ((sp0 - 168#64) ↦₆₄ v168) ∗ ((sp0 - 160#64) ↦₆₄ v160) ∗ ((sp0 - 152#64) ↦₆₄ v152) ∗
        memRegion (sp0 - 144#64) 24 ∗ Rest =
      (((sp0 - 664#64) ↦₆₄ v664) ∗ ((sp0 - 656#64) ↦₆₄ v656) ∗ ((sp0 - 640#64) ↦₆₄ v640) ∗
        ((sp0 - 192#64) ↦₆₄ v192) ∗ ((sp0 - 184#64) ↦₆₄ v184) ∗ ((sp0 - 176#64) ↦₆₄ v176) ∗
        ((sp0 - 168#64) ↦₆₄ v168) ∗ ((sp0 - 160#64) ↦₆₄ v160) ∗ ((sp0 - 152#64) ↦₆₄ v152) ∗
        memRegion (sp0 - 144#64) 24) ∗ Rest by ac_rfl]
  apply sepConj_mono_left
  unfold interpolateScratchAt
  exact Entails.sepExists_right v664 (Entails.sepExists_right v656 (Entails.sepExists_right v640
    (Entails.sepExists_right v192 (Entails.sepExists_right v184 (Entails.sepExists_right v176
      (Entails.sepExists_right v168 (Entails.sepExists_right v160
        (Entails.sepExists_right v152 (Entails.refl _)))))))))

end CryptoVerification.SpqrV1.Poly.DecodedMessage
