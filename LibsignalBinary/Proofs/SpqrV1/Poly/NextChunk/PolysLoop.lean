/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Epilogue -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Pure -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.Proof
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<PolyEncoder as Encoder>::next_chunk`: `EncoderState::Polys` Path

Verifies the 16-iteration polynomial evaluation loop (`0x6a3e0..0x6a45c -> 0x6b508`) when
`x.enc.s = .polys polys`, invoking `<Poly>::compute_at` (`0x61914`) on each `polys[i]`.
-/

public section

namespace CryptoVerification.SpqrV1.Poly.NextChunk

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.ComputeAt
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre
  LagrangePrepare.sp_setPC_pre LagrangePrepare.sp_setMem_setPC_pre
  LagrangePrepare.readReg64_setPC_pre LagrangePrepare.readReg64_setMem_setPC_pre
  LagrangePrepare.readReg32_setPC_pre LagrangePrepare.readReg32_setMem_setPC_pre
  LagrangePrepare.readReg_setPC_pre LagrangePrepare.readReg_setMem_setPC_pre

attribute [local simp, local arm64_norm, local wp_norm]
  polyEncoderTagOff polyEncoderVecsOff polyEncoderVecsSize
  polyEncoderIdxOff polyEncoderPadOff polyEncoderPadSize
  polyEncoderPointsTag polyEncoderPolysTag
  chunkDataOff chunkIndexOff chunkSize

/-! ## 1. Separation-Logic Helpers for `out_ptr` Buffer and `polysArrayAt` -/

theorem memRegion_split_two_bytes (base : BitVec 64) (i : Nat) (hi : i < 16) :
    memRegion (base + BitVec.ofNat 64 (2 * i)) (32 - 2 * i) ⊢
      ∃∗ b0 : BitVec 8, ∃∗ b1 : BitVec 8,
        ((base + BitVec.ofNat 64 (2 * i)) ↦₈ b0) ∗
        ((base + BitVec.ofNat 64 (2 * i + 1)) ↦₈ b1) ∗
        memRegion (base + BitVec.ofNat 64 (2 * (i + 1))) (32 - 2 * (i + 1)) := by
  have h1 : 32 - 2 * i = 1 + (31 - 2 * i) := by omega
  have h2 : 31 - 2 * i = 1 + (32 - 2 * (i + 1)) := by omega
  have ha1 : base + BitVec.ofNat 64 (2 * i + 1) = (base + BitVec.ofNat 64 (2 * i)) + 1#64 := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have ha2 : base + BitVec.ofNat 64 (2 * (i + 1)) = (base + BitVec.ofNat 64 (2 * i + 1)) + 1#64 := by
    have heq : 2 * i + 1 + 1 = 2 * (i + 1) := by omega
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, heq]
  rw [ProofLib.memRegion_split' (b := base + BitVec.ofNat 64 (2 * i)) (n := 1) (k := 31 - 2 * i)
        (b' := base + BitVec.ofNat 64 (2 * i + 1)) h1 ha1 (by omega),
      ProofLib.memRegion_split' (b := base + BitVec.ofNat 64 (2 * i + 1)) (n := 1) (k := 32 - 2 * (i + 1))
        (b' := base + BitVec.ofNat 64 (2 * (i + 1))) h2 ha2 (by omega),
      ProofLib.memRegion_one (base + BitVec.ofNat 64 (2 * i)),
      ProofLib.memRegion_one (base + BitVec.ofNat 64 (2 * i + 1))]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro b1
  apply Entails.sepExists_elim; intro b0
  exact Entails.sepExists_right b0 (Entails.sepExists_right b1 (Entails.of_eq (by ac_rfl)))

theorem pointsToBytes_append_two_bytes (base : BitVec 64) (bs : List (BitVec 8)) (i : Nat)
    (hlen : bs.length = 2 * i) (b0 b1 : BitVec 8) :
    (base ↦ₛ bs) ∗
      ((base + BitVec.ofNat 64 (2 * i)) ↦₈ b0) ∗
      ((base + BitVec.ofNat 64 (2 * i + 1)) ↦₈ b1) ⊢
      (base ↦ₛ (bs ++ [b0, b1])) := by
  rw [ProofLib.pointsToBytes_append base bs [b0, b1], hlen]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
  have ha1 : (base + BitVec.ofNat 64 (2 * i)) + 1#64 = base + BitVec.ofNat 64 (2 * i + 1) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [ha1]
  exact Entails.of_eq (by ac_rfl)

theorem arrayAt_append {α : Type} (elem : α → BitVec 64 → SepProp) (stride : Nat) :
    ∀ (xs ys : List α) (base : BitVec 64),
      arrayAt elem stride base (xs ++ ys) =
        (arrayAt elem stride base xs ∗
         arrayAt elem stride (base + BitVec.ofNat 64 (stride * xs.length)) ys)
  | [], ys, base => by simp [arrayAt]
  | x :: xs, ys, base => by
    simp only [List.cons_append, arrayAt, arrayAt_append elem stride xs ys, List.length_cons]
    have haddr : (base + BitVec.ofNat 64 stride) + BitVec.ofNat 64 (stride * xs.length) =
        base + BitVec.ofNat 64 (stride * (xs.length + 1)) := by
      have hm : stride + stride * xs.length = stride * (xs.length + 1) := by
        rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, hm]
    rw [haddr]
    ac_rfl

theorem polyListOf_split_idx (A : RustAlloc) (base : BitVec 64)
    (polys : List LibsignalSpqrV1.Poly) (i : Nat) (hi : i < polys.length) :
    polyListOf A base polys =
      (polyListOf A base (polys.take i) ∗
        polyOf A (base + BitVec.ofNat 64 (24 * i)) (polys[i]'hi) ∗
        polyListOf A (base + BitVec.ofNat 64 (24 * (i + 1))) (polys.drop (i + 1))) := by
  unfold polyListOf
  conv => lhs; rw [← List.take_append_drop i polys]
  rw [arrayAt_append, List.length_take_of_le (by omega), List.drop_eq_getElem_cons hi]
  simp only [arrayAt, vecHeaderBytes]
  have haddr : (base + BitVec.ofNat 64 (24 * i)) + BitVec.ofNat 64 24 =
      base + BitVec.ofNat 64 (24 * (i + 1)) := by
    have hm : 24 * i + 24 = 24 * (i + 1) := by omega
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, hm]
  rw [haddr]

theorem polyCoefficients_len_bound_of_cap {len cap : Nat}
    (hlen : len ≤ cap) (hcap : cap * gf16Stride < 2 ^ 63) :
    2 * len + 2 ≤ 2 ^ 63 := by
  dsimp [gf16Stride] at hcap
  omega

theorem chunkPolysBytes_add (idx : BitVec 16) (polys : List LibsignalSpqrV1.Poly) :
    ∀ (m k n : Nat),
      chunkPolysBytes idx polys k (m + n) =
        chunkPolysBytes idx polys k m ++ chunkPolysBytes idx polys (k + m) n
  | 0, k, n => by simp [chunkPolysBytes]
  | m + 1, k, n => by
    have hadd : m + 1 + n = (m + n) + 1 := by omega
    have hk : k + (m + 1) = (k + 1) + m := by omega
    rw [hadd]
    conv => lhs; unfold chunkPolysBytes
    conv => rhs; arg 1; unfold chunkPolysBytes
    rw [chunkPolysBytes_add idx polys m (k + 1) n, hk]
    simp only [List.cons_append]

theorem chunkPolysBytes_zero_succ (idx : BitVec 16) (polys : List LibsignalSpqrV1.Poly)
    (i : Nat) (hi : i < polys.length) :
    chunkPolysBytes idx polys 0 (i + 1) =
      chunkPolysBytes idx polys 0 i ++
        [BitVec.setWidth 8 ((computeAtPure (polys[i]'hi) (GF16.new idx)).value >>> 8),
         BitVec.setWidth 8 (computeAtPure (polys[i]'hi) (GF16.new idx)).value] := by
  rw [chunkPolysBytes_add idx polys i 0 1, Nat.zero_add]
  have hp : polys[i]? = some (polys[i]'hi) := List.getElem?_eq_getElem hi
  simp [chunkPolysBytes, hp]

theorem call_panic_sepWPp {α : Type} {prog : Program} {entry ret_pc ret : BitVec 64}
    {s0 s : State} {spec : Spec α} {x : α} {φ : Prop} {T F P R : SepProp}
    {Q : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : s.trace = s0.trace)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_eq : ∀ sf, spec.onPanic x s sf = (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)))
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  refine SepWPp.call_frame hcall hpc hrun hsp hlr hspec hφ hP hexit
    (fun sf _ hm => ?_)
    (fun sf hpcf hrunf hspf hcsf => hnext sf hpcf hrunf hspf hcsf)
    (by intro sf R' _ hm; rw [hoom_eq sf] at hm; exact Satisfies.drop_mid hm)
  have hpan_tr : allocFailedIn s sf = allocFailedIn s0 sf := by
    unfold allocFailedIn; rw [htr]
  rw [hpan_eq sf, hpan_tr, htr, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hpan, hm2⟩
  rw [← sepConj_assoc] at hm2
  unfold nextChunkOnPanic
  exact allowPanic_panicked (φ := allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) hpan hm2

/-- Spare-capacity and allocator-liveness portion of `polyBuf`. -/
@[expose] def polyBufRest (A : RustAlloc) (cap ptr : BitVec 64) (p : LibsignalSpqrV1.Poly) : SepProp :=
  if cap = 0 then emp
  else A.live ptr (cap.toNat * gf16Stride) gf16Align ∗
    memRegion (ptr + BitVec.ofNat 64 (p.coefficients.length * gf16Stride))
      ((cap.toNat - p.coefficients.length) * gf16Stride)

theorem polyBufBody_eq_slice_rest (A : RustAlloc) (cap ptr : BitVec 64)
    (p : LibsignalSpqrV1.Poly) (hlen : p.coefficients.length ≤ cap.toNat) :
    (if cap = 0 then emp
     else A.live ptr (cap.toNat * gf16Stride) gf16Align ∗
       arrayAt gf16At gf16Stride ptr p.coefficients ∗
       memRegion (ptr + BitVec.ofNat 64 (p.coefficients.length * gf16Stride))
         ((cap.toNat - p.coefficients.length) * gf16Stride)) =
      (gf16SliceAt ptr p.coefficients ∗ polyBufRest A cap ptr p) := by
  unfold polyBufRest gf16SliceAt
  by_cases h0 : cap = 0
  · have hcap0 : cap.toNat = 0 := by subst h0; rfl
    have hlen0 : p.coefficients.length = 0 := by omega
    have hnil : p.coefficients = [] := List.eq_nil_of_length_eq_zero hlen0
    simp [h0, hnil, arrayAt]
  · simp only [h0, ↓reduceIte]
    ac_rfl

theorem polyOf_unfold (A : RustAlloc) (v : BitVec 64) (p : LibsignalSpqrV1.Poly) :
    polyOf A v p ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 p.coefficients.length) ∗
        ⌜p.coefficients.length ≤ cap.toNat ∧ cap.toNat * gf16Stride < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (if cap = 0 then emp
         else A.live ptr (cap.toNat * gf16Stride) gf16Align ∗
           arrayAt gf16At gf16Stride ptr p.coefficients ∗
           memRegion (ptr + BitVec.ofNat 64 (p.coefficients.length * gf16Stride))
             ((cap.toNat - p.coefficients.length) * gf16Stride)) := by
  unfold polyOf vecOf vecAt vecHeader vecBuf
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.of_eq (by ac_rfl)))

theorem polyOf_fold (A : RustAlloc) (v cap ptr : BitVec 64) (p : LibsignalSpqrV1.Poly)
    (hbounds : p.coefficients.length ≤ cap.toNat ∧ cap.toNat * gf16Stride < 2 ^ 63 ∧ ptr ≠ 0) :
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 p.coefficients.length) ∗
      gf16SliceAt ptr p.coefficients ∗
      polyBufRest A cap ptr p ⊢
      polyOf A v p := by
  have htrue : (p.coefficients.length ≤ cap.toNat ∧ cap.toNat * gf16Stride < 2 ^ 63 ∧ ptr ≠ 0) = True :=
    propext ⟨fun _ => trivial, fun _ => hbounds⟩
  unfold polyOf vecOf vecAt vecHeader vecBuf
  apply Entails.sepExists_right cap
  apply Entails.sepExists_right ptr
  rw [htrue, pure_true, emp_sepConj, polyBufBody_eq_slice_rest A cap ptr p hbounds.1]
  exact Entails.of_eq (by ac_rfl)

/-! ## 2. Arithmetic and Bitvector Normalization for the `Polys` Loop -/

@[local simp, local arm64_norm, local wp_norm]
theorem x21_sub_8_eq (encA : BitVec 64) (i : Nat) :
    (encA + BitVec.ofNat 64 (24 * i + 24)) + 18446744073709551608#64 =
      ((encA + 8#64) + BitVec.ofNat 64 (24 * i)) + 8#64 := by
  rw [BitVec.ofNat_add]
  generalize BitVec.ofNat 64 (24 * i) = u
  bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem x21_sub_8_add_8_eq (encA : BitVec 64) (i : Nat) :
    (((encA + 8#64) + BitVec.ofNat 64 (24 * i)) + 8#64) + 8#64 =
      ((encA + 8#64) + BitVec.ofNat 64 (24 * i)) + 16#64 := by
  rw [BitVec.add_assoc (((encA + 8#64) + BitVec.ofNat 64 (24 * i))) 8#64 8#64]
  rfl

@[local simp, local arm64_norm, local wp_norm]
theorem x21_add_24_eq (encA : BitVec 64) (i : Nat) :
    (encA + BitVec.ofNat 64 (24 * i + 24)) + 24#64 =
      encA + BitVec.ofNat 64 (24 * (i + 1) + 24) := by
  have hm : (24 * i + 24) + 24 = 24 * (i + 1) + 24 := by omega
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, hm]

@[local simp, local arm64_norm, local wp_norm]
theorem ofNat_two_mul_add_one (i : Nat) :
    BitVec.ofNat 64 (2 * i) + 1#64 = BitVec.ofNat 64 (2 * i + 1) := by
  rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]

@[local simp, local arm64_norm, local wp_norm]
theorem ofNat_two_mul_add_two (i : Nat) :
    BitVec.ofNat 64 (2 * i) + 2#64 = BitVec.ofNat 64 (2 * (i + 1)) := by
  have hm : 2 * i + 2 = 2 * (i + 1) := by omega
  rw [show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, ← BitVec.ofNat_add, hm]

@[local simp, local arm64_norm, local wp_norm]
theorem ofNat_succ_add_neg1 (r : Nat) :
    BitVec.ofNat 64 (r + 1) + 18446744073709551615#64 = BitVec.ofNat 64 r := by
  have hneg : (1#64 : BitVec 64) + 18446744073709551615#64 = 0#64 := rfl
  rw [BitVec.ofNat_add]
  change (BitVec.ofNat 64 r + 1#64) + 18446744073709551615#64 = BitVec.ofNat 64 r
  rw [BitVec.add_assoc, hneg, BitVec.add_zero]

@[local simp, local arm64_norm, local wp_norm]
theorem ofNat_succ_sub_one' (r : Nat) :
    BitVec.ofNat 64 (r + 1) - 1#64 = BitVec.ofNat 64 r :=
  ofNat_sub_one_succ r

theorem ofNat_sub_one_beq_zero {rem : Nat} (hrem : rem < 16) :
    (BitVec.ofNat 64 (rem + 1) == 1#64) = (rem == 0) ∧
    (BitVec.ofNat 64 rem == 0#64) = (rem == 0) := by
  cases rem with
  | zero => decide
  | succ r =>
    have h1 : (1#64 : BitVec 64) = BitVec.ofNat 64 1 := rfl
    have h0 : (0#64 : BitVec 64) = BitVec.ofNat 64 0 := rfl
    rw [h1, h0]
    rcases ofNat_beq_false_of_lt (a := 1) (b := r + 1 + 1) (by omega) (by omega) with ⟨_, _, ha, _⟩
    rcases ofNat_beq_false_of_lt (a := 0) (b := r + 1) (by omega) (by omega) with ⟨_, _, hb, _⟩
    exact ⟨ha, hb⟩

theorem lsr8_trunc8_of_trunc16 {v : BitVec 64} {val16 : BitVec 16}
    (h : v.truncate 16 = val16) :
    BitVec.zeroExtend 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 v) >>> 8) =
      BitVec.setWidth 8 (val16 >>> 8) := by
  subst h; bv_slice

theorem trunc8_of_trunc16 {v : BitVec 64} {val16 : BitVec 16}
    (h : v.truncate 16 = val16) :
    BitVec.zeroExtend 8 v = BitVec.setWidth 8 val16 := by
  subst h; bv_slice

@[local simp, local arm64_norm, local wp_norm]
theorem setWidth16_mov_w_zext16 (idx16 : BitVec 16) :
    ((((idx16.setWidth 64).setWidth 32).setWidth 64).setWidth 16) = idx16 := by
  bv_slice

theorem sepWPp_exists_left {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {P : α → SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ x, SepWPp prog ret s (P x) Q Qp) :
    SepWPp prog ret s (∃∗ x, P x) Q Qp := by
  intro R hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨x, hmx⟩
  exact h x R hmx

end CryptoVerification.SpqrV1.Poly.NextChunk

