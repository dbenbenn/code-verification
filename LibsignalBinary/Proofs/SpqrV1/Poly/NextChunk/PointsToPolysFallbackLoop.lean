/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangeComplete.Defs
public import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Defs
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Epilogue -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Rodata -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangeComplete.Proof
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Proof
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysDefs
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysFallback
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<PolyEncoder as Encoder>::next_chunk`: Dynamic Lagrange Basis Loop

**Checked by Lean.**

Verifies the dynamic Lagrange basis interpolation loop (`0x6b3a4..0x6b490`, `+4128 -> +4368`),
invoking `lagrange_interpolate_prepare` and `lagrange_interpolate_complete` on `toOnePts pts`.
-/

public section

namespace CryptoVerification.SpqrV1.Poly.NextChunk

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.ComputeAt
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
open CryptoVerification.SpqrV1.Poly.LagrangeComplete
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

@[local arm64_norm, local wp_norm] theorem exists_pow_two_eq_two_fbl :
    (∃ k : Nat, 2 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨1, rfl⟩

@[local arm64_norm, local wp_norm] theorem exists_pow_two_eq_eight_fbl :
    (∃ k : Nat, 8 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨3, rfl⟩

attribute [local simp, local arm64_norm, local wp_norm]
  ofNat_succ_sub_one_fb ofNat_succ_add_neg_one_fb ofNat_add_one_eq_succ_fb

/-! ## 1. Pure Characterization of `Poly.lagrangeInterpolatePt` and the Basis Loop -/

/-- Total pure version of `Poly.lagrangeInterpolatePt` (`src/encoding/polynomial.rs:236–242`). -/
@[expose] def lagrangeInterpolatePtPure (ones : List Pt) (i : Nat) : Poly :=
  { coefficients := (lagrangeCompletePure (lagrangePreparePure ones) ones i).coefficients.drop 1 }

@[simp]
theorem lagrangeInterpolatePtPure_length (ones : List Pt) (i : Nat) :
    (lagrangeInterpolatePtPure ones i).coefficients.length = ones.length := by
  simp [lagrangeInterpolatePtPure]

theorem lagrangeComplete_prepare_head_tail (ones : List Pt) (i : Nat) :
    ∃ c0 : GF16,
      (lagrangeCompletePure (lagrangePreparePure ones) ones i).coefficients =
        c0 :: (lagrangeInterpolatePtPure ones i).coefficients := by
  have hlen : (lagrangeCompletePure (lagrangePreparePure ones) ones i).coefficients.length =
      ones.length + 1 := by
    rw [lagrangeCompletePure_length, lagrangePreparePure_length]
  cases hcs : (lagrangeCompletePure (lagrangePreparePure ones) ones i).coefficients with
  | nil =>
    rw [hcs, List.length_nil] at hlen
    omega
  | cons c0 rest =>
    refine ⟨c0, ?_⟩
    simp [lagrangeInterpolatePtPure, hcs]

theorem lagrangeInterpolatePt_eq_ok (ones : List Pt) (i : Nat)
    (hi : i < ones.length) (hbound : ones.length + 1 ≤ USIZE_MAX) :
    Poly.lagrangeInterpolatePt ones i = .ok (lagrangeInterpolatePtPure ones i) := by
  unfold Poly.lagrangeInterpolatePt
  rw [lagrangeInterpolatePrepare_eq_ok ones hbound]
  dsimp only [Bind.bind, Except.bind]
  rw [lagrangeInterpolateComplete_eq_ok hi]
  dsimp only
  obtain ⟨c0, hc0⟩ := lagrangeComplete_prepare_head_tail ones i
  rw [hc0]
  rfl

/-- Tail list of Lagrange basis polynomials `[lagrangeInterpolatePtPure ones i, ..., lagrangeInterpolatePtPure ones (i + rem - 1)]`. -/
@[expose] def lagrangeBasisTail (ones : List Pt) : Nat → Nat → List Poly
  | _, 0 => []
  | i, rem + 1 => lagrangeInterpolatePtPure ones i :: lagrangeBasisTail ones (i + 1) rem

@[simp]
theorem lagrangeBasisTail_length (ones : List Pt) (i rem : Nat) :
    (lagrangeBasisTail ones i rem).length = rem := by
  induction rem generalizing i with
  | zero => rfl
  | succ r ih => simp [lagrangeBasisTail, ih]

theorem lagrangeBasisTail_mem_length (ones : List Pt) :
    ∀ (rem i : Nat) (p : Poly),
      p ∈ lagrangeBasisTail ones i rem → p.coefficients.length = ones.length
  | 0, _, _, h => by simp [lagrangeBasisTail] at h
  | rem + 1, i, p, h => by
    simp only [lagrangeBasisTail, List.mem_cons] at h
    rcases h with rfl | hmem
    · exact lagrangeInterpolatePtPure_length ones i
    · exact lagrangeBasisTail_mem_length ones rem (i + 1) p hmem

theorem mapM_range'_lagrangeInterpolatePt_eq_ok (ones : List Pt)
    (hbound : ones.length + 1 ≤ USIZE_MAX) :
    ∀ (rem i : Nat),
      i + rem ≤ ones.length →
      (List.range' i rem).mapM (fun k => Poly.lagrangeInterpolatePt ones k) =
        .ok (lagrangeBasisTail ones i rem)
  | 0, i, _ => rfl
  | rem + 1, i, hle => by
    have hi : i < ones.length := by omega
    simp only [List.range'_succ, List.mapM_cons, lagrangeInterpolatePt_eq_ok ones i hi hbound,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    rw [mapM_range'_lagrangeInterpolatePt_eq_ok ones hbound rem (i + 1) (by omega)]
    rfl

theorem mapM_range_lagrangeInterpolatePt_eq_ok (ones : List Pt)
    (hbound : ones.length + 1 ≤ USIZE_MAX) :
    (List.range ones.length).mapM (fun k => Poly.lagrangeInterpolatePt ones k) =
      .ok (lagrangeBasisTail ones 0 ones.length) := by
  rw [List.range_eq_range']
  exact mapM_range'_lagrangeInterpolatePt_eq_ok ones hbound ones.length 0 (by omega)

/-! ## 2. Call-Site Offset & Stack / Memory Splitting Helpers -/

theorem sepConj_mono_fbl {P1 P2 Q1 Q2 : SepProp} (h1 : P1 ⊢ P2) (h2 : Q1 ⊢ Q2) :
    (P1 ∗ Q1) ⊢ (P2 ∗ Q2) :=
  Entails.trans (sepConj_mono_left h1) (sepConj_mono_right h2)

theorem stackAt_lagrangePrepare_split_complete (fsp : BitVec 64) :
    stackAt fsp lagrangePrepareStack =
      stackAt fsp lagrangeCompleteStack ∗
      memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
        (lagrangePrepareStack - lagrangeCompleteStack) := by
  have heq : lagrangePrepareStack =
      lagrangeCompleteStack + (lagrangePrepareStack - lagrangeCompleteStack) := by decide
  have h1 := ProofLib.stackAt_split_bottom fsp lagrangeCompleteStack
    (lagrangePrepareStack - lagrangeCompleteStack) (by decide)
  rw [← heq] at h1
  rw [h1, sepConj_comm]

theorem stackAt_lagrangePrepare_split_alloc (fsp : BitVec 64) :
    stackAt fsp lagrangePrepareStack =
      stackAt fsp allocHookStack ∗
      memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
        (lagrangePrepareStack - allocHookStack) := by
  have heq : lagrangePrepareStack =
      allocHookStack + (lagrangePrepareStack - allocHookStack) := by decide
  have h1 := ProofLib.stackAt_split_bottom fsp allocHookStack
    (lagrangePrepareStack - allocHookStack) (by decide)
  rw [← heq] at h1
  rw [h1, sepConj_comm]

/-- Splitting `gf16SliceAt ptr (c0 :: cs)` into `memRegion ptr 2` and `((ptr + 2#64) ↦ₛ gf16SliceBytes cs)`. -/
theorem gf16SliceAt_cons_memRegion2 (ptr : BitVec 64) (c0 : GF16) (cs : List GF16) :
    gf16SliceAt ptr (c0 :: cs) ⊢
      memRegion ptr 2 ∗ ((ptr + 2#64) ↦ₛ gf16SliceBytes cs) := by
  rw [gf16SliceAt_cons, gf16SliceAt_eq_pointsToBytes (ptr + 2#64) cs]
  refine sepConj_mono_fbl ?_ (Entails.refl _)
  rw [ProofLib.memRegion_two ptr]
  exact Entails.sepExists_right c0.value (Entails.refl _)

/-- Recombining `memRegion ptr 2`, `((ptr + 2#64) ↦ₛ bs)` (with `bs.length = 2 * n`), and spare capacity
    into `memRegion ptr (cap.toNat * 2)` for `__rust_dealloc`. -/
theorem memRegion_recombine_prepare (ptr : BitVec 64) (cap : BitVec 64) (n : Nat)
    (bs : List (BitVec 8)) (hbs : bs.length = 2 * n)
    (hcap : n + 1 ≤ cap.toNat) (hcap_bound : cap.toNat * 2 < 2 ^ 63) :
    memRegion ptr 2 ∗ ((ptr + 2#64) ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 (2 * (n + 1))) (2 * (cap.toNat - (n + 1))) ⊢
      memRegion ptr (cap.toNat * 2) := by
  have h1 : 2 * (n + 1) = 2 + 2 * n := by omega
  have h2 : cap.toNat * 2 = 2 * (n + 1) + 2 * (cap.toNat - (n + 1)) := by omega
  have ha1 : (ptr + 2#64) + BitVec.ofNat 64 (2 * n) = ptr + BitVec.ofNat 64 (2 * (n + 1)) := by
    rw [BitVec.add_assoc, show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, ← BitVec.ofNat_add, h1]
  have hm1 := ProofLib.memRegion_split' (b := ptr) (N := 2 * (n + 1)) (n := 2) (k := 2 * n)
    (b' := ptr + 2#64) h1 rfl (by omega)
  have hm2 := ProofLib.memRegion_split' (b := ptr) (N := cap.toNat * 2) (n := 2 * (n + 1))
    (k := 2 * (cap.toNat - (n + 1))) (b' := ptr + BitVec.ofNat 64 (2 * (n + 1))) h2 rfl (by omega)
  refine Entails.trans
    (sepConj_mono_fbl (Entails.refl _)
      (sepConj_mono_fbl (pointsToBytes_entails_memRegion (ptr + 2#64) bs) (Entails.refl _))) ?_
  rw [hbs, ← sepConj_assoc, ← hm1, ← hm2]
  exact Entails.refl _

attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  conditionHolds_mi_subsPState64 conditionHolds_pl_subsPState64
  conditionHolds_eq_addsPState64 conditionHolds_ne_addsPState64

theorem bit62_shl_one_false {n : Nat} (hb : n ≤ 0x0555555555555555) :
    (BitVec.ofNat 64 (n + 1) - 1#64).msb = false ∧
    (BitVec.ofNat 64 n).msb = false := by
  have h2 : (BitVec.ofNat 64 n).msb = false := by
    simp only [BitVec.msb_eq_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
      decide_eq_false_iff_not]
    omega
  refine ⟨?_, h2⟩
  rw [ofNat_succ_sub_one_fb]
  exact h2

theorem ult_max_2n_false {n : Nat} (hb : n ≤ 0x0555555555555555) :
    (0x7ffffffffffffffe#64).ult (BitVec.ofNat 64 (2 * n)) = false := by
  apply Bool.eq_false_iff.mpr; intro h
  have hlt := BitVec.ult_iff_lt.mp h
  bv_omega

theorem adds_one_ne_zero {i : Nat} (hb : i < 0x0555555555555555) :
    (BitVec.ofNat 64 i + 1#64 == 0#64) = false ∧
    (BitVec.ofNat 64 i + 1#64 != 0#64) = true ∧
    (BitVec.ofNat 64 (i + 1) == 0#64) = false ∧
    (BitVec.ofNat 64 (i + 1) != 0#64) = true := by
  have h1 : (BitVec.ofNat 64 i + 1#64 == 0#64) = false := by
    apply Bool.eq_false_iff.mpr; intro h
    have heq := beq_iff_eq.mp h
    bv_omega
  have h2 : (BitVec.ofNat 64 i + 1#64 != 0#64) = true := by
    rw [bne, h1]; rfl
  have h3 : (BitVec.ofNat 64 (i + 1) == 0#64) = false := by
    rw [← ofNat_add_one_eq_succ_fb]; exact h1
  have h4 : (BitVec.ofNat 64 (i + 1) != 0#64) = true := by
    rw [← ofNat_add_one_eq_succ_fb]; exact h2
  exact ⟨h1, h2, h3, h4⟩

@[local simp, local arm64_norm, local wp_norm]
theorem shl_one_ofNat_eq (n : Nat) :
    BitVec.ofNat 64 n <<< 1#64 = BitVec.ofNat 64 (2 * n) := by
  have h : BitVec.ofNat 64 n <<< 1#64 = BitVec.ofNat 64 n * 2#64 := by bv_bits
  rw [h]; bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem shl_one_ofNat_eq_nat (n : Nat) :
    BitVec.ofNat 64 n <<< 1 = BitVec.ofNat 64 (2 * n) :=
  shl_one_ofNat_eq n

theorem shl_one_cap_toNat {cap : BitVec 64} (hbound : cap.toNat * 2 < 2 ^ 63) :
    (cap <<< 1#64).toNat = cap.toNat * 2 := by
  have h : cap <<< 1#64 = cap * 2#64 := by bv_bits
  rw [h, BitVec.toNat_mul, BitVec.toNat_ofNat]
  change (cap.toNat * 2) % 2 ^ 64 = cap.toNat * 2
  exact Nat.mod_eq_of_lt (by omega)

theorem shl_one_cap_toNat_nat {cap : BitVec 64} (hbound : cap.toNat * 2 < 2 ^ 63) :
    (cap <<< 1).toNat = cap.toNat * 2 :=
  shl_one_cap_toNat hbound

theorem memRegion_split_polyHeader_fbl (p : BitVec 64) :
    memRegion p 24 =
      ∃∗ u16 : BitVec 64, ∃∗ u8 : BitVec 64, ∃∗ u0 : BitVec 64,
        (p ↦₆₄ u0) ∗ ((p + 8#64) ↦₆₄ u8) ∗ ((p + 16#64) ↦₆₄ u16) := by
  have hp8 : p + 8#64 = p + BitVec.ofNat 64 8 := rfl
  have hp16 : p + 16#64 = (p + 8#64) + BitVec.ofNat 64 8 := by bv_omega
  rw [ProofLib.memRegion_split' (b := p) (n := 8) (k := 16) (b' := p + 8#64) rfl hp8 (by decide),
      ProofLib.memRegion_split' (b := p + 8#64) (n := 8) (k := 8) (b' := p + 16#64) rfl hp16 (by decide),
      ProofLib.memRegion_eight p, ProofLib.memRegion_eight (p + 8#64), ProofLib.memRegion_eight (p + 16#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem polyHeader_entails_memRegion24 (p : BitVec 64) (u0 u8 u16 : BitVec 64) :
    ((p ↦₆₄ u0) ∗ ((p + 8#64) ↦₆₄ u8) ∗ ((p + 16#64) ↦₆₄ u16)) ⊢ memRegion p 24 := by
  rw [memRegion_split_polyHeader_fbl p]
  exact Entails.sepExists_right u16 (Entails.sepExists_right u8 (Entails.sepExists_right u0 (Entails.refl _)))

theorem polyHeader_entails_memRegion24_off (base : BitVec 64) (u0 u8 u16 : BitVec 64) :
    (((base + 656#64) ↦₆₄ u0) ∗ ((base + 664#64) ↦₆₄ u8) ∗ ((base + 672#64) ↦₆₄ u16)) ⊢
      memRegion (base + 656#64) 24 := by
  have h8 : (base + 656#64) + 8#64 = base + 664#64 := by bv_omega
  have h16 : (base + 656#64) + 16#64 = base + 672#64 := by bv_omega
  rw [← h8, ← h16]
  exact polyHeader_entails_memRegion24 (base + 656#64) u0 u8 u16

theorem polyListOf_cons_fbl (A : RustAlloc) (ptr : BitVec 64) (p : Poly) (ps : List Poly) :
    polyListOf A ptr (p :: ps) =
      (polyOf A ptr p ∗ polyListOf A (ptr + 24#64) ps) := rfl

theorem call_panic_sepWPp_fbl {α : Type} {prog : Program} {entry ret_pc ret : BitVec 64}
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

theorem pull_pure4 (P1 P2 P3 : SepProp) (φ : Prop) (Q : SepProp) :
    P1 ∗ P2 ∗ P3 ∗ ⌜φ⌝ ∗ Q = ⌜φ⌝ ∗ P1 ∗ P2 ∗ P3 ∗ Q := by
  ac_rfl

theorem polyOf_prepare_unfold (A : RustAlloc) (fsp : BitVec 64) (ones : List Pt) :
    polyOf A (fsp + 656#64) (lagrangePreparePure ones) ⊢
      ∃∗ prepCap : BitVec 64, ∃∗ prepPtr : BitVec 64,
        ⌜ones.length + 1 ≤ prepCap.toNat ∧ prepCap.toNat * 2 < 2 ^ 63 ∧ prepPtr ≠ 0#64 ∧ prepCap ≠ 0#64⌝ ∗
        ((fsp + 656#64) ↦₆₄ prepCap) ∗
        ((fsp + 664#64) ↦₆₄ prepPtr) ∗
        ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 (ones.length + 1)) ∗
        A.live prepPtr (prepCap.toNat * 2) 2 ∗
        gf16SliceAt prepPtr (lagrangePreparePure ones).coefficients ∗
        memRegion (prepPtr + BitVec.ofNat 64 ((ones.length + 1) * 2))
          ((prepCap.toNat - (ones.length + 1)) * 2) := by
  have h664 : (fsp + 656#64) + 8#64 = fsp + 664#64 := by bv_omega
  have h672 : (fsp + 656#64) + 16#64 = fsp + 672#64 := by bv_omega
  have hlen : (lagrangePreparePure ones).coefficients.length = ones.length + 1 :=
    lagrangePreparePure_length ones
  rw [LagrangePrepare.polyOf_eq A (fsp + 656#64) (lagrangePreparePure ones), h664, h672]
  apply Entails.sepExists_elim; intro prepCap
  apply Entails.sepExists_elim; intro prepPtr
  apply Entails.sepExists_right prepCap
  apply Entails.sepExists_right prepPtr
  rw [pull_pure4]
  apply Entails.pure_left
  rintro ⟨hle, hbound, hptr⟩
  rw [hlen] at hle
  have hcap_ne : prepCap ≠ 0#64 := by
    intro h0; subst h0; change ones.length + 1 ≤ 0 at hle; omega
  have hcap_ne' : prepCap ≠ 0 := hcap_ne
  refine Entails.pure_right ⟨hle, hbound, hptr, hcap_ne⟩ ?_
  simp only [hcap_ne', ↓reduceIte, hlen, sepConj_assoc]
  exact Entails.refl _

theorem ofNat_succ_ne_zero {n : Nat} (hb : n ≤ 0x0555555555555555) :
    (BitVec.ofNat 64 (n + 1) == 0#64) = false := by
  apply Bool.eq_false_iff.mpr; intro h
  have heq := beq_iff_eq.mp h
  bv_omega

theorem ofNat_pos_ne_zero {n : Nat} (hpos : 0 < n) (hb : n ≤ 0x0555555555555555) :
    (BitVec.ofNat 64 n == 0#64) = false ∧
    (BitVec.ofNat 64 (2 * n) == 0#64) = false := by
  refine ⟨?_, ?_⟩
  · apply Bool.eq_false_iff.mpr; intro h; have heq := beq_iff_eq.mp h; bv_omega
  · apply Bool.eq_false_iff.mpr; intro h; have heq := beq_iff_eq.mp h; bv_omega

theorem stackAt_complete_to_alloc (fsp : BitVec 64) :
    stackAt fsp lagrangeCompleteStack ∗
      memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
        (lagrangePrepareStack - lagrangeCompleteStack) ⊢
      stackAt fsp allocHookStack ∗
        memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
          (lagrangePrepareStack - allocHookStack) := by
  rw [← stackAt_lagrangePrepare_split_complete fsp,
      stackAt_lagrangePrepare_split_alloc fsp]
  exact Entails.refl _

theorem stackAt_alloc_to_prepare (fsp : BitVec 64) :
    stackAt fsp allocHookStack ∗
      memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
        (lagrangePrepareStack - allocHookStack) ⊢
      stackAt fsp lagrangePrepareStack := by
  rw [← stackAt_lagrangePrepare_split_alloc fsp]
  exact Entails.refl _

/-! ## 3. Single Iteration of the Lagrange Basis Loop (`0x6b3a4..0x6b490`, `+4128 -> +4128 / +4368`) -/

/-- Pure Lagrange basis `[(List.range ones.length).map (lagrangeInterpolatePtPure ones)]`. -/
@[expose] def lagrangeBasisPure (ones : List Pt) : List Poly :=
  (List.range ones.length).map (lagrangeInterpolatePtPure ones)

/-- Suffix of `lagrangeBasisPure ones` starting at index `i` of length `k`. -/
@[expose] def lagrangeBasisFrom (ones : List Pt) : Nat → Nat → List Poly
  | _, 0 => []
  | i, k + 1 => lagrangeInterpolatePtPure ones i :: lagrangeBasisFrom ones (i + 1) k

theorem lagrangeBasisFrom_eq_map_range' (ones : List Pt) (i k : Nat) :
    lagrangeBasisFrom ones i k = (List.range' i k).map (lagrangeInterpolatePtPure ones) := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih => simp [lagrangeBasisFrom, List.range', ih]

theorem lagrangeBasisFrom_zero_eq (ones : List Pt) :
    lagrangeBasisFrom ones 0 ones.length = lagrangeBasisPure ones := by
  rw [lagrangeBasisFrom_eq_map_range', ← List.range_eq_range']; rfl

theorem memRegion_split_24_succ (curBasis : BitVec 64) (rem : Nat)
    (hbound : 24 * (rem + 1) < 2 ^ 64) :
    memRegion curBasis (24 * (rem + 1)) =
      memRegion curBasis 24 ∗ memRegion (curBasis + 24#64) (24 * rem) := by
  have h24 : 24 * (rem + 1) = 24 + 24 * rem := by omega
  exact ProofLib.memRegion_split' (b := curBasis) (n := 24) (k := 24 * rem)
    (b' := curBasis + 24#64) h24 rfl (by omega)

end CryptoVerification.SpqrV1.Poly.NextChunk
