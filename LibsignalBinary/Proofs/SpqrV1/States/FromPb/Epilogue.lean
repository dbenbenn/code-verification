/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBase
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Shared `Ok` Epilogue (`+8176..+8496 -> +64 -> +92`)

Proves the shared `Ok` epilogue at `+8176` / `+8180` (`0x5c094..0x5c1d4 -> 0x5a0e4..0x5a100`),
which materializes the 928-byte `Result<States, Error>::Ok(...)` into `out` (`x19`) from registers
and stack slots and returns to `s0.x30`.
-/

public section

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
theorem bv_add_lit_add_lit (x : BitVec 64) (a b : Nat) :
    x + BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

@[local arm64_norm, local wp_norm]
theorem out_168_add_96 (out : BitVec 64) : out + 168#64 + 96#64 = out + 264#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem out_168_add_96_16 (out : BitVec 64) : out + 264#64 + 16#64 = out + 280#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem out_168_add_128 (out : BitVec 64) : out + 168#64 + 128#64 = out + 296#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem out_168_add_128_16 (out : BitVec 64) : out + 296#64 + 16#64 = out + 312#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem out_168_add_160 (out : BitVec 64) : out + 168#64 + 160#64 = out + 328#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem out_168_add_160_16 (out : BitVec 64) : out + 328#64 + 16#64 = out + 344#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem out_168_add_192 (out : BitVec 64) : out + 168#64 + 192#64 = out + 360#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem out_168_add_192_16 (out : BitVec 64) : out + 360#64 + 16#64 = out + 376#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem out_888_add_8 (out : BitVec 64) : out + 888#64 + 8#64 = out + 896#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem out_888_add_16 (out : BitVec 64) : out + 888#64 + 16#64 = out + 904#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem out_904_add_8 (out : BitVec 64) : out + 904#64 + 8#64 = out + 912#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem fsp_848_add_15 (fsp : BitVec 64) : fsp + 848#64 + 15#64 = fsp + 863#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem fsp_848_add_39 (fsp : BitVec 64) : fsp + 848#64 + 39#64 = fsp + 887#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem fsp_576_add_15 (fsp : BitVec 64) : fsp + 576#64 + 15#64 = fsp + 591#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem out_537_add_8 (out : BitVec 64) : out + 537#64 + 8#64 = out + 545#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem out_537_add_16 (out : BitVec 64) : out + 537#64 + 16#64 = out + 553#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem out_145_add_15 (out : BitVec 64) : out + 145#64 + 15#64 = out + 160#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem out_121_add_8 (out : BitVec 64) : out + 121#64 + 8#64 = out + 129#64 := by bv_omega

theorem pointsTo128_eq_pair64 (a : BitVec 64) (q : BitVec 128) :
    (a ↦₁₂₈ q) =
      (a ↦₆₄ q.extractLsb' 0 64) ∗ ((a + 8#64) ↦₆₄ q.extractLsb' 64 64) := by
  have h : q.extractLsb' 64 64 ++ q.extractLsb' 0 64 = q := by bv_kernel
  rw [EncoderFromPb.pointsTo64_pair_eq_pointsTo128, h]

@[expose] def overlapWord7 (w0 w8 : BitVec 64) : BitVec 64 :=
  (w0 >>> 56) ||| (w8 <<< 8)

theorem unpack64_append_loBytes7_eq (w0 w8 : BitVec 64) :
    unpack64 w0 ++ EncoderFromPb.loBytes7 w8 =
      EncoderFromPb.loBytes7 w0 ++ unpack64 (overlapWord7 w0 w8) := by
  simp only [unpack64, EncoderFromPb.loBytes7, overlapWord7, List.take,
    List.cons_append, List.nil_append, List.cons.injEq]
  refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial,
    by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel,
    by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel, trivial⟩

theorem pointsTo64_loBytes7_eq_loBytes7_overlapWord7 (a w0 w8 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦ₛ EncoderFromPb.loBytes7 w8) =
      (a ↦ₛ EncoderFromPb.loBytes7 w0) ∗ ((a + 7#64) ↦₆₄ overlapWord7 w0 w8) := by
  rw [ProofLib.pointsTo64_eq_pointsToBytes a w0,
      ProofLib.pointsTo64_eq_pointsToBytes (a + 7#64) (overlapWord7 w0 w8)]
  have h1 := (ProofLib.pointsToBytes_append a (unpack64 w0) (EncoderFromPb.loBytes7 w8)).symm
  rw [unpack64_length] at h1
  have h2 := (ProofLib.pointsToBytes_append a (EncoderFromPb.loBytes7 w0)
    (unpack64 (overlapWord7 w0 w8))).symm
  rw [EncoderFromPb.length_loBytes7] at h2
  rw [h1, h2, unpack64_append_loBytes7_eq]

theorem pointsTo128_loBytes7_eq (a : BitVec 64) (q : BitVec 128) (w16 : BitVec 64) :
    (a ↦₁₂₈ q) ∗ ((a + 16#64) ↦ₛ EncoderFromPb.loBytes7 w16) =
      (a ↦₆₄ q.extractLsb' 0 64) ∗
      ((a + 8#64) ↦ₛ EncoderFromPb.loBytes7 (q.extractLsb' 64 64)) ∗
      ((a + 15#64) ↦₆₄ overlapWord7 (q.extractLsb' 64 64) w16) := by
  have hm := pointsTo64_loBytes7_eq_loBytes7_overlapWord7 (a + 8#64) (q.extractLsb' 64 64) w16
  have ha16 : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
  have ha15 : a + 8#64 + 7#64 = a + 15#64 := by bv_omega
  rw [ha16, ha15] at hm
  rw [pointsTo128_eq_pair64 a q, sepConj_assoc, hm]

theorem pointsTo128_entails_memRegion_16 (a : BitVec 64) (q : BitVec 128) :
    (a ↦₁₂₈ q) ⊢ memRegion a 16 :=
  IsBlock.entails (IsBlock.pointsTo128 a q) (IsBlock.memRegion a 16) fun _ _ => trivial

theorem loBytes7_overlapWord7_entails_memRegion_15 (a w0 w8 : BitVec 64) :
    (a ↦ₛ EncoderFromPb.loBytes7 w0) ∗ ((a + 7#64) ↦₆₄ overlapWord7 w0 w8) ⊢
      memRegion a 15 := by
  rw [← pointsTo64_loBytes7_eq_loBytes7_overlapWord7 a w0 w8]
  have h1 := Drop.pointsTo64_entails_memRegion a w0
  have h2 : ((a + 8#64) ↦ₛ EncoderFromPb.loBytes7 w8) ⊢ memRegion (a + 8#64) 7 := by
    rw [← EncoderFromPb.length_loBytes7 w8]
    exact ProofLib.pointsToBytes_entails_memRegion (a + 8#64) _
  have h12 : memRegion a 8 ∗ memRegion (a + 8#64) 7 = memRegion a 15 := by
    rw [← ProofLib.memRegion_split' (b := a) (n := 8) (k := 7) (b' := a + 8#64) rfl rfl (by decide)]
  rw [← h12]
  exact sepConj_mono h1 h2

theorem mid128_overlapWord7_entails_memRegion_23 (a : BitVec 64) (q : BitVec 128) (w16 : BitVec 64) :
    (a ↦₆₄ q.extractLsb' 0 64) ∗
      ((a + 8#64) ↦ₛ EncoderFromPb.loBytes7 (q.extractLsb' 64 64)) ∗
      ((a + 15#64) ↦₆₄ overlapWord7 (q.extractLsb' 64 64) w16) ⊢
      memRegion a 23 := by
  rw [← pointsTo128_loBytes7_eq a q w16]
  have h1 := pointsTo128_entails_memRegion_16 a q
  have h2 : ((a + 16#64) ↦ₛ EncoderFromPb.loBytes7 w16) ⊢ memRegion (a + 16#64) 7 := by
    rw [← EncoderFromPb.length_loBytes7 w16]
    exact ProofLib.pointsToBytes_entails_memRegion (a + 16#64) _
  have h12 : memRegion a 16 ∗ memRegion (a + 16#64) 7 = memRegion a 23 := by
    rw [← ProofLib.memRegion_split' (b := a) (n := 16) (k := 7) (b' := a + 16#64) rfl rfl (by decide)]
  rw [← h12]
  exact sepConj_mono h1 h2

theorem pointsTo32_entails_memRegion_4 (a : BitVec 64) (v : BitVec 32) :
    (a ↦₃₂ v) ⊢ memRegion a 4 :=
  IsBlock.entails (IsBlock.pointsTo32 a v) (IsBlock.memRegion a 4) fun _ _ => trivial

theorem pointsTo16_entails_memRegion_2 (a : BitVec 64) (v : BitVec 16) :
    (a ↦₁₆ v) ⊢ memRegion a 2 :=
  IsBlock.entails (IsBlock.pointsTo16 a v) (IsBlock.memRegion a 2) fun _ _ => trivial

theorem byte_32_16_8_entails_memRegion_8 (a : BitVec 64)
    (b0 : BitVec 8) (d1 : BitVec 32) (h5 : BitVec 16) (b7 : BitVec 8) :
    (a ↦₈ b0) ∗ ((a + 1#64) ↦₃₂ d1) ∗ ((a + 5#64) ↦₁₆ h5) ∗ ((a + 7#64) ↦₈ b7) ⊢
      memRegion a 8 := by
  have hm0 := pointsTo8_entails_memRegion a b0
  have hm1 := pointsTo32_entails_memRegion_4 (a + 1#64) d1
  have hm5 := pointsTo16_entails_memRegion_2 (a + 5#64) h5
  have hm7 := pointsTo8_entails_memRegion (a + 7#64) b7
  have hs5 : memRegion (a + 5#64) 2 ∗ memRegion (a + 7#64) 1 = memRegion (a + 5#64) 3 := by
    rw [← ProofLib.memRegion_split' (b := a + 5#64) (n := 2) (k := 1)
      (b' := a + 7#64) rfl (by bv_omega) (by decide)]
  have hs1 : memRegion (a + 1#64) 4 ∗ memRegion (a + 5#64) 3 = memRegion (a + 1#64) 7 := by
    rw [← ProofLib.memRegion_split' (b := a + 1#64) (n := 4) (k := 3)
      (b' := a + 5#64) rfl (by bv_omega) (by decide)]
  have hs0 : memRegion a 1 ∗ memRegion (a + 1#64) 7 = memRegion a 8 := by
    rw [← ProofLib.memRegion_split' (b := a) (n := 1) (k := 7)
      (b' := a + 1#64) rfl rfl (by decide)]
  rw [← hs0, ← hs1, ← hs5]
  refine Entails.trans (sepConj_mono_left hm0) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left hm1)) ?_
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono hm5 hm7))

theorem memRegion_16_entails_128 (a : BitVec 64) :
    memRegion a 16 ⊢ ∃∗ q : BitVec 128, (a ↦₁₂₈ q) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 8) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64),
      sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro w0
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w1
  rw [EncoderFromPb.pointsTo64_pair_eq_pointsTo128 a w0 w1]
  exact Entails.sepExists_right (w1 ++ w0) (Entails.refl _)

theorem pointsTo64_split_1_7 (a w : BitVec 64) :
    (a ↦₆₄ w) = (a ↦₈ EncoderFromPb.loByte w) ∗ ((a + 1#64) ↦ₛ EncoderFromPb.hiBytes7 w) := by
  rw [ProofLib.pointsTo64_eq_pointsToBytes a w,
      EncoderFromPb.unpack64_eq_loByte_cons_hiBytes7 w,
      ProofLib.pointsToBytes_cons]

theorem pointsTo64_split_7_1 (a w : BitVec 64) :
    (a ↦₆₄ w) = (a ↦ₛ EncoderFromPb.loBytes7 w) ∗ ((a + 7#64) ↦₈ EncoderFromPb.hiByte w) := by
  have hsplit : unpack64 w = EncoderFromPb.loBytes7 w ++ [EncoderFromPb.hiByte w] := by
    simp only [EncoderFromPb.loBytes7, EncoderFromPb.hiByte, unpack64]
    rfl
  rw [ProofLib.pointsTo64_eq_pointsToBytes a w, hsplit,
      ProofLib.pointsToBytes_append a (EncoderFromPb.loBytes7 w) [EncoderFromPb.hiByte w],
      EncoderFromPb.length_loBytes7, ProofLib.pointsToBytes_cons,
      ProofLib.pointsToBytes_nil, sepConj_emp]

theorem out_121_136_realign (out w887 : BitVec 64) :
    memRegion (out + 121#64) 7 ∗ ((out + 128#64) ↦₆₄ w887) ⊢
      ∃∗ u121 : BitVec 64,
        ((out + 121#64) ↦₆₄ u121) ∗ ((out + 129#64) ↦ₛ EncoderFromPb.hiBytes7 w887) := by
  rw [pointsTo64_split_1_7 (out + 128#64) w887]
  have ha : out + 128#64 + 1#64 = out + 129#64 := by bv_omega
  rw [ha, ← sepConj_assoc]
  have hm8 := pointsTo8_entails_memRegion (out + 128#64) (EncoderFromPb.loByte w887)
  have hm : memRegion (out + 121#64) 7 ∗ memRegion (out + 128#64) 1 = memRegion (out + 121#64) 8 := by
    rw [← ProofLib.memRegion_split' (b := out + 121#64) (n := 7) (k := 1)
      (b' := out + 128#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans (sepConj_mono_left (sepConj_mono_right hm8)) ?_
  rw [hm, ProofLib.memRegion_eight (out + 121#64), sepExists_sepConj_left]
  exact Entails.refl _

theorem out_145_168_realign (out : BitVec 64) (q848 : BitVec 128) :
    ((out + 145#64) ↦₁₂₈ q848) ∗ memRegion (out + 161#64) 7 ⊢
      ∃∗ u160 : BitVec 64,
        ((out + 145#64) ↦₆₄ q848.extractLsb' 0 64) ∗
        ((out + 153#64) ↦ₛ EncoderFromPb.loBytes7 (q848.extractLsb' 64 64)) ∗
        ((out + 160#64) ↦₆₄ u160) := by
  rw [pointsTo128_eq_pair64 (out + 145#64) q848]
  have ha1 : out + 145#64 + 8#64 = out + 153#64 := by bv_omega
  rw [ha1, pointsTo64_split_7_1 (out + 153#64) (q848.extractLsb' 64 64)]
  have ha2 : out + 153#64 + 7#64 = out + 160#64 := by bv_omega
  rw [ha2]
  have hm1 := pointsTo8_entails_memRegion (out + 160#64) (EncoderFromPb.hiByte (q848.extractLsb' 64 64))
  have hm8 : memRegion (out + 160#64) 1 ∗ memRegion (out + 161#64) 7 = memRegion (out + 160#64) 8 := by
    rw [← ProofLib.memRegion_split' (b := out + 160#64) (n := 1) (k := 7)
      (b' := out + 161#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans
    (Entails.of_eq (show _ =
      ((out + 145#64) ↦₆₄ q848.extractLsb' 0 64) ∗
      ((out + 153#64) ↦ₛ EncoderFromPb.loBytes7 (q848.extractLsb' 64 64)) ∗
      (((out + 160#64) ↦₈ EncoderFromPb.hiByte (q848.extractLsb' 64 64)) ∗
       memRegion (out + 161#64) 7) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hm1))) ?_
  rw [hm8, ProofLib.memRegion_eight (out + 160#64), sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro u160
  refine Entails.sepExists_right u160 ?_
  exact Entails.of_eq (by ac_rfl)

theorem out_537_560_realign (out w591 : BitVec 64) :
    memRegion (out + 537#64) 15 ∗ ((out + 552#64) ↦₆₄ w591) ⊢
      ∃∗ q537 : BitVec 128,
        ((out + 537#64) ↦₁₂₈ q537) ∗ ((out + 553#64) ↦ₛ EncoderFromPb.hiBytes7 w591) := by
  rw [pointsTo64_split_1_7 (out + 552#64) w591]
  have ha : out + 552#64 + 1#64 = out + 553#64 := by bv_omega
  rw [ha, ← sepConj_assoc]
  have hm8 := pointsTo8_entails_memRegion (out + 552#64) (EncoderFromPb.loByte w591)
  have hm : memRegion (out + 537#64) 15 ∗ memRegion (out + 552#64) 1 = memRegion (out + 537#64) 16 := by
    rw [← ProofLib.memRegion_split' (b := out + 537#64) (n := 15) (k := 1)
      (b' := out + 552#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans (sepConj_mono_left (sepConj_mono_right hm8)) ?_
  rw [hm]
  refine Entails.trans (sepConj_mono_left (memRegion_16_entails_128 (out + 537#64))) ?_
  rw [sepExists_sepConj_left]
  exact Entails.refl _

/-- Step A of the shared `Ok` epilogue (`+8180 -> +8284`, 26 instructions). -/
@[expose] def epilogueOutPartA (out : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : BitVec 64)
    (b96 : BitVec 8) (d97 : BitVec 32) (h101 : BitVec 16)
    (q145 q264 q280 q296 q312 q328 q344 q360 q376 : BitVec 128) : SepProp :=
  (out ↦₆₄ w0) ∗ ((out + 8#64) ↦₆₄ w8) ∗ ((out + 16#64) ↦₆₄ w16) ∗ ((out + 24#64) ↦₆₄ w24) ∗
  ((out + 32#64) ↦₆₄ w32) ∗ ((out + 40#64) ↦₆₄ w40) ∗ ((out + 48#64) ↦₆₄ w48) ∗ ((out + 56#64) ↦₆₄ w56) ∗
  ((out + 64#64) ↦₆₄ w64) ∗ ((out + 72#64) ↦₆₄ w72) ∗ ((out + 80#64) ↦₆₄ w80) ∗ ((out + 88#64) ↦₆₄ w88) ∗
  ((out + 96#64) ↦₈ b96) ∗ ((out + 97#64) ↦₃₂ d97) ∗ ((out + 101#64) ↦₁₆ h101) ∗
  ((out + 145#64) ↦₁₂₈ q145) ∗
  ((out + 264#64) ↦₁₂₈ q264) ∗ ((out + 280#64) ↦₁₂₈ q280) ∗
  ((out + 296#64) ↦₁₂₈ q296) ∗ ((out + 312#64) ↦₁₂₈ q312) ∗
  ((out + 328#64) ↦₁₂₈ q328) ∗ ((out + 344#64) ↦₁₂₈ q344) ∗
  ((out + 360#64) ↦₁₂₈ q360) ∗ ((out + 376#64) ↦₁₂₈ q376)

@[expose] def epilogueStackPartA (fsp : BitVec 64)
    (w208 w880 : BitVec 64)
    (q704 q720 q736 q752 q768 q784 q800 q816 q848 : BitVec 128) : SepProp :=
  ((fsp + 208#64) ↦₆₄ w208) ∗
  ((fsp + 704#64) ↦₁₂₈ q704) ∗ ((fsp + 720#64) ↦₁₂₈ q720) ∗
  ((fsp + 736#64) ↦₁₂₈ q736) ∗ ((fsp + 752#64) ↦₁₂₈ q752) ∗
  ((fsp + 768#64) ↦₁₂₈ q768) ∗ ((fsp + 784#64) ↦₁₂₈ q784) ∗
  ((fsp + 800#64) ↦₁₂₈ q800) ∗ ((fsp + 816#64) ↦₁₂₈ q816) ∗
  ((fsp + 848#64) ↦₁₂₈ q848) ∗ ((fsp + 880#64) ↦₆₄ w880)

@[expose] def overlapLow7 (u0 w7 : BitVec 64) : BitVec 64 :=
  (u0 &&& 0x00ffffffffffffff#64) ||| (w7 <<< 56)

theorem loBytes7_append_unpack64_eq (u0 w7 : BitVec 64) :
    EncoderFromPb.loBytes7 u0 ++ unpack64 w7 =
      unpack64 (overlapLow7 u0 w7) ++ EncoderFromPb.hiBytes7 w7 := by
  simp only [EncoderFromPb.loBytes7, EncoderFromPb.hiBytes7, unpack64, overlapLow7,
    List.take, List.drop, List.cons_append, List.nil_append, List.cons.injEq]
  exact ⟨by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel,
    by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel, trivial⟩

theorem loBytes7_pointsTo64_eq_overlap (a u0 w7 : BitVec 64) :
    (a ↦ₛ EncoderFromPb.loBytes7 u0) ∗ ((a + 7#64) ↦₆₄ w7) =
      (a ↦₆₄ overlapLow7 u0 w7) ∗ ((a + 8#64) ↦ₛ EncoderFromPb.hiBytes7 w7) := by
  rw [ProofLib.pointsTo64_eq_pointsToBytes (a + 7#64) w7,
      ProofLib.pointsTo64_eq_pointsToBytes a (overlapLow7 u0 w7)]
  have h1 := (ProofLib.pointsToBytes_append a (EncoderFromPb.loBytes7 u0) (unpack64 w7)).symm
  rw [EncoderFromPb.length_loBytes7] at h1
  have h2 := (ProofLib.pointsToBytes_append a (unpack64 (overlapLow7 u0 w7))
    (EncoderFromPb.hiBytes7 w7)).symm
  rw [unpack64_length] at h2
  rw [h1, h2, loBytes7_append_unpack64_eq]

theorem out_121_realign_rest (out u121 w887 : BitVec 64) (Rest : SepProp) :
    ((out + 121#64) ↦ₛ EncoderFromPb.loBytes7 u121) ∗ ((out + 128#64) ↦₆₄ w887) ∗ Rest =
      ((out + 121#64) ↦₆₄ overlapLow7 u121 w887) ∗
      ((out + 129#64) ↦ₛ EncoderFromPb.hiBytes7 w887) ∗ Rest := by
  have h := loBytes7_pointsTo64_eq_overlap (out + 121#64) u121 w887
  have ha7 : out + 121#64 + 7#64 = out + 128#64 := by bv_omega
  have ha8 : out + 121#64 + 8#64 = out + 129#64 := by bv_omega
  rw [ha7, ha8] at h
  rw [← sepConj_assoc, h, sepConj_assoc]

theorem out_545_realign_rest (out u545 w591 : BitVec 64) (Rest : SepProp) :
    ((out + 545#64) ↦ₛ EncoderFromPb.loBytes7 u545) ∗ ((out + 552#64) ↦₆₄ w591) ∗ Rest =
      ((out + 545#64) ↦₆₄ overlapLow7 u545 w591) ∗
      ((out + 553#64) ↦ₛ EncoderFromPb.hiBytes7 w591) ∗ Rest := by
  have h := loBytes7_pointsTo64_eq_overlap (out + 545#64) u545 w591
  have ha7 : out + 545#64 + 7#64 = out + 552#64 := by bv_omega
  have ha8 : out + 545#64 + 8#64 = out + 553#64 := by bv_omega
  rw [ha7, ha8] at h
  rw [← sepConj_assoc, h, sepConj_assoc]

theorem fsp_584_realign_rest (fsp w584 w592 : BitVec 64) (Rest : SepProp) :
    ((fsp + 584#64) ↦₆₄ w584) ∗ ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592) ∗ Rest =
      ((fsp + 584#64) ↦ₛ EncoderFromPb.loBytes7 w584) ∗
      ((fsp + 591#64) ↦₆₄ overlapWord7 w584 w592) ∗ Rest := by
  have h := pointsTo64_loBytes7_eq_loBytes7_overlapWord7 (fsp + 584#64) w584 w592
  have ha8 : fsp + 584#64 + 8#64 = fsp + 592#64 := by bv_omega
  have ha7 : fsp + 584#64 + 7#64 = fsp + 591#64 := by bv_omega
  rw [ha8, ha7] at h
  rw [← sepConj_assoc, h, sepConj_assoc]

/-- Precondition `out` cells for Step B (`+8284 -> +8468`, 46 instructions). -/
@[expose] def epilogueOutPartBPre (out : BitVec 64)
    (ub103 : BitVec 8) (u104 u112 : BitVec 64) (ub120 : BitVec 8)
    (u121 u128 u136 : BitVec 64) (ub144 : BitVec 8) (u160 : BitVec 64)
    (uq168 uq184 uq200 uq216 uq232 uq248 : BitVec 128)
    (u392 u400 u408 u416 u424 u432 u440 u448 u456 u464 u472 u480 u488 u496 u504 u512 u520 u528 : BitVec 64)
    (ub536 : BitVec 8) (u537 u545 u552 : BitVec 64) : SepProp :=
  ((out + 103#64) ↦₈ ub103) ∗
  ((out + 104#64) ↦₆₄ u104) ∗ ((out + 112#64) ↦₆₄ u112) ∗
  ((out + 120#64) ↦₈ ub120) ∗
  ((out + 121#64) ↦ₛ EncoderFromPb.loBytes7 u121) ∗ ((out + 128#64) ↦₆₄ u128) ∗
  ((out + 136#64) ↦₆₄ u136) ∗
  ((out + 144#64) ↦₈ ub144) ∗ ((out + 160#64) ↦₆₄ u160) ∗
  ((out + 168#64) ↦₁₂₈ uq168) ∗ ((out + 184#64) ↦₁₂₈ uq184) ∗
  ((out + 200#64) ↦₁₂₈ uq200) ∗ ((out + 216#64) ↦₁₂₈ uq216) ∗
  ((out + 232#64) ↦₁₂₈ uq232) ∗ ((out + 248#64) ↦₁₂₈ uq248) ∗
  ((out + 392#64) ↦₆₄ u392) ∗ ((out + 400#64) ↦₆₄ u400) ∗
  ((out + 408#64) ↦₆₄ u408) ∗ ((out + 416#64) ↦₆₄ u416) ∗
  ((out + 424#64) ↦₆₄ u424) ∗ ((out + 432#64) ↦₆₄ u432) ∗
  ((out + 440#64) ↦₆₄ u440) ∗ ((out + 448#64) ↦₆₄ u448) ∗
  ((out + 456#64) ↦₆₄ u456) ∗ ((out + 464#64) ↦₆₄ u464) ∗
  ((out + 472#64) ↦₆₄ u472) ∗ ((out + 480#64) ↦₆₄ u480) ∗
  ((out + 488#64) ↦₆₄ u488) ∗ ((out + 496#64) ↦₆₄ u496) ∗
  ((out + 504#64) ↦₆₄ u504) ∗ ((out + 512#64) ↦₆₄ u512) ∗
  ((out + 520#64) ↦₆₄ u520) ∗ ((out + 528#64) ↦₆₄ u528) ∗
  ((out + 536#64) ↦₈ ub536) ∗
  ((out + 537#64) ↦₆₄ u537) ∗ ((out + 545#64) ↦ₛ EncoderFromPb.loBytes7 u545) ∗
  ((out + 552#64) ↦₆₄ u552)

/-- Postcondition `out` cells for Step B (`+8284 -> +8468`, 46 instructions). -/
@[expose] def epilogueOutPartBPost (out : BitVec 64)
    (b103 : BitVec 8) (w104 w112 : BitVec 64) (b120 : BitVec 8)
    (w121 w128 w136 : BitVec 64) (b144 : BitVec 8) (w160 : BitVec 64)
    (q168 q184 q200 q216 q232 q248 : BitVec 128)
    (w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w488 w496 w504 w512 w520 w528 : BitVec 64)
    (b536 : BitVec 8) (q537 : BitVec 128) (w552 : BitVec 64) : SepProp :=
  ((out + 103#64) ↦₈ b103) ∗
  ((out + 104#64) ↦₆₄ w104) ∗ ((out + 112#64) ↦₆₄ w112) ∗
  ((out + 120#64) ↦₈ b120) ∗
  ((out + 121#64) ↦₆₄ w121) ∗ ((out + 129#64) ↦ₛ EncoderFromPb.hiBytes7 w128) ∗
  ((out + 136#64) ↦₆₄ w136) ∗
  ((out + 144#64) ↦₈ b144) ∗ ((out + 160#64) ↦₆₄ w160) ∗
  ((out + 168#64) ↦₁₂₈ q168) ∗ ((out + 184#64) ↦₁₂₈ q184) ∗
  ((out + 200#64) ↦₁₂₈ q200) ∗ ((out + 216#64) ↦₁₂₈ q216) ∗
  ((out + 232#64) ↦₁₂₈ q232) ∗ ((out + 248#64) ↦₁₂₈ q248) ∗
  ((out + 392#64) ↦₆₄ w392) ∗ ((out + 400#64) ↦₆₄ w400) ∗
  ((out + 408#64) ↦₆₄ w408) ∗ ((out + 416#64) ↦₆₄ w416) ∗
  ((out + 424#64) ↦₆₄ w424) ∗ ((out + 432#64) ↦₆₄ w432) ∗
  ((out + 440#64) ↦₆₄ w440) ∗ ((out + 448#64) ↦₆₄ w448) ∗
  ((out + 456#64) ↦₆₄ w456) ∗ ((out + 464#64) ↦₆₄ w464) ∗
  ((out + 472#64) ↦₆₄ w472) ∗ ((out + 480#64) ↦₆₄ w480) ∗
  ((out + 488#64) ↦₆₄ w488) ∗ ((out + 496#64) ↦₆₄ w496) ∗
  ((out + 504#64) ↦₆₄ w504) ∗ ((out + 512#64) ↦₆₄ w512) ∗
  ((out + 520#64) ↦₆₄ w520) ∗ ((out + 528#64) ↦₆₄ w528) ∗
  ((out + 536#64) ↦₈ b536) ∗
  ((out + 537#64) ↦₁₂₈ q537) ∗ ((out + 553#64) ↦ₛ EncoderFromPb.hiBytes7 w552)

/-- Precondition stack cells for Step B (`+8284 -> +8468`). -/
@[expose] def epilogueStackPartBPre (fsp : BitVec 64)
    (d92 d172 : BitVec 32)
    (w104 w112 w120 w160 w192 w224 w232 w592 w832 w863 w887 : BitVec 64)
    (q576 q608 q624 q640 q656 q672 q688 : BitVec 128) : SepProp :=
  ((fsp + 92#64) ↦₃₂ d92) ∗
  ((fsp + 104#64) ↦₆₄ w104) ∗ ((fsp + 112#64) ↦₆₄ w112) ∗ ((fsp + 120#64) ↦₆₄ w120) ∗
  ((fsp + 160#64) ↦₆₄ w160) ∗ ((fsp + 172#64) ↦₃₂ d172) ∗ ((fsp + 192#64) ↦₆₄ w192) ∗
  ((fsp + 224#64) ↦₆₄ w224) ∗ ((fsp + 232#64) ↦₆₄ w232) ∗
  ((fsp + 576#64) ↦₁₂₈ q576) ∗ ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592) ∗
  ((fsp + 608#64) ↦₁₂₈ q608) ∗ ((fsp + 624#64) ↦₁₂₈ q624) ∗
  ((fsp + 640#64) ↦₁₂₈ q640) ∗ ((fsp + 656#64) ↦₁₂₈ q656) ∗
  ((fsp + 672#64) ↦₁₂₈ q672) ∗ ((fsp + 688#64) ↦₁₂₈ q688) ∗
  ((fsp + 832#64) ↦₆₄ w832) ∗ ((fsp + 863#64) ↦₆₄ w863) ∗ ((fsp + 887#64) ↦₆₄ w887)

/-- Postcondition stack cells for Step B (`+8284 -> +8468`). -/
@[expose] def epilogueStackPartBPost (fsp : BitVec 64)
    (d92 d172 : BitVec 32)
    (w104 w112 w120 w160 w192 w224 w232 w592 w832 w863 w887 : BitVec 64)
    (q576 q608 q624 q640 q656 q672 q688 : BitVec 128) : SepProp :=
  ((fsp + 92#64) ↦₃₂ d92) ∗
  ((fsp + 104#64) ↦₆₄ w104) ∗ ((fsp + 112#64) ↦₆₄ w112) ∗ ((fsp + 120#64) ↦₆₄ w120) ∗
  ((fsp + 160#64) ↦₆₄ w160) ∗ ((fsp + 172#64) ↦₃₂ d172) ∗ ((fsp + 192#64) ↦₆₄ w192) ∗
  ((fsp + 224#64) ↦₆₄ w224) ∗ ((fsp + 232#64) ↦₆₄ w232) ∗
  ((fsp + 576#64) ↦₆₄ q576.extractLsb' 0 64) ∗
  ((fsp + 584#64) ↦ₛ EncoderFromPb.loBytes7 (q576.extractLsb' 64 64)) ∗
  ((fsp + 591#64) ↦₆₄ overlapWord7 (q576.extractLsb' 64 64) w592) ∗
  ((fsp + 608#64) ↦₁₂₈ q608) ∗ ((fsp + 624#64) ↦₁₂₈ q624) ∗
  ((fsp + 640#64) ↦₁₂₈ q640) ∗ ((fsp + 656#64) ↦₁₂₈ q656) ∗
  ((fsp + 672#64) ↦₁₂₈ q672) ∗ ((fsp + 688#64) ↦₁₂₈ q688) ∗
  ((fsp + 832#64) ↦₆₄ w832) ∗ ((fsp + 863#64) ↦₆₄ w863) ∗ ((fsp + 887#64) ↦₆₄ w887)

@[local arm64_norm, local wp_norm]
theorem bv328_toNat : (328#64 : BitVec 64).toNat = 328 := rfl

/-- Split `memRegion out 928` into four 64-bit cells `[out .. out + 32]` and `memRegion (out + 32) 896`
    for the `+2044 / +2048` error exit. -/
theorem memRegion_out_928_split_32 (out : BitVec 64) :
    memRegion out chunkedStatesSize =
      (∃∗ v0 : BitVec 64, (out ↦₆₄ v0)) ∗
      (∃∗ v8 : BitVec 64, ((out + 8#64) ↦₆₄ v8)) ∗
      (∃∗ v16 : BitVec 64, ((out + 16#64) ↦₆₄ v16)) ∗
      (∃∗ v24 : BitVec 64, ((out + 24#64) ↦₆₄ v24)) ∗
      memRegion (out + 32#64) 896 := by
  unfold chunkedStatesSize
  rw [ProofLib.memRegion_split out 8 920 (by decide),
      ProofLib.memRegion_eight out,
      ProofLib.memRegion_split' (b := out + 8#64) (n := 8) (k := 912)
        (b' := out + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (out + 8#64),
      ProofLib.memRegion_split' (b := out + 16#64) (n := 8) (k := 904)
        (b' := out + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (out + 16#64),
      ProofLib.memRegion_split' (b := out + 24#64) (n := 8) (k := 896)
        (b' := out + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (out + 24#64)]

theorem pointsTo64_entails_byte_and_region7 (a w : BitVec 64) :
    (a ↦₆₄ w) ⊢ (a ↦₈ w.extractLsb' 0 8) ∗ memRegion (a + 1#64) 7 := by
  rw [pointsTo64_eq_pointsToBytes a w, unpack64_eq_loByte_cons_hiBytes7 w,
      ProofLib.pointsToBytes_cons]
  exact sepConj_mono_right (length_hiBytes7 w ▸ pointsToBytes_entails_memRegion (a + 1#64) (hiBytes7 w))

/-- Collapse `[out + 8] ↦₆₄ w8 ∗ [out + 16] ↦₆₄ w16 ∗ [out + 24] ↦₆₄ w24 ∗ memRegion (out + 32) 896`
    into `[out + 8] ↦₈ w8.extractLsb' 0 8 ∗ memRegion (out + 9) 919`. -/
theorem out_8_32_entails_err_tail (out w8 w16 w24 : BitVec 64) :
    ((out + 8#64) ↦₆₄ w8) ∗ ((out + 16#64) ↦₆₄ w16) ∗ ((out + 24#64) ↦₆₄ w24) ∗
      memRegion (out + 32#64) 896 ⊢
    ((out + 8#64) ↦₈ w8.extractLsb' 0 8) ∗ memRegion (out + 9#64) 919 := by
  have h8 : ((out + 8#64) ↦₆₄ w8) ⊢
      ((out + 8#64) ↦₈ w8.extractLsb' 0 8) ∗ memRegion (out + 9#64) 7 := by
    have h := pointsTo64_entails_byte_and_region7 (out + 8#64) w8
    rwa [show (out + 8#64) + 1#64 = out + 9#64 by bv_omega] at h
  have h16 := ProofLib.pointsTo64_entails_memRegion (out + 16#64) w16
  have h24 := ProofLib.pointsTo64_entails_memRegion (out + 24#64) w24
  rw [ProofLib.memRegion_split' (b := out + 9#64) (n := 7) (k := 912)
        (b' := out + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 16#64) (n := 8) (k := 904)
        (b' := out + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 24#64) (n := 8) (k := 896)
        (b' := out + 32#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans
    (sepConj_mono h8 (sepConj_mono h16 (sepConj_mono_left h24))) ?_
  exact Entails.of_eq (by ac_rfl)

@[expose] def IsTotalBlock (P : SepProp) (b : BitVec 64) (n : Nat) : Prop :=
  IsBlock P b n (fun _ => True)

theorem IsTotalBlock.memRegion (b : BitVec 64) (n : Nat) :
    IsTotalBlock (ProofLib.memRegion b n) b n :=
  IsBlock.memRegion b n

theorem IsTotalBlock.ex8 (b : BitVec 64) :
    IsTotalBlock (∃∗ v : BitVec 8, (b ↦₈ v)) b 1 :=
  (IsBlock.sepExists (IsBlock.pointsTo8 b)).cast rfl fun m =>
    ⟨fun _ => trivial, fun _ => ⟨m.read8 b, rfl⟩⟩

theorem IsTotalBlock.ex16 (b : BitVec 64) :
    IsTotalBlock (∃∗ v : BitVec 16, (b ↦₁₆ v)) b 2 :=
  (IsBlock.sepExists (IsBlock.pointsTo16 b)).cast rfl fun m =>
    ⟨fun _ => trivial, fun _ => ⟨m.read16 b, rfl⟩⟩

theorem IsTotalBlock.ex32 (b : BitVec 64) :
    IsTotalBlock (∃∗ v : BitVec 32, (b ↦₃₂ v)) b 4 :=
  (IsBlock.sepExists (IsBlock.pointsTo32 b)).cast rfl fun m =>
    ⟨fun _ => trivial, fun _ => ⟨m.read32 b, rfl⟩⟩

theorem IsTotalBlock.ex64 (b : BitVec 64) :
    IsTotalBlock (∃∗ v : BitVec 64, (b ↦₆₄ v)) b 8 :=
  (IsBlock.sepExists (IsBlock.pointsTo64 b)).cast rfl fun m =>
    ⟨fun _ => trivial, fun _ => ⟨m.read64 b, rfl⟩⟩

theorem IsTotalBlock.ex128 (b : BitVec 64) :
    IsTotalBlock (∃∗ v : BitVec 128, (b ↦₁₂₈ v)) b 16 :=
  (IsBlock.sepExists (IsBlock.pointsTo128 b)).cast rfl fun m =>
    ⟨fun _ => trivial, fun _ => ⟨m.read128 b, rfl⟩⟩

theorem IsTotalBlock.step {P Q : SepProp} {a o1 o2 : BitVec 64} {n k : Nat}
    (hP : IsTotalBlock P (a + o1) n) (hQ : IsTotalBlock Q (a + o2) k)
    (ho : o1 + BitVec.ofNat 64 n = o2 := by rfl)
    (hnk : n + k ≤ 2 ^ 64 := by decide) :
    IsTotalBlock (P ∗ Q) (a + o1) (n + k) := by
  have ha : a + o2 = (a + o1) + BitVec.ofNat 64 n := by rw [BitVec.add_assoc, ho]
  exact (hP.sepConj hQ ha hnk).cast rfl fun _ => ⟨fun _ => trivial, fun _ => ⟨trivial, trivial⟩⟩

theorem IsTotalBlock.step0 {P Q : SepProp} {a o2 : BitVec 64} {n k : Nat}
    (hP : IsTotalBlock P a n) (hQ : IsTotalBlock Q (a + o2) k)
    (ho : BitVec.ofNat 64 n = o2 := by rfl)
    (hnk : n + k ≤ 2 ^ 64 := by decide) :
    IsTotalBlock (P ∗ Q) a (n + k) := by
  have ha : a + o2 = a + BitVec.ofNat 64 n := by rw [ho]
  exact (hP.sepConj hQ ha hnk).cast rfl fun _ => ⟨fun _ => trivial, fun _ => ⟨trivial, trivial⟩⟩

theorem IsTotalBlock.to_eq {P : SepProp} {b : BitVec 64} {n m : Nat}
    (hP : IsTotalBlock P b n) (hnm : n = m := by rfl) :
    ProofLib.memRegion b m = P := by
  subst hnm
  exact IsBlock.eq (IsBlock.memRegion b n) hP fun _ => Iff.rfl

theorem split_step {P Q : SepProp} {a o1 o2 : BitVec 64} {n k : Nat}
    (hP : ProofLib.memRegion (a + o1) n ⊢ P) (hQ : ProofLib.memRegion (a + o2) k ⊢ Q)
    (ho : o1 + BitVec.ofNat 64 n = o2 := by rfl)
    (hnk : n + k ≤ 2 ^ 64 := by decide) :
    ProofLib.memRegion (a + o1) (n + k) ⊢ P ∗ Q := by
  rw [IsTotalBlock.to_eq (IsTotalBlock.step (IsTotalBlock.memRegion (a + o1) n)
    (IsTotalBlock.memRegion (a + o2) k) ho hnk) rfl]
  exact sepConj_mono hP hQ

theorem split_step0 {P Q : SepProp} {a o2 : BitVec 64} {n k : Nat}
    (hP : ProofLib.memRegion a n ⊢ P) (hQ : ProofLib.memRegion (a + o2) k ⊢ Q)
    (ho : BitVec.ofNat 64 n = o2 := by rfl)
    (hnk : n + k ≤ 2 ^ 64 := by decide) :
    ProofLib.memRegion a (n + k) ⊢ P ∗ Q := by
  rw [IsTotalBlock.to_eq (IsTotalBlock.step0 (IsTotalBlock.memRegion a n)
    (IsTotalBlock.memRegion (a + o2) k) ho hnk) rfl]
  exact sepConj_mono hP hQ

theorem split_top {P : SepProp} {b : BitVec 64} {n m : Nat}
    (hP : ProofLib.memRegion b n ⊢ P) (hnm : m = n := by rfl) :
    ProofLib.memRegion b m ⊢ P := hnm ▸ hP

theorem mem8_entails (b : BitVec 64) :
    ProofLib.memRegion b 1 ⊢ ∃∗ v : BitVec 8, (b ↦₈ v) :=
  Entails.of_eq (IsTotalBlock.to_eq (IsTotalBlock.ex8 b) rfl)

theorem mem16_entails (b : BitVec 64) :
    ProofLib.memRegion b 2 ⊢ ∃∗ v : BitVec 16, (b ↦₁₆ v) :=
  Entails.of_eq (IsTotalBlock.to_eq (IsTotalBlock.ex16 b) rfl)

theorem mem32_entails (b : BitVec 64) :
    ProofLib.memRegion b 4 ⊢ ∃∗ v : BitVec 32, (b ↦₃₂ v) :=
  Entails.of_eq (IsTotalBlock.to_eq (IsTotalBlock.ex32 b) rfl)

theorem mem64_entails (b : BitVec 64) :
    ProofLib.memRegion b 8 ⊢ ∃∗ v : BitVec 64, (b ↦₆₄ v) :=
  Entails.of_eq (IsTotalBlock.to_eq (IsTotalBlock.ex64 b) rfl)

theorem mem128_entails (b : BitVec 64) :
    ProofLib.memRegion b 16 ⊢ ∃∗ v : BitVec 128, (b ↦₁₂₈ v) :=
  Entails.of_eq (IsTotalBlock.to_eq (IsTotalBlock.ex128 b) rfl)

theorem collapse_step {P Q : SepProp} {a o1 o2 : BitVec 64} {n k : Nat}
    (hP : P ⊢ ProofLib.memRegion (a + o1) n) (hQ : Q ⊢ ProofLib.memRegion (a + o2) k)
    (ho : o1 + BitVec.ofNat 64 n = o2 := by rfl)
    (hnk : n + k ≤ 2 ^ 64 := by decide) :
    P ∗ Q ⊢ ProofLib.memRegion (a + o1) (n + k) := by
  rw [IsTotalBlock.to_eq (IsTotalBlock.step (IsTotalBlock.memRegion (a + o1) n)
    (IsTotalBlock.memRegion (a + o2) k) ho hnk) rfl]
  exact sepConj_mono hP hQ

theorem collapse_step0 {P Q : SepProp} {a o2 : BitVec 64} {n k : Nat}
    (hP : P ⊢ ProofLib.memRegion a n) (hQ : Q ⊢ ProofLib.memRegion (a + o2) k)
    (ho : BitVec.ofNat 64 n = o2 := by rfl)
    (hnk : n + k ≤ 2 ^ 64 := by decide) :
    P ∗ Q ⊢ ProofLib.memRegion a (n + k) := by
  rw [IsTotalBlock.to_eq (IsTotalBlock.step0 (IsTotalBlock.memRegion a n)
    (IsTotalBlock.memRegion (a + o2) k) ho hnk) rfl]
  exact sepConj_mono hP hQ

theorem collapse_top {P : SepProp} {b : BitVec 64} {n m : Nat}
    (hP : P ⊢ ProofLib.memRegion b n) (hnm : n = m := by rfl) :
    P ⊢ ProofLib.memRegion b m := hnm ▸ hP

theorem loBytes7_entails_memRegion_7 (a v : BitVec 64) :
    (a ↦ₛ EncoderFromPb.loBytes7 v) ⊢ ProofLib.memRegion a 7 :=
  EncoderFromPb.length_loBytes7 v ▸ ProofLib.pointsToBytes_entails_memRegion a _

theorem hiBytes7_entails_memRegion_7 (a v : BitVec 64) :
    (a ↦ₛ EncoderFromPb.hiBytes7 v) ⊢ ProofLib.memRegion a 7 :=
  EncoderFromPb.length_hiBytes7 v ▸ ProofLib.pointsToBytes_entails_memRegion a _

theorem memRegion_15_entails_loBytes7_and_64 (a : BitVec 64) :
    ProofLib.memRegion a 15 ⊢
      (∃∗ u0 : BitVec 64, (a ↦ₛ EncoderFromPb.loBytes7 u0)) ∗
      (∃∗ u7 : BitVec 64, ((a + 7#64) ↦₆₄ u7)) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 7) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_eight a, sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro u0
  rw [pointsTo64_split_7_1 a u0, sepConj_assoc]
  have hm1 := pointsTo8_entails_memRegion (a + 7#64) (EncoderFromPb.hiByte u0)
  have hm8 : ProofLib.memRegion (a + 7#64) 1 ∗ ProofLib.memRegion (a + 8#64) 7 =
      ProofLib.memRegion (a + 7#64) 8 := by
    rw [← ProofLib.memRegion_split' (b := a + 7#64) (n := 1) (k := 7)
      (b' := a + 8#64) rfl (by bv_omega) (by decide)]
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_right u0 ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left hm1)) ?_
  rw [hm8, ProofLib.memRegion_eight (a + 7#64)]
  exact Entails.refl _

end CryptoVerification.SpqrV1.States.FromPb

