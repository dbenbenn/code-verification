/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Epilogue -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2a -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8c
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 8 (`EkReceivedCt1Sampled`, `+1764`) — Part D

`<PolyEncoder>::from_pb` setup and result dispatch (`+10836 -> +10900`, `+10904 -> +10916 | +11264`),
5-vector error cleanup (`+10916 -> +4240`), and `Ok(enc)` epilogue staging (`+11264 -> +8180`).
-/

public section

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append



/-! ## 1. `PolyEncoder::from_pb` Result Check (`+10904`) and Error Cleanup (`+10916 -> +4240`) -/

theorem v8_fsp_248_split_for_stur (fsp z248 z256 z264 : BitVec 64) (Rest : SepProp) :
    ((fsp + 248#64) ↦₆₄ z248) ∗ ((fsp + 256#64) ↦₆₄ z256) ∗
      ((fsp + 264#64) ↦₆₄ z264) ∗ Rest =
    ((fsp + 248#64) ↦₈ loByte z248) ∗
      ((fsp + 249#64) ↦₆₄ unshiftWord z248 (loByte z256)) ∗
      ((fsp + 257#64) ↦₆₄ unshiftWord z256 (loByte z264)) ∗
      ((fsp + 265#64) ↦ₛ loBytes7 (unshiftWord z264 0#8)) ∗ Rest := by
  have h := v10_triple64_eq_byte_q128_tail7 (fsp + 248#64) z248 z256 z264
  unfold pointsTo128 at h
  have ha256 : (fsp + 248#64) + 8#64 = fsp + 256#64 := by bv_omega
  have ha264 : (fsp + 248#64) + 16#64 = fsp + 264#64 := by bv_omega
  have ha249 : (fsp + 248#64) + 1#64 = fsp + 249#64 := by bv_omega
  have ha257 : (fsp + 249#64) + 8#64 = fsp + 257#64 := by bv_omega
  have ha265 : (fsp + 248#64) + 17#64 = fsp + 265#64 := by bv_omega
  have hlo : (unshiftWord z256 (loByte z264) ++ unshiftWord z248 (loByte z256)).extractLsb' 0 64 =
      unshiftWord z248 (loByte z256) := by bv_kernel
  have hhi : (unshiftWord z256 (loByte z264) ++ unshiftWord z248 (loByte z256)).extractLsb' 64 64 =
      unshiftWord z256 (loByte z264) := by bv_kernel
  rw [ha256, ha264, ha249, ha257, ha265, hlo, hhi, ← v8_loBytes7_unshiftWord z264 0#8] at h
  have h' := congrArg (· ∗ Rest) h
  exact Eq.trans (by ac_rfl) (Eq.trans h' (by ac_rfl))

theorem v8_resultPolyEncoder_err_entails_tag_392 (A : RustAlloc) (fsp : BitVec 64)
    (err : PolynomialError) :
    resultPolyEncoderFromPbAt A (fsp + 1888#64) (.error err) ⊢
      ((fsp + 1888#64) ↦₆₄ 2#64) ∗ memRegion (fsp + 1896#64) 392 := by
  dsimp only [resultPolyEncoderFromPbAt, polyEncoderNicheTag,
    resultPolyEncoderErrByteOff, resultPolyEncoderErrTailSize]
  have hm8 : ((fsp + 1896#64) ↦₈ polynomialErrorByte err) ∗ memRegion (fsp + 1897#64) 391 ⊢
      memRegion (fsp + 1896#64) 392 := by
    rw [ProofLib.memRegion_split' (b := fsp + 1896#64) (n := 1) (k := 391)
          (b' := fsp + 1897#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (ProofLib.pointsTo8_entails_memRegion (fsp + 1896#64) (polynomialErrorByte err))
  have ha1896 : (fsp + 1888#64) + 8#64 = fsp + 1896#64 := by bv_omega
  have ha1897 : (fsp + 1888#64) + 9#64 = fsp + 1897#64 := by bv_omega
  rw [ha1896, ha1897]
  exact sepConj_mono_right hm8

/-! ## 3. `PolyEncoder` Cell Unpacking / Relocation (`fsp + 1888 -> out + 8`) -/

/-- Pack 8 bytes (little-endian) from `bs` into a `BitVec 64`. -/
@[expose] def v8_pack64 (bs : List (BitVec 8)) : BitVec 64 :=
  (bs.getD 7 0#8) ++ (bs.getD 6 0#8) ++ (bs.getD 5 0#8) ++ (bs.getD 4 0#8) ++
  (bs.getD 3 0#8) ++ (bs.getD 2 0#8) ++ (bs.getD 1 0#8) ++ (bs.getD 0 0#8)

theorem v8_unpack64_pack64 (bs : List (BitVec 8)) (h : bs.length = 8) :
    unpack64 (v8_pack64 bs) = bs := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try (simp at h; done)
  change [_, _, _, _, _, _, _, _] = [b0, b1, b2, b3, b4, b5, b6, b7]
  dsimp only [v8_pack64, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
  simp only [List.cons.injEq, and_true]
  exact ⟨by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel,
         by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel⟩

theorem v8_pointsToBytes_eq_pack64 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 8) :
    (a ↦ₛ bs) = (a ↦₆₄ v8_pack64 bs) := by
  rw [pointsTo64_eq_pointsToBytes, v8_unpack64_pack64 bs h]

/-- Pack 16 bytes (little-endian) from `bs` into a `BitVec 128`. -/
@[expose] def v8_pack128 (bs : List (BitVec 8)) : BitVec 128 :=
  v8_pack64 (bs.drop 8) ++ v8_pack64 (bs.take 8)

theorem v8_pointsToBytes_eq_pack128 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 16) :
    (a ↦ₛ bs) = (a ↦₁₂₈ v8_pack128 bs) := by
  have h1 : (bs.take 8).length = 8 := by simp [h]
  have h2 : (bs.drop 8).length = 8 := by simp [h]
  nth_rw 1 [← List.take_append_drop 8 bs]
  rw [ProofLib.pointsToBytes_append a (bs.take 8) (bs.drop 8), h1]
  change (a ↦ₛ bs.take 8) ∗ ((a + 8#64) ↦ₛ bs.drop 8) = (a ↦₁₂₈ v8_pack128 bs)
  rw [v8_pointsToBytes_eq_pack64 a (bs.take 8) h1,
      v8_pointsToBytes_eq_pack64 (a + 8#64) (bs.drop 8) h2,
      pointsTo64_pair_eq_pointsTo128]
  rfl

/-- 8-byte word at byte offset `i` within `bs`. -/
@[expose] def v8_wordAt (bs : List (BitVec 8)) (i : Nat) : BitVec 64 :=
  v8_pack64 ((bs.drop i).take 8)

/-- 16-byte quadword at byte offset `i` within `bs`. -/
@[expose] def v8_quadAt (bs : List (BitVec 8)) (i : Nat) : BitVec 128 :=
  v8_pack128 ((bs.drop i).take 16)

theorem v8_bs_drop_step8 {bs : List (BitVec 8)} (hbs : bs.length = 384)
    (a o1 o2 : BitVec 64) (i : Nat) {Q : SepProp}
    (hrest : ((a + o2) ↦ₛ bs.drop (i + 8)) = Q)
    (hi : i + 8 ≤ 384 := by decide)
    (ho : o1 + 8#64 = o2 := by rfl) :
    ((a + o1) ↦ₛ bs.drop i) = ((a + o1) ↦₆₄ v8_wordAt bs i) ∗ Q := by
  have htake_len : ((bs.drop i).take 8).length = 8 := by
    rw [List.length_take, List.length_drop, hbs]; omega
  have hsplit : bs.drop i = (bs.drop i).take 8 ++ bs.drop (i + 8) := by
    rw [← List.drop_drop, List.take_append_drop]
  have ha : (a + o1) + BitVec.ofNat 64 ((bs.drop i).take 8).length = a + o2 := by
    rw [htake_len, BitVec.add_assoc, ho]
  rw [hsplit, ProofLib.pointsToBytes_append (a + o1) ((bs.drop i).take 8) (bs.drop (i + 8)),
      ha, v8_pointsToBytes_eq_pack64 (a + o1) ((bs.drop i).take 8) htake_len, hrest]
  rfl

theorem v8_bs_drop_step16 {bs : List (BitVec 8)} (hbs : bs.length = 384)
    (a o1 o2 : BitVec 64) (i : Nat) {Q : SepProp}
    (hrest : ((a + o2) ↦ₛ bs.drop (i + 16)) = Q)
    (hi : i + 16 ≤ 384 := by decide)
    (ho : o1 + 16#64 = o2 := by rfl) :
    ((a + o1) ↦ₛ bs.drop i) = ((a + o1) ↦₁₂₈ v8_quadAt bs i) ∗ Q := by
  have htake_len : ((bs.drop i).take 16).length = 16 := by
    rw [List.length_take, List.length_drop, hbs]; omega
  have hsplit : bs.drop i = (bs.drop i).take 16 ++ bs.drop (i + 16) := by
    rw [← List.drop_drop, List.take_append_drop]
  have ha : (a + o1) + BitVec.ofNat 64 ((bs.drop i).take 16).length = a + o2 := by
    rw [htake_len, BitVec.add_assoc, ho]
  rw [hsplit, ProofLib.pointsToBytes_append (a + o1) ((bs.drop i).take 16) (bs.drop (i + 16)),
      ha, v8_pointsToBytes_eq_pack128 (a + o1) ((bs.drop i).take 16) htake_len, hrest]
  rfl

theorem v8_bs_drop_end8 {bs : List (BitVec 8)} (hbs : bs.length = 384)
    (a o1 : BitVec 64) :
    ((a + o1) ↦ₛ bs.drop 376) = ((a + o1) ↦₆₄ v8_wordAt bs 376) := by
  have hlen : (bs.drop 376).length = 8 := by rw [List.length_drop, hbs]
  have htake : (bs.drop 376).take 8 = bs.drop 376 := List.take_of_length_le (by omega)
  rw [v8_pointsToBytes_eq_pack64 (a + o1) (bs.drop 376) hlen]
  unfold v8_wordAt
  rw [htake]

@[expose] def v8_encCellsAt (a : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ((a + 8#64) ↦₆₄ v8_wordAt bs 0) ∗
  ((a + 16#64) ↦₆₄ v8_wordAt bs 8) ∗
  ((a + 24#64) ↦₆₄ v8_wordAt bs 16) ∗
  ((a + 32#64) ↦₆₄ v8_wordAt bs 24) ∗
  ((a + 40#64) ↦₆₄ v8_wordAt bs 32) ∗
  ((a + 48#64) ↦₆₄ v8_wordAt bs 40) ∗
  ((a + 56#64) ↦₆₄ v8_wordAt bs 48) ∗
  ((a + 64#64) ↦₆₄ v8_wordAt bs 56) ∗
  ((a + 72#64) ↦₆₄ v8_wordAt bs 64) ∗
  ((a + 80#64) ↦₆₄ v8_wordAt bs 72) ∗
  ((a + 88#64) ↦₆₄ v8_wordAt bs 80) ∗
  ((a + 96#64) ↦₆₄ v8_wordAt bs 88) ∗
  ((a + 104#64) ↦₆₄ v8_wordAt bs 96) ∗
  ((a + 112#64) ↦₆₄ v8_wordAt bs 104) ∗
  ((a + 120#64) ↦₆₄ v8_wordAt bs 112) ∗
  ((a + 128#64) ↦₆₄ v8_wordAt bs 120) ∗
  ((a + 136#64) ↦₆₄ v8_wordAt bs 128) ∗
  ((a + 144#64) ↦₆₄ v8_wordAt bs 136) ∗
  ((a + 152#64) ↦₆₄ v8_wordAt bs 144) ∗
  ((a + 160#64) ↦₁₂₈ v8_quadAt bs 152) ∗
  ((a + 176#64) ↦₁₂₈ v8_quadAt bs 168) ∗
  ((a + 192#64) ↦₁₂₈ v8_quadAt bs 184) ∗
  ((a + 208#64) ↦₁₂₈ v8_quadAt bs 200) ∗
  ((a + 224#64) ↦₁₂₈ v8_quadAt bs 216) ∗
  ((a + 240#64) ↦₁₂₈ v8_quadAt bs 232) ∗
  ((a + 256#64) ↦₁₂₈ v8_quadAt bs 248) ∗
  ((a + 272#64) ↦₁₂₈ v8_quadAt bs 264) ∗
  ((a + 288#64) ↦₁₂₈ v8_quadAt bs 280) ∗
  ((a + 304#64) ↦₁₂₈ v8_quadAt bs 296) ∗
  ((a + 320#64) ↦₁₂₈ v8_quadAt bs 312) ∗
  ((a + 336#64) ↦₁₂₈ v8_quadAt bs 328) ∗
  ((a + 352#64) ↦₁₂₈ v8_quadAt bs 344) ∗
  ((a + 368#64) ↦₁₂₈ v8_quadAt bs 360) ∗
  ((a + 384#64) ↦₆₄ v8_wordAt bs 376)

theorem v8_bs384_eq_encCells (bs : List (BitVec 8)) (hbs : bs.length = 384) (a : BitVec 64) :
    ((a + 8#64) ↦ₛ bs) = v8_encCellsAt a bs := by
  unfold v8_encCellsAt
  change ((a + 8#64) ↦ₛ bs.drop 0) = _
  exact
    v8_bs_drop_step8 hbs a 8#64 16#64 0 <|
    v8_bs_drop_step8 hbs a 16#64 24#64 8 <|
    v8_bs_drop_step8 hbs a 24#64 32#64 16 <|
    v8_bs_drop_step8 hbs a 32#64 40#64 24 <|
    v8_bs_drop_step8 hbs a 40#64 48#64 32 <|
    v8_bs_drop_step8 hbs a 48#64 56#64 40 <|
    v8_bs_drop_step8 hbs a 56#64 64#64 48 <|
    v8_bs_drop_step8 hbs a 64#64 72#64 56 <|
    v8_bs_drop_step8 hbs a 72#64 80#64 64 <|
    v8_bs_drop_step8 hbs a 80#64 88#64 72 <|
    v8_bs_drop_step8 hbs a 88#64 96#64 80 <|
    v8_bs_drop_step8 hbs a 96#64 104#64 88 <|
    v8_bs_drop_step8 hbs a 104#64 112#64 96 <|
    v8_bs_drop_step8 hbs a 112#64 120#64 104 <|
    v8_bs_drop_step8 hbs a 120#64 128#64 112 <|
    v8_bs_drop_step8 hbs a 128#64 136#64 120 <|
    v8_bs_drop_step8 hbs a 136#64 144#64 128 <|
    v8_bs_drop_step8 hbs a 144#64 152#64 136 <|
    v8_bs_drop_step8 hbs a 152#64 160#64 144 <|
    v8_bs_drop_step16 hbs a 160#64 176#64 152 <|
    v8_bs_drop_step16 hbs a 176#64 192#64 168 <|
    v8_bs_drop_step16 hbs a 192#64 208#64 184 <|
    v8_bs_drop_step16 hbs a 208#64 224#64 200 <|
    v8_bs_drop_step16 hbs a 224#64 240#64 216 <|
    v8_bs_drop_step16 hbs a 240#64 256#64 232 <|
    v8_bs_drop_step16 hbs a 256#64 272#64 248 <|
    v8_bs_drop_step16 hbs a 272#64 288#64 264 <|
    v8_bs_drop_step16 hbs a 288#64 304#64 280 <|
    v8_bs_drop_step16 hbs a 304#64 320#64 296 <|
    v8_bs_drop_step16 hbs a 320#64 336#64 312 <|
    v8_bs_drop_step16 hbs a 336#64 352#64 328 <|
    v8_bs_drop_step16 hbs a 352#64 368#64 344 <|
    v8_bs_drop_step16 hbs a 368#64 384#64 360 <|
    v8_bs_drop_end8 hbs a 384#64

theorem v8_pointsTo32_pair_eq_pointsTo64 (a : BitVec 64) (lo hi : BitVec 32) :
    ((a ↦₃₂ lo) ∗ ((a + 4#64) ↦₃₂ hi)) = (a ↦₆₄ (hi ++ lo)) := by
  rw [pointsTo64_eq_pointsToBytes, pointsTo32_eq_pointsToBytes, pointsTo32_eq_pointsToBytes]
  change (a ↦ₛ unpack32 lo) ∗ ((a + BitVec.ofNat 64 (unpack32 lo).length) ↦ₛ unpack32 hi) = _
  rw [← ProofLib.pointsToBytes_append a (unpack32 lo) (unpack32 hi)]
  congr 1
  unfold unpack64 unpack32
  simp only [List.singleton_append, List.cons_append, List.nil_append, List.cons.injEq, and_true]
  exact ⟨by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel,
         by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel⟩

theorem v8_polyEncoderAt_relocate (A : RustAlloc) (a1 a2 : BitVec 64) (enc : PolyEncoder) :
    polyEncoderAt A a1 enc ⊢
      ∃∗ tag : BitVec 64, ∃∗ bs : { l : List (BitVec 8) // l.length = 384 },
      ∃∗ hi32 : BitVec 32, ∃∗ P_heap : SepProp,
        ⌜(tag = 0#64 ∨ tag = 1#64) ∧
          ((a2 ↦₆₄ tag) ∗ ((a2 + 8#64) ↦ₛ bs.val) ∗
           ((a2 + 392#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ P_heap ⊢
            polyEncoderAt A a2 enc)⌝ ∗
        (a1 ↦₆₄ tag) ∗
        ((a1 + 8#64) ↦ₛ bs.val) ∗
        ((a1 + 392#64) ↦₆₄ (hi32 ++ enc.idx)) ∗
        P_heap := by
  unfold polyEncoderAt encoderStateAt polyEncoderPointsTag polyEncoderPolysTag
    polyEncoderVecsOff polyEncoderIdxOff polyEncoderPadOff polyEncoderPadSize
  rw [ProofLib.memRegion_four (a1 + 396#64)]
  cases hs : enc.s with
  | points pts =>
    dsimp only
    rw [pointListOf_eq_vecGF16ListOf A pts (a1 + 8#64)]
    refine Entails.trans
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
        (vecGF16ListOf_entails_headers_heaps A (pts.map Point.value) (a1 + 8#64))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro hi32
    apply Entails.sepExists_elim; intro pins
    apply Entails.pure_left; rintro ⟨hpts_len, hpts_bound⟩
    rw [sepConj_pure_left_comm]
    apply Entails.pure_left; intro hpins_len
    have hbs_len : (vecHeadersBytesOf pins (pts.map Point.value)).length = 384 := by
      rw [length_vecHeadersBytesOf pins (pts.map Point.value) hpins_len, List.length_map, hpts_len]
      rfl
    have ha1_396 : a1 + 396#64 = (a1 + 392#64) + 4#64 := by bv_omega
    rw [ha1_396, v8_pointsTo32_pair_eq_pointsTo64 (a1 + 392#64) enc.idx hi32]
    refine Entails.sepExists_right 0#64
      (Entails.sepExists_right ⟨vecHeadersBytesOf pins (pts.map Point.value), hbs_len⟩
        (Entails.sepExists_right hi32
          (Entails.sepExists_right (vecGF16HeapList A pins (pts.map Point.value)) ?_)))
    refine Entails.pure_right ⟨Or.inl rfl, ?_⟩ (Entails.of_eq (by ac_rfl))
    rw [pointListOf_eq_vecGF16ListOf A pts (a2 + 8#64),
        ← v8_pointsTo32_pair_eq_pointsTo64 (a2 + 392#64) enc.idx hi32]
    have ha2_396 : (a2 + 392#64) + 4#64 = a2 + 396#64 := by bv_omega
    rw [ha2_396]
    have hvec2 := headers_heaps_entails_vecGF16ListOf A pins (pts.map Point.value) (a2 + 8#64) hpins_len
    have hm4 : ((a2 + 396#64) ↦₃₂ hi32) ⊢ memRegion (a2 + 396#64) 4 := by
      rw [ProofLib.memRegion_four (a2 + 396#64)]
      exact Entails.sepExists_right hi32 (Entails.refl _)
    refine Entails.trans (Entails.of_eq (show _ =
      (a2 ↦₆₄ 0#64) ∗
      (((a2 + 8#64) ↦ₛ vecHeadersBytesOf pins (pts.map Point.value)) ∗
       vecGF16HeapList A pins (pts.map Point.value)) ∗
      ((a2 + 392#64) ↦₃₂ enc.idx) ∗
      ((a2 + 396#64) ↦₃₂ hi32) by ac_rfl)) ?_
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono hvec2 (sepConj_mono_right hm4))) ?_
    exact Entails.pure_right ⟨hpts_len, hpts_bound⟩ (Entails.of_eq (by ac_rfl))
  | polys ps =>
    dsimp only
    rw [polyListOf_eq_vecGF16ListOf A ps (a1 + 8#64)]
    refine Entails.trans
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
        (vecGF16ListOf_entails_headers_heaps A (ps.map LibsignalSpqrV1.Poly.coefficients) (a1 + 8#64))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro hi32
    apply Entails.sepExists_elim; intro pins
    apply Entails.pure_left; intro hps_len
    rw [sepConj_pure_left_comm]
    apply Entails.pure_left; intro hpins_len
    have hbs_len : (vecHeadersBytesOf pins (ps.map LibsignalSpqrV1.Poly.coefficients)).length = 384 := by
      rw [length_vecHeadersBytesOf pins (ps.map LibsignalSpqrV1.Poly.coefficients) hpins_len, List.length_map, hps_len]
      rfl
    have ha1_396 : a1 + 396#64 = (a1 + 392#64) + 4#64 := by bv_omega
    rw [ha1_396, v8_pointsTo32_pair_eq_pointsTo64 (a1 + 392#64) enc.idx hi32]
    refine Entails.sepExists_right 1#64
      (Entails.sepExists_right ⟨vecHeadersBytesOf pins (ps.map LibsignalSpqrV1.Poly.coefficients), hbs_len⟩
        (Entails.sepExists_right hi32
          (Entails.sepExists_right (vecGF16HeapList A pins (ps.map LibsignalSpqrV1.Poly.coefficients)) ?_)))
    refine Entails.pure_right ⟨Or.inr rfl, ?_⟩ (Entails.of_eq (by ac_rfl))
    rw [polyListOf_eq_vecGF16ListOf A ps (a2 + 8#64),
        ← v8_pointsTo32_pair_eq_pointsTo64 (a2 + 392#64) enc.idx hi32]
    have ha2_396 : (a2 + 392#64) + 4#64 = a2 + 396#64 := by bv_omega
    rw [ha2_396]
    have hvec2 := headers_heaps_entails_vecGF16ListOf A pins (ps.map LibsignalSpqrV1.Poly.coefficients) (a2 + 8#64) hpins_len
    have hm4 : ((a2 + 396#64) ↦₃₂ hi32) ⊢ memRegion (a2 + 396#64) 4 := by
      rw [ProofLib.memRegion_four (a2 + 396#64)]
      exact Entails.sepExists_right hi32 (Entails.refl _)
    refine Entails.trans (Entails.of_eq (show _ =
      (a2 ↦₆₄ 1#64) ∗
      (((a2 + 8#64) ↦ₛ vecHeadersBytesOf pins (ps.map LibsignalSpqrV1.Poly.coefficients)) ∗
       vecGF16HeapList A pins (ps.map LibsignalSpqrV1.Poly.coefficients)) ∗
      ((a2 + 392#64) ↦₃₂ enc.idx) ∗
      ((a2 + 396#64) ↦₃₂ hi32) by ac_rfl)) ?_
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono hvec2 (sepConj_mono_right hm4))) ?_
    exact Entails.pure_right hps_len (Entails.of_eq (by ac_rfl))

/-! ## 4. Staging `Ok(enc)` for Shared Epilogue (`+11264 -> +8180`, 77 instructions) -/

@[expose] def v8_midQ128 (w128 w136 w144 : BitVec 64) : BitVec 128 :=
  unshiftWord w136 (loByte w144) ++ unshiftWord w128 (loByte w136)

theorem v8_hiBytes7_eq_loBytes7_lsr8 (w : BitVec 64) :
    EncoderFromPb.hiBytes7 w = EncoderFromPb.loBytes7 (w >>> 8) := by
  change [_, _, _, _, _, _, _] = [_, _, _, _, _, _, _]
  refine congrArg (_ :: ·) (congrArg (_ :: ·) (congrArg (_ :: ·)
    (congrArg (_ :: ·) (congrArg (_ :: ·) (congrArg (_ :: ·) (congrArg (· :: []) ?_))))))
  all_goals bv_kernel

theorem v8_lsr8_lsl8 (v : BitVec 64) :
    (v >>> 8) <<< 8 = v &&& 0xffffffffffffff00#64 := by
  bv_kernel

theorem v8_unshift_lsr56 (w0 v : BitVec 64) :
    (unshiftWord w0 (loByte v)) >>> 56 = v &&& 0xff#64 := by
  unfold unshiftWord loByte
  bv_kernel

theorem v8_overlapWord7_unshift_lsr8 (w0 w8 : BitVec 64) :
    overlapWord7 (unshiftWord w0 (loByte w8)) (w8 >>> 8) = w8 := by
  unfold overlapWord7
  rw [v8_unshift_lsr56 w0 w8, v8_lsr8_lsl8 w8]
  bv_kernel

theorem v8_overlapWord7_midQ128_lsr8 (w128 w136 w144 : BitVec 64) :
    overlapWord7 ((v8_midQ128 w128 w136 w144).extractLsb' 64 64) (w144 >>> 8) = w144 := by
  have hhi : (v8_midQ128 w128 w136 w144).extractLsb' 64 64 = unshiftWord w136 (loByte w144) := by
    unfold v8_midQ128
    bv_kernel
  rw [hhi]
  exact v8_overlapWord7_unshift_lsr8 w136 w144

@[local arm64_norm, local wp_norm]
theorem v8_orr_x27_w80 (w80 : BitVec 64) :
    ((w80.extractLsb' 8 32).zeroExtend 64 |||
      ((((w80.extractLsb' 40 16).zeroExtend 32 |||
        ((w80.extractLsb' 56 8).zeroExtend 32 <<< 16#64)).zeroExtend 64) <<< 32#64)) =
      (w80.extractLsb' 8 56).zeroExtend 64 := by
  bv_kernel

@[local arm64_norm, local wp_norm]
theorem v8_w80_d97 (w80 : BitVec 64) :
    ((w80.extractLsb' 8 56).zeroExtend 64).setWidth 32 = w80.extractLsb' 8 32 := by
  bv_kernel

@[local arm64_norm, local wp_norm]
theorem v8_w80_h101 (w80 : BitVec 64) :
    ((((w80.extractLsb' 8 56).zeroExtend 64) >>> 32).setWidth 32).setWidth 16 =
      w80.extractLsb' 40 16 := by
  bv_kernel

@[local arm64_norm, local wp_norm]
theorem v8_w80_b103 (w80 : BitVec 64) :
    ((((w80.extractLsb' 8 56).zeroExtend 64) >>> 48).setWidth 32).setWidth 8 =
      w80.extractLsb' 56 8 := by
  bv_kernel

@[local arm64_norm, local wp_norm]
theorem v8_zext32_setWidth8 (b : BitVec 8) :
    (b.zeroExtend 32).setWidth 8 = b := by
  bv_kernel

@[local arm64_norm, local wp_norm]
theorem v8_fsp_1888_add_89 (fsp : BitVec 64) :
    (fsp + 1888#64) + 89#64 = fsp + 1977#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem v8_fsp_1888_add_93 (fsp : BitVec 64) :
    (fsp + 1888#64) + 93#64 = fsp + 1981#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem v8_fsp_1888_add_113 (fsp : BitVec 64) :
    (fsp + 1888#64) + 113#64 = fsp + 2001#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem v8_fsp_1888_add_137 (fsp : BitVec 64) :
    (fsp + 1888#64) + 137#64 = fsp + 2025#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem v8_fsp_848_add_39 (fsp : BitVec 64) :
    (fsp + 848#64) + 39#64 = fsp + 887#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem v8_fsp_848_add_15 (fsp : BitVec 64) :
    (fsp + 848#64) + 15#64 = fsp + 863#64 := by bv_omega

theorem v8_fsp_1976_split_rest (fsp w80 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1976#64) ↦₆₄ w80) ∗ Rest =
      ((fsp + 1976#64) ↦₈ w80.extractLsb' 0 8) ∗
      ((fsp + 1977#64) ↦₃₂ w80.extractLsb' 8 32) ∗
      ((fsp + 1981#64) ↦₁₆ w80.extractLsb' 40 16) ∗
      ((fsp + 1983#64) ↦₈ w80.extractLsb' 56 8) ∗ Rest := by
  have h := v10_pointsTo64_split_1_4_2_1 (fsp + 1976#64) w80
  have ha1 : (fsp + 1976#64) + 1#64 = fsp + 1977#64 := by bv_omega
  have ha5 : (fsp + 1976#64) + 5#64 = fsp + 1981#64 := by bv_omega
  have ha7 : (fsp + 1976#64) + 7#64 = fsp + 1983#64 := by bv_omega
  rw [ha1, ha5, ha7] at h
  have h' := congrArg (· ∗ Rest) h
  exact Eq.trans (by ac_rfl) (Eq.trans h' (by ac_rfl))

theorem v8_fsp_1976_unsplit_rest (fsp w80 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1976#64) ↦₈ w80.extractLsb' 0 8) ∗
      ((fsp + 1977#64) ↦₃₂ w80.extractLsb' 8 32) ∗
      ((fsp + 1981#64) ↦₁₆ w80.extractLsb' 40 16) ∗
      ((fsp + 1983#64) ↦₈ w80.extractLsb' 56 8) ∗ Rest =
      ((fsp + 1976#64) ↦₆₄ w80) ∗ Rest :=
  (v8_fsp_1976_split_rest fsp w80 Rest).symm

theorem v8_fsp_2024_realign_rest (fsp w128 w136 w144 : BitVec 64) (Rest : SepProp) :
    ((fsp + 2024#64) ↦₆₄ w128) ∗ ((fsp + 2032#64) ↦₆₄ w136) ∗ ((fsp + 2040#64) ↦₆₄ w144) ∗ Rest =
      ((fsp + 2024#64) ↦₈ loByte w128) ∗
      ((fsp + 2025#64) ↦₆₄ (v8_midQ128 w128 w136 w144).extractLsb' 0 64) ∗
      ((fsp + 2033#64) ↦₆₄ (v8_midQ128 w128 w136 w144).extractLsb' 64 64) ∗
      ((fsp + 2041#64) ↦ₛ EncoderFromPb.hiBytes7 w144) ∗ Rest := by
  have h := v10_triple64_eq_byte_q128_tail7 (fsp + 2024#64) w128 w136 w144
  have ha8 : (fsp + 2024#64) + 8#64 = fsp + 2032#64 := by bv_omega
  have ha16 : (fsp + 2024#64) + 16#64 = fsp + 2040#64 := by bv_omega
  have ha1 : (fsp + 2024#64) + 1#64 = fsp + 2025#64 := by bv_omega
  have ha17 : (fsp + 2024#64) + 17#64 = fsp + 2041#64 := by bv_omega
  have ha2033 : (fsp + 2025#64) + 8#64 = fsp + 2033#64 := by bv_omega
  rw [ha8, ha16, ha1, ha17] at h
  change _ = ((fsp + 2024#64) ↦₈ loByte w128) ∗
    ((fsp + 2025#64) ↦₁₂₈ v8_midQ128 w128 w136 w144) ∗
    ((fsp + 2041#64) ↦ₛ EncoderFromPb.hiBytes7 w144) at h
  unfold pointsTo128 at h
  rw [ha2033] at h
  have h' := congrArg (· ∗ Rest) h
  exact Eq.trans (by ac_rfl) (Eq.trans h' (by ac_rfl))

theorem v8_fsp_2024_unrealign_rest (fsp w128 w136 w144 : BitVec 64) (Rest : SepProp) :
    ((fsp + 2024#64) ↦₈ loByte w128) ∗
      ((fsp + 2025#64) ↦₆₄ (v8_midQ128 w128 w136 w144).extractLsb' 0 64) ∗
      ((fsp + 2033#64) ↦₆₄ (v8_midQ128 w128 w136 w144).extractLsb' 64 64) ∗
      ((fsp + 2041#64) ↦ₛ EncoderFromPb.hiBytes7 w144) ∗ Rest =
    ((fsp + 2024#64) ↦₆₄ w128) ∗ ((fsp + 2032#64) ↦₆₄ w136) ∗ ((fsp + 2040#64) ↦₆₄ w144) ∗ Rest :=
  (v8_fsp_2024_realign_rest fsp w128 w136 w144 Rest).symm

theorem v8_fsp_2000_realign_rest (fsp w104 w112 : BitVec 64) (Rest : SepProp) :
    ((fsp + 2000#64) ↦₆₄ w104) ∗ ((fsp + 2008#64) ↦₆₄ w112) ∗ Rest =
      ((fsp + 2000#64) ↦₈ loByte w104) ∗
      ((fsp + 2001#64) ↦₆₄ unshiftWord w104 (loByte w112)) ∗
      ((fsp + 2009#64) ↦ₛ EncoderFromPb.hiBytes7 w112) ∗ Rest := by
  have h := pair64_to_byte_word_tail7 (fsp + 2000#64) w104 w112
  have ha8 : (fsp + 2000#64) + 8#64 = fsp + 2008#64 := by bv_omega
  have ha1 : (fsp + 2000#64) + 1#64 = fsp + 2001#64 := by bv_omega
  have ha9 : (fsp + 2000#64) + 9#64 = fsp + 2009#64 := by bv_omega
  rw [ha8, ha1, ha9] at h
  have h' := congrArg (· ∗ Rest) h
  exact Eq.trans (by ac_rfl) (Eq.trans h' (by ac_rfl))

theorem v8_fsp_2000_unrealign_rest (fsp w104 w112 : BitVec 64) (Rest : SepProp) :
    ((fsp + 2000#64) ↦₈ loByte w104) ∗
      ((fsp + 2001#64) ↦₆₄ unshiftWord w104 (loByte w112)) ∗
      ((fsp + 2009#64) ↦ₛ EncoderFromPb.hiBytes7 w112) ∗ Rest =
      ((fsp + 2000#64) ↦₆₄ w104) ∗ ((fsp + 2008#64) ↦₆₄ w112) ∗ Rest :=
  (v8_fsp_2000_realign_rest fsp w104 w112 Rest).symm

theorem v8_fsp_880_realign_rest (fsp u880 w112 : BitVec 64) (Rest : SepProp) :
    ((fsp + 880#64) ↦ₛ EncoderFromPb.loBytes7 u880) ∗ ((fsp + 887#64) ↦₆₄ w112) ∗ Rest =
      ((fsp + 880#64) ↦₆₄ overlapLow7 u880 w112) ∗
      ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 (w112 >>> 8)) ∗ Rest := by
  have h := loBytes7_pointsTo64_eq_overlap (fsp + 880#64) u880 w112
  have ha7 : (fsp + 880#64) + 7#64 = fsp + 887#64 := by bv_omega
  have ha8 : (fsp + 880#64) + 8#64 = fsp + 888#64 := by bv_omega
  rw [ha7, ha8, v8_hiBytes7_eq_loBytes7_lsr8 w112] at h
  rw [← sepConj_assoc, h, sepConj_assoc]

theorem v8_fsp_856_realign_rest (fsp w856 u864 : BitVec 64) (Rest : SepProp) :
    ((fsp + 856#64) ↦₆₄ w856) ∗ ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 u864) ∗ Rest =
      ((fsp + 856#64) ↦ₛ EncoderFromPb.loBytes7 w856) ∗
      ((fsp + 863#64) ↦₆₄ overlapWord7 w856 u864) ∗ Rest := by
  have h := pointsTo64_loBytes7_eq_loBytes7_overlapWord7 (fsp + 856#64) w856 u864
  have ha8 : (fsp + 856#64) + 8#64 = fsp + 864#64 := by bv_omega
  have ha7 : (fsp + 856#64) + 7#64 = fsp + 863#64 := by bv_omega
  rw [ha8, ha7] at h
  rw [← sepConj_assoc, h, sepConj_assoc]

theorem v8_fsp_856_unrealign_midQ128_rest (fsp w128 w136 w144 : BitVec 64) (Rest : SepProp) :
    ((fsp + 856#64) ↦ₛ EncoderFromPb.loBytes7 ((v8_midQ128 w128 w136 w144).extractLsb' 64 64)) ∗
      ((fsp + 863#64) ↦₆₄ w144) ∗ Rest =
    ((fsp + 856#64) ↦₆₄ (v8_midQ128 w128 w136 w144).extractLsb' 64 64) ∗
      ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 (w144 >>> 8)) ∗ Rest := by
  have h := (v8_fsp_856_realign_rest fsp ((v8_midQ128 w128 w136 w144).extractLsb' 64 64)
    (w144 >>> 8) Rest).symm
  rwa [v8_overlapWord7_midQ128_lsr8 w128 w136 w144] at h

/-- Active stack slots in `fsp + 96..895` written by `+11264..+11568` (before execution). -/
@[expose] def v8_stagingSlotsPre (fsp : BitVec 64)
    (d96 : BitVec 32) (u104 u112 u160 : BitVec 64) (d172 : BitVec 32) (u192 u208 u232 : BitVec 64)
    (uq608 uq624 uq640 uq656 uq672 uq688 uq704 uq720 uq736 uq752 uq768 uq784 uq800 uq816 : BitVec 128)
    (u832 : BitVec 64) (uq848 : BitVec 128) (u864 u880 u887 : BitVec 64) : SepProp :=
  ((fsp + 96#64) ↦₃₂ d96) ∗
  ((fsp + 104#64) ↦₆₄ u104) ∗
  ((fsp + 112#64) ↦₆₄ u112) ∗
  ((fsp + 160#64) ↦₆₄ u160) ∗
  ((fsp + 172#64) ↦₃₂ d172) ∗
  ((fsp + 192#64) ↦₆₄ u192) ∗
  ((fsp + 208#64) ↦₆₄ u208) ∗
  ((fsp + 232#64) ↦₆₄ u232) ∗
  ((fsp + 608#64) ↦₁₂₈ uq608) ∗ ((fsp + 624#64) ↦₁₂₈ uq624) ∗
  ((fsp + 640#64) ↦₁₂₈ uq640) ∗ ((fsp + 656#64) ↦₁₂₈ uq656) ∗
  ((fsp + 672#64) ↦₁₂₈ uq672) ∗ ((fsp + 688#64) ↦₁₂₈ uq688) ∗
  ((fsp + 704#64) ↦₁₂₈ uq704) ∗ ((fsp + 720#64) ↦₁₂₈ uq720) ∗
  ((fsp + 736#64) ↦₁₂₈ uq736) ∗ ((fsp + 752#64) ↦₁₂₈ uq752) ∗
  ((fsp + 768#64) ↦₁₂₈ uq768) ∗ ((fsp + 784#64) ↦₁₂₈ uq784) ∗
  ((fsp + 800#64) ↦₁₂₈ uq800) ∗ ((fsp + 816#64) ↦₁₂₈ uq816) ∗
  ((fsp + 832#64) ↦₆₄ u832) ∗
  ((fsp + 848#64) ↦₁₂₈ uq848) ∗ ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 u864) ∗
  ((fsp + 880#64) ↦ₛ EncoderFromPb.loBytes7 u880) ∗ ((fsp + 887#64) ↦₆₄ u887)

/-- Active stack slots in `fsp + 96..895` after `+11264..+11568` (ready for `epilogueStackSlots`). -/
@[expose] def v8_stagingSlotsPost (fsp : BitVec 64) (bs : List (BitVec 8)) (pa5 l2 : BitVec 64) : SepProp :=
  ((fsp + 96#64) ↦₃₂ (loByte (v8_wordAt bs 104)).zeroExtend 32) ∗
  ((fsp + 104#64) ↦₆₄ pa5) ∗
  ((fsp + 112#64) ↦₆₄ 960#64) ∗
  ((fsp + 160#64) ↦₆₄ l2) ∗
  ((fsp + 172#64) ↦₃₂ (loByte (v8_wordAt bs 128)).zeroExtend 32) ∗
  ((fsp + 192#64) ↦₆₄ 1152#64) ∗
  ((fsp + 208#64) ↦₆₄ v8_wordAt bs 0) ∗
  ((fsp + 232#64) ↦₆₄ l2) ∗
  ((fsp + 608#64) ↦₁₂₈ v8_quadAt bs 152) ∗ ((fsp + 624#64) ↦₁₂₈ v8_quadAt bs 168) ∗
  ((fsp + 640#64) ↦₁₂₈ v8_quadAt bs 184) ∗ ((fsp + 656#64) ↦₁₂₈ v8_quadAt bs 200) ∗
  ((fsp + 672#64) ↦₁₂₈ v8_quadAt bs 216) ∗ ((fsp + 688#64) ↦₁₂₈ v8_quadAt bs 232) ∗
  ((fsp + 704#64) ↦₁₂₈ v8_quadAt bs 248) ∗ ((fsp + 720#64) ↦₁₂₈ v8_quadAt bs 264) ∗
  ((fsp + 736#64) ↦₁₂₈ v8_quadAt bs 280) ∗ ((fsp + 752#64) ↦₁₂₈ v8_quadAt bs 296) ∗
  ((fsp + 768#64) ↦₁₂₈ v8_quadAt bs 312) ∗ ((fsp + 784#64) ↦₁₂₈ v8_quadAt bs 328) ∗
  ((fsp + 800#64) ↦₁₂₈ v8_quadAt bs 344) ∗ ((fsp + 816#64) ↦₁₂₈ v8_quadAt bs 360) ∗
  ((fsp + 832#64) ↦₆₄ v8_wordAt bs 376) ∗
  ((fsp + 848#64) ↦₁₂₈ v8_midQ128 (v8_wordAt bs 128) (v8_wordAt bs 136) (v8_wordAt bs 144)) ∗
  ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 (v8_wordAt bs 144 >>> 8)) ∗
  ((fsp + 880#64) ↦₆₄ unshiftWord (v8_wordAt bs 104) (loByte (v8_wordAt bs 112))) ∗
  ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 (v8_wordAt bs 112 >>> 8))

end CryptoVerification.SpqrV1.States.FromPb

