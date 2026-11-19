/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommon -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiation
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSub
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp

public section

namespace CryptoVerification.SpqrV1.Top.DecodeState

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

/-! ## 1. Pure BitVector Helpers for Field Key Decoding and Tag Dispatch -/

@[local simp, local arm64_norm]
theorem truncate32_zeroExtend64_lsr3 (key : BitVec 64) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 key) >>> 3) =
      BitVec.truncate 32 key >>> 3 := by
  bv_bits

theorem key_lsr32_eq_zero_of_lt {key : BitVec 64} (h : ¬ 2 ^ 32 ≤ key.toNat) :
    key >>> 32 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  change key.toNat / 4294967296 = 0
  omega

theorem key_lsr32_ne_zero_of_ge {key : BitVec 64} (h : 2 ^ 32 ≤ key.toNat) :
    (key >>> 32 == 0#64) = false := by
  apply beq_eq_false_iff_ne.mpr
  intro heq
  have h1 := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at h1
  change key.toNat / 4294967296 = 0 at h1
  omega

theorem key_and7_of_wt_none {key : BitVec 64}
    (hwt : WireType.ofNat? (key.toNat % 8) = none) :
    key &&& 7#64 = 6#64 ∨ key &&& 7#64 = 7#64 := by
  have hmod : (key &&& 7#64).toNat = key.toNat % 8 := by
    rw [BitVec.toNat_and, show (7#64).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have hlt : key.toNat % 8 < 8 := Nat.mod_lt _ (by decide)
  rcases h : key.toNat % 8 with _ | _ | _ | _ | _ | _ | _ | n
  · simp [h, WireType.ofNat?] at hwt
  · simp [h, WireType.ofNat?] at hwt
  · simp [h, WireType.ofNat?] at hwt
  · simp [h, WireType.ofNat?] at hwt
  · simp [h, WireType.ofNat?] at hwt
  · simp [h, WireType.ofNat?] at hwt
  · left; exact BitVec.eq_of_toNat_eq (by rw [hmod, h]; rfl)
  · right
    have hn0 : n = 0 := by omega
    subst hn0
    exact BitVec.eq_of_toNat_eq (by rw [hmod, h]; rfl)

theorem key_and7_of_wt_some {key : BitVec 64} {iwt : WireType}
    (hwt : WireType.ofNat? (key.toNat % 8) = some iwt) :
    key &&& 7#64 = BitVec.ofNat 64 iwt.toNat := by
  have hmod : (key &&& 7#64).toNat = key.toNat % 8 := by
    rw [BitVec.toNat_and, show (7#64).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have hlt : key.toNat % 8 < 8 := Nat.mod_lt _ (by decide)
  rcases h : key.toNat % 8 with _ | _ | _ | _ | _ | _ | _ | n <;>
    simp [h, WireType.ofNat?] at hwt <;>
    subst hwt <;>
    exact BitVec.eq_of_toNat_eq (by rw [hmod, h]; rfl)

theorem wt_ult6 (iwt : WireType) :
    (BitVec.ofNat 64 iwt.toNat).ult 6#64 = true ∧
    (6#64).ule (BitVec.ofNat 64 iwt.toNat) = false := by
  cases iwt <;> decide

theorem wt_setWidth8 (iwt : WireType) :
    BitVec.setWidth 8 (BitVec.ofNat 64 iwt.toNat) = BitVec.ofNat 8 iwt.toNat := by
  cases iwt <;> rfl

theorem wt64_ne_two_of_ne_lengthDelimited {iwt : WireType} (hne : iwt ≠ .lengthDelimited) :
    (BitVec.ofNat 64 iwt.toNat != 2#64) = true ∧
    (BitVec.ofNat 64 iwt.toNat == 2#64) = false := by
  cases iwt <;> first | exact (hne rfl).elim | decide

theorem key_lsr3_32_eq {key : BitVec 64} (hk : ¬ 2 ^ 32 ≤ key.toNat) :
    BitVec.truncate 32 key >>> 3 = BitVec.ofNat 32 (key.toNat / 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  change (key.toNat % 4294967296) / 8 = (key.toNat / 8) % 4294967296
  rw [Nat.mod_eq_of_lt (by omega : key.toNat < 4294967296),
    Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 4294967296)]

theorem tag_zeroExtend64_ofNat32 {tag : Nat} (hlt : tag < 2 ^ 29) :
    BitVec.zeroExtend 64 (BitVec.ofNat 32 tag) = BitVec.ofNat 64 tag := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : tag < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : tag < 2 ^ 64)]

theorem tag_lt_pow29_of_key_lt {key : BitVec 64} (hk : ¬ 2 ^ 32 ≤ key.toNat) :
    key.toNat / 8 < 2 ^ 29 := by
  omega

theorem tag_setWidth32_ofNat (tag : Nat) :
    BitVec.truncate 32 (BitVec.ofNat 64 tag) = BitVec.ofNat 32 tag := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

theorem tag_cbz64_false {tag : Nat} (h1 : 1 ≤ tag) (hlt : tag < 2 ^ 29) :
    (BitVec.ofNat 64 tag == 0#64) = false := by
  apply beq_eq_false_iff_ne.mpr
  intro h
  have h2 := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : tag < 2 ^ 64)] at h2
  omega

theorem tag_cbz32_false {tag : Nat} (h1 : 1 ≤ tag) (hlt : tag < 2 ^ 29) :
    (BitVec.ofNat 32 tag == 0#32) = false := by
  apply beq_eq_false_iff_ne.mpr
  intro h
  have h2 := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : tag < 2 ^ 32)] at h2
  omega

theorem tag_cmp32_of_gt {c tag : Nat} (hgt : c < tag) (hlt : tag < 2 ^ 29) :
    (BitVec.ofNat 32 c).slt (BitVec.ofNat 32 tag) = true ∧
    (BitVec.ofNat 32 tag).sle (BitVec.ofNat 32 c) = false ∧
    (BitVec.ofNat 32 c).ult (BitVec.ofNat 32 tag) = true ∧
    (BitVec.ofNat 32 tag).ule (BitVec.ofNat 32 c) = false ∧
    (BitVec.ofNat 32 tag == BitVec.ofNat 32 c) = false ∧
    (BitVec.ofNat 32 tag != BitVec.ofNat 32 c) = true := by
  have hc32 : c < 2 ^ 32 := by omega
  have ht32 : tag < 2 ^ 32 := by omega
  have hc_toInt : (BitVec.ofNat 32 c).toInt = (c : Int) := by
    rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc32]
    split <;> omega
  have ht_toInt : (BitVec.ofNat 32 tag).toInt = (tag : Int) := by
    rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ht32]
    split <;> omega
  have hne : BitVec.ofNat 32 tag ≠ BitVec.ofNat 32 c := by
    intro h
    have h1 := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc32, Nat.mod_eq_of_lt ht32] at h1
    omega
  refine ⟨?_, ?_, ?_, ?_, beq_eq_false_iff_ne.mpr hne, bne_iff_ne.mpr hne⟩
  · simp only [BitVec.slt, hc_toInt, ht_toInt, decide_eq_true_eq]; omega
  · simp only [BitVec.sle, hc_toInt, ht_toInt, decide_eq_false_iff_not]; omega
  · simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc32, Nat.mod_eq_of_lt ht32,
      decide_eq_true_eq]; omega
  · simp only [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc32, Nat.mod_eq_of_lt ht32,
      decide_eq_false_iff_not]; omega

theorem len_ult_of_lt {rest_len : Nat} {len64 : BitVec 64}
    (hlt : rest_len < len64.toNat) :
    (BitVec.ofNat 64 rest_len).ult len64 = true ∧
    len64.ule (BitVec.ofNat 64 rest_len) = false := by
  have hrest64 : rest_len < 2 ^ 64 := by have := len64.isLt; omega
  simp only [BitVec.ult, BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrest64,
    decide_eq_true_eq, decide_eq_false_iff_not]
  omega

theorem len_ult_of_ge {rest_len : Nat} {len64 : BitVec 64}
    (hge : ¬ rest_len < len64.toNat) (hrest : rest_len < 2 ^ 64) :
    (BitVec.ofNat 64 rest_len).ult len64 = false ∧
    len64.ule (BitVec.ofNat 64 rest_len) = true := by
  simp only [BitVec.ult, BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrest,
    decide_eq_false_iff_not, decide_eq_true_eq]
  omega

theorem vecU8Heap_cap_lt (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Heap A cap ptr bs ⊢ ⌜cap.toNat < 2 ^ 63⌝ ∗ vecU8Heap A cap ptr bs := by
  unfold vecU8Heap
  apply Entails.pure_left; rintro ⟨hle, hlt, hptr⟩
  exact Entails.pure_right hlt (Entails.pure_right ⟨hle, hlt, hptr⟩ (Entails.refl _))

theorem after_decodeVarint2_to_errFrame (H_inner : V1InnerHeapPred) (b : BitVec 64) (A : RustAlloc)
    (x : DecodeStateGhost) {cur rest1 : List (BitVec 8)}
    (hcur_le : cur.length ≤ x.st.bytes.length) (hcur_suf : IsDropSuffix x.st.bytes cur)
    (hle1 : rest1.length ≤ cur.length) (curSt : PqRatchetState) (s0 : State) :
    sliceCursorAfter (s0.sp - 1056#64)
        (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) cur rest1 ∗
      (x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
      protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) cur.length curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommon b A x s0 ⊢
      decodeStateErrFrame H_inner b A x curSt s0 := by
  have hj := sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr) hcur_le hcur_suf hle1
  have hreord :
      sliceCursorAfter (s0.sp - 1056#64)
          (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) cur rest1 ∗
        (x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) cur.length curSt ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommon b A x s0 =
      ((x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
        sliceCursorAfter (s0.sp - 1056#64)
          (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) cur rest1) ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) cur.length curSt ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommon b A x s0 := by ac_rfl
  rw [hreord]
  refine Entails.trans (sepConj_mono_left hj) ?_
  exact loopCommon_cursor_to_errFrame H_inner b A x rest1 cur.length curSt s0

/-! ## 2. Tag Dispatch and Single Loop Iteration of `VersionNegotiationPB::merge` -/

theorem cmp_len_limit_bne_of_lt {cur_len limit : Nat} (hlt : cur_len < limit)
    (hlim : limit < 2 ^ 63) :
    (BitVec.ofNat 64 cur_len != BitVec.ofNat 64 limit) = true := by
  have ⟨_, _, hbeq⟩ := cmp_len_limit_of_lt hlt hlim
  exact bne_iff_ne.mpr (beq_eq_false_iff_ne.mp hbeq)

theorem vecU8At_header_fold (A : RustAlloc) (a cap ptr : BitVec 64)
    (bs : List (BitVec 8)) (remLen : Nat) (hcap : BytesMergeCapOk cap remLen) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      vecU8Heap A cap ptr bs ⊢
    vecU8CapOkAt A a remLen bs := by
  unfold vecU8CapOkAt
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  apply Entails.pure_right hcap
  rw [vecU8At_eq_header_heap]
  unfold vecHeader
  exact Entails.of_eq (by ac_rfl)

attribute [local irreducible] Proto.mergeMessage mergeLoopBin Proto.spqrDecodeState

end CryptoVerification.SpqrV1.Top.DecodeState

