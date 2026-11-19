/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncodedLenBase
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint2Base
import LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBase
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Decodes
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncoderBase
import ProofLib.SepLogic.WPp

/-!
# Shared Specification, Pure Lemmas, and Stepping Helpers for `PolynomialDecoder::encode`

Covers shared definitions and stepping blocks for:
- `prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialDecoder, alloc::vec::Vec<u8>> [local#1]`
  (`0x37520..0x37690`, 92 insns)
- `prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialDecoder, alloc::vec::Vec<u8>> [local#2]`
  (`0x52544..0x526d4`, 100 insns)
-/

public section

namespace CryptoVerification.SpqrV1.Prost.MessageEncode

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.RustHeap
  CryptoGames.LibsignalSession CryptoVerification.LibsignalTripleRatchetRepr
  CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
  CryptoVerification.LibsignalProtoCodec
  CryptoVerification.LibsignalTripleRatchet.Prost
  CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
  CryptoVerification.CodeLayout
  CryptoVerification.LibsignalSpqrV1
  CryptoVerification.SpqrV1.Alloc
  CryptoVerification.SpqrV1.Varint
  CryptoVerification.SpqrV1.ProtoRepr
  CryptoVerification.SpqrV1.Poly
  CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 EncodedLen.ule_self_64 EncodedLen.ult_self_64

/-! ## 1. Pure Model & `LibsignalSpqrV1.Proto` Bridge Lemmas -/

/-- Full encoded bytes produced by `prost::encoding::message::encode::<PolynomialDecoder, Vec<u8>>`
for wire tag `tag : BitVec 32` (`w0 = tag`, wire type `lengthDelimited` = `2`). -/
@[expose] def encodePolyDecoderMsg (tag : BitVec 32) (pb : ProtoPolynomialDecoder) : List (BitVec 8) :=
  Proto.encodeMessage PolynomialDecoder.encodeRaw tag (ProtoPolynomialDecoder.toPB pb)

/-- Header bytes (`Proto.encodeKey tag .lengthDelimited ++ encodeVarint (encoded_len)`) of `PolynomialDecoder::encode`. -/
@[expose] def polyDecoderHeaderBytes (tag : BitVec 32) (pb : ProtoPolynomialDecoder) : List (BitVec 8) :=
  Proto.encodeKey tag .lengthDelimited ++
    LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 (polynomialDecoderPBEncodedLen pb))

theorem polyDecoder_tag_orr_eq (tag : BitVec 32) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (2#64 ||| BitVec.zeroExtend 64 (tag <<< 3))) =
      ((tag <<< 3) ||| (Proto.WireType.lengthDelimited).toU32).zeroExtend 64 := by
  dsimp [Proto.WireType.toU32]; bv_bits

theorem encodeVarint_polyDecoder_tag_eq_proto (tag : BitVec 32) :
    LibsignalProtoCodec.encodeVarint
      (((tag <<< 3) ||| (Proto.WireType.lengthDelimited).toU32).zeroExtend 64) =
      Proto.encodeKey tag .lengthDelimited := by
  rw [Proto.encodeKey, protoEncodeVarint_eq_codec]

theorem bs_append_boolField_4_true (bs : List (BitVec 8)) :
    (bs ++ [0x20#8]) ++ [0x01#8] = bs ++ Proto.encodeBoolField 4#32 true := by
  rw [protoEncodeBoolField_4_true, List.append_assoc]; rfl

theorem bs_append_boolField_4_false (bs : List (BitVec 8)) :
    bs ++ Proto.encodeBoolField 4#32 false = bs := by
  rw [protoEncodeBoolField_4_false, List.append_nil]

theorem encodePolyDecoderMsg_eq (tag : BitVec 32) (pb : ProtoPolynomialDecoder) :
    encodePolyDecoderMsg tag pb =
      polyDecoderHeaderBytes tag pb ++ Proto.encodeUint32Field 1#32 pb.ptsNeeded ++
        Proto.encodeUint32Field 2#32 pb.polys ++ Varint.encodeRepeatedBytes 3 pb.pts ++
        Proto.encodeBoolField 4#32 pb.isComplete := by
  have hlen : (PolynomialDecoder.encodeRaw (ProtoPolynomialDecoder.toPB pb)).length =
      polynomialDecoderPBEncodedLen pb := polynomialDecoderPBEncodedLen_eq_proto pb
  dsimp only [encodePolyDecoderMsg, Proto.encodeMessage, polyDecoderHeaderBytes]
  rw [protoEncodeVarint_eq_codec, hlen]
  dsimp only [PolynomialDecoder.encodeRaw, ProtoPolynomialDecoder.toPB]
  rw [← varintEncodeRepeatedBytes_3_eq_proto]; simp only [List.append_assoc]

theorem bs0_append_encodePolyDecoderMsg (bs0 : List (BitVec 8)) (tag : BitVec 32)
    (pb : ProtoPolynomialDecoder) :
    bs0 ++ encodePolyDecoderMsg tag pb =
      ((((bs0 ++ polyDecoderHeaderBytes tag pb) ++
        Proto.encodeUint32Field 1#32 pb.ptsNeeded) ++
        Proto.encodeUint32Field 2#32 pb.polys) ++
        Varint.encodeRepeatedBytes 3 pb.pts) ++
        Proto.encodeBoolField 4#32 pb.isComplete := by
  rw [encodePolyDecoderMsg_eq]; simp only [List.append_assoc]

theorem bs0_append_polyDecoderHeaderBytes (bs0 : List (BitVec 8)) (tag : BitVec 32)
    (pb : ProtoPolynomialDecoder) :
    (bs0 ++ Proto.encodeKey tag .lengthDelimited) ++
      LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 (polynomialDecoderPBEncodedLen pb)) =
    bs0 ++ polyDecoderHeaderBytes tag pb := by
  rw [polyDecoderHeaderBytes, List.append_assoc]

theorem polyDecoderHeaderBytes_len_bounds (tag : BitVec 32) (pb : ProtoPolynomialDecoder) :
    (polyDecoderHeaderBytes tag pb).length =
      (Proto.encodeKey tag .lengthDelimited).length +
        (LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 (polynomialDecoderPBEncodedLen pb))).length ∧
    1 ≤ (Proto.encodeKey tag .lengthDelimited).length ∧
    2 ≤ (polyDecoderHeaderBytes tag pb).length := by
  have hk := (Varint.encodeVarint_length_bounds
    (((tag <<< 3) ||| (Proto.WireType.lengthDelimited).toU32).zeroExtend 64)).1
  rw [encodeVarint_polyDecoder_tag_eq_proto] at hk
  have hb := (Varint.encodeVarint_length_bounds (BitVec.ofNat 64 (polynomialDecoderPBEncodedLen pb))).1
  rw [polyDecoderHeaderBytes, List.length_append]; omega

theorem bs_append_ptsNeeded_of_ne_zero (bs : List (BitVec 8)) (pb : ProtoPolynomialDecoder)
    (hpn : (pb.ptsNeeded == 0#32) = false) :
    (bs ++ [0x08#8]) ++ LibsignalProtoCodec.encodeVarint (pb.ptsNeeded.zeroExtend 64) =
      bs ++ Proto.encodeUint32Field 1#32 pb.ptsNeeded := by
  rw [protoEncodeUint32Field_1_of_ne_zero (beq_eq_false_iff_ne.mp hpn), List.append_assoc]

theorem bs_append_ptsNeeded_of_zero (bs : List (BitVec 8)) (pb : ProtoPolynomialDecoder)
    (hpn : (pb.ptsNeeded == 0#32) = true) :
    bs ++ Proto.encodeUint32Field 1#32 pb.ptsNeeded = bs := by
  rw [eq_of_beq hpn, protoEncodeUint32Field_zero, List.append_nil]

theorem ptsNeeded_field_len_of_ne_zero (pb : ProtoPolynomialDecoder)
    (hpn : (pb.ptsNeeded == 0#32) = false) :
    (Proto.encodeUint32Field 1#32 pb.ptsNeeded).length =
      1 + (LibsignalProtoCodec.encodeVarint (pb.ptsNeeded.zeroExtend 64)).length ∧
    2 ≤ (Proto.encodeUint32Field 1#32 pb.ptsNeeded).length := by
  have hb := (Varint.encodeVarint_length_bounds (pb.ptsNeeded.zeroExtend 64)).1
  rw [protoEncodeUint32Field_1_of_ne_zero (beq_eq_false_iff_ne.mp hpn),
    List.length_append, List.length_singleton]; omega

theorem bs_append_polys_of_ne_zero (bs : List (BitVec 8)) (pb : ProtoPolynomialDecoder)
    (hpl : (pb.polys == 0#32) = false) :
    (bs ++ [0x10#8]) ++ LibsignalProtoCodec.encodeVarint (pb.polys.zeroExtend 64) =
      bs ++ Proto.encodeUint32Field 2#32 pb.polys := by
  rw [protoEncodeUint32Field_2_of_ne_zero (beq_eq_false_iff_ne.mp hpl), List.append_assoc]

theorem bs_append_polys_of_zero (bs : List (BitVec 8)) (pb : ProtoPolynomialDecoder)
    (hpl : (pb.polys == 0#32) = true) :
    bs ++ Proto.encodeUint32Field 2#32 pb.polys = bs := by
  rw [eq_of_beq hpl, protoEncodeUint32Field_zero, List.append_nil]

theorem polys_field_len_of_ne_zero (pb : ProtoPolynomialDecoder)
    (hpl : (pb.polys == 0#32) = false) :
    (Proto.encodeUint32Field 2#32 pb.polys).length =
      1 + (LibsignalProtoCodec.encodeVarint (pb.polys.zeroExtend 64)).length ∧
    2 ≤ (Proto.encodeUint32Field 2#32 pb.polys).length := by
  have hb := (Varint.encodeVarint_length_bounds (pb.polys.zeroExtend 64)).1
  rw [protoEncodeUint32Field_2_of_ne_zero (beq_eq_false_iff_ne.mp hpl),
    List.length_append, List.length_singleton]; omega

theorem encodePolyDecoderMsg_len_split (tag : BitVec 32) (pb : ProtoPolynomialDecoder) :
    (encodePolyDecoderMsg tag pb).length =
      (polyDecoderHeaderBytes tag pb).length +
        (Proto.encodeUint32Field 1#32 pb.ptsNeeded).length +
        (Proto.encodeUint32Field 2#32 pb.polys).length +
        (Varint.encodeRepeatedBytes 3 pb.pts).length +
        (Proto.encodeBoolField 4#32 pb.isComplete).length := by
  rw [encodePolyDecoderMsg_eq, List.length_append, List.length_append,
    List.length_append, List.length_append]

theorem polynomialDecoderPBEncodedLen_le_msg_len (tag : BitVec 32) (pb : ProtoPolynomialDecoder) :
    polynomialDecoderPBEncodedLen pb + 2 ≤ (encodePolyDecoderMsg tag pb).length := by
  have hraw : (PolynomialDecoder.encodeRaw (ProtoPolynomialDecoder.toPB pb)).length =
      polynomialDecoderPBEncodedLen pb :=
    polynomialDecoderPBEncodedLen_eq_proto pb
  have h1 : (PolynomialDecoder.encodeRaw (ProtoPolynomialDecoder.toPB pb)).length =
      (Proto.encodeUint32Field 1#32 pb.ptsNeeded).length +
        (Proto.encodeUint32Field 2#32 pb.polys).length +
        (Varint.encodeRepeatedBytes 3 pb.pts).length +
        (Proto.encodeBoolField 4#32 pb.isComplete).length := by
    dsimp only [PolynomialDecoder.encodeRaw, ProtoPolynomialDecoder.toPB]
    rw [← varintEncodeRepeatedBytes_3_eq_proto]
    simp only [List.length_append]
  have hhdr := (polyDecoderHeaderBytes_len_bounds tag pb).2.2
  rw [encodePolyDecoderMsg_len_split]
  omega

theorem polyDecoder_pts_lt_of_msg_len_lt {tag : BitVec 32} {pb : ProtoPolynomialDecoder}
    (h : (encodePolyDecoderMsg tag pb).length < 2 ^ 59) :
    pb.pts.length < 2 ^ 58 := by
  have h1 := encodeRepeatedBytes_length_ge_two_mul 3 pb.pts
  rw [encodePolyDecoderMsg_len_split] at h
  omega

/-! ## 2. Unpacking `Poly.protoPolynomialDecoderPinnedAt` via `satisfies_vecVecU8PinnedAt_iff` -/

/-- Active fields of `ProtoPolynomialDecoder` accessed during `+56..+248` of `PolynomialDecoder::encode`. -/
@[expose] def polyDecoderElemsAt (decA : BitVec 64) (g : Poly.ProtoPolynomialDecoderGhost)
    (pb : ProtoPolynomialDecoder)
    (ptsElems : List (BitVec 64 × List (BitVec 8))) : SepProp :=
  ((decA + 8#64) ↦₆₄ g.pts.ptr) ∗
    ((decA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
    ((decA + 24#64) ↦₃₂ pb.ptsNeeded) ∗
    ((decA + 28#64) ↦₃₂ pb.polys) ∗
    ((decA + 32#64) ↦₈ boolByte pb.isComplete) ∗
    repeatedBytesSliceAt g.pts.ptr ptsElems

/-- Framed remainder of `Poly.protoPolynomialDecoderPinnedAt A g decA pb` after extracting
`polyDecoderElemsAt decA g pb ptsElems`. -/
@[expose] def polyDecoderRestAt (A : RustAlloc) (decA : BitVec 64) (g : Poly.ProtoPolynomialDecoderGhost)
    (ptsElems : List (BitVec 64 × List (BitVec 8))) : SepProp :=
  (decA ↦₆₄ g.pts.cap) ∗
    vecVecU8PinnedRestAt A g.pts ptsElems ∗
    memRegion (decA + 0x21#64) 7

theorem satisfies_protoPolynomialDecoderPinnedAt_iff (A : RustAlloc)
    (g : Poly.ProtoPolynomialDecoderGhost) (decA : BitVec 64) (pb : ProtoPolynomialDecoder)
    (R : SepProp) (m : Memory) :
    (m ⊨ Poly.protoPolynomialDecoderPinnedAt A g decA pb ∗ R) ↔
    ∃ ptsElems : List (BitVec 64 × List (BitVec 8)),
      ptsElems.map Prod.snd = pb.pts ∧ pb.pts.length * 24 < 2 ^ 63 ∧
      (m ⊨ (polyDecoderElemsAt decA g pb ptsElems ∗
        polyDecoderRestAt A decA g ptsElems) ∗ R) := by
  dsimp only [Poly.protoPolynomialDecoderPinnedAt, Poly.protoPolynomialDecoderPtsNeededOff,
    Poly.protoPolynomialDecoderPolysOff, Poly.protoPolynomialDecoderIsCompleteOff,
    Poly.protoPolynomialDecoderPadOff, Poly.protoPolynomialDecoderPadSize,
    polyDecoderElemsAt, polyDecoderRestAt]
  constructor
  · intro hm
    have hm1 : m ⊨ vecVecU8PinnedAt A g.pts decA pb.pts ∗
        (((decA + 24#64) ↦₃₂ pb.ptsNeeded) ∗
          ((decA + 28#64) ↦₃₂ pb.polys) ∗
          ((decA + 32#64) ↦₈ boolByte pb.isComplete) ∗
          memRegion (decA + 33#64) 7 ∗ R) := by
      convert hm using 1; ac_rfl
    rcases (satisfies_vecVecU8PinnedAt_iff A g.pts decA pb.pts _ m).mp hm1 with
      ⟨ptsElems, hpts_eq, hpts_lt, hm2⟩
    refine ⟨ptsElems, hpts_eq, hpts_lt, ?_⟩
    convert hm2 using 1; ac_rfl
  · rintro ⟨ptsElems, hpts_eq, hpts_lt, hm⟩
    have hm1 : m ⊨ ((decA ↦₆₄ g.pts.cap) ∗ ((decA + 8#64) ↦₆₄ g.pts.ptr) ∗
        ((decA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
        repeatedBytesSliceAt g.pts.ptr ptsElems ∗ vecVecU8PinnedRestAt A g.pts ptsElems) ∗
        (((decA + 24#64) ↦₃₂ pb.ptsNeeded) ∗
          ((decA + 28#64) ↦₃₂ pb.polys) ∗
          ((decA + 32#64) ↦₈ boolByte pb.isComplete) ∗
          memRegion (decA + 33#64) 7 ∗ R) := by
      convert hm using 1; ac_rfl
    have hm2 := (satisfies_vecVecU8PinnedAt_iff A g.pts decA pb.pts _ m).mpr
      ⟨ptsElems, hpts_eq, hpts_lt, hm1⟩
    convert hm2 using 1; ac_rfl

/-- Variant of `polynomialDecoderEncodedLenPinnedSpec` whose postcondition unpacks
`Poly.protoPolynomialDecoderPinnedAt` into `polyDecoderElemsAt ∗ polyDecoderRestAt`. -/
@[expose] def polynomialDecoderEncodedLenElemsOutSpec (A : RustAlloc) :
    Spec PolynomialDecoderEncodedLenPinnedGhost where
  pre := (polynomialDecoderEncodedLenPinnedSpec A).pre
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (polynomialDecoderPBEncodedLen x.m) ∧
      sf.trace = s0.trace⌝ ∗
      (∃∗ ptsElems : List (BitVec 64 × List (BitVec 8)),
        ⌜ptsElems.map Prod.snd = x.m.pts ∧ x.m.pts.length * 24 < 2 ^ 63⌝ ∗
          polyDecoderElemsAt x.a x.g x.m ptsElems ∗
          polyDecoderRestAt A x.a x.g ptsElems) ∗
      stackAt s0.sp polyEncodedLenStack
  onPanic := (polynomialDecoderEncodedLenPinnedSpec A).onPanic
  onExit := (polynomialDecoderEncodedLenPinnedSpec A).onExit

theorem subroutine_ok_polyDecLenElemsOut_of_pinned {prog : Program} {entry : BitVec 64} {A : RustAlloc}
    (h : subroutine_ok prog entry (polynomialDecoderEncodedLenPinnedSpec A)) :
    subroutine_ok prog entry (polynomialDecoderEncodedLenElemsOutSpec A) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  refine h.mono_outcome x R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [polynomialDecoderEncodedLenPinnedSpec] at hq
    dsimp only [polynomialDecoderEncodedLenElemsOutSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨hpure, hq⟩
    refine ⟨hpure, ?_⟩
    have hq' : sf.mem ⊨ Poly.protoPolynomialDecoderPinnedAt A x.g x.a x.m ∗
        (stackAt s0.sp polyEncodedLenStack ∗ R) := by
      convert hq using 1; ac_rfl
    rcases (satisfies_protoPolynomialDecoderPinnedAt_iff A x.g x.a x.m _ sf.mem).mp hq' with
      ⟨ptsElems, hpts_eq, hpts_lt, hm⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨ptsElems, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hpts_eq, hpts_lt⟩, ?_⟩
    convert hm using 1; ac_rfl
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr hrest)

/-! ## 3. Specifications & Symbol Address Lemmas for `PolynomialDecoder::encode` -/

/-- Pinned ghost inputs for `prost::encoding::message::encode::<PolynomialDecoder, Vec<u8>>`. -/
structure EncodePolyDecoderPinnedGhost where
  tag  : BitVec 32
  decA : BitVec 64
  g    : Poly.ProtoPolynomialDecoderGhost
  dec  : ProtoPolynomialDecoder
  v    : BitVec 64
  cap  : BitVec 64
  ptr  : BitVec 64
  bs   : List (BitVec 8)

/-- Unpinned ghost inputs for `prost::encoding::message::encode::<PolynomialDecoder, Vec<u8>>`. -/
structure EncodePolyDecoderGhost where
  tag  : BitVec 32
  decA : BitVec 64
  dec  : ProtoPolynomialDecoder
  v    : BitVec 64
  cap  : BitVec 64
  ptr  : BitVec 64
  bs   : List (BitVec 8)

/-- Pinned specification of `prost::encoding::message::encode::<PolynomialDecoder, Vec<u8>>`
(`[local#1, 2]`), parameterized by `resStack`. Callers establish `x.dec.pts.length < 2 ^ 58`
and either spare capacity (`x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length ≤ x.cap.toNat`)
or the growth bound `x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length + 10 < 2 ^ 62`. -/
@[expose] def encodePolyDecoderPinnedSpecOf (resStack : Nat) (A : RustAlloc) :
    Spec EncodePolyDecoderPinnedGhost where
  pre := fun x s =>
    ⌜s.readReg32 .x0 = x.tag ∧
      s.readReg64 .x1 = x.decA ∧
      s.readReg64 .x2 = x.v ∧
      x.dec.pts.length < 2 ^ 58 ∧
      (x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length ≤ x.cap.toNat ∨
        x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length + 10 < 2 ^ 62)⌝ ∗
      Poly.protoPolynomialDecoderPinnedAt A x.g x.decA x.dec ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp (msgEnc48RepeatedStackOf resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      Poly.protoPolynomialDecoderPinnedAt A x.g x.decA x.dec ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A x.v cap' ptr' (x.bs ++ encodePolyDecoderMsg x.tag x.dec)) ∗
      A.pool ∗ stackAt s0.sp (msgEnc48RepeatedStackOf resStack)
  onPanic := fun _ s0 sf => msgEncOnPanic s0 sf

/-- Unpinned specification of `prost::encoding::message::encode::<PolynomialDecoder, Vec<u8>>`
(`[local#1, 2]`), parameterized by `resStack`. -/
@[expose] def encodePolyDecoderSpecOf (resStack : Nat) (A : RustAlloc) :
    Spec EncodePolyDecoderGhost where
  pre := fun x s =>
    ⌜s.readReg32 .x0 = x.tag ∧
      s.readReg64 .x1 = x.decA ∧
      s.readReg64 .x2 = x.v ∧
      x.dec.pts.length < 2 ^ 58 ∧
      (x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length ≤ x.cap.toNat ∨
        x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length + 10 < 2 ^ 62)⌝ ∗
      Poly.protoPolynomialDecoderAt A x.decA x.dec ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp (msgEnc48RepeatedStackOf resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      Poly.protoPolynomialDecoderAt A x.decA x.dec ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A x.v cap' ptr' (x.bs ++ encodePolyDecoderMsg x.tag x.dec)) ∗
      A.pool ∗ stackAt s0.sp (msgEnc48RepeatedStackOf resStack)
  onPanic := fun _ s0 sf => msgEncOnPanic s0 sf

abbrev encodePolyDecoderPinnedSpec (A : RustAlloc) : Spec EncodePolyDecoderPinnedGhost :=
  encodePolyDecoderPinnedSpecOf doReserveStack A
abbrev encodePolyDecoderSpec (A : RustAlloc) : Spec EncodePolyDecoderGhost :=
  encodePolyDecoderSpecOf doReserveStack A
abbrev encodePolyDecoderPinnedSpecX (A : RustAlloc) : Spec EncodePolyDecoderPinnedGhost :=
  encodePolyDecoderPinnedSpecOf doReserveStackX A
abbrev encodePolyDecoderSpecX (A : RustAlloc) : Spec EncodePolyDecoderGhost :=
  encodePolyDecoderSpecOf doReserveStackX A

theorem polyDecoder_post_unpinned_of_pinned {resStack : Nat} {A : RustAlloc}
    {x : EncodePolyDecoderGhost} {g : Poly.ProtoPolynomialDecoderGhost} {s0 sf : State} {R : SepProp}
    (hq : sf.mem ⊨ (encodePolyDecoderPinnedSpecOf resStack A).post
      ⟨x.tag, x.decA, g, x.dec, x.v, x.cap, x.ptr, x.bs⟩ s0 sf ∗ R) :
    sf.mem ⊨ (encodePolyDecoderSpecOf resStack A).post x s0 sf ∗ R := by
  dsimp only [encodePolyDecoderPinnedSpecOf] at hq
  dsimp only [encodePolyDecoderSpecOf]
  let Rest : SepProp := ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
      ⌜x.cap.toNat ≤ cap'.toNat ∧
        (x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length ≤ x.cap.toNat →
          cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
        vecU8At A x.v cap' ptr' (x.bs ++ encodePolyDecoderMsg x.tag x.dec)) ∗
    A.pool ∗ stackAt s0.sp (msgEnc48RepeatedStackOf resStack) ∗ R
  have hq' : sf.mem ⊨ Poly.protoPolynomialDecoderPinnedAt A g x.decA x.dec ∗ Rest := by
    convert hq using 1; dsimp only [Rest]; ac_rfl
  have hgoal : sf.mem ⊨ Poly.protoPolynomialDecoderAt A x.decA x.dec ∗ Rest := by
    rw [protoPolynomialDecoderAt_eq_exists_pinned, sepExists_sepConj_left, satisfies_sepExists]
    exact ⟨g, hq'⟩
  convert hgoal using 1; dsimp only [Rest]; ac_rfl

theorem polyDecoder_unpinned_of_pinned {resStack : Nat} {prog : Program} {entry : BitVec 64}
    {A : RustAlloc} (hpinned : subroutine_ok prog entry (encodePolyDecoderPinnedSpecOf resStack A)) :
    subroutine_ok prog entry (encodePolyDecoderSpecOf resStack A) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  dsimp only [encodePolyDecoderSpecOf] at hpre
  rw [protoPolynomialDecoderAt_eq_exists_pinned] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine hpinned.mono_outcome ⟨x.tag, x.decA, g, x.dec, x.v, x.cap, x.ptr, x.bs⟩
    R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | hrest
  · exact Or.inl ⟨hret, hcc, polyDecoder_post_unpinned_of_pinned hq⟩
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr hrest)

end CryptoVerification.SpqrV1.Prost.MessageEncode
