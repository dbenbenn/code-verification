/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncodedLenBase
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint2Base
public import LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBase
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Decodes
import ProofLib.SepLogic.WPp

/-!
# Shared Specification, Pure Lemmas, and Stepping Helpers for `PolynomialEncoder::encode`

Covers shared definitions and stepping blocks for:
- `prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialEncoder, alloc::vec::Vec<u8>> [local#1]`
  (`0x37690..0x3776c`, 55 insns)
- `prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialEncoder, alloc::vec::Vec<u8>> [local#2]`
  (`0x526d4..0x527c0`, 59 insns)
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

/-- Full encoded bytes produced by `prost::encoding::message::encode::<PolynomialEncoder, Vec<u8>>`
(hardcoded tag `2#32`, wire type `lengthDelimited` = `2`). -/
@[expose] def encodePolyEncoderMsg (pb : ProtoPolynomialEncoder) : List (BitVec 8) :=
  Proto.encodeMessage PolynomialEncoder.encodeRaw 2#32 (ProtoPolynomialEncoder.toPB pb)

/-- Header bytes (`[0x12#8] ++ encodeVarint (encoded_len)`) of `PolynomialEncoder::encode`. -/
@[expose] def polyEncoderHeaderBytes (pb : ProtoPolynomialEncoder) : List (BitVec 8) :=
  [0x12#8] ++ LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 (polynomialEncoderPBEncodedLen pb))

private theorem codec_encodeKey_2_eq_proto :
    LibsignalProtoCodec.encodeKey 2 .lengthDelimited = Proto.encodeKey 2#32 .lengthDelimited := by
  decide

private theorem codec_encodeKey_3_eq_proto :
    LibsignalProtoCodec.encodeKey 3 .lengthDelimited = Proto.encodeKey 3#32 .lengthDelimited := by
  decide

theorem varintEncodeRepeatedBytes_2_eq_proto :
    ∀ (vs : List (List (BitVec 8))),
      Varint.encodeRepeatedBytes 2 vs = Proto.encodeRepeatedBytes 2#32 vs
  | [] => rfl
  | bs :: rest => by
      dsimp only [Varint.encodeRepeatedBytes, encodeBytesField]
      rw [varintEncodeRepeatedBytes_2_eq_proto rest, codec_encodeKey_2_eq_proto]
      dsimp only [Proto.encodeRepeatedBytes, List.foldr, Proto.encodeBytesUncond]
      rw [protoEncodeVarint_eq_codec]

theorem varintEncodeRepeatedBytes_3_eq_proto :
    ∀ (vs : List (List (BitVec 8))),
      Varint.encodeRepeatedBytes 3 vs = Proto.encodeRepeatedBytes 3#32 vs
  | [] => rfl
  | bs :: rest => by
      dsimp only [Varint.encodeRepeatedBytes, encodeBytesField]
      rw [varintEncodeRepeatedBytes_3_eq_proto rest, codec_encodeKey_3_eq_proto]
      dsimp only [Proto.encodeRepeatedBytes, List.foldr, Proto.encodeBytesUncond]
      rw [protoEncodeVarint_eq_codec]

theorem encodePolyEncoderMsg_eq (pb : ProtoPolynomialEncoder) :
    encodePolyEncoderMsg pb =
      polyEncoderHeaderBytes pb ++
        Proto.encodeUint32Field 1#32 pb.idx ++
        Varint.encodeRepeatedBytes 2 pb.pts ++
        Varint.encodeRepeatedBytes 3 pb.polys := by
  have hlen : (PolynomialEncoder.encodeRaw (ProtoPolynomialEncoder.toPB pb)).length =
      polynomialEncoderPBEncodedLen pb :=
    polynomialEncoderPBEncodedLen_eq_proto pb
  dsimp only [encodePolyEncoderMsg, Proto.encodeMessage, polyEncoderHeaderBytes]
  rw [protoEncodeKey_lengthDelimited_2, protoEncodeVarint_eq_codec, hlen]
  dsimp only [PolynomialEncoder.encodeRaw, ProtoPolynomialEncoder.toPB]
  rw [← varintEncodeRepeatedBytes_2_eq_proto, ← varintEncodeRepeatedBytes_3_eq_proto]
  simp only [List.append_assoc]

theorem bs0_append_encodePolyEncoderMsg (bs0 : List (BitVec 8)) (pb : ProtoPolynomialEncoder) :
    bs0 ++ encodePolyEncoderMsg pb =
      (((bs0 ++ polyEncoderHeaderBytes pb) ++
        Proto.encodeUint32Field 1#32 pb.idx) ++
        Varint.encodeRepeatedBytes 2 pb.pts) ++
        Varint.encodeRepeatedBytes 3 pb.polys := by
  rw [encodePolyEncoderMsg_eq]; simp only [List.append_assoc]

theorem bs0_append_polyEncoderHeaderBytes (bs0 : List (BitVec 8)) (pb : ProtoPolynomialEncoder) :
    (bs0 ++ [0x12#8]) ++
      LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 (polynomialEncoderPBEncodedLen pb)) =
    bs0 ++ polyEncoderHeaderBytes pb := by
  rw [polyEncoderHeaderBytes, List.append_assoc]

theorem polyEncoderHeaderBytes_len_bounds (pb : ProtoPolynomialEncoder) :
    (polyEncoderHeaderBytes pb).length =
      1 + (LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 (polynomialEncoderPBEncodedLen pb))).length ∧
    2 ≤ (polyEncoderHeaderBytes pb).length := by
  have hb := Varint.encodeVarint_length_bounds (BitVec.ofNat 64 (polynomialEncoderPBEncodedLen pb))
  rw [polyEncoderHeaderBytes, List.length_append, List.length_singleton]
  omega

theorem bs_append_idx_of_ne_zero (bs : List (BitVec 8)) (pb : ProtoPolynomialEncoder)
    (hidx : (pb.idx == 0#32) = false) :
    (bs ++ [0x08#8]) ++ LibsignalProtoCodec.encodeVarint (pb.idx.zeroExtend 64) =
      bs ++ Proto.encodeUint32Field 1#32 pb.idx := by
  rw [protoEncodeUint32Field_1_of_ne_zero (beq_eq_false_iff_ne.mp hidx), List.append_assoc]

theorem bs_append_idx_of_zero (bs : List (BitVec 8)) (pb : ProtoPolynomialEncoder)
    (hidx : (pb.idx == 0#32) = true) :
    bs ++ Proto.encodeUint32Field 1#32 pb.idx = bs := by
  rw [eq_of_beq hidx, protoEncodeUint32Field_zero, List.append_nil]

theorem idx_field_len_of_ne_zero (pb : ProtoPolynomialEncoder) (hidx : (pb.idx == 0#32) = false) :
    (Proto.encodeUint32Field 1#32 pb.idx).length =
      1 + (LibsignalProtoCodec.encodeVarint (pb.idx.zeroExtend 64)).length ∧
    2 ≤ (Proto.encodeUint32Field 1#32 pb.idx).length := by
  have hb := (Varint.encodeVarint_length_bounds (pb.idx.zeroExtend 64)).1
  rw [protoEncodeUint32Field_1_of_ne_zero (beq_eq_false_iff_ne.mp hidx),
    List.length_append, List.length_singleton]
  omega

theorem encodePolyEncoderMsg_len_split (pb : ProtoPolynomialEncoder) :
    (encodePolyEncoderMsg pb).length =
      (polyEncoderHeaderBytes pb).length +
        (Proto.encodeUint32Field 1#32 pb.idx).length +
        (Varint.encodeRepeatedBytes 2 pb.pts).length +
        (Varint.encodeRepeatedBytes 3 pb.polys).length := by
  rw [encodePolyEncoderMsg_eq, List.length_append, List.length_append, List.length_append]

theorem polynomialEncoderPBEncodedLen_le_msg_len (pb : ProtoPolynomialEncoder) :
    polynomialEncoderPBEncodedLen pb + 2 ≤ (encodePolyEncoderMsg pb).length := by
  have hraw : (PolynomialEncoder.encodeRaw (ProtoPolynomialEncoder.toPB pb)).length =
      polynomialEncoderPBEncodedLen pb :=
    polynomialEncoderPBEncodedLen_eq_proto pb
  have h1 : (PolynomialEncoder.encodeRaw (ProtoPolynomialEncoder.toPB pb)).length =
      (Proto.encodeUint32Field 1#32 pb.idx).length +
        (Varint.encodeRepeatedBytes 2 pb.pts).length +
        (Varint.encodeRepeatedBytes 3 pb.polys).length := by
    dsimp only [PolynomialEncoder.encodeRaw, ProtoPolynomialEncoder.toPB]
    rw [← varintEncodeRepeatedBytes_2_eq_proto, ← varintEncodeRepeatedBytes_3_eq_proto]
    simp only [List.length_append]
  have hhdr := (polyEncoderHeaderBytes_len_bounds pb).2
  rw [encodePolyEncoderMsg_len_split]
  omega

theorem encodeBytesField_some_length_ge_two (tag : Nat) (bs : List (BitVec 8)) :
    2 ≤ (encodeBytesField tag (some bs)).length := by
  dsimp only [encodeBytesField, encodeKey]
  rw [List.length_append, List.length_append]
  have h1 := (Varint.encodeVarint_length_bounds (BitVec.ofNat 64 (tag * 8 + WireType.lengthDelimited.toNat))).1
  have h2 := (Varint.encodeVarint_length_bounds (BitVec.ofNat 64 bs.length)).1
  omega

theorem encodeRepeatedBytes_length_ge_two_mul (tag : Nat) (vs : List (List (BitVec 8))) :
    2 * vs.length ≤ (Varint.encodeRepeatedBytes tag vs).length := by
  induction vs with
  | nil => simp [Varint.encodeRepeatedBytes]
  | cons bs rest ih =>
    simp only [Varint.encodeRepeatedBytes, List.length_append, List.length_cons]
    have h1 := encodeBytesField_some_length_ge_two tag bs
    omega

theorem polyEncoder_pts_polys_lt_of_msg_len_lt {pb : ProtoPolynomialEncoder}
    (h : (encodePolyEncoderMsg pb).length < 2 ^ 59) :
    pb.pts.length < 2 ^ 58 ∧ pb.polys.length < 2 ^ 58 := by
  have h1 := encodeRepeatedBytes_length_ge_two_mul 2 pb.pts
  have h2 := encodeRepeatedBytes_length_ge_two_mul 3 pb.polys
  rw [encodePolyEncoderMsg_len_split] at h
  omega


/-! ## 2. Unpacking `Poly.protoPolynomialEncoderPinnedAt` via `satisfies_vecVecU8PinnedAt_iff` -/

/-- Active fields of `ProtoPolynomialEncoder` accessed during `+76..+168` of `PolynomialEncoder::encode`. -/
@[expose] def polyEncoderElemsAt (encA : BitVec 64) (g : Poly.ProtoPolynomialEncoderGhost)
    (pb : ProtoPolynomialEncoder)
    (ptsElems polysElems : List (BitVec 64 × List (BitVec 8))) : SepProp :=
  ((encA + 8#64) ↦₆₄ g.pts.ptr) ∗
    ((encA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
    ((encA + 32#64) ↦₆₄ g.polys.ptr) ∗
    ((encA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
    ((encA + 48#64) ↦₃₂ pb.idx) ∗
    repeatedBytesSliceAt g.pts.ptr ptsElems ∗
    repeatedBytesSliceAt g.polys.ptr polysElems

/-- Framed remainder of `Poly.protoPolynomialEncoderPinnedAt A g encA pb` after extracting
`polyEncoderElemsAt encA g pb ptsElems polysElems`. -/
@[expose] def polyEncoderRestAt (A : RustAlloc) (encA : BitVec 64) (g : Poly.ProtoPolynomialEncoderGhost)
    (ptsElems polysElems : List (BitVec 64 × List (BitVec 8))) : SepProp :=
  (encA ↦₆₄ g.pts.cap) ∗
    ((encA + 24#64) ↦₆₄ g.polys.cap) ∗
    vecVecU8PinnedRestAt A g.pts ptsElems ∗
    vecVecU8PinnedRestAt A g.polys polysElems ∗
    memRegion (encA + 0x34#64) 4

theorem satisfies_protoPolynomialEncoderPinnedAt_iff (A : RustAlloc)
    (g : Poly.ProtoPolynomialEncoderGhost) (encA : BitVec 64) (pb : ProtoPolynomialEncoder)
    (R : SepProp) (m : Memory) :
    (m ⊨ Poly.protoPolynomialEncoderPinnedAt A g encA pb ∗ R) ↔
    ∃ ptsElems polysElems : List (BitVec 64 × List (BitVec 8)),
      ptsElems.map Prod.snd = pb.pts ∧ pb.pts.length * 24 < 2 ^ 63 ∧
      polysElems.map Prod.snd = pb.polys ∧ pb.polys.length * 24 < 2 ^ 63 ∧
      (m ⊨ (polyEncoderElemsAt encA g pb ptsElems polysElems ∗
        polyEncoderRestAt A encA g ptsElems polysElems) ∗ R) := by
  dsimp only [Poly.protoPolynomialEncoderPinnedAt, Poly.protoPolynomialEncoderPolysOff,
    Poly.protoPolynomialEncoderIdxOff, Poly.protoPolynomialEncoderPadOff,
    Poly.protoPolynomialEncoderPadSize, polyEncoderElemsAt, polyEncoderRestAt]
  have ha32 : encA + 24#64 + 8#64 = encA + 32#64 := by bv_omega
  have ha40 : encA + 24#64 + 16#64 = encA + 40#64 := by bv_omega
  have ha48 : encA + 0x30#64 = encA + 48#64 := rfl
  constructor
  · intro hm
    have hm0 : m ⊨ Poly.vecVecU8PinnedAt A g.pts encA pb.pts ∗
        (Poly.vecVecU8PinnedAt A g.polys (encA + 24#64) pb.polys ∗
          ((encA + 48#64) ↦₃₂ pb.idx) ∗ memRegion (encA + 0x34#64) 4 ∗ R) := by
      rw [ha48] at hm; convert hm using 1; ac_rfl
    obtain ⟨ptsElems, hpts_eq, hpts_lt, hm1⟩ :=
      (satisfies_vecVecU8PinnedAt_iff A g.pts encA pb.pts _ m).mp hm0
    have hm1' : m ⊨ Poly.vecVecU8PinnedAt A g.polys (encA + 24#64) pb.polys ∗
        (((encA ↦₆₄ g.pts.cap) ∗ ((encA + 8#64) ↦₆₄ g.pts.ptr) ∗
          ((encA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
          repeatedBytesSliceAt g.pts.ptr ptsElems ∗ vecVecU8PinnedRestAt A g.pts ptsElems) ∗
          ((encA + 48#64) ↦₃₂ pb.idx) ∗ memRegion (encA + 0x34#64) 4 ∗ R) := by
      convert hm1 using 1; ac_rfl
    obtain ⟨polysElems, hpolys_eq, hpolys_lt, hm2⟩ :=
      (satisfies_vecVecU8PinnedAt_iff A g.polys (encA + 24#64) pb.polys _ m).mp hm1'
    rw [ha32, ha40] at hm2
    refine ⟨ptsElems, polysElems, hpts_eq, hpts_lt, hpolys_eq, hpolys_lt, ?_⟩
    convert hm2 using 1; ac_rfl
  · rintro ⟨ptsElems, polysElems, hpts_eq, hpts_lt, hpolys_eq, hpolys_lt, hm⟩
    have hm2 : m ⊨ (((encA + 24#64) ↦₆₄ g.polys.cap) ∗
        ((encA + 24#64 + 8#64) ↦₆₄ g.polys.ptr) ∗
        ((encA + 24#64 + 16#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
        repeatedBytesSliceAt g.polys.ptr polysElems ∗
        vecVecU8PinnedRestAt A g.polys polysElems) ∗
        (((encA ↦₆₄ g.pts.cap) ∗ ((encA + 8#64) ↦₆₄ g.pts.ptr) ∗
          ((encA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
          repeatedBytesSliceAt g.pts.ptr ptsElems ∗ vecVecU8PinnedRestAt A g.pts ptsElems) ∗
          ((encA + 48#64) ↦₃₂ pb.idx) ∗ memRegion (encA + 0x34#64) 4 ∗ R) := by
      rw [ha32, ha40]; convert hm using 1; ac_rfl
    have hm1' := (satisfies_vecVecU8PinnedAt_iff A g.polys (encA + 24#64) pb.polys _ m).mpr
      ⟨polysElems, hpolys_eq, hpolys_lt, hm2⟩
    have hm1 : m ⊨ ((encA ↦₆₄ g.pts.cap) ∗ ((encA + 8#64) ↦₆₄ g.pts.ptr) ∗
        ((encA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
        repeatedBytesSliceAt g.pts.ptr ptsElems ∗ vecVecU8PinnedRestAt A g.pts ptsElems) ∗
        (Poly.vecVecU8PinnedAt A g.polys (encA + 24#64) pb.polys ∗
          ((encA + 48#64) ↦₃₂ pb.idx) ∗ memRegion (encA + 0x34#64) 4 ∗ R) := by
      convert hm1' using 1; ac_rfl
    have hm0 := (satisfies_vecVecU8PinnedAt_iff A g.pts encA pb.pts _ m).mpr
      ⟨ptsElems, hpts_eq, hpts_lt, hm1⟩
    rw [ha48]; convert hm0 using 1; ac_rfl

/-- Variant of `polynomialEncoderEncodedLenPinnedSpec` whose postcondition exposes
`polyEncoderElemsAt` and `polyEncoderRestAt` for the subsequent field encodes. -/
@[expose] def polynomialEncoderEncodedLenElemsOutSpec (A : RustAlloc) :
    Spec PolynomialEncoderEncodedLenPinnedGhost where
  pre := (polynomialEncoderEncodedLenPinnedSpec A).pre
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (polynomialEncoderPBEncodedLen x.m) ∧ sf.trace = s0.trace⌝ ∗
      (∃∗ ptsElems : List (BitVec 64 × List (BitVec 8)),
       ∃∗ polysElems : List (BitVec 64 × List (BitVec 8)),
        ⌜ptsElems.map Prod.snd = x.m.pts ∧ x.m.pts.length * 24 < 2 ^ 63 ∧
          polysElems.map Prod.snd = x.m.polys ∧ x.m.polys.length * 24 < 2 ^ 63⌝ ∗
        polyEncoderElemsAt x.a x.g x.m ptsElems polysElems ∗
        polyEncoderRestAt A x.a x.g ptsElems polysElems) ∗
      stackAt s0.sp polyEncodedLenStack

theorem subroutine_ok_polyEncLenElemsOut_of_pinned {prog : Program} {entry : BitVec 64}
    {A : RustAlloc}
    (hok : subroutine_ok prog entry (polynomialEncoderEncodedLenPinnedSpec A)) :
    subroutine_ok prog entry (polynomialEncoderEncodedLenElemsOutSpec A) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  refine (hok.to_outcome x R s0 hpc hrun hpre hsp).mono_outcome ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | hrest)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [polynomialEncoderEncodedLenPinnedSpec] at hq
    dsimp only [polynomialEncoderEncodedLenElemsOutSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    obtain ⟨hpure, hq_mem⟩ := hq
    refine ⟨hpure, ?_⟩
    have hq_mem' : sf.mem ⊨ Poly.protoPolynomialEncoderPinnedAt A x.g x.a x.m ∗
        (stackAt s0.sp polyEncodedLenStack ∗ R) := by
      convert hq_mem using 1; ac_rfl
    obtain ⟨ptsElems, polysElems, hpts_eq, hpts_lt, hpolys_eq, hpolys_lt, hm_unp⟩ :=
      (satisfies_protoPolynomialEncoderPinnedAt_iff A x.g x.a x.m _ sf.mem).mp hq_mem'
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨ptsElems, polysElems, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hpts_eq, hpts_lt, hpolys_eq, hpolys_lt⟩, ?_⟩
    convert hm_unp using 1; ac_rfl
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr hrest)

/-! ## 3. Shared `encodeRepeatedStackOf`-Frame Call Helpers (`step_msg48rep_*`) -/

theorem calleeSavedPreserved_setPC {s0 s : State} (pc : BitVec 64)
    (hcc : CalleeSavedPreserved s0 s) :
    CalleeSavedPreserved s0 (s.setPC pc) := by
  simpa only [CalleeSavedPreserved, State.readReg64_setPC, calleeSavedVRegs_setPC] using hcc

/-! ## 4. Specifications & Symbol Address Lemmas for `PolynomialEncoder::encode` -/

/-- Pinned ghost inputs for `prost::encoding::message::encode::<PolynomialEncoder, Vec<u8>>`. -/
structure EncodePolyEncoderPinnedGhost where
  encA : BitVec 64
  g    : Poly.ProtoPolynomialEncoderGhost
  enc  : ProtoPolynomialEncoder
  v    : BitVec 64
  cap  : BitVec 64
  ptr  : BitVec 64
  bs   : List (BitVec 8)

/-- Unpinned ghost inputs for `prost::encoding::message::encode::<PolynomialEncoder, Vec<u8>>`. -/
structure EncodePolyEncoderGhost where
  encA : BitVec 64
  enc  : ProtoPolynomialEncoder
  v    : BitVec 64
  cap  : BitVec 64
  ptr  : BitVec 64
  bs   : List (BitVec 8)

/-- Pinned specification of `prost::encoding::message::encode::<PolynomialEncoder, Vec<u8>>`
(`[local#1, 2]`), parameterized by `resStack`. Callers establish `x.enc.pts.length < 2 ^ 58`,
`x.enc.polys.length < 2 ^ 58`, and either spare capacity
(`x.bs.length + (encodePolyEncoderMsg x.enc).length ≤ x.cap.toNat`) or the growth bound
`x.bs.length + (encodePolyEncoderMsg x.enc).length + 10 < 2 ^ 62`. -/
@[expose] def encodePolyEncoderPinnedSpecOf (resStack : Nat) (A : RustAlloc) :
    Spec EncodePolyEncoderPinnedGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.encA ∧
      s.readReg64 .x1 = x.v ∧
      x.enc.pts.length < 2 ^ 58 ∧
      x.enc.polys.length < 2 ^ 58 ∧
      (x.bs.length + (encodePolyEncoderMsg x.enc).length ≤ x.cap.toNat ∨
        x.bs.length + (encodePolyEncoderMsg x.enc).length + 10 < 2 ^ 62)⌝ ∗
      Poly.protoPolynomialEncoderPinnedAt A x.g x.encA x.enc ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp (msgEnc48RepeatedStackOf resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      Poly.protoPolynomialEncoderPinnedAt A x.g x.encA x.enc ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodePolyEncoderMsg x.enc).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A x.v cap' ptr' (x.bs ++ encodePolyEncoderMsg x.enc)) ∗
      A.pool ∗ stackAt s0.sp (msgEnc48RepeatedStackOf resStack)
  onPanic := fun _ s0 sf => msgEncOnPanic s0 sf

/-- Unpinned specification of `prost::encoding::message::encode::<PolynomialEncoder, Vec<u8>>`
(`[local#1, 2]`), parameterized by `resStack`. -/
@[expose] def encodePolyEncoderSpecOf (resStack : Nat) (A : RustAlloc) :
    Spec EncodePolyEncoderGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.encA ∧
      s.readReg64 .x1 = x.v ∧
      x.enc.pts.length < 2 ^ 58 ∧
      x.enc.polys.length < 2 ^ 58 ∧
      (x.bs.length + (encodePolyEncoderMsg x.enc).length ≤ x.cap.toNat ∨
        x.bs.length + (encodePolyEncoderMsg x.enc).length + 10 < 2 ^ 62)⌝ ∗
      Poly.protoPolynomialEncoderAt A x.encA x.enc ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp (msgEnc48RepeatedStackOf resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      Poly.protoPolynomialEncoderAt A x.encA x.enc ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodePolyEncoderMsg x.enc).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A x.v cap' ptr' (x.bs ++ encodePolyEncoderMsg x.enc)) ∗
      A.pool ∗ stackAt s0.sp (msgEnc48RepeatedStackOf resStack)
  onPanic := fun _ s0 sf => msgEncOnPanic s0 sf

abbrev encodePolyEncoderPinnedSpec (A : RustAlloc) : Spec EncodePolyEncoderPinnedGhost :=
  encodePolyEncoderPinnedSpecOf doReserveStack A

abbrev encodePolyEncoderSpec (A : RustAlloc) : Spec EncodePolyEncoderGhost :=
  encodePolyEncoderSpecOf doReserveStack A

abbrev encodePolyEncoderPinnedSpecX (A : RustAlloc) : Spec EncodePolyEncoderPinnedGhost :=
  encodePolyEncoderPinnedSpecOf doReserveStackX A

abbrev encodePolyEncoderSpecX (A : RustAlloc) : Spec EncodePolyEncoderGhost :=
  encodePolyEncoderSpecOf doReserveStackX A

theorem polyEncoder_post_unpinned_of_pinned {resStack : Nat} {A : RustAlloc}
    {x : EncodePolyEncoderGhost} {g : Poly.ProtoPolynomialEncoderGhost} {s0 sf : State} {R : SepProp}
    (hq : sf.mem ⊨ (encodePolyEncoderPinnedSpecOf resStack A).post
      ⟨x.encA, g, x.enc, x.v, x.cap, x.ptr, x.bs⟩ s0 sf ∗ R) :
    sf.mem ⊨ (encodePolyEncoderSpecOf resStack A).post x s0 sf ∗ R := by
  dsimp only [encodePolyEncoderPinnedSpecOf] at hq
  dsimp only [encodePolyEncoderSpecOf]
  let Rest : SepProp := ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
      ⌜x.cap.toNat ≤ cap'.toNat ∧
        (x.bs.length + (encodePolyEncoderMsg x.enc).length ≤ x.cap.toNat → cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
        vecU8At A x.v cap' ptr' (x.bs ++ encodePolyEncoderMsg x.enc)) ∗
    A.pool ∗ stackAt s0.sp (msgEnc48RepeatedStackOf resStack) ∗ R
  have hq' : sf.mem ⊨ Poly.protoPolynomialEncoderPinnedAt A g x.encA x.enc ∗ Rest := by
    convert hq using 1; dsimp only [Rest]; ac_rfl
  have hgoal : sf.mem ⊨ Poly.protoPolynomialEncoderAt A x.encA x.enc ∗ Rest := by
    rw [protoPolynomialEncoderAt_eq_exists_pinned, sepExists_sepConj_left, satisfies_sepExists]
    exact ⟨g, hq'⟩
  convert hgoal using 1; dsimp only [Rest]; ac_rfl

theorem polyEncoder_unpinned_of_pinned {resStack : Nat} {prog : Program} {entry : BitVec 64}
    {A : RustAlloc} (hpinned : subroutine_ok prog entry (encodePolyEncoderPinnedSpecOf resStack A)) :
    subroutine_ok prog entry (encodePolyEncoderSpecOf resStack A) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  dsimp only [encodePolyEncoderSpecOf] at hpre
  rw [protoPolynomialEncoderAt_eq_exists_pinned] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine (hpinned.to_outcome ⟨x.encA, g, x.enc, x.v, x.cap, x.ptr, x.bs⟩ R s0 hpc hrun hpre hsp).mono_outcome ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | hrest)
  · exact Or.inl ⟨hret, hcc, polyEncoder_post_unpinned_of_pinned hq⟩
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr hrest)

end CryptoVerification.SpqrV1.Prost.MessageEncode
