/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
public import LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBase
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint2Base
import LibsignalBinary.Proofs.SpqrV1.Auth.Encode1
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Decodes
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.Defs
import ProofLib.SepLogic.WPp

/-!
# Shared Base for `prost::encoding::message::encode::<EpochDirection, Vec<u8>>` (`[local#1, #2]`)

Shared pure encoding model bridge lemmas, Hoare specifications (`encodeEpochDirectionPinnedSpec`,
`encodeEpochDirectionSpec`), callee address equations, and shared basic-block stepping lemmas for:
- `prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#1]`
  at `0x3776c` (`169` insns, `676` bytes)
- `prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#2]`
  at `0x527c0` (`183` insns, `732` bytes)
-/

public section

namespace CryptoVerification.SpqrV1.Prost.MessageEncode

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Auth
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

@[local arm64_norm] theorem zext64_trunc32_orr_1 (w : BitVec 32) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 w ||| 1#64)) =
      BitVec.zeroExtend 64 w ||| 1#64 := by bv_bits

@[local arm64_norm] theorem zext64_trunc32_orr_100000001 (w : BitVec 32) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 w ||| 0x100000001#64)) =
      BitVec.zeroExtend 64 w ||| 1#64 := by bv_bits

@[local arm64_norm] theorem zext64_orr_1_32 (w : BitVec 32) :
    BitVec.zeroExtend 64 (w ||| 1#32) = BitVec.zeroExtend 64 w ||| 1#64 := by bv_bits

/-! ## 1. Pure Model Equivalence & Decomposition Lemmas -/

/-- Pure bytes appended by `prost::encoding::message::encode::<EpochDirection, Vec<u8>>`:
`Proto.encodeMessage EpochDirectionPB.encodeRaw tag d`
(definitionally equal to `Proto.encodeOptMessage EpochDirectionPB.encodeRaw tag (some d)`). -/
abbrev encodeEpochDirectionMsg (tag : BitVec 32) (d : EpochDirectionPB) : List (BitVec 8) :=
  Proto.encodeMessage EpochDirectionPB.encodeRaw tag d

/-- Header bytes (varint-encoded key `(tag << 3) | 2` + varint-encoded payload length) of
`encodeEpochDirectionMsg tag d`. -/
@[expose] def epochDirectionHeaderBytes (tag : BitVec 32) (d : EpochDirectionPB) : List (BitVec 8) :=
  Proto.encodeKey tag .lengthDelimited ++
    CryptoVerification.LibsignalProtoCodec.encodeVarint
      (BitVec.ofNat 64 (epochDirectionPBEncodedLen d))

/-- Field 1 (`ctr : u32`, tag 1) bytes of `encodeEpochDirectionMsg tag d`. -/
@[expose] def epochDirectionCtrBytes (d : EpochDirectionPB) : List (BitVec 8) :=
  Proto.encodeUint32Field 1#32 d.ctr

/-- Field 2 (`next : Vec<u8>`, tag 2) bytes of `encodeEpochDirectionMsg tag d`. -/
@[expose] def epochDirectionNextBytes (d : EpochDirectionPB) : List (BitVec 8) :=
  Proto.encodeBytesField 2#32 d.next

/-- Field 3 (`prev : Vec<u8>`, tag 3) bytes of `encodeEpochDirectionMsg tag d`. -/
@[expose] def epochDirectionPrevBytes (d : EpochDirectionPB) : List (BitVec 8) :=
  Proto.encodeBytesField 3#32 d.prev

private theorem protoEncodeKey_3_lengthDelimited :
    Proto.encodeKey 3#32 .lengthDelimited = [0x1a#8] := rfl

private theorem protoEncodeBytesField_3_of_ne_nil {bs : List (BitVec 8)} (hne : bs ≠ []) :
    Proto.encodeBytesField 3#32 bs =
      [0x1a#8] ++ CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 bs.length) ++ bs := by
  have hemp : bs.isEmpty = false := List.isEmpty_eq_false_iff.mpr hne
  simp only [Proto.encodeBytesField, hemp, Bool.false_eq_true, ↓reduceIte,
    Proto.encodeBytesUncond, protoEncodeKey_3_lengthDelimited, protoEncodeVarint_eq_codec]

theorem bytesField_3_length_of_ne_nil {bs : List (BitVec 8)} (hne : bs ≠ []) :
    (Proto.encodeBytesField 3#32 bs).length =
      1 + (CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 bs.length)).length + bs.length := by
  rw [protoEncodeBytesField_3_of_ne_nil hne]
  simp only [List.length_append, List.length_singleton]

theorem encodeVarint_epochDirection_tag_eq_proto (tag : BitVec 32) :
    CryptoVerification.LibsignalProtoCodec.encodeVarint
      (((tag <<< 3) ||| (Proto.WireType.lengthDelimited).toU32).zeroExtend 64) =
      Proto.encodeKey tag .lengthDelimited := by
  simp only [Proto.encodeKey, Proto.WireType.toU32, protoEncodeVarint_eq_codec]

theorem encodeEpochDirectionMsg_eq_parts (tag : BitVec 32) (d : EpochDirectionPB) :
    encodeEpochDirectionMsg tag d =
      epochDirectionHeaderBytes tag d ++
        epochDirectionCtrBytes d ++
        epochDirectionNextBytes d ++
        epochDirectionPrevBytes d := by
  have hlen : (EpochDirectionPB.encodeRaw d).length = epochDirectionPBEncodedLen d :=
    epochDirectionPBEncodedLen_eq_proto d
  dsimp only [encodeEpochDirectionMsg, Proto.encodeMessage, epochDirectionHeaderBytes,
    epochDirectionCtrBytes, epochDirectionNextBytes, epochDirectionPrevBytes]
  rw [hlen, protoEncodeVarint_eq_codec]
  simp only [EpochDirectionPB.encodeRaw, List.append_assoc]

theorem bs0_append_epochDirectionHeaderBytes (bs0 : List (BitVec 8)) (tag : BitVec 32)
    (d : EpochDirectionPB) :
    (bs0 ++ Proto.encodeKey tag .lengthDelimited) ++
      CryptoVerification.LibsignalProtoCodec.encodeVarint
        (BitVec.ofNat 64 (epochDirectionPBEncodedLen d)) =
      bs0 ++ epochDirectionHeaderBytes tag d := by
  simp only [epochDirectionHeaderBytes, List.append_assoc]

theorem bs_append_epochDirectionCtrBytes_of_ne_zero (bs : List (BitVec 8)) (d : EpochDirectionPB)
    (h : (d.ctr == 0#32) = false) :
    (bs ++ [0x08#8]) ++ CryptoVerification.LibsignalProtoCodec.encodeVarint (d.ctr.zeroExtend 64) =
      bs ++ epochDirectionCtrBytes d := by
  rw [epochDirectionCtrBytes, protoEncodeUint32Field_1_of_ne_zero (beq_eq_false_iff_ne.mp h),
    List.append_assoc]

theorem bs_append_epochDirectionCtrBytes_of_zero (bs : List (BitVec 8)) (d : EpochDirectionPB)
    (h : (d.ctr == 0#32) = true) :
    bs ++ epochDirectionCtrBytes d = bs := by
  rw [epochDirectionCtrBytes, beq_iff_eq.mp h, protoEncodeUint32Field_zero, List.append_nil]

theorem bs_append_epochDirectionNextBytes_of_ne_empty (bs1 : List (BitVec 8)) (d : EpochDirectionPB)
    (hnext : d.next.isEmpty = false) :
    ((bs1 ++ [0x12#8]) ++ CryptoVerification.LibsignalProtoCodec.encodeVarint
      (BitVec.ofNat 64 d.next.length)) ++ d.next = bs1 ++ epochDirectionNextBytes d := by
  rw [epochDirectionNextBytes, protoEncodeBytesField_2_of_ne_nil (List.isEmpty_eq_false_iff.mp hnext)]
  simp only [List.append_assoc]

theorem bs_append_epochDirectionNextBytes_of_empty (bs1 : List (BitVec 8)) (d : EpochDirectionPB)
    (hnext : d.next.isEmpty = true) : bs1 ++ epochDirectionNextBytes d = bs1 := by
  simp only [epochDirectionNextBytes, List.isEmpty_iff.mp hnext, protoEncodeBytesField_nil, List.append_nil]

theorem bs_append_epochDirectionPrevBytes_of_ne_empty (bs2 : List (BitVec 8)) (d : EpochDirectionPB)
    (hprev : d.prev.isEmpty = false) :
    ((bs2 ++ [0x1a#8]) ++ CryptoVerification.LibsignalProtoCodec.encodeVarint
      (BitVec.ofNat 64 d.prev.length)) ++ d.prev = bs2 ++ epochDirectionPrevBytes d := by
  rw [epochDirectionPrevBytes, protoEncodeBytesField_3_of_ne_nil (List.isEmpty_eq_false_iff.mp hprev)]
  simp only [List.append_assoc]

theorem bs_append_epochDirectionPrevBytes_of_empty (bs2 : List (BitVec 8)) (d : EpochDirectionPB)
    (hprev : d.prev.isEmpty = true) : bs2 ++ epochDirectionPrevBytes d = bs2 := by
  simp only [epochDirectionPrevBytes, List.isEmpty_iff.mp hprev, protoEncodeBytesField_nil, List.append_nil]

theorem bs0_append_encodeEpochDirectionMsg (bs0 : List (BitVec 8)) (tag : BitVec 32)
    (d : EpochDirectionPB) :
    (((bs0 ++ epochDirectionHeaderBytes tag d) ++ epochDirectionCtrBytes d) ++
      epochDirectionNextBytes d) ++ epochDirectionPrevBytes d =
      bs0 ++ encodeEpochDirectionMsg tag d := by
  rw [encodeEpochDirectionMsg_eq_parts]
  simp only [List.append_assoc]

theorem encodeEpochDirectionMsg_len_split (tag : BitVec 32) (d : EpochDirectionPB) :
    (encodeEpochDirectionMsg tag d).length =
      (epochDirectionHeaderBytes tag d).length +
        (epochDirectionCtrBytes d).length +
        (epochDirectionNextBytes d).length +
        (epochDirectionPrevBytes d).length := by
  simpa only [List.nil_append, List.length_append, Nat.add_assoc] using
    (congrArg List.length (bs0_append_encodeEpochDirectionMsg [] tag d)).symm

theorem epochDirectionPBEncodedLen_eq_fields_len (d : EpochDirectionPB) :
    epochDirectionPBEncodedLen d =
      (epochDirectionCtrBytes d).length +
        (epochDirectionNextBytes d).length +
        (epochDirectionPrevBytes d).length := by
  have h : (EpochDirectionPB.encodeRaw d).length = epochDirectionPBEncodedLen d :=
    epochDirectionPBEncodedLen_eq_proto d
  rw [← h]
  simp only [EpochDirectionPB.encodeRaw, epochDirectionCtrBytes, epochDirectionNextBytes,
    epochDirectionPrevBytes, List.length_append]

theorem epochDirectionHeaderBytes_len_bounds (tag : BitVec 32) (d : EpochDirectionPB) :
    (epochDirectionHeaderBytes tag d).length =
      (Proto.encodeKey tag .lengthDelimited).length +
        (CryptoVerification.LibsignalProtoCodec.encodeVarint
          (BitVec.ofNat 64 (epochDirectionPBEncodedLen d))).length ∧
    (Proto.encodeKey tag .lengthDelimited).length + 1 ≤ (epochDirectionHeaderBytes tag d).length ∧
    2 ≤ (epochDirectionHeaderBytes tag d).length := by
  have h1 := Varint.encodeVarint_length_bounds
    (((tag <<< 3) ||| (Proto.WireType.lengthDelimited).toU32).zeroExtend 64)
  rw [encodeVarint_epochDirection_tag_eq_proto] at h1
  have h2 := Varint.encodeVarint_length_bounds (BitVec.ofNat 64 (epochDirectionPBEncodedLen d))
  dsimp only [epochDirectionHeaderBytes]
  rw [List.length_append]
  exact ⟨rfl, by omega, by omega⟩

theorem epochDirectionCtrBytes_len_of_ne_zero (d : EpochDirectionPB) (h : (d.ctr == 0#32) = false) :
    (epochDirectionCtrBytes d).length =
      1 + (CryptoVerification.LibsignalProtoCodec.encodeVarint (d.ctr.zeroExtend 64)).length ∧
    2 ≤ (epochDirectionCtrBytes d).length := by
  have hb := Varint.encodeVarint_length_bounds (d.ctr.zeroExtend 64)
  rw [epochDirectionCtrBytes, protoEncodeUint32Field_1_of_ne_zero (beq_eq_false_iff_ne.mp h),
    List.length_append, List.length_singleton]
  exact ⟨rfl, by omega⟩

theorem epochDirectionNextBytes_len_of_ne_empty (d : EpochDirectionPB) (hnext : d.next.isEmpty = false) :
    (epochDirectionNextBytes d).length =
      1 + (CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 d.next.length)).length +
        d.next.length :=
  bytesField_2_length_of_ne_nil (List.isEmpty_eq_false_iff.mp hnext)

theorem epochDirectionPrevBytes_len_of_ne_empty (d : EpochDirectionPB) (hprev : d.prev.isEmpty = false) :
    (epochDirectionPrevBytes d).length =
      1 + (CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 d.prev.length)).length +
        d.prev.length :=
  bytesField_3_length_of_ne_nil (List.isEmpty_eq_false_iff.mp hprev)

/-! ## 2. Specifications of `encode<EpochDirection> [local#1, #2]` -/

/-- Pinned ghost arguments of `prost::encoding::message::encode::<EpochDirection, Vec<u8>>`:
- `tag`: field tag (`w0`, `1#32` for `Epoch.send` or `2#32` for `Epoch.recv`),
- `dirA`: pointer to `&spqr::proto::pq_ratchet::chain::epoch::EpochDirection` (`x1`, 56 bytes),
- `g`: `(cap, ptr)` pins for `next` and `prev`,
- `dir`: pure `EpochDirectionPB` (`ProtoEpochDirection`) value,
- `v`: pointer to `buf: &mut Vec<u8>` (`x2`, 24 bytes),
- `cap`, `ptr`, `bs`: initial capacity, buffer pointer, and contents of `buf`. -/
structure EncodeEpochDirectionPinnedGhost where
  tag : BitVec 32
  dirA : BitVec 64
  g : EpochDirectionPBGhost
  dir : EpochDirectionPB
  v : BitVec 64
  cap : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

/-- Unpinned ghost arguments of `prost::encoding::message::encode::<EpochDirection, Vec<u8>>`. -/
structure EncodeEpochDirectionGhost where
  tag : BitVec 32
  dirA : BitVec 64
  dir : EpochDirectionPB
  v : BitVec 64
  cap : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

/-- Pinned specification of `prost::encoding::message::encode::<EpochDirection, Vec<u8>>` (`[local#1, #2]`),
parameterized by `resStack`. Callers establish either spare capacity
(`x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat`) or the growth bound
`x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length + 10 < 2 ^ 62`. -/
@[expose] def encodeEpochDirectionPinnedSpecOf (resStack : Nat) (A : RustAlloc) :
    Spec EncodeEpochDirectionPinnedGhost where
  pre := fun x s =>
    ⌜s.readReg32 .x0 = x.tag ∧
      s.readReg64 .x1 = x.dirA ∧
      s.readReg64 .x2 = x.v ∧
      (x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat ∨
        x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length + 10 < 2 ^ 62)⌝ ∗
      epochDirectionPBPinnedAt A x.g x.dirA x.dir ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp (authEncodeStackOf resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      epochDirectionPBPinnedAt A x.g x.dirA x.dir ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A x.v cap' ptr' (x.bs ++ encodeEpochDirectionMsg x.tag x.dir)) ∗
      A.pool ∗ stackAt s0.sp (authEncodeStackOf resStack)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Unpinned specification of `prost::encoding::message::encode::<EpochDirection, Vec<u8>>` (`[local#1, #2]`),
parameterized by `resStack`. -/
@[expose] def encodeEpochDirectionSpecOf (resStack : Nat) (A : RustAlloc) :
    Spec EncodeEpochDirectionGhost where
  pre := fun x s =>
    ⌜s.readReg32 .x0 = x.tag ∧
      s.readReg64 .x1 = x.dirA ∧
      s.readReg64 .x2 = x.v ∧
      (x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat ∨
        x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length + 10 < 2 ^ 62)⌝ ∗
      epochDirectionPBAt A x.dirA x.dir ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp (authEncodeStackOf resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      epochDirectionPBAt A x.dirA x.dir ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A x.v cap' ptr' (x.bs ++ encodeEpochDirectionMsg x.tag x.dir)) ∗
      A.pool ∗ stackAt s0.sp (authEncodeStackOf resStack)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

abbrev encodeEpochDirectionPinnedSpec (A : RustAlloc) : Spec EncodeEpochDirectionPinnedGhost :=
  encodeEpochDirectionPinnedSpecOf doReserveStack A

abbrev encodeEpochDirectionPinnedSpecX (A : RustAlloc) : Spec EncodeEpochDirectionPinnedGhost :=
  encodeEpochDirectionPinnedSpecOf doReserveStackX A

abbrev encodeEpochDirectionSpec (A : RustAlloc) : Spec EncodeEpochDirectionGhost :=
  encodeEpochDirectionSpecOf doReserveStack A

abbrev encodeEpochDirectionSpecX (A : RustAlloc) : Spec EncodeEpochDirectionGhost :=
  encodeEpochDirectionSpecOf doReserveStackX A

theorem epochDirection_post_unpinned_of_pinned {resStack : Nat} {A : RustAlloc}
    {x : EncodeEpochDirectionGhost} {g : EpochDirectionPBGhost} {s0 sf : State} {R : SepProp}
    (hq : sf.mem ⊨ (encodeEpochDirectionPinnedSpecOf resStack A).post
      ⟨x.tag, x.dirA, g, x.dir, x.v, x.cap, x.ptr, x.bs⟩ s0 sf ∗ R) :
    sf.mem ⊨ (encodeEpochDirectionSpecOf resStack A).post x s0 sf ∗ R := by
  dsimp only [encodeEpochDirectionPinnedSpecOf] at hq
  dsimp only [encodeEpochDirectionSpecOf]
  let Rest : SepProp := ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
      ⌜x.cap.toNat ≤ cap'.toNat ∧
        (x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat →
          cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
        vecU8At A x.v cap' ptr' (x.bs ++ encodeEpochDirectionMsg x.tag x.dir)) ∗
    A.pool ∗ stackAt s0.sp (authEncodeStackOf resStack) ∗ R
  have hq' : sf.mem ⊨ epochDirectionPBPinnedAt A g x.dirA x.dir ∗ Rest := by
    convert hq using 1; dsimp only [Rest]; ac_rfl
  have hgoal : sf.mem ⊨ epochDirectionPBAt A x.dirA x.dir ∗ Rest := by
    rw [epochDirectionPBAt_eq_exists_pinned, sepExists_sepConj_left, satisfies_sepExists]
    exact ⟨g, hq'⟩
  convert hgoal using 1; dsimp only [Rest]; ac_rfl

theorem epochDirection_unpinned_of_pinned {resStack : Nat} {prog : Program} {entry : BitVec 64}
    {A : RustAlloc} (hpinned : subroutine_ok prog entry (encodeEpochDirectionPinnedSpecOf resStack A)) :
    subroutine_ok prog entry (encodeEpochDirectionSpecOf resStack A) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  dsimp only [encodeEpochDirectionSpecOf] at hpre
  rw [epochDirectionPBAt_eq_exists_pinned] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine hpinned.mono_outcome ⟨x.tag, x.dirA, g, x.dir, x.v, x.cap, x.ptr, x.bs⟩ R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | hrest
  · exact Or.inl ⟨hret, hcc, epochDirection_post_unpinned_of_pinned hq⟩
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr hrest)

/-! ## 3. Memory Decomposition & Bounds of `epochDirectionPBPinnedAt` -/

/-- Read-only fields of `EpochDirectionPB` accessed by `encode<EpochDirection>`. -/
@[expose] def epochDirectionElemsAt (dirA nextPtr prevPtr : BitVec 64) (d : EpochDirectionPB) : SepProp :=
  ((dirA + 8#64) ↦₆₄ nextPtr) ∗
  ((dirA + 16#64) ↦₆₄ BitVec.ofNat 64 d.next.length) ∗
  (nextPtr ↦ₛ d.next) ∗
  ((dirA + 32#64) ↦₆₄ prevPtr) ∗
  ((dirA + 40#64) ↦₆₄ BitVec.ofNat 64 d.prev.length) ∗
  (prevPtr ↦ₛ d.prev) ∗
  ((dirA + 48#64) ↦₃₂ d.ctr)

/-- Frame remainder of `epochDirectionPBPinnedAt` after extracting `epochDirectionElemsAt`. -/
@[expose] def epochDirectionRestAt (A : RustAlloc) (g : EpochDirectionPBGhost) (dirA : BitVec 64)
    (d : EpochDirectionPB) : SepProp :=
  Varint.vecU8ElemRestAt A dirA g.next.cap g.next.ptr d.next ∗
  Varint.vecU8ElemRestAt A (dirA + 24#64) g.prev.cap g.prev.ptr d.prev ∗
  memRegion (dirA + 52#64) 4

theorem epochDirectionPBPinnedAt_eq_elems (A : RustAlloc) (g : EpochDirectionPBGhost)
    (dirA : BitVec 64) (d : EpochDirectionPB)
    (hnext : g.next.cap = 0 → d.next = [])
    (hprev : g.prev.cap = 0 → d.prev = []) :
    epochDirectionPBPinnedAt A g dirA d =
      epochDirectionElemsAt dirA g.next.ptr g.prev.ptr d ∗
      epochDirectionRestAt A g dirA d := by
  unfold epochDirectionPBPinnedAt epochDirectionElemsAt epochDirectionRestAt
  rw [Varint.vecU8At_eq_repeatedBytesElemAt A dirA g.next.cap g.next.ptr d.next hnext,
    Varint.vecU8At_eq_repeatedBytesElemAt A (dirA + 0x18#64) g.prev.cap g.prev.ptr d.prev hprev]
  unfold repeatedBytesElemAt
  have h24 : (0x18#64 : BitVec 64) = 24#64 := rfl
  have h48 : (0x30#64 : BitVec 64) = 48#64 := rfl
  have h52 : (0x34#64 : BitVec 64) = 52#64 := rfl
  have h32 : dirA + 24#64 + 8#64 = dirA + 32#64 := by bv_omega
  have h40 : dirA + 24#64 + 16#64 = dirA + 40#64 := by bv_omega
  rw [h24, h48, h52, h32, h40]
  ac_rfl

theorem epochDirectionPBPinnedAt_bounds_of_satisfies {m : Memory} {A : RustAlloc}
    {g : EpochDirectionPBGhost} {dirA : BitVec 64} {d : EpochDirectionPB} {F : SepProp}
    (h : m ⊨ epochDirectionPBPinnedAt A g dirA d ∗ F) :
    d.next.length < 2 ^ 63 ∧ d.prev.length < 2 ^ 63 ∧
    (g.next.cap = 0 → d.next = []) ∧
    (g.prev.cap = 0 → d.prev = []) := by
  rw [epochDirectionPBPinnedAt] at h
  have hnext := Auth.vecU8At_bounds_of_satisfies (A := A) (v := dirA)
    (cap := g.next.cap) (ptr := g.next.ptr) (bs := d.next)
    (F := vecU8At A (dirA + 0x18#64) g.prev.cap g.prev.ptr d.prev ∗
      ((dirA + 0x30#64) ↦₃₂ d.ctr) ∗ memRegion (dirA + 0x34#64) 4 ∗ F)
    (by convert h using 1; ac_rfl)
  have hprev := Auth.vecU8At_bounds_of_satisfies (A := A) (v := dirA + 0x18#64)
    (cap := g.prev.cap) (ptr := g.prev.ptr) (bs := d.prev)
    (F := vecU8At A dirA g.next.cap g.next.ptr d.next ∗
      ((dirA + 0x30#64) ↦₃₂ d.ctr) ∗ memRegion (dirA + 0x34#64) 4 ∗ F)
    (by convert h using 1; ac_rfl)
  refine ⟨by omega, by omega, ?_, ?_⟩
  · intro h0; apply List.eq_nil_iff_length_eq_zero.mpr; have hle := hnext.1; rw [h0] at hle; exact Nat.eq_zero_of_le_zero hle
  · intro h0; apply List.eq_nil_iff_length_eq_zero.mpr; have hle := hprev.1; rw [h0] at hle; exact Nat.eq_zero_of_le_zero hle

/-- Saved 64-byte stack frame of `encode<EpochDirection>`. -/
@[expose] def epochDirectionSavedFrame (sp fp lr r24 r23 r22 r21 r20 r19 : BitVec 64) : SepProp :=
  ((sp - 64#64) ↦₆₄ fp) ∗ ((sp - 56#64) ↦₆₄ lr) ∗
  ((sp - 48#64) ↦₆₄ r24) ∗ ((sp - 40#64) ↦₆₄ r23) ∗
  ((sp - 32#64) ↦₆₄ r22) ∗ ((sp - 24#64) ↦₆₄ r21) ∗
  ((sp - 16#64) ↦₆₄ r20) ∗ ((sp - 8#64) ↦₆₄ r19)

end CryptoVerification.SpqrV1.Prost.MessageEncode
