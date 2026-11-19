/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7a
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# SPQR V1 `<States>::from_pb`: Variant 7 (`Ct1Sampled`, niche variant) — Part B

`Option<ProtoPolynomialDecoder>` decomposition and error/cleanup blocks
(`+4548`, `+4528`, `+5444`, `+7100`, `+10556`, `+11096`) for Variant 7.
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
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero


/-! ## 1. `Option<ProtoPolynomialDecoder>` Decomposition & Cleanup at `+4548`, `+4528`, `+5444` -/

/-- Pure condition on the exposed `cap` word at `d` of `optProtoPolynomialDecoderAt A d m`. -/
@[expose] def v7_optDecoderCapProp (cap : BitVec 64) : Option ProtoPolynomialDecoder → Prop
  | none => cap = noneCap
  | some _ => cap.toNat * 24 < 2 ^ 63

/-- Remainder of `optProtoPolynomialDecoderAt A d m` after splitting out `d ↦₆₄ cap`,
    exposing `d + 24 ↦₃₂ pb.ptsNeeded` for the `+1068` check. -/
@[expose] def v7_optProtoPolyDecoderTail (A : RustAlloc) (d cap : BitVec 64) :
    Option ProtoPolynomialDecoder → SepProp
  | none => memRegion (d + 8#64) 32
  | some pb =>
    ∃∗ ptr : BitVec 64,
      ⌜pb.pts.length ≤ cap.toNat ∧ cap.toNat * 24 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((d + 8#64) ↦₆₄ ptr) ∗
      ((d + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
      (if cap = 0 then emp
       else A.live ptr (cap.toNat * 24) 8 ∗
         arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr pb.pts ∗
         memRegion (ptr + BitVec.ofNat 64 (pb.pts.length * 24))
           ((cap.toNat - pb.pts.length) * 24)) ∗
      ((d + protoPolynomialDecoderPtsNeededOff) ↦₃₂ pb.ptsNeeded) ∗
      ((d + protoPolynomialDecoderPolysOff) ↦₃₂ pb.polys) ∗
      ((d + protoPolynomialDecoderIsCompleteOff) ↦₈ boolByte pb.isComplete) ∗
      memRegion (d + protoPolynomialDecoderPadOff) protoPolynomialDecoderPadSize

theorem v7_optProtoPolyDecoder_expose_cap (A : RustAlloc) (d : BitVec 64)
    (m : Option ProtoPolynomialDecoder) :
    optProtoPolynomialDecoderAt A d m ⊢
      ∃∗ cap : BitVec 64,
        ⌜v7_optDecoderCapProp cap m⌝ ∗
        (d ↦₆₄ cap) ∗ v7_optProtoPolyDecoderTail A d cap m := by
  cases m with
  | none =>
    rw [optProtoPolynomialDecoderAt_none']
    refine Entails.sepExists_right noneCap ?_
    unfold v7_optDecoderCapProp v7_optProtoPolyDecoderTail
    exact Entails.pure_right rfl (Entails.refl _)
  | some pb =>
    rw [optProtoPolynomialDecoderAt_some']
    unfold protoPolynomialDecoderAt vecVecU8At vecOf Poly.vecHeaderBytes
    rw [sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro cap
    rw [sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro ptr
    refine Entails.sepExists_right cap ?_
    unfold vecAt vecBuf vecHeader v7_optDecoderCapProp v7_optProtoPolyDecoderTail
    refine Entails.trans
      (Entails.of_eq (show _ =
        ⌜pb.pts.length ≤ cap.toNat ∧ cap.toNat * 24 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        ((d ↦₆₄ cap) ∗
         (((d + 8#64) ↦₆₄ ptr) ∗
          ((d + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
          (if cap = 0 then emp
           else A.live ptr (cap.toNat * 24) 8 ∗
             arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr pb.pts ∗
             memRegion (ptr + BitVec.ofNat 64 (pb.pts.length * 24))
               ((cap.toNat - pb.pts.length) * 24)) ∗
          ((d + protoPolynomialDecoderPtsNeededOff) ↦₃₂ pb.ptsNeeded) ∗
          ((d + protoPolynomialDecoderPolysOff) ↦₃₂ pb.polys) ∗
          ((d + protoPolynomialDecoderIsCompleteOff) ↦₈ boolByte pb.isComplete) ∗
          memRegion (d + protoPolynomialDecoderPadOff) protoPolynomialDecoderPadSize)) by ac_rfl)) ?_
    apply Entails.pure_left; intro hp
    refine Entails.pure_right hp.2.1 ?_
    exact sepConj_mono_right (Entails.sepExists_right ptr (Entails.pure_right hp (Entails.refl _)))

theorem v7_optProtoPolyDecoder_unexpose_some (A : RustAlloc) (d cap : BitVec 64)
    (pb : ProtoPolynomialDecoder) :
    (d ↦₆₄ cap) ∗ v7_optProtoPolyDecoderTail A d cap (some pb) ⊢
      protoPolynomialDecoderAt A d pb := by
  unfold v7_optProtoPolyDecoderTail protoPolynomialDecoderAt vecVecU8At vecOf Poly.vecHeaderBytes
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro ptr
  rw [← sepConj_assoc, sepConj_comm (d ↦₆₄ cap), sepConj_assoc]
  apply Entails.pure_left; intro hp
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_right cap ?_
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_right ptr ?_
  unfold vecAt vecBuf vecHeader
  refine Entails.trans ?_
    (Entails.of_eq (show
      ⌜pb.pts.length ≤ cap.toNat ∧ cap.toNat * 24 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((d ↦₆₄ cap) ∗
       (((d + 8#64) ↦₆₄ ptr) ∗
        ((d + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
        (if cap = 0 then emp
         else A.live ptr (cap.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr pb.pts ∗
           memRegion (ptr + BitVec.ofNat 64 (pb.pts.length * 24))
             ((cap.toNat - pb.pts.length) * 24)) ∗
        ((d + protoPolynomialDecoderPtsNeededOff) ↦₃₂ pb.ptsNeeded) ∗
        ((d + protoPolynomialDecoderPolysOff) ↦₃₂ pb.polys) ∗
        ((d + protoPolynomialDecoderIsCompleteOff) ↦₈ boolByte pb.isComplete) ∗
        memRegion (d + protoPolynomialDecoderPadOff) protoPolynomialDecoderPadSize)) = _ by ac_rfl))
  exact Entails.pure_right hp (Entails.refl _)

theorem v7_cleanup_opt_decoder_some_pre (A : RustAlloc) (fsp pbA cap_dec : BitVec 64)
    (pb : ProtoPolynomialDecoder) (Frame : SepProp) :
    stackAt fsp encoderFromPbStack ∗
      (((pbA + 184#64) ↦₆₄ cap_dec) ∗
       v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec (some pb)) ∗
      A.pool ∗ Frame ⊢
    ∃∗ ptsPtr : BitVec 64,
      ⌜pb.pts.length ≤ cap_dec.toNat ∧ cap_dec.toNat * 24 < 2 ^ 63 ∧ ptsPtr ≠ 0⌝ ∗
      (stackAt fsp encoderFromPbStack ∗
       (((pbA + 184#64) ↦₆₄ cap_dec) ∗
        ((pbA + 192#64) ↦₆₄ ptsPtr) ∗
        ((pbA + 200#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
        (if cap_dec = 0 then emp
         else A.live ptsPtr (cap_dec.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
           memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24))
             ((cap_dec.toNat - pb.pts.length) * 24)) ∗
        memRegion (pbA + 208#64) 16) ∗
       A.pool ∗ Frame) := by
  unfold v7_optProtoPolyDecoderTail
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro ptsPtr
  refine Entails.sepExists_right ptsPtr ?_
  have htl := protoPolyDecoderTail_entails_memRegion_16 (pbA + 184#64)
    pb.ptsNeeded pb.polys pb.isComplete
  have h192 : (pbA + 184#64) + 8#64 = pbA + 192#64 := by bv_omega
  have h200 : (pbA + 184#64) + 16#64 = pbA + 200#64 := by bv_omega
  have h208 : (pbA + 184#64) + 24#64 = pbA + 208#64 := by bv_omega
  rw [h208] at htl
  rw [h192, h200]
  refine Entails.trans
    (Entails.of_eq (show _ =
      ⌜pb.pts.length ≤ cap_dec.toNat ∧ cap_dec.toNat * 24 < 2 ^ 63 ∧ ptsPtr ≠ 0⌝ ∗
      (((((pbA + 184#64) + protoPolynomialDecoderPtsNeededOff) ↦₃₂ pb.ptsNeeded) ∗
        (((pbA + 184#64) + protoPolynomialDecoderPolysOff) ↦₃₂ pb.polys) ∗
        (((pbA + 184#64) + protoPolynomialDecoderIsCompleteOff) ↦₈ boolByte pb.isComplete) ∗
        memRegion ((pbA + 184#64) + protoPolynomialDecoderPadOff) protoPolynomialDecoderPadSize) ∗
       (stackAt fsp encoderFromPbStack ∗
        ((pbA + 184#64) ↦₆₄ cap_dec) ∗
        ((pbA + 192#64) ↦₆₄ ptsPtr) ∗
        ((pbA + 200#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
        (if cap_dec = 0 then emp
         else A.live ptsPtr (cap_dec.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
           memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24))
             ((cap_dec.toNat - pb.pts.length) * 24)) ∗
        A.pool ∗ Frame)) by ac_rfl)) ?_
  apply Entails.pure_left; intro hp
  refine Entails.pure_right hp ?_
  exact Entails.trans (sepConj_mono_left htl) (Entails.of_eq (by ac_rfl))

theorem v7_stackAt_encoderFromPbStack_to_dropStack48 (fsp : BitVec 64) :
    stackAt fsp encoderFromPbStack ⊢
      stackAt fsp dropStack48 ∗ memRegion (fsp - 5152#64) 1008 := by
  have h := ProofLib.stackAt_split_bottom fsp dropStack48 1008 (by decide)
  change stackAt fsp encoderFromPbStack =
    memRegion (fsp - 5152#64) 1008 ∗ stackAt fsp dropStack48 at h
  rw [h]
  exact Entails.of_eq (by ac_rfl)

theorem v7_stackAt_dropStack48_to_encoderFromPbStack (fsp : BitVec 64) :
    stackAt fsp dropStack48 ∗ memRegion (fsp - 5152#64) 1008 ⊢
      stackAt fsp encoderFromPbStack := by
  have h := ProofLib.stackAt_split_bottom fsp dropStack48 1008 (by decide)
  change stackAt fsp encoderFromPbStack =
    memRegion (fsp - 5152#64) 1008 ∗ stackAt fsp dropStack48 at h
  rw [h]
  exact Entails.of_eq (by ac_rfl)

theorem v7_expose_some_protoPolyEncoder_pre (A : RustAlloc) (fsp pbA : BitVec 64)
    (enc : ProtoPolynomialEncoder) (Mid Frame : SepProp) :
    stackAt fsp encoderFromPbStack ∗
      protoPolynomialEncoderAt A (pbA + 128#64) enc ∗
      Mid ∗ A.pool ∗ Frame ⊢
    ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
      ⌜cap.toNat < 2 ^ 63⌝ ∗
      (stackAt fsp encoderFromPbStack ∗
       ((pbA + 128#64) ↦₆₄ cap) ∗
       protoPolynomialEncoderRestAt A (pbA + 128#64) cap ptr enc ∗
       Mid ∗ A.pool ∗ Frame) := by
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_left (protoPolynomialEncoderAt_expose_cap A (pbA + 128#64) enc))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro cap
  refine Entails.sepExists_right cap ?_
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right ptr ?_
  exact Entails.of_eq (by ac_rfl)

theorem v7_stackAt_encoderFromPbStack_to_dropStack32 (fsp : BitVec 64) :
    stackAt fsp encoderFromPbStack ⊢
      stackAt fsp dropStack32 ∗ memRegion (fsp - 5152#64) 1024 := by
  have h := ProofLib.stackAt_split_bottom fsp dropStack32 1024 (by decide)
  change stackAt fsp encoderFromPbStack =
    memRegion (fsp - 5152#64) 1024 ∗ stackAt fsp dropStack32 at h
  rw [h]
  exact Entails.of_eq (by ac_rfl)

theorem v7_stackAt_dropStack32_to_encoderFromPbStack (fsp : BitVec 64) :
    stackAt fsp dropStack32 ∗ memRegion (fsp - 5152#64) 1024 ⊢
      stackAt fsp encoderFromPbStack := by
  have h := ProofLib.stackAt_split_bottom fsp dropStack32 1024 (by decide)
  change stackAt fsp encoderFromPbStack =
    memRegion (fsp - 5152#64) 1024 ∗ stackAt fsp dropStack32 at h
  rw [h]
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.States.FromPb
