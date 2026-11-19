/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7b -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7a
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 7 (`Ct1Sampled`, `+1056`) — Part D

Entry exposure, dispatch with `x9`, early error paths (`+1056 -> +1080/+3480 -> +4528 -> +4632`),
and `<Ct1Sent>::from_pb` phase (`+3480 -> +3548 -> +3576..+3648` and `Err` at `+3552 -> +5444`)
for Variant 7 (`InnerState.ct1Sampled`, jump-table target `+1056`).
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



/-! ## 1. Dispatch (`+36 -> +1056`) with `x9` and `Ct1Sampled` Input Decomposition -/

/-- Isomorphism between `V1State.Unchunked.Ct1Sent` and `V1State.Unchunked.Ct1SentEkReceived`
at the proto layout level (five 24-byte `Vec<u8>` fields + `u64 epoch`). -/
@[expose] def v7_ct1SentToCt1SentEkReceived (st : V1State.Unchunked.Ct1Sent) :
    V1State.Unchunked.Ct1SentEkReceived :=
  { es := st.hdr, ek := st.es, ct1 := st.ct1, auth := st.auth, epoch := st.epoch }

theorem v7_protoUnchunkedCt1SentAt_eq (A : RustAlloc) (a : BitVec 64)
    (st : V1State.Unchunked.Ct1Sent) :
    protoUnchunkedCt1SentAt A a st =
      protoUnchunkedCt1SentEkReceivedAt A a (v7_ct1SentToCt1SentEkReceived st) := rfl

/-- Tail of `optProtoUnchunkedCt1SentAt A pbA optUc` after exposing `(pbA ↦₆₄ w0)`. -/
@[expose] def v7_optProtoUnchunkedCt1SentTail (A : RustAlloc) (pbA w0 : BitVec 64)
    (optUc : Option V1State.Unchunked.Ct1Sent) : SepProp :=
  match optUc with
  | none => memRegion (pbA + 8#64) 120
  | some uc =>
    ∃∗ ptr : BitVec 64,
      protoUnchunkedCt1SentEkReceivedRestAt A pbA w0 ptr
        (v7_ct1SentToCt1SentEkReceived uc)

@[expose] def v7_optUcCapProp (w0 : BitVec 64) (optUc : Option V1State.Unchunked.Ct1Sent) : Prop :=
  match optUc with
  | none => w0 = noneCap
  | some _ => w0.toNat < 2 ^ 63

theorem v7_optUcCapProp_imp_or {w0 : BitVec 64} {optUc : Option V1State.Unchunked.Ct1Sent}
    (h : v7_optUcCapProp w0 optUc) : w0 = noneCap ∨ w0.toNat < 2 ^ 63 := by
  cases optUc with
  | none => exact Or.inl h
  | some _ => exact Or.inr h

theorem v7_optProtoUnchunkedCt1Sent_expose_w0 (A : RustAlloc) (pbA : BitVec 64)
    (optUc : Option V1State.Unchunked.Ct1Sent) :
    optProtoUnchunkedCt1SentAt A pbA optUc ⊢
      ∃∗ w0 : BitVec 64,
        ⌜v7_optUcCapProp w0 optUc⌝ ∗
        ((pbA ↦₆₄ w0) ∗ v7_optProtoUnchunkedCt1SentTail A pbA w0 optUc) := by
  cases optUc with
  | none =>
    rw [optProtoUnchunkedCt1SentAt_none]
    dsimp only [v7_optProtoUnchunkedCt1SentTail, v7_optUcCapProp]
    refine Entails.sepExists_right noneCap ?_
    exact Entails.pure_right rfl (Entails.refl _)
  | some uc =>
    rw [optProtoUnchunkedCt1SentAt_some, v7_protoUnchunkedCt1SentAt_eq]
    refine Entails.trans
      (protoUnchunkedCt1SentEkReceivedAt_expose_cap A pbA (v7_ct1SentToCt1SentEkReceived uc)) ?_
    apply Entails.sepExists_elim; intro cap
    apply Entails.sepExists_elim; intro ptr
    apply Entails.pure_left; intro hlt
    dsimp only [v7_optProtoUnchunkedCt1SentTail, v7_optUcCapProp]
    refine Entails.sepExists_right cap ?_
    refine Entails.pure_right hlt ?_
    rw [sepExists_sepConj_right]
    refine Entails.sepExists_right ptr ?_
    exact Entails.of_eq (by ac_rfl)

theorem v7_optProtoUnchunkedCt1Sent_unexpose_some (A : RustAlloc) (pbA w0 : BitVec 64)
    (uc : V1State.Unchunked.Ct1Sent) :
    (pbA ↦₆₄ w0) ∗ v7_optProtoUnchunkedCt1SentTail A pbA w0 (some uc) ⊢
      protoUnchunkedCt1SentAt A pbA uc := by
  dsimp only [v7_optProtoUnchunkedCt1SentTail]
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro ptr
  rw [v7_protoUnchunkedCt1SentAt_eq]
  exact protoUnchunkedCt1SentEkReceivedAt_unexpose_cap A pbA w0 ptr
    (v7_ct1SentToCt1SentEkReceived uc)

theorem v7_optProtoUnchunkedCt1Sent_unexpose_none (pbA : BitVec 64) :
    (pbA ↦₆₄ noneCap) ∗ memRegion (pbA + 8#64) 120 ⊢
      memRegion pbA 128 := by
  rw [ProofLib.memRegion_split pbA 8 120 (by decide)]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion pbA noneCap)

/-! ## 2. Pure Model Reduction Lemmas for `InnerState.ct1Sampled` -/

theorem v7_ptsNeeded_check_eq (ptsNeeded : BitVec 32) :
    (ptsNeeded.toNat != ENCAPSULATION_KEY_SIZE / 2) = !(ptsNeeded == 576#32) := by
  have h576 : ENCAPSULATION_KEY_SIZE / 2 = (576#32).toNat := rfl
  rw [h576]
  cases h : ptsNeeded == 576#32 <;> simp only [Bool.not_true, Bool.not_false]
  · rw [beq_eq_false_iff_ne] at h
    rw [bne_iff_ne, ne_eq, BitVec.toNat_inj]
    exact h
  · rw [beq_iff_eq] at h
    subst h
    decide

theorem v7_from_pb_ct1Sampled_bad_pts (F : ShaCompress)
    (s : V1State.Chunked.Ct1Sampled) (d : PolynomialDecoder)
    (hd : s.receivingEk = some d)
    (hpts : (d.ptsNeeded == 576#32) = false) :
    States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.ct1Sampled s) } =
      .error (.err .msgDecode) := by
  have hne : (d.ptsNeeded.toNat != ENCAPSULATION_KEY_SIZE / 2) = true := by
    rw [v7_ptsNeeded_check_eq, hpts]; rfl
  unfold States.from_pb Chunked.SendCt.Ct1Sampled.from_pb
  simp only [hd, hne, ↓reduceIte, Bind.bind, Except.bind, Functor.map, Except.map]

@[expose] def v7_receivingEkPtsOk (optDecPb : Option PolynomialDecoder) : Prop :=
  match optDecPb with
  | none => True
  | some d => (d.ptsNeeded == 576#32) = true

theorem v7_receivingEk_pts_false {d : PolynomialDecoder}
    (hok : (d.ptsNeeded == 576#32) = true) :
    (d.ptsNeeded.toNat != ENCAPSULATION_KEY_SIZE / 2) = false := by
  rw [v7_ptsNeeded_check_eq, hok]; rfl

theorem v7_from_pb_ct1Sampled_uc_none (F : ShaCompress)
    (s : V1State.Chunked.Ct1Sampled)
    (hpts : v7_receivingEkPtsOk s.receivingEk)
    (huc : s.uc = none) :
    States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.ct1Sampled s) } =
      .error (.err .stateDecode) := by
  unfold States.from_pb Chunked.SendCt.Ct1Sampled.from_pb
  unfold v7_receivingEkPtsOk at hpts
  cases hdec : s.receivingEk with
  | none =>
    simp only [hdec, huc, Bind.bind, Except.bind, Functor.map, Except.map]
  | some d =>
    rw [hdec] at hpts
    simp only [hdec, v7_receivingEk_pts_false hpts, Bool.false_eq_true, ↓reduceIte,
      huc, Bind.bind, Except.bind, Functor.map, Except.map]

theorem v7_from_pb_ct1Sampled_uc_err (F : ShaCompress)
    (s : V1State.Chunked.Ct1Sampled) (u : V1State.Unchunked.Ct1Sent) (err : Error)
    (hpts : v7_receivingEkPtsOk s.receivingEk)
    (huc : s.uc = some u)
    (herr : Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApi F) u = .error (.err err)) :
    States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.ct1Sampled s) } =
      .error (.err err) := by
  unfold States.from_pb Chunked.SendCt.Ct1Sampled.from_pb
  unfold v7_receivingEkPtsOk at hpts
  cases hdec : s.receivingEk with
  | none =>
    simp only [hdec, huc, herr, Bind.bind, Except.bind, Functor.map, Except.map]
  | some d =>
    rw [hdec] at hpts
    simp only [hdec, v7_receivingEk_pts_false hpts, Bool.false_eq_true, ↓reduceIte,
      huc, herr, Bind.bind, Except.bind, Functor.map, Except.map]

theorem v7_from_pb_ct1Sampled_enc_none (F : ShaCompress)
    (s : V1State.Chunked.Ct1Sampled) (u : V1State.Unchunked.Ct1Sent)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (hpts : v7_receivingEkPtsOk s.receivingEk)
    (huc : s.uc = some u)
    (huc_ok : Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApi F) u = .ok uc)
    (henc : s.sendingCt1 = none) :
    States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.ct1Sampled s) } =
      .error (.err .stateDecode) := by
  unfold States.from_pb Chunked.SendCt.Ct1Sampled.from_pb
  unfold v7_receivingEkPtsOk at hpts
  cases hdec : s.receivingEk with
  | none =>
    simp only [hdec, huc, huc_ok, henc, encoderFromPbStateDecode_none,
      Bind.bind, Except.bind, Functor.map, Except.map]
  | some d =>
    rw [hdec] at hpts
    simp only [hdec, v7_receivingEk_pts_false hpts, Bool.false_eq_true, ↓reduceIte,
      huc, huc_ok, henc, encoderFromPbStateDecode_none,
      Bind.bind, Except.bind, Functor.map, Except.map]

theorem v7_from_pb_ct1Sampled_enc_err (F : ShaCompress)
    (s : V1State.Chunked.Ct1Sampled) (u : V1State.Unchunked.Ct1Sent)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (encPb : PolynomialEncoder) (e : PolynomialError)
    (hpts : v7_receivingEkPtsOk s.receivingEk)
    (huc : s.uc = some u)
    (huc_ok : Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApi F) u = .ok uc)
    (henc : s.sendingCt1 = some encPb)
    (henc_err : fromPbResult (pbToProtoPolyEncoder encPb) = .error e) :
    States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.ct1Sampled s) } =
      .error (.err .stateDecode) := by
  unfold States.from_pb Chunked.SendCt.Ct1Sampled.from_pb
  unfold v7_receivingEkPtsOk at hpts
  cases hdec : s.receivingEk with
  | none =>
    simp only [hdec, huc, huc_ok, henc, encoderFromPbStateDecode_some, henc_err,
      Bind.bind, Except.bind, Functor.map, Except.map]
  | some d =>
    rw [hdec] at hpts
    simp only [hdec, v7_receivingEk_pts_false hpts, Bool.false_eq_true, ↓reduceIte,
      huc, huc_ok, henc, encoderFromPbStateDecode_some, henc_err,
      Bind.bind, Except.bind, Functor.map, Except.map]

theorem v7_from_pb_ct1Sampled_dec_none (F : ShaCompress)
    (s : V1State.Chunked.Ct1Sampled) (u : V1State.Unchunked.Ct1Sent)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (encPb : PolynomialEncoder) (enc : PolyEncoder)
    (huc : s.uc = some u)
    (huc_ok : Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApi F) u = .ok uc)
    (henc : s.sendingCt1 = some encPb)
    (henc_ok : fromPbResult (pbToProtoPolyEncoder encPb) = .ok enc)
    (hdec : s.receivingEk = none) :
    States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.ct1Sampled s) } =
      .error (.err .stateDecode) := by
  unfold States.from_pb Chunked.SendCt.Ct1Sampled.from_pb
  simp only [hdec, huc, huc_ok, henc, encoderFromPbStateDecode_some, henc_ok,
    decoderFromPbStateDecode_none, Bind.bind, Except.bind, Functor.map, Except.map]

theorem v7_from_pb_ct1Sampled_dec_err (F : ShaCompress)
    (s : V1State.Chunked.Ct1Sampled) (u : V1State.Unchunked.Ct1Sent)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (encPb : PolynomialEncoder) (enc : PolyEncoder)
    (decPb : PolynomialDecoder) (e : PolynomialError)
    (hpts : (decPb.ptsNeeded == 576#32) = true)
    (huc : s.uc = some u)
    (huc_ok : Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApi F) u = .ok uc)
    (henc : s.sendingCt1 = some encPb)
    (henc_ok : fromPbResult (pbToProtoPolyEncoder encPb) = .ok enc)
    (hdec : s.receivingEk = some decPb)
    (hdec_err : decoderFromPbResult (pbToProtoPolyDecoder decPb) = .error e) :
    States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.ct1Sampled s) } =
      .error (.err .stateDecode) := by
  unfold States.from_pb Chunked.SendCt.Ct1Sampled.from_pb
  simp only [hdec, v7_receivingEk_pts_false hpts, Bool.false_eq_true, ↓reduceIte,
    huc, huc_ok, henc, encoderFromPbStateDecode_some, henc_ok,
    decoderFromPbStateDecode_some, hdec_err,
    Bind.bind, Except.bind, Functor.map, Except.map]

theorem v7_from_pb_ct1Sampled_ok (F : ShaCompress)
    (s : V1State.Chunked.Ct1Sampled) (u : V1State.Unchunked.Ct1Sent)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (encPb : PolynomialEncoder) (enc : PolyEncoder)
    (decPb : PolynomialDecoder) (dec : PolyDecoder)
    (hpts : (decPb.ptsNeeded == 576#32) = true)
    (huc : s.uc = some u)
    (huc_ok : Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApi F) u = .ok uc)
    (henc : s.sendingCt1 = some encPb)
    (henc_ok : fromPbResult (pbToProtoPolyEncoder encPb) = .ok enc)
    (hdec : s.receivingEk = some decPb)
    (hdec_ok : decoderFromPbResult (pbToProtoPolyDecoder decPb) = .ok dec) :
    States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.ct1Sampled s) } =
      .ok (.ct1Sampled { uc := uc, sending_ct1 := enc, receiving_ek := dec }) := by
  unfold States.from_pb Chunked.SendCt.Ct1Sampled.from_pb
  simp only [hdec, v7_receivingEk_pts_false hpts, Bool.false_eq_true, ↓reduceIte,
    huc, huc_ok, henc, encoderFromPbStateDecode_some, henc_ok,
    decoderFromPbStateDecode_some, hdec_ok,
    Bind.bind, Except.bind, Functor.map, Except.map]

/-! ## 3. Entry `ptsNeeded` Check (`+1056 -> +3480` and `+1056 -> +4632`) -/

@[expose] def v7_optProtoPolyDecoderTailWithoutPts (A : RustAlloc) (d cap : BitVec 64)
    (pb : ProtoPolynomialDecoder) : SepProp :=
  ∃∗ ptr : BitVec 64,
    ⌜pb.pts.length ≤ cap.toNat ∧ cap.toNat * 24 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    ((d + 8#64) ↦₆₄ ptr) ∗
    ((d + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
    (if cap = 0 then emp
     else A.live ptr (cap.toNat * 24) 8 ∗
       arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr pb.pts ∗
       memRegion (ptr + BitVec.ofNat 64 (pb.pts.length * 24))
         ((cap.toNat - pb.pts.length) * 24)) ∗
    ((d + protoPolynomialDecoderPolysOff) ↦₃₂ pb.polys) ∗
    ((d + protoPolynomialDecoderIsCompleteOff) ↦₈ boolByte pb.isComplete) ∗
    memRegion (d + protoPolynomialDecoderPadOff) protoPolynomialDecoderPadSize

theorem v7_optProtoPolyDecoderTail_expose_pts (A : RustAlloc) (pbA cap : BitVec 64)
    (pb : ProtoPolynomialDecoder) :
    v7_optProtoPolyDecoderTail A (pbA + 184#64) cap (some pb) ⊢
      ((pbA + 208#64) ↦₃₂ pb.ptsNeeded) ∗
      v7_optProtoPolyDecoderTailWithoutPts A (pbA + 184#64) cap pb := by
  unfold v7_optProtoPolyDecoderTail v7_optProtoPolyDecoderTailWithoutPts
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right ptr ?_
  have h208 : (pbA + 184#64) + protoPolynomialDecoderPtsNeededOff = pbA + 208#64 := by
    dsimp only [protoPolynomialDecoderPtsNeededOff]; bv_omega
  rw [h208]
  exact Entails.of_eq (by ac_rfl)

theorem v7_optProtoPolyDecoderTail_unexpose_pts (A : RustAlloc) (pbA cap : BitVec 64)
    (pb : ProtoPolynomialDecoder) :
    ((pbA + 208#64) ↦₃₂ pb.ptsNeeded) ∗
      v7_optProtoPolyDecoderTailWithoutPts A (pbA + 184#64) cap pb ⊢
      v7_optProtoPolyDecoderTail A (pbA + 184#64) cap (some pb) := by
  unfold v7_optProtoPolyDecoderTail v7_optProtoPolyDecoderTailWithoutPts
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right ptr ?_
  have h208 : (pbA + 184#64) + protoPolynomialDecoderPtsNeededOff = pbA + 208#64 := by
    dsimp only [protoPolynomialDecoderPtsNeededOff]; bv_omega
  rw [h208]
  exact Entails.of_eq (by ac_rfl)

@[local simp, local arm64_norm]
theorem v7_ptsNeeded_sub_576_beq_zero {pts : BitVec 32} (h : (pts == 576#32) = false) :
    (pts - 576#32 == 0#32) = false := by
  cases h2 : pts - 576#32 == 0#32
  · rfl
  · exfalso
    have heq : pts = 576#32 := by
      have h0 := beq_iff_eq.mp h2
      bv_omega
    subst heq
    exact Bool.noConfusion h

end CryptoVerification.SpqrV1.States.FromPb
