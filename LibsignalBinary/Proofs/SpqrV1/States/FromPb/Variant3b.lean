/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Epilogue
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10a
import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBase
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 3 (`Ct1Received`, `+692`) — Error Cleanup

**Checked by Lean.**

Model reduction lemmas and shared error-cleanup paths (`+4968`, `+4176`, `+4924`, `+4908`,
`+4884`, `+1024`) for `InnerState.ct1Received`.
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
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append



/-! ## Pure Model Reduction Lemmas for `InnerState.ct1Received` -/

theorem v3cr_states_from_pb_ct1Received_uc_none_eq {F : ShaCompress}
    (sendingEk : Option PolynomialEncoder) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.ct1Received { uc := none, sendingEk := sendingEk }) } =
    .error (.err .stateDecode) := rfl

theorem v3cr_states_from_pb_ct1Received_uc_err_eq {F : ShaCompress}
    (u : V1State.Unchunked.EkSentCt1Received)
    (sendingEk : Option PolynomialEncoder)
    (huc : Unchunked.SendEk.EkSentCt1Received.from_pb (spqrAuthApi F) u = .error (.err .stateDecode)) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.ct1Received { uc := some u, sendingEk := sendingEk }) } =
    .error (.err .stateDecode) := by
  simp only [States.from_pb, Chunked.SendEk.Ct1Received.from_pb, huc,
    Bind.bind, Except.bind, Functor.map, Except.map]

theorem v3cr_states_from_pb_ct1Received_sendingEk_none_eq {F : ShaCompress}
    (u : V1State.Unchunked.EkSentCt1Received)
    (uc : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F))
    (huc : Unchunked.SendEk.EkSentCt1Received.from_pb (spqrAuthApi F) u = .ok uc) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.ct1Received { uc := some u, sendingEk := none }) } =
    .error (.err .stateDecode) := by
  simp only [States.from_pb, Chunked.SendEk.Ct1Received.from_pb, huc,
    encoderFromPbStateDecode, Bind.bind, Except.bind, Functor.map, Except.map]

theorem v3cr_states_from_pb_ct1Received_sendingEk_err_eq {F : ShaCompress}
    (u : V1State.Unchunked.EkSentCt1Received)
    (uc : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F))
    (pbEnc : PolynomialEncoder)
    (huc : Unchunked.SendEk.EkSentCt1Received.from_pb (spqrAuthApi F) u = .ok uc)
    (henc : fromPbResult (pbToProtoPolyEncoder pbEnc) = .error .serializationInvalid) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.ct1Received { uc := some u, sendingEk := some pbEnc }) } =
    .error (.err .stateDecode) := by
  have henc' := fromPb_eq_ok (pbToProtoPolyEncoder pbEnc)
  rw [henc] at henc'
  simp only [States.from_pb, Chunked.SendEk.Ct1Received.from_pb, huc,
    encoderFromPbStateDecode, spqrPolyApi, henc', StatesResult.ofPanic, Except.mapError,
    Bind.bind, Except.bind, Functor.map, Except.map]

theorem v3cr_states_from_pb_ct1Received_ok_eq {F : ShaCompress}
    (u : V1State.Unchunked.EkSentCt1Received)
    (uc : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F))
    (pbEnc : PolynomialEncoder)
    (enc : PolyEncoder)
    (huc : Unchunked.SendEk.EkSentCt1Received.from_pb (spqrAuthApi F) u = .ok uc)
    (henc : fromPbResult (pbToProtoPolyEncoder pbEnc) = .ok enc) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.ct1Received { uc := some u, sendingEk := some pbEnc }) } =
    .ok (.ct1Received { uc := uc, sending_ek := enc }) := by
  have henc' := fromPb_eq_ok (pbToProtoPolyEncoder pbEnc)
  rw [henc] at henc'
  simp only [States.from_pb, Chunked.SendEk.Ct1Received.from_pb, huc,
    encoderFromPbStateDecode, spqrPolyApi, henc', StatesResult.ofPanic, Except.mapError,
    Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map]

/-! ## Subroutine Call Relocation and Unaligned 24-Byte Copy Helpers -/

theorem v3cr_pair64_eq_byte_unshift (q w1 w2 : BitVec 64) :
    ((q ↦₆₄ w1) ∗ ((q + 8#64) ↦₈ loByte w2)) =
      ((q ↦₈ loByte w1) ∗ ((q + 1#64) ↦₆₄ unshiftWord w1 (loByte w2))) := by
  rw [pointsTo64_eq_pointsToBytes q w1, pointsTo64_eq_pointsToBytes (q + 1#64),
      ← ProofLib.pointsToBytes_cons, loByte_cons_unpack64_unshiftWord w1 (loByte w2),
      ProofLib.pointsToBytes_append q (unpack64 w1) [loByte w2], unpack64_length]
  simp only [ProofLib.pointsToBytes_cons, ProofLib.pointsToBytes_nil, sepConj_emp]

theorem v3cr_triple64_eq_byte_128_tail7 (a w1 w2 w3 : BitVec 64) :
    ((a ↦₆₄ w1) ∗ ((a + 8#64) ↦₆₄ w2) ∗ ((a + 16#64) ↦₆₄ w3)) =
      ((a ↦₈ loByte w1) ∗
       ((a + 1#64) ↦₁₂₈ (unshiftWord w2 (loByte w3) ++ unshiftWord w1 (loByte w2))) ∗
       ((a + 17#64) ↦ₛ hiBytes7 w3)) := by
  have hp := pair64_to_byte_word_tail7 (a + 8#64) w2 w3
  have ha16 : (a + 8#64) + 8#64 = a + 16#64 := by bv_omega
  have ha9 : (a + 8#64) + 1#64 = a + 9#64 := by bv_omega
  have ha17 : (a + 8#64) + 9#64 = a + 17#64 := by bv_omega
  rw [ha16, ha9, ha17] at hp
  rw [hp, ← sepConj_assoc, ← sepConj_assoc, v3cr_pair64_eq_byte_unshift a w1 w2]
  have h128 := pointsTo64_pair_eq_pointsTo128 (a + 1#64)
    (unshiftWord w1 (loByte w2)) (unshiftWord w2 (loByte w3))
  have ha9' : (a + 1#64) + 8#64 = a + 9#64 := by bv_omega
  rw [ha9'] at h128
  rw [sepConj_assoc (a ↦₈ loByte w1), h128, sepConj_assoc]

/-! ## Shared Error Cleanup Paths (`+4968`, `+4176`, `+4924`, `+4908`, `+4884`, `+1024`) -/

theorem v3cr_fsp_1496_none_entails_2304 (fsp : BitVec 64) :
    memRegion fsp 1496 ∗ ((fsp + 1496#64) ↦₆₄ noneCap) ∗
      memRegion (fsp + 1504#64) 48 ∗ memRegion (fsp + 1552#64) 752 ⊢
      memRegion fsp 2304 := by
  exact collapse_top <| collapse_step0 (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Entails.refl _) <| Entails.refl _

theorem v3cr_fsp_1496_56_entails_2304 (fsp : BitVec 64) :
    memRegion fsp 1496 ∗ memRegion (fsp + 1496#64) 56 ∗ memRegion (fsp + 1552#64) 752 ⊢
      memRegion fsp 2304 := by
  exact collapse_top <| collapse_step0 (Entails.refl _) <|
    collapse_step (Entails.refl _) <| Entails.refl _

private theorem v3cr_vecCapPtrDealloc_zero (A : RustAlloc) {ca pa : BitVec 64}
    (h : (ca == 0#64) = true) :
    vecCapPtrDealloc A ca pa = emp := by
  simp only [vecCapPtrDealloc, h, ↓reduceIte]

private theorem v3cr_vecCapPtrDealloc_ne_zero (A : RustAlloc) {ca pa : BitVec 64}
    (h : ¬(ca == 0#64) = true) :
    vecCapPtrDealloc A ca pa = (A.live pa ca.toNat 1 ∗ memRegion pa ca.toNat) := by
  have hbeq : (ca == 0#64) = false := Bool.eq_false_iff.mpr h
  simp only [vecCapPtrDealloc, hbeq, Bool.false_eq_true, ↓reduceIte]

end CryptoVerification.SpqrV1.States.FromPb
