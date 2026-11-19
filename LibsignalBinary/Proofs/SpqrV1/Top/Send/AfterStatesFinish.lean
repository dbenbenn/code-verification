/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesFinish1 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop2
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesFinish2
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp

/-!
# `spqr::send`: Looping `InnerState` Drop Branches & Finish Composition

Symbolic execution of the `PolynomialDecoder` share-vector drop loops, the six looping
`V1State.InnerState` drop variants, and top-level finish composition (`step_send_finish_320a4`)
in `spqr::send::<HookRng>`.
-/

public section

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession CryptoVerification
open CryptoVerification.CodeLayout CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.Drop CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.ProtoRepr CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
open CryptoVerification.SpqrV1.Prost.EncodeToVec

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr v1StatePBPinnedAt optProtoPolynomialEncoderAt optProtoUnchunkedCt1SentAt
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero ofNat_add_one_sub_one

@[local simp, local arm64_norm]
private theorem send3_noneCap2_add_two_beq_zero : (0xfffffffffffffffe#64 + 2#64 == 0#64) = true := rfl
@[local simp, local arm64_norm]
private theorem send3_noneCap2_add_two_bne_zero : (0xfffffffffffffffe#64 + 2#64 != 0#64) = false := rfl

attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero Drop.noneCap_add_two_beq_zero
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero

theorem poly_pts_loop_post_entails (A : RustAlloc) (g : VecPin) (n : Nat) (sp : BitVec 64)
    (F : SepProp) (hle : n ≤ g.cap.toNat) (hcap_lt : g.cap.toNat * 24 < 2 ^ 63) :
    memRegion g.ptr (n * 24) ∗ A.pool ∗ stackAt sp allocHookStack ∗
      (A.live g.ptr (g.cap.toNat * 24) 8 ∗ memRegion (g.ptr + BitVec.ofNat 64 (n * 24)) ((g.cap.toNat - n) * 24) ∗
       memRegion (sp - 123008#64) (spqrSendCalleeStack - allocHookStack) ∗ F) ⊢
    (A.live g.ptr (g.cap.toNat * 24) 8 ∗ memRegion g.ptr (g.cap.toNat * 24)) ∗ A.pool ∗ stackAt sp spqrSendCalleeStack ∗ F := by
  have hsplit : g.cap.toNat * 24 = n * 24 + (g.cap.toNat - n) * 24 := by rw [← Nat.add_mul]; congr 1; omega
  have hbound : n * 24 + (g.cap.toNat - n) * 24 ≤ 2 ^ 64 := by rw [← hsplit]; omega
  have hmr : memRegion g.ptr (n * 24) ∗ memRegion (g.ptr + BitVec.ofNat 64 (n * 24)) ((g.cap.toNat - n) * 24) =
      memRegion g.ptr (g.cap.toNat * 24) := by rw [hsplit, ProofLib.memRegion_split g.ptr (n * 24) ((g.cap.toNat - n) * 24) hbound]
  rw [send_stackAt_callee_eq_allocHook sp, ← hmr]; exact Entails.of_eq (by simp only [sepConj_assoc, sepConj_comm, sepConj_left_comm])

theorem cons_len_rejoin_loop {A : RustAlloc} {sp : BitVec 64} {Frame : SepProp}
    (bs : List (BitVec 8)) (tl : List (List (BitVec 8))) (cur : BitVec 64) (hlen : (bs :: tl).length * 24 < 2 ^ 63) :
    memRegion (cur + 24#64) (tl.length * 24) ∗ A.pool ∗ stackAt sp allocHookStack ∗ (memRegion cur 24 ∗ Frame) ⊢
      memRegion cur ((bs :: tl).length * 24) ∗ A.pool ∗ stackAt sp allocHookStack ∗ Frame := by
  have hsplit := cons_len_mul bs tl 24
  have hbound : 24 + tl.length * 24 ≤ 2 ^ 64 := by rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
  rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 24 (tl.length * 24) hbound]; exact Entails.refl _

theorem cap_add_three_ult_two_false {cap : BitVec 64} (hlt : cap.toNat < 2 ^ 63) :
    (cap + 3#64).ult 2#64 = false := by
  simp only [BitVec.ult, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, decide_eq_false_iff_not]; omega

@[expose] def optProtoUnchunkedCt1SentTaggedRest (A : RustAlloc) (d w : BitVec 64)
    (optUc : Option V1State.Unchunked.Ct1Sent) : SepProp :=
  ∃∗ P : SepProp, ⌜(d ↦₆₄ w) ∗ P ⊢ optProtoUnchunkedCt1SentAt A d optUc⌝ ∗ P

theorem optProtoUnchunkedCt1SentAt_expose_tag (A : RustAlloc) (d : BitVec 64)
    (optUc : Option V1State.Unchunked.Ct1Sent) :
    optProtoUnchunkedCt1SentAt A d optUc ⊢
      ∃∗ w : BitVec 64,
        ⌜(w + 3#64).ult 2#64 = false ∧ ConditionHolds .CC (subsPState64 (w ^^^ 0x8000000000000000#64) 11#64) = false⌝ ∗
        (d ↦₆₄ w) ∗ optProtoUnchunkedCt1SentTaggedRest A d w optUc := by
  cases optUc with
  | none =>
    rw [optProtoUnchunkedCt1SentAt_none]
    refine Entails.sepExists_right 0xffffffffffffffff#64 (Entails.pure_right ⟨rfl, by simp [ConditionHolds, subsPState64, AddWithCarry64]; rfl⟩ (sepConj_mono_right ?_))
    unfold optProtoUnchunkedCt1SentTaggedRest
    exact Entails.sepExists_right (memRegion (d + 8#64) 120)
      (Entails.pure_right (Entails.of_eq (optProtoUnchunkedCt1SentAt_none A d).symm) (Entails.refl _))
  | some u =>
    rw [optProtoUnchunkedCt1SentAt_some, protoUnchunkedCt1SentAt_eq_ct1SentEkReceived]
    refine Entails.trans (protoUnchunkedCt1SentEkReceivedAt_expose_cap A d (ct1SentToCt1SentEkReceived u)) ?_
    apply Entails.sepExists_elim; intro cap; apply Entails.sepExists_elim; intro ptr; apply Entails.pure_left; intro hcap_lt
    refine Entails.sepExists_right cap (Entails.pure_right ⟨cap_add_three_ult_two_false hcap_lt, cap_xor_highBit_cc_11_false hcap_lt⟩ (sepConj_mono_right ?_))
    let P := protoUnchunkedCt1SentEkReceivedRestAt A d cap ptr (ct1SentToCt1SentEkReceived u)
    have hun : (d ↦₆₄ cap) ∗ P ⊢ optProtoUnchunkedCt1SentAt A d (some u) := by
      rw [optProtoUnchunkedCt1SentAt_some, protoUnchunkedCt1SentAt_eq_ct1SentEkReceived]
      exact protoUnchunkedCt1SentEkReceivedAt_unexpose_cap A d cap ptr (ct1SentToCt1SentEkReceived u)
    unfold optProtoUnchunkedCt1SentTaggedRest
    exact Entails.sepExists_right P (Entails.pure_right hun (Entails.refl P))

theorem optProtoUnchunkedCt1SentAt_unexpose_tag (A : RustAlloc) (d w : BitVec 64)
    (optUc : Option V1State.Unchunked.Ct1Sent) :
    (d ↦₆₄ w) ∗ optProtoUnchunkedCt1SentTaggedRest A d w optUc ⊢ optProtoUnchunkedCt1SentAt A d optUc := by
  unfold optProtoUnchunkedCt1SentTaggedRest; rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro P; rw [sepConj_left_comm]; apply Entails.pure_left; exact id

end CryptoVerification.SpqrV1.Top.Send
