/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10a -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBase
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

public section

set_option autoImplicit false

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 10 (`Ct2Sampled`, `+1632`) — Early Errors & `Authenticator` Cloning

Proves the `+1632` early error exits (`s.uc = none` and `auth = none`), original `Authenticator`
buffer deallocation (`+5688 -> +5728`), and `rootKey` (`+1720 -> +5540`) / `macKey` (`+5540 -> +5688`)
cloning steps.
-/

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout
open CryptoVerification.Swarm.IC10.Variant10a

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

theorem v10_protoChunkedCt2SampledAt_uc_none (A : RustAlloc) (pbA : BitVec 64)
    (sendingCt2 : Option PolynomialEncoderPB) :
    protoChunkedCt2SampledAt A (pbA + 8#64) { sendingCt2 := sendingCt2, uc := none } =
      optProtoPolynomialEncoderAt A (pbA + 8#64) (sendingCt2.map pbToProtoPolyEncoder) ∗
      ((pbA + 64#64) ↦₆₄ none2Cap) ∗
      memRegion (pbA + 72#64) 48 := by
  dsimp only [protoChunkedCt2SampledAt, optProtoUnchunkedCt2SentAt]
  have h64 : (pbA + 8#64) + 56#64 = pbA + 64#64 := by bv_omega
  have h72 : (pbA + 64#64) + 8#64 = pbA + 72#64 := by bv_omega
  rw [h64, h72]

theorem v10_protoChunkedCt2SampledAt_auth_none (A : RustAlloc) (pbA epoch : BitVec 64)
    (sendingCt2 : Option PolynomialEncoderPB) :
    protoChunkedCt2SampledAt A (pbA + 8#64)
        { sendingCt2 := sendingCt2, uc := some { auth := none, epoch := epoch } } =
      optProtoPolynomialEncoderAt A (pbA + 8#64) (sendingCt2.map pbToProtoPolyEncoder) ∗
      ((pbA + 64#64) ↦₆₄ noneCap) ∗
      memRegion (pbA + 72#64) 40 ∗
      ((pbA + 112#64) ↦₆₄ epoch) := by
  dsimp only [protoChunkedCt2SampledAt, optProtoUnchunkedCt2SentAt, protoUnchunkedCt2SentAt,
    optProtoAuthenticatorAt]
  have h64 : (pbA + 8#64) + 56#64 = pbA + 64#64 := by bv_omega
  have h72 : (pbA + 64#64) + 8#64 = pbA + 72#64 := by bv_omega
  have h112 : (pbA + 64#64) + 48#64 = pbA + 112#64 := by bv_omega
  rw [h64, h72, h112]
  ac_rfl

@[simp]
theorem v10_states_from_pb_ct2Sampled_uc_none (F : ShaCompress)
    (sendingCt2 : Option PolynomialEncoderPB) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.ct2Sampled { sendingCt2 := sendingCt2, uc := none }) } =
      .error (.err .stateDecode) := rfl

@[simp]
theorem v10_states_from_pb_ct2Sampled_auth_none (F : ShaCompress) (epoch : BitVec 64)
    (sendingCt2 : Option PolynomialEncoderPB) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.ct2Sampled
          { sendingCt2 := sendingCt2, uc := some { auth := none, epoch := epoch } }) } =
      .error (.err .stateDecode) := rfl

theorem v10_fsp_unsplit_0 (fsp : BitVec 64) :
    (fsp ↦₆₄ 0#64) ∗ memRegion (fsp + 8#64) 2296 ⊢
      memRegion fsp 2304 := by
  rw [ProofLib.memRegion_split fsp 8 2296 (by decide)]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion fsp 0#64)

theorem v10_vecU8Payload_entails_vecCapPtrDealloc (A : RustAlloc) (c p : BitVec 64)
    (bs : List (BitVec 8)) :
    vecU8Payload A c p bs ⊢ vecCapPtrDealloc A c p := by
  unfold vecU8Payload vecCapPtrDealloc
  apply Entails.pure_left; intro ⟨hle, _, _⟩
  by_cases hc : c = 0#64
  · subst hc; simp only [beq_self_eq_true, ↓reduceIte]; exact Entails.refl _
  · have hcf : (c == 0#64) = false := beq_false_of_ne hc
    simp only [hc, hcf, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    apply sepConj_mono_right
    have h1 := ProofLib.pointsToBytes_entails_memRegion p bs
    have hadd : bs.length + (c.toNat - bs.length) = c.toNat := Nat.add_sub_of_le hle
    have h2 : memRegion p bs.length ∗ memRegion (p + BitVec.ofNat 64 bs.length) (c.toNat - bs.length) =
        memRegion p c.toNat := by
      rw [← ProofLib.memRegion_split' (b := p) (n := bs.length) (k := c.toNat - bs.length)
        (b' := p + BitVec.ofNat 64 bs.length) hadd.symm rfl (by omega)]
    rw [← h2]
    exact sepConj_mono_left h1

theorem v10_pointsTo64_split_1_4_2_1 (a w : BitVec 64) :
    (a ↦₆₄ w) =
      (a ↦₈ w.extractLsb' 0 8) ∗
      ((a + 1#64) ↦₃₂ w.extractLsb' 8 32) ∗
      ((a + 5#64) ↦₁₆ w.extractLsb' 40 16) ∗
      ((a + 7#64) ↦₈ w.extractLsb' 56 8) := by
  have hb1 : (w.extractLsb' 8 32).extractLsb' 0 8 = w.extractLsb' 8 8 := by bv_kernel
  have hb2 : (w.extractLsb' 8 32).extractLsb' 8 8 = w.extractLsb' 16 8 := by bv_kernel
  have hb3 : (w.extractLsb' 8 32).extractLsb' 16 8 = w.extractLsb' 24 8 := by bv_kernel
  have hb4 : (w.extractLsb' 8 32).extractLsb' 24 8 = w.extractLsb' 32 8 := by bv_kernel
  have hb5 : (w.extractLsb' 40 16).extractLsb' 0 8 = w.extractLsb' 40 8 := by bv_kernel
  have hb6 : (w.extractLsb' 40 16).extractLsb' 8 8 = w.extractLsb' 48 8 := by bv_kernel
  rw [ProofLib.pointsTo64_eq_pointsToBytes a w,
      ProofLib.pointsTo32_eq_pointsToBytes (a + 1#64) (w.extractLsb' 8 32),
      ProofLib.pointsTo16_eq_pointsToBytes (a + 5#64) (w.extractLsb' 40 16)]
  simp only [unpack64, unpack32, unpack16,
    ProofLib.pointsToBytes_cons, ProofLib.pointsToBytes_nil,
    hb1, hb2, hb3, hb4, hb5, hb6,
    sepConj_emp, sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]

theorem v10_live_bytes_entails_vecCapPtrDealloc (A : RustAlloc) (c p : BitVec 64)
    (bs : List (BitVec 8)) (hc : c ≠ 0#64) (hle : bs.length ≤ c.toNat) :
    A.live p c.toNat 1 ∗ (p ↦ₛ bs) ∗
      memRegion (p + BitVec.ofNat 64 bs.length) (c.toNat - bs.length) ⊢
      vecCapPtrDealloc A c p := by
  unfold vecCapPtrDealloc
  have hcf : (c == 0#64) = false := beq_false_of_ne hc
  simp only [hcf, Bool.false_eq_true, ↓reduceIte]
  apply sepConj_mono_right
  have h1 := ProofLib.pointsToBytes_entails_memRegion p bs
  have hadd : bs.length + (c.toNat - bs.length) = c.toNat := Nat.add_sub_of_le hle
  have h2 : memRegion p bs.length ∗ memRegion (p + BitVec.ofNat 64 bs.length) (c.toNat - bs.length) =
      memRegion p c.toNat := by
    rw [← ProofLib.memRegion_split' (b := p) (n := bs.length) (k := c.toNat - bs.length)
      (b' := p + BitVec.ofNat 64 bs.length) hadd.symm rfl (by omega)]
  rw [← h2]
  exact sepConj_mono_left h1

theorem v10_ite_nil_entails_vecCapPtrDealloc (A : RustAlloc) (c p : BitVec 64) :
    (if c = 0#64 then emp
     else A.live p c.toNat 1 ∗ (p ↦ₛ ([] : List (BitVec 8))) ∗
       memRegion (p + 0#64) (c.toNat - 0)) ⊢
      vecCapPtrDealloc A c p := by
  unfold vecCapPtrDealloc
  by_cases hc : c = 0#64
  · subst hc; simp only [beq_self_eq_true, ↓reduceIte]; exact Entails.refl _
  · have hcf : (c == 0#64) = false := beq_false_of_ne hc
    simp only [hc, hcf, Bool.false_eq_true, ↓reduceIte,
      ProofLib.pointsToBytes_nil, emp_sepConj, BitVec.add_zero, Nat.sub_zero]
    exact Entails.refl _

theorem v10_sepWP_exists_post {α : Type} {prog : Program} {target : BitVec 64} {s : State}
    {P : SepProp} {Q : α → State → SepProp → Prop} (a : α)
    (h : SepWP prog target s P (Q a)) :
    SepWP prog target s P (fun sm Pm => ∃ x : α, Q x sm Pm) :=
  SepWP.mono h fun _ _ _ _ hq => ⟨a, hq⟩

end CryptoVerification.SpqrV1.States.FromPb

