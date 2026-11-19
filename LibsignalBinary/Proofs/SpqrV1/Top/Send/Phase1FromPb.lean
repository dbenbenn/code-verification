/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.Defs
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1Steps
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `spqr::send::<HookRng>` Phase 1b: Inner-State Unpack (`+156..+224`)

**Checked by Lean.**

Verifies `spqr_send_inner_none_step` (`+156 -> s0.lr` when `pq.inner = none`, returning
`Ok(Send { state: [], msg: [], key: None })`) and `spqr_send_inner_some_to_224`
(`+156 -> +224` when `pq.inner = some (.v1 v1)`).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.CodeLayout

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit BitVec.toNat_zero bv_add_add_lit1 bv_add_add_lit2

/-! ## `pq.inner = none` Return Path (`+156 -> s0.lr`) -/

/-- Reassemble `(a30 ↦₆₄ w0) ∗ ((a30 + 8#64) ↦₆₄ w1) ∗ DecodeState.optVersionNegotiationPBTailAt A w0 w1 (a30 + 16#64) vn`
    after writing `w0, w1, w2, w3` to `[a30 .. a30 + 32)`. -/
theorem reassemble_optVersionNegotiationPBTail_raw (A : RustAlloc) (a30 : BitVec 64)
    (w0 w1 w2 w3 : BitVec 64) (bs16 : List (BitVec 8))
    (vn : Option VersionNegotiationPB)
    (hlen16 : bs16.length = 16) :
    (a30 ↦₆₄ w0) ∗
      ((a30 + 8#64) ↦₆₄ w1) ∗
      ((a30 + 16#64) ↦₆₄ w2) ∗
      ((a30 + 24#64) ↦₆₄ w3) ∗
      ((a30 + 32#64) ↦ₛ bs16) ∗
      (relocOptVersionNegotiationPBTailAt A w0 w1 vn).1
        ((unpack64 w2 ++ unpack64 w3) ++ bs16) ⊢
      (a30 ↦₆₄ w0) ∗
      ((a30 + 8#64) ↦₆₄ w1) ∗
      DecodeState.optVersionNegotiationPBTailAt A w0 w1 (a30 + 16#64) vn :=
  sepConj_mono_right (reassemble_optVersionNegotiationPBTail A a30 w0 w1 w2 w3 bs16 vn hlen16)

theorem memRegion_sendResult_split_56 (ret : BitVec 64) :
    memRegion ret 72 ⊢
      ∃∗ r0 : BitVec 64, ∃∗ r8 : BitVec 64, ∃∗ r16 : BitVec 64, ∃∗ r24 : BitVec 64,
      ∃∗ r32 : BitVec 64, ∃∗ r40 : BitVec 64, ∃∗ r48 : BitVec 64,
        (ret ↦₆₄ r0) ∗
        ((ret + 8#64) ↦₆₄ r8) ∗
        ((ret + 16#64) ↦₆₄ r16) ∗
        ((ret + 24#64) ↦₆₄ r24) ∗
        ((ret + 32#64) ↦₆₄ r32) ∗
        ((ret + 40#64) ↦₆₄ r40) ∗
        ((ret + 48#64) ↦₆₄ r48) ∗
        memRegion (ret + 56#64) 16 := by
  rw [ProofLib.memRegion_split' (b := ret) (n := 8) (k := 64)
        (b' := ret + 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 8#64) (n := 8) (k := 56)
        (b' := ret + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 16#64) (n := 8) (k := 48)
        (b' := ret + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 24#64) (n := 8) (k := 40)
        (b' := ret + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 32#64) (n := 8) (k := 32)
        (b' := ret + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 40#64) (n := 8) (k := 24)
        (b' := ret + 48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 48#64) (n := 8) (k := 16)
        (b' := ret + 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight ret,
      ProofLib.memRegion_eight (ret + 8#64),
      ProofLib.memRegion_eight (ret + 16#64),
      ProofLib.memRegion_eight (ret + 24#64),
      ProofLib.memRegion_eight (ret + 32#64),
      ProofLib.memRegion_eight (ret + 40#64),
      ProofLib.memRegion_eight (ret + 48#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro r48
  apply Entails.sepExists_elim; intro r40
  apply Entails.sepExists_elim; intro r32
  apply Entails.sepExists_elim; intro r24
  apply Entails.sepExists_elim; intro r16
  apply Entails.sepExists_elim; intro r8
  apply Entails.sepExists_elim; intro r0
  refine Entails.sepExists_right r0
    (Entails.sepExists_right r8
      (Entails.sepExists_right r16
        (Entails.sepExists_right r24
          (Entails.sepExists_right r32
            (Entails.sepExists_right r40
              (Entails.sepExists_right r48 ?_))))))
  exact Entails.of_eq (by ac_rfl)

theorem empty_vecU8_entails (A : RustAlloc) (a : BitVec 64) :
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ⊢
      vecU8 A a [] := by
  unfold vecU8
  refine Entails.sepExists_right 0#64 (Entails.sepExists_right 1#64 ?_)
  unfold vecU8At vecHeader
  have hp : ([] : List (BitVec 8)).length ≤ (0#64 : BitVec 64).toNat ∧
      (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0 := by decide
  have h0 : (0#64 : BitVec 64) = 0 := rfl
  simp only [h0, ↓reduceIte, sepConj_emp]
  refine Entails.trans (Entails.pure_right hp (Entails.refl _)) ?_
  exact Entails.of_eq (by ac_rfl)

theorem empty_ok_sendResult_entails (A : RustAlloc) (ret : BitVec 64) :
    (ret ↦₆₄ 0#64) ∗
      ((ret + 8#64) ↦₆₄ 1#64) ∗
      ((ret + 16#64) ↦₆₄ 0#64) ∗
      ((ret + 24#64) ↦₆₄ 0#64) ∗
      ((ret + 32#64) ↦₆₄ 1#64) ∗
      ((ret + 40#64) ↦₆₄ 0#64) ∗
      ((ret + 48#64) ↦₆₄ LibsignalTripleRatchetRepr.noneCap) ∗
      memRegion (ret + 56#64) 16 ⊢
      spqrSendResultAt A ret (some ([], none, [])) := by
  unfold spqrSendResultAt spqrSendKeyAt
  dsimp only
  have hlen : ([] : List (BitVec 8)).length < 2 ^ 32 := by decide
  have hv1 := empty_vecU8_entails A ret
  have hv2 := empty_vecU8_entails A (ret + 24#64)
  have ha32 : (ret + 24#64) + 8#64 = ret + 32#64 := by bv_omega
  have ha40 : (ret + 24#64) + 16#64 = ret + 40#64 := by bv_omega
  rw [ha32, ha40] at hv2
  have ha56 : (ret + 48#64) + 8#64 = ret + 56#64 := by bv_omega
  rw [ha56]
  refine Entails.pure_right hlen ?_
  refine Entails.trans
    (Entails.of_eq (show _ =
      ((ret ↦₆₄ 0#64) ∗ ((ret + 8#64) ↦₆₄ 1#64) ∗ ((ret + 16#64) ↦₆₄ 0#64)) ∗
      (((ret + 24#64) ↦₆₄ 0#64) ∗ ((ret + 32#64) ↦₆₄ 1#64) ∗ ((ret + 40#64) ↦₆₄ 0#64)) ∗
      (((ret + 48#64) ↦₆₄ LibsignalTripleRatchetRepr.noneCap) ∗ memRegion (ret + 56#64) 16) by ac_rfl)) ?_
  exact sepConj_mono hv1 (sepConj_mono_left hv2)

theorem inner_none_b0_rejoin (fsp : BitVec 64) (w1 w2 w3 : BitVec 64) :
    ((fsp + 0xb0#64) ↦₆₄ DecodeState.none3Cap) ∗
      memRegion (fsp + 0xb8#64) 216 ∗
      ((fsp + 0x190#64) ↦₆₄ w1) ∗
      ((fsp + 0x198#64) ↦₆₄ w2) ∗
      ((fsp + 0x1a0#64) ↦₆₄ w3) ∗
      memRegion (fsp + 0x1a8#64) (0x1f20 - 0x1a8) ⊢
      memRegion (fsp + 0xb0#64) (0x1f20 - 0xb0) := by
  have hinner : ((fsp + 0xb0#64) ↦₆₄ DecodeState.none3Cap) ∗ memRegion (fsp + 0xb8#64) 216 ⊢
      memRegion (fsp + 0xb0#64) 224 := by
    rw [ProofLib.memRegion_split' (b := fsp + 0xb0#64) (n := 8) (k := 216)
          (b' := fsp + 0xb8#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (fsp + 0xb0#64) DecodeState.none3Cap)
  rw [ProofLib.memRegion_split' (b := fsp + 0xb0#64) (n := 224) (k := 0x1f20 - 0x190)
        (b' := fsp + 0x190#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x190#64) (n := 8) (k := 0x1f20 - 0x198)
        (b' := fsp + 0x198#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x198#64) (n := 8) (k := 0x1f20 - 0x1a0)
        (b' := fsp + 0x1a0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x1a0#64) (n := 8) (k := 0x1f20 - 0x1a8)
        (b' := fsp + 0x1a8#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans
    (Entails.of_eq (show _ =
      (((fsp + 0xb0#64) ↦₆₄ DecodeState.none3Cap) ∗ memRegion (fsp + 0xb8#64) 216) ∗
      ((fsp + 0x190#64) ↦₆₄ w1) ∗
      ((fsp + 0x198#64) ↦₆₄ w2) ∗
      ((fsp + 0x1a0#64) ↦₆₄ w3) ∗
      memRegion (fsp + 0x1a8#64) (0x1f20 - 0x1a8) by ac_rfl)) ?_
  exact sepConj_mono hinner
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion (fsp + 0x190#64) w1)
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion (fsp + 0x198#64) w2)
        (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (fsp + 0x1a0#64) w3))))

@[local simp, local arm64_norm, local wp_norm]
theorem none3Cap_add_three_beq_zero :
    (DecodeState.none3Cap + 3#64 == 0#64) = true ∧
    (DecodeState.none3Cap + 3#64 != 0#64) = false := by decide

theorem slt_one_false_iff {w0 : BitVec 64} (h : BitVec.slt w0 1#64 = false) :
    BitVec.sle 1#64 w0 = true := by
  revert h; bv_bits

theorem slt_one_true_iff {w0 : BitVec 64} (h : BitVec.slt w0 1#64 = true) :
    (!BitVec.slt w0 1#64) = false := by
  rw [h]; rfl

/-- Remainder of `Drop.optProtoInnerStateAt A a optSt` when its first 8-byte word `a ↦₆₄ w` is exposed. -/
@[expose] def optProtoInnerStateHeadRest (A : RustAlloc) (a w : BitVec 64)
    (optSt : Option V1State.InnerState) : SepProp :=
  ∃∗ P : SepProp, ⌜(a ↦₆₄ w) ∗ P ⊢ Drop.optProtoInnerStateAt A a optSt⌝ ∗ P

theorem optProtoInnerStateAt_unexpose_head (A : RustAlloc) (a w : BitVec 64)
    (optSt : Option V1State.InnerState) :
    (a ↦₆₄ w) ∗ optProtoInnerStateHeadRest A a w optSt ⊢
      Drop.optProtoInnerStateAt A a optSt := by
  unfold optProtoInnerStateHeadRest
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro P
  rw [sepConj_left_comm]
  apply Entails.pure_left; intro hun
  exact hun

private theorem expose_head_of_tag {A : RustAlloc} {a : BitVec 64}
    (tag : BitVec 64) {optSt : Option V1State.InnerState} (P : SepProp)
    (hne : tag ≠ DecodeState.none3Cap)
    (heq : Drop.optProtoInnerStateAt A a optSt = (a ↦₆₄ tag) ∗ P) :
    Drop.optProtoInnerStateAt A a optSt ⊢
      ∃∗ w : BitVec 64,
        ⌜w ≠ DecodeState.none3Cap⌝ ∗
        (a ↦₆₄ w) ∗
        optProtoInnerStateHeadRest A a w optSt := by
  rw [heq]
  refine Entails.sepExists_right tag (Entails.pure_right hne (sepConj_mono_right ?_))
  unfold optProtoInnerStateHeadRest
  exact Entails.sepExists_right P (Entails.pure_right (Entails.of_eq heq.symm) (Entails.refl P))

theorem vecU8_expose_head_ne_none3Cap (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A a bs ⊢
      ∃∗ w : BitVec 64, ∃∗ Q : SepProp,
        ⌜w ≠ DecodeState.none3Cap⌝ ∗ (a ↦₆₄ w) ∗ ⌜(a ↦₆₄ w) ∗ Q ⊢ vecU8 A a bs⌝ ∗ Q := by
  unfold vecU8
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  let H : SepProp :=
    if cap = 0 then emp
    else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)
  have heq : vecU8At A a cap ptr bs =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (a ↦₆₄ cap) ∗
      (((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ H) := by
    unfold vecU8At vecHeader H
    ac_rfl
  rw [heq]
  apply Entails.pure_left; rintro ⟨hlen, hcap_lt, hptr_ne⟩
  have hne : cap ≠ DecodeState.none3Cap := by
    intro h; rw [h] at hcap_lt
    change 0xfffffffffffffffd < 2 ^ 63 at hcap_lt
    omega
  let Q : SepProp :=
    ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ H
  have hun : (a ↦₆₄ cap) ∗ Q ⊢ vecU8 A a bs := by
    unfold vecU8
    refine Entails.trans ?_ (Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _)))
    rw [heq]
    unfold Q
    exact Entails.of_eq (by ac_rfl)
  refine Entails.sepExists_right cap (Entails.sepExists_right Q ?_)
  refine Entails.pure_right hne (sepConj_mono_right (Entails.pure_right hun ?_))
  unfold Q
  exact Entails.pure_right ⟨hlen, hcap_lt, hptr_ne⟩ (Entails.refl _)

theorem optProtoInnerStateAt_expose_head (A : RustAlloc) (a : BitVec 64)
    (optSt : Option V1State.InnerState) :
    Drop.optProtoInnerStateAt A a optSt ⊢
      ∃∗ w : BitVec 64,
        ⌜w ≠ DecodeState.none3Cap⌝ ∗
        (a ↦₆₄ w) ∗
        optProtoInnerStateHeadRest A a w optSt := by
  cases optSt with
  | none =>
    exact expose_head_of_tag Drop.none2Cap (memRegion (a + 8#64) 216) (by decide) rfl
  | some st =>
    cases st with
    | keysUnsampled s =>
      exact expose_head_of_tag 0x8000000000000000#64
        (Drop.protoChunkedKeysUnsampledAt A (a + 8#64) s ∗ memRegion (a + 64#64) 160)
        (by decide) rfl
    | keysSampled s =>
      exact expose_head_of_tag 0x8000000000000001#64
        (Drop.protoChunkedKeysSampledAt A (a + 8#64) s ∗ memRegion (a + 168#64) 56)
        (by decide) rfl
    | headerSent s =>
      exact expose_head_of_tag 0x8000000000000002#64
        (Drop.protoChunkedHeaderSentAt A (a + 8#64) s ∗ memRegion (a + 184#64) 40)
        (by decide) rfl
    | ct1Received s =>
      exact expose_head_of_tag 0x8000000000000003#64
        (Drop.protoChunkedCt1ReceivedAt A (a + 8#64) s ∗ memRegion (a + 168#64) 56)
        (by decide) rfl
    | ekSentCt1Received s =>
      exact expose_head_of_tag 0x8000000000000004#64
        (Drop.protoChunkedEkSentCt1ReceivedAt A (a + 8#64) s ∗ memRegion (a + 152#64) 72)
        (by decide) rfl
    | noHeaderReceived s =>
      exact expose_head_of_tag 0x8000000000000005#64
        (Drop.protoChunkedNoHeaderReceivedAt A (a + 8#64) s ∗ memRegion (a + 104#64) 120)
        (by decide) rfl
    | headerReceived s =>
      exact expose_head_of_tag 0x8000000000000006#64
        (Drop.protoChunkedHeaderReceivedAt A (a + 8#64) s ∗ memRegion (a + 128#64) 96)
        (by decide) rfl
    | ekReceivedCt1Sampled s =>
      exact expose_head_of_tag 0x8000000000000008#64
        (Drop.protoChunkedEkReceivedCt1SampledAt A (a + 8#64) s ∗ memRegion (a + 192#64) 32)
        (by decide) rfl
    | ct1Acknowledged s =>
      exact expose_head_of_tag 0x8000000000000009#64
        (Drop.protoChunkedCt1AcknowledgedAt A (a + 8#64) s ∗ memRegion (a + 176#64) 48)
        (by decide) rfl
    | ct2Sampled s =>
      exact expose_head_of_tag 0x800000000000000a#64
        (Drop.protoChunkedCt2SampledAt A (a + 8#64) s ∗ memRegion (a + 120#64) 104)
        (by decide) rfl
    | ct1Sampled s =>
      rcases hsuc : s.uc with _ | uc
      · exact expose_head_of_tag noneCap
          (memRegion (a + 8#64) 120 ∗
           Poly.optProtoPolynomialEncoderAt A (a + 128#64) (s.sendingCt1.map pbToProtoPolyEncoder) ∗
           Poly.optProtoPolynomialDecoderAt A (a + 184#64) (s.receivingEk.map pbToProtoPolyDecoder))
          (by decide) (by
            unfold Drop.optProtoInnerStateAt Drop.protoInnerStateAt
              Drop.protoChunkedCt1SampledAt Drop.optProtoUnchunkedCt1SentAt
            dsimp only; rw [hsuc]; dsimp only; ac_rfl)
      · let R : SepProp :=
          vecU8 A (a + 24#64) uc.es ∗
          vecU8 A (a + 48#64) uc.ct1 ∗
          optProtoAuthenticatorAt A (a + 72#64) uc.auth ∗
          ((a + 120#64) ↦₆₄ uc.epoch) ∗
          Poly.optProtoPolynomialEncoderAt A (a + 128#64) (s.sendingCt1.map pbToProtoPolyEncoder) ∗
          Poly.optProtoPolynomialDecoderAt A (a + 184#64) (s.receivingEk.map pbToProtoPolyDecoder)
        have heq : Drop.optProtoInnerStateAt A a (some (.ct1Sampled s)) =
            vecU8 A a uc.hdr ∗ R := by
          unfold Drop.optProtoInnerStateAt Drop.protoInnerStateAt
            Drop.protoChunkedCt1SampledAt Drop.optProtoUnchunkedCt1SentAt
            Drop.protoUnchunkedCt1SentAt R
          dsimp only; rw [hsuc]; dsimp only; ac_rfl
        rw [heq]
        refine Entails.trans (sepConj_mono_left (vecU8_expose_head_ne_none3Cap A a uc.hdr)) ?_
        simp only [sepExists_sepConj_left]
        apply Entails.sepExists_elim; intro w
        apply Entails.sepExists_elim; intro Q
        have hpull :
            ((⌜w ≠ DecodeState.none3Cap⌝ ∗ (a ↦₆₄ w) ∗ ⌜(a ↦₆₄ w) ∗ Q ⊢ vecU8 A a uc.hdr⌝ ∗ Q) ∗ R) =
            ⌜w ≠ DecodeState.none3Cap⌝ ∗ ⌜(a ↦₆₄ w) ∗ Q ⊢ vecU8 A a uc.hdr⌝ ∗
              ((a ↦₆₄ w) ∗ (Q ∗ R)) := by ac_rfl
        rw [hpull]
        apply Entails.pure_left; intro hne
        apply Entails.pure_left; intro hunQ
        refine Entails.sepExists_right w (Entails.pure_right hne (sepConj_mono_right ?_))
        unfold optProtoInnerStateHeadRest
        refine Entails.sepExists_right (Q ∗ R) (Entails.pure_right ?_ (Entails.refl _))
        rw [heq, ← sepConj_assoc]
        exact sepConj_mono_left hunQ

theorem rejoin_190_to_1f20 (fsp w1 w2 w3 : BitVec 64) :
    ((fsp + 0x190#64) ↦₆₄ w1) ∗
      ((fsp + 0x198#64) ↦₆₄ w2) ∗
      ((fsp + 0x1a0#64) ↦₆₄ w3) ∗
      memRegion (fsp + 0x1a8#64) (0x1f20 - 0x1a8) ⊢
      memRegion (fsp + 0x190#64) (0x1f20 - 0x190) := by
  rw [ProofLib.memRegion_split' (b := fsp + 0x190#64) (n := 8) (k := 0x1f20 - 0x198)
        (b' := fsp + 0x198#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x198#64) (n := 8) (k := 0x1f20 - 0x1a0)
        (b' := fsp + 0x1a0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x1a0#64) (n := 8) (k := 0x1f20 - 0x1a8)
        (b' := fsp + 0x1a8#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion (fsp + 0x190#64) w1)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion (fsp + 0x198#64) w2)
      (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (fsp + 0x1a0#64) w3)))

theorem ne_none3Cap_add_three_bne_zero_true {w : BitVec 64} (h : w ≠ DecodeState.none3Cap) :
    (w + 3#64 != 0#64) = true := by
  have h1 := ne_none3Cap_add_three_beq_zero_false h
  simpa [bne] using h1

end CryptoVerification.SpqrV1.Top.Send
