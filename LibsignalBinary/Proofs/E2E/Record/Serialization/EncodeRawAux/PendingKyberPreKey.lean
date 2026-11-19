/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.Base
import Mathlib.Tactic.ToAdditive
import Mathlib.Tactic.ToDual
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.PendingPreKeyFields
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.RemoteIdentityRootKeyCounter
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.SenderReceiverChains
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.E2E.Record.Support.Repr

/-!
# `SessionStructure::encode_raw` tag 14 (`pending_kyber_pre_key`, `+0x50c..+0x648`)
-/

public section

namespace CryptoVerification.E2E.Record.Serialization.EncodeRawAux

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.E2E.Record

theorem uint32Field1_zero_eq_er : uint32Field 1 0#32 = [] := rfl

theorem uint32Field1_nonzero_eq_er {v : BitVec 32} (h : v ≠ 0#32) :
    [0x08#8] ++ encodeVarint (BitVec.zeroExtend 64 v) = uint32Field 1 v := by
  rw [uint32Field_ne_zero (k := 0x08#8) h]

theorem uint32Field1_nonzero_length_bv_er {v : BitVec 32} (h : v ≠ 0#32) :
    BitVec.ofNat 64 (encodeVarint (BitVec.zeroExtend 64 v)).length + 1#64 =
      BitVec.ofNat 64 (uint32Field 1 v).length := by
  rw [← uint32Field1_nonzero_eq_er h]
  simp only [List.length_append, List.length_singleton, ← BitVec.ofNat_add, Nat.add_comm]

theorem uint32Field1_length_le (v : BitVec 32) :
    (uint32Field 1 v).length ≤ 11 := by
  by_cases hv : v = 0#32
  · subst hv; simp [uint32Field1_zero_eq_er]
  · rw [← uint32Field1_nonzero_eq_er hv]
    have h := encodeVarint_length_le_10 (BitVec.zeroExtend 64 v)
    simp only [List.length_append, List.length_singleton]
    omega

theorem encPendingKyber_length_bv (k : PendingKyberPreKey) :
    BitVec.ofNat 64 (bytesField 2 k.ciphertext).length +
      BitVec.ofNat 64 (uint32Field 1 k.preKeyId).length =
      BitVec.ofNat 64 (encPendingKyber k).length := by
  unfold encPendingKyber
  simp only [List.length_append, ← BitVec.ofNat_add, Nat.add_comm]

theorem encPendingKyber_length_bv_ct_nil (k : PendingKyberPreKey) (hct : k.ciphertext = []) :
    0#64 + BitVec.ofNat 64 (uint32Field 1 k.preKeyId).length =
      BitVec.ofNat 64 (encPendingKyber k).length := by
  rw [← encPendingKyber_length_bv k, hct, bytesField_nil]
  rfl

theorem msgField14_some_eq (k : PendingKyberPreKey) :
    [0x72#8] ++ encodeVarint (BitVec.ofNat 64 (encPendingKyber k).length) ++
      uint32Field 1 k.preKeyId ++ bytesField 2 k.ciphertext =
      msgField 14 (some (encPendingKyber k)) := by
  unfold msgField lenField encPendingKyber
  have hk : encodeKey 14 .lengthDelimited = [0x72#8] := by decide +kernel
  rw [hk]
  simp only [List.append_assoc]

theorem optTailVecAt_kyber_none_eq (A : RustAlloc) (ss : BitVec 64) :
    optTailVecAt A 32 (ss + 296#64) none =
      ((ss + 296#64) ↦₆₄ noneCap) ∗ memRegion (ss + 304#64) (32 - 8) := by
  have hadd : (ss + 296#64) + 8#64 = ss + 304#64 := by bv_lin
  dsimp only [optTailVecAt]
  rw [hadd]

@[expose] def kyberTailRest (ss : BitVec 64) (g : TailVecGhost) : SepProp :=
  (ss + 324#64) ↦ₛ g.tail.drop 4

@[expose] def kyberOpenAt (A : RustAlloc) (ss : BitVec 64) (g : TailVecGhost) (k : PendingKyberPreKey) : SepProp :=
  vecU8At A (ss + 296#64) g.vec.cap g.vec.ptr k.ciphertext ∗
  ((ss + 320#64) ↦₃₂ k.preKeyId) ∗
  kyberTailRest ss g

theorem optTailVecAt_kyber_some_eq_open (A : RustAlloc) (ss : BitVec 64)
    (g : TailVecGhost) (k : PendingKyberPreKey)
    (hlen8 : g.tail.length = 8)
    (hrel : KyberRel (some g) (some k)) :
    optTailVecAt A 32 (ss + 296#64) (some g) = kyberOpenAt A ss g k := by
  obtain ⟨hvec, hpk⟩ := hrel
  have hpure : (g.tail.length = 32 - 24) = True := eq_true hlen8
  have hadd : (ss + 296#64) + 24#64 = ss + 320#64 := by bv_lin
  dsimp only [optTailVecAt, vecGhostAt]
  rw [hpure, pure_true, emp_sepConj, hadd, hvec,
      pointsToBytes_kyber_tail_eq ss hpk]
  unfold kyberOpenAt kyberTailRest
  ac_rfl

theorem sepWPp_extract_kyber_some {prog : Program} {ret : BitVec 64} {s : State}
    {A : RustAlloc} {ss : BitVec 64} {g : TailVecGhost} {P F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hfocus : P = optTailVecAt A 32 (ss + 296#64) (some g) ∗ F := by sep_focus)
    (h : g.tail.length = 8 → g.vec.bytes.length ≤ g.vec.cap.toNat →
      g.vec.cap.toNat < 2 ^ 63 → g.vec.ptr ≠ 0#64 →
      SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s P Q Qp := by
  have hfocus1 : P = ⌜g.tail.length = 8⌝ ∗
      (vecU8At A (ss + 296#64) g.vec.cap g.vec.ptr g.vec.bytes ∗
        ((ss + 296#64 + 24#64) ↦ₛ g.tail) ∗ F) := by
    rw [hfocus]; dsimp only [optTailVecAt, vecGhostAt]; ac_rfl
  intro R hm hL
  have hm1 := hm
  rw [hfocus1, sepConj_assoc, satisfies_pure_sepConj] at hm1
  have hfocus2 : P = vecU8At A (ss + 296#64) g.vec.cap g.vec.ptr g.vec.bytes ∗
      (⌜g.tail.length = 8⌝ ∗ ((ss + 296#64 + 24#64) ↦ₛ g.tail) ∗ F) := by
    rw [hfocus]; dsimp only [optTailVecAt, vecGhostAt]; ac_rfl
  exact sepWPp_extract_vecU8At_bounds (hfocus := hfocus2)
    (fun hle hcap hptr => h hm1.1 hle hcap hptr) R hm hL

set_option allowUnsafeReducibility true
attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local irreducible] stackAt vecRest vecU8Buf vecSrcRest vecCopyDone kyberTailRest
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  truncate32_signExtend64_er truncate32_zeroExtend64
  Prost.ofNat_countLeadingZeros_64
  Prost.ofNat_countLeadingZeros_32
  Prost.truncate32_ofNat64
  er_truncate32_zext64_lsr6
  erHwVarintLen_eq_encodeVarint_length
  erHwVarintLen_bvShift_eq_encodeVarint_length

@[local arm64_norm]
theorem bv_add_neg80_4b (x : BitVec 64) : x + bv% (2 ^ 64 - 80) = x - 80#64 :=
  (BitVec.sub_eq_add_neg x 80#64).symm

set_option maxHeartbeats 400000

/-! ## Outer tag `0x72` (`1292..1348`) -/

theorem zext64_bne_zero_true_4b {v : BitVec 32} (h : v ≠ 0#32) :
    (BitVec.zeroExtend 64 v != 0#64) = true := by
  simp only [bne, zext64_beq_zero_false_3b h, Bool.not_false]

end CryptoVerification.E2E.Record.Serialization.EncodeRawAux
