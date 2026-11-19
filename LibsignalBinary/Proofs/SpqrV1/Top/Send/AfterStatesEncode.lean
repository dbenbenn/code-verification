/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.Defs
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Defs
public import LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.Defs
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.Decodes -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesChainStep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `spqr::send`: `Message::serialize`, `States::into_pb`, and `VersionNegotiation` Length

Call setup and post-checks for `<Message>::serialize` and `<States>::into_pb`, 352-byte
`PqRatchetState` stack assembly (`0x317fc..0x31968`), and inlined
`Option<VersionNegotiation>::encoded_len` (`0x3191c..0x31afc`) in `spqr::send::<HookRng>`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.CodeLayout
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.ChainFrom.ChainFromNorm
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.Prost.EncodeToVec
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (ule_self_64 ult_self_64
   ofNat_length_beq_zero_of_lt bv_u32VarintField_nonzero bv_bytesField_nonempty
   bv_add_ofNat_comm bv_add_ofNat_eq adds_no_overflow_of_eq cmp_ls_false_of_lt)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 ule_self_64 ult_self_64

theorem vecU8At_cons_entails (A : RustAlloc) (v cap ptr : BitVec 64) (b0 : BitVec 8)
    (tail : List (BitVec 8)) :
    vecU8At A v cap ptr (b0 :: tail) ⊢
      ⌜(b0 :: tail).length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0 ∧
        (BitVec.ofNat 64 (b0 :: tail).length == 0#64) = false⌝ ∗
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (b0 :: tail).length) ∗
      A.live ptr cap.toNat 1 ∗ (ptr ↦₈ b0) ∗ ((ptr + 1#64) ↦ₛ tail) ∗
      memRegion (ptr + BitVec.ofNat 64 (b0 :: tail).length) (cap.toNat - (b0 :: tail).length) := by
  unfold vecU8At vecHeader
  refine Entails.trans (Entails.of_eq (show
    ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (b0 :: tail).length)) ∗
      ⌜(b0 :: tail).length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ (b0 :: tail)) ∗
        memRegion (ptr + BitVec.ofNat 64 (b0 :: tail).length) (cap.toNat - (b0 :: tail).length)) =
    ⌜(b0 :: tail).length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (b0 :: tail).length) ∗
        (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ (b0 :: tail)) ∗
          memRegion (ptr + BitVec.ofNat 64 (b0 :: tail).length) (cap.toNat - (b0 :: tail).length)))
    by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨h1, h2, h3⟩
  have hcap_ne : cap ≠ 0 := by intro hc; subst hc; simp at h1
  have hlen_ne : (BitVec.ofNat 64 (b0 :: tail).length == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; intro h0
    have h0n := congrArg BitVec.toNat h0
    simp only [List.length_cons, BitVec.toNat_ofNat, BitVec.toNat_zero] at h0n h1
    omega
  simp only [hcap_ne, ↓reduceIte, ProofLib.pointsToBytes_cons]
  exact Entails.pure_right ⟨h1, h2, h3, hlen_ne⟩ (Entails.of_eq (by ac_rfl))

theorem memRegion_928_split1 (a : BitVec 64) :
    memRegion a 928 = (∃∗ b0 : BitVec 8, a ↦₈ b0) ∗ memRegion (a + 1#64) 927 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 1) (k := 927) (b' := a + 1#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_one a]

theorem pointsTo8_memRegion_927_to_928 (a : BitVec 64) (b0 : BitVec 8) :
    (a ↦₈ b0) ∗ memRegion (a + 1#64) 927 ⊢ memRegion a 928 := by
  rw [memRegion_928_split1 a]
  exact sepConj_mono_left (Entails.sepExists_right b0 (Entails.refl _))

theorem vecU8At_cons_repack (A : RustAlloc) (v cap ptr : BitVec 64) (b0 : BitVec 8)
    (tail : List (BitVec 8))
    (h1 : (b0 :: tail).length ≤ cap.toNat) (h2 : cap.toNat < 2 ^ 63) (h3 : ptr ≠ 0) :
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (b0 :: tail).length) ∗
      A.live ptr cap.toNat 1 ∗ (ptr ↦₈ b0) ∗ ((ptr + 1#64) ↦ₛ tail) ∗
      memRegion (ptr + BitVec.ofNat 64 (b0 :: tail).length) (cap.toNat - (b0 :: tail).length) ⊢
      vecU8 A v (b0 :: tail) := by
  have hcap_ne : cap ≠ 0 := by intro hc; subst hc; simp at h1
  unfold vecU8
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  unfold vecU8At vecHeader
  simp only [hcap_ne, ↓reduceIte, ProofLib.pointsToBytes_cons]
  refine Entails.trans ?_ (Entails.of_eq (show
    ⌜(b0 :: tail).length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (b0 :: tail).length) ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦₈ b0) ∗ ((ptr + 1#64) ↦ₛ tail) ∗
        memRegion (ptr + BitVec.ofNat 64 (b0 :: tail).length) (cap.toNat - (b0 :: tail).length)) =
    ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (b0 :: tail).length)) ∗
      ⌜(b0 :: tail).length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (A.live ptr cap.toNat 1 ∗ ((ptr ↦₈ b0) ∗ ((ptr + 1#64) ↦ₛ tail)) ∗
        memRegion (ptr + BitVec.ofNat 64 (b0 :: tail).length) (cap.toNat - (b0 :: tail).length))
    by ac_rfl))
  exact Entails.pure_right ⟨h1, h2, h3⟩ (Entails.of_eq (by ac_rfl))

theorem memRegion_928_entails_split1 (a : BitVec 64) :
    memRegion a 928 ⊢ (∃∗ b0 : BitVec 8, a ↦₈ b0) ∗ memRegion (a + 1#64) 927 :=
  Entails.of_eq (memRegion_928_split1 a)

theorem vecU8_cons_entails (A : RustAlloc) (v : BitVec 64) (b0 : BitVec 8)
    (tail : List (BitVec 8)) :
    vecU8 A v (b0 :: tail) ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜(b0 :: tail).length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0 ∧
          (BitVec.ofNat 64 (b0 :: tail).length == 0#64) = false⌝ ∗
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (b0 :: tail).length) ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦₈ b0) ∗ ((ptr + 1#64) ↦ₛ tail) ∗
        memRegion (ptr + BitVec.ofNat 64 (b0 :: tail).length) (cap.toNat - (b0 :: tail).length) := by
  unfold vecU8
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  exact Entails.sepExists_right cap
    (Entails.sepExists_right ptr (vecU8At_cons_entails A v cap ptr b0 tail))

/-- Pure relation characterizing words `+24`, `+32`, `+40` of `VersionNegotiationPB`:
    `chainParams : Option ChainParamsPB` (`12`B at `+24..+36`), `direction : BitVec 32` (`4`B at
    `+36..+40`), `minVersion : BitVec 32` (`4`B at `+40..+44`), and 4 bytes padding at
    `+44..+48`. -/
@[expose] def vnParamsDirMinVerWords (vn : VersionNegotiationPB) (w3 w4 w5 : BitVec 64) : Prop :=
  (match vn.chainParams with
   | none => ∃ p0 p1 : BitVec 32, w3 = p0 ++ 0#32 ∧ w4 = vn.direction ++ p1
   | some cp => w3 = cp.maxJump ++ 1#32 ∧ w4 = vn.direction ++ cp.maxOooKeys) ∧
  ∃ p2 : BitVec 32, w5 = p2 ++ vn.minVersion

theorem memRegion_40_words5 (a : BitVec 64) :
    memRegion a 40 =
      (∃∗ w1 : BitVec 64, a ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (a + 8#64) ↦₆₄ w2) ∗
      (∃∗ w3 : BitVec 64, (a + 16#64) ↦₆₄ w3) ∗
      (∃∗ w4 : BitVec 64, (a + 24#64) ↦₆₄ w4) ∗
      (∃∗ w5 : BitVec 64, (a + 32#64) ↦₆₄ w5) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 32) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 24) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 16) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 8) (b' := a + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64),
      ProofLib.memRegion_eight (a + 16#64), ProofLib.memRegion_eight (a + 24#64),
      ProofLib.memRegion_eight (a + 32#64)]

theorem words5_to_memRegion_40 (a w1 w2 w3 w4 w5 : BitVec 64) :
    (a ↦₆₄ w1) ∗ ((a + 8#64) ↦₆₄ w2) ∗ ((a + 16#64) ↦₆₄ w3) ∗
    ((a + 24#64) ↦₆₄ w4) ∗ ((a + 32#64) ↦₆₄ w5) ⊢ memRegion a 40 := by
  rw [memRegion_40_words5 a]
  exact sepConj_mono (Entails.sepExists_right w1 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right w2 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right w3 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right w4 (Entails.refl _))
      (Entails.sepExists_right w5 (Entails.refl _)))))

theorem optVersionNegRest_entails_words5 (A : RustAlloc) (g : ProtoRepr.VersionNegotiationPBGhost)
    (a : BitVec 64) (opt : Option VersionNegotiationPB) :
    Prost.EncodeToVec.optVersionNegRest A g a opt ⊢
      ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
        ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
        ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗
        match opt with
        | none => emp
        | some vn =>
          ⌜w1 = g.authKey.ptr ∧ w2 = BitVec.ofNat 64 vn.authKey.length ∧
            vnParamsDirMinVerWords vn w3 w4 w5⌝ ∗
          ProtoRepr.EncodedLen.vecU8Buf A g.authKey.cap g.authKey.ptr vn.authKey := by
  have ha16 : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
  have ha24 : a + 8#64 + 16#64 = a + 24#64 := by bv_omega
  have ha32 : a + 8#64 + 24#64 = a + 32#64 := by bv_omega
  have ha40 : a + 8#64 + 32#64 = a + 40#64 := by bv_omega
  cases opt with
  | none =>
    dsimp only [Prost.EncodeToVec.optVersionNegRest]
    rw [memRegion_40_words5 (a + 8#64), ha16, ha24, ha32, ha40]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply ProofLib.Entails.sepExists_elim; intro w5
    apply ProofLib.Entails.sepExists_elim; intro w4
    apply ProofLib.Entails.sepExists_elim; intro w3
    apply ProofLib.Entails.sepExists_elim; intro w2
    apply ProofLib.Entails.sepExists_elim; intro w1
    refine Entails.sepExists_right w1 (Entails.sepExists_right w2
      (Entails.sepExists_right w3 (Entails.sepExists_right w4
      (Entails.sepExists_right w5 ?_))))
    exact Entails.of_eq (by ac_rfl)
  | some vn =>
    dsimp only [Prost.EncodeToVec.optVersionNegRest, Prost.EncodeToVec.versionNegotiationRest]
    have ha28 : a + 24#64 + 4#64 = a + 28#64 := by bv_omega
    have ha32' : a + 28#64 + 4#64 = a + 32#64 := by bv_omega
    have ha36 : a + 36#64 = a + 32#64 + 4#64 := by bv_omega
    have ha44 : a + 44#64 = a + 40#64 + 4#64 := by bv_omega
    rw [ProofLib.memRegion_four (a + 44#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply ProofLib.Entails.sepExists_elim; intro p2
    have h5 := ChainFromNorm.pointsTo32_pair_eq_pointsTo64 (a + 40#64) vn.minVersion p2
    rw [← ha44] at h5
    cases hcp : vn.chainParams with
    | none =>
      dsimp only [ProtoRepr.optChainParamsPBAt]
      rw [ha28, ha36,
          ProofLib.memRegion_split' (b := a + 28#64) (n := 4) (k := 4)
            (b' := a + 32#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_four (a + 28#64),
          ProofLib.memRegion_four (a + 32#64)]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply ProofLib.Entails.sepExists_elim; intro p1
      apply ProofLib.Entails.sepExists_elim; intro p0
      have h3 := ChainFromNorm.pointsTo32_pair_eq_pointsTo64 (a + 24#64) 0#32 p0
      rw [ha28] at h3
      have h4 := ChainFromNorm.pointsTo32_pair_eq_pointsTo64 (a + 32#64) p1 vn.direction
      refine Entails.sepExists_right g.authKey.ptr
        (Entails.sepExists_right (BitVec.ofNat 64 vn.authKey.length)
        (Entails.sepExists_right (p0 ++ 0#32)
        (Entails.sepExists_right (vn.direction ++ p1)
        (Entails.sepExists_right (p2 ++ vn.minVersion) ?_))))
      have hpure : vnParamsDirMinVerWords vn (p0 ++ 0#32) (vn.direction ++ p1) (p2 ++ vn.minVersion) := by
        unfold vnParamsDirMinVerWords; rw [hcp]; exact ⟨⟨p0, p1, rfl, rfl⟩, ⟨p2, rfl⟩⟩
      refine Entails.trans ?_ (Entails.of_eq (show
        ⌜g.authKey.ptr = g.authKey.ptr ∧
          BitVec.ofNat 64 vn.authKey.length = BitVec.ofNat 64 vn.authKey.length ∧
          vnParamsDirMinVerWords vn (p0 ++ 0#32) (vn.direction ++ p1) (p2 ++ vn.minVersion)⌝ ∗
        (((a + 8#64) ↦₆₄ g.authKey.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
          ((a + 24#64) ↦₆₄ (p0 ++ 0#32)) ∗
          ((a + 32#64) ↦₆₄ (vn.direction ++ p1)) ∗
          ((a + 40#64) ↦₆₄ (p2 ++ vn.minVersion)) ∗
          ProtoRepr.EncodedLen.vecU8Buf A g.authKey.cap g.authKey.ptr vn.authKey) =
        ((a + 8#64) ↦₆₄ g.authKey.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
          ((a + 24#64) ↦₆₄ (p0 ++ 0#32)) ∗
          ((a + 32#64) ↦₆₄ (vn.direction ++ p1)) ∗
          ((a + 40#64) ↦₆₄ (p2 ++ vn.minVersion)) ∗
          (⌜g.authKey.ptr = g.authKey.ptr ∧
            BitVec.ofNat 64 vn.authKey.length = BitVec.ofNat 64 vn.authKey.length ∧
            vnParamsDirMinVerWords vn (p0 ++ 0#32) (vn.direction ++ p1) (p2 ++ vn.minVersion)⌝ ∗
            ProtoRepr.EncodedLen.vecU8Buf A g.authKey.cap g.authKey.ptr vn.authKey) by ac_rfl))
      apply Entails.pure_right ⟨rfl, rfl, hpure⟩
      rw [← h3, ← h4, ← h5]
      exact Entails.of_eq (by ac_rfl)
    | some cp =>
      dsimp only [ProtoRepr.optChainParamsPBAt, ProtoRepr.chainParamsPBAt]
      rw [ha28, ha32', ha36]
      have h3 := ChainFromNorm.pointsTo32_pair_eq_pointsTo64 (a + 24#64) 1#32 cp.maxJump
      rw [ha28] at h3
      have h4 := ChainFromNorm.pointsTo32_pair_eq_pointsTo64 (a + 32#64) cp.maxOooKeys vn.direction
      refine Entails.sepExists_right g.authKey.ptr
        (Entails.sepExists_right (BitVec.ofNat 64 vn.authKey.length)
        (Entails.sepExists_right (cp.maxJump ++ 1#32)
        (Entails.sepExists_right (vn.direction ++ cp.maxOooKeys)
        (Entails.sepExists_right (p2 ++ vn.minVersion) ?_))))
      have hpure : vnParamsDirMinVerWords vn (cp.maxJump ++ 1#32) (vn.direction ++ cp.maxOooKeys) (p2 ++ vn.minVersion) := by
        unfold vnParamsDirMinVerWords; rw [hcp]; exact ⟨⟨rfl, rfl⟩, ⟨p2, rfl⟩⟩
      refine Entails.trans ?_ (Entails.of_eq (show
        ⌜g.authKey.ptr = g.authKey.ptr ∧
          BitVec.ofNat 64 vn.authKey.length = BitVec.ofNat 64 vn.authKey.length ∧
          vnParamsDirMinVerWords vn (cp.maxJump ++ 1#32) (vn.direction ++ cp.maxOooKeys) (p2 ++ vn.minVersion)⌝ ∗
        (((a + 8#64) ↦₆₄ g.authKey.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
          ((a + 24#64) ↦₆₄ (cp.maxJump ++ 1#32)) ∗
          ((a + 32#64) ↦₆₄ (vn.direction ++ cp.maxOooKeys)) ∗
          ((a + 40#64) ↦₆₄ (p2 ++ vn.minVersion)) ∗
          ProtoRepr.EncodedLen.vecU8Buf A g.authKey.cap g.authKey.ptr vn.authKey) =
        ((a + 8#64) ↦₆₄ g.authKey.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
          ((a + 24#64) ↦₆₄ (cp.maxJump ++ 1#32)) ∗
          ((a + 32#64) ↦₆₄ (vn.direction ++ cp.maxOooKeys)) ∗
          ((a + 40#64) ↦₆₄ (p2 ++ vn.minVersion)) ∗
          (⌜g.authKey.ptr = g.authKey.ptr ∧
            BitVec.ofNat 64 vn.authKey.length = BitVec.ofNat 64 vn.authKey.length ∧
            vnParamsDirMinVerWords vn (cp.maxJump ++ 1#32) (vn.direction ++ cp.maxOooKeys) (p2 ++ vn.minVersion)⌝ ∗
            ProtoRepr.EncodedLen.vecU8Buf A g.authKey.cap g.authKey.ptr vn.authKey) by ac_rfl))
      apply Entails.pure_right ⟨rfl, rfl, hpure⟩
      rw [← h3, ← h4, ← h5]
      exact Entails.of_eq (by ac_rfl)

theorem words5_entails_optVersionNegRest (A : RustAlloc) (g : ProtoRepr.VersionNegotiationPBGhost)
    (a : BitVec 64) (opt : Option VersionNegotiationPB) (w1 w2 w3 w4 w5 : BitVec 64) :
    ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
    ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗
    (match opt with
     | none => emp
     | some vn =>
       ⌜w1 = g.authKey.ptr ∧ w2 = BitVec.ofNat 64 vn.authKey.length ∧
         vnParamsDirMinVerWords vn w3 w4 w5⌝ ∗
       ProtoRepr.EncodedLen.vecU8Buf A g.authKey.cap g.authKey.ptr vn.authKey) ⊢
      Prost.EncodeToVec.optVersionNegRest A g a opt := by
  have ha16 : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
  have ha24 : a + 8#64 + 16#64 = a + 24#64 := by bv_omega
  have ha32 : a + 8#64 + 24#64 = a + 32#64 := by bv_omega
  have ha40 : a + 8#64 + 32#64 = a + 40#64 := by bv_omega
  cases opt with
  | none =>
    dsimp only [Prost.EncodeToVec.optVersionNegRest]
    rw [sepConj_emp]
    have h40 := words5_to_memRegion_40 (a + 8#64) w1 w2 w3 w4 w5
    rw [ha16, ha24, ha32, ha40] at h40
    exact h40
  | some vn =>
    dsimp only [Prost.EncodeToVec.optVersionNegRest, Prost.EncodeToVec.versionNegotiationRest]
    refine Entails.trans (Entails.of_eq (show
      ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
        ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗
        (⌜w1 = g.authKey.ptr ∧ w2 = BitVec.ofNat 64 vn.authKey.length ∧
          vnParamsDirMinVerWords vn w3 w4 w5⌝ ∗
          ProtoRepr.EncodedLen.vecU8Buf A g.authKey.cap g.authKey.ptr vn.authKey) =
      ⌜w1 = g.authKey.ptr ∧ w2 = BitVec.ofNat 64 vn.authKey.length ∧
        vnParamsDirMinVerWords vn w3 w4 w5⌝ ∗
        (((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
          ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗
          ProtoRepr.EncodedLen.vecU8Buf A g.authKey.cap g.authKey.ptr vn.authKey) by ac_rfl)) ?_
    apply Entails.pure_left
    rintro ⟨rfl, rfl, hparams, p2, rfl⟩
    have ha28 : a + 24#64 + 4#64 = a + 28#64 := by bv_omega
    have ha32' : a + 28#64 + 4#64 = a + 32#64 := by bv_omega
    have ha36 : a + 36#64 = a + 32#64 + 4#64 := by bv_omega
    have ha44 : a + 44#64 = a + 40#64 + 4#64 := by bv_omega
    have h5 := ChainFromNorm.pointsTo32_pair_eq_pointsTo64 (a + 40#64) vn.minVersion p2
    rw [← ha44] at h5
    have hp2_mem : ((a + 44#64) ↦₃₂ p2) ⊢ memRegion (a + 44#64) 4 :=
      ProofLib.pointsTo32_entails_memRegion (a + 44#64) p2
    cases hcp : vn.chainParams with
    | none =>
      rw [hcp] at hparams
      rcases hparams with ⟨p0, p1, rfl, rfl⟩
      dsimp only [ProtoRepr.optChainParamsPBAt]
      have h3 := ChainFromNorm.pointsTo32_pair_eq_pointsTo64 (a + 24#64) 0#32 p0
      rw [ha28] at h3
      have h4 := ChainFromNorm.pointsTo32_pair_eq_pointsTo64 (a + 32#64) p1 vn.direction
      rw [← ha36] at h4
      rw [← h3, ← h4, ← h5]
      have hp01_mem : ((a + 28#64) ↦₃₂ p0) ∗ ((a + 32#64) ↦₃₂ p1) ⊢ memRegion (a + 24#64 + 4#64) 8 := by
        rw [ha28,
            ProofLib.memRegion_split' (b := a + 28#64) (n := 4) (k := 4)
              (b' := a + 32#64) rfl (by bv_omega) (by decide)]
        exact sepConj_mono (ProofLib.pointsTo32_entails_memRegion _ _)
          (ProofLib.pointsTo32_entails_memRegion _ _)
      refine Entails.trans (Entails.of_eq (show
        ((a + 8#64) ↦₆₄ g.authKey.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
          (((a + 24#64) ↦₃₂ 0#32) ∗ ((a + 28#64) ↦₃₂ p0)) ∗
          (((a + 32#64) ↦₃₂ p1) ∗ ((a + 36#64) ↦₃₂ vn.direction)) ∗
          (((a + 40#64) ↦₃₂ vn.minVersion) ∗ ((a + 44#64) ↦₃₂ p2)) ∗
          ProtoRepr.EncodedLen.vecU8Buf A g.authKey.cap g.authKey.ptr vn.authKey =
        (((a + 28#64) ↦₃₂ p0) ∗ ((a + 32#64) ↦₃₂ p1)) ∗
          ((a + 44#64) ↦₃₂ p2) ∗
          (((a + 8#64) ↦₆₄ g.authKey.ptr) ∗
            ((a + 16#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
            ProtoRepr.EncodedLen.vecU8Buf A g.authKey.cap g.authKey.ptr vn.authKey ∗
            ((a + 24#64) ↦₃₂ 0#32) ∗
            ((a + 36#64) ↦₃₂ vn.direction) ∗
            ((a + 40#64) ↦₃₂ vn.minVersion)) by ac_rfl)) ?_
      refine Entails.trans (sepConj_mono hp01_mem (sepConj_mono_left hp2_mem)) ?_
      exact Entails.of_eq (by ac_rfl)
    | some cp =>
      rw [hcp] at hparams
      rcases hparams with ⟨rfl, rfl⟩
      dsimp only [ProtoRepr.optChainParamsPBAt, ProtoRepr.chainParamsPBAt]
      rw [ha28, ha32']
      have h3 := ChainFromNorm.pointsTo32_pair_eq_pointsTo64 (a + 24#64) 1#32 cp.maxJump
      rw [ha28] at h3
      have h4 := ChainFromNorm.pointsTo32_pair_eq_pointsTo64 (a + 32#64) cp.maxOooKeys vn.direction
      rw [← ha36] at h4
      rw [← h3, ← h4, ← h5]
      refine Entails.trans (Entails.of_eq (show
        ((a + 8#64) ↦₆₄ g.authKey.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
          (((a + 24#64) ↦₃₂ 1#32) ∗ ((a + 28#64) ↦₃₂ cp.maxJump)) ∗
          (((a + 32#64) ↦₃₂ cp.maxOooKeys) ∗ ((a + 36#64) ↦₃₂ vn.direction)) ∗
          (((a + 40#64) ↦₃₂ vn.minVersion) ∗ ((a + 44#64) ↦₃₂ p2)) ∗
          ProtoRepr.EncodedLen.vecU8Buf A g.authKey.cap g.authKey.ptr vn.authKey =
        ((a + 44#64) ↦₃₂ p2) ∗
          (((a + 8#64) ↦₆₄ g.authKey.ptr) ∗
            ((a + 16#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
            ProtoRepr.EncodedLen.vecU8Buf A g.authKey.cap g.authKey.ptr vn.authKey ∗
            ((a + 24#64) ↦₃₂ 1#32) ∗
            ((a + 28#64) ↦₃₂ cp.maxJump) ∗
            ((a + 32#64) ↦₃₂ cp.maxOooKeys) ∗
            ((a + 36#64) ↦₃₂ vn.direction) ∗
            ((a + 40#64) ↦₃₂ vn.minVersion)) by ac_rfl)) ?_
      refine Entails.trans (sepConj_mono_left hp2_mem) ?_
      exact Entails.of_eq (by ac_rfl)

@[expose] def vnWords6At (a w0 w1 w2 w3 w4 w5 : BitVec 64) : SepProp :=
  (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
  ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5)

@[expose] def chainWords9At (a c1 c2 c3 c4 c5 c6 c7 c8 c9 : BitVec 64) : SepProp :=
  (a ↦₆₄ c1) ∗ ((a + 8#64) ↦₆₄ c2) ∗ ((a + 16#64) ↦₆₄ c3) ∗
  ((a + 24#64) ↦₆₄ c4) ∗ ((a + 32#64) ↦₆₄ c5) ∗ ((a + 40#64) ↦₆₄ c6) ∗
  ((a + 48#64) ↦₆₄ c7) ∗ ((a + 56#64) ↦₆₄ c8) ∗ ((a + 64#64) ↦₆₄ c9)

theorem outWords28_entails_memRegion_224 (out : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 w56
     w64 w72 w80 w88 w96 w104 w112 w120
     w128 w136 w144 w152 w160 w168 w176 w184
     w192 w200 w208 w216 : BitVec 64) :
    outWords28 out
      w0 w8 w16 w24 w32 w40 w48 w56
      w64 w72 w80 w88 w96 w104 w112 w120
      w128 w136 w144 w152 w160 w168 w176 w184
      w192 w200 w208 w216 ⊢
    memRegion out optProtoInnerStateSize := by
  rw [memRegion_out_224_eq out]
  exact Entails.sepExists_right w0 (Entails.sepExists_right w8
    (Entails.sepExists_right w16 (Entails.sepExists_right w24
    (Entails.sepExists_right w32 (Entails.sepExists_right w40
    (Entails.sepExists_right w48 (Entails.sepExists_right w56
    (Entails.sepExists_right w64 (Entails.sepExists_right w72
    (Entails.sepExists_right w80 (Entails.sepExists_right w88
    (Entails.sepExists_right w96 (Entails.sepExists_right w104
    (Entails.sepExists_right w112 (Entails.sepExists_right w120
    (Entails.sepExists_right w128 (Entails.sepExists_right w136
    (Entails.sepExists_right w144 (Entails.sepExists_right w152
    (Entails.sepExists_right w160 (Entails.sepExists_right w168
    (Entails.sepExists_right w176 (Entails.sepExists_right w184
    (Entails.sepExists_right w192 (Entails.sepExists_right w200
    (Entails.sepExists_right w208 (Entails.sepExists_right w216 (Entails.refl _))))))))))))))))))))))))))))

theorem memRegion_48_vnWords6 (a : BitVec 64) :
    memRegion a 48 =
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
        vnWords6At a w0 w1 w2 w3 w4 w5 := by
  rw [show (48 : Nat) = 8 * 6 from rfl, ProofLib.memRegion_cells a 6 (by decide)]
  unfold vnWords6At
  simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
    sepExists_sepConj_right, BitVec.add_assoc]
  rfl

theorem vnWords6_to_memRegion_48 (a w0 w1 w2 w3 w4 w5 : BitVec 64) :
    vnWords6At a w0 w1 w2 w3 w4 w5 ⊢ memRegion a 48 := by
  rw [memRegion_48_vnWords6 a]
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1
    (Entails.sepExists_right w2 (Entails.sepExists_right w3
    (Entails.sepExists_right w4 (Entails.sepExists_right w5 (Entails.refl _))))))

theorem chainWords9_to_memRegion_72 (a c1 c2 c3 c4 c5 c6 c7 c8 c9 : BitVec 64) :
    chainWords9At a c1 c2 c3 c4 c5 c6 c7 c8 c9 ⊢ memRegion a 72 :=
  words9_to_memRegion_72 a c1 c2 c3 c4 c5 c6 c7 c8 c9

theorem memRegion_80_chainWords (a : BitVec 64) :
    memRegion a 80 =
      ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64,
      ∃∗ c3 : BitVec 64, ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64,
      ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64, ∃∗ c8 : BitVec 64,
      ∃∗ c9 : BitVec 64,
        (a ↦₆₄ c0) ∗ chainWords9At (a + 8#64) c1 c2 c3 c4 c5 c6 c7 c8 c9 := by
  rw [show (80 : Nat) = 8 * 10 from rfl, ProofLib.memRegion_cells a 10 (by decide)]
  unfold chainWords9At
  simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
    sepExists_sepConj_right, BitVec.add_assoc]
  rfl

theorem memRegion_352_split (a : BitVec 64) :
    memRegion a 352 =
      memRegion a 48 ∗ memRegion (a + 48#64) 80 ∗ memRegion (a + 128#64) optProtoInnerStateSize := by
  rw [ProofLib.memRegion_split' (b := a) (n := 48) (k := 304) (b' := a + 48#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 48#64) (n := 80) (k := 224) (b' := a + 128#64)
        rfl (by bv_omega) (by decide)]
  rfl

end CryptoVerification.SpqrV1.Top.Send

