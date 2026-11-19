/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.EpilogueExt -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

public section

set_option autoImplicit false

/-! # `<spqr::v1::chunked::states::States>::from_pb`: Variant 0 (`KeysUnsampled`, `+156`) -/

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

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

/-! ## Variant 0 (`KeysUnsampled`, `+156`) Error Paths (`uc = none` and `auth = none`) -/

theorem pbA_keysUnsampled_uc_none_entails_224 (pbA : BitVec 64) :
    (pbA ↦₆₄ 0x8000000000000000#64) ∗ ((pbA + 8#64) ↦₆₄ none2Cap) ∗
      memRegion (pbA + 16#64) 48 ∗ memRegion (pbA + 64#64) 160 ⊢
    memRegion pbA optProtoInnerStateSize := by
  exact collapse_top <| collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Entails.refl _) <| Entails.refl _

theorem pbA_keysUnsampled_auth_none_entails_224 (pbA ep : BitVec 64) :
    (pbA ↦₆₄ 0x8000000000000000#64) ∗ ((pbA + 8#64) ↦₆₄ noneCap) ∗
      memRegion (pbA + 16#64) 40 ∗ ((pbA + 56#64) ↦₆₄ ep) ∗ memRegion (pbA + 64#64) 160 ⊢
    memRegion pbA optProtoInnerStateSize := by
  exact collapse_top <| collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| Entails.refl _

theorem pbA_keysUnsampled_some_entails_224 (pbA c1 p1 l1 c2 p2 l2 ep : BitVec 64) :
    (pbA ↦₆₄ 0x8000000000000000#64) ∗
      ((pbA + 8#64) ↦₆₄ c1) ∗ ((pbA + 16#64) ↦₆₄ p1) ∗ ((pbA + 24#64) ↦₆₄ l1) ∗
      ((pbA + 32#64) ↦₆₄ c2) ∗ ((pbA + 40#64) ↦₆₄ p2) ∗ ((pbA + 48#64) ↦₆₄ l2) ∗
      ((pbA + 56#64) ↦₆₄ ep) ∗ memRegion (pbA + 64#64) 160 ⊢
      memRegion pbA optProtoInnerStateSize := by
  exact collapse_top <| collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| Entails.refl _

theorem authPBPinnedTailAt_8_eq (A : RustAlloc) (ga : AuthenticatorPBGhost) (a : BitVec 64)
    (auth : ProtoAuthenticator) :
    authPBPinnedTailAt A ga (a + 8#64) auth =
      ((a + 16#64) ↦₆₄ ga.rootKey.ptr) ∗ ((a + 24#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
      vecU8Payload A ga.rootKey.cap ga.rootKey.ptr auth.rootKey ∗
      vecU8At A (a + 32#64) ga.macKey.cap ga.macKey.ptr auth.macKey := by
  unfold authPBPinnedTailAt
  have h1 : (a + 8#64) + 8#64 = a + 16#64 := by bv_omega
  have h2 : (a + 8#64) + 16#64 = a + 24#64 := by bv_omega
  have h3 : (a + 8#64) + 24#64 = a + 32#64 := by bv_omega
  rw [h1, h2, h3]

theorem authenticatorPBPinnedAt_8_eq_cap_tail (A : RustAlloc) (ga : AuthenticatorPBGhost)
    (a : BitVec 64) (auth : ProtoAuthenticator) :
    authenticatorPBPinnedAt A ga (a + 8#64) auth =
      ((a + 8#64) ↦₆₄ ga.rootKey.cap) ∗
      ((a + 16#64) ↦₆₄ ga.rootKey.ptr) ∗ ((a + 24#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
      vecU8Payload A ga.rootKey.cap ga.rootKey.ptr auth.rootKey ∗
      vecU8At A (a + 32#64) ga.macKey.cap ga.macKey.ptr auth.macKey := by
  rw [authenticatorPBPinnedAt_eq_cap_tail, authPBPinnedTailAt_8_eq]

theorem authenticatorPBPinnedAt_8_eq_full (A : RustAlloc) (ga : AuthenticatorPBGhost)
    (a : BitVec 64) (auth : ProtoAuthenticator) :
    authenticatorPBPinnedAt A ga (a + 8#64) auth =
      ((a + 8#64) ↦₆₄ ga.rootKey.cap) ∗
      ((a + 16#64) ↦₆₄ ga.rootKey.ptr) ∗ ((a + 24#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
      ((a + 32#64) ↦₆₄ ga.macKey.cap) ∗
      ((a + 40#64) ↦₆₄ ga.macKey.ptr) ∗ ((a + 48#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
      vecU8Payload A ga.rootKey.cap ga.rootKey.ptr auth.rootKey ∗
      vecU8Payload A ga.macKey.cap ga.macKey.ptr auth.macKey := by
  rw [authenticatorPBPinnedAt_8_eq_cap_tail]
  unfold vecU8At vecHeader vecU8Payload
  have h1 : (a + 32#64) + 8#64 = a + 40#64 := by bv_omega
  have h2 : (a + 32#64) + 16#64 = a + 48#64 := by bv_omega
  rw [h1, h2]
  ac_rfl

@[simp]
theorem spqrAuthApi_from_pb (F : ShaCompress) :
    (spqrAuthApi F).from_pb = Authenticator.fromPb := rfl

theorem sepWPp_seq_clean {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q_regs : State → Prop} {Q Qp : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q_regs sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q_regs sm →
      SepWPp prog ret sm P_mid Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP (SepWP.mono h1 fun sm _ hpc hrun ⟨hent, hq⟩ =>
    SepWPp.weaken_pre hent (h2 sm hpc hrun hq))

theorem optProtoInnerStateAt_keysUnsampled_some_eq (A : RustAlloc) (pbA : BitVec 64)
    (auth : ProtoAuthenticator) (ep : BitVec 64) :
    optProtoInnerStateAt A pbA (some (.keysUnsampled { uc := some { auth := some auth, epoch := ep } })) =
      (pbA ↦₆₄ 0x8000000000000000#64) ∗
      optProtoAuthenticatorAt A (pbA + 8#64) (some auth) ∗
      ((pbA + 56#64) ↦₆₄ ep) ∗
      memRegion (pbA + 64#64) 160 := by
  dsimp only [optProtoInnerStateAt, protoInnerStateAt, protoChunkedKeysUnsampledAt,
    optProtoUnchunkedKeysUnsampledAt, protoUnchunkedKeysUnsampledAt]
  have h56 : (pbA + 8#64) + 48#64 = pbA + 56#64 := by bv_omega
  rw [h56]; ac_rfl

@[simp]
theorem states_from_pb_keysUnsampled_uc_none_eq (F : ShaCompress) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.keysUnsampled { uc := none }) } =
      .error (.err .stateDecode) := rfl

@[simp]
theorem states_from_pb_keysUnsampled_auth_none_eq (F : ShaCompress) (ep : BitVec 64) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.keysUnsampled { uc := some { auth := none, epoch := ep } }) } =
      .error (.err .stateDecode) := rfl

@[simp]
theorem states_from_pb_keysUnsampled_some_eq (F : ShaCompress)
    (auth : ProtoAuthenticator) (ep : BitVec 64) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.keysUnsampled { uc := some { auth := some auth, epoch := ep } }) } =
      .ok (.keysUnsampled { uc := { auth := Authenticator.fromPb auth, epoch := ep } }) :=
  rfl

theorem authenticatorAt_8_pack (A : RustAlloc) (out ca1 pa1 ca2 pa2 : BitVec 64)
    (auth : Authenticator) :
    ((out + 8#64) ↦₆₄ ca1) ∗ ((out + 16#64) ↦₆₄ pa1) ∗
      ((out + 24#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
      ((out + 32#64) ↦₆₄ ca2) ∗ ((out + 40#64) ↦₆₄ pa2) ∗
      ((out + 48#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
      vecU8Payload A ca1 pa1 auth.rootKey ∗
      vecU8Payload A ca2 pa2 auth.macKey ⊢
    authenticatorAt A (out + 8#64) auth := by
  unfold authenticatorAt
  have h1 := vecU8_of_header_payload A (out + 8#64) ca1 pa1 auth.rootKey
  have h2 := vecU8_of_header_payload A (out + 32#64) ca2 pa2 auth.macKey
  have ha1 : (out + 8#64) + 8#64 = out + 16#64 := by bv_omega
  have ha2 : (out + 8#64) + 16#64 = out + 24#64 := by bv_omega
  have ha3 : (out + 8#64) + 24#64 = out + 32#64 := by bv_omega
  have hb1 : (out + 32#64) + 8#64 = out + 40#64 := by bv_omega
  have hb2 : (out + 32#64) + 16#64 = out + 48#64 := by bv_omega
  rw [ha1, ha2] at h1
  rw [hb1, hb2] at h2
  rw [ha3]
  refine Entails.trans (Entails.of_eq (show _ =
    (((out + 8#64) ↦₆₄ ca1) ∗ ((out + 16#64) ↦₆₄ pa1) ∗
     ((out + 24#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
     vecU8Payload A ca1 pa1 auth.rootKey) ∗
    (((out + 32#64) ↦₆₄ ca2) ∗ ((out + 40#64) ↦₆₄ pa2) ∗
     ((out + 48#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
     vecU8Payload A ca2 pa2 auth.macKey) by ac_rfl)) ?_
  exact sepConj_mono h1 h2

theorem memRegion_2304_split_152_208 (fsp : BitVec 64) :
    memRegion fsp 2304 ⊢
      memRegion fsp 152 ∗
      (∃∗ w152 : BitVec 64, ((fsp + 152#64) ↦₆₄ w152)) ∗
      memRegion (fsp + 160#64) 48 ∗
      (∃∗ w208 : BitVec 64, ((fsp + 208#64) ↦₆₄ w208)) ∗
      memRegion (fsp + 216#64) 2088 := by
  exact split_top <|
    split_step0 (Entails.refl _) <|
    split_step (mem64_entails _) <|
    split_step (Entails.refl _) <|
    split_step (mem64_entails _) <|
    Entails.refl _

theorem memRegion_152_8_48_entails_208 (fsp w152 : BitVec 64) :
    memRegion fsp 152 ∗ ((fsp + 152#64) ↦₆₄ w152) ∗ memRegion (fsp + 160#64) 48 ⊢
      memRegion fsp 208 := by
  exact collapse_top <|
    collapse_step0 (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    Entails.refl _

theorem memRegion_loBytes7_gap_at (a o1 o2 : BitVec 64) (k : Nat)
    (ho : o1 + 7#64 = o2 := by rfl)
    (hk : 8 + k ≤ 2 ^ 64 := by decide) :
    ProofLib.memRegion (a + o1) (7 + (1 + k)) ⊢
      (∃∗ u0 : BitVec 64, ((a + o1) ↦ₛ EncoderFromPb.loBytes7 u0)) ∗
      ProofLib.memRegion (a + o2) (1 + k) := by
  have h1 : 7 + (1 + k) = 8 + k := by omega
  rw [h1, ProofLib.memRegion_split' (b := a + o1) (n := 8) (k := k)
    (b' := a + o1 + 8#64) rfl rfl hk,
    ProofLib.memRegion_eight (a + o1), sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro u0
  rw [pointsTo64_split_7_1 (a + o1) u0, sepConj_assoc, sepExists_sepConj_left]
  refine Entails.sepExists_right u0 (sepConj_mono_right ?_)
  have ha7 : a + o1 + 7#64 = a + o2 := by rw [BitVec.add_assoc, ho]
  have ha8 : a + o1 + 8#64 = a + o2 + 1#64 := by rw [← ha7]; bv_omega
  rw [ha7, ha8, ProofLib.memRegion_split' (b := a + o2) (n := 1) (k := k)
    (b' := a + o2 + 1#64) rfl rfl (by omega)]
  exact sepConj_mono_left (pointsTo8_entails_memRegion _ _)

theorem memRegion_entails_bs :
    ∀ (n : Nat) (a : BitVec 64), n ≤ 2 ^ 64 →
      ProofLib.memRegion a n ⊢
        ∃∗ bs : { l : List (BitVec 8) // l.length = n }, (a ↦ₛ bs.val)
  | 0, a, _ => by
    rw [ProofLib.memRegion_zero]
    refine Entails.sepExists_right ⟨[], rfl⟩ ?_
    rw [ProofLib.pointsToBytes_nil]
    exact Entails.refl _
  | n + 1, a, hn => by
    have hsplit : n + 1 = 1 + n := by omega
    rw [hsplit, ProofLib.memRegion_split a 1 n (by omega), ProofLib.memRegion_one a,
        sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro b0
    refine Entails.trans (sepConj_mono_right (memRegion_entails_bs n (a + 1#64) (by omega))) ?_
    rw [sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro ⟨bs, hlen⟩
    refine Entails.sepExists_right ⟨b0 :: bs, by simp [hlen]; omega⟩ ?_
    rw [ProofLib.pointsToBytes_cons]
    exact Entails.refl _

theorem memRegion_328_entails_bs (a : BitVec 64) :
    ProofLib.memRegion a 328 ⊢
      ∃∗ bs : { l : List (BitVec 8) // l.length = 328 }, (a ↦ₛ bs.val) :=
  memRegion_entails_bs 328 a (by decide)

theorem memRegion_208_entails_epilogue_lo (fsp : BitVec 64) :
    memRegion fsp 208 ⊢
      memRegion fsp 92 ∗ (∃∗ d92 : BitVec 32, ((fsp + 92#64) ↦₃₂ d92)) ∗
      memRegion (fsp + 96#64) 8 ∗ (∃∗ w104 : BitVec 64, ((fsp + 104#64) ↦₆₄ w104)) ∗
      (∃∗ w112 : BitVec 64, ((fsp + 112#64) ↦₆₄ w112)) ∗ (∃∗ w120 : BitVec 64, ((fsp + 120#64) ↦₆₄ w120)) ∗
      memRegion (fsp + 128#64) 32 ∗ (∃∗ w160 : BitVec 64, ((fsp + 160#64) ↦₆₄ w160)) ∗
      memRegion (fsp + 168#64) 4 ∗ (∃∗ d172 : BitVec 32, ((fsp + 172#64) ↦₃₂ d172)) ∗
      memRegion (fsp + 176#64) 16 ∗ (∃∗ w192 : BitVec 64, ((fsp + 192#64) ↦₆₄ w192)) ∗
      memRegion (fsp + 200#64) 8 := by
  exact split_top <| split_step0 (Entails.refl _) <| split_step (mem32_entails _) <|
    split_step (Entails.refl _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (Entails.refl _) <| split_step (mem64_entails _) <|
    split_step (Entails.refl _) <| split_step (mem32_entails _) <|
    split_step (Entails.refl _) <| split_step (mem64_entails _) <| Entails.refl _

theorem memRegion_2088_entails_epilogue_hi (fsp : BitVec 64) :
    memRegion (fsp + 216#64) 2088 ⊢
      memRegion (fsp + 216#64) 8 ∗ (∃∗ w224 : BitVec 64, ((fsp + 224#64) ↦₆₄ w224)) ∗
      (∃∗ w232 : BitVec 64, ((fsp + 232#64) ↦₆₄ w232)) ∗
      (∃∗ bs240 : { l : List (BitVec 8) // l.length = 328 }, ((fsp + 240#64) ↦ₛ bs240.val)) ∗
      memRegion (fsp + 568#64) 8 ∗ (∃∗ q576 : BitVec 128, ((fsp + 576#64) ↦₁₂₈ q576)) ∗
      ((∃∗ w592 : BitVec 64, ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592)) ∗ memRegion (fsp + 599#64) 9) ∗
      (∃∗ q608 : BitVec 128, ((fsp + 608#64) ↦₁₂₈ q608)) ∗ (∃∗ q624 : BitVec 128, ((fsp + 624#64) ↦₁₂₈ q624)) ∗
      (∃∗ q640 : BitVec 128, ((fsp + 640#64) ↦₁₂₈ q640)) ∗ (∃∗ q656 : BitVec 128, ((fsp + 656#64) ↦₁₂₈ q656)) ∗
      (∃∗ q672 : BitVec 128, ((fsp + 672#64) ↦₁₂₈ q672)) ∗ (∃∗ q688 : BitVec 128, ((fsp + 688#64) ↦₁₂₈ q688)) ∗
      (∃∗ q704 : BitVec 128, ((fsp + 704#64) ↦₁₂₈ q704)) ∗ (∃∗ q720 : BitVec 128, ((fsp + 720#64) ↦₁₂₈ q720)) ∗
      (∃∗ q736 : BitVec 128, ((fsp + 736#64) ↦₁₂₈ q736)) ∗ (∃∗ q752 : BitVec 128, ((fsp + 752#64) ↦₁₂₈ q752)) ∗
      (∃∗ q768 : BitVec 128, ((fsp + 768#64) ↦₁₂₈ q768)) ∗ (∃∗ q784 : BitVec 128, ((fsp + 784#64) ↦₁₂₈ q784)) ∗
      (∃∗ q800 : BitVec 128, ((fsp + 800#64) ↦₁₂₈ q800)) ∗ (∃∗ q816 : BitVec 128, ((fsp + 816#64) ↦₁₂₈ q816)) ∗
      (∃∗ w832 : BitVec 64, ((fsp + 832#64) ↦₆₄ w832)) ∗ memRegion (fsp + 840#64) 8 ∗
      (∃∗ q848 : BitVec 128, ((fsp + 848#64) ↦₁₂₈ q848)) ∗
      ((∃∗ w864 : BitVec 64, ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 w864)) ∗ memRegion (fsp + 871#64) 9) ∗
      (∃∗ w880 : BitVec 64, ((fsp + 880#64) ↦₆₄ w880)) ∗
      ((∃∗ w888 : BitVec 64, ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 w888)) ∗ memRegion (fsp + 895#64) 993) ∗
      (∃∗ q1888 : BitVec 128, ((fsp + 1888#64) ↦₁₂₈ q1888)) ∗
      (∃∗ q1904 : BitVec 128, ((fsp + 1904#64) ↦₁₂₈ q1904)) ∗
      (∃∗ w1920 : BitVec 64, ((fsp + 1920#64) ↦₆₄ w1920)) ∗ memRegion (fsp + 1928#64) 376 := by
  exact split_top <| split_step (Entails.refl _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (memRegion_328_entails_bs _) <|
    split_step (Entails.refl _) <| split_step (mem128_entails _) <|
    split_step (memRegion_loBytes7_gap_at fsp 592#64 599#64 8) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem64_entails _) <| split_step (Entails.refl _) <|
    split_step (mem128_entails _) <| split_step (memRegion_loBytes7_gap_at fsp 864#64 871#64 8) <|
    split_step (mem64_entails _) <| split_step (memRegion_loBytes7_gap_at fsp 888#64 895#64 992) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem64_entails _) <| Entails.refl _

theorem pull_alloc_pure (P1 P2 R : SepProp) (φ : Prop) :
    P1 ∗ P2 ∗ ⌜φ⌝ ∗ R = ⌜φ⌝ ∗ (P1 ∗ P2 ∗ R) := by ac_rfl

theorem vecU8Payload_of_nil (A : RustAlloc) :
    emp ⊢ vecU8Payload A (BitVec.ofNat 64 ([] : List (BitVec 8)).length) 1#64 [] := by
  unfold vecU8Payload
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.zero_mod,
    Nat.le_refl, true_and, ↓reduceIte]
  exact Entails.pure_right ⟨by decide, by decide⟩ (Entails.refl _)

theorem vecU8Payload_pos_unpack (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < bs.length) :
    vecU8Payload A cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64 ∧ cap ≠ 0#64⌝ ∗
      (A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
  unfold vecU8Payload
  apply Entails.pure_left; intro ⟨hle, hlt, hptr⟩
  have hcap : cap ≠ 0#64 := cap_ne_zero_of_pos hpos hle
  simp only [hcap, ↓reduceIte]
  exact Entails.pure_right ⟨hle, hlt, hptr, hcap⟩ (Entails.refl _)

theorem vecU8Payload_pos_dealloc (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hle : bs.length ≤ cap.toNat) (hlt : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0#64) (hcap : cap ≠ 0#64) :
    A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ⊢
    vecCapPtrDealloc A cap ptr := by
  refine Entails.trans ?_ (vecU8Payload_entails_dealloc A cap ptr bs)
  unfold vecU8Payload
  simp only [hcap, ↓reduceIte]
  exact Entails.pure_right ⟨hle, hlt, hptr⟩ (Entails.refl _)

theorem vecU8Payload_extract_len_lt63 (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Payload A cap ptr bs ⊢ ⌜bs.length < 2 ^ 63⌝ ∗ vecU8Payload A cap ptr bs := by
  unfold vecU8Payload
  apply Entails.pure_left; intro ⟨hle, hlt, hne⟩
  exact Entails.pure_right (Nat.lt_of_le_of_lt hle hlt)
    (Entails.pure_right ⟨hle, hlt, hne⟩ (Entails.refl _))

end CryptoVerification.SpqrV1.States.FromPb
