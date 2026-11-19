/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10a -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBase
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10c
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 10 (`Ct2Sampled`, `+1632`) — Top-Level Composition

Composes all Variant 10 (`InnerState.ct2Sampled`, jump-table offset `+1632`) error, cloning,
`<PolyEncoder>::from_pb`, and epilogue sub-steps into `states_from_pb_ct2Sampled_1632`.
-/

public section

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.Auth CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

theorem v10_pointsTo64_eq_loByte_hiBytes7 (a w : BitVec 64) :
    (a ↦₆₄ w) = (a ↦₈ loByte w) ∗ ((a + 1#64) ↦ₛ hiBytes7 w) := by
  rw [pointsTo64_eq_pointsToBytes a w]; have hcons : unpack64 w = loByte w :: hiBytes7 w := rfl
  rw [hcons, ProofLib.pointsToBytes_cons]

theorem v10_seven_words_entails_memRegion_56 (a w0 w8 w16 w24 w32 w40 w48 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) ∗ ((a + 24#64) ↦₆₄ w24) ∗
      ((a + 32#64) ↦₆₄ w32) ∗ ((a + 40#64) ↦₆₄ w40) ∗ ((a + 48#64) ↦₆₄ w48) ⊢ memRegion a 56 := by
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (ProofLib.pointsTo64_entails_memRegion (a + 48#64) w48))))))) ?_
  exact protoPolyEncoderHeaders_entails_memRegion_56 a w0 w8 w16 w24 w32 w40

theorem v10_protoPolynomialEncoderAt_relocate (A : RustAlloc) (pbA d : BitVec 64)
    (pb : ProtoPolynomialEncoder) :
    protoPolynomialEncoderAt A (pbA + 8#64) pb ⊢
      ∃∗ cap_pts : BitVec 64, ∃∗ ptr_pts : BitVec 64, ∃∗ cap_polys : BitVec 64,
      ∃∗ ptr_polys : BitVec 64, ∃∗ w56 : BitVec 64, ∃∗ P_enc_heap : SepProp,
        ⌜cap_pts.toNat < 2 ^ 63 ∧
          ((d ↦₆₄ cap_pts) ∗ ((d + 8#64) ↦₆₄ ptr_pts) ∗ ((d + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
           ((d + 24#64) ↦₆₄ cap_polys) ∗ ((d + 32#64) ↦₆₄ ptr_polys) ∗ ((d + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
           ((d + 48#64) ↦₆₄ w56) ∗ P_enc_heap ⊢ protoPolynomialEncoderAt A d pb)⌝ ∗
        ((pbA + 8#64) ↦₆₄ cap_pts) ∗ ((pbA + 16#64) ↦₆₄ ptr_pts) ∗ ((pbA + 24#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
        ((pbA + 32#64) ↦₆₄ cap_polys) ∗ ((pbA + 40#64) ↦₆₄ ptr_polys) ∗
        ((pbA + 48#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗ ((pbA + 56#64) ↦₆₄ w56) ∗ P_enc_heap := by
  conv =>
    lhs
    unfold protoPolynomialEncoderAt vecVecU8At vecOf Poly.vecHeaderBytes
      protoPolynomialEncoderPolysOff protoPolynomialEncoderIdxOff protoPolynomialEncoderPadOff protoPolynomialEncoderPadSize vecAt vecHeader
  rw [ProofLib.memRegion_four ((pbA + 8#64) + 52#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro hi32; apply Entails.sepExists_elim; intro cap_polys
  apply Entails.sepExists_elim; intro ptr_polys; apply Entails.sepExists_elim; intro cap_pts; apply Entails.sepExists_elim; intro ptr_pts
  have ha16 : (pbA + 8#64) + 8#64 = pbA + 16#64 := by bv_omega
  have ha24 : (pbA + 8#64) + 16#64 = pbA + 24#64 := by bv_omega
  have ha32 : (pbA + 8#64) + 24#64 = pbA + 32#64 := by bv_omega
  have ha40 : (pbA + 32#64) + 8#64 = pbA + 40#64 := by bv_omega
  have ha48 : (pbA + 32#64) + 16#64 = pbA + 48#64 := by bv_omega
  have ha56 : (pbA + 8#64) + 48#64 = pbA + 56#64 := by bv_omega
  have ha60 : (pbA + 8#64) + 52#64 = (pbA + 56#64) + 4#64 := by bv_omega
  rw [ha16, ha24, ha32, ha40, ha48, ha56, ha60, v10_pointsTo32_pair_eq_pointsTo64 (pbA + 56#64) pb.idx hi32]
  have hcap_extract :
      vecBuf A 24 8 (fun bs a => vecU8 A a bs) cap_pts ptr_pts pb.pts ⊢
        ⌜cap_pts.toNat < 2 ^ 63⌝ ∗ vecBuf A 24 8 (fun bs a => vecU8 A a bs) cap_pts ptr_pts pb.pts := by
    unfold vecBuf; apply Entails.pure_left; rintro ⟨hle, hlt24, hne⟩
    exact Entails.pure_right (by omega) (Entails.pure_right ⟨hle, hlt24, hne⟩ (Entails.refl _))
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hcap_extract)))) ?_
  simp only [sepConj_assoc]
  rw [show ((pbA + 8#64) ↦₆₄ cap_pts) ∗ ((pbA + 16#64) ↦₆₄ ptr_pts) ∗
        ((pbA + 24#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗ ⌜cap_pts.toNat < 2 ^ 63⌝ ∗
        vecBuf A 24 8 (fun bs a => vecU8 A a bs) cap_pts ptr_pts pb.pts ∗
        ((pbA + 32#64) ↦₆₄ cap_polys) ∗ ((pbA + 40#64) ↦₆₄ ptr_polys) ∗
        ((pbA + 48#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
        vecBuf A 24 8 (fun bs a => vecU8 A a bs) cap_polys ptr_polys pb.polys ∗
        ((pbA + 56#64) ↦₆₄ (hi32 ++ pb.idx)) =
      ⌜cap_pts.toNat < 2 ^ 63⌝ ∗
      (((pbA + 8#64) ↦₆₄ cap_pts) ∗ ((pbA + 16#64) ↦₆₄ ptr_pts) ∗
       ((pbA + 24#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗ ((pbA + 32#64) ↦₆₄ cap_polys) ∗
       ((pbA + 40#64) ↦₆₄ ptr_polys) ∗ ((pbA + 48#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
       ((pbA + 56#64) ↦₆₄ (hi32 ++ pb.idx)) ∗
       (vecBuf A 24 8 (fun bs a => vecU8 A a bs) cap_pts ptr_pts pb.pts ∗
        vecBuf A 24 8 (fun bs a => vecU8 A a bs) cap_polys ptr_polys pb.polys)) by ac_rfl]
  apply Entails.pure_left; intro hcap_lt
  refine Entails.sepExists_right cap_pts (Entails.sepExists_right ptr_pts
    (Entails.sepExists_right cap_polys (Entails.sepExists_right ptr_polys
      (Entails.sepExists_right (hi32 ++ pb.idx) (Entails.sepExists_right
        (vecBuf A 24 8 (fun bs a => vecU8 A a bs) cap_pts ptr_pts pb.pts ∗
         vecBuf A 24 8 (fun bs a => vecU8 A a bs) cap_polys ptr_polys pb.polys) ?_)))))
  refine Entails.pure_right ⟨hcap_lt, ?_⟩ (Entails.of_eq (by ac_rfl))
  unfold protoPolynomialEncoderAt vecVecU8At vecOf Poly.vecHeaderBytes
    protoPolynomialEncoderPolysOff protoPolynomialEncoderIdxOff protoPolynomialEncoderPadOff protoPolynomialEncoderPadSize vecAt vecHeader
  rw [ProofLib.memRegion_four (d + 52#64)]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Entails.sepExists_right hi32 (Entails.sepExists_right cap_polys
    (Entails.sepExists_right ptr_polys (Entails.sepExists_right cap_pts (Entails.sepExists_right ptr_pts ?_))))
  have hd32 : (d + 24#64) + 8#64 = d + 32#64 := by bv_omega
  have hd40 : (d + 24#64) + 16#64 = d + 40#64 := by bv_omega
  have hd52 : d + 52#64 = (d + 48#64) + 4#64 := by bv_omega
  rw [hd32, hd40, hd52, ← v10_pointsTo32_pair_eq_pointsTo64 (d + 48#64) pb.idx hi32]; exact Entails.of_eq (by ac_rfl)

/-! ## 3. Shared Prefix `+1632 -> +5728` for `s.uc = some { auth := some auth, epoch := ep }` -/

theorem v10_sepWPp_bind {prog : Program} {mid ret : BitVec 64} {s : State}
    {P : SepProp} {Q_mid Q Qp : State → SepProp → Prop}
    (h1 : SepWPp prog mid s P Q_mid Qp)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running → Q_mid sm Pm → SepWPp prog ret sm Pm Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL; obtain ⟨sm, hsteps1, hout1⟩ := h1 R hm hL
  rcases hout1 with ⟨hpcm, hrunm, Pm, hmm, hqm⟩ | hpan
  · obtain ⟨sf, hsteps2, hout2⟩ := h2 sm Pm hpcm hrunm hqm R hmm (hsteps1.codeLoaded hL)
    exact ⟨sf, hsteps1.trans hsteps2, hout2⟩
  · exact ⟨sm, hsteps1, Or.inr hpan⟩

theorem v10_authPBPinnedAt_64_eq_full (A : RustAlloc) (ga : AuthenticatorPBGhost)
    (pbA : BitVec 64) (auth : ProtoAuthenticator) :
    authenticatorPBPinnedAt A ga (pbA + 64#64) auth =
      ((pbA + 64#64) ↦₆₄ ga.rootKey.cap) ∗ ((pbA + 72#64) ↦₆₄ ga.rootKey.ptr) ∗
      ((pbA + 80#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
      ((pbA + 88#64) ↦₆₄ ga.macKey.cap) ∗ ((pbA + 96#64) ↦₆₄ ga.macKey.ptr) ∗
      ((pbA + 104#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
      vecU8Payload A ga.rootKey.cap ga.rootKey.ptr auth.rootKey ∗
      vecU8Payload A ga.macKey.cap ga.macKey.ptr auth.macKey := by
  unfold authenticatorPBPinnedAt vecU8At vecHeader vecU8Payload
  have h72 : (pbA + 64#64) + 8#64 = pbA + 72#64 := by bv_omega
  have h80 : (pbA + 64#64) + 16#64 = pbA + 80#64 := by bv_omega
  have h88 : (pbA + 64#64) + 24#64 = pbA + 88#64 := by bv_omega
  have h96 : (pbA + 88#64) + 8#64 = pbA + 96#64 := by bv_omega
  have h104 : (pbA + 88#64) + 16#64 = pbA + 104#64 := by bv_omega
  rw [h72, h80, h88, h96, h104]; ac_rfl

theorem v10_vecU8Payload_extract_bounds (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Payload A cap ptr bs ⊢
      ⌜cap.toNat < 2 ^ 63 ∧ (BitVec.ofNat 64 bs.length).toNat < 2 ^ 63⌝ ∗ vecU8Payload A cap ptr bs := by
  unfold vecU8Payload; apply Entails.pure_left; rintro ⟨hle, hcap_lt, hptr⟩
  have hlen_lt63 : bs.length < 2 ^ 63 := Nat.lt_of_le_of_lt hle hcap_lt
  have hbv_lt63 : (BitVec.ofNat 64 bs.length).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hlen_lt63
  exact Entails.pure_right ⟨hcap_lt, hbv_lt63⟩ (Entails.pure_right ⟨hle, hcap_lt, hptr⟩ (Entails.refl _))

theorem v10_pbA_64_to_120_entails_56 (pbA c1 p1 l1 c2 p2 l2 ep : BitVec 64) :
    ((pbA + 64#64) ↦₆₄ c1) ∗ ((pbA + 72#64) ↦₆₄ p1) ∗ ((pbA + 80#64) ↦₆₄ l1) ∗
      ((pbA + 88#64) ↦₆₄ c2) ∗ ((pbA + 96#64) ↦₆₄ p2) ∗ ((pbA + 104#64) ↦₆₄ l2) ∗
      ((pbA + 112#64) ↦₆₄ ep) ⊢ memRegion (pbA + 64#64) 56 :=
  collapse_top <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| Drop.pointsTo64_entails_memRegion _ _

theorem v10_fsp_split_1632 (fsp : BitVec 64) :
    memRegion fsp 2304 ⊢
      memRegion fsp 152 ∗ (∃∗ v152 : BitVec 64, (fsp + 152#64) ↦₆₄ v152) ∗
      memRegion (fsp + 160#64) 24 ∗ (∃∗ v184 : BitVec 64, (fsp + 184#64) ↦₆₄ v184) ∗
      memRegion (fsp + 192#64) 8 ∗ (∃∗ v200 : BitVec 64, (fsp + 200#64) ↦₆₄ v200) ∗
      memRegion (fsp + 208#64) 16 ∗ (∃∗ v224 : BitVec 32, (fsp + 224#64) ↦₃₂ v224) ∗
      (∃∗ v228 : BitVec 32, (fsp + 228#64) ↦₃₂ v228) ∗
      (∃∗ v232 : BitVec 64, (fsp + 232#64) ↦₆₄ v232) ∗ memRegion (fsp + 240#64) 2064 :=
  split_top <| split_step0 (Entails.refl _) <| split_step (mem64_entails _) <|
    split_step (Entails.refl _) <| split_step (mem64_entails _) <|
    split_step (Entails.refl _) <| split_step (mem64_entails _) <|
    split_step (Entails.refl _) <| split_step (mem32_entails _) <|
    split_step (mem32_entails _) <| split_step (mem64_entails _) <| Entails.refl _

theorem v10_fsp_unsplit_1632 (fsp v152 v184 v200 v232 : BitVec 64) (v224 v228 : BitVec 32) :
    memRegion fsp 152 ∗ ((fsp + 152#64) ↦₆₄ v152) ∗ memRegion (fsp + 160#64) 24 ∗
      ((fsp + 184#64) ↦₆₄ v184) ∗ memRegion (fsp + 192#64) 8 ∗ ((fsp + 200#64) ↦₆₄ v200) ∗
      memRegion (fsp + 208#64) 16 ∗ ((fsp + 224#64) ↦₃₂ v224) ∗ ((fsp + 228#64) ↦₃₂ v228) ∗
      ((fsp + 232#64) ↦₆₄ v232) ∗ memRegion (fsp + 240#64) 2064 ⊢ memRegion fsp 2304 :=
  collapse_top <| collapse_step0 (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Entails.refl _) <|
    collapse_step (pointsTo32_entails_memRegion_4 _ _) <|
    collapse_step (pointsTo32_entails_memRegion_4 _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| Entails.refl _

theorem v10_pbA_none_some_entails_224 (pbA : BitVec 64) (b16 : BitVec 8) :
    (pbA ↦₆₄ 0x800000000000000a#64) ∗ ((pbA + 8#64) ↦₆₄ noneCap) ∗ ((pbA + 16#64) ↦₈ b16) ∗
      memRegion (pbA + 17#64) 47 ∗ memRegion (pbA + 64#64) 56 ∗ memRegion (pbA + 120#64) 104 ⊢
      memRegion pbA optProtoInnerStateSize :=
  collapse_top <| collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (pointsTo8_entails_memRegion _ _) <| collapse_step (Entails.refl _) <|
    collapse_step (Entails.refl _) <| Entails.refl _

theorem v10_pbA_some_some_entails_224 (pbA w8 w16 w24 w32 w40 w48 w56 : BitVec 64) :
    (pbA ↦₆₄ 0x800000000000000a#64) ∗ ((pbA + 8#64) ↦₆₄ w8) ∗ ((pbA + 16#64) ↦₆₄ w16) ∗
      ((pbA + 24#64) ↦₆₄ w24) ∗ ((pbA + 32#64) ↦₆₄ w32) ∗ ((pbA + 40#64) ↦₆₄ w40) ∗
      ((pbA + 48#64) ↦₆₄ w48) ∗ ((pbA + 56#64) ↦₆₄ w56) ∗
      memRegion (pbA + 64#64) 56 ∗ memRegion (pbA + 120#64) 104 ⊢
      memRegion pbA optProtoInnerStateSize :=
  collapse_top <| collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Entails.refl _) <| Entails.refl _

theorem v10_memRegion_15_entails_8_loBytes7 (a : BitVec 64) :
    memRegion a 15 ⊢
      (∃∗ u0 : BitVec 64, a ↦₆₄ u0) ∗ (∃∗ u7 : BitVec 64, (a + 8#64) ↦ₛ EncoderFromPb.loBytes7 u7) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 7) (k := 8) (b' := a + 7#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans (sepConj_mono_right (mem64_entails (a + 7#64))) ?_
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro w7
  rw [v10_pointsTo64_eq_loByte_hiBytes7 (a + 7#64) w7, v10_hiBytes7_eq_loBytes7_lsr8 w7]
  have ha8 : (a + 7#64) + 1#64 = a + 8#64 := by bv_omega
  rw [ha8, ← sepConj_assoc]
  have h8 : memRegion a 7 ∗ ((a + 7#64) ↦₈ loByte w7) ⊢ ∃∗ u0 : BitVec 64, a ↦₆₄ u0 := by
    refine Entails.trans (sepConj_mono_right (pointsTo8_entails_memRegion (a + 7#64) (loByte w7))) ?_
    rw [← ProofLib.memRegion_split' (b := a) (n := 7) (k := 1) (b' := a + 7#64) rfl (by bv_omega) (by decide)]
    exact mem64_entails a
  exact sepConj_mono h8 (Entails.sepExists_right (w7 >>> 8) (Entails.refl _))

theorem v10_fsp_240_split_5728 (fsp : BitVec 64) :
    memRegion (fsp + 240#64) 2064 ⊢
      memRegion (fsp + 240#64) 1152 ∗ (∃∗ u1392 : BitVec 64, (fsp + 1392#64) ↦₆₄ u1392) ∗
      (∃∗ b1400 : BitVec 8, (fsp + 1400#64) ↦₈ b1400) ∗ (∃∗ u1401 : BitVec 64, (fsp + 1401#64) ↦₆₄ u1401) ∗
      ((∃∗ u1409 : BitVec 64, (fsp + 1409#64) ↦₆₄ u1409) ∗
       (∃∗ u1417 : BitVec 64, (fsp + 1417#64) ↦ₛ EncoderFromPb.loBytes7 u1417)) ∗
      (∃∗ u1424 : BitVec 64, (fsp + 1424#64) ↦₆₄ u1424) ∗ (∃∗ u1432 : BitVec 64, (fsp + 1432#64) ↦₆₄ u1432) ∗
      (∃∗ u1440 : BitVec 64, (fsp + 1440#64) ↦₆₄ u1440) ∗
      memRegion (fsp + 1448#64) 440 ∗ memRegion (fsp + 1888#64) 400 ∗ memRegion (fsp + 2288#64) 16 := by
  have h1 : memRegion (fsp + 1400#64) 1 ⊢ ∃∗ b1400 : BitVec 8, (fsp + 1400#64) ↦₈ b1400 := by
    rw [ProofLib.memRegion_one]; exact Entails.refl _
  have h15 : memRegion (fsp + 1409#64) 15 ⊢
      (∃∗ u1409 : BitVec 64, (fsp + 1409#64) ↦₆₄ u1409) ∗
      (∃∗ u1417 : BitVec 64, (fsp + 1417#64) ↦ₛ EncoderFromPb.loBytes7 u1417) := by
    have h := v10_memRegion_15_entails_8_loBytes7 (fsp + 1409#64)
    have ha1417 : (fsp + 1409#64) + 8#64 = fsp + 1417#64 := by bv_omega
    rwa [ha1417] at h
  exact split_top <| split_step (Entails.refl _) <| split_step (mem64_entails _) <|
    split_step h1 <| split_step (mem64_entails _) <| split_step h15 <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (Entails.refl _) <| split_step (Entails.refl _) <| Entails.refl _

theorem v10_fsp_240_merge_1648 (fsp : BitVec 64) :
    memRegion (fsp + 240#64) 1152 ∗ memRegion (fsp + 1392#64) 56 ∗ memRegion (fsp + 1448#64) 440 ⊢
      memRegion (fsp + 240#64) 1648 :=
  collapse_top <| collapse_step (Entails.refl _) <| collapse_step (Entails.refl _) <| Entails.refl _

theorem v10_fsp_5808_err_entails_2064 (fsp : BitVec 64) :
    memRegion (fsp + 240#64) 1648 ∗ ((fsp + 1888#64) ↦₆₄ 2#64) ∗
      memRegion (fsp + 1896#64) 392 ∗ memRegion (fsp + 2288#64) 16 ⊢
      memRegion (fsp + 240#64) 2064 :=
  collapse_top <| collapse_step (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Entails.refl _) <| Entails.refl _

/-! ## 5. `+1632 -> s0.x30` when `sendingCt2 = none` and `uc = some { auth := some auth, epoch := ep }` -/

@[simp]
theorem v10_states_from_pb_ct2Sampled_sending_none (F : ShaCompress)
    (auth : ProtoAuthenticator) (ep : BitVec 64) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.ct2Sampled
          { sendingCt2 := none, uc := some { auth := some auth, epoch := ep } }) } =
      .error (.err .stateDecode) := rfl

theorem v10_sepWPp_entails_to_satisfies {prog : Program} {ret : BitVec 64} {s : State}
    {P R : SepProp} {Q : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q (fun sf Pf => Pf ⊢ statesFromPbOnPanic s sf)) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s sf ∗ R)) := by
  intro R' hm hL; obtain ⟨sf, hsteps, hout⟩ := h R' hm hL
  rcases hout with hok | ⟨hst, Pf, hmf, hPf⟩ | hoom
  · exact ⟨sf, hsteps, Or.inl hok⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hst, Pf, hmf, fun hmR => Satisfies.mono (sepConj_mono_left hPf) hmR⟩)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

/-! ## 6. `+1632 -> s0.x30` when `sendingCt2 = some encPb` and `uc = some { auth := some auth, epoch := ep }` -/

theorem v10_sepWPp_call_ret_entails {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α} (hcall : subroutine_ok prog entry spec)
    {x : α} {s : State} {P_step F : SepProp} {Qpan : State → SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (hpre : P_step ⊢ spec.pre x s)
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf) (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp →
      CalleeSavedPreserved s sf → SepWP prog target_pc sf (spec.post x s sf ∗ F) post)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog target_pc s (P_step ∗ F) post (fun sf P_f => P_f ⊢ Qpan sf) :=
  SepWPp.call (x := x) (F := F) hcall hpc hrun hsp_align hlr
    (fun R' hm => by rw [sepConj_assoc] at hm; exact Satisfies.mono (sepConj_mono_left hpre) hm)
    (fun sf code R' _ hm => by rw [hexit_eq] at hm; exact not_satisfies_false_sepConj hm)
    (hoom := fun sf R' _ hm => by rw [hoom_eq] at hm; exact False.elim (not_satisfies_false_sepConj hm))
    (fun sf _ => hpan sf) (fun sf hpcf hrunf hspf hcsf => SepWPp.of_sepWP_ret (hnext sf hpcf hrunf hspf hcsf))

theorem v10_states_from_pb_ct2Sampled_sending_some_err (F : ShaCompress)
    (encPb : PolynomialEncoderPB) (auth : ProtoAuthenticator) (ep : BitVec 64)
    (err : PolynomialError) (hres : fromPbResult (pbToProtoPolyEncoder encPb) = .error err) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.ct2Sampled { sendingCt2 := some encPb, uc := some { auth := some auth, epoch := ep } }) } =
      .error (.err .stateDecode) := by
  simp only [States.from_pb, Chunked.SendCt.Ct2Sampled.from_pb, Unchunked.SendCt.Ct2Sent.from_pb,
    encoderFromPbStateDecode_some, hres, Bind.bind, Except.bind, Functor.map, Except.map]

theorem v10_states_from_pb_ct2Sampled_sending_some_ok (F : ShaCompress)
    (encPb : PolynomialEncoderPB) (auth : ProtoAuthenticator) (ep : BitVec 64)
    (enc : PolyEncoder) (hres : fromPbResult (pbToProtoPolyEncoder encPb) = .ok enc) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.ct2Sampled { sendingCt2 := some encPb, uc := some { auth := some auth, epoch := ep } }) } =
      .ok (.ct2Sampled { uc := { auth := { rootKey := auth.rootKey, macKey := auth.macKey }, epoch := ep }, sending_ct2 := enc }) := by
  simp only [States.from_pb, Chunked.SendCt.Ct2Sampled.from_pb, Unchunked.SendCt.Ct2Sent.from_pb,
    encoderFromPbStateDecode_some, hres, Bind.bind, Except.bind, Functor.map, Except.map]; rfl

end CryptoVerification.SpqrV1.States.FromPb

