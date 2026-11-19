/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3c -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3d
import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbEk
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 3 (`Ct1Received`, `+692`)

Top-level composition and `subroutine_ok` contract for `InnerState.ct1Received`.
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
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

theorem v3_stackAt_encoder_split_ekSent (sp : BitVec 64) :
    stackAt sp encoderFromPbStack =
      stackAt sp ekSentCt1ReceivedFromPbStack ∗ memRegion (sp - 5152#64) 848 := by
  change memRegion (sp - 5152#64) (848 + 4304) =
    memRegion (sp - 4304#64) 4304 ∗ memRegion (sp - 5152#64) 848
  rw [ProofLib.memRegion_split (sp - 5152#64) 848 4304 (by decide)]
  have h2 : (sp - 5152#64) + BitVec.ofNat 64 848 = sp - 4304#64 := by bv_omega
  rw [h2]
  ac_rfl

theorem v3_ekSentCt1ReceivedAt_eq_unchunked (A : RustAlloc) {F : ShaCompress}
    (a : BitVec 64) (st : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F)) :
    ekSentCt1ReceivedAt A (F := F) a st = unchunkedEkSentCt1ReceivedAt A (F := F) a st := rfl

theorem v3_collapse_1552_752_err (fsp w1896 w1904 w1912 : BitVec 64) :
    memRegion (fsp + 1552#64) 336 ∗
      ((fsp + 1888#64) ↦₆₄ noneCap) ∗ ((fsp + 1896#64) ↦₆₄ w1896) ∗
      ((fsp + 1904#64) ↦₆₄ w1904) ∗ ((fsp + 1912#64) ↦₆₄ w1912) ∗
      memRegion (fsp + 1920#64) 72 ∗ memRegion (fsp + 1992#64) 312 ⊢
      memRegion (fsp + 1552#64) 752 :=
  collapse_top <| collapse_step (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Entails.refl _) <| Entails.refl _

theorem v3_split_1496_none (fsp : BitVec 64) :
    memRegion fsp 1496 ⊢
      memRegion fsp 176 ∗
      (∃∗ v176 : BitVec 64, ((fsp + 176#64) ↦₆₄ v176)) ∗
      memRegion (fsp + 184#64) 40 ∗
      (∃∗ v224 : BitVec 64, ((fsp + 224#64) ↦₆₄ v224)) ∗
      memRegion (fsp + 232#64) 1264 :=
  split_top <| split_step0 (Entails.refl _) <| split_step (mem64_entails _) <|
    split_step (Entails.refl _) <| split_step (mem64_entails _) <| Entails.refl _

theorem v3_collapse_232_2072_none
    (fsp w0 w8 w16 w24 w32 w40 w48 ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep : BitVec 64) :
    memRegion (fsp + 232#64) 1264 ∗
      v1_optProtoPolyEncoderWordsAt (fsp + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
      memRegion (fsp + 1552#64) 336 ∗
      v1_ucWordsAt (fsp + 1888#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
      memRegion (fsp + 1992#64) 312 ⊢
      memRegion (fsp + 232#64) 2072 := by
  have h56 := v1_optProtoPolyEncoderWordsAt_entails_56 (fsp + 1496#64) w0 w8 w16 w24 w32 w40 w48
  have h104 := v1_ucWordsAt_entails_104 (fsp + 1888#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep
  exact collapse_top <| collapse_step (Entails.refl _) <|
    collapse_step h56 <| collapse_step (Entails.refl _) <|
    collapse_step h104 <| Entails.refl _

theorem v3_split_1496_some (fsp : BitVec 64) :
    memRegion fsp 1496 ⊢
      memRegion fsp 64 ∗
      (∃∗ v64 : BitVec 64, ((fsp + 64#64) ↦₆₄ v64)) ∗
      memRegion (fsp + 72#64) 24 ∗
      (∃∗ v96 : BitVec 64, ((fsp + 96#64) ↦₆₄ v96)) ∗
      memRegion (fsp + 104#64) 72 ∗
      (∃∗ v176 : BitVec 64, ((fsp + 176#64) ↦₆₄ v176)) ∗
      (∃∗ v184 : BitVec 64, ((fsp + 184#64) ↦₆₄ v184)) ∗
      (∃∗ v192 : BitVec 64, ((fsp + 192#64) ↦₆₄ v192)) ∗
      (∃∗ v200 : BitVec 64, ((fsp + 200#64) ↦₆₄ v200)) ∗
      memRegion (fsp + 208#64) 16 ∗
      (∃∗ v224 : BitVec 64, ((fsp + 224#64) ↦₆₄ v224)) ∗
      memRegion (fsp + 232#64) 8 ∗
      (∃∗ e0 : BitVec 64, ∃∗ e8 : BitVec 64, ∃∗ e16 : BitVec 64, ∃∗ e24 : BitVec 64,
       ∃∗ e32 : BitVec 64, ∃∗ e40 : BitVec 64, ∃∗ e48 : BitVec 64,
         v1_optProtoPolyEncoderWordsAt (fsp + 240#64) e0 e8 e16 e24 e32 e40 e48) ∗
      memRegion (fsp + 296#64) 1096 ∗
      memRegion (fsp + 1392#64) 104 :=
  split_top <| split_step0 (Entails.refl _) <| split_step (mem64_entails _) <|
    split_step (Entails.refl _) <| split_step (mem64_entails _) <|
    split_step (Entails.refl _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (Entails.refl _) <|
    split_step (mem64_entails _) <| split_step (Entails.refl _) <|
    split_step (v3cr_memRegion_56_entails_encWordsAt _) <|
    split_step (Entails.refl _) <| Entails.refl _

theorem v3_split_2304_692 (fsp : BitVec 64) :
    memRegion fsp 2304 ⊢
      memRegion fsp 1392 ∗
      (∃∗ d8 : BitVec 64, ∃∗ d16 : BitVec 64, ∃∗ d24 : BitVec 64, ∃∗ d32 : BitVec 64,
       ∃∗ d40 : BitVec 64, ∃∗ d48 : BitVec 64, ∃∗ d56 : BitVec 64, ∃∗ d64 : BitVec 64,
       ∃∗ d72 : BitVec 64, ∃∗ d80 : BitVec 64, ∃∗ d88 : BitVec 64, ∃∗ d96 : BitVec 64,
       ∃∗ d104 : BitVec 64,
         v1_ucWordsAt (fsp + 1392#64) d8 d16 d24 d32 d40 d48 d56 d64 d72 d80 d88 d96 d104) ∗
      (∃∗ e0 : BitVec 64, ∃∗ e8 : BitVec 64, ∃∗ e16 : BitVec 64,
       ∃∗ e24 : BitVec 64, ∃∗ e32 : BitVec 64, ∃∗ e40 : BitVec 64, ∃∗ e48 : BitVec 64,
         v1_optProtoPolyEncoderWordsAt (fsp + 1496#64) e0 e8 e16 e24 e32 e40 e48) ∗
      memRegion (fsp + 1552#64) 752 :=
  split_top <|
    split_step0 (Entails.refl _) <|
    split_step (v3cr_memRegion_104_entails_ucWordsAt (fsp + 1392#64)) <|
    split_step (v3cr_memRegion_56_entails_encWordsAt (fsp + 1496#64)) <|
    Entails.refl _

theorem v3_split_1392_896 (fsp : BitVec 64) :
    memRegion fsp 1392 ⊢
      memRegion fsp 896 ∗
      (∃∗ c8 : BitVec 64, ∃∗ c16 : BitVec 64, ∃∗ c24 : BitVec 64, ∃∗ c32 : BitVec 64,
       ∃∗ c40 : BitVec 64, ∃∗ c48 : BitVec 64, ∃∗ c56 : BitVec 64, ∃∗ c64 : BitVec 64,
       ∃∗ c72 : BitVec 64, ∃∗ c80 : BitVec 64, ∃∗ c88 : BitVec 64, ∃∗ c96 : BitVec 64,
       ∃∗ c104 : BitVec 64,
         v1_ucWordsAt (fsp + 896#64) c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104) ∗
      memRegion (fsp + 1000#64) 392 :=
  split_top <|
    split_step0 (Entails.refl _) <|
    split_step (v3cr_memRegion_104_entails_ucWordsAt (fsp + 896#64)) <|
    Entails.refl _

theorem v3_split_752_1888 (fsp : BitVec 64) :
    memRegion (fsp + 1552#64) 752 ⊢
      memRegion (fsp + 1552#64) 336 ∗
      memRegion (fsp + 1888#64) 104 ∗
      memRegion (fsp + 1992#64) 312 :=
  split_top <|
    split_step (Entails.refl _) <|
    split_step (Entails.refl _) <|
    Entails.refl _

theorem v3_collapse_1392_ucWords_1496 (fsp u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 : BitVec 64) :
    memRegion fsp 1392 ∗
      v1_ucWordsAt (fsp + 1392#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ⊢
      memRegion fsp 1496 :=
  collapse_top <|
    collapse_step0 (Entails.refl _) <|
    v1_ucWordsAt_entails_104 (fsp + 1392#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104

theorem v3_collapse_896_104_392_ucWords_1496
    (fsp u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 : BitVec 64) :
    memRegion fsp 896 ∗
      memRegion (fsp + 896#64) 104 ∗
      memRegion (fsp + 1000#64) 392 ∗
      v1_ucWordsAt (fsp + 1392#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ⊢
      memRegion fsp 1496 :=
  collapse_top <|
    collapse_step0 (Entails.refl _) <|
    collapse_step (Entails.refl _) <|
    collapse_step (Entails.refl _) <|
    v1_ucWordsAt_entails_104 (fsp + 1392#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104

theorem v3_optProtoUcHeap_some_cap_lt (A : RustAlloc) (u : V1State.Unchunked.EkSentCt1Received)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 : BitVec 64) :
    v3cr_optProtoUcHeap A (some u) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ⊢
      ⌜u8.toNat < 2 ^ 63⌝ ∗
      v3cr_optProtoUcHeap A (some u) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 := by
  dsimp only [v3cr_optProtoUcHeap]
  apply Entails.pure_left
  rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
  exact Entails.pure_right h2 (Entails.pure_right ⟨h1, h2, h3, h4, h5, h6, h7⟩ (Entails.refl _))

theorem v3_collapse_pbA_tag_ucWords_112
    (pbA tag u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 : BitVec 64) :
    (pbA ↦₆₄ tag) ∗
      v1_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ⊢
      memRegion pbA 112 :=
  collapse_top <|
    collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
    v1_ucWordsAt_entails_104 (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104

end CryptoVerification.SpqrV1.States.FromPb
