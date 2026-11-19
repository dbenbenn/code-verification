/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5a -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5c
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 5 (`NoHeaderReceived`, `+1344`) — Part D

Stack-region splitting helpers, error cleanup paths from `+6420`, `+1396`, and `+6520`, and
`Authenticator` key-buffer cloning (`+3744 -> +6064`) for Variant 5 (`InnerState.noHeaderReceived`).
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

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff /-! ## 1. `SepWPp` & Stack Region Splitting/Joining Helpers (`v5_*`) -/
theorem v5_sepWPp_seq {prog : Program} {mid ret : BitVec 64} {s : State}
    {P : SepProp} {Q_mid Q Qp : State → SepProp → Prop}
    (h1 : SepWPp prog mid s P Q_mid Qp)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running → Q_mid sm Pm →
      SepWPp prog ret sm Pm Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps1, ⟨hpcm, hrunm, Pm, hmm, hqm⟩ | hpan⟩ := h1 R hm hL
  · obtain ⟨sf, hsteps2, hout⟩ := h2 sm Pm hpcm hrunm hqm R hmm (hsteps1.codeLoaded hL)
    exact ⟨sf, hsteps1.trans hsteps2, hout⟩
  · exact ⟨sm, hsteps1, Or.inr hpan⟩

theorem v5_memRegion_224_split_auth (fsp : BitVec 64) :
    memRegion fsp 224 ⊢
      memRegion fsp 136 ∗ (∃∗ z136 : BitVec 64, (fsp + 136#64) ↦₆₄ z136) ∗
      memRegion (fsp + 144#64) 8 ∗ (∃∗ z152 : BitVec 64, (fsp + 152#64) ↦₆₄ z152) ∗
      memRegion (fsp + 160#64) 40 ∗ (∃∗ z200 : BitVec 64, (fsp + 200#64) ↦₆₄ z200) ∗
      (∃∗ z208 : BitVec 64, (fsp + 208#64) ↦₆₄ z208) ∗
      (∃∗ z216 : BitVec 64, (fsp + 216#64) ↦₆₄ z216) := by
  exact split_top <| split_step0 (Entails.refl _) <| split_step (mem64_entails _) <|
    split_step (Entails.refl _) <| split_step (mem64_entails _) <|
    split_step (Entails.refl _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| mem64_entails _

theorem v5_memRegion_224_join_auth (fsp w136 w152 w200 w208 w216 : BitVec 64) :
    memRegion fsp 136 ∗ ((fsp + 136#64) ↦₆₄ w136) ∗
      memRegion (fsp + 144#64) 8 ∗ ((fsp + 152#64) ↦₆₄ w152) ∗
      memRegion (fsp + 160#64) 40 ∗ ((fsp + 200#64) ↦₆₄ w200) ∗
      ((fsp + 208#64) ↦₆₄ w208) ∗ ((fsp + 216#64) ↦₆₄ w216) ⊢
      memRegion fsp 224 := by
  exact collapse_top <| collapse_step0 (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    Drop.pointsTo64_entails_memRegion _ _

theorem v5_memRegion_2068_split_dec (fsp : BitVec 64) :
    memRegion (fsp + 236#64) 2068 ⊢
      (∃∗ z236 : BitVec 32, (fsp + 236#64) ↦₃₂ z236) ∗
      memRegion (fsp + 240#64) 1152 ∗ memRegion (fsp + 1392#64) 40 ∗
      memRegion (fsp + 1432#64) 456 ∗ memRegion (fsp + 1888#64) 400 ∗
      memRegion (fsp + 2288#64) 16 := by
  exact split_top <| split_step (mem32_entails _) <| split_step (Entails.refl _) <|
    split_step (Entails.refl _) <| split_step (Entails.refl _) <|
    split_step (Entails.refl _) <| Entails.refl _

theorem v5_memRegion_240_merge_1648 (fsp : BitVec 64) :
    memRegion (fsp + 240#64) 1152 ∗ memRegion (fsp + 1392#64) 40 ∗
      memRegion (fsp + 1432#64) 456 ⊢ memRegion (fsp + 240#64) 1648 := by
  exact collapse_top <| collapse_step (Entails.refl _) <|
    collapse_step (Entails.refl _) <| Entails.refl _

theorem v5_memRegion_160_merge_48 (fsp w200 : BitVec 64) :
    memRegion (fsp + 160#64) 40 ∗ ((fsp + 200#64) ↦₆₄ w200) ⊢ memRegion (fsp + 160#64) 48 := by
  exact collapse_top <| collapse_step (Entails.refl _) <| Drop.pointsTo64_entails_memRegion _ _

theorem v5_memRegion_2068_join_err (fsp : BitVec 64) (z236 : BitVec 32) (w1888 : BitVec 64) :
    ((fsp + 236#64) ↦₃₂ z236) ∗ memRegion (fsp + 240#64) 1648 ∗
      ((fsp + 1888#64) ↦₆₄ w1888) ∗ memRegion (fsp + 1896#64) 392 ∗
      memRegion (fsp + 2288#64) 16 ⊢ memRegion (fsp + 236#64) 2068 := by
  exact collapse_top <| collapse_step (pointsTo32_entails_memRegion_4 _ _) <|
    collapse_step (Entails.refl _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Entails.refl _) <| Entails.refl _

theorem v5_vecU8Heap_dup_bounds (A : RustAlloc) (bs : List (BitVec 8))
    (cap ptr len : BitVec 64) :
    v5a_vecU8Heap A bs cap ptr len ⊢
      ⌜len = BitVec.ofNat 64 bs.length ∧ bs.length < 2 ^ 63 ∧ cap.toNat < 2 ^ 63⌝ ∗
      vecU8Payload A cap ptr bs := by
  unfold v5a_vecU8Heap vecU8Payload
  apply Entails.pure_left; intro hlen
  apply Entails.pure_left; rintro ⟨hle, hcap, hp⟩
  exact Entails.pure_right ⟨hlen, Nat.lt_of_le_of_lt hle hcap, hcap⟩
    (Entails.pure_right ⟨hle, hcap, hp⟩ (Entails.refl _))

theorem v5_optProtoPolyDecoderHeap_none_dup (A : RustAlloc)
    (w8 w16 w24 : BitVec 64) (d32 d36 : BitVec 32) (w40 : BitVec 64) :
    v5a_optProtoPolyDecoderHeap A none w8 w16 w24 d32 d36 w40 ⊢
      ⌜w8 = noneCap⌝ ∗ v5a_optProtoPolyDecoderHeap A none w8 w16 w24 d32 d36 w40 := by
  dsimp only [v5a_optProtoPolyDecoderHeap]
  by_cases h : w8 = noneCap
  · exact Entails.pure_right h (Entails.refl _)
  · exact Entails.trans (Entails.of_eq (sepConj_emp _).symm)
      (Entails.pure_left fun hw8 => absurd hw8 h)

theorem v5_optProtoPolyDecoderHeap_some_dup (A : RustAlloc) (pb : ProtoPolynomialDecoder)
    (w8 w16 w24 : BitVec 64) (d32 d36 : BitVec 32) (w40 : BitVec 64) :
    v5a_optProtoPolyDecoderHeap A (some pb) w8 w16 w24 d32 d36 w40 ⊢
      ⌜d32 = pb.ptsNeeded ∧ w8.toNat < 2 ^ 63⌝ ∗
      v5a_optProtoPolyDecoderHeap A (some pb) w8 w16 w24 d32 d36 w40 := by
  dsimp only [v5a_optProtoPolyDecoderHeap]
  apply Entails.pure_left; rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
  exact Entails.pure_right ⟨h2, by omega⟩
    (Entails.pure_right ⟨h1, h2, h3, h4, h5, h6, h7⟩ (Entails.refl _))

/-! ## 2. Error Paths from `+6420`, `+1396`, and `+6520` (`-> s0.x30`) -/

end CryptoVerification.SpqrV1.States.FromPb
