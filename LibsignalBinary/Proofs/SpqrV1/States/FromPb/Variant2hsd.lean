/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Drop.PolyEncoder -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsc
import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBase
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 2 (`HeaderSent`, `+508`) — Part D

Cleanup blocks (`+9132`, `+9112`, `+11024`, `+11240 -> +9212/+9228`) for `InnerState.headerSent`.
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
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append



@[local simp, local arm64_norm, local wp_norm]
theorem v2hsd_bv_add_add_lit (x : BitVec 64) (a b : Nat) :
    x + BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by
  bv_omega

/-! ## Subroutine Call Bridges -/

private theorem v2hsd_add_11028_sub_68860_eq (x : BitVec 64) :
    x + 11028#64 + 18446744073709482756#64 = x - 57832#64 := by bv_omega

private theorem v2hsd_add_11244_sub_67264_eq (x : BitVec 64) :
    x + 11244#64 + 18446744073709484352#64 = x - 56020#64 := by bv_omega

private theorem v2hsd_add_11252_sub_66164_eq (x : BitVec 64) :
    x + 11252#64 + 18446744073709485452#64 = x - 54912#64 := by bv_omega

theorem v2hsd_stackAt_encoderFromPbStack_to_dropStack32 (fsp : BitVec 64) :
    stackAt fsp encoderFromPbStack ⊢
      stackAt fsp dropStack32 ∗ memRegion (fsp - 5152#64) 1024 := by
  have h := ProofLib.stackAt_split_bottom fsp dropStack32 1024 (by decide)
  change stackAt fsp encoderFromPbStack =
    memRegion (fsp - 5152#64) 1024 ∗ stackAt fsp dropStack32 at h
  rw [h]
  exact Entails.of_eq (by ac_rfl)

theorem v2hsd_stackAt_dropStack32_to_encoderFromPbStack (fsp : BitVec 64) :
    stackAt fsp dropStack32 ∗ memRegion (fsp - 5152#64) 1024 ⊢
      stackAt fsp encoderFromPbStack := by
  have h := ProofLib.stackAt_split_bottom fsp dropStack32 1024 (by decide)
  change stackAt fsp encoderFromPbStack =
    memRegion (fsp - 5152#64) 1024 ∗ stackAt fsp dropStack32 at h
  rw [h]
  exact Entails.of_eq (by ac_rfl)

theorem v2hsd_polyEncoder_1392_join (fsp tag : BitVec 64) :
    ((fsp + 1392#64) ↦₆₄ tag) ∗
      memRegion (fsp + 1400#64) 384 ∗
      memRegion (fsp + 1784#64) 8 ⊢
    memRegion (fsp + 1392#64) 400 := by
  have h1 : fsp + 1400#64 = (fsp + 1392#64) + 8#64 := by bv_omega
  have h2 : fsp + 1784#64 = (fsp + 1400#64) + 384#64 := by bv_omega
  rw [ProofLib.memRegion_split' (b := fsp + 1392#64) (n := 8) (k := 392)
        (b' := fsp + 1400#64) rfl h1 (by decide),
      ProofLib.memRegion_split' (b := fsp + 1400#64) (n := 384) (k := 8)
        (b' := fsp + 1784#64) rfl h2 (by decide)]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _)

theorem v2hsd_drop_poly16_pre (A : RustAlloc) (fsp : BitVec 64) (enc : PolyEncoder) (Frame : SepProp) :
    stackAt fsp encoderFromPbStack ∗
      polyEncoderAt A (fsp + 1392#64) enc ∗
      A.pool ∗
      Frame ⊢
    ∃∗ tag : BitVec 64, ∃∗ vecs : List (List GF16),
      ⌜vecs.length = NUM_POLYS⌝ ∗
      ((stackAt fsp dropStack32 ∗ memRegion (fsp - 5152#64) 1024) ∗
       ((fsp + 1392#64) ↦₆₄ tag) ∗
       vecGF16ListOf A ((fsp + 1392#64) + 8#64) vecs ∗
       memRegion ((fsp + 1392#64) + 392#64) 8 ∗
       A.pool ∗
       Frame) := by
  refine Entails.trans
    (sepConj_mono
      (v2hsd_stackAt_encoderFromPbStack_to_dropStack32 fsp)
      (sepConj_mono_left (polyEncoderAt_entails_tag_vecs_tail A (fsp + 1392#64) enc))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro tag
  apply Entails.sepExists_elim; intro vecs
  refine Entails.sepExists_right tag ?_
  refine Entails.sepExists_right vecs ?_
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.States.FromPb
