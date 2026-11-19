/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7b -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7a
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 7 (`Ct1Sampled`, `+1056`) — Part C

Mid-stage cleanup paths (`+7100`, `+3732`, `+10556 -> +4632`) for Variant 7 (`InnerState.ct1Sampled`,
jump-table target `+1056`).
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

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append



/-! ## 1. Cleanup at `+7100..+7208 -> +4632` and `+3732..+3740 -> +7104/+7116` -/

/-- The 4 `Vec<u8>` header cells in `fsp + 1296..1376` (`0x510..0x560`) read during `+7116..+7196`
and `+10588..+10668`. -/
@[expose] def v7_ct1SentSpillCells (fsp p2 c3 p3 c4 p4 c5 p5 : BitVec 64) : SepProp :=
  ((fsp + 1296#64) ↦₆₄ p2) ∗
  ((fsp + 1312#64) ↦₆₄ c3) ∗
  ((fsp + 1320#64) ↦₆₄ p3) ∗
  ((fsp + 1336#64) ↦₆₄ c4) ∗
  ((fsp + 1344#64) ↦₆₄ p4) ∗
  ((fsp + 1360#64) ↦₆₄ c5) ∗
  ((fsp + 1368#64) ↦₆₄ p5)

theorem v7_polyEncoder_1392_join (fsp tag : BitVec 64) :
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

theorem v7_drop_poly16_pre (A : RustAlloc) (fsp : BitVec 64) (enc : PolyEncoder) (Frame : SepProp) :
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
      (v7_stackAt_encoderFromPbStack_to_dropStack32 fsp)
      (sepConj_mono_left (polyEncoderAt_entails_tag_vecs_tail A (fsp + 1392#64) enc))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro tag
  apply Entails.sepExists_elim; intro vecs
  refine Entails.sepExists_right tag ?_
  refine Entails.sepExists_right vecs ?_
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.States.FromPb
