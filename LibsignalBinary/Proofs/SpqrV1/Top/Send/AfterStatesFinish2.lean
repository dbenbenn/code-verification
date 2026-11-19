/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.Defs
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesFinish1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `spqr::send`: Non-Looping `InnerState` Drop Variants & `PolynomialDecoder` Loop

Symbolic execution of the four non-looping `V1State.InnerState` drop variants (`.ct2Sampled`,
`.ct1Received`, `.keysSampled`, `.ekReceivedCt1Sampled`) and the shared `PolynomialDecoder`
drop loop in `spqr::send::<HookRng>`.
-/

public section

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification
open CryptoVerification.CodeLayout
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
open CryptoVerification.SpqrV1.Prost.EncodeToVec

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr v1StatePBPinnedAt optProtoPolynomialEncoderAt
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero

@[local simp, local arm64_norm]
private theorem send2_noneCap2_add_two_beq_zero :
    (0xfffffffffffffffe#64 + 2#64 == 0#64) = true := rfl

@[local simp, local arm64_norm]
private theorem send2_noneCap2_add_two_bne_zero :
    (0xfffffffffffffffe#64 + 2#64 != 0#64) = false := rfl

attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero Drop.noneCap_add_two_beq_zero EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero

theorem cap_add_three_ult_2_false {cap : BitVec 64} (hlt : cap.toNat < 2 ^ 63) :
    BitVec.ult (cap + 3#64) 2#64 = false := by
  revert hlt; bv_bits

theorem cap_add_three_cc_2_false {cap : BitVec 64} (hlt : cap.toNat < 2 ^ 63) :
    ConditionHolds .CC (subsPState64 (cap + 3#64) 2#64) = false := by
  rw [conditionHolds_cc_subsPState64, cap_add_three_ult_2_false hlt]

/-! ## 1. Non-Looping `V1State.InnerState` Drop Variants (`ct2Sampled`, `ct1Received`, `keysSampled`, `ekReceivedCt1Sampled`) -/

theorem protoUnchunked3VecHeadersAt_entails_memRegion_128' (a : BitVec 64) (g : ThreeVecGhost) :
    (a ↦₆₄ g.v1.cap) ∗ ((a + 8#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 16#64) 8 ∗
      ((a + 24#64) ↦₆₄ g.v2.cap) ∗ ((a + 32#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 40#64) 8 ∗
      ((a + 48#64) ↦₆₄ g.v3.cap) ∗ ((a + 56#64) ↦₆₄ g.v3.ptr) ∗ memRegion (a + 64#64) 8 ∗
      memRegion (a + 72#64) 48 ∗ memRegion (a + 120#64) 8 ⊢
    memRegion a 128 := by
  refine Entails.trans
    (Entails.of_eq (show _ = protoUnchunked3VecHeadersAt a g ∗ memRegion (a + 72#64) 48 ∗ memRegion (a + 120#64) 8 by
      unfold protoUnchunked3VecHeadersAt; ac_rfl)) ?_
  exact protoUnchunked3VecHeadersAt_entails_memRegion_128 a g

theorem auth72HeadersAt_entails_memRegion_48' (a : BitVec 64) (ga : TwoVecGhost) :
    ((a + 72#64) ↦₆₄ ga.v1.cap) ∗ ((a + 80#64) ↦₆₄ ga.v1.ptr) ∗ memRegion (a + 88#64) 8 ∗
      ((a + 96#64) ↦₆₄ ga.v2.cap) ∗ ((a + 104#64) ↦₆₄ ga.v2.ptr) ∗ memRegion (a + 112#64) 8 ⊢
    memRegion (a + 72#64) 48 := by
  change auth72HeadersAt a ga ⊢ memRegion (a + 72#64) 48
  exact auth72HeadersAt_entails_memRegion_48 a ga

@[local simp, local arm64_norm, local wp_norm]
theorem ofNat_add_one_sub_one (n : Nat) :
    BitVec.ofNat 64 (n + 1) - 1#64 = BitVec.ofNat 64 n := by
  rw [ofNat_succ_eq_add_one, BitVec.add_sub_cancel]

theorem ofNat_succ_beq_one_false_24 {n : Nat} (hpos : 0 < n) (hlt : n * 24 < 2 ^ 63) :
    ¬((BitVec.ofNat 64 (n + 1) == 1#64) = true) := by
  rw [ofNat_succ_eq_add_one]
  exact ofNat_add_one_beq_one_false_24 hpos hlt

end CryptoVerification.SpqrV1.Top.Send

