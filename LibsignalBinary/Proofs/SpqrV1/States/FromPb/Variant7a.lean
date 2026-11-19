/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Drop.PolyEncoder -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBase
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4
import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPb
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# SPQR V1 `<States>::from_pb`: Variant 7 (`Ct1Sampled`, niche variant) — Part A

Helper subroutine bridges, representation decompositions for `V1State.Chunked.Ct1Sampled`,
and error/cleanup blocks (`+4524`, `+4528`, `+4548`, `+4632`, `+5444`, `+7100`, `+10556`, `+11096`)
for Variant 7.
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
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

/-! ## 1. Subroutine Call Bridges for Variant 7 -/

private theorem v7_add_1092_sub_54872_eq (x : BitVec 64) :
    x + 1092#64 + 18446744073709496744#64 = x - 53780#64 := by bv_omega

private theorem v7_add_4544_sub_60772_eq (x : BitVec 64) :
    x + 4544#64 + 18446744073709490844#64 = x - 56228#64 := by bv_omega

private theorem v7_add_10564_sub_68396_eq (x : BitVec 64) :
    x + 10564#64 + 18446744073709483220#64 = x - 57832#64 := by bv_omega

private theorem v7_add_11100_sub_67120_eq (x : BitVec 64) :
    x + 11100#64 + 18446744073709484496#64 = x - 56020#64 := by bv_omega

private theorem v7_add_11108_sub_66156_eq (x : BitVec 64) :
    x + 11108#64 + 18446744073709485460#64 = x - 55048#64 := by bv_omega



/-! ## 2. Error Exit at `+4632` (`bfi x28, x23, #8, #56; b +7084`) -/

@[local simp, local arm64_norm, local wp_norm]
private theorem v7_bfi_8_56_extractLsb_0_8 (x28 x23 : BitVec 64) :
    (x28 &&& 255#64 ||| (x23 &&& 72057594037927935#64) <<< 8).extractLsb' 0 8 =
      x28.extractLsb' 0 8 := by bv_kernel

@[expose, reducible]
def v7_Saved4560Preserved (s0 s : State) (fsp out ptsPtr ptsCap x28_val : BitVec 64) : Prop :=
  s.sp = fsp ∧
  s.readReg64 .x19 = out ∧
  s.readReg64 .x20 = ptsPtr ∧
  s.readReg64 .x22 = ptsCap ∧
  s.readReg64 .x28 = x28_val ∧
  TraceCalleeSaved s s0

end CryptoVerification.SpqrV1.States.FromPb
