/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.V1StateHelpers -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1StateBranches
import ProofLib.SepLogic.WPp

/-!
# CLI `V1State::encoded_len` Two-Field Variant Branches (Part B: `k = 6, 8, 5, 10`)

Proves `SepWPp` branch lemmas for `.headerReceived` (`k = 6`), `.ekReceivedCt1Sampled` (`k = 8`),
`.noHeaderReceived` (`k = 5`), and `.ct2Sampled` (`k = 10`) in `V1State::encoded_len` on the CLI
image.
-/

public section

namespace CryptoVerification.SpqrV1.ProtoRepr

open Arm64 ProofLib CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalSpqrV1

open EncodedLen

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

set_option linter.unusedVariables false

set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_beq_zero32 ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  noneCap2_add_two_beq_zero noneCap2_add_two_bne_zero
  zext64_truncate32 ule_zero_64 ult_zero_64 ule_self_64 ult_self_64
  add_48_sub_40 add_48_add_neg40 add_64_sub_56 add_64_add_neg56

/-! ## 5. Branch `k = 6` (`.headerReceived`, `+732..+864` and `+1464..+1488`) -/

end CryptoVerification.SpqrV1.ProtoRepr
