/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.ChainEncodedLen -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.ChainEncodedLenBase
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EpochEncodedLen
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# CLI `Chain::encoded_len` Verification

Proves stage lemmas (`direction`, `current_epoch`, `links`, `next_root`, `send_epoch`, `params`)
and top-level `subroutine_ok` contracts for `<spqr::proto::pq_ratchet::Chain as
prost::message::Message>::encoded_len` on the CLI image.
-/

public section

namespace CryptoVerification.SpqrV1.ProtoRepr

open Arm64 ProofLib CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalSpqrV1

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_beq_zero32 ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  zext64_truncate32 ule_zero_64 ult_zero_64
  sext64_truncate32 signExtend64_beq_zero64

attribute [local simp] sext64_truncate32 signExtend64_beq_zero64

/-! ## Step 3A: `direction + current_epoch + links + next_root` (`+0x0b8..+0x0ec`) -/

end CryptoVerification.SpqrV1.ProtoRepr
