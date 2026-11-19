/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6a -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 6 (`HeaderReceived`, `+1464`) — Part B

Early `MsgDecode` error cleanup (`+1520 -> +10324`), `StateDecode` error paths from `+3760`
(`s.uc = none`, `hdr.length ≠ 64`, `auth = none`), and validation step `+3760 -> +3796`.
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



theorem v6hr_stackAt_encoderFromPbStack_to_allocHook (fsp : BitVec 64) :
    stackAt fsp encoderFromPbStack ⊢
      stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056 := by
  have h := ProofLib.stackAt_split_bottom fsp allocHookStack 1056 (by decide)
  change stackAt fsp encoderFromPbStack =
    memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack at h
  rw [h]
  exact Entails.of_eq (by ac_rfl)

theorem v6hr_stackAt_allocHook_to_encoderFromPbStack (fsp : BitVec 64) :
    stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056 ⊢
      stackAt fsp encoderFromPbStack := by
  have h := ProofLib.stackAt_split_bottom fsp allocHookStack 1056 (by decide)
  change stackAt fsp encoderFromPbStack =
    memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack at h
  rw [h]
  exact Entails.of_eq (by ac_rfl)

@[simp, arm64_norm, wp_norm]
theorem v6hr_bfm_56_55_low_byte (x : BitVec 64) :
    (((x &&& 72057594037927935#64) <<< 8).extractLsb' 0 8) = 0#8 := by
  bv_kernel

end CryptoVerification.SpqrV1.States.FromPb
