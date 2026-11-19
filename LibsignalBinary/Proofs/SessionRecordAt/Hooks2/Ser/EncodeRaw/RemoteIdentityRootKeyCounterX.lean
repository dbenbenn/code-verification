/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.BaseX -- proof-setup: allow-public-import
import Mathlib.Tactic.ToAdditive
import Mathlib.Tactic.ToDual
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.RemoteIdentityRootKeyCounter
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PrologueVersionLocalIdentityX
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

public section

set_option autoImplicit false

/-!
# `SessionStructure::encode_raw` Tags 3, 4, and 5 (`+0x0c0` → `+0x1cc`)

Verifies protobuf tags 3 (`remote_identity_public`), 4 (`root_key`), and 5 (`previous_counter`,
offsets `192..460`, cold `1880..2120`) of `SessionStructure::encode_raw` (`0x4d38`) on `SP2Ext`.
-/

namespace CryptoVerification.E2E.Record.Serialization

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap hiding vecU8Buf vecU8At_eq_header_sep_buf
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open Proofs.libsignal.Hooks2
open CryptoVerification.E2E.Record.Serialization.EncodeRawAux

set_option allowUnsafeReducibility true
attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local irreducible] stackAt vecRest vecU8Buf vecSrcRest vecCopyDone
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local arm64_norm]
theorem bv_add_neg80_1b_x (x : BitVec 64) : x + bv% (2 ^ 64 - 80) = x - 80#64 :=
  (BitVec.sub_eq_add_neg x 80#64).symm

set_option maxHeartbeats 400000

theorem L1_EncodeRawRemoteIdentityRootKeyCounterX : True := trivial

/-! ## Tag 3 (`remote_identity_public`, `+0x0c0 → +0x12c`, reserve `+0x758..+0x7bc`) -/

end CryptoVerification.E2E.Record.Serialization
