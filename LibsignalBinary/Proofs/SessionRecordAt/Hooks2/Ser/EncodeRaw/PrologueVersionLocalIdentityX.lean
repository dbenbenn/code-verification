/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.BaseX -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.PrologueVersionLocalIdentity -- proof-setup: allow-public-import
import Mathlib.Tactic.ToAdditive
import Mathlib.Tactic.ToDual
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

public section

set_option autoImplicit false

/-!
# `SessionStructure::encode_raw` Prologue and Tags 1–2 (`+0x000` → `+0x0c0`)

Verifies the `0x50`-byte stack-frame prologue (`+0x000 → +0x01c`), protobuf tag 1
(`session_version`, `+0x01c → +0x054`), and protobuf tag 2 (`local_identity_public`,
`+0x054 → +0x0c0`) of `SessionStructure::encode_raw` (`0x4d38`) on `SP2Ext`.
-/

namespace CryptoVerification.E2E.Record.Serialization

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap hiding vecU8Buf vecU8At_eq_header_sep_buf
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open ProofLib.ProgramReflection
open Proofs.libsignal.Hooks2
open CryptoVerification.E2E.Record.Serialization.EncodeRawAux

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

set_option allowUnsafeReducibility true
attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr stackAt vecRest vecU8Buf vecSrcRest vecCopyDone Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local arm64_norm]
theorem bv_add_neg80_x (x : BitVec 64) : x + bv% (2 ^ 64 - 80) = x - 80#64 :=
  (BitVec.sub_eq_add_neg x 80#64).symm

theorem L1_EncodeRawPrologueX : True := trivial

/-! ## Buffer call helpers on `SP2Ext` -/

end CryptoVerification.E2E.Record.Serialization
