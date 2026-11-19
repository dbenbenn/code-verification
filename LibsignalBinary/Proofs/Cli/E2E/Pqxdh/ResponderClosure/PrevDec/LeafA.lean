/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafDefs
import ProofLib
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.TripleRatchet.Prost.SkipFieldLemmas
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DecodeVarint5

public section

set_option autoImplicit false

/-!
# Handshake `prost::encoding::skip_field::<&mut &[u8]> [local#6]` (Non-Group Cases 1–6)

Verifies the six non-group dispatch branches (`depth = 0`, `.endGroup`, `.sixtyFourBit`,
`.thirtyTwoBit`, `.varint`, and `.lengthDelimited`) of
`prost::encoding::skip_field::<&mut &[u8]> [local#6]`.
-/

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.CodeLayout
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local simp, local arm64_norm]
private theorem bv64_sub_zero (x : BitVec 64) : x - 0#64 = x := BitVec.sub_zero x

@[local simp, local arm64_norm]
private theorem bv64_add_zero (x : BitVec 64) : x + 0#64 = x := BitVec.add_zero x

/-! ## Case 1: `depth = 0` (`RecursionLimitReached`) -/

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
