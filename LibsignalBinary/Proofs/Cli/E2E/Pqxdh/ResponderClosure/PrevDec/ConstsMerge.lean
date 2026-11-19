/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import ProofLib.SepLogic.WPp
public meta import Lean -- shake: keep
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DecodeVarint5 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DoReserve10 -- proof-setup: allow-public-import

/-!
# Handshake `bytes::merge` Symbol and Offset Constants

Symbol names, `CodeLayout` offsets, the `merge6_fetches_H` fetch helper, and wrapping 64-bit
callee-relative offset identities for `prost::encoding::bytes::merge::<Vec<u8>, &mut &[u8]> [local#6]`
and `prost::encoding::message::merge::<Chain, &mut &[u8]> [local#5]`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

open Arm64 CryptoVerification CryptoVerification.CodeLayout ProofLib.ProgramReflection

abbrev bytesMerge6Name : String :=
  "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#5]"

abbrev chainMerge5Name : String :=
  "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]"

abbrev rawVecGrowOneMkName : String :=
  "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>::grow_one"

abbrev bm6Off050 : BitVec 64 := 80#64
abbrev bm6Off074 : BitVec 64 := 116#64
abbrev bm6Off07c : BitVec 64 := 124#64
abbrev bm6Off094 : BitVec 64 := 148#64
abbrev bm6Off0e4 : BitVec 64 := 228#64
abbrev bm6Off1b8 : BitVec 64 := 440#64
abbrev bm6Off210 : BitVec 64 := 528#64
abbrev bm6Off220 : BitVec 64 := 544#64
abbrev bm6Off230 : BitVec 64 := 560#64
abbrev bm6Off254 : BitVec 64 := 596#64
abbrev bm6Off29c : BitVec 64 := 668#64
abbrev bm6Off2c0 : BitVec 64 := 704#64

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
