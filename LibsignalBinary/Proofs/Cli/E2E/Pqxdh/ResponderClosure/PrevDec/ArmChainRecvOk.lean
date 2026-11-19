/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.BytesMerge6
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmChainRecvDefs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Defs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmChainRecv
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmChainRecvPush
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.ArmChain
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DecodeVarint5
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeDefs

/-!
# Unconditional Tag 6 (`sender_chain`) and Tag 7 (`receiver_chains`) Decode Arms

Instantiates `chain3CalleeKit_cli` from `decodeVarint5_ok` and `bytes_merge_6_ok_ext_of_alloc`, and
proves unconditional `OverDecArmStmtTR` specifications for tag 6 (`overDecArmSender_cli`) and tag 7
(`overDecArmRecv_cli`).
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

open Arm64 ProofLib
open CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Record (A0)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
