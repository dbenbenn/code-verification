/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneChains -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneKeysFront
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneKeysTail
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClonePack
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClonePending
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.CodeLayout

public section

set_option autoImplicit false

/-!
# General Stage P3 Clone — End-to-End Composition

Assembles all five segments (`CloneKeysFrontStmt`, `CloneChainsStmt`, `ClonePendingStmt`,
`CloneKeysTailStmt`, `ClonePackStmt`) into `CloneGenStmt` (`+0x1778 → +0x1cd4 / +0x1e04`,
`genP3Pre → genP3Post`).
-/

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.ChainClone3
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
