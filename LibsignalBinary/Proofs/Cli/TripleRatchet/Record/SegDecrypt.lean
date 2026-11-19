/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Record.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Defs
public import LibsignalBinary.Proofs.TripleRatchet.TrapRng -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.InImage.SpqrRecvEmpty.Defs
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Getters.Defs
public import LibsignalBinary.Proofs.Cli.Specifications.LibsignalTripleRatchet -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Hooks
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Model
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Statements
public import LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordCallees.Defs
public import LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordChainClone.Defs
import LibsignalBinary.Proofs.SignalSession.Coins.Defs
import Lean
import ProofLib.GenDecodes
import ProofLib.ProgramReflection
import ProofLib.SepLogic.CodeLookup
import ProofLib.VCGen
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import LibsignalBinary.Proofs.TripleRatchet.Record.SegDecrypt
import LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatch
import ProofLib.SepLogic.WPp

/-!
# CLI `SegDecrypt` (`try_decrypt_with_state` Call and 3-Way Dispatch)

Proves `SegDecryptSpec` (`+0x69c → +0x1e8c / +0x850`) in the CLI image: invokes
`try_decrypt_with_state` at `+0x6b4` and dispatches `Ok`, `Err(DuplicatedMessage)`, and other `Err`
outcomes to seams `J` and `F`.
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.Record

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.LibsignalSession

open CryptoVerification.RustHeap

open CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees

open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone

open CryptoVerification.LibsignalTripleRatchet.RawByteMove

set_option maxRecDepth 200000

set_option maxHeartbeats 1600000

namespace SegDecryptFacts

namespace SegDecryptRegReadSimp

end SegDecryptRegReadSimp

open SegDecryptRegReadSimp

end SegDecryptFacts

open SegDecryptFacts

attribute [local irreducible] Program.fetch Program.externAt?

end CryptoVerification.LibsignalTripleRatchet.Record
