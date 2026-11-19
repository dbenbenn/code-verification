/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3c -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyP3a2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropSessionStructure3 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderStore.SessionRecordCallees -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegFront.S0Sym -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.Specifications.LibsignalTripleRatchet
import LibsignalBinary.Specifications.LibsignalSpqrV1.Hooks
import LibsignalBinary.Specifications.LibsignalSpqrV1.Model
import LibsignalBinary.Specifications.LibsignalSpqrV1.Statements
import ProofLib.SepLogic.CodeLookup
import ProofLib.VCGen
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.CtEqRO
import LibsignalBinary.Proofs.TripleRatchet.Statements
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SameAccount
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegBackS9
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SegDhDefs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegMidS4
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegMidBase
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyP3b2
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.ConsumeMessageKey.Seams
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.Model
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegFront.Common
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Defs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyBase

/-!
# Responder Closure Stage P3 Full Assembly (`+0x1778 → +0x34dc` / `x30`)

Proves `stageP3_v4_full_ok`, unified `stageP3_ok` across all `msgVer`, and
`stageP3_initSession_ok` from `initializeRecipientSession` output.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.E2E.Pqxdh.ResponderClosure

namespace P3P4

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

open CryptoVerification.RustHeap

open CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Getters

open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees

open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone

open CryptoVerification.LibsignalTripleRatchet.RawByteMove

open CryptoVerification.LibsignalTripleRatchet.Record

open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps

open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts

open CryptoVerification.LibsignalTripleRatchet.ChainClone3

open CryptoVerification.LibsignalSession

open CryptoVerification.E2E.Pqxdh.WireEntries

open CryptoVerification.E2E.Pqxdh.ResponderStore

set_option maxRecDepth 200000

set_option maxHeartbeats 1600000

set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

end P3P4

end CryptoVerification.E2E.Pqxdh.ResponderClosure
