/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyBase
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyBase
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropSessionStructure3
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropSpe2
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP4a
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StageP2a
import LibsignalBinary.Proofs.TripleRatchet.TrapRng
import ProofLib.SepLogic.WP
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StageP1
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderStore.SessionRecordCallees
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Drops.Local1
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.GrowSpe
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.SetState
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.Chain.VecExt
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Ext
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers

/-!
# Responder Closure Stage P3 Post-`tryDecrypt` `Ok` & `Err` Dispatch

Proves the Stage P3 `Ok` path (`stageP3_sub5_ok`, `+0x1cd8 → +0x34dc`), duplicate and
non-duplicate error funnels (`stageP3_sub5_err_dup_ok`, `stageP3_sub5_err_nondup_ok`,
`stageP3_sub5_err_ok`), and unified post-`tryDecrypt` dispatch (`stageP3_sub5_dispatch_ok`).
-/

public section

set_option autoImplicit false

namespace CryptoVerification.E2E.Pqxdh.ResponderClosure

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

open CryptoVerification.RustHeap

open CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Getters

open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees

open CryptoVerification.LibsignalTripleRatchet.RawByteMove

open CryptoVerification.LibsignalTripleRatchet.Record

open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps

open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts

open CryptoVerification.LibsignalPublicApiRepr

open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux

open CryptoVerification.LibsignalSession

open CryptoVerification.E2E.Pqxdh.WireEntries

open CryptoVerification.E2E.Pqxdh.ResponderStore

set_option maxRecDepth 200000

set_option maxHeartbeats 1600000

set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace P3P4

end P3P4

end CryptoVerification.E2E.Pqxdh.ResponderClosure
