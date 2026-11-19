/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StageP2a -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.TrapRng -- proof-setup: allow-public-import
public import ProofLib.SepLogic.WP
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StageP1
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyBase
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.ErrExit
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.OneKeyStore
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.OneKeyStoreBase

/-!
# Responder Closure `.rodata`, Vtable, and Stage P2/P3 Segment Steps

`.rodata` `"decryption failed"` and `.data.rel.ro` vtable helpers, Stage P3 version-dispatch
and version-mismatch error basic-block `SepWP` lemmas, and Stage P2 zero-capacity signature
segment specializations for `message_decrypt_prekey::<Coins>::{closure#0}`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.E2E.Pqxdh.ResponderClosure

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.LibsignalSession

open CryptoVerification.RustHeap

open CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalSession

open CryptoVerification.E2E.Pqxdh.WireEntries

open CryptoVerification.E2E.Pqxdh.ResponderStore

set_option maxRecDepth 200000

set_option maxHeartbeats 1600000

set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

local macro "cells_unfold_26" : tactic =>
  `(tactic| simp (config := { maxSteps := 1000000 }) (disch := decide) only [
    ProofLib.cells_sub_succ, Nat.reduceSub, ProofLib.cells_zero, sepConj_emp,
    sepExists_sepConj_right] at *)

end CryptoVerification.E2E.Pqxdh.ResponderClosure
