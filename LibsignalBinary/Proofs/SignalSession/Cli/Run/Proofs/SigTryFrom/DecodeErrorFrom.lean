/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeErrorFrom.Core
import ProofLib.SepLogic.WPp
public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.SigTryFromHelpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorFrom

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
theorem stackAt_decodeErrorFromX (sp : BitVec 64) :
    stackAt sp (2 * extHookStack) =
      memRegion (sp - 32768#64) 16352 ∗
        stackAt (sp - 32#64) extHookStack ∗
        cells (sp - 32#64) 4 := by
  have h1 : stackAt sp (2 * extHookStack) =
      memRegion (sp - 32768#64) 16352 ∗ stackAt sp (extHookStack + 32) :=
    ProofLib.stackAt_split_bottom sp (extHookStack + 32) 16352 (by decide)
  have h2 : stackAt sp (extHookStack + 32) =
      stackAt (sp - 32#64) extHookStack ∗ cells (sp - 32#64) 4 :=
    CryptoVerification.LibsignalTripleRatchet.stackAt_split_cells sp 16384 4 (by decide)
  rw [h1, h2]

end CryptoVerification.SignalSession.Cli.RunProofs.SigTryFromHelpers
