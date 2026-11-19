/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1b
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Top-Level Dispatch & Variant Composition (`0x5a0a4`)

Combines the prologue and `.rodata` jump-table dispatch with per-variant `SepWPp` body obligations,
proves Variant 0 (`KeysUnsampled`), and reduces `StatesFromPbOkExt` / `StatesFromPbOkX` to
per-variant `statesFromPbVariantSpec` obligations.
-/

public section

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

/-! ## 1. Stack, Tag, & `SepWPp` Postcondition Helpers (`sfpProof_*`) -/

theorem sfpProof_fsp_0_and_2296_entails_2304 (fsp : BitVec 64) :
    (fsp ↦₆₄ 0#64) ∗ memRegion (fsp + 8#64) 2296 ⊢ memRegion fsp 2304 :=
  cell0_2296_entails_memRegion_2304 fsp 0#64

theorem sfpProof_sp_sub_1552_eq (sp0 : BitVec 64) :
    sp0 - 1552#64 = (sp0 - 2400#64) + 848#64 := by bv_omega

abbrev sfpProof_stackXExtra : Nat := statesFromPbStackX - statesFromPbStack

theorem sfpProof_stackAt_statesFromPbStackX_eq (sp : BitVec 64) :
    stackAt sp statesFromPbStackX =
      memRegion (sp - BitVec.ofNat 64 statesFromPbStackX) sfpProof_stackXExtra ∗
      stackAt sp statesFromPbStack := by
  have heq : statesFromPbStack + sfpProof_stackXExtra = statesFromPbStackX := by decide
  rw [← heq]
  exact ProofLib.stackAt_split_bottom sp statesFromPbStack sfpProof_stackXExtra (by decide)

end CryptoVerification.SpqrV1.States.FromPb
