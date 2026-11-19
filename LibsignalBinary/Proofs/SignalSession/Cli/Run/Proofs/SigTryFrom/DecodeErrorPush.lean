/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.SigTryFrom.PushCore
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.SigTryFrom.PushGrowOne
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeErrorPush.Push
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.SigTryFromHelpers

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.CodeLayout
open CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush
open BS31

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre_x sp_setMem_setPC_pre_x
  readReg64_setPC_pre_x readReg64_setMem_setPC_pre_x
  readReg32_setPC_pre_x readReg32_setMem_setPC_pre_x
  readReg_setPC_pre_x readReg_setMem_setPC_pre_x

@[expose] def pushStackPadX (sp : BitVec 64) : SepProp :=
  memRegion (sp - 32768#64) 16208

theorem stackAt_pushX (sp : BitVec 64) :
    stackAt sp (2 * extHookStack) =
      pushStackPadX sp ∗
      stackAt (sp - 176#64) extHookStack ∗
      cells (sp - 176#64) 4 ∗
      cells (sp - 144#64) 8 ∗
      cells (sp - 80#64) 2 ∗
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
        ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
  have h1 := ProofLib.stackAt_split_bottom sp 16560 16208 (by decide)
  change stackAt sp (2 * extHookStack) = pushStackPadX sp ∗ stackAt sp 16560 at h1
  have h2 := CryptoVerification.LibsignalTripleRatchet.stackAt_split_cells sp 16496 8 (by decide)
  change stackAt sp 16560 = stackAt (sp - 64#64) 16496 ∗ cells (sp - 64#64) 8 at h2
  have h3 := CryptoVerification.LibsignalTripleRatchet.stackAt_split_cells (sp - 64#64) 16480 2 (by decide)
  have h3' : sp - 64#64 - BitVec.ofNat 64 (2 * 8) = sp - 80#64 := by bv_omega
  rw [h3'] at h3
  change stackAt (sp - 64#64) 16496 = stackAt (sp - 80#64) 16480 ∗ cells (sp - 80#64) 2 at h3
  have h4 := CryptoVerification.LibsignalTripleRatchet.stackAt_split_cells (sp - 80#64) 16416 8 (by decide)
  have h4' : sp - 80#64 - BitVec.ofNat 64 (8 * 8) = sp - 144#64 := by bv_omega
  rw [h4'] at h4
  change stackAt (sp - 80#64) 16480 = stackAt (sp - 144#64) 16416 ∗ cells (sp - 144#64) 8 at h4
  have h5 := CryptoVerification.LibsignalTripleRatchet.stackAt_split_cells (sp - 144#64) 16384 4 (by decide)
  have h5' : sp - 144#64 - BitVec.ofNat 64 (4 * 8) = sp - 176#64 := by bv_omega
  rw [h5'] at h5
  change stackAt (sp - 144#64) 16416 =
    stackAt (sp - 176#64) extHookStack ∗ cells (sp - 176#64) 4 at h5
  have hc8 : cells (sp - 64#64) 8 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
        ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
    cells_unfold
  rw [h1, h2, h3, h4, h5, hc8]
  ac_rfl

end CryptoVerification.SignalSession.Cli.RunProofs.SigTryFromHelpers
