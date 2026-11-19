/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Defs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Steps
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedAux
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderStore.Fetch
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommon
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers

/-!
# Stage P2 Basic Blocks — Shared Error Funnel and Arm 1

`SepWP` basic-block lemmas on `tripleRatchetProgAtExt b ext` for the shared 6-word
`SignalProtocolError` unwind funnel (`+0x1648 → +0x1698 → +0x1898 → +0x359c → retAddr`) and
Arm 1 (`get_signed_pre_key` error at `+0x0f38 → spkDropAddr → +0x1648`).
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure

set_option maxRecDepth 200000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

local macro "sep_norm" : tactic =>
  `(tactic| repeat (first
    | simp only [↓reduceIte]
    | simp only [BitVec.add_assoc]
    | simp only [BitVec.reduceAdd]
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [emp_sepConj]
    | simp only [sepConj_emp]
    | simp only [sepConj_assoc]))

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local wp_norm, local arm64_norm]
  bfi_mask_lsr8_id evalBitfield_bfi_lsr8
attribute [local simp] extractLsb_hi_lo_append

theorem bfi_mask_lsr8_of_lo32 {r23 w1 : BitVec 64}
    (hlo : r23.extractLsb' 0 32 = w1.extractLsb' 0 32) :
    (r23 &&& 255#64 ||| (w1 >>> 8 &&& 72057594037927935#64) <<< 8) = w1 := by
  have hmask : ∀ x : BitVec 64, (x.extractLsb' 0 32).zeroExtend 64 &&& 255#64 = x &&& 255#64 := by
    intro x; clear * -; bv_bits
  have hrw : r23 &&& 255#64 = w1 &&& 255#64 := by rw [← hmask r23, hlo, hmask w1]
  rw [hrw]
  exact bfi_mask_lsr8_id w1

theorem evalBitfield_bfi_lsr8_of_lo32 {r23 w1 : BitVec 64}
    (hlo : r23.extractLsb' 0 32 = w1.extractLsb' 0 32) :
    evalBitfield .W64 .BFM r23 (w1 >>> 8) 56 55 = w1 := by
  change (if (BitfieldOp.BFM == BitfieldOp.UBFM) = true then r23 >>> 8 <<< 8
      else r23 &&& 255#64 ||| (w1 >>> 8 &&& 72057594037927935#64) <<< 8) = w1
  have h : (BitfieldOp.BFM == BitfieldOp.UBFM) = false := rfl
  simp only [h]
  exact bfi_mask_lsr8_of_lo32 hlo

/-- Folds the 48-byte epilogue stores at `outPtr + 0x0..0x30` into
`speWordsAt outPtr w0 w1 w2 w3 w4 w5`. -/
theorem speWordsAt_realign_outPtr (outPtr w0 w1 w2 w3 w4 w5 : BitVec 64) :
    ((outPtr + 0x0#64) ↦₆₄ w0) ∗
      ((outPtr + 0x8#64) ↦₃₂ w1.extractLsb' 0 32) ∗
      ((outPtr + 0xc#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
      ((outPtr + 0x14#64) ↦₆₄ (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)) ∗
      ((outPtr + 0x1c#64) ↦₆₄ (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)) ∗
      ((outPtr + 0x24#64) ↦₆₄ (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)) ∗
      ((outPtr + 0x2c#64) ↦₃₂ w5.extractLsb' 32 32) =
    speWordsAt outPtr w0 w1 w2 w3 w4 w5 := by
  have h40 := (realign_40 (outPtr + 8#64) w1 w2 w3 w4 w5).symm
  repeat (simp only [BitVec.add_assoc] at h40); repeat (simp only [BitVec.reduceAdd] at h40)
  dsimp only [speWordsAt]
  rw [BitVec.add_zero]
  rw [h40]

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

