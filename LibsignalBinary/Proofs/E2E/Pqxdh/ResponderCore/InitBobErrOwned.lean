/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptErrOwned -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBob -- proof-setup: allow-public-import
import ProofLib.ProgramReflection.SortedFresh
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.CodeLayout

/-!
# `initialize_bob_session` (`0x21c80`): Owned-Error Rejecting Run

Strengthens the rejecting-branch specification of `initialize_bob_session` (`0x21c80`) to retain
the owned `pqxdhAcceptErrPayloadAt` payload across the 48-byte `SignalProtocolError` copy into
`outPtr + 8#64`, on both `trTrapProgAt` and `tripleRatchetProgAtExt`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.E2E.Pqxdh.ResponderCore

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E.Pqxdh CryptoVerification.E2E.Pqxdh.Initiator

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_sub_sub_lit bv_add_neg64
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
/-- Owned-payload refinement of `initBobErrAt` for the 344-byte
`Result<SessionState, SignalProtocolError>` sret slot `outPtr` of `initialize_bob_session`:
`Result::Err` discriminant (`-1`) at `outPtr`, 48-byte `SignalProtocolError` at `outPtr + 8#64`,
its `pqxdhAcceptErrPayloadAt`, and 288 trailing bytes at `outPtr + 56#64`. -/
@[expose] def initBobErrOwnedAt (A : RustAlloc) (outPtr : BitVec 64) : SepProp :=
  (outPtr ↦₆₄ 0xffffffffffffffff#64) ∗
  ∃∗ errTag : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
  ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
    ⌜errTag ≠ pollReadyOkWord ∧ errTag ≠ 0xfffffffffffffffd#64⌝ ∗
    speWordsAt (outPtr + 8#64) errTag w2 w3 w4 w5 w6 ∗
    pqxdhAcceptErrPayloadAt A errTag w2 w3 w4 ∗
    memRegion (outPtr + 56#64) 288

private theorem initBobErrOwnedAt_merge (A : RustAlloc)
    (outPtr errTag w2 w3 w4 w5 w6 : BitVec 64)
    (hw1 : errTag ≠ pollReadyOkWord ∧ errTag ≠ 0xfffffffffffffffd#64) :
    pqxdhAcceptErrPayloadAt A errTag w2 w3 w4 ∗
    (outPtr ↦₆₄ 0xffffffffffffffff#64) ∗
    ((outPtr + 8#64) ↦₆₄ errTag) ∗
    ((outPtr + 16#64) ↦₆₄ w2) ∗
    ((outPtr + 24#64) ↦₆₄ w3) ∗
    ((outPtr + 32#64) ↦₆₄ w4) ∗
    ((outPtr + 40#64) ↦₆₄ w5) ∗
    ((outPtr + 48#64) ↦₆₄ w6) ∗
    memRegion (outPtr + 56#64) 288 ⊢
    initBobErrOwnedAt A outPtr := by
  have hrearr :
      pqxdhAcceptErrPayloadAt A errTag w2 w3 w4 ∗
      ((outPtr ↦₆₄ 0xffffffffffffffff#64) ∗ (((outPtr + 8#64) ↦₆₄ errTag) ∗
        (((outPtr + 16#64) ↦₆₄ w2) ∗ (((outPtr + 24#64) ↦₆₄ w3) ∗ (((outPtr + 32#64) ↦₆₄ w4) ∗
          (((outPtr + 40#64) ↦₆₄ w5) ∗ (((outPtr + 48#64) ↦₆₄ w6) ∗
            memRegion (outPtr + 56#64) 288))))))) =
      (outPtr ↦₆₄ 0xffffffffffffffff#64) ∗
      (((outPtr + 8#64) ↦₆₄ errTag) ∗ ((outPtr + 16#64) ↦₆₄ w2) ∗
        ((outPtr + 24#64) ↦₆₄ w3) ∗ ((outPtr + 32#64) ↦₆₄ w4) ∗
        ((outPtr + 40#64) ↦₆₄ w5) ∗ ((outPtr + 48#64) ↦₆₄ w6) ∗
        pqxdhAcceptErrPayloadAt A errTag w2 w3 w4 ∗
        memRegion (outPtr + 56#64) 288) := by ac_rfl
  rw [hrearr]
  unfold initBobErrOwnedAt
  refine sepConj_mono_right ?_
  refine Entails.sepExists_right errTag (Entails.sepExists_right w2 (Entails.sepExists_right w3
    (Entails.sepExists_right w4 (Entails.sepExists_right w5 (Entails.sepExists_right w6 ?_)))))
  rw [pure_sepConj_of_true hw1]
  simp only [speWordsAt, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.E2E.Pqxdh.ResponderCore
