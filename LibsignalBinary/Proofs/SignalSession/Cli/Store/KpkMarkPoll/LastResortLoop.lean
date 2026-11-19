/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Layout -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.RoData -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Calls
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Drops
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortErr
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.PublicKeyTryFrom
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoop
import ProofLib.SepLogic.WPp

public section

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.CodeLayout CryptoVerification.SignalSession.Cli
open CryptoVerification.SpqrV1.Varint

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.add_zero BitVec.zero_add
  BitVec.toNat_zero setWidth_32_setWidth_64

/-! ## Postcondition & Result Unpack Helpers -/

theorem getResultAt_b0_ok_unpack (A : RustAlloc) (sp : BitVec 64) (bs : List (BitVec 8)) :
    getResultAt A (sp - 0xb0#64) (.ok bs) =
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        ((sp - 0xb0#64) ↦₆₄ okTagVec) ∗
        ((sp - 0xa8#64) ↦₆₄ cap) ∗
        ((sp - 0xa0#64) ↦₆₄ ptr) ∗
        ((sp - 0x98#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        SpqrV1.ChainProofs.bytesAt false ptr bs ∗
        vecU8Tail A cap ptr bs ∗
        memRegion (sp - 0x90#64) 16) := by
  dsimp only [getResultAt, vecResultAt]
  have e1 : sp - 0xb0#64 + 8#64 = sp - 0xa8#64 := by bv_omega
  have e2 : sp - 0xb0#64 + 0x20#64 = sp - 0x90#64 := by bv_omega
  rw [e1, e2, vecU8_eq_bytes_tail A (sp - 0xa8#64) bs (sp - 0xa0#64) (sp - 0x98#64)
        (by bv_omega) (by bv_omega)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply sepProp_ext <;>
    (refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr =>
      Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.of_eq (by ac_rfl))))

private theorem w0_cbnz_cond_false {v : BitVec 64} (hne : v.setWidth 32 ≠ 0#32) :
    (BitVec.zeroExtend 64 (BitVec.truncate 32 v) == 0#64) = false := by
  apply beq_false_of_ne
  intro h
  apply hne
  have h32 := congrArg (BitVec.setWidth 32) h
  simpa [setWidth_32_setWidth_64] using h32

end CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers
