/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Layout -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Calls
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.PublicKeyTryFrom
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Defs
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoop
import ProofLib.SepLogic.WPp

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout CryptoVerification.SignalSession.Cli

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.add_zero BitVec.zero_add
  BitVec.toNat_zero setWidth_32_setWidth_64

/-! ## Bit-level lemmas for the unaligned `readErr` word round-trip -/

private abbrev readErrV28 (fnPtr : BitVec 64) : BitVec 64 :=
  (fnPtr.extractLsb' 0 8).setWidth 64

private abbrev readErrW8 (fnPtr : BitVec 64) : BitVec 64 :=
  BitVec.zeroExtend 64
    (BitVec.truncate 32
      (BitVec.zeroExtend 64 (BitVec.extractLsb' 40 16 fnPtr) |||
        BitVec.zeroExtend 64 (BitVec.zeroExtend 32 (BitVec.extractLsb' 56 8 fnPtr) <<< 16)))

private abbrev readErrV23 (fnPtr : BitVec 64) : BitVec 64 :=
  (fnPtr.extractLsb' 8 32).setWidth 64 ||| (readErrW8 fnPtr <<< 32)

private theorem readErr_v28_lo (fnPtr : BitVec 64) :
    (readErrV28 fnPtr).setWidth 8 = fnPtr.extractLsb' 0 8 := by
  unfold readErrV28; bv_bits

private theorem readErr_v23_lo (fnPtr : BitVec 64) :
    (readErrV23 fnPtr).setWidth 32 = fnPtr.extractLsb' 8 32 := by
  unfold readErrV23 readErrW8; bv_bits

private theorem readErr_v23_mid (fnPtr : BitVec 64) :
    ((readErrV23 fnPtr) >>> 32).setWidth 16 = fnPtr.extractLsb' 40 16 := by
  unfold readErrV23 readErrW8; bv_bits

private theorem readErr_v23_hi (fnPtr : BitVec 64) :
    ((readErrV23 fnPtr) >>> 48).setWidth 8 = fnPtr.extractLsb' 56 8 := by
  unfold readErrV23 readErrW8; bv_bits

/-! ## Shared Epilogue (`+816 .. +888`) -/

end CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers
