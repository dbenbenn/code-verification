/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.Branches -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.RecordCodecs.RoundTrip
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Common.InImageKit

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.Store.IdSavePoll.Helpers

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.CodeLayout CryptoVerification.SignalSession.Cli

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm] calleeSavedVRegs_writeVReg128_0

private theorem pk_hh16 (h1 : BitVec 16) (b2 : BitVec 8) :
    (h1.zeroExtend 64 ||| (b2.zeroExtend 32 <<< 16).zeroExtend 64).truncate 32 =
      h1.zeroExtend 32 ||| (b2.zeroExtend 32 <<< 16) := by
  ext i hi; interval_cases i <;> simp

private theorem bv_shr32_tr32_tr16 (v : BitVec 64) :
    ((v >>> 32).truncate 32).truncate 16 = (v >>> 32).truncate 16 := by
  ext i hi; interval_cases i <;> simp

private theorem abstract_state {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (k : ∀ s' : State, s' = s → SepWPp prog ret s' P Q Qp) :
    SepWPp prog ret s P Q Qp :=
  k s rfl

end CryptoVerification.SignalSession.Cli.Store.IdSavePoll.Helpers
