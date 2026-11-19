/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.InImage.SpqrRecvEmpty.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeStateEmpty.Proof -- shake: keep
import LibsignalBinary.Proofs.CodeLayout

/-!
# `Ok` and `Err` Tails of Empty-State `spqr::recv`

Proves symbolic execution of the common `Err(MsgDecode)` epilogue and the `Ok` path through
`spqr::decode_state` and `memcpy`.
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.InImage.SpqrRecvEmpty

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalSpqr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.InImage.DecodeStateEmpty
  (mr_cut' vecU8Tail vecArg_at_nil)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- The untouched stack frame pieces of `spqr::recv` after the prologue (`s0.sp - 4992` frame). -/
@[expose] def recvStackRest (sp f0 f8 f16 f24 b50 b58 b60 s29 s30 s28 s27 s26 s25 s24 s23 s22 s21 s20 s19 :
    BitVec 64) : SepProp :=
  memRegion (sp - 131072#64) 109696 ∗
  stackAt (sp - 4992#64) extHookStack ∗
  ((sp - 4992#64) ↦₆₄ f0) ∗
  ((sp - 4984#64) ↦₆₄ f8) ∗
  ((sp - 4976#64) ↦₆₄ f16) ∗
  ((sp - 4968#64) ↦₆₄ f24) ∗
  memRegion (sp - 4960#64) 320 ∗
  memRegion (sp - 4640#64) 448 ∗
  ((sp - 4192#64) ↦₆₄ 0#64) ∗
  memRegion (sp - 4184#64) 1128 ∗
  memRegion (sp - 3056#64) 352 ∗
  memRegion (sp - 2704#64) 608 ∗
  ((sp - 2096#64) ↦₆₄ b50) ∗
  ((sp - 2088#64) ↦₆₄ b58) ∗
  ((sp - 2080#64) ↦₆₄ b60) ∗
  memRegion (sp - 2072#64) 1976 ∗
  ((sp - 96#64) ↦₆₄ s29) ∗
  ((sp - 88#64) ↦₆₄ s30) ∗
  ((sp - 80#64) ↦₆₄ s28) ∗
  ((sp - 72#64) ↦₆₄ s27) ∗
  ((sp - 64#64) ↦₆₄ s26) ∗
  ((sp - 56#64) ↦₆₄ s25) ∗
  ((sp - 48#64) ↦₆₄ s24) ∗
  ((sp - 40#64) ↦₆₄ s23) ∗
  ((sp - 32#64) ↦₆₄ s22) ∗
  ((sp - 24#64) ↦₆₄ s21) ∗
  ((sp - 16#64) ↦₆₄ s20) ∗
  ((sp - 8#64) ↦₆₄ s19)

end CryptoVerification.LibsignalTripleRatchet.InImage.SpqrRecvEmpty
