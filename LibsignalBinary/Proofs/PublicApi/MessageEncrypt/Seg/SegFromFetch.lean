/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Proofs.TripleRatchet.Prog -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.LibsignalPublicApi
public import ProofLib.SepLogic.WP
import ProofLib.SepLogic.WPp
public import ProofLib.GenDecodes

/-!
# Instruction Decode and Stepping Lemmas for `segFrom_ok`

Decode and basic-block stepping lemmas for `+0x20c..+0x2c8` (`Cur → Otr`) of
`session_message_encrypt_with_stores` (`0x3caf4`).
-/

public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi

@[expose] def otrWords25 (o : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 :
      BitVec 64) : SepProp :=
  (o ↦₆₄ w0) ∗ ((o + 0x08#64) ↦₆₄ w1) ∗ ((o + 0x10#64) ↦₆₄ w2) ∗
  ((o + 0x18#64) ↦₆₄ w3) ∗ ((o + 0x20#64) ↦₆₄ w4) ∗ ((o + 0x28#64) ↦₆₄ w5) ∗ ((o + 0x30#64) ↦₆₄ w6) ∗
  ((o + 0x38#64) ↦₆₄ w7) ∗ ((o + 0x40#64) ↦₆₄ w8) ∗ ((o + 0x48#64) ↦₆₄ w9) ∗ ((o + 0x50#64) ↦₆₄ w10) ∗
  ((o + 0x58#64) ↦₆₄ w11) ∗ ((o + 0x60#64) ↦₆₄ w12) ∗ ((o + 0x68#64) ↦₆₄ w13) ∗ ((o + 0x70#64) ↦₆₄ w14) ∗
  ((o + 0x78#64) ↦₆₄ w15) ∗ ((o + 0x80#64) ↦₆₄ w16) ∗ ((o + 0x88#64) ↦₆₄ w17) ∗ ((o + 0x90#64) ↦₆₄ w18) ∗
  ((o + 0x98#64) ↦₆₄ w19) ∗ ((o + 0xa0#64) ↦₆₄ w20) ∗ ((o + 0xa8#64) ↦₆₄ w21) ∗ ((o + 0xb0#64) ↦₆₄ w22) ∗
  ((o + 0xb8#64) ↦₆₄ w23) ∗ ((o + 0xc0#64) ↦₆₄ w24)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom
