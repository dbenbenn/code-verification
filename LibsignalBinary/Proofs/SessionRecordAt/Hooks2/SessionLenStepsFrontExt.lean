/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionLenAux.StepsFront -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Defs
public import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionLenAux.Pure -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Record.Serialization.ChainLenAux.Pure
import Aesop.BuiltinRules
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Simps
import Mathlib.Tactic.ToAdditive
import Mathlib.Tactic.ToDual
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionLenAux.StepsChains
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

public section

set_option autoImplicit false

/-!
# `<SessionStructure as prost::Message>::encoded_len`: Prologue and Tags 1–7 (`+0x000..+0x1bc`)

Verifies the prologue, protobuf tags 1–5 (`+0x000..+0x110`), tag 6 (`sender_chain`, `272..352`), and
tag 7 (`receiver_chains`, `352..444`) of `SessionStructure::encoded_len` (`0x25fd0`) on `SP2Ext`.
-/

namespace CryptoVerification.E2E.Record.Serialization.SessionLenAux

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.E2E.Record CryptoVerification.E2E.Record.Serialization
open Proofs.libsignal.Hooks2

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm]
  bv_sub_add_lit BitVec.toNat_zero
  sessHwVarintLen_eq_encodeVarint_length
  sessHwVarintLen_bvShift_eq_encodeVarint_length
  Prost.ofNat_countLeadingZeros_64
  Prost.ofNat_countLeadingZeros_32
  Prost.truncate32_ofNat64
  sess_truncate32_zext64_lsr6
  sessHwVarintLen_w32_eq_encodeVarint_length
  sessHwVarintLen_w32_natShift_eq_encodeVarint_length
  Prost.noneCap_add_one_beq_zero
  Prost.noneCap_add_one_bne_zero
  Prost.optU32Tag_beq_one
  Prost.optU32Tag_bne_one
  Prost.zext64_optU32Tag_truncate32
  sess_ule_zero_64
  sess_ult_zero_64

@[local simp, local arm64_norm]
theorem add_neg64_eq_sub64' (x : BitVec 64) :
    x + bv% (2 ^ 64 - 64) = x - 64#64 := by
  bv_omega

section Placed

abbrev call_protoChainLen_placed_ext := @call_protoChainLen_placed
abbrev call_chainLen_placed_ext := @call_chainLen_placed
abbrev step_sessLen_f1_placed_ext := @step_sessLen_f1_placed
abbrev step_sessLen_f2_placed_ext := @step_sessLen_f2_placed
abbrev step_sessLen_f3_placed_ext := @step_sessLen_f3_placed
abbrev step_sessLen_f4_placed_ext := @step_sessLen_f4_placed

end Placed

end CryptoVerification.E2E.Record.Serialization.SessionLenAux
