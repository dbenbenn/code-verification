/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Statements -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.AllocContracts4KExt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPrologue -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.TripleRatchet.Wire.NewMacAndBoxes

/-!
# `<SignalMessage>::new` Segment 3 (`+0x3dc .. +0x5d8`)

Proves Phase 3 segment lemmas for `<SignalMessage>::new`: `compute_mac` and 8-byte MAC append,
ciphertext cloning, and deallocation of temporary ratchet-key and ciphertext buffers.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalTripleRatchet.ExtSignalMsgNewSeg3

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.Cli.LibsignalSpqrV1.M4
open CryptoVerification.InImageLift
open ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  sp_sub_96_sub_56 sp_sub_96_sub_64 sp_sub_96_sub_72 sp_sub_96_sub_80
  add_one_eq_zero_iff_noneCap add_one_beq_zero_iff_noneCap add_one_bne_zero_iff_ne_noneCap
  bv_add_8_sub_self
attribute [local simp]
  sp_sub_96_sub_56 sp_sub_96_sub_64 sp_sub_96_sub_72 sp_sub_96_sub_80
  add_one_eq_zero_iff_noneCap add_one_beq_zero_iff_noneCap add_one_bne_zero_iff_ne_noneCap
  bv_add_8_sub_self

/-! ## `4K` Callee Discharges -/

section FnOffShieldComputeMac
attribute [local irreducible] _root_.Arm64.Program.fnOff

end FnOffShieldComputeMac

/-! ## Clone `ciphertext` (`+0x440 → +0x46c / +0x55c`) -/

end CryptoVerification.Cli.LibsignalTripleRatchet.ExtSignalMsgNewSeg3
