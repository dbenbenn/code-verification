/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.Defs
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.Decodes
import ProofLib.SepLogic.WPp
public meta import Lean
public meta import ProofLib.GenDecodes
public meta import ProofLib.ProgramReflection
public meta import ProofLib.SepLogic.CodeLookup
public meta import ProofLib.VCGen
import LibsignalBinary.Proofs.CodeLayout

/-!
# Phase 1a (`0x6d010 .. 0x6d18c/0x6d1bc`): Prologue and `Option<VersionNegotiation>::encoded_len`

Proves symbolic execution of the prologue and inline `Option<VersionNegotiation>::encoded_len`
in `<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec`:
1. Prologue (`+0 .. +48`, `0x6d010 .. 0x6d040`): allocates the 144-byte frame (`sp - 144#64`),
   saves `x19..x28, x29, x30` at `[sp - 96#64, sp)`, sets `x29 = sp - 96#64`, `x20 = a`,
   `x27 = sret`, and loads `x25 = optVersionNegCap g.vn st.versionNegotiation`.
2. Inline `Option<VersionNegotiation>::encoded_len` (`+48 .. +380/+428`, `0x6d040 .. 0x6d18c/0x6d1bc`):
   computes `x21 = BitVec.ofNat 64 (optVersionNegotiationPBFieldEncodedLen st.versionNegotiation)`.
-/

public section

namespace CryptoVerification.SpqrV1.Prost.EncodeToVec

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (ule_self_64 ult_self_64
   ofNat_length_beq_zero_of_lt bv_u32VarintField_nonzero bv_bytesField_nonempty
   bv_add_ofNat_comm bv_add_ofNat_eq adds_no_overflow_of_eq cmp_ls_false_of_lt)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 ule_self_64 ult_self_64

/-! ## Instruction Fetch Infrastructure & Shared `SepWPp` Helpers -/

theorem encodeToVec_fetch_entry {prog : Program} {name : String}
    {entry : BitVec 64} (hfn : prog.fnAddr name = entry) {ins : Instr}
    (h : prog.fetch (prog.fnAddr name) = some ins) :
    prog.fetch entry = some ins :=
  hfn ▸ h

theorem encodeToVec_fetch_add {prog : Program} {name : String}
    {entry : BitVec 64} (hfn : prog.fnAddr name = entry) {k : Nat} {ins : Instr}
    (h : prog.fetch (prog.fnAddr name + BitVec.ofNat 64 k) = some ins) :
    prog.fetch (entry + BitVec.ofNat 64 k) = some ins :=
  hfn ▸ h

end CryptoVerification.SpqrV1.Prost.EncodeToVec
