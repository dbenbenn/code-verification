/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBase
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.Defs
import ProofLib.SepLogic.WPp
public meta import Lean -- shake: keep

/-!
# Instruction Decodes and Shared Step Lemmas for CLI `Authenticator::encode [local#3]`

Generates instruction decodes, defines `AuthEncode1*` contract predicates and `IsAuthEncodeEntry`,
and proves shared tag-push, length-computation, and epilogue steppers for
`prost::encoding::message::encode::<Authenticator, Vec<u8>> [local#3]` on `tripleRatchetProgAtExt`.
-/

public section

/-- Resolve `<P>Cli_decode_…` in the current environment if present, falling back to `<P>_decode_…`. -/
private meta def portCliPickCli (env : Lean.Environment) (opts : Lean.Options) (ns : Lean.Name)
    (od : List Lean.OpenDecl) (n : Lean.Name) : Lean.Name :=
  if (Lean.ResolveName.resolveGlobalName env opts ns od n).any (fun r => r.2.isEmpty) then n
  else match n with
    | .str q s => .str q (((s.replace "Cli_decode_" "_decode_").replace "Cli_rebase_fetch_" "_rebase_fetch_").replace "Cli_fetch_" "_fetch_")
    | _ => n

namespace CryptoVerification.SpqrV1.Auth

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec

open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.CodeLayout

open CryptoVerification.LibsignalTripleRatchet.Prost

open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm

open CryptoVerification.LibsignalSpqrV1

open CryptoVerification.SpqrV1.Alloc

open CryptoVerification.SpqrV1.Varint

open CryptoVerification.SpqrV1.ProtoRepr

open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (zeroExtend64_beq_zero32 hwVarintLen_eq_ofNat_varintLen_norm
   hwVarintLen_bvShift_eq_ofNat_varintLen_norm
   ule_self_64 ult_self_64
   ofNat_length_beq_zero_of_lt bv_bytesField_nonempty adds_no_overflow_of_eq)

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_beq_zero32 ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  ule_zero_64 ult_zero_64 ule_self_64 ult_self_64

/-! ## 1. Instruction Decode Lemmas & Symbol Names -/

/-- `prost::encoding::message::encode::<spqr::proto::pq_ratchet::Authenticator, alloc::vec::Vec<u8>> [local#3]` (`147` instructions). -/
abbrev _root_.CryptoVerification.Cli.SpqrV1.Auth.authEncode1Name : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::Authenticator, alloc::vec::Vec<u8>> [local#3]"

end CryptoVerification.SpqrV1.Auth
