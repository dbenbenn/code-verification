/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExact -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeRepeatedCommon -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp
public meta import Lean -- shake: keep

/-!
# Verification of `prost::encoding::bytes::encode_repeated [local#3]`

Proves `encode_repeated::<Vec<u8>, Vec<u8>> [local#3]` on the CLI image, parameterized over
bounded-stack `memcpy` and `elems.length < 2 ^ 59`.
-/

public section

private meta def portCliPickCli (env : Lean.Environment) (opts : Lean.Options) (ns : Lean.Name)
    (od : List Lean.OpenDecl) (n : Lean.Name) : Lean.Name :=
  if (Lean.ResolveName.resolveGlobalName env opts ns od n).any (fun r => r.2.isEmpty) then n
  else match n with
    | .str q s => .str q (((s.replace "Cli_decode_" "_decode_").replace "Cli_rebase_fetch_" "_rebase_fetch_").replace "Cli_fetch_" "_fetch_")
    | _ => n

namespace CryptoVerification.SpqrV1.Varint

open Arm64 ProofLib CryptoVerification.RustHeap
  CryptoGames.LibsignalSession CryptoVerification.LibsignalTripleRatchetRepr
  CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
  CryptoVerification.LibsignalProtoCodec
  CryptoVerification.LibsignalTripleRatchet.Prost
  CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
  CryptoVerification.CodeLayout
  CryptoVerification.SpqrV1.Alloc
  CryptoVerification.SpqrV1.Prost.EncodeToVec

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
  encodeVarint encodeBytesField encodeRepeatedBytes

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace EncodeRepeated1

private theorem sessionMemcpy_to_withStack {prog : Program} {pc : BitVec 64} (stk : Nat)
    (h : subroutine_ok prog pc sessionMemcpyRegionSpec) :
    subroutine_ok prog pc (withStack sessionMemcpyRegionSpec stk) :=
  subroutine_ok_refine_frame h
    (fun x R s0 hpre => ⟨x, stackAt s0.sp stk,
      by dsimp only [withStack, sessionMemcpyRegionSpec] at hpre ⊢; convert hpre using 1; ac_rfl,
      fun sf hpost => by dsimp only [withStack, sessionMemcpyRegionSpec] at hpost ⊢; convert hpost using 1; ac_rfl⟩)
    (fun _ _ _ _ hp => allowPanic_not_exited hp)
    (fun _ _ _ _ _ he => allowPanic_not_exited he)
    (fun _ _ _ _ _ _ ho => (allowPanic_not_exited ho).elim)

end EncodeRepeated1

end CryptoVerification.SpqrV1.Varint
