/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.EpochDirectionBase
import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2Base
import LibsignalBinary.Proofs.SpqrV1.Auth.Encode1
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirection1
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp
public meta import Lean -- shake: keep

/-!
# CLI `prost::encoding::message::encode<EpochDirection> [local#3]` Verification

Proves stage lemmas and top-level `subroutine_ok` contracts for `EpochDirection` message encoding
on the CLI image.
-/

public section

private meta def portCliPickCli (env : Lean.Environment) (opts : Lean.Options) (ns : Lean.Name)
    (od : List Lean.OpenDecl) (n : Lean.Name) : Lean.Name :=
  if (Lean.ResolveName.resolveGlobalName env opts ns od n).any (fun r => r.2.isEmpty) then n
  else match n with
    | .str q s => .str q (((s.replace "Cli_decode_" "_decode_").replace "Cli_rebase_fetch_" "_rebase_fetch_").replace "Cli_fetch_" "_fetch_")
    | _ => n

namespace CryptoVerification.SpqrV1.Layout.L26

open Lean Meta Elab Tactic ProofLib

end CryptoVerification.SpqrV1.Layout.L26

namespace CryptoVerification.SpqrV1.Prost.MessageEncode

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout CryptoVerification.SpqrV1.Layout.L26
open CryptoVerification.LibsignalTripleRatchet.Prost CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc CryptoVerification.SpqrV1.Varint CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (ofNat_length_beq_zero_of_lt bv_bytesField_nonempty adds_no_overflow_of_eq)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 EncodedLen.ule_self_64 EncodedLen.ult_self_64
  zext64_trunc32_orr_1 zext64_trunc32_orr_100000001 zext64_orr_1_32

local macro "an" : tactic => `(tactic| simp only [arm64_norm, *])
local macro "an0" : tactic => `(tactic| simp only [arm64_norm])

private theorem sessionMemcpy_to_withStack {prog : Program} {pc : BitVec 64} (stk : Nat)
    (h : subroutine_ok prog pc sessionMemcpyRegionSpec) : subroutine_ok prog pc (withStack sessionMemcpyRegionSpec stk) :=
  subroutine_ok_refine_frame h
    (fun x R s0 hpre => ⟨x, stackAt s0.sp stk,
      by dsimp only [withStack, sessionMemcpyRegionSpec] at hpre ⊢; convert hpre using 1; ac_rfl,
      fun sf hpost => by dsimp only [withStack, sessionMemcpyRegionSpec] at hpost ⊢; convert hpost using 1; ac_rfl⟩)
    (fun _ _ _ _ hp => allowPanic_not_exited hp) (fun _ _ _ _ _ he => allowPanic_not_exited he) (fun _ _ _ _ _ _ ho => (allowPanic_not_exited ho).elim)

end CryptoVerification.SpqrV1.Prost.MessageEncode
