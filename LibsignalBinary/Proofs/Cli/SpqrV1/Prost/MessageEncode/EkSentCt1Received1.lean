/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.UnchunkedBase
public import LibsignalBinary.Proofs.Cli.SpqrV1.Auth.EncodeBase
public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.Defs
public import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2Base
import LibsignalBinary.Proofs.Cli.SpqrV1.Auth.Encode1
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked82_93
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp
public meta import Lean -- shake: keep

/-!
# CLI `prost::encoding::message::encode<EkSentCt1Received> [local#3]` Verification

Proves stage lemmas and top-level `subroutine_ok` contracts
(`ek_sent_ct1_received_encode_1_pinned_ok_ext`, `ek_sent_ct1_received_encode_1_pinned_ok_ext_x`)
for `EkSentCt1Received` message encoding on the CLI image.
-/

public section

private meta def portCliPickCli (env : Lean.Environment) (opts : Lean.Options) (ns : Lean.Name)
    (od : List Lean.OpenDecl) (n : Lean.Name) : Lean.Name :=
  if (Lean.ResolveName.resolveGlobalName env opts ns od n).any (fun r => r.2.isEmpty) then n
  else match n with
    | .str q s => .str q (((s.replace "Cli_decode_" "_decode_").replace "Cli_rebase_fetch_" "_rebase_fetch_").replace "Cli_fetch_" "_fetch_")
    | _ => n

namespace CryptoVerification.SpqrV1.Prost.MessageEncode

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalTripleRatchet.Prost CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc CryptoVerification.SpqrV1.Varint CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (zeroExtend64_beq_zero32 hwVarintLen_eq_ofNat_varintLen_norm
   hwVarintLen_bvShift_eq_ofNat_varintLen_norm ule_self_64 ult_self_64
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

local macro "an" : term => `(by simp only [arm64_norm, *])

local macro "cs_step " hcs:term:max hinv:term:max : term =>
  `(UnchunkedEncodeCalleeSaved.step $hcs (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) $hinv)

private theorem sessionMemcpy_to_withStack {prog : Program} {pc : BitVec 64} (stk : Nat)
    (h : subroutine_ok prog pc sessionMemcpyRegionSpec) : subroutine_ok prog pc (withStack sessionMemcpyRegionSpec stk) :=
  subroutine_ok_refine_frame h
    (fun x R s0 hpre => ⟨x, stackAt s0.sp stk,
      by dsimp only [withStack, sessionMemcpyRegionSpec] at hpre ⊢; convert hpre using 1; ac_rfl,
      fun sf hpost => by dsimp only [withStack, sessionMemcpyRegionSpec] at hpost ⊢; convert hpost using 1; ac_rfl⟩)
    (fun _ _ _ _ hp => allowPanic_not_exited hp) (fun _ _ _ _ _ he => allowPanic_not_exited he) (fun _ _ _ _ _ _ ho => (allowPanic_not_exited ho).elim)

private theorem vecU8At_expose_src_of_ne_nil_xa (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hne : bs ≠ []) (hle : bs.length ≤ cap.toNat) :
    vecU8At A a cap ptr bs = (ptr ↦ₛ bs) ∗ (vecHeader a cap ptr (BitVec.ofNat 64 bs.length) ∗
      ⌜ptr ≠ 0 ∧ bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63⌝ ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗ A.live ptr cap.toNat 1) := by
  have hpos := List.length_pos_of_ne_nil hne
  have hcap_ne : cap ≠ 0 := by intro h0; subst h0; change bs.length ≤ 0 at hle; omega
  rw [vecU8At_eq_header_sep_buf, vecU8Buf]; simp only [hcap_ne, ↓reduceIte]; ac_rfl

end CryptoVerification.SpqrV1.Prost.MessageEncode
