/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesPoly -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.DefsChunkedV1 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.CodeLayout
public import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- shake: keep
public meta import Lean -- shake: keep
public import ProofLib
public import ProofLib.ProgramReflection.Variant.TrapTransfer

/-!
# CLI `PolynomialDecoder::encoded_len` and `PolynomialEncoder::encoded_len` Leaf Proofs

Proves `polyDec_entry_pinned_ok_ext` and `polyEnc_entry_pinned_ok_ext` for the CLI `ProtoRepr`
`PolynomialDecoder` and `PolynomialEncoder` `encoded_len` routines.
-/

public section

private meta def portCliPickCli (env : Lean.Environment) (opts : Lean.Options) (ns : Lean.Name)
    (od : List Lean.OpenDecl) (n : Lean.Name) : Lean.Name :=
  if (Lean.ResolveName.resolveGlobalName env opts ns od n).any (fun r => r.2.isEmpty) then n
  else match n with
    | .str q s => .str q (((s.replace "Cli_decode_" "_decode_").replace "Cli_rebase_fetch_" "_rebase_fetch_").replace "Cli_fetch_" "_fetch_")
    | _ => n

namespace CryptoVerification.SpqrV1.ProtoRepr

open Arm64 ProofLib CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalSpqrV1

open EncodedLen

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

set_option linter.unusedVariables false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_beq_zero32 ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  zext64_truncate32 ule_zero_64 ult_zero_64 ule_self_64 ult_self_64

/-! ## Shared Helpers for `repeated bytes` (`Vec<Vec<u8>>`) Loops -/

private theorem pair_fetch_entry {f : BitVec 64 → Option Instr}
    {a1 a2 entry : BitVec 64} (hfn : a1 = entry ∨ a2 = entry) {ins : Instr}
    (h1 : f a1 = some ins) (h2 : f a2 = some ins) :
    f entry = some ins := by
  rcases hfn with rfl | rfl <;> assumption

private theorem pair_fetch_add {f : BitVec 64 → Option Instr}
    {a1 a2 entry : BitVec 64} (hfn : a1 = entry ∨ a2 = entry) {k : Nat} {ins : Instr}
    (h1 : f (a1 + BitVec.ofNat 64 k) = some ins)
    (h2 : f (a2 + BitVec.ofNat 64 k) = some ins) :
    f (entry + BitVec.ofNat 64 k) = some ins := by
  rcases hfn with rfl | rfl <;> assumption

end CryptoVerification.SpqrV1.ProtoRepr
