/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Decodes -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.VersionNegPhase -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodedLenVn
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesVnEncode
import ProofLib.SepLogic.WPp
public meta import Lean -- shake: keep
import LibsignalBinary.Proofs.CodeLayout

public section

set_option autoImplicit false

/-!
# `spqr::send::<signal_session_ratchet::Coins>` Phase 3c (`+4996..+5604`): `Option<VersionNegotiation>` Encoding

Proves the inlined `Option<VersionNegotiation>` encoding phase (`+4996..+5604`) of
`spqr::send::<signal_session_ratchet::Coins>`, parameterized over bounded-stack `memcpy`.
-/

private meta def portCliPickCli (env : Lean.Environment) (opts : Lean.Options) (ns : Lean.Name)
    (od : List Lean.OpenDecl) (n : Lean.Name) : Lean.Name :=
  if (Lean.ResolveName.resolveGlobalName env opts ns od n).any (fun r => r.2.isEmpty) then n
  else match n with
    | .str q s => .str q (((s.replace "Cli_decode_" "_decode_").replace "Cli_rebase_fetch_" "_rebase_fetch_").replace "Cli_fetch_" "_fetch_")
    | _ => n

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen CryptoVerification.SpqrV1.Prost.EncodeToVec

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

private theorem etvMemcpy_to_withStack {prog : Program} {pc : BitVec 64} (stk : Nat)
    (h : subroutine_ok prog pc etvMemcpyRegionSpec) :
    subroutine_ok prog pc (withStack etvMemcpyRegionSpec stk) := by
  apply subroutine_ok.of_codeLoaded
  intro x R s hpc hrun hpre hal _
  have hpre' : s.mem ⊨ etvMemcpyRegionSpec.pre x s ∗ (stackAt s.sp stk ∗ R) := by
    dsimp only [withStack, etvMemcpyRegionSpec] at hpre ⊢
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
  exact subroutine_ok.mono_outcome h x (stackAt s.sp stk ∗ R) s hpc hrun hpre' hal fun sf hout => by
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withStack, etvMemcpyRegionSpec] at hpost ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
    · exact (ProofLib.allowPanic_not_exited hpan).elim
    · exact (ProofLib.allowPanic_not_exited hex).elim
    · exact (ProofLib.allowPanic_not_exited hoom).elim

end CryptoVerification.SpqrV1.Top.Send
