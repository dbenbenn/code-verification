/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.Defs
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Prog -- proof-setup: allow-public-import
public import ProofLib.SepLogic.CodeLookup
public meta import ProofLib.SepLogic.CodeLookup
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked59_71
public import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- shake: keep
public meta import Lean -- shake: keep
public import ProofLib
public import ProofLib.ProgramReflection.Variant.TrapTransfer

/-!
# CLI 59- and 71-Instruction Unchunked `encoded_len` Leaf Proofs

Proves `subroutine_ok` contracts for the 59-instruction (`KeysUnsampled`, `NoHeaderReceived`,
`Ct2Sent`) and 71-instruction (`EkSent`, `HeaderReceived`) unchunked `V1State` leaf `encoded_len`
routines on the CLI image.
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

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_beq_zero32 ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  zext64_truncate32 ule_zero_64 ult_zero_64 ule_self_64 ult_self_64

/-! ## Part 1: 59-Instruction Group (`KeysUnsampled`, `NoHeaderReceived`, `Ct2Sent`) -/

private theorem subroutine_ok_repack {G1 G2 : Type} {prog : Program} {entry : BitVec 64}
    {S1 : Spec G1} {S2 : Spec G2} (f : G2 → G1)
    (hpre : ∀ x s, S2.pre x s = S1.pre (f x) s)
    (hpost : ∀ x s0 sf, S2.post x s0 sf = S1.post (f x) s0 sf)
    (hok : subroutine_ok prog entry S1)
    (honPanic : ∀ x s0 sf, S2.onPanic x s0 sf = S1.onPanic (f x) s0 sf := by intros; rfl)
    (honExit : ∀ x c s0 sf, S2.onExit x c s0 sf = S1.onExit (f x) c s0 sf := by intros; rfl)
    (honOom : ∀ x s0 sf, S2.onOom x s0 sf = S1.onOom (f x) s0 sf := by intros; rfl) :
    subroutine_ok prog entry S2 := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre0 hsp => ?_
  rw [hpre] at hpre0
  refine hok.mono_outcome (f x) R s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost0⟩ | ⟨hpan, hmpan⟩ | ⟨code, hex, hmex⟩ | ⟨hoom, hmoom⟩
  · rw [← hpost] at hpost0
    exact Or.inl ⟨hret, hcc, hpost0⟩
  · rw [← honPanic] at hmpan
    exact Or.inr (Or.inl ⟨hpan, hmpan⟩)
  · rw [← honExit] at hmex
    exact Or.inr (Or.inr (Or.inl ⟨code, hex, hmex⟩))
  · rw [← honOom] at hmoom
    exact Or.inr (Or.inr (Or.inr ⟨hoom, hmoom⟩))

end CryptoVerification.SpqrV1.ProtoRepr
