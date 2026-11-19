/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhase -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.Decodes
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodedLenVn
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1ChainFields
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# Phase 2c (`0x6d4cc .. 0x6d6dc`): `Option<Chain>` Loop and Top-Level Composition

Proves the repeated `ChainEpochPB` loop (`+1376 .. +1552`, `0x6d570 .. 0x6d620`) and
composes all `ChainPB` field steps into `step_encodeToVec_chain`
(`+1212 .. +1740`, `0x6d4cc .. 0x6d6dc`).
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

/-! ## 1. Repeated `ChainEpochPB` Loop (`+1376 .. +1552`, `0x6d570 .. 0x6d620`) -/

theorem bv_lsl7_sub_lsl4_eq_mul_112 (n : Nat) :
    (BitVec.ofNat 64 n <<< 7#64) - (BitVec.ofNat 64 n <<< 4#64) = BitVec.ofNat 64 (n * 112) ∧
    (BitVec.ofNat 64 n <<< 7) - (BitVec.ofNat 64 n <<< 4) = BitVec.ofNat 64 (n * 112) ∧
    (BitVec.ofNat 64 n <<< 7#64) - (BitVec.ofNat 64 n <<< 4) = BitVec.ofNat 64 (n * 112) ∧
    (BitVec.ofNat 64 n <<< 7) - (BitVec.ofNat 64 n <<< 4#64) = BitVec.ofNat 64 (n * 112) := by
  have h1 : ∀ x : BitVec 64, (x <<< 7#64) - (x <<< 4#64) = x * 112#64 := by intro x; bv_bits
  have h2 : ∀ x : BitVec 64, (x <<< 7) - (x <<< 4) = x * 112#64 := by intro x; bv_bits
  have h3 : ∀ x : BitVec 64, (x <<< 7#64) - (x <<< 4) = x * 112#64 := by intro x; bv_bits
  have h4 : ∀ x : BitVec 64, (x <<< 7) - (x <<< 4#64) = x * 112#64 := by intro x; bv_bits
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h1, ← BitVec.ofNat_mul]
  · rw [h2, ← BitVec.ofNat_mul]
  · rw [h3, ← BitVec.ofNat_mul]
  · rw [h4, ← BitVec.ofNat_mul]

private theorem arrayAt_epoch_cons (A : RustAlloc) (p : BitVec 64)
    (ep : ChainEpochPB) (rest : List ChainEpochPB) :
    arrayAt (fun e addr => chainEpochPBAt A addr e) 112 p (ep :: rest) =
      (chainEpochPBAt A p ep ∗
        arrayAt (fun e addr => chainEpochPBAt A addr e) 112 (p + 112#64) rest) := rfl

private theorem vecBuf_epoch_eq_of_ne_zero (A : RustAlloc) {cap ptr : BitVec 64}
    (links : List ChainEpochPB) (hcne : cap ≠ 0) :
    vecBuf A 112 8 (fun ep addr => chainEpochPBAt A addr ep) cap ptr links =
      (⌜links.length ≤ cap.toNat ∧ cap.toNat * 112 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        A.live ptr (cap.toNat * 112) 8 ∗
        arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 ptr links ∗
        memRegion (ptr + BitVec.ofNat 64 (links.length * 112)) ((cap.toNat - links.length) * 112)) := by
  unfold vecBuf; simp only [hcne, ↓reduceIte]

private theorem mul_112_ofNat_beq_zero_false {n : Nat} (hn : 0 < n) (hlt : n * 112 < 2 ^ 64) :
    (BitVec.ofNat 64 (n * 112) == 0#64) = false ∧ (BitVec.ofNat 64 (n * 112) != 0#64) = true := by
  have hne : BitVec.ofNat 64 (n * 112) ≠ 0#64 := by
    intro h
    have h1 : (BitVec.ofNat 64 (n * 112)).toNat = (0#64 : BitVec 64).toNat :=
      congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at h1
    change n * 112 = 0 at h1
    omega
  exact ⟨beq_eq_false_iff_ne.mpr hne, bne_iff_ne.mpr hne⟩

private theorem mul_112_ofNat_beq_112_false {n : Nat} (hn : 2 ≤ n) (hlt : n * 112 < 2 ^ 64) :
    (BitVec.ofNat 64 (n * 112) == 112#64) = false := by
  have hne : BitVec.ofNat 64 (n * 112) ≠ 112#64 := by
    intro h
    have h1 : (BitVec.ofNat 64 (n * 112)).toNat = (112#64 : BitVec 64).toNat :=
      congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at h1
    change n * 112 = 112 at h1
    omega
  exact beq_eq_false_iff_ne.mpr hne

private theorem ofNat_beq_zero_false {n : Nat} (hn : 0 < n) (hlt : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 0#64) = false ∧ (BitVec.ofNat 64 n != 0#64) = true := by
  have hne : BitVec.ofNat 64 n ≠ 0#64 := by
    intro h
    have h1 : (BitVec.ofNat 64 n).toNat = (0#64 : BitVec 64).toNat :=
      congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at h1
    change n = 0 at h1
    omega
  exact ⟨beq_eq_false_iff_ne.mpr hne, bne_iff_ne.mpr hne⟩

/-- Step `+1464 .. +1520/+1404` (`0x6d5c8 .. 0x6d58c`): encodes `ep.send` (`tag = 1`) and `ep.recv` (`tag = 2`). -/

theorem chainLinksBodiesEncodedLen_bounds (ep : ChainEpochPB) (rest : List ChainEpochPB)
    (h : chainLinksBodiesEncodedLen (ep :: rest) < 2 ^ 64) :
    chainEpochPBEncodedLen ep < 2 ^ 64 ∧ chainLinksBodiesEncodedLen rest < 2 ^ 64 := by
  rw [chainLinksBodiesEncodedLen_cons] at h
  dsimp only [chainEpochPBBodyEncodedLen] at h
  omega

/-- Base case (`rest = []`) of the repeated `ChainEpochPB` loop (`+1416 .. +1552`). -/

private theorem mul_112_cons_sub (ep ep2 : ChainEpochPB) (rest2 : List ChainEpochPB)
    (hmul : (ep :: ep2 :: rest2).length * 112 < 2 ^ 64) :
    (ep2 :: rest2).length * 112 < 2 ^ 64 ∧
      BitVec.ofNat 64 ((ep :: ep2 :: rest2).length * 112) - 112#64 =
        BitVec.ofNat 64 ((ep2 :: rest2).length * 112) ∧
      (BitVec.ofNat 64 ((ep :: ep2 :: rest2).length * 112) == 112#64) = false := by
  have hmul_eq : (ep :: ep2 :: rest2).length * 112 = (ep2 :: rest2).length * 112 + 112 := by
    simp only [List.length_cons]; omega
  refine ⟨by omega, ?_, mul_112_ofNat_beq_112_false (by simp) hmul⟩
  rw [hmul_eq, BitVec.ofNat_add]; bv_omega

private theorem chain_links_cons_fit {cap_nat : Nat} (bs l1 l2 : List (BitVec 8))
    (h : bs.length + (l1 ++ l2).length ≤ cap_nat) :
    bs.length + l1.length ≤ cap_nat ∧ (bs ++ l1).length + l2.length ≤ cap_nat := by
  simp only [List.length_append] at h ⊢
  omega



end CryptoVerification.SpqrV1.Prost.EncodeToVec
