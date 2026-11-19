/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclCode -- proof-setup: allow-public-import
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclContracts -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Ref
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Cells
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256RoundDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Math
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclUpdateFetch
meta import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Cells
meta import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256RoundDefs

/-!
# Machine-code proof for `libcrux_sha2::hacl::sha256_update`

Verifies block `1` (`2,074` words) of `libcrux_sha2::hacl::sha256_update`, proving
`sha256Update_raw_subroutineOk` and `sha256Update_subroutineOk`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclUpdateStep

open Arm64 ProofLib
open CryptoGames.HMAC (ShaState)
open CryptoVerification.LibsignalHmac (shaStateBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Ref
  (sha256K sha256SmallSigma0 sha256SmallSigma1 sha256CompressBlock)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Cells
  (readLE32 pointsToBytes_64_eq_cells32 cells_sub_elim SepWP.rw_top_reg)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256RoundDefs
  (sha256Maj_eq_and_xor sha256Maj_eq_and_xor_comm
   sha256BigSigma0_eq sha256BigSigma0_eq_13_22_2
   sha256BigSigma1_eq sha256BigSigma1_eq_11_25_6
   sha256W sha256W_ge_16 sha256W_init_off
   sha256T1 sha256T1_eq1 sha256T1_eq2
   sha256T2 sha256T2_eq
   sha256A sha256E sha256A_0 sha256A_1 sha256A_2 sha256A_3
   sha256E_0 sha256E_1 sha256E_2 sha256E_3
   sha256E_from_t1 sha256A_from_t1_t2 sha256Final4
   sha256CompressBlock_eq_sha256AE)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Math
  (sha256CompressState sha256CompressState_toList pointsToBytes_shaStateBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclCode
  (libcruxHmacLib HaclPlacement haclMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclContracts
  (HaclInProg withHaclPreserved subroutine_ok_of_pure_block sha256UpdateRawSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclUpdateFetch
  (haclPC1 haclPl1 haclPC1_eq_blockProgram haclPl1_base)

arm64_proof_prelude

/-! ## 1. 160-Byte Stack Frame Elimination & Recombination -/

private theorem stackFrame160_elim {prog : Program} {target_pc : BitVec 64}
    {s s0 : State} {R : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : BitVec 64),
      SepWP prog target_pc s
        (R ∗
         ((s0.sp - 160#64) ↦₆₄ v1) ∗ ((s0.sp - 152#64) ↦₆₄ v2) ∗ ((s0.sp - 144#64) ↦₆₄ v3) ∗
         ((s0.sp - 136#64) ↦₆₄ v4) ∗ ((s0.sp - 128#64) ↦₆₄ v5) ∗ ((s0.sp - 120#64) ↦₆₄ v6) ∗
         ((s0.sp - 112#64) ↦₆₄ v7) ∗ ((s0.sp - 104#64) ↦₆₄ v8) ∗ ((s0.sp - 96#64) ↦₆₄ v9) ∗
         ((s0.sp - 88#64) ↦₆₄ v10) ∗ ((s0.sp - 80#64) ↦₆₄ v11) ∗ ((s0.sp - 72#64) ↦₆₄ v12) ∗
         ((s0.sp - 64#64) ↦₆₄ v13) ∗ ((s0.sp - 56#64) ↦₆₄ v14) ∗ ((s0.sp - 48#64) ↦₆₄ v15) ∗
         ((s0.sp - 40#64) ↦₆₄ v16) ∗ ((s0.sp - 32#64) ↦₆₄ v17) ∗ ((s0.sp - 24#64) ↦₆₄ v18) ∗
         ((s0.sp - 16#64) ↦₆₄ v19) ∗ ((s0.sp - 8#64) ↦₆₄ v20)) post oom) :
    SepWP prog target_pc s (R ∗ stackFrame s0 160) post oom := by
  have hst : stackFrame s0 160 = cells (s0.sp - BitVec.ofNat 64 160) 20 :=
    stackAt_eq_cells s0.sp 20 (by decide)
  rw [hst]
  repeat (apply cells_sub_elim (by decide) (by decide); intro _)
  rename_i v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
  have h0 := h v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
  simpa only [Nat.reduceSub, cells_zero, sepConj_emp, BitVec.ofNat_eq_ofNat, sepConj_assoc] using h0

private theorem stackFrame160_entails (s0 : State)
    (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : BitVec 64) :
    (((s0.sp - 160#64) ↦₆₄ v1) ∗ ((s0.sp - 152#64) ↦₆₄ v2) ∗ ((s0.sp - 144#64) ↦₆₄ v3) ∗
     ((s0.sp - 136#64) ↦₆₄ v4) ∗ ((s0.sp - 128#64) ↦₆₄ v5) ∗ ((s0.sp - 120#64) ↦₆₄ v6) ∗
     ((s0.sp - 112#64) ↦₆₄ v7) ∗ ((s0.sp - 104#64) ↦₆₄ v8) ∗ ((s0.sp - 96#64) ↦₆₄ v9) ∗
     ((s0.sp - 88#64) ↦₆₄ v10) ∗ ((s0.sp - 80#64) ↦₆₄ v11) ∗ ((s0.sp - 72#64) ↦₆₄ v12) ∗
     ((s0.sp - 64#64) ↦₆₄ v13) ∗ ((s0.sp - 56#64) ↦₆₄ v14) ∗ ((s0.sp - 48#64) ↦₆₄ v15) ∗
     ((s0.sp - 40#64) ↦₆₄ v16) ∗ ((s0.sp - 32#64) ↦₆₄ v17) ∗ ((s0.sp - 24#64) ↦₆₄ v18) ∗
     ((s0.sp - 16#64) ↦₆₄ v19) ∗ ((s0.sp - 8#64) ↦₆₄ v20))
    ⊢ stackFrame s0 160 := by
  have hst : stackFrame s0 160 = cells (s0.sp - BitVec.ofNat 64 160) 20 :=
    stackAt_eq_cells s0.sp 20 (by decide)
  rw [hst]
  change (((s0.sp - BitVec.ofNat 64 160) ↦₆₄ v1) ∗
    (((s0.sp - BitVec.ofNat 64 152) ↦₆₄ v2) ∗ (((s0.sp - BitVec.ofNat 64 144) ↦₆₄ v3) ∗
    (((s0.sp - BitVec.ofNat 64 136) ↦₆₄ v4) ∗ (((s0.sp - BitVec.ofNat 64 128) ↦₆₄ v5) ∗
    (((s0.sp - BitVec.ofNat 64 120) ↦₆₄ v6) ∗ (((s0.sp - BitVec.ofNat 64 112) ↦₆₄ v7) ∗
    (((s0.sp - BitVec.ofNat 64 104) ↦₆₄ v8) ∗ (((s0.sp - BitVec.ofNat 64 96) ↦₆₄ v9) ∗
    (((s0.sp - BitVec.ofNat 64 88) ↦₆₄ v10) ∗ (((s0.sp - BitVec.ofNat 64 80) ↦₆₄ v11) ∗
    (((s0.sp - BitVec.ofNat 64 72) ↦₆₄ v12) ∗ (((s0.sp - BitVec.ofNat 64 64) ↦₆₄ v13) ∗
    (((s0.sp - BitVec.ofNat 64 56) ↦₆₄ v14) ∗ (((s0.sp - BitVec.ofNat 64 48) ↦₆₄ v15) ∗
    (((s0.sp - BitVec.ofNat 64 40) ↦₆₄ v16) ∗ (((s0.sp - BitVec.ofNat 64 32) ↦₆₄ v17) ∗
    (((s0.sp - BitVec.ofNat 64 24) ↦₆₄ v18) ∗ (((s0.sp - BitVec.ofNat 64 16) ↦₆₄ v19) ∗
    ((s0.sp - BitVec.ofNat 64 8) ↦₆₄ v20)))))))))))))))))))) ⊢ _
  repeat (refine cells_sub_succ_entails _ _ ?_ (by decide) (by decide))
  dsimp only [Nat.reduceSub]
  rw [cells_sub_succ s0.sp 8 1 (by decide) (by decide)]
  exact Entails.sepExists_right v20 (by
    dsimp only [Nat.reduceSub]
    rw [cells_zero, sepConj_emp]
    exact Entails.refl _)

/-! ## 2. HACL SHA-256 Instruction-AST Folding Lemmas -/

private theorem bv32_xor_left_comm (a b c : BitVec 32) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← BitVec.xor_assoc, BitVec.xor_comm a b, BitVec.xor_assoc]

private theorem rotateRight32_eq_rotateLeft32 (x : BitVec 32) (r l : Nat)
    (hr : r < 32 := by decide) (hl : l < 32 := by decide)
    (h1 : 32 - r = l := by rfl) (h2 : 32 - l = r := by rfl) :
    x.rotateRight r = x.rotateLeft l := by
  rw [BitVec.rotateRight_eq_rotateRightAux_of_lt hr,
      BitVec.rotateLeft_eq_rotateLeftAux_of_lt hl]
  unfold BitVec.rotateRightAux BitVec.rotateLeftAux
  rw [h1, h2, BitVec.or_comm]

private theorem setWidth32_append_ushiftRight_eq_rotateLeft (x : BitVec 32) (r l : Nat)
    (hl : l < 32 := by decide) (hrl : r + l = 32 := by rfl) :
    BitVec.setWidth 32 ((x ++ x) >>> r) = x.rotateLeft l := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append,
      BitVec.getLsbD_rotateLeft_of_le hl]
  simp only [hi, decide_true, Bool.true_and]
  by_cases hlt : i < l
  · have hlt2 : r + i < 32 := by omega
    simp only [hlt, hlt2, ↓reduceIte]
    congr 1
    omega
  · have hlt2 : ¬(r + i < 32) := by omega
    simp only [hlt, hlt2, ↓reduceIte]
    congr 1
    omega

private theorem extr32_18 (x : BitVec 32) :
    BitVec.setWidth 32 ((x ++ x) >>> 18) = x.rotateRight 18 := by
  rw [setWidth32_append_ushiftRight_eq_rotateLeft x 18 14,
      ← rotateRight32_eq_rotateLeft32 x 18 14]

private theorem extr32_19 (x : BitVec 32) :
    BitVec.setWidth 32 ((x ++ x) >>> 19) = x.rotateRight 19 := by
  rw [setWidth32_append_ushiftRight_eq_rotateLeft x 19 13,
      ← rotateRight32_eq_rotateLeft32 x 19 13]

private theorem sha256SmallSigma0_eq_18_3_7 (x : BitVec 32) :
    ((BitVec.setWidth 32 ((x ++ x) >>> 18) ^^^ (x >>> 3)) ^^^ x.rotateRight 7) =
      sha256SmallSigma0 x := by
  unfold sha256SmallSigma0
  rw [extr32_18]
  simp only [BitVec.xor_comm, bv32_xor_left_comm]

private theorem sha256SmallSigma1_eq_19_10_17 (x : BitVec 32) :
    ((BitVec.setWidth 32 ((x ++ x) >>> 19) ^^^ (x >>> 10)) ^^^ x.rotateRight 17) =
      sha256SmallSigma1 x := by
  unfold sha256SmallSigma1
  rw [extr32_19]
  simp only [BitVec.xor_comm, bv32_xor_left_comm]

private theorem haclW_step1 (block : List (BitVec 8)) (i15 i16 i7 i2 i : Nat)
    (h16 : 16 ≤ i := by decide) (hi64 : i < 64 := by decide)
    (hi16 : i - 16 = i16 := by decide) (hi15 : i - 15 = i15 := by decide)
    (hi7 : i - 7 = i7 := by decide) (hi2 : i - 2 = i2 := by decide) :
    ((((BitVec.setWidth 32 ((sha256W block i15 ++ sha256W block i15) >>> 18) ^^^
        (sha256W block i15 >>> 3)) ^^^ (sha256W block i15).rotateRight 7) +
      sha256W block i16 + sha256W block i7) +
     ((BitVec.setWidth 32 ((sha256W block i2 ++ sha256W block i2) >>> 19) ^^^
       (sha256W block i2 >>> 10)) ^^^ (sha256W block i2).rotateRight 17)) =
      sha256W block i := by
  subst hi16 hi15 hi7 hi2
  rw [sha256SmallSigma0_eq_18_3_7, sha256SmallSigma1_eq_19_10_17, sha256W_ge_16 block i h16 hi64]
  bv_omega

private theorem haclW_step2 (block : List (BitVec 8)) (i15 i16 i7 i2 i : Nat)
    (h16 : 16 ≤ i := by decide) (hi64 : i < 64 := by decide)
    (hi16 : i - 16 = i16 := by decide) (hi15 : i - 15 = i15 := by decide)
    (hi7 : i - 7 = i7 := by decide) (hi2 : i - 2 = i2 := by decide) :
    ((((BitVec.setWidth 32 ((sha256W block i15 ++ sha256W block i15) >>> 18) ^^^
        (sha256W block i15 >>> 3)) ^^^ (sha256W block i15).rotateRight 7) +
      (sha256W block i16 + sha256W block i7)) +
     ((BitVec.setWidth 32 ((sha256W block i2 ++ sha256W block i2) >>> 19) ^^^
       (sha256W block i2 >>> 10)) ^^^ (sha256W block i2).rotateRight 17)) =
      sha256W block i := by
  subst hi16 hi15 hi7 hi2
  rw [sha256SmallSigma0_eq_18_3_7, sha256SmallSigma1_eq_19_10_17, sha256W_ge_16 block i h16 hi64]
  bv_omega

private theorem haclW_step3 (block : List (BitVec 8)) (i16 i15 i7 i2 i : Nat)
    (h16 : 16 ≤ i := by decide) (hi64 : i < 64 := by decide)
    (hi16 : i - 16 = i16 := by decide) (hi15 : i - 15 = i15 := by decide)
    (hi7 : i - 7 = i7 := by decide) (hi2 : i - 2 = i2 := by decide) :
    (((sha256W block i16 +
       ((BitVec.setWidth 32 ((sha256W block i15 ++ sha256W block i15) >>> 18) ^^^
         (sha256W block i15 >>> 3)) ^^^ (sha256W block i15).rotateRight 7)) +
      sha256W block i7) +
     ((BitVec.setWidth 32 ((sha256W block i2 ++ sha256W block i2) >>> 19) ^^^
       (sha256W block i2 >>> 10)) ^^^ (sha256W block i2).rotateRight 17)) =
      sha256W block i := by
  subst hi16 hi15 hi7 hi2
  rw [sha256SmallSigma0_eq_18_3_7, sha256SmallSigma1_eq_19_10_17, sha256W_ge_16 block i h16 hi64]

private theorem haclT1_eq1 (st : List (BitVec 32)) (block : List (BitVec 8))
    (i2 i3 i i1 : Nat) (k : BitVec 32)
    (hi1 : i + 1 = i1 := by decide) (hi2 : i + 2 = i2 := by decide)
    (hi3 : i + 3 = i3 := by decide) (hk : k = sha256K.getD i 0#32 := by decide) :
    (((((sha256E st block i2 &&& sha256E st block i3) + sha256E st block i) +
        (sha256E st block i1 &&& ~~~sha256E st block i3)) + sha256W block i) + k) +
      ((BitVec.setWidth 32 ((sha256E st block i3 ++ sha256E st block i3) >>> 11) ^^^
        (sha256E st block i3).rotateRight 25) ^^^ (sha256E st block i3).rotateRight 6) =
      sha256T1 (sha256E st block i3) (sha256E st block i2) (sha256E st block i1)
        (sha256E st block i) (sha256K.getD i 0#32) (sha256W block i) := by
  subst hi1 hi2 hi3 hk
  rw [BitVec.and_comm (sha256E st block (i + 2)),
      sha256BigSigma1_eq_11_25_6, ← sha256BigSigma1_eq, sha256T1_eq1]

private theorem haclT1_eq2 (st : List (BitVec 32)) (block : List (BitVec 8))
    (i i1 i3 i2 : Nat) (k : BitVec 32)
    (hi1 : i + 1 = i1 := by decide) (hi2 : i + 2 = i2 := by decide)
    (hi3 : i + 3 = i3 := by decide) (hk : k = sha256K.getD i 0#32 := by decide) :
    ((((sha256E st block i + (sha256E st block i1 &&& ~~~sha256E st block i3)) +
        (sha256E st block i3 &&& sha256E st block i2)) + sha256W block i) + k) +
      ((BitVec.setWidth 32 ((sha256E st block i3 ++ sha256E st block i3) >>> 11) ^^^
        (sha256E st block i3).rotateRight 25) ^^^ (sha256E st block i3).rotateRight 6) =
      sha256T1 (sha256E st block i3) (sha256E st block i2) (sha256E st block i1)
        (sha256E st block i) (sha256K.getD i 0#32) (sha256W block i) := by
  subst hi1 hi2 hi3 hk
  have hac (h x y w kv s : BitVec 32) :
      ((((h + x) + y) + w) + kv) + s = ((((kv + w) + h) + x) + y) + s := by
    congr 1
    rw [BitVec.add_assoc ((h + x) + y) w kv, BitVec.add_comm ((h + x) + y) (w + kv), BitVec.add_comm w kv]
    simp only [BitVec.add_assoc]
  rw [hac, sha256BigSigma1_eq_11_25_6, ← sha256BigSigma1_eq, sha256T1_eq2]

private theorem haclT1_eq3 (st : List (BitVec 32)) (block : List (BitVec 8))
    (i i1 i3 i2 : Nat) (k : BitVec 32)
    (hi1 : i + 1 = i1 := by decide) (hi2 : i + 2 = i2 := by decide)
    (hi3 : i + 3 = i3 := by decide) (hk : k = sha256K.getD i 0#32 := by decide) :
    ((((sha256E st block i + sha256W block i) + (sha256E st block i1 &&& ~~~sha256E st block i3)) +
        (sha256E st block i3 &&& sha256E st block i2)) + k) +
      ((BitVec.setWidth 32 ((sha256E st block i3 ++ sha256E st block i3) >>> 11) ^^^
        (sha256E st block i3).rotateRight 25) ^^^ (sha256E st block i3).rotateRight 6) =
      sha256T1 (sha256E st block i3) (sha256E st block i2) (sha256E st block i1)
        (sha256E st block i) (sha256K.getD i 0#32) (sha256W block i) := by
  subst hi1 hi2 hi3 hk
  have hac (h w x y kv s : BitVec 32) :
      ((((h + w) + x) + y) + kv) + s = ((((kv + w) + h) + x) + y) + s := by
    congr 1; rw [BitVec.add_comm (((h + w) + x) + y) kv, BitVec.add_comm h w]; simp only [BitVec.add_assoc]
  rw [hac, sha256BigSigma1_eq_11_25_6, ← sha256BigSigma1_eq, sha256T1_eq2]

private theorem haclT1_eq4 (st : List (BitVec 32)) (block : List (BitVec 8))
    (i i1 i3 i2 : Nat) (k : BitVec 32)
    (hi1 : i + 1 = i1 := by decide) (hi2 : i + 2 = i2 := by decide)
    (hi3 : i + 3 = i3 := by decide) (hk : k = sha256K.getD i 0#32 := by decide) :
    ((((sha256W block i + sha256E st block i) + (sha256E st block i1 &&& ~~~sha256E st block i3)) +
        (sha256E st block i3 &&& sha256E st block i2)) + k) +
      ((BitVec.setWidth 32 ((sha256E st block i3 ++ sha256E st block i3) >>> 11) ^^^
        (sha256E st block i3).rotateRight 25) ^^^ (sha256E st block i3).rotateRight 6) =
      sha256T1 (sha256E st block i3) (sha256E st block i2) (sha256E st block i1)
        (sha256E st block i) (sha256K.getD i 0#32) (sha256W block i) := by
  subst hi1 hi2 hi3 hk
  have hac (w h x y kv s : BitVec 32) :
      ((((w + h) + x) + y) + kv) + s = ((((kv + w) + h) + x) + y) + s := by
    congr 1; rw [BitVec.add_comm (((w + h) + x) + y) kv]; simp only [BitVec.add_assoc]
  rw [hac, sha256BigSigma1_eq_11_25_6, ← sha256BigSigma1_eq, sha256T1_eq2]

private theorem haclT2_eq1 (a b c : BitVec 32) :
    (((b ^^^ a) &&& c) ^^^ (b &&& a)) +
      ((BitVec.setWidth 32 ((a ++ a) >>> 13) ^^^ a.rotateRight 22) ^^^ a.rotateRight 2) =
      sha256T2 a b c := by
  rw [BitVec.xor_comm b a, BitVec.and_comm b a, sha256Maj_eq_and_xor_comm, ← sha256Maj_eq_and_xor,
      sha256BigSigma0_eq_13_22_2, ← sha256BigSigma0_eq, BitVec.add_comm, sha256T2_eq]

private theorem haclT2_eq2 (a b c : BitVec 32) :
    ((BitVec.setWidth 32 ((a ++ a) >>> 13) ^^^ a.rotateRight 22) ^^^ a.rotateRight 2) +
      (((a ^^^ b) &&& c) ^^^ (a &&& b)) =
      sha256T2 a b c := by
  rw [sha256Maj_eq_and_xor_comm, ← sha256Maj_eq_and_xor,
      sha256BigSigma0_eq_13_22_2, ← sha256BigSigma0_eq, sha256T2_eq]

private theorem haclFinal0 (st : List (BitVec 32)) (block : List (BitVec 8)) :
    sha256A st block 67 + sha256A st block 3 = st.getD 0 0#32 + sha256A st block 67 := by
  rw [← sha256A_3, BitVec.add_comm]
private theorem haclFinal1 (st : List (BitVec 32)) (block : List (BitVec 8)) :
    sha256A st block 66 + sha256A st block 2 = st.getD 1 0#32 + sha256A st block 66 := by
  rw [← sha256A_2, BitVec.add_comm]
private theorem haclFinal2 (st : List (BitVec 32)) (block : List (BitVec 8)) :
    sha256A st block 65 + sha256A st block 1 = st.getD 2 0#32 + sha256A st block 65 := by
  rw [← sha256A_1, BitVec.add_comm]
private theorem haclFinal3 (st : List (BitVec 32)) (block : List (BitVec 8)) :
    sha256A st block 64 + sha256A st block 0 = st.getD 3 0#32 + sha256A st block 64 := by
  rw [← sha256A_0, BitVec.add_comm]
private theorem haclFinal4 (st : List (BitVec 32)) (block : List (BitVec 8)) :
    sha256T1 (sha256E st block 66) (sha256E st block 65) (sha256E st block 64)
      (sha256E st block 63) (sha256K.getD 63 0#32) (sha256W block 63) +
      (sha256A st block 63 + sha256E st block 3) =
      st.getD 4 0#32 + sha256E st block 67 := by
  rw [← sha256E_3, BitVec.add_comm (sha256T1 _ _ _ _ _ _), sha256Final4]
private theorem haclFinal5 (st : List (BitVec 32)) (block : List (BitVec 8)) :
    sha256E st block 66 + sha256E st block 2 = st.getD 5 0#32 + sha256E st block 66 := by
  rw [← sha256E_2, BitVec.add_comm]
private theorem haclFinal6 (st : List (BitVec 32)) (block : List (BitVec 8)) :
    sha256E st block 65 + sha256E st block 1 = st.getD 6 0#32 + sha256E st block 65 := by
  rw [← sha256E_1, BitVec.add_comm]
private theorem haclFinal7 (st : List (BitVec 32)) (block : List (BitVec 8)) :
    sha256E st block 64 + sha256E st block 0 = st.getD 7 0#32 + sha256E st block 64 := by
  rw [← sha256E_0, BitVec.add_comm]

/-! ## 3. Prologue & Bounds-Check Segment (`0x0000 → 0x00a8`, `42` steps) -/

private theorem ule_false_of_lt {x : BitVec 64} {c : Nat} (hc : c < 2 ^ 64) (h : c < x.toNat) :
    BitVec.ule x (BitVec.ofNat 64 c) = false := by
  simp only [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc, decide_eq_false_iff_not]
  omega

private def haclCalleeSavedCells (sp0 : BitVec 64)
    (v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : BitVec 64) : SepProp :=
  ((sp0 - 96#64) ↦₆₄ v9) ∗ ((sp0 - 88#64) ↦₆₄ v10) ∗ ((sp0 - 80#64) ↦₆₄ v11) ∗
  ((sp0 - 72#64) ↦₆₄ v12) ∗ ((sp0 - 64#64) ↦₆₄ v13) ∗ ((sp0 - 56#64) ↦₆₄ v14) ∗
  ((sp0 - 48#64) ↦₆₄ v15) ∗ ((sp0 - 40#64) ↦₆₄ v16) ∗ ((sp0 - 32#64) ↦₆₄ v17) ∗
  ((sp0 - 24#64) ↦₆₄ v18) ∗ ((sp0 - 16#64) ↦₆₄ v19) ∗ ((sp0 - 8#64) ↦₆₄ v20)

private theorem SepWP.of_pre_eq {prog : Program} {target_pc : BitVec 64}
    {s : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hP : P' = P) (h : SepWP prog target_pc s P' post oom) :
    SepWP prog target_pc s P post oom := by
  rw [← hP]; exact h

private theorem haclUpdate_prologue [HaclPlacement]
    (b : BitVec 64) (hb : b = haclPl1.base)
    (s0 : State) (blkA stA : BitVec 64) (bsLen : Nat)
    (v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : BitVec 64)
    (R : SepProp) (post : State → SepProp → Prop)
    (hpc : s0.pc = b)
    (hrun : s0.status = .Running)
    (hsp_align : s0.spAligned = true)
    (hx0 : s0.readReg64 (Reg.gpr 0#5) = blkA)
    (hx1 : (s0.readReg64 (Reg.gpr 1#5)).toNat = bsLen)
    (hbs : 64 ≤ bsLen)
    (hx2 : s0.readReg64 (Reg.gpr 2#5) = stA)
    (hx3 : 8 ≤ (s0.readReg64 (Reg.gpr 3#5)).toNat)
    (hpost : ∀ s1 : State,
      s1.pc = b + 168#64 →
      s1.status = .Running →
      s1.spAligned = true →
      s1.sp = s0.sp - 160#64 →
      s1.readReg64 (Reg.gpr 29#5) = (s0.sp - 160#64) + 64#64 →
      s1.readReg64 (Reg.gpr 0#5) = blkA →
      s1.readReg64 (Reg.gpr 2#5) = stA →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      SepWP (haclPC1.rebase b) (b + 168#64) s1
        (haclCalleeSavedCells s0.sp
           (s0.readReg64 Reg.fp) (s0.readReg64 Reg.lr)
           (s0.readReg64 (Reg.gpr 28#5)) (s0.readReg64 (Reg.gpr 27#5))
           (s0.readReg64 (Reg.gpr 26#5)) (s0.readReg64 (Reg.gpr 25#5))
           (s0.readReg64 (Reg.gpr 24#5)) (s0.readReg64 (Reg.gpr 23#5))
           (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
           (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5)) ∗ R)
        post) :
    SepWP (haclPC1.rebase b) (b + 168#64) s0
      (haclCalleeSavedCells s0.sp v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 ∗ R)
      post := by
  subst hb
  have hc3 : BitVec.ule (s0.readReg64 (Reg.gpr 3#5)) 7#64 = false := ule_false_of_lt (by decide) (by omega)
  have hc1_3 : BitVec.ule (s0.readReg64 (Reg.gpr 1#5)) 3#64 = false := ule_false_of_lt (by decide) (by omega)
  have hc1_7 : BitVec.ule (s0.readReg64 (Reg.gpr 1#5)) 7#64 = false := ule_false_of_lt (by decide) (by omega)
  have hc1_11 : BitVec.ule (s0.readReg64 (Reg.gpr 1#5)) 11#64 = false := ule_false_of_lt (by decide) (by omega)
  have hc1_15 : BitVec.ule (s0.readReg64 (Reg.gpr 1#5)) 15#64 = false := ule_false_of_lt (by decide) (by omega)
  have hc1_19 : BitVec.ule (s0.readReg64 (Reg.gpr 1#5)) 19#64 = false := ule_false_of_lt (by decide) (by omega)
  have hc1_23 : BitVec.ule (s0.readReg64 (Reg.gpr 1#5)) 23#64 = false := ule_false_of_lt (by decide) (by omega)
  have hc1_27 : BitVec.ule (s0.readReg64 (Reg.gpr 1#5)) 27#64 = false := ule_false_of_lt (by decide) (by omega)
  have hc1_31 : BitVec.ule (s0.readReg64 (Reg.gpr 1#5)) 31#64 = false := ule_false_of_lt (by decide) (by omega)
  have hc1_35 : BitVec.ule (s0.readReg64 (Reg.gpr 1#5)) 35#64 = false := ule_false_of_lt (by decide) (by omega)
  have hc1_39 : BitVec.ule (s0.readReg64 (Reg.gpr 1#5)) 39#64 = false := ule_false_of_lt (by decide) (by omega)
  have hc1_43 : BitVec.ule (s0.readReg64 (Reg.gpr 1#5)) 43#64 = false := ule_false_of_lt (by decide) (by omega)
  have hc1_47 : BitVec.ule (s0.readReg64 (Reg.gpr 1#5)) 47#64 = false := ule_false_of_lt (by decide) (by omega)
  have hc1_51 : BitVec.ule (s0.readReg64 (Reg.gpr 1#5)) 51#64 = false := ule_false_of_lt (by decide) (by omega)
  have hc1_55 : BitVec.ule (s0.readReg64 (Reg.gpr 1#5)) 55#64 = false := ule_false_of_lt (by decide) (by omega)
  have hc1_59 : BitVec.ule (s0.readReg64 (Reg.gpr 1#5)) 59#64 = false := ule_false_of_lt (by decide) (by omega)
  have hc1_63 : BitVec.ule (s0.readReg64 (Reg.gpr 1#5)) 63#64 = false := ule_false_of_lt (by decide) (by omega)
  unfold haclCalleeSavedCells
  wp_simp_pre only [sepConj_assoc]
  wp_sym_steps 42
  refine SepWP.of_pre_eq ?_ (hpost _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  · unfold haclCalleeSavedCells
    simp only [Reg.fp, Reg.lr, sepConj_assoc]
  · rfl
  · simp [wp_norm, hrun]
  · change ((s0.sp - 160#64) &&& 15#64 == 0#64) = true
    exact State.spAligned_sub s0 160#64 hsp_align
  · simp [wp_norm]
  · simp [wp_norm]
  · simp [wp_norm, hx0]
  · simp [wp_norm, hx2]
  · simp only [calleeSavedVRegs_setPC, calleeSavedVRegs_setMem, calleeSavedVRegs_setPState,
      calleeSavedVRegs_writeReg64]

/-! ## 4. Custom Top-Register Folding Tactic (`wp_hacl_steps`) -/

section HaclTactic
open Lean Meta Elab Tactic

@[wp_norm]
private theorem zeroExtend_32_64_eq_setWidth (x : BitVec 32) :
    BitVec.zeroExtend 64 x = BitVec.setWidth 64 x := rfl

private theorem congr_setWidth64 {x y : BitVec 32} (h : x = y) :
    BitVec.setWidth 64 x = BitVec.setWidth 64 y :=
  congrArg (BitVec.setWidth 64) h

private theorem sha256W_init_off_norm (block : List (BitVec 8)) (off i : Nat)
    (hblock : block.length = 64) (hi : i < 16) (hoff : 4 * i = off) :
    BitVec.setWidth 32 (rev32_64 (BitVec.setWidth 64 (readLE32 block off))) = sha256W block i :=
  sha256W_init_off block off i hblock hi hoff

private theorem sha256W_init_off_unnorm (block : List (BitVec 8)) (off i : Nat)
    (hblock : block.length = 64) (hi : i < 16) (hoff : 4 * i = off) :
    BitVec.setWidth 32
      (rev32_64 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.zeroExtend 64 (readLE32 block off))))) =
      sha256W block i := by
  have h : BitVec.setWidth 32 (BitVec.zeroExtend 64 (readLE32 block off)) = readLE32 block off := by
    simp
  rw [h]
  exact sha256W_init_off block off i hblock hi hoff

private meta def tryApplyPureEqThm (thmName : Name) (v : Expr) : MetaM (Option (Expr × Expr)) := do
  withoutModifyingState do
    let info ← getConstInfo thmName
    let (mvars, _, ty) ← forallMetaTelescope info.type
    let some (_, lhs, rhs) := ty.eq? | return none
    unless ← withReducible (isDefEq lhs v) do return none
    let prf ← instantiateMVars (mkAppN (mkConst thmName) mvars)
    let rhs' ← instantiateMVars rhs
    if prf.hasExprMVar || rhs'.hasExprMVar then return none
    return some (prf, rhs')

private meta def tryApplyDecideEqThm (thmName : Name) (v : Expr) (decideStart : Nat) :
    MetaM (Option (Expr × Expr)) := do
  withoutModifyingState do
    let info ← getConstInfo thmName
    let (mvars, _, ty) ← forallMetaTelescope info.type
    let some (_, lhs, rhs) := ty.eq? | return none
    unless ← withReducible (isDefEq lhs v) do return none
    try
      for k in [decideStart : mvars.size] do
        let m := mvars[k]!.mvarId!
        if !(← m.isAssigned) then
          let p ← instantiateMVars (← m.getType)
          let dp ← mkDecideProof p
          m.assign dp
    catch _ =>
      return none
    let prf ← instantiateMVars (mkAppN (mkConst thmName) mvars)
    let rhs' ← instantiateMVars rhs
    if prf.hasExprMVar || rhs'.hasExprMVar then return none
    return some (prf, rhs')

private meta def tryApplyIdxEqThm (thmName : Name) (v : Expr)
    (srcIdxPos dstIdxPos : Nat) (offset : Nat) (decideStart : Nat) :
    MetaM (Option (Expr × Expr)) := do
  withoutModifyingState do
    let info ← getConstInfo thmName
    let (mvars, _, ty) ← forallMetaTelescope info.type
    let some (_, lhs, rhs) := ty.eq? | return none
    unless ← withReducible (isDefEq lhs v) do return none
    let srcExpr ← instantiateMVars mvars[srcIdxPos]!
    let some srcVal := srcExpr.nat? | return none
    mvars[dstIdxPos]!.mvarId!.assign (toExpr (srcVal + offset))
    try
      for k in [decideStart : mvars.size] do
        let m := mvars[k]!.mvarId!
        if !(← m.isAssigned) then
          let p ← instantiateMVars (← m.getType)
          let dp ← mkDecideProof p
          m.assign dp
    catch _ =>
      return none
    let prf ← instantiateMVars (mkAppN (mkConst thmName) mvars)
    let rhs' ← instantiateMVars rhs
    if prf.hasExprMVar || rhs'.hasExprMVar then return none
    return some (prf, rhs')

private meta def tryFoldTopRegExpr32 (v : Expr) (hblock? : Option Expr) :
    MetaM (Option (Expr × Expr)) := do
  if v.isAppOfArity ``BitVec.setWidth 3 then
    let some hblock := hblock? | return none
    let revCand := v.getArg! 2
    if revCand.isAppOfArity ``Arm64.rev32_64 1 then
      let arg64 := revCand.getArg! 0
      if arg64.isAppOfArity ``BitVec.setWidth 3 then
        let inner := arg64.getArg! 2
        if inner.isAppOfArity ``readLE32 2 then
          let block := inner.getArg! 0
          let offExpr := inner.getArg! 1
          let some off := offExpr.nat? | return none
          let iExpr := toExpr (off / 4)
          let hi ← mkDecideProof (← mkAppM ``LT.lt #[iExpr, toExpr (16 : Nat)])
          let hoff ← mkDecideProof (← mkEq (← mkAppM ``HMul.hMul #[toExpr (4 : Nat), iExpr]) offExpr)
          let prf := mkApp6 (mkConst ``sha256W_init_off_norm) block offExpr iExpr hblock hi hoff
          let rhs := mkApp2 (mkConst ``sha256W) block iExpr
          return some (prf, rhs)
        if inner.isAppOfArity ``BitVec.setWidth 3 then
          let zext := inner.getArg! 2
          if zext.isAppOfArity ``BitVec.zeroExtend 3 then
            let rle := zext.getArg! 2
            if rle.isAppOfArity ``readLE32 2 then
              let block := rle.getArg! 0
              let offExpr := rle.getArg! 1
              let some off := offExpr.nat? | return none
              let iExpr := toExpr (off / 4)
              let hi ← mkDecideProof (← mkAppM ``LT.lt #[iExpr, toExpr (16 : Nat)])
              let hoff ← mkDecideProof (← mkEq (← mkAppM ``HMul.hMul #[toExpr (4 : Nat), iExpr]) offExpr)
              let prf := mkApp6 (mkConst ``sha256W_init_off_unnorm) block offExpr iExpr hblock hi hoff
              let rhs := mkApp2 (mkConst ``sha256W) block iExpr
              return some (prf, rhs)
    return none
  unless v.isAppOfArity ``HAdd.hAdd 6 do return none
  let lhs := v.getArg! 4
  let rhs := v.getArg! 5
  if rhs.isAppOfArity ``sha256A 3 && lhs.isAppOfArity ``sha256T1 6 then
    return ← tryApplyIdxEqThm ``sha256E_from_t1 v 5 6 4 7
  if rhs.isAppOfArity ``sha256T1 6 && lhs.isAppOfArity ``sha256T2 3 then
    return ← tryApplyIdxEqThm ``sha256A_from_t1_t2 v 5 6 4 7
  if lhs.isAppOfArity ``sha256T1 6 && rhs.isAppOfArity ``HAdd.hAdd 6 then
    return ← tryApplyPureEqThm ``haclFinal4 v
  if rhs.isAppOfArity ``HXor.hXor 6 then
    if lhs.isAppOfArity ``HXor.hXor 6 then
      if let some res ← tryApplyPureEqThm ``haclT2_eq1 v then return some res
      if let some res ← tryApplyPureEqThm ``haclT2_eq2 v then return some res
      return none
    for thm in #[``haclT1_eq1, ``haclT1_eq2, ``haclT1_eq3, ``haclT1_eq4] do
      if let some res ← tryApplyDecideEqThm thm v 7 then return some res
    if let some res ← tryApplyIdxEqThm ``haclW_step1 v 2 5 16 6 then return some res
    if let some res ← tryApplyIdxEqThm ``haclW_step2 v 2 5 16 6 then return some res
    if let some res ← tryApplyIdxEqThm ``haclW_step3 v 1 5 16 6 then return some res
    return none
  if lhs.isAppOfArity ``sha256A 3 && rhs.isAppOfArity ``sha256A 3 then
    for thm in #[``haclFinal0, ``haclFinal1, ``haclFinal2, ``haclFinal3] do
      if let some res ← tryApplyPureEqThm thm v then return some res
    return none
  if lhs.isAppOfArity ``sha256E 3 && rhs.isAppOfArity ``sha256E 3 then
    for thm in #[``haclFinal5, ``haclFinal6, ``haclFinal7] do
      if let some res ← tryApplyPureEqThm thm v then return some res
    return none
  return none

private meta def tryFoldTopRegExpr (v64 : Expr) (hblock? : Option Expr) :
    MetaM (Option (Expr × Expr)) := do
  unless v64.isAppOfArity ``BitVec.setWidth 3 do return none
  unless (v64.getArg! 0).nat? == some 32 && (v64.getArg! 1).nat? == some 64 do return none
  let v32 := v64.getArg! 2
  let some (prf32, rhs32) ← tryFoldTopRegExpr32 v32 hblock? | return none
  let prf64 := mkApp3 (mkConst ``congr_setWidth64) v32 rhs32 prf32
  let rhs64 := mkApp3 (mkConst ``BitVec.setWidth) (v64.getArg! 0) (v64.getArg! 1) rhs32
  return some (prf64, rhs64)

private theorem SepWP.rw_top_reg_pc {prog : Program} {target_pc : BitVec 64}
    {s : Arm64.State} {pc : BitVec 64} {r : Reg} {v v' : BitVec 64}
    {P : SepProp} {post : Arm64.State → SepProp → Prop} {oom : Arm64.State → SepProp}
    (hv : v = v')
    (h : SepWP prog target_pc ((s.writeReg64 r v').setPC pc) P post oom) :
    SepWP prog target_pc ((s.writeReg64 r v).setPC pc) P post oom := by
  rw [hv]; exact h

private theorem SepWP.rw_top_reg_pc_mem {prog : Program} {target_pc : BitVec 64}
    {s : Arm64.State} {pc : BitVec 64} {m : Memory} {r : Reg} {v v' : BitVec 64}
    {P : SepProp} {post : Arm64.State → SepProp → Prop} {oom : Arm64.State → SepProp}
    (hv : v = v')
    (h : SepWP prog target_pc (((s.writeReg64 r v').setPC pc).setMem m) P post oom) :
    SepWP prog target_pc (((s.writeReg64 r v).setPC pc).setMem m) P post oom := by
  rw [hv]; exact h

private theorem SepWP.rw_top_reg_ps_pc_mem {prog : Program} {target_pc : BitVec 64}
    {s : Arm64.State} {ps : PState} {pc : BitVec 64} {m : Memory} {r : Reg} {v v' : BitVec 64}
    {P : SepProp} {post : Arm64.State → SepProp → Prop} {oom : Arm64.State → SepProp}
    (hv : v = v')
    (h : SepWP prog target_pc ((((s.writeReg64 r v').setPState ps).setPC pc).setMem m) P post oom) :
    SepWP prog target_pc ((((s.writeReg64 r v).setPState ps).setPC pc).setMem m) P post oom := by
  rw [hv]; exact h

private meta def finishFoldGoal (bs : WpSymBlockState) (g : MVarId)
    (prog targetPc newS P post oom : Expr) (mkPrf : Expr → Expr) : TacticM WpSymBlockState := do
  let (newSShared, symInternalState') ←
    (Sym.withoutShareCommonChecks (Sym.shareCommon newS)) bs.symCtx |>.run bs.symInternalState
  let seeded := seedNormalizedInSymCache newSShared bs.simpState.persistentCache
  let bs' := { bs with symInternalState := symInternalState',
                       simpState := { bs.simpState with persistentCache := seeded } }
  let newGoalTy := mkApp6 (mkConst ``SepWP) prog targetPc newSShared P post oom
  let newGoalMVar ← mkFreshExprSyntheticOpaqueMVar newGoalTy (← g.getTag)
  g.assign (mkPrf newGoalMVar)
  replaceMainGoal [newGoalMVar.mvarId!]
  return bs'

private meta def tryFoldGoalTopReg (hblock? : Option Expr) (bs : WpSymBlockState) :
    TacticM WpSymBlockState := do
  let g ← getMainGoal
  g.withContext do
    let ty ← instantiateMVars (← g.getType)
    unless ty.isAppOfArity ``SepWP 6 do return bs
    let prog := ty.getArg! 0; let targetPc := ty.getArg! 1; let sExpr := ty.getArg! 2
    let P := ty.getArg! 3; let post := ty.getArg! 4; let oom := ty.getArg! 5
    if sExpr.isAppOfArity ``Arm64.State.setMem 2 then
      let s1 := sExpr.getArg! 0; let m := sExpr.getArg! 1
      if s1.isAppOfArity ``Arm64.State.setPC 2 then
        let s2 := s1.getArg! 0; let pc := s1.getArg! 1
        if s2.isAppOfArity ``Arm64.State.writeReg64 3 then
          let sInner := s2.getArg! 0; let r := s2.getArg! 1; let v := s2.getArg! 2
          let some (hv, v') ← tryFoldTopRegExpr v hblock? | return bs
          let newS := mkApp2 (mkConst ``Arm64.State.setMem)
            (mkApp2 (mkConst ``Arm64.State.setPC)
              (mkApp3 (mkConst ``Arm64.State.writeReg64) sInner r v') pc) m
          return ← finishFoldGoal bs g prog targetPc newS P post oom fun ng =>
            mkAppN (mkConst ``SepWP.rw_top_reg_pc_mem)
              #[prog, targetPc, sInner, pc, m, r, v, v', P, post, oom, hv, ng]
        if s2.isAppOfArity ``Arm64.State.setPState 2 then
          let s3 := s2.getArg! 0; let ps := s2.getArg! 1
          if s3.isAppOfArity ``Arm64.State.writeReg64 3 then
            let sInner := s3.getArg! 0; let r := s3.getArg! 1; let v := s3.getArg! 2
            let some (hv, v') ← tryFoldTopRegExpr v hblock? | return bs
            let newS := mkApp2 (mkConst ``Arm64.State.setMem)
              (mkApp2 (mkConst ``Arm64.State.setPC)
                (mkApp2 (mkConst ``Arm64.State.setPState)
                  (mkApp3 (mkConst ``Arm64.State.writeReg64) sInner r v') ps) pc) m
            return ← finishFoldGoal bs g prog targetPc newS P post oom fun ng =>
              mkAppN (mkConst ``SepWP.rw_top_reg_ps_pc_mem)
                #[prog, targetPc, sInner, ps, pc, m, r, v, v', P, post, oom, hv, ng]
      return bs
    if sExpr.isAppOfArity ``Arm64.State.setPC 2 then
      let s2 := sExpr.getArg! 0; let pc := sExpr.getArg! 1
      if s2.isAppOfArity ``Arm64.State.writeReg64 3 then
        let sInner := s2.getArg! 0; let r := s2.getArg! 1; let v := s2.getArg! 2
        let some (hv, v') ← tryFoldTopRegExpr v hblock? | return bs
        let newS := mkApp2 (mkConst ``Arm64.State.setPC)
          (mkApp3 (mkConst ``Arm64.State.writeReg64) sInner r v') pc
        return ← finishFoldGoal bs g prog targetPc newS P post oom fun ng =>
          mkAppN (mkConst ``SepWP.rw_top_reg_pc)
            #[prog, targetPc, sInner, pc, r, v, v', P, post, oom, hv, ng]
      return bs
    unless sExpr.isAppOfArity ``Arm64.State.writeReg64 3 do return bs
    let sInner := sExpr.getArg! 0; let r := sExpr.getArg! 1; let v := sExpr.getArg! 2
    let some (hv, v') ← tryFoldTopRegExpr v hblock? | return bs
    let newS := mkApp3 (mkConst ``Arm64.State.writeReg64) sInner r v'
    return ← finishFoldGoal bs g prog targetPc newS P post oom fun ng =>
      mkAppN (mkConst ``SepWP.rw_top_reg) #[prog, targetPc, sInner, r, v, v', P, post, oom, hv, ng]

private meta def clearDeadMemFVars : TacticM Unit := do
  let g ← getMainGoal
  g.withContext do
    let lctx ← getLCtx
    let goalTy ← instantiateMVars (← g.getType)
    let live := collectFVars {} goalTy
    let mut toClear : Array FVarId := #[]
    for declOpt in lctx.decls.toList.reverse do
      let some decl := declOpt | continue
      if decl.isImplementationDetail || decl.isAuxDecl then continue
      if decl.type.isConstOf ``Arm64.Memory && !live.fvarSet.contains decl.fvarId then
        toClear := toClear.push decl.fvarId
    if !toClear.isEmpty then
      let g' ← g.tryClearMany toClear
      replaceMainGoal [g']

private meta def wpHaclStepsImpl (steps : Nat) (hblock? : Option Ident) : TacticM Unit := do
  let baseThms ← (← getMainGoal).withContext getOrBuildSymWPTheorems
  let localThms ← (← getMainGoal).withContext buildLocalSymTheorems
  let methods := mkSymWPMethods baseThms localThms
  let config : Sym.Simp.Config := { maxSteps := 100000 }
  let mut bs ← (← getMainGoal).withContext mkInitialWpSymBlockState
  let hblockExpr? ← (← getMainGoal).withContext do
    match hblock? with
    | some id => some <$> getFVarFromUserName id.getId
    | none => pure none
  for stepIdx in [0 : steps] do
    let res ← tryTacticCatchRuntimeMsg do
      let (_, bs') ← wpSymStepInBlock methods config bs (inStepLoop := true)
      let bs'' ← tryFoldGoalTopReg hblockExpr? bs'
      if stepIdx % 32 == 31 then
        clearDeadMemFVars
      return bs''
    match res with
    | .ok bs' => bs := bs'
    | .error msg =>
      logWarning m!"wp_hacl_steps stopped at step {stepIdx}: {msg}"
      break
  clearDeadMemFVars

end HaclTactic

local elab "wp_hacl_steps" n:num : tactic =>
  wpHaclStepsImpl n.getNat none

local elab "wp_hacl_steps_blk" n:num hblock:ident : tactic =>
  wpHaclStepsImpl n.getNat (some hblock)

/-! ## 5. Straight-Line SHA-256 Round Segments (`0x00a8 → 0x1eac`) -/

local notation:50 "gpr32 " s:arg r:arg v:arg =>
  State.readReg64 s (Reg.gpr r) = BitVec.setWidth 64 v

private def haclActiveStack (sp : BitVec 64)
    (w8 w12 : BitVec 32) (v16 : BitVec 64)
    (w24 w28 w32 w36 w40 w44 w48 w52 w56 w60 : BitVec 32) : SepProp :=
  ((sp + 8#64) ↦₃₂ w8) ∗ ((sp + 12#64) ↦₃₂ w12) ∗ ((sp + 16#64) ↦₆₄ v16) ∗
  ((sp + 24#64) ↦₃₂ w24) ∗ ((sp + 28#64) ↦₃₂ w28) ∗ ((sp + 32#64) ↦₃₂ w32) ∗
  ((sp + 36#64) ↦₃₂ w36) ∗ ((sp + 40#64) ↦₃₂ w40) ∗ ((sp + 44#64) ↦₃₂ w44) ∗
  ((sp + 48#64) ↦₃₂ w48) ∗ ((sp + 52#64) ↦₃₂ w52) ∗ ((sp + 56#64) ↦₃₂ w56) ∗
  ((sp + 60#64) ↦₃₂ w60)

private def haclStateCells (stA : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 32) : SepProp :=
  (stA ↦₃₂ w0) ∗ ((stA + 4#64) ↦₃₂ w1) ∗ ((stA + 8#64) ↦₃₂ w2) ∗ ((stA + 12#64) ↦₃₂ w3) ∗
  ((stA + 16#64) ↦₃₂ w4) ∗ ((stA + 20#64) ↦₃₂ w5) ∗ ((stA + 24#64) ↦₃₂ w6) ∗ ((stA + 28#64) ↦₃₂ w7)

set_option maxHeartbeats 2000000 in
private theorem haclUpdate_seg1 [HaclPlacement]
    (b : BitVec 64) (hb : b = haclPl1.base)
    (s : State) (sp blkA stA : BitVec 64) (st : List (BitVec 32)) (block : List (BitVec 8))
    (w8 w12 : BitVec 32) (v16 : BitVec 64)
    (w24 w28 w32 w36 w40 w44 w48 w52 w56 w60 : BitVec 32)
    (R : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = b + 168#64) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hblock : block.length = 64) (hsp : s.sp = sp) (hx29 : s.readReg64 (Reg.gpr 29#5) = sp + 64#64)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = blkA) (hx2 : s.readReg64 (Reg.gpr 2#5) = stA)
    (hpost : ∀ s' : State,
      s'.pc = b + 2032#64 → s'.status = .Running → s'.spAligned = true →
      s'.sp = sp → s'.readReg64 (Reg.gpr 29#5) = sp + 64#64 →
      calleeSavedVRegs s' = calleeSavedVRegs s →
      gpr32 s' 0#5 (sha256A st block 17) →
      gpr32 s' 1#5 (BitVec.setWidth 32 ((sha256W block 4 ++ sha256W block 4) >>> 18)) →
      gpr32 s' 2#5 (sha256W block 13) → gpr32 s' 3#5 (sha256W block 10) →
      gpr32 s' 4#5 (sha256W block 18) → gpr32 s' 5#5 (sha256W block 3) →
      gpr32 s' 6#5 (sha256W block 4) → gpr32 s' 7#5 (sha256W block 14) →
      gpr32 s' 8#5 (sha256T1 (sha256E st block 20) (sha256E st block 19) (sha256E st block 18)
        (sha256E st block 17) (sha256K.getD 17 0#32) (sha256W block 17)) →
      gpr32 s' 9#5 (sha256T2 (sha256A st block 20) (sha256A st block 19) (sha256A st block 18)) →
      gpr32 s' 11#5 (sha256A st block 20) → gpr32 s' 12#5 (sha256A st block 18) →
      gpr32 s' 13#5 (sha256A st block 19) → gpr32 s' 17#5 (sha256W block 6) →
      gpr32 s' 18#5 (sha256W block 16) → gpr32 s' 19#5 (sha256W block 11) →
      gpr32 s' 20#5 (sha256W block 7) → gpr32 s' 21#5 (sha256W block 12) →
      gpr32 s' 22#5 (sha256W block 9) → gpr32 s' 23#5 (sha256W block 5) →
      gpr32 s' 24#5 (sha256E st block 18) → gpr32 s' 25#5 (sha256W block 15) →
      gpr32 s' 26#5 (sha256W block 17) → gpr32 s' 28#5 (sha256E st block 20) →
      gpr32 s' 30#5 (sha256E st block 19) →
      SepWP (haclPC1.rebase b) (b + 2032#64) s'
        (haclActiveStack sp w8 (sha256W block 14) stA
           (sha256A st block 3) (sha256E st block 3) (sha256A st block 2) (sha256E st block 2)
           (sha256A st block 1) (sha256E st block 1) (sha256A st block 0) (sha256E st block 0)
           (sha256W block 6) (sha256W block 8) ∗
         haclStateCells stA (st.getD 0 0#32) (st.getD 1 0#32) (st.getD 2 0#32) (st.getD 3 0#32)
           (st.getD 4 0#32) (st.getD 5 0#32) (st.getD 6 0#32) (st.getD 7 0#32) ∗
         (blkA ↦ₛ block) ∗ R) post) :
    SepWP (haclPC1.rebase b) (b + 2032#64) s
      (haclActiveStack sp w8 w12 v16 w24 w28 w32 w36 w40 w44 w48 w52 w56 w60 ∗
       haclStateCells stA (st.getD 0 0#32) (st.getD 1 0#32) (st.getD 2 0#32) (st.getD 3 0#32)
         (st.getD 4 0#32) (st.getD 5 0#32) (st.getD 6 0#32) (st.getD 7 0#32) ∗
       (blkA ↦ₛ block) ∗ R) post := by
  subst hb
  rw [sha256A_3 st block, sha256A_2 st block, sha256A_1 st block, sha256A_0 st block,
      sha256E_3 st block, sha256E_2 st block, sha256E_1 st block, sha256E_0 st block]
  unfold haclActiveStack haclStateCells
  rw [pointsToBytes_64_eq_cells32 blkA block hblock]; wp_simp_pre only [sepConj_assoc]
  wp_hacl_steps_blk 466 hblock
  refine SepWP.of_pre_eq ?_
    (hpost _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  · rw [sha256A_3 st block, sha256A_2 st block, sha256A_1 st block, sha256A_0 st block,
        sha256E_3 st block, sha256E_2 st block, sha256E_1 st block, sha256E_0 st block]
    unfold haclActiveStack haclStateCells
    rw [pointsToBytes_64_eq_cells32 blkA block hblock]; simp only [sepConj_assoc]
  · rfl
  · simp [wp_norm, hrun]
  · rw [← hsp_align]; simp only [State.spAligned, State.sp_setPC, State.sp_setMem, State.sp_writeReg64_gpr]
  · simp [wp_norm, hsp]
  · simp [wp_norm, hx29]
  · simp only [calleeSavedVRegs_setPC, calleeSavedVRegs_setMem, calleeSavedVRegs_writeReg64]
  all_goals rfl

set_option maxHeartbeats 2000000 in
private theorem haclUpdate_seg2 [HaclPlacement]
    (b : BitVec 64) (hb : b = haclPl1.base)
    (s : State) (sp stA : BitVec 64) (st : List (BitVec 32)) (block : List (BitVec 8))
    (w8 : BitVec 32) (R : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = b + 2032#64) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hsp : s.sp = sp) (hx29 : s.readReg64 (Reg.gpr 29#5) = sp + 64#64)
    (hx0 : gpr32 s 0#5 (sha256A st block 17))
    (hx1 : gpr32 s 1#5 (BitVec.setWidth 32 ((sha256W block 4 ++ sha256W block 4) >>> 18)))
    (hx2 : gpr32 s 2#5 (sha256W block 13)) (hx3 : gpr32 s 3#5 (sha256W block 10))
    (hx4 : gpr32 s 4#5 (sha256W block 18)) (hx5 : gpr32 s 5#5 (sha256W block 3))
    (hx6 : gpr32 s 6#5 (sha256W block 4)) (hx7 : gpr32 s 7#5 (sha256W block 14))
    (hx8 : gpr32 s 8#5 (sha256T1 (sha256E st block 20) (sha256E st block 19) (sha256E st block 18)
      (sha256E st block 17) (sha256K.getD 17 0#32) (sha256W block 17)))
    (hx9 : gpr32 s 9#5 (sha256T2 (sha256A st block 20) (sha256A st block 19) (sha256A st block 18)))
    (hx11 : gpr32 s 11#5 (sha256A st block 20)) (hx12 : gpr32 s 12#5 (sha256A st block 18))
    (hx13 : gpr32 s 13#5 (sha256A st block 19)) (hx17 : gpr32 s 17#5 (sha256W block 6))
    (hx18 : gpr32 s 18#5 (sha256W block 16)) (hx19 : gpr32 s 19#5 (sha256W block 11))
    (hx20 : gpr32 s 20#5 (sha256W block 7)) (hx21 : gpr32 s 21#5 (sha256W block 12))
    (hx22 : gpr32 s 22#5 (sha256W block 9)) (hx23 : gpr32 s 23#5 (sha256W block 5))
    (hx24 : gpr32 s 24#5 (sha256E st block 18)) (hx25 : gpr32 s 25#5 (sha256W block 15))
    (hx26 : gpr32 s 26#5 (sha256W block 17)) (hx28 : gpr32 s 28#5 (sha256E st block 20))
    (hx30 : gpr32 s 30#5 (sha256E st block 19))
    (hpost : ∀ s' : State,
      s'.pc = b + 3652#64 → s'.status = .Running → s'.spAligned = true →
      s'.sp = sp → s'.readReg64 (Reg.gpr 29#5) = sp + 64#64 →
      calleeSavedVRegs s' = calleeSavedVRegs s →
      gpr32 s' 0#5 (sha256W block 22) → gpr32 s' 1#5 (sha256W block 24) →
      gpr32 s' 3#5 (sha256W block 26) → gpr32 s' 4#5 (sha256W block 18) →
      gpr32 s' 5#5 (sha256W block 19) → gpr32 s' 6#5 (sha256W block 20) →
      gpr32 s' 7#5 (sha256W block 21) → gpr32 s' 8#5 (sha256A st block 31) →
      gpr32 s' 9#5 (sha256T1 (sha256E st block 33) (sha256E st block 32) (sha256E st block 31)
        (sha256E st block 30) (sha256K.getD 30 0#32) (sha256W block 30)) →
      gpr32 s' 10#5 (sha256E st block 34) → gpr32 s' 11#5 (sha256E st block 33) →
      gpr32 s' 12#5 (sha256E st block 31) →
      gpr32 s' 13#5 (sha256T2 (sha256A st block 33) (sha256A st block 32) (sha256A st block 31)) →
      gpr32 s' 17#5 (sha256W block 31) → gpr32 s' 18#5 (sha256W block 16) →
      gpr32 s' 19#5 (sha256W block 28) → gpr32 s' 20#5 (sha256W block 23) →
      gpr32 s' 21#5 (sha256W block 30) → gpr32 s' 22#5 (sha256W block 25) →
      gpr32 s' 23#5 (sha256W block 27) → gpr32 s' 24#5 (sha256W block 29) →
      gpr32 s' 26#5 (sha256W block 17) → gpr32 s' 27#5 (sha256A st block 32) →
      gpr32 s' 28#5 (sha256A st block 33) → gpr32 s' 30#5 (sha256E st block 32) →
      SepWP (haclPC1.rebase b) (b + 3652#64) s'
        (haclActiveStack sp w8 (sha256W block 14) stA
           (sha256A st block 3) (sha256E st block 3) (sha256A st block 2) (sha256E st block 2)
           (sha256A st block 1) (sha256E st block 1) (sha256A st block 0) (sha256E st block 0)
           (sha256W block 6) (sha256W block 8) ∗ R) post) :
    SepWP (haclPC1.rebase b) (b + 3652#64) s
      (haclActiveStack sp w8 (sha256W block 14) stA
         (sha256A st block 3) (sha256E st block 3) (sha256A st block 2) (sha256E st block 2)
         (sha256A st block 1) (sha256E st block 1) (sha256A st block 0) (sha256E st block 0)
         (sha256W block 6) (sha256W block 8) ∗ R) post := by
  subst hb; unfold haclActiveStack; wp_simp_pre only [sepConj_assoc]
  wp_hacl_steps 405
  refine SepWP.of_pre_eq ?_
    (hpost _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  · unfold haclActiveStack; simp only [sepConj_assoc]
  · rfl
  · simp [wp_norm, hrun]
  · rw [← hsp_align]; simp only [State.spAligned, State.sp_setPC, State.sp_writeReg64_gpr]
  · simp [wp_norm, hsp]
  · simp [wp_norm, hx29]
  · simp only [calleeSavedVRegs_setPC, calleeSavedVRegs_writeReg64]
  all_goals first | rfl | (simp [wp_norm]; assumption)

set_option maxHeartbeats 2000000 in
private theorem haclUpdate_seg3 [HaclPlacement]
    (b : BitVec 64) (hb : b = haclPl1.base)
    (s : State) (sp stA : BitVec 64) (st : List (BitVec 32)) (block : List (BitVec 8))
    (w8 : BitVec 32) (R : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = b + 3652#64) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hsp : s.sp = sp) (hx29 : s.readReg64 (Reg.gpr 29#5) = sp + 64#64)
    (hx0 : gpr32 s 0#5 (sha256W block 22)) (hx1 : gpr32 s 1#5 (sha256W block 24))
    (hx3 : gpr32 s 3#5 (sha256W block 26)) (hx4 : gpr32 s 4#5 (sha256W block 18))
    (hx5 : gpr32 s 5#5 (sha256W block 19)) (hx6 : gpr32 s 6#5 (sha256W block 20))
    (hx7 : gpr32 s 7#5 (sha256W block 21)) (hx8 : gpr32 s 8#5 (sha256A st block 31))
    (hx9 : gpr32 s 9#5 (sha256T1 (sha256E st block 33) (sha256E st block 32) (sha256E st block 31)
      (sha256E st block 30) (sha256K.getD 30 0#32) (sha256W block 30)))
    (hx10 : gpr32 s 10#5 (sha256E st block 34)) (hx11 : gpr32 s 11#5 (sha256E st block 33))
    (hx12 : gpr32 s 12#5 (sha256E st block 31))
    (hx13 : gpr32 s 13#5 (sha256T2 (sha256A st block 33) (sha256A st block 32) (sha256A st block 31)))
    (hx17 : gpr32 s 17#5 (sha256W block 31)) (hx18 : gpr32 s 18#5 (sha256W block 16))
    (hx19 : gpr32 s 19#5 (sha256W block 28)) (hx20 : gpr32 s 20#5 (sha256W block 23))
    (hx21 : gpr32 s 21#5 (sha256W block 30)) (hx22 : gpr32 s 22#5 (sha256W block 25))
    (hx23 : gpr32 s 23#5 (sha256W block 27)) (hx24 : gpr32 s 24#5 (sha256W block 29))
    (hx26 : gpr32 s 26#5 (sha256W block 17)) (hx27 : gpr32 s 27#5 (sha256A st block 32))
    (hx28 : gpr32 s 28#5 (sha256A st block 33)) (hx30 : gpr32 s 30#5 (sha256E st block 32))
    (hpost : ∀ s' : State,
      s'.pc = b + 5528#64 → s'.status = .Running → s'.spAligned = true →
      s'.sp = sp → s'.readReg64 (Reg.gpr 29#5) = sp + 64#64 →
      calleeSavedVRegs s' = calleeSavedVRegs s →
      gpr32 s' 0#5 (sha256W block 45) → gpr32 s' 1#5 (sha256W block 44) →
      gpr32 s' 2#5 (sha256W block 36) → gpr32 s' 3#5 (sha256W block 43) →
      gpr32 s' 4#5 (sha256W block 42) → gpr32 s' 5#5 (sha256W block 41) →
      gpr32 s' 6#5 (sha256W block 37) → gpr32 s' 7#5 (sha256W block 38) →
      gpr32 s' 8#5 (sha256T1 (sha256E st block 48) (sha256E st block 47) (sha256E st block 46)
        (sha256E st block 45) (sha256K.getD 45 0#32) (sha256W block 45)) →
      gpr32 s' 9#5 (sha256E st block 47) → gpr32 s' 10#5 (sha256A st block 47) →
      gpr32 s' 11#5 (sha256A st block 45) →
      gpr32 s' 13#5 (sha256T2 (sha256A st block 48) (sha256A st block 47) (sha256A st block 46)) →
      gpr32 s' 14#5 (sha256W block 31) → gpr32 s' 16#5 (sha256W block 46) →
      gpr32 s' 17#5 (sha256W block 33) → gpr32 s' 18#5 (sha256W block 32) →
      gpr32 s' 19#5 (sha256E st block 46) → gpr32 s' 20#5 (sha256W block 39) →
      gpr32 s' 22#5 (sha256A st block 48) → gpr32 s' 23#5 (sha256A st block 46) →
      gpr32 s' 24#5 (sha256E st block 48) → gpr32 s' 25#5 (sha256W block 40) →
      SepWP (haclPC1.rebase b) (b + 5528#64) s'
        (haclActiveStack sp (sha256W block 35) (sha256W block 34) stA
           (sha256A st block 3) (sha256E st block 3) (sha256A st block 2) (sha256E st block 2)
           (sha256A st block 1) (sha256E st block 1) (sha256A st block 0) (sha256E st block 0)
           (sha256W block 6) (sha256W block 31) ∗ R) post) :
    SepWP (haclPC1.rebase b) (b + 5528#64) s
      (haclActiveStack sp w8 (sha256W block 14) stA
         (sha256A st block 3) (sha256E st block 3) (sha256A st block 2) (sha256E st block 2)
         (sha256A st block 1) (sha256E st block 1) (sha256A st block 0) (sha256E st block 0)
         (sha256W block 6) (sha256W block 8) ∗ R) post := by
  subst hb; unfold haclActiveStack; wp_simp_pre only [sepConj_assoc]
  wp_hacl_steps 469
  refine SepWP.of_pre_eq ?_
    (hpost _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  · unfold haclActiveStack; simp only [sepConj_assoc]
  · rfl
  · simp [wp_norm, hrun]
  · rw [← hsp_align]; simp only [State.spAligned, State.sp_setPC, State.sp_setMem, State.sp_writeReg64_gpr]
  · simp [wp_norm, hsp]
  · simp [wp_norm, hx29]
  · simp only [calleeSavedVRegs_setPC, calleeSavedVRegs_setMem, calleeSavedVRegs_writeReg64]
  all_goals rfl

set_option maxHeartbeats 2000000 in
private theorem haclUpdate_seg4 [HaclPlacement]
    (b : BitVec 64) (hb : b = haclPl1.base)
    (s : State) (sp stA : BitVec 64) (st : List (BitVec 32)) (block : List (BitVec 8))
    (u0 u1 u2 u3 u4 u5 u6 u7 : BitVec 32) (R : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = b + 5528#64) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hst : st.length = 8) (hsp : s.sp = sp) (hx29 : s.readReg64 (Reg.gpr 29#5) = sp + 64#64)
    (hx0 : gpr32 s 0#5 (sha256W block 45)) (hx1 : gpr32 s 1#5 (sha256W block 44))
    (hx2 : gpr32 s 2#5 (sha256W block 36)) (hx3 : gpr32 s 3#5 (sha256W block 43))
    (hx4 : gpr32 s 4#5 (sha256W block 42)) (hx5 : gpr32 s 5#5 (sha256W block 41))
    (hx6 : gpr32 s 6#5 (sha256W block 37)) (hx7 : gpr32 s 7#5 (sha256W block 38))
    (hx8 : gpr32 s 8#5 (sha256T1 (sha256E st block 48) (sha256E st block 47) (sha256E st block 46)
      (sha256E st block 45) (sha256K.getD 45 0#32) (sha256W block 45)))
    (hx9 : gpr32 s 9#5 (sha256E st block 47)) (hx10 : gpr32 s 10#5 (sha256A st block 47))
    (hx11 : gpr32 s 11#5 (sha256A st block 45))
    (hx13 : gpr32 s 13#5 (sha256T2 (sha256A st block 48) (sha256A st block 47) (sha256A st block 46)))
    (hx14 : gpr32 s 14#5 (sha256W block 31)) (hx16 : gpr32 s 16#5 (sha256W block 46))
    (hx17 : gpr32 s 17#5 (sha256W block 33)) (hx18 : gpr32 s 18#5 (sha256W block 32))
    (hx19 : gpr32 s 19#5 (sha256E st block 46)) (hx20 : gpr32 s 20#5 (sha256W block 39))
    (hx22 : gpr32 s 22#5 (sha256A st block 48)) (hx23 : gpr32 s 23#5 (sha256A st block 46))
    (hx24 : gpr32 s 24#5 (sha256E st block 48)) (hx25 : gpr32 s 25#5 (sha256W block 40))
    (hpost : ∀ s' : State,
      s'.pc = b + 7852#64 → s'.status = .Running → s'.spAligned = true →
      s'.sp = sp → calleeSavedVRegs s' = calleeSavedVRegs s →
      SepWP (haclPC1.rebase b) (b + 7852#64) s'
        (haclActiveStack sp (sha256W block 35) (sha256W block 34) stA
           (sha256A st block 3) (sha256E st block 3) (sha256A st block 2) (sha256E st block 2)
           (sha256A st block 1) (sha256E st block 1) (sha256A st block 0) (sha256E st block 0)
           (sha256W block 46) (sha256W block 47) ∗
         haclStateCells stA
           ((sha256CompressBlock st block).getD 0 0#32) ((sha256CompressBlock st block).getD 1 0#32)
           ((sha256CompressBlock st block).getD 2 0#32) ((sha256CompressBlock st block).getD 3 0#32)
           ((sha256CompressBlock st block).getD 4 0#32) ((sha256CompressBlock st block).getD 5 0#32)
           ((sha256CompressBlock st block).getD 6 0#32) ((sha256CompressBlock st block).getD 7 0#32) ∗ R) post) :
    SepWP (haclPC1.rebase b) (b + 7852#64) s
      (haclActiveStack sp (sha256W block 35) (sha256W block 34) stA
         (sha256A st block 3) (sha256E st block 3) (sha256A st block 2) (sha256E st block 2)
         (sha256A st block 1) (sha256E st block 1) (sha256A st block 0) (sha256E st block 0)
         (sha256W block 6) (sha256W block 31) ∗
       haclStateCells stA u0 u1 u2 u3 u4 u5 u6 u7 ∗ R) post := by
  subst hb; unfold haclActiveStack haclStateCells; wp_simp_pre only [sepConj_assoc]
  wp_hacl_steps 581
  refine SepWP.of_pre_eq ?_ (hpost _ ?_ ?_ ?_ ?_ ?_)
  · rw [sha256CompressBlock_eq_sha256AE st block hst]
    unfold haclActiveStack haclStateCells
    simp only [List.getD_cons_zero, List.getD_cons_succ, sepConj_assoc]
  · rfl
  · simp [wp_norm, hrun]
  · rw [← hsp_align]; simp only [State.spAligned, State.sp_setPC, State.sp_setMem, State.sp_writeReg64_gpr]
  · simp [wp_norm, hsp]
  · simp only [calleeSavedVRegs_setPC, calleeSavedVRegs_setMem, calleeSavedVRegs_writeReg64]

/-! ## 6. Stack Rearrangement, Epilogue (`0x1eac → ret`), & Public `subroutine_ok` Theorems -/

private def haclMidCells64 (sp0 : BitVec 64) (v2 v3 v4 v5 v6 v7 v8 : BitVec 64) : SepProp :=
  ((sp0 - 152#64) ↦₆₄ v2) ∗ ((sp0 - 144#64) ↦₆₄ v3) ∗ ((sp0 - 136#64) ↦₆₄ v4) ∗
  ((sp0 - 128#64) ↦₆₄ v5) ∗ ((sp0 - 120#64) ↦₆₄ v6) ∗ ((sp0 - 112#64) ↦₆₄ v7) ∗
  ((sp0 - 104#64) ↦₆₄ v8)

private theorem cells20_eq_chunks (sp0 : BitVec 64)
    (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : BitVec 64) :
    (((sp0 - 160#64) ↦₆₄ v1) ∗ ((sp0 - 152#64) ↦₆₄ v2) ∗ ((sp0 - 144#64) ↦₆₄ v3) ∗
     ((sp0 - 136#64) ↦₆₄ v4) ∗ ((sp0 - 128#64) ↦₆₄ v5) ∗ ((sp0 - 120#64) ↦₆₄ v6) ∗
     ((sp0 - 112#64) ↦₆₄ v7) ∗ ((sp0 - 104#64) ↦₆₄ v8) ∗ ((sp0 - 96#64) ↦₆₄ v9) ∗
     ((sp0 - 88#64) ↦₆₄ v10) ∗ ((sp0 - 80#64) ↦₆₄ v11) ∗ ((sp0 - 72#64) ↦₆₄ v12) ∗
     ((sp0 - 64#64) ↦₆₄ v13) ∗ ((sp0 - 56#64) ↦₆₄ v14) ∗ ((sp0 - 48#64) ↦₆₄ v15) ∗
     ((sp0 - 40#64) ↦₆₄ v16) ∗ ((sp0 - 32#64) ↦₆₄ v17) ∗ ((sp0 - 24#64) ↦₆₄ v18) ∗
     ((sp0 - 16#64) ↦₆₄ v19) ∗ ((sp0 - 8#64) ↦₆₄ v20)) =
    (((sp0 - 160#64) ↦₆₄ v1) ∗ haclMidCells64 sp0 v2 v3 v4 v5 v6 v7 v8 ∗
     haclCalleeSavedCells sp0 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20) := by
  unfold haclMidCells64 haclCalleeSavedCells
  simp only [sepConj_assoc]

private theorem chunks_entails_stackFrame160 (s0 : State)
    (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : BitVec 64) :
    (((s0.sp - 160#64) ↦₆₄ v1) ∗ haclMidCells64 s0.sp v2 v3 v4 v5 v6 v7 v8 ∗
     haclCalleeSavedCells s0.sp v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20) ⊢
    stackFrame s0 160 := by
  rw [← cells20_eq_chunks]
  exact stackFrame160_entails s0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20

private theorem pointsTo64_sub_split32 (sp off off4 v : BitVec 64) (hoff : off - 4#64 = off4 := by rfl) :
    ((sp - off) ↦₆₄ v) = (((sp - off) ↦₃₂ v.extractLsb' 0 32) ∗ ((sp - off4) ↦₃₂ v.extractLsb' 32 32)) := by
  have h : sp - off + 4#64 = sp - off4 := by subst hoff; bv_lin
  rw [pointsTo64_split32, h]

private theorem pointsTo32_sub_pair (sp off off4 : BitVec 64) (lo hi : BitVec 32)
    (hoff : off - 4#64 = off4 := by rfl) :
    (((sp - off) ↦₃₂ lo) ∗ ((sp - off4) ↦₃₂ hi)) = ((sp - off) ↦₆₄ (hi ++ lo)) := by
  have h : sp - off + 4#64 = sp - off4 := by subst hoff; bv_lin
  rw [← h, pointsTo32_pair]

private theorem haclActiveStack_sub160 (sp0 : BitVec 64)
    (w8 w12 : BitVec 32) (v16 : BitVec 64) (w24 w28 w32 w36 w40 w44 w48 w52 w56 w60 : BitVec 32) :
    haclActiveStack (sp0 - 160#64) w8 w12 v16 w24 w28 w32 w36 w40 w44 w48 w52 w56 w60 =
      (((sp0 - 152#64) ↦₃₂ w8) ∗ ((sp0 - 148#64) ↦₃₂ w12) ∗ ((sp0 - 144#64) ↦₆₄ v16) ∗
       ((sp0 - 136#64) ↦₃₂ w24) ∗ ((sp0 - 132#64) ↦₃₂ w28) ∗ ((sp0 - 128#64) ↦₃₂ w32) ∗
       ((sp0 - 124#64) ↦₃₂ w36) ∗ ((sp0 - 120#64) ↦₃₂ w40) ∗ ((sp0 - 116#64) ↦₃₂ w44) ∗
       ((sp0 - 112#64) ↦₃₂ w48) ∗ ((sp0 - 108#64) ↦₃₂ w52) ∗ ((sp0 - 104#64) ↦₃₂ w56) ∗
       ((sp0 - 100#64) ↦₃₂ w60)) := by
  have hsub (c : BitVec 64) : sp0 - 160#64 + c = sp0 - (160#64 - c) := by bv_lin
  unfold haclActiveStack; simp only [hsub]; rfl

private theorem haclMidCells64_to_active (sp0 v2 v3 v4 v5 v6 v7 v8 : BitVec 64) :
    haclMidCells64 sp0 v2 v3 v4 v5 v6 v7 v8 =
      haclActiveStack (sp0 - 160#64)
        (v2.extractLsb' 0 32) (v2.extractLsb' 32 32) v3
        (v4.extractLsb' 0 32) (v4.extractLsb' 32 32) (v5.extractLsb' 0 32) (v5.extractLsb' 32 32)
        (v6.extractLsb' 0 32) (v6.extractLsb' 32 32) (v7.extractLsb' 0 32) (v7.extractLsb' 32 32)
        (v8.extractLsb' 0 32) (v8.extractLsb' 32 32) := by
  rw [haclActiveStack_sub160]; unfold haclMidCells64
  rw [pointsTo64_sub_split32 sp0 152#64 148#64 v2, pointsTo64_sub_split32 sp0 136#64 132#64 v4,
      pointsTo64_sub_split32 sp0 128#64 124#64 v5, pointsTo64_sub_split32 sp0 120#64 116#64 v6,
      pointsTo64_sub_split32 sp0 112#64 108#64 v7, pointsTo64_sub_split32 sp0 104#64 100#64 v8]
  simp only [sepConj_assoc]

private theorem haclActive_to_midCells64 (sp0 : BitVec 64)
    (w8 w12 : BitVec 32) (v16 : BitVec 64) (w24 w28 w32 w36 w40 w44 w48 w52 w56 w60 : BitVec 32) :
    haclActiveStack (sp0 - 160#64) w8 w12 v16 w24 w28 w32 w36 w40 w44 w48 w52 w56 w60 =
      haclMidCells64 sp0 (w12 ++ w8) v16 (w28 ++ w24) (w36 ++ w32) (w44 ++ w40) (w52 ++ w48) (w60 ++ w56) := by
  rw [haclActiveStack_sub160]; unfold haclMidCells64
  rw [← pointsTo32_sub_pair sp0 152#64 148#64 w8 w12, ← pointsTo32_sub_pair sp0 136#64 132#64 w24 w28,
      ← pointsTo32_sub_pair sp0 128#64 124#64 w32 w36, ← pointsTo32_sub_pair sp0 120#64 116#64 w40 w44,
      ← pointsTo32_sub_pair sp0 112#64 108#64 w48 w52, ← pointsTo32_sub_pair sp0 104#64 100#64 w56 w60]
  simp only [sepConj_assoc]

private theorem haclStateCells_eq_shaStateBytes (stA : BitVec 64) (st : ShaState) :
    (stA ↦ₛ shaStateBytes st) =
      haclStateCells stA (st.toList.getD 0 0#32) (st.toList.getD 1 0#32) (st.toList.getD 2 0#32)
        (st.toList.getD 3 0#32) (st.toList.getD 4 0#32) (st.toList.getD 5 0#32)
        (st.toList.getD 6 0#32) (st.toList.getD 7 0#32) := by
  rw [pointsToBytes_shaStateBytes stA st]; rfl

private theorem perm_to_prologue (BLK ST V1 MID CS : SepProp) :
    (BLK ∗ ST) ∗ V1 ∗ MID ∗ CS = CS ∗ (MID ∗ ST ∗ BLK ∗ V1) := by
  simp only [sepConj_assoc]
  rw [sepConj_comm MID CS, sepConj_left_comm V1 CS, sepConj_left_comm ST CS, sepConj_left_comm BLK CS,
      sepConj_comm V1 MID, sepConj_left_comm ST MID, sepConj_left_comm BLK MID,
      sepConj_left_comm BLK ST]

private theorem perm_to_seg1 (CS ACT ST B1 B2 V1 : SepProp) :
    CS ∗ (ACT ∗ ST ∗ (B1 ∗ B2) ∗ V1) = ACT ∗ ST ∗ B1 ∗ (B2 ∗ V1 ∗ CS) := by
  rw [sepConj_comm CS _]; simp only [sepConj_assoc]

private theorem perm_post (CS MID ST BLK V1 : SepProp) :
    CS ∗ MID ∗ ST ∗ BLK ∗ V1 = BLK ∗ ST ∗ (V1 ∗ MID ∗ CS) := by
  rw [sepConj_left_comm ST BLK, sepConj_left_comm MID BLK, sepConj_left_comm CS BLK,
      sepConj_left_comm MID ST, sepConj_left_comm CS ST,
      sepConj_comm MID V1, sepConj_left_comm CS V1, sepConj_comm CS MID]

private theorem sha256Update_raw_ok_at [HaclPlacement] :
    subroutine_ok (haclPC1.rebase haclPl1.base) haclPl1.base sha256UpdateRawSpec := by
  apply subroutine_ok_of_sepWP_init
  rintro ⟨blkA, bs, stA, st⟩ R s0 hpc hrun hpre hsp_align
  dsimp only [sha256UpdateRawSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hbs, hx2, hx3⟩, hpre⟩
  refine ⟨_, hpre, ?_⟩
  have hblock : (bs.take 64).length = 64 := List.length_take_of_le hbs
  wp_conv_pre => rw [← sepConj_assoc]
  apply stackFrame160_elim
  intro v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
  wp_conv_pre => rw [cells20_eq_chunks, perm_to_prologue]
  apply SepWP.cut (mid := haclPl1.base + 168#64)
  apply haclUpdate_prologue haclPl1.base rfl s0 blkA stA bs.length
    v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 _ _
    hpc hrun hsp_align hx0 hx1 hbs hx2 hx3
  intro s1 hpc1 hrun1 hsp_al1 hsp1 hx29_1 hx0_1 hx2_1 hvregs1
  apply SepWP.done hpc1 hrun1
  change SepWP _ _ s1
    (haclCalleeSavedCells s0.sp (s0.readReg64 Reg.fp) (s0.readReg64 Reg.lr)
       (s0.readReg64 (Reg.gpr 28#5)) (s0.readReg64 (Reg.gpr 27#5))
       (s0.readReg64 (Reg.gpr 26#5)) (s0.readReg64 (Reg.gpr 25#5))
       (s0.readReg64 (Reg.gpr 24#5)) (s0.readReg64 (Reg.gpr 23#5))
       (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
       (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5)) ∗
     (haclMidCells64 s0.sp v2 v3 v4 v5 v6 v7 v8 ∗
      (stA ↦ₛ shaStateBytes st) ∗ (blkA ↦ₛ bs) ∗ ((s0.sp - 160#64) ↦₆₄ v1))) _
  wp_conv_pre =>
    rw [haclMidCells64_to_active, haclStateCells_eq_shaStateBytes stA st,
        pointsToBytes_take_drop blkA 64 bs hbs, perm_to_seg1]
  apply SepWP.cut (mid := haclPl1.base + 2032#64)
  apply haclUpdate_seg1 haclPl1.base rfl s1 (s0.sp - 160#64) blkA stA st.toList (bs.take 64)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hpc1 hrun1 hsp_al1 hblock hsp1 hx29_1 hx0_1 hx2_1
  intro s2 hpc2 hrun2 hsp_al2 hsp2 hx29_2 hvregs2 h2_0 h2_1 h2_2 h2_3 h2_4 h2_5 h2_6 h2_7 h2_8 h2_9
    h2_11 h2_12 h2_13 h2_17 h2_18 h2_19 h2_20 h2_21 h2_22 h2_23 h2_24 h2_25 h2_26 h2_28 h2_30
  apply SepWP.done hpc2 hrun2; apply SepWP.cut (mid := haclPl1.base + 3652#64)
  apply haclUpdate_seg2 haclPl1.base rfl s2 (s0.sp - 160#64) stA st.toList (bs.take 64)
    _ _ _ hpc2 hrun2 hsp_al2 hsp2 hx29_2 h2_0 h2_1 h2_2 h2_3 h2_4 h2_5 h2_6 h2_7 h2_8 h2_9
    h2_11 h2_12 h2_13 h2_17 h2_18 h2_19 h2_20 h2_21 h2_22 h2_23 h2_24 h2_25 h2_26 h2_28 h2_30
  intro s3 hpc3 hrun3 hsp_al3 hsp3 hx29_3 hvregs3 h3_0 h3_1 h3_3 h3_4 h3_5 h3_6 h3_7 h3_8 h3_9 h3_10
    h3_11 h3_12 h3_13 h3_17 h3_18 h3_19 h3_20 h3_21 h3_22 h3_23 h3_24 h3_26 h3_27 h3_28 h3_30
  apply SepWP.done hpc3 hrun3; apply SepWP.cut (mid := haclPl1.base + 5528#64)
  apply haclUpdate_seg3 haclPl1.base rfl s3 (s0.sp - 160#64) stA st.toList (bs.take 64)
    _ _ _ hpc3 hrun3 hsp_al3 hsp3 hx29_3 h3_0 h3_1 h3_3 h3_4 h3_5 h3_6 h3_7 h3_8 h3_9 h3_10
    h3_11 h3_12 h3_13 h3_17 h3_18 h3_19 h3_20 h3_21 h3_22 h3_23 h3_24 h3_26 h3_27 h3_28 h3_30
  intro s4 hpc4 hrun4 hsp_al4 hsp4 hx29_4 hvregs4 h4_0 h4_1 h4_2 h4_3 h4_4 h4_5 h4_6 h4_7 h4_8 h4_9
    h4_10 h4_11 h4_13 h4_14 h4_16 h4_17 h4_18 h4_19 h4_20 h4_22 h4_23 h4_24 h4_25
  apply SepWP.done hpc4 hrun4; apply SepWP.cut (mid := haclPl1.base + 7852#64)
  apply haclUpdate_seg4 haclPl1.base rfl s4 (s0.sp - 160#64) stA st.toList (bs.take 64)
    _ _ _ _ _ _ _ _ _ _ hpc4 hrun4 hsp_al4 st.2 hsp4 hx29_4 h4_0 h4_1 h4_2 h4_3 h4_4 h4_5 h4_6 h4_7 h4_8
    h4_9 h4_10 h4_11 h4_13 h4_14 h4_16 h4_17 h4_18 h4_19 h4_20 h4_22 h4_23 h4_24 h4_25
  intro s5 hpc5 hrun5 hsp_al5 hsp5 hvregs5; apply SepWP.done hpc5 hrun5
  let st' := sha256CompressState st (bs.take 64)
  change SepWP _ _ s5
    (haclActiveStack (s0.sp - 160#64) (sha256W (bs.take 64) 35) (sha256W (bs.take 64) 34) stA
       (sha256A st.toList (bs.take 64) 3) (sha256E st.toList (bs.take 64) 3)
       (sha256A st.toList (bs.take 64) 2) (sha256E st.toList (bs.take 64) 2)
       (sha256A st.toList (bs.take 64) 1) (sha256E st.toList (bs.take 64) 1)
       (sha256A st.toList (bs.take 64) 0) (sha256E st.toList (bs.take 64) 0)
       (sha256W (bs.take 64) 46) (sha256W (bs.take 64) 47) ∗
     haclStateCells stA (st'.toList.getD 0 0#32) (st'.toList.getD 1 0#32)
       (st'.toList.getD 2 0#32) (st'.toList.getD 3 0#32) (st'.toList.getD 4 0#32)
       (st'.toList.getD 5 0#32) (st'.toList.getD 6 0#32) (st'.toList.getD 7 0#32) ∗
     (blkA ↦ₛ bs.take 64) ∗ ((blkA + BitVec.ofNat 64 64) ↦ₛ bs.drop 64) ∗
     ((s0.sp - 160#64) ↦₆₄ v1) ∗
     haclCalleeSavedCells s0.sp (s0.readReg64 Reg.fp) (s0.readReg64 Reg.lr)
       (s0.readReg64 (Reg.gpr 28#5)) (s0.readReg64 (Reg.gpr 27#5))
       (s0.readReg64 (Reg.gpr 26#5)) (s0.readReg64 (Reg.gpr 25#5))
       (s0.readReg64 (Reg.gpr 24#5)) (s0.readReg64 (Reg.gpr 23#5))
       (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
       (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5))) _
  wp_conv_pre =>
    rw [haclActive_to_midCells64, ← haclStateCells_eq_shaStateBytes stA st',
        ← perm_to_seg1, ← pointsToBytes_take_drop blkA 64 bs hbs]
    unfold haclCalleeSavedCells
  wp_simp_pre only [sepConj_assoc]
  wp_sym_steps 8
  refine SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun5]) ⟨?_, by simp [wp_norm], ?_⟩
  · intro hmem
    have hcs (sp0 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : BitVec 64) (Q : SepProp) :
        ((sp0 - 96#64) ↦₆₄ v9) ∗ ((sp0 - 88#64) ↦₆₄ v10) ∗ ((sp0 - 80#64) ↦₆₄ v11) ∗
        ((sp0 - 72#64) ↦₆₄ v12) ∗ ((sp0 - 64#64) ↦₆₄ v13) ∗ ((sp0 - 56#64) ↦₆₄ v14) ∗
        ((sp0 - 48#64) ↦₆₄ v15) ∗ ((sp0 - 40#64) ↦₆₄ v16) ∗ ((sp0 - 32#64) ↦₆₄ v17) ∗
        ((sp0 - 24#64) ↦₆₄ v18) ∗ ((sp0 - 16#64) ↦₆₄ v19) ∗ ((sp0 - 8#64) ↦₆₄ v20) ∗ Q =
        haclCalleeSavedCells sp0 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 ∗ Q := by
      unfold haclCalleeSavedCells; simp only [sepConj_assoc]
    refine Satisfies.of_entails hmem (sepConj_mono_left ?_)
    rw [hcs, perm_post]
    exact sepConj_mono_right (sepConj_mono_right
      (chunks_entails_stackFrame160 s0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _))
  · rw [CalleeSavedPreserved.iff_regs]
    refine ⟨by simp [wp_norm], by simp [wp_norm], by simp [wp_norm], by simp [wp_norm],
            by simp [wp_norm], by simp [wp_norm], by simp [wp_norm], by simp [wp_norm],
            by simp [wp_norm], by simp [wp_norm], by simp [wp_norm], ?_⟩
    simp only [calleeSavedVRegs_setPC, calleeSavedVRegs_writeReg64]
    rw [hvregs5, hvregs4, hvregs3, hvregs2, hvregs1]

/-- Raw `subroutine_ok` for Block 1 (`libcrux_sha2::hacl::sha256_update`) on its standalone
relocated block program. -/
public theorem sha256Update_raw_subroutineOk {mpl : Obj.MultiPlacement}
    (hpl : libcruxHmacLib.Placeable mpl) :
    subroutine_ok (libcruxHmacLib.blockProgram mpl 1) (mpl.base 1) sha256UpdateRawSpec := by
  let _ : HaclPlacement := ⟨mpl, hpl⟩
  change subroutine_ok (libcruxHmacLib.blockProgram haclMpl 1) (haclMpl.base 1) sha256UpdateRawSpec
  rw [← haclPC1_eq_blockProgram, ← haclPl1_base]
  exact sha256Update_raw_ok_at

/-- Ambient `Program`-lifted `subroutine_ok` for Block 1 (`libcrux_sha2::hacl::sha256_update`). -/
public theorem sha256Update_subroutineOk {P : Program} {mpl : Obj.MultiPlacement}
    (hP : HaclInProg P mpl) :
    subroutine_ok P (mpl.base 1) (withHaclPreserved mpl sha256UpdateRawSpec) := by
  refine subroutine_ok_of_pure_block (by decide : 1 < 7) hP ?_ ?_ ?_ ?_ ?_
    (sha256Update_raw_subroutineOk hP.placeable)
  · rintro ⟨blkA, bs, stA, st⟩ s m
    simp [sha256UpdateRawSpec, stackFrame]
  · rintro ⟨blkA, bs, stA, st⟩ s1 s2 m1 m2
    simp [sha256UpdateRawSpec, stackFrame]
  · rintro ⟨blkA, bs, stA, st⟩ s0 sf; rfl
  · rintro ⟨blkA, bs, stA, st⟩ c s0 sf; rfl
  · rintro ⟨blkA, bs, stA, st⟩ s0 sf; rfl

end LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclUpdateStep
