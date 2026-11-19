/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import LibsignalBinary.Specifications.LibsignalHmac
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Cells -- proof-setup: allow-public-import
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Math -- proof-setup: allow-public-import
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256Code -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256Fetch
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256Step

/-!
# Multi-Block Loop, Prologue/Epilogue, and Raw `subroutine_ok` for `sha2::sha256::compress256`

Verifies `_RNvNtCsbvWyylYiyxg_4sha26sha25611compress256` (`0x0000 → 0x1dd4`, `7,636` bytes,
`176`-byte stack frame, `.rodata` `K32` at `pl.ρ sha2K32Sym`), providing `chunks64_of_length_lt`,
`chunks64_cons_take_drop`, `compress256RawROSpec`, `compress256_fnAddr`, and
`compress256_raw_ro_ok`.
-/

set_option autoImplicit false
set_option maxRecDepth 200000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256Loop

open Arm64 ProofLib
open CryptoGames.HMAC (ShaState chunks64)
open CryptoVerification.LibsignalHmac (shaStateBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Cells
  (pointsToBytesRO_take_drop sha256KBytes pointsToBytesRO_sha256KBytes_eq_chunks
   stackFrame176_elim stackFrame176_entails)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Math
  (sha256CompressState sha256CompressState_toList chunks64_eq_map_range pointsToBytes_shaStateBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256Code
  (compress256Sym sha2K32Sym compress256Block compress256Lib Compress256Placement compress256PC)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256Step
  (sha256LoopStack sha2K32AllCells compress256_one_block)

arm64_proof_prelude

@[wp_norm]
private theorem zeroExtend_32_64_eq_setWidth (x : BitVec 32) :
    BitVec.zeroExtend 64 x = BitVec.setWidth 64 x := rfl

/-! ## 1. `HMAC.chunks64` Block-Splitting Lemmas -/

theorem chunks64_of_length_lt {bs : List (BitVec 8)} (h : bs.length < 64) :
    chunks64 bs = [] := by
  rw [chunks64_eq_map_range, Nat.div_eq_of_lt h, List.range_zero, List.map_nil]

theorem chunks64_cons_take_drop {bs : List (BitVec 8)} (h : 64 ≤ bs.length) :
    chunks64 bs = bs.take 64 :: chunks64 (bs.drop 64) := by
  rw [chunks64_eq_map_range, chunks64_eq_map_range]
  have hdiv : bs.length / 64 = (bs.drop 64).length / 64 + 1 := by
    rw [List.length_drop]
    omega
  rw [hdiv, List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [Nat.mul_zero, List.drop_zero]
  congr 1
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_apply]
  have hmul : 64 * (j + 1) = 64 + 64 * j := by omega
  rw [hmul, ← List.drop_drop]

/-! ## 2. Multi-Block Loop Induction (`compress256_loop`) -/

private theorem loop_pre_split_64 (stP kcells R : SepProp) (b_ptr : BitVec 64)
    (bs : List (BitVec 8)) (hle : 64 ≤ bs.length) :
    (stP ∗ (b_ptr ↦ᵣ bs) ∗ kcells ∗ R) =
      (stP ∗ (b_ptr ↦ᵣ bs.take 64) ∗ kcells ∗ (((b_ptr + 64#64) ↦ᵣ bs.drop 64) ∗ R)) := by
  rw [pointsToBytesRO_take_drop b_ptr 64 bs hle]
  simp only [sepConj_assoc]
  rw [sepConj_left_comm ((b_ptr + 64#64) ↦ᵣ bs.drop 64) kcells]

private theorem loop_pre_advance_64 (stP kcells R : SepProp) (b_ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    (stP ∗ (b_ptr ↦ᵣ bs.take 64) ∗ kcells ∗ (((b_ptr + 64#64) ↦ᵣ bs.drop 64) ∗ R)) =
      (stP ∗ ((b_ptr + 64#64) ↦ᵣ bs.drop 64) ∗ kcells ∗ ((b_ptr ↦ᵣ bs.take 64) ∗ R)) := by
  rw [sepConj_left_comm kcells ((b_ptr + 64#64) ↦ᵣ bs.drop 64),
      sepConj_left_comm (b_ptr ↦ᵣ bs.take 64) ((b_ptr + 64#64) ↦ᵣ bs.drop 64),
      sepConj_left_comm (b_ptr ↦ᵣ bs.take 64) kcells]

private theorem add_64_bne_of_le (b_ptr : BitVec 64) (rem : Nat)
    (hlen : 64 * (rem + 1 + 1) ≤ 2 ^ 64) :
    (b_ptr + 64#64 != b_ptr + BitVec.ofNat 64 (64 * (rem + 1 + 1))) = true := by
  rw [bne_iff_ne]
  intro h
  have h2 : (b_ptr + 64#64).toNat = (b_ptr + BitVec.ofNat 64 (64 * (rem + 1 + 1))).toNat :=
    congrArg BitVec.toNat h
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h2
  omega

private theorem compress256_loop [Compress256Placement] (rem : Nat)
    (b : BitVec 64) (hb : b = Compress256Placement.pl.base)
    (s : State) (b_ptr : BitVec 64) (st : ShaState) (bs : List (BitVec 8))
    (vEnd : BitVec 64)
    (w1c w20 w24 w28 w2c w30 w34 w38 w3c w40 w44 : BitVec 32)
    (v48 : BitVec 64)
    (w58 w5c : BitVec 32)
    (R : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = b + 0x38#64)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hbs : bs.length = 64 * (rem + 1))
    (hbs_max : bs.length ≤ 2 ^ 64)
    (hvEnd : vEnd = b_ptr + BitVec.ofNat 64 (64 * (rem + 1)))
    (hx1 : s.readReg64 (Reg.gpr 1#5) = b_ptr)
    (hx2 : s.readReg64 (Reg.gpr 2#5) = BitVec.setWidth 64 (st.toList.getD 0 0#32))
    (hx5 : s.readReg64 (Reg.gpr 5#5) = BitVec.setWidth 64 (st.toList.getD 1 0#32))
    (hx6 : s.readReg64 (Reg.gpr 6#5) = BitVec.setWidth 64 (st.toList.getD 2 0#32))
    (hx7 : s.readReg64 (Reg.gpr 7#5) = BitVec.setWidth 64 (st.toList.getD 3 0#32))
    (hx11 : s.readReg64 (Reg.gpr 11#5) = BitVec.setWidth 64 (st.toList.getD 4 0#32))
    (hx17 : s.readReg64 (Reg.gpr 17#5) = BitVec.setWidth 64 (st.toList.getD 5 0#32))
    (hx3 : s.readReg64 (Reg.gpr 3#5) = BitVec.setWidth 64 (st.toList.getD 6 0#32))
    (hx4 : s.readReg64 (Reg.gpr 4#5) = BitVec.setWidth 64 (st.toList.getD 7 0#32))
    (hpost : ∀ (s' : State)
      (w1c' w20' w24' w28' w2c' w30' w34' w38' w3c' w40' w44' : BitVec 32)
      (v48' : BitVec 64)
      (w58' w5c' : BitVec 32),
      s'.pc = b + 0x1da0#64 →
      s'.status = .Running →
      s'.spAligned = true →
      s'.sp = s.sp →
      s'.readReg64 Reg.fp = s.readReg64 Reg.fp →
      calleeSavedVRegs s' = calleeSavedVRegs s →
      s'.readReg64 (Reg.gpr 2#5) =
        BitVec.setWidth 64 (((chunks64 bs).foldl sha256CompressState st).toList.getD 0 0#32) →
      s'.readReg64 (Reg.gpr 5#5) =
        BitVec.setWidth 64 (((chunks64 bs).foldl sha256CompressState st).toList.getD 1 0#32) →
      s'.readReg64 (Reg.gpr 6#5) =
        BitVec.setWidth 64 (((chunks64 bs).foldl sha256CompressState st).toList.getD 2 0#32) →
      s'.readReg64 (Reg.gpr 7#5) =
        BitVec.setWidth 64 (((chunks64 bs).foldl sha256CompressState st).toList.getD 3 0#32) →
      s'.readReg64 (Reg.gpr 11#5) =
        BitVec.setWidth 64 (((chunks64 bs).foldl sha256CompressState st).toList.getD 4 0#32) →
      s'.readReg64 (Reg.gpr 17#5) =
        BitVec.setWidth 64 (((chunks64 bs).foldl sha256CompressState st).toList.getD 5 0#32) →
      s'.readReg64 (Reg.gpr 3#5) =
        BitVec.setWidth 64 (((chunks64 bs).foldl sha256CompressState st).toList.getD 6 0#32) →
      s'.readReg64 (Reg.gpr 4#5) =
        BitVec.setWidth 64 (((chunks64 bs).foldl sha256CompressState st).toList.getD 7 0#32) →
      SepWP (compress256PC.rebase b) (b + 0x1da0#64) s'
        (sha256LoopStack s.sp vEnd w1c' w20' w24' w28' w2c' w30' w34' w38' w3c' w40' w44' v48' w58' w5c' ∗
         (b_ptr ↦ᵣ bs) ∗
         sha2K32AllCells (Compress256Placement.pl.ρ "sha2:.rodata.sha2::consts::K32") ∗ R)
        post) :
    SepWP (compress256PC.rebase b) (b + 0x1da0#64) s
      (sha256LoopStack s.sp vEnd w1c w20 w24 w28 w2c w30 w34 w38 w3c w40 w44 v48 w58 w5c ∗
       (b_ptr ↦ᵣ bs) ∗
       sha2K32AllCells (Compress256Placement.pl.ρ "sha2:.rodata.sha2::consts::K32") ∗ R)
      post := by
  induction rem generalizing s b_ptr st bs w1c w20 w24 w28 w2c w30 w34 w38 w3c w40 w44 v48 w58 w5c R with
  | zero =>
    have hbs64 : bs.length = 64 := by omega
    have hchunks : (chunks64 bs).foldl sha256CompressState st = sha256CompressState st bs := by
      rw [chunks64_cons_take_drop (by omega), List.take_of_length_le (by omega),
          chunks64_of_length_lt (by simp [hbs64]), List.foldl_cons, List.foldl_nil]
    apply compress256_one_block b hb s b_ptr st.toList bs vEnd
      w1c w20 w24 w28 w2c w30 w34 w38 w3c w40 w44 v48 w58 w5c R post
      hpc hrun hsp_align st.2 hbs64 hx1 hx2 hx5 hx6 hx7 hx11 hx17 hx3 hx4
    intro s' w1c' w20' w24' w28' w2c' w30' w34' w38' w3c' w40' w44' v48' w58' w5c'
      hpc' hrun' hsp_align' hsp' hfp' hvregs' _hx1' hx2' hx5' hx6' hx7' hx11' hx17' hx3' hx4'
    have hcond : (b_ptr + 64#64 != vEnd) = false := by
      rw [hvEnd]
      change (b_ptr + 64#64 != b_ptr + 64#64) = false
      exact bne_self_eq_false _
    rw [hcond] at hpc'
    simp only [Bool.false_eq_true, ↓reduceIte] at hpc'
    rw [← sha256CompressState_toList, ← hchunks] at hx2' hx5' hx6' hx7' hx11' hx17' hx3' hx4'
    exact hpost s' w1c' w20' w24' w28' w2c' w30' w34' w38' w3c' w40' w44' v48' w58' w5c'
      hpc' hrun' hsp_align' hsp' hfp' hvregs' hx2' hx5' hx6' hx7' hx11' hx17' hx3' hx4'
  | succ rem ih =>
    have hle64 : 64 ≤ bs.length := by omega
    have htake : (bs.take 64).length = 64 := by simp [hle64]
    have hdrop : (bs.drop 64).length = 64 * (rem + 1) := by simp [hbs]; omega
    have hdrop_max : (bs.drop 64).length ≤ 2 ^ 64 := by simp; omega
    have hchunks : (chunks64 bs).foldl sha256CompressState st =
        (chunks64 (bs.drop 64)).foldl sha256CompressState (sha256CompressState st (bs.take 64)) := by
      rw [chunks64_cons_take_drop hle64, List.foldl_cons]
    rw [loop_pre_split_64 _ _ _ b_ptr bs hle64]
    apply compress256_one_block b hb s b_ptr st.toList (bs.take 64) vEnd
      w1c w20 w24 w28 w2c w30 w34 w38 w3c w40 w44 v48 w58 w5c _ post
      hpc hrun hsp_align st.2 htake hx1 hx2 hx5 hx6 hx7 hx11 hx17 hx3 hx4
    intro s1 w1c1 w201 w241 w281 w2c1 w301 w341 w381 w3c1 w401 w441 v481 w581 w5c1
      hpc1 hrun1 hsp_align1 hsp1 hfp1 hvregs1 hx1_1 hx2_1 hx5_1 hx6_1 hx7_1 hx11_1 hx17_1 hx3_1 hx4_1
    have hcond : (b_ptr + 64#64 != vEnd) = true := by
      rw [hvEnd]
      exact add_64_bne_of_le b_ptr rem (by omega)
    simp only [hcond, ↓reduceIte] at hpc1
    rw [loop_pre_advance_64]
    have hvEnd' : vEnd = (b_ptr + 64#64) + BitVec.ofNat 64 (64 * (rem + 1)) := by
      rw [hvEnd, BitVec.add_assoc]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    rw [← hsp1]
    rw [← sha256CompressState_toList] at hx2_1 hx5_1 hx6_1 hx7_1 hx11_1 hx17_1 hx3_1 hx4_1
    apply ih s1 (b_ptr + 64#64) (sha256CompressState st (bs.take 64)) (bs.drop 64)
      w1c1 w201 w241 w281 w2c1 w301 w341 w381 w3c1 w401 w441 v481 w581 w5c1
      ((b_ptr ↦ᵣ bs.take 64) ∗ R)
      hpc1 hrun1 hsp_align1 hdrop hdrop_max hvEnd'
      hx1_1 hx2_1 hx5_1 hx6_1 hx7_1 hx11_1 hx17_1 hx3_1 hx4_1
    intro s2 w1c2 w202 w242 w282 w2c2 w302 w342 w382 w3c2 w402 w442 v482 w582 w5c2
      hpc2 hrun2 hsp_align2 hsp2 hfp2 hvregs2 hx2_2 hx5_2 hx6_2 hx7_2 hx11_2 hx17_2 hx3_2 hx4_2
    rw [hsp1, ← loop_pre_advance_64, ← loop_pre_split_64 _ _ _ b_ptr bs hle64]
    rw [← hchunks] at hx2_2 hx5_2 hx6_2 hx7_2 hx11_2 hx17_2 hx3_2 hx4_2
    exact hpost s2 w1c2 w202 w242 w282 w2c2 w302 w342 w382 w3c2 w402 w442 v482 w582 w5c2
      hpc2 hrun2 hsp_align2 (hsp2.trans hsp1) (hfp2.trans hfp1) (hvregs2.trans hvregs1)
      hx2_2 hx5_2 hx6_2 hx7_2 hx11_2 hx17_2 hx3_2 hx4_2

/-! ## 3. Prologue / Epilogue Stack & State Rearrangement -/

private def sha256StateCells (a : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 32) : SepProp :=
  (a ↦₃₂ w0) ∗ ((a + 4#64) ↦₃₂ w1) ∗ ((a + 8#64) ↦₃₂ w2) ∗ ((a + 12#64) ↦₃₂ w3) ∗
  ((a + 16#64) ↦₃₂ w4) ∗ ((a + 20#64) ↦₃₂ w5) ∗ ((a + 24#64) ↦₃₂ w6) ∗ ((a + 28#64) ↦₃₂ w7)

private def sha256SavedCalleeCells (sp : BitVec 64)
    (v1 v10 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 : BitVec 64) (w18 : BitVec 32) : SepProp :=
  ((sp - 168#64) ↦₆₄ v1) ∗ ((sp - 152#64) ↦₃₂ w18) ∗ ((sp - 96#64) ↦₆₄ v10) ∗
  ((sp - 80#64) ↦₆₄ v12) ∗ ((sp - 72#64) ↦₆₄ v13) ∗ ((sp - 64#64) ↦₆₄ v14) ∗
  ((sp - 56#64) ↦₆₄ v15) ∗ ((sp - 48#64) ↦₆₄ v16) ∗ ((sp - 40#64) ↦₆₄ v17) ∗
  ((sp - 32#64) ↦₆₄ v18) ∗ ((sp - 24#64) ↦₆₄ v19) ∗ ((sp - 16#64) ↦₆₄ v20) ∗
  ((sp - 8#64) ↦₆₄ v21)

private theorem sha256LoopStack_sub176 (sp : BitVec 64) (vEnd : BitVec 64)
    (w1c w20 w24 w28 w2c w30 w34 w38 w3c w40 w44 : BitVec 32)
    (v48 : BitVec 64) (w58 w5c : BitVec 32) :
    sha256LoopStack (sp - 176#64) vEnd w1c w20 w24 w28 w2c w30 w34 w38 w3c w40 w44 v48 w58 w5c =
      (((sp - 160#64) ↦₆₄ vEnd) ∗
       ((sp - 148#64) ↦₃₂ w1c) ∗ ((sp - 144#64) ↦₃₂ w20) ∗ ((sp - 140#64) ↦₃₂ w24) ∗
       ((sp - 136#64) ↦₃₂ w28) ∗ ((sp - 132#64) ↦₃₂ w2c) ∗ ((sp - 128#64) ↦₃₂ w30) ∗
       ((sp - 124#64) ↦₃₂ w34) ∗ ((sp - 120#64) ↦₃₂ w38) ∗ ((sp - 116#64) ↦₃₂ w3c) ∗
       ((sp - 112#64) ↦₃₂ w40) ∗ ((sp - 108#64) ↦₃₂ w44) ∗
       ((sp - 104#64) ↦₆₄ v48) ∗
       ((sp - 88#64) ↦₃₂ w58) ∗ ((sp - 84#64) ↦₃₂ w5c)) := by
  have hsub (b : BitVec 64) : sp - 176#64 + b = sp - (176#64 - b) := by bv_lin
  unfold sha256LoopStack
  simp only [hsub]
  rfl

private theorem pointsTo64_sub_split32 (sp : BitVec 64) (off off4 : BitVec 64) (v : BitVec 64)
    (hoff : off - 4#64 = off4 := by rfl) :
    ((sp - off) ↦₆₄ v) =
      (((sp - off) ↦₃₂ v.extractLsb' 0 32) ∗ ((sp - off4) ↦₃₂ v.extractLsb' 32 32)) := by
  have h : sp - off + 4#64 = sp - off4 := by subst hoff; bv_lin
  rw [pointsTo64_split32, h]

private theorem pointsTo32_sub_pair (sp : BitVec 64) (off off4 : BitVec 64) (lo hi : BitVec 32)
    (hoff : off - 4#64 = off4 := by rfl) :
    (((sp - off) ↦₃₂ lo) ∗ ((sp - off4) ↦₃₂ hi)) = ((sp - off) ↦₆₄ (hi ++ lo)) := by
  have h : sp - off + 4#64 = sp - off4 := by subst hoff; bv_lin
  rw [← h, pointsTo32_pair]

private def sha256LoopMidCells (sp : BitVec 64)
    (w1c w20 w24 w28 w2c w30 w34 w38 w3c w40 w44 : BitVec 32) (v48 : BitVec 64) : SepProp :=
  ((sp - 148#64) ↦₃₂ w1c) ∗ ((sp - 144#64) ↦₃₂ w20) ∗ ((sp - 140#64) ↦₃₂ w24) ∗
  ((sp - 136#64) ↦₃₂ w28) ∗ ((sp - 132#64) ↦₃₂ w2c) ∗ ((sp - 128#64) ↦₃₂ w30) ∗
  ((sp - 124#64) ↦₃₂ w34) ∗ ((sp - 120#64) ↦₃₂ w38) ∗ ((sp - 116#64) ↦₃₂ w3c) ∗
  ((sp - 112#64) ↦₃₂ w40) ∗ ((sp - 108#64) ↦₃₂ w44) ∗ ((sp - 104#64) ↦₆₄ v48)

private def sha256CalleeTail (sp : BitVec 64)
    (v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 : BitVec 64) : SepProp :=
  ((sp - 80#64) ↦₆₄ v12) ∗ ((sp - 72#64) ↦₆₄ v13) ∗ ((sp - 64#64) ↦₆₄ v14) ∗
  ((sp - 56#64) ↦₆₄ v15) ∗ ((sp - 48#64) ↦₆₄ v16) ∗ ((sp - 40#64) ↦₆₄ v17) ∗
  ((sp - 32#64) ↦₆₄ v18) ∗ ((sp - 24#64) ↦₆₄ v19) ∗ ((sp - 16#64) ↦₆₄ v20) ∗
  ((sp - 8#64) ↦₆₄ v21)

private theorem perm11 (K ST BLK SA V1 L1 W18 L2 V10 L3 CALLEE : SepProp) :
    (K ∗ ST ∗ BLK ∗ SA ∗ V1 ∗ L1 ∗ W18 ∗ L2 ∗ V10 ∗ L3 ∗ CALLEE) =
    ((L1 ∗ L2 ∗ L3) ∗ BLK ∗ K ∗ (ST ∗ SA ∗ (V1 ∗ W18 ∗ V10 ∗ CALLEE))) := by
  simp only [sepConj_assoc]
  rw [sepConj_left_comm ST BLK, sepConj_left_comm K BLK,
      sepConj_left_comm V1 L1, sepConj_left_comm SA L1, sepConj_left_comm ST L1,
      sepConj_left_comm K L1, sepConj_left_comm BLK L1,
      sepConj_left_comm W18 L2, sepConj_left_comm V1 L2, sepConj_left_comm SA L2,
      sepConj_left_comm ST L2, sepConj_left_comm K L2, sepConj_left_comm BLK L2,
      sepConj_left_comm V10 L3, sepConj_left_comm W18 L3, sepConj_left_comm V1 L3,
      sepConj_left_comm SA L3, sepConj_left_comm ST L3, sepConj_left_comm K L3,
      sepConj_left_comm BLK L3]

private theorem stack_state_perm [Compress256Placement]
    (stA blkA : BitVec 64) (bs : List (BitVec 8))
    (w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 32) (sp : BitVec 64)
    (v1 vEnd : BitVec 64)
    (w18 w1c w20 w24 w28 w2c w30 w34 w38 w3c w40 w44 : BitVec 32)
    (v48 v10 : BitVec 64) (w58 w5c : BitVec 32)
    (v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 : BitVec 64) :
    (sha2K32AllCells (Compress256Placement.pl.ρ "sha2:.rodata.sha2::consts::K32") ∗
     (stA ↦₃₂ w0) ∗ ((stA + 4#64) ↦₃₂ w1) ∗ ((stA + 8#64) ↦₃₂ w2) ∗ ((stA + 12#64) ↦₃₂ w3) ∗
     ((stA + 16#64) ↦₃₂ w4) ∗ ((stA + 20#64) ↦₃₂ w5) ∗ ((stA + 24#64) ↦₃₂ w6) ∗ ((stA + 28#64) ↦₃₂ w7) ∗
     (blkA ↦ᵣ bs) ∗ stackAt (sp - 168#64) 8 ∗
     ((sp - 168#64) ↦₆₄ v1) ∗ ((sp - 160#64) ↦₆₄ vEnd) ∗
     ((sp - 152#64) ↦₃₂ w18) ∗ ((sp - 148#64) ↦₃₂ w1c) ∗
     ((sp - 144#64) ↦₃₂ w20) ∗ ((sp - 140#64) ↦₃₂ w24) ∗
     ((sp - 136#64) ↦₃₂ w28) ∗ ((sp - 132#64) ↦₃₂ w2c) ∗
     ((sp - 128#64) ↦₃₂ w30) ∗ ((sp - 124#64) ↦₃₂ w34) ∗
     ((sp - 120#64) ↦₃₂ w38) ∗ ((sp - 116#64) ↦₃₂ w3c) ∗
     ((sp - 112#64) ↦₃₂ w40) ∗ ((sp - 108#64) ↦₃₂ w44) ∗
     ((sp - 104#64) ↦₆₄ v48) ∗ ((sp - 96#64) ↦₆₄ v10) ∗
     ((sp - 88#64) ↦₃₂ w58) ∗ ((sp - 84#64) ↦₃₂ w5c) ∗
     ((sp - 80#64) ↦₆₄ v12) ∗ ((sp - 72#64) ↦₆₄ v13) ∗ ((sp - 64#64) ↦₆₄ v14) ∗
     ((sp - 56#64) ↦₆₄ v15) ∗ ((sp - 48#64) ↦₆₄ v16) ∗ ((sp - 40#64) ↦₆₄ v17) ∗
     ((sp - 32#64) ↦₆₄ v18) ∗ ((sp - 24#64) ↦₆₄ v19) ∗ ((sp - 16#64) ↦₆₄ v20) ∗
     ((sp - 8#64) ↦₆₄ v21)) =
    (sha256LoopStack (sp - 176#64) vEnd w1c w20 w24 w28 w2c w30 w34 w38 w3c w40 w44 v48 w58 w5c ∗
     (blkA ↦ᵣ bs) ∗
     sha2K32AllCells (Compress256Placement.pl.ρ "sha2:.rodata.sha2::consts::K32") ∗
     (sha256StateCells stA w0 w1 w2 w3 w4 w5 w6 w7 ∗
      stackAt (sp - 168#64) 8 ∗
      sha256SavedCalleeCells sp v1 v10 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 w18)) := by
  have h := perm11
    (sha2K32AllCells (Compress256Placement.pl.ρ "sha2:.rodata.sha2::consts::K32"))
    (sha256StateCells stA w0 w1 w2 w3 w4 w5 w6 w7)
    (blkA ↦ᵣ bs)
    (stackAt (sp - 168#64) 8)
    ((sp - 168#64) ↦₆₄ v1)
    ((sp - 160#64) ↦₆₄ vEnd)
    ((sp - 152#64) ↦₃₂ w18)
    (sha256LoopMidCells sp w1c w20 w24 w28 w2c w30 w34 w38 w3c w40 w44 v48)
    ((sp - 96#64) ↦₆₄ v10)
    (((sp - 88#64) ↦₃₂ w58) ∗ ((sp - 84#64) ↦₃₂ w5c))
    (sha256CalleeTail sp v12 v13 v14 v15 v16 v17 v18 v19 v20 v21)
  have hl : (((sp - 160#64) ↦₆₄ vEnd) ∗
      sha256LoopMidCells sp w1c w20 w24 w28 w2c w30 w34 w38 w3c w40 w44 v48 ∗
      (((sp - 88#64) ↦₃₂ w58) ∗ ((sp - 84#64) ↦₃₂ w5c))) =
      sha256LoopStack (sp - 176#64) vEnd w1c w20 w24 w28 w2c w30 w34 w38 w3c w40 w44 v48 w58 w5c := by
    rw [sha256LoopStack_sub176]
    unfold sha256LoopMidCells
    simp only [sepConj_assoc]
  have hc : (((sp - 168#64) ↦₆₄ v1) ∗ ((sp - 152#64) ↦₃₂ w18) ∗ ((sp - 96#64) ↦₆₄ v10) ∗
      sha256CalleeTail sp v12 v13 v14 v15 v16 v17 v18 v19 v20 v21) =
      sha256SavedCalleeCells sp v1 v10 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 w18 := by
    unfold sha256SavedCalleeCells sha256CalleeTail
    rfl
  rw [hl, hc] at h
  rw [← h]
  unfold sha256StateCells sha256LoopMidCells sha256CalleeTail
  simp only [sepConj_assoc]

private theorem prologue_to_loop_pre [Compress256Placement]
    (stA blkA : BitVec 64) (bs : List (BitVec 8))
    (w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 32) (sp : BitVec 64)
    (v1 vEnd v3 v4 v5 v6 v7 v8 v48 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 : BitVec 64) :
    (((Compress256Placement.pl.ρ sha2K32Sym) ↦ᵣ sha256KBytes) ∗
     (stA ↦₃₂ w0) ∗ ((stA + 4#64) ↦₃₂ w1) ∗ ((stA + 8#64) ↦₃₂ w2) ∗ ((stA + 12#64) ↦₃₂ w3) ∗
     ((stA + 16#64) ↦₃₂ w4) ∗ ((stA + 20#64) ↦₃₂ w5) ∗ ((stA + 24#64) ↦₃₂ w6) ∗ ((stA + 28#64) ↦₃₂ w7) ∗
     (blkA ↦ᵣ bs) ∗
     stackAt (sp - 168#64) 8 ∗
     ((sp - 168#64) ↦₆₄ v1) ∗ ((sp - 160#64) ↦₆₄ vEnd) ∗ ((sp - 152#64) ↦₆₄ v3) ∗
     ((sp - 144#64) ↦₆₄ v4) ∗ ((sp - 136#64) ↦₆₄ v5) ∗ ((sp - 128#64) ↦₆₄ v6) ∗
     ((sp - 120#64) ↦₆₄ v7) ∗ ((sp - 112#64) ↦₆₄ v8) ∗ ((sp - 104#64) ↦₆₄ v48) ∗
     ((sp - 96#64) ↦₆₄ v10) ∗ ((sp - 88#64) ↦₆₄ v11) ∗ ((sp - 80#64) ↦₆₄ v12) ∗
     ((sp - 72#64) ↦₆₄ v13) ∗ ((sp - 64#64) ↦₆₄ v14) ∗ ((sp - 56#64) ↦₆₄ v15) ∗
     ((sp - 48#64) ↦₆₄ v16) ∗ ((sp - 40#64) ↦₆₄ v17) ∗ ((sp - 32#64) ↦₆₄ v18) ∗
     ((sp - 24#64) ↦₆₄ v19) ∗ ((sp - 16#64) ↦₆₄ v20) ∗ ((sp - 8#64) ↦₆₄ v21)) =
    (sha256LoopStack (sp - 176#64) vEnd
       (v3.extractLsb' 32 32) (v4.extractLsb' 0 32) (v4.extractLsb' 32 32)
       (v5.extractLsb' 0 32) (v5.extractLsb' 32 32) (v6.extractLsb' 0 32) (v6.extractLsb' 32 32)
       (v7.extractLsb' 0 32) (v7.extractLsb' 32 32) (v8.extractLsb' 0 32) (v8.extractLsb' 32 32)
       v48 (v11.extractLsb' 0 32) (v11.extractLsb' 32 32) ∗
     (blkA ↦ᵣ bs) ∗
     sha2K32AllCells (Compress256Placement.pl.ρ "sha2:.rodata.sha2::consts::K32") ∗
     (sha256StateCells stA w0 w1 w2 w3 w4 w5 w6 w7 ∗
      stackAt (sp - 168#64) 8 ∗
      sha256SavedCalleeCells sp v1 v10 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 (v3.extractLsb' 0 32))) := by
  have hk : ((Compress256Placement.pl.ρ sha2K32Sym) ↦ᵣ sha256KBytes) =
      sha2K32AllCells (Compress256Placement.pl.ρ "sha2:.rodata.sha2::consts::K32") := by
    change (Compress256Placement.pl.ρ "sha2:.rodata.sha2::consts::K32" ↦ᵣ sha256KBytes) = _
    rw [pointsToBytesRO_sha256KBytes_eq_chunks]
    rfl
  rw [hk,
      pointsTo64_sub_split32 sp 152#64 148#64 v3,
      pointsTo64_sub_split32 sp 144#64 140#64 v4,
      pointsTo64_sub_split32 sp 136#64 132#64 v5,
      pointsTo64_sub_split32 sp 128#64 124#64 v6,
      pointsTo64_sub_split32 sp 120#64 116#64 v7,
      pointsTo64_sub_split32 sp 112#64 108#64 v8,
      pointsTo64_sub_split32 sp 88#64 84#64 v11]
  simp only [sepConj_assoc]
  exact stack_state_perm stA blkA bs w0 w1 w2 w3 w4 w5 w6 w7 sp v1 vEnd
    (v3.extractLsb' 0 32) (v3.extractLsb' 32 32)
    (v4.extractLsb' 0 32) (v4.extractLsb' 32 32)
    (v5.extractLsb' 0 32) (v5.extractLsb' 32 32)
    (v6.extractLsb' 0 32) (v6.extractLsb' 32 32)
    (v7.extractLsb' 0 32) (v7.extractLsb' 32 32)
    (v8.extractLsb' 0 32) (v8.extractLsb' 32 32)
    v48 v10 (v11.extractLsb' 0 32) (v11.extractLsb' 32 32)
    v12 v13 v14 v15 v16 v17 v18 v19 v20 v21

private theorem loop_post_recombine [Compress256Placement]
    (stA blkA : BitVec 64) (bs : List (BitVec 8))
    (w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 32) (sp : BitVec 64)
    (v1 vEnd : BitVec 64)
    (w18 w1c w20 w24 w28 w2c w30 w34 w38 w3c w40 w44 : BitVec 32)
    (v48 v10 : BitVec 64) (w58 w5c : BitVec 32)
    (v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 : BitVec 64) :
    (sha256LoopStack (sp - 176#64) vEnd w1c w20 w24 w28 w2c w30 w34 w38 w3c w40 w44 v48 w58 w5c ∗
     (blkA ↦ᵣ bs) ∗
     sha2K32AllCells (Compress256Placement.pl.ρ "sha2:.rodata.sha2::consts::K32") ∗
     (sha256StateCells stA w0 w1 w2 w3 w4 w5 w6 w7 ∗
      stackAt (sp - 168#64) 8 ∗
      sha256SavedCalleeCells sp v1 v10 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 w18)) =
    (((Compress256Placement.pl.ρ sha2K32Sym) ↦ᵣ sha256KBytes) ∗
     (stA ↦₃₂ w0) ∗ ((stA + 4#64) ↦₃₂ w1) ∗ ((stA + 8#64) ↦₃₂ w2) ∗ ((stA + 12#64) ↦₃₂ w3) ∗
     ((stA + 16#64) ↦₃₂ w4) ∗ ((stA + 20#64) ↦₃₂ w5) ∗ ((stA + 24#64) ↦₃₂ w6) ∗ ((stA + 28#64) ↦₃₂ w7) ∗
     (blkA ↦ᵣ bs) ∗
     stackAt (sp - 168#64) 8 ∗
     ((sp - 168#64) ↦₆₄ v1) ∗ ((sp - 160#64) ↦₆₄ vEnd) ∗ ((sp - 152#64) ↦₆₄ (w1c ++ w18)) ∗
     ((sp - 144#64) ↦₆₄ (w24 ++ w20)) ∗ ((sp - 136#64) ↦₆₄ (w2c ++ w28)) ∗
     ((sp - 128#64) ↦₆₄ (w34 ++ w30)) ∗ ((sp - 120#64) ↦₆₄ (w3c ++ w38)) ∗
     ((sp - 112#64) ↦₆₄ (w44 ++ w40)) ∗ ((sp - 104#64) ↦₆₄ v48) ∗
     ((sp - 96#64) ↦₆₄ v10) ∗ ((sp - 88#64) ↦₆₄ (w5c ++ w58)) ∗ ((sp - 80#64) ↦₆₄ v12) ∗
     ((sp - 72#64) ↦₆₄ v13) ∗ ((sp - 64#64) ↦₆₄ v14) ∗ ((sp - 56#64) ↦₆₄ v15) ∗
     ((sp - 48#64) ↦₆₄ v16) ∗ ((sp - 40#64) ↦₆₄ v17) ∗ ((sp - 32#64) ↦₆₄ v18) ∗
     ((sp - 24#64) ↦₆₄ v19) ∗ ((sp - 16#64) ↦₆₄ v20) ∗ ((sp - 8#64) ↦₆₄ v21)) := by
  have hk : ((Compress256Placement.pl.ρ sha2K32Sym) ↦ᵣ sha256KBytes) =
      sha2K32AllCells (Compress256Placement.pl.ρ "sha2:.rodata.sha2::consts::K32") := by
    change (Compress256Placement.pl.ρ "sha2:.rodata.sha2::consts::K32" ↦ᵣ sha256KBytes) = _
    rw [pointsToBytesRO_sha256KBytes_eq_chunks]
    rfl
  rw [hk,
      ← pointsTo32_sub_pair sp 152#64 148#64 w18 w1c,
      ← pointsTo32_sub_pair sp 144#64 140#64 w20 w24,
      ← pointsTo32_sub_pair sp 136#64 132#64 w28 w2c,
      ← pointsTo32_sub_pair sp 128#64 124#64 w30 w34,
      ← pointsTo32_sub_pair sp 120#64 116#64 w38 w3c,
      ← pointsTo32_sub_pair sp 112#64 108#64 w40 w44,
      ← pointsTo32_sub_pair sp 88#64 84#64 w58 w5c]
  simp only [sepConj_assoc]
  exact (stack_state_perm stA blkA bs w0 w1 w2 w3 w4 w5 w6 w7 sp v1 vEnd
    w18 w1c w20 w24 w28 w2c w30 w34 w38 w3c w40 w44 v48 v10 w58 w5c
    v12 v13 v14 v15 v16 v17 v18 v19 v20 v21).symm

private theorem epilogue_post_entails [Compress256Placement]
    (s0 sf : State) (stA blkA : BitVec 64) (bs : List (BitVec 8)) (st_out : ShaState)
    (hsp_sf : sf.sp = s0.sp)
    (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 : BitVec 64) :
    (((Compress256Placement.pl.ρ sha2K32Sym) ↦ᵣ sha256KBytes) ∗
     (stA ↦₃₂ st_out.toList.getD 0 0#32) ∗ ((stA + 4#64) ↦₃₂ st_out.toList.getD 1 0#32) ∗
     ((stA + 8#64) ↦₃₂ st_out.toList.getD 2 0#32) ∗ ((stA + 12#64) ↦₃₂ st_out.toList.getD 3 0#32) ∗
     ((stA + 16#64) ↦₃₂ st_out.toList.getD 4 0#32) ∗ ((stA + 20#64) ↦₃₂ st_out.toList.getD 5 0#32) ∗
     ((stA + 24#64) ↦₃₂ st_out.toList.getD 6 0#32) ∗ ((stA + 28#64) ↦₃₂ st_out.toList.getD 7 0#32) ∗
     (blkA ↦ᵣ bs) ∗
     stackAt (s0.sp - 168#64) 8 ∗
     ((s0.sp - 168#64) ↦₆₄ v1) ∗ ((s0.sp - 160#64) ↦₆₄ v2) ∗ ((s0.sp - 152#64) ↦₆₄ v3) ∗
     ((s0.sp - 144#64) ↦₆₄ v4) ∗ ((s0.sp - 136#64) ↦₆₄ v5) ∗ ((s0.sp - 128#64) ↦₆₄ v6) ∗
     ((s0.sp - 120#64) ↦₆₄ v7) ∗ ((s0.sp - 112#64) ↦₆₄ v8) ∗ ((s0.sp - 104#64) ↦₆₄ v9) ∗
     ((s0.sp - 96#64) ↦₆₄ v10) ∗ ((s0.sp - 88#64) ↦₆₄ v11) ∗ ((s0.sp - 80#64) ↦₆₄ v12) ∗
     ((s0.sp - 72#64) ↦₆₄ v13) ∗ ((s0.sp - 64#64) ↦₆₄ v14) ∗ ((s0.sp - 56#64) ↦₆₄ v15) ∗
     ((s0.sp - 48#64) ↦₆₄ v16) ∗ ((s0.sp - 40#64) ↦₆₄ v17) ∗ ((s0.sp - 32#64) ↦₆₄ v18) ∗
     ((s0.sp - 24#64) ↦₆₄ v19) ∗ ((s0.sp - 16#64) ↦₆₄ v20) ∗ ((s0.sp - 8#64) ↦₆₄ v21)) ⊢
    (((Compress256Placement.pl.ρ sha2K32Sym) ↦ᵣ sha256KBytes) ∗
     (stA ↦ₛ shaStateBytes st_out) ∗ (blkA ↦ᵣ bs) ∗ stackFrame sf 176) := by
  have hsf : stackFrame sf 176 = stackFrame s0 176 := by
    simp only [stackFrame, hsp_sf]
  rw [hsf, pointsToBytes_shaStateBytes stA st_out]
  simp only [sepConj_assoc]
  iterate 10 refine sepConj_mono_right ?_
  exact stackFrame176_entails s0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21

/-! ## 4. Raw `RO` `Spec` and `compress256_raw_ro_ok` -/

/-- Raw spatial contract for `sha2::sha256::compress256` (`176`-B stack frame + `.rodata` `K32`,
read-only block input `blkA ↦ᵣ bs`). -/
@[expose] def compress256RawROSpec (k32 : BitVec 64) :
    Spec (BitVec 64 × ShaState × BitVec 64 × List (BitVec 8) × Nat) where
  pre := fun (stA, st, blkA, bs, n) s0 =>
    ⌜s0.readReg64 .x0 = stA ∧ s0.readReg64 .x1 = blkA ∧ (s0.readReg64 .x2).toNat = n ∧
      bs.length = 64 * n ∧ bs.length ≤ 2 ^ 64⌝ ∗
      (k32 ↦ᵣ sha256KBytes) ∗ (stA ↦ₛ shaStateBytes st) ∗ (blkA ↦ᵣ bs) ∗ stackFrame s0 176
  post := fun (stA, st, blkA, bs, _) _s0 sf =>
    (k32 ↦ᵣ sha256KBytes) ∗
      (stA ↦ₛ shaStateBytes ((chunks64 bs).foldl sha256CompressState st)) ∗
      (blkA ↦ᵣ bs) ∗ stackFrame sf 176

theorem compress256_fnAddr (pl : Obj.Placement) :
    compress256Lib.fnAddr pl compress256Sym = pl.base := by
  simp [Obj.PlacedLib.fnAddr, compress256Lib, compress256Block, compress256Sym, Obj.lookup]

private theorem compress256_raw_ro_ok_at [Compress256Placement] :
    subroutine_ok (compress256PC.rebase Compress256Placement.pl.base)
      Compress256Placement.pl.base
      (compress256RawROSpec (Compress256Placement.pl.ρ sha2K32Sym)) := by
  apply subroutine_ok_of_sepWP_init
  rintro ⟨stA, st, blkA, bs, n⟩ R s0 hpc hrun hpre hsp_align
  dsimp only [compress256RawROSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hbs_len, hbs_max⟩, hpre⟩
  refine ⟨_, hpre, ?_⟩
  by_cases hz : s0.readReg64 .x2 = 0#64
  · have hn0 : n = 0 := by rw [← hx2, hz]; rfl
    subst hn0
    have hchunks0 : chunks64 bs = [] := chunks64_of_length_lt (by omega)
    have hb0 : (s0.readReg64 (Reg.gpr 2#5) == 0#64) = true := beq_iff_eq.mpr hz
    wp_sym_steps 2
    refine SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun]) ⟨?_, rfl, ?_⟩
    · intro hmf
      rw [hchunks0, List.foldl_nil]
      exact hmf
    · refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
      simp only [calleeSavedVRegs_setPC]
  · have hn_ne : n ≠ 0 := by
      intro h0
      apply hz
      apply BitVec.eq_of_toNat_eq
      rw [hx2, h0]
      rfl
    have hn_rem : (n - 1) + 1 = n := by omega
    have hbs_rem : bs.length = 64 * ((n - 1) + 1) := by omega
    have hb0 : (s0.readReg64 (Reg.gpr 2#5) == 0#64) = false := beq_false_of_ne hz
    rw [← sepConj_assoc, ← sepConj_assoc]
    apply stackFrame176_elim
    intro v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21
    rw [pointsToBytes_shaStateBytes stA st]
    wp_simp_pre only [sepConj_assoc]
    wp_sym_steps 14
    rw [prologue_to_loop_pre]
    apply SepWP.cut (mid := Compress256Placement.pl.base + 7584#64)
    apply compress256_loop (n - 1) Compress256Placement.pl.base rfl _ blkA st bs
    · rfl
    · simp [wp_norm, hrun]
    · change ((s0.sp - 176#64) &&& 15#64 == 0#64) = true
      exact State.spAligned_sub s0 176#64 hsp_align
    · exact hbs_rem
    · exact hbs_max
    · rw [hn_rem]
      have hx2' : (s0.readReg64 (Reg.gpr 2#5)).toNat = n := hx2
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, hx2']
      omega
    · simp [wp_norm, hx1]
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · intro s' w1c' w20' w24' w28' w2c' w30' w34' w38' w3c' w40' w44' v48' w58' w5c'
        hpc' hrun' hsp_align' hsp' hfp' hvregs' hx2' hx5' hx6' hx7' hx11' hx17' hx3' hx4'
      apply SepWP.done hpc' hrun'
      change SepWP _ _ s'
        (sha256LoopStack (s0.sp - 176#64) _ w1c' w20' w24' w28' w2c' w30' w34' w38' w3c' w40' w44'
           v48' w58' w5c' ∗ _) _
      rw [loop_post_recombine]
      wp_sym_steps 13
      refine SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun'])
        ⟨?_, by simp [wp_norm], ?_⟩
      · intro hmem
        exact Satisfies.of_entails hmem (sepConj_mono_left
          (epilogue_post_entails s0 _ stA blkA bs ((chunks64 bs).foldl sha256CompressState st)
            (by simp [wp_norm])
            _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _))
      · refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
        · change s'.readReg64 Reg.fp = s0.readReg64 Reg.fp
          rw [hfp']
          rfl
        · simp only [calleeSavedVRegs_setPC, calleeSavedVRegs_setMem, calleeSavedVRegs_writeReg64]
          rw [hvregs']
          simp only [calleeSavedVRegs_setPC, calleeSavedVRegs_setMem, calleeSavedVRegs_writeReg64]

/-- `compress256Lib` satisfies `compress256RawROSpec` at every valid `Placeable` placement. -/
theorem compress256_raw_ro_ok (pl : Obj.Placement) (hpl : compress256Lib.Placeable pl) :
    subroutine_ok (compress256Lib.program pl) (compress256Lib.fnAddr pl compress256Sym)
      (compress256RawROSpec (pl.ρ sha2K32Sym)) := by
  let _ : Compress256Placement := ⟨pl, hpl⟩
  have hprog : compress256PC.rebase pl.base = compress256Lib.program pl := rfl
  rw [compress256_fnAddr pl, ← hprog]
  exact compress256_raw_ro_ok_at

end LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256Loop
