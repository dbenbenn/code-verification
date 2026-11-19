/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhHooksCommon
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Ref
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Cells
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Math
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Compress512Code
import LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Compress512Fetch
import LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Compress512Step

/-!
# Multi-block loop, prologue/epilogue, and raw `subroutine_ok` for `sha2::sha512::compress512`

Verifies `_RNvNtCsbvWyylYiyxg_4sha26sha51211compress512` (`0x0000 → 0x25b0`, `9,652` bytes,
`256`-byte stack frame, `.rodata` `K64` at `pl.ρ sha2K64Sym`), exporting:

- `chunks128_of_length_lt`, `chunks128_cons_take_drop` (block-splitting lemmas on `E2E.chunks128`).
- `compress512RawROSpec`, `compress512_fnAddr`, `compress512_raw_ro_ok`, `compress512_raw_ok`.
-/

set_option autoImplicit false
set_option maxRecDepth 300000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Compress512Loop

open Arm64 ProofLib
open CryptoVerification.E2E (Sha512State chunks128 sha512StateBytesLE)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Ref
  (sha512CompressState sha512CompressState_toList)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Cells
  (sha512KBytes pointsToBytesRO_sha512KBytes_eq_chunks
   stackFrame256_elim stackFrame256_entails)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Math
  (chunks128_eq_map_range pointsToBytes_sha512StateBytesLE)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Compress512Code
  (compress512Sym sha2K64Sym compress512Block compress512Lib Compress512Placement compress512PC)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Compress512Step
  (sha512LoopStack sha2K64AllCells compress512_one_block)

arm64_proof_prelude

/-! ## 1. `E2E.chunks128` Block-Splitting Lemmas -/

theorem chunks128_of_length_lt {bs : List (BitVec 8)} (h : bs.length < 128) :
    chunks128 bs = [] := by
  rw [chunks128_eq_map_range, Nat.div_eq_of_lt h, List.range_zero, List.map_nil]

theorem chunks128_cons_take_drop {bs : List (BitVec 8)} (h : 128 ≤ bs.length) :
    chunks128 bs = bs.take 128 :: chunks128 (bs.drop 128) := by
  rw [chunks128_eq_map_range, chunks128_eq_map_range]
  have hdiv : bs.length / 128 = (bs.drop 128).length / 128 + 1 := by
    rw [List.length_drop]
    omega
  rw [hdiv, List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [Nat.mul_zero, List.drop_zero]
  congr 1
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_apply]
  have hmul : 128 * (j + 1) = 128 + 128 * j := by omega
  rw [hmul, ← List.drop_drop]

/-! ## 2. Multi-Block Loop Induction (`compress512_loop`) -/

private theorem pointsToBytesRO_take_drop (ptr : BitVec 64) (n : Nat) (bs : List (BitVec 8))
    (hn : n ≤ bs.length) :
    (ptr ↦ᵣ bs) = (ptr ↦ᵣ bs.take n) ∗ ((ptr + BitVec.ofNat 64 n) ↦ᵣ bs.drop n) := by
  have h := pointsToBytesRO_append ptr (bs.take n) (bs.drop n)
  rw [List.take_append_drop, List.length_take_of_le hn] at h
  exact h

private theorem loop_pre_split_128 (stP kcells R : SepProp) (b_ptr : BitVec 64)
    (bs : List (BitVec 8)) (hle : 128 ≤ bs.length) :
    (stP ∗ (b_ptr ↦ᵣ bs) ∗ kcells ∗ R) =
      (stP ∗ (b_ptr ↦ᵣ bs.take 128) ∗ kcells ∗ (((b_ptr + 128#64) ↦ᵣ bs.drop 128) ∗ R)) := by
  rw [pointsToBytesRO_take_drop b_ptr 128 bs hle]
  simp only [sepConj_assoc]
  rw [sepConj_left_comm ((b_ptr + 128#64) ↦ᵣ bs.drop 128) kcells]

private theorem loop_pre_advance_128 (stP kcells R : SepProp) (b_ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    (stP ∗ (b_ptr ↦ᵣ bs.take 128) ∗ kcells ∗ (((b_ptr + 128#64) ↦ᵣ bs.drop 128) ∗ R)) =
      (stP ∗ ((b_ptr + 128#64) ↦ᵣ bs.drop 128) ∗ kcells ∗ ((b_ptr ↦ᵣ bs.take 128) ∗ R)) := by
  rw [sepConj_left_comm kcells ((b_ptr + 128#64) ↦ᵣ bs.drop 128),
      sepConj_left_comm (b_ptr ↦ᵣ bs.take 128) ((b_ptr + 128#64) ↦ᵣ bs.drop 128),
      sepConj_left_comm (b_ptr ↦ᵣ bs.take 128) kcells]

private theorem add_128_bne_of_le (b_ptr : BitVec 64) (rem : Nat)
    (hlen : 128 * (rem + 1 + 1) ≤ 2 ^ 64) :
    (b_ptr + 128#64 != b_ptr + BitVec.ofNat 64 (128 * (rem + 1 + 1))) = true := by
  rw [bne_iff_ne]
  intro h
  have h2 : (b_ptr + 128#64).toNat = (b_ptr + BitVec.ofNat 64 (128 * (rem + 1 + 1))).toNat :=
    congrArg BitVec.toNat h
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h2
  omega

private theorem compress512_loop [Compress512Placement] (rem : Nat)
    (b : BitVec 64) (hb : b = Compress512Placement.pl.base)
    (s : State) (b_ptr : BitVec 64) (st : Sha512State) (bs : List (BitVec 8))
    (vEnd : BitVec 64)
    (v18 v20 v28 v30 v38 v40 v48 v50 v58 v60 v68 v70 v78 v80 v88 v90 v98 va8 : BitVec 64)
    (R : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = b + 0x38#64)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hbs : bs.length = 128 * (rem + 1))
    (hbs_max : bs.length ≤ 2 ^ 64)
    (hvEnd : vEnd = b_ptr + BitVec.ofNat 64 (128 * (rem + 1)))
    (hx1 : s.readReg64 (Reg.gpr 1#5) = b_ptr)
    (hx17 : s.readReg64 (Reg.gpr 17#5) = st.toList.getD 0 0#64)
    (hx18 : s.readReg64 (Reg.gpr 18#5) = st.toList.getD 1 0#64)
    (hx2 : s.readReg64 (Reg.gpr 2#5) = st.toList.getD 2 0#64)
    (hx4 : s.readReg64 (Reg.gpr 4#5) = st.toList.getD 3 0#64)
    (hx10 : s.readReg64 (Reg.gpr 10#5) = st.toList.getD 4 0#64)
    (hx15 : s.readReg64 (Reg.gpr 15#5) = st.toList.getD 5 0#64)
    (hx16 : s.readReg64 (Reg.gpr 16#5) = st.toList.getD 6 0#64)
    (hx3 : s.readReg64 (Reg.gpr 3#5) = st.toList.getD 7 0#64)
    (hpost : ∀ (s' : State)
      (v18' v20' v28' v30' v38' v40' v48' v50' v58' v60' v68' v70' v78' v80' v88' v90' v98' va8' :
        BitVec 64),
      s'.pc = b + 0x2580#64 →
      s'.status = .Running →
      s'.spAligned = true →
      s'.sp = s.sp →
      s'.readReg64 Reg.fp = s.readReg64 Reg.fp →
      calleeSavedVRegs s' = calleeSavedVRegs s →
      s'.readReg64 (Reg.gpr 17#5) =
        ((chunks128 bs).foldl sha512CompressState st).toList.getD 0 0#64 →
      s'.readReg64 (Reg.gpr 18#5) =
        ((chunks128 bs).foldl sha512CompressState st).toList.getD 1 0#64 →
      s'.readReg64 (Reg.gpr 2#5) =
        ((chunks128 bs).foldl sha512CompressState st).toList.getD 2 0#64 →
      s'.readReg64 (Reg.gpr 4#5) =
        ((chunks128 bs).foldl sha512CompressState st).toList.getD 3 0#64 →
      s'.readReg64 (Reg.gpr 10#5) =
        ((chunks128 bs).foldl sha512CompressState st).toList.getD 4 0#64 →
      s'.readReg64 (Reg.gpr 15#5) =
        ((chunks128 bs).foldl sha512CompressState st).toList.getD 5 0#64 →
      s'.readReg64 (Reg.gpr 16#5) =
        ((chunks128 bs).foldl sha512CompressState st).toList.getD 6 0#64 →
      s'.readReg64 (Reg.gpr 3#5) =
        ((chunks128 bs).foldl sha512CompressState st).toList.getD 7 0#64 →
      SepWP (compress512PC.rebase b) (b + 0x2580#64) s'
        (sha512LoopStack s.sp vEnd v18' v20' v28' v30' v38' v40' v48' v50' v58' v60' v68' v70'
           v78' v80' v88' v90' v98' va8' ∗
         (b_ptr ↦ᵣ bs) ∗
         sha2K64AllCells
           (Compress512Placement.pl.ρ "sha2:.rodata..Lanon.ee50d778beb355e4b96e6a1be8d6f35b.0") ∗ R)
        post) :
    SepWP (compress512PC.rebase b) (b + 0x2580#64) s
      (sha512LoopStack s.sp vEnd v18 v20 v28 v30 v38 v40 v48 v50 v58 v60 v68 v70
         v78 v80 v88 v90 v98 va8 ∗
       (b_ptr ↦ᵣ bs) ∗
       sha2K64AllCells
         (Compress512Placement.pl.ρ "sha2:.rodata..Lanon.ee50d778beb355e4b96e6a1be8d6f35b.0") ∗ R)
      post := by
  induction rem generalizing s b_ptr st bs
      v18 v20 v28 v30 v38 v40 v48 v50 v58 v60 v68 v70 v78 v80 v88 v90 v98 va8 R with
  | zero =>
    have hbs128 : bs.length = 128 := by omega
    have hchunks : (chunks128 bs).foldl sha512CompressState st = sha512CompressState st bs := by
      rw [chunks128_cons_take_drop (by omega), List.take_of_length_le (by omega),
          chunks128_of_length_lt (by simp [hbs128]), List.foldl_cons, List.foldl_nil]
    apply compress512_one_block b hb s b_ptr st.toList bs vEnd
      v18 v20 v28 v30 v38 v40 v48 v50 v58 v60 v68 v70 v78 v80 v88 v90 v98 va8 R post
      hpc hrun hsp_align st.2 hbs128 hx1 hx17 hx18 hx2 hx4 hx10 hx15 hx16 hx3
    intro s' v18' v20' v28' v30' v38' v40' v48' v50' v58' v60' v68' v70' v78' v80' v88' v90' v98' va8'
      hpc' hrun' hsp_align' hsp' hfp' hvregs' _hx1' hx17' hx18' hx2' hx4' hx10' hx15' hx16' hx3'
    have hcond : (b_ptr + 128#64 != vEnd) = false := by
      rw [hvEnd]
      change (b_ptr + 128#64 != b_ptr + 128#64) = false
      exact bne_self_eq_false _
    rw [hcond] at hpc'
    simp only [Bool.false_eq_true, ↓reduceIte] at hpc'
    rw [← sha512CompressState_toList, ← hchunks] at hx17' hx18' hx2' hx4' hx10' hx15' hx16' hx3'
    exact hpost s' v18' v20' v28' v30' v38' v40' v48' v50' v58' v60' v68' v70' v78' v80' v88' v90' v98' va8'
      hpc' hrun' hsp_align' hsp' hfp' hvregs' hx17' hx18' hx2' hx4' hx10' hx15' hx16' hx3'
  | succ rem ih =>
    have hle128 : 128 ≤ bs.length := by omega
    have htake : (bs.take 128).length = 128 := by simp [hle128]
    have hdrop : (bs.drop 128).length = 128 * (rem + 1) := by simp [hbs]; omega
    have hdrop_max : (bs.drop 128).length ≤ 2 ^ 64 := by simp; omega
    have hchunks : (chunks128 bs).foldl sha512CompressState st =
        (chunks128 (bs.drop 128)).foldl sha512CompressState (sha512CompressState st (bs.take 128)) := by
      rw [chunks128_cons_take_drop hle128, List.foldl_cons]
    rw [loop_pre_split_128 _ _ _ b_ptr bs hle128]
    apply compress512_one_block b hb s b_ptr st.toList (bs.take 128) vEnd
      v18 v20 v28 v30 v38 v40 v48 v50 v58 v60 v68 v70 v78 v80 v88 v90 v98 va8 _ post
      hpc hrun hsp_align st.2 htake hx1 hx17 hx18 hx2 hx4 hx10 hx15 hx16 hx3
    intro s1 v181 v201 v281 v301 v381 v401 v481 v501 v581 v601 v681 v701 v781 v801 v881 v901 v981 va81
      hpc1 hrun1 hsp_align1 hsp1 hfp1 hvregs1 hx1_1 hx17_1 hx18_1 hx2_1 hx4_1 hx10_1 hx15_1 hx16_1 hx3_1
    have hcond : (b_ptr + 128#64 != vEnd) = true := by
      rw [hvEnd]
      exact add_128_bne_of_le b_ptr rem (by omega)
    simp only [hcond, ↓reduceIte] at hpc1
    rw [loop_pre_advance_128]
    have hvEnd' : vEnd = (b_ptr + 128#64) + BitVec.ofNat 64 (128 * (rem + 1)) := by
      rw [hvEnd, BitVec.add_assoc]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    rw [← hsp1]
    rw [← sha512CompressState_toList] at hx17_1 hx18_1 hx2_1 hx4_1 hx10_1 hx15_1 hx16_1 hx3_1
    apply ih s1 (b_ptr + 128#64) (sha512CompressState st (bs.take 128)) (bs.drop 128)
      v181 v201 v281 v301 v381 v401 v481 v501 v581 v601 v681 v701 v781 v801 v881 v901 v981 va81
      ((b_ptr ↦ᵣ bs.take 128) ∗ R)
      hpc1 hrun1 hsp_align1 hdrop hdrop_max hvEnd'
      hx1_1 hx17_1 hx18_1 hx2_1 hx4_1 hx10_1 hx15_1 hx16_1 hx3_1
    intro s2 v182 v202 v282 v302 v382 v402 v482 v502 v582 v602 v682 v702 v782 v802 v882 v902 v982 va82
      hpc2 hrun2 hsp_align2 hsp2 hfp2 hvregs2 hx17_2 hx18_2 hx2_2 hx4_2 hx10_2 hx15_2 hx16_2 hx3_2
    rw [hsp1, ← loop_pre_advance_128, ← loop_pre_split_128 _ _ _ b_ptr bs hle128]
    rw [← hchunks] at hx17_2 hx18_2 hx2_2 hx4_2 hx10_2 hx15_2 hx16_2 hx3_2
    exact hpost s2 v182 v202 v282 v302 v382 v402 v482 v502 v582 v602 v682 v702 v782 v802 v882 v902 v982 va82
      hpc2 hrun2 hsp_align2 (hsp2.trans hsp1) (hfp2.trans hfp1) (hvregs2.trans hvregs1)
      hx17_2 hx18_2 hx2_2 hx4_2 hx10_2 hx15_2 hx16_2 hx3_2

/-! ## 3. Prologue / Epilogue Stack & State Rearrangement -/

private def sha512StateCells (a : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64) : SepProp :=
  (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
  ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7)

private def sha512SavedCalleeCells (sp : BitVec 64)
    (v1 v20 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 : BitVec 64) : SepProp :=
  ((sp - 248#64) ↦₆₄ v1) ∗ ((sp - 96#64) ↦₆₄ v20) ∗
  ((sp - 80#64) ↦₆₄ v22) ∗ ((sp - 72#64) ↦₆₄ v23) ∗ ((sp - 64#64) ↦₆₄ v24) ∗
  ((sp - 56#64) ↦₆₄ v25) ∗ ((sp - 48#64) ↦₆₄ v26) ∗ ((sp - 40#64) ↦₆₄ v27) ∗
  ((sp - 32#64) ↦₆₄ v28) ∗ ((sp - 24#64) ↦₆₄ v29) ∗ ((sp - 16#64) ↦₆₄ v30) ∗
  ((sp - 8#64) ↦₆₄ v31)

private theorem sha512LoopStack_sub256 (sp : BitVec 64) (vEnd : BitVec 64)
    (v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v21 : BitVec 64) :
    sha512LoopStack (sp - 256#64) vEnd v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v21 =
      (((sp - 240#64) ↦₆₄ vEnd) ∗
       ((sp - 232#64) ↦₆₄ v3) ∗ ((sp - 224#64) ↦₆₄ v4) ∗ ((sp - 216#64) ↦₆₄ v5) ∗
       ((sp - 208#64) ↦₆₄ v6) ∗ ((sp - 200#64) ↦₆₄ v7) ∗ ((sp - 192#64) ↦₆₄ v8) ∗
       ((sp - 184#64) ↦₆₄ v9) ∗ ((sp - 176#64) ↦₆₄ v10) ∗ ((sp - 168#64) ↦₆₄ v11) ∗
       ((sp - 160#64) ↦₆₄ v12) ∗ ((sp - 152#64) ↦₆₄ v13) ∗ ((sp - 144#64) ↦₆₄ v14) ∗
       ((sp - 136#64) ↦₆₄ v15) ∗ ((sp - 128#64) ↦₆₄ v16) ∗ ((sp - 120#64) ↦₆₄ v17) ∗
       ((sp - 112#64) ↦₆₄ v18) ∗ ((sp - 104#64) ↦₆₄ v19) ∗
       ((sp - 88#64) ↦₆₄ v21)) := by
  have hsub (b : BitVec 64) : sp - 256#64 + b = sp - (256#64 - b) := by bv_lin
  unfold sha512LoopStack
  simp only [hsub]
  rfl

private def sha512LoopFrontCells (sp : BitVec 64) (vEnd : BitVec 64)
    (v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 : BitVec 64) : SepProp :=
  ((sp - 240#64) ↦₆₄ vEnd) ∗
  ((sp - 232#64) ↦₆₄ v3) ∗ ((sp - 224#64) ↦₆₄ v4) ∗ ((sp - 216#64) ↦₆₄ v5) ∗
  ((sp - 208#64) ↦₆₄ v6) ∗ ((sp - 200#64) ↦₆₄ v7) ∗ ((sp - 192#64) ↦₆₄ v8) ∗
  ((sp - 184#64) ↦₆₄ v9) ∗ ((sp - 176#64) ↦₆₄ v10) ∗ ((sp - 168#64) ↦₆₄ v11) ∗
  ((sp - 160#64) ↦₆₄ v12) ∗ ((sp - 152#64) ↦₆₄ v13) ∗ ((sp - 144#64) ↦₆₄ v14) ∗
  ((sp - 136#64) ↦₆₄ v15) ∗ ((sp - 128#64) ↦₆₄ v16) ∗ ((sp - 120#64) ↦₆₄ v17) ∗
  ((sp - 112#64) ↦₆₄ v18) ∗ ((sp - 104#64) ↦₆₄ v19)

private def sha512CalleeTail (sp : BitVec 64)
    (v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 : BitVec 64) : SepProp :=
  ((sp - 80#64) ↦₆₄ v22) ∗ ((sp - 72#64) ↦₆₄ v23) ∗ ((sp - 64#64) ↦₆₄ v24) ∗
  ((sp - 56#64) ↦₆₄ v25) ∗ ((sp - 48#64) ↦₆₄ v26) ∗ ((sp - 40#64) ↦₆₄ v27) ∗
  ((sp - 32#64) ↦₆₄ v28) ∗ ((sp - 24#64) ↦₆₄ v29) ∗ ((sp - 16#64) ↦₆₄ v30) ∗
  ((sp - 8#64) ↦₆₄ v31)

private theorem perm9 (K ST BLK SA V1 L1 V20 L2 CALLEE : SepProp) :
    (K ∗ ST ∗ BLK ∗ SA ∗ V1 ∗ L1 ∗ V20 ∗ L2 ∗ CALLEE) =
    ((L1 ∗ L2) ∗ BLK ∗ K ∗ (ST ∗ SA ∗ (V1 ∗ V20 ∗ CALLEE))) := by
  simp only [sepConj_assoc]
  rw [sepConj_left_comm ST BLK, sepConj_left_comm K BLK,
      sepConj_left_comm V1 L1, sepConj_left_comm SA L1, sepConj_left_comm ST L1,
      sepConj_left_comm K L1, sepConj_left_comm BLK L1,
      sepConj_left_comm V20 L2, sepConj_left_comm V1 L2, sepConj_left_comm SA L2,
      sepConj_left_comm ST L2, sepConj_left_comm K L2, sepConj_left_comm BLK L2]

private theorem prologue_to_loop_pre [Compress512Placement]
    (stA blkA : BitVec 64) (bs : List (BitVec 8))
    (w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64) (sp : BitVec 64)
    (v1 vEnd v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19
     v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 : BitVec 64) :
    (((Compress512Placement.pl.ρ sha2K64Sym) ↦ᵣ sha512KBytes) ∗
     (stA ↦₆₄ w0) ∗ ((stA + 8#64) ↦₆₄ w1) ∗ ((stA + 16#64) ↦₆₄ w2) ∗ ((stA + 24#64) ↦₆₄ w3) ∗
     ((stA + 32#64) ↦₆₄ w4) ∗ ((stA + 40#64) ↦₆₄ w5) ∗ ((stA + 48#64) ↦₆₄ w6) ∗ ((stA + 56#64) ↦₆₄ w7) ∗
     (blkA ↦ᵣ bs) ∗
     stackAt (sp - 248#64) 8 ∗
     ((sp - 248#64) ↦₆₄ v1) ∗ ((sp - 240#64) ↦₆₄ vEnd) ∗ ((sp - 232#64) ↦₆₄ v3) ∗
     ((sp - 224#64) ↦₆₄ v4) ∗ ((sp - 216#64) ↦₆₄ v5) ∗ ((sp - 208#64) ↦₆₄ v6) ∗
     ((sp - 200#64) ↦₆₄ v7) ∗ ((sp - 192#64) ↦₆₄ v8) ∗ ((sp - 184#64) ↦₆₄ v9) ∗
     ((sp - 176#64) ↦₆₄ v10) ∗ ((sp - 168#64) ↦₆₄ v11) ∗ ((sp - 160#64) ↦₆₄ v12) ∗
     ((sp - 152#64) ↦₆₄ v13) ∗ ((sp - 144#64) ↦₆₄ v14) ∗ ((sp - 136#64) ↦₆₄ v15) ∗
     ((sp - 128#64) ↦₆₄ v16) ∗ ((sp - 120#64) ↦₆₄ v17) ∗ ((sp - 112#64) ↦₆₄ v18) ∗
     ((sp - 104#64) ↦₆₄ v19) ∗ ((sp - 96#64) ↦₆₄ v20) ∗ ((sp - 88#64) ↦₆₄ v21) ∗
     ((sp - 80#64) ↦₆₄ v22) ∗ ((sp - 72#64) ↦₆₄ v23) ∗ ((sp - 64#64) ↦₆₄ v24) ∗
     ((sp - 56#64) ↦₆₄ v25) ∗ ((sp - 48#64) ↦₆₄ v26) ∗ ((sp - 40#64) ↦₆₄ v27) ∗
     ((sp - 32#64) ↦₆₄ v28) ∗ ((sp - 24#64) ↦₆₄ v29) ∗ ((sp - 16#64) ↦₆₄ v30) ∗
     ((sp - 8#64) ↦₆₄ v31)) =
    (sha512LoopStack (sp - 256#64) vEnd v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v21 ∗
     (blkA ↦ᵣ bs) ∗
     sha2K64AllCells
       (Compress512Placement.pl.ρ "sha2:.rodata..Lanon.ee50d778beb355e4b96e6a1be8d6f35b.0") ∗
     (sha512StateCells stA w0 w1 w2 w3 w4 w5 w6 w7 ∗
      stackAt (sp - 248#64) 8 ∗
      sha512SavedCalleeCells sp v1 v20 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31)) := by
  have hk : ((Compress512Placement.pl.ρ sha2K64Sym) ↦ᵣ sha512KBytes) =
      sha2K64AllCells
        (Compress512Placement.pl.ρ "sha2:.rodata..Lanon.ee50d778beb355e4b96e6a1be8d6f35b.0") := by
    change (Compress512Placement.pl.ρ "sha2:.rodata..Lanon.ee50d778beb355e4b96e6a1be8d6f35b.0" ↦ᵣ sha512KBytes) = _
    rw [pointsToBytesRO_sha512KBytes_eq_chunks]
    rfl
  have h := perm9
    (sha2K64AllCells
      (Compress512Placement.pl.ρ "sha2:.rodata..Lanon.ee50d778beb355e4b96e6a1be8d6f35b.0"))
    (sha512StateCells stA w0 w1 w2 w3 w4 w5 w6 w7)
    (blkA ↦ᵣ bs)
    (stackAt (sp - 248#64) 8)
    ((sp - 248#64) ↦₆₄ v1)
    (sha512LoopFrontCells sp vEnd v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19)
    ((sp - 96#64) ↦₆₄ v20)
    ((sp - 88#64) ↦₆₄ v21)
    (sha512CalleeTail sp v22 v23 v24 v25 v26 v27 v28 v29 v30 v31)
  have hl : (sha512LoopFrontCells sp vEnd v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 ∗
      ((sp - 88#64) ↦₆₄ v21)) =
      sha512LoopStack (sp - 256#64) vEnd v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v21 := by
    rw [sha512LoopStack_sub256]
    unfold sha512LoopFrontCells
    simp only [sepConj_assoc]
  have hc : (((sp - 248#64) ↦₆₄ v1) ∗ ((sp - 96#64) ↦₆₄ v20) ∗
      sha512CalleeTail sp v22 v23 v24 v25 v26 v27 v28 v29 v30 v31) =
      sha512SavedCalleeCells sp v1 v20 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 := by
    unfold sha512SavedCalleeCells sha512CalleeTail
    rfl
  rw [hk]
  rw [hl, hc] at h
  rw [← h]
  unfold sha512StateCells sha512LoopFrontCells sha512CalleeTail
  simp only [sepConj_assoc]

private theorem loop_post_recombine [Compress512Placement]
    (stA blkA : BitVec 64) (bs : List (BitVec 8))
    (w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64) (sp : BitVec 64)
    (v1 vEnd v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19
     v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 : BitVec 64) :
    (sha512LoopStack (sp - 256#64) vEnd v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v21 ∗
     (blkA ↦ᵣ bs) ∗
     sha2K64AllCells
       (Compress512Placement.pl.ρ "sha2:.rodata..Lanon.ee50d778beb355e4b96e6a1be8d6f35b.0") ∗
     (sha512StateCells stA w0 w1 w2 w3 w4 w5 w6 w7 ∗
      stackAt (sp - 248#64) 8 ∗
      sha512SavedCalleeCells sp v1 v20 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31)) =
    (((Compress512Placement.pl.ρ sha2K64Sym) ↦ᵣ sha512KBytes) ∗
     (stA ↦₆₄ w0) ∗ ((stA + 8#64) ↦₆₄ w1) ∗ ((stA + 16#64) ↦₆₄ w2) ∗ ((stA + 24#64) ↦₆₄ w3) ∗
     ((stA + 32#64) ↦₆₄ w4) ∗ ((stA + 40#64) ↦₆₄ w5) ∗ ((stA + 48#64) ↦₆₄ w6) ∗ ((stA + 56#64) ↦₆₄ w7) ∗
     (blkA ↦ᵣ bs) ∗
     stackAt (sp - 248#64) 8 ∗
     ((sp - 248#64) ↦₆₄ v1) ∗ ((sp - 240#64) ↦₆₄ vEnd) ∗ ((sp - 232#64) ↦₆₄ v3) ∗
     ((sp - 224#64) ↦₆₄ v4) ∗ ((sp - 216#64) ↦₆₄ v5) ∗ ((sp - 208#64) ↦₆₄ v6) ∗
     ((sp - 200#64) ↦₆₄ v7) ∗ ((sp - 192#64) ↦₆₄ v8) ∗ ((sp - 184#64) ↦₆₄ v9) ∗
     ((sp - 176#64) ↦₆₄ v10) ∗ ((sp - 168#64) ↦₆₄ v11) ∗ ((sp - 160#64) ↦₆₄ v12) ∗
     ((sp - 152#64) ↦₆₄ v13) ∗ ((sp - 144#64) ↦₆₄ v14) ∗ ((sp - 136#64) ↦₆₄ v15) ∗
     ((sp - 128#64) ↦₆₄ v16) ∗ ((sp - 120#64) ↦₆₄ v17) ∗ ((sp - 112#64) ↦₆₄ v18) ∗
     ((sp - 104#64) ↦₆₄ v19) ∗ ((sp - 96#64) ↦₆₄ v20) ∗ ((sp - 88#64) ↦₆₄ v21) ∗
     ((sp - 80#64) ↦₆₄ v22) ∗ ((sp - 72#64) ↦₆₄ v23) ∗ ((sp - 64#64) ↦₆₄ v24) ∗
     ((sp - 56#64) ↦₆₄ v25) ∗ ((sp - 48#64) ↦₆₄ v26) ∗ ((sp - 40#64) ↦₆₄ v27) ∗
     ((sp - 32#64) ↦₆₄ v28) ∗ ((sp - 24#64) ↦₆₄ v29) ∗ ((sp - 16#64) ↦₆₄ v30) ∗
     ((sp - 8#64) ↦₆₄ v31)) :=
  (prologue_to_loop_pre stA blkA bs w0 w1 w2 w3 w4 w5 w6 w7 sp
    v1 vEnd v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19
    v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31).symm

private theorem epilogue_post_entails [Compress512Placement]
    (s0 sf : State) (stA blkA : BitVec 64) (bs : List (BitVec 8)) (st_out : Sha512State)
    (hsp_sf : sf.sp = s0.sp)
    (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
     v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 : BitVec 64) :
    (((Compress512Placement.pl.ρ sha2K64Sym) ↦ᵣ sha512KBytes) ∗
     (stA ↦₆₄ st_out.toList.getD 0 0#64) ∗ ((stA + 8#64) ↦₆₄ st_out.toList.getD 1 0#64) ∗
     ((stA + 16#64) ↦₆₄ st_out.toList.getD 2 0#64) ∗ ((stA + 24#64) ↦₆₄ st_out.toList.getD 3 0#64) ∗
     ((stA + 32#64) ↦₆₄ st_out.toList.getD 4 0#64) ∗ ((stA + 40#64) ↦₆₄ st_out.toList.getD 5 0#64) ∗
     ((stA + 48#64) ↦₆₄ st_out.toList.getD 6 0#64) ∗ ((stA + 56#64) ↦₆₄ st_out.toList.getD 7 0#64) ∗
     (blkA ↦ᵣ bs) ∗
     stackAt (s0.sp - 248#64) 8 ∗
     ((s0.sp - 248#64) ↦₆₄ v1) ∗ ((s0.sp - 240#64) ↦₆₄ v2) ∗ ((s0.sp - 232#64) ↦₆₄ v3) ∗
     ((s0.sp - 224#64) ↦₆₄ v4) ∗ ((s0.sp - 216#64) ↦₆₄ v5) ∗ ((s0.sp - 208#64) ↦₆₄ v6) ∗
     ((s0.sp - 200#64) ↦₆₄ v7) ∗ ((s0.sp - 192#64) ↦₆₄ v8) ∗ ((s0.sp - 184#64) ↦₆₄ v9) ∗
     ((s0.sp - 176#64) ↦₆₄ v10) ∗ ((s0.sp - 168#64) ↦₆₄ v11) ∗ ((s0.sp - 160#64) ↦₆₄ v12) ∗
     ((s0.sp - 152#64) ↦₆₄ v13) ∗ ((s0.sp - 144#64) ↦₆₄ v14) ∗ ((s0.sp - 136#64) ↦₆₄ v15) ∗
     ((s0.sp - 128#64) ↦₆₄ v16) ∗ ((s0.sp - 120#64) ↦₆₄ v17) ∗ ((s0.sp - 112#64) ↦₆₄ v18) ∗
     ((s0.sp - 104#64) ↦₆₄ v19) ∗ ((s0.sp - 96#64) ↦₆₄ v20) ∗ ((s0.sp - 88#64) ↦₆₄ v21) ∗
     ((s0.sp - 80#64) ↦₆₄ v22) ∗ ((s0.sp - 72#64) ↦₆₄ v23) ∗ ((s0.sp - 64#64) ↦₆₄ v24) ∗
     ((s0.sp - 56#64) ↦₆₄ v25) ∗ ((s0.sp - 48#64) ↦₆₄ v26) ∗ ((s0.sp - 40#64) ↦₆₄ v27) ∗
     ((s0.sp - 32#64) ↦₆₄ v28) ∗ ((s0.sp - 24#64) ↦₆₄ v29) ∗ ((s0.sp - 16#64) ↦₆₄ v30) ∗
     ((s0.sp - 8#64) ↦₆₄ v31)) ⊢
    (((Compress512Placement.pl.ρ sha2K64Sym) ↦ᵣ sha512KBytes) ∗
     (stA ↦ₛ sha512StateBytesLE st_out) ∗ (blkA ↦ᵣ bs) ∗ stackFrame sf 256) := by
  have hsf : stackFrame sf 256 = stackFrame s0 256 := by
    simp only [stackFrame, hsp_sf]
  rw [hsf, pointsToBytes_sha512StateBytesLE stA st_out]
  simp only [sepConj_assoc]
  iterate 10 refine sepConj_mono_right ?_
  exact stackFrame256_entails s0
    v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
    v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31

/-! ## 4. Raw `RO` `Spec` and `compress512_raw_ro_ok` -/

/-- Raw spatial contract for `sha2::sha512::compress512` (`256`-B stack frame + `.rodata` `K64`,
read-only block input `blkA ↦ᵣ bs`). -/
@[expose] def compress512RawROSpec (k64 : BitVec 64) :
    Spec (BitVec 64 × Sha512State × BitVec 64 × List (BitVec 8) × Nat) where
  pre := fun (stA, st, blkA, bs, n) s0 =>
    ⌜s0.readReg64 .x0 = stA ∧ s0.readReg64 .x1 = blkA ∧ (s0.readReg64 .x2).toNat = n ∧
      bs.length = 128 * n ∧ bs.length ≤ 2 ^ 64⌝ ∗
      (k64 ↦ᵣ sha512KBytes) ∗ (stA ↦ₛ sha512StateBytesLE st) ∗ (blkA ↦ᵣ bs) ∗ stackFrame s0 256
  post := fun (stA, st, blkA, bs, _) _s0 sf =>
    (k64 ↦ᵣ sha512KBytes) ∗
      (stA ↦ₛ sha512StateBytesLE ((chunks128 bs).foldl sha512CompressState st)) ∗
      (blkA ↦ᵣ bs) ∗ stackFrame sf 256

theorem compress512_fnAddr (pl : Obj.Placement) :
    compress512Lib.fnAddr pl compress512Sym = pl.base := by
  simp [Obj.PlacedLib.fnAddr, compress512Lib, compress512Block, compress512Sym, Obj.lookup]

private theorem compress512_raw_ro_ok_at [Compress512Placement] :
    subroutine_ok (compress512PC.rebase Compress512Placement.pl.base)
      Compress512Placement.pl.base
      (compress512RawROSpec (Compress512Placement.pl.ρ sha2K64Sym)) := by
  apply subroutine_ok_of_sepWP_init
  rintro ⟨stA, st, blkA, bs, n⟩ R s0 hpc hrun hpre hsp_align
  dsimp only [compress512RawROSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hbs_len, hbs_max⟩, hpre⟩
  refine ⟨_, hpre, ?_⟩
  by_cases hz : s0.readReg64 .x2 = 0#64
  · have hn0 : n = 0 := by rw [← hx2, hz]; rfl
    subst hn0
    have hchunks0 : chunks128 bs = [] := chunks128_of_length_lt (by omega)
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
    have hbs_rem : bs.length = 128 * ((n - 1) + 1) := by omega
    have hb0 : (s0.readReg64 (Reg.gpr 2#5) == 0#64) = false := beq_false_of_ne hz
    rw [← sepConj_assoc, ← sepConj_assoc]
    apply stackFrame256_elim
    intro v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16
          v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31
    rw [pointsToBytes_sha512StateBytesLE stA st]
    wp_simp_pre only [sepConj_assoc]
    wp_sym_steps 14
    rw [prologue_to_loop_pre]
    apply SepWP.cut (mid := Compress512Placement.pl.base + 9600#64)
    apply compress512_loop (n - 1) Compress512Placement.pl.base rfl _ blkA st bs
    · rfl
    · simp [wp_norm, hrun]
    · change ((s0.sp - 256#64) &&& 15#64 == 0#64) = true
      exact State.spAligned_sub s0 256#64 hsp_align
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
    · intro s' v18' v20' v28' v30' v38' v40' v48' v50' v58' v60' v68' v70' v78' v80' v88' v90' v98' va8'
        hpc' hrun' hsp_align' hsp' hfp' hvregs' hx17' hx18' hx2' hx4' hx10' hx15' hx16' hx3'
      apply SepWP.done hpc' hrun'
      change SepWP _ _ s'
        (sha512LoopStack (s0.sp - 256#64) _
           v18' v20' v28' v30' v38' v40' v48' v50' v58' v60' v68' v70' v78' v80' v88' v90' v98' va8' ∗ _) _
      rw [loop_post_recombine]
      wp_sym_steps 13
      refine SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun'])
        ⟨?_, by simp [wp_norm], ?_⟩
      · intro hmem
        exact Satisfies.of_entails hmem (sepConj_mono_left
          (epilogue_post_entails s0 _ stA blkA bs ((chunks128 bs).foldl sha512CompressState st)
            (by simp [wp_norm])
            _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _))
      · refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
        · change s'.readReg64 Reg.fp = s0.readReg64 Reg.fp
          rw [hfp']
          rfl
        · simp only [calleeSavedVRegs_setPC, calleeSavedVRegs_setMem, calleeSavedVRegs_writeReg64]
          rw [hvregs']
          simp only [calleeSavedVRegs_setPC, calleeSavedVRegs_setMem, calleeSavedVRegs_writeReg64]

/-- `compress512Lib` satisfies `compress512RawROSpec` at every valid `Placeable` placement. -/
theorem compress512_raw_ro_ok (pl : Obj.Placement) (hpl : compress512Lib.Placeable pl) :
    subroutine_ok (compress512Lib.program pl) (compress512Lib.fnAddr pl compress512Sym)
      (compress512RawROSpec (pl.ρ sha2K64Sym)) := by
  let _ : Compress512Placement := ⟨pl, hpl⟩
  have hprog : compress512PC.rebase pl.base = compress512Lib.program pl := rfl
  rw [compress512_fnAddr pl, ← hprog]
  exact compress512_raw_ro_ok_at

/-- Alias for `compress512_raw_ro_ok` (the raw `PlacedLib` subroutine proof). -/
abbrev compress512_raw_ok := compress512_raw_ro_ok

end LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Compress512Loop
