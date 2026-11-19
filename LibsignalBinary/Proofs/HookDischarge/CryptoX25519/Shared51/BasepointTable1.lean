/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.InternalSpecs -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedObjDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedCodeBase
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.SliceBase
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Field51Base
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Layer0
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `<LookupTable<AffineNielsPoint>>::select` machine-code proof

Verifies `x25519CliMultiLib` block `06`, re-exported by `Shared51.BasepointTable`.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.BasepointTable1

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj ProofLib
open VerifiedLibraries.Common (p25519 fpNeg)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedObjDefs (x25519CliMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedCodeBase (
  X25519CliPlacement x25519CliMpl X25519Base x25519Caller_ok resolve_blk00)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.CommonBase (
  fe51Val fe51ValOfBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.InternalSpecs (
  fe51LimbsBounded readLE_slice_eq fe51LimbsBoundedAt fe51ValAt
  fe51AffineNielsBoundedAt fe51LookupTable8Bounded edTableEntryAt edSelectAffineNiels
  BlackBoxU8Ok LookupTableAffineNielsSelectOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.SliceBase (
  HasLenGe le_length_of_hasLenGe sub_ofNat64_add write64_length_eq
  readLE_write64_self' readLE_write64_ne fold_fe51ValOfBytes
  fe51Reduce_bounded fe51Reduce_val_mod fe51Neg_val_mod
  sepWP_abstract_bytes sepWP_split_stack_callee sepWP_merge_stack_callee)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Field51Base
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Layer0 (black_box_u8_ok)

open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedCodeBase (x25519CliMpl) in
gen_block_fetches x25519Cli 06 x25519CliMultiLib X25519CliPlacement 191 rebase rho sub

@[local simp, local arm64_norm, local wp_norm]
private theorem x25519CliPl06_rho_norm [X25519CliPlacement] (sym : String) :
    x25519CliPl06.ρ sym = x25519CliMultiLib.resolve x25519CliMpl sym := rfl

private theorem sbfx_getLsbD_7 (r : BitVec 64) (x : BitVec 8) (h : BitVec.zeroExtend 8 r = x) :
    (BitVec.zeroExtend 64 (BitVec.truncate 32 r)).getLsbD 7 = x.getLsbD 7 := by subst h; simp

private theorem sxtb_low8 (r : BitVec 64) (x : BitVec 8) (h : BitVec.zeroExtend 8 r = x) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 r) >>> 0 &&& 255#64 = BitVec.zeroExtend 64 x := by
  subst h; ext i hi
  have h255 := (by decide : ∀ k (hk : k < 64), (255#64)[k] = decide (k < 8)) i hi
  by_cases h8 : i < 8
  · simp [h255, h8, show i < 32 by omega]
  · simp [h255, h8]

private theorem sbfx_bit7 (r : BitVec 64) (x : BitVec 8) (h : BitVec.zeroExtend 8 r = x) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 r) >>> 7 &&& 1#64 = BitVec.zeroExtend 64 x >>> 7 &&& 1#64 := by
  subst h; ext i hi
  have h1 := (by decide : ∀ k (hk : k < 64), (1#64)[k] = decide (k = 0)) i hi
  by_cases hi0 : i = 0 <;> simp [h1, hi0]

private theorem and_255_of_zeroExtend8_ite (r : BitVec 64) (c : Bool)
    (h : BitVec.zeroExtend 8 r = if c then 1#8 else 0#8) :
    r &&& 255#64 = if c then 1#64 else 0#64 := by
  have h255 : r &&& 255#64 = BitVec.zeroExtend 64 (BitVec.zeroExtend 8 r) := by
    ext i hi
    have hm := (by decide : ∀ k (hk : k < 64), (255#64)[k] = decide (k < 8)) i hi
    simp [hm, Bool.and_comm]; rfl
  rw [h255, h]; cases c <;> rfl

private theorem neg_ite_one_zero (c : Bool) :
    -(if c then 1#64 else 0#64) = if c then 0xffffffffffffffff#64 else 0#64 := by cases c <;> rfl
private theorem sub_one_ite_one_zero (c : Bool) :
    (if c then 1#64 else 0#64) - 1#64 = if c then 0#64 else 0xffffffffffffffff#64 := by cases c <;> rfl
private def sel64 (c : Bool) (t f : BitVec 64) : BitVec 64 := if c then t else f
private theorem and_allOnes_64 (x : BitVec 64) : x &&& 0xffffffffffffffff#64 = x := by
  ext i hi; simp [(by decide : ∀ k (hk : k < 64), (0xffffffffffffffff#64)[k] = true) i hi]
private theorem sel64_and_allOnes_zero (x : BitVec 64) (c : Bool) :
    x &&& (if c then 0xffffffffffffffff#64 else 0#64) = sel64 c x 0#64 := by cases c <;> simp [sel64, and_allOnes_64]
private theorem and_ite_zero_allOnes (x : BitVec 64) (c : Bool) :
    x &&& (if c then 0#64 else 0xffffffffffffffff#64) = if c then 0#64 else x := by cases c <;> simp [and_allOnes_64]
private theorem sel64_or_left (c : Bool) (x y : BitVec 64) :
    sel64 c x 0#64 ||| (if c then 0#64 else y) = sel64 c x y := by cases c <;> simp [sel64]
private theorem xor_and_sel64_lhs (a b : BitVec 64) (c : Bool) :
    sel64 c (a ^^^ b) 0#64 ^^^ a = sel64 c b a := by cases c <;> simp [sel64]; ext i hi; simp; cases a[i] <;> cases b[i] <;> rfl
private theorem xor_and_sel64_rhs (a b : BitVec 64) (c : Bool) :
    sel64 c (a ^^^ b) 0#64 ^^^ b = sel64 c a b := by cases c <;> simp [sel64]
private theorem eq_of_eq_rhs {α : Type} {lhs rhs1 rhs2 : α} (h1 : lhs = rhs1) (h2 : rhs1 = rhs2) : lhs = rhs2 := h1.trans h2

private theorem ubfx_high32_sign (v : BitVec 64) (x : BitVec 8) :
    BitVec.zeroExtend 8 (BitVec.zeroExtend 64 (BitVec.extractLsb' 32 32
      (v &&& 4294967295#64 ||| BitVec.zeroExtend 64 (BitVec.setWidth 32
        (BitVec.zeroExtend 64 x ||| (if x.getLsbD 7 = true then 0xffffffffffffffff#64 else 0#64) &&&
          0xffffffffffffff00#64)) <<< 32)) >>> 7 &&& 1#64) =
    if x.getLsbD 7 = true then 1#8 else 0#8 := by
  have hex : ∀ (a : BitVec 64) (b : BitVec 32),
      BitVec.extractLsb' 32 32 (a &&& 4294967295#64 ||| BitVec.zeroExtend 64 b <<< 32) = b := by
    intro a b; ext i hi
    have hmask : (4294967295#64)[32 + i]'(by omega) = false := by revert i hi; decide
    simp [hi, show ¬ (32 + i < 32) by omega, show 32 + i < 64 by omega]
    intro _ h; rw [hmask] at h; contradiction
  rw [hex]; revert x; decide

private def HoldEq {α : Type} (a b : α) : Prop := a = b
private theorem hold_reg {lhs rhs : BitVec 64} (h : lhs = rhs) : ∃ v, HoldEq v rhs ∧ lhs = v := ⟨rhs, rfl, h⟩

private theorem hold_stack7 {prog : Program} {target_pc : BitVec 64} {s : State}
    {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 F : SepProp}
    {p104 p112 p120 p128 p136 p144 p152 v104 v112 v120 v128 v136 v144 v152 : BitVec 64}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ u104 u112 u120 u128 u136 u144 u152,
      HoldEq u104 v104 → HoldEq u112 v112 → HoldEq u120 v120 → HoldEq u128 v128 →
      HoldEq u136 v136 → HoldEq u144 v144 → HoldEq u152 v152 →
      SepWP prog target_pc s (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗
        (p104 ↦₆₄ u104) ∗ (p112 ↦₆₄ u112) ∗ (p120 ↦₆₄ u120) ∗ (p128 ↦₆₄ u128) ∗
        (p136 ↦₆₄ u136) ∗ (p144 ↦₆₄ u144) ∗ (p152 ↦₆₄ u152) ∗ F) post oom) :
    SepWP prog target_pc s (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗
      (p104 ↦₆₄ v104) ∗ (p112 ↦₆₄ v112) ∗ (p120 ↦₆₄ v120) ∗ (p128 ↦₆₄ v128) ∗
      (p136 ↦₆₄ v136) ∗ (p144 ↦₆₄ v144) ∗ (p152 ↦₆₄ v152) ∗ F) post oom :=
  h v104 v112 v120 v128 v136 v144 v152 rfl rfl rfl rfl rfl rfl rfl

private theorem getLsbD_7_eq_msb (x : BitVec 8) : x.getLsbD 7 = x.msb := by revert x; decide

private theorem fe51Bounds_hold_chain4 {c4 c3 c2 c1 : Bool} {B : Nat} {u0 u1 u2 u3 u4
    a4_0 a4_1 a4_2 a4_3 a4_4 a3_0 a3_1 a3_2 a3_3 a3_4 a2_0 a2_1 a2_2 a2_3 a2_4 a1_0 a1_1 a1_2 a1_3 a1_4 b0 b1 b2 b3 b4 : BitVec 64}
    (h0 : HoldEq u0 (sel64 c4 a4_0 (sel64 c3 a3_0 (sel64 c2 a2_0 (sel64 c1 a1_0 b0)))))
    (h1 : HoldEq u1 (sel64 c4 a4_1 (sel64 c3 a3_1 (sel64 c2 a2_1 (sel64 c1 a1_1 b1)))))
    (h2 : HoldEq u2 (sel64 c4 a4_2 (sel64 c3 a3_2 (sel64 c2 a2_2 (sel64 c1 a1_2 b2)))))
    (h3 : HoldEq u3 (sel64 c4 a4_3 (sel64 c3 a3_3 (sel64 c2 a2_3 (sel64 c1 a1_3 b3)))))
    (h4 : HoldEq u4 (sel64 c4 a4_4 (sel64 c3 a3_4 (sel64 c2 a2_4 (sel64 c1 a1_4 b4)))))
    (ha4 : a4_0.toNat < B ∧ a4_1.toNat < B ∧ a4_2.toNat < B ∧ a4_3.toNat < B ∧ a4_4.toNat < B)
    (ha3 : a3_0.toNat < B ∧ a3_1.toNat < B ∧ a3_2.toNat < B ∧ a3_3.toNat < B ∧ a3_4.toNat < B)
    (ha2 : a2_0.toNat < B ∧ a2_1.toNat < B ∧ a2_2.toNat < B ∧ a2_3.toNat < B ∧ a2_4.toNat < B)
    (ha1 : a1_0.toNat < B ∧ a1_1.toNat < B ∧ a1_2.toNat < B ∧ a1_3.toNat < B ∧ a1_4.toNat < B)
    (hb : b0.toNat < B ∧ b1.toNat < B ∧ b2.toNat < B ∧ b3.toNat < B ∧ b4.toNat < B) :
    u0.toNat < B ∧ u1.toNat < B ∧ u2.toNat < B ∧ u3.toNat < B ∧ u4.toNat < B := by
  rw [h0, h1, h2, h3, h4]; cases c4 <;> cases c3 <;> cases c2 <;> cases c1 <;> assumption

private theorem fe51Val_hold_chain4 {c4 c3 c2 c1 : Bool} {u0 u1 u2 u3 u4
    a4_0 a4_1 a4_2 a4_3 a4_4 a3_0 a3_1 a3_2 a3_3 a3_4 a2_0 a2_1 a2_2 a2_3 a2_4 a1_0 a1_1 a1_2 a1_3 a1_4 b0 b1 b2 b3 b4 : BitVec 64}
    (h0 : HoldEq u0 (sel64 c4 a4_0 (sel64 c3 a3_0 (sel64 c2 a2_0 (sel64 c1 a1_0 b0)))))
    (h1 : HoldEq u1 (sel64 c4 a4_1 (sel64 c3 a3_1 (sel64 c2 a2_1 (sel64 c1 a1_1 b1)))))
    (h2 : HoldEq u2 (sel64 c4 a4_2 (sel64 c3 a3_2 (sel64 c2 a2_2 (sel64 c1 a1_2 b2)))))
    (h3 : HoldEq u3 (sel64 c4 a4_3 (sel64 c3 a3_3 (sel64 c2 a2_3 (sel64 c1 a1_3 b3)))))
    (h4 : HoldEq u4 (sel64 c4 a4_4 (sel64 c3 a3_4 (sel64 c2 a2_4 (sel64 c1 a1_4 b4))))) :
    fe51Val u0 u1 u2 u3 u4 =
      if c4 then fe51Val a4_0 a4_1 a4_2 a4_3 a4_4 else if c3 then fe51Val a3_0 a3_1 a3_2 a3_3 a3_4
      else if c2 then fe51Val a2_0 a2_1 a2_2 a2_3 a2_4 else if c1 then fe51Val a1_0 a1_1 a1_2 a1_3 a1_4
      else fe51Val b0 b1 b2 b3 b4 := by
  rw [h0, h1, h2, h3, h4]; cases c4 <;> cases c3 <;> cases c2 <;> cases c1 <;> rfl

private theorem writeSelectEpilogue_spec (bs table_bs : List (BitVec 8)) (x : BitVec 8)
    (yp0 yp1 yp2 yp3 yp4 ym0 ym1 ym2 ym3 ym4 d0 d1 d2 d3 d4 : BitVec 64) (hbs : bs.length = 120)
    (hyp_b : yp0.toNat < 2 ^ 53 ∧ yp1.toNat < 2 ^ 53 ∧ yp2.toNat < 2 ^ 53 ∧ yp3.toNat < 2 ^ 53 ∧ yp4.toNat < 2 ^ 53)
    (hym_b : ym0.toNat < 2 ^ 53 ∧ ym1.toNat < 2 ^ 53 ∧ ym2.toNat < 2 ^ 53 ∧ ym3.toNat < 2 ^ 53 ∧ ym4.toNat < 2 ^ 53)
    (hd_b : d0.toNat < 2 ^ 53 ∧ d1.toNat < 2 ^ 53 ∧ d2.toNat < 2 ^ 53 ∧ d3.toNat < 2 ^ 53 ∧ d4.toNat < 2 ^ 53)
    (hyp_v : fe51Val yp0 yp1 yp2 yp3 yp4 =
      if (x == 8#8 || x == -8#8) then fe51ValAt table_bs 840 else if (x == 7#8 || x == -7#8) then fe51ValAt table_bs 720
      else if (x == 6#8 || x == -6#8) then fe51ValAt table_bs 600 else if (x == 5#8 || x == -5#8) then fe51ValAt table_bs 480
      else if (x == 4#8 || x == -4#8) then fe51ValAt table_bs 360 else if (x == 3#8 || x == -3#8) then fe51ValAt table_bs 240
      else if (x == 2#8 || x == -2#8) then fe51ValAt table_bs 120 else if (x == 1#8 || x == -1#8) then fe51ValAt table_bs 0 else 1)
    (hym_v : fe51Val ym0 ym1 ym2 ym3 ym4 =
      if (x == 8#8 || x == -8#8) then fe51ValAt table_bs 880 else if (x == 7#8 || x == -7#8) then fe51ValAt table_bs 760
      else if (x == 6#8 || x == -6#8) then fe51ValAt table_bs 640 else if (x == 5#8 || x == -5#8) then fe51ValAt table_bs 520
      else if (x == 4#8 || x == -4#8) then fe51ValAt table_bs 400 else if (x == 3#8 || x == -3#8) then fe51ValAt table_bs 280
      else if (x == 2#8 || x == -2#8) then fe51ValAt table_bs 160 else if (x == 1#8 || x == -1#8) then fe51ValAt table_bs 40 else 1)
    (hd_v : fe51Val d0 d1 d2 d3 d4 =
      if (x == 8#8 || x == -8#8) then fe51ValAt table_bs 920 else if (x == 7#8 || x == -7#8) then fe51ValAt table_bs 800
      else if (x == 6#8 || x == -6#8) then fe51ValAt table_bs 680 else if (x == 5#8 || x == -5#8) then fe51ValAt table_bs 560
      else if (x == 4#8 || x == -4#8) then fe51ValAt table_bs 440 else if (x == 3#8 || x == -3#8) then fe51ValAt table_bs 320
      else if (x == 2#8 || x == -2#8) then fe51ValAt table_bs 200 else if (x == 1#8 || x == -1#8) then fe51ValAt table_bs 80 else 0) :
    let s := x.getLsbD 7
    let res_bs :=
      ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 bs
        0 (sel64 s ym0 yp0)) 8 (sel64 s ym1 yp1)) 32 (sel64 s ym4 yp4))
        40 (sel64 s yp0 ym0)) 48 (sel64 s yp1 ym1)) 56 (sel64 s yp2 ym2))
        16 (sel64 s ym2 yp2)) 24 (sel64 s ym3 yp3)) 64 (sel64 s yp3 ym3))
        72 (sel64 s yp4 ym4))
        80 (sel64 s ((36028797018963664#64 - d0 &&& 2251799813685247#64) +
          BitVec.zeroExtend 64 (BitVec.truncate 32 ((36028797018963952#64 - d4) >>> 51)) * 19#64) d0))
        88 (sel64 s ((36028797018963952#64 - d1 &&& 2251799813685247#64) + (36028797018963664#64 - d0) >>> 51) d1))
        96 (sel64 s ((36028797018963952#64 - d2 &&& 2251799813685247#64) + (36028797018963952#64 - d1) >>> 51) d2))
        104 (sel64 s ((36028797018963952#64 - d3 &&& 2251799813685247#64) + (36028797018963952#64 - d2) >>> 51) d3))
        112 (sel64 s ((36028797018963952#64 - d4 &&& 2251799813685247#64) + (36028797018963952#64 - d3) >>> 51) d4)
    res_bs.length = 120 ∧ fe51AffineNielsBoundedAt res_bs 0 (2 ^ 53) ∧
      (fe51ValAt res_bs 0 % p25519, fe51ValAt res_bs 40 % p25519, fe51ValAt res_bs 80 % p25519) =
        edSelectAffineNiels table_bs x := by
  intro s res_bs; have : HasLenGe bs 120 := ⟨by omega⟩
  have hlen : res_bs.length = 120 := by dsimp only [res_bs]; simp only [write64_length_eq, hbs]; decide
  have ⟨hr0, hr1, hr2, hr3, hr4⟩ := fe51Reduce_bounded (36028797018963664#64 - d0) (36028797018963952#64 - d1)
    (36028797018963952#64 - d2) (36028797018963952#64 - d3) (36028797018963952#64 - d4)
  have hred_b := And.intro (Nat.lt_trans hr0 (by decide : 2 ^ 52 < 2 ^ 53))
    (And.intro (Nat.lt_trans hr1 (by decide : 2 ^ 52 < 2 ^ 53))
    (And.intro (Nat.lt_trans hr2 (by decide : 2 ^ 52 < 2 ^ 53))
    (And.intro (Nat.lt_trans hr3 (by decide : 2 ^ 52 < 2 ^ 53))
               (Nat.lt_trans hr4 (by decide : 2 ^ 52 < 2 ^ 53)))))
  have hbnd : fe51AffineNielsBoundedAt res_bs 0 (2 ^ 53) := by
    dsimp only [res_bs, fe51AffineNielsBoundedAt, fe51LimbsBoundedAt]
    simp (disch := decide) only [↓readLE_write64_self', ↓readLE_write64_ne]
    cases s <;> simp only [sel64, ↓ite_true, Bool.false_eq_true, ↓ite_false]
    · exact ⟨hyp_b, hym_b, hd_b⟩
    · exact ⟨hym_b, hyp_b, hred_b⟩
  have hval : (fe51ValAt res_bs 0 % p25519, fe51ValAt res_bs 40 % p25519, fe51ValAt res_bs 80 % p25519) =
      if x.msb then (fe51Val ym0 ym1 ym2 ym3 ym4 % p25519, fe51Val yp0 yp1 yp2 yp3 yp4 % p25519, fpNeg (fe51Val d0 d1 d2 d3 d4 % p25519))
      else (fe51Val yp0 yp1 yp2 yp3 yp4 % p25519, fe51Val ym0 ym1 ym2 ym3 ym4 % p25519, fe51Val d0 d1 d2 d3 d4 % p25519) := by
    dsimp only [res_bs, s, fe51ValAt]; simp (disch := decide) only [↓readLE_write64_self', ↓readLE_write64_ne]
    rw [getLsbD_7_eq_msb x]; cases x.msb <;> simp only [sel64, ↓ite_true, Bool.false_eq_true, ↓ite_false]
    rw [fe51Reduce_val_mod, fe51Neg_val_mod d0 d1 d2 d3 d4 ⟨by omega, by omega, by omega, by omega, by omega⟩]
  have hsel : (fe51Val yp0 yp1 yp2 yp3 yp4 % p25519, fe51Val ym0 ym1 ym2 ym3 ym4 % p25519, fe51Val d0 d1 d2 d3 d4 % p25519) =
      if x == 8#8 || x == -8#8 then edTableEntryAt table_bs 7 else if x == 7#8 || x == -7#8 then edTableEntryAt table_bs 6
      else if x == 6#8 || x == -6#8 then edTableEntryAt table_bs 5 else if x == 5#8 || x == -5#8 then edTableEntryAt table_bs 4
      else if x == 4#8 || x == -4#8 then edTableEntryAt table_bs 3 else if x == 3#8 || x == -3#8 then edTableEntryAt table_bs 2
      else if x == 2#8 || x == -2#8 then edTableEntryAt table_bs 1 else if x == 1#8 || x == -1#8 then edTableEntryAt table_bs 0
      else (1, 1, 0) := by
    rw [hyp_v, hym_v, hd_v]
    cases (x == 8#8 || x == -8#8) <;> simp only [Bool.false_eq_true, ↓ite_false, ↓ite_true] <;> try rfl
    cases (x == 7#8 || x == -7#8) <;> simp only [Bool.false_eq_true, ↓ite_false, ↓ite_true] <;> try rfl
    cases (x == 6#8 || x == -6#8) <;> simp only [Bool.false_eq_true, ↓ite_false, ↓ite_true] <;> try rfl
    cases (x == 5#8 || x == -5#8) <;> simp only [Bool.false_eq_true, ↓ite_false, ↓ite_true] <;> try rfl
    cases (x == 4#8 || x == -4#8) <;> simp only [Bool.false_eq_true, ↓ite_false, ↓ite_true] <;> try rfl
    cases (x == 3#8 || x == -3#8) <;> simp only [Bool.false_eq_true, ↓ite_false, ↓ite_true] <;> try rfl
    cases (x == 2#8 || x == -2#8) <;> simp only [Bool.false_eq_true, ↓ite_false, ↓ite_true] <;> try rfl
    cases (x == 1#8 || x == -1#8) <;> simp only [Bool.false_eq_true, ↓ite_false, ↓ite_true] <;> rfl
  refine ⟨hlen, hbnd, ?_⟩; rw [hval]; unfold edSelectAffineNiels; rw [← hsel]

private theorem sepWP_head_region_sub (sp : BitVec 64) (off off' n m : Nat) {v : BitVec 64}
    {prog : Program} {tpc : BitVec 64} {s : State} {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hP : P = (((sp - BitVec.ofNat 64 off) ↦₆₄ v) ∗ memRegion (sp - BitVec.ofNat 64 off') m) ∗ F := by sep_frame)
    (hoff : off = off' + 8 := by decide) (hnm : n = 8 + m := by decide) (hb : n ≤ 2 ^ 64 := by decide)
    (h : SepWP prog tpc s (memRegion (sp - BitVec.ofNat 64 off) n ∗ F) post oom) :
    SepWP prog tpc s P post oom := by
  have ha : sp - BitVec.ofNat 64 off + 8#64 = sp - BitVec.ofNat 64 off' := by
    rw [sub_ofNat64_add sp off 8 (by omega), show off - 8 = off' by omega]
  rw [← ha] at hP; exact SepWP.head_region (sp - BitVec.ofNat 64 off) n m hnm hb hP h

local syntax "close_cells_sub " term:max num num num : tactic
macro_rules
  | `(tactic| close_cells_sub $sp $off $n $k) => do
    let (off, n, k) := (off.getNat, n.getNat, k.getNat)
    if k == 0 then `(tactic| skip) else
    if n == 8 then
      let offLit := Lean.Syntax.mkNumLit (toString off)
      `(tactic| apply SepWP.last_region ($sp - BitVec.ofNat 64 $offLit))
    else
      let (offLit, off'Lit, nLit, n'Lit, k'Lit) := (Lean.Syntax.mkNumLit (toString off), Lean.Syntax.mkNumLit (toString (off - 8)),
        Lean.Syntax.mkNumLit (toString n), Lean.Syntax.mkNumLit (toString (n - 8)), Lean.Syntax.mkNumLit (toString (k - 1)))
      `(tactic| (close_cells_sub $sp $off'Lit $n'Lit $k'Lit; apply sepWP_head_region_sub $sp $offLit $off'Lit $nLit $n'Lit))

set_option maxHeartbeats 800000 in
attribute [local wp_norm] ByteSlice.pack64_eq_readLE_8 in
private theorem lookup_table_affine_niels_select_tail [X25519CliPlacement]
    (hBlackBox : BlackBoxU8Ok)
    (b : BitVec 64) (_hb : X25519Base x25519CliPl06 b) (hbase : x25519CliPl06.base = b)
    (R : SepProp) (s0 sf : State) (a_1 a v_sp176_lo : BitVec 64)
    (a_2 : BitVec 8) (a_3 a_rest_1 : List (BitVec 8))
    (d2_4 d1_4 yp0_4 ym1_4 ym0_4 d0_4 d4_4 d3_4 ym4_4 ym3_4 yp3_4 yp4_4 ym2_4 yp1_4 yp2_4 : BitVec 64)
    {oom : State → SepProp}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (h_4 : a_3.length = 120)
    (h : fe51LookupTable8Bounded a_rest_1 (2 ^ 53))
    (hpc_sf : sf.pc = b + 136#64) (hrun_sf : sf.status = ExecStatus.Running)
    (hsp_sf : sf.sp = s0.sp - 176#64)
    (h_5 : sf.readReg64 (Reg.gpr 19#5) = d2_4) (h_6 : sf.readReg64 (Reg.gpr 20#5) = d1_4)
    (h_7 : sf.readReg64 (Reg.gpr 21#5) = yp0_4) (h_8 : sf.readReg64 (Reg.gpr 22#5) = ym1_4)
    (h_9 : sf.readReg64 (Reg.gpr 23#5) = ym0_4) (h_10 : sf.readReg64 (Reg.gpr 24#5) = d0_4)
    (h_11 : sf.readReg64 (Reg.gpr 25#5) = a + 536#64) (h_12 : sf.readReg64 (Reg.gpr 26#5) = 5#64)
    (h_13 : sf.readReg64 (Reg.gpr 27#5) = d4_4) (h_14 : sf.readReg64 (Reg.gpr 28#5) = d3_4)
    (hcs_sf : sf.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs sf = calleeSavedVRegs s0)
    (hcl : x25519CliMultiLib.CodeLoaded x25519CliMpl sf.mem)
    (hpost : BitVec.zeroExtend 8 (sf.readReg64 (Reg.gpr 0#5)) = if (a_2 == 5#8 || a_2 == -5#8) then 1#8 else 0#8)
    (hyp4_b : yp0_4.toNat < 2 ^ 53 ∧ yp1_4.toNat < 2 ^ 53 ∧ yp2_4.toNat < 2 ^ 53 ∧ yp3_4.toNat < 2 ^ 53 ∧ yp4_4.toNat < 2 ^ 53)
    (hym4_b : ym0_4.toNat < 2 ^ 53 ∧ ym1_4.toNat < 2 ^ 53 ∧ ym2_4.toNat < 2 ^ 53 ∧ ym3_4.toNat < 2 ^ 53 ∧ ym4_4.toNat < 2 ^ 53)
    (hd4_b : d0_4.toNat < 2 ^ 53 ∧ d1_4.toNat < 2 ^ 53 ∧ d2_4.toNat < 2 ^ 53 ∧ d3_4.toNat < 2 ^ 53 ∧ d4_4.toNat < 2 ^ 53)
    (hyp4_v : fe51Val yp0_4 yp1_4 yp2_4 yp3_4 yp4_4 =
      if (a_2 == 4#8 || a_2 == -4#8) then fe51ValAt a_rest_1 360 else if (a_2 == 3#8 || a_2 == -3#8) then fe51ValAt a_rest_1 240
      else if (a_2 == 2#8 || a_2 == -2#8) then fe51ValAt a_rest_1 120 else if (a_2 == 1#8 || a_2 == -1#8) then fe51ValAt a_rest_1 0 else 1)
    (hym4_v : fe51Val ym0_4 ym1_4 ym2_4 ym3_4 ym4_4 =
      if (a_2 == 4#8 || a_2 == -4#8) then fe51ValAt a_rest_1 400 else if (a_2 == 3#8 || a_2 == -3#8) then fe51ValAt a_rest_1 280
      else if (a_2 == 2#8 || a_2 == -2#8) then fe51ValAt a_rest_1 160 else if (a_2 == 1#8 || a_2 == -1#8) then fe51ValAt a_rest_1 40 else 1)
    (hd4_v : fe51Val d0_4 d1_4 d2_4 d3_4 d4_4 =
      if (a_2 == 4#8 || a_2 == -4#8) then fe51ValAt a_rest_1 440 else if (a_2 == 3#8 || a_2 == -3#8) then fe51ValAt a_rest_1 320
      else if (a_2 == 2#8 || a_2 == -2#8) then fe51ValAt a_rest_1 200 else if (a_2 == 1#8 || a_2 == -1#8) then fe51ValAt a_rest_1 80 else 0) :
    SepWP (x25519CliPC06.rebase b (fun _ => none)) (s0.readReg64 Reg.lr) sf
      (memRegion (s0.sp - 176#64 - 16#64) 16 ∗
        (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5) ∗ (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
        (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗ (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
        (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗ (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
        (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗ (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗
        (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗ (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
        (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗ (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
        (s0.sp - 104#64) ↦₆₄ ym4_4 ∗ (s0.sp - 112#64) ↦₆₄ ym3_4 ∗ (s0.sp - 120#64) ↦₆₄ yp3_4 ∗ (s0.sp - 128#64) ↦₆₄ yp4_4 ∗
        (s0.sp - 136#64) ↦₆₄ ym2_4 ∗ (s0.sp - 144#64) ↦₆₄ yp1_4 ∗ (s0.sp - 152#64) ↦₆₄ yp2_4 ∗ (s0.sp - 160#64) ↦₆₄
          (BitVec.zeroExtend 64 (BitVec.setWidth 32 (BitVec.zeroExtend 64 a_2 >>> 7 &&& 1#64 |||
              (if a_2.getLsbD 7 = true then 0xffffffffffffffff#64 else 0#64) &&& 0xfffffffffffffffe#64)) <<< 32 |||
            BitVec.zeroExtend 64 (BitVec.setWidth 32 (BitVec.zeroExtend 64 a_2 >>> 7 &&& 1#64 |||
              (if a_2.getLsbD 7 = true then 0xffffffffffffffff#64 else 0#64) &&& 0xfffffffffffffffe#64) +
              BitVec.setWidth 32 (BitVec.zeroExtend 64 a_2 |||
                (if a_2.getLsbD 7 = true then 0xffffffffffffffff#64 else 0#64) &&& 0xffffffffffffff00#64))) ∗
        (s0.sp - 168#64) ↦₆₄ a_1 ∗ (s0.sp - 176#64) ↦₆₄ (v_sp176_lo &&& 4294967295#64 |||
          BitVec.zeroExtend 64 (BitVec.setWidth 32 (BitVec.zeroExtend 64 a_2 |||
            (if a_2.getLsbD 7 = true then 0xffffffffffffffff#64 else 0#64) &&& 0xffffffffffffff00#64)) <<< 32) ∗
        a ↦ᵣ a_rest_1 ∗ a_1 ↦ₛ a_3)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ (a ↦ᵣ a_rest_1 ∗ stackFrame sf 192 ∗
        ∃∗ res_bs, a_1 ↦ₛ res_bs ∗ ⌜res_bs.length = 120 ∧ fe51AffineNielsBoundedAt res_bs 0 (2 ^ 53) ∧
          (fe51ValAt res_bs 0 % p25519, fe51ValAt res_bs 40 % p25519, fe51ValAt res_bs 80 % p25519) =
            edSelectAffineNiels a_rest_1 a_2⌝) ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) oom := by
  have htab_len : a_rest_1.length = 960 := h.1
  have : HasLenGe a_3 120 := ⟨by omega⟩; have : HasLenGe a_rest_1 960 := ⟨by omega⟩
  have hpost_m := and_255_of_zeroExtend8_ite _ _ hpost; clear hpost
  wp_cut_codeLoaded
  wp_steps; simp only [neg_ite_one_zero, sub_one_ite_one_zero, sel64_and_allOnes_zero, and_ite_zero_allOnes, sel64_or_left]
  wp_x25519_call hBlackBox; try clear hpost_m; clean_prev_sf; norm_sf 16
  replace hpost : _ = if (a_2 == 6#8 || a_2 == -6#8) then 1#8 else 0#8 := eq_of_eq_rhs hpost (by generalize a_2 = x; revert x; decide)
  have hpost_m := and_255_of_zeroExtend8_ite _ _ hpost; clear hpost
  wp_cut_codeLoaded
  wp_steps; simp only [neg_ite_one_zero, sub_one_ite_one_zero, sel64_and_allOnes_zero, and_ite_zero_allOnes, sel64_or_left]
  wp_x25519_call hBlackBox; try clear hpost_m; clean_prev_sf; norm_sf 16
  replace hpost : _ = if (a_2 == 7#8 || a_2 == -7#8) then 1#8 else 0#8 := eq_of_eq_rhs hpost (by generalize a_2 = x; revert x; decide)
  have hpost_m := and_255_of_zeroExtend8_ite _ _ hpost; clear hpost
  wp_cut_codeLoaded
  wp_steps; simp only [neg_ite_one_zero, sub_one_ite_one_zero, sel64_and_allOnes_zero, and_ite_zero_allOnes, sel64_or_left]
  wp_x25519_call hBlackBox; try clear hpost_m; clean_prev_sf; norm_sf 16
  replace hpost : _ = if (a_2 == 8#8 || a_2 == -8#8) then 1#8 else 0#8 := eq_of_eq_rhs hpost (by generalize a_2 = x; revert x; decide)
  have hpost_m := and_255_of_zeroExtend8_ite _ _ hpost; clear hpost
  wp_cut_codeLoaded
  wp_steps; simp only [neg_ite_one_zero, sub_one_ite_one_zero, sel64_and_allOnes_zero, and_ite_zero_allOnes, sel64_or_left]
  wp_x25519_call hBlackBox; try clear hpost_m; clean_prev_sf; norm_sf 16
  replace hpost : _ = if a_2.getLsbD 7 then 1#8 else 0#8 := eq_of_eq_rhs hpost (ubfx_high32_sign _ a_2)
  rcases hold_reg h_5 with ⟨d2, hd2, h_5⟩; rcases hold_reg h_6 with ⟨d1, hd1, h_6⟩; rcases hold_reg h_7 with ⟨yp0, hyp0, h_7⟩
  rcases hold_reg h_8 with ⟨ym1, hym1, h_8⟩; rcases hold_reg h_9 with ⟨ym0, hym0, h_9⟩; rcases hold_reg h_10 with ⟨d0, hd0, h_10⟩
  rcases hold_reg h_13 with ⟨d4, hd4, h_13⟩; rcases hold_reg h_14 with ⟨d3, hd3, h_14⟩
  apply hold_stack7; intro ym4 ym3 yp3 yp4 ym2 yp1 yp2 hym4 hym3 hyp3 hyp4 hym2 hyp1 hyp2
  wp_steps; simp only [and_255_of_zeroExtend8_ite _ _ hpost, neg_ite_one_zero, sub_one_ite_one_zero, sel64_and_allOnes_zero, and_ite_zero_allOnes, sel64_or_left, xor_and_sel64_lhs, xor_and_sel64_rhs]; clear hpost
  apply sepWP_abstract_bytes a_1
    (fun res_bs => res_bs.length = 120 ∧ fe51AffineNielsBoundedAt res_bs 0 (2 ^ 53) ∧
      (fe51ValAt res_bs 0 % p25519, fe51ValAt res_bs 40 % p25519, fe51ValAt res_bs 80 % p25519) = edSelectAffineNiels a_rest_1 a_2)
  · rcases h with ⟨_, _, _, _, _, ⟨hb4_0, hb4_40, hb4_80⟩, ⟨hb5_0, hb5_40, hb5_80⟩, ⟨hb6_0, hb6_40, hb6_80⟩, ⟨hb7_0, hb7_40, hb7_80⟩⟩
    exact writeSelectEpilogue_spec a_3 a_rest_1 a_2 yp0 yp1 yp2 yp3 yp4 ym0 ym1 ym2 ym3 ym4 d0 d1 d2 d3 d4 h_4
      (fe51Bounds_hold_chain4 hyp0 hyp1 hyp2 hyp3 hyp4 hb7_0 hb6_0 hb5_0 hb4_0 hyp4_b)
      (fe51Bounds_hold_chain4 hym0 hym1 hym2 hym3 hym4 hb7_40 hb6_40 hb5_40 hb4_40 hym4_b)
      (fe51Bounds_hold_chain4 hd0 hd1 hd2 hd3 hd4 hb7_80 hb6_80 hb5_80 hb4_80 hd4_b)
      (by rw [fe51Val_hold_chain4 hyp0 hyp1 hyp2 hyp3 hyp4, hyp4_v]; rfl)
      (by rw [fe51Val_hold_chain4 hym0 hym1 hym2 hym3 hym4, hym4_v]; rfl)
      (by rw [fe51Val_hold_chain4 hd0 hd1 hd2 hd3 hd4, hd4_v]; rfl)
  intro res_bs ⟨hres_len, ⟨hb0, hb40, hb80⟩, hres_val⟩
  have hres_bnd : fe51AffineNielsBoundedAt res_bs 0 (2 ^ 53) := ⟨hb0, hb40, hb80⟩
  unpack_fe51_at hb0; unpack_fe51_at hb40; unpack_fe51_at hb80
  close_cells_sub s0.sp 176 176 22; apply sepWP_merge_stack_callee 16 176; wp_done


public section

set_option maxHeartbeats 800000 in
attribute [local wp_norm] ByteSlice.pack64_eq_readLE_8 in
/-- Conditional `<LookupTable<AffineNielsPoint>>::select` (`Blk06`, 191 insns) contract. -/
theorem lookup_table_affine_niels_select_ok_of (hBlackBox : BlackBoxU8Ok) : LookupTableAffineNielsSelectOk := by
  intro _
  apply x25519Caller_ok x25519CliPC06 x25519CliPl06
  intro b hb hbase
  wp_init
  have htab_b : fe51LookupTable8Bounded a_rest_1 (2 ^ 53) := by assumption
  have htab_u : a_rest_1.length = 960 ∧
      fe51AffineNielsBoundedAt a_rest_1 0 (2 ^ 53) ∧ fe51AffineNielsBoundedAt a_rest_1 120 (2 ^ 53) ∧
      fe51AffineNielsBoundedAt a_rest_1 240 (2 ^ 53) ∧ fe51AffineNielsBoundedAt a_rest_1 360 (2 ^ 53) ∧
      fe51AffineNielsBoundedAt a_rest_1 480 (2 ^ 53) ∧ fe51AffineNielsBoundedAt a_rest_1 600 (2 ^ 53) ∧
      fe51AffineNielsBoundedAt a_rest_1 720 (2 ^ 53) ∧ fe51AffineNielsBoundedAt a_rest_1 840 (2 ^ 53) := by
    unfold fe51LookupTable8Bounded at htab_b; exact htab_b
  have hout_len : a_3.length = 120 := by assumption
  have hx_reg : BitVec.zeroExtend 8 (s0.readReg64 (Reg.gpr 2#5)) = a_2 := by assumption
  have htab_len : a_rest_1.length = 960 := htab_u.1
  have : HasLenGe a_3 120 := ⟨by omega⟩; have : HasLenGe a_rest_1 960 := ⟨by omega⟩
  apply sepWP_split_stack_callee 16 176; open_cells (s0.sp - 176#64) 176 22
  wp_cut_codeLoaded
  wp_sym_steps 28; wp_conv_pre => rw [sbfx_getLsbD_7 _ _ hx_reg, sxtb_low8 _ _ hx_reg, sbfx_bit7 _ _ hx_reg]
  wp_steps; wp_x25519_call hBlackBox; norm_sf 16
  replace hpost : _ = if (a_2 == 1#8 || a_2 == -1#8) then 1#8 else 0#8 := eq_of_eq_rhs hpost (by generalize a_2 = x; revert x; decide)
  have hpost_m := and_255_of_zeroExtend8_ite _ _ hpost; clear hpost
  wp_cut_codeLoaded
  wp_steps; simp only [neg_ite_one_zero, sub_one_ite_one_zero, sel64_and_allOnes_zero, and_ite_zero_allOnes, sel64_or_left]
  wp_x25519_call hBlackBox; try clear hpost_m; clean_prev_sf; norm_sf 16
  replace hpost : _ = if (a_2 == 2#8 || a_2 == -2#8) then 1#8 else 0#8 := eq_of_eq_rhs hpost (by generalize a_2 = x; revert x; decide)
  have hpost_m := and_255_of_zeroExtend8_ite _ _ hpost; clear hpost
  wp_cut_codeLoaded
  wp_steps; simp only [neg_ite_one_zero, sub_one_ite_one_zero, sel64_and_allOnes_zero, and_ite_zero_allOnes, sel64_or_left]
  wp_x25519_call hBlackBox; try clear hpost_m; clean_prev_sf; norm_sf 16
  replace hpost : _ = if (a_2 == 3#8 || a_2 == -3#8) then 1#8 else 0#8 := eq_of_eq_rhs hpost (by generalize a_2 = x; revert x; decide)
  have hpost_m := and_255_of_zeroExtend8_ite _ _ hpost; clear hpost
  wp_cut_codeLoaded
  wp_steps; simp only [neg_ite_one_zero, sub_one_ite_one_zero, sel64_and_allOnes_zero, and_ite_zero_allOnes, sel64_or_left]
  wp_x25519_call hBlackBox; try clear hpost_m; clean_prev_sf; norm_sf 16
  replace hpost : _ = if (a_2 == 4#8 || a_2 == -4#8) then 1#8 else 0#8 := eq_of_eq_rhs hpost (by generalize a_2 = x; revert x; decide)
  have hpost_m := and_255_of_zeroExtend8_ite _ _ hpost; clear hpost
  wp_cut_codeLoaded
  wp_steps; simp only [neg_ite_one_zero, sub_one_ite_one_zero, sel64_and_allOnes_zero, and_ite_zero_allOnes, sel64_or_left]
  wp_x25519_call hBlackBox; try clear hpost_m; clean_prev_sf; norm_sf 16
  replace hpost : _ = if (a_2 == 5#8 || a_2 == -5#8) then 1#8 else 0#8 := eq_of_eq_rhs hpost (by generalize a_2 = x; revert x; decide)
  rcases hold_reg h_6 with ⟨d2_4, hd2_4, h_6⟩; rcases hold_reg h_7 with ⟨d1_4, hd1_4, h_7⟩; rcases hold_reg h_8 with ⟨yp0_4, hyp0_4, h_8⟩
  rcases hold_reg h_9 with ⟨ym1_4, hym1_4, h_9⟩; rcases hold_reg h_10 with ⟨ym0_4, hym0_4, h_10⟩; rcases hold_reg h_11 with ⟨d0_4, hd0_4, h_11⟩
  rcases hold_reg h_14 with ⟨d4_4, hd4_4, h_14⟩; rcases hold_reg h_15 with ⟨d3_4, hd3_4, h_15⟩
  apply hold_stack7; intro ym4_4 ym3_4 yp3_4 yp4_4 ym2_4 yp1_4 yp2_4 hym4_4 hym3_4 hyp3_4 hyp4_4 hym2_4 hyp1_4 hyp2_4
  exact lookup_table_affine_niels_select_tail hBlackBox b hb hbase R s0 _ a_1 a _ a_2 a_3 a_rest_1
    d2_4 d1_4 yp0_4 ym1_4 ym0_4 d0_4 d4_4 d3_4 ym4_4 ym3_4 yp3_4 yp4_4 ym2_4 yp1_4 yp2_4
    hsp_align hout_len htab_b (by assumption) (by assumption) (by assumption)
    h_6 h_7 h_8 h_9 h_10 h_11 h_12 h_13 h_14 h_15 (by assumption) (by assumption) ‹_› hpost
    (fe51Bounds_hold_chain4 hyp0_4 hyp1_4 hyp2_4 hyp3_4 hyp4_4 htab_u.2.2.2.2.1.1 htab_u.2.2.2.1.1 htab_u.2.2.1.1 htab_u.2.1.1 (by decide))
    (fe51Bounds_hold_chain4 hym0_4 hym1_4 hym2_4 hym3_4 hym4_4 htab_u.2.2.2.2.1.2.1 htab_u.2.2.2.1.2.1 htab_u.2.2.1.2.1 htab_u.2.1.2.1 (by decide))
    (fe51Bounds_hold_chain4 hd0_4 hd1_4 hd2_4 hd3_4 hd4_4 htab_u.2.2.2.2.1.2.2 htab_u.2.2.2.1.2.2 htab_u.2.2.1.2.2 htab_u.2.1.2.2 (by decide))
    (by rw [fe51Val_hold_chain4 hyp0_4 hyp1_4 hyp2_4 hyp3_4 hyp4_4]; rfl)
    (by rw [fe51Val_hold_chain4 hym0_4 hym1_4 hym2_4 hym3_4 hym4_4]; rfl)
    (by rw [fe51Val_hold_chain4 hd0_4 hd1_4 hd2_4 hd3_4 hd4_4]; rfl)


/-- `<LookupTable<AffineNielsPoint>>::select` (`Blk06`, 191 insns). -/
theorem lookup_table_affine_niels_select_ok : LookupTableAffineNielsSelectOk :=
  lookup_table_affine_niels_select_ok_of black_box_u8_ok

end

end LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.BasepointTable1
