/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.InternalSpecs -- proof-setup: allow-public-import
import ProofLib.SepLogic.ByteRegion
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedObjDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedCodeBase
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.RoTables
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.SliceBase
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Field51Base

/-!
# Montgomery Ladder Machine-Code Proofs, Part 1 (`Shared51.MontgomeryLadderCode1`)

Verifies the Curve25519 Kummer-line subroutines in `x25519CliMultiLib`:
1. `<curve25519_dalek::montgomery::ProjectivePoint>::as_affine` (`Blk11`, 130 words, stack `1312`)
2. `curve25519_dalek::montgomery::differential_add_and_double` (`Blk12`, 238 words, stack `1056`)
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.MontgomeryLadderCode1

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj ProofLib
open VerifiedLibraries.Common (p25519 fpAdd fpSub fpMul fpSq fpPow fpInv natToLeBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedObjDefs (
  x25519CliMultiLib x25519CliData01Bytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedCodeBase (
  X25519CliPlacement x25519CliMpl X25519Base x25519Caller_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref (
  MontProjPoint montDiffAddAndDouble)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.CommonBase (
  a24 fe51_mont_a24 fe51MontA24Bytes fe51Val fe51ValOfBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.RoTables (fe51MontA24_val)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.InternalSpecs (
  fe51LimbsBounded fe51LimbsBoundedAt fe51ValAt fpPow_two_eq_fpSq montFe51LimbsBoundedAt montFe51ValAt
  montProjBounded montProjOfBytes fe51MontA24_bounded
  Fe51MulOk Fe51MulRoLeftOk Fe51Pow2kOk Fe51Pow22501Ok
  MontProjectiveAsAffineOk MontDiffAddAndDoubleOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.SliceBase (
  HasLenGe write64_length_eq readLE_write64_self' readLE_write64_ne
  fe51Reduce_bounded fe51Reduce_val_mod bv64_add_bias0_sub
  fe51Sub_val_mod fe51Add_bounded fe51Add_val_mod mul_mod_eq_fpMul
  sepWP_split_stack_callee sepWP_merge_stack_callee
  sepWP_peel_stack_bytes sepWP_unpeel_stack_bytes
  sepWP_callee_grow sepWP_callee_shrink sepWP_abstract_bytes
  fold_fe51ValOfBytes fe51_mul_post_props)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Field51Base (
  packCanonical51Bytes fe51_to_bytes_math
  pointsToBytes_list32 pointsToBytes32_eq_cells8 compress_recip_eq_fpInv
  write64_copy5_eq pointsToBytes40_sub_eq_cells sepWP_split_bytes_append
  sepWP_peel_stack_region sepWP_unpeel_stack_region)

attribute [local irreducible] x25519CliData01Bytes

/-! ## 1. Block Fetch Generation (`Blk11`, `Blk12`) -/

open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedCodeBase (x25519CliMpl) in
gen_block_fetches x25519Cli 11 x25519CliMultiLib X25519CliPlacement 130 rebase rho sub

@[local simp, local arm64_norm, local wp_norm]
private theorem x25519CliPl11_rho_norm [X25519CliPlacement] (sym : String) :
    x25519CliPl11.ρ sym = x25519CliMultiLib.resolve x25519CliMpl sym := rfl

open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedCodeBase (x25519CliMpl) in
gen_block_fetches x25519Cli 12 x25519CliMultiLib X25519CliPlacement 238 rebase rho sub

@[local simp, local arm64_norm, local wp_norm]
private theorem x25519CliPl12_rho_norm [X25519CliPlacement] (sym : String) :
    x25519CliPl12.ρ sym = x25519CliMultiLib.resolve x25519CliMpl sym := rfl

/-! ## 2. Private Field & Separation-Logic Helpers -/

private theorem fpAdd_comm (x y : Nat) : fpAdd x y = fpAdd y x := by
  unfold fpAdd; rw [Nat.add_comm]

private theorem fpMul_comm (x y : Nat) : fpMul x y = fpMul y x := by
  unfold fpMul; rw [Nat.mul_comm]

private theorem fpSq_lt (x : Nat) : fpSq x < p25519 := by
  unfold fpSq fpMul; exact Nat.mod_lt _ (by unfold p25519; omega)

private theorem mont_w2_factor_eq (AA BB E : Nat) (hAA : AA < p25519) (hE : E = fpSub AA BB) :
    fpAdd (fpMul (a24 + 1) E) BB = fpAdd AA (fpMul a24 E) := by
  have hp_pos : 0 < p25519 := by unfold p25519; omega
  have hb_lt : BB % p25519 < p25519 := Nat.mod_lt _ hp_pos
  have hE_lt : E < p25519 := by rw [hE]; unfold fpSub; exact Nat.mod_lt _ hp_pos
  have hcancel : (E + BB % p25519) % p25519 = AA := by
    rw [hE]
    unfold fpSub
    rw [Nat.mod_add_mod, show AA + p25519 - BB % p25519 + BB % p25519 = AA + p25519 * 1 by omega,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hAA]
  have ha24_1 : (a24 + 1) % p25519 = a24 + 1 := by unfold a24 p25519; omega
  have ha24_0 : a24 % p25519 = a24 := by unfold a24 p25519; omega
  calc fpAdd (fpMul (a24 + 1) E) BB
      = (((a24 + 1) % p25519 * (E % p25519)) % p25519 + BB) % p25519 := rfl
    _ = ((a24 + 1) * E + BB) % p25519 := by
          rw [Nat.mod_add_mod, ha24_1, Nat.mod_eq_of_lt hE_lt]
    _ = (a24 * E + (E + BB % p25519)) % p25519 := by
          rw [← Nat.add_mod_mod ((a24 + 1) * E) BB p25519, Nat.succ_mul a24 E, Nat.add_assoc]
    _ = (a24 * E + AA) % p25519 := by
          rw [Nat.add_mod (a24 * E), hcancel, Nat.mod_add_mod]
    _ = (AA + (a24 % p25519 * (E % p25519)) % p25519) % p25519 := by
          rw [ha24_0, Nat.mod_eq_of_lt hE_lt, Nat.add_mod_mod AA (a24 * E) p25519,
              Nat.add_comm (a24 * E) AA]
    _ = fpAdd AA (fpMul a24 E) := rfl

private theorem fe51LimbsBounded_mono {bs : List (BitVec 8)} {b1 b2 : Nat}
    (h : fe51LimbsBounded bs b1) (hb : b1 ≤ b2 := by decide) :
    fe51LimbsBounded bs b2 := by
  obtain ⟨hl, h0, h1, h2, h3, h4⟩ := h
  exact ⟨hl, by omega, by omega, by omega, by omega, by omega⟩

private theorem fe51_sq_post_props (w : List (BitVec 8)) (V : Nat)
    {a : List (BitVec 8)} {va : Nat}
    (hb : fe51LimbsBounded w (2 ^ 52) := by assumption)
    (hv : fe51ValOfBytes w % p25519 = fpPow (fe51ValOfBytes a % p25519) (2 ^ (1#32).toNat) := by assumption)
    (ha : fe51ValOfBytes a % p25519 = va := by assumption)
    (hV : fpSq va = V := by rfl) :
    w.length = 40 ∧ fe51LimbsBounded w (2 ^ 52) ∧ fe51ValOfBytes w % p25519 = V := by
  refine ⟨hb.1, hb, ?_⟩
  rw [hv, ha, show 2 ^ (1#32).toNat = 2 from rfl, fpPow_two_eq_fpSq, hV]

private theorem sepWP_peel_stack_bytes6 (sp : BitVec 64) (o0 o1 o2 o3 o4 o5 o6 : Nat)
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = memRegion (sp - BitVec.ofNat 64 o0) o0 ∗ P := by sep_frame)
    (h1 : o0 = 40 + o1 := by decide) (h2 : o1 = 40 + o2 := by decide)
    (h3 : o2 = 40 + o3 := by decide) (h4 : o3 = 40 + o4 := by decide)
    (h5 : o4 = 40 + o5 := by decide) (h6 : o5 = 40 + o6 := by decide)
    (hb : o0 ≤ 2 ^ 64 := by decide)
    (hnext : ∀ b1 b2 b3 b4 b5 b6 : List (BitVec 8),
      b1.length = 40 → b2.length = 40 → b3.length = 40 →
      b4.length = 40 → b5.length = 40 → b6.length = 40 →
      SepWP prog target_pc s
        ((((sp - BitVec.ofNat 64 o0) ↦ₛ b1) ∗ ((sp - BitVec.ofNat 64 o1) ↦ₛ b2) ∗
          ((sp - BitVec.ofNat 64 o2) ↦ₛ b3) ∗ ((sp - BitVec.ofNat 64 o3) ↦ₛ b4) ∗
          ((sp - BitVec.ofNat 64 o4) ↦ₛ b5) ∗ ((sp - BitVec.ofNat 64 o5) ↦ₛ b6) ∗
          memRegion (sp - BitVec.ofNat 64 o6) o6) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  rw [hf]
  apply sepWP_peel_stack_bytes sp o0 40 o1 (hoff := h1) (hb := hb); intro b1 hl1
  apply sepWP_peel_stack_bytes sp o1 40 o2 (hoff := h2) (hb := by omega); intro b2 hl2
  apply sepWP_peel_stack_bytes sp o2 40 o3 (hoff := h3) (hb := by omega); intro b3 hl3
  apply sepWP_peel_stack_bytes sp o3 40 o4 (hoff := h4) (hb := by omega); intro b4 hl4
  apply sepWP_peel_stack_bytes sp o4 40 o5 (hoff := h5) (hb := by omega); intro b5 hl5
  apply sepWP_peel_stack_bytes sp o5 40 o6 (hoff := h6) (hb := by omega); intro b6 hl6
  refine Eq.mp (congrArg (fun Q => SepWP prog target_pc s Q post oom) ?_)
    (hnext b1 b2 b3 b4 b5 b6 hl1 hl2 hl3 hl4 hl5 hl6)
  sep_ac_rfl

private theorem sepWP_unpeel_stack_bytes6 (sp : BitVec 64) (o0 o1 o2 o3 o4 o5 o6 : Nat)
    {b1 b2 b3 b4 b5 b6 : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full =
      (((sp - BitVec.ofNat 64 o0) ↦ₛ b1) ∗ ((sp - BitVec.ofNat 64 o1) ↦ₛ b2) ∗
       ((sp - BitVec.ofNat 64 o2) ↦ₛ b3) ∗ ((sp - BitVec.ofNat 64 o3) ↦ₛ b4) ∗
       ((sp - BitVec.ofNat 64 o4) ↦ₛ b5) ∗ ((sp - BitVec.ofNat 64 o5) ↦ₛ b6) ∗
       memRegion (sp - BitVec.ofNat 64 o6) o6) ∗ P := by sep_frame)
    (hl1 : b1.length = 40) (hl2 : b2.length = 40) (hl3 : b3.length = 40)
    (hl4 : b4.length = 40) (hl5 : b5.length = 40) (hl6 : b6.length = 40)
    (h1 : o0 = 40 + o1 := by decide) (h2 : o1 = 40 + o2 := by decide)
    (h3 : o2 = 40 + o3 := by decide) (h4 : o3 = 40 + o4 := by decide)
    (h5 : o4 = 40 + o5 := by decide) (h6 : o5 = 40 + o6 := by decide)
    (hb : o0 ≤ 2 ^ 64 := by decide)
    (hnext : SepWP prog target_pc s (memRegion (sp - BitVec.ofNat 64 o0) o0 ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  rw [hf]
  apply sepWP_unpeel_stack_bytes sp o5 40 o6 (hbs := hl6) (hoff := h6) (hb := by omega)
  apply sepWP_unpeel_stack_bytes sp o4 40 o5 (hbs := hl5) (hoff := h5) (hb := by omega)
  apply sepWP_unpeel_stack_bytes sp o3 40 o4 (hbs := hl4) (hoff := h4) (hb := by omega)
  apply sepWP_unpeel_stack_bytes sp o2 40 o3 (hbs := hl3) (hoff := h3) (hb := by omega)
  apply sepWP_unpeel_stack_bytes sp o1 40 o2 (hbs := hl2) (hoff := h2) (hb := by omega)
  apply sepWP_unpeel_stack_bytes sp o0 40 o1 (hbs := hl1) (hoff := h1) (hb := hb)
  exact hnext

private theorem pointsToBytes80_split2 (p : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 80) :
    (p ↦ₛ bs) = ((p ↦ₛ bs.take 40) ∗ ((p + 40#64) ↦ₛ bs.drop 40)) := by
  have h1 : bs = bs.take 40 ++ bs.drop 40 := (List.take_append_drop 40 bs).symm
  have ht : (bs.take 40).length = 40 := by simp [h]
  conv => lhs; rw [h1]
  rw [pointsToBytes_append, ht]

private theorem readLE_take40 (bs : List (BitVec 8)) (off : Nat) (hoff : off + 8 ≤ 40) :
    ByteSlice.readLE (bs.take 40) off 8 = ByteSlice.readLE bs off 8 := by
  apply ByteSlice.readLE_congr; intro i hi
  simp only [List.getD, List.getElem?_take]
  split
  · rfl
  · rename_i hlt; omega

private theorem readLE_drop_eq (bs : List (BitVec 8)) (k off n : Nat) :
    ByteSlice.readLE (bs.drop k) off n = ByteSlice.readLE bs (k + off) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [ByteSlice.readLE_succ, ByteSlice.readLE_succ, ih]
    simp only [List.getD, List.getElem?_drop, show k + off + n = k + (off + n) by omega]

private theorem montProj_take40_props (bs : List (BitVec 8)) (B : Nat) (h : montProjBounded bs B) :
    fe51LimbsBounded (bs.take 40) B ∧ fe51ValOfBytes (bs.take 40) % p25519 = (montProjOfBytes bs).U := by
  obtain ⟨hlen, ⟨h0, h8, h16, h24, h32⟩, _⟩ := h
  unfold fe51LimbsBounded fe51ValOfBytes montProjOfBytes montFe51ValAt
  rw [readLE_take40 bs 0 (by omega), readLE_take40 bs 8 (by omega),
      readLE_take40 bs 16 (by omega), readLE_take40 bs 24 (by omega), readLE_take40 bs 32 (by omega)]
  exact ⟨⟨by simp [hlen], h0, h8, h16, h24, h32⟩, rfl⟩

private theorem montProj_drop40_props (bs : List (BitVec 8)) (B : Nat) (h : montProjBounded bs B) :
    fe51LimbsBounded (bs.drop 40) B ∧ fe51ValOfBytes (bs.drop 40) % p25519 = (montProjOfBytes bs).W := by
  obtain ⟨hlen, _, ⟨h0, h8, h16, h24, h32⟩⟩ := h
  unfold fe51LimbsBounded fe51ValOfBytes montProjOfBytes montFe51ValAt
  rw [readLE_drop_eq bs 40 0 8, readLE_drop_eq bs 40 8 8, readLE_drop_eq bs 40 16 8,
      readLE_drop_eq bs 40 24 8, readLE_drop_eq bs 40 32 8]
  exact ⟨⟨by simp [hlen], h0, h8, h16, h24, h32⟩, rfl⟩

private theorem as_affine_val_eq (bs t19 t3 t2_5 recip u_aff : List (BitVec 8))
    (hU : fe51ValOfBytes (bs.take 40) % p25519 = (montProjOfBytes bs).U)
    (hW : fe51ValOfBytes (bs.drop 40) % p25519 = (montProjOfBytes bs).W)
    (ht19 : fe51ValOfBytes t19 % p25519 = fpPow (fe51ValOfBytes (bs.drop 40) % p25519) (2 ^ 250 - 1))
    (ht3 : fe51ValOfBytes t3 % p25519 = fpPow (fe51ValOfBytes (bs.drop 40) % p25519) 11)
    (ht2_5 : fe51ValOfBytes t2_5 % p25519 = fpPow (fe51ValOfBytes t19 % p25519) (2 ^ (5#32).toNat))
    (hrecip : fe51ValOfBytes recip % p25519 = (fe51ValOfBytes t2_5 * fe51ValOfBytes t3) % p25519)
    (hu_aff : fe51ValOfBytes u_aff % p25519 = (fe51ValOfBytes (bs.take 40) * fe51ValOfBytes recip) % p25519) :
    fe51ValOfBytes u_aff % p25519 = fpMul (montProjOfBytes bs).U (fpInv (montProjOfBytes bs).W) := by
  have hinv : fe51ValOfBytes recip % p25519 = fpInv (montProjOfBytes bs).W := by
    rw [← hW]
    exact compress_recip_eq_fpInv (fe51ValOfBytes (bs.drop 40)) (fe51ValOfBytes t19)
      (fe51ValOfBytes t3) (fe51ValOfBytes t2_5) (fe51ValOfBytes recip)
      ht19 ht3 (by simpa using ht2_5) hrecip
  rw [hu_aff, mul_mod_eq_fpMul, hU, hinv]

private theorem sepWP_move_end (p : BitVec 64) (bs : List (BitVec 8))
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (p ↦ₛ bs) ∗ P := by sep_frame)
    (hnext : SepWP prog target_pc s (P ∗ (p ↦ₛ bs)) post oom) :
    SepWP prog target_pc s Full post oom := by rw [hf, sepConj_comm]; exact hnext

private theorem sepWP_fold_point80 (p : BitVec 64) (bs : List (BitVec 8))
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} (h : bs.length = 80)
    (hf : Full = ((p ↦ₛ bs.take 40) ∗ ((p + 40#64) ↦ₛ bs.drop 40)) ∗ P := by sep_frame)
    (hnext : SepWP prog target_pc s ((p ↦ₛ bs) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by rw [hf, ← pointsToBytes80_split2 p bs h]; exact hnext

/-! ## 3. Private Mid-Segment Helper for `differential_add_and_double` (`Blk12`) -/

set_option maxHeartbeats 800000 in
private theorem diff_add_mid [X25519CliPlacement]
    (hpow2k : Fe51Pow2kOk) (hmul : Fe51MulOk) (hmul_ro_left : Fe51MulRoLeftOk)
    (b sp p_ptr q_ptr u1_ptr : BitVec 64)
    (P0 Q0 : MontProjPoint) (U1 V_AA V_BB : Nat)
    (u1_bs bufA bufB bufC bufD w w_1 sE sDA sCB sSum sDiff sU3 sTmp sA24E sU2 sA24EpBB sW2 sW3 :
      List (BitVec 8))
    {target_pc : BitVec 64} {s0 : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hb : X25519Base x25519CliPl12 b) (hbase : x25519CliPl12.base = b)
    (hpc : s0.pc = b + 384#64)
    (hrun : s0.status = .Running) (hsp : s0.sp = sp - 832#64)
    (h_sp_align : (sp &&& 15#64 == 0#64) = true)
    (hx29 : s0.readReg64 (Reg.gpr 29#5) = sp - 96#64)
    (hx20 : s0.readReg64 (Reg.gpr 20#5) = p_ptr) (hx19 : s0.readReg64 (Reg.gpr 19#5) = q_ptr)
    (hx22 : s0.readReg64 (Reg.gpr 22#5) = 36028797018963952#64)
    (hx24 : s0.readReg64 (Reg.gpr 24#5) = 36028797018963664#64)
    (hx25 : s0.readReg64 (Reg.gpr 25#5) = 19#64)
    (hcl : x25519CliMultiLib.CodeLoaded x25519CliMpl s0.mem)
    (hV_AA_lt : V_AA < p25519)
    (hu1_b : fe51LimbsBounded u1_bs (2 ^ 54)) (hu1_v : fe51ValOfBytes u1_bs % p25519 = U1)
    (hA_b : fe51LimbsBounded bufA (2 ^ 54)) (hA_v : fe51ValOfBytes bufA % p25519 = fpAdd P0.U P0.W)
    (hB_b : fe51LimbsBounded bufB (2 ^ 54)) (hB_v : fe51ValOfBytes bufB % p25519 = fpSub P0.U P0.W)
    (hC_b : fe51LimbsBounded bufC (2 ^ 54)) (hC_v : fe51ValOfBytes bufC % p25519 = fpAdd Q0.U Q0.W)
    (hD_b : fe51LimbsBounded bufD (2 ^ 52)) (hD_v : fe51ValOfBytes bufD % p25519 = fpSub Q0.U Q0.W)
    (hw_b : fe51LimbsBounded w (2 ^ 52)) (hw_v : fe51ValOfBytes w % p25519 = V_AA)
    (hw1_b : fe51LimbsBounded w_1 (2 ^ 52)) (hw1_v : fe51ValOfBytes w_1 % p25519 = V_BB)
    (hsE : sE.length = 40) (hsDA : sDA.length = 40) (hsCB : sCB.length = 40)
    (hsSum : sSum.length = 40) (hsDiff : sDiff.length = 40) (hsU3 : sU3.length = 40)
    (hsTmp : sTmp.length = 40) (hsA24E : sA24E.length = 40) (hsU2 : sU2.length = 40)
    (hsA24EpBB : sA24EpBB.length = 40) (hsW2 : sW2.length = 40) (hsW3 : sW3.length = 40)
    (hf : Full = ((((sp - 832#64) ↦₆₄ u1_ptr) ∗ (u1_ptr ↦ₛ u1_bs) ∗
      ((sp - 824#64) ↦ₛ bufA) ∗ ((sp - 784#64) ↦ₛ bufB) ∗
      ((sp - 744#64) ↦ₛ bufC) ∗ ((sp - 704#64) ↦ₛ bufD) ∗
      ((sp - 664#64) ↦ₛ w) ∗ ((sp - 624#64) ↦ₛ w_1) ∗
      ((sp - 584#64) ↦ₛ sE) ∗ ((sp - 544#64) ↦ₛ sDA) ∗
      ((sp - 504#64) ↦ₛ sCB) ∗ ((sp - 464#64) ↦ₛ sSum) ∗
      ((sp - 424#64) ↦ₛ sDiff) ∗ ((sp - 384#64) ↦ₛ sU3) ∗
      ((sp - 344#64) ↦ₛ sTmp) ∗ ((sp - 304#64) ↦ₛ sA24E) ∗
      ((sp - 264#64) ↦ₛ sU2) ∗ ((sp - 224#64) ↦ₛ sA24EpBB) ∗
      ((sp - 184#64) ↦ₛ sW2) ∗ ((sp - 144#64) ↦ₛ sW3) ∗
      ((fe51_mont_a24 x25519CliMpl) ↦ᵣ fe51MontA24Bytes) ∗
      memRegion (sp - 832#64 - 224#64) 224) ∗ P) := by sep_frame)
    (hnext : ∀ (sf : State)
      (bufE w_2 w_3 bufSum bufDiff w_4 w_5 w_6 w_7 bufA24EpBB w_8 w_9 : List (BitVec 8)),
      sf.pc = b + 828#64 →
      sf.status = .Running → sf.sp = sp - 832#64 →
      sf.readReg64 (Reg.gpr 29#5) = sp - 96#64 →
      sf.readReg64 (Reg.gpr 20#5) = p_ptr → sf.readReg64 (Reg.gpr 19#5) = q_ptr →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      x25519CliMultiLib.CodeLoaded x25519CliMpl sf.mem →
      bufE.length = 40 → w_2.length = 40 → w_3.length = 40 → bufSum.length = 40 →
      bufDiff.length = 40 → w_5.length = 40 → w_6.length = 40 → bufA24EpBB.length = 40 →
      fe51LimbsBounded w_4 (2 ^ 52) →
      fe51ValOfBytes w_4 % p25519 =
        fpSq (fpAdd (fpMul (fpSub Q0.U Q0.W) (fpAdd P0.U P0.W))
                    (fpMul (fpAdd Q0.U Q0.W) (fpSub P0.U P0.W))) →
      fe51LimbsBounded w_7 (2 ^ 52) → fe51ValOfBytes w_7 % p25519 = fpMul V_AA V_BB →
      fe51LimbsBounded w_8 (2 ^ 52) →
      fe51ValOfBytes w_8 % p25519 =
        fpMul (fpSub V_AA V_BB) (fpAdd V_AA (fpMul a24 (fpSub V_AA V_BB))) →
      fe51LimbsBounded w_9 (2 ^ 52) →
      fe51ValOfBytes w_9 % p25519 =
        fpMul U1 (fpSq (fpSub (fpMul (fpSub Q0.U Q0.W) (fpAdd P0.U P0.W))
                              (fpMul (fpAdd Q0.U Q0.W) (fpSub P0.U P0.W)))) →
      SepWP (x25519CliPC12.rebase b (fun _ => none)) target_pc sf
        (((((sp - 832#64) ↦₆₄ u1_ptr) ∗ (u1_ptr ↦ₛ u1_bs) ∗
          ((sp - 824#64) ↦ₛ bufA) ∗ ((sp - 784#64) ↦ₛ bufB) ∗
          ((sp - 744#64) ↦ₛ bufC) ∗ ((sp - 704#64) ↦ₛ bufD) ∗
          ((sp - 664#64) ↦ₛ w) ∗ ((sp - 624#64) ↦ₛ w_1) ∗
          ((sp - 584#64) ↦ₛ bufE) ∗ ((sp - 544#64) ↦ₛ w_2) ∗
          ((sp - 504#64) ↦ₛ w_3) ∗ ((sp - 464#64) ↦ₛ bufSum) ∗
          ((sp - 424#64) ↦ₛ bufDiff) ∗ ((sp - 384#64) ↦ₛ w_4) ∗
          ((sp - 344#64) ↦ₛ w_5) ∗ ((sp - 304#64) ↦ₛ w_6) ∗
          ((sp - 264#64) ↦ₛ w_7) ∗ ((sp - 224#64) ↦ₛ bufA24EpBB) ∗
          ((sp - 184#64) ↦ₛ w_8) ∗ ((sp - 144#64) ↦ₛ w_9) ∗
          ((fe51_mont_a24 x25519CliMpl) ↦ᵣ fe51MontA24Bytes) ∗
          memRegion (sp - 832#64 - 224#64) 224) ∗ P)) post oom) :
    SepWP (x25519CliPC12.rebase b (fun _ => none)) target_pc s0 Full post oom := by
  rw [hf]; clear hf Full
  obtain ⟨hA_l, hA0, hA1, hA2, hA3, hA4⟩ := hA_b
  obtain ⟨hB_l, hB0, hB1, hB2, hB3, hB4⟩ := hB_b
  have hw_l : w.length = 40 := hw_b.1
  have hw1_l : w_1.length = 40 := hw1_b.1
  generalize hV_E : fpSub V_AA V_BB = V_E
  generalize hV_DA : fpMul (fpSub Q0.U Q0.W) (fpAdd P0.U P0.W) = V_DA
  have hsE_ge : HasLenGe sE 40 := ⟨by omega⟩
  wp_cut_codeLoaded
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcl_e
  apply sepWP_abstract_bytes (sp - 584#64)
    (fun buf => fe51LimbsBounded buf (2 ^ 52) ∧ fe51ValOfBytes buf % p25519 = V_E)
  · unfold fe51LimbsBounded fe51ValOfBytes
    simp (disch := decide) only [readLE_write64_self', readLE_write64_ne, write64_length_eq, hsE, Nat.min_eq_left, bv64_add_bias0_sub]
    refine ⟨⟨trivial, fe51Reduce_bounded _ _ _ _ _⟩, ?_⟩
    rw [fe51Reduce_val_mod, fe51Sub_val_mod _ _ _ _ _ _ _ _ _ _ hw_b.2 hw1_b.2,
        fold_fe51ValOfBytes w, fold_fe51ValOfBytes w_1, hw_v, hw1_v, hV_E]
  intro bufE ⟨hE_b, hE_v⟩; clear hsE_ge hsE sE
  obtain ⟨hD_l, hD0, hD1, hD2, hD3, hD4⟩ := fe51LimbsBounded_mono hD_b (b2 := 2 ^ 54); clear hD_b
  wp_x25519_call hmul
  rw [hsp, hx29, hx20, hx19, hx22, hx24, hx25] at *; norm_sf 224
  obtain ⟨hw2_l, hw2_b, hw2_v⟩ := fe51_mul_post_props w_2 V_DA (ha := hA_v) (hbv := hD_v) (hV := (fpMul_comm _ _).trans hV_DA)
  clear hA0 hA1 hA2 hA3 hA4 hA_v hD0 hD1 hD2 hD3 hD4 hD_v hsDA sDA
  obtain ⟨hC_l, hC0, hC1, hC2, hC3, hC4⟩ := hC_b
  generalize hV_CB : fpMul (fpAdd Q0.U Q0.W) (fpSub P0.U P0.W) = V_CB
  wp_cut_codeLoaded
  wp_steps
  wp_x25519_call hmul
  clean_prev_sf; norm_sf 224
  obtain ⟨hw3_l, hw3_b, hw3_v⟩ := fe51_mul_post_props w_3 V_CB (ha := hB_v) (hbv := hC_v) (hV := (fpMul_comm _ _).trans hV_CB)
  clear hB0 hB1 hB2 hB3 hB4 hB_v hC0 hC1 hC2 hC3 hC4 hC_v hsCB sCB
  apply sepWP_callee_shrink (sp - 832#64) 224 96 128
  have hsSum_ge : HasLenGe sSum 40 := ⟨by omega⟩
  have hsDiff_ge : HasLenGe sDiff 40 := ⟨by omega⟩
  wp_cut_codeLoaded
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcl_sumdiff
  apply sepWP_abstract_bytes (sp - 464#64)
    (fun buf => fe51LimbsBounded buf (2 ^ 54) ∧ fe51ValOfBytes buf % p25519 = fpAdd V_DA V_CB)
  · unfold fe51LimbsBounded fe51ValOfBytes
    simp (disch := decide) only [readLE_write64_self', readLE_write64_ne, write64_length_eq, hsSum, Nat.min_eq_left]
    refine ⟨⟨trivial, fe51Add_bounded _ _ _ _ _ _ _ _ _ _ (2 ^ 54) hw3_b.2 hw2_b.2⟩, ?_⟩
    rw [fe51Add_val_mod _ _ _ _ _ _ _ _ _ _ hw3_b.2 hw2_b.2,
        fold_fe51ValOfBytes w_3, fold_fe51ValOfBytes w_2, hw3_v, hw2_v, fpAdd_comm]
  intro bufSum ⟨⟨hSum_l, hSum0, hSum1, hSum2, hSum3, hSum4⟩, hSum_v⟩
  apply sepWP_abstract_bytes (sp - 424#64)
    (fun buf => fe51LimbsBounded buf (2 ^ 52) ∧ fe51ValOfBytes buf % p25519 = fpSub V_DA V_CB)
  · unfold fe51LimbsBounded fe51ValOfBytes
    simp (disch := decide) only [readLE_write64_self', readLE_write64_ne, write64_length_eq, hsDiff, Nat.min_eq_left, bv64_add_bias0_sub]
    refine ⟨⟨trivial, fe51Reduce_bounded _ _ _ _ _⟩, ?_⟩
    rw [fe51Reduce_val_mod, fe51Sub_val_mod _ _ _ _ _ _ _ _ _ _ hw2_b.2 hw3_b.2,
        fold_fe51ValOfBytes w_2, fold_fe51ValOfBytes w_3, hw2_v, hw3_v]
  intro bufDiff ⟨hDiff_b, hDiff_v⟩; clear hsSum_ge hsDiff_ge hsSum hsDiff sSum sDiff
  generalize hV_U3 : fpSq (fpAdd V_DA V_CB) = V_U3
  wp_x25519_call hpow2k
  clean_prev_sf; norm_sf 96
  obtain ⟨hw4_l, hw4_b, hw4_v⟩ := fe51_sq_post_props w_4 V_U3 (ha := hSum_v) (hV := hV_U3)
  clear hw2_b hw2_v hw3_b hw3_v hSum0 hSum1 hSum2 hSum3 hSum4 hSum_v hsU3 sU3
  obtain ⟨hDiff_l, hDiff0, hDiff1, hDiff2, hDiff3, hDiff4⟩ := fe51LimbsBounded_mono hDiff_b (b2 := 2 ^ 54); clear hDiff_b
  generalize hV_Tmp : fpSq (fpSub V_DA V_CB) = V_Tmp
  wp_cut_codeLoaded
  wp_steps
  wp_x25519_call hpow2k
  clean_prev_sf; norm_sf 96
  obtain ⟨hw5_l, hw5_b, hw5_v⟩ := fe51_sq_post_props w_5 V_Tmp (ha := hDiff_v) (hV := hV_Tmp)
  clear hDiff0 hDiff1 hDiff2 hDiff3 hDiff4 hDiff_v hsTmp sTmp
  apply sepWP_callee_grow (sp - 832#64) 224 96 128
  obtain ⟨ha24_len, ha24_0, ha24_1, ha24_2, ha24_3, ha24_4⟩ := fe51MontA24_bounded
  rcases fe51LimbsBounded_mono hE_b (b2 := 2 ^ 54) with ⟨hE_l, hE0, hE1, hE2, hE3, hE4⟩
  generalize hV_A24E : fpMul (a24 + 1) V_E = V_A24E
  wp_cut_codeLoaded
  wp_steps
  wp_x25519_call hmul_ro_left
  clean_prev_sf; norm_sf 224
  wp_pull_exists
  rename_i w_6
  wp_focus_pure
  rintro ⟨hw6_b, hw6_raw⟩
  have hw6_l : w_6.length = 40 := hw6_b.1
  have hw6_v : fe51ValOfBytes w_6 % p25519 = V_A24E := by
    rw [hw6_raw, mul_mod_eq_fpMul, fe51MontA24_val, hE_v,
        show (a24 + 1) % p25519 = a24 + 1 by decide +kernel, hV_A24E]
  clear hw6_raw ha24_len ha24_0 ha24_1 ha24_2 ha24_3 ha24_4 hsA24E sA24E
  obtain ⟨_, hw0_0, hw0_1, hw0_2, hw0_3, hw0_4⟩ := fe51LimbsBounded_mono hw_b (b2 := 2 ^ 54)
  obtain ⟨_, hw1_0, hw1_1, hw1_2, hw1_3, hw1_4⟩ := fe51LimbsBounded_mono hw1_b (b2 := 2 ^ 54)
  generalize hV_U2 : fpMul V_AA V_BB = V_U2
  wp_cut_codeLoaded
  wp_steps
  wp_x25519_call hmul
  clean_prev_sf; norm_sf 224
  obtain ⟨hw7_l, hw7_b, hw7_v⟩ := fe51_mul_post_props w_7 V_U2 (ha := hw_v) (hbv := hw1_v) (hV := hV_U2)
  have hsA24EpBB_ge : HasLenGe sA24EpBB 40 := ⟨by omega⟩
  wp_cut_codeLoaded
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcl_a24epbb
  apply sepWP_abstract_bytes (sp - 224#64)
    (fun buf => fe51LimbsBounded buf (2 ^ 54) ∧ fe51ValOfBytes buf % p25519 = fpAdd V_AA (fpMul a24 V_E))
  · unfold fe51LimbsBounded fe51ValOfBytes
    simp (disch := decide) only [readLE_write64_self', readLE_write64_ne, write64_length_eq, hsA24EpBB, Nat.min_eq_left]
    refine ⟨⟨trivial, fe51Add_bounded _ _ _ _ _ _ _ _ _ _ (2 ^ 54) hw6_b.2 hw1_b.2⟩, ?_⟩
    rw [fe51Add_val_mod _ _ _ _ _ _ _ _ _ _ hw6_b.2 hw1_b.2,
        fold_fe51ValOfBytes w_6, fold_fe51ValOfBytes w_1, hw6_v, hw1_v, ← hV_A24E]
    exact mont_w2_factor_eq V_AA V_BB V_E hV_AA_lt hV_E.symm
  intro bufA24EpBB ⟨⟨hA24EpBB_l, hAE0, hAE1, hAE2, hAE3, hAE4⟩, hA24EpBB_v⟩
  clear hsA24EpBB_ge hsA24EpBB sA24EpBB
  generalize hV_W2 : fpMul V_E (fpAdd V_AA (fpMul a24 V_E)) = V_W2
  wp_x25519_call hmul
  clean_prev_sf; norm_sf 224
  obtain ⟨hw8_l, hw8_b, hw8_v⟩ := fe51_mul_post_props w_8 V_W2 (ha := hE_v) (hbv := hA24EpBB_v) (hV := hV_W2)
  clear hw6_b hw6_v hw1_b hw1_v hw0_0 hw0_1 hw0_2 hw0_3 hw0_4 hw1_0 hw1_1 hw1_2 hw1_3 hw1_4 hsU2 sU2
    hE0 hE1 hE2 hE3 hE4 hE_v hE_b hAE0 hAE1 hAE2 hAE3 hAE4 hA24EpBB_v hsW2 sW2
  obtain ⟨hu1_l, hu1_0, hu1_1, hu1_2, hu1_3, hu1_4⟩ := hu1_b
  obtain ⟨_, hw5_0, hw5_1, hw5_2, hw5_3, hw5_4⟩ := fe51LimbsBounded_mono hw5_b (b2 := 2 ^ 54); clear hw5_b
  generalize hV_W3 : fpMul U1 V_Tmp = V_W3
  wp_cut_codeLoaded
  wp_steps
  wp_x25519_call hmul
  clean_prev_sf; norm_sf 224
  obtain ⟨hw9_l, hw9_b, hw9_v⟩ := fe51_mul_post_props w_9 V_W3 (ha := hu1_v) (hbv := hw5_v) (hV := hV_W3)
  subst hV_W3 hV_W2 hV_U2 hV_A24E hV_Tmp hV_U3 hV_CB hV_DA hV_E
  refine Eq.mp (congrArg (fun Q => SepWP _ target_pc _ Q post oom) ?_)
    (hnext _ bufE w_2 w_3 bufSum bufDiff w_4 w_5 w_6 w_7 bufA24EpBB w_8 w_9
      (by exact Eq.trans ‹State.pc _ = _› rfl) (by assumption) (by assumption) (by assumption)
      (by assumption) (by assumption) (by assumption) (by assumption)
      hE_l hw2_l hw3_l hSum_l hDiff_l hw5_l hw6_l hA24EpBB_l
      hw4_b hw4_v hw7_b hw7_v hw8_b hw8_v hw9_b hw9_v)
  sep_ac_rfl

public section

/-! ## 4. Exported Subroutine Contracts (`Blk11`, `Blk12`) -/

set_option maxHeartbeats 800000 in
/-- `<montgomery::ProjectivePoint>::as_affine` (`Blk11`, 130 words, stack 1312). -/
theorem projective_point_as_affine_ok_of
    (hpow22501 : Fe51Pow22501Ok) (hpow2k : Fe51Pow2kOk) (hmul : Fe51MulOk) :
    MontProjectiveAsAffineOk := by
  intro _
  apply x25519Caller_ok x25519CliPC11 x25519CliPl11
  intro b _hb hbase
  wp_init
  have hout_len : a_2.length = 32 := ‹a_2.length = 32›
  have hself_b : montProjBounded a_rest (2 ^ 54) := ‹montProjBounded a_rest _›
  obtain ⟨⟨hu_l, hu_0, hu_1, hu_2, hu_3, hu_4⟩, hu_v⟩ := montProj_take40_props a_rest (2 ^ 54) hself_b
  obtain ⟨⟨hw_in_l, hw_in_0, hw_in_1, hw_in_2, hw_in_3, hw_in_4⟩, hw_in_v⟩ := montProj_drop40_props a_rest (2 ^ 54) hself_b
  apply sepWP_split_stack_callee 1040 272
  apply sepWP_peel_stack_region s0.sp 272 8 264
  apply sepWP_peel_stack_bytes s0.sp 264 40 224; intro recip_init hrecip_init
  apply sepWP_peel_stack_bytes s0.sp 224 40 184; intro c19_init hc19_init
  apply sepWP_peel_stack_region s0.sp 184 8 176
  apply sepWP_peel_stack_bytes s0.sp 176 40 136; intro c3_init hc3_init
  apply sepWP_peel_stack_region s0.sp 136 8 128
  apply sepWP_peel_stack_bytes s0.sp 128 80 48; intro pow_init hpow_init
  open_cells (s0.sp - 48#64) 48 6
  wp_conv_pre => rw [pointsToBytes80_split2 a a_rest hself_b.1]
  wp_cut_codeLoaded
  wp_steps
  wp_x25519_call hpow22501
  norm_sf 1040
  clear hw_in_l hw_in_0 hw_in_1 hw_in_2 hw_in_3 hw_in_4 pow_init hpow_init
  have hw0_b52 : fe51LimbsBounded w (2 ^ 52) := ‹fe51LimbsBounded w _›
  have hw1_b52 : fe51LimbsBounded w_1 (2 ^ 52) := ‹fe51LimbsBounded w_1 _›
  apply sepWP_split_bytes_append s0.sp 128 40 88 (hbs1 := hw0_b52.1)
  obtain ⟨hw_l, hw_0, hw_1, hw_2, hw_3, hw_4⟩ := fe51LimbsBounded_mono hw0_b52 (b2 := 2 ^ 54)
  obtain ⟨hw1_l, hw1_0, hw1_1, hw1_2, hw1_3, hw1_4⟩ := fe51LimbsBounded_mono hw1_b52 (b2 := 2 ^ 54)
  wp_cut_codeLoaded
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcl_copy
  wp_conv_pre => rw [write64_copy5_eq c19_init w hc19_init hw_l, write64_copy5_eq c3_init w_1 hc3_init hw1_l]
  apply sepWP_callee_shrink (s0.sp - 272#64) 1040 96 944
  wp_x25519_call hpow2k
  clean_prev_sf; norm_sf 96
  wp_conv_pre => try rw [show s0.sp - 368#64 = s0.sp - 272#64 - 96#64 by bv_omega]
  apply sepWP_callee_grow (s0.sp - 272#64) 1040 96 944
  clear hw_0 hw_1 hw_2 hw_3 hw_4 c19_init hc19_init c3_init hc3_init
  obtain ⟨hw2_l, hw2_0, hw2_1, hw2_2, hw2_3, hw2_4⟩ := fe51LimbsBounded_mono ‹fe51LimbsBounded w_2 _› (b2 := 2 ^ 54)
  apply sepWP_callee_shrink (s0.sp - 272#64) 1040 224 816
  wp_cut_codeLoaded
  wp_steps
  wp_x25519_call hmul
  clean_prev_sf; norm_sf 224
  clear hw1_0 hw1_1 hw1_2 hw1_3 hw1_4 hw2_0 hw2_1 hw2_2 hw2_3 hw2_4 recip_init hrecip_init
  obtain ⟨hw3_l, hw3_0, hw3_1, hw3_2, hw3_3, hw3_4⟩ := fe51LimbsBounded_mono ‹fe51LimbsBounded w_3 _› (b2 := 2 ^ 54)
  wp_cut_codeLoaded
  wp_steps
  wp_x25519_call hmul
  clean_prev_sf; norm_sf 224
  clear hu_l hu_0 hu_1 hu_2 hu_3 hu_4 hw3_0 hw3_1 hw3_2 hw3_3 hw3_4
  obtain ⟨hw4_l, hl0_b, hl1_b, hl2_b, hl3_b, hl4_b⟩ := fe51LimbsBounded_mono ‹fe51LimbsBounded w_4 _› (b2 := 2 ^ 54)
  have h_val := as_affine_val_eq a_rest w w_1 w_2 w_3 w_4 hu_v hw_in_v
    ‹fe51ValOfBytes w % p25519 = _› ‹fe51ValOfBytes w_1 % p25519 = _›
    ‹fe51ValOfBytes w_2 % p25519 = _› ‹fe51ValOfBytes w_3 % p25519 = _› ‹fe51ValOfBytes w_4 % p25519 = _›
  have h_w4 := pointsToBytes40_sub_eq_cells s0.sp 128#64 120#64 112#64 104#64 96#64 w_4 hw4_l
  apply sepWP_move_end a_1 a_2
  wp_conv_pre => simp only [sepConj_assoc]; rw [h_w4, pointsToBytes32_eq_cells8 a_1 a_2 hout_len]
  generalize hl0_eq : ByteSlice.readLE w_4 0 8 = l0 at *
  generalize hl1_eq : ByteSlice.readLE w_4 8 8 = l1 at *
  generalize hl2_eq : ByteSlice.readLE w_4 16 8 = l2 at *
  generalize hl3_eq : ByteSlice.readLE w_4 24 8 = l3 at *
  generalize hl4_eq : ByteSlice.readLE w_4 32 8 = l4 at *
  wp_cut_codeLoaded
  wp_sym_steps 22
  generalize hh0 : (l0 &&& 2251799813685247#64) + BitVec.setWidth 64 (BitVec.setWidth 32 (l4 >>> 51)) * 19#64 = h0
  generalize hh1 : (l1 &&& 2251799813685247#64) + l0 >>> 51 = h1
  generalize hh2 : (l2 &&& 2251799813685247#64) + l1 >>> 51 = h2
  generalize hh3 : (l3 &&& 2251799813685247#64) + l2 >>> 51 = h3
  generalize hh4 : (l4 &&& 2251799813685247#64) + l3 >>> 51 = h4
  generalize hq : (h4 + (h3 + (h2 + (h1 + (h0 + 19#64) >>> 51) >>> 51) >>> 51) >>> 51) >>> 51 = q
  generalize hu0 : h0 + BitVec.setWidth 64 (BitVec.setWidth 32 q) * 19#64 = u0
  wp_sym_steps 26
  generalize hu1 : h1 + u0 >>> 51 = u1; generalize hu2 : h2 + u1 >>> 51 = u2
  generalize hu3 : h3 + u2 >>> 51 = u3; generalize hu4 : h4 + u3 >>> 51 = u4
  wp_sym_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcl_ret
  have h_bytes : packCanonical51Bytes u0 u1 u2 u3 u4 =
      natToLeBytes 32 (fpMul (montProjOfBytes a_rest).U (fpInv (montProjOfBytes a_rest).W)) := by
    rw [← h_val, fe51ValOfBytes, hl0_eq, hl1_eq, hl2_eq, hl3_eq, hl4_eq]
    exact fe51_to_bytes_math l0 l1 l2 l3 l4 hl0_b hl1_b hl2_b hl3_b hl4_b h0 h1 h2 h3 h4 q u0 u1 u2 u3 u4
      hh0.symm hh1.symm hh2.symm hh3.symm hh4.symm hq.symm hu0.symm hu1.symm hu2.symm hu3.symm hu4.symm
  dsimp only [packCanonical51Bytes] at h_bytes
  wp_conv_pre =>
    rw [← h_w4, ← pointsToBytes_list32 a_1, h_bytes]
    try rw [show s0.sp - 496#64 = s0.sp - 272#64 - 224#64 by bv_omega]
  close_cells (s0.sp - 48#64) 48 6
  apply sepWP_unpeel_stack_bytes s0.sp 88 40 48 (hbs := hw1_l)
  apply sepWP_unpeel_stack_bytes s0.sp 128 40 88 (hbs := hw4_l)
  apply sepWP_unpeel_stack_region s0.sp 136 8 128
  apply sepWP_unpeel_stack_bytes s0.sp 176 40 136 (hbs := hw1_l)
  apply sepWP_unpeel_stack_region s0.sp 184 8 176
  apply sepWP_unpeel_stack_bytes s0.sp 224 40 184 (hbs := hw_l)
  apply sepWP_unpeel_stack_bytes s0.sp 264 40 224 (hbs := hw3_l)
  apply sepWP_unpeel_stack_region s0.sp 272 8 264
  apply sepWP_callee_grow (s0.sp - 272#64) 1040 224 816
  apply sepWP_merge_stack_callee 1040 272
  apply sepWP_fold_point80 a a_rest hself_b.1
  clear h_bytes h_val hu_v hw_in_v hw0_b52 hw1_b52 hself_b h_w4
  generalize natToLeBytes 32 (fpMul (montProjOfBytes a_rest).U (fpInv (montProjOfBytes a_rest).W)) = res_bytes
  wp_done

set_option maxHeartbeats 800000 in
/-- `montgomery::differential_add_and_double` (`Blk12`, 238 words, stack 1056). -/
theorem differential_add_and_double_ok_of
    (hpow2k : Fe51Pow2kOk) (hmul : Fe51MulOk) (hmul_ro_left : Fe51MulRoLeftOk) :
    MontDiffAddAndDoubleOk := by
  intro _
  apply x25519Caller_ok x25519CliPC12 x25519CliPl12
  intro b hb hbase
  wp_init
  obtain ⟨hp_len, hpU_b, hpW_b⟩ : montProjBounded a_3 (2 ^ 53) := by assumption
  obtain ⟨hq_len, hqU_b, hqW_b⟩ : montProjBounded a_4 (2 ^ 53) := by assumption
  dsimp only [montFe51LimbsBoundedAt, fe51LimbsBoundedAt, Nat.reduceAdd] at hpU_b hpW_b hqU_b hqW_b
  have hu1_b : fe51LimbsBounded a_rest (2 ^ 54) := by assumption
  have hu1_len : a_rest.length = 40 := hu1_b.1
  have hp_ge : HasLenGe a_3 80 := ⟨by omega⟩
  have hq_ge : HasLenGe a_4 80 := ⟨by omega⟩
  have hu1_ge : HasLenGe a_rest 40 := ⟨by omega⟩
  have hp0U : fe51Val (ByteSlice.readLE a_3 0 8) (ByteSlice.readLE a_3 8 8)
      (ByteSlice.readLE a_3 16 8) (ByteSlice.readLE a_3 24 8) (ByteSlice.readLE a_3 32 8) % p25519 =
      (montProjOfBytes a_3).U := rfl
  have hp0W : fe51Val (ByteSlice.readLE a_3 40 8) (ByteSlice.readLE a_3 48 8)
      (ByteSlice.readLE a_3 56 8) (ByteSlice.readLE a_3 64 8) (ByteSlice.readLE a_3 72 8) % p25519 =
      (montProjOfBytes a_3).W := rfl
  have hq0U : fe51Val (ByteSlice.readLE a_4 0 8) (ByteSlice.readLE a_4 8 8)
      (ByteSlice.readLE a_4 16 8) (ByteSlice.readLE a_4 24 8) (ByteSlice.readLE a_4 32 8) % p25519 =
      (montProjOfBytes a_4).U := rfl
  have hq0W : fe51Val (ByteSlice.readLE a_4 40 8) (ByteSlice.readLE a_4 48 8)
      (ByteSlice.readLE a_4 56 8) (ByteSlice.readLE a_4 64 8) (ByteSlice.readLE a_4 72 8) % p25519 =
      (montProjOfBytes a_4).W := rfl
  generalize hp0_eq : montProjOfBytes a_3 = P0 at hp0U hp0W ⊢
  generalize hq0_eq : montProjOfBytes a_4 = Q0 at hq0U hq0W ⊢
  generalize hu1_v : fe51ValOfBytes a_rest % p25519 = U1 at ⊢
  clear hp0_eq hq0_eq
  apply sepWP_split_stack_callee 224 832
  apply sepWP_callee_shrink (s0.sp - 832#64) 224 96 128
  apply sepWP_peel_stack_region s0.sp 832 8 824
  open_cells (s0.sp - 832#64) 8 1
  apply sepWP_peel_stack_bytes6 s0.sp 824 784 744 704 664 624 584
  intro sA sB sC sD sAA sBB hsA hsB hsC hsD hsAA hsBB
  apply sepWP_peel_stack_bytes6 s0.sp 584 544 504 464 424 384 344
  intro sE sDA sCB sSum sDiff sU3 hsE hsDA hsCB hsSum hsDiff hsU3
  apply sepWP_peel_stack_bytes6 s0.sp 344 304 264 224 184 144 104
  intro sTmp sA24E sU2 sA24EpBB sW2 sW3 hsTmp hsA24E hsU2 hsA24EpBB hsW2 hsW3
  open_cells (s0.sp - 104#64) 104 13
  have hsA_ge : HasLenGe sA 40 := ⟨by omega⟩
  have hsB_ge : HasLenGe sB 40 := ⟨by omega⟩
  have hsC_ge : HasLenGe sC 40 := ⟨by omega⟩
  have hsD_ge : HasLenGe sD 40 := ⟨by omega⟩
  wp_cut_codeLoaded
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcl_abcd
  apply sepWP_abstract_bytes (s0.sp - 824#64)
    (fun buf => fe51LimbsBounded buf (2 ^ 54) ∧ fe51ValOfBytes buf % p25519 = fpAdd P0.U P0.W)
  · unfold fe51LimbsBounded fe51ValOfBytes
    simp (disch := decide) only [readLE_write64_self', readLE_write64_ne, write64_length_eq, hsA, Nat.min_eq_left]
    refine ⟨⟨trivial, fe51Add_bounded _ _ _ _ _ _ _ _ _ _ (2 ^ 54) hpW_b hpU_b⟩, ?_⟩
    rw [fe51Add_val_mod _ _ _ _ _ _ _ _ _ _ hpW_b hpU_b, hp0W, hp0U, fpAdd_comm]
  intro bufA ⟨⟨hA_l, hA0, hA1, hA2, hA3, hA4⟩, hA_v⟩
  apply sepWP_abstract_bytes (s0.sp - 784#64)
    (fun buf => fe51LimbsBounded buf (2 ^ 52) ∧ fe51ValOfBytes buf % p25519 = fpSub P0.U P0.W)
  · unfold fe51LimbsBounded fe51ValOfBytes
    simp (disch := decide) only [readLE_write64_self', readLE_write64_ne, write64_length_eq, hsB, Nat.min_eq_left, bv64_add_bias0_sub]
    refine ⟨⟨trivial, fe51Reduce_bounded _ _ _ _ _⟩, ?_⟩
    rw [fe51Reduce_val_mod, fe51Sub_val_mod _ _ _ _ _ _ _ _ _ _ hpU_b hpW_b, hp0U, hp0W]
  intro bufB ⟨hB_b, hB_v⟩
  apply sepWP_abstract_bytes (s0.sp - 744#64)
    (fun buf => fe51LimbsBounded buf (2 ^ 54) ∧ fe51ValOfBytes buf % p25519 = fpAdd Q0.U Q0.W)
  · unfold fe51LimbsBounded fe51ValOfBytes
    simp (disch := decide) only [readLE_write64_self', readLE_write64_ne, write64_length_eq, hsC, Nat.min_eq_left]
    refine ⟨⟨trivial, fe51Add_bounded _ _ _ _ _ _ _ _ _ _ (2 ^ 54) hqW_b hqU_b⟩, ?_⟩
    rw [fe51Add_val_mod _ _ _ _ _ _ _ _ _ _ hqW_b hqU_b, hq0W, hq0U, fpAdd_comm]
  intro bufC ⟨hC_b, hC_v⟩
  apply sepWP_abstract_bytes (s0.sp - 704#64)
    (fun buf => fe51LimbsBounded buf (2 ^ 52) ∧ fe51ValOfBytes buf % p25519 = fpSub Q0.U Q0.W)
  · unfold fe51LimbsBounded fe51ValOfBytes
    simp (disch := decide) only [readLE_write64_self', readLE_write64_ne, write64_length_eq, hsD, Nat.min_eq_left, bv64_add_bias0_sub]
    refine ⟨⟨trivial, fe51Reduce_bounded _ _ _ _ _⟩, ?_⟩
    rw [fe51Reduce_val_mod, fe51Sub_val_mod _ _ _ _ _ _ _ _ _ _ hqU_b hqW_b, hq0U, hq0W]
  intro bufD ⟨hD_b, hD_v⟩
  generalize hV_AA : fpSq (fpAdd P0.U P0.W) = V_AA
  wp_x25519_call hpow2k
  norm_sf 96
  obtain ⟨hw_l, hw_b, hw_v⟩ := fe51_sq_post_props w V_AA (ha := hA_v) (hV := hV_AA)
  clear hpU_b hpW_b hqU_b hqW_b hp0U hp0W hq0U hq0W hsA_ge hsB_ge hsC_ge hsD_ge hsA hsB hsC hsD sA sB sC sD hsAA sAA
  obtain ⟨hB_l, hB0, hB1, hB2, hB3, hB4⟩ := fe51LimbsBounded_mono hB_b (b2 := 2 ^ 54); clear hB_b
  generalize hV_BB : fpSq (fpSub P0.U P0.W) = V_BB
  wp_cut_codeLoaded
  wp_steps
  wp_x25519_call hpow2k
  clean_prev_sf; norm_sf 96
  obtain ⟨hw1_l, hw1_b, hw1_v⟩ := fe51_sq_post_props w_1 V_BB (ha := hB_v) (hV := hV_BB)
  clear hsBB sBB
  have hC_l : bufC.length = 40 := hC_b.1
  have hD_l : bufD.length = 40 := hD_b.1
  have hV_AA_lt : V_AA < p25519 := hV_AA ▸ fpSq_lt _
  apply sepWP_callee_grow (s0.sp - 832#64) 224 96 128
  apply diff_add_mid hpow2k hmul hmul_ro_left b s0.sp a_1 a a_2 P0 Q0 U1 V_AA V_BB
    a_rest bufA bufB bufC bufD w w_1 sE sDA sCB sSum sDiff sU3 sTmp sA24E sU2 sA24EpBB sW2 sW3
    hb hbase
    (by exact Eq.trans ‹State.pc _ = _› rfl) (by assumption) (by assumption) hsp_align
    (by exact Eq.trans ‹State.readReg64 _ (Reg.gpr 29#5) = _› rfl)
    (by exact Eq.trans ‹State.readReg64 _ (Reg.gpr 20#5) = _› rfl)
    (by exact Eq.trans ‹State.readReg64 _ (Reg.gpr 19#5) = _› rfl)
    (by exact Eq.trans ‹State.readReg64 _ (Reg.gpr 22#5) = _› rfl)
    (by exact Eq.trans ‹State.readReg64 _ (Reg.gpr 24#5) = _› rfl)
    (by exact Eq.trans ‹State.readReg64 _ (Reg.gpr 25#5) = _› rfl)
    (by assumption)
    hV_AA_lt hu1_b hu1_v
    ⟨hA_l, hA0, hA1, hA2, hA3, hA4⟩ hA_v ⟨hB_l, hB0, hB1, hB2, hB3, hB4⟩ hB_v hC_b hC_v hD_b hD_v
    hw_b hw_v hw1_b hw1_v hsE hsDA hsCB hsSum hsDiff hsU3 hsTmp hsA24E hsU2 hsA24EpBB hsW2 hsW3
  clear hA0 hA1 hA2 hA3 hA4 hA_v hB0 hB1 hB2 hB3 hB4 hB_v hC_b hC_v hD_b hD_v
    hw_b hw_v hw1_b hw1_v hu1_b hu1_v hV_AA_lt
    hsE hsDA hsCB hsSum hsDiff hsU3 hsTmp hsA24E hsU2 hsA24EpBB hsW2 hsW3
    sE sDA sCB sSum sDiff sU3 sTmp sA24E sU2 sA24EpBB sW2 sW3
  intro sf_mid bufE w_2 w_3 bufSum bufDiff w_4 w_5 w_6 w_7 bufA24EpBB w_8 w_9
    hpc_m hrun_m hsp_m hx29_m hx20_m hx19_m hvregs_m _hcl_m
    hE_l hw2_l hw3_l hSum_l hDiff_l hw5_l hw6_l hA24EpBB_l
    hw4_b hw4_v hw7_b hw7_v hw8_b hw8_v hw9_b hw9_v
  clean_prev_sf
  have hw4_l : w_4.length = 40 := hw4_b.1
  have hw7_l : w_7.length = 40 := hw7_b.1
  have hw8_l : w_8.length = 40 := hw8_b.1
  have hw9_l : w_9.length = 40 := hw9_b.1
  wp_cut_codeLoaded
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcl_ret
  close_cells (s0.sp - 104#64) 104 13
  apply sepWP_unpeel_stack_bytes6 s0.sp 344 304 264 224 184 144 104
    (hl1 := hw5_l) (hl2 := hw6_l) (hl3 := hw7_l) (hl4 := hA24EpBB_l) (hl5 := hw8_l) (hl6 := hw9_l)
  apply sepWP_unpeel_stack_bytes6 s0.sp 584 544 504 464 424 384 344
    (hl1 := hE_l) (hl2 := hw2_l) (hl3 := hw3_l) (hl4 := hSum_l) (hl5 := hDiff_l) (hl6 := hw4_l)
  apply sepWP_unpeel_stack_bytes6 s0.sp 824 784 744 704 664 624 584
    (hl1 := hA_l) (hl2 := hB_l) (hl3 := hC_l) (hl4 := hD_l) (hl5 := hw_l) (hl6 := hw1_l)
  close_cells (s0.sp - 832#64) 8 1
  apply sepWP_unpeel_stack_region s0.sp 832 8 824
  apply sepWP_merge_stack_callee 224 832
  have h_out1 : (⟨fe51ValOfBytes w_7 % p25519, fe51ValOfBytes w_8 % p25519⟩ : MontProjPoint) =
      (montDiffAddAndDouble U1 P0 Q0).1 := by
    rw [hw7_v, hw8_v, ← hV_AA, ← hV_BB]; rfl
  have h_out2 : (⟨fe51ValOfBytes w_4 % p25519, fe51ValOfBytes w_9 % p25519⟩ : MontProjPoint) =
      (montDiffAddAndDouble U1 P0 Q0).2 := by
    rw [hw4_v, hw9_v]; rfl
  apply sepWP_abstract_bytes a_1
    (fun p_out => montProjBounded p_out (2 ^ 52) ∧
      montProjOfBytes p_out = (montDiffAddAndDouble U1 P0 Q0).1)
  · unfold montProjBounded montFe51LimbsBoundedAt fe51LimbsBoundedAt montProjOfBytes montFe51ValAt fe51ValAt
    simp (disch := decide) only [Nat.reduceAdd, readLE_write64_self', readLE_write64_ne,
      write64_length_eq, hp_len, Nat.min_eq_left, fold_fe51ValOfBytes w_7, fold_fe51ValOfBytes w_8]
    exact ⟨⟨trivial, hw7_b.2, hw8_b.2⟩, h_out1⟩
  intro p_out ⟨hp_out_b, hp_out_v⟩
  apply sepWP_abstract_bytes a
    (fun q_out => montProjBounded q_out (2 ^ 52) ∧
      montProjOfBytes q_out = (montDiffAddAndDouble U1 P0 Q0).2)
  · unfold montProjBounded montFe51LimbsBoundedAt fe51LimbsBoundedAt montProjOfBytes montFe51ValAt fe51ValAt
    simp (disch := decide) only [Nat.reduceAdd, readLE_write64_self', readLE_write64_ne,
      write64_length_eq, hq_len, Nat.min_eq_left, fold_fe51ValOfBytes w_4, fold_fe51ValOfBytes w_9]
    exact ⟨⟨trivial, hw4_b.2, hw9_b.2⟩, h_out2⟩
  intro q_out ⟨hq_out_b, hq_out_v⟩
  rcases hp_out_b with ⟨hp_out_len, hp_out_u, hp_out_w⟩
  rcases hq_out_b with ⟨hq_out_len, hq_out_u, hq_out_w⟩
  dsimp only [montFe51LimbsBoundedAt, fe51LimbsBoundedAt, Nat.reduceAdd] at hp_out_u hp_out_w hq_out_u hq_out_w
  rcases hp_out_u with ⟨hp0, hp1, hp2, hp3, hp4⟩; rcases hp_out_w with ⟨hp5, hp6, hp7, hp8, hp9⟩
  rcases hq_out_u with ⟨hq0, hq1, hq2, hq3, hq4⟩; rcases hq_out_w with ⟨hq5, hq6, hq7, hq8, hq9⟩
  clear hw4_b hw4_v hw7_b hw7_v hw8_b hw8_v hw9_b hw9_v h_out1 h_out2 hV_AA hV_BB hp_ge hq_ge hu1_ge
  wp_done

end

end LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.MontgomeryLadderCode1
