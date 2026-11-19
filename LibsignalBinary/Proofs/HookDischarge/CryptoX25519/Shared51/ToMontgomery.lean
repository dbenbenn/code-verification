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
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Field51
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Field51Pow
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `<EdwardsPoint>::to_montgomery` Machine-Code Proof

Machine-code verification of `<EdwardsPoint>::to_montgomery` (`x25519CliMultiLib` block `10`).
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.ToMontgomery

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj ProofLib
open VerifiedLibraries.Common (p25519 fpAdd fpSub fpMul fpInv fpPow natToLeBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedObjDefs (x25519CliMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedCodeBase (
  X25519CliPlacement x25519CliMpl x25519Caller_ok
  resolve_blk01 resolve_blk02 resolve_blk05)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.CommonBase (fe51ValOfBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.InternalSpecs (
  fe51LimbsBounded fe51ValAt fe51Point4Bounded edExtOfBytes edExtToMontgomeryU
  Fe51MulOk Fe51Pow2kOk Fe51Pow22501Ok EdwardsPointToMontgomeryOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.SliceBase (
  HasLenGe readLE_write64_self' readLE_write64_ne write64_length_eq sub_ofNat64_add
  sepWP_split_stack_callee sepWP_merge_stack_callee
  sepWP_peel_stack_bytes sepWP_unpeel_stack_bytes
  sepWP_callee_shrink sepWP_callee_grow sepWP_abstract_bytes
  fe51Add_bounded fe51Add_val_mod fe51Reduce_bounded fe51Reduce_val_mod fe51Sub_val_mod)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Field51Base (
  sepWP_split_bytes_append write64_copy5_eq compress_recip_eq_fpInv
  fe51LimbsBounded_of_52 pointsToBytes40_sub_eq_cells pointsToBytes32_eq_cells8
  fe51_to_bytes_of_bytes pointsToBytes_packCanonical51Bytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Field51 (
  fe51_mul_ok fe51_pow2k_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Field51Pow (
  fe51_pow22501_ok)

arm64_proof_prelude

attribute [local irreducible] MultiPlacedLib.CodeLoaded

open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedCodeBase (x25519CliMpl) in
gen_block_fetches x25519Cli 10 x25519CliMultiLib X25519CliPlacement 171 rebase rho sub

@[local simp, local arm64_norm, local wp_norm]
private theorem x25519CliPl10_rho_norm [X25519CliPlacement] (sym : String) :
    x25519CliPl10.ρ sym = x25519CliMultiLib.resolve x25519CliMpl sym := rfl

private theorem toMontgomery_of_muls
    (self_bs u_bs w_bs t19_bs t3_bs t2_5_bs recip_bs res_bs : List (BitVec 8))
    (hu : fe51ValOfBytes u_bs % p25519 = fpAdd (fe51ValAt self_bs 40 % p25519) (fe51ValAt self_bs 80 % p25519))
    (hw : fe51ValOfBytes w_bs % p25519 = fpSub (fe51ValAt self_bs 80 % p25519) (fe51ValAt self_bs 40 % p25519))
    (ht19 : fe51ValOfBytes t19_bs % p25519 = fpPow (fe51ValOfBytes w_bs % p25519) (2 ^ 250 - 1))
    (ht3 : fe51ValOfBytes t3_bs % p25519 = fpPow (fe51ValOfBytes w_bs % p25519) 11)
    (ht2_5 : fe51ValOfBytes t2_5_bs % p25519 = fpPow (fe51ValOfBytes t19_bs % p25519) (2 ^ (5#32 : BitVec 32).toNat))
    (hrecip : fe51ValOfBytes recip_bs % p25519 = (fe51ValOfBytes t2_5_bs * fe51ValOfBytes t3_bs) % p25519)
    (hres : fe51ValOfBytes res_bs % p25519 = (fe51ValOfBytes u_bs * fe51ValOfBytes recip_bs) % p25519) :
    fe51ValOfBytes res_bs % p25519 = edExtToMontgomeryU (edExtOfBytes self_bs) := by
  have h5 : (5#32 : BitVec 32).toNat = 5 := rfl
  rw [h5] at ht2_5
  have hinv := compress_recip_eq_fpInv (fe51ValOfBytes w_bs) (fe51ValOfBytes t19_bs)
    (fe51ValOfBytes t3_bs) (fe51ValOfBytes t2_5_bs) (fe51ValOfBytes recip_bs)
    ht19 ht3 ht2_5 hrecip
  rw [hw] at hinv
  have hu_comm : fpAdd (fe51ValAt self_bs 40 % p25519) (fe51ValAt self_bs 80 % p25519) =
      fpAdd (fe51ValAt self_bs 80 % p25519) (fe51ValAt self_bs 40 % p25519) := by
    dsimp only [fpAdd]
    rw [Nat.add_comm]
  dsimp only [edExtToMontgomeryU, edExtOfBytes, fpMul]
  rw [hres, Nat.mul_mod, hu, hu_comm, hinv, ← Nat.mul_mod]

private theorem sepWP_head_region_sub (sp : BitVec 64) (off off' n m : Nat) {v : BitVec 64}
    {prog : Program} {tpc : BitVec 64} {s : State} {P F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hP : P = (((sp - BitVec.ofNat 64 off) ↦₆₄ v) ∗ memRegion (sp - BitVec.ofNat 64 off') m) ∗ F := by sep_focus)
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
      let offLit := Lean.Syntax.mkNumLit (toString off)
      let off'Lit := Lean.Syntax.mkNumLit (toString (off - 8))
      let nLit := Lean.Syntax.mkNumLit (toString n)
      let n'Lit := Lean.Syntax.mkNumLit (toString (n - 8))
      let k'Lit := Lean.Syntax.mkNumLit (toString (k - 1))
      `(tactic| (close_cells_sub $sp $off'Lit $n'Lit $k'Lit; apply sepWP_head_region_sub $sp $offLit $off'Lit $nLit $n'Lit))

public section

set_option maxHeartbeats 800000 in
/-- Conditional `<EdwardsPoint>::to_montgomery` (`Blk10`, 171 insns) contract. -/
theorem edwards_point_to_montgomery_ok_of
    (hPow22501 : Fe51Pow22501Ok) (hPow2k : Fe51Pow2kOk) (hMul : Fe51MulOk) :
    EdwardsPointToMontgomeryOk := by
  intro _
  apply x25519Caller_ok x25519CliPC10 x25519CliPl10
  intro b hb hbase
  wp_init
  have hout_len : a_2.length = 32 := ‹_›
  obtain ⟨ha_len, hX_b, hY_b, hZ_b, hT_b⟩ := ‹fe51Point4Bounded a_rest (2 ^ 53)›
  have ha_ge : HasLenGe a_rest 160 := ⟨Nat.le_of_eq ha_len.symm⟩
  apply sepWP_split_stack_callee 1040 352
  apply sepWP_peel_stack_bytes s0.sp 352 8 344; intro gap0_init hgap0_init
  apply sepWP_peel_stack_bytes s0.sp 344 40 304; intro u_init hu_init
  apply sepWP_peel_stack_bytes s0.sp 304 40 264; intro w_init hw_init
  apply sepWP_peel_stack_bytes s0.sp 264 40 224; intro recip_init hrecip_init
  apply sepWP_peel_stack_bytes s0.sp 224 40 184; intro c19_init hc19_init
  apply sepWP_peel_stack_bytes s0.sp 184 8 176; intro gap1_init hgap1_init
  apply sepWP_peel_stack_bytes s0.sp 176 40 136; intro c3_init hc3_init
  apply sepWP_peel_stack_bytes s0.sp 136 8 128; intro gap2_init hgap2_init
  apply sepWP_peel_stack_bytes s0.sp 128 80 48; intro pow_init hpow_init
  open_cells (s0.sp - 48#64) 48 6
  wp_cut_codeLoaded
  have hu_ge : HasLenGe u_init 40 := ⟨Nat.le_of_eq hu_init.symm⟩
  have hw_ge : HasLenGe w_init 40 := ⟨Nat.le_of_eq hw_init.symm⟩
  -- Prologue + U = Y + Z (sp + 8) + W = reduce(Z - Y) (sp + 48) -> Call 1: pow22501
  wp_steps
  apply sepWP_abstract_bytes (s0.sp - 344#64)
    (fun buf => fe51LimbsBounded buf (2 ^ 54) ∧
      fe51ValOfBytes buf % p25519 = fpAdd (fe51ValAt a_rest 40 % p25519) (fe51ValAt a_rest 80 % p25519))
  · unfold fe51LimbsBounded fe51ValOfBytes fe51ValAt
    simp (disch := decide) only [readLE_write64_self', readLE_write64_ne, write64_length_eq, hu_init, Nat.min_eq_left]
    exact ⟨⟨trivial, fe51Add_bounded _ _ _ _ _ _ _ _ _ _ (2 ^ 54) hY_b hZ_b⟩,
      fe51Add_val_mod _ _ _ _ _ _ _ _ _ _ hY_b hZ_b⟩
  intro u_bs ⟨⟨hu_l, hu_0, hu_1, hu_2, hu_3, hu_4⟩, hu_v⟩
  clear hu_ge
  apply sepWP_abstract_bytes (s0.sp - 304#64)
    (fun buf => fe51LimbsBounded buf (2 ^ 52) ∧
      fe51ValOfBytes buf % p25519 = fpSub (fe51ValAt a_rest 80 % p25519) (fe51ValAt a_rest 40 % p25519))
  · unfold fe51LimbsBounded fe51ValOfBytes fe51ValAt
    simp (disch := decide) only [readLE_write64_self', readLE_write64_ne, write64_length_eq, hw_init, Nat.min_eq_left]
    refine ⟨⟨trivial, fe51Reduce_bounded _ _ _ _ _⟩, ?_⟩
    rw [fe51Reduce_val_mod]
    exact fe51Sub_val_mod _ _ _ _ _ _ _ _ _ _ hZ_b hY_b
  intro w_bs ⟨hw_b, hw_v⟩
  clear hw_ge
  obtain ⟨hw_l, hw_0, hw_1, hw_2, hw_3, hw_4⟩ := fe51LimbsBounded_of_52 w_bs hw_b
  wp_x25519_call hPow22501; norm_sf 1040
  clear hw_0 hw_1 hw_2 hw_3 hw_4
  -- Split 80-byte pow22501 output into w (t19) and w_1 (t3), copy into c19 and c3
  have ht19_b : fe51LimbsBounded w (2 ^ 52) := ‹_›
  have ht3_b : fe51LimbsBounded w_1 (2 ^ 52) := ‹_›
  have ht19_v : fe51ValOfBytes w % p25519 = fpPow (fe51ValOfBytes w_bs % p25519) (2 ^ 250 - 1) := ‹_›
  have ht3_v : fe51ValOfBytes w_1 % p25519 = fpPow (fe51ValOfBytes w_bs % p25519) 11 := ‹_›
  apply sepWP_split_bytes_append s0.sp 128 40 88 (hbs1 := ht19_b.1)
  obtain ⟨ht19_l, ht19_0, ht19_1, ht19_2, ht19_3, ht19_4⟩ := fe51LimbsBounded_of_52 w ht19_b
  obtain ⟨ht3_l, ht3_0, ht3_1, ht3_2, ht3_3, ht3_4⟩ := fe51LimbsBounded_of_52 w_1 ht3_b
  wp_cut_codeLoaded
  wp_steps
  wp_conv_pre =>
    rw [write64_copy5_eq c19_init w hc19_init ht19_l,
        write64_copy5_eq c3_init w_1 hc3_init ht3_l]
  -- Call 2: pow2k(x29 - 80, sp + 128, 5)
  apply sepWP_callee_shrink (s0.sp - 352#64) 1040 96 944
  wp_x25519_call hPow2k; clean_prev_sf; norm_sf 96
  apply sepWP_callee_grow (s0.sp - 352#64) 1040 96 944
  clear ht19_0 ht19_1 ht19_2 ht19_3 ht19_4
  have ht2_5_v : fe51ValOfBytes w_2 % p25519 = fpPow (fe51ValOfBytes w % p25519) (2 ^ (5#32 : BitVec 32).toNat) := ‹_›
  obtain ⟨ht2_5_l, ht2_5_0, ht2_5_1, ht2_5_2, ht2_5_3, ht2_5_4⟩ := fe51LimbsBounded_of_52 w_2 ‹fe51LimbsBounded w_2 _›
  -- Call 3: mul(sp + 88, x29 - 80, x29 - 128) -> s0.sp - 264#64 (recip)
  apply sepWP_callee_shrink (s0.sp - 352#64) 1040 224 816
  wp_cut_codeLoaded; wp_steps; wp_x25519_call hMul; clean_prev_sf; norm_sf 224
  clear ht3_0 ht3_1 ht3_2 ht3_3 ht3_4 ht2_5_0 ht2_5_1 ht2_5_2 ht2_5_3 ht2_5_4
  have hrec_v : fe51ValOfBytes w_3 % p25519 = (fe51ValOfBytes w_2 * fe51ValOfBytes w_1) % p25519 := ‹_›
  obtain ⟨hrec_l, hrec_0, hrec_1, hrec_2, hrec_3, hrec_4⟩ := fe51LimbsBounded_of_52 w_3 ‹fe51LimbsBounded w_3 _›
  -- Call 4: mul(x29 - 80, sp + 8, sp + 88) -> s0.sp - 128#64 (u_fe)
  wp_cut_codeLoaded; wp_steps; wp_x25519_call hMul; clean_prev_sf; norm_sf 224
  apply sepWP_callee_grow (s0.sp - 352#64) 1040 224 816
  clear hu_0 hu_1 hu_2 hu_3 hu_4 hrec_0 hrec_1 hrec_2 hrec_3 hrec_4
  have hres_v : fe51ValOfBytes w_4 % p25519 = (fe51ValOfBytes u_bs * fe51ValOfBytes w_3) % p25519 := ‹_›
  -- Inline FieldElement51::to_bytes from x29 - 80 (w_4 at s0.sp - 128#64) to x19 (a_1)
  obtain ⟨hw4_len, hl0, hl1, hl2, hl3, hl4⟩ := ‹fe51LimbsBounded w_4 (2 ^ 52)›
  have h_w4 := pointsToBytes40_sub_eq_cells s0.sp 128#64 120#64 112#64 104#64 96#64 w_4 hw4_len
  wp_conv_pre => rw [h_w4, pointsToBytes32_eq_cells8 a_1 a_2 hout_len]
  generalize hl0_eq : ByteSlice.readLE w_4 0 8 = l0 at *
  generalize hl1_eq : ByteSlice.readLE w_4 8 8 = l1 at *
  generalize hl2_eq : ByteSlice.readLE w_4 16 8 = l2 at *
  generalize hl3_eq : ByteSlice.readLE w_4 24 8 = l3 at *
  generalize hl4_eq : ByteSlice.readLE w_4 32 8 = l4 at *
  -- +0x128 .. +0x178 (21 instructions) -> h0..h4, q, u0
  wp_sym_steps 21
  generalize hh0 : (l0 &&& 2251799813685247#64) + BitVec.setWidth 64 (BitVec.setWidth 32 (l4 >>> 51)) * 19#64 = h0
  generalize hh1 : (l1 &&& 2251799813685247#64) + l0 >>> 51 = h1
  generalize hh2 : (l2 &&& 2251799813685247#64) + l1 >>> 51 = h2
  generalize hh3 : (l3 &&& 2251799813685247#64) + l2 >>> 51 = h3
  generalize hh4 : (l4 &&& 2251799813685247#64) + l3 >>> 51 = h4
  generalize hq : (h4 + (h3 + (h2 + (h1 + (h0 + 19#64) >>> 51) >>> 51) >>> 51) >>> 51) >>> 51 = q
  generalize hu0 : h0 + BitVec.setWidth 64 (BitVec.setWidth 32 q) * 19#64 = u0
  wp_conv_pre => rw [← h_w4]
  -- +0x17c .. +0x184 (3 instructions) -> u1
  wp_sym_steps 3
  generalize hu1 : h1 + u0 >>> 51 = u1
  -- +0x188 .. +0x194 (4 instructions) -> u2
  wp_sym_steps 4
  generalize hu2 : h2 + u1 >>> 51 = u2
  -- +0x198 .. +0x1b4 (8 instructions) -> u3
  wp_sym_steps 8
  generalize hu3 : h3 + u2 >>> 51 = u3
  -- +0x1b8 .. +0x1cc (6 instructions) -> u4
  wp_sym_steps 6
  generalize hu4 : h4 + u3 >>> 51 = u4
  -- +0x1d0 .. +0x294 (50 instructions) -> all 32 byte stores to a_1
  wp_sym_steps 50
  have h_bytes := fe51_to_bytes_of_bytes w_4 l0 l1 l2 l3 l4 hl0_eq hl1_eq hl2_eq hl3_eq hl4_eq
    hl0 hl1 hl2 hl3 hl4 h0 h1 h2 h3 h4 q u0 u1 u2 u3 u4
    hh0 hh1 hh2 hh3 hh4 hq hu0 hu1 hu2 hu3 hu4
  have h_val := toMontgomery_of_muls a_rest u_bs w_bs w w_1 w_2 w_3 w_4
    hu_v hw_v ht19_v ht3_v ht2_5_v hrec_v hres_v
  wp_conv_pre =>
    rw [pointsToBytes_packCanonical51Bytes, h_bytes, h_val]
  -- Epilogue (+0x298 .. +0x2a8)
  wp_steps
  close_cells_sub s0.sp 48 48 6
  apply sepWP_unpeel_stack_bytes s0.sp 88 40 48 (hbs := ht3_l)
  apply sepWP_unpeel_stack_bytes s0.sp 128 40 88 (hbs := hw4_len)
  apply sepWP_unpeel_stack_bytes s0.sp 136 8 128 (hbs := hgap2_init)
  apply sepWP_unpeel_stack_bytes s0.sp 176 40 136 (hbs := ht3_l)
  apply sepWP_unpeel_stack_bytes s0.sp 184 8 176 (hbs := hgap1_init)
  apply sepWP_unpeel_stack_bytes s0.sp 224 40 184 (hbs := ht19_l)
  apply sepWP_unpeel_stack_bytes s0.sp 264 40 224 (hbs := hrec_l)
  apply sepWP_unpeel_stack_bytes s0.sp 304 40 264 (hbs := hw_l)
  apply sepWP_unpeel_stack_bytes s0.sp 344 40 304 (hbs := hu_l)
  apply sepWP_unpeel_stack_bytes s0.sp 352 8 344 (hbs := hgap0_init)
  apply sepWP_merge_stack_callee 1040 352
  wp_done

/-- `<EdwardsPoint>::to_montgomery` (`Blk10`, 171 insns). -/
theorem edwards_point_to_montgomery_ok : EdwardsPointToMontgomeryOk :=
  edwards_point_to_montgomery_ok_of fe51_pow22501_ok fe51_pow2k_ok fe51_mul_ok

end

end LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.ToMontgomery
