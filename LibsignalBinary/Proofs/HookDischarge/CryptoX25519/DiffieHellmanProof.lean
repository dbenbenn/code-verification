/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.InternalSpecs -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedObjDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedCodeBase
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.SliceBase
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Field51Base
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Field51
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Field51Pow
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Layer0
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.MontgomeryLadderCode1
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.MontgomeryLadderCode

/-!
# RFC 7748 X25519 Diffie–Hellman entrypoint proofs

Machine-code proofs for `x25519CliMultiLib` blocks `16` and `17`, plus unconditional
instantiation of block `15` and the `x25519Ref` list bridge:

- `montgomery_point_mul_ok : MontgomeryPointMulOk` (`Blk15`, 211 insns, stack 1680)
- `montgomery_point_mul_clamped_ok : MontgomeryPointMulClampedOk` (`Blk16`, 17 insns, stack 1728)
- `static_secret_diffie_hellman_ok : StaticSecretDiffieHellmanOk` (`Blk17`, 13 insns, stack 1808)
- `x25519_eq_x25519Ref_toList`: pure `List.Vector` output-list bridge
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace LibsignalBinary.Proofs.HookDischarge.CryptoX25519.DiffieHellmanProof

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj ProofLib
open VerifiedLibraries.Common (
  p25519 fpMul fpInv leBytesToNat natToLeBytes clampScalarBytes clampScalar)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedObjDefs (x25519CliMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedCodeBase (
  X25519CliPlacement x25519CliMpl x25519Caller_ok resolve_blk15 resolve_blk16)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref (
  decodeU255 montLadderLoop x25519 x25519Ref)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.CommonBase (
  fe51_one fe51_mont_a24 fe51OneBytes fe51MontA24Bytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.InternalSpecs (
  clampScalarBytes_length_of_eq32
  MontgomeryPointMulOk MontgomeryPointMulClampedOk StaticSecretDiffieHellmanOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.SliceBase (
  sepWP_split_stack_callee sepWP_merge_stack_callee sepWP_unpeel_stack_bytes
  pointsToBytes32_eq_cells64)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Field51Base (
  sepWP_peel_stack_region)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Field51 (
  fe51_mul_ok fe51_mul_ro_left_ok fe51_pow2k_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Field51Pow (fe51_pow22501_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Layer0 (black_box_u8_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.MontgomeryLadderCode1 (
  projective_point_as_affine_ok_of differential_add_and_double_ok_of)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.MontgomeryLadderCode (
  rev_nth_bit254_ok montgomery_point_mul_ok_of)

arm64_proof_prelude

attribute [local irreducible] MultiPlacedLib.CodeLoaded

/-! ## 1. Block Fetch Generation (`Blk16`, `Blk17`) -/

open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedCodeBase (x25519CliMpl) in
gen_block_fetches x25519Cli 16 x25519CliMultiLib X25519CliPlacement 17 rebase rho sub

@[local simp, local arm64_norm, local wp_norm]
private theorem x25519CliPl16_rho_norm [X25519CliPlacement] (sym : String) :
    x25519CliPl16.ρ sym = x25519CliMultiLib.resolve x25519CliMpl sym := rfl

open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedCodeBase (x25519CliMpl) in
gen_block_fetches x25519Cli 17 x25519CliMultiLib X25519CliPlacement 13 rebase rho sub

@[local simp, local arm64_norm, local wp_norm]
private theorem x25519CliPl17_rho_norm [X25519CliPlacement] (sym : String) :
    x25519CliPl17.ρ sym = x25519CliMultiLib.resolve x25519CliMpl sym := rfl

/-! ## 2. Scalar Clamping & 32-Byte Stack Copy Bridges -/

private theorem clampScalar_of_len32 (bs : List (BitVec 8)) (h : bs.length = 32) :
    clampScalar bs = leBytesToNat (clampScalarBytes bs) := by
  simp [clampScalar, List.take_of_length_le (Nat.le_of_eq h)]

private theorem write8_0_31_eq_clampScalarBytes (bs : List (BitVec 8)) (h : bs.length = 32)
    {v0 v31 : BitVec 8}
    (hv0 : v0 = (bs.getD 0 0#8) &&& 0xf8#8)
    (hv31 : v31 = ((bs.getD 31 0#8) &&& 0x7f#8) ||| 0x40#8) :
    ByteSlice.write8 (ByteSlice.write8 bs 0 v0) 31 v31 = clampScalarBytes bs := by
  subst hv0 hv31
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15,
    _ | ⟨b16, _ | ⟨b17, _ | ⟨b18, _ | ⟨b19, _ | ⟨b20, _ | ⟨b21, _ | ⟨b22, _ | ⟨b23,
    _ | ⟨b24, _ | ⟨b25, _ | ⟨b26, _ | ⟨b27, _ | ⟨b28, _ | ⟨b29, _ | ⟨b30, _ | ⟨b31,
    _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> try simp at h
  rfl

private theorem clamp_byte0_val (b : BitVec 8) :
    BitVec.zeroExtend 8 (BitVec.zeroExtend 64 b &&& 1065151889656#64) = b &&& 0xf8#8 := by
  revert b; decide

private theorem clamp_byte31_val (b : BitVec 8) :
    BitVec.zeroExtend 8 (64#64 ||| BitVec.zeroExtend 64 b >>> 0 &&& 63#64) =
      (b &&& 0x7f#8) ||| 0x40#8 := by
  revert b; decide

private theorem clamp_write8_eq (bs : List (BitVec 8)) (h : bs.length = 32) :
    ByteSlice.write8
      (ByteSlice.write8 bs 0
        (BitVec.zeroExtend 8 (BitVec.zeroExtend 64 (bs.getD 0 0#8) &&& 1065151889656#64)))
      31
      (BitVec.zeroExtend 8 (64#64 ||| BitVec.zeroExtend 64 (bs.getD 31 0#8) >>> 0 &&& 63#64)) =
    clampScalarBytes bs :=
  write8_0_31_eq_clampScalarBytes bs h (clamp_byte0_val _) (clamp_byte31_val _)

private theorem sepWP_replace_sub32 (A B : SepProp)
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (heq : A = B)
    (hf : Full = A ∗ P := by sep_frame)
    (hnext : SepWP prog target_pc s (B ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  rw [hf, heq]; exact hnext

private theorem pointsToBytes32_sub_eq (sp o0 o1 o2 o3 : BitVec 64) (bs : List (BitVec 8))
    (hbs : bs.length = 32)
    (h1 : o0 - 8#64 = o1 := by decide) (h2 : o0 - 16#64 = o2 := by decide)
    (h3 : o0 - 24#64 = o3 := by decide) :
    ((sp - o0) ↦ₛ bs) =
      (((sp - o0) ↦₆₄ ByteSlice.readLE bs 0 8) ∗
       ((sp - o1) ↦₆₄ ByteSlice.readLE bs 8 8) ∗
       ((sp - o2) ↦₆₄ ByteSlice.readLE bs 16 8) ∗
       ((sp - o3) ↦₆₄ ByteSlice.readLE bs 24 8)) := by
  rw [pointsToBytes32_eq_cells64 (sp - o0) bs hbs]
  have ha1 : sp - o0 + 8#64 = sp - o1 := by subst h1; bv_lin
  have ha2 : sp - o0 + 16#64 = sp - o2 := by subst h2; bv_lin
  have ha3 : sp - o0 + 24#64 = sp - o3 := by subst h3; bv_lin
  rw [ha1, ha2, ha3]

/-! ## 3. Machine-Code Subroutine Contracts (`Blk15`, `Blk16`, `Blk17`) -/

public section

/-- `<&MontgomeryPoint as Mul<&Scalar>>::mul` (`Blk15`, 211 insns, stack 1680). -/
theorem montgomery_point_mul_ok : MontgomeryPointMulOk :=
  montgomery_point_mul_ok_of
    rev_nth_bit254_ok
    black_box_u8_ok
    (differential_add_and_double_ok_of fe51_pow2k_ok fe51_mul_ok fe51_mul_ro_left_ok)
    (projective_point_as_affine_ok_of fe51_pow22501_ok fe51_pow2k_ok fe51_mul_ok)

/-- Conditional `<MontgomeryPoint>::mul_clamped` (`Blk16`, 17 insns, stack 1728) contract. -/
theorem montgomery_point_mul_clamped_ok_of
    (hMul : MontgomeryPointMulOk) : MontgomeryPointMulClampedOk := by
  intro _
  apply x25519Caller_ok x25519CliPC16 x25519CliPl16
  intro b _hb _hbase
  wp_init
  have hbytes_len : a_rest.length = 32 := ‹a_rest.length = 32›
  have hclamped_len : (clampScalarBytes a_rest).length = 32 :=
    clampScalarBytes_length_of_eq32 hbytes_len
  apply sepWP_split_stack_callee 1680 48
  apply sepWP_peel_stack_region s0.sp 48 32 16
  open_cells (s0.sp - 48#64) 32 4
  open_cells (s0.sp - 16#64) 16 2
  wp_cut_codeLoaded
  wp_steps 10
  wp_conv_pre => rw [clamp_write8_eq a_rest hbytes_len]
  wp_steps
  apply sepWP_replace_sub32 _ _
    (pointsToBytes32_sub_eq s0.sp 48#64 40#64 32#64 24#64 (clampScalarBytes a_rest) hclamped_len).symm
  wp_x25519_call hMul; norm_sf 1680
  wp_steps
  close_cells (s0.sp - 16#64) 16 2
  apply sepWP_unpeel_stack_bytes s0.sp 48 32 16 (hbs := hclamped_len)
  wp_conv_pre => try rw [show s0.sp - 1728#64 = s0.sp - 48#64 - 1680#64 by bv_lin]
  apply sepWP_merge_stack_callee 1680 48
  have hx25519_eq :
      natToLeBytes 32
        (let u1 := decodeU255 a_4 % p25519
         let res := montLadderLoop 255 (leBytesToNat (clampScalarBytes a_rest)) u1 ⟨1, 0⟩ ⟨u1, 1⟩
         fpMul res.U (fpInv res.W)) = x25519 a_rest a_4 := by
    rw [← clampScalar_of_len32 a_rest hbytes_len]; rfl
  wp_conv_pre => rw [hx25519_eq]
  clear hx25519_eq
  generalize x25519 a_rest a_4 = out_res
  generalize clampScalarBytes a_rest = clamped_res
  wp_done

/-- `<MontgomeryPoint>::mul_clamped` (`Blk16`, 17 insns, stack 1728). -/
theorem montgomery_point_mul_clamped_ok : MontgomeryPointMulClampedOk :=
  montgomery_point_mul_clamped_ok_of montgomery_point_mul_ok

/-- Conditional `<StaticSecret>::diffie_hellman` (`Blk17`, 13 insns, stack 1808) contract. -/
theorem static_secret_diffie_hellman_ok_of
    (hMulC : MontgomeryPointMulClampedOk) : StaticSecretDiffieHellmanOk := by
  intro _
  apply x25519Caller_ok x25519CliPC17 x25519CliPl17
  intro b _hb _hbase
  wp_init
  have hself_len : a_4.length = 32 := ‹a_4.length = 32›
  have hpub_len : a_rest.length = 32 := ‹a_rest.length = 32›
  have hclamped_len : (clampScalarBytes a_4).length = 32 :=
    clampScalarBytes_length_of_eq32 hself_len
  apply sepWP_split_stack_callee 1728 80
  apply sepWP_peel_stack_region s0.sp 80 32 48
  apply sepWP_peel_stack_region s0.sp 48 32 16
  open_cells (s0.sp - 80#64) 32 4
  open_cells (s0.sp - 48#64) 32 4
  open_cells (s0.sp - 16#64) 16 2
  wp_cut_codeLoaded
  wp_steps
  apply sepWP_replace_sub32 _ _
    (pointsToBytes32_sub_eq s0.sp 80#64 72#64 64#64 56#64 a_rest hpub_len).symm
  apply sepWP_replace_sub32 _ _
    (pointsToBytes32_sub_eq s0.sp 48#64 40#64 32#64 24#64 a_4 hself_len).symm
  wp_x25519_call hMulC; norm_sf 1728
  wp_steps
  close_cells (s0.sp - 16#64) 16 2
  apply sepWP_unpeel_stack_bytes s0.sp 48 32 16 (hbs := hclamped_len)
  apply sepWP_unpeel_stack_bytes s0.sp 80 32 48 (hbs := hpub_len)
  wp_conv_pre => try rw [show s0.sp - 1808#64 = s0.sp - 80#64 - 1728#64 by bv_lin]
  apply sepWP_merge_stack_callee 1728 80
  generalize x25519 a_4 a_rest = out_res
  wp_done

/-- `<StaticSecret>::diffie_hellman` (`Blk17`, 13 insns, stack 1808). -/
theorem static_secret_diffie_hellman_ok : StaticSecretDiffieHellmanOk :=
  static_secret_diffie_hellman_ok_of montgomery_point_mul_clamped_ok

/-- Pure `x25519Ref` output-list bridge connecting byte-list `x25519` to `List.Vector` `x25519Ref`. -/
theorem x25519_eq_x25519Ref_toList (sec pub : List.Vector (BitVec 8) 32) :
    x25519 sec.toList pub.toList = (x25519Ref sec pub).toList :=
  rfl

end

end LibsignalBinary.Proofs.HookDischarge.CryptoX25519.DiffieHellmanProof
