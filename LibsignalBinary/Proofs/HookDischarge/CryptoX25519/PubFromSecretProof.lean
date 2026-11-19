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
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PubFromSecretMath
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.SliceBase
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Field51Base
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.BasepointTable
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.ToMontgomery

/-!
# RFC 7748 X25519 public-key-from-secret entrypoint proof

Machine-code proof for `x25519CliMultiLib` block `18` (`<PublicKey as From<&StaticSecret>>::from`)
and its `x25519Ref` list bridge:

- `public_key_from_static_secret_ok : PublicKeyFromStaticSecretOk` (`Blk18`, 17 insns, stack 1904)
- `x25519Pubkey_eq_x25519PubFromSecretRef_toList`: pure `List.Vector` output-list bridge
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PubFromSecretProof

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj ProofLib
open VerifiedLibraries.Common (natToLeBytes clampScalarBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedObjDefs (x25519CliMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedCodeBase (
  X25519CliPlacement x25519CliMpl x25519Caller_ok resolve_blk10 resolve_blk14)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref (
  x25519Pubkey x25519PubFromSecretRef)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PubFromSecretMath (
  edExtToMontgomeryU_mulBase_clamped)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.CommonBase (
  fe51_one fe51OneBytes ed25519_basepoint_table ed25519BasepointTableBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.InternalSpecs (
  fe51LimbsBoundedAt fe51Point4Bounded edExtOfBytes edExtToMontgomeryU edMulBase
  clampScalarBytes_length_of_eq32
  EdwardsPointMulBaseClampedOk EdwardsPointToMontgomeryOk PublicKeyFromStaticSecretOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.SliceBase (
  HasLenGe sepWP_split_stack_callee sepWP_merge_stack_callee
  sepWP_peel_stack_bytes sepWP_unpeel_stack_bytes
  sepWP_callee_shrink sepWP_callee_grow)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Field51Base (
  fe51LimbsBoundedAt_mono)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Field51Base
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.BasepointTable (
  edwards_point_mul_base_clamped_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.ToMontgomery (
  edwards_point_to_montgomery_ok)

arm64_proof_prelude

attribute [local irreducible] MultiPlacedLib.CodeLoaded

/-! ## 1. Block Fetch Generation (`Blk18`) & Private Stack Copy Helpers -/

open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedCodeBase (x25519CliMpl) in
gen_block_fetches x25519Cli 18 x25519CliMultiLib X25519CliPlacement 17 rebase rho sub

@[local simp, local arm64_norm, local wp_norm]
private theorem x25519CliPl18_rho_norm [X25519CliPlacement] (sym : String) :
    x25519CliPl18.ρ sym = x25519CliMultiLib.resolve x25519CliMpl sym := rfl

private theorem pk_write64_copy4_32_eq (dst src : List (BitVec 8))
    (hdst : dst.length = 32) (hsrc : src.length = 32) :
    ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 dst
      0 (ByteSlice.readLE src 0 8)) 8 (ByteSlice.readLE src 8 8))
      16 (ByteSlice.readLE src 16 8)) 24 (ByteSlice.readLE src 24 8) = src := by
  conv => lhs; arg 1; arg 1; arg 1; arg 1; rw [← ByteSlice.copySet_false dst src]
  rw [ByteSlice.write64_copySet_readLE _ src _ _ (by rw [hdst]; try decide),
      ByteSlice.write64_copySet_readLE _ src _ _ (by rw [hdst]; try decide),
      ByteSlice.write64_copySet_readLE _ src _ _ (by rw [hdst]; try decide),
      ByteSlice.write64_copySet_readLE _ src _ _ (by rw [hdst]; try decide)]
  apply ByteSlice.copySet_all (by omega)
  intro i hi; rw [hdst] at hi
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega

private theorem fe51Point4Bounded_52_to_53 {bs : List (BitVec 8)}
    (h : fe51Point4Bounded bs (2 ^ 52)) : fe51Point4Bounded bs (2 ^ 53) := by
  rcases h with ⟨hl, h0, h40, h80, h120⟩
  exact ⟨hl,
    fe51LimbsBoundedAt_mono h0 (b2 := 2 ^ 53),
    fe51LimbsBoundedAt_mono h40 (b2 := 2 ^ 53),
    fe51LimbsBoundedAt_mono h80 (b2 := 2 ^ 53),
    fe51LimbsBoundedAt_mono h120 (b2 := 2 ^ 53)⟩

/-! ## 2. Machine-Code Subroutine Contract (`Blk18`) -/

public section

/-- Conditional `<PublicKey as From<&StaticSecret>>::from` (`Blk18`, 17 insns, stack 1904) contract. -/
theorem public_key_from_static_secret_ok_of
    (hMBC : EdwardsPointMulBaseClampedOk) (hToM : EdwardsPointToMontgomeryOk) :
    PublicKeyFromStaticSecretOk := by
  intro _
  apply x25519Caller_ok x25519CliPC18 x25519CliPl18
  intro b _hb _hbase
  wp_init
  have hsec_len : a_rest.length = 32 := ‹a_rest.length = 32›
  have hcl_len : (clampScalarBytes a_rest).length = 32 :=
    clampScalarBytes_length_of_eq32 hsec_len
  apply sepWP_split_stack_callee 1680 224
  apply sepWP_peel_stack_bytes s0.sp 224 160 64; intro pt_init hpt_init
  apply sepWP_peel_stack_bytes s0.sp 64 32 32; intro sc_init hsc_init
  open_cells (s0.sp - 32#64) 32 4
  have : HasLenGe a_rest 32 := ⟨by omega⟩
  have : HasLenGe sc_init 32 := ⟨by omega⟩
  wp_cut_codeLoaded
  wp_steps
  wp_conv_pre => rw [pk_write64_copy4_32_eq sc_init a_rest hsc_init hsec_len]
  wp_x25519_call hMBC; norm_sf 1680
  have hres_b52 : fe51Point4Bounded w (2 ^ 52) := ‹_›
  have hres_b53 : fe51Point4Bounded w (2 ^ 53) := fe51Point4Bounded_52_to_53 hres_b52
  obtain ⟨hres_len, hw0, hw40, hw80, hw120⟩ := hres_b53
  unpack_fe51_at hw0; unpack_fe51_at hw40; unpack_fe51_at hw80; unpack_fe51_at hw120
  have hres_eq : edExtOfBytes w = edMulBase ed25519BasepointTableBytes (clampScalarBytes a_rest) := ‹_›
  apply sepWP_callee_shrink (s0.sp - 224#64) 1680 1392 288
  wp_cut_codeLoaded
  wp_steps
  wp_x25519_call hToM; clean_prev_sf; norm_sf 1392
  apply sepWP_callee_grow (s0.sp - 224#64) 1680 1392 288
  wp_conv_pre => rw [hres_eq, edExtToMontgomeryU_mulBase_clamped hsec_len]
  wp_steps
  close_cells (s0.sp - 32#64) 32 4
  apply sepWP_unpeel_stack_bytes s0.sp 64 32 32 (hbs := hcl_len)
  apply sepWP_unpeel_stack_bytes s0.sp 224 160 64 (hbs := hres_len)
  apply sepWP_merge_stack_callee 1680 224
  generalize x25519Pubkey a_rest = pub_res
  wp_done

/-- `<PublicKey as From<&StaticSecret>>::from` (`Blk18`, 17 insns, stack 1904). -/
theorem public_key_from_static_secret_ok : PublicKeyFromStaticSecretOk :=
  public_key_from_static_secret_ok_of edwards_point_mul_base_clamped_ok edwards_point_to_montgomery_ok

/-- Pure `x25519PubFromSecretRef` output-list bridge connecting byte-list `x25519Pubkey`
    to `List.Vector` `x25519PubFromSecretRef`. -/
theorem x25519Pubkey_eq_x25519PubFromSecretRef_toList (sec : List.Vector (BitVec 8) 32) :
    x25519Pubkey sec.toList = (x25519PubFromSecretRef sec).toList :=
  rfl

end

end LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PubFromSecretProof
