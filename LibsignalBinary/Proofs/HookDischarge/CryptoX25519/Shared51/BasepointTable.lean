/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.InternalSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.BasepointTable1 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedObjDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedCodeBase
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.RoTables
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.SliceBase
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Field51Base
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Field51
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.ScalarRadix16
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.CurveModels
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Edwards basepoint table multiplication machine-code proofs

Verifies `x25519CliMultiLib` blocks `13` (`mul_base`) and `14` (`mul_base_clamped`), and
re-exports block `06` from `Shared51.BasepointTable1`.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.BasepointTable

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj ProofLib
open VerifiedLibraries.Common (p25519 fpMul EdExtPoint edExtZero clampScalarBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedObjDefs (x25519CliMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedCodeBase (
  X25519CliPlacement x25519CliMpl X25519Base x25519Caller_ok
  resolve_blk01 resolve_blk03 resolve_blk06 resolve_blk08 resolve_blk09 resolve_blk13
  resolve_ro00 resolve_ro02)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.CommonBase (
  fe51Val fe51ValOfBytes fe51_one fe51OneBytes ed25519_basepoint_table ed25519BasepointTableBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.RoTables (
  fe51OneBytes_length fe51One_readLE_0 fe51One_readLE_8 fe51One_readLE_16 fe51One_readLE_24
  ed25519BasepointTableBytes_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.InternalSpecs (
  fe51LimbsBounded scalarRadix16Digits scalarRadix16Digits_length
  fe51LimbsBoundedAt fe51ValAt fe51Point4Bounded edExtOfBytes
  edAddAffineNiels edDouble4
  fe51AffineNielsBoundedAt fe51LookupTable8Bounded edSelectAffineNiels
  fe51BasepointTable32Bounded fe51BasepointTable32Bounded_mono
  ed25519BasepointTableBytes_bounded
  clampScalarBytes_length_of_eq32 clampScalarBytes_getD31_le_127
  edMulBaseStep edMulBaseStepAt edMulBaseLoopWith edMulBaseLoop edMulBase
  Fe51MulOk ScalarAsRadix16Ok LookupTableAffineNielsSelectOk
  EdwardsPointAddAffineNielsOk EdwardsPointMulByPow2_4Ok
  EdwardsBasepointTableMulBaseOk EdwardsPointMulBaseClampedOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.SliceBase (
  HasLenGe le_length_of_hasLenGe sub_ofNat64_add write64_length_eq
  readLE_write64_self' readLE_write64_ne readLE_append_left readLE_append_right
  pointsToBytesRO_take_drop fold_fe51ValOfBytes edAsExtended_of_append4
  fe51_mul_post_props sepWP_abstract_bytes sepWP_peel_stack_bytes sepWP_unpeel_stack_bytes
  sepWP_split_stack_callee sepWP_merge_stack_callee)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Field51Base (fe51LimbsBoundedAt_mono)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Field51Base
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Field51 (fe51_mul_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.ScalarRadix16 (scalar_as_radix_16_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.CurveModels (
  edwards_point_add_affine_niels_ok edwards_point_mul_by_pow_2_4_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.BasepointTable1 (
  lookup_table_affine_niels_select_ok_of lookup_table_affine_niels_select_ok)

open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedCodeBase (x25519CliMpl) in
gen_block_fetches x25519Cli 13 x25519CliMultiLib X25519CliPlacement 167 rebase rho sub

@[local simp, local arm64_norm, local wp_norm]
private theorem x25519CliPl13_rho_norm [X25519CliPlacement] (sym : String) :
    x25519CliPl13.ρ sym = x25519CliMultiLib.resolve x25519CliMpl sym := rfl

open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedCodeBase (x25519CliMpl) in
gen_block_fetches x25519Cli 14 x25519CliMultiLib X25519CliPlacement 11 rebase rho sub

@[local simp, local arm64_norm, local wp_norm]
private theorem x25519CliPl14_rho_norm [X25519CliPlacement] (sym : String) :
    x25519CliPl14.ρ sym = x25519CliMultiLib.resolve x25519CliMpl sym := rfl

private theorem pointsToBytesRO_split3 (a : BitVec 64) (bs : List (BitVec 8)) (off len : Nat)
    (h : off + len ≤ bs.length) :
    (a ↦ᵣ bs) =
      ((a + BitVec.ofNat 64 off) ↦ᵣ ProofLib.ByteSlice.slice bs off len) ∗
      ((a ↦ᵣ bs.take off) ∗ ((a + BitVec.ofNat 64 (off + len)) ↦ᵣ bs.drop (off + len))) := by
  rw [pointsToBytesRO_take_drop a off bs (by omega),
      pointsToBytesRO_take_drop (a + BitVec.ofNat 64 off) len (bs.drop off) (by simp; omega),
      List.drop_drop]
  have hadd : a + BitVec.ofNat 64 off + BitVec.ofNat 64 len = a + BitVec.ofNat 64 (off + len) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [hadd]
  unfold ProofLib.ByteSlice.slice
  sep_ac_rfl

private theorem mul_base_init_post (dst : List (BitVec 8)) (hdst : dst.length = 160) :
    let buf := ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
        dst 32 0#64) 72 0#64) 120 0#64) 128 0#64) 136 0#64) 144 0#64)
        40 (ByteSlice.readLE fe51OneBytes 0 8)) 48 (ByteSlice.readLE fe51OneBytes 8 8)) 0 0#64) 8 0#64) 16 0#64) 24 0#64)
        56 (ByteSlice.readLE fe51OneBytes 16 8)) 64 (ByteSlice.readLE fe51OneBytes 24 8)) 112 0#64)
        80 (ByteSlice.readLE fe51OneBytes 0 8)) 88 (ByteSlice.readLE fe51OneBytes 8 8))
        96 (ByteSlice.readLE fe51OneBytes 16 8)) 104 (ByteSlice.readLE fe51OneBytes 24 8)) 152 0#64
    fe51Point4Bounded buf (2 ^ 52) ∧ edExtOfBytes buf = edExtZero := by
  have : HasLenGe dst 160 := ⟨by omega⟩
  unfold fe51Point4Bounded fe51LimbsBoundedAt edExtOfBytes edExtZero
  simp (disch := decide) only [fe51ValAt, ↓readLE_write64_self', ↓readLE_write64_ne,
    write64_length_eq, hdst, fe51One_readLE_0, fe51One_readLE_8, fe51One_readLE_16, fe51One_readLE_24]
  decide +kernel

private theorem copy160_point4_post (dst src : List (BitVec 8)) (P : EdExtPoint) (bound : Nat)
    (hdst : dst.length = 160) (hsrc_b : fe51Point4Bounded src bound) (hsrc_v : edExtOfBytes src = P) :
    let buf := ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
        dst 96 (ByteSlice.readLE src 96 8)) 104 (ByteSlice.readLE src 104 8)) 112 (ByteSlice.readLE src 112 8)) 120 (ByteSlice.readLE src 120 8))
        128 (ByteSlice.readLE src 128 8)) 136 (ByteSlice.readLE src 136 8)) 144 (ByteSlice.readLE src 144 8)) 152 (ByteSlice.readLE src 152 8))
        32 (ByteSlice.readLE src 32 8)) 40 (ByteSlice.readLE src 40 8)) 48 (ByteSlice.readLE src 48 8)) 56 (ByteSlice.readLE src 56 8))
        64 (ByteSlice.readLE src 64 8)) 72 (ByteSlice.readLE src 72 8)) 80 (ByteSlice.readLE src 80 8)) 88 (ByteSlice.readLE src 88 8))
        0 (ByteSlice.readLE src 0 8)) 8 (ByteSlice.readLE src 8 8)) 16 (ByteSlice.readLE src 16 8)) 24 (ByteSlice.readLE src 24 8)
    fe51Point4Bounded buf bound ∧ edExtOfBytes buf = P := by
  have : HasLenGe dst 160 := ⟨by omega⟩; obtain ⟨_, h0, h40, h80, h120⟩ := hsrc_b
  unfold fe51Point4Bounded fe51LimbsBoundedAt edExtOfBytes
  simp (disch := decide) only [fe51ValAt, ↓readLE_write64_self', ↓readLE_write64_ne, write64_length_eq, hdst]
  exact ⟨⟨rfl, h0, h40, h80, h120⟩, hsrc_v⟩

private theorem sepWP_resize_callee (sp0 : BitVec 64) (low k : Nat)
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hsum : low + k = 912 := by decide) (hf : Full = memRegion (sp0 - 1680#64) 912 ∗ P := by sep_frame)
    (hnext : SepWP prog target_pc s ((memRegion (sp0 - 768#64 - BitVec.ofNat 64 k) k ∗ stackAt (sp0 - 768#64 - BitVec.ofNat 64 k) low) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have haddr : sp0 - 1680#64 = (sp0 - 768#64) - 912#64 := by rw [BitVec.sub_sub]; rfl
  rw [hf, haddr]; change SepWP prog target_pc s (stackAt (sp0 - 768#64) 912 ∗ P) post oom
  rw [← hsum, stackAt_region (sp0 - 768#64) low k (by omega), sepConj_comm (stackAt _ _) (memRegion _ _)]; exact hnext

private theorem sepWP_unresize_callee (sp0 : BitVec 64) (low k : Nat)
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hsum : low + k = 912 := by decide)
    (hf : Full = (memRegion (sp0 - 768#64 - BitVec.ofNat 64 k) k ∗ stackAt (sp0 - 768#64 - BitVec.ofNat 64 k) low) ∗ P := by sep_frame)
    (hnext : SepWP prog target_pc s (memRegion (sp0 - 1680#64) 912 ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have haddr : (sp0 - 768#64) - 912#64 = sp0 - 1680#64 := by rw [BitVec.sub_sub]; rfl
  rw [hf, sepConj_comm (memRegion _ _) (stackAt _ _), ← stackAt_region (sp0 - 768#64) low k (by omega), hsum]
  change SepWP prog target_pc s (memRegion ((sp0 - 768#64) - 912#64) 912 ∗ P) post oom; rw [haddr]; exact hnext

private theorem sepWP_split_ro_slice (table : BitVec 64) (table_bs : List (BitVec 8)) (i : Nat)
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hi : i < 32) (htab : table_bs.length = 30720) (hf : Full = (table ↦ᵣ table_bs) ∗ P := by sep_frame)
    (hnext : SepWP prog target_pc s ((((table + BitVec.ofNat 64 (960 * i)) ↦ᵣ ProofLib.ByteSlice.slice table_bs (960 * i) 960) ∗
      ((table ↦ᵣ table_bs.take (960 * i)) ∗ ((table + BitVec.ofNat 64 (960 * i + 960)) ↦ᵣ table_bs.drop (960 * i + 960)))) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  rw [hf, pointsToBytesRO_split3 table table_bs (960 * i) 960 (by omega)]; exact hnext

private theorem sepWP_unsplit_ro_slice (table : BitVec 64) (table_bs : List (BitVec 8)) (i : Nat)
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hi : i < 32) (htab : table_bs.length = 30720)
    (hf : Full = (((table + BitVec.ofNat 64 (960 * i)) ↦ᵣ ProofLib.ByteSlice.slice table_bs (960 * i) 960) ∗
       ((table ↦ᵣ table_bs.take (960 * i)) ∗ ((table + BitVec.ofNat 64 (960 * i + 960)) ↦ᵣ table_bs.drop (960 * i + 960)))) ∗ P := by sep_frame)
    (hnext : SepWP prog target_pc s ((table ↦ᵣ table_bs) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  rw [hf, ← pointsToBytesRO_split3 table table_bs (960 * i) 960 (by omega)]; exact hnext

private theorem sepWP_split4_completed_376 (sp : BitVec 64) (C : EdExtPoint) {bs : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = ((sp - 376#64) ↦ₛ bs) ∗ P := by sep_frame) (hbs : bs.length = 160 := by assumption)
    (h0 : fe51LimbsBoundedAt bs 0 (2 ^ 52) := by assumption) (h40 : fe51LimbsBoundedAt bs 40 (2 ^ 53) := by assumption)
    (h80 : fe51LimbsBoundedAt bs 80 (2 ^ 54) := by assumption) (h120 : fe51LimbsBoundedAt bs 120 (2 ^ 52) := by assumption)
    (hval : edExtOfBytes bs = C := by assumption)
    (hnext : ∀ b0 b1 b2 b3 : List (BitVec 8),
      b0.length = 40 → b1.length = 40 → b2.length = 40 → b3.length = 40 →
      fe51LimbsBounded b0 (2 ^ 54) → fe51LimbsBounded b1 (2 ^ 54) → fe51LimbsBounded b2 (2 ^ 54) → fe51LimbsBounded b3 (2 ^ 54) →
      fe51ValOfBytes b0 % p25519 = C.X → fe51ValOfBytes b1 % p25519 = C.Y → fe51ValOfBytes b2 % p25519 = C.Z → fe51ValOfBytes b3 % p25519 = C.T →
      SepWP prog target_pc s ((((sp - 376#64) ↦ₛ b0) ∗ ((sp - 336#64) ↦ₛ b1) ∗ ((sp - 296#64) ↦ₛ b2) ∗ ((sp - 256#64) ↦ₛ b3)) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  let b0 := bs.take 40; let d1 := bs.drop 40; have hd1 : d1.length = 120 := by simp [d1, hbs]
  let b1 := d1.take 40; let d2 := d1.drop 40; have hd2 : d2.length = 80 := by simp [d2, hd1]
  let b2 := d2.take 40; let b3 := d2.drop 40
  have hb0_l : b0.length = 40 := by simp [b0, hbs]
  have hb1_l : b1.length = 40 := by simp [b1, hd1]
  have hb2_l : b2.length = 40 := by simp [b2, hd2]
  have hb3_l : b3.length = 40 := by simp [b3, hd2]
  have hs0 : ((sp - 376#64) ↦ₛ bs) = ((sp - 376#64) ↦ₛ b0) ∗ ((sp - 336#64) ↦ₛ d1) := by
    conv => lhs; rw [← List.take_append_drop 40 bs]
    rw [pointsToBytes_append, List.length_take, hbs, Nat.min_eq_left (by decide), sub_ofNat64_add sp 376 40]
  have hs1 : ((sp - 336#64) ↦ₛ d1) = ((sp - 336#64) ↦ₛ b1) ∗ ((sp - 296#64) ↦ₛ d2) := by
    conv => lhs; rw [← List.take_append_drop 40 d1]
    rw [pointsToBytes_append, List.length_take, hd1, Nat.min_eq_left (by decide), sub_ofNat64_add sp 336 40]
  have hs2 : ((sp - 296#64) ↦ₛ d2) = ((sp - 296#64) ↦ₛ b2) ∗ ((sp - 256#64) ↦ₛ b3) := by
    conv => lhs; rw [← List.take_append_drop 40 d2]
    rw [pointsToBytes_append, List.length_take, hd2, Nat.min_eq_left (by decide), sub_ofNat64_add sp 296 40]
  have hbs_eq : bs = b0 ++ (b1 ++ (b2 ++ b3)) := by
    have e0 : b0 ++ d1 = bs := List.take_append_drop 40 bs; have e1 : b1 ++ d2 = d1 := List.take_append_drop 40 d1
    have e2 : b2 ++ b3 = d2 := List.take_append_drop 40 d2; rw [e2, e1, e0]
  have hr0 (off : Nat) (ho : off + 8 ≤ 40) : ByteSlice.readLE bs off 8 = ByteSlice.readLE b0 off 8 := by
    rw [hbs_eq]; exact readLE_append_left b0 _ off 8 (by omega)
  have hr1 (off : Nat) (ho1 : 40 ≤ off) (ho2 : off + 8 ≤ 80) : ByteSlice.readLE bs off 8 = ByteSlice.readLE b1 (off - 40) 8 := by
    rw [hbs_eq, readLE_append_right b0 _ off 8 (by omega), hb0_l, readLE_append_left b1 _ (off - 40) 8 (by omega)]
  have hr2 (off : Nat) (ho1 : 80 ≤ off) (ho2 : off + 8 ≤ 120) : ByteSlice.readLE bs off 8 = ByteSlice.readLE b2 (off - 80) 8 := by
    rw [hbs_eq, readLE_append_right b0 _ off 8 (by omega), hb0_l, readLE_append_right b1 _ (off - 40) 8 (by omega),
        hb1_l, show off - 40 - 40 = off - 80 by omega, readLE_append_left b2 _ (off - 80) 8 (by omega)]
  have hr3 (off : Nat) (ho1 : 120 ≤ off) : ByteSlice.readLE bs off 8 = ByteSlice.readLE b3 (off - 120) 8 := by
    rw [hbs_eq, readLE_append_right b0 _ off 8 (by omega), hb0_l, readLE_append_right b1 _ (off - 40) 8 (by omega),
        hb1_l, readLE_append_right b2 _ (off - 40 - 40) 8 (by omega), hb2_l, show off - 40 - 40 - 40 = off - 120 by omega]
  have h0' := fe51LimbsBoundedAt_mono h0 (b2 := 2 ^ 54); have h40' := fe51LimbsBoundedAt_mono h40 (b2 := 2 ^ 54)
  have h120' := fe51LimbsBoundedAt_mono h120 (b2 := 2 ^ 54); unfold fe51LimbsBoundedAt at h0' h40' h80 h120'
  simp (disch := omega) only [hr0, hr1, hr2, hr3, Nat.reduceAdd, Nat.reduceSub] at h0' h40' h80 h120'
  have hval' : edExtOfBytes bs = ⟨fe51ValOfBytes b0 % p25519, fe51ValOfBytes b1 % p25519,
      fe51ValOfBytes b2 % p25519, fe51ValOfBytes b3 % p25519⟩ := by
    unfold edExtOfBytes fe51ValAt
    simp (disch := omega) only [hr0, hr1, hr2, hr3, Nat.reduceAdd, Nat.reduceSub,
      fold_fe51ValOfBytes b0, fold_fe51ValOfBytes b1, fold_fe51ValOfBytes b2, fold_fe51ValOfBytes b3]
  rw [hval] at hval'; rw [hf, hs0, hs1, hs2]
  exact hnext b0 b1 b2 b3 hb0_l hb1_l hb2_l hb3_l ⟨hb0_l, h0'⟩ ⟨hb1_l, h40'⟩ ⟨hb2_l, h80⟩ ⟨hb3_l, h120'⟩
    (congrArg EdExtPoint.X hval').symm (congrArg EdExtPoint.Y hval').symm
    (congrArg EdExtPoint.Z hval').symm (congrArg EdExtPoint.T hval').symm

private theorem sepWP_merge4_stack_376 (sp : BitVec 64) {b0 b1 b2 b3 : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (((sp - 376#64) ↦ₛ b0) ∗ ((sp - 336#64) ↦ₛ b1) ∗ ((sp - 296#64) ↦ₛ b2) ∗ ((sp - 256#64) ↦ₛ b3)) ∗ P := by sep_frame)
    (h0 : b0.length = 40 := by assumption) (h1 : b1.length = 40 := by assumption)
    (h2 : b2.length = 40 := by assumption) (h3 : b3.length = 40 := by assumption)
    (hnext : ∀ b160 : List (BitVec 8), b160.length = 160 → SepWP prog target_pc s (((sp - 376#64) ↦ₛ b160) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have ha2 : sp - 296#64 + BitVec.ofNat 64 b2.length = sp - 256#64 := by rw [h2]; exact sub_ofNat64_add sp 296 40
  have ha1 : sp - 336#64 + BitVec.ofNat 64 b1.length = sp - 296#64 := by rw [h1]; exact sub_ofNat64_add sp 336 40
  have ha0' : sp - 376#64 + BitVec.ofNat 64 b0.length = sp - 336#64 := by rw [h0]; exact sub_ofNat64_add sp 376 40
  have hm : ((sp - 376#64) ↦ₛ (b0 ++ (b1 ++ (b2 ++ b3)))) =
      ((sp - 376#64) ↦ₛ b0) ∗ ((sp - 336#64) ↦ₛ b1) ∗ ((sp - 296#64) ↦ₛ b2) ∗ ((sp - 256#64) ↦ₛ b3) := by
    rw [pointsToBytes_append, ha0', pointsToBytes_append, ha1, pointsToBytes_append, ha2]
  rw [hf, ← hm]; exact hnext (b0 ++ (b1 ++ (b2 ++ b3))) (by simp [List.length_append, h0, h1, h2, h3])

private theorem sepWP_split4_stack_536 (sp : BitVec 64) {bs : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = ((sp - 536#64) ↦ₛ bs) ∗ P := by sep_frame) (hbs : bs.length = 160 := by assumption)
    (hnext : ∀ b0 b1 b2 b3 : List (BitVec 8), b0.length = 40 → b1.length = 40 → b2.length = 40 → b3.length = 40 →
      SepWP prog target_pc s ((((sp - 536#64) ↦ₛ b0) ∗ ((sp - 496#64) ↦ₛ b1) ∗ ((sp - 456#64) ↦ₛ b2) ∗ ((sp - 416#64) ↦ₛ b3)) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  let d1 := bs.drop 40; have hd1 : d1.length = 120 := by simp [d1, hbs]
  let d2 := d1.drop 40; have hd2 : d2.length = 80 := by simp [d2, hd1]
  have hs0 : ((sp - 536#64) ↦ₛ bs) = ((sp - 536#64) ↦ₛ bs.take 40) ∗ ((sp - 496#64) ↦ₛ d1) := by
    conv => lhs; rw [← List.take_append_drop 40 bs]
    rw [pointsToBytes_append, List.length_take, hbs, Nat.min_eq_left (by decide), sub_ofNat64_add sp 536 40]
  have hs1 : ((sp - 496#64) ↦ₛ d1) = ((sp - 496#64) ↦ₛ d1.take 40) ∗ ((sp - 456#64) ↦ₛ d2) := by
    conv => lhs; rw [← List.take_append_drop 40 d1]
    rw [pointsToBytes_append, List.length_take, hd1, Nat.min_eq_left (by decide), sub_ofNat64_add sp 496 40]
  have hs2 : ((sp - 456#64) ↦ₛ d2) = ((sp - 456#64) ↦ₛ d2.take 40) ∗ ((sp - 416#64) ↦ₛ d2.drop 40) := by
    conv => lhs; rw [← List.take_append_drop 40 d2]
    rw [pointsToBytes_append, List.length_take, hd2, Nat.min_eq_left (by decide), sub_ofNat64_add sp 456 40]
  rw [hf, hs0, hs1, hs2]
  exact hnext (bs.take 40) (d1.take 40) (d2.take 40) (d2.drop 40) (by simp [hbs]) (by simp [hd1]) (by simp [hd2]) (by simp [hd2])

private theorem sepWP_merge4_stack_536 (sp : BitVec 64) {b0 b1 b2 b3 : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} (Q : List (BitVec 8) → Prop)
    (hf : Full = (((sp - 536#64) ↦ₛ b0) ∗ ((sp - 496#64) ↦ₛ b1) ∗ ((sp - 456#64) ↦ₛ b2) ∗ ((sp - 416#64) ↦ₛ b3)) ∗ P := by sep_frame)
    (h0 : b0.length = 40 := by assumption) (h1 : b1.length = 40 := by assumption) (h2 : b2.length = 40 := by assumption)
    (hQ : Q (b0 ++ (b1 ++ (b2 ++ b3))))
    (hnext : ∀ res_bs : List (BitVec 8), Q res_bs → SepWP prog target_pc s (((sp - 536#64) ↦ₛ res_bs) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have ha2 : sp - 456#64 + BitVec.ofNat 64 b2.length = sp - 416#64 := by rw [h2]; exact sub_ofNat64_add sp 456 40
  have ha1 : sp - 496#64 + BitVec.ofNat 64 b1.length = sp - 456#64 := by rw [h1]; exact sub_ofNat64_add sp 496 40
  have ha0 : sp - 536#64 + BitVec.ofNat 64 b0.length = sp - 496#64 := by rw [h0]; exact sub_ofNat64_add sp 536 40
  have hm : ((sp - 536#64) ↦ₛ (b0 ++ (b1 ++ (b2 ++ b3)))) =
      ((sp - 536#64) ↦ₛ b0) ∗ ((sp - 496#64) ↦ₛ b1) ∗ ((sp - 456#64) ↦ₛ b2) ∗ ((sp - 416#64) ↦ₛ b3) := by
    rw [pointsToBytes_append, ha0, pointsToBytes_append, ha1, pointsToBytes_append, ha2]
  rw [hf, ← hm]; exact hnext (b0 ++ (b1 ++ (b2 ++ b3))) hQ

private def mulBaseLoopPre (sp0 table : BitVec 64)
    (table_bs digits acc_bs ext_bs comp_bs niels_bs : List (BitVec 8)) (F : SepProp) : SepProp :=
  memRegion (sp0 - 1680#64) 912 ∗ (table ↦ᵣ table_bs) ∗ ((sp0 - 768#64) ↦ₛ digits) ∗
  ((sp0 - 704#64) ↦ₛ acc_bs) ∗ ((sp0 - 536#64) ↦ₛ ext_bs) ∗ ((sp0 - 376#64) ↦ₛ comp_bs) ∗ ((sp0 - 216#64) ↦ₛ niels_bs) ∗ F

private theorem sepWP_fold_mulBaseLoopPre (sp0 table : BitVec 64)
    {table_bs digits acc_bs ext_bs comp_bs niels_bs : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (memRegion (sp0 - 1680#64) 912 ∗ (table ↦ᵣ table_bs) ∗ ((sp0 - 768#64) ↦ₛ digits) ∗
      ((sp0 - 704#64) ↦ₛ acc_bs) ∗ ((sp0 - 536#64) ↦ₛ ext_bs) ∗ ((sp0 - 376#64) ↦ₛ comp_bs) ∗ ((sp0 - 216#64) ↦ₛ niels_bs)) ∗ F := by sep_frame)
    (hnext : SepWP prog target_pc s (mulBaseLoopPre sp0 table table_bs digits acc_bs ext_bs comp_bs niels_bs F) post oom) :
    SepWP prog target_pc s Full post oom := by
  have hm : mulBaseLoopPre sp0 table table_bs digits acc_bs ext_bs comp_bs niels_bs F =
      (memRegion (sp0 - 1680#64) 912 ∗ (table ↦ᵣ table_bs) ∗ ((sp0 - 768#64) ↦ₛ digits) ∗
       ((sp0 - 704#64) ↦ₛ acc_bs) ∗ ((sp0 - 536#64) ↦ₛ ext_bs) ∗ ((sp0 - 376#64) ↦ₛ comp_bs) ∗ ((sp0 - 216#64) ↦ₛ niels_bs)) ∗ F := by
    unfold mulBaseLoopPre; sep_ac_rfl
  rw [hf, ← hm]; exact hnext

private theorem even_getLsbD_0 {i : Nat} (hi : i < 32) : (BitVec.ofNat 64 (2 * i)).getLsbD 0 = false :=
  (by decide : ∀ k : Fin 32, (BitVec.ofNat 64 (2 * k.val)).getLsbD 0 = false) ⟨i, hi⟩
private theorem odd_getLsbD_0 {i : Nat} (hi : i < 32) : (BitVec.ofNat 64 (2 * i + 1)).getLsbD 0 = true :=
  (by decide : ∀ k : Fin 32, (BitVec.ofNat 64 (2 * k.val + 1)).getLsbD 0 = true) ⟨i, hi⟩
private theorem ofNat_2i_add_1 {i : Nat} (hi : i < 32) : BitVec.ofNat 64 (2 * i) + 1#64 = BitVec.ofNat 64 (2 * i + 1) :=
  (by decide : ∀ k : Fin 32, BitVec.ofNat 64 (2 * k.val) + 1#64 = BitVec.ofNat 64 (2 * k.val + 1)) ⟨i, hi⟩
private theorem ofNat_2i1_add_1 {i : Nat} (hi : i < 32) : BitVec.ofNat 64 (2 * i + 1) + 1#64 = BitVec.ofNat 64 (2 * (i + 1)) :=
  (by decide : ∀ k : Fin 32, BitVec.ofNat 64 (2 * k.val + 1) + 1#64 = BitVec.ofNat 64 (2 * (k.val + 1))) ⟨i, hi⟩
private theorem ule_64_2i1 {i : Nat} (hi : i < 32) : (64#64).ule (BitVec.ofNat 64 (2 * i + 1)) = false :=
  (by decide : ∀ k : Fin 32, (64#64).ule (BitVec.ofNat 64 (2 * k.val + 1)) = false) ⟨i, hi⟩
private theorem ule_64_2i {i : Nat} (hi : i < 32) : (64#64).ule (BitVec.ofNat 64 (2 * i)) = false :=
  (by decide : ∀ k : Fin 32, (64#64).ule (BitVec.ofNat 64 (2 * k.val)) = false) ⟨i, hi⟩
private theorem lsr_2i1 {i : Nat} (hi : i < 32) : BitVec.ofNat 64 (2 * i + 1) >>> 1 = BitVec.ofNat 64 i :=
  (by decide : ∀ k : Fin 32, BitVec.ofNat 64 (2 * k.val + 1) >>> 1 = BitVec.ofNat 64 k.val) ⟨i, hi⟩
private theorem lsr_2i {i : Nat} (hi : i < 32) : BitVec.ofNat 64 (2 * i) >>> 1 = BitVec.ofNat 64 i :=
  (by decide : ∀ k : Fin 32, BitVec.ofNat 64 (2 * k.val) >>> 1 = BitVec.ofNat 64 k.val) ⟨i, hi⟩
private theorem mul_960_ofNat {i : Nat} (hi : i < 32) : BitVec.ofNat 64 i * 960#64 = BitVec.ofNat 64 (960 * i) :=
  (by decide : ∀ k : Fin 32, BitVec.ofNat 64 k.val * 960#64 = BitVec.ofNat 64 (960 * k.val)) ⟨i, hi⟩

private theorem pc_odd_end (b : BitVec 64) {i : Nat} (hi : i < 32) :
    (if (BitVec.ofNat 64 (2 * i + 1) + 1#64 != 64#64) = true then b + 152#64 else b + 316#64) =
      if i == 31 then b + 316#64 else b + 152#64 := by
  have h : (BitVec.ofNat 64 (2 * i + 1) + 1#64 != 64#64) = !(i == 31) :=
    (by decide : ∀ k : Fin 32, (BitVec.ofNat 64 (2 * k.val + 1) + 1#64 != 64#64) = !(k.val == 31)) ⟨i, hi⟩
  rw [h]; cases (i == 31) <;> simp

private theorem pc_even_end (b : BitVec 64) {i : Nat} (hi : i < 32) :
    (if (BitVec.ofNat 64 (2 * i + 1) + 1#64 == 64#64) = true then b + 580#64 else b + 416#64) =
      if i == 31 then b + 580#64 else b + 416#64 := by
  have h : (BitVec.ofNat 64 (2 * i + 1) + 1#64 == 64#64) = (i == 31) :=
    (by decide : ∀ k : Fin 32, (BitVec.ofNat 64 (2 * k.val + 1) + 1#64 == 64#64) = (k.val == 31)) ⟨i, hi⟩
  rw [h]

private structure MulBaseLoopRegs [X25519CliPlacement]
    (s0 s : State) (out table r22 r24 r26 pc_val x23_val : BitVec 64) : Prop where
  hpc : s.pc = pc_val
  hrun : s.status = .Running
  hsp : s.sp = s0.sp - 768#64
  hx19 : s.readReg64 (Reg.gpr 19#5) = out
  hx20 : s.readReg64 (Reg.gpr 20#5) = table
  hx21 : s.readReg64 (Reg.gpr 21#5) = s0.sp - 536#64
  hx22 : s.readReg64 (Reg.gpr 22#5) = r22
  hx23 : s.readReg64 (Reg.gpr 23#5) = x23_val
  hx24 : s.readReg64 (Reg.gpr 24#5) = r24
  hx25 : s.readReg64 (Reg.gpr 25#5) = 960#64
  hx26 : s.readReg64 (Reg.gpr 26#5) = r26
  hx27 : s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5)
  hx28 : s.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5)
  hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64
  hvregs : calleeSavedVRegs s = calleeSavedVRegs s0
  hcl : x25519CliMultiLib.CodeLoaded x25519CliMpl s.mem

private abbrev MulBaseOddRegs [X25519CliPlacement]
    (s0 s : State) (out table pc_val x23_val : BitVec 64) : Prop :=
  MulBaseLoopRegs s0 s out table (s0.sp - 768#64) (s0.sp - 376#64) (s0.readReg64 (Reg.gpr 26#5)) pc_val x23_val

private abbrev MulBaseEvenRegs [X25519CliPlacement]
    (s0 s : State) (out table pc_val x23_val : BitVec 64) : Prop :=
  MulBaseLoopRegs s0 s out table (s0.sp - 376#64) (s0.sp - 536#64) (s0.sp - 768#64) pc_val x23_val

set_option maxHeartbeats 800000 in
attribute [local irreducible] fe51LookupTable8Bounded in
attribute [local wp_norm] ByteSlice.pack64_eq_readLE_8 in
private theorem mul_base_odd_iter [X25519CliPlacement]
    (b : BitVec 64) (_hb : X25519Base x25519CliPl13 b) (hbase : x25519CliPl13.base = b)
    (hSelect : LookupTableAffineNielsSelectOk) (hAdd : EdwardsPointAddAffineNielsOk) (hMul : Fe51MulOk)
    (i : Nat) (hi : i < 32) (s0 s : State) (target_pc out table : BitVec 64)
    (table_bs digits acc_bs ext_bs comp_bs niels_bs : List (BitVec 8))
    (acc : EdExtPoint) (F : SepProp) (post : State → SepProp → Prop) {oom : State → SepProp}
    (hsp0_align : s0.spAligned = true)
    (hregs : MulBaseOddRegs s0 s out table (b + 152#64) (BitVec.ofNat 64 (2 * i)))
    (htab_len : table_bs.length = 30720)
    (htab_bnd : ∀ j < 32, fe51LookupTable8Bounded (ProofLib.ByteSlice.slice table_bs (960 * j) 960) (2 ^ 53))
    (hdigits_len : digits.length = 64) (hacc_b : fe51Point4Bounded acc_bs (2 ^ 52)) (hacc_v : edExtOfBytes acc_bs = acc)
    (hext_len : ext_bs.length = 160) (hcomp_len : comp_bs.length = 160) (hniels_len : niels_bs.length = 120)
    (hnext : ∀ (sf' : State) (acc' ext' comp' niels' : List (BitVec 8)),
      MulBaseOddRegs s0 sf' out table (if i == 31 then b + 316#64 else b + 152#64) (BitVec.ofNat 64 (2 * (i + 1))) →
      fe51Point4Bounded acc' (2 ^ 52) → edExtOfBytes acc' = edMulBaseStep table_bs i (digits.getD (2 * i + 1) 0#8) acc →
      ext'.length = 160 → comp'.length = 160 → niels'.length = 120 →
      SepWP (x25519CliPC13.rebase b (fun _ => none)) target_pc sf' (mulBaseLoopPre s0.sp table table_bs digits acc' ext' comp' niels' F) post oom) :
    SepWP (x25519CliPC13.rebase b (fun _ => none)) target_pc s
      (mulBaseLoopPre s0.sp table table_bs digits acc_bs ext_bs comp_bs niels_bs F) post oom := by
  rcases hregs with ⟨hpc, hrun, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29, hvregs, hcl⟩
  unfold mulBaseLoopPre
  wp_sym_steps 1; simp only [even_getLsbD_0 hi, beq_self_eq_true, ↓ite_true]
  wp_sym_steps 3; simp only [ofNat_2i_add_1 hi]
  wp_sym_steps 4; simp only [ule_64_2i1 hi, Bool.false_eq_true, ↓ite_false]
  wp_sym_steps 3; simp only [lsr_2i1 hi, mul_960_ofNat hi]
  apply sepWP_resize_callee s0.sp 720 192; apply sepWP_split_ro_slice table table_bs i hi htab_len
  have htab_i : fe51LookupTable8Bounded (ProofLib.ByteSlice.slice table_bs (960 * i) 960) 9007199254740992 := htab_bnd i hi
  wp_steps; wp_x25519_call hSelect; clean_prev_sf
  apply sepWP_unsplit_ro_slice table table_bs i hi htab_len; apply sepWP_unresize_callee s0.sp 720 192
  have hniels_w_len : w.length = 120 := by assumption
  obtain ⟨hsel_0, hsel_40, hsel_80⟩ : fe51AffineNielsBoundedAt w 0 (2 ^ 53) := by assumption
  have hsel_val : (fe51ValAt w 0 % p25519, fe51ValAt w 40 % p25519, fe51ValAt w 80 % p25519) =
      edSelectAffineNiels (ProofLib.ByteSlice.slice table_bs (960 * i) 960) (digits.getD (2 * i + 1) 0#8) := by
    assumption
  have hacc_len : acc_bs.length = 160 := hacc_b.1
  have hacc_0 := fe51LimbsBoundedAt_mono hacc_b.2.1 (b2 := 2 ^ 53); unpack_fe51_at hacc_0
  have hacc_40 := fe51LimbsBoundedAt_mono hacc_b.2.2.1 (b2 := 2 ^ 53); unpack_fe51_at hacc_40
  have hacc_80 : fe51LimbsBoundedAt acc_bs 80 (2 ^ 52) := hacc_b.2.2.2.1; unpack_fe51_at hacc_80
  have hacc_120 := fe51LimbsBoundedAt_mono hacc_b.2.2.2.2 (b2 := 2 ^ 54); unpack_fe51_at hacc_120
  have hsel_0' := fe51LimbsBoundedAt_mono hsel_0 (b2 := 2 ^ 54); unpack_fe51_at hsel_0'
  have hsel_40' := fe51LimbsBoundedAt_mono hsel_40 (b2 := 2 ^ 54); unpack_fe51_at hsel_40'
  have hsel_80' := fe51LimbsBoundedAt_mono hsel_80 (b2 := 2 ^ 54); unpack_fe51_at hsel_80'
  wp_sym_steps 3; apply sepWP_resize_callee s0.sp 384 528; wp_steps; wp_x25519_call hAdd; clean_prev_sf
  apply sepWP_unresize_callee s0.sp 384 528
  let C := edAddAffineNiels acc (fe51ValAt w 0 % p25519) (fe51ValAt w 40 % p25519) (fe51ValAt w 80 % p25519)
  have hadd_val : edExtOfBytes w_1 = edAddAffineNiels (edExtOfBytes acc_bs)
      (fe51ValAt w 0 % p25519) (fe51ValAt w 40 % p25519) (fe51ValAt w 80 % p25519) := by assumption
  have hc_val : edExtOfBytes w_1 = C := by rw [hadd_val, hacc_v]
  apply sepWP_split4_completed_376 s0.sp C
  intro c0 c1 c2 c3 hc0_l hc1_l hc2_l hc3_l hc0_b hc1_b hc2_b hc3_b hc0_v hc1_v hc2_v hc3_v
  unpack_fe51 hc0_b; unpack_fe51 hc1_b; unpack_fe51 hc2_b; unpack_fe51 hc3_b
  apply sepWP_split4_stack_536 s0.sp; intro e0 e1 e2 e3 he0_l he1_l he2_l he3_l
  apply sepWP_resize_callee s0.sp 688 224
  wp_steps; wp_x25519_call hMul; clean_prev_sf; obtain ⟨hr0_l, hr0_b, hr0_v⟩ := fe51_mul_post_props w_2 (fpMul C.X C.T)
  wp_steps; wp_x25519_call hMul; clean_prev_sf; obtain ⟨hr1_l, hr1_b, hr1_v⟩ := fe51_mul_post_props w_3 (fpMul C.Y C.Z)
  wp_steps; wp_x25519_call hMul; clean_prev_sf; obtain ⟨hr2_l, hr2_b, hr2_v⟩ := fe51_mul_post_props w_4 (fpMul C.Z C.T)
  wp_steps; wp_x25519_call hMul; clean_prev_sf; obtain ⟨hr3_l, hr3_b, hr3_v⟩ := fe51_mul_post_props w_5 (fpMul C.X C.Y)
  apply sepWP_unresize_callee s0.sp 688 224
  apply sepWP_merge4_stack_376 s0.sp; intro comp' hcomp'_len
  apply sepWP_merge4_stack_536 s0.sp
    (fun res => fe51Point4Bounded res (2 ^ 52) ∧ edExtOfBytes res = edMulBaseStep table_bs i (digits.getD (2 * i + 1) 0#8) acc)
  · obtain ⟨hl, hb0, hb1, hb2, hb3, hv⟩ := edAsExtended_of_append4 w_2 w_3 w_4 w_5 C hr0_b hr1_b hr2_b hr3_b hr0_v hr1_v hr2_v hr3_v
    refine ⟨⟨hl, hb0, hb1, hb2, hb3⟩, ?_⟩; rw [hv]; unfold edMulBaseStep; rw [← hsel_val]
  intro ext' ⟨hext'_b, hext'_v⟩
  clear_dead_vars [w_1, c0, c1, c2, c3, e0, e1, e2, e3, w_2, w_3, w_4, w_5]
  have hext'_len : ext'.length = 160 := hext'_b.1; have : HasLenGe acc_bs 160 := ⟨by omega⟩
  wp_cut_codeLoaded
  wp_sym_steps 13
  apply SepWP.done
  · rfl
  · wp_norm_lhs
  intro hcl_copy
  apply sepWP_abstract_bytes (s0.sp - 704#64)
    (fun buf => fe51Point4Bounded buf (2 ^ 52) ∧ edExtOfBytes buf = edMulBaseStep table_bs i (digits.getD (2 * i + 1) 0#8) acc)
    (hQ := copy160_point4_post acc_bs ext' _ (2 ^ 52) hacc_len hext'_b hext'_v)
  intro acc' ⟨hacc'_b, hacc'_v⟩
  have hperm : ((s0.sp - 704#64) ↦ₛ acc' ∗ (s0.sp - 536#64) ↦ₛ ext' ∗ (s0.sp - 376#64) ↦ₛ comp' ∗
      memRegion (s0.sp - 1680#64) 912 ∗ (s0.sp - 216#64) ↦ₛ w ∗ table ↦ᵣ table_bs ∗ (s0.sp - 768#64) ↦ₛ digits ∗ F) =
      mulBaseLoopPre s0.sp table table_bs digits acc' ext' comp' w F := by unfold mulBaseLoopPre; sep_ac_rfl
  rw [hperm]
  refine hnext _ acc' ext' comp' w ⟨?_, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
    by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, ?_, by wp_norm_lhs, by wp_norm_lhs,
    by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hcl_copy⟩
    hacc'_b hacc'_v hext'_len hcomp'_len hniels_w_len
  · simp only [State.pc_setMem, State.pc_setPC, pc_odd_end b hi]
  · simp only [arm64_norm, ofNat_2i1_add_1 hi]

private theorem loop_zero_eq {i : Nat} (h : i + 0 = 32) : i = 32 := h
private theorem loop_succ_lt {i rem' : Nat} (h : i + (rem' + 1) = 32) : i < 32 := by omega
private theorem loop_succ_add {i rem' : Nat} (h : i + (rem' + 1) = 32) : (i + 1) + rem' = 32 := by omega
private theorem loop_succ_cond {i rem' : Nat} (h : i + (rem' + 1) = 32) : (i == 31) = (rem' == 0) := by
  cases h0 : (rem' == 0)
  · simp only [beq_eq_false_iff_ne, ne_eq] at h0 ⊢; omega
  · simp only [beq_iff_eq] at h0 ⊢; omega

set_option maxHeartbeats 800000 in
attribute [local irreducible] fe51LookupTable8Bounded in
attribute [local wp_norm] ByteSlice.pack64_eq_readLE_8 in
private theorem mul_base_even_iter [X25519CliPlacement]
    (b : BitVec 64) (_hb : X25519Base x25519CliPl13 b) (hbase : x25519CliPl13.base = b)
    (hSelect : LookupTableAffineNielsSelectOk) (hAdd : EdwardsPointAddAffineNielsOk) (hMul : Fe51MulOk)
    (i : Nat) (hi : i < 32) (s0 s : State) (target_pc out table : BitVec 64)
    (table_bs digits acc_bs ext_bs comp_bs niels_bs : List (BitVec 8))
    (acc : EdExtPoint) (F : SepProp) (post : State → SepProp → Prop) {oom : State → SepProp}
    (hsp0_align : s0.spAligned = true)
    (hregs : MulBaseEvenRegs s0 s out table (b + 416#64) (BitVec.ofNat 64 (2 * i)))
    (htab_len : table_bs.length = 30720)
    (htab_bnd : ∀ j < 32, fe51LookupTable8Bounded (ProofLib.ByteSlice.slice table_bs (960 * j) 960) (2 ^ 53))
    (hdigits_len : digits.length = 64) (hacc_b : fe51Point4Bounded acc_bs (2 ^ 52)) (hacc_v : edExtOfBytes acc_bs = acc)
    (hext_len : ext_bs.length = 160) (hcomp_len : comp_bs.length = 160) (hniels_len : niels_bs.length = 120)
    (hnext : ∀ (sf' : State) (acc' ext' comp' niels' : List (BitVec 8)),
      MulBaseEvenRegs s0 sf' out table (if i == 31 then b + 580#64 else b + 416#64) (BitVec.ofNat 64 (2 * (i + 1))) →
      fe51Point4Bounded acc' (2 ^ 52) → edExtOfBytes acc' = edMulBaseStep table_bs i (digits.getD (2 * i + 0) 0#8) acc →
      ext'.length = 160 → comp'.length = 160 → niels'.length = 120 →
      SepWP (x25519CliPC13.rebase b (fun _ => none)) target_pc sf' (mulBaseLoopPre s0.sp table table_bs digits acc' ext' comp' niels' F) post oom) :
    SepWP (x25519CliPC13.rebase b (fun _ => none)) target_pc s
      (mulBaseLoopPre s0.sp table table_bs digits acc_bs ext_bs comp_bs niels_bs F) post oom := by
  rcases hregs with ⟨hpc, hrun, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29, hvregs, hcl⟩
  unfold mulBaseLoopPre
  wp_sym_steps 1; simp only [even_getLsbD_0 hi]
  wp_sym_steps 3; simp only [ule_64_2i hi, Bool.false_eq_true, ↓ite_false]
  wp_sym_steps 3; simp only [lsr_2i hi, mul_960_ofNat hi]
  apply sepWP_resize_callee s0.sp 720 192; apply sepWP_split_ro_slice table table_bs i hi htab_len
  have htab_i : fe51LookupTable8Bounded (ProofLib.ByteSlice.slice table_bs (960 * i) 960) 9007199254740992 := htab_bnd i hi
  wp_steps; wp_x25519_call hSelect; clean_prev_sf
  apply sepWP_unsplit_ro_slice table table_bs i hi htab_len; apply sepWP_unresize_callee s0.sp 720 192
  have hniels_w_len : w.length = 120 := by assumption
  obtain ⟨hsel_0, hsel_40, hsel_80⟩ : fe51AffineNielsBoundedAt w 0 (2 ^ 53) := by assumption
  have hsel_val : (fe51ValAt w 0 % p25519, fe51ValAt w 40 % p25519, fe51ValAt w 80 % p25519) =
      edSelectAffineNiels (ProofLib.ByteSlice.slice table_bs (960 * i) 960) (digits.getD (2 * i) 0#8) := by
    assumption
  have hacc_len : acc_bs.length = 160 := hacc_b.1
  have hacc_0 := fe51LimbsBoundedAt_mono hacc_b.2.1 (b2 := 2 ^ 53); unpack_fe51_at hacc_0
  have hacc_40 := fe51LimbsBoundedAt_mono hacc_b.2.2.1 (b2 := 2 ^ 53); unpack_fe51_at hacc_40
  have hacc_80 : fe51LimbsBoundedAt acc_bs 80 (2 ^ 52) := hacc_b.2.2.2.1; unpack_fe51_at hacc_80
  have hacc_120 := fe51LimbsBoundedAt_mono hacc_b.2.2.2.2 (b2 := 2 ^ 54); unpack_fe51_at hacc_120
  have hsel_0' := fe51LimbsBoundedAt_mono hsel_0 (b2 := 2 ^ 54); unpack_fe51_at hsel_0'
  have hsel_40' := fe51LimbsBoundedAt_mono hsel_40 (b2 := 2 ^ 54); unpack_fe51_at hsel_40'
  have hsel_80' := fe51LimbsBoundedAt_mono hsel_80 (b2 := 2 ^ 54); unpack_fe51_at hsel_80'
  wp_sym_steps 3; apply sepWP_resize_callee s0.sp 384 528; wp_steps; wp_x25519_call hAdd; clean_prev_sf
  apply sepWP_unresize_callee s0.sp 384 528
  let C := edAddAffineNiels acc (fe51ValAt w 0 % p25519) (fe51ValAt w 40 % p25519) (fe51ValAt w 80 % p25519)
  have hadd_val : edExtOfBytes w_1 = edAddAffineNiels (edExtOfBytes acc_bs)
      (fe51ValAt w 0 % p25519) (fe51ValAt w 40 % p25519) (fe51ValAt w 80 % p25519) := by assumption
  have hc_val : edExtOfBytes w_1 = C := by rw [hadd_val, hacc_v]
  apply sepWP_split4_completed_376 s0.sp C
  intro c0 c1 c2 c3 hc0_l hc1_l hc2_l hc3_l hc0_b hc1_b hc2_b hc3_b hc0_v hc1_v hc2_v hc3_v
  unpack_fe51 hc0_b; unpack_fe51 hc1_b; unpack_fe51 hc2_b; unpack_fe51 hc3_b
  apply sepWP_split4_stack_536 s0.sp; intro e0 e1 e2 e3 he0_l he1_l he2_l he3_l
  apply sepWP_resize_callee s0.sp 688 224
  wp_steps; wp_x25519_call hMul; clean_prev_sf; obtain ⟨hr0_l, hr0_b, hr0_v⟩ := fe51_mul_post_props w_2 (fpMul C.X C.T)
  wp_steps; wp_x25519_call hMul; clean_prev_sf; obtain ⟨hr1_l, hr1_b, hr1_v⟩ := fe51_mul_post_props w_3 (fpMul C.Y C.Z)
  wp_steps; wp_x25519_call hMul; clean_prev_sf; obtain ⟨hr2_l, hr2_b, hr2_v⟩ := fe51_mul_post_props w_4 (fpMul C.Z C.T)
  wp_steps; wp_x25519_call hMul; clean_prev_sf; obtain ⟨hr3_l, hr3_b, hr3_v⟩ := fe51_mul_post_props w_5 (fpMul C.X C.Y)
  apply sepWP_unresize_callee s0.sp 688 224
  apply sepWP_merge4_stack_376 s0.sp; intro comp' hcomp'_len
  apply sepWP_merge4_stack_536 s0.sp
    (fun res => fe51Point4Bounded res (2 ^ 52) ∧ edExtOfBytes res = edMulBaseStep table_bs i (digits.getD (2 * i + 0) 0#8) acc)
  · obtain ⟨hl, hb0, hb1, hb2, hb3, hv⟩ := edAsExtended_of_append4 w_2 w_3 w_4 w_5 C hr0_b hr1_b hr2_b hr3_b hr0_v hr1_v hr2_v hr3_v
    refine ⟨⟨hl, hb0, hb1, hb2, hb3⟩, ?_⟩; rw [hv]; unfold edMulBaseStep; simp only [Nat.add_zero]; rw [← hsel_val]
  intro ext' ⟨hext'_b, hext'_v⟩
  clear_dead_vars [w_1, c0, c1, c2, c3, e0, e1, e2, e3, w_2, w_3, w_4, w_5]
  have hext'_len : ext'.length = 160 := hext'_b.1; have : HasLenGe acc_bs 160 := ⟨by omega⟩
  wp_cut_codeLoaded
  wp_sym_steps 13; simp only [ofNat_2i_add_1 hi]
  wp_sym_steps 1; simp only [odd_getLsbD_0 hi, beq_self_eq_true, ↓ite_true]
  wp_sym_steps 3
  apply SepWP.done
  · rfl
  · wp_norm_lhs
  intro hcl_copy
  apply sepWP_abstract_bytes (s0.sp - 704#64)
    (fun buf => fe51Point4Bounded buf (2 ^ 52) ∧ edExtOfBytes buf = edMulBaseStep table_bs i (digits.getD (2 * i + 0) 0#8) acc)
    (hQ := copy160_point4_post acc_bs ext' _ (2 ^ 52) hacc_len hext'_b hext'_v)
  intro acc' ⟨hacc'_b, hacc'_v⟩
  have hperm : ((s0.sp - 704#64) ↦ₛ acc' ∗ (s0.sp - 536#64) ↦ₛ ext' ∗ (s0.sp - 376#64) ↦ₛ comp' ∗
      memRegion (s0.sp - 1680#64) 912 ∗ (s0.sp - 216#64) ↦ₛ w ∗ table ↦ᵣ table_bs ∗ (s0.sp - 768#64) ↦ₛ digits ∗ F) =
      mulBaseLoopPre s0.sp table table_bs digits acc' ext' comp' w F := by unfold mulBaseLoopPre; sep_ac_rfl
  rw [hperm]
  refine hnext _ acc' ext' comp' w ⟨?_, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
    by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, ?_, by wp_norm_lhs, by wp_norm_lhs,
    by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hcl_copy⟩
    hacc'_b hacc'_v hext'_len hcomp'_len hniels_w_len
  · simp only [State.pc_setMem, State.pc_setPC, pc_even_end b hi]
  · simp only [arm64_norm, ofNat_2i1_add_1 hi]

attribute [local irreducible] edMulBaseStep

private theorem MulBaseLoopRegs.of_pc [X25519CliPlacement]
    {s0 s : State} {out table r22 r24 r26 pc1 pc2 x23 : BitVec 64}
    (h : MulBaseLoopRegs s0 s out table r22 r24 r26 pc1 x23) (hpc : pc1 = pc2) :
    MulBaseLoopRegs s0 s out table r22 r24 r26 pc2 x23 :=
  ⟨h.1.trans hpc, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10, h.11, h.12, h.13, h.14, h.15, h.16⟩

private theorem edMulBaseLoopWith_step {α : Type} (step : Nat → α → α) (i rem : Nat) (acc : α) :
    edMulBaseLoopWith step i (rem + 1) acc = edMulBaseLoopWith step (i + 1) rem (step i acc) := rfl

private theorem edMulBaseLoop_step (table_bs digits : List (BitVec 8)) (parity i rem : Nat) (acc : EdExtPoint) :
    edMulBaseLoop table_bs digits parity i (rem + 1) acc =
    edMulBaseLoop table_bs digits parity (i + 1) rem (edMulBaseStep table_bs i (digits.getD (2 * i + parity) 0#8) acc) :=
  edMulBaseLoopWith_step (edMulBaseStepAt table_bs digits parity) i rem acc

private theorem mul_base_odd_loop [X25519CliPlacement]
    (b : BitVec 64) (hb : X25519Base x25519CliPl13 b) (hbase : x25519CliPl13.base = b)
    (hSelect : LookupTableAffineNielsSelectOk) (hAdd : EdwardsPointAddAffineNielsOk) (hMul : Fe51MulOk)
    (rem i : Nat) (hrem : i + rem = 32) (s0 s : State) (target_pc out table : BitVec 64)
    (table_bs digits acc_bs ext_bs comp_bs niels_bs : List (BitVec 8))
    (acc : EdExtPoint) (F : SepProp) (post : State → SepProp → Prop) {oom : State → SepProp}
    (hsp0_align : s0.spAligned = true)
    (hregs : MulBaseOddRegs s0 s out table (if rem == 0 then b + 316#64 else b + 152#64) (BitVec.ofNat 64 (2 * i)))
    (htab_len : table_bs.length = 30720)
    (htab_bnd : ∀ j < 32, fe51LookupTable8Bounded (ProofLib.ByteSlice.slice table_bs (960 * j) 960) (2 ^ 53))
    (hdigits_len : digits.length = 64) (hacc_b : fe51Point4Bounded acc_bs (2 ^ 52)) (hacc_v : edExtOfBytes acc_bs = acc)
    (hext_len : ext_bs.length = 160) (hcomp_len : comp_bs.length = 160) (hniels_len : niels_bs.length = 120)
    (hnext : ∀ (sf' : State) (acc' ext' comp' niels' : List (BitVec 8)),
      MulBaseOddRegs s0 sf' out table (b + 316#64) 64#64 → fe51Point4Bounded acc' (2 ^ 52) →
      edExtOfBytes acc' = edMulBaseLoop table_bs digits 1 i rem acc → ext'.length = 160 → comp'.length = 160 → niels'.length = 120 →
      SepWP (x25519CliPC13.rebase b (fun _ => none)) target_pc sf' (mulBaseLoopPre s0.sp table table_bs digits acc' ext' comp' niels' F) post oom) :
    SepWP (x25519CliPC13.rebase b (fun _ => none)) target_pc s
      (mulBaseLoopPre s0.sp table table_bs digits acc_bs ext_bs comp_bs niels_bs F) post oom := by
  induction rem generalizing i s acc_bs ext_bs comp_bs niels_bs acc with
  | zero => cases loop_zero_eq hrem; exact hnext s acc_bs ext_bs comp_bs niels_bs hregs hacc_b hacc_v hext_len hcomp_len hniels_len
  | succ rem' ih =>
    have hi : i < 32 := loop_succ_lt hrem
    apply mul_base_odd_iter b hb hbase hSelect hAdd hMul i hi s0 s target_pc out table table_bs digits acc_bs ext_bs comp_bs niels_bs acc F post
      hsp0_align hregs htab_len htab_bnd hdigits_len hacc_b hacc_v hext_len hcomp_len hniels_len
    intro sf1 acc1 ext1 comp1 niels1 hregs1 hacc1_b hacc1_v hext1_l hcomp1_l hniels1_l
    have hpc_eq : (if i == 31 then b + 316#64 else b + 152#64) = (if rem' == 0 then b + 316#64 else b + 152#64) := by rw [loop_succ_cond hrem]
    apply ih (i + 1) (loop_succ_add hrem) sf1 acc1 ext1 comp1 niels1 (edMulBaseStep table_bs i (digits.getD (2 * i + 1) 0#8) acc)
      (hregs1.of_pc hpc_eq) hacc1_b hacc1_v hext1_l hcomp1_l hniels1_l
    intro sf' acc' ext' comp' niels' hr hbnd hv he hc hn
    exact hnext sf' acc' ext' comp' niels' hr hbnd (hv.trans (edMulBaseLoop_step table_bs digits 1 i rem' acc).symm) he hc hn

private theorem mul_base_even_loop [X25519CliPlacement]
    (b : BitVec 64) (hb : X25519Base x25519CliPl13 b) (hbase : x25519CliPl13.base = b)
    (hSelect : LookupTableAffineNielsSelectOk) (hAdd : EdwardsPointAddAffineNielsOk) (hMul : Fe51MulOk)
    (rem i : Nat) (hrem : i + rem = 32) (s0 s : State) (target_pc out table : BitVec 64)
    (table_bs digits acc_bs ext_bs comp_bs niels_bs : List (BitVec 8))
    (acc : EdExtPoint) (F : SepProp) (post : State → SepProp → Prop) {oom : State → SepProp}
    (hsp0_align : s0.spAligned = true)
    (hregs : MulBaseEvenRegs s0 s out table (if rem == 0 then b + 580#64 else b + 416#64) (BitVec.ofNat 64 (2 * i)))
    (htab_len : table_bs.length = 30720)
    (htab_bnd : ∀ j < 32, fe51LookupTable8Bounded (ProofLib.ByteSlice.slice table_bs (960 * j) 960) (2 ^ 53))
    (hdigits_len : digits.length = 64) (hacc_b : fe51Point4Bounded acc_bs (2 ^ 52)) (hacc_v : edExtOfBytes acc_bs = acc)
    (hext_len : ext_bs.length = 160) (hcomp_len : comp_bs.length = 160) (hniels_len : niels_bs.length = 120)
    (hnext : ∀ (sf' : State) (acc' ext' comp' niels' : List (BitVec 8)),
      MulBaseEvenRegs s0 sf' out table (b + 580#64) 64#64 → fe51Point4Bounded acc' (2 ^ 52) →
      edExtOfBytes acc' = edMulBaseLoop table_bs digits 0 i rem acc → ext'.length = 160 → comp'.length = 160 → niels'.length = 120 →
      SepWP (x25519CliPC13.rebase b (fun _ => none)) target_pc sf' (mulBaseLoopPre s0.sp table table_bs digits acc' ext' comp' niels' F) post oom) :
    SepWP (x25519CliPC13.rebase b (fun _ => none)) target_pc s
      (mulBaseLoopPre s0.sp table table_bs digits acc_bs ext_bs comp_bs niels_bs F) post oom := by
  induction rem generalizing i s acc_bs ext_bs comp_bs niels_bs acc with
  | zero => cases loop_zero_eq hrem; exact hnext s acc_bs ext_bs comp_bs niels_bs hregs hacc_b hacc_v hext_len hcomp_len hniels_len
  | succ rem' ih =>
    have hi : i < 32 := loop_succ_lt hrem
    apply mul_base_even_iter b hb hbase hSelect hAdd hMul i hi s0 s target_pc out table table_bs digits acc_bs ext_bs comp_bs niels_bs acc F post
      hsp0_align hregs htab_len htab_bnd hdigits_len hacc_b hacc_v hext_len hcomp_len hniels_len
    intro sf1 acc1 ext1 comp1 niels1 hregs1 hacc1_b hacc1_v hext1_l hcomp1_l hniels1_l
    have hpc_eq : (if i == 31 then b + 580#64 else b + 416#64) = (if rem' == 0 then b + 580#64 else b + 416#64) := by rw [loop_succ_cond hrem]
    apply ih (i + 1) (loop_succ_add hrem) sf1 acc1 ext1 comp1 niels1 (edMulBaseStep table_bs i (digits.getD (2 * i + 0) 0#8) acc)
      (hregs1.of_pc hpc_eq) hacc1_b hacc1_v hext1_l hcomp1_l hniels1_l
    intro sf' acc' ext' comp' niels' hr hbnd hv he hc hn
    exact hnext sf' acc' ext' comp' niels' hr hbnd (hv.trans (edMulBaseLoop_step table_bs digits 0 i rem' acc).symm) he hc hn


/-! ## 2. Clamped Basepoint Wrapper (`Blk14`) Private Helpers -/

private theorem pointsToBytes32_split_ends (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 32) :
    (a ↦ₛ bs) =
      (a ↦₈ bs.getD 0 0#8) ∗
      ((a + 1#64) ↦ₛ (bs.drop 1).take 30) ∗
      ((a + 31#64) ↦₈ bs.getD 31 0#8) := by
  rw [pointsToBytes_take_drop a 1 bs (by omega),
      pointsToBytes_take_drop (a + 1#64) 30 (bs.drop 1) (by simp [h])]
  simp only [List.drop_drop, BitVec.add_assoc, BitVec.reduceAdd]
  rw [show bs.take 1 = (bs.drop 0).take 1 from rfl,
      show bs.drop 31 = (bs.drop 31).take 1 from (List.take_of_length_le (by simp [h])).symm,
      pointsToBytes_take1_eq_pointsTo8 a bs 0 (by omega),
      pointsToBytes_take1_eq_pointsTo8 (a + 31#64) bs 31 (by omega)]

private theorem clamp_byte0_eq (x : BitVec 8) :
    BitVec.zeroExtend 8 (BitVec.zeroExtend 64 x &&& 1065151889656#64) = x &&& 0xf8#8 := by
  revert x; decide

private theorem clamp_byte31_eq (x : BitVec 8) :
    BitVec.zeroExtend 8 (64#64 ||| BitVec.zeroExtend 64 x >>> 0 &&& 63#64) =
      (x &&& 0x7f#8) ||| 0x40#8 := by
  revert x; decide

private theorem pointsToBytes32_clamp (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 32) :
    ((a ↦₈ ((bs.getD 0 0#8) &&& 0xf8#8)) ∗
      ((a + 1#64) ↦ₛ (bs.drop 1).take 30) ∗
      ((a + 31#64) ↦₈ (((bs.getD 31 0#8) &&& 0x7f#8) ||| 0x40#8))) =
    (a ↦ₛ clampScalarBytes bs) := by
  have hc_len : (clampScalarBytes bs).length = 32 := clampScalarBytes_length_of_eq32 h
  rw [pointsToBytes32_split_ends a (clampScalarBytes bs) hc_len]
  have hmid_len : ((bs.drop 1).take 30).length = 30 := by simp [h]
  have hc_eq : clampScalarBytes bs =
      ((bs.getD 0 0#8) &&& 0xf8#8) ::
        (((bs.drop 1).take 30) ++ [((bs.getD 31 0#8) &&& 0x7f#8) ||| 0x40#8]) := by
    unfold clampScalarBytes
    rw [List.append_assoc]; rfl
  have h0 : (clampScalarBytes bs).getD 0 0#8 = (bs.getD 0 0#8) &&& 0xf8#8 := by
    rw [hc_eq]; rfl
  have hmid : ((clampScalarBytes bs).drop 1).take 30 = (bs.drop 1).take 30 := by
    rw [hc_eq]
    exact (List.take_append_of_le_length (Nat.le_of_eq hmid_len.symm)).trans
      (List.take_of_length_le (Nat.le_of_eq hmid_len))
  have h31 : (clampScalarBytes bs).getD 31 0#8 = (((bs.getD 31 0#8) &&& 0x7f#8) ||| 0x40#8) := by
    rw [hc_eq, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
        List.getElem?_append_right (Nat.le_of_eq hmid_len), hmid_len]
    rfl
  rw [h0, hmid, h31]


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

export LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.BasepointTable1 (
  lookup_table_affine_niels_select_ok_of lookup_table_affine_niels_select_ok)

set_option maxHeartbeats 800000 in
attribute [local wp_norm] ByteSlice.pack64_eq_readLE_8 in
/-- Conditional `<EdwardsBasepointTable as BasepointTable>::mul_base` (`Blk13`, 167 insns) contract. -/
theorem edwards_basepoint_table_mul_base_ok_of
    (hSelect : LookupTableAffineNielsSelectOk) (hMul : Fe51MulOk)
    (hMulPow2_4 : EdwardsPointMulByPow2_4Ok) (hAddAN : EdwardsPointAddAffineNielsOk)
    (hRadix16 : ScalarAsRadix16Ok) :
    EdwardsBasepointTableMulBaseOk := by
  intro _
  apply x25519Caller_ok x25519CliPC13 x25519CliPl13
  intro b _hb hbase
  wp_init
  obtain ⟨htab_len, htab_bnd⟩ : fe51BasepointTable32Bounded a_4 (2 ^ 53) := by assumption
  have hout_len : a_3.length = 160 := by assumption
  have h1_len : fe51OneBytes.length = 40 := fe51OneBytes_length; have : HasLenGe fe51OneBytes 40 := ⟨by omega⟩
  apply sepWP_split_stack_callee 912 768
  apply sepWP_peel_stack_bytes s0.sp 768 64 704; intro sp_768 h_768
  apply sepWP_peel_stack_bytes s0.sp 704 160 544; intro sp_704 h_704
  apply sepWP_peel_stack_bytes s0.sp 544 8 536; intro sp_544 h_544
  apply sepWP_peel_stack_bytes s0.sp 536 160 376; intro sp_536 h_536
  apply sepWP_peel_stack_bytes s0.sp 376 160 216; intro sp_376 h_376
  apply sepWP_peel_stack_bytes s0.sp 216 120 96; intro sp_216 h_216
  open_cells (s0.sp - 96#64) 96 12
  wp_cut_codeLoaded; wp_steps; wp_x25519_call hRadix16
  have hdigits_len : (scalarRadix16Digits a_rest).length = 64 := scalarRadix16Digits_length a_rest
  wp_cut_codeLoaded
  wp_sym_steps 19
  apply SepWP.done
  · rfl
  · wp_norm_lhs
  intro hcl_init
  apply sepWP_abstract_bytes (s0.sp - 704#64)
    (fun buf => fe51Point4Bounded buf (2 ^ 52) ∧ edExtOfBytes buf = edExtZero)
    (hQ := mul_base_init_post sp_704 h_704)
  intro acc0 ⟨hacc0_b, hacc0_v⟩; apply sepWP_fold_mulBaseLoopPre s0.sp a
  apply mul_base_odd_loop b _hb hbase hSelect hAddAN hMul 32 0 rfl s0 _ _ a_1 a a_4
    (scalarRadix16Digits a_rest) acc0 sp_536 sp_376 sp_216 edExtZero _ _ hsp_align
    ⟨by simp only [State.pc_setMem, State.pc_setPC]; rfl, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
     by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hcl_init⟩
    htab_len htab_bnd hdigits_len hacc0_b hacc0_v h_536 h_376 h_216
  intro sf_odd acc_odd ext_odd comp_odd niels_odd hregs_odd hacc_odd_b hacc_odd_v hext_odd_l hcomp_odd_l hniels_odd_l
  clear_dead_vars [sf]; try clear sf
  rcases hregs_odd with ⟨hpc_o, hrun_o, hsp_o, hx19_o, hx20_o, hx21_o, hx22_o, hx23_o, hx24_o, hx25_o, hx26_o, hx27_o, hx28_o, hx29_o, hvregs_o, hcl_o⟩
  unfold mulBaseLoopPre; obtain ⟨hacc_odd_l, hacc_o0, hacc_o40, hacc_o80, hacc_o120⟩ := hacc_odd_b
  replace hacc_o0 := fe51LimbsBoundedAt_mono hacc_o0 (b2 := 2 ^ 53); unpack_fe51_at hacc_o0
  replace hacc_o40 := fe51LimbsBoundedAt_mono hacc_o40 (b2 := 2 ^ 53); unpack_fe51_at hacc_o40
  replace hacc_o80 := fe51LimbsBoundedAt_mono hacc_o80 (b2 := 2 ^ 53); unpack_fe51_at hacc_o80
  replace hacc_o120 := fe51LimbsBoundedAt_mono hacc_o120 (b2 := 2 ^ 53); unpack_fe51_at hacc_o120
  wp_steps; wp_x25519_call hMulPow2_4; clean_prev_sf
  obtain ⟨hw_b, hw_post⟩ : fe51Point4Bounded w (2 ^ 52) ∧ edExtOfBytes w = edDouble4 (edExtOfBytes acc_odd) :=
    ⟨by assumption, by assumption⟩
  have hw_len : w.length = 160 := hw_b.1; have : HasLenGe acc_odd 160 := ⟨by omega⟩
  wp_cut_codeLoaded
  wp_sym_steps 16
  apply SepWP.done
  · rfl
  · wp_norm_lhs
  intro hcl_dbl
  have hw_v : edExtOfBytes w = edDouble4 (edMulBaseLoop a_4 (scalarRadix16Digits a_rest) 1 0 32 edExtZero) := by
    rw [hw_post, hacc_odd_v]
  apply sepWP_abstract_bytes (s0.sp - 704#64)
    (fun buf => fe51Point4Bounded buf (2 ^ 52) ∧ edExtOfBytes buf = edDouble4 (edMulBaseLoop a_4 (scalarRadix16Digits a_rest) 1 0 32 edExtZero))
    (hQ := copy160_point4_post acc_odd w _ (2 ^ 52) hacc_odd_l hw_b hw_v)
  intro acc_dbl ⟨hacc_dbl_b, hacc_dbl_v⟩; apply sepWP_fold_mulBaseLoopPre s0.sp a
  apply mul_base_even_loop b _hb hbase hSelect hAddAN hMul 32 0 rfl s0 _ _ a_1 a a_4
    (scalarRadix16Digits a_rest) acc_dbl ext_odd w niels_odd
    (edDouble4 (edMulBaseLoop a_4 (scalarRadix16Digits a_rest) 1 0 32 edExtZero)) _ _ hsp_align
    ⟨by simp only [State.pc_setMem, State.pc_setPC]; rfl, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
     by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hcl_dbl⟩
    htab_len htab_bnd hdigits_len hacc_dbl_b hacc_dbl_v hext_odd_l hw_len hniels_odd_l
  intro sf_even acc_even ext_even comp_even niels_even hregs_even hacc_even_b hacc_even_v hext_even_l hcomp_even_l hniels_even_l
  rcases hregs_even with ⟨hpc_e, hrun_e, hsp_e, hx19_e, hx20_e, hx21_e, hx22_e, hx23_e, hx24_e, hx25_e, hx26_e, hx27_e, hx28_e, hx29_e, hvregs_e, hcl_e⟩
  unfold mulBaseLoopPre; have hacc_even_l : acc_even.length = 160 := hacc_even_b.1; have : HasLenGe a_3 160 := ⟨by omega⟩
  wp_sym_steps 18
  apply sepWP_abstract_bytes a_1
    (fun buf => fe51Point4Bounded buf (2 ^ 52) ∧ edExtOfBytes buf = edMulBase a_4 a_rest)
    (hQ := copy160_point4_post a_3 acc_even _ (2 ^ 52) hout_len hacc_even_b hacc_even_v)
  intro res_bs ⟨hres_b, hres_v⟩; close_cells_sub s0.sp 96 96 12
  apply sepWP_unpeel_stack_bytes s0.sp 216 120 96; apply sepWP_unpeel_stack_bytes s0.sp 376 160 216
  apply sepWP_unpeel_stack_bytes s0.sp 536 160 376; apply sepWP_unpeel_stack_bytes s0.sp 544 8 536
  apply sepWP_unpeel_stack_bytes s0.sp 704 160 544; apply sepWP_unpeel_stack_bytes s0.sp 768 64 704
  apply sepWP_merge_stack_callee 912 768
  obtain ⟨hres_l, hres0, hres40, hres80, hres120⟩ := hres_b
  unpack_fe51_at hres0; unpack_fe51_at hres40; unpack_fe51_at hres80; unpack_fe51_at hres120; wp_done


/-- `<EdwardsBasepointTable as BasepointTable>::mul_base` (`Blk13`, 167 insns). -/
theorem edwards_basepoint_table_mul_base_ok : EdwardsBasepointTableMulBaseOk :=
  edwards_basepoint_table_mul_base_ok_of
    lookup_table_affine_niels_select_ok fe51_mul_ok
    edwards_point_mul_by_pow_2_4_ok edwards_point_add_affine_niels_ok
    scalar_as_radix_16_ok

/-- Conditional `<EdwardsPoint>::mul_base_clamped` (`Blk14`, 11 insns) contract. -/
theorem edwards_point_mul_base_clamped_ok_of
    (hMulBase : EdwardsBasepointTableMulBaseOk) : EdwardsPointMulBaseClampedOk := by
  intro _
  apply x25519Caller_ok x25519CliPC14 x25519CliPl14
  intro b _hb hbase
  wp_init
  have hbytes_l : a_rest.length = 32 := ‹_›
  obtain ⟨htab_l, htab_b⟩ := fe51BasepointTable32Bounded_mono ed25519BasepointTableBytes_bounded (b2 := 2 ^ 53)
  have hcl_len : (clampScalarBytes a_rest).length = 32 := clampScalarBytes_length_of_eq32 hbytes_l
  have hcl_31 : ((clampScalarBytes a_rest).getD 31 0#8).toNat ≤ 127 :=
    clampScalarBytes_getD31_le_127 hbytes_l
  wp_conv_pre => rw [pointsToBytes32_split_ends a a_rest hbytes_l]
  wp_cut_codeLoaded
  wp_steps
  wp_conv_pre =>
    rw [clamp_byte0_eq, clamp_byte31_eq, pointsToBytes32_clamp a a_rest hbytes_l]
  wp_x25519_tailcall hMulBase
  obtain ⟨_, hw0, hw40, hw80, hw120⟩ := (‹fe51Point4Bounded w (2 ^ 52)›)
  unpack_fe51_at hw0; unpack_fe51_at hw40; unpack_fe51_at hw80; unpack_fe51_at hw120
  wp_done

/-- `<EdwardsPoint>::mul_base_clamped` (`Blk14`, 11 insns). -/
theorem edwards_point_mul_base_clamped_ok : EdwardsPointMulBaseClampedOk :=
  edwards_point_mul_base_clamped_ok_of edwards_basepoint_table_mul_base_ok


end

end LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.BasepointTable
