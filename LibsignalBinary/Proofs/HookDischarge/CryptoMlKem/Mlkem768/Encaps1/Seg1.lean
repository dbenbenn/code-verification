/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a -- proof-setup: allow-public-import
meta import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (
  mlkemData02Bytes mlkemData03Bytes mlkemData04Bytes mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement add_off_reloc_cancel add_reloc_cancel add_zero_reloc_cancel
  mbase mlkemBlockPlacement_ρ mlkemCall_of_blockOk mlkemMpl
  resolve_blk00 resolve_blk28 resolve_blk29
  resolve_ro01 resolve_ro02 resolve_ro03 resolve_ro04 seq_codeLoaded_lr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (
  MlKemRoOk cst16_0_vec cst16_1_vec cst16_2_vec
  mlkemData02Bytes_length mlkemData03Bytes_length mlkemData04Bytes_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (
  Keccak2SlicesRW mlkemMemcpySpec mlkemMemsetSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6 (blk00_keccak2_72_6_RW1_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps (blk28_memcpy_ok blk29_memset_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (sha3_512List)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  cell_entails_memRegion8 sepWP_seq_env step_ldrQ128_ro)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Poly32Mem PolyMem SepStore128 Vec128At Vec32 VecRangeMem append_extractLsb64 bytesToVecNat
  poly32Mem_eq_pointsToBytes poly32Mem_ofFn pointsToBytes_eq_vecRangeMem step_strQ128
  vecRangeBytes vecRangeBytes_length SepWP.of_memRegion_vecRangeMem)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  entails_sub sepWP_elim_cell8 sepWP_elim_region32 spAligned_of_sp_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base (
  MlkemBlk03Args SavedFrame03 blk03_code_eq blk03_tree_size blkLib03 blkPC03 blkPl03
  blkPlaceable03 blkTree03 mlkemBlk03RawSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a (
  SavedArgs03 Seg2ConstsLo Seg2Preserved Seg2RegInv Seg2SeedConsts
  blkPC03_rebase_fetchOff_24c blkPC03_rebase_fetchOff_258 blkPC03_rebase_fetchOff_260
  blkPl03_ρ cells32_entails_memRegion seg1_hash_prep seg1_prologue sha3_512List_length)

/-!
# `encapsulate1_serialized` (`B03`) — Segment 1 (`+0x0000 .. +0x0268 → +0x0504`)

Completes `Seg1` after `Seg1a`: steps `bl B00` (`+0x00f8 → +0x00fc`), stores `G(m || H(pk))` at
`sp + 6768`, zeroes `[sp + 4272, sp + 5808)` via `32 × str q0` + `B29`, copies into `aTrans[0..3)`
via `3 × B28` (`+0x00fc → +0x01f4`), stages `Seg2ConstsLo`, `Seg2SeedConsts`, and `Seg2RegInv`
(`+0x01f4 → +0x0504`), and exports `seg1_wp`.
-/

private theorem seq_roOk [MlKemPlacement] {prog : Program} {mid target : BitVec 64} {s : State}
    {P : SepProp} {post : State → SepProp → Prop}
    (hro : MlKemRoOk mlkemMpl s.mem)
    (h : SepWP prog mid s P (fun sm Pm => MlKemRoOk mlkemMpl sm.mem → SepWP prog target sm Pm post)) :
    SepWP prog target s P post :=
  SepWP.seq
    (SepWP.mono_frozen
      (post' := fun sm Pm =>
        MlKemRoOk mlkemMpl sm.mem ∧ (MlKemRoOk mlkemMpl sm.mem → SepWP prog target sm Pm post))
      (Φ := MlKemRoOk mlkemMpl)
      (fun _ _ hr hkf => hr.of_keepsFrozen hkf)
      hro h
      (fun _ _ _ _ hr hk => ⟨hr, hk⟩))
    (fun _ _ _ _ ⟨hr, hk⟩ => hk hr)

local macro "step_strQ0 " k:num : tactic => `(tactic| (
  apply step_strQ128
  · wp_norm_lhs
  · first | wp_norm_lhs | simp [*]
  · wp_norm_lhs
  · first | rfl | wp_norm_lhs | wp_norm_goal | simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, *]
  · wp_norm_lhs
  · wp_norm_lhs
  · apply SepStore128.left; apply SepStore128.vec32 (k := $k)
    · decide
    · bv_omega
    · rfl
  · wp_norm_lhs
  intro _))

private theorem orr_11_of_aligned16 (x : BitVec 64) (hx : (x &&& 15#64 == 0#64) = true) :
    (x ||| 11#64) = x + 11#64 := by
  have hx0 : x &&& 15#64 = 0#64 := of_decide_eq_true hx
  have h15 : (15#64 &&& 11#64 : BitVec 64) = 11#64 := by decide
  have hdisj : x &&& 11#64 = 0#64 := by
    rw [← h15, ← BitVec.and_assoc, hx0]
    decide
  exact (BitVec.add_eq_or_of_and_eq_zero x 11#64 hdisj).symm

private theorem vec4_cells_eq_bytes (ptr : BitVec 64) {bs : List (BitVec 8)} (h : bs.length = 64) :
    let v0 := bytesToVecNat bs 0
    let v1 := bytesToVecNat bs 1
    let v2 := bytesToVecNat bs 2
    let v3 := bytesToVecNat bs 3
    ((ptr ↦₆₄ v0.extractLsb' 0 64) ∗ ((ptr + 8#64) ↦₆₄ v0.extractLsb' 64 64) ∗
      ((ptr + 16#64) ↦₆₄ v1.extractLsb' 0 64) ∗ ((ptr + 24#64) ↦₆₄ v1.extractLsb' 64 64) ∗
      ((ptr + 32#64) ↦₆₄ v2.extractLsb' 0 64) ∗ ((ptr + 40#64) ↦₆₄ v2.extractLsb' 64 64) ∗
      ((ptr + 48#64) ↦₆₄ v3.extractLsb' 0 64) ∗ ((ptr + 56#64) ↦₆₄ v3.extractLsb' 64 64)) =
      (ptr ↦ₛ bs) := by
  intro v0 v1 v2 v3
  rw [pointsToBytes_eq_vecRangeMem 4 ptr h]
  dsimp only [VecRangeMem, Vec128At, v0, v1, v2, v3, Nat.zero_add]
  simp only [show (ptr + 16#64) + 8#64 = ptr + 24#64 by bv_omega,
    show (ptr + 16#64) + 16#64 = ptr + 32#64 by bv_omega,
    show (ptr + 32#64) + 8#64 = ptr + 40#64 by bv_omega,
    show (ptr + 32#64) + 16#64 = ptr + 48#64 by bv_omega,
    show (ptr + 48#64) + 8#64 = ptr + 56#64 by bv_omega]
  exact sepProp_ext (by sep_frame) (by sep_frame)

/-! ## 1. `B00` Call (`+0x00f8 → +0x00fc`) -/

private theorem seg1_b00_call [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (sm : State) (sp : BitVec 64) (a : MlkemBlk03Args) (F : SepProp)
    (hhdr : a.hdr64.length = 64) (hrand : a.rand.length = 32)
    (hpc : sm.pc = b + 0x00f8#64) (hrun : sm.status = .Running)
    (hsp : sm.sp = sp) (hsp_al : sm.spAligned = true)
    (hx0 : sm.readReg64 .x0 = sp + 13984#64)
    (hx1 : sm.readReg64 .x1 = sp + 4272#64)
    (hx2 : sm.readReg64 .x2 = sp + 6832#64)
    (hx19 : sm.readReg64 .x19 = sp + 13984#64)
    (hx20 : sm.readReg64 .x20 = sp + 4272#64)
    (hx21 : sm.readReg64 .x21 = a.hdrA)
    (hx22 : sm.readReg64 .x22 = sp + 6832#64)
    (hx23 : sm.readReg64 .x23 = sp + 2456#64)
    (hx24 : sm.readReg64 (.gpr 24#5) = sp + 2192#64)
    (hx25 : sm.readReg64 (.gpr 25#5) = sp + 14248#64)
    (hx28 : sm.readReg64 .x28 = sp + 13984#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl sm.mem)
    (hro : MlKemRoOk mlkemMpl sm.mem) :
    let msg := a.rand ++ a.hdr64.drop 32
    SepWP (blkPC03.rebase b (fun _ => none)) (b + 0x00fc#64) sm
      (Keccak2SlicesRW (sp + 13984#64) (sp + 2192#64) (sp + 2192#64) msg.length msg.length ∗
        ((sp + 2192#64) ↦ₛ msg) ∗
        memRegion (sp + 4272#64) 64 ∗
        memRegion (sp + 6832#64) 64 ∗
        stackAt sp 1136 ∗ F)
      (fun sk Pk =>
        sk.sp = sp ∧ sk.spAligned = true ∧
        sk.readReg64 .x19 = sp + 13984#64 ∧
        sk.readReg64 .x20 = sp + 4272#64 ∧
        sk.readReg64 .x21 = a.hdrA ∧
        sk.readReg64 .x22 = sp + 6832#64 ∧
        sk.readReg64 .x23 = sp + 2456#64 ∧
        sk.readReg64 (.gpr 24#5) = sp + 2192#64 ∧
        sk.readReg64 (.gpr 25#5) = sp + 14248#64 ∧
        sk.readReg64 .x28 = sp + 13984#64 ∧
        (Pk ⊢ ((sp + 4272#64) ↦ₛ sha3_512List msg) ∗
          memRegion (sp + 2192#64) 64 ∗
          memRegion (sp + 6832#64) 64 ∗
          memRegion (sp + 13984#64) 32 ∗
          stackAt sp 1136 ∗ F)) := by
  intro msg
  subst hbase
  have hmsg_len : msg.length = 64 := by simp [msg, hrand, hhdr]
  have hmsg_lt : msg.length < 72 := by omega
  rw [stackAt_shrink sp 1136 720 (by decide)]
  wp_step
  have hro' : MlKemRoOk mlkemMpl
      ((sm.writeReg64 .lr (blkPl03.base + 252#64)).setPC (mlkemMpl.base 0)).mem := hro
  wp_mlkem_call blk00_keccak2_72_6_RW1_ok
    (sp + 13984#64, sp + 2192#64, sp + 4272#64, sp + 6832#64, msg)
  refine SepWP.done hpc_sf hrun_sf
    ⟨hsp_sf.trans hsp, spAligned_of_sp_eq hsp_al hsp (hsp_sf.trans hsp),
      Eq.trans ‹_› hx19, Eq.trans ‹_› hx20, Eq.trans ‹_› hx21, Eq.trans ‹_› hx22,
      Eq.trans ‹_› hx23, Eq.trans ‹_› hx24, Eq.trans ‹_› hx25, Eq.trans ‹_› hx28, ?_⟩
  rw [hsp]
  have hsl : Keccak2SlicesRW (sp + 13984#64) (sp + 2192#64) (sp + 2192#64)
      msg.length msg.length ⊢ memRegion (sp + 13984#64) 32 := by
    unfold Keccak2SlicesRW
    exact cells32_entails_memRegion (sp + 13984#64) _ _ _ _
  have hm_ent : ((sp + 2192#64) ↦ₛ msg) ⊢ memRegion (sp + 2192#64) 64 := by
    simpa [hmsg_len] using pointsToBytes_entails_memRegion (sp + 2192#64) msg
  have ho1 : ((sp + 6832#64) ↦ₛ sha3_512List msg) ⊢ memRegion (sp + 6832#64) 64 := by
    simpa [sha3_512List_length] using pointsToBytes_entails_memRegion (sp + 6832#64) (sha3_512List msg)
  exact entails_sub hsl (by sep_frame)
    (entails_sub hm_ent (by sep_frame)
      (entails_sub ho1 (by sep_frame) (by sep_frame)))


/-! ## 2. Store `hashed`, Zero Scratch, & Initialize `aTrans` (`+0x00fc → +0x01f4`) -/

private theorem seg1_copy_zero_a [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (sk : State) (sp : BitVec 64) (hashed : List (BitVec 8)) (Rest : SepProp)
    (hhashed : hashed.length = 64)
    (hpc : sk.pc = b + 0x00fc#64) (hrun : sk.status = .Running)
    (hsp : sk.sp = sp) (hsp_al : sk.spAligned = true) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + 0x01b0#64) sk
      (((sp + 4272#64) ↦ₛ hashed) ∗
        memRegion (sp + 4336#64) 1472 ∗
        memRegion (sp + 6768#64) 64 ∗ Rest)
      (fun sz Pz =>
        sz.sp = sp ∧ sz.spAligned = true ∧
        sz.readReg64 .x0 = sp + 4272#64 ∧
        sz.readReg32 .x1 = 0#32 ∧
        sz.readReg64 .x2 = 1024#64 ∧
        sz.readReg64 .x19 = sk.readReg64 .x19 ∧
        sz.readReg64 .x20 = sk.readReg64 .x20 ∧
        sz.readReg64 .x21 = sk.readReg64 .x21 ∧
        sz.readReg64 .x22 = sk.readReg64 .x22 ∧
        sz.readReg64 .x23 = sk.readReg64 .x23 ∧
        sz.readReg64 (.gpr 24#5) = sk.readReg64 (.gpr 24#5) ∧
        sz.readReg64 (.gpr 25#5) = sk.readReg64 (.gpr 25#5) ∧
        sz.readReg64 .x28 = sk.readReg64 .x28 ∧
        (Pz ⊢ memRegion (sp + 4272#64) 1024 ∗
          ((sp + 5296#64) ↦ₛ vecRangeBytes 32 Vec32.zero.get) ∗
          ((sp + 6768#64) ↦ₛ hashed) ∗ Rest)) := by
  subst hbase
  have hal_sp : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hsp_al
  rw [memRegion_split' (b := sp + 4336#64) (b' := sp + 5296#64) (n := 960) (k := 512) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 6768#64) (b' := sp + 6800#64) (n := 32) (k := 32) rfl (by bv_omega) (by decide)]
  sep_frame_apply (sepWP_elim_region32 (a := sp + 6768#64)); intro d0 d1 d2 d3
  sep_frame_apply (sepWP_elim_region32 (a := sp + 6800#64)); intro d4 d5 d6 d7
  rw [← vec4_cells_eq_bytes (sp + 4272#64) hhashed]
  simp only [show sp + 4272#64 + 8#64 = sp + 4280#64 by bv_omega,
    show sp + 4272#64 + 16#64 = sp + 4288#64 by bv_omega,
    show sp + 4272#64 + 24#64 = sp + 4296#64 by bv_omega,
    show sp + 4272#64 + 32#64 = sp + 4304#64 by bv_omega,
    show sp + 4272#64 + 40#64 = sp + 4312#64 by bv_omega,
    show sp + 4272#64 + 48#64 = sp + 4320#64 by bv_omega,
    show sp + 4272#64 + 56#64 = sp + 4328#64 by bv_omega,
    show sp + 6768#64 + 8#64 = sp + 6776#64 by bv_omega,
    show sp + 6768#64 + 16#64 = sp + 6784#64 by bv_omega,
    show sp + 6768#64 + 24#64 = sp + 6792#64 by bv_omega,
    show sp + 6800#64 + 8#64 = sp + 6808#64 by bv_omega,
    show sp + 6800#64 + 16#64 = sp + 6816#64 by bv_omega,
    show sp + 6800#64 + 24#64 = sp + 6824#64 by bv_omega]
  wp_steps 13
  apply SepWP.of_memRegion_vecRangeMem 32 (sp + 5296#64) (hf := by sep_focus)
  intro f
  rw [show VecRangeMem 32 (sp + 5296#64) f = PolyMem (sp + 5296#64) f from rfl, ← poly32Mem_ofFn]
  step_strQ0 31; step_strQ0 30; step_strQ0 29; step_strQ0 28
  step_strQ0 27; step_strQ0 26; step_strQ0 25; step_strQ0 24
  step_strQ0 23; step_strQ0 22; step_strQ0 21; step_strQ0 20
  step_strQ0 19; step_strQ0 18; step_strQ0 17; step_strQ0 16
  step_strQ0 15; step_strQ0 14; step_strQ0 13; step_strQ0 12
  step_strQ0 11; step_strQ0 10; step_strQ0 9; step_strQ0 8
  step_strQ0 7; step_strQ0 6; step_strQ0 5; step_strQ0 4
  step_strQ0 3; step_strQ0 2; step_strQ0 1; step_strQ0 0
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], spAligned_of_sp_eq hsp_al hsp (by simp [hsp]),
      by wp_norm_lhs, by wp_norm_lhs, by simp,
      by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp, ?_⟩
  have htrunc (v : BitVec 128) : v.truncate 64 = v.extractLsb' 0 64 := by bv_bits
  simp only [htrunc, Vec32.set, Vec32.zero, Vec32.ofFn, poly32Mem_eq_pointsToBytes]
  have hd_pts := vec4_cells_eq_bytes (sp + 6768#64) hhashed
  simp only [show sp + 6768#64 + 8#64 = sp + 6776#64 by bv_omega,
    show sp + 6768#64 + 16#64 = sp + 6784#64 by bv_omega,
    show sp + 6768#64 + 24#64 = sp + 6792#64 by bv_omega,
    show sp + 6768#64 + 32#64 = sp + 6800#64 by bv_omega,
    show sp + 6768#64 + 40#64 = sp + 6808#64 by bv_omega,
    show sp + 6768#64 + 48#64 = sp + 6816#64 by bv_omega,
    show sp + 6768#64 + 56#64 = sp + 6824#64 by bv_omega] at hd_pts
  have hc1024 :
      ((sp + 4272#64) ↦₆₄ (bytesToVecNat hashed 0).extractLsb' 0 64) ∗
        ((sp + 4280#64) ↦₆₄ (bytesToVecNat hashed 0).extractLsb' 64 64) ∗
        ((sp + 4288#64) ↦₆₄ (bytesToVecNat hashed 1).extractLsb' 0 64) ∗
        ((sp + 4296#64) ↦₆₄ (bytesToVecNat hashed 1).extractLsb' 64 64) ∗
        ((sp + 4304#64) ↦₆₄ (bytesToVecNat hashed 2).extractLsb' 0 64) ∗
        ((sp + 4312#64) ↦₆₄ (bytesToVecNat hashed 2).extractLsb' 64 64) ∗
        ((sp + 4320#64) ↦₆₄ (bytesToVecNat hashed 3).extractLsb' 0 64) ∗
        ((sp + 4328#64) ↦₆₄ (bytesToVecNat hashed 3).extractLsb' 64 64) ∗
        memRegion (sp + 4336#64) 960 ⊢
      memRegion (sp + 4272#64) 1024 := by
    rw [memRegion_split' (b' := sp + 4304#64) (n := 32) (k := 992) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp + 4336#64) (n := 32) (k := 960) rfl (by bv_omega) (by decide)]
    have hc1 := cells32_entails_memRegion (sp + 4272#64)
      ((bytesToVecNat hashed 0).extractLsb' 0 64)
      ((bytesToVecNat hashed 0).extractLsb' 64 64)
      ((bytesToVecNat hashed 1).extractLsb' 0 64)
      ((bytesToVecNat hashed 1).extractLsb' 64 64)
    have hc2 := cells32_entails_memRegion (sp + 4304#64)
      ((bytesToVecNat hashed 2).extractLsb' 0 64)
      ((bytesToVecNat hashed 2).extractLsb' 64 64)
      ((bytesToVecNat hashed 3).extractLsb' 0 64)
      ((bytesToVecNat hashed 3).extractLsb' 64 64)
    simp only [show sp + 4272#64 + 8#64 = sp + 4280#64 by bv_omega,
      show sp + 4272#64 + 16#64 = sp + 4288#64 by bv_omega,
      show sp + 4272#64 + 24#64 = sp + 4296#64 by bv_omega] at hc1
    simp only [show sp + 4304#64 + 8#64 = sp + 4312#64 by bv_omega,
      show sp + 4304#64 + 16#64 = sp + 4320#64 by bv_omega,
      show sp + 4304#64 + 24#64 = sp + 4328#64 by bv_omega] at hc2
    exact entails_sub hc1 (by sep_frame) (entails_sub hc2 (by sep_frame) (by sep_frame))
  conv_rhs => rw [← hd_pts]
  exact entails_sub hc1024 (by sep_frame) (by sep_frame)

private theorem seg1_copy_zero_b [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (sz : State) (sp : BitVec 64) (Rest : SepProp)
    (hpc : sz.pc = b + 0x01b0#64) (hrun : sz.status = .Running)
    (hsp : sz.sp = sp) (hsp_al : sz.spAligned = true)
    (hx0 : sz.readReg64 .x0 = sp + 4272#64)
    (hx1 : sz.readReg32 .x1 = 0#32)
    (hx2 : sz.readReg64 .x2 = 1024#64)
    (hx22 : sz.readReg64 .x22 = sp + 6832#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl sz.mem) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + 0x01f4#64) sz
      (memRegion (sp + 4272#64) 1024 ∗
        ((sp + 5296#64) ↦ₛ vecRangeBytes 32 Vec32.zero.get) ∗
        memRegion (sp + 6832#64) 4608 ∗ Rest)
      (fun sc Pc =>
        sc.sp = sp ∧ sc.spAligned = true ∧
        sc.readReg64 .x19 = sz.readReg64 .x19 ∧
        sc.readReg64 .x20 = sz.readReg64 .x20 ∧
        sc.readReg64 .x21 = sz.readReg64 .x21 ∧
        sc.readReg64 .x23 = sz.readReg64 .x23 ∧
        sc.readReg64 (.gpr 24#5) = sz.readReg64 (.gpr 24#5) ∧
        sc.readReg64 (.gpr 25#5) = sz.readReg64 (.gpr 25#5) ∧
        sc.readReg64 .x28 = sz.readReg64 .x28 ∧
        (Pc ⊢ memRegion (sp + 4272#64) 1536 ∗
          memRegion (sp + 6832#64) 4608 ∗ Rest)) := by
  subst hbase
  let z1536 := List.replicate 1024 0#8 ++ vecRangeBytes 32 Vec32.zero.get
  have hz_len : z1536.length = 1536 := by
    dsimp only [z1536]
    rw [List.length_append, List.length_replicate, vecRangeBytes_length]
  have hz_join :
      ((sp + 4272#64) ↦ₛ z1536) =
        ((sp + 4272#64) ↦ₛ List.replicate 1024 0#8) ∗
          ((sp + 5296#64) ↦ₛ vecRangeBytes 32 Vec32.zero.get) := by
    dsimp only [z1536]
    rw [pointsToBytes_append, List.length_replicate,
      show sp + 4272#64 + BitVec.ofNat 64 1024 = sp + 5296#64 by bv_omega]
  rw [memRegion_split' (b := sp + 6832#64) (b' := sp + 8368#64) (n := (1536 : Nat)) (k := (3072 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 8368#64) (b' := sp + 9904#64) (n := (1536 : Nat)) (k := (1536 : Nat)) rfl (by bv_omega) (by decide)]
  wp_cut_codeLoaded; wp_step
  wp_mlkem_call blk29_memset_ok (sp + 4272#64, 0#8, (1024 : Nat))
  have hx22_1 : sf.readReg64 .x22 = sp + 6832#64 := Eq.trans ‹_› hx22
  have hsp_al1 : sf.spAligned = true := spAligned_of_sp_eq hsp_al hsp (hsp_sf.trans hsp)
  refine SepWP.weaken_pre (P' :=
      memRegion (sp + 6832#64) z1536.length ∗
        ((sp + 4272#64) ↦ₛ z1536) ∗
        memRegion (sp + 8368#64) z1536.length ∗
        memRegion (sp + 9904#64) z1536.length ∗ Rest)
    (by rw [hz_len, hz_join]; sep_frame) ?_
  wp_cut_codeLoaded; wp_steps
  wp_mlkem_call blk28_memcpy_ok (sp + 6832#64, sp + 4272#64, z1536)
  have hx22_2 : sf_1.readReg64 .x22 = sp + 6832#64 := Eq.trans ‹_› hx22_1
  have hsp_al2 : sf_1.spAligned = true := spAligned_of_sp_eq hsp_al1 (hsp_sf.trans hsp) (hsp_sf_1.trans (hsp_sf.trans hsp))
  wp_cut_codeLoaded; wp_steps
  wp_mlkem_call blk28_memcpy_ok (sp + 8368#64, sp + 4272#64, z1536)
  have hx22_3 : sf_2.readReg64 .x22 = sp + 6832#64 := Eq.trans ‹_› hx22_2
  have hsp_al3 : sf_2.spAligned = true := spAligned_of_sp_eq hsp_al2 (hsp_sf_1.trans (hsp_sf.trans hsp)) (hsp_sf_2.trans (hsp_sf_1.trans (hsp_sf.trans hsp)))
  wp_cut_codeLoaded; wp_steps
  wp_mlkem_call blk28_memcpy_ok (sp + 9904#64, sp + 4272#64, z1536)
  have hsp_fin : sf_3.sp = sp := hsp_sf_3.trans (hsp_sf_2.trans (hsp_sf_1.trans (hsp_sf.trans hsp)))
  refine SepWP.done hpc_sf_3 hrun_sf_3
    ⟨hsp_fin, spAligned_of_sp_eq hsp_al hsp hsp_fin,
      by simp [*], by simp [*], by simp [*], by simp [*],
      by simp [*], by simp [*], by simp [*], ?_⟩
  have he0 : ((sp + 4272#64) ↦ₛ z1536) ⊢ memRegion (sp + 4272#64) 1536 := by
    simpa [hz_len] using pointsToBytes_entails_memRegion (sp + 4272#64) z1536
  have he1 : ((sp + 6832#64) ↦ₛ z1536) ⊢ memRegion (sp + 6832#64) 1536 := by
    simpa [hz_len] using pointsToBytes_entails_memRegion (sp + 6832#64) z1536
  have he2 : ((sp + 8368#64) ↦ₛ z1536) ⊢ memRegion (sp + 8368#64) 1536 := by
    simpa [hz_len] using pointsToBytes_entails_memRegion (sp + 8368#64) z1536
  have he3 : ((sp + 9904#64) ↦ₛ z1536) ⊢ memRegion (sp + 9904#64) 1536 := by
    simpa [hz_len] using pointsToBytes_entails_memRegion (sp + 9904#64) z1536
  exact entails_sub he0 (by sep_frame)
    (entails_sub he1 (by sep_frame)
      (entails_sub he2 (by sep_frame)
        (entails_sub he3 (by sep_frame) (by sep_frame))))


/-! ## 3. Stage `Seg2` Constants & Registers (`+0x01f4 → +0x0504`) and Compose `seg1_wp` -/

@[simp] private theorem extractLsb64_lo_append (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 0 64 = lo := by bv_bits

@[simp] private theorem extractLsb64_hi_append (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 64 64 = hi := by bv_bits

@[simp] private theorem truncate64_append (hi lo : BitVec 64) :
    (hi ++ lo).truncate 64 = lo := by bv_bits

private theorem vec2_cells_eq_bytes (ptr : BitVec 64) {bs : List (BitVec 8)} (h : bs.length = 32) :
    let v0 := bytesToVecNat bs 0
    let v1 := bytesToVecNat bs 1
    ((ptr ↦₆₄ v0.extractLsb' 0 64) ∗ ((ptr + 8#64) ↦₆₄ v0.extractLsb' 64 64) ∗
      ((ptr + 16#64) ↦₆₄ v1.extractLsb' 0 64) ∗ ((ptr + 24#64) ↦₆₄ v1.extractLsb' 64 64)) =
      (ptr ↦ₛ bs) := by
  intro v0 v1
  rw [pointsToBytes_eq_vecRangeMem 2 ptr h]
  dsimp only [VecRangeMem, Vec128At, v0, v1, Nat.zero_add]
  rw [show (ptr + 16#64) + 8#64 = ptr + 24#64 by bv_omega]
  exact sepProp_ext (by sep_frame) (by sep_frame)

attribute [local irreducible] blkLib03

private theorem seg1_consts_a [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (sc : State) (sp : BitVec 64) (a : MlkemBlk03Args) (Rest : SepProp)
    (hhdr : a.hdr64.length = 64)
    (hpc : sc.pc = b + 0x01f4#64) (hrun : sc.status = .Running)
    (hsp : sc.sp = sp) (hsp_al : sc.spAligned = true)
    (hx19 : sc.readReg64 .x19 = sp + 13984#64)
    (hx20 : sc.readReg64 .x20 = sp + 4272#64)
    (hx21 : sc.readReg64 .x21 = a.hdrA)
    (hx23 : sc.readReg64 .x23 = sp + 2456#64)
    (hx24 : sc.readReg64 (.gpr 24#5) = sp + 2192#64)
    (hx25 : sc.readReg64 (.gpr 25#5) = sp + 14248#64)
    (hx28 : sc.readReg64 .x28 = sp + 13984#64) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + 0x023c#64) sc
      (memRegion (sp + 40#64) 8 ∗ memRegion (sp + 88#64) 8 ∗
        memRegion (sp + 384#64) 32 ∗ (a.hdrA ↦ₛ a.hdr64) ∗ Rest)
      (fun s1 P1 =>
        s1.sp = sp ∧ s1.spAligned = true ∧
        s1.readReg64 .x8 = 0#64 ∧
        s1.readReg64 .x9 = pageOf (mlkemMpl.ρ "libcrux_ml_kem:.rodata.cst16.0") ∧
        s1.readReg64 .x10 = pageOf (mlkemMpl.ρ "libcrux_ml_kem:.rodata.cst16.1") ∧
        s1.readReg64 .x19 =
          mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29" ∧
        s1.readReg64 .x20 = sp + 4272#64 ∧
        s1.readReg64 .x21 = sp + 12448#64 ∧
        s1.readReg64 .x23 = sp + 2456#64 ∧
        s1.readReg64 (.gpr 24#5) = 544#64 ∧
        s1.readReg64 (.gpr 25#5) = sp + 14248#64 ∧
        s1.readReg64 (.gpr 26#5) = (sp + 13984#64) + 11#64 ∧
        s1.readReg64 .x28 = sp + 13984#64 ∧
        s1.readVReg128 1#5 =
          (bytesToVecNat (a.hdr64.take 32) 1).extractLsb' 64 64 ++
            (bytesToVecNat (a.hdr64.take 32) 1).truncate 64 ∧
        (P1 ⊢ ((sp + 40#64) ↦₆₄ (sp + 3496#64)) ∗
          ((sp + 88#64) ↦₆₄ ((sp + 2192#64) + 11#64)) ∗
          Vec128At (sp + 384#64)
            (ByteSlice.readLE (a.hdr64.take 32) 8 8 ++ ByteSlice.readLE (a.hdr64.take 32) 8 8) ∗
          Vec128At (sp + 400#64)
            (ByteSlice.readLE (a.hdr64.take 32) 0 8 ++ ByteSlice.readLE (a.hdr64.take 32) 0 8) ∗
          (a.hdrA ↦ₛ a.hdr64) ∗ Rest)) := by
  subst hbase
  have hal_sp : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hsp_al
  have hal2192 : ((sp + 2192#64) &&& 15#64 == 0#64) = true := by
    simpa [show sp - (-2192#64) = sp + 2192#64 by clear *- ; bv_omega] using
      spAligned_sub sp (-2192#64) hal_sp (by decide)
  have hal13984 : ((sp + 13984#64) &&& 15#64 == 0#64) = true := by
    simpa [show sp - (-13984#64) = sp + 13984#64 by clear *- ; bv_omega] using
      spAligned_sub sp (-13984#64) hal_sp (by decide)
  have horr1 : ((sp + 2192#64) ||| 11#64) = (sp + 2192#64) + 11#64 := orr_11_of_aligned16 _ hal2192
  have horr2 : ((sp + 13984#64) ||| 11#64) = (sp + 13984#64) + 11#64 := orr_11_of_aligned16 _ hal13984
  have o384_8 : sp + 384#64 + 8#64 = sp + 392#64 := by clear *- ; bv_omega
  have o384_16 : sp + 384#64 + 16#64 = sp + 400#64 := by clear *- ; bv_omega
  have o384_24 : sp + 384#64 + 24#64 = sp + 408#64 := by clear *- ; bv_omega
  have o400_8 : sp + 400#64 + 8#64 = sp + 408#64 := by clear *- ; bv_omega
  have htake_len : (a.hdr64.take 32).length = 32 := by simp [hhdr]
  have hhdr_split : (a.hdrA ↦ₛ a.hdr64) =
      (a.hdrA ↦ₛ a.hdr64.take 32) ∗ ((a.hdrA + 32#64) ↦ₛ a.hdr64.drop 32) := by
    conv_lhs => rw [← List.take_append_drop 32 a.hdr64]
    rw [pointsToBytes_append, htake_len]
  sep_frame_apply (sepWP_elim_cell8 (a := sp + 40#64)); intro c40
  sep_frame_apply (sepWP_elim_cell8 (a := sp + 88#64)); intro c88
  generalize hv0 : bytesToVecNat (a.hdr64.take 32) 0 = qv0
  generalize hv1 : bytesToVecNat (a.hdr64.take 32) 1 = qv1
  refine SepWP.seq
    (?_ : SepWP _ (blkPl03.base + 544#64) _ _ (fun sm Pm =>
      sm.sp = sp ∧ sm.spAligned = true ∧
      sm.readReg64 .x9 = pageOf (mlkemMpl.ρ "libcrux_ml_kem:.rodata.cst16.0") ∧
      sm.readReg64 .x20 = sp + 4272#64 ∧
      sm.readReg64 .x21 = sp + 12288#64 ∧
      sm.readReg64 .x23 = sp + 2456#64 ∧
      sm.readReg64 (.gpr 25#5) = sp + 14248#64 ∧
      sm.readReg64 (.gpr 26#5) = (sp + 13984#64) + 11#64 ∧
      sm.readReg64 .x28 = sp + 13984#64 ∧
      sm.readVReg128 0#5 = qv0.extractLsb' 64 64 ++ qv0.extractLsb' 64 64 ∧
      sm.readVReg128 1#5 = qv1.extractLsb' 64 64 ++ qv1.truncate 64 ∧
      sm.readVReg128 2#5 = qv0.truncate 64 ++ qv0.truncate 64 ∧
      (Pm ⊢ ((sp + 40#64) ↦₆₄ (sp + 3496#64)) ∗
        ((sp + 88#64) ↦₆₄ ((sp + 2192#64) + 11#64)) ∗
        memRegion (sp + 384#64) 32 ∗ (a.hdrA ↦ₛ a.hdr64) ∗ Rest)))
    ?_
  · refine SepWP.weaken_pre
      (P' := ((sp + 40#64) ↦₆₄ c40) ∗ ((sp + 88#64) ↦₆₄ c88) ∗
        memRegion (sp + 384#64) 32 ∗
        ((a.hdrA ↦₆₄ qv0.extractLsb' 0 64) ∗ ((a.hdrA + 8#64) ↦₆₄ qv0.extractLsb' 64 64) ∗
         ((a.hdrA + 16#64) ↦₆₄ qv1.extractLsb' 0 64) ∗ ((a.hdrA + 24#64) ↦₆₄ qv1.extractLsb' 64 64)) ∗
        ((a.hdrA + 32#64) ↦ₛ a.hdr64.drop 32) ∗ Rest)
      (by subst hv0 hv1; rw [hhdr_split, ← vec2_cells_eq_bytes a.hdrA htake_len]; sep_frame) ?_
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp [hsp], spAligned_of_sp_eq hsp_al hsp (by simp [hsp]),
        by wp_norm_lhs,
        by simp [hx20],
        by wp_norm_lhs,
        by simp [hx23],
        by simp [hx25],
        by simp,
        by simp [hx28],
        by simp,
        by simp,
        by simp, ?_⟩
    subst hv0 hv1
    rw [hhdr_split, ← vec2_cells_eq_bytes a.hdrA htake_len]
    have o2203 : sp + 2203#64 = (sp + 2192#64) + 11#64 := by clear *- ; bv_omega
    simp only [o2203]
    sep_frame
  rintro sm Pm hpcm hrunm
    ⟨hspm, hsp_alm, hx9m, hx20m, hx21m, hx23m, hx25m, hx26m, hx28m, hv0m, hv1m, hv2m, hPm⟩
  refine SepWP.weaken_pre hPm ?_
  sep_frame_apply (sepWP_elim_region32 (a := sp + 384#64)); intro d4 d5 d6 d7
  simp only [o384_8, o384_16, o384_24]
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by simp [hrunm])
    ⟨by simp [hspm], spAligned_of_sp_eq hsp_alm hspm (by simp [hspm]),
      by simp,
      by simp [hx9m],
      by wp_norm_lhs,
      by wp_norm_lhs,
      by simp [hx20m],
      by wp_norm_lhs,
      by simp [hx23m],
      by simp,
      by simp [hx25m],
      by simp [hx26m],
      by simp [hx28m],
      by simp [hv1m], ?_⟩
  subst hv0 hv1
  have htrunc (v : BitVec 128) : v.truncate 64 = v.extractLsb' 0 64 := by bv_bits
  dsimp only [Vec128At, bytesToVecNat]
  simp only [htrunc, extractLsb64_lo_append, extractLsb64_hi_append,
    o384_8, o400_8, Nat.mul_zero, Nat.zero_add]
  generalize ByteSlice.readLE (a.hdr64.take 32) 0 8 = s0w
  generalize ByteSlice.readLE (a.hdr64.take 32) 8 8 = s1w
  sep_frame

private theorem seg1_consts [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (sc : State) (sp : BitVec 64) (a : MlkemBlk03Args) (Rest : SepProp)
    (hhdr : a.hdr64.length = 64)
    (hpc : sc.pc = b + 0x01f4#64) (hrun : sc.status = .Running)
    (hsp : sc.sp = sp) (hsp_al : sc.spAligned = true)
    (hx19 : sc.readReg64 .x19 = sp + 13984#64)
    (hx20 : sc.readReg64 .x20 = sp + 4272#64)
    (hx21 : sc.readReg64 .x21 = a.hdrA)
    (hx23 : sc.readReg64 .x23 = sp + 2456#64)
    (hx24 : sc.readReg64 (.gpr 24#5) = sp + 2192#64)
    (hx25 : sc.readReg64 (.gpr 25#5) = sp + 14248#64)
    (hx28 : sc.readReg64 .x28 = sp + 13984#64)
    (hro : MlKemRoOk mlkemMpl sc.mem) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + 0x0504#64) sc
      (memRegion (sp + 40#64) 8 ∗ memRegion (sp + 48#64) 32 ∗
        memRegion (sp + 88#64) 8 ∗ memRegion (sp + 336#64) 16 ∗
        memRegion (sp + 352#64) 32 ∗ memRegion (sp + 384#64) 32 ∗
        (a.hdrA ↦ₛ a.hdr64) ∗ Rest)
      (fun s2 P2 =>
        Seg2RegInv sp s2 ∧ s2.readReg64 .x8 = 0#64 ∧
        (P2 ⊢ Seg2ConstsLo sp ∗ Seg2SeedConsts sp (a.hdr64.take 32) ∗
          (a.hdrA ↦ₛ a.hdr64) ∗ Rest)) := by
  let midRest := memRegion (sp + 48#64) 32 ∗ memRegion (sp + 336#64) 16 ∗
    memRegion (sp + 352#64) 32 ∗ Rest
  refine SepWP.weaken_pre
    (P' := memRegion (sp + 40#64) 8 ∗ memRegion (sp + 88#64) 8 ∗
      memRegion (sp + 384#64) 32 ∗ (a.hdrA ↦ₛ a.hdr64) ∗ midRest)
    (by dsimp only [midRest]; sep_frame) ?_
  refine seq_roOk (mid := b + 0x023c#64) hro ?_
  refine SepWP.mono
    (seg1_consts_a hb hbase sc sp a midRest hhdr hpc hrun hsp hsp_al
      hx19 hx20 hx21 hx23 hx24 hx25 hx28) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hsp1, hsp_al1, hx8_1, hx9_1, hx10_1, hx19_1, hx20_1, hx21_1,
    hx23_1, hx24_1, hx25_1, hx26_1, hx28_1, hq1_1, hP1⟩ hro1
  subst hbase
  have o48_8 : sp + 48#64 + 8#64 = sp + 56#64 := by clear *- ; bv_omega
  have o48_16 : sp + 48#64 + 16#64 = sp + 64#64 := by clear *- ; bv_omega
  have o48_24 : sp + 48#64 + 24#64 = sp + 72#64 := by clear *- ; bv_omega
  have o64_8 : sp + 64#64 + 8#64 = sp + 72#64 := by clear *- ; bv_omega
  have o336_8 : sp + 336#64 + 8#64 = sp + 344#64 := by clear *- ; bv_omega
  have o352_8 : sp + 352#64 + 8#64 = sp + 360#64 := by clear *- ; bv_omega
  have o352_16 : sp + 352#64 + 16#64 = sp + 368#64 := by clear *- ; bv_omega
  have o352_24 : sp + 352#64 + 24#64 = sp + 376#64 := by clear *- ; bv_omega
  have o368_8 : sp + 368#64 + 8#64 = sp + 376#64 := by clear *- ; bv_omega
  have o384_8 : sp + 384#64 + 8#64 = sp + 392#64 := by clear *- ; bv_omega
  have o400_8 : sp + 400#64 + 8#64 = sp + 408#64 := by clear *- ; bv_omega
  generalize hs0w : ByteSlice.readLE (a.hdr64.take 32) 0 8 = s0w at hP1
  generalize hs1w : ByteSlice.readLE (a.hdr64.take 32) 8 8 = s1w at hP1
  let Tail := ((sp + 40#64) ↦₆₄ (sp + 3496#64)) ∗
    ((sp + 88#64) ↦₆₄ ((sp + 2192#64) + 11#64)) ∗
    Vec128At (sp + 384#64) (s1w ++ s1w) ∗
    Vec128At (sp + 400#64) (s0w ++ s0w) ∗
    (a.hdrA ↦ₛ a.hdr64) ∗ Rest
  refine SepWP.weaken_pre
    (P' := memRegion (sp + 48#64) 32 ∗ memRegion (sp + 336#64) 16 ∗
      memRegion (sp + 352#64) 32 ∗ Tail)
    (Entails.trans hP1 (by dsimp only [midRest, Tail]; sep_frame)) ?_
  rw [memRegion_split' (b := sp + 336#64) (b' := sp + 344#64) (n := 8) (k := 8) rfl o336_8.symm (by decide)]
  sep_frame_apply (sepWP_elim_region32 (a := sp + 48#64)); intro c48 c56 c64 c72
  sep_frame_apply (sepWP_elim_cell8 (a := sp + 336#64)); intro c336
  sep_frame_apply (sepWP_elim_cell8 (a := sp + 344#64)); intro c344
  sep_frame_apply (sepWP_elim_region32 (a := sp + 352#64)); intro d0 d1 d2 d3
  generalize hv1 : bytesToVecNat (a.hdr64.take 32) 1 = qv1 at hq1_1
  simp only [o48_8, o48_16, o48_24, o352_8, o352_16, o352_24]
  refine seq_roOk (mid := blkPl03.base + 588#64) hro1 ?_
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun1]) (fun hro2 => ?_)
  refine step_ldrQ128_ro (wb := none) (by wp_norm_lhs)
    (by simp [hrun1]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx9_1, pageOf_add_lo12Of])
    hro2.cst16_0 mlkemData02Bytes_length cst16_0_vec (by wp_norm_lhs) ?_
  refine seq_roOk (mid := blkPl03.base + 600#64) (by simpa using hro2) ?_
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun1]) (fun hro3 => ?_)
  refine step_ldrQ128_ro (wb := none) (by wp_norm_lhs)
    (by simp [hrun1]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx10_1, pageOf_add_lo12Of])
    hro3.cst16_1 mlkemData03Bytes_length cst16_1_vec (by wp_norm_lhs) ?_
  refine seq_roOk (mid := blkPl03.base + 608#64) (by simpa using hro3) ?_
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun1]) (fun hro4 => ?_)
  refine step_ldrQ128_ro (wb := none) (by wp_norm_lhs)
    (by simp [hrun1]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, pageOf_add_lo12Of])
    hro4.cst16_2 mlkemData04Bytes_length cst16_2_vec (by wp_norm_lhs) ?_
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun1])
    ⟨⟨by simp [hsp1], spAligned_of_sp_eq hsp_al1 hsp1 (by simp [hsp1]),
      by simp [hx19_1],
      by simp [hx20_1],
      by simp [hx21_1],
      by simp [hx23_1],
      by simp [hx24_1],
      by simp [hx25_1],
      by simp [hx26_1],
      by simp,
      by simp [hx28_1]⟩,
     by simp [hx8_1], ?_⟩
  have htrunc (v : BitVec 128) : v.truncate 64 = v.extractLsb' 0 64 := by bv_bits
  subst hv1
  dsimp only [Tail, bytesToVecNat, Seg2ConstsLo, Seg2SeedConsts, Vec128At]
  rw [hs0w, hs1w]
  simp only [htrunc, extractLsb64_lo_append, extractLsb64_hi_append,
    o48_8, o64_8, o336_8, o352_8, o368_8, o384_8, o400_8,
    Nat.mul_one]
  simp only [
    show (0x000000000000000000000000001f0200#128).extractLsb' 0 64 = 0x00000000001f0200#64 by decide,
    show (0x000000000000000000000000001f0200#128).extractLsb' 64 64 = 0#64 by decide,
    show (0x000000000000000000000000001f0100#128).extractLsb' 0 64 = 0x00000000001f0100#64 by decide,
    show (0x000000000000000000000000001f0100#128).extractLsb' 64 64 = 0#64 by decide,
    show (0xffffffffffffffffffffffffff0000ff#128).extractLsb' 0 64 = 0xffffffffff0000ff#64 by decide,
    show (0xffffffffffffffffffffffffff0000ff#128).extractLsb' 64 64 = 0xffffffffffffffff#64 by decide]
  generalize ByteSlice.readLE (a.hdr64.take 32) 16 8 = s2w
  generalize ByteSlice.readLE (a.hdr64.take 32) 24 8 = s3w
  sep_frame

private theorem frame16864_seg1_split (sp : BitVec 64) :
    memRegion sp 16864 =
      memRegion sp 32 ∗ memRegion (sp + 32#64) 8 ∗
      memRegion (sp + 40#64) 8 ∗ memRegion (sp + 48#64) 32 ∗
      memRegion (sp + 80#64) 8 ∗ memRegion (sp + 88#64) 8 ∗
      memRegion (sp + 96#64) 240 ∗ memRegion (sp + 336#64) 16 ∗
      memRegion (sp + 352#64) 32 ∗ memRegion (sp + 384#64) 32 ∗
      memRegion (sp + 416#64) 1776 ∗
      memRegion (sp + 2192#64) 32 ∗ memRegion (sp + 2224#64) 32 ∗ memRegion (sp + 2256#64) 1448 ∗
      memRegion (sp + 3704#64) 568 ∗
      memRegion (sp + 4272#64) 32 ∗ memRegion (sp + 4304#64) 32 ∗
      memRegion (sp + 4336#64) 1472 ∗ memRegion (sp + 5808#64) 96 ∗
      memRegion (sp + 5904#64) 864 ∗ memRegion (sp + 6768#64) 64 ∗
      memRegion (sp + 6832#64) 64 ∗ memRegion (sp + 6896#64) 4544 ∗
      memRegion (sp + 11440#64) 1008 ∗ memRegion (sp + 12448#64) 24 ∗
      memRegion (sp + 12472#64) 1512 ∗
      memRegion (sp + 13984#64) 32 ∗ memRegion (sp + 14016#64) 472 ∗
      memRegion (sp + 14488#64) 2376 := by
  rw [memRegion_split' (b' := sp + 32#64) (n := 32) (k := (16832 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 40#64) (n := 8) (k := (16824 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 48#64) (n := 8) (k := (16816 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 80#64) (n := 32) (k := (16784 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 88#64) (n := 8) (k := (16776 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 96#64) (n := 8) (k := (16768 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 336#64) (n := 240) (k := (16528 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 352#64) (n := 16) (k := (16512 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 384#64) (n := 32) (k := (16480 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 416#64) (n := 32) (k := (16448 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 2192#64) (n := (1776 : Nat)) (k := (14672 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 2224#64) (n := 32) (k := (14640 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 2256#64) (n := 32) (k := (14608 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 3704#64) (n := (1448 : Nat)) (k := (13160 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 4272#64) (n := 568) (k := (12592 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 4304#64) (n := 32) (k := (12560 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 4336#64) (n := 32) (k := (12528 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 5808#64) (n := (1472 : Nat)) (k := (11056 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 5904#64) (n := 96) (k := (10960 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 6768#64) (n := 864) (k := (10096 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 6832#64) (n := 64) (k := (10032 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 6896#64) (n := 64) (k := (9968 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 11440#64) (n := (4544 : Nat)) (k := (5424 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 12448#64) (n := (1008 : Nat)) (k := (4416 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 12472#64) (n := 24) (k := (4392 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 13984#64) (n := (1512 : Nat)) (k := (2880 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 14016#64) (n := 32) (k := (2848 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 14488#64) (n := 472) (k := (2376 : Nat)) rfl (by bv_omega) (by decide)]

theorem seg1_wp [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s0 : State) (a : MlkemBlk03Args) (R : SepProp)
    (hhdr : a.hdr64.length = 64) (hrand : a.rand.length = 32)
    (hpc : s0.pc = b) (hrun : s0.status = .Running) (hsp0 : s0.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s0.mem)
    (hro : MlKemRoOk mlkemMpl s0.mem)
    (hx0 : s0.readReg64 .x0 = a.ret) (hx1 : s0.readReg64 .x1 = a.hdrA)
    (hx2 : s0.readReg64 .x2 = a.randA) (hx3 : s0.readReg64 .x3 = a.esA)
    (hx4 : s0.readReg64 .x4 = 2080#64) (hx5 : s0.readReg64 .x5 = a.ssA)
    (hx6 : s0.readReg64 .x6 = 32#64) :
    let sp := s0.sp - 17024#64
    SepWP (blkPC03.rebase b (fun _ => none)) (b + 0x0504#64) s0
      ((a.hdrA ↦ₛ a.hdr64) ∗ (a.randA ↦ₛ a.rand) ∗
        memRegion a.ret 961 ∗ memRegion a.esA 2080 ∗ memRegion a.ssA 32 ∗
        stackAt s0.sp 18160 ∗ R)
      (fun s2 P2 =>
        Seg2RegInv sp s2 ∧ s2.readReg64 .x8 = 0#64 ∧
        (P2 ⊢ Seg2ConstsLo sp ∗ Seg2SeedConsts sp (a.hdr64.take 32) ∗
          memRegion (sp + 96#64) 240 ∗ memRegion (sp + 416#64) 1776 ∗
          memRegion (sp + 2192#64) 1512 ∗ memRegion (sp + 4272#64) 1632 ∗
          memRegion (sp + 6832#64) 4608 ∗ memRegion (sp + 12448#64) 24 ∗
          memRegion (sp + 13984#64) 504 ∗ Seg2Preserved s0 a R)) := by
  intro sp
  refine SepWP.weaken_pre
    (P' := stackAt s0.sp 18160 ∗ ((a.hdrA ↦ₛ a.hdr64) ∗ (a.randA ↦ₛ a.rand) ∗
      memRegion a.ret 961 ∗ memRegion a.esA 2080 ∗ memRegion a.ssA 32 ∗ R))
    (by sep_frame) ?_
  refine sepWP_seq_env hcl hro
    (seg1_prologue hb hbase s0 a _ hpc hrun hsp0 hx0 hx1 hx2 hx3 hx4 hx5 hx6) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hsp_al1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, hP1⟩
  let commonPres : SepProp :=
    memRegion (sp + 80#64) 8 ∗ memRegion (sp + 96#64) 240 ∗ memRegion (sp + 416#64) 1776 ∗
      memRegion (sp + 2256#64) 1448 ∗ memRegion (sp + 3704#64) 568 ∗
      memRegion (sp + 5808#64) 96 ∗ memRegion (sp + 5904#64) 864 ∗
      memRegion (sp + 11440#64) 1008 ∗ memRegion (sp + 12448#64) 24 ∗
      memRegion (sp + 12472#64) 1512 ∗ memRegion (sp + 14016#64) 472 ∗
      memRegion (sp + 14488#64) 2376 ∗
      SavedFrame03 (sp + 16864#64) s0 ∗
      memRegion a.ret 961 ∗ memRegion a.esA 2080 ∗ memRegion a.ssA 32 ∗ R
  let constRegions : SepProp :=
    memRegion (sp + 40#64) 8 ∗ memRegion (sp + 48#64) 32 ∗
      memRegion (sp + 88#64) 8 ∗ memRegion (sp + 336#64) 16 ∗
      memRegion (sp + 352#64) 32 ∗ memRegion (sp + 384#64) 32
  let rest1 : SepProp :=
    constRegions ∗ memRegion (sp + 4336#64) 1472 ∗ memRegion (sp + 6768#64) 64 ∗
      memRegion (sp + 6832#64) 64 ∗ memRegion (sp + 6896#64) 4544 ∗
      stackAt sp 1136 ∗ commonPres
  refine SepWP.weaken_pre ?_
    (sepWP_seq_env hcl1 hro1
      (seg1_hash_prep hb hbase s1 sp a rest1 hhdr hrand hpc1 hrun1 hsp1 hsp_al1
        hx0_1 hx1_1 hx2_1 hx3_1 hx4_1 hx5_1) ?_)
  · refine Entails.trans hP1 ?_
    dsimp only [rest1, constRegions, commonPres]
    rw [frame16864_seg1_split sp]
    sep_frame
  rintro sm Pm hpcm hrunm hclm hrom
    ⟨hspm, hsp_alm, hx0m, hx1m, hx2m, hx19m, hx20m, hx21m, hx22m, hx23m, hx24m, hx25m, hx28m, hPm⟩
  let rest2 : SepProp :=
    SavedArgs03 sp a ∗ (a.hdrA ↦ₛ a.hdr64) ∗ (a.randA ↦ₛ a.rand) ∗
      constRegions ∗ memRegion (sp + 4336#64) 1472 ∗ memRegion (sp + 6768#64) 64 ∗
      memRegion (sp + 6896#64) 4544 ∗ commonPres
  refine SepWP.weaken_pre ?_
    (sepWP_seq_env hclm hrom
      (seg1_b00_call hb hbase sm sp a rest2 hhdr hrand hpcm hrunm hspm hsp_alm
        hx0m hx1m hx2m hx19m hx20m hx21m hx22m hx23m hx24m hx25m hx28m hclm hrom) ?_)
  · refine Entails.trans hPm ?_
    dsimp only [rest1, rest2]
    sep_frame
  rintro sk Pk hpck hrunk hclk hrok
    ⟨hspk, hsp_alk, hx19k, hx20k, hx21k, hx22k, hx23k, hx24k, hx25k, hx28k, hPk⟩
  have hhashed_len : (sha3_512List (a.rand ++ a.hdr64.drop 32)).length = 64 := sha3_512List_length _
  let rest3 : SepProp :=
    memRegion (sp + 2192#64) 64 ∗ memRegion (sp + 6832#64) 4608 ∗
      memRegion (sp + 13984#64) 32 ∗ stackAt sp 1136 ∗
      SavedArgs03 sp a ∗ (a.hdrA ↦ₛ a.hdr64) ∗ (a.randA ↦ₛ a.rand) ∗
      constRegions ∗ commonPres
  refine SepWP.weaken_pre ?_
    (sepWP_seq_env hclk hrok
      (seg1_copy_zero_a hb hbase sk sp _ rest3 hhashed_len hpck hrunk hspk hsp_alk) ?_)
  · refine Entails.trans hPk ?_
    dsimp only [rest2, rest3]
    rw [memRegion_split' (b := sp + 6832#64) (b' := sp + 6896#64) (n := 64) (k := (4544 : Nat)) rfl (by clear *- ; bv_omega) (by decide)]
    sep_frame
  rintro sz Pz hpcz hrunz hclz hroz
    ⟨hspz, hsp_alz, hx0z, hx1z, hx2z, hx19z, hx20z, hx21z, hx22z, hx23z, hx24z, hx25z, hx28z, hPz⟩
  let rest4 : SepProp :=
    ((sp + 6768#64) ↦ₛ sha3_512List (a.rand ++ a.hdr64.drop 32)) ∗
      memRegion (sp + 2192#64) 64 ∗ memRegion (sp + 13984#64) 32 ∗ stackAt sp 1136 ∗
      SavedArgs03 sp a ∗ (a.hdrA ↦ₛ a.hdr64) ∗ (a.randA ↦ₛ a.rand) ∗
      constRegions ∗ commonPres
  refine SepWP.weaken_pre ?_
    (sepWP_seq_env hclz hroz
      (seg1_copy_zero_b hb hbase sz sp rest4 hpcz hrunz hspz hsp_alz
        hx0z hx1z hx2z (hx22z.trans hx22k) hclz) ?_)
  · refine Entails.trans hPz ?_
    dsimp only [rest3, rest4]
    sep_frame
  rintro sc Pc hpcc hrunc _ hroc
    ⟨hspc, hsp_alc, hx19c, hx20c, hx21c, hx23c, hx24c, hx25c, hx28c, hPc⟩
  let rest5 : SepProp :=
    memRegion (sp + 4272#64) 1536 ∗ memRegion (sp + 6832#64) 4608 ∗
      ((sp + 6768#64) ↦ₛ sha3_512List (a.rand ++ a.hdr64.drop 32)) ∗
      memRegion (sp + 2192#64) 64 ∗ memRegion (sp + 13984#64) 32 ∗ stackAt sp 1136 ∗
      SavedArgs03 sp a ∗ (a.randA ↦ₛ a.rand) ∗ commonPres
  refine SepWP.weaken_pre ?_
    (SepWP.mono
      (seg1_consts hb hbase sc sp a rest5 hhdr hpcc hrunc hspc hsp_alc
        (hx19c.trans (hx19z.trans hx19k))
        (hx20c.trans (hx20z.trans hx20k))
        (hx21c.trans (hx21z.trans hx21k))
        (hx23c.trans (hx23z.trans hx23k))
        (hx24c.trans (hx24z.trans hx24k))
        (hx25c.trans (hx25z.trans hx25k))
        (hx28c.trans (hx28z.trans hx28k))
        hroc) ?_)
  · refine Entails.trans hPc ?_
    dsimp only [rest4, rest5, constRegions]
    sep_frame
  rintro s2 P2 _ _ ⟨hreg, hx8, hP2⟩
  refine ⟨hreg, hx8, Entails.trans hP2 ?_⟩
  dsimp only [rest5, commonPres]
  unfold Seg2Preserved
  dsimp only
  rw [memRegion_split' (b := sp + 2192#64) (b' := sp + 2256#64) (n := 64) (k := (1448 : Nat)) rfl (by clear *- ; bv_omega) (by decide),
    memRegion_split' (b := sp + 4272#64) (b' := sp + 5808#64) (n := (1536 : Nat)) (k := 96) rfl (by clear *- ; bv_omega) (by decide),
    memRegion_split' (b := sp + 13984#64) (b' := sp + 14016#64) (n := 32) (k := 472) rfl (by clear *- ; bv_omega) (by decide)]
  sep_frame

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1
