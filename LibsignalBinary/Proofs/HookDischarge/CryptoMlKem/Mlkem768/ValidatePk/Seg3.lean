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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg1 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg3Simd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg3Loop
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg3Copy

/-!
# `validate_pk_bytes` (`B21`) — Segment 3 Execution (`+0x044c → lr`, `Role::Proof`)

Composes the three 16-iteration AdvSIMD `serialize_12` loops (`Seg3Loop`), setup/dead-store and
`memcpy` blocks (`Seg3Copy`), Copy 3 (`+0x07d8 → +0x0800`), the 32-byte seed copy from
`x19 = sp + 1168`, the 1184-byte `B30` (`bcmp`) check, and the final branch to `Seg1.seg_ret_ok`
(`+0x0840`) or `Seg1.seg_ret_err2` (`+0x0820`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg3

open Arm64 Arm64.Obj ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement add_off_reloc_cancel add_reloc_cancel add_zero_reloc_cancel mbase
  mlkemBlockPlacement_ρ mlkemCall_of_blockOk mlkemMpl resolve_blk28 resolve_blk30 seq_codeLoaded_lr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (
  mlkemBcmpRW1ROSpec mlkemMemcpySpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (mlkem768ValidPk sha3_256List)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps (
  blk28_memcpy_ok blk30_bcmpRW1RO_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Base (
  blk21_code_eq blk21_tree_size blkLib21 blkPC21 blkPl21 blkPlaceable21 blkTree21
  mlkemBcmpRW2Spec mlkemBcmpRW2_of_rw1ro reencodePoly384)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg1 (
  SavedFrame UnspilledSaved ValidatePkPost entails_sub seg_ret_err2 seg_ret_ok
  sepWP_elim_region32 sepWP_mono_ret)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2 (
  Seg3Pre Seg3Spatial reducedPolyBytes reducedPolyBytes_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg3Simd (
  reencodePolyPrefix reencodePolyPrefix_zero)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg3Loop (
  seg3_loop1 seg3_loop2 seg3_loop3)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg3Copy (
  pointsToBytes_reencode_entails_memRegion reencodePoly384_length reencode_bcmp_eq_iff_validPk
  seg3_copy1_setup2 seg3_copy2_setup3 seg3_setup1 sepWP_seq_cl)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC21 blkLib21 blkTree21 blk21_code_eq blk21_tree_size
  via_placement blkPl21 blkPlaceable21
  [0x07d8 → 0x081c]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl21_ρ [MlKemPlacement] (sym : String) :
    blkPl21.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

@[simp] private theorem extractLsb64_lo_append (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 0 64 = lo := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp [hi']

@[simp] private theorem extractLsb64_hi_append (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 64 64 = hi := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp [hi']

private theorem setWidth64_setWidth32_eq_zero_iff (x : BitVec 64) :
    BitVec.setWidth 64 (BitVec.setWidth 32 x) = 0#64 ↔ BitVec.setWidth 32 x = 0#32 := by
  constructor
  · intro h
    simpa using congrArg (BitVec.setWidth 32) h
  · intro h; simp [h]

/-! ## 1. Stack Region Splits & Collapse Lemmas -/

private theorem frame1984_split7 (sp : BitVec 64) :
    memRegion (sp + 2736#64) 1984 =
      memRegion (sp + 2736#64) 384 ∗
      memRegion (sp + 3120#64) 384 ∗
      memRegion (sp + 3504#64) 384 ∗
      memRegion (sp + 3888#64) 32 ∗
      memRegion (sp + 3920#64) 384 ∗
      memRegion (sp + 4304#64) 384 ∗
      memRegion (sp + 4688#64) 32 := by
  rw [memRegion_split' (b := sp + 2736#64) (b' := sp + 3120#64) (n := 384) (k := (1600 : Nat)) (by bv_omega) (by bv_omega) (by decide),
    memRegion_split' (b := sp + 3120#64) (b' := sp + 3504#64) (n := 384) (k := (1216 : Nat)) (by bv_omega) (by bv_omega) (by decide),
    memRegion_split' (b := sp + 3504#64) (b' := sp + 3888#64) (n := 384) (k := 832) (by bv_omega) (by bv_omega) (by decide),
    memRegion_split' (b := sp + 3888#64) (b' := sp + 3920#64) (n := 32) (k := 800) (by bv_omega) (by bv_omega) (by decide),
    memRegion_split' (b := sp + 3920#64) (b' := sp + 4304#64) (n := 384) (k := 416) (by bv_omega) (by bv_omega) (by decide),
    memRegion_split' (b := sp + 4304#64) (b' := sp + 4688#64) (n := 384) (k := 32) (by bv_omega) (by bv_omega) (by decide)]

private theorem pkRe_pointsToBytes_split4 (sp : BitVec 64)
    (bs0 bs1 bs2 sd : List (BitVec 8)) :
    ((sp + 2736#64) ↦ₛ
      (reencodePoly384 bs0 ++ reencodePoly384 bs1 ++ reencodePoly384 bs2 ++ sd)) =
    ((sp + 2736#64) ↦ₛ reencodePoly384 bs0) ∗
    ((sp + 3120#64) ↦ₛ reencodePoly384 bs1) ∗
    ((sp + 3504#64) ↦ₛ reencodePoly384 bs2) ∗
    ((sp + 3888#64) ↦ₛ sd) := by
  have hl0 : (reencodePoly384 bs0).length = 384 := reencodePoly384_length bs0
  have hl01 : (reencodePoly384 bs0 ++ reencodePoly384 bs1).length = 768 := by
    simp
  have hl012 : (reencodePoly384 bs0 ++ reencodePoly384 bs1 ++ reencodePoly384 bs2).length = 1152 := by
    simp
  have ha1 : (sp + 2736#64) + BitVec.ofNat 64 384 = sp + 3120#64 := by bv_omega
  have ha2 : (sp + 2736#64) + BitVec.ofNat 64 768 = sp + 3504#64 := by bv_omega
  have ha3 : (sp + 2736#64) + BitVec.ofNat 64 1152 = sp + 3888#64 := by bv_omega
  rw [pointsToBytes_append, hl012, ha3, pointsToBytes_append, hl01, ha2,
    pointsToBytes_append, hl0, ha1]
  simp only [sepConj_assoc]

private theorem frame4720_seg3_collapse (sp : BitVec 64)
    (pk pkRe : List (BitVec 8)) (bs0 bs1 bs2 : List (BitVec 8))
    (hpk : pk.length = 1184) (hpkRe : pkRe.length = 1184) :
    memRegion sp 16 ∗
      ((sp + 16#64) ↦ₛ pk) ∗
      ((sp + 1200#64) ↦ₛ reducedPolyBytes bs0) ∗
      ((sp + 1712#64) ↦ₛ reducedPolyBytes bs1) ∗
      ((sp + 2224#64) ↦ₛ reducedPolyBytes bs2) ∗
      ((sp + 2736#64) ↦ₛ pkRe) ∗
      memRegion (sp + 3920#64) 384 ∗
      memRegion (sp + 4304#64) 384 ∗
      memRegion (sp + 4688#64) 32 ⊢
      memRegion sp 4720 := by
  have hp1 : ((sp + 16#64) ↦ₛ pk) ⊢ memRegion (sp + 16#64) 1184 := by
    simpa [hpk] using pointsToBytes_entails_memRegion (sp + 16#64) pk
  have hp2 : ((sp + 1200#64) ↦ₛ reducedPolyBytes bs0) ⊢ memRegion (sp + 1200#64) 512 := by
    simpa using pointsToBytes_entails_memRegion (sp + 1200#64) (reducedPolyBytes bs0)
  have hp3 : ((sp + 1712#64) ↦ₛ reducedPolyBytes bs1) ⊢ memRegion (sp + 1712#64) 512 := by
    simpa using pointsToBytes_entails_memRegion (sp + 1712#64) (reducedPolyBytes bs1)
  have hp4 : ((sp + 2224#64) ↦ₛ reducedPolyBytes bs2) ⊢ memRegion (sp + 2224#64) 512 := by
    simpa using pointsToBytes_entails_memRegion (sp + 2224#64) (reducedPolyBytes bs2)
  have hp5 : ((sp + 2736#64) ↦ₛ pkRe) ⊢ memRegion (sp + 2736#64) 1184 := by
    simpa [hpkRe] using pointsToBytes_entails_memRegion (sp + 2736#64) pkRe
  have hsplit : memRegion sp 4720 =
      memRegion sp 16 ∗ memRegion (sp + 16#64) 1184 ∗ memRegion (sp + 1200#64) 512 ∗
      memRegion (sp + 1712#64) 512 ∗ memRegion (sp + 2224#64) 512 ∗ memRegion (sp + 2736#64) 1184 ∗
      memRegion (sp + 3920#64) 384 ∗ memRegion (sp + 4304#64) 384 ∗ memRegion (sp + 4688#64) 32 := by
    rw [memRegion_split' (b := sp) (b' := sp + 16#64) (n := 16) (k := (4704 : Nat)) (by bv_omega) (by bv_omega) (by decide),
      memRegion_split' (b := sp + 16#64) (b' := sp + 1200#64) (n := 1184) (k := (3520 : Nat)) (by bv_omega) (by bv_omega) (by decide),
      memRegion_split' (b := sp + 1200#64) (b' := sp + 1712#64) (n := 512) (k := (3008 : Nat)) (by bv_omega) (by bv_omega) (by decide),
      memRegion_split' (b := sp + 1712#64) (b' := sp + 2224#64) (n := 512) (k := (2496 : Nat)) (by bv_omega) (by bv_omega) (by decide),
      memRegion_split' (b := sp + 2224#64) (b' := sp + 2736#64) (n := 512) (k := (1984 : Nat)) (by bv_omega) (by bv_omega) (by decide),
      memRegion_split' (b := sp + 2736#64) (b' := sp + 3920#64) (n := 1184) (k := 800) (by bv_omega) (by bv_omega) (by decide),
      memRegion_split' (b := sp + 3920#64) (b' := sp + 4304#64) (n := 384) (k := 416) (by bv_omega) (by bv_omega) (by decide),
      memRegion_split' (b := sp + 4304#64) (b' := sp + 4688#64) (n := 384) (k := 32) (by bv_omega) (by bv_omega) (by decide)]
  rw [hsplit]
  exact entails_sub hp1 (by sep_frame) (entails_sub hp2 (by sep_frame)
    (entails_sub hp3 (by sep_frame) (entails_sub hp4 (by sep_frame)
      (entails_sub hp5 (by sep_frame) (by sep_frame)))))

/-! ## 2. Copy 3 (`+0x07d8 → +0x0800`), Seed Copy + `bcmp` (`+0x0800 → +0x081c`), & `seg3_run` -/

attribute [local irreducible] sha3_256List reencodePoly384 reducedPolyBytes

private theorem seg3_copy3a [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl21 b) (_hbase : blkPl21.base = b)
    (s0 s : State) (sp : BitVec 64) (bs2 : List (BitVec 8)) (Rest : SepProp)
    (hpc : s.pc = b + 0x07d8#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : (sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = sp + 1168#64)
    (hus : UnspilledSaved s0 s) (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC21.rebase b (fun _ => none)) (b + 0x07ec#64) s
      (memRegion (sp + 3920#64) 384 ∗ ((sp + 4304#64) ↦ₛ reencodePoly384 bs2) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.readReg64 .x19 = sp + 1168#64 ∧ UnspilledSaved s0 sf ∧
        (Pf ⊢ ((sp + 3920#64) ↦ₛ reencodePoly384 bs2) ∗ ((sp + 4304#64) ↦ₛ reencodePoly384 bs2) ∗ Rest)) := by
  have hsp_align : s.spAligned = true := by rw [State.spAligned, hsp]; exact hspA
  have ha4304 : sp + 4096#64 + 208#64 = sp + 4304#64 := by bv_omega
  have hlen : (reencodePoly384 bs2).length = 384 := reencodePoly384_length bs2
  rw [show memRegion (sp + 3920#64) 384 = memRegion (sp + 3920#64) (reencodePoly384 bs2).length by rw [hlen]]
  wp_cut_codeLoaded; wp_steps
  wp_mlkem_call blk28_memcpy_ok (sp + 3920#64, sp + 4304#64, reencodePoly384 bs2)
  refine SepWP.done hpc_sf hrun_sf
    ⟨hsp_sf.trans hsp, h.trans hx19,
      ⟨h_5.trans hus.1, h_6.trans hus.2.1, h_7.trans hus.2.2.1, h_8.trans hus.2.2.2.1, hvregs.trans hus.2.2.2.2⟩,
      by sep_frame⟩

private theorem seg3_copy3 [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl21 b) (hbase : blkPl21.base = b)
    (s0 s : State) (sp : BitVec 64) (bs2 : List (BitVec 8)) (Rest : SepProp)
    (hpc : s.pc = b + 0x07d8#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : (sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = sp + 1168#64)
    (hus : UnspilledSaved s0 s) (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC21.rebase b (fun _ => none)) (b + 0x0800#64) s
      (memRegion (sp + 3504#64) 384 ∗ memRegion (sp + 3920#64) 384 ∗
        ((sp + 4304#64) ↦ₛ reencodePoly384 bs2) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.readReg64 .x19 = sp + 1168#64 ∧ UnspilledSaved s0 sf ∧
        (Pf ⊢ ((sp + 3504#64) ↦ₛ reencodePoly384 bs2) ∗ memRegion (sp + 3920#64) 384 ∗
          memRegion (sp + 4304#64) 384 ∗ Rest)) := by
  refine sepWP_seq_cl hcl
    (SepWP.weaken_pre (by sep_frame)
      (seg3_copy3a hb hbase s0 s sp bs2 (memRegion (sp + 3504#64) 384 ∗ Rest)
        hpc hrun hsp hspA hx19 hus hcl)) ?_
  rintro sm Pm hpcm hrunm hclm ⟨hspm, hx19m, husm, hPm⟩
  refine SepWP.weaken_pre hPm ?_
  have hsp_align : sm.spAligned = true := by rw [State.spAligned, hspm]; exact hspA
  have ha3504 : sp + 2736#64 + 768#64 = sp + 3504#64 := by bv_omega
  have hlen : (reencodePoly384 bs2).length = 384 := reencodePoly384_length bs2
  rw [show memRegion (sp + 3504#64) 384 = memRegion (sp + 3504#64) (reencodePoly384 bs2).length by rw [hlen]]
  wp_cut_codeLoaded; wp_steps
  wp_mlkem_call blk28_memcpy_ok (sp + 3504#64, sp + 3920#64, reencodePoly384 bs2)
  refine SepWP.done hpc_sf hrun_sf
    ⟨hsp_sf.trans hspm, h.trans hx19m,
      ⟨h_5.trans husm.1, h_6.trans husm.2.1, h_7.trans husm.2.2.1, h_8.trans husm.2.2.2.1, hvregs.trans husm.2.2.2.2⟩,
      entails_sub (pointsToBytes_reencode_entails_memRegion (sp + 3920#64) bs2) (by sep_frame)
        (entails_sub (pointsToBytes_reencode_entails_memRegion (sp + 4304#64) bs2) (by sep_frame)
          (by sep_frame))⟩

private theorem seg3_seed_prep [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl21 b) (_hbase : blkPl21.base = b)
    (s0 s : State) (sp : BitVec 64) (hdr ek bs0 bs1 bs2 : List (BitVec 8)) (Rest : SepProp)
    (hhdr : hdr.length = 64) (hek : ek.length = 1152)
    (hpc : s.pc = b + 0x0800#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : (sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = sp + 1168#64) (hus : UnspilledSaved s0 s) :
    SepWP (blkPC21.rebase b (fun _ => none)) (b + 0x0818#64) s
      (((sp + 16#64) ↦ₛ (ek ++ hdr.take 32)) ∗
        ((sp + 2736#64) ↦ₛ reencodePoly384 bs0) ∗
        ((sp + 3120#64) ↦ₛ reencodePoly384 bs1) ∗
        ((sp + 3504#64) ↦ₛ reencodePoly384 bs2) ∗
        memRegion (sp + 3888#64) 32 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧
        sf.readReg64 .x0 = sp + 16#64 ∧
        sf.readReg64 .x1 = sp + 2736#64 ∧
        sf.readReg64 .x2 = 1184#64 ∧
        UnspilledSaved s0 sf ∧
        (Pf ⊢ ((sp + 16#64) ↦ₛ (ek ++ hdr.take 32)) ∗
          ((sp + 2736#64) ↦ₛ
            (reencodePoly384 bs0 ++ reencodePoly384 bs1 ++ reencodePoly384 bs2 ++ hdr.take 32)) ∗
          Rest)) := by
  have hsp_align : s.spAligned = true := by rw [State.spAligned, hsp]; exact hspA
  have hsd_len : (hdr.take 32).length = 32 := by simp [hhdr]
  obtain ⟨sw0, sw1, sw2, sw3, _, hseed_pts⟩ := exists_unpack64_of_length_32 hsd_len
  have hpk_split :
      ((sp + 16#64) ↦ₛ (ek ++ hdr.take 32)) =
        ((sp + 16#64) ↦ₛ ek) ∗
          (((sp + 1168#64) ↦₆₄ sw0) ∗ ((sp + 1176#64) ↦₆₄ sw1) ∗
            ((sp + 1184#64) ↦₆₄ sw2) ∗ ((sp + 1192#64) ↦₆₄ sw3)) := by
    have ha0 : (sp + 16#64) + BitVec.ofNat 64 1152 = sp + 1168#64 := by bv_omega
    have ha1 : (sp + 1168#64) + 8#64 = sp + 1176#64 := by bv_omega
    have ha2 : (sp + 1168#64) + 16#64 = sp + 1184#64 := by bv_omega
    have ha3 : (sp + 1168#64) + 24#64 = sp + 1192#64 := by bv_omega
    rw [pointsToBytes_append, hek, ha0, hseed_pts (sp + 1168#64), ha1, ha2, ha3]
  have hd1 : (sp + 3888#64) + 8#64 = sp + 3896#64 := by bv_omega
  have hd2 : (sp + 3888#64) + 16#64 = sp + 3904#64 := by bv_omega
  have hd3 : (sp + 3888#64) + 24#64 = sp + 3912#64 := by bv_omega
  sep_frame_apply (sepWP_elim_region32 (a := sp + 3888#64)); intro z0 z1 z2 z3
  rw [hd1, hd2, hd3, hpk_split]
  simp only [sepConj_assoc]
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simp, by simp, by simp only [wp_norm, arm64_norm],
      ⟨by simp [hus.1], by simp [hus.2.1], by simp [hus.2.2.1], by simp [hus.2.2.2.1],
        by simp [calleeSavedVRegs, hus.2.2.2.2]⟩, ?_⟩
  have hsd_dst :
      ((sp + 3888#64) ↦ₛ hdr.take 32) =
        ((sp + 3888#64) ↦₆₄ sw0) ∗ ((sp + 3896#64) ↦₆₄ sw1) ∗
          ((sp + 3904#64) ↦₆₄ sw2) ∗ ((sp + 3912#64) ↦₆₄ sw3) := by
    rw [hseed_pts (sp + 3888#64), hd1, hd2, hd3]
  rw [pkRe_pointsToBytes_split4 sp bs0 bs1 bs2 (hdr.take 32), hsd_dst]
  sep_frame

private theorem seg3_bcmp_call [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl21 b) (_hbase : blkPl21.base = b)
    (s0 s : State) (sp : BitVec 64) (pk pkRe : List (BitVec 8)) (Rest : SepProp)
    (hpk : pk.length = 1184) (hpkRe : pkRe.length = 1184)
    (hpc : s.pc = b + 0x0818#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : (sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = sp + 16#64)
    (hx1 : s.readReg64 .x1 = sp + 2736#64)
    (hx2 : s.readReg64 .x2 = 1184#64)
    (hus : UnspilledSaved s0 s) (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC21.rebase b (fun _ => none)) (b + 0x081c#64) s
      (((sp + 16#64) ↦ₛ pk) ∗ ((sp + 2736#64) ↦ₛ pkRe) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ UnspilledSaved s0 sf ∧
        (sf.readReg32 .x0 = 0#32 ↔ pk = pkRe) ∧
        (Pf ⊢ ((sp + 16#64) ↦ₛ pk) ∗ ((sp + 2736#64) ↦ₛ pkRe) ∗ Rest)) := by
  have hsp_align : s.spAligned = true := by rw [State.spAligned, hsp]; exact hspA
  have hx2_nat : (s.readReg64 .x2).toNat = pk.length := by rw [hx2, hpk]; rfl
  have hlen_eq : pkRe.length = pk.length := by rw [hpkRe, hpk]
  have hpk_lt : pk.length < 2 ^ 64 := by rw [hpk]; decide
  wp_step
  wp_mlkem_call (mlkemBcmpRW2_of_rw1ro blk30_bcmpRW1RO_ok) (sp + 16#64, sp + 2736#64, pk, pkRe)
  refine SepWP.done hpc_sf hrun_sf
    ⟨hsp_sf.trans hsp,
      ⟨h_5.trans hus.1, h_6.trans hus.2.1, h_7.trans hus.2.2.1, h_8.trans hus.2.2.2.1, hvregs.trans hus.2.2.2.2⟩,
      ‹sf.readReg32 .x0 = 0#32 ↔ pk = pkRe›,
      by sep_frame⟩

/-- Full Segment 3 execution (`+0x044c → s0.readReg64 .lr`) discharging `ValidatePkPost`. -/
theorem seg3_run [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl21 b) (hbase : blkPl21.base = b)
    (s0 s : State) (hdrA ekA : BitVec 64) (hdr ek : List (BitVec 8)) (R : SepProp)
    (hpc : s.pc = b + 0x044c#64) (hrun : s.status = .Running)
    (hsp0 : s0.spAligned = true) (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hpre : Seg3Pre s0 s hdr ek) :
    SepWP (blkPC21.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      (Seg3Spatial s0 hdrA hdr ekA ek R)
      (ValidatePkPost s0 hdrA hdr ekA ek R) := by
  rcases hpre with ⟨hhdr, hek, hhash, hsp, hus, hx19, hx20, hx21⟩
  let sp := s0.sp - 4784#64
  have hspA : (sp &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 4784#64 hsp0 (by decide)
  let bs0 := ek.take 384; let bs1 := (ek.drop 384).take 384; let bs2 := (ek.drop 768).take 384
  let pk := ek ++ hdr.take 32
  let pkRe := reencodePoly384 bs0 ++ reencodePoly384 bs1 ++ reencodePoly384 bs2 ++ hdr.take 32
  let Ft := (SavedFrame s0.sp s0 ∗ stackAt sp 1040 ∗ (hdrA ↦ₛ hdr) ∗ (ekA ↦ₛ ek) ∗ R)
  have hreg0 : memRegion (sp + 4304#64) 384 =
      memRegion ((sp + 4304#64) + BitVec.ofNat 64 (24 * 0)) (384 - 24 * 0) := by
    simp only [Nat.mul_zero, Nat.sub_zero, BitVec.add_zero]
  unfold Seg3Spatial; dsimp only; rw [frame1984_split7 sp]
  let wp1 := seg3_setup1 hb hbase s0 s sp
    (memRegion sp 16 ∗ ((sp + 16#64) ↦ₛ pk) ∗ ((sp + 1200#64) ↦ₛ reducedPolyBytes bs0) ∗
      ((sp + 1712#64) ↦ₛ reducedPolyBytes bs1) ∗ ((sp + 2224#64) ↦ₛ reducedPolyBytes bs2) ∗
      memRegion (sp + 2736#64) 384 ∗ memRegion (sp + 3120#64) 384 ∗ memRegion (sp + 3504#64) 384 ∗
      memRegion (sp + 3888#64) 32 ∗ memRegion (sp + 3920#64) 384 ∗ memRegion (sp + 4688#64) 32 ∗ Ft)
    hpc hrun hsp hspA hx19 hx20 hx21 hus
  refine sepWP_seq_cl hcl
    (SepWP.weaken_pre (by dsimp only [sp, pk, bs0, bs1, bs2, Ft]; sep_frame) wp1) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 ⟨hsp1, hx8_1, hx9_1, hx10_1, hx19_1, hx20_1, _, hus1, rfl⟩
  let wp2 := seg3_loop1 s0 (sp + 1200#64) (sp + 4304#64) bs0
    (memRegion sp 16 ∗ ((sp + 16#64) ↦ₛ pk) ∗ ((sp + 1712#64) ↦ₛ reducedPolyBytes bs1) ∗
      ((sp + 2224#64) ↦ₛ reducedPolyBytes bs2) ∗ memRegion (sp + 2736#64) 384 ∗
      memRegion (sp + 3120#64) 384 ∗ memRegion (sp + 3504#64) 384 ∗ memRegion (sp + 3888#64) 32 ∗
      memRegion (sp + 3920#64) 384 ∗ memRegion (sp + 4688#64) 32 ∗ Ft)
    15 0 rfl s1 hpc1 hrun1 hx8_1 hx9_1 hx10_1 hus1
  refine sepWP_seq_cl hcl1
    (SepWP.weaken_pre
      (by rw [hreg0]; simp only [reencodePolyPrefix_zero, pointsToBytes_nil]; sep_frame) wp2) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, hx20_2, _, hus2, hP2⟩
  let wp3 := seg3_copy1_setup2 hb hbase s0 s2 sp bs0
    (memRegion sp 16 ∗ ((sp + 16#64) ↦ₛ pk) ∗ ((sp + 1200#64) ↦ₛ reducedPolyBytes bs0) ∗
      ((sp + 1712#64) ↦ₛ reducedPolyBytes bs1) ∗ ((sp + 2224#64) ↦ₛ reducedPolyBytes bs2) ∗
      memRegion (sp + 3120#64) 384 ∗ memRegion (sp + 3504#64) 384 ∗ memRegion (sp + 3888#64) 32 ∗
      memRegion (sp + 4688#64) 32 ∗ Ft)
    hpc2 hrun2 (hsp2.trans hsp1) hspA (hx19_2.trans hx19_1) (hx20_2.trans hx20_1) hus2 hcl2
  refine sepWP_seq_cl hcl2 (SepWP.weaken_pre (Entails.trans hP2 (by sep_frame)) wp3) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 ⟨hsp3, hx8_3, hx9_3, hx19_3, hx20_3, hx21_3, hus3, hP3⟩
  let wp4 := seg3_loop2 s0 (sp + 1712#64) (sp + 4304#64) bs1
    (memRegion sp 16 ∗ ((sp + 16#64) ↦ₛ pk) ∗ ((sp + 1200#64) ↦ₛ reducedPolyBytes bs0) ∗
      ((sp + 2224#64) ↦ₛ reducedPolyBytes bs2) ∗ ((sp + 2736#64) ↦ₛ reencodePoly384 bs0) ∗
      memRegion (sp + 3120#64) 384 ∗ memRegion (sp + 3504#64) 384 ∗ memRegion (sp + 3888#64) 32 ∗
      memRegion (sp + 3920#64) 384 ∗ memRegion (sp + 4688#64) 32 ∗ Ft)
    15 0 rfl s3 hpc3 hrun3 hx8_3 hx9_3 hx21_3 hus3
  refine sepWP_seq_cl hcl3
    (SepWP.weaken_pre
      (Entails.trans hP3
        (by rw [hreg0]; simp only [reencodePolyPrefix_zero, pointsToBytes_nil]; sep_frame)) wp4) ?_
  rintro s4 P4 hpc4 hrun4 hcl4 ⟨hsp4, hx19_4, hx20_4, _, hus4, hP4⟩
  let wp5 := seg3_copy2_setup3 hb hbase s0 s4 sp bs1
    (memRegion sp 16 ∗ ((sp + 16#64) ↦ₛ pk) ∗ ((sp + 1200#64) ↦ₛ reducedPolyBytes bs0) ∗
      ((sp + 1712#64) ↦ₛ reducedPolyBytes bs1) ∗ ((sp + 2224#64) ↦ₛ reducedPolyBytes bs2) ∗
      ((sp + 2736#64) ↦ₛ reencodePoly384 bs0) ∗ memRegion (sp + 3504#64) 384 ∗
      memRegion (sp + 3888#64) 32 ∗ memRegion (sp + 4688#64) 32 ∗ Ft)
    hpc4 hrun4 (hsp4.trans hsp3) hspA (hx19_4.trans hx19_3) (hx20_4.trans hx20_3) hus4 hcl4
  refine sepWP_seq_cl hcl4 (SepWP.weaken_pre (Entails.trans hP4 (by sep_frame)) wp5) ?_
  rintro s5 P5 hpc5 hrun5 hcl5 ⟨hsp5, hx8_5, hx9_5, hx19_5, _, hx21_5, hus5, hP5⟩
  let wp6 := seg3_loop3 s0 (sp + 2224#64) (sp + 4304#64) bs2
    (memRegion sp 16 ∗ ((sp + 16#64) ↦ₛ pk) ∗ ((sp + 1200#64) ↦ₛ reducedPolyBytes bs0) ∗
      ((sp + 1712#64) ↦ₛ reducedPolyBytes bs1) ∗ ((sp + 2736#64) ↦ₛ reencodePoly384 bs0) ∗
      ((sp + 3120#64) ↦ₛ reencodePoly384 bs1) ∗ memRegion (sp + 3504#64) 384 ∗
      memRegion (sp + 3888#64) 32 ∗ memRegion (sp + 3920#64) 384 ∗ memRegion (sp + 4688#64) 32 ∗ Ft)
    15 0 rfl s5 hpc5 hrun5 hx8_5 hx9_5 hx21_5 hus5
  refine sepWP_seq_cl hcl5
    (SepWP.weaken_pre
      (Entails.trans hP5
        (by rw [hreg0]; simp only [reencodePolyPrefix_zero, pointsToBytes_nil]; sep_frame)) wp6) ?_
  rintro s6 P6 hpc6 hrun6 hcl6 ⟨hsp6, hx19_6, _, _, hus6, hP6⟩
  let wp7 := seg3_copy3 hb hbase s0 s6 sp bs2
    (memRegion sp 16 ∗ ((sp + 16#64) ↦ₛ pk) ∗ ((sp + 1200#64) ↦ₛ reducedPolyBytes bs0) ∗
      ((sp + 1712#64) ↦ₛ reducedPolyBytes bs1) ∗ ((sp + 2224#64) ↦ₛ reducedPolyBytes bs2) ∗
      ((sp + 2736#64) ↦ₛ reencodePoly384 bs0) ∗ ((sp + 3120#64) ↦ₛ reencodePoly384 bs1) ∗
      memRegion (sp + 3888#64) 32 ∗ memRegion (sp + 4688#64) 32 ∗ Ft)
    hpc6 hrun6 (hsp6.trans hsp5) hspA (hx19_6.trans hx19_5) hus6 hcl6
  refine sepWP_seq_cl hcl6 (SepWP.weaken_pre (Entails.trans hP6 (by sep_frame)) wp7) ?_
  rintro s7 P7 hpc7 hrun7 hcl7 ⟨hsp7, hx19_7, hus7, hP7⟩
  let wp8 := seg3_seed_prep hb hbase s0 s7 sp hdr ek bs0 bs1 bs2
    (memRegion sp 16 ∗ ((sp + 1200#64) ↦ₛ reducedPolyBytes bs0) ∗
      ((sp + 1712#64) ↦ₛ reducedPolyBytes bs1) ∗ ((sp + 2224#64) ↦ₛ reducedPolyBytes bs2) ∗
      memRegion (sp + 3920#64) 384 ∗ memRegion (sp + 4304#64) 384 ∗ memRegion (sp + 4688#64) 32 ∗ Ft)
    hhdr hek hpc7 hrun7 hsp7 hspA hx19_7 hus7
  refine sepWP_seq_cl hcl7
    (SepWP.weaken_pre (Entails.trans hP7 (by dsimp only [pk]; sep_frame)) wp8) ?_
  rintro s8 P8 hpc8 hrun8 hcl8 ⟨hsp8, hx0_8, hx1_8, hx2_8, hus8, hP8⟩
  have hpk_len : pk.length = 1184 := by simp [pk, hek, hhdr]
  have hpkRe_len : pkRe.length = 1184 := by simp [pkRe, hhdr]
  let wp9 := seg3_bcmp_call hb hbase s0 s8 sp pk pkRe
    (memRegion sp 16 ∗ ((sp + 1200#64) ↦ₛ reducedPolyBytes bs0) ∗
      ((sp + 1712#64) ↦ₛ reducedPolyBytes bs1) ∗ ((sp + 2224#64) ↦ₛ reducedPolyBytes bs2) ∗
      memRegion (sp + 3920#64) 384 ∗ memRegion (sp + 4304#64) 384 ∗ memRegion (sp + 4688#64) 32 ∗ Ft)
    hpk_len hpkRe_len hpc8 hrun8 hsp8 hspA hx0_8 hx1_8 hx2_8 hus8 hcl8
  refine SepWP.seq (SepWP.weaken_pre (Entails.trans hP8 (by dsimp only [pk, pkRe]; sep_frame)) wp9) ?_
  rintro s9 P9 hpc9 hrun9 ⟨hsp9, hus9, hbcmp, hP9⟩
  refine SepWP.weaken_pre
    (Entails.trans hP9
      (entails_sub (frame4720_seg3_collapse sp pk pkRe bs0 bs1 bs2 hpk_len hpkRe_len)
        (by sep_frame)
        (show memRegion sp 4720 ∗ Ft ⊢
          SavedFrame s0.sp s0 ∗ memRegion (s0.sp - 4784#64) 4720 ∗
            stackAt (s0.sp - 4784#64) 1040 ∗ ((hdrA ↦ₛ hdr) ∗ (ekA ↦ₛ ek) ∗ R) by
          dsimp only [sp, Ft]; sep_frame))) ?_
  wp_step
  wp_if hcond
  · have hw0 : s9.readReg32 .x0 = 0#32 :=
      (setWidth64_setWidth32_eq_zero_iff (s9.readReg64 (.gpr 0#5))).mp (by simpa using hcond)
    have hvalid : mlkem768ValidPk hdr ek = true :=
      (reencode_bcmp_eq_iff_validPk hhdr hek hhash).mp (hbcmp.mp hw0)
    refine sepWP_mono_ret ?_
      (seg_ret_ok hb hbase s0 _ ((hdrA ↦ₛ hdr) ∗ (ekA ↦ₛ ek) ∗ R)
        (by simp [wp_norm, arm64_norm]) (by simp [hrun9]) (by simpa [sp] using hsp9) hsp0
        ⟨by simp [hus9.1], by simp [hus9.2.1], by simp [hus9.2.2.1], by simp [hus9.2.2.2.1],
          by simp [calleeSavedVRegs, hus9.2.2.2.2]⟩)
    rw [hvalid]; simp
  · have hw0 : s9.readReg32 .x0 ≠ 0#32 := by
      intro hz
      exact hcond (by
        simpa using (setWidth64_setWidth32_eq_zero_iff (s9.readReg64 (.gpr 0#5))).mpr hz)
    have hnvalid : mlkem768ValidPk hdr ek ≠ true := by
      intro hv
      exact hw0 (hbcmp.mpr ((reencode_bcmp_eq_iff_validPk hhdr hek hhash).mpr hv))
    refine sepWP_mono_ret ?_
      (seg_ret_err2 hb hbase s0 _ ((hdrA ↦ₛ hdr) ∗ (ekA ↦ₛ ek) ∗ R)
        (by simp [wp_norm, arm64_norm]) (by simp [hrun9]) (by simpa [sp] using hsp9) hsp0
        ⟨by simp [hus9.1], by simp [hus9.2.1], by simp [hus9.2.2.1], by simp [hus9.2.2.2.1],
          by simp [calleeSavedVRegs, hus9.2.2.2.2]⟩)
    exact ⟨(fun h => nomatch h), fun hv => False.elim (hnvalid hv)⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg3
