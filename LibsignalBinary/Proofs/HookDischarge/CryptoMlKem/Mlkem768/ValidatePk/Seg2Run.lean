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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg1 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2Loop
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2Loops

/-!
# `validate_pk_bytes` (`B21`) — Segment 2 Execution (`+0x00b0 .. +0x044c`)

Steps the three 16-iteration AdvSIMD `deserialize_12` loops (`ek0`, `ek1`, `ek2` from `Seg2Loops`),
unrolled dead-store zeroing blocks, three `B28` (`memcpy`) copies into `sp + 1200`, `sp + 1712`,
`sp + 2224`, and the `B29` (`memset`) scratch clear, establishing `Seg3Pre` and `Seg3Spatial`
at `b + 0x044c#64`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2Run

open Arm64 Arm64.Obj ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement add_off_reloc_cancel add_reloc_cancel add_zero_reloc_cancel
  fetch_rebase_ldst128Lo12_site mbase mlkemBlockPlacement_ρ mlkemCall_of_blockOk mlkemMpl
  resolve_blk28 resolve_blk29 resolve_ro05 seq_codeLoaded_lr
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (mlkemMemcpySpec mlkemMemsetSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk cst16Vec cst16_3_vec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps (blk28_memcpy_ok blk29_memset_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Base (
  blk21_code_eq blk21_tree_size blkLib21 blkPC21 blkPl21 blkPlaceable21 blkTree21)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg1 (
  SavedFrame Seg2Pre Seg2Spatial UnspilledSaved cells16_entails_memRegion entails_sub
  sepWP_elim_region16 sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2 (
  Seg3Pre Seg3Spatial deserVec8h reducedPolyBytes reducedPolyBytes_length reducedPolyPrefix
  reducedPolyPrefix_zero setPC_setMem_collapse step_ldrQ128_ro)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2Loop (
  dup8x16_3329 exec_simdDup_8h_gpr exec_simdMovi_2d_0 exec_simdMvni_4s_msl16_3
  pk_pointsToBytes_split4 step_dead_stpQ step_dead_strQ)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2Loops (
  seg2_loop1 seg2_loop2 seg2_loop3)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC21 blkLib21 blkTree21 blk21_code_eq blk21_tree_size
  via_placement blkPl21 blkPlaceable21
  [0x00b0 → 0x01d4, 0x0238 → 0x02ec, 0x0350 → 0x03c0, 0x0424 → 0x0448]
gen_placed_odd_sites blkPC21 blkLib21 blkTree21 blk21_code_eq blk21_tree_size
  via_placement blkPl21 blkPlaceable21 [0x00b0 → 0x00c4]

@[simp, arm64_norm]
private theorem blkPC21_rebase_fetchOff_00c4 [MlKemPlacement] (b : BitVec 64)
    (X : String → Option (Arm64.State → Arm64.State)) :
    (blkPC21.rebase b X).fetch (b + BitVec.ofNat 64 196) =
      some (.ldrSimd .Q128 (BitVec.ofNat 5 6)
        (.Offset (.gpr (BitVec.ofNat 5 9)) (lo12Of (blkPl21.ρ "libcrux_ml_kem:.rodata.cst16.3")))) :=
  fetch_rebase_ldst128Lo12_site (lib := blkLib21) (prog := blkPC21) (pl := blkPl21)
    (b := b) (X := X) (off := 196)
    (r := { off := 196, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.3" })
    rfl blkPlaceable21 (by decide +kernel) rfl
    (ProofLib.GenPlacedFetches.hookAtOff?_rebase_program (by decide +kernel) 196)
    (ProofLib.GenPlacedFetches.wordAt_of_getQuad? (j := 49) blk21_code_eq blk21_tree_size rfl)
    rfl rfl rfl rfl (ProofLib.GenPlacedFetches.target_of_extern_zero rfl (by decide +kernel) rfl)
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl21_ρ [MlKemPlacement] (sym : String) :
    blkPl21.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl
@[simp, arm64_norm, wp_norm]
private theorem evalSimdModImmExt_mvni_4s_3 (v : BitVec 128) :
    evalSimdModImmExt true true 0#3 26#5 3#5 v = .ok 0xfffc0000fffc0000fffc0000fffc0000#128 := rfl
@[simp, arm64_norm, wp_norm]
private theorem applySimdResult_ok (s : State) (rd : BitVec 5) (res : BitVec 128) :
    applySimdResult s rd (.ok res) = (s.writeVReg128 rd res).advancePC := rfl
@[simp, arm64_norm, wp_norm]
private theorem dup8x16_3329_norm :
    dup8x16 ((3329#64 : BitVec 64).truncate 16) = 0x0d010d010d010d010d010d010d010d01#128 := dup8x16_3329

private theorem sepWP_bind_state {prog : Program} {target : BitVec 64} {s : State}
    {P : SepProp} {post : State → SepProp → Prop}
    (h : ∀ s1 : State, s1 = s → SepWP prog target s1 P post) : SepWP prog target s P post := h s rfl
private theorem state_eq_setPC_setMem (s : State) {pc : BitVec 64} (h : s.pc = pc) :
    s = (s.setPC pc).setMem s.mem := by cases s; subst h; rfl
private theorem pointsToBytes_replicate_entails_memRegion (a : BitVec 64) (n : Nat) (v : BitVec 8) :
    (a ↦ₛ List.replicate n v) ⊢ memRegion a n := by
  have h := pointsToBytes_entails_memRegion a (List.replicate n v); rwa [List.length_replicate] at h

attribute [local irreducible] deserVec8h reducedPolyBytes

local macro "dead_strQ " bo:num tot:num pc:num sp:num : tactic =>
  `(tactic| (
    intro m_cur
    refine step_dead_strQ (m := m_cur) $bo $tot ($pc : Nat) (($pc : Nat) + 4) ($sp : Nat)
      (($sp : Nat) - $bo) 2#5 ‹_› ‹_› (by simp only [BitVec.ofNat_eq_ofNat, arm64_norm])
      (by omega) (by omega) (by omega) (by omega) fun m_nxt => ?_
    clear m_cur; revert m_nxt))

local macro "dead_stpQ " tot:num pc:num off:num : tactic =>
  `(tactic| (
    intro m_cur
    refine step_dead_stpQ (m := m_cur) $tot ($pc : Nat) (($pc : Nat) + 4) ($off : Nat) 2#5 2#5
      ‹_› ‹_› (by simp only [BitVec.ofNat_eq_ofNat, arm64_norm])
      (by omega) (by omega) (by omega) fun m_nxt => ?_
    clear m_cur; revert m_nxt))

/-! ## 1. Setup 1 (`+0x00b0 → +0x01d8`) -/

private theorem seg2_setup1 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl21 b) (_hbase : blkPl21.base = b)
    (s0 s : State) (Rest : SepProp)
    (hpc : s.pc = b + 0x00b0#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4784#64) (hsp0 : s0.spAligned = true)
    (hx20 : s.readReg64 .x20 = (s0.sp - 4784#64) + 1200#64)
    (hx22 : s.readReg64 .x22 = (s0.sp - 4784#64) + 2736#64)
    (hx23 : s.readReg64 .x23 = (s0.sp - 4784#64) + 16#64)
    (hus : UnspilledSaved s0 s) (hro : MlKemRoOk mlkemMpl s.mem) :
    SepWP (blkPC21.rebase b (fun _ => none)) (b + 0x01d8#64) s
      (memRegion ((s0.sp - 4784#64) + 1200#64) 3520 ∗ Rest)
      (fun sf Pf =>
        sf.sp = s0.sp - 4784#64 ∧ sf.readReg64 .x8 = 0#64 ∧
        sf.readReg64 .x9 = (s0.sp - 4784#64) + 16#64 ∧ sf.readReg64 .x19 = (s0.sp - 4784#64) + 1168#64 ∧
        sf.readReg64 .x20 = (s0.sp - 4784#64) + 1200#64 ∧ sf.readReg64 .x21 = (s0.sp - 4784#64) + 2736#64 ∧
        sf.readReg64 .x22 = (s0.sp - 4784#64) + 2736#64 ∧ sf.readReg64 .x23 = (s0.sp - 4784#64) + 16#64 ∧
        sf.readVReg128 0#5 = 0xfffc0000fffc0000fffc0000fffc0000#128 ∧
        sf.readVReg128 1#5 = 0x0d010d010d010d010d010d010d010d01#128 ∧
        sf.readVReg128 6#5 = 0x0b0a0a09080707060504040302010100#128 ∧
        UnspilledSaved s0 sf ∧ Pf = (memRegion ((s0.sp - 4784#64) + 1200#64) 3520 ∗ Rest)) := by
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact spAligned_sub s0.sp 4784#64 hsp0 (by decide)
  wp_step; wp_step; wp_step; wp_step; wp_step
  have hfetch_ro : (blkPC21.rebase b (fun _ => none)).fetch (b + 0x00c4#64) =
      some (.ldrSimd .Q128 (BitVec.ofNat 5 6)
        (.Offset (.gpr (BitVec.ofNat 5 9))
          (lo12Of (blkPl21.ρ "libcrux_ml_kem:.rodata.cst16.3")))) :=
    blkPC21_rebase_fetchOff_00c4 b (fun _ => none)
  refine step_ldrQ128_ro (wb := none) (pc := b + 0x00c4#64)
    (roAddr := mlkemMpl.ρ "libcrux_ml_kem:.rodata.cst16.3")
    (by wp_norm_lhs) (by simp [hrun]) hfetch_ro
    rfl (by simp [evalAddrMode, wp_norm, arm64_norm]) hro.cst16_3 (by decide +kernel) cst16_3_vec
    (by wp_norm_lhs) ?_
  wp_steps 4; refine sepWP_bind_state fun s1 hs1 => ?_
  have hrun1 : s1.status = .Running := by simp [hs1, hrun]
  have hspA1 : s1.spAligned = true := by simp [hs1, State.spAligned] at hspA ⊢; exact hspA
  have hsp1 : s1.sp = s0.sp - 4784#64 := by simp [hs1, hsp]
  conv => arg 3; rw [state_eq_setPC_setMem s1 (pc := b + BitVec.ofNat 64 0x00d8) (by simp [hs1, wp_norm, arm64_norm])]
  conv => arg 4; rw [← hsp1, show (1200#64 : BitVec 64) = BitVec.ofNat 64 1200 from rfl]
  generalize s1.mem = m; revert m
  dead_strQ 1200 3520 0x00d8 2720; dead_strQ 1200 3520 0x00dc 2704; dead_strQ 1200 3520 0x00e0 2688; dead_strQ 1200 3520 0x00e4 2672; dead_strQ 1200 3520 0x00e8 2656; dead_strQ 1200 3520 0x00ec 2640; dead_strQ 1200 3520 0x00f0 2624; dead_strQ 1200 3520 0x00f4 2608
  dead_strQ 1200 3520 0x00f8 2592; dead_strQ 1200 3520 0x00fc 2576; dead_strQ 1200 3520 0x0100 2560; dead_strQ 1200 3520 0x0104 2544; dead_strQ 1200 3520 0x0108 2528; dead_strQ 1200 3520 0x010c 2512; dead_strQ 1200 3520 0x0110 2496; dead_strQ 1200 3520 0x0114 2480
  dead_strQ 1200 3520 0x0118 2464; dead_strQ 1200 3520 0x011c 2448; dead_strQ 1200 3520 0x0120 2432; dead_strQ 1200 3520 0x0124 2416; dead_strQ 1200 3520 0x0128 2400; dead_strQ 1200 3520 0x012c 2384; dead_strQ 1200 3520 0x0130 2368; dead_strQ 1200 3520 0x0134 2352
  dead_strQ 1200 3520 0x0138 2336; dead_strQ 1200 3520 0x013c 2320; dead_strQ 1200 3520 0x0140 2304; dead_strQ 1200 3520 0x0144 2288; dead_strQ 1200 3520 0x0148 2272; dead_strQ 1200 3520 0x014c 2256; dead_strQ 1200 3520 0x0150 2240; dead_strQ 1200 3520 0x0154 2224
  dead_strQ 1200 3520 0x0158 3232; dead_strQ 1200 3520 0x015c 3216; dead_strQ 1200 3520 0x0160 3200; dead_strQ 1200 3520 0x0164 3184; dead_strQ 1200 3520 0x0168 3168; dead_strQ 1200 3520 0x016c 3152; dead_strQ 1200 3520 0x0170 3136; dead_strQ 1200 3520 0x0174 3120
  dead_strQ 1200 3520 0x0178 3104; dead_strQ 1200 3520 0x017c 3088; dead_strQ 1200 3520 0x0180 3072; dead_strQ 1200 3520 0x0184 3056; dead_strQ 1200 3520 0x0188 3040; dead_strQ 1200 3520 0x018c 3024; dead_strQ 1200 3520 0x0190 3008; dead_strQ 1200 3520 0x0194 2992
  dead_strQ 1200 3520 0x0198 2976; dead_strQ 1200 3520 0x019c 2960; dead_strQ 1200 3520 0x01a0 2944; dead_strQ 1200 3520 0x01a4 2928; dead_strQ 1200 3520 0x01a8 2912; dead_strQ 1200 3520 0x01ac 2896; dead_strQ 1200 3520 0x01b0 2880; dead_strQ 1200 3520 0x01b4 2864
  dead_strQ 1200 3520 0x01b8 2848; dead_strQ 1200 3520 0x01bc 2832; dead_strQ 1200 3520 0x01c0 2816; dead_strQ 1200 3520 0x01c4 2800; dead_strQ 1200 3520 0x01c8 2784; dead_strQ 1200 3520 0x01cc 2768; dead_strQ 1200 3520 0x01d0 2752; dead_strQ 1200 3520 0x01d4 2736
  intro _
  apply SepWP.done (by simp) (by simp [hrun1])
  exact ⟨by simp [hsp1], by simp [hs1], by simp [hs1]; bv_omega, by simp [hs1]; bv_omega,
      by simp [hs1, hx20], by simp [hs1]; bv_omega, by simp [hs1, hx22], by simp [hs1, hx23],
      by simp [hs1], by simp [hs1], by simp [hs1],
      ⟨by simp [hs1, hus.1], by simp [hs1, hus.2.1], by simp [hs1, hus.2.2.1],
        by simp [hs1, hus.2.2.2.1], by simp [hs1, calleeSavedVRegs, hus.2.2.2.2]⟩,
      by rw [hsp1]⟩

/-! ## 2. `memcpy` #1 + Setup 2 (`+0x0238 → +0x02f0`) & `memcpy` #2 + Setup 3 (`+0x0350 → +0x03c4`) -/

private theorem seg2_memcpy1_setup2 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl21 b) (_hbase : blkPl21.base = b)
    (s0 s : State) (sp : BitVec 64) (bs0 : List (BitVec 8)) (Rest : SepProp)
    (hpc : s.pc = b + 0x0238#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : (sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = sp + 1168#64)
    (hx20 : s.readReg64 .x20 = sp + 1200#64)
    (hx21 : s.readReg64 .x21 = sp + 2736#64)
    (hx23 : s.readReg64 .x23 = sp + 16#64)
    (hv6 : s.readVReg128 6#5 = 0x0b0a0a09080707060504040302010100#128)
    (hus : UnspilledSaved s0 s) (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC21.rebase b (fun _ => none)) (b + 0x02f0#64) s
      (memRegion sp 16 ∗ memRegion (sp + 1200#64) 512 ∗
        ((sp + 2736#64) ↦ₛ reducedPolyBytes bs0) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.readReg64 .x8 = (sp + 2736#64) + BitVec.ofNat 64 (32 * 0) + 16#64 ∧
        sf.readReg64 .x9 = BitVec.ofNat 64 (24 * 0) - 384#64 ∧ sf.readReg64 .x10 = sp + 16#64 ∧
        sf.readReg64 .x19 = sp + 1168#64 ∧ sf.readReg64 .x20 = sp + 1200#64 ∧
        sf.readReg64 .x21 = sp + 2736#64 ∧ sf.readReg64 .x23 = sp + 16#64 ∧
        sf.readVReg128 0#5 = 0xfffc0000fffc0000fffc0000fffc0000#128 ∧
        sf.readVReg128 1#5 = 0x0d010d010d010d010d010d010d010d01#128 ∧
        sf.readVReg128 6#5 = 0x0b0a0a09080707060504040302010100#128 ∧ UnspilledSaved s0 sf ∧
        (Pf ⊢ (sp ↦₆₄ 0x0504040302010100#64) ∗ ((sp + 8#64) ↦₆₄ 0x0b0a0a0908070706#64) ∗
          ((sp + 1200#64) ↦ₛ reducedPolyBytes bs0) ∗ memRegion (sp + 2736#64) 512 ∗ Rest)) := by
  have hsp_align : s.spAligned = true := by rw [State.spAligned, hsp]; exact hspA
  have hlen0 : (reducedPolyBytes bs0).length = 512 := reducedPolyBytes_length bs0
  apply sepWP_elim_region16; intro q0 q1
  rw [show memRegion (sp + 1200#64) 512 =
      memRegion (sp + 1200#64) (reducedPolyBytes bs0).length by rw [hlen0]]
  wp_cut_codeLoaded
  wp_steps
  wp_mlkem_call blk28_memcpy_ok (sp + 1200#64, sp + 2736#64, reducedPolyBytes bs0)
  have hus_sf : UnspilledSaved s0 sf :=
    ⟨h_5.trans hus.1, h_6.trans hus.2.1, h_7.trans hus.2.2.1, h_8.trans hus.2.2.2.1,
      hvregs.trans hus.2.2.2.2⟩
  have hsp_sf' : sf.sp = sp := hsp_sf.trans hsp
  have hspA_sf : sf.spAligned = true := by rw [State.spAligned, hsp_sf']; exact hspA
  have hpts_reg : ((sp + 2736#64) ↦ₛ reducedPolyBytes bs0) ⊢ memRegion (sp + 2736#64) 512 := by
    simpa [reducedPolyBytes_length] using
      pointsToBytes_entails_memRegion (sp + 2736#64) (reducedPolyBytes bs0)
  refine SepWP.weaken_pre
    (entails_sub hpts_reg (by sep_frame)
      (show memRegion (sp + 2736#64) 512 ∗ _ ⊢
        (sp ↦₆₄ 0x0504040302010100#64) ∗ ((sp + 8#64) ↦₆₄ 0x0b0a0a0908070706#64) ∗
        memRegion (sp + 2736#64) 512 ∗ (((sp + 1200#64) ↦ₛ reducedPolyBytes bs0) ∗ Rest) by
        sep_frame)) ?_
  wp_steps 8
  refine SepWP.weaken_pre
    (show _ ⊢ memRegion (sp + 2736#64) 512 ∗
      ((sp ↦₆₄ 0x0504040302010100#64) ∗ ((sp + 8#64) ↦₆₄ 0x0b0a0a0908070706#64) ∗
        ((sp + 1200#64) ↦ₛ reducedPolyBytes bs0) ∗ Rest) by
      sep_frame) ?_
  refine sepWP_bind_state fun s1 hs1 => ?_
  have hrun1 : s1.status = .Running := by simp [hs1, hrun_sf]
  have hspA1 : s1.spAligned = true := by simp [hs1, State.spAligned] at hspA_sf ⊢; exact hspA_sf
  have hsp1 : s1.sp = sp := by simp [hs1, hsp_sf']
  conv => arg 3; rw [state_eq_setPC_setMem s1 (pc := b + BitVec.ofNat 64 0x0270) (by simp [hs1, wp_norm, arm64_norm])]
  conv => arg 4; arg 1; rw [← hsp1, show (2736#64 : BitVec 64) = BitVec.ofNat 64 2736 from rfl]
  generalize s1.mem = m; revert m
  dead_strQ 2736 512 0x0270 3232; dead_strQ 2736 512 0x0274 3216; dead_strQ 2736 512 0x0278 3200; dead_strQ 2736 512 0x027c 3184; dead_strQ 2736 512 0x0280 3168; dead_strQ 2736 512 0x0284 3152; dead_strQ 2736 512 0x0288 3136; dead_strQ 2736 512 0x028c 3120
  dead_strQ 2736 512 0x0290 3104; dead_strQ 2736 512 0x0294 3088; dead_strQ 2736 512 0x0298 3072; dead_strQ 2736 512 0x029c 3056; dead_strQ 2736 512 0x02a0 3040; dead_strQ 2736 512 0x02a4 3024; dead_strQ 2736 512 0x02a8 3008; dead_strQ 2736 512 0x02ac 2992
  dead_strQ 2736 512 0x02b0 2976; dead_strQ 2736 512 0x02b4 2960; dead_strQ 2736 512 0x02b8 2944; dead_strQ 2736 512 0x02bc 2928; dead_strQ 2736 512 0x02c0 2912; dead_strQ 2736 512 0x02c4 2896; dead_strQ 2736 512 0x02c8 2880; dead_strQ 2736 512 0x02cc 2864
  dead_strQ 2736 512 0x02d0 2848; dead_strQ 2736 512 0x02d4 2832; dead_strQ 2736 512 0x02d8 2816; dead_strQ 2736 512 0x02dc 2800; dead_strQ 2736 512 0x02e0 2784; dead_strQ 2736 512 0x02e4 2768; dead_strQ 2736 512 0x02e8 2752; dead_strQ 2736 512 0x02ec 2736
  intro _
  apply SepWP.done (by simp) (by simp [hrun1])
  refine ⟨by simp [hsp1], by simp [hs1], by simp [hs1], by simp [hs1], by simp [hs1, h, hx19],
      by simp [hs1, h_1, hx20], by simp [hs1, h_2, hx21], by simp [hs1, h_4, hx23], by simp [hs1],
      by simp [hs1], by simp [hs1],
      ⟨by simp [hs1, hus_sf.1], by simp [hs1, hus_sf.2.1], by simp [hs1, hus_sf.2.2.1],
        by simp [hs1, hus_sf.2.2.2.1], by simp [hs1, calleeSavedVRegs, hus_sf.2.2.2.2]⟩, ?_⟩
  rw [hsp1, show BitVec.ofNat 64 2736 = 2736#64 from rfl]; sep_frame

private theorem seg2_memcpy2_setup3 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl21 b) (_hbase : blkPl21.base = b)
    (s0 s : State) (sp : BitVec 64) (bs1 : List (BitVec 8)) (Rest : SepProp)
    (hpc : s.pc = b + 0x0350#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : (sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = sp + 1168#64) (hx20 : s.readReg64 .x20 = sp + 1200#64)
    (hx21 : s.readReg64 .x21 = sp + 2736#64) (hx23 : s.readReg64 .x23 = sp + 16#64)
    (hus : UnspilledSaved s0 s) (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC21.rebase b (fun _ => none)) (b + 0x03c4#64) s
      ((sp ↦₆₄ 0x0504040302010100#64) ∗ ((sp + 8#64) ↦₆₄ 0x0b0a0a0908070706#64) ∗
        memRegion (sp + 1712#64) 512 ∗ ((sp + 2736#64) ↦ₛ reducedPolyBytes bs1) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.readReg64 .x8 = (sp + 2736#64) + BitVec.ofNat 64 (32 * 0) + 16#64 ∧
        sf.readReg64 .x9 = BitVec.ofNat 64 (24 * 0) - 384#64 ∧ sf.readReg64 .x10 = sp + 16#64 ∧
        sf.readReg64 .x19 = sp + 1168#64 ∧ sf.readReg64 .x20 = sp + 2736#64 ∧
        sf.readReg64 .x21 = sp + 2736#64 ∧ sf.readReg64 .x23 = sp + 16#64 ∧
        sf.readVReg128 0#5 = 0xfffc0000fffc0000fffc0000fffc0000#128 ∧
        sf.readVReg128 1#5 = 0x0d010d010d010d010d010d010d010d01#128 ∧
        sf.readVReg128 6#5 = 0x0b0a0a09080707060504040302010100#128 ∧ UnspilledSaved s0 sf ∧
        (Pf ⊢ memRegion sp 16 ∗ ((sp + 1712#64) ↦ₛ reducedPolyBytes bs1) ∗
          memRegion (sp + 2736#64) 512 ∗ Rest)) := by
  have hsp_align : s.spAligned = true := by rw [State.spAligned, hsp]; exact hspA
  have ha1712 : sp + 1200#64 + 512#64 = sp + 1712#64 := by bv_omega
  have hlen1 : (reducedPolyBytes bs1).length = 512 := reducedPolyBytes_length bs1
  rw [show memRegion (sp + 1712#64) 512 =
      memRegion (sp + 1712#64) (reducedPolyBytes bs1).length by rw [hlen1]]
  wp_cut_codeLoaded; wp_steps
  wp_mlkem_call blk28_memcpy_ok (sp + 1712#64, sp + 2736#64, reducedPolyBytes bs1)
  have hus_sf : UnspilledSaved s0 sf :=
    ⟨h_5.trans hus.1, h_6.trans hus.2.1, h_7.trans hus.2.2.1, h_8.trans hus.2.2.2.1, hvregs.trans hus.2.2.2.2⟩
  have hsp_sf' : sf.sp = sp := hsp_sf.trans hsp
  have hspA_sf : sf.spAligned = true := by rw [State.spAligned, hsp_sf']; exact hspA
  have hpts_reg : ((sp + 2736#64) ↦ₛ reducedPolyBytes bs1) ⊢ memRegion (sp + 2736#64) 512 := by
    simpa [reducedPolyBytes_length] using pointsToBytes_entails_memRegion (sp + 2736#64) (reducedPolyBytes bs1)
  refine SepWP.weaken_pre
    (entails_sub hpts_reg (by sep_frame)
      (show memRegion (sp + 2736#64) 512 ∗ _ ⊢
        (sp ↦₆₄ 0x0504040302010100#64) ∗ ((sp + 8#64) ↦₆₄ 0x0b0a0a0908070706#64) ∗
          memRegion (sp + 2736#64) 512 ∗ (((sp + 1712#64) ↦ₛ reducedPolyBytes bs1) ∗ Rest) by sep_frame)) ?_
  wp_steps 8
  refine SepWP.weaken_pre
    (entails_sub (cells16_entails_memRegion sp 0x0504040302010100#64 0x0b0a0a0908070706#64) (by sep_frame)
      (show memRegion sp 16 ∗ _ ⊢
        memRegion (sp + 2736#64) 512 ∗ (memRegion sp 16 ∗ ((sp + 1712#64) ↦ₛ reducedPolyBytes bs1) ∗ Rest) by sep_frame)) ?_
  refine sepWP_bind_state fun s1 hs1 => ?_
  have hrun1 : s1.status = .Running := by simp [hs1, hrun_sf]
  have hx21_1 : s1.readReg64 .x21 = sp + 2736#64 := by simp [hs1, h_2, hx21]
  conv => arg 3; rw [state_eq_setPC_setMem s1 (pc := b + BitVec.ofNat 64 0x0384) (by simp [hs1, wp_norm, arm64_norm])]
  generalize s1.mem = m; revert m
  dead_stpQ 512 0x0384 0;   dead_stpQ 512 0x0388 32;  dead_stpQ 512 0x038c 64;  dead_stpQ 512 0x0390 96;  dead_stpQ 512 0x0394 128; dead_stpQ 512 0x0398 160; dead_stpQ 512 0x039c 192; dead_stpQ 512 0x03a0 224
  dead_stpQ 512 0x03a4 256; dead_stpQ 512 0x03a8 288; dead_stpQ 512 0x03ac 320; dead_stpQ 512 0x03b0 352; dead_stpQ 512 0x03b4 384; dead_stpQ 512 0x03b8 416; dead_stpQ 512 0x03bc 448; dead_stpQ 512 0x03c0 480
  intro _
  apply SepWP.done (by simp) (by simp [hrun1])
  exact ⟨by simp [hs1, hsp_sf'], by simp [hs1], by simp [hs1], by simp [hs1],
      by simp [hs1, h, hx19], by simp [hs1, h_1], by simp [hx21_1], by simp [hs1, h_4, hx23], by simp [hs1],
      by simp [hs1], by simp [hs1],
      ⟨by simp [hs1, hus_sf.1], by simp [hs1, hus_sf.2.1], by simp [hs1, hus_sf.2.2.1],
        by simp [hs1, hus_sf.2.2.2.1], by simp [hs1, calleeSavedVRegs, hus_sf.2.2.2.2]⟩,
      by sep_frame⟩

/-! ## 3. `memcpy` #3 + `memset` (`+0x0424 → +0x044c`) & Top-Level `seg2_ok` -/

private theorem seg2_memset [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl21 b) (_hbase : blkPl21.base = b)
    (s0 s : State) (sp : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = b + 0x0438#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : (sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = sp + 1168#64) (hx21 : s.readReg64 .x21 = sp + 1200#64)
    (hus : UnspilledSaved s0 s) (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC21.rebase b (fun _ => none)) (b + 0x044c#64) s
      (memRegion (sp + 3120#64) 800 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.readReg64 .x19 = sp + 1168#64 ∧ sf.readReg64 .x20 = sp + 2736#64 ∧
        sf.readReg64 .x21 = sp + 1200#64 ∧ UnspilledSaved s0 sf ∧
        (Pf ⊢ memRegion (sp + 3120#64) 800 ∗ Rest)) := by
  have hsp_align : s.spAligned = true := by rw [State.spAligned, hsp]; exact hspA
  have ha3120 : sp + 2736#64 + 384#64 = sp + 3120#64 := by bv_omega
  wp_cut_codeLoaded; wp_steps
  wp_mlkem_call blk29_memset_ok (sp + 3120#64, 0#8, 800)
  have hus_sf : UnspilledSaved s0 sf :=
    ⟨h_5.trans hus.1, h_6.trans hus.2.1, h_7.trans hus.2.2.1, h_8.trans hus.2.2.2.1, hvregs.trans hus.2.2.2.2⟩
  refine SepWP.done hpc_sf hrun_sf
    ⟨hsp_sf.trans hsp, h.trans hx19, h_1, h_2.trans hx21, hus_sf,
      entails_sub (pointsToBytes_replicate_entails_memRegion (sp + 3120#64) 800 0#8)
        (by sep_frame) (by sep_frame)⟩

private theorem seg2_memcpy3_memset [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl21 b) (_hbase : blkPl21.base = b)
    (s0 s : State) (sp : BitVec 64) (bs2 : List (BitVec 8)) (Rest : SepProp)
    (hpc : s.pc = b + 0x0424#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : (sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = sp + 1168#64)
    (hus : UnspilledSaved s0 s) (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC21.rebase b (fun _ => none)) (b + 0x044c#64) s
      (memRegion (sp + 2224#64) 512 ∗ ((sp + 2736#64) ↦ₛ reducedPolyBytes bs2) ∗
        memRegion (sp + 3248#64) 1472 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.readReg64 .x19 = sp + 1168#64 ∧ sf.readReg64 .x20 = sp + 2736#64 ∧
        sf.readReg64 .x21 = sp + 1200#64 ∧ UnspilledSaved s0 sf ∧
        (Pf ⊢ ((sp + 2224#64) ↦ₛ reducedPolyBytes bs2) ∗ memRegion (sp + 2736#64) 1984 ∗ Rest)) := by
  have hsp_align : s.spAligned = true := by rw [State.spAligned, hsp]; exact hspA
  have ha2224 : sp + 1200#64 + 1024#64 = sp + 2224#64 := by bv_omega
  have hlen2 : (reducedPolyBytes bs2).length = 512 := reducedPolyBytes_length bs2
  rw [show memRegion (sp + 2224#64) 512 =
      memRegion (sp + 2224#64) (reducedPolyBytes bs2).length by rw [hlen2]]
  wp_cut_codeLoaded; wp_steps
  wp_mlkem_call blk28_memcpy_ok (sp + 2224#64, sp + 2736#64, reducedPolyBytes bs2)
  have hus1 : UnspilledSaved s0 sf :=
    ⟨h_5.trans hus.1, h_6.trans hus.2.1, h_7.trans hus.2.2.1, h_8.trans hus.2.2.2.1, hvregs.trans hus.2.2.2.2⟩
  have h1984 : memRegion (sp + 2736#64) 1984 = memRegion (sp + 2736#64) 512 ∗ memRegion (sp + 3248#64) 1472 :=
    memRegion_split' (b := sp + 2736#64) (b' := sp + 3248#64) (n := 512) (k := (1472 : Nat)) (by bv_omega) (by bv_omega) (by decide)
  have h1984_ms : memRegion (sp + 2736#64) 1984 =
      memRegion (sp + 2736#64) 384 ∗ memRegion (sp + 3120#64) 800 ∗ memRegion (sp + 3920#64) 800 := by
    rw [memRegion_split' (b := sp + 2736#64) (b' := sp + 3120#64) (n := 384) (k := (1600 : Nat)) (by bv_omega) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 3120#64) (b' := sp + 3920#64) (n := 800) (k := 800) (by bv_omega) (by bv_omega) (by decide)]
  have hpts512 : ((sp + 2736#64) ↦ₛ reducedPolyBytes bs2) ⊢ memRegion (sp + 2736#64) 512 := by
    simpa [hlen2] using pointsToBytes_entails_memRegion (sp + 2736#64) (reducedPolyBytes bs2)
  have h512_ms : memRegion (sp + 2736#64) 512 ∗ memRegion (sp + 3248#64) 1472 ⊢
      memRegion (sp + 2736#64) 384 ∗ memRegion (sp + 3120#64) 800 ∗ memRegion (sp + 3920#64) 800 := by
    rw [← h1984, h1984_ms]; exact Entails.refl _
  let wp_ms := seg2_memset _hb _hbase s0 sf sp
    (((sp + 2224#64) ↦ₛ reducedPolyBytes bs2) ∗ memRegion (sp + 2736#64) 384 ∗ memRegion (sp + 3920#64) 800 ∗ Rest)
    hpc_sf hrun_sf (hsp_sf.trans hsp) hspA (h.trans hx19) (h_2.trans (by simp)) hus1 (by assumption)
  refine SepWP.weaken_pre
    (entails_sub hpts512 (by sep_frame) (entails_sub h512_ms (by sep_frame) (by sep_frame)))
    (SepWP.mono wp_ms fun sf2 Pf2 _ _ ⟨hsp2, hx19_2, hx20_2, hx21_2, hus2, hPf2⟩ =>
      ⟨hsp2, hx19_2, hx20_2, hx21_2, hus2, Entails.trans hPf2 (by rw [h1984_ms]; sep_frame)⟩)

private theorem frame3520_split5 (sp : BitVec 64) :
    memRegion (sp + 1200#64) 3520 =
      memRegion (sp + 1200#64) 512 ∗ memRegion (sp + 1712#64) 512 ∗
      memRegion (sp + 2224#64) 512 ∗ memRegion (sp + 2736#64) 512 ∗
      memRegion (sp + 3248#64) 1472 := by
  rw [memRegion_split' (b := sp + 1200#64) (b' := sp + 1712#64) (n := 512) (k := (3008 : Nat)) (by bv_omega) (by bv_omega) (by decide),
    memRegion_split' (b := sp + 1712#64) (b' := sp + 2224#64) (n := 512) (k := (2496 : Nat)) (by bv_omega) (by bv_omega) (by decide),
    memRegion_split' (b := sp + 2224#64) (b' := sp + 2736#64) (n := 512) (k := (1984 : Nat)) (by bv_omega) (by bv_omega) (by decide),
    memRegion_split' (b := sp + 2736#64) (b' := sp + 3248#64) (n := 512) (k := (1472 : Nat)) (by bv_omega) (by bv_omega) (by decide)]

theorem seg2_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl21 b) (hbase : blkPl21.base = b)
    (s0 sm : State) (hdrA ekA : BitVec 64) (hdr ek : List (BitVec 8)) (R : SepProp)
    (hpc : sm.pc = b + 0x00b0#64) (hrun : sm.status = .Running) (hsp0 : s0.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl sm.mem) (hro : MlKemRoOk mlkemMpl sm.mem)
    (hpre : Seg2Pre s0 sm hdr ek) :
    SepWP (blkPC21.rebase b (fun _ => none)) (b + 0x044c#64) sm
      (Seg2Spatial s0 hdrA hdr ekA ek R)
      (fun sf Pf => Seg3Pre s0 sf hdr ek ∧ (Pf ⊢ Seg3Spatial s0 hdrA hdr ekA ek R)) := by
  rcases hpre with ⟨hhdr, hek, hhash, hsp, hus, hx20, hx22, hx23⟩
  let sp := s0.sp - 4784#64
  have hspA : (sp &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 4784#64 hsp0 (by decide)
  have hl0 : (ek.take 384).length = 384 := by simp [hek]
  have hl1 : ((ek.drop 384).take 384).length = 384 := by simp [hek]
  have hl2 : ((ek.drop 768).take 384).length = 384 := by simp [hek]
  let Ft := SavedFrame s0.sp s0 ∗ stackAt sp 1040 ∗ (hdrA ↦ₛ hdr) ∗ (ekA ↦ₛ ek) ∗ R
  let bs0 := ek.take 384; let bs1 := (ek.drop 384).take 384; let bs2 := (ek.drop 768).take 384
  have hp400_to : ((sp + 400#64) ↦ₛ bs1) ⊢ (((sp + 16#64) + 384#64) ↦ₛ bs1) := by
    rw [show (sp + 16#64) + 384#64 = sp + 400#64 by bv_omega]; exact Entails.refl _
  have hp400_fr : (((sp + 16#64) + 384#64) ↦ₛ bs1) ⊢ ((sp + 400#64) ↦ₛ bs1) := by
    rw [show (sp + 16#64) + 384#64 = sp + 400#64 by bv_omega]; exact Entails.refl _
  have hp784_to : ((sp + 784#64) ↦ₛ bs2) ⊢ (((sp + 16#64) + 768#64) ↦ₛ bs2) := by
    rw [show (sp + 16#64) + 768#64 = sp + 784#64 by bv_omega]; exact Entails.refl _
  have hp784_fr : (((sp + 16#64) + 768#64) ↦ₛ bs2) ⊢ ((sp + 784#64) ↦ₛ bs2) := by
    rw [show (sp + 16#64) + 768#64 = sp + 784#64 by bv_omega]; exact Entails.refl _
  have hreg0 : memRegion (sp + 2736#64) 512 =
      memRegion ((sp + 2736#64) + BitVec.ofNat 64 (32 * 0)) (512 - 32 * 0) := by
    simp only [Nat.mul_zero, Nat.sub_zero, BitVec.add_zero]
  unfold Seg2Spatial; dsimp only
  let wp1 := seg2_setup1 hb hbase s0 sm (memRegion sp 16 ∗ ((sp + 16#64) ↦ₛ (ek ++ hdr.take 32)) ∗ Ft)
    hpc hrun hsp hsp0 hx20 hx22 hx23 hus hro
  refine sepWP_seq_env hcl hro (SepWP.weaken_pre (by sep_frame) wp1) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hx8_1, hx9_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hv0_1, hv1_1, hv6_1, hus1, rfl⟩
  rw [frame3520_split5 sp, pk_pointsToBytes_split4 sp hdr ek hek, hreg0]
  let wp2 := seg2_loop1 s0 (sp + 16#64) (sp + 2736#64) bs0
    (memRegion sp 16 ∗ ((sp + 400#64) ↦ₛ bs1) ∗ ((sp + 784#64) ↦ₛ bs2) ∗ ((sp + 1168#64) ↦ₛ hdr.take 32) ∗
      memRegion (sp + 1200#64) 512 ∗ memRegion (sp + 1712#64) 512 ∗ memRegion (sp + 2224#64) 512 ∗
      memRegion (sp + 3248#64) 1472 ∗ Ft)
    hl0 15 0 rfl s1 hpc1 hrun1 hx8_1 (by simpa [sp] using hx9_1) hx22_1 hv0_1 hv1_1 hv6_1 hus1
  refine sepWP_seq_env hcl1 hro1
    (SepWP.weaken_pre (by simp only [reducedPolyPrefix_zero, pointsToBytes_nil]; sep_frame) wp2) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hx19_2, hx20_2, hx21_2, _, hx23_2, hv6_2, hus2, hP2⟩
  let wp3 := seg2_memcpy1_setup2 hb hbase s0 s2 sp bs0
    (((sp + 16#64) ↦ₛ bs0) ∗ ((sp + 400#64) ↦ₛ bs1) ∗ ((sp + 784#64) ↦ₛ bs2) ∗ ((sp + 1168#64) ↦ₛ hdr.take 32) ∗
      memRegion (sp + 1712#64) 512 ∗ memRegion (sp + 2224#64) 512 ∗ memRegion (sp + 3248#64) 1472 ∗ Ft)
    hpc2 hrun2 (hsp2.trans hsp1) hspA (hx19_2.trans hx19_1) (hx20_2.trans hx20_1)
    (hx21_2.trans hx21_1) (hx23_2.trans hx23_1) hv6_2 hus2 hcl2
  refine sepWP_seq_env hcl2 hro2 (SepWP.weaken_pre (Entails.trans hP2 (by sep_frame)) wp3) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 hro3
    ⟨hsp3, hx8_3, hx9_3, hx10_3, hx19_3, hx20_3, hx21_3, hx23_3, hv0_3, hv1_3, hv6_3, hus3, hP3⟩
  let wp4 := seg2_loop2 s0 (sp + 16#64) (sp + 2736#64) bs1
    ((sp ↦₆₄ 0x0504040302010100#64) ∗ ((sp + 8#64) ↦₆₄ 0x0b0a0a0908070706#64) ∗
      ((sp + 1200#64) ↦ₛ reducedPolyBytes bs0) ∗ ((sp + 16#64) ↦ₛ bs0) ∗ ((sp + 784#64) ↦ₛ bs2) ∗
      ((sp + 1168#64) ↦ₛ hdr.take 32) ∗ memRegion (sp + 1712#64) 512 ∗ memRegion (sp + 2224#64) 512 ∗
      memRegion (sp + 3248#64) 1472 ∗ Ft)
    hl1 15 0 rfl s3 hpc3 hrun3 hx8_3 hx9_3 hx10_3 hv0_3 hv1_3 hv6_3 hus3
  refine sepWP_seq_env hcl3 hro3
    (SepWP.weaken_pre
      (Entails.trans hP3 (by
        rw [hreg0]; simp only [reducedPolyPrefix_zero, pointsToBytes_nil]
        exact entails_sub hp400_to (by sep_frame) (by sep_frame))) wp4) ?_
  rintro s4 P4 hpc4 hrun4 hcl4 hro4 ⟨hsp4, hx19_4, hx20_4, hx21_4, hx23_4, hus4, hP4⟩
  let wp5 := seg2_memcpy2_setup3 hb hbase s0 s4 sp bs1
    (((sp + 16#64) ↦ₛ bs0) ∗ ((sp + 400#64) ↦ₛ bs1) ∗ ((sp + 784#64) ↦ₛ bs2) ∗ ((sp + 1168#64) ↦ₛ hdr.take 32) ∗
      ((sp + 1200#64) ↦ₛ reducedPolyBytes bs0) ∗ memRegion (sp + 2224#64) 512 ∗ memRegion (sp + 3248#64) 1472 ∗ Ft)
    hpc4 hrun4 (hsp4.trans hsp3) hspA (hx19_4.trans hx19_3) (hx20_4.trans hx20_3)
    (hx21_4.trans hx21_3) (hx23_4.trans hx23_3) hus4 hcl4
  refine sepWP_seq_env hcl4 hro4
    (SepWP.weaken_pre (Entails.trans hP4 (entails_sub hp400_fr (by sep_frame) (by sep_frame))) wp5) ?_
  rintro s5 P5 hpc5 hrun5 hcl5 hro5
    ⟨hsp5, hx8_5, hx9_5, hx10_5, hx19_5, _, _, _, hv0_5, hv1_5, hv6_5, hus5, hP5⟩
  let wp6 := seg2_loop3 s0 (sp + 16#64) (sp + 2736#64) bs2
    (memRegion sp 16 ∗ ((sp + 16#64) ↦ₛ bs0) ∗ ((sp + 400#64) ↦ₛ bs1) ∗ ((sp + 1168#64) ↦ₛ hdr.take 32) ∗
      ((sp + 1200#64) ↦ₛ reducedPolyBytes bs0) ∗ ((sp + 1712#64) ↦ₛ reducedPolyBytes bs1) ∗
      memRegion (sp + 2224#64) 512 ∗ memRegion (sp + 3248#64) 1472 ∗ Ft)
    hl2 15 0 rfl s5 hpc5 hrun5 hx8_5 hx9_5 hx10_5 hv0_5 hv1_5 hv6_5 hus5
  refine sepWP_seq_env hcl5 hro5
    (SepWP.weaken_pre
      (Entails.trans hP5 (by
        rw [hreg0]; simp only [reducedPolyPrefix_zero, pointsToBytes_nil]
        exact entails_sub hp784_to (by sep_frame) (by sep_frame))) wp6) ?_
  rintro s6 P6 hpc6 hrun6 hcl6 _ ⟨hsp6, hx19_6, _, _, _, hus6, hP6⟩
  let wp7 := seg2_memcpy3_memset hb hbase s0 s6 sp bs2
    (memRegion sp 16 ∗ ((sp + 16#64) ↦ₛ bs0) ∗ ((sp + 400#64) ↦ₛ bs1) ∗ ((sp + 784#64) ↦ₛ bs2) ∗
      ((sp + 1168#64) ↦ₛ hdr.take 32) ∗ ((sp + 1200#64) ↦ₛ reducedPolyBytes bs0) ∗
      ((sp + 1712#64) ↦ₛ reducedPolyBytes bs1) ∗ Ft)
    hpc6 hrun6 (hsp6.trans hsp5) hspA (hx19_6.trans hx19_5) hus6 hcl6
  refine SepWP.weaken_pre (Entails.trans hP6 (entails_sub hp784_fr (by sep_frame) (by sep_frame)))
    (SepWP.mono wp7 fun sf Pf _ _ ⟨hsp_f, hx19_f, hx20_f, hx21_f, hus_f, hPf⟩ =>
      ⟨⟨hhdr, hek, hhash, hsp_f, hus_f, hx19_f, hx20_f, hx21_f⟩, Entails.trans hPf (by
        unfold Seg3Spatial; dsimp only [Ft, sp, bs0, bs1, bs2]
        rw [pk_pointsToBytes_split4 (s0.sp - 4784#64) hdr ek hek]; sep_frame)⟩)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2Run
