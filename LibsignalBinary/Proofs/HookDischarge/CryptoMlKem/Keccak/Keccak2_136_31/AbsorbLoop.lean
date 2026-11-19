/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31.Prologue -- proof-setup: allow-public-import
import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Defs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.LoadSqueeze.LoadBlock
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31.Permute1
meta import ProofLib
meta import ProofLib.ProgramReflection
meta import ProofLib.GenDecodes
meta import ProofLib.GenPlacedFetches

/-!
# `B01` (`keccak2::<136, 31>`): full-block absorb loop

Proof of segments `[0x00a4 → 0x00f4]` and `[0x03ec → 0x0430]` of `mlkemBlk01`. Combines
`Prologue.prologue_ok`, `B09` (`loadBlock136_block_ok`), and `Permute1.permute1_rounds` to prove
`absorb_prefix_ok` (`[0x0000 → 0x0434]`) across all `a.in0.length / 136` full 136-byte blocks.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31.AbsorbLoop

open Arm64 ProofLib ProofLib.GenPlacedFetches SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (
  mlkemData01Bytes
  mlkemMultiLib
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (
  Keccak2ShakeArgs
  Keccak2SlicesRO
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase
  MlKemPlacement
  add_off_reloc_cancel
  add_reloc_cancel
  add_zero_reloc_cancel
  mbase
  mlkemBlockPlacement_ρ
  mlkemCall_of_blockOk
  mlkemMpl
  resolve_blk09
  seq_codeLoaded_lr
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  KeccakState
  keccakF1600
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Defs (
  Keccak2Cap8Mem
  Keccak2Cap8Mem_xorRate17
  Keccak2Mem
  Keccak2Mem_entails_memRegion
  Keccak2Q0Mem
  Keccak2Q1Mem
  Keccak2Q2Mem
  Keccak2Q3Mem
  Keccak2Rate16Mem
  Keccak2Rate17Mem
  Keccak2Vec16Mem
  keccak2Lane
  keccakXorRate17
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp (
  extractLsb_hi_append
  extractLsb_lo_append
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge (
  keccakAbsorbPrefix17
  keccakAbsorbPrefix17_size
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.LoadSqueeze.LoadBlock (
  LoadBlock136Args
  loadBlock136_block_ok
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31.Base (
  SavedCalleeFrame
  Spill11
  blk01_code_eq
  blk01_tree_size
  blkLib01
  blkPC01
  blkPl01
  blkPlaceable01
  blkTree01
  entails_sub
  memRegion176_to_spill11
  spill11_entails_memRegion176
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31.Prologue (
  AbsorbInvMem
  PostAbsorbRegs
  memRegion400_cells
  ofNat_mul136
  prologue_ok
  sepWP_seq_cl
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31.Permute1 (
  P1RoundRegs
  P1Scalars
  permute1_rounds
)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp

section
set_option linter.literalFetch false
gen_placed_fetches blkPC01 blkLib01 blkTree01 blk01_code_eq blk01_tree_size
  via_placement blkPl01 blkPlaceable01 [0x00a4 → 0x00f4]
gen_placed_fetches blkPC01 blkLib01 blkTree01 blk01_code_eq blk01_tree_size
  via_placement blkPl01 blkPlaceable01 [0x03ec → 0x0430]
end

private theorem stack96_split16 (sp1 : BitVec 64) :
    stackAt sp1 96 = memRegion (sp1 - 96#64) 80 ∗ stackAt sp1 16 := by
  unfold stackAt
  rw [memRegion_split (sp1 - 96#64) 80 16 (by decide),
      show (sp1 - 96#64) + 80#64 = sp1 - 16#64 by bv_omega]

private theorem add1_eq_ofNat (k : Nat) :
    BitVec.ofNat 64 k + 1#64 = BitVec.ofNat 64 (k + 1) := by
  rw [BitVec.ofNat_add]

private theorem cmp_k_ne_of_lt {k nBlocks : Nat} (hlt : k + 1 < nBlocks) (hn : nBlocks < 2 ^ 64) :
    BitVec.ofNat 64 k + 1#64 ≠ BitVec.ofNat 64 nBlocks := by
  intro heq
  have h := congrArg BitVec.toNat heq
  simp only [add1_eq_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : k + 1 < 2 ^ 64),
    Nat.mod_eq_of_lt hn] at h
  omega

private theorem cmp_k_eq_of_ge {k nBlocks : Nat} (hk : k < nBlocks) (hge : ¬ (k + 1 < nBlocks)) :
    BitVec.ofNat 64 k + 1#64 = BitVec.ofNat 64 nBlocks := by
  have heq : k + 1 = nBlocks := by omega
  rw [add1_eq_ofNat, heq]

private theorem bne_k_target_eq {k nBlocks : Nat} (hk : k < nBlocks) (hn : nBlocks < 2 ^ 64)
    (t1 t2 : BitVec 64) :
    (if (BitVec.ofNat 64 k + 1#64 != BitVec.ofNat 64 nBlocks) = true then t1 else t2) =
      (if k + 1 < nBlocks then t1 else t2) := by
  by_cases hlt : k + 1 < nBlocks
  · simp [hlt, bne_iff_ne, cmp_k_ne_of_lt hlt hn]
  · simp [hlt, cmp_k_eq_of_ge hk hlt]

private theorem postAbsorbRegs_of_p1Scalars {s sf s0 : State} {rcBase : BitVec 64}
    {a : Keccak2ShakeArgs}
    (hr : PostAbsorbRegs s s0 rcBase a) (hscal : P1Scalars s sf) (hrun : sf.status = .Running) :
    PostAbsorbRegs sf s0 rcBase a := by
  rcases hscal with ⟨hsp', _hx19', hx20', hx21', hx22', hx23', hx24', hx25', hx27', hfp'⟩
  exact
    { hrun      := hrun
      hsp_align := by simp only [State.spAligned, hsp']; exact hr.hsp_align
      hsp       := hsp'.trans hr.hsp
      hx29      := hfp'.trans hr.hx29
      hx27      := hx27'.trans hr.hx27
      hx25      := hx25'.trans hr.hx25
      hx24      := hx24'.trans hr.hx24
      hx23      := hx23'.trans hr.hx23
      hx22      := hx22'.trans hr.hx22
      hx21      := hx21'.trans hr.hx21
      hx20      := hx20'.trans hr.hx20 }

attribute [local simp, local arm64_norm, local wp_norm] ofNat_mul136

/-- Step `[0x00a4 → 0x00b8]`: compute `byteOff = k * 136` and call `B09` (`load_block::<136>`). -/
private theorem seg_call_loadBlock [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl01 b) (_hbase : blkPl01.base = b)
    (a : Keccak2ShakeArgs) (hlen : a.in0.length = a.in1.length) (hin0 : a.in0.length < 2 ^ 32)
    (s0 s : State) (rcBase : BitVec 64) (k : Nat) (hk : k < a.in0.length / 136) (F : SepProp)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hpc : s.pc = b + 0x00a4#64)
    (hregs : PostAbsorbRegs s s0 rcBase a)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 k) :
    let sp1 := s0.sp - 1040#64
    let st0 := keccakAbsorbPrefix17 a.in0 k
    let st1 := keccakAbsorbPrefix17 a.in1 k
    SepWP (blkPC01.rebase b (fun _ => none)) (b + 0x00b8#64) s
      (stackAt sp1 16 ∗
        Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
        (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗
        Keccak2Mem (sp1 + 192#64) st0 st1 ∗ F)
      (fun sf Qf =>
        PostAbsorbRegs sf s0 rcBase a ∧
        sf.readReg64 .x26 = BitVec.ofNat 64 k ∧
        (Qf ⊢ stackAt sp1 16 ∗
          Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
          (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗
          Keccak2Mem (sp1 + 192#64)
            (keccakXorRate17 st0 ((a.in0.drop (k * 136)).take 136))
            (keccakXorRate17 st1 ((a.in1.drop (k * 136)).take 136)) ∗ F)) := by
  intro sp1 st0 st1
  rcases hregs with ⟨hrun, hsp_align, hsp, hx29, hx27, hx25, hx24, hx23, hx22, hx21, hx20⟩
  have hb0 : k * 136 + 136 ≤ a.in0.length := by
    have := Nat.div_mul_le_self a.in0.length 136; omega
  have hb1 : k * 136 + 136 ≤ a.in1.length := by omega
  have hl0 : a.in0.length < 2 ^ 64 := by omega
  have hl1 : a.in1.length < 2 ^ 64 := by omega
  have hsp_off : s0.sp - 848#64 = sp1 + 192#64 := by dsimp [sp1]; bv_omega
  unfold Keccak2Mem
  wp_cut_codeLoaded
  wp_steps
  wp_mlkem_call loadBlock136_block_ok
    ({ statePtr := sp1 + 192#64, slicesPtr := a.slicesPtr, ptr0 := a.ptr0, ptr1 := a.ptr1,
       byteOff := k * 136, in0 := a.in0, in1 := a.in1, st0 := st0, st1 := st1 } : LoadBlock136Args)
  refine SepWP.done hpc_sf hrun_sf ⟨?_, ?_, ?_⟩
  · have hsp_sf' : sf.sp = s0.sp - 1040#64 := hsp_sf.trans hsp
    exact
      { hrun      := hrun_sf
        hsp_align := by rw [State.spAligned, hsp_sf', ← hsp, ← State.spAligned]; exact hsp_align
        hsp       := hsp_sf'
        hx29      := (by assumption : sf.readReg64 .fp = s.readReg64 .fp).trans hx29
        hx27      := (by assumption : sf.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5)).trans hx27
        hx25      := (by assumption : sf.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5)).trans hx25
        hx24      := (by assumption : sf.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5)).trans hx24
        hx23      := (by assumption : sf.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5)).trans hx23
        hx22      := (by assumption : sf.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5)).trans hx22
        hx21      := (by assumption : sf.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5)).trans hx21
        hx20      := (by assumption : sf.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5)).trans hx20 }
  · exact (by assumption : sf.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5)).trans hx26
  · rw [← Keccak2Cap8Mem_xorRate17 (sp1 + 192#64) st0 st1
          ((a.in0.drop (k * 136)).take 136) ((a.in1.drop (k * 136)).take 136)
          (keccakAbsorbPrefix17_size a.in0 k) (keccakAbsorbPrefix17_size a.in1 k)]
    sep_frame


/-- Step `[0x00b8 → +0x00a4 / +0x0434]`: load 2-way state, run `Permute1`, store, and branch. -/
private theorem seg_load_permute_store [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl01 b) (hbase : blkPl01.base = b)
    (s : State) (sp1 rcBase : BitVec 64) (k nBlocks : Nat)
    (st0 st1 : KeccakState) (F : SepProp)
    (hk : k < nBlocks) (hn : nBlocks < 2 ^ 64)
    (hpc : s.pc = b + 0x00b8#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp1) (hsp_align : s.spAligned = true)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 nBlocks)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 k)
    (hx27 : s.readReg64 .x27 = rcBase) :
    SepWP (blkPC01.rebase b (fun _ => none))
      (if k + 1 < nBlocks then b + 0x00a4#64 else b + 0x0434#64) s
      (memRegion (sp1 + 16#64) 176 ∗
        Keccak2Mem (sp1 + 192#64) st0 st1 ∗
        (rcBase ↦ᵣ mlkemData01Bytes) ∗ F)
      (fun sf Q =>
        P1Scalars s sf ∧
        sf.readReg64 .x26 = BitVec.ofNat 64 (k + 1) ∧
        (Q ⊢ memRegion (sp1 + 16#64) 176 ∗
          Keccak2Mem (sp1 + 192#64) (keccakF1600 st0) (keccakF1600 st1) ∗
          (rcBase ↦ᵣ mlkemData01Bytes) ∗ F)) := by
  have hload :
      SepWP (blkPC01.rebase b (fun _ => none)) (b + 0x00f8#64) s
        (memRegion (sp1 + 16#64) 176 ∗
          Keccak2Mem (sp1 + 192#64) st0 st1 ∗
          (rcBase ↦ᵣ mlkemData01Bytes) ∗ F)
        (fun s1 P1 =>
          P1Scalars s s1 ∧
          s1.readReg64 .x26 = BitVec.ofNat 64 k ∧
          s1.readReg64 .x8 = 0#64 ∧
          P1RoundRegs s1 st0 st1 ∧
          ∃ s16 s32 s48 s64 s80 s96 s112 s128,
            P1 ⊢ Spill11 sp1 s16 s32 s48 s64 s80 s96 s112 s128
              (keccak2Lane st0 st1 7) (keccak2Lane st0 st1 8) (keccak2Lane st0 st1 14) ∗
              ((rcBase ↦ᵣ mlkemData01Bytes) ∗ (memRegion (sp1 + 192#64) 400 ∗ F))) := by
    refine memRegion176_to_spill11 sp1 (by sep_focus)
      fun s16 s32 s48 s64 s80 s96 s112 s128 _s144 _s160 _s176 => ?_
    unfold Spill11 Keccak2Mem Keccak2Rate17Mem Keccak2Rate16Mem
      Keccak2Q0Mem Keccak2Q1Mem Keccak2Q2Mem Keccak2Q3Mem Keccak2Vec16Mem Keccak2Cap8Mem
    wp_steps 16
    apply SepWP.done
    · wp_norm_lhs
    · wp_norm_lhs
    refine ⟨⟨Eq.trans (by wp_norm_lhs) hsp.symm,
        by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
        by wp_norm_lhs, by wp_norm_lhs, Eq.trans (by wp_norm_lhs) hx25.symm,
        Eq.trans (by wp_norm_lhs) hx27.symm, by wp_norm_lhs⟩,
      by wp_norm_lhs, by wp_norm_lhs, ?_, s16, s32, s48, s64, s80, s96, s112, s128, ?_⟩
    · dsimp only [P1RoundRegs, keccak2Lane]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals wp_norm_lhs
    · refine entails_sub
        (Rest := Spill11 sp1 s16 s32 s48 s64 s80 s96 s112 s128
          (keccak2Lane st0 st1 7) (keccak2Lane st0 st1 8) (keccak2Lane st0 st1 14) ∗
          (rcBase ↦ᵣ mlkemData01Bytes) ∗ F)
        (Keccak2Mem_entails_memRegion (sp1 + 192#64) st0 st1) ?_ (by unfold Spill11; sep_frame)
      unfold Spill11 Keccak2Mem Keccak2Rate17Mem Keccak2Rate16Mem
        Keccak2Q0Mem Keccak2Q1Mem Keccak2Q2Mem Keccak2Q3Mem Keccak2Vec16Mem Keccak2Cap8Mem
      dsimp only [keccak2Lane]
      simp only [extractLsb_lo_append, extractLsb_hi_append]
      sep_entail
  refine SepWP.seq hload
    fun s1 P1 hpc1 hrun1 ⟨hscal1, hx26_1, hx8_1, hrr1,
      s16, s32, s48, s64, s80, s96, s112, s128, hP1⟩ => ?_
  refine SepWP.weaken_pre hP1 <|
    SepWP.seq
      (permute1_rounds hb hbase s1 sp1 rcBase st0 st1
        s16 s32 s48 s64 s80 s96 s112 s128 (memRegion (sp1 + 192#64) 400 ∗ F)
        hpc1 hrun1 (hscal1.1.trans hsp) (hscal1.spAligned hsp_align)
        hx8_1 (hscal1.2.2.2.2.2.2.2.2.1.trans hx27) hrr1)
      fun s2 P2 hpc2 hrun2 ⟨hscal2, hx26_2, hrr2,
        s16', s32', s48', s64', s80', s96', s112', s128', hP2⟩ => ?_
  have hscal12 := hscal1.trans hscal2
  have hsp2 : s2.sp = sp1 := hscal12.1.trans hsp
  have halign2 : s2.spAligned = true := hscal12.spAligned hsp_align
  have hx25_2 : s2.readReg64 .x25 = BitVec.ofNat 64 nBlocks := hscal12.2.2.2.2.2.2.2.1.trans hx25
  have hx26_2' : s2.readReg64 .x26 = BitVec.ofNat 64 k := hx26_2.trans hx26_1
  clear hx26_2
  refine SepWP.weaken_pre hP2 ?_
  set out0 := keccakF1600 st0
  set out1 := keccakF1600 st1
  rcases hrr2 with ⟨hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9, hv11, hv12, hv15,
    hv16, hv17, hv18, hv19, hv22, hv23, hv24, hv27, hv28, hv29, hv30⟩
  dsimp only [keccak2Lane] at hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv11 hv12 hv15
  dsimp only [keccak2Lane] at hv16 hv17 hv18 hv19 hv22 hv23 hv24 hv27 hv28 hv29 hv30
  refine memRegion400_cells (sp1 + 192#64) (by sep_focus)
    fun _c0 _c1 _c2 _c3 _c4 _c5 _c6 _c7 _c8 _c9 _c10 _c11 _c12 _c13 _c14 _c15
        _d0 _d1 _d2 _d3 _d4 _d5 _d6 _d7 _d8 _d9 _d10 _d11 _d12 _d13 _d14 _d15
        _e0 _e1
        _f0 _f1 _f2 _f3 _f4 _f5 _f6 _f7 _f8 _f9 _f10 _f11 _f12 _f13 _f14 _f15 => ?_
  unfold Spill11
  dsimp only [keccak2Lane]
  simp only [extractLsb_lo_append, extractLsb_hi_append]
  wp_steps 18
  apply SepWP.done
  · rw [← bne_k_target_eq hk hn]; wp_norm_lhs
  · wp_norm_lhs
  refine ⟨hscal12.trans ⟨Eq.trans (by wp_norm_lhs) hsp2.symm,
      by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
      by wp_norm_lhs, by wp_norm_lhs, Eq.trans (by wp_norm_lhs) hx25_2.symm,
      by wp_norm_lhs, by wp_norm_lhs⟩,
    Eq.trans (by wp_norm_lhs) (add1_eq_ofNat k), ?_⟩
  refine entails_sub
    (Rest := Keccak2Mem (sp1 + 192#64) out0 out1 ∗ (rcBase ↦ᵣ mlkemData01Bytes) ∗ F)
    (spill11_entails_memRegion176 sp1 s16' s32' s48' s64' s80' s96' s112' s128'
      (keccak2Lane out0 out1 7) (keccak2Lane out0 out1 8) (keccak2Lane out0 out1 14))
    ?_ (by sep_frame)
  unfold Spill11 Keccak2Mem Keccak2Rate17Mem Keccak2Rate16Mem
    Keccak2Q0Mem Keccak2Q1Mem Keccak2Q2Mem Keccak2Q3Mem Keccak2Vec16Mem Keccak2Cap8Mem
  dsimp only [keccak2Lane]
  simp only [extractLsb_lo_append, extractLsb_hi_append]
  sep_entail

attribute [local irreducible] Keccak2Mem Keccak2SlicesRO SavedCalleeFrame

/-- Single iteration of the full-block absorb loop (`[0x00a4 → +0x00a4 / +0x0434]`). -/
private theorem absorb_iter [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl01 b) (hbase : blkPl01.base = b)
    (a : Keccak2ShakeArgs) (hlen : a.in0.length = a.in1.length) (hin0 : a.in0.length < 2 ^ 32)
    (s0 s : State) (F : SepProp) (k : Nat)
    (hk : k < a.in0.length / 136)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hpc : s.pc = b + 0x00a4#64)
    (hregs : PostAbsorbRegs s s0
      (mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29") a)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 k) :
    let rcBase := mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29"
    let nBlocks := a.in0.length / 136
    SepWP (blkPC01.rebase b (fun _ => none))
      (if k + 1 < nBlocks then b + 0x00a4#64 else b + 0x0434#64) s
      (AbsorbInvMem s0 rcBase a k F)
      (fun sm Qm =>
        PostAbsorbRegs sm s0 rcBase a ∧
        sm.readReg64 .x26 = BitVec.ofNat 64 (k + 1) ∧
        (Qm ⊢ AbsorbInvMem s0 rcBase a (k + 1) F)) := by
  intro rcBase nBlocks
  let sp1 := s0.sp - 1040#64
  unfold AbsorbInvMem
  dsimp only
  rw [stack96_split16 (s0.sp - 1040#64)]
  let restCall := memRegion (sp1 - 96#64) 80 ∗ memRegion sp1 8 ∗
    ((sp1 + 8#64) ↦₆₄ BitVec.ofNat 64 a.outLen) ∗ memRegion (sp1 + 16#64) 176 ∗
    memRegion (sp1 + 592#64) 288 ∗ SavedCalleeFrame s0.sp s0 ∗ (rcBase ↦ᵣ mlkemData01Bytes) ∗ F
  refine SepWP.weaken_pre
    (show _ ⊢ stackAt sp1 16 ∗
      Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
      (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗
      Keccak2Mem (sp1 + 192#64) (keccakAbsorbPrefix17 a.in0 k) (keccakAbsorbPrefix17 a.in1 k) ∗
      restCall by dsimp only [sp1, restCall]; sep_frame) ?_
  refine sepWP_seq_cl hcl
    (seg_call_loadBlock hb hbase a hlen hin0 s0 s rcBase k hk restCall hcl hpc hregs hx26)
    fun s1 Q1 hpc1 _hrun1 _hcl1 ⟨hregs1, hx26_1, hQ1⟩ => ?_
  refine SepWP.weaken_pre hQ1 ?_
  let restPerm := memRegion (sp1 - 96#64) 80 ∗ stackAt sp1 16 ∗ memRegion sp1 8 ∗
    ((sp1 + 8#64) ↦₆₄ BitVec.ofNat 64 a.outLen) ∗ memRegion (sp1 + 592#64) 288 ∗
    SavedCalleeFrame s0.sp s0 ∗
    Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
    (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗ F
  refine SepWP.weaken_pre
    (show _ ⊢ memRegion (sp1 + 16#64) 176 ∗
      Keccak2Mem (sp1 + 192#64)
        (keccakXorRate17 (keccakAbsorbPrefix17 a.in0 k) ((a.in0.drop (k * 136)).take 136))
        (keccakXorRate17 (keccakAbsorbPrefix17 a.in1 k) ((a.in1.drop (k * 136)).take 136)) ∗
      (rcBase ↦ᵣ mlkemData01Bytes) ∗ restPerm by dsimp only [restCall, restPerm]; sep_frame) ?_
  refine SepWP.mono
    (seg_load_permute_store hb hbase s1 sp1 rcBase k nBlocks
      (keccakXorRate17 (keccakAbsorbPrefix17 a.in0 k) ((a.in0.drop (k * 136)).take 136))
      (keccakXorRate17 (keccakAbsorbPrefix17 a.in1 k) ((a.in1.drop (k * 136)).take 136))
      restPerm hk (by omega) hpc1 hregs1.hrun hregs1.hsp hregs1.hsp_align
      hregs1.hx25 hx26_1 hregs1.hx27)
    fun sm Qm _ hrunm ⟨hscal, hx26_m, hQm⟩ =>
      ⟨postAbsorbRegs_of_p1Scalars hregs1 hscal hrunm, hx26_m, ?_⟩
  dsimp only [keccakAbsorbPrefix17]
  exact Entails.trans hQm (by dsimp only [sp1, restPerm]; sep_frame)

/-- Absorb `rem > 0` remaining full 136-byte blocks (`k + rem = a.in0.length / 136`), reaching `+0x0434`. -/
private theorem absorb_loop [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl01 b) (hbase : blkPl01.base = b)
    (a : Keccak2ShakeArgs) (hlen : a.in0.length = a.in1.length) (hin0 : a.in0.length < 2 ^ 32)
    (s0 : State) (F : SepProp) :
    let rcBase := mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29"
    ∀ (rem k : Nat), 0 < rem → k + rem = a.in0.length / 136 →
      ∀ (s : State),
        mlkemMultiLib.CodeLoaded mlkemMpl s.mem →
        s.pc = b + 0x00a4#64 →
        PostAbsorbRegs s s0 rcBase a →
        s.readReg64 .x26 = BitVec.ofNat 64 k →
        SepWP (blkPC01.rebase b (fun _ => none)) (b + 0x0434#64) s
          (AbsorbInvMem s0 rcBase a k F)
          (fun sf Qf =>
            PostAbsorbRegs sf s0 rcBase a ∧
            (Qf ⊢ AbsorbInvMem s0 rcBase a (a.in0.length / 136) F)) := by
  intro rcBase rem
  induction rem with
  | zero => intro _ hpos; exact absurd hpos (Nat.lt_irrefl 0)
  | succ r ih =>
    intro k _ hsum s hcl hpc hregs hx26
    have hk : k < a.in0.length / 136 := by omega
    refine sepWP_seq_cl hcl (absorb_iter hb hbase a hlen hin0 s0 s F k hk hcl hpc hregs hx26)
      fun s1 Q1 hpc1 hrun1 hcl1 ⟨hregs1, hx26_1, hQ1⟩ => ?_
    refine SepWP.weaken_pre hQ1 ?_
    by_cases hr : r = 0
    · subst hr
      have hend : k + 1 = a.in0.length / 136 := by omega
      have hnlt : ¬(k + 1 < a.in0.length / 136) := by omega
      simp only [hnlt, ↓reduceIte] at hpc1
      rw [hend]
      exact SepWP.done hpc1 hrun1 ⟨hregs1, Entails.refl _⟩
    · have hlt : k + 1 < a.in0.length / 136 := by omega
      simp only [hlt, ↓reduceIte] at hpc1
      exact ih (k + 1) (Nat.pos_of_ne_zero hr) (by omega) s1 hcl1 hpc1 hregs1 hx26_1

public section

/-- Prologue + full-block absorb loop `[0x0000 → 0x0434]`. -/
theorem absorb_prefix_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl01 b) (hbase : blkPl01.base = b)
    (a : Keccak2ShakeArgs) (hlen : a.in0.length = a.in1.length) (hin0 : a.in0.length < 2 ^ 32)
    (s0 : State) (F : SepProp)
    (hcl0 : mlkemMultiLib.CodeLoaded mlkemMpl s0.mem)
    (hpc : s0.pc = b) (hrun : s0.status = .Running) (hsp0 : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = a.slicesPtr)
    (hx1 : s0.readReg64 .x1 = a.out0)
    (hx2 : s0.readReg64 .x2 = BitVec.ofNat 64 a.outLen)
    (hx3 : s0.readReg64 .x3 = a.out1)
    (hx4 : s0.readReg64 .x4 = BitVec.ofNat 64 a.outLen) :
    let rcBase := mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29"
    SepWP (blkPC01.rebase b (fun _ => none)) (b + 0x0434#64) s0
      (Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
        (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗
        stackAt s0.sp 1136 ∗
        (rcBase ↦ᵣ mlkemData01Bytes) ∗ F)
      (fun sm Qm =>
        PostAbsorbRegs sm s0 rcBase a ∧
        (Qm ⊢ AbsorbInvMem s0 rcBase a (a.in0.length / 136) F)) := by
  intro rcBase
  refine sepWP_seq_cl hcl0
    (prologue_ok hb hbase a hin0 s0 F hcl0 hpc hrun hsp0 hx0 hx1 hx2 hx3 hx4)
    fun s1 Q1 hpc1 hrun1 hcl1 ⟨hregs1, hx26_1, hQ1⟩ => ?_
  refine SepWP.weaken_pre hQ1 ?_
  by_cases hlt : a.in0.length < 136
  · simp only [hlt, ↓reduceIte] at hpc1
    rw [Nat.div_eq_of_lt hlt]
    exact SepWP.done hpc1 hrun1 ⟨hregs1, Entails.refl _⟩
  · simp only [hlt, ↓reduceIte] at hpc1
    have hpos : 0 < a.in0.length / 136 := Nat.div_pos (by omega) (by decide)
    exact absorb_loop hb hbase a hlen hin0 s0 F (a.in0.length / 136) 0
      hpos (Nat.zero_add _) s1 hcl1 hpc1 hregs1 (hx26_1 hlt)

end

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31.AbsorbLoop
