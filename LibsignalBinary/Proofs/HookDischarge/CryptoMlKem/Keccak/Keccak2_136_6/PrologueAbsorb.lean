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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Defs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.Base
import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.LoadSqueeze.LoadBlock
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.RoundBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.AbsorbPermute
meta import ProofLib
meta import ProofLib.ProgramReflection
meta import ProofLib.GenDecodes
meta import ProofLib.GenPlacedFetches

/-!
# `B02` (`keccak2::<136, 6>`): prologue and full-block absorb loop

Proof of the prologue and full-block absorb loop of `mlkemBlk02`:
- `[0x0000 → 0x0098]`: `1024`-byte local frame allocation (`1040`-byte total stack footprint
  including `16` bytes for `B09`), callee-saved spill (`SavedFrame02`), 50-cell state zeroing
  (`Keccak2Mem (sp + 176#64) keccakZeroState keccakZeroState`), hardware `umulh` + `lsr #7`
  division `x23 = inLen / 136`, and `b.lo +0x042c` (`inLen < 136`).
- `[0x009c → 0x0428]`: `nBlocks = inLen / 136` outer loop calling `B09`
  (`loadBlock136_block_ok`) at `+0x00ac` followed by `AbsorbPermute.seg_absorb_permute`
  (`+0x00b0 → +0x0428`), reaching `+0x042c` with `keccakAbsorbPrefix17`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.PrologueAbsorb

open Arm64 ProofLib ProofLib.GenPlacedFetches SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (
  mlkemData01Bytes
  mlkemMultiLib
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (
  Keccak2FixedArgs
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
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk mlkemData01Bytes_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables.SepWP (roDataAt_intro)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  KeccakState
  keccakF1600
  keccakZeroState
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Defs (
  Keccak2Cap8Mem
  Keccak2Cap8Mem_xorRate17
  Keccak2Mem
  Keccak2Q0Mem
  Keccak2Q1Mem
  Keccak2Q2Mem
  Keccak2Q3Mem
  Keccak2Rate16Mem
  Keccak2Rate17Mem
  Keccak2Vec16Mem
  keccakXorRate17
  keccakZeroState_getD
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge (
  keccakAbsorbPrefix17
  keccakAbsorbPrefix17_size
  memRegion128_cells
  memRegion32_cells
  umulh_div136_nat
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.LoadSqueeze.LoadBlock (
  LoadBlock136Args
  loadBlock136_block_ok
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.Base (
  SavedFrame02
  blk02_code_eq
  blk02_tree_size
  blkLib02
  blkPC02
  blkPl02
  blkPlaceable02
  blkTree02
  sepWP_seq_env
  stack1040_split
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.RoundBase (
  AbsorbRegsPreserved
  spAligned_of_sp_eq
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.AbsorbPermute (
  seg_absorb_permute
)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp

section
set_option linter.literalFetch false
gen_placed_fetches blkPC02 blkLib02 blkTree02 blk02_code_eq blk02_tree_size
  via_placement blkPl02 blkPlaceable02 [0x0000 → 0x00ac]
end

@[local simp, local arm64_norm, local wp_norm]
private theorem blkPl02_ρ [MlKemPlacement] (sym : String) :
    blkPl02.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

attribute [local irreducible] mlkemData01Bytes

public section

/-- Scalar register invariant at `+0x042c` (and throughout the `+0x009c` absorb loop). -/
structure TailEntryRegs (s : State) (sp rcBase : BitVec 64) (a : Keccak2FixedArgs) : Prop where
  hrun      : s.status = .Running
  hsp_align : s.spAligned = true
  hsp       : s.sp = sp
  hfp       : s.readReg64 .fp = sp + 928#64
  hx25      : s.readReg64 .x25 = rcBase
  hx23      : s.readReg64 .x23 = BitVec.ofNat 64 (a.in0.length / 136)
  hx22      : s.readReg64 .x22 = BitVec.ofNat 64 a.in0.length
  hx21      : s.readReg64 .x21 = a.slicesPtr
  hx20      : s.readReg64 .x20 = a.out0
  hx19      : s.readReg64 .x19 = a.out1

end

private theorem sepWP_drop_left {prog : Program} {target_pc : BitVec 64}
    {s : State} {Drop P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP prog target_pc s P post oom) :
    SepWP prog target_pc s (Drop ∗ P) post oom :=
  SepWP.weaken_pre_frame
    (fun _ hm => Satisfies.of_sep_right (by simpa only [sepConj_assoc] using hm)) h

private theorem truncate64_eq_extractLsb0 (v : BitVec 128) :
    v.truncate 64 = v.extractLsb' 0 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi]

private theorem savedFrame02_of_truncate (sp0 : BitVec 64) (s0 : State) :
    (((sp0 - 160#64) ↦₆₄ (s0.readVReg128 15#5).truncate 64) ∗
     ((sp0 - 152#64) ↦₆₄ (s0.readVReg128 14#5).truncate 64) ∗
     ((sp0 - 144#64) ↦₆₄ (s0.readVReg128 13#5).truncate 64) ∗
     ((sp0 - 136#64) ↦₆₄ (s0.readVReg128 12#5).truncate 64) ∗
     ((sp0 - 128#64) ↦₆₄ (s0.readVReg128 11#5).truncate 64) ∗
     ((sp0 - 120#64) ↦₆₄ (s0.readVReg128 10#5).truncate 64) ∗
     ((sp0 - 112#64) ↦₆₄ (s0.readVReg128 9#5).truncate 64) ∗
     ((sp0 - 104#64) ↦₆₄ (s0.readVReg128 8#5).truncate 64)) ∗
    (((sp0 - 96#64) ↦₆₄ s0.readReg64 .fp) ∗
     ((sp0 - 88#64) ↦₆₄ s0.readReg64 .lr) ∗
     ((sp0 - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
     ((sp0 - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
     ((sp0 - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
     ((sp0 - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
     ((sp0 - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
     ((sp0 - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
     ((sp0 - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
     ((sp0 - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
     ((sp0 - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
     ((sp0 - 8#64) ↦₆₄ s0.readReg64 .x19)) = SavedFrame02 sp0 s0 := by
  unfold SavedFrame02
  simp only [truncate64_eq_extractLsb0]

private theorem ult_136_iff {n : Nat} (hn : n < 2 ^ 32) :
    (BitVec.ofNat 64 n).ult 136#64 = true ↔ n < 136 := by
  have hmod : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp [BitVec.ult, hmod]

private theorem umulh_div136_eval {n : Nat} (hn : n < 2 ^ 32) :
    BitVec.truncate 64
      ((BitVec.zeroExtend 128 (BitVec.ofNat 64 n) * 17361641481138401521#128) >>> 64) >>> 7 =
      BitVec.ofNat 64 (n / 136) := by
  apply BitVec.eq_of_toNat_eq
  have hn64 : n < 2 ^ 64 := Nat.lt_trans hn (by decide)
  have hn128 : n < 2 ^ 128 := Nat.lt_trans hn (by decide)
  have h128 : (BitVec.zeroExtend 128 (BitVec.ofNat 64 n)).toNat = n := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64, Nat.mod_eq_of_lt hn128]
  have hc : (17361641481138401521#128).toNat = 0xf0f0f0f0f0f0f0f1 := rfl
  have hmul : n * 0xf0f0f0f0f0f0f0f1 < 2 ^ 128 :=
    Nat.lt_trans (Nat.mul_lt_mul_of_pos_right hn (by decide)) (by decide)
  have hdiv : n * 0xf0f0f0f0f0f0f0f1 / 2 ^ 64 < 2 ^ 64 :=
    Nat.lt_of_le_of_lt
      (Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.le_of_lt hn)))
      (by decide)
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
      BitVec.toNat_mul, h128, hc, Nat.mod_eq_of_lt hmul,
      Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt hdiv, umulh_div136_nat hn,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

private theorem mul136_shift_bv (x : BitVec 64) :
    (x + (x <<< 4)) <<< 3 = x * 136#64 := by
  bv_bits

@[local simp, local arm64_norm, local wp_norm]
private theorem mul136_ofNat (k : Nat) :
    (BitVec.ofNat 64 k + (BitVec.ofNat 64 k <<< 4)) <<< 3 = BitVec.ofNat 64 (k * 136) := by
  rw [mul136_shift_bv, show (136#64 : BitVec 64) = BitVec.ofNat 64 136 from rfl, ← BitVec.ofNat_mul]

private theorem tailEntryRegs_of_absorbPreserved {s1 s2 : State} {sp rcBase : BitVec 64}
    {a : Keccak2FixedArgs} (h1 : TailEntryRegs s1 sp rcBase a)
    (hpres : AbsorbRegsPreserved s1 s2) (hrun2 : s2.status = .Running)
    (halign2 : s2.spAligned = true) :
    TailEntryRegs s2 sp rcBase a :=
  { hrun      := hrun2
    hsp_align := halign2
    hsp       := hpres.1.trans h1.hsp
    hfp       := hpres.2.2.2.2.2.2.2.trans h1.hfp
    hx25      := hpres.2.2.2.2.2.2.1.trans h1.hx25
    hx23      := hpres.2.2.2.2.2.1.trans h1.hx23
    hx22      := hpres.2.2.2.2.1.trans h1.hx22
    hx21      := hpres.2.2.2.1.trans h1.hx21
    hx20      := hpres.2.2.1.trans h1.hx20
    hx19      := hpres.2.1.trans h1.hx19 }

private theorem split400_eq (sp : BitVec 64) :
    memRegion (sp + 176#64) 400 =
      memRegion (sp + 176#64) 128 ∗
      memRegion (sp + 304#64) 128 ∗
      memRegion (sp + 432#64) 8 ∗
      memRegion (sp + 440#64) 8 ∗
      memRegion (sp + 448#64) 128 := by
  rw [memRegion_split' (b' := sp + 448#64) (n := 272) (k := 128) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp + 432#64) (n := 256) (k := 16) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp + 304#64) (n := 128) (k := 128) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 432#64) (b' := sp + 440#64) (n := 8) (k := 8) rfl (by bv_omega) (by decide)]
  simp only [sepConj_assoc]

private theorem split160_saved_eq (sp0 : BitVec 64) :
    memRegion (sp0 - 160#64) 160 =
      memRegion (sp0 - 160#64) 128 ∗ memRegion (sp0 - 32#64) 32 :=
  memRegion_split' (b' := sp0 - 32#64) (n := 128) (k := 32) rfl (by bv_omega) (by decide)

/-- Step `[0x0000 → 0x0030]`: allocate `1024`-byte local frame and spill `SavedFrame02`. -/
private theorem seg_prologue_spill [MlKemPlacement] (b : BitVec 64)
    (_hb : MlKemBase blkPl02 b) (_hbase : blkPl02.base = b)
    (F : SepProp) (s0 : State)
    (hpc : s0.pc = b) (hrun : s0.status = .Running) (hsp0 : s0.spAligned = true) :
    let sp := s0.sp - 1024#64
    SepWP (blkPC02.rebase b (fun _ => none)) (b + 0x0030#64) s0
      (memRegion (s0.sp - 160#64) 160 ∗ F)
      (fun s1 P1 =>
        (s1.status = .Running ∧
          s1.spAligned = true ∧
          s1.sp = sp ∧
          s1.readReg64 .fp = sp + 928#64 ∧
          s1.readReg64 .x0 = s0.readReg64 .x0 ∧
          s1.readReg64 .x1 = s0.readReg64 .x1 ∧
          s1.readReg64 .x2 = s0.readReg64 .x2) ∧
        (P1 ⊢ SavedFrame02 s0.sp s0 ∗ F)) := by
  intro sp
  have hsp160 : ((s0.sp - 160#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 160#64 hsp0 (by decide)
  have hsp1024 : (((s0.sp - 160#64) - 864#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub (s0.sp - 160#64) 864#64 hsp160 (by decide)
  rw [split160_saved_eq s0.sp]
  refine memRegion128_cells (s0.sp - 160#64) (by sep_focus)
    fun _c0 _c1 _c2 _c3 _c4 _c5 _c6 _c7 _c8 _c9 _c10 _c11 _c12 _c13 _c14 _c15 => ?_
  refine memRegion32_cells (s0.sp - 32#64) (by sep_focus) fun _c16 _c17 _c18 _c19 => ?_
  have hs17 : (s0.sp - 32#64) + 8#64  = s0.sp - 24#64 := by clear * -; bv_omega
  have hs18 : (s0.sp - 32#64) + 16#64 = s0.sp - 16#64 := by clear * -; bv_omega
  have hs19 : (s0.sp - 32#64) + 24#64 = s0.sp - 8#64  := by clear * -; bv_omega
  rw [hs17, hs18, hs19]
  clear hs17 hs18 hs19
  wp_steps
  apply SepWP.done
  · wp_norm_lhs
  · wp_norm_lhs
  · refine ⟨⟨by wp_norm_lhs, by rw [State.spAligned]; simpa using hsp1024,
        by refine Eq.trans (by wp_norm_lhs) (by dsimp [sp]),
        by refine Eq.trans (by wp_norm_lhs) (by dsimp [sp]; clear * -; bv_omega),
        by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs⟩, ?_⟩
    rw [← savedFrame02_of_truncate s0.sp s0]
    sep_frame

/-- Step `[0x0030 → if in0.length < 136 then +0x042c else +0x009c]`: zero `Keccak2Mem (sp + 176#64)`
    and compute `nBlocks = in0.length / 136`. -/
private theorem seg_prologue_zero [MlKemPlacement] (b : BitVec 64)
    (_hb : MlKemBase blkPl02 b) (_hbase : blkPl02.base = b)
    (a : Keccak2FixedArgs) (hin0 : a.in0.length < 2 ^ 32)
    (sp : BitVec 64) (F : SepProp) (s1 : State)
    (hpc : s1.pc = b + 0x0030#64) (hrun : s1.status = .Running) (hsp_align : s1.spAligned = true)
    (hsp : s1.sp = sp) (hfp : s1.readReg64 .fp = sp + 928#64)
    (hx0 : s1.readReg64 .x0 = a.slicesPtr)
    (hx1 : s1.readReg64 .x1 = a.out0)
    (hx2 : s1.readReg64 .x2 = a.out1) :
    let rcBase := mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29"
    SepWP (blkPC02.rebase b (fun _ => none))
      (if a.in0.length < 136 then b + 0x042c#64 else b + 0x009c#64) s1
      (Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
        memRegion (sp + 176#64) 400 ∗ F)
      (fun sm Pm =>
        (TailEntryRegs sm sp rcBase a ∧
          (¬(a.in0.length < 136) → sm.readReg64 .x24 = 0#64)) ∧
        (Pm ⊢ Keccak2Mem (sp + 176#64) keccakZeroState keccakZeroState ∗
          Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗ F)) := by
  intro rcBase
  rw [split400_eq sp]
  refine memRegion128_cells (sp + 176#64) (by sep_focus)
    fun _k0 _k1 _k2 _k3 _k4 _k5 _k6 _k7 _k8 _k9 _k10 _k11 _k12 _k13 _k14 _k15 => ?_
  refine memRegion128_cells (sp + 304#64) (by sep_focus)
    fun _m0 _m1 _m2 _m3 _m4 _m5 _m6 _m7 _m8 _m9 _m10 _m11 _m12 _m13 _m14 _m15 => ?_
  refine SepWP.memRegion8_cell (sp + 432#64) fun _e0 => ?_
  refine SepWP.memRegion8_cell (sp + 440#64) fun _e1 => ?_
  refine memRegion128_cells (sp + 448#64) (by sep_focus)
    fun _n0 _n1 _n2 _n3 _n4 _n5 _n6 _n7 _n8 _n9 _n10 _n11 _n12 _n13 _n14 _n15 => ?_
  unfold Keccak2SlicesRO
  wp_steps
  wp_if hbr
  · have hlt : a.in0.length < 136 := (ult_136_iff hin0).mp hbr
    simp only [hlt, ↓reduceIte]
    apply SepWP.done
    · wp_norm_lhs
    · wp_norm_lhs
    · refine ⟨⟨?_, fun hnlt => False.elim (hnlt trivial)⟩, ?_⟩
      · exact
          { hrun      := by wp_norm_lhs
            hsp_align := hsp_align
            hsp       := hsp
            hfp       := hfp
            hx25      := by wp_norm_lhs
            hx23      := by refine Eq.trans (by wp_norm_lhs) (umulh_div136_eval hin0)
            hx22      := by wp_norm_lhs
            hx21      := by wp_norm_lhs
            hx20      := by wp_norm_lhs
            hx19      := by wp_norm_lhs }
      · unfold Keccak2Mem Keccak2Rate17Mem Keccak2Rate16Mem
          Keccak2Q0Mem Keccak2Q1Mem Keccak2Q2Mem Keccak2Q3Mem Keccak2Vec16Mem Keccak2Cap8Mem
        simp only [keccakZeroState_getD]
        sep_entail
  · have hnlt : ¬(a.in0.length < 136) := fun hlt => hbr ((ult_136_iff hin0).mpr hlt)
    simp only [hnlt, ↓reduceIte]
    wp_steps
    apply SepWP.done
    · wp_norm_lhs
    · wp_norm_lhs
    · refine ⟨⟨?_, fun _ => by wp_norm_lhs⟩, ?_⟩
      · exact
          { hrun      := by wp_norm_lhs
            hsp_align := hsp_align
            hsp       := hsp
            hfp       := hfp
            hx25      := by wp_norm_lhs
            hx23      := by refine Eq.trans (by wp_norm_lhs) (umulh_div136_eval hin0)
            hx22      := by wp_norm_lhs
            hx21      := by wp_norm_lhs
            hx20      := by wp_norm_lhs
            hx19      := by wp_norm_lhs }
      · unfold Keccak2Mem Keccak2Rate17Mem Keccak2Rate16Mem
          Keccak2Q0Mem Keccak2Q1Mem Keccak2Q2Mem Keccak2Q3Mem Keccak2Vec16Mem Keccak2Cap8Mem
        simp only [keccakZeroState_getD]
        sep_entail

/-- Step `[0x0000 → if in0.length < 136 then +0x042c else +0x009c]`. -/
private theorem seg_prologue [MlKemPlacement] (b : BitVec 64)
    (hb : MlKemBase blkPl02 b) (hbase : blkPl02.base = b)
    (a : Keccak2FixedArgs) (hin0 : a.in0.length < 2 ^ 32)
    (F : SepProp) (s0 : State)
    (hpc : s0.pc = b) (hrun : s0.status = .Running) (hsp0 : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = a.slicesPtr)
    (hx1 : s0.readReg64 .x1 = a.out0)
    (hx2 : s0.readReg64 .x2 = a.out1) :
    let sp := s0.sp - 1024#64
    let rcBase := mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29"
    SepWP (blkPC02.rebase b (fun _ => none))
      (if a.in0.length < 136 then b + 0x042c#64 else b + 0x009c#64) s0
      (Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
        stackAt s0.sp 1040 ∗ F)
      (fun sm Pm =>
        (TailEntryRegs sm sp rcBase a ∧
          (¬(a.in0.length < 136) → sm.readReg64 .x24 = 0#64)) ∧
        (Pm ⊢ stackAt sp 16 ∗
          memRegion sp 176 ∗
          Keccak2Mem (sp + 176#64) keccakZeroState keccakZeroState ∗
          memRegion (sp + 576#64) 288 ∗
          SavedFrame02 s0.sp s0 ∗
          Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗ F)) := by
  intro sp rcBase
  rw [stack1040_split s0.sp]
  have hpre :
      Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
        (stackAt sp 16 ∗ memRegion sp 176 ∗ memRegion (sp + 176#64) 400 ∗
          memRegion (sp + 576#64) 288 ∗ memRegion (s0.sp - 160#64) 160) ∗ F ⊢
      memRegion (s0.sp - 160#64) 160 ∗
        (Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
          memRegion (sp + 176#64) 400 ∗
          stackAt sp 16 ∗ memRegion sp 176 ∗ memRegion (sp + 576#64) 288 ∗ F) := by
    sep_frame
  refine SepWP.weaken_pre hpre ?_
  refine SepWP.seq
    (seg_prologue_spill b hb hbase _ s0 hpc hrun hsp0)
    fun s1 P1 hpc1 hrun1 ⟨⟨_, halign1, hsp1, hfp1, hx0_1, hx1_1, hx2_1⟩, hP1⟩ => ?_
  have hmid :
      SavedFrame02 s0.sp s0 ∗
        (Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
          memRegion (sp + 176#64) 400 ∗
          stackAt sp 16 ∗ memRegion sp 176 ∗ memRegion (sp + 576#64) 288 ∗ F) ⊢
      Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
        memRegion (sp + 176#64) 400 ∗
        (stackAt sp 16 ∗ memRegion sp 176 ∗ memRegion (sp + 576#64) 288 ∗
          SavedFrame02 s0.sp s0 ∗ F) := by
    sep_frame
  refine SepWP.weaken_pre (Entails.trans hP1 hmid) ?_
  refine SepWP.seq
    (seg_prologue_zero b hb hbase a hin0 sp _ s1 hpc1 hrun1 halign1 hsp1 hfp1
      (hx0_1.trans hx0) (hx1_1.trans hx1) (hx2_1.trans hx2))
    fun sm Pm hpcm hrunm ⟨hpure, hPm⟩ => ?_
  refine SepWP.done hpcm hrunm ⟨hpure, Entails.trans hPm ?_⟩
  sep_frame


attribute [local irreducible] Keccak2Rate17Mem Keccak2Cap8Mem Keccak2SlicesRO SavedFrame02

/-- Step `[0x009c → 0x00b0]` (`add/add/mov/lsl` + `BL B09` `load_block::<136>`). -/
private theorem seg_call_loadBlock [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl02 b) (_hbase : blkPl02.base = b)
    (a : Keccak2FixedArgs) (hin0 : a.in0.length < 2 ^ 32) (hlen_eq : a.in0.length = a.in1.length)
    (sp rcBase : BitVec 64) (k : Nat) (hk : k < a.in0.length / 136)
    (F : SepProp) (s : State)
    (hpc : s.pc = b + 0x009c#64)
    (hregs : TailEntryRegs s sp rcBase a)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 k)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC02.rebase b (fun _ => none)) (b + 0x00b0#64) s
      (stackAt sp 16 ∗
        Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
        (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗
        Keccak2Mem (sp + 176#64) (keccakAbsorbPrefix17 a.in0 k) (keccakAbsorbPrefix17 a.in1 k) ∗
        F)
      (fun s1 P1 =>
        TailEntryRegs s1 sp rcBase a ∧
        s1.readReg64 .x24 = BitVec.ofNat 64 k ∧
        (P1 ⊢ stackAt sp 16 ∗
          Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
          (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗
          Keccak2Mem (sp + 176#64)
            (keccakXorRate17 (keccakAbsorbPrefix17 a.in0 k) ((a.in0.drop (k * 136)).take 136))
            (keccakXorRate17 (keccakAbsorbPrefix17 a.in1 k) ((a.in1.drop (k * 136)).take 136)) ∗
          F)) := by
  rcases hregs with ⟨hrun, hsp_align, hsp, hfp, hx25, hx23, hx22, hx21, hx20, hx19⟩
  subst hsp
  have hk0 : k * 136 + 136 ≤ a.in0.length := by
    have hdiv := Nat.div_add_mod a.in0.length 136
    omega
  have hk1 : k * 136 + 136 ≤ a.in1.length := hlen_eq ▸ hk0
  have h64_0 : a.in0.length < 2 ^ 64 := by omega
  have h64_1 : a.in1.length < 2 ^ 64 := by omega
  have hx21_gpr : s.readReg64 (.gpr 21#5) = a.slicesPtr := hx21
  have hx24_gpr : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 k := hx24
  unfold Keccak2Mem
  wp_cut_codeLoaded
  wp_steps
  wp_mlkem_call loadBlock136_block_ok
    ({ statePtr := s.sp + 176#64
       slicesPtr := a.slicesPtr
       ptr0 := a.ptr0
       ptr1 := a.ptr1
       byteOff := k * 136
       in0 := a.in0
       in1 := a.in1
       st0 := keccakAbsorbPrefix17 a.in0 k
       st1 := keccakAbsorbPrefix17 a.in1 k } : LoadBlock136Args)
  refine SepWP.done hpc_sf hrun_sf ⟨?_, ?_, ?_⟩
  · exact
      { hrun      := hrun_sf
        hsp_align := spAligned_of_sp_eq hsp_sf hsp_align
        hsp       := hsp_sf
        hfp       := (by assumption : sf.readReg64 .fp = s.readReg64 .fp).trans hfp
        hx25      := (by assumption : sf.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5)).trans hx25
        hx23      := (by assumption : sf.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5)).trans hx23
        hx22      := (by assumption : sf.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5)).trans hx22
        hx21      := (by assumption : sf.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5)).trans hx21
        hx20      := (by assumption : sf.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5)).trans hx20
        hx19      := (by assumption : sf.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5)).trans hx19 }
  · exact (by assumption : sf.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5)).trans hx24
  · rw [← Keccak2Cap8Mem_xorRate17 (s.sp + 176#64)
      (keccakAbsorbPrefix17 a.in0 k) (keccakAbsorbPrefix17 a.in1 k)
      ((a.in0.drop (k * 136)).take 136) ((a.in1.drop (k * 136)).take 136)
      (keccakAbsorbPrefix17_size a.in0 k) (keccakAbsorbPrefix17_size a.in1 k)]
    sep_frame

attribute [local irreducible] Keccak2Mem

/-- One full iteration of the `+0x009c → +0x0428` absorb loop (`k < nBlocks`). -/
private theorem absorb_iter [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl02 b) (hbase : blkPl02.base = b)
    (a : Keccak2FixedArgs) (hin0 : a.in0.length < 2 ^ 32) (hlen_eq : a.in0.length = a.in1.length)
    (sp rcBase : BitVec 64)
    (hrc : rcBase = mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29")
    (k : Nat) (hk : k < a.in0.length / 136)
    (F : SepProp) (s : State)
    (hpc : s.pc = b + 0x009c#64)
    (hregs : TailEntryRegs s sp rcBase a)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 k)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hro : MlKemRoOk mlkemMpl s.mem) :
    SepWP (blkPC02.rebase b (fun _ => none))
      (if k + 1 < a.in0.length / 136 then b + 0x009c#64 else b + 0x042c#64) s
      (stackAt sp 16 ∗
        memRegion sp 176 ∗
        Keccak2Mem (sp + 176#64) (keccakAbsorbPrefix17 a.in0 k) (keccakAbsorbPrefix17 a.in1 k) ∗
        Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
        (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗
        F)
      (fun sf Pf =>
        TailEntryRegs sf sp rcBase a ∧
        sf.readReg64 .x24 = BitVec.ofNat 64 (k + 1) ∧
        (Pf ⊢ stackAt sp 16 ∗
          memRegion sp 176 ∗
          Keccak2Mem (sp + 176#64)
            (keccakAbsorbPrefix17 a.in0 (k + 1)) (keccakAbsorbPrefix17 a.in1 (k + 1)) ∗
          Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
          (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗
          F)) := by
  have hpre :
      stackAt sp 16 ∗
        memRegion sp 176 ∗
        Keccak2Mem (sp + 176#64) (keccakAbsorbPrefix17 a.in0 k) (keccakAbsorbPrefix17 a.in1 k) ∗
        Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
        (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗ F ⊢
      stackAt sp 16 ∗
        Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
        (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗
        Keccak2Mem (sp + 176#64) (keccakAbsorbPrefix17 a.in0 k) (keccakAbsorbPrefix17 a.in1 k) ∗
        (memRegion sp 176 ∗ F) := by
    sep_entail
  refine SepWP.weaken_pre hpre ?_
  refine sepWP_seq_env hcl hro
    (seg_call_loadBlock hb hbase a hin0 hlen_eq sp rcBase k hk (memRegion sp 176 ∗ F) s
      hpc hregs hx24 hcl) ?_
  intro s1 P1 hpc1 hrun1 _ hro1 ⟨hregs1, hx24_1, hP1⟩
  refine SepWP.weaken_pre hP1 ?_
  subst hrc
  refine roDataAt_intro hro1.keccakRc (by rw [mlkemData01Bytes_length]; decide) ?_
  have hperm_pre :
      (mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29" ↦ᵣ
          mlkemData01Bytes) ∗
        (stackAt sp 16 ∗
          Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
          (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗
          Keccak2Mem (sp + 176#64)
            (keccakXorRate17 (keccakAbsorbPrefix17 a.in0 k) ((a.in0.drop (k * 136)).take 136))
            (keccakXorRate17 (keccakAbsorbPrefix17 a.in1 k) ((a.in1.drop (k * 136)).take 136)) ∗
          (memRegion sp 176 ∗ F)) ⊢
      (mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29" ↦ᵣ
          mlkemData01Bytes) ∗
        memRegion sp 176 ∗
        Keccak2Mem (sp + 176#64)
          (keccakXorRate17 (keccakAbsorbPrefix17 a.in0 k) ((a.in0.drop (k * 136)).take 136))
          (keccakXorRate17 (keccakAbsorbPrefix17 a.in1 k) ((a.in1.drop (k * 136)).take 136)) ∗
        (stackAt sp 16 ∗
          Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
          (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗ F) := by
    sep_entail
  refine SepWP.weaken_pre hperm_pre ?_
  have hnBlocks_lt : a.in0.length / 136 < 2 ^ 64 := by omega
  refine SepWP.seq
    (seg_absorb_permute hb hbase s1 sp _ k (a.in0.length / 136)
      (keccakXorRate17 (keccakAbsorbPrefix17 a.in0 k) ((a.in0.drop (k * 136)).take 136))
      (keccakXorRate17 (keccakAbsorbPrefix17 a.in1 k) ((a.in1.drop (k * 136)).take 136))
      (stackAt sp 16 ∗
        Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
        (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗ F)
      hk hnBlocks_lt hpc1 hrun1 hregs1.hsp hregs1.hsp_align hregs1.hx23 hx24_1 hregs1.hx25)
    fun sf Qf hpcf hrunf ⟨hpres, halignf, hx24f, hQf⟩ => ?_
  refine SepWP.weaken_pre hQf (sepWP_drop_left (SepWP.done hpcf hrunf
    ⟨tailEntryRegs_of_absorbPreserved hregs1 hpres hrunf halignf, hx24f, ?_⟩))
  dsimp only [keccakAbsorbPrefix17]
  sep_entail

/-- Absorb `rem > 0` remaining full 136-byte blocks (`k + rem = a.in0.length / 136`), reaching `+0x042c`. -/
private theorem absorb_loop [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl02 b) (hbase : blkPl02.base = b)
    (a : Keccak2FixedArgs) (hin0 : a.in0.length < 2 ^ 32) (hlen_eq : a.in0.length = a.in1.length)
    (sp rcBase : BitVec 64)
    (hrc : rcBase = mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29")
    (F : SepProp) :
    ∀ (rem k : Nat), 0 < rem → k + rem = a.in0.length / 136 →
      ∀ (s : State),
        s.pc = b + 0x009c#64 →
        TailEntryRegs s sp rcBase a →
        s.readReg64 .x24 = BitVec.ofNat 64 k →
        mlkemMultiLib.CodeLoaded mlkemMpl s.mem →
        MlKemRoOk mlkemMpl s.mem →
        SepWP (blkPC02.rebase b (fun _ => none)) (b + 0x042c#64) s
          (stackAt sp 16 ∗
            memRegion sp 176 ∗
            Keccak2Mem (sp + 176#64) (keccakAbsorbPrefix17 a.in0 k) (keccakAbsorbPrefix17 a.in1 k) ∗
            Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
            (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗
            F)
          (fun sf Pf =>
            TailEntryRegs sf sp rcBase a ∧
            (Pf ⊢ stackAt sp 16 ∗
              memRegion sp 176 ∗
              Keccak2Mem (sp + 176#64)
                (keccakAbsorbPrefix17 a.in0 (a.in0.length / 136))
                (keccakAbsorbPrefix17 a.in1 (a.in0.length / 136)) ∗
              Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
              (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗
              F))
  | 0, _, hpos, _ => absurd hpos (Nat.lt_irrefl 0)
  | r + 1, k, _, hsum => by
    intro s hpc hregs hx24 hcl hro
    have hk : k < a.in0.length / 136 := by omega
    refine sepWP_seq_env hcl hro
      (absorb_iter hb hbase a hin0 hlen_eq sp rcBase hrc k hk F s hpc hregs hx24 hcl hro) ?_
    intro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hregs1, hx24_1, hP1⟩
    refine SepWP.weaken_pre hP1 ?_
    by_cases hr : r = 0
    · subst hr
      have hend : k + 1 = a.in0.length / 136 := by omega
      have hnlt : ¬(k + 1 < a.in0.length / 136) := by omega
      simp only [hnlt, ↓reduceIte] at hpc1
      rw [hend]
      exact SepWP.done hpc1 hrun1 ⟨hregs1, Entails.refl _⟩
    · have hlt : k + 1 < a.in0.length / 136 := by omega
      simp only [hlt, ↓reduceIte] at hpc1
      exact absorb_loop hb hbase a hin0 hlen_eq sp rcBase hrc F r (k + 1)
        (Nat.pos_of_ne_zero hr) (by omega) s1 hpc1 hregs1 hx24_1 hcl1 hro1

public section

/-- Entry-to-tail segment `[0x0000 → 0x042c]` of `B02`: allocates the `1024`-byte local frame
    (`1040`-byte total stack footprint), zeroes the 2-way sponge state, absorbs all
    `a.in0.length / 136` full 136-byte blocks, and stops at `+0x042c` with `TailEntryRegs` and
    `keccakAbsorbPrefix17`. -/
theorem seg_entry_to_tail [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl02 b) (hbase : blkPl02.base = b)
    (a : Keccak2FixedArgs) (hin0 : a.in0.length < 2 ^ 32) (hlen_eq : a.in0.length = a.in1.length)
    (F : SepProp) (s0 : State)
    (hpc : s0.pc = b) (hrun : s0.status = .Running) (hsp0 : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = a.slicesPtr)
    (hx1 : s0.readReg64 .x1 = a.out0)
    (hx2 : s0.readReg64 .x2 = a.out1)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s0.mem)
    (hro : MlKemRoOk mlkemMpl s0.mem) :
    let sp := s0.sp - 1024#64
    let rcBase := mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29"
    SepWP (blkPC02.rebase b (fun _ => none)) (b + 0x042c#64) s0
      (Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
        (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗
        stackAt s0.sp 1040 ∗ F)
      (fun sm Pm =>
        TailEntryRegs sm sp rcBase a ∧
        (Pm ⊢ stackAt sp 16 ∗
          memRegion sp 176 ∗
          Keccak2Mem (sp + 176#64)
            (keccakAbsorbPrefix17 a.in0 (a.in0.length / 136))
            (keccakAbsorbPrefix17 a.in1 (a.in0.length / 136)) ∗
          memRegion (sp + 576#64) 288 ∗
          SavedFrame02 s0.sp s0 ∗
          Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
          (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗ F)) := by
  intro sp rcBase
  have hpre :
      Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
        (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗ stackAt s0.sp 1040 ∗ F ⊢
      Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
        stackAt s0.sp 1040 ∗ ((a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗ F) := by
    sep_frame
  refine SepWP.weaken_pre hpre ?_
  refine sepWP_seq_env hcl hro
    (seg_prologue b hb hbase a hin0 ((a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗ F) s0
      hpc hrun hsp0 hx0 hx1 hx2) ?_
  intro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨⟨hregs1, hx24_0⟩, hP1⟩
  refine SepWP.weaken_pre hP1 ?_
  by_cases hlt : a.in0.length < 136
  · simp only [hlt, ↓reduceIte] at hpc1
    have hdiv0 : a.in0.length / 136 = 0 := Nat.div_eq_of_lt hlt
    rw [hdiv0]
    refine SepWP.done hpc1 hrun1 ⟨hregs1, ?_⟩
    dsimp only [keccakAbsorbPrefix17]
    sep_frame
  · simp only [hlt, ↓reduceIte] at hpc1
    have hdiv_pos : 0 < a.in0.length / 136 := Nat.div_pos (by omega) (by decide)
    have hloop_pre :
        stackAt sp 16 ∗ memRegion sp 176 ∗
          Keccak2Mem (sp + 176#64) keccakZeroState keccakZeroState ∗
          memRegion (sp + 576#64) 288 ∗ SavedFrame02 s0.sp s0 ∗
          Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
          ((a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗ F) ⊢
        stackAt sp 16 ∗ memRegion sp 176 ∗
          Keccak2Mem (sp + 176#64) (keccakAbsorbPrefix17 a.in0 0) (keccakAbsorbPrefix17 a.in1 0) ∗
          Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
          (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗
          (memRegion (sp + 576#64) 288 ∗ SavedFrame02 s0.sp s0 ∗ F) := by
      dsimp only [keccakAbsorbPrefix17]
      sep_frame
    refine SepWP.weaken_pre hloop_pre ?_
    refine SepWP.seq
      (absorb_loop hb hbase a hin0 hlen_eq sp rcBase rfl
        (memRegion (sp + 576#64) 288 ∗ SavedFrame02 s0.sp s0 ∗ F)
        (a.in0.length / 136) 0 hdiv_pos (Nat.zero_add _) s1 hpc1 hregs1 (hx24_0 hlt) hcl1 hro1)
      fun sf Pf hpcf hrunf ⟨hregsf, hPf⟩ => ?_
    refine SepWP.done hpcf hrunf ⟨hregsf, Entails.trans hPf ?_⟩
    sep_frame

end

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.PrologueAbsorb
