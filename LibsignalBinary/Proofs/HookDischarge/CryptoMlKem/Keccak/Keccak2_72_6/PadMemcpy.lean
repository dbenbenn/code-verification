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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6.Prologue -- proof-setup: allow-public-import
import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp
meta import ProofLib
meta import ProofLib.ProgramReflection
meta import ProofLib.GenDecodes
meta import ProofLib.GenPlacedFetches

/-!
# `B00` (`keccak2::<72, 6>`): `memcpy` calls and `buf0` `SHA3-512` padding

Proof of segment `[0x05b4 → 0x0600]` (`19` instructions) of `mlkemBlk00`: steps both `B28`
`memcpy` calls via `blk28_memcpyRO_ok`, pads `buf0` into `keccakLastBlock 72 0x06#8 a.in0`, and
prepares `buf1` as `a.in1 ++ List.replicate (72 - a.in1.length) 0#8` at `+0x0600`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 20000

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6.PadMemcpy

open Arm64 ProofLib ProofLib.GenPlacedFetches SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
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
  resolve_blk28
  seq_codeLoaded_lr
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps (blk28_memcpyRO_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge (
  keccakLastBlock
  memRegion64_cells
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6.Base (
  SavedFrame00
  blk00_code_eq
  blk00_tree_size
  blkLib00
  blkPC00
  blkPl00
  blkPlaceable00
  blkTree00
  padBuf72_eq_lastBlock
  sepWP_seq_env
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6.Prologue (
  PreMemcpy0Regs
  ZeroStateMem00
  replicate72_entails_memcpy_split
  zeroCells9_eq_replicate72
)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp

section
set_option linter.literalFetch false
gen_placed_fetches blkPC00 blkLib00 blkTree00 blk00_code_eq blk00_tree_size
  via_placement blkPl00 blkPlaceable00 [0x05b4 → 0x05fc]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl00_ρ [MlKemPlacement] (sym : String) :
    blkPl00.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

public section

/-- Live registers at `+0x0600` right after the second `memcpy` call. -/
structure PadReadyRegs (s : State) (sp rcBase out0 out1 : BitVec 64) (len : Nat) : Prop where
  hrun      : s.status = .Running
  hsp_align : s.spAligned = true
  hsp       : s.sp = sp
  hx29      : s.readReg64 .x29 = sp + 624#64
  hx26      : s.readReg64 .x26 = 6#64
  hx25      : s.readReg64 .x25 = rcBase
  hx24      : s.readReg64 .x24 = BitVec.ofNat 64 len
  hx21      : s.readReg64 .x21 = sp + 480#64
  hx20      : s.readReg64 .x20 = out0
  hx19      : s.readReg64 .x19 = out1

theorem orr80_truncate8 (v : BitVec 8) :
    BitVec.zeroExtend 8 (BitVec.zeroExtend 64 v ||| 549755814016#64) = v ||| 0x80#8 := by
  bv_bits

end

private theorem entails_sub {A B P Rest Q : SepProp}
    (hAB : A ⊢ B) (h1 : P ⊢ A ∗ Rest) (h2 : B ∗ Rest ⊢ Q) : P ⊢ Q :=
  Entails.trans h1 (Entails.trans (sepConj_mono_left hAB) h2)

private theorem split88_eq (sp : BitVec 64) :
    memRegion (sp + 472#64) 88 =
      memRegion (sp + 472#64) 8 ∗ memRegion (sp + 480#64) 64 ∗
        memRegion (sp + 544#64) 8 ∗ memRegion (sp + 552#64) 8 := by
  rw [memRegion_split (sp + 472#64) 8 80 (by decide),
      show (sp + 472#64) + 8#64 = sp + 480#64 by bv_omega,
      memRegion_split (sp + 480#64) 64 16 (by decide),
      show (sp + 480#64) + 64#64 = sp + 544#64 by bv_omega,
      memRegion_split (sp + 544#64) 8 8 (by decide),
      show (sp + 544#64) + 8#64 = sp + 552#64 by bv_omega]

/-- Live registers at `+0x05fc` right before the second `memcpy` call. -/
private structure PreMemcpy1Regs (s : State) (sp rcBase : BitVec 64) (a : Keccak2FixedArgs) : Prop where
  hrun      : s.status = .Running
  hsp_align : s.spAligned = true
  hsp       : s.sp = sp
  hx29      : s.readReg64 .x29 = sp + 624#64
  hx26      : s.readReg64 .x26 = 6#64
  hx25      : s.readReg64 .x25 = rcBase
  hx24      : s.readReg64 .x24 = BitVec.ofNat 64 a.in1.length
  hx21      : s.readReg64 .x21 = sp + 480#64
  hx20      : s.readReg64 .x20 = a.out0
  hx19      : s.readReg64 .x19 = a.out1
  hx0       : s.readReg64 .x0 = sp + 480#64
  hx1       : s.readReg64 .x1 = a.ptr1
  hx2       : s.readReg64 .x2 = BitVec.ofNat 64 a.in1.length

/-- Step `[0x05b4 → 0x05fc]` (first `memcpy`, `buf0` SHA3-512 pad, `buf1` zeroing, prepare second `memcpy`). -/
private theorem seg_05b4_to_05fc [MlKemPlacement] (b : BitVec 64)
    (_hb : MlKemBase blkPl00 b) (_hbase : blkPl00.base = b)
    (a : Keccak2FixedArgs) (hlen : a.in0.length = a.in1.length) (hin0 : a.in0.length < 72)
    (sp rcBase : BitVec 64) (s0 s : State) (F : SepProp)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hpc : s.pc = b + 0x05b4#64)
    (hregs : PreMemcpy0Regs s sp rcBase a) :
    SepWP (blkPC00.rebase b (fun _ => none)) (b + 0x05fc#64) s
      (ZeroStateMem00 sp ∗
        memRegion (sp + 400#64) a.in0.length ∗
        (((sp + 400#64) + BitVec.ofNat 64 a.in0.length) ↦ₛ List.replicate (72 - a.in0.length) 0#8) ∗
        memRegion (sp + 472#64) 88 ∗
        SavedFrame00 s0.sp s0 ∗
        Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
        (a.ptr0 ↦ᵣ a.in0) ∗ F)
      (sepPost
        (fun sm => PreMemcpy1Regs sm sp rcBase a)
        (ZeroStateMem00 sp ∗
          ((sp + 400#64) ↦ₛ keccakLastBlock 72 0x06#8 a.in0) ∗
          memRegion (sp + 472#64) 8 ∗
          memRegion (sp + 480#64) a.in1.length ∗
          (((sp + 480#64) + BitVec.ofNat 64 a.in1.length) ↦ₛ List.replicate (72 - a.in1.length) 0#8) ∗
          memRegion (sp + 552#64) 8 ∗
          SavedFrame00 s0.sp s0 ∗
          Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
          (a.ptr0 ↦ᵣ a.in0) ∗ F)) := by
  rcases hregs with ⟨hrun, hsp_align, hsp, hx29, hx27, hx25, hx24, hx23, hx22, hx21,
    hx20, hx19, hx0, hx1, hx2⟩
  have hin0_u64 : a.in0.length < 2 ^ 64 := Nat.lt_trans hin0 (by decide)
  have hin1 : a.in1.length < 72 := by clear * - hlen hin0; omega
  have hx2_nat : (s.readReg64 .x2).toNat = a.in0.length := by
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hin0_u64]
  wp_step
  wp_mlkem_call blk28_memcpyRO_ok (sp + 400#64, a.ptr0, a.in0)
  have hsp_align_sf : sf.spAligned = true := by
    rw [State.spAligned, hsp_sf, ← State.spAligned]; exact hsp_align
  have hsp'  : sf.sp = sp := hsp_sf.trans hsp
  have hx29' : sf.readReg64 .x29 = sp + 624#64 :=
    (by assumption : sf.readReg64 .fp = s.readReg64 .fp).trans hx29
  have hx27' : sf.readReg64 .x27 = sp + 400#64 :=
    (by assumption : sf.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5)).trans hx27
  have hx25' : sf.readReg64 .x25 = rcBase :=
    (by assumption : sf.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5)).trans hx25
  have hx24' : sf.readReg64 .x24 = BitVec.ofNat 64 a.in0.length :=
    (by assumption : sf.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5)).trans hx24
  have hx23' : sf.readReg64 .x23 = 0#64 :=
    (by assumption : sf.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5)).trans hx23
  have hx22' : sf.readReg64 .x22 = a.slicesPtr :=
    (by assumption : sf.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5)).trans hx22
  have hx21' : sf.readReg64 .x21 = BitVec.ofNat 64 a.in0.length :=
    (by assumption : sf.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5)).trans hx21
  have hx20' : sf.readReg64 .x20 = a.out0 :=
    (by assumption : sf.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5)).trans hx20
  have hx19' : sf.readReg64 .x19 = a.out1 :=
    (by assumption : sf.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5)).trans hx19
  have hrejoin0 :
      ((sp + 400#64) ↦ₛ a.in0) ∗
        (((sp + 400#64) + BitVec.ofNat 64 a.in0.length) ↦ₛ List.replicate (72 - a.in0.length) 0#8) =
        ((sp + 400#64) ↦ₛ (a.in0 ++ List.replicate (72 - a.in0.length) 0#8)) :=
    (pointsToBytes_append (sp + 400#64) a.in0 (List.replicate (72 - a.in0.length) 0#8)).symm
  refine SepWP.weaken_pre
    (show _ ⊢
      ((sp + 400#64) ↦ₛ (a.in0 ++ List.replicate (72 - a.in0.length) 0#8)) ∗
        memRegion (sp + 472#64) 88 ∗ ZeroStateMem00 sp ∗ SavedFrame00 s0.sp s0 ∗
        Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
        (a.ptr0 ↦ᵣ a.in0) ∗ F by
      rw [← hrejoin0]; sep_frame) ?_
  rw [split88_eq sp]
  refine memRegion64_cells (sp + 480#64) (by sep_focus)
    fun _d0 _d1 _d2 _d3 _d4 _d5 _d6 _d7 => ?_
  refine SepWP.memRegion8_cell (sp + 544#64) fun _d8 => ?_
  have hbuf0_0_len : (a.in0 ++ List.replicate (72 - a.in0.length) 0#8).length = 72 := by
    clear * - hin0; simp; omega
  have hbuf0_1_len :
      (ByteSlice.write8 (a.in0 ++ List.replicate (72 - a.in0.length) 0#8) a.in0.length 0x06#8).length = 72 := by
    unfold ByteSlice.write8
    rw [ByteSlice.write_length _ _ _ (by simp [hbuf0_0_len]; omega), hbuf0_0_len]
  have hbuf0_0_len' : (a.in0 ++ List.replicate (72 - a.in1.length) 0#8).length = 72 := by
    rw [← hlen]; exact hbuf0_0_len
  have hbuf0_1_len' :
      (ByteSlice.write8 (a.in0 ++ List.replicate (72 - a.in1.length) 0#8) a.in1.length 0x06#8).length = 72 := by
    rw [← hlen]; exact hbuf0_1_len
  unfold Keccak2SlicesRO
  wp_steps
  wp_if hbr
  · exfalso
    simp [BitVec.ult] at hbr
  · wp_steps
    apply SepWP.done
    · wp_norm_lhs
    · wp_norm_lhs
    · rw [sepPost_apply]
      refine ⟨?_, ?_⟩
      · exact
          { hrun      := by wp_norm_lhs
            hsp_align := by wp_norm_lhs
            hsp       := by wp_norm_lhs
            hx29      := by wp_norm_lhs
            hx26      := by wp_norm_lhs
            hx25      := by wp_norm_lhs
            hx24      := by wp_norm_lhs
            hx21      := by refine Eq.trans (by wp_norm_lhs) (by clear * -; bv_omega)
            hx20      := by wp_norm_lhs
            hx19      := by wp_norm_lhs
            hx0       := by refine Eq.trans (by wp_norm_lhs) (by clear * -; bv_omega)
            hx1       := by refine Eq.trans (by wp_norm_lhs) (by simp)
            hx2       := by wp_norm_lhs }
      · have hbuf1 :
            (((((sp + 480#64) ↦₆₄ 0#64) ∗ (((sp + 480#64) + 8#64) ↦₆₄ 0#64)) ∗
               ((((sp + 480#64) + 16#64) ↦₆₄ 0#64) ∗ (((sp + 480#64) + 24#64) ↦₆₄ 0#64))) ∗
              (((((sp + 480#64) + 32#64) ↦₆₄ 0#64) ∗ (((sp + 480#64) + 40#64) ↦₆₄ 0#64)) ∗
               ((((sp + 480#64) + 48#64) ↦₆₄ 0#64) ∗ (((sp + 480#64) + 56#64) ↦₆₄ 0#64)))) ∗
             ((sp + 544#64) ↦₆₄ 0#64) ⊢
              memRegion (sp + 480#64) a.in1.length ∗
                (((sp + 480#64) + BitVec.ofNat 64 a.in1.length) ↦ₛ
                  List.replicate (72 - a.in1.length) 0#8) := by
          rw [show sp + 544#64 = (sp + 480#64) + 64#64 by clear * -; bv_omega,
              zeroCells9_eq_replicate72 (sp + 480#64)]
          exact replicate72_entails_memcpy_split (sp + 480#64) a.in1.length hin1
        have hpad0' := padBuf72_eq_lastBlock a.in0 hin0
        dsimp only at hpad0'
        rw [hlen] at hpad0'
        simp only [orr80_truncate8, hpad0', hlen]
        exact entails_sub hbuf1 (by sep_frame) (by sep_frame)

/-- Step `[0x05fc → 0x0600]` (second `memcpy` into `buf1`). -/
private theorem seg_05fc_to_0600 [MlKemPlacement] (b : BitVec 64)
    (_hb : MlKemBase blkPl00 b) (_hbase : blkPl00.base = b)
    (a : Keccak2FixedArgs) (hin1 : a.in1.length < 72)
    (sp rcBase : BitVec 64) (s0 s : State) (F : SepProp)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hpc : s.pc = b + 0x05fc#64)
    (hregs : PreMemcpy1Regs s sp rcBase a) :
    SepWP (blkPC00.rebase b (fun _ => none)) (b + 0x0600#64) s
      (ZeroStateMem00 sp ∗
        ((sp + 400#64) ↦ₛ keccakLastBlock 72 0x06#8 a.in0) ∗
        memRegion (sp + 472#64) 8 ∗
        memRegion (sp + 480#64) a.in1.length ∗
        (((sp + 480#64) + BitVec.ofNat 64 a.in1.length) ↦ₛ List.replicate (72 - a.in1.length) 0#8) ∗
        memRegion (sp + 552#64) 8 ∗
        SavedFrame00 s0.sp s0 ∗
        Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
        (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗ F)
      (sepPost
        (fun sm => PadReadyRegs sm sp rcBase a.out0 a.out1 a.in1.length)
        (ZeroStateMem00 sp ∗
          ((sp + 400#64) ↦ₛ keccakLastBlock 72 0x06#8 a.in0) ∗
          memRegion (sp + 472#64) 8 ∗
          ((sp + 480#64) ↦ₛ (a.in1 ++ List.replicate (72 - a.in1.length) 0#8)) ∗
          memRegion (sp + 552#64) 8 ∗
          SavedFrame00 s0.sp s0 ∗
          Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
          (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗ F)) := by
  rcases hregs with ⟨hrun, hsp_align, hsp, hx29, hx26, hx25, hx24, hx21, hx20, hx19,
    hx0, hx1, hx2⟩
  have hin1_u64 : a.in1.length < 2 ^ 64 := Nat.lt_trans hin1 (by decide)
  have hx2_nat : (s.readReg64 .x2).toNat = a.in1.length := by
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hin1_u64]
  wp_step
  wp_mlkem_call blk28_memcpyRO_ok (sp + 480#64, a.ptr1, a.in1)
  have hsp_align_sf : sf.spAligned = true := by
    rw [State.spAligned, hsp_sf, ← State.spAligned]; exact hsp_align
  have hrejoin1 :
      ((sp + 480#64) ↦ₛ a.in1) ∗
        (((sp + 480#64) + BitVec.ofNat 64 a.in1.length) ↦ₛ List.replicate (72 - a.in1.length) 0#8) =
        ((sp + 480#64) ↦ₛ (a.in1 ++ List.replicate (72 - a.in1.length) 0#8)) :=
    (pointsToBytes_append (sp + 480#64) a.in1 (List.replicate (72 - a.in1.length) 0#8)).symm
  refine SepWP.done hpc_sf hrun_sf ?_
  rw [sepPost_apply]
  refine ⟨?_, ?_⟩
  · exact
      { hrun      := hrun_sf
        hsp_align := hsp_align_sf
        hsp       := hsp_sf.trans hsp
        hx29      := (by assumption : sf.readReg64 .fp = s.readReg64 .fp).trans hx29
        hx26      := (by assumption : sf.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5)).trans hx26
        hx25      := (by assumption : sf.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5)).trans hx25
        hx24      := (by assumption : sf.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5)).trans hx24
        hx21      := (by assumption : sf.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5)).trans hx21
        hx20      := (by assumption : sf.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5)).trans hx20
        hx19      := (by assumption : sf.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5)).trans hx19 }
  · rw [← hrejoin1]
    sep_frame

public section

/-- Combined `[0x05b4 → 0x0600]` segment (both `memcpy` calls + `buf0` SHA3-512 padding). -/
theorem memcpy_pad_ok [MlKemPlacement] (b : BitVec 64)
    (hb : MlKemBase blkPl00 b) (hbase : blkPl00.base = b)
    (a : Keccak2FixedArgs) (hlen : a.in0.length = a.in1.length) (hin0 : a.in0.length < 72)
    (sp rcBase : BitVec 64) (s0 s : State) (F : SepProp)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hro : MlKemRoOk mlkemMpl s.mem)
    (hpc : s.pc = b + 0x05b4#64)
    (hregs : PreMemcpy0Regs s sp rcBase a) :
    SepWP (blkPC00.rebase b (fun _ => none)) (b + 0x0600#64) s
      (ZeroStateMem00 sp ∗
        memRegion (sp + 400#64) a.in0.length ∗
        (((sp + 400#64) + BitVec.ofNat 64 a.in0.length) ↦ₛ List.replicate (72 - a.in0.length) 0#8) ∗
        memRegion (sp + 472#64) 88 ∗
        SavedFrame00 s0.sp s0 ∗
        Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
        (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗ F)
      (sepPost
        (fun sm => PadReadyRegs sm sp rcBase a.out0 a.out1 a.in1.length)
        (ZeroStateMem00 sp ∗
          ((sp + 400#64) ↦ₛ keccakLastBlock 72 0x06#8 a.in0) ∗
          memRegion (sp + 472#64) 8 ∗
          ((sp + 480#64) ↦ₛ (a.in1 ++ List.replicate (72 - a.in1.length) 0#8)) ∗
          memRegion (sp + 552#64) 8 ∗
          SavedFrame00 s0.sp s0 ∗
          Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
          (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗ F)) := by
  have hin1 : a.in1.length < 72 := by clear * - hlen hin0; omega
  refine sepWP_seq_env hcl hro
    (SepWP.congr_pre (sepProp_ext (by sep_frame) (by sep_frame))
      (seg_05b4_to_05fc b hb hbase a hlen hin0 sp rcBase s0 s
        ((a.ptr1 ↦ᵣ a.in1) ∗ F) hcl hpc hregs)) ?_
  intro s1 P1 hpc1 _ hcl1 _ hpost1
  rw [sepPost_apply] at hpost1
  rcases hpost1 with ⟨hregs1, hP1⟩
  refine SepWP.weaken_pre (Entails.trans hP1 (by sep_frame)) ?_
  exact seg_05fc_to_0600 b hb hbase a hin1 sp rcBase s0 s1 F hcl1 hpc1 hregs1

end

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6.PadMemcpy
