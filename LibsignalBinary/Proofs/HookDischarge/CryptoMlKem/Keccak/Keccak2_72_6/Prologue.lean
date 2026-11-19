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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6.Base
import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp
meta import ProofLib
meta import ProofLib.ProgramReflection
meta import ProofLib.GenDecodes
meta import ProofLib.GenPlacedFetches

/-!
# `B00` (`keccak2::<72, 6>`): prologue and state-zeroing setup

Proof of segments `[0x0000 → 0x00cc]` (`52` instructions, `b.lo +0x0540` taken for `inLen < 72`)
and `[0x0540 → 0x05b4]` (`29` instructions, zeroing all `50` 64-bit cells of `[sp, sp + 400)`
and `buf0` `[sp + 400, sp + 472)`, and preparing arguments for the first `B28` `memcpy` call) of
`mlkemBlk00`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6.Prologue

open Arm64 ProofLib ProofLib.GenPlacedFetches SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (
  Keccak2FixedArgs
  Keccak2SlicesRO
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase
  MlKemPlacement
  mlkemMpl
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge (
  memRegion128_cells
  memRegion32_cells
  memRegion64_cells
  pointsTo64_8_eq_bytes
  pointsTo64_eq_unpackLane64
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
  sepWP_seq_env
  umulh_div72_nat
)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp

section
set_option linter.literalFetch false
gen_placed_fetches blkPC00 blkLib00 blkTree00 blk00_code_eq blk00_tree_size
  via_placement blkPl00 blkPlaceable00 [0x0000 → 0x00cc]
gen_placed_fetches blkPC00 blkLib00 blkTree00 blk00_code_eq blk00_tree_size
  via_placement blkPl00 blkPlaceable00 [0x0540 → 0x05b0]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl00_ρ [MlKemPlacement] (sym : String) :
    blkPl00.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

public section

/-- All 50 64-bit cells (`400` bytes) of `[sp, sp + 400)` zeroed before the 9-lane absorb. -/
@[expose] def ZeroStateMem00 (sp : BitVec 64) : SepProp :=
  (sp ↦₆₄ 0#64) ∗ ((sp + 8#64) ↦₆₄ 0#64) ∗
  ((sp + 16#64) ↦₆₄ 0#64) ∗ ((sp + 24#64) ↦₆₄ 0#64) ∗
  ((sp + 32#64) ↦₆₄ 0#64) ∗ ((sp + 40#64) ↦₆₄ 0#64) ∗
  ((sp + 48#64) ↦₆₄ 0#64) ∗ ((sp + 56#64) ↦₆₄ 0#64) ∗
  ((sp + 64#64) ↦₆₄ 0#64) ∗ ((sp + 72#64) ↦₆₄ 0#64) ∗
  ((sp + 80#64) ↦₆₄ 0#64) ∗ ((sp + 88#64) ↦₆₄ 0#64) ∗
  ((sp + 96#64) ↦₆₄ 0#64) ∗ ((sp + 104#64) ↦₆₄ 0#64) ∗
  ((sp + 112#64) ↦₆₄ 0#64) ∗ ((sp + 120#64) ↦₆₄ 0#64) ∗
  ((sp + 128#64) ↦₆₄ 0#64) ∗ ((sp + 136#64) ↦₆₄ 0#64) ∗
  ((sp + 144#64) ↦₆₄ 0#64) ∗ ((sp + 152#64) ↦₆₄ 0#64) ∗
  ((sp + 160#64) ↦₆₄ 0#64) ∗ ((sp + 168#64) ↦₆₄ 0#64) ∗
  ((sp + 176#64) ↦₆₄ 0#64) ∗ ((sp + 184#64) ↦₆₄ 0#64) ∗
  ((sp + 192#64) ↦₆₄ 0#64) ∗ ((sp + 200#64) ↦₆₄ 0#64) ∗
  ((sp + 208#64) ↦₆₄ 0#64) ∗ ((sp + 216#64) ↦₆₄ 0#64) ∗
  ((sp + 224#64) ↦₆₄ 0#64) ∗ ((sp + 232#64) ↦₆₄ 0#64) ∗
  ((sp + 240#64) ↦₆₄ 0#64) ∗ ((sp + 248#64) ↦₆₄ 0#64) ∗
  ((sp + 256#64) ↦₆₄ 0#64) ∗ ((sp + 264#64) ↦₆₄ 0#64) ∗
  ((sp + 272#64) ↦₆₄ 0#64) ∗ ((sp + 280#64) ↦₆₄ 0#64) ∗
  ((sp + 288#64) ↦₆₄ 0#64) ∗ ((sp + 296#64) ↦₆₄ 0#64) ∗
  ((sp + 304#64) ↦₆₄ 0#64) ∗ ((sp + 312#64) ↦₆₄ 0#64) ∗
  ((sp + 320#64) ↦₆₄ 0#64) ∗ ((sp + 328#64) ↦₆₄ 0#64) ∗
  ((sp + 336#64) ↦₆₄ 0#64) ∗ ((sp + 344#64) ↦₆₄ 0#64) ∗
  ((sp + 352#64) ↦₆₄ 0#64) ∗ ((sp + 360#64) ↦₆₄ 0#64) ∗
  ((sp + 368#64) ↦₆₄ 0#64) ∗ ((sp + 376#64) ↦₆₄ 0#64) ∗
  ((sp + 384#64) ↦₆₄ 0#64) ∗ ((sp + 392#64) ↦₆₄ 0#64)

/-- Live registers at `+0x05b4` right before the first `memcpy` call. -/
structure PreMemcpy0Regs (s : State) (sp rcBase : BitVec 64) (a : Keccak2FixedArgs) : Prop where
  hrun      : s.status = .Running
  hsp_align : s.spAligned = true
  hsp       : s.sp = sp
  hx29      : s.readReg64 .x29 = sp + 624#64
  hx27      : s.readReg64 .x27 = sp + 400#64
  hx25      : s.readReg64 .x25 = rcBase
  hx24      : s.readReg64 .x24 = BitVec.ofNat 64 a.in0.length
  hx23      : s.readReg64 .x23 = 0#64
  hx22      : s.readReg64 .x22 = a.slicesPtr
  hx21      : s.readReg64 .x21 = BitVec.ofNat 64 a.in0.length
  hx20      : s.readReg64 .x20 = a.out0
  hx19      : s.readReg64 .x19 = a.out1
  hx0       : s.readReg64 .x0 = sp + 400#64
  hx1       : s.readReg64 .x1 = a.ptr0
  hx2       : s.readReg64 .x2 = BitVec.ofNat 64 a.in0.length

theorem memRegion16_cells {prog : Program} {target_pc : BitVec 64} {s : State}
    {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (a : BitVec 64)
    (hf : P = memRegion a 16 ∗ F := by sep_focus)
    (h : ∀ w0 w1 : BitVec 64,
      SepWP prog target_pc s (((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1)) ∗ F) post oom) :
    SepWP prog target_pc s P post oom := by
  rw [hf, show memRegion a 16 = memRegion a 8 ∗ memRegion (a + 8#64) 8 from
    memRegion_split a 8 8 (by decide)]
  refine SepWP.memRegion8_cell a fun w0 => ?_
  refine SepWP.memRegion8_cell (a + 8#64) fun w1 => ?_
  exact SepWP.congr_pre (sepProp_ext (by sep_frame) (by sep_frame)) (h w0 w1)

theorem zeroCells9_eq_replicate72 (base : BitVec 64) :
    (((((base ↦₆₄ 0#64) ∗ ((base + 8#64) ↦₆₄ 0#64)) ∗
       (((base + 16#64) ↦₆₄ 0#64) ∗ ((base + 24#64) ↦₆₄ 0#64))) ∗
      ((((base + 32#64) ↦₆₄ 0#64) ∗ ((base + 40#64) ↦₆₄ 0#64)) ∗
       (((base + 48#64) ↦₆₄ 0#64) ∗ ((base + 56#64) ↦₆₄ 0#64)))) ∗
     ((base + 64#64) ↦₆₄ 0#64)) =
      (base ↦ₛ List.replicate 72 0#8) := by
  rw [pointsTo64_8_eq_bytes base 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64,
      pointsTo64_eq_unpackLane64 (base + 64#64) 0#64,
      show base + 64#64 = base + BitVec.ofNat 64
        (Spec.unpackLane64 0#64 ++ Spec.unpackLane64 0#64 ++ Spec.unpackLane64 0#64 ++
         Spec.unpackLane64 0#64 ++ Spec.unpackLane64 0#64 ++ Spec.unpackLane64 0#64 ++
         Spec.unpackLane64 0#64 ++ Spec.unpackLane64 0#64).length from rfl,
      ← pointsToBytes_append]
  rfl

theorem replicate72_entails_memcpy_split (base : BitVec 64) (n : Nat) (hn : n < 72) :
    (base ↦ₛ List.replicate 72 0#8) ⊢
      memRegion base n ∗ ((base + BitVec.ofNat 64 n) ↦ₛ List.replicate (72 - n) 0#8) := by
  have hrep : List.replicate 72 0#8 = List.replicate n 0#8 ++ List.replicate (72 - n) 0#8 := by
    rw [← List.replicate_add, Nat.add_sub_of_le (by omega)]
  rw [hrep, pointsToBytes_append, List.length_replicate]
  simpa only [List.length_replicate] using
    sepConj_mono_left (pointsToBytes_entails_memRegion base (List.replicate n 0#8))

end

private theorem entails_sub {A B P Rest Q : SepProp}
    (hAB : A ⊢ B) (h1 : P ⊢ A ∗ Rest) (h2 : B ∗ Rest ⊢ Q) : P ⊢ Q :=
  Entails.trans h1 (Entails.trans (sepConj_mono_left hAB) h2)

private theorem stack720_prologue_split (sp0 : BitVec 64) :
    let sp := sp0 - 720#64
    stackAt sp0 720 =
      memRegion sp 288 ∗ memRegion (sp + 288#64) 16 ∗ memRegion (sp + 304#64) 96 ∗
        memRegion (sp + 400#64) 160 ∗
        memRegion (sp0 - 160#64) 128 ∗ memRegion (sp0 - 32#64) 32 := by
  intro sp
  unfold stackAt
  change memRegion sp 720 = _
  rw [memRegion_split sp 288 432 (by decide),
      memRegion_split (sp + 288#64) 16 416 (by decide),
      show (sp + 288#64) + 16#64 = sp + 304#64 by dsimp [sp]; bv_omega,
      memRegion_split (sp + 304#64) 96 320 (by decide),
      show (sp + 304#64) + 96#64 = sp + 400#64 by dsimp [sp]; bv_omega,
      memRegion_split (sp + 400#64) 160 160 (by decide),
      show (sp + 400#64) + 160#64 = sp0 - 160#64 by dsimp [sp]; bv_omega,
      memRegion_split (sp0 - 160#64) 128 32 (by decide),
      show (sp0 - 160#64) + 128#64 = sp0 - 32#64 by bv_omega]

private theorem split288_eq (sp : BitVec 64) :
    memRegion sp 288 =
      memRegion sp 128 ∗ memRegion (sp + 128#64) 128 ∗ memRegion (sp + 256#64) 32 := by
  rw [memRegion_split sp 128 160 (by decide),
      memRegion_split (sp + 128#64) 128 32 (by decide),
      show (sp + 128#64) + 128#64 = sp + 256#64 by bv_omega]

private theorem split96_eq (sp : BitVec 64) :
    memRegion (sp + 304#64) 96 =
      memRegion (sp + 304#64) 64 ∗ memRegion (sp + 368#64) 32 := by
  rw [memRegion_split (sp + 304#64) 64 32 (by decide),
      show (sp + 304#64) + 64#64 = sp + 368#64 by bv_omega]

private theorem split160_eq (sp : BitVec 64) :
    memRegion (sp + 400#64) 160 =
      memRegion (sp + 400#64) 64 ∗ memRegion (sp + 464#64) 8 ∗ memRegion (sp + 472#64) 88 := by
  rw [memRegion_split (sp + 400#64) 64 96 (by decide),
      show (sp + 400#64) + 64#64 = sp + 464#64 by bv_omega,
      memRegion_split (sp + 464#64) 8 88 (by decide),
      show (sp + 464#64) + 8#64 = sp + 472#64 by bv_omega]

private theorem ult_72_of_lt {n : Nat} (hn : n < 72) :
    (BitVec.ofNat 64 n).ult 72#64 = true := by
  have hn64 : n < 2 ^ 64 := Nat.lt_trans hn (by decide)
  rw [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]
  exact decide_eq_true hn

private theorem umulh_div72_eval {n : Nat} (hn : n < 72) :
    BitVec.truncate 64
      ((BitVec.zeroExtend 128 (BitVec.ofNat 64 n) * 16397105843297379215#128) >>> 64) >>> 6 =
      0#64 := by
  apply BitVec.eq_of_toNat_eq
  have hn64 : n < 2 ^ 64 := Nat.lt_trans hn (by decide)
  have hn128 : n < 2 ^ 128 := Nat.lt_trans hn (by decide)
  have h128 : (BitVec.zeroExtend 128 (BitVec.ofNat 64 n)).toNat = n := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64, Nat.mod_eq_of_lt hn128]
  have hc : (16397105843297379215#128).toNat = 0xe38e38e38e38e38f := rfl
  have hmul : n * 0xe38e38e38e38e38f < 2 ^ 128 :=
    Nat.lt_trans (Nat.mul_lt_mul_of_pos_right hn (by decide)) (by decide)
  have hdiv : n * 0xe38e38e38e38e38f / 2 ^ 64 < 2 ^ 64 :=
    Nat.lt_of_le_of_lt
      (Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.le_of_lt hn)))
      (by decide)
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
      BitVec.toNat_mul, h128, hc, Nat.mod_eq_of_lt hmul,
      Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt hdiv, umulh_div72_nat hn]
  rfl

/-- Register state at `+0x0540` after `b.lo` is taken (`inLen < 72`). -/
private structure Branch540Regs (s : State) (sp rcBase slicesPtr out0 out1 : BitVec 64)
    (len0 : Nat) : Prop where
  hrun      : s.status = .Running
  hsp_align : s.spAligned = true
  hsp       : s.sp = sp
  hx29      : s.readReg64 .x29 = sp + 624#64
  hx25      : s.readReg64 .x25 = rcBase
  hx22      : s.readReg64 .x22 = slicesPtr
  hx21      : s.readReg64 .x21 = BitVec.ofNat 64 len0
  hx20      : s.readReg64 .x20 = out0
  hx19      : s.readReg64 .x19 = out1
  hx10      : s.readReg64 .x10 = 0#64
  hv1       : s.readVReg128 1#5  = 0#128
  hv2       : s.readVReg128 2#5  = 0#128
  hv4       : s.readVReg128 4#5  = 0#128
  hv5       : s.readVReg128 5#5  = 0#128
  hv6       : s.readVReg128 6#5  = 0#128
  hv7       : s.readVReg128 7#5  = 0#128
  hv10      : s.readVReg128 10#5 = 0#128
  hv12      : s.readVReg128 12#5 = 0#128
  hv13      : s.readVReg128 13#5 = 0#128
  hv16      : s.readVReg128 16#5 = 0#128
  hv17      : s.readVReg128 17#5 = 0#128
  hv18      : s.readVReg128 18#5 = 0#128
  hv19      : s.readVReg128 19#5 = 0#128
  hv20      : s.readVReg128 20#5 = 0#128
  hv21      : s.readVReg128 21#5 = 0#128
  hv22      : s.readVReg128 22#5 = 0#128
  hv23      : s.readVReg128 23#5 = 0#128
  hv24      : s.readVReg128 24#5 = 0#128
  hv25      : s.readVReg128 25#5 = 0#128
  hv26      : s.readVReg128 26#5 = 0#128
  hv27      : s.readVReg128 27#5 = 0#128
  hv28      : s.readVReg128 28#5 = 0#128
  hv30      : s.readVReg128 30#5 = 0#128
  hv31      : s.readVReg128 31#5 = 0#128

/-- Step `[0x0000 → 0x0540]` (prologue + `inLen < 72` branch taken at `+0x00cc`). -/
private theorem seg_0000_to_0540 [MlKemPlacement] (b : BitVec 64)
    (_hb : MlKemBase blkPl00 b) (_hbase : blkPl00.base = b)
    (a : Keccak2FixedArgs) (hin0 : a.in0.length < 72)
    (F : SepProp) (s0 : State)
    (hpc : s0.pc = b) (hrun : s0.status = .Running) (hsp0 : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = a.slicesPtr)
    (hx1 : s0.readReg64 .x1 = a.out0)
    (hx2 : s0.readReg64 .x2 = a.out1) :
    let sp := s0.sp - 720#64
    let rcBase := mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29"
    SepWP (blkPC00.rebase b (fun _ => none)) (b + 0x0540#64) s0
      (Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
        stackAt s0.sp 720 ∗ F)
      (sepPost
        (fun sm => Branch540Regs sm sp rcBase a.slicesPtr a.out0 a.out1 a.in0.length)
        (memRegion sp 288 ∗
          ((sp + 288#64) ↦₆₄ 0#64) ∗ ((sp + 296#64) ↦₆₄ 0#64) ∗
          memRegion (sp + 304#64) 96 ∗
          memRegion (sp + 400#64) 160 ∗
          SavedFrame00 s0.sp s0 ∗
          Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗ F)) := by
  intro sp rcBase
  have hsp160 : ((s0.sp - 160#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 160#64 hsp0 (by decide)
  have hsp720 : (((s0.sp - 160#64) - 560#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub (s0.sp - 160#64) 560#64 hsp160 (by decide)
  rw [stack720_prologue_split s0.sp]
  refine memRegion16_cells ((s0.sp - 720#64) + 288#64) (by sep_focus) fun _p0 _p1 => ?_
  refine memRegion128_cells (s0.sp - 160#64) (by sep_focus)
    fun _c0 _c1 _c2 _c3 _c4 _c5 _c6 _c7 _c8 _c9 _c10 _c11 _c12 _c13 _c14 _c15 => ?_
  refine memRegion32_cells (s0.sp - 32#64) (by sep_focus) fun _c16 _c17 _c18 _c19 => ?_
  have hs17 : (s0.sp - 32#64) + 8#64  = s0.sp - 24#64 := by clear * -; bv_omega
  have hs18 : (s0.sp - 32#64) + 16#64 = s0.sp - 16#64 := by clear * -; bv_omega
  have hs19 : (s0.sp - 32#64) + 24#64 = s0.sp - 8#64  := by clear * -; bv_omega
  rw [hs17, hs18, hs19]
  clear hs17 hs18 hs19
  unfold Keccak2SlicesRO
  wp_steps
  wp_if hbr
  · apply SepWP.done
    · wp_norm_lhs
    · wp_norm_lhs
    · rw [sepPost_apply]
      refine ⟨?_, ?_⟩
      · refine
          { hrun      := by wp_norm_lhs
            hsp_align := by rw [State.spAligned]; simpa using hsp720
            hsp       := by wp_norm_lhs
            hx29      := by refine Eq.trans (by wp_norm_lhs) (by dsimp [sp]; clear * -; bv_omega)
            hx25      := by wp_norm_lhs
            hx22      := by wp_norm_lhs
            hx21      := by wp_norm_lhs
            hx20      := by wp_norm_lhs
            hx19      := by wp_norm_lhs
            hx10      := by refine Eq.trans (by wp_norm_lhs) (umulh_div72_eval hin0)
            hv1  := by wp_norm_lhs, hv2  := by wp_norm_lhs, hv4  := by wp_norm_lhs
            hv5  := by wp_norm_lhs, hv6  := by wp_norm_lhs, hv7  := by wp_norm_lhs
            hv10 := by wp_norm_lhs, hv12 := by wp_norm_lhs, hv13 := by wp_norm_lhs
            hv16 := by wp_norm_lhs, hv17 := by wp_norm_lhs, hv18 := by wp_norm_lhs
            hv19 := by wp_norm_lhs, hv20 := by wp_norm_lhs, hv21 := by wp_norm_lhs
            hv22 := by wp_norm_lhs, hv23 := by wp_norm_lhs, hv24 := by wp_norm_lhs
            hv25 := by wp_norm_lhs, hv26 := by wp_norm_lhs, hv27 := by wp_norm_lhs
            hv28 := by wp_norm_lhs, hv30 := by wp_norm_lhs, hv31 := by wp_norm_lhs }
      · dsimp only [sp, SavedFrame00, Keccak2SlicesRO]
        rw [show (s0.sp - 720#64) + 288#64 = s0.sp - 432#64 by clear * -; bv_omega,
            show (s0.sp - 720#64) + 296#64 = s0.sp - 424#64 by clear * -; bv_omega,
            show (s0.sp - 720#64) + 304#64 = s0.sp - 416#64 by clear * -; bv_omega,
            show (s0.sp - 720#64) + 400#64 = s0.sp - 320#64 by clear * -; bv_omega]
        sep_frame
  · exact absurd (ult_72_of_lt hin0) hbr

/-- Step `[0x0540 → 0x05b4]` (zeroing `[sp, sp + 400)` and `buf0`, preparing `memcpy` args). -/
private theorem seg_0540_to_05b4 [MlKemPlacement] (b : BitVec 64)
    (_hb : MlKemBase blkPl00 b) (_hbase : blkPl00.base = b)
    (a : Keccak2FixedArgs) (hin0 : a.in0.length < 72)
    (sp rcBase : BitVec 64) (s0 s : State) (F : SepProp)
    (hpc : s.pc = b + 0x0540#64)
    (hregs : Branch540Regs s sp rcBase a.slicesPtr a.out0 a.out1 a.in0.length) :
    SepWP (blkPC00.rebase b (fun _ => none)) (b + 0x05b4#64) s
      (memRegion sp 288 ∗
        ((sp + 288#64) ↦₆₄ 0#64) ∗ ((sp + 296#64) ↦₆₄ 0#64) ∗
        memRegion (sp + 304#64) 96 ∗
        memRegion (sp + 400#64) 160 ∗
        SavedFrame00 s0.sp s0 ∗
        Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗ F)
      (sepPost
        (fun sm => PreMemcpy0Regs sm sp rcBase a)
        (ZeroStateMem00 sp ∗
          memRegion (sp + 400#64) a.in0.length ∗
          (((sp + 400#64) + BitVec.ofNat 64 a.in0.length) ↦ₛ List.replicate (72 - a.in0.length) 0#8) ∗
          memRegion (sp + 472#64) 88 ∗
          SavedFrame00 s0.sp s0 ∗
          Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗ F)) := by
  rcases hregs with ⟨hrun, hsp_align, hsp, hx29, hx25, hx22, hx21, hx20, hx19, hx10,
    hv1, hv2, hv4, hv5, hv6, hv7, hv10, hv12, hv13, hv16, hv17, hv18, hv19,
    hv20, hv21, hv22, hv23, hv24, hv25, hv26, hv27, hv28, hv30, hv31⟩
  rw [split288_eq sp, split96_eq sp, split160_eq sp]
  refine memRegion128_cells sp (by sep_focus)
    fun _u0 _u1 _u2 _u3 _u4 _u5 _u6 _u7 _u8 _u9 _u10 _u11 _u12 _u13 _u14 _u15 => ?_
  refine memRegion128_cells (sp + 128#64) (by sep_focus)
    fun _v0 _v1 _v2 _v3 _v4 _v5 _v6 _v7 _v8 _v9 _v10 _v11 _v12 _v13 _v14 _v15 => ?_
  refine memRegion32_cells (sp + 256#64) (by sep_focus) fun _q0 _q1 _q2 _q3 => ?_
  refine memRegion64_cells (sp + 304#64) (by sep_focus)
    fun _w0 _w1 _w2 _w3 _w4 _w5 _w6 _w7 => ?_
  refine memRegion32_cells (sp + 368#64) (by sep_focus) fun _y0 _y1 _y2 _y3 => ?_
  refine memRegion64_cells (sp + 400#64) (by sep_focus)
    fun _b0 _b1 _b2 _b3 _b4 _b5 _b6 _b7 => ?_
  refine SepWP.memRegion8_cell (sp + 464#64) fun _b8 => ?_
  unfold Keccak2SlicesRO
  wp_steps
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
          hx27      := by refine Eq.trans (by wp_norm_lhs) (by clear * -; bv_omega)
          hx25      := by wp_norm_lhs
          hx24      := by refine Eq.trans (by wp_norm_lhs) (by simp)
          hx23      := by wp_norm_lhs
          hx22      := by wp_norm_lhs
          hx21      := by wp_norm_lhs
          hx20      := by wp_norm_lhs
          hx19      := by wp_norm_lhs
          hx0       := by refine Eq.trans (by wp_norm_lhs) (by clear * -; bv_omega)
          hx1       := by refine Eq.trans (by wp_norm_lhs) (by simp)
          hx2       := by refine Eq.trans (by wp_norm_lhs) (by simp) }
    · have hbuf0 :
          (((((sp + 400#64) ↦₆₄ 0#64) ∗ (((sp + 400#64) + 8#64) ↦₆₄ 0#64)) ∗
             ((((sp + 400#64) + 16#64) ↦₆₄ 0#64) ∗ (((sp + 400#64) + 24#64) ↦₆₄ 0#64))) ∗
            (((((sp + 400#64) + 32#64) ↦₆₄ 0#64) ∗ (((sp + 400#64) + 40#64) ↦₆₄ 0#64)) ∗
             ((((sp + 400#64) + 48#64) ↦₆₄ 0#64) ∗ (((sp + 400#64) + 56#64) ↦₆₄ 0#64)))) ∗
           ((sp + 464#64) ↦₆₄ 0#64) ⊢
            memRegion (sp + 400#64) a.in0.length ∗
              (((sp + 400#64) + BitVec.ofNat 64 a.in0.length) ↦ₛ
                List.replicate (72 - a.in0.length) 0#8) := by
        rw [show sp + 464#64 = (sp + 400#64) + 64#64 by clear * -; bv_omega,
            zeroCells9_eq_replicate72 (sp + 400#64)]
        exact replicate72_entails_memcpy_split (sp + 400#64) a.in0.length hin0
      dsimp only [ZeroStateMem00, Keccak2SlicesRO]
      exact entails_sub hbuf0 (by sep_frame) (by sep_frame)

public section

/-- Combined prologue + `inLen < 72` branch + state zeroing (`[0x0000 → 0x05b4]`). -/
theorem prologue_to_05b4_ok [MlKemPlacement] (b : BitVec 64)
    (hb : MlKemBase blkPl00 b) (hbase : blkPl00.base = b)
    (a : Keccak2FixedArgs) (hin0 : a.in0.length < 72)
    (F : SepProp) (s0 : State)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s0.mem)
    (hro : MlKemRoOk mlkemMpl s0.mem)
    (hpc : s0.pc = b) (hrun : s0.status = .Running) (hsp0 : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = a.slicesPtr)
    (hx1 : s0.readReg64 .x1 = a.out0)
    (hx2 : s0.readReg64 .x2 = a.out1) :
    let sp := s0.sp - 720#64
    let rcBase := mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29"
    SepWP (blkPC00.rebase b (fun _ => none)) (b + 0x05b4#64) s0
      (Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
        stackAt s0.sp 720 ∗ F)
      (sepPost
        (fun sm => PreMemcpy0Regs sm sp rcBase a)
        (ZeroStateMem00 sp ∗
          memRegion (sp + 400#64) a.in0.length ∗
          (((sp + 400#64) + BitVec.ofNat 64 a.in0.length) ↦ₛ List.replicate (72 - a.in0.length) 0#8) ∗
          memRegion (sp + 472#64) 88 ∗
          SavedFrame00 s0.sp s0 ∗
          Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗ F)) := by
  intro sp rcBase
  refine sepWP_seq_env hcl hro
    (seg_0000_to_0540 b hb hbase a hin0 F s0 hpc hrun hsp0 hx0 hx1 hx2) ?_
  intro s1 P1 hpc1 _ _ _ hpost1
  rw [sepPost_apply] at hpost1
  rcases hpost1 with ⟨hregs1, hP1⟩
  refine SepWP.weaken_pre hP1 ?_
  exact seg_0540_to_05b4 b hb hbase a hin0 sp rcBase s0 s1 F hpc1 hregs1

end

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6.Prologue
