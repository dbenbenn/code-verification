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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Defs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31.Base
import ProofLib.GenPlacedFetches
import ProofLib.SepLogic.WPFrozen
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp
meta import ProofLib
meta import ProofLib.ProgramReflection
meta import ProofLib.GenDecodes
meta import ProofLib.GenPlacedFetches

/-!
# `B01` (`keccak2::<136, 31>`): prologue and absorb-invariant setup

Proof of segment `[0x0000 → 0x00a0]` of `mlkemBlk01`: spills callee-saved registers, allocates
the `1040`-byte stack frame, computes `in0.length / 136` via `UMULH`, zeroes the `400`-byte
2-way `KeccakState`, and branches to `+0x0434` (`in0.length < 136`) or `+0x00a4`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31.Prologue

open Arm64 Arm64.Obj ProofLib ProofLib.GenPlacedFetches SepProp
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
  mlkemMpl
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (keccakZeroState)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Defs (
  Keccak2Cap8Mem
  Keccak2Mem
  Keccak2Q0Mem
  Keccak2Q1Mem
  Keccak2Q2Mem
  Keccak2Q3Mem
  Keccak2Rate16Mem
  Keccak2Rate17Mem
  Keccak2Vec16Mem
  keccakZeroState_getD
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge (
  keccakAbsorbPrefix17
  memRegion128_cells
  umulh_div136_bv
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31.Base (
  SavedCalleeFrame
  blk01_code_eq
  blk01_tree_size
  blkLib01
  blkPC01
  blkPl01
  blkPlaceable01
  blkTree01
  memRegion160_cells
)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp

section
set_option linter.literalFetch false
gen_placed_fetches blkPC01 blkLib01 blkTree01 blk01_code_eq blk01_tree_size
  via_placement blkPl01 blkPlaceable01 [0x0000 → 0x00a0]
end

public section

/-- Sequence two `SepWP` segments while preserving `CodeLoaded` across `KeepsFrozen` transitions. -/
theorem sepWP_seq_cl {prog : Program} {mid target : BitVec 64} {s : State}
    {P : SepProp} {post1 post2 : State → SepProp → Prop} {mpl : MultiPlacement}
    (hcl : mlkemMultiLib.CodeLoaded mpl s.mem)
    (h1 : SepWP prog mid s P post1)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running →
      mlkemMultiLib.CodeLoaded mpl sm.mem → post1 sm Pm → SepWP prog target sm Pm post2) :
    SepWP prog target s P post2 :=
  SepWP.seq
    (SepWP.mono_frozen
      (post' := fun sm Pm => mlkemMultiLib.CodeLoaded mpl sm.mem ∧ post1 sm Pm)
      (Φ := fun m => mlkemMultiLib.CodeLoaded mpl m)
      (fun _ _ hc hkf => hc.of_keepsFrozen hkf)
      hcl h1
      (fun _ _ _ _ hc hp1 => ⟨hc, hp1⟩))
    (fun sm Pm hpc hrun ⟨hc, hp1⟩ => h2 sm Pm hpc hrun hc hp1)

/-- Live scalar registers at `+0x00a4` (loop head) and `+0x0434` (post-absorb tail entry). -/
structure PostAbsorbRegs (s s0 : State) (rcBase : BitVec 64) (a : Keccak2ShakeArgs) : Prop where
  hrun      : s.status = .Running
  hsp_align : s.spAligned = true
  hsp       : s.sp = s0.sp - 1040#64
  hx29      : s.readReg64 .x29 = s0.sp - 96#64
  hx27      : s.readReg64 .x27 = rcBase
  hx25      : s.readReg64 .x25 = BitVec.ofNat 64 (a.in0.length / 136)
  hx24      : s.readReg64 .x24 = a.slicesPtr
  hx23      : s.readReg64 .x23 = BitVec.ofNat 64 a.in0.length
  hx22      : s.readReg64 .x22 = a.out0
  hx21      : s.readReg64 .x21 = a.out1
  hx20      : s.readReg64 .x20 = BitVec.ofNat 64 a.outLen

/-- Spatial memory layout at `+0x00a4` (for block `k`) and `+0x0434` (`k = a.in0.length / 136`). -/
@[expose] def AbsorbInvMem (s0 : State) (rcBase : BitVec 64) (a : Keccak2ShakeArgs)
    (k : Nat) (F : SepProp) : SepProp :=
  let sp1 := s0.sp - 1040#64
  stackAt sp1 96 ∗
  memRegion sp1 8 ∗
  ((sp1 + 8#64) ↦₆₄ BitVec.ofNat 64 a.outLen) ∗
  memRegion (sp1 + 16#64) 176 ∗
  Keccak2Mem (sp1 + 192#64) (keccakAbsorbPrefix17 a.in0 k) (keccakAbsorbPrefix17 a.in1 k) ∗
  memRegion (sp1 + 592#64) 288 ∗
  SavedCalleeFrame s0.sp s0 ∗
  Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
  (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗
  (rcBase ↦ᵣ mlkemData01Bytes) ∗ F

theorem shift_mul136 (x : BitVec 64) : (x + (x <<< 4)) <<< 3 = x * 136#64 := by
  bv_bits

theorem ofNat_mul136 (k : Nat) :
    (BitVec.ofNat 64 k + (BitVec.ofNat 64 k <<< 4)) <<< 3 = BitVec.ofNat 64 (k * 136) :=
  (shift_mul136 _).trans (BitVec.ofNat_mul k 136).symm

theorem setPC_pc (s : State) (pc' : BitVec 64) : (s.setPC pc').pc = pc' := by
  cases s; rfl

theorem setPC_status {s : State} (pc' : BitVec 64) (h : s.status = .Running) :
    (s.setPC pc').status = .Running := by
  cases s; exact h

theorem setPC_sp {s : State} {v : BitVec 64} (pc' : BitVec 64) (h : s.sp = v) :
    (s.setPC pc').sp = v := by
  cases s; exact h

theorem setPC_spAligned {s : State} (pc' : BitVec 64) (h : s.spAligned = true) :
    (s.setPC pc').spAligned = true := by
  cases s; exact h

theorem setPC_readReg64 {s : State} {r : Reg} {v : BitVec 64} (pc' : BitVec 64)
    (h : s.readReg64 r = v) : (s.setPC pc').readReg64 r = v := by
  cases s; exact h

/-- View `memRegion ptr 400` in a `SepWP` precondition as fifty 64-bit cells matching `Keccak2Mem`. -/
theorem memRegion400_cells {prog : Program} {target_pc : BitVec 64} {s : State}
    {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (ptr : BitVec 64)
    (hf : P = memRegion ptr 400 ∗ F := by sep_focus)
    (h : ∀ c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15
           d0 d1 d2 d3 d4 d4' d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
           e0 e1
           f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : BitVec 64,
      SepWP prog target_pc s
        ((((((((ptr ↦₆₄ c0) ∗ ((ptr + 8#64) ↦₆₄ c1)) ∗
              (((ptr + 16#64) ↦₆₄ c2) ∗ ((ptr + 24#64) ↦₆₄ c3))) ∗
             ((((ptr + 32#64) ↦₆₄ c4) ∗ ((ptr + 40#64) ↦₆₄ c5)) ∗
              (((ptr + 48#64) ↦₆₄ c6) ∗ ((ptr + 56#64) ↦₆₄ c7)))) ∗
            (((((ptr + 64#64) ↦₆₄ c8) ∗ ((ptr + 72#64) ↦₆₄ c9)) ∗
              (((ptr + 80#64) ↦₆₄ c10) ∗ ((ptr + 88#64) ↦₆₄ c11))) ∗
             ((((ptr + 96#64) ↦₆₄ c12) ∗ ((ptr + 104#64) ↦₆₄ c13)) ∗
              (((ptr + 112#64) ↦₆₄ c14) ∗ ((ptr + 120#64) ↦₆₄ c15))))) ∗
           ((((((ptr + 128#64) ↦₆₄ d0) ∗ ((ptr + 136#64) ↦₆₄ d1)) ∗
               (((ptr + 144#64) ↦₆₄ d2) ∗ ((ptr + 152#64) ↦₆₄ d3))) ∗
              ((((ptr + 160#64) ↦₆₄ d4) ∗ ((ptr + 168#64) ↦₆₄ d4')) ∗
               (((ptr + 176#64) ↦₆₄ d6) ∗ ((ptr + 184#64) ↦₆₄ d7)))) ∗
             (((((ptr + 192#64) ↦₆₄ d8) ∗ ((ptr + 200#64) ↦₆₄ d9)) ∗
               (((ptr + 208#64) ↦₆₄ d10) ∗ ((ptr + 216#64) ↦₆₄ d11))) ∗
              ((((ptr + 224#64) ↦₆₄ d12) ∗ ((ptr + 232#64) ↦₆₄ d13)) ∗
               (((ptr + 240#64) ↦₆₄ d14) ∗ ((ptr + 248#64) ↦₆₄ d15)))))) ∗
          ((((ptr + 256#64) ↦₆₄ e0) ∗ ((ptr + 264#64) ↦₆₄ e1)) ∗
           ((((((ptr + 272#64) ↦₆₄ f0) ∗ ((ptr + 280#64) ↦₆₄ f1)) ∗
               (((ptr + 288#64) ↦₆₄ f2) ∗ ((ptr + 296#64) ↦₆₄ f3))) ∗
              ((((ptr + 304#64) ↦₆₄ f4) ∗ ((ptr + 312#64) ↦₆₄ f5)) ∗
               (((ptr + 320#64) ↦₆₄ f6) ∗ ((ptr + 328#64) ↦₆₄ f7)))) ∗
             (((((ptr + 336#64) ↦₆₄ f8) ∗ ((ptr + 344#64) ↦₆₄ f9)) ∗
               (((ptr + 352#64) ↦₆₄ f10) ∗ ((ptr + 360#64) ↦₆₄ f11))) ∗
              ((((ptr + 368#64) ↦₆₄ f12) ∗ ((ptr + 376#64) ↦₆₄ f13)) ∗
               (((ptr + 384#64) ↦₆₄ f14) ∗ ((ptr + 392#64) ↦₆₄ f15))))))) ∗ F) post oom) :
    SepWP prog target_pc s P post oom := by
  rw [hf,
      memRegion_split ptr 272 128 (by decide),
      memRegion_split ptr 256 16 (by decide),
      memRegion_split ptr 128 128 (by decide),
      memRegion_split (ptr + 256#64) 8 8 (by decide),
      show (ptr + 256#64) + 8#64 = ptr + 264#64 by bv_omega]
  refine memRegion128_cells ptr (by sep_focus)
    fun c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 => ?_
  refine memRegion128_cells (ptr + 128#64) (by sep_focus)
    fun d0 d1 d2 d3 d4 d4' d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 => ?_
  refine SepWP.memRegion8_cell (ptr + 256#64) fun e0 => ?_
  refine SepWP.memRegion8_cell (ptr + 264#64) fun e1 => ?_
  refine memRegion128_cells (ptr + 272#64) (by sep_focus)
    fun f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 => ?_
  have h1 := h c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15
    d0 d1 d2 d3 d4 d4' d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
    e0 e1
    f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
  have hf' (k : Nat) : (ptr + 272#64) + BitVec.ofNat 64 k = ptr + BitVec.ofNat 64 (272 + k) := by
    rw [BitVec.add_assoc, show (272#64 : BitVec 64) = BitVec.ofNat 64 272 from rfl, ← BitVec.ofNat_add]
  rw [hf' 8, hf' 16, hf' 24, hf' 32, hf' 40, hf' 48, hf' 56, hf' 64,
      hf' 72, hf' 80, hf' 88, hf' 96, hf' 104, hf' 112, hf' 120]
  exact SepWP.congr_pre (by sep_eq) h1

end

private theorem truncate64_eq_extractLsb (v : BitVec 128) :
    v.truncate 64 = v.extractLsb' 0 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi]

private theorem stack1136_prologue_split (sp0 : BitVec 64) :
    let sp1 := sp0 - 1040#64
    stackAt sp0 1136 =
      stackAt sp1 96 ∗
      memRegion sp1 8 ∗
      memRegion (sp1 + 8#64) 8 ∗
      memRegion (sp1 + 16#64) 176 ∗
      memRegion (sp1 + 192#64) 400 ∗
      memRegion (sp1 + 592#64) 288 ∗
      memRegion (sp0 - 160#64) 160 := by
  intro sp1
  unfold stackAt
  have hbase : sp0 - BitVec.ofNat 64 1136 = sp1 - BitVec.ofNat 64 96 := by
    dsimp [sp1]; bv_omega
  rw [hbase,
      memRegion_split (sp1 - BitVec.ofNat 64 96) 96 1040 (by decide),
      show (sp1 - BitVec.ofNat 64 96) + 96#64 = sp1 by dsimp [sp1]; bv_omega,
      memRegion_split sp1 8 1032 (by decide),
      memRegion_split (sp1 + 8#64) 8 1024 (by decide),
      show (sp1 + 8#64) + 8#64 = sp1 + 16#64 by bv_omega,
      memRegion_split (sp1 + 16#64) 176 848 (by decide),
      show (sp1 + 16#64) + 176#64 = sp1 + 192#64 by bv_omega,
      memRegion_split (sp1 + 192#64) 400 448 (by decide),
      show (sp1 + 192#64) + 400#64 = sp1 + 592#64 by bv_omega,
      memRegion_split (sp1 + 592#64) 288 160 (by decide),
      show (sp1 + 592#64) + 288#64 = sp0 - 160#64 by dsimp [sp1]; bv_omega]

private theorem umulh_div136_eval {n : Nat} (hn : n < 2 ^ 32) :
    BitVec.truncate 64
      ((BitVec.zeroExtend 128 (BitVec.ofNat 64 n) * 0xf0f0f0f0f0f0f0f1#128) >>> 64) >>> 7 =
      BitVec.ofNat 64 (n / 136) := by
  rw [← umulh_div136_bv hn]
  apply BitVec.eq_of_toNat_eq
  have hn64 : n < 2 ^ 64 := Nat.lt_trans hn (by decide)
  have hn128 : n < 2 ^ 128 := Nat.lt_trans hn (by decide)
  have h128 : (BitVec.zeroExtend 128 (BitVec.ofNat 64 n)).toNat = n := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64, Nat.mod_eq_of_lt hn128]
  have hc : (0xf0f0f0f0f0f0f0f1#128).toNat = 0xf0f0f0f0f0f0f0f1 := rfl
  have hc64 : (0xf0f0f0f0f0f0f0f1#64).toNat = 0xf0f0f0f0f0f0f0f1 := rfl
  have hmul : n * 0xf0f0f0f0f0f0f0f1 < 2 ^ 128 :=
    Nat.lt_trans (Nat.mul_lt_mul_of_pos_right hn (by decide)) (by decide)
  have hdiv : n * 0xf0f0f0f0f0f0f0f1 / 2 ^ 64 < 2 ^ 64 :=
    Nat.lt_of_le_of_lt
      (Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.le_of_lt hn)))
      (by decide)
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
      BitVec.toNat_mul, h128, hc, Nat.mod_eq_of_lt hmul,
      Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt hdiv, BitVec.toNat_ushiftRight, hc64, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hdiv, Nat.shiftRight_eq_div_pow]

private theorem spAligned_of_sp_val {st : State} {v : BitVec 64}
    (h2 : (v &&& 15#64 == 0#64) = true) (h1 : st.sp = v) : st.spAligned = true := by
  rw [State.spAligned, h1]
  exact h2

private theorem spAligned_of_sp_eq {s1 s2 : State} {v : BitVec 64}
    (ha : s2.spAligned = true) (h2 : s2.sp = v) (h1 : s1.sp = v) : s1.spAligned = true := by
  rw [State.spAligned, h1, ← h2, ← State.spAligned]
  exact ha

private theorem eq_trans_rhs {α : Type} {x y z : α} (hyz : y = z) (hxy : x = y) : x = z :=
  hxy.trans hyz

/-- Step `[0x0000 → 0x0030]`: spill callee-saved registers and allocate 880-byte local frame. -/
private theorem prologue_save [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl01 b) (_hbase : blkPl01.base = b)
    (s0 : State) (F : SepProp)
    (hpc : s0.pc = b) (hrun : s0.status = .Running) (hsp0 : s0.spAligned = true) :
    SepWP (blkPC01.rebase b (fun _ => none)) (b + 0x0030#64) s0
      (memRegion (s0.sp - 160#64) 160 ∗ F)
      (fun s1 Q1 =>
        s1.sp = s0.sp - 1040#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .x29 = s0.sp - 96#64 ∧
        s1.readReg64 .x0 = s0.readReg64 .x0 ∧
        s1.readReg64 .x1 = s0.readReg64 .x1 ∧
        s1.readReg64 .x2 = s0.readReg64 .x2 ∧
        s1.readReg64 .x3 = s0.readReg64 .x3 ∧
        s1.readReg64 .x4 = s0.readReg64 .x4 ∧
        (Q1 ⊢ SavedCalleeFrame s0.sp s0 ∗ F)) := by
  have hsp1040 : ((s0.sp - 1040#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 1040#64 hsp0 (by decide)
  refine memRegion160_cells (s0.sp - 160#64) (by sep_focus)
    fun _w0 _w1 _w2 _w3 _w4 _w5 _w6 _w7 _w8 _w9 _w10 _w11 _w12 _w13 _w14 _w15 _w16 _w17 _w18 _w19 => ?_
  wp_steps
  apply SepWP.done
  · wp_norm_lhs
  · wp_norm_lhs
  · refine ⟨by wp_norm_lhs,
      spAligned_of_sp_val hsp1040 (by wp_norm_lhs),
      by wp_norm_lhs,
      by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, ?_⟩
    unfold SavedCalleeFrame
    simp only [truncate64_eq_extractLsb]
    sep_entail

/-- Step `[0x0030 → if a.in0.length < 136 then +0x0434 else +0x00a4]`: zero state and check `inLen < 136`. -/
private theorem prologue_init [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl01 b) (_hbase : blkPl01.base = b)
    (a : Keccak2ShakeArgs) (hin0 : a.in0.length < 2 ^ 32)
    (s0 s : State) (sp1 : BitVec 64) (F : SepProp)
    (hpc : s.pc = b + 0x0030#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp1) (hsp_align : s.spAligned = true)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx0 : s.readReg64 .x0 = a.slicesPtr)
    (hx1 : s.readReg64 .x1 = a.out0)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 a.outLen)
    (hx3 : s.readReg64 .x3 = a.out1)
    (hx4 : s.readReg64 .x4 = BitVec.ofNat 64 a.outLen) :
    let rcBase := mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29"
    SepWP (blkPC01.rebase b (fun _ => none))
      (if a.in0.length < 136 then b + 0x0434#64 else b + 0x00a4#64) s
      (memRegion (sp1 + 8#64) 8 ∗
        memRegion (sp1 + 192#64) 400 ∗
        Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗ F)
      (fun sm Qm =>
        (sp1 = s0.sp - 1040#64 → PostAbsorbRegs sm s0 rcBase a) ∧
        (¬(a.in0.length < 136) → sm.readReg64 .x26 = 0#64) ∧
        (Qm ⊢ ((sp1 + 8#64) ↦₆₄ BitVec.ofNat 64 a.outLen) ∗
          Keccak2Mem (sp1 + 192#64) keccakZeroState keccakZeroState ∗
          Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗ F)) := by
  intro rcBase
  refine SepWP.memRegion8_cell (sp1 + 8#64) fun _u0 => ?_
  refine memRegion400_cells (sp1 + 192#64) (by sep_focus)
    fun _c0 _c1 _c2 _c3 _c4 _c5 _c6 _c7 _c8 _c9 _c10 _c11 _c12 _c13 _c14 _c15
        _d0 _d1 _d2 _d3 _d4 _d5 _d6 _d7 _d8 _d9 _d10 _d11 _d12 _d13 _d14 _d15
        _e0 _e1
        _f0 _f1 _f2 _f3 _f4 _f5 _f6 _f7 _f8 _f9 _f10 _f11 _f12 _f13 _f14 _f15 => ?_
  unfold Keccak2SlicesRO
  wp_steps
  wp_if hbr
  · have hlt : a.in0.length < 136 := by
      simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : a.in0.length < 2 ^ 64)] at hbr
      exact hbr
    simp only [hlt, ↓reduceIte]
    apply SepWP.done
    · wp_norm_lhs
    · wp_norm_lhs
    · refine ⟨fun hsp1_eq => ?_, fun h => False.elim (h trivial), ?_⟩
      · exact
          { hrun      := by wp_norm_lhs
            hsp_align := spAligned_of_sp_eq hsp_align (hsp.trans hsp1_eq) (by wp_norm_lhs)
            hsp       := by wp_norm_lhs
            hx29      := by wp_norm_lhs
            hx27      := by wp_norm_lhs
            hx25      := eq_trans_rhs (umulh_div136_eval hin0) (by wp_norm_lhs)
            hx24      := by wp_norm_lhs
            hx23      := by wp_norm_lhs
            hx22      := by wp_norm_lhs
            hx21      := by wp_norm_lhs
            hx20      := by wp_norm_lhs }
      · unfold Keccak2Mem Keccak2Rate17Mem Keccak2Rate16Mem
          Keccak2Q0Mem Keccak2Q1Mem Keccak2Q2Mem Keccak2Q3Mem Keccak2Vec16Mem Keccak2Cap8Mem
        simp only [keccakZeroState_getD]
        sep_entail
  · have hnlt : ¬(a.in0.length < 136) := by
      intro hlt
      apply hbr
      simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : a.in0.length < 2 ^ 64)]
      exact hlt
    simp only [hnlt, ↓reduceIte]
    wp_steps
    apply SepWP.done
    · wp_norm_lhs
    · wp_norm_lhs
    · refine ⟨fun hsp1_eq => ?_, fun _ => by wp_norm_lhs, ?_⟩
      · exact
          { hrun      := by wp_norm_lhs
            hsp_align := spAligned_of_sp_eq hsp_align (hsp.trans hsp1_eq) (by wp_norm_lhs)
            hsp       := by wp_norm_lhs
            hx29      := by wp_norm_lhs
            hx27      := by wp_norm_lhs
            hx25      := eq_trans_rhs (umulh_div136_eval hin0) (by wp_norm_lhs)
            hx24      := by wp_norm_lhs
            hx23      := by wp_norm_lhs
            hx22      := by wp_norm_lhs
            hx21      := by wp_norm_lhs
            hx20      := by wp_norm_lhs }
      · unfold Keccak2Mem Keccak2Rate17Mem Keccak2Rate16Mem
          Keccak2Q0Mem Keccak2Q1Mem Keccak2Q2Mem Keccak2Q3Mem Keccak2Vec16Mem Keccak2Cap8Mem
        simp only [keccakZeroState_getD]
        sep_entail

attribute [local irreducible] Keccak2Mem Keccak2SlicesRO SavedCalleeFrame

public section

/-- Prologue `[0x0000 → if a.in0.length < 136 then +0x0434 else +0x00a4]` establishing `AbsorbInvMem ... 0`. -/
theorem prologue_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl01 b) (hbase : blkPl01.base = b)
    (a : Keccak2ShakeArgs) (hin0 : a.in0.length < 2 ^ 32)
    (s0 : State) (F : SepProp)
    (hcl0 : mlkemMultiLib.CodeLoaded mlkemMpl s0.mem)
    (hpc : s0.pc = b) (hrun : s0.status = .Running) (hsp0 : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = a.slicesPtr)
    (hx1 : s0.readReg64 .x1 = a.out0)
    (hx2 : s0.readReg64 .x2 = BitVec.ofNat 64 a.outLen)
    (hx3 : s0.readReg64 .x3 = a.out1)
    (hx4 : s0.readReg64 .x4 = BitVec.ofNat 64 a.outLen) :
    let rcBase := mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29"
    SepWP (blkPC01.rebase b (fun _ => none))
      (if a.in0.length < 136 then b + 0x0434#64 else b + 0x00a4#64) s0
      (Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
        (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗
        stackAt s0.sp 1136 ∗
        (rcBase ↦ᵣ mlkemData01Bytes) ∗ F)
      (fun sm Qm =>
        PostAbsorbRegs sm s0 rcBase a ∧
        (¬(a.in0.length < 136) → sm.readReg64 .x26 = 0#64) ∧
        (Qm ⊢ AbsorbInvMem s0 rcBase a 0 F)) := by
  intro rcBase
  rw [stack1136_prologue_split s0.sp]
  let sp1 := s0.sp - 1040#64
  refine SepWP.weaken_pre
    (show _ ⊢ memRegion (s0.sp - 160#64) 160 ∗
      (memRegion (sp1 + 8#64) 8 ∗ memRegion (sp1 + 192#64) 400 ∗
        Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
        (stackAt sp1 96 ∗ memRegion sp1 8 ∗ memRegion (sp1 + 16#64) 176 ∗
          memRegion (sp1 + 592#64) 288 ∗
          (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗ (rcBase ↦ᵣ mlkemData01Bytes) ∗ F)) by
      dsimp only [sp1]; sep_frame) ?_
  refine sepWP_seq_cl hcl0 (prologue_save hb hbase s0 _ hpc hrun hsp0)
    fun s1 Q1 hpc1 hrun1 _hcl1 ⟨hsp1, hal1, hx29_1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hQ1⟩ => ?_
  refine SepWP.weaken_pre hQ1 ?_
  refine SepWP.weaken_pre
    (show SavedCalleeFrame s0.sp s0 ∗ _ ⊢
      memRegion (sp1 + 8#64) 8 ∗ memRegion (sp1 + 192#64) 400 ∗
        Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
        (stackAt sp1 96 ∗ memRegion sp1 8 ∗ memRegion (sp1 + 16#64) 176 ∗
          memRegion (sp1 + 592#64) 288 ∗ SavedCalleeFrame s0.sp s0 ∗
          (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗ (rcBase ↦ᵣ mlkemData01Bytes) ∗ F) by
      sep_frame) ?_
  refine SepWP.mono
    (prologue_init hb hbase a hin0 s0 s1 sp1 _ hpc1 hrun1 hsp1 hal1 hx29_1
      (hx0_1.trans hx0) (hx1_1.trans hx1) (hx2_1.trans hx2) (hx3_1.trans hx3) (hx4_1.trans hx4))
    fun sm Qm _ _ ⟨hr_m, hx26_m, hQ_m⟩ => ⟨hr_m rfl, hx26_m, ?_⟩
  unfold AbsorbInvMem
  dsimp only [keccakAbsorbPrefix17, sp1]
  exact Entails.trans hQ_m (by sep_frame)

end

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31.Prologue
