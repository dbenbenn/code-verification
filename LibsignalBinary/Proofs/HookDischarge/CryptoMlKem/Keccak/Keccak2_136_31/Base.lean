/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.GenPlacedFetches
public import ProofLib.ProgramReflection
public import LibsignalBinary.Proofs.HookDischarge.RustStd.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Defs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Round -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge -- proof-setup: allow-public-import
public meta import ProofLib.ProgramReflection
public meta import ProofLib.GenDecodes
public meta import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp

/-!
# `B01` (`keccak2::<136, 31>`): shared setup and folding lemmas

Shared definitions and helper lemmas for `mlkemBlk01` (`601` words):
- `PlacedLib` and `WordTree` setup (`blkLib01`, `blkTree01`, `blk01_code_eq`, `blk01_tree_size`).
- Segment sequencing (`sepWP_seq_env`), `.rodata` round-constant load (`step_ld1r_keccakRc_ro`),
  vector-spine rewrite (`writeVReg128_eq_self`), and sub-entailment (`entails_sub`).
- Callee-saved spill frame (`SavedCalleeFrame`, `160` bytes) and 11-slot SIMD spill layout
  (`Spill11`, `176` bytes at `sp1 + 16 .. sp1 + 192`).
- Stack pad-buffer helpers (`zero17_eq_replicate136`, `replicate136_entails_split`,
  `readLE_write8_135_lt`, `xor_packLane_left`, `xor_packLane_right`).
- `Theta`, `RhoPi`, and `ChiIota` algebraic folding lemmas shared by `Permute1` and `Permute2`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31.Base

open Arm64 Arm64.Obj ProofLib SepProp
open scoped ProofLib.ProgramReflection
open ProofLib.ProgramReflection (WordTree)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (RoDataAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (
  mlkemData01Bytes
  mlkemMultiLib
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (
  MlKemRoOk
  keccakRcAt
  mlkemData01Bytes_length
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps (step_simdLd1r_2d)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  KeccakState
  keccakF1600Round
  keccakRhoOffset
  packLane64
  unpackLane64
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Defs (
  keccakXorRate17
  keccakXorRate17_getD_lt
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp (
  extractLsb_hi_append
  extractLsb_lo_append
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Round (
  keccakC
  keccakD
  keccakF1600Round_getD
  keccakRhoPi
  keccakRhoPiSrc
  keccakRoundLane
  keccakTheta
  rotateLeft_zero_64
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge (
  memRegion128_cells
  memRegion32_cells
  pointsTo64_16_eq_bytes
  pointsTo64_eq_unpackLane64
  readLE_8_eq_packLane64
)

/-! ## Block 01 (`keccak2::<136, 31>`) `PlacedLib` and `WordTree` setup -/

@[expose] def blkLib01 : PlacedLib := mlkemMultiLib.blockLib 1
@[expose] def blkPl01 [MlKemPlacement] : Placement := mlkemMultiLib.blockPlacement mlkemMpl 1
theorem blkPlaceable01 [MlKemPlacement] : blkLib01.Placeable blkPl01 :=
  mlkemMultiLib.placeable_blockLib (by decide) MlKemPlacement.placeable
@[expose] def blkPC01 [MlKemPlacement] : Program := blkLib01.program blkPl01
@[expose] def blkProg01 : Program := { code := blkLib01.text.code, symbols := blkLib01.text.symbols }
@[expose] def blkTree01 : WordTree := word_tree_of% blkProg01
theorem blk01_code_eq : blkLib01.text.code = blkTree01.toBytes := by rfl_kernel
theorem blk01_tree_size : blkTree01.checkSize? = some 601 := by rfl_kernel

abbrev blkProg01R [MlKemPlacement] (b : BitVec 64) : Program :=
  blkPC01.rebase b (fun _ => none)

@[simp, arm64_norm, wp_norm]
theorem blkPl01_ρ [MlKemPlacement] (sym : String) :
    blkPl01.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

/-! ## Segment sequencing, `.rodata` `LD1R`, and sub-entailment combinators -/

/-- Sequence two `SepWP` segments while preserving `CodeLoaded` and `MlKemRoOk` across
    `KeepsFrozen` transitions. -/
theorem sepWP_seq_env {prog : Program} {mid target : BitVec 64} {s : State}
    {P : SepProp} {post1 post2 : State → SepProp → Prop} {mpl : MultiPlacement}
    (hcl : mlkemMultiLib.CodeLoaded mpl s.mem)
    (hro : MlKemRoOk mpl s.mem)
    (h1 : SepWP prog mid s P post1)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running →
      mlkemMultiLib.CodeLoaded mpl sm.mem → MlKemRoOk mpl sm.mem →
      post1 sm Pm → SepWP prog target sm Pm post2) :
    SepWP prog target s P post2 :=
  SepWP.seq
    (SepWP.mono_frozen
      (post' := fun sm Pm =>
        mlkemMultiLib.CodeLoaded mpl sm.mem ∧ MlKemRoOk mpl sm.mem ∧ post1 sm Pm)
      (Φ := fun m => mlkemMultiLib.CodeLoaded mpl m ∧ MlKemRoOk mpl m)
      (fun _ _ ⟨hc, hr⟩ hkf => ⟨hc.of_keepsFrozen hkf, hr.of_keepsFrozen hkf⟩)
      ⟨hcl, hro⟩ h1
      (fun _ _ _ _ ⟨hc, hr⟩ hp1 => ⟨hc, hr, hp1⟩))
    (fun sm Pm hpc hrun ⟨hc, hr, hp1⟩ => h2 sm Pm hpc hrun hc hr hp1)

/-- Rewrite a sub-entailment `A ⊢ B` inside `P ⊢ Q`. -/
theorem entails_sub {A B P Rest Q : SepProp}
    (hAB : A ⊢ B) (h1 : P ⊢ A ∗ Rest) (h2 : B ∗ Rest ⊢ Q) : P ⊢ Q :=
  Entails.trans h1 (Entails.trans (sepConj_mono_left hAB) h2)

/-- Step `LD1R {Vt.2D}, [Xn]` reading `keccakRcAt r` (`r < 24`) directly from a pure
    `RoDataAt s.mem rcBase mlkemData01Bytes` hypothesis without adding `.rodata` atoms to `P`. -/
theorem step_ld1r_keccakRc_ro {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc rcBase : BitVec 64} {rn : Reg} {rm vt : BitVec 5} (r : Nat)
    (hr : r < 24)
    (hro : RoDataAt s.mem rcBase mlkemData01Bytes)
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.simdLd1r true 0x3#2 rn false rm vt))
    (hsp : checkRegSPAligned s rn = true)
    (hea : rcBase + BitVec.ofNat 64 (8 * r) = s.readReg64 rn)
    (hexec : (s.writeVReg128 vt (keccakRcAt r ++ keccakRcAt r)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom := by
  unfold SepWP at hnext ⊢
  intro R hm
  have hm_ro : s.mem ⊨ (rcBase ↦ᵣ mlkemData01Bytes) ∗ (P ∗ R) :=
    Satisfies.rodata_intro hro.1 hro.2 (by rw [mlkemData01Bytes_length]; decide) hm
  have hload : SepLoad64 (s.readReg64 rn) (rcBase ↦ᵣ mlkemData01Bytes) (keccakRcAt r) :=
    SepLoad64.of_pointsToBytes_readLE_RO (F := emp) (by rw [sepConj_emp])
      (by rw [mlkemData01Bytes_length]; omega) hea
  have hs'_pc : s'.pc = pc + 4#64 := by rw [← hexec]; rfl
  have hs'_run : s'.status = .Running := by rw [← hexec]; exact hrun
  have hs'_mem : s'.mem = s.mem := by rw [← hexec]; rfl
  have h1 := SepWP.reaches_of_sepWP
    (step_simdLd1r_2d (prog := prog) (target_pc := pc + 4#64)
      (P := rcBase ↦ᵣ mlkemData01Bytes) (post := fun sf _ => sf = s')
      hpc hrun hfetch hsp rfl hload hexec
      (SepWP.done hs'_pc hs'_run rfl))
    hm_ro
  exact reaches_pc_seq h1 fun sm _ _ hsm => hsm ▸ hnext R (hs'_mem ▸ hm)

/-- Materialize a known 128-bit vector register equality onto a `State.writeVReg128` spine. -/
theorem writeVReg128_eq_self {s : State} {idx : BitVec 5} {val : BitVec 128}
    (h : s.readVReg128 idx = val) :
    s.writeVReg128 idx val = s := by
  cases s with
  | mk _ vregs =>
    cases vregs
    dsimp only [State.writeVReg128, State.readVReg128, VRegFile.write, VRegFile.read] at h ⊢
    congr 2
    funext i
    by_cases hi : i = idx
    · subst hi; simp [h]
    · simp [hi]

/-! ## Callee-saved spill frame (`160` bytes) and 11-slot SIMD spill layout (`176` bytes) -/

private theorem pair64_entails_memRegion16 (a v0 v1 : BitVec 64) :
    ((a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1)) ⊢ memRegion a 16 := by
  rw [memRegion_split a 8 8 (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion a v0)
    (pointsTo64_entails_memRegion (a + 8#64) v1)

private theorem quad64_entails_memRegion32 (base : BitVec 64) (off : Nat)
    (v0 v1 v2 v3 : BitVec 64) :
    (((base + BitVec.ofNat 64 off) ↦₆₄ v0) ∗
     ((base + BitVec.ofNat 64 (off + 8)) ↦₆₄ v1)) ∗
    (((base + BitVec.ofNat 64 (off + 16)) ↦₆₄ v2) ∗
     ((base + BitVec.ofNat 64 (off + 24)) ↦₆₄ v3)) ⊢
      memRegion (base + BitVec.ofNat 64 off) 32 := by
  let a := base + BitVec.ofNat 64 off
  have hk (k : Nat) : base + BitVec.ofNat 64 (off + k) = a + BitVec.ofNat 64 k := by
    dsimp [a]; rw [BitVec.ofNat_add]; bv_omega
  rw [hk 8, hk 16, hk 24]
  change (((a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1)) ∗
          (((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3))) ⊢ memRegion a 32
  rw [show a + 24#64 = (a + 16#64) + 8#64 by bv_omega,
      memRegion_split a 16 16 (by decide)]
  exact sepConj_mono (pair64_entails_memRegion16 a v0 v1)
    (pair64_entails_memRegion16 (a + 16#64) v2 v3)

/-- Spilled callee-saved registers (`d8..d15`, `x19..x28`, `x29`, `x30`) at `[sp0 - 160, sp0)`. -/
@[expose] def SavedCalleeFrame (sp0 : BitVec 64) (s0 : State) : SepProp :=
  let spm := sp0 - 160#64
  (((((spm ↦₆₄ (s0.readVReg128 15#5).extractLsb' 0 64) ∗
      ((spm + 8#64) ↦₆₄ (s0.readVReg128 14#5).extractLsb' 0 64)) ∗
     (((spm + 16#64) ↦₆₄ (s0.readVReg128 13#5).extractLsb' 0 64) ∗
      ((spm + 24#64) ↦₆₄ (s0.readVReg128 12#5).extractLsb' 0 64))) ∗
    ((((spm + 32#64) ↦₆₄ (s0.readVReg128 11#5).extractLsb' 0 64) ∗
      ((spm + 40#64) ↦₆₄ (s0.readVReg128 10#5).extractLsb' 0 64)) ∗
     (((spm + 48#64) ↦₆₄ (s0.readVReg128 9#5).extractLsb' 0 64) ∗
      ((spm + 56#64) ↦₆₄ (s0.readVReg128 8#5).extractLsb' 0 64)))) ∗
   (((((spm + 64#64) ↦₆₄ s0.readReg64 .fp) ∗
      ((spm + 72#64) ↦₆₄ s0.readReg64 .lr)) ∗
     (((spm + 80#64) ↦₆₄ s0.readReg64 .x28) ∗
      ((spm + 88#64) ↦₆₄ s0.readReg64 .x27))) ∗
    ((((spm + 96#64) ↦₆₄ s0.readReg64 .x26) ∗
      ((spm + 104#64) ↦₆₄ s0.readReg64 .x25)) ∗
     (((spm + 112#64) ↦₆₄ s0.readReg64 .x24) ∗
      ((spm + 120#64) ↦₆₄ s0.readReg64 .x23))))) ∗
  ((((spm + 128#64) ↦₆₄ s0.readReg64 .x22) ∗
    ((spm + 136#64) ↦₆₄ s0.readReg64 .x21)) ∗
   (((spm + 144#64) ↦₆₄ s0.readReg64 .x20) ∗
    ((spm + 152#64) ↦₆₄ s0.readReg64 .x19)))

theorem savedCalleeFrame_entails_memRegion160 (sp0 : BitVec 64) (s0 : State) :
    SavedCalleeFrame sp0 s0 ⊢ memRegion (sp0 - 160#64) 160 := by
  unfold SavedCalleeFrame
  let spm := sp0 - 160#64
  have h0 : (((spm ↦₆₄ (s0.readVReg128 15#5).extractLsb' 0 64) ∗
      ((spm + 8#64) ↦₆₄ (s0.readVReg128 14#5).extractLsb' 0 64)) ∗
     (((spm + 16#64) ↦₆₄ (s0.readVReg128 13#5).extractLsb' 0 64) ∗
      ((spm + 24#64) ↦₆₄ (s0.readVReg128 12#5).extractLsb' 0 64))) ⊢ memRegion spm 32 := by
    simpa [spm] using quad64_entails_memRegion32 spm 0
      ((s0.readVReg128 15#5).extractLsb' 0 64) ((s0.readVReg128 14#5).extractLsb' 0 64)
      ((s0.readVReg128 13#5).extractLsb' 0 64) ((s0.readVReg128 12#5).extractLsb' 0 64)
  rw [memRegion_split spm 128 32 (by decide),
      memRegion_split spm 64 64 (by decide),
      memRegion_split spm 32 32 (by decide),
      memRegion_split (spm + 64#64) 32 32 (by decide),
      show (spm + 64#64) + 32#64 = spm + 96#64 by bv_omega]
  exact sepConj_mono
    (sepConj_mono
      (sepConj_mono h0 (quad64_entails_memRegion32 spm 32 _ _ _ _))
      (sepConj_mono (quad64_entails_memRegion32 spm 64 _ _ _ _)
        (quad64_entails_memRegion32 spm 96 _ _ _ _)))
    (quad64_entails_memRegion32 spm 128 _ _ _ _)

/-- View `memRegion a 160` in a `SepWP` precondition as twenty 64-bit cells (`a .. a + 152`). -/
theorem memRegion160_cells {prog : Program} {target_pc : BitVec 64} {s : State}
    {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (a : BitVec 64)
    (hf : P = memRegion a 160 ∗ F := by sep_focus)
    (h : ∀ w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : BitVec 64,
      SepWP prog target_pc s
        (((((((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1)) ∗
             (((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3))) ∗
            ((((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5)) ∗
             (((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7)))) ∗
           (((((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9)) ∗
             (((a + 80#64) ↦₆₄ w10) ∗ ((a + 88#64) ↦₆₄ w11))) ∗
            ((((a + 96#64) ↦₆₄ w12) ∗ ((a + 104#64) ↦₆₄ w13)) ∗
             (((a + 112#64) ↦₆₄ w14) ∗ ((a + 120#64) ↦₆₄ w15))))) ∗
          ((((a + 128#64) ↦₆₄ w16) ∗ ((a + 136#64) ↦₆₄ w17)) ∗
           (((a + 144#64) ↦₆₄ w18) ∗ ((a + 152#64) ↦₆₄ w19)))) ∗ F) post oom) :
    SepWP prog target_pc s P post oom := by
  rw [hf, memRegion_split a 128 32 (by decide)]
  refine memRegion128_cells a (by sep_focus)
    fun w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 => ?_
  refine memRegion32_cells (a + 128#64) (by sep_focus) fun w16 w17 w18 w19 => ?_
  rw [show (a + 128#64) + 8#64 = a + 136#64 by bv_omega,
      show (a + 128#64) + 16#64 = a + 144#64 by bv_omega,
      show (a + 128#64) + 24#64 = a + 152#64 by bv_omega]
  exact SepWP.congr_pre (by sep_eq)
    (h w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19)

/-- Balanced 11-slot (`176`-byte) SIMD spill area at `[sp1 + 16, sp1 + 192)`. -/
@[expose] def Spill11 (sp1 : BitVec 64)
    (s16 s32 s48 s64 s80 s96 s112 s128 s144 s160 s176 : BitVec 128) : SepProp :=
  (((((sp1 + 16#64) ↦₆₄ s16.extractLsb' 0 64) ∗ ((sp1 + 24#64) ↦₆₄ s16.extractLsb' 64 64)) ∗
    (((sp1 + 32#64) ↦₆₄ s32.extractLsb' 0 64) ∗ ((sp1 + 40#64) ↦₆₄ s32.extractLsb' 64 64))) ∗
   ((((sp1 + 48#64) ↦₆₄ s48.extractLsb' 0 64) ∗ ((sp1 + 56#64) ↦₆₄ s48.extractLsb' 64 64)) ∗
    (((sp1 + 64#64) ↦₆₄ s64.extractLsb' 0 64) ∗ ((sp1 + 72#64) ↦₆₄ s64.extractLsb' 64 64)))) ∗
  ((((((sp1 + 80#64) ↦₆₄ s80.extractLsb' 0 64) ∗ ((sp1 + 88#64) ↦₆₄ s80.extractLsb' 64 64)) ∗
     (((sp1 + 96#64) ↦₆₄ s96.extractLsb' 0 64) ∗ ((sp1 + 104#64) ↦₆₄ s96.extractLsb' 64 64))) ∗
    ((((sp1 + 112#64) ↦₆₄ s112.extractLsb' 0 64) ∗ ((sp1 + 120#64) ↦₆₄ s112.extractLsb' 64 64)) ∗
     (((sp1 + 128#64) ↦₆₄ s128.extractLsb' 0 64) ∗ ((sp1 + 136#64) ↦₆₄ s128.extractLsb' 64 64)))) ∗
   ((((sp1 + 144#64) ↦₆₄ s144.extractLsb' 0 64) ∗ ((sp1 + 152#64) ↦₆₄ s144.extractLsb' 64 64)) ∗
    ((((sp1 + 160#64) ↦₆₄ s160.extractLsb' 0 64) ∗ ((sp1 + 168#64) ↦₆₄ s160.extractLsb' 64 64)) ∗
     (((sp1 + 176#64) ↦₆₄ s176.extractLsb' 0 64) ∗ ((sp1 + 184#64) ↦₆₄ s176.extractLsb' 64 64)))))

theorem spill11_entails_memRegion176 (sp1 : BitVec 64)
    (s16 s32 s48 s64 s80 s96 s112 s128 s144 s160 s176 : BitVec 128) :
    Spill11 sp1 s16 s32 s48 s64 s80 s96 s112 s128 s144 s160 s176 ⊢
      memRegion (sp1 + 16#64) 176 := by
  unfold Spill11
  have hp144 :
      ((sp1 + 144#64) ↦₆₄ s144.extractLsb' 0 64) ∗ ((sp1 + 152#64) ↦₆₄ s144.extractLsb' 64 64) ⊢
        memRegion (sp1 + 144#64) 16 := by
    rw [show sp1 + 152#64 = (sp1 + 144#64) + 8#64 by bv_omega]
    exact pair64_entails_memRegion16 (sp1 + 144#64) _ _
  rw [memRegion_split (sp1 + 16#64) 64 112 (by decide),
      memRegion_split (sp1 + 16#64) 32 32 (by decide),
      show (sp1 + 16#64) + 32#64 = sp1 + 48#64 by bv_omega,
      show (sp1 + 16#64) + 64#64 = sp1 + 80#64 by bv_omega,
      memRegion_split (sp1 + 80#64) 64 48 (by decide),
      memRegion_split (sp1 + 80#64) 32 32 (by decide),
      show (sp1 + 80#64) + 32#64 = sp1 + 112#64 by bv_omega,
      show (sp1 + 80#64) + 64#64 = sp1 + 144#64 by bv_omega,
      memRegion_split (sp1 + 144#64) 16 32 (by decide),
      show (sp1 + 144#64) + 16#64 = sp1 + 160#64 by bv_omega]
  exact sepConj_mono
    (sepConj_mono
      (quad64_entails_memRegion32 sp1 16 _ _ _ _)
      (quad64_entails_memRegion32 sp1 48 _ _ _ _))
    (sepConj_mono
      (sepConj_mono
        (quad64_entails_memRegion32 sp1 80 _ _ _ _)
        (quad64_entails_memRegion32 sp1 112 _ _ _ _))
      (sepConj_mono hp144 (quad64_entails_memRegion32 sp1 160 _ _ _ _)))

/-- View `memRegion (sp1 + 16#64) 176` in a `SepWP` precondition as `Spill11 sp1 s16 .. s176`. -/
theorem memRegion176_to_spill11 {prog : Program} {target_pc : BitVec 64} {s : State}
    {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (sp1 : BitVec 64)
    (hf : P = memRegion (sp1 + 16#64) 176 ∗ F := by sep_focus)
    (h : ∀ s16 s32 s48 s64 s80 s96 s112 s128 s144 s160 s176 : BitVec 128,
      SepWP prog target_pc s
        (Spill11 sp1 s16 s32 s48 s64 s80 s96 s112 s128 s144 s160 s176 ∗ F) post oom) :
    SepWP prog target_pc s P post oom := by
  rw [hf,
      memRegion_split (sp1 + 16#64) 128 48 (by decide),
      show (sp1 + 16#64) + 128#64 = sp1 + 144#64 by bv_omega,
      memRegion_split (sp1 + 144#64) 16 32 (by decide),
      show (sp1 + 144#64) + 16#64 = sp1 + 160#64 by bv_omega,
      memRegion_split (sp1 + 144#64) 8 8 (by decide),
      show (sp1 + 144#64) + 8#64 = sp1 + 152#64 by bv_omega]
  refine memRegion128_cells (sp1 + 16#64) (by sep_focus)
    fun w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 => ?_
  refine SepWP.memRegion8_cell (sp1 + 144#64) fun w16 => ?_
  refine SepWP.memRegion8_cell (sp1 + 152#64) fun w17 => ?_
  refine memRegion32_cells (sp1 + 160#64) (by sep_focus) fun w18 w19 w20 w21 => ?_
  have h1 := h (w1 ++ w0) (w3 ++ w2) (w5 ++ w4) (w7 ++ w6) (w9 ++ w8)
    (w11 ++ w10) (w13 ++ w12) (w15 ++ w14) (w17 ++ w16) (w19 ++ w18) (w21 ++ w20)
  dsimp only [Spill11] at h1
  simp only [extractLsb_lo_append, extractLsb_hi_append] at h1
  rw [show (sp1 + 160#64) + 8#64 = sp1 + 168#64 by bv_omega,
      show (sp1 + 160#64) + 16#64 = sp1 + 176#64 by bv_omega,
      show (sp1 + 160#64) + 24#64 = sp1 + 184#64 by bv_omega]
  exact SepWP.congr_pre (by sep_eq) h1

/-! ## Stack pad-buffer (`136`-byte) helpers -/

theorem zero17_eq_replicate136 (a : BitVec 64) :
    ((((((a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 0#64)) ∗
        (((a + 16#64) ↦₆₄ 0#64) ∗ ((a + 24#64) ↦₆₄ 0#64))) ∗
       ((((a + 32#64) ↦₆₄ 0#64) ∗ ((a + 40#64) ↦₆₄ 0#64)) ∗
        (((a + 48#64) ↦₆₄ 0#64) ∗ ((a + 56#64) ↦₆₄ 0#64)))) ∗
      (((((a + 64#64) ↦₆₄ 0#64) ∗ ((a + 72#64) ↦₆₄ 0#64)) ∗
        (((a + 80#64) ↦₆₄ 0#64) ∗ ((a + 88#64) ↦₆₄ 0#64))) ∗
       ((((a + 96#64) ↦₆₄ 0#64) ∗ ((a + 104#64) ↦₆₄ 0#64)) ∗
        (((a + 112#64) ↦₆₄ 0#64) ∗ ((a + 120#64) ↦₆₄ 0#64))))) ∗
     ((a + 128#64) ↦₆₄ 0#64)) =
      (a ↦ₛ List.replicate 136 0#8) := by
  rw [pointsTo64_16_eq_bytes a 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64
        0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64,
      pointsTo64_eq_unpackLane64 (a + 128#64) 0#64]
  have h128 :
      unpackLane64 0#64 ++ unpackLane64 0#64 ++ unpackLane64 0#64 ++ unpackLane64 0#64 ++
        unpackLane64 0#64 ++ unpackLane64 0#64 ++ unpackLane64 0#64 ++ unpackLane64 0#64 ++
        unpackLane64 0#64 ++ unpackLane64 0#64 ++ unpackLane64 0#64 ++ unpackLane64 0#64 ++
        unpackLane64 0#64 ++ unpackLane64 0#64 ++ unpackLane64 0#64 ++ unpackLane64 0#64 =
        List.replicate 128 0#8 := rfl
  have h8 : unpackLane64 0#64 = List.replicate 8 0#8 := rfl
  have h136 : List.replicate 136 (0#8 : BitVec 8) =
      List.replicate 128 0#8 ++ List.replicate 8 0#8 := rfl
  rw [h128, h8, h136, pointsToBytes_append, List.length_replicate]

/-- Split `(a ↦ₛ List.replicate 136 0#8)` at `remLen ≤ 136` for `memcpy` of `remLen` tail bytes. -/
theorem replicate136_entails_split (a : BitVec 64) (remLen : Nat) (hrem : remLen ≤ 136) :
    (a ↦ₛ List.replicate 136 0#8) ⊢
      memRegion a remLen ∗ ((a + BitVec.ofNat 64 remLen) ↦ₛ List.replicate (136 - remLen) 0#8) := by
  have hrep : List.replicate 136 (0#8 : BitVec 8) =
      List.replicate remLen 0#8 ++ List.replicate (136 - remLen) 0#8 := by
    rw [← List.replicate_add, show remLen + (136 - remLen) = 136 by omega]
  rw [hrep, pointsToBytes_append, List.length_replicate]
  refine sepConj_mono ?_ (Entails.refl _)
  simpa [List.length_replicate] using
    pointsToBytes_entails_memRegion a (List.replicate remLen (0#8 : BitVec 8))

/-- Writing byte `135` does not change `ByteSlice.readLE` on offsets `off` with `off + 8 ≤ 135`. -/
theorem readLE_write8_135_lt (bs : List (BitVec 8)) (v : BitVec 8) (off : Nat)
    (hoff : off + 8 ≤ 135 := by decide) (hlen : bs.length = 136 := by omega) :
    ByteSlice.readLE bs off 8 = ByteSlice.readLE (ByteSlice.write8 bs 135 v) off 8 := by
  have g (j : Nat) (hj : j < 8) :
      bs.getD (off + j) 0#8 = (ByteSlice.write8 bs 135 v).getD (off + j) 0#8 := by
    rw [ByteSlice.getD_write8 bs 135 v (off + j) 0#8 (by omega)]
    have hne : off + j ≠ 135 := by omega
    simp only [hne, ↓reduceIte]
  rw [readLE_8_eq_packLane64, readLE_8_eq_packLane64]
  unfold packLane64
  have h0a : bs.getD off 0#8 = bs.getD (off + 0) 0#8 := rfl
  have h0b : (ByteSlice.write8 bs 135 v).getD off 0#8 =
      (ByteSlice.write8 bs 135 v).getD (off + 0) 0#8 := rfl
  rw [h0a, h0b, g 0 (by decide), g 1 (by decide), g 2 (by decide), g 3 (by decide),
      g 4 (by decide), g 5 (by decide), g 6 (by decide), g 7 (by decide)]

theorem xor_packLane_left (s : KeccakState) (blk : List (BitVec 8)) (off k : Nat)
    (hoff : off = 8 * k := by decide) (hk : k < 17 := by decide) :
    packLane64 blk off ^^^ s.getD k 0#64 = (keccakXorRate17 s blk).getD k 0#64 := by
  subst hoff
  rw [BitVec.xor_comm, keccakXorRate17_getD_lt s blk hk]

theorem xor_packLane_right (s : KeccakState) (blk : List (BitVec 8)) (off k : Nat)
    (hoff : off = 8 * k := by decide) (hk : k < 17 := by decide) :
    s.getD k 0#64 ^^^ packLane64 blk off = (keccakXorRate17 s blk).getD k 0#64 := by
  subst hoff
  exact (keccakXorRate17_getD_lt s blk hk).symm

/-! ## Arithmetic and `Keccak-f[1600]` round folding lemmas -/

theorem bv64_8mul_add8 (r : Nat) :
    BitVec.ofNat 64 (8 * r) + 8#64 = BitVec.ofNat 64 (8 * (r + 1)) := by
  change BitVec.ofNat 64 (8 * r) + BitVec.ofNat 64 8 = BitVec.ofNat 64 (8 * r + 8)
  exact (BitVec.ofNat_add (8 * r) 8).symm

theorem cmp192_ne_of_lt {r : Nat} (hlt : r + 1 < 24) :
    BitVec.ofNat 64 (8 * (r + 1)) ≠ 192#64 := by
  intro h
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at this
  omega

theorem cmp192_eq_of_ge {r : Nat} (hr : r < 24) (hge : ¬ (r + 1 < 24)) :
    BitVec.ofNat 64 (8 * (r + 1)) = 192#64 := by
  have : r + 1 = 24 := by omega
  rw [this]

private theorem xor5_c_shape (a0 a1 a2 a3 a4 : BitVec 64) :
    (((a1 ^^^ a0) ^^^ (a2 ^^^ a3)) ^^^ a4) = a0 ^^^ a1 ^^^ a2 ^^^ a3 ^^^ a4 := by
  rw [BitVec.xor_comm a1 a0, ← BitVec.xor_assoc (a0 ^^^ a1) a2 a3]

theorem keccakC_fold_0 (s : KeccakState) :
    (((s.getD 5 0#64 ^^^ s.getD 0 0#64) ^^^ (s.getD 10 0#64 ^^^ s.getD 15 0#64)) ^^^
      s.getD 20 0#64) = keccakC s 0 :=
  xor5_c_shape _ _ _ _ _

theorem keccakC_fold_1 (s : KeccakState) :
    (((s.getD 6 0#64 ^^^ s.getD 1 0#64) ^^^ (s.getD 11 0#64 ^^^ s.getD 16 0#64)) ^^^
      s.getD 21 0#64) = keccakC s 1 :=
  xor5_c_shape _ _ _ _ _

theorem keccakC_fold_2 (s : KeccakState) :
    (((s.getD 7 0#64 ^^^ s.getD 2 0#64) ^^^ (s.getD 12 0#64 ^^^ s.getD 17 0#64)) ^^^
      s.getD 22 0#64) = keccakC s 2 :=
  xor5_c_shape _ _ _ _ _

theorem keccakC_fold_3 (s : KeccakState) :
    (((s.getD 8 0#64 ^^^ s.getD 3 0#64) ^^^ (s.getD 13 0#64 ^^^ s.getD 18 0#64)) ^^^
      s.getD 23 0#64) = keccakC s 3 :=
  xor5_c_shape _ _ _ _ _

theorem keccakC_fold_4 (s : KeccakState) :
    (((s.getD 9 0#64 ^^^ s.getD 4 0#64) ^^^ (s.getD 14 0#64 ^^^ s.getD 19 0#64)) ^^^
      s.getD 24 0#64) = keccakC s 4 :=
  xor5_c_shape _ _ _ _ _

theorem keccakD_fold_0 (s : KeccakState) :
    keccakC s 4 ^^^ (keccakC s 1).rotateLeft 1 = keccakD s 0 := rfl

theorem keccakD_fold_1 (s : KeccakState) :
    (keccakC s 2).rotateLeft 1 ^^^ keccakC s 0 = keccakD s 1 :=
  BitVec.xor_comm _ _

theorem keccakD_fold_2 (s : KeccakState) :
    (keccakC s 3).rotateLeft 1 ^^^ keccakC s 1 = keccakD s 2 :=
  BitVec.xor_comm _ _

theorem keccakD_fold_3 (s : KeccakState) :
    (keccakC s 4).rotateLeft 1 ^^^ keccakC s 2 = keccakD s 3 :=
  BitVec.xor_comm _ _

theorem keccakD_fold_4 (s : KeccakState) :
    keccakC s 3 ^^^ (keccakC s 0).rotateLeft 1 = keccakD s 4 := rfl

theorem keccakTheta_fold_l (s : KeccakState) (d idx : Nat) (hd : d = idx % 5 := by decide) :
    keccakD s d ^^^ s.getD idx 0#64 = keccakTheta s idx := by
  subst hd; exact BitVec.xor_comm _ _

theorem keccakTheta_fold_r (s : KeccakState) (d idx : Nat) (hd : d = idx % 5 := by decide) :
    s.getD idx 0#64 ^^^ keccakD s d = keccakTheta s idx := by
  subst hd; rfl

theorem keccakRhoPi_fold_0 (s : KeccakState) :
    keccakTheta s 0 = keccakRhoPi s 0 := by
  simp [keccakRhoPi, keccakRhoPiSrc, keccakRhoOffset, rotateLeft_zero_64]

theorem keccakRhoPi_fold (s : KeccakState) (src r idx : Nat)
    (hsrc : keccakRhoPiSrc idx = src := by decide)
    (hr : keccakRhoOffset src = r := by decide) :
    (keccakTheta s src).rotateLeft r = keccakRhoPi s idx := by
  dsimp only [keccakRhoPi]
  rw [hsrc, hr]

theorem keccakChi0_fold (s : KeccakState) (rc : BitVec 64) :
    (~~~(keccakRhoPi s 1) &&& keccakRhoPi s 2) ^^^ (rc ^^^ keccakRhoPi s 0) =
      (keccakF1600Round s rc).getD 0 0#64 := by
  rw [keccakF1600Round_getD s rc (by decide)]
  change (~~~(keccakRhoPi s 1) &&& keccakRhoPi s 2) ^^^ (rc ^^^ keccakRhoPi s 0) =
    (keccakRhoPi s 0 ^^^ (~~~(keccakRhoPi s 1) &&& keccakRhoPi s 2)) ^^^ rc
  rw [BitVec.xor_comm rc (keccakRhoPi s 0),
      ← BitVec.xor_assoc _ (keccakRhoPi s 0) rc,
      BitVec.xor_comm _ (keccakRhoPi s 0)]

theorem keccakChi_fold (s : KeccakState) (rc : BitVec 64) (b1 b2 b0 idx : Nat)
    (hpos : (idx == 0) = false := by decide)
    (hlt : idx < 25 := by decide)
    (hb0 : 5 * (idx / 5) + idx % 5 = b0 := by decide)
    (hb1 : 5 * (idx / 5) + (idx % 5 + 1) % 5 = b1 := by decide)
    (hb2 : 5 * (idx / 5) + (idx % 5 + 2) % 5 = b2 := by decide) :
    (~~~(keccakRhoPi s b1) &&& keccakRhoPi s b2) ^^^ keccakRhoPi s b0 =
      (keccakF1600Round s rc).getD idx 0#64 := by
  rw [keccakF1600Round_getD s rc hlt]
  dsimp only [keccakRoundLane]
  rw [hpos, hb0, hb1, hb2]
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact BitVec.xor_comm _ _

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31.Base
