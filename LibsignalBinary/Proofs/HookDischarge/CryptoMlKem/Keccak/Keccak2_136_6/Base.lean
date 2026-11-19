/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.ProgramReflection
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Defs
public meta import ProofLib.ProgramReflection
public meta import ProofLib.GenDecodes
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps

/-!
# `B02` (`keccak2::<136, 6>`): shared placed-block and stack-layout base

Shared definitions and helper lemmas for `mlkemBlk02` (`595` words = `0x94c` bytes, `1040`-byte
total stack footprint):
- Placed-block setup (`blkLib02`, `blkPl02`, `blkPlaceable02`, `blkPC02`, `blkTree02`,
  `blk02_code_eq`, `blk02_tree_size`).
- Callee-saved frame `SavedFrame02` (`[sp0 - 160, sp0)`, `d8..d15` and `x19..x30`) and
  `1040`-byte stack layout equation `stack1040_split`.
- Stationary 25-lane register and spill-slot predicates `Loop1Regs`/`Loop1SpillMem` (`+0x00f0`)
  and `Loop2Regs`/`Loop2SpillMem` (`+0x05e4`), plus `step_ld1r_keccakRc` and `sepWP_seq_env`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.Base

open Arm64 Arm64.Obj ProofLib SepProp
open scoped ProofLib.ProgramReflection
open ProofLib.ProgramReflection (WordTree)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (
  mlkemData01Bytes
  mlkemMultiLib
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemPlacement
  mlkemMpl
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (
  MlKemRoOk
  keccakRcAt
  mlkemData01Bytes_length
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps (step_simdLd1r_2d)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (KeccakState)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Defs (keccak2Lane)

/-! ## Block 2 (`keccak2::<136, 6>`) `PlacedLib` and `WordTree` setup -/

@[expose] def blkLib02 : PlacedLib := mlkemMultiLib.blockLib 2
@[expose] def blkPl02 [MlKemPlacement] : Placement := mlkemMultiLib.blockPlacement mlkemMpl 2
theorem blkPlaceable02 [MlKemPlacement] : blkLib02.Placeable blkPl02 :=
  mlkemMultiLib.placeable_blockLib (by decide) MlKemPlacement.placeable
@[expose] def blkPC02 [MlKemPlacement] : Program := blkLib02.program blkPl02
@[expose] def blkProg02 : Program := { code := blkLib02.text.code, symbols := blkLib02.text.symbols }
@[expose] def blkTree02 : WordTree := word_tree_of% blkProg02
theorem blk02_code_eq : blkLib02.text.code = blkTree02.toBytes := by rfl_kernel
theorem blk02_tree_size : blkTree02.checkSize? = some 595 := by rfl_kernel

/-! ## Environment-preserving segment sequencing and `LD1R` round-constant step -/

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

/-- Step `LD1R {Vt.2D}, [Xn]` reading `keccakRcAt r` (`r < 24`) from `(rcBase ↦ᵣ mlkemData01Bytes)`. -/
theorem step_ld1r_keccakRc {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc rcBase : BitVec 64} {rn : Reg} {rm vt : BitVec 5} (r : Nat)
    (hr : r < 24)
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.simdLd1r true 0x3#2 rn false rm vt))
    (hsp : checkRegSPAligned s rn = true)
    (hea : rcBase + BitVec.ofNat 64 (8 * r) = s.readReg64 rn)
    (hfoc : P = (rcBase ↦ᵣ mlkemData01Bytes) ∗ F := by sep_focus)
    (hexec : (s.writeVReg128 vt (keccakRcAt r ++ keccakRcAt r)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom := by
  have hload : SepLoad64 (s.readReg64 rn) P (keccakRcAt r) :=
    SepLoad64.of_pointsToBytes_readLE_RO hfoc (by rw [mlkemData01Bytes_length]; omega) hea
  exact step_simdLd1r_2d hpc hrun hfetch hsp rfl hload hexec hnext

/-! ## Spilled callee-saved frame (`160` bytes) and `1040`-byte stack layout -/

/-- Spilled callee-saved registers (`d8..d15` and `x19..x30`) at `[sp0 - 160, sp0)`. -/
@[expose] def SavedFrame02 (sp0 : BitVec 64) (s0 : State) : SepProp :=
  (((sp0 - 160#64) ↦₆₄ (s0.readVReg128 15#5).extractLsb' 0 64) ∗
   ((sp0 - 152#64) ↦₆₄ (s0.readVReg128 14#5).extractLsb' 0 64) ∗
   ((sp0 - 144#64) ↦₆₄ (s0.readVReg128 13#5).extractLsb' 0 64) ∗
   ((sp0 - 136#64) ↦₆₄ (s0.readVReg128 12#5).extractLsb' 0 64) ∗
   ((sp0 - 128#64) ↦₆₄ (s0.readVReg128 11#5).extractLsb' 0 64) ∗
   ((sp0 - 120#64) ↦₆₄ (s0.readVReg128 10#5).extractLsb' 0 64) ∗
   ((sp0 - 112#64) ↦₆₄ (s0.readVReg128 9#5).extractLsb' 0 64) ∗
   ((sp0 - 104#64) ↦₆₄ (s0.readVReg128 8#5).extractLsb' 0 64)) ∗
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
   ((sp0 - 8#64) ↦₆₄ s0.readReg64 .x19))

theorem savedFrame02_entails_memRegion (sp0 : BitVec 64) (s0 : State) :
    SavedFrame02 sp0 s0 ⊢ memRegion (sp0 - 160#64) 160 := by
  unfold SavedFrame02
  have h64 :
      (((sp0 - 160#64) ↦₆₄ (s0.readVReg128 15#5).extractLsb' 0 64) ∗
       ((sp0 - 152#64) ↦₆₄ (s0.readVReg128 14#5).extractLsb' 0 64) ∗
       ((sp0 - 144#64) ↦₆₄ (s0.readVReg128 13#5).extractLsb' 0 64) ∗
       ((sp0 - 136#64) ↦₆₄ (s0.readVReg128 12#5).extractLsb' 0 64) ∗
       ((sp0 - 128#64) ↦₆₄ (s0.readVReg128 11#5).extractLsb' 0 64) ∗
       ((sp0 - 120#64) ↦₆₄ (s0.readVReg128 10#5).extractLsb' 0 64) ∗
       ((sp0 - 112#64) ↦₆₄ (s0.readVReg128 9#5).extractLsb' 0 64) ∗
       ((sp0 - 104#64) ↦₆₄ (s0.readVReg128 8#5).extractLsb' 0 64)) ⊢
        memRegion (sp0 - 160#64) 64 := by
    rw [memRegion_split' (b' := sp0 - 152#64) (n := 8) (k := 56) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp0 - 144#64) (n := 8) (k := 48) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp0 - 136#64) (n := 8) (k := 40) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp0 - 128#64) (n := 8) (k := 32) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp0 - 120#64) (n := 8) (k := 24) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp0 - 112#64) (n := 8) (k := 16) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp0 - 104#64) (n := 8) (k := 8) rfl (by bv_omega) (by decide)]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (sepConj_mono (pointsTo64_entails_memRegion _ _)
                (sepConj_mono (pointsTo64_entails_memRegion _ _)
                  (pointsTo64_entails_memRegion _ _)))))))
  have h96 :
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
       ((sp0 - 8#64) ↦₆₄ s0.readReg64 .x19)) ⊢
        memRegion (sp0 - 96#64) 96 := by
    rw [memRegion_split' (b' := sp0 - 88#64) (n := 8) (k := 88) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp0 - 80#64) (n := 8) (k := 80) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp0 - 72#64) (n := 8) (k := 72) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp0 - 64#64) (n := 8) (k := 64) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp0 - 56#64) (n := 8) (k := 56) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp0 - 48#64) (n := 8) (k := 48) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp0 - 40#64) (n := 8) (k := 40) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp0 - 32#64) (n := 8) (k := 32) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp0 - 24#64) (n := 8) (k := 24) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp0 - 16#64) (n := 8) (k := 16) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp0 - 8#64) (n := 8) (k := 8) rfl (by bv_omega) (by decide)]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (sepConj_mono (pointsTo64_entails_memRegion _ _)
                (sepConj_mono (pointsTo64_entails_memRegion _ _)
                  (sepConj_mono (pointsTo64_entails_memRegion _ _)
                    (sepConj_mono (pointsTo64_entails_memRegion _ _)
                      (sepConj_mono (pointsTo64_entails_memRegion _ _)
                        (sepConj_mono (pointsTo64_entails_memRegion _ _)
                          (pointsTo64_entails_memRegion _ _)))))))))))
  rw [memRegion_split' (b' := sp0 - 96#64) (n := 64) (k := 96) rfl (by bv_omega) (by decide)]
  exact sepConj_mono h64 h96

/-- Split `stackAt sp0 1040` around `sp := sp0 - 1024#64` into:
    - `stackAt sp 16` (`B09` callee stack),
    - `memRegion sp 176` (vector spill area),
    - `memRegion (sp + 176#64) 400` (`Keccak2Mem`),
    - `memRegion (sp + 576#64) 288` (`buf0` + `buf1` tail pad buffers + alignment),
    - `memRegion (sp0 - 160#64) 160` (`SavedFrame02`). -/
theorem stack1040_split (sp0 : BitVec 64) :
    let sp := sp0 - 1024#64
    stackAt sp0 1040 =
      stackAt sp 16 ∗
      memRegion sp 176 ∗
      memRegion (sp + 176#64) 400 ∗
      memRegion (sp + 576#64) 288 ∗
      memRegion (sp0 - 160#64) 160 := by
  intro sp
  unfold stackAt
  have h0 : sp - BitVec.ofNat 64 16 = sp0 - BitVec.ofNat 64 1040 := by
    dsimp [sp]; bv_omega
  rw [h0,
      memRegion_split' (b' := sp) (n := 16) (k := (1024 : Nat)) rfl (by dsimp [sp]; bv_omega) (by decide),
      memRegion_split' (b' := sp + 176#64) (n := 176) (k := 848) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp + 576#64) (n := 400) (k := 448) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp0 - 160#64) (n := 288) (k := 160) rfl (by dsimp [sp]; bv_omega) (by decide)]

/-! ## Stationary 25-lane register and spill-slot invariants for both `keccak_f1600` loops -/

/-- Loop 1 (`+0x00f0 → +0x03e0`) 22-register lane assignment (`lanes 7, 8, 14` spilled). -/
@[expose] def Loop1Regs (s : State) (st0 st1 : KeccakState) : Prop :=
  s.readVReg128 9#5 = keccak2Lane st0 st1 0 ∧
  s.readVReg128 6#5 = keccak2Lane st0 st1 1 ∧
  s.readVReg128 24#5 = keccak2Lane st0 st1 2 ∧
  s.readVReg128 16#5 = keccak2Lane st0 st1 3 ∧
  s.readVReg128 19#5 = keccak2Lane st0 st1 4 ∧
  s.readVReg128 30#5 = keccak2Lane st0 st1 5 ∧
  s.readVReg128 7#5 = keccak2Lane st0 st1 6 ∧
  s.readVReg128 11#5 = keccak2Lane st0 st1 9 ∧
  s.readVReg128 5#5 = keccak2Lane st0 st1 10 ∧
  s.readVReg128 22#5 = keccak2Lane st0 st1 11 ∧
  s.readVReg128 18#5 = keccak2Lane st0 st1 12 ∧
  s.readVReg128 15#5 = keccak2Lane st0 st1 13 ∧
  s.readVReg128 29#5 = keccak2Lane st0 st1 15 ∧
  s.readVReg128 23#5 = keccak2Lane st0 st1 16 ∧
  s.readVReg128 27#5 = keccak2Lane st0 st1 17 ∧
  s.readVReg128 12#5 = keccak2Lane st0 st1 18 ∧
  s.readVReg128 3#5 = keccak2Lane st0 st1 19 ∧
  s.readVReg128 8#5 = keccak2Lane st0 st1 20 ∧
  s.readVReg128 28#5 = keccak2Lane st0 st1 21 ∧
  s.readVReg128 17#5 = keccak2Lane st0 st1 22 ∧
  s.readVReg128 4#5 = keccak2Lane st0 st1 23 ∧
  s.readVReg128 2#5 = keccak2Lane st0 st1 24

/-- Loop 1 (`+0x00f0 → +0x03e0`) `176`-byte spill region (`[sp, sp + 128)` scratch + spilled lanes `7, 8, 14`). -/
@[expose] def Loop1SpillMem (sp : BitVec 64) (st0 st1 : KeccakState) : SepProp :=
  memRegion sp 128 ∗
  (((sp + 128#64) ↦₆₄ st0.getD 7 0#64) ∗ ((sp + 136#64) ↦₆₄ st1.getD 7 0#64)) ∗
  (((sp + 144#64) ↦₆₄ st0.getD 8 0#64) ∗ ((sp + 152#64) ↦₆₄ st1.getD 8 0#64)) ∗
  (((sp + 160#64) ↦₆₄ st0.getD 14 0#64) ∗ ((sp + 168#64) ↦₆₄ st1.getD 14 0#64))

theorem loop1SpillMem_entails_memRegion (sp : BitVec 64) (st0 st1 : KeccakState) :
    Loop1SpillMem sp st0 st1 ⊢ memRegion sp 176 := by
  unfold Loop1SpillMem
  rw [memRegion_split' (b' := sp + 128#64) (n := 128) (k := 48) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp + 136#64) (n := 8) (k := 40) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp + 144#64) (n := 8) (k := 32) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 144#64) (b' := sp + 152#64) (n := 8) (k := 24) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp + 160#64) (n := 8) (k := 16) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp + 168#64) (n := 8) (k := 8) rfl (by bv_omega) (by decide)]
  simp only [sepConj_assoc]
  exact sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (pointsTo64_entails_memRegion _ _))))))

/-- Loop 2 (`+0x05e4 → +0x08cc`) 20-register lane assignment (`lanes 7, 6, 9, 8, 4` spilled). -/
@[expose] def Loop2Regs (s : State) (st0 st1 : KeccakState) : Prop :=
  s.readVReg128 31#5 = keccak2Lane st0 st1 0 ∧
  s.readVReg128 6#5 = keccak2Lane st0 st1 1 ∧
  s.readVReg128 18#5 = keccak2Lane st0 st1 2 ∧
  s.readVReg128 17#5 = keccak2Lane st0 st1 3 ∧
  s.readVReg128 28#5 = keccak2Lane st0 st1 5 ∧
  s.readVReg128 26#5 = keccak2Lane st0 st1 10 ∧
  s.readVReg128 23#5 = keccak2Lane st0 st1 11 ∧
  s.readVReg128 22#5 = keccak2Lane st0 st1 12 ∧
  s.readVReg128 20#5 = keccak2Lane st0 st1 13 ∧
  s.readVReg128 15#5 = keccak2Lane st0 st1 14 ∧
  s.readVReg128 9#5 = keccak2Lane st0 st1 15 ∧
  s.readVReg128 29#5 = keccak2Lane st0 st1 16 ∧
  s.readVReg128 25#5 = keccak2Lane st0 st1 17 ∧
  s.readVReg128 12#5 = keccak2Lane st0 st1 18 ∧
  s.readVReg128 7#5 = keccak2Lane st0 st1 19 ∧
  s.readVReg128 8#5 = keccak2Lane st0 st1 20 ∧
  s.readVReg128 27#5 = keccak2Lane st0 st1 21 ∧
  s.readVReg128 21#5 = keccak2Lane st0 st1 22 ∧
  s.readVReg128 3#5 = keccak2Lane st0 st1 23 ∧
  s.readVReg128 4#5 = keccak2Lane st0 st1 24

/-- Loop 2 (`+0x05e4 → +0x08cc`) `176`-byte spill region (`[sp, sp + 96)` scratch + spilled lanes `7, 6, 9, 8, 4`). -/
@[expose] def Loop2SpillMem (sp : BitVec 64) (st0 st1 : KeccakState) : SepProp :=
  memRegion sp 64 ∗ memRegion (sp + 64#64) 32 ∗
  (((sp + 96#64) ↦₆₄ st0.getD 7 0#64) ∗ ((sp + 104#64) ↦₆₄ st1.getD 7 0#64)) ∗
  (((sp + 112#64) ↦₆₄ st0.getD 6 0#64) ∗ ((sp + 120#64) ↦₆₄ st1.getD 6 0#64)) ∗
  (((sp + 128#64) ↦₆₄ st0.getD 9 0#64) ∗ ((sp + 136#64) ↦₆₄ st1.getD 9 0#64)) ∗
  (((sp + 144#64) ↦₆₄ st0.getD 8 0#64) ∗ ((sp + 152#64) ↦₆₄ st1.getD 8 0#64)) ∗
  (((sp + 160#64) ↦₆₄ st0.getD 4 0#64) ∗ ((sp + 168#64) ↦₆₄ st1.getD 4 0#64))

theorem loop2SpillMem_entails_memRegion (sp : BitVec 64) (st0 st1 : KeccakState) :
    Loop2SpillMem sp st0 st1 ⊢ memRegion sp 176 := by
  unfold Loop2SpillMem
  rw [memRegion_split' (b' := sp + 64#64) (n := 64) (k := 112) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp + 96#64) (n := 32) (k := 80) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp + 104#64) (n := 8) (k := 72) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp + 112#64) (n := 8) (k := 64) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 112#64) (b' := sp + 120#64) (n := 8) (k := 56) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp + 128#64) (n := 8) (k := 48) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp + 136#64) (n := 8) (k := 40) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp + 144#64) (n := 8) (k := 32) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 144#64) (b' := sp + 152#64) (n := 8) (k := 24) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp + 160#64) (n := 8) (k := 16) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp + 168#64) (n := 8) (k := 8) rfl (by bv_omega) (by decide)]
  simp only [sepConj_assoc]
  exact sepConj_mono (Entails.refl _)
    (sepConj_mono (Entails.refl _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (sepConj_mono (pointsTo64_entails_memRegion _ _)
                (sepConj_mono (pointsTo64_entails_memRegion _ _)
                  (sepConj_mono (pointsTo64_entails_memRegion _ _)
                    (sepConj_mono (pointsTo64_entails_memRegion _ _)
                      (sepConj_mono (pointsTo64_entails_memRegion _ _)
                        (pointsTo64_entails_memRegion _ _)))))))))))

theorem trunc64_zext128_extractLsb0 (v : BitVec 128) :
    (((v.extractLsb' 0 64).zeroExtend 128 : BitVec 128).truncate 64) = v.truncate 64 := by
  ext i hi
  simp [BitVec.getElem_setWidth]

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.Base
