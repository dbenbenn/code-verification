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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps

/-!
# `validate_pk_bytes` (`B21`) — Segment 1 (`+0x0000 .. +0x00b0` & Epilogue `+0x0820 .. +0x0848`)

Covers:
1. Shared epilogue (`+0x0820 .. +0x0848`: `seg_epilogue`, `seg_ret_err2`, `seg_ret_ok`),
2. Prologue + length checks (`+0x0000 .. +0x0038`: early `0x00#8` returns when `hdr.length ≠ 64` or
   `ek.length ≠ 1152`),
3. Valid-length stack `pk := ek ++ hdr.take 32` assembly (`B28` `memcpy` + `LDP/STR` of 32-byte
   `seed`), `B02` (`keccak2::<136, 6>`) SHA3-256 call, and 4×64-bit `CMP`/`CCMP` digest check
   (`+0x0038 .. +0x00b0`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg1

open Arm64 Arm64.Obj ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase
  MlKemBlockOk
  MlKemPlacement
  add_off_reloc_cancel
  add_reloc_cancel
  add_zero_reloc_cancel
  mbase
  mlkemBlockPlacement_ρ
  mlkemCall_of_blockOk
  mlkemMpl
  resolve_blk02
  resolve_blk28
  seq_codeLoaded_lr
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (
  Keccak2SlicesRW
  keccak2_136_6_RW1Spec
  mlkemMemcpySpec
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  keccakSponge
  mlkem768ValidPk
  sha3_256
  sha3_256List
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Base (
  blk21_code_eq
  blk21_tree_size
  blkLib21
  blkPC21
  blkPl21
  blkPlaceable21
  blkTree21
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps (blk28_memcpy_ok)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC21 blkLib21 blkTree21 blk21_code_eq blk21_tree_size
  via_placement blkPl21 blkPlaceable21 [0x0000 → 0x00ac]
gen_placed_fetches blkPC21 blkLib21 blkTree21 blk21_code_eq blk21_tree_size
  via_placement blkPl21 blkPlaceable21 [0x0820 → 0x0844]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl21_ρ [MlKemPlacement] (sym : String) :
    blkPl21.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

/-! ## 0. Segment Composition & `memRegion` Existential Combinators -/

/-- Sequence two `SepWP` segments while preserving `CodeLoaded` and `MlKemRoOk` across `KeepsFrozen`
    transitions. -/
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

/-- Destructure a leading `memRegion a 8` into an existential `a ↦₆₄ v` inside `SepWP`. -/
theorem sepWP_elim_cell8 {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop}
    (h : ∀ v : BitVec 64, SepWP prog target s ((a ↦₆₄ v) ∗ R0) post) :
    SepWP prog target s (memRegion a 8 ∗ R0) post := by
  unfold SepWP at h ⊢
  intro R hm
  rw [memRegion_eight, sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨v, hv⟩ := hm
  exact h v R (by simpa only [sepConj_assoc] using hv)

private theorem sep_swap1 (X Y Z : SepProp) : X ∗ (Y ∗ Z) = Y ∗ (X ∗ Z) := by
  rw [← sepConj_assoc, sepConj_comm X Y, sepConj_assoc]

/-- Destructure a leading `memRegion a 16` into two 64-bit cells inside `SepWP`. -/
theorem sepWP_elim_region16 {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop}
    (h : ∀ v0 v1 : BitVec 64,
      SepWP prog target s ((a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ R0) post) :
    SepWP prog target s (memRegion a 16 ∗ R0) post := by
  rw [memRegion_split' (b' := a + 8#64) (n := 8) (k := 8) rfl (by bv_omega) (by decide),
    sepConj_assoc]
  apply sepWP_elim_cell8; intro v0
  rw [sep_swap1]
  apply sepWP_elim_cell8; intro v1
  rw [sep_swap1]
  exact h v0 v1

/-- Destructure a leading `memRegion a 32` into four 64-bit cells inside `SepWP`. -/
theorem sepWP_elim_region32 {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop}
    (h : ∀ v0 v1 v2 v3 : BitVec 64,
      SepWP prog target s
        ((a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) ∗ R0)
        post) :
    SepWP prog target s (memRegion a 32 ∗ R0) post := by
  rw [memRegion_split' (b' := a + 16#64) (n := 16) (k := 16) rfl (by bv_omega) (by decide),
    sepConj_assoc]
  apply sepWP_elim_region16; intro v0 v1
  rw [sep_swap1 ((a + 8#64) ↦₆₄ v1), sep_swap1 (a ↦₆₄ v0)]
  apply sepWP_elim_region16; intro v2 v3
  have h24 : a + 16#64 + 8#64 = a + 24#64 := by bv_omega
  rw [h24,
    sep_swap1 ((a + 24#64) ↦₆₄ v3) (a ↦₆₄ v0),
    sep_swap1 ((a + 16#64) ↦₆₄ v2) (a ↦₆₄ v0),
    sep_swap1 ((a + 24#64) ↦₆₄ v3) ((a + 8#64) ↦₆₄ v1),
    sep_swap1 ((a + 16#64) ↦₆₄ v2) ((a + 8#64) ↦₆₄ v1)]
  exact h v0 v1 v2 v3

theorem cells16_entails_memRegion (a v0 v1 : BitVec 64) :
    (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ⊢ memRegion a 16 := by
  rw [memRegion_split' (b' := a + 8#64) (n := 8) (k := 8) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)

theorem cells32_entails_memRegion (a v0 v1 v2 v3 : BitVec 64) :
    (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) ⊢
      memRegion a 32 := by
  rw [memRegion_split' (b' := a + 16#64) (n := 16) (k := 16) rfl (by bv_omega) (by decide)]
  have h24 : a + 16#64 + 8#64 = a + 24#64 := by bv_omega
  refine Entails.trans ?_
    (sepConj_mono (cells16_entails_memRegion a v0 v1) (cells16_entails_memRegion (a + 16#64) v2 v3))
  rw [h24]
  sep_frame

/-- Rewrite a sub-entailment `A ⊢ B` inside `P ⊢ Q` using `sep_frame` to infer `Rest`. -/
theorem entails_sub {A B P Rest Q : SepProp}
    (hAB : A ⊢ B) (h1 : P ⊢ A ∗ Rest) (h2 : B ∗ Rest ⊢ Q) : P ⊢ Q :=
  Entails.trans h1 (Entails.trans (sepConj_mono_left hAB) h2)

/-! ## 1. Spilled Callee-Saved Frame & Epilogue (`+0x0820 .. +0x0848`) -/

/-- Spilled callee-saved registers at `[sp0 - 64, sp0)`. -/
@[expose] def SavedFrame (sp0 : BitVec 64) (s0 : State) : SepProp :=
  ((sp0 - 64#64) ↦₆₄ s0.readReg64 .fp) ∗
  ((sp0 - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
  ((sp0 - 48#64) ↦₆₄ s0.readReg64 .x28) ∗
  ((sp0 - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((sp0 - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
  ((sp0 - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp0 - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((sp0 - 8#64) ↦₆₄ s0.readReg64 .x19)

/-- Unspilled callee-saved registers (`x24..x27` and `v8..v15` low halves) never modified by `B21`. -/
@[expose] def UnspilledSaved (s0 s : State) : Prop :=
  s.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5) ∧
  s.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5) ∧
  s.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) ∧
  s.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

theorem UnspilledSaved.refl (s0 : State) : UnspilledSaved s0 s0 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem UnspilledSaved.of_calleeSavedPreserved {s0 s1 s2 : State}
    (h01 : UnspilledSaved s0 s1) (h12 : CalleeSavedPreserved s1 s2) :
    UnspilledSaved s0 s2 :=
  ⟨h12.2.2.2.2.2.1.trans h01.1,
   h12.2.2.2.2.2.2.1.trans h01.2.1,
   h12.2.2.2.2.2.2.2.1.trans h01.2.2.1,
   h12.2.2.2.2.2.2.2.2.1.trans h01.2.2.2.1,
   h12.2.2.2.2.2.2.2.2.2.2.2.trans h01.2.2.2.2⟩

/-- Standard return postcondition at `s0.readReg64 .lr`. -/
@[expose] def RetPost (s0 : State) (retByte : BitVec 8) (F : SepProp) :
    State → SepProp → Prop :=
  fun sf Q =>
    (sf.readReg64 .x0).setWidth 8 = retByte ∧
    sf.sp = s0.sp ∧
    CalleeSavedPreserved s0 sf ∧
    (Q ⊢ stackAt s0.sp 5824 ∗ F)

/-- End-to-end return postcondition of `B21` against `mlkem768ValidPk`. -/
@[expose] def ValidatePkPost (s0 : State) (hdrA : BitVec 64) (hdr : List (BitVec 8))
    (ekA : BitVec 64) (ek : List (BitVec 8)) (R : SepProp) : State → SepProp → Prop :=
  fun sf Q =>
    ((sf.readReg64 .x0).setWidth 8 = 0xff#8 ↔
      mlkem768ValidPk hdr ek = true) ∧
    sf.sp = s0.sp ∧
    CalleeSavedPreserved s0 sf ∧
    (Q ⊢ (hdrA ↦ₛ hdr) ∗ (ekA ↦ₛ ek) ∗ stackAt s0.sp 5824 ∗ R)

theorem sepWP_mono_ret {prog : Program} {s0 s : State} {P : SepProp}
    {retByte : BitVec 8} {hdrA ekA : BitVec 64} {hdr ek : List (BitVec 8)} {R : SepProp}
    (hiff : retByte = 0xff#8 ↔ mlkem768ValidPk hdr ek = true)
    (hwp : SepWP prog (s0.readReg64 .lr) s P
      (RetPost s0 retByte ((hdrA ↦ₛ hdr) ∗ (ekA ↦ₛ ek) ∗ R))) :
    SepWP prog (s0.readReg64 .lr) s P (ValidatePkPost s0 hdrA hdr ekA ek R) := by
  refine SepWP.mono hwp (fun sf Q _ _ ⟨hx0, hsp, hcs, hQ⟩ => ?_)
  refine ⟨hx0 ▸ hiff, hsp, hcs, ?_⟩
  rw [sep_swap1 (ekA ↦ₛ ek) (stackAt s0.sp 5824) _,
    sep_swap1 (hdrA ↦ₛ hdr) (stackAt s0.sp 5824) _]
  exact hQ

theorem savedFrame_entails_memRegion64 (sp0 : BitVec 64) (s0 : State) :
    SavedFrame sp0 s0 ⊢ memRegion (sp0 - 64#64) 64 := by
  unfold SavedFrame
  have hsplit :
      memRegion (sp0 - 64#64) 64 =
        memRegion (sp0 - 64#64) 8 ∗ memRegion (sp0 - 56#64) 8 ∗
        memRegion (sp0 - 48#64) 8 ∗ memRegion (sp0 - 40#64) 8 ∗
        memRegion (sp0 - 32#64) 8 ∗ memRegion (sp0 - 24#64) 8 ∗
        memRegion (sp0 - 16#64) 8 ∗ memRegion (sp0 - 8#64) 8 := by
    rw [memRegion_split' (b' := sp0 - 56#64) (n := 8) (k := 56) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp0 - 48#64) (n := 8) (k := 48) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp0 - 40#64) (n := 8) (k := 40) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp0 - 32#64) (n := 8) (k := 32) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp0 - 24#64) (n := 8) (k := 24) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp0 - 16#64) (n := 8) (k := 16) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp0 - 8#64) (n := 8) (k := 8) rfl (by bv_omega) (by decide)]
  rw [hsplit]
  refine sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (sepConj_mono (pointsTo64_entails_memRegion _ _)
                (pointsTo64_entails_memRegion _ _)))))))

theorem savedFrame_restore_entails (sp0 : BitVec 64) (s0 : State) :
    SavedFrame sp0 s0 ∗ memRegion (sp0 - 4784#64) 4720 ∗ stackAt (sp0 - 4784#64) 1040 ⊢
      stackAt sp0 5824 := by
  have htop :
      stackAt sp0 5824 =
        stackAt (sp0 - 4784#64) 1040 ∗ memRegion (sp0 - 4784#64) 4720 ∗
          memRegion (sp0 - 64#64) 64 := by
    unfold stackAt
    have h1 : sp0 - 4784#64 - 1040#64 = sp0 - 5824#64 := by bv_omega
    rw [show memRegion (sp0 - BitVec.ofNat 64 5824) 5824 = memRegion (sp0 - 5824#64) 5824 from rfl,
      show memRegion (sp0 - 4784#64 - BitVec.ofNat 64 1040) 1040 =
        memRegion (sp0 - 5824#64) 1040 from congrArg (memRegion · 1040) h1]
    rw [memRegion_split' (b' := sp0 - 4784#64) (n := 1040) (k := (4784 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp0 - 64#64) (n := 4720) (k := 64) rfl (by bv_omega) (by decide)]
  rw [htop]
  refine Entails.trans (sepConj_mono_left (savedFrame_entails_memRegion64 sp0 s0)) ?_
  sep_frame

/-- Shared epilogue (`+0x0824 .. +0x083c`): restores `sp`, `x19..x23`, `x28`, `x29`, `x30` and
    returns to `s0.readReg64 .lr` preserving `(s.readReg64 .x0).setWidth 8`. -/
theorem seg_epilogue [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl21 b) (_hbase : blkPl21.base = b)
    (s0 s : State) (F : SepProp)
    (hpc : s.pc = b + 0x0824#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4784#64)
    (hsp0 : s0.spAligned = true)
    (hus : UnspilledSaved s0 s) :
    SepWP (blkPC21.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      (SavedFrame s0.sp s0 ∗ memRegion (s0.sp - 4784#64) 4720 ∗ stackAt (s0.sp - 4784#64) 1040 ∗ F)
      (RetPost s0 ((s.readReg64 .x0).setWidth 8) F) := by
  unfold SavedFrame
  have hsp_align : s.spAligned = true := by
    rw [State.spAligned, hsp]
    exact spAligned_sub s0.sp 4784#64 hsp0 (by decide)
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun]) ⟨rfl, by simp, ?_, ?_⟩
  · obtain ⟨h24, h25, h26, h27, hv⟩ := hus
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · simp
    · simp
    · simp
    · simpa using h24
    · simpa using h25
    · simpa using h26
    · simpa using h27
    · simp
    · simp
    · simpa [calleeSavedVRegs] using hv
  · have hrest :
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗
          ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x28) ∗
          ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
          ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
          memRegion (s0.sp - 4784#64) 4720 ∗
          stackAt (s0.sp - 4784#64) 1040 ⊢ stackAt s0.sp 5824 := by
      simpa [SavedFrame, sepConj_assoc] using savedFrame_restore_entails s0.sp s0
    exact entails_sub hrest (by sep_frame) (by sep_frame)

/-- Error exit (`+0x0820`): sets `w0 := 2` and runs `seg_epilogue`. -/
theorem seg_ret_err2 [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl21 b) (hbase : blkPl21.base = b)
    (s0 s : State) (F : SepProp)
    (hpc : s.pc = b + 0x0820#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4784#64)
    (hsp0 : s0.spAligned = true)
    (hus : UnspilledSaved s0 s) :
    SepWP (blkPC21.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      (SavedFrame s0.sp s0 ∗ memRegion (s0.sp - 4784#64) 4720 ∗ stackAt (s0.sp - 4784#64) 1040 ∗ F)
      (RetPost s0 0x02#8 F) := by
  wp_step
  exact seg_epilogue hb hbase s0 _ F (by simp [wp_norm, arm64_norm]) (by simp [hrun]) (by simp [hsp]) hsp0
    ⟨hus.1, hus.2.1, hus.2.2.1, hus.2.2.2.1, hus.2.2.2.2⟩

/-- Success exit (`+0x0840`): sets `w0 := 0xff`, branches to `+0x0824`, and runs `seg_epilogue`. -/
theorem seg_ret_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl21 b) (hbase : blkPl21.base = b)
    (s0 s : State) (F : SepProp)
    (hpc : s.pc = b + 0x0840#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4784#64)
    (hsp0 : s0.spAligned = true)
    (hus : UnspilledSaved s0 s) :
    SepWP (blkPC21.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      (SavedFrame s0.sp s0 ∗ memRegion (s0.sp - 4784#64) 4720 ∗ stackAt (s0.sp - 4784#64) 1040 ∗ F)
      (RetPost s0 0xff#8 F) := by
  wp_step
  wp_step
  exact seg_epilogue hb hbase s0 _ F (by simp [wp_norm, arm64_norm]) (by simp [hrun]) (by simp [hsp]) hsp0
    ⟨hus.1, hus.2.1, hus.2.2.1, hus.2.2.2.1, hus.2.2.2.2⟩

/-! ## 2. Pure Byte / Word & Flag Helpers for Segment 1 -/

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

private theorem pack64_unpack64 (x : BitVec 64) :
    x.extractLsb' 56 8 ++ x.extractLsb' 48 8 ++ x.extractLsb' 40 8 ++ x.extractLsb' 32 8 ++
      x.extractLsb' 24 8 ++ x.extractLsb' 16 8 ++ x.extractLsb' 8 8 ++ x.extractLsb' 0 8 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  split_ifs
  all_goals
    rw [decide_eq_true (by omega), Bool.true_and]
    congr 1
    omega

private theorem unpack64_inj {x y : BitVec 64} (h : unpack64 x = unpack64 y) : x = y := by
  simp only [unpack64, List.cons.injEq, and_true] at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  rw [← pack64_unpack64 x, ← pack64_unpack64 y, h0, h1, h2, h3, h4, h5, h6, h7]

private theorem unpack64_quad_eq_iff (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    unpack64 a0 ++ unpack64 a1 ++ unpack64 a2 ++ unpack64 a3 =
      unpack64 b0 ++ unpack64 b1 ++ unpack64 b2 ++ unpack64 b3 ↔
      (a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3) := by
  constructor
  · intro h
    have ⟨h012, h3⟩ := List.append_inj h (by simp)
    have ⟨h01, h2⟩ := List.append_inj h012 (by simp)
    have ⟨h0, h1⟩ := List.append_inj h01 (by simp)
    exact ⟨unpack64_inj h0, unpack64_inj h1, unpack64_inj h2, unpack64_inj h3⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    rfl

private theorem sha3_256List_length (msg : List (BitVec 8)) :
    (sha3_256List msg).length = 32 := by
  simp [sha3_256List, keccakSponge]

private theorem validPkBytes_false_of_hdr_ne {hdr ek : List (BitVec 8)} (h : hdr.length ≠ 64) :
    mlkem768ValidPk hdr ek = false := by
  simp [mlkem768ValidPk, h]

private theorem validPkBytes_false_of_ek_ne {hdr ek : List (BitVec 8)} (h : ek.length ≠ 1152) :
    mlkem768ValidPk hdr ek = false := by
  simp [mlkem768ValidPk, h]

private theorem validPkBytes_false_of_hash_ne {hdr ek : List (BitVec 8)}
    (hhdr : hdr.length = 64) (hek : ek.length = 1152)
    (hhash : sha3_256List (ek ++ hdr.take 32) ≠ (hdr.drop 32).take 32) :
    mlkem768ValidPk hdr ek = false := by
  simp [mlkem768ValidPk, hhdr, hek, hhash]

attribute [local irreducible] sha3_256List

/-! ## 3. Prologue (`+0x0000 → +0x002c`) -/

private theorem stackAt_prologue_split (sp0 : BitVec 64) :
    stackAt sp0 5824 =
      memRegion (sp0 - 4160#64) 8 ∗
      memRegion (sp0 - 64#64) 32 ∗
      memRegion (sp0 - 32#64) 32 ∗
      memRegion (sp0 - 4784#64) 624 ∗
      memRegion (sp0 - 4152#64) 4088 ∗
      stackAt (sp0 - 4784#64) 1040 := by
  have htop :
      stackAt sp0 5824 =
        stackAt (sp0 - 4784#64) 1040 ∗ memRegion (sp0 - 4784#64) 4720 ∗
          memRegion (sp0 - 64#64) 64 := by
    unfold stackAt
    have h1 : sp0 - 4784#64 - 1040#64 = sp0 - 5824#64 := by bv_omega
    rw [show memRegion (sp0 - BitVec.ofNat 64 5824) 5824 = memRegion (sp0 - 5824#64) 5824 from rfl,
      show memRegion (sp0 - 4784#64 - BitVec.ofNat 64 1040) 1040 =
        memRegion (sp0 - 5824#64) 1040 from congrArg (memRegion · 1040) h1]
    rw [memRegion_split' (b' := sp0 - 4784#64) (n := 1040) (k := (4784 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp0 - 64#64) (n := 4720) (k := 64) rfl (by bv_omega) (by decide)]
  have hmid :
      memRegion (sp0 - 4784#64) 4720 =
        memRegion (sp0 - 4784#64) 624 ∗ memRegion (sp0 - 4160#64) 8 ∗
          memRegion (sp0 - 4152#64) 4088 := by
    rw [memRegion_split' (b' := sp0 - 4160#64) (n := 624) (k := (4096 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp0 - 4152#64) (n := 8) (k := (4088 : Nat)) rfl (by bv_omega) (by decide)]
  have hhi :
      memRegion (sp0 - 64#64) 64 =
        memRegion (sp0 - 64#64) 32 ∗ memRegion (sp0 - 32#64) 32 :=
    memRegion_split' (b' := sp0 - 32#64) (n := 32) (k := 32) rfl (by bv_omega) (by decide)
  rw [htop, hmid, hhi]
  exact sepProp_ext (by sep_frame) (by sep_frame)

private theorem probe_restore_entails (sp0 v : BitVec 64) :
    ((sp0 - 4160#64) ↦₆₄ v) ∗ memRegion (sp0 - 4784#64) 624 ∗ memRegion (sp0 - 4152#64) 4088 ⊢
      memRegion (sp0 - 4784#64) 4720 := by
  have hmid :
      memRegion (sp0 - 4784#64) 4720 =
        memRegion (sp0 - 4784#64) 624 ∗ memRegion (sp0 - 4160#64) 8 ∗
          memRegion (sp0 - 4152#64) 4088 := by
    rw [memRegion_split' (b' := sp0 - 4160#64) (n := 624) (k := (4096 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp0 - 4152#64) (n := 8) (k := (4088 : Nat)) rfl (by bv_omega) (by decide)]
  rw [hmid]
  have hp := pointsTo64_entails_memRegion (sp0 - 4160#64) v
  exact entails_sub hp (by sep_frame) (by sep_frame)

private theorem seg1_prologue [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl21 b) (_hbase : blkPl21.base = b)
    (s0 : State) (F : SepProp)
    (hpc : s0.pc = b)
    (hrun : s0.status = .Running)
    (hsp0 : s0.spAligned = true) :
    SepWP (blkPC21.rebase b (fun _ => none)) (b + 0x002c#64) s0
      (stackAt s0.sp 5824 ∗ F)
      (fun s1 P1 =>
        s1.sp = s0.sp - 4784#64 ∧
        s1.readReg64 .fp = s0.sp - 64#64 ∧
        s1.readReg64 .x19 = s0.readReg64 .x0 ∧
        s1.readReg64 .x2 = s0.readReg64 .x2 ∧
        s1.readReg64 .x3 = s0.readReg64 .x3 ∧
        s1.readReg64 .x0 = 0#64 ∧
        s1.pstate = subsPState64 (s0.readReg64 .x1) 64#64 ∧
        UnspilledSaved s0 s1 ∧
        (P1 ⊢ SavedFrame s0.sp s0 ∗ memRegion (s0.sp - 4784#64) 4720 ∗
          stackAt (s0.sp - 4784#64) 1040 ∗ F)) := by
  rw [stackAt_prologue_split s0.sp]
  sep_frame_apply (sepWP_elim_cell8 (a := s0.sp - 4160#64)); intro p0
  sep_frame_apply (sepWP_elim_region32 (a := s0.sp - 64#64)); intro f0 f1 f2 f3
  sep_frame_apply (sepWP_elim_region32 (a := s0.sp - 32#64)); intro f4 f5 f6 f7
  have a1 : s0.sp - 64#64 + 8#64 = s0.sp - 56#64 := by bv_omega
  have a2 : s0.sp - 64#64 + 16#64 = s0.sp - 48#64 := by bv_omega
  have a3 : s0.sp - 64#64 + 24#64 = s0.sp - 40#64 := by bv_omega
  have a5 : s0.sp - 32#64 + 8#64 = s0.sp - 24#64 := by bv_omega
  have a6 : s0.sp - 32#64 + 16#64 = s0.sp - 16#64 := by bv_omega
  have a7 : s0.sp - 32#64 + 24#64 = s0.sp - 8#64 := by bv_omega
  rw [a1, a2, a3, a5, a6, a7]
  have hsp64 : ((s0.sp - 64#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 64#64 hsp0 (by decide)
  have hsp4160 : ((s0.sp - 64#64 - 4096#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub (s0.sp - 64#64) 4096#64 hsp64 (by decide)
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp,
      ⟨by simp, by simp, by simp, by simp, by simp [calleeSavedVRegs]⟩, ?_⟩
  unfold SavedFrame
  exact entails_sub (probe_restore_entails s0.sp 0#64) (by sep_frame) (by sep_frame)

/-! ## 4. Stack `pk` Assembly & Keccak Slice Setup (`+0x0038 → +0x0088`) -/

private theorem frame4720_memcpy_split (sp : BitVec 64) :
    memRegion sp 4720 =
      memRegion (sp + 16#64) 1152 ∗
      memRegion sp 16 ∗
      memRegion (sp + 1168#64) 3552 := by
  rw [memRegion_split' (b' := sp + 16#64) (n := 16) (k := (4704 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 1168#64) (n := 1152) (k := (3552 : Nat)) rfl (by bv_omega) (by decide)]
  exact sepProp_ext (by sep_frame) (by sep_frame)

private theorem frame3552_slices_split (sp : BitVec 64) :
    memRegion (sp + 1168#64) 3552 =
      memRegion (sp + 1168#64) 32 ∗
      memRegion (sp + 1200#64) 32 ∗
      memRegion (sp + 4688#64) 32 ∗
      memRegion (sp + 1232#64) 1504 ∗
      memRegion (sp + 2736#64) 32 ∗
      memRegion (sp + 2768#64) 1920 := by
  rw [memRegion_split' (b := sp + 1168#64) (b' := sp + 1200#64) (n := 32) (k := (3520 : Nat)) (by bv_omega) (by bv_omega) (by decide),
    memRegion_split' (b := sp + 1200#64) (b' := sp + 1232#64) (n := 32) (k := (3488 : Nat)) (by bv_omega) (by bv_omega) (by decide),
    memRegion_split' (b := sp + 1232#64) (b' := sp + 2736#64) (n := 1504) (k := (1984 : Nat)) (by bv_omega) (by bv_omega) (by decide),
    memRegion_split' (b := sp + 2736#64) (b' := sp + 2768#64) (n := 32) (k := (1952 : Nat)) (by bv_omega) (by bv_omega) (by decide),
    memRegion_split' (b := sp + 2768#64) (b' := sp + 4688#64) (n := 1920) (k := 32) (by bv_omega) (by bv_omega) (by decide)]
  exact sepProp_ext (by sep_frame) (by sep_frame)

private theorem seg1_memcpy_ek [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl21 b) (_hbase : blkPl21.base = b)
    (s0 s : State) (hdrA ekA : BitVec 64) (hdr ek : List (BitVec 8)) (R : SepProp)
    (hek : ek.length = 1152)
    (hpc : s.pc = b + 0x0038#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4784#64)
    (hsp0 : s0.spAligned = true)
    (hfp : s.readReg64 .fp = s0.sp - 64#64)
    (hx19 : s.readReg64 .x19 = hdrA)
    (hx2 : s.readReg64 .x2 = ekA)
    (hus : UnspilledSaved s0 s)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC21.rebase b (fun _ => none)) (b + 0x004c#64) s
      (SavedFrame s0.sp s0 ∗ memRegion (s0.sp - 4784#64) 4720 ∗ stackAt (s0.sp - 4784#64) 1040 ∗
        (hdrA ↦ₛ hdr) ∗ (ekA ↦ₛ ek) ∗ R)
      (fun sf Pf =>
        sf.sp = s0.sp - 4784#64 ∧
        sf.readReg64 .fp = s0.sp - 64#64 ∧
        sf.readReg64 .x19 = hdrA ∧
        sf.readReg64 .x23 = (s0.sp - 4784#64) + 16#64 ∧
        UnspilledSaved s0 sf ∧
        (Pf ⊢ SavedFrame s0.sp s0 ∗
          memRegion (s0.sp - 4784#64) 16 ∗
          (((s0.sp - 4784#64) + 16#64) ↦ₛ ek) ∗
          memRegion ((s0.sp - 4784#64) + 1168#64) 3552 ∗
          stackAt (s0.sp - 4784#64) 1040 ∗
          (hdrA ↦ₛ hdr) ∗ (ekA ↦ₛ ek) ∗ R)) := by
  have hsp_align : s.spAligned = true := by
    rw [State.spAligned, hsp]
    exact spAligned_sub s0.sp 4784#64 hsp0 (by decide)
  rw [frame4720_memcpy_split (s0.sp - 4784#64), ← hek]
  wp_cut_codeLoaded
  wp_steps
  wp_mlkem_call blk28_memcpy_ok (s0.sp - 4784#64 + 16#64, ekA, ek)
  have hus1 : UnspilledSaved s0 sf :=
    ⟨h_5.trans hus.1, h_6.trans hus.2.1, h_7.trans hus.2.2.1, h_8.trans hus.2.2.2.1,
      hvregs.trans hus.2.2.2.2⟩
  have ha16 : s0.sp - 4768#64 = (s0.sp - 4784#64) + 16#64 := by clear * -; bv_omega
  have ha1168 : s0.sp - 3616#64 = (s0.sp - 4784#64) + 1168#64 := by clear * -; bv_omega
  refine SepWP.done hpc_sf hrun_sf
    ⟨hsp_sf.trans hsp,
      hcs_sf.trans hfp,
      h.trans hx19,
      h_4.trans ha16,
      hus1,
      ?_⟩
  simp only [ha16, ha1168]
  sep_frame

private theorem seg1_prep_post_entails
    (s0 : State) (hdrA ekA sw0 sw1 sw2 sw3 : BitVec 64)
    (hdr ek : List (BitVec 8)) (R : SepProp)
    (hhdr : hdr.length = 64) (hek : ek.length = 1152)
    (hseed_pts : ∀ a : BitVec 64,
      (a ↦ₛ hdr.take 32) =
        (a ↦₆₄ sw0) ∗ ((a + 8#64) ↦₆₄ sw1) ∗ ((a + 16#64) ↦₆₄ sw2) ∗ ((a + 24#64) ↦₆₄ sw3))
    (hhdr_split :
      (hdrA ↦ₛ hdr) =
        ((hdrA ↦₆₄ sw0) ∗ ((hdrA + 8#64) ↦₆₄ sw1) ∗
          ((hdrA + 16#64) ↦₆₄ sw2) ∗ ((hdrA + 24#64) ↦₆₄ sw3)) ∗
          ((hdrA + 32#64) ↦ₛ hdr.drop 32)) :
    (((s0.sp - 4784#64) + 16#64) ↦ₛ ek) ∗
      (((s0.sp - 4784#64) + 1168#64) ↦₆₄ sw0) ∗ (((s0.sp - 4784#64) + 1176#64) ↦₆₄ sw1) ∗
      (((s0.sp - 4784#64) + 1184#64) ↦₆₄ sw2) ∗ (((s0.sp - 4784#64) + 1192#64) ↦₆₄ sw3) ∗
      (((s0.sp - 4784#64) + 1200#64) ↦₆₄ ((s0.sp - 4784#64) + 16#64)) ∗
      (((s0.sp - 4784#64) + 1208#64) ↦₆₄ 1184#64) ∗
      (((s0.sp - 4784#64) + 1216#64) ↦₆₄ ((s0.sp - 4784#64) + 16#64)) ∗
      (((s0.sp - 4784#64) + 1224#64) ↦₆₄ 1184#64) ∗
      ((s0.sp - 96#64) ↦₆₄ 0#64) ∗ ((s0.sp - 88#64) ↦₆₄ 0#64) ∗
      ((s0.sp - 80#64) ↦₆₄ 0#64) ∗ ((s0.sp - 72#64) ↦₆₄ 0#64) ∗
      (hdrA ↦₆₄ sw0) ∗ ((hdrA + 8#64) ↦₆₄ sw1) ∗
      ((hdrA + 16#64) ↦₆₄ sw2) ∗ ((hdrA + 24#64) ↦₆₄ sw3) ∗
      ((hdrA + 32#64) ↦ₛ hdr.drop 32) ∗
      memRegion ((s0.sp - 4784#64) + 1232#64) 1504 ∗
      memRegion ((s0.sp - 4784#64) + 2736#64) 32 ∗
      memRegion ((s0.sp - 4784#64) + 2768#64) 1920 ∗
      SavedFrame s0.sp s0 ∗
      memRegion (s0.sp - 4784#64) 16 ∗
      stackAt (s0.sp - 4784#64) 1040 ∗
      (ekA ↦ₛ ek) ∗ R ⊢
    Keccak2SlicesRW ((s0.sp - 4784#64) + 1200#64)
        ((s0.sp - 4784#64) + 16#64) ((s0.sp - 4784#64) + 16#64)
        (ek ++ hdr.take 32).length (ek ++ hdr.take 32).length ∗
      (((s0.sp - 4784#64) + 16#64) ↦ₛ (ek ++ hdr.take 32)) ∗
      memRegion ((s0.sp - 4784#64) + 4688#64) 32 ∗
      memRegion ((s0.sp - 4784#64) + 2736#64) 32 ∗
      stackAt (s0.sp - 4784#64) 1040 ∗
      SavedFrame s0.sp s0 ∗
      memRegion (s0.sp - 4784#64) 16 ∗
      memRegion ((s0.sp - 4784#64) + 1232#64) 1504 ∗
      memRegion ((s0.sp - 4784#64) + 2768#64) 1920 ∗
      (hdrA ↦ₛ hdr) ∗ (ekA ↦ₛ ek) ∗ R := by
  have hd1 : (s0.sp - 4784#64) + 1168#64 + 8#64 = (s0.sp - 4784#64) + 1176#64 := by bv_omega
  have hd2 : (s0.sp - 4784#64) + 1168#64 + 16#64 = (s0.sp - 4784#64) + 1184#64 := by bv_omega
  have hd3 : (s0.sp - 4784#64) + 1168#64 + 24#64 = (s0.sp - 4784#64) + 1192#64 := by bv_omega
  have he1 : (s0.sp - 4784#64) + 1200#64 + 8#64 = (s0.sp - 4784#64) + 1208#64 := by bv_omega
  have he2 : (s0.sp - 4784#64) + 1200#64 + 16#64 = (s0.sp - 4784#64) + 1216#64 := by bv_omega
  have he3 : (s0.sp - 4784#64) + 1200#64 + 24#64 = (s0.sp - 4784#64) + 1224#64 := by bv_omega
  have hf0 : (s0.sp - 4784#64) + 4688#64 = s0.sp - 96#64 := by bv_omega
  have hf1 : (s0.sp - 4784#64) + 4688#64 + 8#64 = s0.sp - 88#64 := by bv_omega
  have hf2 : (s0.sp - 4784#64) + 4688#64 + 16#64 = s0.sp - 80#64 := by bv_omega
  have hf3 : (s0.sp - 4784#64) + 4688#64 + 24#64 = s0.sp - 72#64 := by bv_omega
  have hpk_len : (ek ++ hdr.take 32).length = 1184 := by simp [hek, hhdr]
  have hpk_pts :
      (((s0.sp - 4784#64) + 16#64) ↦ₛ ek) ∗
        (((s0.sp - 4784#64) + 1168#64) ↦₆₄ sw0) ∗ (((s0.sp - 4784#64) + 1176#64) ↦₆₄ sw1) ∗
        (((s0.sp - 4784#64) + 1184#64) ↦₆₄ sw2) ∗ (((s0.sp - 4784#64) + 1192#64) ↦₆₄ sw3) ⊢
      (((s0.sp - 4784#64) + 16#64) ↦ₛ (ek ++ hdr.take 32)) := by
    have h1168 : (s0.sp - 4784#64) + 16#64 + BitVec.ofNat 64 ek.length =
        (s0.sp - 4784#64) + 1168#64 := by
      rw [hek]; bv_omega
    have hseed_sp :
        (((s0.sp - 4784#64) + 1168#64) ↦ₛ hdr.take 32) =
          (((s0.sp - 4784#64) + 1168#64) ↦₆₄ sw0) ∗ (((s0.sp - 4784#64) + 1176#64) ↦₆₄ sw1) ∗
            (((s0.sp - 4784#64) + 1184#64) ↦₆₄ sw2) ∗ (((s0.sp - 4784#64) + 1192#64) ↦₆₄ sw3) := by
      simpa only [hd1, hd2, hd3, sepConj_assoc] using hseed_pts ((s0.sp - 4784#64) + 1168#64)
    rw [pointsToBytes_append, h1168, hseed_sp]
    sep_frame
  have hout0 :
      ((s0.sp - 96#64) ↦₆₄ 0#64) ∗ ((s0.sp - 88#64) ↦₆₄ 0#64) ∗
        ((s0.sp - 80#64) ↦₆₄ 0#64) ∗ ((s0.sp - 72#64) ↦₆₄ 0#64) ⊢
      memRegion ((s0.sp - 4784#64) + 4688#64) 32 := by
    have h0 := cells32_entails_memRegion ((s0.sp - 4784#64) + 4688#64) 0#64 0#64 0#64 0#64
    rw [hf1, hf2, hf3] at h0
    conv at h0 => lhs; rw [hf0]
    exact h0
  have hhdr_back :
      ((hdrA ↦₆₄ sw0) ∗ ((hdrA + 8#64) ↦₆₄ sw1) ∗
        ((hdrA + 16#64) ↦₆₄ sw2) ∗ ((hdrA + 24#64) ↦₆₄ sw3)) ∗
        ((hdrA + 32#64) ↦ₛ hdr.drop 32) ⊢ (hdrA ↦ₛ hdr) := by
    rw [hhdr_split]
    exact Entails.refl _
  have hsl :
      (((s0.sp - 4784#64) + 1200#64) ↦₆₄ ((s0.sp - 4784#64) + 16#64)) ∗
        (((s0.sp - 4784#64) + 1208#64) ↦₆₄ 1184#64) ∗
        (((s0.sp - 4784#64) + 1216#64) ↦₆₄ ((s0.sp - 4784#64) + 16#64)) ∗
        (((s0.sp - 4784#64) + 1224#64) ↦₆₄ 1184#64) ⊢
      Keccak2SlicesRW ((s0.sp - 4784#64) + 1200#64)
        ((s0.sp - 4784#64) + 16#64) ((s0.sp - 4784#64) + 16#64)
        (ek ++ hdr.take 32).length (ek ++ hdr.take 32).length := by
    unfold Keccak2SlicesRW
    rw [hpk_len, he1, he2, he3]
    exact Entails.refl _
  exact entails_sub hpk_pts (by sep_frame)
    (entails_sub hout0 (by sep_frame)
      (entails_sub hhdr_back (by sep_frame)
        (entails_sub hsl (by sep_frame) (by sep_frame))))

private theorem seg1_prep_slices [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl21 b) (_hbase : blkPl21.base = b)
    (s0 sf : State) (hdrA ekA : BitVec 64) (hdr ek : List (BitVec 8)) (R : SepProp)
    (hhdr : hdr.length = 64) (hek : ek.length = 1152)
    (hpc : sf.pc = b + 0x004c#64)
    (hrun : sf.status = .Running)
    (hsp : sf.sp = s0.sp - 4784#64)
    (hsp0 : s0.spAligned = true)
    (hfp : sf.readReg64 .fp = s0.sp - 64#64)
    (hx19 : sf.readReg64 .x19 = hdrA)
    (hx23 : sf.readReg64 .x23 = (s0.sp - 4784#64) + 16#64)
    (hus : UnspilledSaved s0 sf) :
    SepWP (blkPC21.rebase b (fun _ => none)) (b + 0x0088#64) sf
      (SavedFrame s0.sp s0 ∗
        memRegion (s0.sp - 4784#64) 16 ∗
        (((s0.sp - 4784#64) + 16#64) ↦ₛ ek) ∗
        memRegion ((s0.sp - 4784#64) + 1168#64) 3552 ∗
        stackAt (s0.sp - 4784#64) 1040 ∗
        (hdrA ↦ₛ hdr) ∗ (ekA ↦ₛ ek) ∗ R)
      (fun sm Pm =>
        sm.sp = s0.sp - 4784#64 ∧
        sm.readReg64 .fp = s0.sp - 64#64 ∧
        sm.readReg64 .x19 = hdrA ∧
        sm.readReg64 .x20 = (s0.sp - 4784#64) + 1200#64 ∧
        sm.readReg64 .x22 = (s0.sp - 4784#64) + 2736#64 ∧
        sm.readReg64 .x23 = (s0.sp - 4784#64) + 16#64 ∧
        sm.readReg64 .x0 = (s0.sp - 4784#64) + 1200#64 ∧
        sm.readReg64 .x1 = (s0.sp - 4784#64) + 4688#64 ∧
        sm.readReg64 .x2 = (s0.sp - 4784#64) + 2736#64 ∧
        UnspilledSaved s0 sm ∧
        (Pm ⊢ Keccak2SlicesRW ((s0.sp - 4784#64) + 1200#64)
            ((s0.sp - 4784#64) + 16#64) ((s0.sp - 4784#64) + 16#64)
            (ek ++ hdr.take 32).length (ek ++ hdr.take 32).length ∗
          (((s0.sp - 4784#64) + 16#64) ↦ₛ (ek ++ hdr.take 32)) ∗
          memRegion ((s0.sp - 4784#64) + 4688#64) 32 ∗
          memRegion ((s0.sp - 4784#64) + 2736#64) 32 ∗
          stackAt (s0.sp - 4784#64) 1040 ∗
          SavedFrame s0.sp s0 ∗
          memRegion (s0.sp - 4784#64) 16 ∗
          memRegion ((s0.sp - 4784#64) + 1232#64) 1504 ∗
          memRegion ((s0.sp - 4784#64) + 2768#64) 1920 ∗
          (hdrA ↦ₛ hdr) ∗ (ekA ↦ₛ ek) ∗ R)) := by
  have hsp_sf_align : sf.spAligned = true := by
    rw [State.spAligned, hsp]
    exact spAligned_sub s0.sp 4784#64 hsp0 (by decide)
  have hseed_len : (hdr.take 32).length = 32 := by simp [hhdr]
  obtain ⟨sw0, sw1, sw2, sw3, _, hseed_pts⟩ := exists_unpack64_of_length_32 hseed_len
  have hhdr_split :
      (hdrA ↦ₛ hdr) =
        ((hdrA ↦₆₄ sw0) ∗ ((hdrA + 8#64) ↦₆₄ sw1) ∗
          ((hdrA + 16#64) ↦₆₄ sw2) ∗ ((hdrA + 24#64) ↦₆₄ sw3)) ∗
          ((hdrA + 32#64) ↦ₛ hdr.drop 32) := by
    conv_lhs => rw [← List.take_append_drop 32 hdr]
    rw [pointsToBytes_append, hseed_len, hseed_pts hdrA]
  rw [frame3552_slices_split (s0.sp - 4784#64)]
  sep_frame_apply (sepWP_elim_region32 (a := (s0.sp - 4784#64) + 1168#64)); intro c0 c1 c2 c3
  sep_frame_apply (sepWP_elim_region32 (a := (s0.sp - 4784#64) + 1200#64)); intro k0 k1 k2 k3
  sep_frame_apply (sepWP_elim_region32 (a := (s0.sp - 4784#64) + 4688#64)); intro z0 z1 z2 z3
  rw [hhdr_split]
  have hd1 : (s0.sp - 4784#64) + 1168#64 + 8#64 = (s0.sp - 4784#64) + 1176#64 := by clear * -; bv_omega
  have hd2 : (s0.sp - 4784#64) + 1168#64 + 16#64 = (s0.sp - 4784#64) + 1184#64 := by clear * -; bv_omega
  have hd3 : (s0.sp - 4784#64) + 1168#64 + 24#64 = (s0.sp - 4784#64) + 1192#64 := by clear * -; bv_omega
  have he1 : (s0.sp - 4784#64) + 1200#64 + 8#64 = (s0.sp - 4784#64) + 1208#64 := by clear * -; bv_omega
  have he2 : (s0.sp - 4784#64) + 1200#64 + 16#64 = (s0.sp - 4784#64) + 1216#64 := by clear * -; bv_omega
  have he3 : (s0.sp - 4784#64) + 1200#64 + 24#64 = (s0.sp - 4784#64) + 1224#64 := by clear * -; bv_omega
  have hf0 : (s0.sp - 4784#64) + 4688#64 = s0.sp - 96#64 := by clear * -; bv_omega
  have hf1 : (s0.sp - 4784#64) + 4688#64 + 8#64 = s0.sp - 88#64 := by clear * -; bv_omega
  have hf2 : (s0.sp - 4784#64) + 4688#64 + 16#64 = s0.sp - 80#64 := by clear * -; bv_omega
  have hf3 : (s0.sp - 4784#64) + 4688#64 + 24#64 = s0.sp - 72#64 := by clear * -; bv_omega
  rw [hd1, hd2, hd3, he1, he2, he3, hf1, hf2, hf3, hf0]
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simp [hfp], by simp [hx19],
      by simp only [wp_norm, arm64_norm],
      by simp only [wp_norm, arm64_norm],
      by simp [hx23],
      by simp only [wp_norm, arm64_norm],
      by simp only [wp_norm, arm64_norm],
      by simp only [wp_norm, arm64_norm],
      ⟨by simp [hus.1], by simp [hus.2.1], by simp [hus.2.2.1], by simp [hus.2.2.2.1],
        by simp [calleeSavedVRegs, hus.2.2.2.2]⟩,
      ?_⟩
  have ha16 : s0.sp - 4768#64 = (s0.sp - 4784#64) + 16#64 := by clear * -; bv_omega
  rw [ha16]
  conv_rhs => rw [← hf0, ← hhdr_split]
  exact Entails.trans (by sep_frame)
    (seg1_prep_post_entails s0 hdrA ekA sw0 sw1 sw2 sw3 hdr ek R hhdr hek hseed_pts hhdr_split)

private theorem seg1_prep_keccak [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl21 b) (hbase : blkPl21.base = b)
    (s0 s : State) (hdrA ekA : BitVec 64) (hdr ek : List (BitVec 8)) (R : SepProp)
    (hhdr : hdr.length = 64) (hek : ek.length = 1152)
    (hpc : s.pc = b + 0x0038#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4784#64)
    (hsp0 : s0.spAligned = true)
    (hfp : s.readReg64 .fp = s0.sp - 64#64)
    (hx19 : s.readReg64 .x19 = hdrA)
    (hx2 : s.readReg64 .x2 = ekA)
    (hus : UnspilledSaved s0 s)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hro : MlKemRoOk mlkemMpl s.mem) :
    SepWP (blkPC21.rebase b (fun _ => none)) (b + 0x0088#64) s
      (SavedFrame s0.sp s0 ∗ memRegion (s0.sp - 4784#64) 4720 ∗ stackAt (s0.sp - 4784#64) 1040 ∗
        (hdrA ↦ₛ hdr) ∗ (ekA ↦ₛ ek) ∗ R)
      (fun sm Pm =>
        sm.sp = s0.sp - 4784#64 ∧
        sm.readReg64 .fp = s0.sp - 64#64 ∧
        sm.readReg64 .x19 = hdrA ∧
        sm.readReg64 .x20 = (s0.sp - 4784#64) + 1200#64 ∧
        sm.readReg64 .x22 = (s0.sp - 4784#64) + 2736#64 ∧
        sm.readReg64 .x23 = (s0.sp - 4784#64) + 16#64 ∧
        sm.readReg64 .x0 = (s0.sp - 4784#64) + 1200#64 ∧
        sm.readReg64 .x1 = (s0.sp - 4784#64) + 4688#64 ∧
        sm.readReg64 .x2 = (s0.sp - 4784#64) + 2736#64 ∧
        UnspilledSaved s0 sm ∧
        (Pm ⊢ Keccak2SlicesRW ((s0.sp - 4784#64) + 1200#64)
            ((s0.sp - 4784#64) + 16#64) ((s0.sp - 4784#64) + 16#64)
            (ek ++ hdr.take 32).length (ek ++ hdr.take 32).length ∗
          (((s0.sp - 4784#64) + 16#64) ↦ₛ (ek ++ hdr.take 32)) ∗
          memRegion ((s0.sp - 4784#64) + 4688#64) 32 ∗
          memRegion ((s0.sp - 4784#64) + 2736#64) 32 ∗
          stackAt (s0.sp - 4784#64) 1040 ∗
          SavedFrame s0.sp s0 ∗
          memRegion (s0.sp - 4784#64) 16 ∗
          memRegion ((s0.sp - 4784#64) + 1232#64) 1504 ∗
          memRegion ((s0.sp - 4784#64) + 2768#64) 1920 ∗
          (hdrA ↦ₛ hdr) ∗ (ekA ↦ₛ ek) ∗ R)) := by
  refine sepWP_seq_env hcl hro
    (seg1_memcpy_ek hb hbase s0 s hdrA ekA hdr ek R hek hpc hrun hsp hsp0 hfp hx19 hx2 hus hcl) ?_
  intro sf Pf hpcf hrunf _ _ ⟨hspf, hfpf, hx19f, hx23f, husf, hPf⟩
  refine SepWP.weaken_pre hPf ?_
  exact seg1_prep_slices hb hbase s0 sf hdrA ekA hdr ek R hhdr hek
    hpcf hrunf hspf hsp0 hfpf hx19f hx23f husf

/-! ## 5. `B02` (`keccak2::<136, 6>`) Call & Digest Comparison (`+0x0088 .. +0x00b0`) -/

private theorem frame3520_restore_entails (sp : BitVec 64) (msg : List (BitVec 8)) :
    Keccak2SlicesRW (sp + 1200#64) (sp + 16#64) (sp + 16#64) msg.length msg.length ∗
      memRegion (sp + 1232#64) 1504 ∗
      ((sp + 2736#64) ↦ₛ sha3_256List msg) ∗
      memRegion (sp + 2768#64) 1920 ∗
      ((sp + 4688#64) ↦ₛ sha3_256List msg) ⊢
      memRegion (sp + 1200#64) 3520 := by
  have hsplit :
      memRegion (sp + 1200#64) 3520 =
        memRegion (sp + 1200#64) 32 ∗
        memRegion (sp + 1232#64) 1504 ∗
        memRegion (sp + 2736#64) 32 ∗
        memRegion (sp + 2768#64) 1920 ∗
        memRegion (sp + 4688#64) 32 := by
    rw [memRegion_split' (b' := sp + 1232#64) (n := 32) (k := (3488 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp + 2736#64) (n := 1504) (k := (1984 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp + 2768#64) (n := 32) (k := (1952 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp + 4688#64) (n := 1920) (k := 32) rfl (by bv_omega) (by decide)]
  rw [hsplit]
  have hsl :
      Keccak2SlicesRW (sp + 1200#64) (sp + 16#64) (sp + 16#64) msg.length msg.length ⊢
        memRegion (sp + 1200#64) 32 := by
    unfold Keccak2SlicesRW
    exact cells32_entails_memRegion (sp + 1200#64) _ _ _ _
  have ho1 : ((sp + 2736#64) ↦ₛ sha3_256List msg) ⊢ memRegion (sp + 2736#64) 32 := by
    simpa [sha3_256List_length] using pointsToBytes_entails_memRegion (sp + 2736#64) (sha3_256List msg)
  have ho0 : ((sp + 4688#64) ↦ₛ sha3_256List msg) ⊢ memRegion (sp + 4688#64) 32 := by
    simpa [sha3_256List_length] using pointsToBytes_entails_memRegion (sp + 4688#64) (sha3_256List msg)
  exact entails_sub hsl (by sep_frame)
    (entails_sub ho1 (by sep_frame)
      (entails_sub ho0 (by sep_frame) (by sep_frame)))

private theorem frame4720_from_pk_entails (sp : BitVec 64) (pk : List (BitVec 8))
    (hpk : pk.length = 1184) :
    memRegion sp 16 ∗ ((sp + 16#64) ↦ₛ pk) ∗ memRegion (sp + 1200#64) 3520 ⊢
      memRegion sp 4720 := by
  have hsplit :
      memRegion sp 4720 =
        memRegion sp 16 ∗ memRegion (sp + 16#64) 1184 ∗ memRegion (sp + 1200#64) 3520 := by
    rw [memRegion_split' (b' := sp + 16#64) (n := 16) (k := (4704 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp + 1200#64) (n := 1184) (k := (3520 : Nat)) rfl (by bv_omega) (by decide)]
  rw [hsplit]
  have hp : ((sp + 16#64) ↦ₛ pk) ⊢ memRegion (sp + 16#64) 1184 := by
    simpa [hpk] using pointsToBytes_entails_memRegion (sp + 16#64) pk
  exact entails_sub hp (by sep_frame) (by sep_frame)

/-- Invariant entering `Seg2` at `b + 0x00b0#64`. -/
@[expose] def Seg2Pre (s0 sm : State) (hdr ek : List (BitVec 8)) : Prop :=
  hdr.length = 64 ∧
  ek.length = 1152 ∧
  sha3_256List (ek ++ hdr.take 32) = (hdr.drop 32).take 32 ∧
  sm.sp = s0.sp - 4784#64 ∧
  UnspilledSaved s0 sm ∧
  sm.readReg64 .x20 = (s0.sp - 4784#64) + 1200#64 ∧
  sm.readReg64 .x22 = (s0.sp - 4784#64) + 2736#64 ∧
  sm.readReg64 .x23 = (s0.sp - 4784#64) + 16#64

/-- Spatial assertion entering `Seg2` at `b + 0x00b0#64`. -/
@[expose] def Seg2Spatial (s0 : State) (hdrA : BitVec 64) (hdr : List (BitVec 8))
    (ekA : BitVec 64) (ek : List (BitVec 8)) (R : SepProp) : SepProp :=
  let sp := s0.sp - 4784#64
  SavedFrame s0.sp s0 ∗
    memRegion sp 16 ∗
    ((sp + 16#64) ↦ₛ (ek ++ hdr.take 32)) ∗
    memRegion (sp + 1200#64) 3520 ∗
    stackAt sp 1040 ∗
    (hdrA ↦ₛ hdr) ∗ (ekA ↦ₛ ek) ∗ R

private theorem seg1_keccak_call [MlKemPlacement]
    (hkeccak : MlKemBlockOk 2 keccak2_136_6_RW1Spec)
    {b : BitVec 64} (_hb : MlKemBase blkPl21 b) (_hbase : blkPl21.base = b)
    (s0 sm : State) (hdrA : BitVec 64) (hdr ek : List (BitVec 8)) (F : SepProp)
    (hhdr : hdr.length = 64) (hek : ek.length = 1152)
    (hpc : sm.pc = b + 0x0088#64)
    (hrun : sm.status = .Running)
    (hsp : sm.sp = s0.sp - 4784#64)
    (hsp0 : s0.spAligned = true)
    (hfp : sm.readReg64 .fp = s0.sp - 64#64)
    (hx19 : sm.readReg64 .x19 = hdrA)
    (hx20 : sm.readReg64 .x20 = (s0.sp - 4784#64) + 1200#64)
    (hx22 : sm.readReg64 .x22 = (s0.sp - 4784#64) + 2736#64)
    (hx23 : sm.readReg64 .x23 = (s0.sp - 4784#64) + 16#64)
    (hx0 : sm.readReg64 .x0 = (s0.sp - 4784#64) + 1200#64)
    (hx1 : sm.readReg64 .x1 = (s0.sp - 4784#64) + 4688#64)
    (hx2 : sm.readReg64 .x2 = (s0.sp - 4784#64) + 2736#64)
    (hus : UnspilledSaved s0 sm)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl sm.mem)
    (hro : MlKemRoOk mlkemMpl sm.mem) :
    SepWP (blkPC21.rebase b (fun _ => none)) (b + 0x008c#64) sm
      (Keccak2SlicesRW ((s0.sp - 4784#64) + 1200#64)
          ((s0.sp - 4784#64) + 16#64) ((s0.sp - 4784#64) + 16#64)
          (ek ++ hdr.take 32).length (ek ++ hdr.take 32).length ∗
        (((s0.sp - 4784#64) + 16#64) ↦ₛ (ek ++ hdr.take 32)) ∗
        memRegion ((s0.sp - 4784#64) + 4688#64) 32 ∗
        memRegion ((s0.sp - 4784#64) + 2736#64) 32 ∗
        stackAt (s0.sp - 4784#64) 1040 ∗ F)
      (fun sk Pk =>
        sk.sp = s0.sp - 4784#64 ∧
        sk.readReg64 .fp = s0.sp - 64#64 ∧
        sk.readReg64 .x19 = hdrA ∧
        sk.readReg64 .x20 = (s0.sp - 4784#64) + 1200#64 ∧
        sk.readReg64 .x22 = (s0.sp - 4784#64) + 2736#64 ∧
        sk.readReg64 .x23 = (s0.sp - 4784#64) + 16#64 ∧
        UnspilledSaved s0 sk ∧
        (Pk ⊢ (((s0.sp - 4784#64) + 4688#64) ↦ₛ sha3_256List (ek ++ hdr.take 32)) ∗
          Keccak2SlicesRW ((s0.sp - 4784#64) + 1200#64)
            ((s0.sp - 4784#64) + 16#64) ((s0.sp - 4784#64) + 16#64)
            (ek ++ hdr.take 32).length (ek ++ hdr.take 32).length ∗
          (((s0.sp - 4784#64) + 2736#64) ↦ₛ sha3_256List (ek ++ hdr.take 32)) ∗
          (((s0.sp - 4784#64) + 16#64) ↦ₛ (ek ++ hdr.take 32)) ∗
          stackAt (s0.sp - 4784#64) 1040 ∗ F)) := by
  have hsp_align : sm.spAligned = true := by
    rw [State.spAligned, hsp]
    exact spAligned_sub s0.sp 4784#64 hsp0 (by decide)
  have hpk_lt : (ek ++ hdr.take 32).length < 2 ^ 32 := by
    simp [hek, hhdr]
  have ha16 : s0.sp - 4768#64 = (s0.sp - 4784#64) + 16#64 := by clear * -; bv_omega
  have ha1200 : s0.sp - 3584#64 = (s0.sp - 4784#64) + 1200#64 := by clear * -; bv_omega
  have ha2736 : s0.sp - 2048#64 = (s0.sp - 4784#64) + 2736#64 := by clear * -; bv_omega
  have ha4688 : s0.sp - 96#64 = (s0.sp - 4784#64) + 4688#64 := by clear * -; bv_omega
  have hx0' : sm.readReg64 (.gpr 0#5) = s0.sp - 3584#64 := hx0.trans ha1200.symm
  have hx1' : sm.readReg64 (.gpr 1#5) = s0.sp - 96#64 := hx1.trans ha4688.symm
  have hx2' : sm.readReg64 (.gpr 2#5) = s0.sp - 2048#64 := hx2.trans ha2736.symm
  wp_step
  have hro' : MlKemRoOk mlkemMpl ((sm.writeReg64 .lr (b + 0x008c#64)).setPC (mlkemMpl.base 2)).mem :=
    hro
  wp_mlkem_call hkeccak
    (s0.sp - 4784#64 + 1200#64, s0.sp - 4784#64 + 16#64,
     s0.sp - 4784#64 + 4688#64, s0.sp - 4784#64 + 2736#64, ek ++ hdr.take 32)
  have hus_sf : UnspilledSaved s0 sf :=
    ⟨h_5.trans hus.1, h_6.trans hus.2.1, h_7.trans hus.2.2.1, h_8.trans hus.2.2.2.1,
      hvregs.trans hus.2.2.2.2⟩
  refine SepWP.done hpc_sf hrun_sf
    ⟨hsp_sf.trans hsp,
      hcs_sf.trans hfp,
      h.trans hx19,
      h_1.trans hx20,
      h_3.trans hx22,
      h_4.trans hx23,
      hus_sf,
      ?_⟩
  simp only [ha16, ha1200, ha2736, ha4688]
  sep_frame

private theorem seg1_cmp_and_branch [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl21 b) (hbase : blkPl21.base = b)
    (s0 sk : State) (hdrA ekA : BitVec 64) (hdr ek : List (BitVec 8)) (R : SepProp)
    (hhdr : hdr.length = 64) (hek : ek.length = 1152)
    (hpc : sk.pc = b + 0x008c#64)
    (hrun : sk.status = .Running)
    (hsp : sk.sp = s0.sp - 4784#64)
    (hsp0 : s0.spAligned = true)
    (hfp : sk.readReg64 .fp = s0.sp - 64#64)
    (hx19 : sk.readReg64 .x19 = hdrA)
    (hx20 : sk.readReg64 .x20 = (s0.sp - 4784#64) + 1200#64)
    (hx22 : sk.readReg64 .x22 = (s0.sp - 4784#64) + 2736#64)
    (hx23 : sk.readReg64 .x23 = (s0.sp - 4784#64) + 16#64)
    (hus : UnspilledSaved s0 sk)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl sk.mem)
    (hro : MlKemRoOk mlkemMpl sk.mem)
    (hcont : ∀ sm : State,
      sm.pc = b + 0x00b0#64 → sm.status = .Running →
      mlkemMultiLib.CodeLoaded mlkemMpl sm.mem → MlKemRoOk mlkemMpl sm.mem →
      Seg2Pre s0 sm hdr ek →
      SepWP (blkPC21.rebase b (fun _ => none)) (s0.readReg64 .lr) sm
        (Seg2Spatial s0 hdrA hdr ekA ek R)
        (ValidatePkPost s0 hdrA hdr ekA ek R)) :
    let sp := s0.sp - 4784#64
    let pk := ek ++ hdr.take 32
    SepWP (blkPC21.rebase b (fun _ => none)) (s0.readReg64 .lr) sk
      (((sp + 4688#64) ↦ₛ sha3_256List pk) ∗
        (hdrA ↦ₛ hdr) ∗
        Keccak2SlicesRW (sp + 1200#64) (sp + 16#64) (sp + 16#64) pk.length pk.length ∗
        memRegion (sp + 1232#64) 1504 ∗
        ((sp + 2736#64) ↦ₛ sha3_256List pk) ∗
        memRegion (sp + 2768#64) 1920 ∗
        SavedFrame s0.sp s0 ∗
        memRegion sp 16 ∗
        ((sp + 16#64) ↦ₛ pk) ∗
        stackAt sp 1040 ∗
        (ekA ↦ₛ ek) ∗ R)
      (ValidatePkPost s0 hdrA hdr ekA ek R) := by
  intro sp pk
  have hpkh_eq : (hdr.drop 32).take 32 = hdr.drop 32 := by
    rw [List.take_of_length_le (by simp [hhdr])]
  have hpkh_len : (hdr.drop 32).length = 32 := by simp [hhdr]
  have hdig_len : (sha3_256List pk).length = 32 := sha3_256List_length pk
  obtain ⟨dw0, dw1, dw2, dw3, hdig_words, hdig_pts⟩ := exists_unpack64_of_length_32 hdig_len
  obtain ⟨hw0, hw1, hw2, hw3, hpkh_words, hpkh_pts⟩ := exists_unpack64_of_length_32 hpkh_len
  have hhdr_split :
      (hdrA ↦ₛ hdr) =
        (hdrA ↦ₛ hdr.take 32) ∗
          ((hdrA + 32#64) ↦₆₄ hw0) ∗ ((hdrA + 40#64) ↦₆₄ hw1) ∗
          ((hdrA + 48#64) ↦₆₄ hw2) ∗ ((hdrA + 56#64) ↦₆₄ hw3) := by
    conv_lhs => rw [← List.take_append_drop 32 hdr]
    have htl : (hdr.take 32).length = 32 := by simp [hhdr]
    have a1 : hdrA + 32#64 + 8#64 = hdrA + 40#64 := by bv_omega
    have a2 : hdrA + 32#64 + 16#64 = hdrA + 48#64 := by bv_omega
    have a3 : hdrA + 32#64 + 24#64 = hdrA + 56#64 := by bv_omega
    rw [pointsToBytes_append, htl, hpkh_pts (hdrA + 32#64), a1, a2, a3]
  have hdig_split :
      ((sp + 4688#64) ↦ₛ sha3_256List pk) =
        ((s0.sp - 96#64) ↦₆₄ dw0) ∗ ((s0.sp - 88#64) ↦₆₄ dw1) ∗
          ((s0.sp - 80#64) ↦₆₄ dw2) ∗ ((s0.sp - 72#64) ↦₆₄ dw3) := by
    have f0' : sp + 4688#64 = s0.sp - 96#64 := by dsimp [sp]; bv_omega
    have f1' : s0.sp - 96#64 + 8#64 = s0.sp - 88#64 := by bv_omega
    have f2' : s0.sp - 96#64 + 16#64 = s0.sp - 80#64 := by bv_omega
    have f3' : s0.sp - 96#64 + 24#64 = s0.sp - 72#64 := by bv_omega
    rw [f0', hdig_pts (s0.sp - 96#64), f1', f2', f3']
  rw [hdig_split, hhdr_split]
  simp only [sepConj_assoc]
  -- Step `+0x008c .. +0x00ac` (loads, compares, and `b.ne +0x0820`; `sk.mem` unchanged):
  wp_steps 9
  -- Fold `hdr` and `memRegion (sp + 1200#64) 3520` back before `+0x00ac` (`b.ne +0x0820`):
  refine SepWP.weaken_pre
    (show ((s0.sp - 96#64) ↦₆₄ dw0) ∗ ((s0.sp - 88#64) ↦₆₄ dw1) ∗
        ((s0.sp - 80#64) ↦₆₄ dw2) ∗ ((s0.sp - 72#64) ↦₆₄ dw3) ∗
        (hdrA ↦ₛ hdr.take 32) ∗
        ((hdrA + 32#64) ↦₆₄ hw0) ∗ ((hdrA + 40#64) ↦₆₄ hw1) ∗
        ((hdrA + 48#64) ↦₆₄ hw2) ∗ ((hdrA + 56#64) ↦₆₄ hw3) ∗
        Keccak2SlicesRW (sp + 1200#64) (sp + 16#64) (sp + 16#64) pk.length pk.length ∗
        memRegion (sp + 1232#64) 1504 ∗
        ((sp + 2736#64) ↦ₛ sha3_256List pk) ∗
        memRegion (sp + 2768#64) 1920 ∗
        SavedFrame s0.sp s0 ∗ memRegion sp 16 ∗ ((sp + 16#64) ↦ₛ pk) ∗
        stackAt sp 1040 ∗ (ekA ↦ₛ ek) ∗ R ⊢
      Seg2Spatial s0 hdrA hdr ekA ek R by
      unfold Seg2Spatial
      dsimp only
      have hd_back :
          ((s0.sp - 96#64) ↦₆₄ dw0) ∗ ((s0.sp - 88#64) ↦₆₄ dw1) ∗
            ((s0.sp - 80#64) ↦₆₄ dw2) ∗ ((s0.sp - 72#64) ↦₆₄ dw3) ⊢
          ((sp + 4688#64) ↦ₛ sha3_256List pk) := by
        rw [hdig_split]; exact Entails.refl _
      have hh_back :
          (hdrA ↦ₛ hdr.take 32) ∗
            ((hdrA + 32#64) ↦₆₄ hw0) ∗ ((hdrA + 40#64) ↦₆₄ hw1) ∗
            ((hdrA + 48#64) ↦₆₄ hw2) ∗ ((hdrA + 56#64) ↦₆₄ hw3) ⊢
          (hdrA ↦ₛ hdr) := by
        rw [hhdr_split]; exact Entails.refl _
      have hf3520 := frame3520_restore_entails sp pk
      dsimp only [sp, pk] at hd_back hf3520 ⊢
      exact entails_sub hd_back (by sep_frame)
        (entails_sub hh_back (by sep_frame)
          (entails_sub hf3520 (by sep_frame) (by sep_frame)))) ?_
  wp_if hcond
  · -- Branch taken (`b.ne +0x0820`): digest mismatch.
    have hwords_ne : ¬(dw0 = hw0 ∧ dw1 = hw1 ∧ dw2 = hw2 ∧ dw3 = hw3) := by
      rintro ⟨rfl, rfl, rfl, rfl⟩
      simp at hcond
    have hhash_ne : sha3_256List pk ≠ (hdr.drop 32).take 32 := by
      rw [hpkh_eq, hdig_words, hpkh_words, Ne, unpack64_quad_eq_iff]
      exact hwords_ne
    have hpk_len : pk.length = 1184 := by simp [pk, hek, hhdr]
    refine SepWP.weaken_pre
      (show Seg2Spatial s0 hdrA hdr ekA ek R ⊢
        SavedFrame s0.sp s0 ∗ memRegion sp 4720 ∗ stackAt sp 1040 ∗
          ((hdrA ↦ₛ hdr) ∗ (ekA ↦ₛ ek) ∗ R) by
        unfold Seg2Spatial
        have hf4720 := frame4720_from_pk_entails sp pk hpk_len
        dsimp only [sp, pk] at hf4720 ⊢
        exact entails_sub hf4720 (by sep_frame) (by sep_frame)) ?_
    refine sepWP_mono_ret ?_
      (seg_ret_err2 hb hbase s0 _ ((hdrA ↦ₛ hdr) ∗ (ekA ↦ₛ ek) ∗ R)
        (by simp [wp_norm, arm64_norm]) (by simp [hrun]) (by simp [hsp]) hsp0
        ⟨by simp [hus.1], by simp [hus.2.1], by simp [hus.2.2.1], by simp [hus.2.2.2.1],
          by simp [calleeSavedVRegs, hus.2.2.2.2]⟩)
    rw [validPkBytes_false_of_hash_ne hhdr hek hhash_ne]
    decide
  · -- Branch not taken (`b + 0x00b0`): digest matches.
    have hwords_eq : dw0 = hw0 ∧ dw1 = hw1 ∧ dw2 = hw2 ∧ dw3 = hw3 := by
      simpa [and_assoc] using hcond
    have hhash_eq : sha3_256List pk = (hdr.drop 32).take 32 := by
      rw [hpkh_eq, hdig_words, hpkh_words, unpack64_quad_eq_iff]
      exact hwords_eq
    exact hcont _ (by simp [wp_norm, arm64_norm]) (by simp [hrun])
      (by simpa using hcl) (by simpa using hro)
      ⟨hhdr, hek, hhash_eq, by simp [hsp],
        ⟨by simp [hus.1], by simp [hus.2.1], by simp [hus.2.2.1], by simp [hus.2.2.2.1],
          by simp [calleeSavedVRegs, hus.2.2.2.2]⟩,
        by simp [hx20], by simp [hx22], by simp [hx23]⟩

/-! ## 6. Complete Segment 1 Theorem (`+0x0000 → s0.readReg64 .lr` via `Seg2` Continuation) -/

/-- Run `B21` from entry (`b + 0x0000`) through length checks, `memcpy`, `B02` (`keccak2::<136, 6>`),
    and 4×64-bit SHA3-256 comparison (`+0x00ac`), discharging all three early-exit return paths and
    handing the valid-length, valid-hash fallthrough at `b + 0x00b0#64` to `hcont`. -/
theorem seg1_run [MlKemPlacement]
    (hkeccak : MlKemBlockOk 2 keccak2_136_6_RW1Spec)
    {b : BitVec 64} (hb : MlKemBase blkPl21 b) (hbase : blkPl21.base = b)
    (s0 : State) (hdrA ekA : BitVec 64) (hdr ek : List (BitVec 8)) (R : SepProp)
    (hpc : s0.pc = b)
    (hrun : s0.status = .Running)
    (hsp0 : s0.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s0.mem)
    (hro : MlKemRoOk mlkemMpl s0.mem)
    (hx0 : s0.readReg64 .x0 = hdrA)
    (hx1 : (s0.readReg64 .x1).toNat = hdr.length)
    (hx2 : s0.readReg64 .x2 = ekA)
    (hx3 : (s0.readReg64 .x3).toNat = ek.length)
    (hcont : ∀ sm : State,
      sm.pc = b + 0x00b0#64 → sm.status = .Running →
      mlkemMultiLib.CodeLoaded mlkemMpl sm.mem → MlKemRoOk mlkemMpl sm.mem →
      Seg2Pre s0 sm hdr ek →
      SepWP (blkPC21.rebase b (fun _ => none)) (s0.readReg64 .lr) sm
        (Seg2Spatial s0 hdrA hdr ekA ek R)
        (ValidatePkPost s0 hdrA hdr ekA ek R)) :
    SepWP (blkPC21.rebase b (fun _ => none)) (s0.readReg64 .lr) s0
      ((hdrA ↦ₛ hdr) ∗ (ekA ↦ₛ ek) ∗ stackAt s0.sp 5824 ∗ R)
      (ValidatePkPost s0 hdrA hdr ekA ek R) := by
  refine SepWP.weaken_pre
    (show (hdrA ↦ₛ hdr) ∗ (ekA ↦ₛ ek) ∗ stackAt s0.sp 5824 ∗ R ⊢
      stackAt s0.sp 5824 ∗ ((hdrA ↦ₛ hdr) ∗ (ekA ↦ₛ ek) ∗ R) by sep_frame) ?_
  refine sepWP_seq_env hcl hro
    (seg1_prologue hb hbase s0 ((hdrA ↦ₛ hdr) ∗ (ekA ↦ₛ ek) ∗ R) hpc hrun hsp0) ?_
  intro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hfp1, hx19_1, hx2_1, hx3_1, hx0_1, hps1, hus1, hP1⟩
  refine SepWP.weaken_pre hP1 ?_
  -- `+0x002c: b.ne +0x0824` (`hdr.length` vs `64`)
  wp_step
  wp_if hne1
  · have hhdr_ne : hdr.length ≠ 64 := by
      intro heq
      have hbv : s0.readReg64 .x1 = 64#64 := BitVec.eq_of_toNat_eq (by simp [hx1, heq])
      simp [hbv] at hne1
    refine sepWP_mono_ret ?_
      (seg_epilogue hb hbase s0 _ ((hdrA ↦ₛ hdr) ∗ (ekA ↦ₛ ek) ∗ R)
        (by simp [wp_norm, arm64_norm]) (by simp [hrun1]) (by simp [hsp1]) hsp0
        ⟨by simp [hus1.1], by simp [hus1.2.1], by simp [hus1.2.2.1], by simp [hus1.2.2.2.1],
          by simp [calleeSavedVRegs, hus1.2.2.2.2]⟩)
    simp [hx0_1, validPkBytes_false_of_hdr_ne hhdr_ne]
  · have hhdr_eq : hdr.length = 64 := by
      have hbv : s0.readReg64 .x1 = 64#64 := by simpa using hne1
      simpa [hbv] using hx1.symm
    -- `+0x0030: cmp x3, #1152` and `+0x0034: b.ne +0x0824`
    wp_steps 2
    wp_if hne2
    · have hek_ne : ek.length ≠ 1152 := by
        intro heq
        have hbv : s0.readReg64 .x3 = 1152#64 := BitVec.eq_of_toNat_eq (by simp [hx3, heq])
        simp [hbv] at hne2
      refine sepWP_mono_ret ?_
        (seg_epilogue hb hbase s0 _ ((hdrA ↦ₛ hdr) ∗ (ekA ↦ₛ ek) ∗ R)
          (by simp [wp_norm, arm64_norm]) (by simp [hrun1]) (by simp [hsp1]) hsp0
          ⟨by simp [hus1.1], by simp [hus1.2.1], by simp [hus1.2.2.1], by simp [hus1.2.2.2.1],
            by simp [calleeSavedVRegs, hus1.2.2.2.2]⟩)
      simp [hx0_1, validPkBytes_false_of_ek_ne hek_ne]
    · have hek_eq : ek.length = 1152 := by
        have hbv : s0.readReg64 .x3 = 1152#64 := by simpa using hne2
        simpa [hbv] using hx3.symm
      -- Sequence `seg1_prep_keccak` (`+0x0038 → +0x0088`) -> `seg1_keccak_call` -> `seg1_cmp_and_branch`
      refine sepWP_seq_env (by simpa using hcl1) (by simpa using hro1)
        (SepWP.weaken_pre (by sep_frame)
          (seg1_prep_keccak hb hbase s0 _ hdrA ekA hdr ek R hhdr_eq hek_eq
            (by simp [wp_norm, arm64_norm]) (by simp [hrun1]) (by simp [hsp1]) hsp0
            (by simp [hfp1]) (by simp [hx19_1, hx0]) (by simp [hx2_1, hx2])
            ⟨by simp [hus1.1], by simp [hus1.2.1], by simp [hus1.2.2.1], by simp [hus1.2.2.2.1],
              by simp [calleeSavedVRegs, hus1.2.2.2.2]⟩
            (by simpa using hcl1) (by simpa using hro1))) ?_
      intro s2 P2 hpc2 hrun2 hcl2 hro2
        ⟨hsp2, hfp2, hx19_2, hx20_2, hx22_2, hx23_2, hx0_2, hx1_2, hx2_2, hus2, hP2⟩
      refine SepWP.weaken_pre (Entails.trans hP2 (by sep_frame)) ?_
      refine sepWP_seq_env hcl2 hro2
        (seg1_keccak_call hkeccak hb hbase s0 s2 hdrA hdr ek
          (SavedFrame s0.sp s0 ∗
            memRegion (s0.sp - 4784#64) 16 ∗
            memRegion ((s0.sp - 4784#64) + 1232#64) 1504 ∗
            memRegion ((s0.sp - 4784#64) + 2768#64) 1920 ∗
            (hdrA ↦ₛ hdr) ∗ (ekA ↦ₛ ek) ∗ R)
          hhdr_eq hek_eq
          hpc2 hrun2 hsp2 hsp0 hfp2 hx19_2 hx20_2 hx22_2 hx23_2 hx0_2 hx1_2 hx2_2 hus2 hcl2 hro2) ?_
      intro s3 P3 hpc3 hrun3 hcl3 hro3 ⟨hsp3, hfp3, hx19_3, hx20_3, hx22_3, hx23_3, hus3, hP3⟩
      exact SepWP.weaken_pre (Entails.trans hP3 (by sep_frame))
        (seg1_cmp_and_branch hb hbase s0 s3 hdrA ekA hdr ek R hhdr_eq hek_eq
          hpc3 hrun3 hsp3 hsp0 hfp3 hx19_3 hx20_3 hx22_3 hx23_3 hus3 hcl3 hro3 hcont)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg1
