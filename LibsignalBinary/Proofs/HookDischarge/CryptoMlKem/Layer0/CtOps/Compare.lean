/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.CtOps.Specs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLift
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.CtOps.InzCompare

/-!
# Constant-time ciphertext comparison (`B17`, `B13`)

Proves the constant-time ciphertext comparison contracts:
- `blk17_compare_ok : MlKemBlockConstOk 17 (mlkemCtCompareROSpec 32)`
- `blk13_compare_ct_ok : MlKemBlockConstOk 13 (mlkemCtCompareROSpec 64)`
-/

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.CtOps.Compare

open Arm64 Arm64.Obj ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase
  MlKemBlockConstOk
  MlKemPlacement
  add_off_reloc_cancel
  add_reloc_cancel
  add_zero_reloc_cancel
  mbase
  mlkemBlockPlacement_ρ
  mlkemCall_of_blockOk
  mlkemCaller_ok
  mlkemMpl
  resolve_blk12
  resolve_blk17
  seq_codeLoaded_lr
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (withNonSyscallPreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLift (
  mlkemBlockConstOk_withNonSyscallPreserved
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLiftBase (
  mlkemKeep
  stripExecOutside_eq_iff_of_perm_eq
  stripS_mem
  stripS_readReg32
  stripS_readReg64
  stripS_regs
  stripS_sp
  stripS_vregs
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.CtOps.Specs (
  mlkemCtCompareROSpec
  mlkemIsNonZeroSpec
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.CtOps.InzCompare (
  blk12_is_non_zero_base_ok
  mlkemConstOk_map_ct
  mlkemIsNonZeroBaseSpec
  satisfies_stackAt32_inz
  stackAt32_inz_entails
)

gen_block_fetches mlkem 17 mlkemMultiLib MlKemPlacement 20 [0x0 → 0x38]
gen_block_fetches mlkem 13 mlkemMultiLib MlKemPlacement 10

@[simp, arm64_norm, wp_norm]
private theorem mlkemPl17_ρ [MlKemPlacement] (sym : String) :
    mlkemPl17.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

@[simp, arm64_norm, wp_norm]
private theorem mlkemPl13_ρ [MlKemPlacement] (sym : String) :
    mlkemPl13.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

private theorem or_xor_beq_zero (acc x y : BitVec 8) :
    (((y ^^^ x) ||| acc) == 0#8) = ((acc == 0#8) && (x == y)) := by
  have hor : ∀ a b : BitVec 8, ((a ||| b) == 0#8) = ((a == 0#8) && (b == 0#8)) := by
    intro a b
    cases ha : (a == 0#8) <;> cases hb : (b == 0#8)
    · rw [Bool.false_and]
      apply beq_false_of_ne
      intro hab
      apply ne_of_beq_false ha
      ext i hi
      have hbit := congrArg (fun v : BitVec 8 => v[i]) hab
      simp at hbit ⊢
      exact hbit.1
    · rw [Bool.false_and]
      apply beq_false_of_ne
      intro hab
      apply ne_of_beq_false ha
      ext i hi
      have hbit := congrArg (fun v : BitVec 8 => v[i]) hab
      simp at hbit ⊢
      exact hbit.1
    · rw [Bool.true_and, beq_iff_eq.mp ha, BitVec.zero_or]
      exact hb
    · rw [Bool.true_and, beq_iff_eq.mp ha, beq_iff_eq.mp hb]; rfl
  have hxor : ((y ^^^ x) == 0#8) = (x == y) := by
    cases hxy : (x == y)
    · apply beq_false_of_ne
      intro h0
      apply ne_of_beq_false hxy
      have := congrArg (· ^^^ x) h0
      simpa [BitVec.xor_assoc, BitVec.xor_self] using this.symm
    · rw [beq_iff_eq.mp hxy, BitVec.xor_self]; rfl
  rw [hor, hxor, Bool.and_comm]

private theorem compare_loop_sepwp [MlKemPlacement] (b : BitVec 64) (_hb : MlKemBase mlkemPl17 b)
    {target_pc : BitVec 64}
    (xs : List (BitVec 8)) :
    ∀ (ys : List (BitVec 8)) (p q : BitVec 64) (acc : BitVec 8) (s : State)
      (F : SepProp) (post : State → SepProp → Prop) (oom : State → SepProp),
      1 ≤ xs.length →
      xs.length < 2 ^ 64 →
      ys.length = xs.length →
      s.pc = b + 0x18#64 →
      s.status = .Running →
      s.readReg64 .x0 = p →
      (s.readReg64 .x1).toNat = xs.length →
      s.readReg64 .x2 = q →
      s.readReg64 .x8 = BitVec.zeroExtend 64 acc →
      (∀ (s' : State) (res : BitVec 8),
        s'.pc = b + 0x30#64 →
        s'.status = .Running →
        s'.mem = s.mem →
        s'.sp = s.sp →
        s'.readReg64 .lr = s.readReg64 .lr →
        CalleeSavedPreserved s s' →
        s'.readReg64 .x8 = BitVec.zeroExtend 64 res →
        (res == 0#8) = ((acc == 0#8) && (xs == ys)) →
        SepWP (mlkemPC17.rebase b (fun _ => none)) target_pc s'
          ((p ↦ᵣ xs) ∗ (q ↦ᵣ ys) ∗ F) post oom) →
      SepWP (mlkemPC17.rebase b (fun _ => none)) target_pc s
        ((p ↦ᵣ xs) ∗ (q ↦ᵣ ys) ∗ F) post oom := by
  induction xs with
  | nil =>
    rintro _ _ _ _ _ _ _ _ h1
    simp at h1
  | cons x xs' ih =>
    intro ys p q acc s F post oom _h1 hlt hlen_eq hpc hrun hx0 hx1 hx2 hx8 hk
    cases ys with
    | nil => simp at hlen_eq
    | cons y ys' =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen_eq hlt
      rw [pointsToBytesRO_cons, pointsToBytesRO_cons]
      cases xs' with
      | nil =>
        cases ys' with
        | nil =>
          have hx1_val : s.readReg64 (Reg.gpr 1#5) = 1#64 := by
            change s.readReg64 .x1 = 1#64
            apply BitVec.eq_of_toNat_eq; simpa using hx1
          wp_steps 6
          have hrestore :
              (((p ↦₈ᵣ x) ∗ ((p + 1#64) ↦ᵣ [])) ∗ ((q ↦₈ᵣ y) ∗ ((q + 1#64) ↦ᵣ [])) ∗ F) =
                ((p ↦ᵣ [x]) ∗ (q ↦ᵣ [y]) ∗ F) := by
            rw [← pointsToBytesRO_cons, ← pointsToBytesRO_cons]
          rw [hrestore]
          refine hk _ ((y ^^^ x) ||| acc)
            (by simp [wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm, hrun])
            rfl
            (by simp [wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm])
            ?_
            ?_
            ?_
          · simp only [wp_norm, arm64_norm]
            exact CalleeSavedPreserved.rfl s
          · simp only [wp_norm, arm64_norm]
            ext i hi
            by_cases hi8 : i < 8 <;> simp [hi8]
          · have hcons_beq : (([x] : List (BitVec 8)) == [y]) = (x == y) := by
              show (x == y && ([] : List (BitVec 8)) == []) = (x == y)
              simp
            rw [hcons_beq]
            exact or_xor_beq_zero acc x y
        | cons _ _ => simp at hlen_eq
      | cons x2 xs'' =>
        have hxs'_pos : 1 ≤ (x2 :: xs'').length := by simp
        have hx1_gt1 : 1 < (s.readReg64 .x1).toNat := by simp at hx1; omega
        wp_steps 6
        wp_if hne
        · have hrearr' : ∀ (A B C D : SepProp),
              ((A ∗ B) ∗ (C ∗ D) ∗ F) = (B ∗ D ∗ (A ∗ C ∗ F)) := fun A B C D => by
            rw [sepConj_comm A B, sepConj_comm C D, sepConj_assoc B A,
              ← sepConj_assoc A (D ∗ C) F, ← sepConj_assoc A D C, sepConj_comm A D,
              sepConj_assoc D A C, sepConj_assoc D (A ∗ C) F, sepConj_assoc A C F]
          rw [hrearr']
          refine ih ys' (p + 1#64) (q + 1#64) ((y ^^^ x) ||| acc) _
            ((p ↦₈ᵣ x) ∗ (q ↦₈ᵣ y) ∗ F) post oom
            hxs'_pos (by omega) hlen_eq
            (by simp [wp_norm, arm64_norm])
            (by simp [wp_norm, arm64_norm, hrun])
            (by simp only [wp_norm, arm64_norm])
            ?_
            (by simp only [wp_norm, arm64_norm])
            ?_
            fun s'' res hpc'' hrun'' hmem'' hsp'' hlr'' hcs'' hx8'' hres'' => ?_
          · simp only [wp_norm, arm64_norm]
            have hle1 : 1#64 ≤ s.readReg64 (Reg.gpr 1#5) :=
              BitVec.le_def.mpr (by change 1 ≤ (s.readReg64 .x1).toNat; omega)
            rw [BitVec.toNat_sub_of_le hle1]
            change (s.readReg64 .x1).toNat - 1 = (x2 :: xs'').length
            simp at hx1 ⊢
            omega
          · simp only [wp_norm, arm64_norm]
            ext i hi
            by_cases hi8 : i < 8 <;> simp [hi8]
          · rw [← hrearr', ← pointsToBytesRO_cons, ← pointsToBytesRO_cons]
            refine hk s'' res hpc'' hrun'' hmem''
              (hsp''.trans (by simp [wp_norm, arm64_norm]))
              (hlr''.trans (by simp [wp_norm, arm64_norm]))
              (CalleeSavedPreserved.trans ?_ hcs'')
              hx8''
              ?_
            · simp only [wp_norm, arm64_norm]
              exact CalleeSavedPreserved.rfl s
            · rw [hres'', or_xor_beq_zero, Bool.and_assoc]
              rfl
        · exfalso
          have hto : (s.readReg64 .x1).toNat = 1 := by
            change (s.readReg64 (Reg.gpr 1#5)).toNat = 1
            rw [hne]; rfl
          omega

private theorem satisfies_stackAt32_pair {m : Memory} {sp : BitVec 64} {R : SepProp}
    (hm : m ⊨ stackAt sp 32 ∗ R) :
    ∃ (w0 w1 : BitVec 64),
      m ⊨ (stackAt (sp - 16#64) 16 ∗ ((sp - 16#64) ↦₆₄ w0) ∗ ((sp - 8#64) ↦₆₄ w1)) ∗ R := by
  rw [stackAt_frame sp 32 2 (by decide),
    cells_sub_succ _ _ _ (by decide) (by decide),
    cells_sub_succ _ _ _ (by decide) (by decide), cells_zero] at hm
  simp only [sepConj_emp,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm
  rcases hm with ⟨w0, w1, hm⟩
  exact ⟨w0, w1, Satisfies.mono (by sep_frame) hm⟩

private theorem stackAt32_pair_entails (sp : BitVec 64) (w0 w1 : BitVec 64) :
    (stackAt (sp - 16#64) 16 ∗ ((sp - 16#64) ↦₆₄ w0) ∗ ((sp - 8#64) ↦₆₄ w1)) ⊢
      stackAt sp 32 := by
  rw [stackAt_frame sp 32 2 (by decide),
    cells_sub_succ _ _ _ (by decide) (by decide),
    cells_sub_succ _ _ _ (by decide) (by decide), cells_zero]
  simp only [sepConj_emp]
  exact sepConj_mono_right (Entails.sepExists_right w0
    (sepConj_mono_right (Entails.sepExists_right w1 (Entails.refl _))))

private theorem satisfies_stackAt64_inz {m : Memory} {sp : BitVec 64} {R : SepProp}
    (hm : m ⊨ stackAt sp 64 ∗ R) :
    ∃ (b0 : BitVec 8) (w0 w1 : BitVec 64),
      m ⊨ (stackAt (sp - 32#64) 32 ∗
        (((sp - 20#64) ↦₈ b0) ∗ ((sp - 16#64) ↦₆₄ w0) ∗ ((sp - 8#64) ↦₆₄ w1) ∗
          memRegion (sp - 32#64) 12 ∗ memRegion (sp - 19#64) 3)) ∗ R := by
  have h64 : stackAt sp 64 = stackAt (sp - 32#64) 32 ∗ stackAt sp 32 :=
    stackAt_region sp 32 32 (by decide)
  rw [h64] at hm
  have hm' : m ⊨ stackAt sp 32 ∗ (stackAt (sp - 32#64) 32 ∗ R) :=
    Satisfies.mono (by sep_frame) hm
  obtain ⟨b0, w0, w1, hm''⟩ := satisfies_stackAt32_inz hm'
  exact ⟨b0, w0, w1, Satisfies.mono (by sep_frame) hm''⟩

private theorem stackAt64_inz_entails (sp : BitVec 64) (b0 : BitVec 8) (w0 w1 : BitVec 64) :
    (stackAt (sp - 32#64) 32 ∗
      (((sp - 20#64) ↦₈ b0) ∗ ((sp - 16#64) ↦₆₄ w0) ∗ ((sp - 8#64) ↦₆₄ w1) ∗
        memRegion (sp - 32#64) 12 ∗ memRegion (sp - 19#64) 3)) ⊢ stackAt sp 64 := by
  have h64 : stackAt sp 64 = stackAt (sp - 32#64) 32 ∗ stackAt sp 32 :=
    stackAt_region sp 32 32 (by decide)
  rw [h64]
  exact sepConj_mono_right (stackAt32_inz_entails sp b0 w0 w1)

public section

/-- Base `B17`/`B13` spec without `NonSyscallPreserved` (used by `B13` and `B16` before outer
    `mlkemBlockConstOk_withNonSyscallPreserved` lifting). -/
@[expose] def mlkemCtCompareBaseSpec (stkBytes : Nat) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8)) where
  pre := (mlkemCtCompareROSpec stkBytes).pre
  post := fun (lhsPtr, rhsPtr, lhs, rhs) s0 sf =>
    ⌜sf.readReg32 .x0 = (if lhs == rhs then 0#32 else 1#32)⌝ ∗
      (lhsPtr ↦ᵣ lhs) ∗ (rhsPtr ↦ᵣ rhs) ∗ stackAt s0.sp stkBytes
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

theorem blk17_compare_base_ok : MlKemBlockConstOk 17 (mlkemCtCompareBaseSpec 32) := by
  intro _
  refine mlkemCaller_ok (j := 17) mlkemPC17 mlkemPl17 (spec := mlkemCtCompareBaseSpec 32)
    (h := fun b hb hbase => ?_)
  apply subroutine_ok_of_sepWP_init
  rintro ⟨lhsPtr, rhsPtr, lhs, rhs⟩ R s0 hpc hrun hpre _hsp
  dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, mlkemCtCompareBaseSpec,
    mlkemCtCompareROSpec] at hpre
  rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre_body⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_body
  obtain ⟨⟨hx0, hx1, hx2, hx3, h1, hrhs, hlt⟩, hspat⟩ := hpre_body
  have hspat_stk : s0.mem ⊨ stackAt s0.sp 32 ∗ ((lhsPtr ↦ᵣ lhs) ∗ (rhsPtr ↦ᵣ rhs) ∗ R) :=
    Satisfies.mono (by sep_frame) hspat
  obtain ⟨w0, w1, hspat'⟩ := satisfies_stackAt32_pair hspat_stk
  refine ⟨(lhsPtr ↦ᵣ lhs) ∗ (rhsPtr ↦ᵣ rhs) ∗
    (stackAt (s0.sp - 16#64) 16 ∗ ((s0.sp - 16#64) ↦₆₄ w0) ∗ ((s0.sp - 8#64) ↦₆₄ w1)),
    Satisfies.mono (by sep_frame) hspat', ?_⟩
  apply MultiPlacedLib.seq_codeLoaded (mid := b + 0x38#64) hcl0
  wp_steps 5
  wp_if hls
  · exfalso
    simp only [wp_norm, arm64_norm, BitVec.ule_iff_toNat_le] at hls
    have hle1 : 1#64 ≤ s0.readReg64 (Reg.gpr 1#5) :=
      BitVec.le_def.mpr (by change 1 ≤ (s0.readReg64 .x1).toNat; omega)
    rw [BitVec.toNat_sub_of_le hle1] at hls
    change (s0.readReg64 .x3).toNat ≤ (s0.readReg64 .x1).toNat - 1 at hls
    omega
  · wp_steps 1
    refine compare_loop_sepwp b hb lhs rhs lhsPtr rhsPtr 0#8 _ _ _ _
      h1 hlt hrhs
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hrun])
      (by simp only [wp_norm, arm64_norm]; exact hx0)
      (by simpa [wp_norm, arm64_norm] using hx1)
      (by simp only [wp_norm, arm64_norm]; exact hx2)
      (by simp [wp_norm, arm64_norm])
      fun s' res hpc' hrun' hmem' hsp' hlr' hcs' hx8' hres' => ?_
    have hres_eq : (res == 0#8) = (lhs == rhs) := by simpa using hres'
    clear hmem'
    wp_steps 2
    apply SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_right
      (stackAt32_pair_entails s0.sp
        (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5)))))
    wp_mlkem_tailcall blk12_is_non_zero_base_ok
    simp only [wp_norm, width_norm, hx8', hres_eq] at *
    wp_done

theorem blk13_compare_ct_base_ok : MlKemBlockConstOk 13 (mlkemCtCompareBaseSpec 64) := by
  intro _
  refine mlkemCaller_ok (j := 13) mlkemPC13 mlkemPl13 (spec := mlkemCtCompareBaseSpec 64)
    (h := fun b hb hbase => ?_)
  apply subroutine_ok_of_sepWP_init
  rintro ⟨lhsPtr, rhsPtr, lhs, rhs⟩ R s0 hpc hrun hpre _hsp
  dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, mlkemCtCompareBaseSpec,
    mlkemCtCompareROSpec] at hpre
  rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre_body⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_body
  obtain ⟨⟨hx0, hx1, hx2, hx3, h1, hrhs, hlt⟩, hspat⟩ := hpre_body
  have hspat_stk : s0.mem ⊨ stackAt s0.sp 64 ∗ ((lhsPtr ↦ᵣ lhs) ∗ (rhsPtr ↦ᵣ rhs) ∗ R) :=
    Satisfies.mono (by sep_frame) hspat
  obtain ⟨b0, w0, w1, hspat'⟩ := satisfies_stackAt64_inz hspat_stk
  refine ⟨(lhsPtr ↦ᵣ lhs) ∗ (rhsPtr ↦ᵣ rhs) ∗ stackAt (s0.sp - 32#64) 32 ∗
    (((s0.sp - 20#64) ↦₈ b0) ∗ ((s0.sp - 16#64) ↦₆₄ w0) ∗ ((s0.sp - 8#64) ↦₆₄ w1) ∗
      memRegion (s0.sp - 32#64) 12 ∗ memRegion (s0.sp - 19#64) 3),
    Satisfies.mono (by sep_frame) hspat', ?_⟩
  wp_cut_codeLoaded
  wp_steps
  wp_mlkem_call blk17_compare_base_ok (lhsPtr, rhsPtr, lhs, rhs)
  wp_steps
  apply SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_right (stackAt64_inz_entails s0.sp _ _ _)))
  simp only [wp_norm, width_norm]
  wp_done

/-- `B17` (`compare`) read-only contract (`32`-byte stack) with `NonSyscallPreserved`. -/
theorem blk17_compare_ok : MlKemBlockConstOk 17 (mlkemCtCompareROSpec 32) := by
  intro _
  exact (mlkemConstOk_map_ct (spec' := mlkemCtCompareROSpec 32)
    (mlkemBlockConstOk_withNonSyscallPreserved blk17_compare_base_ok
      (h_pre := fun mpl x R s0 h => by
        dsimp [mlkemCtCompareBaseSpec, mlkemCtCompareROSpec] at h ⊢
        simpa [stripS_sp, stripS_readReg64, stripS_readReg32, stripS_vregs, stripS_regs] using h)
      (h_post := fun mpl x R s0 sf hnsp h => by
        dsimp [mlkemCtCompareBaseSpec, mlkemCtCompareROSpec] at h ⊢
        simpa [stripS_sp, stripS_readReg64, stripS_readReg32, stripS_vregs, stripS_regs,
          stripS_mem, stripExecOutside_eq_iff_of_perm_eq (mlkemKeep mpl) hnsp.2.1] using h))
    fun args R _s0 hpre => ⟨args, R, hpre, fun _sf hpost => by
      dsimp only [withNonSyscallPreserved, mlkemCtCompareBaseSpec, mlkemCtCompareROSpec] at hpost ⊢
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      exact ⟨⟨hpost.1, hpost.2.1⟩, hpost.2.2⟩⟩)

/-- `B13` (`compare_ciphertexts_in_constant_time`) read-only contract (`64`-byte stack)
    with `NonSyscallPreserved`. -/
theorem blk13_compare_ct_ok : MlKemBlockConstOk 13 (mlkemCtCompareROSpec 64) := by
  intro _
  exact (mlkemConstOk_map_ct (spec' := mlkemCtCompareROSpec 64)
    (mlkemBlockConstOk_withNonSyscallPreserved blk13_compare_ct_base_ok
      (h_pre := fun mpl x R s0 h => by
        dsimp [mlkemCtCompareBaseSpec, mlkemCtCompareROSpec] at h ⊢
        simpa [stripS_sp, stripS_readReg64, stripS_readReg32, stripS_vregs, stripS_regs] using h)
      (h_post := fun mpl x R s0 sf hnsp h => by
        dsimp [mlkemCtCompareBaseSpec, mlkemCtCompareROSpec] at h ⊢
        simpa [stripS_sp, stripS_readReg64, stripS_readReg32, stripS_vregs, stripS_regs,
          stripS_mem, stripExecOutside_eq_iff_of_perm_eq (mlkemKeep mpl) hnsp.2.1] using h))
    fun args R _s0 hpre => ⟨args, R, hpre, fun _sf hpost => by
      dsimp only [withNonSyscallPreserved, mlkemCtCompareBaseSpec, mlkemCtCompareROSpec] at hpost ⊢
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      exact ⟨⟨hpost.1, hpost.2.1⟩, hpost.2.2⟩⟩)

end

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.CtOps.Compare
