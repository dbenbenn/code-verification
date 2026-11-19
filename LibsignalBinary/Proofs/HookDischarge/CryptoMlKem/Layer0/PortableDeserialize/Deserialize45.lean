/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize.Specs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLift
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.CtOps.InzCompare
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize.BitHelpers

/-!
# Portable Deserialization Proofs for `d = 4` (`B25`) and `d = 5` (`B26`)

Proves `blk25_deserialize4_RO_ok : MlKemBlockConstOk 25 mlkemDeserialize4ROSpec` and
`blk26_deserialize5_RO_ok : MlKemBlockConstOk 26 mlkemDeserialize5ROSpec`.
-/

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize.Deserialize45

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
  mlkemLeaf_ok
  mlkemMpl
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
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.CtOps.InzCompare (
  mlkemConstOk_map_ct
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize.Specs (
  PortableDeserializeArgs
  PortableDeserializePurePre
  deserializeChunkBytes
  mlkemDeserialize4ROSpec
  mlkemDeserialize5ROSpec
  mlkemDeserializeROSpec
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize.BitHelpers (
  eq_deserializeChunkBytes_of_halfwordTable
  eq_deserializeChunkCoeff_of_bits
  getLsbD_8_of_ge
  halfwordTable_init
  halfwordTable_write16
  satisfies_stackAt16_two
  stackAt16_two_entails
  vregs_setMem
  vregs_setPC
  vregs_setPState
  vregs_writeReg64
)

attribute [local wp_norm] vregs_setMem vregs_setPC vregs_setPState vregs_writeReg64

private theorem getLsbD_ofNat64_true (n k : Nat)
    (h : decide ((BitVec.ofNat 64 n).getLsbD k = true) = true) :
    (BitVec.ofNat 64 n).getLsbD k = true :=
  of_decide_eq_true h

private theorem getLsbD_ofNat64_false (n k : Nat)
    (h : decide ((BitVec.ofNat 64 n).getLsbD k = false) = true) :
    (BitVec.ofNat 64 n).getLsbD k = false :=
  of_decide_eq_true h

gen_block_fetches mlkem 25 mlkemMultiLib MlKemPlacement 59 [0x0 → 0xc4]
gen_block_fetches mlkem 26 mlkemMultiLib MlKemPlacement 69 [0x0 → 0xec]

/-- Base leaf spec for `deserialize_d` before outer `NonSyscallPreserved` lifting. -/
private def mlkemDeserializeBaseSpec (d : Nat) : Spec PortableDeserializeArgs where
  pre := (mlkemDeserializeROSpec d).pre
  post := fun a s0 sf =>
    ⌜sf.vregs = s0.vregs⌝ ∗
    (a.outPtr ↦ₛ deserializeChunkBytes d a.inBytes) ∗
    (a.inPtr ↦ᵣ a.inBytes) ∗
    stackAt s0.sp 16
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem entails_deserialize_post (d : Nat) {a : PortableDeserializeArgs}
    {out : List (BitVec 8)} {sp : BitVec 64} {w0 w1 : BitVec 64}
    (heq : out = deserializeChunkBytes d a.inBytes) :
    ((a.outPtr ↦ₛ out) ∗ (a.inPtr ↦ᵣ a.inBytes) ∗
      (((sp - 16#64) ↦₆₄ w0) ∗ ((sp - 8#64) ↦₆₄ w1))) ⊢
    ((a.outPtr ↦ₛ deserializeChunkBytes d a.inBytes) ∗
      (a.inPtr ↦ᵣ a.inBytes) ∗ stackAt sp 16) := by
  rw [heq]
  exact sepConj_mono_right (sepConj_mono_right (stackAt16_two_entails sp w0 w1))

private theorem lift_deserialize_nsp {j d : Nat} (hj : j < mlkemMultiLib.blocks.length)
    (hbase : MlKemBlockConstOk j (mlkemDeserializeBaseSpec d)) :
    MlKemBlockConstOk j (mlkemDeserializeROSpec d) := by
  intro _
  exact mlkemConstOk_map_ct (spec' := mlkemDeserializeROSpec d)
    (mlkemBlockConstOk_withNonSyscallPreserved (hj := hj) hbase
      (h_pre := fun mpl a R s0 h => by
        dsimp [mlkemDeserializeBaseSpec, mlkemDeserializeROSpec, PortableDeserializePurePre] at h ⊢
        simpa [stripS_sp, stripS_readReg64, stripS_readReg32, stripS_vregs, stripS_regs,
          stripS_mem] using h)
      (h_post := fun mpl a R s0 sf hnsp h => by
        dsimp [mlkemDeserializeBaseSpec, mlkemDeserializeROSpec] at h ⊢
        simpa [stripS_sp, stripS_readReg64, stripS_readReg32, stripS_vregs, stripS_regs,
          stripS_mem, stripExecOutside_eq_iff_of_perm_eq (mlkemKeep mpl) hnsp.2.1] using h))
    fun a R _s0 hpre => ⟨a, R, hpre, fun _sf hpost => by
      dsimp only [withNonSyscallPreserved, mlkemDeserializeBaseSpec,
        mlkemDeserializeROSpec] at hpost ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      obtain ⟨hnsp, hpost'⟩ := hpost
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost'
      exact ⟨⟨hnsp, hpost'.1⟩, hpost'.2⟩⟩

set_option maxHeartbeats 400000 in
private theorem blk25_deserialize4_base_ok :
    MlKemBlockConstOk 25 (mlkemDeserializeBaseSpec 4) := by
  intro _
  refine mlkemLeaf_ok (j := 25) mlkemPC25 mlkemPl25 (spec := mlkemDeserializeBaseSpec 4)
    (h := fun b hb hbase => ?_)
  apply subroutine_ok_of_sepWP_init
  intro a R s0 hpc hrun hpre _hsp
  dsimp only [ToBaseSpec.toSpec, mlkemDeserializeBaseSpec, mlkemDeserializeROSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx8, hx0, hx1, hlen⟩, hspat⟩ := hpre
  have hx8' : s0.readReg64 (Reg.gpr 8#5) = a.outPtr := hx8
  have hx0' : s0.readReg64 (Reg.gpr 0#5) = a.inPtr := hx0
  have hx1' : 2 * 4 ≤ (s0.readReg64 (Reg.gpr 1#5)).toNat := hx1
  have hspat_stk : s0.mem ⊨ stackAt s0.sp 16 ∗
      (memRegion a.outPtr 32 ∗ (a.inPtr ↦ᵣ a.inBytes) ∗ R) :=
    Satisfies.mono (by sep_frame) hspat
  obtain ⟨w0, w1, hspat'⟩ := satisfies_stackAt16_two hspat_stk
  refine ⟨memRegion a.outPtr 32 ∗ (a.inPtr ↦ᵣ a.inBytes) ∗
    ((s0.sp - 16#64) ↦₆₄ w0) ∗ ((s0.sp - 8#64) ↦₆₄ w1),
    Satisfies.mono (by sep_frame) hspat', ?_⟩
  apply SepWP.memRegion_bytes a.outPtr 32
  intro out₀ hout₀
  wp_steps 5
  wp_if
  · exfalso
    simp only [BitVec.ule_iff_toNat_le, BitVec.toNat_ofNat] at *
    omega
  · wp_steps 2
    wp_if
    · exfalso
      simp only [BitVec.ule_iff_toNat_le, BitVec.toNat_ofNat] at *
      omega
    · wp_steps
      apply SepWP.weaken_pre
        (Entails.trans
          (by sep_frame : _ ⊢
            (a.outPtr ↦ₛ _) ∗ (a.inPtr ↦ᵣ a.inBytes) ∗
              (((s0.sp - 16#64) ↦₆₄ _) ∗ ((s0.sp - 8#64) ↦₆₄ _)))
          (entails_deserialize_post 4 ?_))
      · wp_done
      · apply eq_deserializeChunkBytes_of_halfwordTable 4 a.inBytes
        · repeat apply halfwordTable_write16
          · exact halfwordTable_init hout₀
          all_goals decide
        · intro j hj
          rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | j
          all_goals try omega
          all_goals
            simp only [Nat.reduceDiv, Nat.reduceEqDiff, ↓reduceIte]
            apply eq_deserializeChunkCoeff_of_bits 4 a.inBytes hlen _ (by decide)
            intro i hi
            rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i
            all_goals try omega
            all_goals
              simp (disch := decide) only [BitVec.truncate_eq_setWidth,
                BitVec.getLsbD_setWidth, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight,
                getLsbD_ofNat64_true, getLsbD_ofNat64_false, getLsbD_8_of_ge,
                Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod,
                Nat.reduceLT, decide_true, ↓reduceIte,
                Bool.true_and, Bool.and_true, Bool.and_false]

set_option maxHeartbeats 400000 in
private theorem blk26_deserialize5_base_ok :
    MlKemBlockConstOk 26 (mlkemDeserializeBaseSpec 5) := by
  intro _
  refine mlkemLeaf_ok (j := 26) mlkemPC26 mlkemPl26 (spec := mlkemDeserializeBaseSpec 5)
    (h := fun b hb hbase => ?_)
  apply subroutine_ok_of_sepWP_init
  intro a R s0 hpc hrun hpre _hsp
  dsimp only [ToBaseSpec.toSpec, mlkemDeserializeBaseSpec, mlkemDeserializeROSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx8, hx0, hx1, hlen⟩, hspat⟩ := hpre
  have hx8' : s0.readReg64 (Reg.gpr 8#5) = a.outPtr := hx8
  have hx0' : s0.readReg64 (Reg.gpr 0#5) = a.inPtr := hx0
  have hx1' : 2 * 5 ≤ (s0.readReg64 (Reg.gpr 1#5)).toNat := hx1
  have hspat_stk : s0.mem ⊨ stackAt s0.sp 16 ∗
      (memRegion a.outPtr 32 ∗ (a.inPtr ↦ᵣ a.inBytes) ∗ R) :=
    Satisfies.mono (by sep_frame) hspat
  obtain ⟨w0, w1, hspat'⟩ := satisfies_stackAt16_two hspat_stk
  refine ⟨memRegion a.outPtr 32 ∗ (a.inPtr ↦ᵣ a.inBytes) ∗
    ((s0.sp - 16#64) ↦₆₄ w0) ∗ ((s0.sp - 8#64) ↦₆₄ w1),
    Satisfies.mono (by sep_frame) hspat', ?_⟩
  apply SepWP.memRegion_bytes a.outPtr 32
  intro out₀ hout₀
  wp_steps 5
  wp_if
  · exfalso
    simp only [BitVec.ule_iff_toNat_le, BitVec.toNat_ofNat] at *
    omega
  · wp_steps 2
    wp_if
    · exfalso
      simp only [BitVec.ule_iff_toNat_le, BitVec.toNat_ofNat] at *
      omega
    · wp_steps
      apply SepWP.weaken_pre
        (Entails.trans
          (by sep_frame : _ ⊢
            (a.outPtr ↦ₛ _) ∗ (a.inPtr ↦ᵣ a.inBytes) ∗
              (((s0.sp - 16#64) ↦₆₄ _) ∗ ((s0.sp - 8#64) ↦₆₄ _)))
          (entails_deserialize_post 5 ?_))
      · wp_done
      · apply eq_deserializeChunkBytes_of_halfwordTable 5 a.inBytes
        · repeat apply halfwordTable_write16
          · exact halfwordTable_init hout₀
          all_goals decide
        · intro j hj
          rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | j
          all_goals try omega
          all_goals
            simp only [Nat.reduceDiv, Nat.reduceEqDiff, ↓reduceIte]
            apply eq_deserializeChunkCoeff_of_bits 5 a.inBytes hlen _ (by decide)
            intro i hi
            rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i
            all_goals try omega
            all_goals
              simp (disch := decide) only [BitVec.truncate_eq_setWidth,
                BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_and,
                BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
                getLsbD_ofNat64_true, getLsbD_ofNat64_false, getLsbD_8_of_ge,
                Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod,
                Nat.reduceLT, decide_true, decide_false, ↓reduceIte,
                Bool.not_true, Bool.not_false,
                Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false,
                Bool.false_or, Bool.or_false]

public section

/-- `B25` (`PortableVector::deserialize_4`) RO-input contract with `NonSyscallPreserved`. -/
theorem blk25_deserialize4_RO_ok : MlKemBlockConstOk 25 mlkemDeserialize4ROSpec :=
  lift_deserialize_nsp (by decide) blk25_deserialize4_base_ok

/-- `B26` (`PortableVector::deserialize_5`) RO-input contract with `NonSyscallPreserved`. -/
theorem blk26_deserialize5_RO_ok : MlKemBlockConstOk 26 mlkemDeserialize5ROSpec :=
  lift_deserialize_nsp (by decide) blk26_deserialize5_base_ok

end

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize.Deserialize45
