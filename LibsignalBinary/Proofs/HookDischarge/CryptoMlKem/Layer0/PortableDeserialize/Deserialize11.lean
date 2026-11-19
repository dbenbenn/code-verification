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
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLiftBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLift
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize.BitHelpers

/-!
# Portable Deserialization Proof for `d = 11` (`B27`)

Proves `blk27_deserialize11_RO_ok : MlKemBlockConstOk 27 mlkemDeserialize11ROSpec`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize.Deserialize11

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
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize.Specs (
  PortableDeserializeArgs
  PortableDeserializePurePre
  deserializeChunkBytes
  mlkemDeserialize11ROSpec
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

gen_block_fetches mlkem 27 mlkemMultiLib MlKemPlacement 91 [0x0 → 0x140]

private theorem getLsbD_ofNat64_true (n k : Nat)
    (h : decide ((BitVec.ofNat 64 n).getLsbD k = true) = true) :
    (BitVec.ofNat 64 n).getLsbD k = true := of_decide_eq_true h

private theorem getLsbD_ofNat64_false (n k : Nat)
    (h : decide ((BitVec.ofNat 64 n).getLsbD k = false) = true) :
    (BitVec.ofNat 64 n).getLsbD k = false := of_decide_eq_true h

private theorem forall_lt_16 {P : Nat → Prop}
    (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3)
    (h4 : P 4) (h5 : P 5) (h6 : P 6) (h7 : P 7)
    (h8 : P 8) (h9 : P 9) (h10 : P 10) (h11 : P 11)
    (h12 : P 12) (h13 : P 13) (h14 : P 14) (h15 : P 15) :
    ∀ n, n < 16 → P n
  | 0, _ => h0 | 1, _ => h1 | 2, _ => h2 | 3, _ => h3
  | 4, _ => h4 | 5, _ => h5 | 6, _ => h6 | 7, _ => h7
  | 8, _ => h8 | 9, _ => h9 | 10, _ => h10 | 11, _ => h11
  | 12, _ => h12 | 13, _ => h13 | 14, _ => h14 | 15, _ => h15
  | _ + 16, h => absurd h (by omega)

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

private theorem mlkemConstOk_map {j : Nat} {α β : Type} {spec : Spec α} {spec' : Spec β}
    (h : MlKemBlockConstOk j spec)
    (hmap : ∀ (y : β) (R : SepProp) (s0 : State),
      (s0.mem ⊨ spec'.pre y s0 ∗ R) →
      ∃ x R', (s0.mem ⊨ spec.pre x s0 ∗ R') ∧
        ∀ sf, (sf.mem ⊨ spec.post x s0 sf ∗ R') → (sf.mem ⊨ spec'.post y s0 sf ∗ R))
    (hpan : spec.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hex : spec.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom : spec.onOom = fun _ _ _ => ⌜False⌝ := by rfl) :
    MlKemBlockConstOk j spec' := by
  intro _
  refine subroutine_ok_map h (fun y R s0 hpre => ?_)
    (h_no_panic := fun x R' s0 sf _ hp => by
      dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec] at hp
      rw [hpan] at hp; exact not_satisfies_false_sepConj hp)
    (h_no_exit := fun x c R' s0 sf _ he => by
      dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec] at he
      rw [hex] at he; exact not_satisfies_false_sepConj he)
    (h_oom := fun x y R R' s0 sf _ ho => by
      dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec] at ho
      rw [hoom] at ho; exact False.elim (not_satisfies_false_sepConj ho))
  dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec] at hpre
  rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre_spec⟩ := hpre
  obtain ⟨x, R', hpre_x, hpost_x⟩ := hmap y R s0 hpre_spec
  refine ⟨x, R', ?_, fun sf hpost => ?_⟩
  · dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec]
    rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, pure_sepConj_of_true hcl0]
    exact hpre_x
  · dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec] at hpost ⊢
    exact hpost_x sf hpost

private theorem lift_deserialize_nsp {j d : Nat} (hj : j < mlkemMultiLib.blocks.length)
    (hbase : MlKemBlockConstOk j (mlkemDeserializeBaseSpec d)) :
    MlKemBlockConstOk j (mlkemDeserializeROSpec d) := by
  intro _
  exact (mlkemConstOk_map (spec' := mlkemDeserializeROSpec d)
    (mlkemBlockConstOk_withNonSyscallPreserved hbase (hj := hj)
      (h_pre := fun mpl x R s0 h => by
        dsimp [mlkemDeserializeBaseSpec, mlkemDeserializeROSpec, PortableDeserializePurePre] at h ⊢
        simpa [stripS_sp, stripS_readReg64, stripS_readReg32, stripS_vregs, stripS_regs] using h)
      (h_post := fun mpl x R s0 sf hnsp h => by
        dsimp [mlkemDeserializeBaseSpec, mlkemDeserializeROSpec] at h ⊢
        simpa [stripS_sp, stripS_readReg64, stripS_readReg32, stripS_vregs, stripS_regs,
          stripS_mem, stripExecOutside_eq_iff_of_perm_eq (mlkemKeep mpl) hnsp.2.1] using h))
    fun args R _s0 hpre => ⟨args, R, hpre, fun _sf hpost => by
      dsimp only [withNonSyscallPreserved, mlkemDeserializeBaseSpec,
        mlkemDeserializeROSpec] at hpost ⊢
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      exact ⟨⟨hpost.1, hpost.2.1⟩, hpost.2.2⟩⟩)

private theorem entails_deserialize_post (d : Nat) {a : PortableDeserializeArgs}
    {out : List (BitVec 8)} {sp : BitVec 64} {w0 w1 : BitVec 64}
    (heq : out = deserializeChunkBytes d a.inBytes) :
    ((a.outPtr ↦ₛ out) ∗ (a.inPtr ↦ᵣ a.inBytes) ∗
      (((sp - 16#64) ↦₆₄ w0) ∗ ((sp - 8#64) ↦₆₄ w1))) ⊢
    ((a.outPtr ↦ₛ deserializeChunkBytes d a.inBytes) ∗
      (a.inPtr ↦ᵣ a.inBytes) ∗ stackAt sp 16) := by
  subst heq
  exact sepConj_mono_right (sepConj_mono_right (stackAt16_two_entails sp w0 w1))

set_option maxHeartbeats 400000 in
private theorem blk27_deserialize11_base_ok :
    MlKemBlockConstOk 27 (mlkemDeserializeBaseSpec 11) := by
  intro _
  refine mlkemLeaf_ok (j := 27) mlkemPC27 mlkemPl27 (spec := mlkemDeserializeBaseSpec 11)
    (h := fun b hb hbase => ?_)
  apply subroutine_ok_of_sepWP_init
  intro a R s0 hpc hrun hpre _hsp
  dsimp only [ToBaseSpec.toSpec, mlkemDeserializeBaseSpec, mlkemDeserializeROSpec,
    PortableDeserializePurePre] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx8, hx0, hx1, hin_len⟩, hspat⟩ := hpre
  have hx8' : s0.readReg64 (Reg.gpr 8#5) = a.outPtr := hx8
  have hx0' : s0.readReg64 (Reg.gpr 0#5) = a.inPtr := hx0
  have hx1' : 2 * 11 ≤ (s0.readReg64 (Reg.gpr 1#5)).toNat := hx1
  have hspat_stk : s0.mem ⊨ stackAt s0.sp 16 ∗
      (memRegion a.outPtr 32 ∗ (a.inPtr ↦ᵣ a.inBytes) ∗ R) :=
    Satisfies.mono (by sep_frame) hspat
  obtain ⟨w0, w1, hspat'⟩ := satisfies_stackAt16_two hspat_stk
  refine ⟨memRegion a.outPtr 32 ∗ (a.inPtr ↦ᵣ a.inBytes) ∗
    (((s0.sp - 16#64) ↦₆₄ w0) ∗ ((s0.sp - 8#64) ↦₆₄ w1)),
    Satisfies.mono (by sep_frame) hspat', ?_⟩
  apply SepWP.memRegion_bytes a.outPtr 32
  intro out₀ hout₀
  wp_steps 5
  wp_if
  · exfalso; simp only [BitVec.ule_iff_toNat_le, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at *; omega
  wp_steps 2
  wp_if
  · exfalso; simp only [BitVec.ule_iff_toNat_le, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at *; omega
  wp_steps
  apply SepWP.weaken_pre
    (Entails.trans
      (by sep_frame : _ ⊢
        (a.outPtr ↦ₛ _) ∗ (a.inPtr ↦ᵣ a.inBytes) ∗
          (((s0.sp - 16#64) ↦₆₄ _) ∗ ((s0.sp - 8#64) ↦₆₄ _)))
      (entails_deserialize_post 11 ?_))
  · apply SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun])
    refine ⟨fun hm => ?_, by simp [wp_norm], by simp [CalleeSavedPreserved, wp_norm]⟩
    change _ ⊨ (⌜_ = s0.vregs⌝ ∗ _) ∗ R
    rw [sepConj_assoc, pure_sepConj_of_true
      (by simp only [vregs_writeReg64, vregs_setPState, vregs_setPC, vregs_setMem])]
    exact hm
  · refine eq_deserializeChunkBytes_of_halfwordTable 11 a.inBytes
      (by repeat apply halfwordTable_write16
          · exact halfwordTable_init hout₀
          all_goals decide) ?_
    apply forall_lt_16 <;>
    · simp only [Nat.reduceDiv, Nat.reduceEqDiff, ite_true, ite_false]
      refine eq_deserializeChunkCoeff_of_bits 11 a.inBytes hin_len _ (by decide) _ ?_
      apply forall_lt_16 <;>
        simp (disch := decide) only [
          BitVec.zeroExtend, BitVec.truncate,
          BitVec.getLsbD_setWidth,
          BitVec.getLsbD_and,
          BitVec.getLsbD_or,
          BitVec.getLsbD_shiftLeft,
          BitVec.getLsbD_ushiftRight,
          getLsbD_ofNat64_true,
          getLsbD_ofNat64_false,
          getLsbD_8_of_ge,
          Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod,
          Nat.reduceLT,
          decide_true, decide_false, ite_true, ite_false,
          Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false,
          Bool.false_or, Bool.or_false,
          Bool.not_true, Bool.not_false]

/-- `B27` (`PortableVector::deserialize_11`) read-only contract (`16`-byte stack)
    with `NonSyscallPreserved`. -/
theorem blk27_deserialize11_RO_ok : MlKemBlockConstOk 27 mlkemDeserialize11ROSpec :=
  lift_deserialize_nsp (by decide) blk27_deserialize11_base_ok

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize.Deserialize11
