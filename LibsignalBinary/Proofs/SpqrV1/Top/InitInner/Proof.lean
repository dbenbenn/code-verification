/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.Steps -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbOuter
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

public section

namespace CryptoVerification.SpqrV1.Top.InitInner

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb
open CryptoVerification.SpqrV1.Poly.DecoderPb
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  bv_sub_sub_lit' bv_add_add_lit'

theorem fnAddr_fwd_eq {c : Program} {f1 f2 : String} {o1 o2 d : Nat}
    {b : BitVec 64} {X : String → Option (State → State)}
    (ho1 : c.fnOff f1 = o1) (ho2 : c.fnOff f2 = o2) (hd : o1 + d = o2) :
    (c.rebase b X).fnAddr f1 + BitVec.ofNat 64 d = (c.rebase b X).fnAddr f2 := by
  rw [Program.fnAddr_back (d := d) (b := b) (X := X) ho2 ho1 hd]; bv_omega

theorem stackAt_authNew_split_statesIntoPb (sp : BitVec 64) :
    stackAt sp authNewStackX =
      stackAt sp statesIntoPbStack ∗ memRegion (sp - 16640#64) 10768 := by
  change memRegion (sp - 16640#64) 16640 =
    memRegion (sp - 5872#64) 5872 ∗ memRegion (sp - 16640#64) 10768
  rw [ProofLib.memRegion_split' (b := sp - 16640#64) (n := 10768) (k := 5872)
        (b' := sp - 5872#64) rfl (by bv_omega) (by decide), sepConj_comm]

theorem stackAt_authNew_split_allocHook (sp : BitVec 64) :
    stackAt sp authNewStackX =
      stackAt sp allocHookStack ∗ memRegion (sp - 16640#64) 12544 := by
  change memRegion (sp - 16640#64) 16640 =
    memRegion (sp - 4096#64) 4096 ∗ memRegion (sp - 16640#64) 12544
  rw [ProofLib.memRegion_split' (b := sp - 16640#64) (n := 12544) (k := 4096)
        (b' := sp - 4096#64) rfl (by bv_omega) (by decide), sepConj_comm]

theorem memRegion_24_and_cells_5_eq_cells_8 (sp : BitVec 64) :
    memRegion (sp - 1032#64) 24 ∗ cells (sp - 1008#64) 5 = cells (sp - 1032#64) 8 := by
  rw [← ProofLib.memRegion_cells (sp - 1008#64) 5 (by decide),
      ← ProofLib.memRegion_cells (sp - 1032#64) 8 (by decide)]
  exact (ProofLib.memRegion_split' (b := sp - 1032#64) (n := 24) (k := 40)
    (b' := sp - 1008#64) rfl (by bv_omega) (by decide)).symm

theorem memRegion_24_and_cells_17_eq_cells_20 (sp : BitVec 64) :
    memRegion (sp - 1032#64) 24 ∗ cells (sp - 1008#64) 17 = cells (sp - 1032#64) 20 := by
  rw [← ProofLib.memRegion_cells (sp - 1008#64) 17 (by decide),
      ← ProofLib.memRegion_cells (sp - 1032#64) 20 (by decide)]
  exact (ProofLib.memRegion_split' (b := sp - 1032#64) (n := 24) (k := 136)
    (b' := sp - 1008#64) rfl (by bv_omega) (by decide)).symm

theorem memRegion_992_split_a2b (sp : BitVec 64) :
    memRegion (sp - 1040#64) 992 =
      cells (sp - 1032#64) 3 ∗ memRegion (sp - 104#64) authenticatorSize ∗
      cells (sp - 1008#64) 5 ∗ memRegion (sp - 968#64) 864 ∗
      memRegion (sp - 1040#64) 8 ∗ memRegion (sp - 56#64) 8 := by
  change memRegion (sp - 1040#64) 992 =
    cells (sp - 1032#64) 3 ∗ memRegion (sp - 104#64) 48 ∗
    cells (sp - 1008#64) 5 ∗ memRegion (sp - 968#64) 864 ∗
    memRegion (sp - 1040#64) 8 ∗ memRegion (sp - 56#64) 8
  rw [ProofLib.memRegion_split' (b := sp - 1040#64) (n := 8) (k := 984) (b' := sp - 1032#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 1032#64) (n := 24) (k := 960) (b' := sp - 1008#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 1008#64) (n := 40) (k := 920) (b' := sp - 968#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 968#64) (n := 864) (k := 56) (b' := sp - 104#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 104#64) (n := 48) (k := 8) (b' := sp - 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_cells (sp - 1032#64) 3 (by decide),
      ProofLib.memRegion_cells (sp - 1008#64) 5 (by decide)]
  ac_rfl

theorem memRegion_48_and_8_eq_56 (sp : BitVec 64) :
    memRegion (sp - 104#64) 48 ∗ memRegion (sp - 56#64) 8 = memRegion (sp - 104#64) 56 :=
  (ProofLib.memRegion_split' (b := sp - 104#64) (n := 48) (k := 8)
    (b' := sp - 56#64) rfl (by bv_omega) (by decide)).symm

theorem memRegion_992_split_b2a (sp : BitVec 64) :
    memRegion (sp - 1040#64) 992 =
      cells (sp - 1032#64) 3 ∗ memRegion (sp - 104#64) authenticatorSize ∗
      cells (sp - 56#64) 1 ∗ cells (sp - 1008#64) 17 ∗ cells (sp - 872#64) 20 ∗
      cells (sp - 712#64) 17 ∗ (∃∗ b0 : BitVec 8, (sp - 576#64) ↦₈ b0) ∗
      memRegion (sp - 575#64) 7 ∗ memRegion (sp - 568#64) 464 ∗
      memRegion (sp - 1040#64) 8 := by
  change memRegion (sp - 1040#64) 992 =
    cells (sp - 1032#64) 3 ∗ memRegion (sp - 104#64) 48 ∗ cells (sp - 56#64) 1 ∗
    cells (sp - 1008#64) 17 ∗ cells (sp - 872#64) 20 ∗ cells (sp - 712#64) 17 ∗
    (∃∗ b0 : BitVec 8, (sp - 576#64) ↦₈ b0) ∗ memRegion (sp - 575#64) 7 ∗
    memRegion (sp - 568#64) 464 ∗ memRegion (sp - 1040#64) 8
  rw [ProofLib.memRegion_split' (b := sp - 1040#64) (n := 8) (k := 984) (b' := sp - 1032#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 1032#64) (n := 24) (k := 960) (b' := sp - 1008#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 1008#64) (n := 136) (k := 824) (b' := sp - 872#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 872#64) (n := 160) (k := 664) (b' := sp - 712#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 712#64) (n := 136) (k := 528) (b' := sp - 576#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 576#64) (n := 1) (k := 527) (b' := sp - 575#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 575#64) (n := 7) (k := 520) (b' := sp - 568#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 568#64) (n := 464) (k := 56) (b' := sp - 104#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 104#64) (n := 48) (k := 8) (b' := sp - 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_one (sp - 576#64), ProofLib.memRegion_cells (sp - 1032#64) 3 (by decide),
      ProofLib.memRegion_cells (sp - 1008#64) 17 (by decide), ProofLib.memRegion_cells (sp - 872#64) 20 (by decide),
      ProofLib.memRegion_cells (sp - 712#64) 17 (by decide), ProofLib.memRegion_cells (sp - 56#64) 1 (by decide)]
  ac_rfl

theorem memRegion_992_rejoin_b2a (sp : BitVec 64) :
    memRegion (sp - 1032#64) chunkedStatesSize ∗ memRegion (sp - 104#64) 56 ∗
    memRegion (sp - 1040#64) 8 = memRegion (sp - 1040#64) 992 := by
  change memRegion (sp - 1032#64) 928 ∗ memRegion (sp - 104#64) 56 ∗
    memRegion (sp - 1040#64) 8 = memRegion (sp - 1040#64) 992
  rw [ProofLib.memRegion_split' (b := sp - 1040#64) (n := 8) (k := 984) (b' := sp - 1032#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 1032#64) (n := 928) (k := 56) (b' := sp - 104#64) rfl (by bv_omega) (by decide)]
  ac_rfl

/-! ## 3. Subroutine Call Wrappers (`SepWPp`) -/

/-- Return postcondition of `spqr::init_inner` for `SepWPp`. -/
@[expose] def InitInnerPost (A : RustAlloc) (F : ShaCompress) (b : BitVec 64)
    (s0 : State) (x : InitInnerGhost) : State → SepProp → Prop :=
  fun sf Pf =>
    (Pf ⊢
      initInnerResultAt A (F := F) x.out x.v x.d x.authKey ∗
      (x.akPtr ↦ₛ x.authKey) ∗ statesIntoPbJumpTableAt b ∗
      A.pool ∗ stackAt s0.sp initInnerStack) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace

/-- Panic postcondition of `spqr::init_inner` for `SepWPp`. -/
@[expose] def InitInnerPanic (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)

theorem authenticatorAt_expose_frame (A : RustAlloc) (F : ShaCompress) (sp : BitVec 64)
    (authKey : Bytes) (Frame : SepProp) :
    (authenticatorAt A (sp - 104#64) (Authenticator.new F authKey 1#64) ∗
      memRegion (sp - 1032#64) 24 ∗ A.pool ∗ stackAt (sp - 1040#64) authNewStackX) ∗ Frame ⊢
    ∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64,
    ∃∗ a3 : BitVec 64, ∃∗ a4 : BitVec 64, ∃∗ a5 : BitVec 64,
      (((((sp - 104#64) ↦₆₄ a0) ∗ ((sp - 96#64) ↦₆₄ a1) ∗ ((sp - 88#64) ↦₆₄ a2) ∗
         ((sp - 80#64) ↦₆₄ a3) ∗ ((sp - 72#64) ↦₆₄ a4) ∗ ((sp - 64#64) ↦₆₄ a5)) ∗
        authenticatorHeap A a0 a1 a2 a3 a4 a5 (Authenticator.new F authKey 1#64) ∗
        memRegion (sp - 1032#64) 24 ∗ A.pool ∗ stackAt (sp - 1040#64) authNewStackX) ∗ Frame) := by
  have ha := authenticatorAt_expose A (sp - 104#64) (Authenticator.new F authKey 1#64)
  simp only [arm64_norm] at ha
  refine Entails.trans (sepConj_mono_left (sepConj_mono_left ha)) ?_
  simp only [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro a0; apply Entails.sepExists_elim; intro a1
  apply Entails.sepExists_elim; intro a2; apply Entails.sepExists_elim; intro a3
  apply Entails.sepExists_elim; intro a4; apply Entails.sepExists_elim; intro a5
  refine Entails.sepExists_right a0 (Entails.sepExists_right a1 (Entails.sepExists_right a2
    (Entails.sepExists_right a3 (Entails.sepExists_right a4 (Entails.sepExists_right a5 ?_)))))
  exact Entails.of_eq (by ac_rfl)

theorem cells_1032_3_expose (sp : BitVec 64) (Rest : SepProp) :
    cells (sp - 1032#64) 3 ∗ Rest ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
        ((sp - 1032#64) ↦₆₄ w0) ∗ ((sp - 1024#64) ↦₆₄ w1) ∗ ((sp - 1016#64) ↦₆₄ w2) ∗ Rest := by
  cells_unfold; simp only [sepExists_sepConj_left, arm64_norm]
  apply Entails.sepExists_elim; intro w0; apply Entails.sepExists_elim; intro w1
  apply Entails.sepExists_elim; intro w2
  refine Entails.sepExists_right w0 (Entails.sepExists_right w1 (Entails.sepExists_right w2 ?_))
  exact Entails.of_eq (by ac_rfl)

theorem calleeSaved_chain_hi {s0 s sf : State}
    (hcs_hi : s.readReg64 .x22 = s0.readReg64 .x22 ∧ s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcs : CalleeSavedPreserved s sf) :
    sf.readReg64 .x22 = s0.readReg64 .x22 ∧ sf.readReg64 .x23 = s0.readReg64 .x23 ∧
    sf.readReg64 .x24 = s0.readReg64 .x24 ∧ sf.readReg64 .x25 = s0.readReg64 .x25 ∧
    sf.readReg64 .x26 = s0.readReg64 .x26 ∧ sf.readReg64 .x27 = s0.readReg64 .x27 ∧
    calleeSavedVRegs sf = calleeSavedVRegs s0 := by
  dsimp only [CalleeSavedPreserved] at hcs
  rcases hcs_hi with ⟨h22, h23, h24, h25, h26, h27, hvregs⟩
  exact ⟨by simp only [hcs, h22], by simp only [hcs, h23], by simp only [hcs, h24],
         by simp only [hcs, h25], by simp only [hcs, h26], by simp only [hcs, h27],
         by simp only [hcs, hvregs]⟩

theorem calleeSaved_x29 {s sf : State} {v : BitVec 64}
    (h : s.readReg64 .x29 = v) (hcs : CalleeSavedPreserved s sf) : sf.readReg64 .x29 = v := by
  dsimp only [CalleeSavedPreserved] at hcs; simp only [hcs, h]

theorem calleeSaved_x19 {s sf : State} {v : BitVec 64}
    (h : s.readReg64 .x19 = v) (hcs : CalleeSavedPreserved s sf) : sf.readReg64 .x19 = v := by
  dsimp only [CalleeSavedPreserved] at hcs; simp only [hcs, h]

end CryptoVerification.SpqrV1.Top.InitInner
