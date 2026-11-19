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
public import ProofLib.SepLogic.SafeSepWP
public import LibsignalBinary.Specifications.LibsignalSpqrV1.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import LibsignalBinary.Proofs.HookDischarge.Libc.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.RustStd.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.EncapsStateToBytes -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base -- proof-setup: allow-public-import
public meta import ProofLib.ProgramReflection
public meta import ProofLib.GenDecodes
public meta import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLiftBase

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open scoped ProofLib.ProgramReflection
open ProofLib.ProgramReflection (WordTree)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (SpecSimulates)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (withNonSyscallPreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.EncapsStateToBytes (
  encapsStateBytes encapsStateBytes_length mlkem768Encaps1With_eq toByteVec_eq_of_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly zeroPoly mlkem768Incremental mlkem768Encaps1With sampleNtt sampleMatrixWith
  sampleVecCbd2 samplePolyCbd2 polyNtt polyInvNtt polyAdd vecDotNtt compressAndEncode
  sha3_512List shake256List toByteVec Mlkem768Encaps1Terminates Shake128MatrixTerminates
  polyToCenteredI16Bytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  withMlKemRoOk sepWP_seq_env cell_entails_memRegion8)

/-! ## Block `3` (`encapsulate1_serialized`) and Block `19` (`encapsulate1`) Programs -/

@[expose] def blkLib03 : PlacedLib := mlkemMultiLib.blockLib 3
@[expose] def blkPl03 [MlKemPlacement] : Placement := mlkemMultiLib.blockPlacement mlkemMpl 3

theorem blkPlaceable03 [MlKemPlacement] : blkLib03.Placeable blkPl03 :=
  mlkemMultiLib.placeable_blockLib (by decide) MlKemPlacement.placeable

@[expose] def blkPC03 [MlKemPlacement] : Program := blkLib03.program blkPl03
@[expose] def blkProg03 : Program := { code := blkLib03.text.code, symbols := blkLib03.text.symbols }

set_option maxRecDepth 200000 in
@[expose] def blkTree03 : WordTree := word_tree_of% blkProg03

set_option maxRecDepth 200000 in
theorem blk03_code_eq : blkLib03.text.code = blkTree03.toBytes := by rfl_kernel

theorem blk03_tree_size : blkTree03.checkSize? = some 7114 := by rfl_kernel

@[expose] def blkLib19 : PlacedLib := mlkemMultiLib.blockLib 19
@[expose] def blkPl19 [MlKemPlacement] : Placement := mlkemMultiLib.blockPlacement mlkemMpl 19

theorem blkPlaceable19 [MlKemPlacement] : blkLib19.Placeable blkPl19 :=
  mlkemMultiLib.placeable_blockLib (by decide) MlKemPlacement.placeable

@[expose] def blkPC19 [MlKemPlacement] : Program := blkLib19.program blkPl19
@[expose] def blkProg19 : Program := { code := blkLib19.text.code, symbols := blkLib19.text.symbols }
@[expose] def blkTree19 : WordTree := word_tree_of% blkProg19

theorem blk19_code_eq : blkLib19.text.code = blkTree19.toBytes := by rfl_kernel

theorem blk19_tree_size : blkTree19.checkSize? = some 28 := by rfl_kernel

/-! ## `SepWP` / `SafeSepWP` Environment Threading and `SpecSimulates` Lifting -/

/-- Enrich a `SepWP` postcondition with reached `pc`, `.Running`, `CodeLoaded`, and `MlKemRoOk`. -/
theorem sepWP_with_env {prog : Program} {target : BitVec 64} {s : State}
    {P : SepProp} {post : State → SepProp → Prop} {mpl : MultiPlacement}
    (hcl : mlkemMultiLib.CodeLoaded mpl s.mem)
    (hro : MlKemRoOk mpl s.mem)
    (h : SepWP prog target s P post) :
    SepWP prog target s P (fun sf Pf =>
      sf.pc = target ∧ sf.status = .Running ∧
      mlkemMultiLib.CodeLoaded mpl sf.mem ∧ MlKemRoOk mpl sf.mem ∧ post sf Pf) :=
  sepWP_seq_env hcl hro h fun _sm _Pm hpc hrun hcl' hro' hp => by
    apply SepWP.done
    · exact hpc
    · exact hrun
    · exact ⟨hpc, hrun, hcl', hro', hp⟩

/-- Sequence a total `SepWP` segment before a partial `SafeSepWP` continuation while preserving
    `CodeLoaded` and `MlKemRoOk`. -/
theorem safeSepWP_seq_env {prog : Program} {mid : BitVec 64} {s : State}
    {P : SepProp} {post1 Q : State → SepProp → Prop} {mpl : MultiPlacement}
    (hcl : mlkemMultiLib.CodeLoaded mpl s.mem)
    (hro : MlKemRoOk mpl s.mem)
    (h1 : SepWP prog mid s P post1)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running →
      mlkemMultiLib.CodeLoaded mpl sm.mem → MlKemRoOk mpl sm.mem →
      post1 sm Pm → SafeSepWP prog sm Pm Q) :
    SafeSepWP prog s P Q :=
  SafeSepWP.of_sepWP <| sepWP_seq_env hcl hro h1 fun sm Pm hpc hrun hcl' hro' hp => by
    apply SepWP.done
    · exact hpc
    · exact hrun
    · exact h2 sm Pm hpc hrun hcl' hro' hp

/-- Partial-correctness counterpart to `subroutine_ok_of_simulates`. -/
theorem safe_subroutine_ok_of_simulates {α β : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} {spec' : Spec β}
    (hok : safe_subroutine_ok prog entry spec)
    (hsim : SpecSimulates spec spec') :
    safe_subroutine_ok prog entry spec' := by
  intro y R s0 hentry hpre
  obtain ⟨x, R₁, hpre_x, hout⟩ := hsim y R s0 hpre
  exact (hok x R₁ s0 hentry hpre_x).mono hout

/-! ## Callee-Saved Spill Frames for `B03` (`160` B) and `B19` (`16` B) -/

/-- `160`-byte callee-saved register save area at `spSave = sp0 - 160 = sp + 16864` in `B03`. -/
@[expose] def SavedFrame03 (spSave : BitVec 64) (s0 : State) : SepProp :=
  (spSave ↦₆₄ (s0.readVReg128 15#5).truncate 64) ∗
  ((spSave + 8#64) ↦₆₄ (s0.readVReg128 14#5).truncate 64) ∗
  ((spSave + 16#64) ↦₆₄ (s0.readVReg128 13#5).truncate 64) ∗
  ((spSave + 24#64) ↦₆₄ (s0.readVReg128 12#5).truncate 64) ∗
  ((spSave + 32#64) ↦₆₄ (s0.readVReg128 11#5).truncate 64) ∗
  ((spSave + 40#64) ↦₆₄ (s0.readVReg128 10#5).truncate 64) ∗
  ((spSave + 48#64) ↦₆₄ (s0.readVReg128 9#5).truncate 64) ∗
  ((spSave + 56#64) ↦₆₄ (s0.readVReg128 8#5).truncate 64) ∗
  ((spSave + 64#64) ↦₆₄ s0.readReg64 .fp) ∗
  ((spSave + 72#64) ↦₆₄ s0.readReg64 .lr) ∗
  ((spSave + 80#64) ↦₆₄ s0.readReg64 .x28) ∗
  ((spSave + 88#64) ↦₆₄ s0.readReg64 (.gpr 27#5)) ∗
  ((spSave + 96#64) ↦₆₄ s0.readReg64 (.gpr 26#5)) ∗
  ((spSave + 104#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗
  ((spSave + 112#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗
  ((spSave + 120#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((spSave + 128#64) ↦₆₄ s0.readReg64 .x22) ∗
  ((spSave + 136#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((spSave + 144#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((spSave + 152#64) ↦₆₄ s0.readReg64 .x19)

theorem savedFrame03_entails_memRegion160 (spSave : BitVec 64) (s0 : State) :
    SavedFrame03 spSave s0 ⊢ memRegion spSave 160 := by
  unfold SavedFrame03
  have hsplit :
      memRegion spSave 160 =
        memRegion spSave 8 ∗ memRegion (spSave + 8#64) 8 ∗
        memRegion (spSave + 16#64) 8 ∗ memRegion (spSave + 24#64) 8 ∗
        memRegion (spSave + 32#64) 8 ∗ memRegion (spSave + 40#64) 8 ∗
        memRegion (spSave + 48#64) 8 ∗ memRegion (spSave + 56#64) 8 ∗
        memRegion (spSave + 64#64) 8 ∗ memRegion (spSave + 72#64) 8 ∗
        memRegion (spSave + 80#64) 8 ∗ memRegion (spSave + 88#64) 8 ∗
        memRegion (spSave + 96#64) 8 ∗ memRegion (spSave + 104#64) 8 ∗
        memRegion (spSave + 112#64) 8 ∗ memRegion (spSave + 120#64) 8 ∗
        memRegion (spSave + 128#64) 8 ∗ memRegion (spSave + 136#64) 8 ∗
        memRegion (spSave + 144#64) 8 ∗ memRegion (spSave + 152#64) 8 := by
    rw [memRegion_split' (b' := spSave + 8#64) (n := 8) (k := 152) rfl (by bv_omega) (by decide),
      memRegion_split' (b := spSave + 8#64) (b' := spSave + 16#64) (n := 8) (k := 144) rfl (by bv_omega) (by decide),
      memRegion_split' (b := spSave + 16#64) (b' := spSave + 24#64) (n := 8) (k := 136) rfl (by bv_omega) (by decide),
      memRegion_split' (b := spSave + 24#64) (b' := spSave + 32#64) (n := 8) (k := 128) rfl (by bv_omega) (by decide),
      memRegion_split' (b := spSave + 32#64) (b' := spSave + 40#64) (n := 8) (k := 120) rfl (by bv_omega) (by decide),
      memRegion_split' (b := spSave + 40#64) (b' := spSave + 48#64) (n := 8) (k := 112) rfl (by bv_omega) (by decide),
      memRegion_split' (b := spSave + 48#64) (b' := spSave + 56#64) (n := 8) (k := 104) rfl (by bv_omega) (by decide),
      memRegion_split' (b := spSave + 56#64) (b' := spSave + 64#64) (n := 8) (k := 96) rfl (by bv_omega) (by decide),
      memRegion_split' (b := spSave + 64#64) (b' := spSave + 72#64) (n := 8) (k := 88) rfl (by bv_omega) (by decide),
      memRegion_split' (b := spSave + 72#64) (b' := spSave + 80#64) (n := 8) (k := 80) rfl (by bv_omega) (by decide),
      memRegion_split' (b := spSave + 80#64) (b' := spSave + 88#64) (n := 8) (k := 72) rfl (by bv_omega) (by decide),
      memRegion_split' (b := spSave + 88#64) (b' := spSave + 96#64) (n := 8) (k := 64) rfl (by bv_omega) (by decide),
      memRegion_split' (b := spSave + 96#64) (b' := spSave + 104#64) (n := 8) (k := 56) rfl (by bv_omega) (by decide),
      memRegion_split' (b := spSave + 104#64) (b' := spSave + 112#64) (n := 8) (k := 48) rfl (by bv_omega) (by decide),
      memRegion_split' (b := spSave + 112#64) (b' := spSave + 120#64) (n := 8) (k := 40) rfl (by bv_omega) (by decide),
      memRegion_split' (b := spSave + 120#64) (b' := spSave + 128#64) (n := 8) (k := 32) rfl (by bv_omega) (by decide),
      memRegion_split' (b := spSave + 128#64) (b' := spSave + 136#64) (n := 8) (k := 24) rfl (by bv_omega) (by decide),
      memRegion_split' (b := spSave + 136#64) (b' := spSave + 144#64) (n := 8) (k := 16) rfl (by bv_omega) (by decide),
      memRegion_split' (b := spSave + 144#64) (b' := spSave + 152#64) (n := 8) (k := 8) rfl (by bv_omega) (by decide)]
  rw [hsplit]
  refine sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
      (cell_entails_memRegion8 _ _)))))))))))))))))))

/-- `16`-byte `(x29, x30)` save area at `spSave = sp1 + 128 = sp0 - 16` in `B19`. -/
@[expose] def SavedFrame19 (spSave : BitVec 64) (s0 : State) : SepProp :=
  (spSave ↦₆₄ s0.readReg64 .fp) ∗ ((spSave + 8#64) ↦₆₄ s0.readReg64 .lr)

theorem savedFrame19_entails_memRegion16 (spSave : BitVec 64) (s0 : State) :
    SavedFrame19 spSave s0 ⊢ memRegion spSave 16 := by
  unfold SavedFrame19
  rw [memRegion_split' (b' := spSave + 8#64) (n := 8) (k := 8) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (cell_entails_memRegion8 _ _) (cell_entails_memRegion8 _ _)

/-- Callee-saved registers not spilled by `B19` (`x19..x28`, `d8..d15`). -/
@[expose] def UnspilledSaved19 (s0 s : State) : Prop :=
  s.readReg64 .x19 = s0.readReg64 .x19 ∧
  s.readReg64 .x20 = s0.readReg64 .x20 ∧
  s.readReg64 .x21 = s0.readReg64 .x21 ∧
  s.readReg64 .x22 = s0.readReg64 .x22 ∧
  s.readReg64 .x23 = s0.readReg64 .x23 ∧
  s.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5) ∧
  s.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5) ∧
  s.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) ∧
  s.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) ∧
  s.readReg64 .x28 = s0.readReg64 .x28 ∧
  (s.readVReg128 8#5).truncate 64 = (s0.readVReg128 8#5).truncate 64 ∧
  (s.readVReg128 9#5).truncate 64 = (s0.readVReg128 9#5).truncate 64 ∧
  (s.readVReg128 10#5).truncate 64 = (s0.readVReg128 10#5).truncate 64 ∧
  (s.readVReg128 11#5).truncate 64 = (s0.readVReg128 11#5).truncate 64 ∧
  (s.readVReg128 12#5).truncate 64 = (s0.readVReg128 12#5).truncate 64 ∧
  (s.readVReg128 13#5).truncate 64 = (s0.readVReg128 13#5).truncate 64 ∧
  (s.readVReg128 14#5).truncate 64 = (s0.readVReg128 14#5).truncate 64 ∧
  (s.readVReg128 15#5).truncate 64 = (s0.readVReg128 15#5).truncate 64

/-! ## Pure `encapsulate1` Output Projections and `mlkem768Incremental.encaps1` Bridges -/

@[expose] noncomputable def encaps1OutCt1 (hdr rand : List (BitVec 8)) : List (BitVec 8) :=
  let seed := hdr.take 32
  let pkHash := (hdr.drop 32).take 32
  let m := rand.take 32
  let hashed := sha3_512List (m ++ pkHash)
  let coins := (hashed.drop 32).take 32
  let aTrans := sampleMatrixWith sampleNtt 3 seed false
  let rHat := (sampleVecCbd2 3 coins 0).map polyNtt
  let e1 := sampleVecCbd2 3 coins 3
  let uVec : Array Poly := Array.ofFn (n := 3) fun ⟨i, _⟩ =>
    polyAdd (polyInvNtt (vecDotNtt 3 (aTrans.getD i #[]) rHat)) (e1.getD i zeroPoly)
  ((List.range 3).map fun i => compressAndEncode 10 (uVec.getD i zeroPoly)).flatten

@[expose] def encaps1OutEs (hdr rand : List (BitVec 8)) : List (BitVec 8) :=
  let pkHash := (hdr.drop 32).take 32
  let m := rand.take 32
  let hashed := sha3_512List (m ++ pkHash)
  let coins := (hashed.drop 32).take 32
  let rHat := (sampleVecCbd2 3 coins 0).map polyNtt
  let e2 := samplePolyCbd2 (shake256List 128 (coins ++ [6#8]))
  encapsStateBytes rHat e2 m

@[expose] def encaps1OutSs (hdr rand : List (BitVec 8)) : List (BitVec 8) :=
  let pkHash := (hdr.drop 32).take 32
  let m := rand.take 32
  (sha3_512List (m ++ pkHash)).take 32

private theorem drop32_take32_take64 (hdr : List (BitVec 8)) :
    ((hdr.take 64).drop 32).take 32 = (hdr.drop 32).take 32 := by
  rw [List.drop_take]
  simp [List.take_take]

theorem encaps1OutCt1_take64 (hdr rand : List (BitVec 8)) :
    encaps1OutCt1 (hdr.take 64) rand = encaps1OutCt1 hdr rand := by
  unfold encaps1OutCt1
  simp [List.take_take, drop32_take32_take64]

theorem encaps1OutEs_take64 (hdr rand : List (BitVec 8)) :
    encaps1OutEs (hdr.take 64) rand = encaps1OutEs hdr rand := by
  unfold encaps1OutEs
  simp [drop32_take32_take64]

theorem encaps1OutSs_take64 (hdr rand : List (BitVec 8)) :
    encaps1OutSs (hdr.take 64) rand = encaps1OutSs hdr rand := by
  unfold encaps1OutSs
  simp [drop32_take32_take64]

theorem mlkem768Encaps1With_sampleNtt_eq (hdr rand : List (BitVec 8)) (hhdr : 64 ≤ hdr.length) :
    mlkem768Encaps1With sampleNtt hdr rand =
      some (encaps1OutCt1 hdr rand, encaps1OutEs hdr rand, encaps1OutSs hdr rand) := by
  simpa [encaps1OutCt1, encaps1OutEs, encaps1OutSs] using
    mlkem768Encaps1With_eq sampleNtt hdr rand hhdr

theorem mlkem768Incremental_encaps1_lt64 (hdr : List (BitVec 8))
    (rand : List.Vector (BitVec 8) 32) (hhdr : hdr.length < 64) :
    mlkem768Incremental.encaps1 hdr rand = none := by
  simp [mlkem768Incremental, mlkem768Encaps1With, hhdr]

theorem mlkem768Incremental_encaps1_ge64 (hdr : List (BitVec 8))
    (rand : List.Vector (BitVec 8) 32) (hhdr : 64 ≤ hdr.length) :
    mlkem768Incremental.encaps1 hdr rand =
      some (toByteVec 960 (encaps1OutCt1 hdr rand.toList),
            toByteVec 2080 (encaps1OutEs hdr rand.toList),
            toByteVec 32 (encaps1OutSs hdr rand.toList)) := by
  simp [mlkem768Incremental, mlkem768Encaps1With_sampleNtt_eq hdr rand.toList hhdr]

/-! ## Core Tight-Stack Specifications (`B03`: `18160` B, `B19`: `18304` B) and Projections -/

/-- Call arguments for `B03` (`encapsulate1_serialized`, tight stack `18160` B). -/
structure MlkemBlk03Args where
  ret   : BitVec 64
  hdrA  : BitVec 64
  hdr64 : List (BitVec 8)
  randA : BitVec 64
  rand  : List (BitVec 8)
  esA   : BitVec 64
  ssA   : BitVec 64

/-- Raw tight-stack (`18160` B) specification for `B03` (`x4 = 2080#64`, `x6 = 32#64`). -/
@[expose] noncomputable def mlkemBlk03RawSpec : Spec MlkemBlk03Args where
  pre := fun a s =>
    ⌜s.readReg64 .x0 = a.ret ∧ s.readReg64 .x1 = a.hdrA ∧
      s.readReg64 .x2 = a.randA ∧ s.readReg64 .x3 = a.esA ∧
      s.readReg64 .x4 = 2080#64 ∧ s.readReg64 .x5 = a.ssA ∧
      s.readReg64 .x6 = 32#64 ∧
      a.hdr64.length = 64 ∧ a.rand.length = 32⌝ ∗
      (a.hdrA ↦ₛ a.hdr64) ∗ (a.randA ↦ₛ a.rand) ∗
      memRegion a.ret 961 ∗ memRegion a.esA 2080 ∗ memRegion a.ssA 32 ∗
      stackAt s.sp 18160
  post := fun a s0 _sf =>
    ⌜(encaps1OutCt1 a.hdr64 a.rand).length = 960 ∧
      (encaps1OutEs a.hdr64 a.rand).length = 2080 ∧
      (encaps1OutSs a.hdr64 a.rand).length = 32⌝ ∗
      (a.hdrA ↦ₛ a.hdr64) ∗ (a.randA ↦ₛ a.rand) ∗
      (a.ret ↦₈ 0#8) ∗ ((a.ret + 1#64) ↦ₛ encaps1OutCt1 a.hdr64 a.rand) ∗
      (a.esA ↦ₛ encaps1OutEs a.hdr64 a.rand) ∗
      (a.ssA ↦ₛ encaps1OutSs a.hdr64 a.rand) ∗
      stackAt s0.sp 18160
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Lifted tight-stack (`18160` B) specification for `B03` with `MlKemRoOk` and
    `NonSyscallPreserved`. -/
@[expose] noncomputable def mlkemBlk03CoreSpec (mpl : MultiPlacement) : Spec MlkemBlk03Args :=
  withNonSyscallPreserved (withMlKemRoOk mpl mlkemBlk03RawSpec)

/-- Total-correctness variant of `mlkemBlk03RawSpec` carrying `Shake128MatrixTerminates`. -/
@[expose] noncomputable def mlkemBlk03TermRawSpec : Spec MlkemBlk03Args where
  pre := fun a s =>
    ⌜Shake128MatrixTerminates (a.hdr64.take 32) 3⌝ ∗ mlkemBlk03RawSpec.pre a s
  post := mlkemBlk03RawSpec.post
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

@[expose] noncomputable def mlkemBlk03TermCoreSpec (mpl : MultiPlacement) : Spec MlkemBlk03Args :=
  withNonSyscallPreserved (withMlKemRoOk mpl mlkemBlk03TermRawSpec)

/-- Call arguments for `B19` (`mlkem768::incremental::encapsulate1`, tight stack `18304` B). -/
structure MlkemEncaps1Args where
  ret   : BitVec 64
  hdrA  : BitVec 64
  hdr   : List (BitVec 8)
  randA : BitVec 64
  rand  : List.Vector (BitVec 8) 32
  esA   : BitVec 64
  ssA   : BitVec 64

/-- Raw tight-stack (`18304` B) specification for `B19` covering both `hdr.length < 64`
    (concrete `[1#8, 0#8]` error return) and `64 ≤ hdr.length` (`mlkem768Incremental.encaps1`). -/
@[expose] noncomputable def mlkemEncaps1RawSpec : Spec MlkemEncaps1Args where
  pre := fun a s =>
    ⌜s.readReg64 .x8 = a.ret ∧ s.readReg64 .x0 = a.hdrA ∧
      (s.readReg64 .x1).toNat = a.hdr.length ∧ s.readReg64 .x2 = a.randA ∧
      s.readReg64 .x3 = a.esA ∧ s.readReg64 .x4 = 2080#64 ∧
      s.readReg64 .x5 = a.ssA ∧ s.readReg64 .x6 = 32#64⌝ ∗
      (a.hdrA ↦ₛ a.hdr) ∗ (a.randA ↦ₛ a.rand.toList) ∗
      memRegion a.ret 961 ∗ memRegion a.esA 2080 ∗ memRegion a.ssA 32 ∗
      stackAt s.sp 18304
  post := fun a s0 _sf =>
    (a.hdrA ↦ₛ a.hdr) ∗ (a.randA ↦ₛ a.rand.toList) ∗
      (match mlkem768Incremental.encaps1 a.hdr a.rand with
       | some (ct1, es, ss) =>
           (a.ret ↦₈ 0#8) ∗ ((a.ret + 1#64) ↦ₛ ct1.toList) ∗
           (a.esA ↦ₛ es.toList) ∗ (a.ssA ↦ₛ ss.toList)
       | none =>
           (a.ret ↦₈ 1#8) ∗ ((a.ret + 1#64) ↦₈ 0#8) ∗
           memRegion (a.ret + 2#64) 959 ∗
           memRegion a.esA 2080 ∗ memRegion a.ssA 32) ∗
      stackAt s0.sp 18304
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Tight-stack (`18304` B) core specification for `B19` (`blk19_encaps1_safe_ok`). -/
@[expose] noncomputable def mlkemEncaps1CoreSpec (mpl : MultiPlacement) : Spec MlkemEncaps1Args :=
  withNonSyscallPreserved (withMlKemRoOk mpl mlkemEncaps1RawSpec)

/-- Total-correctness tight-stack (`18304` B) specification for `B19` carrying
    `Mlkem768Encaps1Terminates a.hdr` (`blk19_encaps1_ok`). -/
@[expose] noncomputable def mlkemEncaps1TermRawSpec : Spec MlkemEncaps1Args where
  pre := fun a s =>
    ⌜Mlkem768Encaps1Terminates a.hdr⌝ ∗ mlkemEncaps1RawSpec.pre a s
  post := mlkemEncaps1RawSpec.post
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

@[expose] noncomputable def mlkemEncaps1TermCoreSpec (mpl : MultiPlacement) : Spec MlkemEncaps1Args :=
  withNonSyscallPreserved (withMlKemRoOk mpl mlkemEncaps1TermRawSpec)

/-- Polymorphic caller-struct projection specification parameterized by stack size `stk : Nat`
    and `K : MlKem`, matching `Hooks.mlkemEncaps1Spec K` by `rfl` at `stk = extHookStack`. -/
@[expose] def mlkemEncaps1ProjSpec (stk : Nat) (K : MlKem) {C : Type}
    (ret : C → BitVec 64)
    (hdrA : C → BitVec 64) (hdr : C → List (BitVec 8))
    (randA : C → BitVec 64) (rand : C → List.Vector (BitVec 8) 32)
    (esA : C → BitVec 64) (ssA : C → BitVec 64) : Spec C where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = ret x ∧ s.readReg64 .x0 = hdrA x ∧
      (s.readReg64 .x1).toNat = (hdr x).length ∧ s.readReg64 .x2 = randA x ∧
      s.readReg64 .x3 = esA x ∧ s.readReg64 .x4 = 2080#64 ∧
      s.readReg64 .x5 = ssA x ∧ s.readReg64 .x6 = 32#64⌝ ∗
      (hdrA x ↦ₛ hdr x) ∗ (randA x ↦ₛ (rand x).toList) ∗
      memRegion (ret x) 961 ∗ memRegion (esA x) 2080 ∗ memRegion (ssA x) 32 ∗
      stackAt s.sp stk
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (hdrA x ↦ₛ hdr x) ∗ (randA x ↦ₛ (rand x).toList) ∗
      (match K.encaps1 (hdr x) (rand x) with
       | some (ct1, es, ss) =>
           (ret x ↦₈ 0#8) ∗ ((ret x + 1#64) ↦ₛ ct1.toList) ∗
           (esA x ↦ₛ es.toList) ∗ (ssA x ↦ₛ ss.toList)
       | none =>
           (ret x ↦₈ 1#8) ∗ (∃∗ (err : BitVec 8), ((ret x + 1#64) ↦₈ err)) ∗
           memRegion (ret x + 2#64) 959 ∗
           memRegion (esA x) 2080 ∗ memRegion (ssA x) 32) ∗
      stackAt s0.sp stk

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base
