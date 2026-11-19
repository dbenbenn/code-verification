/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base
import ProofLib.SepLogic.SafeSepWP
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLift
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLiftBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg1HashG
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Matrix
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg4MatVec
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5Dk
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5Pack

/-!
# `B05`: `generate_keypair_compressed` (`Mlkem768.FromSeed.Core05`)

Assembles `Seg1HashG` + `Seg2Matrix` + `Seg3` + `Seg4MatVec` + `Seg5Dk` + `Seg5Pack` (`7,112` words,
tight stack `31,216` B) into partial (`MlKemBlockSafeOk 5`) and total (`MlKemBlockOk 5`) contracts.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Core05

open Arm64 Arm64.Obj ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemBlockOk MlKemBlockSafeOk MlKemPlacement
  mlkemCaller_ok mlkemMpl mlkemSafeCaller_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (withNonSyscallPreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLift (
  mlkemBlockOk_withNonSyscallPreserved mlkemBlockSafeOk_withNonSyscallPreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLiftBase (
  mlkemKeep mlkemRoOk_stripExecOutside stripS_mem stripS_readReg64 stripS_sp)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (mlkem768KeyPairWith sampleNtt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base (
  blkPC05 blkPl05 mlkemGenKeypairRawSpec mlkemGenKeypairTermRawSpec sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg1HashG (seg1_prologue_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Matrix (
  Seg2MatrixExit seg2_matrix_ok seg2_matrix_safe_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3 (seg3_secvecs_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg4MatVec (seg4_matvec_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5Dk (seg5_ek_dk_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5Pack (seg5_pack_ok)

private theorem blk05_tail_from_seg2 [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s0 s2 : State) (seedA outPtr : BitVec 64) (seed : List (BitVec 8))
    (hseed : seed.length = 64) {P2 : SepProp}
    (hex2 : Seg2MatrixExit b s0 seedA outPtr seed (memRegion outPtr 2400) s2 P2) :
    SepWP (blkPC05.rebase b (fun _ => none)) (s0.readReg64 .lr) s2 P2
      (sepPost (fun sf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        ((seedA ↦ₛ seed) ∗ (outPtr ↦ₛ mlkem768KeyPairWith sampleNtt seed) ∗ stackAt s0.sp 31216)) :=
  SepWP.seq (seg3_secvecs_ok hb hbase s0 s2 seedA outPtr seed (memRegion outPtr 2400) hex2)
    fun s3 _ _ _ hex3 =>
    SepWP.seq (seg4_matvec_ok hb hbase s0 s3 seedA outPtr seed (memRegion outPtr 2400) hex3)
      fun s4 _ _ _ hex4 =>
      SepWP.seq (seg5_ek_dk_ok hb hbase s0 s4 seedA outPtr seed hseed (memRegion outPtr 2400) hex4)
        fun s5 _ _ _ hex5 =>
        seg5_pack_ok hb hbase s0 s5 seedA outPtr seed hseed hex5

/-- `B05` (`generate_keypair_compressed`) raw partial-correctness (`MlKemBlockSafeOk 5`) contract. -/
theorem blk05_generate_keypair_raw_safe_ok : MlKemBlockSafeOk 5 mlkemGenKeypairRawSpec := by
  intro _
  refine mlkemSafeCaller_ok blkPC05 blkPl05 rfl rfl fun b hb hbase => ?_
  apply safe_subroutine_ok_of_safeSepWP
  rintro ⟨seedA, seed, outPtr⟩ R s0 hpc hrun hpre hsp0
  dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, mlkemGenKeypairRawSpec] at hpre ⊢
  rw [sepConj_comm _ ⌜mlkemMultiLib.CodeLoaded mlkemMpl s0.mem⌝, sepConj_assoc,
      satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hseed, hro0⟩, hspat⟩ := hpre
  refine ⟨stackAt s0.sp 31216 ∗ (seedA ↦ₛ seed) ∗ memRegion outPtr 2400,
    Satisfies.mono (by sep_frame) hspat, ?_⟩
  refine SafeSepWP.of_sepWP (mid := b + 0x02b8#64) <| sepWP_seq_env hcl0 hro0
    (seg1_prologue_ok hb hbase s0 seedA outPtr seed (memRegion outPtr 2400)
      hseed hpc hrun hsp0 hx0 hx1 hcl0 hro0) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hpost1, hP1⟩
  refine SepWP.done hpc1 hrun1 ?_
  refine SafeSepWP.weaken_pre
    (SafeSepWP.bind (seg2_matrix_safe_ok hb hbase s0 s1 seedA outPtr seed (memRegion outPtr 2400)
        hpc1 hrun1 hcl1 hro1 hpost1)
      fun s2 P2 hex2 => SafeSepWP.ret_of_sepWP <|
        SepWP.mono (blk05_tail_from_seg2 hb hbase s0 s2 seedA outPtr seed hseed hex2)
          fun sf Pf _ _ hpost => by
            rw [sepPost_apply] at hpost
            exact ⟨fun hm => Satisfies.mono (sepConj_mono_left hpost.2) hm, hpost.1.1, hpost.1.2⟩)
    hP1

/-- `B05` (`generate_keypair_compressed`) partial-correctness contract with `NonSyscallPreserved`. -/
theorem blk05_generate_keypair_safe_ok :
    MlKemBlockSafeOk 5 (fun mpl => withNonSyscallPreserved (mlkemGenKeypairRawSpec mpl)) :=
  mlkemBlockSafeOk_withNonSyscallPreserved blk05_generate_keypair_raw_safe_ok (by decide)
    (h_pre := fun mpl ⟨_seedA, _seed, _outPtr⟩ _R _s0 h => by
      dsimp only [mlkemGenKeypairRawSpec] at h ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
      simp only [stripS_readReg64, stripS_sp, stripS_mem]
      exact ⟨⟨h.1.1, h.1.2.1, h.1.2.2.1, mlkemRoOk_stripExecOutside (mlkemKeep mpl) h.1.2.2.2⟩, h.2⟩)
    (h_post := fun _mpl ⟨_seedA, _seed, _outPtr⟩ _R _s0 _sf _ h => by
      dsimp only [mlkemGenKeypairRawSpec] at h ⊢
      simpa only [stripS_sp] using h)

/-- `B05` (`generate_keypair_compressed`) raw total-correctness (`MlKemBlockOk 5`) contract
    under `Shake128MatrixTerminates`. -/
theorem blk05_generate_keypair_raw_ok : MlKemBlockOk 5 mlkemGenKeypairTermRawSpec := by
  intro _
  refine mlkemCaller_ok blkPC05 blkPl05 rfl rfl fun b hb hbase => ?_
  apply subroutine_ok_of_sepWP_init
  rintro ⟨seedA, seed, outPtr⟩ R s0 hpc hrun hpre hsp0
  dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, mlkemGenKeypairTermRawSpec] at hpre ⊢
  rw [sepConj_comm _ ⌜mlkemMultiLib.CodeLoaded mlkemMpl s0.mem⌝, sepConj_assoc,
      satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hseed, hTerm, hro0⟩, hspat⟩ := hpre
  refine ⟨stackAt s0.sp 31216 ∗ (seedA ↦ₛ seed) ∗ memRegion outPtr 2400,
    Satisfies.mono (by sep_frame) hspat, ?_⟩
  refine sepWP_seq_env hcl0 hro0
    (seg1_prologue_ok hb hbase s0 seedA outPtr seed (memRegion outPtr 2400)
      hseed hpc hrun hsp0 hx0 hx1 hcl0 hro0) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hpost1, hP1⟩
  refine SepWP.weaken_pre hP1 <| SepWP.seq
    (seg2_matrix_ok hb hbase s0 s1 seedA outPtr seed (memRegion outPtr 2400)
      hTerm hpc1 hrun1 hcl1 hro1 hpost1) ?_
  rintro s2 P2 _ _ hex2
  refine SepWP.mono (blk05_tail_from_seg2 hb hbase s0 s2 seedA outPtr seed hseed hex2) ?_
  intro sf Pf _ _ hpost
  rw [sepPost_apply] at hpost
  exact ⟨fun hm => Satisfies.mono (sepConj_mono_left hpost.2) hm, hpost.1.1, hpost.1.2⟩

/-- `B05` (`generate_keypair_compressed`) total-correctness contract with `NonSyscallPreserved`. -/
theorem blk05_generate_keypair_ok :
    MlKemBlockOk 5 (fun mpl => withNonSyscallPreserved (mlkemGenKeypairTermRawSpec mpl)) :=
  mlkemBlockOk_withNonSyscallPreserved blk05_generate_keypair_raw_ok (by decide)
    (h_pre := fun mpl ⟨_seedA, _seed, _outPtr⟩ _R _s0 h => by
      dsimp only [mlkemGenKeypairTermRawSpec] at h ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
      simp only [stripS_readReg64, stripS_sp, stripS_mem]
      exact ⟨⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2.1,
        mlkemRoOk_stripExecOutside (mlkemKeep mpl) h.1.2.2.2.2⟩, h.2⟩)
    (h_post := fun _mpl ⟨_seedA, _seed, _outPtr⟩ _R _s0 _sf _ h => by
      dsimp only [mlkemGenKeypairTermRawSpec] at h ⊢
      simpa only [stripS_sp] using h)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Core05

