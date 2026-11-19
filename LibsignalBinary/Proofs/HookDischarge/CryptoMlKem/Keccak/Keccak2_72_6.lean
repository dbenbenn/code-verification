/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLiftBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLift
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Defs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6.Prologue
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6.PadMemcpy
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6.PadAbsorb
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6.RoundHalf2
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6.Squeeze

/-!
# `B00`: `libcrux_sha3::generic_keccak::simd128::keccak2::<72, 6>`

Functional correctness proof for `mlkemBlk00` (`713` words, `720`-byte stack frame), the 2-way
NEON `SHA3-512` function for `in0.length = in1.length < 72`. It calls `B28` (`memcpy`).

Main theorems:
- `blk00_keccak2_72_6_RO_raw_ok`: raw read-only contract (`keccak2_72_6_Spec`).
- `blk00_keccak2_72_6_ok`: read-only contract lifted with `withNonSyscallPreserved`.
- `blk00_keccak2_72_6_RW1_ok`: aliased single-buffer read-write specialization.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6

open Arm64 Arm64.Obj ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (
  mlkemData01Bytes
  mlkemMultiLib
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (
  Keccak2SlicesRO
  keccak2_72_6_RW1Spec
  keccak2_72_6_Spec
  withNonSyscallPreserved
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBlockOk
  mlkemCaller_ok
  mlkemMpl
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (
  MlKemRoOk
  SepWP.roDataAt_intro
  mlkemData01Bytes_length
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  keccakF1600
  keccakZeroState
  sha3_512List
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLiftBase (
  mlkemBlockOk_withNonSyscallPreserved
  mlkemKeep
  mlkemRoOk_stripExecOutside
  stripS_mem
  stripS_readReg64
  stripS_sp
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLift (
  keccak2_72_6_RW1_ok
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Defs (
  keccakXorRate9
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge (
  keccakLastBlock
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6.Base (
  LoopSpillMem
  SavedFrame00
  blkPC00
  blkPl00
  sepWP_seq_env
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6.Prologue (
  prologue_to_05b4_ok
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6.PadMemcpy (
  memcpy_pad_ok
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6.PadAbsorb (
  pad1_absorb_ok
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6.RoundHalf2 (
  loop_24_ok
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6.Squeeze (
  squeeze_epilogue_ok
)

/-- `B00` (`keccak2::<72, 6>`, 2-way `SHA3-512` for `in0.length = in1.length < 72`) raw read-only
    contract. -/
theorem blk00_keccak2_72_6_RO_raw_ok : MlKemBlockOk 0 keccak2_72_6_Spec := by
  intro _
  refine mlkemCaller_ok blkPC00 blkPl00 rfl rfl fun b hb hbase => ?_
  apply subroutine_ok_of_sepWP_init
  intro a R s0 hpc hrun hpre hsp0
  dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, keccak2_72_6_Spec] at hpre ⊢
  rw [sepConj_comm _ ⌜mlkemMultiLib.CodeLoaded mlkemMpl s0.mem⌝, sepConj_assoc,
      satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hlen, hin0, hro0⟩, hspat⟩ := hpre
  have hin1 : a.in1.length < 72 := by clear * - hlen hin0; omega
  let sp := s0.sp - 720#64
  let rcBase := mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29"
  let F_io : SepProp :=
    Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
      (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1)
  let F_out : SepProp := memRegion a.out0 64 ∗ memRegion a.out1 64
  refine ⟨Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
      stackAt s0.sp 720 ∗ ((a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗ F_out),
    ?_, ?_⟩
  · exact Satisfies.mono (by dsimp only [F_out]; sep_frame) hspat
  · refine sepWP_seq_env hcl0 hro0
      (prologue_to_05b4_ok b hb hbase a hin0
        ((a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗ F_out)
        s0 hcl0 hro0 hpc hrun hsp0 hx0 hx1 hx2) ?_
    intro s1 P1 hpc1 _ hcl1 hro1 hpost1
    rw [sepPost_apply] at hpost1
    rcases hpost1 with ⟨hregs1, hP1⟩
    refine sepWP_seq_env hcl1 hro1
      (SepWP.weaken_pre (Entails.trans hP1 (by sep_frame))
        (memcpy_pad_ok b hb hbase a hlen hin0 sp rcBase s0 s1 F_out hcl1 hro1 hpc1 hregs1)) ?_
    intro s2 P2 hpc2 _ hcl2 hro2 hpost2
    rw [sepPost_apply] at hpost2
    rcases hpost2 with ⟨hregs2, hP2⟩
    refine sepWP_seq_env hcl2 hro2
      (SepWP.weaken_pre (Entails.trans hP2 (by dsimp only [F_io]; sep_frame))
        (pad1_absorb_ok b hb hbase sp rcBase a.out0 a.out1 a.in0 a.in1 hin0 hin1
          (SavedFrame00 s0.sp s0 ∗ F_io ∗ F_out) s2 hpc2 hregs2)) ?_
    intro s3 P3 hpc3 _ _ hro3 hpost3
    rw [sepPost_apply] at hpost3
    rcases hpost3 with ⟨hregs3, hP3⟩
    let st0 := keccakXorRate9 keccakZeroState (keccakLastBlock 72 0x06#8 a.in0)
    let st1 := keccakXorRate9 keccakZeroState (keccakLastBlock 72 0x06#8 a.in1)
    refine SepWP.weaken_pre hP3 ?_
    refine SepWP.roDataAt_intro hro3.keccakRc (by rw [mlkemData01Bytes_length]; decide) ?_
    refine SepWP.bind_sepPost
      (F := memRegion sp 176 ∗ memRegion (sp + 400#64) 160 ∗
        SavedFrame00 s0.sp s0 ∗ F_io ∗ F_out)
      (loop_24_ok b hb hbase sp rcBase a.out0 a.out1 st0 st1 s3 hpc3 hregs3)
      (by dsimp only [rcBase, st0, st1]; sep_frame) ?_
    intro s4 hpc4 _ hregs4
    let f0 := keccakF1600 st0
    let f1 := keccakF1600 st1
    have hframe4 :
        (LoopSpillMem sp f0 f1 ∗ (rcBase ↦ᵣ mlkemData01Bytes)) ∗
          (memRegion sp 176 ∗ memRegion (sp + 400#64) 160 ∗
            SavedFrame00 s0.sp s0 ∗ F_io ∗ F_out) ⊢
          memRegion sp 176 ∗ LoopSpillMem sp f0 f1 ∗ memRegion (sp + 400#64) 160 ∗
            SavedFrame00 s0.sp s0 ∗ memRegion a.out0 64 ∗ memRegion a.out1 64 ∗
            ((rcBase ↦ᵣ mlkemData01Bytes) ∗ F_io) := by
      dsimp only [F_out]; sep_frame
    refine SepWP.weaken_pre hframe4 ?_
    refine SepWP.mono
      (squeeze_epilogue_ok b hb hbase a.out0 a.out1 a.in0 a.in1 hin0 hin1 rcBase
        ((rcBase ↦ᵣ mlkemData01Bytes) ∗ F_io) s0 s4 hsp0 hpc4 hregs4) ?_
    intro sf Pf _ _ hpost5
    rw [sepPost_apply] at hpost5
    rcases hpost5 with ⟨⟨hsp_sf, hcs_sf⟩, hPf⟩
    refine ⟨fun hm => ?_, hsp_sf, hcs_sf⟩
    have hm1 := Satisfies.mono (sepConj_mono_left hPf) hm
    have hm2 : sf.mem ⊨ (rcBase ↦ᵣ mlkemData01Bytes) ∗
        ((Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
          (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗
          (a.out0 ↦ₛ sha3_512List a.in0) ∗ (a.out1 ↦ₛ sha3_512List a.in1) ∗
          stackAt s0.sp 720) ∗ R) :=
      Satisfies.mono (by dsimp only [F_io]; sep_frame) hm1
    exact Satisfies.of_sep_right hm2

/-- `B00` (`keccak2::<72, 6>`) read-only contract lifted with `NonSyscallPreserved`. -/
theorem blk00_keccak2_72_6_ok :
    MlKemBlockOk 0 (fun mpl => withNonSyscallPreserved (keccak2_72_6_Spec mpl)) :=
  mlkemBlockOk_withNonSyscallPreserved blk00_keccak2_72_6_RO_raw_ok (by decide)
    (h_pre := fun mpl _a _R _s0 h => by
      dsimp only [keccak2_72_6_Spec] at h ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
      simp only [stripS_readReg64, stripS_sp, stripS_mem]
      exact ⟨⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2.1,
        mlkemRoOk_stripExecOutside (mlkemKeep mpl) h.1.2.2.2.2.2⟩, h.2⟩)
    (h_post := fun _mpl _a _R _s0 _sf _ h => by
      dsimp only [keccak2_72_6_Spec] at h ⊢
      simpa only [stripS_sp] using h)

/-- `B00` (`keccak2::<72, 6>`) aliased single-buffer RW specialization (`keccak2_72_6_RW1Spec`). -/
theorem blk00_keccak2_72_6_RW1_ok : MlKemBlockOk 0 keccak2_72_6_RW1Spec :=
  keccak2_72_6_RW1_ok blk00_keccak2_72_6_RO_raw_ok

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6
