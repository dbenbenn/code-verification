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
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.PrologueAbsorb
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.TailPadXor
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.TailPermute
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.SqueezeEpilogue

/-!
# `B02`: `libcrux_sha3::generic_keccak::simd128::keccak2::<136, 6>`

Functional correctness proof for `mlkemBlk02` (`595` words, `1040`-byte total stack footprint:
`1024`-byte local frame plus `16`-byte callee stack for `B09`), the 2-way NEON `SHA3-256`
function for `in0.length = in1.length < 2 ^ 32`. It calls `B09` (`load_block::<136>`) and
`B28` (`memcpy`).

Main theorems:
- `blk02_keccak2_136_6_RO_raw_ok`: raw read-only contract (`keccak2_136_6_Spec`).
- `blk02_keccak2_136_6_ok`: read-only contract lifted with `withNonSyscallPreserved`.
- `blk02_keccak2_136_6_RW1_ok`: aliased single-buffer read-write specialization.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6

open Arm64 Arm64.Obj ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (
  mlkemData01Bytes
  mlkemMultiLib
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (
  Keccak2SlicesRO
  keccak2_136_6_RW1Spec
  keccak2_136_6_Spec
  withNonSyscallPreserved
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBlockOk
  mlkemCaller_ok
  mlkemMpl
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (
  SepWP.roDataAt_intro
  mlkemData01Bytes_length
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  keccakF1600
  sha3_256List
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
  keccak2_136_6_RW1_ok
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Defs (
  keccakXorRate17
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge (
  keccakAbsorbPrefix17
  keccakLastBlock
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.Base (
  SavedFrame02
  blkPC02
  blkPl02
  sepWP_seq_env
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.PrologueAbsorb (
  seg_entry_to_tail
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.TailPadXor (
  seg_tail_pad_xor
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.TailPermute (
  seg_tail_permute
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.SqueezeEpilogue (
  seg_squeeze_epilogue
)

/-- `B02` (`keccak2::<136, 6>`, 2-way `SHA3-256` for `in0.length = in1.length < 2 ^ 32`) raw
    read-only contract. -/
theorem blk02_keccak2_136_6_RO_raw_ok : MlKemBlockOk 2 keccak2_136_6_Spec := by
  intro _
  refine mlkemCaller_ok blkPC02 blkPl02 rfl rfl fun b hb hbase => ?_
  apply subroutine_ok_of_sepWP_init
  intro a R s0 hpc hrun hpre hsp0
  dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, keccak2_136_6_Spec] at hpre ⊢
  rw [sepConj_comm _ ⌜mlkemMultiLib.CodeLoaded mlkemMpl s0.mem⌝, sepConj_assoc,
      satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hlen, hin0, hro0⟩, hspat⟩ := hpre
  let sp := s0.sp - 1024#64
  let rcBase := mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29"
  let F_io : SepProp :=
    Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
      (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1)
  let F_out : SepProp := memRegion a.out0 32 ∗ memRegion a.out1 32
  refine ⟨Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
      (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗ stackAt s0.sp 1040 ∗ F_out, ?_, ?_⟩
  · exact Satisfies.mono (by dsimp only [F_out]; sep_frame) hspat
  · refine sepWP_seq_env hcl0 hro0
      (seg_entry_to_tail hb hbase a hin0 hlen F_out s0 hpc hrun hsp0 hx0 hx1 hx2 hcl0 hro0) ?_
    intro s1 P1 hpc1 _ hcl1 hro1 ⟨hregs1, hP1⟩
    have hwp2 := seg_tail_pad_xor hb hbase a hin0 hlen sp rcBase
      (stackAt sp 16 ∗ SavedFrame02 s0.sp s0 ∗ F_out) s1 hpc1 hregs1 hcl1 hro1
    refine (fun h h1 => SepWP.weaken_pre h1 h) (sepWP_seq_env hcl1 hro1 hwp2 ?_)
      (Entails.trans hP1 (by sep_frame))
    intro s2 P2 hpc2 _ _ hro2 ⟨⟨hregs2, hvregs2⟩, hP2⟩
    let xst0 := keccakXorRate17 (keccakAbsorbPrefix17 a.in0 (a.in0.length / 136))
      (keccakLastBlock 136 0x06#8 a.in0)
    let xst1 := keccakXorRate17 (keccakAbsorbPrefix17 a.in1 (a.in0.length / 136))
      (keccakLastBlock 136 0x06#8 a.in1)
    refine SepWP.weaken_pre hP2 ?_
    refine SepWP.roDataAt_intro hro2.keccakRc (by rw [mlkemData01Bytes_length]; decide) ?_
    have hwp3 := seg_tail_permute hb hbase s2 sp rcBase xst0 xst1
      (stackAt sp 16 ∗ memRegion (sp + 176#64) 400 ∗ memRegion (sp + 576#64) 288 ∗
        SavedFrame02 s0.sp s0 ∗ F_out ∗ F_io)
      hpc2 hregs2.hrun hregs2.hsp hregs2.hsp_align hregs2.hx8 hregs2.hx25 hvregs2
    refine (fun h h2 => SepWP.weaken_pre h2 h) (SepWP.seq hwp3 ?_)
      (by dsimp only [rcBase, xst0, xst1, F_io]; sep_frame)
    intro s3 P3 hpc3 hrun3 ⟨hpres3, halign3, hvregs3, hP3⟩
    have hxst1_eq : xst1 = keccakXorRate17 (keccakAbsorbPrefix17 a.in1 (a.in1.length / 136))
        (keccakLastBlock 136 0x06#8 a.in1) := by
      dsimp only [xst1]; rw [hlen]
    rw [hxst1_eq] at hvregs3 hP3
    have hwp4 := seg_squeeze_epilogue b hb hbase a.out0 a.out1 a.in0 a.in1
      ((rcBase ↦ᵣ mlkemData01Bytes) ∗ F_io) s0 s3 hsp0 hpc3 hrun3 halign3
      (hpres3.1.trans hregs2.hsp) (hpres3.2.1.trans hregs2.hx9)
      (hpres3.2.2.2.1.trans hregs2.hx20) (hpres3.2.2.1.trans hregs2.hx19) hvregs3
    refine (fun h h3 => SepWP.weaken_pre h3 h) (SepWP.mono hwp4 ?_)
      (Entails.trans hP3 (by dsimp only [sp, xst0, F_out]; sep_frame))
    intro sf Pf _ _ hpost4
    rw [sepPost_apply] at hpost4
    rcases hpost4 with ⟨⟨hsp_sf, hcs_sf⟩, hPf⟩
    refine ⟨fun hm => ?_, hsp_sf, hcs_sf⟩
    have hm1 := Satisfies.mono (sepConj_mono_left hPf) hm
    have hm2 : sf.mem ⊨ (rcBase ↦ᵣ mlkemData01Bytes) ∗
        ((Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
          (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗
          (a.out0 ↦ₛ sha3_256List a.in0) ∗ (a.out1 ↦ₛ sha3_256List a.in1) ∗
          stackAt s0.sp 1040) ∗ R) :=
      Satisfies.mono (by dsimp only [F_io]; sep_frame) hm1
    exact Satisfies.of_sep_right hm2

/-- `B02` (`keccak2::<136, 6>`) read-only contract lifted with `NonSyscallPreserved`. -/
theorem blk02_keccak2_136_6_ok :
    MlKemBlockOk 2 (fun mpl => withNonSyscallPreserved (keccak2_136_6_Spec mpl)) :=
  mlkemBlockOk_withNonSyscallPreserved blk02_keccak2_136_6_RO_raw_ok (by decide)
    (h_pre := fun mpl _a _R _s0 h => by
      dsimp only [keccak2_136_6_Spec] at h ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
      simp only [stripS_readReg64, stripS_sp, stripS_mem]
      exact ⟨⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2.1,
        mlkemRoOk_stripExecOutside (mlkemKeep mpl) h.1.2.2.2.2.2⟩, h.2⟩)
    (h_post := fun _mpl _a _R _s0 _sf _ h => by
      dsimp only [keccak2_136_6_Spec] at h ⊢
      simpa only [stripS_sp] using h)

/-- `B02` (`keccak2::<136, 6>`) aliased single-buffer RW specialization (`keccak2_136_6_RW1Spec`). -/
theorem blk02_keccak2_136_6_RW1_ok : MlKemBlockOk 2 keccak2_136_6_RW1Spec :=
  keccak2_136_6_RW1_ok blk02_keccak2_136_6_RO_raw_ok

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6
