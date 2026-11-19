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
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31.Prologue
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31.AbsorbLoop
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31.TailPad
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31.SqueezeEpilogue

/-!
# `B01`: `libcrux_sha3::generic_keccak::simd128::keccak2::<136, 31>`

Functional correctness proof for `mlkemBlk01` (`601` words, `1136`-byte total stack footprint),
the 2-way NEON `SHAKE-256` function for `in0.length = in1.length < 2 ^ 32` and
`outLen ∈ {32, 128}`. It calls `B09` (`load_block::<136>`), `B28` (`memcpy`), and `B08`
(`squeeze2::<136>`).

Main theorems:
- `blk01_keccak2_136_31_RO_raw_ok`: raw read-only contract (`keccak2_136_31_Spec`).
- `blk01_keccak2_136_31_ok`: read-only contract lifted with `withNonSyscallPreserved`.
- `blk01_keccak2_136_31_RW2_ok`: distinct two-buffer read-write specialization.
- `blk01_keccak2_136_31_RW1_ok`: aliased single-buffer read-write specialization.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31

open Arm64 Arm64.Obj ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (
  mlkemData01Bytes
  mlkemMultiLib
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (
  Keccak2SlicesRO
  keccak2_136_31_RW1Spec
  keccak2_136_31_RW2Spec
  keccak2_136_31_Spec
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
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (shake256List)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLiftBase (
  mlkemBlockOk_withNonSyscallPreserved
  mlkemKeep
  mlkemRoOk_stripExecOutside
  stripS_mem
  stripS_readReg64
  stripS_sp
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLift (
  keccak2_136_31_RW1_ok
  keccak2_136_31_RW2_ok
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Defs (Keccak2Mem)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31.Base (
  SavedCalleeFrame
  Spill11
  blkPC01
  blkPl01
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31.Prologue (
  AbsorbInvMem
  sepWP_seq_cl
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31.AbsorbLoop (
  absorb_prefix_ok
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31.TailPad (tail_pad_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31.SqueezeEpilogue (
  squeeze_epilogue_ok
)

section
attribute [local irreducible] Keccak2Mem Keccak2SlicesRO SavedCalleeFrame Spill11

/-- `B01` (`keccak2::<136, 31>`, 2-way `SHAKE-256` for `in0.length = in1.length < 2 ^ 32` and
    `outLen ∈ {32, 128}`) raw read-only contract. -/
theorem blk01_keccak2_136_31_RO_raw_ok : MlKemBlockOk 1 keccak2_136_31_Spec := by
  intro _
  refine mlkemCaller_ok blkPC01 blkPl01 rfl rfl fun b hb hbase => ?_
  apply subroutine_ok_of_sepWP_init
  intro a R s0 hpc hrun hpre hsp0
  dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, keccak2_136_31_Spec] at hpre ⊢
  rw [sepConj_comm _ ⌜mlkemMultiLib.CodeLoaded mlkemMpl s0.mem⌝, sepConj_assoc,
      satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hx3, hx4, hlen, hin0, hout, hro0⟩, hspat⟩ := hpre
  let sp1 := s0.sp - 1040#64
  let rcBase := mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29"
  let F_io : SepProp :=
    Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
      (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1)
  let F_out : SepProp := memRegion a.out0 a.outLen ∗ memRegion a.out1 a.outLen
  refine ⟨F_io ∗ stackAt s0.sp 1136 ∗ F_out, ?_, ?_⟩
  · exact Satisfies.mono (by dsimp only [F_io, F_out]; sep_frame) hspat
  · refine SepWP.roDataAt_intro hro0.keccakRc (by rw [mlkemData01Bytes_length]; decide) ?_
    refine SepWP.weaken_pre
      (show _ ⊢ Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
          (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗ stackAt s0.sp 1136 ∗
          (rcBase ↦ᵣ mlkemData01Bytes) ∗ F_out by
        dsimp only [rcBase, F_io]; sep_frame) ?_
    refine sepWP_seq_cl hcl0
      (absorb_prefix_ok hb hbase a hlen hin0 s0 F_out hcl0 hpc hrun hsp0 hx0 hx1 hx2 hx3 hx4) ?_
    intro s1 Q1 hpc1 _ hcl1 ⟨hregs1, hQ1⟩
    unfold AbsorbInvMem at hQ1
    let F_tail : SepProp :=
      stackAt sp1 96 ∗ memRegion sp1 8 ∗ ((sp1 + 8#64) ↦₆₄ BitVec.ofNat 64 a.outLen) ∗
        SavedCalleeFrame s0.sp s0 ∗ (rcBase ↦ᵣ mlkemData01Bytes) ∗ F_out
    have hwp2 := tail_pad_ok hb hbase a hin0 hlen s0 rcBase F_tail s1 hpc1 hregs1 hcl1
    refine (fun h h1 => SepWP.weaken_pre h1 h) (sepWP_seq_cl hcl1 hwp2 ?_)
      (Entails.trans hQ1 (by dsimp only [sp1, F_tail]; sep_frame))
    intro s2 Q2 hpc2 _ hcl2 ⟨hregs2, hrr2, s16, s32, s48, s64, s80, s96, s112, hQ2⟩
    rcases hregs2 with ⟨hrun2, halign2, hsp2, hx8_2, hx20_2, hx21_2, hx22_2, hx27_2, _⟩
    have hwp3 := squeeze_epilogue_ok hb hbase a hlen hout s0 rcBase
      s16 s32 s48 s64 s80 s96 s112 F_io s2 hsp0 hcl2 hpc2
      hrun2 halign2 hsp2 hx8_2 hx20_2 hx21_2 hx22_2 hx27_2 hrr2
    refine (fun h h2 => SepWP.weaken_pre h2 h) (SepWP.mono hwp3 ?_)
      (Entails.trans hQ2 (by dsimp only [sp1, F_tail, F_out, F_io]; sep_frame))
    intro sf Qf _ _ hpost3
    rw [sepPost_apply] at hpost3
    rcases hpost3 with ⟨⟨hsp_sf, hcs_sf⟩, hQf⟩
    refine ⟨fun hm => ?_, hsp_sf, hcs_sf⟩
    have hm1 := Satisfies.mono (sepConj_mono_left hQf) hm
    have hm2 : sf.mem ⊨ (rcBase ↦ᵣ mlkemData01Bytes) ∗
        ((Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
          (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗
          (a.out0 ↦ₛ shake256List a.outLen a.in0) ∗
          (a.out1 ↦ₛ shake256List a.outLen a.in1) ∗
          stackAt s0.sp 1136) ∗ R) :=
      Satisfies.mono (by dsimp only [F_io]; sep_frame) hm1
    exact Satisfies.of_sep_right hm2

end

/-- `B01` (`keccak2::<136, 31>`) read-only contract lifted with `NonSyscallPreserved`. -/
theorem blk01_keccak2_136_31_ok :
    MlKemBlockOk 1 (fun mpl => withNonSyscallPreserved (keccak2_136_31_Spec mpl)) :=
  mlkemBlockOk_withNonSyscallPreserved blk01_keccak2_136_31_RO_raw_ok (by decide)
    (h_pre := fun mpl _a _R _s0 h => by
      dsimp only [keccak2_136_31_Spec] at h ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
      simp only [stripS_readReg64, stripS_sp, stripS_mem]
      exact ⟨⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2.1, h.1.2.2.2.2.2.1,
        h.1.2.2.2.2.2.2.1, h.1.2.2.2.2.2.2.2.1,
        mlkemRoOk_stripExecOutside (mlkemKeep mpl) h.1.2.2.2.2.2.2.2.2⟩, h.2⟩)
    (h_post := fun _mpl _a _R _s0 _sf _ h => by
      dsimp only [keccak2_136_31_Spec] at h ⊢
      simpa only [stripS_sp] using h)

/-- `B01` (`keccak2::<136, 31>`) distinct two-buffer RW specialization (`keccak2_136_31_RW2Spec`). -/
theorem blk01_keccak2_136_31_RW2_ok : MlKemBlockOk 1 keccak2_136_31_RW2Spec :=
  keccak2_136_31_RW2_ok blk01_keccak2_136_31_RO_raw_ok

/-- `B01` (`keccak2::<136, 31>`) aliased single-buffer RW specialization (`keccak2_136_31_RW1Spec`). -/
theorem blk01_keccak2_136_31_RW1_ok : MlKemBlockOk 1 keccak2_136_31_RW1Spec :=
  keccak2_136_31_RW1_ok blk01_keccak2_136_31_RO_raw_ok

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31
