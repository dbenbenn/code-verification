/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeMlKemAvoidNonSntt -- proof-setup: allow-public-import
import ProofLib.ProgramReflection
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps

/-!
# `snttStrictAvoid` Rows `B24 → B07`, `B23 → B06`, and `B22 → B04` (`ElfSampleNttStuckDivergeMlKemAvoidTail`)

Discharges the `H2KSnttExtraFacts.snttStrictAvoid` obligations for the three tail-jumping
`SampleNTT` entrypoint wrappers:
- `B24 → B07` (`lsKemEncapsSym`, `kemEncapsGhostAt c2MlkemMpl stk`, `4` wrapper steps + `B07` active core)
- `B23 → B06` (`lsKemDecapsSym`, `kemDecapsGhostAt c2MlkemMpl stk`, `4` wrapper steps + `B06` active core)
- `B22 → B04` (`lsMlkemDecapsSym`, `mlkemDecapsGhostAt c2MlkemMpl stk`, `5` wrapper steps + `B04` active core)

Each proof steps the pure register-shuffle ABI wrapper (`B24`/`B23`/`B22`) in `4`/`4`/`5`
explicit `emptyStdProg` steps (avoiding `MlKemSampleNttStuckAt` at offset `0` via `hTerm` and at
offsets `+4..+16` via `not_mlKemSampleNttStuckAt_of_s5_offset`), runs the active core block
(`B07`/`B06`/`B04` ∈ `mlkemActiveBlocks`) via `mlkemActive_run_visitedIn` (avoiding all 5
`SampleNTT` entrypoints via `not_mlKemSampleNttStuckAt_of_activeKeep`), pins `f u = sf` via
`mlkemBlockGhost_eq_of_visitedIn`, and chains the wrapper + core `StepsStrictAvoid` traces.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeMlKemAvoidTail

open Arm64 Arm64.Obj ProofLib SepProp
open scoped ProofLib.ProgramReflection
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalSpqrV1 (MlkemDecapsCall)
open CryptoVerification.SignalSession (
  CliHooks MlKemSampleNttStuckAt cliElfBytes cliExternsPlaced libsignalSessionLib
  lsKemDecapsSym lsKemEncapsSym lsMlkemDecapsSym)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (withNonSyscallPreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.ConsumerBridgesBase (
  kemDecapsAtSpec kemEncapsPreservedAtSpec mlkemDecapsAtSpec withMlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps (blk04_decaps_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base (
  blkPC22 blkPl22 mlkemBlk04RawSpec mlkemBlk04TermCoreSpec mlkemBlk04TermRawSpec toByteVec_of_vector)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps (
  blk06_decaps_ok kyberDecapsInnerTermCoreSpec kyberDecapsInnerTermRawSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base (
  blkPC23 blkPl23 kyberDecapsInnerRawSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps (
  blk07EncapsTermCoreSpec blk07_encaps_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base (
  blk07EncapsRawSpec blk07EncapsTermRawSpec blkPC24 blkPl24)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Kyber1024DecapsTerminates Kyber1024EncapsTerminates Mlkem768DecapsTerminates
  kyber1024Decaps kyber1024Encaps mlkem768DecapsWith mlkem768Incremental sampleNtt toByteVec)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs withStack)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (SpecSimulates)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (ExecFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKem (
  c2_mlkem_invMem_of_f3CodeInv)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemPlaceable (
  c2MlkemKeep c2MlkemMpl c2_mlkemKeep_noPanic c2_mlkemKeep_sub_rxProg c2_mlkem_placeable
  c2_resolve_kyber1024Decaps_eq c2_resolve_kyber1024Encaps_eq c2_resolve_mlkem768Decaps_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemSampleNttHelpers (
  kemDecapsStateTerminates_iff_of_atSpec_pre kemEncapsStateTerminates_iff_of_preservedAtSpec_pre
  mlkemDecapsStateTerminates_iff_of_atSpec_pre)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookG (
  linkedCallHookG_activeRealPre_of_noException)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK (
  emptyStdProg emptyStdProg_externAt_none)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemFirstStopTransfer (
  mlkemSampleNttSyms mlkemSampleNttTermOf mlkemSampleNttTermOf_kemDecaps
  mlkemSampleNttTermOf_kemEncaps mlkemSampleNttTermOf_mlkemDecaps)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemHooksDehook (
  kemDecapsGhostAt kemEncapsGhostAt mlkemBlockGhost_preserves_execFrozen mlkemDecapsGhostAt
  mlkemInvMem)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (extract_withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoMlKemRowSpecs (
  kemDecapsFallback_preserved kemDecapsTightStack
  kemEncapsFallback_preserved kemEncapsTightStack kyber1024Prims₀
  mlkemDecapsFallback_preserved mlkemDecapsTightStack)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts (
  C2ExternTableFacts f3RxSeg_realProg617_externAt_none)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeInv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeCore (
  StepsStrictAvoid)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeMlKemAvoidNonSntt (
  bddP_bytes bddP_mem bddP_pure bddP_sep bddP_stk bddP_to6 evalInst_eq_of_svc_eq
  mlkemBlockGhost_eq_of_visitedIn not_mlKemSampleNttStuckAt_of_activeKeep
  not_mlKemSampleNttStuckAt_of_entry_term not_mlKemSampleNttStuckAt_of_s5_offset
  rwP_bytes rwP_mem rwP_pure rwP_sep rwP_stk
  step_emptyStdProg_of_mlkem_block_fetch stepsStrictAvoid_realProg617_of_visitedIn
  visitedIn_mono_keep)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeMlKemLocality (
  c2_mlkemActiveInvMem_of_codeLoaded_roOk mlkemActiveKeep_sub_c2MlkemKeep
  mlkemActive_run_visitedIn)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric (
  h2fsgen_StepsVisitedIn)

local instance c2MlKemPlacementInst : MlKemPlacement := ⟨c2MlkemMpl, c2_mlkem_placeable⟩

/-! ## 1. Wrapper Step Combinators (`emptyStdProg` → `realProg617` + `Returned`/`NonSyscallPreserved` Shift) -/

private theorem step_realProg617_of_emptyStdProg {mpl mmpl : MultiPlacement}
    (hExt : C2ExternTableFacts mpl) (W : CliHooks) {z1 z2 : State}
    (hk : c2MlkemKeep c2MlkemMpl z1.pc = true)
    (h1 : Step emptyStdProg z1 z2) :
    Step (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) z1 z2 := by
  let P_real := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W
  have hsvc : emptyStdProg.svc = P_real.svc := rfl
  have he1 : emptyStdProg.externAt? z1.pc = none := emptyStdProg_externAt_none z1.pc
  have he2 : P_real.externAt? z1.pc = none :=
    f3RxSeg_realProg617_externAt_none hExt W (c2_mlkemKeep_sub_rxProg hk)
      (c2_mlkemKeep_noPanic hk)
  have hfm : P_real.fetchMem z1.mem z1.pc = emptyStdProg.fetchMem z1.mem z1.pc := by
    unfold Program.fetchMem; rw [he1, he2]
  cases h1 with
  | @exec inst hr hfm1 =>
    rw [evalInst_eq_of_svc_eq hsvc inst z1]
    exact Step.exec hr (hfm.trans hfm1)
  | halt_unmapped hr hfm1 _ => exact Step.halt_unmapped hr (hfm.trans hfm1) he2
  | extern _ he _ _ => rw [he1] at he; cases he
  | extern_fault _ he _ => rw [he1] at he; cases he

private theorem returned_of_wrapper {u sc sf : State}
    (hlr : sc.readReg64 .lr = u.readReg64 .lr)
    (hsp : sc.sp = u.sp)
    (hr : Returned sc sf) : Returned u sf :=
  ⟨hr.1.trans hlr, hr.2.1.trans hsp, hr.2.2⟩

private theorem nonSyscallPreserved_trans {s0 s1 s2 : State}
    (h01 : ProofLib.NonSyscallPreserved s0 s1)
    (h12 : ProofLib.NonSyscallPreserved s1 s2) :
    ProofLib.NonSyscallPreserved s0 s2 :=
  ⟨h12.1.trans h01.1,
   h12.2.1.trans h01.2.1,
   h12.2.2.1.trans h01.2.2.1,
   h12.2.2.2.1.trans h01.2.2.2.1,
   h12.2.2.2.2.1.trans h01.2.2.2.2.1,
   ⟨h12.2.2.2.2.2.1.1.trans h01.2.2.2.2.2.1.1,
    fun a ha => h12.2.2.2.2.2.1.2 a (h01.2.2.2.2.2.1.2 a ha)⟩,
   h12.2.2.2.2.2.2.trans h01.2.2.2.2.2.2⟩

private theorem with_mlkem_wrapper_step {j : Nat}
    (hj : j < mlkemMultiLib.blocks.length) {P : Program}
    (hP : P = mlkemMultiLib.blockProgram c2MlkemMpl j)
    {s : State} {pc : BitVec 64} {R : Prop}
    (hcl : (mlkemMultiLib.blockProgram c2MlkemMpl j).CodeLoaded s.mem)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (h : ∃ inst, P.fetch pc = some inst ∧ inst.isSvc0 = false ∧
      (∀ s', s' = execInst inst s →
        c2MlkemKeep c2MlkemMpl s.pc = true → Step emptyStdProg s s' → R)) :
    R := by
  rcases h with ⟨inst, hf, hsvc, hkR⟩
  have hf' : (mlkemMultiLib.blockProgram c2MlkemMpl j).fetch s.pc = some inst := by
    rwa [← hP, hpc]
  obtain ⟨hk, hst⟩ := step_emptyStdProg_of_mlkem_block_fetch hj hcl hf' hsvc hrun
  exact hkR (execInst inst s) rfl hk hst

/-! ## 2. Row `B24 → B07`: `lsKemEncapsSym` (`kemEncapsGhostAt c2MlkemMpl stk`) -/

private noncomputable def blk07FixedMaster (ret pkA : BitVec 64)
    (pk : List.Vector (BitVec 8) 1568) (rA : BitVec 64) (rnd : List.Vector (BitVec 8) 32) :
    Spec Unit where
  pre := fun _ s =>
    ⌜s.readReg64 .x0 = ret ∧ s.readReg64 .x1 = pkA ∧ s.readReg64 .x2 = rA ∧
      Kyber1024EncapsTerminates pk.toList⌝ ∗
      (pkA ↦ₛ pk.toList) ∗ (rA ↦ₛ rnd.toList) ∗ memRegion ret 1600 ∗ stackAt s.sp 34240
  post := fun _ s0 _ =>
    let (ct, ss) := kyber1024Encaps pk.toList rnd.toList
    (pkA ↦ₛ pk.toList) ∗ (rA ↦ₛ rnd.toList) ∗
      (ret ↦ₛ ct) ∗ ((ret + 1568#64) ↦ₛ ss) ∗ stackAt s0.sp 34240
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem blk07_simulates_fixed (ret pkA : BitVec 64)
    (pk : List.Vector (BitVec 8) 1568) (rA : BitVec 64) (rnd : List.Vector (BitVec 8) 32)
    (mpl : MultiPlacement) :
    SpecSimulates (blk07EncapsTermCoreSpec mpl)
      (withMlKemRoOk mpl (blk07FixedMaster ret pkA pk rA rnd)) := by
  refine SpecSimulates.of_map ?_
  intro _ R s0 hm
  dsimp only [withMlKemRoOk, blk07FixedMaster] at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hro, hm⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hx0, hx1, hx2, hTerm⟩, hm⟩
  refine ⟨(ret, pkA, pk.toList, rA, rnd.toList), R, ?_, ?_⟩
  · dsimp only [blk07EncapsTermCoreSpec, withNonSyscallPreserved, blk07EncapsTermRawSpec]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, pk.toList_length, rnd.toList_length, hTerm, hro⟩,
      Satisfies.mono (by sep_frame) hm⟩
  · intro sf _ _ hpost
    dsimp only [blk07EncapsTermCoreSpec, withNonSyscallPreserved,
      blk07EncapsTermRawSpec, blk07EncapsRawSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    dsimp only [withMlKemRoOk, blk07FixedMaster]
    exact Satisfies.mono (by sep_frame) hpost.2

private theorem blk24_wrapper_steps {s0 : State}
    (hcl24 : (mlkemMultiLib.blockProgram c2MlkemMpl 24).CodeLoaded s0.mem)
    (hpc : s0.pc = c2MlkemMpl.base 24) (hrun : s0.status = .Running) :
    ∃ s1 s2 s3 s4 : State,
      c2MlkemKeep c2MlkemMpl s0.pc = true ∧ Step emptyStdProg s0 s1 ∧
      s1.pc = c2MlkemMpl.base 24 + BitVec.ofNat 64 4 ∧ s1.status = .Running ∧
      c2MlkemKeep c2MlkemMpl s1.pc = true ∧ Step emptyStdProg s1 s2 ∧
      s2.pc = c2MlkemMpl.base 24 + BitVec.ofNat 64 8 ∧ s2.status = .Running ∧
      c2MlkemKeep c2MlkemMpl s2.pc = true ∧ Step emptyStdProg s2 s3 ∧
      s3.pc = c2MlkemMpl.base 24 + BitVec.ofNat 64 12 ∧ s3.status = .Running ∧
      c2MlkemKeep c2MlkemMpl s3.pc = true ∧ Step emptyStdProg s3 s4 ∧
      s4.pc = c2MlkemMpl.base 7 ∧ s4.status = .Running ∧
      s4.mem = s0.mem ∧ s4.sp = s0.sp ∧ s4.spAligned = s0.spAligned ∧
      ProofLib.NonSyscallPreserved s0 s4 ∧
      s4.readReg64 .lr = s0.readReg64 .lr ∧
      s4.readReg64 .x0 = s0.readReg64 .x8 ∧
      s4.readReg64 .x1 = s0.readReg64 .x0 ∧
      s4.readReg64 .x2 = s0.readReg64 .x1 := by
  have hb : c2MlkemMpl.base 24 = blkPl24.base := rfl
  let P24 := blkPC24.rebase (c2MlkemMpl.base 24) (fun _ => none)
  apply with_mlkem_wrapper_step (j := 24) (by decide) (P := P24) rfl hcl24 hpc hrun
  conv in (P24.fetch _) => simp only [P24, hb, wp_norm, arm64_norm]
  refine ⟨_, rfl, by decide, fun s1 hs1 hk0 hst0 => ?_⟩
  have hpc1 : s1.pc = c2MlkemMpl.base 24 + 4#64 := by simp [hs1, hpc, wp_norm, arm64_norm]
  have hrun1 : s1.status = .Running := by simp [hs1, hrun, wp_norm, arm64_norm]
  have hmem1 : s1.mem = s0.mem := by simp [hs1, wp_norm, arm64_norm]
  apply with_mlkem_wrapper_step (j := 24) (by decide) (P := P24) rfl (hmem1 ▸ hcl24) hpc1 hrun1
  conv in (P24.fetch _) => simp only [P24, hb, wp_norm, arm64_norm]
  refine ⟨_, rfl, by decide, fun s2 hs2 hk1 hst1 => ?_⟩
  have hpc2 : s2.pc = c2MlkemMpl.base 24 + 8#64 := by simp [hs2, hpc1, wp_norm, arm64_norm]
  have hrun2 : s2.status = .Running := by simp [hs2, hrun1, wp_norm, arm64_norm]
  have hmem2 : s2.mem = s0.mem := by simp [hs2, hmem1, wp_norm, arm64_norm]
  apply with_mlkem_wrapper_step (j := 24) (by decide) (P := P24) rfl (hmem2 ▸ hcl24) hpc2 hrun2
  conv in (P24.fetch _) => simp only [P24, hb, wp_norm, arm64_norm]
  refine ⟨_, rfl, by decide, fun s3 hs3 hk2 hst2 => ?_⟩
  have hpc3 : s3.pc = c2MlkemMpl.base 24 + 12#64 := by simp [hs3, hpc2, wp_norm, arm64_norm]
  have hrun3 : s3.status = .Running := by simp [hs3, hrun2, wp_norm, arm64_norm]
  have hmem3 : s3.mem = s0.mem := by simp [hs3, hmem2, wp_norm, arm64_norm]
  apply with_mlkem_wrapper_step (j := 24) (by decide) (P := P24) rfl (hmem3 ▸ hcl24) hpc3 hrun3
  conv in (P24.fetch _) => simp only [P24, hb, wp_norm, arm64_norm]
  refine ⟨_, rfl, by decide, fun s4 hs4 hk3 hst3 => ?_⟩
  refine ⟨s1, s2, s3, s4, hk0, hst0, hpc1, hrun1, hk1, hst1, hpc2, hrun2,
    hk2, hst2, hpc3, hrun3, hk3, hst3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hs4, hpc3, wp_norm, arm64_norm]
    rfl_kernel
  · simp [hs4, hrun3, wp_norm, arm64_norm]
  · simp [hs4, hmem3, wp_norm, arm64_norm]
  · simp [hs4, hs3, hs2, hs1, wp_norm, arm64_norm]
  · simp [hs4, hs3, hs2, hs1, State.spAligned, wp_norm, arm64_norm]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?_, fun _ h => ?_⟩, ?_⟩
    · simp [hs4, hs3, hs2, hs1, wp_norm, arm64_norm]
    · simp [hs4, hmem3, wp_norm, arm64_norm]
    · simp [hs4, hs3, hs2, hs1, wp_norm, arm64_norm]
    · simp [hs4, hs3, hs2, hs1, wp_norm, arm64_norm]
    · simp [hs4, hs3, hs2, hs1, wp_norm, arm64_norm]
    · simp [hs4, hs3, hs2, hs1, wp_norm, arm64_norm]
    · simpa [hs4, hmem3, wp_norm, arm64_norm] using h
    · simp [hs4, hs3, hs2, hs1, wp_norm, arm64_norm]
  · simp [hs4, hs3, hs2, hs1, wp_norm, arm64_norm]
  · simp [hs4, hs3, hs2, hs1, wp_norm, arm64_norm]
  · simp [hs4, hs3, hs2, hs1, wp_norm, arm64_norm]
  · simp [hs4, hs3, hs2, hs1, wp_norm, arm64_norm]

/-- `snttStrictAvoid` + `ExecFrozen` for `B24 → B07` (`lsKemEncapsSym`, `kemEncapsGhostAt`). -/
theorem c2_kemEncaps_snttStrictAvoid [LibsignalPlacement]
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hLs_ls : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hExt : C2ExternTableFacts mpl)
    {stk : Nat} (hstk : kemEncapsTightStack ≤ stk) (hfit : stk ≤ 2 ^ 64)
    (W : CliHooks) {u : State}
    (hTerm : mlkemSampleNttTermOf lsKemEncapsSym u)
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsKemEncapsSym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (kemEncapsGhostAt c2MlkemMpl stk u).status ≠ .Exception msg)
    (hfr : ExecFrozen u.mem)
    (hInv : F3CodeInv mpl mmpl u.mem) :
    StepsStrictAvoid (fun z => z.status = .Running ∧ MlKemSampleNttStuckAt mpl z)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      u (kemEncapsGhostAt c2MlkemMpl stk u) ∧
      ExecFrozen (kemEncapsGhostAt c2MlkemMpl stk u).mem := by
  have hfr_out : ExecFrozen (kemEncapsGhostAt c2MlkemMpl stk u).mem :=
    mlkemBlockGhost_preserves_execFrozen c2MlkemMpl 24
      (keepsFs (kemEncapsPreservedAtSpec stk kyber1024Prims₀)) kemEncapsFallback_preserved hfr
  refine ⟨?_, hfr_out⟩
  have hInvM : mlkemInvMem c2MlkemMpl u.mem := c2_mlkem_invMem_of_f3CodeInv hLs hInv
  have hInvA := c2_mlkemActiveInvMem_of_codeLoaded_roOk hInvM.2.1 hInvM.2.2
  have hpc24 : u.pc = c2MlkemMpl.base 24 := hpc.trans (c2_resolve_kyber1024Encaps_eq hLs)
  obtain ⟨_, hsp, ⟨pkA, pk, rA, rnd, ret⟩, R, hpre_ls⟩ :=
    linkedCallHookG_activeRealPre_of_noException hnoex
  have hpre_at : u.mem ⊨ (kemEncapsPreservedAtSpec stk kyber1024Prims₀).pre
      (pkA, pk, rA, rnd, ret) u ∗ R := by
    simpa only [keepsFs] using (extract_withLsRet hpre_ls).2
  have hTermS : Kyber1024EncapsTerminates pk.toList := by
    have hTerm' := hTerm
    rw [mlkemSampleNttTermOf_kemEncaps u] at hTerm'
    exact (kemEncapsStateTerminates_iff_of_preservedAtSpec_pre hpre_at).mp hTerm'
  obtain ⟨s1, s2, s3, s4, hk0, hst0, hpc1, hrun1, hk1, hst1, hpc2, hrun2,
      hk2, hst2, hpc3, hrun3, hk3, hst3, hpc4, hrun4, hmem4, hsp4, hspA4, hnsp_w4,
      hlr4, hx0_4, hx1_4, hx2_4⟩ :=
    blk24_wrapper_steps (hInvM.2.1 24 (by decide)) hpc24 hrun
  dsimp only [kemEncapsPreservedAtSpec, withStack] at hpre_at
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre_at
  obtain ⟨⟨hx0_u, hx1_u, hx8_u⟩, hspat⟩ := hpre_at
  rw [stackAt_shrink u.sp stk 34240 hstk hfit] at hspat
  let slack := memRegion (u.sp - BitVec.ofNat 64 stk) (stk - 34240)
  let M7 := blk07FixedMaster ret pkA pk rA rnd
  have hpre4 : s4.mem ⊨ M7.pre () s4 ∗ (slack ∗ R) := by
    dsimp only [M7, blk07FixedMaster, slack]
    rw [hmem4, hsp4, hx0_4, hx1_4, hx2_4, hx8_u, hx0_u, hx1_u,
      sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨rfl, rfl, rfl, hTermS⟩, Satisfies.mono (by sep_frame) hspat⟩
  obtain ⟨sf, hvis_act, hret4, _, _, _, hnsp4, _, _⟩ :=
    mlkemActive_run_visitedIn (j := 7) (by decide) c2MlkemMpl blk07_encaps_ok
      (blk07_simulates_fixed ret pkA pk rA rnd) rfl rfl rfl
      (by intro _ s _; cases s; rfl) (by intro _ s0 sf _ _; cases s0; cases sf; rfl)
      (fun _ _ => rwP_sep rwP_pure (rwP_sep (rwP_bytes _ _)
        (rwP_sep (rwP_bytes _ _) (rwP_sep (rwP_mem _ _) (rwP_stk _ _)))))
      (fun _ _ => bddP_to6 (by decide) (bddP_sep bddP_pure
        (bddP_sep (bddP_bytes _ _ (by rw [pk.toList_length]; decide))
          (bddP_sep (bddP_bytes _ _ (by rw [rnd.toList_length]; decide))
            (bddP_sep (bddP_mem _ _ (by decide)) (bddP_stk _ _ (by decide)))))))
      (fun _ _ _ => rwP_sep (rwP_bytes _ _)
        (rwP_sep (rwP_bytes _ _) (rwP_sep (rwP_bytes _ _)
          (rwP_sep (rwP_bytes _ _) (rwP_stk _ _)))))
      hpc4 hrun4 (hspA4.trans hsp) (hmem4 ▸ hInvA) hpre4
  have hvis_tot : h2fsgen_StepsVisitedIn (c2MlkemKeep c2MlkemMpl) emptyStdProg u sf :=
    .step hk0 hst0 (.step hk1 hst1 (.step hk2 hst2 (.step hk3 hst3
      (visitedIn_mono_keep (fun _ hk => mlkemActiveKeep_sub_c2MlkemKeep hk) hvis_act))))
  have hghost_eq : kemEncapsGhostAt c2MlkemMpl stk u = sf :=
    mlkemBlockGhost_eq_of_visitedIn hLs_ls (by decide) hInvM hfr hnoex hpc24 hvis_tot
      (returned_of_wrapper hlr4 hsp4 hret4)
      (nonSyscallPreserved_trans hnsp_w4 hnsp4)
  rw [hghost_eq]
  have hcore_av := stepsStrictAvoid_realProg617_of_visitedIn (mmpl := mmpl)
    (bad := fun z => z.status = .Running ∧ MlKemSampleNttStuckAt mpl z)
    (fun _ hk => mlkemActiveKeep_sub_c2MlkemKeep hk) hExt W
    (fun _ _ hk ⟨_, hst⟩ => not_mlKemSampleNttStuckAt_of_activeKeep hLs hk hst) hvis_act
  exact .step
    (fun ⟨_, hst⟩ => not_mlKemSampleNttStuckAt_of_entry_term hLs (by simp [mlkemSampleNttSyms]) hpc hTerm hst)
    (step_realProg617_of_emptyStdProg hExt W hk0 hst0)
    (.step
      (fun ⟨_, hst⟩ => not_mlKemSampleNttStuckAt_of_s5_offset hLs (j := 24) (off := 4) (by decide) (by decide) (by decide) hpc1 hst)
      (step_realProg617_of_emptyStdProg hExt W hk1 hst1)
      (.step
        (fun ⟨_, hst⟩ => not_mlKemSampleNttStuckAt_of_s5_offset hLs (j := 24) (off := 8) (by decide) (by decide) (by decide) hpc2 hst)
        (step_realProg617_of_emptyStdProg hExt W hk2 hst2)
        (.step
          (fun ⟨_, hst⟩ => not_mlKemSampleNttStuckAt_of_s5_offset hLs (j := 24) (off := 12) (by decide) (by decide) (by decide) hpc3 hst)
          (step_realProg617_of_emptyStdProg hExt W hk3 hst3)
          hcore_av)))

/-! ## 3. Row `B23 → B06`: `lsKemDecapsSym` (`kemDecapsGhostAt c2MlkemMpl stk`) -/

private noncomputable def blk06FixedMaster (ret skA : BitVec 64)
    (sk : List.Vector (BitVec 8) 3168) (ctA : BitVec 64) (ct : List.Vector (BitVec 8) 1568) :
    Spec Unit where
  pre := fun _ s =>
    ⌜s.readReg64 .x0 = ret ∧ s.readReg64 .x1 = skA ∧ s.readReg64 .x2 = ctA ∧
      Kyber1024DecapsTerminates sk.toList⌝ ∗
      (skA ↦ₛ sk.toList) ∗ (ctA ↦ₛ ct.toList) ∗ memRegion ret 32 ∗ stackAt s.sp 35968
  post := fun _ s0 _ =>
    (skA ↦ₛ sk.toList) ∗ (ctA ↦ₛ ct.toList) ∗
      (ret ↦ₛ kyber1024Decaps sk.toList ct.toList) ∗ stackAt s0.sp 35968
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem blk06_simulates_fixed (ret skA : BitVec 64)
    (sk : List.Vector (BitVec 8) 3168) (ctA : BitVec 64) (ct : List.Vector (BitVec 8) 1568)
    (mpl : MultiPlacement) :
    SpecSimulates (kyberDecapsInnerTermCoreSpec mpl)
      (withMlKemRoOk mpl (blk06FixedMaster ret skA sk ctA ct)) := by
  refine SpecSimulates.of_map ?_
  intro _ R s0 hm
  dsimp only [withMlKemRoOk, blk06FixedMaster] at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hro, hm⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hx0, hx1, hx2, hTerm⟩, hm⟩
  refine ⟨(ret, skA, sk.toList, ctA, ct.toList), R, ?_, ?_⟩
  · dsimp only [kyberDecapsInnerTermCoreSpec, withNonSyscallPreserved,
      kyberDecapsInnerTermRawSpec, kyberDecapsInnerRawSpec]
    rw [sepConj_assoc, pure_sepConj_of_true hTerm,
      sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, sk.toList_length, ct.toList_length, hro⟩,
      Satisfies.mono (by sep_frame) hm⟩
  · intro sf _ _ hpost
    dsimp only [kyberDecapsInnerTermCoreSpec, withNonSyscallPreserved,
      kyberDecapsInnerTermRawSpec, kyberDecapsInnerRawSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    dsimp only [withMlKemRoOk, blk06FixedMaster]
    exact Satisfies.mono (by sep_frame) hpost.2

private theorem blk23_wrapper_steps {s0 : State}
    (hcl23 : (mlkemMultiLib.blockProgram c2MlkemMpl 23).CodeLoaded s0.mem)
    (hpc : s0.pc = c2MlkemMpl.base 23) (hrun : s0.status = .Running) :
    ∃ s1 s2 s3 s4 : State,
      c2MlkemKeep c2MlkemMpl s0.pc = true ∧ Step emptyStdProg s0 s1 ∧
      s1.pc = c2MlkemMpl.base 23 + BitVec.ofNat 64 4 ∧ s1.status = .Running ∧
      c2MlkemKeep c2MlkemMpl s1.pc = true ∧ Step emptyStdProg s1 s2 ∧
      s2.pc = c2MlkemMpl.base 23 + BitVec.ofNat 64 8 ∧ s2.status = .Running ∧
      c2MlkemKeep c2MlkemMpl s2.pc = true ∧ Step emptyStdProg s2 s3 ∧
      s3.pc = c2MlkemMpl.base 23 + BitVec.ofNat 64 12 ∧ s3.status = .Running ∧
      c2MlkemKeep c2MlkemMpl s3.pc = true ∧ Step emptyStdProg s3 s4 ∧
      s4.pc = c2MlkemMpl.base 6 ∧ s4.status = .Running ∧
      s4.mem = s0.mem ∧ s4.sp = s0.sp ∧ s4.spAligned = s0.spAligned ∧
      ProofLib.NonSyscallPreserved s0 s4 ∧
      s4.readReg64 .lr = s0.readReg64 .lr ∧
      s4.readReg64 .x0 = s0.readReg64 .x8 ∧
      s4.readReg64 .x1 = s0.readReg64 .x0 ∧
      s4.readReg64 .x2 = s0.readReg64 .x1 := by
  have hb : c2MlkemMpl.base 23 = blkPl23.base := rfl
  let P23 := blkPC23.rebase (c2MlkemMpl.base 23) (fun _ => none)
  apply with_mlkem_wrapper_step (j := 23) (by decide) (P := P23) rfl hcl23 hpc hrun
  conv in (P23.fetch _) => simp only [P23, hb, wp_norm, arm64_norm]
  refine ⟨_, rfl, by decide, fun s1 hs1 hk0 hst0 => ?_⟩
  have hpc1 : s1.pc = c2MlkemMpl.base 23 + 4#64 := by simp [hs1, hpc, wp_norm, arm64_norm]
  have hrun1 : s1.status = .Running := by simp [hs1, hrun, wp_norm, arm64_norm]
  have hmem1 : s1.mem = s0.mem := by simp [hs1, wp_norm, arm64_norm]
  apply with_mlkem_wrapper_step (j := 23) (by decide) (P := P23) rfl (hmem1 ▸ hcl23) hpc1 hrun1
  conv in (P23.fetch _) => simp only [P23, hb, wp_norm, arm64_norm]
  refine ⟨_, rfl, by decide, fun s2 hs2 hk1 hst1 => ?_⟩
  have hpc2 : s2.pc = c2MlkemMpl.base 23 + 8#64 := by simp [hs2, hpc1, wp_norm, arm64_norm]
  have hrun2 : s2.status = .Running := by simp [hs2, hrun1, wp_norm, arm64_norm]
  have hmem2 : s2.mem = s0.mem := by simp [hs2, hmem1, wp_norm, arm64_norm]
  apply with_mlkem_wrapper_step (j := 23) (by decide) (P := P23) rfl (hmem2 ▸ hcl23) hpc2 hrun2
  conv in (P23.fetch _) => simp only [P23, hb, wp_norm, arm64_norm]
  refine ⟨_, rfl, by decide, fun s3 hs3 hk2 hst2 => ?_⟩
  have hpc3 : s3.pc = c2MlkemMpl.base 23 + 12#64 := by simp [hs3, hpc2, wp_norm, arm64_norm]
  have hrun3 : s3.status = .Running := by simp [hs3, hrun2, wp_norm, arm64_norm]
  have hmem3 : s3.mem = s0.mem := by simp [hs3, hmem2, wp_norm, arm64_norm]
  apply with_mlkem_wrapper_step (j := 23) (by decide) (P := P23) rfl (hmem3 ▸ hcl23) hpc3 hrun3
  conv in (P23.fetch _) => simp only [P23, hb, wp_norm, arm64_norm]
  refine ⟨_, rfl, by decide, fun s4 hs4 hk3 hst3 => ?_⟩
  refine ⟨s1, s2, s3, s4, hk0, hst0, hpc1, hrun1, hk1, hst1, hpc2, hrun2,
    hk2, hst2, hpc3, hrun3, hk3, hst3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hs4, hpc3, wp_norm, arm64_norm]
    rfl_kernel
  · simp [hs4, hrun3, wp_norm, arm64_norm]
  · simp [hs4, hmem3, wp_norm, arm64_norm]
  · simp [hs4, hs3, hs2, hs1, wp_norm, arm64_norm]
  · simp [hs4, hs3, hs2, hs1, State.spAligned, wp_norm, arm64_norm]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?_, fun _ h => ?_⟩, ?_⟩
    · simp [hs4, hs3, hs2, hs1, wp_norm, arm64_norm]
    · simp [hs4, hmem3, wp_norm, arm64_norm]
    · simp [hs4, hs3, hs2, hs1, wp_norm, arm64_norm]
    · simp [hs4, hs3, hs2, hs1, wp_norm, arm64_norm]
    · simp [hs4, hs3, hs2, hs1, wp_norm, arm64_norm]
    · simp [hs4, hs3, hs2, hs1, wp_norm, arm64_norm]
    · simpa [hs4, hmem3, wp_norm, arm64_norm] using h
    · simp [hs4, hs3, hs2, hs1, wp_norm, arm64_norm]
  · simp [hs4, hs3, hs2, hs1, wp_norm, arm64_norm]
  · simp [hs4, hs3, hs2, hs1, wp_norm, arm64_norm]
  · simp [hs4, hs3, hs2, hs1, wp_norm, arm64_norm]
  · simp [hs4, hs3, hs2, hs1, wp_norm, arm64_norm]

/-- `snttStrictAvoid` + `ExecFrozen` for `B23 → B06` (`lsKemDecapsSym`, `kemDecapsGhostAt`). -/
theorem c2_kemDecaps_snttStrictAvoid [LibsignalPlacement]
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hLs_ls : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hExt : C2ExternTableFacts mpl)
    {stk : Nat} (hstk : kemDecapsTightStack ≤ stk) (hfit : stk ≤ 2 ^ 64)
    (W : CliHooks) {u : State}
    (hTerm : mlkemSampleNttTermOf lsKemDecapsSym u)
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsKemDecapsSym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (kemDecapsGhostAt c2MlkemMpl stk u).status ≠ .Exception msg)
    (hfr : ExecFrozen u.mem)
    (hInv : F3CodeInv mpl mmpl u.mem) :
    StepsStrictAvoid (fun z => z.status = .Running ∧ MlKemSampleNttStuckAt mpl z)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      u (kemDecapsGhostAt c2MlkemMpl stk u) ∧
      ExecFrozen (kemDecapsGhostAt c2MlkemMpl stk u).mem := by
  have hfr_out : ExecFrozen (kemDecapsGhostAt c2MlkemMpl stk u).mem :=
    mlkemBlockGhost_preserves_execFrozen c2MlkemMpl 23
      (keepsFs (kemDecapsAtSpec stk kyber1024Prims₀)) kemDecapsFallback_preserved hfr
  refine ⟨?_, hfr_out⟩
  have hInvM : mlkemInvMem c2MlkemMpl u.mem := c2_mlkem_invMem_of_f3CodeInv hLs hInv
  have hInvA := c2_mlkemActiveInvMem_of_codeLoaded_roOk hInvM.2.1 hInvM.2.2
  have hpc23 : u.pc = c2MlkemMpl.base 23 := hpc.trans (c2_resolve_kyber1024Decaps_eq hLs)
  obtain ⟨_, hsp, ⟨skA, sk, ctA, ct, ret⟩, R, hpre_ls⟩ :=
    linkedCallHookG_activeRealPre_of_noException hnoex
  have hpre_at : u.mem ⊨ (kemDecapsAtSpec stk kyber1024Prims₀).pre
      (skA, sk, ctA, ct, ret) u ∗ R := by
    simpa only [keepsFs] using (extract_withLsRet hpre_ls).2
  have hTermS : Kyber1024DecapsTerminates sk.toList := by
    have hTerm' := hTerm
    rw [mlkemSampleNttTermOf_kemDecaps u] at hTerm'
    exact (kemDecapsStateTerminates_iff_of_atSpec_pre hpre_at).mp hTerm'
  obtain ⟨s1, s2, s3, s4, hk0, hst0, hpc1, hrun1, hk1, hst1, hpc2, hrun2,
      hk2, hst2, hpc3, hrun3, hk3, hst3, hpc4, hrun4, hmem4, hsp4, hspA4, hnsp_w4,
      hlr4, hx0_4, hx1_4, hx2_4⟩ :=
    blk23_wrapper_steps (hInvM.2.1 23 (by decide)) hpc23 hrun
  dsimp only [kemDecapsAtSpec, withStack] at hpre_at
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre_at
  obtain ⟨⟨hx0_u, hx1_u, hx8_u⟩, hspat⟩ := hpre_at
  rw [stackAt_shrink u.sp stk 35968 hstk hfit] at hspat
  let slack := memRegion (u.sp - BitVec.ofNat 64 stk) (stk - 35968)
  let M6 := blk06FixedMaster ret skA sk ctA ct
  have hpre4 : s4.mem ⊨ M6.pre () s4 ∗ (slack ∗ R) := by
    dsimp only [M6, blk06FixedMaster, slack]
    rw [hmem4, hsp4, hx0_4, hx1_4, hx2_4, hx8_u, hx0_u, hx1_u,
      sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨rfl, rfl, rfl, hTermS⟩, Satisfies.mono (by sep_frame) hspat⟩
  obtain ⟨sf, hvis_act, hret4, _, _, _, hnsp4, _, _⟩ :=
    mlkemActive_run_visitedIn (j := 6) (by decide) c2MlkemMpl blk06_decaps_ok
      (blk06_simulates_fixed ret skA sk ctA ct) rfl rfl rfl
      (by intro _ s _; cases s; rfl) (by intro _ s0 sf _ _; cases s0; cases sf; rfl)
      (fun _ _ => rwP_sep rwP_pure (rwP_sep (rwP_bytes _ _)
        (rwP_sep (rwP_bytes _ _) (rwP_sep (rwP_mem _ _) (rwP_stk _ _)))))
      (fun _ _ => bddP_to6 (by decide) (bddP_sep bddP_pure
        (bddP_sep (bddP_bytes _ _ (by rw [sk.toList_length]; decide))
          (bddP_sep (bddP_bytes _ _ (by rw [ct.toList_length]; decide))
            (bddP_sep (bddP_mem _ _ (by decide)) (bddP_stk _ _ (by decide)))))))
      (fun _ _ _ => rwP_sep (rwP_bytes _ _)
        (rwP_sep (rwP_bytes _ _) (rwP_sep (rwP_bytes _ _) (rwP_stk _ _))))
      hpc4 hrun4 (hspA4.trans hsp) (hmem4 ▸ hInvA) hpre4
  have hvis_tot : h2fsgen_StepsVisitedIn (c2MlkemKeep c2MlkemMpl) emptyStdProg u sf :=
    .step hk0 hst0 (.step hk1 hst1 (.step hk2 hst2 (.step hk3 hst3
      (visitedIn_mono_keep (fun _ hk => mlkemActiveKeep_sub_c2MlkemKeep hk) hvis_act))))
  have hghost_eq : kemDecapsGhostAt c2MlkemMpl stk u = sf :=
    mlkemBlockGhost_eq_of_visitedIn hLs_ls (by decide) hInvM hfr hnoex hpc23 hvis_tot
      (returned_of_wrapper hlr4 hsp4 hret4)
      (nonSyscallPreserved_trans hnsp_w4 hnsp4)
  rw [hghost_eq]
  have hcore_av := stepsStrictAvoid_realProg617_of_visitedIn (mmpl := mmpl)
    (bad := fun z => z.status = .Running ∧ MlKemSampleNttStuckAt mpl z)
    (fun _ hk => mlkemActiveKeep_sub_c2MlkemKeep hk) hExt W
    (fun _ _ hk ⟨_, hst⟩ => not_mlKemSampleNttStuckAt_of_activeKeep hLs hk hst) hvis_act
  exact .step
    (fun ⟨_, hst⟩ => not_mlKemSampleNttStuckAt_of_entry_term hLs (by simp [mlkemSampleNttSyms]) hpc hTerm hst)
    (step_realProg617_of_emptyStdProg hExt W hk0 hst0)
    (.step
      (fun ⟨_, hst⟩ => not_mlKemSampleNttStuckAt_of_s5_offset hLs (j := 23) (off := 4) (by decide) (by decide) (by decide) hpc1 hst)
      (step_realProg617_of_emptyStdProg hExt W hk1 hst1)
      (.step
        (fun ⟨_, hst⟩ => not_mlKemSampleNttStuckAt_of_s5_offset hLs (j := 23) (off := 8) (by decide) (by decide) (by decide) hpc2 hst)
        (step_realProg617_of_emptyStdProg hExt W hk2 hst2)
        (.step
          (fun ⟨_, hst⟩ => not_mlKemSampleNttStuckAt_of_s5_offset hLs (j := 23) (off := 12) (by decide) (by decide) (by decide) hpc3 hst)
          (step_realProg617_of_emptyStdProg hExt W hk3 hst3)
          hcore_av)))

/-! ## 4. Row `B22 → B04`: `lsMlkemDecapsSym` (`mlkemDecapsGhostAt c2MlkemMpl stk`) -/

private noncomputable def blk04FixedMaster (x : MlkemDecapsCall) : Spec Unit where
  pre := fun _ s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.dkA ∧
      s.readReg64 .x2 = x.ct1A ∧ s.readReg64 .x3 = x.ct2A ∧
      Mlkem768DecapsTerminates x.dk⌝ ∗
      (x.dkA ↦ₛ x.dk.toList) ∗ (x.ct1A ↦ₛ x.ct1.toList) ∗ (x.ct2A ↦ₛ x.ct2.toList) ∗
      memRegion x.ret 32 ∗ stackAt s.sp 26960
  post := fun _ s0 _ =>
    (x.dkA ↦ₛ x.dk.toList) ∗ (x.ct1A ↦ₛ x.ct1.toList) ∗ (x.ct2A ↦ₛ x.ct2.toList) ∗
      (x.ret ↦ₛ mlkem768DecapsWith sampleNtt x.dk.toList x.ct1.toList x.ct2.toList) ∗
      stackAt s0.sp 26960
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem blk04_simulates_fixed (x : MlkemDecapsCall) (mpl : MultiPlacement) :
    SpecSimulates (mlkemBlk04TermCoreSpec mpl) (withMlKemRoOk mpl (blk04FixedMaster x)) := by
  refine SpecSimulates.of_map ?_
  intro _ R s0 hm
  dsimp only [withMlKemRoOk, blk04FixedMaster] at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hro, hm⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
      satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hx0, hx1, hx2, hx3, hTerm⟩, hm⟩
  refine ⟨(x.ret, x.dkA, x.dk.toList, x.ct1A, x.ct1.toList, x.ct2A, x.ct2.toList), R, ?_, ?_⟩
  · dsimp only [mlkemBlk04TermCoreSpec, withNonSyscallPreserved,
      mlkemBlk04TermRawSpec, mlkemBlk04RawSpec]
    have hTerm' : Mlkem768DecapsTerminates (toByteVec 2400 x.dk.toList) := by
      rwa [toByteVec_of_vector x.dk]
    rw [sepConj_assoc, pure_sepConj_of_true hTerm',
      sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
      satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, x.dk.toList_length, x.ct1.toList_length, x.ct2.toList_length,
      hro⟩, Satisfies.mono (by sep_frame) hm⟩
  · intro sf _ _ hpost
    dsimp only [mlkemBlk04TermCoreSpec, withNonSyscallPreserved,
      mlkemBlk04TermRawSpec, mlkemBlk04RawSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    dsimp only [withMlKemRoOk, blk04FixedMaster]
    exact Satisfies.mono (by sep_frame) hpost.2

private theorem blk22_wrapper_steps {s0 : State}
    (hcl22 : (mlkemMultiLib.blockProgram c2MlkemMpl 22).CodeLoaded s0.mem)
    (hpc : s0.pc = c2MlkemMpl.base 22) (hrun : s0.status = .Running) :
    ∃ s1 s2 s3 s4 s5 : State,
      c2MlkemKeep c2MlkemMpl s0.pc = true ∧ Step emptyStdProg s0 s1 ∧
      s1.pc = c2MlkemMpl.base 22 + BitVec.ofNat 64 4 ∧ s1.status = .Running ∧
      c2MlkemKeep c2MlkemMpl s1.pc = true ∧ Step emptyStdProg s1 s2 ∧
      s2.pc = c2MlkemMpl.base 22 + BitVec.ofNat 64 8 ∧ s2.status = .Running ∧
      c2MlkemKeep c2MlkemMpl s2.pc = true ∧ Step emptyStdProg s2 s3 ∧
      s3.pc = c2MlkemMpl.base 22 + BitVec.ofNat 64 12 ∧ s3.status = .Running ∧
      c2MlkemKeep c2MlkemMpl s3.pc = true ∧ Step emptyStdProg s3 s4 ∧
      s4.pc = c2MlkemMpl.base 22 + BitVec.ofNat 64 16 ∧ s4.status = .Running ∧
      c2MlkemKeep c2MlkemMpl s4.pc = true ∧ Step emptyStdProg s4 s5 ∧
      s5.pc = c2MlkemMpl.base 4 ∧ s5.status = .Running ∧
      s5.mem = s0.mem ∧ s5.sp = s0.sp ∧ s5.spAligned = s0.spAligned ∧
      ProofLib.NonSyscallPreserved s0 s5 ∧
      s5.readReg64 .lr = s0.readReg64 .lr ∧
      s5.readReg64 .x0 = s0.readReg64 .x8 ∧
      s5.readReg64 .x1 = s0.readReg64 .x0 ∧
      s5.readReg64 .x2 = s0.readReg64 .x1 ∧
      s5.readReg64 .x3 = s0.readReg64 .x2 := by
  have hb : c2MlkemMpl.base 22 = blkPl22.base := rfl
  let P22 := blkPC22.rebase (c2MlkemMpl.base 22) (fun _ => none)
  apply with_mlkem_wrapper_step (j := 22) (by decide) (P := P22) rfl hcl22 hpc hrun
  conv in (P22.fetch _) => simp only [P22, hb, wp_norm, arm64_norm]
  refine ⟨_, rfl, by decide, fun s1 hs1 hk0 hst0 => ?_⟩
  have hpc1 : s1.pc = c2MlkemMpl.base 22 + 4#64 := by simp [hs1, hpc, wp_norm, arm64_norm]
  have hrun1 : s1.status = .Running := by simp [hs1, hrun, wp_norm, arm64_norm]
  have hmem1 : s1.mem = s0.mem := by simp [hs1, wp_norm, arm64_norm]
  apply with_mlkem_wrapper_step (j := 22) (by decide) (P := P22) rfl (hmem1 ▸ hcl22) hpc1 hrun1
  conv in (P22.fetch _) => simp only [P22, hb, wp_norm, arm64_norm]
  refine ⟨_, rfl, by decide, fun s2 hs2 hk1 hst1 => ?_⟩
  have hpc2 : s2.pc = c2MlkemMpl.base 22 + 8#64 := by simp [hs2, hpc1, wp_norm, arm64_norm]
  have hrun2 : s2.status = .Running := by simp [hs2, hrun1, wp_norm, arm64_norm]
  have hmem2 : s2.mem = s0.mem := by simp [hs2, hmem1, wp_norm, arm64_norm]
  apply with_mlkem_wrapper_step (j := 22) (by decide) (P := P22) rfl (hmem2 ▸ hcl22) hpc2 hrun2
  conv in (P22.fetch _) => simp only [P22, hb, wp_norm, arm64_norm]
  refine ⟨_, rfl, by decide, fun s3 hs3 hk2 hst2 => ?_⟩
  have hpc3 : s3.pc = c2MlkemMpl.base 22 + 12#64 := by simp [hs3, hpc2, wp_norm, arm64_norm]
  have hrun3 : s3.status = .Running := by simp [hs3, hrun2, wp_norm, arm64_norm]
  have hmem3 : s3.mem = s0.mem := by simp [hs3, hmem2, wp_norm, arm64_norm]
  apply with_mlkem_wrapper_step (j := 22) (by decide) (P := P22) rfl (hmem3 ▸ hcl22) hpc3 hrun3
  conv in (P22.fetch _) => simp only [P22, hb, wp_norm, arm64_norm]
  refine ⟨_, rfl, by decide, fun s4 hs4 hk3 hst3 => ?_⟩
  have hpc4 : s4.pc = c2MlkemMpl.base 22 + 16#64 := by simp [hs4, hpc3, wp_norm, arm64_norm]
  have hrun4 : s4.status = .Running := by simp [hs4, hrun3, wp_norm, arm64_norm]
  have hmem4 : s4.mem = s0.mem := by simp [hs4, hmem3, wp_norm, arm64_norm]
  apply with_mlkem_wrapper_step (j := 22) (by decide) (P := P22) rfl (hmem4 ▸ hcl22) hpc4 hrun4
  conv in (P22.fetch _) => simp only [P22, hb, wp_norm, arm64_norm]
  refine ⟨_, rfl, by decide, fun s5 hs5 hk4 hst4 => ?_⟩
  refine ⟨s1, s2, s3, s4, s5, hk0, hst0, hpc1, hrun1, hk1, hst1, hpc2, hrun2,
    hk2, hst2, hpc3, hrun3, hk3, hst3, hpc4, hrun4, hk4, hst4,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hs5, hpc4, wp_norm, arm64_norm]
    rfl_kernel
  · simp [hs5, hrun4, wp_norm, arm64_norm]
  · simp [hs5, hmem4, wp_norm, arm64_norm]
  · simp [hs5, hs4, hs3, hs2, hs1, wp_norm, arm64_norm]
  · simp [hs5, hs4, hs3, hs2, hs1, State.spAligned, wp_norm, arm64_norm]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?_, fun _ h => ?_⟩, ?_⟩
    · simp [hs5, hs4, hs3, hs2, hs1, wp_norm, arm64_norm]
    · simp [hs5, hmem4, wp_norm, arm64_norm]
    · simp [hs5, hs4, hs3, hs2, hs1, wp_norm, arm64_norm]
    · simp [hs5, hs4, hs3, hs2, hs1, wp_norm, arm64_norm]
    · simp [hs5, hs4, hs3, hs2, hs1, wp_norm, arm64_norm]
    · simp [hs5, hs4, hs3, hs2, hs1, wp_norm, arm64_norm]
    · simpa [hs5, hmem4, wp_norm, arm64_norm] using h
    · simp [hs5, hs4, hs3, hs2, hs1, wp_norm, arm64_norm]
  · simp [hs5, hs4, hs3, hs2, hs1, wp_norm, arm64_norm]
  · simp [hs5, hs4, hs3, hs2, hs1, wp_norm, arm64_norm]
  · simp [hs5, hs4, hs3, hs2, hs1, wp_norm, arm64_norm]
  · simp [hs5, hs4, hs3, hs2, hs1, wp_norm, arm64_norm]
  · simp [hs5, hs4, hs3, hs2, hs1, wp_norm, arm64_norm]

/-- `snttStrictAvoid` + `ExecFrozen` for `B22 → B04` (`lsMlkemDecapsSym`, `mlkemDecapsGhostAt`). -/
theorem c2_mlkemDecaps_snttStrictAvoid [LibsignalPlacement]
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hLs_ls : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hExt : C2ExternTableFacts mpl)
    {stk : Nat} (hstk : mlkemDecapsTightStack ≤ stk) (hfit : stk ≤ 2 ^ 64)
    (W : CliHooks) {u : State}
    (hTerm : mlkemSampleNttTermOf lsMlkemDecapsSym u)
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsMlkemDecapsSym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (mlkemDecapsGhostAt c2MlkemMpl stk u).status ≠ .Exception msg)
    (hfr : ExecFrozen u.mem)
    (hInv : F3CodeInv mpl mmpl u.mem) :
    StepsStrictAvoid (fun z => z.status = .Running ∧ MlKemSampleNttStuckAt mpl z)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      u (mlkemDecapsGhostAt c2MlkemMpl stk u) ∧
      ExecFrozen (mlkemDecapsGhostAt c2MlkemMpl stk u).mem := by
  have hfr_out : ExecFrozen (mlkemDecapsGhostAt c2MlkemMpl stk u).mem :=
    mlkemBlockGhost_preserves_execFrozen c2MlkemMpl 22
      (keepsFs (mlkemDecapsAtSpec stk mlkem768Incremental)) mlkemDecapsFallback_preserved hfr
  refine ⟨?_, hfr_out⟩
  have hInvM : mlkemInvMem c2MlkemMpl u.mem := c2_mlkem_invMem_of_f3CodeInv hLs hInv
  have hInvA := c2_mlkemActiveInvMem_of_codeLoaded_roOk hInvM.2.1 hInvM.2.2
  have hpc22 : u.pc = c2MlkemMpl.base 22 := hpc.trans (c2_resolve_mlkem768Decaps_eq hLs)
  obtain ⟨_, hsp, x, R, hpre_ls⟩ := linkedCallHookG_activeRealPre_of_noException hnoex
  have hpre_at : u.mem ⊨ (mlkemDecapsAtSpec stk mlkem768Incremental).pre x u ∗ R := by
    simpa only [keepsFs] using (extract_withLsRet hpre_ls).2
  have hTermS : Mlkem768DecapsTerminates x.dk := by
    have hTerm' := hTerm
    rw [mlkemSampleNttTermOf_mlkemDecaps u] at hTerm'
    exact (mlkemDecapsStateTerminates_iff_of_atSpec_pre hpre_at).mp hTerm'
  obtain ⟨s1, s2, s3, s4, s5, hk0, hst0, hpc1, hrun1, hk1, hst1, hpc2, hrun2,
      hk2, hst2, hpc3, hrun3, hk3, hst3, hpc4, hrun4, hk4, hst4,
      hpc5, hrun5, hmem5, hsp5, hspA5, hnsp_w5, hlr5, hx0_5, hx1_5, hx2_5, hx3_5⟩ :=
    blk22_wrapper_steps (hInvM.2.1 22 (by decide)) hpc22 hrun
  dsimp only [mlkemDecapsAtSpec] at hpre_at
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
      satisfies_pure_sepConj] at hpre_at
  obtain ⟨⟨hx8_u, hx0_u, hx1_u, hx2_u⟩, hspat⟩ := hpre_at
  rw [stackAt_shrink u.sp stk 26960 hstk hfit] at hspat
  let slack := memRegion (u.sp - BitVec.ofNat 64 stk) (stk - 26960)
  let M4 := blk04FixedMaster x
  have hpre5 : s5.mem ⊨ M4.pre () s5 ∗ (slack ∗ R) := by
    dsimp only [M4, blk04FixedMaster, slack]
    rw [hmem5, hsp5, hx0_5, hx1_5, hx2_5, hx3_5, hx8_u, hx0_u, hx1_u, hx2_u,
      sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
      satisfies_pure_sepConj]
    exact ⟨⟨rfl, rfl, rfl, rfl, hTermS⟩, Satisfies.mono (by sep_frame) hspat⟩
  obtain ⟨sf, hvis_act, hret5, _, _, _, hnsp5, _, _⟩ :=
    mlkemActive_run_visitedIn (j := 4) (by decide) c2MlkemMpl blk04_decaps_ok
      (blk04_simulates_fixed x) rfl rfl rfl
      (by intro _ s _; cases s; rfl) (by intro _ s0 sf _ _; cases s0; cases sf; rfl)
      (fun _ _ => rwP_sep rwP_pure (rwP_sep (rwP_bytes _ _) (rwP_sep (rwP_bytes _ _)
        (rwP_sep (rwP_bytes _ _) (rwP_sep (rwP_mem _ _) (rwP_stk _ _))))))
      (fun _ _ => bddP_to6 (by decide) (bddP_sep bddP_pure
        (bddP_sep (bddP_bytes _ _ (by rw [x.dk.toList_length]; decide))
          (bddP_sep (bddP_bytes _ _ (by rw [x.ct1.toList_length]; decide))
            (bddP_sep (bddP_bytes _ _ (by rw [x.ct2.toList_length]; decide))
              (bddP_sep (bddP_mem _ _ (by decide)) (bddP_stk _ _ (by decide))))))))
      (fun _ _ _ => rwP_sep (rwP_bytes _ _) (rwP_sep (rwP_bytes _ _)
        (rwP_sep (rwP_bytes _ _) (rwP_sep (rwP_bytes _ _) (rwP_stk _ _)))))
      hpc5 hrun5 (hspA5.trans hsp) (hmem5 ▸ hInvA) hpre5
  have hvis_tot : h2fsgen_StepsVisitedIn (c2MlkemKeep c2MlkemMpl) emptyStdProg u sf :=
    .step hk0 hst0 (.step hk1 hst1 (.step hk2 hst2 (.step hk3 hst3 (.step hk4 hst4
      (visitedIn_mono_keep (fun _ hk => mlkemActiveKeep_sub_c2MlkemKeep hk) hvis_act)))))
  have hghost_eq : mlkemDecapsGhostAt c2MlkemMpl stk u = sf :=
    mlkemBlockGhost_eq_of_visitedIn hLs_ls (by decide) hInvM hfr hnoex hpc22 hvis_tot
      (returned_of_wrapper hlr5 hsp5 hret5)
      (nonSyscallPreserved_trans hnsp_w5 hnsp5)
  rw [hghost_eq]
  have hcore_av := stepsStrictAvoid_realProg617_of_visitedIn (mmpl := mmpl)
    (bad := fun z => z.status = .Running ∧ MlKemSampleNttStuckAt mpl z)
    (fun _ hk => mlkemActiveKeep_sub_c2MlkemKeep hk) hExt W
    (fun _ _ hk ⟨_, hst⟩ => not_mlKemSampleNttStuckAt_of_activeKeep hLs hk hst) hvis_act
  exact .step
    (fun ⟨_, hst⟩ => not_mlKemSampleNttStuckAt_of_entry_term hLs (by simp [mlkemSampleNttSyms]) hpc hTerm hst)
    (step_realProg617_of_emptyStdProg hExt W hk0 hst0)
    (.step
      (fun ⟨_, hst⟩ => not_mlKemSampleNttStuckAt_of_s5_offset hLs (j := 22) (off := 4) (by decide) (by decide) (by decide) hpc1 hst)
      (step_realProg617_of_emptyStdProg hExt W hk1 hst1)
      (.step
        (fun ⟨_, hst⟩ => not_mlKemSampleNttStuckAt_of_s5_offset hLs (j := 22) (off := 8) (by decide) (by decide) (by decide) hpc2 hst)
        (step_realProg617_of_emptyStdProg hExt W hk2 hst2)
        (.step
          (fun ⟨_, hst⟩ => not_mlKemSampleNttStuckAt_of_s5_offset hLs (j := 22) (off := 12) (by decide) (by decide) (by decide) hpc3 hst)
          (step_realProg617_of_emptyStdProg hExt W hk3 hst3)
          (.step
            (fun ⟨_, hst⟩ => not_mlKemSampleNttStuckAt_of_s5_offset hLs (j := 22) (off := 16) (by decide) (by decide) (by decide) hpc4 hst)
            (step_realProg617_of_emptyStdProg hExt W hk4 hst4)
            hcore_av))))

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeMlKemAvoidTail
