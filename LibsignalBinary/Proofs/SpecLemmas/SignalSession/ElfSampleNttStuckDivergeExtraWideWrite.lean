/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliIoWriteRow -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeCore -- proof-setup: allow-public-import
import LibsignalBinary.Heap.Fine.F3LayoutData
import LibsignalBinary.Heap.Fine.SpecBudgetHelpersFine
import LibsignalBinary.Heap.SpecBudget
import LibsignalBinary.Proofs.HookDischarge.CliIoFmt.WriteFileProof
import LibsignalBinary.Proofs.HookDischarge.CliIoFmt.WriteStdoutProof
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook
import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileCliIoInst
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.AesCbc
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliIoWrite
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CodeSubslice
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemPlaceable
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliIoMusl9
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliIoWriteGhostReplays
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemFirstStopTransfer
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet
import LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHonestSpecs
import LibsignalBinary.Proofs.SignalSession.CliIo.Sym
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen
import ProofLib.ProgramReflection
import VerifiedLibraries.Musl.Proofs.SyscallProof

/-!
# Pre-`SampleNTT` `StepsStrictAvoid` Discharges for `write_stdout` and `write_file` (`ElfSampleNttStuckDivergeExtraWideWrite`)

Proves `StepsStrictAvoid (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve mpl))`
on `cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W` for the wide-keep I/O ghost hooks
`c2WriteStdoutGhost` (`lsWriteStdoutSym`), `c2WriteFileGhost` (`lsWriteFileSym`), and
`c2WriteFileFdsGhost` (`lsWriteFileSym` under `FdsGe3Closed`).

Executes `cliIoWriteStdout_honest_withCodeLoaded_ok` and `cliIoWriteFile_budget_withCodeLoaded_ok`
on the pre-`SampleNTT` RX prefix `f3PreS5RxProg` (`[f3RxSegBase, c2Mlkem768FromSeedAddr)`),
strictly below all five `mlkemSampleNttSyms` entrypoints while containing `mallocngLib`,
`signalSessionIoMultiLib`, and the nine `muslSysPlacedLib` syscall blocks.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraWideWrite

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection ProofLib.SepLogic
open VerifiedLibraries (mallocngLib)
open VerifiedLibraries.Musl (muslSysPlacedLib)
open CryptoVerification
  (LibsignalPlacement lsmpl signalSessionIoMultiLib)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliExternsPlaced libsignalSessionLib
   lsWriteFileSym lsWriteStdoutSym writeFileHook writeStdoutHook)
open CryptoVerification.SignalSession.Cli.MainHops (WriteFileGhost WriteStdoutGhost cliIo)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open LibsignalBinary.Heap (BudgetLimits VmPreserved)
open LibsignalBinary.Heap.Fine (f3RxWordCount fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.CliIoFmt.WriteFileProof
  (cliIoWriteFile_budget_withCodeLoaded_ok writeFileHonestCoreClamped writeFileSpecPlacedSatClamped)
open LibsignalBinary.Proofs.HookDischarge.CliIoFmt.WriteStdoutProof
  (cliIoWriteStdout_honest_withCodeLoaded_ok)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (ExecFrozen SpecStripSInvariant)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook
  (fineHookRustCliAllocBudget_pool_stripS)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (FdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileCliIoInst (fineHookPoolErrnoSplit)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks (ActiveF3CallPre)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.AesCbc
  (c2_mng_placeable keepRxSeg_eq_lt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliIoWrite
  (c2CliIoMpl c2CliIoMpl_placeable c2MuslSysMpl c2MuslSysMpl_placeable c2WriteLoByteLen
   c2_cliIo_codeLoaded_of_f3CodeInv c2_cliIo_seg2_rx_blocks c2_muslSys9_rx_blocks
   c2_resolve_writeFile_resolve c2_resolve_writeStdout_resolve f3WriteLoRxProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliIoWriteRow
  (c2KeepWriteIo c2WriteFileFdsGhost c2WriteFileGhost c2WriteStdoutGhost
   c2_writeIo_invCodeIo c2_writeIo_invCodeSub c2_writeIo_lr_out c2_writeIo_realNoExt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CodeSubslice
  (rxSubslice_of_checkProgCodeSubslice)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemPlaceable
  (c2Kyber1024DecapsAddr c2Kyber1024EncapsAddr c2Mlkem768DecapsAddr c2Mlkem768Encaps1Addr
   c2Mlkem768FromSeedAddr c2_resolve_kyber1024Decaps_eq c2_resolve_kyber1024Encaps_eq
   c2_resolve_mlkem768Decaps_eq c2_resolve_mlkem768Encaps1_eq c2_resolve_mlkem768FromSeed_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliIoMusl9
  (muslClose48Local_of_where9_ok muslErrnoLocation_of_where9_ok
   muslOpenCreateTrunc_of_where9_ok muslWriteFile32Clamped_of_where9_ok
   muslWriteStdout32_of_where9_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliIoWriteGhostReplays
  (ActiveWriteIoRun subroutine_ok_withCodeLoaded_withLsRet writeFileCoreSpecOf
   writeFileFdsGhost_eq_of_fds writeFileGhost writeIoLinkedGhost
   writeIoLinkedGhost_activePre_of_noException writeIo_elim_stripS
   writeStdoutCoreSpecOf writeStdoutGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemFirstStopTransfer
  (mlkemSampleNttSyms)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (extract_withLsRet withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHonestSpecs
  (writeFileHonestCore writeFileSpecPlacedSat writeStdoutHonestCore)
open LibsignalBinary.Proofs.SignalSession.CliIo.Sym
  (CliIoBlockNoExtern cliIoCloseSym cliIoErrnoLocationSym cliIoOpenSym
   cliIoWriteFileSym cliIoWriteStdoutSym cliIoWriteSym)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData (f3MngCodeHi f3MngCodeLo)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced
  (f3CliElf_mallocng_code_bounds_of_inElf f3TrialElf f3TrialElf_parse)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeInv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
  (f3RxSegBase f3TrialRxProg f3TrialRxProg_base f3TrialRxProg_no_ext f3TrialRxProg_svc
   f3TrialRxWordTree_eq f3TrialRxWordTree_size)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeCore
  (StepsStrictAvoid)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric
  (h2fsgen_StepsVisitedIn h2fsgen_fetchMem_eq_of_externAt_eq h2fsgen_stepsUntil_det)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen
  (c2FirstExternStubAddr wp4WriteFileAddr wp4WriteStdoutAddr)

/-! ## 1. Pre-`SampleNTT` Prefix `f3PreS5RxProg` & `c2KeepWritePreS5` -/

/-- Byte length of the panic-free pre-`SampleNTT` `seg[2]` prefix `[f3RxSegBase, c2Lib2TextLo)`. -/
private def c2PreS5ByteLen : Nat :=
  c2WriteLoByteLen

/-- Pre-`SampleNTT` keep hull: `seg[1]` `:text_a` `[wp4WriteFileAddr, c2FirstExternStubAddr)`
    unioned with `seg[2]` `[f3RxSegBase, f3RxSegBase + c2PreS5ByteLen)`. -/
private def c2KeepWritePreS5 (a : BitVec 64) : Bool :=
  decide (wp4WriteFileAddr.toNat ≤ a.toNat ∧ a.toNat < c2FirstExternStubAddr.toNat) ||
    decide ((a - f3RxSegBase).toNat < c2PreS5ByteLen)

/-- Hook-free `Syscall.standard` prefix of `f3TrialRxProg` strictly below all `mlkemSampleNttSyms`
    entrypoints. -/
private noncomputable def f3PreS5RxProg : Program :=
  { base := f3RxSegBase
    code := f3TrialRxProg.code.take c2PreS5ByteLen
    svc := Syscall.standard }

private theorem f3PreS5RxProg_base : f3PreS5RxProg.base = f3RxSegBase := rfl

private theorem f3PreS5RxProg_svc : f3PreS5RxProg.svc = Syscall.standard := rfl

private theorem f3PreS5RxProg_no_ext (pc : BitVec 64) : f3PreS5RxProg.externAt? pc = none := rfl

private theorem f3TrialRxProg_code_len :
    f3TrialRxProg.code.length = 4 * f3RxWordCount := by
  rw [f3TrialRxWordTree_eq]
  exact WordTree.length_toBytes_of_checkSize? f3TrialRxWordTree_size

private theorem c2PreS5ByteLen_le_rx : c2PreS5ByteLen ≤ 4 * f3RxWordCount := by
  decide

private theorem f3PreS5RxProg_code_len :
    f3PreS5RxProg.code.length = c2PreS5ByteLen := by
  dsimp only [f3PreS5RxProg]
  rw [List.length_take, f3TrialRxProg_code_len]
  exact Nat.min_eq_left c2PreS5ByteLen_le_rx

private theorem take_getElem_eq (cs : List (BitVec 8)) (n i : Nat)
    (h1 : i < (cs.take n).length) (h2 : i < cs.length) :
    (cs.take n)[i]'h1 = cs[i]'h2 := by
  simp only [List.getElem_take]

private theorem f3PreS5RxProg_getElem (i : Nat)
    (h1 : i < f3PreS5RxProg.code.length) (h2 : i < f3TrialRxProg.code.length) :
    f3PreS5RxProg.code[i]'h1 = f3TrialRxProg.code[i]'h2 := by
  dsimp only [f3PreS5RxProg] at h1 ⊢
  exact take_getElem_eq f3TrialRxProg.code c2PreS5ByteLen i h1 h2

private theorem f3PreS5RxProg_eq_writeLo : f3PreS5RxProg = f3WriteLoRxProg := rfl

attribute [local irreducible] f3PreS5RxProg

private theorem c2KeepWritePreS5_imp_c2KeepWriteIo {a : BitVec 64}
    (hk : c2KeepWritePreS5 a = true) :
    c2KeepWriteIo a = true :=
  hk

private theorem c2_writePreS5_lr_out [LibsignalPlacement]
    (hLsLsmpl : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (lr : BitVec 64) (hlr : LsRetAddr624 lr) :
    c2KeepWritePreS5 lr = false := by
  have hw := c2_writeIo_lr_out hLsLsmpl lr hlr
  cases hp : c2KeepWritePreS5 lr with
  | false => rfl
  | true => exact absurd (c2KeepWritePreS5_imp_c2KeepWriteIo hp) (by rw [hw]; decide)

private theorem c2_writePreS5_realNoExt {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (W : CliHooks) (pc : BitVec 64) (hk : c2KeepWritePreS5 pc = true) :
    (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none :=
  c2_writeIo_realNoExt hLs W pc (c2KeepWritePreS5_imp_c2KeepWriteIo hk)

private theorem c2KeepWritePreS5_lt_fromSeed {pc : BitVec 64}
    (hk : c2KeepWritePreS5 pc = true) :
    pc.toNat < c2Mlkem768FromSeedAddr.toNat := by
  unfold c2KeepWritePreS5 at hk
  rcases Bool.or_eq_true_iff.mp hk with h1 | h2
  · have hseg1 := (of_decide_eq_true h1).2
    have hub : c2FirstExternStubAddr.toNat ≤ c2Mlkem768FromSeedAddr.toNat := by decide
    omega
  · have hlt := of_decide_eq_true h2
    by_cases hge : f3RxSegBase.toNat ≤ pc.toNat
    · have hsub : (pc - f3RxSegBase).toNat = pc.toNat - f3RxSegBase.toNat :=
        BitVec.toNat_sub_of_le (BitVec.le_def.mpr hge)
      have hsum : f3RxSegBase.toNat + c2PreS5ByteLen ≤ c2Mlkem768FromSeedAddr.toNat := by decide
      omega
    · have hrx_le : f3RxSegBase.toNat ≤ c2Mlkem768FromSeedAddr.toNat := by decide
      omega

private theorem c2KeepWritePreS5_not_mem_s5 {mpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {pc : BitVec 64} (hk : c2KeepWritePreS5 pc = true) :
    pc ∉ mlkemSampleNttSyms.map (libsignalSessionLib.resolve mpl) := by
  have hlt := c2KeepWritePreS5_lt_fromSeed hk
  unfold mlkemSampleNttSyms
  simp only [List.map_cons, List.map_nil, c2_resolve_kyber1024Encaps_eq hLs,
    c2_resolve_kyber1024Decaps_eq hLs, c2_resolve_mlkem768FromSeed_eq hLs,
    c2_resolve_mlkem768Encaps1_eq hLs, c2_resolve_mlkem768Decaps_eq hLs,
    List.mem_cons, List.not_mem_nil, or_false]
  rintro (rfl | rfl | rfl | rfl | rfl)
  · exact absurd hlt (by decide)
  · exact absurd hlt (by decide)
  · exact Nat.lt_irrefl _ hlt
  · exact absurd hlt (by decide)
  · exact absurd hlt (by decide)

/-! ## 2. `mallocng`, `muslSysPlacedLib`, & `signalSessionIoMultiLib` Bounds in `f3PreS5RxProg` -/

private theorem c2_mng_inElf (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    mallocngLib.InElf f3TrialElf mmpl := by
  obtain ⟨img, hparse, _, hIn⟩ := hMm
  cases f3TrialElf_parse.symm.trans hparse
  exact hIn

private theorem c2_keepPreS5_mallocng (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (a : BitVec 64) (hsome : (mallocngLib.findCodeBlock mmpl a).isSome = true) :
    c2KeepWritePreS5 a = true := by
  cases hf : mallocngLib.findCodeBlock mmpl a with
  | none => simp [hf] at hsome
  | some k =>
    have hk : k < mallocngLib.blocks.length := findCodeBlock_lt hf
    have hin : Arm64.InRegion (mmpl.base k) (mallocngLib.blockPatched mmpl k).length a :=
      findCodeBlock_inRegion hf
    have hlen : (mallocngLib.blockPatched mmpl k).length = mallocngLib.blocks[k].code.length := by
      unfold MultiPlacedLib.blockPatched
      rw [mallocngLib.blockLib_text hk]
      exact CodeBlock.length_patched_of_aligned _
        ((c2_mng_placeable mmpl hMm).blocks_ok k hk).len_aligned
    rw [hlen] at hin
    obtain ⟨_, _, hm_lo, hm_hi⟩ :=
      f3CliElf_mallocng_code_bounds_of_inElf
        (c2_mng_placeable mmpl hMm) (c2_mng_inElf mmpl hMm) k hk
    have hk_off : (a - mmpl.base k).toNat < mallocngLib.blocks[k].code.length := hin
    have heq_a : mmpl.base k + BitVec.ofNat 64 (a - mmpl.base k).toNat = a := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
    have hlo_rx : f3RxSegBase.toNat ≤ f3MngCodeLo := by decide
    have hhi_pre : f3MngCodeHi ≤ f3RxSegBase.toNat + c2PreS5ByteLen := by decide
    have htop : f3RxSegBase.toNat + c2PreS5ByteLen < 2 ^ 64 := by decide
    have ht : (mmpl.base k + BitVec.ofNat 64 (a - mmpl.base k).toNat).toNat =
        (mmpl.base k).toNat + (a - mmpl.base k).toNat := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
    rw [heq_a] at ht
    have hlt_pre : (a - f3RxSegBase).toNat < c2PreS5ByteLen := by
      rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))]
      omega
    unfold c2KeepWritePreS5
    rw [decide_eq_true hlt_pre, Bool.or_true]

private theorem codeLoaded_strip_of_keep {P : Program} {keep : BitVec 64 → Bool} {m : Memory}
    (hL : P.CodeLoaded m)
    (hk : ∀ i : Nat, i < P.code.length → keep (P.base + BitVec.ofNat 64 i) = true) :
    P.CodeLoaded (stripExecOutside keep m) := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
  rw [strip_read8, strip_perm_of_keep (hk i hi), strip_isLazyFree]
  exact ⟨hL.byte_eq i hi, hL.perm_eq i hi, hL.isLazyFree_eq i hi⟩

private theorem f3PreS5RxProg_codeLoaded_of_trial {m : Memory}
    (hcl : f3TrialRxProg.CodeLoaded m) :
    f3PreS5RxProg.CodeLoaded m := by
  have hlen_le : f3PreS5RxProg.code.length ≤ f3TrialRxProg.code.length := by
    rw [f3PreS5RxProg_code_len, f3TrialRxProg_code_len]
    exact c2PreS5ByteLen_le_rx
  have hbase : f3PreS5RxProg.base = f3TrialRxProg.base :=
    f3PreS5RxProg_base.trans f3TrialRxProg_base.symm
  have halign := hcl.aligned
  rw [← hbase] at halign
  have hnowrap : f3PreS5RxProg.base.toNat + f3PreS5RxProg.code.length ≤ 2 ^ 64 := by
    have hnw := hcl.no_wrap
    rw [← hbase] at hnw
    omega
  refine Program.CodeLoaded.intro halign hnowrap fun i hi => ?_
  have hi_full : i < f3TrialRxProg.code.length := Nat.lt_of_lt_of_le hi hlen_le
  have haddr : f3PreS5RxProg.base + BitVec.ofNat 64 i =
      f3TrialRxProg.base + BitVec.ofNat 64 i :=
    congrArg (· + BitVec.ofNat 64 i) hbase
  have hbyte_mem : m.read8 (f3PreS5RxProg.base + BitVec.ofNat 64 i) =
      f3PreS5RxProg.code[i]'hi := by
    rw [haddr, f3PreS5RxProg_getElem i hi hi_full]
    exact hcl.byte_eq i hi_full
  have hperm_mem := hcl.perm_eq i hi_full
  rw [← haddr] at hperm_mem
  have hlazy_mem := hcl.isLazyFree_eq i hi_full
  rw [← haddr] at hlazy_mem
  exact ⟨hbyte_mem, hperm_mem, hlazy_mem⟩

private theorem c2KeepWritePreS5_of_preS5_offset {i : Nat} (hi : i < c2PreS5ByteLen) :
    c2KeepWritePreS5 (f3RxSegBase + BitVec.ofNat 64 i) = true := by
  have htop : c2PreS5ByteLen < 2 ^ 64 := by decide
  have hi64 : i < 2 ^ 64 := Nat.lt_trans hi htop
  have hlt : (f3RxSegBase + BitVec.ofNat 64 i - f3RxSegBase).toNat < c2PreS5ByteLen := by
    have hsub : f3RxSegBase + BitVec.ofNat 64 i - f3RxSegBase = BitVec.ofNat 64 i := by bv_omega
    rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64]
    exact hi
  unfold c2KeepWritePreS5
  rw [decide_eq_true hlt, Bool.or_true]

private theorem f3PreS5RxProg_codeLoaded_strip {mpl mmpl : MultiPlacement} {m : Memory}
    (hInv : F3CodeInv mpl mmpl m) :
    f3PreS5RxProg.CodeLoaded (stripExecOutside c2KeepWritePreS5 m) := by
  refine codeLoaded_strip_of_keep (f3PreS5RxProg_codeLoaded_of_trial hInv.rxCode) fun i hi => ?_
  rw [f3PreS5RxProg_code_len] at hi
  rw [f3PreS5RxProg_base]
  exact c2KeepWritePreS5_of_preS5_offset hi

set_option maxRecDepth 400000 in
private theorem c2_muslSys9_in_preS5 :
    ((List.range 9).all fun j =>
      let P := muslSysPlacedLib.blockProgram c2MuslSysMpl j
      Nat.ble f3RxSegBase.toNat P.base.toNat &&
        Nat.ble (P.base.toNat + P.code.length)
          (f3RxSegBase.toNat + c2PreS5ByteLen)) = true := by
  rfl_kernel

private theorem c2_muslSys_codeLoadedWhere9_of_preS5 {m : Memory}
    (hPre : f3PreS5RxProg.CodeLoaded m) :
    muslSysPlacedLib.CodeLoadedWhere (fun j => decide (j < 9)) c2MuslSysMpl m := by
  intro j _ hj_dec
  have hj : j < 9 := of_decide_eq_true hj_dec
  have hbnd := List.all_eq_true.mp c2_muslSys9_in_preS5 j (List.mem_range.mpr hj)
  dsimp only at hbnd
  simp only [Bool.and_eq_true, Nat.ble_eq] at hbnd
  obtain ⟨hlo, hhi⟩ := hbnd
  obtain ⟨hAlign, hNoWrap, hSub⟩ := rxSubslice_of_checkProgCodeSubslice (c2_muslSys9_rx_blocks hj)
  generalize muslSysPlacedLib.blockProgram c2MuslSysMpl j = P at hlo hhi hAlign hNoWrap hSub ⊢
  refine Program.CodeLoaded.intro hAlign hNoWrap fun i hi => ?_
  obtain ⟨k, hk_trial, haddr, hbyte⟩ := hSub i hi
  have hk_nat : k < 4 * f3RxWordCount := by
    rw [← f3TrialRxProg_code_len]; exact hk_trial
  rw [f3TrialRxProg_base] at haddr
  have hrx_top : f3RxSegBase.toNat + 4 * f3RxWordCount < 2 ^ 64 := by decide
  have hpre_top : f3RxSegBase.toNat + c2PreS5ByteLen < 2 ^ 64 := by decide
  have hlhs : (P.base + BitVec.ofNat 64 i).toNat = P.base.toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hrhs : (f3RxSegBase + BitVec.ofNat 64 k).toNat = f3RxSegBase.toNat + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have heq_nat : P.base.toNat + i = f3RxSegBase.toNat + k :=
    hlhs.symm.trans ((congrArg BitVec.toNat haddr).trans hrhs)
  have hk_pre : k < f3PreS5RxProg.code.length := by
    rw [f3PreS5RxProg_code_len]; omega
  have hbyte_pre : f3PreS5RxProg.code[k]'hk_pre = f3TrialRxProg.code[k]'hk_trial :=
    f3PreS5RxProg_getElem k hk_pre hk_trial
  have haddr_pre : P.base + BitVec.ofNat 64 i = f3PreS5RxProg.base + BitVec.ofNat 64 k := by
    rw [f3PreS5RxProg_base]; exact haddr
  have hbyte_eq : m.read8 (P.base + BitVec.ofNat 64 i) = P.code[i]'hi := by
    rw [haddr_pre, hbyte, ← hbyte_pre]
    exact hPre.byte_eq k hk_pre
  have hperm_eq := hPre.perm_eq k hk_pre
  rw [← haddr_pre] at hperm_eq
  have hlazy_eq : m.isLazyFree (P.base + BitVec.ofNat 64 i) = false := by
    rw [haddr_pre]; exact hPre.isLazyFree_eq k hk_pre
  exact ⟨hbyte_eq, hperm_eq, hlazy_eq⟩

set_option maxRecDepth 400000 in
private theorem c2_cliIo_seg2_in_preS5 :
    ([0, 3, 4].all fun j =>
      let P := signalSessionIoMultiLib.blockProgram c2CliIoMpl j
      Nat.ble f3RxSegBase.toNat P.base.toNat &&
        Nat.ble (P.base.toNat + P.code.length)
          (f3RxSegBase.toNat + c2PreS5ByteLen)) = true := by
  rfl_kernel

private theorem c2_cliIo_blk1_hi :
    (signalSessionIoMultiLib.blockProgram c2CliIoMpl 1).base.toNat +
      (signalSessionIoMultiLib.blockProgram c2CliIoMpl 1).code.length ≤
      c2FirstExternStubAddr.toNat :=
  Nat.ble_eq.mp (by rfl_kernel)

private theorem c2_cliIo_blk2_hi :
    (signalSessionIoMultiLib.blockProgram c2CliIoMpl 2).base.toNat +
      (signalSessionIoMultiLib.blockProgram c2CliIoMpl 2).code.length ≤
      c2FirstExternStubAddr.toNat :=
  Nat.ble_eq.mp (by rfl_kernel)

private theorem c2KeepWritePreS5_of_seg1_bounds {P : Program}
    (hlo : wp4WriteFileAddr.toNat ≤ P.base.toNat)
    (hhi : P.base.toNat + P.code.length ≤ c2FirstExternStubAddr.toNat)
    {i : Nat} (hi : i < P.code.length) :
    c2KeepWritePreS5 (P.base + BitVec.ofNat 64 i) = true := by
  have htop : c2FirstExternStubAddr.toNat < 2 ^ 64 := BitVec.isLt c2FirstExternStubAddr
  have hadd : (P.base + BitVec.ofNat 64 i).toNat = P.base.toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hseg1 : wp4WriteFileAddr.toNat ≤ (P.base + BitVec.ofNat 64 i).toNat ∧
      (P.base + BitVec.ofNat 64 i).toNat < c2FirstExternStubAddr.toNat := by omega
  unfold c2KeepWritePreS5
  rw [decide_eq_true hseg1, Bool.true_or]

private theorem c2KeepWritePreS5_of_seg2_block {j : Nat} (hj : j ∈ [0, 3, 4])
    {i : Nat} (hi : i < (signalSessionIoMultiLib.blockProgram c2CliIoMpl j).code.length) :
    c2KeepWritePreS5
      ((signalSessionIoMultiLib.blockProgram c2CliIoMpl j).base + BitVec.ofNat 64 i) = true := by
  have hbnd := List.all_eq_true.mp c2_cliIo_seg2_in_preS5 j hj
  dsimp only at hbnd
  simp only [Bool.and_eq_true, Nat.ble_eq] at hbnd
  obtain ⟨hlo, hhi⟩ := hbnd
  generalize signalSessionIoMultiLib.blockProgram c2CliIoMpl j = P at hi hlo hhi ⊢
  have htop : f3RxSegBase.toNat + c2PreS5ByteLen < 2 ^ 64 := by decide
  have hadd : (P.base + BitVec.ofNat 64 i).toNat = P.base.toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hlt_pre : (P.base + BitVec.ofNat 64 i - f3RxSegBase).toNat < c2PreS5ByteLen := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))]
    omega
  unfold c2KeepWritePreS5
  rw [decide_eq_true hlt_pre, Bool.or_true]

private theorem c2_cliIo_codeLoaded_strip_preS5 {mpl mmpl : MultiPlacement} {m : Memory}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hInv : F3CodeInv mpl mmpl m) :
    signalSessionIoMultiLib.CodeLoaded c2CliIoMpl (stripExecOutside c2KeepWritePreS5 m) := by
  have hCode := c2_cliIo_codeLoaded_of_f3CodeInv hLs hInv
  have hlen : signalSessionIoMultiLib.blocks.length = 5 := by decide
  intro j hj
  have hblk := hCode j hj
  rw [hlen] at hj
  match j, hj with
  | 0, _ =>
    exact codeLoaded_strip_of_keep hblk fun _ hi =>
      c2KeepWritePreS5_of_seg2_block (by decide) hi
  | 1, _ =>
    have hlo : wp4WriteFileAddr.toNat ≤
        (signalSessionIoMultiLib.blockProgram c2CliIoMpl 1).base.toNat := Nat.le_refl _
    exact codeLoaded_strip_of_keep hblk fun _ hi =>
      c2KeepWritePreS5_of_seg1_bounds hlo c2_cliIo_blk1_hi hi
  | 2, _ =>
    have hlo : wp4WriteFileAddr.toNat ≤
        (signalSessionIoMultiLib.blockProgram c2CliIoMpl 2).base.toNat := by
      change wp4WriteFileAddr.toNat ≤ wp4WriteStdoutAddr.toNat
      decide
    exact codeLoaded_strip_of_keep hblk fun _ hi =>
      c2KeepWritePreS5_of_seg1_bounds hlo c2_cliIo_blk2_hi hi
  | 3, _ =>
    exact codeLoaded_strip_of_keep hblk fun _ hi =>
      c2KeepWritePreS5_of_seg2_block (by decide) hi
  | 4, _ =>
    exact codeLoaded_strip_of_keep hblk fun _ hi =>
      c2KeepWritePreS5_of_seg2_block (by decide) hi

/-! ## 3. Callee Ties, `SpecStripSInvariant`, & Pre-`SampleNTT` `subroutine_ok` -/

private theorem c2_cliIo_resOpen_fnAddr :
    signalSessionIoMultiLib.resolve c2CliIoMpl cliIoOpenSym =
      muslSysPlacedLib.fnAddr c2MuslSysMpl "open" := by
  rfl_kernel

private theorem c2_cliIo_resErrno_fnAddr :
    signalSessionIoMultiLib.resolve c2CliIoMpl cliIoErrnoLocationSym =
      muslSysPlacedLib.fnAddr c2MuslSysMpl "__errno_location" := by
  rfl_kernel

private theorem c2_cliIo_resWrite_fnAddr :
    signalSessionIoMultiLib.resolve c2CliIoMpl cliIoWriteSym =
      muslSysPlacedLib.fnAddr c2MuslSysMpl "write" := by
  rfl_kernel

private theorem c2_cliIo_resClose_fnAddr :
    signalSessionIoMultiLib.resolve c2CliIoMpl cliIoCloseSym =
      muslSysPlacedLib.fnAddr c2MuslSysMpl "close" := by
  rfl_kernel

private theorem stripS_r64_eq (keep : BitVec 64 → Bool) (s : State) (r : Reg) :
    (stripS keep s).readReg64 r = s.readReg64 r := by cases s; rfl
private theorem stripS_sp_eq (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).sp = s.sp := by cases s; rfl
private theorem stripS_fs_eq (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).fs = s.fs := by cases s; rfl
private theorem stripS_trace_eq (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).trace = s.trace := by cases s; rfl
private theorem fsTraced_stripS_eq (keep : BitVec 64 → Bool)
    (isFs : TraceEvent → Prop) (s0 sf : State) :
    FsTraced isFs (stripS keep s0) (stripS keep sf) = FsTraced isFs s0 sf := by
  cases s0; cases sf; rfl

private theorem specStripSInvariant_writeStdoutCore [LibsignalPlacement]
    {mmpl : MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat)
    (γ : GhostName) (tp : BitVec 64) :
    SpecStripSInvariant c2KeepWritePreS5 (writeStdoutCoreSpecOf mmpl brkStart lim stk γ tp) where
  pre_eq := fun ⟨_, st⟩ s => by
    dsimp only [writeStdoutCoreSpecOf, withLsRet, writeStdoutHonestCore]
    rw [stripS_r64_eq, stripS_r64_eq, stripS_r64_eq, stripS_sp_eq,
      fineHookRustCliAllocBudget_pool_stripS γ mmpl tp brkStart
        (c2_keepPreS5_mallocng mmpl hMm) lim st s]
  post_eq := fun ⟨_, st⟩ _ sf => by
    dsimp only [writeStdoutCoreSpecOf, withLsRet, writeStdoutHonestCore]
    congr 1; funext _
    rw [stripS_r64_eq, stripS_fs_eq, stripS_fs_eq, stripS_trace_eq, stripS_trace_eq, stripS_sp_eq,
      fineHookRustCliAllocBudget_pool_stripS γ mmpl tp brkStart
        (c2_keepPreS5_mallocng mmpl hMm) lim _ sf]
  onPanic_eq := fun _ _ _ => rfl
  onExit_eq := fun _ _ _ _ => rfl
  onOom_eq := fun _ _ _ => rfl

private theorem writeStdoutCore_pre_setPC [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat)
    (γ : GhostName) (tp : BitVec 64)
    (y : WriteStdoutGhost × fineCostModel.σ) (s : State) (pc : BitVec 64) :
    (writeStdoutCoreSpecOf mmpl brkStart lim stk γ tp).pre y (s.setPC pc) =
      (writeStdoutCoreSpecOf mmpl brkStart lim stk γ tp).pre y s := by
  rcases y with ⟨_, _⟩
  cases s; rfl

private theorem writeStdoutCore_outcome_setPC [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat)
    (γ : GhostName) (tp : BitVec 64)
    (y : WriteStdoutGhost × fineCostModel.σ) (R : SepProp) (s0 sf : State) (pc : BitVec 64)
    (h : SubroutineOutcome (writeStdoutCoreSpecOf mmpl brkStart lim stk γ tp) y R
      (s0.setPC pc) sf) :
    SubroutineOutcome (writeStdoutCoreSpecOf mmpl brkStart lim stk γ tp) y R s0 sf := by
  rcases y with ⟨_, _⟩
  cases s0; cases sf; exact h

private theorem writeStdoutCore_outEffects [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat)
    (γ : GhostName) (tp : BitVec 64)
    (y : WriteStdoutGhost × fineCostModel.σ) (R : SepProp) (s0 sf : State)
    (hout : SubroutineOutcome (writeStdoutCoreSpecOf mmpl brkStart lim stk γ tp) y R s0 sf) :
    Returned s0 sf ∧ sf.fs = s0.fs ∧ sf.fs.fds = s0.fs.fds ∧ FsTraced IsFsC s0 sf := by
  rcases y with ⟨x, _⟩
  rcases hout with ⟨hret, _, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · dsimp only [writeStdoutCoreSpecOf, withLsRet, writeStdoutHonestCore] at hpost
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨_, hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    have htr : sf.trace = s0.trace ++ TraceEvent.ofBytes .stdout x.bs := hpost.1.2.2.2.2.2.1
    have hfs : sf.fs = s0.fs := hpost.1.2.2.2.2.2.2
    exact ⟨hret, hfs, congrArg FsState.fds hfs,
      ⟨TraceEvent.ofBytes .stdout x.bs, htr, fun _ => congrArg FsState.files hfs⟩⟩
  · dsimp only [writeStdoutCoreSpecOf, withLsRet, writeStdoutHonestCore] at hpan
    rw [satisfies_pure_sepConj] at hpan; exact False.elim hpan.1
  · dsimp only [writeStdoutCoreSpecOf, withLsRet, writeStdoutHonestCore] at hex
    rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · dsimp only [writeStdoutCoreSpecOf, withLsRet, writeStdoutHonestCore] at hoom
    rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

private theorem writeStdout_preS5_ok [LibsignalPlacement]
    {mmpl : MultiPlacement} {brkStart : BitVec 64} {lim : BudgetLimits} {stk : Nat}
    (hEnf : lim.enforced = true)
    (γ : GhostName) (tp : BitVec 64) :
    subroutine_ok f3PreS5RxProg (signalSessionIoMultiLib.resolve c2CliIoMpl cliIoWriteStdoutSym)
      (signalSessionIoMultiLib.withCodeLoaded c2CliIoMpl
        (withVmPreserved (writeStdoutCoreSpecOf mmpl brkStart lim stk γ tp))) := by
  have hwrite_musl :=
    muslWriteStdout32_of_where9_ok c2MuslSysMpl_placeable f3PreS5RxProg_no_ext f3PreS5RxProg_svc
      (fun _ hPre => c2_muslSys_codeLoadedWhere9_of_preS5 hPre)
  rw [← c2_cliIo_resWrite_fnAddr] at hwrite_musl
  have hwcl :=
    cliIoWriteStdout_honest_withCodeLoaded_ok
      (fineHookPoolErrnoSplit γ mmpl tp brkStart) lim c2CliIoMpl_placeable (stk := stk)
      (CliIoBlockNoExtern.of_no_extern f3PreS5RxProg_no_ext 2) hwrite_musl hEnf
  exact subroutine_ok_withCodeLoaded_withLsRet hwcl

private theorem specStripSInvariant_writeFileCore [LibsignalPlacement]
    {mmpl : MultiPlacement}
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat)
    (γ : GhostName) (tp : BitVec 64) :
    SpecStripSInvariant c2KeepWritePreS5 (writeFileCoreSpecOf mmpl brkStart lim stk γ tp) where
  pre_eq := fun ⟨_, st⟩ s => by
    dsimp only [writeFileCoreSpecOf, withLsRet, writeFileHonestCore]
    rw [stripS_r64_eq, stripS_r64_eq, stripS_r64_eq, stripS_r64_eq, stripS_r64_eq,
      stripS_fs_eq, stripS_sp_eq,
      fineHookRustCliAllocBudget_pool_stripS γ mmpl tp brkStart
        (c2_keepPreS5_mallocng mmpl hMm) lim st s]
  post_eq := fun ⟨_, st⟩ _ sf => by
    dsimp only [writeFileCoreSpecOf, withLsRet, writeFileHonestCore]
    congr 1; funext _
    rw [stripS_r64_eq, stripS_fs_eq, stripS_fs_eq, stripS_trace_eq, stripS_trace_eq,
      fsTraced_stripS_eq, stripS_sp_eq,
      fineHookRustCliAllocBudget_pool_stripS γ mmpl tp brkStart
        (c2_keepPreS5_mallocng mmpl hMm) lim _ sf]
  onPanic_eq := fun _ _ _ => rfl
  onExit_eq := fun _ _ _ _ => rfl
  onOom_eq := fun _ _ _ => rfl

private theorem writeFileCore_pre_setPC [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat)
    (γ : GhostName) (tp : BitVec 64)
    (y : WriteFileGhost × fineCostModel.σ) (s : State) (pc : BitVec 64) :
    (writeFileCoreSpecOf mmpl brkStart lim stk γ tp).pre y (s.setPC pc) =
      (writeFileCoreSpecOf mmpl brkStart lim stk γ tp).pre y s := by
  rcases y with ⟨_, _⟩
  cases s; rfl

private theorem writeFileCore_outcome_setPC [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat)
    (γ : GhostName) (tp : BitVec 64)
    (y : WriteFileGhost × fineCostModel.σ) (R : SepProp) (s0 sf : State) (pc : BitVec 64)
    (h : SubroutineOutcome (writeFileCoreSpecOf mmpl brkStart lim stk γ tp) y R
      (s0.setPC pc) sf) :
    SubroutineOutcome (writeFileCoreSpecOf mmpl brkStart lim stk γ tp) y R s0 sf := by
  rcases y with ⟨_, _⟩
  cases s0; cases sf; exact h

private theorem writeFileCore_outEffects [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat)
    (γ : GhostName) (tp : BitVec 64)
    (y : WriteFileGhost × fineCostModel.σ) (R : SepProp) (s0 sf : State)
    (hout : SubroutineOutcome (writeFileCoreSpecOf mmpl brkStart lim stk γ tp) y R s0 sf) :
    Returned s0 sf ∧ sf.fs.fds = s0.fs.fds ∧ sf.fs.fds = s0.fs.fds ∧ FsTraced IsFsC s0 sf := by
  rcases y with ⟨_, _⟩
  rcases hout with ⟨hret, _, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · dsimp only [writeFileCoreSpecOf, withLsRet, writeFileHonestCore] at hpost
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨_, hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    have hfds : sf.fs.fds = s0.fs.fds := hpost.1.2.2.2.2.1
    have hfst : FsTraced IsFsC s0 sf := hpost.1.2.2.2.2.2.1
    exact ⟨hret, hfds, hfds, hfst⟩
  · dsimp only [writeFileCoreSpecOf, withLsRet, writeFileHonestCore] at hpan
    rw [satisfies_pure_sepConj] at hpan; exact False.elim hpan.1
  · dsimp only [writeFileCoreSpecOf, withLsRet, writeFileHonestCore] at hex
    rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · dsimp only [writeFileCoreSpecOf, withLsRet, writeFileHonestCore] at hoom
    rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

private theorem writeFile_preS5_ok [LibsignalPlacement]
    {mmpl : MultiPlacement} {brkStart : BitVec 64} {lim : BudgetLimits} {stk : Nat}
    (hEnf : lim.enforced = true)
    (γ : GhostName) (tp : BitVec 64) :
    subroutine_ok f3PreS5RxProg (signalSessionIoMultiLib.resolve c2CliIoMpl cliIoWriteFileSym)
      (signalSessionIoMultiLib.withCodeLoaded c2CliIoMpl
        (withVmPreserved (writeFileCoreSpecOf mmpl brkStart lim stk γ tp))) := by
  have hMusl : ∀ m : Memory, f3PreS5RxProg.CodeLoaded m →
      muslSysPlacedLib.CodeLoadedWhere (fun j => decide (j < 9)) c2MuslSysMpl m :=
    fun _ hPre => c2_muslSys_codeLoadedWhere9_of_preS5 hPre
  have hopen := muslOpenCreateTrunc_of_where9_ok c2MuslSysMpl_placeable 3#64
    f3PreS5RxProg_no_ext f3PreS5RxProg_svc hMusl
  have herrno := muslErrnoLocation_of_where9_ok c2MuslSysMpl_placeable
    f3PreS5RxProg_no_ext f3PreS5RxProg_svc hMusl
  have hwrite := muslWriteFile32Clamped_of_where9_ok c2MuslSysMpl_placeable
    f3PreS5RxProg_no_ext f3PreS5RxProg_svc hMusl
  have hclose := muslClose48Local_of_where9_ok c2MuslSysMpl_placeable
    f3PreS5RxProg_no_ext f3PreS5RxProg_svc hMusl
  rw [← c2_cliIo_resOpen_fnAddr] at hopen
  rw [← c2_cliIo_resErrno_fnAddr] at herrno
  rw [← c2_cliIo_resWrite_fnAddr] at hwrite
  rw [← c2_cliIo_resClose_fnAddr] at hclose
  have hwcl_clamped :=
    cliIoWriteFile_budget_withCodeLoaded_ok
      (fineHookPoolErrnoSplit γ mmpl tp brkStart) lim c2CliIoMpl_placeable stk
      (CliIoBlockNoExtern.of_no_extern f3PreS5RxProg_no_ext 1)
      hopen herrno hwrite hclose hEnf
  have hwcl_sat :
      subroutine_ok f3PreS5RxProg (signalSessionIoMultiLib.resolve c2CliIoMpl cliIoWriteFileSym)
        (signalSessionIoMultiLib.withCodeLoaded c2CliIoMpl
          (writeFileSpecPlacedSat cliIo
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk)) := by
    apply subroutine_ok.of_codeLoaded
    rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp _hLP
    dsimp only [MultiPlacedLib.withCodeLoaded, writeFileSpecPlacedSat, withVmPreserved,
      writeFileHonestCore] at hpre
    have hpre_c :
        s0.mem ⊨
          (signalSessionIoMultiLib.withCodeLoaded c2CliIoMpl
            (writeFileSpecPlacedSatClamped cliIo
              (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk)).pre (x, st) s0 ∗ R := by
      dsimp only [MultiPlacedLib.withCodeLoaded, writeFileSpecPlacedSatClamped, withVmPreserved,
        writeFileHonestCoreClamped]
      exact hpre
    exact hwcl_clamped.mono_outcome (x, st) R s0 hpc hrun hpre_c hsp (fun _ hout => hout)
  exact subroutine_ok_withCodeLoaded_withLsRet hwcl_sat

/-! ## 4. Generic `f3PreS5RxProg → f3TrialRxProg` & `StepsStrictAvoid` Lifters -/

private theorem evalInst_eq_of_svc_eq {P1 P2 : Program} (hsvc : P1.svc = P2.svc)
    (inst : Instr) (s : State) :
    P1.evalInst inst s = P2.evalInst inst s := by
  unfold Program.evalInst execInstWithSvc
  rw [hsvc]

private theorem step_of_externAt_none_svc_eq {P1 P2 : Program} {s1 s2 : State}
    (hsvc : P1.svc = P2.svc)
    (he1 : P1.externAt? s1.pc = none)
    (he2 : P2.externAt? s1.pc = none)
    (h : Step P1 s1 s2) :
    Step P2 s1 s2 := by
  have hfm : P2.fetchMem s1.mem s1.pc = P1.fetchMem s1.mem s1.pc :=
    h2fsgen_fetchMem_eq_of_externAt_eq s1.mem s1.pc (he2.trans he1.symm)
  cases h with
  | @exec inst hrun hfm1 =>
    rw [evalInst_eq_of_svc_eq hsvc inst s1]
    exact Step.exec hrun (hfm.trans hfm1)
  | halt_unmapped hrun hfm1 _ =>
    exact Step.halt_unmapped hrun (hfm.trans hfm1) he2
  | extern _ he _ _ => rw [he1] at he; cases he
  | extern_fault _ he _ => rw [he1] at he; cases he

private theorem stepsUntil_preS5_to_trial {stop : State → Prop} {sa sf : State}
    (h : StepsUntil f3PreS5RxProg stop sa sf) :
    StepsUntil f3TrialRxProg stop sa sf := by
  induction h with
  | refl s => exact .refl s
  | @step s1 s2 _ hnot h1 _ ih =>
    exact .step hnot
      (step_of_externAt_none_svc_eq
        (f3PreS5RxProg_svc.trans f3TrialRxProg_svc.symm)
        (f3PreS5RxProg_no_ext s1.pc) (f3TrialRxProg_no_ext s1.pc) h1)
      ih

private theorem cliProgExtPlacedAt_svc (mpl : MultiPlacement)
    (ext : CliHooks → String → Option (State → State)) (idx : Nat) (W : CliHooks) :
    (cliProgExtPlacedAt mpl ext idx W).svc = Syscall.standard :=
  rfl

private theorem stepsStrictAvoid_s5_of_visitedIn_preS5
    {mpl mmpl : MultiPlacement} {W : CliHooks} {sa sf : State}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hvis : h2fsgen_StepsVisitedIn c2KeepWritePreS5 f3PreS5RxProg sa sf) :
    StepsStrictAvoid
      (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve mpl))
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      sa sf := by
  induction hvis with
  | refl s => exact .refl s
  | @step s1 s2 _ hk h1 _ ih =>
    have hnb : s1.pc ∉ mlkemSampleNttSyms.map (libsignalSessionLib.resolve mpl) :=
      c2KeepWritePreS5_not_mem_s5 hLs hk
    have hstep_real : Step (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) s1 s2 :=
      step_of_externAt_none_svc_eq
        (f3PreS5RxProg_svc.trans (cliProgExtPlacedAt_svc mpl (cliExternsPlaced mmpl) 617 W).symm)
        (f3PreS5RxProg_no_ext s1.pc)
        (c2_writePreS5_realNoExt hLs W s1.pc hk) h1
    exact .step hnb hstep_real ih

private theorem setPC_eq_self_of_pc_eq {u : State} {pc : BitVec 64} (hpc : u.pc = pc) :
    u.setPC pc = u := by
  cases u
  dsimp only [State.setPC] at hpc ⊢
  subst hpc
  rfl

/-! ## 5. Exported `StepsStrictAvoid` Theorems for ExtraWide Rows 4–5 -/

/-- `StepsStrictAvoid` of `mlkemSampleNttSyms` for `c2WriteStdoutGhost` (`lsWriteStdoutSym`). -/
theorem c2_writeStdoutGhost_avoidS5 [LibsignalPlacement]
    {mpl mmpl : MultiPlacement} {W : CliHooks}
    {brkStart : BitVec 64} {lim : BudgetLimits} {stk : Nat}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hLsLsmpl : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hEnf : lim.enforced = true := by decide)
    {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsWriteStdoutSym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (c2WriteStdoutGhost mmpl brkStart lim stk u).status ≠ .Exception msg)
    (hfr : ExecFrozen u.mem)
    (hinv : F3CodeInv mpl mmpl u.mem) :
    StepsStrictAvoid
      (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve mpl))
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      u
      (c2WriteStdoutGhost mmpl brkStart lim stk u) := by
  classical
  have hAct0 : ActiveF3CallPre (writeStdoutCoreSpecOf mmpl brkStart lim stk) u :=
    writeIoLinkedGhost_activePre_of_noException hnoex
  rcases hAct0 with ⟨_, hsp, γ, tp, y, R, hpre⟩
  have hAct : ActiveF3CallPre (writeStdoutCoreSpecOf mmpl brkStart lim stk) u :=
    ⟨hrun, hsp, γ, tp, y, R, hpre⟩
  have hlr : LsRetAddr624 (u.readReg64 .lr) := (extract_withLsRet hpre).1
  obtain ⟨sf, huntil_pre, hvis_pre, hstop_sf, _, hFsPres, hFsT, hVm, hfr_sf⟩ :=
    writeIo_elim_stripS f3PreS5RxProg_svc f3PreS5RxProg_no_ext
      (writeStdout_preS5_ok hEnf γ tp)
      (specStripSInvariant_writeStdoutCore hMm brkStart lim stk γ tp)
      (writeStdoutCore_pre_setPC mmpl brkStart lim stk γ tp)
      (writeStdoutCore_outcome_setPC mmpl brkStart lim stk γ tp)
      (writeStdoutCore_outEffects mmpl brkStart lim stk γ tp)
      hrun hsp hpre hfr
      (c2_writePreS5_lr_out hLsLsmpl _ hlr)
      (f3PreS5RxProg_codeLoaded_strip hinv)
      (c2_cliIo_codeLoaded_strip_preS5 hLs hinv)
  have hReal_wide :
      ActiveWriteIoRun c2KeepWriteIo f3WriteLoRxProg c2CliIoMpl
        (signalSessionIoMultiLib.resolve c2CliIoMpl cliIoWriteStdoutSym)
        (fun s0 s1 => s1.fs = s0.fs) u :=
    ⟨hfr, c2_writeIo_lr_out hLsLsmpl _ hlr,
      c2_writeIo_invCodeSub (fun _ h => h) u hfr hinv,
      c2_writeIo_invCodeIo hLs (fun _ h => h) u hfr hinv,
      sf, f3PreS5RxProg_eq_writeLo ▸ huntil_pre, hstop_sf, hFsPres, hFsT, hVm, hfr_sf⟩
  have hEq : c2WriteStdoutGhost mmpl brkStart lim stk u = sf := by
    unfold c2WriteStdoutGhost writeStdoutGhost writeIoLinkedGhost
    simp only [hAct, hReal_wide, ↓reduceDIte]
    have hchoose := Classical.choose_spec hReal_wide.2.2.2.2
    exact h2fsgen_stepsUntil_det hchoose.1 hchoose.2.1
      (f3PreS5RxProg_eq_writeLo ▸ huntil_pre) hstop_sf
  rw [hEq]
  have hset :
      u.setPC (signalSessionIoMultiLib.resolve c2CliIoMpl cliIoWriteStdoutSym) = u :=
    setPC_eq_self_of_pc_eq (hpc.trans (c2_resolve_writeStdout_resolve hLs))
  rw [hset] at hvis_pre
  exact stepsStrictAvoid_s5_of_visitedIn_preS5 hLs hvis_pre

/-- `StepsStrictAvoid` of `mlkemSampleNttSyms` for `c2WriteFileGhost` (`lsWriteFileSym`). -/
theorem c2_writeFileGhost_avoidS5 [LibsignalPlacement]
    {mpl mmpl : MultiPlacement} {W : CliHooks}
    {brkStart : BitVec 64} {lim : BudgetLimits} {stk : Nat}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hLsLsmpl : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hEnf : lim.enforced = true := by decide)
    {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsWriteFileSym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (c2WriteFileGhost mmpl brkStart lim stk u).status ≠ .Exception msg)
    (hfr : ExecFrozen u.mem)
    (hinv : F3CodeInv mpl mmpl u.mem) :
    StepsStrictAvoid
      (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve mpl))
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      u
      (c2WriteFileGhost mmpl brkStart lim stk u) := by
  classical
  have hAct0 : ActiveF3CallPre (writeFileCoreSpecOf mmpl brkStart lim stk) u :=
    writeIoLinkedGhost_activePre_of_noException hnoex
  rcases hAct0 with ⟨_, hsp, γ, tp, y, R, hpre⟩
  have hAct : ActiveF3CallPre (writeFileCoreSpecOf mmpl brkStart lim stk) u :=
    ⟨hrun, hsp, γ, tp, y, R, hpre⟩
  have hlr : LsRetAddr624 (u.readReg64 .lr) := (extract_withLsRet hpre).1
  obtain ⟨sf, huntil_pre, hvis_pre, hstop_sf, _, hFsPres, hFsT, hVm, hfr_sf⟩ :=
    writeIo_elim_stripS f3PreS5RxProg_svc f3PreS5RxProg_no_ext
      (writeFile_preS5_ok hEnf γ tp)
      (specStripSInvariant_writeFileCore hMm brkStart lim stk γ tp)
      (writeFileCore_pre_setPC mmpl brkStart lim stk γ tp)
      (writeFileCore_outcome_setPC mmpl brkStart lim stk γ tp)
      (writeFileCore_outEffects mmpl brkStart lim stk γ tp)
      hrun hsp hpre hfr
      (c2_writePreS5_lr_out hLsLsmpl _ hlr)
      (f3PreS5RxProg_codeLoaded_strip hinv)
      (c2_cliIo_codeLoaded_strip_preS5 hLs hinv)
  have hReal_wide :
      ActiveWriteIoRun c2KeepWriteIo f3WriteLoRxProg c2CliIoMpl
        (signalSessionIoMultiLib.resolve c2CliIoMpl cliIoWriteFileSym)
        (fun s0 s1 => s1.fs.fds = s0.fs.fds) u :=
    ⟨hfr, c2_writeIo_lr_out hLsLsmpl _ hlr,
      c2_writeIo_invCodeSub (fun _ h => h) u hfr hinv,
      c2_writeIo_invCodeIo hLs (fun _ h => h) u hfr hinv,
      sf, f3PreS5RxProg_eq_writeLo ▸ huntil_pre, hstop_sf, hFsPres, hFsT, hVm, hfr_sf⟩
  have hEq : c2WriteFileGhost mmpl brkStart lim stk u = sf := by
    unfold c2WriteFileGhost writeFileGhost writeIoLinkedGhost
    simp only [hAct, hReal_wide, ↓reduceDIte]
    have hchoose := Classical.choose_spec hReal_wide.2.2.2.2
    exact h2fsgen_stepsUntil_det hchoose.1 hchoose.2.1
      (f3PreS5RxProg_eq_writeLo ▸ huntil_pre) hstop_sf
  rw [hEq]
  have hset :
      u.setPC (signalSessionIoMultiLib.resolve c2CliIoMpl cliIoWriteFileSym) = u :=
    setPC_eq_self_of_pc_eq (hpc.trans (c2_resolve_writeFile_resolve hLs))
  rw [hset] at hvis_pre
  exact stepsStrictAvoid_s5_of_visitedIn_preS5 hLs hvis_pre

/-- `StepsStrictAvoid` of `mlkemSampleNttSyms` for `c2WriteFileFdsGhost` (`lsWriteFileSym`)
    under `FdsGe3Closed u.fs`. -/
theorem c2_writeFileFdsGhost_avoidS5 [LibsignalPlacement]
    {mpl mmpl : MultiPlacement} {W : CliHooks}
    {brkStart : BitVec 64} {lim : BudgetLimits} {stk : Nat}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hLsLsmpl : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hEnf : lim.enforced = true := by decide)
    {u : State}
    (hFds : FdsGe3Closed u.fs)
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsWriteFileSym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (c2WriteFileFdsGhost mmpl brkStart lim stk u).status ≠ .Exception msg)
    (hfr : ExecFrozen u.mem)
    (hinv : F3CodeInv mpl mmpl u.mem) :
    StepsStrictAvoid
      (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve mpl))
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      u
      (c2WriteFileFdsGhost mmpl brkStart lim stk u) := by
  have hEq : c2WriteFileFdsGhost mmpl brkStart lim stk u =
      c2WriteFileGhost mmpl brkStart lim stk u :=
    writeFileFdsGhost_eq_of_fds c2KeepWriteIo f3WriteLoRxProg c2CliIoMpl mmpl brkStart lim stk hFds
  rw [hEq] at hnoex ⊢
  exact c2_writeFileGhost_avoidS5 hLs hLsLsmpl hMm hEnf hpc hrun hnoex hfr hinv

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraWideWrite
