/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAuxSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.CoupledCompress256Sat -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore
public import LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Kdf.FinalizeFixedGen
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOk
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixedSat -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAux
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.CompressAndDigest
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.Placed.GenLsBlock
public import LibsignalBinary.Proofs.SpqrV1.Kdf.FinalizeFixed -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Kdf.FrameROExt
import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSlice
import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSliceGen
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Expand
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandCommon
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixedExt
import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
import ProofLib.SepLogic.HeapIntro
import VerifiedLibraries.RustStd.Proofs.ExecSegSym
public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExpand -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.CodeLayout

/-!
# `RunsToVm` & `stripS` Lifting Helpers for `HkdfToSliceOkBudgetSat` (`HkdfToSliceOkBudgetVmSat`)

Provides `RunsToVm`, single-block `memset`-free lifting onto Block `379` (`lift_block_to_379_vm`),
and `stripS` / `unstrip` frame invariance lemmas shared across `HkdfToSliceOkBudgetFinSat` and
`HkdfToSliceOkBudgetSat`.
-/

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetVmSat

open Arm64 ProofLib
open Arm64.Obj (MultiPlacedLib MultiPlacement PlacedLib)
open CryptoGames.HKDF (hkdfExpand)
open CryptoGames.HMAC (ShaState chunks64 hmacWith sha256IV toBEBytes)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
   blkLib_379 blkLib_402 blkLib_425 blkLib_eq_379 blkLib_eq_402 blkLib_eq_425
   blkPC_378 blkPC_379 blkPC_402 blkPC_425 blkPl_378 blkPl_379 blkPl_402 blkPl_425
   libsignalMutatedBlocks libsignalSessionLib
   lsProg_402 ls_externAt?_blockProgram_eq_of_externs_eq ls_externAt?_of_mem lsmpl lsρ)
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister toLEBytes)
open CryptoVerification.LibsignalAesCbc.Run.Bytes
  (readBytes_add readBytes_writeBytes_disjoint readBytes_writeBytes_same)
open CryptoVerification.LibsignalHmac (compress256Hook readShaState shaStateBytes)
open CryptoVerification.LibsignalSession.CryptoHmacSha256
  (disjointRegions_of_ro_rw length_hmacWith)
open CryptoVerification.LibsignalSpqrV1 (hkdfExtractBytes spqrHkdfWith)
open CryptoVerification.LibsignalTripleRatchet
  (CalleeSaved CallingConventionPreserved_of_calleeSaved FinSaved Frame
   HkdfPlacedHooks HmacSt LibsignalCodeRoLoaded RW RunsTo RunsToFrom TraceEq
   agreesOutside_seg2a agreesOutside_seg3a agreesOutside_seg4a
   digestBytes digestBytes_eq_append extHookStack extract_withLsCodeRoLoaded
   finSaved_seg3a finSaved_seg4a frame_seg2a frame_seg3a frame_seg4a fsp_aligned
   hmacInnerInit hmacOuterInit keys_ls_subroutine_ok_of_block_cro
   compress256Hook_eq lsCompress256Sym lsMemcpySym lsMemsetSym noAllocShimSpec
   outerBlock outerBlock_digestBytes_length
   read32_words_at_104_of_shaStateBytes read32_words_at_64_of_shaStateBytes
   read64_seg2a_mid read64_seg3a_pad_32 read64_seg3a_pad_40
   readBytes_56_eq_append_8 readBytes_56_of_buf_eq readBytes_fsp_64_seg2 readBytes_fsp_64_seg3
   readBytes_write32_8_digestBytes ro_outside_rw_shared_lb rw_of_perm_eq
   sessionMemsetRegionSpec shaStateBytes_length
   toLEBytes_4_rev32 toLEBytes_8_read64 toLEBytes_8_rev32_append toLEBytes_8_rev64
   truncate8_truncate32 ult_7_of_lt_56 withLsCodeRoLoaded xor_63_of_lt_64
   zeroExtend64_ofNat8 zeroExtend64_truncate32_ofNat64)
open CryptoVerification.LibsignalTripleRatchet.Expand
  (hkdfExpand_64_eq t1_length t2_length t3_length)
open CryptoVerification.LibsignalTripleRatchet.Extract
  (CallingConventionPreserved.x19 CallingConventionPreserved.x20
   CallingConventionPreserved.x21 CallingConventionPreserved.x22
   CallingConventionPreserved.x27 CallingConventionPreserved.x29 S2Frame
   disjoint_fullComplementHeap fullComplementHeap matches_fullComplementHeap)
open CryptoVerification.LibsignalTripleRatchet.HkdfExt
  (AgreesOn AgreesOn.finSaved_of AgreesOn.read64_eq AgreesOn.readBytes_eq)
open CryptoVerification.SpqrV1.Alloc (spqrRustNoAllocShimSym)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt hkdfToSliceSpec hkdfToSliceSpqrSpec)
open CryptoVerification.SpqrV1.Kdf
  (FinPre3 FinPre3Pfx FinPre3PfxGen HmacStN
   bit_len_innerN_eq bit_len_innerN_eq_lt64 effectiveHmacKey effectiveHmacKey_length_le
   effectiveHmacKey_of_le fin3PlacedFakeB fin3PlacedFakeB_off_0
   hmacWith_effectiveHmacKey hmacWith_pfx_short hmacWith_pfx_two_blocks
   innerLastBlockN innerLastBlockN_length innerPadBlock1 innerPadBlock1_length
   innerPadBlock2 innerPadBlock2_length read64_fsp32_hm readBytes_64_eq_append_8
   readBytes_fsp_64_copy spqrRustAllocZeroedSym toLEBytes_8_zero_7 ult_7_of_ge_56)
open CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof
  (HCommon HExpCommon HFrame HPost HPre HSaved
   StateB1Done StateB1Fin StateB1RetFin StateDone
   StateEFin StateENfs1 StateENfs2 StateERet1 StateERet2 StateERetFin StateExtractDone
   StateLoop StateLoopC StateLoopFin
   b1_done_32_placed_runsTo b1_to_loop_placed_runsTo epilogue_placed_runsTo
   hkdfCodeFakeB hkdfExpand_32_eq hkdfExpand_96_eq hsp hsp_aligned
   iter_a1_placed_runsTo iter_a2_placed_runsTo iter_b_placed_runsTo
   iter_d_continue_placed_runsTo iter_d_done_placed_runsTo rodata_sha256IV_placed
   seg_b1a_placed_runsTo seg_b1b_placed_runsTo seg_b1d_placed_runsTo
   seg_e0_placed_runsTo seg_e1_placed_runsTo seg_e1d_placed_runsTo
   seg_e2_placed_runsTo seg_e3_placed_runsTo)
open CryptoVerification.SpqrV1.Kdf.NewFromSlice3Proof
  (new_from_slice3_placed_run nfs3PlacedFakeB nfs3PlacedFakeB_add_iv spqrSha256IVAddr)
open CryptoVerification.SpqrV1.Kdf.SpqrKdfExt (disjointRegions_of_outside)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.MuslMemOpsRunsTo (MemcpyClobber applyMemcpyClobber)
open LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAux
  (stripExecOutside_readBytes stripExecOutside_readable stripExecOutside_rw unstrip_frame)
open LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAuxSat
  (blockProgram_allInstrs_not_isMsrTpidrEl0 checkBlockNoMsrTpidrEl0
   hookOk_sessionMemsetRegionBudget_elim)
open LibsignalBinary.Proofs.ConsumeMessageKey.CoupledCompress256Sat
  (hmacNoMemsetExcHooksSat steps_hmacNoMemsetExcSat_lift_strip_allocVm)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps
  (vmPreserved_refl_iff vmPreserved_setMem_writeBytes vmPreserved_setPC)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore
  (HookExactMemcpy HookSatExactMemcpy applyMemcpyClobber_ofState_eq)
open LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget
  (allocCallPreserved_trans withAllocVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
  (CallingConventionPreserved.x23 CallingConventionPreserved.x24
   CallingConventionPreserved.x25 CallingConventionPreserved.x26
   CallingConventionPreserved.x28 HkdfPlacedHooksExactSat HkdfPlacedHooksSat
   vmPreserved_applyMemcpyClobber_writeBytes)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixedSat (FinCommonSat FinPostSat)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemsetRegionBudgetSpec)
open VerifiedLibraries.RustStd (blockProgram_rebase_allInstrs_not_isSvc0)

attribute [local arm64_norm] MemWidth.bytes SimdMemSize.bytes

open CryptoVerification.LibsignalTripleRatchet.FinalizeFixedProof (FinCommon FinPost)

/-! ## 2. `RunsToVm` & Single-Block `memset`-Free Lifting onto Block `379` -/

abbrev ProgMemsetAllocVm [LibsignalPlacement] (P : Program) : Prop :=
  ∃ f : State → State,
    P.externAt? (lsρ lsMemsetSym) = some f ∧
    HookOk f (withAllocVmPreserved sessionMemsetRegionSpec)

theorem allocCallPreserved_refl (s : State) : AllocCallPreserved s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

abbrev RunsToVm [LibsignalPlacement] (P : Program) (s : State) (Q : State → Prop) : Prop :=
  P.CodeLoaded s.mem →
  ∃ sf : State,
    Steps P s sf ∧ VmPreserved s sf ∧
    (ProgMemsetAllocVm P → AllocCallPreserved s sf) ∧
    sf.trace = s.trace ∧
    calleeSavedVRegs sf = calleeSavedVRegs s ∧ Q sf ∧ P.CodeLoaded sf.mem

theorem RunsToVm.refl [LibsignalPlacement] {P : Program} {s : State} {Q : State → Prop}
    (hq : Q s) : RunsToVm P s Q :=
  fun hL => ⟨s, .refl s, VmPreserved.refl s, fun _ => allocCallPreserved_refl s, rfl, rfl, hq, hL⟩

theorem RunsToVm.mono [LibsignalPlacement] {P : Program} {s : State} {Q1 Q2 : State → Prop}
    (h : RunsToVm P s Q1) (himp : ∀ sf, Q1 sf → Q2 sf) :
    RunsToVm P s Q2 :=
  fun hL =>
    let ⟨sf, hst, hvm, hacp, htr, hv, hq, hLf⟩ := h hL
    ⟨sf, hst, hvm, hacp, htr, hv, himp sf hq, hLf⟩

theorem RunsToVm.trans_full [LibsignalPlacement] {P : Program} {s : State} {Q1 Q2 : State → Prop}
    (h1 : RunsToVm P s Q1)
    (h2 : ∀ s1, Q1 s1 → s.mem.KeepsFrozen s1.mem → RunsToVm P s1 Q2) :
    RunsToVm P s Q2 :=
  fun hL =>
    let ⟨s1, hst1, hvm1, hacp1, htr1, hv1, hq1, hL1⟩ := h1 hL
    let ⟨s2, hst2, hvm2, hacp2, htr2, hv2, hq2, hL2⟩ := h2 s1 hq1 hst1.keepsFrozen hL1
    ⟨s2, hst1.trans hst2, hvm1.trans hvm2,
      fun hms => allocCallPreserved_trans (hacp1 hms) (hacp2 hms),
      htr2.trans htr1, hv2.trans hv1, hq2, hL2⟩



private theorem strip_codeLoaded_of_keep_vm {prog : Program} {m : Memory} (hL : prog.CodeLoaded m) :
    prog.CodeLoaded (ProofLib.stripExecOutside (ProofLib.progKeep prog) m) := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun k hk => ?_
  have hno := hL.no_wrap
  have hsub : prog.base + BitVec.ofNat 64 k - prog.base = BitVec.ofNat 64 k := by bv_omega
  have hkeep : ProofLib.progKeep prog (prog.base + BitVec.ofNat 64 k) = true := by
    unfold ProofLib.progKeep
    rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact decide_eq_true hk
  rw [ProofLib.strip_read8, ProofLib.strip_perm_of_keep hkeep, ProofLib.strip_isLazyFree]
  exact ⟨hL.byte_eq k hk, hL.perm_eq k hk, hL.isLazyFree_eq k hk⟩

theorem blk379_noSvc0 :
    VerifiedLibraries.RustStd.checkBlockNoSvc0 blkLib_379.text = true := by decide +kernel
theorem blk379_noMsr :
    checkBlockNoMsrTpidrEl0 blkLib_379.text = true := by decide +kernel
theorem blk402_noSvc0 :
    VerifiedLibraries.RustStd.checkBlockNoSvc0 blkLib_402.text = true := by decide +kernel
theorem blk402_noMsr :
    checkBlockNoMsrTpidrEl0 blkLib_402.text = true := by decide +kernel
theorem blk425_noSvc0 :
    VerifiedLibraries.RustStd.checkBlockNoSvc0 blkLib_425.text = true := by decide +kernel
theorem blk425_noMsr :
    checkBlockNoMsrTpidrEl0 blkLib_425.text = true := by decide +kernel

theorem lift_block_to_379_vm [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [hH : HkdfPlacedHooksExactSat C.F H]
    {j : Nat} {blkLib : PlacedLib} {Pj : Program} [hcallee : IsLsBlockProg Pj j H]
    (hlib : blkLib = libsignalSessionLib.blockLib j)
    (hchk_svc : VerifiedLibraries.RustStd.checkBlockNoSvc0 blkLib.text = true)
    (hchk_msr : checkBlockNoMsrTpidrEl0 blkLib.text = true)
    (hj_lt : j < 619) (hj_unmut : (j ∈ libsignalMutatedBlocks) = false)
    {s : State} {PostP PostQ : State → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hrunsP : RunsTo (libsignalSessionLib.blockProgram lsmpl j H) s PostP)
    (hrunsQ : RunsTo
      (libsignalSessionLib.blockProgram lsmpl j
        (hmacNoMemsetExcHooksSat C.F H s.mem
          (ProofLib.progKeep (libsignalSessionLib.blockProgram lsmpl j H))))
      (ProofLib.stripS (ProofLib.progKeep
        (libsignalSessionLib.blockProgram lsmpl j
          (hmacNoMemsetExcHooksSat C.F H s.mem
            (ProofLib.progKeep (libsignalSessionLib.blockProgram lsmpl j H))))) s) PostQ)
    (hrunP : ∀ s', PostP s' → s'.status = .Running)
    (hrunQ : ∀ s', PostQ s' → s'.status = .Running)
    (hunstrip : ∀ sf, VmPreserved s sf →
      PostQ (ProofLib.stripS (ProofLib.progKeep
        (libsignalSessionLib.blockProgram lsmpl j
          (hmacNoMemsetExcHooksSat C.F H s.mem
            (ProofLib.progKeep (libsignalSessionLib.blockProgram lsmpl j H))))) sf) → PostP sf) :
    RunsToVm ((blkPC_379).rebase (blkPl_379).base H) s PostP := by
  subst hlib
  intro hL379
  let kp := ProofLib.progKeep (libsignalSessionLib.blockProgram lsmpl j H)
  let Q := libsignalSessionLib.blockProgram lsmpl j (hmacNoMemsetExcHooksSat C.F H s.mem kp)
  have hLj : (libsignalSessionLib.blockProgram lsmpl j H).CodeLoaded s.mem :=
    hcl j (Nat.lt_trans hj_lt (by decide)) hj_unmut H (fun _ => none) Syscall.standard
  have hall_svc : Q.allInstrs (fun ins => !ins.isSvc0) = true :=
    blockProgram_rebase_allInstrs_not_isSvc0 libsignalSessionLib lsmpl j hchk_svc
  have hall_msr : Q.allInstrs (fun ins => !ins.isMsrTpidrEl0) = true :=
    blockProgram_allInstrs_not_isMsrTpidrEl0 libsignalSessionLib lsmpl j
      (hmacNoMemsetExcHooksSat C.F H s.mem kp) hchk_msr
  have hLQ : Q.CodeLoaded s.mem := hLj.of_base_code rfl rfl
  have hLQ_strip : Q.CodeLoaded (ProofLib.stripS (ProofLib.progKeep Q) s).mem := by
    have hm : (ProofLib.stripS (ProofLib.progKeep Q) s).mem =
        ProofLib.stripExecOutside (ProofLib.progKeep Q) s.mem := by cases s; rfl
    rw [hm]; exact strip_codeLoaded_of_keep_vm hLQ
  obtain ⟨sfP, hstepsP, ⟨htrP, hvregsP⟩, hPostP, _⟩ := hrunsP hLj
  obtain ⟨sf', hstepsQ, ⟨htr', hvregs'⟩, hPost', _⟩ := hrunsQ hLQ_strip
  obtain ⟨sf, hst_j, hvm, hacp, hsf_eq | rfl⟩ :=
    steps_hmacNoMemsetExcSat_lift_strip_allocVm libsignalSessionLib lsmpl j hH.memcpy hH.compress256
      s.mem hall_svc hall_msr hstepsQ (hrunQ sf' hPost') s sfP rfl (fun _ => rfl) hLQ hstepsP
      (hrunP sfP hPostP)
  · have htr : sf.trace = s.trace := by
      have h1 : sf'.trace = sf.trace := by rw [hsf_eq]; cases sf; rfl
      have h2 : (ProofLib.stripS (ProofLib.progKeep Q) s).trace = s.trace := by cases s; rfl
      exact h1.symm.trans (htr'.trans h2)
    have hvregs : calleeSavedVRegs sf = calleeSavedVRegs s := by
      have h1 : calleeSavedVRegs sf' = calleeSavedVRegs sf := by rw [hsf_eq]; cases sf; rfl
      have h2 : calleeSavedVRegs (ProofLib.stripS (ProofLib.progKeep Q) s) = calleeSavedVRegs s := by
        cases s; rfl
      exact h1.symm.trans (hvregs'.trans h2)
    have hPost : PostP sf := hunstrip sf hvm (hsf_eq ▸ hPost')
    have hcaller : IsLsBlockProg ((blkPC_379).rebase (blkPl_379).base H) 379 H := inferInstance
    have hext : ∀ pc, (libsignalSessionLib.blockProgram lsmpl j H).externAt? pc =
        ((blkPC_379).rebase (blkPl_379).base H).externAt? pc := fun pc => by
      rw [hcaller.eq_blockProgram,
        ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
          (hcallee.externs_eq.trans hcaller.externs_eq.symm)]
    have hsvc : (libsignalSessionLib.blockProgram lsmpl j H).svc =
        ((blkPC_379).rebase (blkPl_379).base H).svc := by rw [hcaller.eq_blockProgram]; rfl
    have hst_379 := Steps.of_sameHooks hext hsvc hst_j
    exact ⟨sf, hst_379, hvm, fun _ => hacp, htr, hvregs, hPost, hst_379.codeLoaded hL379⟩
  · have hcaller : IsLsBlockProg ((blkPC_379).rebase (blkPl_379).base H) 379 H := inferInstance
    have hext : ∀ pc, (libsignalSessionLib.blockProgram lsmpl j H).externAt? pc =
        ((blkPC_379).rebase (blkPl_379).base H).externAt? pc := fun pc => by
      rw [hcaller.eq_blockProgram,
        ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
          (hcallee.externs_eq.trans hcaller.externs_eq.symm)]
    have hsvc : (libsignalSessionLib.blockProgram lsmpl j H).svc =
        ((blkPC_379).rebase (blkPl_379).base H).svc := by rw [hcaller.eq_blockProgram]; rfl
    have hst_379 := Steps.of_sameHooks hext hsvc hst_j
    exact ⟨sf, hst_379, hvm, fun _ => hacp, htrP, hvregsP, hPostP, hst_379.codeLoaded hL379⟩

theorem placed_memset_budget_optAlloc_steps_sat [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h_memset : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec)
    {s : State} {dst lr : BitVec 64} {val : BitVec 8} {len : Nat}
    (hrun : s.status = .Running)
    (hpc : s.pc = lsρ lsMemsetSym)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : (s.readReg64 .x1).truncate 8 = val)
    (hx2 : (s.readReg64 .x2).toNat = len)
    (hlr : s.readReg64 .lr = lr)
    (hsp_al : (s.sp &&& 15#64) = 0#64)
    (hrw : s.mem.RW dst len)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    ∃ s' : State,
      Steps prog s s' ∧
      VmPreserved s s' ∧
      (ProgMemsetAllocVm prog → AllocCallPreserved s s') ∧
      s'.trace = s.trace ∧
      calleeSavedVRegs s' = calleeSavedVRegs s ∧
      s'.pc = lr ∧
      s'.status = .Running ∧
      CallingConventionPreserved s s' ∧
      s'.readReg64 .x0 = dst ∧
      s.mem.KeepsFrozen s'.mem ∧
      s'.mem.readBytes dst len = List.replicate len val ∧
      S2Frame s.mem s'.mem [(dst, len)] ∧
      AgreesOn (fun a => (s.mem.perm a).r = true ∧ s.mem.isLazyFree a = false)
        s'.mem (s.mem.writeBytes dst (List.replicate len val)) := by
  obtain ⟨f, hfH, hfOk⟩ := h_memset
  have hhook : prog.externAt? s.pc = some f := by
    rw [hpc, ls_externAt?_of_mem (by decide) hi hunmut, hfH]
  obtain ⟨hkf, hsym, hret, hcc, hvm, hx0', htr', hread', hs2', hag'⟩ :=
    hookOk_sessionMemsetRegionBudget_elim hfOk hrun hx0 hx1 hx2 hsp_al hrw
  have hacp : ProgMemsetAllocVm prog → AllocCallPreserved s (f s) := by
    rintro ⟨f', hext', hfOk_acp⟩
    have hff' : f' = f := Option.some.inj (hext'.symm.trans (hpc ▸ hhook))
    subst hff'
    have hlen_le : len ≤ 2 ^ 64 := by rw [← hx2]; have := (s.readReg64 .x2).isLt; omega
    let hP : Heap := regionHeap dst len s.mem
    have hpP : (memRegion dst len) hP :=
      ((IsBlock.memRegion dst len).iff hP).mpr ⟨s.mem, trivial, rfl⟩
    have hmP : hP.Matches s.mem := IsBlock.regionHeap_matches dst len s.mem hrw
    let R_comp : SepProp := ⟨fun h => h = fullComplementHeap hP s.mem⟩
    have hsep_pre : s.mem ⊨ memRegion dst len ∗ R_comp :=
      Satisfies.sepConj_intro (disjoint_fullComplementHeap hP s.mem) hpP rfl
        (Heap.Matches.union hmP (matches_fullComplementHeap hP s.mem))
    have hx1_32 : (s.readReg32 .x1).truncate 8 = val := by
      rw [State.readReg32, truncate8_truncate32, hx1]
    have hpre_full : s.mem ⊨
        (withAllocVmPreserved sessionMemsetRegionSpec).pre (dst, val, len) s ∗ R_comp := by
      dsimp only [withAllocVmPreserved, sessionMemsetRegionSpec, memsetRegionSpec]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0, hx1_32, hx2, hlen_le⟩, hsep_pre⟩
    have hsp_aligned : s.spAligned = true := by simpa [State.spAligned] using hsp_al
    obtain ⟨-, -, hout⟩ := hfOk_acp (dst, val, len) R_comp s hrun hpre_full hsp_aligned
    rcases hout with ⟨-, -, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
    · dsimp only [withAllocVmPreserved] at hpost
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
      exact hpost.1.1
    · exact False.elim (not_satisfies_false_sepConj hp)
    · exact False.elim (not_satisfies_false_sepConj he)
    · exact False.elim (not_satisfies_false_sepConj ho)
  exact ⟨f s, .step (Step.extern hrun hhook hkf hsym) (.refl (f s)),
    hvm, hacp, htr', hcc.2.2.2.2.2.2.2.2.2.2.2.2, hret.1.trans hlr, hret.2.2, hcc,
    hx0', hkf, hread', hs2', hag'⟩

theorem mem_setMem (s : State) (m : Memory) : (s.setMem m).mem = m := rfl

@[local simp, local arm64_norm]
theorem extractLsb'_0_64_zero128 : BitVec.extractLsb' 0 64 0#128 = 0#64 := rfl

@[local simp, local arm64_norm]
theorem extractLsb'_64_64_zero128 : BitVec.extractLsb' 64 64 0#128 = 0#64 := rfl

theorem stripS_mem (kp : BitVec 64 → Bool) (s : State) :
    (ProofLib.stripS kp s).mem = ProofLib.stripExecOutside kp s.mem := by cases s; rfl

theorem stripS_read8 (kp : BitVec 64 → Bool) (s : State) (a : BitVec 64) :
    (ProofLib.stripS kp s).mem.read8 a = s.mem.read8 a := by
  cases s; simp [ProofLib.stripS, ProofLib.strip_read8]

theorem stripS_read64 (kp : BitVec 64 → Bool) (s : State) (a : BitVec 64) :
    (ProofLib.stripS kp s).mem.read64 a = s.mem.read64 a := by
  cases s; simp [ProofLib.stripS, Memory.read64, ProofLib.strip_read8]

theorem stripS_readBytes (kp : BitVec 64 → Bool) (s : State) (a : BitVec 64) (n : Nat) :
    (ProofLib.stripS kp s).mem.readBytes a n = s.mem.readBytes a n := by
  rw [stripS_mem, stripExecOutside_readBytes]

theorem stripS_hmacSt (kp : BitVec 64 → Bool)
    {F : ShaState → List (BitVec 8) → ShaState} {s : State} {a : BitVec 64}
    {key msg : List (BitVec 8)} :
    HmacSt (ProofLib.stripS kp s).mem a F key msg ↔ HmacSt s.mem a F key msg := by
  unfold HmacSt
  simp only [stripS_read8, stripS_read64, stripS_readBytes]

theorem stripS_hmacStN (kp : BitVec 64 → Bool)
    {F : ShaState → List (BitVec 8) → ShaState} {s : State} {a : BitVec 64}
    {key pfx tail : List (BitVec 8)} :
    HmacStN (ProofLib.stripS kp s).mem a F key pfx tail ↔ HmacStN s.mem a F key pfx tail := by
  unfold HmacStN
  simp only [stripS_read8, stripS_read64, stripS_readBytes]

theorem stripS_finSaved (kp : BitVec 64 → Bool) (s0 s : State) :
    FinSaved (ProofLib.stripS kp s0) ((ProofLib.stripS kp s0).sp - 144#64)
      (ProofLib.stripS kp s).mem ↔
    FinSaved s0 (s0.sp - 144#64) s.mem := by
  have hsp0 : (ProofLib.stripS kp s0).sp = s0.sp := by cases s0; rfl
  have hr : ∀ r, (ProofLib.stripS kp s0).readReg64 r = s0.readReg64 r := fun _ => by cases s0; rfl
  unfold FinSaved
  simp only [hsp0, hr, stripS_read64]

theorem stripS_hsaved (kp : BitVec 64 → Bool) (s0 s : State) :
    HSaved (ProofLib.stripS kp s0) (ProofLib.stripS kp s).mem ↔ HSaved s0 s.mem := by
  have hsp0 : hsp (ProofLib.stripS kp s0) = hsp s0 := by cases s0; rfl
  have hr : ∀ r, (ProofLib.stripS kp s0).readReg64 r = s0.readReg64 r := fun _ => by cases s0; rfl
  have h64 : ∀ off, (ProofLib.stripS kp s).mem.read64 (hsp (ProofLib.stripS kp s0) + off) =
      s.mem.read64 (hsp s0 + off) := fun off => by rw [hsp0, stripS_read64]
  constructor <;> rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  · rw [h64, hr] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  · exact ⟨by rw [h64, hr]; exact h0, by rw [h64, hr]; exact h1,
      by rw [h64, hr]; exact h2, by rw [h64, hr]; exact h3,
      by rw [h64, hr]; exact h4, by rw [h64, hr]; exact h5,
      by rw [h64, hr]; exact h6, by rw [h64, hr]; exact h7,
      by rw [h64, hr]; exact h8, by rw [h64, hr]; exact h9,
      by rw [h64, hr]; exact h10, by rw [h64, hr]; exact h11⟩

theorem unstrip_s2Frame {p : BitVec 64 → Bool} {m m' : Memory} {rs : List (BitVec 64 × Nat)}
    (hf : S2Frame (ProofLib.stripExecOutside p m) (ProofLib.stripExecOutside p m') rs)
    (hperm : ∀ a, m'.perm a = m.perm a) :
    S2Frame m m' rs := by
  refine ⟨fun a hr hlf hout => ?_,
    ⟨⟨fun a hnl => ?_, fun a hrw => (hperm a).trans hrw⟩,
     ⟨fun a ⟨hm, han⟩ => ?_, fun a hpn hout => ?_⟩⟩,
    fun a hr hlf => ?_⟩
  · simpa only [ProofLib.strip_read8] using
      hf.1 a ((ProofLib.strip_perm_props p m a).1.trans hr)
        ((ProofLib.strip_isLazyFree p m a).trans hlf) hout
  · obtain ⟨hrw, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp hnl
    have hnl' : (ProofLib.stripExecOutside p m).permNoLazy a = some .rw :=
      Memory.permNoLazy_eq_some_rw_iff.mpr
        ⟨(ProofLib.strip_perm_props p m a).2.2.2.mpr hrw,
         (ProofLib.strip_isLazyFree p m a).trans hlf⟩
    obtain ⟨hrw', hlf'⟩ := Memory.permNoLazy_eq_some_rw_iff.mp (hf.2.1.1.1 a hnl')
    exact Memory.permNoLazy_eq_some_rw_iff.mpr
      ⟨(ProofLib.strip_perm_props p m' a).2.2.2.mp hrw',
       (ProofLib.strip_isLazyFree p m' a).symm.trans hlf'⟩
  · obtain ⟨hm', han'⟩ :=
      hf.2.1.2.1 a ⟨(ProofLib.strip_perm_props p m a).2.2.1.trans hm,
        (ProofLib.strip_isAnon p m a).trans han⟩
    exact ⟨(ProofLib.strip_perm_props p m' a).2.2.1.symm.trans hm',
      (ProofLib.strip_isAnon p m' a).symm.trans han'⟩
  · have hpn_s : (ProofLib.stripExecOutside p m).perm a = some Perm.protNone := by
      rw [ProofLib.strip_perm, hpn]
      cases p a <;> rfl
    refine ⟨(hperm a).trans hpn, fun hlf => ?_⟩
    obtain ⟨hr8, hlf'⟩ := (hf.2.1.2.2 a hpn_s hout).2 ((ProofLib.strip_isLazyFree p m a).trans hlf)
    simpa only [ProofLib.strip_read8, ProofLib.strip_isLazyFree] using And.intro hr8 hlf'
  · obtain ⟨hr', hlf'⟩ :=
      hf.2.2 a ((ProofLib.strip_perm_props p m a).1.trans hr)
        ((ProofLib.strip_isLazyFree p m a).trans hlf)
    exact ⟨(ProofLib.strip_perm_props p m' a).1.symm.trans hr',
      (ProofLib.strip_isLazyFree p m' a).symm.trans hlf'⟩

theorem unstrip_finCommon {kp : BitVec 64 → Bool} {s0 s : State}
    (hc : FinCommon (ProofLib.stripS kp s0) (ProofLib.stripS kp s))
    (hperm : ∀ a, s.mem.perm a = s0.mem.perm a) :
    FinCommon s0 s := by
  rcases hc with ⟨hst, hsp_c, hx29, hx26, hx27, hx28, hsav, hfr⟩
  have hr0 : ∀ r, (ProofLib.stripS kp s0).readReg64 r = s0.readReg64 r := fun _ => by cases s0; rfl
  have hsp0 : (ProofLib.stripS kp s0).sp = s0.sp := by cases s0; rfl
  rw [stripS_mem, stripS_mem, hr0, hr0, hsp0] at hfr
  exact ⟨(by cases s; exact hst), (by cases s0; cases s; exact hsp_c),
    (by cases s0; cases s; exact hx29), (by cases s0; cases s; exact hx26),
    (by cases s0; cases s; exact hx27), (by cases s0; cases s; exact hx28),
    (stripS_finSaved kp s0 s).mp hsav, unstrip_frame hfr hperm⟩

theorem unstrip_hcommon {kp : BitVec 64 → Bool} {okmLen : Nat} {s0 s : State}
    (hc : HCommon okmLen (ProofLib.stripS kp s0) (ProofLib.stripS kp s))
    (hperm : ∀ a, s.mem.perm a = s0.mem.perm a) :
    HCommon okmLen s0 s := by
  rcases hc with ⟨hst, hsp_c, hx29, hsav, hfr⟩
  have hr0 : (ProofLib.stripS kp s0).readReg64 .x6 = s0.readReg64 .x6 := by cases s0; rfl
  have hsp0 : hsp (ProofLib.stripS kp s0) = hsp s0 := by cases s0; rfl
  unfold HFrame at hfr
  rw [stripS_mem, stripS_mem, hr0, hsp0] at hfr
  exact ⟨(by cases s; exact hst), (by cases s0; cases s; exact hsp_c),
    (by cases s0; cases s; exact hx29), (stripS_hsaved kp s0 s).mp hsav, unstrip_frame hfr hperm⟩

theorem unstrip_hexpCommon {kp : BitVec 64 → Bool}
    {F : ShaState → List (BitVec 8) → ShaState} {prk info : List (BitVec 8)}
    {infoA : BitVec 64} {okmLen : Nat} {s0 s : State}
    (he : HExpCommon F prk info infoA okmLen (ProofLib.stripS kp s0) (ProofLib.stripS kp s))
    (hperm : ∀ a, s.mem.perm a = s0.mem.perm a) :
    HExpCommon F prk info infoA okmLen s0 s := by
  rcases he with ⟨hc, hm0, hm8, hm16, hm24, hhm⟩
  have hsp0 : hsp (ProofLib.stripS kp s0) = hsp s0 := by cases s0; rfl
  rw [hsp0, stripS_read64] at hm0 hm8 hm16 hm24
  rw [hsp0, stripS_hmacSt] at hhm
  exact ⟨unstrip_hcommon hc hperm, hm0, hm8, hm16, hm24, hhm⟩

theorem stripS_hcommon_refl (kp : BitVec 64 → Bool) {okmLen : Nat} {s0 s : State}
    (hc : HCommon okmLen (s0.setMem s.mem) s) :
    HCommon okmLen (ProofLib.stripS kp (s0.setMem s.mem)) (ProofLib.stripS kp s) := by
  rcases hc with ⟨hst, hsp_c, hx29, hsav, _⟩
  have hmem_eq : (ProofLib.stripS kp (s0.setMem s.mem)).mem = (ProofLib.stripS kp s).mem := by
    cases s0; cases s; rfl
  refine ⟨(by cases s; exact hst), (by cases s0; cases s; exact hsp_c),
    (by cases s0; cases s; exact hx29), (stripS_hsaved kp (s0.setMem s.mem) s).mpr hsav, ?_⟩
  unfold HFrame
  rw [hmem_eq]
  exact Frame.refl _ _

theorem stripS_hexpCommon_refl (kp : BitVec 64 → Bool)
    {F : ShaState → List (BitVec 8) → ShaState} {prk info : List (BitVec 8)}
    {infoA : BitVec 64} {okmLen : Nat} {s0 s : State}
    (he : HExpCommon F prk info infoA okmLen (s0.setMem s.mem) s) :
    HExpCommon F prk info infoA okmLen (ProofLib.stripS kp (s0.setMem s.mem))
      (ProofLib.stripS kp s) := by
  rcases he with ⟨hc, hm0, hm8, hm16, hm24, hhm⟩
  have hsp0 : hsp (ProofLib.stripS kp (s0.setMem s.mem)) = hsp (s0.setMem s.mem) := by
    cases s0; cases s; rfl
  refine ⟨stripS_hcommon_refl kp hc, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsp0, stripS_read64]; exact hm0
  · rw [hsp0, stripS_read64]; exact hm8
  · rw [hsp0, stripS_read64]; exact hm16
  · rw [hsp0, stripS_read64]; exact hm24
  · rw [hsp0, stripS_hmacSt]; exact hhm


end LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetVmSat
