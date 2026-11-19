/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAuxSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.CoupledCompress256Sat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixedSat -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAux
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Transfer
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixedExt
import LibsignalBinary.Proofs.CodeLayout

/-!
# `HookSat` Sibling of `CryptoBridgePlacedBudgetAux`, Part A (`CryptoBridgePlacedBudgetAuxASat`)

Proves `RunsToVm`, single-hook steps, and `VmPreserved` + `S2Frame` execution
(`finalize_fixed_placed_runsToVm_sat`) for `finalize_fixed` (Block `123`, `320`-B stack) under
`[HkdfPlacedHooksExactBudgetSat C.F H]`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetAuxASat

open Arm64 ProofLib SepProp
open CryptoGames.HMAC (ShaState chunks64 hmacWith toBEBytes)
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
   libsignalMutatedBlocks libsignalSessionLib
   ls_externAt?_blockProgram_eq_of_externs_eq
   lsmpl lsρ withLsCodeLoaded)
open CryptoVerification.LibsignalAesCbc (toLEBytes)
open CryptoVerification.LibsignalHmac (shaStateBytes)
open CryptoVerification.LibsignalTripleRatchet
  (CalleeSaved CallingConventionPreserved_of_calleeSaved FinSaved Frame HmacSt
   RW RunsTo RunsToFrom TraceEq agreesOutside_pad_memset agreesOutside_seg2a agreesOutside_seg3a
   agreesOutside_seg4a bit_len_inner_eq blkLib_123 blkLib_eq_123
   blkPC_123 blkPl_123 chunks64_single_foldl
   digestBytes digestBytes_eq_append finPlacedFakeB finPlacedFakeB_off_0 finSaved_seg3a finSaved_seg4a
   frame_seg2a frame_seg3a frame_seg4a fsp_aligned
   hmacInnerInit hmacOuterInit hmacWith_short innerLastBlock innerLastBlock_length
   lsCompress256Sym lsMemcpySym lsMemsetSym ls_externAt?_of_mem
   outerBlock outerBlock_digestBytes_length
   read32_words_at_104_of_shaStateBytes read32_words_at_64_of_shaStateBytes
   read64_seg2a_mid read64_seg3a_pad_32 read64_seg3a_pad_40
   readBytes_56_eq_append_8 readBytes_56_of_buf_eq readBytes_64_after_pad_memset
   readBytes_fsp_64_seg2 readBytes_fsp_64_seg3 readBytes_write32_8_digestBytes
   shaStateBytes_length
   toLEBytes_4_rev32 toLEBytes_8_read64 toLEBytes_8_rev32_append toLEBytes_8_rev64
   ult_7_of_lt_56 xor_63_of_lt_64 zeroExtend64_ofNat8 zeroExtend64_truncate32_ofNat64)
open CryptoVerification.LibsignalTripleRatchet.Extract
  (CallingConventionPreserved.x19 CallingConventionPreserved.x20
   CallingConventionPreserved.x21 CallingConventionPreserved.x22
   CallingConventionPreserved.x27 CallingConventionPreserved.x29 S2Frame)
open CryptoVerification.LibsignalTripleRatchet.FinalizeFixedProof (FinPre)
open CryptoVerification.LibsignalTripleRatchet.HkdfExt
  (AgreesOn AgreesOn.finSaved_of AgreesOn.read64_eq AgreesOn.readBytes_eq
   S2Frame.trans_agreesOutside S2Frame.trans_agreesOutside_sub)
open CryptoVerification.LibsignalTripleRatchet.HkdfExt.FinX (read32_seg4a_mid_x)
open LibsignalBinary.Heap (AllocCallPreserved VmPreserved)
open LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAux
  (stripExecOutside_readBytes stripExecOutside_readable stripExecOutside_rw unstrip_frame)
open LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAuxSat
  (checkBlockNoMsrTpidrEl0 placed_memset_budget_steps_sat)
open LibsignalBinary.Proofs.ConsumeMessageKey.CoupledCompress256Sat
  (hmacCompressOnlyExcHooksSat hmacNoMemsetExcHooksSat
   runsTo_block_lift_vm_compress_only_sat runsTo_block_lift_vm_no_memset_sat)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat
  (HkdfPlacedHooksExactBudgetSat)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
  (CallingConventionPreserved.x23 CallingConventionPreserved.x24 CallingConventionPreserved.x25
   CallingConventionPreserved.x26 CallingConventionPreserved.x28 HookSatCompress256
   hookOk_withLsRet624_sessionCompress256ROBudget_elim
   s2_compress256_step_placed_of_hookSat)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixedSat (FinCommonSat FinPostSat FinPreSat)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemsetRegionBudgetSpec)

attribute [local arm64_norm] MemWidth.bytes SimdMemSize.bytes

/-! ## 1. `RunsToVm`, Single-Hook Steps & `memset`-Free Block Lifting -/

/-- `RunsTo` strengthened with `VmPreserved` and split `trace` / `calleeSavedVRegs` preservation. -/
@[expose] public def RunsToVm (P : Program) (s : State) (Q : State → Prop) : Prop :=
  P.CodeLoaded s.mem →
  ∃ sf : State,
    Steps P s sf ∧ VmPreserved s sf ∧ sf.trace = s.trace ∧
    calleeSavedVRegs sf = calleeSavedVRegs s ∧ Q sf ∧ P.CodeLoaded sf.mem

public theorem RunsToVm.refl {P : Program} {s : State} {Q : State → Prop} (hq : Q s) :
    RunsToVm P s Q :=
  fun hL => ⟨s, .refl s, VmPreserved.refl s, rfl, rfl, hq, hL⟩

public theorem RunsToVm.mono {P : Program} {s : State} {Q1 Q2 : State → Prop}
    (h : RunsToVm P s Q1) (himp : ∀ sf, Q1 sf → Q2 sf) :
    RunsToVm P s Q2 :=
  fun hL =>
    let ⟨sf, hst, hvm, htr, hv, hq, hLf⟩ := h hL
    ⟨sf, hst, hvm, htr, hv, himp sf hq, hLf⟩

public theorem RunsToVm.trans_full {P : Program} {s : State} {Q1 Q2 : State → Prop}
    (h1 : RunsToVm P s Q1)
    (h2 : ∀ s1, Q1 s1 → s.mem.KeepsFrozen s1.mem → RunsToVm P s1 Q2) :
    RunsToVm P s Q2 :=
  fun hL =>
    let ⟨s1, hst1, hvm1, htr1, hv1, hq1, hL1⟩ := h1 hL
    let ⟨s2, hst2, hvm2, htr2, hv2, hq2, hL2⟩ := h2 s1 hq1 hst1.keepsFrozen hL1
    ⟨s2, hst1.trans hst2, hvm1.trans hvm2, htr2.trans htr1, hv2.trans hv1, hq2, hL2⟩

/-- Transfer `RunsToVm` from placed block `j` to any caller block `i` sharing `H`. -/
public theorem RunsToVm.of_other_block [LibsignalPlacement] {H : LibsignalHooks}
    {i j : Nat} {Pi Pj : Program}
    [hcaller : IsLsBlockProg Pi i H] [hcallee : IsLsBlockProg Pj j H]
    (hj_lt : j < 624) (hj_unmut : (j ∈ libsignalMutatedBlocks) = false)
    {s : State} {Q : State → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h : RunsToVm Pj s Q) :
    RunsToVm Pi s Q := by
  intro hLi
  have hLj : Pj.CodeLoaded s.mem :=
    hcallee.eq_blockProgram ▸ hcl j hj_lt hj_unmut H (fun _ => none) Syscall.standard
  obtain ⟨sf, hst_j, hvm, htr, hv, hq, _⟩ := h hLj
  have hext : ∀ pc, Pj.externAt? pc = Pi.externAt? pc := fun pc => by
    rw [hcallee.eq_blockProgram, hcaller.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hcallee.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : Pj.svc = Pi.svc := by
    rw [hcallee.eq_blockProgram, hcaller.eq_blockProgram]; rfl
  have hst_i := Steps.of_sameHooks hext hsvc hst_j
  exact ⟨sf, hst_i, hvm, htr, hv, hq, hst_i.codeLoaded hLi⟩

public theorem blk123_noSvc0 :
    VerifiedLibraries.RustStd.checkBlockNoSvc0 blkLib_123.text = true := by decide +kernel
public theorem blk123_noMsr :
    checkBlockNoMsrTpidrEl0 blkLib_123.text = true := by decide +kernel

private theorem runsTo_to_hmac {P : Program} {s : State} {Q : State → Prop} (h : RunsTo P s Q) :
    CryptoVerification.LibsignalSession.CryptoHmacSha256.RunsTo P s Q :=
  fun hL => let ⟨s', hst, ⟨htr, hv⟩, hq, hL'⟩ := h hL; ⟨s', hst, htr, hv, hq, hL'⟩

public theorem RunsToVm.trans {P : Program} {s : State} {Q1 Q2 : State → Prop}
    (h1 : RunsToVm P s Q1)
    (h2 : ∀ s1, Q1 s1 → RunsToVm P s1 Q2) :
    RunsToVm P s Q2 :=
  h1.trans_full fun s1 hq1 _ => h2 s1 hq1

/-- Lift a `memset`-free `RunsTo` segment on block `j` onto any caller block `Pi` (`[IsLsBlockProg Pi i H]`)
under `[HkdfPlacedHooksExactBudgetSat C.F H]`. -/
public theorem lift_block_vm [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [hH : HkdfPlacedHooksExactBudgetSat C.F H]
    {i j : Nat} {blkLib : Obj.PlacedLib} {Pi Pj : Program}
    [hcaller : IsLsBlockProg Pi i H] [hcallee : IsLsBlockProg Pj j H]
    (hlib : blkLib = libsignalSessionLib.blockLib j)
    (hchk_svc : VerifiedLibraries.RustStd.checkBlockNoSvc0 blkLib.text = true)
    (hchk_msr : checkBlockNoMsrTpidrEl0 blkLib.text = true)
    (hj_lt : j < 624) (hj_unmut : (j ∈ libsignalMutatedBlocks) = false)
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
    RunsToVm Pi s PostP := by
  intro hLi
  have hLj : (libsignalSessionLib.blockProgram lsmpl j H).CodeLoaded s.mem :=
    hcl j hj_lt hj_unmut H (fun _ => none) Syscall.standard
  obtain ⟨sf, hst_j, hvm, _hacp, htr, hvregs, hor⟩ :=
    runsTo_block_lift_vm_no_memset_sat hH.memcpy hH.compress256 hlib hchk_svc hchk_msr
      hLj (runsTo_to_hmac hrunsP) (runsTo_to_hmac hrunsQ) hrunP hrunQ
  have hPost : PostP sf := by
    rcases hor with hq | hp
    · exact hunstrip sf hvm hq
    · exact hp
  have hext : ∀ pc, (libsignalSessionLib.blockProgram lsmpl j H).externAt? pc =
      Pi.externAt? pc := fun pc => by
    rw [hcaller.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hcallee.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : (libsignalSessionLib.blockProgram lsmpl j H).svc = Pi.svc := by
    rw [hcaller.eq_blockProgram]; rfl
  have hst_i := Steps.of_sameHooks hext hsvc hst_j
  exact ⟨sf, hst_i, hvm, htr, hvregs, hPost, hst_i.codeLoaded hLi⟩

/-- `compress256`-only sibling of `lift_block_vm`: lifts a `memset`- and `memcpy`-free `RunsTo`
segment on block `j` onto any caller block `Pi` under `[HkdfPlacedHooksExactBudgetSat C.F H]`. -/
public theorem lift_block_vm_compress_only [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [hH : HkdfPlacedHooksExactBudgetSat C.F H]
    {i j : Nat} {blkLib : Obj.PlacedLib} {Pi Pj : Program}
    [hcaller : IsLsBlockProg Pi i H] [hcallee : IsLsBlockProg Pj j H]
    (hlib : blkLib = libsignalSessionLib.blockLib j)
    (hchk_svc : VerifiedLibraries.RustStd.checkBlockNoSvc0 blkLib.text = true)
    (hchk_msr : checkBlockNoMsrTpidrEl0 blkLib.text = true)
    (hj_lt : j < 624) (hj_unmut : (j ∈ libsignalMutatedBlocks) = false)
    {s : State} {PostP PostQ : State → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hrunsP : RunsTo (libsignalSessionLib.blockProgram lsmpl j H) s PostP)
    (hrunsQ : RunsTo
      (libsignalSessionLib.blockProgram lsmpl j
        (hmacCompressOnlyExcHooksSat C.F H s.mem
          (ProofLib.progKeep (libsignalSessionLib.blockProgram lsmpl j H))))
      (ProofLib.stripS (ProofLib.progKeep
        (libsignalSessionLib.blockProgram lsmpl j
          (hmacCompressOnlyExcHooksSat C.F H s.mem
            (ProofLib.progKeep (libsignalSessionLib.blockProgram lsmpl j H))))) s) PostQ)
    (hrunP : ∀ s', PostP s' → s'.status = .Running)
    (hrunQ : ∀ s', PostQ s' → s'.status = .Running)
    (hunstrip : ∀ sf, VmPreserved s sf →
      PostQ (ProofLib.stripS (ProofLib.progKeep
        (libsignalSessionLib.blockProgram lsmpl j
          (hmacCompressOnlyExcHooksSat C.F H s.mem
            (ProofLib.progKeep (libsignalSessionLib.blockProgram lsmpl j H))))) sf) → PostP sf) :
    RunsToVm Pi s PostP := by
  intro hLi
  have hLj : (libsignalSessionLib.blockProgram lsmpl j H).CodeLoaded s.mem :=
    hcl j hj_lt hj_unmut H (fun _ => none) Syscall.standard
  obtain ⟨sf, hst_j, hvm, _hacp, htr, hvregs, hor⟩ :=
    runsTo_block_lift_vm_compress_only_sat hH.compress256 hlib hchk_svc hchk_msr
      hLj (runsTo_to_hmac hrunsP) (runsTo_to_hmac hrunsQ) hrunP hrunQ
  have hPost : PostP sf := by
    rcases hor with hq | hp
    · exact hunstrip sf hvm hq
    · exact hp
  have hext : ∀ pc, (libsignalSessionLib.blockProgram lsmpl j H).externAt? pc =
      Pi.externAt? pc := fun pc => by
    rw [hcaller.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hcallee.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : (libsignalSessionLib.blockProgram lsmpl j H).svc = Pi.svc := by
    rw [hcaller.eq_blockProgram]; rfl
  have hst_i := Steps.of_sameHooks hext hsvc hst_j
  exact ⟨sf, hst_i, hvm, htr, hvregs, hPost, hst_i.codeLoaded hLi⟩

/-- `RunsToFrom` strengthened with `VmPreserved`. -/
@[expose] public def RunsToVmFrom (prog : Program) (s₀ s : State) (P : State → Prop) : Prop :=
  prog.CodeLoaded s.mem →
    ∃ sf : State,
      Steps prog s sf ∧ VmPreserved s sf ∧ TraceEq s₀ sf ∧ P sf ∧ prog.CodeLoaded sf.mem

public theorem runsToVm_of_from {prog : Program} {s : State} {P : State → Prop}
    (h : RunsToVmFrom prog s s P) : RunsToVm prog s P :=
  fun hL =>
    let ⟨sf, hst, hvm, ⟨htr, hv⟩, hp, hL'⟩ := h hL
    ⟨sf, hst, hvm, htr, hv, hp, hL'⟩

public theorem runsToVmFrom_refl {prog : Program} {s₀ s : State} {P : State → Prop} (h : P s)
    (htr : TraceEq s₀ s := by
      repeat' (first
        | with_reducible exact TraceEq.refl _
        | with_reducible apply TraceEq.advancePC_step
        | with_reducible apply TraceEq.setMem_step
        | with_reducible apply TraceEq.setPC_step
        | with_reducible apply TraceEq.setPState_step
        | with_reducible apply TraceEq.writeReg64_step
        | with_reducible apply TraceEq.writeReg32_step
        | with_reducible apply TraceEq.writeVReg128_step (by decide)
        | exact ⟨rfl, rfl⟩)) :
    RunsToVmFrom prog s₀ s P :=
  fun hL => ⟨s, .refl s, VmPreserved.refl s, htr, h, hL⟩

public theorem runsToVmFrom_step {prog : Program} {s₀ s : State} {inst : Instr} {P : State → Prop}
    (hrun : s.status = .Running)
    (hfetch : prog.fetch s.pc = some inst)
    (h : RunsToVmFrom prog s₀ (execInst inst s) P)
    (hnsvc0 : inst.isSvc0 = false := by decide)
    (hnmsr : inst.isMsrTpidrEl0 = false := by decide)
    (hsvc : prog.svc = Syscall.standard := by first | rfl | exact RunsTo.lsProg_svc) :
    RunsToVmFrom prog s₀ s P := by
  intro hL
  have hfm := Program.fetchMem_of_fetch hL hfetch
  have hstep : Step prog s (execInst inst s) :=
    Program.evalInst_eq_execInst inst s hsvc ▸ Step.exec hrun hfm
  have hL' : prog.CodeLoaded (execInst inst s).mem := hstep.codeLoaded hL
  have hvm1 : VmPreserved s (execInst inst s) :=
    (ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 s).toVmPreserved
      (Arm64.execInst_tpidrEl0_of_not_isMsrTpidrEl0 hnmsr s)
  obtain ⟨sf, hst, hvm, htr, hP, hL''⟩ := h hL'
  exact ⟨sf, .step hstep hst, hvm1.trans hvm, htr, hP, hL''⟩

local macro "s2_step_vm" : tactic =>
  `(tactic| (
    refine runsToVmFrom_step (inst := ?inst) ?hrun ?hfetch ?_ ?hnsvc0 ?hnmsr
    case hfetch => ((try simp (config := { decide := true }) only [arm64_norm, *]) <;> rfl)
    (case hnsvc0 => rfl); (case hnmsr => rfl)
    case hrun => (simp only [arm64_norm, *])
    try dsimp only [execInst, execAddSubImm, execAddSubExt, execAddSubShift, execAddSubCarry,
      execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect,
      execCondCompare, execDataProc1, execDataProc2, execDataProc3, execLdr, execLdrLit,
      execStr, execLdp, execStp, evalLogical, evalBitfield, evalAddrMode, AddrMode.baseReg,
      checkRegSPAligned, checkAddrSPAligned, MemWidth.isAligned, State.spAligned, extendVal,
      Reg.fromZRBits, Reg.fromSPBits]
    try simp (config := { decide := true }) only [arm64_norm, *]
    try arm64_discharge_perms_internal))

/-- Step through `memset` (`val = 0#8`) in `RunsToVmFrom` using `HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec`. -/
public theorem s2_memset_step_vm_of_budget [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h_memset : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec)
    {s₀ s : State} {Q : State → Prop}
    {dst lr : BitVec 64} {len : Nat}
    (hrun : s.status = .Running)
    (hpc : s.pc = lsρ lsMemsetSym)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : (s.readReg64 .x1).truncate 8 = 0#8)
    (hx2 : (s.readReg64 .x2).toNat = len)
    (hlr : s.readReg64 .lr = lr)
    (hsp_al : (s.sp &&& 15#64) = 0#64)
    (hrw : s.mem.RW dst len)
    (h : ∀ s' : State,
      TraceEq s₀ s' →
      s'.pc = lr →
      s'.status = .Running →
      CallingConventionPreserved s s' →
      VmPreserved s s' →
      s.mem.KeepsFrozen s'.mem →
      s'.mem.readBytes dst len = List.replicate len 0#8 →
      S2Frame s.mem s'.mem [(dst, len)] →
      AgreesOn (fun a => (s.mem.perm a).r = true ∧ s.mem.isLazyFree a = false)
        s'.mem (s.mem.writeBytes dst (List.replicate len 0#8)) →
      RunsToVmFrom prog s₀ s' Q)
    (htr0 : TraceEq s₀ s := by
      repeat' (first
        | with_reducible exact TraceEq.refl _
        | with_reducible apply TraceEq.advancePC_step
        | with_reducible apply TraceEq.setMem_step
        | with_reducible apply TraceEq.setPC_step
        | with_reducible apply TraceEq.setPState_step
        | with_reducible apply TraceEq.writeReg64_step
        | with_reducible apply TraceEq.writeReg32_step
        | with_reducible apply TraceEq.writeVReg128_step (by decide)
        | exact ⟨rfl, rfl⟩))
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    RunsToVmFrom prog s₀ s Q := by
  intro hL
  obtain ⟨s1, hst1, hvm1, htr1, hv1, hpc1, hstat1, hcc1, _, hkf1, hread1, hs2_1, hag1⟩ :=
    placed_memset_budget_steps_sat (prog := prog) (i := i) h_memset
      hrun hpc hx0 hx1 hx2 hlr hsp_al hrw hi hunmut
  have htr_01 : TraceEq s₀ s1 := ⟨htr1.trans htr0.1, hv1.trans htr0.2⟩
  obtain ⟨sf, hst2, hvm2, htr2, hQ, hL2⟩ :=
    h s1 htr_01 hpc1 hstat1 hcc1 hvm1 hkf1 hread1 hs2_1 hag1 (hst1.codeLoaded hL)
  exact ⟨sf, hst1.trans hst2, hvm1.trans hvm2, htr2, hQ, hL2⟩

/-- Step through `n`-block `compress256` in `RunsToVmFrom` using `HookSatCompress256 H lsCompress256Sym F`. -/
public theorem s2_compress256_multi_step_vm_of_hookSat [LibsignalPlacement] {prog : Program}
    {i : Nat} {F : ShaCompress} {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h_c256 : HookSatCompress256 H lsCompress256Sym F)
    {s₀ s : State} {Q : State → Prop}
    {stPtr blkPtr lr : BitVec 64} {st : ShaState} {bs : List (BitVec 8)} {n : Nat}
    (hrun : s.status = .Running)
    (hpc : s.pc = lsρ lsCompress256Sym)
    (hx0 : s.readReg64 .x0 = stPtr)
    (hx1 : s.readReg64 .x1 = blkPtr)
    (hx2 : (s.readReg64 .x2).toNat = n)
    (hlr : s.readReg64 .lr = lr)
    (hsp_al : (s.sp &&& 15#64) = 0#64)
    (hst : s.mem.readBytes stPtr 32 = shaStateBytes st)
    (hbs : s.mem.readBytes blkPtr (64 * n) = bs)
    (hrw_st : s.mem.RW stPtr 32)
    (hrw_stk : s.mem.RW (s.sp - 176#64) 176)
    (hread_blk : s.mem.Readable blkPtr (64 * n))
    (hdisj_st_stk : DisjointRegions stPtr 32 (s.sp - 176#64) 176)
    (hdisj_st_blk : n = 0 ∨ DisjointRegions stPtr 32 blkPtr (64 * n))
    (hdisj_stk_blk : n = 0 ∨ DisjointRegions (s.sp - 176#64) 176 blkPtr (64 * n))
    (h : ∀ s' : State,
      TraceEq s₀ s' →
      s'.pc = lr →
      s'.status = .Running →
      CallingConventionPreserved s s' →
      VmPreserved s s' →
      AllocCallPreserved s s' →
      s.mem.KeepsFrozen s'.mem →
      s'.mem.readBytes stPtr 32 = shaStateBytes ((chunks64 bs).foldl F st) →
      S2Frame s.mem s'.mem [(stPtr, 32), (s.sp - 176#64, 176)] →
      AgreesOn
        (fun a => (s.mem.perm a).r = true ∧ s.mem.isLazyFree a = false ∧
          OutsideRegion (s.sp - 176#64) 176 a)
        s'.mem (s.mem.writeBytes stPtr (shaStateBytes ((chunks64 bs).foldl F st))) →
      RunsToVmFrom prog s₀ s' Q)
    (hn_le : 64 * n ≤ 2 ^ 64 := by omega)
    (htr0 : TraceEq s₀ s := by
      repeat' (first
        | with_reducible exact TraceEq.refl _
        | with_reducible apply TraceEq.advancePC_step
        | with_reducible apply TraceEq.setMem_step
        | with_reducible apply TraceEq.setPC_step
        | with_reducible apply TraceEq.setPState_step
        | with_reducible apply TraceEq.writeReg64_step
        | with_reducible apply TraceEq.writeReg32_step
        | with_reducible apply TraceEq.writeVReg128_step (by decide)
        | exact ⟨rfl, rfl⟩))
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide)
    (hlr_ls : LsRetAddr624 lr := by prove_ls_ret624) :
    RunsToVmFrom prog s₀ s Q := by
  intro hL
  obtain ⟨f, hfH, hfOk⟩ := h_c256.toHookSat
  have hhook : prog.externAt? s.pc = some f := by
    rw [hpc, ls_externAt?_of_mem (by decide) hi hunmut, hfH]
  obtain ⟨hkf, hsym, hret, hcc, hvm1, hacp1, htr1, hread1, hs2_1, hag1⟩ :=
    hookOk_withLsRet624_sessionCompress256ROBudget_elim hfOk (hlr ▸ hlr_ls) hrun hx0 hx1 hx2 hsp_al
      hst hbs hrw_st hrw_stk hread_blk hdisj_st_stk hdisj_st_blk hdisj_stk_blk hn_le
  have hstep1 : Step prog s (f s) := Step.extern hrun hhook hkf hsym
  have htr_01 : TraceEq s₀ (f s) := ⟨htr1.trans htr0.1, hcc.2.2.2.2.2.2.2.2.2.2.2.2.trans htr0.2⟩
  obtain ⟨sf, hst2, hvm2, htr2, hQ, hL2⟩ :=
    h (f s) htr_01 (hret.1.trans hlr) hret.2.2 hcc hvm1 hacp1 hkf hread1 hs2_1 hag1
      (hL.of_keepsFrozen hkf)
  exact ⟨sf, .step hstep1 hst2, hvm1.trans hvm2, htr2, hQ, hL2⟩

/-- Step through 1-block `compress256` in `RunsToVmFrom` using `HookSatCompress256 H lsCompress256Sym F`. -/
public theorem s2_compress256_step_vm_of_hookSat [LibsignalPlacement] {prog : Program}
    {i : Nat} {F : ShaCompress} {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h_c256 : HookSatCompress256 H lsCompress256Sym F)
    {s₀ s : State} {Q : State → Prop}
    {stPtr blkPtr lr : BitVec 64} {st : ShaState} {blk : List (BitVec 8)}
    (hrun : s.status = .Running)
    (hpc : s.pc = lsρ lsCompress256Sym)
    (hx0 : s.readReg64 .x0 = stPtr)
    (hx1 : s.readReg64 .x1 = blkPtr)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hlr : s.readReg64 .lr = lr)
    (hsp_al : (s.sp &&& 15#64) = 0#64)
    (hst : s.mem.readBytes stPtr 32 = shaStateBytes st)
    (hblk : s.mem.readBytes blkPtr 64 = blk)
    (hlen : blk.length = 64)
    (hrw_st : s.mem.RW stPtr 32)
    (hrw_stk : s.mem.RW (s.sp - 176#64) 176)
    (hread_blk : s.mem.Readable blkPtr 64)
    (hdisj_st_stk : DisjointRegions stPtr 32 (s.sp - 176#64) 176)
    (hdisj_st_blk : DisjointRegions stPtr 32 blkPtr 64)
    (hdisj_stk_blk : DisjointRegions (s.sp - 176#64) 176 blkPtr 64)
    (h : ∀ s' : State,
      TraceEq s₀ s' →
      s'.pc = lr →
      s'.status = .Running →
      CallingConventionPreserved s s' →
      VmPreserved s s' →
      AllocCallPreserved s s' →
      s.mem.KeepsFrozen s'.mem →
      s'.mem.readBytes stPtr 32 = shaStateBytes (F st blk) →
      S2Frame s.mem s'.mem [(stPtr, 32), (s.sp - 176#64, 176)] →
      AgreesOn
        (fun a => (s.mem.perm a).r = true ∧ s.mem.isLazyFree a = false ∧
          OutsideRegion (s.sp - 176#64) 176 a)
        s'.mem (s.mem.writeBytes stPtr (shaStateBytes (F st blk))) →
      RunsToVmFrom prog s₀ s' Q)
    (htr0 : TraceEq s₀ s := by
      repeat' (first
        | with_reducible exact TraceEq.refl _
        | with_reducible apply TraceEq.advancePC_step
        | with_reducible apply TraceEq.setMem_step
        | with_reducible apply TraceEq.setPC_step
        | with_reducible apply TraceEq.setPState_step
        | with_reducible apply TraceEq.writeReg64_step
        | with_reducible apply TraceEq.writeReg32_step
        | with_reducible apply TraceEq.writeVReg128_step (by decide)
        | exact ⟨rfl, rfl⟩))
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide)
    (hlr_ls : LsRetAddr624 lr := by prove_ls_ret624) :
    RunsToVmFrom prog s₀ s Q := by
  have hx2_nat : (s.readReg64 .x2).toNat = 1 := by rw [hx2]; rfl
  refine s2_compress256_multi_step_vm_of_hookSat h_c256 hrun hpc hx0 hx1 hx2_nat hlr
    hsp_al hst (by simpa using hblk) hrw_st hrw_stk (by simpa using hread_blk)
    hdisj_st_stk (Or.inr (by simpa using hdisj_st_blk)) (Or.inr (by simpa using hdisj_stk_blk))
    (fun s' htr hpc' hstat' hcc hvm hacp hkf hread' hs2' hag' => ?_) (by decide) htr0 hi hunmut
    hlr_ls
  rw [chunks64_single_foldl F st blk hlen] at hread' hag'
  exact h s' htr hpc' hstat' hcc hvm hacp hkf hread' hs2' hag'

public theorem mem_setMem (s : State) (m : Memory) : (s.setMem m).mem = m := rfl

@[local simp, local arm64_norm]
private theorem extractLsb'_0_64_zero128 : BitVec.extractLsb' 0 64 0#128 = 0#64 := rfl

@[local simp, local arm64_norm]
private theorem extractLsb'_64_64_zero128 : BitVec.extractLsb' 64 64 0#128 = 0#64 := rfl

public theorem stripS_mem (kp : BitVec 64 → Bool) (s : State) :
    (ProofLib.stripS kp s).mem = ProofLib.stripExecOutside kp s.mem := by cases s; rfl

public theorem stripS_read8 (kp : BitVec 64 → Bool) (s : State) (a : BitVec 64) :
    (ProofLib.stripS kp s).mem.read8 a = s.mem.read8 a := by
  cases s; simp [ProofLib.stripS, ProofLib.strip_read8]

public theorem stripS_read64 (kp : BitVec 64 → Bool) (s : State) (a : BitVec 64) :
    (ProofLib.stripS kp s).mem.read64 a = s.mem.read64 a := by
  cases s; simp [ProofLib.stripS, Memory.read64, ProofLib.strip_read8]

public theorem stripS_readBytes (kp : BitVec 64 → Bool) (s : State) (a : BitVec 64) (n : Nat) :
    (ProofLib.stripS kp s).mem.readBytes a n = s.mem.readBytes a n := by
  rw [stripS_mem, stripExecOutside_readBytes]

public theorem stripS_hmacSt (kp : BitVec 64 → Bool)
    {F : ShaState → List (BitVec 8) → ShaState} {s : State} {a : BitVec 64}
    {key msg : List (BitVec 8)} :
    HmacSt (ProofLib.stripS kp s).mem a F key msg ↔ HmacSt s.mem a F key msg := by
  unfold HmacSt
  simp only [stripS_read8, stripS_read64, stripS_readBytes]

public theorem stripS_finSaved (kp : BitVec 64 → Bool) (s0 s : State) :
    FinSaved (ProofLib.stripS kp s0) ((ProofLib.stripS kp s0).sp - 144#64)
      (ProofLib.stripS kp s).mem ↔
    FinSaved s0 (s0.sp - 144#64) s.mem := by
  have hsp0 : (ProofLib.stripS kp s0).sp = s0.sp := by cases s0; rfl
  have hr : ∀ r, (ProofLib.stripS kp s0).readReg64 r = s0.readReg64 r := fun _ => by cases s0; rfl
  unfold FinSaved
  simp only [hsp0, hr, stripS_read64]

public structure FinCommon (s0 s : State) : Prop where
  status : s.status = .Running
  sp_eq  : s.sp = s0.sp - 144#64
  x29_eq : s.readReg64 .x29 = s0.sp - 144#64 + 0x40#64
  x26_eq : s.readReg64 .x26 = s0.readReg64 .x26
  x27_eq : s.readReg64 .x27 = s0.readReg64 .x27
  x28_eq : s.readReg64 .x28 = s0.readReg64 .x28
  saved  : FinSaved s0 (s0.sp - 144#64) s.mem
  frame  : Frame s0.mem s.mem
    [(s0.readReg64 .x0, 32), (s0.readReg64 .x1, 0x90), (s0.sp - 144#64, 144)]

@[expose] public def FinPost (F : ShaState → List (BitVec 8) → ShaState)
    (key msg : List (BitVec 8)) (s0 s' : State) : Prop :=
  s'.pc = s0.readReg64 .lr ∧
  s'.status = .Running ∧
  CalleeSaved s0 s' ∧
  s'.mem.readBytes (s0.readReg64 .x0) 32 = hmacWith F key msg ∧
  Frame s0.mem s'.mem
    [(s0.readReg64 .x0, 32), (s0.readReg64 .x1, 0x90), (s0.sp - 144#64, 144)]

public theorem rw_of_perm_eq {m m' : Memory} {regs : List (BitVec 64 × ℕ)} {a : BitVec 64} {n : ℕ}
    (hfr : Frame m m' regs)
    (hrw : m.RW a n) : m'.RW a n :=
  (S2Frame.of_frame hfr).rw_of_rw a n hrw

public theorem unstrip_finCommon {kp : BitVec 64 → Bool} {s0 s : State}
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

/-! ## 2. Block `123` (`finalize_fixed`) `RunsToVm` under `HkdfPlacedHooksExactBudgetSat` -/

private theorem read64_write64_add_same (m : Memory) (fsp c v : BitVec 64) :
    (m.write64 (fsp + c) v).read64 (fsp + c) = v :=
  Memory.read64_write64_same m (fsp + c) v

private theorem read64_write64_add_ne (m : Memory) (fsp c1 c2 v : BitVec 64)
    (h : decide (8 ≤ (c1 - c2).toNat ∧ 8 ≤ (c2 - c1).toNat) = true) :
    (m.write64 (fsp + c1) v).read64 (fsp + c2) = m.read64 (fsp + c2) := by
  have hc := of_decide_eq_true h
  exact Memory.read64_write64_disjoint m (fsp + c1) (fsp + c2) v (by bv_omega) (by bv_omega)

public theorem finSaved_of_seg1a (s0 : State) (m : Memory) :
    FinSaved s0 (s0.sp - 144#64)
      (((((((((m.write64 (s0.sp - 144#64 + 64#64) (s0.readReg64 .x29)).write64
        (s0.sp - 144#64 + 72#64) (s0.readReg64 .lr)).write64
        (s0.sp - 144#64 + 80#64) (s0.readReg64 .x25)).write64
        (s0.sp - 144#64 + 96#64) (s0.readReg64 .x24)).write64
        (s0.sp - 144#64 + 104#64) (s0.readReg64 .x23)).write64
        (s0.sp - 144#64 + 112#64) (s0.readReg64 .x22)).write64
        (s0.sp - 144#64 + 120#64) (s0.readReg64 .x21)).write64
        (s0.sp - 144#64 + 128#64) (s0.readReg64 .x20)).write64
        (s0.sp - 144#64 + 136#64) (s0.readReg64 .x19)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · iterate 8 rw [read64_write64_add_ne _ _ _ _ _ (by decide)]
    exact read64_write64_add_same _ _ _ _
  · iterate 7 rw [read64_write64_add_ne _ _ _ _ _ (by decide)]
    exact read64_write64_add_same _ _ _ _
  · iterate 6 rw [read64_write64_add_ne _ _ _ _ _ (by decide)]
    exact read64_write64_add_same _ _ _ _
  · iterate 5 rw [read64_write64_add_ne _ _ _ _ _ (by decide)]
    exact read64_write64_add_same _ _ _ _
  · iterate 4 rw [read64_write64_add_ne _ _ _ _ _ (by decide)]
    exact read64_write64_add_same _ _ _ _
  · iterate 3 rw [read64_write64_add_ne _ _ _ _ _ (by decide)]
    exact read64_write64_add_same _ _ _ _
  · iterate 2 rw [read64_write64_add_ne _ _ _ _ _ (by decide)]
    exact read64_write64_add_same _ _ _ _
  · rw [read64_write64_add_ne _ _ _ _ _ (by decide)]
    exact read64_write64_add_same _ _ _ _
  · exact read64_write64_add_same _ _ _ _

local macro "fin_reg_local" : tactic =>
  `(tactic| (
    try rw [State.readReg64_setMem]
    try rw [State.pc_setMem]
    try rw [State.sp_setMem]
    try rw [State.status_setMem]
    simp (config := { decide := true }) only [arm64_norm, *]))

public theorem s2Frame_144_to_320 {m1 m2 : Memory} {x0 x1 sp : BitVec 64}
    (h : S2Frame m1 m2 [(x0, 32), (x1, 0x90), (sp - 144#64, 144)]) :
    S2Frame m1 m2 [(x0, 32), (x1, 0x90), (sp - 320#64, 320)] := by
  refine h.mono fun a ha r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ha (x0, 32) (by simp)
  · exact ha (x1, 0x90) (by simp)
  · have ha320 := ha (sp - 320#64, 320) (by simp)
    unfold OutsideRegion at ha320 ⊢; bv_omega

private theorem seg4a_disj {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {key msg : List (BitVec 8)} {s0 : State} (hpre : FinPre b F key msg s0) :
    DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1) 0x90 ∧
    DisjointRegions (s0.readReg64 .x1) 0x90 (s0.sp - 144#64 + 0x40#64) 0x50 ∧
    DisjointRegions (s0.sp - 144#64) 64 (s0.sp - 144#64 + 0x40#64) 0x50 ∧
    DisjointRegions (s0.readReg64 .x0) 32 (s0.sp - 144#64 + 0x40#64) 0x50 :=
  ⟨hpre.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩,
   hpre.disj_hm_fsp.sub_right _ ⟨by decide, by bv_omega⟩,
   by unfold DisjointRegions; bv_omega,
   hpre.disj_out_fsp.sub_right _ ⟨by decide, by bv_omega⟩⟩

public theorem ost_eq_seg3a {m m1 m2 m3 m4 : Memory} {hm fsp : BitVec 64} {bs : List (BitVec 8)}
    (host : m.readBytes (hm + 0x68#64) 32 = bs)
    (hag1 : AgreesOutside m m1 hm 64)
    (hag2 : AgreesOutside m1 m2 fsp 64)
    (hag3 : AgreesOutside m2 m3 hm 64)
    (hag4 : AgreesOutside m3 m4 fsp 64)
    (hd_hm : DisjointRegions hm 64 (hm + 0x68#64) 32)
    (hd_fsp : DisjointRegions fsp 64 (hm + 0x68#64) 32) :
    m4.readBytes (hm + 0x68#64) 32 = bs :=
  (hag4.readBytes_eq hd_fsp (by decide)).trans
    ((hag3.readBytes_eq hd_hm (by decide)).trans
      ((hag2.readBytes_eq hd_fsp (by decide)).trans
        ((hag1.readBytes_eq hd_hm (by decide)).trans host)))

private structure StateF0pSat [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key msg : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = (blkPl_123).base + 28#64
  common  : FinCommonSat s0 s
  x0_eq   : s.readReg64 .x0 = s0.readReg64 .x0
  x1_eq   : s.readReg64 .x1 = s0.readReg64 .x1
  hmac_st : HmacSt s.mem (s0.readReg64 .x1) F key msg

private structure StateF1Sat [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key msg : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = (blkPl_123).base + 76#64
  common  : FinCommonSat s0 s
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  x21_eq  : s.readReg64 .x21 = s0.readReg64 .x1 + 0x40#64
  x22_eq  : s.readReg64 .x22 = 0x80#64
  x23_eq  : s.readReg64 .x23 = BitVec.ofNat 64 msg.length
  x24_eq  : s.readReg64 .x24 = 1#64
  x25_eq  : s.readReg64 .x25 = BitVec.ofNat 64 (63 - msg.length)
  buf_eq  : s.mem.readBytes (s0.readReg64 .x1) 64 =
    msg ++ [0x80#8] ++ List.replicate (63 - msg.length) 0#8
  ist_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x40#64) 32 = shaStateBytes (hmacInnerInit F key)
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)
  obl_eq  : s.mem.read64 (s0.readReg64 .x1 + 0x88#64) = 1#64

private structure StateF2Sat [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key msg : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = (blkPl_123).base + 176#64
  common  : FinCommonSat s0 s
  x0_eq   : s.readReg64 .x0 = s0.readReg64 .x1 + 0x40#64
  x1_eq   : s.readReg64 .x1 = s0.sp - 144#64
  x2_eq   : s.readReg64 .x2 = 1#64
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  x21_eq  : s.readReg64 .x21 = s0.readReg64 .x1 + 0x40#64
  x22_eq  : s.readReg64 .x22 = 0x80#64
  blk_eq  : s.mem.readBytes (s0.sp - 144#64) 64 = innerLastBlock msg
  ist_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x40#64) 32 = shaStateBytes (hmacInnerInit F key)
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)
  obl_eq  : s.mem.read64 (s0.readReg64 .x1 + 0x88#64) = 1#64

private structure StateF3Sat [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key msg : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = (blkPl_123).base + 180#64
  common  : FinCommonSat s0 s
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  x21_eq  : s.readReg64 .x21 = s0.readReg64 .x1 + 0x40#64
  x22_eq  : s.readReg64 .x22 = 0x80#64
  ist_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x40#64) 32 =
    shaStateBytes (F (hmacInnerInit F key) (innerLastBlock msg))
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)
  obl_eq  : s.mem.read64 (s0.readReg64 .x1 + 0x88#64) = 1#64

private structure StateF3bSat [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key msg : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = (blkPl_123).base + 304#64
  common  : FinCommonSat s0 s
  x0_eq   : s.readReg64 .x0 = s0.readReg64 .x1 + 0x68#64
  x1_eq   : s.readReg64 .x1 = s0.sp - 144#64
  x2_eq   : s.readReg64 .x2 = 1#64
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  blk_eq  : s.mem.readBytes (s0.sp - 144#64) 64 =
    outerBlock (digestBytes (F (hmacInnerInit F key) (innerLastBlock msg)))
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)

private structure StateF4Sat [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key msg : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = (blkPl_123).base + 308#64
  common  : FinCommonSat s0 s
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 =
    shaStateBytes (F (hmacOuterInit F key)
      (outerBlock (digestBytes (F (hmacInnerInit F key) (innerLastBlock msg)))))

private structure StateF5Sat [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key msg : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq  : s.pc = (blkPl_123).base + 420#64
  common : FinCommonSat s0 s
  out_eq : s.mem.readBytes (s0.readReg64 .x0) 32 = hmacWith F key msg

private theorem seg1a_123 [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    {key msg : List (BitVec 8)} {s0 : State}
    (hpre : FinPreSat finPlacedFakeB C.F key msg s0) :
    RunsToVm ((blkPC_123).rebase (blkPl_123).base H) s0 (StateF0pSat C.F key msg s0) := by
  apply runsToVm_of_from
  have hpc : s0.pc = (blkPl_123).base := by simpa only [finPlacedFakeB_off_0] using hpre.pc_eq
  have hstat := hpre.status
  have hal0 : (s0.sp &&& 15#64) = 0#64 := hpre.sp_aligned
  have hal_fsp : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  have hrw_fsp : s0.mem.RW (s0.sp - 144#64) 144 := hpre.rw_fsp
  iterate 7 s2_step_vm
  refine runsToVmFrom_refl ?_
  have hag : AgreesOutside s0.mem
      (((((((((s0.mem.write64 (s0.sp - 144#64 + 64#64) (s0.readReg64 .x29)).write64
        (s0.sp - 144#64 + 72#64) (s0.readReg64 .lr)).write64
        (s0.sp - 144#64 + 80#64) (s0.readReg64 .x25)).write64
        (s0.sp - 144#64 + 96#64) (s0.readReg64 .x24)).write64
        (s0.sp - 144#64 + 104#64) (s0.readReg64 .x23)).write64
        (s0.sp - 144#64 + 112#64) (s0.readReg64 .x22)).write64
        (s0.sp - 144#64 + 120#64) (s0.readReg64 .x21)).write64
        (s0.sp - 144#64 + 128#64) (s0.readReg64 .x20)).write64
        (s0.sp - 144#64 + 136#64) (s0.readReg64 .x19))
      (s0.sp - 144#64) 144 := by
    agrees_outside_writes
  refine
    { pc_eq := by fin_reg_local
      common :=
        { status := by fin_reg_local, sp_eq := by fin_reg_local, x29_eq := by fin_reg_local,
          x26_eq := by fin_reg_local, x27_eq := by fin_reg_local, x28_eq := by fin_reg_local,
          saved := by rw [mem_setMem]; exact finSaved_of_seg1a s0 s0.mem
          frame := by
            rw [mem_setMem]
            exact s2Frame_144_to_320
              (S2Frame.trans_agreesOutside (S2Frame.refl s0.mem _) (by simp) hag) }
      x0_eq := by fin_reg_local
      x1_eq := by fin_reg_local
      hmac_st := by rw [mem_setMem]; exact HmacSt.of_agreesOutside hpre.hmac_st hag hpre.disj_hm_fsp.symm }

private theorem seg1b_123 [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [hH : HkdfPlacedHooksExactBudgetSat C.F H]
    {key msg : List (BitVec 8)} {s0 s : State}
    (hpre : FinPreSat finPlacedFakeB C.F key msg s0)
    (hs : StateF0pSat C.F key msg s0 s) :
    RunsToVm ((blkPC_123).rebase (blkPl_123).base H) s (StateF1Sat C.F key msg s0) := by
  apply runsToVm_of_from
  rcases hs with ⟨hpc, hcom, hx0, hx1, hhmac⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  rcases hhmac with ⟨hmsg_lt64, hmsg_eq, hpos_eq, hin_eq, hibl_eq, hout_eq, hobl_eq⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := hframe.rw_of_rw _ _ hpre.rw_hm
  have hrw_stk320 : s.mem.RW (s0.sp - 320#64) 320 := hframe.rw_of_rw _ _ hpre.rw_stk320
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := hrw_stk320.sub (by bv_omega)
  have hcw_pos : s.mem.canWrite (s0.readReg64 .x1 + BitVec.ofNat 64 msg.length) 1 = true :=
    hrw_hm.canWrite_sub (by bv_omega) (by decide)
  have hze32 := zeroExtend64_truncate32_ofNat64 hmsg_lt64
  have hze64 := zeroExtend64_ofNat8 hmsg_lt64
  have hxor63 := xor_63_of_lt_64 hmsg_lt64
  have hal_fsp : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  iterate 12 s2_step_vm
  have htoNat_sub : (BitVec.ofNat 64 (63 - msg.length)).toNat = 63 - msg.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  set dst := s0.readReg64 .x1 + BitVec.ofNat 64 msg.length + 1#64
  set len := 63 - msg.length
  set m_pre := s.mem.write8 (s0.readReg64 .x1 + BitVec.ofNat 64 msg.length) 128#8
  have hrw_memset : m_pre.RW dst len := by
    refine Memory.RW.of_perm_eq (by simp [m_pre]) (fun _ => Memory.isLazyFree_write8_of_false _ _)
      (hrw_hm.sub ?_)
    have := hpre.msg_lt; dsimp only [dst, len]; bv_omega
  refine s2_memset_step_vm_of_budget hH.memset
    (dst := dst) (lr := (blkPl_123).base + 76#64) (len := len)
    hstat rfl
    (by simp only [dst, arm64_norm])
    (by simp (config := { decide := true }) only [arm64_norm])
    (by simpa only [len, arm64_norm] using htoNat_sub)
    rfl (by simp only [arm64_norm, hsp]; exact hpre.sp_aligned) hrw_memset
    fun s2 htr2 hpc2 hstat2 hcc2 _ _ _ hs2_frame hag_on => ?_
  refine runsToVmFrom_refl ?_ htr2
  have hag_pad : AgreesOutside s.mem (m_pre.writeBytes dst (List.replicate len 0#8))
      (s0.readReg64 .x1) 64 :=
    agreesOutside_pad_memset s.mem (s0.readReg64 .x1) msg hpre.msg_lt
  have hP_pre : ∀ {a : BitVec 64}, s.mem.permNoLazy a = some Perm.rw →
      (m_pre.perm a).r = true ∧ m_pre.isLazyFree a = false := by
    intro a hnl
    obtain ⟨hrw_a, hlf_a⟩ := Memory.permNoLazy_eq_some_rw_iff.mp hnl
    exact ⟨by dsimp only [m_pre]; rw [Memory.perm_write8, hrw_a]; rfl,
      Memory.isLazyFree_write8_of_false _ _ hlf_a⟩
  have hP_saved : ∀ a, InRegion (s0.sp - 144#64 + 0x40#64) 0x50 a →
      (m_pre.perm a).r = true ∧ m_pre.isLazyFree a = false :=
    fun a ha => hP_pre (hrw_fsp a (by unfold InRegion at ha ⊢; bv_omega))
  have hP_hm64 : ∀ a, InRegion (s0.readReg64 .x1) 64 a →
      (m_pre.perm a).r = true ∧ m_pre.isLazyFree a = false :=
    fun a ha => hP_pre (hrw_hm a (by unfold InRegion at ha ⊢; bv_omega))
  have hP_ist : ∀ a, InRegion (s0.readReg64 .x1 + 0x40#64) 32 a →
      (m_pre.perm a).r = true ∧ m_pre.isLazyFree a = false :=
    fun a ha => hP_pre (hrw_hm a (by unfold InRegion at ha ⊢; bv_omega))
  have hP_ost : ∀ a, InRegion (s0.readReg64 .x1 + 0x68#64) 32 a →
      (m_pre.perm a).r = true ∧ m_pre.isLazyFree a = false :=
    fun a ha => hP_pre (hrw_hm a (by unfold InRegion at ha ⊢; bv_omega))
  have hP_obl : ∀ a, InRegion (s0.readReg64 .x1 + 0x88#64) 8 a →
      (m_pre.perm a).r = true ∧ m_pre.isLazyFree a = false :=
    fun a ha => hP_pre (hrw_hm a (by unfold InRegion at ha ⊢; bv_omega))
  have hd_hm64_fsp : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_hm64_ist : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x40#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_hm64_ost : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x68#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_hm64_obl : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x88#64) 8 := by
    unfold DisjointRegions; bv_omega
  have hframe_s2 : S2Frame s0.mem s2.mem
      [(s0.readReg64 .x0, 32), (s0.readReg64 .x1, 0x90), (s0.sp - 320#64, 320)] := by
    have hag_pre : AgreesOutside s.mem m_pre (s0.readReg64 .x1 + BitVec.ofNat 64 msg.length) 1 := by
      dsimp only [m_pre]; agrees_outside_writes
    have hf1 : S2Frame s0.mem m_pre
        [(s0.readReg64 .x0, 32), (s0.readReg64 .x1, 0x90), (s0.sp - 320#64, 320)] := by
      have := hpre.msg_lt
      exact S2Frame.trans_agreesOutside_sub hframe (rbase := s0.readReg64 .x1) (rlen := 0x90)
        (by simp) (by bv_omega) hag_pre
    have hs2_frame' : S2Frame m_pre s2.mem [(dst, len)] := by
      simpa only [mem_setMem, arm64_norm] using hs2_frame
    refine hf1.trans (hs2_frame'.mono fun a ha => ?_)
    intro r hr_mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr_mem
    subst hr_mem
    have ha_hm := ha (s0.readReg64 .x1, 0x90) (by simp)
    have := hpre.msg_lt; dsimp only [dst, len]
    unfold OutsideRegion at ha_hm ⊢; bv_omega
  have hag_on' : AgreesOn
      (fun a => (m_pre.perm a).r = true ∧ m_pre.isLazyFree a = false)
      s2.mem (m_pre.writeBytes dst (List.replicate len 0#8)) := by
    simpa only [mem_setMem, arm64_norm] using hag_on
  refine
    { pc_eq := hpc2
      common :=
        { status := hstat2
          sp_eq := (CallingConventionPreserved.sp_eq hcc2).trans (by fin_reg_local)
          x29_eq := (CallingConventionPreserved.x29 hcc2).trans (by fin_reg_local)
          x26_eq := (CallingConventionPreserved.x26 hcc2).trans (by fin_reg_local)
          x27_eq := (CallingConventionPreserved.x27 hcc2).trans (by fin_reg_local)
          x28_eq := (CallingConventionPreserved.x28 hcc2).trans (by fin_reg_local)
          saved := AgreesOn.finSaved_of hag_on' (FinSaved.of_agreesOutside hsaved hag_pad hd_hm64_fsp) hP_saved
          frame := hframe_s2 }
      x19_eq := (CallingConventionPreserved.x19 hcc2).trans (by fin_reg_local)
      x20_eq := (CallingConventionPreserved.x20 hcc2).trans (by fin_reg_local)
      x21_eq := (CallingConventionPreserved.x21 hcc2).trans (by fin_reg_local)
      x22_eq := (CallingConventionPreserved.x22 hcc2).trans (by fin_reg_local)
      x23_eq := (CallingConventionPreserved.x23 hcc2).trans (by fin_reg_local)
      x24_eq := (CallingConventionPreserved.x24 hcc2).trans (by fin_reg_local)
      x25_eq := (CallingConventionPreserved.x25 hcc2).trans (by dsimp only [len]; fin_reg_local)
      buf_eq := (AgreesOn.readBytes_eq hag_on' (s0.readReg64 .x1) 64 (by decide) hP_hm64).trans
        (readBytes_64_after_pad_memset s.mem (s0.readReg64 .x1) msg hmsg_eq hpre.msg_lt)
      ist_eq := (AgreesOn.readBytes_eq hag_on' (s0.readReg64 .x1 + 0x40#64) 32 (by decide) hP_ist).trans
        ((hag_pad.readBytes_eq hd_hm64_ist (by decide)).trans hin_eq)
      ost_eq := (AgreesOn.readBytes_eq hag_on' (s0.readReg64 .x1 + 0x68#64) 32 (by decide) hP_ost).trans
        ((hag_pad.readBytes_eq hd_hm64_ost (by decide)).trans hout_eq)
      obl_eq := (AgreesOn.read64_eq hag_on' (s0.readReg64 .x1 + 0x88#64) hP_obl).trans
        ((hag_pad.read64_eq hd_hm64_obl).trans hobl_eq) }

private theorem seg2a_123 [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    {key msg : List (BitVec 8)} {s0 s : State}
    (hpre : FinPreSat finPlacedFakeB C.F key msg s0)
    (hs : StateF1Sat C.F key msg s0 s) :
    RunsToVm ((blkPC_123).rebase (blkPl_123).base H) s (StateF2Sat C.F key msg s0) := by
  apply runsToVm_of_from
  rcases hs with ⟨hpc, hcom, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hbuf, hist, host, hobl⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := hframe.rw_of_rw _ _ hpre.rw_hm
  have hrw_stk320 : s.mem.RW (s0.sp - 320#64) 320 := hframe.rw_of_rw _ _ hpre.rw_stk320
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := hrw_stk320.sub (by bv_omega)
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  have hult_7 := ult_7_of_lt_56 hpre.msg_lt
  obtain ⟨hbit_len1, hbit_len2⟩ := bit_len_inner_eq hpre.msg_lt
  have hd_hm64_fsp64 : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64) 64 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  iterate 6 s2_step_vm
  have hread32 := fun u0 u1 u2 u3 w56 =>
    read64_seg2a_mid s.mem _ _ u0 u1 u2 u3 w56 32#64 (by decide) hd_hm64_fsp64
  have hread40 := fun u0 u1 u2 u3 w56 =>
    read64_seg2a_mid s.mem _ _ u0 u1 u2 u3 w56 40#64 (by decide) hd_hm64_fsp64
  have hread48 := fun u0 u1 u2 u3 w56 =>
    read64_seg2a_mid s.mem _ _ u0 u1 u2 u3 w56 48#64 (by decide) hd_hm64_fsp64
  iterate 7 s2_step_vm
  clear hread32 hread40 hread48
  refine runsToVmFrom_refl ?_
  obtain ⟨hag1, hag2, hag3⟩ := agreesOutside_seg2a s.mem (s0.readReg64 .x1) (s0.sp - 144#64)
    _ _ _ _ _ _ _ _ _
  have hd_fsp64_saved : DisjointRegions (s0.sp - 144#64) 64 (s0.sp - 144#64 + 0x40#64) 0x50 := by
    unfold DisjointRegions; bv_omega
  have hd_hm64_saved : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_fsp64_ist : DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1 + 0x40#64) 32 :=
    (hpre.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_hm64_ist : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x40#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_fsp64_ost : DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1 + 0x68#64) 32 :=
    (hpre.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_hm64_ost : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x68#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_fsp64_obl : DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1 + 0x88#64) 8 :=
    (hpre.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_hm64_obl : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x88#64) 8 := by
    unfold DisjointRegions; bv_omega
  refine
    { pc_eq := by fin_reg_local
      common :=
        { status := by fin_reg_local, sp_eq := by fin_reg_local, x29_eq := by fin_reg_local,
          x26_eq := by fin_reg_local, x27_eq := by fin_reg_local, x28_eq := by fin_reg_local,
          saved := by
            rw [mem_setMem]
            exact FinSaved.of_agreesOutside
              (FinSaved.of_agreesOutside (FinSaved.of_agreesOutside hsaved hag1 hd_fsp64_saved)
                hag2 hd_hm64_saved) hag3 hd_fsp64_saved
          frame := by
            rw [mem_setMem]
            exact hframe.trans (s2Frame_144_to_320
              (S2Frame.of_frame (frame_seg2a (Frame.refl s.mem _) hag1 hag2 hag3))) }
      x0_eq := by fin_reg_local, x1_eq := by fin_reg_local, x2_eq := by fin_reg_local,
      x19_eq := by fin_reg_local, x20_eq := by fin_reg_local,
      x21_eq := by fin_reg_local, x22_eq := by fin_reg_local
      blk_eq := by
        rw [mem_setMem]
        refine (readBytes_fsp_64_seg2 _ _ _ _ _ _ _ _ _ _ _ _ hd_hm64_fsp64).trans ?_
        rw [toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64,
            toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_rev64,
            readBytes_56_eq_append_8 s.mem (s0.readReg64 .x1),
            readBytes_56_of_buf_eq s.mem (s0.readReg64 .x1) msg hbuf hpre.msg_lt]
        rfl
      ist_eq := by
        rw [mem_setMem]
        exact (hag3.readBytes_eq hd_fsp64_ist (by decide)).trans
          ((hag2.readBytes_eq hd_hm64_ist (by decide)).trans
            ((hag1.readBytes_eq hd_fsp64_ist (by decide)).trans hist))
      ost_eq := by
        rw [mem_setMem]
        exact (hag3.readBytes_eq hd_fsp64_ost (by decide)).trans
          ((hag2.readBytes_eq hd_hm64_ost (by decide)).trans
            ((hag1.readBytes_eq hd_fsp64_ost (by decide)).trans host))
      obl_eq := by
        rw [mem_setMem]
        exact (hag3.read64_eq hd_fsp64_obl).trans
          ((hag2.read64_eq hd_hm64_obl).trans
            ((hag1.read64_eq hd_fsp64_obl).trans hobl)) }

private theorem seg2b_123 [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [hH : HkdfPlacedHooksExactBudgetSat C.F H]
    {key msg : List (BitVec 8)} {s0 s : State}
    (hpre : FinPreSat finPlacedFakeB C.F key msg s0)
    (hs : StateF2Sat C.F key msg s0 s) :
    RunsToVm ((blkPC_123).rebase (blkPl_123).base H) s (StateF3Sat C.F key msg s0) := by
  apply runsToVm_of_from
  rcases hs with ⟨hpc, hcom, hx0, hx1, hx2, hx19, hx20, hx21, hx22, hblk, hist, host, hobl⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := hframe.rw_of_rw _ _ hpre.rw_hm
  have hrw_ist : s.mem.RW (s0.readReg64 .x1 + 0x40#64) 32 := hrw_hm.sub (by bv_omega)
  have hrw_stk320 : s.mem.RW (s0.sp - 320#64) 320 := hframe.rw_of_rw _ _ hpre.rw_stk320
  have hsp_sub176 : s.sp - 176#64 = s0.sp - 320#64 := by rw [hsp]; bv_omega
  have hrw_c256 : s.mem.RW (s.sp - 176#64) 176 := by
    rw [hsp_sub176]; exact hrw_stk320.sub (by bv_omega)
  have hread_blk : s.mem.Readable (s0.sp - 144#64) 64 :=
    Memory.RW.readable (hrw_stk320.sub (by bv_omega))
  have hd_ist_c256 : DisjointRegions (s0.readReg64 .x1 + 0x40#64) 32 (s.sp - 176#64) 176 := by
    rw [hsp_sub176]
    unfold DisjointRegions; have := hpre.disj_hm_stk320; unfold DisjointRegions at this; bv_omega
  have hd_ist_blk : DisjointRegions (s0.readReg64 .x1 + 0x40#64) 32 (s0.sp - 144#64) 64 := by
    unfold DisjointRegions; have := hpre.disj_hm_fsp; unfold DisjointRegions at this; bv_omega
  have hd_c256_blk : DisjointRegions (s.sp - 176#64) 176 (s0.sp - 144#64) 64 := by
    rw [hsp_sub176]; unfold DisjointRegions; bv_omega
  s2_step_vm
  refine s2_compress256_step_vm_of_hookSat hH.compress256
    (stPtr := s0.readReg64 .x1 + 0x40#64) (blkPtr := s0.sp - 144#64)
    (lr := (blkPl_123).base + 180#64) (st := hmacInnerInit C.F key) (blk := innerLastBlock msg)
    hstat rfl
    (by fin_reg_local) (by fin_reg_local) (by fin_reg_local) rfl
    (by simp only [arm64_norm, hsp]; exact hpre.sp_aligned)
    hist hblk (innerLastBlock_length hpre.msg_lt)
    hrw_ist (by simpa only [arm64_norm] using hrw_c256) hread_blk
    (by simpa only [arm64_norm] using hd_ist_c256) hd_ist_blk
    (by simpa only [arm64_norm] using hd_c256_blk)
    fun s2 htr2 hpc2 hstat2 hcc2 _ _ _ hread_ist hs2_frame hag_on => ?_
  refine runsToVmFrom_refl ?_ htr2
  set blk_in := shaStateBytes (C.F (hmacInnerInit C.F key) (innerLastBlock msg))
  have hag_comp : AgreesOutside s.mem (s.mem.writeBytes (s0.readReg64 .x1 + 0x40#64) blk_in)
      (s0.readReg64 .x1 + 0x40#64) 32 := by
    have hlen : blk_in.length = 32 := shaStateBytes_length _
    rw [← hlen]
    exact ProofLib.AgreesOutside.writeBytes_self s.mem _ blk_in
  have hag_on' : AgreesOn
      (fun a => (s.mem.perm a).r = true ∧ s.mem.isLazyFree a = false ∧
        OutsideRegion (s0.sp - 320#64) 176 a)
      s2.mem (s.mem.writeBytes (s0.readReg64 .x1 + 0x40#64) blk_in) := by
    simpa only [arm64_norm, hsp_sub176] using hag_on
  have hP_rw : ∀ {a : BitVec 64}, s.mem.permNoLazy a = some Perm.rw →
      OutsideRegion (s0.sp - 320#64) 176 a →
      (s.mem.perm a).r = true ∧ s.mem.isLazyFree a = false ∧ OutsideRegion (s0.sp - 320#64) 176 a := by
    intro a hnl hout_a
    obtain ⟨hrw_a, hlf_a⟩ := Memory.permNoLazy_eq_some_rw_iff.mp hnl
    exact ⟨by rw [hrw_a]; rfl, hlf_a, hout_a⟩
  have hP_saved : ∀ a, InRegion (s0.sp - 144#64 + 0x40#64) 0x50 a →
      (s.mem.perm a).r = true ∧ s.mem.isLazyFree a = false ∧ OutsideRegion (s0.sp - 320#64) 176 a :=
    fun a ha => hP_rw (hrw_stk320 a (by unfold InRegion at ha ⊢; bv_omega))
      (by unfold InRegion at ha; unfold OutsideRegion; bv_omega)
  have hd_hm_c256 : DisjointRegions (s0.readReg64 .x1) 0x90 (s0.sp - 320#64) 176 := by
    have := hpre.disj_hm_stk320; unfold DisjointRegions at this ⊢; bv_omega
  have hP_ost : ∀ a, InRegion (s0.readReg64 .x1 + 0x68#64) 32 a →
      (s.mem.perm a).r = true ∧ s.mem.isLazyFree a = false ∧ OutsideRegion (s0.sp - 320#64) 176 a :=
    fun a ha =>
      have ha_hm : InRegion (s0.readReg64 .x1) 0x90 a := by unfold InRegion at ha ⊢; bv_omega
      hP_rw (hrw_hm a ha_hm) (by unfold DisjointRegions at hd_hm_c256; unfold InRegion at ha_hm; unfold OutsideRegion; bv_omega)
  have hP_obl : ∀ a, InRegion (s0.readReg64 .x1 + 0x88#64) 8 a →
      (s.mem.perm a).r = true ∧ s.mem.isLazyFree a = false ∧ OutsideRegion (s0.sp - 320#64) 176 a :=
    fun a ha =>
      have ha_hm : InRegion (s0.readReg64 .x1) 0x90 a := by unfold InRegion at ha ⊢; bv_omega
      hP_rw (hrw_hm a ha_hm) (by unfold DisjointRegions at hd_hm_c256; unfold InRegion at ha_hm; unfold OutsideRegion; bv_omega)
  have hd_ist_saved : DisjointRegions (s0.readReg64 .x1 + 0x40#64) 32 (s0.sp - 144#64 + 0x40#64) 0x50 := by
    have := hpre.disj_hm_fsp; unfold DisjointRegions at this ⊢; bv_omega
  have hd_ist_ost : DisjointRegions (s0.readReg64 .x1 + 0x40#64) 32 (s0.readReg64 .x1 + 0x68#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_ist_obl : DisjointRegions (s0.readReg64 .x1 + 0x40#64) 32 (s0.readReg64 .x1 + 0x88#64) 8 := by
    unfold DisjointRegions; bv_omega
  have hframe_s2 : S2Frame s0.mem s2.mem
      [(s0.readReg64 .x0, 32), (s0.readReg64 .x1, 0x90), (s0.sp - 320#64, 320)] := by
    have hs2_frame' : S2Frame s.mem s2.mem
        [(s0.readReg64 .x1 + 0x40#64, 32), (s0.sp - 320#64, 176)] := by
      simpa only [arm64_norm, hsp_sub176] using hs2_frame
    refine hframe.trans (hs2_frame'.mono fun a ha r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have ha_hm := ha (s0.readReg64 .x1, 0x90) (by simp)
      unfold OutsideRegion at ha_hm ⊢; bv_omega
    · have ha_stk := ha (s0.sp - 320#64, 320) (by simp)
      unfold OutsideRegion at ha_stk ⊢; bv_omega
  refine
    { pc_eq := hpc2
      common :=
        { status := hstat2
          sp_eq := (CallingConventionPreserved.sp_eq hcc2).trans (by fin_reg_local)
          x29_eq := (CallingConventionPreserved.x29 hcc2).trans (by fin_reg_local)
          x26_eq := (CallingConventionPreserved.x26 hcc2).trans (by fin_reg_local)
          x27_eq := (CallingConventionPreserved.x27 hcc2).trans (by fin_reg_local)
          x28_eq := (CallingConventionPreserved.x28 hcc2).trans (by fin_reg_local)
          saved := AgreesOn.finSaved_of hag_on' (FinSaved.of_agreesOutside hsaved hag_comp hd_ist_saved) hP_saved
          frame := hframe_s2 }
      x19_eq := (CallingConventionPreserved.x19 hcc2).trans (by fin_reg_local)
      x20_eq := (CallingConventionPreserved.x20 hcc2).trans (by fin_reg_local)
      x21_eq := (CallingConventionPreserved.x21 hcc2).trans (by fin_reg_local)
      x22_eq := (CallingConventionPreserved.x22 hcc2).trans (by fin_reg_local)
      ist_eq := hread_ist
      ost_eq := (AgreesOn.readBytes_eq hag_on' (s0.readReg64 .x1 + 0x68#64) 32 (by decide) hP_ost).trans
        ((hag_comp.readBytes_eq hd_ist_ost (by decide)).trans host)
      obl_eq := (AgreesOn.read64_eq hag_on' (s0.readReg64 .x1 + 0x88#64) hP_obl).trans
        ((hag_comp.read64_eq hd_ist_obl).trans hobl) }

private theorem seg3a_123 [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    {key msg : List (BitVec 8)} {s0 s : State}
    (hpre : FinPreSat finPlacedFakeB C.F key msg s0)
    (hs : StateF3Sat C.F key msg s0 s) :
    RunsToVm ((blkPC_123).rebase (blkPl_123).base H) s (StateF3bSat C.F key msg s0) := by
  apply runsToVm_of_from
  rcases hs with ⟨hpc, hcom, hx19, hx20, hx21, hx22, hist, host, hobl⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := hframe.rw_of_rw _ _ hpre.rw_hm
  have hrw_stk320 : s.mem.RW (s0.sp - 320#64) 320 := hframe.rw_of_rw _ _ hpre.rw_stk320
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := hrw_stk320.sub (by bv_omega)
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  set h_in := C.F (hmacInnerInit C.F key) (innerLastBlock msg)
  obtain ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7⟩ :=
    read32_words_at_64_of_shaStateBytes s.mem (s0.readReg64 .x1) h_in hist
  have hd_hm64_fsp64 : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64) 64 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hrev768 : rev64 (256#64 ||| 512#64) = 0x0003000000000000#64 := by decide
  have hread32 := fun w0 w1 w2 w3 w4 w5 w6 w7 u0 u1 u2 u3 =>
    read64_seg3a_pad_32 s.mem _ _ w0 w1 w2 w3 w4 w5 w6 w7 u0 u1 u2 u3 hd_hm64_fsp64
  have hread40 := fun w0 w1 w2 w3 w4 w5 w6 w7 u0 u1 u2 u3 =>
    read64_seg3a_pad_40 s.mem _ _ w0 w1 w2 w3 w4 w5 w6 w7 u0 u1 u2 u3 hd_hm64_fsp64
  iterate 31 s2_step_vm
  clear hread32 hread40
  refine runsToVmFrom_refl ?_
  obtain ⟨hag1, hag2, hag3, hag4⟩ := agreesOutside_seg3a s.mem (s0.readReg64 .x1) (s0.sp - 144#64)
    _ _ _ _ _ _ _ _ _ _ _ _ 0#64 0x0003000000000000#64 0x80#64 0#64 0#64 0x0003000000000000#64
  have hd_fsp64_saved : DisjointRegions (s0.sp - 144#64) 64 (s0.sp - 144#64 + 0x40#64) 0x50 := by
    unfold DisjointRegions; bv_omega
  have hd_hm64_saved : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_fsp64_ost : DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1 + 0x68#64) 32 :=
    (hpre.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_hm64_ost : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x68#64) 32 := by
    unfold DisjointRegions; bv_omega
  refine
    { pc_eq := by fin_reg_local
      common :=
        { status := by fin_reg_local, sp_eq := by fin_reg_local, x29_eq := by fin_reg_local,
          x26_eq := by fin_reg_local, x27_eq := by fin_reg_local, x28_eq := by fin_reg_local,
          saved := by
            rw [mem_setMem]
            exact finSaved_seg3a hsaved hag1 hag2 hag3 hag4 hd_hm64_saved hd_fsp64_saved
          frame := by
            rw [mem_setMem]
            exact hframe.trans (s2Frame_144_to_320
              (S2Frame.of_frame (frame_seg3a (Frame.refl s.mem _) hag1 hag2 hag3 hag4))) }
      x0_eq := by fin_reg_local, x1_eq := by fin_reg_local, x2_eq := by fin_reg_local,
      x19_eq := by fin_reg_local, x20_eq := by fin_reg_local
      blk_eq := by
        rw [mem_setMem]
        refine (readBytes_fsp_64_seg3 _ _ _ _ _ _ _ _ _ _ _ _ _ hd_hm64_fsp64).trans ?_
        rw [toLEBytes_8_rev32_append, toLEBytes_8_rev32_append,
            toLEBytes_8_rev32_append, toLEBytes_8_rev32_append]
        have htail : toLEBytes 8 0x80#64 ++ toLEBytes 8 0#64 ++ toLEBytes 8 0#64 ++
            toLEBytes 8 (rev64 768#64) =
            [0x80#8] ++ List.replicate 23 0#8 ++ toBEBytes 8 768#64 := by decide
        unfold outerBlock
        rw [digestBytes_eq_append h_in]
        simp only [List.append_assoc] at htail ⊢
        rw [htail]; rfl
      ost_eq := by
        rw [mem_setMem]
        exact ost_eq_seg3a host hag1 hag2 hag3 hag4 hd_hm64_ost hd_fsp64_ost }

private theorem seg3b_123 [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [hH : HkdfPlacedHooksExactBudgetSat C.F H]
    {key msg : List (BitVec 8)} {s0 s : State}
    (hpre : FinPreSat finPlacedFakeB C.F key msg s0)
    (hs : StateF3bSat C.F key msg s0 s) :
    RunsToVm ((blkPC_123).rebase (blkPl_123).base H) s (StateF4Sat C.F key msg s0) := by
  apply runsToVm_of_from
  rcases hs with ⟨hpc, hcom, hx0, hx1, hx2, hx19, hx20, hblk, host⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := hframe.rw_of_rw _ _ hpre.rw_hm
  have hrw_ost : s.mem.RW (s0.readReg64 .x1 + 0x68#64) 32 := hrw_hm.sub (by bv_omega)
  have hrw_stk320 : s.mem.RW (s0.sp - 320#64) 320 := hframe.rw_of_rw _ _ hpre.rw_stk320
  have hal_fsp : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  have hsp_sub176 : s.sp - 176#64 = s0.sp - 320#64 := by rw [hsp]; bv_omega
  have hrw_c256 : s.mem.RW (s.sp - 176#64) 176 := by
    rw [hsp_sub176]; exact hrw_stk320.sub (by bv_omega)
  have hread_blk : s.mem.Readable (s0.sp - 144#64) 64 :=
    Memory.RW.readable (hrw_stk320.sub (by bv_omega))
  have hd_ost_c256 : DisjointRegions (s0.readReg64 .x1 + 0x68#64) 32 (s.sp - 176#64) 176 := by
    rw [hsp_sub176]
    have := hpre.disj_hm_stk320; unfold DisjointRegions at this ⊢; bv_omega
  have hd_ost_blk : DisjointRegions (s0.readReg64 .x1 + 0x68#64) 32 (s0.sp - 144#64) 64 := by
    have := hpre.disj_hm_fsp; unfold DisjointRegions at this ⊢; bv_omega
  have hd_c256_blk : DisjointRegions (s.sp - 176#64) 176 (s0.sp - 144#64) 64 := by
    rw [hsp_sub176]; unfold DisjointRegions; bv_omega
  set h_in := C.F (hmacInnerInit C.F key) (innerLastBlock msg)
  s2_step_vm
  refine s2_compress256_step_vm_of_hookSat hH.compress256
    (stPtr := s0.readReg64 .x1 + 0x68#64) (blkPtr := s0.sp - 144#64)
    (lr := (blkPl_123).base + 308#64) (st := hmacOuterInit C.F key) (blk := outerBlock (digestBytes h_in))
    hstat rfl
    (by fin_reg_local) (by fin_reg_local) (by fin_reg_local) rfl
    (by simp only [arm64_norm, hsp]; exact hpre.sp_aligned)
    host hblk (outerBlock_digestBytes_length h_in)
    hrw_ost (by simpa only [arm64_norm] using hrw_c256) hread_blk
    (by simpa only [arm64_norm] using hd_ost_c256) hd_ost_blk
    (by simpa only [arm64_norm] using hd_c256_blk)
    fun s2 htr2 hpc2 hstat2 hcc2 _ _ _ hread_ost hs2_frame hag_on => ?_
  refine runsToVmFrom_refl ?_ htr2
  set blk_out := shaStateBytes (C.F (hmacOuterInit C.F key) (outerBlock (digestBytes h_in)))
  have hag_comp : AgreesOutside s.mem (s.mem.writeBytes (s0.readReg64 .x1 + 0x68#64) blk_out)
      (s0.readReg64 .x1 + 0x68#64) 32 := by
    have hlen : blk_out.length = 32 := shaStateBytes_length _
    rw [← hlen]
    exact ProofLib.AgreesOutside.writeBytes_self s.mem _ blk_out
  have hag_on' : AgreesOn
      (fun a => (s.mem.perm a).r = true ∧ s.mem.isLazyFree a = false ∧
        OutsideRegion (s0.sp - 320#64) 176 a)
      s2.mem (s.mem.writeBytes (s0.readReg64 .x1 + 0x68#64) blk_out) := by
    simpa only [arm64_norm, hsp_sub176] using hag_on
  have hP_saved : ∀ a, InRegion (s0.sp - 144#64 + 0x40#64) 0x50 a →
      (s.mem.perm a).r = true ∧ s.mem.isLazyFree a = false ∧ OutsideRegion (s0.sp - 320#64) 176 a := by
    intro a ha
    have hnl := hrw_stk320 a (by unfold InRegion at ha ⊢; bv_omega)
    obtain ⟨hrw_a, hlf_a⟩ := Memory.permNoLazy_eq_some_rw_iff.mp hnl
    exact ⟨by rw [hrw_a]; rfl, hlf_a, by unfold InRegion at ha; unfold OutsideRegion; bv_omega⟩
  have hd_ost_saved : DisjointRegions (s0.readReg64 .x1 + 0x68#64) 32 (s0.sp - 144#64 + 0x40#64) 0x50 := by
    have := hpre.disj_hm_fsp; unfold DisjointRegions at this ⊢; bv_omega
  have hframe_s2 : S2Frame s0.mem s2.mem
      [(s0.readReg64 .x0, 32), (s0.readReg64 .x1, 0x90), (s0.sp - 320#64, 320)] := by
    have hs2_frame' : S2Frame s.mem s2.mem
        [(s0.readReg64 .x1 + 0x68#64, 32), (s0.sp - 320#64, 176)] := by
      simpa only [arm64_norm, hsp_sub176] using hs2_frame
    refine hframe.trans (hs2_frame'.mono fun a ha r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have ha_hm := ha (s0.readReg64 .x1, 0x90) (by simp)
      unfold OutsideRegion at ha_hm ⊢; bv_omega
    · have ha_stk := ha (s0.sp - 320#64, 320) (by simp)
      unfold OutsideRegion at ha_stk ⊢; bv_omega
  refine
    { pc_eq := hpc2
      common :=
        { status := hstat2
          sp_eq := (CallingConventionPreserved.sp_eq hcc2).trans (by fin_reg_local)
          x29_eq := (CallingConventionPreserved.x29 hcc2).trans (by fin_reg_local)
          x26_eq := (CallingConventionPreserved.x26 hcc2).trans (by fin_reg_local)
          x27_eq := (CallingConventionPreserved.x27 hcc2).trans (by fin_reg_local)
          x28_eq := (CallingConventionPreserved.x28 hcc2).trans (by fin_reg_local)
          saved := AgreesOn.finSaved_of hag_on' (FinSaved.of_agreesOutside hsaved hag_comp hd_ost_saved) hP_saved
          frame := hframe_s2 }
      x19_eq := (CallingConventionPreserved.x19 hcc2).trans (by fin_reg_local)
      x20_eq := (CallingConventionPreserved.x20 hcc2).trans (by fin_reg_local)
      ost_eq := hread_ost }

private theorem seg4a_123 [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    {key msg : List (BitVec 8)} {s0 s : State}
    (hpre : FinPreSat finPlacedFakeB C.F key msg s0)
    (hs : StateF4Sat C.F key msg s0 s) :
    RunsToVm ((blkPC_123).rebase (blkPl_123).base H) s (StateF5Sat C.F key msg s0) := by
  apply runsToVm_of_from
  rcases hs with ⟨hpc, hcom, hx19, hx20, host⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := hframe.rw_of_rw _ _ hpre.rw_hm
  have hrw_stk320 : s.mem.RW (s0.sp - 320#64) 320 := hframe.rw_of_rw _ _ hpre.rw_stk320
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := hrw_stk320.sub (by bv_omega)
  have hrw_out : s.mem.RW (s0.readReg64 .x0) 32 := hframe.rw_of_rw _ _ hpre.rw_out
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  set h_out := C.F (hmacOuterInit C.F key)
    (outerBlock (digestBytes (C.F (hmacInnerInit C.F key) (innerLastBlock msg))))
  obtain ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7⟩ :=
    read32_words_at_104_of_shaStateBytes s.mem (s0.readReg64 .x1) h_out host
  have hzero64 : (0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 : BitVec 64) = 0#64 := rfl
  iterate 11 s2_step_vm
  have hd_fsp64_hm := (seg4a_disj hpre.toFinPre).1
  have hread128 := read32_seg4a_mid_x s.mem (s0.readReg64 .x1) (s0.sp - 144#64) 128#64 (h_out.get 6)
    (Or.inl rfl) hd_fsp64_hm hw6
  have hread132 := read32_seg4a_mid_x s.mem (s0.readReg64 .x1) (s0.sp - 144#64) 132#64 (h_out.get 7)
    (Or.inr rfl) hd_fsp64_hm hw7
  iterate 2 s2_step_vm
  clear hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hread128 hread132 hd_fsp64_hm host
  iterate 15 s2_step_vm
  refine runsToVmFrom_refl ?_
  obtain ⟨hag1, hag2, hag3, hag4⟩ := agreesOutside_seg4a s.mem
    (s0.readReg64 .x0) (s0.readReg64 .x1) (s0.sp - 144#64) _ _ _ _ _ _ _ _
  obtain ⟨_, hd_hm_saved, hd_fsp64_saved, hd_out_saved⟩ := seg4a_disj hpre.toFinPre
  refine
    { pc_eq := by fin_reg_local
      common :=
        { status := by fin_reg_local, sp_eq := by fin_reg_local, x29_eq := by fin_reg_local,
          x26_eq := by fin_reg_local, x27_eq := by fin_reg_local, x28_eq := by fin_reg_local,
          saved := by
            rw [mem_setMem]
            exact finSaved_seg4a hsaved hag1 hag2 hag3 hag4 hd_hm_saved hd_fsp64_saved hd_out_saved
          frame := by
            rw [mem_setMem]
            exact hframe.trans (s2Frame_144_to_320
              (S2Frame.of_frame (frame_seg4a (Frame.refl s.mem _) hag1 hag2 hag3 hag4))) }
      out_eq := by
        rw [mem_setMem]
        exact (readBytes_write32_8_digestBytes _ (s0.readReg64 .x0) h_out _ _ _ _ _ _ _ _
          (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _)
          (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _)).trans
          (hmacWith_short C.F key msg hpre.key_le hpre.msg_lt).symm }

private theorem seg4b_123 [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    {key msg : List (BitVec 8)} {s0 s : State}
    (hpre : FinPreSat finPlacedFakeB C.F key msg s0)
    (hs : StateF5Sat C.F key msg s0 s) :
    RunsToVm ((blkPC_123).rebase (blkPl_123).base H) s (FinPostSat C.F key msg s0) := by
  apply runsToVm_of_from
  rcases hs with ⟨hpc, hcom, hout⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_stk320 : s.mem.RW (s0.sp - 320#64) 320 := hframe.rw_of_rw _ _ hpre.rw_stk320
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := hrw_stk320.sub (by bv_omega)
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  rcases hsaved with ⟨hs29, hslr, hs25, hs24, hs23, hs22, hs21, hs20, hs19⟩
  have hs29' : s.mem.read64 (s0.sp - 144#64 + 64#64) = s0.readReg64 .x29 := hs29
  have hslr' : s.mem.read64 (s0.sp - 144#64 + 72#64) = s0.readReg64 .lr := hslr
  have hs25' : s.mem.read64 (s0.sp - 144#64 + 80#64) = s0.readReg64 .x25 := hs25
  have hs24' : s.mem.read64 (s0.sp - 144#64 + 96#64) = s0.readReg64 .x24 := hs24
  have hs23' : s.mem.read64 (s0.sp - 144#64 + 104#64) = s0.readReg64 .x23 := hs23
  have hs22' : s.mem.read64 (s0.sp - 144#64 + 112#64) = s0.readReg64 .x22 := hs22
  have hs21' : s.mem.read64 (s0.sp - 144#64 + 120#64) = s0.readReg64 .x21 := hs21
  have hs20' : s.mem.read64 (s0.sp - 144#64 + 128#64) = s0.readReg64 .x20 := hs20
  have hs19' : s.mem.read64 (s0.sp - 144#64 + 136#64) = s0.readReg64 .x19 := hs19
  iterate 7 s2_step_vm
  refine runsToVmFrom_refl ⟨by simp (config := { decide := true }) only [arm64_norm], hstat,
    ⟨by simp (config := { decide := true }) only [arm64_norm], fun r hr => ?_⟩, hout, hframe⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [arm64_norm, hx26, hx27, hx28, hs19', hs20', hs21', hs22', hs23', hs24', hs25', hs29', hslr']

/-- Full relocatable `RunsToVm` contract of `finalize_fixed` (Block `123`, `320`-B stack) under
`[HkdfPlacedHooksExactBudgetSat C.F H]` with `FinPostSat` (`S2Frame`). -/
public theorem finalize_fixed_placed_runsToVm_sat [LibsignalPlacement] {C : Crypto}
    {H : LibsignalHooks} [hH : HkdfPlacedHooksExactBudgetSat C.F H]
    {key msg : List (BitVec 8)} {s0 : State}
    (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (hpre : FinPreSat finPlacedFakeB C.F key msg s0) :
    RunsToVm ((blkPC_123).rebase (blkPl_123).base H) s0 (FinPostSat C.F key msg s0) :=
  (seg1a_123 hpre).trans fun _ hs1 =>
  (seg1b_123 hpre hs1).trans fun _ hs2 =>
  (seg2a_123 hpre hs2).trans fun _ hs3 =>
  (seg2b_123 hpre hs3).trans fun _ hs4 =>
  (seg3a_123 hpre hs4).trans fun _ hs5 =>
  (seg3b_123 hpre hs5).trans fun _ hs6 =>
  (seg4a_123 hpre hs6).trans fun _ hs7 =>
  seg4b_123 hpre hs7

end LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetAuxASat
