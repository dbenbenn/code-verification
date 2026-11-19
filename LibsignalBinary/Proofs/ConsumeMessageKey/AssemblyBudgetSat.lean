/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudget
import LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAuxSat
public import LibsignalBinary.Proofs.ConsumeMessageKey.HmacSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.RunOfCalleesBudgetSat -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.ConsumeMessageKey.CoupledCompress256Sat
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.CompressAndDigestExact
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.EntryAndKeyBlock
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.EntryAndKeyBlockExact
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceExact
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractCommon
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAux
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.DefsSat

/-!
# `HookSat`-Backed Budget-Threaded Refinement for `RatchetState::consume_message_key`

Proves the budget-threaded placed `hmac_sha256` and `consume_message_key` contracts assuming
`HookSatExactMemcpy`, `HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec`, and
`HookSatCompress256 H lsCompress256Sym F`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetSat

open Arm64 Arm64.Obj ProofLib
open CryptoGames.HMAC (ShaState hmacWith sha256IV)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (
  IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement LibsignalRoLoaded
  blkLib_eq_73 blkLib_eq_114
  blkPC_24 blkPC_73 blkPC_114 blkPl_24 blkPl_73 blkPl_114
  extract_withLsCodeLoaded libsignalRoLoaded_of_keepsFrozen
  libsignalSessionExterns libsignalSessionLib
  lsBlackBoxU8Sym lsNoAllocShimSym lsProg_73 lsProg_114 lsRustReallocSym
  ls_externAt?_blockProgram_eq_of_externs_eq ls_subroutine_ok_of_block
  lsmpl withLsCodeLoaded
)
open CryptoVerification.LibsignalAesCbc (toLEBytes)
open CryptoVerification.LibsignalHmac (shaStateBytes)
open CryptoVerification.LibsignalSession (blackBoxHook)
open CryptoVerification.LibsignalSession.CryptoHmacSha256 (
  CalleeSaved CallingConventionPreserved_of_calleeSaved Frame
  HmacPlacedPre HmacSaved HmacSt RW RunsTo StateH0Placed
  StateH1Placed StateH1pPlaced StateH2Placed
  disjointRegions_of_ro_rw hmacPlacedSpec hsp hsp_align innerState
  length_hmacWith lsCompress256Sym lsMemcpySym lsMemsetSym lsSha256IVAddr outerState
  read64_writeBytes_replicate_off_disjoint read64_writeBytes_replicate_zero_off
  readBytes_writeBytes_replicate_off_disjoint rodata_placed_sha256IV
  seg0a_placed_runsTo seg1a_placed_runsTo toLEBytes_8_read64_writeBytes_146_62
)
open CryptoVerification.LibsignalTripleRatchet.Extract (
  CallingConventionPreserved.x19 CallingConventionPreserved.x20
  CallingConventionPreserved.x21 CallingConventionPreserved.x22
  CallingConventionPreserved.x27 CallingConventionPreserved.x29 S2Frame
)
open CryptoVerification.LibsignalTripleRatchet.HkdfExt (AgreesOn)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved rustCliReallocBudgetSpec
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.ConsumeMessageKey.DefsBudget (GrowOnePlacedOk hmacSpec)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (
  CmkAllocHooks FindIndexPlacedOk HmacPlacedOk HmacPlacedRoOk
)
open LibsignalBinary.Proofs.ConsumeMessageKey.RunOfCalleesBudgetSat (
  CmkPlacedRunStmtSat consume_message_key_placed_ro_run_of_sat consume_message_key_placed_run_of_sat
)
open LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAux (
  hmacPlacedPre_stripS stripExecOutside_readBytes stripExecOutside_readable stripExecOutside_rw
  unstrip_frame
)
open LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAuxSat (
  placed_memset_budget_steps_sat
)
open LibsignalBinary.Proofs.ConsumeMessageKey.CoupledCompress256Sat (
  hmacCompressOnlyExcHooksSat hmacCompressOnlyExcHooksSat_compress
  hmacNoMemsetExcHooksSat hmacNoMemsetExcHooksSat_compress hmacNoMemsetExcHooksSat_memcpy
  runsTo_block_lift_vm_compress_only_sat runsTo_block_lift_vm_no_memset_sat
)
open LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.CompressAndDigestExact (
  hmac_tail_placed_runsTo_sat
)
open LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.DefsSat (
  hmacSaved_of_agreesOn s2Frame_of_hmacFrame
)
open LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.EntryAndKeyBlockExact (
  HmacPlacedPreSat hmacSaved_of_s2Frame seg1b1_placed_runsTo_exact
)
open LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceExact (
  new_from_slice_placed_run_exact
)
open LibsignalBinary.Proofs.ConsumeMessageKey.HmacSat (StateH2PlacedSat StateH5Sat)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore (
  HookSatExactMemcpy
)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat (
  CallingConventionPreserved.x23 CallingConventionPreserved.x24
  CallingConventionPreserved.x25 CallingConventionPreserved.x26 HookSatCompress256
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemsetRegionBudgetSpec)

attribute [local arm64_norm]
  MemWidth.bytes SimdMemSize.bytes
  Memory.read8_write8_base_off_disjoint
  Memory.read8_write8_base_zero_off
  Memory.read8_write8_base_off_zero
  Memory.read8_write64_base_off_disjoint
  Memory.read8_write64_base_zero_off
  Memory.read8_write64_base_off_zero
  Memory.read8_write64_base_off_inbounds

private theorem stripS_read8 (p : BitVec 64 → Bool) (s : State) (a : BitVec 64) :
    (ProofLib.stripS p s).mem.read8 a = s.mem.read8 a := by
  cases s; simp [ProofLib.stripS, ProofLib.strip_read8]

private theorem stripS_read64 (p : BitVec 64 → Bool) (s : State) (a : BitVec 64) :
    (ProofLib.stripS p s).mem.read64 a = s.mem.read64 a := by
  cases s; simp [ProofLib.stripS, Memory.read64, ProofLib.strip_read8]

private theorem stripExecOutside_hmacSt {F : ShaState → List (BitVec 8) → ShaState}
    {p : BitVec 64 → Bool} {m : Memory} {a : BitVec 64} {key msg : List (BitVec 8)} :
    CryptoVerification.LibsignalSession.CryptoHmacSha256.HmacSt
      (ProofLib.stripExecOutside p m) a F key msg ↔
    CryptoVerification.LibsignalSession.CryptoHmacSha256.HmacSt m a F key msg := by
  unfold CryptoVerification.LibsignalSession.CryptoHmacSha256.HmacSt
  simp only [stripExecOutside_readBytes, Memory.read64, ProofLib.strip_read8]

private theorem runsTo_73_to_bp [LibsignalPlacement] {X : LibsignalHooks}
    {s : State} {P : State → Prop} (h : RunsTo (lsProg_73 X) s P) :
    RunsTo (libsignalSessionLib.blockProgram lsmpl 73 X) s P := by
  rwa [← IsLsBlockProg.eq_blockProgram (prog := lsProg_73 X)]

private theorem steps_bp_to_73 [LibsignalPlacement] {X : LibsignalHooks} {s s' : State}
    (h : Steps (libsignalSessionLib.blockProgram lsmpl 73 X) s s') :
    Steps (lsProg_73 X) s s' := by
  rwa [IsLsBlockProg.eq_blockProgram (prog := lsProg_73 X)]

private theorem stripS_hmacSaved (p : BitVec 64 → Bool) (s0 s : State) :
    HmacSaved (ProofLib.stripS p s0) (hsp (ProofLib.stripS p s0)) (ProofLib.stripS p s).mem ↔
    HmacSaved s0 (hsp s0) s.mem := by
  have hsp0 : hsp (ProofLib.stripS p s0) = hsp s0 := by cases s0; rfl
  have hr : ∀ r, (ProofLib.stripS p s0).readReg64 r = s0.readReg64 r := fun _ => by cases s0; rfl
  unfold HmacSaved
  simp only [hsp0, stripS_read64, hr]

private theorem runsTo_114_to_bp [LibsignalPlacement] {X : LibsignalHooks}
    {s : State} {P : State → Prop} (h : RunsTo (lsProg_114 X) s P) :
    RunsTo (libsignalSessionLib.blockProgram lsmpl 114 X) s P := by
  rwa [← IsLsBlockProg.eq_blockProgram (prog := lsProg_114 X)]

private theorem steps_bp_to_114 [LibsignalPlacement] {X : LibsignalHooks} {s s' : State}
    (h : Steps (libsignalSessionLib.blockProgram lsmpl 114 X) s s') :
    Steps (lsProg_114 X) s s' := by
  rwa [IsLsBlockProg.eq_blockProgram (prog := lsProg_114 X)]

private theorem unstrip_s2Frame {p : BitVec 64 → Bool} {m m' : Memory}
    {regs : List (BitVec 64 × Nat)}
    (hf : S2Frame (ProofLib.stripExecOutside p m) (ProofLib.stripExecOutside p m') regs)
    (hperm : ∀ a, m'.perm a = m.perm a) :
    S2Frame m m' regs := by
  refine ⟨fun a hr hlf hout => ?_,
    ⟨⟨fun a hnl => ?_, fun a hrw => (hperm a).trans hrw⟩,
     ⟨fun a ⟨hm, han⟩ => ?_, fun a hpn hout => ⟨(hperm a).trans hpn, fun hlf => ?_⟩⟩⟩,
    fun a hr hlf => ?_⟩
  · have h := hf.1 a ((ProofLib.strip_perm_props p m a).1.trans hr)
      ((ProofLib.strip_isLazyFree p m a).trans hlf) hout
    simpa only [ProofLib.strip_read8] using h
  · obtain ⟨hrw, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp hnl
    have hnl' : (ProofLib.stripExecOutside p m).permNoLazy a = some Perm.rw :=
      Memory.permNoLazy_eq_some_rw_iff.mpr
        ⟨(ProofLib.strip_perm_props p m a).2.2.2.mpr hrw,
         (ProofLib.strip_isLazyFree p m a).trans hlf⟩
    obtain ⟨_, hlf2'⟩ := Memory.permNoLazy_eq_some_rw_iff.mp (hf.2.1.1.1 a hnl')
    exact Memory.permNoLazy_eq_some_rw_iff.mpr
      ⟨(hperm a).trans hrw, (ProofLib.strip_isLazyFree p m' a).symm.trans hlf2'⟩
  · obtain ⟨_, han2'⟩ := hf.2.1.2.1 a
      ⟨(ProofLib.strip_perm_props p m a).2.2.1.trans hm,
       (ProofLib.strip_isAnon p m a).trans han⟩
    exact ⟨by rw [hperm a]; exact hm, (ProofLib.strip_isAnon p m' a).symm.trans han2'⟩
  · have hpn' : (ProofLib.stripExecOutside p m).perm a = some Perm.protNone := by
      rw [ProofLib.strip_perm, hpn]; cases p a <;> rfl
    obtain ⟨hr8', hlf2'⟩ :=
      (hf.2.1.2.2 a hpn' hout).2 ((ProofLib.strip_isLazyFree p m a).trans hlf)
    exact ⟨by simpa only [ProofLib.strip_read8] using hr8',
      (ProofLib.strip_isLazyFree p m' a).symm.trans hlf2'⟩
  · obtain ⟨_, hlf2'⟩ := hf.2.2 a
      ((ProofLib.strip_perm_props p m a).1.trans hr)
      ((ProofLib.strip_isLazyFree p m a).trans hlf)
    exact ⟨by rw [hperm a]; exact hr, (ProofLib.strip_isLazyFree p m' a).symm.trans hlf2'⟩

theorem new_from_slice_placed_runsTo_vm_sat [LibsignalPlacement]
    {F : ShaCompress}
    {H : LibsignalHooks} (h_memcpy : HookSatExactMemcpy H lsMemcpySym)
    (h_compress : HookSatCompress256 H lsCompress256Sym F) {s₀ : State}
    (hpc : s₀.pc = (blkPl_114).base) (hstat : s₀.status = .Running)
    (hlen : (s₀.readReg64 .x2).toNat ≤ 64)
    (hiv : s₀.mem.readBytes lsSha256IVAddr 32 = shaStateBytes sha256IV)
    (hread_iv : s₀.mem.Readable lsSha256IVAddr 32)
    (hdisj_iv_stack : DisjointRegions lsSha256IVAddr 32 (s₀.sp - 720#64) 720)
    (hrw_out : RW s₀.mem (s₀.readReg64 .x0) 0x98)
    (hrw_stack : RW s₀.mem (s₀.sp - 720#64) 720)
    (hdisj_out_stack : DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 720#64) 720)
    (hread_key_s0 : s₀.mem.Readable (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat)
    (hdisj_key_stack : (s₀.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 720#64) 720)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64)
    (hL114 : (lsProg_114 H).CodeLoaded s₀.mem) :
    let key := s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
    ∃ sf : State,
      Steps (lsProg_114 H) s₀ sf ∧
      VmPreserved s₀ sf ∧
      sf.trace = s₀.trace ∧
      calleeSavedVRegs sf = calleeSavedVRegs s₀ ∧
      sf.pc = s₀.readReg64 .lr ∧ sf.status = .Running ∧ CalleeSaved s₀ sf ∧
      sf.mem.read64 (s₀.readReg64 .x0) = 0#64 ∧
      HmacSt sf.mem (s₀.readReg64 .x0 + 8#64) F key [] ∧
      S2Frame s₀.mem sf.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 720#64, 720)] := by
  intro key
  let kp114 := ProofLib.progKeep (libsignalSessionLib.blockProgram lsmpl 114 H)
  let Q114 := libsignalSessionLib.blockProgram lsmpl 114 (hmacNoMemsetExcHooksSat F H s₀.mem kp114)
  let kpQ := ProofLib.progKeep Q114
  have hmcQ := hmacNoMemsetExcHooksSat_memcpy (F := F) h_memcpy s₀.mem kp114
  have hc256Q := hmacNoMemsetExcHooksSat_compress h_compress s₀.mem kp114
  have hL_bp : (libsignalSessionLib.blockProgram lsmpl 114 H).CodeLoaded s₀.mem := by
    rwa [← IsLsBlockProg.eq_blockProgram (prog := lsProg_114 H)]
  have hm0 : (ProofLib.stripS kpQ s₀).mem = ProofLib.stripExecOutside kpQ s₀.mem := by cases s₀; rfl
  have hr0 : ∀ r, (ProofLib.stripS kpQ s₀).readReg64 r = s₀.readReg64 r := fun _ => by cases s₀; rfl
  have hsp0 : (ProofLib.stripS kpQ s₀).sp = s₀.sp := by cases s₀; rfl
  have hrunsP := runsTo_114_to_bp
    (new_from_slice_placed_run_exact h_memcpy h_compress hpc hstat hlen hiv hread_iv
      hdisj_iv_stack hrw_out hrw_stack hdisj_out_stack hread_key_s0 hdisj_key_stack hal)
  have hrunsQ := runsTo_114_to_bp
    (new_from_slice_placed_run_exact (s₀ := ProofLib.stripS kpQ s₀) hmcQ hc256Q
      (by cases s₀; exact hpc) (by cases s₀; exact hstat) (by rw [hr0]; exact hlen)
      (by rw [hm0, stripExecOutside_readBytes]; exact hiv)
      (by rw [hm0]; exact stripExecOutside_readable kpQ s₀.mem _ _ hread_iv)
      (by rw [hsp0]; exact hdisj_iv_stack)
      (by rw [hm0, hr0]; exact stripExecOutside_rw kpQ s₀.mem _ _ hrw_out)
      (by rw [hm0, hsp0]; exact stripExecOutside_rw kpQ s₀.mem _ _ hrw_stack)
      (by rw [hr0, hsp0]; exact hdisj_out_stack)
      (by rw [hm0, hr0, hr0]; exact stripExecOutside_readable kpQ s₀.mem _ _ hread_key_s0)
      (by rw [hr0, hr0, hsp0]; exact hdisj_key_stack)
      (by rw [hsp0]; exact hal))
  obtain ⟨sf, hsteps_bp, hvm, _, htr, hvregs, hsf_or⟩ :=
    runsTo_block_lift_vm_no_memset_sat h_memcpy h_compress blkLib_eq_114 rfl rfl hL_bp
      hrunsP hrunsQ (fun _ hs => hs.2.1) (fun _ hs => hs.2.1)
  refine ⟨sf, steps_bp_to_114 hsteps_bp, hvm, htr, hvregs, ?_⟩
  rcases hsf_or with hsf_strip | hsf_real
  · rcases hsf_strip with ⟨hpc_f, hstat_f, hcs_f, htag_f, hhmac_f, hframe_f⟩
    have hmf : (ProofLib.stripS kpQ sf).mem = ProofLib.stripExecOutside kpQ sf.mem := by cases sf; rfl
    have hkey_eq :
        (ProofLib.stripS kpQ s₀).mem.readBytes ((ProofLib.stripS kpQ s₀).readReg64 .x1)
          ((ProofLib.stripS kpQ s₀).readReg64 .x2).toNat = key := by
      rw [hm0, hr0, hr0, stripExecOutside_readBytes]
    rw [hm0, hmf, hr0, hsp0] at hframe_f
    rw [hmf, hr0, hkey_eq] at hhmac_f
    exact ⟨by rw [hr0] at hpc_f; cases sf; exact hpc_f,
      by cases sf; exact hstat_f,
      ⟨by cases s₀; cases sf; exact hcs_f.1,
       fun r hr => by have := hcs_f.2 r hr; cases s₀; cases sf; exact this⟩,
      by rw [hr0, stripS_read64] at htag_f; exact htag_f,
      stripExecOutside_hmacSt.mp hhmac_f,
      unstrip_s2Frame hframe_f hvm.perm_eq⟩
  · exact hsf_real

/-- Thread `VmPreserved` across Block 73 (`hmac_sha256`, `compress256`) and Block 114 (`new_from_slice`) under `HookSatExactMemcpy H lsMemcpySym`, `HookSat` for `memset`, and `HookSatCompress256 H lsCompress256Sym F`. -/
theorem hmac_placed_runsTo_vm_sat [LibsignalPlacement]
    {F : ShaCompress}
    {H : LibsignalHooks} (h_memcpy : HookSatExactMemcpy H lsMemcpySym)
    (h_memset : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec)
    (h_compress : HookSatCompress256 H lsCompress256Sym F)
    {key : List (BitVec 8)} {byte : BitVec 8} {s0 : State}
    (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (hpre : HmacPlacedPreSat F key [byte] s0)
    (hread_key : s0.mem.Readable (s0.readReg64 .x1) 32)
    (hL73 : (lsProg_73 H).CodeLoaded s0.mem) :
    ∃ sf : State,
      Steps (lsProg_73 H) s0 sf ∧
      VmPreserved s0 sf ∧
      sf.trace = s0.trace ∧
      calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
      StateH5Sat F key byte s0 sf := by
  have hpre1024 : HmacPlacedPre F key [byte] s0 := hpre.toHmacPlacedPre
  have heq73 : ∀ X, lsProg_73 X = libsignalSessionLib.blockProgram lsmpl 73 X :=
    fun X => IsLsBlockProg.eq_blockProgram (prog := lsProg_73 X)
  have heq114 : ∀ X, lsProg_114 X = libsignalSessionLib.blockProgram lsmpl 114 X :=
    fun X => IsLsBlockProg.eq_blockProgram (prog := lsProg_114 X)
  let kp73 := ProofLib.progKeep (libsignalSessionLib.blockProgram lsmpl 73 H)
  -- Piece 1: `seg0a_placed_runsTo` on Block `73` (`s0 → sc`, 0 extern calls)
  let Q73_0 := libsignalSessionLib.blockProgram lsmpl 73 (hmacCompressOnlyExcHooksSat F H s0.mem kp73)
  let kpQ0 := ProofLib.progKeep Q73_0
  have hL73_bp : (libsignalSessionLib.blockProgram lsmpl 73 H).CodeLoaded s0.mem := by
    rwa [← heq73 H]
  obtain ⟨sc, hsteps0a_bp, hvm0a, _, htr0a, hvregs0a, hsc_or⟩ :=
    runsTo_block_lift_vm_compress_only_sat h_compress blkLib_eq_73 rfl rfl hL73_bp
      (runsTo_73_to_bp (seg0a_placed_runsTo (H := H) hpre1024))
      (runsTo_73_to_bp (seg0a_placed_runsTo (H := hmacCompressOnlyExcHooksSat F H s0.mem kp73)
        (hmacPlacedPre_stripS kpQ0 hpre1024)))
      (fun _ (hs : StateH0Placed s0 _) => hs.common.1)
      (fun _ (hs : StateH0Placed (ProofLib.stripS kpQ0 s0) _) => hs.common.1)
  have hsteps0a : Steps (lsProg_73 H) s0 sc := steps_bp_to_73 hsteps0a_bp
  have hsc : StateH0Placed s0 sc := by
    rcases hsc_or with hsc_strip | hsc_real
    · rcases hsc_strip with ⟨hpc_c, ⟨hstat_c, hsp_c, hx29_c, hx27_c, hsaved_c, hframe_c⟩,
        hx0_c, hx1_c, hx2_c, hlr_c, hx19_c, hx20_c, hx21_c⟩
      have hm0 : (ProofLib.stripS kpQ0 s0).mem = ProofLib.stripExecOutside kpQ0 s0.mem := by cases s0; rfl
      have hmc : (ProofLib.stripS kpQ0 sc).mem = ProofLib.stripExecOutside kpQ0 sc.mem := by cases sc; rfl
      rw [hm0, hmc] at hframe_c
      exact ⟨(by cases sc; exact hpc_c), ⟨(by cases sc; exact hstat_c), (by cases s0; cases sc; exact hsp_c),
        (by cases s0; cases sc; exact hx29_c), (by cases s0; cases sc; exact hx27_c),
        (stripS_hmacSaved kpQ0 s0 sc).mp hsaved_c, unstrip_frame hframe_c hvm0a.perm_eq⟩,
        (by cases s0; cases sc; exact hx0_c), (by cases s0; cases sc; exact hx1_c),
        (by cases sc; exact hx2_c), (by cases sc; exact hlr_c), (by cases s0; cases sc; exact hx19_c),
        (by cases s0; cases sc; exact hx20_c), (by cases sc; exact hx21_c)⟩
    · exact hsc_real
  -- Piece 2: `new_from_slice_placed_runsTo_vm_sat` on Block `114` (`sc → s1`, `720`-B stack)
  have hcl_sc : LibsignalCodeLoaded lsmpl sc.mem := hcl.of_keepsFrozen hsteps0a.keepsFrozen
  have hL114_sc : (lsProg_114 H).CodeLoaded sc.mem := by
    rw [heq114 H]; exact hcl_sc 114 (by decide) (by decide) H (fun _ => none) Syscall.standard
  have hhsp_sub_720 : hsp s0 - 720#64 = s0.sp - 1200#64 := by unfold hsp; bv_omega
  rcases hsc with ⟨hpc_c, ⟨hstat_c, hsp_c, hx29_c, hx27_c, hsaved_c, hframe_c⟩,
    hx0_c, hx1_c, hx2_c, hlr_c, hx19_c, hx20_c, hx21_c⟩
  have hal_hsp : (hsp s0 &&& 0b1111#64) = 0#64 := hsp_align hpre.sp_aligned
  have hkey_c : sc.mem.readBytes (sc.readReg64 .x1) (sc.readReg64 .x2).toNat = key := by
    rw [hx1_c, hx2_c, show (32#64 : BitVec 64).toNat = 32 from rfl,
      hframe_c.readBytes_eq (by simp [hpre1024.disj_key_stack.symm]) (by decide), hpre.key_eq]
  have hiv_c : sc.mem.readBytes lsSha256IVAddr 32 = shaStateBytes sha256IV := by
    rw [hframe_c.readBytes_eq (by simp [hpre1024.disj_iv_stack.symm]) (by decide), hpre.iv_eq]
  have hread_iv_c : sc.mem.Readable lsSha256IVAddr 32 := (hframe_c.readable_iff _ _).mpr hpre.read_iv
  have hrw_stack_c : RW sc.mem (s0.sp - 1200#64) 1200 := (hframe_c.rw_iff _ _).mpr hpre.rw_stack
  have hdisj_iv_nfs : DisjointRegions lsSha256IVAddr 32 (sc.sp - 720#64) 720 := by
    rw [hsp_c, hhsp_sub_720]; exact hpre.disj_iv_stack.sub_right _ ⟨by decide, by clear * -; bv_omega⟩
  have hrw_out_nfs : RW sc.mem (sc.readReg64 .x0) 0x98 := by
    rw [hx0_c]; exact hrw_stack_c.sub (by clear * -; unfold hsp; bv_omega)
  have hrw_stack_nfs : RW sc.mem (sc.sp - 720#64) 720 := by
    rw [hsp_c, hhsp_sub_720]; exact hrw_stack_c.sub (by clear * -; bv_omega)
  have hdisj_out_nfs : DisjointRegions (sc.readReg64 .x0) 0x98 (sc.sp - 720#64) 720 := by
    rw [hx0_c, hsp_c]; clear * -; unfold hsp DisjointRegions; bv_omega
  have hread_key_nfs : sc.mem.Readable (sc.readReg64 .x1) (sc.readReg64 .x2).toNat := by
    rw [hx1_c, hx2_c, show (32#64 : BitVec 64).toNat = 32 from rfl]
    exact (hframe_c.readable_iff _ _).mpr hread_key
  have hdisj_key_nfs : DisjointRegions (sc.readReg64 .x1) (sc.readReg64 .x2).toNat (sc.sp - 720#64) 720 := by
    rw [hx1_c, hx2_c, hsp_c, hhsp_sub_720, show (32#64 : BitVec 64).toNat = 32 from rfl]
    exact hpre.disj_key_stack.sub_right _ ⟨by decide, by clear * -; bv_omega⟩
  obtain ⟨s1, hsteps114, hvm0b, htr0b, hvregs0b, hpc1, hstat1, hcs1, htag1, hhmac1, hframe1⟩ :=
    new_from_slice_placed_runsTo_vm_sat h_memcpy h_compress hpc_c hstat_c (by rw [hx2_c]; decide)
      hiv_c hread_iv_c hdisj_iv_nfs hrw_out_nfs hrw_stack_nfs hdisj_out_nfs hread_key_nfs
      (Or.inr hdisj_key_nfs) (by rw [hsp_c]; exact hal_hsp) hL114_sc
  have hext_114_73 : ∀ pc, (lsProg_114 H).externAt? pc = (lsProg_73 H).externAt? pc := fun pc => by
    have he114 : (libsignalSessionLib.blockLib 114).text.externs = libsignalSessionExterns :=
      IsLsBlockProg.externs_eq (prog := lsProg_114 H)
    have he73 : (libsignalSessionLib.blockLib 73).text.externs = libsignalSessionExterns :=
      IsLsBlockProg.externs_eq (prog := lsProg_73 H)
    rw [heq114 H, heq73 H, ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H
      Syscall.standard (he114.trans he73.symm)]
  have hsteps0b : Steps (lsProg_73 H) sc s1 :=
    Steps.of_sameHooks hext_114_73 (by rw [heq114 H, heq73 H]; rfl) hsteps114
  let s1_base : State := s0.setMem s1.mem
  have hs1_real : StateH1Placed F key s1_base s1 := by
    rw [hlr_c] at hpc1; rw [hx0_c] at htag1 hhmac1 hframe1
    rw [hsp_c, hhsp_sub_720] at hframe1; rw [hkey_c] at hhmac1
    have hhmac_addr : hsp s0 + 144#64 + 8#64 = hsp s0 + 152#64 := by clear * -; bv_omega
    rw [hhmac_addr] at hhmac1
    have hrw_saved_c : RW sc.mem (hsp s0 + 384#64) 96 :=
      hrw_stack_c.sub (by clear * -; unfold hsp; bv_omega)
    exact ⟨hpc1, ⟨hstat1, hcs1.1.trans hsp_c, (hcs1.2 .x29 (by simp)).trans hx29_c,
      (hcs1.2 .x27 (by simp)).trans hx27_c,
      hmacSaved_of_s2Frame hrw_saved_c hsaved_c hframe1 (by
        intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;>
          (dsimp only [s1_base]; clear * -; unfold hsp; simp only [State.sp_setMem]; unfold DisjointRegions; bv_omega)),
      Frame.refl s1.mem _⟩,
      (hcs1.2 .x19 (by simp)).trans hx19_c, (hcs1.2 .x20 (by simp)).trans hx20_c,
      (hcs1.2 .x21 (by simp)).trans hx21_c, htag1, hhmac1⟩
  have hf01 : S2Frame s0.mem s1.mem [(s0.sp - 1200#64, 1200)] := by
    have hs2_0c : S2Frame s0.mem sc.mem [(s0.sp - 1200#64, 1200)] := by
      refine (s2Frame_of_hmacFrame hframe_c).mono fun a ha r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      have hstk := ha (s0.sp - 1200#64, 1200) (by simp)
      clear * - hstk; unfold OutsideRegion at hstk ⊢; bv_omega
    have hs2_c1 : S2Frame sc.mem s1.mem [(s0.sp - 1200#64, 1200)] := by
      rw [hx0_c, hsp_c, hhsp_sub_720] at hframe1
      refine hframe1.mono fun a ha r hr => ?_
      have hstk := ha (s0.sp - 1200#64, 1200) (by simp)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;>
        (dsimp only at *; clear * - hstk; try unfold hsp at *; unfold OutsideRegion at hstk ⊢; bv_omega)
    exact hs2_0c.trans hs2_c1
  -- Piece 3: `seg1a_placed_runsTo` + `seg1b1_placed_runsTo_exact` on Block `73` (`s1 → s1p`)
  obtain ⟨hpre1, _⟩ := hpre.of_s2Frame hread_key hf01
  let Q73_1 := libsignalSessionLib.blockProgram lsmpl 73 (hmacNoMemsetExcHooksSat F H s1.mem kp73)
  let kpQ1 := ProofLib.progKeep Q73_1
  have hmcQ1 := hmacNoMemsetExcHooksSat_memcpy (F := F) h_memcpy s1.mem kp73
  have hpre1_strip := hmacPlacedPre_stripS kpQ1 hpre1.toHmacPlacedPre
  have hs1_strip : StateH1Placed F key (ProofLib.stripS kpQ1 s1_base) (ProofLib.stripS kpQ1 s1) := by
    rcases hs1_real with ⟨hpc1', ⟨hstat1', hsp1, hx29_1, hx27_1, hsaved1, _⟩,
      hx19_1, hx20_1, hx21_1, htag1', hhmac1'⟩
    have hm1_eq : (ProofLib.stripS kpQ1 s1_base).mem = (ProofLib.stripS kpQ1 s1).mem := by
      cases s0; cases s1; rfl
    have hm1 : (ProofLib.stripS kpQ1 s1).mem = ProofLib.stripExecOutside kpQ1 s1.mem := by cases s1; rfl
    have hsp1_b : hsp (ProofLib.stripS kpQ1 s1_base) = hsp s1_base := by cases s0; rfl
    exact ⟨(by cases s1; exact hpc1'), ⟨(by cases s1; exact hstat1'), (by cases s0; cases s1; exact hsp1),
       (by cases s0; cases s1; exact hx29_1), (by cases s0; cases s1; exact hx27_1),
       (stripS_hmacSaved kpQ1 s1_base s1).mpr hsaved1, hm1_eq ▸ Frame.refl _ _⟩,
      (by cases s0; cases s1; exact hx19_1), (by cases s0; cases s1; exact hx20_1),
      (by cases s1; exact hx21_1), by rw [hsp1_b, stripS_read64]; exact htag1',
      by rw [hm1, hsp1_b]; exact stripExecOutside_hmacSt.mpr hhmac1'⟩
  have hL73_s1 : (libsignalSessionLib.blockProgram lsmpl 73 H).CodeLoaded s1.mem := by
    rw [← heq73 H]; exact (hsteps0a.trans hsteps0b).codeLoaded hL73
  have hrunsP1 : RunsTo (libsignalSessionLib.blockProgram lsmpl 73 H) s1
      (StateH1pPlaced F key byte s1_base) :=
    runsTo_73_to_bp ((seg1a_placed_runsTo (H := H) hpre1.toHmacPlacedPre hs1_real).trans
      fun _ h1m => seg1b1_placed_runsTo_exact (H := H) h_memcpy hpre1.toHmacPlacedPre h1m)
  have hrunsQ1 : RunsTo Q73_1 (ProofLib.stripS kpQ1 s1)
      (StateH1pPlaced F key byte (ProofLib.stripS kpQ1 s1_base)) :=
    runsTo_73_to_bp ((seg1a_placed_runsTo (H := hmacNoMemsetExcHooksSat F H s1.mem kp73)
      hpre1_strip hs1_strip).trans fun _ h1m => seg1b1_placed_runsTo_exact hmcQ1 hpre1_strip h1m)
  obtain ⟨s1p, hsteps1_bp, hvm1, _, htr1, hvregs1, h1p_or⟩ :=
    runsTo_block_lift_vm_no_memset_sat h_memcpy h_compress blkLib_eq_73 rfl rfl hL73_s1
      hrunsP1 hrunsQ1 (fun _ hs => hs.common.status) (fun _ hs => hs.common.status)
  have hsteps1b1 : Steps (lsProg_73 H) s1 s1p := steps_bp_to_73 hsteps1_bp
  have hvm0_1p : VmPreserved s0 s1p := (hvm0a.trans hvm0b).trans hvm1
  have h1p : StateH1pPlaced F key byte s1_base s1p := by
    rcases h1p_or with h1p_strip | h1p_real
    · rcases h1p_strip with ⟨hpc_p, ⟨hstat_p, hsp_p, hx29_p, hx27_p, hsaved_p, hframe_p⟩,
        hx0_p, hx1_p, hx2_p, hlr_p, hx19_p, hx20_p, hx21_p, hx22_p, hx23_p, hx24_p, hx25_p, hx26_p,
        hm144_0, hm144_1, hist_p, hibl_p, host_p, hobl_p⟩
      have hm1_b : (ProofLib.stripS kpQ1 s1_base).mem = ProofLib.stripExecOutside kpQ1 s1_base.mem := by
        cases s0; rfl
      have hmp : (ProofLib.stripS kpQ1 s1p).mem = ProofLib.stripExecOutside kpQ1 s1p.mem := by cases s1p; rfl
      have hsp1_b : hsp (ProofLib.stripS kpQ1 s1_base) = hsp s1_base := by cases s0; rfl
      have hs1_b : (ProofLib.stripS kpQ1 s1_base).sp = s1_base.sp := by cases s0; rfl
      have hperm_1_1p : ∀ a, s1p.mem.perm a = s1_base.mem.perm a := fun a => by
        have h := hvm1.perm_eq a; cases s0; exact h
      rw [hm1_b, hmp, hs1_b] at hframe_p
      rw [hsp1_b, hmp, stripExecOutside_readBytes] at hist_p host_p
      rw [hsp1_b, stripS_read8] at hm144_0 hm144_1
      rw [hsp1_b, stripS_read64] at hibl_p hobl_p
      exact ⟨(by cases s1p; exact hpc_p), ⟨(by cases s1p; exact hstat_p),
         (by cases s0; cases s1p; exact hsp_p), (by cases s0; cases s1p; exact hx29_p),
         (by cases s0; cases s1p; exact hx27_p),
         (stripS_hmacSaved kpQ1 s1_base s1p).mp hsaved_p, unstrip_frame hframe_p hperm_1_1p⟩,
        (by cases s0; cases s1p; exact hx0_p), (by cases s1p; exact hx1_p),
        (by cases s1p; exact hx2_p), (by cases s1p; exact hlr_p),
        (by cases s0; cases s1p; exact hx19_p), (by cases s0; cases s1p; exact hx20_p),
        (by cases s0; cases s1p; exact hx21_p), (by cases s0; cases s1p; exact hx22_p),
        (by cases s1p; exact hx23_p), (by cases s1p; exact hx24_p),
        (by cases s1p; exact hx25_p), (by cases s1p; exact hx26_p),
        hm144_0, hm144_1, hist_p, hibl_p, host_p, hobl_p⟩
    · exact h1p_real
  -- Piece 4: `memset` call at `+360#64` (`s1p → s2`)
  rcases h1p with ⟨hpc_p, ⟨hstat_p, hsp_p, hx29_p, hx27_p, hsaved_p, hframe_p⟩,
    hx0_p, hx1_p, hx2_p, hlr_p, hx19_p, hx20_p, hx21_p, hx22_p, hx23_p, hx24_p, hx25_p, hx26_p,
    hm144_0, hm144_1, hist_p, hibl_p, host_p, hobl_p⟩
  have hhsp_b : hsp s1_base = hsp s0 := by cases s0; rfl
  have hs1_sp : s1_base.sp = s0.sp := by cases s0; rfl
  have hr1_b : ∀ r, s1_base.readReg64 r = s0.readReg64 r := fun _ => by cases s0; rfl
  have hsaved_p0 : HmacSaved s0 (hsp s0) s1p.mem := by cases s0; exact hsaved_p
  rw [hhsp_b] at hsp_p hx29_p hx0_p hx20_p hx21_p hx22_p hm144_0 hm144_1 hist_p hibl_p host_p hobl_p
  rw [hr1_b] at hx27_p hx19_p
  have hf1_1p : S2Frame s1.mem s1p.mem [(s0.sp - 1200#64, 1200)] := by
    have hfr1 : Frame s1.mem s1p.mem [(s0.sp - 1024#64, 1024)] := by cases s0; exact hframe_p
    refine (s2Frame_of_hmacFrame hfr1).mono fun a ha r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
    have ha_stk := ha (s0.sp - 1200#64, 1200) (by simp)
    clear * - ha_stk; unfold OutsideRegion at ha_stk ⊢; bv_omega
  have hf0_1p : S2Frame s0.mem s1p.mem [(s0.sp - 1200#64, 1200)] := hf01.trans hf1_1p
  have hrw_hsp : s1p.mem.RW (hsp s0) 480 :=
    (hf0_1p.rw_of_rw _ _ hpre.rw_stack).sub (by clear * -; unfold hsp; bv_omega)
  have hsp_al_1p : (s1p.sp &&& 15#64) = 0#64 := by rw [hsp_p]; exact hal_hsp
  obtain ⟨s2, hsteps1b2, hvm1b2, htr1b2, hvregs1b2, hpc2, hstat2, hcc2, _, _, _, hs2_step_fr, hag2⟩ :=
    placed_memset_budget_steps_sat (prog := lsProg_73 H) (i := 73) h_memset
      (dst := hsp s0 + 146#64) (lr := (blkPl_73).base + 388#64) (val := 0#8) (len := 62)
      hstat_p hpc_p hx0_p hx1_p (by rw [hx2_p]; rfl) hlr_p hsp_al_1p
      (hrw_hsp.sub (by clear * -; bv_omega))
  have hP_hsp : ∀ {off : BitVec 64} {n : Nat},
      (off - hsp s0).toNat + n ≤ 480 →
      ∀ a, InRegion off n a → (s1p.mem.perm a).r = true ∧ s1p.mem.isLazyFree a = false := by
    intro off n hsub a ha
    have hnl := hrw_hsp a (by unfold InRegion at ha ⊢; bv_omega)
    obtain ⟨hp, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp hnl
    exact ⟨by rw [hp]; rfl, hlf⟩
  have hs2_frame : S2Frame s0.mem s2.mem [(s0.sp - 1200#64, 1200)] := by
    refine hf0_1p.trans (hs2_step_fr.mono fun a ha => ?_)
    intro r hr_mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr_mem; subst hr_mem
    have ha_stk := ha (s0.sp - 1200#64, 1200) (by simp)
    clear * - ha_stk; unfold hsp OutsideRegion at ha_stk ⊢; bv_omega
  have hsaved_wb : HmacSaved s0 (hsp s0)
      (s1p.mem.writeBytes (hsp s0 + 146#64) (List.replicate 62 0#8)) :=
    hsaved_p0.of_agreesOutside (AgreesOutside.writeBytes_self _ _ _)
      (by clear * -; simp only [List.length_replicate, DisjointRegions]; bv_omega)
  have h2 : StateH2PlacedSat F key byte s0 s2 :=
    { pc_eq := hpc2
      common :=
        { status := hstat2, sp_eq := (CallingConventionPreserved.sp_eq hcc2).trans hsp_p
          x29_eq := (CallingConventionPreserved.x29 hcc2).trans hx29_p
          x27_eq := (CallingConventionPreserved.x27 hcc2).trans hx27_p
          saved := hmacSaved_of_agreesOn hag2 hsaved_wb (hP_hsp (by clear * -; bv_omega))
          frame := hs2_frame }
      x19_eq := (CallingConventionPreserved.x19 hcc2).trans hx19_p
      x20_eq := (CallingConventionPreserved.x20 hcc2).trans hx20_p
      x21_eq := (CallingConventionPreserved.x21 hcc2).trans hx21_p
      x22_eq := (CallingConventionPreserved.x22 hcc2).trans hx22_p
      x23_eq := (CallingConventionPreserved.x23 hcc2).trans hx23_p
      x24_eq := (CallingConventionPreserved.x24 hcc2).trans hx24_p
      x25_eq := (CallingConventionPreserved.x25 hcc2).trans hx25_p
      x26_eq := (CallingConventionPreserved.x26 hcc2).trans hx26_p
      m144 := by
        rw [AgreesOn.read64_eq hag2 (hsp s0 + 144#64) (hP_hsp (by clear * -; bv_omega)),
            toLEBytes_8_read64_writeBytes_146_62 s1p.mem (hsp s0), hm144_0, hm144_1]; rfl
      m152 := (AgreesOn.read64_eq hag2 (hsp s0 + 152#64) (hP_hsp (by clear * -; bv_omega))).trans
        (read64_writeBytes_replicate_zero_off s1p.mem (hsp s0) 146#64 152#64 62)
      m160 := (AgreesOn.read64_eq hag2 (hsp s0 + 160#64) (hP_hsp (by clear * -; bv_omega))).trans
        (read64_writeBytes_replicate_zero_off s1p.mem (hsp s0) 146#64 160#64 62)
      m168 := (AgreesOn.read64_eq hag2 (hsp s0 + 168#64) (hP_hsp (by clear * -; bv_omega))).trans
        (read64_writeBytes_replicate_zero_off s1p.mem (hsp s0) 146#64 168#64 62)
      m176 := (AgreesOn.read64_eq hag2 (hsp s0 + 176#64) (hP_hsp (by clear * -; bv_omega))).trans
        (read64_writeBytes_replicate_zero_off s1p.mem (hsp s0) 146#64 176#64 62)
      m184 := (AgreesOn.read64_eq hag2 (hsp s0 + 184#64) (hP_hsp (by clear * -; bv_omega))).trans
        (read64_writeBytes_replicate_zero_off s1p.mem (hsp s0) 146#64 184#64 62)
      m192 := (AgreesOn.read64_eq hag2 (hsp s0 + 192#64) (hP_hsp (by clear * -; bv_omega))).trans
        (read64_writeBytes_replicate_zero_off s1p.mem (hsp s0) 146#64 192#64 62)
      ist_eq := (AgreesOn.readBytes_eq hag2 (hsp s0 + 208#64) 32 (by decide)
          (hP_hsp (by clear * -; bv_omega))).trans
        ((readBytes_writeBytes_replicate_off_disjoint s1p.mem (hsp s0) 146#64 208#64 32 62 0#8).trans hist_p)
      ibl_eq := (AgreesOn.read64_eq hag2 (hsp s0 + 240#64) (hP_hsp (by clear * -; bv_omega))).trans
        ((read64_writeBytes_replicate_off_disjoint s1p.mem (hsp s0) 146#64 240#64 62 0#8).trans hibl_p)
      ost_eq := (AgreesOn.readBytes_eq hag2 (hsp s0 + 248#64) 32 (by decide)
          (hP_hsp (by clear * -; bv_omega))).trans
        ((readBytes_writeBytes_replicate_off_disjoint s1p.mem (hsp s0) 146#64 248#64 32 62 0#8).trans host_p)
      obl_eq := (AgreesOn.read64_eq hag2 (hsp s0 + 280#64) (hP_hsp (by clear * -; bv_omega))).trans
        ((read64_writeBytes_replicate_off_disjoint s1p.mem (hsp s0) 146#64 280#64 62 0#8).trans hobl_p) }
  -- Piece 5: `hmac_tail_placed_runsTo_sat` on Block `73` (`s2 → sf`)
  let s0' : State := s0.setMem s2.mem
  obtain ⟨hpre2, hread_key2⟩ := hpre.of_s2Frame hread_key hs2_frame
  let Q73_2 := libsignalSessionLib.blockProgram lsmpl 73 (hmacCompressOnlyExcHooksSat F H s2.mem kp73)
  let kpQ2 := ProofLib.progKeep Q73_2
  have hc256Q2 := hmacCompressOnlyExcHooksSat_compress h_compress s2.mem kp73
  have hpre2_strip := hmacPlacedPre_stripS kpQ2 hpre2.toHmacPlacedPre
  have hread_key2_strip :
      (ProofLib.stripS kpQ2 s0').mem.Readable ((ProofLib.stripS kpQ2 s0').readReg64 .x1) 32 := by
    have hm0' : (ProofLib.stripS kpQ2 s0').mem = ProofLib.stripExecOutside kpQ2 s0'.mem := by cases s0; rfl
    have hr0' : (ProofLib.stripS kpQ2 s0').readReg64 .x1 = s0'.readReg64 .x1 := by cases s0; rfl
    rw [hm0', hr0']
    exact stripExecOutside_readable kpQ2 s0'.mem _ _ hread_key2
  have h2'_real : StateH2Placed F key byte s0' s2 :=
    { pc_eq := h2.pc_eq
      common := { status := h2.common.status, sp_eq := h2.common.sp_eq, x29_eq := h2.common.x29_eq
                  x27_eq := h2.common.x27_eq, saved := h2.common.saved, frame := Frame.refl s2.mem _ }
      x19_eq := h2.x19_eq, x20_eq := h2.x20_eq, x21_eq := h2.x21_eq, x22_eq := h2.x22_eq,
      x23_eq := h2.x23_eq, x24_eq := h2.x24_eq, x25_eq := h2.x25_eq, x26_eq := h2.x26_eq,
      m144 := h2.m144, m152 := h2.m152, m160 := h2.m160, m168 := h2.m168,
      m176 := h2.m176, m184 := h2.m184, m192 := h2.m192,
      ist_eq := h2.ist_eq, ibl_eq := h2.ibl_eq, ost_eq := h2.ost_eq, obl_eq := h2.obl_eq }
  have h2'_strip : StateH2Placed F key byte (ProofLib.stripS kpQ2 s0') (ProofLib.stripS kpQ2 s2) := by
    have hsp0' : hsp (ProofLib.stripS kpQ2 s0') = hsp s0 := by cases s0; rfl
    have hm2_73 : (ProofLib.stripS kpQ2 s2).mem = ProofLib.stripExecOutside kpQ2 s2.mem := by cases s2; rfl
    have hm0'_eq : (ProofLib.stripS kpQ2 s0').mem = (ProofLib.stripS kpQ2 s2).mem := by cases s0; cases s2; rfl
    exact
      { pc_eq := by cases s2; exact h2.pc_eq
        common :=
          { status := by cases s2; exact h2.common.status
            sp_eq := by cases s0; cases s2; exact h2.common.sp_eq
            x29_eq := by cases s0; cases s2; exact h2.common.x29_eq
            x27_eq := by cases s0; cases s2; exact h2.common.x27_eq
            saved := (stripS_hmacSaved kpQ2 s0' s2).mpr h2.common.saved
            frame := hm0'_eq ▸ Frame.refl _ _ }
        x19_eq := by cases s0; cases s2; exact h2.x19_eq
        x20_eq := by cases s0; cases s2; exact h2.x20_eq
        x21_eq := by cases s0; cases s2; exact h2.x21_eq
        x22_eq := by cases s0; cases s2; exact h2.x22_eq
        x23_eq := by cases s2; exact h2.x23_eq
        x24_eq := by cases s2; exact h2.x24_eq
        x25_eq := by cases s2; exact h2.x25_eq
        x26_eq := by cases s2; exact h2.x26_eq
        m144 := by rw [hsp0', stripS_read64]; exact h2.m144
        m152 := by rw [hsp0', stripS_read64]; exact h2.m152
        m160 := by rw [hsp0', stripS_read64]; exact h2.m160
        m168 := by rw [hsp0', stripS_read64]; exact h2.m168
        m176 := by rw [hsp0', stripS_read64]; exact h2.m176
        m184 := by rw [hsp0', stripS_read64]; exact h2.m184
        m192 := by rw [hsp0', stripS_read64]; exact h2.m192
        ist_eq := by rw [hsp0', hm2_73, stripExecOutside_readBytes]; exact h2.ist_eq
        ibl_eq := by rw [hsp0', stripS_read64]; exact h2.ibl_eq
        ost_eq := by rw [hsp0', hm2_73, stripExecOutside_readBytes]; exact h2.ost_eq
        obl_eq := by rw [hsp0', stripS_read64]; exact h2.obl_eq }
  have hsteps0_2 : Steps (lsProg_73 H) s0 s2 :=
    ((hsteps0a.trans hsteps0b).trans hsteps1b1).trans hsteps1b2
  have hL73_s2 : (libsignalSessionLib.blockProgram lsmpl 73 H).CodeLoaded s2.mem := by
    rw [← heq73 H]; exact hsteps0_2.codeLoaded hL73
  have hruns_tail_P :=
    runsTo_73_to_bp (hmac_tail_placed_runsTo_sat h_compress hpre2.toHmacPlacedPre hread_key2 h2'_real)
  have hruns_tail_Q :=
    runsTo_73_to_bp (hmac_tail_placed_runsTo_sat hc256Q2 hpre2_strip hread_key2_strip h2'_strip)
  obtain ⟨sf, hsteps_tail_bp, hvm_tail, _, htr_tail, hvregs_tail, h5_or⟩ :=
    runsTo_block_lift_vm_compress_only_sat h_compress blkLib_eq_73 rfl rfl hL73_s2
      hruns_tail_P hruns_tail_Q (fun _ hs => hs.2.1) (fun _ hs => hs.2.1)
  have hsteps_tail : Steps (lsProg_73 H) s2 sf := steps_bp_to_73 hsteps_tail_bp
  have hvm_all : VmPreserved s0 sf := (hvm0_1p.trans hvm1b2).trans hvm_tail
  have h5_s0' : sf.pc = s0'.readReg64 .lr ∧ sf.status = .Running ∧ CalleeSaved s0' sf ∧
      sf.mem.readBytes (s0'.readReg64 .x0) 32 = hmacWith F key [byte] ∧
      S2Frame s0'.mem sf.mem [(s0'.readReg64 .x0, 32), (s0'.sp - 1024#64, 1024)] := by
    rcases h5_or with h5_strip | h5_real
    · rcases h5_strip with ⟨hpc_sf, hstat_sf, hcs_sf, hout_sf, hframe_sf⟩
      have hm0'_73 : (ProofLib.stripS kpQ2 s0').mem = ProofLib.stripExecOutside kpQ2 s0'.mem := by cases s0; rfl
      have hmf_73 : (ProofLib.stripS kpQ2 sf).mem = ProofLib.stripExecOutside kpQ2 sf.mem := by cases sf; rfl
      have hr0_73 : (ProofLib.stripS kpQ2 s0').readReg64 .x0 = s0'.readReg64 .x0 := by cases s0; rfl
      have hs0_73 : (ProofLib.stripS kpQ2 s0').sp = s0'.sp := by cases s0; rfl
      rw [hm0'_73, hmf_73, hr0_73, hs0_73] at hframe_sf
      rw [hmf_73, hr0_73, stripExecOutside_readBytes] at hout_sf
      have hcs_u : CalleeSaved s0' sf := by
        refine ⟨by cases s0; cases sf; exact hcs_sf.1, fun r hr => ?_⟩
        have := hcs_sf.2 r hr; cases s0; cases sf; exact this
      have hperm_0'f : ∀ a, sf.mem.perm a = s0'.mem.perm a := fun a => by
        have h := hvm_tail.perm_eq a; cases s0; exact h
      exact ⟨by cases s0; cases sf; exact hpc_sf, by cases sf; exact hstat_sf,
        hcs_u, hout_sf, unstrip_s2Frame hframe_sf hperm_0'f⟩
    · exact h5_real
  rcases h5_s0' with ⟨hpc_sf, hstat_sf, hcs_sf, hout_sf, hf25⟩
  have hf02_w : S2Frame s0.mem s2.mem [(s0.readReg64 .x0, 32), (s0.sp - 1200#64, 1200)] :=
    hs2_frame.mono fun a ha r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      exact ha _ (by simp)
  have hf25_s2 : S2Frame s2.mem sf.mem [(s0.readReg64 .x0, 32), (s0.sp - 1024#64, 1024)] := by
    cases s0; exact hf25
  have hf25_w : S2Frame s2.mem sf.mem [(s0.readReg64 .x0, 32), (s0.sp - 1200#64, 1200)] :=
    hf25_s2.mono fun a ha r hr => by
      have hout := ha (s0.readReg64 .x0, 32) (by simp)
      have hstk := ha (s0.sp - 1200#64, 1200) (by simp)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hout
      · clear * - hstk; unfold OutsideRegion at hstk ⊢; bv_omega
  have hcs_0_sf : CalleeSaved s0 sf := by
    refine ⟨hcs_sf.1, fun r hr => ?_⟩
    have := hcs_sf.2 r hr; cases s0; exact this
  exact ⟨sf, hsteps0_2.trans hsteps_tail, hvm_all,
    htr_tail.trans (htr1b2.trans (htr1.trans (htr0b.trans htr0a))),
    hvregs_tail.trans (hvregs1b2.trans (hvregs1.trans (hvregs0b.trans hvregs0a))),
    { pc_eq := by cases s0; exact hpc_sf
      status := hstat_sf
      calleeSaved := hcs_0_sf
      out_eq := by cases s0; exact hout_sf
      frame := hf02_w.trans hf25_w }⟩

/-- `VmPreserved`-strengthened `hmac_sha256` contract on Block 73 under `HookSatExactMemcpy H lsMemcpySym`, `HookSat` for `memset`, and `HookSatCompress256 H lsCompress256Sym F` (sibling of `AssemblyBudget.hmac_sha256_placed_ok`). -/
theorem hmac_sha256_placed_ok_sat [LibsignalPlacement]
    (F : ShaCompress)
    {H : String → Option (State → State)}
    (h_mc : HookSatExactMemcpy H lsMemcpySym)
    (h_ms : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec)
    (h_c256 : HookSatCompress256 H lsCompress256Sym F) :
    subroutine_ok ((blkPC_73).rebase (blkPl_73).base H) (blkPl_73).base
      (withLsCodeLoaded lsmpl (withVmPreserved (hmacPlacedSpec F))) := by
  refine subroutine_ok_intro fun ⟨out, ka, key, ia, inp⟩ R s0 hpc hrun hpre hsp => ?_
  have ⟨hcl, hpre⟩ := extract_withLsCodeLoaded hpre
  rw [withVmPreserved, hmacPlacedSpec] at hpre
  dsimp only [] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2_nat, hx3, hx4_nat, hkey_len, hinp_len, hro⟩, hsep⟩
  rcases inp with _ | ⟨byte, _ | _⟩ <;> try { simp at hinp_len }
  have hx2 : s0.readReg64 .x2 = 32#64 := by
    apply BitVec.eq_of_toNat_eq; simp [hx2_nat, hkey_len]
  have hx4 : s0.readReg64 .x4 = 1#64 := by
    apply BitVec.eq_of_toNat_eq; simp at hx4_nat; simp [hx4_nat]
  have hsp_split : stackAt s0.sp 2048 =
      memRegion (s0.sp - 2048#64) 848 ∗ memRegion (s0.sp - 1200#64) 1200 :=
    stackAt_split_bottom s0.sp 1200 848 (by decide)
  rw [hsp_split] at hsep
  have hb_out := IsBlock.memRegion out 32
  have hb_key := IsBlock.pointsToBytes_len (a := ka) hkey_len
  have hb_inp := IsBlock.pointsToBytes_len (a := ia) (rfl : [byte].length = 1)
  have hb_stk := IsBlock.memRegion (s0.sp - 1200#64) 1200
  have hsep_key : s0.mem ⊨ (ka ↦ₛ key) ∗ (memRegion (s0.sp - 1200#64) 1200 ∗
      (memRegion out 32 ∗ (ia ↦ₛ [byte]) ∗ memRegion (s0.sp - 2048#64) 848 ∗ R)) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hsep
  have hsep_inp : s0.mem ⊨ (ia ↦ₛ [byte]) ∗ (memRegion (s0.sp - 1200#64) 1200 ∗
      (memRegion out 32 ∗ (ka ↦ₛ key) ∗ memRegion (s0.sp - 2048#64) 848 ∗ R)) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hsep
  have hsep_out : s0.mem ⊨ memRegion out 32 ∗ (memRegion (s0.sp - 1200#64) 1200 ∗
      ((ka ↦ₛ key) ∗ (ia ↦ₛ [byte]) ∗ memRegion (s0.sp - 2048#64) 848 ∗ R)) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hsep
  have hsep_stk : s0.mem ⊨ memRegion (s0.sp - 1200#64) 1200 ∗
      (memRegion out 32 ∗ (ka ↦ₛ key) ∗ (ia ↦ₛ [byte]) ∗ memRegion (s0.sp - 2048#64) 848 ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hsep
  have hkey_eq : s0.mem.readBytes ka 32 = key := by
    have h := (hb_key.read hsep_key).2
    rwa [hkey_len] at h
  have hinp_eq : s0.mem.readBytes ia 1 = [byte] :=
    (hb_inp.read hsep_inp).2
  have hrw_out : RW s0.mem out 32 :=
    fun a ha => hb_out.permNoLazy_rw hsep_out ha
  have hrw_stk : RW s0.mem (s0.sp - 1200#64) 1200 :=
    fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
  have hread_key : s0.mem.Readable ka 32 :=
    Memory.RW.readable (fun a ha => hb_key.permNoLazy_rw hsep_key ha)
  have hread_inp : s0.mem.Readable ia 1 :=
    Memory.RW.readable (fun a ha => hb_inp.permNoLazy_rw hsep_inp ha)
  obtain ⟨hro_iv, hiv_eq⟩ := rodata_placed_sha256IV hro
  have hread_iv : s0.mem.Readable lsSha256IVAddr 32 :=
    fun a ha => ⟨by rw [(hro_iv a ha).1]; rfl, (hro_iv a ha).2⟩
  have hpre_hmac : HmacPlacedPreSat F key [byte] s0 := {
    pc_eq := hpc, status := hrun, sp_aligned := by simpa [State.spAligned] using hsp
    x2_eq := hx2, x4_eq := hx4, key_len := hkey_len, inp_len := rfl
    key_eq := by rw [hx1]; exact hkey_eq, inp_eq := by rw [hx3]; exact hinp_eq
    iv_eq := hiv_eq, read_iv := hread_iv, read_inp := by rw [hx3]; exact hread_inp
    rw_out := by rw [hx0]; exact hrw_out, rw_stack := hrw_stk
    disj_iv_stack := disjointRegions_of_ro_rw (by decide) (by decide) hro_iv hrw_stk
    disj_out_stack := by rw [hx0]; exact hb_out.disjoint hb_stk (by decide) (by decide) hsep_out
    disj_key_stack := by rw [hx1]; exact hb_key.disjoint hb_stk (by decide) (by decide) hsep_key
    disj_inp_stack := by rw [hx3]; exact hb_inp.disjoint hb_stk (by simp) (by decide) hsep_inp }
  have hread_x1 : s0.mem.Readable (s0.readReg64 .x1) 32 := by rw [hx1]; exact hread_key
  intro hL73
  obtain ⟨sf, hsteps, hvm, htr, hvregs, hpc_sf, hstat_sf, hcallee, hout_sf, hframe_sf⟩ :=
    hmac_placed_runsTo_vm_sat h_mc h_ms h_c256 hcl hpre_hmac hread_x1 hL73
  refine ⟨sf, hsteps, Or.inl ⟨hpc_sf, hstat_sf, ?_,
    CallingConventionPreserved_of_calleeSaved hcallee hvregs⟩⟩
  dsimp only [withLsCodeLoaded, withVmPreserved, hmacPlacedSpec]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨hvm, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨htr, libsignalRoLoaded_of_keepsFrozen hro hsteps.keepsFrozen⟩, ?_⟩
  rw [hsp_split]
  have hb_out' := IsBlock.pointsToBytes_len (a := out) (length_hmacWith F key [byte])
  rw [hx0] at hout_sf hframe_sf
  have hpost_sep : sf.mem ⊨ (out ↦ₛ hmacWith F key [byte]) ∗ (memRegion (s0.sp - 1200#64) 1200 ∗
      ((ka ↦ₛ key) ∗ (ia ↦ₛ [byte]) ∗ memRegion (s0.sp - 2048#64) 848 ∗ R)) :=
    S2Frame.update_two_blocks hb_out hb_out' hb_stk hb_stk hsep_out hframe_sf
      ⟨by rw [length_hmacWith]; decide, by rwa [length_hmacWith]⟩ trivial
  exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost_sep

/-- `.rodata`-backed `VmPreserved` `hmac_sha256` contract on Block 73 under `HookSatExactMemcpy H lsMemcpySym`, `HookSat` for `memset`, and `HookSatCompress256 H lsCompress256Sym F` (sibling of `AssemblyBudget.hmac_sha256_placed_ro_ok`). -/
theorem hmac_sha256_placed_ro_ok_sat [LibsignalPlacement]
    (F : ShaCompress)
    {H : String → Option (State → State)}
    (h_mc : HookSatExactMemcpy H lsMemcpySym)
    (h_ms : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec)
    (h_c256 : HookSatCompress256 H lsCompress256Sym F) :
    subroutine_ok ((blkPC_73).rebase (blkPl_73).base H) (blkPl_73).base
      (withLsCodeLoaded lsmpl
        { hmacSpec F with pre := fun g s => (hmacSpec F).pre g s ∗ ⌜LibsignalRoLoaded lsmpl s.mem⌝ }) := by
  refine subroutine_ok_mono (hmac_sha256_placed_ok_sat F h_mc h_ms h_c256)
    (fun ⟨out, ka, key, ia, inp⟩ R s0 hp => ?_)
    (fun ⟨out, ka, key, ia, inp⟩ R s0 sf hq => ?_)
  · have ⟨hcl, hp'⟩ := extract_withLsCodeLoaded hp
    dsimp only [withLsCodeLoaded, withVmPreserved, hmacPlacedSpec, hmacSpec,
      CryptoVerification.LibsignalSession.hmacSpec] at hp' ⊢
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hp' ⊢
    rcases hp' with ⟨hro, hp''⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp''
    rcases hp'' with ⟨hpure, hsep⟩
    refine ⟨hcl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hpure.1, hpure.2.1, hpure.2.2.1, hpure.2.2.2.1, hpure.2.2.2.2.1,
      hpure.2.2.2.2.2.1, hpure.2.2.2.2.2.2, hro⟩, hsep⟩
  · dsimp only [withLsCodeLoaded, withVmPreserved, hmacPlacedSpec, hmacSpec,
      CryptoVerification.LibsignalSession.hmacSpec] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    refine ⟨hq.1, ?_⟩
    have hq' := hq.2
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq' ⊢
    exact ⟨hq'.1.1, hq'.2⟩

/-! ## Callee Lifts and Top-Level `consume_message_key` Assembly -/

theorem find_receiver_chain_index_placed_ok_at_cmk_sat [LibsignalPlacement] {M : AllocCostModel}
    {H : String → Option (State → State)} (A : RustCliAllocBudget M)
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    FindIndexPlacedOk H A :=
  AssemblyBudget.find_receiver_chain_index_placed_ok_at_cmk A h_bb

theorem grow_one_placed_ok_at_cmk_sat [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hA : CmkAllocHooks A lim H)
    (h_realloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    GrowOnePlacedOk H A lim :=
  AssemblyBudget.grow_one_placed_ok_at_cmk hA h_realloc

theorem grow_one_placed_ok_of_noop_at_cmk_sat [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_shim : H lsNoAllocShimSym = some hookNoop)
    (h_realloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hA : CmkAllocHooks A lim H) :
    GrowOnePlacedOk H A lim :=
  AssemblyBudget.grow_one_placed_ok_of_noop_at_cmk h_shim h_realloc hA

theorem hmac_sha256_placed_ro_ok_at_cmk_sat [LibsignalPlacement]
    (F : ShaCompress)
    {H : String → Option (State → State)}
    (h_mc : HookSatExactMemcpy H lsMemcpySym)
    (h_ms : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec)
    (h_c256 : HookSatCompress256 H lsCompress256Sym F) :
    HmacPlacedRoOk H F :=
  ls_subroutine_ok_of_block (i := 24) (j := 73) (hmac_sha256_placed_ro_ok_sat F h_mc h_ms h_c256)

theorem consume_message_key_placed_run_of_hooks_sat [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (h_realloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hhmac : HmacPlacedOk H F) :
    CmkPlacedRunStmtSat F A lim H := by
  intro hA hmm
  exact consume_message_key_placed_run_of_sat F A lim H
    (find_receiver_chain_index_placed_ok_at_cmk_sat A h_bb)
    hhmac
    (grow_one_placed_ok_at_cmk_sat hA h_realloc) hA hmm

theorem consume_message_key_placed_run_sat [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (h_shim : H lsNoAllocShimSym = some hookNoop)
    (h_realloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hhmac : HmacPlacedOk H F) :
    CmkPlacedRunStmtSat F A lim H := by
  intro hA hmm
  exact consume_message_key_placed_run_of_sat F A lim H
    (find_receiver_chain_index_placed_ok_at_cmk_sat A h_bb)
    hhmac
    (grow_one_placed_ok_of_noop_at_cmk_sat h_shim h_realloc hA) hA hmm

/-- `.rodata`-backed budget-threaded placed refinement for `consume_message_key` (`HookSat` `memset`, `HookSatCompress256`, `sessionMemmoveBoundedBudgetSpec 4096` `memmove`, and shim; sibling of `consume_message_key_placed_ro_run_of_hooks`). -/
theorem consume_message_key_placed_ro_run_of_hooks_sat [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaCompress)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (h_realloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (h_mc : HookSatExactMemcpy H lsMemcpySym)
    (h_ms : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec)
    (h_c256 : HookSatCompress256 H lsCompress256Sym F) :
    CmkPlacedRunStmtSat F A lim H := by
  intro hA hmm
  exact consume_message_key_placed_ro_run_of_sat F A lim H
    (find_receiver_chain_index_placed_ok_at_cmk_sat A h_bb)
    (hmac_sha256_placed_ro_ok_at_cmk_sat F h_mc h_ms h_c256)
    (grow_one_placed_ok_at_cmk_sat hA h_realloc) hA hmm

/-- `.rodata`-backed budget-threaded placed refinement for `consume_message_key` (`HookSat` `memset`, `HookSatCompress256`, and `sessionMemmoveBoundedBudgetSpec 4096` `memmove`, `hookNoop` shim; sibling of `consume_message_key_placed_ro_run`). -/
theorem consume_message_key_placed_ro_run_sat [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaCompress)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (h_shim : H lsNoAllocShimSym = some hookNoop)
    (h_realloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (h_mc : HookSatExactMemcpy H lsMemcpySym)
    (h_ms : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec)
    (h_c256 : HookSatCompress256 H lsCompress256Sym F) :
    CmkPlacedRunStmtSat F A lim H := by
  intro hA hmm
  exact consume_message_key_placed_ro_run_of_sat F A lim H
    (find_receiver_chain_index_placed_ok_at_cmk_sat A h_bb)
    (hmac_sha256_placed_ro_ok_at_cmk_sat F h_mc h_ms h_c256)
    (grow_one_placed_ok_of_noop_at_cmk_sat h_shim h_realloc hA) hA hmm

end LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetSat
