/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetAuxASat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfGenFin -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfGenFinPlaced -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfGenFinPlacedA
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAuxSat
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.EntryAndKeyBlock
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceInvariants
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractSegs
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixedExt
import LibsignalBinary.Specifications.LibsignalE2E.State -- shake: keep
import LibsignalBinary.Proofs.CodeLayout

/-!
# `HookSat` Sibling of `CryptoCalleesPlacedBudgetAux`, Part A (`CryptoCalleesPlacedBudgetAuxASat`)

Provides `FinGenPreSat`, `finalize_fixed_gen_placed_runsToVm_sat` (Block `123`
`finalize_fixed` on `HmacStGen` with `320`-B stack under `[HkdfPlacedHooksExactBudgetSat C.F H]`),
and Block `54` (`GenericHkdf::extract`) segments `seg1b_hmc`, `seg1b1_long_hc256`, and
`seg1b2_long_hmc`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetAuxASat

open Arm64 ProofLib SepProp
open CryptoGames.HMAC (ShaState chunks64 hmacWith toBEBytes)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
   libsignalMutatedBlocks libsignalSessionLib lsmpl lsρ)
open CryptoVerification.E2E.Pqxdh.ResponderCore
  (EC88Long ECompLongPlaced EMemcpyLongPlaced FinGenPre HmacStGen
   agreesOutside_writeBytes_sub_sp0 bit_len_inner_gen_eq
   hmacWith_gen innerLastBlockGen innerLastBlockGen_length)
open CryptoVerification.LibsignalAesCbc (toLEBytes)
open CryptoVerification.LibsignalAesCbc.Run.Bytes (readBytes_slice_of_readBytes_eq)
open CryptoVerification.LibsignalHmac (shaStateBytes)
open CryptoVerification.LibsignalTripleRatchet
  (CalleeSaved CallingConventionPreserved_of_calleeSaved ExtractGhost FinSaved Frame
   RW RunsTo RunsToFrom TraceEq agreesOutside_pad_memset agreesOutside_seg2a agreesOutside_seg3a
   agreesOutside_seg4a blkLib_123 blkLib_eq_123 blkPC_123 blkPC_54 blkPl_123 blkPl_54
   digestBytes digestBytes_eq_append effectiveSalt extPlacedFakeB extPlacedFakeB_off_328
   finPlacedFakeB finPlacedFakeB_off_0 finSaved_seg3a finSaved_seg4a
   frame_seg2a frame_seg3a frame_seg4a fsp_aligned
   hmacInnerInit hmacOuterInit lsCompress256Sym lsMemcpySym lsMemsetSym ls_externAt?_of_mem
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
   CallingConventionPreserved.x27 CallingConventionPreserved.x29
   EC88 EMemcpyPlaced ExtCommon ExtFrame ExtSaved ExtSaved_and_Frame_of_agreesOutside_328
   HmacSt.of_writeBytes_32_write8_pos S2Frame
   agreesOutside_sp0_write8 disj_sp0_off disj_sp0_sub_off disj_stk_sub_right rw_stk_sub)
open CryptoVerification.LibsignalTripleRatchet.HkdfExt
  (AgreesOn AgreesOn.finSaved_of AgreesOn.read64_eq AgreesOn.readBytes_eq
   S2Frame.trans_agreesOutside S2Frame.trans_agreesOutside_sub)
open CryptoVerification.LibsignalTripleRatchet.HkdfExt.FinX (read32_seg4a_mid_x)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Heap.MuslMemOpsRunsTo (MemcpyClobber applyMemcpyClobber)
open LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAuxSat
  (placed_memcpy_budget_steps_sat_exact)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetAuxASat
  (RunsToVm RunsToVm.trans RunsToVmFrom finSaved_of_seg1a mem_setMem
   runsToVmFrom_refl runsToVmFrom_step runsToVm_of_from s2Frame_144_to_320
   s2_compress256_multi_step_vm_of_hookSat s2_compress256_step_vm_of_hookSat
   s2_memset_step_vm_of_budget stripS_read64 stripS_read8 stripS_readBytes)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore (HookSatExactMemcpy)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat (HkdfPlacedHooksExactBudgetSat)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
  (CallingConventionPreserved.x23 CallingConventionPreserved.x24 CallingConventionPreserved.x25
   CallingConventionPreserved.x26 CallingConventionPreserved.x28 HookSatCompress256)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixedSat (FinCommonSat FinPostSat)

attribute [local arm64_norm] MemWidth.bytes SimdMemSize.bytes

@[local simp, local arm64_norm]
private theorem extractLsb'_0_64_zero128 : BitVec.extractLsb' 0 64 0#128 = 0#64 := rfl

@[local simp, local arm64_norm]
private theorem extractLsb'_64_64_zero128 : BitVec.extractLsb' 64 64 0#128 = 0#64 := rfl

private theorem ost_eq_seg3a_local {m m₄ : Memory} {hm fsp : BitVec 64} {bs : List (BitVec 8)}
    {m₁ m₂ m₃ : Memory}
    (host : m.readBytes (hm + 0x68#64) 32 = bs)
    (hag1 : AgreesOutside m m₁ hm 64)
    (hag2 : AgreesOutside m₁ m₂ fsp 64)
    (hag3 : AgreesOutside m₂ m₃ hm 64)
    (hag4 : AgreesOutside m₃ m₄ fsp 64)
    (hd_hm64_ost : DisjointRegions hm 64 (hm + 0x68#64) 32)
    (hd_fsp64_ost : DisjointRegions fsp 64 (hm + 0x68#64) 32) :
    m₄.readBytes (hm + 0x68#64) 32 = bs :=
  (hag4.readBytes_eq hd_fsp64_ost (by decide)).trans
    ((hag3.readBytes_eq hd_hm64_ost (by decide)).trans
      ((hag2.readBytes_eq hd_fsp64_ost (by decide)).trans
        ((hag1.readBytes_eq hd_hm64_ost (by decide)).trans host)))

local macro "fin_reg_local" : tactic =>
  `(tactic| (
    try rw [State.readReg64_setMem]
    try rw [State.pc_setMem]
    try rw [State.sp_setMem]
    try rw [State.status_setMem]
    simp (config := { decide := true }) only [arm64_norm, *]))

local macro "s2_step_vm" : tactic => `(tactic| (
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

/-! ## 1. `stripS_hmacStGen` & `FinGenPreSat` (`320`-B Stack) -/

public theorem stripS_hmacStGen (kp : BitVec 64 → Bool)
    {F : ShaState → List (BitVec 8) → ShaState} {s : State} {a : BitVec 64}
    {key blocks rem : List (BitVec 8)} :
    HmacStGen (ProofLib.stripS kp s).mem a F key blocks rem ↔
      HmacStGen s.mem a F key blocks rem := by
  unfold HmacStGen
  simp only [stripS_read8, stripS_read64, stripS_readBytes]

/-- `320`-byte stack precondition for multi-block `finalize_fixed`
(`144` B frame + `176` B `compress256` slack). -/
public structure FinGenPreSat (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) (s0 : State) : Prop extends FinGenPre b F key blocks rem s0 where
  rw_stk320       : s0.mem.RW (s0.sp - 320#64) 320
  disj_out_stk320 : DisjointRegions (s0.readReg64 .x0) 32 (s0.sp - 320#64) 320
  disj_hm_stk320  : DisjointRegions (s0.readReg64 .x1) 0x90 (s0.sp - 320#64) 320

public theorem FinGenPreSat.of_320 [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {key blocks rem : List (BitVec 8)} {s0 : State}
    (hpc : s0.pc = (blkPl_123).base) (hstat : s0.status = .Running)
    (hkey : key.length ≤ 64) (hrem : rem.length < 56)
    (hhmac : HmacStGen s0.mem (s0.readReg64 .x1) F key blocks rem)
    (hrw_out : s0.mem.RW (s0.readReg64 .x0) 32)
    (hrw_hm : s0.mem.RW (s0.readReg64 .x1) 0x90)
    (hrw_stk320 : s0.mem.RW (s0.sp - 320#64) 320)
    (hd_out_hm : DisjointRegions (s0.readReg64 .x0) 32 (s0.readReg64 .x1) 0x90)
    (hd_out_stk320 : DisjointRegions (s0.readReg64 .x0) 32 (s0.sp - 320#64) 320)
    (hd_hm_stk320 : DisjointRegions (s0.readReg64 .x1) 0x90 (s0.sp - 320#64) 320)
    (hsp : (s0.sp &&& 15#64) = 0#64) :
    FinGenPreSat finPlacedFakeB F key blocks rem s0 :=
  { toFinGenPre :=
      { pc_eq := by rw [finPlacedFakeB_off_0]; exact hpc
        status := hstat, key_le := hkey, rem_lt := hrem, hmac_st := hhmac,
        rw_out := hrw_out, rw_hm := hrw_hm,
        rw_fsp := hrw_stk320.sub (by bv_omega),
        disj_out_hm := hd_out_hm,
        disj_out_fsp := by unfold DisjointRegions at hd_out_stk320 ⊢; bv_omega,
        disj_hm_fsp := by unfold DisjointRegions at hd_hm_stk320 ⊢; bv_omega,
        sp_aligned := hsp }
    rw_stk320 := hrw_stk320
    disj_out_stk320 := hd_out_stk320
    disj_hm_stk320 := hd_hm_stk320 }

/-! ## 2. Block `123` (`finalize_fixed` on `HmacStGen`) `RunsToVm` under `HkdfPlacedHooksExactBudgetSat` -/

private structure StateGF0pSat [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = (blkPl_123).base + 28#64
  common  : FinCommonSat s0 s
  x0_eq   : s.readReg64 .x0 = s0.readReg64 .x0
  x1_eq   : s.readReg64 .x1 = s0.readReg64 .x1
  hmac_st : HmacStGen s.mem (s0.readReg64 .x1) F key blocks rem

private structure StateGF1Sat [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq  : s.pc = (blkPl_123).base + 76#64
  common : FinCommonSat s0 s
  x19_eq : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq : s.readReg64 .x20 = s0.readReg64 .x1
  x21_eq : s.readReg64 .x21 = s0.readReg64 .x1 + 0x40#64
  x22_eq : s.readReg64 .x22 = 0x80#64
  x23_eq : s.readReg64 .x23 = BitVec.ofNat 64 rem.length
  x24_eq : s.readReg64 .x24 = BitVec.ofNat 64 (1 + blocks.length / 64)
  x25_eq : s.readReg64 .x25 = BitVec.ofNat 64 (63 - rem.length)
  buf_eq : s.mem.readBytes (s0.readReg64 .x1) 64 =
    rem ++ [0x80#8] ++ List.replicate (63 - rem.length) 0#8
  ist_eq : s.mem.readBytes (s0.readReg64 .x1 + 0x40#64) 32 =
    shaStateBytes ((chunks64 blocks).foldl F (hmacInnerInit F key))
  ost_eq : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)
  obl_eq : s.mem.read64 (s0.readReg64 .x1 + 0x88#64) = 1#64

private structure StateGF2Sat [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq  : s.pc = (blkPl_123).base + 176#64
  common : FinCommonSat s0 s
  x0_eq  : s.readReg64 .x0 = s0.readReg64 .x1 + 0x40#64
  x1_eq  : s.readReg64 .x1 = s0.sp - 144#64
  x2_eq  : s.readReg64 .x2 = 1#64
  x19_eq : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq : s.readReg64 .x20 = s0.readReg64 .x1
  x21_eq : s.readReg64 .x21 = s0.readReg64 .x1 + 0x40#64
  x22_eq : s.readReg64 .x22 = 0x80#64
  blk_eq : s.mem.readBytes (s0.sp - 144#64) 64 = innerLastBlockGen blocks rem
  ist_eq : s.mem.readBytes (s0.readReg64 .x1 + 0x40#64) 32 =
    shaStateBytes ((chunks64 blocks).foldl F (hmacInnerInit F key))
  ost_eq : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)
  obl_eq : s.mem.read64 (s0.readReg64 .x1 + 0x88#64) = 1#64

private structure StateGF3Sat [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq  : s.pc = (blkPl_123).base + 180#64
  common : FinCommonSat s0 s
  x19_eq : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq : s.readReg64 .x20 = s0.readReg64 .x1
  x21_eq : s.readReg64 .x21 = s0.readReg64 .x1 + 0x40#64
  x22_eq : s.readReg64 .x22 = 0x80#64
  ist_eq : s.mem.readBytes (s0.readReg64 .x1 + 0x40#64) 32 =
    shaStateBytes
      (F ((chunks64 blocks).foldl F (hmacInnerInit F key)) (innerLastBlockGen blocks rem))
  ost_eq : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)
  obl_eq : s.mem.read64 (s0.readReg64 .x1 + 0x88#64) = 1#64

private structure StateGF3bSat [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq  : s.pc = (blkPl_123).base + 304#64
  common : FinCommonSat s0 s
  x0_eq  : s.readReg64 .x0 = s0.readReg64 .x1 + 0x68#64
  x1_eq  : s.readReg64 .x1 = s0.sp - 144#64
  x2_eq  : s.readReg64 .x2 = 1#64
  x19_eq : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq : s.readReg64 .x20 = s0.readReg64 .x1
  blk_eq : s.mem.readBytes (s0.sp - 144#64) 64 =
    outerBlock (digestBytes (F ((chunks64 blocks).foldl F (hmacInnerInit F key))
      (innerLastBlockGen blocks rem)))
  ost_eq : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)

private structure StateGF4Sat [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq  : s.pc = (blkPl_123).base + 308#64
  common : FinCommonSat s0 s
  x19_eq : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq : s.readReg64 .x20 = s0.readReg64 .x1
  ost_eq : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 =
    shaStateBytes (F (hmacOuterInit F key)
      (outerBlock (digestBytes (F ((chunks64 blocks).foldl F (hmacInnerInit F key))
        (innerLastBlockGen blocks rem)))))

private structure StateGF5Sat [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq  : s.pc = (blkPl_123).base + 420#64
  common : FinCommonSat s0 s
  out_eq : s.mem.readBytes (s0.readReg64 .x0) 32 = hmacWith F key (blocks ++ rem)

private theorem gseg1a_123 [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    {key blocks rem : List (BitVec 8)} {s0 : State}
    (hpre : FinGenPreSat finPlacedFakeB C.F key blocks rem s0) :
    RunsToVm ((blkPC_123).rebase (blkPl_123).base H) s0 (StateGF0pSat C.F key blocks rem s0) := by
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
      (s0.sp - 144#64) 144 := by agrees_outside_writes
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
      x0_eq := by fin_reg_local, x1_eq := by fin_reg_local
      hmac_st := by
        rw [mem_setMem]
        exact HmacStGen.of_agreesOutside hpre.hmac_st hag hpre.disj_hm_fsp.symm }

private theorem gseg1b_123 [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [hH : HkdfPlacedHooksExactBudgetSat C.F H]
    {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hpre : FinGenPreSat finPlacedFakeB C.F key blocks rem s0)
    (hs : StateGF0pSat C.F key blocks rem s0 s) :
    RunsToVm ((blkPC_123).rebase (blkPl_123).base H) s (StateGF1Sat C.F key blocks rem s0) := by
  apply runsToVm_of_from
  rcases hs with ⟨hpc, hcom, hx0, hx1, hhmac⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  rcases hhmac with ⟨hmod, hblk_le, hmsg_lt64, hmsg_eq, hpos_eq, hin_eq, hibl_eq, hout_eq, hobl_eq⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := hframe.rw_of_rw _ _ hpre.rw_hm
  have hrw_stk320 : s.mem.RW (s0.sp - 320#64) 320 := hframe.rw_of_rw _ _ hpre.rw_stk320
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := hrw_stk320.sub (by bv_omega)
  have hcw_pos : s.mem.canWrite (s0.readReg64 .x1 + BitVec.ofNat 64 rem.length) 1 = true :=
    hrw_hm.canWrite_sub (by bv_omega) (by decide)
  have hze32 := zeroExtend64_truncate32_ofNat64 hmsg_lt64
  have hze64 := zeroExtend64_ofNat8 hmsg_lt64
  have hxor63 := xor_63_of_lt_64 hmsg_lt64
  have hal_fsp : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  iterate 12 s2_step_vm
  have htoNat_sub : (BitVec.ofNat 64 (63 - rem.length)).toNat = 63 - rem.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  set dst := s0.readReg64 .x1 + BitVec.ofNat 64 rem.length + 1#64
  set len := 63 - rem.length
  set m_pre := s.mem.write8 (s0.readReg64 .x1 + BitVec.ofNat 64 rem.length) 128#8
  have hrw_memset : m_pre.RW dst len := by
    refine Memory.RW.of_perm_eq (by simp [m_pre]) (fun _ => Memory.isLazyFree_write8_of_false _ _)
      (hrw_hm.sub ?_)
    have := hpre.rem_lt; dsimp only [dst, len]; bv_omega
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
    agreesOutside_pad_memset s.mem (s0.readReg64 .x1) rem hpre.rem_lt
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
    have hag_pre : AgreesOutside s.mem m_pre (s0.readReg64 .x1 + BitVec.ofNat 64 rem.length) 1 := by
      dsimp only [m_pre]; agrees_outside_writes
    have hf1 : S2Frame s0.mem m_pre
        [(s0.readReg64 .x0, 32), (s0.readReg64 .x1, 0x90), (s0.sp - 320#64, 320)] := by
      have := hpre.rem_lt
      exact S2Frame.trans_agreesOutside_sub hframe (rbase := s0.readReg64 .x1) (rlen := 0x90)
        (by simp) (by bv_omega) hag_pre
    have hs2_frame' : S2Frame m_pre s2.mem [(dst, len)] := by
      simpa only [mem_setMem, arm64_norm] using hs2_frame
    refine hf1.trans (hs2_frame'.mono fun a ha => ?_)
    intro r hr_mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr_mem
    subst hr_mem
    have ha_hm := ha (s0.readReg64 .x1, 0x90) (by simp)
    have := hpre.rem_lt; dsimp only [dst, len]
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
        (readBytes_64_after_pad_memset s.mem (s0.readReg64 .x1) rem hmsg_eq hpre.rem_lt)
      ist_eq := (AgreesOn.readBytes_eq hag_on' (s0.readReg64 .x1 + 0x40#64) 32 (by decide) hP_ist).trans
        ((hag_pad.readBytes_eq hd_hm64_ist (by decide)).trans hin_eq)
      ost_eq := (AgreesOn.readBytes_eq hag_on' (s0.readReg64 .x1 + 0x68#64) 32 (by decide) hP_ost).trans
        ((hag_pad.readBytes_eq hd_hm64_ost (by decide)).trans hout_eq)
      obl_eq := (AgreesOn.read64_eq hag_on' (s0.readReg64 .x1 + 0x88#64) hP_obl).trans
        ((hag_pad.read64_eq hd_hm64_obl).trans hobl_eq) }

set_option maxHeartbeats 800000 in
private theorem gseg2a_123 [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hpre : FinGenPreSat finPlacedFakeB C.F key blocks rem s0)
    (hs : StateGF1Sat C.F key blocks rem s0 s) :
    RunsToVm ((blkPC_123).rebase (blkPl_123).base H) s (StateGF2Sat C.F key blocks rem s0) := by
  apply runsToVm_of_from
  rcases hs with ⟨hpc, hcom, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hbuf, hist, host, hobl⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := hframe.rw_of_rw _ _ hpre.rw_hm
  have hrw_stk320 : s.mem.RW (s0.sp - 320#64) 320 := hframe.rw_of_rw _ _ hpre.rw_stk320
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := hrw_stk320.sub (by bv_omega)
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  have hult_7 := ult_7_of_lt_56 hpre.rem_lt
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
      x19_eq := by fin_reg_local, x20_eq := by fin_reg_local, x21_eq := by fin_reg_local,
      x22_eq := by fin_reg_local
      blk_eq := by
        rw [mem_setMem]
        refine (readBytes_fsp_64_seg2 _ _ _ _ _ _ _ _ _ _ _ _ hd_hm64_fsp64).trans ?_
        rw [toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64,
            toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_rev64,
            readBytes_56_eq_append_8 s.mem (s0.readReg64 .x1),
            readBytes_56_of_buf_eq s.mem (s0.readReg64 .x1) rem hbuf hpre.rem_lt,
            bit_len_inner_gen_eq hpre.hmac_st.1 hpre.hmac_st.2.1 hpre.rem_lt]
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

private theorem gseg2b_123 [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [hH : HkdfPlacedHooksExactBudgetSat C.F H]
    {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hpre : FinGenPreSat finPlacedFakeB C.F key blocks rem s0)
    (hs : StateGF2Sat C.F key blocks rem s0 s) :
    RunsToVm ((blkPC_123).rebase (blkPl_123).base H) s (StateGF3Sat C.F key blocks rem s0) := by
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
    have := hpre.disj_hm_stk320; unfold DisjointRegions at this ⊢; bv_omega
  have hd_ist_blk : DisjointRegions (s0.readReg64 .x1 + 0x40#64) 32 (s0.sp - 144#64) 64 := by
    have := hpre.disj_hm_fsp; unfold DisjointRegions at this ⊢; bv_omega
  have hd_c256_blk : DisjointRegions (s.sp - 176#64) 176 (s0.sp - 144#64) 64 := by
    rw [hsp_sub176]; unfold DisjointRegions; bv_omega
  s2_step_vm
  refine s2_compress256_step_vm_of_hookSat hH.compress256
    (stPtr := s0.readReg64 .x1 + 0x40#64) (blkPtr := s0.sp - 144#64)
    (lr := (blkPl_123).base + 180#64) (st := (chunks64 blocks).foldl C.F (hmacInnerInit C.F key))
    (blk := innerLastBlockGen blocks rem)
    hstat rfl
    (by fin_reg_local) (by fin_reg_local) (by fin_reg_local) rfl
    (by simp only [arm64_norm, hsp]; exact hpre.sp_aligned)
    hist hblk (innerLastBlockGen_length hpre.rem_lt)
    hrw_ist (by simpa only [arm64_norm] using hrw_c256) hread_blk
    (by simpa only [arm64_norm] using hd_ist_c256) hd_ist_blk
    (by simpa only [arm64_norm] using hd_c256_blk)
    fun s2 htr2 hpc2 hstat2 hcc2 _ _ _ hread_ist hs2_frame hag_on => ?_
  refine runsToVmFrom_refl ?_ htr2
  set blk_in := shaStateBytes (C.F ((chunks64 blocks).foldl C.F (hmacInnerInit C.F key))
    (innerLastBlockGen blocks rem))
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
      hP_rw (hrw_hm a ha_hm)
        (by unfold DisjointRegions at hd_hm_c256; unfold InRegion at ha_hm; unfold OutsideRegion; bv_omega)
  have hP_obl : ∀ a, InRegion (s0.readReg64 .x1 + 0x88#64) 8 a →
      (s.mem.perm a).r = true ∧ s.mem.isLazyFree a = false ∧ OutsideRegion (s0.sp - 320#64) 176 a :=
    fun a ha =>
      have ha_hm : InRegion (s0.readReg64 .x1) 0x90 a := by unfold InRegion at ha ⊢; bv_omega
      hP_rw (hrw_hm a ha_hm)
        (by unfold DisjointRegions at hd_hm_c256; unfold InRegion at ha_hm; unfold OutsideRegion; bv_omega)
  have hd_ist_saved :
      DisjointRegions (s0.readReg64 .x1 + 0x40#64) 32 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_ist_ost :
      DisjointRegions (s0.readReg64 .x1 + 0x40#64) 32 (s0.readReg64 .x1 + 0x68#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_ist_obl :
      DisjointRegions (s0.readReg64 .x1 + 0x40#64) 32 (s0.readReg64 .x1 + 0x88#64) 8 := by
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

set_option maxHeartbeats 800000 in
private theorem gseg3a_123 [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hpre : FinGenPreSat finPlacedFakeB C.F key blocks rem s0)
    (hs : StateGF3Sat C.F key blocks rem s0 s) :
    RunsToVm ((blkPC_123).rebase (blkPl_123).base H) s (StateGF3bSat C.F key blocks rem s0) := by
  apply runsToVm_of_from
  rcases hs with ⟨hpc, hcom, hx19, hx20, hx21, hx22, hist, host, hobl⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := hframe.rw_of_rw _ _ hpre.rw_hm
  have hrw_stk320 : s.mem.RW (s0.sp - 320#64) 320 := hframe.rw_of_rw _ _ hpre.rw_stk320
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := hrw_stk320.sub (by bv_omega)
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  set h_in := C.F ((chunks64 blocks).foldl C.F (hmacInnerInit C.F key))
    (innerLastBlockGen blocks rem)
  obtain ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7⟩ :=
    read32_words_at_64_of_shaStateBytes s.mem (s0.readReg64 .x1) h_in hist
  have hd_hm64_fsp64 : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64) 64 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hrev768 : rev64 (256#64 ||| 512#64) = (3#64 <<< 48) := by decide
  have hread32 := fun w0 w1 w2 w3 w4 w5 w6 w7 u0 u1 u2 u3 =>
    read64_seg3a_pad_32 s.mem _ _ w0 w1 w2 w3 w4 w5 w6 w7 u0 u1 u2 u3 hd_hm64_fsp64
  have hread40 := fun w0 w1 w2 w3 w4 w5 w6 w7 u0 u1 u2 u3 =>
    read64_seg3a_pad_40 s.mem _ _ w0 w1 w2 w3 w4 w5 w6 w7 u0 u1 u2 u3 hd_hm64_fsp64
  iterate 31 s2_step_vm
  clear hread32 hread40 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hist
  refine runsToVmFrom_refl ?_
  obtain ⟨hag1, hag2, hag3, hag4⟩ := agreesOutside_seg3a s.mem (s0.readReg64 .x1) (s0.sp - 144#64)
    _ _ _ _ _ _ _ _ _ _ _ _ 0#64 (3#64 <<< 48) 0x80#64 0#64 0#64 (3#64 <<< 48)
  have hd_hm64_saved : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_fsp64_saved : DisjointRegions (s0.sp - 144#64) 64 (s0.sp - 144#64 + 0x40#64) 0x50 := by
    unfold DisjointRegions; bv_omega
  have hd_hm64_ost : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x68#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_fsp64_ost : DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1 + 0x68#64) 32 :=
    (hpre.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
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
        exact ost_eq_seg3a_local host hag1 hag2 hag3 hag4 hd_hm64_ost hd_fsp64_ost }

private theorem gseg3b_123 [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [hH : HkdfPlacedHooksExactBudgetSat C.F H]
    {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hpre : FinGenPreSat finPlacedFakeB C.F key blocks rem s0)
    (hs : StateGF3bSat C.F key blocks rem s0 s) :
    RunsToVm ((blkPC_123).rebase (blkPl_123).base H) s (StateGF4Sat C.F key blocks rem s0) := by
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
  set h_in := C.F ((chunks64 blocks).foldl C.F (hmacInnerInit C.F key))
    (innerLastBlockGen blocks rem)
  s2_step_vm
  refine s2_compress256_step_vm_of_hookSat hH.compress256
    (stPtr := s0.readReg64 .x1 + 0x68#64) (blkPtr := s0.sp - 144#64)
    (lr := (blkPl_123).base + 308#64)
    (st := hmacOuterInit C.F key) (blk := outerBlock (digestBytes h_in))
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
  have hd_ost_saved :
      DisjointRegions (s0.readReg64 .x1 + 0x68#64) 32 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
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

private theorem gseg4a_disj {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {key blocks rem : List (BitVec 8)} {s0 : State} (hpre : FinGenPre b F key blocks rem s0) :
    DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1) 0x90 ∧
    DisjointRegions (s0.readReg64 .x1) 0x90 (s0.sp - 144#64 + 0x40#64) 0x50 ∧
    DisjointRegions (s0.sp - 144#64) 64 (s0.sp - 144#64 + 0x40#64) 0x50 ∧
    DisjointRegions (s0.readReg64 .x0) 32 (s0.sp - 144#64 + 0x40#64) 0x50 :=
  ⟨hpre.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩,
   hpre.disj_hm_fsp.sub_right _ ⟨by decide, by bv_omega⟩,
   by unfold DisjointRegions; bv_omega,
   hpre.disj_out_fsp.sub_right _ ⟨by decide, by bv_omega⟩⟩

set_option maxHeartbeats 800000 in
private theorem gseg4a_123 [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hpre : FinGenPreSat finPlacedFakeB C.F key blocks rem s0)
    (hs : StateGF4Sat C.F key blocks rem s0 s) :
    RunsToVm ((blkPC_123).rebase (blkPl_123).base H) s (StateGF5Sat C.F key blocks rem s0) := by
  apply runsToVm_of_from
  rcases hs with ⟨hpc, hcom, hx19, hx20, host⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := hframe.rw_of_rw _ _ hpre.rw_hm
  have hrw_stk320 : s.mem.RW (s0.sp - 320#64) 320 := hframe.rw_of_rw _ _ hpre.rw_stk320
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := hrw_stk320.sub (by bv_omega)
  have hrw_out : s.mem.RW (s0.readReg64 .x0) 32 := hframe.rw_of_rw _ _ hpre.rw_out
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  set h_out := C.F (hmacOuterInit C.F key)
    (outerBlock (digestBytes (C.F ((chunks64 blocks).foldl C.F (hmacInnerInit C.F key))
      (innerLastBlockGen blocks rem))))
  obtain ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7⟩ :=
    read32_words_at_104_of_shaStateBytes s.mem (s0.readReg64 .x1) h_out host
  have hzero64 : (0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 : BitVec 64) = 0#64 := rfl
  iterate 11 s2_step_vm
  have hd_fsp64_hm := (gseg4a_disj hpre.toFinGenPre).1
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
  obtain ⟨_, hd_hm_saved, hd_fsp64_saved, hd_out_saved⟩ := gseg4a_disj hpre.toFinGenPre
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
          (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _)
          (toLEBytes_4_rev32 _)).trans
          (hmacWith_gen C.F key blocks rem hpre.key_le hpre.hmac_st.1 hpre.rem_lt).symm }

private theorem gseg4b_123 [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    {key blocks rem : List (BitVec 8)} {s0 s : State}
    (hpre : FinGenPreSat finPlacedFakeB C.F key blocks rem s0)
    (hs : StateGF5Sat C.F key blocks rem s0 s) :
    RunsToVm ((blkPC_123).rebase (blkPl_123).base H) s
      (FinPostSat C.F key (blocks ++ rem) s0) := by
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

/-- Full relocatable `RunsToVm` contract of Block `123` (`finalize_fixed` on `HmacStGen`, `320`-B stack)
under `[HkdfPlacedHooksExactBudgetSat C.F H]` with `FinPostSat` (`S2Frame`). -/
public theorem finalize_fixed_gen_placed_runsToVm_sat [LibsignalPlacement] {C : Crypto}
    {H : LibsignalHooks} [hH : HkdfPlacedHooksExactBudgetSat C.F H]
    {key blocks rem : List (BitVec 8)} {s0 : State}
    (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (hpre : FinGenPreSat finPlacedFakeB C.F key blocks rem s0) :
    RunsToVm ((blkPC_123).rebase (blkPl_123).base H) s0
      (FinPostSat C.F key (blocks ++ rem) s0) :=
  (gseg1a_123 hpre).trans fun _ hs1 =>
  (gseg1b_123 hpre hs1).trans fun _ hs2 =>
  (gseg2a_123 hpre hs2).trans fun _ hs3 =>
  (gseg2b_123 hpre hs3).trans fun _ hs4 =>
  (gseg3a_123 hpre hs4).trans fun _ hs5 =>
  (gseg3b_123 hpre hs5).trans fun _ hs6 =>
  (gseg4a_123 hpre hs6).trans fun _ hs7 =>
  gseg4b_123 hpre hs7

/-! ## 3. `memset`-Free Block `54` (`GenericHkdf::extract`) Segments -/

private theorem readable_of_rw {m : Memory} {a : BitVec 64} {n : Nat} (h : m.RW a n) :
    m.Readable a n := fun x hx =>
  let ⟨hp, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp (h x hx); ⟨by rw [hp]; rfl, hlf⟩

private theorem runsToVm_of_steps {prog : Program} {s s₁ : State} {P : State → Prop}
    (hst1 : Steps prog s s₁) (hvm1 : VmPreserved s s₁) (htr1 : TraceEq s s₁)
    (hrest : RunsToVm prog s₁ P) : RunsToVm prog s P := fun hL => by
  obtain ⟨sf, hst2, hvm2, htr2, hv2, hpost, hL2⟩ := hrest (hst1.codeLoaded hL)
  exact ⟨sf, hst1.trans hst2, hvm1.trans hvm2, htr2.trans htr1.1, hv2.trans htr1.2, hpost, hL2⟩

/-- `memset`-free `Extract.seg1b_placed_runsTo` lifted to `RunsToVm` under `hmc`. -/
public theorem seg1b_hmc [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    (hmc : HookSatExactMemcpy H lsMemcpySym)
    {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hRW_ikm : RW s0.mem x.ikmA 32)
    (hikm_len : x.ikm.length = 32)
    (hikm_mem0 : s0.mem.readBytes x.ikmA 32 = x.ikm)
    (hd_ikm_stk : DisjointRegions x.ikmA 32 (sp0 - 544#64) 976)
    (hd_ikm_out : DisjointRegions x.ikmA 32 (s0.readReg64 .x0) 0xb0)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : EMemcpyPlaced C.F x s0 sp0 s) :
    RunsToVm ((blkPC_54).rebase (blkPl_54).base H) s (EC88 extPlacedFakeB C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hlr, hx0, hx1, hx2, hx21, hx22, hx25, hhm⟩
  have hsp_s : s.spAligned = true := by simpa [State.spAligned, hsp] using hsp_al
  have hikm_s : s.mem.readBytes x.ikmA 32 = x.ikm := by
    rw [hframe.readBytes_eq hRW_ikm ?_ (by decide)]; · exact hikm_mem0
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl; exacts [hd_ikm_out.symm, hd_ikm_stk.symm]
  have hsub_432 : (sp0 - (sp0 - 544#64)).toNat + 432 ≤ 976 := by
    rw [show sp0 - (sp0 - 544#64) = 544#64 by bv_lin]; decide
  have hrw_sp0_s : s.mem.RW sp0 432 := hframe.rw_of_rw sp0 432 (rw_stk_sub hRW_stk sp0 432 hsub_432)
  have hrw_sp0_32 : s.mem.RW sp0 32 := hrw_sp0_s.sub (by bv_omega)
  have hread_ikm_s : s.mem.Readable x.ikmA 32 := readable_of_rw (hframe.rw_of_rw x.ikmA 32 hRW_ikm)
  have hdisj_ikm : 32 = 0 ∨ DisjointRegions sp0 32 x.ikmA 32 :=
    Or.inr (disj_stk_sub_right hd_ikm_stk sp0 32 ⟨by decide, by omega⟩).symm
  intro hL
  obtain ⟨c, hst1, hvm1, htr1, hv1⟩ :=
    placed_memcpy_budget_steps_sat_exact (prog := (blkPC_54).rebase (blkPl_54).base H) (i := 54)
      hmc hstat hpc hx0 hx1 (by rw [hx2]; rfl) hlr hsp_s hikm_s hrw_sp0_32 hread_ikm_s hdisj_ikm
  refine runsToVm_of_steps hst1 hvm1 ⟨htr1, hv1⟩ (runsToVm_of_from ?_) hL
  dsimp only [applyMemcpyClobber]
  have hag_mc : AgreesOutside s.mem (s.mem.writeBytes sp0 x.ikm) sp0 328 :=
    (ProofLib.AgreesOutside.writeBytes_self s.mem sp0 x.ikm).mono (by omega)
  have hrw_sp0 : (s.mem.writeBytes sp0 x.ikm).RW sp0 432 :=
    CryptoVerification.LibsignalTripleRatchet.rw_of_perm_eq hag_mc.2 hrw_sp0_s
  iterate 3 s2_step_vm
  refine runsToVmFrom_refl ?_
  have hag : AgreesOutside s.mem ((s.mem.writeBytes sp0 x.ikm).write8 (sp0 + 63#64) 32#8) sp0 328 :=
    agreesOutside_sp0_write8 hag_mc (by decide)
  unfold EC88 ExtCommon
  simp (config := { decide := true }) only [State.readReg64_setMem, State.readReg64_setPC,
    State.readReg64_setPState, State.readReg64_advancePC, State.readReg64_writeReg64,
    Reg.x19, Reg.x27, Reg.x29, Reg.x22, ite_false, extPlacedFakeB_off_328]
  dsimp only [State.setMem, State.setPC, State.setPState, State.advancePC, State.writeReg64]
  exact ⟨⟨hstat, hsp, hx19, hx27, hx29,
    ExtSaved_and_Frame_of_agreesOutside_328 hsaved hframe hag⟩,
    rfl, hx22, HmacSt.of_writeBytes_32_write8_pos hhm hikm_len⟩

/-- `memset`-free `seg1b1_long_placed_runsTo` lifted to `RunsToVm` under `hc256` (`HookSatCompress256`). -/
public theorem seg1b1_long_hc256 [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    (hc256 : HookSatCompress256 H lsCompress256Sym C.F)
    {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hRW_ikm : RW s0.mem x.ikmA x.ikm.length)
    (hikm_len : x.ikm.length = 160 ∨ x.ikm.length = 192 ∨ x.ikm.length = 224)
    (hikm_mem0 : s0.mem.readBytes x.ikmA x.ikm.length = x.ikm)
    (hd_ikm_stk : DisjointRegions x.ikmA x.ikm.length (sp0 - 544#64) 976)
    (hd_ikm_out : DisjointRegions x.ikmA x.ikm.length (s0.readReg64 .x0) 0xb0)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : ECompLongPlaced C.F x s0 sp0 s) :
    RunsToVm ((blkPC_54).rebase (blkPl_54).base H) s (EMemcpyLongPlaced C.F x s0 sp0) := by
  apply runsToVm_of_from
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hlr, hx0, hx1, hx2, hx20, hx21, hx22, hx24, hist, hcnt1, hout, hcnt2⟩
  have hikm_le : x.ikm.length ≤ 2 ^ 64 := by rcases hikm_len with h | h | h <;> (rw [h]; decide)
  have hikm_s : s.mem.readBytes x.ikmA x.ikm.length = x.ikm := by
    rw [hframe.readBytes_eq hRW_ikm ?_ hikm_le]
    · exact hikm_mem0
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl; exacts [hd_ikm_out.symm, hd_ikm_stk.symm]
  have hblk_s : s.mem.readBytes x.ikmA (64 * (x.ikm.length / 64)) =
      x.ikm.take (64 * (x.ikm.length / 64)) := by
    simpa using readBytes_slice_of_readBytes_eq s.mem x.ikmA x.ikm hikm_s 0
      (64 * (x.ikm.length / 64)) (by omega)
  have hsub_432 : (sp0 - (sp0 - 544#64)).toNat + 432 ≤ 976 := by
    rw [show sp0 - (sp0 - 544#64) = 544#64 by bv_lin]; decide
  have hsub_40 : 0 < 32 ∧ ((sp0 + 0x40#64) - (sp0 - 544#64)).toNat + 32 ≤ 976 := by
    rw [show (sp0 + 0x40#64) - (sp0 - 544#64) = 608#64 by bv_lin]; decide
  have hsub_m176 : 0 < 176 ∧ ((sp0 - 176#64) - (sp0 - 544#64)).toNat + 176 ≤ 976 := by
    rw [show (sp0 - 176#64) - (sp0 - 544#64) = 368#64 by bv_lin]; decide
  have hsub_336 : ((sp0 + 336#64) - (sp0 - 544#64)).toNat + 96 ≤ 976 := by
    rw [show (sp0 + 336#64) - (sp0 - 544#64) = 880#64 by bv_lin]; decide
  have hrw_sp0_s : s.mem.RW sp0 432 := hframe.rw_of_rw sp0 432 (rw_stk_sub hRW_stk sp0 432 hsub_432)
  have hrw_sp0_40 : s.mem.RW (sp0 + 0x40#64) 32 := hrw_sp0_s.sub (by bv_omega)
  have hrw_c256 : s.mem.RW (s.sp - 176#64) 176 := by
    rw [hsp]; exact hframe.rw_of_rw _ _ (rw_stk_sub hRW_stk _ _ hsub_m176.2)
  have hread_blk : s.mem.Readable x.ikmA (64 * (x.ikm.length / 64)) :=
    readable_of_rw ((hframe.rw_of_rw x.ikmA x.ikm.length hRW_ikm).sub
      (by rcases hikm_len with h | h | h <;> (rw [h]; bv_omega)))
  have hd_blk_stk : DisjointRegions x.ikmA (64 * (x.ikm.length / 64)) (sp0 - 544#64) 976 :=
    hd_ikm_stk.sub_left x.ikmA ⟨by rcases hikm_len with h | h | h <;> (rw [h]; decide),
      by rcases hikm_len with h | h | h <;> (rw [h]; bv_omega)⟩
  have hx2_nat : (s.readReg64 .x2).toNat = x.ikm.length / 64 := by
    rcases hikm_len with h | h | h <;> (rw [hx2, h]; rfl)
  refine s2_compress256_multi_step_vm_of_hookSat hc256
    hstat hpc hx0 hx1 hx2_nat hlr (by rw [hsp]; exact hsp_al) hist hblk_s
    hrw_sp0_40 hrw_c256 hread_blk
    (by rw [hsp]; exact (disj_sp0_sub_off sp0 176#64 176 0x40#64 32 (by decide)).symm)
    (Or.inr (disj_stk_sub_right hd_blk_stk (sp0 + 0x40#64) 32 hsub_40).symm)
    (by rw [hsp]; exact Or.inr (disj_stk_sub_right hd_blk_stk (sp0 - 176#64) 176 hsub_m176).symm)
    (fun s2 htr2 hpc2 hstat2 hcc2 _ _ _ hread_ist2 hs2_frame _ => ?_)
    (by rcases hikm_len with h | h | h <;> (rw [h]; decide))
  rw [hsp] at hs2_frame
  have hsp2 : s2.sp = sp0 := (CallingConventionPreserved.sp_eq hcc2).trans hsp
  have hx19_2 : s2.readReg64 .x19 = s0.readReg64 .x0 :=
    (CallingConventionPreserved.x19 hcc2).trans hx19
  have hx20_2 : s2.readReg64 .x20 = x.ikmA :=
    (CallingConventionPreserved.x20 hcc2).trans hx20
  have hx21_2 : s2.readReg64 .x21 = BitVec.ofNat 64 (x.ikm.length % 64) :=
    (CallingConventionPreserved.x21 hcc2).trans hx21
  have hx22_2 : s2.readReg64 .x22 = sp0 + 176#64 :=
    (CallingConventionPreserved.x22 hcc2).trans hx22
  have hx24_2 : s2.readReg64 .x24 = BitVec.ofNat 64 (64 * (x.ikm.length / 64)) :=
    (CallingConventionPreserved.x24 hcc2).trans hx24
  have hx27_2 : s2.readReg64 .x27 = s0.readReg64 .x27 :=
    (CallingConventionPreserved.x27 hcc2).trans hx27
  have hx29_2 : s2.readReg64 .x29 = sp0 + 336#64 :=
    (CallingConventionPreserved.x29 hcc2).trans hx29
  have hframe2 : ExtFrame s0 sp0 s2.mem :=
    ExtFrame.trans_pair hframe hs2_frame hsub_40.2 hsub_m176.2
  have hsaved2 : ExtSaved s0 sp0 s2.mem := by
    refine hsaved.of_s2frame hs2_frame (hframe.rw_of_rw _ _ (rw_stk_sub hRW_stk _ _ hsub_336)) ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact disj_sp0_off sp0 0x40#64 32 336#64 96 (by decide)
    · exact disj_sp0_sub_off sp0 176#64 176 336#64 96 (by decide)
  have hcnt1_2 : s2.mem.read64 (sp0 + 0x60#64) = BitVec.ofNat 64 (1 + x.ikm.length / 64) := by
    rw [hs2_frame.read64_eq (hrw_sp0_s.sub (by bv_omega))]
    · exact hcnt1
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact disj_sp0_off sp0 0x40#64 32 0x60#64 8 (by decide)
      · exact disj_sp0_sub_off sp0 176#64 176 0x60#64 8 (by decide)
  have hout_2 : s2.mem.readBytes (sp0 + 0x68#64) 32 =
      shaStateBytes (hmacOuterInit C.F (effectiveSalt x.salt)) := by
    rw [hs2_frame.readBytes_eq (hrw_sp0_s.sub (by bv_omega)) ?_ (by decide)]
    · exact hout
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact disj_sp0_off sp0 0x40#64 32 0x68#64 32 (by decide)
      · exact disj_sp0_sub_off sp0 176#64 176 0x68#64 32 (by decide)
  have hcnt2_2 : s2.mem.read64 (sp0 + 0x88#64) = 1#64 := by
    rw [hs2_frame.read64_eq (hrw_sp0_s.sub (by bv_omega))]
    · exact hcnt2
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact disj_sp0_off sp0 0x40#64 32 0x88#64 8 (by decide)
      · exact disj_sp0_sub_off sp0 176#64 176 0x88#64 8 (by decide)
  have hrw_sp0_2 : s2.mem.RW sp0 432 :=
    hframe2.rw_of_rw sp0 432 (rw_stk_sub hRW_stk sp0 432 hsub_432)
  iterate 5 s2_step_vm
  refine runsToVmFrom_refl ?_ htr2
  have hag_w8 : AgreesOutside s2.mem
      (s2.mem.write8 (sp0 + 63#64) (BitVec.ofNat 8 (x.ikm.length % 64))) sp0 328 :=
    agreesOutside_sp0_write8 (AgreesOutside.rfl' _ _ _) (by decide)
  have hag_self : AgreesOutside s2.mem
      (s2.mem.write8 (sp0 + 63#64) (BitVec.ofNat 8 (x.ikm.length % 64))) (sp0 + 63#64) 1 := by
    agrees_outside_writes
  unfold EMemcpyLongPlaced ExtCommon
  simp (config := { decide := true }) only [State.readReg64_setMem, State.readReg64_setPC,
    State.readReg64_advancePC, State.readReg64_writeReg64,
    Reg.lr, Reg.x0, Reg.x1, Reg.x2, Reg.x19, Reg.x27, Reg.x29, Reg.x22, ite_true, ite_false]
  dsimp only [State.setMem, State.setPC, State.advancePC, State.writeReg64]
  exact ⟨⟨hstat2, hsp2, hx19_2, hx27_2, hx29_2,
    hsaved2.of_agreesOutside_328 hag_w8,
    ExtFrame.of_agreesOutside_sp0 hframe2 (by decide) hag_w8⟩,
    rfl, trivial, trivial, trivial, trivial, hx22_2,
    by simp (config := { decide := true }) only [arm64_norm],
    (hag_self.readBytes_eq (disj_sp0_off sp0 63#64 1 0x40#64 32 (by decide)) (by decide)).trans
      hread_ist2,
    (hag_self.read64_eq (disj_sp0_off sp0 63#64 1 0x60#64 8 (by decide))).trans hcnt1_2,
    (hag_self.readBytes_eq (disj_sp0_off sp0 63#64 1 0x68#64 32 (by decide)) (by decide)).trans
      hout_2,
    (hag_self.read64_eq (disj_sp0_off sp0 63#64 1 0x88#64 8 (by decide))).trans hcnt2_2⟩

/-- `RunsTo` projection of `seg1b1_long_hc256`. -/
public theorem seg1b1_long_hc256_runsTo [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    (hc256 : HookSatCompress256 H lsCompress256Sym C.F)
    {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hRW_ikm : RW s0.mem x.ikmA x.ikm.length)
    (hikm_len : x.ikm.length = 160 ∨ x.ikm.length = 192 ∨ x.ikm.length = 224)
    (hikm_mem0 : s0.mem.readBytes x.ikmA x.ikm.length = x.ikm)
    (hd_ikm_stk : DisjointRegions x.ikmA x.ikm.length (sp0 - 544#64) 976)
    (hd_ikm_out : DisjointRegions x.ikmA x.ikm.length (s0.readReg64 .x0) 0xb0)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : ECompLongPlaced C.F x s0 sp0 s) :
    RunsTo ((blkPC_54).rebase (blkPl_54).base H) s (EMemcpyLongPlaced C.F x s0 sp0) :=
  fun hL =>
    let ⟨sf, hst, _, htr, hv, hp, hLf⟩ :=
      seg1b1_long_hc256 hc256 hRW_stk hRW_ikm hikm_len hikm_mem0 hd_ikm_stk hd_ikm_out hsp_al hs hL
    ⟨sf, hst, ⟨htr, hv⟩, hp, hLf⟩

/-- `memset`-free `seg1b2_long_placed_runsTo` lifted to `RunsToVm` under `hmc`. -/
public theorem seg1b2_long_hmc [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    (hmc : HookSatExactMemcpy H lsMemcpySym)
    {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hRW_ikm : RW s0.mem x.ikmA x.ikm.length)
    (hikm_len : x.ikm.length = 160 ∨ x.ikm.length = 192 ∨ x.ikm.length = 224)
    (hikm_mem0 : s0.mem.readBytes x.ikmA x.ikm.length = x.ikm)
    (hd_ikm_stk : DisjointRegions x.ikmA x.ikm.length (sp0 - 544#64) 976)
    (hd_ikm_out : DisjointRegions x.ikmA x.ikm.length (s0.readReg64 .x0) 0xb0)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : EMemcpyLongPlaced C.F x s0 sp0 s) :
    RunsToVm ((blkPC_54).rebase (blkPl_54).base H) s (EC88Long extPlacedFakeB C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hlr, hx0, hx1, hx2, hx22, hpos, hist, hcnt1, hout, hcnt2⟩
  have hsp_s : s.spAligned = true := by simpa [State.spAligned, hsp] using hsp_al
  have hikm_le : x.ikm.length ≤ 2 ^ 64 := by rcases hikm_len with h | h | h <;> (rw [h]; decide)
  have hikm_s : s.mem.readBytes x.ikmA x.ikm.length = x.ikm := by
    rw [hframe.readBytes_eq hRW_ikm ?_ hikm_le]
    · exact hikm_mem0
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl; exacts [hd_ikm_out.symm, hd_ikm_stk.symm]
  have hblk_len : (x.ikm.take (64 * (x.ikm.length / 64))).length = 64 * (x.ikm.length / 64) := by
    simp; omega
  have hrem_len : (x.ikm.drop (64 * (x.ikm.length / 64))).length = x.ikm.length % 64 := by
    simp; omega
  have hrem_s : s.mem.readBytes
      (x.ikmA + BitVec.ofNat 64 (64 * (x.ikm.length / 64))) (x.ikm.length % 64) =
      x.ikm.drop (64 * (x.ikm.length / 64)) := by
    have h := readBytes_slice_of_readBytes_eq s.mem x.ikmA x.ikm hikm_s
      (64 * (x.ikm.length / 64)) (x.ikm.length % 64) (by omega)
    exact h.trans (List.take_of_length_le (by simp; omega))
  have hsub_432 : (sp0 - (sp0 - 544#64)).toNat + 432 ≤ 976 := by
    rw [show sp0 - (sp0 - 544#64) = 544#64 by bv_lin]; decide
  have hrw_sp0_s : s.mem.RW sp0 432 := hframe.rw_of_rw sp0 432 (rw_stk_sub hRW_stk sp0 432 hsub_432)
  have hrw_sp0_nrem : s.mem.RW sp0 (x.ikm.length % 64) := hrw_sp0_s.sub (by bv_omega)
  have hread_rem_s : s.mem.Readable
      (x.ikmA + BitVec.ofNat 64 (64 * (x.ikm.length / 64))) (x.ikm.length % 64) :=
    readable_of_rw ((hframe.rw_of_rw x.ikmA x.ikm.length hRW_ikm).sub
      (by rcases hikm_len with h | h | h <;> (rw [h]; bv_omega)))
  have hdisj_rem : x.ikm.length % 64 = 0 ∨ DisjointRegions sp0 (x.ikm.length % 64)
      (x.ikmA + BitVec.ofNat 64 (64 * (x.ikm.length / 64))) (x.ikm.length % 64) := by
    by_cases h0 : x.ikm.length % 64 = 0
    · exact Or.inl h0
    · exact Or.inr ((hd_ikm_stk.sub_left _ ⟨by omega,
        by rcases hikm_len with h | h | h <;> (rw [h]; bv_omega)⟩).sub_right sp0
        ⟨by omega, by rcases hikm_len with h | h | h <;> (rw [h] at h0 ⊢; bv_omega)⟩).symm
  have hx2_nat : (s.readReg64 .x2).toNat = x.ikm.length % 64 := by
    rcases hikm_len with h | h | h <;> (rw [hx2, h]; rfl)
  intro hL
  obtain ⟨c, hst1, hvm1, htr1, hv1⟩ :=
    placed_memcpy_budget_steps_sat_exact (prog := (blkPC_54).rebase (blkPl_54).base H) (i := 54)
      hmc hstat hpc hx0 hx1 hx2_nat hlr hsp_s hrem_s hrw_sp0_nrem hread_rem_s hdisj_rem
  refine ⟨_, hst1, hvm1, htr1, hv1, ?_, hst1.codeLoaded hL⟩
  dsimp only [applyMemcpyClobber]
  have hag_mc : AgreesOutside s.mem
      (s.mem.writeBytes sp0 (x.ikm.drop (64 * (x.ikm.length / 64)))) sp0 328 :=
    agreesOutside_writeBytes_sub_sp0 (by rw [BitVec.sub_self, hrem_len]; bv_omega)
  unfold EC88Long ExtCommon
  simp (config := { decide := true }) only [State.readReg64_setMem, State.readReg64_setPC,
    State.readReg64_setPState, State.readReg64_writeReg64,
    Reg.x19, Reg.x27, Reg.x29, Reg.x22, ite_false, extPlacedFakeB_off_328]
  dsimp only [State.setMem, State.setPC, State.setPState, State.writeReg64]
  refine ⟨⟨hstat, hsp, hx19, hx27, hx29,
    ExtSaved_and_Frame_of_agreesOutside_328 hsaved hframe hag_mc⟩, rfl, hx22, ?_⟩
  have hcnt1' : s.mem.read64 (sp0 + 0x60#64) =
      BitVec.ofNat 64 (1 + (x.ikm.take (64 * (x.ikm.length / 64))).length / 64) := by
    rw [hblk_len, Nat.mul_div_cancel_left _ (by decide)]; exact hcnt1
  have hpos' : s.mem.read8 (sp0 + 0x3f#64) =
      BitVec.ofNat 8 (x.ikm.drop (64 * (x.ikm.length / 64))).length := by
    rw [hrem_len]; exact hpos
  exact HmacStGen.of_memcpy_rem (by rw [hblk_len]; omega) (by rw [hblk_len]; omega)
    (by rw [hrem_len]; omega) hpos' hist hcnt1' hout hcnt2

end LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetAuxASat
