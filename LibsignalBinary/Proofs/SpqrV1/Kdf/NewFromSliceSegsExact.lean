/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.DefsSat
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSlice
public import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSliceGt64 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.CompressAndDigest
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.EntryAndKeyBlock -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceFirstHalf
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.NewFromSlice
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandCommon
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractCommon
import LibsignalBinary.Proofs.CodeLayout

/-!
# `HookSatExactMemcpy` and `HookSatCompress256` siblings of `SpqrV1.Kdf.NewFromSlice*` (Block `402`)

Replaces `h_memcpy : H lsMemcpySym = some memcpyHook` and
`h_compress : H lsCompress256Sym = some (compress256Hook F)` on Block `402`'s segments with
`h_mc : HookSatExactMemcpy H lsMemcpySym` and `h_c256 : HookSatCompress256 H lsCompress256Sym F`
(`720`-byte stack = `544 + 176`).
-/

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSliceSegsExact

open Arm64 ProofLib
open CryptoGames.HMAC (ShaState chunks64 sha256IV)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement LibsignalRoLoaded blkPl_402
   libsignalMutatedBlocks lsProg_402 lsmpl lsρ
   subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open CryptoVerification.LibsignalAesCbc.Run.Bytes (readBytes_slice_of_readBytes_eq)
open CryptoVerification.LibsignalHmac (shaStateBytes)
open CryptoVerification.LibsignalSession.CryptoHmacSha256
  (AgreesOutside.write64_self AgreesOutside.write8_self CalleeSaved
   CallingConventionPreserved_of_calleeSaved Frame NfsSavedStack RW RunsTo RunsTo.lsProg_svc
   RunsToFrom TraceEq
   TraceEq.advancePC_step TraceEq.refl TraceEq.setMem_step TraceEq.setPC_step
   TraceEq.setPState_step TraceEq.writeReg32_step TraceEq.writeReg64_step
   TraceEq.writeVReg128_step agreesOutside_nfsPrologueMem agreesOutside_toFrame
   disjointRegions_of_ro_rw innerState keyBlock keyBlock_length lsCompress256Sym lsMemcpySym
   ls_externAt?_of_mem nfsPrologueMem nfsSavedStack_prologue_432 nfsSp nfs_sp_add_464_align
   nfs_sp_add_544_align nfs_sp_align nfs_sp_eq_add nfs_ule_65_false
   readBytes_writeBytes_16_other readBytes_writeBytes_16_self rw_xorChunk
   shaStateBytes_length slice16 slice16_length write128_pair_ivsw write64_oct_zero_eq_writeBytes_64
   write64_quad_288_eq_writeBytes_slice16 writeBytes_key_over_zero64 xorChunk xorChunk4_eq_writeBytes
   map_xor_0x36_0x6a)
open CryptoVerification.LibsignalTripleRatchet (HmacSt chunks64_single_foldl)
open CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer (isBlock_nfsResult)
open CryptoVerification.LibsignalTripleRatchet.Extract
  (CallingConventionPreserved.x19 CallingConventionPreserved.x20
   CallingConventionPreserved.x21 CallingConventionPreserved.x22
   CallingConventionPreserved.x27 CallingConventionPreserved.x29 S2Frame)
open CryptoVerification.LibsignalTripleRatchet.HkdfExt (AgreesOn)
open CryptoVerification.SpqrV1.Kdf (ikm_split_lemmas)
open CryptoVerification.SpqrV1.Kdf.NewFromSlice3GenProof
  (StateG0 StateG1 agreesOutside_nfsZeroMem agreesOutside_sub_176_288
   nfs3CodeFakeB nfsZeroMem readBytes_take_of_le write64_quad_240_iv_placed)
open CryptoVerification.SpqrV1.Kdf.NewFromSlice3Proof
  (Nfs3OpadPostHookPlaced Nfs3PostCompress2Placed Nfs3PreCompress2Placed
   NfsMemInv3 NfsRegInv3 nfs3PlacedFakeB nfs3PlacedFakeB_add_iv nfs_chunk1_placed
   nfs_chunk2_placed nfs_chunk3_placed nfs_chunk4_placed nfs_epilogue_placed
   nfs_opad_chunk0_placed nfs_opad_chunk1_placed nfs_opad_chunk2_placed nfs_opad_chunk3_placed
   rodata_placed_spqrSha256IV spqrSha256IVAddr)
open LibsignalBinary.Heap.MuslMemOpsRunsTo (applyMemcpyClobber)
open scoped LibsignalBinary.Heap.MuslMemOpsRunsToPlaced
open scoped CryptoVerification.SpqrV1.Kdf.NewFromSlice3Proof
open scoped CryptoVerification.SpqrV1.Kdf.NewFromSlice3GenProof
open LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.DefsSat
  (s2Frame_of_hmacFrame s2Frame_readBytes_eq_of_readable s2Frame_readable_of_readable)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore
  (HookSatExactMemcpy placed_memcpy_step_of_exact)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
  (CallingConventionPreserved.x23 CallingConventionPreserved.x25
   CallingConventionPreserved.x26 HookSatCompress256
   hookOk_withLsRet624_sessionCompress256ROBudget_elim newFromSliceSpecSat newFromSliceStackSat)

attribute [local arm64_norm]
  MemWidth.bytes SimdMemSize.bytes
  Memory.read8_write8_base_off_disjoint
  Memory.read8_write8_base_zero_off
  Memory.read8_write8_base_off_zero
  Memory.read8_write64_base_off_disjoint
  Memory.read8_write64_base_zero_off
  Memory.read8_write64_base_off_zero
  Memory.read8_write64_base_off_inbounds
  Memory.read64_write64_base_off_disjoint
  Memory.read64_write64_base_zero_off
  Memory.read64_write64_base_off_zero

local macro (priority := high) "sess_step" : tactic =>
  `(tactic| (
    refine RunsTo.step (inst := ?inst) ?hrun ?hfetch ?_
    case hfetch => (
      (try simp (config := { decide := true }) only [arm64_norm, *])
      try rfl)
    case hrun => (simp only [arm64_norm, *])
    try dsimp only [execInst, execAddSubImm, execAddSubExt, execAddSubShift, execAddSubCarry, execLogicalImm,
      execLogicalShift, execMoveWide, execBitfield, execCondSelect, execCondCompare,
      execDataProc1, execDataProc2, execDataProc3, execLdr, execLdrLit, execStr, execLdp, execStp,
      evalLogical, evalBitfield, evalAddrMode, AddrMode.baseReg, checkRegSPAligned,
      checkAddrSPAligned, MemWidth.isAligned, State.spAligned, extendVal, Reg.fromZRBits,
      Reg.fromSPBits]
    try simp (config := { decide := true }) only [arm64_norm, *]
    try arm64_discharge_perms_internal))

local macro "prove_trace_eq" : tactic =>
  `(tactic|
    repeat' (first
      | with_reducible exact TraceEq.refl _
      | with_reducible apply TraceEq.writeReg64_step
      | with_reducible apply TraceEq.advancePC_step
      | with_reducible apply TraceEq.setMem_step
      | with_reducible apply TraceEq.setPC_step
      | with_reducible apply TraceEq.setPState_step
      | with_reducible apply TraceEq.writeReg32_step
      | with_reducible apply TraceEq.writeVReg128_step (by decide)))

private theorem readable_of_rw {m : Memory} {a : BitVec 64} {n : Nat} (h : m.RW a n) :
    m.Readable a n := by
  intro x hx
  obtain ⟨hp, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp (h x hx)
  exact ⟨by rw [hp]; rfl, hlf⟩

/-! ## 1. `key.length ≤ 64` Exact `memcpy` Segment & Composition (Block `402`) -/

set_option maxHeartbeats 3200000 in
/-- `HookSatExactMemcpy` sibling of `NewFromSlice3Proof.nfs_seg0_placed`
(`NewFromSliceFirstHalf.lean:917`). -/
public theorem nfs_seg0_placed_exact [LibsignalPlacement] {H : LibsignalHooks}
    (h_mc : HookSatExactMemcpy H lsMemcpySym) {s₀ : State}
    (hpc : s₀.pc = (blkPl_402).base) (hstat : s₀.status = .Running)
    (hlen : (s₀.readReg64 .x2).toNat ≤ 64)
    (hiv : s₀.mem.readBytes spqrSha256IVAddr 32 = shaStateBytes sha256IV)
    (hread_iv : s₀.mem.Readable spqrSha256IVAddr 32)
    (hdisj_iv_stack : DisjointRegions spqrSha256IVAddr 32 (s₀.sp - 544#64) 544)
    (hrw_out : RW s₀.mem (s₀.readReg64 .x0) 0x98) (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544)
    (hdisj_out_stack : DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 544#64) 544)
    (hread_key : s₀.mem.Readable (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat)
    (hdisj_key_stack : (s₀.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 544#64) 544)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64) :
    let key := s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
    RunsTo (lsProg_402 H) s₀ (fun s' =>
      s'.pc = (blkPl_402).base + 476#64 ∧ s'.status = .Running ∧
      NfsRegInv3 nfs3PlacedFakeB s₀ s' ∧ NfsMemInv3 nfs3PlacedFakeB s₀ s'.mem ∧
      s'.readReg64 .x8 = 0x36#64 ∧ s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧
      s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧ s'.readReg64 .x2 = 1#64 ∧
      s'.readVReg128 2#5 = s'.mem.read64 (nfsSp s₀ + 152#64) ++ s'.mem.read64 (nfsSp s₀ + 144#64) ∧
      s'.readVReg128 0#5 = s'.mem.read64 (nfsSp s₀ + 168#64) ++ s'.mem.read64 (nfsSp s₀ + 160#64) ∧
      s'.mem.readBytes (nfsSp s₀ + 144#64) 32 = (keyBlock key).drop 32 ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 (keyBlock key) 0 ∧
      s'.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 (keyBlock key) 16) := by
  intro key; generalize hPost : (fun s' : State => _) = Post
  have hkey_len : key.length ≤ 64 := by dsimp only [key]; rw [Memory.readBytes_length]; exact hlen
  have hkb_len : (keyBlock key).length = 64 := keyBlock_length hkey_len
  have hsp₀ : s₀.sp = nfsSp s₀ + 544#64 := nfs_sp_eq_add s₀
  have hal_nfs : (nfsSp s₀ &&& 0b1111#64) = 0#64 := nfs_sp_align hal
  have hal_464 : ((nfsSp s₀ + 464#64) &&& 0b1111#64) = 0#64 := nfs_sp_add_464_align hal
  have hal_544 : ((nfsSp s₀ + 544#64) &&& 0b1111#64) = 0#64 := nfs_sp_add_544_align hal
  have hRW_stack : s₀.mem.RW (nfsSp s₀) 544 := hrw_stack
  have hcond : BitVec.ule 0x41#64 (s₀.readReg64 .x2) = false := nfs_ule_65_false hlen
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  refine CryptoVerification.SpqrV1.Kdf.NewFromSlice3Proof.RunsTo.pairStep_402_0x28
    (by simp only [arm64_norm, hpc]) (by simp only [arm64_norm, hstat]) ?_
  sess_step; sess_step; sess_step; sess_step; sess_step
  have hA_pro : AgreesOutside s₀.mem (nfsPrologueMem s₀) (nfsSp s₀ + 464#64) 80 := agreesOutside_nfsPrologueMem s₀
  have hA_zero : AgreesOutside (nfsPrologueMem s₀)
      ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8)) (nfsSp s₀ + 112#64) 64 := by
    simpa using ProofLib.agreesOutside_writeBytes (nfsPrologueMem s₀) (nfsSp s₀ + 112#64) (List.replicate 64 0#8)
  have hread_key_mc : ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8)).readBytes
      (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat = key := by
    rcases hdisj_key_stack with h0 | hdisj_key_stack
    · simp only [key, h0, Memory.readBytes]
    have hdisj_key_pro : DisjointRegions (nfsSp s₀ + 464#64) 80 (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := by
      clear * - hdisj_key_stack; simp only [DisjointRegions, nfsSp] at hdisj_key_stack ⊢; bv_omega
    have hdisj_key_112 : DisjointRegions (nfsSp s₀ + 112#64) 64 (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := by
      clear * - hdisj_key_stack; simp only [DisjointRegions, nfsSp] at hdisj_key_stack ⊢; bv_omega
    rw [(agreesOutside_toFrame hA_zero).readBytes_eq (by simp [hdisj_key_112]) (by omega),
        (agreesOutside_toFrame hA_pro).readBytes_eq (by simp [hdisj_key_pro]) (by omega)]
  have hrw_memcpy : ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8)).RW
      (nfsSp s₀ + 112#64) (s₀.readReg64 .x2).toNat := by
    have hrw0 : ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8)).RW (nfsSp s₀) 544 :=
      (Frame.rw_iff (agreesOutside_toFrame hA_zero) _ _).mpr ((Frame.rw_iff (agreesOutside_toFrame hA_pro) _ _).mpr hrw_stack)
    exact hrw0.sub (by clear * - hlen; bv_omega)
  have hreadable_mc : ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8)).Readable
      (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat :=
    (Frame.readable_iff (agreesOutside_toFrame hA_zero) _ _).mpr
      ((Frame.readable_iff (agreesOutside_toFrame hA_pro) _ _).mpr hread_key)
  have hdisj_mc : (s₀.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (nfsSp s₀ + 112#64) (s₀.readReg64 .x2).toNat
        (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := by
    rcases hdisj_key_stack with h0 | hd
    · exact Or.inl h0
    · exact Or.inr (by clear * - hd hlen; simp only [DisjointRegions, nfsSp] at hd ⊢; bv_omega)
  refine placed_memcpy_step_of_exact h_mc
    (hrun := by simp only [arm64_norm, hstat])
    (hsp := by simp (config := { decide := true }) only [State.spAligned, arm64_norm, hal_nfs])
    (hpc := by simp only [arm64_norm, lsMemcpySym])
    (hx0 := by simp only [arm64_norm])
    (hx1 := by simp only [arm64_norm])
    (hx2 := by simp only [arm64_norm])
    (hlr := by simp only [arm64_norm]; rfl)
    (hmem := write64_oct_zero_eq_writeBytes_64 (nfsPrologueMem s₀) (nfsSp s₀))
    (hread := hread_key_mc) (hrw := hrw_memcpy) (hreadable := hreadable_mc) (hdisj := hdisj_mc)
    fun c => ?_
  dsimp only [applyMemcpyClobber]
  rw [writeBytes_key_over_zero64]
  have hA_k0 : AgreesOutside (nfsPrologueMem s₀)
      ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (keyBlock key)) (nfsSp s₀ + 112#64) 64 := by
    have h := ProofLib.agreesOutside_writeBytes (nfsPrologueMem s₀) (nfsSp s₀ + 112#64) (keyBlock key); rwa [hkb_len] at h
  have hRW_k0 : ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (keyBlock key)).RW (nfsSp s₀) 544 :=
    (Frame.rw_iff (agreesOutside_toFrame hA_k0) _ _).mpr ((Frame.rw_iff (agreesOutside_toFrame hA_pro) _ _).mpr hrw_stack)
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  subst hPost; refine RunsTo.refl ?_ (htr := by prove_trace_eq)
  set m_k0 := (nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (keyBlock key)
  have hk0_64 : m_k0.readBytes (nfsSp s₀ + 112#64) 64 = keyBlock key :=
    readBytes_writeBytes_eq (nfsPrologueMem s₀) (nfsSp s₀ + 112#64) (keyBlock key) 64 hkb_len (by decide)
  have hk0_take32 : m_k0.readBytes (nfsSp s₀ + 112#64) 32 = (keyBlock key).take 32 := by
    simpa using readBytes_slice_of_readBytes_eq m_k0 (nfsSp s₀ + 112#64) (keyBlock key) (by rw [hkb_len]; exact hk0_64) 0 32 (by omega)
  have hk0_drop32 : m_k0.readBytes (nfsSp s₀ + 144#64) 32 = (keyBlock key).drop 32 := by
    have h := readBytes_slice_of_readBytes_eq m_k0 (nfsSp s₀ + 112#64) (keyBlock key) (by rw [hkb_len]; exact hk0_64) 32 32 (by omega)
    have hadd : (nfsSp s₀ + 112#64) + BitVec.ofNat 64 32 = nfsSp s₀ + 144#64 := by clear * -; bv_omega
    rw [hadd, List.take_of_length_le (by simp [hkb_len])] at h; exact h
  have hA_432 : AgreesOutside m_k0 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) (nfsSp s₀ + 432#64) 8 :=
    AgreesOutside.write64_self m_k0 (nfsSp s₀ + 432#64) 1#64
  have hf_k0 : Frame s₀.mem (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) [(s₀.readReg64 .x0, 0x98), (nfsSp s₀, 544)] := by
    have hf0 : Frame s₀.mem s₀.mem [(s₀.readReg64 .x0, 0x98), (nfsSp s₀, 544)] := Frame.refl _ _
    have hf1 := Frame.of_agreesOutside_stack hf0 hA_pro (by decide)
    have hf2 := Frame.of_agreesOutside_stack hf1 hA_k0 (by decide)
    exact Frame.of_agreesOutside_stack hf2 hA_432 (by decide)
  have hM_432 : NfsMemInv3 nfs3PlacedFakeB s₀ (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) := {
    rw_stack := (Frame.rw_iff hf_k0 _ _).mpr hrw_stack, rw_out := (Frame.rw_iff hf_k0 _ _).mpr hrw_out
    readable_iv := by rw [nfs3PlacedFakeB_add_iv]; exact (Frame.readable_iff hf_k0 _ _).mpr hread_iv
    iv_bytes := by
      rw [nfs3PlacedFakeB_add_iv]
      have hd432 : DisjointRegions (nfsSp s₀ + 432#64) 8 spqrSha256IVAddr 32 := by
        clear * - hdisj_iv_stack; simp only [DisjointRegions, nfsSp] at hdisj_iv_stack ⊢; bv_omega
      have hdk0 : DisjointRegions (nfsSp s₀ + 112#64) 64 spqrSha256IVAddr 32 := by
        clear * - hdisj_iv_stack; simp only [DisjointRegions, nfsSp] at hdisj_iv_stack ⊢; bv_omega
      have hdpro : DisjointRegions (nfsSp s₀ + 464#64) 80 spqrSha256IVAddr 32 := by
        clear * - hdisj_iv_stack; simp only [DisjointRegions, nfsSp] at hdisj_iv_stack ⊢; bv_omega
      rw [(agreesOutside_toFrame hA_432).readBytes_eq (by simp [hd432]) (by decide),
          (agreesOutside_toFrame hA_k0).readBytes_eq (by simp [hdk0]) (by decide),
          (agreesOutside_toFrame hA_pro).readBytes_eq (by simp [hdpro]) (by decide), hiv]
    disj_iv_stack := by rw [nfs3PlacedFakeB_add_iv]; exact hdisj_iv_stack
    disj_out_stack := hdisj_out_stack, saved := nfsSavedStack_prologue_432 s₀ m_k0 hA_k0, frame := hf_k0 }
  have hM_final : NfsMemInv3 nfs3PlacedFakeB s₀
      (((m_k0.write64 (nfsSp s₀ + 432#64) 1#64).writeBytes (nfsSp s₀ + 288#64) (slice16 (keyBlock key) 0)).writeBytes
        (nfsSp s₀ + 304#64) (slice16 (keyBlock key) 16)) :=
    (hM_432.writeBytes_low 288#64 _ (by simp [slice16_length])).writeBytes_low 304#64 _ (by simp [slice16_length])
  have h144_eq : (((m_k0.write64 (nfsSp s₀ + 432#64) 1#64).writeBytes (nfsSp s₀ + 288#64)
        (slice16 (keyBlock key) 0)).writeBytes (nfsSp s₀ + 304#64) (slice16 (keyBlock key) 16)).readBytes
        (nfsSp s₀ + 144#64) 32 = (keyBlock key).drop 32 := by
    rw [readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _),
        readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _),
        (agreesOutside_toFrame hA_432).readBytes_eq
          (by clear * -; simp only [List.mem_singleton, forall_eq, DisjointRegions]; bv_omega) (by decide), hk0_drop32]
  refine ⟨by simp only [arm64_norm], by simp only [arm64_norm, hstat],
    ⟨by simp only [arm64_norm], hal_nfs, by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm]⟩, ?_,
    by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm], ?_, ?_, ?_⟩
  · dsimp only [State.setMem, State.setPC, State.setPState, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0 (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact hM_final
  · dsimp only [State.setMem, State.setPC, State.setPState, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0 (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact h144_eq
  · dsimp only [State.setMem, State.setPC, State.setPState, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0 (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans (readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _))
  · dsimp only [State.setMem, State.setPC, State.setPState, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0 (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _)

set_option maxHeartbeats 1600000 in
/-- `HookSatExactMemcpy` sibling of `NewFromSlice3Proof.nfs_first_half_placed`
(`NewFromSliceFirstHalf.lean:1167`). -/
public theorem nfs_first_half_placed_exact [LibsignalPlacement] {H : LibsignalHooks}
    (h_mc : HookSatExactMemcpy H lsMemcpySym) {s₀ : State}
    (hpc : s₀.pc = (blkPl_402).base) (hstat : s₀.status = .Running)
    (hlen : (s₀.readReg64 .x2).toNat ≤ 64)
    (hiv : s₀.mem.readBytes spqrSha256IVAddr 32 = shaStateBytes sha256IV)
    (hread_iv : s₀.mem.Readable spqrSha256IVAddr 32)
    (hdisj_iv_stack : DisjointRegions spqrSha256IVAddr 32 (s₀.sp - 544#64) 544)
    (hrw_out : RW s₀.mem (s₀.readReg64 .x0) 0x98) (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544)
    (hdisj_out_stack : DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 544#64) 544)
    (hread_key : s₀.mem.Readable (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat)
    (hdisj_key_stack : (s₀.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 544#64) 544)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64) :
    let key := s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
    RunsTo (lsProg_402 H) s₀ (fun s' =>
      s'.pc = (blkPl_402).base + 1260#64 ∧ s'.status = .Running ∧
      NfsRegInv3 nfs3PlacedFakeB s₀ s' ∧ NfsMemInv3 nfs3PlacedFakeB s₀ s'.mem ∧
      s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧ s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧ s'.readReg64 .x2 = 1#64 ∧
      s'.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes sha256IV ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x36#8) ∧
      s'.mem.readBytes (nfsSp s₀) 32 = (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16) := by
  intro key
  have hkey_len : key.length ≤ 64 := by dsimp only [key]; rw [Memory.readBytes_length]; exact hlen
  refine (nfs_seg0_placed_exact h_mc hpc hstat hlen hiv hread_iv hdisj_iv_stack hrw_out hrw_stack
    hdisj_out_stack hread_key hdisj_key_stack hal).trans fun s1 h1 => ?_
  rcases h1 with ⟨hpc1, hstat1, hR1, hM1, hx8_1, hx0_1, hx1_1, hx2_1, hq2_1, hq0_1, hk0_1, hs0_1, hs16_1⟩
  refine (nfs_chunk1_placed hkey_len hpc1 hstat1 hR1 hM1 hx8_1 hx0_1 hx1_1 hx2_1 hs0_1 hs16_1).trans fun s2 h2 => ?_
  rcases h2 with ⟨hpc2, hstat2, hR2, hM2, hx8_2, hx0_2, hx1_2, hx2_2, hx10_2, hx11_2, hq2_2, hq0_2, hs0_2, hs16_2⟩
  refine (nfs_chunk2_placed hkey_len hal hpc2 hstat2 hR2 hM2 hx8_2 hx0_2 hx1_2 hx2_2 hx10_2 hx11_2
    (hq2_2.trans hq2_1) (hq0_2.trans hq0_1) hk0_1 hs0_2 hs16_2).trans fun s3 h3 => ?_
  rcases h3 with ⟨hpc3, hstat3, hR3, hM3, hx8_3, hx0_3, hx1_3, hx2_3, hx11_3, hx9_3, hs0_3, hs16_3, hs32_3, hs48_3⟩
  refine (nfs_chunk3_placed hkey_len hpc3 hstat3 hR3 hM3 hx8_3 hx0_3 hx1_3 hx2_3 hx11_3 hx9_3
    hs0_3 hs16_3 hs32_3 hs48_3).trans fun s4 h4 => ?_
  rcases h4 with ⟨hpc4, hstat4, hR4, hM4, hx8_4, hx0_4, hx1_4, hx2_4, hx9_4, hx10_4, hs0_4, hs16_4, hs32_4, hs48_4⟩
  exact nfs_chunk4_placed hkey_len hal hpc4 hstat4 hR4 hM4 hx8_4 hx0_4 hx1_4 hx2_4 hx9_4 hx10_4
    hs0_4 hs16_4 hs32_4 hs48_4

/-- Step multi-block `lsCompress256Sym` in `CryptoHmacSha256.RunsToFrom` under `HookSatCompress256` (`176` B stack). -/
public theorem placed_compress256_multi_step_sat [LibsignalPlacement] {prog : Program} {i : Nat}
    {F : ShaCompress} {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    (h_c256 : HookSatCompress256 H lsCompress256Sym F) {s₀ s : State} {P_post : State → Prop}
    {m₀ : Memory} {stPtr blkPtr lr : BitVec 64} {st : ShaState} {bs : List (BitVec 8)} {n : Nat}
    (hrun : s.status = .Running) (hpc : s.pc = lsρ lsCompress256Sym)
    (hx0 : s.readReg64 .x0 = stPtr) (hx1 : s.readReg64 .x1 = blkPtr)
    (hx2 : (s.readReg64 .x2).toNat = n) (hlr : s.readReg64 .lr = lr)
    (hsp_al : (s.sp &&& 15#64) = 0#64) (hmem : s.mem = m₀ := by rfl)
    (hst : m₀.readBytes stPtr 32 = shaStateBytes st) (hbs : m₀.readBytes blkPtr (64 * n) = bs)
    (hrw_st : m₀.RW stPtr 32) (hrw_stk : m₀.RW (s.sp - 176#64) 176)
    (hread_blk : m₀.Readable blkPtr (64 * n))
    (hdisj_st_stk : DisjointRegions stPtr 32 (s.sp - 176#64) 176)
    (hdisj_st_blk : n = 0 ∨ DisjointRegions stPtr 32 blkPtr (64 * n))
    (hdisj_stk_blk : n = 0 ∨ DisjointRegions (s.sp - 176#64) 176 blkPtr (64 * n))
    (h : ∀ s' : State, TraceEq s₀ s' → s'.pc = lr → s'.status = .Running →
      CallingConventionPreserved s s' →
      s'.mem.readBytes stPtr 32 = shaStateBytes ((chunks64 bs).foldl F st) →
      S2Frame m₀ s'.mem [(stPtr, 32), (s.sp - 176#64, 176)] →
      AgreesOn (fun a => (m₀.perm a).r = true ∧ m₀.isLazyFree a = false ∧
        OutsideRegion (s.sp - 176#64) 176 a)
        s'.mem (m₀.writeBytes stPtr (shaStateBytes ((chunks64 bs).foldl F st))) →
      RunsToFrom prog s₀ s' P_post)
    (hn_le : 64 * n ≤ 2 ^ 64 := by omega) (htr_s : TraceEq s₀ s := by prove_trace_eq)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide)
    (hlr_ls : LsRetAddr624 lr := by
      try dsimp only [nfs3CodeFakeB, nfs3PlacedFakeB]
      try simp only [arm64_norm]
      prove_ls_ret624) :
    RunsToFrom prog s₀ s P_post := by
  rcases hmem with rfl
  obtain ⟨f, hfH, hfOk⟩ := h_c256.toHookSat
  have hhook : prog.externAt? s.pc = some f := by
    rw [hpc, ls_externAt?_of_mem (by decide) hi hunmut, hfH]
  obtain ⟨hkf, hsym, hret, hcc, _, _, htr', hread', hs2', hag'⟩ :=
    hookOk_withLsRet624_sessionCompress256ROBudget_elim hfOk (hlr ▸ hlr_ls) hrun hx0 hx1 hx2 hsp_al hst hbs
      hrw_st hrw_stk hread_blk hdisj_st_stk hdisj_st_blk hdisj_stk_blk hn_le
  have htr_s' : TraceEq s₀ (f s) :=
    ⟨htr'.trans htr_s.1, hcc.2.2.2.2.2.2.2.2.2.2.2.2.trans htr_s.2⟩
  exact RunsTo.hook hrun hhook hkf hsym
    (h (f s) htr_s' (hret.1.trans hlr) hret.2.2 hcc hread' hs2' hag')

/-- Step 1-block `lsCompress256Sym` in `CryptoHmacSha256.RunsToFrom` under `HookSatCompress256` (`176` B stack). -/
public theorem placed_compress256_step_sat [LibsignalPlacement] {prog : Program} {i : Nat}
    {F : ShaCompress} {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    (h_c256 : HookSatCompress256 H lsCompress256Sym F) {s₀ s : State} {P_post : State → Prop}
    {m₀ : Memory} {stPtr blkPtr lr : BitVec 64} {st : ShaState} {blk : List (BitVec 8)}
    (hrun : s.status = .Running) (hpc : s.pc = lsρ lsCompress256Sym)
    (hx0 : s.readReg64 .x0 = stPtr) (hx1 : s.readReg64 .x1 = blkPtr)
    (hx2 : s.readReg64 .x2 = 1#64) (hlr : s.readReg64 .lr = lr)
    (hsp_al : (s.sp &&& 15#64) = 0#64) (hmem : s.mem = m₀ := by rfl)
    (hst : m₀.readBytes stPtr 32 = shaStateBytes st) (hblk : m₀.readBytes blkPtr 64 = blk)
    (hlen : blk.length = 64) (hrw_st : m₀.RW stPtr 32) (hrw_stk : m₀.RW (s.sp - 176#64) 176)
    (hread_blk : m₀.Readable blkPtr 64)
    (hdisj_st_stk : DisjointRegions stPtr 32 (s.sp - 176#64) 176)
    (hdisj_st_blk : DisjointRegions stPtr 32 blkPtr 64)
    (hdisj_stk_blk : DisjointRegions (s.sp - 176#64) 176 blkPtr 64)
    (h : ∀ s' : State, TraceEq s₀ s' → s'.pc = lr → s'.status = .Running →
      CallingConventionPreserved s s' → s'.mem.readBytes stPtr 32 = shaStateBytes (F st blk) →
      S2Frame m₀ s'.mem [(stPtr, 32), (s.sp - 176#64, 176)] →
      AgreesOn (fun a => (m₀.perm a).r = true ∧ m₀.isLazyFree a = false ∧
        OutsideRegion (s.sp - 176#64) 176 a)
        s'.mem (m₀.writeBytes stPtr (shaStateBytes (F st blk))) →
      RunsToFrom prog s₀ s' P_post)
    (htr_s : TraceEq s₀ s := by prove_trace_eq)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide)
    (hlr_ls : LsRetAddr624 lr := by
      try dsimp only [nfs3CodeFakeB, nfs3PlacedFakeB]
      try simp only [arm64_norm]
      prove_ls_ret624) :
    RunsToFrom prog s₀ s P_post := by
  have hx2_nat : (s.readReg64 .x2).toNat = 1 := by rw [hx2]; rfl
  refine placed_compress256_multi_step_sat h_c256 hrun hpc hx0 hx1 hx2_nat hlr hsp_al hmem
    hst (by simpa using hblk) hrw_st hrw_stk (by simpa using hread_blk)
    hdisj_st_stk (Or.inr (by simpa using hdisj_st_blk)) (Or.inr (by simpa using hdisj_stk_blk))
    (fun s' htr hpc' hstat' hcc hread' hs2' hag' => ?_) (by decide) htr_s hi hunmut hlr_ls
  rw [chunks64_single_foldl F st blk hlen] at hread' hag'
  exact h s' htr hpc' hstat' hcc hread' hs2' hag'

private theorem disj_stk544_ext176 (sp : BitVec 64) :
    DisjointRegions sp 544 (sp - 176#64) 176 := by unfold DisjointRegions; bv_omega

private theorem s2Frame_hook_read64_stack_eq_176 {sp off k : BitVec 64} {sz : Nat} {m m' : Memory}
    (hf : S2Frame m m' [(sp + off, sz), (sp - 176#64, 176)]) (hrw_stk : m.RW sp 544)
    (hk : k.toNat + 8 ≤ 544)
    (hd_off_k : sz = 0 ∨ (sz ≤ (k - off).toNat ∧ 8 ≤ (off - k).toNat)) :
    m'.read64 (sp + k) = m.read64 (sp + k) := by
  have hrw_k : RW m (sp + k) 8 := hrw_stk.sub (by clear * - hk; bv_omega)
  refine Memory.read64_congr fun b hb => ?_
  obtain ⟨hperm_b, hlf_b⟩ := Memory.permNoLazy_eq_some_rw_iff.mp (hrw_k b hb)
  refine hf.1 b (by rw [hperm_b]; rfl) hlf_b fun r hr_mem => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr_mem
  rcases hr_mem with rfl | rfl
  · rcases hd_off_k with rfl | ⟨h1, h2⟩
    · simp [OutsideRegion]
    · exact (by clear * - h1 h2; unfold DisjointRegions; bv_omega :
        DisjointRegions (sp + off) sz (sp + k) 8).outside hb (by decide)
  · exact ((disj_stk544_ext176 sp).sub_left (sp + k)
      ⟨by decide, by clear * - hk; bv_omega⟩).symm.outside hb (by decide)

private theorem nfsSavedStack_setMem_iff {s₀ : State} {m₁ m : Memory} :
    NfsSavedStack (s₀.setMem m₁) m ↔ NfsSavedStack s₀ m := by
  constructor <;> intro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ <;>
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

private theorem nfsSavedStack_of_s2Frame_low_176 {s₀ : State} {m m' : Memory}
    {off : BitVec 64} {sz : Nat} (hs : NfsSavedStack s₀ m) (hrw_stk : m.RW (nfsSp s₀) 544)
    (hf : S2Frame m m' [(nfsSp s₀ + off, sz), (nfsSp s₀ - 176#64, 176)])
    (hoff : off.toNat + sz ≤ 432) : NfsSavedStack s₀ m' := by
  have hread (k : BitVec 64) (hk : 432 ≤ k.toNat ∧ k.toNat + 8 ≤ 544) :
      m'.read64 (nfsSp s₀ + k) = m.read64 (nfsSp s₀ + k) :=
    s2Frame_hook_read64_stack_eq_176 hf hrw_stk hk.2 (by
      by_cases hsz : sz = 0
      · exact Or.inl hsz
      · rcases hk with ⟨h1, h2⟩; refine Or.inr ?_; clear * - hsz hoff h1 h2; constructor <;> bv_omega)
  exact {
    m432 := (hread 432#64 (by decide)).trans hs.m432, m464 := (hread 464#64 (by decide)).trans hs.m464,
    m472 := (hread 472#64 (by decide)).trans hs.m472, m480 := (hread 480#64 (by decide)).trans hs.m480,
    m496 := (hread 496#64 (by decide)).trans hs.m496, m504 := (hread 504#64 (by decide)).trans hs.m504,
    m512 := (hread 512#64 (by decide)).trans hs.m512, m520 := (hread 520#64 (by decide)).trans hs.m520,
    m528 := (hread 528#64 (by decide)).trans hs.m528, m536 := (hread 536#64 (by decide)).trans hs.m536 }

private theorem nfsRegInv3_setMem_iff {b : BitVec 64} {s₀ s : State} {m₁ : Memory} :
    NfsRegInv3 b (s₀.setMem m₁) s ↔ NfsRegInv3 b s₀ s := by
  constructor <;> intro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ <;>
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

private theorem nfsRegInv3_of_cc {b : BitVec 64} {s₀ s s' : State}
    (hR : NfsRegInv3 b s₀ s) (hcc : CallingConventionPreserved s s') : NfsRegInv3 b s₀ s' :=
  ⟨hcc.1.trans hR.sp_eq, hR.sp_align, (CallingConventionPreserved.x29 hcc).trans hR.x29_eq,
   (CallingConventionPreserved.x19 hcc).trans hR.x19_eq, (CallingConventionPreserved.x20 hcc).trans hR.x20_eq,
   (CallingConventionPreserved.x22 hcc).trans hR.x22_eq, (CallingConventionPreserved.x25 hcc).trans hR.x25_eq,
   (CallingConventionPreserved.x26 hcc).trans hR.x26_eq, (CallingConventionPreserved.x27 hcc).trans hR.x27_eq⟩

private theorem nfsMemInv3_of_s2Frame_low_176 [LibsignalPlacement] {s₀ : State} {m m' : Memory}
    {off : BitVec 64} {sz : Nat} (hM : NfsMemInv3 nfs3PlacedFakeB s₀ m)
    (hd_iv_stk720 : DisjointRegions spqrSha256IVAddr 32 (s₀.sp - 720#64) 720)
    (hf : S2Frame m m' [(nfsSp s₀ + off, sz), (nfsSp s₀ - 176#64, 176)])
    (hoff : 0 < sz ∧ off.toNat + sz ≤ 432) : NfsMemInv3 nfs3PlacedFakeB (s₀.setMem m') m' := by
  have hdisj_iv : DisjointRegions (nfsSp s₀ + off) sz spqrSha256IVAddr 32 := by
    have hd_iv_stk : DisjointRegions spqrSha256IVAddr 32 (nfsSp s₀) 544 := by
      rw [← nfs3PlacedFakeB_add_iv]; exact hM.disj_iv_stack
    refine hd_iv_stk.symm.sub_left (nfsSp s₀ + off) ⟨hoff.1, ?_⟩
    have := hoff.2; clear * - this; bv_omega
  have hd_iv_176 : DisjointRegions (nfsSp s₀ - 176#64) 176 spqrSha256IVAddr 32 := by
    clear * - hd_iv_stk720; unfold DisjointRegions at hd_iv_stk720 ⊢; unfold nfsSp; bv_omega
  exact {
    rw_stack := hf.rw_of_rw _ _ hM.rw_stack, rw_out := hf.rw_of_rw _ _ hM.rw_out,
    readable_iv := s2Frame_readable_of_readable hf hM.readable_iv,
    iv_bytes := by
      rw [nfs3PlacedFakeB_add_iv]
      exact (s2Frame_readBytes_eq_of_readable hf
        (by rw [← nfs3PlacedFakeB_add_iv]; exact hM.readable_iv) (by decide) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl; exacts [hdisj_iv, hd_iv_176])).trans
        (by rw [← nfs3PlacedFakeB_add_iv]; exact hM.iv_bytes),
    disj_iv_stack := hM.disj_iv_stack, disj_out_stack := hM.disj_out_stack,
    saved := nfsSavedStack_setMem_iff.mpr (nfsSavedStack_of_s2Frame_low_176 hM.saved hM.rw_stack hf hoff.2),
    frame := Frame.refl m' _ }

private theorem s2Frame_widen_544_to_720 {out sp : BitVec 64} {m₁ m₂ : Memory}
    (hf : Frame m₁ m₂ [(out, 0x98), (sp - 544#64, 544)]) :
    S2Frame m₁ m₂ [(out, 0x98), (sp - 720#64, 720)] := by
  refine (s2Frame_of_hmacFrame hf).mono fun a ha r hr => ?_
  have hout := ha (out, 0x98) (by simp); have hstk := ha (sp - 720#64, 720) (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hout
  · clear * - hstk; simp only [OutsideRegion] at hstk ⊢; bv_omega

private theorem s2Frame_widen_hook_to_720 {out sp off : BitVec 64} {sz : Nat} {m₁ m₂ : Memory}
    (hf : S2Frame m₁ m₂ [((sp - 544#64) + off, sz), ((sp - 544#64) - 176#64, 176)])
    (hoff : off.toNat + sz ≤ 544) : S2Frame m₁ m₂ [(out, 0x98), (sp - 720#64, 720)] := by
  refine hf.mono fun a ha r hr => ?_
  have hstk := ha (sp - 720#64, 720) (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · clear * - hstk hoff; simp only [OutsideRegion] at hstk ⊢; bv_omega
  · clear * - hstk; simp only [OutsideRegion] at hstk ⊢; bv_omega

set_option maxHeartbeats 1600000 in
/-- `HookSatCompress256` (`720` B stack) sibling of `NewFromSlice3Proof.nfs_second_half_placed`
(`NewFromSlice.lean:952`). -/
public theorem nfs_second_half_placed_exact [LibsignalPlacement] {F : ShaCompress}
    {H : LibsignalHooks} (h_c256 : HookSatCompress256 H lsCompress256Sym F)
    {s₀ s : State} {key : List (BitVec 8)} (hlen : key.length ≤ 64)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64)
    (hd_iv_stk720 : DisjointRegions spqrSha256IVAddr 32 (s₀.sp - 720#64) 720)
    (hrw_stk720 : RW s₀.mem (s₀.sp - 720#64) 720)
    (hpc : s.pc = (blkPl_402).base + 1260#64) (hstat : s.status = .Running)
    (hR : NfsRegInv3 nfs3PlacedFakeB s₀ s) (hM : NfsMemInv3 nfs3PlacedFakeB s₀ s.mem)
    (hx0 : s.readReg64 .x0 = nfsSp s₀ + 400#64) (hx1 : s.readReg64 .x1 = nfsSp s₀ + 288#64)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hist : s.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes sha256IV)
    (hblk : s.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x36#8))
    (hivsw : s.mem.readBytes (nfsSp s₀) 32 =
      (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16) :
    RunsTo (lsProg_402 H) s (fun s' =>
      s'.pc = s₀.readReg64 .lr ∧ s'.status = .Running ∧ CalleeSaved s₀ s' ∧
      s'.mem.read64 (s₀.readReg64 .x0) = 0#64 ∧ HmacSt s'.mem (s₀.readReg64 .x0 + 8#64) F key [] ∧
      S2Frame s₀.mem s'.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 720#64, 720)]) := by
  have hipad_len : ((keyBlock key).map (· ^^^ 0x36#8)).length = 64 := by simp [keyBlock_length hlen]
  have hopad_len : ((keyBlock key).map (· ^^^ 0x5c#8)).length = 64 := by simp [keyBlock_length hlen]
  have hiv_len : (shaStateBytes sha256IV).length = 32 := shaStateBytes_length sha256IV
  have hrw_s_720 : s.mem.RW (s₀.sp - 720#64) 720 := (hM.frame.rw_iff _ _).mpr hrw_stk720
  have hrw_s_176 : s.mem.RW (nfsSp s₀ - 176#64) 176 :=
    hrw_s_720.sub (by clear * -; simp only [nfsSp]; bv_omega)
  -- Step 1: `bl compress256` #1 (`+1260 -> +1264`)
  have hstep_c1 : RunsTo (lsProg_402 H) s (fun s1 =>
      S2Frame s.mem s1.mem [(nfsSp s₀ + 400#64, 32), (nfsSp s₀ - 176#64, 176)] ∧
      Nfs3OpadPostHookPlaced F (s₀.setMem s1.mem) key s1) := by
    obtain ⟨hsp, hsp_align, hx29, hx19, hx20, hx22, hx25, hx26, hx27⟩ := hR
    sess_step
    have hrw_ist : s.mem.RW (nfsSp s₀ + 400#64) 32 := hM.rw_stack.sub (by clear * -; bv_omega)
    have hread_blk1 : s.mem.Readable (nfsSp s₀ + 288#64) 64 :=
      readable_of_rw (hM.rw_stack.sub (by clear * -; bv_omega))
    refine placed_compress256_step_sat h_c256 (m₀ := s.mem)
      (hrun := by simp only [arm64_norm, hstat]) (hpc := rfl)
      (hx0 := by simp only [arm64_norm, hx0]) (hx1 := by simp only [arm64_norm, hx1])
      (hx2 := by simp only [arm64_norm, hx2]) (hlr := by simp only [arm64_norm]; rfl)
      (hsp_al := by simp only [arm64_norm, hsp]; exact hsp_align)
      (hmem := rfl) (hst := hist) (hblk := hblk) (hlen := hipad_len)
      (hrw_st := hrw_ist)
      (hrw_stk := by simp only [arm64_norm, hsp]; exact hrw_s_176)
      (hread_blk := hread_blk1)
      (hdisj_st_stk := by simp only [arm64_norm, hsp]; clear * -; unfold DisjointRegions; bv_omega)
      (hdisj_st_blk := by clear * -; unfold DisjointRegions; bv_omega)
      (hdisj_stk_blk := by simp only [arm64_norm, hsp]; clear * -; unfold DisjointRegions; bv_omega)
      fun s1 htr1 hpc1 hstat1 hcc1 hist1 hs2_1 _ => ?_
    simp only [arm64_norm, hsp] at hs2_1
    have hR_pre : NfsRegInv3 nfs3PlacedFakeB s₀
        ((s.writeReg64 .lr ((blkPl_402).base + 1264#64)).setPC (lsρ lsCompress256Sym)) :=
      ⟨by simp only [arm64_norm, hsp], hsp_align, by simp only [arm64_norm, hx29],
       by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
       by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx25],
       by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27]⟩
    have hR1 : NfsRegInv3 nfs3PlacedFakeB (s₀.setMem s1.mem) s1 :=
      nfsRegInv3_setMem_iff.mpr (nfsRegInv3_of_cc hR_pre hcc1)
    have hM1 : NfsMemInv3 nfs3PlacedFakeB (s₀.setMem s1.mem) s1.mem :=
      nfsMemInv3_of_s2Frame_low_176 hM hd_iv_stk720 hs2_1 (by decide)
    have hblk1 : s1.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x36#8) :=
      (s2Frame_readBytes_eq_of_readable hs2_1 hread_blk1 (by decide) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> (clear * -; unfold DisjointRegions; bv_omega)).trans hblk
    have hivsw1 : s1.mem.readBytes (nfsSp s₀) 32 =
        (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16 :=
      (s2Frame_readBytes_eq_of_readable hs2_1
        (readable_of_rw (hM.rw_stack.sub (by clear * -; bv_omega))) (by decide) fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> (clear * -; unfold DisjointRegions; bv_omega)).trans hivsw
    exact RunsTo.refl ⟨hs2_1,
      { pc_eq := hpc1, status := hstat1, regInv := hR1, memInv := hM1,
        ist_eq := hist1, blk_eq := hblk1, ivsw_eq := hivsw1 }⟩ htr1
  refine hstep_c1.trans fun s1 ⟨hs2_1, h1⟩ => ?_
  -- Step 2: `opad` SIMD chunks (`+1264 -> +2060`)
  let s₀1 := s₀.setMem s1.mem
  refine (nfs_opad_chunk0_placed h1).trans fun s2 h2 => ?_
  have hrw1 : (xorChunk s1.mem (nfsSp s₀1 + 288#64)).RW (nfsSp s₀1) 544 :=
    rw_xorChunk _ h1.memInv.rw_stack
  refine (nfs_opad_chunk1_placed hrw1 h2).trans fun s3 h3 => ?_
  have hrw2 : (xorChunk s2.mem (nfsSp s₀1 + 304#64)).RW (nfsSp s₀1) 544 :=
    rw_xorChunk _ (h2.mem_eq ▸ hrw1)
  refine (nfs_opad_chunk2_placed hrw2 h3).trans fun s4 h4 => ?_
  have hrw3 : (xorChunk s3.mem (nfsSp s₀1 + 320#64)).RW (nfsSp s₀1) 544 :=
    rw_xorChunk _ (h3.mem_eq ▸ hrw2)
  have hopad_pre : RunsTo (lsProg_402 H) s4 (Nfs3PreCompress2Placed F s₀1 key) := by
    refine (nfs_opad_chunk3_placed hrw3 h4).mono fun s5 h5 => ?_
    have hm4 : xorChunk s4.mem (nfsSp s₀1 + 336#64) =
        s1.mem.writeBytes (nfsSp s₀1 + 288#64) ((keyBlock key).map (· ^^^ 0x5c#8)) := by
      rw [h4.mem_eq, h3.mem_eq, h2.mem_eq,
        (by clear * -; bv_omega : nfsSp s₀1 + 304#64 = (nfsSp s₀1 + 288#64) + 16#64),
        (by clear * -; bv_omega : nfsSp s₀1 + 320#64 = (nfsSp s₀1 + 288#64) + 32#64),
        (by clear * -; bv_omega : nfsSp s₀1 + 336#64 = (nfsSp s₀1 + 288#64) + 48#64),
        xorChunk4_eq_writeBytes, h1.blk_eq, map_xor_0x36_0x6a]
    have hmem5 : s5.mem =
        (((s1.mem.writeBytes (nfsSp s₀1 + 288#64) ((keyBlock key).map (· ^^^ 0x5c#8))).writeBytes
          (nfsSp s₀1 + 176#64) (shaStateBytes sha256IV)).write64 (nfsSp s₀1 + 208#64) 1#64) := by
      rw [h5.mem_eq, hm4, write128_pair_ivsw _ s1.mem (nfsSp s₀1) h1.ivsw_eq]
    have hM5 : NfsMemInv3 nfs3PlacedFakeB s₀1 s5.mem := by
      rw [hmem5]
      exact ((h1.memInv.writeBytes_low 288#64 _ (by rw [hopad_len]; decide)).writeBytes_low
        176#64 _ (by rw [hiv_len]; decide)).write64_low 208#64 1#64 (by decide)
    have hA_opad := ProofLib.agreesOutside_writeBytes s1.mem (nfsSp s₀1 + 288#64) ((keyBlock key).map (· ^^^ 0x5c#8))
    have hA_iv := ProofLib.agreesOutside_writeBytes (s1.mem.writeBytes (nfsSp s₀1 + 288#64) ((keyBlock key).map (· ^^^ 0x5c#8)))
      (nfsSp s₀1 + 176#64) (shaStateBytes sha256IV)
    have hA_208 := AgreesOutside.write64_self
      ((s1.mem.writeBytes (nfsSp s₀1 + 288#64) ((keyBlock key).map (· ^^^ 0x5c#8))).writeBytes
        (nfsSp s₀1 + 176#64) (shaStateBytes sha256IV)) (nfsSp s₀1 + 208#64) 1#64
    exact {
      pc_eq := h5.pc_eq, status := h5.status, regInv := h5.regInv, memInv := hM5,
      x0_eq := h5.x0_eq, x1_eq := h5.x1_eq, x2_eq := h5.x2_eq,
      ist_eq := by
        rw [hmem5, (agreesOutside_toFrame hA_208).readBytes_eq
              (by clear * -; simp only [List.mem_singleton, forall_eq, DisjointRegions]; bv_omega) (by decide),
            (agreesOutside_toFrame hA_iv).readBytes_eq
              (by rw [hiv_len]; clear * -; simp only [List.mem_singleton, forall_eq, DisjointRegions]; bv_omega) (by decide),
            (agreesOutside_toFrame hA_opad).readBytes_eq
              (by rw [hopad_len]; clear * -; simp only [List.mem_singleton, forall_eq, DisjointRegions]; bv_omega) (by decide),
            h1.ist_eq]
      blk_eq := by
        rw [hmem5, (agreesOutside_toFrame hA_208).readBytes_eq
              (by clear * -; simp only [List.mem_singleton, forall_eq, DisjointRegions]; bv_omega) (by decide),
            (agreesOutside_toFrame hA_iv).readBytes_eq
              (by rw [hiv_len]; clear * -; simp only [List.mem_singleton, forall_eq, DisjointRegions]; bv_omega) (by decide)]
        exact readBytes_writeBytes_eq s1.mem (nfsSp s₀1 + 288#64) _ 64 hopad_len (by decide)
      ost_eq := by
        rw [hmem5, (agreesOutside_toFrame hA_208).readBytes_eq
              (by clear * -; simp only [List.mem_singleton, forall_eq, DisjointRegions]; bv_omega) (by decide)]
        exact readBytes_writeBytes_eq _ (nfsSp s₀1 + 176#64) _ 32 hiv_len (by decide)
      obl_eq := by rw [hmem5, Memory.read64_write64_same] }
  refine hopad_pre.trans fun s5 hs5 => ?_
  -- Step 3: `bl compress256` #2 (`+2060 -> +2064`) + epilogue
  have hrw_s1_720 : s1.mem.RW (s₀.sp - 720#64) 720 := hs2_1.rw_of_rw _ _ hrw_s_720
  have hrw_s5_720 : s5.mem.RW (s₀.sp - 720#64) 720 :=
    (hs5.memInv.frame.rw_iff _ _).mpr hrw_s1_720
  have hrw_s5_176 : s5.mem.RW (nfsSp s₀1 - 176#64) 176 := by
    change s5.mem.RW ((s₀.sp - 544#64) - 176#64) 176
    exact hrw_s5_720.sub (by clear * -; bv_omega)
  have hstep_c2 : RunsTo (lsProg_402 H) s5 (fun s6 =>
      S2Frame s5.mem s6.mem [(nfsSp s₀ + 176#64, 32), (nfsSp s₀ - 176#64, 176)] ∧
      Nfs3PostCompress2Placed F (s₀.setMem s6.mem) key s6) := by
    have hpc5 := hs5.pc_eq; have hstat5 := hs5.status
    obtain ⟨hsp5, hsp_align5, hx29_5, hx19_5, hx20_5, hx22_5, hx25_5, hx26_5, hx27_5⟩ := hs5.regInv
    have hM5 := hs5.memInv
    sess_step
    have hrw_ost : s5.mem.RW (nfsSp s₀1 + 176#64) 32 := hM5.rw_stack.sub (by clear * -; bv_omega)
    have hread_blk2 : s5.mem.Readable (nfsSp s₀1 + 288#64) 64 :=
      readable_of_rw (hM5.rw_stack.sub (by clear * -; bv_omega))
    refine placed_compress256_step_sat h_c256 (m₀ := s5.mem)
      (hrun := by simp only [arm64_norm, hstat5]) (hpc := rfl)
      (hx0 := by simp only [arm64_norm, hs5.x0_eq]) (hx1 := by simp only [arm64_norm, hs5.x1_eq])
      (hx2 := by simp only [arm64_norm, hs5.x2_eq]) (hlr := by simp only [arm64_norm]; rfl)
      (hsp_al := by simp only [arm64_norm, hsp5]; exact hsp_align5)
      (hmem := rfl) (hst := hs5.ost_eq) (hblk := hs5.blk_eq) (hlen := hopad_len)
      (hrw_st := hrw_ost)
      (hrw_stk := by simp only [arm64_norm, hsp5]; exact hrw_s5_176)
      (hread_blk := hread_blk2)
      (hdisj_st_stk := by simp only [arm64_norm, hsp5]; clear * -; unfold DisjointRegions; bv_omega)
      (hdisj_st_blk := by clear * -; unfold DisjointRegions; bv_omega)
      (hdisj_stk_blk := by simp only [arm64_norm, hsp5]; clear * -; unfold DisjointRegions; bv_omega)
      fun s6 htr6 hpc6 hstat6 hcc6 host6 hs2_6 _ => ?_
    simp only [arm64_norm, hsp5] at hs2_6
    have hR_pre5 : NfsRegInv3 nfs3PlacedFakeB s₀1
        ((s5.writeReg64 .lr ((blkPl_402).base + 2064#64)).setPC (lsρ lsCompress256Sym)) :=
      ⟨by simp only [arm64_norm, hsp5], hsp_align5, by simp only [arm64_norm, hx29_5],
       by simp only [arm64_norm, hx19_5], by simp only [arm64_norm, hx20_5],
       by simp only [arm64_norm, hx22_5], by simp only [arm64_norm, hx25_5],
       by simp only [arm64_norm, hx26_5], by simp only [arm64_norm, hx27_5]⟩
    have hR6 : NfsRegInv3 nfs3PlacedFakeB (s₀.setMem s6.mem) s6 :=
      nfsRegInv3_setMem_iff.mpr (nfsRegInv3_setMem_iff.mp (nfsRegInv3_of_cc hR_pre5 hcc6))
    have hM6 : NfsMemInv3 nfs3PlacedFakeB (s₀.setMem s6.mem) s6.mem :=
      nfsMemInv3_of_s2Frame_low_176 (s₀ := s₀1) hM5 hd_iv_stk720 hs2_6 (by decide)
    have hist6 : s6.mem.readBytes (nfsSp s₀1 + 400#64) 32 = shaStateBytes (innerState F key) :=
      (s2Frame_readBytes_eq_of_readable hs2_6
        (readable_of_rw (hM5.rw_stack.sub (by clear * -; bv_omega))) (by decide) fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> (clear * -; unfold DisjointRegions; bv_omega)).trans hs5.ist_eq
    have hobl6 : s6.mem.read64 (nfsSp s₀1 + 208#64) = 1#64 :=
      (s2Frame_hook_read64_stack_eq_176 hs2_6 hM5.rw_stack (by decide)
        (Or.inr ⟨by decide, by decide⟩)).trans hs5.obl_eq
    exact RunsTo.refl ⟨hs2_6,
      { pc_eq := hpc6, status := hstat6, regInv := hR6, memInv := hM6,
        ist_eq := hist6, ost_eq := host6, obl_eq := hobl6 }⟩ htr6
  refine hstep_c2.trans fun s6 ⟨hs2_6, hs6⟩ => ?_
  refine (nfs_epilogue_placed (s₀ := s₀.setMem s6.mem) hal hs6).mono
    fun s' ⟨hpc', hstat', hcs', hm0', hhm', hfr'⟩ => ?_
  exact ⟨hpc', hstat', hcs', hm0', hhm',
    ((((s2Frame_widen_544_to_720 hM.frame).trans (s2Frame_widen_hook_to_720 hs2_1 (by decide))).trans
      (s2Frame_widen_544_to_720 hs5.memInv.frame)).trans (s2Frame_widen_hook_to_720 hs2_6 (by decide))).trans
      (s2Frame_widen_544_to_720 hfr')⟩

set_option maxHeartbeats 1600000 in
/-- `HookSatExactMemcpy` + `HookSatCompress256` (`720` B stack) sibling of `new_from_slice3_placed_run`. -/
public theorem new_from_slice3_placed_run_exact [LibsignalPlacement] {F : ShaCompress}
    {H : LibsignalHooks} (h_mc : HookSatExactMemcpy H lsMemcpySym)
    (h_c256 : HookSatCompress256 H lsCompress256Sym F) {s₀ : State}
    (hpc : s₀.pc = (blkPl_402).base) (hstat : s₀.status = .Running)
    (hlen : (s₀.readReg64 .x2).toNat ≤ 64)
    (hiv : s₀.mem.readBytes spqrSha256IVAddr 32 = shaStateBytes sha256IV)
    (hread_iv : s₀.mem.Readable spqrSha256IVAddr 32)
    (hdisj_iv_stack : DisjointRegions spqrSha256IVAddr 32 (s₀.sp - 720#64) 720)
    (hrw_out : RW s₀.mem (s₀.readReg64 .x0) 0x98) (hrw_stack : RW s₀.mem (s₀.sp - 720#64) 720)
    (hdisj_out_stack : DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 720#64) 720)
    (hread_key : s₀.mem.Readable (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat)
    (hdisj_key_stack : (s₀.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 720#64) 720)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64) :
    let key := s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
    RunsTo (lsProg_402 H) s₀ (fun s' =>
      s'.pc = s₀.readReg64 .lr ∧ s'.status = .Running ∧ CalleeSaved s₀ s' ∧
      s'.mem.read64 (s₀.readReg64 .x0) = 0#64 ∧ HmacSt s'.mem (s₀.readReg64 .x0 + 8#64) F key [] ∧
      S2Frame s₀.mem s'.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 720#64, 720)]) := by
  have hkey_len : (s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat).length ≤ 64 := by
    rw [Memory.readBytes_length]; exact hlen
  have hdisj_key_544 : (s₀.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 544#64) 544 :=
    hdisj_key_stack.imp id (fun hd => by clear * - hd hlen; unfold DisjointRegions at hd ⊢; bv_omega)
  refine (nfs_first_half_placed_exact h_mc hpc hstat hlen hiv hread_iv
    (by clear * - hdisj_iv_stack; unfold DisjointRegions at hdisj_iv_stack ⊢; bv_omega)
    hrw_out (hrw_stack.sub (by clear * -; bv_omega))
    (by clear * - hdisj_out_stack; unfold DisjointRegions at hdisj_out_stack ⊢; bv_omega)
    hread_key hdisj_key_544 hal).trans fun s1 h1 => ?_
  rcases h1 with ⟨hpc1, hstat1, hR1, hM1, hx0_1, hx1_1, hx2_1, hist1, hblk1, hivsw1⟩
  exact nfs_second_half_placed_exact h_c256 hkey_len hal hdisj_iv_stack hrw_stack
    hpc1 hstat1 hR1 hM1 hx0_1 hx1_1 hx2_1 hist1 hblk1 hivsw1

/-- `HookSatExactMemcpy` + `HookSatCompress256` (`720` B stack) sibling of `new_from_slice3_placed_ro_ok`. -/
public theorem new_from_slice3_placed_ro_ok_exact [LibsignalPlacement] (F : ShaCompress)
    {H : LibsignalHooks} (h_mc : HookSatExactMemcpy H lsMemcpySym)
    (h_c256 : HookSatCompress256 H lsCompress256Sym F) :
    subroutine_ok (lsProg_402 H) (blkPl_402).base
      { newFromSliceSpecSat F with
        pre := fun x s0 => (newFromSliceSpecSat F).pre x s0 ∗ ⌜LibsignalRoLoaded lsmpl s0.mem⌝ } := by
  refine subroutine_ok_intro fun ⟨ret, keyA, key⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [newFromSliceSpecSat] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hro, ⟨hx0, hx1, hx2_nat, hkey_len⟩, hsep⟩
  have hb_out := IsBlock.memRegion ret 0x98
  have hb_key := IsBlock.pointsToBytes (a := keyA) key
  have hb_stk := IsBlock.memRegion (s0.sp - 720#64) 720
  have hsep_out : s0.mem ⊨ memRegion ret 0x98 ∗ (memRegion (s0.sp - 720#64) 720 ∗ ((keyA ↦ₛ key) ∗ R)) := by
    simp only [newFromSliceStackSat, stackAt] at hsep; ac_nf at hsep ⊢
  have hsep_key : s0.mem ⊨ (keyA ↦ₛ key) ∗ (memRegion (s0.sp - 720#64) 720 ∗ (memRegion ret 0x98 ∗ R)) := by
    simp only [newFromSliceStackSat, stackAt] at hsep; ac_nf at hsep ⊢
  have hsep_stk : s0.mem ⊨ memRegion (s0.sp - 720#64) 720 ∗ (memRegion ret 0x98 ∗ (keyA ↦ₛ key) ∗ R) := by
    simp only [newFromSliceStackSat, stackAt] at hsep; ac_nf at hsep ⊢
  have hkey_eq : s0.mem.readBytes keyA key.length = key := (hb_key.read hsep_key).2
  have hrw_out : s0.mem.RW ret 0x98 := fun a ha => hb_out.permNoLazy_rw hsep_out ha
  have hrw_key : s0.mem.RW keyA key.length := fun a ha => hb_key.permNoLazy_rw hsep_key ha
  have hrw_stk : s0.mem.RW (s0.sp - 720#64) 720 := fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
  obtain ⟨hro_iv, hiv_eq⟩ := rodata_placed_spqrSha256IV hro
  have hdisj_key : key.length = 0 ∨ DisjointRegions keyA key.length (s0.sp - 720#64) 720 := by
    rcases key with _ | ⟨k0, ks⟩
    · exact Or.inl rfl
    · exact Or.inr (hb_key.disjoint hb_stk (by simp) (by decide) hsep_key)
  have hrunsTo := new_from_slice3_placed_run_exact (F := F) h_mc h_c256
    hpc hrun (by rw [hx2_nat]; exact hkey_len) hiv_eq
    (fun a ha => ⟨by rw [(hro_iv a ha).1]; rfl, (hro_iv a ha).2⟩)
    (disjointRegions_of_ro_rw (by decide) (by decide) hro_iv hrw_stk)
    (by rw [hx0]; exact hrw_out) hrw_stk
    (by rw [hx0]; exact hb_out.disjoint hb_stk (by decide) (by decide) hsep_out)
    (by rw [hx1, hx2_nat]; exact readable_of_rw hrw_key) (by rw [hx1, hx2_nat]; exact hdisj_key)
    (by simpa [State.spAligned] using hsp)
  rw [hx1, hx2_nat, hkey_eq] at hrunsTo
  refine hrunsTo.to_reaches_pc fun sf ⟨hpc_sf, hstat_sf, hcallee, hret_sf, hst_sf, hframe_sf⟩ _ _ htr hvregs => ?_
  refine ⟨hpc_sf, hstat_sf, ?_, CallingConventionPreserved_of_calleeSaved hcallee hvregs⟩
  dsimp only [newFromSliceSpecSat]; rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨htr, ?_⟩
  rw [hx0] at hret_sf hst_sf hframe_sf
  have hpost := S2Frame.update_two_blocks hb_out (isBlock_nfsResult F ret key) hb_stk hb_stk
    hsep_out hframe_sf ⟨hret_sf, hst_sf⟩ trivial
  simp only [newFromSliceStackSat, stackAt]; ac_nf at hpost ⊢

/-- `withLsCodeLoaded` corollary of `new_from_slice3_placed_ro_ok_exact`. -/
public theorem new_from_slice3_placed_ok_withLsCodeLoaded_ro_exact [LibsignalPlacement] (F : ShaCompress)
    {H : LibsignalHooks} (h_mc : HookSatExactMemcpy H lsMemcpySym)
    (h_c256 : HookSatCompress256 H lsCompress256Sym F) :
    subroutine_ok (lsProg_402 H) (blkPl_402).base
      (withLsCodeLoaded lsmpl
        { newFromSliceSpecSat F with
          pre := fun x s0 => (newFromSliceSpecSat F).pre x s0 ∗ ⌜LibsignalRoLoaded lsmpl s0.mem⌝ }) :=
  subroutine_ok_withLsCodeLoaded_of_plain (new_from_slice3_placed_ro_ok_exact F h_mc h_c256)

/-! ## 2. `key.length > 64` Exact `memcpy` + `HookSatCompress256` Segment (`nfs_seg0a_gt64_placed_exact`, Block `402`) -/

private structure FixedWriteAt (sp : BitVec 64) (x : BitVec 64) (g : Memory → Memory) : Prop where
  idem : (∀ m, (g m).read8 x = m.read8 x) ∨ (∃ b, ∀ m, (g m).read8 x = b)
  perm_eq : ∀ m, (g m).perm = m.perm
  lf_out : OutsideRegion sp 544 x → ∀ m, (g m).isLazyFree x = m.isLazyFree x
  lf_false : ∀ m, m.isLazyFree x = false → (g m).isLazyFree x = false
  anon_eq : ∀ m, (g m).isAnon x = m.isAnon x

private theorem fixedWriteAt_id (sp x : BitVec 64) : FixedWriteAt sp x id :=
  ⟨Or.inl (fun _ => rfl), fun _ => rfl, fun _ _ => rfl, fun _ h => h, fun _ => rfl⟩

private theorem fixedWriteAt_write8 {sp x a : BitVec 64} {v : BitVec 8} {g : Memory → Memory}
    (hg : FixedWriteAt sp x g) (hin_a : InRegion sp 544 a) :
    FixedWriteAt sp x (fun m => (g m).write8 a v) := by
  have h_idem : (∀ m, ((g m).write8 a v).read8 x = m.read8 x) ∨ (∃ b, ∀ m, ((g m).write8 a v).read8 x = b) := by
    by_cases hxa : x = a
    · subst hxa; exact Or.inr ⟨v, fun m => by simp⟩
    · rcases hg.idem with hid | ⟨b, hb⟩
      · exact Or.inl fun m => (Memory.read8_write8_ne hxa).trans (hid m)
      · exact Or.inr ⟨b, fun m => (Memory.read8_write8_ne hxa).trans (hb m)⟩
  refine ⟨h_idem, fun m => (Memory.perm_write8 (g m) a v).trans (hg.perm_eq m), fun hout m => ?_,
    fun m h => Memory.isLazyFree_write8_of_false a v (hg.lf_false m h),
    fun m => by rw [Memory.isAnon_write8_apply]; exact hg.anon_eq m⟩
  have hne : x ≠ a := by intro h; subst h; dsimp only [InRegion, OutsideRegion] at hin_a hout; omega
  exact (Memory.isLazyFree_write8_ne hne).trans (hg.lf_out hout m)

private theorem fixedWriteAt_write64 {sp x a : BitVec 64} {w : BitVec 64} {g : Memory → Memory}
    (hg : FixedWriteAt sp x g) (hoff : (a - sp).toNat + 8 ≤ 544) :
    FixedWriteAt sp x (fun m => (g m).write64 a w) := by
  unfold Memory.write64
  have hin (k : BitVec 64) (hk : k.toNat < 8) : InRegion sp 544 (a + k) := by
    clear * - hoff hk; dsimp only [InRegion]; bv_omega
  exact fixedWriteAt_write8 (fixedWriteAt_write8 (fixedWriteAt_write8 (fixedWriteAt_write8
    (fixedWriteAt_write8 (fixedWriteAt_write8 (fixedWriteAt_write8 (fixedWriteAt_write8 hg
      (hin 0#64 (by decide))) (hin 1#64 (by decide))) (hin 2#64 (by decide))) (hin 3#64 (by decide)))
      (hin 4#64 (by decide))) (hin 5#64 (by decide))) (hin 6#64 (by decide))) (hin 7#64 (by decide))

private theorem fixedWriteAt_writeBytes {sp x : BitVec 64} :
    ∀ (bs : List (BitVec 8)) (a : BitVec 64) {g : Memory → Memory},
      FixedWriteAt sp x g → (a - sp).toNat + bs.length ≤ 544 → FixedWriteAt sp x (fun m => (g m).writeBytes a bs)
  | [], _, _, hg, _ => hg
  | _ :: rest, a, _, hg, hoff => by
    simp only [Memory.writeBytes]
    have hin : InRegion sp 544 a := by simp only [List.length_cons] at hoff; dsimp only [InRegion]; omega
    have hoff' : ((a + 1#64) - sp).toNat + rest.length ≤ 544 := by
      simp only [List.length_cons] at hoff; clear * - hoff; bv_omega
    exact fixedWriteAt_writeBytes rest (a + 1#64) (fixedWriteAt_write8 hg hin) hoff'

private theorem fixedWriteAt_nfsZeroMem (s₀ : State) (x : BitVec 64) :
    FixedWriteAt (nfsSp s₀) x (fun m => nfsZeroMem (s₀.setMem m)) := by
  have hsub (off : BitVec 64) (sz : Nat) (h : off.toNat + sz ≤ 544) :
      ((nfsSp s₀ + off) - nfsSp s₀).toNat + sz ≤ 544 := by
    have heq : (nfsSp s₀ + off) - nfsSp s₀ = off := by clear * -; bv_omega
    rwa [heq]
  have h0 : FixedWriteAt (nfsSp s₀) x (fun m => (s₀.setMem m).mem) := fixedWriteAt_id (nfsSp s₀) x
  have h1 := fixedWriteAt_write64 (a := nfsSp s₀ + 464#64) (w := s₀.readReg64 .x29) h0 (hsub 464#64 8 (by decide))
  have h2 := fixedWriteAt_write64 (a := nfsSp s₀ + 472#64) (w := s₀.readReg64 .lr) h1 (hsub 472#64 8 (by decide))
  have h3 := fixedWriteAt_write64 (a := nfsSp s₀ + 480#64) (w := s₀.readReg64 .x28) h2 (hsub 480#64 8 (by decide))
  have h4 := fixedWriteAt_write64 (a := nfsSp s₀ + 496#64) (w := s₀.readReg64 .x24) h3 (hsub 496#64 8 (by decide))
  have h5 := fixedWriteAt_write64 (a := nfsSp s₀ + 504#64) (w := s₀.readReg64 .x23) h4 (hsub 504#64 8 (by decide))
  have h6 := fixedWriteAt_write64 (a := nfsSp s₀ + 512#64) (w := s₀.readReg64 .x22) h5 (hsub 512#64 8 (by decide))
  have h7 := fixedWriteAt_write64 (a := nfsSp s₀ + 520#64) (w := s₀.readReg64 .x21) h6 (hsub 520#64 8 (by decide))
  have h8 := fixedWriteAt_write64 (a := nfsSp s₀ + 528#64) (w := s₀.readReg64 .x20) h7 (hsub 528#64 8 (by decide))
  have h9 := fixedWriteAt_write64 (a := nfsSp s₀ + 536#64) (w := s₀.readReg64 .x19) h8 (hsub 536#64 8 (by decide))
  exact fixedWriteAt_writeBytes (List.replicate 64 0#8) (nfsSp s₀ + 112#64) h9
    (by rw [List.length_replicate]; exact hsub 112#64 64 (by decide))

public theorem agreesOutside_nfsZeroMem_of_read_out {s₀ : State} {m' : Memory}
    (hread_out : ∀ x, InRegion (nfsSp s₀) 544 x →
      OutsideRegion (nfsSp s₀ + 176#64) 288 x → m'.read8 x = (nfsZeroMem s₀).read8 x)
    (hrw_m' : m'.RW (nfsSp s₀) 544) :
    AgreesOutside (nfsZeroMem (s₀.setMem m')) m' (nfsSp (s₀.setMem m') + 176#64) 288 := by
  have hsp_set : nfsSp (s₀.setMem m') = nfsSp s₀ := rfl
  rw [hsp_set]
  refine ⟨fun x hx => ?_, ((fixedWriteAt_nfsZeroMem s₀ 0#64).perm_eq m').symm,
    fun x _ => ?_, fun x hlf => ?_, fun x han => ((fixedWriteAt_nfsZeroMem s₀ x).anon_eq m').symm.trans han⟩
  · have hfw := fixedWriteAt_nfsZeroMem s₀ x
    by_cases hin : InRegion (nfsSp s₀) 544 x
    · rcases hfw.idem with hid | ⟨b, hb⟩
      · exact (hid m').symm
      · have hset_self : s₀.setMem s₀.mem = s₀ := by cases s₀; rfl
        rw [hb m', hread_out x hin hx, (hset_self ▸ hb s₀.mem : (nfsZeroMem s₀).read8 x = b)]
    · have hout : OutsideRegion (nfsSp s₀) 544 x := by dsimp only [InRegion, OutsideRegion] at hin ⊢; omega
      have hag_pro := agreesOutside_nfsPrologueMem (s₀.setMem m')
      have hag_z := agreesOutside_nfsZeroMem (s₀.setMem m')
      rw [hsp_set] at hag_pro hag_z
      exact ((hag_z.1 x (by clear * - hout; dsimp only [OutsideRegion] at hout ⊢; bv_omega)).trans
        (hag_pro.1 x (by clear * - hout; dsimp only [OutsideRegion] at hout ⊢; bv_omega))).symm
  · by_cases hin : InRegion (nfsSp s₀) 544 x
    · have hlf_m' := (Memory.permNoLazy_eq_some_rw_iff.mp (hrw_m' x hin)).2
      rw [hlf_m', (fixedWriteAt_nfsZeroMem s₀ x).lf_false m' hlf_m']
    · exact ((fixedWriteAt_nfsZeroMem s₀ x).lf_out
        (by dsimp only [InRegion, OutsideRegion] at hin ⊢; omega) m').symm
  · by_cases hin : InRegion (nfsSp s₀) 544 x
    · exact (Memory.permNoLazy_eq_some_rw_iff.mp (hrw_m' x hin)).2
    · exact ((fixedWriteAt_nfsZeroMem s₀ x).lf_out
        (by dsimp only [InRegion, OutsideRegion] at hin ⊢; omega) m').symm.trans hlf

public theorem s2Frame_720_of_agreesOutside {sp off : BitVec 64} {sz : Nat} {m₁ m₂ : Memory}
    (hag : AgreesOutside m₁ m₂ ((sp - 544#64) + off) sz) (hoff : off.toNat + sz ≤ 544) :
    S2Frame m₁ m₂ [(sp - 720#64, 720)] := by
  refine (s2Frame_of_hmacFrame (agreesOutside_toFrame hag)).mono fun a ha r hr => ?_
  simp only [List.mem_singleton] at hr; subst hr
  have ha' := ha (sp - 720#64, 720) (by simp)
  clear * - ha' hoff; dsimp only [OutsideRegion] at ha' ⊢; bv_omega

private def ReadOutZero (s₀ : State) (m : Memory) : Prop :=
  ∀ x, InRegion (nfsSp s₀) 544 x →
    OutsideRegion (nfsSp s₀ + 176#64) 288 x → m.read8 x = (nfsZeroMem s₀).read8 x

private def St0Bytes (s₀ : State) (st0 : ShaState) (m : Memory) : Prop :=
  m.readBytes (nfsSp s₀ + 240#64) 32 = shaStateBytes st0

set_option maxHeartbeats 1600000 in
/-- `HookSatExactMemcpy` + `HookSatCompress256` (`720` B stack) sibling of `nfs_seg0a_gt64_placed`. -/
public theorem nfs_seg0a_gt64_placed_exact [LibsignalPlacement] {F : ShaCompress}
    {H : LibsignalHooks} (h_mc : HookSatExactMemcpy H lsMemcpySym)
    (h_c256 : HookSatCompress256 H lsCompress256Sym F) {s₀ s : State}
    (hs : StateG0 nfs3CodeFakeB s₀ s nfs3PlacedFakeB)
    (hgt : 64 < (s₀.readReg64 .x2).toNat) (hlt : (s₀.readReg64 .x2).toNat < 2 ^ 63)
    (hiv : s₀.mem.readBytes (nfs3PlacedFakeB + bv% (601056 + 64)) 32 = shaStateBytes sha256IV)
    (hread_iv : s₀.mem.Readable (nfs3PlacedFakeB + bv% (601056 + 64)) 32)
    (hdisj_iv_stack : DisjointRegions (nfs3PlacedFakeB + bv% (601056 + 64)) 32 (s₀.sp - 720#64) 720)
    (hrw_stack : RW s₀.mem (s₀.sp - 720#64) 720)
    (hread_key : s₀.mem.Readable (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat)
    (hdisj_key_stack : DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 720#64) 720) :
    let key := s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
    RunsTo (lsProg_402 H) s (fun s' =>
      S2Frame s₀.mem s'.mem [(s₀.sp - 720#64, 720)] ∧
      (∀ x, InRegion (nfsSp s₀) 544 x →
        OutsideRegion (nfsSp s₀ + 176#64) 288 x → s'.mem.read8 x = (nfsZeroMem s₀).read8 x) ∧
      StateG1 nfs3CodeFakeB F key (s₀.setMem s'.mem) s' nfs3PlacedFakeB) := by
  intro key
  have hrw_stk544 : RW s₀.mem (s₀.sp - 544#64) 544 := hrw_stack.sub (by clear * -; bv_omega)
  have hkey_len : key.length = (s₀.readReg64 .x2).toNat := Memory.readBytes_length _ _ _
  have hkey_gt : 64 < key.length := by omega
  have hkey_lt : key.length < 2 ^ 63 := by omega
  obtain ⟨hs1, hs2, hs3, hs4, hs5⟩ := ikm_split_lemmas hkey_lt
  set st0 := (chunks64 (key.take (64 * (key.length / 64)))).foldl F sha256IV
  have hal_nfs : (nfsSp s₀ &&& 0b1111#64) = 0#64 := hs.common.sp_align
  have hstep1 : RunsTo (lsProg_402 H) s (fun s1 =>
      s1.pc = (blkPl_402).base + 120#64 ∧ s1.status = .Running ∧ s1.sp = nfsSp s₀ ∧
      s1.readReg64 .x19 = s₀.readReg64 .x0 ∧
      s1.readReg64 .x20 = s₀.readReg64 .x2 &&& 63#64 ∧ s1.readReg64 .x21 = s₀.readReg64 .x1 ∧
      s1.readReg64 .x22 = nfs3PlacedFakeB + bv% (601056 + 64) ∧
      s1.readReg64 .x23 = s₀.readReg64 .x2 &&& 9223372036854775744#64 ∧
      s1.readReg64 .x25 = s₀.readReg64 .x25 ∧ s1.readReg64 .x26 = s₀.readReg64 .x26 ∧
      s1.readReg64 .x27 = s₀.readReg64 .x27 ∧ s1.readReg64 .x29 = nfsSp s₀ + 464#64 ∧
      S2Frame s₀.mem s1.mem [(s₀.sp - 720#64, 720)] ∧
      ReadOutZero s₀ s1.mem ∧
      St0Bytes s₀ st0 s1.mem ∧
      s1.mem.read64 (nfsSp s₀ + 272#64) = BitVec.ofNat 64 (key.length / 64)) := by
    rcases hs with ⟨hpc, hcom, hx1, hx2⟩
    have hRW_s : s.mem.RW (nfsSp s₀) 544 := hcom.rw_stack hrw_stk544
    rcases hcom with ⟨hstat, hsp, hal_nfs, hx29, hx19, hx22, hx25, hx26, hx27, hag_zero⟩
    have hA_pro := agreesOutside_nfsPrologueMem s₀
    have hA_zero := agreesOutside_nfsZeroMem s₀
    have hRW_pro720 : (nfsPrologueMem s₀).RW (s₀.sp - 720#64) 720 :=
      (Frame.rw_iff (agreesOutside_toFrame hA_pro) _ _).mpr hrw_stack
    have hRW_zero720 : (nfsZeroMem s₀).RW (s₀.sp - 720#64) 720 :=
      (Frame.rw_iff (agreesOutside_toFrame hA_zero) _ _).mpr hRW_pro720
    have hRW_zero : (nfsZeroMem s₀).RW (nfsSp s₀) 544 :=
      hRW_zero720.sub (by clear * -; simp only [nfsSp]; bv_omega)
    have hread_iv_s : s.mem.Readable (nfs3PlacedFakeB + bv% (601056 + 64)) 32 :=
      (Frame.readable_iff (agreesOutside_toFrame hag_zero) _ _).mpr
        ((Frame.readable_iff (agreesOutside_toFrame hA_zero) _ _).mpr
          ((Frame.readable_iff (agreesOutside_toFrame hA_pro) _ _).mpr hread_iv))
    try simp only [arm64_norm] at hread_iv_s
    have hcr_iv0 : s.mem.canRead spqrSha256IVAddr 16 = true :=
      hread_iv_s.canRead_sub (by clear * -; bv_omega) (by decide)
    have hcr_iv16 : s.mem.canRead (spqrSha256IVAddr + 16#64) 16 = true :=
      hread_iv_s.canRead_sub (by clear * -; bv_omega) (by decide)
    have hdisj_iv_544 : DisjointRegions spqrSha256IVAddr 32 (nfsSp s₀) 544 := by
      have h : DisjointRegions spqrSha256IVAddr 32 (s₀.sp - 720#64) 720 := by
        simpa only [nfs3PlacedFakeB_add_iv] using hdisj_iv_stack
      clear * - h; simp only [DisjointRegions, nfsSp] at h ⊢; bv_omega
    have hiv_s : s.mem.readBytes (nfs3PlacedFakeB + bv% (601056 + 64)) 32 = shaStateBytes sha256IV := by
      have hd0 : DisjointRegions (nfsSp s₀ + 176#64) 288 (nfs3PlacedFakeB + bv% (601056 + 64)) 32 := by
        clear * - hdisj_iv_stack; simp only [DisjointRegions, nfsSp] at hdisj_iv_stack ⊢; bv_omega
      have hd1 : DisjointRegions (nfsSp s₀ + 112#64) 64 (nfs3PlacedFakeB + bv% (601056 + 64)) 32 := by
        clear * - hdisj_iv_stack; simp only [DisjointRegions, nfsSp] at hdisj_iv_stack ⊢; bv_omega
      have hd2 : DisjointRegions (nfsSp s₀ + 464#64) 80 (nfs3PlacedFakeB + bv% (601056 + 64)) 32 := by
        clear * - hdisj_iv_stack; simp only [DisjointRegions, nfsSp] at hdisj_iv_stack ⊢; bv_omega
      rw [(agreesOutside_toFrame hag_zero).readBytes_eq (by simp only [List.mem_singleton, forall_eq]; exact hd0) (by decide),
          (agreesOutside_toFrame hA_zero).readBytes_eq (by simp only [List.mem_singleton, forall_eq]; exact hd1) (by decide),
          (agreesOutside_toFrame hA_pro).readBytes_eq (by simp only [List.mem_singleton, forall_eq]; exact hd2) (by decide), hiv]
    iterate 12 sess_step
    have hx2_eq : s₀.readReg64 .x2 = BitVec.ofNat 64 key.length := by
      rw [hkey_len, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    set m_pre_c1 := ((s.mem.write8 (nfsSp s₀ + 239#64) 0#8).writeBytes
      (nfsSp s₀ + 240#64) (shaStateBytes sha256IV)).write64 (nfsSp s₀ + 272#64) (s₀.readReg64 .x2 >>> 6)
    have hag_pre_c1 : AgreesOutside (nfsZeroMem s₀) m_pre_c1 (nfsSp s₀ + 176#64) 288 := by
      have h1 := agreesOutside_sub_176_288 hag_zero (AgreesOutside.write8_self s.mem (nfsSp s₀ + 239#64) 0#8) (by decide)
      have h2 : AgreesOutside (s.mem.write8 (nfsSp s₀ + 239#64) 0#8)
          ((s.mem.write8 (nfsSp s₀ + 239#64) 0#8).writeBytes (nfsSp s₀ + 240#64) (shaStateBytes sha256IV))
          (nfsSp s₀ + 240#64) 32 := by
        have hlen : (shaStateBytes sha256IV).length = 32 := shaStateBytes_length sha256IV
        rw [← hlen]; exact ProofLib.agreesOutside_writeBytes _ _ _
      exact agreesOutside_sub_176_288 (agreesOutside_sub_176_288 h1 h2 (by decide))
        (AgreesOutside.write64_self _ (nfsSp s₀ + 272#64) (s₀.readReg64 .x2 >>> 6)) (by decide)
    have hRW_pre720 : m_pre_c1.RW (s₀.sp - 720#64) 720 :=
      (Frame.rw_iff (agreesOutside_toFrame hag_pre_c1) _ _).mpr hRW_zero720
    have hRW_pre544 : m_pre_c1.RW (nfsSp s₀) 544 :=
      (Frame.rw_iff (agreesOutside_toFrame hag_pre_c1) _ _).mpr hRW_zero
    have hst_pre_c1 : m_pre_c1.readBytes (nfsSp s₀ + 240#64) 32 = shaStateBytes sha256IV := by
      dsimp only [m_pre_c1]
      have hd : DisjointRegions (nfsSp s₀ + 272#64) 8 (nfsSp s₀ + 240#64) 32 := by
        clear * -; simp only [DisjointRegions]; bv_omega
      rw [(agreesOutside_toFrame (AgreesOutside.write64_self _ (nfsSp s₀ + 272#64) _)).readBytes_eq (by simp [hd]) (by decide)]
      exact readBytes_writeBytes_eq _ _ _ 32 (shaStateBytes_length sha256IV) (by decide)
    have hkey_pre_c1 : m_pre_c1.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat = key := by
      have hd1 : DisjointRegions (nfsSp s₀ + 176#64) 288 (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := by
        clear * - hdisj_key_stack; simp only [DisjointRegions, nfsSp] at hdisj_key_stack ⊢; bv_omega
      have hd2 : DisjointRegions (nfsSp s₀ + 112#64) 64 (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := by
        clear * - hdisj_key_stack; simp only [DisjointRegions, nfsSp] at hdisj_key_stack ⊢; bv_omega
      have hd3 : DisjointRegions (nfsSp s₀ + 464#64) 80 (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := by
        clear * - hdisj_key_stack; simp only [DisjointRegions, nfsSp] at hdisj_key_stack ⊢; bv_omega
      rw [(agreesOutside_toFrame hag_pre_c1).readBytes_eq (by simp [hd1]) (by omega),
          (agreesOutside_toFrame hA_zero).readBytes_eq (by simp [hd2]) (by omega),
          (agreesOutside_toFrame hA_pro).readBytes_eq (by simp [hd3]) (by omega)]
    have hpfx_pre_c1 : m_pre_c1.readBytes (s₀.readReg64 .x1) (64 * (key.length / 64)) = key.take (64 * (key.length / 64)) := by
      rw [readBytes_take_of_le m_pre_c1 (s₀.readReg64 .x1) (by omega : 64 * (key.length / 64) ≤ (s₀.readReg64 .x2).toNat), hkey_pre_c1]
    have hread_key_c1 : m_pre_c1.Readable (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat :=
      (Frame.readable_iff (agreesOutside_toFrame hag_pre_c1) _ _).mpr
        ((Frame.readable_iff (agreesOutside_toFrame hA_zero) _ _).mpr
          ((Frame.readable_iff (agreesOutside_toFrame hA_pro) _ _).mpr hread_key))
    refine placed_compress256_multi_step_sat h_c256 (m₀ := m_pre_c1)
      (hrun := by simp only [arm64_norm, hstat]) (hpc := rfl)
      (hx0 := by simp only [arm64_norm]) (hx1 := by simp only [arm64_norm, hx1])
      (hx2 := by simp only [arm64_norm, hx2, hx2_eq, hs1]) (hlr := by simp only [arm64_norm]; rfl)
      (hsp_al := by simp only [arm64_norm, hsp]; exact hal_nfs)
      (hmem := by
        rw [State.mem_setMem]; dsimp only [m_pre_c1]
        rw [write64_quad_240_iv_placed (s.mem.write8 (nfsSp s₀ + 239#64) 0#8) s.mem (nfsSp s₀)
          (by simpa only [arm64_norm] using hiv_s)])
      (hst := hst_pre_c1) (hbs := hpfx_pre_c1)
      (hrw_st := hRW_pre544.sub (by clear * -; bv_omega))
      (hrw_stk := by simp only [arm64_norm, hsp]; exact hRW_pre720.sub (by clear * -; simp only [nfsSp]; bv_omega))
      (hread_blk := fun a ha => hread_key_c1 a (by dsimp only [InRegion] at ha ⊢; omega))
      (hdisj_st_stk := by simp only [arm64_norm, hsp]; clear * -; unfold DisjointRegions; bv_omega)
      (hdisj_st_blk := Or.inr (by
        have hle_k : 64 * (key.length / 64) ≤ (s₀.readReg64 .x2).toNat := by omega
        have hpos_k : 0 < 64 * (key.length / 64) := by omega
        generalize 64 * (key.length / 64) = plen at hle_k hpos_k ⊢
        clear * - hdisj_key_stack hle_k hpos_k; simp only [DisjointRegions, nfsSp, arm64_norm] at hdisj_key_stack hle_k ⊢; bv_omega))
      (hdisj_stk_blk := Or.inr (by
        simp only [arm64_norm, hsp]
        have hle_k : 64 * (key.length / 64) ≤ (s₀.readReg64 .x2).toNat := by omega
        have hpos_k : 0 < 64 * (key.length / 64) := by omega
        generalize 64 * (key.length / 64) = plen at hle_k hpos_k ⊢
        clear * - hdisj_key_stack hle_k hpos_k; simp only [DisjointRegions, nfsSp, arm64_norm] at hdisj_key_stack hle_k ⊢; bv_omega))
      fun s1 htr1 hpc1 hstat1 hcc1 hst0_1 hs2_c1 _ => ?_
    simp only [arm64_norm, hsp] at hs2_c1
    have hf_c1 : S2Frame m_pre_c1 s1.mem [(s₀.sp - 720#64, 720)] :=
      hs2_c1.mono fun a ha r hr => by
        have ha' := ha (s₀.sp - 720#64, 720) (by simp)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> (clear * - ha'; dsimp only [nfsSp, OutsideRegion] at ha' ⊢; bv_omega)
    have hs2_01 : S2Frame s₀.mem s1.mem [(s₀.sp - 720#64, 720)] :=
      (((s2Frame_720_of_agreesOutside hA_pro (by decide)).trans
        (s2Frame_720_of_agreesOutside hA_zero (by decide))).trans
        (s2Frame_720_of_agreesOutside hag_pre_c1 (by decide))).trans hf_c1
    have hrout1 : ReadOutZero s₀ s1.mem := by
      intro x hin hx
      obtain ⟨hp, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp (hRW_pre544 x hin)
      have hout240 : OutsideRegion (nfsSp s₀ + 240#64) 32 x := by
        clear * - hx; dsimp only [OutsideRegion] at hx ⊢; bv_omega
      have hout176 : OutsideRegion (nfsSp s₀ - 176#64) 176 x :=
        (disj_stk544_ext176 (nfsSp s₀)).symm.outside hin (by decide)
      exact (hs2_c1.1 x (by rw [hp]; rfl) hlf fun r hr_mem => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr_mem
        rcases hr_mem with rfl | rfl; exacts [hout240, hout176]).trans (hag_pre_c1.1 x hx)
    have hnblk_1 : s1.mem.read64 (nfsSp s₀ + 272#64) = BitVec.ofNat 64 (key.length / 64) := by
      rw [s2Frame_hook_read64_stack_eq_176 hs2_c1 hRW_pre544 (by decide) (Or.inr ⟨by decide, by decide⟩)]
      dsimp only [m_pre_c1]; rw [Memory.read64_write64_same, hx2_eq]
      apply BitVec.eq_of_toNat_eq; rw [hs1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact RunsTo.refl
      ⟨hpc1, hstat1, hcc1.1.trans (by simp only [arm64_norm, hsp]),
       (CallingConventionPreserved.x19 hcc1).trans (by simp only [arm64_norm, hx19]),
       (CallingConventionPreserved.x20 hcc1).trans (by simp only [arm64_norm, hx2]),
       (CallingConventionPreserved.x21 hcc1).trans (by simp only [arm64_norm, hx1]),
       (CallingConventionPreserved.x22 hcc1).trans (by simp only [arm64_norm, hx22]; try rfl),
       (CallingConventionPreserved.x23 hcc1).trans (by simp only [arm64_norm, hx2]),
       (CallingConventionPreserved.x25 hcc1).trans (by simp only [arm64_norm, hx25]),
       (CallingConventionPreserved.x26 hcc1).trans (by simp only [arm64_norm, hx26]),
       (CallingConventionPreserved.x27 hcc1).trans (by simp only [arm64_norm, hx27]),
       (CallingConventionPreserved.x29 hcc1).trans (by simp only [arm64_norm, hx29]),
       hs2_01, hrout1, hst0_1, by simpa only [hkey_len, arm64_norm] using hnblk_1⟩ htr1
  refine hstep1.trans fun s1 hs1 => ?_
  clear hs hstep1
  rcases hs1 with ⟨hpc1, hstat1, hsp1, hx19_1, hx20_1, hx21_1,
      hx22_1, hx23_1, hx25_1, hx26_1, hx27_1, hx29_1, hs2_01, hrout1, hst0_1, hnblk_1⟩
  have hRW_s1 : s1.mem.RW (nfsSp s₀) 544 := hs2_01.rw_of_rw _ _ hrw_stk544
  iterate 5 sess_step
  have hx2_eq : s₀.readReg64 .x2 = BitVec.ofNat 64 key.length := by
    rw [hkey_len, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  set m_pre_mc := s1.mem.write8 (nfsSp s₀ + 239#64) (BitVec.truncate 8 (s₀.readReg64 .x2 &&& 63#64))
  have hag_w8 : AgreesOutside s1.mem m_pre_mc (nfsSp s₀ + 239#64) 1 :=
    AgreesOutside.write8_self s1.mem (nfsSp s₀ + 239#64) _
  have hkey_s1 : s1.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat = key :=
    s2Frame_readBytes_eq_of_readable hs2_01 hread_key (by omega) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hdisj_key_stack.symm
  have hkey_pre_mc : m_pre_mc.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat = key := by
    have hd : DisjointRegions (nfsSp s₀ + 239#64) 1 (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := by
      clear * - hdisj_key_stack; simp only [DisjointRegions, nfsSp] at hdisj_key_stack ⊢; bv_omega
    rw [(agreesOutside_toFrame hag_w8).readBytes_eq (by simp [hd]) (by omega), hkey_s1]
  have htail_pre_mc : m_pre_mc.readBytes
      (s₀.readReg64 .x1 + (s₀.readReg64 .x2 &&& 9223372036854775744#64))
      (key.length - 64 * (key.length / 64)) = key.drop (64 * (key.length / 64)) := by
    rw [hx2_eq, hs3]
    have hsplit : (s₀.readReg64 .x2).toNat = 64 * (key.length / 64) + (key.length - 64 * (key.length / 64)) := by omega
    have hadd := readBytes_add m_pre_mc (s₀.readReg64 .x1) (64 * (key.length / 64)) (key.length - 64 * (key.length / 64))
    rw [← hsplit, hkey_pre_mc] at hadd
    have hdrop := congrArg (List.drop (64 * (key.length / 64))) hadd.symm
    rwa [List.drop_left' (Memory.readBytes_length _ _ _)] at hdrop
  have hrw_pre_mc : m_pre_mc.RW (nfsSp s₀ + 176#64) (key.length - 64 * (key.length / 64)) := by
    have hlt64 : key.length - 64 * (key.length / 64) < 64 := by omega
    exact ((Frame.rw_iff (agreesOutside_toFrame hag_w8) _ _).mpr hRW_s1).sub (by
      generalize key.length - 64 * (key.length / 64) = len at hlt64 ⊢; clear * - hlt64; bv_omega)
  have hread_key_mc : m_pre_mc.Readable (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat :=
    (Frame.readable_iff (agreesOutside_toFrame hag_w8) _ _).mpr (s2Frame_readable_of_readable hs2_01 hread_key)
  have hread_tail_mc : m_pre_mc.Readable
      (s₀.readReg64 .x1 + (s₀.readReg64 .x2 &&& 9223372036854775744#64)) (key.length - 64 * (key.length / 64)) := by
    rw [hx2_eq, hs3]; intro a ha; refine hread_key_mc a ?_
    have htot : (BitVec.ofNat 64 (64 * (key.length / 64))).toNat +
        (key.length - 64 * (key.length / 64)) ≤ (s₀.readReg64 .x2).toNat := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
    generalize BitVec.ofNat 64 (64 * (key.length / 64)) = d at ha htot
    generalize key.length - 64 * (key.length / 64) = len at ha htot
    clear * - ha htot hlt; dsimp only [InRegion] at ha ⊢; bv_omega
  have hdisj_tail_mc : (key.length - 64 * (key.length / 64)) = 0 ∨
      DisjointRegions (nfsSp s₀ + 176#64) (key.length - 64 * (key.length / 64))
        (s₀.readReg64 .x1 + (s₀.readReg64 .x2 &&& 9223372036854775744#64)) (key.length - 64 * (key.length / 64)) := by
    by_cases h0 : key.length - 64 * (key.length / 64) = 0
    · exact Or.inl h0
    · refine Or.inr ?_; rw [hx2_eq, hs3]
      refine ((hdisj_key_stack.sub_left (s₀.readReg64 .x1 + BitVec.ofNat 64 (64 * (key.length / 64))) ?_).sub_right
        (nfsSp s₀ + 176#64) ?_).symm
      · refine ⟨by omega, ?_⟩
        have htot : (BitVec.ofNat 64 (64 * (key.length / 64))).toNat +
            (key.length - 64 * (key.length / 64)) ≤ (s₀.readReg64 .x2).toNat := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
        generalize BitVec.ofNat 64 (64 * (key.length / 64)) = d at htot ⊢
        generalize key.length - 64 * (key.length / 64) = tl at htot ⊢
        clear * - htot hlt; bv_omega
      · refine ⟨by omega, ?_⟩
        have htl_lt : key.length - 64 * (key.length / 64) < 64 := by omega
        generalize key.length - 64 * (key.length / 64) = tl at htl_lt ⊢
        clear * - htl_lt; simp only [nfsSp]; bv_omega
  refine placed_memcpy_step_of_exact h_mc
    (by simp only [arm64_norm, hstat1])
    (by simp (config := { decide := true }) only [State.spAligned, arm64_norm, hsp1, hal_nfs])
    rfl (by simp only [arm64_norm, hsp1]) (by simp only [arm64_norm, hx21_1, hx23_1])
    (by simp only [arm64_norm, hx20_1, hx2_eq, hs4]) (by simp only [arm64_norm]; rfl)
    (by simp only [arm64_norm, hsp1, hx20_1])
    htail_pre_mc hrw_pre_mc hread_tail_mc hdisj_tail_mc fun c => ?_
  dsimp only [applyMemcpyClobber]
  refine RunsTo.refl ?_ (htr := by prove_trace_eq)
  set tail := key.drop (64 * (key.length / 64))
  have htail_len : tail.length = key.length - 64 * (key.length / 64) := by simp [tail]
  have htail_lt : tail.length < 64 := by omega
  set m_end := m_pre_mc.writeBytes (nfsSp s₀ + 176#64) tail
  have hag_mc : AgreesOutside m_pre_mc m_end (nfsSp s₀ + 176#64) tail.length :=
    ProofLib.agreesOutside_writeBytes m_pre_mc (nfsSp s₀ + 176#64) tail
  have hs2_end : S2Frame s₀.mem m_end [(s₀.sp - 720#64, 720)] :=
    (hs2_01.trans (s2Frame_720_of_agreesOutside hag_w8 (by decide))).trans
      (s2Frame_720_of_agreesOutside hag_mc (by generalize tail.length = tl at htail_lt ⊢; clear * - htail_lt; bv_omega))
  have hrw_end544 : m_end.RW (nfsSp s₀) 544 := hs2_end.rw_of_rw _ _ hrw_stk544
  have hrout_end : ∀ x, InRegion (nfsSp s₀) 544 x →
      OutsideRegion (nfsSp s₀ + 176#64) 288 x → m_end.read8 x = (nfsZeroMem s₀).read8 x := by
    intro x hin hx
    have hout_mc : OutsideRegion (nfsSp s₀ + 176#64) tail.length x := by
      generalize tail.length = tl at htail_lt ⊢; clear * - hx htail_lt; dsimp only [OutsideRegion] at hx ⊢; bv_omega
    have hout_w8 : OutsideRegion (nfsSp s₀ + 239#64) 1 x := by
      clear * - hx; dsimp only [OutsideRegion] at hx ⊢; bv_omega
    exact (hag_mc.1 x hout_mc).trans ((hag_w8.1 x hout_w8).trans (hrout1 x hin hx))
  have hsp_set : nfsSp (s₀.setMem m_end) = nfsSp s₀ := rfl
  refine ⟨hs2_end, hrout_end,
    { pc_eq := by simp only [arm64_norm]
      common := {
        status := by simp only [arm64_norm, hstat1], sp_eq := by simp only [arm64_norm, hsp1, hsp_set],
        sp_align := hal_nfs, x29_eq := by simp only [arm64_norm, hx29_1, hsp_set],
        x19_eq := by simp only [arm64_norm, hx19_1], x22_eq := by simp only [arm64_norm, hx22_1]; try rfl,
        x25_eq := by simp only [arm64_norm, hx25_1], x26_eq := by simp only [arm64_norm, hx26_1],
        x27_eq := by simp only [arm64_norm, hx27_1],
        agrees_zero := agreesOutside_nfsZeroMem_of_read_out hrout_end hrw_end544 }
      tail_bytes := by
        rw [State.mem_setPC, State.mem_setMem, hsp_set]
        exact readBytes_writeBytes_eq m_pre_mc (nfsSp s₀ + 176#64) tail
          (key.length - 64 * (key.length / 64)) htail_len (by omega)
      pos_byte := by
        have h1 : m_end.read8 (nfsSp s₀ + 239#64) = m_pre_mc.read8 (nfsSp s₀ + 239#64) :=
          hag_mc.1 (nfsSp s₀ + 239#64)
            (by generalize tail.length = tl at htail_lt ⊢; clear * - htail_lt; simp only [OutsideRegion]; bv_omega)
        rw [State.mem_setPC, State.mem_setMem, hsp_set, h1]; dsimp only [m_pre_mc]
        rw [Memory.read8_write8_same, hx2_eq, hs5]
      st0_bytes := by
        have hd1 : DisjointRegions (nfsSp s₀ + 176#64) tail.length (nfsSp s₀ + 240#64) 32 := by
          generalize tail.length = tl at htail_lt ⊢; clear * - htail_lt; simp only [DisjointRegions]; bv_omega
        have hd2 : DisjointRegions (nfsSp s₀ + 239#64) 1 (nfsSp s₀ + 240#64) 32 := by
          clear * -; simp only [DisjointRegions]; bv_omega
        rw [State.mem_setPC, State.mem_setMem, hsp_set,
            (agreesOutside_toFrame hag_mc).readBytes_eq (by simp [hd1]) (by decide),
            (agreesOutside_toFrame hag_w8).readBytes_eq (by simp [hd2]) (by decide), hst0_1]
      nblk_word := by
        have hd1 : DisjointRegions (nfsSp s₀ + 176#64) tail.length (nfsSp s₀ + 272#64) 8 := by
          generalize tail.length = tl at htail_lt ⊢; clear * - htail_lt; simp only [DisjointRegions]; bv_omega
        have hd2 : DisjointRegions (nfsSp s₀ + 239#64) 1 (nfsSp s₀ + 272#64) 8 := by
          clear * -; simp only [DisjointRegions]; bv_omega
        rw [State.mem_setPC, State.mem_setMem, hsp_set,
            (agreesOutside_toFrame hag_mc).read64_eq (by simp [hd1]),
            (agreesOutside_toFrame hag_w8).read64_eq (by simp [hd2]), hnblk_1] }⟩

end LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSliceSegsExact
