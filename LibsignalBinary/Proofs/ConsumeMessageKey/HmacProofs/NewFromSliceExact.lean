/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.Defs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceInvariants -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.DefsSat
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceFirstHalf
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceSecondHalf
import LibsignalBinary.Proofs.CodeLayout

/-!
# `HookSatExactMemcpy` siblings for `<Hmac<Sha256> as KeyInit>::new_from_slice` (Block `114`)

Replaces `H lsMemcpySym = some memcpyHook` on Block `114`'s prologue+`memcpy` segment
(`nfs_seg0_placed`, `NewFromSliceInvariants.lean:943`) with
`h_memcpy : HookSatExactMemcpy H lsMemcpySym` via `placed_memcpy_step_of_exact`. Keeps `NfsRegInv`
and `NfsMemInv` unchanged, reuses `nfs_chunk1_placed`..`nfs_chunk4_placed` and
`nfs_second_half_placed` verbatim, and threads
`hread_key : s₀.mem.Readable (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat` through
`nfs_seg0_placed_exact`, `nfs_first_half_placed_exact`, and `new_from_slice_placed_run_exact`
(discharged from `keyA ↦ₛ key` in `ConsumeMessageKeyTransfer.NewFromSliceSat`).
-/

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceExact

open Arm64 ProofLib
open CryptoGames.HMAC (ShaState sha256IV)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalHooks LibsignalPlacement blkPl_114 lsProg_114)
open CryptoVerification.LibsignalAesCbc.Run.Bytes (readBytes_slice_of_readBytes_eq)
open CryptoVerification.LibsignalHmac (shaStateBytes)
open CryptoVerification.LibsignalTripleRatchet.Extract (S2Frame)
open LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.DefsSat (
  s2Frame_of_hmacFrame s2Frame_readBytes_eq_of_readable s2Frame_readable_of_readable
)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat (
  HookSatCompress256 s2_compress256_step_placed_of_hookSat
)
open CryptoVerification.LibsignalSession.CryptoHmacSha256 (
  AgreesOutside.write64_self CalleeSaved Frame HmacSt
  Layout.readBytes_writeBytes_eq NfsMemInv NfsOpadPostHookPlaced NfsPostCompress2Placed
  NfsPreCompress2Placed NfsRegInv NfsSavedStack RW RunsTo RunsToFrom RunsTo.lsProg_svc
  RunsTo.pairStep_114_0x28 TraceEq agreesOutside_nfsPrologueMem agreesOutside_toFrame
  innerState keyBlock keyBlock_length lsCompress256Sym lsMemcpySym lsSha256IVAddr
  map_xor_0x36_0x6a nfsPlacedFakeB nfsPlacedFakeB_add_iv nfsPrologueMem
  nfsSavedStack_prologue_432 nfsSp nfs_chunk1_placed nfs_chunk2_placed nfs_chunk3_placed
  nfs_chunk4_placed nfs_epilogue_placed nfs_opad_chunk0_placed nfs_opad_chunk1_placed
  nfs_opad_chunk2_placed nfs_opad_chunk3_placed nfs_sp_add_464_align nfs_sp_add_544_align
  nfs_sp_align nfs_sp_eq_add nfs_ule_65_false outerState readBytes_writeBytes_16_other
  readBytes_writeBytes_16_self rw_xorChunk shaStateBytes_length slice16 slice16_length
  write128_pair_ivsw write64_oct_zero_eq_writeBytes_64 write64_quad_288_eq_writeBytes_slice16
  writeBytes_key_over_zero64 xorChunk xorChunk4_eq_writeBytes
)
open LibsignalBinary.Heap.MuslMemOpsRunsTo (applyMemcpyClobber)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore (
  HookSatExactMemcpy placed_memcpy_step_of_exact
)

attribute [local arm64_norm]
  MemWidth.bytes SimdMemSize.bytes
  Memory.read8_write8_base_off_disjoint
  Memory.read8_write8_base_zero_off
  Memory.read8_write8_base_off_zero
  Memory.read8_write64_base_off_disjoint
  Memory.read8_write64_base_zero_off
  Memory.read8_write64_base_off_zero
  Memory.read8_write64_base_off_inbounds

set_option maxHeartbeats 3200000 in
/-- `HookSatExactMemcpy` sibling of `nfs_seg0_placed` (`NewFromSliceInvariants.lean:943`). -/
theorem nfs_seg0_placed_exact [LibsignalPlacement]
    {H : String → Option (State → State)}
    (h_memcpy : HookSatExactMemcpy H lsMemcpySym)
    {s₀ : State}
    (hpc : s₀.pc = (blkPl_114).base)
    (hstat : s₀.status = .Running)
    (hlen : (s₀.readReg64 .x2).toNat ≤ 64)
    (hiv : s₀.mem.readBytes lsSha256IVAddr 32 = shaStateBytes sha256IV)
    (hread_iv : s₀.mem.Readable lsSha256IVAddr 32)
    (hdisj_iv_stack : DisjointRegions lsSha256IVAddr 32 (s₀.sp - 544#64) 544)
    (hrw_out : RW s₀.mem (s₀.readReg64 .x0) 0x98)
    (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544)
    (hdisj_out_stack : DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 544#64) 544)
    (hread_key_s0 : s₀.mem.Readable (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat)
    (hdisj_key_stack : (s₀.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 544#64) 544)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64) :
    let key := s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
    RunsTo (lsProg_114 H) s₀ (fun s' =>
      s'.pc = (blkPl_114).base + 476#64 ∧
      s'.status = .Running ∧
      NfsRegInv nfsPlacedFakeB s₀ s' ∧
      NfsMemInv nfsPlacedFakeB s₀ s'.mem ∧
      s'.readReg64 .x8 = 0x36#64 ∧
      s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧
      s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧
      s'.readReg64 .x2 = 1#64 ∧
      s'.readVReg128 2#5 = s'.mem.read64 (nfsSp s₀ + 152#64) ++ s'.mem.read64 (nfsSp s₀ + 144#64) ∧
      s'.readVReg128 0#5 = s'.mem.read64 (nfsSp s₀ + 168#64) ++ s'.mem.read64 (nfsSp s₀ + 160#64) ∧
      s'.mem.readBytes (nfsSp s₀ + 144#64) 32 = (keyBlock key).drop 32 ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 (keyBlock key) 0 ∧
      s'.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 (keyBlock key) 16) := by
  intro key
  generalize hPost : (fun s' : State => _) = Post
  have hkey_len : key.length ≤ 64 := by
    dsimp only [key]; rw [Memory.readBytes_length]; exact hlen
  have hkb_len : (keyBlock key).length = 64 := keyBlock_length hkey_len
  have hsp₀ : s₀.sp = nfsSp s₀ + 544#64 := nfs_sp_eq_add s₀
  have hal_nfs : (nfsSp s₀ &&& 0b1111#64) = 0#64 := nfs_sp_align hal
  have hal_464 : ((nfsSp s₀ + 464#64) &&& 0b1111#64) = 0#64 := nfs_sp_add_464_align hal
  have hal_544 : ((nfsSp s₀ + 544#64) &&& 0b1111#64) = 0#64 := nfs_sp_add_544_align hal
  have hRW_stack : s₀.mem.RW (nfsSp s₀) 544 := hrw_stack
  have hcond : BitVec.ule 0x41#64 (s₀.readReg64 .x2) = false := nfs_ule_65_false hlen
  -- 10 instructions to `+0x28` (`40`), then relaxable pair at `+0x28..+0x30`, then 5 instructions to `memcpy`
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  refine RunsTo.pairStep_114_0x28 (by simp only [arm64_norm, hpc]) (by simp only [arm64_norm, hstat]) ?_
  sess_step; sess_step; sess_step; sess_step; sess_step
  -- Step 18: `memcpy` hook via `HookSatExactMemcpy`
  have hA_pro : AgreesOutside s₀.mem (nfsPrologueMem s₀) (nfsSp s₀ + 464#64) 80 :=
    agreesOutside_nfsPrologueMem s₀
  have hA_zero : AgreesOutside (nfsPrologueMem s₀)
      ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8))
      (nfsSp s₀ + 112#64) 64 := by
    simpa using AgreesOutside.writeBytes_self (nfsPrologueMem s₀) (nfsSp s₀ + 112#64) (List.replicate 64 0#8)
  have hread_key : ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8)).readBytes
      (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat = key := by
    rcases hdisj_key_stack with h0 | hdisj_key_stack
    · simp only [key, h0, Memory.readBytes]
    have hdisj_key_pro : DisjointRegions (nfsSp s₀ + 464#64) 80 (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := by
      clear * - hdisj_key_stack
      simp only [DisjointRegions, nfsSp] at hdisj_key_stack ⊢
      bv_omega
    have hdisj_key_112 : DisjointRegions (nfsSp s₀ + 112#64) 64 (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := by
      clear * - hdisj_key_stack
      simp only [DisjointRegions, nfsSp] at hdisj_key_stack ⊢
      bv_omega
    rw [(agreesOutside_toFrame hA_zero).readBytes_eq (by simp [hdisj_key_112]) (by omega),
        (agreesOutside_toFrame hA_pro).readBytes_eq (by simp [hdisj_key_pro]) (by omega)]
  have hrw_memcpy : ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8)).RW
      (nfsSp s₀ + 112#64) (s₀.readReg64 .x2).toNat := by
    have hrw0 : ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8)).RW (nfsSp s₀) 544 :=
      (Frame.rw_iff (agreesOutside_toFrame hA_zero) _ _).mpr
        ((Frame.rw_iff (agreesOutside_toFrame hA_pro) _ _).mpr hrw_stack)
    exact hrw0.sub (by clear * - hlen; bv_omega)
  have hreadable_memcpy :
      ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8)).Readable
        (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat :=
    (Frame.readable_iff (agreesOutside_toFrame hA_zero) _ _).mpr
      ((Frame.readable_iff (agreesOutside_toFrame hA_pro) _ _).mpr hread_key_s0)
  have hdisj_memcpy :
      (s₀.readReg64 .x2).toNat = 0 ∨
        DisjointRegions (nfsSp s₀ + 112#64) (s₀.readReg64 .x2).toNat
          (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := by
    rcases hdisj_key_stack with h0 | hdisj_key_stack
    · exact Or.inl h0
    · refine Or.inr ?_
      clear * - hdisj_key_stack hlen
      simp only [DisjointRegions, nfsSp] at hdisj_key_stack ⊢
      bv_omega
  refine placed_memcpy_step_of_exact h_memcpy
    (hrun := by simp only [arm64_norm, hstat])
    (hsp := by simp only [State.spAligned, arm64_norm, hal_nfs])
    (hpc := by simp only [arm64_norm, lsMemcpySym])
    (hx0 := by simp only [arm64_norm])
    (hx1 := by simp only [arm64_norm])
    (hx2 := by simp only [arm64_norm])
    (hlr := by simp only [arm64_norm]; rfl)
    (hmem := write64_oct_zero_eq_writeBytes_64 (nfsPrologueMem s₀) (nfsSp s₀))
    (hread := hread_key)
    (hrw := hrw_memcpy)
    (hreadable := hreadable_memcpy)
    (hdisj := hdisj_memcpy)
    fun c => ?_
  dsimp only [applyMemcpyClobber]
  rw [writeBytes_key_over_zero64]
  have hA_k0 : AgreesOutside (nfsPrologueMem s₀)
      ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (keyBlock key)) (nfsSp s₀ + 112#64) 64 := by
    have h := AgreesOutside.writeBytes_self (nfsPrologueMem s₀) (nfsSp s₀ + 112#64) (keyBlock key)
    rwa [hkb_len] at h
  have hRW_k0 : ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (keyBlock key)).RW (nfsSp s₀) 544 :=
    (Frame.rw_iff (agreesOutside_toFrame hA_k0) _ _).mpr
      ((Frame.rw_iff (agreesOutside_toFrame hA_pro) _ _).mpr hrw_stack)
  -- 10 instructions from `+0x44` (`68`) to `+0x1dc` (`476`)
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  subst hPost
  refine RunsTo.refl ?_
  set m_k0 := (nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (keyBlock key)
  have hk0_64 : m_k0.readBytes (nfsSp s₀ + 112#64) 64 = keyBlock key :=
    Layout.readBytes_writeBytes_eq (nfsPrologueMem s₀) (nfsSp s₀ + 112#64) (keyBlock key) 64 hkb_len (by decide)
  have hk0_take32 : m_k0.readBytes (nfsSp s₀ + 112#64) 32 = (keyBlock key).take 32 := by
    have h := readBytes_slice_of_readBytes_eq m_k0 (nfsSp s₀ + 112#64) (keyBlock key)
      (by rw [hkb_len]; exact hk0_64) 0 32 (by omega)
    simpa using h
  have hk0_drop32 : m_k0.readBytes (nfsSp s₀ + 144#64) 32 = (keyBlock key).drop 32 := by
    have h := readBytes_slice_of_readBytes_eq m_k0 (nfsSp s₀ + 112#64) (keyBlock key)
      (by rw [hkb_len]; exact hk0_64) 32 32 (by omega)
    have hadd : (nfsSp s₀ + 112#64) + BitVec.ofNat 64 32 = nfsSp s₀ + 144#64 := by clear * -; bv_omega
    rw [hadd, List.take_of_length_le (by simp [hkb_len])] at h
    exact h
  have hA_432 : AgreesOutside m_k0 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) (nfsSp s₀ + 432#64) 8 :=
    AgreesOutside.write64_self m_k0 (nfsSp s₀ + 432#64) 1#64
  have hf_k0 : Frame s₀.mem (m_k0.write64 (nfsSp s₀ + 432#64) 1#64)
      [(s₀.readReg64 .x0, 0x98), (nfsSp s₀, 544)] := by
    have hf0 : Frame s₀.mem s₀.mem [(s₀.readReg64 .x0, 0x98), (nfsSp s₀, 544)] := Frame.refl _ _
    have hf1 := Frame.of_agreesOutside_stack hf0 hA_pro (by decide)
    have hf2 := Frame.of_agreesOutside_stack hf1 hA_k0 (by decide)
    exact Frame.of_agreesOutside_stack hf2 hA_432 (by decide)
  have hM_432 : NfsMemInv nfsPlacedFakeB s₀ (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) := {
    rw_stack := (Frame.rw_iff hf_k0 _ _).mpr hrw_stack
    rw_out := (Frame.rw_iff hf_k0 _ _).mpr hrw_out
    readable_iv := by
      rw [nfsPlacedFakeB_add_iv]
      exact (Frame.readable_iff hf_k0 _ _).mpr hread_iv
    iv_bytes := by
      rw [nfsPlacedFakeB_add_iv]
      have hd432 : DisjointRegions (nfsSp s₀ + 432#64) 8 lsSha256IVAddr 32 := by
        clear * - hdisj_iv_stack; simp only [DisjointRegions, nfsSp] at hdisj_iv_stack ⊢; bv_omega
      have hdk0 : DisjointRegions (nfsSp s₀ + 112#64) 64 lsSha256IVAddr 32 := by
        clear * - hdisj_iv_stack; simp only [DisjointRegions, nfsSp] at hdisj_iv_stack ⊢; bv_omega
      have hdpro : DisjointRegions (nfsSp s₀ + 464#64) 80 lsSha256IVAddr 32 := by
        clear * - hdisj_iv_stack; simp only [DisjointRegions, nfsSp] at hdisj_iv_stack ⊢; bv_omega
      rw [(agreesOutside_toFrame hA_432).readBytes_eq (by simp [hd432]) (by decide),
          (agreesOutside_toFrame hA_k0).readBytes_eq (by simp [hdk0]) (by decide),
          (agreesOutside_toFrame hA_pro).readBytes_eq (by simp [hdpro]) (by decide), hiv]
    disj_iv_stack := by rw [nfsPlacedFakeB_add_iv]; exact hdisj_iv_stack
    disj_out_stack := hdisj_out_stack
    saved := nfsSavedStack_prologue_432 s₀ m_k0 hA_k0
    frame := hf_k0
  }
  have hM_final : NfsMemInv nfsPlacedFakeB s₀
      (((m_k0.write64 (nfsSp s₀ + 432#64) 1#64).writeBytes
        (nfsSp s₀ + 288#64) (slice16 (keyBlock key) 0)).writeBytes
        (nfsSp s₀ + 304#64) (slice16 (keyBlock key) 16)) :=
    (hM_432.writeBytes_low 288#64 _ (by simp [slice16_length])).writeBytes_low
      304#64 _ (by simp [slice16_length])
  have h144_eq :
      (((m_k0.write64 (nfsSp s₀ + 432#64) 1#64).writeBytes
        (nfsSp s₀ + 288#64) (slice16 (keyBlock key) 0)).writeBytes
        (nfsSp s₀ + 304#64) (slice16 (keyBlock key) 16)).readBytes (nfsSp s₀ + 144#64) 32 =
      (keyBlock key).drop 32 := by
    rw [readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _),
        readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _),
        (agreesOutside_toFrame hA_432).readBytes_eq
          (by clear * -; simp only [List.mem_singleton, forall_eq, DisjointRegions]; bv_omega) (by decide),
        hk0_drop32]
  refine ⟨by simp only [arm64_norm], by simp only [arm64_norm, hstat],
    ⟨by simp only [arm64_norm], hal_nfs, by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm]⟩,
    ?_,
    by simp only [arm64_norm], by simp only [arm64_norm],
    by simp only [arm64_norm], by simp only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    ?_, ?_, ?_⟩
  · dsimp only [State.setMem, State.setPC, State.setPState, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0
      (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact hM_final
  · dsimp only [State.setMem, State.setPC, State.setPState, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0
      (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact h144_eq
  · dsimp only [State.setMem, State.setPC, State.setPState, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0
      (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans
      (readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _))
  · dsimp only [State.setMem, State.setPC, State.setPState, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0
      (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _)

/-- `HookSatExactMemcpy` sibling of `nfs_first_half_placed` (`NewFromSliceFirstHalf.lean:862`). -/
theorem nfs_first_half_placed_exact [LibsignalPlacement]
    {H : LibsignalHooks} (h_memcpy : HookSatExactMemcpy H lsMemcpySym)
    {s₀ : State}
    (hpc : s₀.pc = (blkPl_114).base)
    (hstat : s₀.status = .Running)
    (hlen : (s₀.readReg64 .x2).toNat ≤ 64)
    (hiv : s₀.mem.readBytes lsSha256IVAddr 32 = shaStateBytes sha256IV)
    (hread_iv : s₀.mem.Readable lsSha256IVAddr 32)
    (hdisj_iv_stack : DisjointRegions lsSha256IVAddr 32 (s₀.sp - 544#64) 544)
    (hrw_out : RW s₀.mem (s₀.readReg64 .x0) 0x98)
    (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544)
    (hdisj_out_stack : DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 544#64) 544)
    (hread_key_s0 : s₀.mem.Readable (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat)
    (hdisj_key_stack : (s₀.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 544#64) 544)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64) :
    let key := s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
    RunsTo (lsProg_114 H) s₀ (fun s' =>
      s'.pc = (blkPl_114).base + 1260#64 ∧
      s'.status = .Running ∧
      NfsRegInv nfsPlacedFakeB s₀ s' ∧
      NfsMemInv nfsPlacedFakeB s₀ s'.mem ∧
      s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧
      s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧
      s'.readReg64 .x2 = 1#64 ∧
      s'.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes sha256IV ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x36#8) ∧
      s'.mem.readBytes (nfsSp s₀) 32 =
        (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16) := by
  intro key
  have hkey_len : key.length ≤ 64 := by
    dsimp only [key]; rw [Memory.readBytes_length]; exact hlen
  refine (nfs_seg0_placed_exact h_memcpy hpc hstat hlen hiv hread_iv hdisj_iv_stack hrw_out hrw_stack
    hdisj_out_stack hread_key_s0 hdisj_key_stack hal).trans fun s1 h1 => ?_
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

private theorem hmacRunsToFrom_of_hkdf {prog : Program} {s₀ s : State} {P : State → Prop}
    (h : CryptoVerification.LibsignalTripleRatchet.RunsToFrom prog s₀ s P) :
    RunsToFrom prog s₀ s P := by
  intro hL
  obtain ⟨s', hst, ⟨htr, hvr⟩, hP, hL'⟩ := h hL
  exact ⟨s', hst, htr, hvr, hP, hL'⟩

private theorem readable_of_rw {m : Memory} {a : BitVec 64} {n : Nat} (hrw : RW m a n) :
    m.Readable a n := by
  intro x hx
  obtain ⟨hp, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp (hrw x hx)
  exact ⟨by rw [hp]; rfl, hlf⟩

private theorem nfsRegInv_setMem_iff {b : BitVec 64} {s₀ s : State} {m₁ : Memory} :
    NfsRegInv b (s₀.setMem m₁) s ↔ NfsRegInv b s₀ s := by
  constructor <;> intro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ <;>
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

private theorem nfsSavedStack_setMem_iff {s₀ : State} {m₁ m : Memory} :
    NfsSavedStack (s₀.setMem m₁) m ↔ NfsSavedStack s₀ m := by
  constructor <;> intro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ <;>
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

private theorem nfsRegInv_of_cc {b : BitVec 64} {s₀ s s' : State}
    (hR : NfsRegInv b s₀ s) (hcc : CallingConventionPreserved s s') :
    NfsRegInv b s₀ s' := by
  rcases hR with ⟨hsp, hal, hx29, hx19, hx20, hx22, hx25, hx26, hx27⟩
  rcases hcc with ⟨hsp', hx19', hx20', _, hx22', _, _, hx25', hx26', hx27', _, hx29', _⟩
  exact ⟨hsp'.trans hsp, hal, hx29'.trans hx29, hx19'.trans hx19, hx20'.trans hx20,
    hx22'.trans hx22, hx25'.trans hx25, hx26'.trans hx26, hx27'.trans hx27⟩

private theorem nfsSavedStack_of_s2Frame {s₀ : State} {m₁ m₂ : Memory} {stOff : BitVec 64}
    (hrw_stack : RW m₁ (nfsSp s₀) 544)
    (hs : NfsSavedStack s₀ m₁)
    (hf : S2Frame m₁ m₂ [(nfsSp s₀ + stOff, 32), (s₀.sp - 720#64, 176)])
    (hoff : stOff.toNat + 32 ≤ 432) :
    NfsSavedStack s₀ m₂ := by
  rcases hs with ⟨m432, m464, m472, m480, m496, m504, m512, m520, m528, m536⟩
  have slot (off : BitVec 64) (hlo : 432 ≤ off.toNat) (hhi : off.toNat + 8 ≤ 544) :
      m₂.read64 (nfsSp s₀ + off) = m₁.read64 (nfsSp s₀ + off) := by
    refine hf.read64_eq (hrw_stack.sub (by clear * - hhi; bv_omega)) ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · clear * - hoff hlo hhi; unfold DisjointRegions; bv_omega
    · clear * - hlo hhi; unfold nfsSp DisjointRegions; bv_omega
  exact ⟨(slot 432#64 (by decide) (by decide)).trans m432,
         (slot 464#64 (by decide) (by decide)).trans m464,
         (slot 472#64 (by decide) (by decide)).trans m472,
         (slot 480#64 (by decide) (by decide)).trans m480,
         (slot 496#64 (by decide) (by decide)).trans m496,
         (slot 504#64 (by decide) (by decide)).trans m504,
         (slot 512#64 (by decide) (by decide)).trans m512,
         (slot 520#64 (by decide) (by decide)).trans m520,
         (slot 528#64 (by decide) (by decide)).trans m528,
         (slot 536#64 (by decide) (by decide)).trans m536⟩

private theorem s2Frame_nfs_sub {s₀ : State} {m₁ m₂ : Memory} {stOff : BitVec 64}
    (hf : S2Frame m₁ m₂ [(nfsSp s₀ + stOff, 32), (s₀.sp - 720#64, 176)])
    (hoff : stOff.toNat + 32 ≤ 544) :
    S2Frame m₁ m₂ [(s₀.readReg64 .x0, 0x98), (s₀.sp - 720#64, 720)] := by
  refine hf.mono fun a ha => ?_
  have hstk := ha (s₀.sp - 720#64, 720) (by simp)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · clear * - hstk hoff; unfold nfsSp OutsideRegion at hstk ⊢; bv_omega
  · clear * - hstk; unfold OutsideRegion at hstk ⊢; bv_omega

private theorem s2Frame_nfs_544_to_720 {s₀ : State} {m₁ m₂ : Memory}
    (hf : Frame m₁ m₂ [(s₀.readReg64 .x0, 0x98), (s₀.sp - 544#64, 544)]) :
    S2Frame m₁ m₂ [(s₀.readReg64 .x0, 0x98), (s₀.sp - 720#64, 720)] := by
  refine (s2Frame_of_hmacFrame hf).mono fun a ha => ?_
  have hout := ha (s₀.readReg64 .x0, 0x98) (by simp)
  have hstk := ha (s₀.sp - 720#64, 720) (by simp)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hout
  · clear * - hstk; unfold OutsideRegion at hstk ⊢; bv_omega

private theorem nfs_opad_from_post_placed [LibsignalPlacement] {F : ShaCompress}
    {H : LibsignalHooks} {s₀ s1 : State} {key : List (BitVec 8)} (hlen : key.length ≤ 64)
    (h1 : NfsOpadPostHookPlaced F s₀ key s1) :
    RunsTo (lsProg_114 H) s1 (NfsPreCompress2Placed F s₀ key) := by
  have hopad_len : ((keyBlock key).map (· ^^^ 0x5c#8)).length = 64 := by simp [keyBlock_length hlen]
  have hiv_len : (shaStateBytes sha256IV).length = 32 := shaStateBytes_length sha256IV
  refine (nfs_opad_chunk0_placed h1).trans fun s2 h2 => ?_
  have hrw1 : (xorChunk s1.mem (nfsSp s₀ + 288#64)).RW (nfsSp s₀) 544 := rw_xorChunk _ h1.memInv.rw_stack
  refine (nfs_opad_chunk1_placed hrw1 h2).trans fun s3 h3 => ?_
  have hrw2 : (xorChunk s2.mem (nfsSp s₀ + 304#64)).RW (nfsSp s₀) 544 := rw_xorChunk _ (h2.mem_eq ▸ hrw1)
  refine (nfs_opad_chunk2_placed hrw2 h3).trans fun s4 h4 => ?_
  have hrw3 : (xorChunk s3.mem (nfsSp s₀ + 320#64)).RW (nfsSp s₀) 544 := rw_xorChunk _ (h3.mem_eq ▸ hrw2)
  refine (nfs_opad_chunk3_placed hrw3 h4).mono fun s5 h5 => ?_
  have hm4 : xorChunk s4.mem (nfsSp s₀ + 336#64) =
      s1.mem.writeBytes (nfsSp s₀ + 288#64) ((keyBlock key).map (· ^^^ 0x5c#8)) := by
    rw [h4.mem_eq, h3.mem_eq, h2.mem_eq,
      (by clear * -; bv_omega : nfsSp s₀ + 304#64 = (nfsSp s₀ + 288#64) + 16#64),
      (by clear * -; bv_omega : nfsSp s₀ + 320#64 = (nfsSp s₀ + 288#64) + 32#64),
      (by clear * -; bv_omega : nfsSp s₀ + 336#64 = (nfsSp s₀ + 288#64) + 48#64),
      xorChunk4_eq_writeBytes, h1.blk_eq, map_xor_0x36_0x6a]
  have hmem5 : s5.mem =
      (((s1.mem.writeBytes (nfsSp s₀ + 288#64) ((keyBlock key).map (· ^^^ 0x5c#8))).writeBytes
        (nfsSp s₀ + 176#64) (shaStateBytes sha256IV)).write64 (nfsSp s₀ + 208#64) 1#64) := by
    rw [h5.mem_eq, hm4, write128_pair_ivsw _ s1.mem (nfsSp s₀) h1.ivsw_eq]
  have hM5 : NfsMemInv nfsPlacedFakeB s₀ s5.mem := by
    rw [hmem5]
    exact ((h1.memInv.writeBytes_low 288#64 _ (by rw [hopad_len]; decide)).writeBytes_low
      176#64 _ (by rw [hiv_len]; decide)).write64_low 208#64 1#64 (by decide)
  have hA_opad := AgreesOutside.writeBytes_self s1.mem (nfsSp s₀ + 288#64) ((keyBlock key).map (· ^^^ 0x5c#8))
  have hA_iv := AgreesOutside.writeBytes_self (s1.mem.writeBytes (nfsSp s₀ + 288#64) ((keyBlock key).map (· ^^^ 0x5c#8)))
    (nfsSp s₀ + 176#64) (shaStateBytes sha256IV)
  have hA_208 := AgreesOutside.write64_self
    ((s1.mem.writeBytes (nfsSp s₀ + 288#64) ((keyBlock key).map (· ^^^ 0x5c#8))).writeBytes
      (nfsSp s₀ + 176#64) (shaStateBytes sha256IV)) (nfsSp s₀ + 208#64) 1#64
  refine {
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
      exact Layout.readBytes_writeBytes_eq s1.mem (nfsSp s₀ + 288#64) _ 64 hopad_len (by decide)
    ost_eq := by
      rw [hmem5, (agreesOutside_toFrame hA_208).readBytes_eq
            (by clear * -; simp only [List.mem_singleton, forall_eq, DisjointRegions]; bv_omega) (by decide)]
      exact Layout.readBytes_writeBytes_eq _ (nfsSp s₀ + 176#64) _ 32 hiv_len (by decide)
    obl_eq := by rw [hmem5, Memory.read64_write64_same] }

private theorem nfs_compress1_placed_runsTo_sat [LibsignalPlacement] {F : ShaCompress}
    {H : LibsignalHooks} (h_compress : HookSatCompress256 H lsCompress256Sym F)
    {s₀ s : State} {key : List (BitVec 8)} (hlen : key.length ≤ 64)
    (hdisj_iv_720 : DisjointRegions lsSha256IVAddr 32 (s₀.sp - 720#64) 720)
    (hrw_slack : RW s.mem (s₀.sp - 720#64) 176)
    (hpc : s.pc = (blkPl_114).base + 1260#64) (hstat : s.status = .Running)
    (hR : NfsRegInv nfsPlacedFakeB s₀ s) (hM : NfsMemInv nfsPlacedFakeB s₀ s.mem)
    (hx0 : s.readReg64 .x0 = nfsSp s₀ + 400#64) (hx1 : s.readReg64 .x1 = nfsSp s₀ + 288#64)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hist : s.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes sha256IV)
    (hblk : s.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x36#8))
    (hivsw : s.mem.readBytes (nfsSp s₀) 32 =
      (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16) :
    RunsTo (lsProg_114 H) s (fun s2 =>
      NfsOpadPostHookPlaced F (s₀.setMem s2.mem) key s2 ∧
      S2Frame s.mem s2.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 720#64, 720)]) := by
  have hsp_s := hR.sp_eq
  have hal_s := hR.sp_align
  have hsp_sub176 : nfsSp s₀ - 176#64 = s₀.sp - 720#64 := by
    unfold nfsSp; bv_omega
  have hipad_len : ((keyBlock key).map (· ^^^ 0x36#8)).length = 64 := by simp [keyBlock_length hlen]
  have hrw_ist : RW s.mem (nfsSp s₀ + 400#64) 32 := hM.rw_stack.sub (by clear * -; bv_omega)
  have hrw_blk : RW s.mem (nfsSp s₀ + 288#64) 64 := hM.rw_stack.sub (by clear * -; bv_omega)
  have hrw_ivsw : RW s.mem (nfsSp s₀) 32 := hM.rw_stack.sub (by clear * -; bv_omega)
  sess_step
  refine hmacRunsToFrom_of_hkdf (s2_compress256_step_placed_of_hookSat h_compress.toHookSat
    (stPtr := nfsSp s₀ + 400#64) (blkPtr := nfsSp s₀ + 288#64)
    (lr := (blkPl_114).base + 1264#64) (st := sha256IV)
    (blk := (keyBlock key).map (· ^^^ 0x36#8))
    (hrun := by simp only [arm64_norm, hstat])
    (hpc := by simp only [arm64_norm])
    (hx0 := by simp only [arm64_norm, hx0])
    (hx1 := by simp only [arm64_norm, hx1])
    (hx2 := by simp only [arm64_norm, hx2])
    (hlr := by simp only [arm64_norm])
    (hsp_al := by simp only [arm64_norm, hsp_s, hal_s])
    (hst := hist) (hblk := hblk) (hlen := hipad_len)
    (hrw_st := hrw_ist)
    (hrw_stk := by simp only [arm64_norm, hsp_s, hsp_sub176]; exact hrw_slack)
    (hread_blk := readable_of_rw hrw_blk)
    (hdisj_st_stk := by
      simp only [arm64_norm, hsp_s, hsp_sub176]
      clear * -; unfold nfsSp DisjointRegions; bv_omega)
    (hdisj_st_blk := by clear * -; unfold DisjointRegions; bv_omega)
    (hdisj_stk_blk := by
      simp only [arm64_norm, hsp_s, hsp_sub176]
      clear * -; unfold nfsSp DisjointRegions; bv_omega)
    (fun s2 htr2 hpc2 hstat2 hcc2 _ _ _ hist2 hs2 _ => ?_)
    (htr_s := ⟨by simp only [arm64_norm], by simp only [arm64_norm]⟩))
  intro hL2
  have hcc_s : CallingConventionPreserved s s2 :=
    CallingConventionPreserved.trans (by
      refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [arm64_norm]) hcc2
  have hs2' : S2Frame s.mem s2.mem [(nfsSp s₀ + 400#64, 32), (s₀.sp - 720#64, 176)] := by
    simpa only [arm64_norm, hsp_s, hsp_sub176] using hs2
  have hiv_disj : ∀ r ∈ [(nfsSp s₀ + 400#64, 32), (s₀.sp - 720#64, 176)],
      DisjointRegions r.1 r.2 (nfsPlacedFakeB + 0x100#64) 32 := by
    rw [nfsPlacedFakeB_add_iv]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · clear * - hdisj_iv_720; unfold nfsSp DisjointRegions at *; bv_omega
    · clear * - hdisj_iv_720; dsimp only; unfold DisjointRegions at hdisj_iv_720 ⊢; bv_omega
  have hM2 : NfsMemInv nfsPlacedFakeB (s₀.setMem s2.mem) s2.mem :=
    { rw_stack := hs2'.rw_of_rw _ _ hM.rw_stack
      rw_out := hs2'.rw_of_rw _ _ hM.rw_out
      readable_iv := s2Frame_readable_of_readable hs2' hM.readable_iv
      iv_bytes := (s2Frame_readBytes_eq_of_readable hs2' hM.readable_iv (by decide) hiv_disj).trans hM.iv_bytes
      disj_iv_stack := hM.disj_iv_stack
      disj_out_stack := hM.disj_out_stack
      saved := nfsSavedStack_setMem_iff.mpr (nfsSavedStack_of_s2Frame hM.rw_stack hM.saved hs2' (by decide))
      frame := Frame.refl s2.mem _ }
  have hblk2 : s2.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x36#8) := by
    refine (hs2'.readBytes_eq hrw_blk ?_ (by decide)).trans hblk
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (clear * -; unfold nfsSp DisjointRegions; bv_omega)
  have hivsw2 : s2.mem.readBytes (nfsSp s₀) 32 =
      (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16 := by
    refine (hs2'.readBytes_eq hrw_ivsw ?_ (by decide)).trans hivsw
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (clear * -; unfold nfsSp DisjointRegions; bv_omega)
  exact ⟨s2, .refl s2, htr2,
    ⟨{ pc_eq := hpc2, status := hstat2, regInv := nfsRegInv_setMem_iff.mpr (nfsRegInv_of_cc hR hcc_s),
       memInv := hM2, ist_eq := hist2, blk_eq := hblk2, ivsw_eq := hivsw2 },
     s2Frame_nfs_sub hs2' (by decide)⟩, hL2⟩

private theorem nfs_compress2_placed_runsTo_sat [LibsignalPlacement] {F : ShaCompress}
    {H : LibsignalHooks} (h_compress : HookSatCompress256 H lsCompress256Sym F)
    {s₀ s : State} {key : List (BitVec 8)} (hlen : key.length ≤ 64)
    (hdisj_iv_720 : DisjointRegions lsSha256IVAddr 32 (s₀.sp - 720#64) 720)
    (hrw_slack : RW s.mem (s₀.sp - 720#64) 176)
    (hs : NfsPreCompress2Placed F s₀ key s) :
    RunsTo (lsProg_114 H) s (fun s2 =>
      NfsPostCompress2Placed F (s₀.setMem s2.mem) key s2 ∧
      S2Frame s.mem s2.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 720#64, 720)]) := by
  have hpc := hs.pc_eq
  have hstat := hs.status
  have hR := hs.regInv
  have hM := hs.memInv
  have hsp_s := hR.sp_eq
  have hal_s := hR.sp_align
  have hsp_sub176 : nfsSp s₀ - 176#64 = s₀.sp - 720#64 := by
    unfold nfsSp; bv_omega
  have hopad_len : ((keyBlock key).map (· ^^^ 0x5c#8)).length = 64 := by simp [keyBlock_length hlen]
  have hrw_ost : RW s.mem (nfsSp s₀ + 176#64) 32 := hM.rw_stack.sub (by clear * -; bv_omega)
  have hrw_blk : RW s.mem (nfsSp s₀ + 288#64) 64 := hM.rw_stack.sub (by clear * -; bv_omega)
  have hrw_ist : RW s.mem (nfsSp s₀ + 400#64) 32 := hM.rw_stack.sub (by clear * -; bv_omega)
  have hrw_obl : RW s.mem (nfsSp s₀ + 208#64) 8 := hM.rw_stack.sub (by clear * -; bv_omega)
  sess_step
  refine hmacRunsToFrom_of_hkdf (s2_compress256_step_placed_of_hookSat h_compress.toHookSat
    (stPtr := nfsSp s₀ + 176#64) (blkPtr := nfsSp s₀ + 288#64)
    (lr := (blkPl_114).base + 2064#64) (st := sha256IV)
    (blk := (keyBlock key).map (· ^^^ 0x5c#8))
    (hrun := by simp only [arm64_norm, hstat])
    (hpc := by simp only [arm64_norm])
    (hx0 := by simp only [arm64_norm, hs.x0_eq])
    (hx1 := by simp only [arm64_norm, hs.x1_eq])
    (hx2 := by simp only [arm64_norm, hs.x2_eq])
    (hlr := by simp only [arm64_norm])
    (hsp_al := by simp only [arm64_norm, hsp_s, hal_s])
    (hst := hs.ost_eq) (hblk := hs.blk_eq) (hlen := hopad_len)
    (hrw_st := hrw_ost)
    (hrw_stk := by simp only [arm64_norm, hsp_s, hsp_sub176]; exact hrw_slack)
    (hread_blk := readable_of_rw hrw_blk)
    (hdisj_st_stk := by
      simp only [arm64_norm, hsp_s, hsp_sub176]
      clear * -; unfold nfsSp DisjointRegions; bv_omega)
    (hdisj_st_blk := by clear * -; unfold DisjointRegions; bv_omega)
    (hdisj_stk_blk := by
      simp only [arm64_norm, hsp_s, hsp_sub176]
      clear * -; unfold nfsSp DisjointRegions; bv_omega)
    (fun s2 htr2 hpc2 hstat2 hcc2 _ _ _ host2 hs2 _ => ?_)
    (htr_s := ⟨by simp only [arm64_norm], by simp only [arm64_norm]⟩))
  intro hL2
  have hcc_s : CallingConventionPreserved s s2 :=
    CallingConventionPreserved.trans (by
      refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [arm64_norm]) hcc2
  have hs2' : S2Frame s.mem s2.mem [(nfsSp s₀ + 176#64, 32), (s₀.sp - 720#64, 176)] := by
    simpa only [arm64_norm, hsp_s, hsp_sub176] using hs2
  have hiv_disj : ∀ r ∈ [(nfsSp s₀ + 176#64, 32), (s₀.sp - 720#64, 176)],
      DisjointRegions r.1 r.2 (nfsPlacedFakeB + 0x100#64) 32 := by
    rw [nfsPlacedFakeB_add_iv]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · clear * - hdisj_iv_720; unfold nfsSp DisjointRegions at *; bv_omega
    · clear * - hdisj_iv_720; dsimp only; unfold DisjointRegions at hdisj_iv_720 ⊢; bv_omega
  have hM2 : NfsMemInv nfsPlacedFakeB (s₀.setMem s2.mem) s2.mem :=
    { rw_stack := hs2'.rw_of_rw _ _ hM.rw_stack
      rw_out := hs2'.rw_of_rw _ _ hM.rw_out
      readable_iv := s2Frame_readable_of_readable hs2' hM.readable_iv
      iv_bytes := (s2Frame_readBytes_eq_of_readable hs2' hM.readable_iv (by decide) hiv_disj).trans hM.iv_bytes
      disj_iv_stack := hM.disj_iv_stack
      disj_out_stack := hM.disj_out_stack
      saved := nfsSavedStack_setMem_iff.mpr (nfsSavedStack_of_s2Frame hM.rw_stack hM.saved hs2' (by decide))
      frame := Frame.refl s2.mem _ }
  have hist2 : s2.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes (innerState F key) := by
    refine (hs2'.readBytes_eq hrw_ist ?_ (by decide)).trans hs.ist_eq
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (clear * -; unfold nfsSp DisjointRegions; bv_omega)
  have hobl2 : s2.mem.read64 (nfsSp s₀ + 208#64) = 1#64 := by
    refine (hs2'.read64_eq hrw_obl ?_).trans hs.obl_eq
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (clear * -; unfold nfsSp DisjointRegions; bv_omega)
  exact ⟨s2, .refl s2, htr2,
    ⟨{ pc_eq := hpc2, status := hstat2, regInv := nfsRegInv_setMem_iff.mpr (nfsRegInv_of_cc hR hcc_s),
       memInv := hM2, ist_eq := hist2, ost_eq := host2, obl_eq := hobl2 },
     s2Frame_nfs_sub hs2' (by decide)⟩, hL2⟩

/-- `HookSatExactMemcpy` + `HookSatCompress256` sibling of `new_from_slice_placed_run`
(`NewFromSliceSecondHalf.lean:1164`), with `720`-B stack (`544` B own frame + `176` B `compress256` slack). -/
theorem new_from_slice_placed_run_exact [LibsignalPlacement] {F : ShaCompress}
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
    (hal : (s₀.sp &&& 0b1111#64) = 0#64) :
    let key := s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
    RunsTo (lsProg_114 H) s₀ (fun s' =>
      s'.pc = s₀.readReg64 .lr ∧ s'.status = .Running ∧ CalleeSaved s₀ s' ∧
      s'.mem.read64 (s₀.readReg64 .x0) = 0#64 ∧ HmacSt s'.mem (s₀.readReg64 .x0 + 8#64) F key [] ∧
      S2Frame s₀.mem s'.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 720#64, 720)]) := by
  intro key
  have hkey_len : key.length ≤ 64 := by
    dsimp only [key]; rw [Memory.readBytes_length]; exact hlen
  have hrw_stack544 : RW s₀.mem (s₀.sp - 544#64) 544 :=
    hrw_stack.sub (by clear * -; bv_omega)
  have hrw_slack0 : RW s₀.mem (s₀.sp - 720#64) 176 :=
    hrw_stack.sub (by clear * -; bv_omega)
  have hdisj_iv_544 : DisjointRegions lsSha256IVAddr 32 (s₀.sp - 544#64) 544 :=
    hdisj_iv_stack.sub_right _ ⟨by decide, by clear * -; bv_omega⟩
  have hdisj_out_544 : DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 544#64) 544 :=
    hdisj_out_stack.sub_right _ ⟨by decide, by clear * -; bv_omega⟩
  have hdisj_key_544 : (s₀.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 544#64) 544 :=
    hdisj_key_stack.imp id (fun hd => hd.sub_right _ ⟨by decide, by clear * -; bv_omega⟩)
  refine (nfs_first_half_placed_exact h_memcpy hpc hstat hlen hiv hread_iv hdisj_iv_544 hrw_out hrw_stack544
    hdisj_out_544 hread_key_s0 hdisj_key_544 hal).trans fun s1 h1 => ?_
  rcases h1 with ⟨hpc1, hstat1, hR1, hM1, hx0_1, hx1_1, hx2_1, hist1, hblk1, hivsw1⟩
  have hf01 : S2Frame s₀.mem s1.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 720#64, 720)] :=
    s2Frame_nfs_544_to_720 hM1.frame
  have hrw_slack1 : RW s1.mem (s₀.sp - 720#64) 176 := hf01.rw_of_rw _ _ hrw_slack0
  refine (nfs_compress1_placed_runsTo_sat h_compress hkey_len hdisj_iv_stack hrw_slack1
    hpc1 hstat1 hR1 hM1 hx0_1 hx1_1 hx2_1 hist1 hblk1 hivsw1).trans fun s2 ⟨hpost1, hf12⟩ => ?_
  have hf02 := hf01.trans hf12
  refine (nfs_opad_from_post_placed hkey_len hpost1).trans fun s3 hpre2 => ?_
  have hf23 : S2Frame s2.mem s3.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 720#64, 720)] :=
    s2Frame_nfs_544_to_720 hpre2.memInv.frame
  have hf03 := hf02.trans hf23
  have hrw_slack3 : RW s3.mem (s₀.sp - 720#64) 176 := hf03.rw_of_rw _ _ hrw_slack0
  refine (nfs_compress2_placed_runsTo_sat (s₀ := s₀.setMem s2.mem) h_compress hkey_len hdisj_iv_stack hrw_slack3 hpre2).trans
    fun s4 ⟨hpost2, hf34⟩ => ?_
  have hf04 := hf03.trans hf34
  refine (nfs_epilogue_placed (s₀ := s₀.setMem s4.mem) hal hpost2).mono fun s5 h5 => ?_
  rcases h5 with ⟨hpc5, hstat5, hcs5, hret5, hhm5, hframe5⟩
  exact ⟨hpc5, hstat5, hcs5, hret5, hhm5, hf04.trans (s2Frame_nfs_544_to_720 hframe5)⟩

end LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceExact
