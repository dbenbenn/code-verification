/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOk
public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetVmSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToVecBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAux
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.SpqrV1.Kdf.FinalizeFixed
import LibsignalBinary.Proofs.SpqrV1.Kdf.FinalizeFixedGen
import LibsignalBinary.Proofs.SpqrV1.Kdf.FinalizeFixedGenSat
import LibsignalBinary.Proofs.SpqrV1.Kdf.FrameROExt
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExpand
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExpandExact
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtractExact
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceLoopExact
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetFinSat
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetNfsSat
import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSlice
import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSliceGen
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Expand
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandCommon
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixedExt
import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.CompressAndDigest

/-!
# `HookSat` Sibling of `SpqrV1.Kdf.HkdfToSliceOkBudget` (`HkdfToSliceOkBudgetSat`)

Budget-threaded multi-placed bridges for `spqr::kdf::hkdf_to_slice` (Block `379`) and
`spqr::kdf::hkdf_to_vec` (Block `378`) under `[HkdfPlacedHooksExactSat C.F H]` and
`HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec` / `withAllocVmPreserved sessionMemsetRegionSpec`.
-/

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetSat

open Arm64 ProofLib
open CryptoGames.HKDF (hkdfExpand)
open CryptoGames.HMAC (ShaState sha256IV)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
  blkLib_eq_379 blkPC_378 blkPC_379 blkPl_378 blkPl_379 blkPl_402 blkPl_425
  libsignalMutatedBlocks libsignalSessionLib ls_externAt?_of_mem lsmpl lsρ)
open CryptoVerification.LibsignalHmac (shaStateBytes)
open CryptoVerification.LibsignalSession.CryptoHmacSha256 (disjointRegions_of_ro_rw length_hmacWith)
open CryptoVerification.LibsignalSpqrV1 (hkdfExtractBytes spqrHkdfWith)
open CryptoVerification.LibsignalTripleRatchet
  (CalleeSaved CallingConventionPreserved_of_calleeSaved Frame HmacSt RW RunsTo
   extHookStack extract_withLsCodeRoLoaded keys_ls_subroutine_ok_of_block_cro
   lsMemsetSym noAllocShimSpec ro_outside_rw_shared_lb sessionMemsetRegionSpec withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Expand
  (hkdfExpand_64_eq t1_length t2_length t3_length)
open CryptoVerification.LibsignalTripleRatchet.Extract (S2Frame)
open CryptoVerification.SpqrV1.Alloc (spqrRustNoAllocShimSym)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt hkdfToSliceSpec hkdfToSliceSpqrSpec)
open CryptoVerification.SpqrV1.Kdf (HmacStN effectiveHmacKey effectiveHmacKey_length_le
  fin3PlacedFakeB hmacWith_effectiveHmacKey spqrRustAllocZeroedSym)
open CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof
  (HCommon HExpCommon HFrame HPost HPre HSaved
   StateB1Fin StateB1RetFin StateE3cc StateEFin StateENfs1 StateENfs2 StateERet1
   StateERet2 StateERetFin StateLoop StateLoopA2 StateLoopC StateLoopFin
   b1_done_32_placed_runsTo b1_to_loop_placed_runsTo bv_sub_add_lit_ge
   epilogue_placed_runsTo hkdfCodeFakeB hkdfExpand_32_eq hkdfExpand_96_eq hsp
   hsp_aligned iter_a1_placed_runsTo rodata_sha256IV_placed
   seg_b1a_placed_runsTo seg_e0_placed_runsTo seg_e1d_placed_runsTo seg_e2_placed_runsTo seg_e3_placed_runsTo)
open CryptoVerification.SpqrV1.Kdf.NewFromSlice3Proof (nfs3PlacedFakeB nfs3PlacedFakeB_add_iv spqrSha256IVAddr)
open CryptoVerification.SpqrV1.Kdf.SpqrKdfExt (disjointRegions_of_outside)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (rustAllocZeroedBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAux
  (stripExecOutside_readable stripExecOutside_rw unstrip_frame)
open LibsignalBinary.Proofs.ConsumeMessageKey.CoupledCompress256Sat
  (hmacNoMemsetExcHooksSat hmacNoMemsetExcHooksSat_compress hmacNoMemsetExcHooksSat_memcpy)
open LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget (withAllocVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Kdf.FinalizeFixedGenSat (FinPre3PfxGenSat)
open LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExpandExact (seg_b1b_placed_runsTo_exact seg_b1d_placed_runsTo_exact)
open LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtractExact (readable_of_rw seg_e1_placed_runsTo_exact)
open LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceLoopExact
  (iter_a2_placed_runsTo_exact iter_b_placed_runsTo_exact
   iter_d_continue_placed_runsTo_exact iter_d_done_placed_runsTo_exact)
open LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetFinSat (finalize_fixed3_pfx_lt64_kdf_vm_sat)
open LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetNfsSat (nfs_gen_vm nfs_le64_vm)
open LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetVmSat
  (ProgMemsetAllocVm RunsToVm blk379_noMsr blk379_noSvc0 lift_block_to_379_vm
   stripS_hcommon_refl stripS_hexpCommon_refl stripS_hmacSt stripS_hmacStN
   stripS_mem stripS_read64 stripS_readBytes unstrip_hcommon unstrip_hexpCommon unstrip_s2Frame)
open LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToVecBudget (hkdfToVecSpec hkdf_to_vec_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat (HkdfPlacedHooksExactSat)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemsetRegionBudgetSpec)

attribute [local arm64_norm] MemWidth.bytes SimdMemSize.bytes
attribute [local simp, local arm64_norm] bv_sub_add_lit hkdfCodeFakeB bv_sub_add_lit_ge

@[local simp, local arm64_norm]
private theorem lsmpl_base_475 [LibsignalPlacement] : lsmpl.base 425 = (blkPl_425).base := rfl

/-! ## 4. Block `379` / `402` Assembly & Separation-Logic Bridges -/

@[local simp]
private theorem hsp_setMem (s₀ : State) (m : Memory) : hsp (s₀.setMem m) = hsp s₀ := rfl

@[local simp]
private theorem setMem_setMem (s₀ : State) (m₁ m₂ : Memory) :
    (s₀.setMem m₁).setMem m₂ = s₀.setMem m₂ := by
  cases s₀; rfl

abbrev HFrameS2 (okmLen : ℕ) (s₀ : State) (m : Memory) : Prop :=
  S2Frame s₀.mem m [(s₀.readReg64 .x6, okmLen), (hsp s₀ - 720#64, 1408)]

structure HPreBase [LibsignalPlacement] (salt ikm info : List (BitVec 8))
    (saltA ikmA infoA okmA : BitVec 64) (okmLen : ℕ) (s₀ : State) : Prop where
  pre               : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s₀ nfs3PlacedFakeB True
  rw_stk1408        : s₀.mem.RW (hsp s₀ - 720#64) 1408
  disj_iv_stk1408   : DisjointRegions spqrSha256IVAddr 32 (hsp s₀ - 720#64) 1408
  disj_salt_stk1408 : salt.length = 0 ∨ DisjointRegions saltA salt.length (hsp s₀ - 720#64) 1408
  out_salt_stk1408  : ∀ a, InRegion saltA salt.length a → OutsideRegion (hsp s₀ - 720#64) 1408 a
  out_ikm_stk1408   : ∀ a, InRegion ikmA ikm.length a → OutsideRegion (hsp s₀ - 720#64) 1408 a
  out_info_stk1408  : ∀ a, InRegion infoA info.length a → OutsideRegion (hsp s₀ - 720#64) 1408 a
  read_salt         : s₀.mem.Readable saltA salt.length
  read_ikm          : s₀.mem.Readable ikmA ikm.length
  read_info         : s₀.mem.Readable infoA info.length

private theorem s2_readable {m₁ m₂ : Memory} {regs : List (BitVec 64 × ℕ)}
    (hf : S2Frame m₁ m₂ regs) {p : BitVec 64} {n : ℕ} (hrd : m₁.Readable p n) : m₂.Readable p n :=
  fun a ha => let ⟨hr, hlf⟩ := hrd a ha; hf.2.2 a hr hlf

private theorem s2_readBytes_eq_of_readable {m₁ m₂ : Memory} {regs : List (BitVec 64 × ℕ)}
    (hf : S2Frame m₁ m₂ regs) {p : BitVec 64} {n : ℕ} (hn : n ≤ 2 ^ 64) (hrd : m₁.Readable p n)
    (hout : ∀ a, InRegion p n a → ∀ r ∈ regs, OutsideRegion r.1 r.2 a) :
    m₂.readBytes p n = m₁.readBytes p n :=
  Memory.readBytes_congr_region hn fun a ha => let ⟨hr, hlf⟩ := hrd a ha; hf.1 a hr hlf (hout a ha)

private theorem HPreBase.at_mem [LibsignalPlacement] {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ : State}
    (hb : HPreBase salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (m : Memory) (hf : HFrameS2 okmLen s₀ m) :
    HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen (s₀.setMem m) nfs3PlacedFakeB True := by
  have hout_pair {p : BitVec 64} {n : ℕ} (ho_okm : ∀ a, InRegion p n a → OutsideRegion okmA okmLen a)
      (ho_stk : ∀ a, InRegion p n a → OutsideRegion (hsp s₀ - 720#64) 1408 a) :
      ∀ a, InRegion p n a → ∀ r ∈ [(s₀.readReg64 .x6, okmLen), (hsp s₀ - 720#64, 1408)], OutsideRegion r.1 r.2 a := by
    intro a ha r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl; · rw [hb.pre.x6_eq]; exact ho_okm a ha
    · exact ho_stk a ha
  have hiv_read_iv : s₀.mem.Readable spqrSha256IVAddr 32 := by have h := hb.pre.ro_iv_read; rwa [nfs3PlacedFakeB_add_iv] at h
  have hiv_bytes_iv : s₀.mem.readBytes spqrSha256IVAddr 32 = shaStateBytes sha256IV := by
    have h := hb.pre.ro_iv_bytes; rwa [nfs3PlacedFakeB_add_iv] at h
  have hd_iv_okm : DisjointRegions spqrSha256IVAddr 32 okmA okmLen := by have h := hb.pre.disj_iv_okm; rwa [nfs3PlacedFakeB_add_iv] at h
  exact {
    pc_eq := hb.pre.pc_eq, status := hb.pre.status, x0_eq := hb.pre.x0_eq, x1_eq := hb.pre.x1_eq,
    x2_eq := hb.pre.x2_eq, x3_eq := hb.pre.x3_eq, x4_eq := hb.pre.x4_eq, x5_eq := hb.pre.x5_eq,
    x6_eq := hb.pre.x6_eq, x7_eq := hb.pre.x7_eq, salt_lt := hb.pre.salt_lt, ikm_len := hb.pre.ikm_len,
    info_ge := hb.pre.info_ge, info_lt := hb.pre.info_lt, okm_len := hb.pre.okm_len, base_al := trivial,
    ro_iv_bytes := by
      rw [nfs3PlacedFakeB_add_iv]
      exact (s2_readBytes_eq_of_readable hf (by decide) hiv_read_iv
        (hout_pair (fun a ha => hd_iv_okm.symm.outside ha (by decide))
          (fun a ha => hb.disj_iv_stk1408.symm.outside ha (by decide)))).trans hiv_bytes_iv,
    ro_iv_read := fun a ha => let ⟨hr, hlf⟩ := hb.pre.ro_iv_read a ha; hf.2.2 a hr hlf,
    disj_iv_stk := hb.pre.disj_iv_stk, disj_iv_okm := hb.pre.disj_iv_okm,
    salt_bytes := (s2_readBytes_eq_of_readable hf (by have := hb.pre.salt_lt; omega) hb.read_salt (hout_pair hb.pre.out_salt_okm hb.out_salt_stk1408)).trans hb.pre.salt_bytes,
    ikm_bytes := (s2_readBytes_eq_of_readable hf (by have := hb.pre.ikm_len; omega) hb.read_ikm (hout_pair hb.pre.out_ikm_okm hb.out_ikm_stk1408)).trans hb.pre.ikm_bytes,
    info_bytes := (s2_readBytes_eq_of_readable hf (by have := hb.pre.info_lt; omega) hb.read_info (hout_pair hb.pre.out_info_okm hb.out_info_stk1408)).trans hb.pre.info_bytes,
    rw_okm := hf.rw_of_rw okmA okmLen hb.pre.rw_okm, rw_stack := hf.rw_of_rw (hsp s₀ - 544#64) 1232 hb.pre.rw_stack,
    disj_okm_stk := hb.pre.disj_okm_stk, disj_salt_stk := hb.pre.disj_salt_stk,
    out_salt_stk := hb.pre.out_salt_stk, out_salt_okm := hb.pre.out_salt_okm,
    out_ikm_stk := hb.pre.out_ikm_stk, out_ikm_okm := hb.pre.out_ikm_okm,
    out_info_stk := hb.pre.out_info_stk, out_info_okm := hb.pre.out_info_okm, sp_aligned := hb.pre.sp_aligned }

private theorem HPreBase.rw_sub_720 [LibsignalPlacement] {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ : State}
    (hb : HPreBase salt ikm info saltA ikmA infoA okmA okmLen s₀)
    {m_ref m : Memory} (hf_ref : HFrameS2 okmLen s₀ m_ref)
    (hfr : HFrame okmLen (s₀.setMem m_ref) m) :
    m.RW (hsp s₀ - 720#64) 720 :=
  (S2Frame.of_frame hfr).rw_of_rw _ _ (hf_ref.rw_of_rw _ _ (hb.rw_stk1408.sub (by bv_omega)))

private theorem hpre_stripS [LibsignalPlacement] (kp : BitVec 64 → Bool)
    {salt ikm info : List (BitVec 8)} {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s0 : State}
    (hp : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s0 nfs3PlacedFakeB True) :
    HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen (ProofLib.stripS kp s0) nfs3PlacedFakeB True := by
  have hr : ∀ r, (ProofLib.stripS kp s0).readReg64 r = s0.readReg64 r := fun _ => by cases s0; rfl
  have hsp0 : hsp (ProofLib.stripS kp s0) = hsp s0 := by cases s0; rfl
  have hsp_eq : (ProofLib.stripS kp s0).sp = s0.sp := by cases s0; rfl
  exact {
    pc_eq := (by cases s0; rfl : (ProofLib.stripS kp s0).pc = s0.pc).trans hp.pc_eq,
    status := (by cases s0; rfl : (ProofLib.stripS kp s0).status = s0.status).trans hp.status,
    x0_eq := (hr .x0).trans hp.x0_eq, x1_eq := (hr .x1).trans hp.x1_eq, x2_eq := (hr .x2).trans hp.x2_eq,
    x3_eq := (hr .x3).trans hp.x3_eq, x4_eq := (hr .x4).trans hp.x4_eq, x5_eq := (hr .x5).trans hp.x5_eq,
    x6_eq := (hr .x6).trans hp.x6_eq, x7_eq := (hr .x7).trans hp.x7_eq, salt_lt := hp.salt_lt,
    ikm_len := hp.ikm_len, info_ge := hp.info_ge, info_lt := hp.info_lt, okm_len := hp.okm_len, base_al := trivial,
    ro_iv_bytes := by rw [stripS_readBytes]; exact hp.ro_iv_bytes,
    ro_iv_read := by rw [stripS_mem]; exact stripExecOutside_readable kp s0.mem _ _ hp.ro_iv_read,
    disj_iv_stk := by rw [hsp0]; exact hp.disj_iv_stk, disj_iv_okm := hp.disj_iv_okm,
    salt_bytes := by rw [stripS_readBytes]; exact hp.salt_bytes,
    ikm_bytes := by rw [stripS_readBytes]; exact hp.ikm_bytes,
    info_bytes := by rw [stripS_readBytes]; exact hp.info_bytes,
    rw_okm := by rw [stripS_mem]; exact stripExecOutside_rw kp s0.mem _ _ hp.rw_okm,
    rw_stack := by rw [stripS_mem, hsp0]; exact stripExecOutside_rw kp s0.mem _ _ hp.rw_stack,
    disj_okm_stk := by rw [hsp0]; exact hp.disj_okm_stk, disj_salt_stk := by rw [hsp0]; exact hp.disj_salt_stk,
    out_salt_stk := by rw [hsp0]; exact hp.out_salt_stk, out_salt_okm := hp.out_salt_okm,
    out_ikm_stk := by rw [hsp0]; exact hp.out_ikm_stk, out_ikm_okm := hp.out_ikm_okm,
    out_info_stk := by rw [hsp0]; exact hp.out_info_stk, out_info_okm := hp.out_info_okm,
    sp_aligned := by rw [hsp_eq]; exact hp.sp_aligned }

private theorem hframeS2_trans_1232 {okmLen : ℕ} {s₀ : State} {m_ref m : Memory}
    (hf_ref : HFrameS2 okmLen s₀ m_ref)
    (hfr : S2Frame m_ref m [(s₀.readReg64 .x6, okmLen), (hsp s₀ - 544#64, 1232)]) :
    HFrameS2 okmLen s₀ m := by
  refine hf_ref.trans (hfr.mono fun a ha r hr => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ha (s₀.readReg64 .x6, okmLen) (by simp)
  · have hstack := ha (hsp s₀ - 720#64, 1408) (by simp)
    unfold OutsideRegion at hstack ⊢
    bv_omega

private theorem hframeS2_step {okmLen : ℕ} {s₀ : State} {m_ref m : Memory}
    (hf_ref : HFrameS2 okmLen s₀ m_ref) (hfr : HFrame okmLen (s₀.setMem m_ref) m) : HFrameS2 okmLen s₀ m :=
  hframeS2_trans_1232 hf_ref (S2Frame.of_frame hfr)

private theorem hcommon_reset_of_fin [LibsignalPlacement] {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA outOff : BitVec 64} {okmLen : ℕ} {s₀ s s' : State} {m_ref : Memory}
    (hb : HPreBase salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hf_ref : HFrameS2 okmLen s₀ m_ref) (hc : HCommon okmLen (s₀.setMem m_ref) s)
    (hstat' : s'.status = .Running) (hcs : CalleeSaved s s')
    (hfr : S2Frame s.mem s'.mem [(hsp s₀ + outOff, 32), (hsp s₀ + 32#64, 0x90), (hsp s₀ - 320#64, 320)])
    (hout : decide (outOff.toNat + 32 ≤ 592) = true) :
    HFrameS2 okmLen s₀ s'.mem ∧ HCommon okmLen (s₀.setMem s'.mem) s' := by
  have hout' : outOff.toNat + 32 ≤ 592 := of_decide_eq_true hout
  have hrw_hsp : s.mem.RW (hsp s₀) 688 := HFrame.rw_hsp (s₀ := s₀.setMem m_ref) (hb.at_mem m_ref hf_ref) hc.frame
  have hd_saved : ∀ r ∈ [(hsp s₀ + outOff, (32 : ℕ)), (hsp s₀ + 32#64, 0x90), (hsp s₀ - 320#64, 320)],
      DisjointRegions r.1 r.2 (hsp s₀ + 592#64) 96 := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (unfold DisjointRegions; bv_omega)
  have h_saved_eq : ∀ (off : BitVec 64), decide (592 ≤ off.toNat ∧ off.toNat + 8 ≤ 688) = true →
      s'.mem.read64 (hsp s₀ + off) = s.mem.read64 (hsp s₀ + off) := fun off hoff => by
    have ⟨h1, h2⟩ := of_decide_eq_true hoff
    exact hfr.read64_eq (hrw_hsp.sub (by bv_omega)) fun r hr => (hd_saved r hr).sub_right (hsp s₀ + off) ⟨by decide, by bv_omega⟩
  rcases hc.saved with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  refine ⟨(hframeS2_step hf_ref hc.frame).trans (hfr.mono fun a ha r hr => ?_),
    ⟨hstat', hcs.sp_eq.trans hc.sp_eq, (CalleeSaved.x29 hcs).trans hc.x29_eq,
      { m592 := (h_saved_eq 592#64 (by decide)).trans h0, m600 := (h_saved_eq 600#64 (by decide)).trans h1,
        m608 := (h_saved_eq 608#64 (by decide)).trans h2, m616 := (h_saved_eq 616#64 (by decide)).trans h3,
        m624 := (h_saved_eq 624#64 (by decide)).trans h4, m632 := (h_saved_eq 632#64 (by decide)).trans h5,
        m640 := (h_saved_eq 640#64 (by decide)).trans h6, m648 := (h_saved_eq 648#64 (by decide)).trans h7,
        m656 := (h_saved_eq 656#64 (by decide)).trans h8, m664 := (h_saved_eq 664#64 (by decide)).trans h9,
        m672 := (h_saved_eq 672#64 (by decide)).trans h10, m680 := (h_saved_eq 680#64 (by decide)).trans h11 },
      Frame.refl s'.mem _⟩⟩
  have hstack := ha (hsp s₀ - 720#64, 1408) (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> (unfold OutsideRegion at *; bv_omega)

private theorem hexpCommon_reset_of_fin [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {prk salt ikm info : List (BitVec 8)} {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ}
    {s₀ s s' : State} {m_ref : Memory} (hb : HPreBase salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hf_ref : HFrameS2 okmLen s₀ m_ref) (hc : HExpCommon F prk info infoA okmLen (s₀.setMem m_ref) s)
    (hstat' : s'.status = .Running) (hcs : CalleeSaved s s')
    (hfr : S2Frame s.mem s'.mem [(hsp s₀ + 540#64, 32), (hsp s₀ + 32#64, 0x90), (hsp s₀ - 320#64, 320)]) :
    HFrameS2 okmLen s₀ s'.mem ∧ HExpCommon F prk info infoA okmLen (s₀.setMem s'.mem) s' := by
  have hrw_hsp : s.mem.RW (hsp s₀) 688 := HFrame.rw_hsp (s₀ := s₀.setMem m_ref) (hb.at_mem m_ref hf_ref) hc.common.frame
  have hd_low : ∀ r ∈ [(hsp s₀ + 540#64, (32 : ℕ)), (hsp s₀ + 32#64, 0x90), (hsp s₀ - 320#64, 320)],
      DisjointRegions r.1 r.2 (hsp s₀) 32 := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> (unfold DisjointRegions; bv_omega)
  have hd_208 : ∀ r ∈ [(hsp s₀ + 540#64, (32 : ℕ)), (hsp s₀ + 32#64, 0x90), (hsp s₀ - 320#64, 320)],
      DisjointRegions r.1 r.2 (hsp s₀ + 208#64) 0x90 := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> (unfold DisjointRegions; bv_omega)
  rcases hc.hmac_208 with ⟨hlen, _, hpos, hin, hcnt1, hout, hcnt2⟩
  have hhm' : HmacSt s'.mem (hsp s₀ + 208#64) F prk [] := by
    refine ⟨hlen, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨hp, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp ((hrw_hsp.sub (by bv_omega) : s.mem.RW (hsp s₀ + 208#64 + 63#64) 1) (hsp s₀ + 208#64 + 63#64) (by simp [InRegion]))
      exact (hfr.1 (hsp s₀ + 208#64 + 63#64) (by rw [hp]; rfl) hlf fun r hr => (hd_208 r hr).outside (by unfold InRegion; bv_omega) (by decide)).trans hpos
    · exact (hfr.readBytes_eq (hrw_hsp.sub (by bv_omega)) (fun r hr => (hd_208 r hr).sub_right _ ⟨by decide, by bv_omega⟩) (by decide)).trans hin
    · exact (hfr.read64_eq (hrw_hsp.sub (by bv_omega)) (fun r hr => (hd_208 r hr).sub_right _ ⟨by decide, by bv_omega⟩)).trans hcnt1
    · exact (hfr.readBytes_eq (hrw_hsp.sub (by bv_omega)) (fun r hr => (hd_208 r hr).sub_right _ ⟨by decide, by bv_omega⟩) (by decide)).trans hout
    · exact (hfr.read64_eq (hrw_hsp.sub (by bv_omega)) (fun r hr => (hd_208 r hr).sub_right _ ⟨by decide, by bv_omega⟩)).trans hcnt2
  obtain ⟨hf_s', hc'⟩ := hcommon_reset_of_fin (outOff := 540#64) hb hf_ref hc.common hstat' hcs hfr (by decide)
  exact ⟨hf_s', {
    common := hc',
    m0_eq := (hfr.read64_eq (hrw_hsp.sub (by bv_omega)) fun r hr => (hd_low r hr).sub_right (hsp s₀ + 0#64) ⟨by decide, by bv_omega⟩).trans hc.m0_eq,
    m8_eq := (hfr.read64_eq (hrw_hsp.sub (by bv_omega)) fun r hr => (hd_low r hr).sub_right (hsp s₀ + 8#64) ⟨by decide, by bv_omega⟩).trans hc.m8_eq,
    m16_eq := (hfr.read64_eq (hrw_hsp.sub (by bv_omega)) fun r hr => (hd_low r hr).sub_right (hsp s₀ + 16#64) ⟨by decide, by bv_omega⟩).trans hc.m16_eq,
    m24_eq := (hfr.read64_eq (hrw_hsp.sub (by bv_omega)) fun r hr => (hd_low r hr).sub_right (hsp s₀ + 24#64) ⟨by decide, by bv_omega⟩).trans hc.m24_eq,
    hmac_208 := hhm' }⟩

private theorem hcommon_reset_of_nfs [LibsignalPlacement] {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA retOff : BitVec 64} {okmLen : ℕ} {s₀ s s' : State} {m_ref : Memory}
    (hb : HPreBase salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hf_ref : HFrameS2 okmLen s₀ m_ref) (hc : HCommon okmLen (s₀.setMem m_ref) s)
    (hstat' : s'.status = .Running) (hcs : CalleeSaved s s')
    (hfr : S2Frame s.mem s'.mem [(hsp s₀ + retOff, 0x98), (hsp s₀ - 720#64, 720)])
    (hret : decide (retOff.toNat + 0x98 ≤ 592) = true) :
    HFrameS2 okmLen s₀ s'.mem ∧ HCommon okmLen (s₀.setMem s'.mem) s' := by
  have hret' : retOff.toNat + 0x98 ≤ 592 := of_decide_eq_true hret
  have hrw_hsp : s.mem.RW (hsp s₀) 688 := HFrame.rw_hsp (s₀ := s₀.setMem m_ref) (hb.at_mem m_ref hf_ref) hc.frame
  have hd_saved : ∀ r ∈ [(hsp s₀ + retOff, (0x98 : ℕ)), (hsp s₀ - 720#64, 720)],
      DisjointRegions r.1 r.2 (hsp s₀ + 592#64) 96 := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> (unfold DisjointRegions; bv_omega)
  have h_saved_eq : ∀ (off : BitVec 64), decide (592 ≤ off.toNat ∧ off.toNat + 8 ≤ 688) = true →
      s'.mem.read64 (hsp s₀ + off) = s.mem.read64 (hsp s₀ + off) := fun off hoff => by
    have ⟨h1, h2⟩ := of_decide_eq_true hoff
    exact hfr.read64_eq (hrw_hsp.sub (by bv_omega)) fun r hr => (hd_saved r hr).sub_right (hsp s₀ + off) ⟨by decide, by bv_omega⟩
  rcases hc.saved with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  refine ⟨(hframeS2_step hf_ref hc.frame).trans (hfr.mono fun a ha r hr => ?_),
    ⟨hstat', hcs.sp_eq.trans hc.sp_eq, (CalleeSaved.x29 hcs).trans hc.x29_eq,
      { m592 := (h_saved_eq 592#64 (by decide)).trans h0, m600 := (h_saved_eq 600#64 (by decide)).trans h1,
        m608 := (h_saved_eq 608#64 (by decide)).trans h2, m616 := (h_saved_eq 616#64 (by decide)).trans h3,
        m624 := (h_saved_eq 624#64 (by decide)).trans h4, m632 := (h_saved_eq 632#64 (by decide)).trans h5,
        m640 := (h_saved_eq 640#64 (by decide)).trans h6, m648 := (h_saved_eq 648#64 (by decide)).trans h7,
        m656 := (h_saved_eq 656#64 (by decide)).trans h8, m664 := (h_saved_eq 664#64 (by decide)).trans h9,
        m672 := (h_saved_eq 672#64 (by decide)).trans h10, m680 := (h_saved_eq 680#64 (by decide)).trans h11 },
      Frame.refl s'.mem _⟩⟩
  have hstack := ha (hsp s₀ - 720#64, 1408) (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> (unfold OutsideRegion at *; bv_omega)

private theorem fin_extract_vm [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [hH : HkdfPlacedHooksExactSat C.F H] (hMemsetVm : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec)
    {salt ikm info : List (BitVec 8)} {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State} {m_ref : Memory}
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hb : HPreBase salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hf_ref : HFrameS2 okmLen s₀ m_ref)
    (hx : StateEFin hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen (s₀.setMem m_ref) s (blkPl_425).base) :
    RunsToVm ((blkPC_379).rebase (blkPl_379).base H) s fun s' =>
      HFrameS2 okmLen s₀ s'.mem ∧ StateERetFin hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen (s₀.setMem s'.mem) s' := by
  rcases hx.hmac_32 with ⟨pfx, tail, hpt, _hmod, hlt, hhm⟩
  have hpre_ref := hb.at_mem m_ref hf_ref
  have hrw_hsp : s.mem.RW (hsp s₀) 688 := HFrame.rw_hsp (s₀ := s₀.setMem m_ref) hpre_ref hx.common.frame
  have hrw_sub : s.mem.RW (hsp s₀ - 544#64) 544 := HFrame.rw_sub_544 (s₀ := s₀.setMem m_ref) hpre_ref hx.common.frame
  have hfin_pre : FinPre3PfxGenSat fin3PlacedFakeB C.F (effectiveHmacKey C.F salt) pfx tail s :=
    FinPre3PfxGenSat.of_320 hx.pc_eq hx.common.status (effectiveHmacKey_length_le C.F salt) hlt
      (by rw [hx.x1_eq]; exact hhm)
      (by rw [hx.x0_eq, hsp_setMem]; exact hrw_hsp.sub (by bv_omega))
      (by rw [hx.x1_eq, hsp_setMem]; exact hrw_hsp.sub (by bv_omega))
      (by rw [hx.common.sp_eq, hsp_setMem]; exact hrw_sub.sub (by bv_omega))
      (by rw [hx.x0_eq, hx.x1_eq, hsp_setMem]; unfold DisjointRegions; bv_omega)
      (by rw [hx.x0_eq, hx.common.sp_eq, hsp_setMem]; unfold DisjointRegions; bv_omega)
      (by rw [hx.x1_eq, hx.common.sp_eq, hsp_setMem]; unfold DisjointRegions; bv_omega)
      (by rw [hx.common.sp_eq, hsp_setMem]; exact (hsp_aligned hb.pre.sp_aligned).2.1)
  refine (finalize_fixed3_pfx_lt64_kdf_vm_sat (C := C) hMemsetVm hcl hfin_pre).mono fun s' ⟨hpc', hrun', hcs, hout, hfr⟩ => ?_
  rw [hx.lr_eq] at hpc'; rw [hx.x0_eq, hsp_setMem, hpt, hmacWith_effectiveHmacKey] at hout
  rw [hx.x0_eq, hx.x1_eq, hx.common.sp_eq, hsp_setMem] at hfr
  have hm16' : s'.mem.read64 (hsp s₀ + 16#64) = BitVec.ofNat 64 info.length := by
    refine (hfr.read64_eq (hrw_hsp.sub (by bv_omega)) fun r hr => ?_).trans hx.m16_eq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> (unfold DisjointRegions; bv_omega)
  obtain ⟨hf_s', hc'⟩ := hcommon_reset_of_fin (outOff := 507#64) hb hf_ref hx.common hrun' hcs hfr (by decide)
  exact ⟨hf_s', ⟨hpc', hc', (CalleeSaved.x19 hcs).trans hx.x19_eq, (CalleeSaved.x22 hcs).trans hx.x22_eq,
    (CalleeSaved.x25 hcs).trans hx.x25_eq, (CalleeSaved.x26 hcs).trans hx.x26_eq, (CalleeSaved.x27 hcs).trans hx.x27_eq, hm16', hout⟩⟩

private theorem fin_b1_vm [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [hH : HkdfPlacedHooksExactSat C.F H] (hMemsetVm : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec)
    {salt ikm info : List (BitVec 8)} {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State} {m_ref : Memory}
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hb : HPreBase salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hf_ref : HFrameS2 okmLen s₀ m_ref)
    (hx : StateB1Fin hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen (s₀.setMem m_ref) s (blkPl_425).base) :
    RunsToVm ((blkPC_379).rebase (blkPl_379).base H) s fun s' =>
      HFrameS2 okmLen s₀ s'.mem ∧ StateB1RetFin hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen (s₀.setMem s'.mem) s' := by
  have hpre_ref := hb.at_mem m_ref hf_ref
  have hrw_hsp : s.mem.RW (hsp s₀) 688 := HFrame.rw_hsp (s₀ := s₀.setMem m_ref) hpre_ref hx.exp.common.frame
  have hrw_sub : s.mem.RW (hsp s₀ - 544#64) 544 := HFrame.rw_sub_544 (s₀ := s₀.setMem m_ref) hpre_ref hx.exp.common.frame
  have hfin_pre : FinPre3PfxGenSat fin3PlacedFakeB C.F (hkdfExtractBytes C.F salt ikm) [] (info ++ [1#8]) s :=
    FinPre3PfxGenSat.of_320 hx.pc_eq hx.exp.common.status
      (by rw [hkdfExtractBytes, length_hmacWith]; decide)
      (by have := hb.pre.info_lt; simp; omega)
      (HmacStN.of_hmacSt (by rw [hx.x1_eq]; exact hx.hmac_32))
      (by rw [hx.x0_eq, hsp_setMem]; exact hrw_hsp.sub (by bv_omega))
      (by rw [hx.x1_eq, hsp_setMem]; exact hrw_hsp.sub (by bv_omega))
      (by rw [hx.exp.common.sp_eq, hsp_setMem]; exact hrw_sub.sub (by bv_omega))
      (by rw [hx.x0_eq, hx.x1_eq, hsp_setMem]; unfold DisjointRegions; bv_omega)
      (by rw [hx.x0_eq, hx.exp.common.sp_eq, hsp_setMem]; unfold DisjointRegions; bv_omega)
      (by rw [hx.x1_eq, hx.exp.common.sp_eq, hsp_setMem]; unfold DisjointRegions; bv_omega)
      (by rw [hx.exp.common.sp_eq, hsp_setMem]; exact (hsp_aligned hb.pre.sp_aligned).2.1)
  refine (finalize_fixed3_pfx_lt64_kdf_vm_sat (C := C) hMemsetVm hcl hfin_pre).mono fun s' ⟨hpc', hrun', hcs, ht1, hfr⟩ => ?_
  simp only [List.nil_append] at ht1; rw [hx.lr_eq] at hpc'; rw [hx.x0_eq, hsp_setMem] at ht1
  rw [hx.x0_eq, hx.x1_eq, hx.exp.common.sp_eq, hsp_setMem] at hfr
  obtain ⟨hf_s', hexp'⟩ := hexpCommon_reset_of_fin hb hf_ref hx.exp hrun' hcs hfr
  exact ⟨hf_s', ⟨hpc', hexp', (CalleeSaved.x21 hcs).trans hx.x21_eq, (CalleeSaved.x22 hcs).trans hx.x22_eq,
    (CalleeSaved.x24 hcs).trans hx.x24_eq, (CalleeSaved.x25 hcs).trans hx.x25_eq,
    (CalleeSaved.x26 hcs).trans hx.x26_eq, (CalleeSaved.x28 hcs).trans hx.x28_eq, ht1⟩⟩

private theorem iter_fin_vm [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [hH : HkdfPlacedHooksExactSat C.F H] (hMemsetVm : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec)
    {salt ikm info tPrev okmSoFar : List (BitVec 8)} {saltA ikmA infoA okmA : BitVec 64}
    {okmLen i rem dstOff : ℕ} {s₀ s : State} {m_ref : Memory}
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hb : HPreBase salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hf_ref : HFrameS2 okmLen s₀ m_ref) (hdst : dstOff ≤ okmLen)
    (hx : StateLoopC hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff (s₀.setMem m_ref) s (blkPl_425).base) :
    RunsToVm ((blkPC_379).rebase (blkPl_379).base H) s fun s' =>
      HFrameS2 okmLen s₀ s'.mem ∧
      StateLoopFin hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff (s₀.setMem s'.mem) s' := by
  have hpre_ref := hb.at_mem m_ref hf_ref
  have hrw_hsp : s.mem.RW (hsp s₀) 688 := HFrame.rw_hsp (s₀ := s₀.setMem m_ref) hpre_ref hx.exp.common.frame
  have hrw_sub : s.mem.RW (hsp s₀ - 544#64) 544 := HFrame.rw_sub_544 (s₀ := s₀.setMem m_ref) hpre_ref hx.exp.common.frame
  have hrw_okm : s.mem.RW okmA okmLen := HFrame.rw_okm hpre_ref hx.exp.common.frame
  have hfin_pre : FinPre3PfxGenSat fin3PlacedFakeB C.F (hkdfExtractBytes C.F salt ikm)
      (tPrev ++ info.take 32) (info.drop 32 ++ [BitVec.ofNat 8 (i + 1)]) s :=
    FinPre3PfxGenSat.of_320 hx.pc_eq hx.exp.common.status
      (by rw [hkdfExtractBytes, length_hmacWith]; decide)
      (by have := hb.pre.info_lt; simp; omega)
      (by rw [hx.x1_eq]; exact hx.hmac_32)
      (by rw [hx.x0_eq, hsp_setMem]; exact hrw_hsp.sub (by bv_omega))
      (by rw [hx.x1_eq, hsp_setMem]; exact hrw_hsp.sub (by bv_omega))
      (by rw [hx.exp.common.sp_eq, hsp_setMem]; exact hrw_sub.sub (by bv_omega))
      (by rw [hx.x0_eq, hx.x1_eq, hsp_setMem]; unfold DisjointRegions; bv_omega)
      (by rw [hx.x0_eq, hx.exp.common.sp_eq, hsp_setMem]; unfold DisjointRegions; bv_omega)
      (by rw [hx.x1_eq, hx.exp.common.sp_eq, hsp_setMem]; unfold DisjointRegions; bv_omega)
      (by rw [hx.exp.common.sp_eq, hsp_setMem]; exact (hsp_aligned hb.pre.sp_aligned).2.1)
  refine (finalize_fixed3_pfx_lt64_kdf_vm_sat (C := C) hMemsetVm hcl hfin_pre).mono fun s' ⟨hpc', hrun', hcs, hout, hfr⟩ => ?_
  rw [hx.lr_eq] at hpc'; rw [hx.x0_eq, hsp_setMem] at hout; rw [hx.x0_eq, hx.x1_eq, hx.exp.common.sp_eq, hsp_setMem] at hfr
  have hmsg_eq : (tPrev ++ info.take 32) ++ (info.drop 32 ++ [BitVec.ofNat 8 (i + 1)]) =
      tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)] := by
    rw [List.append_assoc tPrev (info.take 32), ← List.append_assoc (info.take 32), List.take_append_drop, ← List.append_assoc]
  rw [hmsg_eq] at hout
  have hokm' : s'.mem.readBytes okmA dstOff = okmSoFar := by
    by_cases h0 : dstOff = 0; · subst h0; exact hx.okm_pre
    · have hokm_len := hb.pre.okm_len
      refine (hfr.readBytes_eq (hrw_okm.sub (by bv_omega)) (fun r hr => ?_) (by omega)).trans hx.okm_pre
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> dsimp only
      · exact (hb.pre.disj_okm_stk.symm.sub_left (hsp s₀ + 540#64) ⟨by decide, by bv_omega⟩).sub_right okmA ⟨by omega, by bv_omega⟩
      · exact (hb.pre.disj_okm_stk.symm.sub_left (hsp s₀ + 32#64) ⟨by decide, by bv_omega⟩).sub_right okmA ⟨by omega, by bv_omega⟩
      · exact (hb.pre.disj_okm_stk.symm.sub_left (hsp s₀ - 320#64) ⟨by decide, by bv_omega⟩).sub_right okmA ⟨by omega, by bv_omega⟩
  obtain ⟨hf_s', hexp'⟩ := hexpCommon_reset_of_fin hb hf_ref hx.exp hrun' hcs hfr
  exact ⟨hf_s', ⟨hpc', hexp', (CalleeSaved.x20 hcs).trans hx.x20_eq, (CalleeSaved.x21 hcs).trans hx.x21_eq,
    (CalleeSaved.x22 hcs).trans hx.x22_eq, (CalleeSaved.x24 hcs).trans hx.x24_eq, (CalleeSaved.x25 hcs).trans hx.x25_eq,
    (CalleeSaved.x26 hcs).trans hx.x26_eq, (CalleeSaved.x27 hcs).trans hx.x27_eq, (CalleeSaved.x28 hcs).trans hx.x28_eq, hout, hokm'⟩⟩

private theorem hsaved_setMem {s₀ : State} {m1 m2 m : Memory}
    (h : HSaved (s₀.setMem m1) m) : HSaved (s₀.setMem m2) m := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩; exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩


theorem hkdf_to_slice_kdf_vm_sat [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [hH : HkdfPlacedHooksExactSat C.F H]
    (hMemsetVm : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec)
    {salt ikm info : List (BitVec 8)} {saltA ikmA infoA okmA : BitVec 64}
    {okmLen : ℕ} {s₀ : State} (hcl₀ : LibsignalCodeLoaded lsmpl s₀.mem)
    (hb : HPreBase salt ikm info saltA ikmA infoA okmA okmLen s₀) :
    RunsToVm ((blkPC_379).rebase (blkPl_379).base H) s₀ fun sf =>
      sf.pc = s₀.readReg64 .lr ∧ sf.status = .Running ∧ CalleeSaved s₀ sf ∧
      sf.mem.readBytes okmA okmLen = hkdfExpand C.F (hkdfExtractBytes C.F salt ikm) info okmLen ∧
      HFrameS2 okmLen s₀ sf.mem := by
  have heq379 : ∀ X, (blkPC_379).rebase (blkPl_379).base X = libsignalSessionLib.blockProgram lsmpl 379 X :=
    fun X => IsLsBlockProg.eq_blockProgram (prog := (blkPC_379).rebase (blkPl_379).base X)
  have runsTo_rebase_of_block379 : ∀ {X : LibsignalHooks} {s : State} {P : State → Prop},
      RunsTo ((blkPC_379).rebase (blkPl_379).base X) s P → RunsTo (libsignalSessionLib.blockProgram lsmpl 379 X) s P :=
    fun {X} _ _ h => heq379 X ▸ h
  let kp379 := ProofLib.progKeep (libsignalSessionLib.blockProgram lsmpl 379 H)
  have hkpQ (m : Memory) :
      ProofLib.progKeep (libsignalSessionLib.blockProgram lsmpl 379 (hmacNoMemsetExcHooksSat C.F H m kp379)) = kp379 := rfl
  let hmcQ (m : Memory) := hmacNoMemsetExcHooksSat_memcpy (F := C.F) hH.memcpy m kp379
  let hc256Q (m : Memory) := hmacNoMemsetExcHooksSat_compress hH.compress256 m kp379
  have hsp0_of (m : Memory) : hsp (ProofLib.stripS kp379 (s₀.setMem m)) = hsp s₀ := by cases s₀; rfl
  have hr6_of (m : Memory) : (ProofLib.stripS kp379 (s₀.setMem m)).readReg64 .x6 = s₀.readReg64 .x6 := by cases s₀; rfl
  have hset_strip (m1 : Memory) (sf : State) :
      (ProofLib.stripS kp379 (s₀.setMem m1)).setMem (ProofLib.stripS kp379 sf).mem =
        ProofLib.stripS kp379 (s₀.setMem sf.mem) := by cases s₀; cases sf; rfl
  have hs_id : s₀.setMem s₀.mem = s₀ := by cases s₀; rfl
  have hf₀ : HFrameS2 okmLen s₀ s₀.mem := S2Frame.refl s₀.mem _
  have hc0 : RunsToVm ((blkPC_379).rebase (blkPl_379).base H) s₀
      (StateENfs1 hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen (s₀.setMem s₀.mem) · (blkPl_402).base) := by
    rw [hs_id]
    refine lift_block_to_379_vm (C := C) (Pj := (blkPC_379).rebase (blkPl_379).base H) blkLib_eq_379 blk379_noSvc0 blk379_noMsr (by decide) (by decide) hcl₀
      (heq379 H ▸ seg_e0_placed_runsTo hb.pre)
      (heq379 (hmacNoMemsetExcHooksSat C.F H s₀.mem kp379) ▸ seg_e0_placed_runsTo (hpre_stripS kp379 hb.pre))
      (fun _ hs => hs.common.status) (fun _ hs => hs.common.status)
      fun sf hvm ⟨hpc, hc, hlr, hx0, hx1, hx2, hx22, hx23, hx24, hx25, hx26, hx27⟩ =>
        ⟨(by cases sf; exact hpc), unstrip_hcommon hc hvm.perm_eq, (by cases sf; exact hlr),
          (by cases s₀; cases sf; exact hx0), (by cases sf; exact hx1), (by cases sf; exact hx2),
          (by cases sf; exact hx22), (by cases sf; exact hx23), (by cases sf; exact hx24),
          (by cases sf; exact hx25), (by cases sf; exact hx26), (by cases sf; exact hx27)⟩
  have hext1 : RunsToVm ((blkPC_379).rebase (blkPl_379).base H) s₀ fun s =>
      HFrameS2 okmLen s₀ s.mem ∧ StateERetFin hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen (s₀.setMem s.mem) s := by
    refine hc0.trans_full fun s_n1 hn1 hkf1 => ?_
    have hcl_n1 := hcl₀.of_keepsFrozen hkf1; have hpre1 := hb.at_mem s₀.mem hf₀
    have hx2_nat : (s_n1.readReg64 .x2).toNat = salt.length := by
      rw [hn1.x2_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hb.pre.salt_lt; omega)]
    have hrw_hsp1 : s_n1.mem.RW (hsp s₀) 688 := HFrame.rw_hsp (s₀ := s₀.setMem s₀.mem) hpre1 hn1.common.frame
    have hnfs1 : RunsToVm ((blkPC_379).rebase (blkPl_379).base H) s_n1 fun sr1 =>
        HFrameS2 okmLen s₀ sr1.mem ∧ StateERet1 hkdfCodeFakeB C.F salt ikm info ikmA infoA okmA okmLen (s₀.setMem sr1.mem) sr1 :=
      (nfs_gen_vm (C := C) hMemsetVm hcl_n1 hn1.pc_eq hn1.common.status
        (by rw [hx2_nat]; exact hb.pre.salt_lt)
        (by rw [← nfs3PlacedFakeB_add_iv]; exact HFrame.ro_iv_bytes hpre1 hn1.common.frame)
        (by rw [← nfs3PlacedFakeB_add_iv]; exact HFrame.ro_iv_read hpre1 hn1.common.frame)
        (by rw [hn1.common.sp_eq, hsp_setMem]; exact hb.disj_iv_stk1408.sub_right (hsp s₀ - 720#64) ⟨by decide, by bv_omega⟩)
        (by rw [hn1.x0_eq, hsp_setMem]; exact hrw_hsp1.sub (by bv_omega))
        (by rw [hn1.common.sp_eq, hsp_setMem]; exact hb.rw_sub_720 hf₀ hn1.common.frame)
        (by rw [hn1.x0_eq, hn1.common.sp_eq, hsp_setMem]; unfold DisjointRegions; bv_omega)
        (by rw [hn1.x1_eq, hx2_nat]; exact (hn1.common.frame.readable_iff _ _).mpr hb.read_salt)
        (by rw [hn1.x1_eq, hx2_nat, hn1.common.sp_eq, hsp_setMem]
            exact hb.disj_salt_stk1408.imp id fun hd => hd.sub_right (hsp s₀ - 720#64) ⟨by decide, by bv_omega⟩)
        (by rw [hn1.common.sp_eq, hsp_setMem]; exact (hsp_aligned hb.pre.sp_aligned).2.1)).mono
        fun sr1 ⟨hpc', hrun', hcs', htag', hhm', hfr'⟩ => by
          rw [hn1.lr_eq] at hpc'; rw [hn1.x0_eq, hsp_setMem] at htag'
          have hx0_8 : s_n1.readReg64 .x0 + 8#64 = hsp s₀ + 40#64 := by rw [hn1.x0_eq, hsp_setMem]; bv_lin
          have hsalt_s : s_n1.mem.readBytes (s_n1.readReg64 .x1) (s_n1.readReg64 .x2).toNat = salt := by
            rw [hn1.x1_eq, hx2_nat]; exact HFrame.salt_bytes hpre1 hn1.common.frame
          rw [hx0_8, hsalt_s] at hhm'; rw [hn1.x0_eq, hn1.common.sp_eq, hsp_setMem] at hfr'
          obtain ⟨hf_r1, hc_r1⟩ := hcommon_reset_of_nfs (retOff := 32#64) hb hf₀ hn1.common hrun' hcs' hfr' (by decide)
          exact ⟨hf_r1, ⟨hpc', hc_r1,
            (CalleeSaved.x22 hcs').trans hn1.x22_eq, (CalleeSaved.x23 hcs').trans hn1.x23_eq,
            (CalleeSaved.x24 hcs').trans hn1.x24_eq, (CalleeSaved.x25 hcs').trans hn1.x25_eq,
            (CalleeSaved.x26 hcs').trans hn1.x26_eq, (CalleeSaved.x27 hcs').trans hn1.x27_eq, htag', hhm'⟩⟩
    refine hnfs1.trans_full fun sr1 ⟨hf_r1, hsr1_ref⟩ hkf_r1 => ?_
    have hcl_r1 := hcl_n1.of_keepsFrozen hkf_r1; have hc_r1 := hsr1_ref.common; have hsr1 := hsr1_ref
    have hsr1_strip : StateERet1 hkdfCodeFakeB C.F salt ikm info ikmA infoA okmA okmLen
        (ProofLib.stripS kp379 (s₀.setMem sr1.mem)) (ProofLib.stripS kp379 sr1) :=
      ⟨(by cases sr1; exact hsr1.pc_eq), stripS_hcommon_refl kp379 hc_r1, (by cases sr1; exact hsr1.x22_eq),
        (by cases sr1; exact hsr1.x23_eq), (by cases sr1; exact hsr1.x24_eq), (by cases sr1; exact hsr1.x25_eq),
        (by cases sr1; exact hsr1.x26_eq), (by cases sr1; exact hsr1.x27_eq),
        by rw [hsp0_of, stripS_read64]; exact hsr1.tag_32, by rw [hsp0_of, stripS_hmacSt]; exact hsr1.hmac_40⟩
    have hpre_r1 := hb.at_mem sr1.mem hf_r1; have hread_ikm_r1 := s2_readable hf_r1 hb.read_ikm
    have hread_ikm_r1_s : (ProofLib.stripS kp379 (s₀.setMem sr1.mem)).mem.Readable ikmA ikm.length :=
      stripExecOutside_readable kp379 sr1.mem _ _ hread_ikm_r1
    have hc1a : RunsToVm ((blkPC_379).rebase (blkPl_379).base H) sr1 fun s2 =>
        S2Frame sr1.mem s2.mem [(s₀.readReg64 .x6, okmLen), (hsp s₀ - 544#64, 1232)] ∧
        StateE3cc hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen (s₀.setMem s2.mem) s2 := by
      refine lift_block_to_379_vm (C := C) (Pj := (blkPC_379).rebase (blkPl_379).base H) blkLib_eq_379 blk379_noSvc0 blk379_noMsr (by decide) (by decide) hcl_r1
        (heq379 H ▸ (seg_e1_placed_runsTo_exact hH.memcpy hH.compress256 hpre_r1 hread_ikm_r1 hsr1_ref).mono
          fun s2 ⟨hfr2, hs2⟩ => ⟨hfr2, by simpa only [setMem_setMem] using hs2⟩)
        (heq379 (hmacNoMemsetExcHooksSat C.F H sr1.mem kp379) ▸
          seg_e1_placed_runsTo_exact (hmcQ sr1.mem) (hc256Q sr1.mem) (hpre_stripS kp379 hpre_r1) hread_ikm_r1_s hsr1_strip)
        (fun _ hs => hs.2.common.status) (fun _ hs => hs.2.common.status)
        fun sf hvm ⟨hfr_q, hs2_q⟩ => ?_
      have hm_sr1 : (ProofLib.stripS kp379 (s₀.setMem sr1.mem)).mem = ProofLib.stripExecOutside kp379 sr1.mem := by cases s₀; rfl
      rw [hkpQ sr1.mem] at hfr_q hs2_q
      rw [hm_sr1, stripS_mem, hr6_of, hsp0_of] at hfr_q
      rw [hset_strip sr1.mem sf] at hs2_q
      rcases hs2_q with ⟨hpc, hc, hx19, hx22, hx25, hx26, hx27, hm16, ⟨pfx, tail, hpt, hmod, hlt, hhm⟩⟩
      rw [hsp0_of, stripS_read64] at hm16; rw [hsp0_of, stripS_hmacStN] at hhm
      exact ⟨unstrip_s2Frame hfr_q hvm.perm_eq,
        ⟨(by cases sf; exact hpc), unstrip_hcommon hc (fun _ => by cases s₀; rfl),
          (by cases s₀; cases sf; exact hx19), (by cases sf; exact hx22),
          (by cases sf; exact hx25), (by cases sf; exact hx26), (by cases sf; exact hx27),
          by simpa [hsp_setMem] using hm16, ⟨pfx, tail, hpt, hmod, hlt, by simpa [hsp_setMem] using hhm⟩⟩⟩
    refine hc1a.trans_full fun s2 ⟨hs2_fr, hs2⟩ hkf_s2 => ?_
    have hcl_s2 := hcl_r1.of_keepsFrozen hkf_s2
    have hf_s2 : HFrameS2 okmLen s₀ s2.mem := hframeS2_trans_1232 hf_r1 hs2_fr
    have hpre_s2 := hb.at_mem s2.mem hf_s2
    have hs2_strip : StateE3cc hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen
        (ProofLib.stripS kp379 (s₀.setMem s2.mem)) (ProofLib.stripS kp379 s2) := by
      rcases hs2 with ⟨hpc, hc, hx19, hx22, hx25, hx26, hx27, hm16, ⟨pfx, tail, hpt, hmod, hlt, hhm⟩⟩
      exact ⟨(by cases s2; exact hpc), stripS_hcommon_refl kp379 hc,
        (by cases s₀; cases s2; exact hx19), (by cases s2; exact hx22),
        (by cases s2; exact hx25), (by cases s2; exact hx26), (by cases s2; exact hx27),
        by rw [hsp0_of, stripS_read64]; simpa [hsp_setMem] using hm16,
        ⟨pfx, tail, hpt, hmod, hlt, by rw [hsp0_of, stripS_hmacStN]; simpa [hsp_setMem] using hhm⟩⟩
    have hc1b : RunsToVm ((blkPC_379).rebase (blkPl_379).base H) s2
        (StateEFin hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen (s₀.setMem s2.mem) · (blkPl_425).base) := by
      refine lift_block_to_379_vm (C := C) (Pj := (blkPC_379).rebase (blkPl_379).base H) blkLib_eq_379 blk379_noSvc0 blk379_noMsr (by decide) (by decide) hcl_s2
        (heq379 H ▸ seg_e1d_placed_runsTo hpre_s2 hs2)
        (heq379 (hmacNoMemsetExcHooksSat C.F H s2.mem kp379) ▸ seg_e1d_placed_runsTo (hpre_stripS kp379 hpre_s2) hs2_strip)
        (fun _ hs => hs.common.status) (fun _ hs => hs.common.status)
        fun sf hvm ⟨hpc, hc, hlr, hx0, hx1, hx19, hx22, hx25, hx26, hx27, hm16, ⟨pfx, tail, hpt, hmod, hlt, hhm⟩⟩ => ?_
      rw [hsp0_of, stripS_read64] at hm16; rw [hsp0_of, stripS_hmacStN] at hhm
      exact ⟨(by cases sf; exact hpc), unstrip_hcommon hc hvm.perm_eq, (by cases sf; exact hlr), (by cases s₀; cases sf; exact hx0),
        (by cases s₀; cases sf; exact hx1), (by cases s₀; cases sf; exact hx19), (by cases sf; exact hx22),
        (by cases sf; exact hx25), (by cases sf; exact hx26), (by cases sf; exact hx27), hm16, ⟨pfx, tail, hpt, hmod, hlt, hhm⟩⟩
    exact hc1b.trans_full fun s_ef hef hkf_ef => fin_extract_vm hMemsetVm (hcl_s2.of_keepsFrozen hkf_ef) hb hf_s2 hef
  have hb1_ret : RunsToVm ((blkPC_379).rebase (blkPl_379).base H) s₀ fun s =>
      HFrameS2 okmLen s₀ s.mem ∧ StateB1RetFin hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen (s₀.setMem s.mem) s := by
    refine hext1.trans_full fun s_rf ⟨hf_rf, hs_rf⟩ hkf_rf => ?_
    have hcl_rf := hcl₀.of_keepsFrozen hkf_rf; have hpre_rf := hb.at_mem s_rf.mem hf_rf
    have hs_rf_strip : StateERetFin hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen (ProofLib.stripS kp379 (s₀.setMem s_rf.mem)) (ProofLib.stripS kp379 s_rf) :=
      ⟨(by cases s_rf; exact hs_rf.pc_eq), stripS_hcommon_refl kp379 hs_rf.common, (by cases s₀; cases s_rf; exact hs_rf.x19_eq),
        (by cases s_rf; exact hs_rf.x22_eq), (by cases s_rf; exact hs_rf.x25_eq), (by cases s_rf; exact hs_rf.x26_eq), (by cases s_rf; exact hs_rf.x27_eq),
        by rw [hsp0_of, stripS_read64]; exact hs_rf.m16_eq, by rw [hsp0_of, stripS_readBytes]; exact hs_rf.prk_507⟩
    have hc2 : RunsToVm ((blkPC_379).rebase (blkPl_379).base H) s_rf
        (StateENfs2 hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen (s₀.setMem s_rf.mem) · (blkPl_402).base) := by
      refine lift_block_to_379_vm (C := C) (Pj := (blkPC_379).rebase (blkPl_379).base H) blkLib_eq_379 blk379_noSvc0 blk379_noMsr (by decide) (by decide) hcl_rf
        (heq379 H ▸ seg_e2_placed_runsTo hpre_rf hs_rf)
        (heq379 (hmacNoMemsetExcHooksSat C.F H s_rf.mem kp379) ▸ seg_e2_placed_runsTo (hpre_stripS kp379 hpre_rf) hs_rf_strip)
        (fun _ hs => hs.common.status) (fun _ hs => hs.common.status)
        fun sf hvm ⟨hpc, hc, hlr, hx0, hx1, hx2, hx19, hx22, hx25, hx26, hx27, hm16, hprk⟩ => ?_
      rw [hsp0_of, stripS_read64] at hm16; rw [hsp0_of, stripS_readBytes] at hprk
      exact ⟨(by cases sf; exact hpc), unstrip_hcommon hc hvm.perm_eq, (by cases sf; exact hlr), (by cases s₀; cases sf; exact hx0),
        (by cases s₀; cases sf; exact hx1), (by cases sf; exact hx2), (by cases s₀; cases sf; exact hx19),
        (by cases sf; exact hx22), (by cases sf; exact hx25), (by cases sf; exact hx26), (by cases sf; exact hx27), hm16, hprk⟩
    refine hc2.trans_full fun s_n2 hn2 hkf_n2 => ?_
    have hcl_n2 := hcl_rf.of_keepsFrozen hkf_n2; have hx2_nat : (s_n2.readReg64 .x2).toNat = 32 := by rw [hn2.x2_eq]; rfl
    have hrw_hsp2 : s_n2.mem.RW (hsp s₀) 688 := HFrame.rw_hsp (s₀ := s₀.setMem s_rf.mem) hpre_rf hn2.common.frame
    have hnfs2 : RunsToVm ((blkPC_379).rebase (blkPl_379).base H) s_n2 fun sr2 =>
        HFrameS2 okmLen s₀ sr2.mem ∧ StateERet2 hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen (s₀.setMem sr2.mem) sr2 :=
      (nfs_le64_vm (C := C) (H := H) hcl_n2 hn2.pc_eq hn2.common.status (by rw [hx2_nat]; decide)
        (by rw [← nfs3PlacedFakeB_add_iv]; exact HFrame.ro_iv_bytes hpre_rf hn2.common.frame)
        (by rw [← nfs3PlacedFakeB_add_iv]; exact HFrame.ro_iv_read hpre_rf hn2.common.frame)
        (by rw [hn2.common.sp_eq, hsp_setMem]; exact hb.disj_iv_stk1408.sub_right (hsp s₀ - 720#64) ⟨by decide, by bv_omega⟩)
        (by rw [hn2.x0_eq, hsp_setMem]; exact hrw_hsp2.sub (by bv_omega))
        (by rw [hn2.common.sp_eq, hsp_setMem]; exact hb.rw_sub_720 hf_rf hn2.common.frame)
        (by rw [hn2.x0_eq, hn2.common.sp_eq, hsp_setMem]; unfold DisjointRegions; bv_omega)
        (by rw [hn2.x1_eq, hx2_nat, hsp_setMem]; exact readable_of_rw (hrw_hsp2.sub (by bv_omega)))
        (by rw [hn2.x1_eq, hx2_nat, hn2.common.sp_eq, hsp_setMem]; exact Or.inr (by unfold DisjointRegions; bv_omega))
        (by rw [hn2.common.sp_eq, hsp_setMem]; exact (hsp_aligned hb.pre.sp_aligned).2.1)).mono
        fun sr2 ⟨hpc', hrun', hcs', htag', hhm', hfr'⟩ => by
          rw [hn2.lr_eq] at hpc'; rw [hn2.x0_eq, hsp_setMem] at htag'
          have hx0_8 : s_n2.readReg64 .x0 + 8#64 = hsp s₀ + 360#64 := by rw [hn2.x0_eq, hsp_setMem]; bv_lin
          have hprk_s : s_n2.mem.readBytes (s_n2.readReg64 .x1) (s_n2.readReg64 .x2).toNat = hkdfExtractBytes C.F salt ikm := by
            rw [hn2.x1_eq, hx2_nat]; exact hn2.prk_507
          rw [hx0_8, hprk_s] at hhm'; rw [hn2.x0_eq, hn2.common.sp_eq, hsp_setMem] at hfr'
          have hm16' : sr2.mem.read64 (hsp s₀ + 16#64) = BitVec.ofNat 64 info.length := by
            refine (hfr'.read64_eq (hrw_hsp2.sub (by bv_omega)) fun r hr => ?_).trans hn2.m16_eq
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl <;> (unfold DisjointRegions; bv_omega)
          obtain ⟨hf_r2, hc_r2⟩ := hcommon_reset_of_nfs (retOff := 352#64) hb hf_rf hn2.common hrun' hcs' hfr' (by decide)
          exact ⟨hf_r2, ⟨hpc', hc_r2,
            (CalleeSaved.x19 hcs').trans hn2.x19_eq, (CalleeSaved.x22 hcs').trans hn2.x22_eq,
            (CalleeSaved.x25 hcs').trans hn2.x25_eq, (CalleeSaved.x26 hcs').trans hn2.x26_eq,
            (CalleeSaved.x27 hcs').trans hn2.x27_eq, hm16', htag', hhm'⟩⟩
    refine hnfs2.trans_full fun sr2 ⟨hf_r2, hsr2_ref⟩ hkf_r2 => ?_
    have hcl_r2 := hcl_n2.of_keepsFrozen hkf_r2; have hc_r2 := hsr2_ref.common; have hsr2 := hsr2_ref
    have hsr2_strip : StateERet2 hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen (ProofLib.stripS kp379 (s₀.setMem sr2.mem)) (ProofLib.stripS kp379 sr2) :=
      ⟨(by cases sr2; exact hsr2.pc_eq), stripS_hcommon_refl kp379 hc_r2, (by cases s₀; cases sr2; exact hsr2.x19_eq),
        (by cases sr2; exact hsr2.x22_eq), (by cases sr2; exact hsr2.x25_eq), (by cases sr2; exact hsr2.x26_eq), (by cases sr2; exact hsr2.x27_eq),
        by rw [hsp0_of, stripS_read64]; exact hsr2.m16_eq, by rw [hsp0_of, stripS_read64]; exact hsr2.tag_352, by rw [hsp0_of, stripS_hmacSt]; exact hsr2.hmac_360⟩
    have hpre_r2 := hb.at_mem sr2.mem hf_r2; have hread_info_r2 := s2_readable hf_r2 hb.read_info
    have hread_info_r2_s : (ProofLib.stripS kp379 (s₀.setMem sr2.mem)).mem.Readable infoA info.length :=
      stripExecOutside_readable kp379 sr2.mem _ _ hread_info_r2
    have hc3 : RunsToVm ((blkPC_379).rebase (blkPl_379).base H) sr2
        (StateB1Fin hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen (s₀.setMem sr2.mem) · (blkPl_425).base) := by
      refine lift_block_to_379_vm (C := C) (Pj := (blkPC_379).rebase (blkPl_379).base H) blkLib_eq_379 blk379_noSvc0 blk379_noMsr (by decide) (by decide) hcl_r2
        (heq379 H ▸ (seg_e3_placed_runsTo hpre_r2 hsr2_ref).trans fun _ hs0 =>
          (seg_b1a_placed_runsTo hpre_r2 hs0).trans fun _ hs1 => seg_b1b_placed_runsTo_exact hH.memcpy hpre_r2 hread_info_r2 hs1)
        (heq379 (hmacNoMemsetExcHooksSat C.F H sr2.mem kp379) ▸
          (seg_e3_placed_runsTo (hpre_stripS kp379 hpre_r2) hsr2_strip).trans fun _ hs0 =>
          (seg_b1a_placed_runsTo (hpre_stripS kp379 hpre_r2) hs0).trans fun _ hs1 =>
          seg_b1b_placed_runsTo_exact (hmcQ sr2.mem) (hpre_stripS kp379 hpre_r2) hread_info_r2_s hs1)
        (fun _ hs => hs.exp.common.status) (fun _ hs => hs.exp.common.status)
        fun sf hvm ⟨hpc, hexp, hlr, hx0, hx1, hx21, hx22, hx24, hx25, hx26, hx28, hhm⟩ => ?_
      rw [hsp0_of, stripS_hmacSt] at hhm
      exact ⟨(by cases sf; exact hpc), unstrip_hexpCommon hexp hvm.perm_eq, (by cases sf; exact hlr),
        (by cases s₀; cases sf; exact hx0), (by cases s₀; cases sf; exact hx1), (by cases sf; exact hx21),
        (by cases sf; exact hx22), (by cases sf; exact hx24), (by cases sf; exact hx25),
        (by cases sf; exact hx26), (by cases s₀; cases sf; exact hx28), hhm⟩
    exact hc3.trans_full fun s_bf hbf hkf_bf => fin_b1_vm hMemsetVm (hcl_r2.of_keepsFrozen hkf_bf) hb hf_r2 hbf
  have hiter_vm : ∀ {tPrev okmSoFar : List (BitVec 8)} {i rem dstOff : ℕ} {s : State},
      LibsignalCodeLoaded lsmpl s.mem → HFrameS2 okmLen s₀ s.mem →
      tPrev.length = 32 → (i = 1 ∨ i = 2) → (rem = 32 ∨ rem = 64) → dstOff + 32 ≤ okmLen →
      StateLoop hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff (s₀.setMem s.mem) s →
      RunsToVm ((blkPC_379).rebase (blkPl_379).base H) s fun s' =>
        HFrameS2 okmLen s₀ s'.mem ∧ StateLoopFin hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff (s₀.setMem s'.mem) s' := by
    intro tPrev okmSoFar i rem dstOff s hcl_s hf_s ht_len hi hrem hdst hl
    have hpre_s := hb.at_mem s.mem hf_s; have hread_info_s := s2_readable hf_s hb.read_info
    have hread_info_s_q : (ProofLib.stripS kp379 (s₀.setMem s.mem)).mem.Readable infoA info.length :=
      stripExecOutside_readable kp379 s.mem _ _ hread_info_s
    have hl_strip : StateLoop hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff
        (ProofLib.stripS kp379 (s₀.setMem s.mem)) (ProofLib.stripS kp379 s) :=
      ⟨(by cases s; exact hl.pc_eq), stripS_hexpCommon_refl kp379 hl.exp, (by cases s; exact hl.x12_eq),
        (by cases s₀; cases s; exact hl.x21_eq), (by cases s; exact hl.x22_eq), (by cases s; exact hl.x25_eq),
        (by cases s; exact hl.x26_eq), (by cases s; exact hl.x27_eq), (by cases s₀; cases s; exact hl.x28_eq),
        by rw [hsp0_of, stripS_readBytes]; exact hl.t_508, by rw [stripS_readBytes]; exact hl.okm_pre⟩
    have hc_ita : RunsToVm ((blkPC_379).rebase (blkPl_379).base H) s fun s2 =>
        S2Frame s.mem s2.mem [(s₀.readReg64 .x6, okmLen), (hsp s₀ - 544#64, 1232)] ∧
        StateLoopA2 hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff (s₀.setMem s2.mem) s2 := by
      refine lift_block_to_379_vm (C := C) (Pj := (blkPC_379).rebase (blkPl_379).base H) blkLib_eq_379 blk379_noSvc0 blk379_noMsr (by decide) (by decide) hcl_s
        (heq379 H ▸ ((iter_a1_placed_runsTo hpre_s ht_len hrem (by omega) hl).trans fun _ hs1 =>
          iter_a2_placed_runsTo_exact hH.memcpy hH.compress256 hpre_s hread_info_s ht_len (by omega) hs1).mono
          fun s2 ⟨hfr2, hs2⟩ => ⟨hfr2, by simpa only [setMem_setMem] using hs2⟩)
        (heq379 (hmacNoMemsetExcHooksSat C.F H s.mem kp379) ▸
          ((iter_a1_placed_runsTo (hpre_stripS kp379 hpre_s) ht_len hrem (by omega) hl_strip).trans fun _ hs1 =>
          iter_a2_placed_runsTo_exact (hmcQ s.mem) (hc256Q s.mem) (hpre_stripS kp379 hpre_s) hread_info_s_q ht_len (by omega) hs1))
        (fun _ hs => hs.2.exp.common.status) (fun _ hs => hs.2.exp.common.status)
        fun sf hvm ⟨hfr_q, hs2_q⟩ => ?_
      have hm_s : (ProofLib.stripS kp379 (s₀.setMem s.mem)).mem = ProofLib.stripExecOutside kp379 s.mem := by cases s₀; rfl
      rw [hkpQ s.mem] at hfr_q hs2_q
      rw [hm_s, stripS_mem, hr6_of, hsp0_of] at hfr_q
      rw [hset_strip s.mem sf] at hs2_q
      rcases hs2_q with ⟨hpc, hexp, hx19, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hin416, hcnt448, hout456, hcnt488, hokm⟩
      rw [hsp0_of, stripS_readBytes] at hin416 hout456
      rw [hsp0_of, stripS_read64] at hcnt448 hcnt488
      rw [stripS_readBytes] at hokm
      exact ⟨unstrip_s2Frame hfr_q hvm.perm_eq,
        ⟨(by cases sf; exact hpc), unstrip_hexpCommon hexp (fun _ => by cases s₀; rfl),
          (by cases s₀; cases sf; exact hx19), (by cases sf; exact hx21),
          (by cases sf; exact hx22), (by cases s₀; cases sf; exact hx23),
          (by cases sf; exact hx24), (by cases sf; exact hx25),
          (by cases sf; exact hx26), (by cases sf; exact hx27),
          by simpa [hsp_setMem] using hin416, by simpa [hsp_setMem] using hcnt448,
          by simpa [hsp_setMem] using hout456, by simpa [hsp_setMem] using hcnt488, hokm⟩⟩
    refine hc_ita.trans_full fun s2 ⟨hs2_fr, hs2⟩ hkf_s2 => ?_
    have hcl_s2 := hcl_s.of_keepsFrozen hkf_s2
    have hf_s2 : HFrameS2 okmLen s₀ s2.mem := hframeS2_trans_1232 hf_s hs2_fr
    have hpre_s2 := hb.at_mem s2.mem hf_s2
    have hread_info_s2 := s2_readable hf_s2 hb.read_info
    have hread_info_s2_q : (ProofLib.stripS kp379 (s₀.setMem s2.mem)).mem.Readable infoA info.length :=
      stripExecOutside_readable kp379 s2.mem _ _ hread_info_s2
    have hs2_strip : StateLoopA2 hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff
        (ProofLib.stripS kp379 (s₀.setMem s2.mem)) (ProofLib.stripS kp379 s2) :=
      ⟨(by cases s2; exact hs2.pc_eq), stripS_hexpCommon_refl kp379 hs2.exp,
        (by cases s₀; cases s2; exact hs2.x19_eq), (by cases s2; exact hs2.x21_eq),
        (by cases s2; exact hs2.x22_eq), (by cases s₀; cases s2; exact hs2.x23_eq),
        (by cases s2; exact hs2.x24_eq), (by cases s2; exact hs2.x25_eq),
        (by cases s2; exact hs2.x26_eq), (by cases s2; exact hs2.x27_eq),
        by rw [hsp0_of, stripS_readBytes]; simpa [hsp_setMem] using hs2.in_416,
        by rw [hsp0_of, stripS_read64]; simpa [hsp_setMem] using hs2.cnt_448,
        by rw [hsp0_of, stripS_readBytes]; simpa [hsp_setMem] using hs2.out_456,
        by rw [hsp0_of, stripS_read64]; simpa [hsp_setMem] using hs2.cnt_488,
        by rw [stripS_readBytes]; exact hs2.okm_pre⟩
    have hc_itb : RunsToVm ((blkPC_379).rebase (blkPl_379).base H) s2
        (StateLoopC hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff (s₀.setMem s2.mem) · (blkPl_425).base) := by
      refine lift_block_to_379_vm (C := C) (Pj := (blkPC_379).rebase (blkPl_379).base H) blkLib_eq_379 blk379_noSvc0 blk379_noMsr (by decide) (by decide) hcl_s2
        (heq379 H ▸ iter_b_placed_runsTo_exact hH.memcpy hpre_s2 hread_info_s2 ht_len hi hrem hdst hs2)
        (heq379 (hmacNoMemsetExcHooksSat C.F H s2.mem kp379) ▸
          iter_b_placed_runsTo_exact (hmcQ s2.mem) (hpre_stripS kp379 hpre_s2) hread_info_s2_q ht_len hi hrem hdst hs2_strip)
        (fun _ hs => hs.exp.common.status) (fun _ hs => hs.exp.common.status)
        fun sf hvm ⟨hpc, hexp, hlr, hx0, hx1, hx20, hx21, hx22, hx24, hx25, hx26, hx27, hx28, hhm, hokm⟩ => ?_
      rw [hsp0_of, stripS_hmacStN] at hhm; rw [stripS_readBytes] at hokm
      exact ⟨(by cases sf; exact hpc), unstrip_hexpCommon hexp hvm.perm_eq, (by cases sf; exact hlr), (by cases s₀; cases sf; exact hx0),
        (by cases s₀; cases sf; exact hx1), (by cases sf; exact hx20), (by cases s₀; cases sf; exact hx21), (by cases sf; exact hx22),
        (by cases sf; exact hx24), (by cases sf; exact hx25), (by cases sf; exact hx26), (by cases sf; exact hx27), (by cases s₀; cases sf; exact hx28), hhm, hokm⟩
    exact hc_itb.trans_full fun sc hsc hkf_c => iter_fin_vm hMemsetVm (hcl_s2.of_keepsFrozen hkf_c) hb hf_s2 (by omega) hsc
  have unstrip_hpost : ∀ {s sf : State}, VmPreserved s sf →
      HPost C.F salt ikm info okmA okmLen (ProofLib.stripS kp379 (s₀.setMem s.mem)) (ProofLib.stripS kp379 sf) →
      HPost C.F salt ikm info okmA okmLen (s₀.setMem s.mem) sf := by
    intro s sf hvm ⟨hpc, hst, hcs, hokm, hfr⟩
    have hr0 : (ProofLib.stripS kp379 (s₀.setMem s.mem)).readReg64 .x6 = s₀.readReg64 .x6 := by cases s₀; rfl
    have hm0 : (ProofLib.stripS kp379 (s₀.setMem s.mem)).mem = ProofLib.stripExecOutside kp379 s.mem := by cases s₀; rfl
    rw [stripS_readBytes] at hokm; unfold HFrame at hfr; rw [hm0, stripS_mem, hr0, hsp0_of] at hfr
    refine ⟨(by cases s₀; cases sf; exact hpc), (by cases sf; exact hst), ⟨(by cases s₀; cases sf; exact hcs.1), fun r hr => ?_⟩, hokm, unstrip_frame hfr hvm.perm_eq⟩
    have := hcs.2 r hr; cases s₀; cases sf; exact this
  have unstrip_loop : ∀ {okmL i rem dstOff : ℕ} {tP okmSF : List (BitVec 8)} {s sf : State}, VmPreserved s sf →
      StateLoop hkdfCodeFakeB C.F salt ikm info infoA okmA tP okmSF okmL i rem dstOff (ProofLib.stripS kp379 (s₀.setMem s.mem)) (ProofLib.stripS kp379 sf) →
      StateLoop hkdfCodeFakeB C.F salt ikm info infoA okmA tP okmSF okmL i rem dstOff (s₀.setMem s.mem) sf := by
    intro _ _ _ _ _ _ s sf hvm ⟨hpc, hexp, hx12, hx21, hx22, hx25, hx26, hx27, hx28, ht508, hokm⟩
    rw [hsp0_of, stripS_readBytes] at ht508; rw [stripS_readBytes] at hokm
    exact ⟨(by cases sf; exact hpc), unstrip_hexpCommon hexp hvm.perm_eq, (by cases sf; exact hx12), (by cases s₀; cases sf; exact hx21),
      (by cases sf; exact hx22), (by cases sf; exact hx25), (by cases sf; exact hx26), (by cases sf; exact hx27), (by cases s₀; cases sf; exact hx28), ht508, hokm⟩
  have stateLoop_reanchor : ∀ {tPrev okmSoFar : List (BitVec 8)} {okmL i rem dstOff : ℕ} {m_old : Memory} {sl : State},
      StateLoop hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmL i rem dstOff (s₀.setMem m_old) sl →
      StateLoop hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmL i rem dstOff (s₀.setMem sl.mem) sl :=
    fun hsl => ⟨hsl.pc_eq, ⟨⟨hsl.exp.common.status, hsl.exp.common.sp_eq, hsl.exp.common.x29_eq,
      hsaved_setMem hsl.exp.common.saved, Frame.refl _ _⟩, hsl.exp.m0_eq, hsl.exp.m8_eq,
      hsl.exp.m16_eq, hsl.exp.m24_eq, hsl.exp.hmac_208⟩, hsl.x12_eq, hsl.x21_eq, hsl.x22_eq,
      hsl.x25_eq, hsl.x26_eq, hsl.x27_eq, hsl.x28_eq, hsl.t_508, hsl.okm_pre⟩
  have stateLoopFin_stripS : ∀ {tPrev okmSoFar : List (BitVec 8)} {okmL i rem dstOff : ℕ} {s_lf : State},
      StateLoopFin hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmL i rem dstOff (s₀.setMem s_lf.mem) s_lf →
      StateLoopFin hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmL i rem dstOff
        (ProofLib.stripS kp379 (s₀.setMem s_lf.mem)) (ProofLib.stripS kp379 s_lf) := by
    intro _ _ _ _ _ _ s_lf hlf
    exact ⟨(by cases s_lf; exact hlf.pc_eq), stripS_hexpCommon_refl kp379 hlf.exp, (by cases s_lf; exact hlf.x20_eq),
      (by cases s₀; cases s_lf; exact hlf.x21_eq), (by cases s_lf; exact hlf.x22_eq), (by cases s_lf; exact hlf.x24_eq),
      (by cases s_lf; exact hlf.x25_eq), (by cases s_lf; exact hlf.x26_eq), (by cases s_lf; exact hlf.x27_eq),
      (by cases s₀; cases s_lf; exact hlf.x28_eq), by rw [hsp0_of, stripS_readBytes]; exact hlf.t_540, by rw [stripS_readBytes]; exact hlf.okm_pre⟩
  refine hb1_ret.trans_full fun s_b1r ⟨hf_b1r, hs_b1r⟩ hkf_b1r => ?_
  have hcl_b1r := hcl₀.of_keepsFrozen hkf_b1r; have hpre_b1r := hb.at_mem s_b1r.mem hf_b1r
  have hs_b1r_strip : StateB1RetFin hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen
      (ProofLib.stripS kp379 (s₀.setMem s_b1r.mem)) (ProofLib.stripS kp379 s_b1r) :=
    ⟨(by cases s_b1r; exact hs_b1r.pc_eq), stripS_hexpCommon_refl kp379 hs_b1r.exp,
      (by cases s_b1r; exact hs_b1r.x21_eq), (by cases s_b1r; exact hs_b1r.x22_eq), (by cases s_b1r; exact hs_b1r.x24_eq),
      (by cases s_b1r; exact hs_b1r.x25_eq), (by cases s_b1r; exact hs_b1r.x26_eq), (by cases s₀; cases s_b1r; exact hs_b1r.x28_eq),
      by rw [hsp0_of, stripS_readBytes]; exact hs_b1r.t1_540⟩
  rcases hb.pre.okm_len with rfl | rfl | rfl
  · exact (lift_block_to_379_vm (C := C) (Pj := (blkPC_379).rebase (blkPl_379).base H) blkLib_eq_379 blk379_noSvc0 blk379_noMsr (by decide) (by decide) hcl_b1r
      (heq379 H ▸ (seg_b1d_placed_runsTo_exact hH.memcpy hpre_b1r hs_b1r).trans fun _ hs1 => (b1_done_32_placed_runsTo hpre_b1r hs1).trans fun _ hd => epilogue_placed_runsTo hpre_b1r hd)
      (runsTo_rebase_of_block379 (X := hmacNoMemsetExcHooksSat C.F H s_b1r.mem kp379) <|
        (seg_b1d_placed_runsTo_exact (hmcQ s_b1r.mem) (hpre_stripS kp379 hpre_b1r) hs_b1r_strip).trans
        fun _ hs1 => (b1_done_32_placed_runsTo (hpre_stripS kp379 hpre_b1r) hs1).trans fun _ hd => epilogue_placed_runsTo (hpre_stripS kp379 hpre_b1r) hd)
      (fun _ hp => hp.2.1) (fun _ hp => hp.2.1) fun sf hvm hp => unstrip_hpost hvm hp).mono
      fun sf ⟨hpc, hst, hcs, hokm, hfr⟩ => ⟨hpc, hst, hcs, hokm, hframeS2_step hf_b1r hfr⟩
  · have hl1_vm : RunsToVm ((blkPC_379).rebase (blkPl_379).base H) s_b1r
        (StateLoop hkdfCodeFakeB C.F salt ikm info infoA okmA
          (CryptoVerification.LibsignalTripleRatchet.Expand.t1 C.F (hkdfExtractBytes C.F salt ikm) info)
          (CryptoVerification.LibsignalTripleRatchet.Expand.t1 C.F (hkdfExtractBytes C.F salt ikm) info) 64 1 32 32 (s₀.setMem s_b1r.mem)) :=
      lift_block_to_379_vm (C := C) (Pj := (blkPC_379).rebase (blkPl_379).base H) blkLib_eq_379 blk379_noSvc0 blk379_noMsr (by decide) (by decide) hcl_b1r
        (runsTo_rebase_of_block379 <| (seg_b1d_placed_runsTo_exact hH.memcpy hpre_b1r hs_b1r).trans fun _ hs1 => b1_to_loop_placed_runsTo (Or.inl rfl) hs1)
        (runsTo_rebase_of_block379 (X := hmacNoMemsetExcHooksSat C.F H s_b1r.mem kp379) <| (seg_b1d_placed_runsTo_exact (hmcQ s_b1r.mem) (hpre_stripS kp379 hpre_b1r) hs_b1r_strip).trans fun _ hs1 => b1_to_loop_placed_runsTo (Or.inl rfl) hs1)
        (fun _ hs => hs.exp.common.status) (fun _ hs => hs.exp.common.status) fun _ hvm h => unstrip_loop hvm h
    refine hl1_vm.trans_full fun sl1 hsl1 hkf_l1 => ?_
    have hcl_l1 := hcl_b1r.of_keepsFrozen hkf_l1; have hf_l1 := hframeS2_step hf_b1r hsl1.exp.common.frame
    refine (hiter_vm hcl_l1 hf_l1 (t1_length _ _ _) (Or.inl rfl) (Or.inl rfl) (by decide) (stateLoop_reanchor hsl1)).trans_full
      fun s_lf1 ⟨hf_lf1, hlf1⟩ hkf_lf1 => ?_
    have hcl_lf1 := hcl_l1.of_keepsFrozen hkf_lf1; have hpre_lf1 := hb.at_mem s_lf1.mem hf_lf1
    have hokm64 := (hkdfExpand_64_eq C.F (hkdfExtractBytes C.F salt ikm) info).symm
    exact (lift_block_to_379_vm (C := C) (Pj := (blkPC_379).rebase (blkPl_379).base H) blkLib_eq_379 blk379_noSvc0 blk379_noMsr (by decide) (by decide) hcl_lf1
      (runsTo_rebase_of_block379 <| (iter_d_done_placed_runsTo_exact hH.memcpy hpre_lf1 (by decide) rfl hokm64 hlf1).trans fun _ hd => epilogue_placed_runsTo hpre_lf1 hd)
      (runsTo_rebase_of_block379 (X := hmacNoMemsetExcHooksSat C.F H s_lf1.mem kp379) <|
        (iter_d_done_placed_runsTo_exact (hmcQ s_lf1.mem) (hpre_stripS kp379 hpre_lf1) (by decide) rfl hokm64 (stateLoopFin_stripS hlf1)).trans fun _ hd => epilogue_placed_runsTo (hpre_stripS kp379 hpre_lf1) hd)
      (fun _ hp => hp.2.1) (fun _ hp => hp.2.1) fun sf hvm hp => unstrip_hpost hvm hp).mono
      fun sf ⟨hpc, hst, hcs, hokm, hfr⟩ => ⟨hpc, hst, hcs, hokm, hframeS2_step hf_lf1 hfr⟩
  · have hl1_vm : RunsToVm ((blkPC_379).rebase (blkPl_379).base H) s_b1r
        (StateLoop hkdfCodeFakeB C.F salt ikm info infoA okmA
          (CryptoVerification.LibsignalTripleRatchet.Expand.t1 C.F (hkdfExtractBytes C.F salt ikm) info)
          (CryptoVerification.LibsignalTripleRatchet.Expand.t1 C.F (hkdfExtractBytes C.F salt ikm) info) 96 1 64 32 (s₀.setMem s_b1r.mem)) :=
      lift_block_to_379_vm (C := C) (Pj := (blkPC_379).rebase (blkPl_379).base H) blkLib_eq_379 blk379_noSvc0 blk379_noMsr (by decide) (by decide) hcl_b1r
        (runsTo_rebase_of_block379 <| (seg_b1d_placed_runsTo_exact hH.memcpy hpre_b1r hs_b1r).trans fun _ hs1 => b1_to_loop_placed_runsTo (Or.inr rfl) hs1)
        (runsTo_rebase_of_block379 (X := hmacNoMemsetExcHooksSat C.F H s_b1r.mem kp379) <| (seg_b1d_placed_runsTo_exact (hmcQ s_b1r.mem) (hpre_stripS kp379 hpre_b1r) hs_b1r_strip).trans fun _ hs1 => b1_to_loop_placed_runsTo (Or.inr rfl) hs1)
        (fun _ hs => hs.exp.common.status) (fun _ hs => hs.exp.common.status) fun _ hvm h => unstrip_loop hvm h
    refine hl1_vm.trans_full fun sl1 hsl1 hkf_l1 => ?_
    have hcl_l1 := hcl_b1r.of_keepsFrozen hkf_l1; have hf_l1 := hframeS2_step hf_b1r hsl1.exp.common.frame
    refine (hiter_vm hcl_l1 hf_l1 (t1_length _ _ _) (Or.inl rfl) (Or.inr rfl) (by decide) (stateLoop_reanchor hsl1)).trans_full
      fun s_lf1 ⟨hf_lf1, hlf1⟩ hkf_lf1 => ?_
    have hcl_lf1 := hcl_l1.of_keepsFrozen hkf_lf1; have hpre_lf1 := hb.at_mem s_lf1.mem hf_lf1
    have hl2_vm := lift_block_to_379_vm (C := C) (Pj := (blkPC_379).rebase (blkPl_379).base H) blkLib_eq_379 blk379_noSvc0 blk379_noMsr (by decide) (by decide) hcl_lf1
      (runsTo_rebase_of_block379 <| iter_d_continue_placed_runsTo_exact hH.memcpy hpre_lf1 rfl hlf1)
      (runsTo_rebase_of_block379 (X := hmacNoMemsetExcHooksSat C.F H s_lf1.mem kp379) <| iter_d_continue_placed_runsTo_exact (hmcQ s_lf1.mem) (hpre_stripS kp379 hpre_lf1) rfl (stateLoopFin_stripS hlf1))
      (fun _ hs => hs.exp.common.status) (fun _ hs => hs.exp.common.status) fun _ hvm h => unstrip_loop hvm h
    refine hl2_vm.trans_full fun sl2 hsl2 hkf_l2 => ?_
    have hcl_l2 := hcl_lf1.of_keepsFrozen hkf_l2; have hf_l2 := hframeS2_step hf_lf1 hsl2.exp.common.frame
    refine (hiter_vm hcl_l2 hf_l2 (length_hmacWith _ _ _) (Or.inr rfl) (Or.inl rfl) (by decide) (stateLoop_reanchor hsl2)).trans_full
      fun s_lf2 ⟨hf_lf2, hlf2⟩ hkf_lf2 => ?_
    have hcl_lf2 := hcl_l2.of_keepsFrozen hkf_lf2; have hpre_lf2 := hb.at_mem s_lf2.mem hf_lf2
    have hokm96 := (hkdfExpand_96_eq C.F (hkdfExtractBytes C.F salt ikm) info).symm
    exact (lift_block_to_379_vm (C := C) (Pj := (blkPC_379).rebase (blkPl_379).base H) blkLib_eq_379 blk379_noSvc0 blk379_noMsr (by decide) (by decide) hcl_lf2
      (runsTo_rebase_of_block379 <| (iter_d_done_placed_runsTo_exact hH.memcpy hpre_lf2 (by decide) rfl hokm96 hlf2).trans fun _ hd => epilogue_placed_runsTo hpre_lf2 hd)
      (runsTo_rebase_of_block379 (X := hmacNoMemsetExcHooksSat C.F H s_lf2.mem kp379) <|
        (iter_d_done_placed_runsTo_exact (hmcQ s_lf2.mem) (hpre_stripS kp379 hpre_lf2) (by decide) rfl hokm96 (stateLoopFin_stripS hlf2)).trans fun _ hd => epilogue_placed_runsTo (hpre_stripS kp379 hpre_lf2) hd)
      (fun _ hp => hp.2.1) (fun _ hp => hp.2.1) fun sf hvm hp => unstrip_hpost hvm hp).mono
      fun sf ⟨hpc, hst, hcs, hokm, hfr⟩ => ⟨hpc, hst, hcs, hokm, hframeS2_step hf_lf2 hfr⟩

theorem bytesAt_read {ro : Bool} {p : BitVec 64} {bs : List (BitVec 8)}
    {R : SepProp} {m : Memory} (hle : bs.length ≤ 2 ^ 64) (hsep : m ⊨ bytesAt ro p bs ∗ R) :
    m.readBytes p bs.length = bs := by
  cases ro; · exact ((IsBlock.pointsToBytes p bs).read hsep).2
  · exact (IsBlockRO.pointsToBytesRO p bs hle).read hsep

theorem bytesAt_readable {ro : Bool} {p : BitVec 64} {bs : List (BitVec 8)}
    {R : SepProp} {m : Memory} (hle : bs.length ≤ 2 ^ 64) (hsep : m ⊨ bytesAt ro p bs ∗ R) :
    m.Readable p bs.length := by
  cases ro
  · intro a ha
    obtain ⟨hp, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp ((IsBlock.pointsToBytes p bs).permNoLazy_rw hsep ha)
    exact ⟨by rw [hp]; rfl, hlf⟩
  · have hb := IsBlockRO.pointsToBytesRO p bs hle
    exact fun a ha => ⟨hb.perm_r hsep ha, hb.isLazyFree_false hsep ha⟩

theorem bytesAt_outside_rw {ro : Bool} {p b_rw : BitVec 64} {bs : List (BitVec 8)}
    {n_rw : Nat} {Q R : SepProp} {Φ_rw : Memory → Prop} {m : Memory}
    (hle : bs.length ≤ 2 ^ 64) (hrw_pos : 0 < n_rw)
    (hrw : IsBlock Q b_rw n_rw Φ_rw) (hsep : m ⊨ bytesAt ro p bs ∗ (Q ∗ R)) :
    ∀ a, InRegion p bs.length a → OutsideRegion b_rw n_rw a := by
  cases ro
  · intro a ha; have hpos : 0 < bs.length := by unfold InRegion at ha; omega
    have hd := (IsBlock.pointsToBytes p bs).disjoint hrw hpos hrw_pos hsep
    unfold DisjointRegions at hd; unfold InRegion at ha; unfold OutsideRegion; bv_omega
  · exact ro_outside_rw_shared_lb (IsBlockRO.pointsToBytesRO p bs hle) hrw hsep

theorem stackAt_hkdfToSlice (s₀ : State) : stackAt s₀.sp extHookStack =
    memRegion (s₀.sp - 16384#64) 14976 ∗ memRegion (hsp s₀ - 720#64) 1408 := by
  have h1 : stackAt s₀.sp extHookStack = memRegion (s₀.sp - 16384#64) 14976 ∗ stackAt s₀.sp 1408 :=
    ProofLib.stackAt_split_bottom s₀.sp 1408 14976 (by decide)
  have h2 : stackAt s₀.sp 1408 = memRegion (hsp s₀ - 720#64) 1408 := by
    simp only [stackAt, hsp]; congr 1; bv_lin
  rw [h1, h2]

private theorem hookSat_sessionMemsetRegionBudget_of_allocVm
    {H : String → Option (State → State)} {sym : String}
    (h : HookSat H sym (withAllocVmPreserved sessionMemsetRegionSpec)) :
    HookSat H sym sessionMemsetRegionBudgetSpec := by
  refine ProofLib.HookSat.mono h fun x R s0 hpre => ⟨x, R, hpre, fun sf hpost => ?_⟩
  dsimp only [withAllocVmPreserved, sessionMemsetRegionBudgetSpec] at hpost ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨hpost.1.2, hpost.2⟩

private theorem hkdf_to_slice_spqr_core_sat [LibsignalPlacement] (C : Crypto)
    {H : LibsignalHooks} [hH : HkdfPlacedHooksExactSat C.F H]
    (hMemsetVm : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec)
    (Q : State → State → Prop)
    (hQ : ∀ {s0 sf : State}, VmPreserved s0 sf →
      (ProgMemsetAllocVm ((blkPC_379).rebase (blkPl_379).base H) → AllocCallPreserved s0 sf) →
      Q s0 sf) :
    subroutine_ok ((blkPC_379).rebase (blkPl_379).base H) (blkPl_379).base
      (withLsCodeRoLoaded lsmpl
        { hkdfToSliceSpqrSpec (spqrHkdfWith C.F) with
          post := fun x s0 sf =>
            ⌜Q s0 sf⌝ ∗ (hkdfToSliceSpqrSpec (spqrHkdfWith C.F)).post x s0 sf }) := by
  refine subroutine_ok_intro fun x R s0 hpc hrun hpre hsp_al => ?_
  obtain ⟨⟨hcl, hro⟩, hpre⟩ := extract_withLsCodeRoLoaded hpre
  change s0.mem ⊨ (hkdfToSliceSpqrSpec (spqrHkdfWith C.F)).pre x s0 ∗ R at hpre
  rw [hkdfToSliceSpqrSpec, hkdfToSliceSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7,
    hsalt_lt, hikm_len, hinfo_ge, hinfo_lt, hokm_len⟩, hsep⟩
  rw [stackAt_hkdfToSlice s0] at hsep
  have hb_okm := IsBlock.memRegion x.okmA x.okmLen
  have hb_stk := IsBlock.memRegion (hsp s0 - 720#64) 1408
  let R_inv : SepProp := bytesAt x.saltRO x.saltA x.salt ∗ bytesAt x.ikmRO x.ikmA x.ikm ∗
    bytesAt x.infoRO x.infoA x.info ∗ memRegion (s0.sp - 16384#64) 14976 ∗ R
  have hsep_okm_stk : s0.mem ⊨ memRegion x.okmA x.okmLen ∗ (memRegion (hsp s0 - 720#64) 1408 ∗ R_inv) := by
    dsimp only [R_inv]; ac_nf at hsep ⊢
  have hsep_stk : s0.mem ⊨ memRegion (hsp s0 - 720#64) 1408 ∗ (memRegion x.okmA x.okmLen ∗ R_inv) := by
    dsimp only [R_inv]; ac_nf at hsep ⊢
  have hsep_salt_stk : s0.mem ⊨ bytesAt x.saltRO x.saltA x.salt ∗ (memRegion (hsp s0 - 720#64) 1408 ∗
      (bytesAt x.ikmRO x.ikmA x.ikm ∗ bytesAt x.infoRO x.infoA x.info ∗ memRegion x.okmA x.okmLen ∗ memRegion (s0.sp - 16384#64) 14976 ∗ R)) := by ac_nf at hsep ⊢
  have hsep_salt_okm : s0.mem ⊨ bytesAt x.saltRO x.saltA x.salt ∗ (memRegion x.okmA x.okmLen ∗
      (memRegion (hsp s0 - 720#64) 1408 ∗ bytesAt x.ikmRO x.ikmA x.ikm ∗ bytesAt x.infoRO x.infoA x.info ∗ memRegion (s0.sp - 16384#64) 14976 ∗ R)) := by ac_nf at hsep ⊢
  have hsep_ikm_stk : s0.mem ⊨ bytesAt x.ikmRO x.ikmA x.ikm ∗ (memRegion (hsp s0 - 720#64) 1408 ∗
      (bytesAt x.saltRO x.saltA x.salt ∗ bytesAt x.infoRO x.infoA x.info ∗ memRegion x.okmA x.okmLen ∗ memRegion (s0.sp - 16384#64) 14976 ∗ R)) := by ac_nf at hsep ⊢
  have hsep_ikm_okm : s0.mem ⊨ bytesAt x.ikmRO x.ikmA x.ikm ∗ (memRegion x.okmA x.okmLen ∗
      (memRegion (hsp s0 - 720#64) 1408 ∗ bytesAt x.saltRO x.saltA x.salt ∗ bytesAt x.infoRO x.infoA x.info ∗ memRegion (s0.sp - 16384#64) 14976 ∗ R)) := by ac_nf at hsep ⊢
  have hsep_info_stk : s0.mem ⊨ bytesAt x.infoRO x.infoA x.info ∗ (memRegion (hsp s0 - 720#64) 1408 ∗
      (bytesAt x.saltRO x.saltA x.salt ∗ bytesAt x.ikmRO x.ikmA x.ikm ∗ memRegion x.okmA x.okmLen ∗ memRegion (s0.sp - 16384#64) 14976 ∗ R)) := by ac_nf at hsep ⊢
  have hsep_info_okm : s0.mem ⊨ bytesAt x.infoRO x.infoA x.info ∗ (memRegion x.okmA x.okmLen ∗
      (memRegion (hsp s0 - 720#64) 1408 ∗ bytesAt x.saltRO x.saltA x.salt ∗ bytesAt x.ikmRO x.ikmA x.ikm ∗ memRegion (s0.sp - 16384#64) 14976 ∗ R)) := by ac_nf at hsep ⊢
  have hokm_pos : 0 < x.okmLen := by omega
  have hokm_le : x.okmLen ≤ 2 ^ 64 := by omega
  have hrw_okm : s0.mem.RW x.okmA x.okmLen := fun a ha => hb_okm.permNoLazy_rw hsep_okm_stk ha
  have hrw_stk1408 : s0.mem.RW (hsp s0 - 720#64) 1408 := fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
  obtain ⟨hro_iv, hiv_eq⟩ := rodata_sha256IV_placed hro
  have hread_iv : s0.mem.Readable spqrSha256IVAddr 32 := fun a ha =>
    let ⟨hp, hlf⟩ := hro_iv a ha; ⟨by rw [hp]; rfl, hlf⟩
  have hdisj_iv_stk1408 : DisjointRegions spqrSha256IVAddr 32 (hsp s0 - 720#64) 1408 :=
    disjointRegions_of_ro_rw (by decide) (by decide) hro_iv hrw_stk1408
  have hdisj_okm_stk1408 : DisjointRegions x.okmA x.okmLen (hsp s0 - 720#64) 1408 :=
    hb_okm.disjoint hb_stk hokm_pos (by decide) hsep_okm_stk
  have hout_salt_stk1408 : ∀ a, InRegion x.saltA x.salt.length a → OutsideRegion (hsp s0 - 720#64) 1408 a :=
    bytesAt_outside_rw (by omega) (by decide) hb_stk hsep_salt_stk
  have hout_ikm_stk1408 : ∀ a, InRegion x.ikmA x.ikm.length a → OutsideRegion (hsp s0 - 720#64) 1408 a :=
    bytesAt_outside_rw (by omega) (by decide) hb_stk hsep_ikm_stk
  have hout_info_stk1408 : ∀ a, InRegion x.infoA x.info.length a → OutsideRegion (hsp s0 - 720#64) 1408 a :=
    bytesAt_outside_rw (by omega) (by decide) hb_stk hsep_info_stk
  have hdisj_salt_stk1408 :
      x.salt.length = 0 ∨ DisjointRegions x.saltA x.salt.length (hsp s0 - 720#64) 1408 := by
    by_cases h0 : x.salt.length = 0; · exact Or.inl h0
    · exact Or.inr (disjointRegions_of_outside (by omega) (by decide) hout_salt_stk1408)
  have hb : HPreBase x.salt x.ikm x.info x.saltA x.ikmA x.infoA x.okmA x.okmLen s0 :=
    { pre :=
        { pc_eq := by rw [hkdfCodeFakeB, BitVec.sub_add_cancel]; exact hpc, status := hrun,
          x0_eq := hx0, x1_eq := hx1, x2_eq := hx2, x3_eq := hx3,
          x4_eq := hx4, x5_eq := hx5, x6_eq := hx6, x7_eq := hx7,
          salt_lt := hsalt_lt, ikm_len := hikm_len, info_ge := hinfo_ge, info_lt := hinfo_lt,
          okm_len := hokm_len, base_al := trivial,
          ro_iv_bytes := by rw [nfs3PlacedFakeB_add_iv]; exact hiv_eq,
          ro_iv_read := by rw [nfs3PlacedFakeB_add_iv]; exact hread_iv,
          disj_iv_stk := by
            rw [nfs3PlacedFakeB_add_iv]
            exact hdisj_iv_stk1408.sub_right (hsp s0 - 544#64) ⟨by decide, by bv_omega⟩,
          disj_iv_okm := by rw [nfs3PlacedFakeB_add_iv]; exact disjointRegions_of_ro_rw (by decide) hokm_pos hro_iv hrw_okm,
          salt_bytes := bytesAt_read (by omega) hsep_salt_stk,
          ikm_bytes := bytesAt_read (by omega) hsep_ikm_stk,
          info_bytes := bytesAt_read (by omega) hsep_info_stk,
          rw_okm := hrw_okm, rw_stack := hrw_stk1408.sub (by bv_omega),
          disj_okm_stk := hdisj_okm_stk1408.sub_right (hsp s0 - 544#64) ⟨by decide, by bv_omega⟩,
          disj_salt_stk := hdisj_salt_stk1408.imp id fun hd =>
            hd.sub_right (hsp s0 - 544#64) ⟨by decide, by bv_omega⟩,
          out_salt_stk := fun a ha => by
            have h := hout_salt_stk1408 a ha; unfold OutsideRegion at h ⊢; bv_omega,
          out_salt_okm := bytesAt_outside_rw (by omega) hokm_pos hb_okm hsep_salt_okm,
          out_ikm_stk := fun a ha => by
            have h := hout_ikm_stk1408 a ha; unfold OutsideRegion at h ⊢; bv_omega,
          out_ikm_okm := bytesAt_outside_rw (by omega) hokm_pos hb_okm hsep_ikm_okm,
          out_info_stk := fun a ha => by
            have h := hout_info_stk1408 a ha; unfold OutsideRegion at h ⊢; bv_omega,
          out_info_okm := bytesAt_outside_rw (by omega) hokm_pos hb_okm hsep_info_okm,
          sp_aligned := by simpa [State.spAligned] using hsp_al },
      rw_stk1408 := hrw_stk1408,
      disj_iv_stk1408 := hdisj_iv_stk1408,
      disj_salt_stk1408 := hdisj_salt_stk1408,
      out_salt_stk1408 := hout_salt_stk1408,
      out_ikm_stk1408 := hout_ikm_stk1408,
      out_info_stk1408 := hout_info_stk1408,
      read_salt := bytesAt_readable (by omega) hsep_salt_stk,
      read_ikm := bytesAt_readable (by omega) hsep_ikm_stk,
      read_info := bytesAt_readable (by omega) hsep_info_stk }
  intro hL0
  obtain ⟨sf, hsteps_H, hvm, hacp, htr, hvregs, ⟨hpc_sf, hstat_sf, hcallee, hokm_sf, hframe_sf⟩, _⟩ :=
    hkdf_to_slice_kdf_vm_sat (C := C) hMemsetVm hcl hb hL0
  refine ⟨sf, hsteps_H, Or.inl ⟨hpc_sf, hstat_sf, ?_, CallingConventionPreserved_of_calleeSaved hcallee (htr := ⟨htr, hvregs⟩)⟩⟩
  dsimp only [withLsCodeRoLoaded]
  rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hQ hvm hacp, ?_⟩
  rw [hkdfToSliceSpqrSpec, hkdfToSliceSpec]; dsimp only []; rw [sepConj_assoc, satisfies_pure_sepConj]
  have h_spqr_eq : spqrHkdfWith C.F x.salt x.ikm x.info x.okmLen =
      hkdfExpand C.F (hkdfExtractBytes C.F x.salt x.ikm) x.info x.okmLen := rfl
  have h_exp_len : (spqrHkdfWith C.F x.salt x.ikm x.info x.okmLen).length = x.okmLen := by
    rw [h_spqr_eq]; rcases hokm_len with h32 | h64 | h96
    · rw [h32, hkdfExpand_32_eq, t1_length]
    · rw [h64, hkdfExpand_64_eq]; simp [t1_length, t2_length]
    · rw [h96, hkdfExpand_96_eq]; simp [t1_length, t2_length, t3_length]
  refine ⟨⟨h_exp_len, htr⟩, ?_⟩
  unfold HFrameS2 at hframe_sf; rw [hx6] at hframe_sf; rw [← h_spqr_eq] at hokm_sf
  have hb_okm' := IsBlock.pointsToBytes_len (a := x.okmA) h_exp_len
  have hpost_sep : sf.mem ⊨ (x.okmA ↦ₛ spqrHkdfWith C.F x.salt x.ikm x.info x.okmLen) ∗
      (memRegion (hsp s0 - 720#64) 1408 ∗ R_inv) :=
    S2Frame.update_two_blocks hb_okm hb_okm' hb_stk hb_stk hsep_okm_stk hframe_sf
      ⟨by rw [h_exp_len]; exact hokm_le, by rwa [h_exp_len]⟩ trivial
  rw [stackAt_hkdfToSlice s0]; dsimp only [R_inv] at hpost_sep; ac_nf at hpost_sep ⊢

/-- **Block `379` (`spqr::kdf::hkdf_to_slice`, 473 instructions) meets
`withLsCodeRoLoaded lsmpl (withVmPreserved (hkdfToSliceSpqrSpec (spqrHkdfWith C.F)))`** on
`(blkPC_379).rebase (blkPl_379).base H` under `[HkdfPlacedHooksExactSat C.F H]` and
`HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec`. -/
theorem hkdf_to_slice_spqr_placed_ok_sat [LibsignalPlacement] (C : Crypto)
    {H : LibsignalHooks} [hH : HkdfPlacedHooksExactSat C.F H]
    (hMemsetVm : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec) :
    subroutine_ok ((blkPC_379).rebase (blkPl_379).base H) (blkPl_379).base
      (withLsCodeRoLoaded lsmpl (withVmPreserved (hkdfToSliceSpqrSpec (spqrHkdfWith C.F)))) :=
  hkdf_to_slice_spqr_core_sat C hMemsetVm VmPreserved (fun hvm _ => hvm)

/-- Any caller block `i < 619` can invoke Block `379` (`spqr::kdf::hkdf_to_slice`) at
`lsmpl.base 379` under `withLsCodeRoLoaded lsmpl` with `VmPreserved`. -/
theorem hkdf_to_slice_spqr_placed_ok_of_other_block_sat [LibsignalPlacement] (C : Crypto)
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] [HkdfPlacedHooksExactSat C.F H]
    (hMemsetVm : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 379)
      (withLsCodeRoLoaded lsmpl (withVmPreserved (hkdfToSliceSpqrSpec (spqrHkdfWith C.F)))) :=
  keys_ls_subroutine_ok_of_block_cro (hkdf_to_slice_spqr_placed_ok_sat C hMemsetVm) hi

/-- **Block `379` (`spqr::kdf::hkdf_to_slice`, 473 instructions) meets
`withLsCodeRoLoaded lsmpl (withAllocVmPreserved (hkdfToSliceSpqrSpec (spqrHkdfWith C.F)))`** on
`(blkPC_379).rebase (blkPl_379).base H` under `[HkdfPlacedHooksExactSat C.F H]` and
`HookSat H lsMemsetSym (withAllocVmPreserved sessionMemsetRegionSpec)`. -/
theorem hkdf_to_slice_spqr_allocVm_placed_ok_sat [LibsignalPlacement] (C : Crypto)
    {H : LibsignalHooks} [hH : HkdfPlacedHooksExactSat C.F H]
    (hMemsetAllocVm : HookSat H lsMemsetSym (withAllocVmPreserved sessionMemsetRegionSpec)) :
    subroutine_ok ((blkPC_379).rebase (blkPl_379).base H) (blkPl_379).base
      (withLsCodeRoLoaded lsmpl
        (withAllocVmPreserved (hkdfToSliceSpqrSpec (spqrHkdfWith C.F)))) := by
  have hpma : ProgMemsetAllocVm ((blkPC_379).rebase (blkPl_379).base H) := by
    obtain ⟨f, hfH, hfOk⟩ := hMemsetAllocVm
    refine ⟨f, ?_, hfOk⟩
    rw [ls_externAt?_of_mem (by decide) (by decide) (by decide), hfH]
  exact hkdf_to_slice_spqr_core_sat C
    (hookSat_sessionMemsetRegionBudget_of_allocVm hMemsetAllocVm)
    (fun s0 sf => AllocCallPreserved s0 sf ∧ VmPreserved s0 sf)
    (fun hvm hacp => ⟨hacp hpma, hvm⟩)

/-- Any caller block `i < 619` can invoke Block `379` (`spqr::kdf::hkdf_to_slice`) at
`lsmpl.base 379` under `withLsCodeRoLoaded lsmpl` with `AllocCallPreserved ∧ VmPreserved`. -/
theorem hkdf_to_slice_spqr_allocVm_placed_ok_of_other_block_sat [LibsignalPlacement] (C : Crypto)
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] [HkdfPlacedHooksExactSat C.F H]
    (hMemsetAllocVm : HookSat H lsMemsetSym (withAllocVmPreserved sessionMemsetRegionSpec))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 379)
      (withLsCodeRoLoaded lsmpl
        (withAllocVmPreserved (hkdfToSliceSpqrSpec (spqrHkdfWith C.F)))) :=
  keys_ls_subroutine_ok_of_block_cro
    (hkdf_to_slice_spqr_allocVm_placed_ok_sat C hMemsetAllocVm) hi

/-- **Block `378` (`spqr::kdf::hkdf_to_vec`) meets `hkdfToVecSpec` under `[HkdfPlacedHooksExactSat C.F H]`.** -/
theorem hkdf_to_vec_spqr_placed_ok_sat [LibsignalPlacement] (C : Crypto)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {H : LibsignalHooks} [HkdfPlacedHooksExactSat C.F H]
    (hMemsetVm : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec)
    (hshim : HookSat H spqrRustNoAllocShimSym (withVmPreserved noAllocShimSpec))
    (hZero : HookSat H spqrRustAllocZeroedSym (rustAllocZeroedBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_378).rebase (blkPl_378).base H) (blkPl_378).base
      (withLsCodeRoLoaded lsmpl (hkdfToVecSpec M A lim (spqrHkdfWith C.F))) :=
  hkdf_to_vec_placed_ok M A lim (spqrHkdfWith C.F) hshim hZero
    (hkdf_to_slice_spqr_placed_ok_of_other_block_sat C hMemsetVm)

/-- Any caller block `i < 619` can invoke Block `378` (`spqr::kdf::hkdf_to_vec`) at `lsmpl.base 378`. -/
theorem hkdf_to_vec_spqr_placed_ok_of_other_block_sat [LibsignalPlacement] (C : Crypto)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] [HkdfPlacedHooksExactSat C.F H]
    (hMemsetVm : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec)
    (hshim : HookSat H spqrRustNoAllocShimSym (withVmPreserved noAllocShimSpec))
    (hZero : HookSat H spqrRustAllocZeroedSym (rustAllocZeroedBudgetSpec M A lim))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 378)
      (withLsCodeRoLoaded lsmpl (hkdfToVecSpec M A lim (spqrHkdfWith C.F))) :=
  keys_ls_subroutine_ok_of_block_cro
    (hkdf_to_vec_spqr_placed_ok_sat C M A lim hMemsetVm hshim hZero) hi

end LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetSat
