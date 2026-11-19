/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.EntryAndKeyBlock -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.DefsSat
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceExact
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceSecondHalf
import LibsignalBinary.Proofs.CodeLayout

/-!
# `HookSatExactMemcpy` siblings for `EntryAndKeyBlock` (Block `73`)

Replaces `H lsMemcpySym = some memcpyHook` on Block `73`'s two `memcpy`-touching entry segments
(`seg0b_placed_runsTo` calling `new_from_slice` at Block `114`, and `seg1b1_placed_runsTo`
stepping through the 1-byte `memcpy` call) with `h_memcpy : HookSatExactMemcpy H lsMemcpySym`.
Keeps `StateH1Placed`, `StateH1pPlaced`, and `StateH2Placed` unchanged and reuses
`seg0a_placed_runsTo` and `seg1b2_placed_runsTo` verbatim.
-/

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.EntryAndKeyBlockExact

open Arm64 ProofLib
open CryptoGames.HMAC (ShaState sha256IV)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (
  LibsignalCodeLoaded LibsignalHooks LibsignalPlacement blkPl_73 lsProg_73 lsmpl
)
open CryptoVerification.LibsignalAesCbc (memsetHook)
open CryptoVerification.LibsignalHmac (shaStateBytes)
open CryptoVerification.LibsignalSession.CryptoHmacSha256 (
  Frame HmacPlacedPre HmacSaved RW RunsTo RunsTo.lsProg_svc StateH0Placed StateH1Placed
  StateH1mPlaced StateH1pPlaced StateH2Placed TraceEq hsp hsp_align
  lsCompress256Sym lsMemcpySym lsMemsetSym lsSha256IVAddr readBytes_32_eq_of_read64_eq
  seg0a_placed_runsTo seg1b2_placed_runsTo writeBytes_singleton
)
open CryptoVerification.LibsignalTripleRatchet.Extract (S2Frame)
open LibsignalBinary.Heap.MuslMemOpsRunsTo (applyMemcpyClobber)
open LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.DefsSat (
  s2Frame_of_hmacFrame s2Frame_readBytes_eq_of_readable s2Frame_readable_of_readable
)
open LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceExact (
  new_from_slice_placed_run_exact
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore (
  HookSatExactMemcpy placed_memcpy_step_of_exact
)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat (HookSatCompress256)

attribute [local arm64_norm] MemWidth.bytes SimdMemSize.bytes

/-- `1200`-B stack precondition for `hmac_sha256` (Block `73`), extending `HmacPlacedPre` (`1024` B)
by `176` B at the bottom `[s₀.sp - 1200#64, s₀.sp - 1024#64)` so `new_from_slice` at `sp = hsp s₀`
(`s₀.sp - 480#64`) has its full `720`-B `HookSat` stack (`480 + 720 = 1200 ≤ 2048`). -/
structure HmacPlacedPreSat [LibsignalPlacement] (F : ShaCompress)
    (key inp : List (BitVec 8)) (s₀ : State) : Prop where
  pc_eq          : s₀.pc = (blkPl_73).base
  status         : s₀.status = .Running
  sp_aligned     : (s₀.sp &&& 0b1111#64) = 0#64
  x2_eq          : s₀.readReg64 .x2 = 32#64
  x4_eq          : s₀.readReg64 .x4 = 1#64
  key_len        : key.length = 32
  inp_len        : inp.length = 1
  key_eq         : s₀.mem.readBytes (s₀.readReg64 .x1) 32 = key
  inp_eq         : s₀.mem.readBytes (s₀.readReg64 .x3) 1 = inp
  iv_eq          : s₀.mem.readBytes lsSha256IVAddr 32 = shaStateBytes sha256IV
  read_iv        : s₀.mem.Readable lsSha256IVAddr 32
  read_inp       : s₀.mem.Readable (s₀.readReg64 .x3) 1
  rw_out         : RW s₀.mem (s₀.readReg64 .x0) 32
  rw_stack       : RW s₀.mem (s₀.sp - 1200#64) 1200
  disj_iv_stack  : DisjointRegions lsSha256IVAddr 32 (s₀.sp - 1200#64) 1200
  disj_out_stack : DisjointRegions (s₀.readReg64 .x0) 32 (s₀.sp - 1200#64) 1200
  disj_key_stack : DisjointRegions (s₀.readReg64 .x1) 32 (s₀.sp - 1200#64) 1200
  disj_inp_stack : DisjointRegions (s₀.readReg64 .x3) 1 (s₀.sp - 1200#64) 1200

theorem HmacPlacedPreSat.toHmacPlacedPre [LibsignalPlacement] {F : ShaCompress}
    {key inp : List (BitVec 8)} {s₀ : State} (h : HmacPlacedPreSat F key inp s₀) :
    HmacPlacedPre F key inp s₀ :=
  have hsub : 0 < 1024 ∧ ((s₀.sp - 1024#64) - (s₀.sp - 1200#64)).toNat + 1024 ≤ 1200 :=
    ⟨by decide, by clear * -; bv_omega⟩
  { pc_eq := h.pc_eq, status := h.status, sp_aligned := h.sp_aligned
    x2_eq := h.x2_eq, x4_eq := h.x4_eq, key_len := h.key_len, inp_len := h.inp_len
    key_eq := h.key_eq, inp_eq := h.inp_eq, iv_eq := h.iv_eq
    read_iv := h.read_iv, read_inp := h.read_inp, rw_out := h.rw_out
    rw_stack := h.rw_stack.sub (by clear * -; bv_omega)
    disj_iv_stack := h.disj_iv_stack.sub_right _ hsub
    disj_out_stack := h.disj_out_stack.sub_right _ hsub
    disj_key_stack := h.disj_key_stack.sub_right _ hsub
    disj_inp_stack := h.disj_inp_stack.sub_right _ hsub }

theorem HmacPlacedPreSat.of_s2Frame [LibsignalPlacement] {F : ShaCompress}
    {key inp : List (BitVec 8)} {s₀ : State} {m : Memory}
    (h : HmacPlacedPreSat F key inp s₀)
    (hread_key : s₀.mem.Readable (s₀.readReg64 .x1) 32)
    (hf : S2Frame s₀.mem m [(s₀.sp - 1200#64, 1200)]) :
    HmacPlacedPreSat F key inp (s₀.setMem m) ∧
    (s₀.setMem m).mem.Readable ((s₀.setMem m).readReg64 .x1) 32 :=
  ⟨{ pc_eq := h.pc_eq, status := h.status, sp_aligned := h.sp_aligned
     x2_eq := h.x2_eq, x4_eq := h.x4_eq, key_len := h.key_len, inp_len := h.inp_len
     key_eq := (s2Frame_readBytes_eq_of_readable hf hread_key (by decide)
       (by simp [h.disj_key_stack.symm])).trans h.key_eq
     inp_eq := (s2Frame_readBytes_eq_of_readable hf h.read_inp (by decide)
       (by simp [h.disj_inp_stack.symm])).trans h.inp_eq
     iv_eq := (s2Frame_readBytes_eq_of_readable hf h.read_iv (by decide)
       (by simp [h.disj_iv_stack.symm])).trans h.iv_eq
     read_iv := s2Frame_readable_of_readable hf h.read_iv
     read_inp := s2Frame_readable_of_readable hf h.read_inp
     rw_out := hf.rw_of_rw _ _ h.rw_out
     rw_stack := hf.rw_of_rw _ _ h.rw_stack
     disj_iv_stack := h.disj_iv_stack
     disj_out_stack := h.disj_out_stack
     disj_key_stack := h.disj_key_stack
     disj_inp_stack := h.disj_inp_stack },
   s2Frame_readable_of_readable hf hread_key⟩

theorem hmacSaved_of_s2Frame {s₀ : State} {m₁ m₂ : Memory} {rs : List (BitVec 64 × Nat)}
    (hrw_saved : RW m₁ (hsp s₀ + 384#64) 96)
    (hs : HmacSaved s₀ (hsp s₀) m₁)
    (hf : S2Frame m₁ m₂ rs)
    (hd : ∀ r ∈ rs, DisjointRegions r.1 r.2 (hsp s₀ + 384#64) 96) :
    HmacSaved s₀ (hsp s₀) m₂ := by
  rcases hs with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  have slot (off : BitVec 64) (hoff : (off - 384#64).toNat + 8 ≤ 96) :
      m₂.read64 (hsp s₀ + off) = m₁.read64 (hsp s₀ + off) := by
    have hsub : 0 < 8 ∧ ((hsp s₀ + off) - (hsp s₀ + 384#64)).toNat + 8 ≤ 96 :=
      ⟨by decide, by clear * - hoff; bv_omega⟩
    exact hf.read64_eq (hrw_saved.sub hsub.2) (fun r hr => (hd r hr).sub_right _ hsub)
  exact ⟨(slot 384#64 (by decide)).trans h1,
         (slot 392#64 (by decide)).trans h2,
         (slot 400#64 (by decide)).trans h3,
         (slot 416#64 (by decide)).trans h4,
         (slot 424#64 (by decide)).trans h5,
         (slot 432#64 (by decide)).trans h6,
         (slot 440#64 (by decide)).trans h7,
         (slot 448#64 (by decide)).trans h8,
         (slot 456#64 (by decide)).trans h9,
         (slot 464#64 (by decide)).trans h10,
         (slot 472#64 (by decide)).trans h11⟩

/-- `HookSatExactMemcpy` + `HookSatCompress256` sibling of `seg0b_placed_runsTo`
(`EntryAndKeyBlock.lean:931`), using `1200` B of stack (`480 + 720`). -/
theorem seg0b_placed_runsTo_exact [LibsignalPlacement] {F : ShaCompress}
    {H : LibsignalHooks} (h_memcpy : HookSatExactMemcpy H lsMemcpySym)
    (h_compress : HookSatCompress256 H lsCompress256Sym F) {key inp : List (BitVec 8)} {s₀ sc : State}
    (hcl : LibsignalCodeLoaded lsmpl sc.mem) (hpre : HmacPlacedPreSat F key inp s₀)
    (hread_key : s₀.mem.Readable (s₀.readReg64 .x1) 32)
    (hsc : StateH0Placed s₀ sc) :
    RunsTo (lsProg_73 H) sc (fun s₁ =>
      StateH1Placed F key (s₀.setMem s₁.mem) s₁ ∧
      S2Frame s₀.mem s₁.mem [(s₀.sp - 1200#64, 1200)]) := by
  have hpre1024 := hpre.toHmacPlacedPre
  have hhsp_sub_720 : hsp s₀ - 720#64 = s₀.sp - 1200#64 := by unfold hsp; bv_omega
  rcases hsc with ⟨hpc_c, ⟨hstat_c, hsp_c, hx29_c, hx27_c, hsaved_c, hframe_c⟩,
    hx0_c, hx1_c, hx2_c, hlr_c, hx19_c, hx20_c, hx21_c⟩
  have hal_hsp : (hsp s₀ &&& 0b1111#64) = 0#64 := hsp_align hpre.sp_aligned
  have hkey_c : sc.mem.readBytes (sc.readReg64 .x1) (sc.readReg64 .x2).toNat = key := by
    rw [hx1_c, hx2_c, show (32#64 : BitVec 64).toNat = 32 from rfl,
      hframe_c.readBytes_eq (by simp [hpre1024.disj_key_stack.symm]) (by decide), hpre.key_eq]
  have hiv_c : sc.mem.readBytes lsSha256IVAddr 32 = shaStateBytes sha256IV := by
    rw [hframe_c.readBytes_eq (by simp [hpre1024.disj_iv_stack.symm]) (by decide), hpre.iv_eq]
  have hread_iv_c : sc.mem.Readable lsSha256IVAddr 32 := (hframe_c.readable_iff _ _).mpr hpre.read_iv
  have hrw_stack_c : RW sc.mem (s₀.sp - 1200#64) 1200 := (hframe_c.rw_iff _ _).mpr hpre.rw_stack
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
  refine (RunsTo.of_other_block hcl
    (new_from_slice_placed_run_exact h_memcpy h_compress hpc_c hstat_c (by rw [hx2_c]; decide)
      hiv_c hread_iv_c hdisj_iv_nfs hrw_out_nfs hrw_stack_nfs hdisj_out_nfs
      hread_key_nfs (Or.inr hdisj_key_nfs)
      (by rw [hsp_c]; exact hal_hsp))).mono fun s₁ hs₁ => ?_
  rcases hs₁ with ⟨hpc1, hstat1, hcs1, htag1, hhmac1, hframe1⟩
  rw [hlr_c] at hpc1; rw [hx0_c] at htag1 hhmac1 hframe1; rw [hsp_c, hhsp_sub_720] at hframe1
  rw [hkey_c] at hhmac1
  have hhmac_addr : hsp s₀ + 144#64 + 8#64 = hsp s₀ + 152#64 := by clear * -; bv_omega
  rw [hhmac_addr] at hhmac1
  have hrw_saved_c : RW sc.mem (hsp s₀ + 384#64) 96 :=
    hrw_stack_c.sub (by clear * -; unfold hsp; bv_omega)
  have hs2_0c : S2Frame s₀.mem sc.mem [(s₀.sp - 1200#64, 1200)] := by
    refine (s2Frame_of_hmacFrame hframe_c).mono fun a ha r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
    have hstk := ha (s₀.sp - 1200#64, 1200) (by simp)
    clear * - hstk; unfold OutsideRegion at hstk ⊢; bv_omega
  have hs2_c1 : S2Frame sc.mem s₁.mem [(s₀.sp - 1200#64, 1200)] := by
    refine hframe1.mono fun a ha r hr => ?_
    have hstk := ha (s₀.sp - 1200#64, 1200) (by simp)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;>
      (dsimp only at *; clear * - hstk; try unfold hsp at *; unfold OutsideRegion at hstk ⊢; bv_omega)
  exact ⟨⟨hpc1, ⟨hstat1, hcs1.1.trans hsp_c, (hcs1.2 .x29 (by simp)).trans hx29_c,
    (hcs1.2 .x27 (by simp)).trans hx27_c,
    hmacSaved_of_s2Frame hrw_saved_c hsaved_c hframe1 (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;>
        (try dsimp only; clear * -; unfold hsp; simp only [State.sp_setMem]; unfold DisjointRegions; bv_omega)),
    Frame.refl s₁.mem _⟩,
    (hcs1.2 .x19 (by simp)).trans hx19_c, (hcs1.2 .x20 (by simp)).trans hx20_c,
    (hcs1.2 .x21 (by simp)).trans hx21_c, htag1, hhmac1⟩,
    hs2_0c.trans hs2_c1⟩

/-- `HookSatExactMemcpy` + `HookSatCompress256` sibling of `seg0_placed_runsTo`
(`EntryAndKeyBlock.lean:973`), using `1200` B of stack (`480 + 720`). -/
theorem seg0_placed_runsTo_exact [LibsignalPlacement] {F : ShaCompress}
    {H : LibsignalHooks} (h_memcpy : HookSatExactMemcpy H lsMemcpySym)
    (h_compress : HookSatCompress256 H lsCompress256Sym F) {key inp : List (BitVec 8)} {s₀ : State}
    (hcl : LibsignalCodeLoaded lsmpl s₀.mem) (hpre : HmacPlacedPreSat F key inp s₀)
    (hread_key : s₀.mem.Readable (s₀.readReg64 .x1) 32) :
    RunsTo (lsProg_73 H) s₀ (fun s₁ =>
      StateH1Placed F key (s₀.setMem s₁.mem) s₁ ∧
      S2Frame s₀.mem s₁.mem [(s₀.sp - 1200#64, 1200)]) :=
  RunsTo.trans_keepsFrozen (seg0a_placed_runsTo hpre.toHmacPlacedPre) (fun _ hsc hkf =>
    seg0b_placed_runsTo_exact h_memcpy h_compress (hcl.of_keepsFrozen hkf) hpre hread_key hsc)

set_option maxHeartbeats 1600000 in
/-- `HookSatExactMemcpy` sibling of `seg1b1_placed_runsTo` (`EntryAndKeyBlock.lean:1092`). -/
theorem seg1b1_placed_runsTo_exact [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_memcpy : HookSatExactMemcpy H lsMemcpySym)
    {key : List (BitVec 8)} {byte : BitVec 8} {s₀ s : State}
    (hpre : HmacPlacedPre F key [byte] s₀) (hs : StateH1mPlaced F key s₀ s) :
    RunsTo (lsProg_73 H) s (StateH1pPlaced F key byte s₀) := by
  generalize hPost : StateH1pPlaced F key byte s₀ = Post
  rcases hs with ⟨hpc, ⟨hstat, hsp_eq, hx29, hx27, hsaved, hframe⟩,
    hx0, hx1, hx2, hlr, hx19, hx21, hx22, hx23, hx25, hist, hibl, host, hobl⟩
  have hal_hsp : (hsp s₀ &&& 0b1111#64) = 0#64 := hsp_align hpre.sp_aligned
  have hrw_hsp : s.mem.RW (hsp s₀) 480 :=
    ((hframe.rw_iff _ _).mpr hpre.rw_stack).sub (by clear * -; unfold hsp; bv_omega)
  have hinp_s : s.mem.readBytes (s₀.readReg64 .x3) 1 = [byte] := by
    rw [hframe.readBytes_eq (by simp [hpre.disj_inp_stack.symm]) (by decide), hpre.inp_eq]
  have hread_inp_s : s.mem.Readable (s₀.readReg64 .x3) 1 :=
    (hframe.readable_iff _ _).mpr hpre.read_inp
  have hdisj_inp : 1 = 0 ∨ DisjointRegions (hsp s₀) 1 (s₀.readReg64 .x3) 1 :=
    Or.inr ((hpre.disj_inp_stack.sub_right _ ⟨by decide, by clear * -; unfold hsp; bv_omega⟩).symm)
  refine placed_memcpy_step_of_exact h_memcpy
    (hrun := hstat)
    (hsp := by simp only [State.spAligned, hsp_eq, hal_hsp]; rfl)
    (hpc := hpc) (hx0 := hx0) (hx1 := hx1) (hx2 := by rw [hx2]; rfl)
    (hlr := hlr) (hmem := rfl) (hread := hinp_s) (hrw := hrw_hsp.sub (by clear * -; bv_omega))
    (hreadable := hread_inp_s) (hdisj := hdisj_inp)
    fun c => ?_
  dsimp only [applyMemcpyClobber]
  rw [writeBytes_singleton]
  iterate 25 sess_step
  subst hPost; refine RunsTo.refl ?_
  refine ⟨by simp only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm, lsMemsetSym],
    ⟨by simp only [arm64_norm, hstat], by simp only [arm64_norm, hsp_eq],
     by simp only [arm64_norm, hx29], by simp only [arm64_norm, hx27], ?_, ?_⟩,
    by simp only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm],
    by simp only [arm64_norm], by simp only [arm64_norm],
    by simp only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm],
    by simp only [arm64_norm, hx19], by simp only [arm64_norm],
    by simp only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm],
    by simp only [arm64_norm, hx22], by simp only [arm64_norm],
    by simp only [arm64_norm], by simp only [arm64_norm, hibl],
    by simp (config := { decide := true }) only [arm64_norm], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases hsaved with ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩
    dsimp only [HmacSaved, State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11]
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    refine Frame.write8_stack1024 ?_ _ _; iterate 18 refine Frame.write64_stack1024 ?_ _ _
    (iterate 2 refine Frame.write8_stack1024 ?_ _ _); exact hframe
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm]
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm]
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    rw [← hist]; refine readBytes_32_eq_of_read64_eq _ s.mem (hsp s₀ + 208#64) (hsp s₀ + 64#64) ?_ ?_ ?_ ?_ <;>
      simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm]
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm, hibl]
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    rw [← host]; refine readBytes_32_eq_of_read64_eq _ s.mem (hsp s₀ + 248#64) (hsp s₀ + 104#64) ?_ ?_ ?_ ?_ <;>
      simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm]
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm, hobl]

/-- `HookSatExactMemcpy` sibling of `seg1b_placed_runsTo` (`EntryAndKeyBlock.lean:1182`). -/
theorem seg1b_placed_runsTo_exact [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_memcpy : HookSatExactMemcpy H lsMemcpySym)
    (h_memset : H lsMemsetSym = some memsetHook) {key : List (BitVec 8)} {byte : BitVec 8} {s₀ s : State}
    (hpre : HmacPlacedPre F key [byte] s₀) (hs : StateH1mPlaced F key s₀ s) :
    RunsTo (lsProg_73 H) s (StateH2Placed F key byte s₀) :=
  (seg1b1_placed_runsTo_exact h_memcpy hpre hs).trans (fun _ h1p => seg1b2_placed_runsTo h_memset hpre h1p)

end LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.EntryAndKeyBlockExact
